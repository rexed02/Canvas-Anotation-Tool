import json
import copy
import math
from krita import *
from PyQt5.QtWidgets import (QWidget, QApplication, QDockWidget, QVBoxLayout,
                             QPushButton, QHBoxLayout, QColorDialog, QButtonGroup,
                             QLabel, QAbstractScrollArea, QMdiArea, QSlider, QFrame)
from PyQt5.QtCore import Qt, QPoint, QPointF, QRect, QRectF, QEvent, QTimer, QByteArray, QObject
from PyQt5.QtGui import (QPainter, QPen, QColor, QPainterPath, QTransform,
                         QMouseEvent, QKeyEvent, QVector2D, QCursor)

# --- CONSTANTES HANDLES ---
H_NONE = 0
H_TOP_LEFT = 1
H_TOP = 2
H_TOP_RIGHT = 3
H_RIGHT = 4
H_BOTTOM_RIGHT = 5
H_BOTTOM = 6
H_BOTTOM_LEFT = 7
H_LEFT = 8
H_BODY = 9

# Clave única para guardar los datos en el .kra
ANNOTATION_KEY = "screen_annotation_plugin_data_v17"


class OverlayWidget(QWidget):
    def __init__(self, docker_ref, parent=None):
        super().__init__(parent)
        self.docker = docker_ref

        # --- JERARQUÍA: HIJO DEL VIEWPORT ---
        self.setWindowFlags(Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_NoSystemBackground)
        self.setAttribute(Qt.WA_DeleteOnClose)

        self.setMouseTracking(True)
        # Importante: NoFocus para evitar peleas con el Docker
        self.setFocusPolicy(Qt.NoFocus)

        self.current_path = None

        # --- CONFIGURACIÓN DE SUAVIZADO ---
        self.smoothing_factor = 0.5
        self.stabilizer_pos = QPointF()

        # Navegación
        self.is_panning = False
        self.is_space_held = False
        self.last_pan_pos = QPoint()

        # --- REDIMENSIÓN DE PINCEL ---
        self.is_resizing_brush = False
        self.last_resize_pos = QPoint()
        self.resize_center_doc = None

        # Edición
        self.active_handle = H_NONE
        self.start_pos_doc = QPointF()
        self.initial_paths_map = {}
        self.initial_widths_map = {}
        self.initial_combined_rect = QRectF()

        # Selección
        self.is_selecting_area = False
        self.selection_start_doc = QPointF()
        self.selection_current_doc = QPointF()

        # Undo/Redo Stacks (locales)
        self.undo_stack = []
        self.redo_stack = []

        qApp.installEventFilter(self)

    def closeEvent(self, event):
        try:
            qApp.removeEventFilter(self)
        except Exception:
            pass
        try:
            # Limpiar referencia inversa si existe
            if getattr(self.docker, "overlay", None) is self:
                self.docker.overlay = None
        except Exception:
            pass
        super().closeEvent(event)

    # --- ALGORITMO DE SIMPLIFICACIÓN (RDP) ---
    def perpendicular_distance(self, pt, line_start, line_end):
        x0, y0 = pt.x(), pt.y()
        x1, y1 = line_start.x(), line_start.y()
        x2, y2 = line_end.x(), line_end.y()
        nom = abs((y2 - y1) * x0 - (x2 - x1) * y0 + x2 * y1 - y2 * x1)
        denom = math.sqrt((y2 - y1)**2 + (x2 - x1)**2)
        return nom / denom if denom != 0 else 0

    def rdp_simplify(self, points, epsilon):
        if len(points) < 3:
            return points
        dmax = 0.0
        index = 0
        end = len(points) - 1
        p1 = points[0]
        p2 = points[end]

        for i in range(1, end):
            d = self.perpendicular_distance(points[i], p1, p2)
            if d > dmax:
                index = i
                dmax = d

        if dmax > epsilon:
            rec_results1 = self.rdp_simplify(points[:index+1], epsilon)
            rec_results2 = self.rdp_simplify(points[index:], epsilon)
            return rec_results1[:-1] + rec_results2
        else:
            return [points[0], points[end]]

    def apply_post_processing(self, path):
        point_count = path.elementCount()
        if point_count < 2:
            return path
        raw_points = []
        for i in range(point_count):
            e = path.elementAt(i)
            raw_points.append(QPointF(e.x, e.y))

        simplified_points = self.rdp_simplify(raw_points, 1.0)

        new_path = QPainterPath()
        new_path.moveTo(simplified_points[0])
        for p in simplified_points[1:]:
            new_path.lineTo(p)

        return new_path

    # --- FILTRO DE EVENTOS ---
    def eventFilter(self, obj, event):
        # Protección contra objeto eliminado
        try:
            if not self.isVisible():
                return False
        except RuntimeError:
            return False

        if self.docker.mode == "KRITA_DRAW":
            return False

        # 1. SHORTCUT OVERRIDE
        if event.type() == QEvent.ShortcutOverride:
            key = event.key()
            modifiers = event.modifiers()
            is_undo = (key == Qt.Key_Z and (modifiers & Qt.ControlModifier))
            is_delete = (key == Qt.Key_Delete)
            if is_undo or is_delete:
                event.accept()
                return True

        # 2. KEY PRESS
        if event.type() == QEvent.KeyPress:
            key = event.key()
            modifiers = event.modifiers()

            if key == Qt.Key_Space:
                if not self.is_space_held:
                    self.is_space_held = True
                    if not self.is_panning and not self.is_resizing_brush:
                        self.setCursor(Qt.OpenHandCursor)
                return True

            if key == Qt.Key_Z and (modifiers & Qt.ControlModifier):
                if modifiers & Qt.ShiftModifier:
                    self.redo()
                else:
                    self.undo()
                return True

            if key == Qt.Key_Delete:
                if self.docker.selected_indices:
                    self.commit_state()
                    sorted_indices = sorted(list(self.docker.selected_indices), reverse=True)
                    for idx in sorted_indices:
                        if idx < len(self.docker.stored_paths):
                            del self.docker.stored_paths[idx]
                    self.docker.selected_indices.clear()
                    self.update()
                    self.save_to_document_deferred()
                return True

        # 3. KEY RELEASE
        if event.type() == QEvent.KeyRelease:
            if event.key() == Qt.Key_Space:
                self.is_space_held = False
                if not self.is_panning and not self.is_resizing_brush:
                    self.update_cursor()
                return True

        return super().eventFilter(obj, event)

    # --- MÉTODOS DE NAVEGACIÓN ---
    def pan_canvas(self, delta):
        viewport = self.docker.target_viewport
        if viewport and viewport.parent():
            try:
                scroll_area = viewport.parent()
                if isinstance(scroll_area, QAbstractScrollArea):
                    h_bar = scroll_area.horizontalScrollBar()
                    v_bar = scroll_area.verticalScrollBar()
                    h_bar.setValue(h_bar.value() - delta.x())
                    v_bar.setValue(v_bar.value() - delta.y())
            except RuntimeError:
                self._handle_deleted_viewport()
            except Exception:
                pass

    # --- EVENTOS DE RATÓN ---
    def mousePressEvent(self, e):
        if e.button() == Qt.MiddleButton or (e.button() == Qt.LeftButton and self.is_space_held):
            self.is_panning = True
            self.last_pan_pos = e.pos()
            self.setCursor(Qt.ClosedHandCursor)
            return

        modifiers = QApplication.keyboardModifiers()
        if self.docker.mode == "ANNOTATE" and (modifiers & Qt.ShiftModifier) and e.button() == Qt.LeftButton:
            self.is_resizing_brush = True
            self.last_resize_pos = e.pos()
            try:
                global_pos = self.mapToGlobal(e.pos())
                self.resize_center_doc = self.map_screen_to_doc(global_pos)
            except RuntimeError:
                self.resize_center_doc = None
            return

        if e.button() == Qt.LeftButton:
            self.inputPress(e.pos())

    def mouseMoveEvent(self, e):
        if self.is_panning:
            delta = e.pos() - self.last_pan_pos
            self.last_pan_pos = e.pos()
            self.pan_canvas(delta)
            self.update()
            return

        if self.is_resizing_brush:
            delta_x = e.pos().x() - self.last_resize_pos.x()
            self.last_resize_pos = e.pos()
            new_size = self.docker.line_width + (delta_x * 0.5)
            new_size = max(1.0, min(new_size, 200.0))
            self.docker.line_width = new_size
            try:
                self.docker.slider_size.setValue(int(new_size))
                self.docker.lbl_size_value.setText(f"{int(new_size)} px")
            except Exception:
                pass
            self.update()
            return

        self.inputMove(e.pos())

    def mouseReleaseEvent(self, e):
        is_middle = (e.button() == Qt.MiddleButton)
        is_left = (e.button() == Qt.LeftButton)

        if (is_middle and self.is_panning) or (is_left and self.is_panning):
            self.is_panning = False
            if self.is_space_held:
                self.setCursor(Qt.OpenHandCursor)
            else:
                self.update_cursor()
            return

        if is_left and self.is_resizing_brush:
            self.is_resizing_brush = False
            self.resize_center_doc = None
            self.save_to_document_deferred()
            return

        if is_left:
            self.inputRelease()

    # --- RESTO DE LÓGICA ---
    def commit_state(self):
        state_snapshot = []
        for path, color, width in self.docker.stored_paths:
            state_snapshot.append((QPainterPath(path), QColor(color), width))
        self.undo_stack.append(state_snapshot)
        self.redo_stack.clear()
        if len(self.undo_stack) > 50:
            self.undo_stack.pop(0)

    def undo(self):
        if not self.undo_stack:
            return
        current_state = []
        for path, color, width in self.docker.stored_paths:
            current_state.append((QPainterPath(path), QColor(color), width))
        self.redo_stack.append(current_state)
        prev_state = self.undo_stack.pop()
        self.docker.stored_paths = prev_state
        self.docker.selected_indices.clear()
        self.update()
        self.save_to_document_deferred()

    def redo(self):
        if not self.redo_stack:
            return
        current_state = []
        for path, color, width in self.docker.stored_paths:
            current_state.append((QPainterPath(path), QColor(color), width))
        self.undo_stack.append(current_state)
        next_state = self.redo_stack.pop()
        self.docker.stored_paths = next_state
        self.docker.selected_indices.clear()
        self.update()
        self.save_to_document_deferred()

    def serialize_path(self, path):
        elements = []
        for i in range(path.elementCount()):
            e = path.elementAt(i)
            elements.append((e.type, e.x, e.y))
        return elements

    def save_to_document_deferred(self):
        self.docker.save_settings()

    def get_canvas_state(self):
        try:
            view = Krita.instance().activeWindow().activeView()
            if view:
                canvas = view.canvas()
                return canvas.zoomLevel(), canvas.rotation(), canvas.mirror(), view.flakeToCanvasTransform()
        except Exception:
            pass
        return 1.0, 0, False, QTransform()

    def map_screen_to_doc(self, screen_pos):
        viewport = self.docker.target_viewport
        if not viewport:
            return QPointF(screen_pos)
        try:
            pos_in_viewport = viewport.mapFromGlobal(screen_pos)
            zoom, rot, is_mirrored, t_pos = self.get_canvas_state()
            doc_origin = t_pos.map(QPointF(0, 0))
            m = QTransform()
            m.translate(doc_origin.x(), doc_origin.y())
            m.rotate(rot)
            sx = -zoom if is_mirrored else zoom
            sy = zoom
            m.scale(sx, sy)
            inv, ok = m.inverted()
            if ok:
                return inv.map(QPointF(pos_in_viewport))
        except RuntimeError:
            self._handle_deleted_viewport()
        except Exception:
            pass
        return QPointF(screen_pos)

    def _handle_deleted_viewport(self):
        try:
            if getattr(self.docker, "target_viewport", None) is not None:
                self.docker.target_viewport = None
        except Exception:
            pass
        try:
            QTimer.singleShot(0, self.close)
        except Exception:
            try:
                self.close()
            except Exception:
                pass

    def get_combined_bounding_rect(self):
        if not self.docker.selected_indices:
            return QRectF()
        combined = QRectF()
        first = True
        for idx in self.docker.selected_indices:
            if idx < len(self.docker.stored_paths):
                rect = self.docker.stored_paths[idx][0].boundingRect()
                if first:
                    combined = rect
                    first = False
                else:
                    combined = combined.united(rect)
        return combined

    def paintEvent(self, event):
        viewport = self.docker.target_viewport
        try:
            if not viewport or not viewport.isVisible():
                return
        except RuntimeError:
            self._handle_deleted_viewport()
            return
        except Exception:
            return

        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)

        if self.docker.mode != "KRITA_DRAW":
            painter.setBrush(QColor(0, 0, 0, 1))
            painter.setPen(Qt.NoPen)
            painter.drawRect(self.rect())

        real_zoom, rotation, is_mirrored, t_pos = self.get_canvas_state()

        doc_origin = t_pos.map(QPointF(0, 0))
        final_transform = QTransform()
        final_transform.translate(doc_origin.x(), doc_origin.y())
        final_transform.rotate(rotation)
        sx = -real_zoom if is_mirrored else real_zoom
        sy = real_zoom
        final_transform.scale(sx, sy)

        painter.setTransform(final_transform)
        painter.setBrush(Qt.NoBrush)

        for i, (path, color, width) in enumerate(self.docker.stored_paths):
            try:
                pen = QPen(color, width, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin)
                pen.setCosmetic(False)
                painter.setPen(pen)
                painter.drawPath(path)
            except Exception:
                continue

        if self.docker.mode == "MOVE" and self.docker.selected_indices:
            combined_rect = self.get_combined_bounding_rect()
            if not combined_rect.isEmpty():
                self.draw_transform_box(painter, combined_rect, real_zoom)

        if self.current_path and self.docker.mode == "ANNOTATE":
            current_width = self.docker.line_width
            try:
                pen = QPen(self.docker.current_color, current_width, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin)
                pen.setCosmetic(False)
                painter.setPen(pen)
                painter.setBrush(Qt.NoBrush)
                painter.drawPath(self.current_path)
            except Exception:
                pass

        if self.is_selecting_area and self.docker.mode == "MOVE":
            sel_rect = QRectF(self.selection_start_doc, self.selection_current_doc).normalized()
            painter.setPen(QPen(Qt.white, 1 / real_zoom, Qt.DashLine))
            painter.setBrush(QColor(0, 120, 255, 50))
            painter.drawRect(sel_rect)

        if self.docker.mode == "ANNOTATE" and (not self.is_space_held or self.is_resizing_brush):
            if self.is_resizing_brush and self.resize_center_doc is not None:
                mouse_doc = self.resize_center_doc
            else:
                mouse_global = QCursor.pos()
                mouse_doc = self.map_screen_to_doc(mouse_global)

            cursor_size = self.docker.line_width
            try:
                painter.setPen(QPen(Qt.black, 1 / real_zoom))
            except Exception:
                painter.setPen(QPen(Qt.black, 1))
            painter.setBrush(Qt.NoBrush)
            rad = cursor_size / 2.0
            painter.drawEllipse(mouse_doc, rad, rad)
            try:
                painter.setPen(QPen(Qt.white, 1 / real_zoom))
                inner = max(0.0, rad - (1 / real_zoom))
                painter.drawEllipse(mouse_doc, inner, inner)
            except Exception:
                pass

    def draw_transform_box(self, painter, rect, current_zoom):
        pen_box = QPen(Qt.blue, 1, Qt.DashLine)
        pen_box.setCosmetic(True)
        painter.setPen(pen_box)
        painter.setBrush(Qt.NoBrush)
        painter.drawRect(rect)

        handles = self.get_handle_coords(rect)
        safe_zoom = current_zoom if current_zoom > 0.0001 else 1.0
        h_size = 8.0 / safe_zoom

        painter.setPen(QPen(Qt.blue, 1 / safe_zoom))
        painter.setBrush(Qt.white)
        for h_type, pos in handles.items():
            painter.drawRect(QRectF(pos.x() - h_size/2, pos.y() - h_size/2, h_size, h_size))

    def get_handle_coords(self, rect):
        return {
            H_TOP_LEFT: rect.topLeft(), H_TOP: QPointF(rect.center().x(), rect.top()),
            H_TOP_RIGHT: rect.topRight(), H_RIGHT: QPointF(rect.right(), rect.center().y()),
            H_BOTTOM_RIGHT: rect.bottomRight(), H_BOTTOM: QPointF(rect.center().x(), rect.bottom()),
            H_BOTTOM_LEFT: rect.bottomLeft(), H_LEFT: QPointF(rect.left(), rect.center().y())
        }

    def wheelEvent(self, event):
        delta = event.angleDelta().y()
        action = "view_zoom_in" if delta > 0 else "view_zoom_out"
        try:
            Krita.instance().action(action).trigger()
        except Exception:
            pass
        self.update()

    def update_cursor(self):
        if self.is_space_held:
            self.setCursor(Qt.OpenHandCursor)
        elif self.docker.mode == "ANNOTATE":
            self.setCursor(Qt.BlankCursor)
        elif self.docker.mode == "MOVE":
            self.setCursor(Qt.ArrowCursor)
        else:
            self.setCursor(Qt.ArrowCursor)

    def get_hit_handle(self, doc_pos, rect):
        zoom, _, _, _ = self.get_canvas_state()
        safe_zoom = zoom if zoom > 0.001 else 1.0
        tol = 10.0 / safe_zoom
        handles = self.get_handle_coords(rect)
        for h_type, pos in handles.items():
            if (QVector2D(doc_pos) - QVector2D(pos)).length() < tol:
                return h_type
        if rect.contains(doc_pos):
            return H_BODY
        return H_NONE

    def inputPress(self, pos):
        if self.docker.mode == "KRITA_DRAW":
            return

        try:
            global_pos = self.mapToGlobal(pos)
            doc_pos = self.map_screen_to_doc(global_pos)
        except RuntimeError:
            return

        modifiers = QApplication.keyboardModifiers()
        is_shift = (modifiers & Qt.ShiftModifier)

        if self.docker.mode == "ANNOTATE":
            self.current_path = QPainterPath()
            self.current_path.moveTo(doc_pos)
            self.stabilizer_pos = doc_pos
            self.update()

        elif self.docker.mode == "MOVE":
            combined_rect = self.get_combined_bounding_rect()
            hit_handle = H_NONE
            if not combined_rect.isEmpty():
                hit_handle = self.get_hit_handle(doc_pos, combined_rect)

            if hit_handle != H_NONE:
                self.commit_state()
                self.active_handle = hit_handle
                self.start_pos_doc = doc_pos
                self.initial_combined_rect = combined_rect
                self.initial_paths_map = {}
                self.initial_widths_map = {}
                for idx in self.docker.selected_indices:
                    self.initial_paths_map[idx] = QPainterPath(self.docker.stored_paths[idx][0])
                    self.initial_widths_map[idx] = self.docker.stored_paths[idx][2]
                return

            found_index = -1
            zoom, _, _, _ = self.get_canvas_state()
            safe_zoom = zoom if zoom > 0.001 else 1.0
            hit_radius = 15.0 / safe_zoom
            hit_rect = QRectF(doc_pos.x() - hit_radius, doc_pos.y() - hit_radius, hit_radius*2, hit_radius*2)

            for i in range(len(self.docker.stored_paths) - 1, -1, -1):
                path, _, _ = self.docker.stored_paths[i]
                if path.intersects(hit_rect) or path.contains(doc_pos):
                    found_index = i
                    break

            if found_index != -1:
                if is_shift:
                    if found_index in self.docker.selected_indices:
                        self.docker.selected_indices.remove(found_index)
                    else:
                        self.docker.selected_indices.add(found_index)
                else:
                    if found_index not in self.docker.selected_indices:
                        self.docker.selected_indices = {found_index}

                self.commit_state()
                self.active_handle = H_BODY
                self.start_pos_doc = doc_pos
                self.initial_combined_rect = self.get_combined_bounding_rect()
                self.initial_paths_map = {}
                self.initial_widths_map = {}
                for idx in self.docker.selected_indices:
                    self.initial_paths_map[idx] = QPainterPath(self.docker.stored_paths[idx][0])
                    self.initial_widths_map[idx] = self.docker.stored_paths[idx][2]

            else:
                if not is_shift:
                    self.docker.selected_indices.clear()
                self.is_selecting_area = True
                self.selection_start_doc = doc_pos
                self.selection_current_doc = doc_pos
                self.active_handle = H_NONE
            self.update()

    def inputMove(self, pos):
        if self.docker.mode == "KRITA_DRAW":
            return

        try:
            global_pos = self.mapToGlobal(pos)
            doc_pos = self.map_screen_to_doc(global_pos)
        except RuntimeError:
            return

        if self.docker.mode == "MOVE" and self.active_handle == H_NONE and not self.is_selecting_area:
            combined_rect = self.get_combined_bounding_rect()
            if not combined_rect.isEmpty():
                hit = self.get_hit_handle(doc_pos, combined_rect)
                if hit in [H_TOP_LEFT, H_BOTTOM_RIGHT]:
                    self.setCursor(Qt.SizeFDiagCursor)
                elif hit in [H_TOP_RIGHT, H_BOTTOM_LEFT]:
                    self.setCursor(Qt.SizeBDiagCursor)
                elif hit in [H_TOP, H_BOTTOM]:
                    self.setCursor(Qt.SizeVerCursor)
                elif hit in [H_LEFT, H_RIGHT]:
                    self.setCursor(Qt.SizeHorCursor)
                elif hit == H_BODY:
                    self.setCursor(Qt.SizeAllCursor)
                else:
                    self.setCursor(Qt.ArrowCursor)
            else:
                self.setCursor(Qt.ArrowCursor)

        if self.docker.mode == "ANNOTATE" and self.current_path:
            target = doc_pos
            factor = self.smoothing_factor
            self.stabilizer_pos = self.stabilizer_pos + (target - self.stabilizer_pos) * factor
            self.current_path.lineTo(self.stabilizer_pos)
            self.update()

        elif self.is_selecting_area:
            self.selection_current_doc = doc_pos
            self.update()

        elif self.docker.mode == "MOVE" and self.active_handle != H_NONE:
            if self.active_handle == H_BODY:
                delta = doc_pos - self.start_pos_doc
                for idx in self.docker.selected_indices:
                    if idx in self.initial_paths_map:
                        new_path = QPainterPath(self.initial_paths_map[idx])
                        new_path.translate(delta.x(), delta.y())
                        _, col, wid = self.docker.stored_paths[idx]
                        self.docker.stored_paths[idx] = (new_path, col, wid)
            else:
                r_old = self.initial_combined_rect
                fixed_point = r_old.center()
                original_handle_pos = QPointF()

                if self.active_handle == H_TOP_LEFT:
                    fixed_point = r_old.bottomRight()
                    original_handle_pos = r_old.topLeft()
                elif self.active_handle == H_TOP:
                    fixed_point = QPointF(r_old.center().x(), r_old.bottom())
                    original_handle_pos = QPointF(r_old.center().x(), r_old.top())
                elif self.active_handle == H_TOP_RIGHT:
                    fixed_point = r_old.bottomLeft()
                    original_handle_pos = r_old.topRight()
                elif self.active_handle == H_RIGHT:
                    fixed_point = QPointF(r_old.left(), r_old.center().y())
                    original_handle_pos = QPointF(r_old.right(), r_old.center().y())
                elif self.active_handle == H_BOTTOM_RIGHT:
                    fixed_point = r_old.topLeft()
                    original_handle_pos = r_old.bottomRight()
                elif self.active_handle == H_BOTTOM:
                    fixed_point = QPointF(r_old.center().x(), r_old.top())
                    original_handle_pos = QPointF(r_old.center().x(), r_old.bottom())
                elif self.active_handle == H_BOTTOM_LEFT:
                    fixed_point = r_old.topRight()
                    original_handle_pos = r_old.bottomLeft()
                elif self.active_handle == H_LEFT:
                    fixed_point = QPointF(r_old.right(), r_old.center().y())
                    original_handle_pos = QPointF(r_old.left(), r_old.center().y())

                vec_orig = original_handle_pos - fixed_point
                vec_curr = doc_pos - fixed_point

                sx = vec_curr.x() / vec_orig.x() if abs(vec_orig.x()) > 0.001 else 1.0
                sy = vec_curr.y() / vec_orig.y() if abs(vec_orig.y()) > 0.001 else 1.0

                if self.active_handle in [H_TOP, H_BOTTOM]:
                    sx = abs(sy)
                elif self.active_handle in [H_LEFT, H_RIGHT]:
                    sy = abs(sx)
                else:
                    max_scale = max(abs(sx), abs(sy))
                    sx = max_scale * (1.0 if sx >= 0 else -1.0)
                    sy = max_scale * (1.0 if sy >= 0 else -1.0)

                transform = QTransform()
                transform.translate(fixed_point.x(), fixed_point.y())
                transform.scale(sx, sy)
                transform.translate(-fixed_point.x(), -fixed_point.y())

                avg_scale = (abs(sx) + abs(sy)) / 2.0

                for idx in self.docker.selected_indices:
                    if idx in self.initial_paths_map:
                        new_path = transform.map(self.initial_paths_map[idx])
                        orig_width = self.initial_widths_map.get(idx, 1.0)
                        new_width = orig_width * avg_scale
                        _, col, _ = self.docker.stored_paths[idx]
                        self.docker.stored_paths[idx] = (new_path, col, new_width)
            self.update()

    def inputRelease(self):
        if self.docker.mode == "KRITA_DRAW":
            return

        if self.docker.mode == "ANNOTATE" and self.current_path:
            try:
                last_mouse_pos = self.map_screen_to_doc(self.mapToGlobal(self.mapFromGlobal(QCursor.pos())))
                self.current_path.lineTo(last_mouse_pos)
            except RuntimeError:
                pass

            self.commit_state()
            final_path = self.apply_post_processing(self.current_path)
            self.docker.stored_paths.append((final_path, self.docker.current_color, self.docker.line_width))
            self.current_path = None
            self.update()
            self.save_to_document_deferred()

        elif self.is_selecting_area:
            self.is_selecting_area = False
            sel_rect = QRectF(self.selection_start_doc, self.selection_current_doc).normalized()
            for i, (path, _, _) in enumerate(self.docker.stored_paths):
                if path.intersects(sel_rect) or sel_rect.contains(path.boundingRect()):
                    self.docker.selected_indices.add(i)
            self.update()

        elif self.docker.mode == "MOVE":
            self.active_handle = H_NONE
            self.initial_paths_map = {}
            self.initial_widths_map = {}
            self.save_to_document_deferred()

    def tabletEvent(self, e):
        e.ignore()


class AnnotationDocker(QDockWidget):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Canvas Annotations Tool")
        self.stored_paths = []
        self.current_color = QColor(0, 0, 0)
        self.line_width = 4.0
        self.mode = "ANNOTATE"
        self.selected_indices = set()

        self.target_viewport = None
        self.overlay = None

        widget = QWidget()
        layout = QVBoxLayout()
        widget.setLayout(layout)

        self.btn_toggle = QPushButton("ACTIVATE OVERLAY")
        self.btn_toggle.setCheckable(True)
        self.btn_toggle.setStyleSheet("QPushButton:checked { background-color: #28a745; color: white; font-weight: bold; }")
        self.btn_toggle.clicked.connect(self.toggle_overlay)

        tools = QHBoxLayout()
        self.btn_annotate = QPushButton("Anototate")
        self.btn_annotate.setCheckable(True)
        self.btn_annotate.setChecked(True)

        self.btn_move = QPushButton("Move/Scale")
        self.btn_move.setCheckable(True)

        self.btn_krita_draw = QPushButton("Draw (Krita)")
        self.btn_krita_draw.setCheckable(True)

        self.btn_group = QButtonGroup(self)
        self.btn_group.addButton(self.btn_annotate)
        self.btn_group.addButton(self.btn_move)
        self.btn_group.addButton(self.btn_krita_draw)

        self.btn_annotate.clicked.connect(lambda: self.set_mode("ANNOTATE"))
        self.btn_move.clicked.connect(lambda: self.set_mode("MOVE"))
        self.btn_krita_draw.clicked.connect(lambda: self.set_mode("KRITA_DRAW"))

        tools.addWidget(self.btn_annotate)
        tools.addWidget(self.btn_move)
        tools.addWidget(self.btn_krita_draw)

        props_layout = QHBoxLayout()
        self.btn_color_preview = QPushButton()
        self.btn_color_preview.setFixedSize(24, 24)
        self.update_color_button()
        self.btn_color_preview.clicked.connect(self.change_color)

        self.slider_size = QSlider(Qt.Horizontal)
        self.slider_size.setRange(1, 50)
        self.slider_size.setValue(int(self.line_width))
        self.slider_size.setFixedWidth(100)
        self.slider_size.valueChanged.connect(self.update_size)

        self.lbl_size_value = QLabel(f"{int(self.line_width)} px")

        props_layout.addWidget(QLabel("Color:"))
        props_layout.addWidget(self.btn_color_preview)
        props_layout.addSpacing(10)
        props_layout.addWidget(QLabel("Brush Size:"))
        props_layout.addWidget(self.slider_size)
        props_layout.addWidget(self.lbl_size_value)
        props_layout.addStretch()

        self.btn_clear = QPushButton("Erase All")
        self.btn_clear.setStyleSheet("margin-top: 10px;")
        self.btn_clear.clicked.connect(self.clear_all)

        layout.addWidget(self.btn_toggle)
        layout.addLayout(tools)
        layout.addLayout(props_layout)
        layout.addStretch()
        layout.addWidget(self.btn_clear)

        self.setWidget(widget)
        self.sync_timer = QTimer(self)
        self.sync_timer.timeout.connect(self.sync_geometry)

        # --- SISTEMA MULTI-DOCUMENTO ---
        self.krita = Krita.instance()
        self.notifier = self.krita.notifier()

        try:
            if hasattr(self.notifier, "viewCreated"):
                self.notifier.viewCreated.connect(self.on_view_created)
        except Exception: pass
        try:
            if hasattr(self.notifier, "viewClosed"):
                self.notifier.viewClosed.connect(self.on_view_closed)
        except Exception: pass
        try:
            if hasattr(self.notifier, "imageCreated"):
                self.notifier.imageCreated.connect(self.on_image_created)
        except Exception: pass
        try:
            if hasattr(self.notifier, "windowCreated"):
                self.notifier.windowCreated.connect(self.on_window_created)
        except Exception: pass

        self.aw = None
        try:
            self.aw = self.krita.activeWindow()
            if self.aw and hasattr(self.aw, "activeViewChanged"):
                self.aw.activeViewChanged.connect(self.on_active_view_changed)
        except Exception: pass

        QTimer.singleShot(1000, self.load_settings)

    def on_active_view_changed(self, *args, **kwargs):
        try:
            aw = self.krita.activeWindow()
            if aw:
                view = aw.activeView()
                if view:
                    self.on_active_document_changed(view.document())
                    return
        except Exception: pass
        self.on_active_document_changed(self.krita.activeDocument())

    def on_view_created(self, view):
        try:
            self.on_active_document_changed(view.document())
        except Exception:
            self.on_active_document_changed(self.krita.activeDocument())

    def on_view_closed(self, view):
        try:
            self.on_active_document_changed(self.krita.activeDocument())
        except Exception:
            self.on_active_document_changed(None)

    def on_image_created(self, document):
        self.on_active_document_changed(document)

    def on_window_created(self, *args):
        try:
            try:
                if self.aw and hasattr(self.aw, "activeViewChanged"):
                    self.aw.activeViewChanged.disconnect(self.on_active_view_changed)
            except Exception: pass
            self.aw = self.krita.activeWindow()
            if self.aw and hasattr(self.aw, "activeViewChanged"):
                self.aw.activeViewChanged.connect(self.on_active_view_changed)
        except Exception: pass

    def on_active_document_changed(self, doc):
        self.stored_paths = []
        self.selected_indices.clear()
        if self.overlay:
            try:
                self.overlay.undo_stack.clear()
                self.overlay.redo_stack.clear()
            except Exception: pass

        if doc:
            try:
                self.load_settings()
                # Si load_settings detectó que estaba activo, llamará a toggle_overlay(True)
                # Si no, aseguramos que si el botón está checkeado, se cree el overlay para el nuevo doc
                if self.btn_toggle.isChecked() and not self.overlay:
                    self.toggle_overlay(True)
            except Exception: pass
        else:
            # Sin documento, aseguramos limpieza
            self.target_viewport = None

    def serialize_path(self, path):
        elements = []
        for i in range(path.elementCount()):
            e = path.elementAt(i)
            elements.append((e.type, e.x, e.y))
        return elements

    def deserialize_path(self, elements):
        path = QPainterPath()
        if not elements: return path
        i = 0
        while i < len(elements):
            try:
                t, x, y = elements[i]
            except Exception:
                i += 1
                continue
            if t == 0:
                path.moveTo(x, y)
                i += 1
            elif t == 1:
                path.lineTo(x, y)
                i += 1
            else:
                path.lineTo(x, y)
                i += 1
        return path

    def save_settings(self):
        doc = Krita.instance().activeDocument()
        if not doc: return

        path_data = []
        for path, color, width in self.stored_paths:
            try:
                c_name = color.name(QColor.HexArgb) if isinstance(color, QColor) else QColor(color).name(QColor.HexArgb)
            except Exception:
                c_name = "#00000000"
            path_data.append({
                "path": self.serialize_path(path),
                "color": c_name,
                "width": width
            })

        data = {
            "paths": path_data,
            "last_color": self.current_color.name(QColor.HexArgb),
            "last_size": self.line_width,
            "is_active": self.btn_toggle.isChecked()
        }

        try:
            json_str = json.dumps(data)
            doc.setAnnotation(ANNOTATION_KEY, "Plugin Data", QByteArray(json_str.encode('utf-8')))
        except Exception: pass

    def load_settings(self):
        doc = Krita.instance().activeDocument()
        if not doc: return

        try:
            byte_array = doc.annotation(ANNOTATION_KEY)
        except Exception: return

        if not byte_array or byte_array.isEmpty(): return

        try:
            raw = byte_array.data()
            if isinstance(raw, bytes):
                text = raw.decode('utf-8', errors='ignore')
            else:
                try:
                    text = bytes(raw).decode('utf-8', errors='ignore')
                except Exception:
                    text = str(raw)
            data = json.loads(text)

            self.stored_paths = []
            for item in data.get("paths", []):
                path = self.deserialize_path(item.get("path", []))
                color = QColor(item.get("color", "#000000FF"))
                width = float(item.get("width", 1.0))
                self.stored_paths.append((path, color, width))

            if "last_color" in data:
                try:
                    self.current_color = QColor(data["last_color"])
                    self.update_color_button()
                except Exception: pass

            if "last_size" in data:
                try:
                    size = float(data["last_size"])
                    self.line_width = size
                    self.slider_size.setValue(int(size))
                    self.lbl_size_value.setText(f"{int(size)} px")
                except Exception: pass

            # Activar si estaba guardado como activo
            if data.get("is_active", False):
                if not self.btn_toggle.isChecked():
                    self.btn_toggle.setChecked(True)
                # Forzar toggle para crear el overlay en el nuevo viewport
                self.toggle_overlay(True)

        except Exception: pass

    def closeEvent(self, event):
        try:
            if hasattr(self, "notifier") and self.notifier:
                # desconectar señales si es posible
                pass
        except Exception: pass

        try:
            if self.overlay:
                self.overlay.close()
                self.overlay = None
        except Exception: pass

        try:
            self.sync_timer.stop()
        except Exception: pass

        super().closeEvent(event)

    def find_canvas_viewport(self):
        try:
            app = Krita.instance()
            active_window = app.activeWindow()
            if not active_window: return None
            qwin = active_window.qwindow()
            mdi = qwin.findChild(QMdiArea)
            if mdi and mdi.currentSubWindow():
                scroll_area = mdi.currentSubWindow().findChild(QAbstractScrollArea)
                if scroll_area: return scroll_area.viewport()
        except Exception: pass
        return None

    def _get_overlay_safe(self):
        """Helper para obtener el overlay solo si es válido (C++ object alive)."""
        if self.overlay:
            try:
                # Intentar acceder a un método ligero para ver si el objeto C++ existe
                if self.overlay.isVisible is not None:
                    return self.overlay
            except RuntimeError:
                self.overlay = None
        return None

    def sync_geometry(self):
        # Verificar viewport
        try:
            if not getattr(self, "target_viewport", None):
                self.target_viewport = self.find_canvas_viewport()
            else:
                try:
                    if not self.target_viewport.isVisible():
                        self.target_viewport = self.find_canvas_viewport()
                except RuntimeError:
                    self.target_viewport = self.find_canvas_viewport()
        except Exception:
            self.target_viewport = self.find_canvas_viewport()

        # Verificar overlay de forma segura antes de usarlo
        if self.overlay:
            try:
                if not self.overlay.isVisible():
                    return
                
                if not Krita.instance().activeWindow():
                    self.overlay.close()
                    return
                
                if self.target_viewport:
                    size = self.target_viewport.size()
                    geo = QRect(0, 0, size.width(), size.height())
                    if self.overlay.geometry() != geo:
                        self.overlay.setGeometry(geo)
                    self.overlay.update()
            except RuntimeError:
                self.overlay = None
                self.target_viewport = None
            except Exception: pass

    def toggle_overlay(self, checked):
        if checked:
            self.target_viewport = self.find_canvas_viewport()
            
            if self.target_viewport:
                # Verificar overlay existente
                if self.overlay:
                    try:
                        # Si existe pero es de otro padre, recrear
                        if self.overlay.parent() != self.target_viewport:
                            self.overlay.close()
                            self.overlay = None
                    except RuntimeError:
                        self.overlay = None

                if not self.overlay:
                    self.overlay = OverlayWidget(self, parent=self.target_viewport)
                
                if not self.stored_paths:
                    # Cargar datos si está vacío (recién creado)
                    # Evitar recursión infinita si load_settings llama a toggle_overlay
                    pass 
                
                try:
                    # FIX: Force Krita to clear cursor/artifacts
                    # Send Leave event with a slight delay to let the viewport settle
                    QTimer.singleShot(50, lambda: self.force_cursor_clear())
                    
                    self.overlay.show()
                    self.overlay.raise_()
                    self.overlay.setFocus()
                except Exception: pass
                
                self.sync_timer.start(16)

                if self.btn_annotate.isChecked(): self.set_mode("ANNOTATE")
                elif self.btn_move.isChecked(): self.set_mode("MOVE")
                elif self.btn_krita_draw.isChecked(): self.set_mode("KRITA_DRAW")
                self.save_settings()
            else:
                self.btn_toggle.setChecked(False)
        else:
            if self.overlay:
                try:
                    self.overlay.hide()
                except Exception: pass
            try:
                self.sync_timer.stop()
            except Exception: pass
            self.save_settings()

    def force_cursor_clear(self):
        if self.target_viewport:
            try:
                self.target_viewport.update()
                QApplication.sendEvent(self.target_viewport, QEvent(QEvent.Leave))
            except Exception: pass

    def set_mode(self, mode):
        self.mode = mode
        if mode == "ANNOTATE": self.selected_indices.clear()

        overlay = self._get_overlay_safe()
        if overlay:
            try:
                if mode == "KRITA_DRAW":
                    overlay.setAttribute(Qt.WA_TransparentForMouseEvents, True)
                else:
                    overlay.setAttribute(Qt.WA_TransparentForMouseEvents, False)
                    # FIX: Re-send Leave event to viewport to hide Krita cursor
                    QTimer.singleShot(50, lambda: self.force_cursor_clear())

                overlay.update_cursor()
                overlay.update()
            except RuntimeError:
                self.overlay = None
            except Exception: pass

    def clear_all(self):
        overlay = self._get_overlay_safe()
        if overlay: 
            try:
                overlay.commit_state()
            except Exception: pass
            
        self.stored_paths = []
        self.selected_indices.clear()
        
        if overlay:
            try:
                overlay.update()
            except Exception: pass
        self.save_settings()

    def change_color(self):
        color = QColorDialog.getColor(self.current_color)
        if color.isValid():
            self.current_color = color
            self.update_color_button()
            self.save_settings()

    def update_color_button(self):
        try:
            self.btn_color_preview.setStyleSheet(
                f"background-color: {self.current_color.name()}; border: 1px solid #555; border-radius: 2px;"
            )
        except Exception: pass

    def update_size(self, value):
        self.line_width = float(value)
        try:
            self.lbl_size_value.setText(f"{value} px")
        except Exception: pass
        
        overlay = self._get_overlay_safe()
        if overlay:
            try:
                overlay.update()
            except Exception: pass
        self.save_settings()


class AnnotationDockerFactory(DockWidgetFactoryBase):
    def __init__(self):
        super().__init__("screen_annotation_docker", DockWidgetFactoryBase.DockRight)

    def createDockWidget(self):
        return AnnotationDocker()