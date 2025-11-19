from krita import Krita
from .annotation_tool import AnnotationDockerFactory

# Obtenemos la instancia de Krita
app = Krita.instance()

# Creamos la fábrica
docker_factory = AnnotationDockerFactory()

# Registramos la fábrica en KritSa
app.addDockWidgetFactory(docker_factory)