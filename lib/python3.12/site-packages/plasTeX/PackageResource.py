import re, shutil
from pathlib import Path
from typing import Union, List, Any, Optional

from plasTeX.Logging import getLogger
from plasTeX.Renderers.PageTemplate import Renderer
from plasTeX.TeX import TeXDocument

log = getLogger()

class PackageResource:
    outdir = ''
    copy = False
    key = ''

    def __init__(self, renderers: Optional[Union[List[str], str]] = None,
                 path: Optional[Path] = None, data: Any = None, **kwargs):
        if isinstance(renderers, list):
            self.rendererPatterns = renderers
        elif renderers is None:
            self.rendererPatterns = ['html5']
        else:
            self.rendererPatterns = [renderers]
        self.path = path
        self.data = data

    def alter(self, renderer: Renderer, rendererName: str, document: TeXDocument,
              target: Path) -> None:
        for pattern in self.rendererPatterns:
            if re.match(pattern, rendererName):
                self.alterRenderer(renderer)
                self.alterDocument(document=document, rendererName=rendererName)
                self.copyFile(target)
                return

    def alterRenderer(self, renderer: Renderer) -> None:
        pass

    def alterDocument(self, document: TeXDocument, rendererName: str) -> None:
        rendererdata = document.rendererdata[rendererName]
        if self.key:
            if isinstance(self.data, list):
                data = self.data
            else:
                data = [self.data]
            rendererdata.setdefault(self.key, []).extend(data)

    def copyFile(self, target: Optional[Path] =None) -> None:
        if self.copy and target:
            (target/self.outdir).mkdir(parents=True, exist_ok=True)
            try:
                shutil.copy(str(self.path), str(target/self.outdir))
            except IOError:
                log.error('Package resource cannot be copied :' + str(self.path))


class PackageCss(PackageResource):
    outdir = 'styles'
    key = 'css'
    copy = True

    def __init__(self, renderers: Optional[Union[List[str], str]] = None,
            path: Optional[Path] = None, data: Any = None, copy_only: bool = False):
        super().__init__(renderers, path, data)
        if path is None:
            raise ValueError('PackageCss path was not provided')
        self.data = path.name
        if copy_only:
            self.key = ''

class PackageJs(PackageResource):
    outdir = 'js'
    key = 'js'
    copy = True

    def __init__(self, renderers: Optional[Union[List[str], str]] = None,
                 path: Optional[Path] = None, data: Any = None, copy_only: bool = False):
        super().__init__(renderers, path, data)
        if path is None:
            raise ValueError('PackageJs path was not provided')
        self.data = path.name
        if copy_only:
            self.key = ''

class PackageTemplateDir(PackageResource):
    """A directory of templates to load, specified using the path argument."""
    def alterRenderer(self, renderer: Renderer) -> None:
        renderer.importDirectory(str(self.path))

class PackagePreCleanupCB(PackageResource):
    key = 'preCleanupCallbacks'

class PackageProcessFilecontents(PackageResource):
    key = 'processFileContents'
