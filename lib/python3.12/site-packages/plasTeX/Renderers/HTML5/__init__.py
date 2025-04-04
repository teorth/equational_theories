import subprocess, shlex
import os, shutil, re
from pathlib import Path
from typing import IO
from plasTeX.Renderers.PageTemplate import Renderer as _Renderer
from plasTeX.Renderers.HTML5.Config import addConfig
from plasTeX.Logging import getLogger

log = getLogger()

class HTML5(_Renderer):
    """Renderer targetting HTML5."""

    fileExtension = '.html'
    imageTypes = ['.svg', '.png','.jpg','.jpeg','.gif']
    vectorImageTypes = ['.svg']
    vectorBitmap = False

    def loadTemplates(self, document):
        """Load templates as in PageTemplate but also look for packages that
        want to override some templates and handles extra css and javascript."""

        _Renderer.loadTemplates(self, document)
        rendererdata = document.rendererdata.setdefault('html5', dict())
        config = document.config
        if 'html5' not in config:
            addConfig(config)

        srcDir = document.userdata.get('working-dir', '.') # type: str
        buildDir = os.getcwd()

        # Theme css has already been copied by PageTemplate.loadTemplates,
        # provided config['general']['copy-theme-extras'] is true
        # Still try to create styles directory is case it's false
        try:
            os.mkdir('styles')
        except OSError:
            # This should mean the directory already exists
            pass

        # Start building the css list for use by the layout template
        if config['html5']['use-theme-css'] and config['general']['copy-theme-extras']:
            rendererdata['css'] = ['theme-' + config['html5']['theme-css'] + '.css']
        else:
            rendererdata['css'] = []

        # Theme js has already been copied by PageTemplate.loadTemplates,
        # provided config['general']['copy-theme-extras'] is true
        # Still try to create js directory is case it's false
        try:
            os.mkdir('js')
        except OSError:
            pass

        # Start building the js list for use by the layout template
        if self.loadedTheme:
            theme_js_path = Path(self.loadedTheme)/'js'
            if (config['html5']['use-theme-js'] and
                    config['general']['copy-theme-extras'] and
                    theme_js_path.exists()):
                rendererdata['js'] = sorted(path.name
                        for path in theme_js_path.glob('*.js'))
            else:
                rendererdata['js'] = []

        for resrc in document.packageResources:
            # Next line may load templates or change
            # document.rendererdata['html5'] or copy some files to buildDir
            resrc.alter(
                    renderer=self,
                    rendererName='html5',
                    document=document,
                    target=Path(buildDir))

        # Last loaded files (hence overriding everything else) come from user
        # configuration
        cssBuildDir = os.path.join(buildDir, 'styles')
        for css in config['html5']['extra-css']:
            rendererdata['css'].append(css)
            try:
                shutil.copy(os.path.join(srcDir, css), cssBuildDir)
            except FileNotFoundError:
                log.error('File ' + css + ' not found')
            except IOError as err:
                log.error(str(err))

        jsBuildDir = os.path.join(buildDir, 'js')
        for js in config['html5']['extra-js']:
            rendererdata['js'].append(js)
            try:
                shutil.copy(os.path.join(srcDir, js), jsBuildDir)
            except FileNotFoundError:
                log.error('File ' + js + ' not found')
            except IOError as err:
                log.error(str(err))

    def processFileContent(self, document, s):
        s = _Renderer.processFileContent(self, document, s)

        # Remove empty paragraphs
        s = re.compile(r'<p>\s*</p>', re.I).sub(r'', s)

        # Add a non-breaking space to empty table cells
        s = re.compile(r'(<(td|th)\b[^>]*>)\s*(</\2>)', re.I).sub(r'\1&nbsp;\3', s)

        for fun in document.rendererdata['html5'].get('processFileContents', []):
            s = fun(document, s)

        filters = document.config['html5']['filters']
        for filter_ in filters:
            proc = subprocess.Popen(
                    shlex.split(filter_),
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE)
            output, output_err = proc.communicate(s.encode(encoding="utf-8"))
            if not output_err:
                s = output.decode(encoding="utf-8")

        return s

    def cleanup(self, document, files, postProcess=None):
        """
        Cleanup method called at the end of rendering.
        Uses the base renderer cleanup but calls packages callbacks before and
        after. Callbacks should be listed in
        document.userdata['preCleanupCallbacks']
        or document.userdata['postCleanupCallbacks']. Each call back should accept the
        current document as its only argument. Pre-cleanup call back must return
        the list of path of files they created (relative to the output directory).
        """

        rendererdata = document.rendererdata.get('html5', dict())
        preCleanupCallbacks = rendererdata.get('preCleanupCallbacks', [])
        for preCleanupCallback in preCleanupCallbacks:
            files += preCleanupCallback(document)

        _Renderer.cleanup(self, document, files, postProcess)


Renderer = HTML5
