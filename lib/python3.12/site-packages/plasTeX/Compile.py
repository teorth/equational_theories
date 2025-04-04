import os, sys, string, glob
import importlib
import importlib.util
from types import ModuleType
from pathlib import Path
import pdb
import plasTeX
from plasTeX.TeX import TeX
from plasTeX.ConfigManager import *
from plasTeX.Logging import getLogger, updateLogLevels
from plasTeX.Renderers import Renderer

log = getLogger()

def import_file(path: Path) -> ModuleType:
    module_name = path.name
    while module_name in sys.modules:
        module_name = module_name + "_"

    # Using path.absolute() makes sure the __file__ property of the module is
    # absolute, which is important since we may change directories later.
    spec = importlib.util.spec_from_file_location(module_name, str(path.absolute() / "__init__.py"))
    if spec is None:
        raise ImportError

    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    if spec.loader is None:
        raise ImportError()
    spec.loader.exec_module(module) # type: ignore # mypy doesn't understand importlib well enough
    return module

def load_renderer(rname: str, config: ConfigManager) -> Renderer:
    """Load a renderer by name. First look by name among builtin renderers,
    then among renderers provided by plugins, and then try interpreting rname
    as a path."""
    try:
        return getattr(importlib.import_module('plasTeX.Renderers.'+rname), 'Renderer')()
    except ImportError:
        pass

    for plugin in config['general']['plugins'] or []:
        try:
            return getattr(importlib.import_module(plugin + '.Renderers.' + rname),
                           'Renderer')()
        except ImportError:
            pass

    try:
        return getattr(import_file(Path(rname)), 'Renderer')()
    except (ImportError, FileNotFoundError):
        raise ImportError('Could not import renderer "%s".  Make sure that it is installed correctly, and can be imported by Python.' % rname)


def parse(filename: str, config: ConfigManager) -> TeX:
    updateLogLevels(config['logging']['logging'])

    # Create document instance that output will be put into
    document = plasTeX.TeXDocument(config=config)

    # Instantiate the TeX processor
    tex = TeX(document, file=filename)

    # Send log message to file "jobname.log" instead of console
    if config['files']['log']:
        tex.fileLogging()

    # Populate variables for use later
    if config['document']['title']:
        document.userdata['title'] = config['document']['title']

    jobname = document.userdata['jobname'] = tex.jobname
    cwd = document.userdata['working-dir'] = os.getcwd()

    # Load aux files for cross-document references
    pauxname = '%s.paux' % jobname
    rname = config['general']['renderer']
    for dirname in [cwd] + config['general']['paux-dirs']:
        for fname in glob.glob(os.path.join(dirname, '*.paux')):
            if os.path.basename(fname) == pauxname:
                continue
            document.context.restore(fname, rname)

    # Parse the document
    tex.parse()
    return tex

def run(filename: str, config: ConfigManager):
    rname = config['general']['renderer']
    tex = parse(filename, config)
    document = tex.ownerDocument
    cwd = document.userdata['working-dir'] = os.getcwd()
    jobname = document.userdata['jobname'] = tex.jobname

    if config['general']['debug']:
        print("\n\nWill now start the python debugger. Please inspect the "
              "document variable.\n"
              "Useful methods include \n* print(document.toXML())\n"
              "* document.childNodes\n* document.getElementsByTagName\n"
              "If needed, you should install ipdb to replace pdb.\n"
              "Also consider installing BeautifulSoup4 and using\n"
              "from bs4 import BeautifulSoup; print(BeautifulSoup(document.toXML(), 'xml').prettify())")
        pdb.set_trace()
    renderer = load_renderer(rname, config)

    # Change to specified directory to output to
    outdir = config['files']['directory']
    if outdir:
        outdir = string.Template(outdir).substitute({'jobname':jobname})
        if not os.path.isdir(outdir):
            os.makedirs(outdir)
        log.info('Directing output files to directory: %s.' % outdir)
        os.chdir(outdir)

    # Write expanded source file
    #sourcefile = '%s.source' % jobname
    #open(sourcefile,'w').write(document.source.encode('utf-8'))

    # Write XML dump
    if config['general']['xml']:
        outfile = '%s.xml' % jobname
        with open(outfile,'w',encoding='utf-8') as f:
            f.write(document.toXML())

    # Apply renderer
    renderer.render(document)

    os.chdir(cwd)
    print()
