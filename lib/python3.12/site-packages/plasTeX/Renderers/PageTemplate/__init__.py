"""
Generic Page Template Renderer

This module contains a plasTeX renderer that uses various types of page
templates as the templating engine.  It also makes it possible to add
support for your own templating engines.

"""

import sys, os, re, plasTeX, shutil, string
from io import StringIO
import pdb
from plasTeX.Renderers import Renderer as BaseRenderer
from plasTeX.Renderers.PageTemplate.simpletal import simpleTAL, simpleTALES
from plasTeX.Renderers.PageTemplate.simpletal.simpleTALES import Context as TALContext

log = plasTeX.Logging.getLogger()

# Support for Jinja2 templates
try:
    from jinja2 import Environment
    import jinja2.exceptions
except ImportError:
    def jinja2template(s, encoding='utf8'):
        def renderjinja2(obj):
            return s
        return renderjinja2
else:
    try:
        from jinja2 import pass_context
    except ImportError:
        from jinja2 import contextfunction as pass_context  # type: ignore

    import jinja2.exceptions
    @pass_context
    def debug(context):
        obj = context["obj"]
        config = context["config"]
        print("\n\nWill now start a debugger in the context of the following template:\n")
        print(context['tpl_src'])
        print("\nYou can inspect obj and config.\n")
        pdb.set_trace()

    def jinja2template(s, encoding='utf8'):
        env = Environment(trim_blocks=True, lstrip_blocks=True)
        env.globals['debug'] = debug

        def renderjinja2(obj, s=s):
            tvars = {'here':obj,
                     'obj':obj,
                     'doc':obj.ownerDocument,
                     'container':obj.parentNode,
                     'config':obj.ownerDocument.config,
                     'context':obj.ownerDocument.context,
                     'templates':obj.renderer,
                     'tpl_src': s}

            tpl = env.from_string(s)
            try:
                return tpl.render(tvars)
            except jinja2.exceptions.TemplateError as e:
                log.warning('Jinja2 template error: {} while rendering node {}'
                            ' with source\n {}\n'.format(
                            e, obj.nodeName, obj.source))
                return ''


        return renderjinja2

# Support for Python string templates
def stringtemplate(s):
    template = string.Template(s)
    def renderstring(obj):
        tvars = {'here':obj, 'self':obj, 'container':obj.parentNode,
                 'config':obj.ownerDocument.config, 'template':template,
                 'templates':obj.renderer, 'context':obj.ownerDocument.context}
        return template.substitute(tvars)
    return renderstring

# Support for Python string interpolations
def pythontemplate(s):
    template = s
    def renderpython(obj):
        tvars = {'here':obj, 'self':obj, 'container':obj.parentNode,
                 'config':obj.ownerDocument.config, 'template':template,
                 'templates':obj.renderer, 'context':obj.ownerDocument.context}
        return template % tvars
    return renderpython

# Support for ZPT HTML and XML templates
def htmltemplate(s):
    template = simpleTAL.compileHTMLTemplate(s)
    def renderhtml(obj):
        context = TALContext(allowPythonPath=1)
        context.addGlobal('here', obj)
        context.addGlobal('self', obj)
        context.addGlobal('container', obj.parentNode)
        context.addGlobal('config', obj.ownerDocument.config)
        context.addGlobal('context', obj.ownerDocument.context)
        context.addGlobal('template', template)
        context.addGlobal('templates', obj.renderer)
        output = StringIO()
        template.expand(context, output)
        return output.getvalue()
    return renderhtml

def xmltemplate(s):
    template = simpleTAL.compileXMLTemplate(s)
    def renderxml(obj):
        context = TALContext(allowPythonPath=1)
        context.addGlobal('here', obj)
        context.addGlobal('self', obj)
        context.addGlobal('container', obj.parentNode)
        context.addGlobal('config', obj.ownerDocument.config)
        context.addGlobal('context', obj.ownerDocument.context)
        context.addGlobal('template', template)
        context.addGlobal('templates', obj.renderer)
        output = StringIO()
        template.expand(context, output, docType=None, suppressXMLDeclaration=1)
        return output.getvalue()
    return renderxml

# Support for Cheetah templates
try:

   from Cheetah.Template import Template as CheetahTemplate
   from Cheetah.Filters import Filter as CheetahFilter
   class CheetahUnicode(CheetahFilter):
       def filter(self, val, **kw):
           return str(val)
   def cheetahtemplate(s):
       def rendercheetah(obj, s=s):
           tvars = {'here':obj, 'container':obj.parentNode,
                    'config':obj.ownerDocument.config,
                    'context':obj.ownerDocument.context,
                    'templates':obj.renderer}
           return CheetahTemplate(source=s, searchList=[tvars],
                                  filter=CheetahUnicode).respond()
       return rendercheetah

except (ImportError, AttributeError):

   def cheetahtemplate(s):
       def rendercheetah(obj):
           return str(s)
       return rendercheetah

# Support for Kid templates
try:

    from kid import Template as KidTemplate

    def kidtemplate(s):
        # Add namespace py: in
        s = '<div xmlns:py="http://purl.org/kid/ns#" py:strip="True">%s</div>' % s
        def renderkid(obj, s=s):
            tvars = {'here':obj, 'container':obj.parentNode,
                     'config':obj.ownerDocument.config,
                     'context':obj.ownerDocument.context,
                     'templates':obj.renderer}
            return str(KidTemplate(source=s, **tvars).serialize(fragment=1))
        return renderkid

except ImportError:

    def kidtemplate(s):
        def renderkid(obj):
            return str(s)
        return renderkid

# Support for Genshi templates
try:

    from genshi.template import MarkupTemplate as GenshiTemplate
    from genshi.template import TextTemplate as GenshiTextTemplate
    from genshi.core import Markup

    def markup(obj):
        return Markup(str(obj))

    def genshixmltemplate(s):
        # Add namespace py: in
        s = '<div xmlns:py="http://genshi.edgewall.org/" py:strip="True">%s</div>' % s
        template = GenshiTemplate(s)
        def rendergenshixml(obj):
            tvars = {'here':obj, 'container':obj.parentNode, 'markup':markup,
                     'config':obj.ownerDocument.config, 'template':template,
                     'context':obj.ownerDocument.context,
                     'templates':obj.renderer}
            return str(template.generate(**tvars).render(method='xml'))
        return rendergenshixml

    def genshihtmltemplate(s):
        # Add namespace py: in
        s = '<div xmlns:py="http://genshi.edgewall.org/" py:strip="True">%s</div>' % s
        template = GenshiTemplate(s)
        def rendergenshihtml(obj):
            tvars = {'here':obj, 'container':obj.parentNode, 'markup':markup,
                     'config':obj.ownerDocument.config, 'template':template,
                     'context':obj.ownerDocument.context,
                     'templates':obj.renderer}
            return str(template.generate(**tvars).render(method='html'))
        return rendergenshihtml

    def genshitexttemplate(s):
        template = GenshiTextTemplate(s)
        def rendergenshitext(obj):
            tvars = {'here':obj, 'container':obj.parentNode, 'markup':markup,
                     'config':obj.ownerDocument.config, 'template':template,
                     'context':obj.ownerDocument.context,
                     'templates':obj.renderer}
            return str(template.generate(**tvars).render(method='text'))
        return rendergenshitext

except ImportError:

    def genshixmltemplate(s):
        def rendergenshixml(obj):
            return str(s)
        return rendergenshixml

    def genshihtmltemplate(s):
        def rendergenshihtml(obj):
            return str(s)
        return rendergenshihtml

    def genshitexttemplate(s):
        def rendergenshitext(obj):
            return str(s)
        return rendergenshitext


def copytree(src, dest, symlink=None):
    """
    This is the same as shutil.copytree, but doesn't error out if the
    directories already exist.

    """
    for root, dirs, files in os.walk(src, True):
        for d in dirs:
            if d.startswith('.'):
                continue
            srcpath = os.path.join(root, d)
            destpath = os.path.join(dest, root, d)
            if symlink and os.path.islink(srcpath):
                if os.path.exists(destpath):
                    os.remove(destpath)
                os.symlink(os.readlink(srcpath), destpath)
            elif not os.path.isdir(destpath):
                os.makedirs(destpath)
                try:
                    shutil.copymode(srcpath, destpath)
                except: pass
                try:
                    shutil.copystat(srcpath, destpath)
                except: pass
        for f in files:
            if f.startswith('.'):
                continue
            srcpath = os.path.join(root, f)
            destpath = os.path.join(dest, root, f)
            if symlink and os.path.islink(srcpath):
                if os.path.exists(destpath):
                    os.remove(destpath)
                os.symlink(os.readlink(srcpath), destpath)
            else:
                shutil.copy2(srcpath, destpath)

class TemplateEngine(object):
    def __init__(self, ext, function):
        if not isinstance(ext, (list,tuple)):
            ext = [ext]
        self.ext = ext
        self.function = function
    def compile(self, *args, **kwargs):
        return self.function(*args, **kwargs)

class PageTemplate(BaseRenderer):
    """ Renderer for page template based documents """

    outputType = str
    fileExtension = '.xml'

    def __init__(self, *args, **kwargs):
        BaseRenderer.__init__(self, *args, **kwargs)
        self.loadedTheme = None
        self.engines = {}
        htmlexts = ['.html','.htm','.xhtml','.xhtm','.zpt','.pt']
        self.registerEngine('pt', None, htmlexts, htmltemplate)
        self.registerEngine('zpt', None, htmlexts, htmltemplate)
        self.registerEngine('zpt', 'xml', '.xml', xmltemplate)
        self.registerEngine('tal', None, htmlexts, htmltemplate)
        self.registerEngine('tal', 'xml', '.xml', xmltemplate)
        self.registerEngine('html', None, htmlexts, htmltemplate)
        self.registerEngine('xml', 'xml', '.xml', xmltemplate)
        self.registerEngine('python', None, '.pyt', pythontemplate)
        self.registerEngine('string', None, '.st', stringtemplate)
        self.registerEngine('kid', None, '.kid', kidtemplate)
        self.registerEngine('cheetah', None, '.che', cheetahtemplate)
        self.registerEngine('genshi', None, '.gen', genshihtmltemplate)
        self.registerEngine('genshi', 'xml', '.genx', genshixmltemplate)
        self.registerEngine('genshi', 'text', '.gent', genshitexttemplate)
        self.registerEngine('jinja2', None, '.jinja2', jinja2template)

    def registerEngine(self, name, type, ext, function):
        """
        Register a new type of templating engine

        Arguments:
        name -- the name of the engine
        type -- the type of output supported by the engine (e.g., html,
            xml, text, etc.)
        ext -- the file extensions associated with that template type
        function -- the function used to compile templates of that type

        """
        if not type:
            type = None
        key = (name, type)
        self.engines[key] = TemplateEngine(ext, function)

    def textDefault(self, node):
        """
        Default renderer for text nodes

        This method makes sure that special characters are converted to
        entities.

        Arguments:
        node -- the Text node to process

        """

        if not(getattr(node, 'isMarkup', None)):
            node = node.replace('&', '&amp;')
            node = node.replace('<', '&lt;')
            node = node.replace('>', '&gt;')
        return self.outputType(node)

    def loadTemplates(self, document):
        """ Load and compile page templates """
        themename = document.config['general']['theme']

        # Load templates from renderer directory and parent
        # renderer directories
        sup = list(type(self).__mro__)
        sup.reverse()
        themes = []
        for cls in sup:
            if cls is BaseRenderer or cls is object or cls is dict:
                continue
            cwd = os.path.dirname(sys.modules[cls.__module__].__file__)
            log.info('Importing templates from %s' % cwd)
            self.importDirectory(cwd)

            # Store theme location
            themes.append(os.path.join(cwd, 'Themes', themename))


            # Load templates configured by the environment variable
            templates = os.environ.get('%sTEMPLATES' % cls.__name__,'')
            for path in [x.strip() for x in templates.split(os.pathsep) if x.strip()]:
                log.info('Importing templates from %s' % path)
                self.importDirectory(path)
                themes.append(os.path.join(path, 'Themes', themename))

        working_dir = document.userdata.get('working-dir', '')
        # Load templates configured by the extra-templates option
        for path in document.config['general']['extra-templates']:
            full_path = os.path.join(working_dir, path)
            log.info('Importing templates from %s' % full_path)
            self.importDirectory(full_path)
            themes.append(os.path.join(path, 'Themes', themename))
        # Load only one theme
        for theme in reversed(themes):
            full_path = os.path.join(working_dir, theme)
            if os.path.isdir(full_path):
                log.info('Using theme %s' % theme)
                self.importDirectory(full_path)
                self.loadedTheme = theme

                extensions = []
                for e in self.engines.values():
                    extensions += e.ext + [x+'s' for x in e.ext]

                if document.config['general']['copy-theme-extras']:
                    # Copy all theme extras
                    cwd = os.getcwd()
                    os.chdir(full_path)
                    for item in os.listdir('.'):
                        if os.path.isdir(item):
                            if not os.path.isdir(os.path.join(cwd,item)):
                                os.makedirs(os.path.join(cwd,item))
                            copytree(item, cwd, True)
                        elif os.path.splitext(item)[-1].lower() not in extensions:
                            shutil.copy(item, os.path.join(cwd,item))
                    os.chdir(cwd)

                break

    def render(self, document):
        """ Load templates and render the document """
        self.loadTemplates(document)
        BaseRenderer.render(self, document)

    def importDirectory(self, templatedir):
        """
        Compile all templates files in the given directory

        Templates can exist in two different forms.  First, a template
        can be a file unto itself.  If an XML template is desired,
        the file should have an extension of .xml, .xhtml, or .xhtm.
        If an HTML template is desired, the files should have an
        extension of .zpt, .html, or .htm.  You can also configure
        your own page templates with their own extensions.

        If you have many small templates, or a template that corresponds
        to more than one macro, you can use a multiple ZPT file.  A
        multiple ZPT file contains directives within it to delimit
        individual page templates as well as specify which macros they
        correspond to and what type of template they are (i.e. XML or
        HTML).

        Required Arguments:
        templatedir -- the directory to search for template files

        """
        # Create a list for resolving aliases
        self.aliases = {}

        enames = {}
        for key, value in self.engines.items():
            for i in value.ext:
                enames[i+'s'] = key[0]

        singleenames = {}
        for key, value in self.engines.items():
            for i in value.ext:
                singleenames[i] = key[0]

        if templatedir and os.path.isdir(templatedir):
            files = sorted(os.listdir(templatedir))

            # Compile multi-pt files first
            for f in files:
                ext = os.path.splitext(f)[-1]
                f = os.path.join(templatedir, f)

                if not os.path.isfile(f):
                    continue

                # Multi-pt files
                if ext.lower() in enames:
                    self.parseTemplates(f, {'engine':enames[ext.lower()]})

            # Now compile macros in individual files.  These have
            # a higher precedence than macros found in multi-pt files.
            for f in files:
                basename, ext = os.path.splitext(f)
                f = os.path.join(templatedir, f)

                if not os.path.isfile(f):
                    continue

                options = {'name':basename}

                for value in self.engines.values():
                    if ext in value.ext:
                        options['engine'] = singleenames[ext.lower()]
                        self.parseTemplates(f, options)
                        del options['engine']
                        break

        if self.aliases:
           log.warning('The following aliases were unresolved: %s'
                       % ', '.join(list(self.aliases.keys())))

    def setTemplate(self, template, options):
        """
        Compile template and set it in the renderer

        Required Arguments:
        template -- the content of the template to be compiled
        options -- dictionary containing the name (or names) and type
            of the template

        """

        # Get name
        try:
            names = options['name'].split()
            if not names:
                names = [' ']
        except KeyError:
            raise ValueError('No name given for template')

        # If an alias was specified, link the names to the
        # already specified template.
        if 'alias' in options:
            alias = options['alias'].strip()
            for name in names:
                self.aliases[name] = alias
            if ''.join(template).strip():
                log.warning('Both an alias and a template were specified for: %s' % ', '.join(names))

        # Resolve remaining aliases
        for key, value in list(self.aliases.items()):
            if value in self:
                self[key] = self[value]
            self.aliases.pop(key)

        if 'alias' in options:
            return

        # Compile template and add it to the renderer
        template = ''.join(template).strip()
        ttype = options.get('type')
        if ttype is not None:
            ttype = ttype.lower()
        engine = options.get('engine','zpt').lower()

        templateeng = self.engines.get((engine, ttype),
                            self.engines.get((engine, None)))

        try:
            template = templateeng.compile(template)
        except Exception as msg:
            raise ValueError('Could not compile template "%s"' % names[0])

        for name in names:
            self[name] = template

    def parseTemplates(self, filename, options={}):
        """
        Parse templates from the file and set them in the renderer

        Required Arguments:
        filename -- file to parse templates from

        Keyword Arguments:
        options -- dictionary containing initial parameters for templates
            in the file

        """
        num_templates = 0
        template = []
        options = options.copy()
        defaults = options.copy()
        name = None
        if not options or 'name' not in options:
            with open(filename, 'r') as f:
                for i, line in enumerate(f):
                    # Found a meta-data command
                    if re.match(r'(default-)?\w+:', line):

                        # Purge any awaiting templates
                        if template:
                            try:
                                num_templates += 1
                                self.setTemplate(''.join(template), options)
                            except ValueError as msg:
                                print('ERROR: %s at line %s in file %s' % (msg, i, filename))
                            options = defaults.copy()
                            template = []

                        # Done purging previous template, start a new one
                        name, value = line.split(':', 1)
                        name = name.strip()
                        value = value.rstrip()
                        while value.endswith('\\'):
                            value = value[:-1] + ' '
                            for line in f:
                                value += line.rstrip()
                                break

                        value = re.sub(r'\s+', r' ', value.strip())
                        if name.startswith('default-'):
                            name = name.split('-')[-1]
                            defaults[name] = value
                            if name not in options or num_templates == 0:
                                options[name] = value
                        else:
                            options[name] = value
                        continue

                    if template or (not(template) and line.strip()):
                        template.append(line)
                    elif not(template) and 'name' in options:
                        template.append('')

        else:
            with open(filename, encoding='utf-8') as f:
                template = f.readlines()

        # Purge any awaiting templates
        if template:
            try:
                self.setTemplate(''.join(template), options)
            except ValueError as msg:
                print('ERROR: %s in template %s in file %s' % (msg, ''.join(template), filename))

        elif name and not(template):
            self.setTemplate('', options)

    def processFileContent(self, document, s):
        # Add width, height, and depth to images
        s = re.sub(r'&amp;(\S+)-(width|height|depth);(?:&amp;([a-z]+);)?',
                   self.setImageData, s)

        # Convert characters >127 to entities
        if document.config['files']['escape-high-chars']:
            s = list(s)
            for i, item in enumerate(s):
                if ord(item) > 127:
                    s[i] = '&#%.3d;' % ord(item)
            s = ''.join(s)

        return BaseRenderer.processFileContent(self, document, s)

    def setImageData(self, m):
        """
        Substitute in width, height, and depth parameters in image tags

        The width, height, and depth parameters aren't known until after
        all of the output has been generated.  We have to post-process
        the files to insert this information.  This method replaces
        the &filename-width;, &filename-height;, and &filename-depth;
        placeholders with their appropriate values.

        Required Arguments:
        m -- regular expression match object that contains the filename
            and the parameter: width, height, or depth.

        Returns:
        replacement for entity

        """
        filename, parameter, units = m.group(1), m.group(2), m.group(3)

        try:
            img = self.imager.images.get(filename, self.vectorImager.images.get(filename, self.imager.staticimages.get(filename)))
            if img is not None and getattr(img, parameter) is not None:
                if units:
                    return getattr(getattr(img, parameter), units)
                return str(getattr(img, parameter))
        except KeyError: pass

        return '&%s-%s;' % (filename, parameter)


# Set Renderer variable so that plastex will know how to load it
Renderer = PageTemplate

