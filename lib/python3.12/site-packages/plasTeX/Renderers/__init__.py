import os, shutil, string, importlib
from plasTeX.Filenames import Filenames
from plasTeX.DOM import Node
from plasTeX.Logging import getLogger
from plasTeX.Imagers import Image, PILImage
import collections.abc

log = getLogger()
status = getLogger('status')

import logging
logging.getLogger('simpleTAL').setLevel(logging.WARNING)
logging.getLogger('simpleTALES').setLevel(logging.WARNING)

__all__ = ['Renderer','Renderable']

def baseclasses(cls):
    output = [cls]
    for item in cls.__bases__:
        output.extend(baseclasses(item))
    return [x for x in output if x is not object]

def mixin(base, mix, overwrite=False):
    """
    Mix the methods and members of class `mix` into `base`

    Required Arguments:
    base -- the base class to add mixin to
    mix -- the mixin class

    """
    if '_mixed_' not in vars(base):
        base._mixed_ = {}
    mixed = base._mixed_
    for cls in baseclasses(mix):
        for item, value in list(vars(cls).items()):
            if item in ['__dict__','__module__','__doc__','__weakref__']:
                continue
            if overwrite or item not in vars(base):
                old = vars(base).get(item, None)
                setattr(base, item, value)
                mixed[item] = (mix, old)

def unmix(base, mix=None):
    """
    Remove mixed in methods and members

    Required Arguments:
    base -- the base class to remove mixins from

    Keyword Arguments:
    mix -- the mixin class to remove from `base`

    """
    if mix is None:
        for key, value in list(base._mixed_.items()):
            if value[1] is not None:
                setattr(base, key, value[1])
            else:
                delattr(base, key)
        del base._mixed_
    else:
        for key, value in list(base._mixed_.items()):
            if value[0] is mix:
                if value[1] is not None:
                    setattr(base, key, value[1])
                else:
                    delattr(base, key)
        if not base._mixed_:
            del base._mixed_


class Renderable(object):
    """
    Base class for all renderable nodes

    This class is mixed into nodes of the document object prior to
    rendering.  The actual rendering method is __str__.

    """

    def __str__(self):
        """
        Invoke the rendering process on all of the child nodes.

        """
        r = Node.renderer

        # Short circuit macros that have unicode equivalents
        uni = self.str
        if uni is not None:
            return r.outputType(r.textDefault(uni))

        # If we don't have childNodes, then we're done
        if not self.hasChildNodes():
#           if self.filename:
#               status.info(' [ %s ] ', self.filename)
            return ''

#       if self.filename:
#           status.info(' [ %s ', self.filename)

        # At the very top level, only render the DOCUMENT_LEVEL node
        if self.nodeType == Node.DOCUMENT_NODE:
            childNodes = [x for x in self.childNodes
                            if x.level == Node.DOCUMENT_LEVEL]
        else:
            childNodes = self.childNodes

        # Render all child nodes
        s = []
        for child in childNodes:

            # Short circuit text nodes
            if child.nodeType == Node.TEXT_NODE:
                s.append(r.textDefault(child))
                continue

            # Short circuit macros that have unicode equivalents
            uni = child.str
            if uni is not None:
                s.append(r.textDefault(uni))
                continue

            layouts, names = [], []
            nodeName = child.nodeName
            modifier = None

            # Does the macro specify an alternative templateName
            templateName = getattr(child, 'templateName', None)
            # Does the macro have a modifier (i.e. '*')
            if child.attributes:
                modifier = child.attributes.get('*modifier*')

            if child.filename:
                # Force footnotes to be cached
                if hasattr(child, 'footnotes'):
                    _ = child.footnotes

                status.info(' [ %s ', child.filename)

                # Filename and templateName
                if templateName:
                    layouts.append('%s-layout' % (templateName))
                    if modifier:
                        layouts.append('%s-layout%s' % (templateName, modifier))

                # Filename and modifier
                if modifier:
                    layouts.append('%s-layout%s' % (nodeName, modifier))

                # Add nodeName to list
                layouts.append('%s-layout' % nodeName)

            # templateName
            if templateName:
                names.append(templateName)
                if modifier:
                    names.append('%s%s' % (templateName, modifier))
            # Modifier
            if modifier:
                names.append('%s%s' % (nodeName, modifier))

            names.append(nodeName)
            layouts.append('default-layout')

            # Locate the rendering callable, and call it with the
            # current object (i.e. `child`) as its argument.
            func = r.find(names, r.default)
            val = func(child)

            # If a plain string is returned, we have no idea what
            # the encoding is, but we'll make a guess.
            if type(val) is not str:
                log.warning('The renderer for %s returned a non-unicode string.  Using the default input encoding.' % type(child).__name__)
                val = str(val)

            # If the content should go to a file, write it and go
            # to the next child.
            if child.filename:
                filename = child.filename

                # Create any directories as needed
                directory = os.path.dirname(filename)
                if directory and not os.path.isdir(directory):
                    os.makedirs(directory)

                # Add the layout wrapper if there is one
                func = r.find(layouts)
                if func is not None:
                    val = func(StaticNode(child, val))

                    # If a plain string is returned, we have no idea what
                    # the encoding is, but we'll make a guess.
                    if type(val) is not str:
                        log.warning('The renderer for %s returned a non-unicode string.  Using the default input encoding.' % type(child).__name__)
                        val = str(val)

                # Write the file content

                enc = child.config['files']['output-encoding']
                with open(filename, 'w', encoding=enc) as f:
                    f.write(val)

                status.info(' ] ')

                continue

            # Append the resultant object to the output
            s.append(val)

#       if self.filename:
#           status.info(' ] ')

        return r.outputType(''.join(s))

    # def __str__(self):
    #     return ''


    @property
    def image(self):
        """ Generate an image and return the image filename """
        return Node.renderer.imager.getImage(self)

    @property
    def vectorImage(self):
        """ Generate a vector image and return the image filename """
        image = Node.renderer.vectorImager.getImage(self)
        if Node.renderer.vectorBitmap:
            image.bitmap = Node.renderer.imager.getImage(self)
        return image

    @property
    def url(self):
        """
        Return the relative URL of the object

        If the object actually creates a file, just the filename will
        be returned (e.g. foo.html).  If the object is within a file,
        both the filename and the anchor will be returned
        (e.g. foo.html#bar).

        """
        if getattr(self, 'urloverride', None) is not None:
            return self.urloverride

        base = self.config['document']['base-url']
        if base and base.endswith('/'):
            base = base[:-1]

        # If this generates a file, return that filename
        if self.filename:
            if base:
                return URL('%s/%s' % (base, self.filename))
            return URL(self.filename)

        # If this is a location within a file, return that location
        node = self.parentNode
        while node is not None and node.filename is None:
            node = node.parentNode
        filename = ''
        if node is not None:
            filename = node.filename
        if base:
            return URL('%s/%s#%s' % (base, filename, self.id))
        return URL('%s#%s' % (filename, self.id))

    @property
    def filename(self):
        """
        The filename that this object should create

        Objects that don't create new files should simply return `None`.

        """
        r = Node.renderer

        try: return r.files[self]
        except (KeyError, TypeError): pass


        filename = None

        try:
            override = str(self.filenameoverride)
            if override:
                userdata = self.ownerDocument.userdata
                config = self.ownerDocument.config
                newFilename = Filenames(override,
                                        (config['files']['bad-chars'],
                                         config['files']['bad-chars-sub']),
                                        {'jobname':userdata.get('jobname','')},
                                        r.fileExtension)
                filename = r.files[self] = newFilename()

        except AttributeError as msg:
            if not hasattr(self, 'config'):
                return

            level = getattr(self, 'splitlevel', r.level)

            # If our level doesn't invoke a split, don't return a filename
            if self.level > level:
                return

            # Populate vars of filename generator
            # and call the generator to get the filename.
            ns = r.newFilename.variables
            if hasattr(self, 'id') and getattr(self, '@hasgenid', None) is None:
                ns['id'] = self.id
            if hasattr(self, 'title'):
                if hasattr(self.title, 'textContent'):
                    ns['title'] = self.title.textContent
                elif isinstance(self.title, str):
                    ns['title'] = self.title
            if hasattr(self, 'ref'):
                ref = ''
                if hasattr(self.ref, 'textContent'):
                    ref = self.ref.textContent
                elif isinstance(self.ref, str):
                    ref = self.ref
                if ref:
                    ns['ref'] = ref
            if self.nodeName:
                ns['name'] = self.nodeName
            r.files[self] = filename = r.newFilename()

#       print type(self), filename

        return filename


class Renderer(dict):
    """
    Base class for all renderers

    All renderers must act like a dictionary.  Each macro that is encountered
    in a document must have a corresponding key in the renderer.  This
    key points to a callable object which is called with the object to
    be rendered.

    In addition to callable renderers, the renderer also handles image
    generation.  Images are generated when the output document type can
    not support the rendering of a macro.  One example of this is equations
    in HTML.

    """

    renderableClass = Renderable
    textDefault = str
    default = str
    outputType = str
    vectorBitmap = True
    imageTypes = []
    vectorImageTypes = []
    fileExtension = ''
    imageAttrs = '&${filename}-${attr};'
    imageUnits = '&${units};'
    encodingErrors = 'replace'

    def __init__(self, data=None):
        dict.__init__(self, data or {})

        # Names of generated files
        self.files = {}

        # Instantiated at render time
        self.imager = None
        self.vectorImager = None

        # Filename generator
        self.newFilename = None

    def cacheFilenames(self, node):
        """
        Generate filenames in order

        Since filenames are generated on demand, in order to make the
        nodes have a filename that corresponds to its position in the document,
        the filenames must be generated before rendering the document.

        Required Arguments:
        node -- the top-level node in the document

        """
        # Using the side-effect of the filename property
        _ = node.filename
        for child in node.childNodes:
            self.cacheFilenames(child)

    def render(self, document, postProcess=None):
        """
        Invoke the rendering process

        This method invokes the rendering process as well as handling
        the setup and shutdown of image processing.

        Required Arguments:
        document -- the document object to render
        postProcess -- a function that will be called with the content of

        """
        config = document.config

        self.level = config["files"]["split-level"]
        filenameTemplate = config["files"]["filename"].strip()
        if ' ' not in filenameTemplate and '[' not in filenameTemplate:
            self.level = -10

        # If there are no keys, print a warning.
        # This is most likely a problem.
        if not list(self.keys()):
            log.warning('There are no keys in the renderer.  ' +
                        'All objects will use the default rendering method.')

        # Mix in required methods and members
        mixin(Node, type(self).renderableClass)
        Node.renderer = self

        # Create a filename generator
        self.newFilename = Filenames(config['files'].get('filename'),
                                     (config['files']['bad-chars'],
                                      config['files']['bad-chars-sub']),
                                     {'jobname':document.userdata.get('jobname', '')}, self.fileExtension)

        self.cacheFilenames(document)

        # Instantiate appropriate imager
        names = [x for x in config['images']['imager'].split() if x]
        for name in names:
            if name == 'none':
                break
            elif name == 'dvipng':
                from plasTeX.Imagers.dvipng import Imager
            elif name == 'dvi2bitmap':
                from plasTeX.Imagers.dvi2bitmap  import Imager
            elif name == 'pdftoppm':
                from plasTeX.Imagers.pdftoppm  import Imager
            elif name == 'gspdfpng':
                from plasTeX.Imagers.gspdfpng  import Imager
            elif name == 'gsdvipng':
                from plasTeX.Imagers.gsdvipng  import Imager
            elif name == 'OSXCoreGraphics':
                from plasTeX.Imagers.OSXCoreGraphics  import Imager
            else:
                log.warning("Invalid imager '%s'" % name)
                continue

            self.imager = Imager(document, self.imageTypes)

            # Make sure that this imager works on this machine
            if self.imager.verify():
                log.info('Using the imager "%s".' % name)
                break
            else:
                self.imager = None

        # Still no imager? Just use the default.
        if self.imager is None:
            if 'none' not in names:
                log.warning('Could not find a valid imager in the list: %s.  The default imager will be used.' % ', '.join(names))
            from plasTeX.Imagers import Imager
            self.imager = Imager(document, self.imageTypes)

        if self.imageTypes and self.imager.fileExtension not in self.imageTypes:
            self.imager.fileExtension = self.imageTypes[0]
        if self.imageAttrs and not self.imager.imageAttrs:
            self.imager.imageAttrs = self.imageAttrs
        if self.imageUnits and not self.imager.imageUnits:
            self.imager.imageUnits = self.imageUnits

        # Instantiate appropriate vector imager
        names = [x for x in config['images']['vector-imager'].split() if x]
        for name in names:
            if name == 'none':
                break
            elif name == 'dvisvgm':
                from plasTeX.Imagers.dvisvgm import Imager as VectorImager
            elif name == 'pdf2svg':
                from plasTeX.Imagers.pdf2svg import Imager as VectorImager
            else:
                log.warning("Invalid imager '%s'" % name)
                continue

            self.vectorImager = VectorImager(document, self.vectorImageTypes)

            # Make sure that this imager works on this machine
            if self.vectorImager.verify():
                log.info('Using the vector imager "%s".' % name)
                break

            self.vectorImager = None

        # Still no vector imager? Just use the default.
        if self.vectorImager is None:
            if 'none' not in names:
                log.warning('Could not find a valid vector imager in the list: %s.  The default vector imager will be used.' % ', '.join(names))
            from plasTeX.Imagers import VectorImager
            self.vectorImager = VectorImager(document, self.vectorImageTypes)

        if self.vectorImageTypes and \
           self.vectorImager.fileExtension not in self.vectorImageTypes:
            self.vectorImager.fileExtension = self.vectorImageTypes[0]
        if self.imageAttrs and not self.vectorImager.imageAttrs:
            self.vectorImager.imageAttrs = self.imageAttrs
        if self.imageUnits and not self.vectorImager.imageUnits:
            self.vectorImager.imageUnits = self.imageUnits

        # Invoke the rendering process
        str(document)

        self.imager.close()
        self.vectorImager.close()

        # Run any cleanup activities
        self.cleanup(document, list(self.files.values()), postProcess=postProcess)

        # Write out auxilliary information
        pauxname = os.path.join(document.userdata.get('working-dir','.'),
                                '%s.paux' % document.userdata.get('jobname',''))
        rname = config['general']['renderer']
        document.context.persist(pauxname, rname)

        # Remove mixins
        del Node.renderer
        unmix(Node, type(self).renderableClass)

    def processFileContent(self, document, s):
        return s

    def cleanup(self, document, files, postProcess=None):
        """
        Cleanup method called at the end of rendering

        This method allows you to do arbitrary post-processing after
        all files have been rendered.

        Note: While I greatly dislike post-processing, sometimes it's
              just easier...

        Required Arguments:
        document -- the document being rendered
        files -- the list of filenames that were generated

        Optional Arguments:
        postProcess -- a function that will be called on the content of
            each file.  It is called with the document object and a
            string object with the content of each file.
            It must return a string object.

        """
        if self.processFileContent is Renderer.processFileContent:
            return

        encoding = document.config['files']['output-encoding']
        errs = self.encodingErrors
        for f in files:
            try:
                with open(f, 'r', encoding=encoding, errors=errs) as fd:
                    s = fd.read()

            except IOError as msg:
                log.error(msg)
                continue

            s = self.processFileContent(document, s)
            if isinstance(postProcess, collections.abc.Callable):
                s = postProcess(document, s)

            with open(f, 'w', encoding=encoding) as fd:
                fd.write(''.join(s))

    def find(self, keys, default=None):
        """
        Locate a renderer given a list of possibilities

        Required Arguments:
        keys -- a list of strings containing the requested name of
            a renderer.  This list is traversed in order.  The first
            renderer that is found is returned.

        Keyword Arguments:
        default -- the renderer to return if none of the keys exists

        Returns:
        the requested renderer

        """
        for key in keys:
            if key in self:
                return self[key]

        # Other nodes supplied default
        log.warning('Using default renderer for %s' % ', '.join(keys))
        for key in keys:
            self[key] = default
        return default



class StaticNode(object):
    """
    Object to assist in rendering files

    This object is used to wrap objects that need to have a layout
    file wrapped around them.  The layout wrapper generally includes
    all of the navigation links, table of contents, etc.

    This is simply a proxy object that returns the attributes of
    the given object.  The exceptions is __str__
    which simply returns the rendered string that was passed in.
    This allows you to use two templates: one that renders the content
    and another that is wrapped around any node that generates a
    file.  Without this, you can easily run into infinite recursion
    problems.

    """
    def __init__(self, obj, content):
        """
        Initialize the static node

        Arguments:
        obj -- the object that contains navigation and table of
            contents information
        content -- the rendered object in a  string

        """
        self._node_data = (obj, content)
    def __getattribute__(self, name):
        if name in ['_node_data','__str__']:
            return object.__getattribute__(self, name)
        return getattr(self._node_data[0], name)

    def __str__(self):
        return self._node_data[1]


class URL(str):

    def relativeTo(self, src):
        """
        Get the path of this URL relative to `src'

        """
        if isinstance(src, Node):
            src = src.url

        dest, src = os.path.normpath(str(self)), os.path.normpath(src)
        base = os.path.join(*(['a/'] * max(dest.count('/'), src.count('/'))))
        src = os.path.join(base, src).split('/')
        dest = os.path.join(base, dest).split('/')

        same = 0
        for d, s in zip(dest, src):
            if d == s:
                same += 1
                continue
            break

        dest, src = dest[same:], src[same:-1]

        if src:
            return type(self)(os.path.join(os.path.join(*(['..'] * len(src))),
                                           os.path.join(*dest)))

        return type(self)(os.path.join(*dest))
