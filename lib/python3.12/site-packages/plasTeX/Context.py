import sys
import os
import configparser
import re
import time
from pathlib import Path
from typing import Optional, Dict, List
from importlib import import_module
from importlib.util import find_spec

from plasTeX import ismacro, macroName
from plasTeX.TeX import TeX
from plasTeX.Logging import getLogger
from plasTeX.Base.TeX.Primitives import relax
from plasTeX.Tokenizer import Tokenizer, Token, DEFAULT_CATEGORIES, VERBATIM_CATEGORIES
import plasTeX
import plasTeX.Packages

# Only export the Context singleton
__all__ = ['Context']

# Set up loggers
log = getLogger()
status = getLogger('status')
stacklog = getLogger('context.stack')
macrolog = getLogger('context.macros')


class ContextItem(dict):
    """
    Localized macro/category code stack element

    """

    def __init__(self, data=None):
        dict.__init__(self, data or {})
        self.categories = None # type: Optional[List[str]]
        self.lets = {}
        self.obj = None
        self.parent = None
        self.owner = None

    @property
    def name(self):
        if self.obj is not None:
            return self.obj.nodeName
        return '{}'

    def __getitem__(self, key):
        try:
            return dict.__getitem__(self, key)
        except KeyError:
            if self.parent is not None and self.parent is not self:
                return self.parent[key]
            raise

    def get(self, key, default=None):
        try: return self[key]
        except KeyError: return default

    def has_key(self, key):
        if dict.__contains__(self, key):
            return True
        if self.parent is not None:
            return key in list(self.parent.keys())

    __contains__ = has_key

    def keys(self):
        keys = {}
        for key in list(dict.keys(self)):
            keys[key] = 0
        if self.parent is not None:
            for key in list(self.parent.keys()):
                keys[key] = 0
        return list(keys.keys())

    def __str__(self):
        if self.parent is not None:
             return '%s -> %s' % (self.parent, self.name)
        return self.name


class Counters(dict):
    def __getitem__(self, name):
        try:
            c = dict.__getitem__(self, name)
        except KeyError:
#           log.warning('No counter "%s" exists.  Creating one.' % name)
            c = self[name] = plasTeX.Counter(self.context, name)
        return c


class LanguageParser(object):
    """ Parser for language commands """

    def __init__(self, output=None):
        self.data = output if output is not None else {}
        self.language = None
        self.term = None

    def parse(self, files, encoding='UTF-8'):
        from xml.parsers import expat
        if isinstance(files, str):
            files = [files]
        for fname in files:
            if not os.path.isfile(fname):
                continue

            self.parser = expat.ParserCreate(encoding)
            self.parser.StartElementHandler = self.startElement
            self.parser.EndElementHandler = self.endElement
            self.parser.CharacterDataHandler = self.charData
            with open(fname, encoding=encoding) as f:
                self.parser.Parse(f.read())
        self.mergeLanguages()
        return self.data

    def mergeLanguages(self):
        # Merge language keys from the major language section, into
        # the minor language section
        for key, value in list(self.data.items()):
            if '-' in key:
                major, minor = key.split('-', 1)
                if major in list(self.data.keys()):
                    majordict = self.data[major]
                    for mkey, mvalue in list(majordict.items()):
                        if mkey not in value:
                            value[mkey] = mvalue

    def startElement(self, name, attrs):
        if name == 'terms':
            self.term = None
            if self.data.get(attrs['lang']):
                self.language = self.data[attrs['lang']]
            else:
                self.language = self.data[attrs['lang']] = {}
            if 'babel' in attrs:
                self.data[attrs['babel']] = self.language
        elif name == 'term':
            self.term = attrs['name']
            self.language[self.term] = ''

    def endElement(self, name):
        if name == 'term':
            self.term = None

    def charData(self, data):
        if self.term:
            self.language[self.term] += data


class Context(object):
    """
    Object to handle macro contexts within a TeX document

    This class keeps track of macros (both global and local), labels,
    context groupings, category codes, etc.  The TeX parser uses this
    class to hold any and all information about the document currently
    being processed.  This class also contains methods to generate
    new counters, ifs, dimensions, and other commands and macros.

    """

    def globals(self):
        return self.contexts[0]

    def __init__(self, load=False):
        # Stack of ContextItems
        self.contexts = []

        # Object that the current label points to
        self.currentlabel = None

        # Labeled objects
        self.labels = {}
        self.persistentLabels = {}

        # Unresolved refs
        self.refs = {}

        # LaTeX counters
        self.counters = Counters()
        self.counters.context = self

        # Imported packages and their options
        self.packages = {}

        # Output files
        self.writes = {}

        # Depth of the context stack
        self.depth = 0

        # Holds the current environment name stack
        self._currenvir = []

        # Holds the terms for various languages
        self.languages = {}
        self.terms = {}
        self.currentLanguage = ''

        # Create a global namespace
        self.push()

        self.warnOnUnrecognized = True

        if load:
            self.loadBaseMacros()

    @property
    def currenvir(self):
        if self._currenvir:
            return self._currenvir[-1]
        return

    @currenvir.setter
    def currenvir(self, value):
        if value is None:
            self._currenvir.pop()
        else:
            self._currenvir.append(value)

    @currenvir.deleter
    def currenvir(self):
        self._currenvir.pop()

    def persist(self, filename, rtype='none'):
        """
        Persist cross-document information for labeled nodes

        Required Arguments:
        filename -- the name of the file with the shelved data

        Keyword Arguments:
        rtype -- the key in the shelved data to look under.  This is generally
            the name of the renderer used since the information for each
            renderer may be different.

        """
        import pickle
        if os.path.exists(filename):
            try:
                with open(filename, 'rb') as fh:
                    d = pickle.load(fh)
                    if rtype not in list(d.keys()):
                        d[rtype] = {}
            except:
                os.remove(filename)
                d = {rtype:{}}
        else:
            d = {rtype:{}}
        data = d[rtype]
        for key, value in list(self.persistentLabels.items()):
            data[key] = value.persist()
        try:
            with open(filename, 'wb') as fh:
                pickle.dump(d, fh)
        except Exception as msg:
            log.warning('Could not save auxiliary information. (%s)' % msg)

    def restore(self, filename, rtype='none'):
        """
        Restore cross-document information for labeled nodes

        Required Arguments:
        filename -- the name of the file with the shelved data

        Keyword Arguments:
        rtype -- the key in the shelved data to look under.  This is generally
            the name of the renderer used since the information for each
            renderer may be different.

        """
        import pickle
        if not os.path.exists(filename):
            return
        try:
            d = pickle.load(open(filename, 'rb'))
            try: data = d[rtype]
            except KeyError: return
            wou = self.warnOnUnrecognized
            self.warnOnUnrecognized = False
            for key, value in list(data.items()):
                n = self[value.get('macroName', 'Macro')]()
                n.restore(value)
                self.labels[key] = n
            self.warnOnUnrecognized = wou
        except Exception as msg:
            log.warning('Could not load auxiliary information. (%s)' % msg)

    @property
    def isMathMode(self):
        """ Are we in math mode or not? """
        for i in range(len(self.contexts) - 1, -1, -1):
            obj = self.contexts[i].obj
            if obj is not None and obj.mathMode is not None:
                return obj.mathMode
        return False

    def loadBaseMacros(self):
        """ Import all builtin macros """
        from plasTeX import Base
        self.importMacros(vars(Base))

    def loadLanguage(self, lang, document):
        """
        Load a localized version of macros for a particular language

        Required Arguments:
        lang -- the name of the language file to load

        """

        if not self.languages:
            files = document.config['document']['lang-terms']
            files.append(os.path.join(os.path.dirname(__file__), 'i18n.xml'))

            LanguageParser(self.languages).parse(reversed(files))

        if lang in list(self.languages.keys()):
            self.currentLanguage = lang
            self.newcommand('languagename', definition=lang)
            self.terms = self.languages[lang]
            for key, value in list(self.languages[lang].items()):
                if key == 'today':
                    self.newcommand(key, definition=self._strftime(value))
                else:
                    self.newcommand('%sname' % key, definition=value)
        else:
            log.warning('Could not load language "%s", american will be used instead' % lang)

    def _strftime(self, fmt):
        if '%f' in fmt or '%e' in fmt:
            day = time.strftime('%d')
            suffix = 'th'
            if day.endswith('1'):
                suffix = 'st'
            elif day.endswith('2'):
                suffix = 'nd'
            elif day.endswith('3'):
                suffix = 'rd'
            day = str(int(day))
            return time.strftime(fmt.replace('%f', day + suffix).replace('%e', day))
        return time.strftime(fmt)

    def loadINIPackage(self, inifile):
        """
        Load INI file containing macro definitions

        Arguments:
        inifile -- filename of INI formatted file

        """
        ini = configparser.RawConfigParser()
        if not isinstance(inifile, (list, tuple)):
            inifile = [inifile]
        for f in inifile:
            ini.read(f)
            macros = {}
            for section in ini.sections():
                try: baseclass = self[section]
                except KeyError:
                    log.warning('Could not find macro %s' % section)
                    continue
                for name in ini.options(section):
                    value = ini.get(section, name)
                    m = re.match(r'^str\(\s*(?:(\'|\")(?P<string>.+)(?:\1)|(?P<number>\d+))\s*\)$', value)
                    if m:
                        data = m.groupdict()
                        if data['number'] is not None:
                            value = chr(int(data['number']))
                        else:
                            value = data['string']
                        macros[name] = type(name, (baseclass,),
                                                    {'str': value})
                        continue
                    macros[name] = type(name, (baseclass,),
                                                {'args': value})
            self.importMacros(macros)

    def loadPythonPackage(self, document: plasTeX.TeXDocument, file_name: str, options: Optional[Dict] = None) -> bool:
        """
        Load a Python package

        Packages are first searched for in
        the directories of config['general']['packages-dirs'], then
        in plugins listed in config['general']['plugins'], and then
        among builtin packages.

        Required Arguments:
        document -- the document currently being built.
        file_name -- the name of the file to load

        Keyword Arguments:
        options -- the options given on the macro to pass to the package

        Returns:
        boolean indicating whether or not the package loaded successfully

        """
        config = document.config
        working_dir = document.userdata.get('working-dir', '')
        options = options or {}
        module = os.path.splitext(file_name)[0]
        # See if it has already been loaded
        if module in self.packages:
            return True

        packagesini = os.path.join(os.path.dirname(plasTeX.Packages.__file__),
                                   os.path.basename(module) + '.ini')

        imported = None
        orig_sys_path = sys.path

        for pkg_dir in config['general']['packages-dirs']:
            if Path(pkg_dir).is_absolute():
                path = Path(pkg_dir)
            else:
                path = (Path(working_dir)/pkg_dir).absolute()

            pypath = (path/module).with_suffix('.py')
            if not pypath.exists():
                continue
            if str(path) not in sys.path:
                sys.path.insert(0, str(path))
            spec = find_spec(module)
            if spec is None:
                sys.path = orig_sys_path
                continue
            if module in sys.modules and spec.origin != str(pypath):
                log.warning('Python has already loaded a module named {} '
                        ' from {}, so we cannot load it from {}. '
                        'You can fix this by creating a '
                        'plugin.'.format(module, spec.origin, pkg_dir))
                break

            try:
                imported = import_module(module)
            except (ImportError, ModuleNotFoundError) as msg:
                # Error while importing
                sys.path = orig_sys_path
                raise
            break

        if imported is None:
            for plugin in reversed(config['general']['plugins']):
                sys.path = orig_sys_path
                plugin_module = import_module(plugin)
                assert plugin_module.__file__
                if not (Path(plugin_module.__file__).parent/'Packages').exists():
                    continue
                p_ = str(Path(plugin_module.__file__).parent.parent)
                if p_ not in sys.path:
                    sys.path.insert(0, p_)
                try:
                    imported = import_module(plugin + '.Packages.' + module)
                    break
                except (ImportError, ModuleNotFoundError) as msg:
                    # No Python module
                    if 'No module' in str(msg) and module in str(msg):
                        pass
                        # Failed to load Python package
                    # Error while importing
                    else:
                        sys.path = orig_sys_path
                        raise

        if imported is None:
            # Now try builtin plasTeX packages
            p_ = str(Path(__file__).parent.parent)
            if p_ not in sys.path:
                sys.path.insert(0, p_)
            try:
                imported = import_module('plasTeX.Packages.' + module)
            except (ImportError, ModuleNotFoundError) as msg:
                # No Python module
                if 'No module' in str(msg) and module in str(msg):
                    pass
                    # Failed to load Python package
                # Error while importing
                else:
                    sys.path = orig_sys_path
                    raise

        sys.path = orig_sys_path

        if imported:
            status.info(' (loading package %s ' % imported.__file__)
            if hasattr(imported, 'ProcessOptions'):
                imported.ProcessOptions(options, document) # type: ignore
            assert imported.__file__
            self.importMacros(vars(imported))
            moduleini = os.path.splitext(imported.__file__)[0] + '.ini'
            self.loadINIPackage([packagesini, moduleini])
            self.packages[module] = options
            status.info(' ) ')
            return True
        else:
            return False

    def loadPackage(self, tex: TeX, file_name: str, options: Optional[Dict] = None) -> bool:
        """
        Load a Python or LaTeX package

        A Python version of the package is searched for first,
        if one cannot be found then a LaTeX version of the package
        is searched for if config['general']['load-tex-packages']
        is True, or the package has been white-listed in
        config['general']['tex-packages'].

        Python versions are first searched for in
        the directories of config['general']['packages-dirs'], then
        in plugins listed in config['general']['plugins'], and then
        among builtin packages.

        Required Arguments:
        tex -- the instance of the TeX engine to use for parsing
            the LaTeX file, if needed.
        file_name -- the name of the file to load

        Keyword Arguments:
        options -- the options given on the macro to pass to the package

        Returns:
        boolean indicating whether or not the package loaded successfully

        """
        config = tex.ownerDocument.config
        options = options or {}
        module = os.path.splitext(file_name)[0]
        # See if it has already been loaded
        if module in self.packages:
            return True

        packagesini = os.path.join(os.path.dirname(plasTeX.Packages.__file__),
                                   os.path.basename(module) + '.ini')

        if self.loadPythonPackage(tex.ownerDocument, file_name, options):
            return True

        log.warning('No Python version of %s was found' % file_name)

        # Try to load a LaTeX implementation
        if (config['general']['load-tex-packages'] or
              module in config['general']['tex-packages']):
            log.warning('Will now try to load a LaTeX implementation of %s' % file_name)
            result = tex.loadPackage(file_name, options)
            try:
                moduleini = os.path.join(os.path.dirname(tex.kpsewhich(file_name)),
                                         os.path.basename(module) + '.ini')
                self.loadINIPackage([packagesini, moduleini])
            except OSError: pass
            return result
        return False


    def label(self, label, node=None):
        """
        Set a label to the current labelable object

        Required Arguments:
        label -- string that contains the label

        Keyword Arguments:
        node -- a node to apply the label to rather than the currently
            labelable object

        See Also:
        self.ref()

        """
        label = label.strip()
        if not label:
            return

        if node is None:
            node = self.currentlabel

        if node is not None:
            self.persistentLabels[label] = self.labels[label] = node
            node.id = label

        # print label, ''.join(self.currentlabel.ref[:])

        # Resolve any outstanding references to this object
        if label in list(self.refs.keys()) and label in (self.labels.keys()):
            for obj in self.refs[label]:
                for key, value in list(obj.idref.items()):
                    if value.id != label:
                        continue
                    obj.idref[key] = self.labels[label]
            del self.refs[label]

    def ref(self, obj, name, label):
        """
        Set up a ref for resolution

        Required Arguments:
        obj -- object to put the referenced object onto
        name -- name of key in idref dictionary where object is stored
        label -- label to resolve

        See Also:
        self.label()

        """
        label = label.strip()
        if not label:
            return

        # Resolve ref if label already exists
        if label in list(self.labels.keys()):
            obj.idref[name] = self.labels[label]
            return

        # If the label doesn't exist, store away the object for later
        if label not in list(self.refs.keys()):
            self.refs[label] = []
        self.refs[label].append(obj)

        # Make a fake node with the ID on it for now
        node = self['Macro']()
        node.id = label
        obj.idref[name] = node

    def __getitem__(self, key):
        """
        Look through the stack of macros and return the requested one

        Required Arguments:
        key -- name of macro

        Returns: instance of requested macro

        """
        try: return self.top[key]
        except KeyError: pass

        # Didn't find it, so generate a new class
        if self.warnOnUnrecognized and not self.isMathMode:
            log.warning('unrecognized command/environment: %s', key)
        self[key] = newclass = type(key, (plasTeX.UnrecognizedMacro,), {})
        return newclass

    def push(self, context=None):
        """
        Add a new context to the stack

        This adds a new context grouping to the stack.  A context
        grouping includes both a set of localized macros and localized
        category codes.

        Keyword Arguments:
        context -- macro instance to use as the basis for a context
            grouping.  The local macros and category codes of this
            instance are used.  If this argument isn't supplied,
            an empty context is created.

        """
        if not self.contexts:
            context = ContextItem()
            context.categories = DEFAULT_CATEGORIES[:]
            self.contexts.append(context)

        else:
            name = '{}'
            if context is not None:
                name = context.nodeName
                # If we hit a document element, make sure that we start
                # at the global context.
                if context.level == context.DOCUMENT_LEVEL:
                    while len(self.contexts) > 1:
                        self.contexts.pop()
            stacklog.debug('pushing %s onto %s', name, self.top)
            self.contexts.append(self.createContext(context))

        self.mapMethods()

    append = push

    def __contains__(self, key):
        return key in self.top

    def mapMethods(self):
        # Getter methods use the most local context
        self.top = top = self.contexts[-1]
        self.__getitem__ = top.__getitem__
        self.__contains__ = top.__contains__
        self.get = top.get
        self.keys = top.keys
        self.has_key = top.has_key
        self.categories = top.categories

        # Setter methods always use the global namespace
        self.update = top.update
        self.__setitem__ = self.contexts[0].__setitem__

        # Set up inheritance attributes
        self.top.owner = self
        if len(self.contexts) > 1:
            self.top.parent = self.contexts[-2]

        self.depth = len(self.contexts)

    def createContext(self, obj=None):
        """
        Create the pieces of a new context (i.e. macros and category codes)

        Keyword Arguments:
        obj -- macro instance to use as the basis for a context
            grouping.  The local macros and category codes of this
            instance are used.  If this argument isn't supplied,
            an empty context is created.

        Returns: ContextItem instance

        """
        newcontext = ContextItem()
        newcontext.categories = self.categories
        newcontext.obj = obj

        if obj is not None:

            # Get the local category codes and macros
#           if obj.categories is not None:
#               newcontext.categories = obj.categories

            newcontext.update(obj.locals())

        return newcontext

    def importMacros(self, context):
        """
        Import macros from given context into the global namespace

        Required Arguments:
        context -- dictionary of macros to import

        """
        for value in list(context.values()):
            if ismacro(value):
                self[macroName(value)] = value
#           elif isinstance(value, Context):
#               self.importMacros(value)

    def pop(self, obj=None):
        """
        Remove a context from the stack

        Keyword Arguments:
        index -- index of context item to remove

        Returns: ContextItem instance removed from stack

        """
#       print 'POP', type(obj).__name__, self.contexts[-1]
        if obj is None:
            # Pop until we hit a None in the context
            while len(self.contexts) > 1:
                if self.contexts[-1].obj is None:
                    self.contexts.pop()
                    break
                self.contexts.pop()
        else:
            while len(self.contexts) > 1:
                o = self.contexts[-1].obj
                # If None, keep going
                if o is None:
                    pass
                # Found context pushed by ourself
                elif o is obj:
                    self.contexts.pop()
                    break
                # Don't pop parent node
                elif o is obj.parentNode:
                    break
                # Found the \begin to our \end
                elif type(obj) == type(o) and obj.macroMode == obj.MODE_END:
                    self.contexts.pop()
                    break
                # Found the \foo to our \endfoo
                elif obj.nodeName == ('end%s' % o.nodeName):
                    self.contexts.pop()
                    break
                self.contexts.pop()

        self.mapMethods()

    def addGlobal(self, key, value):
        """
        Add a macro to the global context

        Required Arguments:
        key -- name of macro to add
        value -- item to add to the global namespace.  If the item
            is a macro instance, it is simply added to the namespace.
            If it is a string, it is converted into a string Command
            instance before being added.

        """
        if isinstance(value, str):
            newvalue = plasTeX.Command()
            newvalue.str = value
            value = newvalue

        elif not ismacro(value):
            raise ValueError('"%s" does not implement the macro interface' % key)

        self.contexts[0][macroName(value)] = value

    __setitem__ = addGlobal

    def addLocal(self, key, value):
        """
        Add a macro to the local context

        Required Arguments:
        key -- name of macro to add
        value -- item to add to the global namespace.  If the item
            is a macro instance, it is simply added to the namespace.
            If it is a string, it is converted into a string Command
            instance before being added.

        """
        if isinstance(value, str):
            newvalue = plasTeX.Command()
            newvalue.str = value
            value = newvalue

        elif not ismacro(value):
            raise ValueError('"%s" does not implement the macro interface' % key)

        self.contexts[-1][macroName(value)] = value

    def whichCode(self, char):
        """
        Return the character code that `char` belongs to

        Required Arguments:
        char -- character to determine the code of

        Returns: integer category code of the given character

        """
        c = self.categories
        if char in c[Token.CC_LETTER]:
            return Token.CC_LETTER
        if char in c[Token.CC_SPACE]:
            return Token.CC_SPACE
        if char in c[Token.CC_EOL]:
            return Token.CC_EOL
        if char in c[Token.CC_BGROUP]:
            return Token.CC_BGROUP
        if char in c[Token.CC_EGROUP]:
            return Token.CC_EGROUP
        if char in c[Token.CC_ESCAPE]:
            return Token.CC_ESCAPE
        if char in c[Token.CC_SUPER]:
            return Token.CC_SUPER
        if char in c[Token.CC_SUB]:
            return Token.CC_SUB
        if char in c[Token.CC_MATHSHIFT]:
            return Token.CC_MATHSHIFT
        if char in c[Token.CC_ALIGNMENT]:
            return Token.CC_ALIGNMENT
        if char in c[Token.CC_COMMENT]:
            return Token.CC_COMMENT
        if char in c[Token.CC_ACTIVE]:
            return Token.CC_ACTIVE
        if char in c[Token.CC_PARAMETER]:
            return Token.CC_PARAMETER
        if char in c[Token.CC_IGNORED]:
            return Token.CC_IGNORED
        if char in c[Token.CC_INVALID]:
            return Token.CC_INVALID
        return Token.CC_OTHER

    def catcode(self, char, code):
        """
        Set the category code for a particular character

        Required arguments:
        char -- the character to set the code of
        code -- the category code number to set `char` to

        """
        c = self.contexts[-1].categories = self.categories = self.categories[:]
        for i in range(0, 16):
            c[i] = c[i].replace(char, '')
        # Don't insert if it's code 12.
        if code != 12:
            c[code] += char

    def setVerbatimCatcodes(self):
        """
        Set the category codes up for parsing verbatims

        This method turns the category codes for all characters to CC_OTHER

        """
        self.contexts[-1].categories = self.categories = VERBATIM_CATEGORIES[:]

    def newcounter(self, name, resetby=None, initial=0, format=None, trimLeft = False):
        """
        Create a new counter

        This method corresponds to LaTeX's \\newcounter command

        Required Arguments:
        name -- name of the counter.  The generate counter class will
            use this name.  Also, a new macro called 'the<name>' will
            also be generated for the counter format.

        Keyword Arguments:
        resetby -- the name of the counter that this counter is reset by
        initial -- initial value for the counter

        """
        # Counter already exists
        if name in list(self.counters.keys()):
            macrolog.debug('counter %s already defined', name)
            return
        self.counters[name] = plasTeX.Counter(self, name, resetby, initial)

        if format is None:
            format = '${%s}' % name
        newclass = type('the' + name, (plasTeX.TheCounter,),
                {'format': format, 'trimLeft': trimLeft})
        self.addGlobal('the' + name, newclass)

    def newwrite(self, name, file):
        """
        Create a new output file

        Required Arguments:
        name -- the key name for the file
        file -- the file name to open

        """
        self.writes[name] = open(file, 'w')

    def newcount(self, name, initial=0):
        """
        Create a new count (like \\newcount)

        Required Arguments:
        name -- name of count to create

        Keyword Arguments:
        initial -- value to initialize to

        """
        # Generate a new count class
        macrolog.debug('creating count %s', name)
        newclass = type(name, (plasTeX.CountCommand,),
                               {'value': plasTeX.count(initial)})
        self.addGlobal(name, newclass)

    def newdimen(self, name, initial=0):
        """
        Create a new dimen (like \\newdimen)

        Required Arguments:
        name -- name of dimen to create

        Keyword Arguments:
        initial -- value to initialize to

        """
        # Generate a new dimen class
        macrolog.debug('creating dimen %s', name)
        newclass = type(name, (plasTeX.DimenCommand,),
                                {'value': plasTeX.dimen(initial)})
        self.addGlobal(name, newclass)

    def newskip(self, name, initial=0):
        """
        Create a new glue (like \\newskip)

        Required Arguments:
        name -- name of glue to create

        Keyword Arguments:
        initial -- value to initialize to

        """
        # Generate a new glue class
        macrolog.debug('creating dimen %s', name)
        newclass = type(name, (plasTeX.GlueCommand,),
                                {'value': plasTeX.glue(initial)})
        self.addGlobal(name, newclass)

    def newmuskip(self, name, initial=0):
        """
        Create a new muglue (like \\newmuskip)

        Required Arguments:
        name -- name of muglue to create

        Keyword Arguments:
        initial -- value to initialize to

        """
        # Generate a new muglue class
        macrolog.debug('creating muskip %s', name)
        newclass = type(name, (plasTeX.MuGlueCommand,),
                                {'value': plasTeX.muglue(initial)})
        self.addGlobal(name, newclass)

    def newif(self, name, initial=False):
        """
        Create a new \\if (and accompanying) commands

        This method corresponds to TeX's \\newif command.

        Required Arguments:
        name -- name of the 'if' command.  This name should always
            start with the letters 'if'.

        Keyword Arguments:
        initial -- initial value of the 'if' command

        """

        # \if already exists
        if name in list(self.keys()):
            macrolog.debug('if %s already defined', name)
            return

        # Generate new 'if' class
        macrolog.debug('creating if %s', name)
        ifclass = type(name, (plasTeX.NewIf,), {'state':initial})
        self.addGlobal(name, ifclass)

        # Create \iftrue macro
        truename = name[2:] + 'true'
        newclass = type(truename, (plasTeX.IfTrue,), {'ifclass':ifclass})
        self.addGlobal(truename, newclass)

        # Create \iffalse macro
        falsename = name[2:] + 'false'
        newclass = type(falsename, (plasTeX.IfFalse,), {'ifclass':ifclass})
        self.addGlobal(falsename, newclass)

    def newcommand(self, name, nargs=0, definition=None, opt=None):
        """
        Create a \\newcommand

        Required Arguments:
        name -- name of the macro to create
        nargs -- integer number of arguments that the macro has
        definition -- string containing the LaTeX definition
        opt -- string containing the LaTeX code to use in the
            optional argument

        Examples::
            c.newcommand('bold', 1, r'\\textbf{#1}')
            c.newcommand('foo', 2, r'{\\bf #1#2}', opt='myprefix')

        """
        # Macro already exists
        if name in list(self.keys()):
            if not issubclass(self[name], (plasTeX.NewCommand, plasTeX.UnrecognizedMacro, plasTeX.Definition, relax)):
                if not issubclass(self[name], plasTeX.TheCounter):
                    return
            macrolog.debug('redefining command "%s"', name)

        if nargs is None:
            nargs = 0
        assert isinstance(nargs, int), 'nargs must be an integer'

        if isinstance(definition, str):
            definition = list(Tokenizer(definition, self))

        if isinstance(opt, str):
            opt = list(Tokenizer(opt, self))

        macrolog.debug('creating newcommand %s', name)
        newclass = type(name, (plasTeX.NewCommand,),
                       {'nargs':nargs, 'opt':opt, 'definition':definition})

        self.addGlobal(name, newclass)

    def newenvironment(self, name, nargs=0, def_before=None, def_after=None, opt=None):
        """
        Create a \\newenvironment

        Required Arguments:
        name -- name of the macro to create
        nargs -- integer number of arguments that the macro has
        def_before -- string corresponding to TeX code inserted before the
            environment
        def_after -- string corresponding to TeX code inserted after the
            environment
        opt -- string containing the LaTeX code to use in the
            optional argument

        Examples::
            c.newenvironment('mylist', 0, [r'\\begin{itemize}', r'\\end{itemize}'])

        """
        # Macro already exists
        if name in list(self.keys()):
            if not issubclass(self[name], (plasTeX.NewCommand,
                                           plasTeX.Definition)):
                return
            macrolog.debug('redefining environment "%s"', name)

        if nargs is None:
            nargs = 0
        assert isinstance(nargs, int), 'nargs must be an integer'

        if def_before:
            def_before = list(Tokenizer(def_before, self))
        if def_after:
            def_after = list(Tokenizer(def_after, self))

        if isinstance(opt, str):
            opt = list(Tokenizer(opt, self))

        macrolog.debug('creating newenvironment %s', name)

        # Begin portion
        newclass = type(name, (plasTeX.NewCommand,),
                       {'nargs':nargs, 'opt':opt, 'definition':def_before})
        self.addGlobal(name, newclass)

        # End portion
        newclass = type('end' + name, (plasTeX.NewCommand,),
                       {'nargs':0, 'opt':None, 'definition':def_after})
        self.addGlobal('end' + name, newclass)

    def newdef(self, name, args=None, definition=None, local=True):
        """
        Create a \\def

        Required Arguments:
        name -- name of the macro to create
        args -- string containing the TeX argument profile
        definition -- string containing the LaTeX definition

        Keyword Arguments:
        local -- indicates whether this macro is local or global

        Examples::
            c.newdef('bold', '#1', '{\\bf #1}')
            c.newdef('put', '(#1,#2)#3', '\\dostuff{#1}{#2}{#3}')

        """
        # Macro already exists
#       if self.has_key(name):
#           if not issubclass(self[name], (plasTeX.NewCommand,
#                                          plasTeX.Definition)):
#               return
#           macrolog.debug('redefining definition "%s"', name)

        if isinstance(definition, str):
            definition = list(Tokenizer(definition, self))

        macrolog.debug('creating def %s', name)
        newclass = type(name, (plasTeX.Definition,),
                       {'args':args, 'definition':definition})

        if local:
            self.addLocal(name, newclass)
        else:
            self.addGlobal(name, newclass)

    def get_let(self, command):
        for context in reversed(self.contexts):
            try:
                return context.lets[command]
            except KeyError:
                pass
        return command

    def let(self, dest, source):
        """
        Create a \\let

        Required Arguments:
        dest -- the command sequence to create
        source -- the token to set the command sequence equivalent to

        Examples::
            c.let('bgroup', BeginGroup('{'))

        """
        # Use nodeName instead of macroName to work with Macros as well as
        # EscapeSequence, e.g. when we do
        # \expandafter\let\csname foo\endcsname=1
        if source.catcode == Token.CC_ESCAPE:
            self.top[dest.nodeName] = self[source.nodeName]
        else:
            self.top.lets[dest.nodeName] = source

    def chardef(self, name, num):
        """
        Create a \\chardef

        Required Arguments:
        name -- name of command to create
        num -- character number to use

        """
        # Generate a new chardef class
        macrolog.debug('creating chardef (8-bit) %s', name)
        newclass = type(name, (plasTeX.Command,),
                                {'str':chr(num)})
        self.addGlobal(name, newclass)

    def mathchardef(self, name, num):
        """
        Create a \\mathchardef

        Required Arguments:
        name -- name of command to create
        num -- character number to use

        """
        # Generate a new chardef class
        macrolog.debug('creating mathchardef (16-bit) %s', name)
        newclass = type(name, (plasTeX.Command,),
                                {'str':chr(num)})
        self.addGlobal(name, newclass)
