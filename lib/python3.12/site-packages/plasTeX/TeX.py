"""
TeX

This module contains the facilities for parsing TeX and LaTeX source.
The `TeX' class is an iterator interface to (La)TeX source.  Simply
feed a `TeX' instance using the input method, then iterate over the
expanded tokens through the standard Python iterator interface.

Example:
    tex = TeX()
    tex.input(open('foo.tex','r'))
    for token in tex:
        print token

"""
from io import IOBase
from typing import Optional, List
import string, os, sys, plasTeX, subprocess
from plasTeX.Tokenizer import Tokenizer, Token, EscapeSequence, Other
from plasTeX import TeXDocument
from plasTeX.Base.TeX.Primitives import MathShift
from plasTeX import ParameterCommand, Macro
from plasTeX import glue, muglue, mudimen, dimen, number
from plasTeX.Logging import getLogger, disableLogging, fileLogging

# Only export the TeX class
__all__ = ['TeX']

log = getLogger()

status = getLogger('status')
_type = type

class bufferediter(object):
    """ Buffered iterator """
    def __init__(self, obj):
        self._next = iter(obj).__next__
        self._buffer = []
    def __iter__(self):
        return self
    def __next__(self):
        if self._buffer:
            return self._buffer.pop()
        return self._next()
    def push(self, value):
        self._buffer.append(value)

class ArgumentContext(plasTeX.Macro):
    pass

class TeX(object):
    """
    TeX Stream

    This class is the central TeX engine that does all of the
    parsing, invoking of macros, etc.

    """
    documentClass = TeXDocument

    def __init__(self, ownerDocument=None, file=None):
        if ownerDocument is None:
            ownerDocument = self.documentClass()
            self.toplevel = True
        elif file:
            self.toplevel = True
        else:
            self.toplevel = False
        self.ownerDocument = ownerDocument

        # Input source stack
        self.inputs = []

        # Auxiliary files loaded
        self.auxFiles = []

        # TeX arguments types and their casting functions
        self.argtypes = {
            'url': (self.castNone, {'#':12,'~':12,'%':12,'&':12}),
            'str': self.castString,
            str: self.castString,
            'chr': self.castString,
            chr: self.castString,
            'char': self.castString,
            'cs': self.castControlSequence,
            'label': self.castLabel,
            'id': self.castLabel,
            'idref': self.castRef,
            'ref': self.castRef,
            'nox': lambda x,**y: x,
            'list': self.castList,
            list: self.castList,
            'dict': self.castDictionary,
            dict: self.castDictionary,

            # LaTeX versions of TeX internal parameters
            'dimen': self.castDimen,
            'dimension': self.castDimen,
            'length': self.castDimen,
#           'mudimen': self.castMuDimen,
#           'glue':  self.castGlue,
#           'muglue': self.castMuGlue,
            'number': self.castNumber,
            'count': self.castNumber,
            'int': self.castNumber,
            int: self.castNumber,
            'float': self.castDecimal,
            float: self.castDecimal,
            'double': self.castDecimal,
        }

        # Starting parsing if a source was given
        self.currentInput = (0,0)

        self.jobname = None
        if file is not None:
            # Filename
            if isinstance(file, (str, bytes)):
                file = str(file)
                '''
                if config has no files structure
                or encoding is not specified
                or encoding is utf-8, make encoding utf_8_sig.
                otherwise, use the specified encoding.
                '''
                try:
                    encoding = self.ownerDocument.config['files'].get('input-encoding', 'utf_8_sig')
                except (KeyError, AttributeError):
                    encoding = 'utf_8_sig'

                if encoding in ['utf8', 'utf-8', 'utf_8']:
                    encoding = 'utf_8_sig'

                fname = self.kpsewhich(file)
                self.input(open(fname, encoding=encoding))
                self.jobname = os.path.basename(os.path.splitext(file)[0])

            # File object
            else:
                self.input(file)
                self.jobname = os.path.basename(os.path.splitext(file.name)[0])

    def input(self, source):
        """
        Add a new input source to the stack

        Required Arguments:
        source -- can be a string containing TeX source, a file object
            which contains TeX source, or a list of tokens

        """
        if source is None:
            return
        if self.jobname is None:
            if isinstance(source, str):
                self.jobname = ''
            elif isinstance(source, IOBase):
                self.jobname = os.path.basename(os.path.splitext(source.name)[0])

        t = Tokenizer(source, self.ownerDocument.context)
        self.inputs.append((t, iter(t)))
        self.currentInput = self.inputs[-1]
        return self

    def endInput(self):
        """
        Pop the most recent input source from the stack

        """
        if self.inputs:
            old_input = self.inputs.pop()
            try:
                old_input[0].source.close()
            except AttributeError:
                pass
        if self.inputs:
            self.currentInput = self.inputs[-1]

    def loadPackage(self, file, options=None):
        """
        Load a LaTeX package

        Required Arguments:
        file -- name of the file to load

        Keyword Arguments:
        options -- options passed to the macro which is loading the package

        """
        options = options or {}
        config = self.ownerDocument.config

        try:
            path = self.kpsewhich(file)
        except OSError as msg:
            log.warning(msg)
            return False

        # Try to load the actual LaTeX style file
        status.info(' ( %s ' % path)

        try:
            encoding = config['files']['input-encoding']
            with open(path, 'r', encoding=encoding) as f:
                # Put in a flag so that we can parse past our own
                # package tokens and throw them away, we don't want them in
                # the output document.
                flag = plasTeX.Command()
                self.pushToken(flag)
                self.input(f)
                self.ownerDocument.context.packages[file] = options or {}
                for tok in self:
                    if tok is flag:
                        break

        except (OSError, IOError, TypeError) as msg:
            if msg:
                msg = ' ( %s )' % str(msg)
            # Failed to load LaTeX style file
            log.warning('Error opening package "%s"%s', file, msg)
            status.info(' ) ')
            return False

        status.info(' ) ')

        return True

    @property
    def filename(self):
        return self.currentInput[0].filename

    @property
    def lineNumber(self):
        return self.currentInput[0].lineNumber

    @property
    def lineInfo(self):
        return ' in %s on line %s' % (self.filename, self.lineNumber)

    @staticmethod
    def disableLogging():
        """ Turn off logging """
        disableLogging()

    def fileLogging(self):
        fname = '%s/%s.log' % (os.path.dirname(self.filename), self.jobname)
        fileLogging(fname)

    def itertokens(self):
        """
        Iterate over unexpanded tokens

        Returns:
        generator that iterates through the unexpanded tokens

        """
        # Create locals before going into generator loop
        inputs = self.inputs
        context = self.ownerDocument.context
        endInput = self.endInput
        ownerDocument = self.ownerDocument

        while inputs:
            # Always get next token from top of input stack
            try:
                while 1:
                    t = next(inputs[-1][-1])
                    # Save context depth of each token for use in digestion
                    t.contextDepth = context.depth
                    t.ownerDocument = ownerDocument
                    t.parentNode = None
                    yield t

            except StopIteration:
                endInput()

            # This really shouldn't happen, but just in case...
            except IndexError:
                break

    def __iter__(self):
        """
        Iterate over tokens while expanding them

        Returns:
        generator that iterates through the expanded tokens

        """
        # Cache variables before starting the generator
        next = self.itertokens().__next__
        pushToken = self.pushToken
        pushTokens = self.pushTokens
        createElement = self.ownerDocument.createElement
        ELEMENT_NODE = Macro.ELEMENT_NODE

        while 1:
            # Get the next token
            try:
                token = next()
            except StopIteration:
                return

            # Token is null, ignore it
            if token is None:
                continue

            # Macro that has already been expanded
            elif token.nodeType == ELEMENT_NODE:
                pass

            # We need to expand this one
            elif token.macroName is not None:
                try:
                    # By default, invoke() should put the macro instance
                    # itself into the output stream.  We'll handle this
                    # automatically here if `None' is received.  If you
                    # really don't want anything in the output stream,
                    # just return `[ ]'.
                    obj = createElement(token.macroName)
                    obj.contextDepth = token.contextDepth
                    obj.parentNode = token.parentNode
                    tokens = obj.invoke(self)
                    if tokens is None:
#                       log.info('expanding %s %s', token.macroName, obj)
                        pushToken(obj)
                    elif tokens:
#                       log.info('expanding %s %s', token.macroName, ''.join([x.source for x in tokens]))
                        pushTokens(tokens)
                    continue
                except Exception as message:
                    msg = str(message)
                    if msg.strip():
                        msg = ' (%s)' % msg.strip()
                    log.error('Error while expanding "%s"%s%s',
                              token.macroName, self.lineInfo, msg)
                    raise

#           tokenlog.debug('%s: %s', type(token), token.ownerDocument)

            yield token

    def createSubProcess(self):
        """
        Create a TeX instance using the same document context

        """
        # Push a new context for cleanup later
        tok = ArgumentContext()
        self.ownerDocument.context.push(tok)
        tex = type(self)(ownerDocument=self.ownerDocument)
        tex._endcontext = tok
        return tex

    def endSubProcess(self):
        """
        End the context of a sub-interpreter

        See Also:
        createSubProcess()

        """
        if hasattr(self, '_endcontext'):
            self.ownerDocument.context.pop(self._endcontext)

    def expandTokens(self, tokens, normalize=False, parentNode=None):
        """
        Expand a list of unexpanded tokens

        This can be used to expand tokens in a macro argument without
        having them sent to the output stream.

        Required Arguments:
        tokens -- list of tokens

        Returns:
        `TeXFragment' populated with expanded tokens

        """
        tex = self.createSubProcess()

        # Push the tokens and expand them
        tex.pushTokens(tokens)
        frag = tex.ownerDocument.createDocumentFragment()
        frag.parentNode = parentNode
        out = tex.parse(frag)

        # Pop all of our nested contexts off
        tex.endSubProcess()

        if normalize:
            out.normalize(getattr(tex.ownerDocument, 'charsubs', []))

        return out

    def parse(self, output=None):
        """
        Parse stream content until it is empty

        Keyword Arguments:
        output -- object to put the content in.  This should be either
            a TeXDocument or a TeXFragment

        Returns:
        `TeXDocument' instance

        """
        tokens = bufferediter(self)

        if output is None:
            output = self.ownerDocument

        try:
            for item in tokens:
                if item.nodeType == Macro.ELEMENT_NODE:
                    item.parentNode = output
                    item.digest(tokens)
                output.append(item)
        except Exception as message:
            msg = str(message)
            if msg.strip():
               msg = ' (%s)' % msg.strip()
            log.error('An error occurred while building the document object%s%s', self.lineInfo, msg)
            raise

        if self.toplevel:
            for order, callbacks in sorted(self.ownerDocument.postParseCallbacks.items()):
                for callback in callbacks:
                    callback()
        return output

    def textTokens(self, text):
        """
        Return a list of `Other` tokens from a string

        Required Arguments:
        text -- string containing text to be tokenized

        """
        return [Other(x) for x in text]

    def pushToken(self, token):
        """
        Push a token back into the token buffer to be re-read

        Required Arguments:
        token -- token to push back

        """
        if token is not None:
            if not self.inputs:
                self.input([token])
            else:
                self.inputs[-1][0].pushToken(token)

    def pushTokens(self, tokens):
        """
        Push a list of tokens back into the token buffer to be re-read

        Required Arguments:
        tokens -- list of tokens

        """
        if tokens:
            if not self.inputs:
                self.input(tokens)
            else:
                self.inputs[-1][0].pushTokens(tokens)

    def source(self, tokens):
        """
        Return the TeX source representation of the tokens

        Required Arguments:
        tokens -- list of tokens

        Returns:
        string containing the TeX source

        """
        return ''.join([x.source for x in tokens])

    def normalize(self, tokens):
        """
        Join consecutive character tokens into a string

        Required Arguments:
        tokens -- list of tokens

        Returns:
        string unless the tokens contain values that cannot be casted
        to a string.  In that case, the original tokens are returned
        in a TeXFragment instance

        """
        if tokens is None:
            return tokens

        grouptokens = [Token.CC_EGROUP, Token.CC_BGROUP]
        textTokens = [Token.CC_LETTER, Token.CC_OTHER,
                      Token.CC_EGROUP, Token.CC_BGROUP,
                      Token.CC_SPACE]

        try: iter(tokens)
        except TypeError: return tokens

        for t in tokens:
            if isinstance(t, str):
                continue
            # Element nodes can't be part of normalized text
            if t.nodeType == Macro.ELEMENT_NODE:
                if len(tokens) == 1:
                    return tokens.pop()
                t = self.ownerDocument.createDocumentFragment()
                t.extend(tokens)
                t.normalize(getattr(self.ownerDocument, 'charsubs', []))
                return t
            if t.catcode not in textTokens:
                if len(tokens) == 1:
                    return tokens.pop()
                t = self.ownerDocument.createDocumentFragment()
                t.ownerDocument = self.ownerDocument
                t.parentNode = None
                t.extend(tokens)
                t.normalize(getattr(self.ownerDocument, 'charsubs', []))
                return t

        return (''.join([x for x in tokens
                          if getattr(x, 'catcode', Token.CC_OTHER)
                             not in grouptokens])).strip()

    def processIfContent(self, which, debug=False):
        """
        Process the requested portion of the `if' block

        Required Arguments:
        which -- the case to return.  If this is a boolean, a value of
            `True' will return the first part of the `if' block.  If it
            is `False', it will return the `else' portion.  If this is
            an integer, the `case' matching this integer will be returned.

        """
        # Since the true content always comes first, we need to set
        # True to case 0 and False to case 1.
        elsefound = False
        if isinstance(which, bool):
            if which: which = 0
            else: which = 1

        cases = [[]]
        nesting = 0
        correctly_terminated = False
        iterator = self.itertokens()

        for t in iterator:
            name = getattr(t, 'macroName', '') or ''
            if name == 'newif':
                cases[-1].append(t)
                cases[-1].append(next(iterator))
                continue
            elif name.startswith('if'):
                cases[-1].append(t)
                nesting += 1
            elif name == 'fi':
                if not nesting:
                    correctly_terminated = True
                    break
                cases[-1].append(t)
                nesting -= 1
            elif not(nesting) and name == 'else':
                cases.append([])
                continue
            elif not(nesting) and name == 'or':
                cases.append([])
                continue
            else:
                cases[-1].append(t)

        if not correctly_terminated:
            log.warning(r'\end occurred when \if was incomplete')

        # else case for ifs without elses
        cases.append([])

        # Push if-selected tokens back into tokenizer
        self.pushTokens(cases[which])

    def readArgument(self, *args, **kwargs):
        """
        Return an argument without the TeX source that created it

        See Also:
        self.readArgumentAndSource()

        """
        return self.readArgumentAndSource(*args, **kwargs)[0]

    def readArgumentAndSource(self, spec=None, type=None, subtype=None,
                    delim=',', expanded=False, default=None, parentNode=None,
                    name=None, stripLeadingWhitespace=True,
                    charsubs: Optional[List] = None):
        """
        Get an argument and the TeX source that created it

        Optional Arguments:
        spec -- string containing information about the type of
            argument to get.  If it is 'None', the next token is
            returned.  If it is a two-character string, a grouping
            delimited by those two characters is returned (i.e. '[]').
            If it is a single-character string, the stream is checked
            to see if the next character is the one specified.
            In all cases, if the specified argument is not found,
            'None' is returned.
        type -- data type to cast the argument to.  New types can be
            added to the self.argtypes dictionary.  The key should
            match this 'type' argument and the value should be a callable
            object that takes a list of tokens as the first argument
            and a list of unspecified keyword arguments (i.e. **kwargs)
            for type specific information such as list delimiters.
        subtype -- data type to use for elements of a list or dictionary
        delim -- item delimiter for list and dictionary types
        expanded -- boolean indicating whether the argument content
            should be expanded or just returned as an unexpanded
            text string
        default -- value to return if the argument doesn't exist
        parentNode -- the node that the argument belongs to
        name -- the name of the argument being parsed
        stripLeadingWhitespace -- if True, whitespace is skipped before
            looking for the argument
        charsubs -- a list of character substitution to apply to the
            argument. If None is provided then the document charsubs
            attribute will be used if it exists, otherwise an empty
            list will be used.

        Returns:
        tuple where the first argument is:

        None -- if the argument wasn't found
        object of type `type` -- if `type` was specified
        list of tokens -- for all other arguments

        The second argument is a string containing the TeX source
        for the argument.

        """
        if stripLeadingWhitespace:
            self.readOptionalSpaces()

        # Disable expansion of parameters
        ParameterCommand.disable()

        if charsubs is None:
            charsubs = getattr(self.ownerDocument, 'charsubs', [])

        if type in ['Dimen','Length','Dimension']:
            n = self.readDimen()
            ParameterCommand.enable()
            return n, n.source

        if type in ['MuDimen','MuLength']:
            n = self.readMuDimen()
            ParameterCommand.enable()
            return n, n.source

        if type in ['Glue','Skip']:
            n = self.readGlue()
            ParameterCommand.enable()
            return n, n.source

        if type in ['MuGlue','MuSkip']:
            n = self.readMuGlue()
            ParameterCommand.enable()
            return n, n.source

        if type in ['Number','Int','Integer']:
            n = self.readNumber()
            ParameterCommand.enable()
            return n, n.source

        if type in ['Token','Tok']:
            for tok in self.itertokens():
                ParameterCommand.enable()
                return tok, tok.source

        if type in ['XTok','XToken']:
            self.ownerDocument.context.warnOnUnrecognized = False
            for t in self.itertokens():
                if t.catcode == Token.CC_BGROUP:
                    self.pushToken(t)
                    toks, source = self.readToken(True)
                    if len(toks) == 1:
                        ParameterCommand.enable()
                        return toks[0], toks[0].source
                    ParameterCommand.enable()
                    return toks, source
                else:
                    toks = self.expandTokens([t], parentNode=parentNode)
                    if len(toks) == 1:
                        ParameterCommand.enable()
                        return toks[0], toks[0].source
                    ParameterCommand.enable()
                    return toks, self.source(toks)

        # Definition argument string
        if type in ['Args']:
            args = []
            for t in self.itertokens():
                if t.catcode == Token.CC_BGROUP:
                    self.pushToken(t)
                    break
                else:
                    args.append(t)
            else: pass
            ParameterCommand.enable()
            return args, self.source(args)

        if type in ['any']:
            toks = []
            for t in self.itertokens():
                if t is None or t == '':
                    continue
                if t.catcode == Token.CC_SPACE:
                    break
                toks.append(t)
            return self.expandTokens(toks, parentNode=parentNode), self.source(toks)

        if type in ['cs']:
            expanded = False

        priorcodes = {}

        try:
            # Set catcodes for this argument type
            try:
                if isinstance(self.argtypes[type], (list,tuple)):
                    for key, value in list(self.argtypes[type][1].items()):
                        priorcodes[key] = self.ownerDocument.context.whichCode(key)
                        self.ownerDocument.context.catcode(key, value)
            except KeyError:
                pass

            # Get a TeX token (i.e. {...})
            if spec is None:
                toks, source = self.readToken(expanded, parentNode=parentNode)

            # Get a single character argument
            elif len(spec) == 1:
                toks, source = self.readCharacter(spec)

            # Get an argument grouped by the given characters (e.g. [...], (...))
            elif len(spec) == 2:
                toks, source = self.readGrouping(spec, expanded, parentNode=parentNode)

            # This isn't a correct value
            else:
                raise ValueError('Unrecognized specifier "%s"' % spec)

        except Exception as msg:
            log.error('Error while reading argument "%s" of %s%s (%s)' % \
                          (name, parentNode.nodeName, self.lineInfo, msg))
            raise

        # Set catcodes back to original values
        for key, value in list(priorcodes.items()):
            self.ownerDocument.context.catcode(key, value)

        if toks is None:
            ParameterCommand.enable()
            return default, ''
        res = self.cast(toks, type, subtype, delim, parentNode, name)

        # Normalize any document fragments
        if expanded and \
           getattr(res,'nodeType',None) == Macro.DOCUMENT_FRAGMENT_NODE:
            res.normalize(charsubs)

        # Re-enable Parameters
        ParameterCommand.enable()

        if False and parentNode is not None:
            log.warning('%s %s: %s', parentNode.nodeName, name, source)
            log.warning('categories: %s', self.ownerDocument.context.categories)
            log.warning('stack: %s', self.ownerDocument.context.top)

        return res, source

    def readToken(self, expanded=False, parentNode=None):
        """
        Read a token or token group

        Returns:
        two element tuple containing the parsed tokens and the
        TeX code that they came from

        """
        tokens = self.itertokens()
        isgroup = False
        for t in tokens:
            toks = []
            source = [t]
            # A { ... } grouping was found
            if t.catcode == Token.CC_BGROUP:
                isgroup = True
                level = 1
                for t in tokens:
                    source.append(t)
                    if t.catcode == Token.CC_BGROUP:
                        toks.append(t)
                        level += 1
                    elif t.catcode == Token.CC_EGROUP:
                        level -= 1
                        if level == 0:
                            break
                        toks.append(t)
                    else:
                        toks.append(t)
            # A math token was found (i.e., $ ... $)
            elif t.catcode == Token.CC_MATHSHIFT or isinstance(t, MathShift):
                toks.append(t)
                for t in tokens:
                    source.append(t)
                    toks.append(t)
                    if t.catcode == Token.CC_MATHSHIFT or isinstance(t, MathShift):
                        break
            else:
                toks.append(t)

            # Expand macros and get the argument source string
            if expanded:
                toks = self.expandTokens(toks, parentNode=parentNode)
                if isgroup:
                    s = self.source(toks)
                    source = '%s%s%s' % (source[0].source, s,
                                          source[-1].source)
                else:
                    source = self.source(toks)
            else:
                source = self.source(source)

            return toks, source

        return None, ''

    def readCharacter(self, char):
        """
        Read a character from the stream

        Required Arguments:
        char -- the character that is expected

        Returns:
        two element tuple containing the parsed token and the
        TeX code that it came from

        """
        for t in self.itertokens():
            if t == char:
                return t, self.source([t])
            else:
                self.pushToken(t)
                break
        return None, ''

    def readGrouping(self, chars, expanded=False, parentNode=None):
        """
        Read a group delimited by the given characters

        Keyword Arguments:
        chars -- the two characters that begin and end the group

        Returns:
        two element tuple containing the parsed tokens and the
        TeX code that they came from

        """
        tokens = self.itertokens()
        begin, end = Other(chars[0]), Other(chars[1])
        source = []
        for t in tokens:
            toks = []
            source = [t]
            # A [ ... ], ( ... ), etc. grouping was found
            if t.catcode != Token.CC_ESCAPE and \
               (t == begin or str(t) == str(begin)):
                level = 1
                for t in tokens:
                    source.append(t)
                    if t.catcode != Token.CC_ESCAPE and \
                       (t == begin or str(t) == str(begin)):
                        toks.append(t)
                        level += 1
                    elif t.catcode != Token.CC_ESCAPE and \
                         (t == end or str(t) == str(end)):
                        level -= 1
                        if level == 0:
                            break
                        toks.append(t)
                    else:
                        toks.append(t)
            else:
                self.pushToken(t)
                break
            if expanded:
                toks = self.expandTokens(toks, parentNode=parentNode)
                source = begin + self.source(toks) + end
            else:
                source = self.source(source)
            return toks, source
        return None, ''

    def readInternalType(self, tokens, method):
        """
        Read an internal type from the given tokens

        Required Arguments:
        tokens -- list of tokens that contain the internal value
        method -- reference to the method to parse the tokens

        Returns:
        instance of the TeX type

        """
        # Throw a \relax in here to keep the token after the
        # argument from being expanded when parsing the internal type
        self.pushToken(EscapeSequence('relax'))
        self.pushTokens(tokens)

        # Call the appropriate parsing method for this type
        result = method()

        # Get rid of the \relax token inserted above
        for t in self.itertokens():
            if (t.nodeType == Token.ELEMENT_NODE and t.nodeName == 'relax') \
               or t.macroName == 'relax':
                break

        return result

    def cast(self, tokens, dtype, subtype=None, delim=',',
                   parentNode=None, name=None):
        """
        Cast the tokens to the appropriate type

        This method is used to convert tokens into Python objects.
        This happens when the user has specified that a macro argument
        should be a dictionary (e.g. foo:dict),
        a list (e.g. foo:list), etc.

        Required Arguments:
        tokens -- list of raw, unflattened and unnormalized tokens
        dtype -- reference to the requested datatype

        Optional Arguments:
        subtype -- data type for elements of a list or dictionary
        delim -- delimiter character for list and dictionary types

        Returns:
        object of the specified type

        """
        argtypes = {}
        for key, t in self.argtypes.items():
            if isinstance(t, tuple):
                argtypes[key] = t[0]
            else:
                argtypes[key] = t

        # No type specified
        if dtype is None:
            pass

        # Could not find specified type
        elif dtype not in argtypes.keys():
            log.warning('Could not find datatype "%s"' % dtype)

        # Casting to specified type
        else:
            tokens = argtypes[dtype](tokens, subtype=subtype,
                     delim=delim, parentNode=parentNode, name=name)

        # Set parent node as needed
        if getattr(tokens,'nodeType',None) == Macro.DOCUMENT_FRAGMENT_NODE:
            tokens.parentNode = parentNode

        return tokens

    def castNone(self, tokens, **kwargs):
        return tokens

    def castControlSequence(self, tokens, **kwargs):
        """
        Limit the argument to a single non-space token

        Required Arguments:
        tokens -- list of tokens to cast

        See Also:
        self.readArgument()
        self.cast()

        """

        return [x for x in tokens if x.catcode == Token.CC_ESCAPE].pop(0)

    def castString(self, tokens, type=str, **kwargs):
        """
        Join the tokens into a string

        Required Arguments:
        tokens -- list of tokens to cast

        Keyword Arguments:
        type -- the string class to use for the returned object

        Returns:
        string

        See Also:
        self.readArgument()
        self.cast()

        """
        return type(self.normalize(tokens))

    def castLabel(self, tokens, **kwargs):
        """
        Join the tokens into a string and set a label in the context

        Required Arguments:
        tokens -- list of tokens to cast

        Returns:
        string

        See Also:
        self.readArgument()
        self.cast()
        self.castRef()

        """
        label = self.castString(tokens, **kwargs)
        self.ownerDocument.context.label(label)
        return label

    def castRef(self, tokens, **kwargs):
        """
        Join the tokens into a string and set a reference in the context

        Required Arguments:
        tokens -- list of tokens to cast

        Returns:
        string

        See Also:
        self.readArgument()
        self.cast()
        self.castLabel()

        """
        ref = self.castString(tokens, **kwargs)
        self.ownerDocument.context.ref(kwargs['parentNode'], kwargs['name'], ref)
        return ref

    def castNumber(self, tokens, **kwargs):
        """
        Join the tokens into a string and turn the result into an integer

        Required Arguments:
        tokens -- list of tokens to cast

        Keyword Arguments:
        type -- the integer class to use for the returned object

        Returns:
        integer

        See Also:
        self.readArgument()
        self.cast()

        """
#       try: return number(self.castString(tokens, **kwargs))
#       except: return number(0)
        return self.readInternalType(tokens, self.readNumber)

    def castDecimal(self, tokens, **kwargs):
        """
        Join the tokens into a string and turn the result into a float

        Required Arguments:
        tokens -- list of tokens to cast

        Keyword Arguments:
        type -- the float class to use for the returned object

        Returns:
        float

        See Also:
        self.readArgument()
        self.cast()

        """
#       try: return self.castString(tokens, **kwargs)
#       except: return decimal(0)
        return self.readInternalType(tokens, self.readDecimal)

    def castDimen(self, tokens, **kwargs):
        """
        Join the tokens into a string and convert the result into a `dimen`

        Required Arguments:
        tokens -- list of tokens to cast

        Returns:
        `dimen` instance

        See Also:
        self.readArgument()
        self.cast()

        """
#       try: return dimen(self.castString(tokens, **kwargs))
#       except: return dimen(0)
        return self.readInternalType(tokens, self.readDimen)

    def castMuDimen(self, tokens, **kwargs):
        """
        Join the tokens into a string and convert the result into a `MuDimen`

        Required Arguments:
        tokens -- list of tokens to cast

        Returns:
        `MuDimen` instance

        See Also:
        self.readArgument()
        self.cast()

        """
#       try: return mudimen(self.castString(tokens, **kwargs))
#       except: return mudimen(0)
        return self.readInternalType(tokens, self.readMuDimen)

    def castGlue(self, tokens, **kwargs):
        """
        Join the tokens into a string and convert the result into a `Glue`

        Required Arguments:
        tokens -- list of tokens to cast

        Returns:
        `Glue` instance

        See Also:
        self.readArgument()
        self.cast()

        """
#       try: return glue(self.castString(tokens, **kwargs))
#       except: return glue(0)
        return self.readInternalType(tokens, self.readGlue)

    def castMuGlue(self, tokens, **kwargs):
        """
        Join the tokens into a string and convert the result into a `MuGlue`

        Required Arguments:
        tokens -- list of tokens to cast

        Returns:
        `MuGlue` instance

        See Also:
        self.readArgument()
        self.cast()

        """
#       try: return muglue(self.castString(tokens, **kwargs))
#       except: return muglue(0)
        return self.readInternalType(tokens, self.readMuGlue)

    def castList(self, tokens, type=list, **kwargs):
        """
        Parse items delimited by the given delimiter into a list

        Required Arguments:
        tokens -- TeXFragment of tokens to cast

        Keyword Arguments:
        type -- the list class to use for the returned object
        delim -- the delimiter that separates each element of the list.
            The default delimiter is ','.

        Returns:
        list

        See Also:
        self.readArgument()
        self.cast()

        """
        delim = kwargs.get('delim')
        if delim is None:
            delim = ','
        subtype = kwargs.get('subtype')
        listarg = [[]]
        while tokens:
            current = tokens.pop(0)

            # Item delimiter
            if current == delim:
                listarg.append([])

            # Found grouping
            elif current.catcode == Token.CC_BGROUP:
                level = 1
                listarg[-1].append(current)
                while tokens:
                    current = tokens.pop(0)
                    if current.catcode == Token.CC_BGROUP:
                        level += 1
                    elif current.catcode == Token.CC_EGROUP:
                        level -= 1
                        if not level:
                            break
                    listarg[-1].append(current)
                listarg[-1].append(current)

            else:
                listarg[-1].append(current)

        return type([self.normalize(self.cast(x, subtype)) for x in listarg])

    def castDictionary(self, tokens, type=dict, **kwargs):
        """
        Parse key/value pairs into a dictionary

        Required Arguments:
        tokens -- TeXFragment of tokens to cast

        Keyword Arguments:
        type -- the dictionary class to use for the returned object
        delim -- the delimiter that separates each element of the list.
            The default delimiter is ','.

        Returns:
        dictionary

        See Also:
        self.readArgument()
        self.cast()

        """
        delim = kwargs.get('delim')
        if delim is None:
            delim = ','
        subtype = kwargs.get('subtype')
        dictarg = type()
        currentkey = []
        currentvalue = None
        while tokens:
            current = tokens.pop(0)

            if current.nodeType == Macro.ELEMENT_NODE:
                currentvalue.append(current)
                continue

            # Found grouping
            elif current.catcode == Token.CC_BGROUP:
                level = 1
                currentvalue.append(current)
                while tokens:
                    current = tokens.pop(0)
                    if current.catcode == Token.CC_BGROUP:
                        level += 1
                    elif current.catcode == Token.CC_EGROUP:
                        level -= 1
                        if not level:
                            break
                    currentvalue.append(current)
                currentvalue.append(current)
                continue

            # Found end-of-key delimiter
            if current == '=':
                currentvalue = []

            # Found end-of-value delimiter
            elif current == delim:
                # Handle this later
                pass

            # Extend key
            elif currentvalue is None:
                currentkey.append(current)

            # Extend value
            else:
                currentvalue.append(current)

            # Found end-of-value delimiter
            if current == delim or not tokens:
                currentkey = self.normalize(currentkey)
                currentvalue = self.normalize(self.cast(currentvalue, subtype))
                if currentvalue is None:
                    currentvalue = True
                dictarg[currentkey] = currentvalue
                currentkey = []
                currentvalue = None

        if currentkey:
            currentkey = self.normalize(currentkey)
            currentvalue = self.normalize(self.cast(currentvalue, subtype))
            if currentvalue is None:
                currentvalue = True
            dictarg[currentkey] = currentvalue

        return dictarg

    def kpsewhich(self, name):
        """
        Locate the given file using kpsewhich

        Required Arguments:
        name -- name of file to find

        Returns:
        full path to file -- if it is found

        """
        # When, for example, ``\Input{name}`` is encountered, we should look in
        # the directory containing the file being processed. So the following
        # code adds the directory to the start of $TEXINPUTS.
        TEXINPUTS = os.environ.get("TEXINPUTS",'')
        try:
            srcDir = os.path.dirname(self.filename)
        except AttributeError:
            # I think this happens only for the command line file.
            pass
        else:
            if TEXINPUTS:
                os.environ["TEXINPUTS"] = "%s%s%s%s" % (srcDir, os.path.pathsep, TEXINPUTS, os.path.pathsep)
            else:
                os.environ["TEXINPUTS"] = "%s%s" % (srcDir, os.path.pathsep)

        def restore_texinputs():
            # Undo any mods to $TEXINPUTS.
            if TEXINPUTS:
                os.environ["TEXINPUTS"] = TEXINPUTS
            else:
                os.environ.pop("TEXINPUTS", None)

        try:
            program = self.ownerDocument.config['general']['kpsewhich']

            kwargs = {'stdout':subprocess.PIPE}
            if sys.platform.lower().startswith('win'):
                kwargs['shell'] = True

            output = subprocess.Popen([program, name], **kwargs).communicate()[0].strip()
            output = output.decode('utf-8')
            if output:
                restore_texinputs()
                return output

        except:
            fullname = ''
            paths = os.environ.get("TEXINPUTS", '.').split(os.path.pathsep)
            for path in [x for x in paths if x]:
                if name in os.listdir(path):
                    fullname = os.path.join(path,name)
                    break
            if fullname:
                restore_texinputs()
                return fullname

        restore_texinputs()
        raise FileNotFoundError('Could not find any file named: %s' % name)

#
# Parsing helper methods for parsing numbers, spaces, dimens, etc.
#

    def readOptionalSpaces(self):
        """ Remove all whitespace """
        tokens = []
        for t in self.itertokens():
            if t.nodeType == t.ELEMENT_NODE:
                self.pushToken(t)
                break
            elif t is None or t == '':
                continue
            elif t.catcode != Token.CC_SPACE:
                self.pushToken(t)
                break
            tokens.append(t)
        return tokens

    def readKeyword(self, words, optspace=True):
        """
        Read keyword from the stream

        Required Arguments:
        words -- list of possible keywords to get from the stream

        Keyword Arguments:
        optspace -- boolean indicating if it should eat an optional
            space token after a matched keyword

        Returns:
        matched keyword -- if one is found
        `None' -- if none of the keywords are found

        """
        self.readOptionalSpaces()
        for word in words:
            matched = []
            letters = list(word.upper())
            for t in self.itertokens():
                if t.nodeType == Token.ELEMENT_NODE:
                    break
                matched.append(t)
                if t.upper() == letters[0]:
                    letters.pop(0)
                    if not letters:
                        if optspace:
                            self.readOneOptionalSpace()
                        return word
                else:
                    break
            self.pushTokens(matched)
        return None

    def readDecimal(self):
        """ Read a decimal number from the stream """
        sign = self.readOptionalSigns()
        for t in self:
            if t.nodeType == Token.ELEMENT_NODE:
                self.pushToken(t)
                break
            if t in string.digits:
                num = t + self.readSequence(string.digits, False)
                for t in self:
                    if t.nodeType == Token.ELEMENT_NODE:
                        self.pushToken(t)
                        return sign * float(num)
                    elif t in '.,':
                        num += '.' + self.readSequence(string.digits, default='0')
                    else:
                        self.pushToken(t)
                        return sign * float(num)
                    break
                return sign * float(num)
            if t in '.,':
                return sign * float('.' + self.readSequence(string.digits, default='0'))
            if t in '\'"`':
                self.pushToken(t)
                return sign * self.readInteger()
            break
        log.warning('Missing decimal%s, treating as `0`.', self.lineInfo)
        return float(0)

    def readDimen(self, units=dimen.units):
        """
        Read a dimension from the stream

        Keyword Arguments:
        units -- list of acceptable units of measure

        Returns:
        `dimen' instance

        """
        ParameterCommand.disable()
        sign = self.readOptionalSigns()
        for t in self:
            if t.nodeType == Macro.ELEMENT_NODE and \
               isinstance(t, ParameterCommand):
                ParameterCommand.enable()
                return dimen(sign * dimen(t))
            self.pushToken(t)
            break
        num = dimen(sign * self.readDecimal() * self.readUnitOfMeasure(units=units))
        ParameterCommand.enable()
        return num

    def readMuDimen(self):
        """ Read a mudimen from the stream """
        return mudimen(self.readDimen(units=mudimen.units))

    def readUnitOfMeasure(self, units):
        """
        Read a unit of measure from the stream

        Required Arguments:
        units -- list of acceptable units of measure

        Returns:
        `dimen' instance

        """
        self.readOptionalSpaces()
        ParameterCommand.disable()
        # internal unit
        for t in self:
            if t.nodeType == Macro.ELEMENT_NODE and \
               isinstance(t, ParameterCommand):
                ParameterCommand.enable()
                return dimen(t)
            self.pushToken(t)
            break
        true = self.readKeyword(['true'])
        unit = self.readKeyword(units)
        if unit is None:
            log.warning('Missing unit (expecting %s)%s, treating as `%s`',
                        ', '.join(units), self.lineInfo, units[0])
            unit = units[0]
        ParameterCommand.enable()
        return dimen('1%s' % unit)

    def readOptionalSigns(self):
        """
        Read optional + and - signs

        Returns:
        +1 or -1

        """
        sign = 1
        self.readOptionalSpaces()
        for t in self:
            if t.nodeType == Token.ELEMENT_NODE:
                self.pushToken(t)
                break
            elif t == '+':
                pass
            elif t == '-':
                sign = -sign
            elif t is None or t == '' or t.catcode == Token.CC_SPACE:
                continue
            else:
                self.pushToken(t)
                break
        return sign

    def readOneOptionalSpace(self):
        """ Read one optional space from the stream """
        for t in self.itertokens():
            if t.nodeType == Token.ELEMENT_NODE:
                self.pushToken(t)
                return None
            if t is None or t == '':
                continue
            if t.catcode == Token.CC_SPACE:
                return t
            self.pushToken(t)
            return None

    def readSequence(self, chars, optspace=True, default=''):
        """
        Read a sequence of characters from a given set

        Required Arguments:
        chars -- sequence of characters that should be accepted

        Keyword Arguments:
        optspace -- boolean indicating if an optional space should
            be absorbed after the sequence of characters
        default -- string to return if none of the characters in
            the given set are found

        Returns:
        string of characters matching those in the sequence `chars'
        or `default' if none are found

        """
        output = []
        for t in self:
            if t.nodeType == Macro.ELEMENT_NODE:
                self.pushToken(t)
                break
            if t not in chars:
                if optspace and t.catcode == Token.CC_SPACE:
                    pass
                else:
                    self.pushToken(t)
                break
            output.append(t)
        if not output:
            return default
        return ''.join(output)

    def readInteger(self, optspace=True):
        """
        Read an integer from the stream

        Returns:
        `number` instance

        """
        ParameterCommand.disable()
        num = None
        sign = self.readOptionalSigns()

        for t in self:
            # internal/coerced integers
            if t.nodeType == Macro.ELEMENT_NODE:
                if isinstance(t, ParameterCommand):
                    num = number(sign * number(t))
                else:
                    self.pushToken(t)
                    break
            # integer constant
            elif t in string.digits:
                num = number(sign * int(t + self.readSequence(string.digits,
                                                              optspace=optspace)))
                for t in self:
                    if t.nodeType == Macro.ELEMENT_NODE and \
                       isinstance(t, ParameterCommand):
                        num = number(num * number(t))
                    else:
                        self.pushToken(t)
                    break
            # octal constant
            elif t == "'":
                num = number(sign * int('0' + self.readSequence(string.octdigits,
                                                   default='0', optspace=optspace), 8))
            # hex constant
            elif t == '"':
                num = number(sign * int('0x' + self.readSequence(string.hexdigits,
                                               default='0', optspace=optspace), 16))
            # character token
            elif t == '`':
                for t in self.itertokens():
                    num = number(sign * ord(t))
                    break
            break
        ParameterCommand.enable()
        if num is not None:
            return num
        log.warning('Missing number%s, treating as `0`. (%s)', self.lineInfo, t)
        return number(0)

    readNumber = readInteger

    def readGlue(self):
        """ Read a glue parameter from the stream """
        ParameterCommand.disable()
        sign = self.readOptionalSigns()
        # internal/coerced glue
        for t in self:
            if t.nodeType == Macro.ELEMENT_NODE and \
               isinstance(t, ParameterCommand):
                ParameterCommand.enable()
                return glue(sign * glue(t))
            self.pushToken(t)
            break
        dim = self.readDimen()
        stretch = self.readStretch()
        shrink = self.readShrink()
        ParameterCommand.enable()
        return glue(sign*dim, stretch, shrink)

    def readStretch(self):
        """ Read a stretch parameter from the stream """
        if self.readKeyword(['plus']):
            return self.readDimen(units=dimen.units+['filll','fill','fil'])
        return None

    def readShrink(self):
        """ Read a shrink parameter from the stream """
        if self.readKeyword(['minus']):
            return self.readDimen(units=dimen.units+['filll','fill','fil'])
        return None

    def readMuGlue(self):
        """ Read a muglue parameter from the stream """
        ParameterCommand.disable()
        sign = self.readOptionalSigns()
        # internal/coerced muglue
        for t in self:
            if t.nodeType == Macro.ELEMENT_NODE and \
               isinstance(t, ParameterCommand):
                ParameterCommand.enable()
                return muglue(sign * muglue(t))
            self.pushToken(t)
            break
        dim = self.readMuDimen()
        stretch = self.readMuStretch()
        shrink = self.readMuShrink()
        ParameterCommand.enable()
        return muglue(sign*dim, stretch, shrink)

    def readMuStretch(self):
        """ Read a mustretch parameter from the stream """
        if self.readKeyword(['plus']):
            return self.readDimen(units=mudimen.units+['filll','fill','fil'])
        return None

    def readMuShrink(self):
        """ Read a mushrink parameter from the stream """
        if self.readKeyword(['minus']):
            return self.readDimen(units=mudimen.units+['filll','fill','fil'])
        return None

    def loadAuxiliaryFile(self):
        """ Read in an auxiliary file (only once) """
        if self.jobname in self.auxFiles:
            return
        self.auxFiles.append(self.jobname)
        warn = self.ownerDocument.context.warnOnUnrecognized
        try:
            f = self.kpsewhich(self.jobname+'.aux')
            self.ownerDocument.context.warnOnUnrecognized = False
            dummy = plasTeX.Command()
            self.pushToken(dummy)
            self.input(open(f))
            for item in self:
                if item is dummy:
                    break
        except OSError as msg:
            log.warning(msg)
        self.ownerDocument.context.warnOnUnrecognized = warn

#   @property
#   def jobname(self):
#       """ Return the basename of the main input file """
#       print self.inputs
#       return os.path.basename(os.path.splitext(self.inputs[0][0].filename)[0])
