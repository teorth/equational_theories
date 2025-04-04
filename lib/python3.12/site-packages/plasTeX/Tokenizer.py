from plasTeX.DOM import Node, Text
from plasTeX import encoding
from io import BytesIO, StringIO, TextIOWrapper
from typing import Tuple, NewType, Optional, Callable, List, Generator

# Default TeX categories
DEFAULT_CATEGORIES = [
   '\\',  # 0  - Escape character
   '{',   # 1  - Beginning of group
   '}',   # 2  - End of group
   '$',   # 3  - Math shift
   '&',   # 4  - Alignment tab
   '\n',  # 5  - End of line
   '#',   # 6  - Parameter
   '^',   # 7  - Superscript
   '_',   # 8  - Subscript
   '\x00',# 9  - Ignored character
   ' \t\r\f', # 10 - Space
   encoding.stringletters(), # - Letter
   '',    # 12 - Other character - This isn't explicitly defined.  If it
          #                        isn't any of the other categories, then
          #                        it's an "other" character.
   '~',   # 13 - Active character
   '%',   # 14 - Comment character
   ''     # 15 - Invalid character
]

VERBATIM_CATEGORIES = [''] * 16
VERBATIM_CATEGORIES[11] = encoding.stringletters()

CatCode = NewType('CatCode', int)

class Token(Text):
    """ Base class for all TeX tokens """

    # The 16 category codes defined by TeX
    CC_ESCAPE = CatCode(0)
    CC_BGROUP = CatCode(1)
    CC_EGROUP = CatCode(2)
    CC_MATHSHIFT = CatCode(3)
    CC_ALIGNMENT = CatCode(4)
    CC_EOL = CatCode(5)
    CC_PARAMETER = CatCode(6)
    CC_SUPER = CatCode(7)
    CC_SUB = CatCode(8)
    CC_IGNORED = CatCode(9)
    CC_SPACE = CatCode(10)
    CC_LETTER = CatCode(11)
    CC_OTHER = CatCode(12)
    CC_ACTIVE = CatCode(13)
    CC_COMMENT = CatCode(14)
    CC_INVALID = CatCode(15)

    TOKEN_SLOTS = __slots__ = Text.TEXT_SLOTS

    catcode = None       # type: Optional[CatCode] # TeX category code
    macroName = None     # type: Optional[str] # Macro to invoke in place of this token

    def __repr__(self):
        return self.source

    def __eq__(self, other):
        if isinstance(other, Token):
            return (self is other
            or (self.catcode == other.catcode and super(Token,self).__eq__(other)))
        return super(Token,self).__eq__(str(other))

    def __ne__(self, other):
        try:
            return self.catcode != other.catcode or super(Token,self).__ne__(other)
        except AttributeError:
            return NotImplemented

    def __hash__(self):
        return super(Token,self).__hash__()

    def __lt__(self, other):
        if isinstance(other, Token):
            if self.catcode == other.catcode:
                return str(self) < str(other)
            else:
                return self.catcode <  other.catcode
        else:
            return str(self) <  str(other)

    def __str__(self):
        return self.encode('utf-8').decode('utf-8')


    @property
    def source(self):
        return self


class EscapeSequence(Token):
    """
    Escape sequence token

    This token represents a TeX escape sequence.  Doing str(...)
    on this token returns the name of the escape sequence without
    the escape character.

    """
    catcode = Token.CC_ESCAPE
    @property
    def source(self):
        if self == 'par':
            return '\n\n'
        # Handle active character format
        if '::' in self:
            return self.split('::').pop()
        return '\\%s ' % self
    @property
    def macroName(self):
        return self

    @property
    def nodeName(self):
        return self.macroName

    __slots__ = Token.TOKEN_SLOTS

class BeginGroup(Token):
    """ Beginning of a TeX group """
    catcode = Token.CC_BGROUP
    macroName = 'bgroup'
    __slots__ = Token.TOKEN_SLOTS

class EndGroup(Token):
    """ Ending of a TeX group """
    catcode = Token.CC_EGROUP
    macroName = 'egroup'
    __slots__ = Token.TOKEN_SLOTS

class MathShift(Token):
    catcode = Token.CC_MATHSHIFT
    macroName = 'active::$'
    __slots__ = Token.TOKEN_SLOTS

class Alignment(Token):
    catcode = Token.CC_ALIGNMENT
    macroName = 'active::&'
    __slots__ = Token.TOKEN_SLOTS

class Parameter(Token):
    catcode = Token.CC_PARAMETER
    __slots__ = Token.TOKEN_SLOTS

class Superscript(Token):
    catcode = Token.CC_SUPER
    macroName = 'active::^'
    __slots__ = Token.TOKEN_SLOTS

class Subscript(Token):
    catcode = Token.CC_SUB
    macroName = 'active::_'
    __slots__ = Token.TOKEN_SLOTS

class Space(Token):
    catcode = Token.CC_SPACE
    isElementContentWhitespace = True
    __slots__ = Token.TOKEN_SLOTS

class Letter(Token):
    catcode = Token.CC_LETTER
    __slots__ = Token.TOKEN_SLOTS

class Other(Token):
    catcode = Token.CC_OTHER
    __slots__ = Token.TOKEN_SLOTS

class Tokenizer(object):

    # Tokenizer states
    STATE_S = 1
    STATE_M = 2
    STATE_N = 4

    tokenClasses = [None] * 16 # type: List[Optional[Callable]]
    tokenClasses[Token.CC_BGROUP] = BeginGroup
    tokenClasses[Token.CC_EGROUP] = EndGroup
    tokenClasses[Token.CC_MATHSHIFT] = MathShift
    tokenClasses[Token.CC_ALIGNMENT] = Alignment
    tokenClasses[Token.CC_PARAMETER] = Parameter
    tokenClasses[Token.CC_SUPER] = Superscript
    tokenClasses[Token.CC_SUB] = Subscript
    tokenClasses[Token.CC_LETTER] = Letter
    tokenClasses[Token.CC_OTHER] = Other

    def __init__(self, source, context):
        """
        Instantiate a tokenizer

        Required Arguments:
        source -- the source to tokenize.  This can be a string containing
            TeX source, a file object that contains TeX source, or a
            list of tokens
        context -- the document's context object

        """
        self.context = context
        self.state = Tokenizer.STATE_N
        self._charBuffer = []
        self._tokBuffer = []
        if isinstance(source, str):
            source = StringIO(source)
            self.filename = '<string>'
        elif isinstance(source, bytes):
            source = TextIOWrapper(BytesIO(source), encoding='utf-8')
            self.filename = '<string>'
        elif isinstance(source, (tuple,list)):
            self.pushTokens(source)
            source = StringIO('')
            self.filename = '<tokens>'
        else:
            self.filename = source.name
        self.source = source
        self.seek = source.seek
        self.read = source.read
        self.readline = source.readline
        self.tell = source.tell
        self.lineNumber = 1

# There seems to be a problem with readline in Python 2.4 !!!
    def readline(self):
        read = self.read
        mybuffer = self._charBuffer
        while 1:
            if mybuffer:
                char = mybuffer.pop(0)
            else:
                char = read(1)
            if not char or ord(char) == 10:
                break

    def iterchars(self) -> Generator[Tuple[CatCode, str], None, None]:
        """
        Get the next character in the stream and its category code

        This function handles automatically converts characters like
        ^^M, ^^@, etc. into the correct character.  It also bypasses
        ignored and invalid characters.

        If you are iterating through the characters in a TeX instance
        and you go too far, you can put the character back with
        the pushChar() method.

        """
        # Create locals before going into the generator loop
        mybuffer = self._charBuffer
        read = self.read

        whichCode = self.context.whichCode
        CC_SUPER = Token.CC_SUPER
        CC_IGNORED = Token.CC_IGNORED
        CC_INVALID = Token.CC_INVALID

        def _read1():
            if mybuffer:
                return mybuffer.pop(0)
            return read(1)

        while True:
            token = _read1()

            if not token:
                break

            if token == '\n':
                self.lineNumber += 1

            code = whichCode(token)

            if code == CC_SUPER:

                # Handle characters like ^^M, ^^@, etc.
                next_char = _read1()

                if next_char != token:
                    self.pushChar(next_char)
                else:
                    next_char = _read1()
                    num = ord(next_char)
                    if num >= 64:
                        token = chr(num-64)
                    else:
                        token = chr(num+64)
                    code = whichCode(token)

            # Just go to the next character if you see one of these...
            if code in (CC_IGNORED, CC_INVALID):
                continue

            yield (code, token)

    def pushChar(self, char: str):
        """
        Push a character back into the stream to be re-read

        Required Arguments:
        char -- the character to push back

        """
        self._charBuffer.insert(0, char)
        if char == '\n':
            self.lineNumber -= 1

    def pushToken(self, token):
        """
        Push a token back into the stream to be re-read

        Required Arguments:
        token -- token to be pushed back

        """
        if token is not None:
            self._tokBuffer.insert(0, token)

    def pushTokens(self, tokens):
        """
        Push a list of tokens back into the stream to be re-read

        Required Arguments:
        tokens -- list of tokens to push back

        """
        if tokens:
            tokens = list(tokens)
            tokens.reverse()
            for t in tokens:
                self.pushToken(t)

    def __iter__(self):
        """
        Iterate over tokens in the input stream

        Returns:
        generator that iterates through tokens in the stream

        """
        # Cache variables to prevent globol lookups during generator
        global Space, EscapeSequence
        Space = Space
        EscapeSequence = EscapeSequence
        tokenClasses = self.tokenClasses
        mybuffer = self._tokBuffer
        charIter = self.iterchars()
        context = self.context
        pushChar = self.pushChar
        STATE_N = self.STATE_N
        STATE_M = self.STATE_M
        STATE_S = self.STATE_S
        ELEMENT_NODE = Node.ELEMENT_NODE
        CC_LETTER = Token.CC_LETTER
        CC_OTHER = Token.CC_OTHER
        CC_SPACE = Token.CC_SPACE
        CC_EOL = Token.CC_EOL
        CC_ESCAPE = Token.CC_ESCAPE
        CC_EOL = Token.CC_EOL
        CC_COMMENT = Token.CC_COMMENT
        CC_ACTIVE = Token.CC_ACTIVE
        prev = None

        while 1:

            # Purge mybuffer first
            while mybuffer:
                yield mybuffer.pop(0)

            # Get the next character
            try:
                (code, char) = next(charIter)
            except StopIteration:
                return

            # Short circuit letters and other since they are so common
            if code in (CC_LETTER, CC_OTHER):
                self.state = STATE_M
                token = tokenClasses[code](char)

            # Whitespace
            elif code == CC_SPACE:
                if self.state  == STATE_S or self.state == STATE_N:
                    continue
                self.state = STATE_S
                token = Space(' ')

            # End of line
            elif code == CC_EOL:
                state = self.state
                if state == STATE_S:
                    self.state = STATE_N
                    continue
                elif state == STATE_M:
                    token = Space(' ')
                    code = CC_SPACE
                    self.state = STATE_N
                elif state == STATE_N:
                    # ord(token) != 10 is the same as saying token != '\n'
                    # but it is much faster.
                    if ord(char) != 10:
                        self.lineNumber += 1
                        self.readline()
                    token = EscapeSequence('par')
                    # Prevent adjacent paragraphs
                    if prev == token:
                        continue
                    code = CC_ESCAPE

            # Escape sequence
            elif code == CC_ESCAPE:

                # Get name of command sequence
                self.state = STATE_M

                for (next_code, next_char) in charIter:

                    if next_code == CC_LETTER:
                        word = [next_char]
                        for (next_code_, next_char_) in charIter:
                            if next_code_ == CC_LETTER:
                                word.append(next_char_)
                            else:
                                pushChar(next_char_)
                                break
                        token = EscapeSequence(''.join(word))

                    elif next_code == CC_EOL:
                        #pushChar(token)
                        #token = EscapeSequence()
                        token = Space(' ')
                        self.state = STATE_S

                    else:
                        token = EscapeSequence(next_char)
#
# Because we can implement macros both in LaTeX and Python, we don't
# always want the whitespace to be eaten.  For example, implementing
# \chardef\%=`% would be \char{`%} in TeX, but in Python it's just
# another macro class that would eat whitspace incorrectly.  So we
# have to do this kind of thing in the parse() method of Macro.
#
                    if next_code != CC_EOL:
# HACK: I couldn't get the parse() thing to work so I'm just not
#       going to parse whitespace after EscapeSequences that end in
#       non-letter characters as a half-assed solution.
                        if token[-1] in encoding.stringletters():
                            # Absorb following whitespace
                            self.state = STATE_S

                    break

                else: token = EscapeSequence()

                # Check for any \let aliases
                token = context.get_let(token)

                # TODO: This action should be generalized so that the
                #       tokens are processed recursively
                if token is not token and token.catcode == CC_COMMENT:
                    self.readline()
                    self.lineNumber += 1
                    self.state = STATE_N
                    continue

            elif code == CC_COMMENT:
                self.readline()
                self.lineNumber += 1
                self.state = STATE_N
                continue

            elif code == CC_ACTIVE:
                token = EscapeSequence('active::%s' % char)
                token = context.get_let(token)
                self.state = STATE_M

            else:
                token = tokenClasses[code](char)
                self.state = STATE_M

            prev = token

            yield token
