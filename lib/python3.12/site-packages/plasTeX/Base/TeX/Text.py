"""
B.5 Macros for text

"""

from plasTeX import Command, sourceChildren

class frenchspacing(Command):
    str = ''

class nonfrenchspacing(Command):
    str = ''

class normalbaselines(Command):
    str = ''

class lq(Command):
    str = chr(8216)

class rq(Command):
    str = chr(8217)

class lbrack(Command):
    str = '['

class rbrack(Command):
    str = ']'

class space(Command):
    str = ' '

class empty(Command):
    str = ''

class null(Command):
    str = ''

class bgroup(Command):

    def invoke(self, tex):
        self.ownerDocument.context.push()

    def digest(self, tokens):
        # Absorb the tokens that belong to us
        for item in tokens:
            if item.nodeType == Command.ELEMENT_NODE:
                if item.level < self.ENDSECTIONS_LEVEL:
                    tokens.push(item)
                    break
                if isinstance(item, (egroup,endgroup)):
                    self.endit = True
                    break
                if item.contextDepth < self.contextDepth:
                    tokens.push(item)
                    break
                item.parentNode = self
                item.digest(tokens)
            self.appendChild(item)
        self.paragraphs(force=False)

    @property
    def source(self):
        if self.hasChildNodes():
            return '{%s}' % sourceChildren(self)
        elif hasattr(self, 'endit'):
            return '{}'
        return '{'

class begingroup(bgroup):
    pass

class egroup(Command):
    str = ''

    def invoke(self, tex):
        self.ownerDocument.context.pop()

    @property
    def source(self):
        return '}'

    def digest(self, tokens):
        return

class endgroup(egroup):
    str = ''

class obeyspaces(Command):
    str = ''

class loop(Command):
    args = 'var:Tok'
    str = ''

class iterate(Command):
    str = ''

class repeat(Command):
    str = ''

class enskip(Command):
    pass

class enspace(Command):
    pass

class quad(Command):
    pass

class qquad(Command):
    pass

class thinspace(Command):
    pass

class negthinspace(Command):
    pass

class hglue(Command):
    pass

class vglue(Command):
    pass

class topglue(Command):
    pass

class nointerlineskip(Command):
    pass

class offinterlineskip(Command):
    pass

class TeXBreak(Command):
    macroName = 'break'
    str = ''

class allowbreak(Command):
    str = ''

class ControlSpace(Command):
    macroName = 'active::~'

class slash(Command):
    pass

class filbreak(Command):
    pass

class goodbreak(Command):
    pass

class eject(Command):
    str = ''

class supereject(Command):
    str = ''

class removelastskip(Command):
    pass

class smallbreak(Command):
    pass

class medbreak(Command):
    pass

class bigbreak(Command):
    pass

class line(Command):
    pass

class leftline(Command):
    args = 'self'

class llap(Command):
    args = 'self'

class centerline(Command):
    args = 'self'

class underbar(Command):
    args = 'self'

class uppercase(Command):
    args = 'argument:str'

    def invoke(self, tex):
        Command.invoke(self, tex)
        self.attributes['argument'] = self.attributes['argument'].upper()

class hang(Command):
    pass

class textindent(Command):
    args = 'self'

class narrower(Command):
    pass

#
# Accents are done in the LaTeX package
#

class dots(Command):
    str = chr(8230)
