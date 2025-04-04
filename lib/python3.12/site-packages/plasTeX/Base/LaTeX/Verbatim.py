"""
C.6.4 Verbatim

"""

from plasTeX import VerbatimEnvironment, Command, sourceArguments, sourceChildren
from plasTeX.Base.TeX.Text import bgroup
from plasTeX.Tokenizer import Other

class verbatim(VerbatimEnvironment):
    pass

class endverbatim(verbatim):
    def invoke(self, tex):
        end = self.ownerDocument.createElement(self.nodeName[3:])
        end.parentNode = self.parentNode
        end.macroMode = Environment.MODE_END
        return [end]

class VerbatimStar(verbatim):
    macroName = 'verbatim*'

class EndVerbatimStar(endverbatim):
    macroName = 'endverbatim*'

class verb(Command):
    args = '*'

    def invoke(self, tex):
        """ Parse for matching delimiters """
        self.ownerDocument.context.push(self)
        self.parse(tex)
        self.ownerDocument.context.setVerbatimCatcodes()
        # See what the delimiter is
        for endpattern in tex:
            self.delimiter = endpattern
            if isinstance(endpattern, bgroup):
                self.delimiter = endpattern = Other('}')
            break
        tokens = [self, endpattern]
        # Parse until this delimiter is seen again
        for tok in tex:
            tokens.append(tok)
            if tok == endpattern:
                break
        self.ownerDocument.context.pop(self)
        return tokens

    def digest(self, tokens):
        endpattern = next(iter(tokens))
        for tok in tokens:
            if tok == endpattern:
                break
            self.appendChild(tok)

    @property
    def source(self):
        return '\\%s%s%s%s%s' % (self.nodeName, sourceArguments(self),
                                 self.delimiter, sourceChildren(self),
                                 self.delimiter)

    def normalize(self, charsubs=None):
        """ Normalize, but don't allow character substitutions """
        return Command.normalize(self)
