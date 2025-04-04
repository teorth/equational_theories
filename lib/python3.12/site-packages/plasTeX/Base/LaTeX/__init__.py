#from Entities import *

from plasTeX.Base.LaTeX.Accents import *
from plasTeX.Base.LaTeX.Alignment import *
from plasTeX.Base.LaTeX.Arrays import *
from plasTeX.Base.LaTeX.Bibliography import *
from plasTeX.Base.LaTeX.Boxes import *
from plasTeX.Base.LaTeX.Breaking import *
from plasTeX.Base.LaTeX.Characters import *
from plasTeX.Base.LaTeX.Crossref import *
from plasTeX.Base.LaTeX.Definitions import *
from plasTeX.Base.LaTeX.Document import *
from plasTeX.Base.LaTeX.Environments import *
from plasTeX.Base.LaTeX.FontSelection import *
from plasTeX.Base.LaTeX.Footnotes import *
from plasTeX.Base.LaTeX.Files import *
from plasTeX.Base.LaTeX.Floats import *
from plasTeX.Base.LaTeX.Index import *
from plasTeX.Base.LaTeX.Lengths import *
from plasTeX.Base.LaTeX.Lists import *
from plasTeX.Base.LaTeX.Math import *
from plasTeX.Base.LaTeX.Numbering import *
from plasTeX.Base.LaTeX.Packages import *
from plasTeX.Base.LaTeX.Pictures import *
from plasTeX.Base.LaTeX.Paragraphs import *
from plasTeX.Base.LaTeX.Quotations import *
from plasTeX.Base.LaTeX.Sectioning import *
from plasTeX.Base.LaTeX.Sentences import *
from plasTeX.Base.LaTeX.Space import *
from plasTeX.Base.LaTeX.Tabbing import *
from plasTeX.Base.LaTeX.Verbatim import *

from plasTeX import Command
from plasTeX.Tokenizer import Token

class ifundefined_(Command):
    macroName = '@ifundefined'
    args = 'name:str true:nox false:nox'
    def invoke(self, tex):
        a = self.parse(tex)
        if a['name'] in list(self.ownerDocument.context.keys()):
            tex.pushTokens(a['false'])
        else:
            tex.pushTokens(a['true'])
        return []

class vwritefile_(Command):
    macroName = '@vwritefile'
    args = 'file:nox content:nox'

class pagelabel(Command):
    args = 'label:nox content:nox'

class verbatiminput(Command):
    pass

class makeatother(Command):
    def invoke(self, tex):
        self.ownerDocument.context.catcode('@', Token.CC_OTHER)

class makeatletter(Command):
    def invoke(self, tex):
        self.ownerDocument.context.catcode('@', Token.CC_LETTER)
