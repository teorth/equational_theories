"""
C.15 Font Selection (p225)

"""

from plasTeX import Command, Environment
from plasTeX.Base.TeX.Primitives import BoxCommand


#
# C.15.1 Changing the Type Style
# 

class TextDeclaration(Environment):
    pass

class mdseries(TextDeclaration): pass
class bfseries(TextDeclaration): pass
class rmfamily(TextDeclaration): pass
class sffamily(TextDeclaration): pass
class ttfamily(TextDeclaration): pass
class upshape(TextDeclaration): pass
class itshape(TextDeclaration): pass
class slshape(TextDeclaration): pass
class scshape(TextDeclaration): pass
class normalfont(TextDeclaration): pass


class TextCommand(BoxCommand):
    pass

class textmd(TextCommand): pass
class textbf(TextCommand): pass
class textrm(TextCommand): pass
class textsf(TextCommand): pass
class texttt(TextCommand): pass
class textup(TextCommand): pass
class textit(TextCommand): pass
class textsl(TextCommand): pass
class textsc(TextCommand): pass
class textnormal(TextCommand): pass
   

#
# C.15.2 Changing the Type Size
#

class TextSizeDeclaration(Environment):
    pass

class tiny(TextSizeDeclaration): pass
class scriptsize(TextSizeDeclaration): pass
class footnotesize(TextSizeDeclaration): pass
class small(TextSizeDeclaration): pass
class normalsize(TextSizeDeclaration): pass
class large(TextSizeDeclaration): pass
class Large(TextSizeDeclaration): pass
class LARGE(TextSizeDeclaration): pass
class huge(TextSizeDeclaration): pass
class Huge(TextSizeDeclaration): pass


#
# Special Symbols
#

class symbol(Command):
    args = 'num:int'
