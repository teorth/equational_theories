"""
C.12 Line and Page Breaking (p212)

"""

from plasTeX import Command


#
# C.12.1
#

class linebreak(Command):
    args = '[ num:int ]'

class nolinebreak(Command):
    args = '[ num:int ]'


class newline(Command):
    pass

class NewLine(newline):
    macroName = '\\'
    args = '* [ len:dimen ]'

class AllowHyphen(Command):
    macroName = '-'

class hyphenation(Command):
    args = 'words:str'

class sloppy(Command):
    pass

class fussy(Command):
    pass

class sloppypar(Command):
    pass

#
# C.12.2 Page Breaking
#

class pagebreak(Command):
    args = '[ num:int ]'

class nopagebreak(Command):
    args = '[ num:int ]'

class enlargethispage(Command):
    args = '* len:dimen'

class newpage(Command):
    pass

class clearpage(Command):
    pass

class cleardoublepage(Command):
    pass

