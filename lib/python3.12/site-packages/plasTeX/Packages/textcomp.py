from plasTeX import Command
from plasTeX.Base.LaTeX import Accents

class textleftarrow(Command):
    str = '←'

class textrightarrow(Command):
    str = '→'

class textuparrow(Command):
    str = '↑'

class textdownarrow(Command):
    str = '↓'

class textlbrackdbl(Command):
    str = '〚'

class textrbrackdbl(Command):
    str = '〛'

class textbigcircle(Command):
    str = '◯'

class textohm(Command):
    str = 'Ω'

class textmu(Command):
    str = 'µ'

class textpm(Command):
    str = '±'

class textdagger(Command):
    str = '†'

class textdaggerdbl(Command):
    str = '‡'

class textbardbl(Command):
    str = '‖'

class textbrokenbar(Command):
    str = '¦'

class textdegree(Command):
    str = '°'

class textbullet(Command):
    str = '•'

class textsurd(Command):
    str = '√'

class textordmasculine(Command):
    str = 'º'

class textordfeminine(Command):
    str = 'ª'

class textnumero(Command):
    str = '№'

class textcent(Command):
    str = '¢'

class textonequarter(Command):
    str = '\u00BC'

class textonehalf(Command):
    str = '\u00BD'

class textthreequarters(Command):
    str = '\u00BE'

class textzerooldstyle(Command):
    str = '0'

class textoneoldstyle(Command):
    str = '1'

class texttwooldstyle(Command):
    str = '2'

class textthreeoldstyle(Command):
    str = '3'

class textfouroldstyle(Command):
    str = '4'

class textfiveoldstyle(Command):
    str = '5'

class textsixoldstyle(Command):
    str = '6'

class textsevenoldstyle(Command):
    str = '7'

class texteightoldstyle(Command):
    str = '8'

class textnineoldstyle(Command):
    str = '9'

class textflorin(Command):
    str = '\u0192'

class textyen(Command):
    str = '\u00a5'

class textwon(Command):
    str = '\u20a9'

class textnaira(Command):
    str = '\u20a6'

class textpeso(Command):
    str = '\u20b1'

class textborn(Command):
    str = '\u2605'

class textdied(Command):
    str = '\u2020'

class textmarried(Command):
    str = '\u26ad'

class textdivorced(Command):
    str = '\u26ae'

class textcelsius(Command):
    str = '\u00b0C'

class textopenbullet(Command):
    str = '\u25e6'

class textdollaroldstyle(Command):
    str = '$'

class textsterling(Command):
    str = '\u00a3'

class textlira(Command):
    str = '\u20a4'

class textguarani(Command):
    str = '\u20b2'

class texteuro(Command):
    str = '\u20ac'

class textcentoldstyle(Command):
    str = '\u00a2'

class textestimated(Command):
    str = '\u212e'

class newtie(Accents.Accent):
    combining = '\u0311'

class capitaltie(Accents.t):
    macroName = None

class capitalacute(Accents.Acute):
    macroName = None

class capitaldieresis(Accents.Umlaut):
    macroName = None

class capitalbreve(Accents.Macron):
    macroName = None

class capitalnewtie(Accents.Accent):
    combining = '\u0311'

class capitalgrave(Accents.Grave):
    macroName = None

class capitaldotaccent(Accents.Dot):
    macroName = None

class capitalcedilla(Accents.c):
    macroName = None
