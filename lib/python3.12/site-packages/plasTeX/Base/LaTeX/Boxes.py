"""
C.13.3 Boxes (p217)

"""

from plasTeX.Base.TeX.Primitives import BoxCommand
from plasTeX import Command, Environment
from plasTeX import DimenCommand, GlueCommand


class TextBoxCommand(Command):

    class width(DimenCommand):
        value = DimenCommand.new(0)
 
    class height(DimenCommand):
        value = DimenCommand.new(0)

    class depth(DimenCommand):
        value = DimenCommand.new(0)

    class totalheight(DimenCommand):
        value = DimenCommand.new(0)


class mbox(BoxCommand):
    args = 'self'

class makebox(TextBoxCommand):
    args = '[ width:dimen ] [ pos:str ] self'

class fbox(Command):
    args = 'self'

class framebox(TextBoxCommand):
    args = '[ width:dimen ] [ pos:str ] self'

class newsavebox(Command):
    args = 'name:cs'

class sbox(Command):
    args = 'name:cs text'

class savebox(TextBoxCommand):
    args = 'name:cs [ width:dimen ] [ pos ] text'

class lrbox(Environment):
    args = 'name:cs'

class usebox(Command):
    args = 'name:cs'

class parbox(Command):
    args = '[ pos:str ] width:dimen self'

class minipage(Environment):
    args = '[ pos:str ] [ height:dimen ] [ innerpos:str ] width:dimen'

class rule(Command):
    args = '[ raise:dimen ] width:dimen height:dimen'

class raisebox(TextBoxCommand):
    args = 'raise:dimen [ height:dimen ] [ depth:dimen ] self'

# Style Parameters

class fboxrule(DimenCommand):
    value = DimenCommand.new(0)

class fboxsep(GlueCommand):
    value = GlueCommand.new(0)
