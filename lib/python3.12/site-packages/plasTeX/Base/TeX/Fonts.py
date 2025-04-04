"""
B.4 Font Information

"""

from plasTeX import Command, Environment

class magstephalf(Command):
    str = '1095 '

class magstep(Command):
    args = 'value:Number'

class Font(Environment):
    pass

class rm(Font):
    pass

class cal(Font):
    pass

class it(Font):
    pass

class sl(Font):
    pass

class bf(Font):
    pass

class sf(Font):
    pass

class tt(Font):
    pass

class sc(Font):
    pass

