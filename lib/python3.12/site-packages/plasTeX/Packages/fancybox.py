"""
plasTeX package for fancy boxes

"""

from plasTeX import Command

class fbox(Command):
    args = 'self'

class shadowbox(fbox):
    pass

class doublebox(fbox):
    pass

class ovalbox(fbox):
    pass

class Ovalbox(ovalbox):
    pass
