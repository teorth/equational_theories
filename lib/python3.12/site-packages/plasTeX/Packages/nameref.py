"""
Implementation of the nameref package

"""

from plasTeX import Command

class nameref(Command):
    args = 'label:idref'
    
class Nameref(Command):
    args = 'label:idref'