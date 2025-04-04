"""
Implement the tikz package using the imager
"""
from plasTeX import VerbatimEnvironment
from plasTeX import Command

class tikzpicture(VerbatimEnvironment):
    pass

class usetikzlibrary(Command):
    args = "library"

class tikzset(Command):
    args = "library"
