from plasTeX import Command
from plasTeX.Packages.tikz import tikzpicture, usetikzlibrary,  tikzset

class pgfplotsset(Command):
    args = "vars"
