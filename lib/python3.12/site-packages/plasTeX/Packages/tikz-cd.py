from plasTeX import VerbatimEnvironment, Command

def ProcessOptions(options, document):
    document.config['images']['scales'].setdefault('tikzcd', 1.5)

class tikzcd(VerbatimEnvironment):
    pass

class usetikzlibrary(Command):
    args = "library"

class tikzset(Command):
    args = "library"
