from plasTeX import VerbatimEnvironment, Command

def ProcessOptions(options, document):
    document.config['images']['scales'].setdefault('forest', 1.5)

class forest(VerbatimEnvironment):
    pass

class forestset(Command):
    args = "setting"

