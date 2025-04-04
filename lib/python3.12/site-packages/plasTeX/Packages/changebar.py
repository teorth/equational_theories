from plasTeX import Command, Environment, DimenCommand, Counter

class cbstart(Command):
    def invoke(self, tex):
        cb = self.ownerDocument.createElement('changebar')
        cb.macroMode = self.MODE_BEGIN
        cb.invoke(tex)
        return [cb]

class cbend(Command):
    def invoke(self, tex):
        cb = self.ownerDocument.createElement('changebar')
        cb.macroMode = self.MODE_END
        cb.invoke(tex)
        return [cb]

class changebar(Environment):
    args = '[ width:str ]'
    blockType = True
    forcePars = True

class cbdelete(Command):
    args = '[ width:str ]'

class nochangebars(Command):
    pass

class cbcolor(Command):
    args = '[ model:str ] color:str'

class changebarwidth(DimenCommand):
    pass

class deletebarwidth(DimenCommand):
    pass

class changebarsep(DimenCommand):
    pass

class changebargrey(Counter):
    pass

class outerbarstrue(Command):
    pass

class driver(Command):
    args = 'name:str'
