"""
C.8.4 Numbering (p194)

"""

from plasTeX import Command


class newcounter(Command):
    args = 'name:str [ within ]'
    def invoke(self, tex):
        a = self.parse(tex)
        self.ownerDocument.context.newcounter(a['name'], a['within'])

class setcounter(Command):
    args = 'name:str value:int'
    def invoke(self, tex):
        a = self.parse(tex)
        self.ownerDocument.context.counters[a['name']].setcounter(a['value'])

class addtocounter(Command):
    args = 'name:str value:int'
    def invoke(self, tex):
        a = self.parse(tex)
        self.ownerDocument.context.counters[a['name']].addtocounter(a['value'])

class value(Command):
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].arabic)

class arabic(Command):
    """ Return arabic representation """
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].arabic)

class Roman(Command):
    """ Return uppercase roman representation """
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].Roman)

class roman(Roman):
    """ Return the lowercase roman representation """
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].roman)

class Alph(Command):
    """ Return the uppercase letter representation """
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].Alph)

class alph(Alph):
    """ Return the lowercase letter representation """
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].alph)

class fnsymbol(Command):
    """ Return the symbol representation """
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return tex.textTokens(self.ownerDocument.context.counters[a['name']].fnsymbol)

class stepcounter(Command):
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return self.ownerDocument.context.counters[a['name']].stepcounter()

class refstepcounter(Command):
    args = 'name:str'
    def invoke(self, tex):
        a = self.parse(tex)
        return self.ownerDocument.context.counters[a['name']].stepcounter()
