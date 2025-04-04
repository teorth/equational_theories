"""
B.2 Allocation of Registers (p346)

"""

from plasTeX import Command
from plasTeX import DimenCommand, GlueCommand


class dimen_(Command):
    macroName = 'dimen'

class toks(Command):
    pass

class skip(Command):
    pass

class box(Command):
    pass

class TeXCount(Command):
    macroName = 'count'

class newcount(Command):
    args = 'arg:cs'
    def invoke(self, tex):
        self.ownerDocument.context.newcount(self.parse(tex)['arg'])

class newdimen(Command):
    args = 'arg:cs'
    def invoke(self, tex):
        self.ownerDocument.context.newdimen(self.parse(tex)['arg'])

class newskip(Command):
    args = 'arg:cs'
    def invoke(self, tex):
        self.ownerDocument.context.newskip(self.parse(tex)['arg'])

class newmuskip(Command):
    args = 'arg:cs'
    def invoke(self, tex):
        self.ownerDocument.context.newmuskip(self.parse(tex)['arg'])

class newbox(Command):
    args = 'name:cs'

class newtoks(Command):
    args = 'name:cs'

class newhelp(Command):
    args = 'name:cs value'

class newread(Command):
    args = 'name:cs'

class newwrite(Command):
    args = 'name:cs'

class newfam(Command):
    args = 'name:cs'

class newlanguage(Command):
    args = 'name:cs'

class maxdimen(DimenCommand):
    value = DimenCommand.new('16383.99pt')

class hideskip(GlueCommand):
    value = GlueCommand.new('-1000pt plus 1fill')

#class centering(GlueCommand):
#    value = GlueCommand.new('0pt plus 1000pt minus 1000pt')

class newif(Command):
    args = 'name:cs'
    def invoke(self, tex):
        self.ownerDocument.context.newif(self.parse(tex)['name'])

