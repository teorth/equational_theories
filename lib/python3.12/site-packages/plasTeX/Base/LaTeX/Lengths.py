"""
C.13.1 Length (p215)

"""

from plasTeX import Command, DimenCommand


class fill(DimenCommand):
    value = DimenCommand.new('1fill')

class stretch(Command):
    args = 'num:dimen'

class newlength(Command):
    args = 'name:cs'
    def invoke(self, tex):
        self.ownerDocument.context.newdimen(self.parse(tex)['name'])

class setlength(Command):
    args = 'name:cs len:nox'
#   def invoke(self, tex):
#       a = self.parse(tex)
#       ownerDocument.createElement(a['name']).setlength(a['len'])

class addtolength(Command):
    args = 'name:cs len:nox'
#   def invoke(self, tex):
#       a = self.parse(tex)
#       self.ownerDocument.createElement(a['name']).addtolength(a['len'])

class settowidth(Command):
    args = 'name:cs text:nox'
    
class settoheight(Command):
    args = 'name:cs text:nox'

class settodepth(Command):
    args = 'name:cs text:nox'
    

