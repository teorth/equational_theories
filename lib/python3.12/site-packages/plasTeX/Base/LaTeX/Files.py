"""
C.11.1 Files (p206)
C.11.4 Splitting the Input
C.11.6 Terminal Input and Output

"""

from plasTeX import Command, Environment
from plasTeX.Logging import getLogger

log = getLogger()

class nofiles(Command):
    pass

class includeonly(Command):
    args = 'files:list:str'

class filecontents(Environment):
    args = 'file:str'

class FileContentsStar(Environment):
    macroName = 'filecontents*'
    args = 'file:str'

class listfiles(Command):
    pass

class typeout(Command):
    args = 'message:str'
    def invoke(self, tex):
        log.info(self.parse(tex)['message'])

class typein(Command):
    args = '[ command:str ] message'
    def invoke(self, tex):
        log.info(self.parse(tex)['message'])
