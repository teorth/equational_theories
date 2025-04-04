from plasTeX import Command

class DefineKey(Command):
    macroName = 'define@key'
    args = 'group:str name:str [ default:nox ] definition:nox'

class ProcessOptionsWithKV(Command):
    args = 'group:str'
