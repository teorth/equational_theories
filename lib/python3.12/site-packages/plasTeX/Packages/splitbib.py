from plasTeX import Command, Environment

class category(Environment):
    args = '[ label ] title'

class SBentries(Command):
    args = ' entries:list '

class SBtitlestyle(Command):
    args = 'type:str'

class SBsubtitlestyle(Command):
    args = 'type:str'
