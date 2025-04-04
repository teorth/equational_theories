"""
C.10.1 The tabbing Environment (p201)

"""

from plasTeX import Command, Environment, DimenCommand


class tabbing(Environment):
    blockType = True

    class SetTabStop(Command):
        macroName = '='

    class JumpTabStop(Command):
        macroName = '>'

    class EndRow(Command):
        macroName = '\\\\'
   
    class kill(Command):
        pass

    class IncrementTab(Command):
        macroName = '+'

    class DecrementTab(Command):
        macroName = '-'

    class JumpBackTabStop(Command):
        macroName = '<' 

    class LeftMargin(Command):
        macroName = "'"

    class RightMargin(Command):
        macroName = '`'

    class pushtabs(Command):
        pass

    class poptabs(Command):
        pass

    class a(Command):
        args = 'accent'


# Style Parameters

class tabbingsep(DimenCommand):
    value = DimenCommand.new(0)
