"""
C.3.2 Making Paragraphs (p171)

"""

from plasTeX import Command, DimenCommand


class noindent(Command):
    pass

class indent(Command):
    pass

# Defined in TeX
#class par(Command):
#    pass

#
# Style Parameters
#

class columnwidth(DimenCommand):
    value = DimenCommand.new('6.5in')

class linewidth(DimenCommand):
    value = DimenCommand.new('6.5in')

class baselinestretch(Command):
    str = '1'
