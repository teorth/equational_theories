"""
subfigure package

"""

from plasTeX import Command

def ProcessOptions(options, document):
    context = document.context
    context.newcounter('subfigure', resetby='figure', 
                       format='${thefigure}.${subfigure.alph}')
    context.newcounter('subtable', resetby='table', 
                       format='${thetable}.${subtable.alph}')

class subfigurename(Command):
    str = ''

class subtablename(Command):
    str = ''

class subfigure(Command):
    args = '[ title ] self'
    counter = 'subfigure'

class subtable(Command):
    args = '[ title ] self'
    counter = 'subtable'
