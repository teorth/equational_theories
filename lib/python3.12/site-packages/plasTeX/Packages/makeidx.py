from plasTeX import Command

class see(Command):
    args = 'self page:nox'
    counter = 'see'
    
class seealso(Command):
    args = 'self page:nox'
    counter = 'also'

# Dummy macros to accompany counters above
class thesee(Command):
    str = ''

class thealso(Command):
    str = ''