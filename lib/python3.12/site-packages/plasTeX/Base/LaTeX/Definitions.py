"""
C.8 Definitions, Numbering, and Programming

"""

from plasTeX import Command, Environment
from plasTeX.Logging import getLogger

deflog = getLogger('parse.definitions')

#
# C.8.1 Defining Commands
#

class newcommand(Command):
    """ \\newcommand """
    args = '* name:cs [ nargs:int ] [ opt:nox ] definition:nox'
    def invoke(self, tex):
        self.parse(tex)
        a = self.attributes
        args = (a['name'], a['nargs'], a['definition'])
        kwargs = {'opt':a['opt']}
        deflog.debug('command %s %s %s', *args)
        self.ownerDocument.context.newcommand(*args, **kwargs)

class renewcommand(newcommand):
    pass

class providecommand(newcommand):
    pass

class DeclareRobustCommand(newcommand):
    pass

class DeclareTextCommandDefault(newcommand):
    pass

#
# C.8.2 Defining Environments
#

class newenvironment(Command):
    """ \\newenvironment """
    args = '* name:str [ nargs:int ] [ opt:nox ] begin:nox end:nox'
    def invoke(self, tex):
        self.parse(tex)
        a = self.attributes
        args = (a['name'], a['nargs'], a['begin'], a['end'])
        kwargs = {'opt':a['opt']}
        deflog.debug('environment %s %s %s', *args)
        self.ownerDocument.context.newenvironment(*args, **kwargs)

class renewenvironment(newenvironment):
    pass


#
# C.8.3 Theorem-like Environments
#

class newtheorem(Command):
    args = '* name:str [ counter:str ] caption [ within:str ]'
    def invoke(self, tex):
        self.parse(tex)
        attrs = self.attributes
        name = attrs['name']
        counter = attrs['counter']
        caption = attrs['caption']
        within = attrs['within']
        if not counter and not attrs['*modifier*']:
            counter = name
            if within:
                self.ownerDocument.context.newcounter(counter,initial=0,resetby=within, format='${the%s}.${%s}' % (within, name))
            else:
                self.ownerDocument.context.newcounter(counter,initial=0)
        deflog.debug('newtheorem %s', name)

        # The nodeName key below ensure all theorem type will call the same
        # rendering method, the type of theorem being retained in the thmName
        # attribute
        if attrs['*modifier*']:
            newclass = type(str(name), (Environment,),
                    {'caption': caption, 'nodeName': 'thmenv', 'thmName': name,
                        'args': '[title]', 'forcePars': True, 'style': None})
        else:
            newclass = type(str(name), (Environment,),
                    {'caption': caption, 'nodeName': 'thmenv', 'thmName': name,
                        'counter': counter, 'args': '[title]', 'forcePars': True,
                        'style': None})
        self.ownerDocument.context.addGlobal(name, newclass)
