"""
This is a huge package!  Most of the commands are simply stubbed out
and not implemented yet.  Of course, many of the commands simply won't
need anything more since they either don't make sense for plasTeX or
the renderer will be doing all the work.

"""

from plasTeX import Command

def ProcessOptions(options, document):
    context = document.context
    context.newcounter('partlofdepth')
    context.newcounter('partlotdepth')
    context.newcounter('parttocdepth')
    context.newcounter('minilofdepth')
    context.newcounter('minilotdepth')
    context.newcounter('minitocdepth')
    context.newcounter('seclofdepth')
    context.newcounter('seclotdepth')
    context.newcounter('sectocdepth')
    context.newcounter('mtc')
    context.newcounter('ptc')
    context.newcounter('stc')

class dominitoc(Command):
    args = '[ pos:str ]'

class dominilof(dominitoc):
    pass

class dominilot(dominitoc):
    pass

class _minitoccommand(Command):
    args = '[ pos:str ]'
    titleMacro = ''

    def invoke(self, tex):
        Command.invoke(self, tex)
        self.title = self.ownerDocument.createElement(self.titleMacro).expand(tex)

    @property
    def tableofcontents(self):
        node = self.parentNode
        while node is not None and node.level > Command.ENDSECTIONS_LEVEL:
            node = node.parentNode
        if node is not None:
            return node.tableofcontents

class minitoc(_minitoccommand):
    titleMacro = 'mtctitle'

class minilof(_minitoccommand):
    titleMacro = 'mlftitle'

class minilot(_minitoccommand):
    titleMacro = 'mlttitle'

class dosecttoc(dominitoc):
    pass

class dosectlof(dominitoc):
    pass

class dosectlot(dominitoc):
    pass

class secttoc(minitoc):
    titleMacro = 'stctitle'

class sectlof(minilof):
    titleMacro = 'slftitle'

class sectlot(minilot):
    titleMacro = 'slttitle'

class doparttoc(dominitoc):
    pass

class dopartlof(dominilof):
    pass

class dopartlot(dominilot):
    pass

class parttoc(minitoc):
    titleMacro = 'ptctitle'

class partlof(minilof):
    titleMacro = 'plftitle'

class partlot(minilot):
    titleMacro = 'plttitle'

# 
# Formatting
#

class mtcsetfont(Command):
    args = 'which:str level:str format:nox'

class mtcsetdepth(Command):
    args = 'which:str depth:int'

class mtcprepare(Command):
    args = 'toc:str level:str commands'

class mtcskip(Command):
    pass

class mtcskipammount(Command):
    pass

class tightmtcfalse(Command):
    pass

class tightmtctrue(Command):
    pass

class ktightmtcfalse(Command):
    pass

class ktightmtctrue(Command):
    pass

class undottedmtcfalse(Command):
    pass

class undottedmtctrue(Command):
    pass

class addstarredpart(Command):
    args = 'title'

class addstarredchapter(Command):
    args = 'title'

class addstarredsection(Command):
    args = 'title'

class _adjust(Command):
    args = '[ num:int ]'
    default = 1
    counterName = ''
    def invoke(self, tex):
        Command.invoke(self, tex)
        n = self.attributes['num'] or self.default
        self.ownerDocument.context.counters[self.counterName].addtocounter(n)

class adjustptc(_adjust):
    counterName = 'ptc'

class adjustmtc(_adjust):
    counterName = 'mtc'

class adjuststc(_adjust):
    counterName = 'stc'

class _decrement(Command):
    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.context.counters[self.counterName].addtocounter(-1)

class decrementptc(_decrement):
    counterName = 'ptc'

class decrementmtc(_decrement):
    counterName = 'mtc'

class decrementstc(_decrement):
    counterName = 'stc'

class _increment(Command):
    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.context.counters[self.counterName].addtocounter(1)

class incrementptc(_increment):
    counterName = 'ptc'

class incrementmtc(_increment):
    counterName = 'mtc'

class incrementstc(_increment):
    counterName = 'stc'

class mtcaddpart(Command):
    args = '[ title ]'

class mtcaddchapter(Command):
    args = '[ title ]'

class mtcaddsection(Command):
    args = '[ title ]'

#
# Titles
#

class mtctitle(Command):
    str = 'Contents'

class mlftitle(Command):
    str = 'Figures'

class mlttitle(Command):
    str = 'Tables'

class ptctitle(Command):
    str = 'Table of Contents'

class plftitle(Command):
    str = 'List of Figures'

class plttitle(Command):
    str = 'List of Tables'

class stctitle(Command):
    str = 'Contents'

class slftitle(Command):
    str = 'Figures'

class slttitle(Command):
    str = 'Tables'

class mtcsettitle(Command):
    args = 'which:str title'

class mtcsettitlefont(Command):
    args = 'which:str commands:nox'

class mtcsetformat(Command):
    args = 'which:str param:str value:nox'

#
# Rules
#

class mtcsetrules(Command):
    args = 'which:str value'

class ptcrule(Command):
    pass

class noptcrule(Command):
    pass

class mtcrule(Command):
    pass

class nomtcrule(Command):
    pass

class stcrule(Command):
    pass

class nostcrule(Command):
    pass

class plfrule(Command):
    pass

class noplfrule(Command):
    pass

class mlfrule(Command):
    pass

class nomlfrule(Command):
    pass

class slfrule(Command):
    pass

class noslfrule(Command):
    pass

class pltrule(Command):
    pass

class nopltrule(Command):
    pass

class mltrule(Command):
    pass

class nomltrule(Command):
    pass

class sltrule(Command):
    pass

class nosltrule(Command):
    pass


# 
# Page Numbers
#

class mtcsetpagenumbers(Command):
    args = 'which:str value'

class ptcpagenumbers(Command):
    pass

class noptcpagenumbers(Command):
    pass

class plfpagenumbers(Command):
    pass

class noplfpagenumbers(Command):
    pass

class pltpagenumbers(Command):
    pass

class nopltpagenumbers(Command):
    pass

class mtcpagenumbers(Command):
    pass

class nomtcpagenumbers(Command):
    pass

class mlfpagenumbers(Command):
    pass

class nomlfpagenumbers(Command):
    pass

class mltpagenumbers(Command):
    pass

class nomltpagenumbers(Command):
    pass

class stcpagenumbers(Command):
    pass

class nostcpagenumbers(Command):
    pass

class slfpagenumbers(Command):
    pass

class noslfpagenumbers(Command):
    pass

class sltpagenumbers(Command):
    pass

class nosltpagenumbers(Command):
    pass


class mtcsetfeature(Command):
    args = 'which:str param:str commands:nox'

class firstpartis(Command):
    args = 'num:int'

class firstchapteris(Command):
    args = 'num:int'

class firstsectionis(Command):
    args = 'num:int'

class mtcfixglossary(Command):
    pass

class mtcfixindex(Command):
    pass

class faketableofcontents(Command):
    pass

class fakelistoffigures(Command):
    pass

class fakelistoftables(Command):
    pass

class mtcselectlanguage(Command):
    args = 'language:str'


