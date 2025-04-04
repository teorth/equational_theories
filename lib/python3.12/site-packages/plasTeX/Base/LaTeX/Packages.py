"""
C.5 Classes, Packages, and Page Styles (p176)

"""
from plasTeX import Command, Environment, DimenCommand, Token
from plasTeX.Logging import getLogger

log = getLogger()

class PackageLoader(Command):
    extension = '.sty'
    def load(self, tex, file, options=None):
        try:
            self.ownerDocument.context.loadPackage(
                    tex, file+self.extension, options or {})
        except Exception as exc:
            log.error('Loading package "%s" raised exception %s : %s' % (
                file, type(exc).__name__, exc))

#
# C.5.1 Document Class
#

class documentclass(PackageLoader):
    args = '[ options:dict ] name:str'
    extension = '.cls'
    def invoke(self, tex):
        a = self.parse(tex)
        at_catcode = self.ownerDocument.context.whichCode('@')
        self.ownerDocument.context.catcode('@', Token.CC_LETTER)
        self.load(tex, a['name'], a['options'])
        packages = self.ownerDocument.context.packages
        if a['name'] in list(packages.keys()):
            packages['documentclass'] = packages[a['name']]
        self.ownerDocument.context.catcode('@', at_catcode)

class documentstyle(documentclass):
    pass

#
# Style Parameters
#

class bibindent(DimenCommand):
    value = DimenCommand.new(0)

class columnsep(DimenCommand):
    value = DimenCommand.new(0)

class columnseprule(DimenCommand):
    value = DimenCommand.new(0)

#
# C.5.2 Packages
#

class usepackage(PackageLoader):
    args = '[ options:dict ] names:list:str'
    extension = '.sty'
    def invoke(self, tex):
        # Allow & in option names (this happens in natbib)
        catcode = self.ownerDocument.context.whichCode('&')
        self.ownerDocument.context.catcode('&', Token.CC_LETTER)
        a = self.parse(tex)
        self.ownerDocument.context.catcode('&', catcode)
        at_catcode = self.ownerDocument.context.whichCode('@')
        self.ownerDocument.context.catcode('@', Token.CC_LETTER)
        for fname in a['names']:
            self.load(tex, fname, a['options'])
        self.ownerDocument.context.catcode('@', at_catcode)

class RequirePackage(usepackage):
    pass

#
# C.5.3 Page Styles
#

class pagestyle(Command):
    args = 'style:str'

class thispagestyle(pagestyle):
    pass

class markright(Command):
    args = 'text'

class markboth(Command):
    args = 'left right'

class pagenumbering(Command):
    args = 'style:str'

class twocolumn(Command):
    args = '[ text ]'

class onecolumn(Command):
    pass

#
# Style Parameters
#

# Figure C.3: Page style parameters

class paperheight(DimenCommand):
    value = DimenCommand.new('11in')

class paperwidth(DimenCommand):
    value = DimenCommand.new('8.5in')

class oddsidemargin(DimenCommand):
    value = DimenCommand.new('1in')

class evensidemargin(DimenCommand):
    value = DimenCommand.new('1in')

class textheight(DimenCommand):
    value = DimenCommand.new('9in')

class textwidth(DimenCommand):
    value = DimenCommand.new('6.5in')

class topmargin(DimenCommand):
    value = DimenCommand.new(0)

class headheight(DimenCommand):
    value = DimenCommand.new('0.5in')

class headsep(DimenCommand):
    value = DimenCommand.new('0.25in')

class footskip(DimenCommand):
    value = DimenCommand.new('0.5in')

class marginparsep(DimenCommand):
    value = DimenCommand.new('0.25in')

class marginparwidth(DimenCommand):
    value = DimenCommand.new('0.75in')

#
# C.5.4 The Title Page and Abstract
#

class maketitle(Command):
    blockType = True

class title(Command):
    args = '[ toc ] self'
    def invoke(self, tex):
        Command.invoke(self, tex)
        if 'title' not in list(self.ownerDocument.userdata.keys()):
            self.ownerDocument.userdata['title'] = self

class author(Command):
    args = 'self'
    def invoke(self, tex):
        Command.invoke(self, tex)
        userdata = self.ownerDocument.userdata
        if userdata.get('author') is None:
            userdata['author'] = []
        userdata['author'].append(self)

class date(Command):
    args = 'self'
    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['date'] = self

class thanks(Command):
    args = 'self'
    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['thanks'] = self

class abstract(Environment):
    blockType = True

class titlepage(Environment):
    blockType = True


#
# Extras...
#
class ProvidesPackage(Command):
    args = 'name [ message ]'

class ProvidesClass(Command):
    pass

class DeclareOption(Command):
    args = 'name:str [ default:nox ] value:nox'

class PackageWarning(Command):
    args = 'name:str message:str'

class ProcessOptions(Command):
    args = '*'

class LoadClass(usepackage):
    args = '[ options:dict ] names:list:str'
    extension = '.cls'

class NeedsTeXFormat(Command):
    args = 'name:str date:str'

class InputIfFileExists(Command):
    args = 'file:str true:nox false:nox'
    def invoke(self, tex):
        a = self.parse(tex)
        try:
            tex.input(tex.kpsewhich(a['file']))
            tex.pushTokens(a['true'])
        except (IOError, OSError):
            tex.pushTokens(a['false'])
        return []

class IfFileExists(Command):
    args = 'file:str true:nox false:nox'
    def invoke(self, tex):
        a = self.parse(tex)
        try:
            tex.kpsewhich(a['file'])
            tex.pushTokens(a['true'])
        except (IOError, OSError):
            tex.pushTokens(a['false'])
        return []
