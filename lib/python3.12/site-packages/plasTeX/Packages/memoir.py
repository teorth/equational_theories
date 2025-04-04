from plasTeX.Packages.book import *

class checkandfixthelayout(Command): pass
class setlrmarginsandblock(Command): pass

class titleref(Command):
    args = 'label:idref'

class tightlist(Command):
    def invoke(self, tex):
        return []

class firmlist(Command):
    def invoke(self, tex):
        return []
