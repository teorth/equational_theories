"""
C.3.3 Footnotes (p172)

"""

from plasTeX import Command, DimenCommand


class footnote(Command):
    args = '[ num:int ] self'
    mark = None

    def invoke(self, tex):
        # Add the footnote to the document
        output = Command.invoke(self, tex)
        userdata = self.ownerDocument.userdata
        if 'footnotes' not in userdata:
            userdata['footnotes'] = []
        userdata['footnotes'].append(self)
        self.mark = self
        return output

class footnotemark(Command):
    args = '[ num:int ]'
    mark = None

    def invoke(self, tex):
        # Add the footnotemarks to the document
        output = Command.invoke(self, tex)
        userdata = self.ownerDocument.userdata
        if 'footnotemarks' not in userdata:
            userdata['footnotemarks'] = []
        userdata['footnotemarks'].append(self)
        self.mark = self
        return output

class footnotetext(footnote):
    args = '[ num:int ] self'
    mark = None
    
    def invoke(self, tex):
        output = footnote.invoke(self, tex)
        self.mark = self.ownerDocument.userdata.get('footnotemarks',[None]).pop(0)
        return output

#
# Style Parameters
#

class footnotesep(DimenCommand):
    value = DimenCommand.new(0)

class footnoterule(Command):
    pass
