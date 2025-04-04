"""
C.2 The Structure of the Document (p170)

"""

from plasTeX import Command, Environment
from plasTeX.Base.LaTeX.Sectioning import SectionUtils

class document(Environment, SectionUtils):
    level = Environment.DOCUMENT_LEVEL

    @property
    def title(self):
        return self.ownerDocument.userdata.get('title','')

    @title.setter
    def title(self, value):
        self.ownerDocument.userdata["title"] = value

    def invoke(self, tex):
        res = Environment.invoke(self, tex)

        # Set initial counter values
        for name, value in self.config["counters"]["counters"].items():
            self.ownerDocument.context.counters[name].setcounter(value-1)

        return res
 
    @property
    def index(self):
        idx = self.getElementsByTagName(['theindex','printindex'])
        if idx:
            return idx[0]
        return []

class AtEndDocument(Command):
    args = 'commands:nox'

class AtBeginDocument(Command):
    args = 'commands:nox'
