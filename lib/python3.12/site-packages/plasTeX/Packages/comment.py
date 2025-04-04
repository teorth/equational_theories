from plasTeX.Base.LaTeX.Verbatim import verbatim

class comment(verbatim):

    def invoke(self, tex):
        verbatim.invoke(self, tex)
        return []
