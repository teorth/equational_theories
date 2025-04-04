from plasTeX import Environment

class multicols(Environment):
    args = 'num:int [ text:nox ] [ width:dimen ]'

    def invoke(self, tex):
        super(multicols, self).invoke(tex)
        if self.macroMode == self.MODE_BEGIN:
            return self.attributes['text']
        return []
