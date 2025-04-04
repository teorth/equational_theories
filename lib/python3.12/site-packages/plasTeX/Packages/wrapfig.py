from plasTeX import Environment
from plasTeX.Base.LaTeX.Floats import Caption

class wrapfigure(Environment):
    args = '[ lines ] place:str [ overhang ] width'
    float = 'left'
    def invoke(self, tex):
        res = Environment.invoke(self, tex)
        if self.macroMode == self.MODE_BEGIN:
            a = self.attributes['place'].lower()
            if a in ['r','o']:
                self.float = 'right'
        return res
    
    class caption(Caption):
        counter = 'figure'

class wraptable(wrapfigure):
    pass