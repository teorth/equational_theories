from plasTeX import Command
from plasTeX.Base.LaTeX.Floats import Float, Caption

class newfloat(Command):
    args = 'name:str pos:str capfile:str [ reset:str ]'
    def invoke(self, tex):
        Command.invoke(self, tex)
        name = str(self.attributes['name'])

        # Create the float class and the caption class
        floatcls = type(name, (Float,), {})
        captioncls = type('caption', (Caption,),
                                  {'macroName':'caption', 'counter':name})
        floatcls.caption = captioncls
        c = self.ownerDocument.context
        c.addGlobal(name, floatcls)

        # Create a counter
        resetby = self.attributes['reset'] or 'chapter'
        c.newcounter(name, resetby, 0, format='${the%s}.${%s}' % (resetby,name))

        # Create the float name macro
        c.newcommand(name+'name', 0, name)


class floatstyle(Command):
    args = 'style:str'

class restylefloat(Command):
    args = 'float:str'

class floatname(Command):
    args = 'float:str name:str'
    def invoke(self, tex):
        Command.invoke(self, tex)
        float = str(self.attributes['float'])
        name = self.attributes['name']
        c = self.ownerDocument.context
        c.newcommand(float+'name', 0, name)

class floatplacement(Command):
    args = 'float:str pos:str'

class listof(Command):
    args = 'float:str title'
