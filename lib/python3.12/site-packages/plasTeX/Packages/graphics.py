import os
from plasTeX import Command

class includegraphics(Command):
    args = '* [ ll ] [ ur ] file:str'
    packageName = 'graphics'
    captionable = True
    
    def invoke(self, tex):
        res = Command.invoke(self, tex)

        f = self.attributes['file']

        ext = self.ownerDocument.userdata.getPath(
                      'packages/%s/extensions' % self.packageName, 
                      ['.png','.jpg','.jpeg','.gif','.pdf','.ps','.eps'])
        paths = self.ownerDocument.userdata.getPath(
                        'packages/%s/paths' % self.packageName, ['.'])
        img = None

        # Check for file using graphicspath
        for p in paths:
            for e in ['']+ext:
                fname = os.path.join(p,f+e)
                if os.path.isfile(fname):
                    img = os.path.abspath(fname)
                    break
            if img is not None:
                break

        # Check for file using kpsewhich
        if img is None:
            for e in ['']+ext:
                try: 
                    img = os.path.abspath(tex.kpsewhich(f+e))
                    break
                except (OSError, IOError): 
                    pass 

        self.imageoverride = img
        return res

class graphicspath(Command):
    args = 'paths'
    packageName = 'graphics'
    def invoke(self, tex):
        res = Command.invoke(self, tex)
        output = [x.textContent.strip() for x in self.attributes['paths']]
        output = [x for x in output if x]
        self.ownerDocument.userdata.setPath(
                'packages/%s/paths' % self.packageName, output)
        return res

class DeclareGraphicsExtensions(Command):
    packageName = 'graphics'
    args = 'ext:list'
    def invoke(self, tex):
        res = Command.invoke(self, tex)
        ext = [x for x in self.attributes['ext'] if x]
        self.ownerDocument.userdata.setPath(
                'packages/%s/extensions' % self.packageName, ext)
        return res

class rotatebox(Command):
    args = 'angle:float self'

class scalebox(Command):
    args = 'hscale:float [ vscale:float ] self'

class reflectbox(Command):
    args = 'self'

class resizebox(Command):
    args = 'hlength:dimen vlength:dimen self'
