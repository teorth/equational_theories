from plasTeX import Command, Environment

def ProcessOptions(options, document):
    colors = {}
    document.userdata.setPath('packages/color/colors', colors)
    colors['red'] = latex2htmlcolor('1,0,0')
    colors['green'] = latex2htmlcolor('0,1,0')
    colors['blue'] = latex2htmlcolor('0,0,1')
    
    colors['cyan'] = latex2htmlcolor('0,1,1')
    colors['magenta'] = latex2htmlcolor('1,0,1')
    colors['yellow'] = latex2htmlcolor('1,1,0')
    
    colors['white'] = latex2htmlcolor('1')
    colors['black'] = latex2htmlcolor('0')
    colors['gray'] = latex2htmlcolor('0.9')
    
    colors['darkred'] = latex2htmlcolor('0.8,0,0')
    colors['middlered'] = latex2htmlcolor('0.9,0,0')
    colors['lightred'] = latex2htmlcolor('1,0,0')
    
    colors['darkgreen'] = latex2htmlcolor('0,0.6,0')
    colors['middlegreen'] = latex2htmlcolor('0,0.8,0')
    colors['lightgreen'] = latex2htmlcolor('0,1,0')
    
    colors['darkblue'] = latex2htmlcolor('0,0,0.8')
    colors['middleblue'] = latex2htmlcolor('0,0,0.9')
    colors['lightblue'] = latex2htmlcolor('0,0,1')
    
    colors['darkcyan'] = latex2htmlcolor('0.6,0.8,0.8')
    colors['middlecyan'] = latex2htmlcolor('0,0.8,0.8')
    
    colors['darkmagenta'] = latex2htmlcolor('0.8,0.6,0.8')
    colors['middlemagenta'] = latex2htmlcolor('1,0,0.6')
    
    colors['darkyellow'] = latex2htmlcolor('0.8,0.8,0.6')
    colors['middleyellow'] = latex2htmlcolor('1,1,0.2')
    
    colors['darkgray'] = latex2htmlcolor('0.5')
    colors['middlegray'] = latex2htmlcolor('0.7')
    colors['lightgray'] = latex2htmlcolor('0.9')

def latex2htmlcolor(arg, model='rgb', named=None):
    named = named or {}
    if model == 'named':
        return named.get(arg, '')
    if ',' in arg:
        parts = [float(x) for x in arg.split(',')]
        # rgb
        if len(parts) == 3:
            red, green, blue = parts
            red = min(int(red * 255), 255)
            green = min(int(green * 255), 255)
            blue = min(int(blue * 255), 255)
        # cmyk
        elif len(parts) == 4:
            c, m, y, k = parts
            red, green, blue = [int(255*x) for x in [1-c*(1-k)-k, 1-m*(1-k)-k, 1-y*(1-k)-k]]
        else:
            return arg.strip()
    else:
        try: 
            red = green = blue = min(int(float(arg) * 255), 255)
        except ValueError:
            try:
                return named[arg]
            except KeyError:
                return arg.strip()
    return '#%.2X%.2X%.2X' % (red, green, blue)

class definecolor(Command):
    args = 'name:str model:str color:str'
    def invoke(self, tex):
        a = self.parse(tex)
        u = self.ownerDocument.userdata
        colors = u.getPath('packages/color/colors')
        colors[a['name']] = latex2htmlcolor(a['color'], a['model'], colors)

class textcolor(Command):
    args = '[ model:str ] color:str self'
    def invoke(self, tex):
        a = self.parse(tex)
        self.style['color'] = latex2htmlcolor(a['color'], a['model'], 
                  self.ownerDocument.userdata.getPath('packages/color/colors'))

class color(Environment):
    args = '[ model:str ] color:str'
    def invoke(self, tex):
        a = self.parse(tex)
        self.style['color'] = latex2htmlcolor(a['color'], a['model'], 
                  self.ownerDocument.userdata.getPath('packages/color/colors'))

class pagecolor(Command):
    args = '[ model:str ] color:str'

class colorbox(Command):
    args = '[ model:str ] color:str self'
    def invoke(self, tex):
        a = self.parse(tex)
        self.style['background-color'] = latex2htmlcolor(a['color'], 
     a['model'], self.ownerDocument.userdata.getPath('packages/color/colors'))

class fcolorbox(Command):
    args = '[ model:str ] bordercolor:str color:str self'
    def invoke(self, tex):
        a = self.parse(tex)
        self.style['background-color'] = latex2htmlcolor(a['color'], 
     a['model'], self.ownerDocument.userdata.getPath('packages/color/colors'))
        self.style['border'] = '1px solid %s' % latex2htmlcolor(
                                          a['bordercolor'], a['model'], 
           self.ownerDocument.userdata.getPath('packages/color/colors'))

class normalcolor(Command):
    pass
