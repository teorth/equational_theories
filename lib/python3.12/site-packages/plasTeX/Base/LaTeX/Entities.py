"""
This package is dynamically generated.  It loads data from the ent.xml file.

"""

import re, Accents, Characters
from xml.parsers import expat
from plasTeX import Command


g = globals()

class EntityParser(object):
    """ Parser for XML entities """

    accentmap = {
        '\'': Accents.Acute,
        '^': Accents.Circumflex,
        '`': Accents.Grave,
        '~': Accents.Tilde,
        '"': Accents.Umlaut,
        'c': Accents.c,
        'v': Accents.v,
        'u': Accents.u,
        'k': Accents.k,
        '.': Accents.Dot,
        '=': Accents.Macron,
        'H': Accents.H,
        'r': Accents.r,
    }

    def __init__(self):
        self.parser = expat.ParserCreate()
        self.parser.StartElementHandler = self.start_element
        self.parser.CharacterDataHandler = self.char_data
        self.str = None
        self.inseq = False
        self.defined = {}

    def parse(self, file):
        self.parser.Parse(open(file).read())
        self.defined.clear()

    def start_element(self, name, attrs):
        if name == 'char':
            self.str = None
        elif name == 'str':
            self.str = int('0x%s' % attrs['value'], 16)
        elif name in ['seq','mathseq']:
            self.inseq = True
        else:
            self.inseq = False

    def char_data(self, data):
        if self.str is None:
            self.inseq = False
            return

        if not self.inseq:
            return

        # Just a macro
        m = re.match(r'^\\(\w+|\W)$', data)
        if m:
            name = str(m.group(1)).replace('\\','\\\\')
            if name not in self.defined:
                g[name+'_'] = type(name+'_', (Command,),
                                          {'str':chr(self.str),
                                           'macroName':name})
                self.defined[name] = True

        # Wingdings
        m = re.match(r'^\\ding\{(\d+)\}$', data)
        if m:
            int(m.group(1))
            Characters.ding.values[int(m.group(1))] = chr(self.str)

        # Accented characters
        m = re.match(r'^(\\(%s)\{([^\}])\})' %
                      '|'.join(list(self.accentmap.keys())), data)
        if m and m.group(1) not in self.defined:
            accent = self.accentmap[m.group(2)]
            accent.chars[m.group(3)] = chr(self.str)
            self.defined[m.group(1)] = True

        self.inseq = False


# Parse the entities file
#e = EntityParser()
#e.parse(os.path.join(os.path.dirname(__file__),'ent.xml'))
