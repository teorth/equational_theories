import re
from plasTeX.Renderers.PageTemplate import Renderer as _Renderer
from plasTeX.Renderers.PageTemplate import xmltemplate
from plasTeX import Command
try:
    from lxml import etree
except ImportError:
    have_lxml = False
else:
    have_lxml = True
xns = {'d': 'http://docbook.org/ns/docbook'}

def drop_tag(elem):
    """
    Remove the tag, but not its children or text.
    The children and text are merged into the parent.
    """
    parent = elem.getparent()
    previous = elem.getprevious()
    if elem.text and isinstance(elem.tag, str):
        if previous is None:
            parent.text = (parent.text or '') + elem.text
        else:
            previous.tail = (previous.tail or '') + elem.text
    if elem.tail:
        if elem:
            last = elem[-1]
            last.tail = (last.tail or '') + elem.tail
        elif previous is None:
            parent.text = (parent.text or '') + elem.tail
        else:
            previous.tail = (previous.tail or '') + elem.tail
    index = parent.index(elem)
    parent[index:index + 1] = elem[:]

def clean_para(tree, name):
    for elem in tree.findall('.//d:%s' % name, namespaces=xns):
        e = elem.findall('d:para', namespaces=xns)
        if e:
            for tag in e:
                drop_tag(tag)
    return tree

def get_see(term):
    see = None
    seealso = None
    if term.find('|') != -1:
        term, fmt = term.split('|')
        if fmt.find('seealso') != -1:
            seealso = fmt
        elif fmt.find('see') != -1:
            see = fmt

    return term, see, seealso

def parse_indexentry(s):
    term = s
    sortstr = None
    if term.find('@') != -1:
        term, sortstr = term.split('@')
    term, see, seealso = get_see(term)
    return (term, sortstr, see, seealso)

class index(Command):
    args = 'argument:str'

    def invoke(self, tex):
        Command.invoke(self, tex)
        entry = self.attributes['argument']
        if entry.find('!') != -1:
            primary, secondary = entry.split('!')

            primary, prisort, see, seealso= parse_indexentry(primary)
            if see or seealso:
                secondary, secsort, _, _ = parse_indexentry(secondary)
            else:
                secondary, secsort, see, seealso = parse_indexentry(secondary)
        else:
            primary, prisort, see, seealso = parse_indexentry(entry)

        self.data = {
            'primary': primary,
            'secondary':secondary,
            'prisort': prisort,
            'secsort': secsort,
            'see': see,
            'seealso': seealso,
            }

class DocBook(_Renderer):
    """ Renderer for DocBook documents """
    fileExtension = '.xml'
    imageTypes = ['.png','.jpg','.jpeg','.gif']
    vectorImageTypes = ['.svg']

    def __init__(self, *args, **kwargs):
        _Renderer.__init__(self, *args, **kwargs)
        self.registerEngine('xml', None, '.xml', xmltemplate)

    def cleanup(self, document, files, postProcess=None):
        res = _Renderer.cleanup(self, document, files, postProcess=postProcess)
        return res

    def processFileContent(self, document, s):
        s = _Renderer.processFileContent(self, document, s)

        if have_lxml:
            tree = etree.fromstring(s)
            for name in ['itemizedlist', 'table', 'term', 'para']:
                tree = clean_para(tree, name)
            s = etree.tostring(tree, encoding='unicode')
        else:
            s = re.sub(r'</partintro>\s*<partintro>','', s, flags=re.I)
            s = re.sub(r'<para>\s*(<articleinfo>)', r'\1', s, flags=re.I)
            s = re.sub(r'(</articleinfo>)\s*</para>', r'\1', s, flags=re.I)
            s = re.sub(r'<para>\s*</para>', '', s, flags=re.I)

            for name in ['itemizedlist', 'term', 'para']:
                s = re.sub(r'(<%s>)\s*<para>' % name, r'\1', s, flags=re.I)
                s = re.sub(r'</para>\s*(</%s>)' % name, r'\1', s, flags=re.I)

        return s

Renderer = DocBook
