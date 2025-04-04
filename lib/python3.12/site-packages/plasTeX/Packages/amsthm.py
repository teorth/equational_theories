r"""

plasTeX.Package.amsthm.py: Partial support for `amsthm.sty` LaTeX Package.

This python package provides support for

* Command: `\newtheorem`
* Command: `swapnumbers`
* Command: `\newtheoremstyle`
* Command: `\theoremstyle`
* Environment: `proof`

It supports the starred version (without numbers) of `\newtheorem`.
The `header spec` argument of `\newtheoremstyle` is not supported.

This package keeps a list of user defined styles in the `userdata` space under
`packages/amsthm/styles`. This userdata is prepopulated with (a simplified
version of) the  default styles in amsthm.sty: plain, remark, and definition.

It also keeps a list of theorem-like environments under
`packages/amsthm/theorems`.
"""
from pathlib import Path

from plasTeX import Environment, Command, dimen, TeXFragment
from plasTeX.Base.LaTeX.FontSelection import itshape, bfseries
from plasTeX.PackageResource import PackagePreCleanupCB, PackageCss

def fontweight(tag):
    if tag.getElementsByTagName('bfseries'):
        return 'bold'
    else:
        return 'normal'

def fontstyle(tag):
    if tag.getElementsByTagName('itshape'):
        return 'italic'
    else:
        return 'normal'

def make_amsthm_css(document):
    styles = document.userdata.getPath("packages/amsthm/styles")
    path = Path('styles')/'amsthm.css'
    with path.open('w') as cssfile:
        swap = document.userdata.getPath("packages/amsthm/swapnumbers")
        if swap:
            cssfile.write(r"""
            div[class$='_thmheading'] span:nth-child(2) {
                order: -1;
            }
            span[class$='_thmlabel']
            {
                margin-right: .5rem;
            }
            """)
        else:
            cssfile.write(r"""
            span[class$='_thmlabel']
            {
                margin-left: .5rem;
            }
            """)
        for name, style in styles.items():
            hf = style['headfont']
            css = ""
            if hf:
                hcolor = hf.getElementsByTagName('color')
                hcol = f"color: {hcolor[0].style['color']};" if hcolor else ''
                css += f"""
                div.theorem-style-{name} div[class$='_thmheading'] {{
                    font-style: {fontstyle(hf)};
                    font-weight: {fontweight(hf)};
                    {hcol}
                }}"""
            css += f"""
                div.theorem-style-{name} span[class$='_thmlabel']::after
                {{
                     content: '{style['punctuation']}';
                }}"""
            bf = style['bodyfont']
            if bf:
                bcolor = bf.getElementsByTagName('color')
                bcol = f"color: {bcolor[0].style['color']};" if bcolor else ''
                css += f"""
                div.theorem-style-{name} div[class$='_thmcontent'] {{
                    font-style: {fontstyle(bf)};
                    font-weight: {fontweight(bf)};
                    {bcol}
                }}
                """
            cssfile.write(css)
    return [str(path)]

def ProcessOptions(options, document):
    empty = TeXFragment()
    bf = TeXFragment()
    bf.ownerDocument = document
    bf.append(bfseries(), False)
    it = TeXFragment()
    it.ownerDocument = document
    it.append(itshape(), False)
    document.userdata.setPath('packages/amsthm/styles',{
        'plain' : {
            'name': 'plain',
            'above': dimen('0pt'),
            'below': dimen('0pt'),
            'bodyfont': it,
            'indentamount': dimen('0pt'),
            'headfont': bf,
            'punctuation': ".",
            'between': ' ',
            'headspec': None },
        'definition' : {
            'name': 'definition',
            'above': dimen('0pt'),
            'below': dimen('0pt'),
            'bodyfont': empty,
            'indentamount': dimen('0pt'),
            'headfont': bf,
            'punctuation': ".",
            'between': ' ',
            'headspec': None },
        'remark' : {
            'name': 'remark',
            'above': dimen("0pt"),
            'below': dimen("0pt"),
            'bodyfont': empty,
            'indentamount': dimen('0pt'),
            'headfont': bf,
            'punctuation': ".",
            'between': ' ',
            'headspec': None }})
    document.userdata.setPath('packages/amsthm/theorems',[])
    document.userdata.setPath('packages/amsthm/currentstyle', 'plain')
    cb = PackagePreCleanupCB(renderers='html5', data=make_amsthm_css)
    css = PackageCss(renderers='html5', path=Path('amsthm.css'))
    css.copy = False
    document.addPackageResource([cb, css])


class swapnumbers(Command):
    def invoke(self, tex):
        self.parse(tex)
        self.ownerDocument.userdata.setPath('packages/amsthm/swapnumbers', True)

class theoremstyle(Command):
    args = 'style:str'
    def invoke(self, tex):
        self.parse(tex)
        self.ownerDocument.userdata.setPath('packages/amsthm/currentstyle', self.attributes['style'])


class newtheoremstyle(Command):
    args = 'name:str above:dimen below:dimen bodyfont indentamount:dimen headfont punctuation:str between:dimen headspec'
    def invoke(self, tex):
        self.parse(tex)
        name = self.attributes['name']
        self.ownerDocument.userdata.setPath("packages/amsthm/styles/"+name, self.attributes)


class newtheorem(Command):
    args = '* name:str [ shared:str ] header:str [ parent:str]'

    def invoke(self, tex):
        self.parse(tex)
        a = self.attributes
        name = str(a['name'])
        header = a['header']
        star = a['*modifier*'] == '*'
        parent = a['parent']
        shared = a['shared']
        style = self.ownerDocument.userdata.getPath('packages/amsthm/currentstyle')

        l = self.ownerDocument.userdata.getPath('packages/amsthm/theorems')
        l.append(name)


        if star:
            counter = None
        else:
            if parent and not shared:
                self.ownerDocument.context.newcounter(name, initial=0, resetby=parent)
                self.ownerDocument.context.newcommand("the"+name, 0,
                                                      r"\the%s.\arabic{%s}"%(parent, name))
                counter = name
            elif shared:
                counter = shared
            else:
                counter = name
                self.ownerDocument.context.newcounter(name, initial=0)

        data = {'nodeName': 'thmenv',
                'thmName': name,
                'args': '[title]',
                'counter': counter,
                'caption': header,
                'forcePars': True,
                'blockType': True,
                'style': style
            }
        th = type(name, (Environment,), data)
        self.ownerDocument.context.addGlobal(name, th)


class qedhere(Command):
    pass


class qed(Command):
    pass


class proof(Environment):
    blockType = True
    args ='[caption]'
    forcePars= True

    def digest(self, tokens):
        Environment.digest(self, tokens)
        self.caption = self.attributes.get('caption', '')
