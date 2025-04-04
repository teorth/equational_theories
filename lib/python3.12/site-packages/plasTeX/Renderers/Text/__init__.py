from plasTeX.Renderers import Renderer as BaseRenderer
from plasTeX import encoding
import textwrap, re, string

class TextRenderer(BaseRenderer):
    """ Renderer for plain text documents """

    outputType = str
    fileExtension = '.txt'
    lineWidth = 76

    aliases = {
        'superscript': 'active::^',
        'subscript': 'active::_',
        'dollar': '$',
        'percent': '%',
        'opencurly': '{',
        'closecurly': '}',
        'underscore': '_',
        'ampersand': '&',
        'hashmark': '#',
        'space': ' ',
        'tilde': 'active::~',
        'at': '@',
        'backslash': '\\',
    }

    def __init__(self, *args, **kwargs):
        BaseRenderer.__init__(self, *args, **kwargs)

        # Load dictionary with methods
        for key in dir(self):
            if key.startswith('do__'):
                self[self.aliases[key[4:]]] = getattr(self, key)
            elif key.startswith('do_'):
                self[key[3:]] = getattr(self, key)

        self['default-layout'] = self['document-layout'] = self.default

        self.footnotes = []
        self.blocks = []

    def addBlock(self, s):
        """ Create a new block level element placeholder """
        self.blocks.append(s)
        width = max([len(x) for x in s.split('\n')])
        return u'\001[%s%s]' % (len(self.blocks)-1, '@'*width)

    def default(self, node):
        """ Rendering method for all non-text nodes """
        # Handle characters like \&, \$, \%, etc.
        if len(node.nodeName) == 1 and node.nodeName not in encoding.stringletters():
            return self.textDefault(node.nodeName)

        # Render child nodes
        return str(node)

    def processFileContent(self, document, s):
        s = BaseRenderer.processFileContent(self, document, s)

        # Put block level elements back in
        block_re = re.compile('(\\s*)\001\\[(\\d+)@+\\]')
        while 1:
            m = block_re.search(s)
            if not m:
                break

            space = ''
            before = m.group(1)
            if before is None:
                before = ''
            if '\n' in before:
                spaces = before.split('\n')
                space = spaces.pop()
                before = '\n'.join(spaces) + '\n'

            block = self.blocks[int(m.group(2))]
            block = space + block.replace('\n', u'\n%s' % space)

            s = s[:m.start()] + before + block + s[m.end():]

        # Clean up newlines
        return re.sub(r'\s*\n\s*\n(\s*\n)+', r'\n\n\n', s)

    def textDefault(self, node):
        return str(node)

    def wrap(self, s, **kwargs):
        return textwrap.wrap(str(s), self.lineWidth, break_long_words=False, **kwargs)

    def fill(self, s, **kwargs):
        return textwrap.fill(str(s), self.lineWidth, break_long_words=False, **kwargs)

    # Alignment

    def do_flushleft(self, node):
        return self.fill(str(node)).strip()

    do_raggedbottom = do_raggedright = do_leftline = do_flushleft

    def center(self, text):
        s = self.wrap(text)
        for i, line in enumerate(s):
            indent = int((self.lineWidth - len(line)) / 2)
            s[i] = '%s%s' % (' '*indent, line)
        return '\n'.join(s)

    def do_center(self, node):
        return self.center(str(node))

    do_centering = do_centerline = do_center

    def do_flushright(self, node):
        s = self.wrap(node)
        for i, line in enumerate(s):
            indent = self.lineWidth - len(line)
            s[i] = '%s%s' % (' '*indent, line)
        return '\n'.join(s).rstrip()

    do_raggedleft = do_llap = do_flushright

    # Arrays

    def do_array(self, node, cellspacing=(2,1), render=str):
        # Render the table cells and get min and max column widths
        colwidths = []
        for r, row in enumerate(node):
            for c, cell in enumerate(row):
                if isinstance(render, str):
                    s = getattr(cell, render)().strip()
                else:
                    s = render(cell).strip()
                if s.strip():
                    maxlength = max([len(x) for x in s.split('\n')])
                    minlength = min([len(x) for x in s.split() if x.strip()])
                else:
                    minlength = maxlength = 0
                if r == 0:
                    colwidths.append([minlength, maxlength])
                else:
                    colwidths[c] = [max(minlength, colwidths[c][0]),
                                    max(maxlength, colwidths[c][1])]

        # Determine best column widths
        maxline = self.lineWidth - len(colwidths)*cellspacing[0]
        minwidths = [x[0] for x in colwidths] # minimums
        maxwidths = [x[1] for x in colwidths] # maximums
        if sum(maxwidths) < maxline:
            outwidths = maxwidths
        elif sum(minwidths) > maxline:
            outwidths = minwidths
        else:
            outwidths = list(maxwidths)
            # If the minimum is also the maximum, take it out of the
            # algorithm to determine lengths.
            for i, item in enumerate(maxwidths):
                if maxwidths[i] == minwidths[i]:
                    maxwidths[i] = -1
            # Iteratively subtract one from the longest line until the
            # table will fit within maxline.
            while sum(outwidths) > maxline:
                index = maxwidths.index(max(maxwidths))
                maxwidths[i] -= 1
                outwidths[i] -= 1
                if maxwidths[i] == minwidths[i]:
                    maxwidths[i] = -1

        # Render cells to correct widths
        rendered = []
        for r, row in enumerate(node):
            current = []
            rendered.append(current)
            for c, cell in enumerate(row):
                origwidth = self.lineWidth
                self.lineWidth = outwidths[c]
                if isinstance(render, str):
                    s = getattr(cell, render)().split('\n')
                else:
                    s = render(cell).strip().split('\n')
                if s and r == 0 and c == 0:
                    s[0] = s[0].lstrip()
                current.append((max([len(x) for x in s]), len(s), s))
                self.lineWidth = origwidth

        # Pad cells to fill out a block
        for r, row in enumerate(rendered):
            linesneeded = max([x[1] for x in row]) + cellspacing[1]
            for c, cell in enumerate(row):
                width, height, content = cell
                # Add the appropriate number of lines
                for i in range(linesneeded - len(content)):
                    content.append(' '*width)
                # Pad all lines to the same length
                for i, line in enumerate(content):
                    content[i] = content[i] + ' '*(outwidths[c]-width+cellspacing[0])
                rendered[r][c] = content

        # Piece all of the table parts together
        output = []
        for row in rendered:
            # Continue until cell content is empty (the last cell in this case)
            while row[-1]:
                for cell in row:
                    output.append(cell.pop(0))
                # Get rid of unneeded whitespace and put in a line break
                output[-1] = output[-1].strip()
                output.append('\n')

        return ''.join(output)

    do_tabular = do_tabularx = do_longtable = do_array

    def do_cline(self, node):
        return ''

    def do_multicolumn(self, node):
        return str(node)

    # Bibliography
    def do_thebibliography(self, node):
        output = ['', 'Bibliography', '']
        for item in node:
            bullet = u'[%s] ' % item.bibcite
            bulletlen = len(bullet)
            output.append(self.fill(item, initial_indent=bullet,
                                        subsequent_indent=' '*bulletlen))
            output.append('')
        output.append('')
        return u'\n'.join(output)

    def do_bibliographystyle(self, node):
        return u''

    def do_bibliography(self, node):
        return self.default(node)

    def do_cite(self, node):
        output = []
        for item in node.citation():
            output.append(str(item))
        return u''.join(output)

    def do_bibliographyref(self, node):
        return self.default(node)

    # Boxes

    do_mbax = do_makebox = do_fbox = do_framebox = do_parbox = default
    do_minipage = do_raisebox = do_rule = default

    # Breaking

    def do_linebreak(self, node):
        return u'\n\n'

    do_newline = do_pagebreak = do_newpage = do_clearpage = do_cleardoublepage = do_linebreak

    # Crossref

    def do_ref(self, node):
        return str(node.idref['label'].ref)

    def do_pageref(self, node):
        return u'*'

    def do_label(self, node):
        return u''

    # Floats

    def do_figure(self, node):
        return str(node)

    do_table = do_marginpar = do_figure

    def do_caption(self, node):
        return u'%s %s: %s' % (node.title, node.ref, str(node))

    # Font Selection

    do_mdseries = do_textmd = do_bfseries = do_textbf = default
    do_rmfamily = do_textrm = do_sffamily = do_textsf = default
    do_ttfamily = do_texttt = do_upshape = do_textup = default
    do_itshape = do_textit = do_scshape = do_textsc = default
    do_slshape = do_textsl = do_textnormal = do_rm = default
    do_cal = do_it = do_sl = do_bf = do_tt = do_sc = default
    do_tiny = do_scriptsize = do_footnotesize = do_small = default
    do_normalsize = do_large = do_Large = do_LARGE = do_huge = do_HUGE = default

    def do_symbol(self, node):
        return u'*'

    # Footnotes
    def do_footnote(self, node):
        mark = u'[%s]' % (len(self.footnotes)+1)
        self.footnotes.append(self.fill(node, initial_indent='%s ' % mark,
                                     subsequent_indent=' ' * (len(mark)+1)).strip())
        return mark

    def do_footnotetext(self, node):
        self.do_footnote(node)
        return ''

    def do_footnotemark(self, node):
        return u'[%s]' % (len(self.footnotes)+1)

    # Index

    def do_theindex(self, node):
        return u''

    do_printindex = do_index = do_theindex

    # Lists

    def do_itemize(self, node):
        output = []
        for item in node:
            bullet = '   * '
            bulletlen = len(bullet)
            output.append(self.fill(item, initial_indent=bullet,
                                        subsequent_indent=' '*bulletlen))
        return self.addBlock(u'\n'.join(output))

    def do_enumerate(self, node):
        output = []
        for i, item in enumerate(node):
            bullet = '   %d. ' % (i+1)
            bulletlen = len(bullet)
            output.append(self.fill(item, initial_indent=bullet,
                                        subsequent_indent=' '*bulletlen))
        return self.addBlock(u'\n'.join(output))

    def do_description(self, node):
        output = []
        for item in node:
            bullet = '   %s - ' % item.attributes.get('term','')
            bulletlen = len(bullet)
            output.append(self.fill(item, initial_indent=bullet,
                                        subsequent_indent='      '))
        return self.addBlock(u'\n'.join(output))

    do_list = do_trivlist = do_description

    # Math

    def do_math(self, node):
        return re.sub(r'\s*(_|\^)\s*', r'\1', node.source)

    do_ensuremath = do_math

    def do_equation(self, node):
        s = u'   %s' % re.compile(r'^\s*\S+\s*(.*?)\s*\S+\s*$', re.S).sub(r'\1', node.source)
        return re.sub(r'\s*(_|\^)\s*', r'\1', s)

    do_displaymath = do_equation

    def do_eqnarray(self, node):
        def render(node):
            s = re.compile(r'^\$\\displaystyle\s*(.*?)\s*\$\s*$', re.S).sub(r'\1', node.source)
            return re.sub(r'\s*(_|\^)\s*', r'\1', s)
        s = self.do_array(node, cellspacing=(1,1), render=render)
        output = []
        for line in s.split('\n'):
            output.append('   %s' % line)
        return u'\n'.join(output)

    do_align = do_gather = do_falign = do_multiline = do_eqnarray
    do_multline = do_alignat = do_split = do_eqnarray

    # Misc

    do_bgroup = default

    def do_def(self, node):
        return u''

    do_tableofcontents = do_input = do_protect = do_let = do_def
    do_newcommand = do_hfill = do_hline = do_openout = do_renewcommand = do_def
    do_write = do_appendix = do_global = do_noindent = do_def
    do_include = do_markboth = do_setcounter = do_refstepcounter = do_def
    do_medskip = do_smallskip = do_parindent = do_indent = do_setlength = do_def
    do_settowidth = do_addtolength = do_nopagebreak = do_newwrite = do_def
    do_newcounter = do_typeout = do_sloppypar = do_hfil = do_thispagestyle = do_def

    def do_egroup(self, node):
        return u''

    # Pictures

    def do_picture(self, node):
        return u''

    # Primitives

    def do_par(self, node):
        numchildren = len(node.childNodes)
        if numchildren == 1 and not isinstance(node[0], str):
            return u'%s\n\n' % str(node)
        elif numchildren == 2 and isinstance(node[1], str) and \
           not node[1].strip():
            return u'%s\n\n' % str(node)
        s = u'%s\n\n' % self.fill(node)
        if not s.strip():
            return u''
        return s

    def do__superscript(self, node):
        return self.default(node)

    def do__subscript(self, node):
        return self.default(node)

    # Quotations

    def do_quote(self, node):
        backslash = self['\\']
        self['\\'] = lambda *args: u'\001'
        res = [x.strip() for x in str(node).split(u'\001')]
        output = []
        for par in [x.strip() for x in str(node).split(u'\n\n')]:
            for item in [x.strip() for x in par.split(u'\001')]:
                output.append(self.fill(item, initial_indent='   ', subsequent_indent='      '))
            output.append('')
        output.pop()
        self['\\'] = backslash
        return u'\n'.join(output)

    do_quotation = do_verse = do_quote

    # Sectioning

    def do_document(self, node):
        content = str(node).rstrip()
        footnotes = u'\n\n'.join(self.footnotes).rstrip()
        if footnotes:
            content = u'%s\n\n\n%s' % (content, footnotes)
        return u'%s\n\n' % content

    def do_maketitle(self, node):
        output = []
        metadata = node.ownerDocument.userdata
        if 'title' in metadata:
            output.append(self.center(metadata['title']).rstrip().upper())
            output.append('')
        if 'author' in metadata:
            for author in metadata['author']:
                if [a for a in author if getattr(a,'macroName','') == '\\']:
                    for a in author:
                        if getattr(a,'macroName','') == '\\':
                            continue
                        output.append(self.center(a).rstrip())
                else:
                    output.append(self.center(author).rstrip())
            output.append('')
        if 'date' in metadata:
            output.append(self.center(metadata['date']).rstrip())
            output.append('')
        if 'thanks' in metadata:
            output.append(self.center(metadata['thanks']).rstrip())
        return u'\n%s\n\n' % u'\n'.join(output)

    def do_section(self, node):
        return u'\n\n\n%s' % (u'%s\n\n%s' % (self.fill(node.fullTitle), node)).strip()

    do_part = do_chapter = do_subsection = do_subsubsection = do_section
    do_paragraph = do_subparagraph = do_subsubparagraph = do_section

    def do_title(self, node):
        return u''

    do_author = do_date = do_thanks = do_title

    def do_abstract(self, node):
        return self.center(node)

    # Sentences

    def do__dollar(self, node):
        return u'$'

    def do__percent(self, node):
        return u'%'

    def do__opencurly(self, node):
        return u'{'

    def do__closecurly(self, node):
        return u'}'

    def do__underscore(self, node):
        return u'_'

    def do__ampersand(self, node):
        return u'&'

    def do__hashmark(self, node):
        return u'#'

    def do__space(self, node):
        return u' '

    def do_LaTeX(self, node):
        return u'LaTeX'

    def do_TeX(self, node):
        return u'TeX'

    def do_emph(self, node):
        return self.default(node)

    do_em = do_emph

    def do__tilde(self, node):
        return u' '

    def do_enspace(self, node):
        return u' '

    do_quad = do_qquad = do_enspace

    def do_enskip(self, node):
        return u''

    do_thinspace = do_enskip

    def do_underbar(self, node):
        return self.default(node)

    # Space

    def do_hspace(self, node):
        return u' '

    def do_vspace(self, node):
        return u''

    do_bigskip = do_medskip = do_smallskip = do_vspace

    # Tabbing - not implemented yet

    # Verbatim

    def do_verbatim(self, node):
        return re.sub(r'^\s*\n', r'', str(node)).rstrip()

    do_alltt = do_verbatim

    def do_mbox(self, node):
        return self.default(node)

    def do__at(self, node):
        return u''

    def do__backslash(self, node):
        return u'\\'

Renderer = TextRenderer
