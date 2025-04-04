r"""
natbib

TODO:
    - compress multiple years
    - \shortcites
    - Indexing features
    - Bibliography preamble

"""

import re, string
from plasTeX import Base, Text

def ProcessOptions(options, document):
    """ Process package options """
    options = options or dict()
    new_options = dict()
    punct = {'post': bstyleoption(', '),
             'open': bstyleoption('('),
             'close':bstyleoption(')'),
             'sep':  bstyleoption(';'),
             'style':bstyleoption('a'),
             'dates':bstyleoption(','),
             'years':bstyleoption(',')}
    for key, value in options.items():
        if key == 'numbers':
            punct['style'] = 'n'
            new_options.update({'square':True, 'comma':True})
        elif key == 'super':
            punct['style'] = 's'
            punct['open'] = ''
            punct['close'] = ''
        elif key == 'authoryear':
            new_options.update({'round':True, 'colon':True})
        elif key == 'round':
            punct['open'] = '('
            punct['close'] = ')'
        elif key == 'square':
            punct['open'] = '['
            punct['close'] = ']'
        elif key == 'angle':
            punct['open'] = '<'
            punct['close'] = '>'
        elif key == 'curly':
            punct['open'] = '{'
            punct['close'] = '}'
        elif key == 'comma':
            punct['sep'] = ','
        elif key == 'colon':
            punct['sep'] = ';'
        elif key == 'sectionbib':
            Base.bibliography.level = Base.section.level
        elif key == 'sort':
            pass
        elif key in ['sort&compress','sortandcompress']:
            pass
        elif key == 'longnamesfirst':
            pass
        elif key == 'nonamebreak':
            pass
    document.userdata['natbib'] = {**options, **new_options, 'punctuation': punct}

class bibliography(Base.bibliography):

    class setcounter(Base.Command):
        # Added so that setcounters in the aux file don't mess counters up
        args = 'name:nox num:nox'

    def loadBibliographyFile(self, tex):
        doc = self.ownerDocument
        # Clear out any bib info from the standard package.
        # We have to get our info from the aux file.
        doc.userdata.setPath('bibliography/bibcites', {})
        self.ownerDocument.context.push(self)
        self.ownerDocument.context['setcounter'] = self.setcounter
        tex.loadAuxiliaryFile()
        self.ownerDocument.context.pop(self)
        Base.bibliography.loadBibliographyFile(self, tex)

class bibstyle(Base.Command):
    args = 'style:str'

class citestyle(Base.Command):
    args = 'style:str'

    styles = {
        'plain'  : [', ','[',']',',','n','',','],
        'plainnat':[', ','[',']',',','a',',',','],
        'chicago': [', ','(',')',';','a',',',','],
        'chicago': [', ','(',')',';','a',',',','],
        'named'  : [', ','[',']',';','a',',',','],
        'agu'    : [', ','[',']',';','a',',',', '],
        'egs'    : [', ','(',')',';','a',',',','],
        'agsm'   : [', ','(',')',';','a','',','],
        'kluwer' : [', ','(',')',';','a','',','],
        'dcu'    : [', ','(',')',';','a',';',','],
        'aa'     : [', ','(',')',';','a','',','],
        'pass'   : [', ','(',')',';','a',',',','],
        'anngeo' : [', ','(',')',';','a',',',','],
        'nlinproc':[', ','(',')',';','a',',',','],
        'cospar' : [', ','/','/',',','n','',''],
        'esa'    : [', ','(Ref. ',')',',','n','',''],
        'nature' : [', ','','',',','s','',','],
    }

    def invoke(self, tex):
        res = Base.Command.invoke(self, tex)
        try:
            s = self.styles[self.attributes['style']]
        except KeyError:
        #    log.warning('Could not find bibstyle: "%s"',
        #                 self.attributes['style'])
            return res
        p = self.ownerDocument.userdata['natbib']['punctuation']
        for i, opt in enumerate(['post','open','close','sep','style','dates','years']):
            p[opt] = s[i]
        return res

class bstyleoption(Text):
    """ Option that can only be overridden by package options,
        citestyle, or bibpunct """

class bibliographystyle(citestyle):
    def invoke(self, tex):
        res = Base.Command.invoke(self, tex)
        try:
            s = self.styles[self.attributes['style']]
        except KeyError:
        #    log.warning('Could not find bibstyle: "%s"',
        #                 self.attributes['style'])
            return res
        p = self.ownerDocument.userdata['natbib']['punctuation']
        for i, opt in enumerate(['post','open','close','sep','style','dates','years']):
            if isinstance(p[opt], bstyleoption):
                p[opt] = s[i]
        return res

class bibpunct(Base.Command):
    """ Set up punctuation of citations """
    args = '[ post:str ] open:str close:str sep:str ' + \
           'style:str dates:str years:str'
    def invoke(self, tex):
        res = Base.Command.invoke(self, tex)
        punct = self.ownerDocument.userdata['natbib']['punctuation']
        for key, value in self.attributes.items():
            if value is None:
                continue
            elif isinstance(value, str):
                punct[key] = value
            else:
                punct[key] = value.textContent
        return res

class bibcite(Base.Command):
    """ Auxiliary file information """
    args = 'key:str info'

    def invoke(self, tex):
        Base.Command.invoke(self, tex)
        value, year, author, fullauthor = list(self.attributes['info'])
        value.attributes['year'] = year
        value.attributes['author'] = author
        if not fullauthor.textContent.strip():
            value.attributes['fullauthor'] = author
        else:
            value.attributes['fullauthor'] = fullauthor
        doc = self.ownerDocument
        bibcites = doc.userdata.getPath('bibliography/bibcites', {})
        bibcites[self.attributes['key']] = value
        doc.userdata.setPath('bibliography/bibcites', bibcites)

class thebibliography(Base.thebibliography):

    class bibitem(Base.thebibliography.bibitem):

        @property
        def bibcite(self):
            try:
                doc = self.ownerDocument
                return doc.userdata.getPath('bibliography/bibcites', {})[self.attributes['key']]
            except KeyError as msg:
                pass
            # We don't have a citation that matches, fill the fields
            # with dummy data
            value = self.ownerDocument.createElement('citation')
            value.parentNode = self
            value.append('??')
            for item in ['year','author','fullauthor']:
                obj = self.ownerDocument.createDocumentFragment()
                obj.parentNode = value
                obj.append('??')
                value.attributes[item] = obj
            return value

        @property # type: ignore # mypy#4125
        def ref(self):
            return self.bibcite.textContent

        @ref.setter
        def ref(self, value):
            pass

class harvarditem(thebibliography.bibitem):
    args = '[ abbrlabel ] label year key:str'

class NatBibCite(Base.cite):
    """ Base class for all natbib-style cite commands """
    args = '* [ text ] [ text2 ] bibkeys:list:str'

    class Connector(str):
        pass

    @property
    def punctuation(self):
        return self.ownerDocument.userdata['natbib']['punctuation']

    @property
    def bibitems(self):
        items = []
        doc = self.ownerDocument
        opts = doc.userdata['natbib']
        b = doc.userdata.getPath('bibliography/bibitems', {})
        for key in self.attributes['bibkeys']:
            if key in b:
                items.append(b[key])
        if len(items) > 1:
            if self.isNumeric() and \
            ('sort' in opts or 'sort&compress' in opts or 'sortandcompress' in opts):
                items.sort(key=lambda x: int(x.ref))
                if 'sort&compress' in opts or 'sortandcompress' in opts:
                    items = self.compressRange(items)
        return items

    def compressRange(self, items):
        """ Compress ranges of numbers """
        idx, idxdict = [], {}
        for i, value in enumerate(items):
            idx.append(int(value.ref))
            idxdict[int(value.ref)] = value
        output = []
        for i, value in enumerate(idx):
            if i == 0:
                output.append(' ')
                output.append(value)
            elif idx[i-1] == (value-1):
                output.append('-')
                output.append(value)
            else:
                output.append(' ')
                output.append(value)
        output.append(' ')
        output = ''.join([str(x) for x in output])
        output = re.sub(r'( \d+)-(\d+ )', r'\1 \2', output)
        while re.search(r'-\d+-', output):
            output = re.sub(r'-\d+-', r'-', output)
        output = [x for x in re.split(r'([ -])', output) if x.strip()]
        for i, value in enumerate(output):
            if value in string.digits:
                output[i] = idxdict[int(value)]
            else:
                output[i] = self.Connector(value)
        return output

    def isConnector(self, value):
        return isinstance(value, self.Connector)

    @property
    def prenote(self):
        """ Text that comes before the citation """
        a = self.attributes
        if a.get('text2') is not None and a.get('text') is not None:
            if not a.get('text').textContent.strip():
                return ''
            out = self.ownerDocument.createElement('bgroup')
            out.extend(a['text'])
            out.append(' ')
            return out
        return ''

    @property
    def postnote(self):
        """ Text that comes after the citation """
        a = self.attributes
        if a.get('text2') is not None and a.get('text') is not None:
            if not a.get('text2').textContent.strip():
                return ''
            out = self.ownerDocument.createElement('bgroup')
            out.append(self.punctuation['post'])
            out.extend(a['text2'])
            return out
        elif a.get('text') is not None:
            if not a.get('text').textContent.strip():
                return ''
            out = self.ownerDocument.createElement('bgroup')
            out.append(self.punctuation['post'])
            out.extend(a['text'])
            return out
        return ''

    @property
    def separator(self):
        """ Separator for multiple items """
        return self.punctuation['sep']

    @property
    def dates(self):
        """ Separator between author and dates """
        return self.punctuation['dates']

    @property
    def years(self):
        """ Separator for multiple years """
        return self.punctuation['years']

    def selectAuthorField(self, key, full=False):
        """ Determine if author should be a full name or shortened """
        if full or self.attributes.get('*modifier*'):
            return 'fullauthor'
        doc = self.ownerDocument
        opts = doc.userdata['natbib']
        # longnamesfirst means that only the first reference
        # gets the full length name, the rest use short names.
        cited = doc.userdata.getPath('bibliography/cited', [])
        if 'longnamesfirst' in opts and key not in cited:
            full = True
            cited.append(key)
        doc.userdata.setPath('bibliography/cited', cited)
        if full:
            return 'fullauthor'
        return 'author'

    def isNumeric(self):
        return self.punctuation['style'] in ['n','s']

    def isSuperScript(self):
        return self.punctuation['style'] == 's'

    def citeValue(self, item, text=None):
        """ Return cite value based on current style """
        b = self.ownerDocument.createElement('bibliographyref')
        b.idref['bibitem'] = item
        if text is not None:
            b.append(text)
        elif self.punctuation['style'] in ['n','s']:
            b.append(item.bibcite)
        else:
            b.append(item.bibcite.attributes['year'])
        return b

    def capitalize(self, item):
        """ Capitalize the first text node """
        item = item.cloneNode(True)
        textnodes = [x for x in item.allChildNodes
                       if x.nodeType == self.TEXT_NODE]
        if not textnodes:
            return item
        node = textnodes.pop(0)
        node.parentNode.replaceChild(node.cloneNode(True).capitalize() ,node)
        return item

# class citep(NatBibCite):

#     def numcitation(self):
#         """ Numeric style citations """
#         res = []
#         res.append(self.punctuation['open'])
#         for i, item in enumerate(self.bibitems):
#             frag = self.ownerDocument.createDocumentFragment()
#             frag.append(item.ref)
#             frag.idref = item
#             res.append(frag)
#             res.append(self.punctuation['sep'])
#         res.pop()
#         res.append(self.punctuation['close'])
#         return res

#     def citation(self):
#         if self.punctuation['style'] == 'n':
#             return self.numcitation()
#         elif self.punctuation['style'] == 's':
#             return self.numcitation()

#         res = []
#         res.append(self.punctuation['open'] + self.prenote)
#         prevauthor = None
#         prevyear = None
#         duplicateyears = 0
#         previtem = None
#         opts = self.ownerDocument.userdata['natbib']
#         for i, item in enumerate(self.bibitems):
#             currentauthor = item.citeauthor().textContent
#             currentyear = item.citeyear().textContent

#             # Previous author and year are the same
#             if prevauthor == currentauthor and prevyear == currentyear:
#                 res.pop()
#                 # This is the first duplicate
#                 if duplicateyears == 0:
#                     # Make a reference that points to the same item as
#                     # the first citation in this set.  This will make
#                     # hyperlinked output prettier since the 'a' will
#                     # be linked to the same place as the reference that
#                     # we just put out.
#                     res.append('')
#                     frag = self.ownerDocument.createDocumentFragment()
#                     frag.append('a')
#                     frag.idref = previtem
#                     res.append(frag)
#                     res.append(self.punctuation['years'])
#                 else:
#                     res.append(self.punctuation['years'])
#                 # Create a new fragment with b,c,d... in it
#                 frag = self.ownerDocument.createDocumentFragment()
#                 frag.append(chr(duplicateyears+ord('b')))
#                 frag.idref = item
#                 res.append(frag)
#                 res.append(self.punctuation['sep']+' ')
#                 duplicateyears += 1

#             # Previous author is the same
#             elif prevauthor == currentauthor:
#                 duplicateyears = 0
#                 res.pop()
#                 res.append(self.punctuation['years']+' ')
#                 res.append(item.citeyear())
#                 res.append(self.punctuation['sep']+' ')

#             # Nothing about the previous citation is the same
#             else:
#                 doc = self.ownerDocument
#                 cited = doc.userdata.getPath('bibliography/cited', [])
#                 duplicateyears = 0
#                 if 'longnamesfirst' in opts and \
#                    item.attributes['key'] not in cited:
#                     cited.append(item.attributes['key'])
#                     doc.userdata.setPath('bibliography/cited', cited)
#                     res.append(item.citealp(full=True))
#                 else:
#                     res.append(item.citealp())
#                 res.append(self.punctuation['sep']+' ')

#             prevauthor = currentauthor
#             prevyear = currentyear
#             previtem = item

#         res.pop()
#         res.append(self.postnote + self.punctuation['close'])
#         return res

class citet(NatBibCite):

    def citation(self, full=False, capitalize=False, text=None):
        """ Jones et al. (1990) """
        if text is None and self.isNumeric():
            return self.numcitation()
        res = self.ownerDocument.createDocumentFragment()
        i = 0
        sameauthor = prevauthor = None
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if text is None:
                if not item.bibcite.attributes:
                    continue
                fullauthor = item.bibcite.attributes['fullauthor'].textContent
                sameauthor = (prevauthor == fullauthor)
                prevauthor = fullauthor
                # Author, only print author if it wasn't equal to the last author
                if sameauthor:
                    # Pop punctuation from previous year
                    res.pop()
                    res.pop()
                    # Add year separator
                    res.append(self.years+' ')
                else:
                    author = self.selectAuthorField(item.attributes['key'], full=full)
                    if i == 0 and capitalize:
                        res.extend(self.capitalize(item.bibcite.attributes[author]))
                    else:
                        res.extend(item.bibcite.attributes[author])
                    res.append(' ')
                    res.append(self.punctuation['open'])
                    # Prenote
                    res.append(self.prenote)
            # Year or text
            res.append(self.citeValue(item, text=text))
            # Separator, postnote, and closing punctuation
            if i < (len(bibitems)-1):
                if text is None:
                    res.append(self.punctuation['close'])
                    res.append(self.separator+' ')
            else:
                res.append(self.postnote)
                if text is None:
                    res.append(self.punctuation['close'])
        return res

    def numcitation(self):
        """ (1, 2) """
        element = self.ownerDocument.createElement
        orig = res = self.ownerDocument.createDocumentFragment()
        if self.isSuperScript():
            group = element('bgroup')
            orig.append(group)
            res = element('active::^')
            group.append(res)
        i = 0
        res.append(self.prenote)
        res.append(self.punctuation['open'])
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if self.isConnector(item):
                res.pop()
                res.append('-')
                continue
            res.append(self.citeValue(item))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
        res.append(self.punctuation['close'])
        res.append(self.postnote)
        return orig

class citetfull(citet):

    def citation(self):
        """ Jones, Baker, and Williams (1990) """
        return citet.citation(self, full=True)

class Citet(citet):

    def citation(self):
        return citet.citation(self, capitalize=True)

class citep(NatBibCite):

    def citation(self, full=False, capitalize=False, text=None):
        """ (Jones et al., 1990) """
        if text is None and self.isNumeric():
            return self.numcitation()
        res = self.ownerDocument.createDocumentFragment()
        res.append(self.punctuation['open'])
        res.append(self.prenote)
        i = 0
        sameauthor = prevauthor = None
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if text is None:
                if item.bibcite.attributes is None:
                    continue
                fullauthor = item.bibcite.attributes['fullauthor'].textContent
                sameauthor = (prevauthor == fullauthor)
                prevauthor = fullauthor
                # Author, only print author if it wasn't equal to the last author
                if sameauthor:
                    res.pop()
                    res.append(self.years+' ')
                else:
                    author = self.selectAuthorField(item.attributes['key'], full=full)
                    if i == 0 and capitalize:
                        res.extend(self.capitalize(item.bibcite.attributes[author]))
                    else:
                        res.extend(item.bibcite.attributes[author])
                    res.append(self.dates+' ')
            res.append(self.citeValue(item, text=text))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
                res.append(self.punctuation['close'])
        return res

    def numcitation(self):
        """ (1, 2) """
        element = self.ownerDocument.createElement
        orig = res = self.ownerDocument.createDocumentFragment()
        if self.isSuperScript():
            group = element('bgroup')
            orig.append(group)
            res = element('active::^')
            group.append(res)
        res.append(self.punctuation['open'])
        res.append(self.prenote)
        i = 0
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if self.isConnector(item):
                res.pop()
                res.append('-')
                continue
            res.append(self.citeValue(item))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
                res.append(self.punctuation['close'])
        return orig

class cite(citep, citet):

    def citation(self, full=False, capitalize=False):
        if self.prenote or self.postnote:
            return citep.citation(self, full=full, capitalize=capitalize)
        return citet.citation(self, full=full, capitalize=capitalize)

class Cite(cite):

    def citation(self):
        return cite.citation(self, capitalize=True)

class citepfull(citep):

    def citation(self):
        """ (Jones, Baker, and Williams, 1990) """
        return citep.citation(self, full=True)

class Citep(citep):

    def citation(self):
        return citep.citation(self, capitalize=True)

class citealt(NatBibCite):

    def citation(self, full=False, capitalize=False):
        """ Jones et al. 1990 """
        if self.isNumeric():
            return self.numcitation()
        res = self.ownerDocument.createDocumentFragment()
        i = 0
        prevauthor = sameauthor = None
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if not item.bibcite.attributes:
                fullauthor = '???'
            else:
                fullauthor = item.bibcite.attributes['fullauthor'].textContent
            sameauthor = (prevauthor == fullauthor)
            prevauthor = fullauthor
            # Author, only print author if it wasn't equal to the last author
            if sameauthor:
                res.pop()
                res.append(self.years+' ')
            else:
                author = self.selectAuthorField(item.attributes['key'], full=full)
                if not item.bibcite.attributes:
                    res.extend('???')
                elif i == 0 and capitalize:
                    res.extend(self.capitalize(item.bibcite.attributes[author]))
                else:
                    res.extend(item.bibcite.attributes[author])
                res.append(' ')
                res.append(self.prenote)
            res.append(self.citeValue(item))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
        return res

    def numcitation(self):
        """ 1, 2 """
        element = self.ownerDocument.createElement
        orig = res = self.ownerDocument.createDocumentFragment()
        if self.isSuperScript():
            group = element('bgroup')
            orig.append(group)
            res = element('active::^')
            group.append(res)
        i = 0
        res.append(self.prenote)
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if self.isConnector(item):
                res.pop()
                res.append('-')
                continue
            res.append(self.citeValue(item))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
        return orig

class citealtfull(citealt):

    def citation(self):
        """ Jones, Baker, and Williams 1990 """
        return citealt.citation(self, full=True)

class Citealt(citealt):

    def citation(self):
        return citealt.citation(self, capitalize=True)

class citealp(NatBibCite):

    def citation(self, full=False, capitalize=False):
        """ Jones et al., 1990 """
        if self.isNumeric():
            return self.numcitation()
        res = self.ownerDocument.createDocumentFragment()
        res.append(self.prenote)
        i = 0
        prevauthor = sameauthor = None
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if not item.bibcite.attributes:
                fullauthor = '???'
            else:
                fullauthor = item.bibcite.attributes['fullauthor'].textContent
            sameauthor = (prevauthor == fullauthor)
            prevauthor = fullauthor
            # Author, only print author if it wasn't equal to the last author
            if sameauthor:
                res.pop()
                res.append(self.years+' ')
            else:
                author = self.selectAuthorField(item.attributes['key'], full=full)
                if not item.bibcite.attributes:
                    res.extend('???')
                elif i == 0 and capitalize:
                    res.extend(self.capitalize(item.bibcite.attributes[author]))
                else:
                    res.extend(item.bibcite.attributes[author])
                res.append(self.separator+' ')
            res.append(self.citeValue(item))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
        return res

    def numcitation(self):
        """ 1, 2 """
        element = self.ownerDocument.createElement
        orig = res = self.ownerDocument.createDocumentFragment()
        if self.isSuperScript():
            group = element('bgroup')
            orig.append(group)
            res = element('active::^')
            group.append(res)
        res.append(self.prenote)
        i = 0
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            if self.isConnector(item):
                res.pop()
                res.append('-')
                continue
            res.append(self.citeValue(item))
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
        res.append(self.postnote)
        return orig

class citealpfull(citealp):

    def citation(self):
        """ Jones, Baker, and Williams, 1990 """
        return citealp.citation(self, full=True)

class Citealp(citealp):

    def citation(self):
        return citealp.citation(self, capitalize=True)

class citeauthor(NatBibCite):

    def citation(self, full=False, capitalize=False):
        """ Jones et al. """
        if self.isNumeric():
            return
        res = self.ownerDocument.createDocumentFragment()
        #res.append(self.prenote)
        i = 0
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            author = self.selectAuthorField(item.attributes['key'], full=full)
            b = self.ownerDocument.createElement('bibliographyref')
            b.idref['bibitem'] = item
            if not item.bibcite.attributes:
                b.append('???')
            elif i == 0 and capitalize:
                b.append(self.capitalize(item.bibcite.attributes[author]))
            else:
                b.append(item.bibcite.attributes[author])
            res.append(b)
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
        return res

class citefullauthor(citeauthor):

    def citation(self):
        """ Jones, Baker, and Williams """
        return citeauthor.citation(self, full=True)

class Citeauthor(citeauthor):

    def citation(self):
        return citeauthor.citation(self, capitalize=True)

class citeyear(NatBibCite):

    def citation(self):
        """ 1990 """
        if self.isNumeric():
            return
        res = self.ownerDocument.createDocumentFragment()
        #res.append(self.prenote)
        i = 0
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            b = self.ownerDocument.createElement('bibliographyref')
            b.idref['bibitem'] = item
            if not item.bibcite.attributes:
                b.append('???')
            else:
                b.append(item.bibcite.attributes['year'])
            res.append(b)
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
        return res

class citeyearpar(NatBibCite):

    def citation(self):
        """ (1990) """
        if self.isNumeric():
            return
        res = self.ownerDocument.createDocumentFragment()
        res.append(self.punctuation['open'])
        res.append(self.prenote)
        i = 0
        bibitems = self.bibitems
        for i, item in enumerate(bibitems):
            b = self.ownerDocument.createElement('bibliographyref')
            b.idref['bibitem'] = item
            if not item.bibcite.attributes:
                b.append('???')
            else:
                b.append(item.bibcite.attributes['year'])
            res.append(b)
            if i < (len(bibitems)-1):
                res.append(self.separator+' ')
            else:
                res.append(self.postnote)
        res.append(self.punctuation['close'])
        return res

class citetext(Base.Command):
    args = 'self'
    def digest(self, tokens):
        punct = self.ownerDocument.userdata['natbib']['punctuation']
        self.insert(0, punct['open'])
        self.append(punct['close'])

class defcitealias(Base.Command):
    args = 'key:str text'
    aliases = {}
    def invoke(self, tex):
        res = Base.Command.invoke(self, tex)
        defcitealias.aliases[self.attributes['key']] = self.attributes['text']
        return res

class citetalias(citet):
    args = 'bibkeys:list:str'
    def citation(self):
        return citet.citation(self, text=defcitealias.aliases.get(self.attributes['bibkeys'][0],''))

class citepalias(citep):
    args = 'bibkeys:list:str'
    def citation(self):
        return citep.citation(self, text=defcitealias.aliases.get(self.attributes['bibkeys'][0],''))

class shortcites(Base.Command):
    args = 'bibkeys:list:str'

class urlstyle(Base.Command):
    pass
