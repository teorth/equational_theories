"""
C.11.3 Bibliography and Citation (p208)

"""

import plasTeX
from plasTeX.Base.LaTeX.Sectioning import chapter
from plasTeX import Command
from plasTeX.Base.LaTeX.Lists import List


log = plasTeX.Logging.getLogger()

class bibliography(chapter):
    args = 'files:str'
    linkType = 'bibliography'

    def invoke(self, tex):
        res = chapter.invoke(self, tex)
        self.title = self.ownerDocument.createElement('bibname').expand(tex)
        self.loadBibliographyFile(tex)
        return res

    def loadBibliographyFile(self, tex):
        # Load bibtex file
        try:
            filename = tex.kpsewhich(tex.jobname+'.bbl')
            encoding = self.ownerDocument.config['files']['input-encoding']
            with open(filename, encoding=encoding) as f:
                tex.input(f.read())
        except OSError as msg:
            log.warning(msg)

class bibliographystyle(Command):
    args = 'style'

class thebibliography(List):
    args = 'widelabel'
    linkType = 'bibliography'

    class bibitem(List.item):
        args = '[ label ] key:str'

        def invoke(self, tex):
            res = List.item.invoke(self, tex)
            a = self.attributes
            # Put the entry into the global bibliography
            doc = self.ownerDocument
            bibitems = doc.userdata.getPath('bibliography/bibitems', {})
            bibitems[a['key']] = self
            doc.userdata.setPath('bibliography/bibitems', bibitems)
            self.ref = str(len([x for x in list(bibitems.values())
                                  if not x.attributes['label']]))
            key = a['key']
            label = a.get('label')
            bibcites = doc.userdata.getPath('bibliography/bibcites', {})
            if key not in list(bibcites.keys()):
                if label is None:
                    label = doc.createDocumentFragment()
                    label.extend(self.ref)
                bibcites[key] = label
            doc.userdata.setPath('bibliography/bibcites', bibcites)
            return res

        @property
        def id(self):
            return self.attributes['key']

        @id.setter
        def id(self, value):
            self.attributes['key'] = value

        @property
        def bibcite(self):
            doc = self.ownerDocument
            res = doc.createDocumentFragment()
            bibcites = doc.userdata.getPath('bibliography/bibcites', {})
            res.extend(bibcites.get(self.attributes['key']))
            return res

    def digest(self, tokens):
        if self.macroMode == Command.MODE_END:
            return
        for tok in tokens:
            if not isinstance(tok, thebibliography.bibitem):
                continue
            tokens.push(tok)
            break
        return List.digest(self, tokens)

class cite(Command):
    args = '[ text ] bibkeys:list:str'

    @property
    def bibitems(self):
        # Get all referenced items
        output = []
        doc = self.ownerDocument
        for x in self.attributes['bibkeys']:
            item = doc.userdata.getPath('bibliography/bibitems', {}).get(x)
            if item is None:
                log.warning('Bibliography item "%s" has no entry', x)
            else:
                output.append(item)
        return output

    @property
    def postnote(self):
        a = self.attributes
        if a['text'] is not None:
            return a['text']
        return ''

    def citation(self):
        """ (Jones et al., 1990) """
        res = self.ownerDocument.createDocumentFragment()
        i = 0
        res.append('[')
        for i, item in enumerate(self.bibitems):
            node = self.ownerDocument.createElement('bgroup')
            node.extend(item.bibcite)
            node.idref['bibitem'] = item
            res.append(node)
            if i < (len(self.bibitems)-1):
                res.append(', ')
            else:
                if self.postnote:
                    res.append(', ')
                    res.append(self.postnote)
                res.append(']')
        return res

class nocite(Command):
    args = 'bibkeys:str'

class bibcite(Command):
    args = 'key:str info'

    def invoke(self, tex):
        Command.invoke(self, tex)
        value = self.attributes['info'].firstChild
        doc = self.ownerDocument
        bibcites = doc.userdata.getPath('bibliography/bibcites', {})
        bibcites[self.attributes['key']] = value
        doc.userdata.setPath('bibliography/bibcites', bibcites)

class citation(Command):
    pass

class bibstyle(Command):
    pass

class bibdata(Command):
    pass

class newblock(Command):
    pass

class bibliographyref(Command):
    pass
