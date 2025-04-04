from plasTeX import Command, Environment

def ProcessOptions(options, document):
    context = document.context

    languages = list(document.context.languages.keys())
    for key, value in list(options.items()):
        if key in languages:
            context.loadLanguage(key, document)
        if key in ['german','ngerman']:
            class glqq(Command): str = '\u201e'
            class grqq(Command): str = '\u201c'
            context.addGlobal('glqq', glqq)
            context.addGlobal('grqq', grqq)

class selectlanguage(Command):
    args = 'lang:str'

    def invoke(self, tex):
        res = Command.invoke(self, tex)
        self.ownerDocument.context.loadLanguage(self.attributes['lang'], self.ownerDocument)
        return res

class otherlanguage(Environment):
    args = 'lang:str'

    def invoke(self, tex):
        res = Environment.invoke(self, tex)
        doc = self.ownerDocument
        if self.macroMode != self.MODE_END:
            self.ownerDocument.userdata.setPath('babel/previouslanguage',
                                              doc.context.currentLanguage)
            doc.context.loadLanguage(self.attributes['lang'], self.ownerDocument)
        else:
            lang = doc.userdata.getPath('babel/previouslanguage')
            doc.context.loadLanguage(lang, self.ownerDocument)
        return res

class foreignlanguage(Command):
    args = 'lang:str self'

    def postArgument(self, arg, value, tex):
        if arg.name == 'lang':
            doc = self.ownerDocument
            doc.userdata.setPath('babel/previouslanguage',
                               doc.context.currentLanguage)
            doc.context.loadLanguage(value, doc)
        else:
            Command.postArgument(self, arg, value, tex)

    def invoke(self, tex):
        res = Command.invoke(self, tex)
        doc = self.ownerDocument
        lang = doc.userdata.getPath('babel/previouslanguage')
        doc.context.loadLanguage(lang, doc)
        return res

class OtherLanguageStar(Environment):
    args = 'lang:str'
    macroName = 'otherlanguage*'

class iflanguage(Command):
    args = 'lang:str yes:nox no:nox'

    def invoke(self, tex):
        res = Command.invoke(self, tex)
        if self.ownerDocument.context.currentLanguage == self.attributes['lang']:
            return self.attributes['yes']
        return self.attributes['no']
        
