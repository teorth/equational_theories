from plasTeX.Base import Command

class url(Command):
    args = 'url:url'

class urldef(Command):
    args = 'name:cs type:cs'

    class DefinedURL(Command):
        result = None
        def invoke(self, tex):
            return self.result

    def invoke(self, tex):
        Command.invoke(self, tex)
        name = self.attributes['name']
        type = self.attributes['type']
        c = self.ownerDocument.context
        obj = c[type]()
        obj.parentNode = self.parentNode
        obj.ownerDocument = self.ownerDocument
        result = obj.invoke(tex)
        c.addGlobal(name, type(name, (self.DefinedURL,), {'result':result}))

class urlstyle(Command):
    args = 'style:str'

class DeclareUrlCommand(Command):
    args = 'name:cs style'
    def invoke(self, tex):
        Command.invoke(self, tex)
        name = str(self.attributes['name'])
        c = self.ownerDocument.context
        c.addGlobal(name, type(name, (url,), {}))
