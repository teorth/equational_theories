from plasTeX import Command
from plasTeX.Tokenizer import Token, Other

class MakeShortVerb(Command):
    args = 'char:cs'
    def invoke(self, tex):
        # Parse arguments
        res = Command.invoke(self, tex)
        # Get the specified character from the command sequence in
        # the `char` attribute
        char = str(self.attributes['char'].macroName)
        # Set the specified character as active
        self.ownerDocument.context.catcode(char, Token.CC_ACTIVE)
        # Create a new macro for the active character that calls _ShortVerb
        newclass = type('active::%s' % char, (_ShortVerb,),{})
        # Add the new macro to the global namespace
        self.ownerDocument.context['active::%s' % char] = newclass
        return res

class _ShortVerb(Command):
    """ Command to handle short verbatims """
    def invoke(self, tex):
        # Push the active character back to the input stream as
        # an Other token
        tex.pushToken(Other(self.nodeName.split('::')[-1]))
        # Instantiate a `verb` macro and let it take over the parsing
        # from here.  Also, return its return value.
        return self.ownerDocument.createElement('verb').invoke(tex)
