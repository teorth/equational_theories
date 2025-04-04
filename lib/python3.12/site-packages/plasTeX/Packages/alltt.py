from plasTeX.Tokenizer import Token
from plasTeX import Environment


class alltt(Environment):

    def invoke(self, tex):
        self.ownerDocument.context.push(self)
        esc = self.ownerDocument.context.categories[Token.CC_ESCAPE]
        begin = self.ownerDocument.context.categories[Token.CC_BGROUP]
        end = self.ownerDocument.context.categories[Token.CC_EGROUP]
        self.ownerDocument.context.setVerbatimCatcodes()
        for i in esc:
            self.ownerDocument.context.catcode(i, Token.CC_ESCAPE)
        for i in begin:
            self.ownerDocument.context.catcode(i, Token.CC_BGROUP)
        for i in end:
            self.ownerDocument.context.catcode(i, Token.CC_EGROUP)
        Environment.invoke(self, tex)
        self.ownerDocument.context.pop(self)

