"""
These macros are actually taken from the T1 font encoding package, but 
I figure that it wouldn't hurt to put them all in by default.

"""

from plasTeX import Command

class ding(Command):
    args = 'self'
    values = {}
    @property
    def str(self):
        if int(self.textContent.strip()) in type(self).values:
            return type(self).values[int(self.textContent)]

class textogonekcentered(Command):
    str = chr(731)

class textperthousand(Command):
    str = chr(8240)

class textpertenthousand(Command):
    str = chr(8241)

class textasciicircum(Command):
    str = '^'

class textasciitilde(Command):
    str = '~'

class textbackslash(Command):
    str = '\\'

class textbar(Command):
    str = '|'

class textbraceleft(Command):
    str = '{'

class textbraceright(Command):
    str = '}'

class textcompwordmark(Command): pass

class textdollar(Command):
    str = '$'

class textemdash(Command):
    str = chr(8212)

class textendash(Command):
    str = chr(8211)

class textexclamdown(Command):
    str = chr(161)

class textgreater(Command):
    str = '>'

class textless(Command):
    str = '<'

class textquestiondown(Command):
    str = chr(191)

class textquotedblleft(Command):
    str = chr(8220)

class textquotedblright(Command):
    str = chr(8221)

class textquotedbl(Command):
    str = '"'

class textquoteright(Command):
    str = chr(8217)

class textquoteleft(Command):
    str = chr(8216)

class textsection(Command):
    str = chr(167)

class textsterling(Command): pass

class textunderscore(Command):
    str = '_'

class textvisiblespace(Command):
    str = chr(160)

class texttrademark(Command):
   str = chr(8482)

class textregistered(Command):
   str = chr(174)

class textcopyright(Command):
   str = chr(169)

class AE(Command):
    str = chr(198)

class DH(Command):
    str = chr(272)

class DJ(Command):
    str = chr(272)

class L(Command):
    str = chr(321)

class NG(Command):
    str = chr(330)

class OE(Command):
    str = chr(338)

class O(Command):
    str = chr(216)

class SS(Command):
    str = chr(223)

class TH(Command):
    str = chr(222)

class ae(Command):
    str = chr(230)

class dh(Command): pass

class dj(Command):
    str = chr(273)

class guillmotleft(Command):
    str = chr(171)

class guillemotright(Command):
    str = chr(187)

class guilsinglleft(Command):
    str = chr(8249)

class guilsinglright(Command):
    str = chr(8250)

class i(Command):
    str = chr(305)

class j(Command): pass

class l(Command):
    str = chr(322)

class ng(Command):
    str = chr(331)

class oe(Command):
    str = chr(339)

class o(Command):
    str = chr(248)

class quotedblbase(Command):
    str = chr(8222)

class quotesinglbase(Command):
    str = chr(8218)

class ss(Command):
    str = 'SS'

class th(Command):
    str = chr(254)
