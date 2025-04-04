from plasTeX import Command, Environment, log

# Map of CJK encoding names to Python encoding names
encodings = {
    'Bg5': 'big5',
    'GB': '',
    'GBt': '',
    'JIS': 'euc_jp',
    'SJIS': 'shift_jis',
    'KS': '',
    'UTF8': 'utf_8',
}

class CJK(Environment):
    args = '* [ fontencoding ] encoding args'

class CJKchar(Command):
    args = '[ encoding:str ] char1:int char2:int'
    @property
    def str(self):
        a = self.attributes
        enc = encodings[a['encoding'].strip()]
        if not enc:
            log.warning('Unknown encoding: %s' % a['encoding'])
            raise AttributeError('str')
        return str(chr(a['char1'])+chr(a['char2'])).encode(enc)

class Str(Command):
    args = 'char1:int char2:int'
    @property
    def str(self):
        return chr(a['char1'])+chr(a['char2']) 

class CJKcaption(Command):
    args = 'caption:str'

class CKJenc(Command):
    args = 'encoding:str'

class CJKfamily(Command):
    args = 'family:str'

class CJKencfamily(Command):
    args = '[ fontencoding:str ] encoding:str family:str'

class CJKfontenc(Command):
    args = 'encoding:str fontencoding:str'

class CJKkern(Command):
    pass

class CJKglue(Command):
    pass

class CJKtilde(Command):
    pass

class nbs(Command):
    pass

class standardtilde(Command):
    pass

class CJKspace(Command):
    pass

class CJKnospace(Command):
    pass

class CJKhanja(Command):
    pass

class CJKhanjul(Command):
    pass

class CJKtolerance(Command):
    pass

class CJKuppercase(Command):
    pass

class Bg5text(Environment):
    pass

class SJIStext(Environment):
    pass

class CJKCJKchar(Command):
    pass

class CJKhangulchar(Command):
    pass

class CJKlatinchar(Command):
    pass

class CJKbold(Command):
    pass

class CJKnormal(Command):
    pass

class CJKsymbol(Command):
    pass

class CJKsymbols(Command):
    pass

class CJKboldshift(Command):
    pass

class CJKaddEncHook(Command):
    args = 'encoding:str body'
