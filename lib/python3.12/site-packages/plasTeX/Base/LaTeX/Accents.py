"""
C.3.4 Accents and Special Symbols (p173)

"""

from plasTeX import Command
from plasTeX.DOM import Node, Text
from typing import Optional

#
# Table 3.1: Accents
#

class Accent(Command):
    args = 'self'
    chars = {}
    combining = ''
    middle_combining = ''

    @property
    def str(self):
        content = self.textContent.strip()
        if not content:
            return self.macroName or ''
        elif len(content) == 1:
            return type(self).chars.get(content,
                    content[0]+self.combining)
        else:
            return type(self).chars.get(content,
                    content[0]+self.middle_combining+content[1:]+self.combining)

    @property
    def textContent(self):
        """
        We need a customized textContent that doesn't look up
        textContent recursively.

        """
        output = []
        for item in self:
            if item.nodeType == Node.TEXT_NODE:
                output.append(item)
            elif getattr(item, 'str', None) is not None:
                output.append(item.str)
            else:
                output.append(item.textContent)
        if self.ownerDocument is not None:
            return self.ownerDocument.createTextNode(''.join(output))
        else:
            return Text(''.join(output))


class Grave(Accent):
    macroName = '`' # type: Optional[str]
    chars = {
        'A': chr(192),
        'E': chr(200),
        'I': chr(204),
        'O': chr(210),
        'U': chr(217),
        'a': chr(224),
        'e': chr(232),
        'i': chr(236),
        'o': chr(242),
        'u': chr(249),
        'N': chr(504),
        'n': chr(505),
    }
    combining = '\u0300'

class Acute(Accent):
    macroName = "'" # type: Optional[str]
    chars = {
        'A': chr(193),
        'E': chr(201),
        'I': chr(205),
        'O': chr(211),
        'U': chr(218),
        'Y': chr(221),
        'a': chr(225),
        'e': chr(233),
        'i': chr(237),
        'o': chr(243),
        'u': chr(250),
        'y': chr(253),
        'C': chr(262),
        'c': chr(263),
        'L': chr(313),
        'l': chr(314),
        'N': chr(323),
        'n': chr(324),
        'R': chr(340),
        'r': chr(341),
        'S': chr(346),
        's': chr(347),
        'Z': chr(377),
        'z': chr(378),
        'G': chr(500),
        'g': chr(501),
    }
    combining = '\u0300'

class Circumflex(Accent):
    macroName = '^' # type: Optional[str]
    chars = {
        'A': chr(194),
        'E': chr(202),
        'I': chr(206),
        'O': chr(212),
        'U': chr(219),
        'a': chr(226),
        'e': chr(234),
        'i': chr(238),
        'o': chr(244),
        'u': chr(251),
        'C': chr(264),
        'c': chr(265),
        'G': chr(284),
        'g': chr(285),
        'H': chr(292),
        'h': chr(293),
        'J': chr(308),
        'j': chr(309),
        'S': chr(348),
        's': chr(349),
        'W': chr(372),
        'w': chr(373),
        'Y': chr(374),
        'y': chr(375),
        '': '^',
    }

class Umlaut(Accent):
    macroName = '"' # type: Optional[str]
    chars = {
        'A': chr(196),
        'E': chr(203),
        'I': chr(207),
        'O': chr(214),
        'U': chr(220),
        'a': chr(228),
        'e': chr(235),
        'i': chr(239),
        'o': chr(246),
        'u': chr(252),
        'y': chr(255),
        'Y': chr(376),
    }
    combining = '\u030e'

class Tilde(Accent):
    macroName = '~' # type: Optional[str]
    chars = {
        'A': chr(195),
        'N': chr(209),
        'O': chr(213),
        'a': chr(227),
        'n': chr(241),
        'o': chr(245),
        'I': chr(296),
        'i': chr(297),
        'U': chr(360),
        'u': chr(361),
    }
    combining = '\u0303'

class Macron(Accent):
    macroName = '=' # type: Optional[str]
    chars = {
        'A': chr(256),
        'a': chr(257),
        'E': chr(274),
        'e': chr(275),
        'I': chr(298),
        'i': chr(299),
        'O': chr(332),
        'o': chr(333),
        'U': chr(362),
        'u': chr(363),
        'Y': chr(562),
        'y': chr(563),
    }
    combining = '\u0304'

class Dot(Accent):
    macroName = '.' # type: Optional[str]
    chars = {
        'C': chr(266),
        'c': chr(267),
        'E': chr(278),
        'e': chr(279),
        'G': chr(288),
        'g': chr(289),
        'I': chr(304),
        'Z': chr(379),
        'z': chr(380),
        'A': chr(550),
        'a': chr(551),
        'O': chr(558),
        'o': chr(559),
        'B': chr(7682),
        'b': chr(7683),
        'D': chr(7690),
        'd': chr(7691),
        'F': chr(7710),
        'f': chr(7711),
        'H': chr(7714),
        'h': chr(7715),
        'M': chr(7744),
        'm': chr(7745),
        'N': chr(7748),
        'n': chr(7749),
        'P': chr(7766),
        'p': chr(7767),
        'R': chr(7768),
        'r': chr(7769),
        'S': chr(7776),
        's': chr(7777),
        'T': chr(7786),
        't': chr(7787),
        'W': chr(7814),
        'w': chr(7815),
        'X': chr(7818),
        'x': chr(7819),
        'Y': chr(7822),
        'y': chr(7823),
    }
    combining = '\u0307'

class u(Accent):
    chars = {
        'A': chr(258),
        'a': chr(259),
        'E': chr(276),
        'e': chr(277),
        'G': chr(286),
        'g': chr(287),
        'I': chr(300),
        'i': chr(301),
        'O': chr(334),
        'o': chr(335),
        'U': chr(364),
        'u': chr(365),
    }
    combining = '\u0306'

class v(Accent):
    chars = {
        'C': chr(268),
        'c': chr(269),
        'D': chr(270),
        'd': chr(271),
        'E': chr(282),
        'e': chr(283),
        'L': chr(317),
        'l': chr(318),
        'N': chr(327),
        'n': chr(328),
        'R': chr(344),
        'r': chr(345),
        'S': chr(352),
        's': chr(353),
        'T': chr(356),
        't': chr(357),
        'Z': chr(381),
        'z': chr(382),
        'A': chr(461),
        'a': chr(462),
        'I': chr(463),
        'i': chr(464),
        'O': chr(465),
        'o': chr(466),
        'U': chr(467),
        'u': chr(468),
        'G': chr(486),
        'g': chr(487),
        'K': chr(488),
        'k': chr(489),
        'j': chr(496),
        'H': chr(542),
        'h': chr(543),
    }
    combining = '\u030c'

class H(Accent):
    chars = {
        'O': chr(336),
        'o': chr(337),
        'U': chr(368),
        'u': chr(369),
    }
    combining = '\u030b'

class t(Accent):
    chars = {}
    middle_combining = '\u0361'

class c(Accent):
    chars = {
        'C': chr(199),
        'c': chr(231),
        'G': chr(290),
        'g': chr(123),
        'K': chr(310),
        'k': chr(311),
        'L': chr(315),
        'l': chr(316),
        'N': chr(325),
        'n': chr(326),
        'R': chr(342),
        'r': chr(343),
        'S': chr(350),
        's': chr(351),
        'T': chr(354),
        't': chr(355),
        'E': chr(552),
        'e': chr(553),
    }
    combining = '\u0327'

class d(Accent):
    chars = {
        'B': chr(7684),
        'b': chr(7684),
        'D': chr(7692),
        'd': chr(7693),
        'H': chr(7716),
        'h': chr(7717),
        'K': chr(7730),
        'k': chr(7731),
        'L': chr(7734),
        'l': chr(7735),
        'M': chr(7746),
        'm': chr(7747),
        'N': chr(7750),
        'n': chr(7751),
        'R': chr(7770),
        'r': chr(7771),
        'S': chr(7778),
        's': chr(7779),
        'T': chr(7788),
        't': chr(7789),
        'V': chr(7806),
        'v': chr(7807),
        'W': chr(7816),
        'w': chr(7817),
        'Z': chr(7826),
        'z': chr(7827),
        'A': chr(7840),
        'a': chr(7841),
        'E': chr(7864),
        'e': chr(7865),
        'I': chr(7882),
        'i': chr(7883),
        'O': chr(7884),
        'o': chr(7885),
        'U': chr(7908),
        'u': chr(7909),
        'Y': chr(7924),
        'y': chr(7925),
    }
    combining = '\u0323'

class b(Accent):
    chars = {
        'B': chr(7686),
        'b': chr(7687),
        'D': chr(7694),
        'd': chr(7695),
        'K': chr(7732),
        'k': chr(7733),
        'L': chr(7738),
        'l': chr(7739),
        'N': chr(7752),
        'n': chr(7753),
        'R': chr(7774),
        'r': chr(7775),
        'T': chr(7790),
        't': chr(7791),
        'Z': chr(7828),
        'z': chr(7829),
        'h': chr(7830),
    }
    combining = '\u0331'

class k(Accent):
    chars = {
        'A': chr(260),
        'a': chr(261),
        'E': chr(280),
        'e': chr(281),
        'I': chr(302),
        'i': chr(303),
        'U': chr(370),
        'u': chr(371),
        'O': chr(490),
        'o': chr(491),
    }
    combining = '\u0328'

class r(Accent):
    chars = {}
    combining = '\u030a'

#
# Table 3.2: Non-English Symbols (see Characters.py)
#

class Symbol(Command):
    pass

#class oe(Symbol): pass
#class OE(Symbol): pass
#class ae(Symbol): pass
#class AE(Symbol): pass
#class aa(Symbol): pass
#class AA(Symbol): pass
#class o(Symbol): pass
#class O(Symbol): pass
#class l(Symbol): pass
#class L(Symbol): pass
#class ss(Symbol): pass
# ?`
# !`


#
# Special symbols
#

class dag(Symbol):
    str = chr(8224)

class ddag(Symbol):
    str = chr(8225)

class S(Symbol):
    str = chr(167)

class P(Symbol):
    str = chr(182)

class copyright(Symbol):
    str = chr(169)

class pounds(Symbol):
    str = chr(163)
