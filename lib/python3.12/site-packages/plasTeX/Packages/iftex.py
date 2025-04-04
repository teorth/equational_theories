r"""
Partial implementation of the iftex package
See https://ctan.org/pkg/iftex

Provides
 \ifetex, \ifeTeX
to be true

and all the following to be false:

\ifpdftex, \ifPDFTeX
\ifxetex, \ifXeTeX
\ifluatex, \ifLuaTeX
\ifluahbtex, \ifLuaHBTeX
\ifptex, \ifpTeX
\ifuptex, \ifupTeX
\ifptexng, \ifpTeXng
\ifvtex, \ifVTeX
\ifalephtex, \ifAlephTeX
\iftutex, \ifTUTeX
"""

from plasTeX.Base.TeX.Primitives import iftrue, iffalse

class ifetex(iftrue): pass
class ifeTeX(iftrue): pass

class ifpdftex(iffalse): pass
class ifPDFTeX(iffalse): pass

class ifxetex(iffalse): pass
class ifXeTeX(iffalse): pass

class ifluatex(iffalse): pass
class ifLuaTeX(iffalse): pass

class ifluahbtex(iffalse): pass
class ifLuaHBTeX(iffalse): pass

class ifptex(iffalse): pass
class ifpTeX(iffalse): pass

class ifuptex(iffalse): pass
class ifupTeX(iffalse): pass

class ifptexng(iffalse): pass
class ifpTeXng(iffalse): pass

class ifvtex(iffalse): pass
class ifVTeX(iffalse): pass

class ifalephtex(iffalse): pass
class ifAlephTeX(iffalse): pass

class iftutex(iffalse): pass
class ifTUTeX(iffalse): pass
