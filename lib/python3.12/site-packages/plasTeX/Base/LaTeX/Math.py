"""
C.7 Mathematical Formulas (p187)

"""

from plasTeX.Base.LaTeX.Arrays import Array
from plasTeX import Command, Environment, sourceChildren, NoCharSubEnvironment
from plasTeX import DimenCommand, GlueCommand, TeXFragment
from typing import Optional

#
# C.7.1
#

# These space commands are only documented as being available in math mode,
# but it was requested to have them be in the global namespace.

class ThinSpace(Command):
    macroName = '.'
    str = '\u2009'

class NegativeThinSpace(Command):
    macroName = '!'

class MediumSpace(Command):
    macroName = ':'
    str = '\u205f'

class ThickSpace(Command):
    macroName = ';'
    str = '\u2005'

class ThinSpace_(Command):
    macroName = '/'
    str = '\u2009'

class MathEnvironment(NoCharSubEnvironment):
    mathMode = True

    @property
    def mathjax_source(self):
        return mathjax_lt_gt(self.source)

class MathEnvironmentPre(MathEnvironment):
    """
    A math environment whose source property keeps the begin and end markup.
    """
    @property
    def source(self):
        return u"\\begin{{{0}}}{1}\\end{{{0}}}".format(
                self.tagName,
                sourceChildren(self))

# Need \newcommand\({\begin{math}} and \newcommand\){\end{math}}

def mathjax_lt_gt(s: str) -> str:
    """Help mathjax deal with < and >, see http://docs.mathjax.org/en/latest/input/tex/html.html?highlight=lt#html-special-characters."""
    return s.replace('<', r'{\lt}').replace('>', r'{\gt}')

class math(MathEnvironment):
    @property
    def source(self):
        if self.hasChildNodes():
            return u'$%s$' % sourceChildren(self)
        return '$'

    @property
    def mathjax_source(self):
        if self.hasChildNodes():
            s = sourceChildren(self)
            return r'\({}\)'.format(mathjax_lt_gt(s))
        return ''

class displaymath(MathEnvironment):
    blockType = True
    @property
    def source(self):
        if self.hasChildNodes():
            return r'\[ %s \]' % sourceChildren(self)
        if self.macroMode == Command.MODE_END:
            return r'\]'
        return r'\['

class BeginDisplayMath(Command):
    macroName = '['
    def invoke(self, tex):
        o = self.ownerDocument.createElement('displaymath')
        o.macroMode = Command.MODE_BEGIN
        self.ownerDocument.context.push(o)
        return [o]

class EndDisplayMath(Command):
    macroName = ']'
    def invoke(self, tex):
        o = self.ownerDocument.createElement('displaymath')
        o.macroMode = Command.MODE_END
        self.ownerDocument.context.pop(o)
        return [o]

class BeginMath(Command):
    macroName = '('
    disableMath:bool = False
    def invoke(self, tex):
        if self.disableMath:
            return Command.invoke(self,tex)
        o = self.ownerDocument.createElement('math')
        o.macroMode = Command.MODE_BEGIN
        self.ownerDocument.context.push(o)
        return [o]

class EndMath(Command):
    macroName = ')'
    disableMath:bool = False
    def invoke(self, tex):
        if self.disableMath:
            return Command.invoke(self,tex)
        o = self.ownerDocument.createElement('math')
        o.macroMode = Command.MODE_END
        self.ownerDocument.context.pop(o)
        return [o]

class ensuremath(Command):
    """
    Stub for ensuremath. This implementation is extremely wrong and (hopefully)
    emulates the correct behavior only when used with the HTML5 renderer.
    See the unit tests too.
    """
    args = 'self'
    mathMode = True
    @property
    def source(self):
        return sourceChildren(self)

    @property
    def mathjax_source(self):
        if self.hasChildNodes():
            return mathjax_lt_gt(sourceChildren(self))
        return ""

class equation(MathEnvironment):
    blockType = True
    counter = 'equation'

class EqnarrayStar(Array, MathEnvironmentPre, NoCharSubEnvironment):
    macroName = 'eqnarray*' # type: Optional[str]
    blockType = True
    mathMode = True

    class lefteqn(Command):
        args = 'self'
        def digest(self, tokens):
            res = Command.digest(self, tokens)
            obj = self.parentNode
            while obj is not None and not isinstance(obj, Array.ArrayCell):
                obj = obj.parentNode
            if obj is not None:
                obj.attributes['colspan'] = 3
                obj.style['text-align'] = 'left'
            return res

    class ArrayCell(Array.ArrayCell):
        @property
        def source(self):
            return '$\\displaystyle %s $' % sourceChildren(self, par=False)

class eqnarray(EqnarrayStar):
    macroName = None
    counter = 'equation'

    class EndRow(Array.EndRow):
        """ End of a row """
        counter = 'equation'
        def invoke(self, tex):
            res = Array.EndRow.invoke(self, tex)
            res[1].ref = self.ref
            self.ownerDocument.context.currentlabel = res[1]
            return res

    def invoke(self, tex):
        res = EqnarrayStar.invoke(self, tex)
        if self.macroMode == self.MODE_END:
            return res
        res[1].ref = self.ref
        return res
class nonumber(Command):

    def invoke(self, tex):
        self.ownerDocument.context.counters['equation'].addtocounter(-1)

    def digest(self, tokens):
        try:
            row = self.parentNode
            while not isinstance(row, Array.ArrayRow):
                row = row.parentNode
            row.ref = None
        except AttributeError as e:
            print('problem encountered %s' % e)

class notag(nonumber):
    pass

class lefteqn(Command):
    args = 'self'

#
# Style Parameters
#

class jot(DimenCommand):
    value = DimenCommand.new(0)

class mathindent(DimenCommand):
    value = DimenCommand.new(0)


#
# C.7.2 Common Structures
#

# _
# ^
# '

class frac(Command):
    args = 'numer denom'

class sqrt(Command):
    args = '[ n ] self'

class ldots(Command):
    str = '\u2026'

class cdots(Command):
    pass

class vdots(Command):
    pass

class ddots(Command):
    pass

#
# C.7.3 Mathematical Symbols
#

#
# Table 3.3: Greek Letters
#

class MathSymbol(Command):
    pass

# Lowercase
class alpha(MathSymbol): str = chr(945)
class beta(MathSymbol): str = chr(946)
class gamma(MathSymbol): str = chr(947)
class delta(MathSymbol): str = chr(948)
class epsilon(MathSymbol): str = chr(949)
class varepsilon(MathSymbol): str = chr(949)
class zeta(MathSymbol): str = chr(950)
class eta(MathSymbol): str = chr(951)
class theta(MathSymbol): str = chr(952)
class vartheta(MathSymbol): str = chr(977)
class iota(MathSymbol): str = chr(953)
class kappa(MathSymbol): str = chr(954)
class GreekLamda(MathSymbol):
    macroName = 'lambda'
    str = chr(955)
class mu(MathSymbol): str = chr(956)
class nu(MathSymbol): str = chr(957)
class xi(MathSymbol): str = chr(958)
class pi(MathSymbol): str = chr(960)
class varpi(MathSymbol): str = chr(982)
class rho(MathSymbol): str = chr(961)
class varrho(MathSymbol): str = chr(1009)
class sigma(MathSymbol): str = chr(963)
class varsigma(MathSymbol): str = chr(962)
class tau(MathSymbol): str = chr(964)
class upsilon(MathSymbol): str = chr(965)
class phi(MathSymbol): str = chr(966)
class varphi(MathSymbol): str = chr(981)
class chi(MathSymbol): str = chr(967)
class psi(MathSymbol): str = chr(968)
class omega(MathSymbol): str = chr(969)

# Uppercase
class Gamma(MathSymbol): str = chr(915)
class Delta(MathSymbol): str = chr(916)
class Theta(MathSymbol): str = chr(920)
class Lambda(MathSymbol): str = chr(923)
class Xi(MathSymbol): str = chr(926)
class Pi(MathSymbol): str = chr(928)
class Sigma(MathSymbol): str = chr(931)
class Upsilon(MathSymbol): str = chr(978)
class Phi(MathSymbol): str = chr(934)
class Psi(MathSymbol): str = chr(936)
class Omega(MathSymbol): str = chr(8486)


#
# Table 3.4: Binary Operation Symbols
#

class pm(MathSymbol): str = chr(177)
class mp(MathSymbol): str = chr(8723)
class times(MathSymbol): str = chr(215)
class div(MathSymbol): str = chr(247)
class ast(MathSymbol): str = chr(42)
class star(MathSymbol): str = chr(8902)
class circ(MathSymbol): str = chr(9675)
class bullet(MathSymbol): str = chr(8226)
class cdot(MathSymbol): str = chr(183)
class cap(MathSymbol): str = chr(8745)
class cup(MathSymbol): str = chr(8746)
class uplus(MathSymbol): str = chr(8846)
class sqcap(MathSymbol): str = chr(8851)
class sqcup(MathSymbol): str = chr(8852)
class vee(MathSymbol): str = chr(8744)
class wedge(MathSymbol): str = chr(8743)
class setminus(MathSymbol): str = chr(8726)
class wr(MathSymbol): str = chr(8768)
class diamond(MathSymbol): str = chr(8900)
class bigtriangleup(MathSymbol): str = chr(9651)
class bigtriangledown(MathSymbol): str = chr(9661)
class triangleleft(MathSymbol): str = chr(9667)
class triangleright(MathSymbol): str = chr(9657)
class lhd(MathSymbol): pass
class rhd(MathSymbol): pass
class unlhd(MathSymbol): pass
class unrhd(MathSymbol): pass
class oplus(MathSymbol): str = chr(8853)
class ominus(MathSymbol): str = chr(8854)
class otimes(MathSymbol): str = chr(8855)
class oslash(MathSymbol): str = chr(8856)
class odot(MathSymbol): str = chr(8857)
class bigcirc(MathSymbol): str = chr(9711)
class dagger(MathSymbol): str = chr(8224)
class ddagger(MathSymbol): str = chr(8225)
class amalg(MathSymbol): str = chr(8720)

#
# Table 3.5: Relation Symbols
#

class Not(MathSymbol):
    macroName = 'not'
    args = 'symbol'
class leq(MathSymbol): str = chr(8804)
class le(MathSymbol): str = chr(8804)
class prec(MathSymbol): str = chr(8826)
class preceq(MathSymbol): str = chr(8828)
class ll(MathSymbol): str = chr(8810)
class subset(MathSymbol): str = chr(8834)
class subseteq(MathSymbol): str = chr(8838)
class sqsubseteq(MathSymbol): str = chr(8849)
class In(MathSymbol):
    macroName = 'in'
class vdash(MathSymbol): str = chr(8866)
class geq(MathSymbol): str = chr(8805)
class ge(MathSymbol): str = chr(8805)
class succ(MathSymbol): str = chr(8827)
class succeq(MathSymbol): str = chr(8829)
class gg(MathSymbol): str = chr(8811)
class supset(MathSymbol): str = chr(8835)
class supseteq(MathSymbol): str = chr(8839)
class sqsupset(MathSymbol): str = chr(8848)
class sqsupseteq(MathSymbol): str = chr(8850)
class ni(MathSymbol): str = chr(8715)
class dashv(MathSymbol): str = chr(8867)
class equiv(MathSymbol): str = chr(8801)
class sim(MathSymbol): str = chr(8764)
class simeq(MathSymbol): str = chr(8771)
class asymp(MathSymbol): str = chr(8781)
class approx(MathSymbol): str = chr(8776)
class cong(MathSymbol): str = chr(8773)
class neq(MathSymbol): str = chr(8800)
class ne(MathSymbol): str = chr(8800)
class doteq(MathSymbol): str = chr(8784)
class notin(MathSymbol): pass
class models(MathSymbol): str = chr(8871)
class perp(MathSymbol): str = chr(8869)
class mid(MathSymbol): str = chr(8739)
class parallel(MathSymbol): str = chr(8741)
class bowtie(MathSymbol): str = chr(8904)
class Join(MathSymbol): pass
class smile(MathSymbol): str = chr(8995)
class frown(MathSymbol): str = chr(8994)
class propto(MathSymbol): str = chr(8733)

#
# Table 3.6: Arrow Symbols
#

class leftarrow(MathSymbol): str = chr(8592)
class Leftarrow(MathSymbol): str = chr(8656)
class rightarrow(MathSymbol): str = chr(8594)
class Rightarrow(MathSymbol): str = chr(8658)
class leftrightarrow(MathSymbol): str = chr(8596)
class Leftrightarrow(MathSymbol): str = chr(8660)
class mapsto(MathSymbol): str = chr(8614)
class hookleftarrow(MathSymbol): str = chr(8617)
class leftharpoonup(MathSymbol): str = chr(8636)
class leftharpoondown(MathSymbol): str = chr(8637)
class rightleftharpoons(MathSymbol): str = chr(8652)
class longleftarrow(MathSymbol): pass
class Longleftarrow(MathSymbol): pass
class longrightarrow(MathSymbol): pass
class Longrightarrow(MathSymbol): pass
class longleftrightarrow(MathSymbol): pass
class Longleftrightarrow(MathSymbol): pass
class longmapsto(MathSymbol): pass
class hookrightarrow(MathSymbol): str = chr(8618)
class rightharpoonup(MathSymbol): str = chr(8640)
class rightharpoondown(MathSymbol): str = chr(8641)
class leadsto(MathSymbol): pass
class nearrow(MathSymbol): str = chr(8599)
class searrow(MathSymbol): str = chr(8600)
class swarrow(MathSymbol): str = chr(8601)
class nwarrow(MathSymbol): str = chr(8598)

#
# Table 3.7: Miscellaneous Symbols
#

class aleph(MathSymbol): str = chr(8501)
class hbar(MathSymbol): str = chr(8463)
class ell(MathSymbol): str = chr(8467)
class wp(MathSymbol): str = chr(8472)
class Re(MathSymbol): str = chr(8476)
class Im(MathSymbol): str = chr(8465)
class mho(MathSymbol): str = chr(8487)
class prime(MathSymbol): str = chr(8242)
class emptyset(MathSymbol): str = chr(8709)
class nabla(MathSymbol): str = chr(8711)
class surd(MathSymbol): str = chr(8730)
class top(MathSymbol): str = chr(8868)
class bot(MathSymbol): str = chr(8869)
class VerticalBar(MathSymbol):
    macroName = '|'
class forall(MathSymbol): str = chr(8704)
class exists(MathSymbol): str = chr(8707)
class neg(MathSymbol): pass
class flat(MathSymbol): str = chr(9837)
class natural(MathSymbol): str = chr(9838)
class sharp(MathSymbol): str = chr(9839)
class partial(MathSymbol): str = chr(8706)
class infty(MathSymbol): str = chr(8734)
class Box(MathSymbol): pass
class Diamond(MathSymbol): pass
class triangle(MathSymbol): str = chr(9653)
class clubsuit(MathSymbol): str = chr(9827)
class diamondsuit(MathSymbol): str = chr(9830)
class heartsuit(MathSymbol): str = chr(9829)
class spadesuit(MathSymbol): str = chr(9824)

#
# Table 3.8: Variable-sized Symbols
#

class sum(MathSymbol): str = chr(8721)
class prod(MathSymbol): str = chr(8719)
class coprod(MathSymbol): str = chr(8720)
class int(MathSymbol): str = chr(8747)
class oint(MathSymbol): str = chr(8750)
class bigcap(MathSymbol): pass
class bigcup(MathSymbol): pass
class bigsqcup(MathSymbol): pass
class bigvee(MathSymbol): pass
class bigwedge(MathSymbol): pass
class bigodot(MathSymbol): pass
class bigotimes(MathSymbol): pass
class bigoplus(MathSymbol): pass
class biguplus(MathSymbol): pass

#
# Table 3.9: Log-like Functions
#

class Logarithm(MathSymbol):
    macroName = 'log'
class bmod(MathSymbol): pass
class pmod(MathSymbol):
    args = 'self'
class arccos(MathSymbol): pass
class arcsin(MathSymbol): pass
class arctan(MathSymbol): pass
class arg(MathSymbol): pass
class cos(MathSymbol): pass
class cosh(MathSymbol): pass
class cot(MathSymbol): pass
class coth(MathSymbol): pass
class csc(MathSymbol): pass
class deg(MathSymbol): pass
class det(MathSymbol): pass
class dim(MathSymbol): pass
class exp(MathSymbol): pass
class gcd(MathSymbol): pass
class hom(MathSymbol): pass
class inf(MathSymbol): pass
class ker(MathSymbol): pass
class lg(MathSymbol): pass
class lim(MathSymbol): pass
class liminf(MathSymbol): pass
class limsup(MathSymbol): pass
class ln(MathSymbol): pass
class log(MathSymbol): pass
class max(MathSymbol): pass
class min(MathSymbol): pass
class Pr(MathSymbol): pass
class sec(MathSymbol): pass
class sin(MathSymbol): pass
class sinh(MathSymbol): pass
class sup(MathSymbol): pass
class tan(MathSymbol): pass
class tanh(MathSymbol): pass


#
# C.7.4 Arrays (see Arrays.py)
#

#
# C.7.5 Delimiters
#

class AngleReplacingDelimiter(Command):
    """
    Utility classes for delimiter such as `\\big` which
    needs to replace `<` or `>` as arguments by `\\langle` or
    `\\rangle`. Note that people should never write this anyway...
    """
    args = 'char'

    def invoke(self, tex):
        Command.invoke(self, tex)
        if self.attributes['char'].textContent.strip() == '<':
            newarg = TeXFragment()
            newarg.ownerDocument = self.ownerDocument
            newarg.parentNode = self
            newarg.appendChild(langle())
            self.attributes['char'] = newarg
            self.argSource = r'\langle '
        elif self.attributes['char'].textContent == '>':
            newarg = TeXFragment()
            newarg.ownerDocument = self.ownerDocument
            newarg.parentNode = self
            newarg.appendChild(rangle())
            self.attributes['char'] = newarg
            self.argSource = r'\rangle '

class left(AngleReplacingDelimiter): pass

class right(AngleReplacingDelimiter): pass

# Table 3.10: Delimiters and TeXbook (p359)

class Delimiter(Command):
    pass

class langle(Delimiter): pass
class rangle(Delimiter): pass
class lbrace(Delimiter): pass
class rbrace(Delimiter): pass
class lceil(Delimiter): pass
class rceil(Delimiter): pass
class lfloor(Delimiter): pass
class rfloor(Delimiter): pass
class lgroup(Delimiter): pass
class rgroup(Delimiter): pass
class lmoustache(Delimiter): pass
class rmoustache(Delimiter): pass
class uparrow(Delimiter): pass
class Uparrow(Delimiter): pass
class downarrow(Delimiter): pass
class Downarrow(Delimiter): pass
class updownarrow(Delimiter): pass
class Updownarrow(Delimiter): pass
class arrowvert(Delimiter): pass
class Arrowvert(Delimiter): pass
class vert(Delimiter): pass
class Vert(Delimiter): pass
class backslash(Delimiter): pass
class bracevert(Delimiter): pass

class big(AngleReplacingDelimiter): pass
class bigl(AngleReplacingDelimiter): pass
class bigm(Delimiter): pass
class bigr(AngleReplacingDelimiter): pass
class Bigl(AngleReplacingDelimiter): pass
class Bigm(Delimiter): pass
class Bigr(AngleReplacingDelimiter): pass
class biggl(AngleReplacingDelimiter): pass
class biggr(AngleReplacingDelimiter): pass
class Biggl(AngleReplacingDelimiter): pass
class Biggr(AngleReplacingDelimiter): pass
class biggm(Delimiter): pass
class Biggm(Delimiter): pass
class Big(AngleReplacingDelimiter): pass
class bigg(AngleReplacingDelimiter): pass
class Bigg(AngleReplacingDelimiter): pass

class choose(Command):
    pass

class brack(Command):
    pass

class brace(Command):
    pass

#class sqrt(Command):
#    pass

#
# C.7.6 Putting One Thing Above Another
#

class overline(Command):
    args = 'self'

class underline(Command):
    args = 'self'

class overbrace(Command):
    args = 'self'

class underbrace(Command):
    args = 'self'

# Accents

class MathAccent(Command):
    args = 'self'

class hat(MathAccent): pass
class check(MathAccent): pass
class breve(MathAccent): pass
class acute(MathAccent): pass
class grave(MathAccent): pass
class tilde(MathAccent): pass
class bar(MathAccent): pass
class vec(MathAccent): pass
class dot(MathAccent): pass
class ddot(MathAccent): pass

class widehat(MathAccent): pass
class widetilde(MathAccent): pass
class imath(MathAccent): pass
class jmath(MathAccent): pass
class stackrel(MathAccent):
    args = 'top bottom'

#
# C.7.7 Spacing
#

# These are nested inside the MathEnvironemnt


#
# C.7.8 Changing Style
#

# Type Style

class mathrm(Command):
    args = 'self'

class mathop(Command):
    args = 'self'

class mathit(Command):
    args = 'self'

class mathbf(Command):
    args = 'self'

class mathsf(Command):
    args = 'self'

class mathtt(Command):
    args = 'self'

class mathcal(Command):
    args = 'self'

class boldmath(Command):
    pass

class unboldmath(Command):
    pass

class text(Command):
    args = 'self'

# Math Style

class displaystyle(Command):
    pass

class textstyle(Command):
    pass

class scriptstyle(Command):
    pass

class scriptscriptstyle(Command):
    pass
