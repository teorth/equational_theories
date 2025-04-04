from plasTeX import Command
from plasTeX.Base.LaTeX.Arrays import Array
from plasTeX.Base.LaTeX.Math import EqnarrayStar, eqnarray
#### Imports Added by Tim ####
from plasTeX.Base.LaTeX.Math import math, MathEnvironmentPre

from plasTeX import Tokenizer
from plasTeX.Logging import getLogger

deflog = getLogger('parse.definitions')

class pmatrix(Array):
    pass

class _AMSEquation(eqnarray):
    pass

class _AMSEquationStar(EqnarrayStar):
    macroName = None

class align(_AMSEquation):
    pass

class AlignStar(_AMSEquationStar):
    macroName = 'align*'

class gather(_AMSEquation):
    pass

class GatherStar(_AMSEquationStar):
    macroName = 'gather*'

class falign(_AMSEquation):
    pass

class FAlignStar(_AMSEquationStar):
    macroName = 'falign*'

class multiline(_AMSEquation):
    pass

class MultilineStar(_AMSEquationStar):
    macroName = 'multiline*'

class alignat(_AMSEquation):
    args = 'column:int'

class AlignatStar(_AMSEquationStar):
    args = 'column:int'
    macroName = 'alignat*'

class split(_AMSEquation):
    pass

#### Added by Tim ####
class EquationStar(_AMSEquationStar):
    macroName = 'equation*'

class aligned(_AMSEquationStar):
    pass

class gathered(MathEnvironmentPre):
    pass

class cases(_AMSEquation):
    pass

class flalign(_AMSEquation):
    pass
class FlalignStar(_AMSEquationStar):
    macroName = 'flalign*'

class subequations(_AMSEquation):
    pass

class xalignat(alignat):
    pass

class multline(multiline):
    pass
class MultlineStar(MultilineStar):
    macroName = 'multline*'

class matrix(Array):
    pass

class vmatrix(Array):
    pass
class Vmatrix(Array):
    pass

class bmatrix(Array):
    pass
class Bmatrix(Array):
    pass

class smallmatrix(Array):
    pass

class dddot(math):
    pass

class ddddot(math):
    pass

class DeclareMathOperator(Command):
    args = '* name:cs definition:nox'
    def invoke(self, tex):
        self.parse(tex)
        a = self.attributes
        if a.get('*modifier*'):
            macro = r'\operatorname*'
        else:
            macro = r'\operatorname'
        definition = [Tokenizer.Token(macro), Tokenizer.Token('{')] + a['definition']+[Tokenizer.Token('}')]
        args = (a['name'], 0, definition)
        deflog.debug('math operator %s %s', *args)
        self.ownerDocument.context.newcommand(*args)


class numberwithin(Command):
    args = 'target:str control:str'

    def invoke(self, tex):
        self.parse(tex)
        control = self.attributes['control']
        target = self.attributes['target']
        ctx = self.ownerDocument.context

        # Resetting
        target_cnt = ctx.counters[target]
        target_cnt.resetby = control

        # Formatting
        ctx['the'+target].format = '{}.${{{}}}'.format(
                ctx['the'+control].format, target)

class eqref(Command):
    args = 'label:idref'
