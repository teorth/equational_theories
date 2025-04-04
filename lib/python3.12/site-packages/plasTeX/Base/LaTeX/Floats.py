"""
C.9 Figures and Other Floating Bodies (p196)

"""

from plasTeX import Command, Environment
from plasTeX import GlueCommand, DimenCommand
from plasTeX.Base.LaTeX.Arrays import Array


class Caption(Command):
    args = '[ toc ] self'
    blockType = True
    # Is the caption attached to an object?
    attached = False

    def invoke(self, tex):
        res = Command.invoke(self, tex)
        self.title = self.captionName
        return res

#
# C.9.1 Figures and Tables
#

class Float(Environment):
    blockType = True
    forcePars = True
    args = '[ loc:str ]'

    def digest(self, tokens):
        res = Environment.digest(self, tokens)
        # Apply captions to objects
        if self.macroMode == self.MODE_BEGIN:
            # Locate all caption nodes and nodes that are
            # capable of being captioned.
            all = self.allChildNodes
            captions = [x for x in all if isinstance(x, (Caption, Array.caption))]
            objects = [x for x in all if getattr(x, 'captionable', False)]
            # If there is only one caption, apply it to the float
            if len(captions) == 1:
                captions[0].attached = True
                self.title = captions[0]
            # If there are the same number of captions as there are
            # captionable items, apply the captions to the objects.
            if len(captions) == len(objects):
                while captions and objects:
                    captions[0].attached = True
                    objects.pop(0).title = captions.pop(0)
        return res

class figure(Float):
    class caption(Caption):
        counter = 'figure'
        templateName = 'nestedfigurecaption'

class FigureStar(figure):
    macroName = 'figure*'

class table(Float):
    captionable = []
    forcePars = False

    class caption(Caption):
        counter = 'table'
        templateName = 'nestedtablecaption'

    class tabular(Array):
        args = '[ pos:str ] colspec:nox'
        templateName = 'nestedtabular'

    class TabularStar(tabular):
        macroName = 'tabular*'
        args = 'width:dimen [ pos:str ] colspec:nox'
        templateName = 'nestedtabular'

    class tabularx(Array):
        args = 'width:nox colspec:nox'
        templateName = 'nestedtabular'

    class tabulary(Array):
        args = 'width:nox colspec:nox'
        templateName = 'nestedtabular'

class TableStar(table):
    macroName = 'table*'

class suppressfloats(Command):
    pass

# Counters

class topfraction(Command):
    str = '0.25'

class bottomfraction(Command):
    str = '0.25'

class textfraction(Command):
    str = '0.25'

class floatpagefraction(Command):
    str = '0.25'

class dbltopfraction(Command):
    str = '0.25'

class dblfloatpagefraction(Command):
    str = '0.25'

class floatsep(GlueCommand):
    value = GlueCommand.new(0)

class textfloatsep(GlueCommand):
    value = GlueCommand.new(0)

class intextsep(GlueCommand):
    value = GlueCommand.new(0)

class dblfloatsep(GlueCommand):
    value = GlueCommand.new(0)

class dbltextfloatsep(GlueCommand):
    value = GlueCommand.new(0)


#
# C.9.2 Marginal Notes
#

class marginpar(Command):
    args = '[ left ] right'

class reversemarginpar(Command):
    pass

class normalmarginpar(Command):
    pass

# Style Parameters

class marginparpush(DimenCommand):
    value = DimenCommand.new(0)
