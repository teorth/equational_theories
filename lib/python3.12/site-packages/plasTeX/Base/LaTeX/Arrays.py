"""
C.10.2 The array and tabular Environments

"""

import sys
from plasTeX import Macro, Environment, Command, DimenCommand
from plasTeX import sourceChildren, sourceArguments
from typing import Optional

class ColumnType(Macro):

    columnAttributes = {}
    columnTypes = {}

    def __init__(self, *args, **kwargs):
        Macro.__init__(self, *args, **kwargs)
        self.style.update(self.columnAttributes)

    @classmethod
    def new(cls, name, attributes, args='', 
            before=None, after=None, between=None):
        """
        Generate a new column type definition

        Required Arguments:
        name -- name of the column type
        attributes -- dictionary of style attributes for this column

        Keyword Arguments:
        args -- argument description string
        before -- tokens to insert before this column
        after -- tokens to insert after this column

        """
        newclass = type(name, (cls,),
            {'columnAttributes':attributes, 'args':args,
             'before': before or [], 
             'after': after or [], 
             'between': between or []})
        cls.columnTypes[name] = newclass

    def __repr__(self):
        return '%s: %s' % (type(self).__name__, self.style)

ColumnType.new('r', {'text-align':'right'})
ColumnType.new('R', {'text-align':'right'})
ColumnType.new('c', {'text-align':'center'})
ColumnType.new('C', {'text-align':'center'})
ColumnType.new('l', {'text-align':'left'})
ColumnType.new('L', {'text-align':'left'})
ColumnType.new('J', {'text-align':'left'})
ColumnType.new('X', {'text-align':'left'})
ColumnType.new('p', {'text-align':'left'}, args='width:str')
ColumnType.new('d', {'text-align':'right'}, args='delim:str')


class Array(Environment):
    """
    Base class for all array-like structures

    """

    colspec = None
    blockType = True
    captionable = True

    class caption(Command):
        """ Table caption """
        args = '* [ toc ] self'
        labelable = True
        counter = 'table' # type: Optional[str]
        blockType = True
        def invoke(self, tex):
            res = Command.invoke(self, tex)
            self.title = self.captionName
            return res

    class CellDelimiter(Command):
        """ Cell delimiter """
        macroName = 'active::&'
        def invoke(self, tex):
            # Pop and push a new context for each cell, this keeps
            # any formatting changes from the previous cell from
            # leaking over into the next cell
            self.ownerDocument.context.pop()
            self.ownerDocument.context.push()
            # Add a phantom cell to absorb the appropriate tokens
            return [self, self.ownerDocument.createElement('ArrayCell')]

    class EndRow(Command):
        """ End of a row """
        macroName = '\\' # type: Optional[str]
        args = '* [ space ]' # type: str

        def invoke(self, tex):
            # Pop and push a new context for each row, this keeps
            # any formatting changes from the previous row from
            # leaking over into the next row
            self.ownerDocument.context.pop()
            self.parse(tex)
            self.ownerDocument.context.push()
            # Add a phantom row and cell to absorb the appropriate tokens
            return [self, self.ownerDocument.createElement('ArrayRow'),
                          self.ownerDocument.createElement('ArrayCell')]

    class cr(EndRow):
        macroName = None
        args = ''

    class tabularnewline(EndRow):
        macroName = None
        args = ''

    class BorderCommand(Command):
        """
        Base class for border commands

        """
        BORDER_BEFORE = 0
        BORDER_AFTER  = 1

        position = BORDER_BEFORE

        def applyBorders(self, cells, location=None):
            """
            Apply borders to the given cells

            Required Arguments:
            location -- place where the border should be applied.
                This should be 'top', 'bottom', 'left', or 'right'
            cells -- iterable containing cell instances to apply
                the borders

            """
            # Find out if the border should start and stop, or just
            # span the whole table.
            a = self.attributes
            if a and 'span' in list(a.keys()):
                try: start, end = a['span']
                except TypeError: start = end = a['span']
            else:
                start = -sys.maxsize
                end = sys.maxsize
            # Determine the position of the border
            if location is None:
                location = self.locations[self.position]
            colnum = 1
            for cell in cells:
                if colnum < start or colnum > end:
                    colnum += 1
                    continue
                cell.style['border-%s-style' % location] = 'solid'
                cell.style['border-%s-color' % location] = 'black'
                cell.style['border-%s-width' % location] = '1px'
                if cell.attributes:
                    colnum += cell.attributes.get('colspan', 1)
                else:
                    colnum += 1

    class hline(BorderCommand):
        """ Full horizontal line """
        locations = ('top','bottom')

    class vline(BorderCommand):
        """ Vertical line """
        locations = ('left','right')

    #
    # booktabs commands
    #

    class cline(hline):
        """ Partial horizontal line """
        args = 'span:list(-):int'

    class _rule(hline):
        """ Full horizontal line """
        args = '[ width:str ]'

    class toprule(_rule):
        pass

    class midrule(_rule):
        pass

    class bottomrule(_rule):
        pass

    class cmidrule(cline):
        args = '[ width:str ] ( trim:str ) span:list(-):int'

    class morecmidrules(Command):
        pass

    class addlinespace(Command):
        args = '[ width:str ]'

    class specialrule(Command):
        args = 'width:str above:str below:str'

    # end booktabs

    class ArrayRow(Macro):
        """ Table row class """
        endToken = None

        def digest(self, tokens):
            # Absorb tokens until the end of the row
            self.endToken = self.digestUntil(tokens, Array.EndRow)
            if self.endToken is not None:
                next(tokens)
                self.endToken.digest(tokens)

        @property
        def source(self):
            """
            This source property is a little different than most.
            Instead of printing just the source of the row, it prints
            out the entire environment with just this row as its content.
            This allows renderers to render images for arrays a row
            at a time.

            """
            name = self.parentNode.nodeName or 'array'
            escape = '\\'
            s = []
            argSource = sourceArguments(self.parentNode)
            if not argSource:
                argSource = ' '
            s.append('%sbegin{%s}%s' % (escape, name, argSource))
            for cell in self:
                s.append(sourceChildren(cell, par=not(self.parentNode.mathMode)))
                if cell.endToken is not None:
                    s.append(cell.endToken.source)
            if self.endToken is not None:
                s.append(self.endToken.source)
            s.append('%send{%s}' % (escape, name))
            return ''.join(s)

        def applyBorders(self, tocells=None, location=None):
            """
            Apply borders to every cell in the row

            Keyword Arguments:
            row -- the row of cells to apply borders to.  If none
               is given, then use the current row

            """
            if tocells is None:
                tocells = self
            for cell in self:
                horiz, vert = cell.borders
                # Horizontal borders go across all columns
                for border in horiz:
                    border.applyBorders(tocells, location=location)
                # Vertical borders only get applied to the same column
                for applyto in tocells:
                    for border in vert:
                        border.applyBorders([applyto], location=location)

        @property
        def isBorderOnly(self):
            """ Does this row exist only for applying borders? """
            for cell in self:
                if not cell.isBorderOnly:
                    return False
            return True

    class ArrayCell(Macro):
        """ Table cell class """
        endToken = None
        isHeader = False

        def digest(self, tokens):
            self.endToken = self.digestUntil(tokens, (Array.CellDelimiter,
                                                      Array.EndRow))
            if isinstance(self.endToken, Array.CellDelimiter):
                next(tokens)
                self.endToken.digest(tokens)
            else:
                self.endToken = None

            # Check for multicols
            hasmulticol = False
            for item in self:
                if item.attributes and 'colspan' in list(item.attributes.keys()):
                    self.attributes['colspan'] = item.attributes['colspan']
                if hasattr(item, 'colspec') and not isinstance(item, Array):
                    self.colspec = item.colspec
                if hasattr(item, 'isHeader'):
                    self.isHeader = item.isHeader

            # Cache the border information.  This must be done before
            # grouping paragraphs since a paragraph might swallow
            # an hline/vline/cline command.
            h,v = self.borders

            # Throw out the border commands, we're done with them
#           for i in range(len(self)-1, -1, -1):
#               if isinstance(self[i], Array.BorderCommand):
#                   self.pop(i)

            self.paragraphs()

        @property
        def borders(self):
            """
            Return all of the border control macros

            Returns:
            list of border command instances

            """
            # Use cached version if it exists
            if hasattr(self, '@borders'):
                return getattr(self, '@borders')

            horiz, vert = [], []

            # Locate the border control macros at the end of the cell
            for i in range(len(self)-1, -1, -1):
                item = self[i]
                if item.isElementContentWhitespace:
                    continue
                if isinstance(item, Array.hline):
                    item.position = Array.hline.BORDER_AFTER
                    horiz.append(item)
                    continue
                elif isinstance(item, Array.vline):
                    item.position = Array.vline.BORDER_AFTER
                    vert.append(item)
                    continue
                break

            # Locate border control macros at the beginning of the cell
            for item in self:
                if item.isElementContentWhitespace:
                    continue
                if isinstance(item, Array.hline):
                    item.position = Array.hline.BORDER_BEFORE
                    horiz.append(item)
                    continue
                elif isinstance(item, Array.vline):
                    item.position = Array.vline.BORDER_BEFORE
                    vert.append(item)
                    continue
                break

            setattr(self, '@borders', (horiz, vert))

            return horiz, vert


        @property
        def isBorderOnly(self):
            """ Does this cell exist only for applying borders? """
            for par in self:
                for item in par:
                    if item.isElementContentWhitespace:
                        continue
                    elif isinstance(item, Array.BorderCommand):
                        continue
                    return False
            return True


        @property
        def source(self):
            # Don't put paragraphs into math mode arrays
            if self.parentNode is None:
               # no parentNode, assume mathMode==False
               return sourceChildren(self, True)
            return sourceChildren(self,
                       par=not(self.parentNode.parentNode.mathMode))



    class multicolumn(Command):
        """ Column spanning cell """
        args = 'colspan:int colspec:nox self'
        isHeader = False

        def invoke(self, tex):
            Command.invoke(self, tex)
            self.colspec = Array.compileColspec(tex, self.attributes['colspec']).pop(0)

        def digest(self, tokens):
            Command.digest(self, tokens)
            #self.paragraphs()


    def invoke(self, tex):
        if self.macroMode == Macro.MODE_END:
            self.ownerDocument.context.pop(self) # End of table, row, and cell
            return

        Environment.invoke(self, tex)

#!!!
#
# Need to handle colspec processing here so that tokens that must
# be inserted before and after columns are known
#
#!!!
        if 'colspec' in list(self.attributes.keys()):
            self.colspec = Array.compileColspec(tex, self.attributes['colspec'])

        self.ownerDocument.context.push() # Beginning of cell
        # Add a phantom row and cell to absorb the appropriate tokens
        return [self, self.ownerDocument.createElement('ArrayRow'),
                      self.ownerDocument.createElement('ArrayCell')]

    def digest(self, tokens):
        Environment.digest(self, tokens)

        # Give subclasses a hook before going on
        self.processRows()

        self.applyBorders()

        self.linkCells()

    def processRows(self):
        """
        Subcloss hook to process rows after digest

        Tables are fairly complex structures, so subclassing them
        in a useful way can be difficult.  This method was added
        simply to allow subclasses to have access to the content of a
        table immediately after the digest method.

        """

    def linkCells(self):
        """
        Add attributes to spanning cells to indicate their start and end points

        This information is added mainly for DocBook's table model.
        It does spans by indicating the starting and ending points within
        the table rather than just saying how many columns are spanned.

        """
        # Link cells to colspec
        if self.colspec:
            for r, row in enumerate(self):
                for c, cell in enumerate(row):
                    colspan = cell.attributes.get('colspan', 0)
                    if colspan > 1:
                        try:
                            cell.colspecStart = self.colspec[c]
                            cell.colspecEnd = self.colspec[c+colspan-1]
                        except IndexError:
                            if hasattr(cell, 'colspecStart'):
                                del cell.colspecStart
                            if hasattr(cell, 'colspecEnd'):
                                del cell.colspecEnd

        # Determine the number of rows by counting cells
        if self:
            cols = []
            for row in self:
                numcols = 0
                for cell in row:
                    numcols += cell.attributes.get('colspan', 1)
                cols.append(numcols)
            self.numCols = max(cols)

    def applyBorders(self):
        """
        Apply borders from \\(h|c|v)line and colspecs

        """
        lastrow = len(self) - 1
        emptyrows = []
        prev = None
        for i, row in enumerate(self):
            if not isinstance(row, Array.ArrayRow):
                continue
            # If the row is only here to apply borders, apply the
            # borders to the adjacent row.  Empty rows are deleted later.
            if row.isBorderOnly:
                if i == 0 and lastrow:
                    row.applyBorders(self[1], 'top')
                elif prev is not None:
                    row.applyBorders(prev, 'bottom')
                emptyrows.insert(0, i)
            else:
                row.applyBorders()
                if self.colspec:
                    # Expand multicolumns so that they don't mess up
                    # the colspec attributes
                    cells = []
                    for cell in row:
                        span = 1
                        if cell.attributes:
                            span = cell.attributes.get('colspan', 1)
                        cells += [cell] * span
                    for spec, cell in zip(self.colspec, cells):
                        spec = getattr(cell, 'colspec', spec)
                        cell.style.update(spec.style)
                prev = row

        # Pop empty rows
        for i in emptyrows:
            self.pop(i)

    @classmethod
    def compileColspec(cls, tex, colspec):
        """
        Compile colspec into an object

        Required Arguments:
        colspec -- an unexpanded token list that contains a LaTeX colspec

        Returns:
        list of `ColumnType` instances

        """
        output = []
        colspec = iter(colspec)
        before = None
        leftborder = None

        tex.pushToken(Array)
        tex.pushTokens(colspec)

        for tok in tex.itertokens():
            if tok is Array:
                break

            if tok.isElementContentWhitespace:
                continue

            if tok == '|':
                if not output:
                    leftborder = True
                else:
                    output[-1].style['border-right'] = '1px solid black'
                continue

            if tok == '>':
                before = tex.readArgument()
                continue

            if tok == '<':
                output[-1].after = tex.readArgument()
                continue

            if tok == '@':
                if output:
                    output[-1].between = tex.readArgument()
                continue

            if tok == '*':
                num = tex.readArgument(type=int, expanded=True)
                spec = tex.readArgument()
                for i in range(num):
                    tex.pushTokens(spec)
                continue

            output.append(ColumnType.columnTypes.get(tok, ColumnType)())

            if tok.lower() in ['p','d']:
                tex.readArgument()

            if before:
                output[-1].before = before
                before = None

        if leftborder:
            output[0].style['border-left'] = '1px solid black'

        return output

    @property
    def source(self):
        """
        This source property is a little different than most.
        Instead of calling the source property of the child nodes,
        it walks through the rows and cells manually.  It does
        this because rows and cells have special source properties
        as well that don't return the correct markup for inserting
        into this source property.

        """
        name = self.nodeName
        escape = '\\'
        # \begin environment
        # If self.childNodes is not empty, print out the entire environment
        if self.macroMode == Macro.MODE_BEGIN:
            s = []
            argSource = sourceArguments(self)
            if not argSource:
                argSource = ' '
            s.append('%sbegin{%s}%s' % (escape, name, argSource))
            if self.hasChildNodes():
                for row in self:
                    for cell in row:
                        s.append(sourceChildren(cell, par=not(self.mathMode)))
                        if cell.endToken is not None:
                            s.append(cell.endToken.source)
                    if row.endToken is not None:
                        s.append(row.endToken.source)
                s.append('%send{%s}' % (escape, name))
            return ''.join(s)

        # \end environment
        if self.macroMode == Macro.MODE_END:
            return '%send{%s}' % (escape, name)

class array(Array):
    args = '[ pos:str ] colspec:nox'
    mathMode = True
    class nonumber(Command):
        pass

class tabular(Array):
    args = '[ pos:str ] colspec:nox'

class TabularStar(tabular):
    macroName = 'tabular*'
    args = 'width:dimen [ pos:str ] colspec:nox'

class tabularx(Array):
    args = 'width:nox colspec:nox'

class tabulary(Array):
    args = 'width:nox colspec:nox'

# Style Parameters

class arraycolsep(DimenCommand):
    value = DimenCommand.new(0)

class tabcolsep(DimenCommand):
    value = DimenCommand.new(0)

class arrayrulewidth(DimenCommand):
    value = DimenCommand.new(0)

class doublerulesep(DimenCommand):
    value = DimenCommand.new(0)

class arraystretch(Command):
    str = '1'
