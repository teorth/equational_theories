from plasTeX.Base.LaTeX.Arrays import tabular
from plasTeX import Command, DimenCommand, CountCommand, GlueCommand 
from plasTeX import dimen, glue, count

class LTleft(GlueCommand): value = glue('1fil')
class LTright(GlueCommand): value = glue('1fil')
class LTpre(GlueCommand): value = glue('1fil')
class LTpost(GlueCommand): value = glue('1fil')
class LTchunksize(CountCommand): value = count(20)

class setlongtables(Command): pass

class longtable(tabular):
    args = '[ position:str ] colspec:nox'

    class caption(tabular.caption):
        def digest(self, tokens):
            tabular.caption.digest(self, tokens)
            node = self.parentNode

            # Mark caption row to be moved later
            while not isinstance(node, tabular.ArrayRow):
               node = node.parentNode
            if node is not None:
                node.isCaptionRow = True

            # Attach caption to longtable node in case it is needed
            while not isinstance(node, longtable):
               node = node.parentNode
            if node is not None and getattr(node, 'title', None) is None:
                node.title = self

    class nocountcaption(caption):
        """ Caption that doesn't increment the counter """
        counter = None

    class tabularnewline(Command): pass

    class LongTableEndRow(tabular.EndRow):
        args = ''
        macroName = None
        digested = False
        def digest(self, tokens):
            if self.digested:
                return

            tabular.EndRow.digest(self, tokens)

            # Push the instance into the stream a second time.
            # This will be used in longtable.digest() to split out
            # the header and footer chunks.
            tokens.push(self)

            self.digested = True

    class endhead(LongTableEndRow):
        """ End of head section """

    class endfirsthead(LongTableEndRow):
        """ End of first head section """
        def invoke(self, tex):
            # Store the current table counter value.  If more than one
            # caption exists, we need to set this counter back to this value.
            self._tabularcount = self.ownerDocument.context.counters[longtable.caption.counter].value
            return longtable.LongTableEndRow.invoke(self, tex)

    class endfoot(LongTableEndRow):
        """ End of footer section """

    class endlastfoot(LongTableEndRow):
        """ End of last footer section """

    class kill(LongTableEndRow):
        """ Throw-away row used for measurement """
        def digest(self, tokens):
            longtable.LongTableEndRow.digest(self, tokens)
            node = self.parentNode
            while node is not None and not isinstance(node, longtable):
                node = node.parentNode
            if node is not None:
                node[-1].isKillRow = True

    def processRows(self):
        # Strip header and footer chunks from the table
        delims = [x for x in self if isinstance(x, type(self).EndRow)]
        delims = [x for x in delims if not isinstance(x, type(self).kill)] 
        header = footer = None
        for current in delims:
            cache = []
            while 1:
                node = self.pop(0)
                if current is node:
                    if isinstance(current, type(self).endhead):
                        if header is None:
                            header = cache
                    elif isinstance(current, type(self).endfirsthead):
                        header = cache
                        # Set counter back to correct value in case there
                        # were multiple captions.
                        self.ownerDocument.context.counters[longtable.caption.counter].setcounter(node._tabularcount)
                    elif isinstance(current, type(self).endfoot):
                        if footer is None:
                            footer = cache
                    elif isinstance(current, type(self).endlastfoot):
                        footer = cache
                    break
                else:
                    cache.append(node)

        # Re-insert only the first header and last footer
        if header is not None:
            header.reverse()
            for item in header:
                for cell in item:
                    cell.isHeader = True
                self.insert(0, item)

        if footer is not None:
            for item in footer:
                for cell in item:
                    cell.isHeader = True
                self.append(item)

        # Move caption before the longtable, and delete killed rows
        removeRows = []
        for i, row in enumerate(self):
           if getattr(row, 'isCaptionRow', None):
               #while row.childNodes:
               #    cell = row.pop(0)
               #    while cell.childNodes:
               #        para = cell.pop(0)
               #        while para.childNodes:
               #           self.parentNode.append(para.pop(0))
               removeRows.insert(0,i)
           elif getattr(row, 'isKillRow', None):
               removeRows.insert(0,i)
        for i in removeRows:
            self.pop(i)

class LongTableStar(longtable):
    macroName = 'longtable*'
