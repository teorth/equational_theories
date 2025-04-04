"""
C.6.2 List-Making Environments
C.6.3 The list and trivlist Enviroments

"""

from plasTeX import Environment, Command, DimenCommand

class enuminame(Command): str = ''
class enumiiname(Command): str = ''
class enumiiiname(Command): str = ''
class enumivname(Command): str = ''

class List(Environment):
    """ Base class for all list-based environments """
    depth = 0
    counters = ['enumi','enumii','enumiii','enumiv']
    blockType = True

    class item(Command):
        args = '[ term ]'
        counter = 'enumi'
        position = 0
        forcePars = True

        def invoke(self, tex):
            """ Set up counter for this list depth """
            try:
                self.counter = List.counters[List.depth-1]
                self.position = self.ownerDocument.context.counters[self.counter].value + 1
            except (KeyError, IndexError):
                pass
            return Command.invoke(self, tex)

        def digest(self, tokens):
            """
            Items should absorb all of the content within that 
            item, not just the `[...]' argument.  This is 
            more useful for the resulting document object.

            """
            for tok in tokens:
                if tok.isElementContentWhitespace:
                    continue
                tokens.push(tok)
                break
            self.digestUntil(tokens, List.item)
            if self.forcePars:
                self.paragraphs()

    def invoke(self, tex):
        """ Set list nesting depth """
        if self.macroMode != Environment.MODE_END:
            List.depth += 1
        else:
            List.depth -= 1
        try:
            for i in range(List.depth, len(List.counters)):
                self.ownerDocument.context.counters[List.counters[i]].setcounter(0)
        except (IndexError, KeyError):
            pass
        return Environment.invoke(self, tex)

    def digest(self, tokens):
        if self.macroMode != Environment.MODE_END:
            # Drop any whitespace before the first item
            for tok in tokens:
                if tok.isElementContentWhitespace:
                    continue
                elif tok.nodeName == 'setcounter':
                    tok.digest([])
                    continue
#               if tok.nodeName != 'item':
#                   log.warning('dropping non-item from beginning of list')
#                   continue
                tokens.push(tok)
                break
        Environment.digest(self, tokens) 

#
# Counters -- enumi, enumii, enumiii, enumiv
#            

# C.6.2
    
class itemize(List): 
    pass

class labelitemi(Command):
    pass
class labelitemii(Command):
    pass
class labelitemiii(Command):
    pass
class labelitemiv(Command):
    pass

class enumerate_(List): 
    macroName = 'enumerate'
    args = '[ type ]'  # Actually defined in the enumerate package, but it doesn't hurt

class description(List): 
    pass

# C.6.3

class trivlist(List): 
    pass

class ConfigurableList(List):
    macroName = 'list'
    args = 'defaultlabel decls:nox'

class topsep(DimenCommand):
    value = DimenCommand.new(0)

class partopsep(DimenCommand):
    value = DimenCommand.new(0)

class itemsep(DimenCommand):
    value = DimenCommand.new(0)

class parsep(DimenCommand):
    value = DimenCommand.new(0)

class leftmargin(DimenCommand):
    value = DimenCommand.new(0)

class rightmargin(DimenCommand):
    value = DimenCommand.new(0)

class listparindent(DimenCommand):
    value = DimenCommand.new(0)

class itemindent(DimenCommand):
    value = DimenCommand.new(0)

class labelsep(DimenCommand):
    value = DimenCommand.new(0)

class labelwidth(DimenCommand):
    value = DimenCommand.new(0)

class makelabel(Command):
    args = 'label'

class usecounter(Command):
    args = 'name:str'
