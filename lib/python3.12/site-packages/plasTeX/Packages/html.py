from plasTeX import Command, IgnoreCommand
from plasTeX.Base.LaTeX.Verbatim import verbatim
from plasTeX.DOM import Text

class htmladdnormallink(Command):
    args = 'self url'
    
class htmladdimg(Command):
    args = 'url'    
    
class rawhtml(verbatim):
    captionable = True
    blockType = False
    def digest(self, tokens):
        verbatim.digest(self, tokens)
        self.str = Text(''.join(self))
        self.str.isMarkup = True
        return []
        
class latexonly(IgnoreCommand):
    args = 'latex:nox'    
    
class htmlonly(Command):
    args = 'self'
    
class latexhtml(Command):
    args = 'latex:nox self'
        
class hyperref(Command):
    args = 'self latexpre:nox latexpost:nox label:idref'    
    
class htmlref(Command):
    args = 'self label:idref'    
    
class externallabels(IgnoreCommand):
    args = 'url labels'
    
class externalref(IgnoreCommand):
    args = 'label'    
    
class segment(IgnoreCommand):
    args = 'file type self'
        
class internal(IgnoreCommand):
    args = '[ type ] prefix'    
    
class startdocument(IgnoreCommand):
    pass

class htmlhead(IgnoreCommand):
    args = 'type self'
    
class htmladdtonavigation(IgnoreCommand):
    args = 'self'