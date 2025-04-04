r"""
embed package

To use the embed package, include the following code in your latex document.
It will define the HTML environment and the \html command.  The HTML
environment is exactly the same as the comment environment.  The \html
command acts like the \verb command in that it will eat up all content
between two matching characters (e.g., \html+<b>bold text</b>+).  In
plasTeX, the content of both of these macros will appear in the output
document as-is.

\newif\ifplastex\plastexfalse
\ifplastex
    \\usepackage{embed}
\else
    \\usepackage{comment}\excludecomment{HTML}
    \def\html#1{\def\@html##1#1{}\@html}
\fi

Example:

before \html+<span style="color:red">red text</span>+ after

before
\begin{HTML}
<div style="background-color:blue; color:white">
<p>line 1</p>
<p><b>line 2</b></p>
</div>
\end{HTML}
after

"""

from plasTeX.DOM import Text
from plasTeX.Base.LaTeX.Verbatim import verbatim
from plasTeX.Base.LaTeX.Verbatim import verb

class HTML(verbatim):
    captionable = True
    blockType = False
    
    def digest(self, tokens):
        verbatim.digest(self, tokens)
        self.str = Text(''.join(self))
        self.str.isMarkup = True
        return []
    
class XHTML(HTML):
    pass
    
class html(verb):
    args = ''
    
    def digest(self, tokens):
        verb.digest(self, tokens)
        self.str = Text(''.join(self))
        self.str.isMarkup = True
        return []
    
class xhtml(html):
    pass
