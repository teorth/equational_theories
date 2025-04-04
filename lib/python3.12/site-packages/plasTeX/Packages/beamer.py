from plasTeX import Command, Environment
from plasTeX.Base import textbf, textit, textsl, textrm, textsf
from plasTeX.Base import List, label, newcommand, newenvironment
from plasTeX.Base import renewcommand, renewenvironment
from plasTeX.Base import itemize, enumerate_, description
from plasTeX.Base import part, section, subsection, subsubsection
from plasTeX.Base import tableofcontents, thebibliography
from plasTeX.Base import abstract, verse, quotation, quote, footnote, footnotetext
from plasTeX.Packages.color import color
from plasTeX.Packages.graphicx import includegraphics
from plasTeX.Packages.hyperref import hypertarget, hyperlink
from plasTeX.Packages.article import *

class frame(Command):
    args = '< overlay > self'
    subtitle = None

    def invoke(self, tex):
        # This macro can be an environment or a command each 
        # with different arguments.
        if self.macroMode == Command.MODE_BEGIN or \
           self.macroMode == Command.MODE_END:
            f = self.ownerDocument.createElement('frameenv')
            f.parentNode = self.parentNode
            f.macroMode = self.macroMode
            f.invoke(tex)
            # Add to frames collection
            if self.macroMode == Command.MODE_BEGIN:
                f.addToFrames()
            return [f]
        # Add to frames collection
        self.addToFrames()
        return Command.invoke(self, tex)

    def addToFrames(self):
        """ Add this frame to the frame collection """
        u = self.ownerDocument.userdata
        frames = u.get('frames')
        if frames is None:
            frames = []
            u['frames'] = frames
        frames.append(self) 

class frameenv(Environment):
    args = '< overlay > < defaultoverlay > [ options:dict ] { title } { subtitle }'
    subtitle = None
    forcePars = True

    def addToFrames(self):
        """ Add this frame to the frame collection """
        u = self.ownerDocument.userdata
        frames = u.get('frames')
        if frames is None:
            frames = []
            u['frames'] = frames
        frames.append(self) 

class frametitle(Command):
    args = '< overlay > [ shorttitle ] self'
    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['frames'][-1].title = self

class framesubtitle(Command):
    args = '< overlay > self'
    def invoke(self, tex):
        Command.invoke(self, tex)
        self.ownerDocument.userdata['frames'][-1].subtitle = self

class setbeamertemplate(Command):
    args = '< overlay > theme [ options ] [ suboptions ]'

class setbeamersize(Command):
    args = 'options:dict'

class logo(Command):
    args = '< overlay > self'

class setbeamercolor(Command):
    args = 'mode color'

class pause(Command):
    args = '[ number:int ]'

class onslide(Command):
    args = '*+ < overlay > { self }'

class only(Command):
    args = '< overlay > self < overlay2 >'

class onlyenv(Environment):
    args = '< overlay >'

class uncover(Command):
    args = '< overlay > self'

class uncoverenv(Environment):
    args = uncover.args

class visible(Command):
    args = '< overlay > self'

class visibleenv(Environment):
    args = visible.args

class invisible(Command):
    args = '< overlay > self'

class invisibleenv(Environment):
    args = invisible.args

class alt(Command):
    args = '< overlay > default alternative < overlay2 >'

class altenv(Environment):
    args = '< overlay > begin end alternatebegin alternate end < overlay2 >'

class temporal(Command):
    args = '< overlay > before default after'

class alert(Command):
    args = '< overlay > self'

class overlayarea(Environment):
    args = 'width height'

class overprint(Environment):
    args = 'width'

List.item.args = '< alert >' + List.item.args + '< alert2 >'
textbf.args = '< overlay >' + textbf.args
textit.args = '< overlay >' + textit.args
textsl.args = '< overlay >' + textsl.args
textrm.args = '< overlay >' + textrm.args
textsf.args = '< overlay >' + textsf.args
color.args = '< overlay >' + color.args
label.args = '< overlay >' + label.args
includegraphics.args = '< overlay >' + includegraphics.args
newcommand.args = '< overlay >' + newcommand.args
renewcommand.args = '< overlay >' + renewcommand.args
newenvironment.args = '< overlay >' + newenvironment.args
renewenvironment.args = '< overlay >' + renewenvironment.args
itemize.args = '[ overlay ]'
enumerate_.args = '[ overlay ] [ template ]'
description.args = '[ overlay ] [ longtext ]'
section.args = '< overlay >' + section.args
subsection.args = '< overlay >' + subsection.args
subsubsection.args = '< overlay >' + subsubsection.args
part.args = '< overlay >' + part.args
thebibliography.bibitem.args = '< overlay >' + thebibliography.bibitem.args
appendix.args = '< overlay >' + appendix.args
hypertarget.args = '< overlay >' + hypertarget.args
hyperlink.args = '< overlay >' + hyperlink.args + '< overlay2 >'
tableofcontents.args = '[ options:dict ]' + tableofcontents.args
abstract.args = '< overlay >' + abstract.args
verse.args = '< overlay >' + verse.args
quotation.args = '< overlay >' + quotation.args
quote.args = '< overlay >' + quote.args
footnote.args = '< overlay > [ options:dict ] self' # modify options int -> dict
footnotetext.args = '< overlay > [ options:dict ] self' # modify options int -> dict

class resetcounteronoverlays(Command):
    args = 'counter'

class resetcountonoverlays(Command):
    args = 'count'

class action(Command):
    args = '< action > self'

class actionenv(Environment):
    args = '< action >'

class beamerdefaultoverlayspecification(Command):
    args = 'overlay'

class AtBeginSection(Command):
    args = '[ special ] text'

class AtBeginSubsection(AtBeginSection):
    pass

class AtBeginSubsubsection(AtBeginSection):
    pass

class partpage(Command):
    pass

class AtBeginPart(Command):
    args = 'text'

class lecture(Command):
    args = '[ shorttitle ] title { label }'

class includeonlylecture(Command):
    args = 'label'

class AtBeginLecture(Command):
    args = 'text'

class beamerbutton(Command):
    args = 'self'

class beamergotobutton(Command):
    args = 'self'

class beamerskipbutton(Command):
    args = 'self'

class beamerreturnbutton(Command):
    args = 'self'

class HyperlinkCommand(Command):
    args = '< overlay > self < overlay2 >'

class hyperlinkslideprev(HyperlinkCommand):
    pass

class hyperlinkslidenext(HyperlinkCommand):
    pass

class hyperlinkframestart(HyperlinkCommand):
    pass

class hyperlinkframeend(HyperlinkCommand):
    pass

class hyperlinkframestartnext(HyperlinkCommand):
    pass

class hyperlinkframeendprev(HyperlinkCommand):
    pass

class hyperlinkpresentationstart(HyperlinkCommand):
    pass

class hyperlinkpresentationend(HyperlinkCommand):
    pass

class hyperlinkappendixstart(HyperlinkCommand):
    pass

class hyperlinkappendixend(HyperlinkCommand):
    pass

class hyperlinkdocumentstart(HyperlinkCommand):
    pass

class hyperlinkdocumentend(HyperlinkCommand):
    pass

class againframe(Command):
    args = '< overlay > [ default ] [ options:dict ] name'

class framezoom(Command):
    args = '< buttonoverlay > < zoomedoverlay > [ options:dict ] ( pos:list ) ( zoom:list )'

class structure(Command):
    args = '< overlay > self'

class structureenv(Environment):
    args = '< overlay >'

class block(Environment):
    args = '< action > title < action2 >'

class alertblock(Environment):
    args = '< action > title < action2 >'

class exampleblock(Environment):
    args = '< action > title < action2 >'

#
# Theorems
#

# theorem.args = '< action > [ text ] < action2 >'
# corollary.args = '< action > [ text ] < action2 >'
# definition.args = '< action > [ text ] < action2 >'
# definitions.args = '< action > [ text ] < action2 >'
# fact.args = '< action > [ text ] < action2 >'
# example.args = '< action > [ text ] < action2 >'
# examples.args = '< action > [ text ] < action2 >'

class beamercolorbox(Environment):
    args = '[ options:dict ] color'

class beamerboxesrounded(Environment):
    args = '[ options:dict ] title'

class columns(Environment):
    args = '[ options:dict ]'

class column(Command):
    args = '[ placement ] width'
    def invoke(self, tex):
        # This macro can be an environment or a command each 
        # with different arguments.
        if self.macroMode == Command.MODE_BEGIN or \
           self.macroMode == Command.MODE_END:
            f = self.ownerDocument.createElement('columnenv')
            f.parentNode = self.parentNode
            f.macroMode = self.macroMode
            res = f.invoke(tex)
            if res is None:
                res = [f]
            return res
        return Command.invoke(self, tex)

class columnenv(Environment):
    args = column.args

class movie(Command):
    args = '[ options:dict ] text filename:str'

class hyperlinkmovie(Command):
    args = '[ options:dict ] label text'

class animate(Command):
    args = '< overlay >'

class animatevalue(Command):
    args = '< interval > name start end'

class multiinclude(Command):
    args = '[ overlay ] [ options:dict ] filename:str'

class sound(Command):
    args = '[ options:dict ] text filename:str'

class hyperlinksound(Command):
    args = '[ options:dict ] label text'

class hyperlinkmute(Command):
    args = 'text'

#
# Transitions
#

class TransitionCommand(Command):
    args = '< overlay > [ options:dict ]'

class transblindshorizontal(TransitionCommand):
    pass

class transblindsvertical(TransitionCommand):
    pass

class transboxin(TransitionCommand):
    pass

class transboxout(TransitionCommand):
    pass

class transdissolve(TransitionCommand):
    pass

class transglitter(TransitionCommand):
    pass

class transsplitverticalout(TransitionCommand):
    pass

class transsplitverticalin(TransitionCommand):
    pass

class transsplithorizontalin(TransitionCommand):
    pass

class transsplithorizontalout(TransitionCommand):
    pass

class transwipe(TransitionCommand):
    pass

class transduration(Command):
    args = '< overlay > seconds:int'

#
# Themes
#

class usetheme(Command):
    args = '[ options:dict ] name:list:str'

class usecolortheme(Command):
    args = '[ options:dict ] name:list:str'

class usefonttheme(Command):
    args = '[ options:dict ] name:list:str'

class useinnertheme(Command):
    args = '[ options:dict ] name:list:str'

class useoutertheme(Command):
    args = '[ options:dict ] name:list:str'

class addheadbox(Command):
    args = 'color template'

class addfootbox(Command):
    args = 'color template'
