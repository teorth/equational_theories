"""
B.3 Parameters

"""

from datetime import datetime
from plasTeX import ParameterCommand, DimenCommand
from plasTeX import GlueCommand, MuGlueCommand

#
# TeX parameters (see The TeXbook, page 272)
#

# Integer parameters
class pretolerance(ParameterCommand): value = ParameterCommand.new(100)
class tolerance(ParameterCommand): value = ParameterCommand.new(200)
class hbadness(ParameterCommand): value = ParameterCommand.new(1000)
class vbadness(ParameterCommand): value = ParameterCommand.new(1000)
class linepenalty(ParameterCommand): value = ParameterCommand.new(1000)
class hyphenpenalty(ParameterCommand): value = ParameterCommand.new(50)
class exhyphenpenalty(ParameterCommand): value = ParameterCommand.new(50)
class binoppenalty(ParameterCommand): value = ParameterCommand.new(700)
class relpenalty(ParameterCommand): value = ParameterCommand.new(500)
class clubpenalty(ParameterCommand): value = ParameterCommand.new(150)
class widowpenalty(ParameterCommand): value = ParameterCommand.new(150)
class displaywidowpenalty(ParameterCommand): value = ParameterCommand.new(50)
class brokenpenalty(ParameterCommand): value = ParameterCommand.new(100)
class predisplaypenalty(ParameterCommand): value = ParameterCommand.new(10000)
class postdisplaypenalty(ParameterCommand): value = ParameterCommand.new(0)
class interlinepenalty(ParameterCommand): value = ParameterCommand.new(0)
class floatingpenalty(ParameterCommand): value = ParameterCommand.new(0)
class outputpenalty(ParameterCommand): value = ParameterCommand.new(0)
class doublehyphendemerits(ParameterCommand): value = ParameterCommand.new(100000)
class finalhyphendemerits(ParameterCommand): value = ParameterCommand.new(5000)
class adjdemerits(ParameterCommand): value = ParameterCommand.new(10000)
class looseness(ParameterCommand): value = ParameterCommand.new(0)
class pausing(ParameterCommand): value = ParameterCommand.new(0)
class holdinginserts(ParameterCommand): value = ParameterCommand.new(0)
class tracingonline(ParameterCommand): value = ParameterCommand.new(0)
class tracingmacros(ParameterCommand): value = ParameterCommand.new(0)
class tracingstats(ParameterCommand): value = ParameterCommand.new(0)
class tracingparagraphs(ParameterCommand): value = ParameterCommand.new(0)
class tracingpages(ParameterCommand): value = ParameterCommand.new(0)
class tracingoutput(ParameterCommand): value = ParameterCommand.new(0)
class tracinglostchars(ParameterCommand): value = ParameterCommand.new(1)
class tracingcommands(ParameterCommand): value = ParameterCommand.new(0)
class tracingrestores(ParameterCommand): value = ParameterCommand.new(0)
class language(ParameterCommand): value = ParameterCommand.new(0)
class uchyph(ParameterCommand): value = ParameterCommand.new(1)
class lefthyphenmin(ParameterCommand): value = ParameterCommand.new(0)
class righthyphenmin(ParameterCommand): value = ParameterCommand.new(0)
class globaldefs(ParameterCommand): value = ParameterCommand.new(0)
class defaulthyphenchar(ParameterCommand): value = ParameterCommand.new(ord('-'))
class defaultskewchar(ParameterCommand): value = ParameterCommand.new(-1)
class escapechar(ParameterCommand): value = ParameterCommand.new(ord('\\'))
class endlinechar(ParameterCommand): value = ParameterCommand.new(ord('\n'))
class newlinechar(ParameterCommand): value = ParameterCommand.new(-1)
class maxdeadcycles(ParameterCommand): value = ParameterCommand.new(25)
class hangafter(ParameterCommand): value = ParameterCommand.new(1)
class fam(ParameterCommand): value = ParameterCommand.new(0)
class mag(ParameterCommand): value = ParameterCommand.new(1000)
class delimiterfactor(ParameterCommand): value = ParameterCommand.new(901)
class time(ParameterCommand): value = ParameterCommand.new((datetime.now().hour*60) + datetime.now().minute)
class day(ParameterCommand): value = ParameterCommand.new(datetime.now().day)
class month(ParameterCommand): value = ParameterCommand.new(datetime.now().month)
class year(ParameterCommand): value = ParameterCommand.new(datetime.now().year)
class showboxbreadth(ParameterCommand): value = ParameterCommand.new(5)
class showboxdepth(ParameterCommand): value = ParameterCommand.new(3)
class errorcontextlines(ParameterCommand): value = ParameterCommand.new(5)

# Dimen parameters
class hfuzz(DimenCommand): value = DimenCommand.new('0.1pt')
class vfuzz(DimenCommand): value = DimenCommand.new('0.1pt')
class overfullrule(DimenCommand): value = DimenCommand.new('5pt')
class emergencystretch(DimenCommand): value = DimenCommand.new(0)
class hsize(DimenCommand): value = DimenCommand.new('6.5in')
class vsize(DimenCommand): value = DimenCommand.new('8.9in')
class maxdepth(DimenCommand): value = DimenCommand.new('4pt')
class splitmaxdepth(DimenCommand): value = DimenCommand.new('65536pt')
class boxmaxdepth(DimenCommand): value = DimenCommand.new('65536pt')
class lineskipamount(DimenCommand): value = DimenCommand.new(0)
class delimitershortfall(DimenCommand): value = DimenCommand.new('5pt')
class nulldelimiterspace(DimenCommand): value = DimenCommand.new('1.2pt')
class scriptspace(DimenCommand): value = DimenCommand.new('0.5pt')
class mathsurround(DimenCommand): value = DimenCommand.new(0)
class predisplaysize(DimenCommand): value = DimenCommand.new(0)
class displaywidth(DimenCommand): value = DimenCommand.new(0)
class displayindent(DimenCommand): value = DimenCommand.new(0)
class parindent(DimenCommand): value = DimenCommand.new('20pt')
class hangindent(DimenCommand): value = DimenCommand.new(0)
class hoffset(DimenCommand): value = DimenCommand.new(0)
class voffset(DimenCommand): value = DimenCommand.new(0)

# Glue parameters
class baselineskip(GlueCommand): value = GlueCommand.new('12pt')
class lineskip(GlueCommand): value = GlueCommand.new('1pt')
class parskip(GlueCommand): value = GlueCommand.new('0pt', plus='1pt')
class abovedisplayskip(GlueCommand): value = GlueCommand.new('0pt', plus='3pt', minus='9pt')
class abovedisplayshortskip(GlueCommand): value = GlueCommand.new('0pt', plus='3pt')
class belowdisplayskip(GlueCommand): value = GlueCommand.new('12pt', plus='3pt', minus='9pt')
class belowdisplayshortskip(GlueCommand): value = GlueCommand.new('7pt', plus='3pt', minus='4pt')
class leftskip(GlueCommand): value = GlueCommand.new(0)
class rightskip(GlueCommand): value = GlueCommand.new(0)
class topskip(GlueCommand): value = GlueCommand.new('10pt')
class splittopskip(GlueCommand): value = GlueCommand.new('10pt')
class tabskip(GlueCommand): value = GlueCommand.new(0)
class spaceskip(GlueCommand): value = GlueCommand.new(0)
class xspaceskip(GlueCommand): value = GlueCommand.new(0)
class parfillskip(GlueCommand): value = GlueCommand.new('0pt', plus='1fil')

# MuGlue parameters
class thinmuskip(MuGlueCommand): value = MuGlueCommand.new('3mu')
class medmuskip(MuGlueCommand): value = MuGlueCommand.new('4mu', plus='2mu', minus='4mu')
class thickmuskip(MuGlueCommand): value = MuGlueCommand.new('5mu', plus='5mu')

# Token parameters
#class output(ParameterCommand): pass
#class everypar(ParameterCommand): pass
#class everymath(ParameterCommand): pass
#class everydisplay(ParameterCommand): pass
#class everyhbox(ParameterCommand): pass
#class everyvbox(ParameterCommand): pass
#class everyjob(ParameterCommand): pass
#class everycr(ParameterCommand): pass
#class errhelp(ParameterCommand): pass
