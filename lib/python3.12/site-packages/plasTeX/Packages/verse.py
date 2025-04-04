from plasTeX.Base.LaTeX.Quotations import verse

verse.args = '[ width:nox ]'

class altverse(verse):
    pass

class patverse(verse):
    pass

class patverse__star(verse):
    macroName = 'patverse*'
