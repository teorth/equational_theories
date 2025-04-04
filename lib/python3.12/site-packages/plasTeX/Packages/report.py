from plasTeX.Packages.book import *
from plasTeX.Packages import book

def ProcessOptions(options, document): # type: ignore
    book.ProcessOptions(options, document)
    document.context['theequation'].format = '${equation}'
