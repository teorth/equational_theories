from plasTeX import log

from plasTeX.Packages.book import *
import plasTeX.Packages.book as book

def ProcessOptions(options, document): # type: ignore
    log.info('The amsbook class is currently nothing but the book class.')
    book.ProcessOptions(options, document)
