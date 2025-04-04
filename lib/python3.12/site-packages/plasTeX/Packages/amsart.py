from plasTeX import log
from plasTeX.Packages.article import appendix
import plasTeX.Packages.article as article

def ProcessOptions(options, document): # type: ignore
    log.info('The amsart class is currently nothing but the article class.')
    article.ProcessOptions(options, document)
