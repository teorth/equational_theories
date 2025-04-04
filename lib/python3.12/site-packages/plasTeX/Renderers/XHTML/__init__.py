import re
from plasTeX.Renderers.PageTemplate import Renderer as _Renderer

class XHTML(_Renderer):
    """ Renderer for XHTML documents """

    fileExtension = '.html'
    imageTypes = ['.png','.jpg','.jpeg','.gif']
    vectorImageTypes = ['.svg']

    def cleanup(self, document, files, postProcess=None):
        res = _Renderer.cleanup(self, document, files, postProcess=postProcess)
        return res

    def processFileContent(self, document, s):
        s = _Renderer.processFileContent(self, document, s)

        # Force XHTML syntax on empty tags
        s = re.compile(r'(<(?:hr|br|img|link|meta|col)\b.*?)\s*/?\s*(>)',
                       re.I|re.S).sub(r'\1 /\2', s)

        # Remove empty paragraphs
        s = re.compile(r'<p>\s*</p>', re.I).sub(r'', s)

        # Add a non-breaking space to empty table cells
        s = re.compile(r'(<(td|th)\b[^>]*>)\s*(</\2>)', re.I).sub(r'\1&nbsp;\3', s)

        return s


Renderer = XHTML
