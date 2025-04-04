import plasTeX.Imagers
from plasTeX.Imagers import Imager as _Imager

class DVI2Bitmap(_Imager):
    """ Imager that uses dvi2bitmap """

    command = 'dvi2bitmap --magnification=6 --scaledown=6 ' + \
              '--process=notransparent --crop=all=5 --output=img%d.png'
    fileExtension = '.png'

    def writePreamble(self, document):
        _Imager.writePreamble(self, document)
        self.source.write('\\special{dvi2bitmap default imageformat png}\n')
        self.source.write('\\special{dvi2bitmap default unit pixels}\n')

    def formatConfigOptions(self, config):
        options = []
        if config['resolution']:
            options.append(('--resolution=%s' % config['resolution'], ''))
        return options

Imager = DVI2Bitmap
