import subprocess, sys
import plasTeX.Imagers.gspdfpng as gspdfpng

gs = 'gs'
if sys.platform.startswith('win'):
   gs = 'gswin32c'

class GSDVIPNG(gspdfpng.GSPDFPNG):
    """ Imager that uses gs to convert dvi to png """
    compiler = 'latex'
    verifications = ['%s --help' % gs, 'dvips --help', 'latex --help']

    def executeConverter(self, outfile=None):
        if outfile is None:
            outfile = self.tmpFile.with_suffix('.dvi').name

        subprocess.run(['dvips', '-o', self.tmpFile.with_suffix('.ps').name, outfile], check=True)
        return gspdfpng.GSPDFPNG.executeConverter(self, self.tmpFile.with_suffix('.ps').name)

Imager = GSDVIPNG
