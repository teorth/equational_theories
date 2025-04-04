import subprocess
import re
import xml.etree.ElementTree as ET
from typing import List, Tuple
from plasTeX.Imagers import VectorImager

length_re = re.compile('([0-9\\.]*)(.*)')
class PDFSVG(VectorImager):
    """ Imager that uses pdf2svg """
    fileExtension = '.svg'
    verifications = ['pdflatex --help', 'which pdf2svg', 'pdfcrop --help']
    compiler = 'pdflatex'

    def executeConverter(self, outfile=None) -> List[Tuple[str, str]]:
        if outfile is None:
            outfile = self.tmpFile.with_suffix('.pdf').name

        subprocess.call(["pdfcrop", outfile, self.tmpFile.with_suffix('.cropped.pdf').name], stdout=subprocess.DEVNULL)

        images = []
        with open("images.csv") as fh:
            for no, line in enumerate(fh.readlines()):
                filename = 'img%d.svg' % no
                page, output, scale_str = line.split(",")
                scale = float(scale_str.strip())
                images.append((filename, output.rstrip()))

                subprocess.run(['pdf2svg', self.tmpFile.with_suffix('.cropped.pdf').name, filename, str(page)], stdout=subprocess.DEVNULL, check=True)

                if scale != 1:
                    tree = ET.parse(filename)
                    root = tree.getroot()

                    for attrib in ["width", "height"]:
                        m = length_re.match(root.attrib[attrib])
                        if m is None:
                            raise ValueError
                        root.attrib[attrib] = "{:.2f}{}".format(float(m.group(1)) * scale, m.group(2))

                    tree.write(filename)

        return images

Imager = PDFSVG
