import subprocess
from pathlib import Path
from plasTeX.Imagers import VectorImager as _Imager
from typing import List, Tuple, Optional

class DVISVGM(_Imager):
    """ Imager that uses dvisvgm """
    fileExtension = '.svg'
    verifications = ['dvisvgm --help', 'latex --help']
    compiler = 'latex'

    def executeConverter(self, outfile=None) -> List[Tuple[str, str]]:
        if outfile is None:
            outfile = self.tmpFile.with_suffix('.dvi').name

        default_scale = self.config["images"]["scale-factor"]

        images = []
        with open("images.csv") as fh:
            for no, line in enumerate(fh.readlines()):
                out = 'img%d.svg' % no
                page, output, scale_str = line.split(",")
                scale = float(scale_str.strip()) or default_scale
                images.append((out, output.rstrip()))

                rc = subprocess.run([
                    "dvisvgm",
                    "--exact",
                    "--scale={}".format(scale),
                    "--no-fonts",
                    "--output={}".format(out),
                    "--page={}".format(page),
                    outfile
                ], stdout=subprocess.DEVNULL, check=True)

        return images

Imager = DVISVGM
