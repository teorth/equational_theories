import subprocess
import shlex

from plasTeX.Imagers import Imager as _Imager

class pdftoppm(_Imager):
    """ Imager that uses libpoppler's pdftoppm to convert pdf to png """
    command = 'pdftoppm -png -r 150'
    compiler = 'pdflatex'
    fileExtension = '.png'

    def verify(self):
        """
        pdftoppm writes its help message to standard error, and not
        standard output as plasTeX expects, and we thus have to
        override this method. Note that this method will also work if
        pdftoppm writes its help message to standard output.

        """
        cmd = self.command.split()[0]
        proc = subprocess.Popen('%s --help' % cmd,
                                shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT,
                                universal_newlines=True)
        return 'pdftoppm' in str(proc.communicate())

    def executeConverter(self, outfile=None):
        """
        We need to override this because plasTeX always puts the input
        file at the end of the command-line.  We also need to return the
        list of images.

        """
        if outfile is None:
            outfile = self.tmpFile.with_suffix('.pdf')

        options = ''
        if self._configOptions:
            for opt, value in self._configOptions:
                opt, value = str(opt), str(value)
                if ' ' in value:
                    value = '"%s"' % value
                options += '%s %s ' % (opt, value)
        subprocess.run(shlex.split('%s %s%s img' % (self.command, options, outfile)), check=True)

        images = []
        with open("images.csv") as fh:
            lines = fh.readlines()
        for line in lines:
            page, output, _ = line.split(",")
            images.append(["img-{}.png".format(page), output.rstrip()])

        return images

Imager = pdftoppm
