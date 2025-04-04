from plasTeX.ConfigManager import *
from typing import Type
from argparse import ArgumentTypeError
import os

def defaultConfig(loadConfigFiles: bool=False):
    config = ConfigManager()

    #
    # General
    #
    general = config.addSection('general')

    general['renderer'] = StringOption(
        """
        Renderer to use for conversion

        This is either one of the built in renderers, or a path to the
        directory of a renderer
        """,
        options = '--renderer',
        default = 'HTML5',
    )

    general['theme'] = StringOption(
        """ Theme for the renderer to use """,
        options = '--theme',
        default = 'default',
    )

    general['extra-templates'] = MultiStringOption(
        """ Extra templates files to use """,
        options='--extra-templates',
        default=[],
    )

    general['copy-theme-extras'] = BooleanOption(
        """  Copy files associated with the theme to the output directory """,
        options = '--copy-theme-extras !--no-theme-extras',
        default = True,
    )

    general['kpsewhich'] = StringOption(
        """ Program which locates LaTeX files and packages """,
        options = '--kpsewhich',
        default = 'kpsewhich',
    )

    general['xml'] = BooleanOption(
        """ Dump XML representation of the document (for debugging) """,
        options = '--xml',
        default = False,
    )

    general['debug'] = BooleanOption(
        """ Parse the document and drop into a debugger.""",
        options = '--debug',
        default = False,
    )

    general['paux-dirs'] = MultiStringOption(
        """Directories where *.paux files should be loaded from.""",
        options = '--paux-dirs',
        default = [],
    )

    general['plugins'] = MultiStringOption(
        """
        A list of plugins to use. Each element must be a valid python module name,
        accessible from the current python path.

        """,
        options = '--plugins',
        default = [],
    )

    general['load-tex-packages'] = BooleanOption(
        """Try to load the TeX implementation of packages having no python
        implementation.""",
        options = '--load-tex-packages !--no-load-tex-packages',
        default = True,
    )

    general['tex-packages'] =  MultiStringOption(
        """
        Packages that we will try to load from their TeX implementation if no
        python implementation is found, even if the load-tex-packages
        option is False.
        """,
        options = '--tex-packages',
        default = [],
    )

    general['packages-dirs'] = MultiStringOption(
        """
        Directories where packages could be implemented in python.
        Use either absolute paths or paths relative to the current directory.
        """,
        options = '--packages-dirs',
        default = [],
    )

    #
    # Links
    #

    links = config.addSection('links')

    class LinksOption(DictOption[str]):
        @classmethod
        def entryFromString(cls, entry: str) -> str:
            return entry

        def registerArgparse(self, group: ArgumentGroup):
            group.add_argument(*self.options, dest=self.name, help=self.description, action='append', nargs='+')

        def updateFromDict(self, data: Dict["str", Any]):
            try:
                data = data[self.name]
                if data is not None:
                    for entry in data:
                        if len(entry) == 2:
                            self.set("{}-title".format(entry[0]), entry[1])
                        elif len(entry) == 3:
                            self.set("{}-url".format(entry[0]), entry[1])
                            self.set("{}-title".format(entry[0]), entry[2])
                        else:
                            raise ArgumentTypeError("--link must be 2 or 3 arguments. {} were supplied".format(len(entry)))
            except KeyError:
                pass

    links['links'] = LinksOption(
        """ Set links for use in navigation """,
        options = '--link',
        default = {},
    )

    #
    # Counters
    #

    counters = config.addSection('counters')

    class CountersOption(DictOption[int]):
        @classmethod
        def entryFromString(cls, entry: str) -> int:
            return int(entry)

        def registerArgparse(self, group: ArgumentGroup):
            group.add_argument(*self.options, dest=self.name, help=self.description, action='append', nargs=2, metavar=("COUNTER", "VALUE"))

    counters['counters'] = CountersOption(
        """ Set initial counter values """,
        options = '--counter',
        default = {}
    )

    files = config.addSection('files', 'File Handling Options')

    files['input-encoding'] = StringOption(
        """ Input file encoding """,
        options = '--input-encoding',
        default = 'utf-8',
    )

    files['output-encoding'] = StringOption(
        """ Output file encoding """,
        options = '--output-encoding',
        default = 'utf-8',
    )

    files['escape-high-chars'] = BooleanOption(
        """ Escape characters that are higher than 7-bit """,
        options = '--escape-high-chars',
        default = False,
    )

    files['split-level'] = IntegerOption(
        """ Highest section level that generates a new file """,
        options = '--split-level',
        default = 2,
    )

    files['log'] = BooleanOption(
        """ Log messages go to log file instead of console """,
        options = '--log',
        default = False,
    )

    files['filename'] = StringOption(
        """ Template for output filenames """,
        options = '--filename',
        default = 'index [$id, sect$num(4)]',
    )

    files['bad-chars'] = StringOption(
        """ Characters that should not be allowed in a filename """,
        options = '--bad-filename-chars',
        default = ': #$%%^&*!~`"\'=?/{}[]()|<>;\\,.', # Double % to escape since we interoplate values
    )

    files['bad-chars-sub'] = StringOption(
        """ Character that should be used instead of an illegal character """,
        options = '--bad-filename-chars-sub',
        default = '-',
    )

    files['directory'] = StringOption(
        """ Directory to put output files into """,
        options = '--dir -d',
        default = '$jobname',
    )

    #
    # Images
    #

    images = config.addSection('images')

    class ImageScaleOption(DictOption[float]):
        @classmethod
        def entryFromString(cls, entry: str) -> float:
            return float(entry)

        def registerArgparse(self, group: ArgumentGroup):
            group.add_argument(*self.options, dest=self.name, help=self.description, action='append', nargs=2, metavar=("NODE", "VALUE"))

    images['scales'] = ImageScaleOption(
        """ Set image scale for given node name """,
        options = '--scales',
        default = {}
    )

    images['base-url'] = StringOption(
        """ Base URL for all images """,
        options = '--image-base-url',
        default = '',
    )

    images['enabled'] = BooleanOption(
        """ Enable image generation """,
        options = '--enable-images !--disable-images',
        default = True,
    )

    images['imager'] = StringOption(
        """ LaTeX to image program """,
        options = '--imager',
        default = 'gspdfpng pdftoppm dvipng dvi2bitmap gsdvipng OSXCoreGraphics',
    )

    images['vector-imager'] = StringOption(
        """ LaTeX to vector image program """,
        options = '--vector-imager',
        default = 'pdf2svg dvisvgm',
    )

    images['filenames'] = StringOption(
        """ Template for image filenames """,
        options = '--image-filenames',
        default = 'images/img-$num(4)',
    )

    images['baseline-padding'] = IntegerOption(
        """ Amount to pad the image below the baseline """,
        options = '--image-baseline-padding',
        default = 0,
    )

    images['scale-factor'] = FloatOption(
        """ Factor to scale externally included images by """,
        options = '--image-scale-factor',
        default = 1.0,
    )

    images['vector-compiler'] = StringOption(
        """ LaTeX command to use when compiling image document with vector imager""",
        options = '--vector-image-compiler',
        default = '',
    )

    images['compiler'] = StringOption(
        """ LaTeX command to use when compiling image document """,
        options = '--image-compiler',
        default = '',
    )

    images['cache'] = BooleanOption(
        """  Enable image caching between runs """,
        options = '--enable-image-cache !--disable-image-cache',
        default = False,
    )

    images['save-file'] = BooleanOption(
        """ Should the temporary images.tex file be saved for debugging? """,
        options = '--save-image-file !--delete-image-file',
        default = False,
    )

    images['transparent'] = BooleanOption(
        """ Specifies whether the image backgrounds should be transparent or not """,
        options = '--transparent-images !--opaque-images',
        default = False,
    )

    images['resolution'] = IntegerOption(
        """ Resolution of images document """,
        options = '--image-resolution',
        default = 0,
    )

    #
    # Document
    #

    doc = config.addSection('document', "Document Options")

    doc['base-url'] = StringOption(
        """ Base URL for inter-node links """,
        options = '--base-url',
        default = '',
    )

    doc['title'] = StringOption(
        """
        Title for the document

        This option specifies a title to use instead of the title
        specified in the LaTeX document.

        """,
        options = '--title',
        default = '',
    )

    doc['toc-depth'] = IntegerOption(
        """ Number of levels to display in the table of contents """,
        options = '--toc-depth',
        default = 3,
    )

    doc['toc-non-files'] = BooleanOption(
        """ Display sections that do not create files in the table of contents """,
        options = '--toc-non-files',
        default = False,
    )

    doc['sec-num-depth'] = IntegerOption(
        """ Maximum section depth to display section numbers """,
        options = '--sec-num-depth',
        default = 2,
    )

    doc['index-columns'] = IntegerOption(
        """ Number of columns to split the index entries into """,
        options = '--index-columns',
        default = 2,
    )

    doc['lang-terms'] = MultiStringOption(
        """ A list of files that contain language terms """,
        options = '--lang-terms',
        default = [],
    )

    doc['disable-charsub'] = MultiStringOption(
        """A list of characters to not perform character substitutions""",
        options = "--disable-charsub",
        default = []
    )

    #
    # Logging
    #

    logging = config.addSection('logging', "Logging Options")

    class LogOption(DictOption[str]):
        @classmethod
        def entryFromString(cls, entry: str) -> str:
            return entry

        def registerArgparse(self, group: ArgumentGroup):
            group.add_argument(*self.options, dest=self.name, help=self.description, action='append', nargs=2, metavar=("NAME", "LEVEL"))

    logging["logging"] = LogOption("Log levels", options = "--logging", default = {})

    if loadConfigFiles:
        config.read(['~/.plasTeXrc', '/usr/local/etc/plasTeXrc', os.path.join(os.path.dirname(__file__), 'plasTeXrc')])

    return config
