from plasTeX.ConfigManager import *
from plasTeX.DOM import Node

class MacrosOption(DictOption[str]):
    @classmethod
    def entryFromString(cls, entry: str) -> str:
        return entry

    def registerArgparse(self, group: ArgumentGroup):
        group.add_argument(*self.options, dest=self.name,
                           help=self.description, action='append',
                           nargs=2, metavar=("MACRO", "VALUE"))

def addConfig(config: ConfigManager):
    section = config.addSection('html5', 'Html5 renderer Options')

    section['extra-css'] = MultiStringOption(
        """ Extra css files to use """,
        options='--extra-css',
        default=[],
    )

    section['extra-js'] = MultiStringOption(
        """ Extra javascript files to use """,
        options='--extra-js',
        default=[],
    )

    section['theme-css'] = StringOption(
        """ Theme css file""",
        options='--theme-css',
        default='white',
    )

    section['use-theme-css'] = BooleanOption(
        """ Use theme css """,
        options='--use-theme-css !--no-theme-css',
        default=True,
    )

    section['use-theme-js'] = BooleanOption(
        """ Use theme javascript """,
        options='--use-theme-js !--no-theme-js',
        default=True,
    )

    section['display-toc'] = BooleanOption(
        """ Display table of contents on each page """,
        options='--display-toc !--no-display-toc',
        default=True,
    )

    section['localtoc-level'] = IntegerOption(
        """ Create local toc above this level """,
        options='--localtoc-level',
        default=Node.DOCUMENT_LEVEL-1,
    )

    section['breadcrumbs-level'] = IntegerOption(
        """ Create breadcrumbs from this level """,
        options='--breadcrumbs-level',
        default=10,
    )

    section['use-mathjax'] = BooleanOption(
        """ Use mathjax """,
        options='--use-mathjax !--no-mathjax',
        default=True,
    )

    section['mathjax-url'] = StringOption(
        """ Url of the MathJax lib """,
        options='--mathjax-url',
        default='https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js',
    )

    section['mathjax-dollars'] = BooleanOption(
        """ Use single dollars as math delimiter for mathjax """,
        options='--dollars !--no-dollars',
        default=False,
    )

    section['filters'] = MultiStringOption(
        """Comma separated list of commands to invoke on each output page.""",
        options='--filters',
        default=[],
    )
    mjsection = config.addSection('mathjax-macros', 'MathJax macros')
    mjsection['macros'] = MacrosOption(
        """ Set MathJax macros """,
        options = '--mj-macros',
        default = {}
    )
