"""
Package Show more

"""
from pathlib import Path

from plasTeX.PackageResource import PackageJs, PackageCss

PKG_DIR = Path(__file__).parent
STATIC_DIR = Path(__file__).parent.parent/'static'

def ProcessOptions(options, document):
    """This is called when the package is loaded."""

    navs = [{'icon': 'eye-minus', 'id': 'showmore-minus', 'class': 'showmore'},
            {'icon': 'eye-plus', 'id': 'showmore-plus', 'class': 'showmore'}]
    if 'extra-nav' in document.rendererdata['html5']:
        document.rendererdata['html5']['extra-nav'].extend(navs)
    else:
        document.rendererdata['html5']['extra-nav'] = navs

    css = PackageCss(path=STATIC_DIR/'showmore.css')
    js = PackageJs(path=STATIC_DIR/'js.cookie.min.js')
    js2 = PackageJs(path=STATIC_DIR/'showmore.js')
    document.addPackageResource([css, js, js2])
    document.userdata['expand-proof_default_content'] = '▶'

