import pickle
import os
from typing import Dict
from plasTeX import Command
from plasTeX.Logging import getLogger

log = getLogger()

def load_paux(name: str) -> Dict:
    if not os.path.exists(name):
        log.warning('Could not find {}'.format(name))
        return dict()
    try:
        data = pickle.load(open(name, 'rb'))
    except:
        log.warning('Failed to load {}'.format(name))
        return dict()
    return data


class externaldocument(Command):
    args = '[prefix:str] name:str [url:url]'

    def invoke(self, tex):
        super().invoke(tex)
        pauxname = self.attributes['name'].replace('.tex', '') + '.paux'
        prefix = self.attributes['prefix'] or ''
        url = self.attributes['url']
        if url:
            url = url.textContent.rstrip('/') + '/'
        labels = self.ownerDocument.context.labels
        for block in load_paux(pauxname).values():
            for lbl, val in block.items():
                labels[prefix + lbl] = val
                if url:
                    labels[prefix + lbl]['url'] = url + labels[prefix + lbl]['url']
