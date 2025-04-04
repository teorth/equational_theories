import pdb

from plasTeX import Command
from plasTeX.Logging import getLogger


class settrace(Command):
    def invoke(self, tex):
        document = self.ownerDocument
        config = document.config
        context = document.context
        pdb.set_trace()


class setloglevel(Command):
    args = 'logger:str level:str'

    def invoke(self, tex):
        self.parse(tex)
        logger_name = self.attributes['logger']
        level = self.attributes['level']
        logger = getLogger(logger_name)
        logger.setLevel(level)

        config = self.ownerDocument.config
        config['logging'].data[logger_name].setValue(level)


def ProcessOptions(options, document):
    if 'post_parse_trace' in options:
        def trace_callback():
            config = document.config
            context = document.context
            pdb.set_trace()
        document.addPostParseCallbacks(1000, trace_callback)
