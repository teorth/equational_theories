from plasTeX import Command

class todo(Command):
    disabled = False
    args = '[ attr:dict ] todo'

    @property
    def blockType(self):
        if self.attributes.get("attr") is None:
            return False

        return bool(self.attributes["attr"].get("inline"))

def ProcessOptions(options, document):
    if options.get("disable"):
        document.userdata['todonotes'] = {'disable': True}
    else:
        document.userdata['todonotes'] = {'disable': False}
