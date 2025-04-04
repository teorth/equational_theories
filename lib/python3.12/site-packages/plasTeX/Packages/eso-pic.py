from plasTeX import Command

class LenToUnit(Command):
    args = 'length:nox'

class AtPageUpperLeft(Command):
    args = 'commands:nox'

class AtPageLowerLeft(Command):
    args = 'commands:nox'

class AtPageCenter(Command):
    args = 'commands:nox'

class AtTextUpperLeft(Command):
    args = 'commands:nox'

class AtTextLowerLeft(Command):
    args = 'commands:nox'

class AtTextCenter(Command):
    args = 'commands:nox'

class AddToShipoutPicture(Command):
    args = '*'

class ClearShipoutPicture(Command):
    pass

class gridSetup(Command):
    args = '[ gridunitname:nox ] [ gridunit:nox ] labelfactor:nox griddelta:nox gridDelta:nox gap:nox'

