#!/usr/bin/env python

from plasTeX import Command

class xymatrix(Command):
    args = '{ str }'
    doCharSubs = False

    class EndRow(Command):
        """ End of a row """
        macroName = '\\'

    class CellDelimiter(Command):
        """ Cell delimiter """
        macroName = 'active::&'
        pass

    class ar(Command):
        args = '[ misc:str ]'

    class arAt(Command):
        macroName = "ar@"
        args = 'arType:str [ misc:str ]'

        def postArgument(self, arg, value, tex):
            self.argSource = self.argSource.replace("~ ","~")
            super(Command, self).postArgument(arg, value, tex)

    class omit(Command):
        @property
        def source(self):
            return '\\omit'

    def preArgument(self, arg, tex):
            # Check whether there are any spacing arguments for xymatrix
            self.spacingArgs = []
            for t in tex.itertokens():
                if t == '{':
                    tex.pushToken(t)
                    break
                else:
                    self.spacingArgs.append(t)
            super(xymatrix, self).preArgument(arg, tex)

    def postArgument(self, arg, value, tex):
            self.argSource = "".join(self.spacingArgs) + self.argSource
            super(xymatrix, self).postArgument(arg, value, tex)

# These are variants of the xymatrix command in which some spacing parameters
# are specified before the main argument.
# See section 3.3 of the "XY-pic User's Guide'.
class xymatrixR(xymatrix):
    macroName = "xymatrix@R"

class xymatrixC(xymatrix):
    macroName = "xymatrix@C"

class xymatrixM(xymatrix):
    macroName = "xymatrix@M"

class xymatrixW(xymatrix):
    macroName = "xymatrix@W"

class xymatrixH(xymatrix):
    macroName = "xymatrix@H"

class xymatrixL(xymatrix):
    macroName = "xymatrix@L"

class xymatrix1(xymatrix):
    macroName = "xymatrix@1"

class xyoption(Command):
    # Options for xymatrix; unless we are writing xymatrix completely in python,
    # this is mostly irrelevant.
    pass

class useTwocells(Command):
    macroName ="UseTwocells"

class useAllTwocells(Command):
    macroName = "UseAllTwocells"
