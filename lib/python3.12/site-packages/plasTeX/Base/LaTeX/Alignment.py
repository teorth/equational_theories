"""

"""

from plasTeX import Environment


class center(Environment): 
    blockType = True

class centering(center):
    blockType = True

class flushleft(Environment):
    blockType = True

class raggedright(flushleft):
    blockType = True

class flushright(Environment):
    blockType = True

class raggedleft(flushright):
    blockType = True

class raggedbottom(Environment):
    pass
