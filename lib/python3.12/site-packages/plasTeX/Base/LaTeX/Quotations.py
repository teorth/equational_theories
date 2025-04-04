"""
C.6.1 Quotations and Verse (p184)

"""

from plasTeX import Environment


class quote(Environment): 
    blockType = True

class quotation(Environment):
    blockType = True

class verse(Environment):
    blockType = True
