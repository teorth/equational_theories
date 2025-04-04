"""
C.14.1 The picture Environment (p219)

"""

from plasTeX import Command, Environment, DimenCommand


class qbeziermax(Command):
    str = '250'

class unitlength(DimenCommand):
    value = DimenCommand.new('1pt')

class picture(Environment):
    args = '( dimension:str ) ( offset:str )'
    blockType = True
    captionable = True

#   def digest(self, tex):
#       result = Environment.digest(self, tex)
#       import pdb
#       pdb.set_trace()
#       return result

    def paragraphs(self):
        pass

    class put(Command):
        args = '( coord:str ) object'

    class multiput(Command):
        args = '( coord:str ) ( incr:str ) num:int object'

    class qbezier(Command):
        args = '[ num:int ] ( coord1:str ) ( coord2:str ) ( coord3:str )'

    class graphpaper(Command):
        args = '[ spacing ] ( coord:str ) ( dimen:str )'

    class makebox(Command):
        args = '( dimen:str ) [ pos:str ] text'

    class framebox(Command):
        args = '( dimen:str ) [ pos:str ] text'

    class dashbox(Command):
        args = 'dashdimen:str ( dimen:str ) [ pos:str ] text'

    class line(Command):
        args = '( slope ) dimen'

    class vector(Command):
        args = '( slope ) dimen'

    class shortstack(Command):
        args = '[ pos:str ] col'

    class circle(Command):
        args = '* diam'

    class oval(Command):
        args = '[ radius:str ] ( dimen:str ) [ part:str ]' 

    class frame(Command):
        args = 'object'

    class savebox(Command):
        args = 'name:cs ( dimen:str ) [ pos:str ] text'

    class thinlines(Command):
        pass

    class thicklines(Command):
        pass

    class linethickness(Command):
        args = 'len:dimen'
    
