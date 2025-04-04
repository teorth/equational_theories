from plasTeX import Command

class fancypagestyle(Command):
    args = 'style'

class fancyhead(Command):
    args = '[ pos ] text'

class fancyfoot(fancyhead):
    pass

class fancyhf(Command):
    args = 'text'

class rightmark(Command):
    pass

class leftmark(Command):
    pass

class chaptermark(Command):
    pass

class sectionmark(Command):
    pass

class markboth(Command):
    pass

class markright(Command):
    pass
