from plasTeX import Command, TheCounter

def ProcessOptions(options, document):
    context = document.context
    # Lists
    context.newcounter('enumi')
    context.newcounter('enumii', resetby='enumi')
    context.newcounter('enumiii', resetby='enumii')
    context.newcounter('enumiv', resetby='enumiii')

    # Sections
    context.newcounter('part', resetby='volume',
                       format='$part')
    context.newcounter('chapter', resetby='volume',
                       format='$chapter')
    context.newcounter('section', resetby='chapter',
                       format='${thechapter}.${section}')
    context.newcounter('subsection', resetby='section',
                       format='${thesection}.${subsection}')
    context.newcounter('subsubsection', resetby='subsection',
                       format='${thesubsection}.${subsubsection}')
    context.newcounter('paragraph', resetby='subsubsection',
                       format='${thesubsubsection}.${paragraph}')
    context.newcounter('subparagraph', resetby='paragraph',
                       format='${theparagraph}.${subparagraph}')
    context.newcounter('subsubparagraph', resetby='subparagraph',
                       format='${thesubparagraph}.${subsubparagraph}')

    context.newcounter('equation', resetby='chapter',
                       format='${thechapter}.${equation}')

    context.newcounter('secnumdepth')
    context.newcounter('tocdepth')
    context.newcounter('page')

    # Floats
    context.newcounter('figure', resetby='chapter',
                       format='${thechapter}.${figure}', trimLeft=True)
    context.newcounter('table', resetby='chapter',
                       format='${thechapter}.${table}', trimLeft=True)
    context.newcounter('topnumber')
    context.newcounter('bottomnumber')
    context.newcounter('totalnumber')
    context.newcounter('dbltopnumber')
    context.loadLanguage('american', document)
    
    language = False
    languages = list(document.context.languages.keys())
    for key, value in list(options.items()):
        if key == 'language':
            language = True
            context.loadLanguage(value, document)
        elif key in languages:
            language = True
            context.loadLanguage(key, document)

class frontmatter(Command):
    pass

class mainmatter(Command):
    pass

class backmatter(Command):
    pass

class appendix(Command):

    class thechapter(TheCounter):
        format = '${chapter.Alph}'

    def invoke(self, tex):
        self.ownerDocument.context.counters['chapter'].setcounter(0)
        self.ownerDocument.context['thechapter'] = type(self).thechapter
