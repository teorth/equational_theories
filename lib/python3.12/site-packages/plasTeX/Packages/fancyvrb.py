from plasTeX.Base.LaTeX.Verbatim import verbatim

class Verbatim(verbatim):
    args = '[ options:dict ]'

    def parse(self, tex):
        verbatim.parse(self, tex)

        options = self.attributes['options']

        if options is None:
            options = {}

        # Format command
        formatcom = None
        if 'formatcom' in list(options.keys()):
            formatcom = options['formatcom']

        # Frame width
        framerule = '1px'
        if 'framerule' in list(options.keys()):
            framerule = options['framerule'].strip()

        # Frame color
        rulecolor = 'black'
        if 'rulecolor' in list(options.keys()):
            rulecolor = options['rulecolor'].style['color']

        # Frames
        if 'frame' in list(options.keys()):
            frame = options['frame'].strip()
            if frame in ['leftline','single']:
                self.style['border-left'] = '%s solid %s' % \
                                             (framerule, rulecolor)
            if frame in ['rightline','single']:
                self.style['border-right'] = '%s solid %s' % \
                                              (framerule, rulecolor)
            if frame in ['topline','single','lines']:
                self.style['border-top'] = '%s solid %s' % \
                                            (framerule, rulecolor)
            if frame in ['bottomline','single','lines']:
                self.style['border-bottom'] = '%s solid %s' % \
                                               (framerule, rulecolor)

        # Padding
        if 'framesep' in list(options.keys()):
            self.style['padding'] = options['framesep'].strip()

        # Font family
        if 'fontfamily' in list(options.keys()):
            self.style['font-family'] = options['fontfamily'].strip()

        # Font size
        if 'fontsize' in list(options.keys()):
            fontsize = options['fontsize'].strip()
            if fontsize == 'tiny':
                self.style['font-size'] = 'xx-small'
            elif fontsize == 'footnotesize':
                self.style['font-size'] = 'x-small'
            elif fontsize == 'small':
                self.style['font-size'] = 'small'
            elif fontsize == 'normalsize':
                self.style['font-size'] = 'medium'
            elif fontsize == 'large':
                self.style['font-size'] = 'large'
            elif fontsize == 'Large':
                self.style['font-size'] = 'x-large'
            elif fontsize == 'huge':
                self.style['font-size'] = 'xx-large'
            elif fontsize == 'huge':
                self.style['font-size'] = 'xx-large'

        # Font shape
        if 'fontshape' in list(options.keys()):
            fontshape = options['fontshape'].strip()
            if fontshape.startswith('i') or fontshape.startswith('o'):
                self.style['font-style'] = 'italic'

        # Font weight
        if 'fontseries' in list(options.keys()):
            fontseries = options['fontseries'].strip()
            if fontshape.startswith('b'):
                self.style['font-weight'] = 'bold'

        # Suppress characters at beginning
        if 'gobble' in list(options.keys()):
            gobble = int(options['gobble'])
            content = content.split('\n')
            for i in range(len(content)):
                try: content[i] = content[i][gobble:]
                except: content[i] = ''
            content = '\n'.join(content)

        # Command chars
        if 'commandchars' in list(options.keys()):
            chars = options['commandchars']
            self.ownerDocument.context.catcode(chars[0], Token.CC_ESCAPE)
            self.ownerDocument.context.catcode(chars[1], Token.CC_BGROUP)
            self.ownerDocument.context.catcode(chars[2], Token.CC_EGROUP)

        # Comment char
        if 'commentchar' in list(options.keys()):
            char = options['commentchar']
            self.ownerDocument.context.catcode(char, Token.CC_COMMENT)

        return self.attributes
