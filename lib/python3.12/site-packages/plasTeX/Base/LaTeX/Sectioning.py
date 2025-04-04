"""
C.4 Sectioning and Table of Contents (p174)

"""

from plasTeX import Command

#
# C.4.1 Sectioning Commands
#

class cachedproperty(object):
    """ Property whose value is only calculated once and cached """
    def __init__(self, func):
        self._func = func
    def __get__(self, obj, type=None):
        if obj is None:
            return self
        try:
            return getattr(obj, '@%s' % self._func.__name__)
        except AttributeError:
            result = self._func(obj)
            setattr(obj, '@%s' % self._func.__name__, result)
            return result


class TableOfContents(object):
    """
    Table of Contents object

    The table of contents object is a proxy object that limits the
    depth of a table of contents entry.  Each time the `tableofcontents'
    attribute is accessed on the given node, the depth level is
    increased.  Once the depth limit has been reached, no more
    table of contents entries are returned.

    """

    def __init__(self, node, limit, level=1):
        """
        Instantiate a table of contents object

        Arguments:
        node -- the node to retrieve the table of contents from
        limit -- the number of levels to display
        level -- the current level

        """
        self._toc_node = node
        self._toc_limit = limit
        self._toc_level = level

    def __getattribute__(self, name):
        """
        Proxy all attributes to the real object except `tableofcontents'

        Each nested call to the tableofcontents should limit the
        depth of the items displayed.

        """
        # Attributes that belong to the ToC object
        if name.startswith('_toc_'):
            return object.__getattribute__(self, name)

        # Limit the number of ToC levels
        if name in ['tableofcontents','fulltableofcontents']:
            if self._toc_level < self._toc_limit:
                return [type(self)(x._toc_node, self._toc_limit,
                        self._toc_level+1) for x in self._toc_node.fulltableofcontents]
            else:
                return []

        # All other attribute accesses get passed on
        return getattr(self._toc_node, name)

class SectionUtils(object):
    """ General utilities for getting information about sections """

    tocdepth = None

    @cachedproperty
    def footnotes(self):
        output = []
        for f in self.ownerDocument.userdata.get('footnotes', []):
            s = f.currentSection
            while s is not None and not s.filename:
                s = s.currentSection
            if s is self:
                output.append(f)
        for i, f in enumerate(output):
            f.mark.attributes['num'] = i+1
        return output

    @cachedproperty
    def subsections(self):
        """ Retrieve a list of all immediate subsections of this section """
        return [x for x in self if x.level < Command.ENDSECTIONS_LEVEL]

    @cachedproperty
    def siblings(self):
        """ Retrieve a list of all sibling sections of this section """
        if not self.parentNode or self.level == Command.DOCUMENT_LEVEL:
            return []
        return [x for x in self.parentNode.subsections if x is not self]

    @cachedproperty
    def tableofcontents(self):
        """ Return a toble of contents object limited to toc-depth """
        if self.tocdepth is not None:
            tocdepth = self.tocdepth
        else:
            tocdepth = self.config['document']['toc-depth']

        # Bail out if they don't want a ToC
        if tocdepth < 1:
            return []

        # Don't create a ToC unless at least one subsection creates a file
        if not [x for x in self.subsections if x.filename]:
            return []

        # Include sections that don't create files in the ToC
        if self.config['document']['toc-non-files']:
            return [TableOfContents(x, tocdepth) for x in self.subsections]

        # Only include sections that create files in the ToC
        return [TableOfContents(x, tocdepth) for x in self.subsections
                                             if x.filename]

    @cachedproperty
    def fulltableofcontents(self):
        """ Return a toble of contents object without limits """
        # Include sections that don't create files in the ToC
        if self.config['document']['toc-non-files']:
            return [TableOfContents(x, 1000) for x in self.subsections]

        # Only include sections that create files in the ToC
        return [TableOfContents(x, 1000) for x in self.subsections
                                             if x.filename]

    @cachedproperty
    def allSections(self):
        """ Retrieve a list of all sections within (and including) this one """
        sections = [self]
        for item in self.subsections:
            sections.extend(item.allSections)
        return sections

    @cachedproperty
    def documentSections(self):
        """ Retrieve a list of all sections in the document """
        document = self
        while document.level is not Command.DOCUMENT_LEVEL:
            document = document.parentNode
            if document is None:
                return []
        return document.allSections

    @cachedproperty
    def links(self):
        """
        Return a dictionary containing a lot of navigation information

        See http://fantasai.tripod.com/qref/Appendix/LinkTypes/ltdef.html

        """
        sections = [x for x in self.documentSections if x.filename]

        breadcrumbs = [self]
        parent = None
        if self.level > Command.DOCUMENT_LEVEL:
            item = parent = self.parentNode
            while item is not None and item.level > Command.DOCUMENT_LEVEL:
                breadcrumbs.append(item)
                item = item.parentNode
            if item is not None:
                breadcrumbs.append(item)
        breadcrumbs.reverse()

        first = top = breadcrumbs[0]
        last = sections[-1]
        prev = next = None
        breaknext = False
        for item in sections:
            if item is self:
                breaknext = True
                continue
            if breaknext:
                next = item
                break
            prev = item

        document = part = chapter = section = subsection = None
        for item in breadcrumbs:
            if item.level == Command.DOCUMENT_LEVEL:
                document = item
            elif item.level == Command.PART_LEVEL:
                part = item
            elif item.level == Command.CHAPTER_LEVEL:
                chapter = item
            elif item.level == Command.SECTION_LEVEL:
                section = item
            elif item.level == Command.SUBSECTION_LEVEL:
                subsection = item

        nav = {}
        nav['home'] = top
        nav['start'] = top
        nav['begin'] = nav['first'] = first
        nav['end'] = nav['last'] = last
        nav['next'] = next
        nav['previous'] = nav['prev'] = prev
        nav['up'] = parent
        nav['top'] = nav['origin'] = top
        nav['parent'] = parent
        nav['child'] = self.subsections
        nav['sibling'] = self.siblings

        # These aren't actually part of the spec, but I added
        # them for consistency.
        nav['document'] = document
        nav['part'] = part

        nav['chapter'] = chapter
        nav['section'] = section
        nav['subsection'] = subsection
        nav['appendix'] = None
        nav['glossary'] = None
        nav['bibliography'] = None
        nav['help'] = None
        nav['navigator'] = top
        nav['toc'] = nav['contents'] = top
        nav['index'] = None
        nav['search'] = None
        nav['bookmark'] = None
        nav['banner'] = None
        nav['copyright'] = None
        nav['trademark'] = None
        nav['disclaimer'] = None
        nav['publisher'] = None
        nav['editor'] = None
        nav['author'] = None
        nav['made'] = None
        nav['meta'] = None
        nav['script'] = None
        nav['stylesheet'] = []
        nav['alternate'] = []
        nav['translation'] = []

        # Additional related entries
        nav['shortcut icon'] = None
        nav['breadcrumbs'] = breadcrumbs

        # Get navigation info from the linkTypes
        navinfo = self.ownerDocument.userdata.get('links', {})
        for key, value in list(navinfo.items()):
            nav[key] = value

        # Get user-defined links
        links = {}
        for key, value in self.config['links']['links'].items():
            newkey, type = key.strip().split('-',1)
            if newkey not in links:
                links[newkey] = {}
            links[newkey][type] = value

        # Set links in nav object
        for key, value in list(links.items()):
            if key not in list(nav.keys()) or nav[key] is None:
                nav[key] = value

        return nav

    def digest(self, tokens):
        # Absorb the tokens that belong to us
#       text = []
        for item in tokens:
#           if item.nodeType == Command.TEXT_NODE:
#               text.append(item)
#               continue
            if item.level <= self.level:
                tokens.push(item)
                break
            if item.nodeType == Command.ELEMENT_NODE:
                item.parentNode = self
                item.digest(tokens)
#           self.appendText(text, self.ownerDocument.charsubs)
            self.appendChild(item)
#       self.appendText(text, self.ownerDocument.charsubs)
        self.paragraphs()


class StartSection(SectionUtils, Command):
    blockType = True
    args = '* [ toc ] title'

class part(StartSection):
    level = Command.PART_LEVEL
    counter = 'part'

class chapter(StartSection):
    level = Command.CHAPTER_LEVEL
    counter = 'chapter'

class section(StartSection):
    level = Command.SECTION_LEVEL
    counter = 'section'

class subsection(StartSection):
    level = Command.SUBSECTION_LEVEL
    counter = 'subsection'

class subsubsection(StartSection):
    level = Command.SUBSUBSECTION_LEVEL
    counter = 'subsubsection'

class paragraph(StartSection):
    level = Command.PARAGRAPH_LEVEL
    counter = 'paragraph'

class subparagraph(StartSection):
    level = Command.SUBPARAGRAPH_LEVEL
    counter = 'subparagraph'

class subsubparagraph(StartSection):
    level = Command.SUBSUBPARAGRAPH_LEVEL
    counter = 'subsubparagraph'

#
# C.4.2 The Appendix
#

class appendix(Command):
    """ This needs to be implemented in the cls file """
    blockType = True

#
# C.4.3 Table of Contents
#

class tableofcontents(Command):
    blockType = True

class listoffigures(Command):
    blockType = True

class listoftables(Command):
    blockType = True

class addcontentsline(Command):
    args = 'file:str level:str text'

class addtocontents(Command):
    args = 'file:str text'

#
# C.4.4 Style Parameters
#
