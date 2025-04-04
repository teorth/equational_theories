import sys, re
import builtins
from typing import Optional, NewType, List

NodeType = NewType("NodeType", int)

class DOMString(str):
    """
    DOM String

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-C74D1578
    """

class DOMTimeStamp(int):
    """
    DOM Time Stamp

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#Core-DOMTimeStamp
    """

class DOMUserData(dict):
    """
    DOM User Data

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#Core-DOMUserData
    """
    def setPath(self, path, value):
        """
        Traverse the nested dictionary `d` and set the value

        Arguments:
        path -- a '/' delimited string of keys
        value -- value to set at the last key

        Examples::
        userdata.setPath('packages/graphics/extensions', ['.ps','jpg'])

        See Also:
        getPath()

        """
        keys = path.split('/')
        for key in keys[:-1]:
            if key not in self:
                self[key] = {}
            self = self[key]
        self[keys[-1]] = value

    def getPath(self, path, default=None):
        """
        Return the value of the nested dictionary `d` at the path

        Arguments:
        path -- a '/' delimited string of keys
        default -- value to return if the path doesn't exist

        Examples::
        userdata.getPath('packages/graphics/extensions')

        See Also:
        setPath()

        """
        keys = path.split('/')
        for key in keys[:-1]:
            if key not in self:
                return default
            self = self[key]
        return self.get(keys[-1], default)

class DOMObject(object):
    """
    DOM Object

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#Core-DOMObject
    """

# Exception Code
INDEX_SIZE_ERR                 = 1
DOMSTRING_SIZE_ERR             = 2
HIERARCHY_REQUEST_ERR          = 3
WRONG_DOCUMENT_ERR             = 4
INVALID_CHARACTER_ERR          = 5
NO_DATA_ALLOWED_ERR            = 6
NO_MODIFICATION_ALLOWED_ERR    = 7
NOT_FOUND_ERR                  = 8
NOT_SUPPORTED_ERR              = 9
INUSE_ATTRIBUTE_ERR            = 10
INVALID_STATE_ERR              = 11
SYNTAX_ERR                     = 12
INVALID_MODIFICATION_ERR       = 13
NAMESPACE_ERR                  = 14
INVALID_ACCESS_ERR             = 15
VALIDATION_ERR                 = 16

class DOMException(Exception):
    """
    DOM Exception

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-17189187
    """
    def __init__(self, *args, **kw):
        if self.__class__ is DOMException:
            raise RuntimeError(
                "DOMException should not be instantiated directly")
        Exception.__init__(self, *args, **kw)

    def _get_code(self):
        return self.code

class IndexSizeErr(DOMException):
    code = INDEX_SIZE_ERR

class DomstringSizeErr(DOMException):
    code = DOMSTRING_SIZE_ERR

class HierarchyRequestErr(DOMException):
    code = HIERARCHY_REQUEST_ERR

class WrongDocumentErr(DOMException):
    code = WRONG_DOCUMENT_ERR

class InvalidCharacterErr(DOMException):
    code = INVALID_CHARACTER_ERR

class NoDataAllowedErr(DOMException):
    code = NO_DATA_ALLOWED_ERR

class NoModificationAllowedErr(DOMException):
    code = NO_MODIFICATION_ALLOWED_ERR

class NotFoundErr(DOMException):
    code = NOT_FOUND_ERR

class NotSupportedErr(DOMException):
    code = NOT_SUPPORTED_ERR

class InuseAttributeErr(DOMException):
    code = INUSE_ATTRIBUTE_ERR

class InvalidStateErr(DOMException):
    code = INVALID_STATE_ERR

class SyntaxErr(DOMException):
    code = SYNTAX_ERR

class InvalidModificationErr(DOMException):
    code = INVALID_MODIFICATION_ERR

class NamespaceErr(DOMException):
    code = NAMESPACE_ERR

class InvalidAccessErr(DOMException):
    code = INVALID_ACCESS_ERR

class ValidationErr(DOMException):
    code = VALIDATION_ERR


class _DOMList(list):
    """ Generic List """

    @property
    def length(self):
        return len(self)

    def item(self, i):
        try: return self[i]
        except IndexError: return None


class DOMStringList(_DOMList):
    """
    DOM String List

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#DOMStringList
    """

class NameList(_DOMList):
    """
    Name List

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#NameList
    """
    def getName(self, i):
        try: return self[i]
        except IndexError: return None

    def getNamespaceURI(self, i):
        return None

    def containsNS(self, ns, name):
        if ns: return False
        return self.contains(name)

class NodeList(_DOMList):
    """
    Node List

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-536297177
    """

class DOMImplementationList(_DOMList):
    """
    DOM Implementation List

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#DOMImplementationList
    """

class DOMImplementationSource(object):
    """
    DOM Implementation Source

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#DOMImplementationSource
    """
    def getDOMImplementation(self, features):
        raise NotImplementedError
    def getDOMImplementationList(self, features):
        raise NotImplementedError

class DOMImplementation(object):
    """
    DOM Implementation

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-102161490
    """
    def hasFeature(self, feature, version):
        raise NotSupportedErr

    def createDocumentType(self, qualifiedName, publicId=None, systemId=None):
        raise NotSupportedErr

    def createDocument(self, namespaceURI, qualifiedName, doctype):
        raise NotSupportedErr

    def getFeature(self, feature, version):
        raise NotSupportedErr

class NamedNodeMap(dict):
    """
    DOM Named Node Map

    This class is a Python dictionary that also supports the
    DOM Named Node Map interface.  It is used for the `attributes`
    attribute on Node.  Since LaTeX's attributes are actually
    objects instead of strings, 'parentNode' and 'ownerDocument'
    attributes were also added.  Whenever a new object is added to
    the dictionary, the object's parent and owner are set to
    the parent and owner of this object.

    """

    @property
    def parentNode(self):
        """
        Get/Set the parent node

        Since the children of this object can contain document fragments
        when it is set we have to reset the parentNode of all of
        our children.

        """
        return getattr(self, '_dom_parentNode', None)

    @parentNode.setter
    def parentNode(self, value):
        if getattr(self, '_dom_parentNode', None) is not value:
            self._dom_parentNode = value
            for value in list(self.values()):
                self._resetPosition(value.parentNode)

    @property
    def ownerDocument(self):
        if self.parentNode is not None:
            return self.parentNode.ownerDocument
        return

    def getNamedItem(self, name):
        """
        Get the value for name `name`

        Required Arguments:
        name -- string containing the name of the item

        Returns:
        the value stored in `name`, or None if it doesn't exist

        """
        return self.get(name)

    def setNamedItem(self, arg):
        """
        Add a new item

        Required Arguments:
        arg -- node to add.  The nodeName attribute determines the name
            that it will be store under.

        Returns:
        the node given in `arg`

        """
        self[arg.nodeName] = arg
        return arg

    def removeNamedItem(self, name):
        """
        Remove item by name `name`

        Required Arguments:
        name -- name of the item to remove

        Returns:
        the value at `name`

        """
        try:
            value = self[name]
            del self[name]
        except KeyError:
            raise NotFoundErr('Could not find name "%s"' % name)
        return value

    def item(self, index):
        """
        Return item at index `index`

        Required Arguments:
        index -- the index of the item to return

        Returns:
        the requested value, or None if it doesn't exist

        """
        items = list(self.items())
        items.sort()
        try: return items[num][1]
        except IndexError: return None

    @property
    def length(self):
        """ Return the number of stored items """
        return len(self)

    def getNamedItemNS(self, ns, name):
        """
        Get a named item in a particular namespace

        Required Arguments:
        ns -- the namespace for the item (ignored)
        name -- the name of the item

        Returns:
        the requested value

        """
        return self.getNamedItem(name)

    def setNamedItemNS(self, arg):
        """
        Set a named item in a particular namespace

        Required Arguments:
        arg -- node containing the value to store

        """
        return self.setNamedItem(arg)

    def removeNamedItemNS(self, ns, name):
        """
        Remove a named item in a particular namespace

        Required Arguments:
        ns -- the namespace for the item (ignored)
        name -- the name of the item

        """
        return self.removeNamedItem(name)

    def __setitem__(self, name, value):
        """
        Set the value at name `name` to `value`

        Required Arguments:
        name -- the name to use
        value -- the value to put under `name`

        """
        self._resetPosition(value)
        dict.__setitem__(self, name, value)

    def _resetPosition(self, value, parent=None):
        """
        Set the parent node and owner document of the value

        Required Arguments:
        value -- the object to set the position of

        """
        nodeType = getattr(value, 'nodeType', None)

        if parent is None:
            parent = self.parentNode

        if value is None:
            return

        elif nodeType == Node.DOCUMENT_FRAGMENT_NODE:
            for item in value:
                self._resetPosition(item, parent=value)

        elif nodeType is not None:
            value.parentNode = parent
            value.ownerDocument = self.ownerDocument

        elif isinstance(value, list):
            for item in value:
                self._resetPosition(item)

        elif isinstance(value, dict):
            for item in list(value.values()):
                self._resetPosition(item)

        else:
            if hasattr(value, 'parentNode'):
                value.parentNode = parent
            if hasattr(value, 'ownerDocument'):
                value.ownerDocument = self.ownerDocument

    def update(self, other):
        """
        Merge another named node map into this one

        Required Arguments:
        other -- another instance of a NamedNodeMap

        """
        for key, value in list(other.items()):
            self[key] = value



def _compareDocumentPosition(self, other):
    """
    Compare the position of the current node to `other`

    Required Arguments:
    other -- the node to compare our position against

    Returns:
    DOCUMENT_POSITION_DISCONNECTED -- nodes are disconnected
    DOCUMENT_POSITION_PRECEDING -- `other` precedes this node
    DOCUMENT_POSITION_FOLLOWING -- `other` follows this node
    DOCUMENT_POSITION_CONTAINS -- `other` contains this node
    DOCUMENT_POSITION_CONTAINED_BY -- `other` is contained by this node
    DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC -- unknown

    """
    if self.ownerDocument is not other.ownerDocument:
        return Node.DOCUMENT_POSITION_DISCONNECTED

    if self.previousSibling is other:
        return Node.DOCUMENT_POSITION_PRECEDING

    if self.nextSibling is other:
        return Node.DOCUMENT_POSITION_FOLLOWING

    if self is other:
        return Node.DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC

    sparents = []
    parent = self
    while parent is not None:
        if parent is other:
            return Node.DOCUMENT_POSITION_CONTAINS
        sparents.append(parent)
        parent = parent.parentNode

    oparents = []
    parent = other
    while parent is not None:
        if parent is self:
            return Node.DOCUMENT_POSITION_CONTAINED_BY
        oparents.append(parent)
        parent = parent.parentNode

    sparents.reverse()
    oparents.reverse()

    for i, sparent in enumerate(sparents):
        for j, oparent in enumerate(oparents):
            if sparent is oparent:
                s = sparents[i+1]
                o = oparents[j+1]
                for item in sparent:
                   if item is s:
                       return Node.DOCUMENT_POSITION_FOLLOWING
                   if item is o:
                       return Node.DOCUMENT_POSITION_PRECEDING

    return Node.DOCUMENT_POSITION_DISCONNECTED


def _previousSibling(self):
    """
    Return the previous sibling

    NOTE: This is fairly inefficient.  The reason that it has
    to be done this way is because Text nodes are a subclass of
    `str` which is an immutable object.  This means that
    we can't have two references to the same Text object (i.e.
    `previousSibling` and `nextSibling` can't be variables).

    """
    if not self.parentNode:
        return None
    previous = None
    for i, item in enumerate(self.parentNode):
        if item is self:
            return previous
        previous = item
    return None


def _nextSibling(self):
    """
    Return the next sibling

    NOTE: This is fairly inefficient.  The reason that it has
    to be done this way is because Text nodes are a subclass of
    `str` which is an immutable object.  This means that
    we can't have two references to the same Text object (i.e.
    `previousSibling` and `nextSibling` can't be variables).

    """
    if not self.parentNode:
        return None
    next = False
    for i, item in enumerate(self.parentNode):
        if next:
            return item
        if item is self:
            next = True
    return None

def xmlstr(obj):
    """ Escape special characters to create a legal xml string """
    if isinstance(obj, str):
        return obj.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')
    elif isinstance(obj, list):
        return str([xmlstr(x) for x in obj])
    elif isinstance(obj, dict):
        return str(dict([(xmlstr(x),xmlstr(y)) for x,y in list(obj.items())]))
    else:
        return xmlstr(str(obj))

class Node(object):
    """
    Node

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-1950641247
    """
#
# LaTeX Node extensions
#
    # LaTeX document hierarchy
    DOCUMENT_LEVEL = -sys.maxsize
    VOLUME_LEVEL = -2
    PART_LEVEL = -1
    CHAPTER_LEVEL = 0
    SECTION_LEVEL = 1
    SUBSECTION_LEVEL = 2
    SUBSUBSECTION_LEVEL = 3
    PARAGRAPH_LEVEL = 4
    SUBPARAGRAPH_LEVEL = 5
    SUBSUBPARAGRAPH_LEVEL = 6
    ENDSECTIONS_LEVEL = 100
    PAR_LEVEL = 101
    ENVIRONMENT_LEVEL = 201
    CHARACTER_LEVEL = COMMAND_LEVEL = 1001

    level = CHARACTER_LEVEL    # Document hierarchy level of the node
    blockType = False     # Indicates that this node is a block-level element
                          # (i.e. should not be in a paragraph)
    contextDepth = 1000   # TeX context level of this node (used during digest)

#
# End LaTeX Node extensions
#

    ELEMENT_NODE = NodeType(1)
    ATTRIBUTE_NODE = NodeType(2)
    TEXT_NODE = NodeType(3)
    CDATA_SECTION_NODE = NodeType(4)
    ENTITY_REFERENCE_NODE = NodeType(5)
    ENTITY_NODE = NodeType(6)
    PROCESSING_INSTRUCTION_NODE = NodeType(7)
    COMMENT_NODE = NodeType(8)
    DOCUMENT_NODE = NodeType(9)
    DOCUMENT_TYPE_NODE = NodeType(10)
    DOCUMENT_FRAGMENT_NODE = NodeType(11)
    NOTATION_NODE = NodeType(12)

    DOCUMENT_POSITION_DISCONNECTED = 0x01
    DOCUMENT_POSITION_PRECEDING = 0x02
    DOCUMENT_POSITION_FOLLOWING = 0x04
    DOCUMENT_POSITION_CONTAINS = 0x08
    DOCUMENT_POSITION_CONTAINED_BY = 0x10
    DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC = 0x20

    NODE_SLOTS = ['parentNode','contextDepth','ownerDocument',
                  '_dom_childNodes','_dom_userdata']
    ELEMENT_SLOTS = NODE_SLOTS + ['_dom_attributes','nodeName']
    TEXT_SLOTS = ['parentNode','contextDepth','ownerDocument','isMarkup']

    __slots__ = []

    isElementContentWhitespace = False

    namespaceURI = None
    prefix = None
    localName = None
    baseURI = None

    nodeName = None # type: Optional[str]
    nodeValue = None # type: Optional[str]
    nodeType = None # type: Optional[NodeType]
    parentNode = None
    ownerDocument = None # type: Optional[Document]
    attributes = None
    nonNormalizedAttrs = [] # type: List[str]

    str = None # type: Optional[str]

    # String containing type of node relating to navigation.
    # Common values are: glossary, bibliography, contents, index, search, etc.
    linkType = None # type: Optional[builtins.str]

    def toXML(self, debug=False):
        """
        Dump the object as XML

        Returns:
        string in XML format

        """
        # Only the content of DocumentFragments get rendered
        if self.nodeType == Node.DOCUMENT_FRAGMENT_NODE:
            s = []
            for value in self:
                if hasattr(value, 'toXML'):
                    value = value.toXML()
                else:
                    value = xmlstr(value)
                s.append(value)
            return ''.join(s)

        # Remap name into valid XML tag name
        name = self.nodeName
        name = name.replace('@','-')
        name = name.replace('#','dom-')
        if name.startswith('-'):
            name = 'x%s' % name

        modifier = ''
        if '::' in name:
            name, modifier = name.split('::')
            modifier = ' char="%s"' % xmlstr(modifier)
        else:
            modifier = re.search(r'(\W*)$', name).group(1)
            if modifier:
                name = re.sub(r'(\W*)$', r'', name)
                modifier = ' modifier="%s"' % xmlstr(modifier)

        if not name:
            name = 'unknown'

        source = ''
        #source = ' source="%s"' % xmlstr(self.source)

        style = ''
        if hasattr(self, 'style') and self.style:
            style = ' style="%s"' % xmlstr(getattr(self.style, 'inline', self.style))

        ref = ''
        try:
            if self.ref is not None:
                ref = ' ref="%s"' % self.ref.toXML()
        except AttributeError: pass

        label = ''
        try:
            if self.id != ('a%s' % id(self)):
                lid = xmlstr(self.id).strip()
                if lid:
                    label = ' id="%s"' % lid
        except AttributeError: pass

        extra = ''
        if debug:
            extra = ' parentNode="%s" ownerDocument="%s"' % \
                    (id(self.parentNode), id(self.ownerDocument))

        if not self.parentNode:
            extra += ' xmlns:plastex="http://plastex.sf.net/"'

        beginning = False
        if getattr(self, 'macroMode', -2) == getattr(self, 'MODE_BEGIN', -1):
            beginning = True

        ending = ''
        if getattr(self, 'macroMode', -2) == getattr(self, 'MODE_END', -1):
            ending = '/'

        # Bail out early if the element is empty
        if not(self.attributes) and not(self.hasChildNodes()):
            if ending:
                return '</%s%s>' % (name, modifier)
            if beginning:
                return '<%s%s%s%s%s%s%s>' % (name, modifier, style, source, ref, label, extra)

            return '<%s%s%s%s%s%s%s/>' % (name, modifier, style, source, ref, label, extra)

        s = ['<%s%s%s%s%s%s%s%s>\n' % (ending, name, modifier, style, source, ref, label, extra)]

        # Render attributes
        if self.attributes:
            for key, value in self.attributes.items():
                if value is None:
                    s.append('    <plastex:arg name="%s"/>\n' % key)
                elif isinstance(value, dict):
                    newdict = {}
                    for k, v in list(value.items()):
                        if hasattr(v, 'toXML'):
                            newdict[k] = v.toXML()
                        else:
                            newdict[k] = xmlstr(v)
                    s.append('    <plastex:arg name="%s">%s</plastex:arg>\n' % (key, newdict))
                else:
                    if hasattr(value, 'toXML'):
                        value = value.toXML()
                    else:
                        value = xmlstr(value)
                    s.append('    <plastex:arg name="%s">%s</plastex:arg>\n' % (key, value))

        # Render content
        if self.hasChildNodes():
            if not(self.attributes and 'self' in self.attributes):
                for value in self.childNodes:
                    if hasattr(value, 'toXML'):
                        value = value.toXML()
                    else:
                        value = xmlstr(value)
                    s.append(value)

        s.append('</%s>' % name)

        return ''.join(s)

    @property
    def childNodes(self):
        try:
            return self._dom_childNodes
        except AttributeError:
            pass
        # Allow the `self` key of attributes to act as the `childNodes`
        a = self.attributes
        if a and 'self' in a:
            nodes = a['self']
            if nodes is None:
                nodes = []
            self._dom_childNodes = nodes
            return nodes
        else:
            self._dom_childNodes = nodes = []
            return nodes

    def hasChildNodes(self):
        """ Do we have any child nodes? """
        if hasattr(self, '_dom_childNodes'):
            return True
        a = self.attributes
        return a and 'self' in a

    @property
    def firstChild(self):
        """ Return the first child in the list """
        if self.hasChildNodes() and self.childNodes: return self.childNodes[0]

    @property
    def lastChild(self):
        """ Return the last child in the list """
        if self.hasChildNodes() and self.childNodes: return self.childNodes[-1]

    previousSibling = property(_previousSibling)

    nextSibling = property(_nextSibling)

    compareDocumentPosition = _compareDocumentPosition

    def insertBefore(self, newChild, refChild):
        """
        Insert `newChild` before `refChild`

        Required Arguments:
        newChild -- the child to insert
        refChild -- the child that `newChild` should be inserted before

        Returns:
        `newChild`

        """
        try: self.removeChild(newChild)
        except NotFoundErr: pass

        # Insert the new item
        for i, item in enumerate(self):
            if item is refChild:
                self.insert(i, newChild)
                return newChild

        raise NotFoundErr

    def insertAfter(self, newChild, refChild):
        """
        Insert `newChild` after `refChild`

        Required Arguments:
        newChild -- the child to insert
        refChild -- the child that `newChild` should be inserted after

        Returns:
        `newChild`

        """
        try: self.removeChild(newChild)
        except NotFoundErr: pass

        # Insert the new item
        for i, item in enumerate(self):
            if item is refChild:
                self.insert(i+1, newChild)
                return newChild

        raise NotFoundErr

    def replaceChild(self, newChild, oldChild):
        """
        Replace `newChild` with `oldChild`

        Required Arguments:
        newChild -- the child to insert
        oldChild -- the child that `newChild` will replace

        Returns:
        `oldChild`

        """
        try: self.removeChild(newChild)
        except NotFoundErr: pass

        # Do the replacement
        for i, item in enumerate(self):
            if item is oldChild:
                self.pop(i)
                self.insert(i, newChild)
                return oldChild

        raise NotFoundErr

    def removeChild(self, oldChild):
        """
        Remove 'oldChild' from list of children

        Required Arguments:
        oldChild -- the child to remove

        Returns:
        `oldChild`

        """
        for i, item in enumerate(self):
            if item is oldChild:
                return self.pop(i)
        raise NotFoundErr

    remove = removeChild

    def pop(self, index=-1):
        """
        Pop an item from the list

        Required Arguments:
        index -- the index of the item to remove

        Returns:
        the item removed from the list

        """
        try: return self.childNodes.pop(index)
        except: raise IndexError('object has no childNodes')

    def append(self, newChild, setParent=True):
        """
        Append `newChild` to child list

        Required Arguments:
        newChild -- the child to add

        Returns:
        `newChild`

        """

        if type(newChild) == str:
            newChild = self.ownerDocument.createTextNode(newChild)
        if newChild.nodeType == Node.DOCUMENT_FRAGMENT_NODE:
            for item in newChild:
                self.append(item, setParent=setParent)
        else:
            self.childNodes.append(newChild)

        if setParent:
            if self.nodeType == self.DOCUMENT_FRAGMENT_NODE:
                newChild.parentNode = self.parentNode
            else:
                newChild.parentNode = self
        newChild.ownerDocument = self.ownerDocument
        return newChild

    appendChild = append

    def insert(self, i, newChild, setParent=True):
        """
        Insert `newChild` into child list at position `i`

        Required Arguments:
        i -- the position to insert the new child
        newChild -- the object to insert

        Returns:
        `newChild`

        """
        if type(newChild) == str:
            newChild = self.ownerDocument.createTextNode(newChild)
        if newChild.nodeType == Node.DOCUMENT_FRAGMENT_NODE:
            for item in newChild:
                self.insert(i, item, setParent=setParent)
                i += 1
        else:
            self.childNodes.insert(i, newChild)
        if setParent:
            if self.nodeType == self.DOCUMENT_FRAGMENT_NODE:
                newChild.parentNode = self.parentNode
            else:
                newChild.parentNode = self
        newChild.ownerDocument = self.ownerDocument
        return newChild

    def __setitem__(self, i, node):
        """
        Set the item at index `i` to `node`

        Required Arguments:
        i -- the index to set the item of
        node -- the object to put at that index

        """
        if type(node) == str:
            node = self.ownerDocument.createTextNode(node)
        # If a DocumentFragment is being inserted, but it isn't replacing
        # a slice, we need to put each child in manually.
        if node.nodeType == Node.DOCUMENT_FRAGMENT_NODE \
           and not(isinstance(i, slice)):
            for item in node:
                self.insert(i, item)
                i += 1
            self.pop(i)

        else:
            self.insert(i, node)
            self.pop(i+1)

    def extend(self, other, setParent=True):
        """ self += other """
        for item in other:
            self.append(item, setParent=setParent)
        return self

    __iadd__ = extend

    def appendText(self, text, charsubs=None, setParent=True):
        """ Append a list of text nodes as one node """
        charsubs = charsubs or []
        if not text:
            return
        value = ''.join(text)
        for src, dest in charsubs:
            value = value.replace(src, dest)
        text[:] = []
        value = self.ownerDocument.createTextNode(value)
        if setParent:
            value.parentNode = self
        value.ownerDocument = self.ownerDocument
        self.appendChild(value)

    def __radd__(self, other):
        """ other + self """
        obj = type(self)()
        obj.ownerDocument = self.ownerDocument
        obj.parentNode = None
        for item in other:
            obj.append(item)
        for item in self:
            obj.append(item)
        return obj

    def __add__(self, other):
        """ self + other """
        obj = type(self)()
        obj.ownerDocument = self.ownerDocument
        obj.parentNode = None
        for item in self:
            obj.append(item)
        for item in other:
            obj.append(item)
        return obj

    def cloneNode(self, deep=False):
        """
        Clone the current node

        Required Arguments:
        deep -- boolean indicating if the copy is a deep copy

        Returns:
        new node

        """
        node = type(self)()
        try: node.nodeName = self.nodeName
        except: pass
#       node.nodeValue = self.nodeValue
#       node.nodeType = self.nodeType
        node.parentNode = self.parentNode
        node.ownerDocument = self.ownerDocument
        if deep:
            if node.attributes is not None and self.attributes is not None:
                node.attributes.update(self.attributes)
            if self.hasChildNodes():
                for x in self.childNodes:
                    node.append(x.cloneNode(deep))
        else:
            if node.attributes is not None and self.attributes is not None:
                node.attributes.update(self.attributes)
            if self.hasChildNodes():
                for x in self.childNodes:
                    node.append(x)
        return node

    def normalize(self, charsubs=None):
        """
        Combine consecutive text nodes and remove comments

        Keyword Arguments:
        charsubs -- a list of two-element tuples that contain string
            replacements.  The first element in each tuple is the source
            string.  The second element is the string to convert the
            source to.

        """
        charsubs = charsubs or []

        if self.hasAttributes():
            for key, value in self.attributes.items():
                if isinstance(value, Node) and key not in self.nonNormalizedAttrs:
                    value.normalize(charsubs)

        if not self.hasChildNodes():
            return

        nodes = list(self.childNodes)
        while self.childNodes:
            self.childNodes.pop()
        text = []
        for item in nodes:
            if item.nodeType == item.TEXT_NODE:
                text.append(item)
                continue
            self.appendText(text, charsubs)
            self.appendChild(item)
            item.normalize(charsubs)
        self.appendText(text, charsubs)

    def isSupported(self, feature, version):
        """ Is the requested feature supported? """
        return True

    def hasAttributes(self):
        """ Are there any attributes set? """
        return bool(self.attributes)

    @property
    def textContent(self):
        """ Get the text content of the current node """
        output = []
        if getattr(self, 'str', None) is not None:
            output.append(self.str)
        else:
            for item in self:
                if item.nodeType == Node.TEXT_NODE:
                    output.append(item)
                elif getattr(item, 'str', None) is not None:
                    output.append(item.str)
                else:
                    output.append(item.textContent)
        if self.ownerDocument is not None:
            return self.ownerDocument.createTextNode(''.join(output))
        else:
            return Text(''.join(output))

    def isSameNode(self, other):
        """ Is this the same node as `other`? """
        return other is self

    def lookupPrefix(self, ns):
        """ Lookup the prefix for the given namespace """
        return None

    def isDefaultNamespace(self, ns):
        """
        Is `ns` the default namespace?

        Required Arguments:
        ns -- requested namespace

        Returns:
        boolean indicating whether this is the default namespace or not

        """
        if ns is None: return True
        return False

    def lookupNamespaceURI(self, ns):
        """
        Lookup the namespace URI for `ns`

        Required Arguments:
        ns -- the namespace to lookup

        Returns:
        the namespace URI

        """
        return None

    def isEqualNode(self, other):
        """ Is this node equivalent to `other`? """
        return other == self

    def __eq__(self, other):
        try:
            return (self.nodeName == other.nodeName and
                    self.attributes == other.attributes and
                    self.childNodes == other.childNodes)
        except:
            return False

    def __hash__(self):
        return id(self)

    def __lt__(self, other):
        try:
            res = self.nodeName < other.nodeName
            if res: return res
            res = self.attributes < other.attributes
            if res: return res
            if self.hasChildNodes() and other.hasChildNodes():
                return self.childNodes < other.childNodes
        except (AttributeError, TypeError):
            pass
        return self.nodeName < other.nodeName

    def getFeature(self, feature, version):
        """ Get the requested feature """
        return None

    def setUserData(self, key, data, handler=None):
        """
        Set user data

        Required Arguments:
        key -- the name to store the data under
        data -- the data to store

        Keyword Arguments:
        handler -- data handler

        """
        self.userdata[key] = data

    def getUserData(self, key):
        """
        Get the user data at `key`

        Required Arguments:
        key -- the name of the data entry to get

        Returns:
        the stored value, or None if it wasn't set

        """
        try: return self.userdata[key]
        except (AttributeError, KeyError): pass
        return None

    @property
    def userdata(self):
        try:
            return self._dom_userdata
        except AttributeError:
            pass
        userdata = DOMUserData()
        self._dom_userdata = userdata
        return userdata

    def __iter__(self):
        if self.hasChildNodes():
            return iter(self.childNodes)
        return iter([])

    def __len__(self):
        if self.hasChildNodes():
            return len(self.childNodes)
        return 0

    def __getitem__(self, i):
        if self.hasChildNodes():
            return self.childNodes[i]
        raise IndexError('object has no childNodes')

    @property
    def allChildNodes(self):
        """ Return a list containing all of the child nodes in the branch """
        nodes = []
        if not self.hasChildNodes():
            return nodes
        for child in self.childNodes:
            nodes.append(child)
            nodes.extend(child.allChildNodes)
        return nodes

def _getElementsByTagName(self, tagname):
    """
    Get a list of nodes with the given name

    Required Arguments:
    tagname -- the name or list of names of the elements to find

    Returns:
    list of elements

    """
    output = NodeList()

    # Allow a list of names
    if not isinstance(tagname, (tuple,list)):
        tagname = [tagname]

    # Look in attributes dictionary for document fragments as well
    if self.attributes and list(self.attributes.keys()):
        for item in list(self.attributes.values()):
            if getattr(item, 'tagName', None) in tagname:
                 output.append(item)
            if hasattr(item, 'getElementsByTagName'):
                output += item.getElementsByTagName(tagname)
            elif isinstance(item, list):
                for e in item:
                    if getattr(e, 'tagName', None) in tagname:
                        output.append(e)
                    if hasattr(item, 'getElementsByTagName'):
                        output += item.getElementsByTagName(tagname)
            elif isinstance(item, dict):
                for e in list(item.values()):
                    if getattr(e, 'tagName', None) in tagname:
                        output.append(e)
                    if hasattr(item, 'getElementsByTagName'):
                        output += item.getElementsByTagName(tagname)

    # Now look in the child elements
    for item in self:
        if getattr(item, 'tagName', None) in tagname:
            output.append(item)
        if hasattr(item, 'getElementsByTagName'):
            output += item.getElementsByTagName(tagname)

    return output


def _getElementById(self, elementId):
    """
    Get element with the given ID

    Required Arguments:
    elementId -- ID of the element to find

    Returns:
    element with the given ID

    """
    # Look in attributes dictionary for document fragments as well
    if getattr(self, 'attributes', None):
        for item in list(self.attributes.values()):
            if id(item) == elementId:
                 return item
            if hasattr(item, 'getElementById'):
                e = item.getElementsById(elementId)
                if e is not None:
                    return e
            elif isinstance(item, list):
                for e in item:
                    if id(e) == elementId:
                        return e
                    if hasattr(item, 'getElementById'):
                        e = item.getElementById(elementId)
                        if e is not None:
                            return e
            elif isinstance(item, dict):
                for e in list(item.values()):
                    if id(e) == elementId:
                        return e
                    if hasattr(item, 'getElementById'):
                        e = item.getElementById(elementId)
                        if e is not None:
                            return e

    # Now look in the child elements
    for item in self:
        if id(item) == elementId:
            return item
        if hasattr(item, 'getElementById'):
            e = item.getElementById(elementId)
            if e is not None:
                return e

    return None

class DocumentFragment(Node):
    """
    Document Fragment

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-B63ED1A3
    """
    nodeName = '#document-fragment'
    nodeType = Node.DOCUMENT_FRAGMENT_NODE
    __slots__ = Node.NODE_SLOTS

    def getElementsByTagNameNS(self, namespaceURI, localName):
        """
        Get list of elements of a specific name and namespace

        Required Arguments:
        namespaceURI -- namespace of the element
        localName -- name of the element to find

        Returns:
        list of elements

        """
        return self.getElementsByTagName(localName)

    getElementById = _getElementById

    getElementsByTagName = _getElementsByTagName

class Attr(Node):
    """
    Attr

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-637646024
    """
    nodeType = Node.ATTRIBUTE_NODE
#   __slots__ = Node.NODE_SLOTS + ['name']

    name = None # type: Optional[str]
    specified = None
    value = None # type: Optional[str]
    ownerElement = None
    schemaTypeInfo = None
    isId = None

    def __repr__(self):
        return '<%s attribute at 0x%s>' % (self.nodeName, id(self))

    @property # type: ignore # mypy#4125
    def nodeName(self) -> Optional[str]: # type: ignore # mypy#4125
        return self.name

    @nodeName.setter
    def nodeName(self, value):
        self.name = value

    @property # type: ignore # mypy#4125
    def nodeValue(self):
        return self.value

    @nodeValue.setter
    def nodeValue(self, value):
        self.value = value

class Element(Node):
    """
    Element

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-745549614
    """
    nodeType = Node.ELEMENT_NODE
#   __slots__ = Node.ELEMENT_SLOTS

    def __repr__(self):
        return '<%s element at 0x%s>' % (self.nodeName, id(self))

    @property
    def attributes(self):
        try:
            return self._dom_attributes
        except AttributeError:
            pass
        nnm = NamedNodeMap()
        nnm.parentNode = self
        self._dom_attributes = nnm
        return nnm

    @property
    def tagName(self):
        return self.nodeName

    @tagName.setter
    def tagName(self, value):
        self.nodeName = value

    def getAttribute(self, name):
        """
        Get attribute with name `name`

        Required Arguments:
        name -- name of attribute to retrieve

        Returns:
        value of attribute, or None if it doesn't exist

        """
        return self.attributes.get(name)

    def setAttribute(self, name, value):
        """
        Set attribute

        Required Arguments:
        name -- name of attribute to set
        value -- value to set the attribute to

        """
        self.attributes[name] = value

    def removeAttribute(self, name):
        """
        Remove attribute

        Required Arguments:
        name -- name of attribute to remove

        """
        try: del self.attributes[name]
        except KeyError: pass

    getAttributeNode = getAttribute

    def setAttributeNode(self, newAttr):
        """
        Set an attribute node

        Required Arguments:
        newAttr -- attribute node

        """
        self.setAttribute(newAttr.name, newAttr)

    def removeAttributeNode(self, oldAttr):
        """
        Remove an attribute node

        Required Arguments:
        oldAttr -- attribute node to remove

        """
        self.removeAttribute(oldAttr.name)

    getElementsByTagName = _getElementsByTagName

    def getAttributeNS(self, namespaceURI, localName):
        """
        Get attribute in given namespace

        Required Arguments:
        namespaceURI -- namespace of attribute
        localName -- name of attribute

        Returns:
        attribute

        """
        return self.getAttribute(localName)

    def setAttributeNS(self, namespaceURI, qualifiedName, value):
        """
        Set an attribute with given namespace

        Required Argument:
        namespaceURI -- namespace of attribute
        qualifiedName -- name of attribute
        value -- value of the attribute

        """
        return self.setAttribute(qualifiedName, value)

    def removeAttributeNS(self, namespaceURI, localName):
        """
        Remove an attribute in the given namespace

        Required Arguments:
        namespaceURI -- namespace of attribute
        localName -- name of attribute

        """
        return self.removeAttribute(localName)

    def getAttributeNodeNS(self, namespaceURI, localName):
        """
        Get attribute from given namespace

        Required Arguments:
        namespaceURI -- namespace of attribute
        localName -- name of attribute

        Returns:
        attribute node

        """
        return self.getAttributeNode(localName)

    setAttributeNodeNS = setAttributeNode

    def getElementsByTagNameNS(self, namespaceURI, localName):
        """
        Get elements with tag name in given namespace

        Required Arguments:
        namespaceURI -- namespace of element
        localName -- name of element to retrieve

        Returns:
        list of elements

        """
        return _getElementsByTagName(localName)

    def hasAttribute(self, name):
        """
        Does the attribute exist?

        Required Arguments:
        name -- name of attribute to look for

        Returns:
        boolean indicating whether or not the attribute exists

        """
        return name in list(self.attributes.keys())

    def hasAttributeNS(self, namespaceURI, localName):
        """
        Does the attribute in the given namespace exist

        Required Arguments:
        namespaceURI -- namespace of attribute
        localName -- name of attribute

        Returns:
        boolean indicating whether or not the attribute exists

        """
        return self.hasAttribute(localName)

    def setIdAttribute(self, name, isId=True):
        """
        Set attribute as an ID attribute

        Required Arguments:
        name -- name of attribute

        Keyword Arguments:
        isId -- boolean indicating whether this attribute should be an
            ID attribute or not

        """
        try: self.attributes[name].isId = isId
        except KeyError: raise NotFoundErr

    def setIdAttributeNS(self, namespaceURI, localName, isId=True):
        """
        Set attribute as an ID attribute in the given namespace

        Required Arguments:
        namespaceURI -- namespace of attribute
        localName -- name of attribute

        Keyword Arguments:
        isId -- boolean indicating whether this attribute should be an
            ID attribute or not

        """
        self.setIdAttribute(localName, isId)

    def setIdAttributeNode(self, idAttr, isId=True):
        """
        Set attribute node as an ID attribute node

        Required Arguments:
        idAttr -- attribute node

        Keyword Arguments:
        isId -- boolean indicating whether this attribute should be an
            ID attribute or not

        """
        self.setIdAttribute(idAttr.name, isId)


class CharacterData(str, Node):
    """
    Character Data

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-FF21A306

    This class doesn't follow the entire API. Because it is also
    a subclass of str it is immutable making methods like insertData,
    deleteData, etc. impossible.

    """
    __slots__ = Node.TEXT_SLOTS

    _dummyChildNodes = []

    @property
    def childNodes(self):
        return CharacterData._dummyChildNodes

    # LaTeX extension that allows getting the LaTeX source from a plain string
    @property
    def source(self):
        return self

    @property
    def str(self):
        return self

    def toXML(self, *args, **kwargs):
        return xmlstr(self)

    @property
    def nodeValue(self):
        return self

    def cloneNode(self, deep=True):
        o = type(self)(self)
        o.ownerDocument = self.ownerDocument
        o.parentNode = self.parentNode
        return o

    @property
    def data(self):
        return self

    @property
    def length(self):
        """ Number of characters in string """
        return len(self)

    def _notImplemented(self, *args, **kwargs):
        raise NotImplementedError

    substringData = _notImplemented
    appendData = _notImplemented
    insertData = _notImplemented
    deleteData = _notImplemented
    replaceData = _notImplemented
    insertBefore = _notImplemented
    replaceChild = _notImplemented
    removeChild = _notImplemented
    appendChild = _notImplemented

    def normalize(self, charsubs=None):
        pass

    @property
    def textContent(self):
        return self

    def getElementsByTagName(self, name):
        return []

    def __add__(self, other):
        return str.__add__(self, other)

    def __radd__(self, other):
        return other.__add__(self)

    def __len__(self):
        return str.__len__(self)

    def __iter__(self):
        for i in range(len(self)):
            yield self[i]

    def __getitem__(self, i):
        return str.__getitem__(self, i)

    def __str__(self):
        return self

class Text(CharacterData):
    """
    Text

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-1312295772
    """
    nodeName = '#text'
    nodeType = Node.TEXT_NODE
    __slots__ = Node.TEXT_SLOTS

    replaceWholeText = CharacterData._notImplemented
    splitText = CharacterData._notImplemented

    @property
    def isElementContentWhitespace(self):
        return not(self.strip())

    @property
    def wholeText(self):
        """ Return text from siblings and self """
        return self.parentNode.textContent



class TypeInfo(object):
    """
    Type Info

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#TypeInfo
    """

    # DerivationMethods
    DERIVATION_RESTRICTION = 0x00000001
    DERIVATION_EXTENSION = 0x00000002
    DERIVATION_UNION = 0x00000004
    DERIVATION_LIST = 0x00000008

    typeName = None
    typeNamespace = None

    def isDerivedFrom(self, typeNamespaceArg, typeNameArg, derivationMethod):
        raise NotImplementedError


class UserDataHandler(object):
    """
    User Data Handler

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#UserDataHandler
    """

    # OperationType
    NODE_CLONED = 1
    NODE_IMPORTED = 2
    NODE_DELETED = 3
    NODE_RENAMED = 4
    NODE_ADOPTED = 5

    def handle(self, operation, key, data, src, dst):
        raise NotImplementedError


class DOMError(object):
    """
    DOM Error

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ERROR-Interfaces-DOMError
    """

    # ErrorSeverity
    SEVERITY_WARNING = 1
    SEVERITY_ERROR = 2
    SEVERITY_FATAL_ERROR = 3

    severity = None
    message = None
    type = None
    relatedException = None
    relatedData = None
    location = None


class DOMErrorHandler(object):
    """
    DOM Error Handler

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ERROR-Interfaces-DOMErrorHandler
    """
    def handleError(self, error):
        raise NotImplementedError


class DOMLocator(object):
    """
    DOM Locator

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#Interfaces-DOMLocator
    """
    lineNumber = 0
    columnNumber = 0
    byteOffset = 0
    utf16Offset = 0
    relatedNode = None
    uri = None


class DOMConfiguration(dict):
    """
    DOM Configuration

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#DOMConfiguration
    """

    def __init__(self, data=None):
        dict.__init__(self, data or {})
        self['canonical-form'] = False
        self['cdata-sections'] = True
        self['check-character-normalization'] = False
        self['comments'] = True
        self['datatype-normalization'] = False
        self['element-content-whitespace'] = True
        self['entities'] = True
        self['error-handler'] = DOMErrorHandler()
        self['infoset'] = True
        self['namespaces'] = True
        self['namespace-declarations'] = True
        self['normalize-characters'] = False
        self['schema-location'] = None
        self['schema-type'] = None
        self['split-cdata-sections'] = True
        self['validate'] = False
        self['validate-if-schema'] = False
        self['well-formed'] = True

    @property
    def parameterNames(self):
        """ Return list of all possible parameter names """
        return list(self.keys())

    def setParameter(self, name, value):
        """
        Set the given parameter

        Required Arguments:
        name -- name of parameter
        value -- value of parameter

        """
        if name in list(self.keys()):
            raise NotFoundErr
        self[name] = value

    def getParameter(self, name):
        """
        Get the specified paramater value

        Required Arguments:
        name -- name of parameter

        Returns:
        value of parameter `name`

        """
        try: return self[name]
        except KeyError: raise NotFoundErr

    def canSetParameter(self, name, value):
        """
        Can the parameter `name` be set to `value`?

        Required Arguments:
        name -- name of parameter
        value -- value of parameter

        Returns:
        boolean indicating whether the parameter value can be set or not

        """
        return True


class CDATASection(Text):
    """
    CDATA Section

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-667469212
    """
    nodeName = '#cdata-section'
    nodeType = Node.CDATA_SECTION_NODE
    __slots__ = Node.TEXT_SLOTS


class DocumentType(Node):
    """
    Document Type

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-412266927
    """
    nodeType = Node.DOCUMENT_TYPE_NODE
    __slots__ = Node.NODE_SLOTS

    name = None
    entities = None
    notations = None
    publicId = None
    systemId = None
    internalSubset = None

    @property # type: ignore # mypy#4125
    def nodeName(self):
        return self.name

    @nodeName.setter
    def nodeName(self, value):
        self.name = value


class Notation(Node):
    """
    Notation

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-5431D1B9
    """
    nodeType = Node.NOTATION_NODE
    __slots__ = Node.NODE_SLOTS

    publicId = None
    systemId = None


class Entity(Node):
    """
    Entity

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-527DCFF2
    """
    nodeType = Node.ENTITY_NODE
    __slots__ = Node.NODE_SLOTS

    publicId = None
    systemId = None
    notationName = None
    inputEncoding = None
    xmlEncoding = None
    xmlVersion = None


class EntityReference(Node):
    """
    Entity Reference

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-11C98490
    """
    nodeType = Node.ENTITY_REFERENCE_NODE
    __slots__ = Node.NODE_SLOTS


class ProcessingInstruction(Node):
    """
    Processing Instruction

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#ID-1004215813
    """
    nodeType = Node.PROCESSING_INSTRUCTION_NODE
    __slots__ = Node.NODE_SLOTS

    target = None # type: Optional[str]
    data = None # type: Optional[str]

    @property # type: ignore # mypy#4125
    def nodeName(self):
        return self.target

    @nodeName.setter
    def nodeName(self, value):
        self.target = value

    @property # type: ignore # mypy#4125
    def nodeValue(self):
        return self.data

    @nodeName.setter
    def nodeValue(self, value):
        self.data = value

class Document(Node):
    """
    Document

    http://www.w3.org/TR/2004/REC-DOM-Level-3-Core-20040407/core.html#i-Document

    """

    elementClass = Element
    documentFragmentClass = DocumentFragment
    textNodeClass = Text
    cdataSectionClass = CDATASection
    processingInstructionClass = ProcessingInstruction
    attributeClass = Attr
    entityReferenceClass = EntityReference

    nodeName = '#document'
    nodeType = Node.DOCUMENT_NODE
    #__slots__ = Node.NODE_SLOTS

    doctype = None
    implementation = None
    documentElement = None
    inputEncoding = None
    xmlEncoding = None
    xmlStandalone = None
    xmlVersion = None
    strictErrorChecking = None
    documentURI = None
    domConfig = None

    @property
    def parentNode(self):
        return None

    @property
    def ownerDocument(self):
        return self

    def createElement(self, tagName):
        """
        Instantiate a new element

        Required Arguments:
        tagName -- the name of the element to create

        Returns:
        the new instance

        """
        o = self.elementClass()
        o.nodeName = tagName
        o.parentNode = None
        o.ownerDocument = self
        return o

    def createDocumentFragment(self):
        """ Instantiate a new document fragment """
        o = self.documentFragmentClass()
        o.ownerDocument = self
        o.parentNode = None
        return o

    def createTextNode(self, data):
        """
        Instantiate a new text node

        Required Arguments:
        data -- string to initialize text node with

        Returns:
        new text node

        """
        o = self.textNodeClass(data)
        o.ownerDocument = self
        o.parentNode = None
        return o

    def createCDATASection(self, data):
        """
        Instantiate a new CDATA section

        Required Arguments:
        data -- string to initialize CDATA section with

        Returns:
        new CDATA section node

        """
        o = self.cdataSectionClass(data)
        o.ownerDocument = self
        o.parentNode = None
        return o

    def createProcessingInstruction(self, target, data):
        """
        Instantiate a new processing instruction node

        Required Arguments:
        target --
        data -- string to initialize processing instruction with

        Returns:
        new processing instruction node

        """
        o = self.processingInstructionClass(data)
        o.ownerDocument = self
        o.parentNode = None
        return o

    def createAttribute(self, name):
        """
        Instantiate a new attribute node

        Required Arguments:
        name -- name of attribute

        Returns:
        new attribute node

        """
        o = self.attributeClass()
        o.name = name
        o.ownerDocument = self
        o.parentNode = None
        return o

    def createEntityReference(self, name):
        """
        Instantiate a new entity reference

        Required Arguments:
        name -- name of entity

        Returns:
        new entity reference node

        """
        o = self.entityReferenceClass()
        o.name = name
        o.ownerDocument = self
        o.parentNode = None
        return o

    getElementsByTagName = _getElementsByTagName

    def importNode(self, importedNode, deep=False):
        """
        Import a node from another document

        Required Arguments:
        importedNode -- node to import

        Keyword Arguments:
        deep -- boolean indicating whether this should be a deep copy

        Returns:
        imported node

        """
        node = importedNode.cloneNode(deep)
        node.parentNode = self
        node.ownerDocument = self
        return node

    def createElementNS(self, namespaceURI, qualifiedName):
        """
        Create an element in the given namespace

        Required Arguments:
        namespaceURI -- namespace of the new element
        qualifiedName -- name of the element

        Returns:
        new element node

        """
        return self.createElement(qualifiedName)

    def createAttributeNS(self, namespaceURI, qualifiedName):
        """
        Create attribute in the given namespace

        Required Arguments:
        namespaceURI -- namespace of the attribute
        qualifiedName -- name of the attribute

        Returns:
        new attribute node

        """
        return self.createAttribute(qualifiedName)

    def getElementsByTagNameNS(self, namespaceURI, localName):
        """
        Get list of elements of a specific name and namespace

        Required Arguments:
        namespaceURI -- namespace of the element
        localName -- name of the element to find

        Returns:
        list of elements

        """
        return self.getElementsByTagName(localName)

    getElementById = _getElementById

    def adoptNode(self, source):
        """
        Adopt node into document

        Required Arguments:
        source -- node to adopt

        Returns:
        `source`

        """
        if source.parentNode is not None:
            for i, item in enumerate(source.parentNode):
                if item is source:
                    source.parentNode.pop(i)
        self.append(source)
        return source

    normalizeDocument = Node.normalize

    def renameNode(self, n, namespaceURI, qualifiedName):
        """
        Rename a node

        Required Arguments:
        n -- node to rename
        namespaceURI -- namespace to use
        qualifiedName -- name to change to

        Returns:
        `n`

        """
        raise NotImplementedError
