from plasTeX.Base.LaTeX.Crossref import ref
from plasTeX.Base.LaTeX.Math import equation

from plasTeX.Base.LaTeX.Sectioning import StartSection
from plasTeX.DOM import Node
from typing import Union, Tuple

class CleverRef(ref):
    def refname_raw(self) -> Union[str, Tuple[str, str]]:
        """
        The type of the object being referenced.

        Returns:
        either a string that is the name of the type, or a tuple
        (abbreviated name, unabbreviated name)
        """

        label = self.idref["label"]

        if label.nodeName == "thmenv":
            if isinstance(label.caption, str):
                return label.caption
            else:
                return label.caption.textContent

        if isinstance(label, StartSection):
            if label.level >= Node.SECTION_LEVEL:
                return "section"
            else:
                assert label.counter is not None
                return label.counter

        if isinstance(label, equation):
            return ("eq.", "equation")

        try:
            return label.counter
        except:
            return label.nodeName

class cref(CleverRef):
    def refname(self) -> str:
        name = self.refname_raw()
        if name is None:
            return ""
        if isinstance(name, tuple):
            name = name[0]
        return name[0].lower() + name[1:]

class Cref(CleverRef):
    def refname(self) -> str:
        name = self.refname_raw()
        if name is None:
            return ""
        if isinstance(name, tuple):
            name = name[1]
        return name[0].upper() + name[1:]
