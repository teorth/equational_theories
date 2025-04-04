from argparse import _ArgumentGroup as ArgumentGroup, ArgumentParser
from abc import ABC, abstractmethod
from typing import Dict, List, Generic, TypeVar, Any, Optional, Type, KeysView, Union
from configparser import ConfigParser
import shlex
from collections.abc import Sequence

T = TypeVar('T')

def formatDefault(s: Any):
    return " [" + str(s).replace("%", "%%") + "]"

class ConfigOption(Generic[T]):
    def __init__(self, description: str, options: str, default: T):
        self.description = description
        self.options = options.split(" ")
        self.name = self.options[0].lstrip("-")
        self.value = default

    def registerArgparse(self, group: ArgumentGroup):
        """
        adds an argument to the `ArgumentGroup` corresponding to this
        configuration option.
        """
        group.add_argument(*self.options, dest=self.name, type=self.valueType(), help=self.description + formatDefault(self.value))

    def valueType(self) -> Type:
        """
        helper function that indicates the type of the option. Since
        configuration options usually come in the form of strings, this is used
        to convert a string into the appropriate type in the default
        implementations of `registerArgparse` and `setFromString`.
        """
        return type(self.value)

    def updateFromDict(self, data: Dict[str, Any]):
        """
        sets the config values based on the parsed command line options. `data`
        is the dict returned by `vars(ArgumentParser.parse_args))`. It should
        read back the argument that was set by `registerArgparse.
        """
        value = data.get(self.name)
        if value is not None:
            self.value = value

    def setFromString(self, string: str):
        self.value = self.valueType()(string)

class BooleanOption(ConfigOption[bool]):
    def registerArgparse(self, group: ArgumentGroup):
        enables = [x for x in self.options if x[0] != "!"]
        disables = [x[1:] for x in self.options if x[0] == "!"]

        group.add_argument(*enables, dest=self.name, help=self.description + formatDefault(self.value), action='store_true', default=None)
        if disables:
            group.add_argument(*disables, dest=self.name, help=self.description + formatDefault(self.value), action='store_false', default=None)

class MultiStringOption(ConfigOption[List[str]]):
    def registerArgparse(self, group: ArgumentGroup):
        group.add_argument(*self.options, dest=self.name, type=str, nargs="*", help=self.description, action="append")

    def setFromString(self, string: str):
        self.value.extend(shlex.split(string))

    def updateFromDict(self, data: Dict[str, Any]):
        value = data.get(self.name)
        if value is not None:
            for entry in value:
                self.value.extend(entry)

class StringOption(ConfigOption[str]):
    pass

class FloatOption(ConfigOption[float]):
    pass

class IntegerOption(ConfigOption[int]):
    pass

class DictOption(ABC, ConfigOption[Dict[str, T]]):
    """
    A DictOption is an option whose value is a dict. This receives special
    treatment when reading config files --- in a config file, any line whose
    key is unrecognized (i.e. not the key of an existing option) is added to
    the first `DictOption` in the section. Usually, such sections only contain
    a single option which is a `DictOption`.
    """
    @classmethod
    @abstractmethod
    def entryFromString(cls, entry: str) -> T:
        """Converts a string into T"""

    @abstractmethod
    def registerArgparse(self, group: ArgumentGroup):
        pass

    def set(self, key: str, value: str):
        self.value[key] = self.entryFromString(value)

    def setFromString(self, string: str):
        for entry in string.split(","):
            key, val = entry.split("=", maxsplit=1)
            self.set(key.strip(), val.strip())

    def updateFromDict(self, data: Dict[str, Any]):
        entries = data.get(self.name) # type: Optional[List[List[str]]]
        if entries is not None:
            for key, val in entries:
                self.set(key, val)

class ConfigSection():
    """
    A configuration section.

    For the most part, a `ConfigSection` is a dict of `ConfigOption`s. However,
    when we access `section["key"]`, it doesn't return the `ConfigOption`
    itself, but the value of the option.

    The rationale for this decision is that we want to think of a
    `ConfigOption` as the value of the option together with some metadata. When
    trying to read or write the config option, what we want to do is the read
    or write to the value and ignoring the metadata.

    The only exception is when we want to add a new config option to the
    section, where we would write

      section["new_key"] = ConfigOption(...)

    """
    def __init__(self, name: str, parent: 'ConfigManager'):
        self.name = name
        self.parent = parent
        self.data = {} # type: Dict[str, ConfigOption]

    def __getitem__(self, key: str) -> Any:
        value = self.data[key].value
        wrapper = InterpolationWrapper(self.parent)
        if isinstance(value, str):
            return value % wrapper
        elif isinstance(value, Sequence) and value and isinstance(value[0], str):
            return [x % wrapper for x in value]
        else:
            return value

    def __setitem__(self, key: str, value: Any):
        if isinstance(value, ConfigOption):
            if key in self.data:
                raise ValueError
            self.data[key] = value
        else:
            self.data[key].value = value

    def get(self, key: str, default: Optional[Any]=None) -> Optional[Any]:
        try:
            return self[key]
        except KeyError:
            return default

    def keys(self) -> KeysView[str]:
        return self.data.keys()

    def registerArgparse(self, parser: ArgumentParser):
        """
        See the documentation for `ConfigManager` for the purpose of this
        function.

        Implemenation-wise, this adds an argument group to the parser and calls
        the `registerArgparse` function on each of the configuration items.
        """
        group = parser.add_argument_group(self.name)

        for option in self.data.values():
            option.registerArgparse(group)

    def updateFromDict(self, data: Dict[str, Any]):
        """
        See the documentation for `ConfigManager` for the purpose of this
        function. This simply calls `updateFromDict` on each of the
        configuration items.
        """

        for option in self.data.values():
            option.updateFromDict(data)

class ConfigManager(Dict[str, ConfigSection]):
    """
    A `ConfigManager` manages the configuration options for plastex. From the
    end user's point of view, this behaves like a 2-layered nested dict, so
    that configuration options can be retrieved as
    
      config["general"]["theme"]

    for example. However, `ConfigManager` is much more powerful than a nested
    dict. It supports reading in configuration options from `.ini` files and
    command line arguments.

    The former is performed via the `read` function, and the latter is via the
    `registerArgparse` and `updateFromDict` functions. The first function adds
    the options to an `ArgumentParser` from `argparse`, and the latter reads in
    the values obtained from `argparse`. A typical usage is as follows:

      config = ConfigManager()

      # Set up the config manager here

      from argparse import ArgumentParser
      parser = ArgumentParser("plasTeX")
      
      # This function adds a command line option to `parser` for each
      # configuration item in `config`
      config.registerArgparse(parser)

      # We now let the parser parse the arguments in `sys.argv`
      data = vars(parser.parse_args())

      # Finally, we let `config` read the values back in
      config.updateFromDict(data)

    The reason for this setup is that this allows us to add and process
    additional arguments that do not correspond to configuration options.
    """

    def registerArgparse(self, parser: ArgumentParser):
        """
        adds command line options to `parser` for each configuration item. This
        function merely delegates the job to the identically-named function of
        each of the sections.
        """
        for item in self.values():
            item.registerArgparse(parser)

    def updateFromDict(self, data: Dict[str, Any]):
        """
        reads in configuration options from the dict returned by
        `vars(ArgumentParser.parse_args)`. This function merely delegates the
        job to the identically-named function of each of the sections.
        """

        for section in self.values():
            section.updateFromDict(data)

    def addSection(self, name: str, description: Optional[str]=None) -> ConfigSection:
        """
        Creates a section with the given name and description and adds it to
        the ConfigManager.

        Requried arguments:
        name -- the key for accessing the section, which is also the section
        header used in the INI file.

        Optional arguments:
        description -- the header of the section for the cli `--help` function.
        Defaults to `name.capitalize() + " Options"`

        Returns:
        the new `ConfigSection` object produced
        """
        if name in self:
            raise ValueError("Section {} already exists".format(name))

        if description is None:
            description = name.capitalize() + " Options"

        self[name] = ConfigSection(description, self)
        return self[name]

    def read(self, filenames: Union[List[str], str]):
        """
        Loads config from the INI files in `filenames`. The function ignores
        files that do not exist. The argument may also be a single filename.
        """
        if isinstance(filenames, str):
            filenames = [filenames]

        for filename in filenames:
            data = ConfigParser(interpolation=None)
            data.read(filename)

            for section in data.sections():
                if section not in self:
                    print("Unrecognized section: {}".format(section))
                    continue

                dictObject = next((x for x in self[section].data.values() if isinstance(x, DictOption)), None)

                for key, val in data.items(section):
                    if key in self[section].data:
                        self[section].data[key].setFromString(val)
                    else:
                        if dictObject is not None:
                            dictObject.set(key, val)
                        else:
                            print("Unrecognized config: {}.{}".format(section, key))

class InterpolationWrapper(Dict[str, Any]):
    """
    A wrapper to flatten ConfigMangaer into a single-layered dict for
    interpolation.

    This class subclasses dict. The behaviour is such that the following
    holds::

      config = ConfigManager()
      # Set up config here
      wrapper = InterpolationWrapper(config)
      assert config["foo"]["bar"] == wrapper["bar"]

    If two sections contain the same key, the result from the first section is
    returned.
    """
    def __init__(self, config: ConfigManager):
        self.inner = config

    def __getitem__(self, key) -> Any:
        for section in self.inner.values():
            try:
                return section[key]
            except KeyError:
                continue
        raise KeyError(key)
