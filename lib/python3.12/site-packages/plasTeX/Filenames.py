import re, string, os.path

class Filenames(object):

    def __init__(self, spec, charsub=None, variables=None, extension='',
            invalid=None):
        """
        Generate filenames based on the `spec' and using the given variables

        Arguments:
        spec -- string containing filename specifier.  The filename specifier
            is a list of space separated names.  Each name in the list is
            returned once.  An example is shown below::

                index.html toc.html file1.html file2.html

            These filenames can also contain variables as described in
            Python's string Templates (e.g. $title, ${id}).  These variables
            come from the `variables' variable.  One special variable is
            $num.  This value in generated dynamically whenever a filename
            with $num is requested.  Each time a filename with $num is
            successfully generated, the value of $num is incremented.

            The values of variables can also be modified by a format specified
            in parentheses after the variable.  The format is simply an integer
            that specifies how wide of a field to create for integers
            (zero-padded), or, for strings, how many space separated words
            to limit the name to.  The example below shows $num being padded
            to four places and $title being limited to five words::

                sect$num(4).html $title(5).html

            The list can also contain a wildcard filename (which should be
            specified last).  Once a wildcard name is reached, it is
            used from that point on to generate the remaining filenames.
            The wildcard filename contains a list of alternatives to use as
            part of the filename indicated by a comma separated list of
            alternatives surrounded by a set of square brackets ([ ]).
            Each of the alternatives specified is tried until a filename is
            successfully created (i.e. all variables resolve).  For example,
            the specification below creates three alternatives::

                $jobname_[$id, $title, sect$num(4)].html

            The code above is expanded to the following possibilities::

                $jobname_$id.html
                $jobname_$title.html
                $jobname_sect$num(4).html

            Each of the alternatives is attempted until one of them succeeds.
            Generally, the last one should contain no variables except for
            $num as a fail-safe alternative.

        Keyword Arguments:
        charsub -- two-element list that contains character substitutions.
            The first element is a string containing all of the characters
            that are illegal in a filename.  The second string is a string
            that will be used in place of each of the "bad" characters in
            resulting filename.
        variables -- the namespace of variables to use when expanding the
            filenames.  New variables can be added to this namespace between
            each iteration.  The namespace is reset to the value sent in
            the initial generator call after each iteration.
        extension -- file extension to add to filenames that do not
            already have an extension
        invalid -- names that can not be used.  If the generated name is
            found to be one of the specified invalid names, a new one
            is generated until a valid name is found.

        Returns:
        generator that creates filenames

        """
        self.files = self.parseFilenames(spec)
        self.charsub = charsub or []
        self.variables = variables or {}
        self.extension = extension
        self.invalid = invalid or {}
        self.newFilename = self._newFilename()

    def parseFilenames(self, spec):
        """ Parse and expand the filename string """
        # Normalize string before parsing
        spec = spec.strip()
        spec = re.sub(r'\$(\w+)', r'${\1}', spec)
        spec = re.sub(r'\${\s*(\w+)\s*}', r'${\1}', spec)
        spec = re.sub(r'\}\(\s*(\d+)\s*\)', r'.\1}', spec)
        spec = re.sub(r'\[\s*', r'[', spec)
        spec = re.sub(r'\s*\]', r']', spec)
        spec = re.sub(r'\s*,\s*', r',', spec)

        files = ['']
        spec = iter(spec)
        for char in spec:

            # Spaces mark a division between names
            if not char.strip():
                 files.append('')
                 continue

            # Check for alternatives
            elif char == '[':
                options = [files[-1]]
                for char in spec:
                    if char == ',':
                        options.append(files[-1])
                        continue
                    elif char == ']':
                        break
                    options[-1] += char
                files[-1] = [x for x in options if x]
                continue

            # Append the character to the current filename
            if isinstance(files[-1], list):
                for i, item in enumerate(files[-1]):
                    files[-1][i] += char
            else:
                files[-1] += char

        files = [x for x in files if x]

        return files

    def __call__(self):
        return next(self)

    def __next__(self):
        for name in self.newFilename:
            return name

    def addExtension(self, filename):
        """ Add a file extension to the filename if none exists """
        ext = os.path.splitext(filename)[-1]
        if not ext:
            return filename + self.extension
        return filename

    def _newFilename(self):
        """ Generator that generates new filenames """
        g = self.variables.copy()

        # Split filenames into static and wildcard groups
        static = []
        wildcard = []
        while self.files:
            if isinstance(self.files[0], list):
                break
            static.append(self.files.pop(0))
        if self.files:
            wildcard = self.files.pop(0)

        # If there is no wildcard template, assume that the last
        # template given is a wildcard template.
        if not wildcard and static:
            wildcard = [static.pop()]

        # Initialize file number counter
        num = 1

        # Locate all key names and formats in the string
        keysre = re.compile(r'\$\{(\w+)(?:\.(\d+))?}')

        # Return static filenames
        for item in static:
            currentns = self.variables.copy()
            for key, value in list(currentns.items()):
                if self.charsub:
                    for char in self.charsub[0]:
                        value = value.replace(char, self.charsub[1])
                currentns[key] = value
            for key, format in keysre.findall(item):
                # Supply a file number as needed
                if key == 'num':
                    currentns['num'] = ('%%.%sd' % format) % num
                # Limit other variables to specified number of words
                elif format and key in currentns:
                    value = currentns[key].split()
                    newvalue = []
                    for i in range(int(format)):
                        newvalue.append(value.pop(0))
                        if not value:
                            break
                    currentns[key] = ' '.join(newvalue)
            try:
                # Strip formats
                item = re.sub(r'(\$\{\w+)\.\d+(\})', r'\1\2', item)
                # Do variable substitution
                result = string.Template(item).substitute(currentns)
                if 'num' in currentns:
                    num += 1
                self.variables.clear()
                self.variables.update(g)
                result = self.addExtension(result)
                if result not in self.invalid:
                    self.invalid[result] = None
                    yield result
            except KeyError:
                continue

        # We've reached the wildcard stage.  The wildcard gives us
        # multiple alternatives of filenames to choose from.  Keep trying
        # each one with the current namespace until one works.
        passes = 0
        while 1:
            passes += 1
            for item in wildcard:
                currentns = self.variables.copy()
                for key, value in list(currentns.items()):
                    if self.charsub:
                        for char in self.charsub[0]:
                            value = value.replace(char, self.charsub[1])
                    currentns[key] = value
                for key, format in keysre.findall(item):
                    # Supply a file number as needed
                    if key == 'num':
                        currentns['num'] = ('%%.%sd' % format) % num
                    # Limit other variables to specified number of words
                    elif format and key in currentns:
                        value = currentns[key].split()
                        newvalue = []
                        for i in range(int(format)):
                            newvalue.append(value.pop(0))
                            if not value:
                                break
                        currentns[key] = ' '.join(newvalue)
                try:
                    # Strip formats
                    item = re.sub(r'(\$\{\w+)\.\d+(\})', r'\1\2', item)
                    # Do variable substitution
                    result = string.Template(item).substitute(currentns)
                    if 'num' in currentns:
                        num += 1
                    self.variables.clear()
                    self.variables.update(g)
                    result = self.addExtension(result)
                    if result not in self.invalid:
                        self.invalid[result] = None
                        yield result
                    else:
                        continue
                    break
                except KeyError as key:
                    if 'num' in self.variables:
                        del self.variables['num']
                    continue
            else:
                # We tried 100 different names and still don't have a unique
                # one, we better just bail out.
                if passes > 100:
                    break

        raise ValueError('Filename could not be created.')
