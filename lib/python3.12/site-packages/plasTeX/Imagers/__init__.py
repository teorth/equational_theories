from pathlib import Path
import os, tempfile, shutil, re, string, pickle
from hashlib import md5
from io import StringIO
import subprocess
import shlex
from typing import List, Tuple, Optional, Dict, Any

from plasTeX import Macro
from plasTeX.Filenames import Filenames
from plasTeX.Logging import getLogger

log = getLogger()
depthlog = getLogger('render.images.depth')
status = getLogger('status')
imagelog = getLogger('imager')

try:
    from PIL import Image as PILImage
    from PIL import ImageChops as PILImageChops
except ImportError:
    PILImage = PILImageChops = None  # type: ignore

def autoCrop(im, bgcolor=None, margin=0):
    """
    Automatically crop image down to non-background portion

    Required Argument:
    im -- image object

    Optional Argument:
    bgcolor -- value or tuple containing the color to use for the
        background color when cropping
    margin -- leave this many pixels around the content.  If there
        aren't that many pixels to leave, leave as many as possible.

    Returns: cropped image object and tuple containing the number
        of pixels removed from each side (left, top, right, bottom)

    """
    if im.mode != "RGB":
        im = im.convert("RGB")

    origbbox = im.getbbox()
    if origbbox is None:
        origbbox = (0,0,im.size[0],im.size[1])

    # Figure out the background color from the corners, if needed
    if bgcolor is None:
        topleft = im.getpixel((origbbox[0],origbbox[1]))
        topright = im.getpixel((origbbox[2]-1,origbbox[1]))
        bottomleft = im.getpixel((origbbox[0],origbbox[3]-1))
        bottomright = im.getpixel((origbbox[2]-1,origbbox[3]-1))
        corners = [topleft, topright, bottomleft, bottomright]

        matches = []
        matches.append(len([x for x in corners if x == topleft]))
        matches.append(len([x for x in corners if x == topright]))
        matches.append(len([x for x in corners if x == bottomleft]))
        matches.append(len([x for x in corners if x == bottomright]))

        try: bgcolor = corners[matches.index(1)]
        except ValueError: pass
        try: bgcolor = corners[matches.index(2)]
        except ValueError: pass
        try: bgcolor = corners[matches.index(3)]
        except ValueError: pass
        try: bgcolor = corners[matches.index(4)]
        except ValueError: pass

    # Create image with only the background color
    bg = PILImage.new("RGB", im.size, bgcolor)

    # Get bounding box of non-background content
    diff = PILImageChops.difference(im, bg)
    bbox = diff.getbbox()
    if bbox:
        if margin:
            bbox = list(bbox)
            bbox[0] -= margin
            bbox[1] -= margin
            bbox[2] += margin
            bbox[3] += margin
            bbox = tuple([max(0,x) for x in bbox])
        return im.crop(bbox), tuple([abs(x-y) for x,y in zip(origbbox,bbox)]), bgcolor
    return PILImage.new("RGB", (1,1), bgcolor), (0,0,0,0), bgcolor

class Box(object):
    pass

class Dimension(float):
    """
    Dimension object used for width, height, and depth of images

    This object is simply a float value.  The value of the float
    is in pixels.  All other units can be gotten using their
    corresponding property.

    """
    fontSize = 15
    @property
    def ex(self):
        return '%sex' % self.format(self / (self.fontSize * 0.6))
    @property
    def em(self):
        return '%sem' % self.format(self / self.fontSize)
    @property
    def pt(self):
        return '%spt' % self.format(self)
    @property
    def px(self):
        return '%spx' % self.format(self)
    @property
    def mm(self):
        return '%smm' % self.format(self.cm * 10.0)
    @property
    def inch(self):
        return '%sin' % self.format(self.pt / 72.0)
    @property
    def cm(self):
        return '%scm' % self.format(self.inch * 2.54)
    @property
    def pc(self):
        return '%spc' % self.format(self.pt / 12.0)

    def __getattribute__(self, name):
        if name in ['in']:
            return self.inch
        return float.__getattribute__(self, name)

    def format(self, value):
        if abs(int(value) - value) < 0.0001:
            return '%s' % int(value)
        return '%0.3f' % value

    def __str__(self):
        return self.format(self)

    def __repr__(self):
        return self.format(self)


class DimensionPlaceholder(str):
    """
    Placeholder for dimensions

    Dimensions for an image aren't generally known until the end of
    the rendering process.  This object generates a placeholder
    for the dimension.

    """
    imageUnits = ''
    def __getattribute__(self, name):
        if name in ['in','ex','em','pt','px','mm','cm','pc']:
            if not self:
                return self
            vars = {'units':name}
            return self + string.Template(self.imageUnits).substitute(vars)
        return str.__getattribute__(self, name)
    def __setattribute__(self, name, value):
        if name in ['in','ex','em','pt','px','mm','cm','pc']:
            return
        return str.__setattribute__(self, name, value)

class Image(object):
    """ Generic image object """

    def __init__(self, filename, config: Dict[str, Any], width=None, height=None, alt=None,
                       depth=None, longdesc=None):
        self.filename = filename
        self.path = os.path.join(os.getcwd(), self.filename)
        self.width = width
        self.height = height
        self.alt = alt
        self.depth = depth
        self.depthRatio = 0
        self.longdesc = longdesc
        self.config = config
        self._cropped = False
        self.bitmap = self
        self.checksum = None

    @property
    def height(self):
        return getattr(self.bitmap, '_height', None)

    @height.setter
    def height(self, value):
        if value is None:
            self._height = value
        elif isinstance(value, DimensionPlaceholder):
            self._height = value
        else:
            self._height = Dimension(value)

    @property
    def width(self):
        return getattr(self.bitmap, '_width', None)

    @width.setter
    def width(self, value):
        if value is None:
            self._width = value
        elif isinstance(value, DimensionPlaceholder):
            self._width = value
        else:
            self._width = Dimension(value)

    @property
    def depth(self):
        return getattr(self, '_depth', None)

    @depth.setter
    def depth(self, value):
        if value is None:
            self._depth = value
        elif isinstance(value, DimensionPlaceholder):
            self._depth = value
        else:
            self._depth = Dimension(value)

    @property
    def url(self):
        base = self.config['base-url']
        if base and base.endswith('/'):
            base = base[:-1]
        if base:
            return '%s/%s' % (base, self.filename)
        return self.filename

    def crop(self):
        """ Do the actual cropping """
        if self._cropped:
            return

        # Crop an SVG image
        if os.path.splitext(self.path)[-1] in ['.svg']:
            with open(self.path,'r') as fh:
                svg = fh.read()

            self.width = 0
            width = re.search(r'width=(?:\'|")([^\d\.]+)\w*(?:\'|")', svg)
            if width:
                self.width = float(width)

            self.height = 0
            height = re.search(r'height=(?:\'|")([^\d\.]+)\w*(?:\'|")', svg)
            if height:
                self.height = float(height)

            self.depth = 0
            if self.bitmap and self.height:
                depth = (self.height / self.bitmap.height) * self.bitmap.depth
                if abs(depth - int(depth)) > 0.1:
                    self.depth = depth - 1
                else:
                    self.depth = depth

            self._cropped = True
            return

        padbaseline = self.config['baseline-padding']

        try:
            im, self.depth = self._stripBaseline(PILImage.open(self.path),
                                             padbaseline)
            self.width, self.height = im.size
        except IOError as msg:
#           import traceback
#           traceback.print_exc()
            self._cropped = True
            log.warning(msg)
            return

        if padbaseline and self.depth > padbaseline:
            log.warning('depth of image %s (%d) is greater than the baseline padding (%s).  This may cause the image to be misaligned with surrounding text.', self.filename, self.depth, padbaseline)

        if self.config['transparent']:
            im = im.convert("P")
            lut = im.resize((256,1))
            lut.putdata(list(range(256)))
            index = list(lut.convert("RGB").getdata()).index((255,255,255))
            im.save(self.path, transparency=index)
        else:
            im.save(self.path)

        self._cropped = True

    def __str__(self):
        return self.filename

    def __repr__(self):
        return self.filename

    def _autoCrop(self, im, bgcolor=None, margin=0):
        return autoCrop(im, bgcolor, margin)

    def _stripBaseline(self, im, padbaseline=0):
        """
        Find the baseline register mark and crop it out

        The image has to have a particular layout.  The top left corner
        must be the background color of the image.  There should be a
        square registration mark which has the bottom edge at the baseline
        of the image (see \\plasTeXregister in LaTeX code at the top
        of this file).  This registration mark should be the leftmost
        content of the image.  If the registration mark is at the top
        of the image, the baseline is ignored.

        Required Arguments:
        im -- image to be cropped

        Keyword Arguments:
        padbaseline -- amount to pad the bottom of all cropped images.
            This allows you to use one margin-bottom for all images;
            however, you need to make sure that this padding is large
            enough to handle the largest descender in the document.

        Returns:
        (cropped image, distance from baseline to bottom of image)

        """
        if im.mode != "RGB":
            im = im.convert("RGB")

        depth = 0

        # Crop the image so that the regitration mark is on the left edge
        im, box, background = self._autoCrop(im)

        width, height = im.size

        # Determine if registration mark is at top or left
        top = False
        # Found mark at top
        if im.getpixel((0,0)) != background:
            top = True
            i = 1
            # Parse past the registration mark
            # We're fudging the vertical position by 1px to catch
            # things sitting right under the baseline.
            while i < width and im.getpixel((i,1)) != background:
                i += 1
            # Look for additional content after mark
            if i < width:
                while i < width and im.getpixel((i,1)) == background:
                    i += 1
                # If there is non-background content after mark,
                # consider the mark to be on the left
                if i < width:
                    top = False

        # Registration mark at the top
        blank = False
        if top:
            pos = height - 1
            while pos and im.getpixel((0,pos)) == background:
                pos -= 1
            depth = pos - height + 1

            # Get the height of the registration mark so it can be cropped out
            rheight = 0
            while rheight < height and im.getpixel((0,rheight)) != background:
                rheight += 1

            # If the depth is the entire height, just make depth = 0
            if -depth == (height-rheight):
                depth = 0

            # Handle empty images
            bbox = im.getbbox()
            if bbox is None or rheight == (height-1):
                blank = True
            else:
                bbox = list(bbox)
                bbox[1] = rheight

        # Registration mark on left side
        if blank or not(top) or im.getbbox()[1] == 0:
            pos = height - 1
            while pos and im.getpixel((0,pos)) == background:
                pos -= 1
            depth = pos - height + 1

            # Get the width of the registration mark so it can be cropped out
            rwidth = 0
            while rwidth < width and im.getpixel((rwidth,pos)) != background:
                rwidth += 1

            # Handle empty images
            bbox = im.getbbox()
            if bbox is None or rwidth == (width-1):
                return PILImage.new("RGB", (1,1), background), 0

            bbox = list(bbox)
            bbox[0] = rwidth

        # Crop out register mark, and autoCrop result
        im, cropped, background = self._autoCrop(im.crop(bbox), background)

        # If the content was entirely above the baseline,
        # we need to keep that whitespace
        depth += cropped[3]
        depthlog.debug('Depth of image %s is %s', self.filename, depth)

        # Pad all images with the given amount.  This allows you to
        # set one margin-bottom for all images.
        if padbaseline:
            width, height = im.size
            newim = PILImage.new("RGB", (width,height+(padbaseline+depth)), background)
            newim.paste(im, im.getbbox())
            im = newim

        return im, depth

def run_command(cmd: str, env: Optional[Dict] = None):
    p = subprocess.Popen(shlex.split(cmd),
                 stdin=subprocess.DEVNULL,
                 stdout=subprocess.PIPE,
                 stderr=subprocess.STDOUT,
                 universal_newlines=True,
                 env=env or os.environ)
    try:
        if p.stdout is not None:
            for line in p.stdout:
                imagelog.info(line.strip())
    except Exception as e:
        imagelog.error('Failed to read output from {}\n{}'.format(cmd, str(e)))

    p.wait()
    if p.stdout is not None:
        p.stdout.close()
    if p.returncode:
        raise subprocess.CalledProcessError(p.returncode, cmd)

class Imager(object):
    """ Generic Imager """

    # The command to run on the LaTeX output file to generate images.
    # This should be overridden by the subclass.
    command = '' # dvipng -o img%d.png -D 120 -Q 4'

    # The compiler command used to compile the LaTeX document
    compiler = 'latex'

    # The filename for temporary LaTeX source
    tmpFile = Path('images.tex')

    # Verification command to determine if the imager is available
    verifications = []

    fileExtension = '.png'

    imageAttrs = ''
    imageUnits = ''

    def __init__(self, document, imageTypes=None):
        self.config = document.config
        self.ownerDocument = document

        if imageTypes is None:
            self.imageTypes = [self.fileExtension]
        else:
            self.imageTypes = imageTypes[:]

        # Dictionary that makes sure each image is only generated once.
        # The key is the LaTeX source and the value is the image instance.
        self._cache = {}
        usednames = {}
        self._filecache = os.path.abspath(os.path.join('.cache',
                                          self.__class__.__name__+'.images'))
        if self.config['images']['cache'] and os.path.isfile(self._filecache):
            try:
                with open(self._filecache, 'rb') as fh:
                    self._cache = pickle.load(fh)
                for key, value in list(self._cache.items()):
                    if not os.path.isfile(value.filename):
                        del self._cache[key]
                        continue
                    usednames[value.filename] = None
            except ImportError:
                os.remove(self._filecache)

        # List of images
        self.images = {}

        # Images that are simply copied from the source directory
        self.staticimages = {}

        # Filename generator
        self.newFilename = Filenames(self.config['images'].get('filenames'),
                           variables={'jobname':document.userdata.get('jobname','')},
                           extension=self.fileExtension, invalid=usednames)

        # Start the document with a preamble
        self.source = StringIO()
        self.source.write('\\nonstopmode\n')
        self.writePreamble(document)
        self.source.write('\\begin{document}\n')

        # Set up additional options
        self._configOptions = self.formatConfigOptions(self.config['images'])

    def formatConfigOptions(self, config):
        """
        Format configuration options as command line options

        Required Arguments:
        config -- the images section of the configuration object

        Returns: a list of two-element tuples contain option value pairs

        Example::
            output = []
            if config['resolution']:
                output.append(('-D', config['resolution']))
            return output

        """
        return []

    def writePreamble(self, document):
        """ Write any necessary code to the preamble of the document """
        self.source.write(document.preamble.source)
        self.source.write('\\makeatletter\\oddsidemargin -0.25in\\evensidemargin -0.25in\n')

#       self.source.write('\\tracingoutput=1\n')
#       self.source.write('\\tracingonline=1\n')
#       self.source.write('\\showboxbreadth=\maxdimen\n')
#       self.source.write('\\showboxdepth=\maxdimen\n')
#       self.source.write('\\newenvironment{plasTeXimage}[1]{\\def\\@current@file{#1}\\thispagestyle{empty}\\def\\@eqnnum{}\\setbox0=\\vbox\\bgroup}{\\egroup\\typeout{imagebox:\\@current@file(\\the\\ht0+\\the\\dp0)}\\box0\\newpage}')

        self.source.write(r'''
\newwrite\imager@log
\immediate\openout\imager@log=images.csv
\@ifundefined{plasTeXimage}{%
\newenvironment{plasTeXimage}[2]{%
\vfil\break\plasTeXregister%
\thispagestyle{empty}\def\@eqnnum{}\def\tagform@{\@gobble}%
\write\imager@log{\arabic{page},#1,#2}%
\ignorespaces}{}}{}
''')
        self.source.write(r'''
\@ifundefined{plasTeXregister}{%
\def\plasTeXregister{\parindent=-0.5in\ifhmode\hrule%
\else\vrule\fi height 2pt depth 0pt %
width 2pt\hskip2pt}}{}
''')

    def verify(self):
        """ Verify that this commmand works on this machine """
        if self.verifications:
            for command in self.verifications:
                proc = os.popen(command)
                proc.read()
                if proc.close():
                    return False

            return True

        if not self.command.strip():
            return False

        cmd = self.command.split()[0]

        if not cmd:
            return False

        proc = os.popen('%s --help' % cmd)
        proc.read()
        if not proc.close():
            return True

        return False

    @property
    def enabled(self):
        if self.config['images']['enabled'] and \
           (self.command or (type(self) is not Imager and type(self) is not VectorImager)):
            return True
        return False

    def close(self):
        """ Invoke the rendering code """
        # Bail out if there are no images
        if not self.images:
            return

        if not self.enabled:
            return

        # Finish the document
        save_file = self.config["images"]["save-file"]

        self.source.write('\n\\end{document}\\endinput')

        for value in list(self._cache.values()):
            if value.checksum and os.path.isfile(value.path):
                with open(value.path,'r') as fh:
                    d = md5().digest(fh.read())
                if value.checksum != d:
                    log.warning('The image data for "%s" on the disk has changed.  You may want to clear the image cache.' % value.filename)

        cwd = Path.cwd()

        folders = []
        root = Path(self.ownerDocument.userdata.get('working-dir', '.')).absolute()
        for folder in os.environ.get('TEXINPUTS', '').split(os.pathsep):
            if folder.strip():
                folders.append(str((root/folder)))
        new_texinputs = os.pathsep.join(['.'] + folders + [str(root)]) + os.pathsep

        # Make a temporary directory to work in. We don't use
        # `with TemporaryDirectory() as tempdir` because we want to retain the
        # possibility of keeping the temporary directory.
        tempdir = Path(tempfile.mkdtemp())
        os.chdir(str(tempdir))

        # Compile LaTeX source, then convert the output
        self.source.seek(0)
        (_, fname) = tempfile.mkstemp('.tex', 'images-', '.', True)
        self.tmpFile = Path(fname)
        self.tmpFile.write_text(self.source.read(), encoding=self.config['files']['input-encoding'])

        def on_error(e):
            log.warning("Source files are saved at {}.".format(tempdir))
            os.chdir(str(cwd))
            raise e

        try:
            self.compileLatex(texinputs=new_texinputs)
        except Exception as e:
            log.warning("Failed to compile image: {}".format(e))
            on_error(e)

        # Execute converter
        try:
            images = self.executeConverter()
        except Exception as e:
            log.warning("Failed to convert image: {}".format(e))
            on_error(e)

        os.chdir(str(cwd))

        if len(images) != len(self.images):
            save_file = True
            log.warning('The number of images generated (%d) and the number of images requested (%d) is not the same.' % (len(images), len(self.images)))

        if PILImage is None and type(self) is not VectorImager:
            log.warning('PIL (Python Imaging Library) is not installed.  ' +
                        'Images will not be cropped.')


        # Move images to their final location
        for src, dest in images:
            try:
                dest_img = self.images[dest]
            except KeyError:
                save_file = True
                log.warning("Generated extra image: {} => {}".format(src, dest))
                continue

            if not (cwd / dest).parent.is_dir():
                (cwd / dest).parent.mkdir(parents=True)

            # Move the image
            try:
                shutil.copy2(str(tempdir / src), str(cwd / dest))
            except OSError:
                shutil.copy(str(tempdir / src), str(cwd / dest))

            # Crop the image
            try:
                dest_img.crop()
                status.dot()
            except Exception as msg:
                import traceback
                traceback.print_exc()
                log.warning('failed to crop %s (%s)', dest, msg)

        for value in list(self._cache.values()):
            if value.checksum is None and os.path.isfile(value.path):
                with open(value.path,'rb') as fh:
                    value.checksum = md5(fh.read()).digest()

        if not os.path.isdir(os.path.dirname(self._filecache)):
            os.makedirs(os.path.dirname(self._filecache))

        with open(self._filecache,'wb') as fh:
            pickle.dump(self._cache, fh)

        if save_file:
            log.warning("Imager temp files saved at {}".format(tempdir))
        else:
            shutil.rmtree(str(tempdir), True)

    def getCompiler(self):
        return self.config['images']['compiler'] or self.compiler

    def compileLatex(self, texinputs=''):
        """
        Compile the LaTeX source, located at self.tmpFile

        This should raise an exception if the compilation fails.
        """
        env = os.environ.copy()
        env['TEXINPUTS'] = texinputs
        run_command(r'%s %s' % (self.getCompiler(), self.tmpFile.name), env=env)

    def executeConverter(self, outfile: Optional[str] = None) -> List[Tuple[str, str]]:
        """
        Execute the actual image converter

        The converter should read `images.csv`. Each row of `images.csv` is a
        triple `n,dest,scale`, where `n` is the page that contains the image, `dest`
        is the destination filename and `scale` is the requested scaling factor.
        The converter then converts the output on page `n` to an image file.

        Arguments:
        outfile -- output file from latex to convert from. If left None, it
        uses the default value. This is usually None.

        Returns:
        A list of pairs (src, dest), where src is the name of the image file
        produced, and dest is the destination filename.

        This should raise an exception if the conversion fails.
        """
        if outfile is None:
            for ext in ['.dvi', ".pdf", ".ps"]:
                if self.tmpFile.with_suffix(ext).is_file():
                    outfile = self.tmpFile.with_suffix(ext).name
                    break

        if outfile is None:
            imagelog.warning("Missing image output file")
            raise Exception

        options = ''
        if self._configOptions:
            for opt, value in self._configOptions:
                opt, value = str(opt), str(value)
                if ' ' in value:
                    value = '"%s"' % value
                options += '%s %s ' % (opt, value)

        run_command(r'%s %s%s' % (self.command, options, outfile))

        images = []
        with open("images.csv") as fh:
            for line in fh.readlines():
                page, output, _ = line.split(",")
                images.append(("img{}{}".format(page, self.fileExtension), output.rstrip()))

        return images

    def writeImage(self, filename: str, code: str, context: str='', scale: float=1.0) -> None:
        """
        Write LaTeX source for the image

        Arguments:
        filename -- the name of the file that will be generated
        code -- the LaTeX code of the image
        context -- the LaTeX code of the context of the image

        """
        self.source.write('%s\n\\begin{plasTeXimage}{%s}{%s}\n%s\n\\end{plasTeXimage}\n' % (context, filename, scale, code))

    def get_scale(self, nodeName: str) -> float:
        return self.config["images"]["scales"].get(nodeName,
            self.config["images"]["scale-factor"])

    def newImage(self, node: Macro, context: str='', filename: Optional[str]=None) -> Image:
        """
        Invoke a new image

        Required Arguments:
        node -- the node to be rendered in an image

        Keyword Arguments:
        context -- LaTeX source to be executed before the image
            is created.  This generally consists of setting counters,
            lengths, etc. that will be used by the code that
            generates the image.
        filename -- filename to force the image to.  This filename
            should not include the file extension.

        """
        text = node.source
        # Convert ligatures back to original string
        for dest, src in self.ownerDocument.charsubs:
            text = text.replace(src, dest)

        # See if this image has been cached
        if text in self._cache:
            return self._cache[text]

        # Generate a filename if none has been provided
        filename = filename or self.newFilename()

        scale = self.get_scale(node.nodeName) # type: ignore

        # Add the image to the current document and cache
        #log.debug('Creating %s from %s', filename, text)
        self.writeImage(filename, text, context, scale)

        img = Image(filename, dict(self.config['images']))

        # Populate image attrs that will be bound later
        if self.imageAttrs:
            tmpl = string.Template(self.imageAttrs)
            vars = {'filename':filename}
            for name in ['height','width','depth']:
                if getattr(img, name) is None:
                    vars['attr'] = name
                    value = DimensionPlaceholder(tmpl.substitute(vars))
                    value.imageUnits = self.imageUnits
                    setattr(img, name, value)

        self.images[filename] = self._cache[text] = img
        return img

    def getImage(self, node):
        """
        Get an image from the given node whatever way possible

        This method attempts to find an existing image using the
        `imageoverride' attribute.  If it finds it, the image is
        converted to the appropriate output format and copied to the
        images directory.  If no image is available, or there was
        a problem in getting the image, an image is generated.

        Arguments:
        node -- the node to create the image from

        Returns:
        Image instance

        """
        name = getattr(node, 'imageoverride', None)
        if name is None:
            return self.newImage(node)

        if name in self.staticimages:
            return self.staticimages[name]

        # Copy or convert the image as needed
        path = self.newFilename()
        newext = os.path.splitext(path)[-1].lower()
        oldext = os.path.splitext(name)[-1].lower()
        try:
            directory = os.path.dirname(path)
            if directory and not os.path.isdir(directory):
                os.makedirs(directory)

            # If PIL isn't available or no conversion is necessary,
            # just copy the image to the new location
            if newext == oldext or oldext in self.imageTypes:
                path = os.path.splitext(path)[0] + os.path.splitext(name)[-1]
                if PILImage is None:
                    shutil.copyfile(name, path)
                    tmpl = string.Template(self.imageAttrs)
                    width = DimensionPlaceholder(tmpl.substitute({'filename':path, 'attr':'width'}))
                    height = DimensionPlaceholder(tmpl.substitute({'filename':path, 'attr':'height'}))
                    height.imageUnits = width.imageUnits = self.imageUnits
                else:
                    if os.path.splitext(name)[1].lower() == '.svg':
                        shutil.copyfile(name, path)
                        width = height = None
                    else:
                        img = PILImage.open(name)
                        width, height = img.size
                        scale = self.get_scale(node.nodeName)
                        if scale != 1:
                            width = int(width * scale)
                            height = int(height * scale)
                            img.resize((width,height))
                            img.save(path)
                        else:
                            shutil.copyfile(name, path)

            # If PIL is available, convert the image to the appropriate type
            else:
                img = PILImage.open(name)
                width, height = img.size
                scale = self.get_scale(node.nodeName)
                if scale != 1:
                    width = int(width * scale)
                    height = int(height * scale)
                    img.resize((width,height))
                img.save(path)
            img = Image(path, self.ownerDocument.config['images'], width=width, height=height)
            self.staticimages[name] = img
            return img

        # If anything fails, just let the imager handle it...
        except Exception as msg:
            #log.warning('%s in image "%s".  Reverting to LaTeX to generate the image.' % (msg, name))
            pass
        return self.newImage(node)


class VectorImager(Imager):
    fileExtension = '.svg'

    def writePreamble(self, document):
        Imager.writePreamble(self, document)
#       self.source.write('\\usepackage{type1ec}\n')
        self.source.write('\\def\\plasTeXregister{}\n')

    def getCompiler(self):
        return self.config['images']['vector-compiler'] or Imager.getCompiler(self)
