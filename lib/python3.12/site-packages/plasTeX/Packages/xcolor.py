#!/usr/bin/env python

r"""
Partial support for `xcolor.sty` LaTeX Package.

Most features of xcolor are implemented, including color series and mixing.

Note that the following features are unimplemented:
    * Color blending (with \blendcolors)
    * Color masking (with \maskcolors)
    * Color testing (with \testcolors)
    * Localised color definitions (all colors are globally defined)
    * The tHsb color model and twheel function expressions

Current Issues:
    * Using \color to set the color of a block of content spanning multiple
      paragraphs does not work correctly.
    * Colors defined in cmy/cmyk will not match a PDF version exactly, due to
      the way the HTML representation is calculated. The HTML representation
      should either be outputted in cmyk directly in these cases (proposed for
      CSS4) or converted to rgb in a more sophisticated way, such as using
      color profiles.
"""

from plasTeX import Command, Environment, sourceChildren, Node
from enum import Enum, auto
from typing import Optional, Union, Dict, List
from typing_extensions import TypedDict
from re import Scanner # type: ignore
import math

class ColorModel(Enum):
    """An enumeration of supported color models.

    Color model support means that colors can be mixed within that model, and
    it is also possible to specify colors directly with their model parameters.

    Models with uppercase names, e.g. RGB, are 'derived' models and not really
    color models of their own right, but rather a user interface for convenience.
    They are immediately converted to a 'core' color model, e.g. rgb, on use.

    The natural color model keeps colors in whatever model they were originally
    specified in. They are not converted until mixing with a color in another
    model is requested, or a HTML representation is required.
    """
    natural = auto()
    rgb = auto()
    cmy = auto()
    cmyk = auto()
    hsb = auto()
    gray = auto()
    RGB = auto()
    HSB = auto()
    HTML = auto()
    Gray = auto()
    Hsb = auto()
    wave = auto()

class ColorError(Exception):
    """There was some problem with color definition or mixing."""
    pass

class ColorParser:
    """ A top-down parser for xcolor's color specification syntax.

    Description of terminology and a full list of elements supported
    by the parser is shown in the xcolor documentation (c.f. Table 4, pg 13,
    xcolor v2.12, 2016/05/11).

    The parser takes an xcolor expression in the form of a string. The string
    is first scanned (using the scan() method) from left to right and converted
    into a list of tokens. Class methods can then be used to build dict objects
    describing specific syntax elements. These objects are then used for further
    parsing or can be used as part of some other computation.

    Typically color specifications will be parsed as a whole using the
    parseColor() method, which returns a single Color object with any requested
    color mixing or other operations applied.
    """
    Spec = TypedDict('Spec',{
        'element': 'ColorParser.Elements',
        'id': str,
        'values': List[Union[int,float]]
    }, total=False)

    ColorMix = TypedDict('ColorMix',{
        'element': 'ColorParser.Elements',
        'pct': float,
        'id': str,
    }, total=False)

    Token = TypedDict('Token',{
            'element': 'ColorParser.Elements',
            'id': str,
            'ids': List[str],
            'idlist': List[List[str]],
            'value': Union[int,float],
            'values': List[Union[int,float]],
            'specs': List[Spec],
            'mix': ColorMix,
            'mixes': List[ColorMix],
            'model': ColorModel,
            'models': List[ColorModel],
            'color': 'Color',
    }, total=False)

    class Elements(Enum):
        """An enumeration of all syntax elements supported by the parser.

        Note that this includes primitive elements (e.g. comma) along
        with parsed elements such as real numbers, model lists and mix
        expressions.
        """
        empty = auto()
        minus = auto()
        plus = auto()
        space = auto()
        int = auto()
        dec = auto()
        id = auto()
        model = auto()
        symbol = auto()
        comma = auto()
        ext_id = auto()
        id_list = auto()
        dot = auto()
        named = auto()
        model_list = auto()
        spec = auto()
        spec_list = auto()
        series_step = auto()
        series_access = auto()
        mix = auto()
        mix_expr = auto()
        func_expr = auto()
        expr = auto()
        color = auto()

    class ParseError(Exception):
        """There was some problem parsing with the xcolor specification
        syntax."""
        pass

    def __init__(self, colors:Dict[str,'Color']={}, target_model:ColorModel=ColorModel.natural):
        self.colors:Dict[str,'Color'] = colors
        self.target:ColorModel = target_model
        self.tokens:List['ColorParser.Token'] = []
        self.current_color:Optional['Color'] = None

    def empty(self) -> Token:
        """An element to denote that the list of tokens is empty"""
        return {'element': ColorParser.Elements.empty}
    
    def int(self) -> Optional[Token]:
        """An integer number"""
        if self.next['element'] == ColorParser.Elements.int:
            return self.tokens.pop(0)
        else:
            return None
    
    def num(self) -> Optional[Token]:
        """A non-negative integer number"""
        if self.next['element'] == ColorParser.Elements.int and self.next['value'] >= 0:
            return self.tokens.pop(0)
        else:
            return None
    
    def dec(self) -> Optional[Token]:
        """A real Number"""
        if self.next['element'] == ColorParser.Elements.dec or self.next['element'] == ColorParser.Elements.int:
            return self.tokens.pop(0)
        else:
            return None

    def div(self) -> Optional[Token]:
        """A non-zero real number"""
        if (self.next['element'] == ColorParser.Elements.dec or self.next['element'] == ColorParser.Elements.int) \
                and int(self.next['value']) != 0:
            return self.tokens.pop(0)
        else:
            return None

    def pct(self) -> Optional[Token]:
        """A real number in the interval [0,100], a percentage"""
        if (self.next['element'] == ColorParser.Elements.dec or self.next['element'] == ColorParser.Elements.int) \
                and self.next['value'] >=0 and self.next['value'] <=100:
            return self.tokens.pop(0)
        else:
            return None

    def id(self) -> Optional[Token]:
        """An identifier, a non-empty string consisting of letters and digits"""
        if self.next['element'] == ColorParser.Elements.id:
            return self.tokens.pop(0)
        else:
            return None
    
    def function(self) -> Optional[Token]:
        """A color function, 'wheel' or 'twheel'"""
        if self.next['element'] == ColorParser.Elements.id:
            if self.next['id'] == 'wheel' or self.next['id'] == 'twheel':
                return self.tokens.pop(0)
        return None

    def dot(self) -> Optional[Token]:
        """A literal dot"""
        if self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '.':
            self.tokens.pop(0)
            return {'element': ColorParser.Elements.id, 'id': '.'}
        else:
            return None

    def named(self) -> Optional[Token]:
        """The literal string 'named'"""
        if self.next['element'] == ColorParser.Elements.named:
            return self.tokens.pop(0)
        else:
            return None
    
    def ext_id(self) -> Optional[Token]:
        """An identifier element or an identifier assignment ([id]=[id])"""
        if self.next['element'] == ColorParser.Elements.id:
            id1 = self.tokens.pop(0)
            if self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '=':
                self.tokens.pop(0)
                id2 = self.tokens.pop(0)
                return {'element': ColorParser.Elements.ext_id, 'ids': [id1['id'], id2['id']]}
            else:
                return {'element': ColorParser.Elements.ext_id, 'ids': [id1['id'], id1['id']]}
        else:
            return None

    def id_list(self) -> Optional[Token]:
        """A list of identifier (ext_id) elements"""
        ext_id_elem = self.ext_id()
        if ext_id_elem is None:
            return None
        ext_ids = [ext_id_elem['ids']]
        while self.next['element'] == ColorParser.Elements.comma:
            self.tokens.pop(0)
            ext_id_elem = self.ext_id()
            if ext_id_elem is None:
                return None
            ext_ids.append(ext_id_elem['ids'])
        return {'element': ColorParser.Elements.id_list, 'idlist': ext_ids}

    def name(self) -> Optional[Token]:
        """An implicit (the literal '.') or explicit (an identifier) color name"""
        return self.id() or self.dot()
    
    def core_model(self) -> Optional[Token]:
        """An element corresponding to one of the core color models"""
        core_models = [ColorModel.rgb, ColorModel.cmy,
                ColorModel.cmyk, ColorModel.hsb, ColorModel.gray]
        if self.next['element'] == ColorParser.Elements.model and self.next['model'] in core_models:
            return self.tokens.pop(0)
        else:
            return None
    
    def num_model(self) -> Optional[Token]:
        """An element corresponding one of the numerical color models"""
        if self.next['element'] == ColorParser.Elements.model:
            return self.tokens.pop(0)
        else:
            return None
        
    def model(self) -> Optional[Token]:
        """An element corresponding to a color model"""
        return self.num_model() or self.named()

    def model_list_basic(self) -> Optional[Token]:
        """An element corresponding to a list of color models"""
        model_elem = self.model()
        if model_elem is None:
            return None
        models = [model_elem['model']]
        while self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '/':
            self.tokens.pop(0)
            model_elem = self.model()
            if model_elem is None:
                return None
            models.append(model_elem['model'])
        return {'element': ColorParser.Elements.model_list, 'models': models}
    
    def model_list(self) -> Optional[Token]:
        """An element corresponding to a list of color models with a core model specified"""
        first = self.model()
        if first is None:
            return None
        if self.next['element'] == ColorParser.Elements.symbol and (self.next['id'] in [':','/']):
            sep = self.tokens.pop(0)
            if sep['element'] == ColorParser.Elements.symbol and sep['id'] == ':':
                models = self.model_list_basic()
                if models is not None:
                    models['model'] = first['model']
                return models
            elif sep['element'] == ColorParser.Elements.symbol and sep['id'] == '/':
                models = self.model_list_basic()
                if models is not None:
                    models['models'].insert(0, first['model'])
                return models
            else:
                raise ColorParser.ParseError("Missing separator in color model list")
        else:
            return {'element': ColorParser.Elements.model_list, 'models': [first['model']]}

    def spec(self) -> Spec:
        """An implicit or explicit color specification"""
        if self.next['element'] == ColorParser.Elements.id:
            id_elem = self.tokens.pop(0)
            return {'element': ColorParser.Elements.spec, 'id': id_elem['id']}
        else:
            valid_next = [ColorParser.Elements.int, ColorParser.Elements.dec, ColorParser.Elements.comma]
            num_elem = self.int() or self.dec()
            if num_elem is not None:
                spec = [num_elem['value']]
                while self.next['element'] in valid_next:
                    if self.next['element'] == ColorParser.Elements.comma:
                        self.tokens.pop(0)
                    num_elem = self.int() or self.dec()
                    if num_elem is not None:
                        spec.append(num_elem['value'])
                return {'element': ColorParser.Elements.spec, 'values': spec}
            else:
                raise ColorParser.ParseError("Missing expected integer or real.")

    def spec_list(self) -> Token:
        """An element corresponding to a list of implicit or explicit color specifications"""
        specs = [self.spec()]
        while self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '/':
            self.tokens.pop(0)
            specs.append(self.spec())
        return {'element': ColorParser.Elements.spec_list, 'specs': specs}

    def prefix(self) -> Optional[Token]:
        """A color expression prefix"""
        if self.next['element'] == ColorParser.Elements.minus:
            return self.tokens.pop(0)
        else:
            return None

    def postfix(self) -> Optional[Token]:
        """A color expression postfix"""
        if self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '!!':
            self.tokens.pop(0)
            if self.next['element'] == ColorParser.Elements.plus:
                plus = self.tokens.pop(0)
                return {'element': ColorParser.Elements.series_step, 'value': plus['value'] }
            else:
                obrace = self.tokens.pop(0) #[
                num = self.num()
                if num is None:
                    raise ColorParser.ParseError("Missing expected non-negative integer number")
                cbrace = self.tokens.pop(0) #]
                return {'element': ColorParser.Elements.series_access, 'value': num['value'] }
        return None

    def mix(self) -> Optional[ColorMix]:
        """An element corresponding to a color and percentage pair for mixing"""
        if self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '!':
            self.tokens.pop(0)
            pct = self.pct()
            if pct is None:
                raise ColorParser.ParseError("Missing expected real number percentage")
            if self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '!':
                self.tokens.pop(0)
                name = self.name()
                if name is None:
                    raise ColorParser.ParseError("Missing expected color name or '.'")
                return {'element': ColorParser.Elements.mix, 'pct': pct['value'], 'id': name['id'] }
            else:
                return {'element': ColorParser.Elements.mix, 'pct': pct['value'], 'id': 'white' }
        else:
            return None
    
    def mix_expr(self) -> Optional[Token]:
        """An element corresponding to a mix of colors"""
        mix_elem = self.mix()
        if mix_elem is None:
            return None
        mixes = [mix_elem]
        while self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '!':
            mix_elem = self.mix()
            if mix_elem is None:
                return None
            mixes.append(mix_elem)
        return {'element': ColorParser.Elements.mix_expr, 'mixes': mixes}

    def expr(self) -> Optional[Token]:
        """A standard color expression"""
        prefix = self.prefix()
        name = self.name()
        if name is None:
            raise ColorParser.ParseError("Missing expected color name or '.'")
        mix = self.mix_expr()
        postfix = self.postfix()
        color = Color().makeColor('named',name['id'], self.colors, self.current_color).copy()

        if postfix is not None:
            color_series = self.colors[name['id']]
            if not isinstance(color_series,ColorSeries):
                raise ColorParser.ParseError("Postfix operator can only be used on color series")
            if postfix['element'] == ColorParser.Elements.series_step:
                while postfix['value']>0:
                    color_series.series_step()
                    postfix['value'] -= 1
            elif postfix['element'] == ColorParser.Elements.series_access:
                color = color_series.series_n(int(postfix['value'])).copy()

        if mix is not None:
            for m in mix['mixes']:
                mpct = m['pct']
                mcol = Color().makeColor('named',m['id'],
                        self.colors, self.current_color).as_model(color.model)
                color = color.mix(mcol, mpct)
            
        if prefix is not None and prefix['value']%2 == 1:
            color = color.complement
        
        return {'element': ColorParser.Elements.expr, 'color': color}
    
    def ext_expr(self) -> Optional[Token]:
        """An extended color expression"""
        div = 0.
        model_elem = self.core_model()
        if model_elem is None:
            return None
        model = model_elem['model']

        if self.next['element'] == ColorParser.Elements.comma:
            self.tokens.pop(0)
            div_elem = self.div()
            if div_elem is None:
                raise ColorParser.ParseError("Missing expected non-zero real number")
            div = div_elem['value']
        
        if self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == ':':
            self.tokens.pop(0)
            expr_elem = self.expr()
            if expr_elem is None:
                raise ColorParser.ParseError("Missing expected color expression")
            exprs = [expr_elem]
            if self.next['element'] != ColorParser.Elements.comma:
                raise ColorParser.ParseError("Missing expected comma")
            self.tokens.pop(0)
            dec_elem = self.dec()
            if dec_elem is None:
                raise ColorParser.ParseError("Missing expected real number")
            decs = [dec_elem['value']]

            while self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == ';':
                self.tokens.pop(0)
                expr_elem = self.expr()
                if expr_elem is None:
                    raise ColorParser.ParseError("Missing expected color expression")
                exprs.append(expr_elem)
                if self.next['element'] != ColorParser.Elements.comma:
                    raise ColorParser.ParseError("Missing expected comma")
                self.tokens.pop(0)
                dec_elem = self.dec()
                if dec_elem is None:
                    raise ColorParser.ParseError("Missing expected real number")
                decs.append(dec_elem['value'])

            if div==0:
                div = sum(decs)

            color = 0.0*(grayColor(0.).as_model(model))
            for expr,dec in zip(exprs,decs):
                color = color + (dec/div)*(expr['color'].as_model(model))

            return {'element': ColorParser.Elements.expr, 'color': color.wrapped}
        else:
            return None
    
    def color(self) -> Optional[Token]:
        """A color expression including any color functions to be applied"""
        color_expr = self.ext_expr() or self.expr()
        if color_expr is None:
            return None
        color = color_expr['color']
        while self.next['element'] == ColorParser.Elements.symbol and self.next['id'] == '>':
            self.tokens.pop(0)
            func = self.function()
            if func is None:
                raise ColorParser.ParseError("Missing expected color function 'wheel', 'twheel'")
            args: List[float] = []
            while self.next['element'] == ColorParser.Elements.comma:
                self.tokens.pop(0)
                arg = self.int()
                if arg is None:
                    raise ColorError("Invalid argument passed to color function.")
                args.append(arg['value'])

            if func['id'] == 'wheel':
                if len(args) == 0:
                    raise ColorError("Insufficient arguments for color function: wheel.")
                full_circle = 360. if len(args)<2 else args[1]
                angle = args[0]
                fcolor = color.as_hsb
                fcolor.h = (fcolor.h + float(angle)/full_circle)
                color = fcolor.wrapped
            else:
                raise ColorError("Color function {} is not implemented".format(func['id']))
        return {'element': ColorParser.Elements.color, 'color':color}

    @property
    def next(self) -> Token:
        """Return the next element from the token stream.

        Returns an empty element if there are no more tokens.
        """
        if len(self.tokens) > 0:
            return self.tokens[0]
        return self.empty()
    
    def scan(self, expr:str) -> List[Token]:
        """Scan an expression and populate the token stream.

        Uses SRE's Scanner to convert an expression from a string into a list of
        syntax elements for the token stream. This method is the first
        step in parsing a given expression string.
        """
        scanner = Scanner([
            (r',\s*', lambda s, t: {'element': ColorParser.Elements.comma}),
            (r'RGB|rgb|cmyk|cmy|HSB|hsb|Gray|gray|HTML|Hsb|tHsb|wave',
                lambda s, t: {'element': ColorParser.Elements.model, 'model': ColorModel[t]}),
            (r'named', lambda s, t: {'element': ColorParser.Elements.named, 'model': ColorModel.natural}),
            (r'[0-9A-F]{6}', lambda s, t: {'element': ColorParser.Elements.int, 'value': int(t,16)}),
            (r'[-+]?(\d*\.\d+)|(\d+\.\d*)',
                lambda s, t: {'element': ColorParser.Elements.dec, 'value': float(t)}),
            (r'[-+]?\d+', lambda s, t: {'element': ColorParser.Elements.int, 'value': int(t)}),
            (r'-+', lambda s, t: {'element': ColorParser.Elements.minus, 'value': len(t)}),
            (r'\++', lambda s, t: {'element': ColorParser.Elements.plus, 'value': len(t)}),
            (r'\w+', lambda s, t: {'element': ColorParser.Elements.id, 'id': t}),
            (r'!!', lambda s, t: {'element': ColorParser.Elements.symbol, 'id': t}),
            (r'\s+', lambda s, t: None),
            (r'.', lambda s, t: {'element': ColorParser.Elements.symbol, 'id': t}),
            ])
        self.tokens, unknown = scanner.scan(expr)
        return self.tokens

    def parseColor(self, colorspec: str, model: Optional[str] = None) -> 'Color':
        """Parse xcolor color specification(s) (with optional color model(s)).

        This function returns a ready-to-use Color object representing the
        final mixed color.
        """
        if model is not None:
            self.scan(model)
            model_list = self.model_list()
            if model_list is None:
                raise ColorParser.ParseError("Error parsing color model list")
            models = model_list['models']

            self.scan(colorspec)
            spec_list = self.spec_list()
            if spec_list is None:
                raise ColorParser.ParseError("Error parsing color specification list")
            specs = spec_list['specs']

            if self.target in models:
                spec = specs[models.index(self.target)]
                color = Color().makeColor(self.target, spec['id'] if 'id' in spec else spec['values'],
                        self.colors, self.current_color)
            else:
                spec = specs[0]
                color = Color().makeColor(models[0], spec['id'] if 'id' in spec else spec['values'],
                        self.colors, self.current_color)
            
            core = model_list['model'] if 'model' in model_list else ColorModel.natural
            return color.as_model(core).as_model(self.target)
        else:
            self.scan(colorspec)
            color_elem = self.color()
            if color_elem is None:
                raise ColorParser.ParseError("Error parsing color element")
            return color_elem['color']

    def parseColorSeries(self, model:str, method:str, b_model:Optional[str], b_spec:str,
            s_model:Optional[str], s_spec:str) -> 'ColorSeries':
        """Parse an xcolor color series (with optional model(s)).

        This function returns a ready-to-use ColorSeries object representing the
        final color series.
        """
        self.scan(model)
        model_elem = self.core_model()
        if model_elem is None:
            raise ColorParser.ParseError("Missing expected core model.")
        base = self.parseColor(b_spec, b_model)
        if method == 'last':
            last = self.parseColor(s_spec, s_model)
            return ColorSeries(model_elem['model'], method, base, last = last)
        else:
            self.scan(s_spec)
            spec_elem = self.spec()
            if spec_elem is None:
                raise ColorParser.ParseError("Missing expected color specification.")
            return ColorSeries(model_elem['model'], method, base, step = spec_elem['values'])

class Color:
    """ A base color class representing a certain color shade in a certain color
    model.

    This is an abstract class implementing color mixing, arithmetic and general
    methods applicable to all color models.

    Each color model should be implemented as a subclass of Color, overriding
    color model specific abstract methods, e.g. as_rgb().
    """
    model = ColorModel.natural
    
    def __repr__(self) -> str:
        return '<{}Color: {}>'.format(self.model, self.as_list)

    def __add__(self, add_color: 'Color') -> 'Color':
        add_color = add_color.as_model(self.model)
        c = [ a+b for (a,b) in zip(self.as_list, add_color.as_list)]
        return self.makeColor(self.model, c)
    
    def __sub__(self, sub_color: 'Color') -> 'Color':
        sub_color = sub_color.as_model(self.model)
        c = [ a-b for (a,b) in zip(self.as_list, sub_color.as_list)]
        return self.makeColor(self.model, c)
    
    def __rmul__(self, dec:float) -> 'Color':
        c = [ dec*a for a in self.as_list ]
        return self.makeColor(self.model, c)

    def copy(self) -> 'Color':
        """Return a copy of this color as a new color object"""
        c = [ a for a in self.as_list]
        return self.makeColor(self.model, c)

    def mix(self, mix_color: 'Color', p: float) -> 'Color':
        """Mix the given color into this color, with percentage p.

        Linear interpolation within this color's model is used.
        """
        mix_color = mix_color.as_model(self.model)
        c = [ a*(p/100.)+b*(1.-p/100.) for (a,b) in zip(self.as_list, mix_color.as_list)]
        return self.makeColor(self.model, c)

    def makeColor(self, model: Union[str, ColorModel], spec: Union[str,List[Union[int,float]]],
            named:Dict[str,'Color']={}, current_color:Optional['Color']=None) -> 'Color':
        """Create a new Color object according to given arguments.

        Returns a color object corresponding to either a named color in the
        given color dictionary, a color shade specified by the given color model
        and list of parameters, or the "current color".

        If the current_color argument is not provided, black is used as the
        current color.

        This allows for a generic way to create color objects similar to how
        colors are defined in xcolor, for example:
            * The color named 'red' in color_dict:
                makeColor('named','red',color_dict)

            * The color {255,255,255} in the derived model RGB:
                makeColor(ColorModel.RGB,[255,255,255])

            * The "current color" (here given as "foo") in the rgb model:
                makeColor('rgb','.',current_color=foo)
        """
        if spec == '.':
            req_model:ColorModel = model if isinstance(model,ColorModel) else ColorModel.natural 
            return current_color or grayColor(0.).as_model(req_model)
        elif isinstance(spec, list):
            if model == ColorModel.rgb:
                r,g,b = spec
                return rgbColor(r,g,b)
            elif model == ColorModel.RGB:
                r,g,b = spec
                return rgbColor(r/255.,g/255.,b/255.)
            elif model == ColorModel.cmyk:
                c,m,y,k = spec
                return cmykColor(c,m,y,k)
            elif model == ColorModel.cmy:
                c,m,y = spec
                return cmyColor(c,m,y)
            elif model == ColorModel.gray:
                return grayColor(spec[0])
            elif model == ColorModel.Gray:
                return grayColor(spec[0]/15.)
            elif model == ColorModel.hsb:
                h,s,b = spec
                return hsbColor(h,s,b)
            elif model == ColorModel.Hsb:
                h,s,b = spec
                return hsbColor(h/360.,s,b)
            elif model == ColorModel.HSB:
                h,s,b = spec
                return hsbColor(h/240.,s/240.,b/240.)
            elif model == ColorModel.HTML:
                h = int(spec[0])
                r = ((h&0xFF0000)>>16)/255.
                g = ((h&0xFF00)>>8)/255.
                b = (h&0xFF)/255.
                return rgbColor(r,g,b)
            elif model == ColorModel.wave:
                return waveColor(spec[0])
            raise ColorError('Unable to create requested ColorModel "{}"'.format(model))
        else:
            if spec in named:
                return named[spec]
            else:
                raise ColorError('Named color "{}" not found in color database.'.format(spec))


    def as_model(self, model: ColorModel) -> 'Color':
        """Return this color in the specified color model.

        Color models are converted if necessary.
        """
        if model == ColorModel.natural:
            return self
        if model == ColorModel.rgb:
            return self.as_rgb
        elif model == ColorModel.cmyk:
            return self.as_cmyk
        elif model == ColorModel.cmy:
            return self.as_cmy
        elif model == ColorModel.gray:
            return self.as_gray
        elif model == ColorModel.hsb:
            return self.as_hsb
        elif model == ColorModel.wave:
            return self.as_wave
        else:
            raise ColorError('Unable to convert to requested ColorModel')
    
    @property
    def html(self) -> str:
        """Return this color as a string, compatible with HTML."""
        rgb = self.as_rgb
        return '#%.2X%.2X%.2X' % (min(int(rgb.r*255), 255),
                min(int(rgb.g*255), 255), min(int(rgb.b*255), 255))

    @property
    def wrapped(self) -> 'Color':
        """Return this color with wrapping applied.

        Returns this color as a new color object, in the same core color model
        but with a "wrapping" function applied to the color parameters. The
        function maps n arbitrary color parameters into the unit n-cube so as
        to yield a valid color with parameters from the interval [0,1].
        (c.f. Equation (6), pg 26, xcolor v2.12, 2016/05/11)
        """
        c = [ a - math.floor(a) if a != 1. else a for a in self.as_list]
        return self.makeColor(self.model, c)

    @property
    def as_list(self) -> List[float]:
        """This color as a list of parameters"""
        raise NotImplementedError()

    @property
    def as_rgb(self) -> 'rgbColor':
        """This color as a color in the rgb model"""
        raise NotImplementedError()

    @property
    def as_gray(self) -> 'grayColor':
        """This color as a color in the gray model"""
        raise NotImplementedError()

    @property
    def as_cmy(self) -> 'cmyColor':
        """This color as a color in the cmy model"""
        raise NotImplementedError()

    @property
    def as_hsb(self) -> 'hsbColor':
        """This color as a color in the hsb model"""
        raise NotImplementedError()

    @property
    def as_cmyk(self) -> 'cmykColor':
        """This color as a color in the cmyk model"""
        raise NotImplementedError()

    @property
    def as_wave(self) -> 'waveColor':
        """This color as a color in the wave model"""
        raise ColorError('Unable to convert to the wave color model')

    @property
    def complement(self) -> 'Color':
        """The complement of this color, computed in this color model.

        (c.f. Section 6.3, pg 47, xcolor v2.12, 2016/05/11)
        """
        raise NotImplementedError()

class rgbColor(Color):
    """A subclass of Color for colors in the rgb base color model"""
    model = ColorModel.rgb

    def __init__(self, r:float, g:float, b:float) -> None:
        self.r:float = r
        self.g:float = g
        self.b:float = b

    @property
    def as_list(self) -> List[float]:
        return [self.r, self.g, self.b]

    @property
    def as_rgb(self) -> 'rgbColor':
        return self
    
    @property
    def as_gray(self) -> 'grayColor':
        return grayColor(0.3*self.r + 0.59*self.g + 0.11*self.b)
    
    @property
    def as_cmy(self) -> 'cmyColor':
        return cmyColor(1. - self.r, 1. - self.g, 1. - self.b)

    @property
    def as_hsb(self) -> 'hsbColor':
        maxc = max((self.r, self.g, self.b))
        minc = min((self.r, self.g, self.b))
        if minc == maxc:
            return hsbColor(0., 0., maxc)
        rc = (maxc-self.r) / (maxc-minc)
        gc = (maxc-self.g) / (maxc-minc)
        bc = (maxc-self.b) / (maxc-minc)
        if self.r == maxc:
            h = bc-gc
        elif self.g == maxc:
            h = 2.+rc-bc
        else:
            h = 4.+gc-rc
        h = (h/6.) % 1.
        return hsbColor(h, (maxc-minc) / maxc, maxc)
    
    @property
    def as_cmyk(self) -> 'cmykColor':
        (c,m,y) = (1.-self.r, 1.-self.g, 1.-self.b)
        k = min((c, m, y))
        ck = min(1., max(0., c - k))
        mk = min(1., max(0., m - k))
        yk = min(1., max(0., y - k))
        return cmykColor(ck,mk,yk,k)

    @property
    def complement(self) -> 'rgbColor':
        return rgbColor(1. - self.r, 1. - self.g, 1. - self.b)
    
class grayColor(Color):
    """A subclass of Color for colors in the gray base color model"""
    model = ColorModel.gray

    def __init__(self, gray:float) -> None:
        self.gray:float = gray
    
    @property
    def as_list(self) -> List[float]:
        return [self.gray]
    
    @property
    def as_gray(self) -> 'grayColor':
        return self

    @property
    def as_rgb(self) -> 'rgbColor':
        return rgbColor(self.gray,self.gray,self.gray)
    
    @property
    def as_cmy(self) -> 'cmyColor':
        return cmyColor(1.-self.gray, 1.-self.gray, 1.-self.gray)
    
    @property
    def as_cmyk(self) -> 'cmykColor':
        return cmykColor(0., 0., 0., 1.-self.gray)
    
    @property
    def as_hsb(self) -> 'hsbColor':
        return hsbColor(0., 0., 1.-self.gray)

    @property
    def complement(self) -> 'grayColor':
        return grayColor(1. - self.gray)

class cmykColor(Color):
    """A subclass of Color for colors in the cmyk base color model"""
    model = ColorModel.cmyk

    def __init__(self, c:float, m:float, y:float, k:float) -> None:
        self.c:float = c
        self.m:float = m
        self.y:float = y
        self.k:float = k
    
    @property
    def as_list(self) -> List[float]:
        return [self.c, self.m, self.y, self.k]
    
    @property
    def as_cmyk(self) -> 'cmykColor':
        return self
    
    @property
    def as_hsb(self) -> 'hsbColor':
        return self.as_rgb.as_hsb

    @property
    def as_cmy(self) -> 'cmyColor':
        c = min(1., self.c + self.k)
        m = min(1., self.m + self.k)
        y = min(1., self.y + self.k)
        return cmyColor(c, m, y)

    @property
    def as_gray(self) -> 'grayColor':
        return grayColor(1. - min(1., 0.3*self.c + 0.59*self.m + 0.11*self.y + self.k))
    
    @property
    def as_rgb(self) -> 'rgbColor':
        return rgbColor((1-self.c)*(1-self.k), (1-self.m)*(1-self.k), (1-self.y)*(1-self.k))

    @property
    def complement(self) -> 'cmykColor':
        return self.as_cmy.complement.as_cmyk

class cmyColor(Color):
    """A subclass of Color for colors in the cmy base color model"""
    model = ColorModel.cmy

    def __init__(self, c:float, m:float, y:float) -> None:
        self.c:float = c
        self.m:float = m
        self.y:float = y
    
    @property
    def as_list(self) -> List[float]:
        return [self.c, self.m, self.y]
    
    @property
    def as_cmy(self) -> 'cmyColor':
        return self
    
    @property
    def as_cmyk(self) -> 'cmykColor':
        k = min((self.c, self.m, self.y))
        ck = min(1., max(0., self.c - k))
        mk = min(1., max(0., self.m - k))
        yk = min(1., max(0., self.y - k))
        return cmykColor(ck,mk,yk,k)
    
    @property
    def as_rgb(self) -> 'rgbColor':
        return rgbColor(1.-self.c, 1.-self.m, 1.-self.y)
    
    @property
    def as_gray(self) -> 'grayColor':
        gray = 1. - (0.3*self.c + 0.59*self.m + 0.11*self.y)
        return grayColor(gray)

    @property
    def as_hsb(self) -> 'hsbColor':
        return self.as_rgb.as_hsb
    
    @property
    def complement(self) -> 'cmyColor':
        return cmyColor(1.-self.c, 1.-self.m, 1.-self.y)

class hsbColor(Color):
    """A subclass of Color for colors in the hsb base color model"""
    model = ColorModel.hsb

    def __init__(self, h:float, s:float, b:float) -> None:
        self.h:float = h
        self.s:float = s
        self.b:float = b
    
    @property
    def as_list(self) -> List[float]:
        return [self.h, self.s, self.b]
    
    @property
    def as_hsb(self) -> 'hsbColor':
        return self
    
    @property
    def as_cmyk(self) -> 'cmykColor':
        return self.as_rgb.as_cmyk
    
    @property
    def as_cmy(self) -> 'cmyColor':
        return self.as_rgb.as_cmy
    
    @property
    def as_rgb(self) -> 'rgbColor':
        if self.s == 0.: return rgbColor(self.b, self.b, self.b)
        i = int(self.h*6.)
        f = (self.h*6.)-i
        p,q,t = self.b*(1.-self.s), self.b*(1.-self.s*f), self.b*(1.-self.s*(1.-f))
        i%=6
        if i == 0: return rgbColor(self.b, t, p)
        if i == 1: return rgbColor(q, self.b, p)
        if i == 2: return rgbColor(p, self.b, t)
        if i == 3: return rgbColor(p, q, self.b)
        if i == 4: return rgbColor(t, p, self.b)
        return rgbColor(self.b, p, q)
    
    @property
    def as_gray(self) -> 'grayColor':
        return self.as_rgb.as_gray
    
    @property
    def complement(self) -> 'hsbColor':
        h = self.h+0.5 if self.h < 0.5 else self.h-0.5
        b = 1. - self.b*(1.-self.s)
        s = 0. if self.b == 0. else (self.b*self.s)/b
        return hsbColor(h,s,b)

class waveColor(Color):
    """A subclass of Color for colors in the wave base color model.

    (c.f. Section 6.3.12, pg 55, xcolor v2.12, 2016/05/11)
    """
    model = ColorModel.wave

    def __init__(self, freq:float) -> None:
        self.freq:float = freq
    
    @property
    def wrapped(self) -> 'Color':
        return self

    @property
    def as_list(self) -> List[float]:
        return [self.freq]
    
    def mix(self, mix_color:'Color', p:float) -> 'waveColor':
        if not isinstance(mix_color, waveColor):
            raise ColorError('Unable to mix non-wave color into to a wave color.')
        return waveColor(self.freq * (p/100.) + (1. - p/100.)*mix_color.freq)

    @property
    def as_wave(self) -> 'waveColor':
        return self

    @property
    def as_rgb(self) -> 'rgbColor':
        return self.as_hsb.as_rgb

    @property
    def as_hsb(self) -> 'hsbColor':
        if self.freq<440:
            h = 1./6.*(4.+max(min((self.freq-440)/(380-440),1.),0.))
        elif self.freq < 490:
            h = 1./6.*(4.-max(min((self.freq-440)/(490-440),1.),0.))
        elif self.freq < 510:
            h = 1./6.*(2.+max(min((self.freq-510)/(490-510),1.),0.))
        elif self.freq < 580:
            h = 1./6.*(2.-max(min((self.freq-510)/(580-510),1.),0.))
        elif self.freq < 645:
            h = 1./6.*max(min((self.freq-645)/(580-645),1.),0.)
        else:
            h = 0.
        if self.freq < 420:
            b = 0.3+0.7*(self.freq-380)/(420-380)
        elif self.freq < 700:
            b = 1
        else:
            b = 0.3+0.7*(self.freq-780)/(700-780)
        return hsbColor(h,1.,max(min(b,1.),0.))

    @property
    def complement(self) -> 'waveColor':
        raise ColorError('Unable to compute complement of wave color')

class ColorSeries(Color):
    """A subclass of Color for colors defined as a color series.

    A color series has some initial color, an end color, and a series length.
    The color series can be used in the same way as a named color, but can also
    be "stepped" with various schemes to change the associated color.

    Stepping starts from the initial color, moves through the color model
    linearly, and finishes with the end color at the end of the series.
    (c.f. Section 2.9, pg 25, xcolor v2.12, 2016/05/11)
    """
    def __init__(self, model:ColorModel, method:str, base:Color,
            step:List[float] = [], last:Optional[Color] = None) -> None:
        self.model:ColorModel = model
        self.method:str = method
        self.base:Color = base.as_model(self.model)
        self.step:List[float] = step
        self.last:Optional[Color] = last.as_model(self.model) if last is not None else None
        self.stepColor:Color = grayColor(0.)
        self.current:Optional[Color] = None
    
    def __repr__(self) -> str:
        if self.method == 'last':
            return '<ColorSeries(model={},current={},base={},last={})>'.format(self.model,
                    self.current, self.base, self.last)
        else:
            return '<ColorSeries(model={},current{},base={},step={})>'.format(self.model,
                    self.current, self.base, self.step)

    def reset(self, div:float) -> None:
        """Reset the color series to the initial color.
        
        The series step is recalculated, using the length of the color series
        provided as an argument here.
        """
        self.current = self.base
        if self.method == 'step':
            steplist = self.step
        elif self.method == 'grad':
            steplist = [a/div for a in self.step]
        elif self.method == 'last' and self.last is not None:
            steplist = [a/div for a in (self.last-self.base).as_list]
        else:
            raise ColorError('Error applying requested step method')
        self.stepColor = self.makeColor(self.model, steplist)

    def series_step(self) -> None:
        """Step the color to the next color in the series"""
        if not self.current:
            raise ColorError(r'Unable to step color series, missing \resetcolorseries?')
        self.current = self.current + self.stepColor
        self.current = self.current.wrapped
    
    def series_n(self,n:int) -> Color:
        """Return the n-th color in the series"""
        color = self.base
        while n>0:
            color = color + self.stepColor
            color = color.wrapped
            n -= 1
        return color
    
    @property
    def as_list(self) -> List[float]:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.as_list
    
    @property
    def as_hsb(self) -> hsbColor:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.as_hsb
    
    @property
    def as_cmyk(self) -> cmykColor:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.as_cmyk
    
    @property
    def as_cmy(self) -> cmyColor:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.as_cmy

    @property
    def as_rgb(self) -> rgbColor:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.as_rgb
    
    @property
    def as_gray(self) -> grayColor:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.as_gray
    
    @property
    def complement(self) -> Color:
        if not self.current:
            raise ColorError(r'Unable to convert color series, missing \resetcolorseries?')
        return self.current.complement

def basenames(target_model:ColorModel = ColorModel.natural) -> Dict[str,Color]:
    """Return the base color names names dictionary.

    The base colors are always available in xcolor.
    """
    return {
        'red': rgbColor(1., 0., 0.).as_model(target_model),
        'green': rgbColor(0., 1., 0.).as_model(target_model),
        'blue': rgbColor(0., 0., 1.).as_model(target_model),
        'cyan': cmykColor(1., 0., 0., 0.).as_model(target_model),
        'magenta': cmykColor(0., 1., 0., 0.).as_model(target_model),
        'yellow': cmykColor(0., 0., 1., 0.).as_model(target_model),
        'black': grayColor(0.).as_model(target_model),
        'darkgray': grayColor(0.25).as_model(target_model),
        'gray': grayColor(0.5).as_model(target_model),
        'lightgray': grayColor(0.75).as_model(target_model),
        'white': grayColor(1.).as_model(target_model),
        'orange': rgbColor(1.,.5,0.).as_model(target_model),
        'violet': rgbColor(.5,0.,.5).as_model(target_model),
        'purple': rgbColor(.75,0.,.25).as_model(target_model),
        'brown': rgbColor(.75,.5,.25).as_model(target_model),
        'lime': rgbColor(.75,1.,0.).as_model(target_model),
        'pink': rgbColor(1.,.75,.75).as_model(target_model),
        'teal': rgbColor(0.,.5,.5).as_model(target_model),
        'olive': rgbColor(.5,.5,0.).as_model(target_model)
    }

def dvipsnames() -> Dict[str,Color]:
    """Return the dvipsnames dictionary.

    The full list of 68 colors known to dvips, loaded when xcolor is invoked
    with the dvipsnames option.
    """
    return {
        'GreenYellow': cmykColor(0.15,0,0.69,0),
        'Yellow': cmykColor(0,0,1,0),
        'Goldenrod': cmykColor(0,0.10,0.84,0),
        'Dandelion': cmykColor(0,0.29,0.84,0),
        'Apricot': cmykColor(0,0.32,0.52,0),
        'Peach': cmykColor(0,0.50,0.70,0),
        'Melon': cmykColor(0,0.46,0.50,0),
        'YellowOrange': cmykColor(0,0.42,1,0),
        'Orange': cmykColor(0,0.61,0.87,0),
        'BurntOrange': cmykColor(0,0.51,1,0),
        'Bittersweet': cmykColor(0,0.75,1,0.24),
        'RedOrange': cmykColor(0,0.77,0.87,0),
        'Mahogany': cmykColor(0,0.85,0.87,0.35),
        'Maroon': cmykColor(0,0.87,0.68,0.32),
        'BrickRed': cmykColor(0,0.89,0.94,0.28),
        'Red': cmykColor(0,1,1,0),
        'OrangeRed': cmykColor(0,1,0.50,0),
        'RubineRed': cmykColor(0,1,0.13,0),
        'WildStrawberry': cmykColor(0,0.96,0.39,0),
        'Salmon': cmykColor(0,0.53,0.38,0),
        'CarnationPink': cmykColor(0,0.63,0,0),
        'Magenta': cmykColor(0,1,0,0),
        'VioletRed': cmykColor(0,0.81,0,0),
        'Rhodamine': cmykColor(0,0.82,0,0),
        'Mulberry': cmykColor(0.34,0.90,0,0.02),
        'RedViolet': cmykColor(0.07,0.90,0,0.34),
        'Fuchsia': cmykColor(0.47,0.91,0,0.08),
        'Lavender': cmykColor(0,0.48,0,0),
        'Thistle': cmykColor(0.12,0.59,0,0),
        'Orchid': cmykColor(0.32,0.64,0,0),
        'DarkOrchid': cmykColor(0.40,0.80,0.20,0),
        'Purple': cmykColor(0.45,0.86,0,0),
        'Plum': cmykColor(0.50,1,0,0),
        'Violet': cmykColor(0.79,0.88,0,0),
        'RoyalPurple': cmykColor(0.75,0.90,0,0),
        'BlueViolet': cmykColor(0.86,0.91,0,0.04),
        'Periwinkle': cmykColor(0.57,0.55,0,0),
        'CadetBlue': cmykColor(0.62,0.57,0.23,0),
        'CornflowerBlue': cmykColor(0.65,0.13,0,0),
        'MidnightBlue': cmykColor(0.98,0.13,0,0.43),
        'NavyBlue': cmykColor(0.94,0.54,0,0),
        'RoyalBlue': cmykColor(1,0.50,0,0),
        'Blue': cmykColor(1,1,0,0),
        'Cerulean': cmykColor(0.94,0.11,0,0),
        'Cyan': cmykColor(1,0,0,0),
        'ProcessBlue': cmykColor(0.96,0,0,0),
        'SkyBlue': cmykColor(0.62,0,0.12,0),
        'Turquoise': cmykColor(0.85,0,0.20,0),
        'TealBlue': cmykColor(0.86,0,0.34,0.02),
        'Aquamarine': cmykColor(0.82,0,0.30,0),
        'BlueGreen': cmykColor(0.85,0,0.33,0),
        'Emerald': cmykColor(1,0,0.50,0),
        'JungleGreen': cmykColor(0.99,0,0.52,0),
        'SeaGreen': cmykColor(0.69,0,0.50,0),
        'Green': cmykColor(1,0,1,0),
        'ForestGreen': cmykColor(0.91,0,0.88,0.12),
        'PineGreen': cmykColor(0.92,0,0.59,0.25),
        'LimeGreen': cmykColor(0.50,0,1,0),
        'YellowGreen': cmykColor(0.44,0,0.74,0),
        'SpringGreen': cmykColor(0.26,0,0.76,0),
        'OliveGreen': cmykColor(0.64,0,0.95,0.40),
        'RawSienna': cmykColor(0,0.72,1,0.45),
        'Sepia': cmykColor(0,0.83,1,0.70),
        'Brown': cmykColor(0,0.81,1,0.60),
        'Tan': cmykColor(0.14,0.42,0.56,0),
        'Gray': cmykColor(0,0,0,0.50),
        'Black': cmykColor(0,0,0,1),
        'White': cmykColor(0,0,0,0)
    }

def svgnames() -> Dict[str,Color]:
    """Return the svgnames dictionary.

    The full list of 151 colors defined by the SVG 1.1 specification, loaded
    when xcolor is invoked with the svgnames option.
    """
    return {
        'AliceBlue': rgbColor(.94,.972,1),
        'AntiqueWhite': rgbColor(.98,.92,.844),
        'Aqua': rgbColor(0,1,1),
        'Aquamarine': rgbColor(.498,1,.83),
        'Azure': rgbColor(.94,1,1),
        'Beige': rgbColor(.96,.96,.864),
        'Bisque': rgbColor(1,.894,.77),
        'Black': rgbColor(0,0,0),
        'BlanchedAlmond': rgbColor(1,.92,.804),
        'Blue': rgbColor(0,0,1),
        'BlueViolet': rgbColor(.54,.17,.888),
        'Brown': rgbColor(.648,.165,.165),
        'BurlyWood': rgbColor(.87,.72,.53),
        'CadetBlue': rgbColor(.372,.62,.628),
        'Chartreuse': rgbColor(.498,1,0),
        'Chocolate': rgbColor(.824,.41,.116),
        'Coral': rgbColor(1,.498,.312),
        'CornflowerBlue': rgbColor(.392,.585,.93),
        'Cornsilk': rgbColor(1,.972,.864),
        'Crimson': rgbColor(.864,.08,.235),
        'Cyan': rgbColor(0,1,1),
        'DarkBlue': rgbColor(0,0,.545),
        'DarkCyan': rgbColor(0,.545,.545),
        'DarkGoldenrod': rgbColor(.72,.525,.044),
        'DarkGray': rgbColor(.664,.664,.664),
        'DarkGreen': rgbColor(0,.392,0),
        'DarkGrey': rgbColor(.664,.664,.664),
        'DarkKhaki': rgbColor(.74,.716,.42),
        'DarkMagenta': rgbColor(.545,0,.545),
        'DarkOliveGreen': rgbColor(.332,.42,.185),
        'DarkOrange': rgbColor(1,.55,0),
        'DarkOrchid': rgbColor(.6,.196,.8),
        'DarkRed': rgbColor(.545,0,0),
        'DarkSalmon': rgbColor(.912,.59,.48),
        'DarkSeaGreen': rgbColor(.56,.736,.56),
        'DarkSlateBlue': rgbColor(.284,.24,.545),
        'DarkSlateGray': rgbColor(.185,.31,.31),
        'DarkSlateGrey': rgbColor(.185,.31,.31),
        'DarkTurquoise': rgbColor(0,.808,.82),
        'DarkViolet': rgbColor(.58,0,.828),
        'DeepPink': rgbColor(1,.08,.576),
        'DeepSkyBlue': rgbColor(0,.75,1),
        'DimGray': rgbColor(.41,.41,.41),
        'DimGrey': rgbColor(.41,.41,.41),
        'DodgerBlue': rgbColor(.116,.565,1),
        'FireBrick': rgbColor(.698,.132,.132),
        'FloralWhite': rgbColor(1,.98,.94),
        'ForestGreen': rgbColor(.132,.545,.132),
        'Fuchsia': rgbColor(1,0,1),
        'Gainsboro': rgbColor(.864,.864,.864),
        'GhostWhite': rgbColor(.972,.972,1),
        'Gold': rgbColor(1,.844,0),
        'Goldenrod': rgbColor(.855,.648,.125),
        'Gray': rgbColor(.5,.5,.5),
        'Green': rgbColor(0,.5,0),
        'GreenYellow': rgbColor(.68,1,.185),
        'Grey': rgbColor(.5,.5,.5),
        'Honeydew': rgbColor(.94,1,.94),
        'HotPink': rgbColor(1,.41,.705),
        'IndianRed': rgbColor(.804,.36,.36),
        'Indigo': rgbColor(.294,0,.51),
        'Ivory': rgbColor(1,1,.94),
        'Khaki': rgbColor(.94,.9,.55),
        'Lavender': rgbColor(.9,.9,.98),
        'LavenderBlush': rgbColor(1,.94,.96),
        'LawnGreen': rgbColor(.488,.99,0),
        'LemonChiffon': rgbColor(1,.98,.804),
        'LightBlue': rgbColor(.68,.848,.9),
        'LightCoral': rgbColor(.94,.5,.5),
        'LightCyan': rgbColor(.88,1,1),
        'LightGoldenrod': rgbColor(.933,.867,.51),
        'LightGoldenrodYellow': rgbColor(.98,.98,.824),
        'LightGray': rgbColor(.828,.828,.828),
        'LightGreen': rgbColor(.565,.932,.565),
        'LightGrey': rgbColor(.828,.828,.828),
        'LightPink': rgbColor(1,.712,.756),
        'LightSalmon': rgbColor(1,.628,.48),
        'LightSeaGreen': rgbColor(.125,.698,.668),
        'LightSkyBlue': rgbColor(.53,.808,.98),
        'LightSlateBlue': rgbColor(.518,.44,1),
        'LightSlateGray': rgbColor(.468,.532,.6),
        'LightSlateGrey': rgbColor(.468,.532,.6),
        'LightSteelBlue': rgbColor(.69,.77,.87),
        'LightYellow': rgbColor(1,1,.88),
        'Lime': rgbColor(0,1,0),
        'LimeGreen': rgbColor(.196,.804,.196),
        'Linen': rgbColor(.98,.94,.9),
        'Magenta': rgbColor(1,0,1),
        'Maroon': rgbColor(.5,0,0),
        'MediumAquamarine': rgbColor(.4,.804,.668),
        'MediumBlue': rgbColor(0,0,.804),
        'MediumOrchid': rgbColor(.73,.332,.828),
        'MediumPurple': rgbColor(.576,.44,.86),
        'MediumSeaGreen': rgbColor(.235,.7,.444),
        'MediumSlateBlue': rgbColor(.484,.408,.932),
        'MediumSpringGreen': rgbColor(0,.98,.604),
        'MediumTurquoise': rgbColor(.284,.82,.8),
        'MediumVioletRed': rgbColor(.78,.084,.52),
        'MidnightBlue': rgbColor(.098,.098,.44),
        'MintCream': rgbColor(.96,1,.98),
        'MistyRose': rgbColor(1,.894,.884),
        'Moccasin': rgbColor(1,.894,.71),
        'NavajoWhite': rgbColor(1,.87,.68),
        'Navy': rgbColor(0,0,.5),
        'NavyBlue': rgbColor(0,0,.5),
        'OldLace': rgbColor(.992,.96,.9),
        'Olive': rgbColor(.5,.5,0),
        'OliveDrab': rgbColor(.42,.556,.136),
        'Orange': rgbColor(1,.648,0),
        'OrangeRed': rgbColor(1,.27,0),
        'Orchid': rgbColor(.855,.44,.84),
        'PaleGoldenrod': rgbColor(.932,.91,.668),
        'PaleGreen': rgbColor(.596,.985,.596),
        'PaleTurquoise': rgbColor(.688,.932,.932),
        'PaleVioletRed': rgbColor(.86,.44,.576),
        'PapayaWhip': rgbColor(1,.936,.835),
        'PeachPuff': rgbColor(1,.855,.725),
        'Peru': rgbColor(.804,.52,.248),
        'Pink': rgbColor(1,.752,.796),
        'Plum': rgbColor(.868,.628,.868),
        'PowderBlue': rgbColor(.69,.88,.9),
        'Purple': rgbColor(.5,0,.5),
        'Red': rgbColor(1,0,0),
        'RosyBrown': rgbColor(.736,.56,.56),
        'RoyalBlue': rgbColor(.255,.41,.884),
        'SaddleBrown': rgbColor(.545,.27,.075),
        'Salmon': rgbColor(.98,.5,.448),
        'SandyBrown': rgbColor(.956,.644,.376),
        'SeaGreen': rgbColor(.18,.545,.34),
        'Seashell': rgbColor(1,.96,.932),
        'Sienna': rgbColor(.628,.32,.176),
        'Silver': rgbColor(.752,.752,.752),
        'SkyBlue': rgbColor(.53,.808,.92),
        'SlateBlue': rgbColor(.415,.352,.804),
        'SlateGray': rgbColor(.44,.5,.565),
        'SlateGrey': rgbColor(.44,.5,.565),
        'Snow': rgbColor(1,.98,.98),
        'SpringGreen': rgbColor(0,1,.498),
        'SteelBlue': rgbColor(.275,.51,.705),
        'Tan': rgbColor(.824,.705,.55),
        'Teal': rgbColor(0,.5,.5),
        'Thistle': rgbColor(.848,.75,.848),
        'Tomato': rgbColor(1,.39,.28),
        'Turquoise': rgbColor(.25,.88,.815),
        'Violet': rgbColor(.932,.51,.932),
        'VioletRed': rgbColor(.816,.125,.565),
        'Wheat': rgbColor(.96,.87,.7),
        'White': rgbColor(1,1,1),
        'WhiteSmoke': rgbColor(.96,.96,.96),
        'Yellow': rgbColor(1,1,0),
        'YellowGreen': rgbColor(.604,.804,.196)
    }

def x11names() -> Dict[str,Color]:
    """Return the x11names dictionary.

    The full list of 317 colors traditionally shipped with a X11 installation,
    loaded when xcolor is invoked with the x11names option.
    """
    return {
        'AntiqueWhite1': rgbColor(1,.936,.86),
        'AntiqueWhite2': rgbColor(.932,.875,.8),
        'AntiqueWhite3': rgbColor(.804,.752,.69),
        'AntiqueWhite4': rgbColor(.545,.512,.47),
        'Aquamarine1': rgbColor(.498,1,.83),
        'Aquamarine2': rgbColor(.464,.932,.776),
        'Aquamarine3': rgbColor(.4,.804,.668),
        'Aquamarine4': rgbColor(.27,.545,.455),
        'Azure1': rgbColor(.94,1,1),
        'Azure2': rgbColor(.88,.932,.932),
        'Azure3': rgbColor(.756,.804,.804),
        'Azure4': rgbColor(.512,.545,.545),
        'Bisque1': rgbColor(1,.894,.77),
        'Bisque2': rgbColor(.932,.835,.716),
        'Bisque3': rgbColor(.804,.716,.62),
        'Bisque4': rgbColor(.545,.49,.42),
        'Blue1': rgbColor(0,0,1),
        'Blue2': rgbColor(0,0,.932),
        'Blue3': rgbColor(0,0,.804),
        'Blue4': rgbColor(0,0,.545),
        'Brown1': rgbColor(1,.25,.25),
        'Brown2': rgbColor(.932,.23,.23),
        'Brown3': rgbColor(.804,.2,.2),
        'Brown4': rgbColor(.545,.136,.136),
        'Burlywood1': rgbColor(1,.828,.608),
        'Burlywood2': rgbColor(.932,.772,.57),
        'Burlywood3': rgbColor(.804,.668,.49),
        'Burlywood4': rgbColor(.545,.45,.332),
        'CadetBlue1': rgbColor(.596,.96,1),
        'CadetBlue2': rgbColor(.556,.898,.932),
        'CadetBlue3': rgbColor(.48,.772,.804),
        'CadetBlue4': rgbColor(.325,.525,.545),
        'Chartreuse1': rgbColor(.498,1,0),
        'Chartreuse2': rgbColor(.464,.932,0),
        'Chartreuse3': rgbColor(.4,.804,0),
        'Chartreuse4': rgbColor(.27,.545,0),
        'Chocolate1': rgbColor(1,.498,.14),
        'Chocolate2': rgbColor(.932,.464,.13),
        'Chocolate3': rgbColor(.804,.4,.112),
        'Chocolate4': rgbColor(.545,.27,.075),
        'Coral1': rgbColor(1,.448,.336),
        'Coral2': rgbColor(.932,.415,.312),
        'Coral3': rgbColor(.804,.356,.27),
        'Coral4': rgbColor(.545,.244,.185),
        'Cornsilk1': rgbColor(1,.972,.864),
        'Cornsilk2': rgbColor(.932,.91,.804),
        'Cornsilk3': rgbColor(.804,.785,.694),
        'Cornsilk4': rgbColor(.545,.532,.47),
        'Cyan1': rgbColor(0,1,1),
        'Cyan2': rgbColor(0,.932,.932),
        'Cyan3': rgbColor(0,.804,.804),
        'Cyan4': rgbColor(0,.545,.545),
        'DarkGoldenrod1': rgbColor(1,.725,.06),
        'DarkGoldenrod2': rgbColor(.932,.68,.055),
        'DarkGoldenrod3': rgbColor(.804,.585,.048),
        'DarkGoldenrod4': rgbColor(.545,.396,.03),
        'DarkOliveGreen1': rgbColor(.792,1,.44),
        'DarkOliveGreen2': rgbColor(.736,.932,.408),
        'DarkOliveGreen3': rgbColor(.635,.804,.352),
        'DarkOliveGreen4': rgbColor(.43,.545,.24),
        'DarkOrange1': rgbColor(1,.498,0),
        'DarkOrange2': rgbColor(.932,.464,0),
        'DarkOrange3': rgbColor(.804,.4,0),
        'DarkOrange4': rgbColor(.545,.27,0),
        'DarkOrchid1': rgbColor(.75,.244,1),
        'DarkOrchid2': rgbColor(.698,.228,.932),
        'DarkOrchid3': rgbColor(.604,.196,.804),
        'DarkOrchid4': rgbColor(.408,.132,.545),
        'DarkSeaGreen1': rgbColor(.756,1,.756),
        'DarkSeaGreen2': rgbColor(.705,.932,.705),
        'DarkSeaGreen3': rgbColor(.608,.804,.608),
        'DarkSeaGreen4': rgbColor(.41,.545,.41),
        'DarkSlateGray1': rgbColor(.592,1,1),
        'DarkSlateGray2': rgbColor(.552,.932,.932),
        'DarkSlateGray3': rgbColor(.475,.804,.804),
        'DarkSlateGray4': rgbColor(.32,.545,.545),
        'DeepPink1': rgbColor(1,.08,.576),
        'DeepPink2': rgbColor(.932,.07,.536),
        'DeepPink3': rgbColor(.804,.064,.464),
        'DeepPink4': rgbColor(.545,.04,.312),
        'DeepSkyBlue1': rgbColor(0,.75,1),
        'DeepSkyBlue2': rgbColor(0,.698,.932),
        'DeepSkyBlue3': rgbColor(0,.604,.804),
        'DeepSkyBlue4': rgbColor(0,.408,.545),
        'DodgerBlue1': rgbColor(.116,.565,1),
        'DodgerBlue2': rgbColor(.11,.525,.932),
        'DodgerBlue3': rgbColor(.094,.455,.804),
        'DodgerBlue4': rgbColor(.064,.305,.545),
        'Firebrick1': rgbColor(1,.19,.19),
        'Firebrick2': rgbColor(.932,.172,.172),
        'Firebrick3': rgbColor(.804,.15,.15),
        'Firebrick4': rgbColor(.545,.1,.1),
        'Gold1': rgbColor(1,.844,0),
        'Gold2': rgbColor(.932,.79,0),
        'Gold3': rgbColor(.804,.68,0),
        'Gold4': rgbColor(.545,.46,0),
        'Goldenrod1': rgbColor(1,.756,.145),
        'Goldenrod2': rgbColor(.932,.705,.132),
        'Goldenrod3': rgbColor(.804,.608,.112),
        'Goldenrod4': rgbColor(.545,.41,.08),
        'Green1': rgbColor(0,1,0),
        'Green2': rgbColor(0,.932,0),
        'Green3': rgbColor(0,.804,0),
        'Green4': rgbColor(0,.545,0),
        'Honeydew1': rgbColor(.94,1,.94),
        'Honeydew2': rgbColor(.88,.932,.88),
        'Honeydew3': rgbColor(.756,.804,.756),
        'Honeydew4': rgbColor(.512,.545,.512),
        'HotPink1': rgbColor(1,.43,.705),
        'HotPink2': rgbColor(.932,.415,.655),
        'HotPink3': rgbColor(.804,.376,.565),
        'HotPink4': rgbColor(.545,.228,.385),
        'IndianRed1': rgbColor(1,.415,.415),
        'IndianRed2': rgbColor(.932,.39,.39),
        'IndianRed3': rgbColor(.804,.332,.332),
        'IndianRed4': rgbColor(.545,.228,.228),
        'Ivory1': rgbColor(1,1,.94),
        'Ivory2': rgbColor(.932,.932,.88),
        'Ivory3': rgbColor(.804,.804,.756),
        'Ivory4': rgbColor(.545,.545,.512),
        'Khaki1': rgbColor(1,.965,.56),
        'Khaki2': rgbColor(.932,.9,.52),
        'Khaki3': rgbColor(.804,.776,.45),
        'Khaki4': rgbColor(.545,.525,.305),
        'LavenderBlush1': rgbColor(1,.94,.96),
        'LavenderBlush2': rgbColor(.932,.88,.898),
        'LavenderBlush3': rgbColor(.804,.756,.772),
        'LavenderBlush4': rgbColor(.545,.512,.525),
        'LemonChiffon1': rgbColor(1,.98,.804),
        'LemonChiffon2': rgbColor(.932,.912,.75),
        'LemonChiffon3': rgbColor(.804,.79,.648),
        'LemonChiffon4': rgbColor(.545,.536,.44),
        'LightBlue1': rgbColor(.75,.936,1),
        'LightBlue2': rgbColor(.698,.875,.932),
        'LightBlue3': rgbColor(.604,.752,.804),
        'LightBlue4': rgbColor(.408,.512,.545),
        'LightCyan1': rgbColor(.88,1,1),
        'LightCyan2': rgbColor(.82,.932,.932),
        'LightCyan3': rgbColor(.705,.804,.804),
        'LightCyan4': rgbColor(.48,.545,.545),
        'LightGoldenrod1': rgbColor(1,.925,.545),
        'LightGoldenrod2': rgbColor(.932,.864,.51),
        'LightGoldenrod3': rgbColor(.804,.745,.44),
        'LightGoldenrod4': rgbColor(.545,.505,.298),
        'LightPink1': rgbColor(1,.684,.725),
        'LightPink2': rgbColor(.932,.635,.68),
        'LightPink3': rgbColor(.804,.55,.585),
        'LightPink4': rgbColor(.545,.372,.396),
        'LightSalmon1': rgbColor(1,.628,.48),
        'LightSalmon2': rgbColor(.932,.585,.448),
        'LightSalmon3': rgbColor(.804,.505,.385),
        'LightSalmon4': rgbColor(.545,.34,.26),
        'LightSkyBlue1': rgbColor(.69,.888,1),
        'LightSkyBlue2': rgbColor(.644,.828,.932),
        'LightSkyBlue3': rgbColor(.552,.712,.804),
        'LightSkyBlue4': rgbColor(.376,.484,.545),
        'LightSteelBlue1': rgbColor(.792,.884,1),
        'LightSteelBlue2': rgbColor(.736,.824,.932),
        'LightSteelBlue3': rgbColor(.635,.71,.804),
        'LightSteelBlue4': rgbColor(.43,.484,.545),
        'LightYellow1': rgbColor(1,1,.88),
        'LightYellow2': rgbColor(.932,.932,.82),
        'LightYellow3': rgbColor(.804,.804,.705),
        'LightYellow4': rgbColor(.545,.545,.48),
        'Magenta1': rgbColor(1,0,1),
        'Magenta2': rgbColor(.932,0,.932),
        'Magenta3': rgbColor(.804,0,.804),
        'Magenta4': rgbColor(.545,0,.545),
        'Maroon1': rgbColor(1,.204,.7),
        'Maroon2': rgbColor(.932,.19,.655),
        'Maroon3': rgbColor(.804,.16,.565),
        'Maroon4': rgbColor(.545,.11,.385),
        'MediumOrchid1': rgbColor(.88,.4,1),
        'MediumOrchid2': rgbColor(.82,.372,.932),
        'MediumOrchid3': rgbColor(.705,.32,.804),
        'MediumOrchid4': rgbColor(.48,.215,.545),
        'MediumPurple1': rgbColor(.67,.51,1),
        'MediumPurple2': rgbColor(.624,.475,.932),
        'MediumPurple3': rgbColor(.536,.408,.804),
        'MediumPurple4': rgbColor(.365,.28,.545),
        'MistyRose1': rgbColor(1,.894,.884),
        'MistyRose2': rgbColor(.932,.835,.824),
        'MistyRose3': rgbColor(.804,.716,.71),
        'MistyRose4': rgbColor(.545,.49,.484),
        'NavajoWhite1': rgbColor(1,.87,.68),
        'NavajoWhite2': rgbColor(.932,.81,.63),
        'NavajoWhite3': rgbColor(.804,.7,.545),
        'NavajoWhite4': rgbColor(.545,.475,.37),
        'OliveDrab1': rgbColor(.752,1,.244),
        'OliveDrab2': rgbColor(.7,.932,.228),
        'OliveDrab3': rgbColor(.604,.804,.196),
        'OliveDrab4': rgbColor(.41,.545,.132),
        'Orange1': rgbColor(1,.648,0),
        'Orange2': rgbColor(.932,.604,0),
        'Orange3': rgbColor(.804,.52,0),
        'Orange4': rgbColor(.545,.352,0),
        'OrangeRed1': rgbColor(1,.27,0),
        'OrangeRed2': rgbColor(.932,.25,0),
        'OrangeRed3': rgbColor(.804,.215,0),
        'OrangeRed4': rgbColor(.545,.145,0),
        'Orchid1': rgbColor(1,.512,.98),
        'Orchid2': rgbColor(.932,.48,.912),
        'Orchid3': rgbColor(.804,.41,.79),
        'Orchid4': rgbColor(.545,.28,.536),
        'PaleGreen1': rgbColor(.604,1,.604),
        'PaleGreen2': rgbColor(.565,.932,.565),
        'PaleGreen3': rgbColor(.488,.804,.488),
        'PaleGreen4': rgbColor(.33,.545,.33),
        'PaleTurquoise1': rgbColor(.732,1,1),
        'PaleTurquoise2': rgbColor(.684,.932,.932),
        'PaleTurquoise3': rgbColor(.59,.804,.804),
        'PaleTurquoise4': rgbColor(.4,.545,.545),
        'PaleVioletRed1': rgbColor(1,.51,.67),
        'PaleVioletRed2': rgbColor(.932,.475,.624),
        'PaleVioletRed3': rgbColor(.804,.408,.536),
        'PaleVioletRed4': rgbColor(.545,.28,.365),
        'PeachPuff1': rgbColor(1,.855,.725),
        'PeachPuff2': rgbColor(.932,.796,.68),
        'PeachPuff3': rgbColor(.804,.688,.585),
        'PeachPuff4': rgbColor(.545,.468,.396),
        'Pink1': rgbColor(1,.71,.772),
        'Pink2': rgbColor(.932,.664,.72),
        'Pink3': rgbColor(.804,.57,.62),
        'Pink4': rgbColor(.545,.39,.424),
        'Plum1': rgbColor(1,.732,1),
        'Plum2': rgbColor(.932,.684,.932),
        'Plum3': rgbColor(.804,.59,.804),
        'Plum4': rgbColor(.545,.4,.545),
        'Purple1': rgbColor(.608,.19,1),
        'Purple2': rgbColor(.57,.172,.932),
        'Purple3': rgbColor(.49,.15,.804),
        'Purple4': rgbColor(.332,.1,.545),
        'Red1': rgbColor(1,0,0),
        'Red2': rgbColor(.932,0,0),
        'Red3': rgbColor(.804,0,0),
        'Red4': rgbColor(.545,0,0),
        'RosyBrown1': rgbColor(1,.756,.756),
        'RosyBrown2': rgbColor(.932,.705,.705),
        'RosyBrown3': rgbColor(.804,.608,.608),
        'RosyBrown4': rgbColor(.545,.41,.41),
        'RoyalBlue1': rgbColor(.284,.464,1),
        'RoyalBlue2': rgbColor(.264,.43,.932),
        'RoyalBlue3': rgbColor(.228,.372,.804),
        'RoyalBlue4': rgbColor(.152,.25,.545),
        'Salmon1': rgbColor(1,.55,.41),
        'Salmon2': rgbColor(.932,.51,.385),
        'Salmon3': rgbColor(.804,.44,.33),
        'Salmon4': rgbColor(.545,.298,.224),
        'SeaGreen1': rgbColor(.33,1,.624),
        'SeaGreen2': rgbColor(.305,.932,.58),
        'SeaGreen3': rgbColor(.264,.804,.5),
        'SeaGreen4': rgbColor(.18,.545,.34),
        'Seashell1': rgbColor(1,.96,.932),
        'Seashell2': rgbColor(.932,.898,.87),
        'Seashell3': rgbColor(.804,.772,.75),
        'Seashell4': rgbColor(.545,.525,.51),
        'Sienna1': rgbColor(1,.51,.28),
        'Sienna2': rgbColor(.932,.475,.26),
        'Sienna3': rgbColor(.804,.408,.224),
        'Sienna4': rgbColor(.545,.28,.15),
        'SkyBlue1': rgbColor(.53,.808,1),
        'SkyBlue2': rgbColor(.494,.752,.932),
        'SkyBlue3': rgbColor(.424,.65,.804),
        'SkyBlue4': rgbColor(.29,.44,.545),
        'SlateBlue1': rgbColor(.512,.435,1),
        'SlateBlue2': rgbColor(.48,.404,.932),
        'SlateBlue3': rgbColor(.41,.35,.804),
        'SlateBlue4': rgbColor(.28,.235,.545),
        'SlateGray1': rgbColor(.776,.888,1),
        'SlateGray2': rgbColor(.725,.828,.932),
        'SlateGray3': rgbColor(.624,.712,.804),
        'SlateGray4': rgbColor(.424,.484,.545),
        'Snow1': rgbColor(1,.98,.98),
        'Snow2': rgbColor(.932,.912,.912),
        'Snow3': rgbColor(.804,.79,.79),
        'Snow4': rgbColor(.545,.536,.536),
        'SpringGreen1': rgbColor(0,1,.498),
        'SpringGreen2': rgbColor(0,.932,.464),
        'SpringGreen3': rgbColor(0,.804,.4),
        'SpringGreen4': rgbColor(0,.545,.27),
        'SteelBlue1': rgbColor(.39,.72,1),
        'SteelBlue2': rgbColor(.36,.675,.932),
        'SteelBlue3': rgbColor(.31,.58,.804),
        'SteelBlue4': rgbColor(.21,.392,.545),
        'Tan1': rgbColor(1,.648,.31),
        'Tan2': rgbColor(.932,.604,.288),
        'Tan3': rgbColor(.804,.52,.248),
        'Tan4': rgbColor(.545,.352,.17),
        'Thistle1': rgbColor(1,.884,1),
        'Thistle2': rgbColor(.932,.824,.932),
        'Thistle3': rgbColor(.804,.71,.804),
        'Thistle4': rgbColor(.545,.484,.545),
        'Tomato1': rgbColor(1,.39,.28),
        'Tomato2': rgbColor(.932,.36,.26),
        'Tomato3': rgbColor(.804,.31,.224),
        'Tomato4': rgbColor(.545,.21,.15),
        'Turquoise1': rgbColor(0,.96,1),
        'Turquoise2': rgbColor(0,.898,.932),
        'Turquoise3': rgbColor(0,.772,.804),
        'Turquoise4': rgbColor(0,.525,.545),
        'VioletRed1': rgbColor(1,.244,.59),
        'VioletRed2': rgbColor(.932,.228,.55),
        'VioletRed3': rgbColor(.804,.196,.47),
        'VioletRed4': rgbColor(.545,.132,.32),
        'Wheat1': rgbColor(1,.905,.73),
        'Wheat2': rgbColor(.932,.848,.684),
        'Wheat3': rgbColor(.804,.73,.59),
        'Wheat4': rgbColor(.545,.494,.4),
        'Yellow1': rgbColor(1,1,0),
        'Yellow2': rgbColor(.932,.932,0),
        'Yellow3': rgbColor(.804,.804,0),
        'Yellow4': rgbColor(.545,.545,0),
        'Gray0': rgbColor(.745,.745,.745),
        'Green0': rgbColor(0,1,0),
        'Grey0': rgbColor(.745,.745,.745),
        'Maroon0': rgbColor(.69,.19,.376),
        'Purple0': rgbColor(.628,.125,.94)
    }

def ProcessOptions(options, document): # type: ignore
    """ Load the xcolor package.

    Sets the target model, loads any requested colors, sets the package
    defaults, and defines the always available 19 color names.
    """
    colors:Dict[colors] = {}
    target_model:ColorModel = ColorModel.natural
    if 'rgb' in options or 'RGB' in options:
        target_model = ColorModel.rgb
    if 'cmy' in options:
        target_model = ColorModel.cmy
    if 'cmyk' in options:
        target_model = ColorModel.cmyk
    if 'gray' in options or 'Gray' in options:
        target_model = ColorModel.gray
    
    document.userdata.setPath('packages/xcolor/target_model', target_model)
    document.userdata.setPath('packages/xcolor/colors', colors)
    document.userdata.setPath('packages/xcolor/colorseriescycle',16.)

    colors.update(basenames(target_model))
    if 'dvipsnames' in options:
        colors.update(dvipsnames())
    if 'svgnames' in options:
        colors.update(svgnames())
    if 'x11names' in options:
        colors.update(x11names())

class ColorCommandClass(Node):
    """A base class used to add a "current color" property to a class.

    Deriving from this class adds a new property current_color, which is useful
    for color mixing.
    """
    @property
    def current_color(self) -> Optional[Color]:
        node = self.parentNode
        while node is not None and not issubclass(node.__class__, ColorEnvironment):
            node = node.parentNode
        if node is not None:
            return node.parser.parseColor(node.attributes['color'], node.attributes['model'])
        else:
            return None

class ColorEnvironment(Environment, ColorCommandClass):
    """A base class for plastex color environments"""
    def invoke(self, tex) -> None:
        Environment.invoke(self, tex)
        u = self.ownerDocument.userdata # type: ignore
        self.parser:ColorParser = ColorParser(
                u.getPath('packages/xcolor/colors'),
                u.getPath('packages/xcolor/target_model'))

class ColorCommand(Command, ColorCommandClass):
    """A base class for plastex color commands"""
    def invoke(self, tex) -> None:
        Command.invoke(self, tex)
        u = self.ownerDocument.userdata # type: ignore
        self.parser:ColorParser = ColorParser(
                u.getPath('packages/xcolor/colors'),
                u.getPath('packages/xcolor/target_model'))
    
class color(ColorEnvironment):
    r"""The \color command (c.f. pg 22, xcolor v2.12, 2016/05/11)"""
    args = '[ model:str ] color:str'

    def digest(self, tokens) -> None:
        Environment.digest(self, tokens)
        self.parser.current_color = self.current_color
        self.color:Color = self.parser.parseColor(self.attributes['color'], self.attributes['model'])
        self.style['color'] = self.color.html

    @property
    def source(self) -> str:
        """Rewrite the source tex to apply the final mixed color directly.

        This ensures colors mixed by xcolor can be displayed when the source
        tex is used in output that doesn't support xcolor, e.g. with mathjax
        and the HTML5 renderer.
        """
        rgb = self.color.as_model(self.parser.target).as_rgb
        return r'\require{{color}}{{\color[rgb]{{{r:.15f},{g:.15f},{b:.15f}}}{children}}}'.format(
                r = rgb.r, g = rgb.g, b= rgb.b, children = sourceChildren(self))

class textcolor(ColorCommand):
    r"""The \textcolor command (c.f. pg 22, xcolor v2.12, 2016/05/11)"""
    args = '[ model:str ] color:str self'

    def digest(self, tokens) -> None:
        Command.digest(self, tokens)
        self.parser.current_color = self.current_color
        self.color:Color = self.parser.parseColor(self.attributes['color'], self.attributes['model'])
        self.style['color'] = self.color.html

class colorbox(ColorCommand):
    r"""The \colorbox command (c.f. pg 22, xcolor v2.12, 2016/05/11)"""
    args = '[ model:str ] color:str self'

    def digest(self, tokens) -> None:
        Command.digest(self, tokens)
        self.parser.current_color = self.current_color
        self.color:Color = self.parser.parseColor(self.attributes['color'], self.attributes['model'])
        self.style['background-color'] = self.color.html

class fcolorbox(ColorCommand):
    r"""The \fcolorbox command (c.f. pg 22, xcolor v2.12, 2016/05/11)"""
    args = '[ f_model:str ] f_color:str [ bg_model:str] bg_color:str self'

    def digest(self, tokens) -> None:
        Command.digest(self, tokens)
        a = self.attributes
        self.parser.current_color = self.current_color
        if a['bg_model'] is None:
            a['bg_model'] = a['f_model']
        self.f_color:Color = self.parser.parseColor(a['f_color'], a['f_model'])
        self.color:Color = self.parser.parseColor(a['bg_color'], a['bg_model'])
        self.style['background-color'] = self.color.html
        self.style['border'] = '1px solid %s' % self.f_color.html

class definecolor(ColorCommand):
    r"""The \definecolor command (c.f. pg 19, xcolor v2.12, 2016/05/11)"""
    args = '[ type:str ] name:str model:str color:str'
    replace:bool = True

    def digest(self, tokens) -> None:
        Command.digest(self, tokens)
        a = self.attributes
        self.parser.current_color = self.current_color
        if self.replace or a['name'] not in self.parser.colors:
            self.parser.colors[a['name']] = self.parser.parseColor(a['color'], a['model'])
    
    @property
    def source(self)->str:
        r"""Rewrite the source tex to ignore the \definecolor command.

        This allows one to define colors in a math expression, even when source
        tex is used as part of output and it doesn't support xcolor, e.g. with
        mathjax and the HTML5 renderer.
        """
        return r'{children}'.format(children = sourceChildren(self))

class DefineNamedColor(definecolor):
    r"""The \DefineNamedColor command, an alternate form of \definecolor.

    (c.f. pg 21, xcolor v2.12, 2016/05/11)
    """
    args = 'type:str name:str model:str color:str'

class providecolor(definecolor):
    r"""The \providecolor command.

    Similar to \definecolor, but the color is only defined if it does not exist
    already. (c.f. pg 19, xcolor v2.12, 2016/05/11)
    """
    replace:bool = False

class preparecolor(definecolor):
    r"""The \preparecolor command, an alternate form of \definecolor.

    (c.f. pg 21, xcolor v2.12, 2016/05/11)
    """
    pass

class colorlet(ColorCommand):
    r"""The \colorlet command (c.f. pg 20, xcolor v2.12, 2016/05/11)"""
    args = '[ type:str ] name:str [ model:str ] color:str'

    def digest(self, tokens) -> None:
        Command.digest(self,tokens)
        a = self.attributes
        self.parser.current_color = self.current_color
        new_color:Color = self.parser.parseColor(a['color'])
        if a['model'] is not None:
            new_color = new_color.as_model(ColorModel[a['model']])
        self.parser.colors[a['name']] = new_color.copy()

class definecolorset(ColorCommand):
    r"""The \definecolorset command (c.f. pg 20, xcolor v2.12, 2016/05/11)"""
    args = '[ type:str ] model:str head:str tail:str set_spec:str'
    replace:bool = True

    def digest(self, tokens) -> None:
        Command.digest(self,tokens)
        a = self.attributes
        self.parser.current_color = self.current_color
        for s in a['set_spec'].split(';'):
            s = s.split(',')
            name = a['head'] + s[0] + a['tail']
            if self.replace or name not in self.parser.colors:
                self.parser.colors[name] = self.parser.parseColor(','.join(s[1:]), a['model'])

class providecolorset(definecolorset):
    r"""The \providecolorset command.

    Similar to \definecolorset, but the colors are only defined if they do not
    already exist. (c.f. pg 20, xcolor v2.12, 2016/05/11)
    """
    replace:bool = False

class preparecolorset(definecolorset):
    r"""The \preparecolorset command, an alternate form of \definecolorset.

    (c.f. pg 21, xcolor v2.12, 2016/05/11)
    """
    pass

class definecolors(ColorCommand):
    r"""The \deinecolors command (c.f. pg 21, xcolor v2.12, 2016/05/11)"""
    args = 'id_list:str'
    replace:bool = True

    def digest(self, tokens) -> None:
        Command.digest(self,tokens)
        a = self.attributes
        self.parser.current_color = self.current_color
        self.parser.scan(a['id_list'])
        id_list = self.parser.id_list()

        if id_list is not None:
            for ids in id_list['idlist']:
                src = self.parser.colors[ids[1]]
                if self.replace or ids[0] not in self.parser.colors:
                    self.parser.colors[ids[0]] = src.copy()
                self.parser.colors[ids[1]] = src

class providecolors(definecolors):
    r"""The \providecolors command.

    Similar to \definecolors, but individual colors are only defined if they do
    not exist already. (c.f. pg 21, xcolor v2.12, 2016/05/11)
    """
    replace:bool = False

class definecolorseries(ColorCommand):
    r"""The \definecolorseries command (c.f. pg 25, xcolor v2.12, 2016/05/11)"""
    args = 'name:str model:str method:str [b_model:str] b_spec:str [s_model:str] s_spec:str'
    
    def digest(self, tokens) -> None:
        Command.digest(self,tokens)
        a = self.attributes
        self.parser.current_color = self.current_color
        self.parser.colors[a['name']] = self.parser.parseColorSeries(a['model'], a['method'],
                a['b_model'], a['b_spec'], a['s_model'], a['s_spec'])

class resetcolorseries(Command):
    r"""The \resetcolorseries command (c.f. pg 26, xcolor v2.12, 2016/05/11)"""
    args = '[ div:str ] name:str'
    def invoke(self, tex) -> None:
        Command.invoke(self, tex)
        a = self.attributes
        u = self.ownerDocument.userdata #type: ignore
        colors = u.getPath('packages/xcolor/colors')
        if a['div'] is not None:
            div = float(a['div'])
        else:
            div = u.getPath('packages/xcolor/colorseriescycle')
        colors[a['name']].reset(div)

class pagecolor(Command):
    r"""The \pagecolor command (not implemented)"""
    args = '[ model:str ] color:str'

class nopagecolor(Command):
    r"""The \nopagecolor command (not implemented)"""
    pass
