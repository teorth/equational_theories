""" simpleTAL Interpreter

		Copyright (c) 2009 Colin Stewart (http://www.owlfish.com/)
		All rights reserved.

		Redistribution and use in source and binary forms, with or without
		modification, are permitted provided that the following conditions
		are met:
		1. Redistributions of source code must retain the above copyright
		   notice, this list of conditions and the following disclaimer.
		2. Redistributions in binary form must reproduce the above copyright
		   notice, this list of conditions and the following disclaimer in the
		   documentation and/or other materials provided with the distribution.
		3. The name of the author may not be used to endorse or promote products
		   derived from this software without specific prior written permission.

		THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
		IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
		OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
		IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
		INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
		NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
		DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
		THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
		(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
		THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

		If you make any bug fixes or feature enhancements please let me know!


		The classes in this module implement the TAL language, expanding
		both XML and HTML templates.

		Module Dependencies: logging, simpleTALES, simpleTALTemplates
"""

import logging

import xml.sax, html, io, re, codecs
from .. import simpletal
import copy, sys
from . import FixedHTMLParser, sgmlentitynames


__version__ = simpletal.__version__

try:
    # Is PyXML's LexicalHandler available?
    from xml.sax.saxlib import LexicalHandler
    use_lexical_handler = 1
except ImportError:
    use_lexical_handler = 0
    class LexicalHandler: # type: ignore # mypy#1153
        pass

try:
	# Is PyXML's DOM2SAX available?
	import xml.dom.ext.Dom2Sax
	use_dom2sax = 1
except ImportError:
	use_dom2sax = 0

# Check Python version.  If 3.3 or later, all SGML entities will be expanded in the HTML Parser
if sys.version_info[0] > 3 or (sys.version_info[0] == 3 and sys.version_info[1] > 3):
	HTML_ENTITIES_PRE_EXPANDED = True
else:
	HTML_ENTITIES_PRE_EXPANDED = False

from . import simpleTALES

# Name-space URIs
METAL_NAME_URI="http://xml.zope.org/namespaces/metal"
TAL_NAME_URI="http://xml.zope.org/namespaces/tal"

# All commands are of the form (opcode, args, commandList)
# The numbers are the opcodes, and also the order of priority

# Argument: [(isLocalFlag (Y/n), variableName, variablePath),...]
TAL_DEFINE = 1
# Argument: expression, endTagSymbol
TAL_CONDITION = 2
# Argument: (varname, expression, endTagSymbol)
TAL_REPEAT = 3
# Argument: (replaceFlag, type, expression)
TAL_CONTENT = 4
# Not used in byte code, only ordering.
TAL_REPLACE = 5
# Argument: [(attributeName, expression)]
TAL_ATTRIBUTES = 6
# Argument: expression
TAL_OMITTAG = 7
# Argument: (originalAttributeList, currentAttributeList)
TAL_START_SCOPE = 8
# Argument: String to output
TAL_OUTPUT = 9
# Argument: None
TAL_STARTTAG = 10
# Argument: Tag, omitTagFlag
TAL_ENDTAG_ENDSCOPE = 11
# Argument: None
TAL_NOOP = 13

# METAL Starts here
# Argument: expression, slotParams, endTagSymbol
METAL_USE_MACRO = 14
# Argument: macroName, endTagSymbol
METAL_DEFINE_SLOT=15
# Only used for parsing
METAL_FILL_SLOT=16
METAL_DEFINE_MACRO=17

METAL_NAME_REGEX = re.compile ("[a-zA-Z_][a-zA-Z0-9_]*")
SINGLETON_XML_REGEX = re.compile (br'^<[^\s/>]+(?:\s*[^=>]+="[^">]+")*\s*/>')
SINGLETON_BYTES_XML_REGEX = re.compile (br'^<[^\s/>]+(?:\s*[^=>]+="[^">]+")*\s*/>')
ENTITY_REF_REGEX = re.compile (r'(?:&[a-zA-Z][\-\.a-zA-Z0-9]*[^\-\.a-zA-Z0-9])|(?:&#[xX]?[a-eA-E0-9]*[^0-9a-eA-E])')

# The list of elements in HTML that can not have end tags - done as a dictionary for fast
# lookup.
HTML_FORBIDDEN_ENDTAG = {'AREA': 1, 'BASE': 1, 'BASEFONT': 1, 'BR': 1, 'COL': 1
						,'FRAME': 1, 'HR': 1, 'IMG': 1, 'INPUT': 1, 'ISINDEX': 1
						,'LINK': 1, 'META': 1, 'PARAM': 1}

# List of element:attribute pairs that can use minimized form in HTML
HTML_BOOLEAN_ATTS = {'AREA:NOHREF': 1, 'IMG:ISMAP': 1, 'OBJECT:DECLARE': 1
									, 'INPUT:CHECKED': 1, 'INPUT:DISABLED': 1, 'INPUT:READONLY': 1, 'INPUT:ISMAP': 1
									, 'SELECT:MULTIPLE': 1, 'SELECT:DISABLED': 1
									, 'OPTGROUP:DISABLED': 1
									, 'OPTION:SELECTED': 1, 'OPTION:DISABLED': 1
									, 'TEXTAREA:DISABLED': 1, 'TEXTAREA:READONLY': 1
									, 'BUTTON:DISABLED': 1, 'SCRIPT:DEFER': 1}

class TemplateInterpreter:
	def __init__ (self):
		self.programStack = []
		self.commandList = None
		self.symbolTable = None
		self.slotParameters = {}
		self.commandHandler  = {}
		self.commandHandler [TAL_DEFINE] = self.cmdDefine
		self.commandHandler [TAL_CONDITION] = self.cmdCondition
		self.commandHandler [TAL_REPEAT] = self.cmdRepeat
		self.commandHandler [TAL_CONTENT] = self.cmdContent
		self.commandHandler [TAL_ATTRIBUTES] = self.cmdAttributes
		self.commandHandler [TAL_OMITTAG] = self.cmdOmitTag
		self.commandHandler [TAL_START_SCOPE] = self.cmdStartScope
		self.commandHandler [TAL_OUTPUT] = self.cmdOutput
		self.commandHandler [TAL_STARTTAG] = self.cmdOutputStartTag
		self.commandHandler [TAL_ENDTAG_ENDSCOPE] = self.cmdEndTagEndScope
		self.commandHandler [METAL_USE_MACRO] = self.cmdUseMacro
		self.commandHandler [METAL_DEFINE_SLOT] = self.cmdDefineSlot
		self.commandHandler [TAL_NOOP] = self.cmdNoOp

	def tagAsText (self, tagObj, singletonFlag=0):
		""" This returns a tag as text.
		"""
		tag,atts = tagObj
		result = ["<"]
		result.append (tag)
		for attName, attValue in atts:
			result.append (' ')
			result.append (attName)
			result.append ('="')
			result.append (html.escape (attValue, quote=1))
			result.append ('"')
		if (singletonFlag):
			result.append (" />")
		else:
			result.append (">")
		return "".join (result)

	def initialise (self, context, outputFile):
		self.context = context
		self.file = outputFile

	def cleanState (self):
		self.scopeStack = []
		self.programCounter = 0
		self.movePCForward = None
		self.movePCBack = None
		self.outputTag = 1
		self.originalAttributes = {}
		self.currentAttributes = []
		# Used in repeat only.
		self.repeatAttributesCopy = []
		self.currentSlots = {}
		self.repeatVariable = None
		self.tagContent = None
		# tagState flag as to whether there are any local variables to pop
		self.localVarsDefined = 0
		# Pass in the parameters
		self.currentSlots = self.slotParameters

	def popProgram (self):
		vars, self.commandList, self.symbolTable = self.programStack.pop()
		self.programCounter,self.scopeStack,self.slotParameters,self.currentSlots, self.movePCForward,self.movePCBack,self.outputTag,self.originalAttributes,self.currentAttributes,self.repeatVariable,self.repeatAttributesCopy,self.tagContent,self.localVarsDefined = vars

	def pushProgram (self):
		vars = (self.programCounter
				,self.scopeStack
				,self.slotParameters
				,self.currentSlots
				,self.movePCForward
				,self.movePCBack
				,self.outputTag
				,self.originalAttributes
				,self.currentAttributes
				,self.repeatVariable
				,self.repeatAttributesCopy
				,self.tagContent
				,self.localVarsDefined)
		self.programStack.append ((vars,self.commandList, self.symbolTable))

	def execute (self, template):
		self.cleanState()
		self.commandList, self.programCounter, programLength, self.symbolTable = template.getProgram()
		cmndList = self.commandList
		while (self.programCounter < programLength):
			cmnd = cmndList [self.programCounter]
			#print "PC: %s  -  Executing command: %s" % (str (self.programCounter), str (cmnd))
			self.commandHandler[cmnd[0]] (cmnd[0], cmnd[1])

	def cmdDefine (self, command, args):
		""" args: [(isLocalFlag (Y/n), variableName, variablePath),...]
				Define variables in either the local or global context
		"""
		foundLocals = 0
		for isLocal, varName, varPath in args:
			result = self.context.evaluate (varPath, self.originalAttributes)
			if (isLocal):
				if (not foundLocals):
					foundLocals = 1
					self.context.pushLocals ()
				self.context.setLocal (varName, result)
			else:
				self.context.addGlobal (varName, result)
		self.localVarsDefined = foundLocals
		self.programCounter += 1

	def cmdCondition (self, command, args):
		""" args: expression, endTagSymbol
				Conditionally continues with execution of all content contained
				by it.
		"""
		result = self.context.evaluate (args[0], self.originalAttributes)
		#~ if (result is None or (not result)):
		conditionFalse = 0
		if (result is None):
			conditionFalse = 1
		else:
			if (not result): conditionFalse = 1
			try:
				temp = len (result)
				if (temp == 0): conditionFalse = 1
			except:
				# Result is not a sequence.
				pass
		if (conditionFalse):
			# Nothing to output - evaluated to false.
			self.outputTag = 0
			self.tagContent = None
			self.programCounter = self.symbolTable[args[1]]
			return
		self.programCounter += 1

	def cmdRepeat (self, command, args):
		""" args: (varName, expression, endTagSymbol)
				Repeats anything in the cmndList
		"""
		if (self.repeatVariable is not None):
			# We are already part way through a repeat
			# Restore any attributes that might have been changed.
			if (self.currentAttributes != self.repeatAttributesCopy):
				self.currentAttributes = copy.copy (self.repeatAttributesCopy)
			self.outputTag = 1
			self.tagContent = None
			self.movePCForward = None

			try:
				self.repeatVariable.increment()
				self.context.setLocal (args[0], self.repeatVariable.getCurrentValue())
				self.programCounter += 1
				return
			except IndexError as e:
				# We have finished the repeat
				self.repeatVariable = None
				self.context.removeRepeat (args[0])
				# The locals were pushed in context.addRepeat
				self.context.popLocals()
				self.movePCBack = None
				# Suppress the final close tag and content
				self.tagContent = None
				self.outputTag = 0
				self.programCounter = self.symbolTable [args[2]]
				# Restore the state of repeatAttributesCopy in case we are nested.
				self.repeatAttributesCopy = self.scopeStack.pop()
				return

		# The first time through this command
		result = self.context.evaluate (args[1], self.originalAttributes)
		if (result is not None and result == simpleTALES.DEFAULTVALUE):
			# Leave everything un-touched.
			self.programCounter += 1
			return
		try:
			# We have three options, either the result is a natural sequence, an iterator, or something that can produce an iterator.
			isSequence = len (result)
			if (isSequence):
				# Only setup if we have a sequence with length
				self.repeatVariable = simpleTALES.RepeatVariable (result)
			else:
				# Delete the tags and their contents
				self.outputTag = 0
				self.programCounter = self.symbolTable [args[2]]
				return
		except:
			# Not a natural sequence, can it produce an iterator?
			if (hasattr (result, "__iter__") and hasattr (result.__iter__, "__call__")):
				# We can get an iterator!
				self.repeatVariable = simpleTALES.IteratorRepeatVariable (result.__iter__())
			elif (hasattr (result, "__next__") and hasattr (result.__next__, "__call__")):
				# Treat as an iterator
				self.repeatVariable = simpleTALES.IteratorRepeatVariable (result)
			else:
				# Just a plain object, let's not loop
				# Delete the tags and their contents
				self.outputTag = 0
				self.programCounter = self.symbolTable [args[2]]
				return

		try:
			curValue = self.repeatVariable.getCurrentValue()
		except IndexError as e:
			# The iterator ran out of values before we started - treat as an empty list
			self.outputTag = 0
			self.repeatVariable = None
			self.programCounter = self.symbolTable [args[2]]
			return
		# We really do want to repeat - so lets do it
		self.movePCBack = self.programCounter
		self.context.addRepeat (args[0], self.repeatVariable, curValue)
		# We keep the old state of the repeatAttributesCopy for nested loops
		self.scopeStack.append (self.repeatAttributesCopy)
		# Keep a copy of the current attributes for this tag
		self.repeatAttributesCopy = copy.copy (self.currentAttributes)
		self.programCounter += 1

	def cmdContent (self, command, args):
		""" args: (replaceFlag, structureFlag, expression, endTagSymbol)
				Expands content
		"""
		result = self.context.evaluate (args[2], self.originalAttributes)
		if (result is None):
			if (args[0]):
				# Only output tags if this is a content not a replace
				self.outputTag = 0
			# Output none of our content or the existing content, but potentially the tags
			self.movePCForward = self.symbolTable [args[3]]
			self.programCounter += 1
			return
		elif (not result == simpleTALES.DEFAULTVALUE):
			# We have content, so let's suppress the natural content and output this!
			if (args[0]):
				self.outputTag = 0
			self.tagContent = (args[1], result)
			self.movePCForward = self.symbolTable [args[3]]
			self.programCounter += 1
			return
		else:
			# Default, let's just run through as normal
			self.programCounter += 1
			return

	def cmdAttributes (self, command, args):
		""" args: [(attributeName, expression)]
				Add, leave, or remove attributes from the start tag
		"""
		attsToRemove = {}
		newAtts = []
		for attName, attExpr in args:
			resultVal = self.context.evaluate (attExpr, self.originalAttributes)
			if (resultVal is None):
				# Remove this attribute from the current attributes
				attsToRemove [attName]=1
			elif (not resultVal == simpleTALES.DEFAULTVALUE):
				# We have a value - let's use it!
				attsToRemove [attName]=1
				if (isinstance (resultVal, str)):
					escapedAttVal = resultVal
				elif (isinstance (resultVal, bytes)):
					# THIS IS NOT A BUG!
					# Use Unicode in the Context object if you are not using Ascii
					escapedAttVal = str (resultVal, 'ascii')
				else:
					# THIS IS NOT A BUG!
					# Use Unicode in the Context object if you are not using Ascii
					escapedAttVal = str (resultVal)
				newAtts.append ((attName, escapedAttVal))
		# Copy over the old attributes
		for oldAttName, oldAttValue in self.currentAttributes:
			if (not oldAttName in attsToRemove):
				newAtts.append ((oldAttName, oldAttValue))
		self.currentAttributes = newAtts
		# Evaluate all other commands
		self.programCounter += 1

	def cmdOmitTag (self, command, args):
		""" args: expression
				Conditionally turn off tag output
		"""
		result = self.context.evaluate (args, self.originalAttributes)
		if (result is not None and result):
			# Turn tag output off
			self.outputTag = 0
		self.programCounter += 1

	def cmdOutputStartTag (self, command, args):
		# Args: tagName
		tagName, singletonTag = args
		if (self.outputTag):
			if (self.tagContent is None and singletonTag):
				self.file.write (self.tagAsText ((tagName, self.currentAttributes), 1))
			else:
				self.file.write (self.tagAsText ((tagName, self.currentAttributes)))

		if (self.movePCForward is not None):
			self.programCounter = self.movePCForward
			return
		self.programCounter += 1
		return

	def cmdEndTagEndScope (self, command, args):
		# Args: tagName, omitFlag, singletonTag
		if (self.tagContent is not None):
			contentType, resultVal = self.tagContent
			if (contentType):
				if (isinstance (resultVal, Template)):
					# We have another template in the context, evaluate it!
					# Save our state!
					self.pushProgram()
					resultVal.expandInline (self.context, self.file, self)
					# Restore state
					self.popProgram()
					# End of the macro expansion (if any) so clear the parameters
					self.slotParameters = {}
				else:
					if (isinstance (resultVal, str)):
						self.file.write (resultVal)
					elif (isinstance (resultVal, bytes)):
						# THIS IS NOT A BUG!
						# Use Unicode in the Context object if you are not using Ascii
						self.file.write (str (resultVal, 'ascii'))
					else:
						# THIS IS NOT A BUG!
						# Use Unicode in the Context object if you are not using Ascii
						print('got a result: %r' % type(resultVal))
						self.file.write (str (resultVal))
			else:
				if (isinstance (resultVal, str)):
					self.file.write(html.escape(resultVal, quote=False))
				else:

					# try:
					# 	print('got a result: %r (%s)' % (type(resultVal), resultVal))
					# except TypeError as e:
					# 	print(str(e))
					self.file.write(str(resultVal))

		if (self.outputTag and not args[1]):
			# Do NOT output end tag if a singleton with no content
			if not (args[2] and self.tagContent is None):
				self.file.write ('</' + args[0] + '>')

		if (self.movePCBack is not None):
			self.programCounter = self.movePCBack
			return

		if (self.localVarsDefined):
			self.context.popLocals()

		self.movePCForward,self.movePCBack,self.outputTag,self.originalAttributes,self.currentAttributes,self.repeatVariable,self.tagContent,self.localVarsDefined = self.scopeStack.pop()
		self.programCounter += 1

	def cmdOutput (self, command, args):
		self.file.write (args)
		self.programCounter += 1

	def cmdStartScope (self, command, args):
		""" args: (originalAttributes, currentAttributes)
				Pushes the current state onto the stack, and sets up the new state
		"""
		self.scopeStack.append ((self.movePCForward
								,self.movePCBack
								,self.outputTag
								,self.originalAttributes
								,self.currentAttributes
								,self.repeatVariable
								,self.tagContent
								,self.localVarsDefined))

		self.movePCForward = None
		self.movePCBack = None
		self.outputTag = 1
		self.originalAttributes = args[0]
		self.currentAttributes = args[1]
		self.repeatVariable = None
		self.tagContent = None
		self.localVarsDefined = 0

		self.programCounter += 1

	def cmdNoOp (self, command, args):
		self.programCounter += 1

	def cmdUseMacro (self, command, args):
		""" args: (macroExpression, slotParams, endTagSymbol)
				Evaluates the expression, if it resolves to a SubTemplate it then places
				the slotParams into currentSlots and then jumps to the end tag
		"""
		value = self.context.evaluate (args[0], self.originalAttributes)
		if (value is None):
			# Don't output anything
			self.outputTag = 0
			# Output none of our content or the existing content
			self.movePCForward = self.symbolTable [args[2]]
			self.programCounter += 1
			return
		if (not value == simpleTALES.DEFAULTVALUE and isinstance (value, SubTemplate)):
			# We have a macro, so let's use it
			self.outputTag = 0
			self.slotParameters = args[1]
			self.tagContent = (1, value)
			# NOTE: WE JUMP STRAIGHT TO THE END TAG, NO OTHER TAL/METAL COMMANDS ARE EVALUATED.
			self.programCounter = self.symbolTable [args[2]]
			return
		else:
			# Default, let's just run through as normal
			self.programCounter += 1
			return

	def cmdDefineSlot (self, command, args):
		""" args: (slotName, endTagSymbol)
				If the slotName is filled then that is used, otherwise the original conent
				is used.
		"""
		if (args[0] in self.currentSlots):
			# This slot is filled, so replace us with that content
			self.outputTag = 0
			self.tagContent = (1, self.currentSlots [args[0]])
			# Output none of our content or the existing content
			# NOTE: NO FURTHER TAL/METAL COMMANDS ARE EVALUATED
			self.programCounter = self.symbolTable [args[1]]
			return
		# Slot isn't filled, so just use our own content
		self.programCounter += 1
		return


class HTMLTemplateInterpreter (TemplateInterpreter):
	def __init__ (self, minimizeBooleanAtts = 0):
		TemplateInterpreter.__init__ (self)
		self.minimizeBooleanAtts = minimizeBooleanAtts
		if (minimizeBooleanAtts):
			# Override the tagAsText method for this instance
			self.tagAsText = self.tagAsTextMinimizeAtts

	def tagAsTextMinimizeAtts (self, tagObj, singletonFlag=0):
		""" This returns a tag as text.
		"""
		tag,atts = tagObj
		result = ["<"]
		result.append (tag)
		upperTag = tag.upper()
		for attName, attValue in atts:
			if ('%s:%s' % (upperTag, attName.upper()) in HTML_BOOLEAN_ATTS):
				# We should output a minimised boolean value
				result.append (' ')
				result.append (attName)
			else:
				result.append (' ')
				result.append (attName)
				result.append ('="')
				result.append (html.escape (attValue, quote=1))
				result.append ('"')
		if (singletonFlag):
			result.append (" />")
		else:
			result.append (">")
		return "".join (result)

class Template:
	def __init__ (self, commands, macros, symbols, doctype = None):
		self.commandList = commands
		self.macros = macros
		self.symbolTable = symbols
		self.doctype = doctype
		self.log = logging.getLogger("simpleTAL.Template")

		# Setup the macros
		for macro in list(self.macros.values()):
			macro.setParentTemplate (self)

		# Setup the slots
		for cmnd, arg in self.commandList:
			if (cmnd == METAL_USE_MACRO):
				# Set the parent of each slot
				slotMap = arg[1]
				for slot in list(slotMap.values()):
					slot.setParentTemplate (self)

	def expand (self, context, outputFile, outputEncoding=None, interpreter=None):
		""" This method will write to the outputFile, using the encoding specified,
			the expanded version of this template.  The context passed in is used to resolve
			all expressions with the template.
		"""
		# This method must wrap outputFile if required by the encoding, and write out
		# any template pre-amble (DTD, Encoding, etc)
		self.expandInline (context, outputFile, interpreter)

	def expandInline (self, context, outputFile, interpreter=None):
		""" Internally used when expanding a template that is part of a context."""
		if (interpreter is None):
			ourInterpreter = TemplateInterpreter()
			ourInterpreter.initialise (context, outputFile)
		else:
			ourInterpreter = interpreter
		try:
			ourInterpreter.execute (self)
		except UnicodeError as unierror:
			self.log.error ("UnicodeError caused by placing a non-Unicode string in the Context object.")
			raise simpleTALES.ContextContentException ("Found non-unicode string in Context!")

	def getProgram (self):
		""" Returns a tuple of (commandList, startPoint, endPoint, symbolTable) """
		return (self.commandList, 0, len (self.commandList), self.symbolTable)

	def __str__ (self):
		result = "Commands:\n"
		index = 0
		for cmd in self.commandList:
			if (cmd[0] != METAL_USE_MACRO):
				result = result + "\n[%s] %s" % (str (index), str (cmd))
			else:
				result = result + "\n[%s] %s, (%s{" % (str (index), str (cmd[0]), str (cmd[1][0]))
				for slot in list(cmd[1][1].keys()):
					result = result + "%s: %s" % (slot, str (cmd[1][1][slot]))
				result = result + "}, %s)" % str (cmd[1][2])
			index += 1
		result = result + "\n\nSymbols:\n"
		for symbol in list(self.symbolTable.keys()):
			result = result + "Symbol: " + str (symbol) + " points to: " + str (self.symbolTable[symbol]) + ", which is command: " + str (self.commandList[self.symbolTable[symbol]]) + "\n"

		result = result + "\n\nMacros:\n"
		for macro in list(self.macros.keys()):
			result = result + "Macro: " + str (macro) + " value of: " + str (self.macros[macro])
		return result

class SubTemplate (Template):
	""" A SubTemplate is part of another template, and is used for the METAL implementation.
			The two uses for this class are:
				1 - metal:define-macro results in a SubTemplate that is the macro
				2 - metal:fill-slot results in a SubTemplate that is a parameter to metal:use-macro
	"""
	def __init__ (self, startRange, endRangeSymbol):
		""" The parentTemplate is the template for which we are a sub-template.
				The startRange and endRange are indexes into the parent templates command list,
				and defines the range of commands that we can execute
		"""
		Template.__init__ (self, [], {}, {})
		self.startRange = startRange
		self.endRangeSymbol = endRangeSymbol

	def setParentTemplate (self, parentTemplate):
		self.parentTemplate = parentTemplate
		self.commandList = parentTemplate.commandList
		self.symbolTable = parentTemplate.symbolTable

	def getProgram (self):
		""" Returns a tuple of (commandList, startPoint, endPoint, symbolTable) """
		return (self.commandList, self.startRange, self.symbolTable[self.endRangeSymbol]+1, self.symbolTable)

	def __str__ (self):
		endRange = self.symbolTable [self.endRangeSymbol]
		result = "SubTemplate from %s to %s\n" % (str (self.startRange), str (endRange))
		return result

class HTMLTemplate (Template):
	"""A specialised form of a template that knows how to output HTML
	"""
	def __init__ (self, commands, macros, symbols, doctype = None, minimizeBooleanAtts = 0):
		self.minimizeBooleanAtts = minimizeBooleanAtts
		Template.__init__ (self, commands, macros, symbols, doctype = None)

	def expand (self, context, outputFile, outputEncoding = "utf-8", interpreter=None):
		""" This method will write to the outputFile the expanded version of this template.
			The context passed in is used to resolve all expressions with the template.
		"""
		if isinstance(outputFile, (io.TextIOBase, codecs.StreamWriter)):
			self.log.debug ("Text based output file detected")
		else:
			self.log.debug ("Bytes based output file detected - wrapping in codec for %s", outputEncoding)
			outputFile = codecs.lookup (outputEncoding).streamwriter (outputFile, 'xmlcharrefreplace')
		self.expandInline (context, outputFile, interpreter)

	def expandInline (self, context, outputFile, interpreter=None):
		""" Ensure we use the HTMLTemplateInterpreter"""
		if (interpreter is None):
			ourInterpreter = HTMLTemplateInterpreter(minimizeBooleanAtts = self.minimizeBooleanAtts)
			ourInterpreter.initialise (context, outputFile)
		else:
			ourInterpreter = interpreter
		Template.expandInline (self, context, outputFile, ourInterpreter)

class XMLTemplate (Template):
	"""A specialised form of a template that knows how to output XML
	"""

	def __init__ (self, commands, macros, symbols, doctype = None):
		Template.__init__ (self, commands, macros, symbols)
		self.doctype = doctype

	def expand (self, context, outputFile, outputEncoding = "utf-8", docType=None, suppressXMLDeclaration=False,interpreter=None):
		""" This method will write to the outputFile, using the encoding attached to the outputFile,
			the expanded version of this template.  The context passed in is used to resolve
			all expressions with the template.
		"""
		if isinstance(outputFile, (io.TextIOBase, codecs.StreamWriter)):
			self.log.debug ("Text based output file detected")
		else:
			self.log.debug ("Bytes based output file detected - wrapping in codec for %s", outputEncoding)
			outputFile = codecs.lookup (outputEncoding).streamwriter (outputFile, 'xmlcharrefreplace')

		if (not suppressXMLDeclaration):
			if (outputEncoding.lower() != "utf-8"):
				outputFile.write ('<?xml version="1.0" encoding="%s"?>\n' % outputEncoding.lower())
			else:
				outputFile.write ('<?xml version="1.0"?>\n')
		if not docType and self.doctype:
			docType = self.doctype
		if docType:
			outputFile.write (docType)
			outputFile.write ('\n')
		self.expandInline (context, outputFile, interpreter)

class TemplateCompiler:
	def __init__ (self):
		""" Initialise a template compiler.
		"""
		self.commandList = []
		self.tagStack = []
		self.symbolLocationTable = {}
		self.macroMap = {}
		self.endTagSymbol = 1

		self.commandHandler  = {}
		self.commandHandler [TAL_DEFINE] = self.compileCmdDefine
		self.commandHandler [TAL_CONDITION] = self.compileCmdCondition
		self.commandHandler [TAL_REPEAT] = self.compileCmdRepeat
		self.commandHandler [TAL_CONTENT] = self.compileCmdContent
		self.commandHandler [TAL_REPLACE] = self.compileCmdReplace
		self.commandHandler [TAL_ATTRIBUTES] = self.compileCmdAttributes
		self.commandHandler [TAL_OMITTAG] = self.compileCmdOmitTag

		# Metal commands
		self.commandHandler [METAL_USE_MACRO] = self.compileMetalUseMacro
		self.commandHandler [METAL_DEFINE_SLOT] = self.compileMetalDefineSlot
		self.commandHandler [METAL_FILL_SLOT] = self.compileMetalFillSlot
		self.commandHandler [METAL_DEFINE_MACRO] = self.compileMetalDefineMacro

		# Default namespaces
		self.setTALPrefix ('tal')
		self.tal_namespace_prefix_stack = []
		self.metal_namespace_prefix_stack = []
		self.tal_namespace_prefix_stack.append ('tal')
		self.setMETALPrefix ('metal')
		self.metal_namespace_prefix_stack.append ('metal')

		self.log = logging.getLogger ("simpleTAL.TemplateCompiler")

	def setTALPrefix (self, prefix):
		self.tal_namespace_prefix = prefix
		self.tal_namespace_omittag = '%s:omit-tag' % self.tal_namespace_prefix
		self.tal_attribute_map = {}
		self.tal_attribute_map ['%s:attributes'%prefix] = TAL_ATTRIBUTES
		self.tal_attribute_map ['%s:content'%prefix]= TAL_CONTENT
		self.tal_attribute_map ['%s:define'%prefix] = TAL_DEFINE
		self.tal_attribute_map ['%s:replace'%prefix] = TAL_REPLACE
		self.tal_attribute_map ['%s:omit-tag'%prefix] = TAL_OMITTAG
		self.tal_attribute_map ['%s:condition'%prefix] = TAL_CONDITION
		self.tal_attribute_map ['%s:repeat'%prefix] = TAL_REPEAT

	def setMETALPrefix (self, prefix):
		self.metal_namespace_prefix = prefix
		self.metal_attribute_map = {}
		self.metal_attribute_map ['%s:define-macro'%prefix] = METAL_DEFINE_MACRO
		self.metal_attribute_map ['%s:use-macro'%prefix] = METAL_USE_MACRO
		self.metal_attribute_map ['%s:define-slot'%prefix] = METAL_DEFINE_SLOT
		self.metal_attribute_map ['%s:fill-slot'%prefix] = METAL_FILL_SLOT

	def popTALNamespace (self):
		newPrefix = self.tal_namespace_prefix_stack.pop()
		self.setTALPrefix (newPrefix)

	def popMETALNamespace (self):
		newPrefix = self.metal_namespace_prefix_stack.pop()
		self.setMETALPrefix (newPrefix)

	def tagAsText (self, tagObj, singletonFlag=0):
		""" This returns a tag as text.
		"""
		tag,atts = tagObj
		result = ["<"]
		result.append (tag)
		for attName, attValue in atts:
			result.append (' ')
			result.append (attName)
			result.append ('="')
			result.append (html.escape (attValue, quote=1))
			result.append ('"')
		if (singletonFlag):
			result.append (" />")
		else:
			result.append (">")
		return "".join (result)

	def getTemplate (self):
		template = Template (self.commandList, self.macroMap, self.symbolLocationTable)
		return template

	def addCommand (self, command):
		if command[0] == TAL_OUTPUT and self.commandList and self.commandList[-1][0] == TAL_OUTPUT:
			# We can combine output commands
			self.commandList[-1] = (TAL_OUTPUT, self.commandList[-1][1] + command[1])
		else:
			self.commandList.append (command)

	def addTag (self, tag, tagProperties=None):
		""" Used to add a tag to the stack.  Various properties can be passed in the dictionary
		    as being information required by the tag.
		    Currently supported properties are:
		    		'command'         - The (command,args) tuple associated with this command
		    		'originalAtts'    - The original attributes that include any metal/tal attributes
		    		'endTagSymbol'    - The symbol associated with the end tag for this element
		    		'popFunctionList' - A list of functions to execute when this tag is popped
					'singletonTag'    - A boolean to indicate that this is a singleton flag
		"""
		# Add the tag to the tagStack (list of tuples (tag, properties, useMacroLocation))
		tagProperties = tagProperties or {}
		self.log.debug ("Adding tag %s to stack" % tag[0])
		command = tagProperties.get ('command',None)
		originalAtts = tagProperties.get ('originalAtts', None)
		singletonTag = tagProperties.get ('singletonTag', 0)
		if (command is not None):
			if (command[0] == METAL_USE_MACRO):
				self.tagStack.append ((tag, tagProperties, len (self.commandList)+1))
			else:
				self.tagStack.append ((tag, tagProperties, None))
		else:
			self.tagStack.append ((tag, tagProperties, None))
		if (command is not None):
			# All tags that have a TAL attribute on them start with a 'start scope'
			self.addCommand((TAL_START_SCOPE, (originalAtts, tag[1])))
			# Now we add the TAL command
			self.addCommand(command)
		else:
			# It's just a straight output, so create an output command and append it
			self.addCommand((TAL_OUTPUT, self.tagAsText (tag, singletonTag)))

	def popTag (self, tag, omitTagFlag=0):
		""" omitTagFlag is used to control whether the end tag should be included in the
				output or not.  In HTML 4.01 there are several tags which should never have
				end tags, this flag allows the template compiler to specify that these
				should not be output.
		"""
		while self.tagStack:
			oldTag, tagProperties, useMacroLocation = self.tagStack.pop()
			endTagSymbol = tagProperties.get ('endTagSymbol', None)
			popCommandList = tagProperties.get ('popFunctionList', [])
			singletonTag = tagProperties.get ('singletonTag', 0)
			for func in popCommandList:
				func()
			self.log.debug ("Popped tag %s off stack" % oldTag[0])
			if (oldTag[0] == tag[0]):
				# We've found the right tag, now check to see if we have any TAL commands on it
				if (endTagSymbol is not None):
					# We have a command (it's a TAL tag)
					# Note where the end tag symbol should point (i.e. the next command)
					self.symbolLocationTable [endTagSymbol] = len (self.commandList)

					# We need a "close scope and tag" command
					self.addCommand((TAL_ENDTAG_ENDSCOPE, (tag[0], omitTagFlag, singletonTag)))
					return
				elif (omitTagFlag == 0 and singletonTag == 0):
					# We are popping off an un-interesting tag, just add the close as text
					self.addCommand((TAL_OUTPUT, '</' + tag[0] + '>'))
					return
				else:
					# We are suppressing the output of this tag, so just return
					return
			else:
				# We have a different tag, which means something like <br> which never closes is in
				# between us and the real tag.

				# If the tag that we did pop off has a command though it means un-balanced TAL tags!
				if (endTagSymbol is not None):
					# ERROR
					msg = "TAL/METAL Elements must be balanced - found close tag %s expecting %s" % (tag[0], oldTag[0])
					self.log.error (msg)
					raise TemplateParseException (self.tagAsText(oldTag), msg)
		self.log.error ("Close tag %s found with no corresponding open tag." % tag[0])
		raise TemplateParseException ("</%s>" % tag[0], "Close tag encountered with no corresponding open tag.")

	def parseStartTag (self, tag, attributes, singletonElement=0):
		# Note down the tag we are handling, it will be used for error handling during
		# compilation
		self.currentStartTag = (tag, attributes)

		# Look for tal/metal attributes
		foundTALAtts = []
		foundMETALAtts = []
		foundCommandsArgs = {}
		cleanAttributes = []
		originalAttributes = {}
		tagProperties = {}
		popTagFuncList = []
		TALElementNameSpace = 0
		prefixToAdd = ""
		tagProperties ['singletonTag'] = singletonElement

		# Determine whether this element is in either the METAL or TAL namespace
		if (tag.find (':') > 0):
			# We have a namespace involved, so let's look to see if its one of ours
			namespace = tag[0:tag.find (':')]
			if (namespace == self.metal_namespace_prefix):
				TALElementNameSpace = 1
				prefixToAdd = self.metal_namespace_prefix +":"
			elif (namespace == self.tal_namespace_prefix):
				TALElementNameSpace = 1
				prefixToAdd = self.tal_namespace_prefix +":"

			if (TALElementNameSpace):
				# We should treat this an implicit omit-tag
				foundTALAtts.append (TAL_OMITTAG)
				# Will go to default, i.e. yes
				foundCommandsArgs [TAL_OMITTAG] = ""

		for att, value in attributes:
			originalAttributes [att] = value
			if (TALElementNameSpace and not att.find (':') > 0):
				# This means that the attribute name does not have a namespace, so use the prefix for this tag.
				commandAttName = prefixToAdd + att
			else:
				commandAttName = att
			self.log.debug ("Command name is now %s" % commandAttName)
			if (att[0:5] == "xmlns"):
				# We have a namespace declaration.
				prefix = att[6:]
				if (value == METAL_NAME_URI):
					# It's a METAL namespace declaration
					if prefix:
						self.metal_namespace_prefix_stack.append (self.metal_namespace_prefix)
						self.setMETALPrefix (prefix)
						# We want this function called when the scope ends
						popTagFuncList.append (self.popMETALNamespace)
					else:
						# We don't allow METAL/TAL to be declared as a default
						msg = "Can not use METAL name space by default, a prefix must be provided."
						raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
				elif (value == TAL_NAME_URI):
					# TAL this time
					if prefix:
						self.tal_namespace_prefix_stack.append (self.tal_namespace_prefix)
						self.setTALPrefix (prefix)
						# We want this function called when the scope ends
						popTagFuncList.append (self.popTALNamespace)
					else:
						# We don't allow METAL/TAL to be declared as a default
						msg = "Can not use TAL name space by default, a prefix must be provided."
						raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
				else:
					# It's nothing special, just an ordinary namespace declaration
					cleanAttributes.append ((att, value))
			elif (commandAttName in self.tal_attribute_map):
				# It's a TAL attribute
				cmnd = self.tal_attribute_map [commandAttName]
				if (cmnd == TAL_OMITTAG and TALElementNameSpace):
					self.log.warning ("Supressing omit-tag command present on TAL or METAL element")
				else:
					foundCommandsArgs [cmnd] = value
					foundTALAtts.append (cmnd)
			elif (commandAttName in self.metal_attribute_map):
				# It's a METAL attribute
				cmnd = self.metal_attribute_map [commandAttName]
				foundCommandsArgs [cmnd] = value
				foundMETALAtts.append (cmnd)
			else:
				cleanAttributes.append ((att, value))
		tagProperties ['popFunctionList'] = popTagFuncList

		# This might be just content
		if ((len (foundTALAtts) + len (foundMETALAtts)) == 0):
			# Just content, add it to the various stacks
			self.addTag ((tag, cleanAttributes), tagProperties)
			return

		# Create a symbol for the end of the tag - we don't know what the offset is yet
		self.endTagSymbol += 1
		tagProperties ['endTagSymbol'] = self.endTagSymbol

		# Sort the METAL commands
		foundMETALAtts.sort()
		# Sort the tags by priority
		foundTALAtts.sort()

		# We handle the METAL before the TAL
		allCommands = foundMETALAtts + foundTALAtts
		firstTag = 1
		for talAtt in allCommands:
			# Parse and create a command for each
			cmnd = self.commandHandler [talAtt](foundCommandsArgs[talAtt])
			if (cmnd is not None):
				if (firstTag):
					# The first one needs to add the tag
					firstTag = 0
					tagProperties ['originalAtts'] = originalAttributes
					tagProperties ['command'] = cmnd
					self.addTag ((tag, cleanAttributes), tagProperties)
				else:
					# All others just append
					self.addCommand(cmnd)

		if (firstTag):
			tagProperties ['originalAtts'] = originalAttributes
			tagProperties ['command'] = (TAL_STARTTAG, (tag, singletonElement))
			self.addTag ((tag, cleanAttributes), tagProperties)
		else:
			# Add the start tag command in as a child of the last TAL command
			self.addCommand((TAL_STARTTAG, (tag,singletonElement)))

	def parseEndTag (self, tag):
		""" Just pop the tag and related commands off the stack. """
		self.popTag ((tag,None))

	def parseData (self, data):
		# Just add it as an output
		self.addCommand((TAL_OUTPUT, data))

	def compileCmdDefine (self, argument):
		# Compile a define command, resulting argument is:
		# [(isLocalFlag (Y/n), variableName, variablePath),...]
		# Break up the list of defines first
		commandArgs = []
		# We only want to match semi-colons that are not escaped
		argumentSplitter =  re.compile ('(?<!;);(?!;)')
		for defineStmt in argumentSplitter.split (argument):
			#  remove any leading space and un-escape any semi-colons
			defineStmt = defineStmt.lstrip().replace (';;', ';')
			# Break each defineStmt into pieces "[local|global] varName expression"
			stmtBits = defineStmt.split (' ')
			isLocal = 1
			if (len (stmtBits) < 2):
				# Error, badly formed define command
				msg = "Badly formed define command '%s'.  Define commands must be of the form: '[local|global] varName expression[;[local|global] varName expression]'" % argument
				self.log.error (msg)
				raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
			# Assume to start with that >2 elements means a local|global flag
			if (len (stmtBits) > 2):
				if (stmtBits[0] == 'global'):
					isLocal = 0
					varName = stmtBits[1]
					expression = ' '.join (stmtBits[2:])
				elif (stmtBits[0] == 'local'):
					varName = stmtBits[1]
					expression = ' '.join (stmtBits[2:])
				else:
					# Must be a space in the expression that caused the >3 thing
					varName = stmtBits[0]
					expression = ' '.join (stmtBits[1:])
			else:
				# Only two bits
				varName = stmtBits[0]
				expression = ' '.join (stmtBits[1:])

			commandArgs.append ((isLocal, varName, expression))
		return (TAL_DEFINE, commandArgs)

	def compileCmdCondition (self, argument):
		# Compile a condition command, resulting argument is:
		# path, endTagSymbol
		# Sanity check
		if not argument:
			# No argument passed
			msg = "No argument passed!  condition commands must be of the form: 'path'"
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		return (TAL_CONDITION, (argument, self.endTagSymbol))

	def compileCmdRepeat (self, argument):
		# Compile a repeat command, resulting argument is:
		# (varname, expression, endTagSymbol)
		attProps = argument.split (' ')
		if (len (attProps) < 2):
			# Error, badly formed repeat command
			msg = "Badly formed repeat command '%s'.  Repeat commands must be of the form: 'localVariable path'" % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		varName = attProps [0]
		expression = " ".join (attProps[1:])
		return (TAL_REPEAT, (varName, expression, self.endTagSymbol))

	def compileCmdContent (self, argument, replaceFlag=0):
		# Compile a content command, resulting argument is
		# (replaceFlag, structureFlag, expression, endTagSymbol)

		# Sanity check
		if not argument:
			# No argument passed
			msg = "No argument passed!  content/replace commands must be of the form: 'path'"
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		structureFlag = 0
		attProps = argument.split (' ')
		if attProps:
			if (attProps[0] == "structure"):
				structureFlag = 1
				express = " ".join (attProps[1:])
			elif (attProps[0] == "text"):
				structureFlag = 0
				express = " ".join (attProps[1:])
			else:
				# It's not a type selection after all - assume it's part of the path
				express = argument
		else:
			express = argument
		return (TAL_CONTENT, (replaceFlag, structureFlag, express, self.endTagSymbol))

	def compileCmdReplace (self, argument):
		return self.compileCmdContent (argument, replaceFlag=1)

	def compileCmdAttributes (self, argument):
		# Compile tal:attributes into attribute command
		# Argument: [(attributeName, expression)]

		# Break up the list of attribute settings first
		commandArgs = []
		# We only want to match semi-colons that are not escaped
		argumentSplitter =  re.compile ('(?<!;);(?!;)')
		for attributeStmt in argumentSplitter.split (argument):
			#  remove any leading space and un-escape any semi-colons
			attributeStmt = attributeStmt.lstrip().replace (';;', ';')
			# Break each attributeStmt into name and expression
			stmtBits = attributeStmt.split (' ')
			if (len (stmtBits) < 2):
				# Error, badly formed attributes command
				msg = "Badly formed attributes command '%s'.  Attributes commands must be of the form: 'name expression[;name expression]'" % argument
				self.log.error (msg)
				raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
			attName = stmtBits[0]
			attExpr = " ".join (stmtBits[1:])
			commandArgs.append ((attName, attExpr))
		return (TAL_ATTRIBUTES, commandArgs)

	def compileCmdOmitTag (self, argument):
		# Compile a condition command, resulting argument is:
		# path
		# If no argument is given then set the path to default
		if not argument:
			expression = "default"
		else:
			expression = argument
		return (TAL_OMITTAG, expression)

	# METAL compilation commands go here
	def compileMetalUseMacro (self, argument):
		# Sanity check
		if not argument:
			# No argument passed
			msg = "No argument passed!  use-macro commands must be of the form: 'use-macro: path'"
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
		cmnd = (METAL_USE_MACRO, (argument, {}, self.endTagSymbol))
		self.log.debug ("Returning METAL_USE_MACRO: %s" % str (cmnd))
		return cmnd

	def compileMetalDefineMacro (self, argument):
		if not argument:
			# No argument passed
			msg = "No argument passed!  define-macro commands must be of the form: 'define-macro: name'"
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		# Check that the name of the macro is valid
		if (METAL_NAME_REGEX.match (argument).end() != len (argument)):
			msg = "Macro name %s is invalid." % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
		if (argument in self.macroMap):
			msg = "Macro name %s is already defined!" % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		# The macro starts at the next command.
		macro = SubTemplate (len (self.commandList), self.endTagSymbol)
		self.macroMap [argument] = macro
		return None

	def compileMetalFillSlot (self, argument):
		if not argument:
			# No argument passed
			msg = "No argument passed!  fill-slot commands must be of the form: 'fill-slot: name'"
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		# Check that the name of the macro is valid
		if (METAL_NAME_REGEX.match (argument).end() != len (argument)):
			msg = "Slot name %s is invalid." % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		# Determine what use-macro statement this belongs to by working through the list backwards
		ourMacroLocation = None
		location = len (self.tagStack) - 1
		while (ourMacroLocation is None):
			macroLocation = self.tagStack[location][2]
			if (macroLocation is not None):
				ourMacroLocation = macroLocation
			else:
				location -= 1
				if (location < 0):
					msg = "metal:fill-slot must be used inside a metal:use-macro call"
					self.log.error (msg)
					raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		# Get the use-macro command we are going to adjust
		cmnd, args = self.commandList [ourMacroLocation]
		self.log.debug ("Use macro argument: %s" % str (args))
		macroName, slotMap, endSymbol = args

		# Check that the name of the slot is valid
		if (METAL_NAME_REGEX.match (argument).end() != len (argument)):
			msg = "Slot name %s is invalid." % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		if (argument in slotMap):
			msg = "Slot %s has already been filled!" % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		# The slot starts at the next command.
		slot = SubTemplate (len (self.commandList), self.endTagSymbol)
		slotMap [argument] = slot

		# Update the command
		self.commandList [ourMacroLocation] = (cmnd, (macroName, slotMap, endSymbol))
		return None

	def compileMetalDefineSlot (self, argument):
		if not argument:
			# No argument passed
			msg = "No argument passed!  define-slot commands must be of the form: 'name'"
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)
		# Check that the name of the slot is valid
		if (METAL_NAME_REGEX.match (argument).end() != len (argument)):
			msg = "Slot name %s is invalid." % argument
			self.log.error (msg)
			raise TemplateParseException (self.tagAsText (self.currentStartTag), msg)

		return (METAL_DEFINE_SLOT, (argument, self.endTagSymbol))

class TemplateParseException (Exception):
	def __init__ (self, location, errorDescription):
		self.location = location
		self.errorDescription = errorDescription

	def __str__ (self):
		return "[" + self.location + "] " + self.errorDescription


class HTMLTemplateCompiler (TemplateCompiler, FixedHTMLParser.HTMLParser):
	def __init__ (self):
		TemplateCompiler.__init__ (self)
		FixedHTMLParser.HTMLParser.__init__ (self)
		self.log = logging.getLogger ("simpleTAL.HTMLTemplateCompiler")

	def parseTemplate (self, file, minimizeBooleanAtts = False):
		self.minimizeBooleanAtts = minimizeBooleanAtts
		self.feed (file.read())
		self.close()

	def tagAsText (self, tagObj, singletonFlag=0):
		""" This returns a tag as text.
		"""
		tag,atts = tagObj
		result = ["<"]
		result.append (tag)
		upperTag = tag.upper()
		for attName, attValue in atts:
			if (self.minimizeBooleanAtts and '%s:%s' % (upperTag, attName.upper()) in HTML_BOOLEAN_ATTS):
				# We should output a minimised boolean value
				result.append (' ')
				result.append (attName)
			else:
				result.append (' ')
				result.append (attName)
				result.append ('="')
				result.append (html.escape (attValue, quote=1))
				result.append ('"')
		if (singletonFlag):
			result.append (" />")
		else:
			result.append (">")
		return "".join (result)

	def handle_startendtag (self, tag, attributes):
		self.handle_starttag (tag, attributes)
		if not (tag.upper() in HTML_FORBIDDEN_ENDTAG):
			self.handle_endtag(tag)

	def handle_starttag (self, tag, attributes):
		self.log.debug ("Received Start Tag: " + tag + " Attributes: " + str (attributes))
		atts = []
		for att, attValue in attributes:
			# We need to spot empty tal:omit-tags
			if (attValue is None):
				if (att == self.tal_namespace_omittag):
					atts.append ((att, ""))
				else:
					atts.append ((att, att))
			elif not HTML_ENTITIES_PRE_EXPANDED:
				# Expand any SGML entity references or char references
				goodAttValue = []
				last = 0
				match = ENTITY_REF_REGEX.search (attValue)
				while (match):
					goodAttValue.append (attValue[last:match.start()])
					ref = attValue[match.start():match.end()]
					if (ref.startswith ('&#')):
						# A char reference
						if (ref[2] in ['x', 'X']):
							# Hex
							refValue = int (ref[3:-1], 16)
						else:
							refValue = int (ref[2:-1])
						goodAttValue.append (chr (refValue))
					else:
						# A named reference.
						goodAttValue.append (chr (sgmlentitynames.htmlNameToUnicodeNumber.get (ref[1:-1], 65533)))
					last = match.end()
					match = ENTITY_REF_REGEX.search (attValue, last)
				goodAttValue.append (attValue [last:])
				atts.append ((att, "".join (goodAttValue)))
			else:
				atts.append ((att, attValue))

		if (tag.upper() in HTML_FORBIDDEN_ENDTAG):
			# This should have no end tag, so we just do the start and suppress the end
			self.parseStartTag (tag, atts)
			self.log.debug ("End tag forbidden, generating close tag with no output.")
			self.popTag ((tag, None), omitTagFlag=1)
		else:
			self.parseStartTag (tag, atts)

	def handle_endtag (self, tag):
		self.log.debug ("Recieved End Tag: " + tag)
		if (tag.upper() in HTML_FORBIDDEN_ENDTAG):
			self.log.warning ("HTML 4.01 forbids end tags for the %s element" % tag)
		else:
			# Normal end tag
			self.popTag ((tag, None))

	def handle_data (self, data):
		self.parseData (html.escape (data, quote=False))

	# These two methods are required so that we expand all character and entity references prior to parsing the template.
	def handle_charref (self, ref):
		self.log.debug ("Got Ref: %s", ref)
		self.parseData (chr (int (ref)))

	def handle_entityref (self, ref):
		self.log.debug ("Got Ref: %s", ref)
		# Use handle_data so that <&> are re-encoded as required.
		self.handle_data( chr (sgmlentitynames.htmlNameToUnicodeNumber.get (ref, 65533)))

	# Handle document type declarations
	def handle_decl (self, data):
		self.parseData ('<!%s>' % data)

	# Pass comments through un-affected.
	def handle_comment (self, data):
		self.parseData ('<!--%s-->' % data)

	def handle_pi (self, data):
		self.log.debug ("Recieved processing instruction.")
		self.parseData ('<?%s>' % data)

	def report_unbalanced (self, tag):
		self.log.warning ("End tag %s present with no corresponding open tag.")

	def getTemplate (self):
		template = HTMLTemplate (self.commandList, self.macroMap, self.symbolLocationTable, minimizeBooleanAtts = self.minimizeBooleanAtts)
		return template

class XMLTemplateCompiler (TemplateCompiler, xml.sax.handler.ContentHandler, xml.sax.handler.DTDHandler, LexicalHandler):
	def __init__ (self):
		TemplateCompiler.__init__ (self)
		xml.sax.handler.ContentHandler.__init__ (self)
		self.doctype = None
		self.log = logging.getLogger ("simpleTAL.XMLTemplateCompiler")
		self.singletonElement = 0

	def parseTemplate (self, templateFile):
		self.ourParser = xml.sax.make_parser()
		self.log.debug ("Setting features of parser")
		try:
			self.ourParser.setFeature (xml.sax.handler.feature_external_ges, False)
			self.log.debug ("Set SAX Handler feature OK")
		except:
			pass
		if use_lexical_handler:
			self.ourParser.setProperty(xml.sax.handler.property_lexical_handler, self)

		self.ourParser.setContentHandler (self)
		self.ourParser.setDTDHandler (self)

		self.ourParser.parse (templateFile)

	def startDTD(self, name, public_id, system_id):
		self.log.debug ("Recieved DOCTYPE: " + name + " public_id: " + public_id + " system_id: " + system_id)
		if public_id:
			self.doctype = '<!DOCTYPE %s PUBLIC "%s" "%s">' % (name, public_id, system_id,)
		else:
			self.doctype = '<!DOCTYPE %s SYSTEM "%s">' % (name, system_id,)

	def startElement (self, tag, attributes):
		self.log.debug ("Recieved Real Start Tag: " + tag + " Attributes: " + str (attributes))
		try:
			xmlText = self.ourParser.getProperty (xml.sax.handler.property_xml_string)
			if (isinstance (xmlText, str)):
				# Once issue 6686 is solved this should allow singletons to be detected
				if (SINGLETON_XML_REGEX.match (xmlText)):
					# This is a singleton!
					self.singletonElement=1
			else:
				if (SINGLETON_BYTES_XML_REGEX.match (xmlText)):
					# This is a singleton!
					self.singletonElement = 1
		except xml.sax.SAXException as e:
			# Parser doesn't support this property
			pass
		# Convert attributes into a list of tuples
		atts = []
		for att in attributes.getNames():
			self.log.debug ("Attribute name %s has value %s" % (att, attributes[att]))
			atts.append ((att, attributes [att]))
		self.parseStartTag (tag, atts, singletonElement=self.singletonElement)

	def endElement (self, tag):
		self.log.debug ("Recieved Real End Tag: " + tag)
		self.parseEndTag (tag)
		self.singletonElement = 0

	def skippedEntity (self, name):
		self.log.info ("Recieved skipped entity: %s" % name)
		self.characters( chr (sgmlentitynames.htmlNameToUnicodeNumber.get (name, 65533)))

	def characters (self, data):
		#self.log.debug ("Recieved Real Data: " + data)
		# Escape any data we recieve - we don't want any: <&> in there.
		self.parseData (html.escape (data, quote=False))

	def processingInstruction (self, target, data):
		self.log.debug ("Recieved processing instruction.")
		self.parseData ('<?%s %s?>' % (target, data))

	def comment (self, data):
		# This is only called if your XML parser supports the LexicalHandler interface.
		self.parseData ('<!--%s-->' % data)

	def getTemplate (self):
		template = XMLTemplate (self.commandList, self.macroMap, self.symbolLocationTable, self.doctype)
		return template

def compileHTMLTemplate (template, minimizeBooleanAtts = 0):
	""" Reads the templateFile and produces a compiled template.
		To use the resulting template object call:
			template.expand (context, outputFile)
	"""
	if (isinstance (template, str)):
		# It's a string!
		templateFile = io.StringIO (template)
	else:
		templateFile = template
	compiler = HTMLTemplateCompiler()
	compiler.parseTemplate (templateFile, minimizeBooleanAtts)
	return compiler.getTemplate()

def compileXMLTemplate (template):
	""" Reads the templateFile and produces a compiled template.
		To use the resulting template object call:
			template.expand (context, outputFile)
	"""
	if (isinstance (template, str)):
		# It's a string!
		templateFile = io.StringIO (template)
	elif (isinstance (template, bytes)):
		templateFile = io.BytesIO (template)
	else:
		templateFile = template
	compiler = XMLTemplateCompiler()
	compiler.parseTemplate (templateFile)
	return compiler.getTemplate()
