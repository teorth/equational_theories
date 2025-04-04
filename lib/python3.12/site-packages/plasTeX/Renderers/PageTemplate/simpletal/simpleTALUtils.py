""" simpleTALUtils

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

		This module is holds utilities that make using SimpleTAL easier.
		Initially this is just the HTMLStructureCleaner class, used to clean
		up HTML that can then be used as 'structure' content.

		Module Dependencies: None
"""

import io, os, stat, threading, codecs, cgi, re
from . import __version__, simpleTAL

# This is used to check for already escaped attributes.
ESCAPED_TEXT_REGEX=re.compile (r"\&\S+?;")

class TemplateCache:
	""" A TemplateCache is a multi-thread safe object that caches compiled templates.
		This cache only works with file based templates, the ctime of the file is
		checked on each hit, if the file has changed the template is re-compiled.
	"""
	def __init__ (self):
		self.templateCache = {}
		self.cacheLock = threading.Lock()
		self.hits = 0
		self.misses = 0

	def getTemplate (self, name, inputEncoding='utf-8'):
		""" Name should be the path of a template file.  If the path ends in 'xml' it is treated
			as an XML Template, otherwise it's treated as an HTML Template.  If the template file
			has changed since the last cache it will be re-compiled.

			inputEncoding is only used for HTML templates, and should be the encoding that the template
			is stored in.
		"""
		if (name in self.templateCache):
			template, oldctime = self.templateCache [name]
			ctime = os.stat (name)[stat.ST_MTIME]
			if (oldctime == ctime):
				# Cache hit!
				self.hits += 1
				return template
		# Cache miss, let's cache this template
		return self._cacheTemplate_ (name, inputEncoding)

	def getXMLTemplate (self, name):
		""" Name should be the path of an XML template file.
		"""
		if (name in self.templateCache):
			template, oldctime = self.templateCache [name]
			ctime = os.stat (name)[stat.ST_MTIME]
			if (oldctime == ctime):
				# Cache hit!
				self.hits += 1
				return template
		# Cache miss, let's cache this template
		return self._cacheTemplate_ (name, None, xmlTemplate=1)

	def _cacheTemplate_ (self, name, inputEncoding, xmlTemplate=0):
		self.cacheLock.acquire ()
		try:
			tempFile = open (name, 'r')
			if (xmlTemplate):
				# We know it is XML
				template = simpleTAL.compileXMLTemplate (tempFile)
			else:
				# We have to guess...
				firstline = tempFile.readline()
				tempFile.seek(0)
				if (name [-3:] == "xml") or (firstline.strip ()[:5] == b'<?xml') or (firstline [:9] == b'<!DOCTYPE' and firstline.find(b'XHTML') != -1):
					template = simpleTAL.compileXMLTemplate (tempFile)
				else:
					template = simpleTAL.compileHTMLTemplate (codecs.lookup (inputEncoding).streamreader(tempFile))
			tempFile.close()
			self.templateCache [name] = (template, os.stat (name)[stat.ST_MTIME])
			self.misses += 1
		except Exception as e:
			self.cacheLock.release()
			raise e

		self.cacheLock.release()
		return template

def tagAsText (tag,atts):
	result = "<" + tag
	for name,value in atts:
		if (ESCAPED_TEXT_REGEX.search (value) is not None):
			# We already have some escaped characters in here, so assume it's all valid
			result += ' %s="%s"' % (name, value)
		else:
			result += ' %s="%s"' % (name, cgi.escape (value))
	result += ">"
	return result

class MacroExpansionInterpreter (simpleTAL.TemplateInterpreter):
	def __init__ (self):
		simpleTAL.TemplateInterpreter.__init__ (self)
		# Override the standard interpreter way of doing things.
		self.macroStateStack = []
		self.commandHandler [simpleTAL.TAL_DEFINE] = self.cmdNoOp
		self.commandHandler [simpleTAL.TAL_CONDITION] = self.cmdNoOp
		self.commandHandler [simpleTAL.TAL_REPEAT] = self.cmdNoOp
		self.commandHandler [simpleTAL.TAL_CONTENT] = self.cmdNoOp
		self.commandHandler [simpleTAL.TAL_ATTRIBUTES] = self.cmdNoOp
		self.commandHandler [simpleTAL.TAL_OMITTAG] = self.cmdNoOp
		self.commandHandler [simpleTAL.TAL_START_SCOPE] = self.cmdStartScope
		self.commandHandler [simpleTAL.TAL_OUTPUT] = self.cmdOutput
		self.commandHandler [simpleTAL.TAL_STARTTAG] = self.cmdOutputStartTag
		self.commandHandler [simpleTAL.TAL_ENDTAG_ENDSCOPE] = self.cmdEndTagEndScope
		self.commandHandler [simpleTAL.METAL_USE_MACRO] = self.cmdUseMacro
		self.commandHandler [simpleTAL.METAL_DEFINE_SLOT] = self.cmdDefineSlot
		self.commandHandler [simpleTAL.TAL_NOOP] = self.cmdNoOp

		self.inMacro = None
		self.macroArg = None
	# Original cmdOutput
	# Original cmdEndTagEndScope

	def popProgram (self):
		self.inMacro = self.macroStateStack.pop()
		simpleTAL.TemplateInterpreter.popProgram (self)

	def pushProgram (self):
		self.macroStateStack.append (self.inMacro)
		simpleTAL.TemplateInterpreter.pushProgram (self)

	def cmdOutputStartTag (self, command, args):
		newAtts = []
		for att, value in list(self.originalAttributes.items()):
			if (self.macroArg is not None and att == "metal:define-macro"):
				newAtts.append (("metal:use-macro",self.macroArg))
			elif (self.inMacro and att=="metal:define-slot"):
				newAtts.append (("metal:fill-slot", value))
			else:
				newAtts.append ((att, value))
		self.macroArg = None
		self.currentAttributes = newAtts
		simpleTAL.TemplateInterpreter.cmdOutputStartTag (self, command, args)

	def cmdUseMacro (self, command, args):
		simpleTAL.TemplateInterpreter.cmdUseMacro (self, command, args)
		if (self.tagContent is not None):
			# We have a macro, add the args to the in-macro list
			self.inMacro = 1
			self.macroArg = args[0]

	def cmdEndTagEndScope (self, command, args):
		# Args: tagName, omitFlag
		if (self.tagContent is not None):
			contentType, resultVal = self.tagContent
			if (contentType):
				if (isinstance (resultVal, simpleTAL.Template)):
					# We have another template in the context, evaluate it!
					# Save our state!
					self.pushProgram()
					resultVal.expandInline (self.context, self.file, self)
					# Restore state
					self.popProgram()
					# End of the macro expansion (if any) so clear the parameters
					self.slotParameters = {}
					# End of the macro
					self.inMacro = 0
				else:
					if (isinstance (resultVal, str)):
						self.file.write (resultVal)
					elif (isinstance (resultVal, bytes)):
						self.file.write (str (resultVal, 'ascii'))
					else:
						self.file.write (str (str (resultVal), 'ascii'))
			else:
				if (isinstance (resultVal, str)):
					self.file.write (cgi.escape (resultVal))
				elif (isinstance (resultVal, bytes)):
					self.file.write (cgi.escape (str (resultVal, 'ascii')))
				else:
					self.file.write (cgi.escape (str (str (resultVal), 'ascii')))

		if (self.outputTag and not args[1]):
			self.file.write ('</' + args[0] + '>')

		if (self.movePCBack is not None):
			self.programCounter = self.movePCBack
			return

		if (self.localVarsDefined):
			self.context.popLocals()

		self.movePCForward,self.movePCBack,self.outputTag,self.originalAttributes,self.currentAttributes,self.repeatVariable,self.tagContent,self.localVarsDefined = self.scopeStack.pop()
		self.programCounter += 1

def ExpandMacros (context, template, outputEncoding="utf-8"):
	out = io.StringIO()
	interp = MacroExpansionInterpreter()
	interp.initialise (context, out)
	template.expand (context, out, outputEncoding=outputEncoding, interpreter=interp)
	return out.getvalue()
