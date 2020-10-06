local antlr = {}
local typeof = type

function printTable(id, t)
	local processEntry;
	local tabs = "";
	local tabCount = 0
	
	local TABLES = {};
	
	local function addTab()
		tabCount = tabCount + 1;
		tabs = string.rep("     ", tabCount);
	end;
	local function removeTab()
		tabCount = tabCount -1;
		tabs = string.rep("     ", tabCount);
	end;
	processEntry = function(i, v)
		local istring, vstring
		
		if typeof(i) == 'table' then
			istring = "{\n"
			addTab()
			for ii, vv in pairs(i)do
				istring = istring .. processEntry(ii, vv) .. "; ";
			end;	
			removeTab()	
			istring = istring .. "\n" .. tabs .. "}";
		else
			istring = tostring(i);
		end
		if(typeof(v)=='function') then
			vstring = 'FN';
		elseif typeof(v)=='table' then
			local tid = tostring(v);
			local processed = TABLES[tid]
			if processed then
				return tabs .. istring .. ": " .. tid .. "\n"
			else
				TABLES[tid] = true;
				vstring = "{\n"
				addTab()
				for ii, vv in pairs(v)do
					vstring = vstring .. processEntry(ii, vv) ;
				end;
				removeTab()		
				vstring = vstring .. "\n" .. tabs .. "}";
			end
		else
			vstring = tostring(v)
		end
		vstring = vstring .. "; ";
		
		return tabs .. istring .. ": " .. vstring .. "\n";
	end;
	
	print (processEntry(id, t))
end

function antlr.generateSourceTable(source)
	local t = {}
	local c = 0
	for char in string.gmatch(source, '.')do
		c = c + 1
		t[c] = char
	end
	return t	
end

function antlr.generateLexer(tokenRules)
	local tokenLookup = {} -- modeName: [name: string, token]
	local tokens = {} --Enums
	local tokensByName = {}
	local tokenCount = 0
	local tokenList = {} 
	local sourceTable = antlr.generateSourceTable(tokenRules)
	
	local captureTypes = {
		Declaration = -2,
		None = -1,
		String = 0,
		Word = 1,
		Qualifier = 2,
		Directive = 3,
		Assignment = 4,
		Range = 5,
	}
	local qualifierTypes = {
		One = 0,
		List = 2,
		OptionalList = 3,
		Optional = 4,
	}
	local modeTypes = {
		None = -1,
		Rule = 0,
		Mode = 1,
		Directive = 2,
		Pattern = 3,
	}
	local patternTypes = {
		None = -1,
		Subpattern = 0,
		StringLiteral = 1,
		Reference = 2,
		Range = 3,
		Directive = 4,
	}
	local currentMode
	
	--Functions--
	local generateTokens
	local getTokenStream
	do --Function Implementations--
		generateTokens = function()

			
			local captureType = captureTypes.Declaration
			local captureStack = {[1] = captureTypes.Declaration}
			local captureStackPosition = 1

			local modeType = modeTypes.None
			local modeStack = {[1] = modeTypes.None}
			local modeStackPosition = 1

			local currentCharacter = ''
			local lastCharacter = ''
			
			local modes_priority = {}
			local modes_name = {}
			
			local ACCEPTING = true
			local EXCLUDE = false
			local FRAGMENT = false
			
			local EXIT = false
			
			local function getCaptureType()
				captureType = captureStack[captureStackPosition]
			end
			local function pushCaptureType(ctype)
				captureStackPosition = captureStackPosition + 1
				captureStack[captureStackPosition] = ctype
				getCaptureType()
			end
			local function popCaptureType()
				captureStackPosition = captureStackPosition - 1
				getCaptureType()
			end
			local function getModeType()
				modeType = modeStack[modeStackPosition]
			end
			local function pushModeType(mtype)
				modeStackPosition = modeStackPosition + 1
				modeStack[modeStackPosition] = mtype
				getModeType()
			end
			local function popModeType()
				modeStackPosition = modeStackPosition - 1
				getModeType()
			end
			
			local lineCount = 1
			local appendLine = function()
				lineCount = lineCount + 1
			end

			local function exitWarning(...)
				warn(...)
				EXIT = true
			end
			local createMode
			local currentRule
			local currentPattern
			
			local lastPattern
			local patternStack = {}			--Reserved for Rules/Subpatterns
			local patternStackPosition = 0
			local function getPattern()
				currentPattern = patternStack[patternStackPosition]
			end
			local function pushPattern(pattern)
				patternStackPosition = patternStackPosition + 1
				patternStack[patternStackPosition] = pattern
				getPattern()
			end
			local function popPattern()
				patternStackPosition = patternStackPosition - 1
				getPattern()
			end
			
			local modeCount = 0
			
			createMode = function(modeName)
				modeCount = modeCount + 1
				local mode = {}
				mode.name = modeName
				mode.ruleCount = 0
				local rules = {}
				mode.rules_priority = {}
				mode.rules_name = {}
				modes_name[modeName] = mode
				modes_priority[modeCount] = mode
				currentMode = mode
			end
			
			local function createPattern(patternType)
				local s
				if patternType == patternTypes.Range then
					s = ''
				elseif patternType == patternTypes.Reference then
					s = ''
				elseif patternType == patternTypes.StringLiteral then
					s = ''
				elseif patternType == patternTypes.Subpattern then
					s = {[1] = {}}
				end
				local pattern = {
					subject = s, --'String', WORD, StringRange, { children, children }
					parent = currentPattern,
					patternType = patternType,
					qualifierType = qualifierTypes.One,
					childrenId = 1,
					assignedName = nil, -- X = Y, assignedName X subject Y
					closedAssignment = false,
					accepting = ACCEPTING,
					exclude = EXCLUDE,
					fragment = FRAGMENT,
				}
				ACCEPTING = true
				EXCLUDE = false
				FRAGMENT = false
				
				lastPattern = pattern
				
				return pattern
			end
			local function addPatternChildren(pattern)
				pattern.childrenId = pattern.childrenId + 1
				local t = {}
				pattern.subject[pattern.childrenId] = t
				return t
			end
			local function addPatternChild(pattern)
				table.insert(currentPattern.subject[currentPattern.childrenId], pattern)
			end
			local function enterSubpattern(pattern)
				pattern.parent = currentPattern
				addPatternChild(pattern)
				currentPattern = pattern
			end
			local function exitSubpattern()
				local c = currentPattern
				currentPattern = currentPattern.parent
				return c
			end
			
			local createRule createRule = function(ruleName)
				currentMode.ruleCount = currentMode.ruleCount + 1
				local rule = createPattern(patternTypes.Subpattern)
				if rule.fragment == false then
					currentMode.rules_priority[currentMode.ruleCount] = rule
				end
				currentMode.rules_name[ruleName] = rule
				currentRule = rule
				currentRule.name = ruleName
				tokenCount = tokenCount + 1
				currentRule.tokenId = tokenCount
				tokens[ruleName] = tokenCount
				tokensByName[ruleName] = currentRule.tokenId
				return rule
			end

			local currentWord = ''
			local lastWord = ''
			local assignDebounce = false
			local setAssignDebounce = false
			local function clearCurrentWord()
				lastWord = currentWord
				currentWord = ''
			end
			local function captureWord(char)
				currentWord = currentWord .. char
			end
			local lastWordPattern
			local assigning = false
			local onWordFinished onWordFinished = function()
				--[[if modeType == modeTypes.None then
					--pushModeType(modeTypes)
					if currentWord == 'mode' then
						pushModeType(modeTypes.Mode)
						clearCurrentWord()
					else
						if currentCharacter == ':' then
							pushModeType(modeTypes.Rule)
							local rule = createRule(currentWord)
							pushPattern(rule)
							clearCurrentWord()
						else
							exitWarning('Expecting Rule Beginning \':\'- Got \'' .. currentCharacter .. '\' Line: ' .. lineCount)
						end
					end
				elseif modeType == modeTypes.Rule then]]
					--X: HERE
				if captureType == captureTypes.Declaration then
					if currentCharacter == ':' then
						local rule = createRule(currentWord)
						pushPattern(rule)
						pushCaptureType(captureTypes.None)
						clearCurrentWord()
					else
						if FRAGMENT == false and string.match(currentCharacter, '%s') then
							FRAGMENT = true
							clearCurrentWord()
						else
							exitWarning('Expecting Rule Beginning \':\'- Got \'' .. currentCharacter .. '\' Line: ' .. lineCount)
						end
						
					end
				else
					if currentWord == 'not' then
						ACCEPTING = false
					elseif currentWord == 'exclude' then
						EXCLUDE = true
					else
						local p
						if assigning then
							p = lastWordPattern
							p.closedAssignment = true
							p.assignedName = p.subject
							p.subject = currentWord
							p.patternType = patternTypes.Reference
							assigning = false
						else
							p = createPattern(patternTypes.Reference)
							p.subject = currentWord
							addPatternChild(p)	
			
						end
						
						if p~= nil and (currentWord == 'break' or currentWord == 'continue') then
							p.patternType = patternTypes.Directive
						else
							lastWordPattern = p	
						end		
						lastPattern = p							
					end
				
					clearCurrentWord()
				end	
				--[[elseif modeType == modeTypes.Mode then
					--create Token Mode
					createMode(currentWord)
					popModeType()
					clearCurrentWord()
				end]]
			end
			
			local currentStringLiteral = ''
			local stringEscape = false
			local function captureStringLiteral(char)
				local c = char
				if stringEscape then
					stringEscape = false
					--Put in the escape items here
				else
					if c == '\\' then
						stringEscape = true
						c = ''
					end	
				end
				currentStringLiteral = currentStringLiteral .. c
			end
			local onStringLiteralFinished onStringLiteralFinished = function()
				--Place within table
				local p
				if assigning then
					p = lastWordPattern
					p.closedAssignment = true
					p.assignedName = p.subject
					p.subject = currentStringLiteral
					p.patternType = patternTypes.StringLiteral
					assigning = false
				else
					p = createPattern(patternTypes.StringLiteral)
					p.subject = currentStringLiteral
					addPatternChild(p)	
				end
				lastWordPattern = nil
				lastPattern = p
				currentStringLiteral = ''
			end
			
			local currentRange = ''
			local rangeEscape = false
			
			local captureRange captureRange = function(char)
				local c = char
				if rangeEscape then
					rangeEscape = false
				else
					if c == '\\' then
						rangeEscape = true
					end	
				end
				currentRange = currentRange .. c
			end
			
			local processRange = function()
				local replacements = {
					['a%-z'] = '%l',
					['A%-Z'] = '%u',
					['a%-Z'] = '%a',
					['A%-z'] = '%a',
					['0%-9'] = '%d'
				}
				local replacements2 = {}
				for i, v in pairs{ 'd', 'a', 'l', 'u', 'p', 'w', 's', 'c', 'x', 'z'} do
					local upper = string.upper(v)
					replacements2['\\' .. v] = '%' .. v
					replacements2['\\' .. upper] = '%' .. upper
				end
				
				local built = ''
				local current = ''
				
				local new = currentRange
				
				for recognized, replacement in pairs(replacements)do
					--print(recognized, replacement)
					new = string.gsub(new, recognized, function(c)
						return replacements[recognized]
					end)
				end
				for recognized, replacement in pairs(replacements2)do
					--print(recognized, replacement)
					new = string.gsub(new, recognized, function(c)
						return replacements2[recognized]
					end)
				end
				
				currentRange = new--'[' .. new .. ']'
			end
			
			local onRangeFinished onRangeFinished = function()
				local p
				processRange()
				if assigning then
					p = lastWordPattern
					p.closedAssignment = true
					p.assignedName = p.subject
					p.subject = currentRange
					p.patternType = patternTypes.Range
					assigning = false
				else
					p = createPattern(patternTypes.Range)
					p.subject = currentRange
					addPatternChild(p)	
				end
				lastPattern = p
				lastWordPattern = nil
				currentRange = ''
			end
			
			
			local ExamineCharacter
			ExamineCharacter = function(char)
				local letter = string.match(char, '%a')
				local alphanumeric = string.match(char, '%w')
				local isColon = char == ':'
				local isEquals = char == '='
				local isOptional = char == '?'
				local isList = char == '+'
				local isOptionalList = char == '*'
				local isShortlist = char == '-'
				local isDash = isShortlist
				local isGTS = char == '>'
				local isLPAR = char == '('
				local isRPAR = char == ')'
				local isLBRACE = char == '['
				local isRBRACE = char == ']'
				local isQuote = char == '\''
				local isTermination = char == ';'
				local isWhitespace = string.match(char, '%s')
				local isOr = char == '|'
				local isNewLine = char == '\r' or char == '\n'
				local isRuleTerminator = char == ';'
				
				if isNewLine then
					appendLine()
				elseif captureType == captureTypes.Declaration then
					if letter then
						pushCaptureType(captureTypes.Word)
						ExamineCharacter(char)
					elseif isWhitespace then
					else
					end
				elseif captureType == captureTypes.None then
					if letter then
						pushCaptureType(captureTypes.Word)
						ExamineCharacter(char)						
					elseif isWhitespace or isColon then
					elseif isOr then
						addPatternChildren(currentPattern)
					elseif isLPAR then
						local newp = createPattern(patternTypes.Subpattern)
						enterSubpattern(newp)
						pushCaptureType(captureTypes.None)
					elseif isRPAR then
						lastPattern = exitSubpattern()
						popCaptureType()
					elseif isEquals then
						
						if assigning then
							--error, double assignment operator
							exitWarning('Stray Assignment Operand \'' .. char .. '\' Rule \'' .. currentRule.name.. ' Line: ' .. lineCount)
						else
							
							if lastWordPattern ~= nil and lastWordPattern.closedAssignment == false then
								assigning = true
							else
								 
								--Stray assignment operator
								exitWarning('Stray Assignment Operand \'' .. char .. '\' Rule \'' .. currentRule.name ..' Line: ' .. lineCount)
							end
						end
					elseif isQuote then
						pushCaptureType(captureTypes.String)
					elseif isLBRACE then
						pushCaptureType(captureTypes.Range)
					elseif isRuleTerminator then
						popModeType()
						popCaptureType()
					else
						if lastPattern~=nil then
							if isList then
								lastPattern.qualifierType = qualifierTypes.List
							elseif isOptionalList then
								lastPattern.qualifierType = qualifierTypes.OptionalList
							elseif isOptional then
								lastPattern.qualifierType = qualifierTypes.Optional
							end
						else
							exitWarning('Expecting Pattern Rule- Got \'' .. char .. '\' Line: ' .. lineCount)
						end
						
					end
				elseif captureType == captureTypes.Word then
					if letter then
						captureWord(char)
					else
						popCaptureType()
						onWordFinished()
						ExamineCharacter(char)		
					end
				elseif captureType == captureTypes.String then
					if isQuote and stringEscape == false then
						popCaptureType()
						onStringLiteralFinished()
					else
						captureStringLiteral(char)
					end		
				elseif captureType == captureTypes.Range then
					--print(char)
					if isRBRACE and rangeEscape == false then
						popCaptureType()
						onRangeFinished()
					else
						--print(char)
						captureRange(char)
					end
				else
					if modeType == modeTypes.Rule then
						if isRuleTerminator then
							popModeType()
							popCaptureType()
							if captureType ~= captureTypes.None then
								exitWarning('Unfinished Rule: \'' .. currentRule.name .. '\' Line: ' .. lineCount)
							end
						end
					end

				end
		  	end
			
			createMode('Main')
			
			for i = 1, #sourceTable do
				local char = sourceTable[i]
				currentCharacter = char
				ExamineCharacter(char)
				if EXIT then
					break
				end
				lastCharacter = char
				
			end
			
		end
		
		getTokenStream = function(sourceRaw)
			local matchTokens		--rules
			local matchComponents 	--rule contents
			
			local source = antlr.generateSourceTable(sourceRaw)
			
			local stream = {}
			
			matchTokens = function() 
				local currentPos = 1
				local artifact = ''
				
				while currentPos <= #source do
					--wait(.1)print(currentPos)
					local success = false
					for i,v in pairs(currentMode.rules_priority) do
						local found, captured, originalPos, newPos, trueBreak = matchComponents(source, currentPos, v)
						--print(found, captured, originalPos, newPos)
						if found then
							success = true
							currentPos = newPos
							table.insert(stream, {name = v.name, text = captured, id = v.tokenId})
							break
						end
					end					
					if success == false then
						artifact = artifact .. source[currentPos]
						currentPos = currentPos + 1
					else
						
						--print('current artifact:', artifact)
						--table.insert(stream, {name = 'Artifact', text = artifact, id = -1})
						artifact = ''
					end
				end
				
				--printTable('Stream', stream)
				--return stream
			end				
			matchComponents = function(sourceTable, currentPosition, component) 		
				local built = ''
				local FOUND = false
				local original = currentPosition
				local trueBreak = false
				local excluding = false
				if component.patternType == patternTypes.Subpattern then
					local searching = true
					
					local str = ''
					local allsuccess = true
					for i,children in pairs(component.subject)do
						local subsuccess = true
						for i2, child in pairs(children)do
							local found, captured, originalPos, newPos, trueB, ff = matchComponents(sourceTable, currentPosition, child)
							--print(found, captured, originalPos, newPos)
							local canPass = ff
							if child.qualifierType == qualifierTypes.One or child.qualifier == qualifierTypes.List then
								canPass = found or ff
							else --OptionalList, Optional
								canPass = true
							end
							
							if canPass then
								if child.qualifierType ~= qualifierTypes.One and trueB == false then
									local success = true
									while success do
										local found2, captured2, originalPos2, newPos2, ex = matchComponents(sourceTable, newPos, child)
										if found2 then
											captured = captured .. captured2
											newPos = newPos2
										else
											break
										end
									end
								end
								if child.exclude == false then
									str = str .. captured
								end
								currentPosition = newPos
							elseif trueB then
								trueBreak = true
								subsuccess = true
								currentPosition = newPos
							else
								subsuccess = false
								str = ''
								break
							end
						end
						if subsuccess then
							allsuccess = true
							FOUND = true
							if component.exclude == false then
								built = built .. str
							end
							break
						end
					end
				elseif component.patternType == patternTypes.Directive then
					if component.subject == 'break' then
						trueBreak = true
						--currentPosition = currentPosition + 5
					end
				elseif component.patternType == patternTypes.Reference then
					local searching = true
					--print(component.subject)

					local rule = currentMode.rules_name[component.subject]
					if rule.fragment == false then
						warn('Attempting to reference non-fragment Rule:' .. rule.name)
					else
						local str = ''
						local allsuccess = true
						--print(component.subject, currentMode.rules_name[component.subject])
						for i,children in pairs(rule.subject)do
							local subsuccess = true
							for i2, child in pairs(children)do
								local found, captured, originalPos, newPos, trueB, ff = matchComponents(sourceTable, currentPosition, child)
								--print(found, captured, originalPos, newPos)
								local canPass = ff
								if child.qualifierType == qualifierTypes.One or child.qualifier == qualifierTypes.List then
									canPass = found or ff
								else --OptionalList, Optional
									canPass = true
								end

								if canPass then
									if child.qualifierType ~= qualifierTypes.One and trueB == false then
										local success = true
										while success do
											local found2, captured2, originalPos2, newPos2 = matchComponents(sourceTable, newPos, child)
											if found2 then
												
												captured = captured .. captured2
												newPos = newPos2
											else
												break
											end
										end
									end
									if child.exclude == false then
										str = str .. captured
									end								
									
									currentPosition = newPos
								elseif trueB then
									trueBreak = true
									subsuccess = true
									currentPosition = newPos
								else
									subsuccess = false
									str = ''
									break
								end
							end
							if subsuccess then
								FOUND = true
								allsuccess = true
								if component.exclude == false then
									built = built .. str	
								end
								break
							end
						end	
					end
					
				elseif component.patternType == patternTypes.StringLiteral then
					local searching = true
					while searching do
						
						local str = ''
						for i = currentPosition, currentPosition + #component.subject -1 do
							if sourceTable[i] ~=nil then
								str = str .. sourceTable[i]
							end
						end
						--wait(.1) --print(123)
						local works = str == component.subject
						FOUND = works
						if (works==true and component.accepting == true) or (works == false and component.accepting == false) then
							if component.exclude == false then
								built = built .. str
							end
							--print(str, currentPosition, currentPosition + #component.subject)
							currentPosition = currentPosition + #component.subject
							if component.qualifierType == qualifierTypes.One then
								searching = false
							end
						else
							searching = false
						end
					end
				elseif component.patternType == patternTypes.Range then
					local searching = true
					while searching do
						--print(sourceTable[currentPosition])
						local str = sourceTable[currentPosition]
						if str ~= nil then
							local works = (string.match(str, '[' .. component.subject .. ']') or string.match(str, component.subject) ) ~= nil
							FOUND = works
							if (works==true and component.accepting == true) or (works == false and component.accepting == false) then
								if component.exclude == false then
									built = built .. str
								end
								currentPosition = currentPosition + 1
								if component.qualifierType == qualifierTypes.One then
									searching = false
								end
							else
								searching = false
							end
						else
							searching = false
						end
					end
				end
				--print(component.subject, component.exclude)
				return built~= '' or (component.exclude == true and FOUND), built, original, currentPosition, trueBreak, FOUND
				
			end
			matchTokens()
			return stream
		end
		
	end

	generateTokens()
	
	local built = {}
	built.getTokenStream = getTokenStream
	built.tokens = tokens
	built.tokensByName = tokensByName
	--printTable(currentMode.name, currentMode)
	return built
end

antlr.parserLexer = antlr.generateLexer(
	[==[
		COLON: ':';
		SEMICOLON: ';';
		fragment word: [a-Z][a-Z0-9_]*;
		EQUALS: word exclude [\s]* exclude '=';
		WORD: word;
		LPAR: '(';
		RPAR: ')';
		OR: '|';
		OPTIONAL: '?';
		LIST: '+';
		OPTIONALLIST: '*';
		
	]==]
)

function antlr.generateParser(lexer, parserRules)
	local rulesPriority = {}
	local rulesName = {}
	local ruleCount = 0
	
	local tokens = antlr.parserLexer.tokens
	local tokensByName = antlr.parserLexer.tokensByName
	local tokenStream = antlr.parserLexer.getTokenStream(parserRules)
	--printTable('TokenStream', tokenStream)
	
	local rules = {}
	
	local stateTypes = {
		None = -1,
		Declaration = 0,
		Rule = 2,
	}
	local patternTypes = {
		None = -1,
		Subpattern = 0,
		Reference = 2,
		Directive = 4,
	}
	
	local qualifierTypes = {
		One = 0,
		List = 2,
		OptionalList = 3,
		Optional = 4,
	}
	
	local state
	local statePosition = 0
	local stateStack = {}
	local function getState()
		state = stateStack[statePosition]
	end
	local function pushState(s)
		statePosition = statePosition + 1
		stateStack[statePosition] = s
		getState()
	end
	local function popState()
		statePosition = statePosition - 1
		getState()
	end
	
	pushState(stateTypes.Declaration)
	
	local currentPattern
	local lastPattern
	local patternPosition = 0
	local patternStack = {}
	
	local function getPattern()
		currentPattern = patternStack[patternPosition]
	end
	local function pushPattern(p)
		patternPosition = patternPosition + 1
		patternStack[patternPosition] = p
		getPattern()
	end
	local function popPattern()
		patternPosition = patternPosition - 1
		getPattern()
	end
	
	local apatternPosition = 0
	local apatternStack = {}
	local currentaPattern
	
	local function getaPattern()
		currentaPattern = apatternStack[apatternPosition]
	end
	local function pushaPattern(p)
		apatternPosition = apatternPosition + 1
		apatternStack[apatternPosition] = p
		getaPattern()
	end
	local function popaPattern()
		apatternPosition = apatternPosition - 1
		getaPattern()
	end
		
	local function createPattern(patternType)
		local s
		if patternType == patternTypes.Reference then
			s = ''
		elseif patternType == patternTypes.Subpattern then
			s = {[1] = {}}
		end
		local pattern 
		--ACCEPTING = true
		--EXCLUDE = false
		--FRAGMENT = false
		
		if apatternPosition == 0 then --currentaPattern nil
			pattern = {
				subject = s, --'String', WORD, StringRange, { children, children }
				parent = currentPattern, --current (...) surrounded
				patternType = patternType,
				qualifierType = qualifierTypes.One,
				childrenId = 1,
				assignedName = nil, -- X = Y, assignedName X subject Y
				closedAssignment = false,
				--accepting = ACCEPTING,
				--exclude = EXCLUDE,
				--fragment = FRAGMENT,
			}
		else
			pattern = currentaPattern
			popaPattern()
			pattern.subject = s
			pattern.parent = currentaPattern
			pattern.patternType = patternType
			
		end
		
		lastPattern = pattern
		
		return pattern
	end
	
	local appendChild
	
	local function EnterSubpattern()
		local sp = createPattern(patternTypes.Subpattern)
		pushPattern(sp)
		lastPattern = nil
		return sp
	end
	local function ExitSubpattern()
		local p = currentPattern
		popPattern()
		lastPattern = p
	end
	
	local function createRule(ruleName)
		ruleCount = ruleCount + 1
		local rule = EnterSubpattern()--createPattern(patternTypes.Subpattern)
		
		rulesName[ruleName] = rule
		rule.name = ruleName
		rule.ruleId = ruleCount
		--currentRule = rule
		--currentRule.name = ruleName
		--tokenCount = tokenCount + 1
		--currentRule.tokenId = tokenCount
		rules[ruleName] = ruleCount
		rulesPriority[ruleCount] = rule
		return rule
	end
	
	local function appendChildren()
		if currentPattern ~= nil then
			currentPattern.childrenId = currentPattern.childrenId + 1
			currentPattern.subject[currentPattern.childrenId] = {}
		end
	end
	function appendChild(pattern)
		if currentPattern ~= nil then
			--local pattern = createPattern(patternType)
			table.insert(currentPattern.subject[currentPattern.childrenId], pattern)
			lastPattern = pattern
		end
	end
	local function appendChildSpec(parent, pattern)
		table.insert(parent.subject[parent.childrenId], pattern)
		--lastPattern = pattern
	end
	
	local currentDeclared
	
	local currentAssignmentPattern
	local ExamineToken ExamineToken = function(token)
		local isWord = token.id == tokens.WORD
		local isColon = token.id == tokens.COLON
		local isSemi = token.id == tokens.SEMICOLON
		local isLPAR = token.id == tokens.LPAR
		local isRPAR = token.id == tokens.RPAR
		local isOR = token.id == tokens.OR
		local isOPTIONAL = token.id == tokens.OPTIONAL
		local isList = token.id == tokens.LIST
		local isOPTIONALLIST = token.id == tokens.OPTIONALLIST
		local isEQUALS = token.id == tokens.EQUALS
		local isArtifact = token.id == -1
		local text = token.text
		
		if state == stateTypes.Declaration then
			if isWord then
				currentDeclared = text
			elseif isColon then
				pushState(stateTypes.Rule)
				createRule(currentDeclared)
			end
		elseif state == stateTypes.Rule then
			if isWord then
				--if currentAssignmentPattern ~=nil then
					--currentAssignmentPattern.subject = text
					--appendChild(currentAssignmentPattern)
					--currentAssignmentPattern = nil
				--else
				local p = createPattern(patternTypes.Reference)
				p.subject = text
				appendChild(p)
				--end
			elseif isEQUALS then
				local p = createPattern(patternTypes.Reference)
				p.assignedName = text
				pushaPattern(p)
				appendChild(p)
			elseif isColon then
				--popState()
			elseif isOR then
				appendChildren()
			elseif isLPAR then
				--local c = currentPattern
				EnterSubpattern()
			elseif isRPAR then
				ExitSubpattern()
				if lastPattern.assignedName == nil then
					appendChild(lastPattern)
				end
			elseif isSemi then
				popState()
			elseif lastPattern~= nil then
				if isOPTIONAL then
					lastPattern.qualifierType = qualifierTypes.Optional
				elseif isList then
					lastPattern.qualifierType = qualifierTypes.List
				elseif isOPTIONALLIST then
					lastPattern.qualifierType = qualifierTypes.OptionalList
				end
			end
		end
		
	end
	for i, v in pairs(tokenStream) do
		ExamineToken(v)
	end
	
	--printTable('Rules', rulesPriority)
	
	local parser = {}
	
	function parser.parse(source, options)
		local specificRule
		local lexerFilter
		if options~=nil then
			specificRule = options['rule']
			lexerFilter = options['filter']
		end
		local tokenStream = lexer.getTokenStream(source)
		printTable('TokenStream', tokenStream)
		
		local tokens = lexer.tokens
		local tokensByName = lexer.tokensByName

		local matchComponent
		local matchRule
		local matchToken
		local streamPosition
		local assignmentOwner
		local assignmentStackPosition = 0
		local assignmentStack = {}
		
		
		local function getAssignmentOwner()
			assignmentOwner = assignmentStack[assignmentStackPosition]
			return assignmentStack[assignmentStackPosition]
		end		
		local function pushAssignmentOwner(owner)
			assignmentStackPosition = assignmentStackPosition + 1
			assignmentStack[assignmentStackPosition] = owner
			getAssignmentOwner()
		end
		local function popAssignmentOwner(owner)
			assignmentStackPosition = assignmentStackPosition - 1
			getAssignmentOwner()
		end
		local function appendValueToOwner(owner, name, value, qualifier)
			if owner[name] == nil then
				if qualifier == qualifierTypes.List or qualifier == qualifierTypes.Optional or qualifier == qualifierTypes.OptionalList then
					owner[name] = {}
					table.insert(owner[name], value)
				else
					owner[name] = value
				end
			elseif owner[name] ~= nil then
				local o = owner[name]
				owner[name] = {}
				if typeof(o) == 'table' then
					for i,v in pairs(o)do
						table.insert(owner[name], o)
					end
				else
					table.insert(owner[name], o)
				end
				
				table.insert(owner[name], value)
			end
		end
		
		matchComponent = function(currentPosition, component)-- return found, captured, originalPos, newPos
			local token = tokenStream[currentPosition]
			local built = {}
			local numberFound = 0
			local originalPosition = currentPosition
			local newPosition = currentPosition
			local qualifier = component.qualifier
			local assignedName
			if component.patternType == patternTypes.Reference then
				local t = tokensByName[component.subject]
				local p = rulesName[component.subject]
				if assignedName == nil then
					assignedName = component.subject
				end				
				if t ~= nil then
					print(token.id, t)
					if token.id == t then
						numberFound = numberFound + 1
						newPosition = currentPosition + 1
						appendValueToOwner(built, assignedName, token, qualifier) --actually just make the built absolorb whats found,
						--and when it transfers to another built, just absorb the values. Then when a RULE passes, THEN you assign to owner.
						if qualifier ~= qualifierTypes.One then
							local searching = true
							while searching do
								local nextToken = tokenStream[newPosition]
								if nextToken ~= nil then
									if token.id == t then
										numberFound = numberFound + 1
										newPosition = newPosition + 1
										appendValueToOwner(built, assignedName, nextToken, qualifier)
									else
										searching = false
									end
								else
									searching = false
								end
							end
							
						end
					else
						
					end
				elseif p ~= nil then
					--This is a rule
				end
			elseif component.patternType == patternTypes.Subpattern then
				for i, children in pairs(component.subject)do
					local childrenSuccess = true
					local builtTemp = {}
					for i2, child in pairs(children)do
						local childSuccess = false
						local success, b, original, new = matchComponent(newPosition, child)
						local qualifier = child.qualifierType
						local canPass = success
						if qualifier ~= qualifierTypes.One or qualifier ~= qualifierTypes.List then
							canPass = true
						end
						
						if canPass then
							local merge = {}
							table.insert(merge, b)
							local newestPos = new
							if qualifier == qualifierTypes.List or qualifier == qualifierTypes.OptionalList then
								local searching = true
								while searching do
									local success2, b2, original2, new2 = matchComponent(newestPos, child)
									if success2 then
										newestPos = new2
										table.insert(merge, b2)
									else
										searching = false
									end
								end
							end
							for _, build in pairs(merge)do
								for name, value in pairs(build)do
									if type(value)=='table' then
										for __, value0 in pairs(value)do
											appendValueToOwner(builtTemp, name, value0, qualifier)
										end
									else
										appendValueToOwner(builtTemp, name, value, qualifier)
									end
								end
							end
							newPosition = newestPos
						else
							childrenSuccess = false
							break
							newPosition = originalPosition
						end
					end
					if childrenSuccess then
						numberFound = 1
						for _, build in pairs(builtTemp)do
							for name, value in pairs(build)do
								if type(value)=='table' then
									for __, value0 in pairs(value)do
										appendValueToOwner(built, name, value0, qualifierTypes.One)
									end
								else
									appendValueToOwner(built, name, value, qualifierTypes.One)
								end
							end
						end
						break
					end
				end
			end
			
			return numberFound ~= 0, built, originalPosition, newPosition, assignedName
		end
		printTable('Rules', rulesPriority)
		printTable('tokensByName', tokensByName)

		local function appendAssignedNameGroup(name)
			if assignmentOwner ~=nil then
				if assignmentOwner[name]==nil then
					assignmentOwner[name] = {}
				end
				return assignmentOwner[name]
			else
				
			end
		end
		local function appendAssignmentValue(name, value)
			if assignmentOwner ~=nil then
				local tab = assignmentOwner[name]
				if tab == nil then
					assignmentOwner[name] = {}
					tab = assignmentOwner[name]
				end
				table.insert(tab, value)
			else
				print(123)
			end
		end

		matchComponent2 = function(currentPosition, parserComponent, overrideSearch,optionalBuild)
			local currentToken = tokenStream[currentPosition]
			local componentType = parserComponent.patternType
			local found = false
			local originalPosition = currentPosition
			local newPosition = currentPosition
			local optional = parserComponent.qualifierType == qualifierTypes.Optional or parserComponent.qualifierType == qualifierTypes.OptionalList
			local isCollection = parserComponent.qualifierType == qualifierTypes.OptionalList or parserComponent.qualifierType == qualifierTypes.List
			local built = optionalBuild or {}
			local builtString = ''
			local canPass = false
			if currentToken==nil then
			elseif componentType == patternTypes.Reference then
				local tokenReference = tokensByName[parserComponent.subject]
				local parserReference = rulesName[parserComponent.subject]
				if tokenReference~=nil then
					local matches = tokenReference == currentToken.id
					if matches then
						newPosition = newPosition + 1
						found = true
						builtString = builtString .. currentToken.text
						local assignedName = parserComponent.assignedName or parserComponent.subject
						--if built[assignedName] == nil then
						--	built[assignedName] = {}
						--end
						appendAssignmentValue(assignedName, currentToken)
						--table.insert(built[assignedName], currentToken)
						--[[
						if parserComponent.assignedName~=nil then
							if built[parserComponent.assignedName] == nil then
								built[parserComponent.assignedName] = {}
							end
							table.insert(built[parserComponent.assignedName], currentToken)
						else
							if built[parserComponent.subject] == nil then
								built[parserComponent.subject] = {}
							end
							table.insert(built[parserComponent.subject], currentToken)
						end
							]]
					end
				elseif parserReference~=nil then
					local subpattern = parserReference
					--if assign then
					--	pushAssignmentOwner(appendAssignedNameGroup(assignedName))
					--end
					local t = {}
					pushAssignmentOwner(t)

					local f2, b2, originPos, newPos, canp, bstr = matchComponent2(currentPosition, subpattern, false)
					popAssignmentOwner()
					if f2 then
						appendAssignmentValue(parserComponent.assignedName or parserComponent.subject, t)
						if t.text == nil then
							t.text = ''
						end
						t.text = t.text .. bstr
						--local assignedName = parserComponent.assignedName or parserComponent.subject
						--if built[assignedName] == nil then
						--	built[assignedName] = {}
						--end
						found = true
						newPosition = newPos
						--table.insert(built[assignedName], b2)
						--appendAssignmentValue(b2)
						builtString = builtString .. bstr
					end
					
				else
					print('non-working reference', parserComponent.subject)
				end
			elseif componentType == patternTypes.Subpattern then
				for index0, children in pairs(parserComponent.subject)do
					local childrenSuccess = true
					local builtTemp = {}
					local bstringTemp = ''
					local assignedName = parserComponent.assignedName or parserComponent.subject
					local assign = parserComponent.assignedName ~=nil
					local group
					if assign then
						local group = appendAssignedNameGroup(assignedName)
						pushAssignmentOwner(group)
					end


					for index1, child in pairs(children)do
						local f, b, opos, npos, canPass, bstr = matchComponent2(newPosition, child, false)
						if f then
							bstringTemp = bstringTemp .. bstr
							
							newPosition = npos
							--[[
							for name,collected in pairs(b)do
								if name ~= 'text' then
									local ins
									if assign then
										if builtTemp[assignedName] == nil then
											builtTemp[assignedName] = {}
										end
										if builtTemp[assignedName][name] == nil then
											builtTemp[assignedName][name] = {}
										end
										--ins = {}
										--table.insert(builtTemp[assignedName], ins)
										ins = builtTemp[assignedName][name]
									else
										if builtTemp[name] == nil then
											builtTemp[name] = {}
										end
										ins = builtTemp[name]
									end
									for _,v in pairs(collected)do
										table.insert(ins, v)
									end
								end
							end]]
						else
							newPosition = opos
							if canPass == false then
								childrenSuccess = false
								break
							end
						end
					end
					if assign then
						if assignmentOwner.text == nil then
							assignmentOwner.text = ''
						end
						assignmentOwner.text = assignmentOwner.text .. bstringTemp
						popAssignmentOwner()
					end

					if childrenSuccess then
						found = true
						builtString = builtString .. bstringTemp
						for name,collected in pairs(builtTemp)do
							if name ~= 'text' then
								if built[name] == nil then
									built[name] = {}
								end
								for _,v in pairs(collected)do
									table.insert(built[name], v)
								end
							end
						end
						break
					else
						newPosition = originalPosition
					end
				end
			end
			--print(parserComponent.qualifierType, qualifierTypes.List, parserComponent.qualifierType== qualifierTypes.List)
			if found and isCollection and overrideSearch == false then
				
				local searching = true
				while searching do
					local tempNextPosition = newPosition
					local found2, b2, origin, newPos, bstring  = matchComponent2(tempNextPosition, parserComponent, true, built)
					if found2 then
						newPosition = newPosition + 1
						builtString = builtString .. bstring
					else
						searching = false
					end
				end
			elseif not found or canPass then
				newPosition = originalPosition
			end

			built.text = builtString

			return found , built, originalPosition, newPosition, optional, builtString
		end

		local currentPos = 1
		local parserArtifacts = {}
		--local testComponent = rulesName['main']
		local specificComponent = rulesName[specificRule]
		local Built = {
			byOrder = {};
			byName = {};
		}
		while currentPos <= #tokenStream do
			local currentToken = tokenStream[currentPos]
			if currentToken == nil then
				break
			end
			--printTable(currentToken.name, currentToken)
			local ff = false
			if specificRule == nil then
				for i = 1, #rulesPriority do
					local priority = i
					local component = rulesPriority[priority]
				--for priority, component in pairs(rulesPriority)do
					local b = {}
					pushAssignmentOwner(b)
					local found, built, originalPos, newPos, canp, bstr = matchComponent2(currentPos, component, false)
					popAssignmentOwner()
					if found then
						ff = true
						for name,collected in pairs(built)do
							if name ~= 'text' then
								if b[name] == nil then
									b[name] = {}
								end
								for _,v in pairs(collected)do
									table.insert(b[name], v)
								end
							end
						end
						currentPos = newPos
						b['ruleId'] = component.name
						b['text'] = bstr
						table.insert(Built.byOrder, b)
						if Built.byName[component.name]==nil then
							Built.byName[component.name] = {}
						end
						table.insert(Built.byName[component.name], b)
						break
					end
					--printTable('built', b)
					--currentPos = newPos
				end
			else
				local component = specificComponent
				local b = {}
				pushAssignmentOwner(b)
				local found, built, originalPos, newPos, canp, bstr = matchComponent2(currentPos, component, false)
				popAssignmentOwner()
				if found then
					ff = true
					for name,collected in pairs(built)do
						if name ~= 'text' then
							if b[name] == nil then
								b[name] = {}
							end
							for _,v in pairs(collected)do
								table.insert(b[name], v)
							end
						end
					end
					currentPos = newPos
					b['ruleId'] = component.name
					b['text'] = bstr
					table.insert(Built.byOrder, b)
					if Built.byName[component.name]==nil then
						Built.byName[component.name] = {}
					end
					table.insert(Built.byName[component.name], b)
					
				end
			end
			if ff == false then
				currentPos = currentPos + 1
			end
		end

		printTable('Built', Built)
		return Built
	end


	return parser
end


local lexerRules = 
	[==[
		PUBLIC: 'public';

		VAR: 'var';
		VAL: 'val';
		EQUALS: '=';
		COMMA: ',';
		LT: '<';
		GT: '>';
		SLASH: '/';
		WORD: [a-Z][a-Z_0-9]*;
		NUMBER: [0-9]*;

		STRING: '"' not'"'* '"';
	]==]

local parserRules = 
	[==[
		declaration: DECTYPE=(VAR | VAL) VARIABLENAMES = (WORD (COMMA WORD)*) VALUES = (EQUALS value (COMMA value)*)?;
		value: WORD | NUMBER | STRING;
	]==]

local lexer = antlr.generateLexer(lexerRules)
local parser = antlr.generateParser(lexer, parserRules)
local test = parser.parse([==[
	var X, Y = 0, 1
	var a,b = 2,3
	]==], {rule = 'declaration'})

local declarations = test.byOrder
for i, declaration in pairs(declarations)do
	local varWords = declaration.VARIABLENAMES.WORD
	local values = declaration.VALUES.value
	local word0, word1 = varWords[1].text, varWords[2].text
	local value0, value1 = values[1].text, values[2].text
	print(word0, value0, word1, value1) 
end
