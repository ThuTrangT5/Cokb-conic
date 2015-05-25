# Reading COKB files
# - Objects.txt
# - Relation.txt
# - Rules.txt
# - Functions.txt
# - Define_Functions.txt

(* Cac ham:
 1.Url
 2. Init
 3.readObjectsTXT
 4.readRelationsTXT
 5.readOperators
 6.readDefineOperatorsTXT
 7.readFunctionsTXT
 8.readDefineFunctionsTXT
 9.ReadCObject:
	- readObjectName
	- readBaseObject
	- readVariables
	- readConstraints
	- readConstructRelations
	- readProperties
	- readComputationRelations
	- readRulesO
 10.readFunctions
*)

#URL funcion
GeometryConicSolver[Url] := proc (urlInput::string) 
	global url; 
	url := urlInput; 
	return url;
end proc:

GeometryConicSolver[Init] := proc () 
	local fileName;
	global Obj_Structs, Rela_Structs, Rule_Structs, Func_Names, Func_Structs, url, RuleEqs_Structs;
	fileName := cat(url, "/data/Objects.txt"); 
	readObjectsTXT(fileName); 
	fileName := cat(url, "/Data/relations.txt");
	readRelationsTXT(fileName);
	fileName := cat(url, "/data/Functions.txt");
	readFunctionsTXT(fileName);
	fileName := cat(url, "/data/define_functions.txt");
	readDefineFunctionsTXT(fileName);
	fileName := cat(url, "/data/Rules.txt");
	readRulesTXT(fileName);
end proc:

#Read file Objects.txt
GeometryConicSolver[readObjectsTXT] := proc (fileName::string)
	local fd, line;
	global Obj_Structs;
	
	Obj_Structs := [];
	fd := fopen(fileName, READ, TEXT);
	line := readline(fd);
	while line <> 0 and SearchText("begin_Objects", line) = 0 do line := readline(fd) end do;
	line := readline(fd);
	while line <> 0 and SearchText("end_Objects", line) = 0 do 
	      if line <> "" then 
		      Obj_Structs := [op(Obj_Structs), [convert(parse(line), string), []]];
	      end if; 
	      line := readline(fd)
	end do;
	fclose(fd);
	return Obj_Structs;
end proc:

#Read file Relations.txt
GeometryConicSolver[readRelationsTXT] := proc (fileName::string) 
	local fd, line, exps, x; 
	global Rela_Structs; Rela_Structs := []; 
	x := []; 
	fd := fopen(fileName, READ, TEXT); 
	line := readline(fd); 
	while line <> 0 and SearchText("begin_Relations", line) = 0 do 
	      line := readline(fd) 
	end do; 
	line := readline(fd); 
	while line <> 0 and SearchText("end_Relations", line) = 0 do
	      if line <> "" then 
		    exps := [parse(line)]; 
		    if nops(exps) = 2 then 
		       if evalb(op(1, exps[1]) = "=") then 
			      x := map(s->convert(s, string), exps[1]) 
		       else 
			    x := map(s->convert(parse(s), string), exps[1]) 
		       end if; 
		       exps[1] := x; 
		       Rela_Structs := [op(Rela_Structs), exps];
		    end if;
	      end if; 
	 line := readline(fd);
	end do; 
	fclose(fd); 
	return Rela_Structs;
end proc:

#Read file Rules.txt
GeometryConicSolver[readRulesTXT] := proc (fileName::string)
	local rules, sortRule; 
	global Rule_Structs, readRules, RuleEqs_Structs; 
	
	# readRules function
	readRules := proc (fileName::string) 
		local line, fd, readRule1, readKindRule, Init, readHypothesis, readGoal, readProc, readVariables, kindRule, variableNames, variableNames1, variableTypes, hypothesisGoal, procs, k, i, ruleStructs, readRead; 
	
		#---Init
		Init := proc () 
			kindRule := ""; 
			variableNames := []; 
			variableTypes := []; 
			hypothesisGoal := [{}, {}]; 
			procs := [];	
		end proc; 
	
		#---readKindRule
		readKindRule := proc () 
			kindRule := rhs(parse(line))		
		end proc;
		
		#---readHypothesis
		readHypothesis := proc () 
			line := readline(fd); 
			while line <> 0 and SearchText("end_hypothesis_part", line) = 0 do 
			     if type(parse(line), set) then 
				  hypothesisGoal[1] := parse(line) 
			     end if; 
			     line := readline(fd);
			end do;
		end proc;

		#---readGoal
		readGoal := proc () 
			line := readline(fd); 
			while line <> 0 and SearchText("end_goal_part", line) = 0 do
			      if type(parse(line), set) then 
				    hypothesisGoal[2] := parse(line) 
			      end if; 
			      line := readline(fd);
			end do;
		end proc; 

		#---readProc
		readProc := proc () 
			k := SearchText(":", line); 
			procs := [op(procs), parse(substring(line, k+1 .. length(line)))]; 
		end proc;

		#---readVariables
		readVariables := proc () 
			k := SearchText(":", line);
			variableNames1 := [parse(substring(line, 1 .. k-1))]; 
			for i to nops(variableNames1) do 
			    variableTypes := [op(variableTypes), convert(parse(substring(line, k+1 .. length(line))), string)]; 
			end do; 
			variableNames := [op(variableNames), op(variableNames1)];
		end proc;

		#--readRule1
		readRule1 := proc () 
			Init();  
			while line <> 0 and SearchText("begin_rule", line) = 0 do
			      if 0 < SearchText("end_rules", line) then 
				    return;  
			      end if;
			      line := readline(fd); 
			end do; 
			line := readline(fd); 
			while line <> 0 and SearchText("end_rule", line) = 0 do 
			      if 0 < SearchText("kind_rule", line) then 
				    readKindRule(); 
			      elif 0 < SearchText("hypothesis_part", line) then 
				    readHypothesis(); 
			      elif 0 < SearchText("goal_part", line) then 
				    readGoal(); 
			      elif 0 < SearchText("proc:", line) then 
				    readProc();
			      else 
				   if line <> "" then 
					readVariables();
				   end if;
			      end if; 
			      line := readline(fd);
			end do; 
			if kindRule = "thanh_lap_phuong_trinh" then 
			      RuleEqs_Structs := [op(RuleEqs_Structs), [kindRule, variableNames, variableTypes, hypothesisGoal, procs, readTrue]];
			else 
			      Rule_Structs := [op(Rule_Structs), [kindRule, variableNames, variableTypes, hypothesisGoal, procs]];
			end if;
		end proc;

		#Thân hàm readRules---
		fd := fopen(fileName, READ, TEXT); 
		line := readline(fd); 
		Rule_Structs := []; 
		RuleEqs_Structs := []; 
		while line <> 0 and SearchText("begin_rules", line) = 0 do 
		      line := readline(fd);
		end do; 
		line := readline(fd); 
		while line <> 0 and SearchText("end_rules", line) = 0 do 
		      readRule1();
		end do; 
		fclose(fd); 
		return Rule_Structs;
	end proc; #------------------readRules

	# sort rules by number of hypothesis of rule by descending
	sortRule := proc (rules) 
		local numOfHypos, newRules, arr, s, i, arr2; 
		numOfHypos := seq(nops(i[4][1]), `in`(i, rules)); 
		newRules := []; arr := []; s := nops(rules); 
		for i to s do 
			newRules := [op(newRules), []]; 
			arr := [op(arr), [numOfHypos[i], i]] 
		end do;
		
		arr2 := sort(arr); 
		for i to s do 
			newRules[s-i+1] := rules[arr2[i][2]] 
		end do; 
		return newRules; 
	end proc:#end sortRule 
	
	#Main--------------------
	rules := readRules(fileName);
	Rule_Structs := sortRule(rules);
	#Rule_Structs := readRules(fileName); 
end proc:

#Read file Operators.txt
GeometryConicSolver[readOperators] := proc (fileName::string) 
	local fd, line, chuyen; 
	global Op_Names; 
	
	chuyen := proc (s::list) 
		local n, i, l; 
		n := nops(s);
		i := 1; 
		l := []; 
		while i <= n do 
		      if type(op(i, s), list) then 
			    l := [op(l), map(proc (x) options operator, arrow; convert(x, string) end proc, s[i])];
		      else l := [op(l), convert(s[i], string)]; 
		      end if; 
		      i := i+1; 
		end do;
		return l 
	end proc; 
	
	Op_Names := []; 
	fd := fopen(fileName, READ, TEXT); 
	line := readline(fd); 
	while line <> 0 and SearchText("begin_Operators", line) = 0 do 
	      line := readline(fd); 
	end do; 
	line := readline(fd); 
	while line <> 0 and SearchText("end_Operators", line) = 0 do 
	      if line <> "" then 
		    Op_Names := [op(Op_Names), chuyen(parse(line))] 
	      end if; 
	      line := readline(fd) 
	end do; 
	fclose(fd); 
	return Op_Names; 
end proc:

#Read file Define_Operators.txt
GeometryConicSolver[readDefineOperatorsTXT] := proc (fileName::string) 
	local line, fd, readOpsStruct1, readOpsName, readOpsArgumentAndType, readOpsReturn, readOpsProc, readOpsProperties, Init, opsName, opsArgumentAndType, opsReturn, opsProc, opsProperties, k, argTemp, l;	 
	global Op_Structs; 
	
	l := 0; 
	
	Init := proc () 
		opsName := ""; 
		opsArgumentAndType := [[], []]; 
		opsReturn := []; 
		opsProc := ""; 
		opsProperties := [];
	end proc; #---------------Init
	
	readOpsReturn := proc () 
		local name, type; 
		k := SearchText(":", line); 
		type := substring(line, k+1 .. length(line)); 
		name := parse(substring(line, SearchText("return", line)+6 .. k-1)); 
		opsReturn := [name, type];
	end proc; #-------------readOpsReturn
	
	readOpsName := proc () 
		k := SearchText(":", line); 
		opsName := substring(line, k+1 .. length(line)); 
		argTemp := substring(opsName, SearchText("(", opsName) .. SearchText(")", opsName));
	end proc; #----------------------readOpsName
	
	readOpsArgumentAndType := proc () 
		local argNames1, i; 
		k := SearchText(":", line); 
		argNames1 := [parse(substring(line, 1 .. k-1))]; 
		for i to nops(argNames1) do 
		     opsArgumentAndType[2] := [op(opsArgumentAndType[2]), convert(parse(substring(line, k+1 .. length(line))), string)];
		end do;
		opsArgumentAndType[1] := [op(opsArgumentAndType[1]), op(argNames1)];
	end proc; #------------readOpsArgumentAndType
	
	readOpsProc := proc ()
		line := readline(fd); 
		while line <> 0 and SearchText("end_proc", line) = 0 do 
		     opsProc := cat(opsProc, line); 
		     line := readline(fd);
		end do; 
		opsProc := cat("proc", argTemp, opsProc, "end:");
	end proc;#-------------------readOpsProc
	
	readOpsProperties := proc () 
		local s; line := readline(fd); 
		while line <> 0 and SearchText("end_properties", line) = 0 do
		     s := parse(line); 
		     if evalb(s <> NULL) then 
			  opsProperties := [op(opsProperties), s];
		     end if; 
		     line := readline(fd);
		end do;
	end proc; #----------readOpsProperties
	
	readOpsStruct1 := proc ()
		Init(); 
		line := readline(fd); 
		while line <> 0 and SearchText("begin_operator", line) = 0 do 
		     line := readline(fd);
		     if 0 < SearchText("end_operators", line) then 
			  return;
		     end if;
		end do; 
		while line <> 0 and SearchText("end_operator", line) = 0 do 
		     if 0 < SearchText("begin_operator", line) then 
			  readOpsName() 
		     elif 0 < SearchText("return", line) then 
			  readopsReturn() 
		     elif 0 < SearchText("begin_proc", line) then 
			  readOpsProc() 
		     elif 0 < SearchText("properties", line) then 
			  readOpsProperties();
		     else 
			 if line <> "" then 
			     readOpsArgumentAndType(); 
			 end if; 
		     end if; 
		     line := readline(fd);
		end do; 
		Op_Structs := [op(Op_Structs), [opsName, opsArgumentAndType, opsReturn, opsProc, opsProperties]];
	end proc;#-------------readOpsStruct1
	
	#Main---------------
	fd := fopen(fileName, READ, TEXT); 
	line := readline(fd); 
	Op_Structs := []; 
	while line <> 0 and SearchText("begin_operators", line) = 0 do 
	      line := readline(fd);
	end do; 
	while line <> 0 and SearchText("end_operators", line) = 0 do 
	      readOpsStruct1();
	end do; 
	fclose(fd); 
	return Op_Structs;
end proc:

#Read file Functions.txt
GeometryConicSolver[readFunctionsTXT] := proc (fileName::string) 
	local line, fd, returnz, funcname, arguments, properties, i, k, l,Vitrik; 
	global Func_Names;
	
	Func_Names := []; 
	returnz := ""; 
	funcname := ""; 
	arguments := []; 
	properties := {}; 
	
	fd := fopen(fileName, READ, TEXT); 
		line := readline(fd); 
		while line <> 0 and SearchText("begin_functions", line) = 0 do 
		      line := readline(fd) 
		end do; 
		line := readline(fd); 
		# tim vi tri k khac " " bat dau tu dau chuoi, vd: "  line", k=3 (ngay chu l)
		Vitrik := proc (line) 
		local k, s, n, i; 
		n := length(line); 
		i := 1; 
		while i <= n do s := substring(line, i); 
		    if evalb(s = " ") then 
			i := i+1; 
		    else 
			break 
		    end if;
		end do; 
		return i ;
	end proc; 
	
	while line <> 0 and SearchText("end_functions", line) = 0 do 
	      if line <> "" then 
		    i := Vitrik(line); 
		    l:=SearchText(";", line);
		    k := i-2+SearchText(" ", line, i .. l-1); 
		    returnz := substring(line, i .. k);
		    funcname := convert(parse(substring(line, k+2 .. SearchText("(", line)-1)), string); 
		    arguments := map(s->convert(s, string), [parse(substring(line, SearchText("(", line)+1 .. SearchText(")", line)-1))]);         
		    if(SearchText("{", line) = 0) then
		       properties := {};
		    else
		       properties := parse(substring(line, SearchText("{", line) .. l-1));
		    end if;           
	      
		    Func_Names := [op(Func_Names), [returnz, funcname, arguments, properties]];
	     end if;
	     line := readline(fd);
	end do;
	fclose(fd);
	return Func_Names; 
end proc:

#Read file Define_Functions.txt
GeometryConicSolver[readDefineFunctionsTXT] := proc (fileName::string) 
	local line, fd, readFuncStruct1, readFuncName, readFuncArgumentAndType, readFuncReturn, readFuncProc, readFuncProperties, readFuncConditions, InitFunc, funcName, funcArgumentAndType, funcReturn, funcProc, funcProperties, funcConditions,k, argTemp, l;
	global Func_Structs; 
	l := 0; 
	
	InitFunc := proc () 
		funcName := ""; 
		funcArgumentAndType := [[], []]; funcReturn := []; 
		funcProc := ""; 
		funcProperties := [];
		funcConditions:=[];
	end proc; #--------------Init
	
	readFuncReturn := proc ()
		local name, type; 
		k := SearchText(":", line); 
		type := substring(line, k+1 .. length(line)); 
		name := parse(substring(line, SearchText("return", line)+6 .. k-1)); 
		funcReturn := [name, type];
	end proc; #------------readFuncReturn
	
	readFuncName := proc () 
		k := SearchText(":", line); 
		funcName := substring(line, k+1 .. length(line)); 
		argTemp := substring(funcName, SearchText("(", funcName) .. SearchText(")", funcName))
	end proc; #--------------readFuncName
	
	readFuncArgumentAndType := proc ()
		local argNames1, i; 
		k := SearchText(":", line); 
		argNames1 := [parse(substring(line, 1 .. k-1))]; 
		for i to nops(argNames1) do 
		     funcArgumentAndType[2] := [op(funcArgumentAndType[2]), convert(parse(substring(line, k+1 .. length(line))), string)]; 
		end do; 
		funcArgumentAndType[1] := [op(funcArgumentAndType[1]), op(argNames1)]; 
	end proc;#-----------------readFuncArgumentAndType
	
	readFuncProc := proc () 
		line := readline(fd); 
		while line <> 0 and SearchText("end_proc", line) = 0 do 
		      funcProc := cat(funcProc, line); 
		      line := readline(fd); 
		end do; 
		funcProc := cat("proc", argTemp, funcProc, "end:");
	end proc; #-----------------readFuncProc
	
	readFuncProperties := proc () 
		local s; 
		line := readline(fd); 
		while line <> 0 and SearchText("end_properties", line) = 0 do 
		      s := parse(line); 
		      if evalb(s <> NULL) then 
			    funcProperties := [op(funcProperties), s];
		      end if; 
		      line := readline(fd);
		end do;
	end proc; #----------------readFuncProperties
	
	readFuncConditions := proc ()
		local k;
		k:=SearchText(":", line);
		funcConditions := [ op(funcConditions), parse(substring(line, k+1 .. length(line)))];
	end proc; #-----------------readFuncConditions
	
	readFuncStruct1 := proc ()	
		InitFunc(); 
		line := readline(fd):
		while line <> 0 and SearchText("begin_function", line) = 0 do 
		      line := readline(fd); 
		      if (line =0) or (0 < SearchText("end_functions", line)) then 
			    return;
		      end if;
		end do; 
		while line <> 0 and SearchText("end_function", line) = 0 do 
		     if 0 < SearchText("begin_function", line) then 
			  readFuncName();
		     elif 0 < SearchText("return", line) then 
			  readFuncReturn(); 
		     elif 0 < SearchText("begin_proc", line) then 
			  readFuncProc();
		     elif 0 < SearchText("properties", line) then 
			  readFuncProperties();
		     elif 0 < SearchText("condition:", line) then 
			  readFuncConditions();
		     else 
			  if line <> "" then readFuncArgumentAndType(); end if;
		     end if; 
		     line := readline(fd);
		end do; 
		Func_Structs := [op(Func_Structs), [funcName, funcArgumentAndType, funcReturn, funcProc, funcProperties, funcConditions]];
	end proc; #---------------------readFuncStruct1
	
	#Main---------------
	fd := fopen(fileName, READ, TEXT); 
	line := readline(fd):
	Func_Structs := []; 
	while line <> 0 and SearchText("begin_functions", line) = 0 do 
	      line := readline(fd); 
	end do; 
	while line <> 0 and SearchText("end_functions", line) = 0 do 
	      readFuncStruct1();
	end do; 
	fclose(fd); 
	return Func_Structs ;
end proc:

#Read file <ten cac khai niem CObject>.txt
GeometryConicSolver[ReadCObject] := proc (fileName::string)
	local objectName, baseObject, variables, constraints, constructRelations, properties, computationRelations, rules, functions, result, line, fd, k, Init, readObjectName, readBaseObject, readVariables, readConstraints, readConstructRelations, readProperties, readComputationRelations, readFunctions, readRulesO; 

	Init := proc () 
		objectName := ""; 
		baseObject := [[], []]; 
		variables := [[], []]; 
		constraints := []; 
		constructRelations := []; 
		properties := []; 
		computationRelations := []; 
		rules := []; 
		functions := [] 
	end proc; #-----------------Init

	readObjectName := proc () 
		k := SearchText(":", line); 
		objectName := convert(parse(substring(line, k+1 .. length(line))), string); 
	end proc; #----------readObjectName

	readBaseObject := proc () 
		local temp, i; 
		while line <> 0 and SearchText("begin_variables", line) = 0 do 
		      if line <> "" then k := SearchText(":", line); 
			  temp := [parse(substring(line, 1 .. k-1))]; 
			  for i to nops(temp) do 
			      baseObject[2] := [op(baseObject[2]), convert(parse(substring(line, k+1 .. length(line))), string)] 
			  end do; 
			  baseObject[1] := [op(baseObject[1]), op(temp)]; 
		      end if; 
		line := readline(fd);
		end do;
	end proc; #--------------readBaseObject

	readVariables := proc () 
		local temp, i; 
		line := readline(fd); 
		while line <> 0 and SearchText("end_variables", line) = 0 do 
		      if line <> "" then 
			   k := SearchText(":", line); 
			   temp := [parse(substring(line, 1 .. k-1))]; 
			   for i to nops(temp) do 
				 variables[2] := [op(variables[2]), convert(parse(substring(line, k+1 .. length(line))), string)];
			   end do; 
			   variables[1] := [op(variables[1]), op(temp)]; 
		      end if; 
		      line := readline(fd);
		end do; 
	end proc; #----------------readVariables

	readConstraints := proc () 
		line := readline(fd); 
		while line <> 0 and SearchText("end_constraints", line) = 0 do 
		      if line <> "" then 
			   constraints := [op(constraints), parse(line)];
		      end if; 
		      line := readline(fd);
		end do;
	end proc; #--------------------readConstraints

	readConstructRelations := proc () 
		line := readline(fd); 
		while line <> 0 and SearchText("end_construct_relations", line) = 0 do 
		     if line <> "" then 
			   constructRelations := [op(constructRelations), parse(line)]; 
		     end if; 
		     line := readline(fd);
		end do; 
	end proc; #-----------------readConstructRelations

	readProperties := proc () 
		line := readline(fd); 
		while line <> 0 and SearchText("end_properties", line) = 0 do 
		      if line <> "" then 
			   properties := [op(properties), parse(line)]; 
		      end if; 
		      line := readline(fd);
		end do; 
	end proc; #-------------readProperties
	
	readComputationRelations := proc () 
		local expr, f, readRelation; 
		readRelation := proc () 
			f:=["CompuRela  "]; 
			line := readline(fd); 
			while line <> 0 and SearchText("end_relation", line) = 0 do 
				if line <> "" then 
					expr := rhs(parse(line)); 
					f := [op(f), expr]; 
				end if; 
				line := readline(fd);
			end do; 
			f[6] := parse(f[6]);
		end proc; #---------------readRelation

		f := []; 
		line := readline(fd); 
		while line <> 0 and SearchText("end_computation_relations", line) = 0 do 
		     if 0 < SearchText("begin_relation", line) then 
			   readRelation(); 
			   computationRelations := [op(computationRelations), f]; 
		     end if; 
		     line := readline(fd);
		end do;
	end proc; #-----------readComputationRelations 

	readRulesO := proc ()
		local readRule1, readKindRule, Init, readHypothesis, readGoals, readProcs, readVariables, kindRule, variableNames, variableNames1, variableTypes, hypothesisGoal, procs, k, i; 
		
		Init := proc () 
		     kindRule := ""; 
		     variableNames := []; 
		     variableTypes := []; 
		     hypothesisGoal := [{}, {}]; 
		     procs := [];
		end proc;#-------------Init 
	
		readKindRule := proc () 
		     kindRule := rhs(parse(line)) 
		end proc; #-----------readKindRule
	     
		readHypothesis := proc () 
			line := readline(fd); 
			while line <> 0 and SearchText("end_hypothesis_part", line) = 0 do 
				hypothesisGoal[1] := parse(line); 
				line := readline(fd);
			end do;
		end proc;
     
		readGoals := proc ()
			line := readline(fd); 

			while line <> 0 and SearchText("end_goal_part", line) = 0 do 
				hypothesisGoal[2] := parse(line);
				line := readline(fd);
			end do;
		end proc; 

		readProcs := proc () 
			k := SearchText(":", line); 
			procs := [op(procs), parse(substring(line, k+1 .. length(line)))];
		end proc; 
		
		readVariables := proc () 
			k := SearchText(":", line); 
			variableNames1 := [parse(substring(line, 1 .. k-1))]; 
			for i to nops(variableNames1) do 
				variableTypes := [op(variableTypes), convert(parse(substring(line, k+1 .. length(line))), string)];
			end do; 
			variableNames := [op(variableNames), op(variableNames1)];
		end proc; 

		readRule1 := proc () 
			Init(); 
			
			while line <> 0 and SearchText("begin_rule", line) = 0 do 
				if 0 < SearchText("end_rules", line) then 
					return;
				end if; 
				line := readline(fd); 
			end do; 
			line := readline(fd);
			while line <> 0 and SearchText("end_rule", line) = 0 do
				if 0 < SearchText("kind_rule", line) then 
					readKindRule();
				elif 0 < SearchText("hypothesis_part", line) then 
					readHypothesis();
				elif 0 < SearchText("goal_part", line) then 
					readGoals(); 
				elif 0 < SearchText("proc:", line) then 
					readProcs() 
				else 
					if line <> "" then readVariables() end if;
				end if;
				
				line := readline(fd) 
			end do; 
			
			rules := [op(rules), [kindRule, variableNames, variableTypes, hypothesisGoal, procs]];
		end proc; #-------------------readRule1
			
		line := readline(fd);
		while line <> 0 and SearchText("end_rules", line) = 0 do
			readRule1();
		end do;
	end proc; 

	readFunctions := proc ()
		line := readline(fd); 
		while line <> 0 and SearchText("end_functions", line) = 0 do 
		      if line <> "" then 
			   functions := [op(functions), parse(line)];
		      end if; 
		      line := readline(fd);
		end do;
	end proc; #-----readFunctions

	#Main-----------------
	Init(); 
	result := []; 
	fd := fopen(fileName, READ, TEXT); 
	line := readline(fd); 
	while line <> 0 and SearchText("begin_object", line) = 0 do 
	     line := readline(fd);
	end do;
	
	while line <> 0 and SearchText("end_object", line) = 0 do 
	     if 0 < SearchText("begin_object", line) then 
		   readObjectName(); 
		   line := readline(fd); 
		   readBaseObject(); 
		   next;
	      elif 0 < SearchText("begin_variables", line) then 
		   readVariables(); 
	      elif 0 < SearchText("begin_constraints", line) then 
		   readConstraints(); 
	      elif 0 < SearchText("begin_construct_relations", line) then 
		   readConstructRelations();
	      elif 0 < SearchText("begin_properties", line) then 
		   readProperties(); 
	      elif 0 < SearchText("begin_functions", line) then 
		   readFunctions();
	      elif 0 < SearchText("begin_computation_relations", line) then 
		   readComputationRelations();
	      elif 0 < SearchText("begin_rules", line) then
		   readRulesO(); 
	      end if; 
	      line := readline(fd);
	end do; 
	fclose(fd); 
	result := [objectName, baseObject, variables, constraints, constructRelations, properties, computationRelations, rules, functions];
	return result; 
end proc:

# Function to display object information by object name
GeometryConicSolver[ObjStruct] := proc (objName::string, s) 
	global Obj_Structs, url;
	local i,flag;flag:=0;
	for i from 1 to nops(Obj_Structs) do
		if evalb(Obj_Structs[i][1]=objName) then
			flag:=1;break;
		fi;
	od;
	if(flag=0)then return(NULL);fi;
	if  nargs = 2 and s = "reset"  then  Obj_Structs[i][2] := [];  return (NULL);  fi;
	if Obj_Structs[i][2] = [] then
		Obj_Structs[i][2]:= ReadCObject(cat(url,"/data/Objects/",objName,".txt"));
	fi;
	return(Obj_Structs[i][2]);
end proc:
