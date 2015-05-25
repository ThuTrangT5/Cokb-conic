#Giải bài toán
	#Test_Goal, 
	#Output_Result, 
	#Determine, 
	#Determine_Goal, 
	#Determine_Goals, 
	#Determine_Param
	#Deduce_Objects
# Sol : lời giải ban đầu
# OptimizeSol : lời giải đã rút gọn

GeometryConicSolver[Deduce_Objects]:=proc()
	local i,k,j;
	global Fact_Kinds;
	
	for i from 1 to nops(Objects) do
		if isPrint= true then print("7.0 - Deduce_Objects : ",Objects[i]); 
		fi;
		Deduce_Object(Objects[i]);
		if flag and Test_Goal(Goal,FactSet) then next;fi;
	od;
	return [Fact_Kinds,Sol]; 
end proc: # Deduce_Objects

#Deduce_Object
GeometryConicSolver[Deduce_Object]:=proc(d)
	local ObjStructTemp,thaythe,FK2,FK3,FK45,Deduce_ObjRules,Deduce_ObjProp,Deduce_OConstructRela,Deduce_ObjRela1,Deduce_ObjRela21,Deduce_ObjRela22,Deduce_ObjRela3,Deduce_ObjFunc;
	global Fact_Kinds,FactSet,Sol,flag,TestOR,TestOCR,TestProp;
	
	if isPrint= true then lprint("*Deduce_Object"); fi;
	if (type_Onet(d) = "Real")then return; fi;
	
	ObjStructTemp:= ObjStruct_Replace(d);	
	thaythe := Find_VarUnify({op(Fact_Kinds[2])});
	
	FK2 := Replace_StructName(subs(thaythe,{op(Fact_Kinds[2])}));	
	FK3 := Replace_StructName(subs(thaythe,{op(Fact_Kinds[3])}));
	FK45:= Replace_StructName(subs(thaythe,{op(Fact_Kinds[4]),op(Fact_Kinds[5])}));

	Deduce_ObjProp:=proc()
		local prop,k,news;
		if isPrint= true then print("7.1--Deduce_ObjProp ");
		fi;
		news:={};
		for prop in ObjStructTemp[6] do 
			k:=Kind_Fact(prop);
			#printf("kind fact => ");#printf(k);
			if k>=1 and k<=11 and not Unify_In1(prop,Fact_Kind[k]) then
				news:={op(news),prop};
				Fact_Kinds[k] :=[op(Fact_Kinds[k]),prop];
			fi;
		od;
		
		if news<>{} then 
			FactSet:=FactSet union news; 
			Sol:=[op(Sol),["Deduce_ObjProp",[],{},news]];
			if isPrint= true then print("go to 1 : TestProp = ",TestProp);
			fi;
			TestProp:={op(TestProp),d};
		fi;
	end:#Deduce_ObjProp

	Deduce_OConstructRela:=proc()
		local i,f,expr,the,k,vars;
		
		the:={};
		#if isPrint= true then 
		#print("7.2--Deduce_OConstructRela");
		#fi;
		for f in ObjStructTemp[5] do
			if member([d,f],TestOCR) then next;fi; 
			vars:=Set_Vars(f);
			for i in vars do
				if type(i,function)and op(0,i)<>`.` then
				vars:=vars minus {i} union Set_Vars(op(i));
				fi;
			od;
			for i in vars do
				if type(i,function)and op(0,i)=`.` 
				and member(op(1,i),ObjStructTemp[2][1],'k')
				and type(parse(ObjStruct(ObjStructTemp[2][2][k])[1]),indexed) 
				and member(op(1,i),FK2)then 
					if op(2,i)=x then 
						the:={op(the),i=Get_Values(op(1,i))[1]};
					elif op(2,i)=y then 
						the:={op(the),i=Get_Values(op(1,i))[2]};
					fi; 
				elif type(i,function)and op(0,i)=`.` and member(i,ObjStructTemp[2][1],'k') and member(i,FK2)then 
					if op(2,i)=x then
						the:={op(the),i=Get_Values(i)};
					elif op(2,i)=y then
						the:={op(the),i=Get_Values(i)};
					fi; 
				fi;
			od;
		
			if the <> {} then 
				expr:=subs(the,f);
				
				if Set_Vars(rhs(expr)) = {} then 
					k := Kind_Fact(expr);
					if k>=1 and k<=11 and not Unify_In1(expr,FactSet) then
						Fact_Kinds[k] :=[op(Fact_Kinds[k]),expr];
						FactSet:=FactSet union {expr};
						Sol:=[op(Sol),["Deduce_OConstructRela",[f],the,{expr}]]; 
						TestOCR:= TestOCR union {[d,f]}; 
						flag:=true; 
					fi; 
				fi; 
			fi;
		od;
	end:#Deduce_OConstructRela

	Deduce_ObjRela1:=proc()
		local f,vars,fact,expr,news,ex,k;
		if isPrint= true then print("7.3--Deduce_ObjRela1 ");
		fi;
		
		for f in ObjStructTemp[7] do 
			if member([d,f],TestOCR) then next;fi; 
			vars:=`minus`(f[3],FK2);
			if (f[2]=1 and nops(vars)=1) or (f[2]=0 and vars=f[5]) then 
				expr:=subs(FK3,f[6]);
				news:=MySolve(expr,vars,1);
				#news co the la {}, hay co nhieu nghiem nhu {{a=1,b=3},{a=2,b=4}}.Neu co nhieu nghiem thi chon 1 nghiem ngau nhien....VIET LAI SAU
				if news<>{}then
					TestOCR:= TestOCR union {[d,f]}; 
					for ex in news[1] do 
						k := Kind_Fact(ex);
						if k>=1 and k<=11 and evalb(ex) = false and not Unify_In1(ex,FactSet) then
							Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
							FactSet:=FactSet union {ex}; 
						fi;
					od; 
					if (thaythe={}) then 
						thaythe:={op(f[3]),f[6]};
					fi; 
					Sol:=[op(Sol),["Deduce_ObjRela1",f,thaythe,news[1]]];
					flag:=true;					
				fi; 
			fi;
		od; 
	end: # Deduce_ObjRela1

	Deduce_ObjRela21:=proc()
		local f,vars,fact,expr,news,ex,k;
		if isPrint= true then print("7.4--Deduce_ObjRela21 ");
		fi;
		
		for f in ObjStructTemp[7] do 
			if member([d,f],TestOCR) then next;fi; 
			vars:=`minus`(f[3],FK2);
			if nops(vars)=2 then
				for fact in FK45 minus DF53 minus DF43 do
					if `minus`(Set_Vars(fact),FK2) = vars then 
						expr:=subs(FK3,{f[6],fact});
						news:={}; 
						if nops(expr)=2 then news:=MySolve(expr,vars,1);fi; 
						if news<>{}then 
							TestOCR:= TestOCR union {[d,f]}; 
							for ex in news[1] do 
								k := Kind_Fact(ex);
								if k>=1 and k<=11 and evalb(ex) = false and not Unify_In1(ex,FactSet) then
									Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
									FactSet:=FactSet union {ex}; 
								fi;
							od; 
							Sol:=[op(Sol),["Deduce_ObjRela21",[f,fact],{},news[1]]];
							flag:=true; 
						fi; 
					fi;
				od;
			fi;
		od;
	end:#Deduce_ObjRela21

	Deduce_ObjRela22:=proc()
		local f,vars,vars1,vars2,fact,fact1,fact2,expr,news,ex,k;
		
		for f in ObjStructTemp[7] do 
			if member([d,f],TestOCR) then next;fi; 
			vars:=`minus`(f[3],FK2);
			
			if nops(vars)=3 then 
				for fact in combinat[choose](FK45 minus DF53 minus DF43 ,2) do 
					fact1:=fact[1];
					fact2:=fact[2];
					vars1:=`minus`(Set_Vars(fact1),FK2);
					vars2:=`minus`(Set_Vars(fact2),FK2);
					
					if Unify_In1(vars1,vars) and nops(vars1)>1 and Unify_In1(vars2,vars) and nops(vars2)>1 then
						expr:=subs(FK3,{f[6],fact1,fact2});
						news:={}; 
						if nops(expr)=3 then news:=MySolve(expr,vars,1);fi; 
						if news<>{}then 
							TestOCR:= TestOCR union {[d,f]}; 
							for ex in news[1] do              
								k := Kind_Fact(ex);
								if k>=1 and k<=11 and evalb(ex)= false and not Unify_In1(ex,FactSet) then
									Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
									FactSet:=FactSet union {ex};
								fi;
							od; 
							Sol:=[op(Sol),["Deduce_ObjRela22",[f,fact],{},news[1]]];
							flag:=true; 
						fi; 
					fi;
				od;
			fi;
		od;
	end:#Deduce_ObjRela22
		
	Deduce_ObjRela3:=proc()
		local f,vars,expr,expr1,news,ex,k,fact;
		if isPrint= true then print("7.6--Deduce_ObjRela3 chua xu ly xong !!! ");
		fi;
		(*
		for f in ObjStructTemp[7] do 
			if member([d,f],TestOCR) then next;fi; 
			expr:=subs(FK3,f[6]);
			
			#Để tạo sự kiện mới có ít biến hơn thì phải có biến trong f[6] đã đc xác định, tức là thuộc FK3
			if expr = f[6] then next; fi;
			
			for fact in FK45 minus DF53 minus DF43 do
				# tìm các biến có trong f
				varf := f[3];
				# tìm các biến có trong sự kiện loại 4,5 
				varFact := Set_Vars(fact);
				varsUnion := varf intersect varFact;
				
				if nops(varsUnion) > 0 then
					news:=subs(expr,fact);
					varNews := Set_Vars(news);
										
					if nops(varNews) < nops(varFact) then
					
						TestOCR:= TestOCR union {[d,f]}; 
						for ex in news do              
							k := Kind_Fact(ex);
							if k>=1 and k<=11 and evalb(ex)= false and not Unify_In1(ex,FactSet) then
								Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
								FactSet:=FactSet union {ex};
							fi;
						od;
						
						Sol:=[op(Sol),["Deduce_ObjRela3",[f,fact],{},news]];
						flag:=true; 
					fi;
				fi;
			od;
		od;*)
	end:#Deduce_ObjRela3
		
	Deduce_ObjFunc:=proc()
		#???
	end:#Deduce_ObjFunc
				
	Deduce_ObjRules := proc()
		local rule,news,ex,k,trihp,hamphu, phu, objRules, checkMember;
		global temp;
		if isPrint= true then print("7.8--Deduce_ObjRules");
		fi;
		
		
		# hamphu: tính giá trị các goals theo các procs của object rules
		hamphu:=proc()
			local h,tt,doi,j,s, i, return_;
			global DF3;
			 
			return_:={};
			# rule[5] là thành phần proc của object's rule
			for i in rule[5] do
				if not type(i,`=`) then
					tt:=op(0,i);
					doi:=op(i);
					phu:= parse(convert(tt(op(doi)),string));
				else
					tt:=op(0,rhs(i));
					doi:=[op(rhs(i))];
					
					for j to nops(doi) do
						s:= Unify_In1(doi[j],[op(Fact_Kinds[2]),op(Fact_Kinds[7])]);
						if(s <>-1)then doi[j]:=op(Get_Values([doi[j]]));fi;
					od;
					h:= parse(cat(convert(lhs(i),string), "=(",convert(tt(op(doi)),string),")"));
					k:= Kind_Fact(h);
					if k=3 and not Unify_In1(h,FactSet)then 
						Fact_Kinds[k] :=[op(Fact_Kinds[k]),h];
						if not Unify_In1(lhs(h),FactSet) then 
							Fact_Kinds[2]:=[op(Fact_Kinds[2]),lhs(h)];
						fi;
						DF3:=DF3 union {h};
						FactSet:=FactSet union {h,lhs(h)};
						return_:={op(return_),h,lhs(h)};
					fi;
				fi;
			od;
			return return_;
		end:#hamphu
		
		# Deduce_ObjecRules BODY
		if isPrint = true then 
			#lprint("BEGIN Deduce_ObjRules");
			#print("TestOR = ",TestOR);
			#printf("ObjStructTemp[8] = ");
			#print(ObjStructTemp[8]);
		fi;
				
		#flag := false; #Them moi => dang check
		objRules := OrderRulesByGoals(ObjStructTemp[8]); # Trang them moi
		
		#lprint("===> objRules ORDER :");
		#print(objRules);
				
		#for rule in ObjStructTemp[8] do
		for rule in objRules do
		
			#if member([d,rule],TestOR) then next;fi;
			checkMember := {};
			checkMember := {[d,rule]} intersect {op(TestOR)}; #member([d,rule],TestOR);
			if checkMember <> {} then
				next;
			(*else 
				print("NEW =>", [d,rule]);
				print("TestOR => ",TestOR);
				print("checkMember1 = ", checkMember);
				print("checkMember2 = ", member([d,rule],TestOR));*)
			fi;
			
			news := ApplyRule(rule,FactSet);
			if news<>{}then
				if isPrint= true then 
					print("ApplyRule rule = ",rule);
					print("ApplyRule rule => get news = ",news);
					print("Test OR = ", TestOR);
				fi;
			
				TestOR := TestOR union {[d,rule]};
				for ex in news do
					k := Kind_Fact(ex);
					if k>=1 and k<=11 and not Unify_In1(ex,FactSet) then
						Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
						FactSet:=FactSet union {ex};
					fi;
				od;
				trihp:={}; 
				if(rule[5]<>[]) then 
					trihp:=hamphu();
				fi; 
		
				Sol:=[op(Sol),["Deduce_ObjRules",rule,rule[4][1],news union trihp]];
				flag:=true;
				
				#print("new Sol = ", ["Deduce_ObjRules",rule,rule[4][1],news union trihp]);
				#print("flag = ", flag);

			fi;
		od;
	end: #Deduce_ObjRules
	#trace(Deduce_ObjRules);

	#Deduce_Objects BODY
	#BUOC 1 -----------------------------------
	#Do tim cac tinh chat ben trong cau truc doi tuong
	if isPrint= true then lprint("Deduce_Object's body => buoc 1");
	fi;
	if not member(d,TestProp) then 
		Deduce_ObjProp();
		if flag and Test_Goal(Goal,FactSet) then return;fi;
	fi; 
	
	#-BUOC 2 -----------------------------------
	#do tim luat suy dien co the ap dung dc ben trong cau truc doi tuong
	if isPrint= true then lprint("Deduce_Object's body => buoc 2");
	fi;
	Deduce_ObjRules();
	if flag and Test_Goal(Goal,FactSet) then return;fi;
	
	#-BUOC 3 ------------------------------
	#thuc hien tinh toan cac quan he tren cau truc thiet lap
	#if isPrint= true then 
	#lprint("Deduce_Object's body => buoc 3");
	#fi;
	Deduce_OConstructRela();
	if flag and Test_Goal(Goal,FactSet) then return;fi; 
	
	#-BUOC 4 -----------------------------------
	if isPrint= true then lprint("Deduce_Object's body => buoc 4");
	fi;
	#ap dung qui tac 1: ap dung 1 quan he tinh toan f bang cach the vao f cac sk loai 2,3 de sinh ra sk 2,3.DK:f co dung 1 bien ko co mat trong tap sk2. 
	Deduce_ObjRela1();
	if flag and Test_Goal(Goal,FactSet) then return;fi;
	
	#-BUOC 5 -----------------------------------
	#ap dung qui tac 2: ap dung nhung quan he f chua 2 bien ko nam trong Fact_Kinds[2] co kha nang ket hop voi 1 su kien loai 4,5 cung co 2 bien nhu tren de giai ra sk moi loai 2,3
	if isPrint= true then 
		lprint("Deduce_Object's body => buoc 5");
	fi;
	Deduce_ObjRela21();
	if flag and Test_Goal(Goal,FactSet) then return;fi;
	
	#-BUOC 6 -----------------------------------
	#nhu buoc 4 .ap dung nhung quan he f thoa chua 3 bien ko nam trong Fact_Kinds[2] co kha nang ket hop voi 2 sk 4,5 cung co
	if isPrint= true then lprint("Deduce_Object's body => buoc 6");
	fi;
	Deduce_ObjRela22();
	if flag and Test_Goal(Goal,FactSet) then return;fi;
	
	#-BUOC 7 -----------------------------------
	# ap dung qui tac 3:ap dung 1 quan he tinh toan f tren sk loai 3,2 bang cach thay the mot bien trong f ma co mat trong su kien loai 3 de tao ra sk moi co so bien it hon.
	if isPrint= true then lprint("Deduce_Object's body => buoc 7");
	fi;      
	#Deduce_ObjRela3();
	#if flag and Test_Goal(Goal,FactSet) then return;fi; 

end proc: # Deduce_Object

#ODeduce_From3s : Deduce_From3 & Deduce_From3s 
#Deduce_From3 : sinh 1 sk2 tu 1 sk3. 
#Neu nhieu sk3 cung sinh mot sk2 thi se gom chung vao mot buoc giai trong Sol. 
#Vi du: {a = 2, a =3} cung sinh ra {a} nen ta co ["Deduce_From3s",[],{a = 2, a =3}, {a}].
GeometryConicSolver[Deduce_From3]:=proc(fact3)
	local fact2,i,attValues,Otype,atts,oValues,oStruct,attTypes;
	global Fact_Kinds, FactSet, Sol, flag, OAttrs,OAttr_Types,TEST_DF3;
	
	fact2:=lhs(fact3);
	if not Unify_In1(fact2, Fact_Kinds[2]) then 
		Fact_Kinds[2]:=[op(Fact_Kinds[2]),fact2];
		FactSet:=FactSet union {fact2};
		
		# xác định luôn giá trị của các thuộc tính cơ bản của đối tượng, đặc biệt là Diem
		Otype := type_Onet(fact2);
		attValues := [];
		
		#Trường hợp đối tượng đang xét là Diem hoặc Vecto (không xét Vecto cho dạng Conic)
		if Otype = "Diem" then
			oStruct := ObjStruct(Otype);
			atts := oStruct[2][1];
			attTypes := oStruct[2][2];
			atts := [seq(rhs(atts[i]=fact2.atts[i]), i=1..nops(atts))];
			oValues := rhs(fact3);
			attValues := seq(atts[i] = oValues[i], i=1..nops(atts));
		fi;

		Sol:=[op(Sol),["Deduce_From3s",[],{fact3},{fact2}]];
		if (attValues<>[]) then
			if not Unify_In1({attValues}, Fact_Kinds[3]) then
				Sol:=[op(Sol),["Deduce_From3s",[],{fact3},{attValues}]];
				Fact_Kinds[3] := [op({op(Fact_Kinds[3])} union {attValues})];
				OAttrs := [op(OAttrs),op(atts)];
				OAttr_Types := [op(OAttr_Types),op(attTypes)] ;
			fi;
		fi;
	else
		for i to nops(Sol) do
			if Sol[i][1] = "Deduce_From3s" and Sol[i][4] = {fact2} then
				Sol[i][3]:= Sol[i][3] union {fact3};
			fi;
		od; 
	fi; 
	flag:= true; 
end proc: # Deduce_From3

#Deduce_From3s : Sinh cac sk2 tu cac sk3
GeometryConicSolver[Deduce_From3s]:=proc()
	local fact3;
	global Fact_Kinds, DF3; 
	

	for fact3 in Fact_Kinds[3] do
		if not member(fact3, DF3) then
			Deduce_From3(fact3);
			DF3:= DF3 union {fact3};
		fi;
	od;
	if isPrint = true then
		#printf("==> END Deduce 3s");
		#print(Fact_Kinds);
	fi;
	return [Fact_Kinds,Sol];
end proc: # Deduce_From3s

#Deduce_From8s : sinh 1 sk7 tu 1 sk8
#Neu co nhieu sk8 cung sinh mot sk7 thi se gom chung vao mot buoc giai trong Sol. 
#Vi du: {VECTO(A,B) = [2,3], VECTO(A,B) =[4,5]} cung sinh ra {VECTO(A,B)} nen ta co ["Deduce_From8s",[],{VECTO(A,B) = [2,3], VECTO(A,B) =[4,5]}, {VECTO(A,B)}].
GeometryConicSolver[Deduce_From8]:=proc(fact8)
	local fact7,i;
	global Fact_Kinds, FactSet,Sol,flag;
	
	fact7:=lhs(fact8);
	if not Unify_In1(fact7, Fact_Kinds[7]) then 
		Fact_Kinds[7]:=[op(Fact_Kinds[7]),fact7];
		FactSet:=FactSet union {fact7}; 
		Sol:=[op(Sol),["Deduce_From8s",[],{fact8},{fact7}]];
	else
		for i to nops(Sol) do
			if Sol[i][1] = "Deduce_From8s" and Sol[i][4] = {fact7} then
				Sol[i][3]:= Sol[i][3] union {fact8};
			fi;
		od; 
	fi; 
	flag:=true; 
end proc: # Deduce_From8

#Deduce_From8s : Sinh cac sk7 tu cac sk8
GeometryConicSolver[Deduce_From8s]:=proc()
	local fact8;
	global Fact_Kinds, DF8; 
	
	for fact8 in Fact_Kinds[8] do
		if not member(fact8,DF8) then
			Deduce_From8(fact8);
			DF8:= DF8 union {fact8};
		fi;
	od;
	return [Fact_Kinds,Sol];
end proc: # Deduce_From8s

#Deduce_From53s :suy ra su kien moi loai 3, 4, 5 tu 1 su kien 5 va nhieu su kien 3 bang cach the cac su kien 3 vao su kien 5
GeometryConicSolver[Deduce_From53s]:=proc()
	local fact5,fact3,news, vars5,f, k,f3,numOfNewsVars, fact3vars,i;
	global Fact_Kinds,FactSet,Sol,flag,DF53;
	
	f3:=[];
	fact3vars := [seq(lhs(i), i in Fact_Kinds[3])];
	Obj_Attrs := [op(Objects),op(OAttrs)];
	Obj_Attr_Types := [op(Obj_Types), op(OAttr_Types)];

	for fact5 in Fact_Kinds[5] do
		if member(fact5,DF53) then next;fi;
		if(type(rhs(fact5),`=`)) then
			news := rhs(fact5);
		else
			news:=lhs(fact5)-rhs(fact5)=0;
		fi;
		vars5:= Set_Vars(fact5);		
		
		for f in vars5 do
			i :='i';
			if(member(f,fact3vars,`i`)) then (*=> code cũ : if Unify_Fact(lhs(fact3), f) then*)
				fact3 := Fact_Kinds[3][i];
								
				i :='i';
				#Không xét những trường hợp là Điểm nhưng vẫn xét TH thay thế tọa độ x,y của Điểm
				if member(lhs(fact3), Obj_Attrs,`i`) then
					lprint("i2=",i);
					if (Obj_Attr_Types[i] = "Diem") then next; fi;				
				fi;
				#i :='i';
				news:= subs(f = rhs(fact3),news);		
				f3:=[op(f3),fact3];
			fi;
		od;

		numOfNewsVars := nops(Set_Vars(news));
		if numOfNewsVars = 0 then
			news:= lhs(fact5) = news;
			numOfNewsVars := numOfNewsVars+1;
		elif numOfNewsVars = 1 then
			news:=MySolve(news,Set_Vars(news),1)[1][1];	
		fi;
		if numOfNewsVars < nops(vars5) then
			DF53:= DF53 union {fact5};
			k := Kind_Fact(news);
			if k>=1 and k<=11 and not Unify_In1(news,FactSet) then
				Fact_Kinds[k]:= [op(Fact_Kinds[k]),news];
				FactSet:= FactSet union {news};
				Sol:=[op(Sol),["Deduce_From53s",[],{fact5,op(f3)},{news}]];
				flag:= true;
			fi;
		fi;
	od;
end proc: # Deduce_From5s3s

# Deduce_From45s & Deduce_From45
GeometryConicSolver[Deduce_From45] := proc(fact5)
	global Fact_Kinds,Sol,OAttrs, flag,DF45, TEST_45;
	local vars,kq,f,fact4s,fact3s,i,fact4OK,fAtts,temp,typeAtts;

	vars := Set_Vars(fact5);
	kq := lhs(fact5)- rhs(fact5);
	typeAtts := [];
	fact4s := Fact_Kinds[4];
	fact4OK :={};
	
	for f in fact4s do
		if member(lhs(f),vars) then
			kq := subs(f,kq);
			fact4OK := fact4OK union {f};
		fi;
	od;
	# k tìm được sự kiện loại 4 thõa fact5 
	if (fact4OK ={})then return fi; 
	
	fact3s :={};
	if (whattype(kq)=`list`) then
		for i in kq do
			vars := Set_Vars(i);
			f := solve({i = 0},vars);
			fact3s := fact3s union f;
		od; 
	else
		f := solve(kq = 0,vars);
		fact3s := fact3s union f;
	fi;

	# Kiểm tra tính xác định của đối tượng hay thuộc tính
	kq := f;
	f := {seq(op(1,lhs(fact3s[i])), i=1..nops(fact3s))};
	if (nops(f) = 1) then # kiểm tra đối tượng đã đc xác định chưa
		vars := Set_Vars(fact3s);
		fAtts := ObjStruct_Replace((f[1]));
		
		if (vars = {op(fAtts[2][1])} ) then
			temp :=f[1] = subs(fact3s,fAtts[2][1]);
			Sol :=[op(Sol), ["Deduce_From45",[],fact4OK union {fact5},{temp}]];
		if not Unify_In1(temp,Fact_Kinds[3])then
			Fact_Kinds[3] := [op(Fact_Kinds[3]), temp];
		fi;
	fi;
	else # chỉ có thuộc tính của đối tượng được xác định
		Sol :=[op(Sol), ["Deduce_From45",[],fact4OK union {fact5},{kq}]]; 
		if not Unify_In1(kq,Fact_Kinds[3])then
			Fact_Kinds[3] := [op(Fact_Kinds[3]), kq];
		fi;
		OAttrs := [{op(OAttrs)}union Set_Vars(kq) ];
		# chưa làm type của OAtts; !!!
	fi;
	
	flag :=true;
	DF45:= DF45 union {fact5};
end proc: #Deduce_From45

#Deduce_From45s
GeometryConicSolver[Deduce_From45s] := proc()
	global Fact_Kinds,DF45;
	local fact5,fact5s;

	fact5s := Fact_Kinds[5];
	if nops(Fact_Kinds[4])>0 then
		for fact5 in fact5s do
			if not member(fact5, DF45) then
				Deduce_From45(fact5);
print("Loai 5 = ", Fact_Kinds[5]);				
			fi;
		od;
	fi;
end proc: #Deduce_From45s

#Deduce_From43s : sinh sk3s tu sk4s va sk3s bang cach the sk3s vao sk4s
GeometryConicSolver[Deduce_From43s]:=proc()
	local fact4,fact3,news,k, f3, i, f4;
	global Fact_Kinds, DF43, flag, FactSet, Sol, TEST_43s;

	news:={};
	for fact4 in Fact_Kinds[4] do
		if member(fact4,DF43) then next;fi; 
		f3:={};
		for fact3 in Fact_Kinds[3] do 
			if type(rhs(fact4),list) then
				news:={};
				if lhs(fact4)=lhs(fact3) then break; fi; 
				if member(lhs(fact3), Set_Vars(rhs(fact4))) then
					f3:={op(f3),fact3};
				fi; 
			else
				news:={};
				if Unify_Fact(lhs(fact3), lhs(fact4)) then
					news:={subs(lhs(fact3) = rhs(fact4),fact3)}; 
				elif Unify_Fact(lhs(fact3), rhs(fact4)) then
					news:={subs(lhs(fact3) = lhs(fact4),fact3)};
				fi;
				if news <> {} then
					DF43:= DF43 union {fact4};
					k := Kind_Fact(news[1]);
					if k>=1 and k<=11 and not Unify_In1(news[1],FactSet) then
						Fact_Kinds[k]:= [op(Fact_Kinds[k]),op(news)]; 
						FactSet:= FactSet union news; 
						Sol:=[op(Sol),["Deduce_From43s",[],{fact4,fact3},news]]; 
						flag:= true; 
						break;
					fi; 
				fi; 
			fi;
		od; 

		if type(rhs(fact4),list) then
			# chỉ với trường hợp fact4:=a=[1-D.x,1-D.y]; , chỉ có 2 biến cần tính D.x, D.y
			if lhs(fact4)=lhs(fact3) then 
				DF43:= DF43 union {fact4};
				TEST_43s:=[op(TEST_43s),"vao"];
				news:=solve({rhs(fact4)[1]=rhs(fact3)[1], rhs(fact4)[2]=rhs(fact3)[2]},{ op(Set_Vars(rhs(fact4)[1])), op(Set_Vars(rhs(fact4)[2])) }); 
				for i from 1 to nops(news) do 
					k := Kind_Fact(news[i]);
					if k>=1 and k<=11 and not Unify_In1(news[i],FactSet) then
						Fact_Kinds[k]:= [op(Fact_Kinds[k]),news[i]]; 
						FactSet:= FactSet union {news[i]}; 
						Sol:=[op(Sol),["Deduce_From43s",[],{fact4,fact3},{news[i]}]]; 
						flag:= true; 
					fi; 
				od;
				break;
			elif f3 <> {} then
				DF43:= DF43 union {fact4};
				f4:=fact4;
				
				for i in f3 do
					f4:=subs(i,f4);
				od;
				
				news:={f4}; 
				for i from 1 to nops(news) do 
					k := Kind_Fact(news[i]);
					if k>=1 and k<=11 and not Unify_In1(news[i],FactSet) then
						Fact_Kinds[k]:= [op(Fact_Kinds[k]),news[i]]; 
						FactSet:= FactSet union {news[i]}; 
						Sol:=[op(Sol),["Deduce_From43s",[],{fact4,op(f3)},{news[i]}]]; 
						flag:= true; 
					fi; 
				od;
			fi;
		fi; 
	od; 
	
	return [Fact_Kinds,Sol];
end: # Deduce_From43s

#Deduce_From9s : Deduce_From9 (xử lý 1 sk loại 9) & Deduce_From9s (xử lý nhiều sk9) 
GeometryConicSolver[Deduce_From9]:=proc(fact9)
	local Values, i, func,k, funcstruct,facts,Set,hasFunc,notTested;
	global Fact_Kinds,TestF,Sol;
	
	if isPrint= true then 
		#print("8.1-- vao Deduce_From9");
		#print("fact9 = ", fact9);
	fi;
	
	Values:= Get_Values([op(rhs(fact9))]);
	func:=type_Onet(rhs(fact9));
	hasFunc := evalb(convert(func, string) <> "type?");
	notTested := not member([func,[op(rhs(fact9))]],TestF);
		
	if hasFunc and notTested then
		funcstruct:=Find_FuncStruct(func);
		facts:= Compute_Func(funcstruct,[op(rhs(fact9))],Values,lhs(fact9));
		TestF:=TestF union {[func,[op(rhs(fact9))]]};
		Set:=Classify_Facts([op(facts)]);
		Sol:=[op(Sol),["Deduce_From9",[func],{fact9, op(rhs(fact9))},Set]]; 
	fi;
end proc: # Deduce_From9

#xu ly cac su kien loai 9: "doituong = ham" bang cach tinh toan ham
GeometryConicSolver[Deduce_From9s]:=proc()
	local fact9;
	global Fact_Kinds, DF9;
	
	for fact9 in Fact_Kinds[9] do
		if not member(fact9,DF9) and SubList([op(rhs(fact9))] ,Fact_Kinds[2]) then
			Deduce_From9(fact9);
			DF9:= DF9 union {fact9};
		fi;
	od;
	return [Fact_Kinds,Sol] ;
end: # Deduce_From9s

#Deduce_From983s : tu cac sk loai 3(sk loai 8) va sk loai9 sinh ra sk moi bang cach the sk loai 3(hay sk8) vao sk loai 9
GeometryConicSolver[Deduce_From983s]:=proc()
	local fact9, temp, fact3,fact8;
	global Fact_Kinds, flag, FactSet, Sol, DF9; 
	
	for fact9 in Fact_Kinds[9] do 
		if not member(fact9,DF9) then
			for fact3 in Fact_Kinds[3] do
				if Unify_Fact(lhs(fact9), lhs(fact3)) and not Unify_Fact(rhs(fact9),Fact_Kinds[8])then 
					temp:= subs(lhs(fact3) = rhs(fact9), fact3);
					Fact_Kinds[8]:= [op(Fact_Kinds[8]),temp]; 
					FactSet:= FactSet union {temp}; 
					Sol:=[op(Sol),["deduce 983",[],{fact9,fact3},{temp}]];
					DF9:= DF9 union {fact9} ;
					flag:= true; 
					break;
				fi; 
			od; 
			if not member(fact9,DF9) then
				for fact8 in Fact_Kinds[8] do
					if Unify_Fact(rhs(fact9), lhs(fact8)) and not Unify_Fact(lhs(fact9),Fact_Kinds[3]) then 
						temp:= subs(lhs(fact8) = lhs(fact9), fact8);
						Fact_Kinds[3]:= [op(Fact_Kinds[3]),temp];
						FactSet:= FactSet union {temp}; 
						Sol:=[op(Sol),["deduce 983",[],{fact9,fact8},{temp}]];
						DF9:= DF9 union {fact9} ;
						flag:= true;
						break; 
					fi; 
				od; 
			fi; 
		fi;
	od;
	
	return [Fact_Kinds,Sol]; 
end: # Deduce_From983s

#Deduce_Funcs : Buoc giai ap dung ham
GeometryConicSolver[Deduce_Funcs]:=proc(Goal)
	local HuongMT, 
	 func, uutien, kh_uutien, GoalType, ds, ToHop, funcstruct,temp,FactTypes,
	 FuncsApp, FuncStruct, FuncNew, i, tri,Values,facts,k,Set, HMT, co;
	global Found, Objects, Obj_Types, TestF, FactsNew,Funcs,Sol;

	#HuongMT : la ham tra ve nhung kieu doi tuong huong muc tieu 
	HuongMT:= proc(MT)
		if evalb(MT = "Diem") then 
			return ["Diem","DuongThang"];
		elif evalb(MT = "Vecto") then 
			return ["Diem"];
		elif evalb(MT = "Doan") then 
			return ["Diem"];
		elif evalb(MT = "DuongThang") or evalb(MT = "PhuongTrinh") then 
			return ["Diem","Vecto","DuongThang"]; 
		else return [];
		fi; 
	end:

	#Deduce_Funcs BODY
	#Tim kiem cac ham huong muc tieu va co doi so xac dinh
	
	if isPrint= true then 
		#print("----vao Deduce_Funcs");
		#print("Fact_Kinds=",Fact_Kinds);
	fi;
	
	HMT := HuongMT(type_Onet(Goal,1)); 
	FactTypes:=Find_Fact_Types([op(Fact_Kinds[2])],1);
	FuncsApp:=[];
	for func in Func_Names do
		#Không xét những func nào chỉ dành riêng cho từng Object (ví dụ như hàm tìm phương trình chính tắc)
		if(member("Object",func[4])) then next;fi;
		if member(func[1],HMT) and SubList(func[3],FactTypes) then 
			FuncsApp:= [op(FuncsApp),func];
		fi;
	od;

	# Thuc hien tinh toan tung ham 
	FuncNew:={};
	for func in FuncsApp do
		funcstruct:=Find_FuncStruct(func);
		ToHop:= MyCombinat(func[3], Fact_Kinds[2]);
		for ds to nops(ToHop) do
			if member([func,ToHop[ds]],TestF) then 
				next;
			fi;
			if func[4]={"doi_xung"} then
				co := false; 
				for i in TestF do
					if {op(ToHop[ds])}={op(i[2])} then 
						co:= true;
						break;
					fi; 
				od;
				if co = true then next;fi;
			fi;

			Values:=Get_Values(ToHop[ds]);
			FuncNew:= Compute_Func(funcstruct,ToHop[ds],Values);
			if FuncNew <> {} then
				Set:=Classify_Facts(convert(FuncNew,list));
				Sol:=[op(Sol),["Deduce_Funcs",[func],{op(ToHop[ds])},Set]]; 
				TestF:=TestF union {[func,ToHop[ds]]} ; 
			fi;
		od;
	od;
	
	return [Fact_Kinds,Sol];
end proc: # Deduce_Funcs

#Deduce_Rules
	#Các hàm phụ cho Deduce_Rules
	#Index_Element : Hàm trả về vị trí của 1 phần trong tập lớn (nếu có)
	#Hàm có tham số truyền vào là (e1,exp)
#

#Ham tra ve vi tri cua el trong exp neu co
GeometryConicSolver[Index_Element] := proc(el, exp)
	local i,kq;	
	kq := {};
	
	for i from 1 to nops(exp) do
		if (el = op(i,exp)) then
			kq := kq union {i};
		fi; 
	od;
	
	if kq = {} then 
		return 0;
	elif nops(kq)=1 then 
		return op(kq);
	else
		return kq;
	fi;
end proc:

#Rule_Type : Hàm trả về kiểu của một luật, tham số truyền vào dạng rule [[],[],...]
GeometryConicSolver[Rule_Type] := proc(rules)
	local i,j,k,rule,r_varNames,r_varTypes,r_hypos,obj,vt,temp,r_hypo,kq,kq1;
	
	if (whattype(rules) = `symbol`) then return [] fi;
	
	for i from 1 to nops(rules) do
		rule := op(i,rules);
		r_varNames := rule[2];
		r_varTypes := rule[3];
		r_hypos := rule[4][1];
		if (r_hypos = {}) then 
			kq[i] := [];
			next; 
		fi;
		j := 1;
		while nops(r_hypos)>0 do
			r_hypo := op(1,r_hypos); 
			r_hypos := r_hypos minus {r_hypo};
	
			for k from 2 to nops(r_hypo) do
				obj := op(k,r_hypo);
				vt := Index_Element(obj,r_varNames);
				if vt >0 then
					r_hypo[k] := r_varTypes[j];
				else
					temp := convert(obj,`string`);
					vt := SearchText("[",temp);
					if vt >0 then
						r_hypo[k] := substring(temp,1..vt-1);
					else
						r_hypo[k] := temp;
					fi; 
				fi;
			od;
			kq1[j]:= r_hypo;
			j := j +1;
			end;
			kq1 := op(op(kq1));
			for j from 1 to nops(kq1) do
				kq1[j] := rhs(kq1[j]);
			od; 
			kq[i] := kq1;
		od ;

		kq := op(op(kq));
		for i from 1 to nops(kq) do
			kq[i] := rhs(kq[i]);
		od;
		return kq;
end proc:

#Rela_Type : Hàm trả về kiểu của một quan hệ, hoặc 1 đối tượng (trong tập sự kiện của đề bài)
#rela truyền vào có dạng [[],[],...]
GeometryConicSolver[Rela_Type] := proc(relas)
	local kq,r,op_type,i,j;
	
	op_type := type_Onet(op(relas));
	
	if (op_type <> "type?") then
		# Đây là kiểu của một đối tượng
		return [op_type];
	fi;
	
	for j from 1 to nops(relas) do
		r := relas[j];
		for i from 2 to nops(r) do
			op_type := type_Onet(op(i,r));
			r[i] := op_type;
		od;
		kq[j] := r;
	od;
	
	kq := op(op(kq));
	for i from 1 to nops(kq) do
		kq[i] := rhs (kq[i]) ;
	od;
	return kq;
end proc:

#Deduce_Rules : Do tim luat co the ap dung duoc["",[dt],[kieudt],[{gt},{kl}]] 
GeometryConicSolver[Deduce_Rules]:=proc()
	local i, Cb,Comb,ReRule,news,ex,k,trihp,hamphu, temp,kt, co_them_newfact;
	global FactSet,Fact_Kinds,flag,Sol,TestR, TEST_DR, chisochay;
	
	hamphu:=proc()
		local h,tt,doi,j,s, i, return_,phu;
		global DF3;
		return_:={};

		for i in ReRule[5] do
			if not type(i,`=`) then
				tt:=op(0,i);
				doi:=op(i);
				phu:= parse(convert(tt(op(doi)),string));
			else
				tt:=op(0,rhs(i));
				doi:=[op(rhs(i))];
				for j to nops(doi) do
					s:=Unify_In(doi[j],[op(Fact_Kinds[2]),op(Fact_Kinds[7])]);
					if(s <>-1)then 
						doi[j]:=op(Get_Values([doi[j]]));
					fi;
				od;
				
				h:= parse(cat(convert(lhs(i),string), "=(",convert(tt(op(doi)),string),")"));
				k := Kind_Fact(h);
				
				if k=3 and not Unify_In1(h,FactSet)then 
					Fact_Kinds[k] :=[op(Fact_Kinds[k]),h];
					if not Unify_In1(lhs(h),FactSet) then 
						Fact_Kinds[2]:=[op(Fact_Kinds[2]),lhs(h)];
					fi;
					DF3:=DF3 union {h};
					FactSet:=FactSet union {h,lhs(h)}; 
					return_:={op(return_),h,lhs(h)};
				fi;
			fi;
		od;
		return return_;
	end:

	#Do tung luat
	kt:=0;
	for i in Rule_Structs do 
		# B1:kiem tra buoc 1: neu tap kieu doi tuong trong luat thuoc tap kieu doi tuong trong mo hinh bai toan thi luat co the ap dung duoc
		if SubList(i[3],Obj_Types) then
			#B2: to hop cac doi tuong trong bai toan co the ap dung tren luat
			Comb:=MyCombinat(i[3],[op(Objects),op(OAttrs)]);
			for Cb in Comb do
				if member([Cb,i],TestR) then next;fi;
				
				#B3: xet tung to hop va the cac phan tu trong to hop vao luat
				ReRule:=ReplaceR(Cb,i);
				
				#B4: kiem tra to hop nay co ap dung dc ko-neu co thi luu su kien moi sinh ra vao news 
				news:=ApplyRule(ReRule,FactSet);
				
				#B5: kiem tra cac su kien moi sinh ra, neu chua thuoc tap su kien moi FN thi them vao va cap nhat buoc giai
				if news<>{}then
					TestR:= TestR union {[Cb,i]}; 
					for ex in news do 
						k := Kind_Fact(ex);
						(*
						if k>=1 and k<=11 and not Unify_In1(ex,FactSet) then
							Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
							FactSet:=FactSet union {ex};# co_them_newfact:=1;
						fi;*)
						if k>=1 and k<=11 and not member(ex,Fact_Kinds[k]) then
							Fact_Kinds[k] :=[op(Fact_Kinds[k]),ex];
							FactSet:=FactSet union {ex};# co_them_newfact:=1;
						fi;
					od;
	
					#B6: neu luat co kem theo thu tuc phu de tinh gia tri cua su kien moi thi goi thu nay.VD: thu tuc viet phuong trinh duong thang
					trihp:={};
					if(ReRule[5]<>[]) then 
						trihp:=hamphu();
					fi; 
					
					Sol:=[op(Sol),["Deduce_Rules",i,ReRule[4][1],news union trihp ]];
					flag:=true; 
				fi; 
			od;
		fi;
	od;
	return [Fact_Kinds,Sol]; 
end proc: # Deduce_Rules

#Deduce_EqsGoal
GeometryConicSolver[Deduce_EqsGoal] := proc(Goal)
	local goal, typegoal, k, i,Value,
		Vars,ans,Values,RuleFunc,co,
		find_rule, test_values, find_fact8, rule_func, find_fact10,find_fact9,find_fact3_object, set_vars, find_fact11;
	global RuleEqs_Structs, Objects, FactSet, Fact_Kinds,flag, Sol, TEST_Eqs;
lprint("Deduce_EqsGoal ***");

	test_values := proc(tohops, giatris)
		local j, giatristemp;		
		giatristemp := giatris;
		
		if type(giatris,`set`) then giatristemp:=giatris[1];fi;
		for j to nops(giatristemp) do
			if evalb(giatristemp[j] ="cxd") then return true;fi; 
		od; 
		return false;
	end: # test_values

	set_vars := proc(fact11) 
		local temp, i, fact; 
		temp := {op(op(Set_Vars(lhs(fact11))))}; 
		if type(rhs(fact11),`+`) then 
			fact:=convert(rhs(fact11),list); 
		else 
			fact:=[rhs(fact11)]; 
		fi;
		
		for i in fact do 
			temp := `union`(temp, {op(op(Set_Vars(i)))});
		od; 
		return temp;
	end proc;#set_vars

	find_rule := proc()
		local rule, combs, cb, rerule, tam;
		tam:= [];
		
		for rule in RuleEqs_Structs do
			combs := MyCombinat(rule[3],Objects,1);
			for cb in combs do
				if test_values(cb,Get_Values(cb)) then 
					rerule := ReplaceR(cb,rule);
					if Unify_In1(rerule[4][1], FactSet) then
						if not member("Diem", rerule[3]) then
							tam:= [rerule,op(tam)];
						else tam:= [op(tam),rerule];
						fi; 
						
						Vars := Vars union {op(cb)};
					fi; 
				fi; 
			od; 
		od;
		RuleFunc := [op(RuleFunc),op(tam)];co := [op(co),seq("rule", i=1..nops(tam))]; 
	end : #find_rule

	find_fact8 := proc()
		local fact8;

		for fact8 in Fact_Kinds[8] do
			if nops({op(lhs(fact8))})<> 1 and test_values([op(lhs(fact8))],Get_Values([op(lhs(fact8))])) then
				RuleFunc := [op(RuleFunc),fact8]; co := [op(co),"fact8"];
				Vars := Vars union {op(lhs(fact8))};
			fi; 
		od;
	end:#find_fact8

	find_fact9 := proc()
		local fact9;
		for fact9 in Fact_Kinds[9] do
			if Unify_In1(fact9, DF9) then next; fi;
			if nops({op(rhs(fact9))})<> 1 and test_values([lhs(fact9),op(rhs(fact9))],Get_Values([lhs(fact9),op(rhs(fact9))])) then
				RuleFunc := [op(RuleFunc),fact9];co := [op(co),"fact9"]; 
				Vars := Vars union {lhs(fact9),op(rhs(fact9))};
			fi;
		od; 
	end: # find_fact9

	find_fact10 := proc()
		local fact10;
				
		for fact10 in Fact_Kinds[10] do
			if nops({op(rhs(fact10))})<> 1 and nops({op(lhs(fact10))})<> 1 and test_values([op(lhs(fact10)),op(rhs(fact10))],Get_Values([op(lhs(fact10)),op(rhs(fact10))])) then
				RuleFunc := [op(RuleFunc),fact10];co := [op(co),"fact10"]; 
				Vars := Vars union {op(lhs(fact10)),op(rhs(fact10))}; 
			fi;
		od; 
	end: # find_fact10

	find_fact11 := proc()
		local fact11, setVars;
		setVars:={};

		for fact11 in Fact_Kinds[11] do
			setVars:=set_vars(fact11);
			if nops({op(rhs(fact11))})<> 1
				and nops({op(lhs(fact11))})<> 1 and test_values([op(setVars)],Get_Values([op(setVars)])) then
				RuleFunc := [op(RuleFunc),fact11];co := [op(co),"fact11"];
				Vars := Vars union setVars; 
			fi;
		od;
	end: # find_fact11

	find_fact3_object := proc()
		local fact3, construct, obj, att, c, vars,j, varstem;

		for fact3 in Fact_Kinds[3] do
			if member(lhs(fact3),OAttrs) then 
				construct := ObjStruct_Replace(op(lhs(fact3))[1])[5];
				if construct <> [] then
					for c in construct do
						if Unify_Fact(lhs(c),lhs(fact3)) then
							vars := Set_Vars(rhs(c));
							for j in vars do
								if type(j,function)and op(0,j) <> `.` then 
									vars:= vars minus {j} union Set_Vars(op(j));
								fi;
							od;
							varstem:={};
							for j in vars do
								if type(j,function)and op(0,j)= `.` then
									varstem := varstem union {op(j)[1]};
								else varstem := varstem union {j};
								fi; 
							od; 
							
							Sol := [op(Sol),["find_fact3_object",{},{fact3,c},{rhs(c) = rhs(fact3)}]]; 
							RuleFunc:= [op(RuleFunc),[rhs(c) = rhs(fact3),[op(varstem),lhs(fact3)],vars]];
							co := [op(co),"fact3_object"];
							Vars := Vars union {op(varstem),lhs(fact3)};
						fi; 
					od; 
				fi; 
			fi;
		od; 
	end : # find_fact3_object 

	rule_func := proc(giatri)
		local funcname, giatritemp,eq1,eq2,Eqs,Eq,rf,vt,vp,eq,j,ex,exgt,thaythe,ngt,
		test_solve,GetVars_Poly,get_values,solve_eqs, init_values,get_value,find_eqs, test_vars, computationFunc;
		
		get_value := proc(bien,tapbien,tapgt)
			local b,gt;
			gt := Get_Values(bien);
			
			if gt = "cxd" then
				for b to nops(tapbien) do
					if tapbien[b]=bien then return tapgt[b];fi
				od; 
			fi; 
			return gt; 
		end: # get_value 

		get_values := proc(biens,tapbien,tapgt)
			local b, gts;
			gts := [];
			for b in biens do 
				gts := [op(gts),get_value(b,tapbien,tapgt)];
			od; 
			return gts; 
		end:# get_values

		#vd: Vecto(A,B)+Vecto(D,F)
		computationFunc:=proc(funcs)
			local temp, func, i, vp, k, f;
			k:=1;
			if type(vt,`list`) then vp:=[0,0]; else vp:=0; fi;
			if type(funcs,`+`) then 
				temp:=convert(funcs,`list`);
			else temp:=[funcs]; fi;
			
			for func in temp do
				if type(func,`*`) then 
					k:=op(select(type,{op(func)},numeric));
					f:=op(select(type,{op(func)},function));
				else
					f:=func;
				fi;
				funcname:= Find_FuncStruct(type_Onet(f));
				funcname:= parse(funcname[4]); 
				vp:= vp+ k*funcname(op(get_values([op(f)],Vars,giatritemp)));
			od;
			return vp;
		end:#computationFunc

		init_values := proc(biens,giatris)
			local b , giatristemp, init_value, temp,funcname,vt,h, gt;
			
			init_value := proc(bien)
				Eq := {}; 
				if type_Onet(bien) = "Diem" or type_Onet(bien)="Vecto" then 
					return [bien[1],bien[2]];
				elif type_Onet(bien) = "DuongThang" or type_Onet(bien) = "Doan" then 
					Eq:= {bien[1] = 1};
					return bien[1]*x + bien[2]*y + bien[3]=0;
				fi; 
			end: # init_value

			giatristemp:= giatris; 
			
			for b to nops(biens) do
				gt := get_value(biens[b],biens,giatristemp); 
				if gt = "cxd" then
					if Is_Function(biens[b]) then
						temp:= init_values([op(biens[b])],get_values([op(biens[b])],biens, giatristemp));
						funcname:= Find_FuncStruct(type_Onet(biens[b]));
						funcname:= parse(funcname[4]);
						vt:=funcname(op(temp));
						giatristemp[b] := vt;
					else 
						giatristemp[b] := init_value(biens[b]);
					fi;
				fi;
			od; 
			return giatristemp; 
		end: # init_values 

		GetVars_Poly:=proc(expr)
			local F,i;
			if type(expr, constant) or type(expr, string) then 
				return({});
			elif type(expr,`name`)or type(expr,`indexed`) or (type(expr, function) and evalb(op(0,expr) = "." ))then 
				return {expr};
			elif type(expr,`set`) or type(expr,list)then
				F:={}; 
				for i in expr do 
					F:= F union GetVars_Poly(i);
				od; 
				return F; 
			else 
				F:= GetVars_Poly({op(expr)}); 
				return F;
			fi;
		end : # GetVars_Poly 
		
		test_solve := proc(pts)
			ans := GetVars_Poly(pts);
			if nops(pts) < nops(ans) then 
				return false;
			fi;
			return true;
		end: # test_solve 
	
		test_vars:= proc(e, pts)
			local tam1, tam2, var1, var2, jj, tam;
			var1 := GetVars_Poly(e); 
			var2 := GetVars_Poly(pts);
			
			if var1 intersect var2 <> {} then return true;fi;
			
			tam1:= {};
			for jj in var1 do
				tam := convert(jj, string);
				if length(tam) >= 3 then 
					tam1:= tam1 union {parse(substring(tam,1..length(tam)-3))};
				else 
					tam1:= tam1 union {jj};
				fi;
			od; 
			
			tam2:= {};
			for jj in var2 do
				tam := convert(jj, string);
				if length(tam) >= 3 then 
					tam2:= tam2 union {parse(substring(tam,1..length(tam)-3))};
				else 
					tam2:= tam2 union {jj}; 
				fi; 
			od; 
			if tam1 intersect tam2 <> {} then return true;fi;
			return false;
		end: # test_vars 
	
		find_eqs:= proc(eqs)
			local e, tappt, t,r,i;
			tappt:=[];
			
			for e in eqs do 
				if tappt <> [] then
					r:= false;
					for t to nops(tappt) do
						if test_vars(e,tappt[t]) then 
							tappt[t]:= tappt[t] union {e};
							r:= true; 
						fi; 
					od;
					if not r then 
						tappt := [op(tappt),{e}]; 
					fi;
				else 
					tappt := [op(tappt),{e}]; 
				fi; 
			od; 
			tappt:=selectremove(has, tappt,[{}])[2];
			return tappt; 
		end: # find_eqs
	
		solve_eqs:= proc()
			local nghiem, n, tam, t, ta, thu, thutam;
			tam := find_eqs(Eqs);ngt :=0;
			
			for ta in tam do
				if test_solve(ta) then 
					nghiem:= MySolve(ta,ans); 
					for n in nghiem do
						thutam := subs(n, giatritemp);
						for t to nops(Vars) do
							if (GetVars_Poly(thutam[t]) minus {x,y}) = {} then					
								if type_Onet(Vars[t])="DuongThang" or type_Onet(Vars[t])="Doan" then
									thu := Vars[t].f = thutam[t];
								else 
									thu := Vars[t] = thutam[t]; 
								fi;
								if not Unify_In1(thu, Fact_Kinds[3]) then
									Fact_Kinds[3]:=[op(Fact_Kinds[3]),thu];
									FactSet := FactSet union {thu} ;
									flag := true;
									Sol :=[op(Sol),[["Deduce_EqsGoal"],[],ta,{thu}]]; 
								fi; 
							fi; 
						od;
					od;
					if nops(nghiem)<> 1 then 
						ngt := 1; return;
					else 
						giatritemp := thutam;
						Eqs := Eqs minus ta;
						Eqs:=subs(nghiem[1],Eqs);
					fi;
				fi; 
			od:
		end: # solve_eqs 
		
		#RuleFuns BODY
		
		giatritemp := init_values(Vars,giatri); 
		Eqs := {};
		for rf to nops(RuleFunc) do
			eq2 := 0;
			if evalb(co[rf]="rule") then 
				for i in RuleFunc[rf][5] do
					funcname := op(0,i);
					eq:= {funcname(op(get_values(RuleFunc[rf][2],Vars,giatritemp)))}; 
					Sol := [op(Sol),["Ap dung luat",[RuleFunc[rf]],{op(RuleFunc[rf][2])},eq]];
					if member(x,GetVars_Poly(eq)) or member(y, GetVars_Poly(eq)) then
						ex:= convert((op(GetVars_Poly(eq)minus{x,y})),string);
						ex := parse(substring(ex, 1..length(ex)-3));
						for j to nops(Vars) do
							if Vars[j]=ex then 
								giatritemp[j]:= op(eq);
								eq1:=op(eq);
								eq2:= 1;
							fi;
						od; 
					fi;
					
					if eq2 <> 1 then 
						Eqs := Eqs union eq; 
					fi;
				od;	
			elif evalb(co[rf]="fact8") then
				funcname:= Find_FuncStruct(type_Onet(lhs(RuleFunc[rf])));
				funcname:= parse(funcname[4]);
				vt:=funcname(op(get_values([op(lhs(RuleFunc[rf]))],Vars,giatritemp)));
				if type(vt,`list`) and nops(vt) <> 1 then
					eq:={}; 
					for j to nops(vt) do
						eq := eq union {vt[j] = rhs(RuleFunc[rf])[j] };
					od; 
				else 
					eq := {vt = rhs(RuleFunc[rf])}; 
				fi; 
				
				if eq2 = 1 then 
					Sol := [op(Sol),["Ap dung sk8",type_Onet(lhs(RuleFunc[rf])),{RuleFunc[rf],eq1},eq]];
				else
					Sol := [op(Sol),["Ap dung sk8",type_Onet(lhs(RuleFunc[rf])),{RuleFunc[rf]},eq]];
				fi;
				
				Eqs := Eqs union eq;		
			elif evalb(co[rf] = "fact9") then
				vt:= get_value(lhs(RuleFunc[rf]),Vars,giatritemp);
				funcname:= Find_FuncStruct(type_Onet(rhs(RuleFunc[rf])));
				funcname:= parse(funcname[4]); 
				vp:=funcname(op(get_values([op(rhs(RuleFunc[rf]))],Vars,giatritemp)));
				if type(vt,`list`) and nops(vp) <> 1 then
					eq:= {};
					for j to nops(vt) do
						eq := eq union {vt[j] = vp[j] };
					od; 
				else 
					eq := {vt = vp}; 
				fi;
				
				Sol := [op(Sol),["Ap dung sk9",[RuleFunc[rf]],{lhs(RuleFunc[rf]),op(rhs(RuleFunc[rf]))},eq]]; 
				Eqs := Eqs union eq;
			elif evalb(co[rf] = "fact10") then
				funcname:= Find_FuncStruct(type_Onet(lhs(RuleFunc[rf])));			
				funcname:= parse(funcname[4]); 
				vt:=funcname(op(get_values([op(lhs(RuleFunc[rf]))],Vars,giatritemp)));
				vp:=computationFunc(rhs(RuleFunc[rf]));
				
				if type(vt,`list`) and nops(vp)<>1 then
					eq:= {};
					for j to nops(vt) do
						eq := eq union {vt[j] = vp[j] };
					od; 
					else 
						eq := {vt = vp}; 
				fi;
				
				Sol := [op(Sol),["Ap dung sk10",[RuleFunc[rf]],set_vars(RuleFunc[rf]),eq]];
				Eqs := Eqs union eq;
			elif evalb(co[rf] = "fact11") then
				funcname:= Find_FuncStruct(type_Onet(lhs(RuleFunc[rf])));			
				funcname:= parse(funcname[4]); 
				vt:=computationFunc(lhs(RuleFunc[rf]));			
				vp:=computationFunc(rhs(RuleFunc[rf]));
				
				if type(vt,`list`) and nops(vp)<>1 then
					eq:= {};
					for j to nops(vt) do
						eq := eq union {vt[j] = vp[j] };
					od; 
				else eq := {vt = vp}; 
				fi;
				
				Sol := [op(Sol),["Ap dung sk11",[],set_vars(RuleFunc[rf]) union {RuleFunc[rf]},eq]];
				Eqs := Eqs union eq;
			elif evalb(co[rf] = "fact3_object") then
				ex := RuleFunc[rf][1]; thaythe:={}; 
				for j in RuleFunc[rf][3] do 
					if type(j,`function`) and op(0,j)=`.` then
						exgt:= get_value(op(j)[1],Vars,giatritemp);
						if op(j)[2] = x then 
							thaythe:=thaythe union {j=exgt[1]};
						elif op(j)[2] = y then 
							thaythe:=thaythe union {j=exgt[2]};
						fi;
					else 
						thaythe := thaythe union {j=get_value(j,Vars, giatritemp)}; 
					fi; 
				od; 
							
				eq := {subs(thaythe,RuleFunc[rf][1])};
				Sol := [op(Sol),[" ",[],{RuleFunc[rf][1],op(thaythe)},eq]]; 
				Eqs := Eqs union eq;
			fi;
			if rf = nops(RuleFunc) then Eqs := Eqs union Eq;fi;
			if nops(Eqs) =2 then
				ex := (map(s->parse(substring(convert(s,string),1..length(convert(s,string))-3)),GetVars_Poly(Eqs))) ;
				if nops(ex) = 1 and (type_Onet(ex[1])="DuongThang" or type_Onet(ex[1])="Doan" ) then
					Eqs := Eqs union Eq;
				fi;
			fi; 
			
			solve_eqs();
			if ngt =1 then return;fi; 			
			next;
		od;
	end: #rule_func


	#Deduce_EqsGoal BODY
	goal := Goal; 
	typegoal := type_Onet(goal);
	
	if evalb(typegoal = "PhuongTrinh") then 
		goal:= op(goal)[1];
		typegoal:="DuongThang";
	fi;
	RuleFunc := []; co := []; Vars := {}; 
	
	# tim luat, ham sinh phuong trinh
	find_rule();
lprint("1:"); print("RuleFunc:",RuleFunc);print("co:",co); print("Vars: ",Vars);
	find_fact8();
lprint("2:"); print("RuleFunc:",RuleFunc);print("co:",co); print("Vars: ",Vars);	
	find_fact9();
lprint("3:"); print("RuleFunc:",RuleFunc);print("co:",co); print("Vars: ",Vars);	
	find_fact10();	
	find_fact11();
	find_fact3_object();
lprint("4init_values:"); print("RuleFunc:",RuleFunc);print("co:",co); print("Vars: ",Vars);	
	
	# thu giai phuong trinh (voi truong hop co nhieu nghiem)
	Vars := [op(Vars)];
	Values := Get_Values(Vars);
	k:= Unify_In(goal,Vars);
	
	if type(Values,`set`) then
		for Value in Values do 
			rule_func(Value);
			if not flag then break;fi;
		od;
	else rule_func(Values);
	fi; 
	return [Fact_Kinds,Sol];
end: # Deduce_EqsGoal

#-------------------------------------------------------#
#Test_Goal : Hàm kiểm tra xem Goal đã tìm được chưa
GeometryConicSolver[Test_Goal]:=proc(Goal, Facts) 
	return Unify_In1(Goal,Facts);
end proc: # Test_Goal

#Output_Result
GeometryConicSolver[Output_Result]:=proc(Goal)
	local facts, value,Solution,i;
	global Fact_Kinds, Sol, OptimizeSol; 
	
	#Solution Hàm rút gọn lời giải
	Solution:= proc()
		local goalvars,Solnew,Step,i, j, Solnew1,Solnew2;
		Solnew2:=[]; 
		Solnew:=[];
		
		for j from 1 to nops(Goal) do
			goalvars:={Goal[j]};
			Solnew1:=[];
			for i from nops(Sol) to 1 by -1 do
				Step:=Sol[i]; 
				if (Step[4] intersect goalvars) <> {} then 
					if Step[1]="Determine_Goal" then 
						Solnew1 := [Step, op(Solnew1)];
						Step[4] := Step[4] intersect goalvars;
					else
						Step[4] := Step[4] intersect goalvars;
						Solnew1 := [Step, op(Solnew1)];
					fi;
					goalvars := (goalvars minus Step[4]) union Step[3];
				fi;
			od;
			Solnew2:=[op(Solnew2), op(Solnew1)];
		od;
		for i in Sol do
			if member(i,Solnew2) then 
				Solnew:=[op(Solnew),i]; 
			fi;
		od; 
		
		return(Solnew);		 
	end:#Solution	
	
	if not Test_Goal(op(1,Goal), FactSet) then 
		#printf("(*_*) Rat tiec %a khong giai duoc \n\n", op(1,Goal)); 
	else 
		#printf("(^_^) Ket qua can tim la:\n");
		
		value := Get_Values(op(1,Goal));
		if type(value,`set`) then
			
			for i in value do
				#print(op(1,Goal),"=",i);
			od;
		else 
			#print(op(1,Goal),"=",value);
		fi;
		
		OptimizeSol := Solution();
	fi;
end proc: # Output_Result

#Determine : Hàm xác định goal
GeometryConicSolver[Determine]:= proc(Goal)
	local Init, dem, lan;
	global Found, flag,Objects,Obj_Types, temp;
	
	Init:= proc()
		Found:=false;
		flag:=true;
		dem:=0; # biến đếm
		lan:=0; # lần
	end: # Init

	# Determine BODY
	Init(); 
	while not Found and flag do 
		flag:=false;
		lan:=lan+1;
		if isPrint= true then 
			lprint("GOAL = ", Goal);
			printf("[***] LAN = %a with Fact[2] and last Sol = \n",lan);
			print("found = ", Found); print("flag = ",flag);
			print(Fact_Kinds[2]);
			if nops(Sol) > 0 then
			print(Sol[nops(Sol)]); fi;
			print(Fact_Kinds[5]);
		fi;
		#-BUOC 1-
		# Ap dung Deduce_From3s de sinh ra cac sk2 tu cac sk3 
		if {op(Fact_Kinds[3])} <> DF3 then
			if isPrint= true then lprint("BUOC 1 - vao deduce 3s");	fi;
			
			Deduce_From3s();
			if flag then Found:=Test_Goal(Goal,FactSet);next;fi;
		fi;
		
		#-BUOC 2- 
		# Ap dung Deduce_From43s de sinh cac sk3 tu cac sk4 va cac sk3 bang cach the sk3 vao sk4
		if {op(Fact_Kinds[4])} <> DF43 then
			if isPrint= true then lprint("BUOC 2 - vao deduce 43s");			fi;
			Deduce_From43s();
			if flag then Found:=Test_Goal(Goal,FactSet);next;fi;
		fi;
		
		#-BUOC 3- 
		# Ap dung Deduce_From53s de sinh cac sk3, 4, 5 tu cac sk5 va cac sk3 bang cach the sk3 vao sk5
		#print("Fact_Kinds[5] = ",Fact_Kinds[5]);
		#print("DF53 = ",DF53);
		if {op(Fact_Kinds[5])} <> DF53 then
			if isPrint= true then lprint("BUOC 3 - vao deduce 53s");fi;
			Deduce_From53s();
			if flag then Found:=Test_Goal(Goal,FactSet);next;fi;
		fi;
		
		#-BUOC 4- 
		# Ap dung Deduce_From45s de sinh cac sk3 tu cac sk4 va cac sk5 bang cach giai he phuong trinh
		if {op(Fact_Kinds[4]),op(Fact_Kinds[5])} <> DF45 then
			if isPrint= true then lprint("BUOC 4 - vao deduce 45s");fi;
			Deduce_From45s();			
			if flag then Found:=Test_Goal(Goal,FactSet);next;fi;
			fi; 
		
		#-BUOC 5-
		# Ap dung Deduce_From8s de sinh ra cac sk7 tu cac sk8 
		if {op(Fact_Kinds[8])} <> DF8 then 
			if isPrint= true then lprint("BUOC 5 - vao deduce 8s");	fi;
			Deduce_From8s();
			if flag then Found:=Test_Goal(Goal,FactSet); next;fi;
		fi; 
		
		#-BUOC 6-
		# Ap dung Deduce_From983s sinh ra sk loai 3(hay sk loai 8) tu sk loai 3,8,9 bang cach the sk3 (sk8) vao sk9
		if {op(Fact_Kinds[9])} <> DF9 then
			if isPrint= true then lprint("BUOC 6 - vao deduce 983s");fi;
			Deduce_From983s();
			if flag then Found:=Test_Goal(Goal,FactSet); next;fi;
		fi;
		
		#-BUOC 7- 
		# Ap dung Deduce_Objects de giai ben trong doi tuong 
		if isPrint= true then lprint("BUOC 7 - vao deduce Objs");fi;
		Deduce_Objects();				
		if flag then Found:=Test_Goal(Goal,FactSet); next;fi; 

		#-BUOC 8-
		# Ap dung Deduce_From9s
		if {op(Fact_Kinds[9])} <> DF9 then 
			if isPrint= true then lprint("BUOC 8 - vao deduce 9s");	fi;
			Deduce_From9s(); 
			if flag then Found:=Test_Goal(Goal,FactSet);next;fi;
		fi;
		
		#-BUOC 9- 
		# Ap dung luat 
		if isPrint= true then lprint("BUOC 9 - vao Deduce_Rules");fi;
		Deduce_Rules();
		if flag then Found:=Test_Goal(Goal,FactSet);
		next;
		fi;
		
		#-BUOC 10- 
		# Ap dung Deduce_Func sinh su kien moi tu ham co the ap dung duoc 
		if isPrint= true then lprint("BUOC 10 - vao Deduce_Funcs");fi;
		Deduce_Funcs(Goal); 
		if flag then Found:=Test_Goal(Goal,FactSet); next;fi;
		
		#-BUOC 11- 
		# Ap dung Deduce_Eqs de tao ra sk moi bang cach giai pt
		if isPrint= true then 
			lprint("BUOC 11 - vao Deduce_EqsGoal");
		fi;
		Deduce_EqsGoal(Goal); 
		if flag then Found:=Test_Goal(Goal,FactSet); next;fi;
		#break; #???              
		if isPrint= true then 
			lprint("BUOC 11.1 - Sau dong lenh break ???");
			print("found = ", Found); print("flag = ",flag);
		fi;
		
		#-BUOC 12- 
		# Them vao doi tuong doi
		if ObjsNew <>[] then
			if dem < 2 then
				if isPrint= true then 
					lprint("BUOC 12 - Them doi tuong moi");
				fi;
				dem:=dem+1; 
				Objects:=[op(Objects),op(ObjsNew)];
				Obj_Types:=[op(Obj_Types),op(OTypesNew)];
				Classify_Facts(FactsNew);
				flag:=true
			fi;
		fi;	

	od; # end while
end proc: # Determine

#Determine_Goal
GeometryConicSolver[Determine_Goal]:=proc(Goal) 
	local Init,Values, func, funcstruct, facts, Set, ds, foundds, k, thamso, Goals_SAVE, temp;
	global TestF,Sol,ObjsNew, OTypesNew, FactsNew, Fact_Kinds, FactSet, Goals,Goal_ThehienTrongLoiGiai, TEST_Output;
	
	Init:= proc()
		ObjsNew:=[];
		OTypesNew:=[];
		FactsNew:=[]; 
	end: # Init 
	#Determine_Goal BODY
	Init();	
	if Is_Function(Goal) then
		# thuc hien tim doi so cua Goal-------founds = true: cac doi so deu xac dinh
		# thamso:=[op(Goal)];
		thamso:=XulyGoal_Bandau(Goal);		
		for ds in thamso do 		
			if not Test_Goal(ds, FactSet) then 
				Determine_Goal(ds); 
				if not Test_Goal(ds, FactSet) then 
					foundds:= false; 
					break; 
				else 
					foundds:= true;
				fi;
			else 
				foundds:=true;
			fi;
		od;
		
		# Neu cac doi so deu xac dinh thi thuc hien tinh toan Goal
		if foundds then
			Values:=Get_Values([op(Goal)]); 
			func:=type_Onet(Goal); #vd: type_Onet(VectoDoi(a));--->["Vecto", "VectoDoi", ["Vecto"], {}]
			funcstruct:=Find_FuncStruct(func); 
			facts:= Compute_Func(funcstruct,[op(Goal)],Values);
			TestF:=TestF union {[func,[op(Goal)]]};
			Set:=Classify_Facts([op(facts)]);
			Sol:=[op(Sol),["Determine_Goal",func,{op(Goal)},Set]]; 
		fi;
	else
		Determine(Goal);
	fi;
end: # Determine_Goal

GeometryConicSolver[XulyGoal_Bandau]:=proc(goal)
	local Goal,thamso,i;
	global Goal_ThehienTrongLoiGiai;
	Goal:=[];                        
	thamso:=[op(goal)];
	
	if type(goal,function) and op(0,goal)<>`.` then
		if op(0,goal)=r1 or op(0,goal)=r2 then 
			thamso:=[["Thuoc",op(1,goal),op(2,goal)],op(1,goal), op(2,goal).a, op(2,goal).c];
			Goal:=[goal,op(thamso)];
			Goal_ThehienTrongLoiGiai:=Goal;
		else 
			Goal:=[goal];thamso:=[op(goal)];
		fi;
	fi;	
	return thamso;
end proc:#XulyGoal_Bandau

#Determine_Goals
GeometryConicSolver[Determine_Goals]:=proc()
	local Init, Goal, time1;
	local TrSolve, s;
	global FactSet, TestF, TestR,TestOR,TestOCR,Sol,Goals,DF3, DF43,DF53,DF45, DF9, DF8,TestProp,chiso, Sols,TEST_, Goal_ThehienTrongLoiGiai;
	
	time1:=time();
	
	Init:= proc()
		Goal_ThehienTrongLoiGiai:=[];
		FactSet:=Hypos;
		DF3:= {}; # luu cac sk3 da xu ly
		DF43:= {}; # luu cac sk4 da xu ly
		DF53:= {}; # luu cac sk5 da xu ly
		DF45:= {}; # luu cac sk45 da xu ly
		DF8:={}; # luu cac sk8 da xu ly
		DF9:= {}; # luu cac sk9 da xu ly
		TestF:={}; # luu cac ham va cac doi so da xu ly
		TestR:={}; # luu cac luat va cac doi so da xu ly
		TestOR:={}; # luu cac luat ben trong doi tuong da xu ly
		TestOCR:={}; # luu cac quan he tinh toan ben trong doi tuong da xu ly
		TestProp:={}; # luu tinh trang cac tinh chat ben trong doi tuong xu ly roi
		chiso:= 1; # luu chi so dung trong viec sinh doi tuong moi
		Sols:={};
	end: # Init 
		
	# Determin_Goals BODY
	Init();
	Sol:=[]; 
	for Goal in Goals do
		if Test_Goal(Goal,FactSet) then 
			if isPrint= true then printf("(@_@)Bai toan khong can giai\n");
			fi;
		else
			Goal_ThehienTrongLoiGiai:=[Goal];
			Determine_Goal(Goal);
			# với Goal là r1(M,E) thì thể hiện ra cả những lời giải có r1(M,E),M.x, E.a,E.c;
			Output_Result(Goal_ThehienTrongLoiGiai);
		fi;
		Sols:={op(Sols),Sol};
	od;
	
	#lprint(`Total Time`,time()-time1);
	
	(*for s in Sol do 
		#print("s=",s); 
	od;*)

	if isPrint= true then lprint(`Total Time`,time()-time1);fi;
end proc: # Determine_Goals
