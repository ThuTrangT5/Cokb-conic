#Ham xu ly tren ONet theo mo hinh bai toan 
	#Is_Element;
	#Has_Element;
	#Is_Object;
	#Has_Object;
	#Is_Function;
	#type_Onet;
	#Find_Fact_Types.
	#AttrName;
	#StructName.
	#ObjStruct_Replace.
#

#Hàm Is_Element
GeometryConicSolver[Is_Element] := proc(ex) # <object>| <object>.<thuoc tinh>

(*if(isPrint = true) then
	lprint("Is_Element : ex = ", ex);
	print("1. type(ex, function) = ",type(ex, function));
	print("2. op(0,ex) = " + op(0,ex));
	print("3. op(1,ex) = ",op(1,ex));
	print("4. member(op(1,ex), Objects) = ",member(op(1,ex), Objects));
	print("5. ValidStructName_Onet(op(1,ex) = "+ValidStructName_Onet(op(1,ex)));
	print("6. op(op(1,ex)) = ",op(op(1,ex)));
	print("7. SubList([op(op(1,ex))],Objects) = ", SubList([op(op(1,ex))],Objects));
fi;*)

	if member(ex, Objects) or member(ex, OAttrs) then
		return true;
		
	elif type(ex, function) 
		and op(0,ex)=`.` 
		and (	member(op(1,ex), Objects) or member(op(1,op(1,ex)), Objects)
			or (ValidStructName_Onet(op(1,ex)))
			and SubList([op(op(1,ex))],Objects)			
		) then		
		return true;
		
	(*elif ValidStructName_Onet(ex) and SubList([op(ex)],[op(OAttrs),op(Objects)]) then
		return true; # DOAN[A,B]
	*)
	elif ValidStructName_Onet(ex) then
		return true;# cho trường hợp Doan[...] và Diem[...]		
	fi;
	
	return false;
end: # Is_Element

GeometryConicSolver[Has_Element] := proc(ex)
	local i;
	for i in ex do
		if Is_Element(i) then 
			return true;
		fi;
	end do;
	return false;
end: # Has_Element

GeometryConicSolver[Is_Object]:=proc(ex)
	local i;
	for i in Obj_Structs do
		if evalb(convert(ex,string) = i[1]) then 
			return true;
		fi;
	od;  
	return false;
end proc: # Is_Object

GeometryConicSolver[Has_Object] := proc(ex)
	local i;
	for i in ex do
		if not Is_Object(i) then 
			return false;
		fi;
	end do;
	return true;
end proc: #  Has_Object 

GeometryConicSolver[Is_Function]:=proc(ex)  #có cấu trúc của 1 hàm là ok
	local k,t,i;
	t:=convert(ex,string);
	k:= SearchText("(",t);
	
	if type(ex,function) and k <> 0 then
		return true;
	fi; 
	return false;
end proc: # Is_Function

GeometryConicSolver[ObjStruct_Replace]:=proc(d)
	local OSTemp,i,k,thaythe, objType, f, fact4, numOfBaseObjs;
	
	objType := type_Onet(d);
	OSTemp := ObjStruct(objType);
	#objProperties := OSTemp[6];
	
	#Bước 1: thay thế tên đối tượng và các biến trong cấu trúc Objecy(OSTemp[3])
	thaythe := seq(	OSTemp[3][1][i]=d.OSTemp[3][1][i],
			i=1..nops(OSTemp[3][1]));
	OSTemp := subs("Object" = d,thaythe,OSTemp);
	
	#Bước 2: thay thế các biến là đối tượng cơ bản của Object (OSTemp[2])
	thaythe:={};
	fact4 := 0;
	numOfBaseObjs := nops(OSTemp[2][1]);
	# tìm các sự kiện loại 4 là định nghĩa của đối tượng
	for f in Fact_Kinds[4] do
		if lhs(f) = d and (type( rhs(f), 'list') or type( rhs(f), 'indexed')) and nops(rhs(f))= numOfBaseObjs then
			fact4 := rhs(f);
			break;
		fi;
	od;
	
	if (fact4 <> 0) then
		thaythe := seq(OSTemp[2][1][i] = op(fact4)[i], i=1..numOfBaseObjs);
		OSTemp := subs(thaythe,OSTemp);
	fi;
	
	#Bước 3: Kiểm tra lại sự thay thế của OSTemp[6] : các properties của đối tượng
	#??? Chưa làm

	(*if type(d,indexed) then 
		OSTemp:=subs(seq([op(parse(OSTemp[1]))][i]=[op(d)][i],i=1..nops([op(d)])),OSTemp);
		OSTemp[3][2]:=map(s->convert(subs(seq([op(parse(OSTemp[1]))][i]=[op(d)][i],i=1..nops([op(d)])),parse(s)),string),OSTemp[3][2]);
		OSTemp[1]:=convert(subs(seq([op(parse(OSTemp[1]))][i]=[op(d)][i],i=1..nops([op(d)])),parse(OSTemp[1])),string); 
		
		for k to nops(OSTemp[3][1]) do
			if SearchText("Goc",convert(OSTemp[3][1][k],string))>0 then 
				thaythe:={op(thaythe),OSTemp[3][1][k]=d.parse(cat("Goc",op(parse(OSTemp[3][2][k]))[2]))};
			fi;
		od;	
	else

		for i in Fact_Kinds[1] do
			if i[1]=d and type(parse(i[2]),indexed)then
				OSTemp:=subs(seq([op(parse(OSTemp[1]))][j]=[op(parse(i[2]))][j],j=1..nops([op(parse(i[2]))])),OSTemp);
				OSTemp[3][2]:=map(s->convert(subs(seq([op(parse(OSTemp[1]))][j]=[op(parse(i[2]))][j],j=1..nops([op(parse(i[2]))])),parse(s)),string),OSTemp[3][2]);
				OSTemp[1]:=convert(subs(seq([op(parse(OSTemp[1]))][j]=[op(parse(i[2]))][j],j=1..nops([op(parse(i[2]))])),parse(OSTemp[1])),string);
			
				for k to nops(OSTemp[3][1]) do
					if SearchText("Goc",convert(OSTemp[3][1][k],string))>0 then 
						thaythe:={op(thaythe),OSTemp[3][1][k]=d.parse(cat("Goc",op(parse(OSTemp[3][2][k]))[2]))};
					fi;
				od;
			fi;
		od;
	fi;*)
	
	OSTemp:=subs(thaythe,OSTemp);	
	return OSTemp;
end:

#Hàm cho biết kiểu của một Object hay một thuộc tính của Object trên mạng COnet
#vi du ve cac truong hop cua element: O1 là, Ob.a là "DOAN", Ob.DOAN[A,B] là "DOAN", TRUNGDIEM(M,P) là "DIEM"
# return <type cua element> hoac la "type?"
GeometryConicSolver[type_Onet] := proc(element)
	global Objs_CONet, Otypes_CONet;
	local k,i, Otype, nameA,OS, name1;
	
	if member(element, Objects, 'k') then 
		return Obj_Types[k];
	elif type(element, function) and op(0, element) = `.` then
		Otype := type_Onet(op(1, element));
		if Otype = "type?" then return "type?";fi;
	
		if nops(element)=2 then
			nameA := op(2, element);# nameA chính là tên thuộc tính của đối tượng VD : E.f => nameA = f
			if type(nameA, indexed) then 
				return NameType(nameA);
			else 
				OS:=ObjStruct_Replace(op(1, element));
				if member(element, OS[3][1], 'k') then return OS[3][2][k];fi;
			fi;
		else #E.A1.x
			name1:=parse(cat(op(1,element),".",op(2,element)));# name1:=E.A1
			nameA:= op(3, element);#nameA:=x
			
			if type(nameA, indexed) then 
				return NameType(nameA);
			else
				OS:=ObjStruct_Replace(name1);
				if member(element, OS[3][1], 'k') then return OS[3][2][k];fi;
			fi;
		fi;
	elif type(element, indexed)  then # vd ve element: DOAN[M,A]
		return NameType(element);	
	elif Is_Function(element) then 
		for i in Func_Names do
			if i[2]=convert(op(0,element), string) and evalb(i[3]=[seq(type_Onet([op(element)][i],1),i=1..nops([op(element)]))]) then 
				if (nargs=2 ) then 
					return i[1];
				else 
					return i;
				fi;
			fi;
		od;
	fi;
	
	# Khong biet kieu gi
	return "type?";
end proc: # type_Onet

#Hàm tìm kiểu đối tượng cho các sự kiện trong Facts
GeometryConicSolver[Find_Fact_Types]:=proc(Facts,ds)
	local fact,Types;	
	Types:=[]; 
	
	for fact in Facts do
		if(nargs=2) then 
			Types:=[op(Types),type_Onet(fact,1)];
		else 
			Types:=[op(Types),type_Onet(fact)];
		fi;
	od; 
	return Types;
end proc: # Find_Fact_Types

#Hàm xác định tên thuộc tính từ tên cấu trúc
#VD: Goc[A,B,C] la cau truc cua thuoc tinh GocB .
GeometryConicSolver[AttrName]:=proc(ex)
	local OS,temp, prop,p;
	
	if not (type(ex,function)and op(0,ex)=`.` and type(op(2,ex),indexed)) then 
		return ex;
	fi;
	
	OS:=CObjectStruct(convert(op(0,op(2,ex)),string));
	if member(convert(op(2,ex),string),ObjStruct_Replace(op(1,ex))[3][2],'k') then 
		return ObjStruct_Replace(op(1,ex))[3][1][k];
	fi;
	
	prop:=subs(seq([op(parse(OS[1]))][i]=[op(op(2,ex))][i],i=1..nops([op(op(2,ex))])),OS[6]);
	
	for p in prop do
		if type(p,`=`) then
			temp:="";
			if lhs(p)=op(2,ex) then 
				temp:=rhs(p);
			elif rhs(p)=op(2,ex) then 
				temp:=lhs(p);       
			fi;
			if temp <> "" and member(convert(temp,string),ObjStruct_Replace(op(1,ex))[3][2],'k') then
				return ObjStruct_Replace(op(1,ex))[3][1][k];
			fi;
		fi;
	od;
	return ex;
end:

#Hàm xác định cấu trúc của một thuộc tính của đối tượng
#VD: thuoc tinh GocB co cau truc Goc[A.B,C]
GeometryConicSolver[StructName]:=proc(ex)
	if not (type(ex,function)and op(0,ex)=`.` ) then 
		return ex;
	fi;
	if member(ex,ObjStruct_Replace(op(1,ex))[3][1],'k') then 
		return op(1,ex).parse(ObjStruct_Replace(op(1,ex))[3][2][k]);
	fi;
	return ex;
end:

