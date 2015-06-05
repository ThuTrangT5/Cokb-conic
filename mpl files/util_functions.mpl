#Các hàm hỗ trợ cơ bản
	#SubList         kiểm tra list1 có phải con của list2 không
	#Is_RelationType     kiểm tra loại quan hệ có đúng không
	#RelaProp        kiểm tra các tính chất x có trong quan hệ s không
	#Is_DacTrung       kiểm tra O1 có phải là tính chất đặc trưng của O2 không
	#NameType        lấy tên của đối tượng DOAN[A,B]->DOAN
	#ValidStructName_Onet  kiềm tra sự hợp lệ của tên đối tượng DOAN[A,B]
	#Set_Vars        tìm các biến trong 1 biểu thức
	#Is_Equal: kiểm tra sự bằng nhau giữa 2 biểu thức
#
GeometryConicSolver[Is_Equal] := proc(expr1,expr2)
	local flag, i,j;
	 
	# Truong hop expr1 va expr2 deu la list
	if type(expr1,list) and type(expr2,list) then
		if nops(expr1) <> nops(expr2) then   
			RETURN(false);
		fi;
		for i from 1 to nops(expr1) do
			if not Is_Equal(expr1[i],expr2[i]) then
				RETURN(false);
			fi;
		od;
		
		RETURN(true);
	fi;
	
	# Truong hop expr1 va expr2 deu la set
	if type(expr1,set) and type(expr2,set) then
		for i in expr1 do
			flag := false;
			for j in expr2 do
				if Is_Equal(i,j) then 
					flag := true; 
					break;
				fi; 
			od;
			
			if not flag then RETURN(false);fi;
		od;
		
		for i in expr2 do
			flag := false;
			for j in expr1 do
				if Is_Equal(i,j) then 
					flag := true; break;
				fi; 
			od;
			if not flag then RETURN(false);fi;
		od;
		RETURN(true);
	fi;
	
	# Truong hop khac
	flag := evalb(expr1 = expr2);
	if flag = false and not type(expr1,string) and not type(expr1,string) then 
		if type(expr1, polynom) and type(expr2, polynom) then  
			flag := evalb(simplify(expand(expr1-expr2))=0);
		elif type(expr1, `=`) and type(expr2, `=`) then  
			flag := evalb(simplify(expand(abs(lhs(expr1)-rhs(expr1))-abs(lhs(expr2)-rhs(expr2))))=0);
		fi;
	fi;
	return flag;
end proc: # Is_Equal

GeometryConicSolver[SubList]:=proc(list1,list2)
	local i,j,B,flag1; 
	B:=list2;
	if nops(list1) > nops(list2) then return false;fi;
	if not `subset`(convert(list1,set),convert(list2,set)) then return false;fi;
	for i to nops(list1) do
		flag1:=0;
		for j to nops(B) do
			if B[j]=list1[i] then 
				B[j]:="";
				flag1:=1;
				break;
			fi;
		od;
		if flag1=0 then return false;fi;
	od;
	return true;
end proc: # SubList

#Is_RelationType(["TrungDiem","Diem","Doan"]);#kiem tra slist co phai la 1 quan he vd: slist :=["TrungDiem","Diem","Doan"]# vd: slist["TrungDiem","Diem","Doan"]
GeometryConicSolver[Is_RelationType] := proc(slist::list)
	local nlist, i;
	nlist := map(s->NameType(s), slist);
	for i from 1 to nops(Rela_Structs) do
		if nlist = Rela_Structs[i][1] then 
			return true;
		fi;
		if Rela_Structs[i][1][1]=nlist[1] 
			and member("doi_xung", Rela_Structs[i] [2]) 
			and evalb(convert(nlist,set)= convert(Rela_Structs[i][1],set))then 
			return true;
		fi;
	end do; 
	return false;
end proc: # Is_RelationType

GeometryConicSolver[RelaProp] := proc(slist::list,prop::string)
	# kiem tra tinh chat prop co la tinh chat cua quan he slist
	# Neu khong co doi thu hai thi RETURN (tap cac tinh chat cua quan he)
	local nlist, i;
	nlist := map(s->NameType(s), slist);
	for i from 1 to nops(Rela_Structs) do
		if nlist = Rela_Structs[i][1]  then
			if nargs = 1 then 
				return Rela_Structs[i][2];
			elif member(prop, Rela_Structs[i][2]) then 
				RETURN (true);
			else RETURN(false);
			fi;
		fi;
	end do;
	if nargs = 1 then return {}; else RETURN(false);
	fi;	
end proc: # RelaProp
#RelaProp(["CungHuong", "Vecto", "Vecto"], "doi_xung");
#RelaProp(["ThangHang","Diem","Diem","Diem"],"doi_xung");

#kiem tap O1 co la tinh chat dac trung cua O2 khong
GeometryConicSolver[Is_DacTrung]:=proc(O1,O2) 
	local rule,r,O1_1;
	for rule in ObjStruct(type_Onet(O2))[8] do
		if evalb(rule[1] = "xac_dinh_doi_tuong") then 
			r:= map(s->O2.s,rule[4][1]);			
			if Unify_In1(O1,r) then
				return true;
			fi;
		fi;
	od;
	return false;
end proc: # IsDacTrung

#lay ten cua doi tuong vd: Doan[A,B] -----> "Doan", "Doan[A,B]"--->"Doan","Doan"--->"Doan"
GeometryConicSolver[NameType] := proc(s)
	local k;
	if type(s, string) then
		k := SearchText("[",s);
		if k > 0 then RETURN(substring(s,1..(k-1)));
		else RETURN(s);
		fi;
	fi;
	if type(s, indexed) then RETURN( convert(op(0,s), string) );fi;
	RETURN ("?");
end proc: # NameType

# Kiem tra tinh hop le cua mot ten cau truc nhu: Doan[A,B]
GeometryConicSolver[ValidStructName_Onet] := proc(name) 
	local  Sn1;
	if not type(name, indexed) then RETURN (false);fi;
	if not member(NameType(name), map(x->x[1],Obj_Structs)) then RETURN (false);fi;
	Sn1 := parse(ObjStruct(NameType(name)) [1]);
	if not type(Sn1, indexed) or nops(name) <> nops(Sn1) then
		RETURN (false);
	fi;
	RETURN (true);	
end proc: # ValidStructName_Onet

#tìm các biến trong 1 biểu thức
GeometryConicSolver[Set_Vars]:=proc(expr)
	local F,i, allObjs, oName;
			
	if type(expr, constant) or type(expr, string) then 
		RETURN ({});
		
	#Trang bổ sung kiểu indexed dạng Doan[A,B] => vars = A,B
	(*elif type(expr,`indexed`) then
		#Lấy tất cả tên các đối tượng lưu trong file Objects.txt
		allObjs := {seq(Obj_Structs[i][1], i=1..nops(Obj_Structs))};
		#lấy tên object 
		oName := convert(op(0, expr), string);
		
		if member(oName, allObjs) then
			F:={}; 
			for i in expr do
				if not member(i,{x,y})then
					F:= F union Set_Vars(i);
				fi;
			od; 
			return F;
		else
			return {expr};
		fi;
	#End Bổ sung
	*)
	elif type(expr,`name`)or type(expr,`indexed`) or type(expr, function) then # Trang sửa chỗ này
	#elif type(expr,`name`) or type(expr, function) then
	
		return {expr};
	elif type(expr,`set`) or type(expr,list)then
		F:={}; 
		for i in expr do
			if not member(i,{x,y})then
				F:= F union Set_Vars(i);
			fi;
		od; 
		return F;
	
	else F:= Set_Vars({op(expr)});
		return F;
	fi;
end proc: # Set_Vars

#Sao chép obj thành n obj khác
GeometryConicSolver[CopyObject]:= proc(obj, n)
	global Fact_Kinds;
	local objName, objType, objFacts, newNames, newTypes, newFacts, newGoals, newName, facts, i, j;

	objName  := convert(obj,string); #tên của đối tượng dưới dạng String
	objType  := type_Onet(obj);#kiểu của đối tượng
	objFacts :=  [[], [], [], [], [], [], [], [], [], [], []];#Các sự kiện có mặt đối tượng 
	
	newNames := [];
	newTypes := [];
	newFacts := [[], [], [], [], [], [], [], [], [], [], []];
	newGoals := [];
	
	for i from 1 to 11 do 
		objFacts[i] := select(has,Fact_Kinds[i], obj);
	od;
	for i from 1 to n do
		newName := parse(cat(objName, i));
		newNames := [op(newNames), newName];
		newTypes := [op(newTypes), objType];
		
		for j from 1 to 11 do 
			facts := subs(obj = newName, objFacts[j]);
			newFacts[j] := [op(newFacts[j]), op(facts)];
		od;
	od;
	
	if member(obj, Goals) then
		newGoals := newNames;
	fi;
	
	return [newNames, newTypes, newFacts, newGoals];
end:

#Phát sinh thêm đối tượng khi tìm được nhiều nghiệm đúng cho đối tượng hoặc thuộc tính của đối tượng đó
#Trường hợp này chỉ phát sinh khi có sự kiện loại 3 được sinh ra
GeometryConicSolver[CreateNewObjectsWithMultiResult]:= proc(results)
	global Fact_Kinds, FactSet, Sol, Objects, Obj_Types, Goals;
	local obj, n, i, newObjs, newFact3s, r, f3;

	obj := lhs(results[1][1]);
	if type(obj,`.`) then
		obj := op(1,obj);
	fi;
	n := nops(results)-1;
	
	newObjs := CopyObject(obj, n);
	newFact3s := {results[n+1][1]}; 
	
	for i from 1 to n do
		r := results[i];
		f3 := subs(obj=newObjs[1][i], r);
		newFact3s := newFact3s union f3;
	od;
	
	newObjs[3][3] := [op(newObjs[3][3]), op(newFact3s)];
	
	#--- Update ---
	#1. Objects, ObjTypes, OAttrs & OAttr_Types
	Objects := [op(Objects), op(newObjs[1])];
	Obj_Types := [op(Obj_Types), op(newObjs[2])];
	# OAttrs & OAttr_Types => Do NOT update => TODO later
	
	#2. Update Fact_Kinds
	for i from 1 to 11 do 
		Fact_Kinds[i]:= [op(Fact_Kinds[i]), op(newObjs[3][i])];
		FactSet:= FactSet union {op(newObjs[3][i])};
	od;
	
	#3. DF53, FactSet, Sol
	Sol:=[op(Sol),["New_Object",[],{obj}, {op(newObjs[1])}]];
	
	#4. Goals
	Goals := [op(Goals), op(newObjs[4])];
	#--- End Update ---
	
	return op(newFact3s);
end: