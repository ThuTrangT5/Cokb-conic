#Phân loại sự kiện trên Onet
	#Kind_Fact;
	#Unify_Fact;
	#Unify_In;Unify_In1;
	#Classify_Facts;
	#Intersect_Unify;Minus_Unify;Union_Unify;
	#Find_VarUnify;
	#Replace_StructName;Replace_AttrName;Replace_Unify, IsEqual_Unify

#Hàm kiểm tra loại của một sự kiện
#Hàm nhận vào một sự kiện và xuất ra số thứ tự của sự kiện đó (1-11)
GeometryConicSolver[Kind_Fact]:=proc(fact)
	global Objects, Obj_Types, OAttrs, OAttr_Types, Fact_Kinds, Sol; 
	local temp, i, rightIsElement, rightVars, rightHasElement, rightIsIdentifyElement, f4new;
	
	#Loại trường hợp fact có dạng A=A, A=true, true=A
	if type(fact,`=`) then
		if fact then return 0; fi; # A=A => loại
		if type(lhs(fact),`=`) and lhs(fact) then return 0; fi; # A = true => loại
		if type(rhs(fact),`=`) and rhs(fact) then return 0; fi; # true = A => loại
	fi;

	if type(fact, list) then
		#Loai 1: Su kien thong tin ve loai doi tuong
		if nops(fact)=2 and 
		 (member(fact[1],Objects) or (ValidStructName_Onet(fact[1]))and SubList([op(fact1)],Objects)) and
		 type(fact[2],string) and member(NameType(fact[2]),Obj_Types) then 
			return 1;
			
		#Loai 6: Su kien ve 1 quan he tren cac dt/tt
		elif nops(fact) > 1 then
			temp:=fact;
			for i from 2 to nops(fact) do
				if member(fact[i],[op(Objects),op(OAttrs)] , 'k') then
					temp[i] := NameType([op(Obj_Types),op(OAttr_Types)][k]);
				elif ValidStructName_Onet(fact[i]) and SubList([op(fact[i])],Objects) then 
					temp[i] := NameType(fact[i]);
				elif Is_Function(fact[i]) then
					temp[i]:= type_Onet(fact[i])[1];
				elif type(fact[i],function) and op(0,fact[i])=`.` then 
					temp[i]:=NameType(type_Onet(fact[i]));
				else temp[i] := "?";
				fi;
			od;
			if Is_RelationType(temp) then return 6; fi; 
		fi;	
	#Loai 2: Su kien ve tinh xac dinh cua 1 dt/tt
	elif Is_Element(fact) then 
		return 2;
	
	elif type(fact,`=`) and Is_Element(lhs(fact)) then 

		#Loai 4:Sự kiện về sự bằng nhau giữa một đối tượng hay một thuộc tính với một đối tượng hay một thuộc tính khác
		#if Is_Element(rhs(fact)) or (type(rhs(fact),list) and Has_Element( Set_Vars(rhs(fact)) )) then return 4;
		
		#Trang sửa dòng trên thành 
		rightIsElement := Is_Element(rhs(fact));
		rightVars := Set_Vars(rhs(fact));
		rightHasElement := Has_Element(rightVars);
		
		#Kiểm tra xem vế phải có phải là định nghĩa của Element k?
		#Ví dụ : Doan[A,B] => là định nghĩa về đoạn => 
		rightIsIdentifyElement := false;
		if type(rhs(fact),`indexed`) then
			temp := [seq(Obj_Structs[i][1],i=1..nops(Obj_Structs))];
			if member(convert(op(0, rhs(fact)),string), temp) then
				rightIsIdentifyElement := true;
			fi;
		fi;
		
		if rightIsElement or rightIsIdentifyElement or (type(rhs(fact),list) and rightHasElement) then
			
			#Kiểm tra nếu fact này có dạng Doan = Doan thì thêm vào Fact_Kind[3] fact Doan.length = Doan.length
			if type_Onet(lhs(fact)) = "Doan" then
				f4new:= lhs(fact).length = rhs(fact).length;
				if not member(f4new, Fact_Kinds[4]) then
					Fact_Kinds[4] := [op(Fact_Kinds[4]), f4new];
					Sol :=[op(Sol), ["Deduce_FromObjectDoan",[],fact,{f4new}]]; 
				fi;
			fi;
			return 4;
		#End Trang sửa

		#Loai 9: <doi tuong> = <ham> 
		elif Is_Function(rhs(fact)) then return 9;
		
		#Loai 3: Su kien ve su xac dinh cua 1dt/tt thong qua bieu thuc hang
		#elif not Has_Element(Set_Vars(rhs(fact))) then return 3;
		elif not rightHasElement then
			return 3;
		
		#Loai 5: Su kien ve su phu thuoc cua 1dt/tt theo cac dt/tt khac thong qua 1 cong thuc tinh toan hoac la dang thuc theo cac dt/tt
		else return 5;
		fi;
	
	#Loai 5:
	elif type(fact,`=`) and (Has_Element( Set_Vars(lhs(fact)) ) or Has_Element( Set_Vars(rhs(fact)) )) then
		return 5;
	
	# Loai 7: Tinh xac dinh cua mot ham 
	elif Is_Function(fact) then return 7;
	
	elif type(fact,`=`) and Is_Function(lhs(fact)) then

		# Loai 10: Su kien ve su bang nhau cua 1ham voi 1ham khac:<ham>=<ham>.
		if Is_Function(rhs(fact)) then return 10; 
	
		# Loai 8: Tinh xac dinh cua mot ham thong qua bieu thuc hang:<ham>= <biểu thức hằng>.
		elif (Set_Vars(rhs(fact)))<>{} then 
			if ((op(0,rhs(fact))=`+`) or (op(0,rhs(fact))=`*`)) and Has_Element(op(Set_Vars(rhs(fact)))) and not Is_Function(rhs(fact)) then
				# Loai 11: Su phu thuoc cua 1 ham thong qua cac ham khac:<ham>=<bieu thuc ham/dt>
				return 11;
			else return 8;
			fi;		
		else return 8;
		fi;
	
	fi;
	return 0;
end proc: # Kind_Fact

#Hàm kiểm tra sự hợp nhất của 2 sự kiện
GeometryConicSolver[Unify_Fact]:=proc(fact1,fact2)
	local k1,k2,vars1, vars2,i,j,p, temp,prop,
	TestDX,Func_DX, fact1_, fact2_, fact1__, fact2__, time1;
	
	#Kiem tra su kien loai 6 co doi xung khong
	TestDX := proc()
		local type1, type2, n1, n2, i, j, k, expr1, expr2, flag;
		
		if fact1[1] <> fact2[1] then return (false);fi;
		
		type1 := fact1; n1 := nops(fact1);
		type2 := fact2; n2 := nops(fact2);
		
		for i from 2 to n1 do
			if type(type1[i], indexed) then 
				type1[i]:= convert(op(0,type1[i]), string);
			else
				type1[i]:= type_Onet(type1[i],1);
			fi;
		od;
		for i from 2 to n2 do
			if type(type2[i], indexed) then 
				type2[i]:= convert(op(0,type2[i]), string);
			else
				type2[i]:= type_Onet(type2[i],1);
			fi;
		od;
		
		if RelaProp(type1,"doi_xung") or RelaProp(type2,"doi_xung") then
			expr1 := convert(fact1[2..n1],set);
			expr2 := convert(fact2[2..n2],set);
			
			for i in expr1 do
				flag := false;
				for j in expr2 do
					if Unify_Fact(i, j) then flag := true;fi;
				end do;
				if flag = false then return (false);fi;
			end do;
			
			for i in expr2 do
				flag := false;
				for j in expr1 do
					if Unify_Fact(i, j) then flag := true;fi;
				end do;
				if flag = false then return (false);fi;
			end do;
			return true;
			
		elif n1 <> n2 then return (false);
		else
			for i from 2 to n1 do 
				if not Unify_Fact(fact1[i], fact2[i]) then 
					return (false);
				fi;
			end do;
			return(true); 
		fi;		
	end: # TestDX 
	
	Func_DX:=proc()
		local name, type1, type2, tinhchat, func, f;
		
		if fact1 = fact2 then return true;fi;
		
		if op(0,fact1) = op(0,fact2) and nops([op(fact1)]) = nops([op(fact2)])and {op(fact1)} = {op(fact2)} then 
			name:=convert(op(0,fact1),string);
			type1:= Find_Fact_Types([op(fact1)]);
			type2:= Find_Fact_Types([op(fact2)]);
			if SubList(type1,type2) and SubList(type2,type1) then 
				for func in Func_Names do
					if evalb(name = func[2]) and SubList(type1,func[3]) and SubList(func[3],type1) then
						break;
					fi;
				od;
			fi;
			
			if member("doi_xung", func[4]) then return(true);fi;
		fi;
		
		return (false);	
	end: # Func_DX
	
	k1:=Kind_Fact(fact1);
	k2:=Kind_Fact(fact2);
	if k1 <> k2 then return false;fi;
	
	# Khi fact1, fact2 la su kien loai 1
	if k1 = 1 then 
		if Unify_Fact(fact1[1],fact2[1]) and evalb(fact1[2]=fact2[2]) then 
			return(true);
		fi; 
	
	# Khi fact1, fact2 la su kien loai 2
	elif k1 = 2 then 
		if Is_Equal(fact1,fact2) then 
			return(true); 
		elif type(fact1,indexed) and type(fact2,indexed) and Is_Equal(op(0,fact1),op(0,fact2)) and {op(fact1)} = {op(fact2)} then 
			prop:=ObjStruct(convert(op(0,fact1),string))[6] ; 
			prop:=subs(seq([op(parse(ObjStruct(convert(op(0,fact1),string))[1]))][i]=[op(fact1)][i],i=1..nops([op(fact1)])),prop);

			for p in prop do
				if type(p,`=`) and 
				( [op(lhs(p))]=[op(fact1)] and [op(rhs(p))]=[op(fact2)] ) or 
				( [op(rhs(p))]=[op(fact1)] and [op(lhs(p))]=[op(fact2)] ) then
					return(true);
				fi; 
			od;
			
		elif type(fact1,function) and op(0,fact1)=`.` and type(fact2,function) and op(0,fact2)=`.` then
			if nops(fact1)=nops(fact2) then 
				if nops(fact1)=2 then
					if Unify_Fact(op(1,fact1),op(1,fact2)) and (AttrName(fact1)= AttrName(fact2)or (Unify_Fact(op(1,AttrName(fact1)),op(1,AttrName(fact2)))and op(2,AttrName(fact1))=op(2,AttrName(fact2)) )) then 
						return(true);
					fi;
				else
					fact1_:=parse(cat(op(1,fact1),".",op(2,fact1)));
					fact2_:=parse(cat(op(1,fact2),".",op(2,fact2)));
					fact1__:=op(3,fact1);
					fact2__:=op(3,fact2);
					if Unify_Fact(fact1_,fact2_) and (AttrName(fact1)= AttrName(fact2)or ( Unify_Fact(op(1,AttrName(fact1)),op(1,AttrName(fact2)))and op(2,AttrName(fact1))=op(2,AttrName(fact2)) )) then 
						return(true);
					fi;
				fi;
			fi;
		fi;
		
	# Khi fact1, fact2 la su kien loai 3
	elif k1 = 3 then	
		if Is_Equal(lhs(fact1),lhs(fact2)) and Is_Equal(rhs(fact1),rhs(fact2)) then 
			return(true);	
		elif Is_Equal(lhs(fact1),rhs(fact2)) and Is_Equal(rhs(fact1),lhs(fact2)) then
			return(true);		
		elif Unify_Fact(lhs(fact1),lhs(fact2)) and Is_Equal(rhs(fact1),rhs(fact2)) then
			return(true);		
		elif Unify_Fact(lhs(fact1),rhs(fact2)) and Is_Equal(lhs(fact1),rhs(fact2)) then
			return(true); 
		fi; 
	
	# Khi fact1, fact2 la su kien loai 4
	elif k1 = 4 then 
		if Unify_Fact(lhs(fact1),lhs(fact2)) and Unify_Fact(rhs(fact1),rhs(fact2)) then
			return(true);
		elif Unify_Fact(lhs(fact1),rhs(fact2)) and Unify_Fact(rhs(fact1),lhs(fact2)) then 
			return(true); 
		fi;	
	
	# Khi fact1, fact2 la su kien loai 5
	elif k1 = 5 then
		if Is_Equal(lhs(fact1)- rhs(fact1) + lhs(fact2) - rhs(fact2),0) then 
			return(true);
		elif Is_Equal(lhs(fact1)- rhs(fact1) - lhs(fact2) + rhs(fact2),0) then
			return(true);
		else
			vars1:=Set_Vars(fact1);
			vars2:=Set_Vars(fact2);
			temp:=fact2; 
			for i in vars1 do
				for j in vars2 do
					if Unify_Fact(i,j) then temp:=subs(j=i,temp); fi;
				od;
			od;
			if temp <> fact2 and Unify_Fact(fact1,temp) then 
				return(true);
			fi;
		fi;
		
	# Khi fact1, fact2 la su kien loai 6
	elif k1 = 6 then
		if fact1=fact2 then 
			return true;
		else
			#kiem tra kha nang hop nhat khi quan he la doi xung
			return TestDX();
		fi;
	
	# Khi fact1, fact2 la su kien loai 7
	elif k1 = 7 then 
		return Func_DX();	
	# Khi fact1, fact2 la su kien loai 8
	elif k1 = 8 then
		return Unify_Fact(lhs(fact1),lhs(fact2)); 
		
	# Khi fact1, fact2 la su kien loai 9
	elif k1=9 then 
		if evalb( lhs(fact1) <> lhs(fact2) ) then 
			return (false);
		else 
			return Unify_Fact(rhs(fact1),rhs(fact2));
		fi;
		
	# Khi fact1, fact2 la su kien loai 9,10,11
	elif k1 >=9 and k1<=11 then 
		if evalb( fact1 = fact2 ) then return(true);fi;
	fi;
	
	return (false);
end proc: # Unify_Fact

#Unify_In1
GeometryConicSolver[Unify_In1] := proc (fact, Facts) 
	local i,fact1,time1;
	
	if type(fact, set) then
		for fact1 in fact do
			if not Unify_In1(fact1, Facts) then 
				return(false);
			fi;
		end do;
		return(true);	
	else
		for i to nops(Facts) do
			if Unify_Fact(fact, Facts[i]) 
				then return(true); 
			fi;
		od; 
		return(false)
	fi;
end proc:#-------------Unify_In1

#Hàm phân lớp sự kiện
#Hàm nhận vào danh sách các sự kiện, xuất ra danh sách chứa 11 tập hợp tương ứng với 11 loại sự kiện ??? (code mới set có 8 loại)
GeometryConicSolver[Classify_Facts]:=proc(facts::list)
	local i,k, Set; 
	global Fact_Kinds, flag, FactSet;
	
	Set:={}; 
	
	for i in facts do	
		k:=Kind_Fact(i);
		if k>=1 and k<=11 then 
			if not Unify_In1(i,Fact_Kinds[k]) then    
				Fact_Kinds[k]:= [op(Fact_Kinds[k]),i];		
				FactSet:=FactSet union {i};
				Set:= Set union {i} ;
				flag:= true; 
			fi; 
		fi; 
	od; 
return Set;
end proc: # Classify_Facts

#Các hàm tìm phần giao, hiệu, hội của các tập sự kiện xét theo sự hợp nhất của hàm Unify_Fact.
GeometryConicSolver[Intersect_Unify] := proc(Aset, Bset) 
	local fact, Cset;
	
	Cset := {};
	for fact in Aset do
		if Unify_In1(fact, Bset) then 
			Cset := {op(Cset), fact};
		fi;
	od;
	return Cset;
end: # Intersect_Unify

GeometryConicSolver[Minus_Unify]:= proc( Aset, Bset)
	return  Aset minus Intersect_Unify(Aset, Bset);  
end: # Minus_Unify

GeometryConicSolver[Union_Unify] := proc(Aset, Bset)  
	return Aset union Minus_Unify(Bset, Aset);  
end: # Union_Unify

GeometryConicSolver[IsEqual_Unify]:= proc( expr1, expr2)
	# ???
end: # IsEqual_Unify

GeometryConicSolver[Replace_Unify]:= proc( expr)
	# ???
end: # Replace_Unify

#Hàm tìm tập hợp các biến hợp nhất có thể thay thế cho nhau
GeometryConicSolver[Find_VarUnify]:= proc(ex)
	local i,j,flag1,vars,vars1,thaythe,used;
		
	#vars1 luu cac bien cau truc, vars2 luu cac bien khong co cau truc
	vars1:={}; vars:=Set_Vars(ex);	
	thaythe:={};
	used:={};
	
	for i in vars do
		if type(i,indexed)or (type(i,function)and op(0,i)=`.`and type(op(2,i),indexed)) then 
			vars1:={op(vars1),i};vars:=vars minus {i};
		fi;
	od;
	vars1:=[op(vars),op(vars1)];
	for i in vars1 do
		flag1:=false;
		for j in used do
			if Unify_Fact(i,j) then 
				thaythe:={op(thaythe),i=j};
				flag1:=true;
			fi;
		od;
		if not flag1 then used:={op(used),i};fi;
	od;
	return thaythe;
end:

# thay the ten cau truc bang ten thuoc tinh.
#VD:thay the Goc[A,B,C] bang GocB
GeometryConicSolver[Replace_StructName]:=proc(ex)
	local vars,thaythe;
	
	vars:=Set_Vars(ex);
	thaythe := map(s->s=AttrName(s),vars);
	return subs(thaythe,ex);
end:

#thay the ten thuoc tinh bang ten cau truc
#VD: thay the GocB bang Goc[A,B,C]
GeometryConicSolver[Replace_AttrName]:=proc()
	#???
end:
