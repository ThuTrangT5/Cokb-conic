#Hàm hỗ trợ giải bài toán
	#ApplyRule,Find_FuncStruct,MyCombinat,
	#ReplaceR,Get_Values,Compute_Func;
#

#Ap dung rule tren tap FactSet
GeometryConicSolver[ApplyRule] := proc(rule, FactSet)
	local  fact, setfact, news, pr, time1,  i, hypos, hypo5s, hypo, vars, f3;
	
	#gia thiet nam trong FactSet
	if Unify_In1(rule[4][1], FactSet)  then 
		setfact := {};
		
		#Tìm những sự kiện trong Goal của Rule chưa có trong tập FactSet
		setfact := `minus`(rule[4][2],FactSet);
		if nops(rule[5]) = 0 then
			return setfact;
		else
			news := {};
			for pr in rule[5] do
				fact := lhs(pr);
				if `subset`({fact},setfact) then
					news := {op(news), pr};
				fi;
			od;
			return news;
		fi;
	else  
		#RETURN ({});
		#Xét những fact chưa có trong tập FactSet có phải là fact loại 5 hay k?		
		hypos := rule[4][1] minus FactSet;
		hypo5s := {};
		for i from 1 to nops(hypos) do
			hypo := hypos[i];
			if Kind_Fact(hypo) = 5 then
				hypo5s := hypo5s union {hypo};
				vars := Set_Vars(hypo);
				if `subset`(vars, {op(Fact_Kinds[2])}) = false then return ({});fi;
				
				#Tìm và thay thế các fact3 vào rule hypo 
				for f3 in Fact_Kinds[3] do
					if member(lhs(f3), vars) then
						hypo := subs(f3,hypo);
						if hypo then break;fi;
					fi;
				od;				
				if not hypo then
					return ({});					
				fi;
			fi;
		od;
		
		if hypo5s <> {} then
			return rule[4][2];
		fi;
		
		return ({});
	fi;
end proc: #  ApplyRule 

#Tìm cấu trúc của hàm
GeometryConicSolver[Find_FuncStruct]:=proc(func)
	local i;
	
	for i in Func_Structs do
		if evalb(func[2]=convert(op(0,parse(i[1])),string)) and func[3] = i[2][2] then 
			return i;
		fi; 
	od;
	return NULL;
end proc: # Find_FuncStruct
	
# Xet cac to hop co the co tu cac sk loai 2 va sk loai 7
GeometryConicSolver[MyCombinat]:=proc(doiso::list, Fact)
	local TH_Obj, n, i, ToHop, k,Otemp,fact, TestCombinat;   
	
	TestCombinat := proc(th,tohop)
		#Kiểm tra th có trong tohop chưa
		# VD: th = [1,2], tohop = [[2,1],[3,4]] => th thuộc tohop =>return true  
		local j;
		for j to nops (tohop) do
			if SubList(tohop[j],th) and SubList(th,tohop[j]) then 
				return true;
			fi;  
		od;  
		return false; 
	end: # TestCombinat
	
	#MyCombinat's body	
	n:=nops(doiso);
	Otemp:=[];
	
	for fact in Fact do
		if member(type_Onet(fact,1),doiso) then  
			Otemp:=[op(Otemp),fact];
		fi;
	od;
	
	TH_Obj:= combinat[permute](Otemp,n);   
	ToHop:=[];
	
	for i to nops(TH_Obj) do
		if nargs=3 and TestCombinat(TH_Obj[i],ToHop) then 
			next;
		fi;
		if doiso = Find_Fact_Types(TH_Obj[i],1) then      
			ToHop:=[op(ToHop),TH_Obj[i]];
		fi;
	od;
	return ToHop;
end proc:#  MyCombinat

#Xét các tổ hợp có thể có từ các sự kiện loại 2 và loại 7
GeometryConicSolver[MyCombinat1]:=proc(doiso::list, Fact)
	local TH_Obj, n, i, ToHop, k, Otemp, fact, TestCombinat;
	
	# kiem tra th co trong tohop chua
	#Kiểm tra th có trong tập con của tohop chưa
	#return về vị trí chứa trong của th
	TestCombinat := proc(th,tohop)
		local j;
		for j to nops (tohop) do
			if SubList(tohop[j],th) and SubList(th,tohop[j]) then 
				return j;
			fi;  
		od;  
		return 0; 
	end: # TestCombinat
	
	#MyCombinat's body
	n:=nops(doiso);
	Otemp:=[];
	
	for fact in Fact do
		if member(type_Onet(fact,1),doiso) then
			Otemp:=[op(Otemp),fact];
		fi;
	od;
	
	TH_Obj:= combinat[choose](Otemp,n);	
	ToHop:=[];
	
	for i to nops(TH_Obj) do
		if doiso = Find_Fact_Types(TH_Obj[i],1) then
			ToHop:=[op(ToHop),TH_Obj[i]];
		fi;	
	od;
	return ToHop;
end proc:   #  MyCombinat1

GeometryConicSolver[ReplaceR]:=proc(comb::list,rule)
	return subs(seq(rule[2][i]=comb[i],i=1..nops(comb)),rule);
end proc:  #  ReplaceR

GeometryConicSolver[ReplaceR_]:=proc(comb::list,rule)
	return subs(seq(rule[2][i]=comb[i],i=1..nops(comb)),rule);	
end proc:  #  ReplaceR

#Tìm giá trị của biến, biến có thể có nhiều giá trị
GeometryConicSolver[Get_Values]:=proc(biens) 
	local get_value, giatridon, cacgiatridon, tachgiatri, bien, values;
	global Fact_Kinds, Obj_Types, temp;
	
	get_value:= proc(bien)
		# ham tim gia tri cua bien : vidu: bien := a;
		# Neu a co gia tri cu the (sk3,sk8)--> gia tri
		# Neu a thuoc sk2 hay sk7 va khong co gt cu the --> "xd"
		# Neu a khong thuoc sk2,sk3,sk7,sk8 --> "cxd"
		# Neu a co nhieu gt (vd : a = 2,a = 3)---> {2,3}
		local fact, value, j;
		value:= {};
		
		if Unify_In1(bien,[op(Fact_Kinds[2]),op(Fact_Kinds[7])]) then
			value:= value union {"xd"}; 
		fi;
		for fact in [op(Fact_Kinds[3]),op(Fact_Kinds[8])] do
		
			if Unify_Fact(AttrName(bien), lhs(fact)) then
				value:= value union {rhs(fact)};
			fi;
		od; 
		for fact in [op(Fact_Kinds[9])] do 
			if Unify_In1(bien, {rhs(fact)}) then 
				if member("xd", Get_Values([lhs(fact)])) then
					value := value union {lhs(fact)};
				fi;
			fi;
		end do;  
	
		# tim gia tri cua d khi biet d.f------------van chua dung cho moi truong hop---sua sau
		if member(type_Onet(bien),Obj_Types) and value ={"xd"} then
			for j to nops(Fact_Kinds[2]) do
				if not evalb(bien = Fact_Kinds[2][j]) and Is_DacTrung({Fact_Kinds[2][j]},bien) and type_Onet(Fact_Kinds[2][j])="PhuongTrinh" then
					value := value union {get_value(Fact_Kinds[2][j])};
				fi;
			od; 
		fi;

		if nops(value) >=2 then 
			if member("cxd",value) then
				value:={"cxd"};
			else 
				value := value minus {"xd"}; 
			fi;
		fi;
		
		if nops(value) = 0 then return "cxd";
		elif nops(value) = 1 then return op(value);
		else return value;
		fi;
	end: # get_value

	giatridon:=proc(giatri)
		# ham kiem tra giatri co phai la gia tri don khong
		# neu giatri khong la gia tri don thi tra ve vi tri 
		# vi du: giatri: =[1,2,{3,4}]-- gia tri phuc--> return 3;  
		# vi du: giatri:= [1,2,3]---> gia tri don---> return 0;  
		local i;
		for i to nops(giatri) do 
			if type(giatri[i],`set`) then 
				return i;
			fi;
		od;
		return 0;
	end: # giatridon  
		
	cacgiatridon:= proc(giatri)
		local gt;
		for gt in giatri do
			if giatridon(gt) <> 0 then 
				return false;
			fi;
		od; 
		return true;
	end : # cacgiatridon

	tachgiatri:= proc(giatri)
		# vi du: giatri:=[1,2,{3,4,5}]--->giatri:=[[1,2,3],[1,2,4],[1,2,5]]
		local k,i, temp, seq1, seq2, giatritemp;
		giatritemp:=giatri;
		
		while not cacgiatridon(giatritemp) do
			for i to nops(giatritemp) do
				k := giatridon(giatritemp[i]);
				if k <> 0 then
					seq1:= seq(giatritemp[i][j],j=1..k-1);
					seq2:= seq(giatritemp[i][j],j=k+1..nops(giatritemp[i]));
					temp:=map(s->[seq1,s,seq2],giatritemp[i][k]);
					giatritemp:= subs(giatritemp[i]=op(temp),giatritemp);
					break;
				fi; 
			od; 
		od;  
		return giatritemp;
	end: # tachgiatri

	#Get_Values's body
	if type(biens,`list`) then 
		# tim gia tri cua nhieu bien cung luc
		values:= [];
		for bien in biens do
			values:= [op(values),get_value(bien)];
		od;
		
		# neu trong values co gia tri phuc thi tach thanh cac gia tri don
		# vi du: values:=[1,2,{3,4}]--->values:=[[1,2,3],[1,2,4],[1,2,5]]
		if giatridon(values) <> 0 then
			values:= {op(tachgiatri([values]))};
		fi;
	else # tim gia tri cua mot bien
		values:= get_value(biens);
	fi; 
	return values;
end: # Get_Values

#Compute_Func :  Doc cau truc cua func vao maple de tinh gia tri cua ham voi doi so truyen vao la bien
GeometryConicSolver[Compute_Func]:=proc(func,bien,giatri,tri)
	local funcname, temp, gt, thaythe,i,ketqua,tinhgiatri ;
	global ObjsNew, OTypesNew, FactsNew,chiso;
	
	tinhgiatri:= proc(gt, n)
		local result, gtt, g;
		result:={}; 
		
		# Neu trong giatri co "xd" thi khong can tinh ham -> ham xd
		if member("xd",gt) then 
			result:={subs(thaythe,parse(temp[1]))}; 
			if func[3] <> [] then
				if n = 4 then
					result:=result union {temp[3][1],op(temp[5])};
				else
					ObjsNew:=[op(ObjsNew),temp[3][1]];
					OTypesNew:=[op(OTypesNew),temp[3][2]];
					FactsNew:=[op(FactsNew),temp[3][1],op(temp[5])];
				fi; 
			fi;
		else # co gia tri xac dinh
			gtt:= funcname(op(gt)); 
			
			# giá trị hàm tính được trả về sự kiện loại 6 ["Thuoc", A, E]
			if type(gtt ,`list` )and nops(gtt)=3 then 
				gtt[2]:=op(1,bien);
				gtt[3]:=op(2,bien);
			fi;
			
			if gtt <> NULL then
				
				#result:={subs(thaythe,parse(temp[1])) = gtt}; 
				#=> Trang sửa dòng này cho hàm trả về nhiều giá trị
				result := {};
				if type(gtt,`set`) then
					for g in gtt do
						result := result union {subs(thaythe,parse(temp[1])) = g}
					od;
				else 
					result:={subs(thaythe,parse(temp[1])) = gtt};
				fi;
				if func[3] <> [] then
					if n = 4 then
						#result:=result union {temp[3][1]= gtt,op(temp[5])};
						#=> Trang sửa dòng này cho hàm trả về nhiều giá trị
						if type(gtt,`set`) then
							for g in gtt do
								result := result union {temp[3][1]= g,op(temp[5])};
							od;
						else
							result:=result union {temp[3][1]= gtt,op(temp[5])};
						fi;
					else
						ObjsNew:=[op(ObjsNew),temp[3][1]];
						OTypesNew:=[op(OTypesNew),temp[3][2]];
						FactsNew:=[op(FactsNew),temp[3][1]= gtt,op(temp[5])];
					fi; 
				fi;
				result:= result union {subs(thaythe,parse(temp[1]))};
			fi;  
		fi;
		return result;   
	end: # tinh giatri
	
	# Compute_Func BODY
	thaythe:={};
	
	for i to nops(bien) do
		thaythe:= thaythe union {func[2][1][i] = bien[i]};
	od;
	if func[3] <> [] then
		if nargs = 4 then
			thaythe:=thaythe union {func[3][1] = tri};
		else
			thaythe:= thaythe union {func[3][1] = cat(func[3][1],chiso)};
			chiso:= chiso+1;
		fi; 
	fi;
	temp:= subs(thaythe,func);
	funcname:=parse(func[4]); 
	
	# Neu gia tri cua bien nhieu hon 1
	ketqua := {}; 
	if type(giatri,`set`) then
		for gt in giatri do
			ketqua := ketqua union {tinhgiatri(gt, nargs)};
		od; 
	else
		ketqua := tinhgiatri(giatri,nargs);
	fi;
	return ketqua;  
end proc: # Compute_Func

#Đọc cấu trúc của func vào mapke để tính giá trị của hàm với đối số truyền vào là biến
GeometryConicSolver[Compute_Func_VectoDoi]:=proc(func,bien,giatri,tri)
	local funcname, temp, gt, thaythe,i,ketqua,tinhgiatri ;
	global ObjsNew, OTypesNew, FactsNew,chiso;
	
	tinhgiatri:= proc(gt, n)
		local result, gtt;
		result:={}; 
		
		if member("xd",gt) then
			gtt:= funcname(op(bien)); 
			if gtt <> NULL then
				result:={gtt=subs(thaythe,parse(temp[1]))}; 
				# không ghi subs(thaythe,parse(temp[1]))=gtt: Vì tính toán hàm VectoDoi chi cho ra ket qua la 1 doi tuong xac dinh chu ko phải là giá trị cụ thể (VectoDoi(Vecto[M,N])=Vecto[N,M]--> đối tượng loại 9, Vecto[N,M]=VectoDoi(Vecto[M,N])--> sẽ hiểu nhầm là đối tượng loại 4)
				if func[3] <> [] then
					if n = 4 then
						result:=result union {gtt=temp[3][1],op(temp[5])};
					else
						ObjsNew:=[op(ObjsNew),temp[3][1]];
						OTypesNew:=[op(OTypesNew),temp[3][2]];
						FactsNew:=[op(FactsNew),temp[3][1]= gtt];
					fi; 
				fi;
				result:= result union {subs(thaythe,parse(temp[1]))};
			fi;  
		fi;
		return result;   
	end: # tinh giatri

	#Compute_Func's body : thay thế biến vào hàm
	thaythe:={};
	for i to nops(bien) do
		thaythe:= thaythe union {func[2][1][i] = bien[i]};
	od;
	if func[3] <> [] then
		if nargs = 4 then
			thaythe:=thaythe union {func[3][1] = tri};
		else
			thaythe:= thaythe union {func[3][1] = cat(func[3][1],chiso)};
			chiso:= chiso+1;
		fi; 
	fi;
	
	temp:= subs(thaythe,func); 
	funcname:=parse(func[4]); 
		
	# Neu gia tri cua bien nhieu hon 1
	ketqua := {}; 
	if type(giatri,`set`) then
		for gt in giatri do
			ketqua := ketqua union {tinhgiatri(gt, nargs)};
		od; 
	else
		ketqua := tinhgiatri(giatri,nargs);
	fi;
	return ketqua;  
end proc: # Compute_Func