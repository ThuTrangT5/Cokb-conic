#Hàm xử lý nghiệm

Signof := proc(expr)
	local  dau_tong, dau_tich, dau_ham;
	
	#dấu tổng
	dau_tong := proc(expr)
		local x, oplist, i, flag;
		
		oplist := [op(expr)];
		x := Signof(oplist[1]);
		
		if evalb(x > 0) = true then 
			flag := 1;
		elif evalb(x < 0) = true then 
			flag := -1;
		elif evalb(x = 0) = true then 
			flag := 0;
		else 
			return(expr);
		fi;
		
		for i from 2 to nops(oplist) do
			x := Signof(oplist[i]);
			if evalb(x > 0) = true and (flag >= 0) then 
				flag := 1;
			elif evalb(x < 0) = true and (flag <= 0) then 
				flag := -1;
			elif evalb(x = 0) = true then  ;
			else 
				return(expr);
			fi;
		od;
		return(flag);
	end: # dau_tong

	#dấu tích
	dau_tich := proc(expr)
		local x, oplist, i, flag;
		oplist := [op(expr)] ;
		x := Signof(oplist[1]);
		
		if evalb(x > 0) = true then flag := 1;
		elif evalb(x < 0) = true then flag := -1;
		elif evalb(x = 0) = true then return (0);
		else return(expr);
		fi;
		
		for i from 2 to nops(oplist) do
			x := Signof(oplist[i]);
			if evalb(x > 0) = true then  ;
			elif evalb(x < 0) = true then flag := -flag;
			elif evalb(x = 0) = true then  return (0);
			else return(expr);
			fi;
		od;
		return(flag);
	end: # dau_tich

	dau_ham := proc(btham)
		local tenham, doiham;
		
		tenham := convert(op(0,btham), string);
		doiham := op(1,btham);
		
		if tenham = "abs" then
			if evalb(Signof(doiham) = 0) = true then 
				return(0);
			else 
				return(1);
			fi;
		fi;
		
		if tenham = "arcsin" then
			if evalb(Signof(doiham) > 0) = true then return(1);
			elif evalb(Signof(doiham) < 0) = true then return(-1);
			elif evalb(Signof(doiham) = 0) = true then return(0);
			else return (btham);
			fi;
		fi;
		# cac truong hop khac
		return (btham);
	end: # dau_ham

	if evalb(expr > 0) = true then 
		return(1);
	elif evalb(expr < 0) = true then 
		return(-1);
	elif  evalb(expr = 0) = true then 
		return(0);
	elif type(expr, function) then 
		return (dau_ham(expr));	
	elif type(expr,`^`) and evalb(op(1,expr)=0) = true 
		then return(0);
	elif type(expr,`^`) and type(op(2,expr),even) 
		then return(1);
	elif type(expr,`^`) and type(op(2,expr),fraction) and type(op(2, op(2,expr)), even) then 
		return(1);
	elif type(expr,`^`) and type(op(2, expr),odd) then 
		return( Signof(op(1,expr)) ^ op(2,expr));
	elif type(expr,`+`) then
		return (dau_tong(expr) ); # xac dinh dau cua tong
	elif type(expr,`*`) then
		return (dau_tich(expr) ); # xac dinh dau cua tich
	fi;
	#Truong hop khong xac dinh duoc dau cua bieu thuc
	return(expr);
end: #---Signof

GeometryConicSolver[Xuly_RootOf]:=proc(tapnghiem)
	# Loai bo nghiệm RootOf neu khong chuyen duoc ra dang thuong.
	local L1, taphop, fact, Lng;
	
	if tapnghiem = [] then 
		return ([]);
	fi;
	
	taphop := tapnghiem[1];
	
	if SearchText("RootOf", convert(taphop, string)) = 0 then
		return( [taphop, op(Xuly_RootOf(tapnghiem[2..nops(tapnghiem)]))]);
	fi;
	
	for fact in taphop do
		if SearchText("RootOf", convert(rhs(fact), string)) > 0 then
			Lng := [allvalues(rhs(fact))];
		
			#VD: e2 := RootOf(_Z^3-1); 
			#    allvalues(e2);KQ:1, -1/2+1/2*I*3^(1/2), -1/2-1/2*I*3^(1/2)
			if Lng <> [] and SearchText("RootOf", convert(Lng, string)) = 0 then
				L1 := map(s-> (`minus`(taphop,{fact}) union {lhs(fact) = s}), Lng);
			else 
				L1 := [];
			fi;
			break;
		fi;
	end do;
	return (Xuly_RootOf([op(L1), op(2..nops(ListSet),ListSet)]));
end: # Xuly_RootOf

#Loại bỏ nghiệm phức 
GeometryConicSolver[Xuly_Phuc]:=proc(nghiem)
	#???
end: # Xuly_Phuc

GeometryConicSolver[MySolve]:=proc(eqns,vars)
	local tapnghiem,nghiem, result, flag,fact, expr;
	result:={};
	
	#B1: Giai phuong trinh hay he phuong trinh
	tapnghiem := [solve(eqns, vars)]; 
	# VD: nghiem={{a=0,b=3},{a=1,b=2}}
	tapnghiem := Xuly_RootOf(tapnghiem);

	#B2: Loai nghiem RootOf,nghiem an, nghiem phuc
	for nghiem in tapnghiem do
		flag := true;
		for fact in nghiem do
			expr := rhs(fact);
			if (nargs = 3 and evalb(Signof(expr) <= 0) = true) or SearchText("I", convert(expr, string)) > 0 then
				flag := false;break;
			fi;
		od;
		if flag then 
			result := {op(result), nghiem};
		fi;
	od;
	return result;  
end: # MySolve

GeometryConicSolver[MySolve0]:=proc(eqns,vars)
	local result,nghiem,tapnghiem;
	result:={};
	
	#B1: Giai phuong trinh hay he phuong trinh
	tapnghiem:={solve(eqns,vars)};    #VD: nghiem=[{a=0,b=3},{a=1,b=2}]

	#B2: Loai nghiem RootOf,nghiem am, nghiem phuc
	for nghiem in tapnghiem do
		result:=result union {nghiem};
	od:
	return result;
end: # MySolve

GeometryConicSolver[SolveFact]:=proc(fact, vars::set) # chua dung den
	#Giai <fact> thuoc loai 3, 4 hay 5 de tinh thuoc tinh ve trai hoac tinh theo thuoc tinh duoc ghi trong tap hop <vars> .dieu kien: <fact> phai thuoc loai 3, 4 hay 5
	local expr, list1;

	if nargs = 3 then 
		expr := simplify(dongian_ptO(fact)); list1 := MySolve( expr, vars);
	else 
		list1 := [MySolve(fact, SetVars(lhs(fact), nameO) )];
	fi;
	if list1 = {} then return (NULL);
	fi;
	
	return (list1[1]);
end: # SolveFact

GeometryConicSolver[Test]:=proc(fact)# chua dung den
	#  Kiem tra su mau thuan cua su kien moi loai `=` voi nhung su kien da co trong,VD: a = 2*c va a = sqrt(3)*c  
	local expr, fact1, vars1, vars,f;
	
	if type(fact, set) or type(fact, list) then
		for f in fact do
			if Test(f) = false then 
				return(false);
			fi;
		od;
	fi;
	
	if not type(fact, `=`) then 
		return(true);
	fi;
	
	vars := Set_Vars(fact);
	if nops(vars) <> 2 then 
		return(true);
	fi;
	
	for fact1 in {op(Fact_Kinds[4]),op(Fact_Kinds[5])} do
		vars1 := Set_Vars(fact1);
		if nops(vars1) = 2 and Unify_in(vars, vars1) and MySolve({fact, fact1}, vars) = {} then  
			return(false);
		fi;
	od;
	# Khong phat hien thay mau thuan
	return (true);
end proc: # Test
