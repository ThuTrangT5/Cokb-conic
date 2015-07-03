#GeometryConicSolver
#1. Khởi tạo package
#2. Đọc file cấu trúc COKB
#3. Đọc đề bài và ghi nhận mô hình bài toán
#4. Các hàm hỗ trợ cơ bản
#5. Phân loại sự kiện 
#6. Xử lý theo mô hình bài toán trên Onet
#7. Hàm hỗ trợ giải bài toán
#8. Hàm xử lý nghiệm
#9. Giải toán
#10.


packageUrl := currentdir();
mplUrl := cat(packageUrl,"\\mpl files\\");

#1. Khởi tạo package
	with(geometry):
	#Định nghĩa chiều x,y cho các hình conic
	_EnvHorizontalName := 'x': _EnvVerticalName := 'y':
	GeometryConicSolver := table():

#2. Đọc file cấu trúc COKB
read cat(mplUrl,"read_cokb_files.mpl");

#3. Đọc đề bài và ghi nhận mô hình bài toán
read cat(mplUrl,"read_exercise_files.mpl");

#4. Các hàm hỗ trợ cơ bản
read cat(mplUrl,"util_functions.mpl");

#5. Phân loại sự kiện
read cat(mplUrl,"classify_facts.mpl");

#6. Xử lý theo mô hình bài toán trên Onet
read cat(mplUrl,"classify_facts_Onet_exercises.mpl");

#7. Hàm hỗ trợ giải bài toán
read cat(mplUrl,"util_exercise_functions.mpl");

#8. Hàm xử lý nghiệm
read cat(mplUrl,"util_result_functions.mpl");

#9. Giải toán
read cat(mplUrl,"sol_exercise.mpl");

#10.
GeometryConicSolver[Kind_Fact_Tr]:=proc(fact)
	global Objects, Obj_Types, OAttrs, OAttr_Types,test; 
	local temp, i, mpType;
	
	mpType:= whattype(fact);	
	if type(fact, list) then
		#Loai 1: Su kien thong tin ve loai doi tuong
		if nops(fact)=2 and 
		 (member(fact[1],Objects) or (ValidStructName_Onet(fact[1]))and SubList([op(fact1)],Objects)) and
		 type(fact[2],string) and member(NameType(fact[2]),Obj_Types) then
		 
		 print("loai 1");
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
			if Is_RelationType(temp) then
				print("loai 6");
				return 6; 
			fi; 
		fi;	
	#Loai 2: Su kien ve tinh xac dinh cua 1 dt/tt
	elif Is_Element(fact) then 
		print("loai 2");
		return 2; 
			
	elif type(fact,`=`) and Is_Element(lhs(fact)) then 
		test := lhs(fact);
		test := Is_Element(lhs(fact));
		
		test := rhs(fact);
		test := Is_Element(rhs(fact));
		test := type(rhs(fact));
		test := Set_Vars(rhs(fact));
		
		#Loai 4:Sự kiện về sự bằng nhau giữa một đối tượng hay một thuộc tính với một đối tượng hay một thuộc tính khác
		if Is_Element(rhs(fact)) or (type(rhs(fact),list) and Has_Element( Set_Vars(rhs(fact)) )) then
			print("loai 4");
			return 4;

		#Loai 9: <doi tuong> = <ham> 
		elif Is_Function(rhs(fact)) then
			print("loai 9");
			return 9;
		
		#Loai 3: Su kien ve su xac dinh cua 1dt/tt thong qua bieu thuc hang
		elif not Has_Element( Set_Vars(rhs(fact)) ) then
			print("loai 3");
			return 3;
			
		#Loai 5: Su kien ve su phu thuoc cua 1dt/tt theo cac dt/tt khac thong qua 1 cong thuc tinh toan hoac la dang thuc theo cac dt/tt
		else 
			print("loai 5 - 1");
			return 5;
		fi;
	
	#Loai 5:
	elif type(fact,`=`) and (Has_Element( Set_Vars(lhs(fact)) ) or Has_Element( Set_Vars(rhs(fact)) )) then
		print("loai 5 - 2");
		return 5;
	
	# Loai 7: Tinh xac dinh cua mot ham 
	elif Is_Function(fact) then
		print("loai 7");
		return 7;
	
	elif type(fact,`=`) and Is_Function(lhs(fact)) then
		# Loai 10:Su kien ve su bang nhau cua 1ham voi 1ham khac:<ham>=<ham>.
		if Is_Function(rhs(fact)) then
			print("loai 10");
			return 10; 
	
		# Loai 8: Tinh xac dinh cua mot ham thong qua bieu thuc hang:<ham>= <bieu thuc háº±ng>.
		elif (Set_Vars(rhs(fact)))<>{} then 
			if ((op(0,rhs(fact))=`+`) or (op(0,rhs(fact))=`*`)) and Has_Element(op(Set_Vars(rhs(fact)))) and not Is_Function(rhs(fact)) then
				# Loai 11: Su phu thuoc cua 1 ham thong qua cac ham khac:<ham>=<bieu thuc ham/dt>
				print("loai 11");
				return 11;
			else
				print("loai 8 = 1");
				return 8;
			fi;		
		else 
			print("loai 8 - 2");
			return 8;
		fi;
	
	fi;
	print("loai 0");
	return 0;
end proc: # Kind_Fact

GeometryConicSolver[OrderRulesByGoals] := proc(rules)
	local goalOfRules, hypoOfRules, orderedRules, fact2s, goalsSet, checkHypos, checkGoals, r, g, intersectSet;
	#orderedRules := [[],[],[]];
	orderedRules := [[],[]];
	
	fact2s := {op(Fact_Kinds[2])};
	goalsSet := {op(Goals)};
	
	
	for r in rules do
		goalOfRules := GetGoalNames(r[4][2]);
		hypoOfRules := r[4][1];
		
		#Hypos đã có trong Fact2, đã xác định
		checkHypos := verify({op(hypoOfRules)}, fact2s, `subset`);
		#Goals phải chưa xác định, checkGoals = false
		checkGoals := verify({op(goalOfRules)}, fact2s, `subset`);
		
		if (checkGoals = false) and (checkHypos = true) then
			#check goalOfRules có chức các thành phần trong Goals của bài toán không
			intersectSet := goalOfRules intersect goalsSet;
			if intersectSet = {} then
				orderedRules[2] := [op(orderedRules[2]), r];
			else
				# ưu tiên những rules chứa goals là tập con của Goals bài toán
				orderedRules[1] := [op(orderedRules[1]), r];
			fi;
		fi;		
	od;

	#return [op(orderedRules[1]), op(orderedRules[2]), op(orderedRules[3])];
	return [op(orderedRules[1]), op(orderedRules[2])];
end proc:

GeometryConicSolver[GetGoalNames] := proc(goals) 
	local goalNames, goal;
	goalNames := {};
	
	for goal in goals do
		if type(goal,`symbol`) or type(goal,`function`) then
			goalNames := {op(goalNames), goal};
		elif type(goal,`=`) then
			goalNames := {op(goalNames), lhs(goal)};
		fi;
	od;
	return goalNames;
end proc:

DuongThang_pt2d := proc(M,N)
	local f,fM,fN,vtcp,vtpt,fVT,kq,ucln;

	f := a*x + b*y + c = 0;
	fM := subs({x=M[1],y=M[2]},f);
	fN := subs({x=N[1],y=N[2]},f);
	vtcp := [M[1]-N[1],M[2]-N[2]]; #vecto chỉ phương(a,b)
	ucln := gcd(vtcp[1],vtcp[2]);#tìm ước chung lớn nhất
	vtcp := [vtcp[1]/ucln,vtcp[2]/ucln]; #tối giản vtcp
	vtpt := [-vtcp[2],vtcp[1]]; #vecto pháp tuyến(-b,a)
	fVT := {a=vtpt[1], b=vtpt[2]};

	kq := solve({fM,fN,op(fVT)},{a,b,c});

	return subs(kq,f);
end proc:

TiepTuyenElipQuaM := proc(E,M,d)
	global Objects,Obj_Types,Fact_Kinds,Sol, FactSet;
	local sol0,pt1,sol1,pt2,sol2,pt3,sol3,sol4,result, ef, df, xM, yM, x0, y0, x1, y1, test;
lprint("Goto TiepTuyenElipQuaM");

	ef := Get_Values(E.f1);
	df := subs({x^2 = x*(x0), y^2 = y*(y0)}, ef);
	xM := Get_Values(M.x);
	yM := Get_Values(M.y);
	
	if xM = "cxd" or yM = "cxd" then return []; fi;
	
	# Kiem tra M co thuoc E hay khong
	test := subs({x = xM, y = yM}, lhs(ef));
	if test = 1 then 
		df := subs({x0 = xM, y0 = yM}, df);
		
		sol1 := [["Bai toan mau"], [],{E.f1=ef,M=[xM,yM]},{["Thuoc",M,E]} ];
		sol2 := [["Bai toan mau"], [],{E.f1=ef, ["Thuoc", M,E], ["Thuoc", M,d], ["TiepTuyen",d,E]},{d.f = df}];
		Sol := [op(Sol), sol1, sol2];
		Fact_Kinds[3]:= [op(Fact_Kinds[3]), d.f = df];
		return [];
	fi;
	
	# Goi M0 la tiep diem cua E va d
	sol0 := [["Bai toan mau"], [], {"Tao doi tuong moi"}, {M0=[x0,y0],["Thuoc",M0, E], ["Thuoc", M0, d]}];
	
	pt1 := subs({x = x0, y = y0}, ef);
	sol1 := [["Bai toan mau"], [], {["Thuoc",M0, E]}, {pt1}];
	
	pt2 := df;
	sol2 := [["Bai toan mau"], [], {["Thuoc",M0, d], ["Thuoc",M0, E], ["TiepTuyen",d,E]}, {d.f=pt2}];
	
	pt3 := subs({x = xM, y = yM}, df);
	sol3 := [["Bai toan mau"], [], {["Thuoc",M, d]}, {pt3}];
	
	result:= [solve({pt1,pt3}, {x0, y0})];
	sol4 := [["Bai toan mau"], [], {pt1,pt3}, {result}];	
	
	if nops(result)= 0 then return []; fi; 

	x0 :=  rhs(result[1][1]);
	y0 := rhs(result[1][2]);
	
	if nops(result) = 2 then	
		x1 :=  rhs(result[2][1]);
		y1 := rhs(result[2][2]);
		
		df := {subs(result[1], d.f=pt2), subs(result[2], d.f=pt2)};
		sol1 := [["Bai toan mau"], [], {d.f=pt2, result}, {d.f= df}];
		sol2 := [["Bai toan mau"], [], {"Tao doi tuong moi"}, {M1=[x1,y1]}];
		sol2 := [["Bai toan mau"], [], {d.f = {rhs(df[1]), rhs(df[2])}} , {d.f=rhs(df[1]), d1.f=rhs(df[2])}];
		
		Sol := [op(Sol), sol1, sol2];
		Fact_Kinds[3]:= [op(Fact_Kinds[3]), M0=[x0,y0], M1=[x1,y1], d.f=rhs(df[1]), d1.f=rhs(df[2])];
		Fact_Kinds[2]:= [op(Fact_Kinds[2]), M0, M1, d.f, d1.f];
		Objects := [op(Objects), M0, M1, d1];
		Obj_Types := [op(Obj_Types), "Diem", "Diem", "DuongThang"];
		Fact_Kinds[6] := [op(Fact_Kinds[6]), ["Thuoc",M0, E], ["Thuoc", M0, d], ["Thuoc",M1, E], ["Thuoc", M1, d1], ["TiepTuyen", E,d1]];
		FactSet:= FactSet union {M0=[x0,y0], M1=[x1,y1], d.f=rhs(df[1]), d1.f=rhs(df[2])};
	else 
		Fact_Kinds[2]:= [op(Fact_Kinds[2]), M0, d.f];
		Fact_Kinds[3]:= [op(Fact_Kinds[3]), M0=[x0, y0], d.f = rhs(df[1])];	
		Objects := [op(Objects), M0];
		Obj_Types := [op(Obj_Types), "Diem"];
		Fact_Kinds[6] := [op(Fact_Kinds[6]), ["Thuoc",M0, E], ["Thuoc", M0, d]];
		Sol := [op(Sol), sol0, sol1, sol2, sol3, sol4];
		FactSet:= FactSet union {M0=[rhs(result[1][1]), rhs(result[1][2])]};
	fi;
	(*if nops(result) = 2 then
		x1 :=  rhs(result[2][1]);
		y1 := rhs(result[2][2]);
		Fact_Kinds[3]:= [op(Fact_Kinds[3]), M1=[x1,y1]];
		Fact_Kinds[3]:= [op(Fact_Kinds[3]), d1.f = subs(result[2], df)];
				
		Objects := [op(Objects), M1, d1];
		Obj_Types := [op(Obj_Types), "Diem", "DuongThang"];
		FactSet:= FactSet union {M1=[x1,y1]};
		Sol := [op(Sol), [["Bai toan mau"], [], {"Tao doi tuong moi"}, {M1=[x1,y1], d1,["Thuoc",M1, E], ["Thuoc", M1, d1], d1.f = subs(result[2], df)}]];
	fi;*)
	
	return [];
end proc:

TimThanhPhanElip := proc(E)
	local a,b,c,e,F1,F2,A1,A2,B1,B2,TrucLon,TrucNho,TieuCu,ptct;
	
	ptct := Get_Values(E.f1);
	a := sqrt( 1/(coeff(lhs(ptct),x,2)));
	b := sqrt(1/coeff(lhs(ptct),y,2));
	
	if (convert(a-b,float)>0) then
		c := sqrt(a^2 - b^2);		
		TrucLon := 2*a;
		TrucNho := 2*b
	else
		c := sqrt(b^2 - a^2);
		TrucLon := 2*b;
		TrucNho := 2*a
	fi;
	TieuCu := 2*c;
	e := c/a;
	F1 := [-c,0];
	F2 := [c,0];
	A1 := [-a,0];
	A2 := [a,0];
	B1 := [-b,0];
	B2 := [b,0];
	return [a,b,c,e,F1,F2,A1,A2,B1,B2,TrucLon,TrucNho,TieuCu];	
end proc:

TimDiemThuocElip := proc(E,M,n)
	#global Objects,Obj_Types,Fact_Kinds,Sol, FactSet;
	global Sol, FactSet, Fact_Kinds;
	local ea,ts, mf1, mf2, pt, ef, efM, xM, yM, result, s;
	
	ea := Get_Values(E.a);
	ea := 4;
	ts:= Get_Values(E.e);# tâm sai
	mf1 := ea + ts*(M.x);
	mf2 := ea - ts*(M.x);
	pt := (mf1 = n * mf2);
	xM := solve(pt,M.x);
	
	ef := Get_Values(E.f1);
	efM := subs({x = M.x, y = M.y}, ef); # pt elip theo M
	pt := subs(x = xM, ef);
	yM := solve(pt, y);
	
	result := {};
	if nops([xM]) > nops([yM]) then
		result := { [[xM][1], yM], [[xM][2], yM] };
	else 
		result := { [xM, [yM][1]], [xM, [yM][2]] };
	fi;
	
	s    := [[],[],[],[],[]];
	s[1] := [["Bai toan mau"], [{["Thuoc",M,E]}, {(M.x)^2/(E.a)^2 + (M.y)^2/(E.b)^2 = 1, Doan[M,F1]= E.a + (E.e)*(M.x), Doan[M,F2]= E.a - (E.e)*(M.x)}], {["Thuoc",M,E], E.f1 = ef}, {efM, Doan[M,E.F1] = mf1, Doan[M,E.F2] = mf2}];
	s[2] := [["Bai toan mau"],[],{Doan[M,E.F1] = mf1, Doan[M,E.F2] = mf2, Doan[M,E.F1] = n*Doan[M,E.F2]},{mf1 = n * mf2}];
	s[3] := [["Bai toan mau"], [], {mf1 = n * mf2}, {M.x = xM}];	
	s[4] := [["Bai toan mau"], [], {efM, M.x = xM}, {M.y = yM}];
	s[5] := [["Bai toan mau"], [], {M.x = xM, M.y = yM}, {M = result[1], M = result[2]}];
	
	Sol := [op(Sol), op(s)];
	#Fact_Kinds[2] := [op(Fact_Kinds[2]), M];
	Fact_Kinds[3] := [op(Fact_Kinds[3]), M = result[1], M = result[2]];
	FactSet := FactSet union {M = result[1], M = result[2]};
	return [];
end proc:


GeometryConicSolver[GiaiHePhuongTrinh] := proc(hept, tapthamso)
	local ptbac2, ptbac1, kq, pt, expr, bacpt, d1, d2, a, b, temp, d;
	
	ptbac2 := {};
	ptbac1 := {};
	kq := [{}, {}, {}, {}]; # 0, 1, 2, nhiều giao điểm theo tham số
	
	for pt in hept do
		expr := lhs(pt) - rhs(pt);
		bacpt := max(degree(expr,x), degree(expr,y));# bậc của phương trình 
		if bacpt = 2 then
			ptbac2 := ptbac2 union {pt};
		elif bacpt = 1 then
			ptbac1 := ptbac1 union {pt};
		fi;
	od;
	
	d1 := []; # d1 = [a1, b1, c1]
	d2 := []; # d2 = [a2, b2, c2]
		
	if nops(ptbac2) = 0 then # Giải hệ gồm các phương trình bậc nhất
		# Dạng tìm giao điểm của 2 đường thẳng
		pt := ptbac1[1];
		pt := lhs(pt) - rhs(pt);
		a := [coeff(pt,x), coeff(pt,y), pt - coeff(pt,x)*x - coeff(pt,y)*y];
		
		pt := ptbac1[2];
		pt := lhs(pt) - rhs(pt);
		b := [coeff(pt,x), coeff(pt,y), pt - coeff(pt,x)*x - coeff(pt,y)*y];
		
		# Trường hợp vô nghiệm
		temp := solve({a[1]/b[1] = a[2]/b[2], a[1]/b[1] <> a[3]/b[3]}, tapthamso);
		if nops({temp}) > 0 then kq[1] := temp; fi;
		
		# Có 1 nghiệm
		temp := solve({a[1]/b[1] <> a[2]/b[2]}, tapthamso);
		if nops({temp}) > 0 then kq[2] := temp; fi;
		
		# Có vô số nghiệm
		temp := solve({a[1]/b[1]= a[2]/b[2], a[1]/b[1] = a[3]/b[3]}, tapthamso);
		if nops({temp}) > 0 then kq[4] := temp; fi;
		
	elif nops (ptbac1) = 0 then # Giải hệ gồm các phương trình bậc 2
		
	else # gồm 1 bậc 1 và 1 bậc 2
		# giải pt bậc 1 theo y rồi thế vào pt bậc 2
		temp := solve({ptbac1[1]}, y);
		temp := subs(temp, ptbac2[1]);
		temp := lhs(temp) - rhs(temp);
		temp := collect(temp,x);
		
		# Tính giá trị delta
		d  := (coeff(temp,x))^2 - 4*(coeff(temp,x,2))*(coeff(temp,x,0)); 
		
		# Có 0 nghiệm
		temp := solve({d<0}, tapthamso);
		if nops({temp}) > 0 then kq[1] := {temp}; fi;
		
		# Có 1 nghiệm
		temp := solve({d=0}, tapthamso);
		if nops({temp}) > 0 then kq[2] := {temp}; fi;
		
		# có 2 nghiệm
		temp := solve({d>0}, tapthamso);
		if nops({temp}) > 0 then kq[3] := {temp}; fi;
	fi;
	
	return kq;
end proc: