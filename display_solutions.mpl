# Hiển thị lời giải cho bài toán

(*GeometryConicSolver[Display_Solutions]:=proc()
	(*global Sol, TrSol;
	local hiddenDeduces, sol_step;
	TrSol := [];
	
	hiddenDeduces := ["Deduce_From3s","Deduce_ObjRules"];
	for s in Sol do 
		if (member(op(1,s), hiddenDeduces) = false then
			sol_step[1] := op(3,s);
			sol_step[2] := op(4,s);
			sol_step[3] := op(2,op(4,op(2,s)));
			
		fi;
	od;*)
	
	
	for Goal in Goals do
		Sol:=[]; 
		
		Goal_ThehienTrongLoiGiai:=[Goal];
		if Test_Goal(Goal,FactSet) then 
			#printf("(@_@)Bai toan khong can giai\n");
			Output_Result(Goal_ThehienTrongLoiGiai);
		else
			Goal_ThehienTrongLoiGiai:=[Goal];
			Determine_Goal(Goal);# với Goal là r1(M,E) thì thể hiện ra cả những lời giải có r1(M,E),M.x, E.a,E.c;
			Output_Result(Goal_ThehienTrongLoiGiai);
		fi;
		Sols:={op(Sols),Sol};
	od;
end proc:

*)