#Đọc đề bài và ghi nhận mô hình bài toán
#This file include 2 main function : Reset_Onet and ReadExer

#Reset_Onet: Hàm khởi tạo lại các biến cơ bản của một bài toán
GeometryConicSolver[Reset_Onet] := proc () 
	global Hypos, Goals, Objects, Obj_Types, Facts, Fact_Kinds, OAttrs, OAttr_Types, Sol, Params, Funcs, Func_Types, Functions, FactSet; 
	Params := {}; 
	Objects := []; 
	Obj_Types := []; 
	OAttrs := []; 
	OAttr_Types := []; 
	Facts := {}; 
	Fact_Kinds := [[], [], [], [], [], [], [], [], [], [], []]; 
	Hypos := {}; 
	Goals := []; 
	Sol := []; 
	Funcs := []; 
	Func_Types := []; 
	Functions := {};
	FactSet := {};
end proc:#------------Reset_Onet

#ReadExer: Hàm đọc mô hình bài toán
GeometryConicSolver[ReadExer] := proc (url::string)
	local line, fd, read_objects, read_facts, read_funcs, read_goals, read_params, update; 
	global Hypos, Goals, Params, Objects, Obj_Types, Facts, Fact_Kinds, OAttrs, OAttr_Types, Funcs, Func_Types, Functions, FactSet, Argumentations; 
	
	update := proc (ex_vars)
		local vars, i, j; 
		vars := `minus`(ex_vars, `union`(`union`(convert(Objects, set), convert(OAttrs, set)), convert(Funcs, set)));
		for i in vars do 
		    if Is_Function(i) then 
			if type_Onet(i) = "type?" then next end if; 
			Funcs := [op(Funcs), i]; 
			Func_Types := [op(Func_Types), type_Onet(i)]; 
			for j in [op(i)] do 
			    update(Set_Vars(j));
			end do;
		    elif ValidStructName_Onet(i) and Unify_In1({op(i)}, Objects) then 
			if type_Onet(i) = "type?" then next end if; 
			Obj_Types := [op(Obj_Types), type_Onet(i)]; 
			Objects := [op(Objects), i];
		    elif type(i, function) and op(0, i) = `.` and not Unify_In1(op(1, i), Objects) and ValidStructName_Onet(op(1, i)) and Unify_In1({op(op(1, i))}, Objects) then 
			if type_Onet(i) = "type?" then next end if; 
			Obj_Types := [op(Obj_Types), type_Onet(op(1, i))]; 
			Objects := [op(Objects), op(1, i)]; 
			OAttrs := [op(OAttrs), i]; 
			OAttr_Types := [op(OAttr_Types), type_Onet(i)];
		    else 
			if type_Onet(i) = "type?" then next end if; 
			OAttrs := [op(OAttrs), i]; OAttr_Types := [op(OAttr_Types), type_Onet(i)];
		    end if;
		end do;
	end proc;#---------update
	
	read_params := proc () 
		line := readline(fd); 
		while line <> 0 and SearchText("end_parameters", line) = 0 do 
		       Params := `union`(Params, {parse(line)}); line := readline(fd);
		end do;
	end proc; #------------------read_params
		
	read_objects := proc () 
		local k, ten1, kieu1, n1; 
		line := readline(fd); 
		while line <> 0 and SearchText("end_objects", line) = 0 do 
		     k := SearchText(":", line); 
		     if 0 < k then 
			   ten1 := [parse(substring(line, 1 .. k-1))]; 
			   n1 := nops(ten1); 
			   kieu1 := convert(parse(substring(line, k+1 .. length(line))), string); 
			   Objects := [op(Objects), op(ten1)]; 
			   Obj_Types := [op(Obj_Types), `$`(kieu1, n1)];
		     end if; 
		     line := readline(fd);
		end do;
	end proc; #---------------------read_objects
	
	read_facts := proc () 
		local k, s, ex_vars, ex; 
		line := readline(fd); 
		ex_vars := {};

		while line <> 0 and SearchText("end_facts", line) = 0 do 
		     s := [parse(line)]; 
		     for ex in s do
			  k := Kind_Fact(ex);		  
			  if 1 <= k and k <= 11 then 
			      Facts := {op(Facts), ex}; 
			      Fact_Kinds[k] := [op(Fact_Kinds[k]), ex]; 
			      ex_vars := `union`(ex_vars, Set_Vars(ex));
			  end if;
		     end do; 
		     line := readline(fd);
		end do; 
		update(ex_vars);
	end proc;#------------read_facts
	
	read_funcs := proc () 
		local k, s, ex_vars, ex; 
		line := readline(fd); 
		ex_vars := {}; 
		while line <> 0 and SearchText("end_functions", line) = 0 do 
		      s := [parse(line)]; 
		      for ex in s do k := Kind_Fact(ex); 
			   if 1 <= k and k <= 11 and not Unify_In1(ex, Functions) then 
				 Functions := {op(Functions), ex}; 
				 Fact_Kinds[k] := [op(Fact_Kinds[k]), ex]; 
				 ex_vars := `union`(ex_vars, Set_Vars(ex));
			   end if;
		      end do; 
		      line := readline(fd);
		end do; 
		update(ex_vars); 
	end proc;#------------read_funcs 
	
	read_goals := proc () 
		local s, ex, ex_vars, k; 
		line := readline(fd); 
		ex_vars := {}; 
		while line <> 0 and SearchText("end_goal", line) = 0 do 
		     s := [parse(line)]; 
		     for ex in s do 
			  k := Kind_Fact(ex); 
			  if 1 <= k and k <= 11 or member(ex, Params) and not Unify_In1(ex, Goals) then 
			       Goals := [op(Goals), ex]; 
			       ex_vars := `union`(ex_vars, Set_Vars(ex));
			  end if;
		     end do; 
		     line := readline(fd);
		end do; 
		update(ex_vars);
	end proc;#------------read_goals
	
	# Main 
	Reset_Onet();
	fd := fopen(url, READ, TEXT);
	line := readline(fd); 
	while line <> 0 and SearchText("begin_exercise", line) = 0 do 
	      line := readline(fd);
	end do;
	while line <> 0 and SearchText("end_exercise", line) = 0 do 
	     line := readline(fd); 
	     while line <> 0 and SearchText("begin_hypothesis", line) = 0 and SearchText("end_exercise", line) = 0 do
		  line := readline(fd);
	     end do; 
	     if 0 < SearchText("end_exercise", line) then 
		  fclose(fd); 
		  return NULL;
	     end if; 
	     line := readline(fd); 
	     while line <> 0 and SearchText("end_hypothesis", line) = 0 do 
		  if 0 < SearchText("parameters:", line) then 
		       read_params(); 
		  elif 0 < SearchText("objects:", line) then 
		       read_objects();
		  elif 0 < SearchText("facts:", line) then 
		       read_facts(); 
		  elif 0 < SearchText("functions:", line) then 
		       read_funcs();
		  end if; 
		  line := readline(fd);
	     end do; 
	     Hypos := `union`(Facts, Functions); 
	     line := readline(fd); 
	     while line <> 0 and SearchText("begin_goals", line) = 0 do 
		  line := readline(fd);
	     end do; 
	     read_goals(); 
	     line := readline(fd);
	     
	     # read Biện luận
	     while line <> 0 and SearchText("begin_argumentations", line) = 0 do 
		  line := readline(fd);
	     end do;
	     
	     Argumentations := [];
	     line := readline(fd);
	     while line <> 0 and SearchText("end_argumentations", line) = 0 do
		  Argumentations := [op(Argumentations), parse(line)];
		  line := readline(fd);
	     end do;
	end do; 
	fclose(fd); 
end proc:#------------ReadExer


