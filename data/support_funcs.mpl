Elip_ptct := proc(pt) 
	local f1,a,b,st,a2,a1,b2,b1,fx,fy,x0,y0,msc;
	f1 :=  lhs(pt)-rhs(pt); (* pt quy ve dang chi co ve trai*)
	a2 := coeff(f1,x,2);
	b2 := coeff(f1,y,2); 
	a1 := coeff(f1,x,1);
	b1 := coeff(f1,y,1);

	if(a1=0 and b1=0) then
	  st := -(f1 - a2*x^2 - b2*y^2);
	  if(st <> 1) then
		f1 := f1/st;
	  end if;

	  a := sqrt(1/coeff(f1,x,2));
	  b := sqrt(1/coeff(f1,y,2));
	  return (x^2/a^2 + y^2/b^2 = 1);

	else 
	  x0 := -a1/a2/2;
	  y0 := -b1/b2/2;
	  fx := (x - x0 )^2;
	  fy := (y - y0)^2;

	  msc := -simplify(f1 - (a2*fx + b2*fy));
	  f1 := a2*fx/msc + b2*fy/msc = 1;
	  return f1;
	end if;
end proc:

Elip_a := proc(ptct)
	local a;
	a := coeff(lhs(ptct),x,2);
	a := 1/a;
	return sqrt(a);
end proc:
	
Elip_b(ptct) := proc(ptct)
	local b;
	b := coeff(lhs(ptct),y,2);
	b := 1/b;
	return sqrt(b);
end proc:

Elip_c(a,b) := proc(a,b)
	local c;
	if (convert(a-b,float)>0) then
	  c := sqrt(a^2 - b^2);
	else
	  c := sqrt(b^2 - a^2);
	fi;
	return c;
end proc:

Elip_tam_sai(a,b) := proc(a,b)
	local c,e;
	  if (convert(a-b,float)>0) then
	    c := sqrt(a^2 - b^2);
		e := c/a;
	  else 
		c := sqrt(b^2 - a^2);				
		e := c/b;
	  fi;
	return e;
end proc:

Elip_pt2diem(M,N,Tam) := proc(M, N, Tam)
	local x0,y0,f,fM,fN,a,b,nghiem;
	x0 := Tam[1];
	y0 := Tam[2];
	f := (x-x0)^2/a^2 + (y-y0)^2/b^2 = 1;

	fM:= subs({x = M[1],y = M[2]},f);
	fN:= subs({x = N[1],y = N[2]},f);
	nghiem := solve({fM,fN,a>0,b>0},{a,b});
	f:= subs({a=rhs(nghiem[1]),b=rhs(nghiem[2])},f);
	return f;
end proc: