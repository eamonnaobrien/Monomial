import "s-modules.m": Def_s, Def_z, Def_x_pj;

// primitive insoluble subgroups of order m up to conjugacy in GL(3, C) 

PrimitiveInsolubleDimension3 := function (m)
   L := [];
   orders := [60, 1080, 168];
   if forall{o: o in orders | m mod o ne 0} then return L; end if;
 
   p := 3;
   // A5 
   if m mod 60 eq 0 then 
      n := m div 60;
      F := CyclotomicField (n);
      P<x> := PolynomialRing (F);
      f := x^2 - 5; 
      flag, mu := HasRoot (f);
      if not flag then 
         F<mu> := NumberField (f);
      end if;
      mu1 := (-1 + mu) / 2;
      mu2 := (-1 - mu) / 2;
   
      MA := MatrixAlgebra (F, 3);
      a := MA!DiagonalMatrix([1, -1, -1]);
      s := MA!Def_s (p);
      a1 := 1/2 * MA![-1, mu2, mu1,
                      mu2, mu1, -1,
                      mu1, -1, mu2];
      zn := Def_z (p, n);
      Append (~L, sub<GL(3, F) | s, a, a1, zn>);
   end if;

   // 3.Alt(6)
   n := m div 360;
   if m mod 360 eq 0 and (n mod 3 eq 0) then 
      F := CyclotomicField (LCM (n, 3));
      v := RootOfUnity (3, F);
      P<x> := PolynomialRing (F);
      f := x^2 - 5; 
      flag, mu := HasRoot (f);
      if not flag then 
         F<mu> := NumberField (f);
      end if;
      mu1 := (-1 + mu) / 2;
      mu2 := (-1 - mu) / 2;
   
      MA := MatrixAlgebra (F, 3);
      a := MA!DiagonalMatrix([1, -1, -1]);
      s := MA!Def_s (p);
      a1 := 1/2 * MA![-1, mu2, mu1,
                      mu2, mu1, -1,
                      mu1, -1, mu2];
      b1 := MA![-1, 0, 0, 
                0, 0, -v^2,
                0, -v, 0];
      zn := Def_z (p, n);
      Append (~L, sub<GL(3, F) | s, a, a1, b1, zn>);
   end if;

   // PSL(2, 7) 
   if m mod 168 eq 0 then 
      n := m div 168;
      F := CyclotomicField (LCM ([n, 7]));
      w := RootOfUnity (7, F);

      P<x> := PolynomialRing (F);
      f := x^2 + 7; 
      flag, r := HasRoot (f);
      if not flag then 
         F<r> := NumberField (f);
      end if;
   
      MA := MatrixAlgebra (F, 3);
      s := MA!Def_s (p);
      c := MA!DiagonalMatrix ([w, w^2, w^4]);
      c1 := 1/r * MA![ w^4 - w^3, w^2 - w^5, w - w^6, 
                       w^2 - w^5, w - w^6, w^4 - w^3, 
                       w - w^6, w^4 - w^3, w^2 - w^5]; 
      zn := Def_z (p, n);
      
      // Append (~L, sub<GL(3, F) | s, c, c1, zn>);
      Append (~L, sub<GL(3, F) | c, c1, zn>);
   end if;

   return L;
end function;

CaseI := function (m)
   if m mod 108 ne 0 then return []; end if;
   n := m div 36;
   p := 3;

   if n mod 4 eq 0 then 
      E := CyclotomicField (LCM ([4*n, 3]));
   elif n mod 4 eq 2 then 
      E := CyclotomicField (LCM ([n, 3, 8]));
   else 
      E := CyclotomicField (LCM ([n, 3, 4]));
   end if;
     
   omega := RootOfUnity (3, E);

   MA := MatrixAlgebra (E, 3);
   u := MA![1, 1, 1, 1, omega, omega^2, 1, omega^2, omega];
   u := (omega - omega^2)^-1 * u;

   z_n := MA!Def_z (3, n);
   gl := GL(3, E);
   s := MA!Def_s (p);
   S := [sub< gl | s, u, z_n>];
   if IsOdd (n) then
      Append (~S, sub< gl | s, -u, z_n>);
      i := RootOfUnity (4, E);
      Append (~S, sub< gl | s, i * u, z_n>);
   elif n mod 4 eq 0 then
      z_4n := MA!Def_z (3, 4*n);
      Append (~S, sub< gl | s, z_4n * u, z_n>);
      Append (~S, sub< gl | s, z_4n^2 * u, z_n>);
   elif n mod 2 eq 0 then
      i := RootOfUnity (4, E);
      Append (~S, sub< gl | s, i * u, z_n>);
      j := RootOfUnity (8, E);
      Append (~S, sub< gl | s, j * u, z_n>);
   end if;

   return S;
end function;

CaseII := function (m) 
   if m mod 216 ne 0 then return []; end if;
   n := m div 72;
   p := 3;

   if IsEven (n) then 
      E := CyclotomicField (LCM ([2*n, 3]));
   else
      E := CyclotomicField (LCM ([n, 3]));
   end if;
   omega := RootOfUnity (3, E);

   gl := GL(3, E);
   MA := MatrixAlgebra (E, 3);

   u := MA![1, 1, 1, 1, omega, omega^2, 1, omega^2, omega];
   u := (omega - omega^2)^-1 * u;

   u1 := MA![1, omega, omega, omega^2, omega, omega^2, omega^2, omega^2, omega];
   u1 := (omega - omega^2)^-1 * u1;

   z_n := MA!Def_z (3, n);

   s := MA!Def_s (p);
   S := [sub< gl | s, u, u1, z_n>];
   if IsOdd (n) then
      Append (~S, sub< gl | s, u, -u1, z_n>);
   else 
      z_2n := MA!Def_z (3, 2*n);
      Append (~S, sub< gl | s, u * z_2n, u1, z_n>);
   end if;
    
   return S;
end function;

// SL(2, 3) 

CaseIII := function (m) 
   if m mod 648 ne 0 then return []; end if;
   n := m div 216;
   p := 3;

   E := CyclotomicField (3 * n);
   omega := RootOfUnity (3, E);

   gl := GL(3, E);
   MA := MatrixAlgebra (E, 3);

   u := MA![1, 1, 1, 1, omega, omega^2, 1, omega^2, omega];
   u := (omega - omega^2)^-1 * u;

   x_27 := MA!Def_x_pj (3, 3);
   z_n := MA!Def_z (3, n);
   z_3n := MA!Def_z (3, 3*n);

   S := [sub< gl | u, x_27, z_n>, 
         sub< gl | u, z_3n * x_27, z_n>, 
         sub< gl | u, z_3n^2 * x_27, z_n>]; 
   return S;
end function;

PrimitiveSolubleDimension3 := function (m)
   if m mod 108 ne 0 then return []; end if;
   return CaseI (m) cat CaseII (m) cat CaseIII (m);
end function;

PrimitiveDimension3 := function (m: Soluble := true, Insoluble := true)
   if Soluble then 
      A := PrimitiveSolubleDimension3 (m);
      if Insoluble eq false then return A; end if;
   end if;
   
   if Insoluble then 
      B := PrimitiveInsolubleDimension3 (m);
      if Soluble eq false then return B; end if;
   end if;

   return A cat B;
end function;
