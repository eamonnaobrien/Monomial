// irreducible primitive groups of order m up to conjugacy in GL(2, C) 

PrimitiveDimension2 := function (m: Soluble := false)
   L := [];

   n := m div 12;
   if m mod 12 eq 0 and IsEven (n) then 
      E := CyclotomicField (LCM (3 * n, 4): Sparse := false);
      i := RootOfUnity (4, E);

      MA := MatrixAlgebra (E, 2);

      a := 1/2 * MA![i-1, i-1, i+1, -i-1];
      x4 := MA!Def_x_pj (2, 2);

      z_n := MA!Def_z (2, n);
      I := sub<GL(2, E) | a, x4, z_n>;
      Append (~L, I);

      z_3n := MA!Def_z (2, 3 * n);
      J := sub<GL(2, E) | a * z_3n, x4>;

      Append (~L, J);
   end if;

   n := m div 24;
   if m mod 24 eq 0 and IsEven (n) then 
      E := CyclotomicField (2 * n: Sparse := false);
      i := RootOfUnity (4, E);

      P<x> := PolynomialRing (E);
      f2 := x^2 - 2;
      flag, l := HasRoot (f2);
      if not flag then E<l> := ext<E | f2>; end if;

      MA := MatrixAlgebra (E, 2);

      a := 1/2 * MA![i-1, i-1, i+1, -i-1];
      b := 1/l * MA![1+i, 0, 0, 1-i];

      z_n := MA!Def_z (2, n);
      I := sub<GL(2, E) | a, b, z_n>;
      Append (~L, I);

      z_2n := MA!Def_z (2, 2 * n);
      J := sub<GL(2, E) | a, b * z_2n, z_n>;

      Append (~L, J);
   end if;

   if Soluble then return L; end if;

   n := m div 60;
   if m mod 60 eq 0 and IsEven (n) then 
      E := CyclotomicField (LCM(n, 4) : Sparse := false);
      i := RootOfUnity (4, E);

      P<x> := PolynomialRing (E);
      f5 := x^2 - 5;
      flag, r := HasRoot (f5);
      if not flag then E<r> := ext<E | f5>; end if;

      MA := MatrixAlgebra (E, 2);

      a := 1/2 * MA![i-1, i-1, i+1, -i-1];
      r1 := (1 - r) / 2; r2 := (1 + r) / 2;
      c := 1/2 * MA![i, r1 - r2 * i, -r1 - r2 * i, -i];

      x4 := MA!Def_x_pj (2, 2);

      z_n := MA!Def_z (2, n);
      I := sub<GL(2, E) | a, c, x4, z_n>;
      Append (~L, I);
   end if;

   return L;
end function;

/* 
for m in [1..5] do 
  L := Dimension2 (m * 120);
  S := L;
  // SS, S := StandardGroups (L, m * 120);
 [#x: x in S];
 [#quo<X | Centre (X)>: X in S];
 [IdentifyGroup (x): x in S];
end for;

*/
