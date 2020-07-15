import "s-modules.m": QPrimes, Def_s, ConstructModules, EliminateReducible;
import "symmetric.m": Sym_ListSubmodules;

// Chapter 9: Alt (p) 

// perm matrix for (1, 2, 3) 
Def_u := function (p)
   Z := Integers ();
   S := Sym (p);
   u := S!(1,2,3);
   return GL(p, Z) ! PermutationMatrix (Z, u);
end function;

// Definition 9.10
Def_c := function (m: Sparse := true)
   p := 5;
   C := CyclotomicField (3^m: Sparse := Sparse);
   r := RootOfUnity (3^m, C);
   return GL(p, C) ! DiagonalMatrix ([1, r, r^-1, r^-1, r]), C;
end function;

// Definition 9.12

Alt5_ListGroups := function (p, P, O, M, L: Sparse := true, Count := false)
   if p ne 5 then return []; end if;
   P := [Append (x, []): x in P];

   T := []; NP := [];
   s := Def_s (p);
   u := Def_u (p);

   for i in [1..#L] do
      Append (~NP, P[i]);
      if Count eq true then continue; end if;

      params := P[i];
      // q = 3
      flag := exists(k){k: k in [1..#params] | #params[k] gt 0 and params[k][1] eq 3}; 
      if flag then 
         params := params[k];
         n := &+[params[j]: j in [2..#params]]; 
      else 
         n := 0; 
      end if;
      
      c, C := Def_c (n + 1);
      
      j := L[i];
      F := BaseRing (M[j]);
      lcm := LCM ([CyclotomicOrder (F), CyclotomicOrder (C)]);
      // "Alt5List: lcm is ", lcm;
      if lcm le 2^30 then 
         F := CyclotomicField (lcm: Sparse := Sparse);
      else 
         error "Field cannot be constructed -- degree too large";
      end if;
      MA := MatrixAlgebra (F, 5);
      u := GL(5, F)!u; 
      c := GL(5, F)!c; 
      S := sub<MA | [Eltseq (M[j].k): k in [1..Ngens (M[j])]], s, u * c>;
      Append (~T, S);
   end for;

   return T, NP;
end function;

// Definition 9.4 

Alt_ListGroups := function (p, P, M, L: Count := false)
   T := []; NP := [];
   s := Def_s (p);
   u := Def_u (p);
   for i in L do
      Append (~NP, P[i]);
      if Count eq true then continue; end if;
      F := BaseRing (M[i]);
      S := sub<Generic (M[i]) | M[i], s, u>;
      Append (~T, S);
   end for;
   return T, NP;
end function;

// Alt (p) as monomial group

Alt_Reps := function (p, m: Count := false)
   assert IsPrime (p) and p ge 5;
   o := Factorial (p) div 2;
   assert m mod o eq 0;
   O := m div o;

   M, P, Z := ConstructModules (p, O: Count := Count);
   // "# of modules is ", #M;
   L := Sym_ListSubmodules (p, P, O);
   X, P := Alt_ListGroups (p, P, M, L: Count := Count);
   assert #P eq #L;
   index := EliminateReducible (p, P, O: offset := 0);

   if Count eq false then 
      X := [X[i]: i in index];
   else
      X := [];
   end if;

   if p eq 5 then 
      Y, YP := Alt5_ListGroups (p, P, O, M, L: Count := Count); 
      assert #YP eq #L; 
   else
      Y := []; YP := [];
   end if;
   P := [P[i]: i in index];
   if p eq 5 then 
      vprint Monomial, 1: "# of special A5 groups is ", #Y; 
   end if;
   return X cat Y, P cat YP;
end function;
