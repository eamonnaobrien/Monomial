import "s-modules.m": QPrimes, Def_s, ConstructModules, EliminateReducible,
Table, Image_under_t, ConstructScalar;
 
// Chapter 8: Symmetric group 

// Defn 8.1 
Sym_ListSubmodules := function (p, P, O)

   P := [Append (x, []): x in P];
   Q := QPrimes (p, O);

   L := [];
   for i in [1..#P] do
      if #(&cat P[i]) eq 0 then Append (~L, i); continue; end if;
      R := P[i];
      paras := R[#R - 1];
      assert #paras eq 4; // [p, j, k, l]
      assert paras[1] eq p;
      j := paras[2];
      l := paras[4];
      good := (j mod (p - 1) eq 0) or (l eq 0 and ((j + 1) mod (p - 1) eq 0));
      if not good then continue; end if;
      T := Table (p, P[i], Q);
      Im := Image_under_t (T);
      if T eq Im then Append (~L, i); end if;
   end for;
   return L;
end function;

// perm matrix for (1, 2) 
Def_r := function (p)
   Z := Integers ();
   S := Sym (p);
   s := S!(1,2);
   return GL(p, Z) ! PermutationMatrix (Z, s);
end function;

// Definition 8.5 
Sym_ListGroups := function (p, P, M, O, L, Z: Sparse := true, Count := false)
   r := Def_r (p);
   T := []; NP := [];
   for i in L do
      Append (~NP, P[i]);
      Append (~NP, P[i]);
      if Count eq true then continue i; end if;
      
      N := M[i];
      F := BaseRing (N);
      // s := GL(p, F) ! 
      s := Def_s (p);
      MA := MatrixAlgebra (F, p);
      S := sub<MA | [N.i: i in [1..Ngens (N)]], s, r>;
      Append (~T, S);

      k := Valuation (Z[i], 2);
      z := ConstructScalar (p, 2^(k + 1))[1];
      z := z.Ngens (z);
      lcm := LCM ([CyclotomicOrder (BaseRing (N)), CyclotomicOrder (BaseRing (Parent (z)))]);
      if lcm le 2^30 then
         K := CyclotomicField (lcm: Sparse := Sparse);
      else
         error "Field cannot be constructed -- degree too large";
      end if;
      MA := MatrixAlgebra (K, p);
      g := MA ! r * MA ! z;
      S := sub<MA | [Eltseq (N.i): i in [1..Ngens (N)]], s, g>;
      Append (~T, S);
   end for;
   
   return T, NP;
end function;

// Sym (p) as monomial group 

Sym_Reps := function (p, m: Count := false)
   assert IsPrime (p) and p ge 5;
   assert m mod Factorial (p) eq 0;
   La := [];
   O := m div Factorial (p);

   M, P, Z := ConstructModules (p, O: Count := Count);
   // "Number of modules is ", #M;
   L := Sym_ListSubmodules (p, P, O);
   X, P := Sym_ListGroups (p, P, M, O, L, Z: Count := Count);
   // "# of groups is ", #X;
   index := EliminateReducible (p, P, O: offset := 0);
   if Count eq false then 
      return [X[i]: i in index], [P[i]: i in index];
   else 
      return [], [P[i]: i in index];
   end if;
end function;
