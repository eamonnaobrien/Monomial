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
Sym_ListGroups := function (p, P, M, O, L, Z: Sparse := true)
   r := Def_r (p);
   T := []; NP := [];
   for i in L do
      N := M[i];
      F := BaseRing (N);
      s := GL(p, F) ! Def_s (p);
      S := sub<GL(p, F) | [N.i: i in [1..Ngens (N)]], s, r>;
      Append (~T, S);
      Append (~NP, P[i]);
      k := Valuation (Z[i], 2);
      z := ConstructScalar (p, 2^(k + 1))[1];
      z := z.Ngens (z);
      lcm := LCM ([CyclotomicOrder (BaseRing (N)), CyclotomicOrder (BaseRing (Parent (z)))]);
      if lcm lt 2^30 then
         K := CyclotomicField (lcm: Sparse := Sparse);
      else
         "HARD"; K := CyclotomicField (lcm);
      end if;
      g := GL(p, K) ! r * GL(p, K) ! z;
      S := sub<GL(p, K) | [N.i: i in [1..Ngens (N)]], s, g>;
      Append (~T, S);
      Append (~NP, P[i]);
   end for;
   
   return T, NP;
end function;

// Sym (p) as monomial group 

Sym_Reps := function (p, m)
   assert IsPrime (p) and p ge 5;
   assert m mod Factorial (p) eq 0;
   La := [];
   O := m div Factorial (p);

   M, P, Z := ConstructModules (p, O);
   // "modules is ", [#x: x in M];
   L := Sym_ListSubmodules (p, P, O);
   X, P := Sym_ListGroups (p, P, M, O, L, Z);
   // "# of groups is ", #X;
   index := EliminateReducible (p, P, O: offset := 0);
   return [X[i]: i in index];
end function;
