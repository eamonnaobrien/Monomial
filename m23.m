import "s-modules.m": QPrimes, Table, Image_under_t, Def_s,
ConstructModules, EliminateReducible;

// Chapter 15 M23 

// Definition 15.1 
Def_qperm := function (p) 
   q := Sym (p) ! (1,3)(4,19)(5,17)(6,9)(7,8)(10,16)(12,15)(13,18);
   return PermutationMatrix (Integers (), q);
end function;

// Defn 15.2 
M23_Submodules := function (p, P, O)

   P := [Append (x, []): x in P];
   Q := QPrimes (p, O);

   L := []; N := [];
   for i in [1..#P] do
      if #(&cat P[i]) eq 0 then 
         Append (~L, i); Append (~N, 0); continue; 
      end if;

      // "M23: i = ", i;
      params := P[i];
      // "M23: paras ", params;
      flag := exists(k){k: k in [1..#params] | #params[k] gt 0 and params[k][1] eq 2}; // q = 2
      if flag then n2 := params[k][3]; else k := 0; n2 := 0; end if;

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
      one := T eq Im;
      if good and one then Append (~L, i); Append (~N, n2); continue; end if;

      if k gt 0 then 
         // params := P[i]; n2 := params[k][3];
         params := P[i]; n1 := params[k][2];
         two := n1 eq n2 + 1;
      else
         two := false; 
      end if;
      if not two then continue; end if;

      assert #Q eq Nrows (T);
      row := [i: i in [1..#Q] | Q[i] ne 2];
      if #row gt 0 then 
         col := [1..Ncols (T)];
         Tbar := ExtractBlock (T, row, col);
         Im_Tbar := ExtractBlock (Im, row, col);
         three := Tbar eq Im_Tbar;
      else 
         three := true;
      end if;
      if three then Append (~L, i); Append (~N, n1); end if;
   end for;
   return L, N;
end function;

M23_ListGroups := function (p, P, M, L: Sparse := true, Count := false)
   s := Def_s (p);
   q := Def_qperm (p);

   T := []; NP := [];
   for i in L do
      Append (~NP, P[i]);
      if Count eq true then continue i; end if;
      F := BaseRing (M[i]);
      G := sub<Generic (M[i]) | M[i], s, Eltseq (q)>;
      Append (~T, G);
   end for;
   return T, NP;
end function;

// M23 as monomial 
M23_Reps := function (p, m: Count := false)
   assert p eq 23;
   o := 10200960;
   assert m mod o eq 0;
   O := m div o;

   M, P, Z := ConstructModules (p, O: Count := Count);
   // "# of modules is ", #M;
   // "modules is ", [#x: x in M];
   L :=  M23_Submodules (p, P, O);
   X, P := M23_ListGroups (p, P, M, L: Sparse := true, Count := Count);
   assert #P eq #L;
   index := EliminateReducible (p, P, O: offset := 0);
   if Count eq false then 
      X := [X[i]: i in index]; 
   else
      X := [];
   end if;
   P := [P[i]: i in index]; 
   
   return X, P;
end function;
