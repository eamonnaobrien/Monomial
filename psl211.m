// Chapter 11 PSL(2, 11) 

// Definition 11.1 
Def_pperm := function (p) 
   v := Sym (p) ! (1,7)(2,3)(4,8)(5,9);
   return PermutationMatrix (Integers (), v);
end function;

// Definition 11.1 
Def_qperm := function (p) 
   q := Sym (p) ! (1,3)(2,8)(4,7)(5,6);
   return PermutationMatrix (Integers (), q);
end function;

// Defn 11.2 
PSL211_Submodules := function (p, P, O)

   P := [Append (x, []): x in P];
   Q := QPrimes (p, O);

   L := []; N := [];
   for i in [1..#P] do
      if #(&cat P[i]) eq 0 then 
         Append (~L, i); Append (~N, 0); continue; 
      end if;

      // "PSL211: i = ", i;
      params := P[i];
      // "PSL211: paras ", params;
      flag := exists(k){k: k in [1..#params] | #params[k] gt 0 and params[k][1] eq 3}; // q = 3 
      if flag then n1 := params[k][2]; else k := 0; n1 := 0; end if;

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
      if good and one then Append (~L, i); Append (~N, n1); continue; end if;

      if k gt 0 then 
         params := P[i]; n2 := params[k][3];
         // correction to 11.2 
         two := n2 eq n1 + 1;
      else
         two := false; 
      end if;
      if not two then continue; end if;

      assert #Q eq Nrows (T);
      row := [i: i in [1..#Q] | Q[i] ne 3];
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

PSL211_ListGroups := function (p, P, M, L: Sparse := true)
   s := Def_s (p);
   p1 := Def_pperm (p);

   T := []; NP := [];
   for i in L do
      F := BaseRing (M[i]);
      G := sub<Generic (M[i]) | M[i], s, p1>;
      Append (~T, G);
      Append (~NP, P[i]);
   end for;
   return T, NP;
end function;

// PSL(2, 11) as monomial 
PSL211_Reps := function (p, m)
   assert p eq 11;
   o := 660;
   assert m mod o eq 0;
   O := m div o;

   M, P, Z := ConstructModules (p, O);
   // "# of modules is ", #M;
   // "modules is ", [#x: x in M];
   L :=  PSL211_Submodules (p, P, O);
   X, P := PSL211_ListGroups (p, P, M, L: Sparse := true);
   index := EliminateReducible (p, P, O: offset := 0);
   X := [X[i]: i in index]; 
   
   return X;
end function;
