import "s-modules.m": QPrimes, Table, Image_under_t, Def_s, 
   ConstructModules, EliminateReducible;

// Latest version May 2020 to accord with paper 
// Chapter 10: SL(3, 2) 

// 10.11 
Def_f := function (m: Sparse := false)
   p := 7;
   if m le 30 then 
      C := CyclotomicField (2^m: Sparse := Sparse);
   else 
      error "Field cannot be constructed -- degree too large";
   end if;
   r := RootOfUnity (2^m, C);
   return GL(p, C) ! DiagonalMatrix ([1, 1, 1, r, 1, r^-1, 1]), C;
end function;

Def_g := function (m: Sparse := false)
   p := 7;
   if m le 30 then 
      C := CyclotomicField (2^m: Sparse := Sparse);
   else 
      error "Field cannot be constructed -- degree too large";
   end if;
   r := RootOfUnity (2^m, C);
   return GL(p, C) ! DiagonalMatrix ([r, r, 1, r^-1, 1, 1, r^-1]), C;
end function;

Def_vperm := function (p) 
   v := Sym (p) ! (1,2)(3,5);
   return PermutationMatrix (Integers (), v);
end function;

// Defn 10.6 
SL32_ListSubmodules := function (p, P, O: ListS := true)

   P := [Append (x, []): x in P];
   Q := QPrimes (p, O);

   L := []; N := [];
   for i in [1..#P] do
      if #(&cat P[i]) eq 0 then Append (~L, i); Append (~N, 0); continue; end if;
      params := P[i];
      flag := exists(k){k: k in [1..#params] | #params[k] gt 0 and params[k][1] eq 2}; // q = 2 
      if flag then 
         n1 := params[k][2]; n2 := params[k][3]; 
      else 
         k := 0; n1 := 0; n2 := 0; 
      end if;

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
      if ListS then continue; end if;

      if k gt 0 then 
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

SL32_ListGroups := function (p, P, M, L, S, V, N_S, N_V: 
   Sparse := true, Count := false)

   s := Def_s (p);
   v := Def_vperm (p);

   V0 := []; NP := [];
   for i in L do
      Append (~NP, P[i]);
      if Count then continue; end if;
      F := BaseRing (M[i]);
      G := sub<Generic (M[i]) | [Eltseq (M[i].j): j in [1..Ngens (M[i])]], s, Eltseq (v)>;
      Append (~V0, G);
   end for;

   T := []; NT := [];
   for i in [1..#V] do 
      n := N_V[i]; 
      assert n gt 0;
      Append (~NT, N_V[i]);
      if Count eq true then continue i; end if;
      j := V[i];
      F := BaseRing (M[j]);
      f, F_f := Def_f (n);
      lcm := LCM ([CyclotomicOrder (F), CyclotomicOrder (F_f)]);
      if lcm le 2^30 then
         F := CyclotomicField (lcm: Sparse := Sparse);
      else
         error "Field cannot be constructed -- degree too large";
      end if;
      v := GL(p, F) ! v;
      f := GL(p, F) ! f;
      MA := MatrixAlgebra (F, p);
      G := sub<MA | [Eltseq (M[j].k): k in [1..Ngens (M[j])]], s, Eltseq (v * f)>;
      Append (~T, G);
   end for;

   // original from thesis 
   for i in [1..#S] do 
      n := N_S[i];
      Append (~NT, N_S[i]);
      if Count eq true then continue i; end if;
      j := S[i];
      F := BaseRing (M[j]);
      g, F_g := Def_g (n + 1);
      v := Def_vperm (p);
      lcm := LCM ([CyclotomicOrder (F), CyclotomicOrder (F_g)]);
      if lcm le 2^30 then
         F := CyclotomicField (lcm: Sparse := Sparse);
      else
         error "Field cannot be constructed -- degree too large";
      end if;
      v := GL(p, F) ! v;
      g := GL(p, F) ! g;
      MA := MatrixAlgebra (F, p);
      G := sub<MA | [Eltseq (M[j].k): k in [1..Ngens (M[j])]], s, Eltseq (v * g)>;
      Append (~T, G);
   end for;

   return V0, NP, T, NT;
end function;

// SL(3, 2) as monomial 

SL32_Reps := function (p, m: Count := false) 
   assert IsPrime (p) and p eq 7;
   o := 168;
   assert m mod o eq 0;
   O := m div o;

   M, P, Z := ConstructModules (p, O: Count := Count);
   // "# of modules is ", #M;
   // "modules is ", [#x: x in M];
   V, N_V := SL32_ListSubmodules (p, P, O: ListS := false);
   L := V;

   S, N_S := SL32_ListSubmodules (p, P, O: ListS := true);

   index := [i: i in [1..#V] | not (V[i] in S)];

   V := [V[i]: i in index];
   N_V := [N_V[i]: i in index];

   V0, P, Y, PY := SL32_ListGroups (p, P, M, L, S, V, N_S, N_V: 
      Sparse := true, Count := Count);

   index := EliminateReducible (p, P, O: offset := 0);
   if Count eq false then 
      X := [V0[i]: i in index] cat Y;
   else
      X := [];
   end if;
   // PY: special parameters from Defn 10.14 
   P := [P[i]: i in index] cat [[[y]] : y in PY];
   return X, P; 
end function;
