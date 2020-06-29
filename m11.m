import "s-modules.m": QPrimes, Table, Image_under_t, Def_s, 
   ConstructModules, EliminateReducible;
import "psl211.m": Def_qperm; 

// Definition 11.15 
Def_h := function (m: Sparse := true)
   p := 11;
   if m le 30 then 
      C := CyclotomicField (2^m: Sparse := Sparse);
   else 
      error "Field cannot be constructed -- degree too large";
   end if;
   r := RootOfUnity (2^m, C);
   return GL(p, C) ! DiagonalMatrix ([r, r^-1, r^-1, 1, r^-1, r, 1, r, 1, 1, 1]), C;
end function;

// Defn 11.16 
M11_Submodules := function (p, P, O) 

   P := [Append (x, []): x in P];
   Q := QPrimes (p, O);

   L := []; N := [];
   for i in [1..#P] do
      if #(&cat P[i]) eq 0 then 
         Append (~L, i); Append (~N, 0); continue; 
      end if;

      params := P[i];
      // "M11: i, params ", i, params;
      flag := exists(k){k: k in [1..#params] | #params[k] gt 0 and params[k][1] eq 2}; // q = 3 
      if flag then n1 := params[k][2]; else n1 := 0; end if;

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
      if T eq Im then Append (~L, i); Append (~N, n1); end if;
   end for;
   return L, N;
end function;

M11_ListGroups := function (p, P, M, L: Sparse := true, Count := false)
   s := Def_s (p);

   T := []; NP := [];
   for i in [1..#L] do 
      Append (~NP, P[i]);
      Append (~NP, P[i]);
      if Count eq true then continue i; end if;

      j := L[i];
      q := Def_qperm (p);
      F := BaseRing (M[j]);
      G := sub<Generic (M[j]) | M[j], s, Eltseq (q)>;
      Append (~T, G);

      // correction to thesis: intersection condition for q = 2 not 3 
      params := P[i];
      flag := exists(k){k: k in [1..#params] | #params[k] gt 0 and params[k][1] eq 2};
      if flag then
         // "params is ", params;
         n := params[k][2];
      else
         n := 0;
      end if;
      // "h -- n is ", n;
      // correction to thesis: n + 1, not n 
      h, F_h := Def_h (n + 1: Sparse := Sparse);

      lcm := LCM ([CyclotomicOrder (F), CyclotomicOrder (F_h)]);
      if lcm le 2^30 then
         F := CyclotomicField (lcm: Sparse := Sparse);
      else
         error "Field cannot be constructed -- degree too large";
      end if;
      q := GL(p, F) ! q;
      h := GL(p, F) ! h;
      MA := MatrixAlgebra (F, p);
      G := sub<MA | [Eltseq (M[j].k): k in [1..Ngens (M[j])]], s, Eltseq (q * h)>;
      Append (~T, G);
   end for;

   return T, NP;
end function;

// M11 as monomial 
M11_Reps := function (p, m: Count := false)

   assert p eq 11;
   o := 7920;
   assert m mod o eq 0;
   O := m div o;

   M, P, Z := ConstructModules (p, O: Count := Count);

   // "# of modules is ", #M;
   L :=  M11_Submodules (p, P, O);
   X, P := M11_ListGroups (p, P, M, L: Sparse := true, Count := Count);
   index := EliminateReducible (p, P, O: offset := 0);
   if m eq 7920 then index := [2]; end if;
   if Count eq false then 
      X := [X[i]: i in index]; 
   else
      X := [];
   end if;
   P := [P[i]: i in index]; 
   
   return X, P;
end function;
