// complete list of irreducible monomial subgroups of GL(p, C) 
// with projection <s>

import "s-modules.m": Def_s, Def_t, Def_z, 
ConstructScalar, SetupGroups, EliminateReducible, ConstructModules;

import "filter.m": Chap5, Chap6, ListSubmodules;

ProcessParametersA := function (G, params, power, p)
   if exists(j){j : j in [1..#params] | #params[j] gt 0 and params[j][1] cmpeq p} then 
      k := params[j][3]; 
   else 
      k := 0; 
   end if;
   z := Def_z (p, p^(k + 1));
   PZ := Generic (Parent (z));
   s := PZ!Def_s (p);
   gens := [s * z^power];
   add := [sub<PZ | Eltseq (a) >: a in gens]; 
   C := CartesianProduct ([G], add);
   J := SetupGroups (p, C: AlgebraParent := true);
   return J[1];
end function;

FastChap5 := function (p, m) 
   if m mod p ne 0 then return [], []; end if;
   _, Params := Chap5 (p, m: Count := true);
   if #Params eq 0 then return [], []; end if;
   O := m div p;
   L, P := ConstructModules (p, O: Count := false);
   M := [];
   for i in [1..#Params] do 
      Good := Params[i];
      Two := [Good[i]: i in [1..#Good-1]];
      power := Good[#Good][1];
      ell := Position (P, Two);
      params := P[ell];
      G := L[ell];
      Q := ProcessParametersA (G, params, power, p);
      Append (~M, Q);
   end for;
   return M, Params;
end function;

// Lemma 6.13 
ListGroupsB := function (p, P, M, O, L, Z, a, C) 
   T := []; 
   for k in [1..#L] do 
      if #C[k] eq 0 then continue k; end if;
      i := L[k];
      N := M[i];
      F := BaseRing (N);
      s := Def_s (p);
      t := Def_t (p, F);
      z := ConstructScalar (p, Z[i] * (p - 1))[1];
      z := z.Ngens (z); 
      K := MinimalField (&cat [Eltseq (N.i): i in [1..Ngens (N)]] 
                          cat Eltseq (z) cat Eltseq (t^a));
      MA := MatrixAlgebra (K, p);
      gens := [MA ! t^a * MA ! z^(a * c): c in C[k]];
      S := [sub< MA | [Eltseq (N.i): i in [1..Ngens (N)]], s, g>: g in gens];
      // S := [sub<GL(p, K) | [N.i: i in [1..Ngens (N)]], s, g>: g in gens];
      Append (~T, S);
   end for;
   return &cat (T);
end function;

// general case: Chap 6

Special_Chap6 := function (p, m, C: D := []) 
   La := []; Pa := [];
   if #C eq 0 then return La, Pa; end if;
   if D eq [] then D := Divisors (p - 1); Exclude (~D, p - 1); end if;
   assert #C eq #D;
   for k in [1..#D] do 
      a := D[k];
      n := ((p - 1) div a * p); 
      if m mod n ne 0 then continue; end if;
      O := m div (p * (p - 1) div a); 
      if O eq 1 then continue; end if;
      M, P, Z := ConstructModules (p, O);
      index := EliminateReducible (p, P, O: offset := 0);
      M := [M[i]: i in index];
      Z := [Z[i]: i in index];
      P := [P[i]: i in index];
      L := ListSubmodules (p, P, O, a);
      X := ListGroupsB (p, P, M, O, L, Z, a, C[k]);
      Append (~La, X);
      Append (~Pa, P);
   end for;
   return La, Pa;
end function; 

FastChap6 := function (p, m)
   _, Pa, C_val := Chap6 (p, m: Count := true);
   if #&cat (Pa) eq 0 then return [], []; end if;
   La := Special_Chap6 (p, m, C_val);
   return &cat (La), &cat (Pa);
end function;
