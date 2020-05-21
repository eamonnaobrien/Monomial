// Defn 6.2 : identify <s, t^a>-submodules of D
ListSubmodules := function (p, P, O, a)

   P := [Append (x, []): x in P];
   Q := QPrimes (p, O);
  
   L := [];
   for i in [1..#P] do
      if #(&cat P[i]) eq 0 then Append (~L, i); continue; end if;
      T := Table (p, P[i], Q);
      Im := Image_under_power (T, a);
      if T eq Im then 
         R := P[i];
         paras := R[#R - 1]; 
         assert #paras eq 4; // [p, j, k, l]
         assert paras[1] eq p;
         j := paras[2]; 
         l := paras[4]; 
         if l eq 0 or (a * j) mod (p - 1) eq 0 then Append (~L, i); end if; 
      end if;
   end for;
   return L;
end function;

// Lemma 6.13 
ListGroups := function (p, P, M, O, L, Z, a)
   a_hat := (p - 1) div a;
   T := []; NP := [];
   for i in L do
      N := M[i];
      F := BaseRing (N);
      s := GL(p, F) ! Def_s (p);
      t := Def_t (p, F);
      z := ConstructScalar (p, Z[i] * (p - 1))[1];
      z := z.Ngens (z); 
      K := MinimalField (&cat [Eltseq (N.i): i in [1..Ngens (N)]] 
                          cat Eltseq (z) cat Eltseq (t^a));
      gens := [GL(p, K) ! t^a * GL(p, K) ! z^(a * c): c in [0..a_hat - 1]];
      S := [sub<GL(p, K) | [N.i: i in [1..Ngens (N)]], s, g>: g in gens];
      Append (~NP, [Append (P[i], [a, c]): c in [0..a_hat - 1]]);
      Append (~T, S);
   end for;
   return &cat (T), &cat (NP);
end function;

// Defn 6.15
NextFilter := function (p, P, O)

   if #P le 1 then return P, [], [], []; end if;
   t := PrimitiveRoot (p);
   Q := QPrimes (p, O);
   L1 := []; L2 := []; L3 := [];

   for m in [1..#P] do
      params := P[m]; len := #params;
      a := params[len][1];
      a_hat := (p - 1) div a;

      c := params[len][2];
      Y_params := params[len - 1];
      assert Y_params[1] eq p;
      j := Y_params[2]; k := Y_params[3]; l := Y_params[4];

      T := Table (p, P[m], Q);
      
      if l eq 0 and c in {0..a_hat div 2} and j eq 1 and T eq 0 then 
         Append (~L1, m);
      end if;
      if l eq 0 and (j ge 2 or T ne 0) then  
         Append (~L2, m);
      end if;
      if j ne 0 and j mod a_hat eq 0 and l in {t^i mod p: i in [1..Gcd (p - 1, j)]} then 
         Append (~L3, m);
      end if;
   end for;

   L2_star := ConstructL_star (p, P, L2, O);
   L3_star := ConstructL_star (p, P, L3, O: t_orbit := false);

   L := L1 cat L2_star cat L3_star;
   return L, L1, L2_star, L3_star;
end function; 

// general case: Chap 6

Chap6 := function (p, m: D := [])
   if D eq [] then D := Divisors (p - 1); Exclude (~D, p - 1); end if;
   La := [];
   for a in D do 
      n := ((p - 1) div a * p); 
      if m mod n ne 0 then continue; end if;
      O := m div (p * (p - 1) div a); 
      if O eq 1 then continue; end if;

      M, P, Z := ConstructModules (p, O);
      index := EliminateReducible (p, P, O: offset := 0);
      M := [M[i]: i in index];
      P := [P[i]: i in index];
      Z := [Z[i]: i in index];

      L := ListSubmodules (p, P, O, a);
      X, P := ListGroups (p, P, M, O, L, Z, a);

      // R := (p - 1) div a * p * O; //order of group 
      // assert forall{x : x in X |  #x eq R};

      index := NextFilter (p, P, O);

       // "Final list is ", index;

      Append (~La, [X[i]: i in index]);
   end for;
   return La;
end function; 

// general case: Chap 5

Chap5 := function (p, O)
"p is ", p, O;
   if O eq 1 then return []; end if;
   I, P := IrreducibleGroups (p, O);
   if #I eq 0 then return []; end if;
   L1, L2, L3, L4 := MyPartitionLists (p, P);
   // "Lists before filters has length ", #L1, #L2, #L3, #L4;

   // Lemma 4.17
   if Gcd (p, O) eq 1 then
      L2_star := ConstructL_star (p, P, L2, O);
   else
      L2_star := L2;
   end if;

   if p gt 2 then 
      L3_star := ConstructL_star (p, P, L3, O);
      L4_star := ConstructL_star (p, P, L4, O: t_orbit := false);
   else
      L3_star := L3;
      L4_star := L4;
   end if;

   // "Lists after filters have length ", #L1, #L2_star, #L3_star, #L4_star;

   L := L1 cat L2_star cat L3_star cat L4_star;
   Sort (~L);
   L := [I[l]: l in L];
   return L;
end function;

// conjugacy classes of soluble monomial subgroups of order m in GL(p, C) 
AllSolubleClasses := function (p, m)
   if m mod p ne 0 then return []; end if;
   L := Chap5 (p, m div p);
   La := Chap6 (p, m);
   Append (~L, La);
   return &cat (L), L;
end function;
