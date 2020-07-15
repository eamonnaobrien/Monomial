// declare verbose Monomial, 1;

// Chapters 2-5 of Bacskai: construct up to GL(p,C) conjugacy list of 
// finite irreducible subgroups of M(p, C) with projection group s = <(1..p)>

// matrix group defined over sparse cyclotomic field to standard one 

SparseToStandard := function (G)
   d := Degree (G);
   o := CyclotomicOrder (BaseRing (G));
   C := CyclotomicField (o);
   return sub<GL(d, C) | Generators (G)>;
end function;

// return sequence of primes distinct from p which divide O 
QPrimes := function (p, O)
   m := O div (p^Valuation (O, p));
   return PrimeBasis (m);
end function;

// all integer sequences whose i-th entry is in the range 
// [0..M[i] by 1] for i in [1..#M] and whose sum is at most bound 

BackTrack := function (M, bound)
   offset := 1;
   n := #M;
   m := [0: i in [1..#M]] cat [0];
   original := m;
   min := Minimum (m);
 
   IndexList := [i: i in [1..#M] | M[i] ge min];
   len := #IndexList;
   Append (~IndexList, n + 1);
 
   Solns := [];
   repeat
      index := 1;
      m[IndexList[index]] +:= offset;
//      while (index le len and m[IndexList[index]] gt M[IndexList[index]]) do 
      while (index le len and m[IndexList[index]] gt M[IndexList[index]]) 
         or (index le len and &+m gt bound) do 
         m[IndexList[index]] := original[IndexList[index]];
         index +:= 1;
         m[IndexList[index]] +:= offset;                                       
      end while;
      Append (~Solns, Prune (m));
   until (index gt len);
 
   return Solns;
end function;

// express b as sum of n entries from [0.. b] 
Weights := function (b, n)
   vprint Monomial: "Weights ", b, n;
   M := [b: i in [1..n]];
   S := BackTrack (M, b);
   // vprint Monomial: "Total time in Weights ", Cputime (tt);
   return [x : x in S | &+x eq b];
end function;

// 3.2 
Def_a := function (p, m: Sparse := true)
   if m le 2^30 then 
      C := CyclotomicField (m: Sparse := Sparse);
   else 
      error "Field cannot be constructed -- degree too large"; 
   end if;
   MA := MatrixAlgebra (C, p);
   a := Identity (MA);
   r := RootOfUnity (m, C);
   a[1,1] := r;
   return MA ! a;
end function;

// 3.2 
Apply_gamma := function (a)
   p := Nrows (a);
   block := [a[i,i]: i in [1..p]];
   block[1] := a[1,1] * a[p,p]^-1;
   for i in [2..p] do
      block[i] := a[i, i] * a[i-1, i - 1]^-1;
   end for;
   C := BaseRing (a);
   MA := MatrixAlgebra (C, p);
   return MA ! DiagonalMatrix (C, block);
end function;

// 3.2 
Apply_delta := function (a)
   p := Nrows (a);
   r := &*[a[i,i]: i in [1..p]];
   C := BaseRing (a);
   MA := MatrixAlgebra (C, p);
   return MA ! ScalarMatrix (C, p, r);
end function;

// 3.2 
Def_b := function (p, m)
   a := Def_a (p, m);
   b := Apply_gamma (a);
   return b;
end function;

// 3.2 
Def_z := function (p, m)
   a := Def_a (p, m);
   z := Apply_delta (a);
   return z;
end function;

// 3.7 
Def_x_pj := function (p, j)
   n := Ceiling (j / (p - 1));
   assert exists(m){m: m in [0..p - 2] | m eq (-j mod (p - 1))};
   assert j eq n * (p - 1) - m;
   x := Def_b (p, p^n);
   for i in [1..m] do x := Apply_gamma (x); end for;
   return x;
end function;

// 2.1 
Def_s := function (p)
   Z := Integers ();
   S := Sym (p);
   s := S.1;
   return GL(p, Z) ! PermutationMatrix (Z, s);
end function;

Def_v := function (p, F: Sparse := true)
   C := CyclotomicField (p: Sparse := Sparse);
   alpha := C.1;
   Alpha := [];
   for i in [1..p] do 
      for j in [1..p] do 
         Append (~Alpha, alpha^(i * j));
      end for;
   end for;
   return GL(p, F) ! Alpha;
end function;

// 2.4 
Def_t := function (p, F)
   S := Sym (p);
   r := PrimitiveRoot (p);
   perm := []; 
   for i in [0.. p - 2] do
      perm[r^i mod p] := r^(i + 1) mod p;
   end for;
   perm cat:= [p];
   t := Sym (p) ! perm;
   return GL(p, F) ! PermutationMatrix (F, t), t;
end function;

SModule := function (U: Group := false) 
   if Type (U) in {GrpMatElt, AlgMatElt} then U := [U]; end if;
   z := Rep (U);
   P := Generic (Parent (z));
   p := Degree (P);
   F := BaseRing (P);
   s := P ! Def_s (p);
   if Group then 
      return sub<GL(p, F) | &cat[[s^-i * z * s^i: i in [1..p - 1]]: z in U]>;
   else 
      return sub<MatrixAlgebra (F, p) | &cat[[s^-i * z * s^i: i in [1..p - 1]]: z in U]>;
   end if;
end function;

// 3.11 
Def_Y := function (p, j, k, l: Check := false)
   assert l in {0..p -1};
   assert k ge 0;
   if j eq 0 and l eq 0 then 
      Z := SModule (Def_z (p, p^k));
      return Z;
   elif j gt 0 and k gt 0 then 
      x1 := Def_x_pj (p, j + 1);
      z := Def_z (p, p^(k + 1));
      zl := z^l;
      X := SModule (Def_x_pj (p, j));
      z2 := Def_z (p, p^k);
      a := x1; b := [X.i: i in [1..Ngens (X)]]; c := z2;
      entries := Eltseq (a) cat Eltseq (zl) cat &cat ([Eltseq (x) : x in b]) cat Eltseq (c);
      F := MinimalField (entries);
      MA := MatrixAlgebra (F, p);
      a := MA ! Eltseq (x1) * MA ! Eltseq (zl); 
      H := sub<MA | a, [Eltseq (X.i): i in [1..Ngens (X)]], Eltseq (z2)>;
      return H;
   else
      "Invalid parameters";
      return false;
   end if;
   if Check then assert #H eq p^(j + k); end if;
end function;

Def_Polys := function (p, q)
   f, r, e := IsPrimePower (q);
   assert f;
   R := Integers ();
   P<x> := PolynomialRing (R);
   f := &+[x^i: i in [0..p - 1]];
   F := GF (q);
   Q<x> := PolynomialRing (F);
   g := &+[x^i: i in [0..p - 1]];
   return f, g;
end function;

EvaluatePoly := function (f, t)
   P<x> := Parent (f);
   C := Coefficients (f);
   return &+[C[i] * (x^t)^(i - 1): i in [1..#C]];
end function;

// 4.6 and 4.7 
Def_g_qr := function (g, q)
   p := Degree (g) + 1;
   assert IsPrime (q) and q mod p ne 0;
   d := Order (q, p);
   s := (p - 1) div d;
   facs :=Factorisation (g);
   facs := [f[1]: f in facs];
   Sort (~facs);
   g_qr := [facs[1]];
   t := PrimitiveRoot (p);
   for i in [1..s - 1] do 
      g_qr[i + 1] := Gcd (g, EvaluatePoly (g_qr[i], t)); 
   end for;
   assert Gcd (g, EvaluatePoly (g_qr[s], t)) eq g_qr[1];
   assert g eq &*g_qr;
   assert forall{e : e in g_qr | IsIrreducible (e)};
   return g_qr;
end function;

// 4.8 
Def_f_qn := function (p, q, n)
   assert IsPrime (q) and q mod p ne 0;
   d := Order (q, p);
   s := (p - 1) div d;

   f, g := Def_Polys (p, q);
   facs := Def_g_qr (g, q);
   T<t> := PolynomialRing (Integers (q^(n)));
   Z := Integers ();
   R<r> := PolynomialRing (Z);
   L := HenselLift (f, facs, T);
   Facs := [];
   for i in [1..s] do 
      rest := [L[j]: j in [1..#L] | j ne i];
      r := #rest eq 0 select L[1]^0 else &*rest;
      Append (~Facs, r);
   end for;
   Facs := [R!f: f in Facs];
   return Facs, facs, f;
end function;

MyEvaluate := function (f, s, b)
   C := Coefficients (f);
   return &*[s^(-i+1) * (b^C[i]) * s^(i-1): i in [1..#C]];
   // return &*[(b^C[i])^(s^(i-1)): i in [1..#C]];
end function;

// 4.12: element returned has order q^(dn) 
Def_x_qnr := function (p, q, n, r)
   // s := Def_s (p);
   facs := Def_f_qn (p, q, n);
   b := Def_b (p, q^n);
   K := BaseRing (Parent (b));
   // b := GL(p, K) ! b;
   s := GL(p, K) ! Def_s (p);
   x := MyEvaluate (facs[r], s, b);
   d := Order (q, p);
   return x, d * n;
end function;

Def_X_qnr := function (p, q, n, r)
   x, o := Def_x_qnr (p, q, n, r);
   return SModule (x), o;
end function;

// Lemma 4.11: want to construct an element of order q^b;
// but x_q(n,r) has order q^dk for some k, hence b must be divisible by d  
GetValid_n := function (p, q, b)
   d := Order (q, p);
   if b mod d ne 0 then return 0; else return b div d; end if;
end function;

// 4.19 for p-subgroup 
GetValid_jkl := function (p, b)
   L := [<j, k, l>: j in [0..b], k in [0..b], l in [0..p - 1] | j + k eq b];
   M := [[x[1], x[2], x[3]] : x in L | (x[1] eq 0 and x[3] eq 0 and x[2] gt 0) 
                              or (x[1] gt 0 and x[2] gt 0)]; 
   return M;
end function;

SetupGroups := function (p, C: Sparse := true, AlgebraParent := true)
   L := [ ];
   nmr := 0;
   for c in C do
      nmr +:= 1;
      lcm := LCM ([CyclotomicOrder (BaseRing (c[i])): i in [1..#c]]);
      vprint Monomial, 2: "SetupGroups: # and LCM is ", nmr, lcm;
      if lcm le 2^30 then 
         F := CyclotomicField (lcm : Sparse := Sparse);
      else 
         error "Field cannot be constructed -- degree too large"; 
      end if;
      E := &cat[[Eltseq (g): g in Generators (c[i])]: i in [1..#c]];
      MA := AlgebraParent select MatrixAlgebra (F, p) else GL(p, F);
      G := sub<MA | E>;
      Append (~L, G);
   end for;
   return L;
end function;

// set up q-subgroups: M = sum of s components each in {0..M} 
ProcessOrder := function (p, q, M: Sparse := true, Count := false) 
   X := [];
   s := (p - 1) div Order (q, p);
   W := Weights (M, s);
   if Count eq true then 
      return X, [[q] cat w: w in W];
   end if;

   for w in W do 
      x := [* Def_x_qnr (p, q, w[r], r) : r in [1..s] | w[r] ne 0 *];
      F := [BaseRing (Parent (a)): a in x];
      if #x eq 1 then 
         F := Rep (F);
      else 
         B := [BaseRing (Parent (f)): f in x];
         lcm := LCM ([CyclotomicOrder (f): f in B]);
         if lcm le 2^30 then 
            F := CyclotomicField (lcm: Sparse := Sparse);
         else 
            error "Field cannot be constructed -- degree too large"; 
         end if;
      end if;
      MA := MatrixAlgebra (F, p); 
      x := [MA | a : a in x];
      // x := [GL(p, F) | a : a in x];
      x := SModule (x);
      Append (~X, x);
   end for;
   W := [[q] cat w: w in W];
   return X, W;
end function;

// Gcd (p, D) = 1; construct subgroups of order D as direct products of 
// q-subgroups for q in Q, a list of primes   
ConstructCoprime := function (p, D: Count := false) 
   vprint Monomial, 2: "ConstructCoprime: p D", p, D;
   if D eq 1 then return [], []; end if;
   assert Gcd (p, D) eq 1; 
   fac := Factorisation (D);
   Q := [fac[i][1]: i in [1..#fac]];
   B := [fac[i][2]: i in [1..#fac]];
   M := [GetValid_n (p, Q[i], B[i]): i in [1..#fac]];
   if 0 in M then return [], []; end if;
   X := []; W := [];
   for i in [1..#Q] do 
      if M[i] gt 0 then 
         Xm, Wm := ProcessOrder (p, Q[i], M[i]: Count := Count);
         Append (~X, Xm);
         Append (~W, Wm);
      end if;
   end for;
   if Count eq false then 
      C := CartesianProduct (X);
      X := SetupGroups (p, C);
   else 
      X := [];
   end if;
   C := CartesianProduct (W);
   W := [[y: y in x]: x in C];
   return X, W;
end function;

// Sylow p-subgroup of order p^v 
ConstructSylowp := function (p, v: Count := false, AlgebraParent := true)
   M := GetValid_jkl (p, v);
   if Count eq false then 
      if AlgebraParent then
         Y := [* Def_Y (p, m[1], m[2], m[3]): m in M *];
         Y := [sub<MatrixAlgebra (BaseRing (Y[i]), p) | Generators (Y[i])>: i in [1..#Y]];
      else
         Y := [Def_Y (p, m[1], m[2], m[3]): m in M];
      end if;
   else
      Y := [];
   end if;
   M := [[p] cat m : m in M];
   return Y, M;
end function;

ConstructScalar := function (p, O)
   vprint Monomial, 2: "Order of scalar is ", O;
   z := Def_z (p, O);
   Z := [sub<Parent (z) | z>];
   return Z;
end function;

// Defn 4.19: construct complete list of finite <s>-modules
ConstructModules := function (p, O: Count := false) 
   assert IsPrime (p);
   // assert O gt 1; 

   if O gt 1 then 
      facs := Factorisation (O);
      primes := [f[1]: f in facs];
   else 
      facs := [<1,1>];
      primes := [1];
   end if;
   index := Position (primes, p);
   v := index gt 0 select facs[index][2] else 0; 
   if index gt 0 then Remove (~facs, index); end if;

   Z := Integers ();
   if O eq 1 then 
      m := 1;
   else 
      m := Z!facs;
   end if;
   D := Divisors (m);
   vprint Monomial, 1: "# of divisors is ", #D;
   L := []; Params := [];
   OrdZ := [];

   // Sylow p-subgroup 
   Y, M := ConstructSylowp (p, v: Count := Count);
   vprint Monomial: "#M is ", #M;

   for i in [1..#D] do
      vprint Monomial, 1: "ConstructModules i = ", i, "order of p'-dash scalars = ", D[i];

      // coprime q-groups 
      vprint Monomial, 2: "Coprime subgroups";
      Q, P := ConstructCoprime (p, D[i]: Count := Count);
      // "i Order ", i, D[i], [#x: x in Q];

      if D[i] gt 1 and #P eq 0 then continue; end if;
      // "Q order is ", D[i];
      
      // p-dash scalars 
      z := O div (D[i] * p^v);
      vprint Monomial, 1: "Scalar matrix of order", z;
      if Count eq false then 
         Z := ConstructScalar (p, z);
      end if;

      if #P eq 0 and #M eq 0 then 
         vprint Monomial, 2:"ConstructModules: Case 1";
         A := Z;
         P := [[[], []]];
      elif #P eq 0 then 
         vprint Monomial, 2: "ConstructModules: Case 2";
         if Count eq false then 
            C := CartesianProduct ([Y, Z]);
            A := SetupGroups (p, C);
         end if;
         P := [[m] : m in M];
      elif #M eq 0 then 
         vprint Monomial, 2: "ConstructModules: Case 3";
         if Count eq false then 
            C := CartesianProduct ([Q, Z]);
            A := SetupGroups (p, C);
         end if;
         P := [Append (x, [p,0,0,0]): x in P];
      else 
         vprint Monomial, 2: "ConstructModules: Case 4";
         if Count eq false then 
            C := CartesianProduct ([Q, Y, Z]);
            // "#C is ", #C;
            A := SetupGroups (p, C);
         end if;
         C := CartesianProduct (P, M);
         P := [x : x in C];
         P := [Append (x[1], x[2]): x in P];
      end if;
      
      if Count eq false then 
         OrdZ cat:= [z: k in [1..#P]];
         Append (~L, A);
      end if;
      Append (~Params, P);
   end for;
   return &cat(L), &cat (Params), OrdZ;
end function;

// value of s for prime q 
S := function (p, q)
   assert IsPrime (p);
   assert IsPrime (q);
   d := Order (q, p);
   s := (p - 1) div d;
   return s;
end function;

// Lemma 6.11
EliminateReducible := function (p, P, O: offset := 0)
   L := [];
   Q := QPrimes (p, O);
   for i in [1..#P] do
      flag := exists(k){k: k in [1..#P[i] - offset] | #P[i][k] gt 0 and P[i][k][1] in Q};
      flag := flag or exists(k){k: k in [1..#P[i] - offset] | #P[i][k] eq 4 and
                                   P[i][k][1] eq p and P[i][k][2] gt 0};
      if flag then Append (~L, i); end if;
   end for;
   return L;
end function;

// complete list of irreducible monomial subgroups of GL(p, C) 
// with projection <s>
IrreducibleGroups := function (p, O: Count := false)
   L, P := ConstructModules (p, O: Count := Count);
   vprint Monomial: "# of modules constructed is ", #P;
   index := EliminateReducible (p, P, O: offset := 0);
   if Count eq false then 
      L := [L[i]: i in index];
   end if;
   P := [P[i]: i in index];

   I := []; R := [];
   for ell in [1..#P] do 
      if Count eq false then 
         G := L[ell];
      end if;
      params := P[ell];

      if exists(j){j : j in [1..#params] | #params[j] gt 0 and params[j][1] cmpeq p} then 
         k := params[j][3]; 
      else 
         k := 0; 
      end if;
      if Count eq false then 
         z := Def_z (p, p^(k + 1));
         PZ := Generic (Parent (z));
         s := PZ!Def_s (p);
         gens := [s * z^i: i in [0..p - 1]];
         add := [sub<PZ | Eltseq (a) >: a in gens]; 
         C := CartesianProduct ([G], add);
         J := SetupGroups (p, C);
         Append (~I, J);
      end if;
      if forall{x : x in params | #x eq 0} then 
         params := [[[i]]: i in [0..p - 1]]; 
      else 
         params := [Append (params, [i]): i in [0..p - 1]];
      end if;
      Append (~R, params);
   end for;

   R := &cat (R);
   if Count eq false then 
      I := &cat (I); 
   else 
      I := [];
   end if;
   return I, R;
end function;

// Defn 5.10: partition list of parameters returning lists L1, .., L4  
MyPartitionLists := function (p, P)
   L1 := []; L2 := []; L3 := []; L4 := [];
   for m in [1..#P] do
      params := P[m]; len := #params;
      i := params[len][1];
      Y_params := params[len - 1];
      j := Y_params[2]; k := Y_params[3]; l := Y_params[4]; 
      assert Y_params[1] eq p;
      N := &join{{params[i][j]: j in [2..#params[i]]}: i in [1..len - 2]};
      if N eq {} then N := {0}; end if;
      if i in {0, 1} and l eq 0 and j eq 1 and N eq {0} then
         Append (~L1, m);
      elif i eq 1 and l eq 0 and (j ge 2 or exists{n: n in N | n gt 0}) then
         Append (~L2, m);
      elif i eq 0 and l eq 0 and (j ge 2 or exists{n: n in N | n gt 0}) then
         // Append (~L3, m);
         // correction to Defn 5.10 
         omit := j eq 0 and l eq 0 and k eq 0;
         if not omit then Append (~L3, m); end if;
      elif i eq 0 and l ne 0 and (j ge 2 or exists{n: n in N | n gt 0}) then
         Append (~L4, m);
      end if;
   end for;
   return L1, L2, L3, L4;
end function;

// Defn 5.14 
Table := function (p, P, Q)
   Z := Integers ();
   R := RMatrixSpace (Z, #Q, p - 1);
   V := RMatrixSpace (Z, 1, p - 1);
   T := [Zero (V): i in [1..#Q]];
   len := #P;
   for i in [1..len - 2] do 
      q := P[i][1];
      w := Position (Q, q);
      s := S (p, q);
      N := [P[i][j]: j in [2..#P[i]]];
      for r in [s + 1..p - 1] do
         N[r] := N[r - s];
      end for;
      T[w] := V!N;
   end for;
   return R!T;
end function;

// action of permutation matrix t on A 
Image_under_t := function (A)
   B := Transpose (A);
   P := Parent (B);
   r := Nrows (B);
   x := [B[r]] cat [B[i]: i in [1..r - 1]];
   return Transpose (P!x);
end function;

// action of n-th power of t on A 
Image_under_power := function (A, n)
   I := A;
   for i in [1..n] do 
      I := Image_under_t (I);
   end for;
   return I;
end function;

// orbit under t^n 
ConstructOrbit := function (v, n)
   O := {@ v @};
   k := 1; 
   while k le #O do
      pt := O[k];
      im := Image_under_power (pt, n);
      Include (~O, im);
      k +:= 1;
   end while;
   return O;
end function;

AllOrbits := function (A, n)
   O := [];
   if #A eq 0 then return O; end if;
   repeat 
      x := Rep (A);
      orbit := ConstructOrbit (x, n);
      A := A diff {o : o in orbit};
      Append (~O, orbit);
   until #A eq 0;
   return O;
end function;

// Defn 5.16 and 6.15  
// Q is ordered list of primes 
// L is subsequence of [1..#P] 
// P is sequence of parameters 
// for each relevant element of P, construct its table and orbit of that 
// table under (a power of) the permutation matrix t;
// if the table is the minimal element of its orbit, then the corresponding 
// element of P is a conjugacy class rep 
// t_orbit is orbit under t, otherwise orbit under t^((p - 1) div j_sharp)  
// this last power is correction to 5.10 and 6.15 

ConstructL_star := function (p, P, L, O: t_orbit := true)
   if #L le 1 then return L, P; end if;
   Q := QPrimes (p, O);
   if t_orbit then 
      T := [Table (p, P[L[i]], Q): i in [1..#L]];
      O := AllOrbits (Set (T), 1);
      assert &+[#x: x in O] eq #Set (T);
      table_reps := [Minimum (o): o in O];
      reps := [i: i in [1..#T] | T[i] in table_reps];
      index := [L[i]: i in reps];
   else 
      r := PrimitiveRoot (p);
      index := []; reps := [];
      for i in [1..#L] do 
         R := P[L[i]];
         paras := R[#R - 1]; 
         assert #paras eq 4; // [p, j, k, l]
         l := paras[4]; 
         j := paras[2]; 
         j_sharp  := Gcd (p - 1, j);
         if l in {r^e mod p: e in {1..j_sharp}} then 
            T := Table (p, R, Q);
            // EOB -- correction to 5.10 and 6.15 
            // O := ConstructOrbit (T, j_sharp);
            O := ConstructOrbit (T, (p - 1) div j_sharp);
            if Minimum (O) eq T then 
               Append (~index, i);
               Append (~reps, T);
            end if;
         end if;
      end for;
      index := [L[i]: i in index];
   end if;
   Sort (~index);
   return index, reps;
end function;
