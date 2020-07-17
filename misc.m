AttachSpec ("spec");

// by default group is defined over sparse cyclotomic field; 
// best to convert to standard field before doing computations with group
SparseToStandard := function (G)
   d := Degree (G);
   o := CyclotomicOrder (BaseRing (G));
   C := CyclotomicField (o);
   return sub<GL(d, C) | Generators (G)>;
end function;

// return group having same generators as algebra 
AlgebraToGroup := function (A)
   F := BaseRing (A);
   p := Degree (A);
   G := sub<GL(p, F) | [A.j : j in [1..Ngens (A)]]>;
   return G;
end function;


// example of their use 

/* 

time A, B := MonomialClasses (7, 168 * 8: Algebras:=true, 
                           Soluble := false);
G := AlgebraToGroup (A[3]);
G := SparseToStandard (G);
f, I := IsomorphicCopy (G);
LMGCompositionFactors (I);
*/


