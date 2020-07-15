declare verbose Monomial, 2;

import "filter.m": Chap5, Chap6;
import "faster.m": FastChap5, FastChap6;
import "symmetric.m": Sym_Reps;
import "alt.m": Alt_Reps;
import "sl32.m": SL32_Reps;
import "psl211.m": PSL211_Reps;
import "m11.m": M11_Reps;
import "m23.m": M23_Reps;
import "primitive-3.m": PrimitiveDimension3;
import "primitive-2.m": PrimitiveDimension2;

AlgebrasToGroups := function (A, p)
   L := [];
   for i in [1..#A] do
      F := BaseRing (A[i]);
      G := sub<GL(p, F) | [A[i].j : j in [1..Ngens (A[i])]]>;
      Append (~L, G);
   end for;
   return L;
end function;

// conjugacy classes of soluble monomial subgroups of order m in GL(p, C)
MonomialSolubleClasses := function (p, m: Algebras := false, 
   Fast := true, Count := false)

   if m mod p ne 0 then return [], []; end if;
   if Fast and Count eq false then 
      vprint Monomial, 1: "Running faster soluble code";
      L, P := FastChap5 (p, m);
      La, Pa := FastChap6 (p, m);
      vprint Monomial, 1: "Now convert", #L + #La, "algebras to groups";
      if Algebras then
         return L cat La, P cat Pa;
      else 
         return AlgebrasToGroups (L cat La, p), P cat Pa;
      end if;
   else
      vprint Monomial, 1: "Running original soluble code";
      L, P := Chap5 (p, m: Count := Count);
      La, Pa := Chap6 (p, m: Count := Count);
      L cat:= &cat La;
      P cat:= &cat Pa;
      return (L), (P);
   end if;
end function;

// conjugacy classes of soluble monomial subgroups of order m in GL(p, C)

MonomialInsolubleClasses := function (p, m: Count := false, Algebras := false)
   L := []; P := [];

   if p ge 5 and m mod Factorial (p) eq 0 then 
      X, Y := Sym_Reps (p, m: Count := Count);
      L cat:= X; P cat:= Y;
   end if;

   if p ge 5 and 2 * m mod Factorial (p) eq 0 then 
      X, Y := Alt_Reps (p, m: Count := Count);
      L cat:= X; P cat:= Y;
   end if;

   if p eq 7 and m mod 168 eq 0 then 
      X, Y := SL32_Reps (p, m: Count := Count);
      L cat:= X; P cat:= Y;
   end if;

   if p eq 11 and m mod 660 eq 0 then 
      X, Y := PSL211_Reps (p, m: Count := Count);
      L cat:= X; P cat:= Y;
   end if;

   if p eq 11 and m mod 7920 eq 0 then 
      X, Y := M11_Reps (p, m: Count := Count);
      L cat:= X; P cat:= Y;
   end if;

   if p eq 23 and m mod 10200960 eq 0 then 
      X, Y := M23_Reps (p, m: Count := Count);
      L cat:= X; P cat:= Y;
   end if;

   if Algebras then 
      return L, P;
   else 
      return AlgebrasToGroups (L, p), P; 
   end if;
end function;

intrinsic MonomialClasses (p :: RngIntElt, m :: RngIntElt : 
  Algebras := false, 
  Count := false, Soluble := true, Insoluble := true) -> [], []
{return representatives of conjugacy classes of monomial irreducible subgroups 
 of order m in GL(p, C), where p is a prime, and their parameters;
 if either Soluble or Insoluble is false, then the corresponding groups 
 are omitted; default for both is true; if Count then return [] and sequence
 of parameters for the classes; if Algebras then return algebras, not groups,
 reducing associated setup time}

   require IsPrime (p): "Dimension must be prime";

   if m mod p ne 0 then return [], []; end if;
   if Soluble eq false and Insoluble eq false then return [], []; end if;

   Fast := true;
   if Soluble then 
      LS, PS := MonomialSolubleClasses (p, m: Fast := Fast, Algebras := Algebras, Count := Count);
      vprint Monomial: "Soluble list has length ", #PS;
      if not Insoluble then return LS, PS; end if;
   end if;
    
   if Insoluble then 
      L, P := MonomialInsolubleClasses (p, m: Count := Count, Algebras := Algebras);
      vprint Monomial: "Insoluble list has length ", #P;
      if not Soluble then return L, P; end if;
   end if;

   return LS cat L, PS cat P;
end intrinsic;

PrimitiveClasses := function (p, m: Soluble := true, Insoluble := true)
   if p eq 3 then
      return PrimitiveDimension3 (m: Soluble := Soluble, Insoluble := Insoluble);
   elif p eq 2 then 
      return PrimitiveDimension2 (m: Soluble := Soluble, Insoluble := Insoluble);
   end if;
end function;

intrinsic IrreducibleClasses (p :: RngIntElt, m :: RngIntElt: 
  Soluble := true, Insoluble := true) -> [], []
{return representatives of conjugacy classes of irreducible subgroups 
 of order m in GL(p, C), where p is 2 or 3, as separate lists of monomial 
 and primitive groups; if either Soluble or Insoluble is false, then the 
 corresponding groups are omitted; default for both is true.}

   require p in {2, 3}: "Dimension 2 and 3 only";
   M := MonomialClasses (p, m: Soluble := Soluble, Insoluble := Insoluble);
   if (not Soluble and not Insoluble) then
      P := [];
   elif (Soluble and Insoluble) then 
      P := PrimitiveClasses (p, m);
   elif Soluble eq false then 
      P := PrimitiveClasses (p, m: Soluble := false); 
   elif Insoluble eq false then 
      P := PrimitiveClasses (p, m: Insoluble := false); 
   end if;
  
   return M, P;
end intrinsic;
