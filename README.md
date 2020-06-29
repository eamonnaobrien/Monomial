# Monomial
Monomial groups in characteristic 0 and prime degree 

Dane Flannery and Eamonn O'Brien
Code prepared June 2020
===========================

Intrinsic functions are the following:

intrinsic MonomialClasses (p :: RngIntElt, m :: RngIntElt :
  Algebras := false,
  Count := false, Soluble := true, Insoluble := true) -> [], []
{return representatives of conjugacy classes of monomial subgroups
 of order m in GL(p, C), where p is a prime, and their parameters;
 if either Soluble or Insoluble is false, then the corresponding groups
 are omitted; default for both is true; if Count then return [] and sequence
 of parameters for the classes; if Algebras then return algebras, not groups,
 reducing associated setup time}

intrinsic IrreducibleClasses (p :: RngIntElt, m :: RngIntElt:
  Soluble := true, Insoluble := true) -> []
{return representatives of conjugacy classes of irreducible subgroups
 of order m in GL(p, C), where p is 2 or 3, as lists of monomial and
 primitive groups; if either Soluble or Insoluble is false, then the
 corresponding groups are omitted; default for both is true.}

A few examples:

// all 5-dimensional monomial representation for groups of order 2000
L := MonomialClasses (5, 2000);

// all 7-dimensional monomial representations for insoluble groups of order 55440
L := MonomialClasses (7, 55440: Soluble := false);

// count the number of 3-dimension monomial representations for groups of order 270000
// L is empty; the # of representation is #P
L, P := MonomialClasses (3, 270000: Count := true);
#P; 

// all 3-dimensional irreducible groups of order 3600
L := IrreducibleClasses (3, 3600);

