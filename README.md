# Monomial
Monomial groups in characteristic 0 and prime degree 

Dane Flannery and Eamonn O'Brien

The code is based on the paper: 

Z. B'acskai, D.L. Flannery, and E.A. O'Brien.  "Classifying finite monomial linear groups of prime degree in characteristic zero". 
Internat. Journal Algebra Comput. 2021
https://arxiv.org/abs/2107.12252 

===========================

Intrinsic functions are the following:

intrinsic MonomialClasses (p :: RngIntElt, m :: RngIntElt :
  Algebras := false, Count := false, Soluble := true, Insoluble := true) -> [], []
  
{return representatives of conjugacy classes of monomial irreducible subgroups
 of order m in GL(p, C), where p is a prime, and their parameters;
 if either Soluble or Insoluble is false, then the corresponding groups
 are omitted; default for both is true; if Count then return [] and sequence
 of parameters for the classes; if Algebras then return algebras, not groups,
 reducing associated setup time}

intrinsic IrreducibleClasses (p :: RngIntElt, m :: RngIntElt:
  Soluble := true, Insoluble := true) -> [], [] 

{return representatives of conjugacy classes of irreducible subgroups
 of order m in GL(p, C), where p is 2 or 3, as separate lists of monomial 
 and primitive groups; if either Soluble or Insoluble is false, then the
 corresponding groups are omitted; default for both is true.}

A few examples:

// all 5-dimensional monomial representation for groups of order 2000

L := MonomialClasses (5, 2000);

// all 7-dimensional monomial representations for insoluble groups of order 55440

L := MonomialClasses (7, 55440: Soluble := false);

// count the number of 3-dimensional monomial representations for groups of order 270000

// L is empty; the # of representation is #P

L, P := MonomialClasses (3, 270000: Count := true);

#P; // number of classes  

// all 3-dimensional irreducible groups of order 3600

M, P := IrreducibleClasses (3, 3600);

#M; // monomial groups

#P; // primitive groups 


The following files illustrate related computations:
insoluble-table3, soluble-table3, table2, insoluble-checks

The file misc.m has some auxiliary functions which may be useful for working with the output of the intrinsic functions. 

