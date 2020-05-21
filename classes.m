// conjugacy classes of soluble monomial subgroups of order m in GL(p, C)
MonomialSolubleClasses := function (p, m)
   if m mod p ne 0 then return []; end if;
   L := Chap5 (p, m div p);
   La := Chap6 (p, m);
   Append (~La, L);
   return &cat (La), La;
end function;

// conjugacy classes of soluble monomial subgroups of order m in GL(p, C)

MonomialInsolubleClasses := function (p, m)
   L := [];
   if p ge 5 and m mod Factorial (p) eq 0 then 
      L cat:= Sym_Reps (p, m);
   end if;
   if p ge 5 and 2 * m mod Factorial (p) eq 0 then 
      L cat:= Alt_Reps (p, m);
   end if;
   if p eq 7 and m mod 168 eq 0 then 
      L cat:= SL32_Reps (p, m);
   end if;
   if p eq 11 and m mod 660 eq 0 then 
      L cat:= PSL211_Reps (p, m);
   end if;
   if p eq 11 and m mod 7920 eq 0 then 
      L cat:= M11_Reps (p, m);
   end if;
   if p eq 23 and m mod 10200960 eq 0 then 
      "NEED to add results for M23";
   end if;
   return L;
end function;

PrimitiveClasses := function (p, m: Soluble := false)
   if p eq 3 then
      return PrimitiveDimension3 (m: Soluble := Soluble);
   elif p eq 2 then 
      return PrimitiveDimension2 (m: Soluble := Soluble);
   else
      error "Dimension is restricted to 2 or 3"; 
   end if;
end function;
