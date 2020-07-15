AttachSpec ("spec");
import "classes.m": PrimitiveClasses;

load "checks/schur.m";

SKIP := [];
p := 2;
for m in [2..1000 by 2] do 
if NumberOfSmallGroups (m) gt 10^2 then Append (~SKIP, m); continue m; end if;

"\n\n Order = ", m;

X := PrimitiveClasses (2, m: Insoluble:=false);

ids := [IdentifyGroup (x): x in X];
"Set of ids is ", Multiset (ids);
flag := forall{x :x in X | #x eq m};
if not flag then 
   "*** error orders";
   continue;
end if;

assert forall{x :x in X | #x div #Centre (x) in {12, 24, 60}};

S := SmallGroups (m);
index := [i: i in [1..#S] | HasMonomialReps (S[i])];
J := {1..NumberOfSmallGroups (m)} diff Set (index);
J := [i : i in J];
J := [i: i in J | IsSoluble (SmallGroup (m, i))];
Sort (~J);
"J is ", J;
"Possible ids are ", #J;
N := [NumberOfReps (SmallGroup (m, i), p): i in J ];
"Number of prim reps ", N;
"Number of iso types having prim reps", #[x :x in N | x ne 0];
"Total number is ", &+N;
assert &+N eq #X;

end for;
