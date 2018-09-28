/* quick test */
load "experiments/om5_search.m";

q := 17;
k := GF (q);
V := VectorSpace (k, 5);
Q := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);
Om := MyOmega (5, q); 
l := sub < V | V.4 , V.5 >;
TYPE := IdentifyLineType (Q, l);
rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
R := Centralizer (Om, rho);
reps := [ c[3] : c in ConjugacyClasses (R) | 
    (c[1] eq 2) and (c[3] ne rho) and (Dimension (Eigenspace (c[3],1)) eq 3) ];
[ #Conjugates (R, x) : x in reps ];

gREPS := [ reps[2] , reps[3] ];

rho0, R0, GRPS0 := Omega5_Search (q);
assert rho0 eq rho;
for i in [1..#GRPS0] do
  "i =", i;
  GRPSi := GRPS0[i];
  { SchlafliSymbol (H) : H in GRPSi };
  [ [WhichClass (R, gREPS, H.j) : j in [3,4]] : H in GRPSi ];
end for;

for i in [1..#gREPS] do
"rep", i;
  r := gREPS[i];
  m := Eigenspace (r, -1);
  "<l, m> =", MyWittIndex (Q, PerpSpace (Q, l meet m));
  "<l, m*> =", MyWittIndex (Q, PerpSpace (Q, l meet PerpSpace (Q, m)));
  "<l*, m> =", MyWittIndex (Q, PerpSpace (Q, PerpSpace (Q, l) meet m));
  "<l*, m*> =", IdentifyLineType (Q, PerpSpace (Q, l) meet PerpSpace (Q, m));
  "-------";
end for;

