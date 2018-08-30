/* check claims in notes */

__test_line := function (L, g, B)
return (Dimension (L*g meet L) eq 0) and (Dimension (L*g meet PerpSpace (B, L)) eq 0);
end function;

q := 17;  "q =", q;  k := GF (q);  V := VectorSpace (k, 5);
GG := MyGO (5, q);
G := MyOmega (5, q);   assert G subset GG;
F := Identity (MatrixAlgebra (k, 5));

rho := InvolutionOdd (sub<V|V.3,V.4,V.5>, sub<V|V.1,V.2>);  assert rho in G;
assert forall { i : i in [1..Ngens(G)] | G.i * F * Transpose (G.i) eq F };

z := V.5;  Z := sub < V | z >;  U := PerpSpace (F, Z);
GZ := Stabilizer (G, Z);  assert rho in GZ;
U := sub < V | V.1 , V.2 , V.3 , V.4 >;  assert U eq PerpSpace (F, Z);

tau0 := InvolutionOdd (sub<V|V.1>, sub<V|V.2,V.3,V.4,V.5>);   assert tau0 in GZ;
GGZ := Stabilizer (GG, Z);
T0 := Conjugates (GGZ, tau0);   assert #T0 eq #Conjugates (GZ, tau0);

pts0 := { sub < U | u > : u in U | InnerProduct (u * F, u) ne 0 };
pts1 := { P : P in pts0 | MyWittIndex (RestrictBilinearForm (F, PerpSpace (F, P))) eq 2 };
assert #T0 eq #pts1;

CGG := Centralizer (GGZ, rho);
//T0 := [ t : t in T0 | (t, rho) ne Identity (GZ) ];
T0 := [ t : t in T0 | Order (rho * t) eq (q+1) ];
"|T0| =", #T0;
T := RefineClass (T0, CGG);
"|T| =", #T;

CG := Centralizer (GZ, rho);
"|CG| =", #CG; 
cl := ConjugacyClasses (CG);
icl := [ c : c in cl | c[1] eq 2 ];
"|icl| =", #icl;
S0reps := [ c[3] : c in icl | (not IsScalar (c[3] * rho)) and (Dimension (Eigenspace (c[3], 1)) gt 1) ];
"|S0reps| =", #S0reps;
S0 := &join [ Conjugates (CG, S0reps[i]) : i in [1..#S0reps] ];
"|S0| =", #S0;
Erp := U meet Eigenspace (rho, 1);  Erm := U meet Eigenspace (rho, -1);
inc := [ ];
for s in S0 do
  Esp := U meet Eigenspace (s, 1);  Esm := U meet Eigenspace (s, -1);
  Append (~inc, [Dimension(Erp meet Esp), Dimension(Erp meet Esm), Dimension (Erm meet Esp), 
     Dimension (Erm meet Esm)]);
end for;
"incidence types:", Set (inc);
"=========";

good := [ ];   bad := [ ];
good_inc := [ ];   bad_inc := [ ];
for i in [1..#T] do
"testing <tau> candidate", i, "out of", #T, "...";
  tau := T[i];
  Wi := Eigenspace (tau, 1);   assert Wi subset U;
  Li := (Wi + sub < U | V.1 , V.2 >) meet (Wi + sub < U | V.3, V.4 >);
     assert (Li * rho eq Li) and (Li * tau eq Li);
  D := sub < GZ | rho , tau >;
     if #InduceGroup (D, Li) ne 2*(q+1) then
     "   ALERT: |rho * tau| =", Order (rho * tau), "   yet |D_Li| =", #InduceGroup (D, Li);
     end if;
  CD := Centralizer (GGZ, D);
  "   |CD| =", #CD, "    abelian?", IsAbelian (CD);
//  S0 := [ s : s in S0 | (s, tau) ne Identity (GZ) ];
  S0 := [ s : s in S0 | Order (tau * s) eq (q+1) ];
  S := RefineClass (S0, CD);
  goodi := [ ];
  badi := [ ];
  for j in [1..#S] do
       sigma := S[j];
       Esp := U meet Eigenspace (sigma, 1);  Esm := U meet Eigenspace (sigma, -1);
       h := tau * sigma;   assert Order (h) eq (q+1);
       J := sub < GZ | rho, tau, sigma >;
       if J eq GZ then
            //assert exists {a : a in [1..q] | __test_line (Li, h^a, F)};
            Append (~goodi, [rho, tau, sigma]);
            Append (~good_inc, [Dimension(Erp meet Esp), Dimension(Erp meet Esm), Dimension (Erm meet Esp), 
     Dimension (Erm meet Esm)]);
       else
            //assert forall {a : a in [1..q] | not __test_line (Li, h^a, F)};
            Append (~badi, [rho, tau, sigma]);
            Append (~bad_inc, [Dimension(Erp meet Esp), Dimension(Erp meet Esm), Dimension (Erm meet Esp), 
     Dimension (Erm meet Esm)]);
       end if;
  end for;
  "   of the", #S, "corresponding <sigma> candidates,", #goodi, " were good, and", #badi,"were bad";
  "----------";
  good cat:= goodi;
  bad cat:= badi;
end for;
"|good| =", #good, "    |bad| =", #bad;
Set ([ SchlafliSymbol (t) : t in good ]);



__examine_triple := function (trip, U, F)
  a := trip[1];  b := trip[2];  c := trip[3];
  Ap := U meet Eigenspace (a, 1);  Am := U meet Eigenspace (a, -1);
  Bp := U meet Eigenspace (b, 1);  Bm := U meet Eigenspace (b, -1);
  Cp := U meet Eigenspace (c, 1);  Cm := U meet Eigenspace (c, -1);
  lAB := (Ap + Bp) meet (Am + Bp);
  lBC := (Cp + Bp) meet (Cm + Bp);
  W := lAB + lBC;  
return (Dimension (W) eq 3) and not (forall { i : i in [1,2,3] | W * trip[i] eq W });
end function;

"good test:", { __examine_triple (t, U, F) : t in good };
"bad test:", { __examine_triple (t, U, F) : t in bad };
"good incidences", Set (good_inc);
"bad incidences", Set (bad_inc);
