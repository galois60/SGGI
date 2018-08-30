// BUILD 5-POLYTOPE FOR Omega(5,q) FROM SCRATCH AT RANDOM

/*
q := 11;
k := GF (q);
V := VectorSpace (k, 5);
G := Omega (5, q);
F := ClassicalForms (G)`bilinearForm;
Q := ClassicalForms (G)`quadraticForm;
WL := sub < V | V.3 >;
UL := sub < V | [ V.i : i in [1,2,4,5] ] >;
if q mod 4 eq 1 then
     type := "hyperbolic";
else
     type := "asingular";
end if;
repeat
     z := Random (UL);
until InnerProduct (z * Q, z) ne 0;
repeat
     repeat
          u1 := Random (UL);
          U1 := sub < V | z , u1 >;
     until Dimension (U1) eq 2;
until IdentifyLineType (Q, U1) eq type;
W1 := PerpSpace (F, U1);
repeat
     repeat
          u3 := Random (UL meet W1);
          U3 := sub < V | z , u3 >;
     until (Dimension (U3) eq 2) and (Dimension (U3 meet U1) eq 1);
until IdentifyLineType (Q, U3) eq type;
W3 := PerpSpace (F, U3);
assert (Dimension (W1 meet W3) eq 2) and (WL subset (W1 meet W3));
X1 := UL meet W1;
X3 := UL meet W3;
assert UL eq (U1 + U3 + X1 + X3);
i1 := InvolutionOdd (W1, U1);
i3 := InvolutionOdd (W3, U3);
"[i1, i3] = 1?", (i1, i3) eq Identity (G);

pts0 := { sub<UL|u> : u in UL | u ne 0 };
"|pts0| =", #pts0;
pts1 := { P : P in pts0 | InnerProduct (P.1 * F, P.1) ne 0 };
"|pts1| =", #pts1;
pts2 := { P : P in pts1 | 
              forall { Y : Y in {U1, U3, X1, X3} | Dimension (P meet Y) eq 0 } };
"|pts2| =", #pts2;
pts3 := { P : P in pts2 | InvolutionOdd (P, PerpSpace (F, P)) in G };
"|pts3| =", #pts3;

I2 := [ InvolutionOdd (P, PerpSpace(F, P)) : P in pts3 ];
for j in [1..#I2] do
"j =", j, "   out of", #I2;
   i2 := I2[j];
"  |i1 * i2| =", Order (i1*i2);
"  |i2 * i3| =", Order (i2*i3);
L := sub < G | [ i1 , i2 , i3 ] >;
"  comp facs L:"; CompositionFactors (L);
end for;
*/

/*
repeat
     repeat 
          x2 := sub < V | Random (UL) >;
     until (InnerProduct (x2.1 * Q, x2.1) ne 0) and 
        forall { Y : Y in {U1, U3, W1, W3} | Dimension (x2 meet Y) eq 0 };
     H2 := PerpSpace (F, x2);
     i2 := InvolutionOdd (x2, H2);
until i2 in G;
"|i1 * i2| =", Order (i1*i2);
"|i2 * i3| =", Order (i2*i3);

L := sub < G | [ i1 , i2 , i3 ] >;
"comp facs L:"; CompositionFactors (L);
LUL := InduceGroup (L, UL);
M12 := GModule (sub<LUL|LUL.1,LUL.2>);
M23 := GModule (sub<LUL|LUL.2,LUL.3>);
*/



// ANALYZE THE 5-POLYS FOR PSp(4,q) CONSTRUCUTED BY BRUTE FORCE WITHIN Omega(5,q)
/*
q := 11;
SpH := SpHyperbolic (4, q);
assert forall { t : t in SpH_polys | t subset SpH };
PSpH, pi := ProjectiveGroup (SpH);
proj_polys := [ t @ pi : t in SpH_polys ];
proj_types := [ SchlafliSymbol (t) : t in proj_polys ];

// study 4-polytopes inside isomorphic group Omega(5,q)
Om := Omega (5, q);
isit, fOm, gOm := RecogniseSp4 (Om, q); assert isit;
isit, fSpH, gSpH := RecogniseSp4 (SpH, q); assert isit;
Om_polys := [ (t @ fSpH) @ gOm : t in SpH_polys ];
Om_types := [ SchlafliSymbol (t) : t in Om_polys ]; 
assert proj_types eq Om_types;
DT := Set (Om_types);
dpols := [ ];
for type in DT do
     assert exists (t){ u : u in Om_polys | SchlafliSymbol (u) eq type };
     Append (~dpols, t);
end for;

V := VectorSpace (GF (q), 5);
Q := ClassicalForms (Om)`quadraticForm;
F := ClassicalForms (Om)`bilinearForm;

for i in [1..#dpols] do
"i =", i;
  t := dpols[i];
  assert forall { i : i in [1..4] | SpinorNorm (QuadraticSpace (Q), t[i]) eq 0 };
  x2 := Eigenspace (t[2], 1); assert Dimension (x2) eq 1;
  X2 := Eigenspace (t[2], -1); assert Dimension (X2) eq 4;
  L := sub<Om|[t[i] : i in [1,2,3]]>;
  R := sub<Om|[t[i] : i in [2,3,4]]>;
  ML := GModule (L);
  MR := GModule (R);
  IL := IndecomposableSummands (ML);
  IL := [ sub < V | [ V!(ML!(N.i)) : i in [1..Ngens (N)] ] > : N in IL ];
  IR := IndecomposableSummands (MR);
  IR := [ sub < V | [ V!(MR!(N.i)) : i in [1..Ngens (N)] ] > : N in IR ];
  assert exists (XL){ N : N in IL | Dimension (N) eq 4 }; assert x2 subset XL;
  assert exists (YL){ N : N in IL | Dimension (N) eq 1 };
  assert exists (XR){ N : N in IR | Dimension (N) eq 3 };
  assert exists (YR){ N : N in IR | Dimension (N) eq 2 };
  QXL := RestrictQuadraticForm (Q, XL);
  LXL := InduceGroup (L, XL);
  UL := QuadraticSpace (QXL);
  assert IsIsometric (UL, QuadraticSpace (ClassicalForms (OmegaPlus (4,q))`quadraticForm));
  "spinor norms of LXL gens on quadratic space UL:", [ SpinorNorm (UL, LXL.i) : i in [1..Ngens (LXL)] ];
  "determinants of LXL gens:", [ Determinant (LXL.i) : i in [1..Ngens (LXL)] ];
  "line YR has type", IdentifyLineType (Q, YR);
  assert XL eq PerpSpace (F, YL);
  assert XR eq PerpSpace (F, YR);
  XX := XL meet XR;  assert Dimension (XX) eq 2; 
  "x2 on XX?", x2 subset XX;
  "line XX has type", IdentifyLineType (Q, XX);
  XY := XL meet YR;  assert Dimension (XY) eq 1;
  "XY on X2?", XY subset X2;
  "XY on E3minus?", XY subset Eigenspace (t[3], -1);
  if InnerProduct(XY.1 * Q, XY.1) eq 0 then "XY is singular"; else "XY is nonsingular"; end if;
  YX := YL meet XR;
  YY := YL meet YR;
  LR := L meet R;  M := sub < Om | t[2] , t[3] >;  assert LR eq M; 
  MXX := InduceGroup (M, XX);
  "gens of MXX:"; [ MXX.i : i in [1..Ngens (MXX)] ];
  "|t[2] * t[3]| =", Order (t[2] * t[3]); assert 2 * Order (t[2] * t[3]) eq #M;
  "-------------";
end for;

/*
for i in [1..#dpols] do
     t := dpols[i];
     "i =", i;
     "Schlafli type of t:", SchlafliSymbol (t);
     Etp := [ Eigenspace (t[j], 1) : j in [1..4] ];
     Etm := [ Eigenspace (t[j], -1) : j in [1..4] ];
     "  ";
     "eigenspace configurations:";
     "   t[1] plus:", [ Dimension (Etp[1] meet Etp[j]) : j in [2,3,4] ],
     "   ", [Dimension (Etp[1] meet Etm[j]) : j in [2,3,4] ];
     "   t[1] minus:", [ Dimension (Etm[1] meet Etp[j]) : j in [2,3,4] ],
     "   ", [Dimension (Etm[1] meet Etm[j]) : j in [2,3,4] ];
     "   t[2] plus:", [ Dimension (Etp[2] meet Etp[j]) : j in [3,4] ],
     "   ", [Dimension (Etp[2] meet Etm[j]) : j in [3,4] ];
     "   t[2] minus:", [ Dimension (Etm[2] meet Etp[j]) : j in [3,4] ],
     "   ", [Dimension (Etm[2] meet Etm[j]) : j in [3,4] ];
     "   t[3] plus:", [ Dimension (Etp[3] meet Etp[j]) : j in [4] ],
     "   ", [Dimension (Etp[3] meet Etm[j]) : j in [4] ];
     "   t[3] minus:", [ Dimension (Etm[3] meet Etp[j]) : j in [4] ],
     "   ", [Dimension (Etm[3] meet Etm[j]) : j in [4] ];
Z := Etp[1] meet Etp[3];
assert Dimension (Z) eq 2;
"type of Z:", IdentifyLineType (Q,Z);
"   ";
ZZ := Etm[1] meet Etm[3];
assert Dimension (ZZ) eq 1;
"ZZ nonsingular?", InnerProduct (ZZ.1 * Q, ZZ.1) ne 0;
"   ";
     
     // left and right module information
     L := sub < Om | [ t[i] : i in [1,2,3] ] >;
     ML := GModule (L);
     indL := IndecomposableSummands (ML);
     VL := [ sub<V|[V!(ML!(N.i)) : i in [1..Ngens(N)]]> : N in indL ];
     stabL := Stabilizer (Om, VL[1]);
     assert L subset stabL;
     "  [stabL : L] =", #stabL div #L;
     assert exists (UL){ X : X in VL | Dimension (X) eq 4 };
     assert exists (WL){ X : X in VL | Dimension (X) eq 1 };
     "dim(UL) =", Dimension (UL);
     "UL configurations:", [ [ Dimension (UL meet Etp[j]) , Dimension (UL meet Etm[j]) ] :
         j in [1..4] ];
     "dim(WL) =", Dimension (WL);
     "WL configurations:", [ [ Dimension (WL meet Etp[j]) , Dimension (WL meet Etm[j]) ] :
         j in [1..4] ];  
     "   "; 
     
     R := sub < Om | [ t[i] : i in [2,3,4] ] >;
     MR := GModule (R);
     indR := IndecomposableSummands (MR);
     VR := [ sub<V|[V!(MR!(N.i)) : i in [1..Ngens(N)]]> : N in indR ];
     stabR := Stabilizer (Om, VR[1]);
     assert R subset stabR;
     "  [stabR : R] =", #stabR div #R;
     assert exists (UR){ X : X in VR | Dimension (X) eq 3 };
     assert exists (WR){ X : X in VR | Dimension (X) eq 2 };
     "dim(UR) =", Dimension (UR);
     "UR configurations:", [ [ Dimension (UR meet Etp[j]) , Dimension (UR meet Etm[j]) ] :
         j in [1..4] ];
     "dim(WR) =", Dimension (WR);
     "WR configurations:", [ [ Dimension (WR meet Etp[j]) , Dimension (WR meet Etm[j]) ] :
         j in [1..4] ];    
     "     ";
     "---------";
end for;
*/




// BUILDING 3-POLYTOPE FOR SUBGROUP OF O+(4,q) FROM SCRATCH
/*
q := 13;
k := GF (q);
if q mod 4 eq 1 then type := "hyperbolic"; else type := "asingular"; end if;
G := GOPlus (4, q);
isit, Q := QuadraticForm (G); assert isit;
F := Q + Transpose (Q);
V := VectorSpace (k, 4);
repeat
  repeat
    U0 := sub < V | [ Random (V) , Random (V) ] >;
  until Dimension (U0) eq 2;
until IdentifyLineType (Q, U0) eq type;
W0 := PerpSpace (F, U0); assert (Dimension (W0) eq 2) and (Dimension (W0 meet U0) eq 0);
repeat
  repeat
    U2 := sub < V | Random (U0) , Random (W0) >;
  until Dimension (U2) eq 2;
until IdentifyLineType (Q, U2) eq type;
W2 := PerpSpace (F, U2); assert (Dimension (W2) eq 2) and (Dimension (W2 meet U2) eq 0);
sides := [ U0 , W0 , U2 , W2 ];
corners := [ U0 meet U2 , U0 meet W2 , W0 meet U2 , W0 meet W2 ];
assert forall { c : c in corners | Dimension (c) eq 1 };
i0 := InvolutionOdd (U0, W0);
i2 := InvolutionOdd (U2, W2);
assert (i0, i2) eq Identity (G);

hyps := [ U0 + U2 , U0 + W2 , W0 + U2 , W0 + W2 ];
pts := { sub < V | v > : v in V | (InnerProduct (v*Q, v) ne 0) and
           forall { H : H in hyps | not v in H } };
"points =", #pts, "  ( out of", (q^4 - 1) div (q - 1),")";
gpts := [ ]; 
polys := [ ];
for x1 in pts do
  H1 := PerpSpace (F, x1);
  assert forall { s : s in sides | Dimension (s meet H1) eq 1 };
  i1 := InvolutionOdd (x1, H1);
  X := sub < G | i0 , i1 , i2 >;
  if #G div #X eq 2 then
       Append (~gpts, x1);
       Append (~polys, X);
  end if;
end for;
"good points =", #gpts;
Set ([ SchlafliSymbol (X) : X in polys ]);
*/


/*
q := 11;
if q mod 4 eq 1 then type := "hyperbolic"; else type := "asingular"; end if;
SpH := SpHyperbolic (4, q);
assert forall { t : t in SpH_polys | t subset SpH };
PSpH, pi := ProjectiveGroup (SpH);
proj_polys := [ t @ pi : t in SpH_polys ];
proj_types := [ SchlafliSymbol (t) : t in proj_polys ];
// study 4-polytopes inside isomorphic group Omega(5,q)
Om := Omega (5, q);
isit, fOm, gOm := RecogniseSp4 (Om, q); assert isit;
isit, fSpH, gSpH := RecogniseSp4 (SpH, q); assert isit;
Om_polys := [ (t @ fSpH) @ gOm : t in SpH_polys ];
Om_types := [ SchlafliSymbol (t) : t in Om_polys ]; 
assert proj_types eq Om_types;
DT := Set (Om_types);
dpols := [ ];
for type in DT do
     assert exists (t){ u : u in Om_polys | SchlafliSymbol (u) eq type };
     Append (~dpols, t);
end for;
V := VectorSpace (GF (q), 5);
Q := ClassicalForms (Om)`quadraticForm;
F := ClassicalForms (Om)`bilinearForm;
for i in [1..#dpols] do
     t := dpols[i];
     L := sub < Om | [ t[i] : i in [1,2,3] ] >;
     M := GModule (L);
     indM := IndecomposableSummands (M);
     indV := [ sub<V|[V!(M!(N.i)) : i in [1..Ngens(N)]]> : N in indM ];
     st := Stabilizer (Om, indV[1]);
     assert L eq st; 
     assert exists (U){ X : X in indV | Dimension (X) eq 4 };
     assert exists (W){ X : X in indV | Dimension (X) eq 1 };
     LU := InduceGroup (L, U);
     Ep := [ Eigenspace (LU.j, 1) : j in [1,2,3] ];
     Em := [ Eigenspace (LU.j, -1) : j in [1,2,3] ];
     QU := RestrictQuadraticForm (Q, U);
     assert IdentifyLineType (QU, Ep[1]) eq type;
     assert IdentifyLineType (QU, Ep[3]) eq type;
     assert IdentifyLineType (QU, Em[1]) eq type;
     assert IdentifyLineType (QU, Em[3]) eq type;
     corners := [ Ep[1] meet Ep[3] , Ep[1] meet Em[3] , Em[1] meet Ep[3] , Em[1] meet Em[3] ];
     assert forall { c : c in corners | Dimension (c) eq 1 };
     assert Dimension (Ep[2]) eq 1;
"Ep[2] in corners?",     Ep[2] in corners;
end for;
*/

__is_orthogonal := function (X, Y)
return forall { i : i in [1..Ngens (X)] | forall { j : j in [1..Ngens (Y)] | 
   InnerProduct (X.i, Y.j) eq 0 } };
end function;

// V a quadratic space
PROFILE := function (V, T)
  val := 1;
  i0 := T[1];  i1 := T[2];  i2 := T[3];
  E0p := Eigenspace (i0, 1);  E0m := Eigenspace (i0, -1);
  E1p := Eigenspace (i1, 1);  E1m := Eigenspace (i1, -1);
  E2p := Eigenspace (i2, 1);  E2m := Eigenspace (i2, -1);
  cor := [ E0p meet E2p , E0p meet E2m , E0m meet E2p , E0m meet E2m ];
  hcor := [ E0p + E2p , E0p + E2m , E0m + E2p , E0m + E2m ];
  assert forall { x : x in cor | Dimension (x) eq 1 };
  assert forall { x : x in hcor | Dimension (x) eq 3 };
  cor := [ sub<V|V!(x.1)> : x in cor ];
  hcor := [ sub<V|[V!(U.i) : i in [1,2,3]]> : U in hcor ];
  x1 := sub < V | V!(E1p.1) >;
  H1 := sub < V | [ V!(E1m.i) : i in [1,2,3] ] >;
  if exists { y : y in cor | y subset H1 } then
      "a corner lies on H1"; val := 0;
  end if;
  if exists { U : U in hcor | x1 subset U } then
      "x1 lies on a hypercorner"; val := 0;
  end if;
  if val eq 0 then return val, _, _, _, _; end if;
  L := sub < Generic (Parent (i0)) | i0 , i1 >;
  R := sub < Generic (Parent (i0)) | i1 , i2 >;
  ML := GModule (L);
  MR := GModule (R);
  IND_ML := IndecomposableSummands (ML);
  IND_MR := IndecomposableSummands (MR);
  IND_VL := [ sub < V | [ V!(ML!(N.i)) : i in [1..Ngens(N)] ] > : N in IND_ML ];
  IND_VR := [ sub < V | [ V!(MR!(N.i)) : i in [1..Ngens(N)] ] > : N in IND_MR ];
  assert forall { l : l in Generators (L) | forall { U : U in IND_VL | U*l eq U } };
  assert forall { r : r in Generators (R) | forall { U : U in IND_VR | U*r eq U } };
  assert exists (UL){ X : X in IND_VL | Dimension (X) eq 2 };
  assert exists (UR){ X : X in IND_VR | Dimension (X) eq 2 }; 
  assert x1 eq UL meet UR;
return val, UL, UR, x1, H1;
end function;

// NEW ATTEMPT TO BUILD 3-POLYTOPE FROM SCRATCH FOR INDEX 2 SUBGROUP OF O*(4,q)
/*
p := 7;  e := 1;  q := p^e;  k := GF (q);   kt := [ a : a in k | a ne 0 ];
Q := Identity (MatrixAlgebra (k, 4));
V := QuadraticSpace (Q);
C := TransformForm (Q, "orthogonalplus");
G0 := GOPlus (4, k);
G := sub < Generic (G0) | [ C * G0.i * C^-1 : i in [1..Ngens (G0)] ] >;
C := CyclicGroup (2);
f := hom < G -> C | x :-> C.1^(SpinorNorm (x, Q)) >; 
H := Kernel (f);
assert #G div #H eq 2;
i0 := InvolutionOdd (sub<V|V.1,V.2>, sub<V|V.3,V.4>);
i2 := InvolutionOdd (sub<V|V.1,V.3>, sub<V|V.2,V.4>);
assert (i0 in H) and (i2 in H);
j1 := Generic (G)![1,0,0,0,0,-1,0,0,0,0,-1,0,0,0,0,-1];
assert j1 in H;
tt := Cputime ();
I1 := Conjugates (H, j1);
"computed all conjugates of j1 in time", Cputime (tt);
"initially, |I1| =", #I1;
I1 := [ x : x in I1 | (x, i0) ne Identity (H) and (x, i2) ne Identity (H) ];
"after basic pruning, |I1| =", #I1;
good := [ ];  bad := [ ];
for i1 in I1 do
  X := sub < H | i0 , i1 , i2 >;
  if #X eq #H then
      Append (~good, [i0, i1, i2]);
  else
      Append (~bad, [i0, i1, i2]);
  end if;
end for;
"|good| =", #good;
"|bad| =", #bad;
"  ";
"  ";
*/

/*
//good := [ t : t in good | SchlafliSymbol (t) in { [q-1,q-1] , [q-1,q+1] , [q+1,q-1] , [q+1,q+1] } ];
//bad := [ t : t in bad | SchlafliSymbol (t) in { [q-1,q-1] , [q-1,q+1] , [q+1,q-1] , [q+1,q+1] } ];

good := [ t : t in good | exists { a : a in SchlafliSymbol (t) | a mod p eq 0 } ];
bad := [ t : t in bad | exists { a : a in SchlafliSymbol (t) | a mod p eq 0 } ];

for i in [1..#bad] do
"  testing triple", i, "out of", #bad, "bad triples";
t := bad[i];
"  Schlafli type of t:", SchlafliSymbol (t);
J := sub < H | t >;
"  [ H : J ] =", #H div #J;
M := GModule (J);
"  J acts irreducibly?", IsIrreducible (M);
"  J is solvable?", IsSolvable (J);
//v, UL, UR, x1, H1 := PROFILE (V, t);
//if v eq 1 then
//"  UL and UR perpendicular?", __is_orthogonal (UL, UR);
//end if;
"--------";
end for;
"  ";
for i in [1..#good] do
"  testing triple", i, "out of", #good, "good triples";
t := good[i];
"  Schlafli type of t:", SchlafliSymbol (t);
J := sub < H | t >;
"  [ H : J ] =", #H div #J;
M := GModule (J);
"  J acts irreducibly?", IsIrreducible (M);
//v, UL, UR, x1, H1 := PROFILE (V, t);
//if v eq 1 then
//"  UL and UR perpendicular?", __is_orthogonal (UL, UR);
//end if;
"--------";
end for;
"  ";
"after restricting Schlafli type ...";
"|good| =", #good;
"|bad| =", #bad;
*/

/*
q := 11;
SpH := SpHyperbolic (4, q);
assert forall { t : t in SpH_polys | t subset SpH };
PSpH, pi := ProjectiveGroup (SpH);
proj_polys := [ t @ pi : t in SpH_polys ];
// study 4-polytopes inside isomorphic group Omega(5,q)
Om := Omega (5, q);
F := ClassicalForms (Om)`bilinearForm;
isit, fOm, gOm := RecogniseSp4 (Om, q); assert isit;
isit, fSpH, gSpH := RecogniseSp4 (SpH, q); assert isit;
Om_polys := [ (t @ fSpH) @ gOm : t in SpH_polys ];

for i in [1..#Om_polys] do
  t := Om_polys[i];
  "4-polytope", i, "( out of", #Om_polys,") has Schlafli symbol", SchlafliSymbol (t); 
  E0p := Eigenspace (t[1], 1);   E2p := Eigenspace (t[3], 1);   E1m := Eigenspace (t[2], -1);
  z := &meet ([E0p, E2p, E1m]);
  assert Dimension (z) eq 1;
  U := PerpSpace (F, z);   assert Dimension (U) eq 4;
  E0m := Eigenspace (t[1], -1);   E2m := Eigenspace (t[3], -1); 
  C := Matrix (
        Basis (E0p meet E2p meet U) cat
        Basis (E0p meet E2m) cat
        Basis (E0m meet E2p) cat
        Basis (E0m meet E2m) cat
        Basis (z)
              );
  t := [ C * t[i] * C^-1 : i in [1..4] ];
  G := sub < Generic (Om) | [ C * Om.i * C^-1 : i in [1..Ngens (Om)] ] >;
  isit, Q := QuadraticForm (G);  assert isit;
  "quadratic form:"; Q;
  V := QuadraticSpace (Q);
  U := sub < V | [ V.j : j in [1..4] ] >;
  x := V!(Eigenspace (t[2], 1).1);
  H := U meet sub < V | [ V!(Eigenspace (t[2], -1).j) : j in [1..4] ] >;
  L := sub < G | t[1] , t[2] , t[3] >;
  R := sub < G | t[2] , t[3] , t[4] >;
  "comp facs of L:"; CompositionFactors (L);
  "  ";
  "comp facs of R:"; CompositionFactors (R);
  "--------";
end for;
*/


MySpinorMap := function (G, F)
  C := CyclicGroup (2);
return hom < G -> C | x :-> C.1^(SpinorNorm (x, F)) >;
end function;

__line_pairs := function (U, W, F)
  t := IdentifyLineType (F, U); assert IdentifyLineType (F, W) eq t;
  Upts := { sub < U | u > : u in U | InnerProduct (u * F, u) ne 0 };
  Wpts := { sub < W | w > : w in W | InnerProduct (w * F, w) ne 0 };
  lp := [ ];
  for PU in Upts do
       for PW in Wpts do
            X := PU + PW;
            if IdentifyLineType (F, X) eq t then
                 Y := PerpSpace (F, X) meet (U + W);
                 if (Y meet U in Upts) and (Y meet W in Wpts) then
                      Append (~lp, [X, Y]);
                 end if;
            end if;
       end for;
  end for;
return [ pair : pair in Set (lp) ];
end function;


q := 7;  "q =", q;
k := GF (q);
V := VectorSpace (k, 5);
G := MyOmega (5, q);
F := Identity (MatrixAlgebra (k, 5));
rho := InvolutionOdd (sub<V|V.3,V.4,V.5>,sub<V|V.1,V.2>);  assert rho in G;
assert forall { i : i in [1..Ngens(G)] | G.i * F * Transpose (G.i) eq F };
z := V.5;  Z := sub < V | z >;
H := Stabilizer (G, Z);  assert rho in H;
U := sub < V | V.1 , V.2 , V.3 , V.4 >;  assert U eq PerpSpace (F, Z);
Xm := sub < V | V.1, V.2 >;
Xp := sub < V | V.3, V.4 >;
LINE_PAIRS := __line_pairs (Xm, Xp, F);
pts := [ sub < U | u > : u in U | u ne 0 ];
pts := [ P : P in pts | InnerProduct (P.1 * F, P.1) ne 0 ];
"there are", #pts, "nonsingular points";
gpts := [ P : P in pts | WittIndex (QuadraticSpace (RestrictBilinearForm (F, PerpSpace (F, P)))) eq 2 ];
"of these", #gpts, "are centres of suitable involutions in G";
gpts := [ P : P in gpts | (not P subset Xm) and (not P subset Xp) ];
"of these", #gpts, "do not lie on eigenspaces of rho";
ords := [ ];
trips := [ ];
good := [ ];
for i in [1..#gpts] do
     if i mod 50 eq 0 then "testing good point", i; end if; 
     P := gpts[i];
     tau := InvolutionOdd (P, PerpSpace (F, P));  assert tau in H;
XX := (P + Xm) meet (P + Xp);   assert (XX * tau eq XX) and (XX * rho eq XX);
     LPP := [ pair : pair in LINE_PAIRS | (not P subset pair[1]) and (not P subset pair[2]) ]; 
     b := 0;
     for pair in LPP do
          Yp := Z + pair[1];
          Ym := pair[2];
          sigma := InvolutionOdd (Yp, Ym);  assert sigma in H;  assert (sigma, rho) eq Identity (H);
YY := (P + Yp) meet (P + Ym);   assert (YY * tau eq YY) and (YY * sigma eq YY);
          J := sub < H | rho, tau, sigma >;
          if #J eq #H then
assert (XX + YY eq U) and (Dimension (XX meet PerpSpace (F, YY)) eq 0);
               Append (~trips, [rho, tau, sigma]);
          else
               b +:= 1;
          end if;
     end for;
     Append (~good, <Order (rho*tau), #LPP - b>);
end for;
"good:", Set (good);
"|trips| =", #trips;


