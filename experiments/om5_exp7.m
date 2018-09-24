// want to check that the left and right parabolics are, 
// in fact, involution centralizers.

q := 19;  load "~/MagmaPackages/SGGI/data/PSp4/poly19.m";
FULL := false;

G := MyOmega (5, q);   Q := Identity (MatrixAlgebra (GF (q), 5));
isit, f, g := RecogniseSp4 (G, q);   assert isit;
H := sub < GL (4, q) | SpH_polys[1] >;
isit, a, b := RecogniseSp4 (H, q);   assert isit;

polys := [ ];
for t in SpH_polys do
    tt := [ (t[i] @ a) @ g : i in [1..#t] ];
    Append (~polys, tt);
end for;

S := Set ([ SchlafliSymbol (t) : t in polys ]);
rpolys := [ ];
for s in S do
   assert exists (t){u : u in polys | SchlafliSymbol (u) eq s};
   Append (~rpolys, t);
end for;

V := VectorSpace (GF (q), 5);

"checking", #rpolys, "polytopes for q =", q, "...";
IT2 := [ ];  IT3 := [ ];
INTS := [ ];
for i in [1..#rpolys] do
  "   ";
  "   polytope", i;
  tup := rpolys[i];
  "   Schlafli symbol", SchlafliSymbol (tup);
  L := sub < G | [ tup[a] : a in [1,2,3] ] >;
  R := sub < G | [ tup[a] : a in [2,3,4] ] >;
  if FULL then
     "   R is maximal?", IsMaximal (G, R); 
     "   L is maximal?", IsMaximal (G, L);
  end if;
  
  // construct L as an involution centraliser
  ML := GModule (L);
  IML := IndecomposableSummands (ML);
  assert [1,4] eq [ Dimension (N) : N in IML ];
  IVL := [ sub < V | [ V!(ML!(N.j)) : j in [1..Ngens (N)] ] > : N in IML ];
  assert exists (Ft){ U : U in IVL | Dimension (U) eq 4 };
  assert MyWittIndex (Q, Ft) eq 2;
  assert exists (Et){ U : U in IVL | Dimension (U) eq 1 };
  assert InnerProduct (Et.1 * Q, Et.1) ne 0;
  t := InvolutionOdd (Et, Ft);   assert t in G;
  Ct := Centraliser (G, t);
  assert L eq Ct;
  
  // construct R as an involution centraliser
  MR := GModule (R);
  IMR := IndecomposableSummands (MR);
  assert [2,3] eq [ Dimension (N) : N in IMR ];
  IVR := [ sub < V | [ V!(MR!(N.j)) : j in [1..Ngens (N)] ] > : N in IMR ];
  assert exists (Fr){ U : U in IVR | Dimension (U) eq 2 };
  assert MyWittIndex (Q, Fr) eq (3-(q mod 4)) div 2;
  assert exists (Er){ U : U in IVR | Dimension (U) eq 3 };
  r := InvolutionOdd (Er, Fr);   assert r in G;
  Cr := Centraliser (G, r);
  assert R eq Cr;
  
  D0 := sub < G | r , t >;
  D := L meet R;
  assert D eq sub < G | tup[2] , tup[3] >;
  isit, x, y := IsDihedral (D);
  assert isit;
  MD := GModule (D);
  IMD := IndecomposableSummands (MD);
  IVD := [ sub < V | [ V!(MD!(N.j)) : j in [1..Ngens (N)] ] > : N in IMD ];
  "   indecomposable summands of D have dimensions", [ Dimension (U) : U in IVD ];
  ind := [ InduceGroup (D, U) : U in IVD ];
  "   induced group orders:", [ #X : X in ind ];
  Append (~INTS, D);
  Append (~IT2, [ InduceTransformation (tup[2], U) : U in IVD | Dimension (U) eq 1 ]);
  Append (~IT3, [ InduceTransformation (tup[3], U) : U in IVD | Dimension (U) eq 1 ]);
  
  CD := Centraliser (G, D);   
  assert D0 subset CD;
  "   |D| =", #D, "   |D0| =", #D0, "   [CD : D0] =", #CD div #D0;
  
end for;