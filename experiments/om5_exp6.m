q := 9;
if (q mod 4 eq 1) then WI := 1; else WI := 0; end if;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
Q := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Q * Transpose (G.i) eq Q };
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Q * Transpose (O.i) eq Q };

P := sub < V | V.3 , V.4 , V.5 >;   l := sub < V | V.1 , V.2 >;
r := InvolutionOdd (P, l);   assert r in O;
Cr := Centralizer (O, r);  

/*
found := false;
count := 0;
LIMIT := 100;
while (count lt LIMIT) and (not found) do
  count +:= 1;
  repeat
     repeat
        v := V![ Random ([0..q-1]) : i in [1..5] ];
     until (InnerProduct (v * Q, v) ne 0) and (not v in Er) and (not v in Fr);
     Et := sub <V|v>;
     Ft := PerpSpace (Q, Et);
  until MyWittIndex (Q, Ft) eq 2;
  t := InvolutionOdd (Et, Ft);   assert t in O;
  Ct := Centralizer (O, t);   
  D := Ct meet Cr;
  isit, i, j := IsDihedral (D);
  if isit then 
      found := true;    
  end if;
end while;

if found then
   "found a suitable pair of involutions after", count, "tries";
   "i * j has order", Order (i*j);
   "v =", v;
else
   "failed to find a suitable pair of involutions after", LIMIT, "tries";
end if;
*/


// exhaustive

pts := { sub <V|v> : v in V | (not v in P) and (not v in l) and 
           (InnerProduct (v*Q,v) ne 0) and (MyWittIndex (Q, PerpSpace (Q, sub<V|v>)) eq 2) };
"trying", #pts, "points...";

good := [];   bad := [];
count := 0;
for x in pts do
  H := PerpSpace (Q, x);
  t := InvolutionOdd (x, H);   assert t in O;
  D0 := sub < O | r , t >;
  m := H meet P;   assert Dimension (m) eq 2; 
  type_m := IdentifyLineType (Q, m);
if not type_m eq "singular" then  
  y := H meet l;   assert Dimension (y) eq 1;
  ysing := InnerProduct (y.1 * Q, y.1) eq 0;
  Ct := Centralizer (O, t);   
  D := Ct meet Cr;
  isit, i, j := IsDihedral (D);
//  "   D0 induces on X a group of order", #InduceGroup (D0, X);
//  "   D induces on X a group of order", #InduceGroup (D, X);
  R := PerpSpace (Q, m);
  if not ysing then
//    "   D0 induces on Xperp a group of order", #InduceGroup (D0, Xperp);
//    "   D induces on Xperp a group of order", #InduceGroup (D, Xperp);
//  else
    n := PerpSpace (Q, y) meet R;   assert Dimension (n) eq 2;
//    "   line m is", type_m;
//    "   line n is", IdentifyLineType (Q, n);
type_n := IdentifyLineType (Q, n);
//    "   D0 induces on Y a group of order", #InduceGroup (D0, Y);
//    "   D induces on Y a group of order", #InduceGroup (D, Y);
//    "   D0 induces on Z a group of order", #InduceGroup (D0, Z);
//    "   D induces on Z a group of order", #InduceGroup (D, Z);
  end if;
//  "   |D| =", #D;
//  "   D is dihedral?", isit;
  if not isit then 
     Append (~bad, [type_m, type_n]); 
  else 
     Append (~good, [type_m, type_n]); 
         if type_m eq "hyperbolic" and type_n eq "hyperbolic" then
            [ < InduceTransformation (x, m) , InduceTransformation (x, n) > : x in D ];
         end if; 
  end if;
end if;
//  "-----------";
end for;
"good", Set (good);
"bad", Set (bad);




/*
q := 13;
k := GF (q);    mu := PrimitiveElement (k);
I1 := Identity (MatrixAlgebra (k, 1));
I2 := Identity (MatrixAlgebra (k, 2));
V1 := QuadraticSpace (Matrix(k,1,1,[1]));
U2 := QuadraticSpace (Matrix(k,2,2,[1,0,0,1])); 
W2 := QuadraticSpace (Matrix(k,2,2,[1,0,0,mu])); 
"q =", q;
"Sp(-1) in ...";
"   V1 is", SpinorNorm (V1, -I1);
"   U2 of Witt index", WittIndex (U2), "  is", SpinorNorm (U2, -I2);
"   W2 of Witt index", WittIndex (W2), "  is", SpinorNorm (W2, -I2);
*/