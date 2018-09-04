q := 13;
if (q mod 4 eq 1) then WI := 1; else WI := 0; end if;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
Q := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Q * Transpose (G.i) eq Q };
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Q * Transpose (O.i) eq Q };

Er := sub < V | V.3 , V.4 , V.5 >;   Fr := sub < V | V.1 , V.2 >;
r := InvolutionOdd (Er, Fr);   assert r in O;
repeat
     v := Random (V);
     Ft := sub < V | v , V.2 , V.3 , V.4 >;
until MyWittIndex (Q, Ft) eq 2;
Et := PerpSpace (Q, Ft);
t := InvolutionOdd (Et, Ft);   assert t in O;


Ct := Centralizer (O, t);
Cr := Centralizer (O, r);
D := Ct meet Cr;
"|D| =", #D;
ZD := Center (D);
"|ZD| =", #ZD;



