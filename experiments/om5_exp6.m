q := 7;
if (q mod 4 eq 1) then WI := 1; else WI := 0; end if;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
Q := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Q * Transpose (G.i) eq Q };
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Q * Transpose (O.i) eq Q };

Er := sub < V | V.3 , V.4 , V.5 >;   Fr := sub < V | V.1 , V.2 >;
r := InvolutionOdd (Er, Fr);   assert r in O;
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
pts := { sub <V|v> : v in V | (not v in Er) and (not v in Fr) and 
           (InnerProduct (v*Q,v) ne 0) and (MyWittIndex (Q, PerpSpace (Q, sub<V|v>)) eq 2) };
"trying", #pts, "points...";

good := [];   bad := [];
for Et in pts do
  Ft := PerpSpace (Q, Et);
  t := InvolutionOdd (Et, Ft);   assert t in O;
  Ct := Centralizer (O, t);   
  D := Ct meet Cr;
  isit, i, j := IsDihedral (D);
  if isit then Append (~good, t); else Append (~bad, t); end if;
end for;
"...", #good, "were good";