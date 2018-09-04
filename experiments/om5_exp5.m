p := 11;  exp := 1;  q := p^exp;
if (q mod 4 eq 1) then type := "hyperbolic"; else type := "asingular"; end if;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
Q := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Q * Transpose (G.i) eq Q };
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Q * Transpose (O.i) eq Q };

// create r at random
repeat
    Fr := sub < V | Random (V) , Random (V) >;
until Dimension (Fr) eq 2 and IdentifyLineType (Q, Fr) eq type;
Er := PerpSpace (Q, Fr);
r := InvolutionOdd (Er, Fr);   assert r in O;


prod_order := (q-1);    // must be one or q+1, q-1, 2*p
if prod_order eq q-1 then
   int_order := 2*(q+1);
elif prod_order eq q+1 then
   int_order := 2*(q-1);
else assert prod_order eq 2*p; 
   int_order := 4*p;
end if;

// create at random so that |r * t| = q+1
found := false;
while not found do
    Et := sub < V | Random (V) >;
    if InnerProduct (Et.1 * Q, Et.1) ne 0 then
        Ft := PerpSpace (Q, Et);
        if MyWittIndex (Q, Ft) eq 2 then
             t := InvolutionOdd (Et, Ft);   assert t in O;
             if Order (r * t) eq prod_order then
                 found := true;
             end if;
        end if;
    end if;
end while;

assert Dimension (Er meet Et) eq 0;
assert Dimension (Fr meet Et) eq 0;
X := Er meet Ft;
assert Dimension (X) eq 2; "isometry type of X:", IdentifyLineType (Q, X);
Y := Fr meet Ft;
assert Dimension (Y) eq 1; assert InnerProduct (Y.1, Y.1) ne 0;
assert MyWittIndex (Q, PerpSpace (Q, Y)) eq 1;   // if prod_order is q +/- 1
U := PerpSpace (Q, Y) meet PerpSpace (Q, X);   
assert Dimension (U) eq 2; "isometry type of U:", IdentifyLineType (Q, U);



// so far the same as "om5_exp4.m" ... but now let's use r and t to define the key maximals
Cr := Centraliser (O, r);   
Ct := Centraliser (O, t);
D := Cr meet Ct;   assert #D eq int_order;
cl := ConjugacyClasses (D);
icl := [ c[3] : c in cl | c[1] eq 2 and 
             not forall { x : x in Generators (D) | (c[3], x) eq Identity (D) } ];
ZD := Center (D);   assert #ZD eq 2;   assert exists (z){ x : x in ZD | Order (x) eq 2 };
Ez := Eigenspace (z, 1);   Fz := Eigenspace (z, -1);
assert Ez eq (X + Y);
assert Fz eq PerpSpace (Q, X+Y);

 

