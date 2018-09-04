MyPointType := function (x, F)
return WittIndex (QuadraticSpace (RestrictBilinearForm (F, PerpSpace (F, x))));
end function;

GetLine := function (U, rho, tau)
  L := U meet Eigenspace (rho, 1);
  M := U meet Eigenspace (rho, -1);
  x := U meet Eigenspace (tau, 1);
  X := (L + x) meet (M + x);   assert Dimension (X) eq 2;
return X;
end function;

/*---- constructions ----*/

q := 13;
if (q mod 4 eq 1) then WI := 1; else WI := 0; end if;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
Q := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Q * Transpose (G.i) eq Q };
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Q * Transpose (O.i) eq Q };

// create r at random
repeat
    X := sub < V | Random (V) , Random (V) >;
until Dimension (X) eq 2 and MyWittIndex (Q, X) eq WI;
Y := PerpSpace (Q, X);
r := InvolutionOdd (Y, X);   assert r in O;

// create at random so that |r * t| = q+1
found := false;
while not found do
    a := sub < V | Random (V) >;
    if InnerProduct (a.1 * Q, a.1) ne 0 then
        H := PerpSpace (Q, a);
        if MyWittIndex (Q, H) eq 2 then
             t := InvolutionOdd (a, H);
             if Order (r * t) eq (q+1) then
                 found := true;
             end if;
        end if;
    end if;
end while;

D := sub < O | r , t >;

// check various geometric consitions
b := H meet X;   assert Dimension (b) eq 1;   assert (b.1 * r eq -b.1) and (b.1 * t eq -b.1);
L := H meet Y;   assert Dimension (L) eq 2;   "WI(L) =", MyWittIndex (Q, L);
M := PerpSpace (Q, L);   assert (Dimension (M) eq 3) and (Dimension (L meet M) eq 0);
assert M eq a + X;  
LD := PerpSpace (Q, b) meet M;   assert (Dimension (LD) eq 2) and (MyWittIndex (Q, LD) eq 0); 

DL := InduceGroup (D, L);
DM := InduceGroup (D, M); 

