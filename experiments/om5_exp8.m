q := 11;   "q =", q;
k := GF (q); 
LIMIT := 100;
I5 := Identity (MatrixAlgebra (k, 5));

/*
// set up groups, and vector spaces, etc––copy and paste to avoid seed issues
V := VectorSpace (k, 5);
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Transpose (G.i) eq I5};
assert IsometryGroup (V) eq G;
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Transpose (O.i) eq I5 };

// fix rho
P := sub < V | V.3 , V.4 , V.5 >;   
l := sub < V | V.1 , V.2 >;
rho := InvolutionOdd (P, l);   assert rho in O;
Crho := Centralizer (O, rho); 
*/


/*
 TYPES TO AVOID:
   (HYPERBOLIC, HYPERBOLIC) if q = 1 (mod 4)
   (ASINGULAR,  ASINGULAR)  if q = 3 (mod 4)
*/
MTYPE := "hyperbolic";
NTYPE := "hyperbolic";
"(MTYPE, NTYPE) =", [ MTYPE , NTYPE ];

// find a suitable x0 to translate
found := false;
i := 0;
while (not found) and (i lt LIMIT) do
  i +:= 1;
  v0 := Random (V);
  x0 := sub< V | v0 >;
  H0 := sub < V | PerpSpace (I5, x0) >;
  if InnerProduct (v0, v0) ne 0 then
    if MyWittIndex (I5, H0) eq 2 then
      found := true;
    end if;
  end if;
end while;

"  ";
if found then
  "found a suitable x0 after", i, "tries";
else
  "failed to find a suitable x0 after", LIMIT, "tries";
end if;

// now translate x under random elements of G to find desired geometric configuration 
found := false;
i := 0;
while (not found) and (i lt LIMIT) do
  i +:= 1;
  g := Random (G);
  x := sub < V | x0 * g >;
  H := sub < V | H0 * g >;
  if (not x subset P) and (not x subset l) then
    m := H meet P;   assert Dimension (m) eq 2;
    y := H meet l;   assert Dimension (y) eq 1;
    Q := sub < V | PerpSpace (I5, m) >;
    n := sub < V | PerpSpace (I5, y) > meet Q;
    if Rank (RestrictQuadraticForm (I5, m)) eq 2 and Rank (RestrictQuadraticForm (I5, n)) eq 2 then
      if IdentifyLineType (I5, m) eq MTYPE and IdentifyLineType (I5, n) eq NTYPE then
        found := true;
      end if;
    end if;
  end if;
end while;

if found then
  "found suitable x after", i, "tries";
else
  "failed to find suitable x after", LIMIT, "tries";
end if;
"  ";

c := Matrix (Basis (m) cat Basis (y) cat Basis (n));

tau := InvolutionOdd (x, H);   assert tau in O;
Ctau := Centralizer (O, tau);
D := sub < O | rho , tau >;
C := Crho meet Ctau;
"|D| =", #D;

// compute induced group orders
Dn := InduceGroup (D, n);
"D induces on n a group of order", #Dn;
"  ";

Cm := InduceGroup (C, m);
"|C| =", #C;
"C induces on m a group of order", #Cm;


CC := sub < Generic (C) | [ c * C.i * c^-1 : i in [1..Ngens (C)] ] >;
DD := sub < Generic (D) | [ c * D.i * c^-1 : i in [1..Ngens (D)] ] >;
isit, i, j := IsDihedral (C);
"C is dihedral?", isit;
"  ";
"  ";





  