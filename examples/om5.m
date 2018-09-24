q := 11;   "q =", q;
k := GF (q); 
LIMIT := 100;
I5 := Identity (MatrixAlgebra (k, 5));

if not INIT then
  
  // set up groups, and vector spaces
  V := VectorSpace (k, 5);
  G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * Transpose (G.i) eq I5};
  assert IsometryGroup (V) eq G;
  O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * Transpose (O.i) eq I5 };
  // fix rho
  P := sub < V | V.3 , V.4 , V.5 >;   
  l := sub < V | V.1 , V.2 >;
  rho := InvolutionOdd (P, l);   assert rho in O;
  R := Centralizer (O, rho); 
  /* 
    NOTE: <R> is the "right" parabolic subgroup of our 4-polytope:
      as the centralizer of involution <rho> it is maximal in O,
      and we shall construct it as a polyhedron. There is a single
      conjugacy class of involutions possessing the geometric properties
      of <rho> so it's fine to fix it once and for all.
  */
  
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
  
  INIT := true;

end if;

/* 
  specify the desired geometric decomposition of our "middle"
  subgroup––the intersection of the "left" and "right" maximals.
  NOTE: the "type pairs" to avoid are as follows:
   (HYPERBOLIC, HYPERBOLIC) if q = 1 (mod 4)
   (ASINGULAR,  ASINGULAR)  if q = 3 (mod 4)
*/
MTYPE := "hyperbolic";
NTYPE := "hyperbolic";
"(MTYPE, NTYPE) =", [ MTYPE , NTYPE ];


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
//  x := sub < V | x0 * g >;
x := sub<V|V![1,5,1,0,3]>;
//  H := sub < V | H0 * g >;
H := PerpSpace (I5, x);
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
L := Centralizer (O, tau);
  /* 
    NOTE: <L> is the "left" parabolic subgroup of our 4-polytope:
      as the centralizer of involution <tau> it is maximal in O,
      and we shall again construct it as a polyhedron. 
  */
D := sub < O | rho , tau >;
M := L meet R;
isit, a, b := IsDihedral (M);
  /*
    NOTE: <M> is the "middle" subgroup of our 4-polytope.
      It is constructed as the intersection of <L> and <M>
      to be dihedral, generated by elements r and t that
      will form the middle pair of our eventual generating
      4-tuple; hence we're guaranteed to satisfy the key
      intersection property.
  */
assert isit;

// is M maximal in L and/or R? Probably not ...
//"M is maximal in L?", IsMaximal (L, M);
//"M is maximal in R?", IsMaximal (R, M);

// figure out which involution is which
EIG_a := [ Dimension (Eigenspace (a, 1)) , Dimension (Eigenspace (a, -1)) ];
if EIG_a eq [1,4] then
  t := a;
  r := b;
else assert EIG_a eq [3,2];
  t := b;
  r := a;
end if;
assert [ Dimension (Eigenspace (t,1)) , Dimension (Eigenspace (t,-1)) ] eq [1,4];
assert [ Dimension (Eigenspace (r,1)) , Dimension (Eigenspace (r,-1)) ] eq [3,2];

// now begin the search for the remaining generating involutions ...
CLr := Centraliser (L, r);
cl := ConjugacyClasses (CLr);
  DEG := sub < O | tau , r >;
icl := [ c[3] : c in cl | (c[1] eq 2) and (not c[3] in DEG) ];
"there are", #icl, "involution classes in C_L(r)...";
Ireps := [ i : i in icl | [ Dimension (Eigenspace (i, 1)) , Dimension (Eigenspace (i, -1)) ] eq [3,2] ];
"...of which", #Ireps, "are of the correct type";
I := &join [ Conjugates (CLr, i) : i in Ireps ];
"...giving rise to", #I, "involutions to check";
A := CLr meet R;
"...order of acting group is", #A;
J := RefineClass (A, [ i : i in I ]);
"...reducing the number to", #J;
J := [ j : j in J | sub<L|M,j> eq L ];
"...and", #J, "of these generate L";


"testing each one of them...";
"-----------------";
count := 0;
TUPS := [ ];
for rL in J do
  count +:= 1;
  "   involution", count;
  CRtrL := Centraliser (R, sub<O|t,rL>);
  cl := ConjugacyClasses (CRtrL);
    DEG := sub < O | rho , t , rL >;
  icl := [ c[3] : c in cl | (c[1] eq 2) and (not c[3] in DEG) ];
  "   there are", #icl, "involution classes in C_L(r)...";
  Ireps := [ i : i in icl | [ Dimension (Eigenspace (i, 1)) , Dimension (Eigenspace (i, -1)) ] eq [3,2] ];
  "   ...of which", #Ireps, "are of the correct type";
  I := &join [ Conjugates (CRtrL, i) : i in Ireps ];
  "   ...giving rise to", #I, "involutions to check";
  A := CRtrL meet L;
  "   ...order of acting group is", #A;
  J := RefineClass (A, [ i : i in I ]);
  "   ...reducing the number to", #J;
  TUPS cat:= [ [rL, t, r, rR] : rR in J ];
  "   =============";
end for;
"total number of candidate tuples:", #TUPS;

__get_info := function (TUP)
  k := BaseRing (Parent (TUP[1]));
  G := MyGO (5, #k);
  O := MyOmega (5, #k);
  V := VectorSpace (k, 5);
  P0 := sub < V | V.3 , V.4 , V.5 >;   
  l0 := sub < V | V.1 , V.2 >;
  rho0 := InvolutionOdd (P0, l0);   assert rho0 in O;
  Q := Identity (MatrixAlgebra (k, 5));
  assert forall { g : g in TUP | g in O };
  
  R := sub < O | [ TUP[i] : i in [2,3,4] ] >;
  MR := GModule (R);
  IMR := IndecomposableSummands (MR);
  assert [2,3] eq [ Dimension (N) : N in IMR ];
  IVR := [ sub < V | [ V!(MR!(N.j)) : j in [1..Ngens (N)] ] > : N in IMR ];
  assert exists (l){ U : U in IVR | Dimension (U) eq 2 };
  assert MyWittIndex (Q, l) eq (3-(q mod 4)) div 2;
  assert exists (P){ U : U in IVR | Dimension (U) eq 3 };
  rho := InvolutionOdd (P, l);   assert rho in O;
  Crho := Centraliser (O, rho);
  assert R eq Crho;
  isit, c := IsConjugate (O, rho, rho0);
  assert isit;
  l * c;
  P * c;
  
  L := sub < O | [ TUP[i] : i in [1,2,3] ] >;
  ML := GModule (L);
  IML := IndecomposableSummands (ML);
  assert [1,4] eq [ Dimension (N) : N in IML ];
  IVL := [ sub < V | [ V!(ML!(N.j)) : j in [1..Ngens (N)] ] > : N in IML ];
  assert exists (x){ U : U in IVL | Dimension (U) eq 1 };
  assert InnerProduct (x.1, x.1) ne 0;
  assert exists (H){ U : U in IVL | Dimension (U) eq 4 };
  assert MyWittIndex (Q, H) eq 2;
  tau := InvolutionOdd (x, H);   assert tau in O;
  Ctau := Centraliser (O, tau);
  assert L eq Ctau;
  
return x * c;
end function;



  