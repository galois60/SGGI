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

q := 17;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
F := Identity (MatrixAlgebra (k, 5));
G := MyGO (5, q);  assert forall { i : i in [1..Ngens(G)] | G.i * F * Transpose (G.i) eq F };
O := MyOmega (5, q);  assert forall { i : i in [1..Ngens(O)] | O.i * F * Transpose (O.i) eq F };

H := Stabilizer (O, sub<V|V.5>);

// first, a polyhedron for the stabilizer in O of a nonsingular point
if q mod 4 eq 1 then
  type := "hyperbolic";
  m := q-1;
else
  type := "asingular";
  m := q+1;
end if;
"line type =", type;
     
A := sub<V|V.3,V.4,V.5>;
B := sub<V|V.1,V.2>;
rho := InvolutionOdd (A, B);  
z := sub<V|V.5>;  assert MyPointType (z, F) eq 2;
U := PerpSpace (F, z);
Erp := A meet U;   Erm := B meet U;  assert ((Dimension (Erp) eq 2) and (Dimension (Erm) eq 2));
pPTS := { sub < Erp | u > : u in Erp | InnerProduct (u * F, u) ne 0 };   assert #pPTS eq m;
mPTS := { sub < Erm | u > : u in Erm | InnerProduct (u * F, u) ne 0 };   assert #mPTS eq m;
assert exists (xp){ P : P in pPTS | MyPointType (P, F) eq 1 };
assert exists (yp){ P : P in pPTS | MyPointType (P, F) eq 2 };
assert exists (xm){ P : P in mPTS | (MyPointType (P, F) eq 1) and 
                  (IdentifyLineType (F, P + xp) eq type) };
assert exists (ym){ P : P in mPTS | (MyPointType (P, F) eq 2) and 
                  (IdentifyLineType (F, P + xm) eq type) };
B1 := xp + xm;   A1 := PerpSpace (F, B1);
B2 := yp + ym;   A2 := PerpSpace (F, B2);
sigma1 := InvolutionOdd (A1, B1);   assert (rho, sigma1) eq Identity (O);
sigma2 := InvolutionOdd (A2, B2);   assert (rho, sigma2) eq Identity (O);
Es1p := A1 meet U;   Es1m := B1 meet U;
Es2p := A2 meet U;   Es2m := B2 meet U;


// NOW BUILD ALL <tau> THAT WORK FOR ONE OF THESE (<rho>,<sigma>) PAIRS ...

PTS0 := { sub < U | u > : u in U | InnerProduct (u*F, u) ne 0 }; 
"|PTS0| =", #PTS0;
PTS1 := { P : P in PTS0 | MyPointType (P, F) eq 2 };
"|PTS1| =", #PTS1;
"==============";

// <sigma1> first
"   ";
"<sigma1>:";
PTS_s1a := { P : P in PTS1 | 
    forall { W : W in [ Erp + Es1p , Erp + Es1m , Erm + Es1p , Erm + Es1m ] | not P subset W } };
"|PTS_s1a| =", #PTS_s1a;
PTS_s1b := { P : P in PTS_s1a | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) in [q+1, q-1] and 
                        Order (sigma1 * InvolutionOdd (P, PerpSpace (F, P))) in [q+1, q-1] };
"|PTS_s1b| =", #PTS_s1b;
PTS_s1c := { P : P in PTS_s1b | 
   Dimension (PerpSpace (F, GetLine (U, rho, InvolutionOdd (P, PerpSpace (F, P)))) meet
               GetLine (U, sigma1, InvolutionOdd (P, PerpSpace (F, P)))) eq 0 };
"|PTS_s1c| =", #PTS_s1c;
if #PTS_s1c eq 0 then
"   THERE ARE NO SUITABLE <tau> FOR <sigma1>";
end if;
pols1 := [ ];
if exists (P1){P : P in PTS_s1c | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) eq q+1 and
                        Order (sigma1 * InvolutionOdd (P, PerpSpace (F, P))) eq q-1 } then
  Append (~pols1, [rho, InvolutionOdd (P1, PerpSpace (F, P1)), sigma1]);
  Append (~pols1, [sigma1, InvolutionOdd (P1, PerpSpace (F, P1)), rho]);
else
  "<sigma1> admits no polyhedron of type [q+1, q-1]";
end if;
if exists (P2){P : P in PTS_s1c | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) eq q-1 and
                        Order (sigma1 * InvolutionOdd (P, PerpSpace (F, P))) eq q-1 } then
Append (~pols1, [rho, InvolutionOdd (P2, PerpSpace (F, P2)), sigma1]);
else
  "<sigma1> admits no polyhedron of type [q-1, q-1]";
end if;
if exists (P3){P : P in PTS_s1c | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) eq q+1 and
                        Order (sigma1 * InvolutionOdd (P, PerpSpace (F, P))) eq q+1 } then
  Append (~pols1, [rho, InvolutionOdd (P3, PerpSpace (F, P3)), sigma1]);
else
  "<sigma1> admits no polyhedron of type [q+1, q+1]";
end if;
"polyhedron types for <sigma1>:", [ SchlafliSymbol (t) : t in pols1 ];
"indices in H:", [ #H div #sub<H|t> : t in pols1 ];
"------------";


// now <sigma2> 
"   ";
"<sigma2>:";
PTS_s2a := { P : P in PTS1 | 
    forall { W : W in [ Erp + Es2p , Erp + Es2m , Erm + Es2p , Erm + Es2m ] | not P subset W } };
"|PTS_s1a| =", #PTS_s1a;
PTS_s2b := { P : P in PTS_s2a | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) in [q-1,q+1] and 
                        Order (sigma2 * InvolutionOdd (P, PerpSpace (F, P))) in [q+1, q-1] };
"|PTS_s2b| =", #PTS_s2b;
PTS_s2c := { P : P in PTS_s2b | 
   Dimension (PerpSpace (F, GetLine (U, rho, InvolutionOdd (P, PerpSpace (F, P)))) meet
               GetLine (U, sigma2, InvolutionOdd (P, PerpSpace (F, P)))) eq 0 };
"|PTS_s2c| =", #PTS_s2c;
if #PTS_s2c eq 0 then
"   THERE ARE NO SUITABLE <tau> FOR <sigma1>";
end if;
pols2 := [ ];
if exists (P1){P : P in PTS_s2c | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) eq q+1 and 
                         Order (sigma2 * InvolutionOdd (P, PerpSpace (F, P))) eq q-1 } then
  Append (~pols2, [rho, InvolutionOdd (P1, PerpSpace (F, P1)), sigma2]);
  Append (~pols2, [sigma2, InvolutionOdd (P1, PerpSpace (F, P1)), rho]);
else
  "<sigma2> admits no polyhedron of type [q+1, q-1]";
end if;
if exists (P2){P : P in PTS_s2c | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) eq q-1 and
                         Order (sigma2 * InvolutionOdd (P, PerpSpace (F, P))) eq q-1 } then
  Append (~pols2, [rho, InvolutionOdd (P2, PerpSpace (F, P2)), sigma2]);
else
  "<sigma2> admits no polyhedron of type [q-1, q-1]";
end if;
if exists (P3){P : P in PTS_s2c | Order (rho * InvolutionOdd (P, PerpSpace (F, P))) eq q+1 and
                         Order (sigma2 * InvolutionOdd (P, PerpSpace (F, P))) eq q+1 } then
  Append (~pols2, [rho, InvolutionOdd (P3, PerpSpace (F, P3)), sigma2]);
else
  "<sigma2> admits no polyhedron of type [q+1, q+1]";
end if;
"polyhedron types for <sigma1>:", [ SchlafliSymbol (t) : t in pols2 ];
"indices in H:", [ #H div #sub<H|t> : t in pols2 ];
"==========";

// now try to extend each of these "representative" polyhedra to a 4-polytope of Omega(5,q)
"     ";
"TRANCH 1: trying to extend", #pols1, "polyhedra to 4-polytopes of O";
bad1 := [ ];
npols1 := [ ];
for i in [1..#pols1] do
  "   i =", i;
  t := pols1[i];
  D := sub < O | t[1] , t[2] >;
  CD := Centralizer (O, D);
  I0 := Involutions (CD);
  I := [ j : j in I0 | not j in H ];
  "    there are", #I0, "involutions commuting with D, of which", #I, "lie outside H";
  for j in [1..#I] do
  "    testing involution", j, "...";
       rho := I[j];
       tt := Append (t, rho);
       assert IsStringGroup (tt);
       if HasIP (tt) then
       "    ...it is a string C-group";
            Append (~npols1, tt);
       else
       "    ...it does not satisfy the intersection property";
            Append (~bad1, tt);
       end if;       
  end for;
  "----------";
end for;

"     ";
"================";
"TRANCH 2: trying to extend", #pols2, "polyhedra to 4-polytopes of O";
bad2 := [ ];
npols2 := [ ];
for i in [1..#pols2] do
  "    i =", i;
  t := pols2[i];
  D := sub < O | t[1] , t[2] >;
  CD := Centralizer (O, D);
  I0 := Involutions (CD);
  I := [ j : j in I0 | not j in H ];
  "    there are", #I0, "involutions commuting with D, of which", #I, "lie outside H";
  for j in [1..#I] do
  "    testing involution", j, "...";
       rho := I[j];
       tt := Append (t, rho);
       assert IsStringGroup (tt);
       if HasIP (tt) then
       "    ...it is a string C-group";
            Append (~npols2, tt);
       else
       "    ...it does not satisfy the intersection property";
            Append (~bad2, tt);
       end if;  
  "----------";     
  end for;
end for;

"indices in Omega(5,q) for type 1 polys:", [ #O div #sub<O|t> : t in npols1 ];
"   ";
"indices in Omega(5,q) for type 2 polys:", [ #O div #sub<O|t> : t in npols2 ];
"   ";
"Schlafli symbols for type 1 polys:", [ SchlafliSymbol (t) : t in npols1 ];
"  ";
"Schlafli symbols for type 2 polys:", [ SchlafliSymbol (t) : t in npols2 ];









