__MySet := function (L)
  D := [ ];
  for l in L do
    if not l in D and not Reverse (l) in D then
      Append (~D, l);
    end if;
  end for;
return D;
end function;

__GetLine := function (U, rho, tau)
  L := U meet Eigenspace (rho, 1);
  M := U meet Eigenspace (rho, -1);
  x := U meet Eigenspace (tau, 1);
  X := (L + x) meet (M + x);   assert Dimension (X) eq 2;
return X;
end function;



/* sanity check on involutions and their centralizers */
q := 19;
"q =", q;
k := GF (q); V := VectorSpace (k, 5);
G := MyGO (5, q);
F := Identity (MatrixAlgebra (k, 5));
assert forall { i : i in [1..Ngens(G)] | G.i * F * Transpose (G.i) eq F };

//type
if q mod 4 eq 1 then
  type := "hyperbolic";
  m := q-1;
else
  type := "asingular";
  m := q+1;
end if;
"line type =", type;
  
O := MyOmega (5, q);   

Erp := sub<V|V.3,V.4,V.5>;
Erm := sub<V|V.1,V.2>;
rho := InvolutionOdd (Erp, Erm);  assert rho in O;

z := V.5;  Z := sub < V | z >;  U := PerpSpace (F, Z);
assert U eq sub < V | V.1 , V.2 , V.3 , V.4 >; 
NS := { sub < U | u > : u in U | u ne 0 };
"# nonsingular points in U:", #NS;
NS := [ P : P in NS | WittIndex (QuadraticSpace (RestrictBilinearForm (F, PerpSpace (F, P)))) eq 2 ];
"# with correct perp space:", #NS;

time OZ := Stabilizer (O, Z);  assert rho in OZ;
time GZ := Stabilizer (G, Z); 
time COZ := Centralizer (OZ, rho);
time CGZ := Centralizer (GZ, rho);   
assert #CGZ eq 8 * m^2;  // 2 x D_2m x D_2m

E1 := Erp meet U;   E2 := Erm meet U;  assert ((Dimension (E1) eq 2) and (Dimension (E2) eq 2));

// transitivity ...
P1 := { sub < V | v > : v in E1 | InnerProduct (v, v) ne 0 };   assert #P1 eq m;
P2 := { sub < V | v > : v in E2 | InnerProduct (v, v) ne 0 };   assert #P2 eq m;
lines0 := { x + y : x in P1 , y in P2 };
lines, sizes := OrbitReps (CGZ, lines0); 
"orbit sizes:", sizes; 
glines := [ L : L in lines | IdentifyLineType (F, L) eq type ];   assert #glines eq 2;
pols := [ ];
for i in [1,2] do
"-----------";
     "  i =", i;
     Esm := glines[i];
     Esp := PerpSpace (F, Esm);  assert (U meet Esp) in Orbit (CGZ, Esm); 
     sigma := InvolutionOdd (Esp, Esm);  assert sigma in OZ;
     C := Centralizer (CGZ, sigma);   assert #C eq 32;
     F1 := Esp meet U;  F2 := Esm meet U;  assert ((Dimension (F1) eq 2) and (Dimension (F2) eq 2));
     COR := [ E1 meet F1 , E1 meet F2 , E2 meet F1 , E2 meet F2 ];
"  corner types:",
[ WittIndex (QuadraticSpace (RestrictBilinearForm (F, PerpSpace (F, P)))) : P in COR ];
     HYP := [ E1 + F1 , E1 + F2 , E2 + F1 , E2 + F2 ]; assert forall { X : X in HYP | Dimension (X) eq 3 };
"  hypercorner types:",
[ IdentifyLineType (F, PerpSpace (F, H)) : H in HYP ];
     bNS := { P : P in NS | exists { X : X in HYP | P subset X } };
     bREPS := OrbitReps (C, bNS);
     "  there", #bNS, "bad nonsingular points, yielding", #bREPS, "distinct C-classes";
     bad := true;
     for P in bREPS do
          tau := InvolutionOdd (P, PerpSpace (F, P));   assert tau in OZ;
          if OZ eq sub < OZ | rho, tau, sigma > then bad := false; end if;
     end for;
     "     ...all bad?", bad;
     "   ";
     gNS := { P : P in NS | not P in bNS };
     gREPS := OrbitReps (C, gNS);
     "  there are", #gNS, "good nonsingular points, yielding", #gREPS, "distinct C-classes";
     gREPS := [ P : P in gREPS | (Order (rho * InvolutionOdd (P, PerpSpace (F, P))) in [q+1,q-1])
              and (Order (sigma * InvolutionOdd (P, PerpSpace (F, P))) in [q+1,q-1]) ];
     "  after restricting product orders, there are", #gREPS, "C-classes";
     gpts := [ ];
     spols := [ ];
     for P in gREPS do
assert WittIndex (QuadraticSpace (RestrictBilinearForm (F, PerpSpace (F, P)))) eq 2;
          tau := InvolutionOdd (P, PerpSpace (F, P));   assert tau in OZ;
t := [rho, tau, sigma];
          X := __GetLine (U, rho, tau);
          Y := __GetLine (U, sigma, tau); 
          if Dimension (X meet PerpSpace (F, Y)) eq 0 then
               Append (~gpts, P);
               Append (~spols, [ rho , tau , sigma ]);
          end if;
J := sub<OZ|t>;   JU := InduceGroup (J, U);
if #J lt #OZ then
subs := Submodules (GModule (JU));
"subs =", [ Dimension (A) : A in subs ];
/*
assert exists (W){ A : A in subs | Dimension (A) eq 1 };
W := sub<U|U!(GModule(JU)!(W.1))>;
"W.1 =", W.1;
"(W.1, W.1) =", InnerProduct (W.1 * F, W.1);
*/
end if;
     end for;
     "  of these,", #spols, "act on suitable line pairs";
     pols cat:= spols;
end for;

[ #OZ div #sub<OZ|t> : t in pols ];





