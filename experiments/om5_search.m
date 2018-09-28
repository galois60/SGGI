__identify := function (Q, U)
  assert Dimension (U) le 3;
  if Dimension (U) eq 0 then
    return "triv";
  elif Dimension (U) eq 1 then
    if InnerProduct (U.1 * Q, U.1) eq 0 then
      return "sing";
    else
      if MyWittIndex (Q, PerpSpace (Q, U)) eq 1 then
        return "minus";
      else
        return "plus";
      end if;
    end if;
  elif Dimension (U) eq 2 then
    return IdentifyLineType (Q, U);
  else
    QU := RestrictBilinearForm (Q, U);
    if Determinant (QU) eq 0 then
      return "deg-plane";
    else
      return "plane";
    end if;
  end if;
end function;

__config := function (Q, rho, sigma)
  l := Eigenspace (rho, -1);
  m := Eigenspace (sigma, -1);
  P := PerpSpace (Q, l);
  R := PerpSpace (Q, m);
  spaces := [ l meet m , l meet R , P meet m , P meet R ];
return [ __identify (Q, U) : U in spaces ];
end function;


__config2 := function (Q, rho, tau)
  l := Eigenspace (rho, -1);
  x := Eigenspace (tau, 1);
  P := PerpSpace (Q, l);
  H := PerpSpace (Q, x);
  spaces := [ l meet x , l meet H , P meet x , P meet H ];
return [ __identify (Q, U) : U in spaces ];
end function;


__Preprocess := function (q)
"   << ---preprocessing the projective space--- >>";
  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q); 
  // set up <rho>
  l := sub < V | V.4 , V.5 >;
  TYPE := IdentifyLineType (Q, l);
  rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
"   << the -1 eigenspace of <rho> is a line of", TYPE, "type >>";
  R := Centralizer (Om, rho); 
  // determine the list of suitable points to search over
  PI := { sub < V | v > : v in V | v ne 0 };
"   << the projective space has", #PI, "points >>";
  PI := { z : z in PI | MyWittIndex (Q, PerpSpace (Q, z)) eq 2 };
     assert forall { z : z in PI | InnerProduct (z.1, z.1) ne 0 };
"   << of these", #PI, "are nonsingular with a V_4^+ orthogonal complement >>";
  C := Centralizer (G, rho);
  PI, sizes := OrbitReps (C, PI);
"   << and there are", #PI, "orbits under the centralizer of rho >>";
  // determine the points determining <tau> that produce dihedral intersections
  PI := [ z : z in PI ];
  TUPLES := [ ];
  GOOD := [ ];   BAD1 := [ ];   BAD2 := [ ];
  MIDDLES := [ ];   CENTRALIZERS := [ ];
  "----------";
  for i in [1..#PI] do
  "   << processing orbit rep", i, "... >>";
      tau := InvolutionOdd (PI[i], PerpSpace (Q, PI[i]));
      L := Centralizer (Om, tau);
      M := L meet R;
  "      << gives group M of order", #M, "... >>";
      isit, a, b := IsDihedral (M);
      if not isit then
      "      << ... but M is not dihedral >>";
          Append (~BAD1, tau);
      else
          // analyze the dihedral group ...
          if Dimension (Eigenspace (a, 1)) eq 1 then
              if Dimension (Eigenspace (b, 1)) eq 3 then
                  M := sub < Om | [a , b] >; 
                  Append (~MIDDLES, M);
                  Append (~CENTRALIZERS, L);
                  Append (~GOOD, tau);
                  "      << ... and M is good >>"; 
              else
              "      << ... but M is dihedral of the wrong type >>";
                  Append (~BAD2, tau);
              end if;
          elif Dimension (Eigenspace (a, 1)) eq 3 then
              if Dimension (Eigenspace (b, 1)) eq 1 then
                  M := sub < Om | [b, a] >;
                  Append (~MIDDLES, M);
                  Append (~CENTRALIZERS, L);
                  Append (~GOOD, tau);
                  "      << ... and M is good >>";
              else
              "      << ... but M is dihedral of the wrong type >>";
                  Append (~BAD2, tau);
              end if;
          else
          "      << ... but M is dihedral of the wrong type >>";
                  Append (~BAD2, tau);
          end if;
      end if;
  "----------";
  end for;
return rho, R, GOOD, MIDDLES, CENTRALIZERS, BAD1, BAD2;
end function;

__Complete_Good := function (rho, R, tau, L, M)
  k := BaseRing (M);   q := #k;
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q);
  t1 := M.1;
  s2 := M.2;
  h := t1 * s2;   m := Order (h);
  T2 := [ s2^(h^i) : i in [0..m-1] | Order (t1 * s2^(h^i)) eq m ];
  "      [ |M| =", #M, "]";
  "      [ there are", #T2, "generating involutions to try ]";
  TUPLES := [ ];
  for j in [1..#T2] do   
      "         [ trying generator", j, "... ]";
      t2 := T2[j];
      CLt2 := Centralizer (L, t2);
      cl := ConjugacyClasses (CLt2);
      icl := [ c[3] : c in cl | c[1] eq 2 ];
      I0 := &join [ Conjugates (CLt2, a) : a in icl | Dimension (Eigenspace (a, 1)) eq 3 ];
      C := Centralizer (L, M);
      J0 := RefineClass (C, [ i : i in I0 | sub < L | M , i > eq L ]);
      "         [ ... and found", #J0, "t0 candidates to try ]";
      for b in [1..#J0] do
          t0 := J0[b];
          CRt0t1 := Centralizer (R, sub < Om | t0 , t1 >);
          I3 := [ a : a in CRt0t1 | (Order (a) eq 2) and (not a in L) and 
                             (Dimension (Eigenspace (a, 1)) eq 3) and
                             (sub < R | M , a > eq R) ]; 
          if #I3 gt 0 then
          "            [ candidate", b, "produced", #I3, "4-polytopes ]";      
          end if;            
          TUPLES cat:= [ [t0, t1, t2, t3] : t3 in I3 ];
      end for;
  end for;
  GRPS := [ sub < Om | t > : t in TUPLES ];
  assert forall { H : H in GRPS | IsStringCGroup (H) };
return GRPS;
end function;

Omega5_Search := function (q)

  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q);
  
  rho, R, GOOD0, MIDS0, CENTS0, B1, B2 := __Preprocess (q);
  "|B1| =", #B1, "    |B2| =", #B2;
  "AFTER PREPROCESSING, THERE ARE", #GOOD0, "GOOD POINTS TO TRY ...";
  
  GRPS := [ ];   GOOD := [ ];   MIDS := [ ];   CENTS := [ ]; 
  BAD := [ ];
  for i in [1..#GOOD0] do
  "   TRYING GOOD POINT", i, "...";
      tau := GOOD0[i];
      L := CENTS0[i];
      M := MIDS0[i];
      GRPSi := __Complete_Good (rho, R, tau, L, M);
      if #GRPSi gt 0 then
          Append (~GRPS, GRPSi);
          Append (~GOOD, tau);
          Append (~MIDS, M);
          Append (~CENTS, L);
      else
          Append (~BAD, tau);
      end if;
  "   ... AND FOUND", #GRPSi, "4-POLYTOPES WITH SCHLAFLI SYMBOLS"; 
  { SchlafliSymbol (H) : H in GRPSi };
  "   =============";
  end for;
  
return rho, R, GRPS, GOOD, MIDS, CENTS, BAD, B1, B2;

end function;

Omega5_NewSearch := function (q)

  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q);
  
  // set up <rho>
  l := sub < V | V.4 , V.5 >;
  TYPE := IdentifyLineType (Q, l);
  rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
  N := Centralizer (G, rho);
  R := Centralizer (Om, rho);
  CGR := Centralizer (G, R);
assert #N div #R eq 4;
"|N| =", #N, "    |R| =", #R, "    |CGR| =", #CGR;

  // fix <r0> that we like
  l0 := sub < V | V.1 , V.5 >;
  assert IdentifyLineType (Q, l0) eq TYPE;
  r0 := InvolutionOdd (PerpSpace (Q, l0), l0);   assert r0 in R;
  CR0 := Centralizer (R, r0);
  CN0 := Centralizer (N, r0);

  T0 := [ c[3] : c in ConjugacyClasses (CR0) | c[1] eq 2 ];
  T0 := [ a : a in T0 | Dimension (Eigenspace (a, 1)) eq 1 ];
  "there are", #T0, "classes of reflections in R commuting with r0";
  T0 := &join [ Conjugates (CR0, a) : a in T0 ];
  T0 := [ a : a in T0 ];
  "giving rise to", #T0, "potential t candidates...";
  T0 := [ a : a in T0 | (not Eigenspace (a, 1) subset l) and
                         (not Eigenspace (a, 1) subset l0) ];
  "of which", #T0, "are of the correct type";
  assert #Set ([ __config2 (Q, rho, tau) : tau in T0 ]) eq 1;
  assert #Set ([ __config2 (Q, r0, tau) : tau in T0 ]) eq 1;       
"------------------";
  
  // work through possibilities for <r1> and <t>
  reps0 := InvolutionClassReps (R);
  reps0 := [ a : a in reps0 | (a ne rho) and (Dimension (Eigenspace (a, 1)) eq 3)
  and (not Eigenspace (a, -1) subset Eigenspace (rho, 1)) ];
  assert #reps0 eq 2;
  j := WhichClass (R, reps0, r0); 
  s1 := reps0[3-j];   // the other rep
  X1 := Conjugates (R, s1);   // the entire "opposite" class
"there are", #X1, "involutions in R of the opposite sort as r0";
  if (q mod 4 eq 1) then m := (q-1); else m := (q+1); end if;
  Y1 := [ a : a in X1 | Order (a * r0) eq m ];
"of these,", #Y1, "are such that the product with r0 has order", m;
      // the centralizer in N of r0 acts on this set; we need only consider orbit reps
  pre_reps1, pre_sizes1 := RefineClass (CN0, Y1);
"taking reps under the action of C_{N(R)}(r0) we get", #pre_reps1, "candidates for r1";
      // but we should only consider those that admit an <r3>
  
  reps1 := [ ]; sizes1 := [ ];
  REPS3 := [* *];
  BAD2 := [ ];
  CENTS12 := [ ];
  CENTS3 := [ ];
  for i in [1..#pre_reps1] do
    r1 := pre_reps1[i];
    D12 := sub < Om | r0 , r1 >;
    C12 := Centralizer (Om, D12);
    Append (~CENTS12, C12);
    X3 := Involutions (C12);
    Y3 := [ a : a in X3 | not a in R and Dimension (Eigenspace (a, 1)) eq 3 ];
    reps3 := RefineClass (CGR, [ a : a in Y3 ]);
    if #reps3 gt 0 then
      Append (~reps1, r1);
      Append (~sizes1, pre_sizes1[i]);
      Append (~REPS3, reps3);
      Append (~CENTS3, C12);
    else
      Append (~BAD2, r1);
    end if; 
  end for;
"removing candidates that admit no suitable r3,", #reps1, "r1 candidates remain";
"|C(<r0,r1>)| =", { #H : H in CENTS3 }, "   for candidates";
"|C(<r0,r1>)| =", { #H : H in CENTS12 | not H in CENTS3 }, "   for discarded r1";
"------------------";
  
  TRIPS := [ ];
  BAD1 := [ ];
  for i in [1..#reps1] do
"   processing r1 candidate", i, "of class size", sizes1[i];
      r1 := reps1[i];
      CN01 := Centralizer (CN0, r1);
      T := RefineClass (CN01, T0);
"   taking reps under the action of C_{N(R)}(<r0,r1>) we get", #T, "candidates for t";
      T := [ a : a in T | sub<R|a,r1,r0> eq R ];
"   of these,", #T, "generate R";
      if #T eq 0 then
          Append (~BAD1, r1);
      end if;
      TRIPS cat:= [ [r0, r1, a] : a in T ];
"   ============";
  end for;

"of the", #reps1, "candidates for r1,", #BAD1, "did not admit a suitable t";
"altogether, we obtained", #TRIPS, "polyhedra for R = C(<rho>)";

  // try to extend each of these polyhedra
  GRPS := [ ];
  Cr0 := Centralizer (Om, r0);
    
"---------------------";
  for i in [1..#TRIPS] do
"   processing polyhedron", i;
      trip := TRIPS[i];
      r1 := trip[2];
      j := Position (reps1, r1);
"   r1 class", j;
      reps3 := REPS3[j];
              "   polyhedron admits", #reps3, "r3 candidates";
      S3 := [ a : a in reps3 | sub<Om|r1,trip[3],a> meet R eq sub<Om|r1,trip[3]> ];
              "   of these,", #S3, "satisfy the intersection condition";
      GRPS cat:= [ sub<Om|trip cat [a]> : a in S3 ];
"   =================";      
  end for;
  
/*  
BAD2 := Set (BAD2);   BAD3 := Set (BAD3);
BAD2 := [ a : a in BAD2 ];   BAD3 := [ a : a in BAD3 ];
GOOD := [ a : a in pre_reps1 | (not a in BAD1) and (not a in BAD2) and (not a in BAD3) ];
"we processed", #pre_reps1, "candidates for r1:";
"   ", #BAD1, "did not admit polyedra for R = C(rho)";
"   ", #BAD2, "did not admit a suitable r3";
"   ", #BAD3, "admitted suitable r3 but none produced 4-polytopes";
*/

/*
"geometric configuations of good r1:";
for i in [1..#GOOD] do
  "i =", i;
  r1 := GOOD[i];
  __config (Q, r0, r1);
D := sub < Om | r0, r1 >;
MD := GModule (D);
IMD := IndecomposableSummands (MD);
IVD := [ sub<V|[V!(MD!(N.i)) : i in [1..Ngens(N)]]> : N in IMD ];
[ __identify (Q, U) : U in IVD ];
  l1 := Eigenspace (r1, -1);
  "l0 me l1:", Dimension (l0 meet l1);
  "l0 me l1*:", Dimension (l0 meet PerpSpace (Q, l1));
  "l0* me l1:", Dimension (PerpSpace (Q, l0) meet l1);
  "l0* me l1*:", Dimension (PerpSpace (Q, l0) meet PerpSpace (Q, l1));
  "-------";
end for;
"  ";

"geometric configurations of BAD1:";
for i in [1..#BAD1] do
  "i =", i;
  r1 := BAD1[i];
  __config (Q, r0, r1);
D := sub < Om | r0, r1 >;
MD := GModule (D);
IMD := IndecomposableSummands (MD);
IVD := [ sub<V|[V!(MD!(N.i)) : i in [1..Ngens(N)]]> : N in IMD ];
[ __identify (Q, U) : U in IVD ];
  l1 := Eigenspace (r1, -1);
  "l0 me l1:", Dimension (l0 meet l1);
  "l0 me l1*:", Dimension (l0 meet PerpSpace (Q, l1));
  "l0* me l1:", Dimension (PerpSpace (Q, l0) meet l1);
  "l0* me l1*:", Dimension (PerpSpace (Q, l0) meet PerpSpace (Q, l1));
  "-------";
end for;

"geometric configurations of BAD2:";
for i in [1..#BAD2] do
  "i =", i;
  r1 := BAD2[i];
  __config (Q, r0, r1);
D := sub < Om | r0, r1 >;
MD := GModule (D);
IMD := IndecomposableSummands (MD);
IVD := [ sub<V|[V!(MD!(N.i)) : i in [1..Ngens(N)]]> : N in IMD ];
[ __identify (Q, U) : U in IVD ];
  l1 := Eigenspace (r1, -1);
  "l0 me l1:", Dimension (l0 meet l1);
  "l0 me l1*:", Dimension (l0 meet PerpSpace (Q, l1));
  "l0* me l1:", Dimension (PerpSpace (Q, l0) meet l1);
  "l0* me l1*:", Dimension (PerpSpace (Q, l0) meet PerpSpace (Q, l1));
  "-------";
end for;
"  ";

"geometric configurations of BAD3:";
for i in [1..#BAD3] do
  "i =", i;
  r1 := BAD3[i];
  __config (Q, r0, r1);
D := sub < Om | r0, r1 >;
MD := GModule (D);
IMD := IndecomposableSummands (MD);
IVD := [ sub<V|[V!(MD!(N.i)) : i in [1..Ngens(N)]]> : N in IMD ];
[ __identify (Q, U) : U in IVD ];
  l1 := Eigenspace (r1, -1);
  "l0 me l1:", Dimension (l0 meet l1);
  "l0 me l1*:", Dimension (l0 meet PerpSpace (Q, l1));
  "l0* me l1:", Dimension (PerpSpace (Q, l0) meet l1);
  "l0* me l1*:", Dimension (PerpSpace (Q, l0) meet PerpSpace (Q, l1));
  "-------";
end for;
*/

"We found", #GRPS, "4-polytopes having Schlafli symbols:";
{ SchlafliSymbol (H) : H in GRPS };
  
return GRPS, rho, r0; 
//GOOD, BAD1, BAD2, BAD3;
end function;

PairClasses := function (q : SAN := false)

  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q);
  
  cl := ConjugacyClasses (Om);
  icl := [ c : c in cl | c[1] eq 2 ];
  reps := [ c[3] : c in icl | Dimension (Eigenspace (c[3], 1)) eq 3 ];
  assert #reps eq 1;
  rho := reps[1];
  l := Eigenspace (rho, -1); P := PerpSpace (Q, l); assert P eq Eigenspace (rho, 1);
  C := Centralizer (G, rho);
  
  X := Conjugates (Om, rho);
  if SAN then assert X eq Conjugates (G, rho); end if;
    
  Y := { a : a in X | (a, rho) eq Identity (G) };
  X := Set (X) diff Y;
  
  X := [ a : a in X ];
  Y := [ a : a in Y | a ne rho ];
  
  Xreps := RefineClass (C, X);
  Yreps := RefineClass (C, Y);
  "there are", #Yreps, "commuting classes";
  "there are", #Xreps, "non-commuting classes ...";
/*
  if (q mod 4 eq 1) then M := (q-1); else M := (q+1); end if;
  Xreps := [ a : a in Xreps | Order (a * rho) eq M ];
  "... of which", #Xreps, "have the desired order";
*/
  
  configs := [ ];
  for i in [1..#Xreps] do
  "--------";
  "   i =", i;
     s := Xreps[i];
  "   |rho * s| =", Order (rho * s);
     m := Eigenspace (s, -1);   R := PerpSpace (Q, m);   assert R eq Eigenspace (s, 1);
     "   dim(l meet m) =", Dimension (l meet m), "    ", __identify (Q, l meet m);
     "   dim(l meet R) =", Dimension (l meet R), "    ", __identify (Q, l meet R);
     "   dim(P meet m) =", Dimension (P meet m), "    ", __identify (Q, P meet m);
     "   dim(P meet R) =", Dimension (P meet R), "    ", __identify (Q, P meet R);
     Append (~configs,
       [ __identify (Q, l meet m),  __identify (Q, l meet R), __identify (Q, P meet m),
         __identify (Q, P meet R) ]
            );
  end for;
  
  "  ";
  "  ";
  for i in [1..#Yreps] do
  "--------";
  "   i =", i;
     s := Yreps[i];
     m := Eigenspace (s, -1);   R := PerpSpace (Q, m);   assert R eq Eigenspace (s, 1);
     "   dim(l meet m) =", Dimension (l meet m), "    ", __identify (Q, l meet m);
     "   dim(l meet R) =", Dimension (l meet R), "    ", __identify (Q, l meet R);
     "   dim(P meet m) =", Dimension (P meet m), "    ", __identify (Q, P meet m);
     "   dim(P meet R) =", Dimension (P meet R), "    ", __identify (Q, P meet R);
  end for;  
  "  ";
  
  
return Xreps, Yreps, configs;

end function;

__basics := function (q)
  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q); 
  // set up <rho>
  l := sub < V | V.4 , V.5 >;
  TYPE := IdentifyLineType (Q, l);
  rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
  N := Centralizer (G, rho);
  R := Centralizer (Om, rho);
  assert #N div #R eq 4;
  // fix <r0> 
  l0 := sub < V | V.1 , V.5 >;
  assert IdentifyLineType (Q, l0) eq TYPE;
  r0 := InvolutionOdd (PerpSpace (Q, l0), l0);   assert r0 in R;
  R0 := Centralizer (R, r0);
  N0 := Centralizer (N, r0);
  cl := ConjugacyClasses (R);
  cl := [ c[3] : c in cl | (c[1] eq 2) and ((c[3], r0) ne Identity (R)) ];
  I := &join [ Conjugates (R, a) : a in cl ];
  I := [ a : a in I ];
  R0cl := RefineClass (R0, I);
  N0cl := RefineClass (N0, I);
return rho, r0, N, R, N0, R0, N0cl, R0cl;
end function;
  
  