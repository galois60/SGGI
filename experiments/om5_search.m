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
  
  