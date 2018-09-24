Omega5_Search := function (q)

  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  S := MySO (5, q);
  Om := MyOmega (5, q);
  
  // set up <rho>
  l := sub < V | V.4 , V.5 >;
  TYPE := IdentifyLineType (Q, l);
  rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
  "-1 eigenspace of <rho> is a line of", TYPE, "type";
  R := Centralizer (Om, rho);
  
  // determine the list of suitable points to search over
  PI := { sub < V | v > : v in V | v ne 0 };
  "projective space has", #PI, "points";
  PI := { z : z in PI | MyWittIndex (Q, PerpSpace (Q, z)) eq 2 };
     assert forall { z : z in PI | InnerProduct (z.1, z.1) ne 0 };
  "of which", #PI, "are of the correct type";
  C := Centralizer (G, rho);
  PI, sizes := OrbitReps (C, PI);
  "C_G(<rho>) acts on this set with", #PI, "orbits";
  
  // main loop
  PI := [ z : z in PI ];
  TUPLES := [ ];
  GOOD_tau := [ ];
  BAD_tau := [ ];
  for i in [1..#PI] do
      "   trying orbit rep", i;
      good := false;
      tau := InvolutionOdd (PI[i], PerpSpace (Q, PI[i]));
      L := Centralizer (Om, tau);
      M := L meet R;
      isit, a, b := IsDihedral (M);
      if isit then
      "   gives M of order", #M;
          // analyze the dihedral group ...
          if Dimension (Eigenspace (a, 1)) eq 1 then
              assert Dimension (Eigenspace (b, 1)) eq 3;
              t1 := a;
              s2 := b;
          else
              assert Dimension (Eigenspace (a, 1)) eq 3;
              assert Dimension (Eigenspace (b, 1)) eq 1;
              t1 := b;
              s2 := a;
          end if;
          h := a * b;   
          m := Order (h); assert 2*m eq #M;
          T2 := [ s2^(h^i) : i in [0..m-1] | Order (t1 * s2^(h^i)) eq m ];
          //assert #T2 eq EulerPhi (m);
          "   there are", #T2, "generating involutions to try";
          COUNT := 0;
          for j in [1..#T2] do   // may want to keep track of which work and which don't
             //"      trying generator", j;
             t2 := T2[j];
             CLt2 := Centralizer (L, t2);
             cl := ConjugacyClasses (CLt2);
             icl := [ c[3] : c in cl | c[1] eq 2 ];
             I0 := &join [ Conjugates (CLt2, a) : a in icl | Dimension (Eigenspace (a, 1)) eq 3 ];
             C := Centralizer (L, M);
             J0 := RefineClass (C, [ i : i in I0 | sub < L | M , i > eq L ]);
             for t0 in J0 do
                 CRt0t1 := Centralizer (R, sub < Om | t0 , t1 >);
                 I3 := [ a : a in CRt0t1 | (Order (a) eq 2) and (not a in L) and 
                             (Dimension (Eigenspace (a, 1)) eq 3) and
                             (sub < R | M , a > eq R) ];
                 if #I3 gt 0 then
                     good := true;
                 end if;
                 TUPLES cat:= [ [t0, t1, t2, t3] : t3 in I3 ];
             end for;
          end for;         
          if good then
              Append (~GOOD_tau, tau);
          else
              Append (~BAD_tau, tau);
          end if;
      else
          Append (~BAD_tau, tau);
          "M is not dihedral";
      end if;
      "---------";
  end for;
  "of these orbit reps", #GOOD_tau, "are of the desired type";
  
  GRPS := [ sub < Om | t > : t in TUPLES ];
  assert forall { H : H in GRPS | IsStringCGroup (H) };
  
  "resulting Schlafli types are", Set ([ SchlafliSymbol (H) : H in GRPS ]);
  
return GRPS, rho, GOOD_tau, BAD_tau;

end function;
  
  