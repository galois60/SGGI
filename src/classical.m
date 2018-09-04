/* ----- some useful intrinsics for computing with classical groups ----- */


intrinsic PerpSpace (F::Mtrx, U::ModTupFld) -> ModTupFld
  {Compute the perp-space of U relative to the bilinear form F.}
  V := Generic (U);
  k := BaseRing (V);
  M := Matrix (k, Dimension (V), Dimension (U), 
			     [ 0 : i in [1..Dimension (V) * Dimension (U)] ]);
  for s in [1..Dimension (V)] do
    for t in [1..Dimension (U)] do
      M[s][t] := InnerProduct (V.s * F, U.t);
    end for;
  end for;
return Nullspace (M);
end intrinsic;


intrinsic PreservesBilinearForm (g::GrpMatElt, F::Mtrx) -> BoolElt
  {Check if g is an isometry of the bilinear form F.}
  require Degree (Parent (g)) eq Nrows (F) : "arguments must have compatible degrees";
return g * F * Transpose (g) eq F;
end intrinsic;


intrinsic PreservesBilinearForm (G::GrpMat, F::Mtrx) -> BoolElt
  {Check if G is a group of isometries of the bilinear form F.}
return forall { i : i in [1..Ngens (G)] | PreservesBilinearForm (G.i, F) };
end intrinsic;


intrinsic PreservesQuadraticForm (g::GrpMatElt, Q::Mtrx) -> BoolElt
  {Check if g is an isometry of the quadratic form Q.}
  if not PreservesBilinearForm (g, Q + Transpose (Q)) then
      return false;
  end if;
  if Characteristic (BaseRing (Parent (g))) mod 2 eq 1 then
      return true;
  end if;
  V := VectorSpace (BaseRing (Parent (g)), Degree (Parent (g)));
return forall { i : i in [1..Ngens (V)] |
         InnerProduct (V.i * g * Q, V.i * g) eq InnerProduct (V.i * Q, V.i) };
end intrinsic;


intrinsic PreservesQuadraticForm (G::GrpMat, Q::Mtrx) -> BoolElt
  {Check if G is a group of isometries of the quadratic form Q.}
return forall { i : i in [1..Ngens (G)] | PreservesQuadraticForm (G.i, Q) };
end intrinsic;


intrinsic RestrictBilinearForm (F::Mtrx, U::ModTupFld) -> Mtrx
  {Restrict the bilinear form F to the subspace U.}
  B := Basis (U);
  F_res := Matrix ([ [ InnerProduct (B[i] * F, B[j]) : j in [1..#B] ] : 
              i in [1..#B] ]);
return MatrixAlgebra (BaseRing (U), Dimension (U))!F_res;
end intrinsic;


intrinsic RestrictQuadraticForm (Q::Mtrx, U::ModTupFld) -> Mtrx
  {Restrict the quadratic form Q to the subspace U.}
  F := Q + Transpose (Q);
  B := Basis (U);
  Q_res := MatrixAlgebra (BaseRing (U), #B)!0;
  for i in [1..#B] do
      Q_res[i][i] := InnerProduct (B[i] * Q, B[i]);
      for j in [i+1..#B] do
          Q_res[i][j] := InnerProduct (B[i] * F, B[j]);
      end for;
  end for; 
return Q_res;
end intrinsic;

intrinsic InvolutionOdd (Ep::ModTupFld, Em::ModTupFld) -> GrpMatElt
  {In a field of odd characteristic, the involution inducing 1 on Ep and -1 on Em.}
  n := Degree (Ep);
  k := BaseRing (Ep);
  i := Identity (MatrixAlgebra (k, n));
  for x in [1+Dimension (Ep)..n] do
       i[x][x] := -1;
  end for;
  C := Matrix (Basis (Ep) cat Basis (Em));
return GL (n, k)!(C^-1 * i * C);
end intrinsic; 


intrinsic InduceGroup (G::GrpMat, U::ModTupFld) -> GrpMat, Map
  {For G stabilizing U, return the group induced by G on U and the 
   homomorphism from G to this group.}
   require BaseRing (G) eq BaseRing (U) : "arguments must be defined over same ring";
   require forall { i : i in [1..Ngens (G)] | U * (G.i) eq U } :
      "G must stabilize U";
   e := Dimension (U);
   K := BaseRing (U);
   BU := Basis (U);
   gens := [ GL (e, K)!Matrix ([ Coordinates (U, BU[j] * G.i) : j in [1..e] ]) :
               i in [1..Ngens (G)] ];
   H := sub < GL (e, K) | gens >;
   RandomSchreier (H);
   f := hom < G -> H | gens >; 
return H, f;
end intrinsic;


intrinsic IsNonsingularOrthogonalSpace (Q::Mtrx) -> BoolElt
  {Decide if Q is a nonsingular quadratic form on its underlying module.}
  U := VectorSpace (BaseRing (Parent (Q)), Nrows (Q));
  F := Q + Transpose (Q);
  if Nrows (Q) mod 2 eq 0 then
      return Determinant (F) eq 0;
  else
  radU := PerpSpace (F, U);
      return Dimension (radU) eq 1 and InnerProduct (radU.1 * Q, radU.1) ne 0;
  end if;
end intrinsic;


intrinsic IsHyperbolicLine (Q::Mtrx, U::ModTupFld) -> BoolElt, ModTupFldElt, ModTupFldElt
  {Decide if U is a hyperbolic line relative to quadratic form Q.}
    if Dimension (U) ne 2 then
        return false, _, _;
    end if;
    F := Q + Transpose (Q);
    B := Basis (U);
    u1 := B[1];   
    u2 := B[2];
    R<x> := PolynomialRing (BaseRing (U));
    f := InnerProduct (u1 * Q, u1) + InnerProduct (u1 * F, u2) * x + 
         InnerProduct (u2 * Q, u2) * x^2;
    if Degree (f) eq 0 then
        return false, _, _;
    elif Degree (f) eq 1 then
        roots := Roots (f);
        return true, u1 + roots[1][1] * u2, u2;
    else
        roots := Roots (f);
        if #roots ne 2 then
            return false, _, _;
        else
            return true, u1 + roots[1][1] * u2, u1 + roots[2][1] * u2;
        end if;
    end if;  
end intrinsic;


intrinsic IdentifyLineType (Q::Mtrx, U::ModTupFld : SANITY := false) -> MonStgElt
  {Decide whether the 2-space is totally singular, hyperbolic, singular, or asingular.} 
  require Dimension (U) eq 2 : "U must be 2-dimensional";
  if SANITY then
      pts := { sub < U | u > : u in U | u ne 0 };
  end if;  
  F := Q + Transpose (Q);
  u1 := Basis (U)[1];   u2 := Basis (U)[2];
  R<x> := PolynomialRing (BaseRing (U));
  f := InnerProduct (u1 * Q, u1) + InnerProduct (u1 * F, u2) * x + 
         InnerProduct (u2 * Q, u2) * x^2;        
  if f eq 0 then   
      if SANITY then
          assert forall { P : P in pts | InnerProduct (P.1 * Q, P.1) eq 0 };
      end if;
      return "totally singular";     
  elif Degree (f) eq 0 then 
      if SANITY then
          assert #{ P : P in pts | InnerProduct (P.1 * Q, P.1) eq 0 } eq 1;
      end if; 
      return "singular";    
  elif Degree (f) eq 1 then
      if SANITY then
          assert #{ P : P in pts | InnerProduct (P.1 * Q, P.1) eq 0 } eq 2;
      end if;
      return "hyperbolic";  
  else  
      roots := Roots (f);
      if #roots eq 0 then
          if SANITY then
              assert forall { P : P in pts | InnerProduct (P.1 * Q, P.1) ne 0 };
          end if;
          return "asingular";
      elif #roots eq 1 then
          if SANITY then
              assert #{ P : P in pts | InnerProduct (P.1 * Q, P.1) eq 0 } eq 1;
          end if; 
          return "singular";
      else
          if SANITY then
              assert #{ P : P in pts | InnerProduct (P.1 * Q, P.1) eq 0 } eq 2;
          end if;
          return "hyperbolic";
      end if;    
  end if;
end intrinsic;


intrinsic MyWittIndex (Q::Mtrx, U::ModTupFld) -> RngIntElt
  {The isometry type of the subspace U of the quadratic space determined by Q.}
    if Dimension (U) eq 0 then
         return -2;
    end if;
    QU := RestrictQuadraticForm (Q, U);
    if Determinant (Q + Transpose (Q)) eq 0 then
         return -1;
    else
         return WittIndex (QuadraticSpace (QU));
    end if;  
end intrinsic;

// this should just be cut now
intrinsic Reflection (v::ModTupFldElt, Q::Mtrx) -> GrpMatElt
  {Return the reflection in the perp-space of v relative to F, where v
   is non-singular with respect to Q.}
    F := Q + Transpose (Q);
    V := Generic (Parent (v));
    k := BaseRing (V);
    d := Degree (V);
    nu := InnerProduct (v * Q, v);
    require nu ne 0 : "v must be nonsingular with respect to Q";
    R := Matrix ([ V.i - InnerProduct (V.i * F, v) * v / nu : i in [1..d] ]);
    r := GL (d, k)!R;
    assert Order (r) eq 2;
return r;
end intrinsic;


// Symmetry is the correct (i.e. more general) name for Reflection.
intrinsic Symmetry (v::ModTupFldElt, Q::Mtrx) -> GrpMatElt
  {Return the symmetry defined by the nonsingular vector v.}
    F := Q + Transpose (Q);
    V := Generic (Parent (v));
    k := BaseRing (V);
    d := Degree (V);
    nu := InnerProduct (v * Q, v);
    require nu ne 0 : "v must be nonsingular with respect to Q";
    R := Matrix ([ V.i - InnerProduct (V.i * F, v) * v / nu : i in [1..d] ]);
    r := GL (d, k)!R;
    assert r * F * Transpose (r) eq F;
    assert forall { i : i in [1..d] | InnerProduct (V.i * r * Q, V.i * r) eq InnerProduct (V.i * Q, V.i) };
    assert Order (r) in [1,2];
return r;
end intrinsic;


intrinsic TransvectionGroup (v::ModTupFldElt, F::Mtrx) -> GrpMat
  {Return the group of (v,W)-transvections, where W is the perp-space
   of v relative to F.}
    V := Generic (Parent (v));
    k := BaseRing (V);
    d := Degree (V);
    e := Degree (k);
return sub < GL (d, k) | [ 
  GL (d, k)!Matrix ([ V.i + k.1^j * InnerProduct (V.i * F, v) * v : i in [1..d] ]) 
     : j in [0..e-1] 
          ] >;
end intrinsic;


intrinsic PseudoTransvectionGroup (v::ModTupFldElt, b::ModTupFldElt, Q::Mtrx)
     -> GrpMat
  {Return the group of pseudo-tansvections associated to the line 
   L = <v,b>, where Q(v)=(v,b)=0.}
    V := Generic (Parent (v));
    F := Q + Transpose (Q);
    k := BaseRing (V);
    d := Degree (V);
    e := Degree (k);
return sub < GL (d, k) | [ 
  GL (d, k)!Matrix ([ V.i + 
     k.1^j * ( InnerProduct (V.i * F, b) * v - InnerProduct (V.i * F, v) * b )
     -k.1^(2*j) * InnerProduct (b * Q, b) * InnerProduct (V.i * F, v) * v : 
     i in [1..d] ]) : j in [0..e-1] 
          ] >;  
end intrinsic;


intrinsic MySupport (X::Mtrx) -> ModTupFld
  {Compute the support of matrix X on its underlying vector space.}
    k := BaseRing (X);
    d := Degree (X);
    V := VectorSpace (k, d);
    gens := [ V.i - V.i * X : i in [1..d] ];
    W := sub < V | gens >;
return sub < V | Basis (W) >;
end intrinsic;


intrinsic MySupport (H::GrpMat) -> ModTupFld
  {Compute the support of matrix group H on its underlying vector space.}
return &+ [ MySupport (H.i) : i in [1..Ngens (H)] ];
end intrinsic;


intrinsic MySupport (A::AlgMat) -> ModTupFld
  {Compute the support of matrix algebra A on its underlying vector space.}
return &+ [ MySupport (A.i) : i in [1..Ngens (A)] ];
end intrinsic;


intrinsic SpIsotropic (d::RngIntElt, q::RngIntElt) -> GrpMat, Mtrx, Map
  {Return the symplect group Sp(d,q) relative to a totally isotropic basis.}
  assert d mod 2 eq 0;
  m := d div 2;
  pi := SymmetricGroup (d)!([1..m] cat Reverse ([m+1..d]));
  c := PermutationMatrix (GF (q), pi);
  G0 := Sp (d, q);
  F0 := ClassicalForms (G0)`bilinearForm;
  G := sub < GL (d, q) | [ c * G0.i * c^-1 : i in [1..Ngens (G0)] ] >;
  F := c * F0 * Transpose (c);
  phi := hom < G0 -> G | [ G.i : i in [1..Ngens (G)] ] >;
return G, F, phi;
end intrinsic;

intrinsic SpHyperbolic (d::RngIntElt, q::RngIntElt) -> GrpMat, Mtrx, Map
  {Return the symplect group Sp(d,q) relative to a hyperbolic basis.}
  assert d mod 2 eq 0;
  m := d div 2;
  pi := SymmetricGroup (d)!([2*i-1 : i in [1..m]] cat Reverse ([2*i : i in [1..m]]));
  c := PermutationMatrix (GF (q), pi)^-1;
  G0 := Sp (d, q);
  F0 := ClassicalForms (G0)`bilinearForm;
  G := sub < GL (d, q) | [ c * G0.i * c^-1 : i in [1..Ngens (G0)] ] >;
  F := c * F0 * Transpose (c);
  phi := hom < G0 -> G | [ G.i : i in [1..Ngens (G)] ] >;
return G, F, phi;
end intrinsic;

intrinsic MyGO (d::RngIntElt, q::RngIntElt) -> GrpMat
  {Full orthogonal group written relative to an orthonormal basis.}
  F := Identity (MatrixAlgebra (GF (q), d));
  if d mod 2 eq 0 then
       C := TransformForm (F, "orthogonalplus");
       G0 := GOPlus (d, q);
  else
       C := TransformForm (F, "orthogonalcircle");
       G0 := GO (d, q);
  end if;
  G := sub < GL (d, q) | [ C * G0.i * C^-1 : i in [1..Ngens (G0)] ] >;
return G;
end intrinsic;

intrinsic MySO (d::RngIntElt, q::RngIntElt) -> GrpMat
  {Full orthogonal group written relative to an orthonormal basis.}
  F := Identity (MatrixAlgebra (GF (q), d));
  if d mod 2 eq 0 then
       C := TransformForm (F, "orthogonalplus");
       G0 := SOPlus (d, q);
  else
       C := TransformForm (F, "orthogonalcircle");
       G0 := SO (d, q);
  end if;
  G := sub < GL (d, q) | [ C * G0.i * C^-1 : i in [1..Ngens (G0)] ] >;
return G;
end intrinsic;

intrinsic MyOmega (d::RngIntElt, q::RngIntElt) -> GrpMat
  {Full orthogonal group written relative to an orthonormal basis.}
  F := Identity (MatrixAlgebra (GF (q), d));
  if d mod 2 eq 0 then
       C := TransformForm (F, "orthogonalplus");
       G0 := OmegaPlus (d, q);
  else
       C := TransformForm (F, "orthogonalcircle");
       G0 := Omega (d, q);
  end if;
  G := sub < GL (d, q) | [ C * G0.i * C^-1 : i in [1..Ngens (G0)] ] >;
return G;
end intrinsic;


intrinsic C2MaximalSpIsotropic (d::RngIntElt, q::RngIntElt) -> GrpMat
  {Return the totally isotropic (C2) maximal subgroup of the nice Sp(d,q).}
  G, F := SpIsotropic (d, q);
  require d mod 2 eq 0 : "d must be even";
  m := d div 2;
  gens := [ GL (d, q)!(DiagonalJoin (GL (m, q).i, Transpose (GL (m, q).i^-1))) :
                      i in [1..Ngens (GL (m, q))] ];
  t := MatrixAlgebra (GF (q), d)!0;
  InsertBlock (~t, Identity (GL (m, q)), 1, m+1);
  InsertBlock (~t, -Identity (GL (m, q)), m+1, 1);
  Append (~gens, GL (d, q)!t);
  M := sub < GL (d, q) | gens >;
return M;
end intrinsic;


intrinsic C2MaximalSp4Hyperbolic (q::RngIntElt) -> GrpMat
  {Return the totally hyperbolic (C2) maximal subgroup of 
   Sp(4,q) relative to hyperbolic basis.}
  G, F := SpHyperbolic (4, q);
  sl2 := SL (2, q);
  gens1 := [ ];
  gens2 := [ ];
  for i in [1..Ngens (sl2)] do
      x := sl2.i;
      g1 := MatrixAlgebra (GF (q), 4)!1;
      InsertBlock (~g1, x, 1, 1);
      Append (~gens1, GL (4, q)!g1);
      g2 := MatrixAlgebra (GF (q), 4)!1;
      InsertBlock (~g2, x, 3, 3);
      Append (~gens2, GL (4, q)!g2);
  end for;
  gens := gens1 cat gens2;
  t := MatrixAlgebra (GF (q), 4)!0;
  InsertBlock (~t, MatrixAlgebra (GF (q), 2)!1, 1, 3);
  InsertBlock (~t, MatrixAlgebra (GF (q), 2)!1, 3, 1);
  Append (~gens, GL (4, q)!t);
  M := sub < GL (4, q) | gens >;
  assert forall { i : i in [1..Ngens (M)] | M.i * F * Transpose (M.i) eq F };
return M;
end intrinsic;


/* analogue of "Eltseq" that allows one to specify basis */
__Eltseq_With_Basis := function (K, k, bas, x)
     assert #bas eq (Degree (K) div Degree (k));
     W, g := VectorSpace (K, k);
     U := VectorSpaceWithBasis ([ bas[i] @ g : i in [1..#bas] ]);
return Coordinates (U, x @ g);
end function;


/* 
 given <T> acting irreducibly on its underlying module, return 
 inverse isomorphsisms from Env(<T>) to the isomorphic field.
 */
intrinsic IsomorphismWithField (T::AlgMatElt) -> AlgMat, FldFin, Map, Map
  {Given T acting irreducibly on its underlying module, compute
   inverse isomorphsisms from Env(<T>) to the isomorphic field.}
     if T eq Identity (Parent (T)) then
         K := BaseRing (Parent (T));
         EnvT := sub < Parent (T) | T >;
         phi := hom < EnvT -> K | x :-> x[1][1] >;
         psi := hom < K -> EnvT | x :-> x * T >;
     else
         mT := MinimalPolynomial (T);
         assert IsIrreducible (mT);
         e := Degree (mT);
         k := BaseRing (Parent (T));
         d := Degree (Parent (T));
         K := ext < k | mT >;
         Kbas := [ (K.1)^i : i in [0..e-1] ];
         Tbas := [ T^i : i in [0..e-1] ];
         MS := KMatrixSpace (k, d, d);
         MS := KMatrixSpaceWithBasis ([ MS!(Tbas[i]) : i in [1..e] ]);
         EnvT := sub < Parent (T) | T >; 
         phi := hom < EnvT -> K | x :-> &+ [c[i] * Kbas[i] : i in [1..e]]
            where c := Coordinates (MS, MS!x) >;
         psi := hom < K -> EnvT | x :-> &+ [c[i] * Tbas[i] : i in [1..e]]
            where c := __Eltseq_With_Basis (K, k, Kbas, x) >;
     end if;
return EnvT, K, phi, psi;
end intrinsic;


/* embedding of GU(2,q):2 in nice copy of Sp(4,q).      */
/* Note: "nice" involution in Magma copy of GU(2,q) is  */
/*     [ 0  1 ]                                         */
/*     [ 1  0 ]                                         */ 
intrinsic C3MaximalSp4 (p::RngIntElt, e::RngIntElt) -> GrpMat
  {Return the nondegenerate semilinear (C3) maximal subgroup of the nice Sp(4,q).} 
  q := p^e;
  assert (q + 1) mod 4 eq 0;
  k := GF (q);
  G := SpIsotropic (4, q); 
  /* build nice generator of K */
  T := Matrix (k, 2, 2, [0, 1, -1, 0]);
  assert (T^2 eq -1) and (IsIrreducible (CharacteristicPolynomial (T)));
  F, K, phi, psi := IsomorphismWithField (T);
  assert (K.1 eq T @ phi) and (Order (K.1) eq 4);
  /* build the embedding of GU(2,K) */
  gu := GU (2, K);
  gu_gens := [ gu.i : i in [1..Ngens (gu)] ] cat [ gu![0,1,1,0] ];
  gens := [ ];
  for h in gu_gens do
      A := Eltseq (h[1][1]);  
      B := Eltseq (h[1][2]);  
      C := Eltseq (h[2][1]);  
      D := Eltseq (h[2][2]); 
      g := Matrix (k, 4, 4, 
          [ A[1] ,  B[1] ,  B[2] ,  A[2] ,
            C[1] ,  D[1] ,  D[2] ,  C[2] ,
           -C[2] , -D[2] ,  D[1] ,  C[1] ,
           -A[2] , -B[2] ,  B[1] ,  A[1] ]);  
      g := GL (4, k)!g;
      Append (~gens, g);
  end for;
  H := sub < GL (4, k) | gens >;
  assert H subset G; 
  t := G![-1,0,0,0,0,1,0,0,0,0,-1,0,0,0,0,1];
  assert H^t eq H;
  Append (~gens, t);
  M := sub < GL (4, k) | gens >; 
return M;
end intrinsic;

intrinsic SL2toGO3 (q::RngIntElt) -> Map
  { Given q return isomorphism SL(2,q) --> GO(3,q) }  
  require #Factorisation (q) eq 1 : "q must be a prime power";
  SL2 := SL (2, q);
  RandomSchreier (SL2);
  MS := KMatrixSpace (GF (q), 2, 2);
  e := MS![1,0,0,0];
  u := MS![0,1,1,0];
  f := MS![0,0,0,1];
  SYM := KMatrixSpaceWithBasis ([e, u, f]);
  gens := [ GL (3, q)!Matrix (
             [ 
         Coordinates (SYM, SL2.j * SYM.i * Transpose (SL2.j)) :
               i in [1,2,3]
              ]
               ) : j in [1..Ngens (SL2)]
          ];
  GO3 := sub < GL (3, q) | gens >;  
  RandomSchreier (GO3);
  phi := hom < SL2 -> GO3 | gens >;  
return phi;
end intrinsic;


intrinsic ProjectiveGroup (G::GrpMat) -> GrpPerm , Map
  { Given a matrix group, compute its action on the underlying projective space } 
  K := BaseRing (G);
  d := Degree (G);
  V := VectorSpace (K, d);
  pts := { sub < V | v > : v in V | v ne 0 };
  pts := [ x : x in pts ];
  // compute permutation action of the generators of G
  gens := [ ];
  S := SymmetricGroup (#pts);
  for i in [1..Ngens (G)]  do
      perm := [ ];
      for x in pts do
          Append (~perm, Position (pts, sub<V|(x.1) * (G.i)>));
      end for;
      Append (~gens, S!perm);
  end for;
  H := sub < S | gens >;
  RandomSchreier (H);
  RandomSchreier (G);
  f := hom < G -> H | gens >;
return H, f;
end intrinsic;














