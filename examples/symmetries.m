/* constructions using symmetries */

// the elements of K such that
//  [ -1    x   ]
//  [ -x  x^2-1 ]
// has order |K| + 1 or |K| - 1
__FieldElementsPlus := function (K)
return [ x : x in K | x ne 0 and Order (GL (2, K)![-1,x,-x,x^2-1]) in [#K+1] ];
end function;

__FieldElementsMinus := function (K)
return [ x : x in K | x ne 0 and Order (GL (2, K)![-1,x,-x,x^2-1]) in [#K-1] ];
end function;

// Quadratic form with 1's on the main diagonal and elements of S on superdiagonal
__QuadraticForm := function (S)
  d := 1 + #S;
  Q := Identity (MatrixAlgebra (Parent (S[1]), d));
  for i in [1..d-1] do
      Q[i][i+1] := S[i];
  end for;
return Q;
end function;

// the subgroup of GL(V) generated by the symmetries determined by points in X 
__SigmaGroup := function (Q, X)
  assert forall { x : x in X | InnerProduct (x * Q, x) ne 0 };
  SX := [ Symmetry (x, Q) : x in X ];
return sub < GL (Nrows (Q), BaseRing (Q)) | SX >;
end function;

// the sigma group defined by a space
SigmaGroup := function (Q, W)
  P := { sub < W | w > : w in W | w ne 0 };
  X := [ x.1 : x in P | InnerProduct (x.1 * Q, x.1) ne 0 ];
return __SigmaGroup (Q, X);
end function;

// produces a quadratic form of the type we require
// can specify S or generate a random S
__GoodQuadraticForm := function (K, d : S := [ ])
  if #S gt 0 then
      return __QuadraticForm (S);
  else
      A := __FieldElementsPlus (K);
      S := [ Random (A) : i in [1..d-1] ];
      return __QuadraticForm (S);
  end if;
end function;

// produces a random string C-subgroup of O(r,2^k) of rank r
RandomStringCGroupBySymmetries := function (k, r)
  K := GF (2^k);
  V := VectorSpace (K, r);
  A := __FieldElementsPlus (K);
  S := [ Random (A) : i in [1..r-1] ];
//S := [K!1] cat [ K.1 : i in [2..r-2] ] cat [ K.1+K.1^2 ];
  Q := __QuadraticForm (S);
  T := [ Symmetry (V.i, Q) : i in [1..r] ];
  if not IsStringCGroup (T) then
    "problem!";
    "Q =", Q:Magma;
    "T =", T:Magma;
    return false, _;
  end if;
  G := sub < GL (r, K) | T >;
return G, Q;
end function;

TEST := function (k, r)
  K := GF (2^k);
  V := VectorSpace (K, r);
  Aplus := __FieldElementsPlus (K);
  Aminus := __FieldElementsMinus (K);
//  assert (#Aminus eq 1) and (#Aplus eq 2);
  S0 := [ Aminus[1] : i in [1..r-1] ];
  Q0 := __QuadraticForm (S0);
  T0 := [ Symmetry (V.i, Q0) : i in [1..r] ];
  G0 := sub < GL (r, K) | T0 >; 
  i := Random ([1..r-1]);
  S := S0;
  S[i] := Random (Aplus);
  Q := __QuadraticForm (S);
"Q =", Q;
  T := [ Symmetry (V.i, Q) : i in [1..r] ];
  G := sub < GL (r, K) | T >;
  assert IsStringCGroup (G);
CompositionFactors (G);  
return G;
end function;
