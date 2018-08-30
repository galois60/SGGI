/* Witt index test */

//for e in [2..16] do
/*
e := 4;
n := 2; 
d := 2 * n;
q := 2^e;
F := GF (q);
Ft := [ a : a in F | a ne 0 ];
T := { a + 1/a : a in Ft };
T := [ a : a in T | a ne 0 ];

assert { a : a in Ft | (q+1) mod Order (GL (2,F)![1,a,a,1+a^2]) eq 0 } 
eq { a : a in Ft | not a in T };

Fnice := [ a : a in Ft | Order (GL (2,F)![1,a,a,1+a^2]) eq q+1 ];
"there are", #Fnice, "good field elements out of a total of", #Ft;
"ratio of", RealField (20)!(#Fnice / #Ft);
"----";
//end for;
*/

/* calculation check */
/*
X := CartesianProduct ([ Fnice : i in [1..d-1] ]);
//"|X| =", #X;
Y := [ x : x in X | x[1] ne x[2] ];
K := { y[1] * y[3] / (y[1] + y[2]) : y in Y };
"e =", e;
"|Ft| =", #Ft;
"|K| =", #K;
"------";
end for;
*/

/* another check */
/*
for a in Fnice do
  for b in Fnice do
    Q := __QuadraticForm ([a, a, b]);
    V := QuadraticSpace (Q);
    assert WittIndex (V) eq 1;
  end for;
end for;
"done";
*/

/*
total := 0;
W1 := 0;
W2 := 0;
for x in X do
  if x[1] ne x[2] then
    Q := __QuadraticForm ([ b : b in x]);
    V := QuadraticSpace (Q);
    if WittIndex (V) eq 1 then W1 +:= 1; else W2 +:= 1; end if;
    U := sub < V | V.1 , V.2 >;
    W := OrthogonalComplement (V, U);
    assert W eq sub < V | x[2] * V.1 + x[1] * V.3 , V.4 >;
    W := VectorSpaceWithBasis (
       [ (x[2]/(x[1]+x[2])) * V.1 + (x[1]/(x[1]+x[2])) * V.3 , V.4 ]
                              );
    QW := RestrictQuadraticForm (Q, W);
    assert QW[1][2] eq x[1] * x[3] / (x[1] + x[2]);
    total +:= 1;
  end if;
end for;
"Witt index 1:", W1;
"Witt index 2:", W2;
"total =", total;
*/


// try building forms where all scalars are the same
/*
for a in Fnice do
  Q0 := __QuadraticForm ([ a : i in [1..d-1] ]);
  V0 := QuadraticSpace (Q0);
  "Q0 =", Q0;
  "has Witt index", WittIndex (V0);
  assert exists (b){ x : x in Fnice | x ne a };
  Q1 := __QuadraticForm ([ a^(2^i) : i in [0..d-2] ]);
  V1 := QuadraticSpace (Q1);
  "Q1 =", Q1;
  "has Witt index", WittIndex (V1);
  "---------";
end for;
*/

// build all quadratic forms on F^4 and find their Witt indices
/*
a := Fnice[1];
X := CartesianProduct (Fnice, Fnice);
for x in X do
  b := x[1]; c := x[2];
  Q := __QuadraticForm ([a,b,c]);
  V := QuadraticSpace (Q);
  "Q =", Q;
  "has Witt index", WittIndex (V);
  "---------";
end for;
*/

/*
b := a;
for c in Fnice do
  Q := __QuadraticForm ([a,b,c]);
  V := QuadraticSpace (Q);
  "Q =", Q;
  "has Witt index", WittIndex (V);
end for;
*/

/*
for a in Ft do
  Q := __QuadraticForm ([a]);
  V := QuadraticSpace (Q);
  "Q =", Q;
  "has Witt index", WittIndex (V);
  "----------";
end for; 
*/

/*
"d =", d;
"F =", F;
def1 := [ ];
def2 := [ ];
for a in Ft do
  for b in Ft do
    Q := __QuadraticForm ([a,b,1]);
    V := QuadraticSpace (Q);
    e := V.1 + V.3;
    f := V.1 + V.4;
    assert QuadraticNorm (e) eq 0;
    assert QuadraticNorm (f) eq 0;
    assert InnerProduct (e, f) eq 1;
    U := sub<V|e,f>;
    W := PerpSpace (Q + Transpose(Q), U);
    "Q restricted to perp space:", RestrictQuadraticForm (Q, W);
    "  ";
  end for;
end for;
*/


/*
"Witt defects of type 1 spaces:", def1;
"Q1 =", Q1;
"Witt defects of type 2 spaces:", def2;
"Q2 =", Q2;
*/

__Count := function (K, m)
  C := CartesianProduct ([ [ a : a in K | a ne 0 ] : i in [1..2*m-1] ]);
  cp := 0;
  cm := 0;
  for c in C do
     Q := __QuadraticForm (c);
     V := QuadraticSpace (Q);
     if WittIndex (V) eq m then
        cp +:= 1;
     else
        assert WittIndex (V) eq m-1;
        cm +:= 1;
     end if;
  end for;  
return #C, cp, cm;
end function;


__Maximal := function (K, pm)
  V := VectorSpace (K, 3);
  if pm eq 1 then
      X := __FieldElementsPlus (K);
  else
      X := __FieldElementsMinus (K);
  end if;
  Q := __QuadraticForm ([ Random (X) , Random (X) ]);
"Q =", Q;
  G := SigmaGroup (Q, V);
"composition factors of G:";
CompositionFactors (G);
  D := sub < G | [ Symmetry (V.i, Q) : i in [1,2] ] >;
"|D| =", #D;
return IsMaximal (G, D);
end function;


__CheckBill := function (Q, K)
  V := QuadraticSpace (Q);
  d := Dimension (V);
  m := d div 2;
  B := InnerProductMatrix (V);
  assert B eq Q + Transpose (Q);
  C := TransformForm (B, "symplectic");
  D := C^-1;
  A, phi := AdditiveGroup (K);
  N := sub < A | [ (x^2 + x) @@ phi : x in K ] >;
  AA, pi := A / N;
  assert Order (AA) eq 2;
//  [ a @ pi : a in A ];
  Arf := A!0;
  for i in [1..m] do
      x := QuadraticNorm (V!(D[i])) * QuadraticNorm (V!(D[d+1-i]));
      assert x in K;
      Arf +:= x @@ phi;
  end for;
  Arf := Arf @ pi;
  flag := ((Arf eq Identity (AA)) and (ArfInvariant (V) eq 0)) or
          ((Arf ne Identity (AA)) and (ArfInvariant (V) eq 1));
return flag;
end function;

CheckBill := function (K, m)
  C := CartesianProduct ([ [ a : a in K | a ne 0 ] : i in [1..2*m-1] ]);
"checking", #C, "quadratic forms";
  flag := true;
  for c in C do
      Q := __QuadraticForm (c);
      flag and:= __CheckBill (Q, K);
  end for;
return flag;
end function;


__ArfInvariant := function (S, K)
  Q := __QuadraticForm (S);
  V := QuadraticSpace (Q);
  m := Dimension (V) div 2;
"Arf(V) =", ArfInvariant (V);
  N := { a^2 + a : a in K };
  assert #N * 2 eq #K;
  arf := 1 / S[1];
  for i in [2..m] do
      arf +:= (1 + S[2*i-2] / S[2*i-3]) / S[2*i-1];
  end for;
  if arf in N then
      __arf := 0;
  else
      __arf := 1;
  end if;
"__arf(Q) =", __arf;
return __arf eq ArfInvariant (V);
end function;


CheckPete := function (K, m)
  Ktimes := [ x : x in K | x ne 0 ];
  A, phi := AdditiveGroup (K);
  N := sub < A | [ (x^2 + x) @@ phi : x in K ] >;
  AA, pi := A / N;
  assert Order (AA) eq 2;
  PLUS := [ y @ phi : y in N | y @ phi ne 0 ];
  MINUS := [ x : x in K | not x in PLUS ];
  flag := true;
  for x in PLUS do
      for z in Ktimes do
          Q := __QuadraticForm ([ x : i in [1..2*(m-1)] ] cat [z]);
          V := QuadraticSpace (Q);
if ArfInvariant (V) ne 0 then
Q:Magma;
end if;
          flag and:= (ArfInvariant (V) eq 0);
      end for;
  end for;
return flag;
end function;

Lemma_4_7 := function (k, m)
  d := 2 * m;
  K := GF (2^k);
  N := { a^2 + a : a in K };
  K_times := [ a : a in K | a ne 0 ];
  flag := true;
  for a in K_times do
      for b in K_times do
          S := [a, a] cat [b : i in [1..d-3]];
          Q := __QuadraticForm (S);
          V := QuadraticSpace (Q);
          c := 1/a + (Binomial(m+1,2) - 1) * 1/b;
          flag and:= (((ArfInvariant (V) eq 0) and (c in N)) or
                     ((ArfInvariant (V) eq 1) and (not c in N)));
      end for;
  end for;
return flag;  
end function;

__check := function (q)
  K := GF (q);
  N := { a^2 + a : a in K };
  A := [ a : a in K | (a ne 0) and (not 1/a in N) ];
  bad := [ ];
  for a in A do
      Q := __QuadraticForm ([a]);
      V := QuadraticSpace (Q);
      assert (((ArfInvariant (V) eq 0) and (1/a in N)) or  
              ((ArfInvariant (V) eq 1) and (not 1/a in N)));
      h := GL (2, K)![1,a,a,1+a^2];
      assert (q+1) mod Order (h) eq 0;
      if Order (h) ne (q+1) then Append (~bad, a); end if;
  end for;
//  "divisors of q+1:", Divisors (q+1);
  "|A| =", #A, "   |bad| =", #bad;
  R := RealField (10);
  "|good| / |A| =", R!((#A-#bad) / #A);
  "|phi(q+1)| / q =", R!(EulerPhi (q+1) / q);
return bad;
end function;


__test := function (m, s, t)
  d := 2 * m;
  forms := [ ];
  arfs := [ ];
  C := CartesianPower ([s, t], d-1);
  for c in C do
      Q := __QuadraticForm (c);
      V := QuadraticSpace (Q);
      Append (~forms, Q);
      Append (~arfs, ArfInvariant (V));
  end for;
return arfs, forms;
end function;


__torus := function (a)
return GL (2, Parent (a))![1,a,a,1+a^2];
end function;

for k in [2..10] do
  q := 2^k;
  K := GF (q);
  N := { a^2 + a : a in K };
  A0 := [ a : a in K | (a ne 0) and (not 1/a in N) ];
  A := [ a : a in A0 | Order (__torus (a)) eq q+1 ];
n := #[ <x,y> : x in A, y in A | x/y^2 eq 1/(A[1]) ];
  assert 2 * #A eq EulerPhi (q+1);
  X := { x / y^2 : x in A, y in A };
  "|K^{times}| =", 2^k-1;"     |X| =", #X, "    |A|^2/n =", (#A)^2 / n;
  "----------";  
end for;

Phi1 := function (m, s, t)
    Q := __QuadraticForm ([s : i in [1..2*m-1]]);
    V := QuadraticSpace (Q);
return V, Q;
end function;

Phi2 := function (m, s, t)
    Q := __QuadraticForm ([s] cat [t:i in [1..2*m-3]] cat [s]);
    V := QuadraticSpace (Q);
return V, Q;
end function;



