/*
  Some standard functions to compute with SGGIs
*/

intrinsic CoxeterMatrix (T::SeqEnum[RngIntElt]) -> Mtrx
  {The Coxeter matrix for a reflection group from its Schlafli type}

  n := 1 + #T;
  M := Matrix (Integers (), n, n, [ 2 : i in [1..n^2] ]);
  for i in [1..n-1] do
      M[i][i] := 1;
      M[i][i+1] := T[i];
      M[i+1][i] := T[i];
  end for;
  M[n][n] := 1;
  assert IsCoxeterMatrix (M);
return M;
end intrinsic;


intrinsic Simplex (n::RngIntElt) -> SGGI
  {The n-simplex as an SGGI.}
  SYM := SymmetricGroup (n+1);
  gens := [ SYM!(i, i+1) : i in [1..n] ];
  G := sub < SYM | gens >;
  H := StringGroupGeneratedByInvolutions (G);
  H`HasIP := true;
return H;
end intrinsic;



// rank reduction via Petrie-like constructions
intrinsic LeftPetrie (H::SGGI) -> SGGI
  {The reduced rank SGGI obtained from H by the (left) Petrie-like construction.}
  require Rank (H) gt 3 : "the rank of H must be at least 4";
  G := H`AsGrp;
  gens := [ H`DistGens[2] , H`DistGens[1] * H`DistGens[3] ] cat [ H`DistGens[i] : i in [4..Rank (H)] ];
  GG := sub < G | gens >;
  J := StringGroupGeneratedByInvolutions (GG);
  if assigned H`HasIP then   // see if we can readily see that J satisfies the IP
      if H`HasIP then
          D := sub < GG | GG.1 , GG.2 >;
          if H`DistGens[1] in D then
              J`HasIP := true;
          end if;
      end if;
  end if;
return J;
end intrinsic;


intrinsic RightPetrie (H::SGGI) -> SGGI 
  {The reduced rank SGGI obtained from H by the (right) Petrie-like construction.}
  require Rank (H) gt 3 : "the rank of H must be at least 4"; 
  J := Dual (H);
  J := LeftPetrie (J);
return Dual (J);
end intrinsic;


intrinsic ModularReflectionGroup (T::SeqEnum[RngIntElt], p::RngIntElt) -> SGGI
  {The SGGI obtained by reducing the string reflection group of Schlafli type T modulo prime p.}
  require IsPrime (p) and (p gt 2) : "p must be an odd prime";
  M := CoxeterMatrix (T);
  G0 := ReflectionGroup (M);
  require IsCrystallographic (G0) : "T must define a crystallographic Coxeter group";
  assert Degree (G0) eq (1 + #T);
  G := sub < GL (Degree (G0), p) | [ GL (Degree (G0), p)!(G0.i) : i in [1..Ngens (G0)] ] >;
return StringGroupGeneratedByInvolutions (G);
end intrinsic;