/* 
  Constructions from the article:
    
  On chiral polytopes having a group PSL(3,q) as automorphism group
  
  by Dimitri Leemans and Adrien Vandenschrick
*/

Q := [ m : m in [5..50] | #Factorization (m) eq 1 ];

Rank4 := function (G, PG, f)
  F := BaseRing (G);
  x := PrimitiveElement (F);
     s1 := G![  x,  1,  0,
                0, 1+x^-1, -x^-1,
                0,  1,  0  ];
     s2 := G![ -x^-1, 0, 0,
                0,   0, 1,
                0,   x, 0  ];
     s3 := G![  x,     0,  0,
              x-x^-1,  1,  0,
              x-x^-1,  0, x^-1 ];
  X := sub < PG | [ s1 @ f, s2 @ f, s3 @ f] >;
  assert X eq PG;
  assert IsCPlusGroup (X);
  "Schlafli type of X:", [ Order (X.i) : i in [1..Ngens (X)] ];
return X;
end function;

Rank5 := function (G, PG, f, k, i)
  F := BaseRing (G);
  p := Characteristic (F);
  assert (p eq #F) and ((p-1) mod 6 eq 0);
  x := PrimitiveElement (F);
  w := x^((p-1) div 3);
  assert w ne 1 and w^3 eq 1;
     s1 := G![  1,  0,  0,
                0, w^i, 0,
                0,  0, w^(2*i) ];
     s2 := G![ -1, 0, -k,
                0, -w^(2*i), -k*w^(2*i),
                0,   0,  w^i  ];
     s3 := G![  1,  k,  0,
                0,  k,  1,
                0, -1, 0 ];
     s4 := G![  0,  1,  0,
                0,  0,  1,
                1,  0,  0 ];
  X := sub < PG | [ s1 @ f , s2 @ f , s3 @ f , s4 @ f ] >;
  assert X eq PG;
  assert IsCPlusGroup (X);
  "Schlafli type of X:", [ Order (X.i) : i in [1..Ngens (X)] ];
return X;
end function;

// checks the automorphism condition for C+ groups
CheckAuto := function (G)
  A := AutomorphismGroup (G);
end function;

for q in Q do
  "q =", q;
  F := GF (q);
  G := SL(3,F);
  PG, f := ProjectiveGroup (G);
  "rank 4 construction ...";
  H := Rank4 (G, PG, f);
  "...ok";
  "   ";
  if IsPrime (q) and ((q-1) mod 6 eq 0) then
  "rank 5 constructions ...";
  H1 := Rank5 (G, PG, f, 1, 1);
  H2 := Rank5 (G, PG, f, -1, 1);
  "   ";
  end if;
  "----------";
end for;