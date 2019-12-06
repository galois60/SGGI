n := 7;
G := SymmetricGroup (n);
polys := [* *];

/* 
    makeshift isomorphism tester for symmetric groups
    for n > 6, Aut(S_n) = S_n

    when the generic iso tester is built hardwire it 
    into search functions.
*/

ISO := function (H1, H2)
    assert Group (H1) eq Group (H2);
    n := Degree (Group (H1));
    X1 := Generators (H1);
    X2 := Generators (H2);
    flag := exists (g){ y : y in SymmetricGroup (n) | 
                        forall {i : i in [1..#X1] | X1[i]^y eq X2[i] } };
    if flag then
        return true, g;
    else 
        return false, _;
    end if;
end function;

__clean := function (L)
  CL := [ L[1] ];
  for i in [2..#L] do
    H2 := L[i];
    if not exists {H1 : H1 in CL | ISO (H1, H2) or ISO (Dual(H1), H2)} then
      Append (~CL, H2);
    end if;
  end for;
return CL;
end function;

/*
for r in [3..n-1] do
"r =", r;
    L := AllStringCReps (G, r);
    "  raw:", #L;
    CL := __clean (L);
    "  filtered:", #CL;
    Append (~polys, CL);
"-----------";
end for;
*/

// plan: separate the polys of a fixed rank that cannot be
// inflated from those that can; do this by reducing down 
// and seeing which ones get hit.
// do we notice anything obvious that distinguishes the sets?

// quick timing comparison ...
n := 10;
SYM := SymmetricGroup (n+1);
gens := [ SYM!(i, i+1) : i in [1..n] ];
G := sub < SYM | gens >;
tt := Cputime ();
//assert IsStringCGroup (G);
//"magma function time:", Cputime (tt);
H := StringGroupGeneratedByInvolutions (G);
tt := Cputime ();
assert IsStringCGroup (H);

// magma functions burn through memory quickly