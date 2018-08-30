/* code for reflection groups lifted from sequence of three papers */

SchlafliSymbolToCoxeterMatrix := function (T)
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
end function;

PI := [ n : n in [5..13] | IsPrime (n) ];


k := 1;
l := 3;
m := 2;
T := [ 3 : i in [1..k] ] cat [ 0 : i in [1..l] ] cat [ 3 : i in [1..m] ];


//T := [4,3,3,3,3,4];
n := 1 + #T;

M := SchlafliSymbolToCoxeterMatrix (T);
G := ReflectionGroup (M);

SanityCheck := false;
"T =", T;

p := 7;

//for p in PI do
  "   ";
  "p =", p;
  "comp facs of GO:"; CompositionFactors (GO (n, p));
  Gp := sub < GL (n, p) | [ GL (n, p)!(G.i) : i in [1..Ngens (G)] ] >;
  "   ";
  "comp facs of Gp:"; CompositionFactors (Gp);
  "Schlafli type of Gp:", SchlafliSymbol ([ Gp.i : i in [1..Ngens (Gp)] ]);
  "   ";
  "comp facs of left factor:";
  CompositionFactors (sub<Generic (Gp)|[Gp.i : i in [1..Ngens (Gp) - 1]]>);
  "   ";
  "comp facs of right factor:";
  CompositionFactors (sub<Generic (Gp)|[Gp.i : i in [2..Ngens (Gp)]]>);
  "   ";
  assert IsStringGroup ([ Gp.i : i in [1..Ngens (G)] ]);
  if IsIrreducible (Gp) then
      flag, type, B := OrthogonalForm (Gp);
      assert flag;
      "  type:", type;
      "B =", B;
      // pin Gp down
      "    subgp of ker(det)?", 
         forall { i : i in [1..Ngens (Gp)] | Determinant (Gp.i) eq 1 };
      "    subgp of ker(spinor)?", 
         forall { i : i in [1..Ngens (Gp)] | SpinorNorm (Gp.i, B) eq 0 };
  else
      "    Gp is not acting irreducibly";
  end if;
  
  if n mod 2 eq 1 then
      N := #GO(n,p);
  elif type eq "orth+" then
      N := #GOPlus(n,p);
  else
      N := #GOMinus(n,p);
  end if;
  
  if SanityCheck then
      "    index in GO:", N div LMGOrder (Gp);  
      assert IsStringCGroup ([ Gp.i : i in [1..Ngens (G)] ]);
  end if;
  "----------------------";
//end for;


