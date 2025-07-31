/* a first attempt at a rank inflation function for SGGIs */

intrinsic PetrieInflation (H:SGGI) -> SeqEnum
  {All increased rank SGGIs obtained from H by reversing the Petrie-like construction.}
  G := Group (H);
  assert Ngens (G) gt 2;
  P := sub < G | [ G.i : i in [2..Ngens (G)] ] >;
  C := Centraliser (G, P);
  IC := Involutions (C);
  R0 := [ i : i in IC | (i, G.1) ne Identity (G) ];
  L := [ ];
  for r0 in R0 do
       r2 := G.2 * r0;
       X := sub < G | [ r0 , G.1 , r2 ] cat [ G.i : i in [3..Ngens (G)] ] >;
       assert X eq G;
       Append (~L, StringGroupGeneratedByInvolutions (X));
  end for;
return L;
end intrinsic;

