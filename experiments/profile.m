/* run through all of the 4-polytopes we have found and profile them */

q := 11;  load "~/MagmaPackages/SGGI/data/PSp4/poly11.m";

G := MyOmega (5, q);
isit, f, g := RecogniseSp4 (G, q);   assert isit;
H := sub < GL (4, q) | SpH_polys[1] >;
isit, a, b := RecogniseSp4 (H, q);   assert isit;
polys := [ ];
for t in SpH_polys do
    tt := [ (t[i] @ a) @ g : i in [1..#t] ];
    Append (~polys, tt);
end for;
S := Set ([ SchlafliSymbol (t) : t in polys ]);
rpolys := [ ];
for s in S do
   assert exists (t){u : u in polys | SchlafliSymbol (u) eq s};
   Append (~rpolys, t);
end for;

V := VectorSpace (GF (q), 5);
Q := Identity (MatrixAlgebra (GF (q), 5));
for i in [1..#rpolys] do
"processing polytope", i, "out of", #rpolys;
  t := rpolys[i];
"Schlafli symbol:", SchlafliSymbol (t);
  L := sub < G | [ t[i] : i in [1,2,3] ] >;
  R := sub < G | [ t[i] : i in [2,3,4] ] >;
  ML := GModule (L);
  iML := IndecomposableSummands (ML);
  MR := GModule (R);
  iMR := IndecomposableSummands (MR);
  iVL := [ sub < V | [ V!(ML!(N.i)) : i in [1..Ngens (N)] ] > : N in iML ];
  iVR := [ sub < V | [ V!(MR!(N.i)) : i in [1..Ngens (N)] ] > : N in iMR ];
"  left and right decomposition data:";
  for j in [1..#iVL] do
      UL := iVL[j];
      "    * left", j, "has dim", Dimension (UL), "and W.I.", 
      MyWittIndex (Q, UL), "meets:";
      for k in [1..#iVR] do
          UR := iVR[k];
          "      ** right", k, "of dim", Dimension (UR), "and W.I.", 
          MyWittIndex (Q, UR), "in dim", Dimension (UL meet UR), "and W.I.",
          MyWittIndex (Q, UL meet UR);
          if Dimension (UL meet UR) eq 2 then 
              Z := UL meet UR;
          "          ( LINE TYPE:", IdentifyLineType (Q, Z), ")";
          end if;
          "  ";
      end for;
      "    -----------";
  end for;
"  commuting involution data:";
  for j in [1,2] do
      x := t[j];
      xEp := Eigenspace (x, 1);
      xEm := Eigenspace (x, -1);
      for k in [j+2..4] do
          y := t[k];
          yEp := Eigenspace (y, 1);
          yEm := Eigenspace (y, -1);
          "    * j =", j, "  k =", k;
          "    * dim(xEp) =", Dimension (xEp);
          "      ** dim(yEp) =", Dimension (yEp), ":  dim(xEp ^ yEp) =", Dimension (xEp meet yEp),
          "W.I.", MyWittIndex (Q, xEp meet yEp);
          "      ** dim(yEm) =", Dimension (yEm), ":  dim(xEp ^ yEm) =", Dimension (xEp meet yEm),
          "W.I.", MyWittIndex (Q, xEp meet yEm);
          "    * dim(xEm) =", Dimension (xEm);
          "      ** dim(yEp) =", Dimension (yEp), ":  dim(xEm ^ yEp) =", Dimension (xEm meet yEp),
          "W.I.", MyWittIndex (Q, xEm meet yEp);
          "      ** dim(yEm) =", Dimension (yEm), ":  dim(xEm ^ yEm) =", Dimension (xEm meet yEm),
          "W.I.", MyWittIndex (Q, xEm meet yEm);   
          "   ";      
      end for;
   end for;
"=============";
"   ";
"   ";
"   ";
end for;


__CommutingInvolutionInfo := function (d, q)
  go := MyGO (d, q);
  Q := Identity (MatrixAlgebra (GF (q), d));
  om := MyOmega (d, q);
  I := __Omega_InvClassReps (d, q);
  for i in [1..#I] do
  "processing involution", i;
  "  1-eigenspace has dimension", I[i][2][1], "and Witt index", I[i][2][2];
  "  -1-eigenspace has dimension", I[i][3][1], "and Witt index", I[i][3][2];
      Eip := Eigenspace (I[i][1], 1);
      Eim := Eigenspace (I[i][1], -1);
      C0 := Centralizer (go, I[i][1]);
      C := Centralizer (om, I[i][1]);
      cl := ConjugacyClasses (C);
      icl := [ c[3] : c in cl | c[1] eq 2 ];
      J := [ x : x in icl | not IsScalar (x) and x ne I[i][1] ];
      "  there are", #J, "non-scalar C-classes of involutions in Omega..."; 
flag := exists { <a,b> : a in J, b in J | (a ne b) and IsConjugate (C0, a, b) };
if flag then
"  ...but some of these are fused in C0";
else
"  ...and these are all distinct C0-classes";
end if;
"  ---------------";
      for j in [1..#J] do
      "      processing involution", j;
      "   ";
          rho := J[j];
          Erp := Eigenspace (rho, 1);
          "      1-eigenspace has dimension", Dimension (Erp), "and Witt index", 
              MyWittIndex (Q, Erp);
          "      int w/ Eip has dimension", Dimension (Erp meet Eip), "and Witt index", 
              MyWittIndex (Q, Erp meet Eip);
          "      int w/ Eim has dimension", Dimension (Erp meet Eim), "and Witt index",
              MyWittIndex (Q, Erp meet Eim);
          "   ";
          Erm := Eigenspace (rho, -1);
          "      -1-eigenspace has dimension", Dimension (Erm), "and Witt index", 
              MyWittIndex (Q, Erm);
          "      int w/ Eip has dimension", Dimension (Erm meet Eip), "and Witt index",
              MyWittIndex (Q, Erm meet Eip);
          "      int w/ Eim has dimension", Dimension (Erm meet Eim), "and Witt index",
              MyWittIndex (Q, Erm meet Eim); 
          "      -------------";         
      end for;
  "==========";
  end for;
return true;
end function;


