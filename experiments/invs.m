/* geometric properties of involutions in O(V) */
__GO_InvClassReps := function (d, q)
  G := MyGO (d, q);
  Q := Identity (MatrixAlgebra (GF (q), d));
  cl := ConjugacyClasses (G);
  icl := [ c : c in cl | c[1] eq 2 ];
  R := [ c[3] : c in icl ];
  info := [ ];
  for i in R do
      Ep := Eigenspace (i, 1);
      Em := Eigenspace (i, -1);
      Append (~info, < i , [ Dimension (Ep) , MyWittIndex (Q, Ep) ] , 
                           [ Dimension (Em) , MyWittIndex (Q, Em) ] >);
  end for;
return info;
end function;

__SO_InvClassReps := function (d, q)
  G := MySO (d, q);
  Q := Identity (MatrixAlgebra (GF (q), d));
  cl := ConjugacyClasses (G);
  icl := [ c : c in cl | c[1] eq 2 ];
  R := [ c[3] : c in icl ];
  info := [ ];
  for i in R do
      Ep := Eigenspace (i, 1);
      Em := Eigenspace (i, -1);
      Append (~info, < i , [ Dimension (Ep) , MyWittIndex (Q, Ep) ] , 
                           [ Dimension (Em) , MyWittIndex (Q, Em) ] >);
  end for;
return info;
end function;

__Omega_InvClassReps := function (d, q)
  G := MyOmega (d, q);
  Q := Identity (MatrixAlgebra (GF (q), d));
  cl := ConjugacyClasses (G);
  icl := [ c : c in cl | c[1] eq 2 ];
  R := [ c[3] : c in icl ];
  info := [ ];
  for i in R do
      Ep := Eigenspace (i, 1);
      Em := Eigenspace (i, -1);
      Append (~info, < i , [ Dimension (Ep) , MyWittIndex (Q, Ep) ] , 
                           [ Dimension (Em) , MyWittIndex (Q, Em) ] >);
  end for;
return info;
end function;

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


