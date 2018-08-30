intrinsic Involutions (G::Grp) -> SeqEnum
  {Given a group, return all of its involutions.}
  cl := ConjugacyClasses (G);
  icl := [ c : c in cl | c[1] eq 2 ];
  I := &join [ Conjugates (G, c[3]) : c in icl ];
return [ i : i in I ];
end intrinsic;


intrinsic WhichClass (G::GrpMat, C::SeqEnum, x::GrpMatElt) -> RngIntElt
  {Given a list of G class reps decide which one x belongs to, if any.}
  if exists (j){i : i in [1..#C] | IsConjugate (G, C[i], x)} then
       return j;
  else 
       return 0;
  end if;
end intrinsic;


intrinsic WhichClass (G::GrpPerm, C::SeqEnum, x::GrpPermElt) -> RngIntElt
  {Given a list of G-classes decide which one x belongs to, if any.}
  if exists (j){i : i in [1..#C] | IsConjugate (G, C[i][3], x)} then
       return j;
  else 
       return 0;
  end if;
end intrinsic;
