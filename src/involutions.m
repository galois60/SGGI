intrinsic Involutions (G::Grp) -> SeqEnum
  {Given a group, return all of its involutions.}
  cl := ConjugacyClasses (G);
  icl := [ c : c in cl | c[1] eq 2 ];
  I := &join [ Conjugates (G, c[3]) : c in icl ];
return [ i : i in I ];
end intrinsic;


intrinsic IsDihedral (G::Grp) -> SeqEnum
  {Given a group, decide if it is dihedral.}
  n := #G;
  if n mod 2 eq 1 then return false, _, _; end if;
  I := Involutions (G);
  isit := exists (i){ k : k in I | exists { x : x in Generators (G) | (k,x) ne Identity (G) } };
  isit := exists (j){ k : k in I | Order (i*k) eq n div 2 };   
  if not isit then return false, _, _; end if;
  assert sub<G|i,j> eq G;
return true, i, j;
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


intrinsic ClassProfile (G::Grp, R::SeqEnum, T::SeqEnum) -> SeqEnum 
  { Given a list R of G-conjugacy class representatives, and a list
    T of elements of G, return the positions of the elements of R
    to which elements of T are G-conjugate. }
  pos := [ ];
  for i in [1..#T] do
      flag, n := WhichClass (G, R, T[i]);
      require flag : "elements of T must be conjugate to reps in R";
      Append (~pos, n);
  end for;   
return pos;
end intrinsic;


// given H acting by conjugation on class, return reps of H-classes
intrinsic RefineClass (H::Grp, C::SeqEnum) -> SeqEnum
  { Replace the H-invariant list C with a (possibly) smaller list 
    of representatives under the H-action. }
     if #C eq 0 then 
         return [ ];
     end if;
     assert exists (r){ s : s in C };
     ref := [ r ];
     nclass := Conjugates (H, r);
     while #nclass lt #C do
         assert exists (r){ s : s in C | not s in nclass };
         nclass join:= Conjugates (H, r);
         Append (~ref, r);
     end while;
return ref;
end intrinsic;

intrinsic OrbitReps (G::Grp, S::Set) -> SeqEnum, SeqEnum
  { Given a group G acting on a set S, find representatives of G-orbits };
  if #S eq 0 then
       return [ ];
  end if;
  assert exists (s){ x : x in S };
  R := [ s ];
  T := Orbit (G, s);
  sizes := [ #T ];
  while #T lt #S do
       assert exists (s){ x : x in S | not x in T };
       O := Orbit (G, s);
       T join:= O;
       Append (~R, s);
       Append (~sizes, #O);
  end while;
return R, sizes;
end intrinsic;

