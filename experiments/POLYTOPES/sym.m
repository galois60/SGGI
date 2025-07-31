/* 
  Experiment to see which string C-group representations of Sym(n)
  are not rank-reducible, which a not rank-inflatable, and which
  are neither.

  Define the following terms:
     ISLAND = any SGGI that isn't a reduction and cannot be reduced
     ROOT = any SGGI of rank [3..n-3] that isn't a reduction
     LEAF = any SGGI of rank [4..n-2] that does not reduce
     NORMAL = all remaining SGGIs
*/

__Process := function (S)
  N := {@ @};   // the normal SC-reps
  I := {@ @};   // the islands
  R := {@ @};   // the roots
  L := {@ @};   // the leaves
  // set up the loop variables
  A := IndexedSet (S[1]);   // all nodes on level 1 are aliens
  C := {@ @};               // no nodes on level 1 are children
  i := 1;
  while i lt #S do
    C_new := {@ @};
    T := IndexedSet (S[i+1]);
    // process first the children on level i
    for H in C do
      // consider the two reductions of H
      HL := LeftPetrie (H);
      HR := RightPetrie (H);
      Lflag := (#Group(HL) eq #Group(H)) and HasIntersectionProperty (HL);
      Rflag := (#Group(HR) eq #Group(H)) and HasIntersectionProperty (HR);
      if Lflag then   
          assert exists (J){ K : K in T | IsEquivalent (HL, K) };
          Include (~N, H);
          Include (~C_new, J);
      end if;
      if Rflag then   
          assert exists (J){ K : K in T | IsEquivalent (HR, K) };
          Include (~N, H);
          Include (~C_new, J);
      end if;
      if (not Lflag) and (not Rflag) then
          Include (~L, H);
      end if;
    end for;
    // now process the aliens on level i
    for H in A do
      HL := LeftPetrie (H);
      HR := RightPetrie (H);
      Lflag := (#Group(HL) eq #Group(H)) and HasIntersectionProperty (HL);
      Rflag := (#Group(HR) eq #Group(H)) and HasIntersectionProperty (HR);
      if Lflag then   
          assert exists (J){ K : K in T | IsEquivalent (HL, K) };
          Include (~R, H);
          Include (~C_new, J);
      end if;
      if Rflag then   
          assert exists (J){ K : K in T | IsEquivalent (HR, K) };
          Include (~R, H);
          Include (~C_new, J);
      end if;
      if (not Lflag) and (not Rflag) then
          Include (~I, H);
      end if;
    end for;
    C := C_new;
    A := T diff C;
    i +:= 1;
  end while;

  // now classify the rank 3 SC-reps into "normal" and "islands"
  T := IndexedSet (S[#S]);
  N join:= C;
  I join:= (T diff C);

return I, L, N, R;
end function;


n := 7;
G := SymmetricGroup (n);
ALL := [ AllStringCReps (G, r) : r in [n-2..3 by -1] ];
assert #ALL[1] eq 1;


