// NEEDS WORK: MODIFY USING NEW NAMES AND INPUTS OF SGGI PROPERTIES

/*
  This subroutine is designed for use in a parallel search.
  Given:
    <G> a group
    <TUPLES> a list of r-tuples generating string C subgroups of <G>
             of rank r.
    <INVS> a subset of the set of involutions of <G>
  Find: all extensions of all elements of <TUPLES> to string C
        subgroups of <G> of rank r+1.
*/
__Extend_Rank := function (G, TUPLES, INVS)
     if #TUPLES eq 0 then
         return [ ];
     end if;
     s := #TUPLES[1];
     NTUPS := [ ];
     for i in [1..#TUPLES] do
         T := TUPLES[i];
         L := sub < G | T >;
         // find eligible involutions
         TINVS := [ j : j in INVS |
                        not j in L and
                        forall { a : a in [1..s-1] | (T[a], j) eq Identity (G) }
                        and (j, T[s]) ne Identity (G) ];
         // refine class under the centraliser of <L> in <G>
         CL := Centraliser (G, L);
         TINVS := RefineClass (CL, TINVS);
         // see which of them will satisfy the intersection condition
         for j in TINVS do
                 if forall { a : a in [2..s] | 
                                 L meet sub < G | [ T[b] : b in [a..s] ] cat [ j ] > 
                                 eq  sub < G | [ T[b] : b in [a..s] ] > } then
                      Append (~NTUPS, T cat [j]);
                 end if;   
         end for;
     end for;
return NTUPS;
end function;


/*
  Given a group G and a rank r, this function finds all r-tuples
  of involutions that generate G as a string C-group of rank r.
  
  Optional input: if <ICReps> is specified, then the search for 
  string C-group generating sequences is restricted to conjugates
  of elements in <ICReps>. If it is not specified, then the function
  will consider all possible involutions by first computing 
  conjugacy classes.
  
  Optional input: a sanity check that the output sequences are indeed
  string C sequences.
*/

__ExhaustiveSearch := function (G, r : ICReps := [ ] , SanityCheck := false)

     /* if no involution class reps are specified, compute them all */
     if ICReps eq [ ] then
         tt := Cputime ();
         classes := ConjugacyClasses (G);
         iclasses := [ c : c in classes | c[1] eq 2 ];
         ICReps := [ c[3] : c in iclasses ];
         /* remove central elements */
         ICReps := [ r : r in ICReps | not forall { v : v in [1..Ngens (G)] |
                                            (G.v, r) eq Identity (G) } ];
     end if;

     assert forall { j : j in ICReps | j in G and Order (j) eq 2 };
     
     /* we list the union of conjugacy classes of involutions */
     INVS := &join [ Conjugates (G, r) : r in ICReps ];
     
     /* form all (conjugacy classes of) strings of length 3 */
     TRIPS := [ ];
     for a in [1..#ICReps] do
     
         i0 := ICReps[a];
     
         /* list i2 commuting with i0 up to C(i0)-conjugacy */
         tt := Cputime ();
         C0 := Centraliser (G, i0); 
         I2 := [ j : j in INVS | (i0, j) eq Identity (G) and i0 ne j ];
         R2 := RefineClass (C0, I2);
         
         for i2 in R2 do
     
            /* list i1 not commuting with i0, i2 up to C(i0,i2)-conjugacy */
            D02 := sub < G | i0, i2 >;
            C02 := Centraliser (G, D02);
            I1 := [ j : j in INVS | (i0, j) ne Identity (G) 
                                and (i2, j) ne Identity (G) ];    
            R1 := RefineClass (C02, I1);
            GOOD1 := [ j : j in R1 | #(sub<G|i0,j> meet sub<G|i2,j>) eq 2 ];
            TRIPS cat:= [ [ i0 , i1 , i2 ] : i1 in GOOD1 ]; 
     
         end for;
     
     end for;
     
     TUPLES := TRIPS;
     
     if (r gt 3) then
     
         /* see if we can extend to string gps of higher rank */
         s := 3;     
         while (s lt r) do
             TUPLES := __Extend_Rank (G, TUPLES, INVS);
             s +:= 1;
         end while;
     
     end if;
     
     /* decide which of the TUPLES generate G and turn them into SGGIs */
     SGGIs := [ ];
     for t in TUPLES do
         J := sub < G | t >;
         if J eq G then
             H := StringGroupGeneratedByInvolutions (J);
             if SanityCheck then
                  assert HasIntersectionProperty (H);
             else 
                  H`HasIP := true;
             end if;
             Append (~SGGIs, H);
         end if;
     end for;

return SGGIs;
          
end function;


intrinsic AllStringCReps (G::GrpPerm, r::RngIntElt :
    ICReps := [ ],    // if non-empty, restrict to conjugates of this list
    SanityCheck := false   // don't bother to verify the string C sequences
                           ) -> SeqEnum
    
  { Find by brute force search all string C generating sequences in G.}

   require r gt 2 : "rank of string C-group must be at least 3";

return __ExhaustiveSearch (G, r : ICReps := ICReps , SanityCheck := SanityCheck);

end intrinsic;


intrinsic AllStringCReps (G::GrpMat, r::RngIntElt :
    ICReps := [ ],    // if non-empty, restrict to conjugates of this list
    SanityCheck := false   // don't bother to verify the string C sequences
                           ) -> SeqEnum
    
  { Find by brute force search all string C generating sequences in G.}

   require r gt 2 : "rank of string C-group must be at least 3";

return __ExhaustiveSearch (G, r : ICReps := ICReps , SanityCheck := SanityCheck);

end intrinsic;

