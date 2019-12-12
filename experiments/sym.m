/* 
  Experiment to see which string C-group representations of Sym(n)
  are not rank-reducible, which a not rank-inflatable, and which
  are neither.

  Define the following terms:
     ISLAND = any SGGI that isn't a reduction and cannot be reduced
     ROOT = any SGGI of rank [3..n-3] that isn't a reduction
     LEAF = any SGGI of rank [4..n-2]
*/

n := 8;
G := SymmetricGroup (n);

ALL := [ AllStringCReps (G, r) : r in [n-2..3 by -1] ];
assert #ALL[1][1] eq 1;


ROOTS := { ALL[1][1] };



for i in [1..n-4] do
  Ei := [ ];
  Ai := ALL[i];
  for j in [1..#Ai] do
    H := Ai[j];
    HL := LeftPetrie (H);
    if HasIntersectionProperty (HL) and (#Group(HL) eq #Group(H)) then
         assert exists (k){ l : l in [1..#ALL[i+1]] | IsEquivalent (HL, ALL[i+1][l]) };
         Append (~Ei, [j, k]);
    end if;
    HR := RightPetrie (H);
    if HasIntersectionProperty (HR) and (#Group(HR) eq #Group(H)) then
         assert exists (k){ l : l in [1..#ALL[i+1]] | IsEquivalent (HR, ALL[i+1][l]) };
        Append (~Ei, [j, k]);
    end if;
  end for;
  Append (~edges, Ei);
end for;
edges;

__PROFILE := function (E, nums)
  roots := [ ];
  leaves := [ ];
  islands := [ ];
  for i in [1..#nums] do
    for j in [1..nums[i]] do
      // is [i,j] a root, a leaf, both (i.e. an island) or neither?
      if (i eq 1) then
           Rij := true;
      else
           Rij := not exists { e : e in E[i-1] | e[2] eq j };
      end if;
      Lij := not exists { e : e in E[i] | e[1] eq j };
      if Rij then
        if Lij then
          Append (~islands, [i,j]);
        else 
          Append (~roots, [i,j]);
        end if;
      elif Lij then
        Append (~leaves, [i,j]);
      end if;
    end for;
  end for;
return roots, leaves, islands;
end function;