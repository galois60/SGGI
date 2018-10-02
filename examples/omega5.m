__f := function (a)
return (1-a^2)/(1+a^2);
end function;

__g := function (a)
return (-2*a)/(1+a^2);
end function;

Omega5_4Polytopes := function (p, e)

  // basics
  q := p^e;
  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q);
  
  // compute necessary sets of scalars 
  A0 := [ a : a in k | a^2 ne -1 ];   // eliminate singular points
"|A0| =", #A0;
  assert forall { a : a in A0 | InnerProduct (V.1+a*V.2, V.1+a*V.2) ne 0 };
  A := [ ];
  for a in A0 do
    if (q mod 4 eq 1) then
      assert IsSquare (k!(-1));
      if not IsSquare (-1-a^2) then
        Append (~A, a);
      end if;
    else
      assert not IsSquare (k!(-1));
      if IsSquare (-1-a^2) then
        Append (~A, a);
      end if;
    end if;
  end for;
"|A| =", #A;
  // ensure that they define "negative" points
  assert forall { a : a in A | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+a*V.2>)) eq 1 };
  // define scalars that define "plus" points (other than basis vectors)
  B := [ a : a in A0 | (a ne 0) and (not a in A) ];
  assert forall { b : b in B | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+b*V.2>)) eq 2 };
"|B| =", #B;
    
  // define <rho> and <R>
  l := sub < V | V.4 , V.5 >;
  TYPE := IdentifyLineType (Q, l);
  if (q mod 4 eq 1) then m := (q-1); else m := (q+1); end if;
  rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
  R := Centralizer (Om, rho);

  // define <r0> 
  l0 := sub < V | V.1 , V.5 >;
  assert IdentifyLineType (Q, l0) eq TYPE;
  r0 := InvolutionOdd (PerpSpace (Q, l0), l0);   assert r0 in R;
  
  // determine all pairs (<r1>,<t>) such that <r0>,<r1>,<t> generates <R> 
  polys := [ ];
  for a in A do   // define one <r1> for each choice of scalar a in A
      l1 := sub < V | V.1 + a * V.2 , a * V.4 + V.5 >;
      assert IdentifyLineType (Q, l1) eq TYPE;
      r1 := InvolutionOdd (PerpSpace (Q, l1), l1);   assert r1 in R;
      if Order (r0 * r1) eq m then
          c := 0;
          for b in B do   // determine which choices work with <r1>
              x := sub < V | V.2 + b * V.3 >;
              t := InvolutionOdd (x, PerpSpace (Q, x));   assert t in R;
              if (Order (r1 * t) in [q-1, q+1, 2*p]) then
                  c +:= 1;
                  assert R eq sub<R|r0,r1,t>;
                  // tack on our favorite choice for <r2> and make sure it works
                  l2 := sub < V | [ V.1 - V.5 , V.2 - V.4 ] >;
                  r2 := InvolutionOdd (PerpSpace (Q, l2), l2);   assert r2 in Om;
                  assert (r0, r2) eq Identity (Om) and (r1, r2) eq Identity (Om);
                  assert R meet sub <Om|r1,t,r2> eq sub <Om|r1,t>;
                  Append (~polys, [r0, r1, t, r2]);
              end if;
          end for;
          assert c gt 0;
      end if;
  end for;
  
  // tack on our favorite choice for <r2> and make sure it works
  groups := [ sub < Om | tup > : tup in polys ];
  assert forall { H : H in groups | IsStringCGroup (H) };
  
  "#polys:", #groups;
  "Schlafli symbols:", { SchlafliSymbol (H) : H in groups };
  
return groups;

end function; 