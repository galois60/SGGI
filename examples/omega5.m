

__f := function (a)
return (1-a^2)/(1+a^2);
end function;

__g := function (a)
return (-2*a)/(1+a^2);
end function;

__get_scalars := function (q) 
  k := GF (q);
  X := [ a : a in k | (a ne 0) and (a^2 ne -1) ];   // this is to eliminate singular points
  A0 := [ ];
  for a in X do
    if (q mod 4 eq 1) then
      assert IsSquare (k!(-1));
      if not IsSquare (-1-a^2) then
        Append (~A0, a);
      end if;
    else
      assert not IsSquare (k!(-1));
      if IsSquare (-1-a^2) then
        Append (~A0, a);
      end if;
    end if;
  end for;
  // every element in A0 defines a "negative" nonsingular point
  // now build the scalars that give "positive" nonsingular points
  B := [ a : a in X | (a ne 0) and (not a in A0) ];
  // finally, build the scalars that generate the appropriate dihedral group
  if (q mod 4 eq 1) then m := q-1; else m := q+1; end if;
  A := [ ];
  for a in A0 do
    h := GL (2, q)![ -__f(a) , -__g(a) , __g(a) , -__f(a) ];
    if Order (h) eq m then
      Append (~A, a);
    end if;
  end for;
  "q =", q;
  "A0 =", #A0;
  "A =", #A;
  "B =", #B;
  "phi(m) =", EulerPhi (m);
return A0, A, B;
end function;


GenericConstruction := function (q)

  k := GF (q);
  K<a,b> := RationalFunctionField (k, 2);
  G := GL (5, K);
  
  r := G![ -1, 0, 0, 0, 0,
            0, 1, 0, 0, 0,
            0, 0, 1, 0, 0,
            0, 0, 0, 1, 0,
            0, 0, 0, 0, -1 ];
           
  ra := G![ __f(a), __g(a),   0,     0,      0,
            __g(a), -__f(a),  0,     0,      0,
               0  ,    0   ,  1,     0,      0,
               0  ,    0   ,  0,  -__f(a), __g(a), 
               0  ,    0   ,  0,   __g(a), __f(a) ];  
               
  tb := G![    1,      0,     0,     0,      0,
               0 , -__f(b), __g(b),  0,      0,
               0 ,  __g(b), __f(b),  0,      0,
               0  ,    0   ,  0,     1,      0, 
               0  ,    0   ,  0,     0,      1 ];
               
  s := G![  0, 0, 0, 0, 1,
            0, 0, 0, 1, 0,
            0, 0, 1, 0, 0,
            0, 1, 0, 0, 0,
            1, 0, 0, 0, 0 ];
            
return [r, ra, tb, s];
end function;



Omega5_All_4Polytopes := function (p, e)

  // basics
  q := p^e;
  k := GF (q);
  V := VectorSpace (k, 5);
  Q := Identity (MatrixAlgebra (k, 5));
  G := MyGO (5, q);
  Om := MyOmega (5, q);
  
  // compute necessary sets of scalars 
  A0, A, B := __get_scalars (q);
  
      // ensure A0 scalars define "negative" points
      assert forall { a : a in A0 | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+a*V.2>)) eq 1 };
  
      // ensure B scalars define "positive" points 
      assert forall { b : b in B | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+b*V.2>)) eq 2 };
    
  // define <rho> and <R>
  l := sub < V | V.4 , V.5 >;
  Oml := Stabilizer  (Om, l);
  TYPE := IdentifyLineType (Q, l);
  if (q mod 4 eq 1) then m := (q-1); else m := (q+1); end if;
  rho := InvolutionOdd (PerpSpace (Q, l), l);   assert rho in Om;
  L := Centralizer (Om, rho);
  assert L eq Oml;

  // define <r0> 
  l0 := sub < V | V.1 , V.5 >;
  assert IdentifyLineType (Q, l0) eq TYPE;
  r0 := InvolutionOdd (PerpSpace (Q, l0), l0);   assert r0 in L;
  
  // determine all pairs (<r1>,<t>) such that <r0>,<r1>,<t> generates <R> 
  polys := [ ];
  for a in A do   // define one <r1> for each choice of scalar a in A
      l1 := sub < V | V.1 + a * V.2 , a * V.4 + V.5 >;
      assert IdentifyLineType (Q, l1) eq TYPE;
      r1 := InvolutionOdd (PerpSpace (Q, l1), l1);   assert r1 in L;
      h := r0 * r1;    assert Order (h) eq m;
      c := 0;
      for b in B do   // determine which choices work with <r1>
          x := sub < V | V.2 + b * V.3 >;
          t := InvolutionOdd (x, PerpSpace (Q, x));   assert t in L;
          ht := r1 * t;
          if (Order (ht) in [q-1, q+1, 2*p]) then
ht1 := InduceTransformation (ht, l);   assert Order (ht1) eq 2;
ht2 := InduceTransformation (ht, sub<V|V.1,V.2,V.3>);   "|ht| =", Order (ht), Order (ht2);
E := Eigenspace (ht2, -1); assert Dimension (E) eq 1;
QQ := RestrictQuadraticForm (Q, sub<V|V.1,V.2,V.3>);
F := PerpSpace (QQ, E);
"E =", E;
"F =", F;
htF := InduceTransformation (ht2, F);
"htF =", htF;
"|htF| =", Order (htF);
"------";
"   ";
              c +:= 1;
              assert L eq sub<L|r0,r1,t>;
              // tack on our favorite choice for <r2> and make sure it works
              l2 := sub < V | [ V.1 - V.5 , V.2 - V.4 ] >;
              r2 := InvolutionOdd (PerpSpace (Q, l2), l2);   assert r2 in Om;
              assert (r0, r2) eq Identity (Om) and (r1, r2) eq Identity (Om);
              assert L meet sub <Om|r1,t,r2> eq sub <Om|r1,t>;
              Append (~polys, [r0, r1, t, r2]);
          end if;
      end for;
      assert c gt 0;
  end for;
  
  // tack on our favorite choice for <r2> and make sure it works
  groups := [ sub < Om | tup > : tup in polys ];
  assert forall { H : H in groups | IsStringCGroup (H) };
  
  "the construction found", #groups, "polytopes for Omega ( 5 ,",q,")";
  
return groups;

end function; 


