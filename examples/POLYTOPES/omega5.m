__identify_point := function (Q, x)
  if InnerProduct (x.1 * Q, x.1) eq 0 then
      return "singular";
  else
      if MyWittIndex (Q, PerpSpace (Q, x)) eq 2 then
          return "positive";
      else
          return "negative";
      end if;
  end if;
end function;

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
               
  tb := G![   -1,      0,     0,     0,      0,
               0 ,  __f(b), -__g(b), 0,      0,
               0 ,  -__g(b), -__f(b),0,      0,
               0  ,    0   ,  0,    -1,      0, 
               0  ,    0   ,  0,     0,     -1 ];
               
  s := G![  0, 0, 0, 0, 1,
            0, 0, 0, 1, 0,
            0, 0, 1, 0, 0,
            0, 1, 0, 0, 0,
            1, 0, 0, 0, 0 ];
            
return [r, ra, tb, s];
end function;


Omega5_All_4Polytopes := function (p, e)

  q := p^e;
  k := GF (q);
  Om := MyOmega (5, q);
  
  // compute necessary sets of scalars and do the sanity checks
  
  A0, A, B := __get_scalars (q);
      // ensure A0 scalars define "negative" points
      Q := Identity (MatrixAlgebra (k, 5));
      V := VectorSpace (k, 5);
      assert forall { a : a in A0 | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+a*V.2>)) eq 1 };
      // ensure B scalars define "positive" points 
      assert forall { b : b in B | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+b*V.2>)) eq 2 };
    
  // build the generic string tuple corresponding to q
  S := GenericConstruction (q);
  
  // now work through the scalars and select the combinations that work
  good := [ q+1 , q-1 , 2*p ];
  polys := [ ];
  r := S[2];
  t := S[3];
  for a in A do
      Ba := [ b : b in B | Order (Evaluate (r, [a,b]) * Evaluate (t, [a,b])) in good ];
      polys cat:= [ [ Evaluate (S[i], [a,b]) : i in [1..4] ] : b in Ba ];
  end for;
  
  // tack on our favorite choice for <r2> and make sure it works
  groups := [ sub < Om | tup > : tup in polys ];
  assert forall { H : H in groups | IsStringCGroup (H) };
  
  "the construction found", #groups, "polytopes for Omega ( 5 ,",q,")";
  
return groups;

end function; 


// use this verbose variant to check all of the claims in the paper
Omega5_Check := function (p, e)

  q := p^e;
  k := GF (q);
  Om := MyOmega (5, q);
  
  // compute necessary sets of scalars and do the sanity checks
  
  A0, A, B := __get_scalars (q);
      // ensure A0 scalars define "negative" points
      Q := Identity (MatrixAlgebra (k, 5));
      V := VectorSpace (k, 5);
      assert forall { a : a in A0 | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+a*V.2>)) eq 1 };
      // ensure B scalars define "positive" points 
      assert forall { b : b in B | MyWittIndex (Q, PerpSpace (Q, sub<V|V.1+b*V.2>)) eq 2 };
    
  // build the generic string tuple corresponding to q
  S := GenericConstruction (q);
  
  // now work through the scalars and select the combinations that work
  good := [ q+1 , q-1 , 2*p ];
  polys := [ ];
  r := S[2];
  t := S[3];
  P := sub < V | V.1 , V.2 , V.3 >;
  
  for a in A do
"a =", a;

      Ba := [ b : b in B | Order (Evaluate (r, [a,b]) * Evaluate (t, [a,b])) in good ];
      polys cat:= [ [ Evaluate (S[i], [a,b]) : i in [1..4] ] : b in Ba ];
      
      for b in Ba do
      "   b =", b;

          ra := Evaluate (r, [a,b]);
          assert Eigenspace (ra, 1) meet P eq sub < V | V.1 - a * V.2 , V.3 >;
          tb := Evaluate (t, [a,b]);
          assert Eigenspace (tb, -1) meet P eq sub < V | V.1, V.3 - b * V.2 >;
          lab := sub < V | a * V.1 + V.2 , V.2 + b * V.3 >;  assert (lab * ra eq lab) and (lab * tb eq lab);
          "   l_{ab} is", IdentifyLineType (Q, lab),
          "    and |ra * tb| =", Order (ra * tb);
          r2 := Evaluate (S[4], [a,b]);
          z := sub < V | V.1 - a*V.2 + (a/b)*V.3 - a*V.4 + V.5 >;   
          assert (z * ra eq z) and (z * tb eq z) and (z * r2 eq z);
          "   z is", __identify_point (Q, z);
          lb := sub < V | V.2 - V.4 , V.2 + b*V.3 >;   assert (lb * r2 eq lb) and (lb * tb eq lb);
          "   l_{b} is", IdentifyLineType (Q, lb),
          "    and |tb * r2| =", Order (tb * r2);
"   -----";
end for;
  end for;
  
  // tack on our favorite choice for <r2> and make sure it works
  groups := [ sub < GL (5, q) | tup > : tup in polys ];
//  assert forall { H : H in groups | IsStringCGroup (H) };
  
  "the construction found", #groups, "polytopes for Omega ( 5 ,",q,")";
  
return groups;

end function; 




