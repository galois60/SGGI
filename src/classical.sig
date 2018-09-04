174,0
S,PerpSpace,Compute the perp-space of U relative to the bilinear form F,0,2,0,0,0,0,0,0,0,159,,0,0,-34,,159,-38,-38,-38,-38,-38
S,PreservesBilinearForm,Check if g is an isometry of the bilinear form F,0,2,0,0,0,0,0,0,0,-34,,0,0,180,,36,-38,-38,-38,-38,-38
S,PreservesBilinearForm,Check if G is a group of isometries of the bilinear form F,0,2,0,0,0,0,0,0,0,-34,,0,0,178,,36,-38,-38,-38,-38,-38
S,PreservesQuadraticForm,Check if g is an isometry of the quadratic form Q,0,2,0,0,0,0,0,0,0,-34,,0,0,180,,36,-38,-38,-38,-38,-38
S,PreservesQuadraticForm,Check if G is a group of isometries of the quadratic form Q,0,2,0,0,0,0,0,0,0,-34,,0,0,178,,36,-38,-38,-38,-38,-38
S,RestrictBilinearForm,Restrict the bilinear form F to the subspace U,0,2,0,0,0,0,0,0,0,159,,0,0,-34,,-34,-38,-38,-38,-38,-38
S,RestrictQuadraticForm,Restrict the quadratic form Q to the subspace U,0,2,0,0,0,0,0,0,0,159,,0,0,-34,,-34,-38,-38,-38,-38,-38
S,InvolutionOdd,"In a field of odd characteristic, the involution inducing 1 on Ep and -1 on Em",0,2,0,0,0,0,0,0,0,159,,0,0,159,,180,-38,-38,-38,-38,-38
S,InduceGroup,"For G stabilizing U, return the group induced by G on U and the homomorphism from G to this group",0,2,0,0,0,0,0,0,0,159,,0,0,178,,178,175,-38,-38,-38,-38
S,IsNonsingularOrthogonalSpace,Decide if Q is a nonsingular quadratic form on its underlying module,0,1,0,0,0,0,0,0,0,-34,,36,-38,-38,-38,-38,-38
S,IsHyperbolicLine,Decide if U is a hyperbolic line relative to quadratic form Q,0,2,0,0,0,0,0,0,0,159,,0,0,-34,,36,160,160,-38,-38,-38
S,IdentifyLineType,"Decide whether the 2-space is totally singular, hyperbolic, singular, or asingular",0,2,0,0,0,0,0,0,0,159,,0,0,-34,,298,-38,-38,-38,-38,-38
<<<<<<< HEAD
=======
S,MyWittIndex,The isometry type of the subspace U of the quadratic space determined by Q,0,2,0,0,0,0,0,0,0,159,,0,0,-34,,148,-38,-38,-38,-38,-38
>>>>>>> 326647854c10b1e26857789b9d3f9fb98b4f85a1
S,Reflection,"Return the reflection in the perp-space of v relative to F, where v is non-singular with respect to Q",0,2,0,0,0,0,0,0,0,-34,,0,0,160,,180,-38,-38,-38,-38,-38
S,Symmetry,Return the symmetry defined by the nonsingular vector v,0,2,0,0,0,0,0,0,0,-34,,0,0,160,,180,-38,-38,-38,-38,-38
S,TransvectionGroup,"Return the group of (v,W)-transvections, where W is the perp-space of v relative to F",0,2,0,0,0,0,0,0,0,-34,,0,0,160,,178,-38,-38,-38,-38,-38
S,PseudoTransvectionGroup,"Return the group of pseudo-tansvections associated to the line L = <v,b>, where Q(v)=(v,b)=0",0,3,0,0,0,0,0,0,0,-34,,0,0,160,,0,0,160,,178,-38,-38,-38,-38,-38
S,MySupport,Compute the support of matrix X on its underlying vector space,0,1,0,0,0,0,0,0,0,-34,,159,-38,-38,-38,-38,-38
S,MySupport,Compute the support of matrix group H on its underlying vector space,0,1,0,0,0,0,0,0,0,178,,159,-38,-38,-38,-38,-38
S,MySupport,Compute the support of matrix algebra A on its underlying vector space,0,1,0,0,0,0,0,0,0,176,,159,-38,-38,-38,-38,-38
<<<<<<< HEAD
S,MyWittIndex,The Witt index of the quadratic space determined by Q,0,1,0,0,0,0,0,0,0,-34,,148,-38,-38,-38,-38,-38
=======
>>>>>>> 326647854c10b1e26857789b9d3f9fb98b4f85a1
S,SpIsotropic,"Return the symplect group Sp(d,q) relative to a totally isotropic basis",0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-34,175,-38,-38,-38
S,SpHyperbolic,"Return the symplect group Sp(d,q) relative to a hyperbolic basis",0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-34,175,-38,-38,-38
S,MyGO,Full orthogonal group written relative to an orthonormal basis,0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,MySO,Full orthogonal group written relative to an orthonormal basis,0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,MyOmega,Full orthogonal group written relative to an orthonormal basis,0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,C2MaximalSpIsotropic,"Return the totally isotropic (C2) maximal subgroup of the nice Sp(d,q)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,C2MaximalSp4Hyperbolic,"Return the totally hyperbolic (C2) maximal subgroup of Sp(4,q) relative to hyperbolic basis",0,1,0,0,0,0,0,0,0,148,,178,-38,-38,-38,-38,-38
S,IsomorphismWithField,"Given T acting irreducibly on its underlying module, compute inverse isomorphsisms from Env(<T>) to the isomorphic field",0,1,0,0,0,0,0,0,0,177,,176,84,175,175,-38,-38
S,C3MaximalSp4,"Return the nondegenerate semilinear (C3) maximal subgroup of the nice Sp(4,q)",0,2,0,0,0,0,0,0,0,148,,0,0,148,,178,-38,-38,-38,-38,-38
S,SL2toGO3,"Given q return isomorphism SL(2,q) --> GO(3,q)",0,1,0,0,0,0,0,0,0,148,,175,-38,-38,-38,-38,-38
S,ProjectiveGroup,"Given a matrix group, compute its action on the underlying projective space",0,1,0,0,0,0,0,0,0,178,,224,175,-38,-38,-38,-38
