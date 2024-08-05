newPackage(
        "HSMnew",
        Version => "0.1", 
        Date => "August 2, 2024",
        Authors => {
             {Name => "Xianglong Ni", Email => "xlni@berkeley.edu"}
             },
        HomePage => "http://math.berkeley.edu/~xlni/",
        Headline => "higher structure maps",
        AuxiliaryFiles => false -- set to true if package comes with auxiliary files
        )

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "structureMap",
    "StructureMapCache",
    "verifyHST",
    "liftingMaps",
    "symProd", --fromrst
    "divProd"
    }
exportMutable {}

needsPackage "SchurFunctors"

--multiplication S_a \otimes S_b \to S_{a+b}
symProd = method()
symProd (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    R := ring M;
    d := rank M;
    if a==0 or b==0 then return id_((ring M)^(binomial(d-1+a+b,a+b)));
    LA := LB := L1 := apply(d,i->{i});
    for i from 2 to a do (
    LA = select((LA**L1)/flatten/toList, j->j_(i-1)>=j_(i-2))
    );
    for i from 2 to b do (
    LB = select((LB**L1)/flatten/toList, j->j_(i-1)>=j_(i-2))
    );
    --find the basis element of sym that corresponds to a
    --weakly increasing list of indices
    symLookup := p -> (
    binomial(d+#p-1,#p)-1-sum(#p, i -> binomial(d-(p_i)-2+#p-i,#p-i))
    );
    return map(
    R^(binomial(d-1+a+b,a+b)),R^(binomial(d-1+a,a)*binomial(d-1+b,b)),
    apply(apply(#LA,i->i)**apply(#LB,i->i),
        i -> (symLookup sort (LA_(i_0)|LB_(i_1)), (i_0)*#LB+i_1)=>1)
    );
    )

--multiplication D^a \otimes D^b \to D^{a+b}
divProd = method()
divProd (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    R := ring M;
    d := rank M;
    if a==0 or b==0 then return id_((ring M)^(binomial(d-1+a+b,a+b)));
    LA := LB := L1 := apply(d,i->{i});
    for i from 2 to a do (
    LA = select((LA**L1)/flatten/toList, j->j_(i-1)>=j_(i-2))
    );
    for i from 2 to b do (
    LB = select((LB**L1)/flatten/toList, j->j_(i-1)>=j_(i-2))
    );
    --find the basis element of sym that corresponds to a
    --weakly increasing list of indices
    symLookup := p -> (
    binomial(d+#p-1,#p)-1-sum(#p, i -> binomial(d-(p_i)-2+#p-i,#p-i))
    );
    coeff := (L1,L2) -> (
    L := L1|L2;
    return product(unique L, a -> binomial(number(L,i->i==a),number(L1,i->i==a)))
    );
    return map(
    R^(binomial(d-1+a+b,a+b)),R^(binomial(d-1+a,a)*binomial(d-1+b,b)),
    apply(apply(#LA,i->i)**apply(#LB,i->i),
        i -> (symLookup sort (LA_(i_0)|LB_(i_1)), (i_0)*#LB+i_1)=>coeff(LA_(i_0),LB_(i_1)))
    );
    )

wedgeDiag = method();
wedgeDiag (ZZ,ZZ,Module) := Matrix => (a,b,M) -> (
    return dual wedgeProduct(a,b,dual M)
    )

--compute the map w^(i)_j
structureMap = method()
structureMap (ChainComplex,ZZ,ZZ) := Matrix => (C,i,j) -> (
    if not C.cache.?StructureMapCache then C.cache.StructureMapCache = new MutableHashTable;
    if C.cache.StructureMapCache#?(i,j) then return C.cache.StructureMapCache#(i,j);
    if j == 0 then (
        if member(i,{1,2,3}) then (
            return C.dd_i --don't cache these; it'll interfere with liftingMaps
            )
        );
    (f,g,targ,src) := liftingMaps(C,i,j);
    --f is to be lifted through g
    if f === null then error "invalid structure map specified";
    v := f // map(target f, source g, g);
    if debugLevel > 0 and (entries (g*v) != entries f) then error "lifting failed";
    if src === null then (
        return C.cache.StructureMapCache#(i,j) = v --this should eventually be deleted
        ) else (
        return C.cache.StructureMapCache#(i,j) = map(targ,src,v)
        )
    )

--checks if the computed maps are actually valid
verifyHST = method()
verifyHST (ChainComplex) := () => C -> (
    if not C.cache.?StructureMapCache then error "no structure maps to verify";
    for ij in (keys C.cache.StructureMapCache) do (
	i := ij_0; j := ij_1;
	v := C.cache.StructureMapCache#ij;
	(f,g,src,targ) := liftingMaps(C,i,j);
	if (entries (g*v) != entries f) then error ("structure map "|net(i,j)|" invalid")
	);
    << "maps are valid" << endl;
    return
    )
verifyHST (ChainComplex,ZZ,ZZ) := () => (C,i,j) -> (
    if not C.cache.?StructureMapCache then error "no structure maps to verify";
    if not C.cache.StructureMapCache#?(i,j) then error "specified map doesn't (yet) exist";
    v := C.cache.StructureMapCache#(i,j);
    (f,g,src,targ) := liftingMaps(C,i,j);
    if (entries (g*v) != entries f) then error ("structure map "|net(i,j)|" invalid");
    << "map is valid" << endl;
    return
    )

--outputs f,g for lifting by main method, also for verifying manually specified str maps
liftingMaps = method()
liftingMaps(ChainComplex,ZZ,ZZ) := Sequence => (C,i,j) -> (
    f := null; g := null; src := null; targ := null;
    frmt := ((C_0,C_1,C_2,C_3)/rank);
    -----------------------
    --multiplication maps--
    -----------------------
    if j == 1 then (
        --\wedge^3 F_1 -> F_3
        if i == 1 then (
            (targ,src) = (C_3,exteriorPower(3,C_1));
            f = (C.dd_1 ** structureMap(C,3,1))*(transpose wedgeProduct(1,2,C_1));
            g = C.dd_3
            );
        --F_1 \otimes F_2 -> F_3
        if i == 2 then (
            (targ,src) = (C_3,C_1**C_2);
            f = (
                (C.dd_1 ** id_(C_2)) - (structureMap(C,3,1))*(wedgeProduct(1,1,C_1))*(id_(C_1) ** C.dd_2)
                );
            g = C.dd_3
            );
        --\wedge^2 F_1 -> F_2
        if i == 3 then (
            (targ,src) = (C_2,exteriorPower(2,C_1));
            f = (
                (C.dd_1 ** id_(C_1))
                *(transpose wedgeProduct(1,1,C_1))
                );
            g =  C.dd_2
            )
        ) else
    -----------
    --w^(3)_2--
    -----------
    if (i,j) == (3,2) then (
        (targ,src) = (C_3**C_2,exteriorPower(4,C_1));
        f = (1/2)*(
            symProd(1,1,C_2)
            *(structureMap(C,3,1)**structureMap(C,3,1))
            *wedgeDiag(2,2,C_1)
            );
        g = (
            symProd(1,1,C_2)
            *(C.dd_3**id_(C_2))
            );
        ) else
    if (i,j) == (3,3) then (
	(targ,src) = (exteriorPower(2,C_3)**C_2,exteriorPower(5,C_1)**C_1);
        f1 := (
            (id_(C_3) ** symProd(1,1,C_2))
            *(structureMap(C,3,2)**structureMap(C,3,1))
            *(id_(exteriorPower(4,C_1))**wedgeProduct(1,1,C_1))
            *((transpose wedgeProduct(4,1,C_1))**id_(C_1))
            );
        f2 := (
            (id_(C_3) ** symProd(1,1,C_2))
            *(structureMap(C,3,2)**structureMap(C,3,1))
            *flip(exteriorPower(2,C_1),exteriorPower(4,C_1))
            *(id_(exteriorPower(2,C_1))**wedgeProduct(3,1,C_1))
            *((transpose wedgeProduct(2,3,C_1))**id_(C_1))
            );
        f = (2/3)*f1 - (1/3)*f2; --works
        g = (
            (id_(C_3) ** symProd(1,1,C_2))
            *(id_(C_3) ** C.dd_3 ** id_(C_2))
            *((transpose wedgeProduct(1,1,C_3))**id_(C_2))
            );
        ) else
    if (i,j) == (3,4) then (
	(targ,src) = (exteriorPower(3,C_3)**C_2,exteriorPower(5,C_1)**exteriorPower(3,C_1));
        f1 = (
            (wedgeProduct(1,1,C_3)**symProd(1,1,C_2))
            *(id_(C_3)**flip(C_2,C_3)**id_(C_2))
            *(structureMap(C,3,2)**structureMap(C,3,2))
            *(id_(exteriorPower(4,C_1))**wedgeProduct(1,3,C_1))
            *((dual wedgeProduct(4,1,C_1))**id_(exteriorPower(3,C_1)))
            );
    	f2 = (
            (id_(exteriorPower(2,C_3))**symProd(1,1,C_2))
            *(structureMap(C,3,3)**structureMap(C,3,1))
            *(id_(exteriorPower(5,C_1))**(dual wedgeProduct(1,2,C_1)))
            );
    	f3 := (
            (id_(exteriorPower(2,C_3))**symProd(1,1,C_2))
            *flip(C_2,exteriorPower(2,C_3)**C_2)
            *(structureMap(C,3,1)**structureMap(C,3,3))
            *(id_(exteriorPower(2,C_1))**wedgeProduct(3,2,C_1)**id_(C_1))
            *((dual wedgeProduct(2,3,C_1))**(dual wedgeProduct(2,1,C_1)))
            );
    	g = (
            (id_(exteriorPower(2,C_3)) ** symProd(1,1,C_2))
            *(id_(exteriorPower(2,C_3)) ** C.dd_3 ** id_(C_2))
            *((transpose wedgeProduct(2,1,C_3))**id_(C_2))
            );
    	f = (-1)*f1 + (3/2)*f2 + (1/2)*f3;
    	) else
    if (i,j) == (2,2) then (
	(targ,src) = (exteriorPower(2,C_3),exteriorPower(3,C_1)**C_2);
    	f = (
	    (structureMap(C,1,1)**id_(C_2))
	    -
	    flip(C_2,C_3)*(structureMap(C,3,1)**structureMap(C,2,1))*(wedgeDiag(2,1,C_1)**id_(C_2))
	    -
	    (structureMap(C,3,2)*wedgeProduct(3,1,C_1)*(id_(exteriorPower(3,C_1))**C.dd_2))
	    );
    	g = (id_(C_3)**C.dd_3)*(wedgeDiag(1,1,C_3));
    	) else
    if (i,j) == (1,22) then (
	(targ,src) = (symmetricPower(2,C_3),exteriorPower(5,C_1));
        f = (structureMap(C,1,1)**structureMap(C,3,1))*(transpose wedgeProduct(3,2,C_1));
	g = (id_(C_3)**C.dd_3)*dual(divProd(1,1,C_3));
    	) else
    if (i,j) == (1,2) then (
	(targ,src) = (exteriorPower(2,C_3),exteriorPower(4,C_1)**C_1);
    	g = (
    	    (id_(C_3)**C.dd_3)
    	    *wedgeDiag(1,1,C_3)
    	    );
    	f1 = (
    	    (id_(C_3)**structureMap(C,3,1))
    	    *(structureMap(C,1,1)**wedgeProduct(1,1,C_1))
    	    *(wedgeDiag(3,1,C_1)**id_(C_1))
    	    );
    	f4 := (
    	    (C.dd_1**(structureMap(C,3,2)*wedgeProduct(3,1,C_1)))
    	    *(wedgeDiag(1,3,C_1)**id_(C_1))
    	    );
    	f = (-1)*f1 + f4;
    	) else
    if (i,j) == (2,3) then (
	(targ,src) = (exteriorPower(3,C_3),exteriorPower(4,C_1)**C_1**C_2);
    	f1' := (
    	    structureMap(C,1,2)**id_(C_2)
    	    );
    	f2' := (
    	    flip(C_2,exteriorPower(2,C_3))
    	    *(structureMap(C,3,1)**id_(exteriorPower(2,C_3)))
    	    *(wedgeProduct(1,1,C_1)**structureMap(C,2,2))
    	    *(id_(C_1)**wedgeDiag(1,3,C_1)**id_(C_2))
    	    *(flip(exteriorPower(4,C_1),C_1)**id_(C_2))
    	    );
    	f3' := (
    	    (wedgeProduct(1,1,C_3)**id_(C_2))
    	    *(id_(C_3)**flip(C_2,C_3))
    	    *(structureMap(C,3,2)**id_(C_3))
    	    *(wedgeProduct(1,3,C_1)**structureMap(C,2,1))
    	    *(id_(C_1)**wedgeDiag(3,1,C_1)**id_(C_2))
    	    *(flip(exteriorPower(4,C_1),C_1)**id_(C_2))
    	    );
    	f4' := (
    	    structureMap(C,3,3)
    	    *(wedgeProduct(4,1,C_1)**C.dd_2)
    	    );
    	f4'' := (
    	    structureMap(C,3,3)
    	    *(wedgeProduct(4,1,C_1)**id_(C_1))
    	    *(id_(exteriorPower(4,C_1))**(flip(C_1,C_1)*(id_(C_1)**C.dd_2)))
    	    );
    	g = (
    	    (id_(exteriorPower(2,C_3))**C.dd_3)
    	    *wedgeDiag(2,1,C_3)
    	    );
    	f = f1' + f2' - f3' - f4' - f4'';
    	) else
    if (i,j) == (1,3) then (
	(targ,src) = (exteriorPower(3,C_3),exteriorPower(4,C_1)**exteriorPower(3,C_1));
    	f1' = (
    	    (structureMap(C,1,2)**structureMap(C,3,1))
    	    *(id_(exteriorPower(4,C_1))**wedgeDiag(1,2,C_1))
    	    );
    	f2' = (
    	    (wedgeProduct(1,1,C_3)**id_(C_2))
    	    *(id_(C_3)**flip(C_2,C_3))
    	    *(structureMap(C,3,2)**structureMap(C,1,1))
    	    *(wedgeProduct(3,1,C_1)**id_(exteriorPower(3,C_1)))
    	    *(id_(exteriorPower(3,C_1))**wedgeDiag(1,3,C_1))
    	    *flip(exteriorPower(4,C_1),exteriorPower(3,C_1))
    	    );
    	f3' = (
    	    structureMap(C,3,3)
    	    *(wedgeProduct(3,2,C_1)**C.dd_1**id_(C_1))
    	    *(id_(exteriorPower(3,C_1))**flip(C_1,exteriorPower(2,C_1))**id_(C_1))
    	    *(wedgeDiag(3,1,C_1)**wedgeDiag(2,1,C_1))
    	    );
    	f = f1' - f2' + f3';
    	g = (
    	    (id_(exteriorPower(2,C_3))**C.dd_3)
    	    *wedgeDiag(2,1,C_3)
    	    );
    	);
    return (f,g,targ,src)
    )


beginDocumentation()

doc ///
    Key
        HSMnew
    Headline
        higher structure maps
    Description
        Text
            The code here will eventually be combined into the ResolutionStructureTheorems package.
///

doc ///
    Key
        structureMap
        StructureMapCache
        (structureMap,ChainComplex,ZZ,ZZ)
    Headline
        higher structure map
    Usage
        structureMap(C,i,j)
    Inputs
        C: ChainComplex
            an exact sequence $0 \to F_3 \to F_2 \to F_1 \to F_0$
        i: ZZ
        j: ZZ
    Outputs
        : Matrix
            (a particular choice of) the map $w^{(i)}_j$ associated to $C$
    Description
        Text
            When {\tt i} is 0, the output is just the {\tt j}-th differential in
            the input complex.
            
            All the maps $w^{(i)}_j$ for $i > 0$ involve some sort of lifting, which may or may
            not be unique. For instance, the multiplication map
            $w^{(3)}_1 \colon \bigwedge^2 F_1 \to F_2$ involves lifting through $F_2 \to F_1$,
            which has kernel $F_3 \to F_2$.
        Example
            S = QQ[x,y,z];
            I = ideal(-x^2+x*y-y^2+x*z-2*y*z, -x*y+y*z, -y^2-y*z, x^2+x*y+y^2+y*z);
            C = res I;
            structureMap(C,3,1)
///
	    
--tests still need to be written

end--
uninstallPackage "HSMnew"
restart

------------------------
-- example code below --
------------------------
needsPackage("HSMnew",Reload=>true)

debugLevel = 1 --to check if liftings succeed

S = QQ[x_1..x_8];
I = minors(2,genericMatrix(S,2,4))
F = res I

--these are the implemented structure maps

structureMap(F,1,1); -- wedge^3 F1 -> F3
structureMap(F,1,2); -- wedge^4 F1 ** F1 -> wedge^2 F3
structureMap(F,1,22); -- wedge^5 F1 -> S2 F3
structureMap(F,1,3); -- wedge^4 F1 ** wedge^3 F1 -> wedge^3 F3
structureMap(F,2,1); -- F1 ** F2 -> F3
structureMap(F,2,2); -- wedge^3 F1 ** F2 -> wedge^2 F3
structureMap(F,2,3); -- wedge^4 F1 ** F1 ** F2 -> wedge^3 F3
structureMap(F,3,1); -- wedge^2 F1 -> F2
structureMap(F,3,2); -- wedge^4 F1 -> F3 ** F2
structureMap(F,3,3); -- wedge^5 F1 ** F1 -> wedge^2 F3 ** F2
structureMap(F,3,4); -- wedge^5 F1 ** wedge^3 F1 -> wedge^3 F3 ** F2






