newPackage(
        "HigherStructureMaps",
        Version => "0.1", 
        Date => "October 30, 2021",
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
    "initDefectVars",
    "StartingIndex",
    "topComplex",
    "Maps1nn1", --for debugging
    "Maps14xm", --
    "Maps1562",
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
	LA = select((LA**L1)/flatten, j->j_(i-1)>=j_(i-2))
	);
    for i from 2 to b do (
	LB = select((LB**L1)/flatten, j->j_(i-1)>=j_(i-2))
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
	LA = select((LA**L1)/flatten, j->j_(i-1)>=j_(i-2))
	);
    for i from 2 to b do (
	LB = select((LB**L1)/flatten, j->j_(i-1)>=j_(i-2))
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
    --is this the same for all formats?
    if (i,j) == (3,2) then (
        (targ,src) = (C_3**C_2,exteriorPower(4,C_1));
        f = (
            (symProd(1,1,C_2))
            *(structureMap(C,3,1)**structureMap(C,3,1))
            *(transpose wedgeProduct(2,2,C_1))
            );
        f = f//(2*id_(target f)); --is this halving correct?
        g = (symProd(1,1,C_2))*(C.dd_3 ** id_(C_2))
        ) else
    -------------------------
    --format-dependent maps--
    -------------------------
    if frmt == (1,rank C_1,rank C_1,1) then (
        if debugLevel > 0 then << "format: (1,n,n,1)" << endl;
        (f,g,targ,src) = Maps1nn1(C,i,j)
        ) else
    if frmt == (1,4,3 + rank C_3, rank C_3) then (
        if debugLevel > 0 then << "format: (1,4,m+3,m)" << endl;
        (f,g,targ,src) = Maps14xm(C,i,j)
        ) else
    if frmt == (1,5,6,2) then (
	if debugLevel > 0 then << "format: (1,5,6,2)" << endl;
	(f,g,targ,src) = Maps1562(C,i,j)
	) else
    if frmt == (1,6,7,2) then (
	if debugLevel > 0 then << "format: (1,6,7,2)" << endl;
	(f,g,targ,src) = Maps1672(C,i,j)
	) else
    if frmt == (1,5,7,3) then (
	if debugLevel > 0 then << "format: (1,5,7,3)" << endl;
	(f,g,targ,src) = Maps1573(C,i,j)
	);
    return (f,g,targ,src)
    )

---------------------------
-- format-specific lifts --
---------------------------
--this method should not be invoked directly
--outputs f,g for lifting by main method
Maps14xm = method()
Maps14xm (ChainComplex,ZZ,ZZ) := Sequence => (C,i,j) -> (
    f := null; g := null; src := null; targ := null;
    if (i == 1 and j > 1) then (
        if even j then (
            (targ,src) = (
                exteriorPower(j,C_3),
                fold(tensor,apply(j//2,i->(exteriorPower(4,C_1))))**C_1
                );
            f = (
                -(id_(exteriorPower(j-1,C_3))**structureMap(C,3,1))
                *(structureMap(C,1,j-1)**wedgeProduct(1,1,C_1))
                *((dual wedgeProduct(3,1,C_1))**(id_(C_1)))
                -
                (wedgeProduct(j-2,1,C_3)**id_(C_2))
                *(structureMap(C,1,j-2)**structureMap(C,3,2))
                )
            ) else (
            (targ,src) = (
                exteriorPower(j,C_3),
                fold(tensor,apply(j//2,i->(exteriorPower(4,C_1))))**exteriorPower(3,C_1)
                );
            f = (
                (structureMap(C,1,j-1)**structureMap(C,3,1))
                *(dual wedgeProduct(1,2,C_1))
                -
                (wedgeProduct(j-2,1,C_3)**id_(C_2))
                *(structureMap(C,1,j-2)**structureMap(C,3,2))
                )
            );
        g = (
            (id_(exteriorPower(j-1,C_3))**C.dd_3)
            *(dual wedgeProduct(j-1,1,C_3))
            )
        );
    if (i == 2 and j > 1) then (
        if j == 2 then (
            (targ,src) = (exteriorPower(2,C_3),exteriorPower(3,C_1)**C_2);
            f = (
                flip(C_2,exteriorPower(j-1,C_3))
                *(structureMap(C,3,1)**structureMap(C,2,j-1))
                *((dual wedgeProduct(2,1,C_1))**id_(C_2))
                + --check signs?
                (wedgeProduct(j-2,1,C_3)**id_(C_2))
                *((wedgeProduct(3,1,C_1)*(id_(exteriorPower(3,C_1))**C.dd_2))**structureMap(C,3,2))
                - --ditto
                (structureMap(C,1,j-1)**id_(C_2))
                )
            ) else
        if even j then (
            targ = exteriorPower(j,C_3);
            if j > 3 then (
                src = fold(tensor,apply((j//2)-1,i->(exteriorPower(4,C_1))))**exteriorPower(3,C_1)**C_2
                ) else (
                src = exteriorPower(3,C_1)**C_2
                );
            f = (
                flip(C_2,exteriorPower(j-1,C_3))
                *(structureMap(C,3,1)**structureMap(C,2,j-1))
                *((dual wedgeProduct(2,1,C_1))**id_(C_2))
                - --check signs?
                (wedgeProduct(j-2,1,C_3)**id_(C_2))
                *(structureMap(C,2,j-2)**structureMap(C,3,2)) --needed an exception for this in the case j=2
                - --ditto
                (structureMap(C,1,j-1)**id_(C_2))
                );
            ) else (
            (targ,src) = (
                exteriorPower(j,C_3),
                fold(tensor,apply(j//2,i->(exteriorPower(4,C_1))))**C_1**C_2
                );
            f = (
                -flip(C_2,exteriorPower(j-1,C_3))
                *(structureMap(C,3,1)**id_(exteriorPower(j-1,C_3)))
                *(wedgeProduct(1,1,C_1)**structureMap(C,2,j-1))
                *(id_(C_1)**(dual wedgeProduct(1,3,C_1))**id_(C_2))
                - --check signs?
                (wedgeProduct(j-2,1,C_3)**id_(C_2))
                *(structureMap(C,2,j-2)**structureMap(C,3,2))
                + --ditto
                (structureMap(C,1,j-1)**id_(C_2))
                );
            );
        g = (
            (id_(exteriorPower(j-1,C_3))**C.dd_3)
            *(dual wedgeProduct(j-1,1,C_3))
            )
        );
    return (f,g,targ,src)
    )

--this method should not be invoked directly
--outputs f,g for lifting by main method
Maps1nn1 = method()
Maps1nn1 (ChainComplex,ZZ,ZZ) := Sequence => (C,i,j) -> (
    f := null; g := null; src := null; targ := null;
    if (i == 3 and j > 2) then (
        (targ,src) = (symmetricPower(j-1,C_3)**C_2,exteriorPower(2*j,C_1));
        f = (
            (id_(symmetricPower(j-2,C_3))**symProd(1,1,C_2))
            *(structureMap(C,3,j-1)**structureMap(C,3,1))
            *(transpose wedgeProduct(2*j-2,2,C_1))
            );
	f = f//(j*id_(target f)); --is this division correct?
        g = (
            (id_(symmetricPower(j-2,C_3))**symProd(1,1,C_2))
            *(
                ((id_(symmetricPower(j-2,C_3))**C.dd_3)*(dual divProd(j-2,1,C_3)))
                **(id_(C_2))
                )
            );
	g = g//((j-1)*id_(target g)) --is this division correct?
        );
    if (i == 1 and j > 1) then (
        (targ,src) = (symmetricPower(j,C_3),exteriorPower(2*j+1,C_1));
        f = (
            (C.dd_1**structureMap(C,3,j))
            *(dual wedgeProduct(1,2*j,C_1))
            );
        g = (id_(symmetricPower(j-1,C_3))**C.dd_3)*(dual divProd(j-1,1,C_3));
	g = g//(j*id_(target g)) --is this division correct?
        );
    return (f,g,targ,src)
    )

--this method should not be invoked directly
--outputs f,g for lifting by main method
Maps1562 = method()
Maps1562 (ChainComplex,ZZ,ZZ) := Sequence => (C,i,j) -> (
    f := null; g := null; src := null; targ := null; f1 := 0; f2 := 0; f3 := 0;
    ------------------
    --Maps of W(d_3)--
    ------------------
    if (i,j) == (3,3) then (
        f = (
            (id_(C_3) ** symProd(1,1,C_2))
            *(structureMap(C,3,2)**structureMap(C,3,1))
            *(id_(exteriorPower(4,C_1))**wedgeProduct(1,1,C_1))
            *((transpose wedgeProduct(4,1,C_1))**id_(C_1))
            );
        g = (
            (id_(C_3) ** symProd(1,1,C_2))
            *(id_(C_3) ** C.dd_3 ** id_(C_2))
            *((transpose wedgeProduct(1,1,C_3))**id_(C_2))
            )
        );
    ------------------
    --Maps of W(d_1)--
    ------------------
    if (i,j) == (1,21) then (
        f = (structureMap(C,1,1)**structureMap(C,3,1))*(transpose wedgeProduct(3,2,C_1));
        g = (id_(C_3)**C.dd_3)*(matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}}); --matrix is S2 -> T2
        );
    if (i,j) == (1,22) then (
        f = (
            ((structureMap(C,1,1)**structureMap(C,3,1))*(transpose wedgeProduct(3,2,C_1)))
            + (-2)*(C.dd_1 ** structureMap(C,3,2))*(transpose wedgeProduct(1,4,C_1))
            );
        g = (id_(C_3)**C.dd_3)*(transpose wedgeProduct(1,1,C_3))
        );
    if (i,j) == (1,3) then (
        f1 = ((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}}) ** id_(C_2))*(structureMap(C,1,21)**structureMap(C,3,1));
        f2 = (
            (((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*symProd(1,1,C_3))**id_(C_2))
            *(flip(C_3**C_2,C_3))
            *(structureMap(C,3,2)**(structureMap(C,2,1)*(id_(C_1)**structureMap(C,3,1))))
            *((transpose wedgeProduct(4,1,C_1))**id_(exteriorPower(2,C_1))));
        g = (
            (((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*symProd(1,1,C_3))**C.dd_3)
            *(id_(C_3)**(transpose wedgeProduct(1,1,C_3)))
            *(flip(exteriorPower(2,C_3),C_3)));
        f = f1-f2
        );
    if (i,j) == (1,4) then (
        f1 = ((structureMap(C,1,3)**structureMap(C,3,1))
            *(id_(exteriorPower(5,C_1))**(transpose wedgeProduct(2,2,C_1))));
        f2 = (
            (id_(exteriorPower(2,C_3))**flip(C_2,C_3))
            *(structureMap(C,3,3)**structureMap(C,1,1))
            *(id_(exteriorPower(5,C_1))**(transpose wedgeProduct(1,3,C_1))));
        f3 = (
            (structureMap(C,1,22)**structureMap(C,3,2))
            );
        f = f1+f2-f3;
        g = id_(exteriorPower(2,C_3))**((id_(C_3)**C.dd_3)*(transpose wedgeProduct(1,1,C_3)))
        );
    ------------------
    --Maps of W(d_2)--
    ------------------
    if (i,j) == (2,2) then (
        f = (
            (structureMap(C,2,1)**structureMap(C,3,1))*(flip(C_2,C_1)**id_(exteriorPower(2,C_1)))*(id_(C_2)**(transpose wedgeProduct(1,2,C_1)))
            +
            (structureMap(C,3,2)*wedgeProduct(3,1,C_1)*(id_(exteriorPower(3,C_1))**C.dd_2))*flip(C_2,exteriorPower(3,C_1))
            -
            (structureMap(C,1,1)**id_(C_2))*flip(C_2,exteriorPower(3,C_1))
            );
        g = (id_(C_3)**C.dd_3)*(transpose wedgeProduct(1,1,C_3))
        );
    if (i,j) == (2,3) then (
        f1 = (
            ((
                    --(matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*
                    symProd(1,1,C_3))**id_(C_2))*
            ((structureMap(C,2,1)*flip(C_2,C_1))**(structureMap(C,3,2)))
            *(id_(C_2)**(transpose wedgeProduct(1,4,C_1)))
            );
        f2 = ( --no halving?
            --((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})**id_(C_2))*
            ((structureMap(C,1,21)) ** id_(C_2))
            *(flip(C_2,exteriorPower(5,C_1))) --unnecessary
            );
        f = f1 - f2;
        g = (
            ((
                    --(matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*
                    symProd(1,1,C_3))**C.dd_3)*
            (id_(C_3)**(transpose wedgeProduct(1,1,C_3)))
            *(flip(exteriorPower(2,C_3),C_3)))
        );
    return (f,g,targ,src)
    )

Maps1672 = method()
Maps1672 (ChainComplex,ZZ,ZZ) := Sequence => (C,i,j) -> (
    f := null; g := null; src := null; targ := null;
    f1 := 0; f2 := 0; f3 := 0;
    ------------------
    --Maps of W(d_3)--
    ------------------
    if (i,j) == (3,31) then (
	(targ,src) = (
	    exteriorPower(2,C_3)**C_2,
	    schurModule({2,1,1,1,1},C_1)
	    );
        proj := src.cache#"Schur"#0 || wedgeProduct(5,1,C_1);
	f1 = (
    	    (id_(exteriorPower(4,C_1))**wedgeProduct(1,1,C_1))
    	    *(wedgeDiag(4,1,C_1)**id_(C_1))
    	    *(inverse proj)_{0..34}
    	    );
	f = (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(structureMap(C,3,2)**structureMap(C,3,1))
    	    *f1
    	    );
	g = (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *(wedgeDiag(1,1,C_3)**id_(C_2))
    	    )
        );
    if (i,j) == (3,323) then (
	(targ,src) = (
	    directSum("e"=>exteriorPower(2,C_3)**C_2,"s"=>schurModule({2},C_3)**C_2),
	    exteriorPower(6,C_1)
	    );
	fs := (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(structureMap(C,3,2)**structureMap(C,3,1))
    	    *(dual wedgeProduct(4,2,C_1))
    	    );
	fe := (
    	    (id_(C_3)**wedgeProduct(1,1,C_2))
    	    *(structureMap(C,3,2)**structureMap(C,3,1))
    	    *(dual wedgeProduct(4,2,C_1))
    	    );
	E'1 := directSum("e"=>C_3**schurModule({1,1},C_2),"s"=>C_3**schurModule({2},C_2));
	d2ee := (
    	    (id_(C_3)**wedgeProduct(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *(wedgeDiag(1,1,C_3)**id_(C_2))
    	    );
	d2es := (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *(wedgeDiag(1,1,C_3)**id_(C_2))
    	    );
	d2se := (
    	    (id_(C_3)**wedgeProduct(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *((dual divProd(1,1,C_3))**id_(C_2))
    	    );
	d2ss := (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *((dual divProd(1,1,C_3))**id_(C_2))
    	    );
	f = E'1_["e"]*fe+E'1_["s"]*fs;
	g = (
    	    E'1_["e"]*d2ee*targ^["e"]
    	    +E'1_["s"]*d2es*targ^["e"]
    	    +E'1_["e"]*d2se*targ^["s"]
    	    +(-3)*E'1_["s"]*d2ss*targ^["s"]
    	    );
	);
    if (i,j) == (3,32) then (
	(targ,src) = (
	    exteriorPower(2,C_3)**C_2,
	    exteriorPower(6,C_1)
	    );
	ttarg := target structureMap(C,3,323);
	f = (ttarg^["e"])*structureMap(C,3,323);
	g = id_targ
	);
    if (i,j) == (3,33) then (
	(targ,src) = (
	    schurModule({2},C_3)**C_2,
	    exteriorPower(6,C_1)
	    );
	ttarg = target structureMap(C,3,323);
	f = (ttarg^["s"])*structureMap(C,3,323);
	g = id_targ
	);
    if (i,j) == (3,4) then (
	(targ,src) = (
	    exteriorPower(2,C_3)**C_3**C_2,
	    exteriorPower(6,C_1)**exteriorPower(2,C_1)
	    );
	f3s := (
    	    (id_(exteriorPower(2,C_3))**symProd(1,1,C_2))
    	    *(structureMap(C,3,31)**structureMap(C,3,1))
    	    *((schurModule({2,1,1,1,1},C_1)).cache#"Schur"#0**wedgeProduct(1,1,C_1))
    	    *(id_(exteriorPower(5,C_1))**flip(C_1,C_1)**id_(C_1))
    	    *(wedgeDiag(5,1,C_1)**wedgeDiag(1,1,C_1))
    	    ); --slow
	f3e := (
    	    (id_(exteriorPower(2,C_3))**wedgeProduct(1,1,C_2))
    	    *(structureMap(C,3,31)**structureMap(C,3,1))
    	    *((schurModule({2,1,1,1,1},C_1)).cache#"Schur"#0**wedgeProduct(1,1,C_1))
    	    *(id_(exteriorPower(5,C_1))**flip(C_1,C_1)**id_(C_1))
    	    *(wedgeDiag(5,1,C_1)**wedgeDiag(1,1,C_1))
    	    ); --slow
	f1s := (
    	    (id_(exteriorPower(2,C_3))**symProd(1,1,C_2))
    	    *(structureMap(C,3,32)**structureMap(C,3,1))
    	    );
	f1e := (
    	    (id_(exteriorPower(2,C_3))**wedgeProduct(1,1,C_2))
    	    *(structureMap(C,3,32)**structureMap(C,3,1))
    	    );
	f2e := (
    	    (wedgeProduct(1,1,C_3)**wedgeProduct(1,1,C_2))
    	    *(id_(C_3)**flip(C_2,C_3)**id_(C_2))
    	    *(structureMap(C,3,2)**structureMap(C,3,2))
    	    *(id_(exteriorPower(4,C_1))**wedgeProduct(2,2,C_1))
    	    *(wedgeDiag(4,2,C_1)**id_(exteriorPower(2,C_1)))
    	    );
	T := directSum(
    	    exteriorPower(2,C_3)**exteriorPower(2,C_2),
    	    exteriorPower(2,C_3)**schurModule({2},C_2)
    	    );
	f = (4/3)*T_[0]*f1e + T_[0]*f2e + 2*T_[0]*f3e + T_[1]*((4/3)*f1s - f3s);
	g = (
    	    (id_(exteriorPower(2,C_3))**(T_[1]*symProd(1,1,C_2) + T_[0]*wedgeProduct(1,1,C_2)))
    	    *(id_(exteriorPower(2,C_3))**C.dd_3**id_(C_2))
    	    );
	);
    if (i,j) == (3,5) then (
	(targ,src) = (
	    exteriorPower(2,C_3)**exteriorPower(2,C_3)**C_2,
	    exteriorPower(6,C_1)**exteriorPower(4,C_1)
	    );
	f1 = (
    	    (id_(exteriorPower(2,C_3)**C_3)**symProd(1,1,C_2))
    	    *(structureMap(C,3,4)**structureMap(C,3,1))
    	    *(id_(exteriorPower(6,C_1))**wedgeDiag(2,2,C_1))
    	    );
	f2 = (
    	    (id_(exteriorPower(2,C_3)**C_3)**symProd(1,1,C_2))
    	    *(id_(exteriorPower(2,C_3))**flip(C_2,C_3)**id_(C_2))
    	    *(structureMap(C,3,32)**structureMap(C,3,2))
    	    );
	X := flip(C_3,exteriorPower(2,C_3))*(id_(C_3)**wedgeProduct(1,1,C_3))*((dual divProd(1,1,C_3))**id_(C_3));
	f3 = (
    	    (X**symProd(1,1,C_2))
    	    *(id_(schurModule({2},C_3))**flip(C_2,C_3)**id_(C_2))
    	    *(structureMap(C,3,33)**structureMap(C,3,2))
    	    );
	f = (-1/2)*f1+f2+f3;
	g = id_(exteriorPower(2,C_3))**(
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *(wedgeDiag(1,1,C_3)**id_(C_2))
    	    );
	);
    if (i,j) == (3,6) then (
	(targ,src) = (
	    exteriorPower(2,C_3)**exteriorPower(2,C_3)**C_3**C_2,
	    exteriorPower(6,C_1)**exteriorPower(6,C_1)
	    );
	E := directSum(exteriorPower(2,C_2),schurModule({2},C_2));
	--5,1 split
	f1 = (
    	    (structureMap(C,3,5)**structureMap(C,3,1))
    	    *(id_(exteriorPower(6,C_1))**wedgeDiag(4,2,C_1))
    	    );
	--4,2 split
	f2 = (
    	    (id_(exteriorPower(2,C_3))**wedgeProduct(1,1,C_3)**id_(C_2**C_2))
    	    *(id_(exteriorPower(2,C_3)**C_3)**flip(C_2,C_3)**id_(C_2))
    	    *(structureMap(C,3,4)**structureMap(C,3,2))
    	    *(id_(exteriorPower(6,C_1))**wedgeDiag(2,4,C_1))
    	    );
	--3,3 split
	f3 = (
    	    (id_(exteriorPower(2,C_3))**flip(C_2,exteriorPower(2,C_3))**id_(C_2))
    	    *(structureMap(C,3,32)**structureMap(C,3,32))
    	    );
	f = (
    	    ((-2/3)*E_[1]*symProd(1,1,C_2) - (-1)*E_[0]*wedgeProduct(1,1,C_2))*f1
    	    +
    	    ((-1/12)*E_[1]*symProd(1,1,C_2) - (-1/4)*E_[0]*wedgeProduct(1,1,C_2))*f2
    	    +
    	    ((2/3)*E_[1]*symProd(1,1,C_2))*f3
    	    );
	g = (
    	    (id_(exteriorPower(2,C_3)**exteriorPower(2,C_3))**(
	    	    (E_[1]*symProd(1,1,C_2) + E_[0]*wedgeProduct(1,1,C_2))
	    	    *(C.dd_3**id_(C_2))
	    	    )
		)
    	    )
	);
    ------------------
    --Maps of W(d_1)--
    ------------------
    ------------------
    --Maps of W(d_2)--
    ------------------
    return (f,g,targ,src)
    )


Maps1573 = method()
Maps1573 (ChainComplex,ZZ,ZZ) := Sequence => (C,i,j) -> (
    f := null; g := null; src := null; targ := null;
    f1 := 0; f2 := 0; f3 := 0;
    ------------------
    --Maps of W(d_3)--
    ------------------
    if (i,j) == (3,3) then (
	(targ,src) = (
	    exteriorPower(2,C_3)**C_2,
	    exteriorPower(5,C_1)**C_1
	    );
	f = (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(structureMap(C,3,2)**(structureMap(C,3,1)*wedgeProduct(1,1,C_1)))
    	    *(wedgeDiag(4,1,C_1)**id_(C_1))
    	    );
	g = (
    	    (id_(C_3)**symProd(1,1,C_2))
    	    *(id_(C_3)**C.dd_3**id_(C_2))
    	    *(wedgeDiag(1,1,C_3)**id_(C_2))
    	    );
        );
    if (i,j) == (3,4) then (
	(targ,src) = (
	    exteriorPower(3,C_3)**C_2,
	    exteriorPower(5,C_1)**exteriorPower(3,C_1)
	    );
	f1 = (
    	    (wedgeProduct(1,1,C_3)**symProd(1,1,C_2))
    	    *(id_(C_3)**flip(C_2,C_3)**id_(C_2))
    	    *(structureMap(C,3,2)**structureMap(C,3,2))
    	    *(id_(exteriorPower(4,C_1))**wedgeProduct(1,3,C_1))
    	    *(wedgeDiag(4,1,C_1)**id_(exteriorPower(3,C_1)))
    	    );
	f2 = (
    	    (id_(exteriorPower(2,C_3))**symProd(1,1,C_2))
    	    *(structureMap(C,3,3)**structureMap(C,3,1))
    	    *(id_(exteriorPower(5,C_1))**wedgeDiag(1,2,C_1))
    	    );
	f = (-1/2)*f1+f2;
	g = (
    	    (id_(exteriorPower(2,C_3))**symProd(1,1,C_2))
    	    *(id_(exteriorPower(2,C_3))**C.dd_3**id_(C_2))
    	    *(wedgeDiag(2,1,C_3)**id_(C_2))
    	    );
        );
    if (i,j) == (3,5) then (
	(targ,src) = (
	    exteriorPower(3,C_3)**C_3**C_2,
	    exteriorPower(5,C_1)**exteriorPower(5,C_1)
	    );
        E := directSum("e"=>exteriorPower(2,C_2),"s"=>schurModule({2},C_2));
	g = (
    	    (id_(exteriorPower(3,C_3))**(
	    	    (E_["s"]*symProd(1,1,C_2) + E_["e"]*wedgeProduct(1,1,C_2))
	    	    *(C.dd_3**id_(C_2))
	    	    )
		)
    	    );
	f1 = (
    	    (structureMap(C,3,4)**structureMap(C,3,1))
    	    *(id_(exteriorPower(5,C_1))**wedgeDiag(3,2,C_1))
    	    ); --both e and s nonzero	 
	f2 = (
    	    (wedgeProduct(2,1,C_3)**id_(C_2**C_2))
    	    *(id_(exteriorPower(2,C_3))**flip(C_2,C_3)**id_(C_2))
    	    *(structureMap(C,3,3)**structureMap(C,3,2))
    	    *(id_(exteriorPower(5,C_1))**wedgeDiag(1,4,C_1))
    	    );
	f = (
    	    (5*E_["e"]*wedgeProduct(1,1,C_2) - 3*E_["s"]*symProd(1,1,C_2))*f1
    	    +
    	    ((-5)*E_["e"]*wedgeProduct(1,1,C_2) + E_["s"]*symProd(1,1,C_2))*f2
    	    );
        );
    return (f,g,targ,src)
    );

















-------------------
-- other methods --
-------------------

initDefectVars = method(Options => {StartingIndex => 1})
initDefectVars (ChainComplex,List) := ChainComplex => opts -> (C,dv) -> (
    S := ring C;
    frmt := (f0,f1,f2,f3) := rank\(C_0,C_1,C_2,C_3);
    ic := opts.StartingIndex; --whether to start indexing at 0 or 1
    --convert subscripts (1,2,3) to 123 for easier reading
    --I assume we won't be working with f1 >= 10 anytime soon...
    seqToNum := L -> (
	sum(#L, i -> 10^i*(reverse L)_i)
	);
    inds := L -> (
	apply(L, l -> toSequence(seqToNum\l))
	);
    --the subscripts on b match the basis order for \bigwedge^2 F_1^* \otimes F_3
    --c for wedge 2 f3
    varlist := (
	(i -> (dv_0)_i)\inds(subsets(ic..(ic+f1-1),2)**subsets(ic..(ic+f3-1),1))|
        (i -> (dv_1)_i)\inds(subsets(ic..(ic+f1-1),4)**subsets(ic..(ic+f3-1),2))
    	);
    deglist := (
	((degrees exteriorPower(2,C_1))**(degrees C_3))|
	((degrees exteriorPower(4,C_1))**(degrees exteriorPower(2,C_3)))
	);
    --for the third set of defect vars, depends if format is
    --(1,5,*,*) or (1,*,*,2)
    if (f1==5 and f3>2) then (
	varlist = varlist | (
	    (i -> (dv_2)_i)\inds(subsets(ic..(ic+f1-1),1)**subsets(ic..(ic+f3-1),3))
	    );
	deglist = deglist | (
	    ((degrees (exteriorPower(5,C_1)**C_1))**(degrees exteriorPower(3,C_3)))
	    );
	);
    if (f1>5 and f3==2) then (
	varlist = varlist | (
	    (i -> (dv_2)_i)\inds(subsets(ic..(ic+f1-1),6)**subsets(ic..(ic+f3-1),1))
	    );
	deglist = deglist | (
	    ((degrees exteriorPower(6,C_1))**(degrees (exteriorPower(2,C_3)**C_3)))
	    );
	);
    Sdef := S[varlist,Degrees => deglist/(L -> L_0-L_1),Join => false];
    -*
    Sdef := (S[
            (i -> (dv_0)_i)\(toSequence\flatten\(subsets(ic..(ic+f1-1),2)**subsets(ic..(ic+f3-1),1))),
            (i -> (dv_1)_i)\(toSequence\flatten\(subsets(ic..(ic+f1-1),4)**subsets(ic..(ic+f3-1),2))),
            Join=>false,
	    Degrees=> ((degrees exteriorPower(2,C_1))**(degrees C_3))/(L-> (
		    L_0-L_1
		    )) |
	    ((degrees exteriorPower(4,C_1))**(degrees exteriorPower(2,C_3)))/(L-> (
		    L_0-L_1
		    ))
	    ]); --Degrees=>{binomial(n,2):{0,1,0}},
    *-
    --now, to actually compute the defects
    Cdef := C**Sdef;
    usedvars := 0;
    if (f1 >= 2) then (
        defmatrix1 := genericMatrix(Sdef,Sdef_usedvars,f3,binomial(f1,2));
        usedvars = usedvars + f3*binomial(f1,2);
        structureMap(Cdef,3,1);
        Cdef.cache.StructureMapCache#(3,1) = structureMap(Cdef,3,1) + (Cdef.dd_3)*defmatrix1
        );
    if (f3 >= 2 and f1 >= 4) then (
        defmatrix2 := genericMatrix(Sdef,Sdef_usedvars,binomial(f3,2),binomial(f1,4));
        structureMap(Cdef,3,2);
        usedvars = usedvars + binomial(f3,2)*binomial(f1,4);
        Cdef.cache.StructureMapCache#(3,2) = structureMap(Cdef,3,2) + (id_(Cdef_3)**Cdef.dd_3)*(dual wedgeProduct(1,1,Cdef_3))*defmatrix2
        );
    if (f3 >= 3 and f1 == 5) then ( --currently only for 1573
	defmatrix3 := genericMatrix(Sdef,Sdef_usedvars,binomial(f3,3),f1);
	usedvars = usedvars + binomial(f3,3)*f1;
	structureMap(Cdef,3,3);
	Cdef.cache.StructureMapCache#(3,3) = structureMap(Cdef,3,3) + (
	    (id_(exteriorPower(2,C_3))**C.dd_3)
	    *wedgeDiag(2,1,C_3)
	    *defmatrix3
	    );
	);
    if (f3 == 2 and f1 >= 6) then ( --currently only for 1672
	defmatrix3 = genericMatrix(Sdef,Sdef_usedvars,f3,binomial(f1,6));
	usedvars = usedvars + f3*binomial(f1,6);
	structureMap(Cdef,3,323);
	E'2 := directSum(schurModule({1,1},C_3)**C_2,schurModule({2},C_3)**C_2);
	E'1 := directSum(C_3**schurModule({1,1},C_2),C_3**schurModule({2},C_2));
	d3e := (
    	    id_(exteriorPower(2,C_3))**C.dd_3
    	    +
    	    (1/2)**(wedgeProduct(1,1,C_3)**id_(C_2))
    	    *(id_(C_3)**flip(C_2,C_3))
    	    *(id_(C_3)**C.dd_3**id_(C_3))
    	    *(wedgeDiag(1,1,C_3)**id_(C_3))
    	    );
	d3s := (
    	    (1/2)*(symProd(1,1,C_3)**id_(C_2))
    	    *(id_(C_3)**flip(C_2,C_3))
    	    *(id_(C_3)**C.dd_3**id_(C_3))
    	    *(wedgeDiag(1,1,C_3)**id_(C_3))
    	    );
	d3 := E'2_[0]*d3e+E'2_[1]*d3s;
    	Cdef.cache.StructureMapCache#(3,323) = structureMap(Cdef,3,323) + d3*defmatrix3;
	);
    return Cdef
    )

topComplex = method()
topComplex ChainComplex := ChainComplex => C -> (
    S := ring C;
    frmt := ((C_0,C_1,C_2,C_3)/rank);
    if frmt == (1,rank C_1,rank C_1,1) then (
        if debugLevel > 0 then << "format: (1,n,n,1)" << endl;
        n := rank C_1;
        --F_1^* -> \wedge^{n-1}F_1 -> S_{n/2-1}F_3
        dtop1 := structureMap(C,1,n//2-1)*adjoint(wedgeProduct(1,n-1,C_1),C_1,exteriorPower(n-1,C_1));
        dtop1 = map(S^1,,dtop1);
        --F_2 -> F_1^* \otimes F_3
        dtop2 := adjoint(structureMap(C,2,1)*flip(C_2,C_1),C_2,C_1);
        dtop2 = map(source dtop1,,dtop2);
        --\wedge^n F_1 -> S_{n/2-1}F_3 \otimes F_2
        dtop3 := structureMap(C,3,n//2);
        dtop3 = map(source dtop2,,dtop3);
        ) else
    if frmt == (1,4,3 + rank C_3, rank C_3) then (
        if debugLevel > 0 then << "format: (1,4,m+3,3)" << endl;
        m := rank C_3;
        --dual( F_1 or \wedge^3 F_1 )-> \wedge^m F_3
        dtop1 = structureMap(C,1,m)*adjoint(wedgeProduct(3,1,C_1),exteriorPower(3,C_1),C_1);
        dtop1 = map(S^1,,dtop1);
        --F_2 -> dual (F_1 or \wedge^3 F_1) 
        dtop2 = dual adjoint(structureMap(C,2,m),C_1,C_2);
        dtop2 = map(source dtop1,,dtop2);
        --
        dtop3 = adjoint'(structureMap(C,3,2),C_3,C_2);
        dtop3 = map(source dtop2,,dtop3);
        ) else
    if frmt == (1,5,6,2) then (
	if debugLevel > 0 then << "format: (1,5,6,2)" << endl;
	--F_1* -> R
	dtop1 = structureMap(C,1,4)*adjoint(wedgeProduct(1,4,C_1),C_1,exteriorPower(4,C_1));
	dtop1 = map(S^1,,dtop1);
	--F_2* -> F_1*
	dtop2 = dual structureMap(C,3,3);
        dtop2 = map(source dtop1,,dtop2);
	--F_3* -> F_2*
	dtop3 = dual structureMap(C,2,3);
	dtop3 = map(source dtop2,,dtop3);
	) else error "Ftop not yet implemented for this format";
    return chainComplex(dtop1,dtop2,dtop3)
    )

beginDocumentation()

doc ///
    Key
        HigherStructureMaps
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
            which has kernel $F_3 \to F_2$. See @TO initDefectVars@ for handling
            this indeterminacy.
        Example
            S = QQ[x,y,z];
            I = ideal(-x^2+x*y-y^2+x*z-2*y*z, -x*y+y*z, -y^2-y*z, x^2+x*y+y^2+y*z);
            C = res I;
            structureMap(C,3,1)
///

doc ///
    Key
        initDefectVars
        (initDefectVars,ChainComplex,List)
    Headline
        introduce defect variables
    Usage
        initDefectVars(C,L)
    Inputs
    	C: ChainComplex
	    an exact sequence $0 \to F_3 \to F_2 \to F_1 \to F_0$
	L: List
	    of @TO IndexedVariableTable@s
    Outputs
    	: ChainComplex
    Description
    	Text
	    (The subscript organization convention for this work-in-progress method is still placeholder,
	    and it currently only handles $v^{(3)}_1$ and $v^{(3)}_2$, i.e. formats with two
	    nonzero graded pieces of the defect Lie algebra.)
	
	    In defining the maps $w^{(3)}_j$ some of the lifts involved are not unique,
	    which is reflected in the defect Lie algebra. This method introduces auxiliary
	    variables to keep track of this non-uniqueness.
	Example
	    S = QQ[x,y];
	    C = (chainComplex id_(S^3))[-2] ++ res (ideal(x,y))^(3)
	    structureMap(C,3,1)
	Text
	    This is one choice of multiplication
	    $w^{(3)}_1\colon\bigwedge^2 F_1 \to F_2$, but it
	    is not unique.
	    
	    The below computes $v^{(3)}_1$, and other choices of $w^{(3)}_1$ are obtained by specializing the
	    variables $b$.
	Example
	    Cdef = initDefectVars(C,{b,c}); Sdef = ring Cdef;
	    Cdef
	    structureMap(Cdef,3,1)
	Text
	    For this format, more defect variables are introduced in
	    computing $v^{(3)}_2$:
	Example
	    structureMap(Cdef,3,2)
	Text
	    The method assigns degrees to the adjoined variables in an attempt to keep things
	    homogeneous.
	Example
	    degree b_(12,1)
    Caveat
    	It seems like there may currently be an issue with the heft vector of {\tt Sdef}.
///

doc ///
    Key
    	topComplex
	(topComplex,ChainComplex)
    Headline
    	top complex for a Dynkin format
    Usage
    	Ftop(C)
    Inputs
    	C: ChainComplex
	    an exact sequence $0 \to F_3 \to F_2 \to F_1 \to F_0$
    Outputs
    	: ChainComplex
    Description
    	Text
	    When the T-shaped graph associated to the format of $C$ is Dynkin, the representations
	    corresponding to the three extremal vertices of the graph are finite-dimensional
	    and there are maps $w^{(1)}_\text{top},w^{(2)}_\text{top},w^{(3)}_\text{top}$
	    corresponding to the top graded components. These maps assemble into a complex,
	    which this method computes.
	    
	    Note that if you want the top complex computed with defect variables, you must
	    use @TO initDefectVars@ first.
	Example
	    S = QQ;
	    C = (chainComplex id_(S^1)) ++ (chainComplex (-1*(id_(S^3))))[-1] ++ (chainComplex id_(S^1))[-2]
	    Cdef = initDefectVars(C,{b}); Sdef = ring Cdef;
	    (topComplex(Cdef)).dd
///
	    
--tests still need to be written

end--
uninstallPackage "HigherStructureMaps"
restart

------------------------
-- example code below --
------------------------
installPackage "HigherStructureMaps"

debugLevel = 1 --to check if liftings succeed

--split exact complex with defect variables, with "usual" grading |b| = 1, |c| = 2, etc.
frmt = (1,5,6,2)
S = QQ[x]
C = chainComplex(-id_(S^(frmt_1-1)))[-1] ++ chainComplex(id_(S^1)) ++ chainComplex(id_(S^{(frmt_3):1}))[-2]
C.dd
Cdef = initDefectVars(C,{b,c,d}); Sdef = ring Cdef;
structureMap(Cdef,3,1)
degree b_(12,1)
degree c_(1234,12)

Ctop = topComplex Cdef; --only implemented for formats up to E_6


--1672 example of interest
S = ZZ/32003[x_1, x_2, x_3];
I = ideal(x_2^2*x_3-2*x_1*x_3^2+x_2*x_3^2,x_1*x_2*x_3-x_1*x_3^2,x_1^2*x_3-x_1*x_3^2,x_1^2*x_2+x_1*x_2^2-2*x_1*x_3^2,x_1*x_2^3+4
*x_1*x_3^3-x_2*x_3^3-3*x_3^4,x_1^7-x_2^7,x_1^8,x_2^8,x_3^6)

C = res I
structureMap(C,3,1);

defpart = C.dd_3*matrix{
    {1,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    {0,0,0,0,0,1,0,0,0,0,0,0,0,0,0}};

C.cache.StructureMapCache#(3,1) = structureMap(C,3,1)+defpart;
structureMap(C,3,6);
delta3 = adjoint'(structureMap(C,3,6),dual (S**C_3),(S**C_2));

--delta3 is a split inclusion:
1%(ideal exteriorPower(2,delta3))

--another check
splitting = dual(id_(target dual delta3) // dual(delta3))
splitting*delta3
