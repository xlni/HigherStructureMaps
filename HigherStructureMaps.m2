newPackage(
        "HigherStructureMaps",
        Version => "0.1", 
        Date => "October 30, 2021",
        Authors => {
             {Name => "Xianglong Ni", Email => "xlni@berkeley.edu"}
             },
        HomePage => "http://math.berkeley.edu/~xlni/",
        Headline => "higher structure maps",
        AuxiliaryFiles => true -- set to true if package comes with auxiliary files
        )

-- Any symbols or functions that the user is to have access to
-- must be placed in one of the following two lists
export {
    "structureMap",
    "StructureMapCache",
    "initDefectVars",
    "StartingIndex",
    "topComplex"
    }
exportMutable {}

load "./HigherStructureMaps/FromRST.m2" --some methods from the main package

--compute the map w^(i)_j
structureMap = method()
structureMap (ChainComplex,ZZ,ZZ) := Matrix => (C,i,j) -> (
    if not C.cache.?StructureMapCache then C.cache.StructureMapCache = new MutableHashTable;
    if C.cache.StructureMapCache#?(i,j) then return C.cache.StructureMapCache#(i,j);
    frmt := ((C_0,C_1,C_2,C_3)/rank);
    f := null; g := null; src := null; targ := null;
    -------------------------------------
    --differentials of original complex--
    -------------------------------------
    if j == 0 then (
        if member(i,{1,2,3}) then (
            return C.cache.StructureMapCache#(i,j) = C.dd_i
            )
        ) else
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
        ); -- else
--    if frmt == (1,5,6,2) then ( --The 1562 code is still using old organization and needs to be updated before this is enabled!
--      (f,g,targ,src) = Maps1562(C,i,j)
--      );
    --at this point, f and g should have been computed, where f is to be lifted through g
    if f === null then error "invalid structure map specified";
    v := f // map(target f, source g, g);
    if debugLevel > 0 and (entries (g*v) != entries f) then error "lifting failed";
    if src === null then (
        return C.cache.StructureMapCache#(i,j) = v --this should eventually be deleted
        ) else (
        return C.cache.StructureMapCache#(i,j) = map(targ,src,v)
        )
    )

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
                (id_(exteriorPower(j-1,C_3))**structureMap(C,3,1))
                *(structureMap(C,1,j-1)**wedgeProduct(1,1,C_1))
                *((dual wedgeProduct(3,1,C_1))**(id_(C_1)))
                + --check sign?
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
                + --check sign?
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
                + --check signs?
                (wedgeProduct(j-2,1,C_3)**id_(C_2))
                --needed an exception for the following line in the case j=2
                *(structureMap(C,2,j-2)**structureMap(C,3,2))
                + --ditto
                (structureMap(C,1,j-1)**id_(C_2))
                );
            ) else (
            (targ,src) = (
                exteriorPower(j,C_3),
                fold(tensor,apply(j//2,i->(exteriorPower(4,C_1))))**C_1**C_2
                );
            f = (
                flip(C_2,exteriorPower(j-1,C_3))
                *(structureMap(C,3,1)**id_(exteriorPower(j-1,C_3)))
                *(wedgeProduct(1,1,C_1)**structureMap(C,2,j-1))
                *(id_(C_1)**(dual wedgeProduct(1,3,C_1))**id_(C_2))
                + --check signs?
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
        g = (
            (id_(symmetricPower(j-2,C_3))**symProd(1,1,C_2))
            *(
                ((id_(symmetricPower(j-2,C_3))**C.dd_3)*(dual divProd(j-2,1,C_3)))
                **(id_(C_2))
                )
            )
        );
    if (i == 1 and j > 1) then (
        (targ,src) = (symmetricPower(j,C_3),exteriorPower(2*j+1,C_1));
        f = (
            (C.dd_1**structureMap(C,3,j))
            *(dual wedgeProduct(1,2*j,C_1))
            );
        g = (id_(symmetricPower(j-1,C_3))**C.dd_3)*(dual divProd(j-1,1,C_3))
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
            *(Maps1562(C,2,3)**Maps1562(C,1,3))
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
    if (i,j) == (21,1) then (
        f = (Maps1562(C,1,1)**Maps1562(C,1,3))*(transpose wedgeProduct(3,2,C_1));
        g = (id_(C_3)**C.dd_3)*(matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}}); --matrix is S2 -> T2
        );
    if (i,j) == (22,1) then (
        f = (
            ((Maps1562(C,1,1)**Maps1562(C,1,3))*(transpose wedgeProduct(3,2,C_1)))
            + (-2)*(C.dd_1 ** Maps1562(C,2,3))*(transpose wedgeProduct(1,4,C_1))
            );
        g = (id_(C_3)**C.dd_3)*(transpose wedgeProduct(1,1,C_3))
        );
    if (i,j) == (3,1) then (
        f1 = ((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}}) ** id_(C_2))*(Maps1562(C,21,1)**Maps1562(C,1,3));
        f2 = (
            (((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*symProd(1,1,C_3))**id_(C_2))
            *(flip(C_3**C_2,C_3))
            *(Maps1562(C,2,3)**(Maps1562(C,1,2)*(id_(C_1)**Maps1562(C,1,3))))
            *((transpose wedgeProduct(4,1,C_1))**id_(exteriorPower(2,C_1))));
        g = (
            (((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*symProd(1,1,C_3))**C.dd_3)
            *(id_(C_3)**(transpose wedgeProduct(1,1,C_3)))
            *(flip(exteriorPower(2,C_3),C_3)));
        f = f1-f2
        );
    if (i,j) == (4,1) then (
        f1 = ((Maps1562(C,3,1)**Maps1562(C,1,3))
            *(id_(exteriorPower(5,C_1))**(transpose wedgeProduct(2,2,C_1))));
        f2 = (
            (id_(exteriorPower(2,C_3))**flip(C_2,C_3))
            *(Maps1562(C,3,3)**Maps1562(C,1,1))
            *(id_(exteriorPower(5,C_1))**(transpose wedgeProduct(1,3,C_1))));
        f3 = (
            (Maps1562(C,22,1)**Maps1562(C,2,3))
            );
        f = f1+f2-f3;
        g = id_(exteriorPower(2,C_3))**((id_(C_3)**C.dd_3)*(transpose wedgeProduct(1,1,C_3)))
        );
    ------------------
    --Maps of W(d_2)--
    ------------------
    if (i,j) == (2,2) then (
        f = (
            (Maps1562(C,1,2)**Maps1562(C,1,3))*(flip(C_2,C_1)**id_(exteriorPower(2,C_1)))*(id_(C_2)**(transpose wedgeProduct(1,2,C_1)))
            +
            (Maps1562(C,2,3)*wedgeProduct(3,1,C_1)*(id_(exteriorPower(3,C_1))**C.dd_2))*flip(C_2,exteriorPower(3,C_1))
            -
            (Maps1562(C,1,1)**id_(C_2))*flip(C_2,exteriorPower(3,C_1))
            );
        g = (id_(C_3)**C.dd_3)*(transpose wedgeProduct(1,1,C_3))
        );
    if (i,j) == (3,2) then (
        f1 = (
            ((
                    --(matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})*
                    symProd(1,1,C_3))**id_(C_2))*
            ((Maps1562(C,1,2)*flip(C_2,C_1))**(Maps1562(C,2,3)))
            *(id_(C_2)**(transpose wedgeProduct(1,4,C_1)))
            );
        f2 = ( --no halving?
            --((matrix{{2,0,0},{0,1,0},{0,1,0},{0,0,2}})**id_(C_2))*
            ((Maps1562(C,21,1)) ** id_(C_2))
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

initDefectVars = method(Options => {StartingIndex => 1})
initDefectVars (ChainComplex,List) := ChainComplex => opts -> (C,dv) -> (
    S := ring C;
    f3 := rank C_3;
    f2 := rank C_2; f1 := rank C_1;
    ic := opts.StartingIndex; --whether to start indexing at 0 or 1
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
    --the subscripts on b match the basis order for \bigwedge^2 F_1^* \otimes F_3
    --c for wedge 2 f3
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
        Ctop := chainComplex(dtop1,dtop2,dtop3)
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
        Ctop = chainComplex(dtop1,dtop2,dtop3)
        ) else error "Ftop not yet implemented for this format";
    return Ctop
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
	    degree b_(1,2,1)
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
installPackage "HigherStructureMaps"
viewHelp "HigherStructureMaps"

--------------------------------------------------------
--manufacturing "simple" resolutions of desired format--
--------------------------------------------------------

n=4
S = QQ[x,y,z]
d3 = dual matrix{{x,y,z,0}} --n by 1 matrix, must be at least grade 3
F2 = target d3
d3wedge = wedgeProduct(1,1,F2)*(d3**id_F2)

--repeatedly randomly project until a valid choice is found
prjdeg = 1 --degree of projection map wedge^2 F2 -> F1
while true do (
    prj = random(S^{n:prjdeg}, S^{binomial(n,2):0},
        Density=>0.3,Height => 1); --tweakable
    d2 = prj*d3wedge;
    if (rank d2 == n-1) and (codim ideal exteriorPower(rank d2,d2) >= 2) then break
    )
d1 = dual gens ker dual d2
assert((ker d1 == image d2) and (ker d2 == image d3))

--fix degrees
d1 = map(S^1,,d1); d2 = map(source d1,,d2); d3 = map(source d2,,d3);

C = chainComplex(d1,d2,d3)
C.dd
betti C
--if all went well, that should produce a computationally simple res of format 1,4,4,1

structureMap(C,3,1) --w^(3)_1
Cdef = initDefectVars(C,{b});
S' = ring Cdef
structureMap(Cdef,3,1) --v^(3)_1

C' = topComplex Cdef
prune HH C'
betti(C',Weights=>{1})
--seems like HH_1,2,3 = 0 in the examples I've done,
--even though the starting ideal was not perfect

C'' = topComplex initDefectVars(C',{b'})

S'' = ring C''
prune HH C''
betti(C'',Weights=>{1})

C''**S''/ideal((vars ring C')**S'') --kill first set of defvars; also exact
C''**S''/ideal(vars S'') --kill second set of defvars; original complex, up to sign

--investigating the last phenomenon more:
--no defect variables for second iteration, i.e. b' set to 0
structureMap(C',3,0)
structureMap(Cdef,3,2)

structureMap(C',3,1)
structureMap(Cdef,3,1)

structureMap(C',3,2)
structureMap(Cdef,3,0)


structureMap(C',2,0)
structureMap(Cdef,2,1) --well, shape needs adjusting

structureMap(C',2,1) --ditto
structureMap(Cdef,2,0)


structureMap(C',1,0)
structureMap(Cdef,1,1)

structureMap(C',1,1)
structureMap(Cdef,1,0)
