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
