newPackage(
	"PFProjBundle",
	Version => "1.0", 
    	Date => "March 10, 2016",
    	Authors => {{Name => "Martin Helmer", 
		  Email => "martin.helmer@berkeley.edu", 
		  HomePage => "https://math.berkeley.edu/~mhelmer/"}},
    	Headline => "Computes a Pushforward formula in some projective bundles",
    	DebuggingMode => false,
	Reload => true
    	);
export{"PushForward",
       "TaylorCoeffs",
       "qdiff",
       "FindQ",
       "ChQFromr"
    }
qdiff=method(TypicalValue=>RingElement);
qdiff(RingElement,RingElement):=(var,rational)->(
    print var;
    if not instance(ring(rational),FractionField) then(
	dee:=diff(var,rational);
	print "reg diff done";	
	return dee;
	);
    num:=numerator(rational);
    denom:=denominator(rational);
    R:=ring(num);
    if num==0 or num==0_R then return 0_R;
    var=substitute(var,R);
    Dnum:=diff(var,num);
    Ddenom:=diff(var,denom);
    Drational:=(Dnum*denom-Ddenom*num)/(denom^2);
    return Drational;
    );
qdiff(RingElement,RingElement,ZZ):=(var,rational,n)->(
    if n<1 then return rational;
    ans:=qdiff(var,rational);
    for i from 2 to n do(
	ans=qdiff(var,ans);
	);
    return ans;
    );
TaylorCoeffs=method(TypicalValue=>List);
TaylorCoeffs(RingElement,RingElement,ZZ):=(f,z,n)->(
    df:=f;
    val:=0;
    zbar:=substitute(z,ring(f));
    tayList:={sub(df,{zbar=>0})};
    for i from 1 to n-1 do(
	df=qdiff(z,df);
	val=sub(df,{zbar=>0})/(i!);
	tayList=append(tayList,val);
	);
    return tayList;
    );
ElePushForward=method(TypicalValue=>RingElement);
ElePushForward(List,RingElement):=(CEList,alpha)->(
    z:=CEList_0;
    Ls:=CEList_1;
    LPows:=CEList_2;
    rankE:=CEList_3;
    n:=rankE-1;
    A:=ring(alpha);
    R:=ring(z);
    kk:=coefficientRing(R);
    m:=#Ls;
    aPF:=0;
    a:=TaylorCoeffs(alpha,z,n);
    Galpha:=(alpha-sum(0..(n-1),i->a_i*z^i))/(z^(n-m+1));
    v:=0;
    S:=0;
    Lbars:=for l in Ls list substitute(l,ring(Galpha));
    zbar:=substitute(z,ring(Galpha));
    if sum(LPows)==m then(
	S=sum(m,i->sub(Galpha,{zbar=>-Lbars_i})/product(delete(Lbars_i,Lbars),L->-Lbars_i+L));
	aPF=S;
	)
    else(
	w:=symbol w;
	R1:=kk[w_0..w_(m-1),gens(R)];
	GaR1:=substitute(numerator(Galpha),R1)/substitute(denominator(Galpha),R1);
	wbars:=for l in (gens(R1))_{0..m-1} list substitute(l,ring(GaR1));
	lR1bars:=for l in Ls list substitute(l,ring(GaR1));
	zb:=substitute(substitute(z,R1),ring(GaR1));
	S=sum(m,i->sub(GaR1,{zb=>w_i})/product(delete(wbars_i,wbars),L->wbars_i-L));
	aPF=S;
	for i from 0 to m-1 do(
	    v=LPows_i-1;
	    if v>0 then(
		temp1:=(((wbars_i)^v)*aPF)/(v!);
	    	aPF=qdiff(wbars_i,temp1,v);
	    	);
	    );
	for i from 0 to m-1 do(
	    aPF=sub(aPF,{wbars_i=>-lR1bars_i});
	    );
	aPF=substitute(aPF,ring(Galpha));
	);
    return aPF;
    );
FindQ=method(TypicalValue=>RingElement);
FindQ (List,RingElement):=(CEList,Yclass)->(
    z:=CEList_0;
    Ls:=CEList_1;
    LPows:=CEList_2;
    rankE:=CEList_3;
    r:=rankE-sum(LPows);
    alpha:=(1+z)^r*product(#Ls,i->(1+Ls_i+z)^(LPows_i))*Yclass/(1+Yclass);
    Q:=ElePushForward(CEList,alpha);
    use(ring(Ls_0));
    return Q;
    );

FindQ (ZZ):=(Ran)->(
    z:=symbol z;
    L:=symbol L;
    a:=symbol a;
    d:=symbol d;
    m:=Ran-1;
    R:=QQ[z,L_1..L_m,a,d];
    Ls:=toList(L_1..L_m);
    LPows:=for j in Ls list 1;
    RankE:=Ran;
    CE:={z,Ls,LPows,RankE};
    Y:=d*z+a;
    return FindQ(CE,Y);
    );

TEST ///
{*  
    --Table 3.1
    --Example 1:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)(1+S)=(1+2*L)(1+3*L)
    --i.e we will sub in at the end
    R=ZZ[L,S,z];
    --names of variables
    Ls={L,S}
    --exponants 
    ks={1,1}
    RankE=3
    CE={z,Ls,ks,RankE}
    --class of Y, [Y], note L=>3L at the end, so we write 2L here
    --which will become 6L later
    Y=3*z+2*L;
    pf3=FindQ(CE,Y)
    fR=ring(pf3)
    l=substitute(L,fR)
    s=substitute(S,fR)
    --put constansts back in
    as=sub(pf3,{s=>2*l,l=>3*l})
    factor numerator(as)
    factor denominator(as)
///

TEST ///
{*  
    --Table 3.1
    --Example 2:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)(1+S)
    R=ZZ[L,S,z];
    --names of variables
    Ls={L,S}
    --exponants 
    ks={1,1}
    RankE=3
    CE={z,Ls,ks,RankE}
    --class of Y, [Y]
    Y=3*z+2*L+S;
    pf3=FindQ(CE,Y)
    factor numerator(pf3)
    factor denominator(pf3)
///

TEST ///
{*  
    --Table 3.1
    --Example 3:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)(1+S)
    R=ZZ[L,S,z];
    --names of variables
    Ls={L,S}
    --exponants 
    ks={1,1}
    RankE=3
    CE={z,Ls,ks,RankE}
    --class of Y, [Y]
    Y=3*z+4*L;
    pf3=FindQ(CE,Y)
    fR=ring(pf3)
    l=substitute(L,fR)
    s=substitute(S,fR)
    as=sub(pf3,{s=>2*l})
    factor numerator(as)
    factor denominator(as)
///

TEST ///
{*  
    --Table 3.1
    --Example 4:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)^3
    R=ZZ[L,z];
    --names of variables
    Ls={L}
    --exponants 
    ks={3}
    RankE=4
    CE={z,Ls,ks,RankE}
    --class of Y, [Y]
    Y=3*z+3*L;
    pf3=FindQ(CE,Y)
    fR=ring(pf3)

///

TEST ///
{*  
    --Table 3.1
    --Example 5:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)^3
    R=ZZ[L,z];
    --names of variables
    Ls={L}
    --exponants 
    ks={3}
    RankE=4
    CE={z,Ls,ks,RankE}
    --class of Y, [Y]
    Y=4*z+4*L;
    pf3=FindQ(CE,Y)
    fR=ring(pf3)
    factor numerator(pf3)
    factor denominator(pf3)
///

TEST ///
{*  
    --Table 3.1
    --Example 6:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)^3
    R=ZZ[L,z];
    --names of variables
    Ls={L}
    --exponants 
    ks={3}
    RankE=4
    CE={z,Ls,ks,RankE}
    --class of Y, [Y]
    Y=5*z+5*L;
    pf3=FindQ(CE,Y)
    fR=ring(pf3)
    factor numerator(pf3)
    factor denominator(pf3)
///
TEST ///
{*  
    --Table 3.1
    --Example 7:
    restart
    needsPackage "PFProjBundle"
*}

    ----E=(1+L)^4
    R=ZZ[L,z];
    --names of variables
    Ls={L}
    --exponants 
    ks={4}
    RankE=5
    CE={z,Ls,ks,RankE}
    --class of Y, [Y]
    Y=5*z+5*L;
    pf3=FindQ(CE,Y)
    fR=ring(pf3)
    factor numerator(pf3)
    factor denominator(pf3)
///

