
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

