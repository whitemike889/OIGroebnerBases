doc ///
    Key
        OIGroebnerBases
    Headline
        Computation in OI-modules over Noetherian polynomial OI-algebras
    Description
        Text
            This package allows one to compute Gröbner bases, syzygies and free resolutions for submodules of free OI-modules over Noetherian polynomial OI-algebras.
        Text
            Given a Noetherian polynomial OI-algebra $\mathbf{P} := (\mathbf{X}^{\text{OI},1})^{\otimes c}$ for some integer $c > 0$, one can consider free OI-modules $\mathbf{F} := \bigoplus_{i=1}^s\mathbf{F}^{\text{OI}, d_i}$ over $\mathbf{P}$ for integers $d_i\geq 0$. If $\mathbf{M}$ is a $\mathbf{P}$-submodule of $\mathbf{F}$ generated by $B=\{b_1,\ldots,b_t\}$, then a finite Gröbner basis can be computed from $B$ using @TO oiGB@. Furthermore, one can compute syzygies and resolutions with respect to $B$ using @TO oiSyz@ and @TO oiRes@. In this documentation we often use the terms OI-Gröbner basis and Gröbner basis interchangeably.
        Text
            For an introduction to the theory of OI-modules and OI-resolutions, we refer the reader to the @TO "Bibliography"@.
    Subnodes
        :Polynomial OI-algebras
        PolynomialOIAlgebra
        makePolynomialOIAlgebra
        getAlgebraInWidth
        (net,PolynomialOIAlgebra)
        (toString,PolynomialOIAlgebra)
        (symbol _,PolynomialOIAlgebra,ZZ)
        :Free OI-modules
        FreeOIModule
        makeFreeOIModule
        getFreeModuleInWidth
        (net,FreeOIModule)
        (toString,FreeOIModule)
        (symbol _,FreeOIModule,ZZ)
        getGenWidths
        DegreeShifts
        getDegShifts
        installBasisElements
        makeMonic
        :Maps between free OI-modules
        FreeOIModuleMap
        makeFreeOIModuleMap
        (net,FreeOIModuleMap)
        (symbol SPACE,FreeOIModuleMap,List)
        (isHomogeneous,FreeOIModuleMap)
        (source,FreeOIModuleMap)
        (target,FreeOIModuleMap)
        :Algorithms
        oiGB
        isOIGB
        oiSyz
        MinimalOIGB
        :OI-resolutions
        OIResolution
        oiRes
        isComplex
        (describe,OIResolution)
        (net,OIResolution)
        (symbol _,OIResolution,ZZ)
        :Miscellaneous
        "Bibliography"
///

doc ///
    Key
        "Bibliography"
    Headline
        Bibliography for the OIGroebnerBases package
    Description
        Text
            [NR] U. Nagel and T. Römer, {\it FI- and OI-modules with varying coefficients}, J. Algebra {\bf 535} (2019), 286-322.

            [FN] N. Fieldsteel and U. Nagel, {\it Minimal and cellular free resolutions over polynomial OI-algebras}, Preprint, arXiv:2105.08603, 2021.
///

doc ///
    Key
        PolynomialOIAlgebra
    Headline
        The class of all Noetherian polynomial OI-algebras over a field
    Description
        Text
            This type implements OI-algebras of the form $(\mathbf{X}^{\text{OI},1})^{\otimes c}$ for some integer $c>0$. To make a new @TT "PolynomialOIAlgebra"@ use @TO makePolynomialOIAlgebra@. To get the $K$-algebra in a specific width of a polynomial OI-algebra, use @TO getAlgebraInWidth@.

            Each @TT "PolynomialOIAlgebra"@ object carries the lexicographic monomial order determined by $x_{i,j}>x_{i',j'}$ iff $j>j'$ or $j=j'$ and $i>i'$.
///

doc ///
    Key
        makePolynomialOIAlgebra
        (makePolynomialOIAlgebra,Ring,ZZ,Symbol)
    Headline
        Make a new PolynomialOIAlgebra object
    Usage
        makePolynomialOIAlgebra(K,c,x)
    Inputs
        K:Ring
        c:ZZ
        x:Symbol
    Outputs
        :PolynomialOIAlgebra
    Description
        Text
            Makes a new @TO PolynomialOIAlgebra@ object implementing the functor $(\mathbf{X}^{\text{OI}, 1})^{\otimes c}$ over $K$ with variables in $x$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x)
            Q = makePolynomialOIAlgebra(QQ,2,y)
///

doc ///
    Key
        getAlgebraInWidth
        (getAlgebraInWidth,PolynomialOIAlgebra,ZZ)
    Headline
        Get the $K$-algebra in a specified width of a polynomial OI-algebra
    Usage
        getAlgebraInWidth(P,n)
    Inputs
        P:PolynomialOIAlgebra
        n:ZZ
    Outputs
        :PolynomialRing
    Description
        Text
            Returns the width $n$ component of a @TO PolynomialOIAlgebra@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            getAlgebraInWidth(P, 3)
            Q = makePolynomialOIAlgebra(QQ,2,y);
            getAlgebraInWidth(Q, 4)            
///

doc ///
    Key
        (toString,PolynomialOIAlgebra)
    Headline
        Convert a PolynomialOIAlgebra object to a string
    Usage
        toString P
    Inputs
        P:PolynomialOIAlgebra
    Outputs
        :String
    Description
        Text
            Outputs the base field, number of variable rows and variable symbol of a @TO PolynomialOIAlgebra@ object.
        Example
            Q = makePolynomialOIAlgebra(QQ,2,y);
            toString Q
///

doc ///
    Key
        (net,PolynomialOIAlgebra)
    Headline
        Display extended information about a PolynomialOIAlgebra object
    Usage
        net P
    Inputs
        P:PolynomialOIAlgebra
    Outputs
        :Net
    Description
        Text
            Outputs the base field, number of variable rows and variable symbol of a @TO PolynomialOIAlgebra@ object in extended format.
        Example
            Q = makePolynomialOIAlgebra(QQ,2,y);
            net Q
///

doc ///
    Key
        (symbol _,PolynomialOIAlgebra,ZZ)
    Headline
        Get the $K$-algebra in a specified width of a polynomial OI-algebra
    Usage
        P_n
    Inputs
        P:PolynomialOIAlgebra
        n:ZZ
    Outputs
        :PolynomialRing
    Description
        Text
            This is a shortcut version of @TO getAlgebraInWidth@.
        Example
            Q = makePolynomialOIAlgebra(QQ,2,y);
            Q_4
///

doc ///
    Key
        FreeOIModule
    Headline
        The class of all free OI-modules over a polynomial OI-algebra
    Description
        Text
            This type implements free OI-modules $\mathbf{F} := \bigoplus_{i=1}^s\mathbf{F}^{\text{OI}, d_i}$ over a @TO PolynomialOIAlgebra@ object $\mathbf{P}$ for integers $d_i\geq 0$. To make a new @TT "FreeOIModule"@ object use @TO makeFreeOIModule@. To get the free module in a specific width of a free OI-module, use @TO getFreeModuleInWidth@. One may also obtain the generator widths and degree shifts using @TO getGenWidths@ and @TO getDegShifts@ respectively.

            Each @TT "FreeOIModule"@ object carries either the @TO Lex@ monomial order determined by the monomial order of $\mathbf{P}$, or a Schreyer monomial order induced by a @TO FreeOIModuleMap@.
///

doc ///
    Key
        makeFreeOIModule
        (makeFreeOIModule,PolynomialOIAlgebra,Symbol,List)
        [makeFreeOIModule,DegreeShifts]
    Headline
        Make a new FreeOIModule object
    Usage
        makeFreeOIModule(P, e, W)
    Inputs
        P:PolynomialOIAlgebra
        e:Symbol
        W:List
    Outputs
        :FreeOIModule
    Description
        Text
            Makes a new @TO FreeOIModule@ object over the @TO PolynomialOIAlgebra@ $\mathbf{P}$ with basis symbol $e$ and generator widths given by @TT "W"@.

            The option @TT "DegreeShifts"@ allows one to specify a shift of grading.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2})
///

doc ///
    Key
        getFreeModuleInWidth
        (getFreeModuleInWidth,FreeOIModule,ZZ)
    Headline
        Get the free module in a specified width of a free OI-module
    Usage
        getFreeModuleInWidth(F, n)
    Inputs
        F:FreeOIModule
        n:ZZ
    Outputs
        :Module
    Description
        Text
            Returns the width $n$ component of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            getFreeModuleInWidth(F, 1)
            getFreeModuleInWidth(F, 3)
///

doc ///
    Key
        (toString,FreeOIModule)
    Headline
        Convert a FreeOIModule object to a string
    Usage
        toString F
    Inputs
        F:FreeOIModule
    Outputs
        :String
    Description
        Text
            Outputs the generator widths and degree shifts of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            toString F
///

doc ///
    Key
        (net,FreeOIModule)
    Headline
        Display extended information about a FreeOIModule object
    Usage
        net F
    Inputs
        F:FreeOIModule
    Outputs
        :Net
    Description
        Text
            Outputs the underlying @TO PolynomialOIAlgebra@ object, the basis symbol, the generator widths, the degree shifts and the monomial order of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            net F
///

doc ///
    Key
        getGenWidths
        (getGenWidths,FreeOIModule)
    Usage
        getGenWidths F
    Inputs
        F:FreeOIModule
    Outputs
        :List
    Description
        Text
            Outputs the @TO List@ of generator widths of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            getGenWidths F
///

doc ///
    Key
        getDegShifts
        (getDegShifts,FreeOIModule)
    Usage
        getDegShifts F
    Inputs
        F:FreeOIModule
    Outputs
        :List
    Description
        Text
            Outputs the @TO List@ of degree shifts of a @TO FreeOIModule@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            getDegShifts F
///

doc ///
    Key
        (symbol _,FreeOIModule,ZZ)
    Usage
        F_n
    Inputs
        F:FreeOIModule
        n:ZZ
    Outputs
        :Module
    Description
        Text
            This is a shortcut version of @TO getFreeModuleInWidth@.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            F_1
            F_3         
///

doc ///
    Key
        installBasisElements
        (installBasisElements,FreeOIModule,ZZ)
    Usage
        installBasisElements(F,n)
    Inputs
        F:FreeOIModule
        n:ZZ
    Description
        Text
            Suppose $\mathbf{F}$ is a free OI-module with basis symbol $e$ and generator widths $\{d_1=1,d_2=2\}$. Then the local basis elements in width $n$ are represented as @TT "e_(n,{...},i)"@ where @TT "{...}"@ describes an OI-morphism from $[d_i]$ to $[n]$. For example, $e_{(5,\{2,4\},2)}$ is the local basis element in $\mathbf{F}_5$ given by $$\mathbf{F}(\pi)(e_{\text{id}_{[d_2]=[2]}})$$ where $\pi:[2]\to[5]$ is the OI-morphism with $1\mapsto2$ and $2\mapsto4$.
            This method assigns the @TO IndexedVariable@s @TT "e_(n,{...},i)"@ to the appropriate basis elements of $\mathbf{F}_n$ so that the user may access them.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(F, 5);
            e_(5,{2,4},2)
            F_5; x_(1,5)*e_(5,{2,4},2)+x_(1,4)^2*e_(5,{3},1)
///

doc ///
    Key
        makeMonic
        (makeMonic,List)
    Headline
        Make a list of elements of a FreeOIModule monic
    Usage
        makeMonic L
    Inputs
        L:List
    Outputs
        :List
    Description
        Text
            Given a @TO List@ of elements of a @TO FreeOIModule@, this method makes each element have a lead coefficient of $1$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(F, 5);
            F_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            makeMonic {b}
///

doc ///
    Key
        FreeOIModuleMap
    Headline
        The class of all maps between FreeOIModule objects
    Description
        Text
            This type implements maps $\varphi:\mathbf{F}\to\mathbf{G}$ between @TO FreeOIModule@ objects $\mathbf{F}$ and $\mathbf{G}$. To make a new @TT "FreeOIModuleMap"@ use @TO makeFreeOIModuleMap@. To get the source and target of a @TT "FreeOIModuleMap"@ use @TO (source,FreeOIModuleMap)@ and @TO (target,FreeOIModuleMap)@ respectively.
///

doc ///
    Key
        makeFreeOIModuleMap
        (makeFreeOIModuleMap,FreeOIModule,FreeOIModule,List)
    Headline
        Make a map between two FreeOIModules
    Usage
        makeFreeOIModuleMap(G, F, L)
    Inputs
        G:FreeOIModule
        F:FreeOIModule
        L:List
    Outputs
        :FreeOIModuleMap
    Description
        Text
            A map of free OI-modules $\varphi:\mathbf{F}\to\mathbf{G}$ is determined by its action on the basis of $\mathbf{F}$. The @TO List@ @TT "L"@ is used to specify where these basis elements are sent.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b})
        Text
            In the above example, the basis element of $\mathbf{F}$ is sent to $b$ under the action of $f$.  
///

doc ///
    Key
        (source,FreeOIModuleMap)
    Headline
        Get the source of a FreeOIModuleMap
    Usage
        source f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :FreeOIModule
    Description
        Text
            Returns the @TO source@ of a @TO FreeOIModuleMap@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            source f
///

doc ///
    Key
        (target,FreeOIModuleMap)
    Headline
        Get the target of a FreeOIModuleMap
    Usage
        target f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :FreeOIModule
    Description
        Text
            Returns the @TO target@ of a @TO FreeOIModuleMap@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            target f
///

doc ///
    Key
        (net,FreeOIModuleMap)
    Headline
        Display extended information for a FreeOIModuleMap object
    Usage
        net f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :Net
    Description
        Text
            Outputs the source module, target module and list of generator images for a @TO FreeOIModuleMap@ object.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            net f 
///

doc ///
    Key
        (symbol SPACE,FreeOIModuleMap,List)
    Headline
        Apply a FreeOIModuleMap to a List of elements
    Usage
        f L
    Inputs
        f:FreeOIModuleMap
        L:List
    Outputs
        :List
    Description
        Text
            Given a @TO FreeOIModuleMap@ $\varphi:\mathbf{F}\to\mathbf{G}$ and a finite subset $L\subset\mathbf{F}$, computes $\varphi(L)$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)*e_(5,{2,4},2)+3*x_(1,4)^2*e_(5,{3},1);
            F = makeFreeOIModule(P, d, {5});
            f = makeFreeOIModuleMap(G, F, {b});
            installBasisElements(F, 5);
            F_5; a = d_(5,{1,2,3,4,5},1);
            f {a, x_(1,4)*x_(1,3)*a}
///

doc ///
    Key
        (isHomogeneous,FreeOIModuleMap)
    Headline
        Check if a FreeOIModuleMap is homogeneous
    Usage
        isHomogeneous f
    Inputs
        f:FreeOIModuleMap
    Outputs
        :Boolean
    Description
        Text
            Checks if a @TO FreeOIModuleMap@ $\varphi:\mathbf{F}\to\mathbf{G}$ is graded.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2});
            installBasisElements(G, 5);
            G_5; b = x_(1,5)^2*e_(5,{2,4},2)+3*x_(1,4)*e_(5,{3},1);
            degree b
            F = makeFreeOIModule(P, d, {5}, DegreeShifts => {-4});
            f = makeFreeOIModuleMap(G, F, {b});
            isHomogeneous f
        Text
            In the above example, $f$ maps the degree $4$ basis element of $\mathbf{F}$ to the degree $4$ homogeneous element $b$ of $\mathbf{G}$ and is therefore a graded map.
///

doc ///
    Key
        MinimalOIGB
    Headline
        Option for minimal Gröbner bases
    Description
        Text
            If @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.

            If @TT "MinimalOIGB => true"@ is given then the algorithm will minimize the Gröbner basis. Most methods have this as the default option (all but @TO oiRes@).
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);
            F_1; b1 = x_(1,1)^3*e_(1,{1},1);
            F_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
            B = oiGB {b1, b2, b3, b4}
            oiSyz(B, d)
            oiSyz(B, d, MinimalOIGB => false)
///

doc ///
    Key
        DegreeShifts
    Headline
        Option for makeFreeOIModule
    Description
        Text
            This is an @TO Option@ for the @TO makeFreeOIModule@ method. It allows one to specify a shift of grading when construction a free OI-module.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1,2}, DegreeShifts => {-3,-2})
///

doc ///
    Key
        oiSyz
        (oiSyz,List,Symbol)
        [oiSyz,Verbose]
        [oiSyz,MinimalOIGB]
    Headline
        Compute the module of syzygies of a finite Gröbner basis
    Usage
        oiSyz(B, d)
    Inputs
        B:List
        d:Symbol
    Outputs
        :List
    Description
        Text
            Given a finite OI-Gröbner basis $B$, this method will use an OI-analogue of Schreyer's Theorem to compute a finite Gröbner basis for the module of syzygies of $B$ using the basis symbol $d$.

            If the option @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.
        
            The option @TT "Verbose => true"@ will output (a lot) of debug information.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            G = makeFreeOIModule(P, e, {1});
            installBasisElements(G, 1);
            installBasisElements(G, 2);
            G_1; b1 = x_(1,1)^3*e_(1,{1},1);
            G_2; b2 = x_(1,1)^2*e_(2,{1},1); b3 = x_(1,2)^2*e_(2,{2},1); b4 = x_(1,1)*x_(1,2)*e_(2,{2},1);
            B = oiGB {b1, b2, b3, b4}
            C = oiSyz(B, d)
        Text
            Note that in the above example, the $b_i$ are all monomials so @TO oiGB@ doesn't actually do anything.
///

doc ///
    Key
        isOIGB
        (isOIGB,List)
        [isOIGB,Verbose]
    Headline
        Check if a subset is an OI-Gröbner basis
    Usage
        isOIGB B
    Inputs
        B:List
    Outputs
        :Boolean
    Description
        Text
            Uses an OI-analogue of Buchberger's Criterion to determine if $B$ is an OI-Gröbner basis.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);
            F_1; f = x_(1,1)^3*e_(1,{1}, 1);
            F_2; h = x_(1,2)^2*e_(2, {2}, 1) + x_(1,1)*x_(1,2)*e_(2, {2}, 1);
            B = oiGB {f, h}
            isOIGB B
///

doc ///
    Key
        OIResolution
    Headline
        The class of all OI-resolutions of submodules of free OI-modules
    Description
        Text
            This type implements OI-resolutions for submodules of free OI-modules. To make a new @TT "OIResolution"@ object, use @TO oiRes@. To verify that an OI-resolution is a complex, use @TO isComplex@. Given an @TT "OIResolution"@ object @TT "C"@, one can view the differentials via @TT "C.dd"@. Furthermore, the $i^{\text{th}}$ module in the sequence may be accessed with @TT "C_i"@. To view more information about an OI-resolution, use @TO (describe,OIResolution)@.
///

doc ///
    Key
        oiRes
        (oiRes,List,ZZ)
        [oiRes,FastNonminimal]
        [oiRes,MinimalOIGB]
        [oiRes,Verbose]
    Headline
        Compute an OI-resolution for a submodule of a free OI-module
    Usage
        oiRes(B, n)
    Inputs
        B:List
        n:ZZ
    Outputs
        :OIResolution
    Description
        Text
            Suppose $B$ is a generating set of a submodule of a free OI-module $\mathbf{F}$. This method computes a length $n$ OI-resolution of the module generated by $B$ by iterating the @TO oiSyz@ method.

            If $B$ consists of homogeneous elements and the option @TT "FastNonminimal => false"@ is given (which it is by default) then the maps in the sequence will be minimized (in the sense of Definition 3.1 of @TO2{"Bibliography","[FN]"}@).

            If the option @TT "MinimalOIGB => true"@ is given, then a minimal Gröbner basis will be computed at each step. Since this greatly increases computation time, the option is set to false by default.

            The option @TT "Verbose => true"@ will output (a lot) of debug information.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1)
    Caveat
        Even though the maps in the sequence are minimized, the $n^{\text{th}}$ module in the sequence may not have minimal rank since the $(n+1)^{\text{st}}$ map (which has not been computed yet) may not be minimal.
///

doc ///
    Key
        (symbol _,OIResolution,ZZ)
    Headline
        Get the $n^{\text{th}}$ module in an OI-resolution
    Usage
        C_n
    Inputs
        C:OIResolution
        n:ZZ
    Outputs
        :FreeOIModule
    Description
        Text
            If $C:\cdots\to\mathbf{F}_2\to\mathbf{F}_1\to\mathbf{F}_0$ is some OI-resolution, this method returns $\mathbf{F}_n$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1);
            C_0
            C_1
///

doc ///
    Key
        (describe,OIResolution)
    Headline
        Display the modules and maps in an OI-resolution
    Usage
        describe C
    Inputs
        C:OIResolution
    Outputs
        :Net
    Description
        Text
            Displays the modules and differentials in an OI-resolution.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1);
            describe C
///

doc ///
    Key
        (net,OIResolution)
    Headline
        Display extended information about an OIResolution object
    Usage
        net C
    Inputs
        C:OIResolution
    Outputs
        :Net
    Description
        Text
            Displays the modules in an OI-resolution.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1);
            net C
///

doc ///
    Key
        isComplex
        (isComplex,OIResolution)
    Headline
        Checks if the differentials in an OI-resolution compose to zero
    Usage
        isComplex C
    Inputs
        C:OIResolution
    Outputs
        :Boolean
    Description
        Text
            Given an @TO OIResolution@ object @TT "C"@ with at least two maps in the sequence, this method checks if @TT "CC.dd_i CC.dd_(i+1) = 0"@ for all $i$.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);

            F_1; b1 = x_(1,1)*e_(1,{1},1); b2 = x_(1,1)^2*e_(1,{1},1);
            F_2; b3 = x_(1,2)*e_(2,{1},1);
            C = oiRes({b1, b2, b3}, 1)
            isComplex C
///

doc ///
    Key
        oiGB
        (oiGB,List)
        [oiGB,Verbose]
        [oiGB,Strategy]
        [oiGB,MinimalOIGB]
    Headline
        Compute a Gröbner basis for a finitely generated $\mathbf{P}$-submodule of $\mathbf{F}$
    Usage
        oiGB B
    Inputs
        B:List
    Outputs
        :List
    Description
        Text
            Uses an OI-analogue of Buchberger's Algorithm to produce a finite Gröbner basis from a given generating set $B=\{b_1,\ldots,b_t\}$ of some $\mathbf{P}$-submodule of $\mathbf{F}$. The algorithm uses the monomial order specified by $\mathbf{F}$, see @TO FreeOIModule@ for more details.
            
            If the option @TT "MinimalOIGB => false"@ is given, then the algorithm will not take the extra steps to remove redundant elements from the basis. Note that by "minimal" we mean minimal as a Gröbner basis, not necessarily as a generating set.
            
            The option @TT "Verbose => true"@ will output (a lot) of debug information.

            If @TT "Strategy => 2"@ is given, then the algorithm will append all nonzero remainders to the basis on a given step before moving to the next step. This can sometimes improve performance, but most of the time the default option @TT "Strategy => 1"@ seems to be faster, which appends only a single nonzero remainder to the basis before moving on to the next step.
        Example
            P = makePolynomialOIAlgebra(QQ,1,x);
            F = makeFreeOIModule(P, e, {1});
            installBasisElements(F, 1);
            installBasisElements(F, 2);
            F_1; b1 = x_(1,1)*e_(1,{1},1);
            F_2; b2 = x_(1,2)*e_(2,{1},1) + x_(1,1)*e_(2,{2},1);
            L = oiGB {b1, b2}
///