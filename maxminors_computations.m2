-- maxminors_computations.m2
-- Macaulay2 computations for "Arrangements of maximal minors: Gale duality,
-- complements, and the non-free 3x5 case".
-- Run with:   M2 --script maxminors_computations.m2
-- Tested with Macaulay2 1.22. All computations are exact (over QQ).

say = s -> (stdio << s << endl << flush);

----------------------------------------------------------------------------
-- Der(-log f) for f = product of the (irreducible, pairwise non-associate)
-- homogeneous factors in the list L; returned as a graded submodule of R^N,
-- where a vector field with coefficients of degree d has degree d.
----------------------------------------------------------------------------
logDer = L -> (
    R := ring first L; n := numgens R; k := #L;
    J := matrix apply(L, f -> apply(gens R, x -> diff(x,f)));
    H := diagonalMatrix apply(L, f -> -f);
    tgt := R^(apply(L, f -> (first degree f) - 1));
    src := R^(toList(n:0) | toList(k:-1));
    phi := map(tgt, src, J | H);
    assert isHomogeneous phi;
    K := gens ker phi;
    P := map(R^n, src, (id_(R^n)) | map(R^n,R^k,0));
    image (P*K)
);
-- ungraded version (factors need not be homogeneous)
logDerUngraded = L -> (
    R := ring first L; n := numgens R; k := #L;
    J := matrix apply(L, f -> apply(gens R, x -> diff(x,f)));
    H := diagonalMatrix apply(L, f -> -f);
    K := gens ker (J | H);
    image (map(R^n, R^(n+k), (id_(R^n)) | map(R^n,R^k,0)) * K)
);
report = (name, M, r) -> (
    G := mingens M;
    say(name | ": " | toString numcols G | " minimal generators (rank " | toString r | "), degrees " | toString sort flatten degrees source G);
    G
);
maxMinors = (m,n) -> (
    T := QQ[x_(1,1)..x_(m,n)];
    N := transpose genericMatrix(T, x_(1,1), n, m);
    (T, N, apply(subsets(n,m), s -> det N_s))
);

say "=== Part 1. Known free cases ===";
for n from 3 to 7 do ( (T,N,L) = maxMinors(2,n); report("2x" | toString n, logDer L, 2*n); );
(T,N,L) = maxMinors(3,4); report("3x4", logDer L, 12);

say "=== Part 2. The 9-variable certificate (chart of Prop. 5.3 at (e1,e2,0,0,0)) ===";
S = QQ[a_3..a_5,b_3..b_5,c_3..c_5];
N9 = matrix{{1,0,a_3,a_4,a_5},{0,1,b_3,b_4,b_5},{0,0,c_3,c_4,c_5}};
L9 = apply(subsets(5,3), s -> det N9_s);
say("factors: " | toString L9);
D9 = logDer L9;
report("chart f'_{3,5}", D9, 9);
say("betti table of a minimal resolution:"); say betti res prune D9;
P9 = presentation prune D9;
say("non-free locus of E'_{3,5} (radical of Fitting ideal): " | toString radical minors(numrows P9 - 9, P9));

say "=== Part 3. Der(-log D_{3,5}) ===";
(T,N,L) = maxMinors(3,5);
Dl = new HashTable from apply(subsets(5,3), s -> s => det N_s);
Der = logDer L;
report("D_{3,5}", Der, 15);
say("betti table:"); say betti res prune Der;
vidx = (r,k) -> (r-1)*5 + (k-1);
field = (lst,d) -> ( v := new MutableList from toList(15:0_T);
    scan(lst, p -> v#(p#0) = v#(p#0) + p#1); map(T^15, T^{-d}, transpose matrix{toList v}));
lin = {};
for r from 1 to 3 do for s from 1 to 3 do if not (r == 3 and s == 3) then
    lin = append(lin, field(apply(5, k -> (vidx(r,k+1), x_(s,k+1))), 1));      -- xi_{E_rs}
for k from 1 to 5 do lin = append(lin, field(apply(3, r -> (vidx(r+1,k), x_(r+1,k))), 1));  -- eta_k
Lmat = fold(lin, (u,w) -> u | w);
say("13 linear fields: rank " | toString rank image Lmat | "; they span the degree-1 part of Der: " | toString (numcols basis(1,Der) == 13));
psi = (i,k) -> ( c := product(select(subsets(5,3), s -> member(i-1,s) and not member(k-1,s)), s -> Dl#s);
                 field(apply(3, r -> (vidx(r+1,i), c * x_(r+1,k))), 10) );
sgnf = (i,k) -> (-1)^(i+k) * (if i > k then 1 else -1);
psit = (i,k) -> sgnf(i,k) * psi(i,k);
prs = select(flatten for i from 1 to 5 list for k from 1 to 5 list (i,k), p -> p#0 != p#1);
say("all psi_{i->k} logarithmic: " | toString all(prs, p -> isSubset(image psi p, Der)));
say("no psi_{i->k} lies in R*L: " | toString all(prs, p -> not isSubset(image psi p, image Lmat)));
cong = true;
for k from 1 to 5 do for i from 1 to 5 do for j from i+1 to 5 do if i != k and j != k then
    cong = cong and isSubset(image(psit(i,k) - psit(j,k)), image Lmat);
say("for fixed k the fields psi~_{i->k} are congruent mod R*L: " | toString cong);
for choice in {{2,1,1,1,1},{5,5,5,5,4},{3,4,5,1,2}} do (
    Phi := apply(5, k -> psit(choice#k, k+1));
    Fm := fold(Phi, (u,w) -> u | w);
    say("Phi_k = psi~_{i(k)->k}, i = " | toString choice | ": L + Phi = Der: " | toString (image(Lmat | Fm) == Der)
        | "; sum_k x_(r,k) Phi_k in R*L: " | toString apply(3, r -> isSubset(image sum(5, k -> x_(r+1,k+1) * Phi#k), image Lmat))
        | "; syzygy degrees " | toString flatten degrees source mingens image gens ker (Lmat | Fm));
);

say "=== Part 3b. Multidegrees (row degrees | column degrees) ===";
degs = flatten for r from 1 to 3 list for k from 1 to 5 list
    (apply(3, i -> if i == r-1 then 1 else 0) | apply(5, i -> if i == k-1 then 1 else 0));
TT = QQ[y_(1,1)..y_(3,5), Degrees => degs];
NN = transpose genericMatrix(TT, y_(1,1), 5, 3);
LL = apply(subsets(5,3), s -> det NN_s);
Jmat = matrix apply(LL, f -> apply(gens TT, v -> diff(v,f)));
Hmat = diagonalMatrix apply(LL, f -> -f);
tg = TT^(apply(LL, f -> degree f));
sr = TT^(apply(gens TT, v -> degree v) | toList(10:toList(8:0)));
phiM = map(tg, sr, Jmat | Hmat);
assert isHomogeneous phiM;
DD = image (map(TT^(apply(gens TT, v -> degree v)), sr, (id_(TT^15)) | map(TT^15,TT^10,0)) * gens ker phiM);
say("generator multidegrees: " | toString tally degrees source mingens DD);
say("syzygy multidegrees: " | toString tally degrees (res prune DD)_1);

say "=== Part 4. Rank of the presentation matrix on the rank-1 locus ===";
P = presentation prune Der;
U1 = QQ[u_1..u_3, w_1..w_5];
M1 = (transpose matrix{{u_1,u_2,u_3}}) * matrix{{w_1,w_2,w_3,w_4,w_5}};
say("rank over QQ(u,w) of the 18x3 presentation matrix at M = u w^T: " | toString rank sub(P, matrix{flatten entries M1}));

say "=== Part 5. The ten-plane arrangement A(e1,e2,e3,(2,3,5),(7,-1,4)) ===";
Rc = QQ[z_1..z_3];
Pts = {{1,0,0},{0,1,0},{0,0,1},{2,3,5},{7,-1,4}};
L10 = apply(subsets(5,2), s -> det matrix{Pts#(s#0), Pts#(s#1), {z_1,z_2,z_3}});
D10 = logDer L10;
report("A(P)", D10, 3);
say("pd = " | toString pdim prune D10);

say "=== Part 6. The family of generic 5-plane arrangements over its moduli ===";
Sf = QQ[s,u,c_1..c_3];
Lf = {c_1, c_2, c_3, c_1+c_2+c_3, c_1+s*c_2+u*c_3};
Df = prune logDerUngraded Lf;
Pf = presentation Df;
say("generators: " | toString numgens Df | " (rank 5); non-free locus: " | toString radical minors(numgens Df - 5, Pf));

say "=== Part 7. Charts at rank-(m-1) points for other sizes ===";
chartTest = (m,n) -> (
    c := n - m + 1;
    Sc := QQ[t_(1,1)..t_(m,c)];
    Z := transpose genericMatrix(Sc, t_(1,1), c, m);
    Nc := (id_(Sc^(m-1)) || map(Sc^1, Sc^(m-1), 0)) | Z;
    Lc := select(apply(subsets(n,m), s -> det Nc_s), f -> f != 0);
    t0 := cpuTime();
    G := mingens logDer Lc;
    say(toString m | "x" | toString n | " chart at rank " | toString(m-1) | ": " | toString numcols G
        | " minimal generators in " | toString numgens Sc | " variables; degrees "
        | toString sort flatten degrees source G | "  [" | toString(cpuTime()-t0) | " s]");
);
chartTest(3,5); chartTest(4,6); chartTest(5,7); chartTest(3,6);

say "=== Part 8. 4x6 chart: local number of generators at random points ===";
setRandomSeed 2026;
S46 = QQ[t_(1,1)..t_(4,3)];
Z46 = transpose genericMatrix(S46, t_(1,1), 3, 4);
N46 = (id_(S46^3) || map(S46^1, S46^3, 0)) | Z46;
D46 = prune logDer select(apply(subsets(6,4), s -> det N46_s), f -> f != 0);
P46 = presentation D46;
for trial from 1 to 3 do (
    vals = flatten apply(4, r -> apply(3, j -> if r == 3 then 0_QQ else random(-50,50)/1));
    say("random point with z = 0 (rank 3): stalk needs " | toString(numgens D46 - rank sub(P46, matrix{vals})) | " generators (rank 12)");
);
vals = flatten apply(4, r -> apply(3, j -> random(-50,50)/1));
say("random point with z != 0 (rank 4): stalk needs " | toString(numgens D46 - rank sub(P46, matrix{vals})) | " generators");
say "done";
