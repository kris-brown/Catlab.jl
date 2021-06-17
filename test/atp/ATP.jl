include("/Users/ksb/Catlab.jl/src/atp/ATP.jl");
using Catlab.CategoricalAlgebra

##########################################

# Possible generators for a theory of monoids
mmul = Box(:mul, Two, One);
e = Box(:e, Zero, One);
Σ = Set([mmul, e]);

mul_assoc_1 = WiringDiagram(Three, One);
mul_assoc_2 = WiringDiagram(Three, One);
m1,m2 = [add_box!(mul_assoc_1, mmul) for _ in 1:2];
add_wires!(mul_assoc_1, Pair[
    (input_id(mul_assoc_1), 1) => (m1, 1),
    (input_id(mul_assoc_1), 2) => (m1, 2),
    (input_id(mul_assoc_1), 3) => (m2, 2),
    (m1, 1) => (m2, 1),
    (m2, 1) => (output_id(mul_assoc_1), 1)]);

m1,m2 = [add_box!(mul_assoc_2, mmul) for _ in 1:2];
add_wires!(mul_assoc_2, Pair[
    (input_id(mul_assoc_2), 1) => (m1, 1),
    (input_id(mul_assoc_2), 2) => (m2, 1),
    (input_id(mul_assoc_2), 3) => (m2, 2),
    (m2, 1) => (m1, 2),
    (m1, 1) => (output_id(mul_assoc_2), 1)]);

leftid_1, rightid_1, passthru = [WiringDiagram(One, One) for _ in 1:3]
ebox,mbox = [add_box!(leftid_1, x) for x in [e, mmul]];
add_wires!(leftid_1, Pair[
    (input_id(leftid_1), 1) => (mbox, 2),
    (ebox, 1) => (mbox, 1),
    (mbox, 1) => (output_id(leftid_1), 1)])
ebox,mbox = [add_box!(rightid_1, x) for x in [e, mmul]];
add_wires!(rightid_1, Pair[
    (input_id(rightid_1), 1) => (mbox, 1),
    (ebox, 1) => (mbox, 2),
    (mbox, 1) => (output_id(rightid_1), 1)])
node = add_box!(passthru, dot);
add_wires!(passthru, Pair[
    (input_id(passthru), 1)=>(node,1),
    (node,1)=>(output_id(passthru), 1)]);


mul_assoc = mul_assoc_1 => mul_assoc_2;
leftid = leftid_1 => passthru;
rightid = rightid_1 => passthru;

# bres = branch2(leftid[1], leftid[2]);
# wd_to_cospan(bres, Σ)

I = Set([mul_assoc, leftid, rightid]);

idxxid = WiringDiagram(One, One);
e1,e2,split, m1,m2,m3 = [add_box!(idxxid, x) for x in [e, e, δ, mmul, mmul, mmul]];
add_wires!(idxxid, Pair[
    (input_id(idxxid), 1) => (split,1),
    (e1, 1) => (m1, 1),
    (e2, 1) => (m2, 2),
    (split, 1) => (m1, 2),
    (split, 2) => (m2, 1),
    (m1, 1) => (m3, 1),
    (m2, 1) => (m3, 2),
    (m3, 1) => (output_id(idxxid), 1)
    ]);

_, idxxid_scp = wd_to_cospan(idxxid, Σ);


xx = WiringDiagram(One, One)
split, m1 = [add_box!(xx, x) for x in [δ, mmul]]
add_wires!(xx, Pair[
    (input_id(xx), 1) => (split, 1),
    (split, 1) => (m1, 1),
    (split, 2) => (m1, 2),
    (m1, 1) => (output_id(xx), 1)]);

_, xx_hg = wd_to_cospan(xx, Σ);
rw1 = apply_eq(idxxid_scp, Σ, leftid);
rw2 = apply_eq(rw1, Σ, rightid);

@test !is_homomorphic(xx_hg, idxxid_scp) # not yet
@test !is_homomorphic(xx_hg, rw1) # not yet
@test is_homomorphic(xx_hg, rw2) # can prove after applying leftid AND rightid

branch2(mul_assoc_1, mul_assoc_2)

@assert !(prove(Σ, I, idxxid, xx) === nothing)
##########################################
# Relation
R = Box(:R, One, One);
f = Box(:f, One, One);
g = Box(:g, One, One);
Σ₂ = Set([R, f, g]);

R_copy = WiringDiagram(One, Two);
r, cpy = add_box!(R_copy, R), add_box!(R_copy, δ);
add_wires!(R_copy, Pair[
    (input_id(R_copy), 1) => (r, 1),
    (r, 1) => (cpy, 1),
    (cpy, 1) => (output_id(R_copy), 1),
    (cpy, 2) => (output_id(R_copy), 2)]);

csp,cc = wd_to_cospan(R_copy, Σ₂);



##########################################
fig26 = WiringDiagram(One, Two);
cpy,f1,g1,f2,g2 = [add_box!(fig26, x) for x in [δ, f, g, f, g]];
add_wires!(fig26, Pair[
    (input_id(fig26), 1) => (cpy, 1),
    (cpy, 1) => (f1, 1),
    (cpy, 2) => (f2, 1),
    (f1, 1) => (g1, 1),
    (f2, 1) => (g2, 1),
    (g1, 1) => (output_id(fig26), 1),
    (g2, 1) => (output_id(fig26), 2)]);

ex211 = WiringDiagram(Six, Five)
b01,b02,b03,b04,b11,b12,b21,b22,b23 = [add_box!(ex211, x) for x in [μ,μ,μ,δ, η,ϵ,μ,δ,δ]];
add_wires!(ex211, Pair[
    (input_id(ex211), 1) => (b02, 1),
    (input_id(ex211), 2) => (b01, 1),
    (input_id(ex211), 3) => (b01, 2),
    (input_id(ex211), 4) => (b03, 2),
    (input_id(ex211), 5) => (b21, 2),
    (input_id(ex211), 6) => (b21, 1),
    (b01, 1) => (b02, 2),
    (b02, 1) => (b03, 1),
    (b03, 1) => (b04, 1),
    (b11, 1) => (b12, 1),
    (b21, 1) => (b22, 1),
    (b22, 2) => (b23, 1),
    (b04,1) => (output_id(ex211), 1),
    (b04,2) => (output_id(ex211), 2),
    (b22,1) => (output_id(ex211), 3),
    (b23,1) => (output_id(ex211), 4),
    (b23,2) => (output_id(ex211), 5)]);
ex211b = WiringDiagram(Five, Four)
b1, b2, b3, b4 = [add_box!(ex211b, x) for x in [dot, μ,dot, dot]];
add_wires!(ex211b, Pair[
    (input_id(ex211b), 1) => (b1, 1),
    (input_id(ex211b), 2) => (b2, 1),
    (input_id(ex211b), 3) => (b2, 2),
    (input_id(ex211b), 4) => (b3, 1),
    (input_id(ex211b), 5) => (b4, 1),
    (b1,1) => (output_id(ex211b), 1),
    (b2,1) => (output_id(ex211b), 2),
    (b3,1) => (output_id(ex211b), 3),
    (b4,1) => (output_id(ex211b), 4)])



Σ0 = Set{Box{Symbol}}()


aptype, _, sctype, sccsettype = sigma_to_hyptype(Σ₂);

csp,cc = wd_to_cospan(fig26, Set([f,g]));


csp211,_ = wd_to_cospan(ex211, Σ0);
csp211b,_ = wd_to_cospan(ex211b, Σ0);
csp211_comp = compose(csp211, csp211b);