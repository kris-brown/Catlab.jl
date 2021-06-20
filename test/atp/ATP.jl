include("/Users/ksb/Catlab.jl/src/atp/ATP.jl");
using Catlab.CategoricalAlgebra
using Test

##########################################



# Possible generators for a theory of monoids
mmul = Box(:mul, Two, One);
e = Box(:e, Zero, One);
Σ_monoid = Set([mmul, e]);

mul_assoc_1 = WiringDiagram(Three, One);
mul_assoc_2 = WiringDiagram(Three, One);
m1,m2 = add_boxes!(mul_assoc_1, [mmul, mmul])
add_wires!(mul_assoc_1, Pair[
    (input_id(mul_assoc_1), 1) => (m1, 1),
    (input_id(mul_assoc_1), 2) => (m1, 2),
    (input_id(mul_assoc_1), 3) => (m2, 2),
    (m1, 1) => (m2, 1),
    (m2, 1) => (output_id(mul_assoc_1), 1)]);

m1,m2 = add_boxes!(mul_assoc_2, [mmul, mmul])
add_wires!(mul_assoc_2, Pair[
    (input_id(mul_assoc_2), 1) => (m1, 1),
    (input_id(mul_assoc_2), 2) => (m2, 1),
    (input_id(mul_assoc_2), 3) => (m2, 2),
    (m2, 1) => (m1, 2),
    (m1, 1) => (output_id(mul_assoc_2), 1)]);

leftid_1, rightid_1, passthru = [WiringDiagram(One, One) for _ in 1:3]
ebox, mbox = add_boxes!(leftid_1, [e, mmul]);
add_wires!(leftid_1, Pair[
    (input_id(leftid_1), 1) => (mbox, 2),
    (ebox, 1) => (mbox, 1),
    (mbox, 1) => (output_id(leftid_1), 1)])
ebox,mbox = add_boxes!(rightid_1, [e, mmul])
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

I_monoid = Set([mul_assoc, leftid, rightid]);

merge_leftid = branch(leftid...);

idxxid = WiringDiagram(One, One);
e1,e2,split, m1,m2,m3 = add_boxes!(idxxid, [e, e, δ, mmul, mmul, mmul]);
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

_, idxxid_sc = wd_to_cospan(idxxid, Σ_monoid);


xx = WiringDiagram(One, One)
split, m1 = add_boxes!(xx, [δ, mmul]);
add_wires!(xx, Pair[
    (input_id(xx), 1) => (split, 1),
    (split, 1) => (m1, 1),
    (split, 2) => (m1, 2),
    (m1, 1) => (output_id(xx), 1)]);

_, xx_hg = wd_to_cospan(xx, Σ_monoid);
rw1 = apply_eq(idxxid_sc, Σ_monoid, leftid);
rw2 = apply_eq(rw1, Σ_monoid, rightid);

@test !is_homomorphic(xx_hg, idxxid_sc) # not yet
@test !is_homomorphic(xx_hg, rw1) # not yet
@test is_homomorphic(xx_hg, rw2) # can prove after applying leftid AND rightid

mbranch = branch(wd_pad(mul_assoc_1), wd_pad(mul_assoc_2));
@test wd_pad(mul_assoc_1) == wd_pad(wd_pad(mul_assoc_1)) # idempotency
proveresult = prove(Σ_monoid, Set([leftid, rightid]), idxxid, xx, oriented=true)
@test !(proveresult === nothing)

# uniqueness of identity
e_uniq_1, e_uniq_2 = [WiringDiagram(Zero, Zero) for _ in 1:2]
e1,e2,ep1,ep2 = add_boxes!(e_uniq_1, [e,e,ϵ,ϵ])
add_wires!(e_uniq_1, Pair[
    (e1, 1) => (ep1, 1)
    (e2, 1) => (ep2, 1)])

e1,e2,μbox = add_boxes!(e_uniq_2, [e,e,μ])
add_wires!(e_uniq_2, Pair[
    (e1, 1) => (μbox, 1),
    (e2, 1) => (μbox, 2)])

e_uniq = e_uniq_1 => e_uniq_2;

proveresult = prove(Σ_monoid, Set([leftid, rightid]), e_uniq_1, e_uniq_2,
                    oriented=true);

@test !(proveresult === nothing)

################################################################################
# Generators for a theory of GROUPS
inv = Box(:inv, One, One);
Σ_group = Set([mmul, e, inv]);

# Add inverse axioms
leftinv_1, rightinv_1, e11 = [WiringDiagram(One, One) for _ in 1:3]

δbox, ibox, mbox = add_boxes!(leftinv_1, [δ, inv, mmul])
add_wires!(leftinv_1, Pair[
    (input_id(leftinv_1), 1) => (δbox, 1),
    (δbox, 1) => (ibox, 1),
    (δbox, 2) => (mbox, 2),
    (ibox, 1) => (mbox, 1),
    (mbox, 1) => (output_id(leftinv_1), 1)])

δbox, ibox, mbox = add_boxes!(rightinv_1, [δ, inv, mmul])
add_wires!(rightinv_1, Pair[
    (input_id(rightinv_1), 1) => (δbox, 1),
    (δbox, 1) => (ibox, 1),
    (δbox, 2) => (mbox, 1),
    (ibox, 1) => (mbox, 2),
    (mbox, 1) => (output_id(rightinv_1), 1)])

ϵbox, ebox = add_boxes!(e11, [ϵ, e])
add_wires!(e11, Pair[
    (input_id(e11), 1) => (ϵbox, 1),
    (ebox, 1) => (output_id(e11), 1)])


leftinv = leftinv_1 => e11
rightinv = rightinv_1 => e11
I_group = union(I_monoid, [leftinv, rightinv]);

# important things to prove: uniqueness of inverse & division
uniq_inv_1, uniq_inv_2 = [WiringDiagram(One, Two) for _ in 1:2]
δbox, i1, i2 = add_boxes!(uniq_inv_1, [δ, inv, inv])
add_wires!(uniq_inv_1, Pair[
    (input_id(uniq_inv_1), 1) => (δbox, 1),
    (δbox, 1) => (i1, 1),
    (δbox, 2) => (i2, 1),
    (i1, 1) => (output_id(uniq_inv_1), 1),
    (i2, 1) => (output_id(uniq_inv_1), 2)])

δbox, ibox = add_boxes!(uniq_inv_2, [δ, inv])
add_wires!(uniq_inv_2, Pair[
    (input_id(uniq_inv_2), 1) => (ibox, 1),
    (ibox, 1) => (δbox, 1),
    (δbox, 1) =>  (output_id(uniq_inv_2), 1),
    (δbox, 2) => (output_id(uniq_inv_2), 2)])

uniq_inv = uniq_inv_1 => uniq_inv_2 # proof?

div_1, div_2 = [WiringDiagram(Three, Zero) for _ in 1:2]
mbox, μbox = add_boxes!(div_1, [mmul, μ])
add_wires!(div_1, Pair[
    (input_id(div_1), 1) => (mbox, 1),
    (input_id(div_1), 2) => (mbox, 2),
    (input_id(div_1), 3) => (μbox, 2),
    (mbox, 1) => (μbox, 1)])

mbox, μbox, ibox = add_boxes!(div_2, [mmul, μ, inv])
add_wires!(div_2, Pair[
    (input_id(div_2), 1) => (ibox, 1),
    (input_id(div_2), 2) => (μbox, 2),
    (input_id(div_2), 3) => (mbox, 2),
    (ibox, 1) => (mbox, 1),
    (mbox, 1) => (μbox, 1)])

gdiv = div_1 => div_2 # proof?

leftcancel_1, leftcancel_2 = [WiringDiagram(Three, Zero) for _ in 1:2]
m1, m2, μbox, δbox = add_boxes!(leftcancel_1, [mmul, mmul, μ, δ])
add_wires!(leftcancel_1, Pair[
    (input_id(leftcancel_1), 1) => (δbox, 1),
    (input_id(leftcancel_1), 2) => (m1, 2),
    (input_id(leftcancel_1), 3) => (m2, 2),
    (δbox, 1) => (m1,1),
    (δbox, 2) => (m2,1),
    (m1, 1) => (μbox, 1),
    (m2, 1) => (μbox, 2)])

μbox, ϵbox = add_boxes!(leftcancel_2, [μ,ϵ])
add_wires!(leftcancel_2, Pair[
    (input_id(leftcancel_2), 1) => (ϵbox, 1),
    (input_id(leftcancel_2), 2) => (μbox, 1),
    (input_id(leftcancel_2), 3) => (μbox, 2)])

leftcancel = leftcancel_1 => leftcancel_2
# Dihedral groups

gens, genr = [Box(x, Zero, One) for x in [:s, :r]]
ss, rrr, e_wd, srs, rinv, sr2 = [WiringDiagram(Zero, One) for _ in 1:6]
sbox, sδ, smul = add_boxes!(ss, [gens, δ, mmul]);
rbox, rδ1, rδ2, rmul1, rmul2 = add_boxes!(rrr, [genr, δ, δ, mmul, mmul]);

add_wires!(ss, Pair[
    (sbox, 1) => (sδ, 1),
    (sδ, 1) => (smul, 1),
    (sδ, 2) => (smul, 2),
    (smul, 1) => (output_id(ss), 1)])

add_wires!(rrr, Pair[
    (rbox, 1)  => (rδ1, 1),
    (rδ1, 1)   => (rmul1, 1),
    (rδ1, 2)   => (rδ2, 1),
    (rδ2, 1)   => (rmul1, 2),
    (rδ2, 2)   => (rmul2, 2),
    (rmul1, 1) => (rmul2, 1),
    (rmul2, 1) => (output_id(rrr), 1)])

ebox = add_box!(e_wd, e)
add_wire!(e_wd, (ebox, 1) => (output_id(e_wd), 1))

s_order_2 = ss => ebox
r_order_3 = rrr => ebox

Σ_d3h = Set([mmul, e, inv, gens, genr]);
I_d3h = union(I_group, [s_order_2, r_order_3])

sbox, rbox, ibox, δbox, m1, m2 = add_boxes!(srs, [
    gens, genr, inv, δ, mmul, mmul])
add_wires!(srs, Pair[
    (sbox, 1) => (δbox, 1),
    (δbox, 1) => (m1, 1),
    (δbox, 2) => (ibox, 1),
    (rbox, 1) => (m1, 2),
    (m1, 1)   => (m2, 1),
    (ibox, 1) => (m2, 2),
    (m2, 1)   => (output_id(srs), 1)])

rbox, ibox = add_boxes!(rinv, [genr, inv]);
add_wires!(rinv, Pair[
    (rbox, 1) => (ibox, 1),
    (ibox, 1) => (output_id(srs), 1)])

sbox, rbox, δbox, m1, m2 = add_boxes!(sr2, [gens, genr, δ, mmul, mmul])
add_wires!(sr2, Pair[
    (sbox, 1) => (m1, 1),
    (rbox, 1) => (m1, 2),
    (m1, 1)   => (δbox, 1),
    (δbox, 1) => (m2, 1),
    (δbox, 2) => (m2, 2),
    (m2, 1)   => (output_id(sr2), 1)])

I_d3h_pres1 = union(I_d3h, [srs => rinv]) # from this prove (sr)²=1
I_d3h_pres2 = union(I_d3h, [sr2 => ebox]) # from this prove srs⁻¹ = r⁻¹

##########################################
# Relation
R = Box(:R, One, One);
f = Box(:f, One, One);
g = Box(:g, One, One);
Σ_rel = Set([R, f, g]);

R_copy = WiringDiagram(One, Two);
r, cpy = add_boxes!(R_copy, [R, δ]);
add_wires!(R_copy, Pair[
    (input_id(R_copy), 1) => (r, 1),
    (r, 1) => (cpy, 1),
    (cpy, 1) => (output_id(R_copy), 1),
    (cpy, 2) => (output_id(R_copy), 2)]);

cc = wd_to_cospan(R_copy, Σ_rel)[2];
aptype, _, sctype, sccsettype = sigma_to_hyptype(Σ_rel);

fig26 = WiringDiagram(One, Two);
cpy,f1,g1,f2,g2 = add_boxes!(fig26, [δ, f, g, f, g]);
add_wires!(fig26, Pair[
    (input_id(fig26), 1) => (cpy, 1),
    (cpy, 1) => (f1, 1),
    (cpy, 2) => (f2, 1),
    (f1, 1) => (g1, 1),
    (f2, 1) => (g2, 1),
    (g1, 1) => (output_id(fig26), 1),
    (g2, 1) => (output_id(fig26), 2)]);

cc = wd_to_cospan(fig26, Σ_rel)[2];

##########################################
# Empty theory

ex211 = WiringDiagram(Six, Five)
b01,b02,b03,b04,b11,b12,b21,b22,b23 = add_boxes!(ex211, [μ,μ,μ,δ, η,ϵ,μ,δ,δ]);
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
b1, b2, b3, b4 = add_boxes!(ex211b, [dot, μ,dot, dot]);
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
csp211 = wd_to_cospan(ex211, Σ0)[1];
csp211b = wd_to_cospan(ex211b, Σ0)[1];
csp211_comp = compose(csp211, csp211b);