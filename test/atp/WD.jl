include("/Users/ksb/Catlab.jl/src/atp/ATP.jl")
using Catlab.WiringDiagrams

Zero, One, Two, Three, Four, Five, Six = [noth(i) for i in 0:6]

# Boxes
mmul = Box(:mul, Two,  One);
e    = Box(:e,   Zero, One);
inv  = Box(:inv, One,  One);
gens = Box(:s,   Zero, One);
genr = Box(:r,   Zero, One);
R    = Box(:R,   One,  One);
f    = Box(:f,   One,  One);
g    = Box(:g,   One,  One);
s    = Box(:s,   One,  One);   # Should be A->O
t    = Box(:t,   One,  One);   # Should be A->O
Id   = Box(:Id,   One,  One);  # Should be O->A
cmp  = Box(:cmp,   Two,  One); # Should be A,A -> A


# These should be functions which take a Sort symbol
ϵ, η, δ, μ, dot = [Box(nothing, x, y) for (x, y) in
    [(One, Zero), (Zero, One), (One, Two), (Two, One), (One, One)]]

# Generator sets
Σ0         = Set{Box{Symbol}}()
Σ_monoid   = Set([mmul, e]);
Σ_group    = Set([inv]);
Σ_dihedral = Set([gens, genr]);
Σ_rel      = Set([R, f, g]);
Σ_reflG    = Set([s,t,Id])
Σ_cat      = Set([cmp])


# Diagrams
mul_1 = WiringDiagram(Two, Zero);
ϵ1, ϵ2 = add_boxes!(mul_1, [ϵ,ϵ]);
add_wires!(mul_1, Pair[
    (input_id(mul_1), 1) => (ϵ1, 1),
    (input_id(mul_1), 2) => (ϵ2, 1)])

mul_2 = WiringDiagram(Two, Zero);
ϵ1, m1 = add_boxes!(mul_2, [ϵ,mmul]);
add_wires!(mul_2, Pair[
    (input_id(mul_2), 1) => (m1, 1),
    (input_id(mul_2), 2) => (m1, 2),
    (m1, 1)              => (ϵ1, 1)])

mul_assoc_1 = WiringDiagram(Three, One);
m1, m2 = add_boxes!(mul_assoc_1, [mmul, mmul])
add_wires!(mul_assoc_1, Pair[
    (input_id(mul_assoc_1), 1) => (m1, 1),
    (input_id(mul_assoc_1), 2) => (m1, 2),
    (input_id(mul_assoc_1), 3) => (m2, 2),
    (m1, 1)                    => (m2, 1),
    (m2, 1)                    => (output_id(mul_assoc_1), 1)]);

mul_assoc_2 = WiringDiagram(Three, One);
m1,m2 = add_boxes!(mul_assoc_2, [mmul, mmul])
add_wires!(mul_assoc_2, Pair[
    (input_id(mul_assoc_2), 1) => (m1, 1),
    (input_id(mul_assoc_2), 2) => (m2, 1),
    (input_id(mul_assoc_2), 3) => (m2, 2),
    (m2, 1)                    => (m1, 2),
    (m1, 1)                    => (output_id(mul_assoc_2), 1)]);

leftid_1 = WiringDiagram(One, One)
ebox, mbox = add_boxes!(leftid_1, [e, mmul]);
add_wires!(leftid_1, Pair[
    (input_id(leftid_1), 1) => (mbox, 2),
    (ebox, 1)               => (mbox, 1),
    (mbox, 1)               => (output_id(leftid_1), 1)])

rightid_1 = WiringDiagram(One, One)
ebox,mbox = add_boxes!(rightid_1, [e, mmul])
add_wires!(rightid_1, Pair[
    (input_id(rightid_1), 1) => (mbox, 1),
    (ebox, 1)                => (mbox, 2),
    (mbox, 1)                => (output_id(rightid_1), 1)])

passthru = WiringDiagram(One, One)
node = add_box!(passthru, dot);
add_wires!(passthru, Pair[
    (input_id(passthru), 1) => (node,1),
    (node,1)                => (output_id(passthru), 1)]);

idxxid = WiringDiagram(One, One);
e1,e2,split, m1,m2,m3 = add_boxes!(idxxid, [e, e, δ, mmul, mmul, mmul]);
add_wires!(idxxid, Pair[
    (input_id(idxxid), 1) => (split,1),
    (e1, 1)    => (m1, 1),
    (e2, 1)    => (m2, 2),
    (split, 1) => (m1, 2),
    (split, 2) => (m2, 1),
    (m1, 1)    => (m3, 1),
    (m2, 1)    => (m3, 2),
    (m3, 1)    => (output_id(idxxid), 1)]);

xx = WiringDiagram(One, One)
split, m1 = add_boxes!(xx, [δ, mmul]);
add_wires!(xx, Pair[
    (input_id(xx), 1) => (split, 1),
    (split, 1)        => (m1, 1),
    (split, 2)        => (m1, 2),
    (m1, 1)           => (output_id(xx), 1)]);

e_uniq_1 = WiringDiagram(Zero, Two)
e1,e2 = add_boxes!(e_uniq_1, [e,e])
add_wires!(e_uniq_1, Pair[
    (e1, 1) => (output_id(e_uniq_1), 1),
    (e2, 1) => (output_id(e_uniq_1), 2)])

e_uniq_2 = WiringDiagram(Zero, Two)
e1,e2, μbox, δbox = add_boxes!(e_uniq_2, [e,e,μ,δ])
add_wires!(e_uniq_2, Pair[
    (e1, 1) => (μbox, 1),
    (e2, 1) => (μbox, 2),
    (μbox, 1) => (δbox, 1),
    (δbox, 1) => (output_id(e_uniq_2), 1),
    (δbox, 2) => (output_id(e_uniq_2), 2)])

leftinv_1 = WiringDiagram(One, One)
δbox, ibox, mbox = add_boxes!(leftinv_1, [δ, inv, mmul])
add_wires!(leftinv_1, Pair[
    (input_id(leftinv_1), 1) => (δbox, 1),
    (δbox, 1)                => (ibox, 1),
    (δbox, 2)                => (mbox, 2),
    (ibox, 1)                => (mbox, 1),
    (mbox, 1)                => (output_id(leftinv_1), 1)])

rightinv_1 = WiringDiagram(One, One)
δbox, ibox, mbox = add_boxes!(rightinv_1, [δ, inv, mmul])
add_wires!(rightinv_1, Pair[
    (input_id(rightinv_1), 1) => (δbox, 1),
    (δbox, 1)                 => (ibox, 1),
    (δbox, 2)                 => (mbox, 1),
    (ibox, 1)                 => (mbox, 2),
    (mbox, 1)                 => (output_id(rightinv_1), 1)])

e11 = WiringDiagram(One, One)
ϵbox, ebox = add_boxes!(e11, [ϵ, e])
add_wires!(e11, Pair[
    (input_id(e11), 1) => (ϵbox, 1),
    (ebox, 1)          => (output_id(e11), 1)])

uniq_inv_1 = WiringDiagram(One, Two)
δbox, i1, i2 = add_boxes!(uniq_inv_1, [δ, inv, inv])
add_wires!(uniq_inv_1, Pair[
    (input_id(uniq_inv_1), 1) => (δbox, 1),
    (δbox, 1)                 => (i1, 1),
    (δbox, 2)                 => (i2, 1),
    (i1, 1)                   => (output_id(uniq_inv_1), 1),
    (i2, 1)                   => (output_id(uniq_inv_1), 2)])

uniq_inv_2 = WiringDiagram(One, Two)
δbox, ibox = add_boxes!(uniq_inv_2, [δ, inv]);
add_wires!(uniq_inv_2, Pair[
    (input_id(uniq_inv_2), 1) => (ibox, 1),
    (ibox, 1)                 => (δbox, 1),
    (δbox, 1)                 =>  (output_id(uniq_inv_2), 1),
    (δbox, 2)                 => (output_id(uniq_inv_2), 2)]);

div_1 = WiringDiagram(Three, Zero)
mbox, μbox, ϵbox = add_boxes!(div_1, [mmul, μ, ϵ]);
add_wires!(div_1, Pair[
    (input_id(div_1), 1) => (mbox, 1),
    (input_id(div_1), 2) => (mbox, 2),
    (input_id(div_1), 3) => (μbox, 2),
    (mbox, 1)            => (μbox, 1),
    (μbox, 1)            => (ϵbox, 1)]);

div_2 = WiringDiagram(Three, Zero)
mbox, μbox, ibox, ϵbox = add_boxes!(div_2, [mmul, μ, inv, ϵ]);
add_wires!(div_2, Pair[
    (input_id(div_2), 1) => (ibox, 1),
    (input_id(div_2), 2) => (μbox, 2),
    (input_id(div_2), 3) => (mbox, 2),
    (ibox, 1)            => (mbox, 1),
    (mbox, 1)            => (μbox, 1),
    (μbox, 1)            => (ϵbox, 1)]);

leftcancel_1 = WiringDiagram(Three, Zero)
m1, m2, μbox, δbox, ϵbox  = add_boxes!(leftcancel_1, [mmul, mmul, μ, δ, ϵ]);
add_wires!(leftcancel_1, Pair[
    (input_id(leftcancel_1), 1) => (δbox, 1),
    (input_id(leftcancel_1), 2) => (m1, 2),
    (input_id(leftcancel_1), 3) => (m2, 2),
    (δbox, 1)                   => (m1,1),
    (δbox, 2)                   => (m2,1),
    (m1, 1)                     => (μbox, 1),
    (m2, 1)                     => (μbox, 2),
    (μbox, 1)                   => (ϵbox, 1)]);

leftcancel_2 = WiringDiagram(Three, Zero)
μbox, ϵ1, ϵ2 = add_boxes!(leftcancel_2, [μ,ϵ,ϵ]);
add_wires!(leftcancel_2, Pair[
    (input_id(leftcancel_2), 1) => (ϵ1, 1),
    (input_id(leftcancel_2), 2) => (μbox, 1),
    (input_id(leftcancel_2), 3) => (μbox, 2),
    (μbox, 1)                   => (ϵ2, 1)]);

ss = WiringDiagram(Zero, One)
sbox, sδ, smul = add_boxes!(ss, [gens, δ, mmul]);
add_wires!(ss, Pair[
    (sbox, 1) => (sδ, 1),
    (sδ, 1) => (smul, 1),
    (sδ, 2) => (smul, 2),
    (smul, 1) => (output_id(ss), 1)])

rrr = WiringDiagram(Zero, One)
rbox, rδ1, rδ2, rmul1, rmul2 = add_boxes!(rrr, [genr, δ, δ, mmul, mmul]);
add_wires!(rrr, Pair[
    (rbox, 1)  => (rδ1, 1),
    (rδ1, 1)   => (rmul1, 1),
    (rδ1, 2)   => (rδ2, 1),
    (rδ2, 1)   => (rmul1, 2),
    (rδ2, 2)   => (rmul2, 2),
    (rmul1, 1) => (rmul2, 1),
    (rmul2, 1) => (output_id(rrr), 1)]);

e_wd = WiringDiagram(Zero, One)
ebox = add_box!(e_wd, e);
add_wire!(e_wd, (ebox, 1) => (output_id(e_wd), 1));


srs = WiringDiagram(Zero, One)
sbox, rbox, ibox, δbox, m1, m2 = add_boxes!(srs, [
    gens, genr, inv, δ, mmul, mmul]);
add_wires!(srs, Pair[
    (sbox, 1) => (δbox, 1),
    (δbox, 1) => (m1, 1),
    (δbox, 2) => (ibox, 1),
    (rbox, 1) => (m1, 2),
    (m1, 1)   => (m2, 1),
    (ibox, 1) => (m2, 2),
    (m2, 1)   => (output_id(srs), 1)]);

rinv = WiringDiagram(Zero, One)
rbox, ibox = add_boxes!(rinv, [genr, inv]);
add_wires!(rinv, Pair[
    (rbox, 1) => (ibox, 1),
    (ibox, 1) => (output_id(srs), 1)]);

sr2 = WiringDiagram(Zero, One)
sbox, rbox, δbox, m1, m2 = add_boxes!(sr2, [gens, genr, δ, mmul, mmul])
add_wires!(sr2, Pair[
    (sbox, 1) => (m1, 1),
    (rbox, 1) => (m1, 2),
    (m1, 1)   => (δbox, 1),
    (δbox, 1) => (m2, 1),
    (δbox, 2) => (m2, 2),
    (m2, 1)   => (output_id(sr2), 1)]);

R_copy = WiringDiagram(One, Two);
r, cpy = add_boxes!(R_copy, [R, δ]);
add_wires!(R_copy, Pair[
    (input_id(R_copy), 1) => (r, 1),
    (r, 1)                => (cpy, 1),
    (cpy, 1)              => (output_id(R_copy), 1),
    (cpy, 2)              => (output_id(R_copy), 2)]);

fig26 = WiringDiagram(One, Two);
cpy,f1,g1,f2,g2 = add_boxes!(fig26, [δ, f, g, f, g]);
add_wires!(fig26, Pair[
    (input_id(fig26), 1) => (cpy, 1),
    (cpy, 1)             => (f1, 1),
    (cpy, 2)             => (f2, 1),
    (f1, 1)              => (g1, 1),
    (f2, 1)              => (g2, 1),
    (g1, 1)              => (output_id(fig26), 1),
    (g2, 1)              => (output_id(fig26), 2)]);

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
    (b4,1) => (output_id(ex211b), 4)]);

# Equations
mul        = Eq(:mul,        mul_1,        mul_2,        false);
mul_assoc  = Eq(:assoc,      mul_assoc_1,  mul_assoc_2,  true);
leftid     = Eq(:leftid,     leftid_1,     passthru,     true);
rightid    = Eq(:rightid,    rightid_1,    passthru,     true);
e_uniq     = Eq(:e_uniq,     e_uniq_1,     e_uniq_2,     false);
leftinv    = Eq(:leftinv,    leftinv_1,    e11,          true)
rightinv   = Eq(:rightinv,   rightinv_1,   e11,          true)
uniq_inv   = Eq(:uniq_inv,   uniq_inv_1,   uniq_inv_2,   true);
gdiv       = Eq(:gdiv,       div_1,        div_2,        true);
leftcancel = Eq(:leftcancel, leftcancel_1, leftcancel_2, true);
s_order_2  = Eq(:s_ord_2, ss, e_wd, true);
r_order_3  = Eq(:r_ord_3, rrr, e_wd, true);


# Equation sets
I_monoid = Set([mul_assoc, leftid, rightid, mul]);
I_group  = Set([leftinv, rightinv]);
I_d3h    = Set([s_order_2, r_order_3]);

# Theories
T_monoid = EqTheory(Σ_monoid, I_monoid);
T_group  = union(T_monoid, Σ_group, I_group)
T_d3h    = union(T_group, Σ_dihedral, I_d3h);
