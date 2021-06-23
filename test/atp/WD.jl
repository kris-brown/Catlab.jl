include("/Users/ksb/Catlab.jl/src/atp/ATP.jl")
using Catlab.WiringDiagrams

# Single sorted inputs/outputs
Zero, One, Two, Three, Four, Five, Six = [repeat([:X], i) for i in 0:6]

# Boxes
mmul = Box(:mul, Two,     One);
e    = Box(:e,   Zero,    One);
inv  = Box(:inv, One,     One);
gens = Box(:s,   Zero,    One);
genr = Box(:r,   Zero,    One);
R    = Box(:R,   One,     One);
f    = Box(:f,   One,     One);
g    = Box(:g,   One,     One);
s    = Box(:s,   [:A],    [:O]);
t    = Box(:t,   [:A],    [:O]);
Id   = Box(:Id,  [:O],    [:A]);
cmp  = Box(:cmp, [:A,:A], [:A]);

ϵ(x::Symbol=:X)   = Junction(x, 1, 0)
η(x::Symbol=:X)   = Junction(x, 0, 1)
δ(x::Symbol=:X)   = Junction(x, 1, 2)
μ(x::Symbol=:X)   = Junction(x, 2, 1)
dot(x::Symbol=:X) = Junction(x, 1, 1)

# Generator sets
Σ0         = Set{Box{Symbol}}()
Σ_monoid   = Set([mmul, e]);
Σ_group    = Set([inv]);
Σ_dihedral = Set([gens, genr]);
Σ_rel      = Set([R, f, g]);
Σ_reflG    = Set([s, t, Id]);
Σ_cat      = Set([cmp]);


# Diagrams
function assoc(b::Box{Symbol})::Eq
    l = WiringDiagram(Three, One);
    m1, m2 = add_boxes!(l, [b, b])
    add_wires!(l, Pair[
        (input_id(l), 1) => (m1, 1),
        (input_id(l), 2) => (m1, 2),
        (input_id(l), 3) => (m2, 2),
        (m1, 1)          => (m2, 1),
        (m2, 1)          => (output_id(l), 1)]);

    r = WiringDiagram(Three, One);
    m1,m2 = add_boxes!(r, [b, b])
    add_wires!(r, Pair[
        (input_id(r), 1) => (m1, 1),
        (input_id(r), 2) => (m2, 1),
        (input_id(r), 3) => (m2, 2),
        (m2, 1)          => (m1, 2),
        (m1, 1)          => (output_id(r), 1)]);
    return Eq(Symbol(string(b.value)*"_assoc"), l,  r,  true);
end

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
node = add_box!(passthru, dot());
add_wires!(passthru, Pair[
    (input_id(passthru), 1) => (node,1),
    (node,1)                => (output_id(passthru), 1)]);

idxxid = WiringDiagram(One, One);
e1,e2,split, m1,m2,m3 = add_boxes!(idxxid, [e, e, δ(), mmul, mmul, mmul]);
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
split, m1 = add_boxes!(xx, [δ(), mmul]);
add_wires!(xx, Pair[
    (input_id(xx), 1) => (split, 1),
    (split, 1)        => (m1, 1),
    (split, 2)        => (m1, 2),
    (m1, 1)           => (output_id(xx), 1)]);

leftinv_1 = WiringDiagram(One, One)
δbox, ibox, mbox = add_boxes!(leftinv_1, [δ(), inv, mmul])
add_wires!(leftinv_1, Pair[
    (input_id(leftinv_1), 1) => (δbox, 1),
    (δbox, 1)                => (ibox, 1),
    (δbox, 2)                => (mbox, 2),
    (ibox, 1)                => (mbox, 1),
    (mbox, 1)                => (output_id(leftinv_1), 1)])

rightinv_1 = WiringDiagram(One, One)
δbox, ibox, mbox = add_boxes!(rightinv_1, [δ(), inv, mmul])
add_wires!(rightinv_1, Pair[
    (input_id(rightinv_1), 1) => (δbox, 1),
    (δbox, 1)                 => (ibox, 1),
    (δbox, 2)                 => (mbox, 1),
    (ibox, 1)                 => (mbox, 2),
    (mbox, 1)                 => (output_id(rightinv_1), 1)])

e11 = WiringDiagram(One, One)
ϵbox, ebox = add_boxes!(e11, [ϵ(), e])
add_wires!(e11, Pair[
    (input_id(e11), 1) => (ϵbox, 1),
    (ebox, 1)          => (output_id(e11), 1)])

uniq_inv_1 = WiringDiagram(Three, Zero)
δbox, m1, m2, μ1, μ2, eb, ϵbox = add_boxes!(uniq_inv_1, [
    δ(), mmul, mmul, μ(), μ(), e, ϵ()])
add_wires!(uniq_inv_1, Pair[
    (input_id(uniq_inv_1), 1) => (m1, 1),
    (input_id(uniq_inv_1), 2) => (δbox, 1),
    (input_id(uniq_inv_1), 3) => (m2, 2),
    (δbox, 1)                 => (m1, 2),
    (δbox, 2)                 => (m2, 1),
    (m1, 1)                   => (μ1, 1),
    (m2, 1)                   => (μ1, 2),
    (μ1, 1)                   => (μ2, 1),
    (eb, 1)                   => (μ2, 2),
    (μ2, 1)                   => (ϵbox, 1)])

uniq_inv_2 = WiringDiagram(Three, Zero)
μbox, ϵ1, ϵ2 = add_boxes!(uniq_inv_2, [μ(), ϵ(), ϵ()]);
add_wires!(uniq_inv_2, Pair[
    (input_id(uniq_inv_2), 1) => (μbox, 1),
    (input_id(uniq_inv_2), 2) => (ϵ1, 1),
    (input_id(uniq_inv_2), 3) => (μbox, 2),
    (μbox, 1)                 => (ϵ2, 1)]);

div_1 = WiringDiagram(Three, Zero)
mbox, μbox, ϵbox = add_boxes!(div_1, [mmul, μ(), ϵ()]);
add_wires!(div_1, Pair[
    (input_id(div_1), 1) => (mbox, 1),
    (input_id(div_1), 2) => (mbox, 2),
    (input_id(div_1), 3) => (μbox, 2),
    (mbox, 1)            => (μbox, 1),
    (μbox, 1)            => (ϵbox, 1)]);

div_2 = WiringDiagram(Three, Zero)
mbox, μbox, ibox, ϵbox = add_boxes!(div_2, [mmul, μ(), inv, ϵ()]);
add_wires!(div_2, Pair[
    (input_id(div_2), 1) => (ibox, 1),
    (input_id(div_2), 2) => (μbox, 2),
    (input_id(div_2), 3) => (mbox, 2),
    (ibox, 1)            => (mbox, 1),
    (mbox, 1)            => (μbox, 1),
    (μbox, 1)            => (ϵbox, 1)]);

leftcancel_1 = WiringDiagram(Three, Zero)
m1, m2, μbox, δbox, ϵbox  = add_boxes!(leftcancel_1, [
    mmul, mmul, μ(), δ(), ϵ()]);
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
μbox, ϵ1, ϵ2 = add_boxes!(leftcancel_2, [μ(), ϵ(), ϵ()]);
add_wires!(leftcancel_2, Pair[
    (input_id(leftcancel_2), 1) => (ϵ1, 1),
    (input_id(leftcancel_2), 2) => (μbox, 1),
    (input_id(leftcancel_2), 3) => (μbox, 2),
    (μbox, 1)                   => (ϵ2, 1)]);

ss = WiringDiagram(Zero, One)
sbox, sδ, smul = add_boxes!(ss, [gens, δ(), mmul]);
add_wires!(ss, Pair[
    (sbox, 1) => (sδ, 1),
    (sδ, 1) => (smul, 1),
    (sδ, 2) => (smul, 2),
    (smul, 1) => (output_id(ss), 1)])

rrr = WiringDiagram(Zero, One)
rbox, rδ1, rδ2, rmul1, rmul2 = add_boxes!(rrr, [genr, δ(), δ(), mmul, mmul]);
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
    gens, genr, inv, δ(), mmul, mmul]);
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
sbox, rbox, δbox, m1, m2 = add_boxes!(sr2, [gens, genr, δ(), mmul, mmul])
add_wires!(sr2, Pair[
    (sbox, 1) => (m1, 1),
    (rbox, 1) => (m1, 2),
    (m1, 1)   => (δbox, 1),
    (δbox, 1) => (m2, 1),
    (δbox, 2) => (m2, 2),
    (m2, 1)   => (output_id(sr2), 1)]);

R_copy = WiringDiagram(One, Two);
r, cpy = add_boxes!(R_copy, [R, δ()]);
add_wires!(R_copy, Pair[
    (input_id(R_copy), 1) => (r, 1),
    (r, 1)                => (cpy, 1),
    (cpy, 1)              => (output_id(R_copy), 1),
    (cpy, 2)              => (output_id(R_copy), 2)]);

fig26 = WiringDiagram(One, Two);
cpy,f1,g1,f2,g2 = add_boxes!(fig26, [δ(), f, g, f, g]);
add_wires!(fig26, Pair[
    (input_id(fig26), 1) => (cpy, 1),
    (cpy, 1)             => (f1, 1),
    (cpy, 2)             => (f2, 1),
    (f1, 1)              => (g1, 1),
    (f2, 1)              => (g2, 1),
    (g1, 1)              => (output_id(fig26), 1),
    (g2, 1)              => (output_id(fig26), 2)]);

ex211 = WiringDiagram(Six, Five)
b01,b02,b03,b04,b11,b12,b21,b22,b23 = add_boxes!(ex211, [
    μ(), μ(), μ(), δ(), η(), ϵ(), μ(), δ(), δ()]);
add_wires!(ex211, Pair[
    (input_id(ex211), 1) => (b02, 1),
    (input_id(ex211), 2) => (b01, 1),
    (input_id(ex211), 3) => (b01, 2),
    (input_id(ex211), 4) => (b03, 2),
    (input_id(ex211), 5) => (b21, 2),
    (input_id(ex211), 6) => (b21, 1),
    (b01, 1)             => (b02, 2),
    (b02, 1)             => (b03, 1),
    (b03, 1)             => (b04, 1),
    (b11, 1)             => (b12, 1),
    (b21, 1)             => (b22, 1),
    (b22, 2)             => (b23, 1),
    (b04,1)              => (output_id(ex211), 1),
    (b04,2)              => (output_id(ex211), 2),
    (b22,1)              => (output_id(ex211), 3),
    (b23,1)              => (output_id(ex211), 4),
    (b23,2)              => (output_id(ex211), 5)]);

ex211b = WiringDiagram(Five, Four)
b1, b2, b3, b4 = add_boxes!(ex211b, [dot(), μ(), dot(), dot()]);
add_wires!(ex211b, Pair[
    (input_id(ex211b), 1) => (b1, 1),
    (input_id(ex211b), 2) => (b2, 1),
    (input_id(ex211b), 3) => (b2, 2),
    (input_id(ex211b), 4) => (b3, 1),
    (input_id(ex211b), 5) => (b4, 1),
    (b1,1)                => (output_id(ex211b), 1),
    (b2,1)                => (output_id(ex211b), 2),
    (b3,1)                => (output_id(ex211b), 3),
    (b4,1)                => (output_id(ex211b), 4)]);

refls_1 = WiringDiagram([:O], [:O])
idbox, sbox = add_boxes!(refls_1, [Id, s]);
add_wires!(refls_1, Pair[
    (input_id(refls_1), 1) => (idbox, 1),
    (idbox, 1)             => (sbox, 1),
    (sbox, 1)              => (output_id(refls_1), 1)]);

reflt_1 = WiringDiagram([:O], [:O])
idbox, tbox = add_boxes!(reflt_1, [Id, t]);
add_wires!(reflt_1, Pair[
    (input_id(reflt_1), 1) => (idbox, 1),
    (idbox, 1)             => (tbox, 1),
    (tbox, 1)              => (output_id(reflt_1), 1)]);

o1 = WiringDiagram([:O], [:O])
dotbox = add_box!(o1, dot(:O));
add_wires!(o1, Pair[
    (input_id(o1), 1) => (dotbox, 1),
    (dotbox, 1)       => (output_id(o1), 1)]);

cmp_1 = WiringDiagram([:A, :A], [])
δ1, δ2, μbox, ϵ1, ϵ2, ϵ3, s1, s2, t1, t2 = add_boxes!(cmp_1, [
    δ(:A), δ(:A), μ(:O), ϵ(:O), ϵ(:O), ϵ(:O), s, s, t ,t]);
add_wires!(cmp_1, Pair[
    (input_id(cmp_1), 1) => (δ1, 1),
    (input_id(cmp_1), 2) => (δ2, 1),
    (δ1, 1)       =>  (s1,1),
    (δ1, 2)       =>  (t1,1),
    (δ2, 1)       =>  (s2,1),
    (δ2, 2)       =>  (t2,1),
    (t1, 1) => (μbox, 1),
    (s2, 1) => (μbox, 2),
    (μbox, 1) => (ϵ2, 1),
    (s1, 1) => (ϵ1, 1),
    (t2, 1) => (ϵ3, 1),]);

cmp_2 = WiringDiagram([:A, :A], [])
c, s1, s2, t1, t2, δ1, δ2,δ3, μ1, μ2, ϵ1, ϵ2 = add_boxes!(cmp_2, [
    cmp, s, s, t ,t, δ(:A), δ(:A), δ(:A), μ(:O), μ(:O), ϵ(:O), ϵ(:O),]);
add_wires!(cmp_2, Pair[
    (input_id(cmp_1), 1) => (δ1, 1),
    (input_id(cmp_1), 2) => (δ2, 1),
    (δ1, 1)              => (s1, 1),
    (δ1, 2)              => (c,  1),
    (δ2, 1)              => (c,  2),
    (δ2, 2)              => (t1, 1),
    (c,  1)              => (δ3, 1),
    (δ3, 1)              => (s2, 1),
    (δ3, 2)              => (t2, 1),
    (s1, 1)              => (μ1, 1),
    (s2, 1)              => (μ1, 2),
    (t1, 1)              => (μ2, 1),
    (t2, 1)              => (μ2, 2),
    (μ1, 1)              => (ϵ1, 1),
    (μ2, 1)              => (ϵ2, 1)])


# Equations
mul_assoc  = assoc(mmul);
cmp_assoc  = assoc(cmp);
leftid     = Eq(:leftid,     leftid_1,     passthru,     true);
rightid    = Eq(:rightid,    rightid_1,    passthru,     true);
leftinv    = Eq(:leftinv,    leftinv_1,    e11,          true);
rightinv   = Eq(:rightinv,   rightinv_1,   e11,          true);
uniq_inv   = Eq(:uniq_inv,   uniq_inv_1,   uniq_inv_2,   true);
gdiv       = Eq(:gdiv,       div_1,        div_2,        true);
leftcancel = Eq(:leftcancel, leftcancel_1, leftcancel_2, true);
s_order_2  = Eq(:s_ord_2,    ss,           e_wd,         true);
r_order_3  = Eq(:r_ord_3,    rrr,          e_wd,         true);
refls      = Eq(:refls,      refls_1,      o1,           true);
reflt      = Eq(:reflt,      reflt_1,      o1,           true);
cmp_intro  = Eq(:cmp,        cmp_1,        cmp_2,        false);

# Equation sets
I_monoid = Set([mul_assoc, leftid, rightid]);
I_group  = Set([leftinv, rightinv]);
I_d3h    = Set([s_order_2, r_order_3]);
I_reflG  = Set([refls, reflt])
I_cat    = Set{Eq}() # TODO associativity of cmp

# Theories
T_monoid = EqTheory(Σ_monoid, I_monoid);
T_group  = union(T_monoid, Σ_group, I_group)
T_d3h    = union(T_group, Σ_dihedral, I_d3h);
T_reflG  = EqTheory(Σ_reflG, I_reflG)
T_cat    = union(T_reflG, Σ_cat, I_cat)