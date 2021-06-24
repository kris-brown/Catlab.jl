include("/Users/ksb/Catlab.jl/src/atp/ATP.jl")
using Catlab.WiringDiagrams

tf = [true, false]
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
o_o  = Box(Symbol("⊗ₒ"), [:O,:O], [:O]);
o_a  = Box(Symbol("⊗ₐ"), [:A,:A], [:A]);
ounit= Box(:⊤, Symbol[], [:O])
σ    = Box(:σ, [:O, :O], [:A])
del  = Box(:δ, [:O], [:A])
eps  = Box(:ϵ, [:O], [:A])
mu   = Box(:μ, [:O], [:A])
ev   = Box(:ev, [:O, :O], [:A])
Exp   = Box(:exp, [:O, :O], [:O])
lam   = Box(:λ, [:O, :O, :O, :A], [:A])

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
Σ_mc       = Set([o_o, o_a, ounit])
Σ_smc      = Set([σ])
Σ_crc      = Set([del, eps])
Σ_dcr      = Set([mu])
Σ_ccc      = Set([ev, Exp, lam])

# Diagrams
function assoc(b::Box{Symbol})::Eq
    s = b.value
    in_t = collect(Set(b.input_ports))
    err = "assoc requires binary function: $b"
    length(in_t) == 1 && in_t == b.output_ports || error(err)
    typ = in_t[1]
    l = WiringDiagram([typ,typ,typ], [typ]);
    m1, m2 = add_boxes!(l, [b, b])
    add_wires!(l, Pair[
        (input_id(l), 1) => (m1, 1),
        (input_id(l), 2) => (m1, 2),
        (input_id(l), 3) => (m2, 2),
        (m1, 1)          => (m2, 1),
        (m2, 1)          => (output_id(l), 1)]);

    r = WiringDiagram([typ,typ,typ], [typ]);
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

function passthru(x::Symbol=:X)::WD
    wd = WiringDiagram([x], [x])
    node = add_box!(wd, dot(x));
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (node,1),
        (node,1)          => (output_id(wd), 1)]);
    return wd
end

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

function reflid(is_s::Bool)::WD
    wd = WiringDiagram([:O], [:O])
    ibox, b = add_boxes!(wd, [Id, is_s ? s : t])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (ibox, 1),
        (ibox, 1)         => (b, 1),
        (b, 1)            => (output_id(wd), 1)])
    return wd
end

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

function idcat(is_s::Bool)::WD
    wd = WiringDiagram([:A], [:A])
    ibox, b, δbox, cbox = add_boxes!(wd, [Id, is_s ? s : t, δ(:A), cmp])
    i, j = is_s ? (1, 2) : (2, 1)
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (δbox, 1),
        (δbox, j)         => (cbox, j),
        (δbox, i)         => (b, 1),
        (b, 1)            => (ibox, 1),
        (ibox, 1)         => (cbox, i),
        (cbox, 1)         => (output_id(wd), 1)])
    return wd
end

function ofunc_st(is_s::Bool)::Eq
    st = is_s ? s : t
    l = WiringDiagram([:A,:A],[:O])
    obox, ost = add_boxes!(l, [o_a, st])
    add_wires!(l, Pair[
        (input_id(l), 1) => (obox, 1),
        (input_id(l), 2) => (obox, 2),
        (obox, 1)        => (ost, 1),
        (ost, 1)         => (output_id(l), 1)
    ])
    r = WiringDiagram([:A,:A],[:O])
    ost1, ost2, obox = add_boxes!(r, [st, st, o_o])
    add_wires!(r, Pair[
        (input_id(r), 1) => (ost1, 1),
        (input_id(r), 2) => (ost2, 1),
        (ost1, 1)        => (obox, 1),
        (ost2, 1)        => (obox, 2),
        (obox, 1)        => (output_id(r), 1)
    ])

    return Eq(Symbol("o_func_$(st.value)"), l, r, true)
end

o_f_c_1 = WiringDiagram([:A,:A,:A,:A],[:A])
o1, o2, cbox = add_boxes!(o_f_c_1, [o_a, o_a, cmp])
add_wires!(o_f_c_1,  Pair[
    (input_id(o_f_c_1), 1) => (o1, 1),
    (input_id(o_f_c_1), 2) => (o1, 2),
    (input_id(o_f_c_1), 3) => (o2, 1),
    (input_id(o_f_c_1), 4) => (o2, 2),
    (o1, 1) => (cbox, 1),
    (o2, 1) => (cbox, 2),
    (cbox, 1) => (output_id(o_f_c_1), 1)])

o_f_c_2 = WiringDiagram([:A,:A,:A,:A],[:A])
c1, c2, obox = add_boxes!(o_f_c_2, [cmp, cmp, o_a])
add_wires!(o_f_c_2, Pair[
    (input_id(o_f_c_2), 1) => (c1, 1),
    (input_id(o_f_c_2), 2) => (c2, 1),
    (input_id(o_f_c_2), 3) => (c1, 2),
    (input_id(o_f_c_2), 4) => (c2, 2),
    (c1, 1) => (obox, 1),
    (c2, 1) => (obox, 2),
    (obox, 1) => (output_id(o_f_c_2), 1)])

lunit_o_a_ = WiringDiagram([:A],[:A])
tbox, ibox, obox = add_boxes!(lunit_o_a_, [ounit, Id, o_a])
add_wires!(lunit_o_a_, Pair[
    (input_id(lunit_o_a_), 1) => (obox, 2),
    (tbox,1)  => (ibox, 1),
    (ibox, 1) => (obox, 1),
    (obox,1)  => (output_id(lunit_o_a_), 1)])

runit_o_a_ = WiringDiagram([:A],[:A])
tbox, ibox, obox = add_boxes!(runit_o_a_, [ounit, Id, o_a])
add_wires!(runit_o_a_, Pair[
    (input_id(runit_o_a_), 1) => (obox, 1),
    (tbox,1)  => (ibox,1),
    (ibox, 1) => (obox, 2),
    (obox,1)  => (output_id(runit_o_a_), 1)])

lunit_o_o_ = WiringDiagram([:O],[:O])
tbox, obox = add_boxes!(lunit_o_o_, [ounit, o_o ])
add_wires!(lunit_o_o_, Pair[
    (input_id(lunit_o_o_), 1) => (obox,1),
    (tbox,1)  => (obox,2),
    (obox,1)  => (output_id(lunit_o_o_), 1)])

runit_o_o_ = WiringDiagram([:O],[:O])
tbox, obox = add_boxes!(runit_o_o_, [ounit, o_o])
add_wires!(runit_o_o_, Pair[
    (input_id(runit_o_o_), 1) => (obox,2),
    (tbox,1)  => (obox,1),
    (obox,1)  => (output_id(runit_o_o_), 1)])


bb_1 = WiringDiagram([:O, :O], [:A])
δ1, δ2, s1, s2, cbox = add_boxes!(bb_1, [δ(:O), δ(:O), σ, σ, cmp])
add_wires!(bb_1, Pair[
    (input_id(bb_1), 1) => (δ1,1),
    (input_id(bb_1), 2) => (δ2,1),
    (δ1, 1) => (s1,1),
    (δ1, 2) => (s2,2),
    (δ2, 1) => (s1,2),
    (δ2, 2) => (s2,1),
    (s1, 1) => (cbox, 1),
    (s2, 1) => (cbox, 2),
    (cbox, 1) => (output_id(bb_1), 1)])

bb_2 = WiringDiagram([:O, :O], [:A])
obox, ibox = add_boxes!(bb_2, [o_o, Id])
add_wires!(bb_2, Pair[
    (input_id(bb_2), 1) => (obox,1),
    (input_id(bb_2), 2) => (obox,2),
    (obox, 1) => (ibox, 1),
    (ibox, 1) => (output_id(bb_2), 1)])

function braid_ts(is_s::Bool)::Eq
    st = is_s ? s : t
    l =  WiringDiagram([:O,:O],[:O])
    sbox, xbox = add_boxes!(l, [σ, st])
    add_wires!(l, Pair[
        (input_id(l), 1) => (sbox,1),
        (input_id(l), 2) => (sbox,2),
        (sbox, 1)        => (xbox, 1),
        (xbox,1)         => (output_id(l), 1)])
    r =  WiringDiagram([:O,:O],[:O])
    b = add_box!(r, o_o)
    add_wires!(r, Pair[
        (input_id(r), 1) => (b,is_s ? 1 : 2),
        (input_id(r), 2) => (b,is_s ? 2 : 1),
        (b,1) => (output_id(r), 1)])
    return Eq(Symbol("braid_$(st.value)"), l ,r, true)
end

function braid_ots_ts(is_s::Bool)::WD
    st = is_s ? s : t
    wd = WiringDiagram([:A,:A],[:A])
    δ1, δ2, obox, x1, x2, sbox, cbox = add_boxes!(wd, [
        δ(:A), δ(:A),o_a, st, st, σ,cmp])
    i, j = is_s ? (2,1) : (1,2)
    xs = [x1, x2]
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (δ1, 1),
        (input_id(wd), 2) => (δ2, 1),
        (δ1, i) => (obox, i),
        (δ1, j) => (xs[i],1),
        (δ2, i) => (obox, j),
        (δ2, j) => (xs[j], 1),
        (xs[i], 1) => (sbox, 1),
        (xs[j], 1) => (sbox, 2),
        (sbox, 1) => (cbox, j),
        (obox, 1) => (cbox, i),
        (cbox, 1) => (output_id(wd), 1)])
    return wd
end

function epsdel_s(is_eps::Bool)::Eq
    ed = is_eps ? eps : del
    l = WiringDiagram([:O], [:O])
    xbox, sb = add_boxes!(l, [ed, s])
    add_wires!(l, Pair[
        (input_id(l), 1) => (xbox,1),
        (xbox,1) => (sb,1),
        (sb, 1)=> (output_id(l), 1)])
    r = passthru(:O)
    return Eq(Symbol("$(ed.value)_s"), l, r, true)
end

function ed_t_1(is_eps::Bool)::WD
    ed = is_eps ? eps : del
    wd = WiringDiagram([:O], [:O])
    xbox, tbox = add_boxes!(wd, [ed, t])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (xbox,1),
        (xbox, 1) => (tbox, 1),
        (tbox,1) => (output_id(wd), 1)])
    return wd
end

del_t_2 = WiringDiagram([:O], [:O])
dbox, obox = add_boxes!(del_t_2, [δ(:O), o_o])
add_wires!(del_t_2, Pair[
    (input_id(del_t_2), 1) => (dbox, 1),
    (dbox, 1) => (obox, 1),
    (dbox, 2) => (obox, 2),
    (obox, 1) => (output_id(del_t_2), 1)])

eps_t_2 = WiringDiagram([:O], [:O])
ebox, tbox = add_boxes!(eps_t_2, [ϵ(:O), ounit])
add_wires!(eps_t_2, Pair[
    (input_id(eps_t_2), 1) => (ebox, 1),
    (tbox, 1) => (output_id(eps_t_2), 1)])

eps_coh_1 = WiringDiagram([:O, :O], [:A])
obox, ebox = add_boxes!(eps_coh_1, [o_o, eps])
add_wires!(eps_coh_1, Pair[
    (input_id(eps_coh_1), 1) => (obox,1),
    (input_id(eps_coh_1), 2) => (obox,2),
    (obox, 1) => (ebox, 1),
    (ebox,1) =>  (output_id(eps_coh_1), 1)])

eps_coh_2 = WiringDiagram([:O,:O], [:A])
e1, e2, obox = add_boxes!(eps_coh_2, [eps, eps, o_a])
add_wires!(eps_coh_2, Pair[
    (input_id(eps_coh_2), 1) => (e1, 1),
    (input_id(eps_coh_2), 2) => (e2, 1),
    (e1,1) =>(obox, 1),
    (e2,1) =>(obox, 2),
    (obox, 1) => (output_id(eps_coh_2), 1)])
#
del_coh_1 = WiringDiagram([:O, :O], [:A])
obox, dbox = add_boxes!(del_coh_1, [o_o, del])
add_wires!(del_coh_1, Pair[
    (input_id(del_coh_1), 1) => (obox, 1),
    (input_id(del_coh_1), 2) => (obox, 2),
    (obox, 1)                => (dbox, 1),
    (dbox, 1)                => (output_id(del_coh_1), 1)])

del_coh_2 = WiringDiagram([:O, :O], [:A])
δ1, δ2, δ3, δ4, μbox, o1, o2, o3, i1, i2, sbox, d1, d2 = add_boxes!(del_coh_2, [
    δ(:O), δ(:O), δ(:O), δ(:O), μ(:A), o_a, o_a, o_a, Id, Id, σ, del, del])
add_wires!(del_coh_2, Pair[
    (input_id(del_coh_2), 1) => (δ1, 1),
    (input_id(del_coh_2), 2) => (δ2, 1),
    (δ1, 1) => (δ3,1),
    (δ2, 1) => (δ4,1),
    (δ1, 2) => (d1,1),
    (δ2, 2) => (d2,1),
    (δ3, 1) => (i1,1),
    (δ3, 2) => (sbox,1),
    (δ4, 1) => (sbox,2),
    (δ4, 2) => (i2,1),
    (i1, 1) => (o1, 1),
    (sbox, 1) => (o1, 2),
    (o1, 1) => (o2, 1),
    (i2, 1) => (o2, 2),
    (o2, 1) => (μbox, 1),
    (d1, 1) => (o3, 1),
    (d2, 1) => (o3, 2),
    (o3, 1) => (μbox, 2),
    (μbox, 1) => (output_id(del_coh_2), 1)])

del_nat_1 = WiringDiagram([:O], [:A])
δ1, δ2, dbox, sbox, cbox = add_boxes!(del_nat_1, [δ(:O), δ(:O), del, σ, cmp])
add_wires!(del_nat_1, Pair[
    (input_id(del_nat_1), 1) => (δ1, 1),
    (δ1, 1) => (dbox, 1),
    (δ1, 2) => (δ2, 1),
    (δ2, 1) => (sbox,1),
    (δ2, 2) => (sbox,2),
    (dbox, 1) => (cbox, 1),
    (sbox, 1) => (cbox, 2),
    (cbox, 1) => (output_id(del_nat_1), 1)])

del_nat_2 = WiringDiagram([:O], [:A])
b = add_box!(del_nat_2, del)
add_wires!(del_nat_2, Pair[
    (input_id(del_nat_2),1) => (b,1),
    (b,1)                  => (output_id(del_nat_2), 1)])


#
function cc1_(is_left::Bool, is_del::Bool)::WD
    wd = WiringDiagram([:O], [:A])
    de = is_del ? del : eps
    δ1, δ2, d1, d2, ibox, obox, cbox = add_boxes!(wd, [
        δ(:O),δ(:O),del,de,Id,o_a,cmp])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (δ1,1),
        (δ1,2) => (δ2,1),
        (δ1,1) => (d1,1),
        (δ2,1) => (d2,1),
        (δ2,2) => (ibox,1),
        (d2, 1) => (obox, is_left ? 1 : 2),
        (ibox, 1) => (obox, is_left ? 2 : 1),
        (d1, 1) => (cbox, 1),
        (obox, 1) => (cbox, 2),
        (cbox,1) => (output_id(wd), 1)])
    return wd
end

cc3_1 = WiringDiagram([:A], [:A])
δ1,δ2,sbox,dbox,obox,cbox = add_boxes!(cc3_1, [δ(:A),δ(:A),s,del,o_a,cmp])
add_wires!(cc3_1, Pair[
    (input_id(cc3_1), 1) => (δ1,1),
    (δ1,2) => (δ2,1),
    (δ1,1) => (sbox,1),
    (δ2,1) => (obox,1),
    (δ2,2) => (obox,2),
    (sbox, 1) => (dbox, 1),
    (dbox, 1) => (cbox, 1),
    (obox, 1) => (cbox, 2),
    (cbox,1) => (output_id(cc3_1), 1)])

cc3_2 = WiringDiagram([:A], [:A])
δbox, tbox, dbox, cbox = add_boxes!(cc3_2, [δ(:A), t, del, cmp])
add_wires!(cc3_2, Pair[
    (input_id(cc3_2), 1) => (δ1,1),
    (δ1, 1) => (cbox, 1),
    (δ1, 2) => (tbox, 1),
    (tbox, 1) => (dbox, 1),
    (dbox, 1) => (cbox, 2),
    (cbox,1) => (output_id(cc3_2), 1)])
#
function delmu(forward::Bool)::WD
    wd = WiringDiagram([:O], [:A])
    δbox, dbox, mbox, cbox = add_boxes!(wd, [δ(:O), del, mu, cmp])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (δbox, 1),
        (δbox, 1) => (dbox,1),
        (δbox, 2) => (mbox,1),
        (dbox, 1) => (cbox, forward ? 1 : 2),
        (mbox, 1) => (cbox, forward ? 2 : 1 ),
        (cbox, 1) => (output_id(wd), 1)])
    return wd
end

idbox = WiringDiagram([:O], [:A])
b = add_box!(idbox, Id)
add_wires!(idbox, Pair[
    (input_id(idbox),1) => (b, 1),
    (b, 1) => (output_id(idbox), 1)])

function projmu(is_s::Bool)::Eq
    st = is_s ? s : t
    wd = WiringDiagram([:O], [:O])
    mbox, stbox = add_boxes!(wd, [mu, st])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (mbox, 1),
        (mbox, 1) => (stbox, 1),
        (stbox, 1) => (output_id(wd), 1)])
    return Eq(Symbol("mu_$(st.value)"), wd, passthru(:O), true)
end

function frob(is_left::Bool)::Eq
    wd = WiringDiagram([:O], [:A])
    δ1,δ2,δ3,i1,i2,dbox,mbox,o1,o2,cbox = add_boxes!(wd, [
        δ(:O),δ(:O),δ(:O),Id,Id,del,mu,o_a,o_a,cmp])
    b1, b2, b3, b4 = is_left ? (i1, dbox, mbox, i2) : (dbox, i1, i2, mbox)
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (δ1, 1),
        (δ1, 1) => (δ2, 1),
        (δ1, 2) => (δ3, 1),
        (δ2, 1) => (b1, 1),
        (δ2, 2) => (b2,1),
        (δ3, 1) => (b3,1),
        (δ3, 2) => (b4,1),
        (b1, 1) => (o1, 1),
        (b2, 1) => (o1, 2),
        (b3, 1) => (o2, 1),
        (b4, 1) => (o2, 2),
        (o1, 1) => (cbox, 1),
        (o2, 1) => (cbox, 2),
        (cbox, 1)=>(output_id(wd),1)])
    return Eq(Symbol("frob_" * (is_left ? "l" : "r")), wd, delmu(false), true)
end

epsnat1 = WiringDiagram([:A],[:A])
dbox, tbox, ebox, cbox = add_boxes!(epsnat1, [δ(:A), t, eps, cmp])
add_wires!(epsnat1, Pair[
    (input_id(epsnat1), 1) => (dbox, 1),
    (dbox, 1) => (cbox, 1),
    (dbox, 2) => (tbox, 1),
    (tbox, 1) => (ebox, 1),
    (ebox, 1 )=> (cbox, 2),
    (cbox, 1) => (output_id(epsnat1),1)])

epsnat2 = WiringDiagram([:A],[:A])
sbox, ebox = add_boxes!(epsnat2, [s, eps])
add_wires!(epsnat2, Pair[
    (input_id(epsnat2), 1) => (sbox, 1),
    (sbox, 1) => (ebox, 1),
    (ebox, 1) => (output_id(epsnat2), 1)])
#
function evst1(is_s::Bool)::WD
    st = is_s ? s : t
    wd = WiringDiagram([:O, :O], [:O])
    ebox, sbox = add_boxes!(wd, [ev, st])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (ebox, 1),
        (input_id(wd), 2) => (ebox, 2),
        (ebox, 1) => (sbox, 1),
        (sbox, 1) => (output_id(wd), 1)])
    return wd
end
evs2 = WiringDiagram([:O, :O], [:O])
ebox, obox, dbox = add_boxes!(evs2, [Exp, o_o, δ(:O)])
add_wires!(evs2, Pair[
    (input_id(evs2), 1) => (dbox, 1),
    (input_id(evs2), 2) => (ebox, 2),
    (dbox, 1) => (ebox, 1),
    (dbox, 2) => (obox, 2),
    (ebox, 1) => (obox, 1),
    (obox, 1) => (output_id(evs2), 1)])

evt2 = WiringDiagram([:O, :O], [:O])
ebox, dbox = add_boxes!(evt2, [ϵ(:O), dot(:O)])
add_wires!(evt2, Pair[
    (input_id(evt2), 1) => (ebox, 1),
    (input_id(evt2), 2) => (dbox, 1),
    (dbox, 1) => (output_id(evt2), 1)])
#
lam_intro1 = WiringDiagram([:O,:O,:O,:A],Symbol[])
sbox, tbox, ϵ1, ϵ2, μ1, μ2, δ1, obox = add_boxes!(lam_intro1, [
    s, t, ϵ(:O), ϵ(:O), μ(:O), μ(:O), δ(:A), o_o])
add_wires!(lam_intro1, Pair[
    (input_id(lam_intro1), 1) => (obox,1),
    (input_id(lam_intro1), 2) => (obox,2),
    (input_id(lam_intro1), 3) => (μ2,2),
    (input_id(lam_intro1), 4) => (δ1,1),
    (δ1, 1) => (sbox,1),
    (δ1, 2) => (tbox,1),
    (sbox, 1) => (μ1, 2),
    (tbox, 1) => (μ2, 1),
    (obox, 1) => (μ1, 1),
    (μ1, 1) => (ϵ1, 1),
    (μ2, 1) => (ϵ2, 1),])

lam_intro2 = WiringDiagram([:O,:O,:O,:A], Symbol[])
b, cap = add_boxes!(lam_intro2, [lam, ϵ(:A)])
add_wires!(lam_intro2, Pair[
    (input_id(lam_intro2), 1) => (b,1),
    (input_id(lam_intro2), 2) => (b,2),
    (input_id(lam_intro2), 3) => (b,3),
    (input_id(lam_intro2), 4) => (b,4),
    (b, 1) => (cap, 1)])

function lam_st(is_s::Bool)::WD
    wd = WiringDiagram([:O,:O,:O,:A],[:O])
    st = is_s ? s : t
    lbox, sbox = add_boxes!(wd, [lam, st])
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (lbox,1),
        (input_id(wd), 2) => (lbox,2),
        (input_id(wd), 3) => (lbox,3),
        (input_id(wd), 4) => (lbox,4),
        (lbox, 1) => (sbox, 1),
        (sbox, 1) => (output_id(wd), 1)])
    return wd
end
lam_s2 = WiringDiagram([:O,:O,:O,:A],[:O])
e1,e2,e3,dbox = add_boxes!(lam_s2, [ϵ(:O),ϵ(:O),ϵ(:A),dot(:O)])
add_wires!(lam_s2, Pair[
    (input_id(lam_s2), 1) => (dbox,1),
    (input_id(lam_s2), 2) => (e1,1),
    (input_id(lam_s2), 3) => (e2,1),
    (input_id(lam_s2), 4) => (e3,1),
    (dbox, 1) => (output_id(lam_s2), 1)])

lam_t2 = WiringDiagram([:O,:O,:O,:A],[:O])
e1, e2, expbox = add_boxes!(lam_t2, [ϵ(:O),ϵ(:A),Exp])
add_wires!(lam_t2, Pair[
    (input_id(lam_t2), 1) => (e1,1),
    (input_id(lam_t2), 2) => (expbox,1),
    (input_id(lam_t2), 3) => (expbox,2),
    (input_id(lam_t2), 4) => (e2,1),
    (expbox, 1) => (output_id(lam_t2), 1)])
lam_eqf1 = WiringDiagram([:O,:O,:O,:A],[:A])
d1,d2,d3,lbox, obox, ibox, ebox, cbox = add_boxes!(lam_eqf1,[
    δ(:O),δ(:O),δ(:O),lam, o_a,Id,ev,cmp])
add_wires!(lam_eqf1, Pair[
    (input_id(lam_eqf1), 1) => (lbox,1),
    (input_id(lam_eqf1), 2) => (d1,1),
    (input_id(lam_eqf1), 3) => (d2,1),
    (input_id(lam_eqf1), 4) => (lbox,4),
    (d1, 1) => (lbox,2),
    (d1, 2) => (d3,1),
    (d3, 1) => (ibox,1),
    (d3, 2) => (ebox,1),
    (d2, 1) => (lbox,3),
    (d2, 2) => (ebox,2),
    (lbox, 1) => (obox, 1),
    (ibox, 1) => (obox, 2),
    (obox, 1) => (cbox, 1),
    (ebox, 1) => (cbox, 2),
    (cbox,1) => (output_id(lam_eqf1), 1)])

lam_eqf2 = WiringDiagram([:O,:O,:O,:A],[:A])
obox,d1,d2,sbox, tbox, m1, m2, e1, e2 =add_boxes!(lam_eqf2, [
    o_o, δ(:A), δ(:A), s, t, μ(:O),μ(:O),ϵ(:O),ϵ(:O)])
add_wires!(lam_eqf2, Pair[
    (input_id(lam_eqf2), 1) => (obox,1),
    (input_id(lam_eqf2), 2) => (obox,2),
    (input_id(lam_eqf2), 3) => (m2,2),
    (input_id(lam_eqf2), 4) => (d1,1),
    (obox, 1) => (m1, 1),
    (m1, 1) => (e1, 1),
    (m2, 1) => (e2, 1),
    (d1, 1) => (d2, 1),
    (d2, 1) => (sbox, 1),
    (sbox, 1) => (m1, 2),
    (d2, 2) => (tbox, 1),
    (tbox, 1) => (m2, 1),
    (d1,2) => (output_id(lam_eqf2), 1)])

lam_eqg1 = WiringDiagram([:O,:O,:O,:A],[:A])
ebox, d1, d2, sbox, tbox, m1, m2, e1, e2 = add_boxes!(lam_eqg1, [
    Exp, δ(:A), δ(:A), s, t, μ(:O),μ(:O),ϵ(:O),ϵ(:O)])
add_wires!(lam_eqg1, Pair[
    (input_id(lam_eqg1), 1) => (m1,1),
    (input_id(lam_eqg1), 2) => (ebox,1),
    (input_id(lam_eqg1), 3) => (ebox,2),
    (input_id(lam_eqg1), 4) => (d1,1),
    (d1, 1) => (d2, 1),
    (d2, 1) => (sbox,1),
    (d2, 2) => (tbox,1),
    (sbox, 1) => (m1, 2),
    (tbox, 1) => (m2, 1),
    (ebox, 1) => (m2, 2),
    (m1, 1) => (e1, 1),
    (m2, 1) => (e2, 1),
    (d1,2) => (output_id(lam_eqg1), 1)])

lam_eqg2 = WiringDiagram([:O,:O,:O,:A],[:A])
d1, d2, d3, ebox, ibox, obox, cbox, lbox = add_boxes!(lam_eqg2, [
    δ(:O), δ(:O), δ(:O), ev, Id, o_a, cmp, lam])
add_wires!(lam_eqg2, Pair[
    (input_id(lam_eqg2), 1) => (lbox,1),
    (input_id(lam_eqg2), 2) => (d1,1),
    (input_id(lam_eqg2), 3) => (d3,1),
    (input_id(lam_eqg2), 4) => (obox,1),
    (d1, 1) => (d2,1),
    (d1, 2) => (ibox,1),
    (d2, 1) => (lbox,2),
    (d2, 2) => (ebox,1),
    (d3, 1) => (ebox,2),
    (d3, 2) => (lbox,3),
    (ibox, 1) => (obox, 2),
    (obox, 1) => (cbox, 1),
    (ebox, 1) => (cbox, 2),
    (cbox, 1) => (lbox, 4),
    (lbox,1) => (output_id(lam_eqg2), 1)])

# Equations
mul_assoc, cmp_assoc, o_o_assoc, o_a_assoc  = map(assoc, [mmul, cmp, o_o, o_a])
o_func_s, o_func_t = map(ofunc_st, tf)

leftid     = Eq(:leftid,     leftid_1,     passthru(),   true);
rightid    = Eq(:rightid,    rightid_1,    passthru(),   true);
leftinv    = Eq(:leftinv,    leftinv_1,    e11,          true);
rightinv   = Eq(:rightinv,   rightinv_1,   e11,          true);
uniq_inv   = Eq(:uniq_inv,   uniq_inv_1,   uniq_inv_2,   true);
gdiv       = Eq(:gdiv,       div_1,        div_2,        true);
leftcancel = Eq(:leftcancel, leftcancel_1, leftcancel_2, true);
s_order_2  = Eq(:s_ord_2,    ss,           e_wd,         true);
r_order_3  = Eq(:r_ord_3,    rrr,          e_wd,         true);
refls      = Eq(:refls,      reflid(true), passthru(:O), true);
reflt      = Eq(:reflt,      reflid(false),passthru(:O), true);
cmp_intro  = Eq(:cmp,        cmp_1,        cmp_2,        false);
l_unit     = Eq(:l_unit,     idcat(true),  passthru(:A), true);
r_unit     = Eq(:r_unit,     idcat(false), passthru(:A), true);
o_func_cmp = Eq(:o_func_cmp, o_f_c_1,      o_f_c_2,      true);
lunit_o_a  = Eq(:lunit_o_a,  lunit_o_a_,   passthru(:A), true);
runit_o_a  = Eq(:runit_o_a,  runit_o_a_,   passthru(:A), true);
lunit_o_o  = Eq(:lunit_o_o,  lunit_o_o_,   passthru(:O), true);
runit_o_o  = Eq(:runit_o_o,  runit_o_o_,   passthru(:O), true);
braidbraid = Eq(:braidbraid, bb_1,         bb_2,         true);

braid_s, braid_t = map(braid_ts, tf)
braid_ots = Eq(:braid_ots, braid_ots_ts(false), braid_ots_ts(true), true);

eps_s, del_s = map(epsdel_s, tf)
eps_t   = Eq(:eps_o, ed_t_1(true), eps_t_2, true);
del_t   = Eq(:del_t, ed_t_1(false), del_t_2, true);
eps_coh = Eq(:eps_coh, eps_coh_1, eps_coh_2, true);
del_coh = Eq(:del_coh, del_coh_1, del_coh_2, true);
del_nat = Eq(:del_nat, del_nat_1, del_nat_2, true);
cc1 = Eq(:cc1, cc1_(true, true), cc1_(false, true), true);
cc2 = Eq(:cc2, cc1_(true, false), cc1_(false, false), true);
cc3 = Eq(:cc3, cc3_1, cc3_2, true);
bone = Eq(:bone, delmu(true), idbox, true)
proj1, proj2 = map(projmu, tf)
frob1, frob2 = map(frob, tf)
eps_nat = Eq(:epsnat, epsnat1, epsnat2, true)

evs = Eq(:evs, evst1(true), evs2, true)
evt = Eq(:evt, evst1(false), evt2, true)
λ_intro = Eq(:λ_intro, lam_intro1, lam_intro2, false)
lam_s = Eq(:lam_s, lam_st(true), lam_s2, true)
lam_t = Eq(:lam_t, lam_st(false), lam_t2, true)
lam_eqf = Eq(:lam_eqf, lam_eqf1, lam_eqf2, true)
lam_eqg = Eq(:lam_eqg, lam_eqg1, lam_eqg2, true)

# Equation sets
I_monoid = Set([mul_assoc, leftid, rightid]);
I_group  = Set([leftinv, rightinv]);
I_d3h    = Set([s_order_2, r_order_3]);
I_reflG  = Set([refls, reflt])
I_cat    = Set([cmp_assoc, l_unit, r_unit])
I_mc     = Set([o_o_assoc, o_a_assoc, o_func_s, o_func_t, o_func_cmp,
                lunit_o_a, runit_o_a, lunit_o_o, runit_o_o])
I_smc    = Set([braidbraid, braid_t, braid_s, braid_ots])
I_crc    = Set([eps_s, del_s, eps_t, del_t, eps_coh, del_coh, del_nat,
                cc1, cc2, cc3])
I_dcr = Set([bone, proj1, proj2, frob1, frob2])
I_cc = Set([eps_nat])
I_ccc = Set([evs, evt, λ_intro, lam_s, lam_t, lam_eqf, lam_eqg])

# Theories
T_monoid = EqTheory(Σ_monoid, I_monoid);
T_group  = union(T_monoid, Σ_group, I_group);
T_d3h    = union(T_group, Σ_dihedral, I_d3h);
T_reflG  = EqTheory(Σ_reflG, I_reflG);
T_cat    = union(T_reflG, Σ_cat, I_cat);
T_mc     = union(T_cat, Σ_mc, I_mc);
T_smc    = union(T_mc, Σ_smc, I_smc);
T_crc    = union(T_smc, Σ_crc, I_crc);
T_dcr    = union(T_crc, Σ_dcr, I_dcr);
T_cc     = union(T_dcr, Set{Box{Symbol}}(), I_cc)
T_ccc    = union(T_cc, Σ_ccc, I_ccc)