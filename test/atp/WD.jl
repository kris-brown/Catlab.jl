include("/Users/ksb/Catlab.jl/src/atp/ATP.jl")
using Catlab.WiringDiagrams
using Catlab.Theories
using Catlab.Programs


tf = [true, false]
# Single sorted inputs/outputs
Zero, One, Two, Three, Four, Five, Six = [repeat([:X], i) for i in 0:6]

# Boxes
mmul = Box(:mul, Two,     One);
e    = Box(:e,   Zero,    One);
inv  = Box(:inv, One,     One);
gens = Box(:s_,   Zero,    One);
genr = Box(:r_,   Zero,    One);
R    = Box(:R,   One,     One);
f    = Box(:f,   One,     One);
g    = Box(:g,   One,     One);
s    = Box(:s,   [:A],    [:O]);
t    = Box(:t,   [:A],    [:O]);
Id   = Box(:Id,  [:O],    [:A]);
cmp  = Box(:cmp, [:A,:A], [:A]);

o_o  = Box(:o_o, [:O,:O], [:O]); # ⊗ₒ
o_a  = Box(:o_a, [:A,:A], [:A]); # ⊗ₐ

ounit= Box(:⊤,    Symbol[], [:O])
σ    = Box(:σ,    [:O, :O], [:A])
del  = Box(:δ,    [:O],     [:A])
eps  = Box(:ϵ,    [:O],     [:A])
mu   = Box(:μ,    [:O],     [:A])
ev   = Box(:ev,   [:O, :O], [:A])
Exp   = Box(:exp, [:O, :O], [:O])

lam   = Box(:lam, [:O, :O, :O, :A], [:A])

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


@present C(FreeBiproductCategory) begin
  X::Ob
  A::Ob
  O::Ob
  mul::Hom(otimes(X, X), X)
  e::Hom(munit(), X)
  inv::Hom(X,X)
  s_::Hom(munit(), X)
  r_::Hom(munit(), X)
  R::Hom(X, X)
  f::Hom(X,X)
  g::Hom(X,X)
  s::Hom(A,O)
  t::Hom(A,O)
  Id::Hom(O,A)
  cmp::Hom(otimes(A, A),A)
  o_o::Hom(otimes(O, O), O)
  o_a::Hom(otimes(A, A), A)

  ⊤::Hom(munit(), O)
  σ::Hom(otimes(O,O), A)
  δ::Hom(O,A)
  ϵ::Hom(O,A)
  μ::Hom(O,A)
  ev::Hom(otimes(O,O), A)
  exp::Hom(otimes(O,O), O)
  lam::Hom(otimes(O, O, O, A), A)
end

X, O, A = (generator(C, name) for name in [:X,:O,:A])
mul_,e_,lam_ = (generator(C, name) for name in [:mul, :e, :lam])

passx = @program C (x::X) -> x
passo = @program C (x::O) -> x
passa = @program C (x::A) -> x

ll = @program C (x::X) -> mul(e(), x)
leftid = Eq(:leftid, ll, passx);

rr = @program C (x::X) -> mul(x, e())
rightid = Eq(:rightid, rr, passx);

ma1 = @program C (x::X,y::X,z::X) -> mul(x, mul(y, z))
ma2 = @program C (x::X,y::X,z::X) -> mul(mul(x, y), z)
mul_assoc = Eq(:mul_assoc, ma1, ma2);

ma1 = @program C (x::A,y::A,z::A) -> cmp(x, cmp(y, z))
ma2 = @program C (x::A,y::A,z::A) -> cmp(cmp(x, y), z)
cmp_assoc = Eq(:cmp_assoc, ma1, ma2);

ma1 = @program C (x::O,y::O,z::O) -> o_o(x, o_o(y, z))
ma2 = @program C (x::O,y::O,z::O) -> o_o(o_o(x, y), z)
o_o_assoc = Eq(:o_o_assoc, ma1, ma2);

ma1 = @program C (x::A,y::A,z::A) -> o_a(x, o_a(y, z))
ma2 = @program C (x::A,y::A,z::A) -> o_a(o_a(x, y), z)
o_a_assoc = Eq(:o_a_assoc, ma1, ma2);

idxxid = @program C (x::X) mul(mul(e(), x), mul(x, e()))
xx = @program C (x::X) mul(x, x)

rightinv_1 = @program C (x::X) mul(x, inv(x))

e11 =  @program C (_::X) e()

# uniq_inv_1 = @program C (a::X,b::X,c::X) begin
#     [mul(a, b),mul(b, c),e()]
#     return a
# end

# uniq_inv_2 = @program C (a::X,b::X,c::X) begin
#  [a,c]
# end

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

div_1 =  @program C (a::X,b::X,c::X) [mul(a,b),c]
div_2 =  @program C (a::X,b::X,c::X) [mul(inv(a),c),b]

leftcancel_1 = @program C (a::X,b::X,c::X) [mul(a, b), mul(a, c)]
leftcancel_2 = @program C (a::X,b::X,c::X) [b, c]

ss = @program C () let x=s_(); mul(x,x) end

rrr = @program C () let x=r_(); mul(x,mul(x,x)) end

e_wd = @program C () e()

srs = @program C () let x=r_(), y=s_(); mul(mul(y, x), inv(y)) end

rinv = @program C () inv(r_())

sr2 =  @program C () let x=mul(s_(), r_()); mul(x,x) end


R_copy = @program C (i::X) let x=R(i); (x,x) end

fig26 =  @program C (i::X) let x=g(f(i)); (x,x) end

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


refl_s = @program C (a::O) s(Id(a))
refl_t = @program C (a::O) t(Id(a))
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


id_s =  @program C (a::A) cmp(Id(s(a)),a)
id_t =  @program C (a::A) cmp(a,Id(t(a)))


o_func_sl = @program C (a::A, b::A) s(o_a(a,b))
o_func_sr = @program C (a::A, b::A) o_o(t(a),t(b))
o_func_tl = @program C (a::A, b::A) t(o_a(a,b))
o_func_tr = @program C (a::A, b::A) o_o(t(a),t(b))

o_f_c_1 =  @program C (a::A,b::A,c::A,d::A) cmp(o_a(a,b),o_a(c,d))
o_f_c_2 =  @program C (a::A,b::A,c::A,d::A) o_a(cmp(a,c),cmp(b,d))

lunit_o_a_ = @program C (a::A) o_a(Id(⊤()), a)
runit_o_a_ = @program C (a::A) o_a(a, Id(⊤()))
lunit_o_o_ = @program C (a::O) o_o(⊤(), a)
runit_o_o_ = @program C (a::O) o_o(a, ⊤())

bb_1 = @program C (a::O,b::O) cmp(σ(a,b),σ(b,a))
bb_2 = @program C (a::O,b::O) Id(o_o(a,b))



braid_tl = @program C (a::O,b::O) t(σ(a,b))
braid_tr = @program C (a::O,b::O) o_o(b,a)
braid_sl = @program C (a::O,b::O) s(σ(a,b))
braid_sr = @program C (a::O,b::O) o_o(a,b)
braid_ots_t = @program C (a::A,b::A) cmp(o_a(a,b), σ(t(a),t(b)))
braid_ots_s = @program C (a::A,b::A) cmp(σ(s(a),s(b)),o_a(b,a))


eps_s_l = @program C (a::O) s(ϵ(a))
del_s_l =@program C (a::O) s(δ(a))

e_t = @program C (a::O) t(ϵ(a))
d_t = @program C (a::O) t(δ(a))
del_t_2 = @program C (a::O) o_o(a,a)
eps_t_2 = @program C (_::O) ⊤()

eps_coh_1 = @program C (a::O,b::O) ϵ(o_o(a,b))


eps_coh_2 = @program C (a::O,b::O) o_a(ϵ(a),ϵ(b))

del_coh_1 = @program C (a::O,b::O) δ(o_o(a,b))
del_coh_2 = @program C (a::O,b::O) [o_a(δ(a),δ(b)),o_a(o_a(Id(a),σ(a,b)),Id(b))]

del_nat_1 = @program C (a::O) cmp(δ(a),σ(a,a))

del_nat_2 =@program C (a::O) δ(a)

cc1_tt = @program C (a::O) let x=δ(a); cmp(x,o_a(x,Id(a))) end
cc1_ft = @program C (a::O) let x=δ(a); cmp(x,o_a(Id(a),x)) end
cc1_tf = @program C (a::O) cmp(δ(a),o_a(ϵ(a),Id(a)))
cc1_ff = @program C (a::O) cmp(δ(a),o_a(Id(a),ϵ(a)))

cc3_1 = @program C (a::A) cmp(δ(s(a)), o_a(a,a))
cc3_2 = @program C (a::A) cmp(a, δ(t(a)))

delmu_t = @program C (a::O) cmp(δ(a), μ(a))
delmu_f = @program C (a::O) cmp(μ(a), δ(a))

idbox = @program C (a::O) Id(a)


frobll = @program C (a::O) let x=Id(a); cmp(o_a(x,δ(a)),o_a(μ(a),x)) end
frobr = @program C (a::O) cmp(μ(a),δ(a))
frobrl = @program C (a::O) let x=Id(a); cmp(o_a(δ(a),x),o_a(x,μ(a))) end

epsnat1 = @program C (a::A) cmp(a,ϵ(t(a)))

epsnat2 = @program C (a::A) ϵ(s(a))


ev_s = @program C (a::O,b::O) s(ev(a,b))
ev_t = @program C (a::O,b::O) t(ev(a,b))

evs2 = @program C (a::O,b::O) o_o(exp(a,b),a)

evt2 = @program C (_::O,b::O) (b,)

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


lam_s =  @program C (a::O,b::O,c::O,d::A) s(lam(a,b,c,d))
lam_t =  @program C (a::O,b::O,c::O,d::A) t(lam(a,b,c,d))
lam_s2 = @program C (x::O,_::O,_::O,_::A) (x,)

lam_t2 = @program C (_::O,x::O,y::O,_::A) exp(x,y)

lam_eqf1 = @program C (a::O,b::O,c::O,d::A) cmp(o_a(lam(a,b,c,d),Id(b)),ev(b,c))

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

lam_eqg2 = @program C (a::O,b::O,c::O,d::A) lam(a,b,c,cmp(
    o_a(d, Id(b)), ev(b,c)))

# Equations


leftinv    = Eq(:leftinv,    @program(C, (x::X), mul(inv(x), x)),    e11);
rightinv   = Eq(:rightinv,   rightinv_1,   e11);
uniq_inv   = Eq(:uniq_inv,   uniq_inv_1,   uniq_inv_2);
gdiv       = Eq(:gdiv,       div_1,        div_2);
leftcancel = Eq(:leftcancel, leftcancel_1, leftcancel_2);
s_order_2  = Eq(:s_ord_2,    ss,           e_wd);
r_order_3  = Eq(:r_ord_3,    rrr,          e_wd);
refls      = Eq(:refls,      refl_s, passo);
reflt      = Eq(:reflt,      refl_t, passo);
cmp_intro  = Eq(:cmp,        cmp_1,        cmp_2,        false);
l_unit     = Eq(:l_unit, id_s, passa);
r_unit     = Eq(:r_unit, id_t, passa);
o_func_cmp = Eq(:o_func_cmp, o_f_c_1,      o_f_c_2);
lunit_o_a  = Eq(:lunit_o_a,  lunit_o_a_,   passa);
runit_o_a  = Eq(:runit_o_a,  runit_o_a_,   passa);
lunit_o_o  = Eq(:lunit_o_o,  lunit_o_o_,   passo);
runit_o_o  = Eq(:runit_o_o,  runit_o_o_,   passo);
braidbraid = Eq(:braidbraid, bb_1,         bb_2);
braid_t = Eq(:braid_t, braid_tl, braid_tr)
braid_s = Eq(:braid_s, braid_sl, braid_sr)

braid_ots = Eq(:braid_ots, braid_ots_t, braid_ots_s);

eps_s   = Eq(:eps_s, eps_s_l, passo)
del_s   = Eq(:del_s, del_s_l, passo)
eps_t   = Eq(:eps_o,   e_t, eps_t_2);
del_t   = Eq(:del_t,   d_t, del_t_2);
eps_coh = Eq(:eps_coh, eps_coh_1, eps_coh_2);
del_coh = Eq(:del_coh, del_coh_1, del_coh_2);
del_nat = Eq(:del_nat, del_nat_1, del_nat_2);
cc1     = Eq(:cc1, cc1_tt, cc1_ft);
cc2     = Eq(:cc2, cc1_tf, cc1_ff);
cc3     = Eq(:cc3, cc3_1, cc3_2);
bone    = Eq(:bone, delmu_t, idbox)
proj1   = Eq(:mu_s, @program(C,(a::O),s(μ(a))), passo)
proj2   = Eq(:mu_t, @program(C,(a::O),t(μ(a))), passo)
frob1 = Eq(:frob_l, frobll, frobr)
frob2 = Eq(:frob_r, frobrl, frobr)
o_func_s =Eq(:o_func_s,o_func_sl,o_func_sr)
o_func_t =Eq(:o_func_t,o_func_tl,o_func_tr)

eps_nat = Eq(:epsnat, epsnat1, epsnat2)
evs     = Eq(:evs, ev_s, evs2)
evt     = Eq(:evt, ev_t, evt2)
λ_intro = Eq(:λ_intro, lam_intro1,    lam_intro2, false)
lam_s   = Eq(:lam_s,   lam_st(true),  lam_s2)
lam_t   = Eq(:lam_t,   lam_st(false), lam_t2)
lam_eqf = Eq(:lam_eqf, lam_eqf1,      lam_eqf2)
lam_eqg = Eq(:lam_eqg, lam_eqg1,      lam_eqg2)

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
I_dcr    = Set([bone, proj1, proj2, frob1, frob2])
I_cc     = Set([eps_nat])
I_ccc    = Set([evs, evt, λ_intro, lam_s, lam_t, lam_eqf, lam_eqg])

# Theories
T_monoid = EqTheory(Σ_monoid, I_monoid);
T_group  = union(T_monoid, Σ_group,    I_group);
T_d3h    = union(T_group,  Σ_dihedral, I_d3h);

T_reflG  = EqTheory(Σ_reflG, I_reflG);
T_cat    = union(T_reflG, Σ_cat, I_cat);
T_mc     = union(T_cat,   Σ_mc,  I_mc);
T_smc    = union(T_mc,    Σ_smc, I_smc);
T_crc    = union(T_smc,   Σ_crc, I_crc);
T_dcr    = union(T_crc,   Σ_dcr, I_dcr);
T_cc     = union(T_dcr,   Σ0,    I_cc)
T_ccc    = union(T_cc,    Σ_ccc, I_ccc)