using Revise, Test
using Catlab
using Catlab.Graphs
using Catlab.CategoricalAlgebra, Catlab.Present, Catlab.Theories
using Catlab.Graphs.BasicGraphs: TheoryGraph, AbstractGraph
import Catlab.CategoricalAlgebra: colimit
using DataStructures: DefaultDict
getS(::StructACSet{S}) where S = S

@present TheorySetAttr(FreeSchema) begin
  X::Ob
  D::AttrType
  f::Attr(X,D)
end
@acset_type SetAttr(TheorySetAttr)


const Strings = SetAttr{String}
const Vars = SetAttr{Var}

ab = @acset Strings begin X=2; f=["a","b"] end;
c = @acset Strings begin X=1; f=["c"] end;
d = @acset Strings begin X=1; f=["d"] end;
v2 = @acset Vars begin X=2; f=[Var(1), Var(2)] end ;
v1 = @acset Vars begin X=2; f=[Var(3), Var(3)] end ;

cnst = x -> (y -> x)
abc = homomorphism(ab, c; type_components=(D=cnst("c"),))
abd = homomorphism(ab, d; type_components=(D=cnst("d"),))
#
hs = homomorphisms(v1, ab)
@test all(is_natural.(hs))

if false

@present TheoryLabeledGraph <: TheoryGraph begin
  (VLabel, ELabel)::AttrType
  vlabel::Attr(V,VLabel)
  elabel::Attr(E,ELabel)
end
@acset_type LabeledGraph(TheoryLabeledGraph, index=[:src,:tgt]) <: AbstractGraph
const LG = LabeledGraph{Bool, Rational}
const LGvar = LabeledGraph{Bool, Var}
const LGvar = LabeledGraph{Bool, Var}
const LGivar = LabeledGraph{Union{Bool,Var}, Union{Rational,Var}}
const LGx = LabeledGraph{Bool, Expr}







l = @acset LGvar begin V=2; E=2; src=[1,1]; tgt=[2,2];
  vlabel=[false,false];elabel=[Var(:a), Var(:b)] end
i = @acset LGvar begin V=2;vlabel=[false,false] end
r = @acset LGx begin V=2; E=1; src=[1]; tgt=[2];
   vlabel=[false,false];elabel=[:(Var(:a)+Var(:b))] end
L = homomorphism(i,l;monic=true); R = homomorphism(i,r;monic=true)
G = @acset LG begin V=3; E=4; src=[1,1,1,1]; tgt=[2,2,2,3];
vlabel=[false,false,false]; elabel=[2,3,2,2] end

#res = rewrite_var(L, R, G)

# Deleting three self loops in parallel
t = apex(terminal(Graph))
G = t ⊕ t ⊕ t
L = homomorphism(Graph(1), t)
rule = Rule(L,id(Graph(1)))
S = getS(G); monic=true
@test apply_parallel_rule(rule, G) == Graph(3)

# Can only delete one span in parallel
G = @acset Graph begin V=4; E=3; src=[1,1,1]; tgt=[2,3,4] end
l = @acset Graph begin V=3; E=2; src=[1,1]; tgt=[2,3] end
L = homomorphism(Graph(3), l; monic=true); R=id(Graph(3))
expected = @acset Graph begin V=4; E=1; src=[1]; tgt=[4] end
@test is_isomorphic(apply_parallel_rule(Rule(L,R), G), expected)

# Negative application condition.
# Can't delete edges pointing to things with a self loop.
n = @acset Graph begin V=3; E=4; src=[1,1,2,3]; tgt=[2,3,2,3] end
N = homomorphism(l,n; monic=true)
r = Rule(L,R,N)
G = @acset Graph begin V=6; E=6; src=[1,1,1,1,4,5]; tgt=[2,3,4,5,4,5] end
expected = @acset Graph begin V=6; E=4; src=[1,1,4,5]; tgt=[4,5,4,5] end
@test is_isomorphic(apply_parallel_rule(r, G), expected)

# Matching with variable attributes
###################################

# Identify pair of parallel arrows w/ same label by keeping one
l_ = @acset LGvar begin V=2; E=2; src=[1,1]; tgt=[2,2];
  vlabel=[false,false];elabel=[Var(:a), Var(:a)] end
# Replace w/ single arrow w/ same label
r_ = @acset LGvar begin V=2; E=1; src=[1]; tgt=[2];
   vlabel=[false,false];elabel=[Var(:a)] end
L_ = homomorphism(r_,l_); R_ = id(r_)
# Target has two pairs of par arrows, only one of them has matching labels
G = @acset LG begin V=3; E=4; src=[1,1,1,1]; tgt=[2,2,2,3];
                      vlabel=[false,false,false]; elabel=[2,3,2,2] end
rule = Rule(L_, R_)
monic=true;
S = getS(G)
res = apply_parallel_rule(rule, G)
@test is_isomorphic(res, @acset LG begin V=3; E=3; src=[1,1,1]; tgt=[2,2,3];
  vlabel=[false,false,false]; elabel=[2,3,2] end)

# Identify pair of parallel arrows w/ same label by deleting both, creating new
l_ = @acset LGvar begin V=2; E=2; src=[1,1]; tgt=[2,2];
  vlabel=[false,false];elabel=[Var(:a), Var(:a)] end
i_ = @acset LGvar begin V=2; vlabel=[false,false] end
r_ = @acset LGvar begin V=2; E=1; src=[1]; tgt=[2];
   vlabel=[false,false];elabel=[Var(:a)] end
L_ = homomorphism(i_,l_; monic=true); R_ = homomorphism(i_, r_; monic=true)
G_ = @acset LG begin V=3; E=4; src=[1,1,1,1]; tgt=[2,2,2,3];
                      vlabel=[false,false,false]; elabel=[2,3,2,2] end
rule = Rule(L_, R_)
res = apply_parallel_rule(rule, G_)





##########################################################################
@present TheoryBWGraph <: TheoryGraph begin
  (BoolType, ELabel)::AttrType
  B::Ob
  blabel::Attr(B, BoolType)
  bw::Hom(B,V)
  elabel::Attr(E,ELabel)
end
@acset_type BWGraph(TheoryBWGraph, index=[:src,:tgt, :bw, :blabel]) <: AbstractGraph
const BW = BWGraph{Bool, Rational}
const BWvar = BWGraph{Union{Bool,Var, Expr}, Union{Rational, Var, Expr}}
ab = [Var(:a), Var(:b)]
aa, cc = [Var(:a), Var(:a)], [Var(:c), Var(:c)]
ff, tt = [false, false], [true, true]
ft = [false, true]
rules = Rule[]

# i: Sum parallel black to white nodes
#------------------------------------
bw_ab = @acset BWvar begin
  V=2; E=2; B=2; src=[1,1]; tgt=[2,2]; bw=[1,2]; blabel=ft; elabel=ab end
bw = @acset BW begin V=2; B=2; bw=[1,2]; blabel=ft end
bw_sum = @acset BWvar begin V=2; E=1; B=2; src=[1]; tgt=[2]; bw=[1,2];
                            blabel=ft; elabel=[:(Var(:a)+Var(:b))] end

push!(rules, Rule(homomorphism(bw,bw_ab), homomorphism(bw, bw_sum)))

# Test 1
G = @acset BW begin V=2; B=2; E=3; src=[1,1,1]; tgt=[2,2,2]; bw=[1,2];
                    blabel=ft; elabel=[3,3,4] end
@test normalize(rules, G) == @acset BW begin
   V=2; B=2; E=1; src=[1]; tgt=[2]; bw=[1,2]; blabel=ft; elabel=[10] end

# ii: White to black is replaced with neg reciprocal black to white
#------------------------------------------------------------------
wba = @acset BWvar begin V=2; B=2; E=1; src=[2]; tgt=[1]; bw=[1,2]; blabel=ft;
                         elabel=[Var(:a)] end
bw_neg_a = @acset BWvar begin V=2; B=2; E=1; src=[1]; tgt=[2]; bw=[1,2];
                              blabel=ft;elabel=[:(-1/Var(:a))] end
wba0 = @acset BWvar begin V=2; B=2; E=2; src=[2,2]; tgt=[1,1]; bw=[1,2];
                          blabel=ft;elabel=[Var(:a), 0//1] end
push!(rules, Rule(homomorphism(bw,wba),
                  homomorphism(bw, bw_neg_a),
                  homomorphism(wba, wba0)))

# test 1: basic
G = @acset BW begin V=2; B=2; E=1; src=[2]; tgt=[1]; bw=[1,2]; blabel=ft;
                    elabel=[2] end
@test is_isomorphic(normalize(rules, G), @acset BW begin
  V=2; E=1; B=2; src=[1]; tgt=[2]; bw=[1,2]; blabel=ft; elabel=[-1//2] end)
# test 2:  no op when edge is 0
G = @acset BW begin V=2; B=2; E=1; src=[1]; tgt=[2]; bw=[1,2]; blabel=ft;
                    elabel=[0] end
@test normalize(rules, G) == G
# test 3: combine with earlier rules
G = @acset BW begin V=2; B=2; E=2;
  src=[1,2]; tgt=[2,1]; bw=[1,2]; blabel=ft; elabel=[2,2] end
X = @acset BW begin V=2; B=2; E=1;
  src=[1]; tgt=[2]; bw=[1,2]; blabel=ft; elabel=[3//2] end
@test is_isomorphic(normalize(rules, G), X)

# iii && iv: Zero edges between *different* color nodes deleted
#------------------------------------------------------------

vv0 =  @acset BWvar begin V=2; E=1; src=[1]; tgt=[2]; elabel=[0//1] end
vv = @acset BW begin V=2 end
vv0same = @acset BWvar begin V=2; B=2; E=1; src=[1]; tgt=[2]; bw=[1,2];
                             blabel = aa; elabel=[0//1] end
push!(rules, Rule(homomorphism(vv, vv0;monic=true),
                  id(vv),
                  homomorphism(vv0, vv0same)))

# test 1: combine with earlier rules
G = @acset BW begin V=2; B=2; E=4;
  src=[1,2,1,2]; tgt=[2,1,2,1]; bw=[1,2]; blabel=ft; elabel=[2,2,0,0]
end
@test is_isomorphic(normalize(rules, G), X)

# vii && viii: Self loop of 1 erased
#--------------------------------------
c_ = @acset BWvar begin V=1; B=1; bw=[1]; blabel=[Var(:c)] end
c_1 = @acset BWvar begin
    V=1; B=1; E=1; src=[1]; tgt=[1]; bw=[1]; blabel=[Var(:c)]; elabel=[1//1] end
push!(rules, Rule(homomorphism(c_, c_1), id(c_)))

# Test 1: combine with other rules

G = @acset BW begin
  V=2; B=2; E=6; src=[1,2,1,2,1,2]; tgt=[2,1,2,1,1,2]; bw=[1,2];
  blabel=ft; elabel=[2,2,0,0,1,1] end
@test is_isomorphic(normalize(rules, G), X)

# v && vi: non-1 self edge means flip color
#------------------------------------------
ba = @acset BWvar begin
  V=1; B=1; E=1; src=[1]; tgt=[1]; bw=[1]; blabel=[false]; elabel=[Var(:a)] end
wa = @acset BWvar begin
    V=1; B=1; E=1; src=[1]; tgt=[1]; bw=[1]; blabel=[true]; elabel=[Var(:a)] end

ba1 = @acset BWvar begin V=1; B=1; E=2;
  src=[1,1]; tgt=[1,1]; bw=[1]; blabel=[false]; elabel=[Var(:a), 1//1] end
wa1 = @acset BWvar begin V=1; B=1; E=2; src=[1];
  tgt=[1,1]; bw=[1,1]; blabel=[true]; elabel=[Var(:a), 1//1] end
v = @acset BW begin V=1 end
b =  @acset BW begin V=1; B=1; bw=[1]; blabel=[false] end
w =  @acset BW begin V=1; B=1; bw=[1]; blabel=[true] end

append!(rules,
      [Rule(homomorphism(v, ba),
           homomorphism(v,w),
           homomorphism(ba, ba1)),
       Rule(homomorphism(v, wa),
           homomorphism(v,b),
           homomorphism(wa, wa1))])

# Test 1: alone
G = @acset BW begin V=2; B=2; E=2; src=[1,2]; tgt=[1,2]; bw=[1,2];
                    blabel=ft; elabel=[2,3] end

@test normalize(rules[end-1:end], G) == bw
# Test 2: combine with other rules

# switch the order of white black, but add non-1 self edges to both
G = @acset BW begin
  V=2; B=2; E=8; src=[1,2,1,2,1,2,1,2]; tgt=[2,1,2,1,1,2,1,2]; bw=[2,1];
  blabel=ft; elabel=[2,2,0,0,1,1,3,4] end
@test is_isomorphic(normalize(rules, G), X)


# ix and x: Merge nodes (of same color that are connected by 1)
#----------------------------------------------------------------
cc_ = @acset BWvar begin V=2; B=2; bw=[1,2]; blabel=cc end
cc1 = @acset BWvar begin V=2; B=2; E=1; src=[1]; tgt=[2];
                         bw=[1,2]; blabel=cc; elabel=[1//1] end
push!(rules, Rule(homomorphism(cc_, cc1; monic=true), homomorphism(cc_, c_)))

# Test 1: alone
G = @acset BW begin V=4; B=4; E=3; src=[1,2,3]; tgt=[2,3,4]; bw=[1,2,3,4];
                    blabel=[false,false,false,false]; elabel=[1,1,1] end

@test normalize([rules[end]], G) == b

# test 2: together
G = @acset BW begin
  V=4; B=4; E=10; src=[1,2,1,2,1,2,1,2,1,2]; tgt=[2,1,2,1,1,2,1,2,3,4]; bw=[2,1,3,4];
  blabel=vcat(ft,ft); elabel=[2,2,0,0,1,1,3,4,1,1] end
@test is_isomorphic(normalize(rules, G), X)


# xiii && xiv: parallel edges of same value replaced with single edge
#-------------------------------------------------------------------
cc_aa = @acset BWvar begin  V=2; B=2; E=2;
  src=[1,1]; tgt=[2,2]; bw=[1,2]; blabel=cc; elabel=aa end

cc_a = @acset BWvar begin
      V=2; B=2; E=1; src=[1]; tgt=[2]; bw=[1,2]; blabel=cc; elabel=[Var(:a)] end

push!(rules, Rule(homomorphism(cc_, cc_aa; monic=true),
                  homomorphism(cc_, cc_a; monic=true)))

# test 1: isolation
G = @acset BW begin V=3; B=3; E=6; src=[1,1,1,2,2,2]; tgt=[2,2,2,3,3,3]
  bw=[1,2,3]; blabel=false; elabel=[4,4,4,5,5,5] end

@test is_isomorphic(normalize([rules[end]], G), @acset BW begin V=3;B=3;E=2;
  src=[1,2]; tgt=[2,3]; bw=[1,2,3]; blabel=false; elabel=[4,5] end)

# xi xii: zero edge b->b or w->w is replaced with (b w)
#-----------------------------------------------------
cc0 = @acset BWvar begin V=2; B=2; E=1; src=[1]; tgt=[2];
                          bw=[1,2]; blabel=cc; elabel=[0//1] end

push!(rules, Rule(homomorphism(vv, cc0; monic=true),
                  ACSetTransformation(vv, bw; V=[1,2])))
# test 1: isolation
G= @acset BW begin V=4; E=4; B=4; src=[1,1,2,3]; tgt=[2,4,3,4]; bw=[1,2,3,4];
  blabel=[false,true,true,false]; elabel=[1,0,0,2] end

@test is_isomorphic(normalize([rules[end]], G), @acset BW begin V=4; E=2; B=4;
  bw=[1,2,3,4]; blabel=vcat(ff,tt); src=[1,4]; tgt=[2,3];
  elabel=[1,2] end)

# xv && xvi: parallel edges with diff values get edges removed and color swap
#-------------------------------------------------------------------
bb_ab = @acset BWvar begin V=2; B=2; E=2; src=[1,1]; tgt=[2,2]; bw=[1,2];
    blabel=ff; elabel=ab end
ww_ab = @acset BWvar begin V=2; B=2; E=2; src=[1,1]; tgt=[2,2]; bw=[1,2];
    blabel=tt; elabel=ab end
bb = @acset BWvar begin V=2; B=2;  bw=[1,2]; blabel=ff end
ww = @acset BWvar begin V=2; B=2;  bw=[1,2]; blabel=tt end
bb_abcc = @acset BWvar begin V=2; B=2; E=4; src=[1,1,1,1]; tgt=[2,2,2,2];
  bw=[1,2]; blabel=ff;  elabel=vcat(ab,cc) end
# We are in a tricky position here. We need the match from the NAC to be monic
# only on certain components. Requires big change in CSets.jl.
# append!(rules, [Rule(homomorphism(vv, bb_ab; monic=true),
#                      homomorphism(vv, ww; monic=true),
#                      homomorphism(bb_ab, bb_abcc; monic=true))
#                 ])

# xvii: get rid of 'useless' nodes
#----------------------------------

bwb_cospan = @acset BWvar begin V=3; E=2; B=3; bw=[1,2,3]; src=[1,2]; tgt=[3,3]
                                blabel=[false,false,true]; elabel=ab end
#
bb_a_over_b = @acset BWvar begin V=2; B=2; E=1; bw=[1,2]; blabel=ff; src=1;tgt=2
                                 elabel=[:(-Var(:a)/Var(:b))] end
wbw_span = @acset BWvar begin V=3; E=2; B=3; bw=[1,2,3]; src=[3,3]; tgt=[1,2]
  blabel=[true,true,false]; elabel=ab end
#
ww_b_over_a = @acset BWvar begin V=2; B=2; E=1; bw=[1,2]; blabel=tt; src=1;tgt=2
  elabel=[:(-Var(:b)/Var(:a))] end
#


push!(rules, )

#

#