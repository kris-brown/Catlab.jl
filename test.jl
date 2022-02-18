# Single pushout rewriting
using Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: Subobject

(f::CSetTransformation)(X::SubACSet)::SubACSet = Subobject(codom(f); Dict(
    [k=>f.(collect(X.components[k])) for (k,f) in pairs(f.components)])...)
(f::CSetTransformation)(X::StructACSet)::SubACSet = f(¬(⊥(X)))
inv(f::CSetTransformation,Y::SubACSet)::SubACSet = Subobject(dom(f);
  Dict{Symbol, Vector{Int}}(
    [k => vcat([preimage(f,y) for y in collect(Y.components[k])]...)
     for (k,f) in pairs(f.components)])...)
inv(f::CSetTransformation,Y::StructACSet)::SubACSet = inv(f,¬(⊥(Y)))

"""Closes a fragment of a C-set under functionality. Updates a dict of sets"""
function complete!(X::StructACSet{S}, vs::Dict) where {S}
  changed = true
  while changed
    changed = false
    for (k, d, cd) in zip(hom(S), dom(S), codom(S))
      for v in X[collect(vs[d]), k]
        if v ∉ vs[cd]
          push!(vs[cd], v)
          changed=true
        end
      end
    end
  end
end
function Subobj(X::StructACSet{S}; vs...) where {S}
  vs = Dict([k=>Set(get(vs, k, [])) for k in ob(S)])
  complete!(X, vs)
  return Subobject(X; Dict{Symbol,Vector{Int}}([k=>sort(collect(v))
                                                for (k,v) in pairs(vs)])...)
end


"""
f         f
A ↣ B     A ↣ B
    ↓ g   ↓   ↓ g
    C     D ↣ C

Define D to be Im(g) to make it the largest possible subset of C such that we
can get a pullback.
"""
function pullback_complement(f::CSetTransformation, g::CSetTransformation
    )::Pair{CSetTransformation,CSetTransformation}
    A = dom(f)
    d_to_c = hom(¬g(¬f(A)))
    # force square to commute by looking for the index in D making it commute
    ad = Dict([cmp=>Int[findfirst(==(fg_a), collect(d_to_c[cmp]))
                        for fg_a in collect(fg_as)]
               for (cmp, fg_as) in pairs(compose(f,g).components)])
    return CSetTransformation(A, dom(d_to_c); ad...) => d_to_c
end
"""
In the following diagram, a double arrow indicates a monic arrow.

We start with two partial morphisms, construct M by pullback, then N & O by
pullback complement, then finally D by pushout.

            ⭆
A ⇇ K → B         A ⇇ K → B
⇈                 ⇈ ⌟ ⇈ ⌞ ⇈
L                 L ⇇ M → N
↓                 ↓ ⌞ ↓ ⌜ ↓
C                 C ⇇ O → D

We assume the input A→C is total, whereas A→B may be partial, so it is given
as a monic K↣A and K→B.

Specified in Fig 6 of:
"Graph rewriting in some categories of partial morphisms"
"""
function single_pushout_rewrite_data(
    ka::CSetTransformation, kb::CSetTransformation, ac::CSetTransformation
    )::Vector{CSetTransformation}
  e = "SPO rule is not a partial morphism. Left leg not monic."
  is_injective(ka) || error(e)
  lc, la = ac, id(dom(ac))
  ml, mk = pullback(la, ka)
  mn, nb = pullback_complement(mk, kb)
  mo, oc = pullback_complement(ml, lc)
  od, nd = pushout(mo, mn)
  return [ml, mk, mn, mo, nb, oc, nd, od]
end


function single_pushout_rewrite(
    ka::CSetTransformation, kb::CSetTransformation, ac::CSetTransformation
    )::StructCSet
  codom(last(single_pushout_rewrite_data(ka,kb,ac)))
end

using Catlab.Graphs
using Test

G3, G5, G4 = Graph.([3,5,4])
G35 = CSetTransformation(G3,G5;V=[1,2,3])
G54 = CSetTransformation(G5,G4;V=[1,1,2,3,4])
ad,dc = pullback_complement(G35,G54)


A = path_graph(Graph, 3);
K = path_graph(Graph, 2);
B = path_graph(Graph, 2);
add_edge!(B, 2, 2);
C = path_graph(Graph, 4);
add_edge!(C, 1, 3);
ka = path_graph(Graph, 2);
ka, kb = [CSetTransformation(K, x, V=[1,2], E=[1]) for x in [A,B]];
ac = CSetTransformation(A, C, V=[1,2,3], E=[1,2]);


# od, nd = pushout(mo, mn)
spr = single_pushout_rewrite(ka,kb,ac)
@test is_isomorphic(spr, @acset Graph begin V=3;E=2;src=[1,2];tgt=[2,2] end)


