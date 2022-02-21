# Single pushout rewriting
using Catlab.CategoricalAlgebra
import Catlab.CategoricalAlgebra: Subobject

inv(f::CSetTransformation,Y::SubACSet)::SubACSet = Subobject(dom(f);
  Dict{Symbol, Vector{Int}}(
    [k => vcat([preimage(f,y) for y in collect(Y.components[k])]...)
     for (k,f) in pairs(f.components)])...)
inv(f::CSetTransformation,Y::StructACSet)::SubACSet = inv(f,top(Y))

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


using Catlab.Graphs
using Test

