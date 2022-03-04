module DPO
export rewrite, rewrite_match, rewrite_match_maps, pushout_complement,
       can_pushout_complement, id_condition, dangling_condition, extend_morphism

using ...Theories
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits
using ..FinSets: id_condition
using ..CSets: dangling_condition

"""    extend_morphism(f::ACSetTransformation,g::ACSetTransformation)::Union{Nothing, ACSetTransformation}
Given a span of morphisms, we seek to find a morphism B→C that makes a
commuting triangle.

   B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
                         monic=false)::Union{Nothing, ACSetTransformation}
  dom(f) == dom(g) || error("NAC morphism doesn't match L")

  init = map(collect(pairs(components(f)))) do (ob, mapping)
    init_comp = Pair{Int,Int}[]
    for i in parts(codom(g), ob)
      vs = Set(mapping(preimage(g[ob], i)))
      if length(vs) == 1
        push!(init_comp, i => only(vs))
      elseif length(vs) > 1 # no homomorphism possible
        return nothing
      end
    end
    ob => Dict(init_comp)
  end
  ini = NamedTuple(Dict(init))
  homomorphism(codom(g), codom(f); initial=ini, monic=monic)
end

"""    rewrite_match_maps(L::ACSetTransformation, R::ACSetTransformation, m::ACSetTransformation)::Tuple{ACSetTransformation,ACSetTransformation,ACSetTransformation,ACSetTransformation}

Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite.
              l   r
           L <- I -> R
         m ↓    ↓    ↓
           G <- K -> H


Optionally specify negative application conditions in the form of a morphism
L→N, where the existence of a monic morphism N↪G is forbidden.

Returns:
- `nothing`, if the negative application condition is triggered. Otherwise:
- the morphisms I->K, K->G (produced by pushout complement), followed by
  R->H, and K->H (produced by pushout)
"""
function rewrite_match_maps(
    L::ACSetTransformation, R::ACSetTransformation, m::ACSetTransformation;
    N::Union{Nothing,ACSetTransformation}=nothing)::Union{Nothing, Tuple{
      ACSetTransformation,ACSetTransformation,
      ACSetTransformation,ACSetTransformation}}
  # Check domains
  dom(L) == dom(R) || error("Rewriting where L, R do not share domain")
  codom(L) == dom(m) || error("Rewriting where L does not compose with m")
  # Check NAC
  if !isnothing(N)
    if !isnothing(extend_morphism(m, N; monic=true))
      return nothing
    end
  end
  # Compute rewrite
  (ik, kg) = pushout_complement(L, m)
  rh, kh = pushout(R, ik)
  return ik, kg, rh, kh
end

"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet
using a match morphism `m` which indicates where to apply
the rewrite. Return the rewritten ACSet.
"""
rewrite_match(L::ACSetTransformation, R::ACSetTransformation,
  m::ACSetTransformation; N::Union{Nothing,ACSetTransformation}=nothing
  )::Union{Nothing,ACSet} =
  let res=rewrite_match_maps(L, R, m; N=N);
      isnothing(res) ? res : codom(res[4]) end


"""
Apply a rewrite rule (given as a span, L<-I->R) to a ACSet,
where a match morphism is found automatically. If multiple
matches are found, a particular one can be selected using
`m_index`.
"""
function rewrite(L::ACSetTransformation, R::ACSetTransformation,
                 G::ACSet; monic::Bool=false, m_index::Int=0,
                 N::Union{Nothing,ACSetTransformation}=nothing
                 )::Union{Nothing,ACSet}
  if m_index == 0 && isnothing(N)
    m = homomorphism(codom(L), G, monic=monic)
  else
    ms = filter(m-> (can_pushout_complement(L, m)
                     && isnothing(complete_morphism(m,N))),
                homomorphisms(codom(L), G, monic=monic))
    m =  (0 < m_index <= length(ms)) ? ms[m_index] : nothing
  end
  if isnothing(m)
    return nothing
  else
    return rewrite_match(L, R, m)
  end
end

end
