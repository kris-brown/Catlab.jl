module DPO
export rewrite, rewrite_match, pushout_complement, can_pushout_complement,
  id_condition, dangling_condition, sesqui_pushout_rewrite_data,
  sesqui_pushout_rewrite, final_pullback_complement,
  partial_map_classifier_universal_property, partial_map_classifier_eta,
  partial_map_functor_hom, partial_map_functor_ob, topo_obs,
  single_pushout_rewrite_data, single_pushout_rewrite, open_rewrite,
  open_rewrite_match, pullback_complement, extend_morphism, Rule,
  apply_parallel_rule, normalize, copairs, invert, quotient_acset,
  quotient_domain, quotient_codomain

using ...Theories
using ...Theories: attr, adom
using ..FinSets, ..CSets, ..FreeDiagrams, ..Limits, ..StructuredCospans
using ..FinSets: id_condition
using ..CSets: dangling_condition, SchemaDescType, ¬, ⊤
using DataStructures
using ...Graphs
using ...Present

# Double-pushout rewriting
##########################

struct Rule
  L::ACSetTransformation
  R::ACSetTransformation
  N::Union{Nothing, ACSetTransformation}
  monic::Bool
  function Rule(L::ACSetTransformation, R::ACSetTransformation,
                N::Union{Nothing, ACSetTransformation}=nothing,
                monic::Bool=false)
    #dom(L) == dom(R) || error("L<->R not a span") # type issues...
    # isnothing(N) || dom(N) == codom(L) || error("NAC does not compose with L")
    new(L, R, N, monic)
  end
end

"""Taken from the pure chase PR that has not yet been merged"""
function copairs(xs::Vector{T}, shared_tgt::Bool
                )::ACSetTransformation where T<:ACSetTransformation
  comps = Dict([k=>Int[] for k in keys(xs[1].components)])
  new_d = Base.invokelatest(typeof(dom(xs[1])))
  new_cd = shared_tgt ? codom(xs[1]) : Base.invokelatest(typeof(codom(xs[1])))
  for x in xs
    copy_parts!(new_d,dom(x))
    if shared_tgt
      for k in keys(x.components)
        append!(comps[k], collect(x[k]))
      end
    else
      for (k,v) in pairs(copy_parts!(new_cd,codom(x)))
        append!(comps[k], [v.start + vv - 1 for vv in collect(x[k])])
      end
    end
  end
  return ACSetTransformation(new_d, new_cd; comps...)
end

function quotient_acset(X::StructACSet{S}, d) where {S}
  new_X = typeof(X)()
  map(collect(d)) do (c, dup)
    add_parts!(new_X, c, nparts(X, c) - length(dup))
  end
  map(zip(hom(S), dom(S), codom(S))) do (f, s, t)
    cmp = [get(d[t], v, v) for (i, v) in enumerate(X[f]) if !haskey(d[s], i)]
    set_subpart!(new_X, f, cmp)
  end

  map(zip(attr(S), adom(S))) do (f, s)
    cmp = [v for (i, v) in enumerate(X[f]) if !haskey(d[s], i)]
    set_subpart!(new_X, f, cmp)
  end

  new_X
end
function quotient_codomain(f::ACSetTransformation, d)
  t = quotient_acset(codom(f), d)
  comps = Dict(map(collect(pairs(components(f)))) do (c, fun)
    c=>[get(d[c],v,v) for (i, v) in enumerate(collect(fun))]
  end)

  return ACSetTransformation(dom(f), t; comps...)

end
function quotient_domain(f::ACSetTransformation, d)
  s = quotient_acset(dom(f), d)
  comps = Dict(map(collect(pairs(components(f)))) do (c, fun)
    c=>[v for (i, v) in enumerate(collect(fun)) if !haskey(d[c], i)]
  end)
  return ACSetTransformation(s, codom(f); comps...)
end

function apply_parallel_rule(rule::Rule, G::StructACSet{S}; monic::Bool=false
                            )::Union{StructACSet, Nothing} where S
  ms, seen  = ACSetTransformation[], [Set{Int}() for _ in ob(S)]
  vars = DefaultDict{Symbol,Dict}(()->Dict())
  LRN = [rule.L, rule.R, rule.N]
  # Get all valid matches, greedily keep the ones that can be done in parallel
  for m in homomorphisms(codom(rule.L), G; monic=monic||rule.monic)
    new_vars = get_vars(codom(rule.L), dom(m))
    bs = map(collect(new_vars)) do (k, nvs)
      all([(get(vars[k], nk, nv) == nv) for (nk, nv) in collect(nvs)])
    end
    if all(bs)
      [merge!(vars[k], nvs) for (k, nvs) in collect(new_vars)]
    else
      #println("Inconsistent new vars $vars \n$new_vars")
      continue
    end

    L = sub_vars(LRN[1], G, vars)#isempty(vars) ? LRN : [isnothing(x) ? x : sub_vars(x, G, vars) for x in LRN]
    # println("codom L $(codom(L))\ndom(m) $(dom(m))")
    if can_pushout_complement(L, m)
      nac = isnothing(LRN[3]) ? nothing : extend_morphism(
        m, sub_vars(LRN[3], nothing, vars))
      if isnothing(nac)
        new_dels = map(zip(components(L), components(m))) do (l_comp, m_comp)
          image = Set(collect(l_comp))
          (Set([ m_comp(x) for x in codom(l_comp) if x ∉ image ])
            => Set(m_comp(collect(image))))
        end
        if all(isempty.([x∩new_keep for (x,(_, new_keep)) in zip(seen, new_dels)]))
        [union!(x, union(new_del, new_keep) ) for (x,(new_del, new_keep))
         in zip(seen, new_dels)]
          push!(ms, m)
        end
      end
    end
  end

  n = length(ms)
  if n == 0 return nothing end
  L, R = isempty(vars) ? LRN : [sub_vars(x, G, vars) for x in LRN[1:2]]
  is_natural(L) || error("L $L")
  is_natural(R) || error("R $R")

  # Create parallel rule
  m_paired = copairs(ms, true)
  l_paired = copairs([L for _ in 1:n], false)
  r_paired = copairs([R for _ in 1:n], false)
  can_pushout_complement(l_paired,m_paired) || error("PO n $n del $del \nms $ms \nm_paired $m_paired")
  rewrite_match(l_paired,r_paired,m_paired)
end

"""Applies rules until they cannot be applied anymore"""
normalize(rs::Vector{Rule}, G::StructACSet) = normalize([
  Symbol(string(i))=>r for (i, r) in enumerate(rs)], G)

function normalize(rs::Vector{Pair{Symbol,Rule}}, G::StructACSet)
  while true
    updated=false
    for (n, r) in rs
      #println("Applying rule $n")
      res = apply_parallel_rule(r, G; monic=true)
      if !isnothing(res)
        #println("res $res")
        G = res
        updated |= true
      end
    end
    if !updated
      return G
    end
  end
end

"""    extend_morphism(f::ACSetTransformation,g::ACSetTransformation)::Union{Nothing, ACSetTransformation}
Given a span of morphisms, we seek to find a morphism B→C that makes a
commuting triangle if possible.

    B
 g ↗ ↘ ?
 A ⟶ C
   f
"""
function extend_morphism(f::ACSetTransformation, g::ACSetTransformation;
                         monic=false)::Union{Nothing, ACSetTransformation}
  jf, jg = generate_json_acset.([dom(f), dom(g)])
  jf == jg || error("f and g are not a span: $jf \n$jg")

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

# Sesqui-pushout rewriting
##########################

"""
The specification for the following functions comes from:
  - 'Concurrency Theorems for Non-linear Rewriting Theories'
     - for final pullback complement and sesqui-pushout rewriting
  - 'AGREE - Algebraic Graph Rewriting with Controlled Embedding'
     - for partial map classifier (a functor T and natural transformation η)

 Cockett and Lack 2003 discuss partial map classifiers of copresheaves, so there may be something interesting there.
"""

"""Get topological sort of objects of a schema. Fail if cyclic"""
function topo_obs(S::Type)::Vector{Symbol}

  G = Graph(length(ob(S)))
  for (s, t) in zip(S.parameters[5], S.parameters[6])
    add_edge!(G, s, t)
  end
  return [ob(S)[i] for i in reverse(topological_sort(G))]
end

function check_eqs(x::StructACSet, pres::Presentation, o::Symbol, i::Int)::Bool
  for (p1,p2) in filter(e->only(e[1].type_args[1].args) == o, pres.equations)
    eval_path(x, p1, i) == eval_path(x,p2, i) || return false
  end
  return true
end

function eval_path(x::StructACSet, h, i::Int)::Int
  val = i
  for e in h.args
    val = x[val, e]
  end
  return val
end
"""
A functor T, playing the role of Maybe in Set, but generalized to C-Sets.

When called on the terminal object, this produces the subobject classifier:
See Mulry "Partial map classifiers and cartesian closed categories" (1994)

This function specifies what T does on objects. The key properties:
  1. for all X ∈ Ob(C), η(X):X⟶T(X) is monic.
                     m   f                                    ϕ(m,f)
  2. for each span A ↩ X → B, there exists a unique morphism A ⟶ T(B)
     such that (m,f) is the pullback of ϕ(m,f),η(B))

Not only do we add an extra element to each component of the C-Set, but we need
to consider the possibility that a component (with n outgoing morphisms) has any
combination of the targets of those morphisms deleted (like the subobject
classifier, there are different *ways* for something to be deleted).

For example, in Graph, an edge can be deleted that goes between any two vertices
of the graph. We can't map all deleted edges to the same point in T(E) (if we're
going to satisfy that desired property #2), so we need an extra edge in T(E) for
every possibility (from V1 to V2, from V1 to V3, ..., from [Deleted] to V1, ...,
from V2 to [Deleted], ... from [Deleted] to [Deleted]), where [Deleted] is our
name for the extra element added to T(V).

                    [src]     [tgt]
Thus, T(E) ≅ |E| + (|V|+1) × (|V|+1).

In general, T(X) ≅ |X| + ∏ₕ(|T(codom(h))|) for each outgoing morphism h::X⟶Y
- the |X| corresponds to the 'real' elements of X
- the second term corresponds to the possible ways an X can be deleted.
- This recursive formula means we require the schema of the C-set to be acyclic
  otherwise the size is infinite (assumes schema is free).
"""
function partial_map_functor_ob(x::StructCSet{S};
    pres::Union{Nothing, Presentation}=nothing
    )::Pair{StructCSet, Dict{Symbol,Dict{Vector{Int},Int}}} where {S}
  res = deepcopy(x)
  d = DefaultDict{Symbol,Dict{Vector{Int},Int}}(()->Dict{Vector{Int},Int}())
  hdata = collect(zip(hom(S), dom(S), codom(S)))
  extra_data = Dict{Symbol, Vector{Dict{Symbol, Int}}}()
  for o in topo_obs(S)
    extra_data[o] = Dict{Symbol, Int}[]
    homs_cds = [(h,cd) for (h,d,cd) in hdata if d==o] # outgoing morphism data
    if isempty(homs_cds)
      d[o][Int[]] = add_part!(res, o)
    else
      homs, cds = collect.(zip(homs_cds...))
      for c in Iterators.product([1:nparts(res,cd) for cd in cds]...)
        d[o][collect(c)] = v = add_part!(res, o; Dict(zip(homs,c))...)
        if !isnothing(pres) && !check_eqs(res, pres, o, v)
          delete!(d[o], collect(c))
          rem_part!(res, o, v)
        end
      end
    end
  end
  return res => d
end

"""
Because the functorial embedding of objects keeps a copy of the original data,
what to do with morphisms is just carry them along. Because our implementation
adds all of the additional stuff afterwards, index-wise, we can use literally
the same data for a morphism lifted from X⟶Y to T(X)⟶T(Y).

However, we still need to map the extra stuff in T(X) to the proper extra stuff
in T(Y).
"""
function partial_map_functor_hom(f::CSetTransformation{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where S
  X, Y = dom(f), codom(f)
  (d, _), (cd, cddict) = [partial_map_functor_ob(x; pres=pres) for x in [X,Y]]
  comps, mapping = Dict{Symbol,Vector{Int}}(), Dict()
  hdata = collect(zip(hom(S),dom(S),codom(S)))

  for (k,v) in pairs(f.components)
    mapping[k] = vcat(collect(v), [nparts(Y, k)+1]) # map extra val to extra
  end

  for o in topo_obs(S)
    comps[o] = map(parts(d, o)) do i
      if i <= nparts(X,o) # use f for elements that are defined
        return f[o](i)
      else  # find which extra elem ∈ T(Y) it maps to (by its outgoing maps)
        outdata = Int[comps[cd][d[i, h]]
                      for (h,c_,cd) in hdata if c_==o]
        return cddict[o][outdata]
      end
    end
  end
  return CSetTransformation(d,cd;comps...)
end

"""
The natural injection from X ⟶ T(X)
"""
function partial_map_classifier_eta(x::StructCSet{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where {S}
  codom = partial_map_functor_ob(x; pres=pres)[1]
  d = Dict([k=>collect(v) for (k,v) in pairs(id(x).components)])
  return CSetTransformation(x, codom; d...)
end



"""A partial function is defined by the following span:
                          m   f
                        A ↩ X → B

We compute ϕ(m,f): A ⟶ T(B) such that the following is a pullback square:
     f
  X  ⟶ B
m ↓     ↓ η(B)
  A  ⟶ T(B)
     ϕ

Essentially, ϕ sends elements of A to the 'real' values in T(B) when A is in
the subobject picked out by X. When A is 'deleted', it picks out the right
element of the additional data added by T(B).
"""
function partial_map_classifier_universal_property(
    m::CSetTransformation{S}, f::CSetTransformation{S};
    pres::Union{Nothing, Presentation}=nothing)::CSetTransformation where {S}
  hdata   = collect(zip(hom(S),dom(S),codom(S)))
  A, B    = codom(m), codom(f)
  ηB      = partial_map_classifier_eta(B;pres=pres)
  Bdict   = partial_map_functor_ob(B; pres=pres)[2]
  TB      = codom(ηB)
  fdata   = DefaultDict{Symbol, Dict{Int,Int}}(()->Dict{Int,Int}())
  res     = Dict{Symbol, Vector{Int}}()
  unknown = Dict{Symbol, Int}()
  is_injective(m) || error("partial map classifier called w/ non monic m $m")
  # Get mapping of the known values
  for (o, fcomp) in pairs(components(f))
    unknown[o] = nparts(TB, o)
    for (aval, fval) in zip(collect(m[o]), collect(fcomp))
      fdata[o][aval] = fval
    end
  end
  # Compute components of phi
  for o in topo_obs(S)
    res[o] = map(parts(A, o)) do i
      if haskey(fdata[o], i)
        return fdata[o][i]
      else # What kind of unknown value is it?
        homdata = [res[cd][A[i, h]] for (h,d,cd) in hdata if d == o]
        return Bdict[o][homdata]
      end
    end
  end
  ϕ = CSetTransformation(A, TB; res...)
  @assert is_natural(ηB)
  @assert is_natural(ϕ)
  @assert is_isomorphic(apex(pullback(ηB,ϕ)), dom(m))
  return ϕ
end

"""
See Theorem 2 of 'Concurrency Theorems for Non-linear Rewriting Theories'
      f
  B <--- A
m ↓      ↓ n
  C <--  D
     g

"""
function final_pullback_complement(fm::ComposablePair;
    pres::Union{Nothing, Presentation}=nothing)::ComposablePair
  f, m = fm
  A, B = dom(f), codom(f)
  m_bar = partial_map_classifier_universal_property(m, id(B); pres=pres)
  T_f = partial_map_functor_hom(f; pres=pres)
  pb_2 = pullback(T_f, m_bar)
  _, g = pb_2.cone
  s = Span(partial_map_classifier_eta(A; pres=pres), compose(f,m))
  n = universal(pb_2, s)
  @assert is_isomorphic(apex(pullback(m,g)), A)
  return ComposablePair(n, g)
end

"""
Sesqui-pushout is just like DPO, except we use a final pullback complement
instead of a pushout complement.
"""
function sesqui_pushout_rewrite_data(
    i::CSetTransformation,
    o::CSetTransformation,
    m::CSetTransformation;
    pres::Union{Nothing, Presentation}=nothing
    )::Tuple{CSetTransformation,CSetTransformation,
             CSetTransformation,CSetTransformation}
  m_, i_ = final_pullback_complement(ComposablePair(i, m); pres=pres)
  m__, o_ = pushout(o, m_).cocone

  return (m__, o_, m_, i_)
end

"""Just get the result of the SqPO transformation"""
function sesqui_pushout_rewrite(
    i::CSetTransformation, o::CSetTransformation, m::CSetTransformation;
    pres::Union{Nothing, Presentation}=nothing)::StructCSet
  m__, _, _, _ = sesqui_pushout_rewrite_data(i,o,m;pres=pres)
  return codom(m__)
end

# Single pushout rewriting

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
NOTE: In the following diagram, a double arrow indicates a monic arrow.

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


# Structured multicospan rewriting
##################################


"""
Initial data: 4 structured cospans + 3 cospan morphisms: μ, λ, ρ
     g
G₁₋ₙ --> G
↑    l  ↑ μ
L₁₋ₙ --> L
↑    i  ↑ λ
I₁₋ₙ --> I
↓    r  ↓ ρ
R₁₋ₙ --> R
Computed data: 2 new structured cospans + 4 cospan morphisms: γ, η, ik, rh
        G₁₋ₙ      G
          ↑    k  ↑ γ   ik
 I₁₋ₙ -> K₁₋ₙ  --> K    <-- I
          ↓    h  ↓ η   rh
 R₁₋ₙ -> H₁₋ₙ  --> H    <-- R
In the context of the legs of a multicospan, the indices 1-n refer to the n
legs of the cospan. In the context of a map of multicospans, there are 1-(n+1)
maps, with the first one designating the map of the apexes. Hence it can make
sense to have the elements: zip(legs, maps[2:end]) = [(legᵢ, mapᵢ), ...]
"""
function open_pushout_complement(
    rule::openrule,
    μ::StructuredMultiCospanHom)::openrule

  # Unpack data
  L_ = typeof(left(rule.data)).parameters[1];
  ob = L_.parameters[1]
  λ, ρ = rule.data;
  I, R, G = dom(ρ), codom(ρ), codom(μ);

  # Compute pushouts and pushout complements
  ik_γ = [pushout_complement(λᵢ,μᵢ) for (λᵢ, μᵢ) in zip(λ.maps, μ.maps)];
  rh_η = [legs(pushout(ρᵢ,ikᵢ)) for (ρᵢ, (ikᵢ, _)) in zip(ρ.maps, ik_γ)];
  rh, ik = rh_η[1][1], ik_γ[1][1]
  k = [compose(invert(ikᵢ), iᵢ, ik) for (iᵢ, (ikᵢ, _))
       in zip(legs(I), ik_γ[2:end])]
  h = [compose(invert(rhᵢ), r₍, rh) for (r₍, (rhᵢ, _))
       in zip(legs(R), rh_η[2:end])]

  # Reassemble resulting data into span of multicospans
  feetK = [FinSet(nparts(codom(ikᵢ), ob)) for (ikᵢ, _) in ik_γ[2:end]]
  feetH = [FinSet(nparts(codom(rhᵢ), ob)) for (rhᵢ, _) in rh_η[2:end]]
  K = StructuredMulticospan{L_}(Multicospan(k), feetK)
  H = StructuredMulticospan{L_}(Multicospan(h), feetH)
  maps_γ = ACSetTransformation[γᵢ for (_, γᵢ) in ik_γ]
  maps_η = ACSetTransformation[ηᵢ for (_, ηᵢ) in rh_η]
  γ = StructuredMultiCospanHom(K, G, maps_γ)
  η = StructuredMultiCospanHom(K, H, maps_η)
  return openrule(Span(γ, η))
end

"""
Extract the rewritten structured cospan from the induced rewrite rule
"""
function open_rewrite_match(
    rule::openrule, m::StructuredMultiCospanHom)::StructuredMulticospan
  right(open_pushout_complement(rule, m).data).tgt
end

"""
Apply a rewrite rule to a structured multicospan, where a matching cospan
homomorphism is found automatically. If multiple matches are found, a particular
one can be selected using `m_index`. Returns `nothing` if none are found.
"""
function open_rewrite(rule::openrule, G::StructuredMulticospan;
                      monic::Bool=false, m_index::Int=1)::StructuredMulticospan

  ms = filter(m->can_open_pushout_complement(left(rule.data), m),
              open_homomorphisms(left(rule.data).tgt, G, monic=monic))
  if 0 < m_index <= length(ms)
    open_rewrite_match(rule, ms[m_index])
  else
    nothing
  end
end

end # module
