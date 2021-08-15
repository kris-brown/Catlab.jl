using Catlab.CategoricalAlgebra
using Catlab.Present
using Catlab.Theories
using Catlab.WiringDiagrams
using Catlab.Programs
using Catlab.Programs.RelationalPrograms: parse_relation_context, parse_relation_call

using Catlab.CategoricalAlgebra.FinSets
using Catlab.CategoricalAlgebra.CSetDataStructures: AttributedCSet
using DataStructures: IntDisjointSets, find_root!

struct Schema
  arities::Dict{Symbol, Int}
end

ids = x -> Symbol("id_$x")
arg = (x, y) -> Symbol("$(x)_$y")

"""
We can slightly complicate this by splitting V up into an object for each color
and arities can be a list of symbols.
"""
function schema_to_csettype(sch::Schema)
  pres = Presentation(FreeSchema)

  Id, Name = [FreeSchema.Data{:generator}([x], []) for x in [:Id, :Name]]
  add_generator!(pres, Id)

  relobs = [Ob(FreeSchema, s) for s in keys(sch.arities)]
  vob = Ob(FreeSchema, :V)

  add_generator!(pres, vob)
  add_generator!(pres, FreeSchema.Attr{:generator}([:id_V, vob, Id], [vob, Id]))

  for x in relobs
    add_generator!(pres, x)
    add_generator!(pres, FreeSchema.Attr{:generator}(
      [ids(x.args[1]), x, Id], [x, Id]))
  end

  for (n, (s, a)) in enumerate(sch.arities)
    relob = relobs[n]
    for src_sym in 1:a
      add_generator!(pres, Hom(arg(s,src_sym), relob, vob))
    end
  end

  cset = ACSetType(pres, index=vcat([:id_V],
                   map(ids, collect(keys(sch.arities)))))
  return ACSetType(pres){Int}, cset{Int}
end

"""
Dependency: When the body pattern is seen, the result pattern is asserted to
exist and eqs hold between subsets of the body variables.
"""
struct Dep
  body :: ACSet
  res :: ACSet
  eqs :: Set{Set{Int}}
end

function Dep(body::ACSet,res::ACSet)::Dep
  return Dep(body,res,Set{Set{Int}}())
end

struct restricted_chase
  I::ACSet
  It::Type
  Σ::Set{Dep}
end

struct chase_state
  I::ACSet
  dI::ACSet
  counter::Int
end

function maxes(x::ACSet{CD})::Dict{Symbol, Int} where {CD}
  Dict([o => max0(x[ids(o)]) for o in ob(CD)])
end

function merge_maxes(d1::Dict{Symbol, Int},
                     d2::Dict{Symbol, Int})::Dict{Symbol, Int}
  Dict([o => max(d1[o], d2[o]) for o in keys(d1)])
end

Base.isempty(rc::chase_state) = sum(nparts(rc.dI, o)
  for o in filter(!=(:V), ob(typeof(rc.dI).parameters[1]))) == 0

function Base.union(x::ACSet{CD}, y::ACSet{CD})::ACSet{CD} where {CD}
  if nparts(x, :V) == 0 return y
  elseif nparts(y,:V) ==0 return x
  end

  overlap = AttributedCSet{typeof(x).parameters...}()
  o_ids = Dict([let s = ids(o); o=>collect(x[s] ∩ y[s]) end
                for o in ob(CD)])
  o_indexes = filter(x->!isempty(x[2]), [o => vcat(incident(x, v, ids(o))...)
               for (o, v) in collect(o_ids)])
  if !isempty(o_indexes)
    copy_parts!(overlap, x; Dict(o_indexes)...)
  end
  inexact = collect(filter(!=(:id_V), map(ids, ob(CD))))
  fx = homomorphism(overlap,x)
  fy = homomorphism(overlap,y, inexact=inexact)
  !(fx===nothing) || error("overlap $overlap x $x")
  !(fy===nothing) || error("overlap $overlap y $y")
  res = apex(pushout(fx,fy))
  trim!(res)
  return res
end

"""Computes d1;d2 as functions"""
# function compdict(d1::Dict{Int,Int}, d2::Dict{Int,Int})::Dict{Int,Int}
#   res = deepcopy(d2)
#   for (k, v) in collect(d1)
#     res[k] = get(d2, v, v)
#   end
#   return filter(x->x[1]!=x[2], res)
# end
# appdict(d::Dict{Int,Int}, v::Vector{Int}) = [get(d, x, x) for x in v]
# appdict(d::Dict{Int,Int}, v::Set{Int}) = Set([get(d, x, x) for x in collect(v)])
unionfind_to_dict(d::IntDisjointSets, idvec::Vector{Int})::Dict{Int,Int} = Dict(
  [idvec[k]=>idvec[v] for (k, v) in [
  x => find_root!(d, x) for x in 1:length(d)] if k!=v])
"""
Apply a mapping to a DB instance. The mapping refers to V id's. {a ↦ b}
collapses the vertex identified by `a` into the vertex identified by `b`.
If `b` is not found in the DB instance, a vertex gets created for it.
"""
function appdict(d::Dict{Int,Int}, I::ACSet{CD})::ACSet{CD} where {CD}
  I_ = deepcopy(I)
  seenV = Set{Int}()
  for o in filter(!=(:V), ob(CD))
    del_list, seen = Int[], Set()
    for (i, r) in enumerate(I.tables[o])
      for (k, v) in filter(x->x[1]!=ids(o), collect(zip(keys(r), r)))
        v_id = I_[:id_V][v]
        new_v_id = get(d, v_id, v_id)
        # println("o $o i $i r $r k $k v_id $v_id I_[id_V] new_v_id $new_v_id | $(I_[:id_V])")
        new_v_ = incident(I_, new_v_id, :id_V)
        new_v = isempty(new_v_) ? add_part!(I_, :V, id_V=new_v_id) : only(new_v_)
        push!(seenV, new_v)
        set_subpart!(I_, i, k, new_v)
      end
      new_r = collect(I_.tables[o][i])[1:end-1]
      # println("o $o i $i new_r $new_r")
      if new_r in seen
        push!(del_list, i)
      else
        push!(seen, new_r)
      end
    end
    # println("Del list $o $del_list")
    rem_parts!(I_, o, del_list)
  end
  rem_parts!(I_, :V, sort(collect(setdiff(parts(I_, :V), seenV))))
  return I_
end

max0 = x -> isempty(x) ? 0 : maximum(x)


"""Offset IDs componentwise"""
function offset(I::ACSet{CD}, maxes::Dict{Symbol, Int})::ACSet{CD} where {CD}
  res = deepcopy(I)
  for o in ob(CD)
    atr, off = ids(o), maxes[o]
    for i in sort(res[atr], rev=true)
      set_subpart!(res, only(incident(res, i, atr)), atr, i + off)
    end
  end
  return res
end

"""Creates a new version of add_on with fresh ids
I - a base that will have y added to it
mapping - a subset of node IDs in add_on are mapped to IDs in I
add_on - a pattern that will be added to I
"""
function fresh(mapping::Dict{Int,Int},
               add_on::ACSet{CD}, mxs::Dict{Symbol, Int})::ACSet where {CD}
  new_add_on1 = offset(add_on, mxs)
  μ = Dict([k+mxs[:V]=>v for (k, v) in pairs(mapping)])
  new_add_on2 = appdict(μ, new_add_on1)
  trim!(new_add_on2)
  return new_add_on2
end


"""Remove nodes that appear in no tuples. Remove duplicate tuples."""
function trim!(I::ACSet{CD})::Nothing where {CD}
  keep_v = Set{Int}()
  for o in filter(!=(:V), ob(CD))
    del_list, seen = Int[], Set()
    for (i, r) in enumerate(I.tables[o])
      vs = collect(r)[1:end-1]
      if vs in seen
        push!(del_list, i)
      else
        push!(seen, vs)
        union!(keep_v, vs)
      end
    end
    rem_parts!(I, o, del_list)
  end
  del_v = sort(collect(setdiff(parts(I, :V), keep_v)))
  rem_parts!(I, :V, del_v)
  return nothing
end

function Base.iterate(IΣ::restricted_chase)::Tuple{ACSet, chase_state}
  iterate(IΣ, chase_state(IΣ.I, IΣ.I, 1))
end

function Base.iterate(IΣ::restricted_chase, state::Union{Nothing,chase_state}
                      )::Union{Nothing, Tuple{ACSet, chase_state}}
  if isempty(state) # Terminate
    return nothing
  else # Normal
    I, ∆I, counter = state.I, state.dI, state.counter
  end
  println("counter = $counter\nI=$I\n∆I=$∆I")
  N = IΣ.It() # new changes from TGDs
  μ = IntDisjointSets(nparts(I, :V))
  for τ in IΣ.Σ
    for trig in query(I, tgd_relation(τ.body)[1])
      #println("potential trigger in I $trig")
      # make sure trigger at least somewhat pertains to the 'unknown' subset of I
      d = zip([parse(Int, string(k)[2:end]) for k in keys(trig)], trig)
      d2 = Dict([k=>I[:id_V][v] for (k,v) in d])
      if !isempty(intersect(values(d2), ∆I[:id_V]))  # ACTUALLY we should check that any of the relations intersect, not the vertices. Requires change to output of query

        # Quotient by equivalences
        for eqset in τ.eqs
          eqids = [only(incident(I, d2[x], :id_V)) for x in eqset]
          for (x, y) in zip(eqids, eqids[2:end])
            union!(μ, x, y)
          end
        end

        # Add to graph if needed
        if nparts(τ.res, :V) > 0
          q, ps = tgd_relation(τ.res, d2)
          uI = appdict(unionfind_to_dict(μ, I[:id_V]), I ∪ N)
          if isempty(query(uI, q, ps))
            #println("active tgd trigger w/ $d2")
            newstuff = fresh(d2, τ.res, merge_maxes(maxes(N), maxes(I)))
            println("newstuff $newstuff")
            N = N ∪ newstuff
          end
        end
      end
    end
  end
  μ = unionfind_to_dict(μ, I[:id_V])
  println("μ = $μ")
  ∆I = appdict(μ, N) # TODO understand what line 14 means
  # prune!(∆I, setdiff(Set(N[:id_V]), Set(I[:id_V])))
  I = union(appdict(μ, I), ∆I)
  println("end of iteration: I=$I")# \ndI = $∆I")
  return I, chase_state(I, ∆I, counter+1) # output, new_state
end
Base.IteratorSize(::restricted_chase) = Base.IsInfinite()


function tgd_relation(X::ACSet{CD}, bound::Dict{Int,Int}=Dict{Int,Int}()
                      )::Tuple{UndirectedWiringDiagram, NamedTuple} where {CD}
  vars = [Symbol("x$i") for i in X[:id_V]]
  bodstr, params = ["begin"], Set{String}()
  for (k, v) in collect(bound)
    bound_ind = findfirst(==(k), X[:id_V])
    if !(bound_ind===nothing)
      push!(bodstr, "V(_id=$(vars[bound_ind]),id_V=i$v)")
      push!(params, ("i$v=$v"))
    end
  end
  for o in filter(!=(:V), ob(CD))
    for row in X.tables[o]
      is = enumerate(collect(row)[1:end-1])
      push!(bodstr, "$o($(join(["$(arg(o,i))=$(vars[v])"
                                for (i, v) in is],",")))")
    end
  end
  push!(bodstr, "end")
  exstr = "($(join(["$v=$v" for v in vars],",") ))"
  ctxstr = "($(join(vcat(
    ["$v::V" for v in vars],
    collect(Set(["i$v::Int" for v in values(bound)]))
    ),",")))"
  pstr = "($(join(params,",")),)"
  ex  = Meta.parse(exstr)
  ctx = Meta.parse(ctxstr)
  hed = Expr(:where, ex, ctx)
  bod = Meta.parse(join(bodstr, "\n"))
  # println("$exstr\n$ctxstr\n$bodstr\n$pstr")
  ps = isempty(bound) ? NamedTuple() : eval(Meta.parse(pstr))
  return parse_relation_diagram(hed, bod), ps
end

# Tests
if 1+1==1
  sch = Schema(Dict(:R=>2, :A=>1))
  _, Isch = schema_to_csettype(sch)
  I = Isch()
  add_parts!(I, :V, 2, id_V=[101,202])
  add_parts!(I, :R, 2, R_1=[1,2], R_2=[2,2], id_R=[1001,2002])
  I2 = deepcopy(I)
  add_parts!(I2, :V, 1, id_V=[303])
  add_parts!(I2, :A, 2, A_1=[2,3], id_A=[1000,2000])
  I3 = deepcopy(I2)
  add_parts!(I2, :R, 1, R_1=[2], R_2=[3], id_R=[3003]) # x2, y relation
  add_parts!(I3, :R, 1, R_1=[1], R_2=[3], id_R=[3003]) # x1, y relation

  t1 = @acset Isch begin
    V = 2
    R = 1
    R_1 = [1]
    R_2 = [2]
    id_V = [11, 22]
    id_R = [241]
  end
  t2 = @acset Isch begin
    V = 3
    R = 1
    A = 2
    R_1 = [1]
    R_2 = [3]
    A_1 = [3, 2]
    id_V = [11,22,33]
    id_R = [799]
    id_A = [900, 901]
  end
  tgd3 = Dep(t1, t2)
  egd3 = Dep(t1, Isch(), Set([Set([11,22])]))
  te = Dep(t1, t2, Set([Set([11,22])]))

  rc = restricted_chase(I, Isch, Set([te]))
  che = collect(Iterators.take(rc, 4))
end