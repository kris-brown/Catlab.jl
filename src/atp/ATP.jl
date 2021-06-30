using Catlab.WiringDiagrams
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra.StructuredCospans
using Catlab.Present: translate_generator
using Catlab.CategoricalAlgebra.FinSets
using Catlab.Theories: attr, adom
using Catlab.CategoricalAlgebra.DPO
using Catlab.CategoricalAlgebra.DPO: rewrite_match_data

using AutoHashEquals
using DataStructures: IntDisjointSets, find_root

WD = WiringDiagram{Any,Any,Any,Any}
WDPair = Pair{WiringDiagram{Any,Any,Any,Any},
              WiringDiagram{Any,Any,Any,Any}}

"""
An equation for a partial theory. May or may not be reversible.
"""
function check_wd(wd::WD)::Nothing
    d = wd.diagram
    # no pass through wires
    nparts(d, :PassWire) == 0 || error("$wd has a passthrough wire")
    # Every external port has exactly one external wire
    for (w, W, p) in [(:in_src,:InWire, :OuterInPort),
                      (:out_tgt, :OutWire, :OuterOutPort)]
        nparts(d, W) == nparts(d, p) || error("#$W != #$p")
        err = "$w indices: $(d.indices[w]) - not all length 1"
        all(x->length(x)==1, d.indices[w]) || error(err)
    end
    # Every port has exactly one wire/extwire connected
    for (ew, w, p) in [(:in_tgt, :tgt, :InPort),
                      (:out_src, :src, :OutPort)]
        ewind, wind = [d.indices[x] for x in [ew, w]]
        ewlen, wlen = [map(length, x) for x in [ewind, wind]]

        for port in 1:nparts(d, p)
            err = "Port $port does not have exactly one wire"
            sort([ewlen[port], wlen[port]]) == [0, 1] || error("$wd\n"*err)
        end
    end
    # TODO
    # all junctions must have same type for all in/outports
    # external port types must match internal ports they're connected to

end

@auto_hash_equals struct Eq
    name::Symbol
    l::WD
    r::WD
    rev::Bool
    function Eq(n,l,r,v)
        for ext in [:OuterInPort, :OuterOutPort]
            err = "$n has different # of $ext in left and right patterns"
            @assert nparts(l.diagram, ext) == nparts(r.diagram, ext) err
        end
        check_wd(l)
        check_wd(r)
        return new(n,l,r,v)
    end
end
function Base.isless(x::Eq, y::Eq)::Bool
    return Base.isless(x.name, y.name)
end

"""
TODO Automatically create (total) intro and single-valuedness axioms for gens.
These defaults can be overridden by providing eqs [SYM]_intro and [SYM]_sv
respectively.
"""
struct EqTheory
    gens :: Set{Box{Symbol}}
    eqs :: Set{Eq}
    function EqTheory(gs::Set{Box{Symbol}}, es::Set{Eq})
        es = deepcopy(es)
        esyms = Set{Symbol}()
        for eq in es
            check_eq(gs, eq)
            push!(esyms, eq.name)
        end
        # Create total intro and singlevalued axioms for each gen if not in e
        for gen in gs
            si, ss = [Symbol(string(gen.value)*x) for x in ["_intro", "_sv"]]
            si in esyms || push!(es, intro_rule(gen))
            ss in esyms || push!(es, singlevalued_rule(gen))
        end
        return new(gs,es)
    end
end

ϵ_box(x::Symbol) = Junction(x, 1, 0)
δ_box(x::Symbol) = Junction(x, 1, 2)
μ_box(x::Symbol) = Junction(x, 2, 1)

function intro_rule(gen::Box{Symbol})::Eq
    l, r = [WiringDiagram(gen.input_ports, Symbol[]) for _ in 1:2]
    rb = add_box!(r, gen)
    for (i, typ) in enumerate(gen.input_ports)
        b = add_box!(l, ϵ_box(typ))
        add_wire!(l, (input_id(l), i)=>(b,1))
        add_wire!(r, (input_id(r), i)=>(rb,i))
    end
    for (i, typ) in enumerate(gen.output_ports)
        b = add_box!(r, ϵ_box(typ))
        add_wire!(r, (rb, i)=>(b, 1))
    end
    return Eq(Symbol(string(gen.value)*"_intro"), l, r, false)
end

function singlevalued_rule(gen::Box{Symbol})::Eq
    op = gen.output_ports
    no = length(op)
    l, r = [WiringDiagram(gen.input_ports, [op...,op...]) for _ in 1:2]
    lb1, lb2 = add_boxes!(l, [gen, gen])
    rb = add_box!(r, gen)

    for (i, typ) in enumerate(gen.input_ports)
        lδ = add_box!(l, δ_box(typ))
        add_wires!(l, Pair[
            (input_id(l), i)=>(lδ,1),
            (lδ, 1) => (lb1, i),
            (lδ, 2) => (lb2, i)])
        add_wire!(r, (input_id(r), i)=>(rb,i))
    end
    for (i, typ) in enumerate(op)
        rδ = add_box!(r, δ_box(typ))
        add_wires!(r, Pair[
            (rb, i)=>(rδ,1),
            (rδ, 1) => (output_id(r), i),
            (rδ, 2) => (output_id(r), i+no)])
        add_wires!(l, Pair[
            (lb1,i)=>(output_id(l), i),
            (lb2,i)=>(output_id(l), i+no)])
        end

    return Eq(Symbol(string(gen.value)*"_sv"), l, r, false)

end

"""

"""
function check_eq(Σ::Set{Box{Symbol}}, e::Eq)::Nothing
    for s in [:outer_in_port_type, :outer_out_port_type]
        e.l.diagram[s] == e.r.diagram[s] || error("Interfaces of $e don't match")
    end
    Σd = Dict{Symbol, Pair{Vector{Symbol}, Vector{Symbol}}}([
        b.value => (b.input_ports => b.output_ports) for b in Σ])
    check_wd(Σd, e.l)
    check_wd(Σd, e.r)
end
"""
Check that all terms in eqs are built from generators in gens / have
the right arity
"""
function check_wd(Σ::Dict{Symbol, Pair{Vector{Symbol},Vector{Symbol}}},
                  wd::WD)::Nothing
    for b in boxes(wd)
        if haskey(Σ, b.value)
            ps = b.input_ports => b.output_ports
            ps == Σ[b.value] || error("Wd $wd Box $b has mismatch with signature $Σ")
        else
            b isa Junction || error("Wd $wd Unknown box symbol $(b.value) for $Σ")
        end
    end
end

function Base.union(t1::EqTheory, t2::EqTheory)::EqTheory
    return EqTheory(union(t1.gens, t2.gens), union(t1.eqs, t2.eqs))
end

function Base.union(t1::EqTheory, gens::Set{Box{Symbol}}, eqs::Set{Eq})::EqTheory
    return EqTheory(union(t1.gens, gens), union(t1.eqs, eqs))
end

function add_eq(t::EqTheory, eqs...)::EqTheory
    return EqTheory(t.gens, union(t.eqs, eqs))
end

function Base.getindex(t::EqTheory, x::Symbol)::Eq
    for eq in t.eqs
        if eq.name == x
            return eq
        end
    end
    throw(KeyError(x))
end


"""
Defined only for monic morphisms
"""
function invert(x::ACSetTransformation)::ACSetTransformation
    function invert_comp(s::Symbol)::Vector{Int}
        res = Int[]
        for i in 1:nparts(codom(x), s)
            v = findfirst(==(i), collect(x.components[s]))
            if v === nothing
                push!(res, 1)
            else
                push!(res, v)
            end
        end
        return res
    end
    d = Dict([s=>invert_comp(s) for s in keys(x.components)])
    return ACSetTransformation(codom(x), dom(x); d...)
end

function δsd(x::Symbol)::WD
    wd = WiringDiagram([x], [x,x])
    add_box!(wd, δ_box(x))
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (1,1),
        (1,1) => (output_id(wd), 1),
        (1,2) => (output_id(wd), 2)])
    return wd
end

function μsd(x::Symbol)::WD
    wd = WiringDiagram([x,x],[x])
    add_box!(wd, μ_box(x))
    add_wires!(wd, Pair[
        (input_id(wd), 1) => (1,1),
        (input_id(wd), 2) => (1,2),
        (1,1) => (output_id(wd), 1)])
    return wd
end

"""
Apply equality as a rewrite rule

repl = replace one side of an equality with the other, as opposed to just
adding the other side to a diagram.

forward = the searched pattern is the `l` side of the Eq

n = expected number of homomorphisms (default of -1 means allow any #)
"""
function apply_eq(sc_cset::ACSet, T::EqTheory,
                  eq::Symbol; forward::Bool=true, repl::Bool=false,
                  n::Int=1, monic::Bool=false,
                  kw...
                 )::ACSet
    rule = T[eq]
    partial = Dict{Symbol, Dict{Int,Int}}([k=>Dict(v)
                                           for (k, v) in collect(kw)])
    # Orient the rule in the forward or reverse direction, determining which
    # side of the rule is the "L" pattern in the DPO rewrite
    @assert rule.rev || forward "Cannot apply $(rule.name) in reverse direction"
    l, r = map(wd_pad, forward ? (rule.l, rule.r) : (rule.r, rule.l))
    pat,_,Lmap = wd_to_cospan(l, T.gens)[2:4]

    # l is either replaced with merging of l and r or, or just r
    r_, lrmap = repl ? (r, nothing) : branch(l, r)[1:2]
    R_,ccR,Rmap = wd_to_cospan(r_, T.gens)[2:4]

    # Store interface data and then erase it from CSets
    vmap = Pair{Int,Int}[]
    for i in 1:nparts(pat, :_I)
        push!(vmap, pat[:_i][i] => R_[:_i][i])
    end
    for o in 1:nparts(pat, :_O)
        push!(vmap, pat[:_o][o] => R_[:_o][o])
    end
    vmapset = sort(collect(Set(vmap)))

    rem_IO!(pat)
    rem_IO!(R_)
    if repl
        I = sigma_to_hyptype(T.gens)[4]()
        lnodes = [v[1] for v in vmapset]
        add_parts!(I, :V, length(vmapset), color=pat[:color][lnodes])
        L = ACSetTransformation(I, pat, V=lnodes)
        R = ACSetTransformation(I, R_, V=[v[2] for v in vmapset])
    else
        L = id(pat)
        R = construct_cospan_homomorphism(pat, R_, Lmap, lrmap, Rmap, ccR)
    end

    # Construct match morphism
    pdict = Dict(k=>[get(v, i, nothing) for i in 1:nparts(pat, k)]
                     for (k, v) in collect(partial))
    ms = filter(m->valid_dpo(L,m), homomorphisms(
        pat, sc_cset, monic=monic, initial=pdict))

    # could we do a horizontal composition of structured cospan rewrites to
    # do all at once?
    mseq = []
    hcs = [h.components for h in ms]
    err = "expected $n matches, but found $(length(ms)): $(hcs)"
    n == -1 || length(ms) == n || error(err)
    if isempty(ms)
        return sc_cset
    end
    h = nothing

    for m in ms
         new_m = compose(vcat([m], mseq))
         _, g, _, h = rewrite_match_data(L,R,new_m)
         append!(mseq, [invert(g), h])
    end
    new_apex = codom(h)
    return new_apex
end

"""
A cospan homomorphism requires inputs and outputs to be isomorphic and for the
following diagram to commute
   X1
  ↗   ↖
I   ↓  O
  ↘   ↙
   X2
"""
function csp_homomorphic(sc_cset1, sc_cset2)::Bool
    return is_homomorphic(sc_cset1, sc_cset2, iso = [:_I, :_O])
end

"""
Remove the _I and _O components
"""
function rem_IO!(sc_cset::ACSet)::Nothing
    rem_parts!(sc_cset, :_I, 1:nparts(sc_cset,:_I))
    rem_parts!(sc_cset, :_O, 1:nparts(sc_cset,:_O))
end

"""
Remove redundant nodes of a hypergraph. Paradigmatic case:

 ↗[F]↘
•     •   ... this can be simplified to •→[F]→•
 ↘[F]↗

A less trivial case, two copies of the following w/ same input and output:
⟶ [F] ⟶ [G] ⟶
   ↑        ↓
  [e]      [X]

Perhaps a search over all pairs of hyperedge legs that emanate from the same
vertex? Homomorphism queries for each possible subhypergraph?
"""
function rem_dups!(sc_cset::ACSet)::Nothing
    # to do
end


"""
Construct a cospan homomorphism from the following data:
WD₁  ↪  WD₂
 ↟       ↟
CSP₁ → CSP₂
The maps from CSP to WD are effectively surjective because we keep track of the
connected components in the WD.
"""
function construct_cospan_homomorphism(csp1::ACSet, csp2::ACSet,
                                       cspwd1::Dict{Symbol, Vector{Int}},
                                       wd1wd2::Vector{Int},
                                       cspwd2::Dict{Symbol, Vector{Int}},
                                       cc2::Dict{Int,Int}
                                       )::ACSetTransformation
    d = Dict{Symbol, Vector{Int}}()
    for (k, map1) in collect(cspwd1)
        mapping, map2 = Int[], [get(cc2, i, i) for i in cspwd2[k]]
        for (_, csp1box) in enumerate(map1)
            csp2box = wd1wd2[csp1box]
            csp2box_canonical = get(cc2, csp2box, csp2box)
            res = findfirst(==(csp2box_canonical), map2)
            push!(mapping, res)
        end
        d[k] = mapping
    end
    return ACSetTransformation(csp1, csp2; d...)
end

function branch(l::WD, r::WD)# ::WD
    ld, rd = l.diagram, r.diagram
    nin, nout = [nparts(ld, x) for x in [:OuterInPort, :OuterOutPort]]
    intypes, outtypes = ld[:outer_in_port_type], ld[:outer_out_port_type]
    res = WiringDiagram(intypes, outtypes)
    inboxes = [add_box!(res, δ_box(s)) for s in intypes]
    outboxes = [add_box!(res, μ_box(s)) for s in outtypes]
    subbox = Box(intypes, outtypes)
    b1, b2 = [add_box!(res, subbox) for _ in 1:2]
    for i in 1:nin
        add_wires!(res, Pair[
            (input_id(res), i) => (inboxes[i], 1),
            (inboxes[i], 1) => (b1, i),
            (inboxes[i], 2) => (b2, i)])
    end
    for i in 1:nout
        add_wires!(res, Pair[
            (outboxes[i], 1) => (output_id(res), i),
            (b1, i) => (outboxes[i], 1),
            (b2, i) => (outboxes[i], 2)])
    end
    subboxes = [[δsd(s) for s in intypes]...,
                [μsd(s) for s in outtypes]..., l, r]
    start = nin+nout
    lb, rb = [nparts(x, :Box) for x in [ld, rd]]
    lboxrange = collect(start+1:start+lb)
    rboxrange = collect(start+lb+1:start+lb+rb)
    ores = ocompose(res, subboxes)
    @assert start+lb+rb == nparts(ores.diagram, :Box)
    return ores, lboxrange, rboxrange
end

"""
Prove an inequality in a relational theory
Return homomorphism as witness, if any
Takes in set of generators Σ, equations I, wiring diagram csets c1 and c2.
If oriented, then rewrites are only applied in the forward direction.
"""
function prove(T::EqTheory, c1::WD, c2::WD;
               n::Int=3, oriented::Bool=false)::Union{Nothing, Any}
    d1 = wd_to_cospan(c1, T.gens)[2]
    d2 = wd_to_cospan(c2, T.gens)[2]
    h = homomorphism(d2, d1)
    if !(h===nothing)
        return h
    end
    for _ in 1:n
        for eq in sort(collect(T.eqs)) #, rev=true)
            # println("applying $(eq.name)")
            d1 = apply_eq(d1, T, eq.name; n=-1)
            if !oriented && eq.rev  # apply both rewrite rules
                d1 = apply_eq(d1, T, eq.name; forward=false, match=false)
            end
            h = homomorphism(d2, d1)
        end
        if !(h===nothing)
            return h
        end
    end
    return nothing # return d1 if debugging
end


"""
Given a signature, create an OpenCSetType for hypergraphs including a distinct
hyperedge for each arity (distinguished by # and type of in/outputs).

TODO: return a specific ACSet HΣ for the signature, where being homomorphic to
HΣ means that a diagram satisfies the signature.
"""
function sigma_to_hyptype(Σ::Set{Box{Symbol}})
    arities = Dict{Pair{Vector{Symbol}, Vector{Symbol}}, Set{Symbol}}()
    for op in Σ
        ar = op.input_ports => op.output_ports
        if haskey(arities, ar)
            push!(arities[ar], op.value)
        else
            arities[ar] = Set([op.value])
        end
    end
    pres = Presentation(FreeSchema)
    name = FreeSchema.Data{:generator}([:Name], [])
    add_generator!(pres, name)
    obsyms = [:V]
    for (i, o) in keys(arities)
        push!(obsyms, hypsyms(i,o)[1])
    end
    xobs = [Ob(FreeSchema, s) for s in obsyms]

    for x in xobs
        add_generator!(pres, x)
    end

    v = xobs[1]
    add_generator!(pres, FreeSchema.Attr{:generator}(
        [:color, xobs[1], name], [xobs[1], name]))

    for (n, (i, o)) in enumerate(keys(arities))
        x = xobs[n+1]
        _, lab, src, tgt = hypsyms(i, o)
        add_generator!(pres, FreeSchema.Attr{:generator}(
            [lab, x, name], [x, name]))

        for src_sym in src
            add_generator!(pres, Hom(src_sym, x, v))
        end
        for tgt_sym in tgt
            add_generator!(pres, Hom(tgt_sym, x, v))
        end
    end
    acst = ACSetType(pres, index=[])
    obtype, sctype = OpenACSetTypes(acst, :V)

    # Explicit cospan CSet
    _I, _O = Ob(FreeSchema, :_I), Ob(FreeSchema, :_O)
    add_generator!(pres, _I)
    add_generator!(pres, _O)
    add_generator!(pres, Hom(:_i, _I, xobs[1]))
    add_generator!(pres, Hom(:_o, _O, xobs[1]))
    cspcset = ACSetType(pres, index=[])
    return acst{Symbol}, obtype{Symbol}, sctype{Symbol}, cspcset{Symbol}
end

function hypsyms(i::Vector{Symbol}, j::Vector{Symbol}
                )::Tuple{Symbol, Symbol, Vector{Symbol}, Vector{Symbol}}
    str = x -> join(map(string,x),"_")
    istr, jstr = map(str, [i,j])
    ename = Symbol("E__$(istr)__$jstr")
    lab = Symbol("l__$(istr)__$jstr")
    src = [Symbol("s__$(istr)__$(jstr)__$i_ind") for i_ind in eachindex(i)]
    tgt = [Symbol("t__$(istr)__$(jstr)__$j_ind") for j_ind in eachindex(j)]
    return ename, lab, src, tgt
end


"""
Add a empty node between each generator and the outerbox and a node between each
generator. This should be an idempotent function. (todo: add tests for this)
"""
function wd_pad(sd::WD)::WD
    check_wd(sd)
    sd = deepcopy(sd)
    d = sd.diagram
    in_delete, out_delete = Set{Int}(), Set{Int}()
    extwires = [:InWire, :OutWire]
    portboxes = [:in_port_box, :out_port_box]
    exttypes = [:outer_in_port_type, :outer_out_port_type]
    deletes = [in_delete, out_delete]
    extsrctgt = [(:in_src, :in_tgt), (:out_src, :out_tgt)]
    for (i,j) in [(1,2),(2,1)]
        extwire = extwires[i]
        portbox = portboxes[i]
        extsrc, exttgt = extsrctgt[i]
        for (outwire_id, extwire_data) in enumerate(d.tables[extwire])
            extport, innerport = collect(extwire_data)[[i,j]]
            if d[:box_type][d[portbox][innerport]] <: Box
                exttype = d[exttypes[i]][extport]
                newbox = add_part!(d, :Box, value=exttype,
                                   box_type=Junction{Nothing, Symbol})
                new_in = add_part!(d, :InPort, in_port_box=newbox,
                                   in_port_type=exttype)
                new_out = add_part!(d, :OutPort, out_port_box=newbox,
                                    out_port_type=exttype)
                extin = [extport, new_out]
                extout = [new_in, extport]
                insrc = [new_out, innerport]
                intgt = [innerport, new_in]
                add_part!(d, extwire; Dict([extsrc => extin[i], exttgt => extout[i]])...)
                add_part!(d, :Wire, src=insrc[i], tgt=intgt[i], wire_value=nothing)
                push!(deletes[i], outwire_id)
            end
        end
    end
    w_delete = Set{Int}()
    for (w, (s_port, t_port, _)) in enumerate(d.tables[:Wire])
        s_box = d[:out_port_box][s_port]
        t_box = d[:in_port_box][t_port]
        if d[:box_type][s_box] <: Box && d[:box_type][t_box] <: Box
            s_typ, t_typ = d[:out_port_type][s_port], d[:in_port_type][t_port]
            newbox = add_part!(d, :Box, value=s_typ, box_type=Junction{Nothing, Symbol})
            new_in = add_part!(d, :InPort, in_port_box=newbox, in_port_type=s_typ)
            new_out = add_part!(d, :OutPort, out_port_box=newbox, out_port_type=t_typ)
            add_part!(d, :Wire, src=s_port, tgt=new_in, wire_value=nothing)
            add_part!(d, :Wire, src=new_out, tgt=t_port, wire_value=nothing)
            push!(w_delete, w)
        end
    end
    # no FKs point to a wire, so we can freely delete them
    rem_parts!(d, :Wire, sort(collect(w_delete)))
    rem_parts!(d, :InWire, sort(collect(in_delete)))
    rem_parts!(d, :OutWire, sort(collect(out_delete)))
    return sd
end

"""
For a Wiring Diagram with labeled ports, a given box has an arity (and coarity)
"""
function get_arity(sd::WD, i::Int)::Pair{Vector{Symbol}, Vector{Symbol}}
    d = sd.diagram
    ss = [:in_port_box => :in_port_type, :out_port_box => :out_port_type]
    ip, op = [d[y][incident(d, i, x)] for (x, y) in ss]
    return ip => op
end

"""
Convert wiring diagram to cospan
All components connected by Frobenius generators are condensed together.
"""
function wd_to_cospan(sd::WD, Σ::Set{Box{Symbol}}
                     )# ::Tuple{StructuredCospan, ACSet}
    sd = wd_pad(sd)
    d = sd.diagram
    aptype, _, sctype, sccsettype = sigma_to_hyptype(Σ)

    # For each component in apex, keep track of which box each part comes from
    mapping = Dict([sym => Int[] for sym in ob(aptype.body.body.parameters[1])])

    # Isolate box indices that correspond to Frobenius nodes
    nodes = [i for (i, v) in enumerate(d[:box_type]) if v<:Junction]
    # Determine connected components by iterating over all wires
    conn_comps = IntDisjointSets(nparts(d, :Box))
    for (srcport, tgtport, _) in d.tables[:Wire]
        srcbox, tgtbox = d[:out_port_box][srcport], d[:in_port_box][tgtport]
        if srcbox in nodes && tgtbox in nodes
            union!(conn_comps, srcbox, tgtbox)
        end
    end

    # Get hyperedge-specific info given a box index
    hs = i -> hypsyms(get_arity(sd, i)...)

    # Total # of connected components
    n = conn_comps.ngroups - (nparts(d, :Box) - length(nodes))
    nodetypes = Union{Nothing, Symbol}[nothing for _ in 1:n]

    # Representative box index for each connected component
    cclist = sort(collect(Set([find_root(conn_comps,i) for i in nodes])))

    mapping[:V] = cclist
    # Map each boxid (that is Frobenius) to boxid that is its representative
    vert_dict = Dict([i=>findfirst(==(find_root(conn_comps,i)), cclist)
                      for i in nodes])
    apx = aptype()
    add_parts!(apx, :V, n)
    box_dict = Dict{Int,Int}()
    for (box, (val, btype)) in enumerate(zip(d[:value], d[:box_type]))
        if btype <: Box
            etype, lab, _, _ = hs(box)
            eind = add_part!(apx, etype; Dict([lab => val])...)
            box_dict[box] = eind
            push!(mapping[etype], box)
        end
    end

    for (srcport, tgtport, _) in d.tables[:Wire]
        srcbox, tgtbox = d[:out_port_box][srcport], d[:in_port_box][tgtport]
        if !(srcbox in nodes && tgtbox in nodes)
            if srcbox in nodes || tgtbox in nodes
                # true if wire is vert -> hyperedge, false if hyperedge -> vert
                srcnode = srcbox in nodes
                vert, hypedge, hypport, = (srcnode
                                            ? (srcbox, tgtbox, tgtport)
                                            : (tgtbox, srcbox, srcport))

                typ1 = d[:out_port_type][srcport]
                typ2 = d[:in_port_type][tgtport]
                err = "inconsistent ports $srcport ($typ1) -> $tgtport ($typ2)"
                typ1 == typ2 || error(err)
                prevtyp = nodetypes[vert_dict[vert]]
                if !(prevtyp === nothing)
                    prevtyp == typ1 || error("inconsistent types")
                end
                nodetypes[vert_dict[vert]] = typ1

                _, _, ins, outs = hs(hypedge)

                part, porttype, portbtype = (srcnode
                                              ? (ins, :InPort, :in_port_box)
                                              : (outs, :OutPort, :out_port_box))
                boxports = [i for i in 1:nparts(d, porttype)
                            if d[portbtype][i] == hypedge]
                port_ind = findfirst(==(hypport), boxports)

                box_ind = box_dict[hypedge]
                set_subpart!(apx, box_ind, part[port_ind], vert_dict[vert])
            else
            end
        end
    end

    # Assemble structured cospan legs
    indata  = sort([i=>d[:in_port_box][t]  for (i,t,_) in d.tables[:InWire]])
    outdata = sort([i=>d[:out_port_box][t] for (t,i,_) in d.tables[:OutWire]])
    lft = FinFunction(Int[vert_dict[i[2]] for i in indata],n)
    rght = FinFunction(Int[vert_dict[i[2]] for i in outdata],n)

    for (v, c) in [zip(collect(lft), d[:outer_in_port_type])...,
                   zip(collect(rght), d[:outer_out_port_type])...]
        prevtyp = nodetypes[v]
        if !(prevtyp === nothing)
            prevtyp == c || error("inconsistent types")
        end
        nodetypes[v] = c
    end
    set_subpart!(apx, :color, nodetypes)

    # assemble StructuredCospan
    sc = sctype(apx, lft, rght)

    # Copy over apex data to ACSet representing entering s.c. structure
    cset = sccsettype()
    cd, ad = aptype.body.body.parameters[1:2]
    for o in ob(cd)
        add_parts!(cset, o, nparts(apx, o))
    end
    for h in [hom(cd)..., attr(ad)...]
        set_subpart!(cset, h, apx[h])
    end

    # Represent leg data within the acset
    add_parts!(cset, :_I, length(indata))
    add_parts!(cset, :_O, length(outdata))
    set_subpart!(cset, :_i, collect(lft))
    set_subpart!(cset, :_o, collect(rght))

    return sc, cset, vert_dict, mapping  # --- we no longer use this data
end

function cospan_to_wd(csp::ACSet{CD})::WD where{CD}
    obs = ob(CD)
    nin, nout = [nparts(csp, x) for x in [:_I, :_O]]
    intypes, outtypes = [csp[:color][csp[x]] for x in [:_i, :_o]]

    res = WiringDiagram(intypes, outtypes)

    boxdict = Dict()
    for o in obs[2:end-2] # skip V, _I, and _O
        _, o_nin_, o_nout_ = Base.split(string(o), "__")
        o_intypes, o_outtypes = arity = [
            map(Symbol, filter(!isempty, Base.split(x, "_"))) for x in [o_nin_, o_nout_]]
        lab = hypsyms(o_intypes, o_outtypes)[2]
        # arity = o_nin => o_nout
        boxdict[arity] = Int[]
        for j in 1:nparts(csp, o)
            bx = Box(csp[lab][j], o_intypes, o_outtypes)
            push!(boxdict[arity], add_box!(res, bx))
        end
    end

    @assert obs[1] == :V
    for i in 1:nparts(csp, :V)
        v_in  =Tuple{Int, Union{Nothing, Int}}[
                (-inp, nothing) for inp in 1:nin if csp[:_i][inp] == i]
        v_out = Tuple{Int, Union{Nothing, Int}}[
                (-oup, nothing) for oup in 1:nout if csp[:_o][oup] == i]
        for ((o_nin, o_nout), hypboxes) in collect(boxdict)
            _, _, osrc, otgt  = hypsyms(o_nin, o_nout)
            for (hypind, hypbox) in enumerate(hypboxes)
                for (srcport, srcpart) in enumerate(osrc)
                    if csp[srcpart][hypind] == i
                        push!(v_out, (hypbox, srcport))
                    end
                end
                for (tgtort, tgtart) in enumerate(otgt)
                    if csp[tgtart][hypind] == i
                        push!(v_in, (hypbox, tgtort))
                    end
                end
            end
        end
        b = add_box!(res, Junction(csp[:color][i], 1, 1))

        for (_, (v_i, port)) in enumerate(v_in)
            src = v_i < 0 ? (input_id(res),-v_i) : (v_i, port)
            add_wire!(res, src => (b, 1)) # replace 1 w/ indx for distinct ports
        end
        for (_, (v_o, port)) in enumerate(v_out)
            tgt = v_o < 0 ?  (output_id(res),-v_o) : (v_o, port)
            add_wire!(res, (b, 1) => tgt) # see above
        end
    end
    return res
end

function label(wd::WD;
               w::Union{Vector{Pair{Int, String}}, Vector{String}}=String[],
               i::Union{Vector{Pair{Int, String}}, Vector{String}}=String[],
               o::Union{Vector{Pair{Int, String}}, Vector{String}}=String[],
              )::WD

    wd_ = deepcopy(wd)
    d = wd_.diagram
    function to_vec(x::Union{Vector{Pair{Int, String}}, Vector{String}}, s::Symbol)
        return x[1] isa String ? x : [get(Dict(x), i, nothing)
                                   for i in 1:nparts(d, s)]
    end
    set_subpart!(d, :in_port_type, repeat([nothing], nparts(d, :InPort)))
    set_subpart!(d, :out_port_type, repeat([nothing], nparts(d, :OutPort)))
    set_subpart!(d, :outer_in_port_type, repeat([nothing], nparts(d, :InWire)))

    if !isempty(w)
        v = to_vec(w, :Wire)
        for (i, val) in enumerate(v)
            set_subpart!(d, d[:tgt][i], :in_port_type, val)
            set_subpart!(d, d[:src][i], :out_port_type, val)
        end
    end
    if !isempty(o)
        set_subpart!(d, [d[:out_src][i] for i in 1:nparts(d, :OutWire)],
                         :out_port_type, to_vec(o, :OutWire))
    end
    if !isempty(i)
        set_subpart!(d, :outer_in_port_type, to_vec(i, :InWire))
    end
    return wd_
end
