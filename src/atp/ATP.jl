using Catlab.WiringDiagrams
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra.StructuredCospans
using Catlab.Present: translate_generator
using Catlab.CategoricalAlgebra.FinSets
using Catlab.Theories: attr, adom
using Catlab.CategoricalAlgebra.DPO

using DataStructures: IntDisjointSets

"""
Apply equality as a rewrite rule
"""
function apply_eq(sc_cset::ACSet, Σ::Set{Box{Symbol}},
                  rule::Pair{WiringDiagram{Any,Any,Any,Any},
                             WiringDiagram{Any,Any,Any,Any}},
                  forward::Bool=true) where {L}
    l, r = forward ? (rule[1], rule[2]) : (rule[2], rule[1])
    pat = wd_to_cospan(l, Σ)[2]
    rem_IO!(pat)
    m = homomorphism(pat, sc_cset)
    L_ = id(pat)
    R_ = wd_to_cospan(branch2(l, r), Σ)[2]
    Rs = homomorphisms(pat, R_)
    @assert length(Rs) == 1
    R = Rs[1] # this should be done cleaner
    @assert dom(L_) == dom(R)
    new_apex = rewrite_match(L_, R, m)
    return new_apex
end

function rem_IO!(sc_cset::ACSet)::Nothing
    rem_parts!(sc_cset, :_I, 1:nparts(sc_cset,:_I))
    rem_parts!(sc_cset, :_O, 1:nparts(sc_cset,:_O))
end

function branch(Σ, l::WiringDiagram, r::WiringDiagram)::ACSetTransformation
    aptype, _, _, _ = sigma_to_hyptype(Σ);
    cd, ad = aptype.body.body.parameters[1:2]
    _, lcset = wd_to_cospan(l, Σ);
    l_i, l_o = [deepcopy(lcset[x]) for x in [:_i,:_o]]
    rem_IO!(lcset)

    comps = Dict([o=>collect(1:nparts(lcset, o)) for o in ob(cd)])
    R = deepcopy(lcset);
    _, rcset = wd_to_cospan(r, Σ);
    r_i, r_o = [deepcopy(rcset[x]) for x in [:_i,:_o]]
    newinds = Dict{Symbol, Vector{Int}}([:V=>Int[]])
    for o in filter(!=(:V), ob(cd))
        newinds[o] = add_parts!(R, o, nparts(rcset, o))
    end

    for i in 1:nparts(rcset, :V)
        leftind  = findfirst(==(i), r_i)
        rightind = findfirst(==(i), r_o)
        if !(leftind===nothing)
            push!(newinds[:V], l_i[leftind])
        elseif !(rightind===nothing)
            push!(newinds[:V], l_o[rightind])
        else
            push!(newinds[:V], add_part!(R, :V))
        end
    end
    for (src, tgt, h) in zip(dom(cd), codom(cd), hom(cd))
        srcsym, tgtsym = ob(cd)[src], ob(cd)[tgt]
        set_subpart!(R, newinds[srcsym], h, newinds[tgtsym][rcset[h]])
    end
    for (src, h) in zip(adom(ad),attr(ad))
        srcsym = ob(cd)[src]
        set_subpart!(R, newinds[srcsym], h, rcset[h])
    end
    return ACSetTransformation(deepcopy(lcset), R; comps...)
end

function branch2(l::WiringDiagram, r::WiringDiagram)::WiringDiagram
    ld, rd = l.diagram, r.diagram
    nin, nout = [nparts(ld, x) for x in [:OuterInPort, :OuterOutPort]]
    res = WiringDiagram([nothing for _ in 1:nin],
                        [nothing for _ in 1:nout])
    inboxes = [add_box!(res, δ) for _ in 1:nin]
    outboxes = [add_box!(res, μ) for _ in 1:nin]
    subbox = Box([nothing for _ in 1:nin], [nothing for _ in 1:nout])
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
    return ocompose(res, [repeat([δsd], nin)...,repeat([μsd], nout)..., l, r])
end

"""
Prove an inequality in a relational theory
Return homomorphism as witness, if any
Takes in wiring diagram csets c1 and c2
"""
function prove(rt, c1, c2)::Union{Nothing, Any}
    Σ, I = rt
    csp1 = sd_to_cospan(c1, Σ)
    csp2 = sd_to_cospan(c2, Σ)
    d1 = apex(csp1)
    d2 = apex(csp2)
    # TODO: color d1 and d2 w/ interface data
    # As we want a COSPAN morphism of csp2->csp1
    for _ in 1:5
        h = homomorphism(d2, d1)
        if !(h===nothing)
            return h
        else
            for i in I
                apply_eq(d1, i)
            end
        end
    end
    return nothing
end

# Tests

Zero, One, Two, Three, Four, Five, Six = [collect(repeat([nothing], n)) for n in 0:6]
ϵ, η, δ, μ, dot = [Box(nothing, x, y) for (x, y) in
    [(One, Zero), (Zero, One), (One, Two), (Two, One), (One, One)]]

# Generators for special commutative Frobenius algebra
scfa = [ϵ, η, δ, μ]
δsd, μsd = WiringDiagram(One, Two), WiringDiagram(Two, One)
add_box!(δsd, δ)
add_box!(μsd, μ)
add_wires!(δsd, Pair[
    (input_id(δsd), 1) => (1,1),
    (1,1) => (output_id(δsd), 1),
    (1,2) => (output_id(δsd), 2)])
add_wires!(μsd, Pair[
    (input_id(μsd), 1) => (1,1),
    (input_id(μsd), 2) => (1,2),
    (1,1) => (output_id(μsd), 1)])

"""
Given a signature, create an OpenCSetType for hypergraphs
including a distinct hyperedge for each arity.

Also return a specific ACSet HΣ for the signature, to be
in making a slice category.
"""
function sigma_to_hyptype(Σ::Set{Box{Symbol}})
    arities = Dict{Pair{Int}, Set{Symbol}}()
    for op in Σ
        ar = length(op.input_ports) => length(op.output_ports)
        if haskey(arities, ar)
            push!(arities[ar], op.value)
        else
            arities[ar] = Set([op.value])
        end
    end
    pres = Presentation(FreeSchema)
    name = FreeSchema.Data{:generator}([:Name], [])
    add_generator!(pres, name)
    obsyms = vcat([:V], [Symbol("E_$(i)_$j") for (i, j) in keys(arities)])
    xobs = [Ob(FreeSchema, s) for s in obsyms]

    for x in xobs
        add_generator!(pres, x)
    end

    v = xobs[1]
    for (n, (i, o)) in enumerate(keys(arities))
        x = xobs[n+1]
        add_generator!(pres, FreeSchema.Attr{:generator}([Symbol("l_$(i)_$o"), x, name], [x, name]))

        for i_ind in 1:i
            add_generator!(pres, Hom(Symbol("s_$(i)_$(o)_$i_ind"), x, v))
        end
        for o_ind in 1:o
            add_generator!(pres, Hom(Symbol("t_$(i)_$(o)_$o_ind"), x, v))
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

function hypsyms(i::Int, j::Int)::Tuple{Symbol, Symbol, Vector{Symbol}, Vector{Symbol}}
    ename = Symbol("E_$(i)_$j")
    lab = Symbol("l_$(i)_$j")
    src = [Symbol("s_$(i)_$(j)_$i_ind") for i_ind in 1:i]
    tgt = [Symbol("t_$(i)_$(j)_$j_ind") for j_ind in 1:j]
    return ename, lab, src, tgt
end


"""
Add a empty node between each generator and the outerbox
and a node between each generator
"""
function wd_pad!(sd)::Nothing
    d = sd.diagram
    in_delete, out_delete = Set{Int}(), Set{Int}()
    extwires = [:InWire, :OutWire]
    portboxes = [:in_port_box, :out_port_box]
    deletes = [in_delete, out_delete]
    extsrctgt = [(:in_src, :in_tgt), (:out_src, :out_tgt)]
    for (portbox, extwire, delset, (extsrc, exttgt), out) in zip(portboxes, extwires, deletes, extsrctgt, [false, true])
        for (ow, (os, ot, _)) in enumerate(d.tables[extwire])
            if !(d[:value][d[portbox][os]] === nothing)
                newbox = add_part!(d, :Box, value=nothing, box_type=Box{Nothing})
                new_in = add_part!(d, :InPort, in_port_box=newbox, in_port_type=nothing)
                new_out = add_part!(d, :OutPort, out_port_box=newbox, out_port_type=nothing)
                xsrc, xtgt, src, tgt = out ? (new_out, ot, os, new_in) : (os, new_in, new_out, ot)
                add_part!(d, extwire; Dict([extsrc => xsrc, exttgt => xtgt])...)
                add_part!(d, :Wire, src=src, tgt=tgt, wire_value=nothing)
                push!(delset, ow)
            end
        end
    end
    w_delete = Set{Int}()
    for (w, (s_port, t_port, _)) in enumerate(d.tables[:Wire])
        s_box = d[:out_port_box][s_port]
        t_box = d[:in_port_box][t_port]
        if !(d[:value][s_box] === nothing ||  d[:value][t_box] === nothing)
            newbox = add_part!(d, :Box, value=nothing, box_type=Box{Nothing})
            new_in = add_part!(d, :InPort, in_port_box=newbox, in_port_type=nothing)
            new_out = add_part!(d, :OutPort, out_port_box=newbox, out_port_type=nothing)
            add_part!(d, :Wire, src=s_port, tgt=new_in, wire_value=nothing)
            add_part!(d, :Wire, src=new_out, tgt=t_port, wire_value=nothing)
            push!(w_delete, w)
        end
    end
    # no FKs point to a wire, so we can freely delete them
    rem_parts!(d, :Wire, sort(collect(w_delete)))
    rem_parts!(d, :InWire, sort(collect(in_delete)))
    rem_parts!(d, :OutWire, sort(collect(out_delete)))
end

"""
Convert wiring diagram to cospan
All components connected by Frobenius generators are condensed
together.
"""
function wd_to_cospan(sd, Σ::Set{Box{Symbol}})
    wd_pad!(sd)
    d = sd.diagram
    aptype, _, sctype, sccsettype = sigma_to_hyptype(Σ)

    nodes = [i for (i, v) in enumerate(d[:value]) if v===nothing]
    conn_comps = IntDisjointSets(nparts(d, :Box))
    for (srcport, tgtport, _) in d.tables[:Wire]
        srcbox, tgtbox = d[:out_port_box][srcport], d[:in_port_box][tgtport]
        if srcbox in nodes && tgtbox in nodes
            union!(conn_comps, srcbox, tgtbox)
        end
    end
    hs = i -> hypsyms(length(inneighbors(sd, i)), length(outneighbors(sd, i)))
    n = conn_comps.ngroups - (nparts(d, :Box) - length(nodes))
    cclist = sort(collect(Set([conn_comps.parents[i] for i in nodes])))
    vert_dict = Dict([i=>findfirst(==(conn_comps.parents[i]), cclist) for i in nodes])

    apx = aptype()
    add_parts!(apx, :V, n)
    box_dict = Dict{Int,Int}()
    for (box, val) in enumerate(d[:value])
        if !(val===nothing)
            etype, lab, _, _ = hs(box)
            eind = add_part!(apx, etype; Dict([lab => val])...)
            box_dict[box] = eind
        end
    end

    for (srcport, tgtport, _) in d.tables[:Wire]
        srcbox, tgtbox = d[:out_port_box][srcport], d[:in_port_box][tgtport]
        if !(srcbox in nodes && tgtbox in nodes)
            if srcbox in nodes || tgtbox in nodes
                vert, hypedge = srcbox in nodes ? (srcbox, tgtbox) : (tgtbox, srcbox)
                _, _, ins, outs = hs(hypedge)
                box_ind = box_dict[hypedge]
                part = srcbox in nodes ? ins : outs
                boxports = (srcbox in nodes ? inneighbors(sd, hypedge)
                                         : outneighbors(sd, hypedge))
                port_ind = findfirst(==(vert), boxports)
                set_subpart!(apx, box_ind, part[port_ind], vert_dict[vert])
            else
            end
        end
    end

    indata = sort([i=>d[:in_port_box][t] for (i,t,_) in d.tables[:InWire]]) # (InSrc,InTgt)
    outdata = sort([i=>d[:out_port_box][t] for (t,i,_) in d.tables[:OutWire]]) # (InSrc,InTgt)
    lft = FinFunction([vert_dict[i[2]] for i in indata],n)
    rght = FinFunction([vert_dict[i[2]] for i in outdata],n)
    sc = sctype(apx, lft, rght)

    cset = sccsettype()
    cd, ad = aptype.body.body.parameters[1:2]
    for o in ob(cd)
        add_parts!(cset, o, nparts(apx, o))
    end
    for h in [hom(cd)..., attr(ad)...]
        set_subpart!(cset, h, apx[h])
    end
    add_parts!(cset, :_I, length(indata))
    add_parts!(cset, :_O, length(outdata))
    set_subpart!(cset, :_i, collect(lft))
    set_subpart!(cset, :_o, collect(rght))

    return sc, cset
end

