using Catlab.WiringDiagrams
using Catlab.Present
using Catlab.Theories
using Catlab.CategoricalAlgebra.CSets
using Catlab.CategoricalAlgebra.StructuredCospans
using Catlab.Present: translate_generator
using Catlab.CategoricalAlgebra.FinSets

using DataStructures: IntDisjointSets

"""
Apply inequality as a rewrite rule
"""
function apply_ineq(sd, ineq)
end

"""
Prove an inequality in a relational theory
Return homomorphism as witness, if any
Takes in wiring diagram csets c1 and c2
"""
function prove(rt, c1,c2)::Union{Nothing, Any}
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
    return acst{Symbol}, obtype{Symbol}, sctype{Symbol}
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

    # for (ow, (os, ot, _)) in enumerate(d.tables[:OutWire])
    #     if !(d[:value][d[:out_port_box][os]] === nothing)
    #         newbox = add_part!(d, :Box, value=nothing, box_type=Box{Nothing})
    #         new_in = add_part!(d, :InPort, in_port_box=newbox, in_port_type=nothing)
    #         new_out = add_part!(d, :OutPort, out_port_box=newbox, out_port_type=nothing)
    #         add_part!(d, :OutWire, out_src=new_out, out_tgt=ot)
    #         add_part!(d, :Wire, src=os, tgt=new_in, wire_value=nothing)
    #         push!(out_delete, ow)
    #     end
    # end
    # for (iw, (is, it, _)) in enumerate(d.tables[:InWire])
    #     if !(d[:value][d[:in_port_box][it]] === nothing)
    #         newbox = add_part!(d, :Box, value=nothing, box_type=Box{Nothing})
    #         new_in = add_part!(d, :InPort, in_port_box=newbox, in_port_type=nothing)
    #         new_out = add_part!(d, :OutPort, out_port_box=newbox, out_port_type=nothing)
    #         add_part!(d, :InWire, in_src=is, in_tgt=new_in)
    #         add_part!(d, :Wire, src=new_out, tgt=it, wire_value=nothing)
    #         push!(in_delete, iw)
    #     end
    # end
    # no FKs point to a wire, so we can freely delete them
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
    aptype, _, sctype = sigma_to_hyptype(Σ)

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
    return sctype(apx, lft, rght)
end

