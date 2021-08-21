using Catlab.WiringDiagrams.DirectedWiringDiagrams: WiringDiagramACSet
using Catlab.CategoricalAlgebra
using Catlab.WiringDiagrams

d = @acset WiringDiagramACSet{Any, Any, Any, DataType} begin
    Box = 3
    InPort = 5
    OutPort = 3
    OuterInPort = 3
    OuterOutPort = 1
    Wire = 1
    InWire = 3
    OutWire = 1
    PassWire = 0
    src  = [1]
    tgt= [4]
    in_src  = [2, 3, 1]
    in_tgt  = [1, 2, 3]
    out_src  = [2]
    out_tgt = [1]
    pass_src = Int64[]
    pass_tgt  = Int64[]
    in_port_box  = [1, 1, 2, 2, 3]
    out_port_box  = [1, 2, 3]
    in_port_type = Any[:X, :X, :X, :X, :X]
    out_port_type = Any[:X, :X, :X]
    outer_in_port_type  = Any[:X, :X, :X]
    outer_out_port_type  = Any[:X]
    value  = Any[:mul, :mul, :X]
    box_type = DataType[Box{Symbol}, Box{Symbol}, Junction{Nothing, Symbol}]
    wire_value  = Any[nothing]
    in_wire_value  = Any[nothing, nothing, nothing]
    out_wire_value = Any[nothing]
    pass_wire_value= Any[]
end

add_part!(d, :InWire, in_src=2,in_tgt=5, in_wire_value=nothing)

d2 = @acset WiringDiagramACSet{Any, Any, Any, DataType} begin
  Box = 3
  InPort = 1
  OutPort = 3
  OuterInPort = 0
  OuterOutPort = 2
  Wire = 0
  InWire = 0
  OutWire = 2
  PassWire = 0
  src = Int64[]
  tgt  = Int64[]
  in_src  = Int64[]
  in_tgt  = Int64[]
  out_src  = [1, 2]
  out_tgt = [1, 2]
  pass_src  = Int64[]
  pass_tgt = Int64[]
  in_port_box  = [3]
  out_port_box = [1, 2, 3]
  in_port_type  = Any[:X]
  out_port_type  = Any[:X, :X, :X]
  outer_in_port_type  = Any[]
  outer_out_port_type = Any[:X, :X]
  value = Any[:e, :e, :X]
  box_type  = DataType[Box{Symbol}, Box{Symbol}, Junction{Nothing, Symbol}]
  wire_value = Any[]
  in_wire_value = Any[]
  out_wire_value= Any[nothing, nothing]
  pass_wire_value  = Any[]
end

  add_part!(d2, :OutWire, out_src=3,out_tgt=1, out_wire_value=nothing)