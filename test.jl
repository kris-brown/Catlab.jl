using Revise, Test
using Catlab
using Catlab.CategoricalAlgebra, Catlab.Present, Catlab.Theories
using Catlab.Graphs.BasicGraphs: TheoryGraph, AbstractGraph
import Catlab.CategoricalAlgebra: colimit

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


# function colimit(::Type{Tuple{Y, LooseACSetTransformation{T}, Z}},
#                  ::Multispan) where {Y,T,Z}
#     println("Y=$Y\nT=$T")
#     return 1
# end

#pushout(abc,abd)

@present TheoryLabeledGraph <: TheoryGraph begin
  (VLabel, ELabel)::AttrType
  vlabel::Attr(V,VLabel)
  elabel::Attr(E,ELabel)
end
@acset_type LabeledGraph(TheoryLabeledGraph, index=[:src,:tgt]) <: AbstractGraph
const LG = LabeledGraph{Bool, Int}
const LGvar = LabeledGraph{Bool, Var}
const LGx = LabeledGraph{Bool, Expr}


function rewrite_var(L::ACSetTransformation,R::ACSetTransformation, G::StructACSet;monic::Bool=false)
  m = homomorphism(codom(L),G; monic=true)
  vars = get_vars(codom(L), dom(m))
  L_ = sub_vars(L, G, vars)
  R_ = sub_vars(R, G, vars)
  is_natural(L_) || error("L $L_")
  all([typeof(dom(x))==typeof(codom(x)) for x in [L_,R_,m]]) || error("")
  is_natural(R_) || error("R $R_")
  is_natural(m) || error("m $m")
  can_pushout_complement(L_,m) || error("L_ $L_ m_ $m_")
  rewrite_match(L_,R_,m)
end


l = @acset LGvar begin V=2; E=2; src=[1,1]; tgt=[2,2];
  vlabel=[false,false];elabel=[Var(:a), Var(:a)] end

r = @acset LGvar begin V=2; E=1; src=[1]; tgt=[2];
   vlabel=[false,false];elabel=[Var(:a)] end
L = homomorphism(r,l); R = id(r)
G = @acset LG begin V=3; E=4; src=[1,1,1,1]; tgt=[2,2,2,3];
vlabel=[false,false,false]; elabel=[2,3,2,2] end
res = rewrite_var(L, R, G)


l = @acset LGvar begin V=2; E=2; src=[1,1]; tgt=[2,2];
  vlabel=[false,false];elabel=[Var(:a), Var(:b)] end
i = @acset LGvar begin V=2;vlabel=[false,false] end
r = @acset LGx begin V=2; E=1; src=[1]; tgt=[2];
   vlabel=[false,false];elabel=[:(Var(:a)+Var(:b))] end
L = homomorphism(i,l;monic=true); R = homomorphism(i,r;monic=true)
G = @acset LG begin V=3; E=4; src=[1,1,1,1]; tgt=[2,2,2,3];
vlabel=[false,false,false]; elabel=[2,3,2,2] end

res = rewrite_var(L, R, G)
