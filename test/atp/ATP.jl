
include("/Users/ksb/Catlab.jl/test/atp/WD.jl")

using Test

if 1+1==0
# idxxid = @program C (x::X) let y=e(); mul(mul(y, x), mul(x, y)) end
# xx = @program C (x::X) mul(x, x) # final result
# pr, res, m, r2 = prove(T_monoid, idxxid, xx; maxi=4)


xnyymx = trim(@program(C, (x::X,n::X,m::X),
              let nx = mul(n,x); (nx,[mul(nx,m),x]) end), 1,1)
s = [:e_intro, :sym, :mul_assoc, :cancel, :pos, :leftid]
h, newres, r, r2 = prove(T_pcs_mon, xnyymx, passx; strat=seq([[ss] for ss in s]), maxi=length(s))
end
