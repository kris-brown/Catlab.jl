
include("/Users/ksb/Catlab.jl/test/atp/WD.jl")

using Test

##########################################
if 1+1==1
    idxxid_sc = wd_to_cospan(idxxid, Σ_monoid)[2];
    xx_hg     = wd_to_cospan(xx, Σ_monoid)[2];
    rw1 = apply_eq(idxxid_sc, T_monoid, :leftid);
    rw2 = apply_eq(rw1,       T_monoid, :rightid);

    @test !csp_homomorphic(xx_hg, idxxid_sc) # not yet
    @test !csp_homomorphic(xx_hg, rw1) # not yet
    @test csp_homomorphic(xx_hg, rw2) # prove after applying leftid AND rightid

    proveresult = prove(T_monoid, idxxid, xx, oriented=true)
    @test !(proveresult === nothing)
end
