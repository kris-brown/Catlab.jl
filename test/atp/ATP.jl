
include("/Users/ksb/Catlab.jl/test/atp/WD.jl")

using Test

##########################################
if 1+1==2
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

# uniqueness of identity


# proveresult = prove(T_monoid, e_uniq_1, e_uniq_2,
#                     oriented=true);

# @test !(proveresult === nothing)

################################################################################





# Dihedral groups



# from this prove (sr)²=1
#T_d3h_pres1 = add_eq(T_d3h, Eq(:srsinv_rinv, srs,  rinv, true))
# from this prove srs⁻¹ = r⁻¹
#T_d3h_pres2 = add_eq(T_d3h, Eq(:sr2_1, sr2, e_wd, true))

##########################################
# Relation



##########################################
# Empty theory

# csp211 = wd_to_cospan(ex211, Σ0)[1];
# csp211b = wd_to_cospan(ex211b, Σ0)[1];
# csp211_comp = compose(csp211, csp211b);