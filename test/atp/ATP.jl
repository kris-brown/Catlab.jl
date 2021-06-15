include("/Users/ksb/Catlab.jl/src/atp/ATP.jl");
using Catlab.CategoricalAlgebra


# Possible generators for a theory of monoids
mmul = Box(:mul, Two, One);
e = Box(:e, Zero, One);

# Relation
R = Box(:R, One, One);
f = Box(:f, One, One);
g = Box(:g, One, One);

Σ = Set([mmul, e, R]);
# I = Set([leftid, rightid])

R_copy = WiringDiagram(One, Two);
r, cpy = add_box!(R_copy, R), add_box!(R_copy, δ);
add_wires!(R_copy, Pair[
    (input_id(R_copy), 1) => (r, 1),
    (r, 1) => (cpy, 1),
    (cpy, 1) => (output_id(R_copy), 1),
    (cpy, 2) => (output_id(R_copy), 2)]);

fig26 = WiringDiagram(One, Two);
cpy,f1,g1,f2,g2 = [add_box!(fig26, x) for x in [δ, f, g, f, g]];
add_wires!(fig26, Pair[
    (input_id(fig26), 1) => (cpy, 1),
    (cpy, 1) => (f1, 1),
    (cpy, 2) => (f2, 1),
    (f1, 1) => (g1, 1),
    (f2, 1) => (g2, 1),
    (g1, 1) => (output_id(fig26), 1),
    (g2, 1) => (output_id(fig26), 2)]);

ex211 = WiringDiagram(Six, Five)
b01,b02,b03,b04,b11,b12,b21,b22,b23 = [add_box!(ex211, x) for x in [μ,μ,μ,δ, η,ϵ,μ,δ,δ]];
add_wires!(ex211, Pair[
    (input_id(ex211), 1) => (b02, 1),
    (input_id(ex211), 2) => (b01, 1),
    (input_id(ex211), 3) => (b01, 2),
    (input_id(ex211), 4) => (b03, 2),
    (input_id(ex211), 5) => (b21, 2),
    (input_id(ex211), 6) => (b21, 1),
    (b01, 1) => (b02, 2),
    (b02, 1) => (b03, 1),
    (b03, 1) => (b04, 1),
    (b11, 1) => (b12, 1),
    (b21, 1) => (b22, 1),
    (b22, 2) => (b23, 1),
    (b04,1) => (output_id(ex211), 1),
    (b04,2) => (output_id(ex211), 2),
    (b22,1) => (output_id(ex211), 3),
    (b23,1) => (output_id(ex211), 4),
    (b23,2) => (output_id(ex211), 5)]);
ex211b = WiringDiagram(Five, Four)
b1, b2, b3, b4 = [add_box!(ex211b, x) for x in [dot, μ,dot, dot]];
add_wires!(ex211b, Pair[
    (input_id(ex211b), 1) => (b1, 1),
    (input_id(ex211b), 2) => (b2, 1),
    (input_id(ex211b), 3) => (b2, 2),
    (input_id(ex211b), 4) => (b3, 1),
    (input_id(ex211b), 5) => (b4, 1),
    (b1,1) => (output_id(ex211b), 1),
    (b2,1) => (output_id(ex211b), 2),
    (b3,1) => (output_id(ex211b), 3),
    (b4,1) => (output_id(ex211b), 4)])



Σ0 = Set{Box{Symbol}}()
Σ = Set([e, mmul, R]);


sigma_to_hyptype(Σ);

wd_pad!(R_copy);

csp = wd_to_cospan(R_copy, Σ);

csp = wd_to_cospan(fig26, Set([f,g]));


csp211 = wd_to_cospan(ex211, Σ0);
csp211b = wd_to_cospan(ex211b, Σ0);
csp211_comp = compose(csp211, csp211b);
