# # Upper Sets
#
# Upper sets are a generalization of subsets to preorders, such that
# the preorder structure is respected.

using Catlab.CategoricalAlgebra.FinSets, Catlab.CategoricalAlgebra
using Test

# ## Power Sets
# We can construct a powerset of a given set by considering all possible subsets.
# This is isomorphic to considering all possible functions into the following set:
#   {"Nope, I'm not in the subset", "Yes, I'm in the subset"}

# Let's represent the subset {1,3} ⊆ {1,2,3}
f13 = FinFunction([2,1,2], FinSet(3), FinSet(2))


"""This function can compute all elements of the power set"""
function powerset(s::FinSet)::Vector{Set{Int}}
  result = [Set{Int}()]  # start with empty subset
  for index in s  # consider subsets that have `index` as a member
    newres = Set{Int}[]
    for res in result
      push!(newres, res ∪ [index])
    end
    append!(result, newres)
  end
  return result
end

for i in 1:5
  @test length(powerset(FinSet(i))) == 2^i
end

# Exercise 1: Create the associated FinFunction to `FinSet(2)` for a particular subset.
function subset_to_map(s::FinSet, subset::Set{Int})::FinFunction
  # TODO
end

# Exercise 2: And create the inverse function
function map_to_subset(f::FinFunction)::Set{Int}
  # TODO
end
###############################################################################
# Answer 1
function subset_to_map(s::FinSet, subset::Set{Int})::FinFunction
  all([0 < i <= s.set for i in subset]) || error("illegal subset")
  return FinFunction([i ∈ subset ? 2 : 1 for i ∈ s], s, FinSet(2))
end

@test subset_to_map(FinSet(3), Set([1,2,3])) == FinFunction([2,2,2])
@test subset_to_map(FinSet(2), Set([2])) == FinFunction([1,2])
@test_throws ErrorException subset_to_map(FinSet(3), Set([4]))
@test_throws ErrorException subset_to_map(FinSet(3), Set([0]))

# Answer 2
function map_to_subset(f::FinFunction)::Set{Int}
  codom(f) == FinSet(2) || error("subset functions must be maps into {yes,no}")
  return Set(findall(==(2), collect(f))) # indices where condition is true
end

@test map_to_subset(FinFunction([2,2,2])) == Set([1,2,3])
@test map_to_subset(FinFunction([1,1,1,1,1,1,1,1], FinSet(2))) == Set{Int}()
@test map_to_subset(FinFunction([1,1,1,1,1,1,1,2])) == Set([8])
@test_throws ErrorException map_to_subset(FinFunction([1,2,3], FinSet(3), FinSet(3)))
###############################################################################

# ## Preorders
# Here we'll represent preorders as relations, i.e. subsets of `S × S`.
# To check whether `a ≤ᵣ b`, we check if `(a,b) ∈ r`.

struct Preorder
  carrier:: FinSet
  relation :: Set{Pair{Int,Int}}
  """Construct valid preorder by taking reflexive/transitive closure"""
  function Preorder(carrier:: FinSet, rel :: Vector{Pair{Int,Int}})
    for (a,b) ∈ rel
      a ∈ carrier && b ∈ carrier || error("relation element not in carrier set")
    end
    relation = Set(rel)
    for (a, b, c) in Iterators.product(carrier, carrier, carrier)
      if ((a=>b) ∈ relation) && ((b=>c) ∈ relation)
        push!(relation, a=>c) # enforces relation is transitive
      end
    end
    for i in carrier
      push!(relation, i=>i) # enforces that relation is reflexive
    end
    return new(carrier, relation)
  end
end

# Example preorders
empty = Preorder(Finset(0), Pair{Int,Int}[])
maybe = Preorder(FinSet(3), [1=>2, 2=>3])
bool = Preorder(FinSet(2), [1=>2])
diamond = Preorder(FinSet(4), [1=>2,1=>3,2=>4,3=>4])
discrete = Preorder(FinSet(4),Pair{Int,Int}[])
full = Preorder(FinSet(4),[1=>2,1=>3,1=>4,2=>1,2=>1,3=>1,4=>1])
preorders = [empty, maybe, bool, diamond, discrete, full]

# Example FinFunctions from 3 -> 2
mmap1 = FinFunction([1,1,2], FinSet(3), FinSet(2))
mmap2 = FinFunction([2,1,2], FinSet(3), FinSet(2))
mmap3 = FinFunction([2,2,2], FinSet(3), FinSet(2))

# ## Monotone maps
# Monotone maps are analogous to functions, but respecting preorder structure.
# x ≤ y ⟹ f(x) ≤ f(y)

struct Monotone_map
  domain::Preorder
  codomain::Preorder
  mapping::FinFunction
  function Monotone_map(domain::Preorder, cod::Preorder, mapping::FinFunction)
    ((dom(mapping) == domain.carrier) && (codom(mapping) == cod.carrier)
    ) || error("mapping mismatch")
    return new(domain,cod,mapping)
  end
end

# Exercise 3: Check if a map is monotone
function is_monotone(mm::Monotone_map)::Bool
  # todo
end

# Exercise 4: write a function to compose monotone maps
function compose(m1::Monotone_map, m2::Monotone_map)::Monotone_map
  # TODO
end

# Exercise 5: Enumerate monotone maps to bool by filtering powerset maps to 2
function monotone_maps_to_bool(p::Preorder)::Vector{Monotone_map}
  pset_maps = ["""TODO""" for s in powerset(p.carrier)]
  return """TODO"""
end

# Exercise 6: Enumerate upper sets
function uppersets(s::Preorder)::Vector{Set{Int}}
  result = Set([Set{Int}()]) # Start with an initial upper set
  for index in s.carrier # consider upper sets that have `index` as a member
    newres = Set{Set{Int}}()
    for res in result
        # in `powerset`, we pushed `res ∪ [index]`.
        # What else are we obligated to do for this to be an upper set?
        push!(newres, """TODO""")
    end
    union!(result, newres)
  end
  return collect(result)
end

###############################################################################

# Answer 3
function is_monotone(mm::Monotone_map)::Bool
  all([(mm.mapping(a) => mm.mapping(b)) ∈ mm.codomain.relation
       for (a,b) ∈ mm.domain.relation])
end

@test is_monotone(Monotone_map(maybe, bool, mmap1))
@test !is_monotone(Monotone_map(maybe, bool, mmap2))
@test is_monotone(Monotone_map(maybe, bool, mmap3))

# Answer 4
function compose(m1::Monotone_map, m2::Monotone_map)::Monotone_map
  return Monotone_map(m1.domain, m2.codomain, compose(m1.mapping, m2.mapping))
end

# Answer 5
function monotone_maps_to_bool(p::Preorder)::Vector{Monotone_map}
  pset_maps = [Monotone_map(p, bool, subset_to_map(p.carrier, s))
               for s in powerset(p.carrier)]
  return filter(is_monotone, pset_maps)
end

# Answer 6
function uppersets(s::Preorder)::Vector{Set{Int}}
  result = Set([Set{Int}()]) # start with one empty list of integers
  for index in s.carrier
    newres = Set{Set{Int}}()
    for res in result
        if index ∉ res # be efficient
          push!(newres, res ∪ [j for (i,j) ∈ s.relation if i==index])
        end
    end
    union!(result, newres)
  end
  return collect(result)
end

# Monotone maps to bool are in bijection with upper sets for all preorders
for p in preorders
  @test length(uppersets(p)) == length(monotone_maps_to_bool(p))
end
