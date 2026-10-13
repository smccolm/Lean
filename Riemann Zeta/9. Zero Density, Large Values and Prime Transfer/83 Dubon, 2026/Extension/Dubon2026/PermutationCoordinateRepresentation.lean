import Dubon2026.RegularBasisCohomology

/-! # The original permutation basis in coordinate representations

The displayed permutation basis becomes the inverse-coordinate action
on actual functions on the same indexing set. This is the entry bridge
from DUB-17's constructed integral S-unit sublattice to the orbit and
stabilizer cohomology calculation using the existing Shapiro theorem.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]

/-- The actual inverse-coordinate permutation representation on functions on the original indexing set. -/
def permutationCoordinateRep : Rep R G := Rep.of {
  toFun := fun g => LinearMap.funLeft R R (fun i : ι => g⁻¹ • i)
  map_one' := by ext x i; simp
  map_mul' := by intro g h; ext x i; simp [mul_smul] }

/-- The coordinate action evaluates at the actual inverse translate. -/
theorem permutationCoordinateRep_apply (g : G) (x : ι → R) (i : ι) :
    (permutationCoordinateRep R G ι).ρ g x i = x (g⁻¹ • i) := rfl

variable [Fintype ι] (A : Rep R G) (b : Module.Basis ι R A)
  (hb : ∀ g i, A.ρ g (b i) = b (g • i))

/-- The original displayed permuted basis gives an actual isomorphism with the original coordinate permutation representation. -/
def permutationBasisCoordinateIso : A ≅ permutationCoordinateRep R G ι := by
  classical
  apply Rep.mkIso
  refine Representation.Equiv.mk b.equivFun ?_
  intro g
  apply b.ext
  intro i
  funext j
  change b.repr (A.ρ g (b i)) j = b.repr (b i) (g⁻¹ • j)
  rw [hb]
  have he : g • i = j ↔ i = g⁻¹ • j := eq_inv_smul_iff.symm
  simp only [Module.Basis.repr_self, Finsupp.single_apply, he]

end
end Dubon2026
