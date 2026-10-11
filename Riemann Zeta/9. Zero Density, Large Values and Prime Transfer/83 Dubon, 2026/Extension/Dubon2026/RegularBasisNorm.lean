import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-! # The actual action norm for a regularly permuted basis -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G] [Fintype G]
  (A : Rep.{0} R G) (b : Module.Basis G R A)
  (hb : ∀ g h, A.ρ g (b h) = b (g * h))

include hb in
omit [Fintype G] in
/-- The actual coefficient of an acted-on vector is its original coefficient
at the inverse-translated basis index. -/
theorem regularBasis_action_coordinate (g h : G) (a : A) :
    b.repr (A.ρ g a) h = b.repr a (g⁻¹ * h) := by
  classical
  have he : (b.coord h).comp (A.ρ g) = b.coord (g⁻¹ * h) := by
    apply b.ext
    intro t
    have ht : g * t = h ↔ t = g⁻¹ * h := eq_inv_mul_iff_mul_eq.symm
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, hb,
      Module.Basis.repr_self, Finsupp.single_apply, ht]
  exact LinearMap.congr_fun he a

include hb in
/-- Every original invariant vector is the actual full action norm of one
original basis vector multiplied by its identity coordinate. This proves the
degree-zero Tate norm quotient vanishes for this regular basis. -/
theorem regularBasis_invariant_mem_norm
    (a : A) (ha : ∀ g, A.ρ g a = a) :
    ∃ x : A, ∑ g : G, A.ρ g x = a := by
  classical
  have hc (g : G) : b.repr a g = b.repr a 1 := by
    have h := regularBasis_action_coordinate A b hb g g a
    simpa only [ha, inv_mul_cancel] using h
  refine ⟨b.repr a 1 • b 1, ?_⟩
  calc
    ∑ g : G, A.ρ g (b.repr a 1 • b 1) = ∑ g : G, b.repr a 1 • b g := by
      simp only [map_smul, hb, mul_one]
    _ = ∑ g : G, b.repr a g • b g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hc g]
    _ = a := b.sum_repr a

end
end Dubon2026
