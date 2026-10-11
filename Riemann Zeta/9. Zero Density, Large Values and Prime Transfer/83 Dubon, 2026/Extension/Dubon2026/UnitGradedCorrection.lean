import Dubon2026.ScalarQuotientInvariantLift
import Mathlib.Algebra.Group.TypeTags.Basic

/-! # Actual one-step unit corrections from an equivariant graded map -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped BigOperators

variable {R G U : Type} [CommRing R] [Group G] [CommGroup U]
  [MulDistribMulAction G U] (A : Rep R G) (f : Additive U →+ A)
  (hf : ∀ (g : G) (u : U), f (Additive.ofMul (g • u)) = A.ρ g (f (Additive.ofMul u)))

include hf in
/-- An original multiplicative one-cocycle maps to an actual additive
one-cocycle in the displayed equivariant quotient. -/
theorem unitGradedMap_mem_cocycles (c : G → U)
    (hc : ∀ g h, c (g * h) = (g • c h) * c g) :
    (fun g => f (Additive.ofMul (c g))) ∈ groupCohomology.cocycles₁ A := by
  apply (groupCohomology.mem_cocycles₁_iff _).mpr
  intro g h
  rw [hc, ofMul_mul, map_add, hf]

include hf in
/-- Surjectivity of the actual graded map and vanishing of its first
cohomology supply an original unit coboundary correction whose remaining
cocycle takes values in the literal kernel of that same map. -/
theorem unitGraded_cocycle_correction (hsurj : Function.Surjective f)
    (hA : Limits.IsZero (groupCohomology A 1)) (c : G → U)
    (hc : ∀ g h, c (g * h) = (g • c h) * c g) :
    ∃ u : U, ∀ g, f (Additive.ofMul (c g / ((g • u) / u))) = 0 := by
  obtain ⟨x, hx⟩ := representation_one_cocycle_coboundary_of_isZero A hA
    ⟨fun g => f (Additive.ofMul (c g)), unitGradedMap_mem_cocycles A f hf c hc⟩
  obtain ⟨v, hv⟩ := hsurj x
  refine ⟨Additive.toMul v, fun g => ?_⟩
  rw [ofMul_div, ofMul_div, map_sub, map_sub, hf]
  change f (Additive.ofMul (c g)) - (A.ρ g (f v) - f v) = 0
  rw [hv, hx]
  exact sub_self _

include hf in
/-- The actual product of acted-on original units maps to the genuine sum
of their original quotient actions. -/
theorem unitGradedMap_norm [Fintype G] (u : U) :
    f (Additive.ofMul (∏ g : G, g • u)) = ∑ g : G, A.ρ g (f (Additive.ofMul u)) := by
  classical
  have he : Additive.ofMul (∏ g : G, g • u) = ∑ g : G, Additive.ofMul (g • u) := by
    exact ofMul_prod Finset.univ _
  rw [he, map_sum]
  exact Finset.sum_congr rfl (fun g _ => hf g u)

include hf in
/-- A genuine invariant original unit admits an original norm correction
whose remaining error lies in the exact kernel of the graded map. -/
theorem unitGraded_norm_correction [Fintype G] (hsurj : Function.Surjective f)
    (hNorm : ∀ a : A, (∀ g, A.ρ g a = a) → ∃ x : A, ∑ g : G, A.ρ g x = a)
    (u : U) (hu : ∀ g : G, g • u = u) :
    ∃ v : U, f (Additive.ofMul (u / ∏ g : G, g • v)) = 0 := by
  have hi : ∀ g, A.ρ g (f (Additive.ofMul u)) = f (Additive.ofMul u) := by
    intro g
    rw [← hf, hu]
  obtain ⟨x, hx⟩ := hNorm (f (Additive.ofMul u)) hi
  obtain ⟨v, hv⟩ := hsurj x
  refine ⟨Additive.toMul v, ?_⟩
  rw [ofMul_div, map_sub, unitGradedMap_norm A f hf]
  change f (Additive.ofMul u) - (∑ g : G, A.ρ g (f v)) = 0
  rw [hv, hx, sub_self]

end
end Dubon2026
