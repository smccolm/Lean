import Dubon2026.SourceOriginalWeilClasses
import Dubon2026.SourceOriginalRegularFinite

/-! DUB-17/18 -> original Weil pairing descent -> independence of
principal function choices. Reuse the actual global-regular-function theorem
to identify a quotient with zero orders as a base constant. Such a constant
evaluates to one on a degree-zero divisor. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
open scoped Classical BigOperators
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

theorem original_constant_of_orders_zero (f : modularFunctionFieldOver N L)
    (h : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = 0) :
    ∃ c : L, f = algebraMap L (modularFunctionFieldOver N L) c := by
  have hm : f ∈ LSpace (0 : Divisor L (modularFunctionFieldOver N L)) := by
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    simp only [Finsupp.zero_apply, neg_zero, h v, le_refl]
  rw [original_lSpace_zero_eq_range N L] at hm
  obtain ⟨c, hc⟩ := hm
  exact ⟨c, hc.symm⟩

theorem originalDivisorEval_constant_of_degree_zero (c : L) (hc : c ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L)) (hD : Divisor.degree D = 0) :
    originalDivisorEval N L (algebraMap L (modularFunctionFieldOver N L) c) D = 1 := by
  have hs : ∑ v ∈ D.support, D v = 0 := by
    rw [Divisor.degree_eq_sum_support] at hD
    have hr (v : Place L (modularFunctionFieldOver N L)) : Module.finrank L v.ResidueField = 1 :=
      Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N L v)
    simpa only [hr, Nat.cast_one, mul_one] using hD
  have hp : (∏ v ∈ D.support, c ^ D v) = c ^ (∑ v ∈ D.support, D v) := by
    induction D.support using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]
  change (∏ v ∈ D.support, originalPlaceEval N L v
    (algebraMap L (modularFunctionFieldOver N L) c) ^ D v) = 1
  simp_rw [originalPlaceEval_algebraMap]
  rw [hp, hs, zpow_zero]

theorem originalDivisorEval_eq_of_same_orders (f g : modularFunctionFieldOver N L)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hord : ∀ v : Place L (modularFunctionFieldOver N L), v.ord f = v.ord g)
    (D : Divisor L (modularFunctionFieldOver N L)) (hD : Divisor.degree D = 0)
    (hunit : ∀ v ∈ D.support, v.ord g = 0) : originalDivisorEval N L f D = originalDivisorEval N L g D := by
  obtain ⟨c, hc⟩ := original_constant_of_orders_zero N L (f * g⁻¹) (fun v => by
    rw [v.ord_mul hf (inv_ne_zero hg), v.ord_inv, hord v, add_neg_cancel])
  have hc0 : c ≠ 0 := by
    intro hz
    apply mul_ne_zero hf (inv_ne_zero hg)
    rw [hc, hz, map_zero]
  have he : f = algebraMap L (modularFunctionFieldOver N L) c * g := by
    rw [← hc, mul_assoc, inv_mul_cancel₀ hg, mul_one]
  rw [he, originalDivisorEval_mul N L _ _ D (fun v _ => v.algebraMap_mem' c)
    (fun v hv => v.mem_of_ord_nonneg (hunit v hv).ge),
    originalDivisorEval_constant_of_degree_zero N L c hc0 D hD, one_mul]

end
end Dubon2026.SourceFunctionField
