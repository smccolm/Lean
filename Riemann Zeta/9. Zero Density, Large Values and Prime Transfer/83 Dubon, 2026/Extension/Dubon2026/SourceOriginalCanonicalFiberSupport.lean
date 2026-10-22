import Dubon2026.SourceOriginalExceptionalFiberCounts
import Dubon2026.SourceOriginalJCoordinatePlaces

/-! DUB-17/18 -> matching cusp-form dimension -> numerical modular genus.
The canonical j-divisor of the actual original field is supported on the
two exceptional finite fibers and the cusps. The existing simple-order
theorem discharges every other finite place; no ramification premise remains.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem original_j_fiber_nonneg (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (c : ℂ)
    (hc : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c)) :
    0 ≤ v.ord (jOver N ℂ) := by
  apply v.ord_nonneg_of_mem
  have h := add_mem (v.mem_of_ord_nonneg hc.le) (v.algebraMap_mem' c)
  simpa only [sub_add_cancel] using h

theorem original_j_fiber_value_unique (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (c d : ℂ)
    (hc : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c))
    (hd : 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) d)) :
    c = d := by
  rcases original_j_place_dichotomy N ℂ v with hp | ⟨a, _, ha⟩
  · exact False.elim ((not_lt_of_ge (original_j_fiber_nonneg N v c hc)) hp)
  · exact (ha c hc).trans (ha d hd).symm

theorem original_jCanonical_eq_zero_off_exceptional (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (hpole : ¬ v.ord (jOver N ℂ) < 0)
    (h0 : ¬ 0 < v.ord (jOver N ℂ))
    (h1728 : ¬ 0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728)) :
    originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ) v = 0 := by
  rcases original_j_place_dichotomy N ℂ v with hp | ⟨c, hc, _⟩
  · exact False.elim (hpole hp)
  · have hc0 : c ≠ 0 := by
      intro he
      apply h0
      simpa only [he, map_zero, sub_zero] using hc
    have hc1728 : c ≠ 1728 := fun he => h1728 (he ▸ hc)
    rw [original_jCanonical_at_value N ℂ v c hc,
      original_finite_j_fiber_order_one N v c hc0 hc1728 hc, sub_self]

theorem original_jCanonical_support_subset_fibers (N : ℕ) [NeZero N]
    [DecidableEq (Place ℂ (modularFunctionFieldOver N ℂ))]
    (S0 S1728 Spole : Finset (Place ℂ (modularFunctionFieldOver N ℂ)))
    (h0 : ∀ v, v ∈ S0 ↔ 0 < v.ord (jOver N ℂ))
    (h1728 : ∀ v, v ∈ S1728 ↔
      0 < v.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728))
    (hpole : ∀ v, v ∈ Spole ↔ v.ord (jOver N ℂ) < 0) :
    (originalCanonicalDivisor N ℂ (D_jOver_ne_zero N ℂ)).support ⊆ S0 ∪ S1728 ∪ Spole := by
  classical
  intro v hv
  by_contra hn
  have hz : v ∉ S0 ∧ v ∉ S1728 ∧ v ∉ Spole := by
    simpa only [Finset.mem_union, not_or, and_assoc] using hn
  exact (Finsupp.mem_support_iff.mp hv)
    (original_jCanonical_eq_zero_off_exceptional N v
      (fun h => hz.2.2 ((hpole v).mpr h)) (fun h => hz.1 ((h0 v).mpr h))
      (fun h => hz.2.1 ((h1728 v).mpr h)))

end
end Dubon2026.SourceFunctionField
