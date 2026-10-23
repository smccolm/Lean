import Dubon2026.SourceModularCoefficientHurwitzCuspBound
import Dubon2026.SourceCurveCoordinateValues

/-! The remaining tame input for the DUB-17/18 reverse genus inequality
is exactly the cardinality of the two finite exceptional fibers. All
degree, cusp and Hurwitz assumptions are derived on the actual field.
This is conditional on the displayed finite census, which remains open. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceLevelProjective
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

theorem coeff_genus_lower_of_exceptional_fiber_counts (hNK : (N : K) ≠ 0)
    (h1728 : (1728 : K) ≠ 0)
    (S₀ S₁ : Finset (Place K (modularFunctionFieldCoeff N K)))
    (hS₀ : ∀ v, v ∈ S₀ ↔ 0 < v.ord (jCoeff N K))
    (hS₁ : ∀ v, v ∈ S₁ ↔ 0 < v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) 1728))
    (hc₀ : 3 * S₀.card = dedekindPsi N + 2 * nuThree N)
    (hc₁ : 2 * S₁.card = dedekindPsi N + nuTwo N) :
    genusFormula N ≤ (genusFF K (modularFunctionFieldCoeff N K) : ℚ) := by
  classical
  have hdis : Disjoint S₀ S₁ := by
    rw [Finset.disjoint_left]
    intro v h₀ h₁
    have hf := v.mem_of_ord_nonneg ((hS₀ v).mp h₀).le
    have hz : 0 < v.ord (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) 0) := by
      simpa only [map_zero, sub_zero] using (hS₀ v).mp h₀
    have he := ((v.ord_sub_algebraMap_pos_iff_residue_eq
      (transcendental_jCoeff N K) hf 0).mp hz).symm.trans
        ((v.ord_sub_algebraMap_pos_iff_residue_eq
          (transcendental_jCoeff N K) hf 1728).mp ((hS₁ v).mp h₁))
    exact h1728 ((algebraMap K v.ResidueField).injective he).symm
  have h := coeff_hurwitz_ramification_cusp_bound N K hNK (S₀ ∪ S₁)
    (fun v => if v ∈ S₀ then 0 else 1728) (by
      intro v hv
      rcases Finset.mem_union.mp hv with h₀ | h₁
      · simpa only [if_pos h₀, map_zero, sub_zero] using (hS₀ v).mp h₀
      · simpa only [if_neg (Finset.disjoint_right.mp hdis h₁)] using (hS₁ v).mp h₁)
  rw [Finset.sum_union hdis] at h
  have he₀ : (∑ v ∈ S₀, (v.ord (jCoeff N K -
      algebraMap K (modularFunctionFieldCoeff N K) (if v ∈ S₀ then 0 else 1728)) - 1)) =
      (dedekindPsi N : ℤ) - S₀.card := by
    have hs := sum_coeff_j_fiber_orders_finset N K hNK 0 S₀ (fun v => by
      simpa only [map_zero, sub_zero] using hS₀ v)
    simp only [map_zero, sub_zero] at hs
    rw [Finset.sum_congr rfl (g := fun v => v.ord (jCoeff N K) - 1)
      (fun v hv => by rw [if_pos hv, map_zero, sub_zero]), Finset.sum_sub_distrib, hs]
    simp
  have he₁ : (∑ v ∈ S₁, (v.ord (jCoeff N K -
      algebraMap K (modularFunctionFieldCoeff N K) (if v ∈ S₀ then 0 else 1728)) - 1)) =
      (dedekindPsi N : ℤ) - S₁.card := by
    rw [Finset.sum_congr rfl (g := fun v => v.ord
      (jCoeff N K - algebraMap K (modularFunctionFieldCoeff N K) 1728) - 1)
      (fun v hv => by rw [if_neg (Finset.disjoint_right.mp hdis hv)]),
      Finset.sum_sub_distrib, sum_coeff_j_fiber_orders_finset N K hNK 1728 S₁ hS₁]
    simp
  rw [he₀, he₁] at h
  have hq : ((dedekindPsi N : ℚ) - S₀.card) + ((dedekindPsi N : ℚ) - S₁.card) ≤
      2 * (genusFF K (modularFunctionFieldCoeff N K) : ℚ) - 2 +
        (dedekindPsi N : ℚ) + (cuspCount N : ℚ) := by exact_mod_cast h
  have hq₀ : (3 : ℚ) * S₀.card = dedekindPsi N + 2 * nuThree N := by exact_mod_cast hc₀
  have hq₁ : (2 : ℚ) * S₁.card = dedekindPsi N + nuTwo N := by exact_mod_cast hc₁
  unfold genusFormula
  linarith

end
end Dubon2026.SourceFunctionField
