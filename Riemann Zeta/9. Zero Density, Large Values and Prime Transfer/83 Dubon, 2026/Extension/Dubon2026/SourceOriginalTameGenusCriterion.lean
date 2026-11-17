import Dubon2026.SourceOriginalResidueHurwitz
import Dubon2026.SourceGammaOneArithmeticGenusBound
import Dubon2026.SourceCurveSeparatingFiberSums
import Dubon2026.SourceCurveCoordinateValues

/-! DUB-17/18 -> original all-weight association -> homogeneous Gamma1
realization -> original genus preservation -> reverse genus. Native complete
fiber multiplicities and the original Hurwitz/cusp bound turn the two tame
cardinality bounds into the reverse genus inequality on the actual original
residue field. The displayed finite sets and counts are intermediate inputs;
the next consumer supplies them from the proved original marked charts. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open CongruenceSubgroup GammaOne SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem original_genus_lower_of_tame_fiber_bounds (hℓN : ¬ ℓ ∣ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (h1728 : (1728 : kk) ≠ 0)
    (S₀ S₁ : Finset (Place kk F))
    (hS₀ : ∀ v, v ∈ S₀ ↔ 0 < v.ord (x))
    (hS₁ : ∀ v, v ∈ S₁ ↔ 0 < v.ord
      (x - algebraMap kk F 1728))
    (hc₀ : 3 * S₀.card ≤ (plusMinus (Gamma1 N)).index)
    (hc₁ : 2 * S₁.card ≤ (plusMinus (Gamma1 N)).index) :
    genusFF Qbar (functionFieldOver (Gamma1 N) Qbar) ≤ genusFF kk F := by
  classical
  letI := valuation_residue_isAlgClosed A
  letI := original_coordinate_finite A N ℓ hℓN x hx
  letI := original_coordinate_isSeparable A N ℓ hℓN x hx
  have hxtr : Transcendental kk x := by
    intro h
    apply transcendental_jqModC kk
    rw [← hx]
    exact h.algHom (F).val
  have hdis : Disjoint S₀ S₁ := by
    rw [Finset.disjoint_left]
    intro v h₀ h₁
    have hf := v.mem_of_ord_nonneg ((hS₀ v).mp h₀).le
    have hz : 0 < v.ord (x - algebraMap kk F 0) := by
      simpa only [map_zero, sub_zero] using (hS₀ v).mp h₀
    have he := ((v.ord_sub_algebraMap_pos_iff_residue_eq
      hxtr hf 0).mp hz).symm.trans
        ((v.ord_sub_algebraMap_pos_iff_residue_eq
          hxtr hf 1728).mp ((hS₁ v).mp h₁))
    exact h1728 ((algebraMap kk v.ResidueField).injective he).symm
  have h := original_hurwitz_ramification_cusp_bound A N ℓ hℓN x hx (S₀ ∪ S₁)
    (fun v => if v ∈ S₀ then 0 else 1728) (by
      intro v hv
      rcases Finset.mem_union.mp hv with h₀ | h₁
      · simpa only [if_pos h₀, map_zero, sub_zero] using (hS₀ v).mp h₀
      · simpa only [if_neg (Finset.disjoint_right.mp hdis h₁)] using (hS₁ v).mp h₁)
  rw [Finset.sum_union hdis] at h
  have he₀ : (∑ v ∈ S₀, (v.ord (x -
      algebraMap kk F (if v ∈ S₀ then 0 else 1728)) - 1)) =
      ((plusMinus (Gamma1 N)).index : ℤ) - S₀.card := by
    have hs := sum_fiber_orders_finset_separating x hxtr 0 S₀ (fun v => by
      simpa only [map_zero, sub_zero] using hS₀ v)
    rw [original_coordinate_finrank_eq_index A N ℓ hℓN x hx] at hs
    simp only [map_zero, sub_zero] at hs
    rw [Finset.sum_congr rfl (g := fun v => v.ord (x) - 1)
      (fun v hv => by rw [if_pos hv, map_zero, sub_zero]), Finset.sum_sub_distrib, hs]
    simp
  have he₁ : (∑ v ∈ S₁, (v.ord (x -
      algebraMap kk F (if v ∈ S₀ then 0 else 1728)) - 1)) =
      ((plusMinus (Gamma1 N)).index : ℤ) - S₁.card := by
    rw [Finset.sum_congr rfl (g := fun v => v.ord
      (x - algebraMap kk F 1728) - 1)
      (fun v hv => by rw [if_neg (Finset.disjoint_right.mp hdis hv)]),
      Finset.sum_sub_distrib, sum_fiber_orders_finset_separating x hxtr 1728 S₁ hS₁,
      original_coordinate_finrank_eq_index A N ℓ hℓN x hx]
    simp
  rw [he₀, he₁] at h
  have hg := gamma1_arithmetic_genus_cusp_bound N
  change 12 * genusFF Qbar (functionFieldOver (Gamma1 N) Qbar) +
    6 * Nat.card (CuspCounting.PolePlaces (Gamma1 N)) ≤
      12 + (plusMinus (Gamma1 N)).index at hg
  omega

end
end Dubon2026.SourceFunctionField.MarkedChart
