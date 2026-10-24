import Dubon2026.SourceJointChartLaurentWindow
import Dubon2026.SourceJointChartLocalizations

/-! DUB-17/18 -> Kummer power lifting -> finite overlap. A basis with
proved good coordinate denominators and a common inverse-chart power gives
an explicit decomposition of every overlap element into the two localized
charts plus a finite Laurent window. No finiteness certificate is assumed. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing

theorem overlap_decomposition_of_good_basis
    {L : Type} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {ι J : Type*} [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hf : ∀ i, f ∈ (R i).integers) (hfi : ∀ i, f⁻¹ ∈ (R i).integers)
    (htr : Transcendental L f) (z : J → F) (hz : ∀ j, z j ∈ Sg R f)
    (m : ℕ) (hzm : ∀ j, f⁻¹ ^ m * z j ∈ Sg R f⁻¹)
    (hgood : ∀ s ∈ Sg R f, ∃ (t : L[X]) (p : J → L[X]), IsGood A t ∧
      (∀ j k, (p j).coeff k ∈ A) ∧ s * aeval f t = ∑ j, aeval f (p j) * z j)
    (x : F) (hx : x ∈ Ppp R f hf) :
    ∃ y ∈ Pg R f hf, ∃ v ∈ Pg R f⁻¹ hfi, ∃ a : J → Fin (m + 1) → A,
      x = y + v + ∑ j, ∑ k : Fin (m + 1),
        algebraMap L F (a j k : L) * (f⁻¹ ^ (k : ℕ) * z j) := by
  classical
  have htri : Transcendental L f⁻¹ := fun h => htr (IsAlgebraic.inv_iff.mp h)
  obtain ⟨D, d, hD, hs⟩ := hx
  obtain ⟨t, p, ht, hp, he⟩ := hgood (x * aeval f D) hs
  have hDt : IsGoodAt A d (D * t) := by
    simpa only [Nat.add_zero] using hD.mul (show IsGoodAt A 0 t from ht)
  have hDt0 : D * t ≠ 0 := by
    intro h
    have hh := hDt.1
    rw [h, coeff_zero, map_zero] at hh
    exact zero_ne_one hh
  have hden : aeval f (D * t) ≠ 0 := fun h => hDt0 (transcendental_iff.mp htr _ h)
  have hxsum : x = ∑ j, (aeval f (p j) / aeval f (D * t)) * z j := by
    have he' : x * aeval f (D * t) = ∑ j, aeval f (p j) * z j := by
      rw [map_mul, ← mul_assoc]
      exact he
    rw [(eq_div_iff hden).mpr he', Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hex : ∀ j, ∃ (y v : F) (a : Fin (m + 1) → A),
      y ∈ Pg R f hf ∧ v ∈ Pg R f⁻¹ hfi ∧
      (aeval f (p j) / aeval f (D * t)) * z j = y + v +
        ∑ k : Fin (m + 1), algebraMap L F (a k : L) * (f⁻¹ ^ (k : ℕ) * z j) := by
    intro j
    obtain ⟨p₁, t₁, q, s, r, hp₁, hq, hr, hrdeg, ht₁, hs, hwindow⟩ :=
      exists_two_chart_laurent_window A f htr (p j) (D * t) (hp j) hDt m
    have ht₁0 : aeval f t₁ ≠ 0 := fun h => ht₁.ne_zero A (transcendental_iff.mp htr _ h)
    have hs0 : aeval f⁻¹ s ≠ 0 := fun h => hs.ne_zero A (transcendental_iff.mp htri _ h)
    refine ⟨(aeval f p₁ / aeval f t₁) * z j,
      (aeval f⁻¹ q / aeval f⁻¹ s) * (f⁻¹ ^ m * z j),
      fun k => ⟨r.coeff k, hr k⟩, ?_, ?_, ?_⟩
    · refine ⟨t₁, ht₁, ?_⟩
      rw [mul_right_comm, div_mul_cancel₀ _ ht₁0]
      exact mul_mem (aeval_mem_Sg R hf hp₁) (hz j)
    · refine ⟨s, hs, ?_⟩
      rw [mul_right_comm, div_mul_cancel₀ _ hs0]
      exact mul_mem (aeval_mem_Sg R hfi hq) (hzm j)
    · have hrval : aeval f⁻¹ r = ∑ k : Fin (m + 1),
          algebraMap L F (r.coeff k) * f⁻¹ ^ (k : ℕ) := by
        rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hrdeg), Finset.sum_range]
        simp only [Algebra.smul_def]
      rw [hwindow, hrval, add_mul, add_mul, Finset.sum_mul]
      refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun k _ => ?_)
      exact mul_assoc _ _ _
  choose y v a hy hv hsum using hex
  refine ⟨∑ j, y j, (Pg R f hf).sum_mem fun j _ => hy j,
    ∑ j, v j, (Pg R f⁻¹ hfi).sum_mem fun j _ => hv j, a, ?_⟩
  rw [hxsum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => hsum j

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
