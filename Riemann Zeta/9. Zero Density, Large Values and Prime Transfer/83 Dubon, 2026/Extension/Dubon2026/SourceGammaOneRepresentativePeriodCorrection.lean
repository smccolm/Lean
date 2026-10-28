import Dubon2026.SourceGammaOneRepresentativePeriods

/-! DUB-17/18 -> original arithmetic association -> Gamma1 Picard/H1 ->
Abel-Jacobi converse -> reciprocity -> original finite divisor functional.
The already constructed distinct orbit representatives are a finite lift of
the same analytic divisor. Native Finsupp pushforward and the existing period
quotient theorem give the exact integral-period correction. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup
open scoped MatrixGroups Classical

theorem representative_period_difference_mem (N : ℕ) [NeZero N]
    (hT : ModularGroup.T ∈ Gamma1 N) (c : ℍ →₀ ℤ) (S : Finset ℍ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S, (∃ γ : Gamma1 N, γ.val • s = t) → s = t)
    (hcov : ∀ τ : ℍ, (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT τ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : Gamma1 N, γ.val • s = τ) :
    (c.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) -
      ∑ s ∈ S, (Finsupp.mapDomain (analyticPlace hT) c) (analyticPlace hT s) •
        sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I s) ∈
          sourceWeightTwoIntegralLattice (Gamma1 N) := by
  classical
  let D := Finsupp.mapDomain (analyticPlace hT) c
  let d : ℍ →₀ ℤ := ∑ s ∈ S, Finsupp.single s (D (analyticPlace hT s))
  have hd : Finsupp.mapDomain (analyticPlace hT) d = D := by
    dsimp only [d]
    rw [Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single]
    ext P
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
    by_cases hP : D P = 0
    · apply Eq.trans ?_ hP.symm
      apply Finset.sum_eq_zero
      intro s _
      split_ifs with hs
      · rw [hs, hP]
      · rfl
    · obtain ⟨τ, hτ⟩ : ∃ τ : ℍ, analyticPlace hT τ = P := by
        by_contra hn
        exact hP (Finsupp.mapDomain_notin_range c P hn)
      obtain ⟨s, hs, γ, hγ⟩ := hcov τ (by rwa [hτ])
      have hsp : analyticPlace hT s = P :=
        ((analyticPlace_eq_iff_gamma1_orbit N hT s τ).mpr ⟨γ, hγ⟩).trans hτ
      rw [Finset.sum_eq_single s]
      · simp [hsp]
      · intro t ht hts
        have hne : analyticPlace hT t ≠ P := by
          intro htp
          exact hts (hinj t ht s hs
            ((analyticPlace_eq_iff_gamma1_orbit N hT t s).mp (htp.trans hsp.symm)))
        simp [hne]
      · exact fun hns => (hns hs).elim
  have hsum : d.sum (fun τ n => n • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ) =
      ∑ s ∈ S, D (analyticPlace hT s) • sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I s := by
    dsimp only [d]
    rw [← Finsupp.sum_finsetSum_index
      (fun τ => zero_smul ℤ (sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ))
      (fun τ m n => add_smul m n (sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ))]
    exact Finset.sum_congr rfl fun τ _ =>
      Finsupp.sum_single_index (zero_smul ℤ (sourceWeightTwoAlong (Gamma1 N) UpperHalfPlane.I τ))
  have hm := period_difference_mem_of_mapDomain_eq N hT c d hd.symm
  rwa [hsum] at hm

end
end Dubon2026.SourceFunctionField.GammaOne
