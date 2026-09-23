import TaoTrudgianYang2025.SargosModelRemainderJets

/-! Actual approximate-model input to the constructed smooth source reduction. -/

noncomputable section

open Set Expdb GafniTao
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem sargos_model_smooth_reduction (σ : ℝ) (hσ : 0 ≤ σ)
    (Q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M P : ℕ) (F : ℝ → ℝ) (δ T N A : ℝ),
      1 ≤ H → H ≤ M → Q+6 ≤ P → δ ≤ 1 →
      0 < N → N ≤ A → A+(M:ℝ) ≤ 2*N →
      IsApproximateModelPhaseFunction F σ P δ →
      (∀ q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3,
        ContDiff ℝ ∞ (sargosPhysicalExtendedRemainder
          (heathBrownPhysicalPhase F T N A 1) M Q q) ∧
        (∀ m ∈ sargosSextupleInterior M q,
          sargosPhysicalExtendedRemainder (heathBrownPhysicalPhase F T N A 1) M Q q m =
            sargosSextupleRemainder (heathBrownPhysicalPhase F T N A 1) q m) ∧
        ∀ x ∈ Icc (0:ℝ) M, ∀ j ≤ Q,
          |iteratedDeriv j (sargosPhysicalExtendedRemainder
            (heathBrownPhysicalPhase F T N A 1) M Q q) x| ≤
              C * |T| * (H:ℝ)^6/(60*N^6*(M:ℝ)^j)) ∧
      ‖∑ m ∈ Finset.Ioc (0:ℤ) M,
        fordAdditiveCharacter (heathBrownPhysicalPhase F T N A 1 m)‖^12 ≤
        1492992*((M:ℝ)/H)^6*(M:ℝ)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*
          sargosExtendedSextupleCorrelation (heathBrownPhysicalPhase F T N A 1) M H Q+
        C*(M:ℝ)^11*(H:ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := sargos_smooth_extended_reduction Q ε hε
  let D := sargosModelJetBudget σ Q
  have hD : 1 ≤ D := sargosModelJetBudget_one_le σ Q
  have hCD : C ≤ C*D := by nlinarith
  refine ⟨C*D,hC.trans hCD,?_⟩
  intro H M P F δ T N A hH hHM hP hδ hN ha hb hF
  have hM : 1 ≤ M := hH.trans hHM
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hsource := hbound H M (heathBrownPhysicalPhase F T N A 1)
    (D*|T|/N^6) hH hHM (by positivity)
    (fun y hy => sargosModelPhysicalPhase_contDiffAt hF.1 hN ha hb hy T)
    (fun j hj y hy => sargosModelPhysicalPhase_source_jets hσ hF hδ hP hM hN ha hb hj hy)
  constructor
  · intro q
    obtain ⟨hc,he,hj⟩ := hsource.1 q
    refine ⟨hc,he,?_⟩
    intro x hx j hjQ
    convert hj x hx j hjQ using 1
    ring
  · exact hsource.2.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCD (by positivity))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

end TaoTrudgianYang2025
