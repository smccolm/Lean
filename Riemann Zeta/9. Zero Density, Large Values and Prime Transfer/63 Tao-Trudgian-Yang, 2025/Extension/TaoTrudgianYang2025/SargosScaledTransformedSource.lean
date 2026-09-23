import TaoTrudgianYang2025.SargosScaledTransformedModel
import TaoTrudgianYang2025.SargosPositiveSextupleModel

/-! Exact arbitrary-window entry of the actual sextuple phase into its scaled model. -/

noncomputable section

open Set Expdb GafniTao Filter
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem sargosScaledTransformedModel_physical_identity {F : ℝ → ℝ}
    {σ N A τ T : ℝ} {H M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hσ : 0 < σ)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+(M:ℝ) ≤ 2*N)
    (hτ : 0 < τ) (hT : 0 < T) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) M) :
    sargosScaledTransformedTime σ N τ T*sargosScaledTransformedModel F σ M N A Q q τ T ((A+x)/N) =
      τ*iteratedDeriv 4 (heathBrownPhysicalPhase F T N A 1) x+
        sargosScaledPhysicalRemainder (heathBrownPhysicalPhase F T N A 1) M N Q q x := by
  have hD : 0 < modelPhaseJetCoefficient σ 4 := modelPhaseJetCoefficient_pos hσ 4
  have hu := heathBrownPhysicalPoint_mem_interior hN ha hb hx
  have hfat : ContDiffAt ℝ 4 F ((A+x)/N) :=
    ((hF _ ⟨hu.1.le,hu.2.le⟩).contDiffAt
      (mem_of_superset (isOpen_Ioo.mem_nhds hu) Ioo_subset_Icc_self)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hw := iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hfat
    (show (A+x)/N ∈ phaseInterval from ⟨hu.1.le,hu.2.le⟩)
  have hsrc := heathBrownPhysicalPhase_iteratedDeriv hF hN ha hb hx T 1 4
  have hp : N*((A+x)/N)-A = x := by
    field_simp
    ring
  rw [sargosScaledTransformedModel,sargosFourthDerivativeModel,sargosAffinePhysicalCorrection,
    hw,hp,hsrc]
  unfold sargosScaledTransformedTime
  field_simp

theorem sargosScaledTransformedModel_source_phase {F : ℝ → ℝ}
    {σ N A τ T : ℝ} {H M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hσ : 0 < σ)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+(M:ℝ) ≤ 2*N)
    (hτ : 0 < τ) (hT : 0 < T) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hfreq : (sargosQuarticDifference q:ℝ)/12 = τ)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosSextuplePhase (heathBrownPhysicalPhase F T N A 1) q m =
      sargosScaledTransformedTime σ N τ T*
        sargosScaledTransformedModel F σ M N A Q q τ T ((A+m)/N) := by
  have hr : (0:ℝ) ≤ sargosSextupleRadius q := by
    exact_mod_cast (show 0 ≤ sargosSextupleRadius q from
      le_trans (by norm_num) (sargosSextupleRadius_bounds q).1)
  have hi := sargosSextupleInterior_real q hm
  have hx : (m:ℝ) ∈ Ioo (0:ℝ) M := ⟨by linarith [hi.1],by linarith [hi.2]⟩
  change ((sargosQuarticDifference q:ℝ)/12)*
    iteratedDeriv 4 (heathBrownPhysicalPhase F T N A 1) m+
    sargosSextupleRemainder (heathBrownPhysicalPhase F T N A 1) q m = _
  rw [hfreq,← sargosScaledPhysicalRemainder_agrees (heathBrownPhysicalPhase F T N A 1) hN Q q hm]
  exact (sargosScaledTransformedModel_physical_identity hF hσ hN ha hb hτ hT Q q hx).symm

theorem sargosScaledTransformedModel_source_sum {F : ℝ → ℝ}
    {σ N A τ T : ℝ} {H M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hσ : 0 < σ)
    (hN : 0 < N) (ha : N ≤ A) (hb : A+(M:ℝ) ≤ 2*N)
    (hτ : 0 < τ) (hT : 0 < T) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hfreq : (sargosQuarticDifference q:ℝ)/12 = τ) :
    (∑ m ∈ sargosSextupleInterior M q,
      fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T N A 1) q m)) =
      ∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter
          (sargosScaledTransformedTime σ N τ T*
            sargosScaledTransformedModel F σ M N A Q q τ T ((A+m)/N)) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [sargosScaledTransformedModel_source_phase hF hσ hN ha hb hτ hT Q q hfreq hm]

theorem sargos_scaled_positive_sextuple_model (σ : ℝ) (hσ : 0 < σ) (P : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (H M : ℕ) (F : ℝ → ℝ) (δ N A T : ℝ)
      (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3),
      1 ≤ M → δ ≤ 1 → 0 < N → N ≤ A → A+(M:ℝ) ≤ 2*N →
      0 < T → 0 < sargosQuarticDifference q →
      IsApproximateModelPhaseFunction F σ (P+7) δ →
      let τ : ℝ := (sargosQuarticDifference q:ℝ)/12
      IsApproximateModelPhaseFunction (sargosScaledTransformedModel F σ M N A (P+1) q τ T)
        (σ+4) P ((δ+C*(H:ℝ)^6/(τ*N^2))/modelPhaseJetCoefficient σ 4) ∧
      (∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T N A 1) q m)) =
        ∑ m ∈ sargosSextupleInterior M q,
          fordAdditiveCharacter
            (sargosScaledTransformedTime σ N τ T*
              sargosScaledTransformedModel F σ M N A (P+1) q τ T ((A+m)/N)) := by
  obtain ⟨C,hC,hmodel⟩ := sargosScaledTransformedModel_approximate σ hσ P
  refine ⟨C,hC,?_⟩
  intro H M F δ N A T q hM hδ hN ha hb hT hq hF τ
  have hτ : 0 < τ := by
    have hp : (0:ℝ) < sargosQuarticDifference q := by exact_mod_cast hq
    exact div_pos hp (by norm_num)
  exact ⟨hmodel H M F δ N A τ T q hM hδ hN ha hb hτ hT hF,
    sargosScaledTransformedModel_source_sum hF.1 hσ hN ha hb hτ hT (P+1) q rfl⟩

end TaoTrudgianYang2025
