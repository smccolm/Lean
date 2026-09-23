import TaoTrudgianYang2025.SargosTransformedModel

/-! The transformed model is the actual physical sextuple phase, with its linked time scale. -/

noncomputable section

open Set Expdb GafniTao Filter
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

theorem sargosTransformedModel_physical_identity {F : ℝ → ℝ} {σ τ T : ℝ} {H M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hσ : 0 < σ) (hM : 1 ≤ M)
    (hτ : 0 < τ) (hT : 0 < T) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    {x : ℝ} (hx : x ∈ Ioo (0:ℝ) M) :
    sargosTransformedTime σ M τ T*sargosTransformedModel F σ M Q q τ T (1+x/M) =
      τ*iteratedDeriv 4 (heathBrownPhysicalPhase F T M M 1) x+
        sargosPhysicalExtendedRemainder (heathBrownPhysicalPhase F T M M 1) M Q q x := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hD : 0 < modelPhaseJetCoefficient σ 4 := modelPhaseJetCoefficient_pos hσ 4
  have hu := heathBrownPhysicalPoint_mem_interior hM0 le_rfl
    (by linarith : (M:ℝ)+M ≤ 2*M) hx
  have hfat : ContDiffAt ℝ 4 F (((M:ℝ)+x)/M) :=
    ((hF _ ⟨hu.1.le,hu.2.le⟩).contDiffAt
      (mem_of_superset (isOpen_Ioo.mem_nhds hu) Ioo_subset_Icc_self)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hw := iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hfat
    (show ((M:ℝ)+x)/M ∈ phaseInterval from ⟨hu.1.le,hu.2.le⟩)
  have hsrc := heathBrownPhysicalPhase_iteratedDeriv hF hM0 le_rfl
    (by linarith : (M:ℝ)+M ≤ 2*M) hx T 1 4
  have he : (1:ℝ)+x/M = ((M:ℝ)+x)/M := by field_simp
  have hp : (M:ℝ)*(((M:ℝ)+x)/M-1) = x := by
    field_simp
    ring
  rw [he,sargosTransformedModel,sargosFourthDerivativeModel,sargosPhysicalCorrection,hw,hp,hsrc]
  unfold sargosTransformedTime
  field_simp

theorem sargosTransformedModel_source_phase {F : ℝ → ℝ} {σ τ T : ℝ} {H M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hσ : 0 < σ) (hM : 1 ≤ M)
    (hτ : 0 < τ) (hT : 0 < T) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hfreq : (((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2:ℤ):ℝ)/12) = τ)
    {m : ℤ} (hm : m ∈ sargosSextupleInterior M q) :
    sargosSextuplePhase (heathBrownPhysicalPhase F T M M 1) q m =
      sargosTransformedTime σ M τ T*sargosTransformedModel F σ M Q q τ T (1+(m:ℝ)/M) := by
  have hr : (0:ℝ) ≤ sargosSextupleRadius q := by
    exact_mod_cast (show 0 ≤ sargosSextupleRadius q from
      le_trans (by norm_num) (sargosSextupleRadius_bounds q).1)
  have hi := sargosSextupleInterior_real q hm
  have hx : (m:ℝ) ∈ Ioo (0:ℝ) M := ⟨by linarith [hi.1],by linarith [hi.2]⟩
  rw [← sargosExtendedSextuplePhase_agrees (heathBrownPhysicalPhase F T M M 1) hM Q q hm,
    sargosExtendedSextuplePhase,hfreq]
  exact (sargosTransformedModel_physical_identity hF hσ hM hτ hT Q q hx).symm

theorem sargosTransformedModel_source_sum {F : ℝ → ℝ} {σ τ T : ℝ} {H M : ℕ}
    (hF : ContDiffOn ℝ ∞ F phaseInterval) (hσ : 0 < σ) (hM : 1 ≤ M)
    (hτ : 0 < τ) (hT : 0 < T) (Q : ℕ)
    (q : SargosInitialMomentTuple H 3 × SargosInitialMomentTuple H 3)
    (hfreq : (((sargosInitialTuplePower 4 q.1-sargosInitialTuplePower 4 q.2:ℤ):ℝ)/12) = τ) :
    (∑ m ∈ sargosSextupleInterior M q,
      fordAdditiveCharacter (sargosSextuplePhase (heathBrownPhysicalPhase F T M M 1) q m)) =
      ∑ m ∈ sargosSextupleInterior M q,
        fordAdditiveCharacter
          (sargosTransformedTime σ M τ T*sargosTransformedModel F σ M Q q τ T (1+(m:ℝ)/M)) := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [sargosTransformedModel_source_phase hF hσ hM hτ hT Q q hfreq hm]

end TaoTrudgianYang2025
