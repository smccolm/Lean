import Dubon2026.SpectralUnramifiedInvariantCompatibility
import Dubon2026.SpectralFiniteStageUnramifiedH2Detection
import Dubon2026.ContinuousGaloisUnitH2FiniteStage

/-! # The arithmetic period invariant of the original continuous local H2 -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Every original continuous class comes from a genuine spectral
unramified stage, retaining its original unit coefficients and Krull topology. -/
theorem spectralContinuousH2_exists_unramified_stage
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ _ : SpectralStageUnramified K Ω F,
      ∃ y : GaloisUnitH2FiniteStage K Ω F, galoisUnitH2FiniteStageMap K Ω F y = x := by
  obtain ⟨E, y, hy⟩ := continuousGaloisUnitH2_exists_finite_stage x
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  obtain ⟨F, _, hF, z, hz⟩ := spectralFiniteStageH2_exists_unramified_representative E y
  exact ⟨F, hF, z, hz.symm.trans hy⟩

/-- The full continuous class has a unique rational value obtained
from an actual unramified arithmetic-Frobenius period. Existence and
independence are proved for the original class rather than assumed. -/
theorem spectralContinuousH2Invariant_existsUnique
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃! q : AddCircle (1 : ℚ),
      ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hF : SpectralStageUnramified K Ω F,
        ∃ y : GaloisUnitH2FiniteStage K Ω F,
          galoisUnitH2FiniteStageMap K Ω F y = x ∧ spectralUnramifiedStageInvariant K Ω F hF y = q := by
  obtain ⟨F, hF, y, hy⟩ := spectralContinuousH2_exists_unramified_stage K Ω x
  refine ⟨spectralUnramifiedStageInvariant K Ω F hF y, ⟨F, hF, y, hy, rfl⟩, ?_⟩
  rintro q ⟨E, hE, z, hz, hq⟩
  exact hq.symm.trans
    (spectralUnramifiedStageInvariant_eq_of_inflation_eq K Ω E F hE hF z y (hz.trans hy.symm))

/-- The actual rational invariant on full original continuous H2,
defined by the proved unique arithmetic period value. -/
def spectralContinuousH2Invariant
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) : AddCircle (1 : ℚ) :=
  (spectralContinuousH2Invariant_existsUnique K Ω x).exists.choose

/-- The selected invariant is realized by a genuine unramified
representative of the original class. -/
theorem spectralContinuousH2Invariant_spec
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hF : SpectralStageUnramified K Ω F,
      ∃ y : GaloisUnitH2FiniteStage K Ω F,
        galoisUnitH2FiniteStageMap K Ω F y = x ∧
          spectralUnramifiedStageInvariant K Ω F hF y = spectralContinuousH2Invariant K Ω x :=
  (spectralContinuousH2Invariant_existsUnique K Ω x).exists.choose_spec

/-- On each actual unramified stage the full invariant equals the
original arithmetic-Frobenius period divided by the actual field degree. -/
theorem spectralContinuousH2Invariant_stage
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    (y : GaloisUnitH2FiniteStage K Ω F) :
    spectralContinuousH2Invariant K Ω (galoisUnitH2FiniteStageMap K Ω F y) =
      spectralUnramifiedStageInvariant K Ω F hF y := by
  obtain ⟨E, hE, z, hz, hq⟩ :=
    spectralContinuousH2Invariant_spec K Ω (galoisUnitH2FiniteStageMap K Ω F y)
  exact hq.symm.trans (spectralUnramifiedStageInvariant_eq_of_inflation_eq K Ω E F hE hF z y hz)

end
end Dubon2026
