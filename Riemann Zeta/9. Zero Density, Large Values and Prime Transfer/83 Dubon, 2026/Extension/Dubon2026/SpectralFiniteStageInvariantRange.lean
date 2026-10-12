import Dubon2026.SpectralUnramifiedStageDescent
import Dubon2026.SpectralContinuousH2InvariantEquiv

/-! # The exact full invariant range of every original finite Galois stage -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original finite-stage invariant is the full arithmetic invariant
of its genuine inflation into the original continuous Galois H2. -/
def spectralFiniteStageFullInvariant (E : FiniteGaloisIntermediateField K Ω) :
    GaloisUnitH2FiniteStage K Ω E →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (spectralContinuousH2InvariantLinear K Ω).comp (galoisUnitH2FiniteStageMap K Ω E)

/-- Actual finite-stage inflation and the full invariant both detect
equality, so their original finite-stage composition is injective. -/
theorem spectralFiniteStageFullInvariant_injective (E : FiniteGaloisIntermediateField K Ω) :
    Function.Injective (spectralFiniteStageFullInvariant K Ω E) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  exact (spectralContinuousH2Invariant_injective K Ω).comp
    (galoisUnitFiniteStageH2Inflation_injective E)

/-- The invariant of every original finite-stage class is annihilated
by its actual field degree. This follows by genuine same-degree
unramified detection, not by an assumed order of the cohomology group. -/
theorem spectralFiniteStageFullInvariant_degree_annihilates
    (E : FiniteGaloisIntermediateField K Ω) (x : GaloisUnitH2FiniteStage K Ω E) :
    Module.finrank K E • spectralFiniteStageFullInvariant K Ω E x = 0 := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K E) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K E) := ⟨rfl⟩
  obtain ⟨F, hdegree, hF, y, hy⟩ := spectralFiniteStageH2_exists_unramified_representative E x
  have hvalue : spectralFiniteStageFullInvariant K Ω E x =
      spectralUnramifiedStageInvariant K Ω F hF y := by
    change spectralContinuousH2Invariant K Ω (galoisUnitFiniteStageH2Inflation E x) = _
    rw [hy]
    exact spectralContinuousH2Invariant_stage K Ω F hF y
  rw [hvalue, ← hdegree]
  exact (spectralUnramifiedStageInvariant_mem_range_iff K Ω F hF _).mp ⟨y, rfl⟩

/-- The exact image of the invariant on every actual finite Galois
stage is the full degree-annihilated subgroup of the rational circle.
The reverse inclusion constructs an original same-degree unramified
representative and descends it to the actual given finite field. -/
theorem spectralFiniteStageFullInvariant_mem_range_iff
    (E : FiniteGaloisIntermediateField K Ω) (q : AddCircle (1 : ℚ)) :
    q ∈ (spectralFiniteStageFullInvariant K Ω E).range ↔ Module.finrank K E • q = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact spectralFiniteStageFullInvariant_degree_annihilates K Ω E x
  · intro hq
    haveI : NeZero (Module.finrank K E) := ⟨Module.finrank_pos.ne'⟩
    obtain ⟨F, hdegree, hF⟩ := localField_exists_spectral_original_unramified_stage K Ω (Module.finrank K E)
    have hqF : Module.finrank K F • q = 0 := by rw [hdegree, hq]
    obtain ⟨y, hy⟩ := (spectralUnramifiedStageInvariant_mem_range_iff K Ω F hF q).mpr hqF
    obtain ⟨x, hx⟩ := spectralUnramifiedStageH2_descends_same_degree E F hdegree hF y
    refine ⟨x, ?_⟩
    change spectralContinuousH2Invariant K Ω (galoisUnitH2FiniteStageMap K Ω E x) = q
    rw [hx, spectralContinuousH2Invariant_stage K Ω F hF]
    exact hy

end
end Dubon2026
