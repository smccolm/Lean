import Dubon2026.SpectralContinuousH2Invariant

/-! # Original continuous local H2 is the rational circle via arithmetic periods -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [ValuativeRel K] [(NormedField.valuation (K := K)).Compatible]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Additivity follows by representing the two original classes
in their actual common unramified finite extension. -/
theorem spectralContinuousH2Invariant_add
    (x y : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    spectralContinuousH2Invariant K Ω (x + y) =
      spectralContinuousH2Invariant K Ω x + spectralContinuousH2Invariant K Ω y := by
  obtain ⟨E, hE, u, rfl⟩ := spectralContinuousH2_exists_unramified_stage K Ω x
  obtain ⟨F, hF, v, rfl⟩ := spectralContinuousH2_exists_unramified_stage K Ω y
  let H := E ⊔ F
  have hH : SpectralStageUnramified K Ω H := spectralStageUnramified_sup K Ω E F hE hF
  let uH := galoisUnitH2FiniteTransition K Ω E H le_sup_left u
  let vH := galoisUnitH2FiniteTransition K Ω F H le_sup_right v
  have hu := galoisUnitH2FiniteStageMap_transition K Ω E H le_sup_left u
  have hv := galoisUnitH2FiniteStageMap_transition K Ω F H le_sup_right v
  have hsum : galoisUnitH2FiniteStageMap K Ω H (uH + vH) =
      galoisUnitH2FiniteStageMap K Ω E u + galoisUnitH2FiniteStageMap K Ω F v :=
    (map_add (galoisUnitH2FiniteStageMap K Ω H) uH vH).trans (congrArg₂ (· + ·) hu hv)
  have hui : spectralUnramifiedStageInvariant K Ω H hH uH =
      spectralContinuousH2Invariant K Ω (galoisUnitH2FiniteStageMap K Ω E u) :=
    (spectralUnramifiedStageInvariant_transition K Ω E H le_sup_left hE hH u).trans
      (spectralContinuousH2Invariant_stage K Ω E hE u).symm
  have hvi : spectralUnramifiedStageInvariant K Ω H hH vH =
      spectralContinuousH2Invariant K Ω (galoisUnitH2FiniteStageMap K Ω F v) :=
    (spectralUnramifiedStageInvariant_transition K Ω F H le_sup_right hF hH v).trans
      (spectralContinuousH2Invariant_stage K Ω F hF v).symm
  exact (congrArg (spectralContinuousH2Invariant K Ω) hsum.symm).trans
    ((spectralContinuousH2Invariant_stage K Ω H hH (uH + vH)).trans
      ((map_add (spectralUnramifiedStageInvariant K Ω H hH) uH vH).trans
        (congrArg₂ (· + ·) hui hvi)))

/-- The full original arithmetic period invariant is a linear map. -/
def spectralContinuousH2InvariantLinear :
    GaloisUnitContinuousH2 (K := K) (Ω := Ω) →ₗ[ℤ] AddCircle (1 : ℚ) :=
  (AddMonoidHom.mk' (spectralContinuousH2Invariant K Ω)
    (spectralContinuousH2Invariant_add K Ω)).toIntLinearMap

/-- A zero invariant forces an actual unramified representative
to be zero, and therefore the original continuous class is zero. -/
theorem spectralContinuousH2Invariant_injective :
    Function.Injective (spectralContinuousH2InvariantLinear K Ω) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨F, hF, y, rfl⟩ := spectralContinuousH2_exists_unramified_stage K Ω x
  change spectralContinuousH2Invariant K Ω (galoisUnitH2FiniteStageMap K Ω F y) = 0 at hx
  rw [spectralContinuousH2Invariant_stage K Ω F hF] at hx
  have hy : y = 0 := spectralUnramifiedStageInvariant_injective K Ω F hF
    (hx.trans (map_zero _).symm)
  rw [hy, map_zero]

/-- Every rational class occurs: its positive denominator is the
degree of a constructed original unramified extension. -/
theorem spectralContinuousH2Invariant_surjective :
    Function.Surjective (spectralContinuousH2InvariantLinear K Ω) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective q
  haveI : NeZero a.den := ⟨a.den_pos.ne'⟩
  obtain ⟨F, hdegree, hF⟩ := localField_exists_spectral_original_unramified_stage K Ω a.den
  have hkill : Module.finrank K F • (a : AddCircle (1 : ℚ)) = 0 := by
    rw [hdegree, ← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff]
    refine ⟨a.num, ?_⟩
    simp only [zsmul_eq_mul, mul_one, nsmul_eq_mul]
    exact (Rat.den_mul_eq_num a).symm
  obtain ⟨y, hy⟩ := (spectralUnramifiedStageInvariant_mem_range_iff K Ω F hF _).mpr hkill
  refine ⟨galoisUnitH2FiniteStageMap K Ω F y, ?_⟩
  change spectralContinuousH2Invariant K Ω _ = _
  exact (spectralContinuousH2Invariant_stage K Ω F hF y).trans hy

/-- Arithmetic-Frobenius periods give an actual linear equivalence
from original continuous Galois unit H2 to the genuine rational circle. -/
def spectralContinuousH2InvariantEquiv :
    GaloisUnitContinuousH2 (K := K) (Ω := Ω) ≃ₗ[ℤ] AddCircle (1 : ℚ) :=
  LinearEquiv.ofBijective (spectralContinuousH2InvariantLinear K Ω)
    ⟨spectralContinuousH2Invariant_injective K Ω, spectralContinuousH2Invariant_surjective K Ω⟩

/-- The full equivalence evaluates on each original unramified
class as its genuine arithmetic period invariant. -/
theorem spectralContinuousH2InvariantEquiv_stage
    (F : FiniteGaloisIntermediateField K Ω) (hF : SpectralStageUnramified K Ω F)
    (y : GaloisUnitH2FiniteStage K Ω F) :
    spectralContinuousH2InvariantEquiv K Ω (galoisUnitH2FiniteStageMap K Ω F y) =
      spectralUnramifiedStageInvariant K Ω F hF y :=
  spectralContinuousH2Invariant_stage K Ω F hF y

end
end Dubon2026
