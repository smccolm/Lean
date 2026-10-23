import Dubon2026.SourceOriginalCuspPeriodLattice
import Dubon2026.SourceOriginalFinitePlaceExhaustion

/-! DUB-17/18 -> original Picard-period Hecke comparison -> reverse
period-lattice inclusion. The actual normalized primitive vector descends
to finite original places modulo the actual modular periods. Existing
orbit separation and finite-place exhaustion prove independence and
existence of the analytic representative. No value is assigned at a cusp.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup KaehlerDifferential
open scoped MatrixGroups
variable (N : ℕ) [NeZero N]

/-- The actual normalized primitive vector modulo the native modular period lattice. -/
def originalAnalyticCuspClass {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) (τ : ℍ) :
    (Fin n → ℂ) ⧸ originalCuspPeriodLattice N b :=
  (originalCuspPeriodLattice N b).mkQ
    (fun i => sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) τ -
      sourceWeightTwoPrimitive 1 (originalRegularCuspEquiv N (b i)) I)

theorem originalAnalyticCuspClass_eq_of_place_eq {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {τ τ' : ℍ} (he : originalAnalyticPlace N τ = originalAnalyticPlace N τ') :
    originalAnalyticCuspClass N b τ = originalAnalyticCuspClass N b τ' := by
  obtain ⟨γ, rfl⟩ := (originalAnalyticPlace_eq_iff_gamma0_orbit N τ τ').mp he
  apply (Submodule.Quotient.eq _).mpr
  have hm : (fun i => sourceWeightTwoPeriodValue (Gamma0 N)
      (originalRegularCuspEquiv N (b i)) γ) ∈ originalCuspPeriodLattice N b :=
    Submodule.subset_span ⟨γ, rfl⟩
  convert (originalCuspPeriodLattice N b).neg_mem hm using 1
  funext i
  simp only [Pi.sub_apply, Pi.neg_apply, original_cusp_primitive_period]
  ring

/-- The actual modular primitive class of a finite original place, using its proved analytic realization. -/
def originalFiniteCuspClass {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P : {v : Place ℂ (modularFunctionFieldOver N ℂ) // jOver N ℂ ∈ v.toValuationSubring}) :
    (Fin n → ℂ) ⧸ originalCuspPeriodLattice N b :=
  originalAnalyticCuspClass N b (exists_original_analytic_place_eq N P.val P.property).choose

theorem originalFiniteCuspClass_apply {n : ℕ}
    (b : Fin n → regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (P : {v : Place ℂ (modularFunctionFieldOver N ℂ) // jOver N ℂ ∈ v.toValuationSubring})
    (τ : ℍ) (he : originalAnalyticPlace N τ = P.val) :
    originalFiniteCuspClass N b P = originalAnalyticCuspClass N b τ :=
  originalAnalyticCuspClass_eq_of_place_eq N b
    ((exists_original_analytic_place_eq N P.val P.property).choose_spec.trans he.symm)

end
end Dubon2026.SourceFunctionField.OriginalChart
