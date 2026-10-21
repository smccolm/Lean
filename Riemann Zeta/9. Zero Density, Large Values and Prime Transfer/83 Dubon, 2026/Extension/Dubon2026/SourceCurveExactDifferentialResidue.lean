import Dubon2026.SourceCurveCoordinateDerivation
import Dubon2026.SourceCurveCanonicalResidueData
import Dubon2026.SourceCurveIntegralDerivatives

/-! DUB-17/18 -> function-field Riemann--Roch -> global residue identity
-> local compatibility of residues with differentials. Exact differentials
have zero local residue. The actual coordinate derivation and proved
integral derivative bound reduce this to pure negative uniformizer powers;
finite principal-part uniqueness completes the argument without completion.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem localResidueScalar_coordinateDerivation_eq_zero
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f : F) :
    v.localResidueScalar (v.coordinateDerivation f) = 0 := by
  have he : v.localResidueScalar.comp v.coordinateDerivation.toLinearMap = 0 := by
    apply v.linearMap_zero_of_integral_and_poles hres
    · intro g hg
      exact v.localResidueScalar_of_mem (v.differentialCoeff_D_mem_of_mem hg)
    · intro n
      change v.localResidueScalar (v.coordinateDerivation (v.uniformizer ^ (-(n + 1 : ℤ)))) = 0
      rw [v.coordinateDerivation_zpow]
      have hn : -(n + 1 : ℤ) - 1 = -((n + 1) + 1 : ℤ) := by omega
      rw [hn]
      rw [← map_intCast (algebraMap K F) (-(n + 1 : ℤ)), ← Algebra.smul_def, map_smul]
      have hp := v.localResidueScalar_neg_pow (n + 1)
      rw [if_neg (Nat.succ_ne_zero n)] at hp
      simp only [Nat.cast_add, Nat.cast_one] at hp
      rw [hp, smul_zero]
  exact LinearMap.congr_fun he f

theorem canonicalLocalResidueData_exactDifferential
    (hres : Function.Bijective (algebraMap K v.ResidueField))
    (d : v.CanonicalLocalResidueDataK) (f : F) :
    d.res (v.differentialCoeff (D K F f)) = 0 := by
  rw [v.canonicalLocalResidueData_res_unique hres d]
  change algebraMap K v.ResidueField (v.localResidueScalar (v.coordinateDerivation f)) = 0
  rw [v.localResidueScalar_coordinateDerivation_eq_zero hres.surjective, map_zero]

end
end Dubon2026.SourceCurve.Place
