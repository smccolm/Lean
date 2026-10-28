import Definitions.Def_AlgebraicCurve_Differentials
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_eq_one
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_ordDiff_smul
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

noncomputable section
open KaehlerDifferential

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.diffCoeff Place.ordDiff_def Place Place.diffCoeff_smul_D_of_ord_ne_zero Place.diffCoeff_smul_D_eq"
namespace FF2R4A
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section R3grade
variable [CharZero K] (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
theorem ordDiff_smul (v : Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have h1 : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt v.exists_ord_eq_one]; exact one_ne_zero
  set a := Place.diffCoeff v.uniformizer_alt ω with ha
  have hωa : a • D K F v.uniformizer_alt = ω := Place.diffCoeff_smul_D_of_ord_ne_zero x v h1 ω
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, zero_smul] at hωa; exact hω hωa.symm
  rw [Place.ordDiff_def, Place.ordDiff_def, ← ha, ← hωa, smul_smul,
    Place.diffCoeff_smul_D_eq x v h1, v.ord_mul hg ha0]

end R3grade

end AlgebraicCurve.FF2R4A

end

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω :=
  AlgebraicCurve.FF2R4A.ordDiff_smul x v hg hω
