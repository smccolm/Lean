import Dubon2026.SourceReductionSingleChartMonic
import Dubon2026.SourceReductionEquationSpecialization

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
comparison of orders in one reduction fiber. Integral chart functions remain
integral after reduction. The existing single-chart monic equation and its
proved residue specialization give this directly, without the external
lifted-basis and Gauss-coordinate argument or a chart-surjectivity premise.
This is the integrality input to the required pole-cancellation argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem isIntegral_residue_of_integral_chart
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers) (hf : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F)) :
    IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) (R.residue f) := by
  obtain ⟨p, hp, hroot⟩ := exists_monic_equation_of_integral_chart R x hx hfin hdeg f hf
  let B := Algebra.adjoin (ResidueField A) ({R.residue x} : Set Fbar)
  let y : B := ⟨R.residue x, Algebra.self_mem_adjoin_singleton _ _⟩
  let φ : Polynomial A →+* B := Polynomial.eval₂RingHom
    ((algebraMap (ResidueField A) B).comp (IsLocalRing.residue A)) y
  refine ⟨p.map φ, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap B Fbar).comp φ =
      Polynomial.eval₂RingHom (resConst A Fbar) (R.residue x) := by
    ext a <;> simp [φ, y, resConst]
  rw [hcomp]
  exact eval₂_residue_eq_zero R x f p hroot

end
end Dubon2026.SourceCurve.RegularProlongation
