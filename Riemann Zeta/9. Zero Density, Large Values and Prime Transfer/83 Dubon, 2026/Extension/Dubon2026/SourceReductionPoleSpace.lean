import Dubon2026.SourceReductionPoleCharts
import Dubon2026.SourceReductionEquationSpecialization

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison. Reduction preserves the actual pole bounds of functions
at a coordinate whose residue is transcendental and whose field degree is
preserved. Chart integrality, integral minimal-polynomial coefficients, their
degree bounds, and the reduced monic equation are all assembled here.
The residue characteristic is unrestricted. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] [CharZero L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_mem_pole_space (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    {D : Divisor L F} (hD : ∀ v, D v = max 0 (-v.ord (x : F)))
    {Db : Divisor (ResidueField A) Fbar} (hDb : ∀ w, Db w = max 0 (-w.ord (R.residue x)))
    (m : ℕ) {f : R.integers} (hf : (f : F) ∈ LSpace (m • D)) :
    R.residue f ∈ LSpace (m • Db) := by
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hcharts := integral_charts_of_pole_bound (x : F)
    (transcendental_of_residue_transcendental R x hx) D hD m hf
  obtain ⟨p, hp, hpdeg, hroot⟩ :=
    exists_monic_equation_of_integral_charts R x hx hfin hdeg f m hcharts.1 hcharts.2
  apply mem_lSpace_iff_ord.mpr
  right
  intro w
  have h := mul_min_ord_residue_le R x f m p hp hpdeg hroot w
  have heq : -(Db w) = min 0 (w.ord (R.residue x)) := by
    rw [hDb]
    omega
  simpa only [Finsupp.smul_apply, nsmul_eq_mul, ← mul_neg, heq] using h

end
end Dubon2026.SourceCurve.RegularProlongation
