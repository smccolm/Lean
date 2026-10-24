import Dubon2026.SourceReductionIntegralPolynomials
import Mathlib.RingTheory.Algebraic.Integral

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
arbitrary-function fiber equality. Native algebraic integral multiples clear
chart denominators. The existing polynomial normalization produces an actual
Gauss-integral denominator with nonzero reduction, so both it and its product
with the original function satisfy the integral-chart identity.
The first step adapts the integral-multiple argument from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective.
The external coefficient-rescaling and residue-polynomial construction are
replaced by the already proved exists_normalize_aeval. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_chart_integral_multiple {L F : Type*} [Field L] [Field F] [Algebra L F]
    (y : F) (hfin : 0 < Module.finrank (IntermediateField.adjoin L ({y} : Set F)) F) (f : F) :
    ∃ p : L[X], p ≠ 0 ∧ IsIntegral (Algebra.adjoin L {y}) (aeval y p * f) := by
  haveI : Module.Finite (IntermediateField.adjoin L ({y} : Set F)) F :=
    Module.finite_of_finrank_pos hfin
  have halg : IsAlgebraic (IntermediateField.adjoin L ({y} : Set F)) f :=
    Algebra.IsAlgebraic.isAlgebraic f
  have halg' : IsAlgebraic (Algebra.adjoin L ({y} : Set F)) f :=
    IsAlgebraic.restrictScalars (S := IntermediateField.adjoin L ({y} : Set F)) (A := F) _ halg
  obtain ⟨z, hz0, hz⟩ := halg'.exists_integral_multiple
  obtain ⟨p, hp⟩ : ∃ p : L[X], aeval y p = (z : F) := Algebra.adjoin_eq_exists_aeval _ y z
  refine ⟨p, ?_, ?_⟩
  · rintro rfl
    apply hz0
    ext
    rw [← hp, map_zero]
    rfl
  · rw [Algebra.smul_def] at hz
    change IsIntegral _ ((z : F) * f) at hz
    rwa [← hp] at hz

theorem exists_regular_chart_integral_multiple
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F)
    (f : R.integers) :
    ∃ q : R.integers, R.residue q ≠ 0 ∧
      IsIntegral (Algebra.adjoin L {(x : F)}) (q : F) ∧
      IsIntegral (Algebra.adjoin L {(x : F)}) ((q * f : R.integers) : F) := by
  obtain ⟨p, hp0, hpf⟩ := exists_chart_integral_multiple (x : F) hfin (f : F)
  obtain ⟨q, hq0, c, -, hqF⟩ := exists_normalize_aeval R x hx p hp0
  have hc : IsIntegral (Algebra.adjoin L {(x : F)}) (algebraMap L F c⁻¹) :=
    (isIntegral_algebraMap (R := L) (A := F) (x := c⁻¹)).tower_top
  have hp : IsIntegral (Algebra.adjoin L {(x : F)}) (aeval (x : F) p) :=
    isIntegral_algebraMap (x := (⟨aeval (x : F) p, aeval_mem_adjoin_singleton L (x : F)⟩ :
      Algebra.adjoin L {(x : F)}))
  refine ⟨q, hq0, ?_, ?_⟩
  · rw [hqF]
    exact hc.mul hp
  · change IsIntegral _ ((q : F) * f)
    rw [hqF, mul_assoc]
    exact hc.mul hpf

end
end Dubon2026.SourceCurve.RegularProlongation
