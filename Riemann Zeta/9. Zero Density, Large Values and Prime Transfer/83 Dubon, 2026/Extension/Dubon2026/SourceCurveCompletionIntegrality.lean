import Dubon2026.SourceCurveCompletionNorm
import Dubon2026.SourceCurveCompletionIntegralAlgebra
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.Integral

/-! The actual completed valuation ring is the integral closure of the
completed base valuation ring. The proved ramification-normalized absolute
value is the unique native spectral norm, so an integral element has an
integral-coefficient monic minimal polynomial. This is the missing ring
input to finite integral bases for residue/field-trace compatibility. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsDedekindDomain WithZero
open scoped Valued NNReal

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E) [FiniteDimensional F E]

/-- Every integral element of the actual completed extension is integral over the base integers. -/
theorem isIntegral_completionIntegers (x : w.adicCompletionIntegers) :
    IsIntegral (w.restrict F).adicCompletionIntegers x := by
  letI := (w.restrict F).completionRankOne
  letI := w.completionRankOne
  haveI := w.finiteDimensional_completion (F := F)
  haveI : Algebra.IsAlgebraic (w.restrict F).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : IsUltrametricDist (w.restrict F).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  have hr : (0 : ℝ) < ((w.ramificationIndex (F := F) : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w.ramificationIndex_pos (F := F)))
  have hxn : ‖(x : w.adicCompletion)‖ ≤ 1 :=
    (Valued.toNormedField.norm_le_one_iff).mpr x.2
  have hsn : spectralNorm (w.restrict F).adicCompletion w.adicCompletion (x : w.adicCompletion) =
      ‖(x : w.adicCompletion)‖ ^ ((w.ramificationIndex (F := F) : ℝ))⁻¹ :=
    (spectralNorm_unique_field_norm_ext (f := w.completionRelativeAbsoluteValue (F := F))
      w.completionRelativeAbsoluteValue_extends (x : w.adicCompletion)).symm
  have hspec : spectralValue (minpoly (w.restrict F).adicCompletion (x : w.adicCompletion)) ≤ 1 := by
    change spectralNorm (w.restrict F).adicCompletion w.adicCompletion (x : w.adicCompletion) ≤ 1
    rw [hsn]
    exact Real.rpow_le_one (norm_nonneg _) hxn hr.le
  have hmon : (minpoly (w.restrict F).adicCompletion (x : w.adicCompletion)).Monic :=
    minpoly.monic (Algebra.IsAlgebraic.isAlgebraic
      (R := (w.restrict F).adicCompletion) (x : w.adicCompletion)).isIntegral
  have hlift : minpoly (w.restrict F).adicCompletion (x : w.adicCompletion) ∈
      Polynomial.lifts (algebraMap (w.restrict F).adicCompletionIntegers (w.restrict F).adicCompletion) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, ?_⟩, rfl⟩
    exact (Valued.toNormedField.norm_le_one_iff).mp ((spectralValue_le_one_iff hmon).mp hspec n)
  obtain ⟨P, hP, -, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hint : IsIntegral (w.restrict F).adicCompletionIntegers (x : w.adicCompletion) := by
    refine ⟨P, hPmon, ?_⟩
    rw [← Polynomial.aeval_def,
      ← Polynomial.aeval_map_algebraMap (w.restrict F).adicCompletion, hP, minpoly.aeval]
  exact (isIntegral_algHom_iff
    (IsScalarTower.toAlgHom (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers w.adicCompletion)
    Subtype.val_injective).mp hint

/-- The actual completed extension integers are precisely the integral closure of the base integers. -/
theorem isIntegralClosure_completionIntegers :
    IsIntegralClosure w.adicCompletionIntegers (w.restrict F).adicCompletionIntegers w.adicCompletion where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    constructor
    · intro hx
      have hxw : IsIntegral w.adicCompletionIntegers x := hx.tower_top
      haveI : IsIntegrallyClosed w.adicCompletionIntegers :=
        Valuation.Integers.isIntegrallyClosed
          (HeightOneSpectrum.adicCompletionIntegers.integers (K := E) (v := w.heightOneSpectrum))
      exact IsIntegrallyClosed.isIntegral_iff.mp hxw
    · rintro ⟨y, rfl⟩
      exact (w.isIntegral_completionIntegers (F := F) y).map
        (IsScalarTower.toAlgHom (w.restrict F).adicCompletionIntegers
          w.adicCompletionIntegers w.adicCompletion)

end Dubon2026.SourceCurve.Place
