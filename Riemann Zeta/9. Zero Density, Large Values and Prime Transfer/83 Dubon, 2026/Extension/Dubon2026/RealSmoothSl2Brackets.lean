import Dubon2026.RealSmoothInfinitesimalTangents
import Dubon2026.RealConjugatedCurveTangents
import Dubon2026.RealSmoothSemidirectBracket
import Mathlib.Tactic.NoncommRing

/-! # Full original real infinitesimal bracket relations on genuine smooth vectors -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup
open scoped MatrixGroups ContDiff

private theorem complex_neg_one_smul {W : Type*} [AddCommGroup W] [Module ℂ W] (w : W) :
    ((-1 : ℝ) : ℂ) • w = -w := by simp

private theorem third_bracket_of_conjugation {R : Type*} [Ring R] (A U F : R)
    (hAU : A * U - U * A = U) (hAF : A * F - F * A = -F)
    (hC : (A - U) * (F + (A + A) - U) - (F + (A + A) - U) * (A - U) =
      -(F + (A + A) - U)) : U * F - F * U = A + A := by
  linear_combination (norm := noncomm_ring) hAF + hAU - hC

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
  (ρ : Representation ℂ SL(2, ℝ) V) (L : SL(2, ℝ) → V →L[ℝ] V)
  (hL : ∀ g v, L g v = ρ g v)

local notation "D" => realMatrixSmoothInfinitesimal ρ L hL

/-- Original upper and lower infinitesimals have commutator twice the original geodesic infinitesimal. -/
theorem realMatrixSmoothInfinitesimal_upper_lower :
    D realUpperUnipotent realUpperUnipotent_entries_contDiff *
        D realLowerUnipotent realLowerUnipotent_entries_contDiff -
      D realLowerUnipotent realLowerUnipotent_entries_contDiff *
        D realUpperUnipotent realUpperUnipotent_entries_contDiff =
      (2 : ℂ) • D realGeodesicCurve realGeodesicCurve_entries_contDiff := by
  let A := D realGeodesicCurve realGeodesicCurve_entries_contDiff
  let U := D realUpperUnipotent realUpperUnipotent_entries_contDiff
  let F := D realLowerUnipotent realLowerUnipotent_entries_contDiff
  have hAU : A * U - U * A = U := by
    simpa only [Complex.ofReal_one, one_smul] using
      realMatrixSmoothInfinitesimal_semidirect ρ L hL realGeodesicCurve realUpperUnipotent
        realGeodesicCurve_entries_contDiff realUpperUnipotent_entries_contDiff
        realGeodesicCurve_zero 1 (fun s t => by
          simpa only [one_mul] using realGeodesicCurve_mul_upper s t)
  have hAF : A * F - F * A = -F := by
    have he := realMatrixSmoothInfinitesimal_semidirect ρ L hL realGeodesicCurve realLowerUnipotent
      realGeodesicCurve_entries_contDiff realLowerUnipotent_entries_contDiff
      realGeodesicCurve_zero (-1) (fun s t => by
        simpa only [neg_one_mul] using realGeodesicCurve_mul_lower s t)
    exact he.trans (complex_neg_one_smul F)
  let g := realUpperUnipotent 1
  have hCA : D (realConjugatedCurve g realGeodesicCurve)
      (realConjugatedCurve_entries_contDiff g realGeodesicCurve realGeodesicCurve_entries_contDiff) =
        A - U := by
    have he := realMatrixSmoothInfinitesimal_tangent ρ L hL
      (realConjugatedCurve g realGeodesicCurve)
      (realConjugatedCurve_entries_contDiff g realGeodesicCurve realGeodesicCurve_entries_contDiff)
      (realConjugatedCurve_zero g realGeodesicCurve realGeodesicCurve_zero)
      (1 / 2) 0 (-1) (realUpperConjugatedGeodesic_entry_hasDerivAt 0 0)
      (realUpperConjugatedGeodesic_entry_hasDerivAt 1 0) (realUpperConjugatedGeodesic_entry_hasDerivAt 0 1)
    rw [complex_neg_one_smul U] at he
    simpa [A, U, sub_eq_add_neg] using he
  have hCF : D (realConjugatedCurve g realLowerUnipotent)
      (realConjugatedCurve_entries_contDiff g realLowerUnipotent realLowerUnipotent_entries_contDiff) =
        F + (A + A) - U := by
    have he := realMatrixSmoothInfinitesimal_tangent ρ L hL
      (realConjugatedCurve g realLowerUnipotent)
      (realConjugatedCurve_entries_contDiff g realLowerUnipotent realLowerUnipotent_entries_contDiff)
      (realConjugatedCurve_zero g realLowerUnipotent realLowerUnipotent_zero)
      1 1 (-1) (realUpperConjugatedLower_entry_hasDerivAt 0 0)
      (realUpperConjugatedLower_entry_hasDerivAt 1 0) (realUpperConjugatedLower_entry_hasDerivAt 0 1)
    rw [complex_neg_one_smul U] at he
    simpa [A, U, F, sub_eq_add_neg, two_smul ℂ] using he
  have hC : (A - U) * (F + (A + A) - U) - (F + (A + A) - U) * (A - U) =
      -(F + (A + A) - U) := by
    have he := realMatrixSmoothInfinitesimal_semidirect ρ L hL
      (realConjugatedCurve g realGeodesicCurve) (realConjugatedCurve g realLowerUnipotent)
      (realConjugatedCurve_entries_contDiff g realGeodesicCurve realGeodesicCurve_entries_contDiff)
      (realConjugatedCurve_entries_contDiff g realLowerUnipotent realLowerUnipotent_entries_contDiff)
      (realConjugatedCurve_zero g realGeodesicCurve realGeodesicCurve_zero) (-1)
      (realConjugatedCurve_semidirect g realGeodesicCurve realLowerUnipotent (-1)
        (fun s t => by simpa only [neg_one_mul] using realGeodesicCurve_mul_lower s t))
    rw [hCA, hCF] at he
    exact he.trans (complex_neg_one_smul (F + (A + A) - U))
  simpa only [two_smul ℂ] using third_bracket_of_conjugation A U F hAU hAF hC

/-- The actual compact infinitesimal is exactly original upper minus original lower. -/
theorem realMatrixSmoothInfinitesimal_compact :
    D realRotationCurve realRotationCurve_entries_contDiff =
      D realUpperUnipotent realUpperUnipotent_entries_contDiff -
        D realLowerUnipotent realLowerUnipotent_entries_contDiff := by
  have he := realMatrixSmoothInfinitesimal_tangent ρ L hL realRotationCurve
    realRotationCurve_entries_contDiff realRotationCurve_zero 0 (-1) 1
    (realRotationCurve_entry_hasDerivAt 0 0) (realRotationCurve_entry_hasDerivAt 1 0)
    (realRotationCurve_entry_hasDerivAt 0 1)
  rw [complex_neg_one_smul (D realLowerUnipotent realLowerUnipotent_entries_contDiff)] at he
  simpa [sub_eq_add_neg, add_comm] using he

end
end Dubon2026
