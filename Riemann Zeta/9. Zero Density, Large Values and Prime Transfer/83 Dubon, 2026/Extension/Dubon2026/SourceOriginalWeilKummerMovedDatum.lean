import Dubon2026.SourceOriginalWeilKummerMoving
import Dubon2026.SourceCurveKummerMovedEvaluation
import Dubon2026.SourceOriginalWeilDatumAssembly

/-! DUB-17/18 -> finite Weil detection -> assembly after actual divisor moving.
The caller supplies the norm and avoiding representatives constructed by the
preceding native theorems. Their corrected functions give the literal Weil
datum, its original class and the inverse-multiplier pairing value. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial IntermediateField
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n] (f : modularFunctionFieldOver N L)
local notation "FF" => modularFunctionFieldOver N L
local notation "EE" => Polynomial.SplittingField (X ^ n - C f)

theorem exists_originalWeilKummer_moved_datum
    (D D' : Divisor.degZero (K := L) (F := FF)) (hf : f ≠ 0)
    (hfD : ∀ v : Place L FF, v.ord f = (n : ℤ) * D.val v)
    (h : EE) (hh : h ^ n = algebraMap FF EE f)
    (σ : EE ≃ₐ[FF] EE) (ζ : L) (hσ : σ h = algebraMap L EE ζ * h)
    (w : Place L EE) (B : Divisor L EE) (u : EE) (hu : u ≠ 0)
    (hU : ∀ q : Place L EE, q.ord u =
      (originalWeilKummerPointDifference N L n f σ w).val q + n * B q)
    (hnorm : Algebra.norm FF u ≠ 0)
    (hnormD : ∀ v : Place L FF, v.ord (Algebra.norm FF u) = n * Divisor.geometricPushforward FF B v)
    (r : FF) (hr : r ≠ 0) (hrD : ∀ v : Place L FF, v.ord r = D'.val v - D.val v)
    (hdisj : ∀ v : Place L FF, D'.val v = 0 ∨ Divisor.geometricPushforward FF B v = 0)
    (hA : ∀ q : Place L EE, q ∈ (originalWeilKummerPointDifference N L n f σ w).val.support →
      D'.val (q.restrict FF) = 0)
    (hB : ∀ q : Place L EE, q ∈ B.support → D'.val (q.restrict FF) = 0)
    (hw : D'.val (w.restrict FF) = 0)
    (hfiber : ∀ v : Place L FF, v ∈ D'.val.support → ∀ q : Place L EE,
      q.restrict FF = v → q.ord u = 0)
    (huSupport : ∀ q : Place L EE, q.ord u ≠ 0 → D'.val (q.restrict FF) = 0) :
    ∃ d : OriginalWeilDatum N L n, d.classLeft.val = Pic0.mk D' ∧ d.pairing = ζ⁻¹ := by
  let t := algebraMap FF EE (jOver N L)
  haveI : FiniteDimensional L⟮t⟯ EE := (originalWeilKummerCover_finite_coordinate N L n f).2
  haveI := originalWeilKummerCover_curve N L n f
  obtain ⟨g, hg, hgD, hratio⟩ := exists_kummer_moved_evaluation t
    (original_place_residue_algebraMap_bijective N L)
    (originalWeilKummerCover_residue_bijective N L n f) n D.val D'.val
    (originalWeilKummerPointDifference N L n f σ w).val B f hf hfD h hh σ ζ hσ w u hu hU
    r hr hrD hA hB hw hfiber huSupport
    (fun H hH hHσ hHw => originalWeilKummerPointDifference_eval N L n f σ w H hH ζ hHσ hHw)
  obtain ⟨d, hd, hpair⟩ := exists_originalWeilDatum_of_degree_zero N L n D'
    (Divisor.geometricPushforward FF B) g (Algebra.norm FF u) hg hnorm hgD hnormD hdisj
  exact ⟨d, hd, hpair.trans hratio⟩

end
end Dubon2026.SourceFunctionField
