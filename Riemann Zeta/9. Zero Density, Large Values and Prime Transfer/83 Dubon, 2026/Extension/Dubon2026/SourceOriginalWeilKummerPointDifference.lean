import Dubon2026.SourceOriginalWeilCoverReciprocity
import Dubon2026.SourceCurveRationalEvaluationEquiv
import Dubon2026.SourceCurveGaloisPlaceCenter

/-! DUB-17/18 -> finite Weil detection -> the auxiliary point-difference class.
This is the actual difference between a cover point and its pullback by the
Kummer automorphism. Closed residues prove degree zero; restriction proves
its norm divisor is zero. Its n-division is a separate upstream obligation.
The detecting-divisor route follows NYLL, Apache-2.0, commit
8c1b16d10afaca09e0dc72753c6575e230d31a55,
WeilPairing/DivisorialPairingToHomInjectiveDivisible.lean, lines 209-408. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "FF" => modularFunctionFieldOver N L
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

/-- The actual degree-zero point difference on the literal Kummer cover. -/
def originalWeilKummerPointDifference (σ : E ≃ₐ[FF] E) (w : Place L E) :
    Divisor.degZero (K := L) (F := E) :=
  ⟨Finsupp.single (w.comapEquiv (σ.restrictScalars L)) 1 - Finsupp.single w 1, by
    change Divisor.degree _ = 0
    rw [map_sub, Divisor.degree_single, Divisor.degree_single]
    have hr (v : Place L E) : Module.finrank L v.ResidueField = 1 :=
      Module.finrank_of_bijective_algebraMap (originalWeilKummerCover_residue_bijective N L n f v)
    rw [hr, hr, sub_self]⟩

theorem originalWeilKummerPointDifference_pushforward (σ : E ≃ₐ[FF] E) (w : Place L E) :
    Divisor.geometricPushforward FF (originalWeilKummerPointDifference N L n f σ w).val = 0 := by
  change Divisor.geometricPushforward FF
    (Finsupp.single (w.comapEquiv (σ.restrictScalars L)) 1 - Finsupp.single w 1) = 0
  rw [map_sub, Divisor.geometricPushforward_single, Divisor.geometricPushforward_single,
    Place.restrict_comapEquiv_galois, sub_self]

theorem originalWeilKummerPoint_eval (σ : E ≃ₐ[FF] E) (w : Place L E) (h : E) (ζ : L)
    (hσ : σ h = algebraMap L E ζ * h) (hm : h ∈ w.toValuationSubring) :
    (w.comapEquiv (σ.restrictScalars L)).rationalEval
      (originalWeilKummerCover_residue_bijective N L n f _) h =
      ζ * w.rationalEval (originalWeilKummerCover_residue_bijective N L n f w) h := by
  have he : σ h ∈ w.toValuationSubring := by
    rw [hσ]
    exact mul_mem (w.algebraMap_mem' ζ) hm
  rw [w.rationalEval_comapEquiv_of_mem (σ.restrictScalars L)
    (originalWeilKummerCover_residue_bijective N L n f w)
    (originalWeilKummerCover_residue_bijective N L n f _) h he]
  change w.rationalEval _ (σ h) = _
  rw [hσ, w.rationalEval_mul_of_mem _ (w.algebraMap_mem' ζ) hm,
    w.rationalEval_algebraMap]

end
end Dubon2026.SourceFunctionField
