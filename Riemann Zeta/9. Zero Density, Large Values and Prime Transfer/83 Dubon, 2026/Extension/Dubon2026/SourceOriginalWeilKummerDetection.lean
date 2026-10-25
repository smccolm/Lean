import Dubon2026.SourceOriginalWeilKummerDetectingDatum
import Dubon2026.SourceOriginalAdelicQuotients
import Dubon2026.SourceCurveFiberResidueConstants

/-! DUB-17/18 -> finite Weil nondegeneracy -> the exact remaining cover input.
The nonzero original Picard torsion class supplies the actual Kummer function,
root and nontrivial multiplier. Native lying-over supplies a cover point.
The proved detecting datum and actual pairing descent give a nontrivial
partner, conditional only on the displayed point-difference division input.
This does not establish that the auxiliary division exists. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n]
local notation "FF" => modularFunctionFieldOver N L

theorem originalWeilPairing_detects_of_kummer_point_division
    (hdivision : ∀ a : FF, a ≠ 0 →
      ∀ (σ : Polynomial.SplittingField (X ^ n - C a : FF[X]) ≃ₐ[FF]
        Polynomial.SplittingField (X ^ n - C a : FF[X]))
        (w : Place L (Polynomial.SplittingField (X ^ n - C a : FF[X]))),
        ∃ y : Pic0 L (Polynomial.SplittingField (X ^ n - C a : FF[X])),
          n • y = Pic0.mk (K := L) (F := Polynomial.SplittingField (X ^ n - C a : FF[X])) (originalWeilKummerPointDifference N L n a σ w))
    (x : Pic0.torsion (K := L) (F := FF) n) (hx : x ≠ 0) :
    ∃ y : Pic0.torsion (K := L) (F := FF) n, originalWeilPairing N L n x y ≠ 1 := by
  obtain ⟨D, f, hD, hf, hfD, _, h, σ, ζ, hζ, hh, hσ⟩ :=
    originalPic0_nonzero_torsion_kummer_cover N L n x hx
  obtain ⟨v⟩ := nonempty_original_places N L
  obtain ⟨w, _⟩ := v.exists_fiberPlace (E := Polynomial.SplittingField (X ^ n - C f))
  obtain ⟨d, hd, hval⟩ := exists_originalWeilKummer_detecting_datum N L n f D hf hfD h hh
    σ ζ hσ w (hdivision f hf σ w)
  have hleft : d.classLeft = x := Subtype.ext (hd.trans hD)
  refine ⟨d.classRight, ?_⟩
  intro he
  have hc := congrArg (fun z : rootsOfUnity n L => ((z : Lˣ) : L)) he
  change ((originalWeilPairing N L n x d.classRight : Lˣ) : L) = 1 at hc
  have hp := originalWeilPairing_eq_pairing N L n d
  rw [hleft] at hp
  exact hζ (inv_eq_one.mp (hval.symm.trans (hp.symm.trans hc)))

end
end Dubon2026.SourceFunctionField
