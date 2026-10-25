import Dubon2026.SourceOriginalWeilCoverPointDivision
import Dubon2026.SourceOriginalWeilKummerDetection

/-! DUB-17/18 -> original pairing nondegeneracy. The actual nonzero complex
torsion class supplies its n-divisible radicand orders; the now-proved
unramified cover point division discharges the sole remaining input in the
existing NYLL norm-detection argument. No arbitrary-cover divisibility premise
is introduced. Arithmetic descent and Tate/component consumers remain.
Adapted from NYLL, Apache-2.0, commit 8c1b16d10afaca09e0dc72753c6575e230d31a55,
with the existing native moving, norm and reciprocity proofs. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N]
variable (n : ℕ) [NeZero n]
local notation "FF" => modularFunctionFieldOver N ℂ


theorem originalComplexWeilPairing_detects
    (x : Pic0.torsion (K := ℂ) (F := FF) n) (hx : x ≠ 0) :
    ∃ y : Pic0.torsion (K := ℂ) (F := FF) n, originalWeilPairing N ℂ n x y ≠ 1 := by
  obtain ⟨D, f, hD, hf, hfD, _, h, σ, ζ, hζ, hh, hσ⟩ :=
    originalPic0_nonzero_torsion_kummer_cover N ℂ n x hx
  obtain ⟨v⟩ := nonempty_original_places N ℂ
  obtain ⟨w, _⟩ := v.exists_fiberPlace (E := Polynomial.SplittingField (X ^ n - C f))
  obtain ⟨d, hd, hval⟩ := exists_originalWeilKummer_detecting_datum N ℂ n f D hf hfD h hh
    σ ζ hσ w (OriginalWeilCoverChart.cover_point_difference_has_division N n f D.val hf hfD σ w)
  have hleft : d.classLeft = x := Subtype.ext (hd.trans hD)
  refine ⟨d.classRight, ?_⟩
  intro he
  have hc := congrArg (fun z : rootsOfUnity n ℂ => ((z : ℂˣ) : ℂ)) he
  change ((originalWeilPairing N ℂ n x d.classRight : ℂˣ) : ℂ) = 1 at hc
  have hp := originalWeilPairing_eq_pairing N ℂ n d
  rw [hleft] at hp
  exact hζ (inv_eq_one.mp (hval.symm.trans (hp.symm.trans hc)))

end
end Dubon2026.SourceFunctionField
