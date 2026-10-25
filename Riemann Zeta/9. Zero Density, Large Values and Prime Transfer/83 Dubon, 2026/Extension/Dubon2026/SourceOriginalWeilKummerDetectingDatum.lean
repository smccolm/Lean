import Dubon2026.SourceOriginalWeilKummerMoving
import Dubon2026.SourceOriginalWeilKummerNormAvoidance
import Dubon2026.SourceOriginalWeilKummerMovedDatum

/-! DUB-17/18 -> finite Weil nondegeneracy -> actual detecting divisor.
Adapt the norm argument reviewed in NYLL, Apache-2.0, commit
8c1b16d10afaca09e0dc72753c6575e230d31a55,
WeilPairing/DivisorialPairingToHomInjectiveDivisible.lean, lines 209-408.
Upstream copyright 2026 Anthropic, PBC; NYLL adaptation by Naganori Yamaguchi.
All moving, norm, residue and reciprocity inputs are supplied by native proofs.
Only n-division of the specified actual point-difference class remains assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n] (f : modularFunctionFieldOver N L)
local notation "FF" => modularFunctionFieldOver N L
local notation "EE" => Polynomial.SplittingField (X ^ n - C f)

theorem exists_originalWeilKummer_detecting_datum
    (D : Divisor.degZero (K := L) (F := FF)) (hf : f ≠ 0)
    (hfD : ∀ v : Place L FF, v.ord f = (n : ℤ) * D.val v)
    (h : EE) (hh : h ^ n = algebraMap FF EE f)
    (σ : EE ≃ₐ[FF] EE) (ζ : L) (hσ : σ h = algebraMap L EE ζ * h)
    (w : Place L EE)
    (hdiv : ∃ y : Pic0 L EE, n • y = Pic0.mk (originalWeilKummerPointDifference N L n f σ w)) :
    ∃ d : OriginalWeilDatum N L n, d.classLeft.val = Pic0.mk D ∧ d.pairing = ζ⁻¹ := by
  obtain ⟨B, u, hu, hU, hnorm, hnormD⟩ :=
    exists_originalWeilKummerDivision_norm_data N L n f σ w hdiv
  obtain ⟨D', r, hr, hD', hrD, hdisj, hA, hB, hw, hfiber, huSupport⟩ :=
    exists_originalWeilKummer_norm_avoiding N L n f D σ w B.val u hU
  obtain ⟨d, hd, hpair⟩ := exists_originalWeilKummer_moved_datum N L n f D D' hf hfD h hh
    σ ζ hσ w B.val u hu hU hnorm hnormD r hr hrD hdisj hA hB hw hfiber huSupport
  exact ⟨d, hd.trans hD', hpair⟩

end
end Dubon2026.SourceFunctionField
