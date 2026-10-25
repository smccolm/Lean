import Dubon2026.SourceOriginalWeilPairingDescent

/-! DUB-17/18 -> the detecting datum -> its original Picard class.
This is the definitional constructor bridge for the literal original Weil
datum. The actual norm-detecting consumer supplies every order and support
proof; this lemma introduces no independent mathematical assumption there. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) [NeZero n]
local notation "FF" => modularFunctionFieldOver N L

theorem exists_originalWeilDatum_of_degree_zero
    (D : Divisor.degZero (K := L) (F := FF)) (E : Divisor L FF) (g h : FF)
    (hg : g ≠ 0) (hh : h ≠ 0)
    (hgD : ∀ v : Place L FF, v.ord g = n * D.val v)
    (hhE : ∀ v : Place L FF, v.ord h = n * E v)
    (hdisj : ∀ v : Place L FF, D.val v = 0 ∨ E v = 0) :
    ∃ d : OriginalWeilDatum N L n, d.classLeft.val = Pic0.mk D ∧
      d.pairing = originalDivisorEval N L g E / originalDivisorEval N L h D.val := by
  exact ⟨{
    D₁ := D.val
    D₂ := E
    f₁ := g
    f₂ := h
    f₁_ne_zero := hg
    f₂_ne_zero := hh
    ord_f₁ := hgD
    ord_f₂ := hhE
    disjoint := hdisj }, rfl, rfl⟩

end
end Dubon2026.SourceFunctionField
