import Dubon2026.SourceOriginalTateCoordinateLift
import Dubon2026.SourceOriginalTateWeilLinearity

/-! DUB-17/18 -> determinant -> original Tate Weil nondegeneracy.
The existing period comparison supplies all finite-coordinate lifts.
The remaining explicit hypothesis is finite-level Weil detection; its
auxiliary-cover divisibility proof remains open and is not hidden here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve OriginalChart
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

theorem originalTateWeilPairing_detects_of_finiteLevel
    (hfinite : ∀ (k : ℕ) (a : originalJZeroTorsion N (p ^ k)), a ≠ 0 →
      ∃ b, originalWeilPairing N Qbar (p ^ k) a b ≠ 1)
    (x : TateModule p (originalJZero N)) (hx : x ≠ 0) :
    ∃ y, originalTateWeilPairing N p x y ≠ 0 := by
  have hk : ∃ k, originalTateTorsionCoordinate N p k x ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply Subtype.ext
    funext k
    exact congrArg Subtype.val (h k)
  obtain ⟨k, hk⟩ := hk
  obtain ⟨q, hq⟩ := hfinite k _ hk
  obtain ⟨y, hy⟩ := originalTateTorsionCoordinate_surjective N p k q
  refine ⟨y, fun hzero => hq ?_⟩
  have hz := congrArg (fun z : TateModule p (Additive Qbarˣ) =>
    Additive.toMul ((z : ℕ → Additive Qbarˣ) k)) hzero
  simp only [originalTateWeilPairing_coordinate, toMul_ofMul,
    TateModule.coe_zero, Pi.zero_apply, toMul_zero, hy] at hz
  exact Subtype.ext hz

theorem originalTateWeilBilinear_injective_of_finiteLevel
    (hfinite : ∀ (k : ℕ) (a : originalJZeroTorsion N (p ^ k)), a ≠ 0 →
      ∃ b, originalWeilPairing N Qbar (p ^ k) a b ≠ 1) :
    Function.Injective (originalTateWeilBilinear N p) := by
  apply (injective_iff_map_eq_zero (originalTateWeilBilinear N p)).mpr
  intro x hx
  by_contra hne
  obtain ⟨y, hy⟩ := originalTateWeilPairing_detects_of_finiteLevel N p hfinite x hne
  exact hy (congrArg (fun f => f y) hx)

end
end Dubon2026.SourceFunctionField
