import Dubon2026.AdelicRaisingEnvelopingSpan
import Dubon2026.WeightLadderIrreducibility

/-! # Irreducibility of the original infinitesimal cyclic lowest-weight module -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem positiveWeight_lowering_ne_zero {k : ℤ} (hk : 0 < k) (n : ℕ) :
    ((n : ℂ) + 1) * (-(k : ℂ) - n) ≠ 0 := by
  have hp : (k : ℂ) + n ≠ 0 := by
    exact_mod_cast (show (k + (n : ℤ)) ≠ 0 from
      (add_pos_of_pos_of_nonneg hk (Int.natCast_nonneg n)).ne')
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  apply mul_ne_zero hn
  have hn' : -(k : ℂ) - n = -((k : ℂ) + n) := by ring
  rw [hn']
  exact neg_ne_zero.mpr hp

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original enveloping cyclic lowest-weight module is irreducible as an actual complex matrix Lie module for every nonzero positive-weight cusp form. -/
theorem adelicRaisingLieSubmodule_irreducible (hf : f ≠ 0) (hk : 0 < k) :
    LieModule.IsIrreducible ℂ ComplexSl2 (adelicRaisingLieSubmodule f hf) := by
  let b : Module.Basis ℕ ℂ (adelicRaisingLieSubmodule f hf) := adelicRaisingBasis f hf hk
  have hb (n : ℕ) : (b n).val = adelicRaisingJet f n := adelicRaisingBasis_apply f hf hk n
  apply weightLadder_lie_irreducible compactSl2H compactSl2E compactSl2F b
    (fun n => (k : ℂ) + 2 * n) (fun n => ((n : ℂ) + 1) * (-(k : ℂ) - n))
  · exact b.ne_zero 0
  · exact b.span_eq
  · intro m n he
    have hn : (m : ℂ) = n := by linear_combination he / 2
    exact_mod_cast hn
  · intro n
    apply Subtype.ext
    change ⁅compactSl2H, (b n).val⁆ = ((k : ℂ) + 2 * n) • (b n).val
    exact ((congrArg (fun w : adelicRealSmoothSubmodule f => ⁅compactSl2H, w⁆) (hb n)).trans
      (adelicRaisingJet_weight f hf n)).trans
        (congrArg (fun w : adelicRealSmoothSubmodule f => ((k : ℂ) + 2 * n) • w) (hb n)).symm
  · intro n
    apply Subtype.ext
    change ⁅compactSl2E, (b n).val⁆ = (b (n + 1)).val
    exact ((congrArg (fun w : adelicRealSmoothSubmodule f => ⁅compactSl2E, w⁆) (hb n)).trans
      (adelicRaisingJet_raise f n)).trans (hb (n + 1)).symm
  · intro n
    apply Subtype.ext
    change ⁅compactSl2F, (b (n + 1)).val⁆ = (((n : ℂ) + 1) * (-(k : ℂ) - n)) • (b n).val
    exact ((congrArg (fun w : adelicRealSmoothSubmodule f => ⁅compactSl2F, w⁆) (hb (n + 1))).trans
      (adelicRaisingJet_lower f hf n)).trans
        (congrArg (fun w : adelicRealSmoothSubmodule f =>
          (((n : ℂ) + 1) * (-(k : ℂ) - n)) • w) (hb n)).symm
  · exact positiveWeight_lowering_ne_zero hk

/-- Every Lie submodule of the actual original lowest-weight cyclic module is zero or the whole original module. -/
theorem adelicRaisingLieSubmodule_eq_bot_or_top (hf : f ≠ 0) (hk : 0 < k)
    (p : LieSubmodule ℂ ComplexSl2 (adelicRaisingLieSubmodule f hf)) : p = ⊥ ∨ p = ⊤ := by
  letI := adelicRaisingLieSubmodule_irreducible f hf hk
  exact IsSimpleOrder.eq_bot_or_eq_top p

end
end Dubon2026
