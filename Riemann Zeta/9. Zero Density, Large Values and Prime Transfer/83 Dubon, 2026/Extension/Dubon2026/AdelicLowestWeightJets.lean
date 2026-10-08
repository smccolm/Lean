import Dubon2026.AdelicCompactWeightModule
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # The original nonzero raising jets and their exact compact weights -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual nth raising derivative of the original smooth cusp generator. -/
def adelicRaisingJet (n : ℕ) : adelicRealSmoothSubmodule f :=
  ((adelicComplexSl2Action f compactSl2E) ^ n) (adelicSmoothGenerator f)

/-- The zeroth actual raising derivative is the original generator itself. -/
theorem adelicRaisingJet_zero : adelicRaisingJet f 0 = adelicSmoothGenerator f := rfl

/-- Applying the actual raising matrix gives the next original raising derivative. -/
theorem adelicRaisingJet_raise (n : ℕ) :
    ⁅compactSl2E, adelicRaisingJet f n⁆ = adelicRaisingJet f (n + 1) := by
  simp only [adelicRaisingJet, pow_succ', Module.End.mul_apply, adelicSmoothComplexLie_apply]

/-- Every actual raising derivative has its exact original compact Cartan weight. -/
theorem adelicRaisingJet_weight (hf : f ≠ 0) (n : ℕ) :
    ⁅compactSl2H, adelicRaisingJet f n⁆ = ((k : ℂ) + 2 * n) • adelicRaisingJet f n := by
  have he := (adelicSmoothGenerator_primitive f hf).lie_h_pow_toEnd_f n
  change ⁅-compactSl2H, adelicRaisingJet f n⁆ = (-(k : ℂ) - 2 * n) • adelicRaisingJet f n at he
  rw [neg_lie] at he
  calc
    ⁅compactSl2H, adelicRaisingJet f n⁆ = -((-(k : ℂ) - 2 * n) • adelicRaisingJet f n) :=
      neg_eq_iff_eq_neg.mp he
    _ = (-(-(k : ℂ) - 2 * n)) • adelicRaisingJet f n :=
      (neg_smul (-(k : ℂ) - 2 * n) (adelicRaisingJet f n)).symm
    _ = ((k : ℂ) + 2 * n) • adelicRaisingJet f n := by congr 1; ring

/-- The actual lowering derivative has the exact nonzero scalar recurrence on original raising derivatives. -/
theorem adelicRaisingJet_lower (hf : f ≠ 0) (n : ℕ) :
    ⁅compactSl2F, adelicRaisingJet f (n + 1)⁆ =
      (((n : ℂ) + 1) * (-(k : ℂ) - n)) • adelicRaisingJet f n := by
  exact (adelicSmoothGenerator_primitive f hf).lie_e_pow_succ_toEnd_f n

/-- Every original raising derivative is nonzero for a nonzero positive-weight cusp form. -/
theorem adelicRaisingJet_ne_zero (hf : f ≠ 0) (hk : 0 < k) (n : ℕ) : adelicRaisingJet f n ≠ 0 := by
  induction n with
  | zero =>
      intro he
      exact adelicCyclicHilbertGenerator_ne_zero f hf (congrArg Subtype.val he)
  | succ n ih =>
      intro he
      have hl := adelicRaisingJet_lower f hf n
      rw [he, lie_zero] at hl
      have hp : (k : ℂ) + n ≠ 0 := by
        exact_mod_cast (show (k + (n : ℤ)) ≠ 0 from
          (add_pos_of_pos_of_nonneg hk (Int.natCast_nonneg n)).ne')
      have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      have hc : ((n : ℂ) + 1) * (-(k : ℂ) - n) ≠ 0 := by
        apply mul_ne_zero hn
        have hn' : -(k : ℂ) - n = -((k : ℂ) + n) := by ring
        rw [hn']
        exact neg_ne_zero.mpr hp
      exact (smul_ne_zero hc ih) hl.symm

/-- The original raising derivatives form a linearly independent family in the genuine adelic smooth space. -/
theorem adelicRaisingJet_linearIndependent (hf : f ≠ 0) (hk : 0 < k) :
    LinearIndependent ℂ (adelicRaisingJet f) := by
  apply (adelicComplexSl2Action f compactSl2H).eigenvectors_linearIndependent'
    (fun n : ℕ => (k : ℂ) + 2 * n)
  · intro m n he
    have hn : (m : ℂ) = n := by linear_combination he / 2
    exact_mod_cast hn
  · intro n
    exact ⟨Module.End.mem_eigenspace_iff.mpr (adelicRaisingJet_weight f hf n),
      adelicRaisingJet_ne_zero f hf hk n⟩

end
end Dubon2026
