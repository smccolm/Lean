import Dubon2026.HeckeGoodAdjoint
import Mathlib.Analysis.InnerProductSpace.Defs

/-! # A genuine positive-definite inner-product core from the actual Gamma0 integral -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

/-- The actual finite-coset Petersson self-pairing has nonnegative real part. -/
theorem cuspPetersson_re_nonneg {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : 0 ≤ (cuspPetersson f f).re := by
  unfold cuspPetersson
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro q _
  obtain ⟨r, hr, he⟩ := cuspPetersson_summand_nonneg f q
  rw [he, Complex.ofReal_re]
  exact hr

/-- The self-pairing is a real number, independently of coefficient reality. -/
theorem cuspPetersson_im_self {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : (cuspPetersson f f).im = 0 :=
  Complex.conj_eq_iff_im.mp (cuspPetersson_conj_symm f f)

/-- The actual Gamma0 Petersson pairing satisfies every positive-definite inner-product axiom. -/
@[reducible]
def cuspPeterssonCore (Q : ℕ) [NeZero Q] (k : ℤ) :
    InnerProductSpace.Core ℂ (CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) where
  inner := cuspPetersson
  conj_inner_symm := cuspPetersson_conj_symm
  re_inner_nonneg := cuspPetersson_re_nonneg
  add_left := cuspPetersson_add_left
  smul_left f g c := cuspPetersson_conj_smul_left c f g
  definite := cuspPetersson_definite

/-- Cauchy–Schwarz for the actual Gamma0 Petersson integrals. -/
theorem norm_cuspPetersson_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f g : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    ‖cuspPetersson f g‖ ≤ Real.sqrt (cuspPetersson f f).re * Real.sqrt (cuspPetersson g g).re := by
  letI := cuspPeterssonCore Q k
  exact InnerProductSpace.Core.norm_inner_le_norm f g

end
end Dubon2026
