import Dubon2026.Gamma0Eisenstein
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Holomorphy of the genuine nonholomorphic Eisenstein series in its parameter -/

namespace Dubon2026

open UpperHalfPlane Set
open scoped Topology

noncomputable section

/-- Each genuine primitive-row summand is entire in the complex parameter. -/
theorem nonholomorphicEisensteinTerm_differentiable {Q : ℕ}
    (v : gamma0PrimitiveRows Q) (z : ℍ) :
    Differentiable ℂ (fun s => nonholomorphicEisensteinTerm s v.val z) := by
  unfold nonholomorphicEisensteinTerm
  exact differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr
    (eisensteinRowHeight_pos (gamma0PrimitiveRow_ne_zero v) z).ne'))

/-- Two real boundary exponents dominate each actual term throughout a closed vertical strip. -/
theorem nonholomorphicEisensteinTerm_strip_bound {Q : ℕ}
    (v : gamma0PrimitiveRows Q) (z : ℍ) {a b : ℝ} {s : ℂ}
    (ha : a ≤ s.re) (hb : s.re ≤ b) :
    ‖nonholomorphicEisensteinTerm s v.val z‖ ≤
      ‖nonholomorphicEisensteinTerm (a : ℂ) v.val z‖ +
        ‖nonholomorphicEisensteinTerm (b : ℂ) v.val z‖ := by
  have hp := eisensteinRowHeight_pos (gamma0PrimitiveRow_ne_zero v) z
  simp only [nonholomorphicEisensteinTerm,
    Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.ofReal_re]
  by_cases hh : 1 ≤ eisensteinRowHeight v.val z
  · exact (Real.rpow_le_rpow_of_exponent_le hh hb).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hp.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hp (le_of_not_ge hh) ha).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hp.le _))

/-- Absolute lattice convergence on two boundary lines proves actual parameter differentiability. -/
theorem gamma0Eisenstein_differentiableAt (Q : ℕ) (z : ℍ) {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun t => gamma0Eisenstein Q t z) s := by
  let a : ℝ := (1 + s.re) / 2
  let b : ℝ := s.re + 1
  let U : Set ℂ := {t | a < t.re ∧ t.re < b}
  have ha : 1 < a := by dsimp [a]; linarith
  have hb : 1 < b := by dsimp [b]; linarith
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hsU : s ∈ U := by dsimp [U, a, b]; constructor <;> linarith
  have hu := (gamma0Eisenstein_summable_norm Q (s := (a : ℂ)) ha z).add
    (gamma0Eisenstein_summable_norm Q (s := (b : ℂ)) hb z)
  have hf (v : gamma0PrimitiveRows Q) :
      DifferentiableOn ℂ (fun t => nonholomorphicEisensteinTerm t v.val z) U :=
    (nonholomorphicEisensteinTerm_differentiable v z).differentiableOn
  have hh := Complex.differentiableOn_tsum_of_summable_norm hu hf hU
    (fun v t ht => nonholomorphicEisensteinTerm_strip_bound v z ht.1.le ht.2.le)
  exact (hh.differentiableAt (hU.mem_nhds hsU)).const_mul (1 / 2 : ℂ)

/-- The literal Eisenstein series is holomorphic in s throughout Re(s)>1. -/
theorem gamma0Eisenstein_analyticOnNhd (Q : ℕ) (z : ℍ) :
    AnalyticOnNhd ℂ (fun s => gamma0Eisenstein Q s z) {s : ℂ | 1 < s.re} := by
  have h : DifferentiableOn ℂ (fun s => gamma0Eisenstein Q s z) {s : ℂ | 1 < s.re} :=
    fun s hs => (gamma0Eisenstein_differentiableAt Q z hs).differentiableWithinAt
  exact h.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end
end Dubon2026
