import Dubon2026.PrimitiveFirstContinuation
import Dubon2026.RankinBoundaryNonvanishing
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # The actual entire pole-cancelled Rankin product under a first-power zero at one -/

namespace Dubon2026

open scoped Topology

noncomputable section

/-- The genuine pole numerators and the actual divided difference of the first symmetric continuation. -/
def firstRankinPoleCancellation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ Q s * rankinConvolutionEntireNumerator f.toCuspForm s *
    (dslope (primitiveFirstContinuation f) 1 s) ^ 2 * primitiveRankinBadCorrection f s

/-- The actual divided-difference construction is entire, including at its removed point one. -/
theorem firstRankinPoleCancellation_differentiable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    Differentiable ℂ (firstRankinPoleCancellation f) := by
  have hd : Differentiable ℂ (dslope (primitiveFirstContinuation f) 1) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      (primitiveFirstContinuation_differentiable f hk).differentiableOn
  exact (((DirichletCharacter.differentiable_LFunctionTrivChar₁ Q).mul
    (differentiable_rankinConvolutionEntireNumerator f.toCuspForm)).mul (hd.pow 2)).mul
      (primitiveRankinBadCorrection_differentiable f)

/-- If the actual first symmetric function vanished at one, its pole-cancelled Rankin product would retain the genuine real trivial zero. -/
theorem firstRankinPoleCancellation_trivial_zero_of_zero_at_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hz : primitiveFirstContinuation f 1 = 0) :
    firstRankinPoleCancellation f (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) = 0 := by
  have hs : (((1 - (k : ℝ)) / 2 : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at hr
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rw [firstRankinPoleCancellation, dslope_of_ne _ hs, slope,
    primitiveFirstContinuation_trivial_zero, hz, vsub_eq_sub, sub_self, smul_zero]
  simp

/-- Under the displayed hypothetical zero, the entire function agrees with the exact original Euler product on its convergence half-plane. -/
theorem firstRankinPoleCancellation_eq_product {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 ≤ k) (hz : primitiveFirstContinuation f 1 = 0)
    {s : ℂ} (hs : 1 < s.re) :
    firstRankinPoleCancellation f s =
      DirichletCharacter.LFunctionTrivChar Q s * rankinConvolutionGlobalContinuation f.toCuspForm s *
        primitiveRankinBadCorrection f s * primitiveSymmetricLFunction f 1 s ^ 2 := by
  have hs1 : s ≠ 1 := by intro he; simp [he] at hs
  rw [firstRankinPoleCancellation, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs1, dslope_of_ne _ hs1, slope, vsub_eq_sub, hz, sub_zero,
    smul_eq_mul, primitiveFirstContinuation_eq_symmetric f hk hs,
    rankinConvolutionGlobalContinuation]
  field_simp [sub_ne_zero.mpr hs1]

end
end Dubon2026
