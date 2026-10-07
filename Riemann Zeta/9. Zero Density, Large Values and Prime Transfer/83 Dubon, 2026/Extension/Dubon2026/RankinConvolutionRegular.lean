import Dubon2026.PrincipalSquareMass
import Dubon2026.CuspRankinRegular

/-! # The actual pole and regular part of the nonnegative Rankin convolution series -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Set
open scoped Topology

noncomputable section

/-- The genuine residue of the convolution series, including its principal-character factor. -/
def rankinConvolutionResidue {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℝ :=
  principalSquareMass Q * cuspRankinResidue f

/-- The actual convolution residue is positive for every nonzero cusp form of positive weight. -/
theorem rankinConvolutionResidue_pos {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) (hf : f ≠ 0) :
    0 < rankinConvolutionResidue f :=
  mul_pos (principalSquareMass_pos Q) (cuspRankinResidue_pos f hk hf)

/-- The actual analytic convolution numerator before division by its simple pole. -/
def rankinConvolutionPoleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar Q (2 * s) * cuspRankinPoleNumerator f s

/-- The genuine convolution numerator is holomorphic on the entire half-plane Re(s)>1/2. -/
theorem differentiableAt_rankinConvolutionPoleNumerator {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ}
    (hs : 1 / 2 < s.re) : DifferentiableAt ℂ (rankinConvolutionPoleNumerator f) s := by
  have h2 : 2 * s ≠ (1 : ℂ) := by
    intro he
    have hh := congrArg Complex.re he
    simp only [two_mul, Complex.add_re, Complex.one_re] at hh
    linarith
  exact ((DirichletCharacter.differentiableAt_LFunction 1 (2 * s) (Or.inl h2)).comp s
    (differentiableAt_id.const_mul 2)).mul (differentiableAt_cuspRankinPoleNumerator f hk hs)

/-- At one the actual pole numerator equals the constructed real residue. -/
theorem rankinConvolutionPoleNumerator_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    rankinConvolutionPoleNumerator f 1 = (rankinConvolutionResidue f : ℂ) := by
  simp only [rankinConvolutionPoleNumerator, mul_one, cuspRankinPoleNumerator_one f hk,
    rankinConvolutionResidue, Complex.ofReal_mul, principalSquareMass_eq_LFunction]

/-- In its convergence half-plane the genuine numerator is exactly (s−1) times the literal convolution series. -/
theorem rankinConvolutionPoleNumerator_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    rankinConvolutionPoleNumerator f s = (s - 1) * LSeries (rankinConvolutionCoefficients f) s := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, Complex.one_re] at hs; linarith
  rw [rankinConvolutionPoleNumerator, cuspRankinPoleNumerator_eq f hk (by linarith) hs1,
    cuspRankinContinuation_eq_series f hk.le hs, rankinConvolution_LSeries f hk.le hs]
  ring

/-- The actual analytic regular part, with its derivative value at the removed pole. -/
def rankinConvolutionRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℂ → ℂ :=
  dslope (rankinConvolutionPoleNumerator f) 1

/-- The genuine regular part is holomorphic after removal of the convolution pole. -/
theorem differentiableOn_rankinConvolutionRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    DifferentiableOn ℂ (rankinConvolutionRegular f) {s : ℂ | 1 / 2 < s.re} := by
  apply (Complex.differentiableOn_dslope
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} by norm_num))).mpr
  exact fun s hs => (differentiableAt_rankinConvolutionPoleNumerator f hk hs).differentiableWithinAt

/-- The actual pole-subtracted function is continuous on the whole closed convergence boundary. -/
theorem continuousOn_rankinConvolutionRegular {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    ContinuousOn (rankinConvolutionRegular f) {s : ℂ | 1 ≤ s.re} := by
  apply (differentiableOn_rankinConvolutionRegular f hk).continuousOn.mono
  intro s hs
  change 1 ≤ s.re at hs
  change 1 / 2 < s.re
  linarith

/-- The constructed regular part agrees with the literal convergent convolution series minus its genuine pole. -/
theorem rankinConvolutionRegular_eq_series_sub_pole {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    rankinConvolutionRegular f s = LSeries (rankinConvolutionCoefficients f) s -
      (rankinConvolutionResidue f : ℂ) / (s - 1) := by
  have hs1 : s ≠ 1 := by intro he; simp only [he, Complex.one_re] at hs; linarith
  rw [rankinConvolutionRegular, dslope_of_ne _ hs1, slope, smul_eq_mul, vsub_eq_sub,
    rankinConvolutionPoleNumerator_one f hk, rankinConvolutionPoleNumerator_eq f hk hs]
  field_simp [sub_ne_zero.mpr hs1]

end
end Dubon2026
