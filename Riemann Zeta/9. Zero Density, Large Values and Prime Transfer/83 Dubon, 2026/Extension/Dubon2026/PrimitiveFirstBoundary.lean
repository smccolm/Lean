import Dubon2026.PrimitiveMixedEulerGlobal

/-! # Nonvanishing of the actual first symmetric continuation at nonreal boundary points -/

namespace Dubon2026

open Filter Asymptotics
open scoped Topology

noncomputable section

/-- The genuine mixed Euler inequality rules out a zero of the actual first symmetric continuation at every nonzero boundary height. -/
theorem primitiveFirstContinuation_nonzero_height {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {y : ℝ} (hy : y ≠ 0) :
    primitiveFirstContinuation f (1 + Complex.I * y) ≠ 0 := by
  intro hz
  have hs2 : 1 + Complex.I * ((2 * y : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hi
    exact hy (by linarith)
  have hR := rankinConvolutionGlobal_isBigO_near_one f.toCuspForm
  have hA := DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal (N := Q)
  have hU := boundary_horizontal_isBigO_of_zero
    (primitiveFirstContinuation_differentiable f (by omega) _) hz
  have hB := boundary_horizontal_isBigO_one (y := 2 * y)
    (DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ Q) _ (.inl hs2))
  have hupper := ((hR.mul (hA.pow 2)).mul (hU.pow 4)).mul (hB.pow 2)
  have hcancel (x : ℝ) : ((1 / x) * (1 / x) ^ 2 * x ^ 4 * 1 ^ 2 : ℂ) = x := by
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [Complex.ofReal_ne_zero.mpr hx]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_left_comm Complex.I,
    ← mul_assoc, hcancel] at hupper
  have hlower : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => rankinConvolutionGlobalContinuation f.toCuspForm (1 + x) *
        DirichletCharacter.LFunctionTrivChar Q (1 + x) ^ 2 *
          primitiveFirstContinuation f (1 + x + Complex.I * y) ^ 4 *
            DirichletCharacter.LFunctionTrivChar Q (1 + x + 2 * Complex.I * y) ^ 2 :=
    IsBigO.of_bound' (eventually_nhdsWithin_of_forall (fun x hx =>
      (norm_one (α := ℝ)).symm ▸ primitive_mixed_global_inequality f hk hx y))
  have hh := (hlower.trans hupper).norm_right
  simp only [Complex.norm_real] at hh
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero))
    (hh.of_norm_right.trans_isLittleO (isLittleO_id_one.mono nhdsWithin_le_nhds))

/-- The explicit actual first symmetric continuation is nonzero on Re(s)=1 except possibly at the real point one. -/
theorem primitiveFirstContinuation_nonreal_boundary {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : s.re = 1) (hs1 : s ≠ 1) :
    primitiveFirstContinuation f s ≠ 0 := by
  have hy : s.im ≠ 0 := by
    intro hi
    apply hs1
    exact Complex.ext (by simpa using hs) (by simpa using hi)
  have he : s = 1 + Complex.I * s.im := by apply Complex.ext <;> simp [hs]
  rw [he]
  exact primitiveFirstContinuation_nonzero_height f hk hy

/-- The genuine first symmetric continuation is nonzero on the closed half-plane with only the real boundary point one still excluded. -/
theorem primitiveFirstContinuation_ne_zero_of_ne_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    primitiveFirstContinuation f s ≠ 0 := by
  rcases hs.eq_or_lt with he | hlt
  · exact primitiveFirstContinuation_nonreal_boundary f hk he.symm hs1
  · rw [primitiveFirstContinuation_eq_symmetric f (by omega) hlt]
    exact primitive_first_symmetric_ne_zero f (by omega) hlt

end
end Dubon2026
