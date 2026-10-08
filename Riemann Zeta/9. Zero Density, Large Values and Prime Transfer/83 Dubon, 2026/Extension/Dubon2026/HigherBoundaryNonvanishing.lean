import Dubon2026.HigherMixedEuler
import Dubon2026.PrimitiveHigherContinuationReduction

/-! # Nonreal boundary nonvanishing from the genuine higher tensor Euler inequality -/

namespace Dubon2026

noncomputable section
open Filter Asymptotics
open scoped Topology

/-- The actual principal function times the supplied positive even symmetric continuations. -/
def higherTensorContinuation (Q : ℕ) [NeZero Q] (H : ℕ → ℂ → ℂ) (r : ℕ) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar Q s * ∏ t ∈ Finset.range r, H (2 * (t + 1)) s

/-- Matching the actual even symmetric factors gives the literal original tensor Euler function. -/
theorem higherTensorContinuation_eq_euler {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n) (primitiveSymmetricLFunction f n) {s | 1 < s.re})
    (r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    higherTensorContinuation Q H r s = ∏ t ∈ Finset.range (r + 1), primitiveSymmetricLFunction f (2 * t) s := by
  rw [Finset.prod_range_succ' (fun t => primitiveSymmetricLFunction f (2 * t) s),
    Nat.mul_zero, primitiveSymmetric_zero_eq_principal f hk hs, higherTensorContinuation, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  exact hmatch _ (by omega) hs

/-- Holomorphic positive even continuations give the actual tensor product at most a simple pole at one. -/
theorem higherTensorContinuation_isBigO_near_one (Q : ℕ) [NeZero Q]
    (H : ℕ → ℂ → ℂ) (hH : ∀ n, 0 < n → AnalyticOnNhd ℂ (H n) {s | 1 ≤ s.re}) (r : ℕ) :
    (fun x : ℝ => higherTensorContinuation Q H r (1 + x)) =O[𝓝[>] 0] fun x => (1 : ℂ) / x := by
  have hd : DifferentiableAt ℂ (fun s => ∏ t ∈ Finset.range r, H (2 * (t + 1)) s) 1 :=
    DifferentiableAt.fun_finsetProd (fun t _ => (hH _ (by omega) 1 (by simp)).differentiableAt)
  have hc : ContinuousAt (fun x : ℝ => ∏ t ∈ Finset.range r, H (2 * (t + 1)) (1 + x)) 0 := by
    apply ContinuousAt.comp (f := fun x : ℝ => 1 + (x : ℂ))
      (g := fun s : ℂ => ∏ t ∈ Finset.range r, H (2 * (t + 1)) s)
    · simpa using hd.continuousAt
    · fun_prop
  have hb := (hc.tendsto.isBigO_one ℂ).mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hh := (DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal (N := Q)).mul hb
  simpa only [higherTensorContinuation, mul_one] using hh

/-- The actual mixed Euler inequality and a simple tensor pole exclude every nonreal boundary
zero of a positive symmetric continuation. No nonvanishing input is used. -/
theorem primitive_symmetric_nonreal_boundary_of_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (H : ℕ → ℂ → ℂ)
    (hH : ∀ n, 0 < n → AnalyticOnNhd ℂ (H n) {s | 1 ≤ s.re})
    (hmatch : ∀ n, 0 < n → Set.EqOn (H n) (primitiveSymmetricLFunction f n)
      {s | (n : ℝ) + 1 < s.re}) {r : ℕ} (hr : 0 < r) {y : ℝ} (hy : y ≠ 0) :
    H r (1 + Complex.I * y) ≠ 0 := by
  have hb : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2 := by
    intro p hp hpQ
    apply primitive_prime_bound_of_higher_symmetric_holomorphy f hk _ hp hpQ
    intro n hn
    exact ⟨H n, (hH n (by omega)).differentiableOn.mono (fun s hs => (show 1 < s.re from hs).le),
      hmatch n (by omega)⟩
  have hnear (n : ℕ) (hn : 0 < n) : Set.EqOn (H n) (primitiveSymmetricLFunction f n) {s | 1 < s.re} :=
    primitive_symmetric_continuation_eqOn_of_far f hb n (hH n hn) (hmatch n hn)
  intro hz
  have hs2 : 1 + Complex.I * ((2 * y : ℝ) : ℂ) ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add] at hi
    exact hy (by linarith)
  have hR := higherTensorContinuation_isBigO_near_one Q H hH r
  have hA := DirichletCharacter.LFunctionTrivChar_isBigO_near_one_horizontal (N := Q)
  have hU := boundary_horizontal_isBigO_of_zero ((hH r hr _ (by simp)).differentiableAt) hz
  have hB := boundary_horizontal_isBigO_one (y := 2 * y)
    (DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ Q) _ (.inl hs2))
  have hupper := ((hR.mul (hA.pow 2)).mul (hU.pow 4)).mul (hB.pow 2)
  have hcancel (x : ℝ) : ((1 / x) * (1 / x) ^ 2 * x ^ 4 * 1 ^ 2 : ℂ) = x := by
    by_cases hx : x = 0
    · simp [hx]
    · field_simp [Complex.ofReal_ne_zero.mpr hx]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, mul_left_comm Complex.I,
    ← mul_assoc, hcancel] at hupper
  have hEuler (x : ℝ) (hx : 0 < x) :
      1 ≤ ‖higherTensorContinuation Q H r (1 + x) *
        DirichletCharacter.LFunctionTrivChar Q (1 + x) ^ 2 *
          H r (1 + x + Complex.I * y) ^ 4 *
            DirichletCharacter.LFunctionTrivChar Q (1 + x + 2 * Complex.I * y) ^ 2‖ := by
    rw [higherTensorContinuation_eq_euler f hk H hnear r (by simp; exact hx),
      hnear r hr (by simp; exact hx)]
    exact primitive_higher_mixed_global f hb r hx y
  have hlower : (fun _ : ℝ => (1 : ℝ)) =O[𝓝[>] 0]
      fun x => higherTensorContinuation Q H r (1 + x) *
        DirichletCharacter.LFunctionTrivChar Q (1 + x) ^ 2 *
          H r (1 + x + Complex.I * y) ^ 4 *
            DirichletCharacter.LFunctionTrivChar Q (1 + x + 2 * Complex.I * y) ^ 2 :=
    IsBigO.of_bound' (eventually_nhdsWithin_of_forall (fun x hx =>
      (norm_one (α := ℝ)).symm ▸ hEuler x hx))
  have hh := (hlower.trans hupper).norm_right
  simp only [Complex.norm_real] at hh
  exact isLittleO_irrefl (.of_forall (fun _ => one_ne_zero))
    (hh.of_norm_right.trans_isLittleO (isLittleO_id_one.mono nhdsWithin_le_nhds))

end
end Dubon2026
