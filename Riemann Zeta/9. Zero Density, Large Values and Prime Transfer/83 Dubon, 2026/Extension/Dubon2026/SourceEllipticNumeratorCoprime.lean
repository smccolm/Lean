import Dubon2026.SourceEllipticMultiplicationXFormula

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction ->
reverse genus -> finite exceptional fibers -> elliptic inertia orbits ->
actual torsion cardinality. The proved actual point-multiplication formula
now controls the native univariate division polynomials and their fibers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean. -/
namespace Dubon2026.SourceEllipticTorsion
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open Dubon2026.SourceEllipticPointFormula
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)
omit [DecidableEq K] in

private theorem eval_ne_of_isCoprime {f g : Polynomial K} (h : IsCoprime f g) {x₀ : K}
    (hf : f.eval x₀ = 0) (hg : g.eval x₀ = 0) : False := by
  obtain ⟨a, b, hab⟩ := h
  have h1 := congrArg (Polynomial.eval x₀) hab
  simp only [eval_add, eval_mul, hf, hg, mul_zero, add_zero, eval_one] at h1
  exact zero_ne_one h1

theorem isCoprime_Φ_ΨSq [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    IsCoprime ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hΦ0, hΨ0⟩ := hcon
  rw [coe_aeval_eq_eval] at hΦ0 hΨ0
  have hΦdef : (W.baseChange K).Φ (n : ℤ) =
      X * (W.baseChange K).ΨSq (n : ℤ) -
        (W.baseChange K).preΨ ((n : ℤ) + 1) * (W.baseChange K).preΨ ((n : ℤ) - 1) *
          (if Even (n : ℤ) then 1 else (W.baseChange K).Ψ₂Sq) := rfl
  have h0 : ((W.baseChange K).preΨ ((n : ℤ) + 1)).eval x₀ *
      ((W.baseChange K).preΨ ((n : ℤ) - 1)).eval x₀ *
      (if Even (n : ℤ) then (1 : K) else ((W.baseChange K).Ψ₂Sq).eval x₀) = 0 := by
    have h1 := congrArg (Polynomial.eval x₀) hΦdef
    rw [hΦ0] at h1
    simp only [eval_sub, eval_mul, eval_X, apply_ite (Polynomial.eval x₀), eval_one, hΨ0,
      mul_zero, zero_sub] at h1
    linear_combination h1
  rcases mul_eq_zero.mp h0 with h12 | hG
  · rcases mul_eq_zero.mp h12 with hE | hF
    ·
      have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 := ΨSq_eval_eq_zero_of_preΨ W (m := n + 1) (K := K)
          (by rwa [Nat.cast_add, Nat.cast_one])
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb
    ·
      have hb : ((W.baseChange K).ΨSq ((n - 1 : ℕ) : ℤ)).eval x₀ = 0 :=
        ΨSq_eval_eq_zero_of_preΨ W (m := n - 1) (K := K)
          (by rwa [Nat.cast_sub hn, Nat.cast_one])
      have hA := isCoprime_ΨSq_succ W (K := K) (n - 1)
      have hc : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
      rw [hc] at hA
      exact eval_ne_of_isCoprime hA hb hΨ0
  ·
    by_cases hev : Even (n : ℤ)
    · rw [if_pos hev] at hG
      exact one_ne_zero hG
    · rw [if_neg hev] at hG
      have hnodd : ¬Even n := fun h => hev (by exact_mod_cast h)
      have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 : ((W.baseChange K).ΨSq ((n + 1 : ℕ) : ℤ)).eval x₀ = 0 := by
          rw [ΨSq_ofNat, if_pos (Nat.even_add_one.mpr hnodd), eval_mul, hG, mul_zero]
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb


end
end Dubon2026.SourceEllipticTorsion
