import GafniTao.FordLemma51Fibers

/-!
# Ford Lemma 5.1: equation (5.3)

The finite oscillatory fiber sum and its moment `T` are kept literal.  This
module assembles the representation-fiber expansion with the exact second
Hölder inequality.
-/

open Finset
open scoped BigOperators NNReal

namespace GafniTao

noncomputable section

def fordLemma51FiberOscillatorySum
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) : ℂ :=
  ∑ b ∈ B,
    fordLemma51Epsilon k M r t z b *
      fordAdditiveCharacter (fordLemma51FiberPhase k t z b c)

/-- The literal finite `T` in Ford's equation (5.3). -/
def fordLemma51MomentT
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) : ℝ≥0 :=
  ∑ c ∈ fordLemma51FiberSet r k M,
    ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s)

theorem fordLemma51_epsilon_sum_eq_weighted_fiber_sum
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) :
    (∑ b ∈ B,
      fordLemma51Epsilon k M r t z b *
        fordLemma51InnerSum k M t z b ^ r) =
      ∑ c ∈ fordLemma51FiberSet r k M,
        (fordLemma51RepresentationCount r k M c : ℂ) *
          fordLemma51FiberOscillatorySum k M r B t z c := by
  simp_rw [fordLemma51InnerSum_pow_eq_fiber_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  unfold fordLemma51FiberOscillatorySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem fordLemma51_weighted_fiber_power_bound
    (k M r : ℕ) {s : ℕ} (hs : 1 ≤ s) (B : Finset ℕ) (t z : ℝ) :
    ‖(∑ c ∈ fordLemma51FiberSet r k M,
        (fordLemma51RepresentationCount r k M c : ℂ) *
          fordLemma51FiberOscillatorySum k M r B t z c)‖₊ ^ (2 * s) ≤
      (M ^ r : ℝ≥0) ^ (2 * s - 2) *
        (fordVinogradovMomentNat r k M : ℝ≥0) *
        fordLemma51MomentT k M r s B t z := by
  let C := fordLemma51FiberSet r k M
  let n : (Fin k → ℤ) → ℝ≥0 := fun c =>
    fordLemma51RepresentationCount r k M c
  let Z : (Fin k → ℤ) → ℂ := fun c =>
    fordLemma51FiberOscillatorySum k M r B t z c
  have hnorm :
      ‖(∑ c ∈ C, (fordLemma51RepresentationCount r k M c : ℂ) * Z c)‖₊ ≤
        ∑ c ∈ C, n c * ‖Z c‖₊ := by
    calc
      ‖(∑ c ∈ C, (fordLemma51RepresentationCount r k M c : ℂ) * Z c)‖₊ ≤
          ∑ c ∈ C,
            ‖(fordLemma51RepresentationCount r k M c : ℂ) * Z c‖₊ :=
        nnnorm_sum_le _ _
      _ = ∑ c ∈ C, n c * ‖Z c‖₊ := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [n, Z]
  have hpow :
      ‖(∑ c ∈ C, (fordLemma51RepresentationCount r k M c : ℂ) * Z c)‖₊ ^
          (2 * s) ≤ (∑ c ∈ C, n c * ‖Z c‖₊) ^ (2 * s) := by
    gcongr
  have hholder := ford_second_holder_power C n (fun c => ‖Z c‖₊) hs
  have hn : (∑ c ∈ C, n c) = (M ^ r : ℝ≥0) := by
    change (∑ c ∈ fordLemma51FiberSet r k M,
      (fordLemma51RepresentationCount r k M c : ℝ≥0)) = (M ^ r : ℝ≥0)
    exact_mod_cast fordLemma51_sum_representationCount r k M
  have hn2 : (∑ c ∈ C, n c ^ 2) =
      (fordVinogradovMomentNat r k M : ℝ≥0) := by
    change (∑ c ∈ fordLemma51FiberSet r k M,
      (fordLemma51RepresentationCount r k M c : ℝ≥0) ^ 2) =
        (fordVinogradovMomentNat r k M : ℝ≥0)
    exact_mod_cast fordLemma51_sum_representationCount_sq r k M
  calc
    ‖(∑ c ∈ fordLemma51FiberSet r k M,
        (fordLemma51RepresentationCount r k M c : ℂ) *
          fordLemma51FiberOscillatorySum k M r B t z c)‖₊ ^ (2 * s) =
        ‖(∑ c ∈ C,
          (fordLemma51RepresentationCount r k M c : ℂ) * Z c)‖₊ ^
            (2 * s) := by rfl
    _ ≤ (∑ c ∈ C, n c * ‖Z c‖₊) ^ (2 * s) := hpow
    _ ≤ (∑ c ∈ C, n c) ^ (2 * s - 2) *
          (∑ c ∈ C, n c ^ 2) *
          (∑ c ∈ C, ‖Z c‖₊ ^ (2 * s)) := hholder
    _ = (M ^ r : ℝ≥0) ^ (2 * s - 2) *
          (fordVinogradovMomentNat r k M : ℝ≥0) *
          fordLemma51MomentT k M r s B t z := by
      rw [hn, hn2]
      rfl

theorem fordLemma51U_nnnorm_pow_le
    {k M r : ℕ} {B : Finset ℕ} {t z : ℝ} (hr : 1 ≤ r) :
    ‖fordLemma51U k M B t z‖₊ ^ r ≤
      (B.card : ℝ≥0) ^ (r - 1) *
        ∑ b ∈ B, ‖fordLemma51InnerSum k M t z b‖₊ ^ r := by
  apply (NNReal.coe_le_coe).mp
  push_cast
  simpa using (fordLemma51U_pow_le (k := k) (M₁ := M) (B := B)
    (t := t) (z := z) hr)

theorem fordLemma51_nnnorm_epsilon_sum_eq_norm_power_sum
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) :
    ‖(∑ b ∈ B, fordLemma51Epsilon k M r t z b *
        fordLemma51InnerSum k M t z b ^ r)‖₊ =
      ∑ b ∈ B, ‖fordLemma51InnerSum k M t z b‖₊ ^ r := by
  apply NNReal.eq
  have h := congrArg norm
    (fordLemma51_norm_power_sum_eq_epsilon_sum k M r B t z)
  push_cast
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun b _ => pow_nonneg (norm_nonneg _) _),
    NNReal.sq_sqrt, NNReal.coe_nonneg] using h.symm

theorem fordLemma51_nnnorm_epsilon_sum_eq_weighted_fiber_sum
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) :
    ‖(∑ b ∈ B, fordLemma51Epsilon k M r t z b *
        fordLemma51InnerSum k M t z b ^ r)‖₊ =
      ‖(∑ c ∈ fordLemma51FiberSet r k M,
        (fordLemma51RepresentationCount r k M c : ℂ) *
          fordLemma51FiberOscillatorySum k M r B t z c)‖₊ := by
  rw [fordLemma51_epsilon_sum_eq_weighted_fiber_sum]

/-- Ford's equation (5.3), with the finite Vinogradov moment and the literal
oscillatory moment `T` exposed in the conclusion. -/
theorem ford_equation_5_3
    (k M r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (B : Finset ℕ) (t z : ℝ) :
    ‖fordLemma51U k M B t z‖₊ ^ (2 * r * s) ≤
      (B.card : ℝ≥0) ^ (2 * r * s - 2 * s) *
        (M : ℝ≥0) ^ (2 * r * s - 2 * r) *
        (fordVinogradovMomentNat r k M : ℝ≥0) *
        fordLemma51MomentT k M r s B t z := by
  let S : ℝ≥0 :=
    ∑ b ∈ B, ‖fordLemma51InnerSum k M t z b‖₊ ^ r
  let W : ℂ :=
    ∑ c ∈ fordLemma51FiberSet r k M,
      (fordLemma51RepresentationCount r k M c : ℂ) *
        fordLemma51FiberOscillatorySum k M r B t z c
  have hU : ‖fordLemma51U k M B t z‖₊ ^ r ≤
      (B.card : ℝ≥0) ^ (r - 1) * S := by
    exact fordLemma51U_nnnorm_pow_le hr
  have hS : S = ‖W‖₊ := by
    calc
      S = ‖(∑ b ∈ B, fordLemma51Epsilon k M r t z b *
          fordLemma51InnerSum k M t z b ^ r)‖₊ :=
        (fordLemma51_nnnorm_epsilon_sum_eq_norm_power_sum
          k M r B t z).symm
      _ = ‖W‖₊ := fordLemma51_nnnorm_epsilon_sum_eq_weighted_fiber_sum
        k M r B t z
  have hW : ‖W‖₊ ^ (2 * s) ≤
      (M ^ r : ℝ≥0) ^ (2 * s - 2) *
        (fordVinogradovMomentNat r k M : ℝ≥0) *
        fordLemma51MomentT k M r s B t z := by
    exact fordLemma51_weighted_fiber_power_bound k M r hs B t z
  have hBexp : (r - 1) * (2 * s) = 2 * r * s - 2 * s := by
    rw [Nat.sub_mul, one_mul]
    rw [show r * (2 * s) = 2 * r * s by ring]
  have hMexp : r * (2 * s - 2) = 2 * r * s - 2 * r := by
    rw [Nat.mul_sub_left_distrib]
    rw [show r * (2 * s) = 2 * r * s by ring,
      show r * 2 = 2 * r by ring]
  have hpow := pow_le_pow_left₀ (by positivity) hU (2 * s)
  calc
    ‖fordLemma51U k M B t z‖₊ ^ (2 * r * s) =
        (‖fordLemma51U k M B t z‖₊ ^ r) ^ (2 * s) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ ((B.card : ℝ≥0) ^ (r - 1) * S) ^ (2 * s) := hpow
    _ = (B.card : ℝ≥0) ^ (2 * r * s - 2 * s) * S ^ (2 * s) := by
      rw [mul_pow, ← pow_mul, hBexp]
    _ = (B.card : ℝ≥0) ^ (2 * r * s - 2 * s) * ‖W‖₊ ^ (2 * s) := by
      rw [hS]
    _ ≤ (B.card : ℝ≥0) ^ (2 * r * s - 2 * s) *
          ((M ^ r : ℝ≥0) ^ (2 * s - 2) *
            (fordVinogradovMomentNat r k M : ℝ≥0) *
            fordLemma51MomentT k M r s B t z) :=
      by gcongr
    _ = (B.card : ℝ≥0) ^ (2 * r * s - 2 * s) *
          (M : ℝ≥0) ^ (2 * r * s - 2 * r) *
          (fordVinogradovMomentNat r k M : ℝ≥0) *
          fordLemma51MomentT k M r s B t z := by
      rw [← pow_mul, hMexp]
      ring

#print axioms fordLemma51_epsilon_sum_eq_weighted_fiber_sum
#print axioms fordLemma51_weighted_fiber_power_bound
#print axioms fordLemma51U_nnnorm_pow_le
#print axioms fordLemma51_nnnorm_epsilon_sum_eq_norm_power_sum
#print axioms ford_equation_5_3

end

end GafniTao
