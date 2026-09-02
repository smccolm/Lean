import GafniTao.FordLemma63Phase
import GafniTao.FordVinogradovIntegral
import Mathlib.Algebra.BigOperators.Module

/-!
# Ford Lemma 6.3: discrete partial summation

Ford writes the partial-summation remainder as an integral in `w`.  On the
integer sum the equivalent Abel identity is exact and gives the same source
constant: the variation of the phase multiplier is at most `2/M` per step.
All partial sums remain the literal complete Vinogradov Weyl sums.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordLemma63PolynomialPhase
    {k : ℕ} (β : Fin k → ℝ) (m : ℕ) : ℝ :=
  ∑ j : Fin k, β j * (m : ℝ) ^ ((j : ℕ) + 1)

def fordLemma63PolynomialSum
    (k Q : ℕ) (β : Fin k → ℝ) : ℂ :=
  ∑ i ∈ Finset.range Q,
    fordAdditiveCharacter (fordLemma63PolynomialPhase β (i + 1))

def fordLemma63DeltaCharacter
    (k n : ℕ) (u t : ℝ) (β : Fin k → ℝ) (w : ℝ) : ℂ :=
  fordAdditiveCharacter (fordLemma63Delta k n u t β w)

def fordLemma63SZeroTail
    (k M : ℕ) (β : Fin k → ℝ) : ℝ :=
  (2 / (M : ℝ)) *
    ∑ q ∈ Finset.range (M - 1), ‖fordLemma63PolynomialSum k (q + 1) β‖

def fordLemma63SZero
    (k M : ℕ) (β : Fin k → ℝ) : ℝ :=
  ‖fordLemma63PolynomialSum k M β‖ + fordLemma63SZeroTail k M β

def fordLemma63AbelDifference
    (k n q : ℕ) (u t : ℝ) (β : Fin k → ℝ) : ℂ :=
  fordLemma63DeltaCharacter k n u t β (q + 2) -
    fordLemma63DeltaCharacter k n u t β (q + 1)

def fordLemma63AbelRemainder
    (k M n : ℕ) (u t : ℝ) (β : Fin k → ℝ) : ℂ :=
  ∑ q ∈ Finset.range (M - 1),
    fordLemma63AbelDifference k n q u t β * fordLemma63PolynomialSum k (q + 1) β

theorem fordLemma63_log_phase_factorization
    {k m n : ℕ} {u t : ℝ} {β : Fin k → ℝ} :
    fordLogOscillation t ((m : ℝ) / ((n : ℝ) + u)) =
      fordAdditiveCharacter (fordLemma63PolynomialPhase β m) *
        fordLemma63DeltaCharacter k n u t β m := by
  unfold fordLogOscillation fordLemma63PolynomialPhase
    fordLemma63DeltaCharacter fordLemma63Delta fordAdditiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  abel

theorem fordLemma63PolynomialSum_eq_vinogradovWeylSum
    (k Q : ℕ) (β : Fin k → ℝ) :
    fordLemma63PolynomialSum k Q β =
      fordVinogradovWeylSum k Q (fun j => (β j : UnitAddCircle)) := by
  unfold fordLemma63PolynomialSum fordVinogradovWeylSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold fordLemma63PolynomialPhase fordAdditiveCharacter
    fordVinogradovMonomial UnitAddTorus.mFourier fordVinogradovExponent
  simp only [ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf

/-- The real phase changes by at most `1/(pi*M)` across a unit subinterval. -/
theorem abs_fordLemma63Delta_sub_le
    {k M N n q : ℕ} {u t : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hq : q + 1 ≤ M) (hβ : β ∈ fordLemma63Omega k M n u t) :
    |fordLemma63Delta k n u t β (q + 1) -
        fordLemma63Delta k n u t β q| ≤
      1 / (Real.pi * M) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_of_lt hN) hn)
  have hdenpos : 0 < (n : ℝ) + u := add_pos hnpos hu
  let D : Set ℝ := Set.Icc (0 : ℝ) M
  have hderiv : ∀ x ∈ D,
      HasDerivWithinAt (fordLemma63Delta k n u t β)
        (fordLemma63DeltaDeriv k n u t β x) D x := by
    intro x hx
    have hz : (n : ℝ) + u ≠ 0 := hdenpos.ne'
    have hlog : 1 + x / ((n : ℝ) + u) ≠ 0 := by
      have hx0 : 0 ≤ x := hx.1
      positivity
    exact (hasDerivAt_fordLemma63Delta hz hlog).hasDerivWithinAt
  have hbound : ∀ x ∈ D,
      ‖fordLemma63DeltaDeriv k n u t β x‖ ≤ 1 / (Real.pi * M) := by
    intro x hx
    rw [Real.norm_eq_abs]
    exact abs_fordLemma63DeltaDeriv_le hk hM hN hn hu ht hscale hx hβ
  have hq0 : ((q : ℝ)) ∈ D := by
    constructor
    · positivity
    · exact_mod_cast (show q ≤ M by omega)
  have hq1 : (((q + 1 : ℕ) : ℝ)) ∈ D := by
    constructor
    · positivity
    · exact_mod_cast hq
  have hmv := (convex_Icc (0 : ℝ) M).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hq0 hq1
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have hdist : |((q + 1 : ℕ) : ℝ) - q| = 1 := by
    push_cast
    simp
  rw [hdist, mul_one] at hmv
  simpa only [Nat.cast_add, Nat.cast_one] using hmv

/-- The additive-character multiplier has Ford's exact step variation
`2/M`. -/
theorem norm_fordLemma63DeltaCharacter_sub_le
    {k M N n q : ℕ} {u t : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hq : q + 1 ≤ M) (hβ : β ∈ fordLemma63Omega k M n u t) :
    ‖fordLemma63DeltaCharacter k n u t β (q + 1) -
        fordLemma63DeltaCharacter k n u t β q‖ ≤ 2 / M := by
  let a := fordLemma63Delta k n u t β (q + 1)
  let b := fordLemma63Delta k n u t β q
  have hfactor :
      fordAdditiveCharacter a - fordAdditiveCharacter b =
        fordAdditiveCharacter b *
          (Complex.exp (Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)) - 1) := by
    unfold fordAdditiveCharacter
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  change ‖fordAdditiveCharacter a - fordAdditiveCharacter b‖ ≤ _
  rw [hfactor, norm_mul]
  have hunit : ‖fordAdditiveCharacter b‖ = 1 := by
    unfold fordAdditiveCharacter
    rw [Complex.norm_exp]
    simp
  rw [hunit, one_mul]
  calc
    ‖Complex.exp (Complex.I * ((2 * Real.pi * (a - b) : ℝ) : ℂ)) - 1‖ ≤
        ‖2 * Real.pi * (a - b)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by norm_num),
        abs_of_pos Real.pi_pos]
    _ ≤ 2 * Real.pi * (1 / (Real.pi * M)) := by
      gcongr
      exact abs_fordLemma63Delta_sub_le hk hM hN hn hu ht hscale hq hβ
    _ = 2 / M := by
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      field_simp [Real.pi_ne_zero, hMpos.ne']

/-- Exact discrete Abel identity for Ford's inner logarithmic sum. -/
theorem fordLemma63T_abel_identity
    {k M n : ℕ} {u t : ℝ} {β : Fin k → ℝ}
    (hM : 1 ≤ M) :
    fordLemma63T M n u t =
      fordLemma63DeltaCharacter k n u t β M *
          fordLemma63PolynomialSum k M β -
        fordLemma63AbelRemainder k M n u t β := by
  let f : ℕ → ℂ := fun q => fordLemma63DeltaCharacter k n u t β (q + 1)
  let g : ℕ → ℂ := fun q =>
    fordAdditiveCharacter (fordLemma63PolynomialPhase β (q + 1))
  have hab := Finset.sum_range_by_parts f g M
  have hleft :
      (∑ i ∈ Finset.range M, f i • g i) = fordLemma63T M n u t := by
    have hIcc : Finset.Icc 1 M =
        (Finset.range M).image (fun i : ℕ => i + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hx
        refine ⟨x - 1, ?_, ?_⟩
        · omega
        · omega
      · rintro ⟨i, hi, rfl⟩
        omega
    have hsum :
        (∑ m ∈ Finset.Icc 1 M,
          fordLogOscillation t ((m : ℝ) / ((n : ℝ) + u))) =
        ∑ i ∈ Finset.range M,
          fordLogOscillation t (((i + 1 : ℕ) : ℝ) / ((n : ℝ) + u)) := by
      rw [hIcc, Finset.sum_image]
      intro a _ha b _hb hab
      exact Nat.add_right_cancel hab
    unfold fordLemma63T f g
    rw [hsum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [fordLemma63_log_phase_factorization (k := k) (β := β)]
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    exact mul_comm _ _
  rw [hleft] at hab
  have hMcast : ((M - 1 : ℕ) : ℝ) + 1 = M := by
    exact_mod_cast Nat.sub_add_cancel hM
  simpa only [f, g, smul_eq_mul, hMcast, Nat.add_assoc, add_assoc,
    one_add_one_eq_two,
    Nat.cast_add, Nat.cast_one, fordLemma63PolynomialSum,
    fordLemma63AbelDifference, fordLemma63AbelRemainder] using hab

private theorem norm_finset_sum_mul_le_const
    (s : Finset ℕ) (a b : ℕ → ℂ) (C : ℝ)
    (ha : ∀ q ∈ s, ‖a q‖ ≤ C) :
    ‖∑ q ∈ s, a q * b q‖ ≤ ∑ q ∈ s, C * ‖b q‖ := by
  calc
    ‖∑ q ∈ s, a q * b q‖ ≤ ∑ q ∈ s, ‖a q * b q‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ha q hq) (norm_nonneg _)

theorem norm_fordLemma63AbelDifference_le
    {k M N n q : ℕ} {u t : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hq : q + 2 ≤ M) (hβ : β ∈ fordLemma63Omega k M n u t) :
    ‖fordLemma63AbelDifference k n q u t β‖ ≤ 2 / M := by
  unfold fordLemma63AbelDifference
  simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc,
    one_add_one_eq_two] using
      (norm_fordLemma63DeltaCharacter_sub_le
        hk hM hN hn hu ht hscale (q := q + 1) (by omega) hβ)

theorem norm_fordLemma63AbelRemainder_le
    {k M N n : ℕ} {u t : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hβ : β ∈ fordLemma63Omega k M n u t) :
    ‖fordLemma63AbelRemainder k M n u t β‖ ≤ fordLemma63SZeroTail k M β := by
  unfold fordLemma63AbelRemainder fordLemma63SZeroTail
  rw [Finset.mul_sum]
  apply norm_finset_sum_mul_le_const
  intro q hq
  exact norm_fordLemma63AbelDifference_le
    hk hM hN hn hu ht hscale
      (by simp only [Finset.mem_range] at hq; omega) hβ

/-- Pointwise partial summation, exactly the `S_0(beta)` majorant in Ford's
proof (with the integral replaced by its lossless discrete Abel form). -/
theorem norm_fordLemma63T_le_SZero
    {k M N n : ℕ} {u t : ℝ} {β : Fin k → ℝ}
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : N ≤ n)
    (hu : 0 < u) (ht : 0 ≤ t)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1))
    (hβ : β ∈ fordLemma63Omega k M n u t) :
    ‖fordLemma63T M n u t‖ ≤ fordLemma63SZero k M β := by
  rw [fordLemma63T_abel_identity hM]
  have hunit : ‖fordLemma63DeltaCharacter k n u t β M‖ = 1 := by
    unfold fordLemma63DeltaCharacter fordAdditiveCharacter
    rw [Complex.norm_exp]
    simp
  calc
    ‖fordLemma63DeltaCharacter k n u t β M *
          fordLemma63PolynomialSum k M β -
        fordLemma63AbelRemainder k M n u t β‖ ≤
      ‖fordLemma63DeltaCharacter k n u t β M *
          fordLemma63PolynomialSum k M β‖ +
        ‖fordLemma63AbelRemainder k M n u t β‖ := norm_sub_le _ _
    _ ≤ ‖fordLemma63PolynomialSum k M β‖ +
        fordLemma63SZeroTail k M β := by
      rw [norm_mul, hunit, one_mul]
      refine add_le_add_right ?_ _
      exact norm_fordLemma63AbelRemainder_le hk hM hN hn hu ht hscale hβ
    _ = _ := rfl

/-- The polynomial sum is the exact Weyl sum, so its complete unit-cube
moment is the Vinogradov mean value `J_{s,k}(Q)`. -/
theorem fordLemma63PolynomialSum_unitCube_mean_eq
    (s k Q : ℕ) :
    (∫ (α : Fin k → ℝ) in
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1},
        ‖fordLemma63PolynomialSum k Q α‖ ^ (2 * s)) =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  have hfun :
      (fun α : Fin k → ℝ => ‖fordLemma63PolynomialSum k Q α‖ ^ (2 * s)) =
        fun α : Fin k → ℝ =>
          ‖fordVinogradovWeylSum k Q (fun j => (α j : UnitAddCircle))‖ ^ (2 * s) := by
    funext α
    rw [fordLemma63PolynomialSum_eq_vinogradovWeylSum]
  rw [hfun]
  exact ford_equation_1_3 s k Q

#print axioms fordLemma63_log_phase_factorization
#print axioms abs_fordLemma63Delta_sub_le
#print axioms norm_fordLemma63DeltaCharacter_sub_le
#print axioms fordLemma63T_abel_identity
#print axioms norm_fordLemma63T_le_SZero
#print axioms fordLemma63PolynomialSum_unitCube_mean_eq

end

end GafniTao
