import Tao2026.Vinogradov

/-!
# The effective Iwaniec--Kowalski degree

The Taylor cutoff in the source proof is
`10 * ceil (log F / log X)`.  The polynomial mean-value argument, however,
uses the smaller effective degree `floor (4 * log F / log X)`.  This module
records that second parameter and the elementary comparisons needed to split
the two roles.
-/

namespace Tao2026

open scoped ContDiff

/-- The polynomial degree used in Theorem 8.25 of Iwaniec--Kowalski after
choosing the fourth-root averaging range. -/
noncomputable def vinogradovIKDegree (X F : ℝ) : ℕ :=
  ⌊4 * (Real.log F / Real.log X)⌋₊

/-- The source hypothesis `X^4 ≤ F` makes the logarithmic scale ratio at
least four. -/
theorem four_le_vinogradov_log_ratio
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    4 ≤ Real.log F / Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  rw [le_div_iff₀ hlogX]
  calc
    4 * Real.log X = Real.log (X ^ 4) := by
      rw [Real.log_pow]
      norm_num
    _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh

/-- The effective degree is bounded above by its defining real parameter. -/
theorem vinogradovIKDegree_cast_le
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovIKDegree X F : ℝ) ≤
      4 * (Real.log F / Real.log X) := by
  rw [vinogradovIKDegree]
  exact Nat.floor_le (mul_nonneg (by norm_num)
    (by linarith [four_le_vinogradov_log_ratio hX hFhigh]))

/-- The reverse floor comparison, with the unavoidable additive one. -/
theorem four_mul_vinogradov_log_ratio_lt_IKDegree_add_one
    (X F : ℝ) :
    4 * (Real.log F / Real.log X) < (vinogradovIKDegree X F : ℝ) + 1 := by
  rw [vinogradovIKDegree]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Nat.lt_floor_add_one (4 * (Real.log F / Real.log X))

/-- In the source range the effective degree is already at least sixteen. -/
theorem sixteen_le_vinogradovIKDegree
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    16 ≤ vinogradovIKDegree X F := by
  rw [vinogradovIKDegree]
  apply Nat.le_floor
  nlinarith [four_le_vinogradov_log_ratio hX hFhigh]

/-- A convenient lower comparison used for all derivative orders in the
medium-coefficient block. -/
theorem two_mul_vinogradov_log_ratio_le_IKDegree
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    2 * (Real.log F / Real.log X) ≤ (vinogradovIKDegree X F : ℝ) := by
  have hs := four_le_vinogradov_log_ratio hX hFhigh
  have hfloor := four_mul_vinogradov_log_ratio_lt_IKDegree_add_one X F
  linarith

/-- The effective degree is no larger than the source's Taylor-remainder
degree. -/
theorem vinogradovIKDegree_le_vinogradovTaylorDegree
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    vinogradovIKDegree X F ≤ vinogradovTaylorDegree X F := by
  have hs := four_le_vinogradov_log_ratio hX hFhigh
  have hfloor := vinogradovIKDegree_cast_le hX hFhigh
  have hceil : Real.log F / Real.log X ≤
      (⌈Real.log F / Real.log X⌉₊ : ℝ) := Nat.le_ceil _
  have hreal : (vinogradovIKDegree X F : ℝ) ≤
      (vinogradovTaylorDegree X F : ℝ) := by
    rw [vinogradovTaylorDegree]
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- Hence every derivative needed by the effective polynomial is available
under the original source cutoff. -/
theorem vinogradovIKDegree_add_one_le_vinogradovDerivativeCutoff
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    vinogradovIKDegree X F + 1 ≤ vinogradovDerivativeCutoff X F := by
  rw [← vinogradovTaylorDegree_add_one]
  exact Nat.add_le_add_right
    (vinogradovIKDegree_le_vinogradovTaylorDegree hX hFhigh) 1

/-- Taylor replacement at the effective IK degree.  The derivative used in
the remainder is `k + 1`, not the much larger source cutoff. -/
theorem norm_sum_standardAdditiveCharacter_vinogradovIKPolynomial_sub_le
    (s : Finset ℕ) {f : ℝ → ℝ} {X F α q u v : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) (hq : 0 < q)
    (hXn : ∀ n ∈ s, X ≤ (n : ℝ))
    (hwindow : ∀ n ∈ s,
      Set.Icc (n : ℝ) (n + q) ⊆ Set.Icc u v)
    (hsmooth : ∀ t ∈ Set.Icc u v, ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc u v, ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n q)‖ ≤
      2 * Real.pi * (s.card : ℝ) *
        ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
          (q / X) ^ (vinogradovIKDegree X F + 1)) := by
  have hF : 0 ≤ F := (by positivity : 0 ≤ X ^ 4).trans hFhigh
  have htopOne : 1 ≤ vinogradovIKDegree X F + 1 := by omega
  have htopCutoff :=
    vinogradovIKDegree_add_one_le_vinogradovDerivativeCutoff hX hFhigh
  have hTaylor :=
    norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_normalized
      s (show 0 < X by linarith) hq
      (mul_nonneg (pow_nonneg (by linarith) _) hF) hXn
      (R := vinogradovIKDegree X F)
      (B := α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F)
      (fun n hn t ht =>
        ((contDiffAt_infty.mp (hsmooth t (hwindow n hn ht)))
          (vinogradovIKDegree X F + 1)).contDiffWithinAt)
      (fun n hn ξ hξ =>
        (hderiv ξ (hwindow n hn hξ) (vinogradovIKDegree X F + 1)
          htopOne htopCutoff).2)
  have hsum :
      (∑ n ∈ s, standardAdditiveCharacter
        (taylorWithinEval f (vinogradovIKDegree X F)
          (Set.Icc (n : ℝ) (n + q)) n (n + q))) =
        ∑ n ∈ s, standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n q) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply taylorWithinEval_eq_vinogradovTaylorPolynomial hq
    exact hsmooth n (hwindow n hn ⟨le_rfl, by linarith⟩)
  rw [hsum] at hTaylor
  exact hTaylor

/-- Integer-interval Taylor reduction at the effective degree. -/
theorem norm_sum_Ico_standardAdditiveCharacter_sub_vinogradovIKPolynomial_le
    {f : ℝ → ℝ} {X F α : ℝ} {a b q : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hq : 0 < q) (hXa : X ≤ (a : ℝ))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
        ∑ n ∈ Finset.Ico a (b - q), standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n q)‖ ≤
      (q : ℝ) + 2 * Real.pi * ((Finset.Ico a (b - q)).card : ℝ) *
        ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
          ((q : ℝ) / X) ^ (vinogradovIKDegree X F + 1)) := by
  let S : Finset ℕ := Finset.Ico a (b - q)
  have hXn : ∀ n ∈ S, X ≤ (n : ℝ) := by
    intro n hn
    exact hXa.trans (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
  have hwindow : ∀ n ∈ S,
      Set.Icc (n : ℝ) (n + (q : ℝ)) ⊆ Set.Icc (a : ℝ) (b : ℝ) := by
    intro n hn t ht
    have hn := Finset.mem_Ico.mp hn
    constructor
    · exact (by exact_mod_cast hn.1 : (a : ℝ) ≤ n) |>.trans ht.1
    · exact ht.2.trans (by exact_mod_cast (show n + q ≤ b by omega))
  have hTaylor :=
    norm_sum_standardAdditiveCharacter_vinogradovIKPolynomial_sub_le
      S hX hFhigh hα (by exact_mod_cast hq) hXn hwindow hsmooth hderiv
  have hshift :=
    norm_sum_Ico_standardAdditiveCharacter_sub_forwardShift_le f a b q
  calc
    ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
        ∑ n ∈ S, standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n q)‖ =
      ‖((∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
          ∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))) +
        ((∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))) -
          ∑ n ∈ S, standardAdditiveCharacter
            (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n q))‖ := by
        congr 1
        ring
    _ ≤ ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
          ∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))‖ +
        ‖(∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))) -
          ∑ n ∈ S, standardAdditiveCharacter
            (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n q)‖ :=
      norm_add_le _ _
    _ ≤ (q : ℝ) + 2 * Real.pi * (S.card : ℝ) *
        ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
          ((q : ℝ) / X) ^ (vinogradovIKDegree X F + 1)) := by
      exact add_le_add (by simpa only [S, Nat.cast_add] using hshift) hTaylor

/-- Boundary plus effective-degree Taylor error for one product shift. -/
noncomputable def vinogradovIKTaylorShiftError
    (X F α : ℝ) (a b : ℕ) (p : ℕ × ℕ) : ℝ :=
  ((p.1 * p.2 : ℕ) : ℝ) +
    2 * Real.pi * ((Finset.Ico a (b - p.1 * p.2)).card : ℝ) *
      ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
        (((p.1 * p.2 : ℕ) : ℝ) / X) ^ (vinogradovIKDegree X F + 1))

/-- Uniform effective-degree Taylor envelope over product shifts. -/
noncomputable def vinogradovIKTaylorShiftErrorEnvelope
    (X F α : ℝ) (a b V : ℕ) : ℝ :=
  ((V ^ 2 : ℕ) : ℝ) +
    2 * Real.pi * ((b - a : ℕ) : ℝ) *
      ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
        (((V ^ 2 : ℕ) : ℝ) / X) ^ (vinogradovIKDegree X F + 1))

/-- Summing the effective-degree error over the product multiset costs its
cardinality times the uniform envelope. -/
theorem sum_vinogradovIKTaylorShiftError_le_envelope
    {X F α : ℝ} {a b V : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) :
    ∑ p ∈ vinogradovShiftPairs V, vinogradovIKTaylorShiftError X F α a b p ≤
      ((V ^ 2 : ℕ) : ℝ) *
        vinogradovIKTaylorShiftErrorEnvelope X F α a b V := by
  have hF : 0 ≤ F := (by positivity : 0 ≤ X ^ 4).trans hFhigh
  have hB : 0 ≤ α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F :=
    mul_nonneg (pow_nonneg (by linarith) _) hF
  calc
    ∑ p ∈ vinogradovShiftPairs V, vinogradovIKTaylorShiftError X F α a b p ≤
        ∑ _p ∈ vinogradovShiftPairs V,
          vinogradovIKTaylorShiftErrorEnvelope X F α a b V := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
      have hx := Finset.mem_Icc.mp hp₁
      have hy := Finset.mem_Icc.mp hp₂
      have hqV : p.1 * p.2 ≤ V ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul hx.2 hy.2
      have hcard : (Finset.Ico a (b - p.1 * p.2)).card ≤ b - a := by
        simp only [Nat.card_Ico]
        omega
      unfold vinogradovIKTaylorShiftError
        vinogradovIKTaylorShiftErrorEnvelope
      apply add_le_add
      · exact_mod_cast hqV
      · gcongr
    _ = ((V ^ 2 : ℕ) : ℝ) *
        vinogradovIKTaylorShiftErrorEnvelope X F α a b V := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vinogradovShiftPairs]

/-- Exact product-multiset averaging reduction at the effective degree. -/
theorem norm_vinogradovShiftPairs_nsmul_sum_sub_IKPolynomialPairSum_le
    {f : ℝ → ℝ} {X F α : ℝ} {a b V : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hXa : X ≤ (a : ℝ))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(V ^ 2) • (∑ n ∈ Finset.Ico a b,
          standardAdditiveCharacter (f n)) -
        vinogradovTaylorPolynomialPairSum f
          (vinogradovIKDegree X F) a b V‖ ≤
      ∑ p ∈ vinogradovShiftPairs V,
        vinogradovIKTaylorShiftError X F α a b p := by
  rw [← card_vinogradovShiftPairs V]
  unfold vinogradovTaylorPolynomialPairSum
  refine (norm_card_nsmul_sub_sum_le_sum_norm_sub
    (vinogradovShiftPairs V)
    (∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n))
    (fun p => ∑ n ∈ Finset.Ico a (b - p.1 * p.2),
      standardAdditiveCharacter
        (vinogradovTaylorPolynomial f (vinogradovIKDegree X F) n
          ((p.1 * p.2 : ℕ) : ℝ)))).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  have hx := Finset.mem_Icc.mp hp₁
  have hy := Finset.mem_Icc.mp hp₂
  have hq : 0 < p.1 * p.2 := Nat.mul_pos hx.1 hy.1
  simpa only [vinogradovIKTaylorShiftError] using
    (norm_sum_Ico_standardAdditiveCharacter_sub_vinogradovIKPolynomial_le
      hX hFhigh hα hq hXa hsmooth hderiv)

/-- Any effective-degree polynomial pair-sum estimate transfers to the
original exponential sum with the effective Taylor envelope. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_IKPolynomialPairSum
    {f : ℝ → ℝ} {X F α : ℝ} {a b V : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hV : 1 ≤ V) (hXa : X ≤ (a : ℝ))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovIKDegree X F) a b V‖ ≤ ((V ^ 2 : ℕ) : ℝ) * A) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      vinogradovIKTaylorShiftErrorEnvelope X F α a b V + A := by
  apply norm_le_of_square_nsmul_sub_le_and_norm_le hV
  · exact
      (norm_vinogradovShiftPairs_nsmul_sum_sub_IKPolynomialPairSum_le
        hX hFhigh hα hXa hsmooth hderiv).trans
        (sum_vinogradovIKTaylorShiftError_le_envelope hX hFhigh hα)
  · exact hpoly

/-- At the fourth-root range, the raw effective Taylor envelope has the
same source shape as before, with top order `k+1`. -/
theorem vinogradovIKTaylorShiftErrorEnvelope_averagingRange_le
    {X F α : ℝ} {a b : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hlength : ((b - a : ℕ) : ℝ) ≤ X) :
    vinogradovIKTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤
      Real.sqrt X + 2 * Real.pi * X *
        ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovIKDegree X F + 1)) := by
  have hXpos : 0 < X := by linarith
  have hF : 0 ≤ F := (by positivity : 0 ≤ X ^ 4).trans hFhigh
  have hB : 0 ≤ α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F :=
    mul_nonneg (pow_nonneg (by linarith) _) hF
  have hV := vinogradovAveragingRange_sq_le_sqrt X
  have hratio :
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) / X ≤
        Real.sqrt X / X := by
    exact (div_le_div_iff_of_pos_right hXpos).2 hV
  unfold vinogradovIKTaylorShiftErrorEnvelope
  apply add_le_add hV
  gcongr

/-- Vinogradov's numerical smallness condition makes the complete Taylor
remainder negligible already at the effective degree `k`.  This is the
quantitative point that permits the source's Taylor cutoff and mean-value
degree to be separated. -/
theorem vinogradovIKTaylorRemainder_le_one
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000) :
    X * (α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
        (Real.sqrt X / X) ^ (vinogradovIKDegree X F + 1) ≤ 1 := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := by
    apply Real.log_pos
    calc
      1 < (2 : ℝ) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
      _ ≤ F := hFhigh
  have hlogAlpha : 0 ≤ Real.log α := Real.log_nonneg hα
  let s := Real.log F / Real.log X
  let R : ℝ := (vinogradovIKDegree X F + 1 : ℕ)
  have hs : 4 ≤ s := by
    simpa only [s] using four_le_vinogradov_log_ratio hX hFhigh
  have hsnonneg : 0 ≤ s := by linarith
  have hRlower : 4 * s < R := by
    simpa only [s, R, Nat.cast_add, Nat.cast_one] using
      four_mul_vinogradov_log_ratio_lt_IKDegree_add_one X F
  have hRupper : R ≤ (17 / 4 : ℝ) * s := by
    have hk := vinogradovIKDegree_cast_le hX hFhigh
    dsimp only [R, s]
    push_cast
    nlinarith
  have hRnonneg : 0 ≤ R := by positivity
  have hcube : R ^ 3 ≤ ((17 / 4 : ℝ) * s) ^ 3 :=
    pow_le_pow_left₀ hRnonneg hRupper 3
  have hlogIdentity : Real.log F = s * Real.log X := by
    dsimp only [s]
    field_simp
  have hlogBound :
      R ^ 3 * Real.log α ≤ (R / 2 - s - 1) * Real.log X := by
    have hmul : R ^ 3 * Real.log α ≤
        ((17 / 4 : ℝ) * s) ^ 3 * Real.log α :=
      mul_le_mul_of_nonneg_right hcube hlogAlpha
    have hidentity : ((17 / 4 : ℝ) * s) ^ 3 * Real.log α =
        (4913 / 64 : ℝ) *
          (Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3) *
            Real.log F := by
      dsimp only [s]
      field_simp
      ring
    have hsmallMul :
        (4913 / 64 : ℝ) *
            (Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3) *
              Real.log F <
          (4913 / 64 : ℝ) * (1 / 1000 : ℝ) * Real.log F := by
      gcongr
    have htiny :
        (4913 / 64 : ℝ) * (1 / 1000 : ℝ) * Real.log F <
          (1 / 13 : ℝ) * Real.log F := by
      nlinarith
    have hRmul := mul_lt_mul_of_pos_right hRlower hlogX
    have hmargin : (1 / 13 : ℝ) * Real.log F <
        (R / 2 - s - 1) * Real.log X := by
      rw [hlogIdentity]
      nlinarith [mul_pos (show (0 : ℝ) < 12 / 13 by norm_num) hlogX]
    exact (hmul.trans_lt (by rw [hidentity]; exact hsmallMul.trans htiny)).trans
      hmargin |>.le
  have hαpow : α ^ ((vinogradovIKDegree X F + 1) ^ 3) ≤
      X ^ (R / 2 - s - 1) := by
    apply Real.le_rpow_of_log_le hXpos
    rw [Real.log_pow]
    norm_num only [Nat.cast_pow]
    simpa only [R] using hlogBound
  have hFpow : F ≤ X ^ s := by
    apply Real.le_rpow_of_log_le hXpos
    rw [hlogIdentity]
  have hbase : Real.sqrt X / X = X ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      X ^ (1 / (2 : ℝ)) / X = X ^ (1 / (2 : ℝ)) / X ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = X ^ (1 / (2 : ℝ) - 1) := Real.rpow_sub hXpos _ _ |>.symm
      _ = X ^ (-1 / 2 : ℝ) := by
        congr 1
        ring
  have hbasepow : (Real.sqrt X / X) ^ (vinogradovIKDegree X F + 1) =
      X ^ (-R / 2) := by
    rw [hbase, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    congr 1
    dsimp only [R]
    push_cast
    ring
  have hfirstRpow : X * X ^ (R / 2 - s - 1) =
      X ^ ((1 : ℝ) + (R / 2 - s - 1)) := by
    calc
      X * X ^ (R / 2 - s - 1) =
          X ^ (1 : ℝ) * X ^ (R / 2 - s - 1) := by rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (R / 2 - s - 1)) :=
        (Real.rpow_add hXpos _ _).symm
  rw [hbasepow]
  calc
    X * (α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) * X ^ (-R / 2) ≤
        X * (X ^ (R / 2 - s - 1) * X ^ s) * X ^ (-R / 2) := by
      gcongr
    _ = X ^ ((1 : ℝ) + (R / 2 - s - 1) + s + (-R / 2)) := by
      calc
        X * (X ^ (R / 2 - s - 1) * X ^ s) * X ^ (-R / 2) =
            (X * X ^ (R / 2 - s - 1)) * X ^ s * X ^ (-R / 2) := by ring
        _ = X ^ ((1 : ℝ) + (R / 2 - s - 1)) * X ^ s *
            X ^ (-R / 2) := by rw [hfirstRpow]
        _ = X ^ ((1 : ℝ) + (R / 2 - s - 1) + s) * X ^ (-R / 2) := by
          rw [← Real.rpow_add hXpos]
        _ = X ^ ((1 : ℝ) + (R / 2 - s - 1) + s + (-R / 2)) := by
          rw [← Real.rpow_add hXpos]
    _ = 1 := by
      rw [show (1 : ℝ) + (R / 2 - s - 1) + s + (-R / 2) = 0 by ring,
        Real.rpow_zero]

/-- Complete discharge of the effective-degree Taylor envelope. -/
theorem vinogradovIKTaylorShiftErrorEnvelope_averagingRange_le_source
    {X F α : ℝ} {a b : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hlength : ((b - a : ℕ) : ℝ) ≤ X)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000) :
    vinogradovIKTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤ Real.sqrt X + 2 * Real.pi := by
  have htail := vinogradovIKTaylorRemainder_le_one hX hFhigh hα hsmall
  have htwoPi : 0 ≤ 2 * Real.pi := by positivity
  calc
    vinogradovIKTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤
      Real.sqrt X + 2 * Real.pi * X *
        ((α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovIKDegree X F + 1)) :=
      vinogradovIKTaylorShiftErrorEnvelope_averagingRange_le
        hX hFhigh hα hlength
    _ = Real.sqrt X + (2 * Real.pi) *
        (X * (α ^ ((vinogradovIKDegree X F + 1) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovIKDegree X F + 1)) := by ring
    _ ≤ Real.sqrt X + (2 * Real.pi) * 1 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htail htwoPi)
    _ = Real.sqrt X + 2 * Real.pi := by ring

/-- Source-specialized transfer theorem with the pair sum at the effective
IK degree, rather than at the Taylor-remainder cutoff. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_IKSourcePairSum
    {f : ℝ → ℝ} {X F α : ℝ} {a b : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000)
    (hXa : X ≤ (a : ℝ)) (hlength : ((b - a : ℕ) : ℝ) ≤ X)
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovIKDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * A) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      Real.sqrt X + 2 * Real.pi + A := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have htransfer :=
    norm_sum_Ico_standardAdditiveCharacter_le_of_IKPolynomialPairSum
      hX hFhigh hα hV hXa hsmooth hderiv hpoly
  exact htransfer.trans (add_le_add
    (vinogradovIKTaylorShiftErrorEnvelope_averagingRange_le_source
      hX hFhigh hα hlength hsmall) le_rfl)

/-- Contract-shaped effective-degree Taylor reduction for an arbitrary
integer interval contained in `[X,2X]`. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_IKSourcePairSum_of_subset
    {f : ℝ → ℝ} {X F α : ℝ} {a b : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000)
    (hI : Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc X (2 * X))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovIKDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * A) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      Real.sqrt X + 2 * Real.pi + A := by
  by_cases hab : a < b
  · have habReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
    have hXa : X ≤ (a : ℝ) := (hI ⟨le_rfl, habReal⟩).1
    have hbX : (b : ℝ) ≤ 2 * X := (hI ⟨habReal, le_rfl⟩).2
    have hlength : ((b - a : ℕ) : ℝ) ≤ X := by
      rw [Nat.cast_sub hab.le]
      linarith
    exact norm_sum_Ico_standardAdditiveCharacter_le_of_IKSourcePairSum
      hX hFhigh hα hsmall hXa hlength hsmooth hderiv hpoly
  · rw [Finset.Ico_eq_empty hab, Finset.sum_empty, norm_zero]
    have hsqrt : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hpi : 0 < Real.pi := Real.pi_pos
    have hAnorm : 0 ≤ A := by
      have hnorm := norm_nonneg (vinogradovTaylorPolynomialPairSum f
        (vinogradovIKDegree X F) a b (vinogradovAveragingRange X))
      have hVpos : 0 < (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) := by
        have := vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
        positivity
      nlinarith
    positivity

end Tao2026
