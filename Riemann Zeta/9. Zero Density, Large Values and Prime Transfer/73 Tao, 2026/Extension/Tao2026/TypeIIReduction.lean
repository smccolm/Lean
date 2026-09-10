import Tao2026.VinogradovPhase
import Tao2026.ShortIntervalDecomposition
import Mathlib.Algebra.Order.Chebyshev

/-!
# Type II correlation reduction

This module proves the exact finite algebra used after Cauchy--Schwarz in the
Type II portion of Proposition 1.12.  It expands a squared complex sum into a
double correlation sum and rewrites every phase difference into the source's
reciprocal phase with the transformed parameters.
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

/-- Finite Cauchy--Schwarz in the squared-norm form used for the Type II
outer sum. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ S, f x‖ ^ 2 ≤
      (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
  have htri : ‖∑ x ∈ S, f x‖ ≤ ∑ x ∈ S, ‖f x‖ :=
    norm_sum_le S f
  calc
    ‖∑ x ∈ S, f x‖ ^ 2 ≤ (∑ x ∈ S, ‖f x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (S.card : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := S) (f := fun x => ‖f x‖))

/-- Algebraic expansion of a finite complex sum times its conjugate. -/
theorem sum_mul_conj_sum_eq_doubleSum
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    (∑ x ∈ S, f x) * conj (∑ x ∈ S, f x) =
      ∑ x ∈ S, ∑ y ∈ S, f x * conj (f y) := by
  rw [map_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- One inner Type II reciprocal-phase sum at the outer variable `m`. -/
def typeIIInnerSum (S : Finset ℕ) (γ : ℕ → ℂ)
    (N M : ℝ) (j m : ℕ) : ℂ :=
  ∑ n ∈ S, γ n *
    standardAdditiveCharacter (reciprocalPhase N M j (m * n))

/-- The bilinear Type II sum before Cauchy--Schwarz. -/
def typeIIOuterSum (K S : Finset ℕ) (β γ : ℕ → ℂ)
    (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ K, β m * typeIIInnerSum S γ N M j m

/-- The exact outer Cauchy--Schwarz reduction, retaining an explicit uniform
bound for the outer coefficients. -/
theorem norm_typeIIOuterSum_sq_le
    (K S : Finset ℕ) (β γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hβ : ∀ m ∈ K, ‖β m‖ ≤ L) :
    ‖typeIIOuterSum K S β γ N M j‖ ^ 2 ≤
      (K.card : ℝ) * L ^ 2 *
        ∑ m ∈ K, ‖typeIIInnerSum S γ N M j m‖ ^ 2 := by
  have hcs := norm_sum_sq_le_card_mul_sum_norm_sq K
    (fun m => β m * typeIIInnerSum S γ N M j m)
  rw [typeIIOuterSum]
  refine hcs.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg K.card)
  calc
    (∑ m ∈ K, ‖β m * typeIIInnerSum S γ N M j m‖ ^ 2) ≤
        ∑ m ∈ K, L ^ 2 * ‖typeIIInnerSum S γ N M j m‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hβ m hm) 2)
        (sq_nonneg _)
    _ = L ^ 2 * ∑ m ∈ K, ‖typeIIInnerSum S γ N M j m‖ ^ 2 := by
      rw [Finset.mul_sum]

/-- Exact double-correlation expansion of the Type II inner sum.  The
transformed phase is precisely the source's displayed `X_{n,n'}` phase. -/
theorem typeIIInnerSum_mul_conj
    (S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {m : ℕ}
    (hm : m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0) :
    typeIIInnerSum S γ N M j m * conj (typeIIInnerSum S γ N M j m) =
      ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          standardAdditiveCharacter
            (reciprocalPhase
              (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
              (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
  rw [typeIIInnerSum, sum_mul_conj_sum_eq_doubleSum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro n' hn'
  rw [map_mul]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hS n hn
  have hn'R : (n' : ℝ) ≠ 0 := by exact_mod_cast hS n' hn'
  calc
    γ n * standardAdditiveCharacter (reciprocalPhase N M j (m * n)) *
          (conj (γ n') * conj (standardAdditiveCharacter
            (reciprocalPhase N M j (m * n')))) =
        γ n * conj (γ n') *
          (standardAdditiveCharacter (reciprocalPhase N M j (m * n)) *
            conj (standardAdditiveCharacter
              (reciprocalPhase N M j (m * n')))) := by ring
    _ = _ := by
      rw [standardAdditiveCharacter_reciprocalPhase_mul_conj
        N M j hmR hnR hn'R]

/-- Real squared-norm form of the exact Type II correlation expansion. -/
theorem typeIIInnerSum_norm_sq
    (S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {m : ℕ}
    (hm : m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0) :
    ((‖typeIIInnerSum S γ N M j m‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          standardAdditiveCharacter
            (reciprocalPhase
              (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
              (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
  rw [← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self, mul_comm,
    typeIIInnerSum_mul_conj S γ N M j hm hS]

/-- Linear reciprocal coefficient after the source's Type II correlation
transformation. -/
def typeIICorrelationLinearParameter (N : ℝ) (n n' : ℕ) : ℝ :=
  N * ((n' : ℝ) - n) / ((n : ℝ) * n')

/-- Higher reciprocal coefficient after the source's Type II correlation
transformation. -/
def typeIICorrelationHigherParameter (M : ℝ) (j n n' : ℕ) : ℝ :=
  M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
    ((n : ℝ) ^ j * (n' : ℝ) ^ j)

/-- The correlation sum denoted `X_{n,n'}` in the source, for an arbitrary
finite outer support `K`. -/
def typeIICorrelationSum (K : Finset ℕ) (N M : ℝ)
    (j n n' : ℕ) : ℂ :=
  ∑ m ∈ K,
    standardAdditiveCharacter
      (reciprocalPhase
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m)

/-- On the diagonal `n' = n`, the transformed phase vanishes and the
correlation is exactly the outer support cardinality. -/
theorem typeIICorrelationSum_self
    (K : Finset ℕ) (N M : ℝ) (j n : ℕ) :
    typeIICorrelationSum K N M j n n = (K.card : ℂ) := by
  unfold typeIICorrelationSum
  simp [reciprocalPhase, standardAdditiveCharacter]

/-- Off the diagonal, a nonzero linear coefficient stays nonzero after the
source's Type II parameter transformation. -/
theorem typeIICorrelationLinearParameter_ne_zero
    {N : ℝ} {n n' : ℕ} (hN : N ≠ 0) (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hne : n ≠ n') :
    N * ((n' : ℝ) - n) / ((n : ℝ) * n') ≠ 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn'R : (n' : ℝ) ≠ 0 := by exact_mod_cast hn'
  have hdiff : (n' : ℝ) - n ≠ 0 := sub_ne_zero.mpr (by
    exact_mod_cast hne.symm)
  exact div_ne_zero (mul_ne_zero hN hdiff) (mul_ne_zero hnR hn'R)

/-- Positive powers distinguish distinct natural numbers after coercion to
the reals. -/
theorem natCast_pow_sub_ne_zero
    {n n' j : ℕ} (hj : 1 ≤ j) (hne : n ≠ n') :
    (n' : ℝ) ^ j - (n : ℝ) ^ j ≠ 0 := by
  apply sub_ne_zero.mpr
  intro heq
  have hnat : n' ^ j = n ^ j := by exact_mod_cast heq
  exact hne.symm (Nat.pow_left_injective (by omega : j ≠ 0) hnat)

/-- Off the diagonal, a nonzero higher reciprocal coefficient also stays
nonzero after the Type II transformation.  This supplies the nonvanishing
hypothesis required by the critical-interval deletion argument. -/
theorem typeIICorrelationHigherParameter_ne_zero
    {M : ℝ} {j n n' : ℕ} (hM : M ≠ 0) (hj : 1 ≤ j)
    (hn : n ≠ 0) (hn' : n' ≠ 0) (hne : n ≠ n') :
    M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j) ≠ 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn'R : (n' : ℝ) ≠ 0 := by exact_mod_cast hn'
  exact div_ne_zero
    (mul_ne_zero hM (natCast_pow_sub_ne_zero hj hne))
    (mul_ne_zero (pow_ne_zero j hnR) (pow_ne_zero j hn'R))

/-- Exact absolute size of the transformed linear reciprocal coefficient.
This is the first half of the source's comparison of the `X_{n,n'}` phase
scale with `|n'-n| / N_r` times the original phase scale. -/
theorem abs_typeIICorrelationLinearParameter
    (N : ℝ) (n n' : ℕ) :
    |N * ((n' : ℝ) - n) / ((n : ℝ) * n')| =
      |N| * |(n' : ℝ) - n| / ((n : ℝ) * n') := by
  calc
    |N * ((n' : ℝ) - n) / ((n : ℝ) * n')| =
        |N * ((n' : ℝ) - n)| / |(n : ℝ) * n'| := abs_div _ _
    _ = |N| * |(n' : ℝ) - n| / |(n : ℝ) * n'| := by rw [abs_mul]
    _ = |N| * |(n' : ℝ) - n| / ((n : ℝ) * n') := by
      have hden : 0 ≤ (n : ℝ) * n' :=
        mul_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)
        (show 0 ≤ (n' : ℝ) from Nat.cast_nonneg n')
      rw [abs_of_nonneg hden]

/-- The absolute difference of two natural indices, viewed in `ℝ`, is the
cast of their natural distance. -/
theorem abs_natCast_sub_eq_natDist_cast (n n' : ℕ) :
    |(n' : ℝ) - n| = (Nat.dist n' n : ℝ) := by
  rcases le_total n n' with h | h
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h, Nat.cast_sub h]
    exact abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring

/-- A nonzero linear frequency supplies a sharp lower bound for the
transformed Type II phase scale.  The form on the left is exactly
`distance / B` times the original linear contribution at product scale
`K*B`. -/
theorem typeIICorrelationScale_lower_of_linear
    (N M K B : ℝ) (j n n' : ℕ)
    (hK : 0 < K) (hB : 0 < B) (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    (Nat.dist n' n : ℝ) / B * (|N| / (K * B)) ≤
      reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M j n n') j K := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn'R : 0 < (n' : ℝ) := by exact_mod_cast hn'
  have hden : (n : ℝ) * n' ≤ B ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hnB hn'B hn'R.le hB.le
  have hnum : 0 ≤ |N| * (Nat.dist n' n : ℝ) := by positivity
  have hcoeff :
      |N| * (Nat.dist n' n : ℝ) / B ^ 2 ≤
        |typeIICorrelationLinearParameter N n n'| := by
    calc
      |N| * (Nat.dist n' n : ℝ) / B ^ 2 ≤
          |N| * (Nat.dist n' n : ℝ) / ((n : ℝ) * n') :=
        div_le_div_of_nonneg_left hnum (mul_pos hnR hn'R) hden
      _ = |typeIICorrelationLinearParameter N n n'| := by
        rw [typeIICorrelationLinearParameter,
          abs_typeIICorrelationLinearParameter,
          abs_natCast_sub_eq_natDist_cast]
  have hlinear :
      (|N| * (Nat.dist n' n : ℝ) / B ^ 2) / K ≤
        |typeIICorrelationLinearParameter N n n'| / K :=
    div_le_div_of_nonneg_right hcoeff hK.le
  calc
    (Nat.dist n' n : ℝ) / B * (|N| / (K * B)) =
        (|N| * (Nat.dist n' n : ℝ) / B ^ 2) / K := by
      field_simp
    _ ≤ |typeIICorrelationLinearParameter N n n'| / K := hlinear
    _ ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M j n n') j K := by
      unfold reciprocalPhaseScale
      exact le_add_of_nonneg_right (by positivity)

/-- The linear term of the reciprocal phase scale recovers the absolute
linear coefficient after multiplication by the positive base scale. -/
theorem abs_le_reciprocalPhaseScale_mul_scale
    (N M : ℝ) (j : ℕ) {Z : ℝ} (hZ : 0 < Z) :
    |N| ≤ reciprocalPhaseScale N M j Z * Z := by
  have hlinear : |N| / Z ≤ reciprocalPhaseScale N M j Z := by
    unfold reciprocalPhaseScale
    exact le_add_of_nonneg_right (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hlinear hZ.le
  calc
    |N| = (|N| / Z) * Z := by field_simp
    _ ≤ reciprocalPhaseScale N M j Z * Z := hmul

/-- For equal phase parameters and product scale at least one, the full source
scale is at most twice its linear contribution. -/
theorem reciprocalPhaseScale_equalParameters_le_two_mul_linear
    (N Z : ℝ) {j : ℕ} (hZ : 1 ≤ Z) (hj : 1 ≤ j) :
    reciprocalPhaseScale N N j Z ≤ 2 * (|N| / Z) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hZpow : Z ≤ Z ^ j := le_self_pow₀ hZ (Nat.ne_of_gt hj)
  have hhigher : |N| / Z ^ j ≤ |N| / Z :=
    div_le_div_of_nonneg_left (abs_nonneg N) hZpos hZpow
  unfold reciprocalPhaseScale
  linarith

/-- In the `N=M` specialization ultimately used by Tao, natural distance
controls the complete original phase scale, with only the explicit factor
two lost when the higher reciprocal term is absorbed. -/
theorem typeIICorrelationScale_lower_of_equalParameters
    (N K B : ℝ) {j n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B) (hj : 1 ≤ j)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    (Nat.dist n' n : ℝ) / B *
        (reciprocalPhaseScale N N j (K * B) / 2) ≤
      reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N j n n') j K := by
  have hdB : 0 ≤ (Nat.dist n' n : ℝ) / B := by positivity
  have hsource := reciprocalPhaseScale_equalParameters_le_two_mul_linear
    N (K * B) hKB hj
  have hmul := mul_le_mul_of_nonneg_left hsource hdB
  have hhalf :
      (Nat.dist n' n : ℝ) / B *
          (reciprocalPhaseScale N N j (K * B) / 2) ≤
        (Nat.dist n' n : ℝ) / B * (|N| / (K * B)) := by
    nlinarith
  exact hhalf.trans
    (typeIICorrelationScale_lower_of_linear
      N N K B j n n' hK hB hn hn' hnB hn'B)

/-- Off the diagonal, the reciprocal transformed scale is controlled by the
original equal-parameter source scale.  This is the inverse-scale term needed
in the Type II four-step effective error. -/
theorem one_div_typeIICorrelationScale_le_two_mul_B_div_sourceScale
    (N K B : ℝ) {j n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B) (hj : 1 ≤ j)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hF : 0 < reciprocalPhaseScale N N j (K * B)) :
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N j n n') j K ≤
      2 * B / reciprocalPhaseScale N N j (K * B) := by
  let F := reciprocalPhaseScale N N j (K * B)
  let F' := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter N j n n') j K
  have hdistNat : 1 ≤ Nat.dist n' n :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hne (Nat.eq_of_dist_eq_zero h).symm)
  have hdist : (1 : ℝ) ≤ (Nat.dist n' n : ℝ) := by exact_mod_cast hdistNat
  have hdiv : 1 / B ≤ (Nat.dist n' n : ℝ) / B :=
    div_le_div_of_nonneg_right hdist hB.le
  have hhalf0 : 0 ≤ F / 2 := by unfold F; positivity
  have hbaseRaw := mul_le_mul_of_nonneg_right hdiv hhalf0
  have hbase : F / (2 * B) ≤ (Nat.dist n' n : ℝ) / B * (F / 2) := by
    calc
      F / (2 * B) = (1 / B) * (F / 2) := by field_simp
      _ ≤ (Nat.dist n' n : ℝ) / B * (F / 2) := hbaseRaw
  have hlower : (Nat.dist n' n : ℝ) / B * (F / 2) ≤ F' := by
    simpa only [F, F'] using
      (typeIICorrelationScale_lower_of_equalParameters
        N K B hK hB hKB hj hn hn' hnB hn'B)
  have hbasePos : 0 < F / (2 * B) := by unfold F; positivity
  have hinv : 1 / F' ≤ 1 / (F / (2 * B)) :=
    one_div_le_one_div_of_le hbasePos (hbase.trans hlower)
  calc
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N j n n') j K = 1 / F' := by rfl
    _ ≤ 1 / (F / (2 * B)) := hinv
    _ = 2 * B / reciprocalPhaseScale N N j (K * B) := by
      unfold F
      field_simp

/-- Once the source-scaled distance is at least three, the transformed phase
scale is at least `3/2`, so its reciprocal contributes at most `2/3`.  This
is the far-pair counterpart to the trivial near-pair kernel estimate. -/
theorem one_div_typeIICorrelationScale_le_two_thirds_of_three_le_scaledDistance
    (N K B : ℝ) {j n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B) (hKB : 1 ≤ K * B) (hj : 1 ≤ j)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N N j (K * B) / B) :
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N j n n') j K ≤ 2 / 3 := by
  let F := reciprocalPhaseScale N N j (K * B)
  let F' := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter N j n n') j K
  have hlower : (Nat.dist n' n : ℝ) / B * (F / 2) ≤ F' := by
    simpa only [F, F'] using
      (typeIICorrelationScale_lower_of_equalParameters
        N K B hK hB hKB hj hn hn' hnB hn'B)
  have hthreeHalves : (3 / 2 : ℝ) ≤
      (Nat.dist n' n : ℝ) / B * (F / 2) := by
    calc
      (3 / 2 : ℝ) ≤
          ((Nat.dist n' n : ℝ) * F / B) / 2 := by
        apply div_le_div_of_nonneg_right
        · simpa only [F] using hfar
        · norm_num
      _ = (Nat.dist n' n : ℝ) / B * (F / 2) := by field_simp
  have hinv : 1 / F' ≤ 1 / (3 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (hthreeHalves.trans hlower)
  calc
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N j n n') j K = 1 / F' := by rfl
    _ ≤ 1 / (3 / 2 : ℝ) := hinv
    _ = 2 / 3 := by norm_num

/-- Exact absolute size of the transformed higher reciprocal coefficient. -/
theorem abs_typeIICorrelationHigherParameter
    (M : ℝ) (j n n' : ℕ) :
    |M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j)| =
      |M| * |(n' : ℝ) ^ j - (n : ℝ) ^ j| /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j) := by
  calc
    |M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j)| =
      |M * ((n' : ℝ) ^ j - (n : ℝ) ^ j)| /
        |(n : ℝ) ^ j * (n' : ℝ) ^ j| := abs_div _ _
    _ = |M| * |(n' : ℝ) ^ j - (n : ℝ) ^ j| /
        |(n : ℝ) ^ j * (n' : ℝ) ^ j| := by rw [abs_mul]
    _ = |M| * |(n' : ℝ) ^ j - (n : ℝ) ^ j| /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j) := by
      have hden : 0 ≤ (n : ℝ) ^ j * (n' : ℝ) ^ j :=
        mul_nonneg
        (pow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) j)
        (pow_nonneg (show 0 ≤ (n' : ℝ) from Nat.cast_nonneg n') j)
      rw [abs_of_nonneg hden]

/-- Mean-value bound for the numerator of the transformed higher reciprocal
coefficient.  On a support `n,n' ≤ B`, the power difference loses only the
source factor `j B^(j-1)`. -/
theorem abs_typeIICorrelationPowerDifference_le
    {B : ℝ} {j n n' : ℕ} (hnB : (n : ℝ) ≤ B)
    (hn'B : (n' : ℝ) ≤ B) :
    |(n' : ℝ) ^ j - (n : ℝ) ^ j| ≤
      |(n' : ℝ) - n| * (j : ℝ) * B ^ (j - 1) := by
  refine (abs_pow_sub_pow_le (n' : ℝ) (n : ℝ) j).trans ?_
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn'0 : (0 : ℝ) ≤ (n' : ℝ) := Nat.cast_nonneg n'
  have hmax : max |(n' : ℝ)| |(n : ℝ)| ≤ B :=
    max_le (by simpa only [abs_of_nonneg hn'0] using hn'B)
      (by simpa only [abs_of_nonneg hn0] using hnB)
  have hmax0 : 0 ≤ max |(n' : ℝ)| |(n : ℝ)| :=
    (abs_nonneg (n' : ℝ)).trans (le_max_left _ _)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hmax0 hmax (j - 1))
    (mul_nonneg (abs_nonneg ((n' : ℝ) - n)) (Nat.cast_nonneg j))

/-- Quantitative size bound for the transformed higher reciprocal
coefficient on a support `n,n' ≤ B`.  The denominators are deliberately left
exact; lower support bounds can therefore be inserted without losing source
constants prematurely. -/
theorem abs_typeIICorrelationHigherParameter_le
    (M : ℝ) {B : ℝ} {j n n' : ℕ} (hnB : (n : ℝ) ≤ B)
    (hn'B : (n' : ℝ) ≤ B) :
    |M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j)| ≤
      |M| * (|(n' : ℝ) - n| * (j : ℝ) * B ^ (j - 1)) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j) := by
  rw [abs_typeIICorrelationHigherParameter]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (abs_typeIICorrelationPowerDifference_le hnB hn'B)
      (abs_nonneg M))
    (mul_nonneg
      (pow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) j)
      (pow_nonneg (show 0 ≤ (n' : ℝ) from Nat.cast_nonneg n') j))

/-- The complete transformed phase scale is bounded by its exact linear
contribution and the mean-value majorant for its higher-power contribution.
This is the quantitative input used when Proposition `expi` is applied to
the source's off-diagonal sums `X_{n,n'}`. -/
theorem reciprocalPhaseScale_typeIICorrelation_le
    (N M K B : ℝ) (j n n' : ℕ) (hK : 0 ≤ K)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    reciprocalPhaseScale
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j K ≤
      (|N| * |(n' : ℝ) - n| / ((n : ℝ) * n')) / K +
        (|M| * (|(n' : ℝ) - n| * (j : ℝ) * B ^ (j - 1)) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) / K ^ j := by
  unfold reciprocalPhaseScale
  apply add_le_add
  · exact le_of_eq (congrArg (fun x : ℝ => x / K)
      (abs_typeIICorrelationLinearParameter N n n'))
  · exact div_le_div_of_nonneg_right
      (abs_typeIICorrelationHigherParameter_le M hnB hn'B)
      (pow_nonneg hK j)

/-- A positive lower support bound replaces the exact linear denominator by
`R²`. -/
theorem abs_typeIICorrelationLinearParameter_le_of_lower
    (N R : ℝ) {n n' : ℕ} (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ)) :
    |N * ((n' : ℝ) - n) / ((n : ℝ) * n')| ≤
      |N| * |(n' : ℝ) - n| / R ^ 2 := by
  rw [abs_typeIICorrelationLinearParameter]
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : R * R ≤ (n : ℝ) * n' :=
    mul_le_mul hn hn' hR.le hn0
  simpa only [pow_two] using
    (div_le_div_of_nonneg_left
      (mul_nonneg (abs_nonneg N) (abs_nonneg ((n' : ℝ) - n)))
      (mul_pos hR hR) hden)

/-- Positive lower and upper support bounds give the source-scale majorant
for the transformed higher reciprocal coefficient. -/
theorem abs_typeIICorrelationHigherParameter_le_of_bounds
    (M R B : ℝ) {j n n' : ℕ} (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ))
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    |M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
        ((n : ℝ) ^ j * (n' : ℝ) ^ j)| ≤
      |M| * (|(n' : ℝ) - n| * (j : ℝ) * B ^ (j - 1)) /
        (R ^ j * R ^ j) := by
  refine (abs_typeIICorrelationHigherParameter_le M hnB hn'B).trans ?_
  have hRpow : 0 < R ^ j := pow_pos hR j
  have hnPow : R ^ j ≤ (n : ℝ) ^ j :=
    pow_le_pow_left₀ hR.le hn j
  have hn'Pow : R ^ j ≤ (n' : ℝ) ^ j :=
    pow_le_pow_left₀ hR.le hn' j
  have hden : R ^ j * R ^ j ≤ (n : ℝ) ^ j * (n' : ℝ) ^ j :=
    mul_le_mul hnPow hn'Pow hRpow.le
      (pow_nonneg (Nat.cast_nonneg n) j)
  exact div_le_div_of_nonneg_left
    (mul_nonneg (abs_nonneg M)
      (mul_nonneg
        (mul_nonneg (abs_nonneg ((n' : ℝ) - n)) (Nat.cast_nonneg j))
        (pow_nonneg (le_trans (Nat.cast_nonneg n) hnB) (j - 1))))
    (mul_pos hRpow hRpow) hden

/-- Full transformed phase-scale bound after inserting lower and upper bounds
for the short Type II support. -/
theorem reciprocalPhaseScale_typeIICorrelation_le_of_bounds
    (N M K R B : ℝ) (j n n' : ℕ) (hK : 0 < K) (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ))
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    reciprocalPhaseScale
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j K ≤
      (|N| * |(n' : ℝ) - n| / R ^ 2) / K +
        (|M| * (|(n' : ℝ) - n| * (j : ℝ) * B ^ (j - 1)) /
          (R ^ j * R ^ j)) / K ^ j := by
  unfold reciprocalPhaseScale
  exact add_le_add
    (div_le_div_of_nonneg_right
      (abs_typeIICorrelationLinearParameter_le_of_lower N R hR hn hn') hK.le)
    (div_le_div_of_nonneg_right
      (abs_typeIICorrelationHigherParameter_le_of_bounds
        M R B hR hn hn' hnB hn'B)
      (pow_nonneg hK.le j))

/-- Exact normalization of the support-bound majorant.  It displays the
source factor `|n'-n|/R` and expresses the remaining two terms at the product
scale `K R`; the higher reciprocal term carries precisely the mean-value loss
`j (B/R)^(j-1)`. -/
theorem typeIICorrelationScaleMajorant_eq
    (N M K R B : ℝ) (k n n' : ℕ) (hK : K ≠ 0) (hR : R ≠ 0) :
    (|N| * |(n' : ℝ) - n| / R ^ 2) / K +
        (|M| * (|(n' : ℝ) - n| * ((k + 1 : ℕ) : ℝ) * B ^ k) /
          (R ^ (k + 1) * R ^ (k + 1))) / K ^ (k + 1) =
      |(n' : ℝ) - n| / R *
        (|N| / (K * R) +
          ((k + 1 : ℕ) : ℝ) * (B / R) ^ k *
            (|M| / (K * R) ^ (k + 1))) := by
  simp only [pow_succ, mul_pow, div_pow]
  field_simp

/-- Source-form comparison for the transformed phase scale.  At product
scale `K R`, an off-diagonal separation contributes the expected factor
`|n'-n|/R`; the only additional higher-power loss is
`j (B/R)^(j-1)`. -/
theorem reciprocalPhaseScale_typeIICorrelation_le_productScale
    (N M K R B : ℝ) {j n n' : ℕ} (hj : 1 ≤ j)
    (hK : 0 < K) (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ))
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B) :
    reciprocalPhaseScale
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j K ≤
      |(n' : ℝ) - n| / R *
        (|N| / (K * R) +
          (j : ℝ) * (B / R) ^ (j - 1) *
            (|M| / (K * R) ^ j)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  exact (reciprocalPhaseScale_typeIICorrelation_le_of_bounds
    N M K R B (k + 1) n n' hK hR hn hn' hnB hn'B).trans_eq
      (typeIICorrelationScaleMajorant_eq N M K R B k n n' hK.ne' hR.ne')

/-- If the two inner indices are separated by at most the lower support scale,
the transformed phase's `K⁻⁵` contribution is uniformly bounded by the source
product-scale majorant divided by `K⁵`.  This is the explicit error parameter
used by the four-step Type II theorem. -/
theorem reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_productScale
    (N M K R B : ℝ) {j n n' : ℕ} (hj : 1 ≤ j)
    (hK : 0 < K) (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ))
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hdR : (Nat.dist n' n : ℝ) ≤ R) :
    reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M j n n') j K / K ^ 5 ≤
      (|N| / (K * R) +
          (j : ℝ) * (B / R) ^ (j - 1) * (|M| / (K * R) ^ j)) /
        K ^ 5 := by
  have hscale := reciprocalPhaseScale_typeIICorrelation_le_productScale
    N M K R B hj hK hR hn hn' hnB hn'B
  rw [← abs_natCast_sub_eq_natDist_cast] at hdR
  have hratio0 : 0 ≤ |(n' : ℝ) - n| / R := by positivity
  have hratio1 : |(n' : ℝ) - n| / R ≤ 1 := by
    apply (div_le_one hR).2
    exact hdR
  have hmajorant : 0 ≤ |N| / (K * R) +
      (j : ℝ) * (B / R) ^ (j - 1) * (|M| / (K * R) ^ j) := by
    have hBR : 0 ≤ B / R := by
      have hB0 : 0 ≤ B := (Nat.cast_nonneg n).trans hnB
      positivity
    positivity
  have huniform : reciprocalPhaseScale
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j K ≤
      |N| / (K * R) +
        (j : ℝ) * (B / R) ^ (j - 1) * (|M| / (K * R) ^ j) :=
    hscale.trans <| by
      have hmul := mul_le_mul_of_nonneg_right hratio1 hmajorant
      simpa using hmul
  apply div_le_div_of_nonneg_right _ (pow_nonneg hK.le 5)
  simpa only [typeIICorrelationLinearParameter,
    typeIICorrelationHigherParameter] using huniform

/-- Version of the product-scale upper bound with a separate separation
majorant `D`.  This is the form naturally used on a short interval: `R` is
its left endpoint, whereas `D` is its length. -/
theorem reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_productScale_of_dist
    (N M K R B D : ℝ) {j n n' : ℕ} (hj : 1 ≤ j)
    (hK : 0 < K) (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ))
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hdD : (Nat.dist n' n : ℝ) ≤ D) :
    reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M j n n') j K / K ^ 5 ≤
      (D / R * (|N| / (K * R) +
          (j : ℝ) * (B / R) ^ (j - 1) * (|M| / (K * R) ^ j))) /
        K ^ 5 := by
  have hscale := reciprocalPhaseScale_typeIICorrelation_le_productScale
    N M K R B hj hK hR hn hn' hnB hn'B
  rw [← abs_natCast_sub_eq_natDist_cast] at hdD
  have hratio : |(n' : ℝ) - n| / R ≤ D / R :=
    div_le_div_of_nonneg_right hdD hR.le
  have hmajorant : 0 ≤ |N| / (K * R) +
      (j : ℝ) * (B / R) ^ (j - 1) * (|M| / (K * R) ^ j) := by
    have hB0 : 0 ≤ B := (Nat.cast_nonneg n).trans hnB
    have hBR : 0 ≤ B / R := by positivity
    positivity
  have huniform : reciprocalPhaseScale
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j K ≤
      D / R * (|N| / (K * R) +
        (j : ℝ) * (B / R) ^ (j - 1) * (|M| / (K * R) ^ j)) :=
    hscale.trans (mul_le_mul_of_nonneg_right hratio hmajorant)
  apply div_le_div_of_nonneg_right _ (pow_nonneg hK.le 5)
  simpa only [typeIICorrelationLinearParameter,
    typeIICorrelationHigherParameter] using huniform

/-- Pair-independent high-scale error attached to a literal short block.
The support lower bound is its left endpoint `1 + kq`, and its diameter is
bounded by `q`. -/
def typeIIShortIntervalScaleError
    (N M K B : ℝ) (j q k : ℕ) : ℝ :=
  ((q : ℝ) / ((1 + k * q : ℕ) : ℝ) *
      (|N| / (K * ((1 + k * q : ℕ) : ℝ)) +
        (j : ℝ) * (B / ((1 + k * q : ℕ) : ℝ)) ^ (j - 1) *
          (|M| / (K * ((1 + k * q : ℕ) : ℝ)) ^ j))) /
    K ^ 5

/-- Pair-independent high-scale error for a short block with arbitrary
positive initial endpoint `S₀`. -/
def typeIIShortIntervalScaleErrorAt
    (N M K B : ℝ) (j S₀ q k : ℕ) : ℝ :=
  ((q : ℝ) / ((S₀ + k * q : ℕ) : ℝ) *
      (|N| / (K * ((S₀ + k * q : ℕ) : ℝ)) +
        (j : ℝ) * (B / ((S₀ + k * q : ℕ) : ℝ)) ^ (j - 1) *
          (|M| / (K * ((S₀ + k * q : ℕ) : ℝ)) ^ j))) /
    K ^ 5

/-- Uniform transformed-scale estimate for two indices in a short block with
an arbitrary positive initial endpoint. -/
theorem reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortIntervalAt
    (N M K B : ℝ) {j S₀ S₁ q k n n' : ℕ} (hj : 1 ≤ j)
    (hK : 0 < K) (hS₀ : 0 < S₀) (hq : 0 < q)
    (hS₁ : (S₁ : ℝ) ≤ B)
    (hn : n ∈ shortIntervalBlock S₀ S₁ q k)
    (hn' : n' ∈ shortIntervalBlock S₀ S₁ q k) :
    reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M j n n') j K / K ^ 5 ≤
      typeIIShortIntervalScaleErrorAt N M K B j S₀ q k := by
  have hnData := mem_shortIntervalBlock.mp hn
  have hn'Data := mem_shortIntervalBlock.mp hn'
  have hdist : (Nat.dist n' n : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_lt
      (natDist_lt_of_mem_same_shortIntervalBlock hq hn' hn)
  have hnLower : S₀ + k * q ≤ n := by
    rw [shortIntervalBlock_eq_Ico hq] at hn
    exact (Finset.mem_Ico.mp hn).1
  have hn'Lower : S₀ + k * q ≤ n' := by
    rw [shortIntervalBlock_eq_Ico hq] at hn'
    exact (Finset.mem_Ico.mp hn').1
  have hnUpper : n ≤ S₁ := by omega
  have hn'Upper : n' ≤ S₁ := by omega
  have hnUpperReal : (n : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hnUpper
  have hn'UpperReal : (n' : ℝ) ≤ (S₁ : ℝ) := by exact_mod_cast hn'Upper
  apply reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_productScale_of_dist
    N M K (((S₀ + k * q : ℕ) : ℝ)) B (q : ℝ) hj hK
  · have hleft : 0 < S₀ + k * q := by omega
    exact_mod_cast hleft
  · exact_mod_cast hnLower
  · exact_mod_cast hn'Lower
  · exact hnUpperReal.trans hS₁
  · exact hn'UpperReal.trans hS₁
  · exact hdist

/-- In the quadratic equal-parameter case, dyadic support collapses the
short-block scale error to the explicit monomial `5q|N|/(K^6 R^2)`, where
`R = S₀ + kq` is the inner block's left endpoint. -/
theorem typeIIShortIntervalScaleErrorAt_quadratic_le_monomial
    (N K B : ℝ) {S₀ q k : ℕ}
    (hK : 1 ≤ K) (hS₀ : 0 < S₀) (hB0 : 0 ≤ B)
    (hB : B ≤ 2 * (((S₀ + k * q : ℕ) : ℝ))) :
    typeIIShortIntervalScaleErrorAt N N K B 2 S₀ q k ≤
      5 * (q : ℝ) * |N| /
        (K ^ 6 * (((S₀ + k * q : ℕ) : ℝ)) ^ 2) := by
  let R : ℝ := ((S₀ + k * q : ℕ) : ℝ)
  have hR : 1 ≤ R := by
    unfold R
    exact_mod_cast Nat.succ_le_iff.mpr (by omega : 0 < S₀ + k * q)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hKR : 1 ≤ K * R := by nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hR)]
  have hKRpos : 0 < K * R := zero_lt_one.trans_le hKR
  have hKRpow : K * R ≤ (K * R) ^ 2 := le_self_pow₀ hKR (by norm_num)
  have hpower : |N| / (K * R) ^ 2 ≤ |N| / (K * R) :=
    div_le_div_of_nonneg_left (abs_nonneg N) hKRpos hKRpow
  have hBR : B / R ≤ 2 := by
    apply (div_le_iff₀ hRpos).2
    simpa only [R] using hB
  have hBR0 : 0 ≤ B / R := by
    positivity
  have hsecond : 2 * (B / R) * (|N| / (K * R) ^ 2) ≤
      4 * (|N| / (K * R)) := by
    calc
      2 * (B / R) * (|N| / (K * R) ^ 2) ≤
          2 * 2 * (|N| / (K * R)) := by gcongr
      _ = 4 * (|N| / (K * R)) := by ring
  have hsum : |N| / (K * R) +
      2 * (B / R) * (|N| / (K * R) ^ 2) ≤
        5 * (|N| / (K * R)) := by linarith
  have hqR0 : 0 ≤ (q : ℝ) / R := by positivity
  calc
    typeIIShortIntervalScaleErrorAt N N K B 2 S₀ q k =
        ((q : ℝ) / R * (|N| / (K * R) +
          2 * (B / R) * (|N| / (K * R) ^ 2))) / K ^ 5 := by
      norm_num only [typeIIShortIntervalScaleErrorAt, R, Nat.reduceSubDiff,
        pow_one, Nat.cast_ofNat]
    _ ≤ ((q : ℝ) / R * (5 * (|N| / (K * R)))) / K ^ 5 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum hqR0) (pow_nonneg hKpos.le 5)
    _ = 5 * (q : ℝ) * |N| / (K ^ 6 * R ^ 2) := by field_simp
    _ = 5 * (q : ℝ) * |N| /
        (K ^ 6 * (((S₀ + k * q : ℕ) : ℝ)) ^ 2) := by rfl

/-- A single polynomial-scale inequality suffices for the low-scale condition
`typeIIShortIntervalScaleErrorAt ≤ 1/K`. -/
theorem typeIIShortIntervalScaleErrorAt_quadratic_le_one_div
    (N K B : ℝ) {S₀ q k : ℕ}
    (hK : 1 ≤ K) (hS₀ : 0 < S₀) (hB0 : 0 ≤ B)
    (hB : B ≤ 2 * (((S₀ + k * q : ℕ) : ℝ)))
    (hsize : 5 * (q : ℝ) * |N| ≤
      K ^ 5 * (((S₀ + k * q : ℕ) : ℝ)) ^ 2) :
    typeIIShortIntervalScaleErrorAt N N K B 2 S₀ q k ≤ 1 / K := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine (typeIIShortIntervalScaleErrorAt_quadratic_le_monomial
    N K B hK hS₀ hB0 hB).trans ?_
  rw [div_le_div_iff₀ (mul_pos (pow_pos hKpos 6)
    (pow_pos (by positivity) 2)) hKpos]
  have hcalc : 5 * (q : ℝ) * |N| * K ≤
        (K ^ 5 * (((S₀ + k * q : ℕ) : ℝ)) ^ 2) * K :=
    mul_le_mul_of_nonneg_right hsize hKpos.le
  calc
    5 * (q : ℝ) * |N| * K ≤
        (K ^ 5 * (((S₀ + k * q : ℕ) : ℝ)) ^ 2) * K := hcalc
    _ = 1 * (K ^ 6 * (((S₀ + k * q : ℕ) : ℝ)) ^ 2) := by ring

/-- Source-scale form of the quadratic low-frequency condition.  The global
phase scale controls `|N|`, so `10qF ≤ K⁴R` implies the canonical block error
bound `E ≤ 1/K`. -/
theorem typeIIShortIntervalScaleErrorAt_quadratic_le_one_div_of_sourceScale
    (N K B : ℝ) {S₀ q k : ℕ}
    (hK : 1 ≤ K) (hS₀ : 0 < S₀) (hB : 0 < B)
    (hBupper : B ≤ 2 * (((S₀ + k * q : ℕ) : ℝ)))
    (hsource : 10 * (q : ℝ) * reciprocalPhaseScale N N 2 (K * B) ≤
      K ^ 4 * (((S₀ + k * q : ℕ) : ℝ))) :
    typeIIShortIntervalScaleErrorAt N N K B 2 S₀ q k ≤ 1 / K := by
  let R : ℝ := ((S₀ + k * q : ℕ) : ℝ)
  let F := reciprocalPhaseScale N N 2 (K * B)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hRpos : 0 < R := by
    unfold R
    exact_mod_cast (by omega : 0 < S₀ + k * q)
  have hKBpos : 0 < K * B := mul_pos hKpos hB
  have hN : |N| ≤ F * (K * B) := by
    simpa only [F] using
      (abs_le_reciprocalPhaseScale_mul_scale N N 2 hKBpos)
  have hF0 : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
  have hN' : |N| ≤ 2 * F * K * R := by
    calc
      |N| ≤ F * (K * B) := hN
      _ ≤ F * (K * (2 * R)) := by gcongr
      _ = 2 * F * K * R := by ring
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hleft : 5 * (q : ℝ) * |N| ≤ 10 * (q : ℝ) * F * K * R := by
    have h5q0 : 0 ≤ 5 * (q : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hN' h5q0
    nlinarith
  have hsourceK := mul_le_mul_of_nonneg_right hsource hKpos.le
  have hsourceKR := mul_le_mul_of_nonneg_right hsourceK hRpos.le
  have hsize : 5 * (q : ℝ) * |N| ≤ K ^ 5 * R ^ 2 := by
    calc
      5 * (q : ℝ) * |N| ≤ 10 * (q : ℝ) * F * K * R := hleft
      _ ≤ (K ^ 4 * R) * K * R := by
        simpa only [F, R, mul_assoc] using hsourceKR
      _ = K ^ 5 * R ^ 2 := by ring
  apply typeIIShortIntervalScaleErrorAt_quadratic_le_one_div
    N K B hK hS₀ hB.le hBupper
  simpa only [R] using hsize

/-- Uniform transformed-scale estimate for two indices in one literal short
block.  Its explicit error scale uses the block left endpoint and length, so
no pair-dependent upper-bound premise remains. -/
theorem reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_shortInterval
    (N M K B : ℝ) {j Binner q k n n' : ℕ} (hj : 1 ≤ j)
    (hK : 0 < K) (hq : 0 < q)
    (hBinner : (Binner : ℝ) ≤ B)
    (hn : n ∈ shortIntervalBlock 1 (Binner + 1) q k)
    (hn' : n' ∈ shortIntervalBlock 1 (Binner + 1) q k) :
    reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M j n n') j K / K ^ 5 ≤
      typeIIShortIntervalScaleError N M K B j q k := by
  have hnData := mem_shortIntervalBlock.mp hn
  have hn'Data := mem_shortIntervalBlock.mp hn'
  have hdist : (Nat.dist n' n : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.le_of_lt
      (natDist_lt_of_mem_same_shortIntervalBlock hq hn' hn)
  have hnLower : 1 + k * q ≤ n := by
    rw [shortIntervalBlock_eq_Ico hq] at hn
    exact (Finset.mem_Ico.mp hn).1
  have hn'Lower : 1 + k * q ≤ n' := by
    rw [shortIntervalBlock_eq_Ico hq] at hn'
    exact (Finset.mem_Ico.mp hn').1
  have hnUpper : n ≤ Binner := by omega
  have hn'Upper : n' ≤ Binner := by omega
  have hnUpperReal : (n : ℝ) ≤ (Binner : ℝ) := by exact_mod_cast hnUpper
  have hn'UpperReal : (n' : ℝ) ≤ (Binner : ℝ) := by exact_mod_cast hn'Upper
  apply reciprocalPhaseScale_typeIICorrelation_div_pow_five_le_productScale_of_dist
    N M K (((1 + k * q : ℕ) : ℝ)) B (q : ℝ) hj hK
  · positivity
  · exact_mod_cast hnLower
  · exact_mod_cast hn'Lower
  · exact hnUpperReal.trans hBinner
  · exact hn'UpperReal.trans hBinner
  · exact hdist

/-- Dyadic-support specialization of the transformed phase-scale comparison.
For `n,n' ∈ [R,2R]`, the higher-power loss is explicitly
`j·2^(j-1)`, exactly the logarithmic-size factor absorbed in the source. -/
theorem reciprocalPhaseScale_typeIICorrelation_le_dyadic
    (N M K R : ℝ) {j n n' : ℕ} (hj : 1 ≤ j)
    (hK : 0 < K) (hR : 0 < R)
    (hn : R ≤ (n : ℝ)) (hn' : R ≤ (n' : ℝ))
    (hn2 : (n : ℝ) ≤ 2 * R) (hn'2 : (n' : ℝ) ≤ 2 * R) :
    reciprocalPhaseScale
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j K ≤
      |(n' : ℝ) - n| / R *
        (|N| / (K * R) +
          (j : ℝ) * 2 ^ (j - 1) * (|M| / (K * R) ^ j)) := by
  have hratio : (2 * R) / R = (2 : ℝ) := by field_simp
  simpa only [hratio] using
    (reciprocalPhaseScale_typeIICorrelation_le_productScale
      N M K R (2 * R) hj hK hR hn hn' hn2 hn'2)

/-- The off-diagonal portion of the source's Type II correlation sum. -/
def typeIIOffDiagonalSum (K S : Finset ℕ) (γ : ℕ → ℂ)
    (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ S, ∑ n' ∈ S.erase n,
    γ n * conj (γ n') * typeIICorrelationSum K N M j n n'

/-- Exact diagonal/off-diagonal split after the Type II Cauchy expansion. -/
theorem typeIICorrelationSum_split_diagonal
    (K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) :
    ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n' =
      (K.card : ℂ) * ∑ n ∈ S, γ n * conj (γ n) +
        typeIIOffDiagonalSum K S γ N M j := by
  calc
    ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n' =
      ∑ n ∈ S,
        (γ n * conj (γ n) * typeIICorrelationSum K N M j n n +
          ∑ n' ∈ S.erase n,
            γ n * conj (γ n') * typeIICorrelationSum K N M j n n') := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hn]
      rw [Finset.sdiff_singleton_eq_erase]
    _ = (∑ n ∈ S,
          γ n * conj (γ n) * typeIICorrelationSum K N M j n n) +
        typeIIOffDiagonalSum K S γ N M j := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = (K.card : ℂ) * ∑ n ∈ S, γ n * conj (γ n) +
        typeIIOffDiagonalSum K S γ N M j := by
      congr 1
      simp_rw [typeIICorrelationSum_self]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring

/-- Coefficient-explicit triangle bound for the off-diagonal Type II
correlations.  All remaining cancellation is isolated in the norms of the
source sums `X_{n,n'}`. -/
theorem norm_typeIIOffDiagonalSum_le
    (K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ‖typeIIOffDiagonalSum K S γ N M j‖ ≤
      L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIICorrelationSum K N M j n n'‖ := by
  unfold typeIIOffDiagonalSum
  calc
    ‖∑ n ∈ S, ∑ n' ∈ S.erase n,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n'‖ ≤
      ∑ n ∈ S, ‖∑ n' ∈ S.erase n,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n'‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖γ n * conj (γ n') * typeIICorrelationSum K N M j n n'‖ := by
      apply Finset.sum_le_sum
      intro n _hn
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ∑ n' ∈ S.erase n,
        L ^ 2 * ‖typeIICorrelationSum K N M j n n'‖ := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro n' hn'
      rw [norm_mul, norm_mul, norm_conj]
      have hn'S : n' ∈ S := Finset.mem_of_mem_erase hn'
      have hprod : ‖γ n‖ * ‖γ n'‖ ≤ L ^ 2 := by
        nlinarith [norm_nonneg (γ n), norm_nonneg (γ n'), hγ n hn, hγ n' hn'S]
      exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIICorrelationSum K N M j n n'‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]

/-- The diagonal Type II contribution has the expected trivial size
`#K * #S * L²`. -/
theorem norm_typeIIDiagonal_le
    (K S : Finset ℕ) (γ : ℕ → ℂ) {L : ℝ}
    (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ‖(K.card : ℂ) * ∑ n ∈ S, γ n * conj (γ n)‖ ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 := by
  calc
    ‖(K.card : ℂ) * ∑ n ∈ S, γ n * conj (γ n)‖ =
        (K.card : ℝ) * ‖∑ n ∈ S, γ n * conj (γ n)‖ := by
      rw [norm_mul]
      simp
    _ ≤ (K.card : ℝ) * ∑ n ∈ S, ‖γ n * conj (γ n)‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (Nat.cast_nonneg K.card)
    _ = (K.card : ℝ) * ∑ n ∈ S, ‖γ n‖ ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      rw [norm_mul, norm_conj, pow_two]
    _ ≤ (K.card : ℝ) * ∑ _n ∈ S, L ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg K.card)
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hγ n hn) 2
    _ = (K.card : ℝ) * (S.card : ℝ) * L ^ 2 := by
      simp
      ring

/-- Complete norm reduction for the Type II correlation expression: the
diagonal is explicit and every unresolved analytic input is an off-diagonal
`X_{n,n'}` norm. -/
theorem norm_typeIICorrelationExpression_le
    (K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ‖∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n'‖ ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
          ‖typeIICorrelationSum K N M j n n'‖ := by
  rw [typeIICorrelationSum_split_diagonal]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_typeIIDiagonal_le K S γ hγ)
      (norm_typeIIOffDiagonalSum_le K S γ N M j hL hγ))

/-- A uniform off-diagonal correlation bound sums over exactly at most
`#S (#S-1)` ordered pairs. -/
theorem sum_norm_typeIICorrelationSum_offDiagonal_le
    (K S : Finset ℕ) (N M : ℝ) (j : ℕ) {C : ℝ}
    (hC : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIICorrelationSum K N M j n n'‖ ≤ C) :
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIICorrelationSum K N M j n n'‖ ≤
      (S.card : ℝ) * (S.card - 1 : ℕ) * C := by
  calc
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIICorrelationSum K N M j n n'‖ ≤
      ∑ n ∈ S, ∑ _n' ∈ S.erase n, C := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro n' hn'
      have hn'Data := Finset.mem_erase.mp hn'
      exact hC n hn n' hn'Data.2 hn'Data.1.symm
    _ = ∑ _n ∈ S, ((S.card - 1 : ℕ) : ℝ) * C := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_const, Finset.card_erase_of_mem hn, nsmul_eq_mul]
    _ = (S.card : ℝ) * (S.card - 1 : ℕ) * C := by
      simp
      ring

/-- Type II reduction under one uniform off-diagonal estimate.  This is the
finite inequality immediately preceding the analytic estimate for
`X_{n,n'}` in the source. -/
theorem norm_typeIICorrelationExpression_le_of_uniform
    (K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L C : ℝ}
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L)
    (hC : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIICorrelationSum K N M j n n'‖ ≤ C) :
    ‖∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n'‖ ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) * (S.card - 1 : ℕ) * C) := by
  exact (norm_typeIICorrelationExpression_le K S γ N M j hL hγ).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (sum_norm_typeIICorrelationSum_offDiagonal_le K S N M j hC)
      (sq_nonneg L)))

/-- Summing the squared Type II inner sums and interchanging the three finite
sums gives the exact coefficient-correlation expression used in the source. -/
theorem sum_typeIIInnerSum_norm_sq
    (K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ)
    (hK : ∀ m ∈ K, m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0) :
    ∑ m ∈ K, ((‖typeIIInnerSum S γ N M j m‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') * typeIICorrelationSum K N M j n n' := by
  calc
    (∑ m ∈ K, ((‖typeIIInnerSum S γ N M j m‖ ^ 2 : ℝ) : ℂ)) =
        ∑ m ∈ K, ∑ n ∈ S, ∑ n' ∈ S,
          γ n * conj (γ n') *
            standardAdditiveCharacter
              (reciprocalPhase
                (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
                (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                  ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact typeIIInnerSum_norm_sq S γ N M j (hK m hm) hS
    _ = ∑ n ∈ S, ∑ m ∈ K, ∑ n' ∈ S,
          γ n * conj (γ n') *
            standardAdditiveCharacter
              (reciprocalPhase
                (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
                (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                  ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ S, ∑ n' ∈ S, ∑ m ∈ K,
          γ n * conj (γ n') *
            standardAdditiveCharacter
              (reciprocalPhase
                (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
                (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                  ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [typeIICorrelationSum, Finset.mul_sum]

/-- The actual Type II inner sum in the pinned source: besides the short
support `S` of `γ`, it retains exactly those `n` for which the product `m n`
lies in the prime-sum interval `I`. -/
def typeIIProductRestrictedInnerSum (I S : Finset ℕ) (γ : ℕ → ℂ)
    (N M : ℝ) (j m : ℕ) : ℂ :=
  typeIIInnerSum S (fun n => if m * n ∈ I then γ n else 0) N M j m

/-- The source's exact product-restricted correlation support
`K ∩ (1/n)I ∩ (1/n')I`. -/
def typeIIProductRestrictedCorrelationSum (I K : Finset ℕ) (N M : ℝ)
    (j n n' : ℕ) : ℂ :=
  ∑ m ∈ K.filter (fun m => m * n ∈ I ∧ m * n' ∈ I),
    standardAdditiveCharacter
      (reciprocalPhase
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m)

/-- Exact lower endpoint of the source's intersection
`[K₀,K₁) ∩ (1/n)[a,b) ∩ (1/n')[a,b)` when the outer support is
the `k`-th quotient block. -/
def typeIIProductRestrictedBlockLower
    (a K₀ q k n n' : ℕ) : ℕ :=
  max (K₀ + k * q) (max (a ⌈/⌉ n) (a ⌈/⌉ n'))

/-- Exact upper endpoint of the same three-interval intersection. -/
def typeIIProductRestrictedBlockUpper
    (b K₀ K₁ q k n n' : ℕ) : ℕ :=
  min (min K₁ (K₀ + (k + 1) * q))
    (min (b ⌈/⌉ n) (b ⌈/⌉ n'))

/-- The filtered support appearing in `X_{n,n'}` is literally one half-open
natural interval, with all integer endpoint rounding made explicit. -/
theorem typeIIProductRestrictedBlock_filter_eq_Ico
    {a b K₀ K₁ q k n n' : ℕ} (hq : 0 < q)
    (hn : 0 < n) (hn' : 0 < n') :
    (shortIntervalBlock K₀ K₁ q k).filter
        (fun m => m * n ∈ Finset.Ico a b ∧ m * n' ∈ Finset.Ico a b) =
      Finset.Ico (typeIIProductRestrictedBlockLower a K₀ q k n n')
        (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n') := by
  rw [shortIntervalBlock_eq_Ico hq]
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico,
    mul_mem_Ico_iff_mem_Ico_ceilDiv hn,
    mul_mem_Ico_iff_mem_Ico_ceilDiv hn',
    typeIIProductRestrictedBlockLower,
    typeIIProductRestrictedBlockUpper, max_le_iff, lt_min_iff]
  aesop

/-- Intersecting with the two product restrictions cannot enlarge the outer
quotient block: the resulting interval has natural length at most `q`. -/
theorem typeIIProductRestrictedBlock_length_le
    (a b K₀ K₁ q k n n' : ℕ) :
    typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
        typeIIProductRestrictedBlockLower a K₀ q k n n' ≤ q := by
  have hlower : K₀ + k * q ≤
      typeIIProductRestrictedBlockLower a K₀ q k n n' :=
    le_max_left _ _
  have hupper :
      typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' ≤
        K₀ + (k + 1) * q := by
    exact (min_le_left _ _).trans (min_le_right _ _)
  rw [Nat.add_mul] at hupper
  simp only [one_mul] at hupper
  omega

/-- Consequently the source's product-restricted correlation `X_{n,n'}` is
exactly a reciprocal-phase sum over one explicit interval.  This is the
direct input shape required by the integer Vinogradov/Weyl proposition. -/
theorem typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) (j : ℕ) {n n' : ℕ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') :
    typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n' =
      reciprocalPhaseSum
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j
        (typeIIProductRestrictedBlockLower a K₀ q k n n')
        (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n') := by
  unfold typeIIProductRestrictedCorrelationSum reciprocalPhaseSum
  rw [typeIIProductRestrictedBlock_filter_eq_Ico hq hn hn']

/-- Specialization to the actual named dyadic block used by the canonical
Vaughan family. -/
theorem typeIIProductRestrictedCorrelationSum_dyadicBlock_eq
    (a b L : ℕ) (N M : ℝ) (j : ℕ) {sk : ℕ × ℕ} {n n' : ℕ}
    (hL : 0 < L) (hn : 0 < n) (hn' : 0 < n') :
    typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (dyadicShortIntervalIndexedBlock L sk) N M j n n' =
      reciprocalPhaseSum
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j
        (typeIIProductRestrictedBlockLower a (2 ^ sk.1)
          (dyadicShortIntervalLength (2 ^ sk.1) L) sk.2 n n')
        (typeIIProductRestrictedBlockUpper b (2 ^ sk.1) (2 * 2 ^ sk.1)
          (dyadicShortIntervalLength (2 ^ sk.1) L) sk.2 n n') := by
  unfold dyadicShortIntervalIndexedBlock
  exact typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b (2 ^ sk.1) (2 * 2 ^ sk.1)
      (dyadicShortIntervalLength (2 ^ sk.1) L) sk.2 N M j
      (dyadicShortIntervalLength_pos (pow_pos (by omega) sk.1) hL) hn hn'

/-- The same exact interval rewrite for a canonical Vaughan outer block. -/
theorem typeIIProductRestrictedCorrelationSum_vaughanBlock_eq
    (a b B : ℕ) (N M : ℝ) (j : ℕ) {sk : ℕ × ℕ} {n n' : ℕ}
    (hn : 0 < n) (hn' : 0 < n') :
    typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget B) sk)
        N M j n n' =
      reciprocalPhaseSum
        (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
        (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
          ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j
        (typeIIProductRestrictedBlockLower a (2 ^ sk.1)
          (dyadicShortIntervalLength (2 ^ sk.1)
            (vaughanShortIntervalBudget B)) sk.2 n n')
        (typeIIProductRestrictedBlockUpper b (2 ^ sk.1) (2 * 2 ^ sk.1)
          (dyadicShortIntervalLength (2 ^ sk.1)
            (vaughanShortIntervalBudget B)) sk.2 n n') := by
  exact typeIIProductRestrictedCorrelationSum_dyadicBlock_eq
    a b (vaughanShortIntervalBudget B) N M j
      (vaughanShortIntervalBudget_pos B) hn hn'

/-- On the diagonal, the exact product-restricted correlation is the number
of outer variables whose product lies in `I`. -/
theorem typeIIProductRestrictedCorrelationSum_self
    (I K : Finset ℕ) (N M : ℝ) (j n : ℕ) :
    typeIIProductRestrictedCorrelationSum I K N M j n n =
      ((K.filter (fun m => m * n ∈ I)).card : ℂ) := by
  unfold typeIIProductRestrictedCorrelationSum
  simp [reciprocalPhase, standardAdditiveCharacter]

/-- The restricted diagonal correlation is bounded by the ambient outer
support cardinality. -/
theorem norm_typeIIProductRestrictedCorrelationSum_self_le
    (I K : Finset ℕ) (N M : ℝ) (j n : ℕ) :
    ‖typeIIProductRestrictedCorrelationSum I K N M j n n‖ ≤ (K.card : ℝ) := by
  rw [typeIIProductRestrictedCorrelationSum_self]
  simp only [Complex.norm_natCast]
  exact_mod_cast Finset.card_filter_le K (fun m => m * n ∈ I)

/-- Off-diagonal part of the literal product-restricted Type II correlation
expression. -/
def typeIIProductRestrictedOffDiagonalSum
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ S, ∑ n' ∈ S.erase n,
    γ n * conj (γ n') *
      typeIIProductRestrictedCorrelationSum I K N M j n n'

/-- Exact diagonal/off-diagonal split with the source's product restriction
retained. -/
theorem typeIIProductRestrictedCorrelationSum_split_diagonal
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) :
    ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n' =
      ∑ n ∈ S, γ n * conj (γ n) *
          ((K.filter (fun m => m * n ∈ I)).card : ℂ) +
        typeIIProductRestrictedOffDiagonalSum I K S γ N M j := by
  calc
    ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n' =
      ∑ n ∈ S,
        (γ n * conj (γ n) *
            typeIIProductRestrictedCorrelationSum I K N M j n n +
          ∑ n' ∈ S.erase n,
            γ n * conj (γ n') *
              typeIIProductRestrictedCorrelationSum I K N M j n n') := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hn]
      rw [Finset.sdiff_singleton_eq_erase]
    _ = (∑ n ∈ S, γ n * conj (γ n) *
            typeIIProductRestrictedCorrelationSum I K N M j n n) +
        typeIIProductRestrictedOffDiagonalSum I K S γ N M j := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro n _hn
      rw [typeIIProductRestrictedCorrelationSum_self]

/-- Coefficient-explicit triangle bound for the product-restricted
off-diagonal correlations. -/
theorem norm_typeIIProductRestrictedOffDiagonalSum_le
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ‖typeIIProductRestrictedOffDiagonalSum I K S γ N M j‖ ≤
      L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ := by
  unfold typeIIProductRestrictedOffDiagonalSum
  calc
    ‖∑ n ∈ S, ∑ n' ∈ S.erase n,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      ∑ n ∈ S, ‖∑ n' ∈ S.erase n,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ := by
      apply Finset.sum_le_sum
      intro n _hn
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ∑ n' ∈ S.erase n,
        L ^ 2 *
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro n' hn'
      rw [norm_mul, norm_mul, norm_conj]
      have hn'S : n' ∈ S := Finset.mem_of_mem_erase hn'
      have hprod : ‖γ n‖ * ‖γ n'‖ ≤ L ^ 2 := by
        nlinarith [norm_nonneg (γ n), norm_nonneg (γ n'),
          hγ n hn, hγ n' hn'S]
      exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.mul_sum]

/-- The literal restricted diagonal has the same ambient
`#K·#S·L²` bound as the simplified fixed-support model. -/
theorem norm_typeIIProductRestrictedDiagonal_le
    (I K S : Finset ℕ) (γ : ℕ → ℂ) {L : ℝ}
    (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ‖∑ n ∈ S, γ n * conj (γ n) *
        ((K.filter (fun m => m * n ∈ I)).card : ℂ)‖ ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 := by
  calc
    ‖∑ n ∈ S, γ n * conj (γ n) *
        ((K.filter (fun m => m * n ∈ I)).card : ℂ)‖ ≤
      ∑ n ∈ S, ‖γ n * conj (γ n) *
        ((K.filter (fun m => m * n ∈ I)).card : ℂ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ S, ‖γ n‖ ^ 2 *
        ((K.filter (fun m => m * n ∈ I)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [norm_mul, norm_mul, norm_conj, Complex.norm_natCast, pow_two]
    _ ≤ ∑ _n ∈ S, L ^ 2 * (K.card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul
      · exact pow_le_pow_left₀ (norm_nonneg _) (hγ n hn) 2
      · exact_mod_cast Finset.card_filter_le K (fun m => m * n ∈ I)
      · exact_mod_cast Nat.zero_le (K.filter (fun m => m * n ∈ I)).card
      · exact sq_nonneg L
    _ = (K.card : ℝ) * (S.card : ℝ) * L ^ 2 := by
      simp
      ring

/-- Complete norm reduction for the literal product-restricted Type II
correlation expression. -/
theorem norm_typeIIProductRestrictedCorrelationExpression_le
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ‖∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ := by
  rw [typeIIProductRestrictedCorrelationSum_split_diagonal]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_typeIIProductRestrictedDiagonal_le I K S γ hγ)
      (norm_typeIIProductRestrictedOffDiagonalSum_le
        I K S γ N M j hL hγ))

/-- A uniform estimate for the literal restricted off-diagonal correlations
propagates over at most `#S(#S-1)` ordered pairs. -/
theorem sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le
    (I K S : Finset ℕ) (N M : ℝ) (j : ℕ) {C : ℝ}
    (hC : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤ C) :
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      (S.card : ℝ) * (S.card - 1 : ℕ) * C := by
  calc
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      ∑ n ∈ S, ∑ _n' ∈ S.erase n, C := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro n' hn'
      have hn'Data := Finset.mem_erase.mp hn'
      exact hC n hn n' hn'Data.2 hn'Data.1.symm
    _ = ∑ _n ∈ S, ((S.card - 1 : ℕ) : ℝ) * C := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_const, Finset.card_erase_of_mem hn, nsmul_eq_mul]
    _ = (S.card : ℝ) * (S.card - 1 : ℕ) * C := by
      simp
      ring

/-- Final finite Type II reduction for the literal product-restricted
correlations under one uniform off-diagonal estimate. -/
theorem norm_typeIIProductRestrictedCorrelationExpression_le_of_uniform
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L C : ℝ}
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L)
    (hC : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤ C) :
    ‖∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) * (S.card - 1 : ℕ) * C) := by
  exact (norm_typeIIProductRestrictedCorrelationExpression_le
    I K S γ N M j hL hγ).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le
          I K S N M j hC) (sq_nonneg L)))

/-- Exact Type II rearrangement with the product restriction retained.  This
is the literal finite form of the source's displayed correlation identity,
including the support `K ∩ (1/n)I ∩ (1/n')I`. -/
theorem sum_typeIIProductRestrictedInnerSum_norm_sq
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ)
    (hK : ∀ m ∈ K, m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0) :
    ∑ m ∈ K,
        ((‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n' := by
  calc
    ∑ m ∈ K,
        ((‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ K, ∑ n ∈ S, ∑ n' ∈ S,
        (if m * n ∈ I then γ n else 0) *
          conj (if m * n' ∈ I then γ n' else 0) *
          standardAdditiveCharacter
            (reciprocalPhase
              (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
              (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact typeIIInnerSum_norm_sq S
        (fun n => if m * n ∈ I then γ n else 0) N M j (hK m hm) hS
    _ = ∑ n ∈ S, ∑ n' ∈ S, ∑ m ∈ K,
        (if m * n ∈ I then γ n else 0) *
          conj (if m * n' ∈ I then γ n' else 0) *
          standardAdditiveCharacter
            (reciprocalPhase
              (N * ((n' : ℝ) - n) / ((n : ℝ) * n'))
              (M * ((n' : ℝ) ^ j - (n : ℝ) ^ j) /
                ((n : ℝ) ^ j * (n' : ℝ) ^ j)) j m) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro n' _hn'
      rw [typeIIProductRestrictedCorrelationSum, Finset.mul_sum]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hnI : m * n ∈ I
      · by_cases hn'I : m * n' ∈ I
        · simp [hnI, hn'I]
        · simp [hnI, hn'I]
      · simp [hnI]

/-- The exact product-restricted squared-inner-sum reduction before imposing
any uniform or distance-dependent analytic bound on the off-diagonal
correlations. -/
theorem sum_typeIIProductRestrictedInnerSum_norm_sq_le
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L : ℝ}
    (hK : ∀ m ∈ K, m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0)
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L) :
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ := by
  have hrearrange :=
    sum_typeIIProductRestrictedInnerSum_norm_sq I K S γ N M j hK hS
  have hre :
      ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
        (∑ n ∈ S, ∑ n' ∈ S,
          γ n * conj (γ n') *
            typeIIProductRestrictedCorrelationSum I K N M j n n').re := by
    calc
      ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
          ∑ m ∈ K,
            (((‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 : ℝ) : ℂ).re) := by
        apply Finset.sum_congr rfl
        intro m _hm
        change ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
          ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2
        rfl
      _ = (∑ m ∈ K,
            ((‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [Complex.re_sum]
      _ = _ := congrArg Complex.re hrearrange
  calc
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
        (∑ n ∈ S, ∑ n' ∈ S,
          γ n * conj (γ n') *
            typeIIProductRestrictedCorrelationSum I K N M j n n').re := hre
    _ ≤ ‖∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ :=
      Complex.re_le_norm _
    _ ≤ _ := norm_typeIIProductRestrictedCorrelationExpression_le
      I K S γ N M j hL hγ

/-- The real squared-inner-sum estimate delivered by the complete literal
Type II finite reduction.  The sole remaining input is the uniform analytic
bound `C` for restricted off-diagonal correlations. -/
theorem sum_typeIIProductRestrictedInnerSum_norm_sq_le_of_uniform
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j : ℕ) {L C : ℝ}
    (hK : ∀ m ∈ K, m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0)
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L)
    (hC : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤ C) :
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) * (S.card - 1 : ℕ) * C) := by
  have hrearrange :=
    sum_typeIIProductRestrictedInnerSum_norm_sq I K S γ N M j hK hS
  have hre :
      ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
        (∑ n ∈ S, ∑ n' ∈ S,
          γ n * conj (γ n') *
            typeIIProductRestrictedCorrelationSum I K N M j n n').re := by
    calc
      ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
          ∑ m ∈ K,
            (((‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 : ℝ) : ℂ).re) := by
        apply Finset.sum_congr rfl
        intro m _hm
        change ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
          ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2
        rfl
      _ = (∑ m ∈ K,
            ((‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 : ℝ) : ℂ)).re := by
        rw [Complex.re_sum]
      _ = _ := congrArg Complex.re hrearrange
  calc
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 =
        (∑ n ∈ S, ∑ n' ∈ S,
          γ n * conj (γ n') *
            typeIIProductRestrictedCorrelationSum I K N M j n n').re := hre
    _ ≤ ‖∑ n ∈ S, ∑ n' ∈ S,
        γ n * conj (γ n') *
          typeIIProductRestrictedCorrelationSum I K N M j n n'‖ :=
      Complex.re_le_norm _
    _ ≤ _ := norm_typeIIProductRestrictedCorrelationExpression_le_of_uniform
      I K S γ N M j hL hγ hC

end

end Tao2026
