import Tao2026.PhaseVariation
import PrimeNumberTheoremAnd.Consequences

/-!
# Low-frequency reduction to a prime-number-theorem discrepancy

The low-frequency branch of Proposition 1.12 in the pinned source applies
summation by parts to the slowly varying reciprocal-phase character.  This
module makes that reduction exact.  The remaining input is only a uniform
bound for initial partial sums of `Λ - 1`; no exponential-sum conclusion is
postulated.
-/

open Complex Finset Set Filter
open scoped ArithmeticFunction.vonMangoldt BigOperators Topology

namespace Tao2026

noncomputable section

/-- The complex embedding of the pointwise von-Mangoldt discrepancy
`Λ(n) - 1`. -/
def mangoldtDiscrepancyTerm (n : ℕ) : ℂ := (Λ n : ℂ) - 1

/-- The discrepancy on the half-open interval `[a,k)`. -/
def mangoldtDiscrepancyPartialSum (a k : ℕ) : ℂ :=
  intervalPartialSum mangoldtDiscrepancyTerm a k

/-- The global complex discrepancy is exactly the real PNT discrepancy
`∑_{n<k} Λ(n) - k`, embedded in `ℂ`. -/
theorem mangoldtDiscrepancyPartialSum_zero_eq (k : ℕ) :
    mangoldtDiscrepancyPartialSum 0 k =
      (((cumsum Λ k : ℝ) - k : ℝ) : ℂ) := by
  simp [mangoldtDiscrepancyPartialSum, intervalPartialSum,
    mangoldtDiscrepancyTerm, cumsum, Finset.sum_sub_distrib]

/-- The frozen qualitative prime number theorem, normalized as convergence
of the relative Mangoldt discrepancy to zero. -/
theorem tendsto_mangoldtRatio_sub_one : Tendsto
    (fun k : ℕ => (cumsum Λ k / (k : ℝ)) - 1)
    atTop (𝓝 0) := by
  simpa using WeakPNT.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- The normalized PNT discrepancy is eventually smaller than every positive
constant. -/
theorem eventually_norm_mangoldtRatio_sub_one_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ‖(cumsum Λ k / (k : ℝ)) - 1‖ < ε := by
  simpa [dist_eq_norm] using
    (Metric.tendsto_atTop.1 tendsto_mangoldtRatio_sub_one ε hε)

/-- A direct `o(k)` form of the frozen qualitative prime number theorem for
the exact discrepancy used by the Abel reduction. -/
theorem eventually_norm_mangoldtDiscrepancyPartialSum_zero_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ‖mangoldtDiscrepancyPartialSum 0 k‖ ≤ ε * k := by
  have hratio := eventually_norm_mangoldtRatio_sub_one_lt hε
  filter_upwards [hratio, eventually_ge_atTop (1 : ℕ)] with k hk hk1
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk1)
  have hrewrite : (cumsum Λ k : ℝ) - k =
      (k : ℝ) * (cumsum Λ k / (k : ℝ) - 1) := by
    field_simp
  rw [mangoldtDiscrepancyPartialSum_zero_eq, hrewrite]
  simp only [ofReal_mul, norm_mul, norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Nat.cast_nonneg k), mul_comm ε]
  simpa [Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_left hk.le (Nat.cast_nonneg k)

/-- An interval discrepancy is the difference of its two global prefix
discrepancies. -/
theorem mangoldtDiscrepancyPartialSum_eq_sub
    {a k : ℕ} (hak : a ≤ k) :
    mangoldtDiscrepancyPartialSum a k =
      mangoldtDiscrepancyPartialSum 0 k -
        mangoldtDiscrepancyPartialSum 0 a := by
  unfold mangoldtDiscrepancyPartialSum intervalPartialSum
  rw [Finset.sum_Ico_eq_sub _ hak]
  simp

/-- Uniform qualitative PNT discrepancy on every subinterval of a dyadic
block.  The factor four needed for the two prefix sums is absorbed by
applying the global estimate with `ε / 4`. -/
theorem eventually_uniform_mangoldtDiscrepancyPartialSum_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop, ∀ a k : ℕ,
      P ≤ a → a ≤ k → k ≤ 2 * P →
        ‖mangoldtDiscrepancyPartialSum a k‖ ≤ ε * P := by
  have hquarter : 0 < ε / 4 := div_pos hε (by norm_num)
  have hglobal :=
    eventually_norm_mangoldtDiscrepancyPartialSum_zero_le hquarter
  obtain ⟨K, hK⟩ := (eventually_atTop.1 hglobal)
  filter_upwards [eventually_ge_atTop K] with P hPK
  intro a k hPa hak hkP
  have haK : K ≤ a := hPK.trans hPa
  have hkK : K ≤ k := haK.trans hak
  rw [mangoldtDiscrepancyPartialSum_eq_sub hak]
  calc
    ‖mangoldtDiscrepancyPartialSum 0 k -
        mangoldtDiscrepancyPartialSum 0 a‖ ≤
        ‖mangoldtDiscrepancyPartialSum 0 k‖ +
          ‖mangoldtDiscrepancyPartialSum 0 a‖ := norm_sub_le _ _
    _ ≤ (ε / 4) * k + (ε / 4) * a := add_le_add (hK k hkK) (hK a haK)
    _ ≤ ε * P := by
      have hkP' : (k : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hkP
      have haP' : (a : ℝ) ≤ 2 * (P : ℝ) := by
        exact_mod_cast hak.trans hkP
      nlinarith

/-- The reciprocal-phase-weighted Mangoldt discrepancy on `[a,b)`. -/
def mangoldtDiscrepancyReciprocalPhaseSum
    (N M : ℝ) (j a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a b,
    standardAdditiveCharacter (reciprocalPhase N M j n) •
      mangoldtDiscrepancyTerm n

/-- The discrepancy sum is exactly the Mangoldt phase sum minus the
unweighted integer phase sum. -/
theorem mangoldtDiscrepancyReciprocalPhaseSum_eq_sub
    (N M : ℝ) (j a b : ℕ) :
    mangoldtDiscrepancyReciprocalPhaseSum N M j a b =
      mangoldtReciprocalPhaseSum N M j a b -
        reciprocalPhaseSum N M j a b := by
  unfold mangoldtDiscrepancyReciprocalPhaseSum mangoldtDiscrepancyTerm
    mangoldtReciprocalPhaseSum weightedRealArithmeticSum reciprocalPhaseSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  simp only [smul_eq_mul]
  ring

/-- Exact low-frequency Abel reduction.  A uniform bound `B` for initial
partial sums of `Λ - 1` is multiplied only by one endpoint contribution and
the explicitly bounded total variation of the reciprocal-phase character. -/
theorem norm_mangoldtDiscrepancyReciprocalPhaseSum_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    {a b : ℕ} (hab : a < b) (hXa : X ≤ a) (hbTop : b ≤ 2 * X)
    {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ B) :
    ‖mangoldtDiscrepancyReciprocalPhaseSum N M j a b‖ ≤
      B + ((Finset.Ico a (b - 1)).card : ℝ) *
        (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) * B := by
  let f : ℕ → ℂ := fun n =>
    standardAdditiveCharacter (reciprocalPhase N M j n)
  have habel := norm_sum_Ico_complex_smul_le_endpoint_add_variation
    f mangoldtDiscrepancyTerm hab (fun k hak hkb => by
      simpa [mangoldtDiscrepancyPartialSum] using hpartial k hak hkb)
  have hvariation :=
    sum_norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le
      N M hj hX hXa hbTop
  have hvariation' :
      ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ ≤
        ((Finset.Ico a (b - 1)).card : ℝ) *
          (2 * Real.pi *
            ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) := by
    simpa [f, Nat.cast_add, Nat.cast_one] using hvariation
  change ‖∑ n ∈ Finset.Ico a b, f n • mangoldtDiscrepancyTerm n‖ ≤ _
  calc
    ‖∑ n ∈ Finset.Ico a b, f n • mangoldtDiscrepancyTerm n‖ ≤
        B + ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ * B := by
      simpa [f, norm_standardAdditiveCharacter] using habel
    _ ≤ B + ((Finset.Ico a (b - 1)).card : ℝ) *
        (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) * B := by
      rw [← Finset.sum_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hvariation' hB)

/-- Dyadic source-scale form of the low-frequency Abel reduction.  The
entire character variation has now been absorbed into `2π(j+1)F`. -/
theorem norm_mangoldtDiscrepancyReciprocalPhaseSum_le_scale
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    {a b : ℕ} (hab : a < b) (hXa : X ≤ a) (hbTop : b ≤ 2 * X)
    {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ B) :
    ‖mangoldtDiscrepancyReciprocalPhaseSum N M j a b‖ ≤
      B + (2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X)) * B := by
  let f : ℕ → ℂ := fun n =>
    standardAdditiveCharacter (reciprocalPhase N M j n)
  have habel := norm_sum_Ico_complex_smul_le_endpoint_add_variation
    f mangoldtDiscrepancyTerm hab (fun k hak hkb => by
      simpa [mangoldtDiscrepancyPartialSum] using hpartial k hak hkb)
  have hvariation :=
    sum_norm_standardAdditiveCharacter_reciprocalPhase_succ_sub_le_scale
      N M hj hX hab hXa hbTop
  have hvariation' :
      ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ ≤
        2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j X) := by
    simpa [f, Nat.cast_add, Nat.cast_one] using hvariation
  change ‖∑ n ∈ Finset.Ico a b, f n • mangoldtDiscrepancyTerm n‖ ≤ _
  calc
    ‖∑ n ∈ Finset.Ico a b, f n • mangoldtDiscrepancyTerm n‖ ≤
        B + ∑ n ∈ Finset.Ico a (b - 1), ‖f (n + 1) - f n‖ * B := by
      simpa [f, norm_standardAdditiveCharacter] using habel
    _ ≤ B + (2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X)) * B := by
      rw [← Finset.sum_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hvariation' hB)

/-- Source-facing comparison between the Mangoldt and integer reciprocal
phase sums in the low-frequency regime. -/
theorem norm_mangoldtReciprocalPhaseSum_sub_reciprocalPhaseSum_le
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    {a b : ℕ} (hab : a < b) (hXa : X ≤ a) (hbTop : b ≤ 2 * X)
    {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ B) :
    ‖mangoldtReciprocalPhaseSum N M j a b -
        reciprocalPhaseSum N M j a b‖ ≤
      B + ((Finset.Ico a (b - 1)).card : ℝ) *
        (2 * Real.pi *
          ((j + 1 : ℕ) * reciprocalPhaseScale N M j X / X)) * B := by
  rw [← mangoldtDiscrepancyReciprocalPhaseSum_eq_sub]
  exact norm_mangoldtDiscrepancyReciprocalPhaseSum_le
    N M hj hX hab hXa hbTop hB hpartial

/-- Dyadic source-scale comparison between the Mangoldt and integer phase
sums. -/
theorem norm_mangoldtReciprocalPhaseSum_sub_reciprocalPhaseSum_le_scale
    (N M : ℝ) {j : ℕ} (hj : 1 ≤ j) {X : ℝ} (hX : 0 < X)
    {a b : ℕ} (hab : a < b) (hXa : X ≤ a) (hbTop : b ≤ 2 * X)
    {B : ℝ} (hB : 0 ≤ B)
    (hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ B) :
    ‖mangoldtReciprocalPhaseSum N M j a b -
        reciprocalPhaseSum N M j a b‖ ≤
      B + (2 * Real.pi *
        ((j + 1 : ℕ) * reciprocalPhaseScale N M j X)) * B := by
  rw [← mangoldtDiscrepancyReciprocalPhaseSum_eq_sub]
  exact norm_mangoldtDiscrepancyReciprocalPhaseSum_le_scale
    N M hj hX hab hXa hbTop hB hpartial

/-- Uniform bounded-frequency consequence of the frozen qualitative PNT.
For every fixed reciprocal-phase scale bound `F₀`, the Mangoldt-to-integer
phase-sum discrepancy is `o(P)`, uniformly over all subintervals of
`[P,2P)`.  Tao's source needs a stronger logarithmic saving when the scale is
allowed to grow polylogarithmically; that quantitative PNT input is not
asserted here. -/
theorem eventually_norm_mangoldtReciprocalPhaseSum_sub_le_of_scale_le
    {j : ℕ} (hj : 1 ≤ j) {F₀ ε : ℝ} (hF₀ : 0 ≤ F₀) (hε : 0 < ε) :
    ∀ᶠ P : ℕ in atTop, ∀ (N M : ℝ) (a b : ℕ),
      P ≤ a → a < b → b ≤ 2 * P →
      reciprocalPhaseScale N M j (P : ℝ) ≤ F₀ →
      ‖mangoldtReciprocalPhaseSum N M j a b -
          reciprocalPhaseSum N M j a b‖ ≤ ε * P := by
  let C : ℝ := 1 + 2 * Real.pi * ((j + 1 : ℕ) * F₀)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hδ : 0 < ε / C := div_pos hε hC
  have huniform :=
    eventually_uniform_mangoldtDiscrepancyPartialSum_le hδ
  filter_upwards [huniform, eventually_ge_atTop (1 : ℕ)] with P hP hP1
  intro N M a b hPa hab hbP hscale
  have hPreal : 0 < (P : ℝ) := by exact_mod_cast hP1
  have hPaReal : (P : ℝ) ≤ (a : ℝ) := by exact_mod_cast hPa
  have hbPReal : (b : ℝ) ≤ 2 * (P : ℝ) := by exact_mod_cast hbP
  have hB : 0 ≤ (ε / C) * (P : ℝ) :=
    mul_nonneg hδ.le (Nat.cast_nonneg P)
  have hpartial : ∀ k, a < k → k ≤ b →
      ‖mangoldtDiscrepancyPartialSum a k‖ ≤ (ε / C) * P := by
    intro k hak hkb
    exact hP a k hPa hak.le (hkb.trans hbP)
  calc
    ‖mangoldtReciprocalPhaseSum N M j a b -
        reciprocalPhaseSum N M j a b‖ ≤
        (ε / C) * P +
          (2 * Real.pi * ((j + 1 : ℕ) *
            reciprocalPhaseScale N M j (P : ℝ))) * ((ε / C) * P) :=
      norm_mangoldtReciprocalPhaseSum_sub_reciprocalPhaseSum_le_scale
        N M hj hPreal hab hPaReal hbPReal hB hpartial
    _ ≤ (ε / C) * P +
        (2 * Real.pi * ((j + 1 : ℕ) * F₀)) * ((ε / C) * P) := by
      gcongr
    _ = ε * P := by
      dsimp [C]
      field_simp

end

end Tao2026
