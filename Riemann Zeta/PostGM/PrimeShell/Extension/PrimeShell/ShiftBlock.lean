import PrimeShell.KernelLocalization
import PrimeShell.GMInterface

namespace PrimeShell

noncomputable section

open scoped BigOperators ArithmeticFunction
open Set MeasureTheory Real
open Zeta23 Zeta23.PrimeSide

/-- One row of the actual normalized correlation restricted to a shift block
`(J,K]`, with the ambient dyadic right endpoint retained. -/
def rowShiftBlockCorrelation (N n J K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc J K,
    if n + h ∈ Finset.Ioc N (2 * N) then dyadicLambdaWeight n h else 0

/-- The literal kernel-weighted version of `rowShiftBlockCorrelation`. -/
def rowShiftBlockSum
    (Phi : ℝ → ℝ) (T : ℝ) (N n J K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc J K,
    if n + h ∈ Finset.Ioc N (2 * N) then
      dyadicLambdaWeight n h * dyadicShiftKernel Phi T n h
    else 0

/-- The first positive shift in `(J,K]`, used as the literal block anchor. -/
def rowShiftBlockAnchor
    (Phi : ℝ → ℝ) (T : ℝ) (n J : ℕ) : ℝ :=
  dyadicShiftKernel Phi T n (J + 1)

/-- Exact error from freezing one literal kernel row on `(J,K]`. -/
def rowShiftBlockVariation
    (Phi : ℝ → ℝ) (T : ℝ) (N n J K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc J K,
    if n + h ∈ Finset.Ioc N (2 * N) then
      dyadicLambdaWeight n h *
        (dyadicShiftKernel Phi T n h - rowShiftBlockAnchor Phi T n J)
    else 0

/-- Exact anchored decomposition on one row and one shift block. -/
theorem rowShiftBlockSum_eq_anchor_add_variation
    (Phi : ℝ → ℝ) (T : ℝ) (N n J K : ℕ) :
    rowShiftBlockSum Phi T N n J K =
      rowShiftBlockAnchor Phi T n J * rowShiftBlockCorrelation N n J K +
        rowShiftBlockVariation Phi T N n J K := by
  unfold rowShiftBlockSum rowShiftBlockCorrelation rowShiftBlockVariation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true]
    ring
  · simp [hmem]

/-- The exact shift-coordinate oscillation budget at one row. -/
def rowShiftOscillationBudget
    (Phi : ℝ → ℝ) (T N : ℝ) (h j : ℕ) : ℝ :=
  3 * T ^ 2 * (|(h : ℝ) - j| / N) * (∫ x, Phi x ^ 2) +
    T * (|(h : ℝ) - j| / N) * (∫ x, Phi x ^ 2 * |x|) +
    12 * T * (|(h : ℝ) - j| / (h : ℝ)) * (∫ x, Phi x ^ 2)

/-- Full literal error ledger for one geometric (or arbitrary finite) shift
block.  It requires no scalar-prefix collapse and no unspecified weight. -/
theorem abs_rowShiftBlockVariation_le
    {Phi : ℝ → ℝ} {T : ℝ} {N n J K : ℕ}
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hn : n ∈ Finset.Ioc N (2 * N)) (hKN : K ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |rowShiftBlockVariation Phi T N n J K| ≤
      ∑ h ∈ Finset.Ioc J K,
        dyadicLambdaWeight n h *
          rowShiftOscillationBudget Phi T N h (J + 1) := by
  unfold rowShiftBlockVariation rowShiftOscillationBudget rowShiftBlockAnchor
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro h hhmem
  have hh := Finset.mem_Ioc.mp hhmem
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N)
  · simp only [hmem, if_true, abs_mul]
    have hw : 0 ≤ dyadicLambdaWeight n h := dyadicLambdaWeight_nonneg n h
    rw [abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left
      (abs_dyadicShiftKernel_sub_le_shiftBox hT hN hn (by omega)
        (hh.2.trans hKN) (by omega) hPhi hPhi2 hPhiAbs) hw
  · simp only [hmem, if_false, abs_zero]
    exact mul_nonneg (dyadicLambdaWeight_nonneg n h) (by
      have hI0 : 0 ≤ ∫ x, Phi x ^ 2 := integral_nonneg fun x => sq_nonneg _
      have hI1 : 0 ≤ ∫ x, Phi x ^ 2 * |x| :=
        integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
      positivity)

/-- The raw von-Mangoldt row block before the exact Zeta23 square-root
normalization is restored. -/
def rawRowShiftBlockCorrelation (N n J K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc J K,
    if n + h ∈ Finset.Ioc N (2 * N) then
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + h)
    else 0

/-- Exact relation between the normalized source row and the future
coefficient sum. -/
theorem rowShiftBlockCorrelation_eq_acoef_mul
    (N n J K : ℕ) :
    rowShiftBlockCorrelation N n J K =
      acoef n * (∑ h ∈ Finset.Ioc J K,
        if n + h ∈ Finset.Ioc N (2 * N) then acoef (n + h) else 0) := by
  unfold rowShiftBlockCorrelation dyadicLambdaWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N) <;> simp [hmem]

/-- Exact relation between the raw row block and the corresponding future
von-Mangoldt interval. -/
theorem rawRowShiftBlockCorrelation_eq_lambda_mul
    (N n J K : ℕ) :
    rawRowShiftBlockCorrelation N n J K =
      ArithmeticFunction.vonMangoldt n *
        (∑ h ∈ Finset.Ioc J K,
          if n + h ∈ Finset.Ioc N (2 * N) then
            ArithmeticFunction.vonMangoldt (n + h) else 0) := by
  unfold rawRowShiftBlockCorrelation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hmem : n + h ∈ Finset.Ioc N (2 * N) <;> simp [hmem]

/-- Exact reindexing of an untruncated future von-Mangoldt block to the
paper's `(x,x+H]` interval convention. -/
theorem sum_lambda_add_Ioc_eq_interval_sub
    (n J K : ℕ) (hJK : J ≤ K) :
    (∑ h ∈ Finset.Ioc J K, ArithmeticFunction.vonMangoldt (n + h)) =
      lambdaIntervalSum n K - lambdaIntervalSum n J := by
  unfold lambdaIntervalSum
  have hK :
      (∑ m ∈ Finset.Ioc n (n + K), ArithmeticFunction.vonMangoldt m) =
        ∑ h ∈ Finset.Icc 1 K, ArithmeticFunction.vonMangoldt (n + h) := by
    apply Finset.sum_bij' (fun m _ => m - n) (fun h _ => n + h)
    · intro m hm
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hh ⊢
      omega
    · intro m hm
      exact Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ioc.mp hm).1)
    · intro h hh
      exact Nat.add_sub_cancel_left n h
    · intro m hm
      rw [Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ioc.mp hm).1)]
  have hJ :
      (∑ m ∈ Finset.Ioc n (n + J), ArithmeticFunction.vonMangoldt m) =
        ∑ h ∈ Finset.Icc 1 J, ArithmeticFunction.vonMangoldt (n + h) := by
    apply Finset.sum_bij' (fun m _ => m - n) (fun h _ => n + h)
    · intro m hm
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hh ⊢
      omega
    · intro m hm
      exact Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ioc.mp hm).1)
    · intro h hh
      exact Nat.add_sub_cancel_left n h
    · intro m hm
      rw [Nat.add_sub_of_le (Nat.le_of_lt (Finset.mem_Ioc.mp hm).1)]
  rw [hK, hJ]
  have hsub : Finset.Icc 1 J ⊆ Finset.Icc 1 K := by
    intro h hh
    simp only [Finset.mem_Icc] at hh ⊢
    omega
  rw [← Finset.sum_sdiff hsub]
  have hset : Finset.Icc 1 K \ Finset.Icc 1 J = Finset.Ioc J K := by
    ext h
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  ring

/-! ### Restoring the exact square-root normalization -/

/-- Quantitative variation of the reciprocal square root.  This is the
normalization loss needed to pass from the fixed-length GM `Λ` statement to
the literal Zeta23 coefficient `acoef (n+h)`. -/
theorem one_div_sqrt_sub_one_div_sqrt_add_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    0 ≤ 1 / Real.sqrt x - 1 / Real.sqrt (x + y) ∧
      1 / Real.sqrt x - 1 / Real.sqrt (x + y) ≤
        y / (x * Real.sqrt x) := by
  have hxy : 0 < x + y := by linarith
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hb : 0 < Real.sqrt (x + y) := Real.sqrt_pos.2 hxy
  have hab : Real.sqrt x ≤ Real.sqrt (x + y) :=
    Real.sqrt_le_sqrt (by linarith)
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le ha hab)
  · have hsqx : Real.sqrt x * Real.sqrt x = x :=
      Real.mul_self_sqrt hx.le
    have hsqxy : Real.sqrt (x + y) * Real.sqrt (x + y) = x + y :=
      Real.mul_self_sqrt hxy.le
    have hid :
        1 / Real.sqrt x - 1 / Real.sqrt (x + y) =
          y / (Real.sqrt x * Real.sqrt (x + y) *
            (Real.sqrt x + Real.sqrt (x + y))) := by
      field_simp [ha.ne', hb.ne', (add_pos ha hb).ne']
      nlinarith
    rw [hid]
    have hden :
        x * Real.sqrt x ≤
          Real.sqrt x * Real.sqrt (x + y) *
            (Real.sqrt x + Real.sqrt (x + y)) := by
      calc
        x * Real.sqrt x =
            (Real.sqrt x * Real.sqrt x) * Real.sqrt x := by rw [hsqx]
        _ ≤ (Real.sqrt x * Real.sqrt (x + y)) * Real.sqrt x :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hab ha.le) ha.le
        _ ≤ Real.sqrt x * Real.sqrt (x + y) *
            (Real.sqrt x + Real.sqrt (x + y)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb.le)
            (mul_nonneg ha.le hb.le)
    exact div_le_div_of_nonneg_left hy (mul_pos hx ha) hden

/-- The preceding real-variable estimate in the exact natural-number
coordinates of a shift row. -/
theorem one_div_sqrt_nat_sub_le
    {n h : ℕ} (hn : 1 ≤ n) :
    0 ≤ 1 / Real.sqrt n - 1 / Real.sqrt (n + h) ∧
      1 / Real.sqrt n - 1 / Real.sqrt (n + h) ≤
        h / ((n : ℝ) * Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  simpa only [Nat.cast_add] using
    one_div_sqrt_sub_one_div_sqrt_add_le hn0
      (show (0 : ℝ) ≤ h by positivity)

/-- The untruncated future Zeta23 coefficient mass on one shift block. -/
def futureAcoefBlock (n J K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc J K, acoef (n + h)

/-- Exact loss from freezing `1/sqrt(n+h)` at the row start `n`. -/
def sqrtNormalizationRemainder (n J K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Ioc J K, ArithmeticFunction.vonMangoldt (n + h) *
    (1 / Real.sqrt n - 1 / Real.sqrt (n + h))

/-- Exact square-root normalization identity on a finite shift block. -/
theorem futureAcoefBlock_eq_lambda_sub_remainder
    (n J K : ℕ) (hJK : J ≤ K) :
    futureAcoefBlock n J K =
      (lambdaIntervalSum n K - lambdaIntervalSum n J) / Real.sqrt n -
        sqrtNormalizationRemainder n J K := by
  rw [← sum_lambda_add_Ioc_eq_interval_sub n J K hJK]
  unfold futureAcoefBlock sqrtNormalizationRemainder
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  unfold acoef
  rw [Nat.cast_add]
  ring

/-- The normalization remainder is nonnegative. -/
theorem sqrtNormalizationRemainder_nonneg
    {n J K : ℕ} (hn : 1 ≤ n) :
    0 ≤ sqrtNormalizationRemainder n J K := by
  unfold sqrtNormalizationRemainder
  exact Finset.sum_nonneg fun h _ => mul_nonneg
    ArithmeticFunction.vonMangoldt_nonneg
    (one_div_sqrt_nat_sub_le hn).1

/-- Uniform quantitative bound for the square-root freezing loss.  The
factor `K/n` is the exact relative loss on a block contained in shifts at
most `K`. -/
theorem sqrtNormalizationRemainder_le
    {n J K : ℕ} (hn : 1 ≤ n) (hJK : J ≤ K) :
    sqrtNormalizationRemainder n J K ≤
      (K : ℝ) / ((n : ℝ) * Real.sqrt n) *
        (lambdaIntervalSum n K - lambdaIntervalSum n J) := by
  rw [← sum_lambda_add_Ioc_eq_interval_sub n J K hJK]
  unfold sqrtNormalizationRemainder
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h hhmem
  have hhK : h ≤ K := (Finset.mem_Ioc.mp hhmem).2
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : 0 < (n : ℝ) * Real.sqrt n :=
    mul_pos hn0 (Real.sqrt_pos.2 hn0)
  have hvar := (one_div_sqrt_nat_sub_le (n := n) (h := h) hn).2
  have hcast : (h : ℝ) ≤ K := by exact_mod_cast hhK
  have hquot :
      (h : ℝ) / ((n : ℝ) * Real.sqrt n) ≤
        (K : ℝ) / ((n : ℝ) * Real.sqrt n) :=
    div_le_div_of_nonneg_right hcast hden.le
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (hvar.trans hquot)
      ArithmeticFunction.vonMangoldt_nonneg

/-- On an interior row the ambient dyadic cutoff is identically true on
the whole block. -/
theorem rowShiftBlockCorrelation_eq_acoef_mul_future
    {N n J K : ℕ} (hn : n ∈ Finset.Ioc N (2 * N))
    (hRight : n + K ≤ 2 * N) :
    rowShiftBlockCorrelation N n J K =
      acoef n * futureAcoefBlock n J K := by
  rw [rowShiftBlockCorrelation_eq_acoef_mul]
  unfold futureAcoefBlock
  congr 1
  apply Finset.sum_congr rfl
  intro h hhmem
  have hh := Finset.mem_Ioc.mp hhmem
  have hmem : n + h ∈ Finset.Ioc N (2 * N) := by
    simp only [Finset.mem_Ioc]
    have hn' := Finset.mem_Ioc.mp hn
    constructor
    · omega
    · omega
  simp [hmem]

/-- Exact interior-row identity combining the GM endpoint convention with
the literal Zeta23 square-root normalization. -/
theorem rowShiftBlockCorrelation_eq_normalizedLambda_sub
    {N n J K : ℕ} (hn : n ∈ Finset.Ioc N (2 * N))
    (hJK : J ≤ K) (hRight : n + K ≤ 2 * N) :
    rowShiftBlockCorrelation N n J K =
      acoef n *
        ((lambdaIntervalSum n K - lambdaIntervalSum n J) / Real.sqrt n -
          sqrtNormalizationRemainder n J K) := by
  rw [rowShiftBlockCorrelation_eq_acoef_mul_future hn hRight,
    futureAcoefBlock_eq_lambda_sub_remainder n J K hJK]

/-- The deterministic block main term after the fixed-length GM input and
the exact Zeta23 normalization are aligned. -/
def normalizedRowBlockMain (n J K : ℕ) : ℝ :=
  acoef n * ((K - J : ℕ) / Real.sqrt n)

/-- Complete finite error ledger for one good interior row.  The first term
is the two-endpoint GM error; the second is exactly the square-root freezing
loss, with the same GM bound used to majorize the raw block mass. -/
def normalizedRowBlockErrorBudget
    (C : ℝ) (X n J K : ℕ) : ℝ :=
  acoef n *
    (C * (K + J) * gmDecay X / Real.sqrt n +
      (K : ℝ) / ((n : ℝ) * Real.sqrt n) *
        ((K - J : ℕ) + C * (K + J) * gmDecay X))

/-- Exact finite good-row consumer of simultaneous fixed-length GM control.
It reaches the actual normalized Zeta23 correlation and retains the dyadic
right-edge condition explicitly. -/
theorem abs_rowShiftBlockCorrelation_sub_main_le
    {C : ℝ} {X N n J K : ℕ} {lengths : Finset ℕ}
    (hC : 0 ≤ C)
    (hnDyadic : n ∈ Finset.Ioc N (2 * N))
    (hnGM : n ∈ Finset.Icc X (2 * X))
    (hgood : n ∉ gmSimultaneousLambdaBadSet C X lengths)
    (hJ : J ∈ lengths) (hK : K ∈ lengths) (hJK : J ≤ K)
    (hRight : n + K ≤ 2 * N) :
    |rowShiftBlockCorrelation N n J K - normalizedRowBlockMain n J K| ≤
      normalizedRowBlockErrorBudget C X n J K := by
  let L : ℝ := lambdaIntervalSum n K - lambdaIntervalSum n J
  let B : ℝ := (K - J : ℕ)
  let E : ℝ := C * (K + J) * gmDecay X
  let R : ℝ := sqrtNormalizationRemainder n J K
  have hnOne : 1 ≤ n := by
    have hn' := Finset.mem_Ioc.mp hnDyadic
    omega
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnOne)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have ha : 0 ≤ acoef n := acoef_nonneg n
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg hC (by positivity)) (Real.exp_pos _).le
  have hLerr : |L - B| ≤ E := by
    dsimp [L, B, E]
    exact abs_lambdaInterval_sub_sub_blockLength_le
      hnGM hgood hJ hK hJK
  have hL : L ≤ B + E := by
    have := (le_abs_self (L - B)).trans hLerr
    linarith
  have hcoef : 0 ≤ (K : ℝ) / ((n : ℝ) * Real.sqrt n) := by positivity
  have hR0 : 0 ≤ R := by
    dsimp [R]
    exact sqrtNormalizationRemainder_nonneg hnOne
  have hR : R ≤ (K : ℝ) / ((n : ℝ) * Real.sqrt n) * (B + E) := by
    dsimp [R]
    refine (sqrtNormalizationRemainder_le hnOne hJK).trans ?_
    exact mul_le_mul_of_nonneg_left hL hcoef
  rw [rowShiftBlockCorrelation_eq_normalizedLambda_sub
    hnDyadic hJK hRight]
  unfold normalizedRowBlockMain normalizedRowBlockErrorBudget
  change |acoef n * (L / Real.sqrt n - R) -
      acoef n * (B / Real.sqrt n)| ≤
    acoef n * (E / Real.sqrt n +
      (K : ℝ) / ((n : ℝ) * Real.sqrt n) * (B + E))
  rw [show acoef n * (L / Real.sqrt n - R) -
      acoef n * (B / Real.sqrt n) =
      acoef n * ((L - B) / Real.sqrt n - R) by ring,
    abs_mul, abs_of_nonneg ha]
  apply mul_le_mul_of_nonneg_left _ ha
  calc
    |(L - B) / Real.sqrt n - R| ≤
        |(L - B) / Real.sqrt n| + |R| := by
      rw [sub_eq_add_neg]
      simpa only [abs_neg] using
        abs_add_le ((L - B) / Real.sqrt n) (-R)
    _ = |L - B| / Real.sqrt n + R := by
      rw [abs_div, abs_of_pos hsqrt, abs_of_nonneg hR0]
    _ ≤ E / Real.sqrt n + R := by
      exact add_le_add
        (div_le_div_of_nonneg_right hLerr hsqrt.le) le_rfl
    _ ≤ E / Real.sqrt n +
        (K : ℝ) / ((n : ℝ) * Real.sqrt n) * (B + E) :=
      add_le_add le_rfl hR

/-- Full error budget after both the arithmetic correlation and the literal
kernel are frozen on one good row/block. -/
def goodRowShiftBlockErrorBudget
    (Phi : ℝ → ℝ) (T C : ℝ) (X N n J K : ℕ) : ℝ :=
  |rowShiftBlockAnchor Phi T n J| *
      normalizedRowBlockErrorBudget C X n J K +
    ∑ h ∈ Finset.Ioc J K,
      dyadicLambdaWeight n h *
        rowShiftOscillationBudget Phi T N h (J + 1)

/-- The exact one-row arithmetic-plus-kernel consumer.  This is the point at
which the simultaneous GM endpoint information acts on the literal Zeta23
shift kernel, rather than on a detached scalar prefix. -/
theorem abs_rowShiftBlockSum_sub_anchoredMain_le
    {Phi : ℝ → ℝ} {T C : ℝ} {X N n J K : ℕ}
    {lengths : Finset ℕ}
    (hT : 0 ≤ T) (hC : 0 ≤ C) (hN : 1 ≤ N)
    (hnDyadic : n ∈ Finset.Ioc N (2 * N))
    (hnGM : n ∈ Finset.Icc X (2 * X))
    (hgood : n ∉ gmSimultaneousLambdaBadSet C X lengths)
    (hJ : J ∈ lengths) (hK : K ∈ lengths) (hJK : J ≤ K)
    (hRight : n + K ≤ 2 * N) (hKN : K ≤ N)
    (hPhi : Continuous Phi)
    (hPhi2 : Integrable fun x => Phi x ^ 2)
    (hPhiAbs : Integrable fun x => Phi x ^ 2 * |x|) :
    |rowShiftBlockSum Phi T N n J K -
        rowShiftBlockAnchor Phi T n J * normalizedRowBlockMain n J K| ≤
      goodRowShiftBlockErrorBudget Phi T C X N n J K := by
  rw [rowShiftBlockSum_eq_anchor_add_variation]
  unfold goodRowShiftBlockErrorBudget
  rw [show rowShiftBlockAnchor Phi T n J * rowShiftBlockCorrelation N n J K +
        rowShiftBlockVariation Phi T N n J K -
        rowShiftBlockAnchor Phi T n J * normalizedRowBlockMain n J K =
      rowShiftBlockAnchor Phi T n J *
          (rowShiftBlockCorrelation N n J K - normalizedRowBlockMain n J K) +
        rowShiftBlockVariation Phi T N n J K by ring]
  calc
    |rowShiftBlockAnchor Phi T n J *
          (rowShiftBlockCorrelation N n J K - normalizedRowBlockMain n J K) +
        rowShiftBlockVariation Phi T N n J K| ≤
      |rowShiftBlockAnchor Phi T n J| *
          |rowShiftBlockCorrelation N n J K - normalizedRowBlockMain n J K| +
        |rowShiftBlockVariation Phi T N n J K| := by
      simpa only [abs_mul] using abs_add_le
        (rowShiftBlockAnchor Phi T n J *
          (rowShiftBlockCorrelation N n J K - normalizedRowBlockMain n J K))
        (rowShiftBlockVariation Phi T N n J K)
    _ ≤ |rowShiftBlockAnchor Phi T n J| *
          normalizedRowBlockErrorBudget C X n J K +
        ∑ h ∈ Finset.Ioc J K,
          dyadicLambdaWeight n h *
            rowShiftOscillationBudget Phi T N h (J + 1) :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (abs_rowShiftBlockCorrelation_sub_main_le hC hnDyadic hnGM hgood
            hJ hK hJK hRight)
          (abs_nonneg _))
        (abs_rowShiftBlockVariation_le hT hN hnDyadic hKN
          hPhi hPhi2 hPhiAbs)

end

end PrimeShell
