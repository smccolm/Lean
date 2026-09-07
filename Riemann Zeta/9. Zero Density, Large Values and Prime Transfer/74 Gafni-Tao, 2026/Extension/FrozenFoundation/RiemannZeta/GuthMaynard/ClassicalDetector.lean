import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.ZetaTruncation
import RiemannZeta.GuthMaynard.ArithmeticCoefficients

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RiemannZeta.GuthMaynard

/-- The Dirichlet identity truncated to the positive interval `[1,A]`. -/
noncomputable def truncatedZeta (A : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Icc 1 A then 1 else 0
  map_zero' := by simp

@[simp] theorem truncatedZeta_apply (A n : ℕ) :
    truncatedZeta A n = if n ∈ Icc 1 A then 1 else 0 := rfl

theorem truncatedZeta_hasFiniteSupport (A : ℕ) :
    Function.HasFiniteSupport (truncatedZeta A) := by
  apply Set.Finite.subset (Icc 1 A).finite_toSet
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  by_contra hnMem
  have hnMem' : n ∉ Icc 1 A := by simpa using hnMem
  exact hn (by rw [truncatedZeta_apply, if_neg hnMem'])

theorem truncatedZeta_LSeriesSummable (A : ℕ) (s : ℂ) :
    LSeriesSummable (truncatedZeta A) s := by
  unfold LSeriesSummable
  exact summable_of_hasFiniteSupport <|
    (truncatedZeta_hasFiniteSupport A).subset (by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn ⊢
      contrapose! hn
      rw [LSeries.term_def₀ (truncatedZeta A).map_zero]
      simp [hn])

/-- The finite zeta sum is the L-series of `truncatedZeta`. -/
theorem zetaPartialSum_eq_LSeries (A : ℕ) (s : ℂ) :
    (∑ n ∈ Icc 1 A, (n : ℂ) ^ (-s)) = LSeries (truncatedZeta A) s := by
  rw [LSeries, tsum_eq_sum (s := Icc 1 A)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (truncatedZeta A).map_zero]
    simp only [truncatedZeta_apply, if_pos hn, one_mul]
  · intro n hn
    rw [LSeries.term_def₀ (truncatedZeta A).map_zero]
    simp [hn]

/-- Coefficients of the rectangular product of a finite zeta sum and a
finite Möbius mollifier. -/
noncomputable def sharpMollifiedCoeff (A X : ℕ) : ArithmeticFunction ℂ :=
  truncatedZeta A * truncatedMoebius X

/-- A mollifier of length one is the identity arithmetic function. -/
theorem truncatedMoebius_one : truncatedMoebius 1 = (1 : ArithmeticFunction ℂ) := by
  ext n
  rw [truncatedMoebius_apply, ArithmeticFunction.one_apply]
  by_cases hn : n = 1
  · subst n
    simp
  · simp [hn]

/-- With mollifier length one the sharp product is exactly the truncated
zeta coefficient sequence. -/
theorem sharpMollifiedCoeff_one (A : ℕ) :
    sharpMollifiedCoeff A 1 = truncatedZeta A := by
  rw [sharpMollifiedCoeff, truncatedMoebius_one, mul_one]

theorem norm_sharpMollifiedCoeff_one_le_one (A n : ℕ) :
    ‖sharpMollifiedCoeff A 1 n‖ ≤ 1 := by
  rw [sharpMollifiedCoeff_one, truncatedZeta_apply]
  split <;> simp

/-- Möbius cancellation is exact below both truncation lengths. -/
theorem sharpMollifiedCoeff_eq_ite (A X n : ℕ) (hn : 0 < n)
    (hnA : n ≤ A) (hnX : n ≤ X) :
    sharpMollifiedCoeff A X n = if n = 1 then 1 else 0 := by
  have hEq : sharpMollifiedCoeff A X n =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) n := by
    rw [sharpMollifiedCoeff, ArithmeticFunction.mul_apply,
      ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpMul, _hnNe⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hnNe : n ≠ 0 := Nat.ne_of_gt hn
    have hpLeftNe : p.1 ≠ 0 := by
      intro hpZero
      apply hnNe
      rw [← hpMul, hpZero, zero_mul]
    have hpRightNe : p.2 ≠ 0 := by
      intro hpZero
      apply hnNe
      rw [← hpMul, hpZero, mul_zero]
    have hpLeftPos : 0 < p.1 := Nat.pos_of_ne_zero hpLeftNe
    have hpRightPos : 0 < p.2 := Nat.pos_of_ne_zero hpRightNe
    have hpLeftOne : 1 ≤ p.1 := Nat.one_le_iff_ne_zero.mpr hpLeftNe
    have hpRightOne : 1 ≤ p.2 := Nat.one_le_iff_ne_zero.mpr hpRightNe
    have hpLeftLeN : p.1 ≤ n := by
      rw [← hpMul]
      exact Nat.le_mul_of_pos_right p.1 hpRightPos
    have hpRightLeN : p.2 ≤ n := by
      rw [← hpMul]
      exact Nat.le_mul_of_pos_left p.2 hpLeftPos
    simp [truncatedZeta_apply, truncatedMoebius_apply, Finset.mem_Icc,
      hpLeftNe, hpLeftOne, hpRightOne, hpLeftLeN.trans hnA,
      hpRightLeN.trans hnX]
  rw [hEq, ArithmeticFunction.coe_zeta_mul_coe_moebius]
  exact ArithmeticFunction.one_apply

theorem sharpMollifiedCoeff_eq_zero (A X n : ℕ) (hn : 1 < n)
    (hnA : n ≤ A) (hnX : n ≤ X) :
    sharpMollifiedCoeff A X n = 0 := by
  rw [sharpMollifiedCoeff_eq_ite A X n (by omega) hnA hnX,
    if_neg (by omega)]

/-- Exact finite Dirichlet-series expansion of the sharp partial-zeta sum
times the Möbius mollifier. -/
theorem zetaPartialSum_mul_zetaMollifier_eq_LSeries (A X : ℕ) (s : ℂ) :
    (∑ n ∈ Icc 1 A, (n : ℂ) ^ (-s)) * zetaMollifier X s =
      LSeries (sharpMollifiedCoeff A X) s := by
  have hLeft := truncatedZeta_LSeriesSummable A s
  have hRight := truncatedMoebius_LSeriesSummable X s
  have hMul :
      LSeries (sharpMollifiedCoeff A X) s =
        LSeries (truncatedZeta A) s * LSeries (truncatedMoebius X) s := by
    simpa only [sharpMollifiedCoeff] using
      ArithmeticFunction.LSeries_mul' (f := truncatedZeta A)
        (g := truncatedMoebius X) (s := s) hLeft hRight
  rw [zetaPartialSum_eq_LSeries, zetaMollifier_eq_LSeries, hMul]

/-- The rectangular convolution has no coefficient beyond the product of its
two truncation lengths. -/
theorem sharpMollifiedCoeff_eq_zero_of_mul_lt (A X n : ℕ) (hn : A * X < n) :
    sharpMollifiedCoeff A X n = 0 := by
  rw [sharpMollifiedCoeff, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hpMul, _hnNe⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  simp only [truncatedZeta_apply, truncatedMoebius_apply]
  by_cases hpA : p.1 ∈ Icc 1 A
  · have hpX : p.2 ∉ Icc 1 X := by
      intro hpX
      have hpLe : p.1 * p.2 ≤ A * X :=
        Nat.mul_le_mul (Finset.mem_Icc.mp hpA).2 (Finset.mem_Icc.mp hpX).2
      omega
    simp [hpA, hpX]
  · simp [hpA]

theorem sharpMollifiedCoeff_hasFiniteSupport (A X : ℕ) :
    Function.HasFiniteSupport (sharpMollifiedCoeff A X) := by
  apply Set.Finite.subset (Icc 1 (A * X)).finite_toSet
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn ⊢
  by_contra hnMem
  by_cases hnZero : n = 0
  · subst n
    exact hn (sharpMollifiedCoeff A X).map_zero
  · have hnLt : A * X < n := by
      have hnNot : ¬(1 ≤ n ∧ n ≤ A * X) := by
        simpa [Finset.mem_Icc] using hnMem
      omega
    exact hn (sharpMollifiedCoeff_eq_zero_of_mul_lt A X n hnLt)

/-- Each sharp convolution coefficient is bounded by the number of positive
divisors of its index. -/
theorem norm_sharpMollifiedCoeff_le_divisors_card (A X n : ℕ) :
    ‖sharpMollifiedCoeff A X n‖ ≤ (n.divisors.card : ℝ) := by
  rw [sharpMollifiedCoeff, ArithmeticFunction.mul_apply]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal, truncatedZeta A p.1 * truncatedMoebius X p.2‖
        ≤ ∑ p ∈ n.divisorsAntidiagonal,
            ‖truncatedZeta A p.1 * truncatedMoebius X p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      have hLeft : ‖truncatedZeta A p.1‖ ≤ 1 := by
        simp only [truncatedZeta_apply]
        split <;> simp
      have hRight : ‖truncatedMoebius X p.2‖ ≤ 1 := by
        simp only [truncatedMoebius_apply]
        split
        · rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.2)
        · simp
      calc
        ‖truncatedZeta A p.1‖ * ‖truncatedMoebius X p.2‖ ≤ 1 * 1 :=
          mul_le_mul hLeft hRight (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
    _ = (n.divisors.card : ℝ) := by
      rw [← Nat.map_div_right_divisors, Finset.card_map]

/-- The sharp convolution coefficients have the uniform epsilon-power bound
needed to normalize every dyadic detector block. -/
theorem sharpMollifiedCoeff_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (A X n : ℕ), 0 < n →
        ‖sharpMollifiedCoeff A X n‖ ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hC, hDiv⟩ := divisorCountBound_native ε hε
  exact ⟨C, hC, fun A X n hn =>
    (norm_sharpMollifiedCoeff_le_divisors_card A X n).trans (hDiv n hn)⟩

/-- The finite product L-series is exactly supported on `[1,A*X]`. -/
theorem sharpMollifiedCoeff_LSeries_eq_sum (A X : ℕ) (s : ℂ) :
    LSeries (sharpMollifiedCoeff A X) s =
      ∑ n ∈ Icc 1 (A * X), sharpMollifiedCoeff A X n * (n : ℂ) ^ (-s) := by
  rw [LSeries, tsum_eq_sum (s := Icc 1 (A * X))]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (sharpMollifiedCoeff A X).map_zero]
  · intro n hn
    rw [LSeries.term_def₀ (sharpMollifiedCoeff A X).map_zero]
    by_cases hnZero : n = 0
    · simp [hnZero]
    · have hnLt : A * X < n := by
        have hnNot : ¬(1 ≤ n ∧ n ≤ A * X) := by
          simpa [Finset.mem_Icc] using hn
        omega
      rw [sharpMollifiedCoeff_eq_zero_of_mul_lt A X n hnLt, zero_mul]

/-- Exact cancellation removes every nonconstant coefficient up through the
mollifier length, leaving one finite tail. -/
theorem zetaPartialSum_mul_zetaMollifier_eq_one_add_tail
    (A X : ℕ) (s : ℂ) (hA : 1 ≤ A) (hX : 1 ≤ X) (hXA : X ≤ A) :
    (∑ n ∈ Icc 1 A, (n : ℂ) ^ (-s)) * zetaMollifier X s =
      1 + ∑ n ∈ Ioc X (A * X),
        sharpMollifiedCoeff A X n * (n : ℂ) ^ (-s) := by
  rw [zetaPartialSum_mul_zetaMollifier_eq_LSeries,
    sharpMollifiedCoeff_LSeries_eq_sum]
  have hXAX : X ≤ A * X := by
    calc
      X = 1 * X := by simp
      _ ≤ A * X := Nat.mul_le_mul_right X hA
  have hUnion : Icc 1 (A * X) = Icc 1 X ∪ Ioc X (A * X) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  rw [hUnion, Finset.sum_union (by
    rw [Finset.disjoint_left]
    intro n hnLow hnHigh
    exact (not_lt_of_ge (Finset.mem_Icc.mp hnLow).2) (Finset.mem_Ioc.mp hnHigh).1)]
  have hLow :
      (∑ n ∈ Icc 1 X, sharpMollifiedCoeff A X n * (n : ℂ) ^ (-s)) = 1 := by
    rw [Finset.sum_eq_single 1]
    · rw [sharpMollifiedCoeff_eq_ite A X 1 (by omega) hA hX]
      simp
    · intro n hn hnOne
      have hnData := Finset.mem_Icc.mp hn
      rw [sharpMollifiedCoeff_eq_zero A X n (by omega) (hnData.2.trans hXA) hnData.2]
      simp
    · intro h
      exact False.elim (h (Finset.mem_Icc.mpr ⟨by omega, hX⟩))
  rw [hLow]

/-- A direct majorant for the finite Möbius mollifier on the closed right
half-plane. -/
theorem norm_zetaMollifier_le_sum_rpow (X : ℕ) (s : ℂ) :
    ‖zetaMollifier X s‖ ≤ ∑ n ∈ Icc 1 X, (n : ℝ) ^ (-s.re) := by
  unfold zetaMollifier
  calc
    ‖∑ n ∈ Icc 1 X,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Icc 1 X,
            ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 X, (n : ℝ) ^ (-s.re) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos]
      · have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hμ
      · exact lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1

/-- At a zeta zero the exact mollified convolution has a large tail, with
the truncation error and mollifier mass both displayed explicitly. -/
theorem norm_sharpMollifiedTail_ge {σ T : ℝ} {ρ : ℂ} (X : ℕ)
    (hT : 3 / 4 ≤ T) (hρmem : ρ ∈ zerosInRect σ 1 T (2 * T))
    (hσ : 0 < σ) (hX : 1 ≤ X) (hXA : X ≤ ⌊sharpZetaCutoff T⌋₊) :
    1 - 149 * sharpZetaCutoff T ^ (-ρ.re) *
        (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) ≤
      ‖∑ n ∈ Ioc X (⌊sharpZetaCutoff T⌋₊ * X),
        sharpMollifiedCoeff ⌊sharpZetaCutoff T⌋₊ X n * (n : ℂ) ^ (-ρ)‖ := by
  let A := ⌊sharpZetaCutoff T⌋₊
  let tail := ∑ n ∈ Ioc X (A * X),
    sharpMollifiedCoeff A X n * (n : ℂ) ^ (-ρ)
  have hA : 1 ≤ A := by
    apply (Nat.one_le_floor_iff _).mpr
    have hTpos : 0 < T := by linarith
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hSplit :
      (∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) * zetaMollifier X ρ = 1 + tail := by
    exact zetaPartialSum_mul_zetaMollifier_eq_one_add_tail A X ρ hA hX hXA
  have hMollifier : ‖zetaMollifier X ρ‖ ≤
      ∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re) := by
    exact norm_zetaMollifier_le_sum_rpow X ρ
  have hProduct :
      ‖(∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) * zetaMollifier X ρ‖ ≤
        149 * sharpZetaCutoff T ^ (-ρ.re) *
          (∑ n ∈ Icc 1 X, (n : ℝ) ^ (-ρ.re)) := by
    rw [norm_mul]
    have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
      have hTpos : 0 < T := by linarith
      exact (four_mul_lt_sharpZetaCutoff T).le.trans' (mul_nonneg (by norm_num) hTpos.le)
    have hSharpNonneg :
        0 ≤ 149 * sharpZetaCutoff T ^ (-ρ.re) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hCutNonneg _)
    exact mul_le_mul
      (by simpa only [A] using norm_zeta_zero_sharp_cutoff_sum_le hT hρmem hσ)
      hMollifier (norm_nonneg _) hSharpNonneg
  have hTriangle :
      (1 : ℝ) ≤
        ‖(∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) * zetaMollifier X ρ‖ + ‖tail‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖((∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) * zetaMollifier X ρ) - tail‖ := by
        rw [hSplit]
        ring_nf
      _ ≤ ‖(∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) * zetaMollifier X ρ‖ + ‖tail‖ :=
        norm_sub_le _ _
  dsimp only [A, tail] at hTriangle ⊢
  linarith

/-- At a zeta zero, sharp truncation forces the nonconstant finite zeta tail
to have norm close to one. This is the raw zeta-polynomial witness used by the
finite density transfer. -/
theorem norm_sharpZetaTail_ge {σ T : ℝ} {ρ : ℂ} (hT : 3 / 4 ≤ T)
    (hρmem : ρ ∈ zerosInRect σ 1 T (2 * T)) (hσ : 0 < σ) :
    1 - 149 * sharpZetaCutoff T ^ (-ρ.re) ≤
      ‖∑ n ∈ Ioc 1 ⌊sharpZetaCutoff T⌋₊, (n : ℂ) ^ (-ρ)‖ := by
  let A := ⌊sharpZetaCutoff T⌋₊
  let tail := ∑ n ∈ Ioc 1 A, (n : ℂ) ^ (-ρ)
  have hCutOne : 1 ≤ sharpZetaCutoff T := by
    have hTpos : 0 < T := by linarith
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hA : 1 ≤ A := by
    exact (Nat.one_le_floor_iff _).mpr hCutOne
  have hSplit :
      (∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) = 1 + tail := by
    rw [Finset.Icc_eq_cons_Ioc hA, Finset.sum_cons]
    simp [tail]
  have hTriangle :
      (1 : ℝ) ≤ ‖∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)‖ + ‖tail‖ := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)) - tail‖ := by
        rw [hSplit]
        ring_nf
      _ ≤ ‖∑ n ∈ Icc 1 A, (n : ℂ) ^ (-ρ)‖ + ‖tail‖ := norm_sub_le _ _
  have hSharp := norm_zeta_zero_sharp_cutoff_sum_le hT hρmem hσ
  dsimp only [A] at hSharp hTriangle
  linarith

end RiemannZeta.GuthMaynard
