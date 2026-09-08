import Tao2026.PowerfulAsymptotics
import Tao2026.PublicStatements
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

open Filter Asymptotics Topology

namespace Tao2026

private theorem sqrt_nat_div_le_nat_sqrt_add_two (x q : ℕ) (hq : 0 < q) :
    Real.sqrt x / Real.sqrt q ≤ (Nat.sqrt (x / q) : ℝ) + 2 := by
  have hxlt : x < (x / q + 1) * q :=
    (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (x / q))
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : (x : ℝ) / (q : ℝ) < (x / q : ℕ) + 1 := by
    rw [div_lt_iff₀ hqReal]
    exact_mod_cast hxlt
  calc
    Real.sqrt x / Real.sqrt q = Real.sqrt ((x : ℝ) / (q : ℝ)) := by
      rw [Real.sqrt_div (Nat.cast_nonneg x)]
    _ ≤ Real.sqrt ((x / q : ℕ) + 1) := Real.sqrt_le_sqrt hdiv.le
    _ ≤ Real.sqrt (x / q : ℕ) + 1 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · have hs := Real.sq_sqrt (Nat.cast_nonneg (x / q))
        nlinarith [Real.sqrt_nonneg (x / q : ℕ)]
    _ ≤ (Nat.sqrt (x / q) : ℝ) + 2 := by
      linarith [Real.real_sqrt_le_nat_sqrt_succ (a := x / q)]

private theorem sqrt_mul_rpow_neg_three_halves (x b : ℕ) :
    Real.sqrt x * (b : ℝ) ^ (-(3 / 2 : ℝ)) =
      Real.sqrt x / Real.sqrt (b ^ 3 : ℕ) := by
  simp only [Real.sqrt_eq_rpow]
  rw [show ((b ^ 3 : ℕ) : ℝ) = (b : ℝ) ^ (3 : ℕ) by norm_cast,
    ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg b)]
  norm_num
  simp only [Real.rpow_neg (Nat.cast_nonneg b), div_eq_mul_inv]

private theorem normalized_sqrt_div_cube_tendsto (b : ℕ) (hb : 1 ≤ b) :
    Tendsto (fun x : ℕ =>
      (Nat.sqrt (x / b ^ 3) : ℝ) / Real.sqrt x) atTop
      (𝓝 ((b : ℝ) ^ (-(3 / 2 : ℝ)))) := by
  have hbCube : 0 < b ^ 3 := pow_pos (Nat.zero_lt_of_lt hb) 3
  have herr : Tendsto (fun x : ℕ => 2 / Real.sqrt x) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 2
  have hdiff : Tendsto (fun x : ℕ =>
      (b : ℝ) ^ (-(3 / 2 : ℝ)) -
        (Nat.sqrt (x / b ^ 3) : ℝ) / Real.sqrt x) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun x : ℕ => 2 / Real.sqrt x)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by exact_mod_cast hx)
      rw [sub_nonneg]
      apply (div_le_iff₀ hsqrtPos).2
      simpa [mul_comm] using cast_sqrt_div_cube_le x b
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by exact_mod_cast hx)
      rw [sub_le_iff_le_add]
      calc
        (b : ℝ) ^ (-(3 / 2 : ℝ)) ≤
            ((Nat.sqrt (x / b ^ 3) : ℝ) + 2) / Real.sqrt x := by
          apply (le_div_iff₀ hsqrtPos).2
          rw [mul_comm, sqrt_mul_rpow_neg_three_halves x b]
          exact sqrt_nat_div_le_nat_sqrt_add_two x (b ^ 3) hbCube
        _ = (Nat.sqrt (x / b ^ 3) : ℝ) / Real.sqrt x +
            2 / Real.sqrt x := by rw [add_div]
        _ = 2 / Real.sqrt x +
            (Nat.sqrt (x / b ^ 3) : ℝ) / Real.sqrt x := add_comm _ _
    · exact herr
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
    (b : ℝ) ^ (-(3 / 2 : ℝ))) atTop
      (𝓝 ((b : ℝ) ^ (-(3 / 2 : ℝ))))).sub hdiff
  convert h using 1 <;> simp

noncomputable def normalizedPowerfulSummand (x b : ℕ) : ℝ :=
  if b ∈ (Finset.Icc 1 x).filter Squarefree then
    (Nat.sqrt (x / b ^ 3) : ℝ) / Real.sqrt x
  else 0

noncomputable def squarefreePSeriesSummand (b : ℕ) : ℝ :=
  if 1 ≤ b ∧ Squarefree b then (b : ℝ) ^ (-(3 / 2 : ℝ)) else 0

noncomputable def squarefreePSeriesConstant : ℝ :=
  ∑' b : ℕ, squarefreePSeriesSummand b

theorem summable_squarefreePSeriesSummand : Summable squarefreePSeriesSummand := by
  apply summable_powerfulPSeries.of_nonneg_of_le
  · intro b
    simp only [squarefreePSeriesSummand]
    split <;> positivity
  · intro b
    simp only [squarefreePSeriesSummand]
    split <;> simp [Real.rpow_nonneg (Nat.cast_nonneg b)]

theorem normalizedPowerfulSummand_tendsto (b : ℕ) :
    Tendsto (fun x : ℕ => normalizedPowerfulSummand x b) atTop
      (𝓝 (squarefreePSeriesSummand b)) := by
  by_cases hb : 1 ≤ b ∧ Squarefree b
  · rw [squarefreePSeriesSummand, if_pos hb]
    refine (normalized_sqrt_div_cube_tendsto b hb.1).congr' ?_
    filter_upwards [eventually_ge_atTop b] with x hbx
    simp [normalizedPowerfulSummand, hb.1, hb.2, hbx]
  · rw [squarefreePSeriesSummand, if_neg hb]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [] with x
    symm
    rw [normalizedPowerfulSummand, if_neg]
    intro hmem
    have hmem' := Finset.mem_filter.mp hmem
    exact hb ⟨(Finset.mem_Icc.mp hmem'.1).1, hmem'.2⟩

theorem norm_normalizedPowerfulSummand_le (x : ℕ) (hx : 1 ≤ x) (b : ℕ) :
    ‖normalizedPowerfulSummand x b‖ ≤
      (b : ℝ) ^ (-(3 / 2 : ℝ)) := by
  simp only [normalizedPowerfulSummand]
  split_ifs with hb
  · rw [Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))]
    have hsqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 (by exact_mod_cast hx)
    apply (div_le_iff₀ hsqrtPos).2
    simpa [mul_comm] using cast_sqrt_div_cube_le x b
  · simp [Real.rpow_nonneg (Nat.cast_nonneg b)]

theorem tsum_normalizedPowerfulSummand (x : ℕ) :
    ∑' b : ℕ, normalizedPowerfulSummand x b =
      (veryBadOneTermCount x : ℝ) / Real.sqrt x := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 x).filter Squarefree)]
  · calc
      ∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
          normalizedPowerfulSummand x b =
        ∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
          (Nat.sqrt (x / b ^ 3) : ℝ) / Real.sqrt x := by
            apply Finset.sum_congr rfl
            intro b hb
            simp [normalizedPowerfulSummand, hb]
      _ = (∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
          (Nat.sqrt (x / b ^ 3) : ℝ)) / Real.sqrt x := by
            simp only [div_eq_mul_inv]
            rw [Finset.sum_mul]
      _ = (veryBadOneTermCount x : ℝ) / Real.sqrt x := by
            rw [veryBadOneTermCount_eq_sum_sqrt_div_cube]
            push_cast
            rfl
  · intro b hb
    simp [normalizedPowerfulSummand, hb]

theorem veryBadOneTermCount_normalized_tendsto :
    Tendsto (fun x : ℕ =>
      (veryBadOneTermCount x : ℝ) / Real.sqrt x) atTop
      (𝓝 squarefreePSeriesConstant) := by
  have h := tendsto_tsum_of_dominated_convergence
    summable_powerfulPSeries normalizedPowerfulSummand_tendsto
    (show ∀ᶠ x : ℕ in atTop, ∀ b,
        ‖normalizedPowerfulSummand x b‖ ≤
          (b : ℝ) ^ (-(3 / 2 : ℝ)) by
      filter_upwards [eventually_ge_atTop 1] with x hx b
      exact norm_normalizedPowerfulSummand_le x hx b)
  simpa only [tsum_normalizedPowerfulSummand, squarefreePSeriesConstant] using h

theorem squarefreePSeriesConstant_pos : 0 < squarefreePSeriesConstant := by
  exact summable_squarefreePSeriesSummand.tsum_pos
    (fun b => by
      simp only [squarefreePSeriesSummand]
      split <;> positivity)
    1 (by norm_num [squarefreePSeriesSummand])

theorem veryBadOneTermCount_asymptotic_squarefreePSeries :
    SequenceEquivalent
      (fun x : ℕ => (veryBadOneTermCount x : ℝ))
      (fun x : ℕ => squarefreePSeriesConstant * Real.sqrt x) := by
  apply isEquivalent_of_tendsto_one
  have hdiv := veryBadOneTermCount_normalized_tendsto.div_const
    squarefreePSeriesConstant
  have hlimit : Tendsto (fun x : ℕ =>
      ((veryBadOneTermCount x : ℝ) / Real.sqrt x) /
        squarefreePSeriesConstant) atTop (𝓝 1) := by
    simpa [squarefreePSeriesConstant_pos.ne'] using hdiv
  refine hlimit.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hsqrt : Real.sqrt (x : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (by exact_mod_cast hx)).ne'
  change ((veryBadOneTermCount x : ℝ) / Real.sqrt x) /
      squarefreePSeriesConstant =
    (veryBadOneTermCount x : ℝ) /
      (squarefreePSeriesConstant * Real.sqrt x)
  field_simp [squarefreePSeriesConstant_pos.ne', hsqrt]

def PositiveNat := {n : ℕ // 0 < n}

def PositiveSquarefreeNat := {n : ℕ // 0 < n ∧ Squarefree n}

noncomputable def squarePart (n : PositiveNat) : ℕ :=
  Classical.choose (exists_sq_mul_squarefreeComponent n.property)

theorem squarePart_spec (n : PositiveNat) :
    squarePart n ^ 2 * squarefreeComponent n.1 = n.1 :=
  Classical.choose_spec (exists_sq_mul_squarefreeComponent n.property)

theorem squarePart_pos (n : PositiveNat) : 0 < squarePart n := by
  by_contra h
  have hz : squarePart n = 0 := Nat.eq_zero_of_not_pos h
  have hspec := squarePart_spec n
  rw [hz] at hspec
  simp at hspec
  exact n.property.ne' hspec.symm

theorem squarefreeComponent_pos_of_positive (n : PositiveNat) :
    0 < squarefreeComponent n.1 := by
  by_contra h
  have hz : squarefreeComponent n.1 = 0 := Nat.eq_zero_of_not_pos h
  have hspec := squarePart_spec n
  rw [hz] at hspec
  simp at hspec
  exact n.property.ne' hspec.symm

noncomputable def squareTimesSquarefreeEquiv :
    PositiveNat × PositiveSquarefreeNat ≃ PositiveNat where
  toFun ab := ⟨ab.1.1 ^ 2 * ab.2.1,
    mul_pos (pow_pos ab.1.2 2) ab.2.2.1⟩
  invFun n :=
    (⟨squarePart n, squarePart_pos n⟩,
      ⟨squarefreeComponent n.1, squarefreeComponent_pos_of_positive n,
        squarefree_squarefreeComponent n.1⟩)
  left_inv := by
    rintro ⟨a, b⟩
    have hn : 0 < a.1 ^ 2 * b.1 :=
      mul_pos (pow_pos a.2 2) b.2.1
    have hcomponent :
        squarefreeComponent (a.1 ^ 2 * b.1) = b.1 :=
      (eq_squarefreeComponent_of_sq_mul hn b.2.2 rfl).symm
    apply Prod.ext
    · apply Subtype.ext
      have hspec := squarePart_spec
        (⟨a.1 ^ 2 * b.1, hn⟩ : PositiveNat)
      change squarePart (⟨a.1 ^ 2 * b.1, hn⟩ : PositiveNat) = a.1
      apply Nat.pow_left_injective (by norm_num : 2 ≠ 0)
      apply Nat.mul_right_cancel b.2.1
      simpa [hcomponent] using hspec
    · apply Subtype.ext
      exact hcomponent
  right_inv := by
    intro n
    apply Subtype.ext
    exact squarePart_spec n

noncomputable def positiveNatRpow (p : ℝ) (n : PositiveNat) : ℝ :=
  (n.1 : ℝ) ^ p

noncomputable def positiveSquarefreeRpow (p : ℝ)
    (n : PositiveSquarefreeNat) : ℝ := (n.1 : ℝ) ^ p

theorem summable_positiveNatRpow {p : ℝ} (hp : p < -1) :
    Summable (positiveNatRpow p) := by
  exact (Real.summable_nat_rpow.mpr hp).subtype _

theorem summable_positiveSquarefreeRpow {p : ℝ} (hp : p < -1) :
    Summable (positiveSquarefreeRpow p) := by
  exact (Real.summable_nat_rpow.mpr hp).subtype _

theorem tsum_positiveNatRpow (p : ℝ) (hp : p ≠ 0) :
    ∑' n : PositiveNat, positiveNatRpow p n =
      ∑' n : ℕ, (n : ℝ) ^ p := by
  calc
    ∑' n : PositiveNat, positiveNatRpow p n =
        ∑' n : ℕ, (Set.Ioi (0 : ℕ)).indicator (fun n => (n : ℝ) ^ p) n := by
      exact tsum_subtype (Set.Ioi (0 : ℕ)) (fun n : ℕ => (n : ℝ) ^ p)
    _ = ∑' n : ℕ, (n : ℝ) ^ p := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · subst n
        simp [Set.indicator, Real.zero_rpow hp]
      · simp [Set.indicator, Nat.pos_of_ne_zero hn]

theorem tsum_positiveSquarefreeRpow_neg_three_halves :
    ∑' n : PositiveSquarefreeNat,
        positiveSquarefreeRpow (-(3 / 2 : ℝ)) n =
      squarefreePSeriesConstant := by
  let s : Set ℕ := {n : ℕ | 0 < n ∧ Squarefree n}
  calc
    ∑' n : PositiveSquarefreeNat,
        positiveSquarefreeRpow (-(3 / 2 : ℝ)) n =
        ∑' n : ℕ, s.indicator
          (fun n => (n : ℝ) ^ (-(3 / 2 : ℝ))) n := by
      exact tsum_subtype s (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ)))
    _ = squarefreePSeriesConstant := by
      rw [squarefreePSeriesConstant]
      apply tsum_congr
      intro n
      by_cases hn : 0 < n ∧ Squarefree n
      · have hnOne : 1 ≤ n := hn.1
        simp [s, Set.indicator, squarefreePSeriesSummand, hn, hnOne]
      · have hnOne : ¬(1 ≤ n ∧ Squarefree n) := by
          intro h
          exact hn ⟨h.1, h.2⟩
        simp [s, Set.indicator, squarefreePSeriesSummand, hn, hnOne]

theorem squareTimesSquarefree_rpow_identity
    (ab : PositiveNat × PositiveSquarefreeNat) :
    positiveNatRpow (-3 : ℝ) ab.1 *
        positiveSquarefreeRpow (-(3 / 2 : ℝ)) ab.2 =
      positiveNatRpow (-(3 / 2 : ℝ)) (squareTimesSquarefreeEquiv ab) := by
  change
    (ab.1.1 : ℝ) ^ (-3 : ℝ) * (ab.2.1 : ℝ) ^ (-(3 / 2 : ℝ)) =
      ((ab.1.1 ^ 2 * ab.2.1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  rw [Nat.cast_mul, Nat.cast_pow,
    Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem squarefreePSeries_product_identity :
    (∑' a : ℕ, (a : ℝ) ^ (-3 : ℝ)) * squarefreePSeriesConstant =
      ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have ha : Summable (positiveNatRpow (-3 : ℝ)) :=
    summable_positiveNatRpow (by norm_num)
  have hb : Summable
      (positiveSquarefreeRpow (-(3 / 2 : ℝ))) :=
    summable_positiveSquarefreeRpow (by norm_num)
  have hab : Summable (fun ab : PositiveNat × PositiveSquarefreeNat =>
      positiveNatRpow (-3 : ℝ) ab.1 *
        positiveSquarefreeRpow (-(3 / 2 : ℝ)) ab.2) :=
    ha.mul_of_nonneg hb
      (fun a => Real.rpow_nonneg (Nat.cast_nonneg a.1) _)
      (fun b => Real.rpow_nonneg (Nat.cast_nonneg b.1) _)
  have hmul := ha.tsum_mul_tsum hb hab
  have hreindex :
      (∑' ab : PositiveNat × PositiveSquarefreeNat,
          positiveNatRpow (-3 : ℝ) ab.1 *
            positiveSquarefreeRpow (-(3 / 2 : ℝ)) ab.2) =
        ∑' n : PositiveNat, positiveNatRpow (-(3 / 2 : ℝ)) n := by
    have hsum : HasSum
        (fun n : PositiveNat =>
          (fun ab : PositiveNat × PositiveSquarefreeNat =>
            positiveNatRpow (-3 : ℝ) ab.1 *
              positiveSquarefreeRpow (-(3 / 2 : ℝ)) ab.2)
            (squareTimesSquarefreeEquiv.symm n))
        (∑' ab : PositiveNat × PositiveSquarefreeNat,
          positiveNatRpow (-3 : ℝ) ab.1 *
            positiveSquarefreeRpow (-(3 / 2 : ℝ)) ab.2) :=
      (squareTimesSquarefreeEquiv.symm.hasSum_iff).2 hab.hasSum
    have hsum' : HasSum
        (positiveNatRpow (-(3 / 2 : ℝ)))
        (∑' ab : PositiveNat × PositiveSquarefreeNat,
          positiveNatRpow (-3 : ℝ) ab.1 *
            positiveSquarefreeRpow (-(3 / 2 : ℝ)) ab.2) := by
      apply hsum.congr_fun
      intro n
      symm
      simpa using squareTimesSquarefree_rpow_identity
        (squareTimesSquarefreeEquiv.symm n)
    exact hsum'.tsum_eq.symm
  rw [← tsum_positiveNatRpow (-3 : ℝ) (by norm_num),
    ← tsum_positiveSquarefreeRpow_neg_three_halves,
    hmul, hreindex, tsum_positiveNatRpow (-(3 / 2 : ℝ)) (by norm_num)]

theorem tsum_nat_rpow_neg_eq_riemannZeta_re (r : ℝ) (hr : 1 < r) :
    ∑' n : ℕ, (n : ℝ) ^ (-r) = (riemannZeta (r : ℂ)).re := by
  have hs : 1 < ((r : ℂ)).re := by simpa using hr
  have hsumC : HasSum
      (fun n : ℕ => riemannZetaSummandHom
        (Complex.ne_zero_of_one_lt_re hs) n)
      (riemannZeta (r : ℂ)) := by
    have h := (summable_riemannZetaSummand hs).of_norm.hasSum
    rw [tsum_riemannZetaSummand hs] at h
    exact h
  have hsumR := hsumC.map Complex.reCLM Complex.continuous_re
  have hsumR' : HasSum (fun n : ℕ => (n : ℝ) ^ (-r))
      (riemannZeta (r : ℂ)).re := by
    refine HasSum.congr_fun hsumR ?_
    intro n
    simp only [Function.comp_apply, riemannZetaSummandHom,
      MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    have hcpow := Complex.ofReal_cpow (Nat.cast_nonneg n) (-r)
    simpa using congrArg Complex.re hcpow
  exact hsumR'.tsum_eq

theorem squarefreePSeriesConstant_eq_powerfulNumberConstant :
    squarefreePSeriesConstant = powerfulNumberConstant := by
  have hProduct := squarefreePSeries_product_identity
  rw [tsum_nat_rpow_neg_eq_riemannZeta_re 3 (by norm_num),
    tsum_nat_rpow_neg_eq_riemannZeta_re (3 / 2) (by norm_num)] at hProduct
  have hden : 0 < (riemannZeta (3 : ℝ)).re :=
    riemannZeta_re_pos_of_one_lt (by norm_num)
  rw [powerfulNumberConstant]
  apply (eq_div_iff hden.ne').2
  simpa [mul_comm] using hProduct

theorem veryBadOneTermCount_asymptotic_powerfulNumberConstant :
    SequenceEquivalent
      (fun x : ℕ => (veryBadOneTermCount x : ℝ))
      (fun x : ℕ => powerfulNumberConstant * Real.sqrt x) := by
  rw [← squarefreePSeriesConstant_eq_powerfulNumberConstant]
  exact veryBadOneTermCount_asymptotic_squarefreePSeries

end Tao2026
