import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.ZetaZeros
import RiemannZeta.GuthMaynard.DyadicTransfer
import RiemannZeta.GuthMaynard.InghamBound
import RiemannZeta.GuthMaynard.ZeroCount

open Complex Finset Filter MeromorphicOn Topology
open scoped ArithmeticFunction.Moebius BigOperators

namespace RiemannZeta.GuthMaynard

/-- The finite Möbius mollifier used in the classical Ingham zero-density
argument. The lower endpoint excludes the junk value of `Nat`-indexed
Dirichlet monomials at zero. -/
noncomputable def zetaMollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 X,
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)

/-- The error in the finite Möbius approximation to the reciprocal of zeta. -/
noncomputable def mollifiedZetaError (X : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s * zetaMollifier X s - 1

/-- Dirichlet coefficient of `ζ(s) M_X(s)`: the Möbius sum over divisors not
exceeding the mollifier length. -/
noncomputable def mollifiedZetaCoeff (X n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ≤ X),
    ((ArithmeticFunction.moebius d : ℤ) : ℂ)

/-- Below the truncation length, Möbius inversion makes the coefficients of
`ζ(s) M_X(s)` equal to the Dirichlet identity. -/
theorem mollifiedZetaCoeff_eq_ite (X n : ℕ) (hn : 0 < n) (hnX : n ≤ X) :
    mollifiedZetaCoeff X n = if n = 1 then 1 else 0 := by
  have hFilter : n.divisors.filter (fun d => d ≤ X) = n.divisors := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)).trans hnX
  rw [mollifiedZetaCoeff, hFilter]
  calc
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) =
        ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          ArithmeticFunction.zeta) n := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      simp only [ArithmeticFunction.intCoe_apply]
    _ = (1 : ArithmeticFunction ℂ) n := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

/-- In particular, every nonconstant coefficient through `X` vanishes. -/
theorem mollifiedZetaCoeff_eq_zero (X n : ℕ) (hn : 1 < n) (hnX : n ≤ X) :
    mollifiedZetaCoeff X n = 0 := by
  rw [mollifiedZetaCoeff_eq_ite X n (by omega) hnX, if_neg (by omega)]

/-- The finite Möbius mollifier as an arithmetic function. -/
noncomputable def truncatedMoebius (X : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Icc 1 X then
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0
  map_zero' := by simp

@[simp] theorem truncatedMoebius_apply (X n : ℕ) :
    truncatedMoebius X n = if n ∈ Icc 1 X then
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0 := rfl

theorem truncatedMoebius_hasFiniteSupport (X : ℕ) :
    Function.HasFiniteSupport (truncatedMoebius X) := by
  apply Set.Finite.subset (Icc 1 X).finite_toSet
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  by_contra hnMem
  have hnMem' : n ∉ Icc 1 X := by simpa using hnMem
  exact hn (by rw [truncatedMoebius_apply, if_neg hnMem'])

theorem truncatedMoebius_LSeriesSummable (X : ℕ) (s : ℂ) :
    LSeriesSummable (truncatedMoebius X) s := by
  unfold LSeriesSummable
  exact summable_of_hasFiniteSupport <|
    (truncatedMoebius_hasFiniteSupport X).subset (by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn ⊢
      contrapose! hn
      rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
      simp [hn])

/-- The finite-sum definition of the mollifier agrees exactly with its
L-series representation. -/
theorem zetaMollifier_eq_LSeries (X : ℕ) (s : ℂ) :
    zetaMollifier X s = LSeries (truncatedMoebius X) s := by
  rw [zetaMollifier, LSeries, tsum_eq_sum (s := Icc 1 X)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
    simp only [truncatedMoebius_apply, if_pos hn]
  · intro n hn
    rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
    simp [hn]

/-- Multiplication by zeta produces the truncated divisor-sum coefficient. -/
theorem zeta_mul_truncatedMoebius_apply (X n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * truncatedMoebius X) n =
      mollifiedZetaCoeff X n := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  simp only [truncatedMoebius_apply, mollifiedZetaCoeff]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hd
    have hdData := Nat.mem_divisors.mp hd
    have hdNe : d ≠ 0 := ne_zero_of_dvd_ne_zero hdData.2 hdData.1
    simp [Nat.one_le_iff_ne_zero.mpr hdNe]
  · intro d hd
    simp only [Finset.mem_filter] at hd
    simp

/-- In the half-plane of absolute convergence, the analytic mollified zeta
product is the L-series with the truncated Möbius divisor coefficients. -/
theorem riemannZeta_mul_zetaMollifier_eq_LSeries (X : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    riemannZeta s * zetaMollifier X s = LSeries (mollifiedZetaCoeff X) s := by
  have hProd :
      LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        truncatedMoebius X) n) s =
      LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s *
        LSeries (fun n => truncatedMoebius X n) s :=
    ArithmeticFunction.LSeries_mul'
      (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
      (g := truncatedMoebius X) (s := s)
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
      (truncatedMoebius_LSeriesSummable X s)
  have hZeta :
      LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s =
        riemannZeta s := by
    simpa only [ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  calc
    riemannZeta s * zetaMollifier X s =
        LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s *
          LSeries (fun n => truncatedMoebius X n) s := by
      rw [hZeta, ← zetaMollifier_eq_LSeries]
    _ = LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        truncatedMoebius X) n) s := hProd.symm
    _ = LSeries (mollifiedZetaCoeff X) s :=
      LSeries_congr (fun {_n} _hn => zeta_mul_truncatedMoebius_apply X _n) s

/-- Dirichlet coefficient of the mollified zeta error `ζ M_X - 1`. -/
noncomputable def mollifiedZetaErrorCoeff (X n : ℕ) : ℂ :=
  mollifiedZetaCoeff X n - LSeries.delta n

/-- Every positive error coefficient through the truncation length is zero. -/
theorem mollifiedZetaErrorCoeff_eq_zero (X n : ℕ) (hn : 0 < n) (hnX : n ≤ X) :
    mollifiedZetaErrorCoeff X n = 0 := by
  rw [mollifiedZetaErrorCoeff, mollifiedZetaCoeff_eq_ite X n hn hnX]
  simp [LSeries.delta]

theorem LSeriesSummable_delta (s : ℂ) : LSeriesSummable LSeries.delta s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_singleton 1)
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn ⊢
  by_contra hnOne
  have hnOne' : n ≠ 1 := by simpa using hnOne
  exact hn (by rw [LSeries.term_delta, if_neg hnOne'])

theorem mollifiedZetaCoeff_LSeriesSummable (X : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mollifiedZetaCoeff X) s := by
  have hMul := ArithmeticFunction.LSeriesSummable_mul
    (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := truncatedMoebius X) (s := s)
    (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
    (truncatedMoebius_LSeriesSummable X s)
  exact (LSeriesSummable_congr s
    (fun {_n} _hn => zeta_mul_truncatedMoebius_apply X _n)).mp hMul

/-- In the half-plane of absolute convergence, the mollified zeta error is
the L-series whose first `X` positive coefficients vanish. -/
theorem mollifiedZetaError_eq_LSeries (X : ℕ) {s : ℂ} (hs : 1 < s.re) :
    mollifiedZetaError X s = LSeries (mollifiedZetaErrorCoeff X) s := by
  have hCoeff := mollifiedZetaCoeff_LSeriesSummable X hs
  have hDelta := LSeriesSummable_delta s
  have hDeltaValue : LSeries LSeries.delta s = 1 := by
    simpa using congrFun LSeries_delta s
  calc
    mollifiedZetaError X s = LSeries (mollifiedZetaCoeff X) s - 1 := by
      rw [mollifiedZetaError, riemannZeta_mul_zetaMollifier_eq_LSeries X hs]
    _ = LSeries (mollifiedZetaCoeff X) s - LSeries LSeries.delta s := by
      rw [hDeltaValue]
    _ = LSeries (mollifiedZetaCoeff X - LSeries.delta) s :=
      (LSeries_sub hCoeff hDelta).symm
    _ = LSeries (mollifiedZetaErrorCoeff X) s := by
      apply LSeries_congr
      intro n _hn
      rfl

/-- Ingham's zero-containing auxiliary function
`1 - (ζ M_X - 1)^2 = (2 - ζ M_X) ζ M_X`.  The factored definition makes the
zeta-zero multiplicity transparent. -/
noncomputable def inghamZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  (2 - riemannZeta s * zetaMollifier X s) *
    (riemannZeta s * zetaMollifier X s)

/-- A pole-free version of Ingham's detector. Away from `s = 1` this is
`(s - 1)^2 * inghamZeroDetector X s`. -/
noncomputable def regularizedInghamZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  (2 * (s - 1) - regularizedRiemannZeta s * zetaMollifier X s) *
    (regularizedRiemannZeta s * zetaMollifier X s)

lemma inghamZeroDetector_eq_one_sub_sq (X : ℕ) (s : ℂ) :
    inghamZeroDetector X s = 1 - mollifiedZetaError X s ^ 2 := by
  simp only [inghamZeroDetector, mollifiedZetaError]
  ring

lemma regularizedInghamZeroDetector_of_ne (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    regularizedInghamZeroDetector X s =
      (s - 1) ^ 2 * inghamZeroDetector X s := by
  rw [regularizedInghamZeroDetector, regularizedRiemannZeta,
    Function.update_of_ne hs, inghamZeroDetector]
  ring

lemma analyticAt_zetaMollifier (X : ℕ) (s : ℂ) :
    AnalyticAt ℂ (zetaMollifier X) s := by
  unfold zetaMollifier
  have h : AnalyticAt ℂ
      (∑ n ∈ Icc 1 X, fun z : ℂ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-z)) s := by
    apply Finset.analyticAt_sum
    intro n hn
    have hnPos : 0 < n := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    have hpow : AnalyticAt ℂ (fun z : ℂ => (n : ℂ) ^ (-z)) s :=
      analyticAt_const.cpow analyticAt_id.neg
        (Complex.natCast_mem_slitPlane.mpr (Nat.ne_of_gt hnPos))
    exact analyticAt_const.mul hpow
  have heq :
      (fun z : ℂ => ∑ n ∈ Icc 1 X,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-z)) =
      ∑ n ∈ Icc 1 X, fun z : ℂ =>
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-z) := by
    funext z
    simp
  rw [heq]
  exact h

theorem analytic_regularizedInghamZeroDetector (X : ℕ) :
    ∀ s, AnalyticAt ℂ (regularizedInghamZeroDetector X) s := by
  intro s
  unfold regularizedInghamZeroDetector
  have hz : AnalyticAt ℂ regularizedRiemannZeta s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    exact Eventually.of_forall differentiableAt_regularizedRiemannZeta
  have hm : AnalyticAt ℂ (zetaMollifier X) s := analyticAt_zetaMollifier X s
  have hprod := hz.mul hm
  exact ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).sub hprod).mul hprod

lemma tendsto_natCast_cpow_neg_ofReal_atTop (n : ℕ) (hn : 1 < n) :
    Filter.Tendsto (fun t : ℝ => (n : ℂ) ^ (-(t : ℂ))) Filter.atTop (𝓝 0) := by
  have hr : Filter.Tendsto (fun u : ℝ => (n : ℝ) ^ u) Filter.atBot (𝓝 0) :=
    tendsto_rpow_atBot_of_base_gt_one (n : ℝ) (by exact_mod_cast hn)
  have hrneg : Filter.Tendsto (fun t : ℝ => (n : ℝ) ^ (-t)) Filter.atTop (𝓝 0) :=
    hr.comp tendsto_neg_atTop_atBot
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hrneg
  convert hc using 1
  funext t
  change (n : ℂ) ^ (-(t : ℂ)) = (((n : ℝ) ^ (-t) : ℝ) : ℂ)
  simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-t)).symm

/-- Along the positive real axis, the finite Möbius mollifier tends to its
leading term `1`. This supplies a concrete witness that it is not the zero
analytic function. -/
theorem tendsto_zetaMollifier_ofReal_atTop (X : ℕ) (hX : 1 ≤ X) :
    Filter.Tendsto (fun t : ℝ => zetaMollifier X (t : ℂ)) Filter.atTop (𝓝 1) := by
  unfold zetaMollifier
  have hterm : ∀ n ∈ Icc 1 X,
      Filter.Tendsto
        (fun t : ℝ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
          (n : ℂ) ^ (-(t : ℂ))) Filter.atTop
        (𝓝 (if n = 1 then 1 else 0)) := by
    intro n hn
    by_cases hnOne : n = 1
    · subst n
      simp
    · have hnLt : 1 < n := lt_of_le_of_ne (Finset.mem_Icc.mp hn).1 (Ne.symm hnOne)
      have hpow := tendsto_natCast_cpow_neg_ofReal_atTop n hnLt
      have hmul := hpow.const_mul (((ArithmeticFunction.moebius n : ℤ) : ℂ))
      simpa [hnOne] using hmul
  have hsum := tendsto_finsetSum (Icc 1 X) hterm
  simpa [hX] using hsum

lemma exists_zetaMollifier_ofReal_ne_zero (X : ℕ) (hX : 1 ≤ X) :
    ∃ t : ℝ, zetaMollifier X (t : ℂ) ≠ 0 := by
  have hlim := tendsto_zetaMollifier_ofReal_atTop X hX
  have hnhds : ({0}ᶜ : Set ℂ) ∈ 𝓝 (1 : ℂ) :=
    isOpen_compl_singleton.mem_nhds (by simp)
  have heventually : ∀ᶠ t : ℝ in Filter.atTop,
      zetaMollifier X (t : ℂ) ∈ ({0}ᶜ : Set ℂ) := hlim.eventually hnhds
  obtain ⟨t, ht⟩ := heventually.exists
  exact ⟨t, by simpa using ht⟩

/-- For a nonempty mollifier, its analytic order is finite at every complex
point. The proof uses its limit to `1` to rule out the identically-zero case. -/
theorem zetaMollifier_analyticOrderAt_ne_top (X : ℕ) (hX : 1 ≤ X) (s : ℂ) :
    analyticOrderAt (zetaMollifier X) s ≠ ⊤ := by
  obtain ⟨t, ht⟩ := exists_zetaMollifier_ofReal_ne_zero X hX
  have hAnalytic : AnalyticOnNhd ℂ (zetaMollifier X) Set.univ := by
    intro z _
    exact analyticAt_zetaMollifier X z
  have htOrder : analyticOrderAt (zetaMollifier X) (t : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr ht)
  apply hAnalytic.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := (t : ℂ)) (y := s)
  · simp
  · simp
  · rw [htOrder]
    simp

lemma analyticAt_mollifiedZetaError (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (mollifiedZetaError X) s := by
  unfold mollifiedZetaError
  have hz : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs)
  exact (hz.mul (analyticAt_zetaMollifier X s)).sub analyticAt_const

lemma analyticAt_inghamZeroDetector (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ (inghamZeroDetector X) s := by
  unfold inghamZeroDetector
  have hz : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs)
  have hprod := hz.mul (analyticAt_zetaMollifier X s)
  exact (analyticAt_const.sub hprod).mul hprod

/-- Zeta has finite analytic order at every point away from its pole. -/
theorem riemannZeta_analyticOrderAt_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have htwoNe : riemannZeta (2 : ℂ) ≠ 0 := by
    rw [riemannZeta_two]
    exact_mod_cast div_ne_zero (pow_ne_zero 2 Real.pi_ne_zero) (by norm_num : (6 : ℝ) ≠ 0)
  have htwoOrder : analyticOrderAt riemannZeta (2 : ℂ) = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr htwoNe)
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (x := (2 : ℂ)) (y := s)
  · norm_num
  · simpa using hs
  · rw [htwoOrder]
    simp

lemma inghamZeroDetector_eq_zero_of_zeta_eq_zero (X : ℕ) {s : ℂ}
    (hs : riemannZeta s = 0) :
    inghamZeroDetector X s = 0 := by
  simp [inghamZeroDetector, hs]

/-- Every zeta zero away from the pole occurs in Ingham's auxiliary function
with at least its zeta multiplicity. -/
theorem analyticVanishingOrder_zeta_le_inghamZeroDetector (X : ℕ) {s : ℂ}
    (hX : 1 ≤ X) (hsPole : s ≠ 1) (hsZero : riemannZeta s = 0) :
    analyticVanishingOrder riemannZeta s ≤
      analyticVanishingOrder (inghamZeroDetector X) s := by
  let p : ℂ → ℂ := fun z => riemannZeta z * zetaMollifier X z
  let q : ℂ → ℂ := fun z => 2 - p z
  have hz : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hsPole)
  have hzFinite : analyticOrderAt riemannZeta s ≠ ⊤ :=
    riemannZeta_analyticOrderAt_ne_top hsPole
  have hm : AnalyticAt ℂ (zetaMollifier X) s := analyticAt_zetaMollifier X s
  have hmFinite : analyticOrderAt (zetaMollifier X) s ≠ ⊤ :=
    zetaMollifier_analyticOrderAt_ne_top X hX s
  have hp : AnalyticAt ℂ p s := hz.mul hm
  have hq : AnalyticAt ℂ q s := analyticAt_const.sub hp
  have hpZero : p s = 0 := by simp [p, hsZero]
  have hqNe : q s ≠ 0 := by simp [q, hpZero]
  have hqOrder : analyticOrderNatAt q s = 0 := by
    have hqOrder' : analyticOrderAt q s = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hqNe)
    simp [analyticOrderNatAt, hqOrder']
  have hqFinite : analyticOrderAt q s ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hqNe)]
    simp
  have hpFinite : analyticOrderAt p s ≠ ⊤ := by
    rw [show analyticOrderAt p s =
      analyticOrderAt riemannZeta s + analyticOrderAt (zetaMollifier X) s by
        simpa [p] using analyticOrderAt_mul hz hm]
    apply ENat.ne_top_iff_exists.mpr
    obtain ⟨m, hmOrder⟩ := ENat.ne_top_iff_exists.mp hzFinite
    obtain ⟨n, hnOrder⟩ := ENat.ne_top_iff_exists.mp hmFinite
    refine ⟨m + n, ?_⟩
    rw [← hmOrder, ← hnOrder]
    simp
  have hpOrder : analyticOrderNatAt p s =
      analyticOrderNatAt riemannZeta s + analyticOrderNatAt (zetaMollifier X) s := by
    simpa [p] using analyticOrderNatAt_mul hz hm hzFinite hmFinite
  have hdetOrder : analyticOrderNatAt (inghamZeroDetector X) s =
      analyticOrderNatAt q s + analyticOrderNatAt p s := by
    have hfun : inghamZeroDetector X = q * p := by
      funext z
      rfl
    rw [hfun]
    exact analyticOrderNatAt_mul hq hp hqFinite hpFinite
  unfold analyticVanishingOrder
  rw [hdetOrder, hqOrder, zero_add, hpOrder]
  exact Nat.le_add_right _ _

/-- Away from the pole, multiplying Ingham's detector by its pole-clearing
factor does not change its vanishing order. -/
theorem analyticVanishingOrder_regularizedInghamZeroDetector_eq (X : ℕ) {s : ℂ}
    (hsPole : s ≠ 1) :
    analyticVanishingOrder (regularizedInghamZeroDetector X) s =
      analyticVanishingOrder (inghamZeroDetector X) s := by
  let q : ℂ → ℂ := fun z => (z - 1) ^ 2
  have hq : AnalyticAt ℂ q s := by
    exact (analyticAt_id.sub analyticAt_const).pow 2
  have hqNe : q s ≠ 0 := by
    exact pow_ne_zero 2 (sub_ne_zero.mpr hsPole)
  have hdet : AnalyticAt ℂ (inghamZeroDetector X) s :=
    analyticAt_inghamZeroDetector X hsPole
  have heq : regularizedInghamZeroDetector X =ᶠ[𝓝 s]
      q * inghamZeroDetector X := by
    filter_upwards [eventually_ne_nhds hsPole] with z hz
    simpa [q] using regularizedInghamZeroDetector_of_ne X hz
  unfold analyticVanishingOrder analyticOrderNatAt
  congr 1
  calc
    analyticOrderAt (regularizedInghamZeroDetector X) s =
        analyticOrderAt (q * inghamZeroDetector X) s := analyticOrderAt_congr heq
    _ = analyticOrderAt q s + analyticOrderAt (inghamZeroDetector X) s :=
      analyticOrderAt_mul hq hdet
    _ = analyticOrderAt (inghamZeroDetector X) s := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hqNe)]
      simp

/-- Every zeta zero away from the pole occurs in the globally analytic,
pole-free Ingham detector with at least its zeta multiplicity. -/
theorem analyticVanishingOrder_zeta_le_regularizedInghamZeroDetector
    (X : ℕ) {s : ℂ} (hX : 1 ≤ X) (hsPole : s ≠ 1)
    (hsZero : riemannZeta s = 0) :
    analyticVanishingOrder riemannZeta s ≤
      analyticVanishingOrder (regularizedInghamZeroDetector X) s := by
  rw [analyticVanishingOrder_regularizedInghamZeroDetector_eq X hsPole]
  exact analyticVanishingOrder_zeta_le_inghamZeroDetector X hX hsPole hsZero

/-- A finite family of zeta zeros contributes no more total multiplicity than
the same family does to the pole-free Ingham detector. -/
theorem sum_zeta_multiplicity_le_regularizedInghamZeroDetector
    (X : ℕ) (hX : 1 ≤ X) (S : Finset ℂ)
    (hZeros : ∀ s ∈ S, riemannZeta s = 0) :
    ∑ s ∈ S, analyticVanishingOrder riemannZeta s ≤
      ∑ s ∈ S, analyticVanishingOrder (regularizedInghamZeroDetector X) s := by
  apply Finset.sum_le_sum
  intro s hs
  exact analyticVanishingOrder_zeta_le_regularizedInghamZeroDetector X hX
    (fun hsOne => riemannZeta_one_ne_zero (hsOne ▸ hZeros s hs)) (hZeros s hs)

/-- Jensen's inequality applied to the entire Ingham detector, with the zeta
zero multiplicities inserted through the detector divisibility theorem. This
is the quantitative disk-counting interface used by the classical density
argument. -/
theorem sum_zeta_multiplicity_le_of_regularizedInghamZeroDetector_bound
    (X : ℕ) (hX : 1 ≤ X) (S : Finset ℂ) (c : ℂ) (r R M : ℝ)
    (hr : 0 < |r|) (hrR : |r| < |R|) (hM : 1 ≤ M)
    (hc : regularizedInghamZeroDetector X c ≠ 0)
    (hSphere : ∀ z ∈ Metric.sphere c |R|,
      ‖regularizedInghamZeroDetector X z‖ ≤ M)
    (hZeros : ∀ s ∈ S, riemannZeta s = 0)
    (hS : ∀ s ∈ S, s ∈ Metric.closedBall c |r|) :
    ((∑ s ∈ S, analyticVanishingOrder riemannZeta s : ℕ) : ℝ) ≤
      Real.log (M / ‖regularizedInghamZeroDetector X c‖) /
        Real.log (R / r) := by
  let f : ℂ → ℂ := regularizedInghamZeroDetector X
  have hfAll : AnalyticOnNhd ℂ f Set.univ := by
    intro z _
    exact analytic_regularizedInghamZeroDetector X z
  have hfSmall : AnalyticOnNhd ℂ f (Metric.closedBall c |r|) :=
    hfAll.mono (Set.subset_univ _)
  have hfLarge : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) :=
    hfAll.mono (Set.subset_univ _)
  have hcOrder : analyticOrderAt f c ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hc)]
    exact ENat.coe_ne_top 0
  have hBridge := finset_analyticVanishingOrder_le_finsum_divisor hfSmall
    (isCompact_closedBall c |r|) (convex_closedBall c |r|).isPreconnected
    (by simp) hcOrder S hS
  have hJensen := hfLarge.sum_divisor_le hr hrR hM hc hSphere
  have hMultiplicity :=
    sum_zeta_multiplicity_le_regularizedInghamZeroDetector X hX S hZeros
  calc
    ((∑ s ∈ S, analyticVanishingOrder riemannZeta s : ℕ) : ℝ) ≤
        ((∑ s ∈ S, analyticVanishingOrder f s : ℕ) : ℝ) := by
      exact_mod_cast hMultiplicity
    _ ≤ ((∑ᶠ u, divisor f (Metric.closedBall c |r|) u : ℤ) : ℝ) := hBridge
    _ ≤ Real.log (M / ‖regularizedInghamZeroDetector X c‖) /
        Real.log (R / r) := by simpa [f] using hJensen

/-- There are no zeta zeros in a rectangle whose real interval is the
singleton `{1}`. -/
theorem zerosInRect_one_eq_empty (T₁ T₂ : ℝ) :
    zerosInRect 1 1 T₁ T₂ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff] at hs
  rcases hs with ⟨hsRect, hsZero⟩
  rw [mem_ZeroRectangle] at hsRect
  exact riemannZeta_ne_zero_of_one_le_re hsRect.1 hsZero

/-- The symmetric zeta-zero count vanishes identically at `σ = 1`. -/
@[simp] theorem N_one (T : ℝ) : N 1 T = 0 := by
  rw [N, zeroCountRect, zerosInRect_one_eq_empty]
  simp

/-- An identically zero counting function satisfies every epsilon-power
upper bound. -/
theorem epsilonPowerBound_zero (g : ℝ → ℝ) :
    EpsilonPowerBound (fun _T : ℝ => 0) g := by
  intro ε _hε
  simpa using
    (Asymptotics.isBigO_zero (fun T : ℝ => T ^ ε * |g T|) Filter.atTop :
      (fun _T : ℝ => (0 : ℝ)) =O[Filter.atTop]
        (fun T : ℝ => T ^ ε * |g T|))

/-- The `σ = 1` endpoint required by Ingham's density theorem. -/
theorem ingham_zero_density_at_one_native :
    EpsilonPowerBound (fun T => (N 1 T : ℝ))
      (fun T => T ^ (3 * (1 - (1 : ℝ)) / (2 - 1))) := by
  simpa only [N_one, Nat.cast_zero] using
    (epsilonPowerBound_zero
      (fun T => T ^ (3 * (1 - (1 : ℝ)) / (2 - 1))))

/-- The `σ = 1` endpoint required by Huxley's density theorem. -/
theorem huxley_zero_density_at_one_native :
    EpsilonPowerBound (fun T => (N 1 T : ℝ))
      (fun T => T ^ (3 * (1 - (1 : ℝ)) / (3 * 1 - 1))) := by
  simpa only [N_one, Nat.cast_zero] using
    (epsilonPowerBound_zero
      (fun T => T ^ (3 * (1 - (1 : ℝ)) / (3 * 1 - 1))))

/-- All zeta zeros in one unit-height bin of a positive dyadic slab. -/
noncomputable def zeroUnitBin (σ T : ℝ) (z : ℤ) : Finset ℂ :=
  (zerosInRect σ 1 T (2 * T)).filter
    (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1)

/-- A pole-safe Jensen estimate for every zero in a unit-height bin. Unlike
`typeI_unit_bin_sum_le_jensen`, this theorem has no detector-class filter and
is valid down to the critical line. -/
theorem zeroUnitBin_multiplicity_le_jensen (σ T : ℝ) (z : ℤ)
    (hσLower : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ zeroUnitBin σ T z,
        analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
  let S := zeroUnitBin σ T z
  by_cases hSEmpty : S = ∅
  · change ((∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤ _
    rw [hSEmpty]
    simp only [Finset.sum_empty, Nat.cast_zero]
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hRatio : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
      norm_num at hM ⊢
      nlinarith
    exact div_nonneg (Real.log_nonneg hRatio) hLogDen.le
  · have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    obtain ⟨ρ₀, hρ₀⟩ := hSNonempty
    have hρ₀Data := Finset.mem_filter.mp hρ₀
    have hρ₀Rect : ρ₀ ∈ zerosInRect σ 1 T (2 * T) := hρ₀Data.1
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hρ₀Rect
    have hzRange : (z : ℝ) ∈ Set.Icc (T - 1) (2 * T) := by
      constructor
      · linarith [hρ₀Rect.1.2.2.1, hρ₀Data.2.2]
      · linarith [hρ₀Rect.1.2.2.2, hρ₀Data.2.1]
    let c : ℂ := 2 + I * (((z : ℝ) + 1 / 2 : ℝ) : ℂ)
    let U : Set ℂ := Metric.closedBall c (7 / 4 : ℝ)
    have hUAnalytic : AnalyticOnNhd ℂ riemannZeta U := by
      apply analyticOn_riemannZeta.mono
      intro w hw
      have hwNorm : ‖w - c‖ ≤ 7 / 4 := by
        simpa [U, Metric.mem_closedBall, dist_eq_norm] using hw
      have hwImDiff : |w.im - ((z : ℝ) + 1 / 2)| ≤ 7 / 4 := by
        calc
          |w.im - ((z : ℝ) + 1 / 2)| = |(w - c).im| := by simp [c]
          _ ≤ ‖w - c‖ := abs_im_le_norm _
          _ ≤ 7 / 4 := hwNorm
      have hwIm : 1 < w.im := by
        have := (abs_le.mp hwImDiff).1
        linarith [hzRange.1]
      intro hwOne
      subst w
      norm_num at hwIm
    have hcLower : (0.6 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa [c] using euler_product_lower_bound_2 (z : ℝ)
    have hcNe : riemannZeta c ≠ 0 := by
      intro hcZero
      rw [hcZero, norm_zero] at hcLower
      norm_num at hcLower
    have hcOrder : analyticOrderAt riemannZeta c ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hcNe)]
      exact ENat.coe_ne_top 0
    have hSU : ∀ ρ ∈ S, ρ ∈ Metric.closedBall c (8 / 5 : ℝ) := by
      intro ρ hρ
      have hρData := Finset.mem_filter.mp hρ
      have hρRect : ρ ∈ zerosInRect σ 1 T (2 * T) := hρData.1
      rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
        mem_ZeroRectangle] at hρRect
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hreLower : -(3 / 2 : ℝ) ≤ (ρ - c).re := by
        norm_num [c]
        linarith [hσLower, hρRect.1.1]
      have hreUpper : (ρ - c).re ≤ -1 := by
        norm_num [c]
        linarith [hρRect.1.2.1]
      have himLower : -(1 / 2 : ℝ) ≤ (ρ - c).im := by
        norm_num [c]
        linarith [hρData.2.1]
      have himUpper : (ρ - c).im ≤ 1 / 2 := by
        norm_num [c]
        linarith [hρData.2.2]
      rw [mul_self_le_mul_self_iff (norm_nonneg _) (by norm_num)]
      rw [Complex.norm_mul_self_eq_normSq, normSq_apply]
      nlinarith [sq_nonneg ((ρ - c).re + 3 / 2),
        sq_nonneg ((ρ - c).im + 1 / 2),
        sq_nonneg ((ρ - c).im - 1 / 2)]
    let V : Set ℂ := Metric.closedBall c (8 / 5 : ℝ)
    have hVAnalytic : AnalyticOnNhd ℂ riemannZeta V :=
      hUAnalytic.mono
        (Metric.closedBall_subset_closedBall (by norm_num : (8 / 5 : ℝ) ≤ 7 / 4))
    have hBridge := finset_analyticVanishingOrder_le_finsum_divisor hVAnalytic
      (isCompact_closedBall c (8 / 5 : ℝ))
      (convex_closedBall c (8 / 5 : ℝ)).isPreconnected (by
        simp only [V, Metric.mem_closedBall, dist_self]
        norm_num) hcOrder S
      (by simpa [V] using hSU)
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hUAnalyticAbs : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall c |(7 / 4 : ℝ)|) := by
      simpa [U, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hUAnalytic
    have hJensen := hUAnalyticAbs.sum_divisor_le
      (r := (8 / 5 : ℝ)) (R := (7 / 4 : ℝ))
      (M := 100 * T ^ (3 : ℝ)) (by norm_num) (by norm_num) hM hcNe (by
        intro w hw
        exact zeta_jensen_sphere_bound T (z : ℝ) hT hzRange w (by
          simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hw))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)] at hJensen
    change ((∑ ρ ∈ S, analyticVanishingOrder riemannZeta ρ : ℕ) : ℝ) ≤ _
    refine hBridge.trans (le_trans (by simpa [c, V] using hJensen) ?_)
    have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
      apply Real.log_pos
      norm_num
    apply div_le_div_of_nonneg_right _ hLogDen.le
    have hMPos : 0 < 100 * T ^ (3 : ℕ) := by positivity
    have hcNormPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcNe
    have hRatioLe : (100 * T ^ (3 : ℕ)) / ‖riemannZeta c‖ ≤
        (100 * T ^ (3 : ℕ)) / (0.6 : ℝ) :=
      div_le_div_of_nonneg_left hMPos.le (by norm_num) hcLower
    exact Real.log_le_log
      (div_pos hMPos (by simpa [c] using hcNormPos)) (by simpa [c] using hRatioLe)

/-- Summing the unit-bin Jensen estimate gives an explicit bound for a full
positive dyadic slab. -/
theorem zeroCountRect_dyadic_le_jensen (σ T : ℝ)
    (hσLower : 1 / 2 ≤ σ) (hT : 8 ≤ T) :
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (T + 2) *
        (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by
  let S := zerosInRect σ 1 T (2 * T)
  let bins : Finset ℤ := Finset.Icc ⌊T⌋ ⌊2 * T⌋
  let floorIm : ℂ → ℤ := fun ρ => ⌊ρ.im⌋
  let mult : ℂ → ℕ := fun ρ => analyticVanishingOrder riemannZeta ρ
  have hFloorMem : ∀ ρ ∈ S, floorIm ρ ∈ bins := by
    intro ρ hρ
    change ρ ∈ zerosInRect σ 1 T (2 * T) at hρ
    rw [zerosInRect, Set.Finite.mem_toFinset, Set.mem_inter_iff,
      mem_ZeroRectangle] at hρ
    change floorIm ρ ∈ Finset.Icc ⌊T⌋ ⌊2 * T⌋
    rw [Finset.mem_Icc]
    exact ⟨Int.floor_mono hρ.1.2.2.1, Int.floor_mono hρ.1.2.2.2⟩
  have hAll : S.filter (fun ρ => floorIm ρ ∈ bins) = S :=
    Finset.filter_eq_self.mpr hFloorMem
  have hFiber := Finset.sum_fiberwise_eq_sum_filter S bins floorIm mult
  rw [hAll] at hFiber
  have hEach : ∀ z ∈ bins,
      ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
        Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    intro z _hz
    have hSubset : S.filter (fun w => floorIm w = z) ⊆ zeroUnitBin σ T z := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rw [zeroUnitBin, Finset.mem_filter]
      refine ⟨by simpa [S] using hρ.1, ?_⟩
      have hFloorLe : ((⌊ρ.im⌋ : ℤ) : ℝ) ≤ ρ.im := Int.floor_le ρ.im
      have hLtFloor : ρ.im < ((⌊ρ.im⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one ρ.im
      change (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1
      simpa [floorIm, hρ.2] using And.intro hFloorLe hLtFloor
    have hNat :
        ∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ ≤
          ∑ ρ ∈ zeroUnitBin σ T z, mult ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSubset
      intro _ _ _
      exact Nat.zero_le _
    have hNatReal :
        ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ zeroUnitBin σ T z, mult ρ : ℕ) : ℝ) := by
      exact_mod_cast hNat
    exact hNatReal.trans (by
      simpa [mult] using zeroUnitBin_multiplicity_le_jensen σ T z hσLower hT)
  have hSum :
      ∑ z ∈ bins,
          ((∑ ρ ∈ S.filter (fun w => floorIm w = z), mult ρ : ℕ) : ℝ) ≤
        ∑ _z ∈ bins,
          Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    exact Finset.sum_le_sum hEach
  have hFiberReal := congrArg (fun n : ℕ => (n : ℝ)) hFiber
  simp only [Nat.cast_sum] at hFiberReal
  have hTotal : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      (bins.card : ℝ) *
        (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
          Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by
    rw [zeroCountRect]
    change ((∑ ρ ∈ S, mult ρ : ℕ) : ℝ) ≤ _
    calc
      ((∑ ρ ∈ S, mult ρ : ℕ) : ℝ) =
          ∑ ρ ∈ S, (mult ρ : ℝ) := by simp
      _ = ∑ z ∈ bins, ∑ ρ ∈ S.filter (fun w => floorIm w = z),
          (mult ρ : ℝ) := hFiberReal.symm
      _ ≤ ∑ _z ∈ bins,
          Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
        simpa only [Nat.cast_sum] using hSum
      _ = (bins.card : ℝ) *
          (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
            Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))) := by simp
  have hab : ⌊T⌋ ≤ ⌊2 * T⌋ + 1 := by
    have hmono : ⌊T⌋ ≤ ⌊2 * T⌋ := Int.floor_mono (by linarith)
    omega
  have hCardInt : (bins.card : ℤ) = ⌊2 * T⌋ + 1 - ⌊T⌋ := by
    simpa [bins] using Int.card_Icc_of_le ⌊T⌋ ⌊2 * T⌋ hab
  have hCardReal : (bins.card : ℝ) =
      (⌊2 * T⌋ : ℝ) + 1 - (⌊T⌋ : ℝ) := by
    exact_mod_cast hCardInt
  have hCard : (bins.card : ℝ) ≤ T + 2 := by
    rw [hCardReal]
    have hUpper : (⌊2 * T⌋ : ℝ) ≤ 2 * T := Int.floor_le (2 * T)
    have hLower : T - 1 < (⌊T⌋ : ℝ) := Int.sub_one_lt_floor T
    linarith
  have hLogDen : 0 < Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) := by
    apply Real.log_pos
    norm_num
  have hM : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
    have hTPos : 0 < T := by linarith
    have : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      nlinarith [sq_nonneg T]
    norm_num at this ⊢
    nlinarith
  have hJNonneg : 0 ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
    div_nonneg (Real.log_nonneg hM) hLogDen.le
  exact hTotal.trans (mul_le_mul_of_nonneg_right hCard hJNonneg)

/-- The full positive dyadic zeta-zero count is `T^(1+ε)`-bounded uniformly
for every fixed vertical line at or to the right of the critical line. -/
theorem dyadic_zero_count_epsilon_one (σ : ℝ) (hσLower : 1 / 2 ≤ σ) :
    EpsilonPowerBound
      (fun T => (zeroCountRect σ 1 T (2 * T) : ℝ))
      (fun T => T ^ (1 : ℝ)) := by
  intro ε hε
  let D : ℝ := Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ))
  let C : ℝ := 125 / (D * ε)
  have hD : 0 < D := by
    dsimp [D]
    apply Real.log_pos
    norm_num
  have hC : 0 < C := div_pos (by norm_num) (mul_pos hD hε)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [Filter.eventually_ge_atTop (max (Real.exp 2) 8)] with T hT
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hT
  have hTExp : Real.exp 2 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTNonneg : 0 ≤ T := hTPos.le
  have hLogTwo : 2 ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos 2) hTExp
    simpa using this
  have hNumerator :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) ≤ 100 * Real.log T := by
    have hConst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500 / 3 by norm_num)
    calc
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) =
          Real.log ((500 / 3 : ℝ) * T ^ (3 : ℝ)) := by
        congr 1
        ring
      _ = Real.log (500 / 3 : ℝ) + Real.log (T ^ (3 : ℝ)) := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTPos 3).ne']
      _ = Real.log (500 / 3 : ℝ) + 3 * Real.log T := by
        rw [Real.log_rpow hTPos]
      _ ≤ 100 * Real.log T := by nlinarith
  have hJensenBound :
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) / D ≤
        100 * Real.log T / D :=
    div_le_div_of_nonneg_right hNumerator hD.le
  have hLogPow : Real.log T ≤ T ^ ε / ε :=
    Real.log_le_rpow_div hTNonneg hε
  have hRaw := zeroCountRect_dyadic_le_jensen σ T hσLower hTEight
  have hCount : (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
      C * (T ^ ε * T) := by
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          (T + 2) *
            (Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) / D) := by
        simpa [D] using hRaw
      _ ≤ (T + 2) * (100 * Real.log T / D) := by
        exact mul_le_mul_of_nonneg_left hJensenBound (by linarith)
      _ ≤ ((5 / 4 : ℝ) * T) * (100 * (T ^ ε / ε) / D) := by
        gcongr
        · linarith
      _ = C * (T ^ ε * T) := by
        dsimp [C]
        field_simp [hD.ne', hε.ne']
        ring
  calc
    ‖|(zeroCountRect σ 1 T (2 * T) : ℝ)|‖ =
        (zeroCountRect σ 1 T (2 * T) : ℝ) := by
      simp
    _ ≤ C * (T ^ ε * T) := hCount
    _ = C * ‖T ^ ε * |T ^ (1 : ℝ)|‖ := by
      rw [Real.rpow_one, abs_of_nonneg hTNonneg, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hTNonneg ε) hTNonneg)]

/-- The coarse exponent-one estimate for the full symmetric count, obtained
from the dyadic Jensen bound. -/
theorem global_zero_count_epsilon_one (σ : ℝ) (hσLower : 1 / 2 ≤ σ) :
    EpsilonPowerBound (fun T => (N σ T : ℝ)) (fun T => T ^ (1 : ℝ)) :=
  dyadicToGlobalZeroCount σ 1 (by norm_num) (dyadic_zero_count_epsilon_one σ hσLower)

/-- The `σ = 1/2` endpoint required by Ingham's density theorem. -/
theorem ingham_zero_density_at_half_native :
    EpsilonPowerBound (fun T => (N (1 / 2) T : ℝ))
      (fun T => T ^ (3 * (1 - (1 / 2 : ℝ)) / (2 - 1 / 2))) := by
  convert global_zero_count_epsilon_one (1 / 2) (by norm_num) using 1
  norm_num

end RiemannZeta.GuthMaynard
