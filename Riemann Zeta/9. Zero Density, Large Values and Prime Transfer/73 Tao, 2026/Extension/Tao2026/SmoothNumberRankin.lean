import Tao2026.SmoothNumberBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Rankin bounds for smooth numbers

The elementary iterated-square-root bound is effective when the smoothness
cutoff is logarithmic.  Tao's Proposition 2.1(i), however, needs the much
larger saddle range `y = z^(alpha+o(1))`.  This module starts the appropriate
source-faithful route: a finite Rankin inequality and the exact finite-prime
Euler product for the Dirichlet series of positive smooth numbers.
-/

namespace Tao2026

open Filter Asymptotics

noncomputable section

/-- The positive Dirichlet series over natural numbers whose prime factors
are strictly below `k`. -/
def smoothDirichletSeries (k : ℕ) (sigma : ℝ) : ℝ :=
  ∑' n : Nat.smoothNumbers k, (n.1 : ℝ) ^ (-sigma)

/-- The finite Euler product attached to the strict Mathlib smoothness
convention. -/
def smoothEulerProduct (k : ℕ) (sigma : ℝ) : ℝ :=
  ∏ p ∈ k.primesBelow, (1 - (p : ℝ) ^ (-sigma))⁻¹

theorem natCast_rpow_neg_mul (m n : ℕ) (sigma : ℝ) :
    ((m * n : ℕ) : ℝ) ^ (-sigma) =
      (m : ℝ) ^ (-sigma) * (n : ℝ) ^ (-sigma) := by
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

theorem natCast_pow_rpow_neg (p e : ℕ) (sigma : ℝ) :
    ((p ^ e : ℕ) : ℝ) ^ (-sigma) = ((p : ℝ) ^ (-sigma)) ^ e := by
  push_cast
  calc
    ((p : ℝ) ^ e) ^ (-sigma) = ((p : ℝ) ^ (e : ℝ)) ^ (-sigma) := by
      rw [Real.rpow_natCast]
    _ = (p : ℝ) ^ ((e : ℝ) * (-sigma)) := by
      rw [Real.rpow_mul (Nat.cast_nonneg p)]
    _ = (p : ℝ) ^ ((-sigma) * (e : ℝ)) := by ring_nf
    _ = ((p : ℝ) ^ (-sigma)) ^ (e : ℝ) := by
      rw [Real.rpow_mul (Nat.cast_nonneg p)]
    _ = ((p : ℝ) ^ (-sigma)) ^ e := Real.rpow_natCast _ _

theorem norm_natCast_rpow_neg_lt_one {p : ℕ} (hp : 1 < p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    ‖(p : ℝ) ^ (-sigma)‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (neg_neg_of_pos hsigma)

/-- Exact Euler product and summability for the Dirichlet series of
`k`-smooth numbers. -/
theorem summable_smoothDirichletSeries_and_eq_eulerProduct
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : Nat.smoothNumbers k => (n.1 : ℝ) ^ (-sigma)) ∧
      smoothDirichletSeries k sigma = smoothEulerProduct k sigma := by
  induction k with
  | zero =>
      have hone : Nat.smoothNumbers 0 = ({1} : Set ℕ) := Nat.smoothNumbers_zero
      constructor
      · rw [hone]
        exact (Set.finite_singleton 1).summable (fun n : ℕ => (n : ℝ) ^ (-sigma))
      · rw [smoothDirichletSeries, smoothEulerProduct, hone]
        simp
  | succ k ih =>
      by_cases hk : k.Prime
      · have hkTwo : 1 < k := hk.one_lt
        let r : ℝ := (k : ℝ) ^ (-sigma)
        have hr : ‖r‖ < 1 := norm_natCast_rpow_neg_lt_one hkTwo hsigma
        have hgeom : Summable (fun e : ℕ => r ^ e) :=
          summable_geometric_of_norm_lt_one hr
        have hprimes : (k + 1).primesBelow = insert k k.primesBelow := by
          ext p
          simp only [Nat.mem_primesBelow, Finset.mem_insert]
          constructor
          · intro hp
            by_cases hpk : p = k
            · exact Or.inl hpk
            · exact Or.inr ⟨by omega, hp.2⟩
          · rintro (hpk | hp)
            · subst p
              exact ⟨Nat.lt_succ_self k, hk⟩
            · exact ⟨hp.1.trans (Nat.lt_succ_self k), hp.2⟩
        have hknot : k ∉ k.primesBelow := by simp [Nat.mem_primesBelow]
        have hprod : Summable (fun em : ℕ × Nat.smoothNumbers k =>
            r ^ em.1 * (em.2.1 : ℝ) ^ (-sigma)) :=
          Summable.mul_of_nonneg hgeom ih.1 (fun _ => by positivity) (fun _ => by positivity)
        have htransport : Summable
            (fun n : Nat.smoothNumbers (k + 1) => (n.1 : ℝ) ^ (-sigma)) := by
          rw [← (Nat.equivProdNatSmoothNumbers hk).summable_iff]
          refine hprod.congr (fun em => ?_)
          simp only [Function.comp_apply, Nat.equivProdNatSmoothNumbers_apply', r]
          rw [natCast_rpow_neg_mul, natCast_pow_rpow_neg]
        refine ⟨htransport, ?_⟩
        rw [smoothDirichletSeries, smoothEulerProduct,
          ← (Nat.equivProdNatSmoothNumbers hk).tsum_eq]
        simp_rw [Nat.equivProdNatSmoothNumbers_apply',
          natCast_rpow_neg_mul,
          natCast_pow_rpow_neg]
        rw [hprod.tsum_prod]
        simp_rw [tsum_mul_left]
        rw [tsum_mul_right,
          hasSum_geom_series_inverse r hr |>.tsum_eq]
        rw [← smoothDirichletSeries]
        rw [ih.2]
        rw [hprimes, Finset.prod_insert hknot]
        simp only [smoothEulerProduct, r, Ring.inverse_eq_inv]
      · have hsmooth : Nat.smoothNumbers (k + 1) = Nat.smoothNumbers k :=
          Nat.smoothNumbers_succ hk
        have hprimes : (k + 1).primesBelow = k.primesBelow := by
          ext p
          simp only [Nat.mem_primesBelow]
          constructor
          · intro hp
            refine ⟨?_, hp.2⟩
            by_contra hpk
            have : p = k := Nat.le_antisymm (Nat.le_of_lt_succ hp.1) (Nat.not_lt.mp hpk)
            exact hk (this ▸ hp.2)
          · exact fun hp => ⟨hp.1.trans (Nat.lt_succ_self k), hp.2⟩
        constructor
        · rw [hsmooth]
          exact ih.1
        · rw [smoothDirichletSeries, hsmooth, ← smoothDirichletSeries, ih.2]
          simp only [smoothEulerProduct, hprimes]

/-- The exact source-inclusive Euler product: Tao's `y`-smooth convention is
Mathlib's strict `(y+1)`-smooth convention. -/
theorem smoothDirichletSeries_source_eq_eulerProduct
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    smoothDirichletSeries (y + 1) sigma =
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  rw [(summable_smoothDirichletSeries_and_eq_eulerProduct
    (y + 1) hsigma).2]
  rw [smoothEulerProduct]
  have hprimes : (y + 1).primesBelow = (Finset.Icc 2 y).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · exact fun hp => ⟨⟨hp.2.two_le, Nat.lt_succ_iff.mp hp.1⟩, hp.2⟩
    · exact fun hp => ⟨Nat.lt_succ_iff.mpr hp.1.2, hp.2⟩
  rw [hprimes]

/-- Finite Rankin inequality before the Euler product is inserted. -/
theorem psiNat_cast_le_rpow_mul_smoothDirichletSeries
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤
      (X : ℝ) ^ sigma * smoothDirichletSeries (y + 1) sigma := by
  have hsumSub :
      (∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), (n : ℝ) ^ (-sigma)) ≤
        ∑' n : Nat.smoothNumbers (y + 1), (n.1 : ℝ) ^ (-sigma) := by
    let e : {n // n ∈ Nat.smoothNumbersUpTo X (y + 1)} ↪
        Nat.smoothNumbers (y + 1) :=
      ⟨fun n => ⟨n.1, (Nat.mem_smoothNumbersUpTo.mp n.2).2⟩,
        fun a b hab => by
          have hv : (a.val : ℕ) = b.val :=
            congrArg (fun z : Nat.smoothNumbers (y + 1) => z.val) hab
          exact Subtype.ext hv⟩
    let s : Finset (Nat.smoothNumbers (y + 1)) :=
      (Nat.smoothNumbersUpTo X (y + 1)).attach.map e
    have hsummable := (summable_smoothDirichletSeries_and_eq_eulerProduct
      (y + 1) hsigma).1
    have hs := hsummable.sum_le_tsum s (fun _ _ => Real.rpow_nonneg (by positivity) _)
    simp only [s, Finset.sum_map] at hs
    rw [← Finset.sum_attach]
    exact hs
  have hone_le (n : ℕ) (hn : n ∈ Nat.smoothNumbersUpTo X (y + 1)) :
      (1 : ℝ) ≤ (X : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) := by
    have hnSmooth := (Nat.mem_smoothNumbersUpTo.mp hn).2
    have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hnSmooth
    have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
    have hnX : (n : ℝ) ≤ X := by
      exact_mod_cast (Nat.mem_smoothNumbersUpTo.mp hn).1
    have hpow : (n : ℝ) ^ sigma ≤ (X : ℝ) ^ sigma :=
      Real.rpow_le_rpow (le_of_lt hnPos) hnX (le_of_lt hsigma)
    calc
      (1 : ℝ) = (n : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) := by
        rw [← Real.rpow_add hnPos]
        simp
      _ ≤ (X : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) :=
        mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) _)
  calc
    (psiNat X y : ℝ) =
        ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), (1 : ℝ) := by
      simp [psiNat]
    _ ≤ ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1),
        (X : ℝ) ^ sigma * (n : ℝ) ^ (-sigma) := by
      exact Finset.sum_le_sum fun n hn => hone_le n hn
    _ = (X : ℝ) ^ sigma *
        ∑ n ∈ Nat.smoothNumbersUpTo X (y + 1), (n : ℝ) ^ (-sigma) := by
      rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ sigma *
        ∑' n : Nat.smoothNumbers (y + 1), (n.1 : ℝ) ^ (-sigma) :=
      mul_le_mul_of_nonneg_left hsumSub (Real.rpow_nonneg (by positivity) _)
    _ = (X : ℝ) ^ sigma * smoothDirichletSeries (y + 1) sigma := rfl

/-- The source-convention Rankin bound with the Dirichlet series replaced by
its exact Euler product over primes `p ≤ y`. -/
theorem psiNat_cast_le_rpow_mul_sourceEulerProduct
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤ (X : ℝ) ^ sigma *
      ∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-sigma))⁻¹ := by
  rw [← smoothDirichletSeries_source_eq_eulerProduct y hsigma]
  exact psiNat_cast_le_rpow_mul_smoothDirichletSeries hX hsigma

/-- A geometric Euler factor written as `1` plus its positive tail. -/
theorem one_sub_inv_eq_one_add_div {r : ℝ} (hr : r < 1) :
    (1 - r)⁻¹ = 1 + r / (1 - r) := by
  have hne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  field_simp
  ring

/-- The exact smooth Euler product is at most the exponential of the sum of
its geometric tails.  This is the first analytic majorant used in Rankin's
method; all terms remain restricted to the literal source primes `p ≤ y`. -/
theorem sourceEulerProduct_le_exp_sum_geometricTail
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    (∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-sigma))⁻¹) ≤
      Real.exp (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma))) := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  have htail (p : ℕ) :
      0 ≤ (p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma)) := by
    by_cases hpTwo : 2 ≤ p
    · have hrlt : (p : ℝ) ^ (-sigma) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast (lt_of_lt_of_le one_lt_two hpTwo))
          (neg_neg_of_pos hsigma)
      exact div_nonneg (Real.rpow_nonneg (by positivity) _) (sub_nonneg.mpr hrlt.le)
    · interval_cases p
      · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hsigma.ne')]
        norm_num
      · norm_num
  change (∏ p ∈ S, (1 - (p : ℝ) ^ (-sigma))⁻¹) ≤
    Real.exp (∑ p ∈ S, (p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma)))
  calc
    (∏ p ∈ S, (1 - (p : ℝ) ^ (-sigma))⁻¹) =
        ∏ p ∈ S, (1 + (p : ℝ) ^ (-sigma) /
          (1 - (p : ℝ) ^ (-sigma))) := by
      apply Finset.prod_congr rfl
      intro p hp
      apply one_sub_inv_eq_one_add_div
      have hpTwo : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast (lt_of_lt_of_le one_lt_two hpTwo))
        (neg_neg_of_pos hsigma)
    _ ≤ Real.exp (∑ p ∈ S, (p : ℝ) ^ (-sigma) /
        (1 - (p : ℝ) ^ (-sigma))) :=
      Real.prod_one_add_le_exp_sum S htail

/-- Rankin's inequality after replacing every Euler factor by its exponential
geometric-tail majorant. -/
theorem psiNat_cast_le_rpow_mul_exp_sum_geometricTail
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤ (X : ℝ) ^ sigma *
      Real.exp (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma))) := by
  exact (psiNat_cast_le_rpow_mul_sourceEulerProduct hX hsigma).trans
    (mul_le_mul_of_nonneg_left
      (sourceEulerProduct_le_exp_sum_geometricTail y hsigma)
      (Real.rpow_nonneg (by positivity) _))

/-- For primes at least two, every geometric tail has a common denominator
controlled by the Euler factor at two. -/
theorem geometricTail_le_twoFactor_mul_rpow
    {p : ℕ} (hp : 2 ≤ p) {sigma : ℝ} (hsigma : 0 < sigma) :
    (p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma)) ≤
      (1 - (2 : ℝ) ^ (-sigma))⁻¹ * (p : ℝ) ^ (-sigma) := by
  have hneg : -sigma ≤ 0 := neg_nonpos.mpr hsigma.le
  have hrle : (p : ℝ) ^ (-sigma) ≤ (2 : ℝ) ^ (-sigma) :=
    Real.rpow_le_rpow_of_nonpos zero_lt_two (by exact_mod_cast hp) hneg
  have htwoLt : (2 : ℝ) ^ (-sigma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hsigma)
  have hpLt : (p : ℝ) ^ (-sigma) < 1 := hrle.trans_lt htwoLt
  have hinv : (1 - (p : ℝ) ^ (-sigma))⁻¹ ≤
      (1 - (2 : ℝ) ^ (-sigma))⁻¹ :=
    (inv_le_inv₀ (sub_pos.mpr hpLt) (sub_pos.mpr htwoLt)).2 (sub_le_sub_left hrle 1)
  rw [div_eq_mul_inv]
  calc
    (p : ℝ) ^ (-sigma) * (1 - (p : ℝ) ^ (-sigma))⁻¹ ≤
        (p : ℝ) ^ (-sigma) * (1 - (2 : ℝ) ^ (-sigma))⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg (by positivity) _)
    _ = (1 - (2 : ℝ) ^ (-sigma))⁻¹ * (p : ℝ) ^ (-sigma) := mul_comm _ _

/-- Uniformized exponential Euler-product bound.  The nonlinear geometric
tails are reduced to the weighted prime sum `∑_{p≤y} p⁻ˢ`. -/
theorem sourceEulerProduct_le_exp_twoFactor_mul_primeRpowSum
    (y : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    (∏ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (1 - (p : ℝ) ^ (-sigma))⁻¹) ≤
      Real.exp ((1 - (2 : ℝ) ^ (-sigma))⁻¹ *
        ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) := by
  refine (sourceEulerProduct_le_exp_sum_geometricTail y hsigma).trans ?_
  apply Real.exp_le_exp.mpr
  calc
    (∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
        (p : ℝ) ^ (-sigma) / (1 - (p : ℝ) ^ (-sigma))) ≤
        ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime,
          (1 - (2 : ℝ) ^ (-sigma))⁻¹ * (p : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro p hp
      exact geometricTail_le_twoFactor_mul_rpow
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1 hsigma
    _ = (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
        ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma) := by
      rw [Finset.mul_sum]

/-- Source-convention Rankin inequality reduced to a single weighted prime
sum and the harmless Euler factor at two. -/
theorem psiNat_cast_le_rpow_mul_exp_twoFactor_mul_primeRpowSum
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤ (X : ℝ) ^ sigma *
      Real.exp ((1 - (2 : ℝ) ^ (-sigma))⁻¹ *
        ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) := by
  exact (psiNat_cast_le_rpow_mul_sourceEulerProduct hX hsigma).trans
    (mul_le_mul_of_nonneg_left
      (sourceEulerProduct_le_exp_twoFactor_mul_primeRpowSum y hsigma)
      (Real.rpow_nonneg (by positivity) _))

/-- Exact exponential form of the Rankin power. -/
theorem rpow_eq_self_mul_exp_neg_one_sub_mul_log
    {X sigma : ℝ} (hX : 0 < X) :
    X ^ sigma = X * Real.exp (-(1 - sigma) * Real.log X) := by
  calc
    X ^ sigma = Real.exp (Real.log X * sigma) := Real.rpow_def_of_pos hX _
    _ = Real.exp (Real.log X + (-(1 - sigma) * Real.log X)) := by
      congr 1
      ring
    _ = Real.exp (Real.log X) * Real.exp (-(1 - sigma) * Real.log X) :=
      Real.exp_add _ _
    _ = X * Real.exp (-(1 - sigma) * Real.log X) := by rw [Real.exp_log hX]

/-- The smooth-number Rankin estimate in saddle-exponent form.  Subsequent
work only has to upper-bound the displayed weighted prime sum and choose
`sigma`; the negative term is the full Rankin saving. -/
theorem psiNat_cast_le_self_mul_exp_rankinExponent
    {X y : ℕ} {sigma : ℝ} (hX : 1 ≤ X) (hsigma : 0 < sigma) :
    (psiNat X y : ℝ) ≤ (X : ℝ) * Real.exp
      (-(1 - sigma) * Real.log X +
        (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  calc
    (psiNat X y : ℝ) ≤ (X : ℝ) ^ sigma *
        Real.exp ((1 - (2 : ℝ) ^ (-sigma))⁻¹ *
          ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) :=
      psiNat_cast_le_rpow_mul_exp_twoFactor_mul_primeRpowSum hX hsigma
    _ = (X : ℝ) * Real.exp
        (-(1 - sigma) * Real.log X +
          (1 - (2 : ℝ) ^ (-sigma))⁻¹ *
            ∑ p ∈ (Finset.Icc 2 y).filter Nat.Prime, (p : ℝ) ^ (-sigma)) := by
      rw [rpow_eq_self_mul_exp_neg_one_sub_mul_log hXpos, Real.exp_add]
      ring

end

end Tao2026
