import RiemannZeta.GuthMaynard.DFIEquation27
import RiemannZeta.GuthMaynard.DFIEquation22Source
import RiemannZeta.GuthMaynard.DFIEquation28
import RiemannZeta.GuthMaynard.DFIEquation29
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# DFI equation (30): absolute kernel integrals

This file proves the logarithmic `L¹` estimate used twice in the DFI
argument: first to control the tail of the main series in equation (27), and
then to estimate the four dual Voronoi branches after equation (29).
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators ContDiff Topology Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-- Split a finite modulus interval at `K` while splitting an absolutely
convergent comparison series at the matching index.  This is the exact
algebraic decomposition used in DFI equation (27): the first summand is the
small-modulus delta approximation, the second is the large-modulus physical
main term, and the last is the complete comparison-series tail. -/
theorem sum_Icc_sub_tsum_eq_small_error_add_large_sub_tail
    (F G : ℕ → ℂ) (K L : ℕ) (hKL : K ≤ L)
    (hG : Summable G) (hG0 : G 0 = 0) :
    (∑ q ∈ Finset.Icc 1 L, F q) - ∑' q : ℕ, G q =
      (∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
      (∑ q ∈ Finset.Ioc K L, F q) -
      ∑' j : ℕ, G (j + (K + 1)) := by
  have hsplitF : (∑ q ∈ Finset.Icc 1 L, F q) =
      (∑ q ∈ Finset.Icc 1 K, F q) +
      (∑ q ∈ Finset.Ioc K L, F q) := by
    rw [← Finset.sum_union]
    · congr 1
      ext q
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      omega
    · simp only [Finset.disjoint_left, Finset.mem_Icc, Finset.mem_Ioc]
      omega
  have hprefixG : (∑ q ∈ Finset.range (K + 1), G q) =
      ∑ q ∈ Finset.Icc 1 K, G q := by
    rw [show Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) by
      ext q
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega]
    simp [hG0]
  have hsplitG := hG.sum_add_tsum_nat_add (K + 1)
  rw [hsplitF, ← hsplitG, hprefixG]
  rw [Finset.sum_sub_distrib]
  ring

/-- Open-upper-endpoint version of the equation-(27) modulus split.  This
matches the delta-symbol support `1 ≤ q < ceil (2Q)` without an endpoint
conversion in the analytic estimates. -/
theorem sum_Ioo_zero_sub_tsum_eq_small_error_add_large_sub_tail
    (F G : ℕ → ℂ) (K L : ℕ) (hKL : K < L)
    (hG : Summable G) (hG0 : G 0 = 0) :
    (∑ q ∈ Finset.Ioo 0 L, F q) - ∑' q : ℕ, G q =
      (∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
      (∑ q ∈ Finset.Ioo K L, F q) -
      ∑' j : ℕ, G (K + (j + 1)) := by
  have hKsub : K ≤ L - 1 := by omega
  have h := sum_Icc_sub_tsum_eq_small_error_add_large_sub_tail
    F G K (L - 1) hKsub hG hG0
  have hfull : Finset.Icc 1 (L - 1) = Finset.Ioo 0 L := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioo]
    omega
  have hlarge : Finset.Ioc K (L - 1) = Finset.Ioo K L := by
    ext q
    simp only [Finset.mem_Ioc, Finset.mem_Ioo]
    omega
  simpa [hfull, hlarge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Reindex the strict tail of a sequence by its distance from the cutoff.
This identifies the tail in the exact equation-(27) decomposition with the
filtered arithmetic tail estimated below. -/
theorem tsum_if_nat_lt_eq_tsum_nat_add_one
    {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [T2Space M]
    (F : ℕ → M) (K : ℕ) :
    (∑' q : ℕ, if K < q then F q else 0) =
      ∑' j : ℕ, F (K + (j + 1)) := by
  let f : ℕ → M := fun q => if K < q then F q else 0
  let g : ℕ → ℕ := fun j => K + (j + 1)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    omega
  have hfOutside : ∀ q ∉ Set.range g, f q = 0 := by
    intro q hq
    dsimp [f]
    split_ifs with hKq
    · exfalso
      apply hq
      exact ⟨q - (K + 1), by dsimp [g]; omega⟩
    · rfl
  apply tsum_eq_tsum_of_hasSum_iff_hasSum
  intro x
  have hcomp : f ∘ g = fun j => F (K + (j + 1)) := by
    funext j
    dsimp [f, g]
    rw [if_pos]
    omega
  rw [← hcomp]
  exact (hg.hasSum_iff hfOutside).symm

/-- Summability form of the strict-tail reindexing. -/
theorem summable_nat_add_one_iff_if_nat_lt
    {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (F : ℕ → M) (K : ℕ) :
    Summable (fun j : ℕ => F (K + (j + 1))) ↔
      Summable (fun q : ℕ => if K < q then F q else 0) := by
  let f : ℕ → M := fun q => if K < q then F q else 0
  let g : ℕ → ℕ := fun j => K + (j + 1)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    omega
  have hfOutside : ∀ q ∉ Set.range g, f q = 0 := by
    intro q hq
    dsimp [f]
    split_ifs with hKq
    · exfalso
      apply hq
      exact ⟨q - (K + 1), by dsimp [g]; omega⟩
    · rfl
  have hcomp : f ∘ g = fun j => F (K + (j + 1)) := by
    funext j
    dsimp [f, g]
    rw [if_pos]
    omega
  rw [← hcomp]
  exact hg.summable_iff hfOutside

/-- Exact factorization behind the sparse-multiple tail estimate used in
equation (27).  Writing `q = d r` assigns an arbitrary positive decay
`alpha` to the modulus cutoff and leaves a summable `r ^ (-1-theta)`
factor. -/
theorem dfiSparseMultipleTerm_factor
    (d r q : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hq : q = d * r) (alpha theta : ℝ) :
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) =
      (q : ℝ) ^ (-alpha) * (d : ℝ) ^ (-theta) *
        (r : ℝ) ^ (-(1 + theta)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqmul : (q : ℝ) = (d : ℝ) * r := by rw [hq]; norm_num
  rw [hqmul, Real.mul_rpow hdR.le hrR.le]
  rw [div_eq_mul_inv, mul_inv]
  rw [← Real.rpow_neg hdR.le, ← Real.rpow_neg hrR.le]
  rw [Real.mul_rpow hdR.le hrR.le]
  calc
    (d : ℝ) * ((d : ℝ) ^ (-(1 + alpha + theta)) *
        (r : ℝ) ^ (-(1 + alpha + theta))) =
      ((d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-(1 + alpha + theta))) *
        (r : ℝ) ^ (-(1 + alpha + theta)) := by
      rw [Real.rpow_one]
      ring
    _ = (d : ℝ) ^ ((1 : ℝ) - (1 + alpha + theta)) *
        (r : ℝ) ^ (-(1 + alpha + theta)) := by
      rw [← Real.rpow_add hdR]
      ring_nf
    _ = ((d : ℝ) ^ (-alpha) * (d : ℝ) ^ (-theta)) *
        ((r : ℝ) ^ (-alpha) * (r : ℝ) ^ (-(1 + theta))) := by
      rw [← Real.rpow_add hdR, ← Real.rpow_add hrR]
      congr 1 <;> ring_nf
    _ = (d : ℝ) ^ (-alpha) * (r : ℝ) ^ (-alpha) *
        (d : ℝ) ^ (-theta) * (r : ℝ) ^ (-(1 + theta)) := by ring

/-- Pointwise sparse-multiple estimate after assigning `alpha` powers of
the modulus to the lower cutoff. -/
theorem dfiSparseMultipleTerm_le
    (K d r q : ℕ) (hd : 0 < d) (hr : 0 < r) (hKr : K < q)
    (hq : q = d * r) (alpha theta : ℝ) (ha : 0 < alpha) (ht : 0 < theta) :
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) ≤
      (K + 1 : ℝ) ^ (-alpha) * (r : ℝ) ^ (-(1 + theta)) := by
  rw [dfiSparseMultipleTerm_factor d r q hd hr hq alpha theta]
  have hKq : (K + 1 : ℝ) ≤ q := by exact_mod_cast hKr
  have hKpos : (0 : ℝ) < K + 1 := by positivity
  have hqpow : (q : ℝ) ^ (-alpha) ≤ (K + 1 : ℝ) ^ (-alpha) :=
    Real.rpow_le_rpow_of_nonpos hKpos hKq (by linarith)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpow : (d : ℝ) ^ (-theta) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hdOne
      (by linarith : -theta ≤ 0)
  have hrpow : 0 ≤ (r : ℝ) ^ (-(1 + theta)) :=
    Real.rpow_nonneg (by positivity) _
  calc
    (q : ℝ) ^ (-alpha) * (d : ℝ) ^ (-theta) *
        (r : ℝ) ^ (-(1 + theta)) ≤
      (K + 1 : ℝ) ^ (-alpha) * 1 *
        (r : ℝ) ^ (-(1 + theta)) := by gcongr
    _ = _ := by ring

/-- Uniform infinite tail over multiples of one source divisor.  This is
the summable refinement of equation (26) needed when the central series is
cut at `K`: it is independent of the upper modulus and retains the full
`K ^ (-alpha)` saving. -/
theorem tsum_dfiSparseMultiples_rpow_le
    (K d : ℕ) (hd : 0 < d) (alpha theta : ℝ)
    (ha : 0 < alpha) (ht : 0 < theta) :
    (∑' q : ℕ, if K < q ∧ d ∣ q then
        (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) ≤
      (K + 1 : ℝ) ^ (-alpha) * (1 + theta⁻¹) := by
  let f : ℕ → ℝ := fun q => if K < q ∧ d ∣ q then
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0
  let g : ℕ → ℕ := fun r => d * r
  have hg : Function.Injective g := by
    intro r s hrs
    dsimp [g] at hrs
    exact Nat.eq_of_mul_eq_mul_left (by omega) hrs
  have hfOutside : ∀ q ∉ Set.range g, f q = 0 := by
    intro q hq
    dsimp [f]
    split_ifs with h
    · exfalso
      apply hq
      obtain ⟨r, hr⟩ := h.2
      exact ⟨r, by simpa [g] using hr.symm⟩
    · rfl
  have htsum : (∑' q : ℕ, f q) = ∑' r : ℕ, f (g r) := by
    apply tsum_eq_tsum_of_hasSum_iff_hasSum
    intro x
    exact (hg.hasSum_iff hfOutside).symm
  have hsPower : Summable (fun r : ℕ => (r : ℝ) ^ (-(1 + theta))) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hmajorSummable : Summable (fun r : ℕ =>
      (K + 1 : ℝ) ^ (-alpha) * (r : ℝ) ^ (-(1 + theta))) := by
    exact hsPower.mul_left _
  rw [show (∑' q : ℕ, if K < q ∧ d ∣ q then
        (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) =
      ∑' q : ℕ, f q by rfl, htsum]
  calc
    (∑' r : ℕ, f (g r)) ≤
        ∑' r : ℕ, (K + 1 : ℝ) ^ (-alpha) *
          (r : ℝ) ^ (-(1 + theta)) := by
      apply Summable.tsum_le_tsum
      · intro r
        by_cases hr0 : r = 0
        · subst r
          dsimp [f, g]
          simp only [Nat.cast_zero]
          rw [Real.zero_rpow (by linarith : -(1 + theta) ≠ 0)]
          positivity
        · have hr : 0 < r := Nat.pos_of_ne_zero hr0
          dsimp [f, g]
          simp only [dvd_mul_right]
          split_ifs with hKr
          · simpa [hr0] using
              dfiSparseMultipleTerm_le K d r (d * r) hd hr hKr.1 rfl
                alpha theta ha ht
          · positivity
      · have hcomp : Summable (f ∘ g) := by
          refine Summable.of_nonneg_of_le
            (f := fun r : ℕ => (K + 1 : ℝ) ^ (-alpha) *
              (r : ℝ) ^ (-(1 + theta)))
            (g := f ∘ g) ?_ ?_ hmajorSummable
          · intro r
            dsimp [f, g]
            split_ifs <;> positivity
          · intro r
            by_cases hr0 : r = 0
            · subst r
              dsimp [f, g]
              simp only [Nat.cast_zero]
              have hzero : (0 : ℝ) ^ (-(1 + theta)) = 0 :=
                Real.zero_rpow (by linarith)
              rw [hzero]
              positivity
            · have hr : 0 < r := Nat.pos_of_ne_zero hr0
              dsimp [f, g]
              simp only [dvd_mul_right]
              split_ifs with hKr
              · simpa [hr0] using
                  dfiSparseMultipleTerm_le K d r (d * r) hd hr hKr.1 rfl
                    alpha theta ha ht
              · positivity
        exact hcomp
      · exact hmajorSummable
    _ = (K + 1 : ℝ) ^ (-alpha) *
        (∑' r : ℕ, (r : ℝ) ^ (-(1 + theta))) := by
      rw [tsum_mul_left]
    _ ≤ (K + 1 : ℝ) ^ (-alpha) * (1 + theta⁻¹) := by
      gcongr
      have htail := tsum_nat_add_one_rpow_neg_le
        (L := (1 : ℝ)) (p := 1 + theta) (by norm_num) (by linarith)
      have hsShift : Summable (fun j : ℕ =>
          ((j + 1 : ℕ) : ℝ) ^ (-(1 + theta))) := by
        simpa [Nat.add_comm] using (summable_nat_add_iff 1).2 hsPower
      have hsplit0 := hsPower.sum_add_tsum_nat_add 1
      have hsplit1 := hsShift.sum_add_tsum_nat_add 1
      have hrewrite : (∑' r : ℕ, (r : ℝ) ^ (-(1 + theta))) =
          1 + ∑' j : ℕ, ((1 : ℝ) + (j + 1 : ℕ)) ^ (-(1 + theta)) := by
        calc
          (∑' r : ℕ, (r : ℝ) ^ (-(1 + theta))) =
              ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ (-(1 + theta)) := by
            have hzero : (0 : ℝ) ^ (-(1 + theta)) = 0 :=
              Real.zero_rpow (by linarith)
            have hprefix : ∑ i ∈ Finset.range 1,
                (i : ℝ) ^ (-(1 + theta)) = 0 := by
              simp only [Finset.sum_range_succ, Finset.sum_range_zero,
                zero_add, Nat.cast_zero, hzero]
            rw [hprefix, zero_add] at hsplit0
            simpa [Nat.cast_add] using hsplit0.symm
          _ = 1 + ∑' j : ℕ,
              (((j + 1) + 1 : ℕ) : ℝ) ^ (-(1 + theta)) := by
            simpa using hsplit1.symm
          _ = _ := by
            congr 1
            apply tsum_congr
            intro j
            congr 1
            push_cast
            ring
      rw [hrewrite]
      calc
        1 + ∑' j : ℕ, ((1 : ℝ) + (j + 1 : ℕ)) ^ (-(1 + theta)) ≤
            1 + (1 : ℝ) ^ (1 - (1 + theta)) / ((1 + theta) - 1) := by
          gcongr
        _ = 1 + theta⁻¹ := by
          rw [Real.one_rpow]
          field_simp [ne_of_gt ht]
          ring

/-- Multiplying an inverse-square arithmetic coefficient by a real power
of the modulus is exactly the denominator exponent used in the
sparse-multiple estimate. -/
theorem dfiDivisorRpowWeight_identity
    (d q : ℕ) (hq : 0 < q) (beta : ℝ) :
    ((d : ℝ) / (q : ℝ) ^ 2) * (q : ℝ) ^ beta =
      (d : ℝ) / (q : ℝ) ^ (2 - beta) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (q : ℝ) ^ 2 = (q : ℝ) ^ (2 : ℝ) by
    exact (Real.rpow_natCast (q : ℝ) 2).symm]
  rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
  calc
    (d : ℝ) * (q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ beta =
        (d : ℝ) * ((q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ beta) := by ring
    _ = (d : ℝ) * (q : ℝ) ^ (-(2 : ℝ) + beta) := by
      rw [Real.rpow_add hqR]
    _ = (d : ℝ) / (q : ℝ) ^ (2 - beta) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
      congr 1
      ring_nf

/-- Pointwise equation-(26) expansion with the source divisors of `h`
retained.  Keeping the divisibility condition is essential for a uniform
tail in the shift. -/
theorem norm_dfiEquation27ArithmeticCoefficient_le_divisorExpansion
    (a b h q : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) [NeZero q] :
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      ((a * b : ℕ) : ℝ) *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) := by
  rw [dfiEquation27ArithmeticCoefficient_eq]
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_natCast]
  have hram := norm_ramanujanSum_le_sum_divisors_filter_dvd q h hh.ne'
  have hgcd : (Nat.gcd (a * b) q : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_le_left q (Nat.mul_pos ha hb)
  have hqR : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hqSq : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqR
  calc
    ((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
        ‖ramanujanSum q h‖ ≤
      (((a * b : ℕ) : ℝ) / (q : ℝ) ^ 2) *
        (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0) := by
      exact mul_le_mul (div_le_div_of_nonneg_right hgcd hqSq.le) hram
        (norm_nonneg _) (div_nonneg (by positivity) hqSq.le)
    _ = ((a * b : ℕ) : ℝ) *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdq : d ∣ q
      · simp only [hdq, if_true]
        field_simp
      · simp [hdq]

/-- Interpolation between the two elementary bounds
`gcd(A,q) ≤ A` and `gcd(A,q) ≤ q`.  This is the quantitative device that
retains a negative power of `ab` while keeping almost the full inverse
modulus in DFI's large-`q` equation-(27) tail. -/
theorem natCast_gcd_le_geometric_interpolation
    (A q : ℕ) (hA : 0 < A) (hq : 0 < q)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (Nat.gcd A q : ℝ) ≤
      (A : ℝ) ^ delta * (q : ℝ) ^ (1 - delta) := by
  have hg : 0 < Nat.gcd A q := Nat.gcd_pos_of_pos_left q hA
  have hgA : Nat.gcd A q ≤ A := Nat.gcd_le_left q hA
  have hgq : Nat.gcd A q ≤ q := Nat.gcd_le_right A hq
  have hgR : (0 : ℝ) < Nat.gcd A q := by exact_mod_cast hg
  calc
    (Nat.gcd A q : ℝ) =
        (Nat.gcd A q : ℝ) ^ delta *
          (Nat.gcd A q : ℝ) ^ (1 - delta) := by
      rw [← Real.rpow_add hgR]
      norm_num
    _ ≤ (A : ℝ) ^ delta * (q : ℝ) ^ (1 - delta) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hgA) hdelta0
      · exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hgq) (sub_nonneg.mpr hdelta1)
      · positivity
      · positivity

/-- Equation (26) after multiplying by the exact external Jacobian
`(ab)⁻¹`.  The interpolated gcd factor exposes `(ab)^(-1+delta)` and
changes the modulus exponent to `-1-delta`, without losing the sparse
source-divisor support of the Ramanujan sum. -/
theorem norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
    (a b h q : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    [NeZero q] (delta : ℝ) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 1) :
    ‖(((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
  have hq : 0 < q := NeZero.pos q
  have hA : 0 < a * b := Nat.mul_pos ha hb
  have hg := natCast_gcd_le_geometric_interpolation
    (a * b) q hA hq delta hdelta0 hdelta1
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast]
  rw [dfiEquation27ArithmeticCoefficient_eq]
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_natCast]
  have hram := norm_ramanujanSum_le_sum_divisors_filter_dvd q h hh.ne'
  let A : ℝ := (a : ℝ) * b
  have hAcast : 0 < A := by dsimp [A]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hAinv : A⁻¹ = A ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg hAcast.le, Real.rpow_one]
  have hscalar :
      (((a : ℝ) * b)⁻¹) *
          ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
            (q : ℝ) ^ 2) =
        (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (q : ℝ) ^ (-(1 + delta)) := by
    push_cast
    change A⁻¹ * (A ^ delta * (q : ℝ) ^ (1 - delta) /
      (q : ℝ) ^ 2) = A ^ (-1 + delta) * (q : ℝ) ^ (-(1 + delta))
    rw [hAinv, show (q : ℝ) ^ 2 = (q : ℝ) ^ (2 : ℝ) by norm_num,
      div_eq_mul_inv, ← Real.rpow_neg hqR.le]
    calc
      A ^ (-(1 : ℝ)) *
          (A ^ delta * q ^ (1 - delta) * q ^ (-(2 : ℝ))) =
        (A ^ (-(1 : ℝ)) * A ^ delta) *
          (q ^ (1 - delta) * q ^ (-(2 : ℝ))) := by ring
      _ = A ^ (-(1 : ℝ) + delta) *
          q ^ ((1 - delta) + -(2 : ℝ)) := by
        rw [← Real.rpow_add hAcast, ← Real.rpow_add hqR]
      _ = _ := by
        congr 1
        all_goals ring_nf
  calc
    (((a : ℝ) * b)⁻¹) *
        (((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
          ‖ramanujanSum q h‖) ≤
      (((a : ℝ) * b)⁻¹) *
        ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
          (q : ℝ) ^ 2 *
          (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0)) := by
      gcongr
    _ = (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
      rw [show (((a : ℝ) * b)⁻¹) *
          ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
            (q : ℝ) ^ 2 *
            (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0)) =
          ((((a : ℝ) * b)⁻¹) *
            ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
              (q : ℝ) ^ 2)) *
            (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0) by ring,
        hscalar]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdq : d ∣ q
      · simp only [hdq, if_true]
        rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
        ring
      · simp [hdq]

/-- Sparse-multiple tail with an arbitrary positive extra modulus exponent.
Writing `q=d r` converts the remaining factor `d/q` into `1/r`; the
ordinary harmonic sum is therefore the only loss. -/
theorem sum_Ioo_dvd_weighted_rpow_le
    (K L d : ℕ) (hd : 0 < d)
    (delta : ℝ) (hdelta : 0 < delta) :
    (∑ q ∈ Finset.Ioo K L,
        if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) ≤
      ((K + 1 : ℕ) : ℝ) ^ (-delta) *
        ((harmonic L : ℚ) : ℝ) := by
  rw [← Finset.sum_filter]
  calc
    ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
        (d : ℝ) / (q : ℝ) ^ (1 + delta) ≤
      ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
        ((K + 1 : ℕ) : ℝ) ^ (-delta) *
          (1 / ((q / d : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqIoo := Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1
      have hdq := (Finset.mem_filter.mp hq).2
      have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hqIoo.1
      have hKq : ((K + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hqIoo.1
      have hKpos : (0 : ℝ) < (K + 1 : ℕ) := by positivity
      have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPos
      have hdPosR : (0 : ℝ) < d := by exact_mod_cast hd
      have hquot : (q : ℝ) / d = (q / d : ℕ) := by
        rw [Nat.cast_div hdq hdPosR.ne']
      have hpow : (q : ℝ) ^ (-delta) ≤
          ((K + 1 : ℕ) : ℝ) ^ (-delta) :=
        Real.rpow_le_rpow_of_nonpos hKpos hKq
          (neg_nonpos.mpr hdelta.le)
      calc
        (d : ℝ) / (q : ℝ) ^ (1 + delta) =
            (q : ℝ) ^ (-delta) * ((d : ℝ) / q) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hqPosR.le]
          rw [show (q : ℝ) ^ (-(1 + delta)) =
              (q : ℝ) ^ (-delta) * (q : ℝ) ^ (-(1 : ℝ)) by
            rw [← Real.rpow_add hqPosR]
            congr 1
            ring]
          have hqnegone : (q : ℝ) ^ (-(1 : ℝ)) = (q : ℝ)⁻¹ := by
            rw [Real.rpow_neg hqPosR.le, Real.rpow_one]
          rw [hqnegone]
          ring
        _ ≤ ((K + 1 : ℕ) : ℝ) ^ (-delta) * ((d : ℝ) / q) := by
          gcongr
        _ = ((K + 1 : ℕ) : ℝ) ^ (-delta) *
            (1 / ((q : ℝ) / d)) := by field_simp
        _ = ((K + 1 : ℕ) : ℝ) ^ (-delta) *
            (1 / ((q / d : ℕ) : ℝ)) := by rw [hquot]
    _ = ((K + 1 : ℕ) : ℝ) ^ (-delta) *
        (∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
          (1 / ((q / d : ℕ) : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ ((K + 1 : ℕ) : ℝ) ^ (-delta) *
        ((harmonic L : ℚ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_filter_dvd_one_div_quotient_le_harmonic K L d hd)
        (Real.rpow_nonneg (by positivity) _)

/-- Source-uniform finite large-modulus tail after the exact `(ab)⁻¹`
Jacobian is included.  Unlike the earlier coarse estimate, this retains
`(ab)^(-1+delta)` and hence permits all `log a`, `log b` factors to be
absorbed with a constant independent of the arithmetic coefficients. -/
theorem sum_Ioo_norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (h.divisors.card : ℝ) *
        (((K + 1 : ℕ) : ℝ) ^ (-delta) *
          ((harmonic L : ℚ) : ℝ)) := by
  let A : ℝ := (((a * b : ℕ) : ℝ) ^ (-1 + delta))
  let B : ℝ := ((K + 1 : ℕ) : ℝ) ^ (-delta) *
    ((harmonic L : ℚ) : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hEach : ∀ d ∈ h.divisors,
      (∑ q ∈ Finset.Ioo K L,
        if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) ≤ B := by
    intro d hdmem
    have hd : 0 < d := Nat.pos_of_mem_divisors hdmem
    simpa only [B] using
      sum_Ioo_dvd_weighted_rpow_le K L d hd delta hdelta0
  calc
    (∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      ∑ q ∈ Finset.Ioo K L, A *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q :=
        lt_of_le_of_lt (Nat.zero_le K) (Finset.mem_Ioo.mp hq).1
      letI : NeZero q := ⟨hqpos.ne'⟩
      simpa only [A] using
        norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
          a b h q ha hb hh delta hdelta0.le hdelta1
    _ = A * (∑ d ∈ h.divisors,
        ∑ q ∈ Finset.Ioo K L,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
      calc
        (∑ q ∈ Finset.Ioo K L, A *
            (∑ d ∈ h.divisors,
              if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0)) =
          ∑ q ∈ Finset.Ioo K L, ∑ d ∈ h.divisors,
            A * (if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
        _ = ∑ d ∈ h.divisors, ∑ q ∈ Finset.Ioo K L,
            A * (if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
          rw [Finset.sum_comm]
        _ = A * (∑ d ∈ h.divisors,
            ∑ q ∈ Finset.Ioo K L,
              if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
    _ ≤ A * (∑ _d ∈ h.divisors, B) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun d hd => hEach d hd) hA
    _ = (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (h.divisors.card : ℝ) *
        (((K + 1 : ℕ) : ℝ) ^ (-delta) *
          ((harmonic L : ℚ) : ℝ)) := by
      simp only [A, B, Finset.sum_const, nsmul_eq_mul]
      ring

/-- Absolute summability of the interpolated sparse-multiple sequence. -/
private theorem summable_dfiSparseMultiples_rpow_interpolated_aux
    (K d : ℕ) (alpha theta : ℝ)
    (ha : 0 < alpha) (ht : 0 < theta) :
    Summable (fun q : ℕ => if K < q ∧ d ∣ q then
      (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) := by
  have hs : Summable (fun q : ℕ =>
      (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta))) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    linarith
  refine Summable.of_nonneg_of_le
    (f := fun q : ℕ => (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta)))
    ?_ ?_ hs
  · intro q
    split_ifs <;> positivity
  · intro q
    split_ifs with hq
    · have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hq.1
      have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
      rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
    · positivity

private theorem summable_finset_sum_apply_interpolated_aux
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

private theorem tsum_finset_sum_apply_interpolated_aux
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' q, ∑ i ∈ s, f i q) = ∑ i ∈ s, ∑' q, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [(hf i (by simp)).tsum_add
        (summable_finset_sum_apply_interpolated_aux s f
          (fun j hj => hf j (by simp [hj])))]
      rw [ih (fun j hj => hf j (by simp [hj]))]

/-- Algebraic exponent conversion used after interpolating the gcd factor in
DFI equation (26).  It is the `(ab)⁻¹` analogue of
`dfiDivisorRpowWeight_identity`. -/
theorem dfiInterpolatedDivisorRpowWeight_identity
    (d q : ℕ) (hq : 0 < q) (rho beta alpha theta : ℝ)
    (hexp : rho - beta = alpha + theta) :
    ((d : ℝ) / (q : ℝ) ^ (1 + rho)) * (q : ℝ) ^ beta =
      (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ← Real.rpow_neg hqR.le, ← Real.rpow_neg hqR.le]
  calc
    (d : ℝ) * (q : ℝ) ^ (-(1 + rho)) * (q : ℝ) ^ beta =
        (d : ℝ) *
          ((q : ℝ) ^ (-(1 + rho)) * (q : ℝ) ^ beta) := by ring
    _ = (d : ℝ) * (q : ℝ) ^ (-(1 + rho) + beta) := by
      rw [← Real.rpow_add hqR]
    _ = (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta)) := by
      congr 2
      linarith

/-- Infinite source-sharp arithmetic tail after the exact `(ab)⁻¹`
Jacobian is included.  The gcd interpolation parameter `rho` preserves the
negative factor `(ab)^(-1+rho)`, while the relation
`rho-beta=alpha+theta` leaves a summable sparse-multiple tail. -/
theorem tsum_norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le
    (K a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (rho alpha theta beta : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (htheta : 0 < theta)
    (hexp : rho - beta = alpha + theta) :
    (∑' q : ℕ, if K < q then
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) ≤
      (((a * b : ℕ) : ℝ) ^ (-1 + rho)) * h.divisors.card *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
  let g : ℕ → ℕ → ℝ := fun d q => if K < q ∧ d ∣ q then
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0
  let A : ℕ → ℝ := fun q => if K < q then
    ‖(((a : ℂ) * b)⁻¹) *
      dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta else 0
  let B : ℕ → ℝ := fun q =>
    (((a * b : ℕ) : ℝ) ^ (-1 + rho)) * ∑ d ∈ h.divisors, g d q
  have hgSummable (d : ℕ) (hd : d ∈ h.divisors) : Summable (g d) := by
    dsimp [g]
    exact summable_dfiSparseMultiples_rpow_interpolated_aux
      K d alpha theta halpha htheta
  have hsumGSummable : Summable (fun q => ∑ d ∈ h.divisors, g d q) :=
    summable_finset_sum_apply_interpolated_aux h.divisors g hgSummable
  have hBSummable : Summable B := by
    dsimp [B]
    exact hsumGSummable.mul_left _
  have hAnonneg (q : ℕ) : 0 ≤ A q := by
    dsimp [A]
    split_ifs <;> positivity
  have hBnonneg (q : ℕ) : 0 ≤ B q := by
    dsimp [B, g]
    positivity
  have hAB (q : ℕ) : A q ≤ B q := by
    by_cases hKq : K < q
    · have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hKq
      letI : NeZero q := ⟨hq.ne'⟩
      have harith :=
        norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
          a b h q ha hb hh rho hrho0.le hrho1
      have hqpow : 0 ≤ (q : ℝ) ^ beta := Real.rpow_nonneg (by positivity) _
      dsimp [A, B, g]
      rw [if_pos hKq]
      calc
        ‖(((a : ℂ) * b)⁻¹) *
              dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta ≤
            ((((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
              (∑ d ∈ h.divisors,
                if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + rho) else 0)) *
              (q : ℝ) ^ beta :=
          mul_le_mul_of_nonneg_right harith hqpow
        _ = (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
            ∑ d ∈ h.divisors,
              if K < q ∧ d ∣ q then
                (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0 := by
          rw [show ((((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
                (∑ d ∈ h.divisors,
                  if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + rho) else 0)) *
                (q : ℝ) ^ beta =
              (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
                ((∑ d ∈ h.divisors,
                  if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + rho) else 0) *
                  (q : ℝ) ^ beta) by ring,
            Finset.sum_mul]
          apply congrArg (((a * b : ℕ) : ℝ) ^ (-1 + rho) * ·)
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdq : d ∣ q
          · simp only [hdq, hKq, and_self, if_true]
            exact dfiInterpolatedDivisorRpowWeight_identity
              d q hq rho beta alpha theta hexp
          · simp [hdq]
    · dsimp [A]
      rw [if_neg hKq]
      exact hBnonneg q
  have hASummable : Summable A :=
    Summable.of_nonneg_of_le hAnonneg hAB hBSummable
  have hsumG : (∑' q : ℕ, ∑ d ∈ h.divisors, g d q) =
      ∑ d ∈ h.divisors, ∑' q : ℕ, g d q :=
    tsum_finset_sum_apply_interpolated_aux h.divisors g hgSummable
  change (∑' q : ℕ, A q) ≤ _
  calc
    (∑' q : ℕ, A q) ≤ ∑' q : ℕ, B q :=
      Summable.tsum_le_tsum hAB hASummable hBSummable
    _ = (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
        (∑ d ∈ h.divisors, ∑' q : ℕ, g d q) := by
      dsimp [B]
      rw [tsum_mul_left, hsumG]
    _ ≤ (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
        (∑ d ∈ h.divisors,
          ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹)) := by
      gcongr with d hd
      dsimp [g]
      exact tsum_dfiSparseMultiples_rpow_le K d
        (Nat.pos_of_mem_divisors hd) alpha theta halpha htheta
    _ = (((a * b : ℕ) : ℝ) ^ (-1 + rho)) * h.divisors.card *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

/-- Absolute summability of the sparse-multiple sequence. -/
theorem summable_dfiSparseMultiples_rpow
    (K d : ℕ) (alpha theta : ℝ)
    (ha : 0 < alpha) (ht : 0 < theta) :
    Summable (fun q : ℕ => if K < q ∧ d ∣ q then
      (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) := by
  have hs : Summable (fun q : ℕ =>
      (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta))) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    linarith
  refine Summable.of_nonneg_of_le
    (f := fun q : ℕ => (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta)))
    ?_ ?_ hs
  · intro q
    split_ifs <;> positivity
  · intro q
    split_ifs with h
    · have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le K) h.1
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
    · positivity

/-- A finite sum of pointwise summable real-valued families is summable.
This local bridge is used to retain the individual source divisors in
equation (26), instead of discarding their sparse modulus support. -/
theorem summable_finset_sum_apply
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

/-- Exchange an absolutely convergent series with a finite source-divisor
sum. -/
theorem tsum_finset_sum_apply
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' q, ∑ i ∈ s, f i q) = ∑ i ∈ s, ∑' q, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [(hf i (by simp)).tsum_add
        (summable_finset_sum_apply s f (fun j hj => hf j (by simp [hj])))]
      rw [ih (fun j hj => hf j (by simp [hj]))]

/-- Source-sharp weighted arithmetic tail for DFI equation (27).  Equation
(26) is kept in divisor-expanded form, so the series is summed only over
multiples of each `d ∣ h`.  This yields a negative power of the cutoff and
only the divisor count of `h`; in particular it avoids the nonuniform
pointwise `h²` majorant. -/
theorem tsum_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le
    (K a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (alpha theta beta : ℝ) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hexp : 2 - beta = 1 + alpha + theta) :
    (∑' q : ℕ, if K < q then
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) ≤
      ((a * b : ℕ) : ℝ) * h.divisors.card *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
  let g : ℕ → ℕ → ℝ := fun d q => if K < q ∧ d ∣ q then
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0
  let A : ℕ → ℝ := fun q => if K < q then
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta else 0
  let B : ℕ → ℝ := fun q =>
    ((a * b : ℕ) : ℝ) * ∑ d ∈ h.divisors, g d q
  have hgSummable (d : ℕ) (hd : d ∈ h.divisors) : Summable (g d) := by
    dsimp [g]
    exact summable_dfiSparseMultiples_rpow K d alpha theta halpha htheta
  have hsumGSummable : Summable (fun q => ∑ d ∈ h.divisors, g d q) :=
    summable_finset_sum_apply h.divisors g hgSummable
  have hBSummable : Summable B := by
    dsimp [B]
    exact hsumGSummable.mul_left _
  have hAnonneg (q : ℕ) : 0 ≤ A q := by
    dsimp [A]
    split_ifs <;> positivity
  have hBnonneg (q : ℕ) : 0 ≤ B q := by
    dsimp [B, g]
    positivity
  have hAB (q : ℕ) : A q ≤ B q := by
    by_cases hKq : K < q
    · have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hKq
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      have harith :=
        norm_dfiEquation27ArithmeticCoefficient_le_divisorExpansion
          a b h q ha hb hh
      have hqpow : 0 ≤ (q : ℝ) ^ beta := Real.rpow_nonneg (by positivity) _
      dsimp [A, B, g]
      rw [if_pos hKq]
      calc
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta ≤
            (((a * b : ℕ) : ℝ) *
              (∑ d ∈ h.divisors,
                if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0)) *
              (q : ℝ) ^ beta :=
          mul_le_mul_of_nonneg_right harith hqpow
        _ = ((a * b : ℕ) : ℝ) *
            ((∑ d ∈ h.divisors,
                if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) *
              (q : ℝ) ^ beta) := by ring
        _ = ((a * b : ℕ) : ℝ) *
            ∑ d ∈ h.divisors,
              if K < q ∧ d ∣ q then
                (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0 := by
          rw [Finset.sum_mul]
          apply congrArg (((a * b : ℕ) : ℝ) * ·)
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdq : d ∣ q
          · simp only [hdq, hKq, and_self, if_true]
            rw [dfiDivisorRpowWeight_identity d q hq beta, hexp]
          · simp [hdq]
    · dsimp [A]
      rw [if_neg hKq]
      exact hBnonneg q
  have hASummable : Summable A :=
    Summable.of_nonneg_of_le hAnonneg hAB hBSummable
  have hsumG : (∑' q : ℕ, ∑ d ∈ h.divisors, g d q) =
      ∑ d ∈ h.divisors, ∑' q : ℕ, g d q :=
    tsum_finset_sum_apply h.divisors g hgSummable
  change (∑' q : ℕ, A q) ≤ _
  calc
    (∑' q : ℕ, A q) ≤ ∑' q : ℕ, B q :=
      Summable.tsum_le_tsum hAB hASummable hBSummable
    _ = ((a * b : ℕ) : ℝ) *
        (∑ d ∈ h.divisors, ∑' q : ℕ, g d q) := by
      dsimp [B]
      rw [tsum_mul_left, hsumG]
    _ ≤ ((a * b : ℕ) : ℝ) *
        (∑ d ∈ h.divisors,
          ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹)) := by
      gcongr with d hd
      dsimp [g]
      exact tsum_dfiSparseMultiples_rpow_le K d
        (Nat.pos_of_mem_divisors hd) alpha theta halpha htheta
    _ = ((a * b : ℕ) : ℝ) * h.divisors.card *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

/-- Equation-(26) tail with the remaining divisor count absorbed by the
standard `h^delta` bound.  The displayed constant depends only on `delta`,
while all dependence on the shift is the permitted epsilon power. -/
theorem tsum_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le_epsilon
    (K a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (alpha theta beta delta : ℝ)
    (halpha : 0 < alpha) (htheta : 0 < theta) (hdelta : 0 < delta)
    (hexp : 2 - beta = 1 + alpha + theta) :
    (∑' q : ℕ, if K < q then
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) ≤
      ((a * b : ℕ) : ℝ) * divisorEpsilonConstant delta * (h : ℝ) ^ delta *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
  calc
    (∑' q : ℕ, if K < q then
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) ≤
        ((a * b : ℕ) : ℝ) * h.divisors.card *
          ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) :=
      tsum_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le
        K a b h ha hb hh alpha theta beta halpha htheta hexp
    _ ≤ ((a * b : ℕ) : ℝ) *
        (divisorEpsilonConstant delta * (h : ℝ) ^ delta) *
          ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
      gcongr
      exact card_divisors_le_const_mul_rpow hdelta hh.ne'
    _ = _ := by ring

/-- Absolute convergence companion to the source-sharp arithmetic tail.
The coarse pointwise estimate is used here only to establish convergence;
the quantitative bound itself remains the divisor-expanded theorem above. -/
theorem summable_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail
    (K a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (alpha theta beta : ℝ) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hexp : 2 - beta = 1 + alpha + theta) :
    Summable (fun q : ℕ => if K < q then
      ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) := by
  let D : ℝ := ((a * b * h ^ 2 : ℕ) : ℝ)
  have hs : Summable (fun q : ℕ =>
      D * (q : ℝ) ^ (-(2 - beta))) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    rw [hexp]
    linarith
  refine Summable.of_nonneg_of_le (fun q => by split_ifs <;> positivity) ?_ hs
  intro q
  by_cases hKq : K < q
  · have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hKq
    letI : NeZero q := ⟨hq.ne'⟩
    have harith := norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b h q ha hb hh
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    rw [if_pos hKq]
    calc
      ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta ≤
          (D * ((q : ℝ) ^ 2)⁻¹) * (q : ℝ) ^ beta :=
        mul_le_mul_of_nonneg_right harith (Real.rpow_nonneg hqR.le _)
      _ = D * (q : ℝ) ^ (-(2 - beta)) := by
        rw [show ((q : ℝ) ^ 2)⁻¹ = (q : ℝ) ^ (-(2 : ℝ)) by
          calc
            ((q : ℝ) ^ 2)⁻¹ = ((q : ℝ) ^ (2 : ℝ))⁻¹ :=
              congrArg (fun z : ℝ => z⁻¹)
                (Real.rpow_natCast (q : ℝ) 2).symm
            _ = (q : ℝ) ^ (-(2 : ℝ)) :=
              (Real.rpow_neg hqR.le (2 : ℝ)).symm]
        calc
          D * (q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ beta =
              D * ((q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ beta) := by ring
          _ = D * (q : ℝ) ^ (-(2 : ℝ) + beta) := by
            rw [Real.rpow_add hqR]
          _ = D * (q : ℝ) ^ (-(2 - beta)) := by
            congr 2
            ring
  · rw [if_neg hKq]
    positivity

/-- Exact elementary integral behind DFI equation (30). -/
theorem intervalIntegral_inv_add_eq_log_div
    {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    (∫ u : ℝ in 0..U, (A + u)⁻¹) = Real.log ((A + U) / A) := by
  have hadd : (fun u : ℝ => (A + u)⁻¹) = fun u => (u + A)⁻¹ := by
    funext u
    rw [add_comm A u]
  rw [hadd]
  rw [intervalIntegral.integral_comp_add_right (fun x : ℝ => x⁻¹) A]
  simpa [add_comm] using
    (integral_inv_of_pos hA (by positivity : 0 < U + A))

/-- The even reciprocal majorant has the exact logarithmic integral on a
symmetric interval. -/
theorem intervalIntegral_inv_add_abs_eq_two_mul_log_div
    {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    (∫ u : ℝ in -U..U, (A + |u|)⁻¹) =
      2 * Real.log ((A + U) / A) := by
  have hcont : Continuous (fun u : ℝ => (A + |u|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀
      (fun u => ne_of_gt (add_pos_of_pos_of_nonneg hA (abs_nonneg u)))
  have hleftInt : IntervalIntegrable (fun u : ℝ => (A + |u|)⁻¹)
      volume (-U) 0 := hcont.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable (fun u : ℝ => (A + |u|)⁻¹)
      volume 0 U := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
  have hneg : (∫ u : ℝ in -U..0, (A + |u|)⁻¹) =
      ∫ u : ℝ in 0..U, (A + u)⁻¹ := by
    calc
      (∫ u : ℝ in -U..0, (A + |u|)⁻¹) =
          ∫ u : ℝ in 0..U, (A + |-u|)⁻¹ := by
        simpa using (intervalIntegral.integral_comp_neg
          (f := fun u : ℝ => (A + |u|)⁻¹) (a := 0) (b := U)).symm
      _ = ∫ u : ℝ in 0..U, (A + u)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro u hu
        simp only [abs_neg]
        rw [abs_of_nonneg]
        exact (Set.uIcc_of_le hU ▸ hu).1
  rw [hneg]
  have hpos : (∫ u : ℝ in 0..U, (A + |u|)⁻¹) =
      ∫ u : ℝ in 0..U, (A + u)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    simp only
    rw [abs_of_nonneg]
    exact (Set.uIcc_of_le hU ▸ hu).1
  rw [hpos, intervalIntegral_inv_add_eq_log_div hA hU]
  ring

/-- Set-integral form of the exact symmetric logarithmic integral. -/
theorem setIntegral_Icc_inv_add_abs_eq_two_mul_log_div
    {A U : ℝ} (hA : 0 < A) (hU : 0 ≤ U) :
    (∫ u : ℝ in Set.Icc (-U) U, (A + |u|)⁻¹) =
      2 * Real.log ((A + U) / A) := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  exact intervalIntegral_inv_add_abs_eq_two_mul_log_div hA hU

/-- Integrated form of the pointwise DFI equation-(19) estimate. -/
theorem integral_abs_dfiDeltaKernel_Icc_le
    {Q U : ℝ} (w : DFIDeltaWeight Q) (hU : 0 ≤ U) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        K * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) := by
  obtain ⟨K, hK, hpoint⟩ := dfiEquation19 w
  refine ⟨K, hK, ?_⟩
  intro q hq
  have hqQ : 0 < (q : ℝ) * Q := mul_pos (by exact_mod_cast hq) w.Q_pos
  have hconst : IntegrableOn (fun _ : ℝ =>
      (((q : ℝ) * Q + Q ^ 2)⁻¹)) (Set.Icc (-U) U) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hinv : Continuous (fun u : ℝ =>
      (((q : ℝ) * Q + |u|)⁻¹)) :=
    (continuous_const.add continuous_abs).inv₀
      (fun u => ne_of_gt (add_pos_of_pos_of_nonneg hqQ (abs_nonneg u)))
  have hinvInt : IntegrableOn (fun u : ℝ =>
      (((q : ℝ) * Q + |u|)⁻¹)) (Set.Icc (-U) U) :=
    hinv.continuousOn.integrableOn_compact isCompact_Icc
  have hkernel : IntegrableOn (fun u : ℝ => |dfiDeltaKernel w q u|)
      (Set.Icc (-U) U) :=
    (contDiff_dfiDeltaKernel w q hq).continuous.abs.continuousOn
      |>.integrableOn_compact isCompact_Icc
  calc
    (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        ∫ u : ℝ in Set.Icc (-U) U,
          K * ((((q : ℝ) * Q + Q ^ 2)⁻¹) +
            (((q : ℝ) * Q + |u|)⁻¹)) := by
      apply integral_mono hkernel ((hconst.add hinvInt).const_mul K)
      intro u
      exact hpoint q hq u
    _ = K * ((∫ u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + Q ^ 2)⁻¹)) +
        ∫ u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + |u|)⁻¹)) := by
      rw [← integral_add hconst hinvInt, integral_const_mul]
    _ = K * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) := by
      rw [setIntegral_Icc_inv_add_abs_eq_two_mul_log_div hqQ hU]
      have hconstEval : (∫ _u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + Q ^ 2)⁻¹)) =
          2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ U - -U)]
        ring
      rw [hconstEval]

/-- Profile-explicit integrated equation-(19) estimate.  Its constant is
independent of `Q`, `U`, and the modulus whenever one derivative profile is
shared by the cutoff family. -/
theorem integral_abs_dfiDeltaKernel_Icc_le_of_profile
    {Q U : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) (hU : 0 ≤ U) :
    ∀ (q : ℕ), 0 < q →
      (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        (24 * max (D 0) (D 1)) *
          (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
            2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) := by
  intro q hq
  let K : ℝ := 24 * max (D 0) (D 1)
  have hK : 0 < K := mul_pos (by norm_num)
    ((hD.positive 0).trans_le (le_max_left _ _))
  have hqQ : 0 < (q : ℝ) * Q :=
    mul_pos (by exact_mod_cast hq) w.Q_pos
  have hconst : IntegrableOn (fun _ : ℝ =>
      (((q : ℝ) * Q + Q ^ 2)⁻¹)) (Set.Icc (-U) U) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hinv : Continuous (fun u : ℝ =>
      (((q : ℝ) * Q + |u|)⁻¹)) :=
    (continuous_const.add continuous_abs).inv₀
      (fun u => ne_of_gt (add_pos_of_pos_of_nonneg hqQ (abs_nonneg u)))
  have hinvInt : IntegrableOn (fun u : ℝ =>
      (((q : ℝ) * Q + |u|)⁻¹)) (Set.Icc (-U) U) :=
    hinv.continuousOn.integrableOn_compact isCompact_Icc
  have hkernel : IntegrableOn (fun u : ℝ => |dfiDeltaKernel w q u|)
      (Set.Icc (-U) U) :=
    (contDiff_dfiDeltaKernel w q hq).continuous.abs.continuousOn
      |>.integrableOn_compact isCompact_Icc
  calc
    (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        ∫ u : ℝ in Set.Icc (-U) U,
          K * ((((q : ℝ) * Q + Q ^ 2)⁻¹) +
            (((q : ℝ) * Q + |u|)⁻¹)) := by
      apply integral_mono hkernel ((hconst.add hinvInt).const_mul K)
      intro u
      simpa only [K] using dfiEquation19_of_profile hD q hq u
    _ = K * ((∫ u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + Q ^ 2)⁻¹)) +
        ∫ u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + |u|)⁻¹)) := by
      rw [← integral_add hconst hinvInt, integral_const_mul]
    _ = K * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) := by
      rw [setIntegral_Icc_inv_add_abs_eq_two_mul_log_div hqQ hU]
      have hconstEval : (∫ _u : ℝ in Set.Icc (-U) U,
          (((q : ℝ) * Q + Q ^ 2)⁻¹)) =
          2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def,
          Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ U - -U)]
        ring
      rw [hconstEval]
    _ = _ := by rfl

/-- With the source choice `U = Q²`, equation (19) integrates to the
logarithmic kernel bound used in DFI equation (30). -/
theorem integral_abs_dfiDeltaKernel_Icc_le_log
    {Q U : ℝ} (w : DFIDeltaWeight Q)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        K * Real.log Q := by
  have hUnonneg : 0 ≤ U := by rw [hU]; positivity
  obtain ⟨K₀, hK₀, hraw⟩ :=
    integral_abs_dfiDeltaKernel_Icc_le w hUnonneg
  let A : ℝ := 2 / Real.log 2 + 4
  have hA : 0 < A := by dsimp [A]; positivity
  let K := K₀ * A
  have hK : 0 < K := mul_pos hK₀ hA
  refine ⟨K, hK, ?_⟩
  intro q hq
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hqpos hQpos
  have hQsq : 0 < Q ^ 2 := by positivity
  have hfirst : 2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ 2 := by
    rw [hU]
    have hinv : (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ (Q ^ 2)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) hQsq).2
      nlinarith [hqQ]
    calc
      2 * Q ^ 2 * (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤
          2 * Q ^ 2 * (Q ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 := by field_simp [ne_of_gt hQsq]
  have hratioEq : (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) =
      1 + Q / (q : ℝ) := by
    rw [hU]
    field_simp [ne_of_gt hqQ, show (q : ℝ) ≠ 0 by positivity]
  have hQdiv : Q / (q : ℝ) ≤ Q :=
    div_le_self (by positivity) hqR
  have hratioPos : 0 < (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) := by
    rw [hratioEq]
    positivity
  have hratio : (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤ Q ^ 2 := by
    rw [hratioEq]
    nlinarith
  have hlogratio : Real.log (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤
      2 * Real.log Q := by
    calc
      Real.log (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤
          Real.log (Q ^ 2) := Real.log_le_log hratioPos hratio
      _ = 2 * Real.log Q := by rw [Real.log_pow]; norm_num
  have hexpr :
      2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q))) ≤
        2 + 4 * Real.log Q := by nlinarith
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMono : Real.log 2 ≤ Real.log Q :=
    Real.log_le_log (by norm_num) hQ
  have htwo : 2 ≤ (2 / Real.log 2) * Real.log Q := by
    calc
      2 = (2 / Real.log 2) * Real.log 2 := by field_simp [hlogTwo.ne']
      _ ≤ (2 / Real.log 2) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlogMono (by positivity)
  have habsorb : 2 + 4 * Real.log Q ≤ A * Real.log Q := by
    dsimp [A]
    nlinarith
  exact (hraw q hq).trans (by
    calc
      K₀ * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) ≤
          K₀ * (2 + 4 * Real.log Q) :=
        mul_le_mul_of_nonneg_left hexpr hK₀.le
      _ ≤ K₀ * (A * Real.log Q) :=
        mul_le_mul_of_nonneg_left habsorb hK₀.le
      _ = K * Real.log Q := by simp [K]; ring)

/-- Profile-explicit logarithmic equation-(30) kernel bound. -/
theorem integral_abs_dfiDeltaKernel_Icc_le_log_of_profile
    {Q U : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∀ (q : ℕ), 0 < q →
      (∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|) ≤
        ((24 * max (D 0) (D 1)) *
          (2 / Real.log 2 + 4)) * Real.log Q := by
  intro q hq
  have hUnonneg : 0 ≤ U := by rw [hU]; positivity
  have hraw := integral_abs_dfiDeltaKernel_Icc_le_of_profile hD hUnonneg q hq
  let K₀ : ℝ := 24 * max (D 0) (D 1)
  let A : ℝ := 2 / Real.log 2 + 4
  have hK₀ : 0 < K₀ := mul_pos (by norm_num)
    ((hD.positive 0).trans_le (le_max_left _ _))
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hqQ : 0 < (q : ℝ) * Q := mul_pos hqpos hQpos
  have hQsq : 0 < Q ^ 2 := by positivity
  have hfirst : 2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ 2 := by
    rw [hU]
    have hinv : (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤ (Q ^ 2)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) hQsq).2
      nlinarith [hqQ]
    calc
      2 * Q ^ 2 * (((q : ℝ) * Q + Q ^ 2)⁻¹) ≤
          2 * Q ^ 2 * (Q ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 2 := by field_simp [ne_of_gt hQsq]
  have hratioEq : (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) =
      1 + Q / (q : ℝ) := by
    rw [hU]
    field_simp [ne_of_gt hqQ, show (q : ℝ) ≠ 0 by positivity]
  have hQdiv : Q / (q : ℝ) ≤ Q :=
    div_le_self (by positivity) hqR
  have hratioPos : 0 < (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) := by
    rw [hratioEq]
    positivity
  have hratio : (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤ Q ^ 2 := by
    rw [hratioEq]
    nlinarith
  have hlogratio : Real.log (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤
      2 * Real.log Q := by
    calc
      Real.log (((q : ℝ) * Q + U) / ((q : ℝ) * Q)) ≤
          Real.log (Q ^ 2) := Real.log_le_log hratioPos hratio
      _ = 2 * Real.log Q := by rw [Real.log_pow]; norm_num
  have hexpr :
      2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q))) ≤
        2 + 4 * Real.log Q := by nlinarith
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMono : Real.log 2 ≤ Real.log Q :=
    Real.log_le_log (by norm_num) hQ
  have htwo : 2 ≤ (2 / Real.log 2) * Real.log Q := by
    calc
      2 = (2 / Real.log 2) * Real.log 2 := by field_simp [hlogTwo.ne']
      _ ≤ (2 / Real.log 2) * Real.log Q :=
        mul_le_mul_of_nonneg_left hlogMono (by positivity)
  have habsorb : 2 + 4 * Real.log Q ≤ A * Real.log Q := by
    dsimp [A]
    nlinarith
  exact hraw.trans (by
    calc
      K₀ * (2 * U * (((q : ℝ) * Q + Q ^ 2)⁻¹) +
          2 * Real.log ((((q : ℝ) * Q + U) / ((q : ℝ) * Q)))) ≤
          K₀ * (2 + 4 * Real.log Q) :=
        mul_le_mul_of_nonneg_left hexpr hK₀.le
      _ ≤ K₀ * (A * Real.log Q) :=
        mul_le_mul_of_nonneg_left habsorb hK₀.le
      _ = ((24 * max (D 0) (D 1)) *
          (2 / Real.log 2 + 4)) * Real.log Q := by simp [K₀, A]; ring)

/-- The equation-(30) kernel after restriction to the displacement interval
forced by the redundant cutoff. -/
noncomputable def dfiEquation30TruncatedKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U u : ℝ) : ℝ :=
  Set.indicator (Set.Icc (-U) U) (fun v => |dfiDeltaKernel w q v|) u

theorem integrable_dfiEquation30TruncatedKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q) (U : ℝ) :
    Integrable (dfiEquation30TruncatedKernel w q U) := by
  unfold dfiEquation30TruncatedKernel
  exact ((contDiff_dfiDeltaKernel w q hq).continuous.abs.continuousOn
    |>.integrableOn_compact isCompact_Icc).integrable_indicator measurableSet_Icc

theorem integral_dfiEquation30TruncatedKernel
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U : ℝ) :
    (∫ u : ℝ, dfiEquation30TruncatedKernel w q U u) =
      ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
  change (∫ u : ℝ, Set.indicator (Set.Icc (-U) U)
    (fun v => |dfiDeltaKernel w q v|) u) = _
  exact integral_indicator measurableSet_Icc

/-- Translation and reflection preserve the truncated kernel integral.  This
is the exact affine change `u = x-y-h` used in DFI equation (30). -/
theorem integral_dfiEquation30TruncatedKernel_affine
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U x h : ℝ) :
    (∫ y : ℝ, dfiEquation30TruncatedKernel w q U (x - y - h)) =
      ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
  let G := dfiEquation30TruncatedKernel w q U
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := volume) (fun y : ℝ => G (-y)) (h - x)
  have hneg := MeasureTheory.integral_neg_eq_self G volume
  calc
    (∫ y : ℝ, G (x - y - h)) =
        ∫ y : ℝ, G (-(y + (h - x))) := by
      apply integral_congr_ae
      filter_upwards [] with y
      congr 1
      ring
    _ = ∫ y : ℝ, G (-y) := hshift
    _ = ∫ y : ℝ, G y := hneg
    _ = ∫ u : ℝ in Set.Icc (-U) U,
        |dfiDeltaKernel w q u| := integral_dfiEquation30TruncatedKernel w q U

theorem integrable_dfiEquation30TruncatedKernel_affine
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U x h : ℝ) :
    Integrable (fun y : ℝ =>
      dfiEquation30TruncatedKernel w q U (x - y - h)) := by
  let G := dfiEquation30TruncatedKernel w q U
  have hG : Integrable G := integrable_dfiEquation30TruncatedKernel w q hq U
  have hcomp : Integrable (fun y : ℝ => G (-(y + (h - x)))) :=
    hG.comp_neg.comp_add_right (h - x)
  simpa only [G, show ∀ y : ℝ, -(y + (h - x)) = x - y - h by
    intro y
    ring] using hcomp

theorem integral_dfiEquation30TruncatedKernel_translate
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (U y h : ℝ) :
    (∫ x : ℝ, dfiEquation30TruncatedKernel w q U (x - y - h)) =
      ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u| := by
  let G := dfiEquation30TruncatedKernel w q U
  calc
    (∫ x : ℝ, G (x - y - h)) = ∫ x : ℝ, G (x + (-y - h)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      ring
    _ = ∫ x : ℝ, G x :=
      MeasureTheory.integral_add_right_eq_self (μ := volume) G (-y - h)
    _ = ∫ u : ℝ in Set.Icc (-U) U,
        |dfiDeltaKernel w q u| := integral_dfiEquation30TruncatedKernel w q U

theorem integrable_dfiEquation30TruncatedKernel_translate
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ) (hq : 0 < q)
    (U y h : ℝ) :
    Integrable (fun x : ℝ =>
      dfiEquation30TruncatedKernel w q U (x - y - h)) := by
  let G := dfiEquation30TruncatedKernel w q U
  have hG : Integrable G := integrable_dfiEquation30TruncatedKernel w q hq U
  have hcomp : Integrable (fun x : ℝ => G (x + (-y - h))) :=
    hG.comp_add_right (-y - h)
  simpa only [G, show ∀ x : ℝ, x + (-y - h) = x - y - h by
    intro x
    ring] using hcomp

/-- The nonnegative physical-variable double integral denoted `||I||` in
DFI equation (30), before the two divisor-variable Jacobians are restored. -/
noncomputable def dfiEquation30PhysicalAbsoluteIntegral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q : ℕ)
    (F : ℝ → ℝ → ℂ) (h : ℝ) : ℝ :=
  ∫ x : ℝ, ∫ y : ℝ,
    ‖F x y‖ * |dfiDeltaKernel w q (x - y - h)|

/-- The `X`-length half of the source estimate in DFI equation (30).  All
smoothness, support and size hypotheses are discharged from equations (2)
and (21); the only constant is the legitimate order-zero source constant. -/
theorem dfiEquation30_physical_le_X_of_profiles
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        X * (dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  let C := dfiEquation2FiniteConstant Cf 0 *
    dfiCutoffFiniteConstant Cφ 0
  have hC : 0 < C := mul_pos (hfC.finiteConstant_pos 0)
    (by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk ↦ hφC.positive k) ⟨0, by simp⟩)
  have hbound := dfiEquation21_of_profiles_uniform_in_shift
    hf hfC hbox hφ hφC hscale 0 0
  intro h q hq
  change dfiEquation30PhysicalAbsoluteIntegral w q
      (dfiLocalizedWeight f φ h) h ≤
    X * C * (∫ u : ℝ in Set.Icc (-U) U,
      |dfiDeltaKernel w q u|)
  let H : ℝ × ℝ → ℝ := fun p =>
    ‖dfiLocalizedWeight f φ h p.1 p.2‖ *
      |dfiDeltaKernel w q (p.1 - p.2 - h)|
  have hHcont : Continuous H := by
    dsimp [H]
    exact (contDiff_uncurry_dfiLocalizedWeight (h := h) hf hφ).continuous.norm.mul
      ((contDiff_dfiDeltaKernel w q hq).continuous.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hlocal : dfiLocalizedWeight f φ h p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hlocal
  have hHcompact : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hHsupport
  have hHint : Integrable H (volume.prod volume) :=
    hHcont.integrable_of_hasCompactSupport hHcompact
  have houter : Integrable (fun x : ℝ => ∫ y : ℝ, H (x, y)) :=
    hHint.integral_prod_left
  let D : ℝ := ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|
  let R : ℝ → ℝ := Set.indicator (Set.Icc X (2 * X)) (fun _ => C * D)
  have hRint : Integrable R := by
    dsimp [R]
    exact (continuousOn_const.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  have hinner (x : ℝ) : (∫ y : ℝ, H (x, y)) ≤ R x := by
    change (∫ y : ℝ, H (x, y)) ≤ R x
    by_cases hx : x ∈ Set.Icc X (2 * X)
    · simp only [R, Set.indicator_of_mem hx]
      have hsliceCont : Continuous (fun y : ℝ => H (x, y)) :=
        hHcont.comp (by fun_prop)
      have hsliceSupport : Function.support (fun y : ℝ => H (x, y)) ⊆
          Set.Icc Y (2 * Y) := by
        intro y hy
        exact (hHsupport hy).2
      have hsliceInt : Integrable (fun y : ℝ => H (x, y)) :=
        hsliceCont.integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact
            isCompact_Icc hsliceSupport)
      have hmajorInt : Integrable (fun y : ℝ =>
          C * dfiEquation30TruncatedKernel w q U (x - y - h)) :=
        (integrable_dfiEquation30TruncatedKernel_affine w q hq U x h).const_mul C
      calc
        (∫ y : ℝ, H (x, y)) ≤
            ∫ y : ℝ, C * dfiEquation30TruncatedKernel w q U (x - y - h) := by
          apply integral_mono hsliceInt hmajorInt
          intro y
          change H (x, y) ≤
            C * dfiEquation30TruncatedKernel w q U (x - y - h)
          by_cases hlocal : dfiLocalizedWeight f φ h x y = 0
          · have hHxy : H (x, y) = 0 := by simp [H, hlocal]
            rw [hHxy]
            exact mul_nonneg hC.le (by
              unfold dfiEquation30TruncatedKernel
              by_cases hu : x - y - h ∈ Set.Icc (-U) U
              · simp [hu]
              · simp [hu])
          · have hφne : φ (x - y - h) ≠ 0 := by
              intro hz
              exact hlocal (by simp only [dfiLocalizedWeight, hz, mul_zero])
            have hu : x - y - h ∈ Set.Icc (-U) U :=
              Set.Ioo_subset_Icc_self (hφ.support_subset hφne)
            change ‖dfiLocalizedWeight f φ h x y‖ *
                |dfiDeltaKernel w q (x - y - h)| ≤
              C * Set.indicator (Set.Icc (-U) U)
                (fun v => |dfiDeltaKernel w q v|) (x - y - h)
            rw [Set.indicator_of_mem hu]
            have hb : ‖dfiLocalizedWeight f φ h x y‖ ≤ C := by
              simpa [C] using (hbound h x y).1
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ = C * D := by
          rw [integral_const_mul,
            integral_dfiEquation30TruncatedKernel_affine w q U x h]
    · have hRx : R x = 0 := by simp [R, hx]
      rw [hRx]
      have hzero : (fun y : ℝ => H (x, y)) = 0 := by
        funext y
        have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
          by_contra hne
          have hp : (x, y) ∈ Function.support
              (Function.uncurry (dfiLocalizedWeight f φ h)) := hne
          exact hx (support_uncurry_dfiLocalizedWeight_subset hbox hp).1
        simp [H, hlocal]
      rw [hzero]
      simp
  change (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ X * C * D
  calc
    (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ ∫ x : ℝ, R x :=
      integral_mono houter hRint hinner
    _ = X * C * D := by
      dsimp [R]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        smul_eq_mul, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal]
      · ring
      · nlinarith [hf.one_le_X]

/-- Fixed-instance projection of the scale-uniform equation-(30) `X`-bound. -/
theorem dfiEquation30_physical_le_X
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        X * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  let C := dfiEquation2FiniteConstant Cf 0 *
    dfiCutoffFiniteConstant Cφ 0
  have hC : 0 < C := mul_pos (hfC.finiteConstant_pos 0)
    (by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk ↦ hφC.positive k) ⟨0, by simp⟩)
  exact ⟨C, hC, by
    simpa only [C] using
      dfiEquation30_physical_le_X_of_profiles
        w hf hfC hbox hφ hφC hscale⟩

/-- The symmetric `Y`-length half of DFI equation (30). -/
theorem dfiEquation30_physical_le_Y_of_profiles
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        Y * (dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  let C := dfiEquation2FiniteConstant Cf 0 *
    dfiCutoffFiniteConstant Cφ 0
  have hC : 0 < C := mul_pos (hfC.finiteConstant_pos 0)
    (by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk ↦ hφC.positive k) ⟨0, by simp⟩)
  have hbound := dfiEquation21_of_profiles_uniform_in_shift
    hf hfC hbox hφ hφC hscale 0 0
  intro h q hq
  change dfiEquation30PhysicalAbsoluteIntegral w q
      (dfiLocalizedWeight f φ h) h ≤
    Y * C * (∫ u : ℝ in Set.Icc (-U) U,
      |dfiDeltaKernel w q u|)
  let H : ℝ × ℝ → ℝ := fun p =>
    ‖dfiLocalizedWeight f φ h p.1 p.2‖ *
      |dfiDeltaKernel w q (p.1 - p.2 - h)|
  have hHcont : Continuous H := by
    dsimp [H]
    exact (contDiff_uncurry_dfiLocalizedWeight (h := h) hf hφ).continuous.norm.mul
      ((contDiff_dfiDeltaKernel w q hq).continuous.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hlocal : dfiLocalizedWeight f φ h p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hlocal
  have hHcompact : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc.prod isCompact_Icc) hHsupport
  have hHint : Integrable H (volume.prod volume) :=
    hHcont.integrable_of_hasCompactSupport hHcompact
  have houter : Integrable (fun y : ℝ => ∫ x : ℝ, H (x, y)) :=
    hHint.integral_prod_right
  let D : ℝ := ∫ u : ℝ in Set.Icc (-U) U, |dfiDeltaKernel w q u|
  let R : ℝ → ℝ := Set.indicator (Set.Icc Y (2 * Y)) (fun _ => C * D)
  have hRint : Integrable R := by
    dsimp [R]
    exact (continuousOn_const.integrableOn_compact isCompact_Icc
      |>.integrable_indicator measurableSet_Icc)
  have hinner (y : ℝ) : (∫ x : ℝ, H (x, y)) ≤ R y := by
    by_cases hy : y ∈ Set.Icc Y (2 * Y)
    · simp only [R, Set.indicator_of_mem hy]
      have hsliceCont : Continuous (fun x : ℝ => H (x, y)) :=
        hHcont.comp (by fun_prop)
      have hsliceSupport : Function.support (fun x : ℝ => H (x, y)) ⊆
          Set.Icc X (2 * X) := by
        intro x hx
        exact (hHsupport hx).1
      have hsliceInt : Integrable (fun x : ℝ => H (x, y)) :=
        hsliceCont.integrable_of_hasCompactSupport
          (HasCompactSupport.of_support_subset_isCompact
            isCompact_Icc hsliceSupport)
      have hmajorInt : Integrable (fun x : ℝ =>
          C * dfiEquation30TruncatedKernel w q U (x - y - h)) :=
        (integrable_dfiEquation30TruncatedKernel_translate w q hq U y h).const_mul C
      calc
        (∫ x : ℝ, H (x, y)) ≤
            ∫ x : ℝ, C * dfiEquation30TruncatedKernel w q U (x - y - h) := by
          apply integral_mono hsliceInt hmajorInt
          intro x
          change H (x, y) ≤
            C * dfiEquation30TruncatedKernel w q U (x - y - h)
          by_cases hlocal : dfiLocalizedWeight f φ h x y = 0
          · have hHxy : H (x, y) = 0 := by simp [H, hlocal]
            rw [hHxy]
            exact mul_nonneg hC.le (by
              unfold dfiEquation30TruncatedKernel
              by_cases hu : x - y - h ∈ Set.Icc (-U) U
              · simp [hu]
              · simp [hu])
          · have hφne : φ (x - y - h) ≠ 0 := by
              intro hz
              exact hlocal (by simp only [dfiLocalizedWeight, hz, mul_zero])
            have hu : x - y - h ∈ Set.Icc (-U) U :=
              Set.Ioo_subset_Icc_self (hφ.support_subset hφne)
            change ‖dfiLocalizedWeight f φ h x y‖ *
                |dfiDeltaKernel w q (x - y - h)| ≤
              C * Set.indicator (Set.Icc (-U) U)
                (fun v => |dfiDeltaKernel w q v|) (x - y - h)
            rw [Set.indicator_of_mem hu]
            have hb : ‖dfiLocalizedWeight f φ h x y‖ ≤ C := by
              simpa [C] using (hbound h x y).1
            exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        _ = C * D := by
          rw [integral_const_mul,
            integral_dfiEquation30TruncatedKernel_translate w q U y h]
    · have hRy : R y = 0 := by simp [R, hy]
      rw [hRy]
      have hzero : (fun x : ℝ => H (x, y)) = 0 := by
        funext x
        have hlocal : dfiLocalizedWeight f φ h x y = 0 := by
          by_contra hne
          have hp : (x, y) ∈ Function.support
              (Function.uncurry (dfiLocalizedWeight f φ h)) := hne
          exact hy (support_uncurry_dfiLocalizedWeight_subset hbox hp).2
        simp [H, hlocal]
      rw [hzero]
      simp
  change (∫ x : ℝ, ∫ y : ℝ, H (x, y)) ≤ Y * C * D
  rw [integral_integral_swap hHint]
  calc
    (∫ y : ℝ, ∫ x : ℝ, H (x, y)) ≤ ∫ y : ℝ, R y :=
      integral_mono houter hRint hinner
    _ = Y * C * D := by
      dsimp [R]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        smul_eq_mul, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal]
      · ring
      · nlinarith [hf.one_le_Y]

/-- Fixed-instance projection of the scale-uniform equation-(30) `Y`-bound. -/
theorem dfiEquation30_physical_le_Y
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        Y * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  obtain ⟨Cf, hfC⟩ := hf.exists_profile
  obtain ⟨Cφ, hφC⟩ := hφ.exists_profile
  let C := dfiEquation2FiniteConstant Cf 0 *
    dfiCutoffFiniteConstant Cφ 0
  have hC : 0 < C := mul_pos (hfC.finiteConstant_pos 0)
    (by
      unfold dfiCutoffFiniteConstant
      exact Finset.sum_pos (fun k _hk ↦ hφC.positive k) ⟨0, by simp⟩)
  exact ⟨C, hC, by
    simpa only [C] using
      dfiEquation30_physical_le_Y_of_profiles
        w hf hfC hbox hφ hφC hscale⟩

/-- Profile-explicit `min(X,Y)` form of source equation (30). -/
theorem dfiEquation30_physical_le_min_of_profiles
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        min X Y * (dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          (∫ u : ℝ in Set.Icc (-U) U,
            |dfiDeltaKernel w q u|) := by
  intro h q hq
  rcases le_total X Y with hXY | hYX
  · rw [min_eq_left hXY]
    exact dfiEquation30_physical_le_X_of_profiles
      w hf hfC hbox hφ hφC hscale h q hq
  · rw [min_eq_right hYX]
    exact dfiEquation30_physical_le_Y_of_profiles
      w hf hfC hbox hφ hφC hscale h q hq

/-- The literal `min(X,Y)` physical estimate displayed in DFI equation
(30), still retaining the exact truncated delta-kernel integral. -/
theorem dfiEquation30_physical_le_min
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        min X Y * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) := by
  obtain ⟨CX, hCX, hXbound⟩ :=
    dfiEquation30_physical_le_X w hf hbox hφ hscale
  obtain ⟨CY, hCY, hYbound⟩ :=
    dfiEquation30_physical_le_Y w hf hbox hφ hscale
  let C := max CX CY
  have hC : 0 < C := hCX.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro h q hq
  have hXbound := hXbound h q hq
  have hYbound := hYbound h q hq
  have hD : 0 ≤ (∫ u : ℝ in Set.Icc (-U) U,
      |dfiDeltaKernel w q u|) := integral_nonneg (fun _ => abs_nonneg _)
  rcases le_total X Y with hXY | hYX
  · rw [min_eq_left hXY]
    exact hXbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left CX CY)
        (zero_le_one.trans hf.one_le_X)) hD)
  · rw [min_eq_right hYX]
    exact hYbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right CX CY)
        (zero_le_one.trans hf.one_le_Y)) hD)

/-- DFI equation (30) in its published logarithmic physical-variable form,
for the source choice `U = Q²`. -/
theorem dfiEquation30_physical_log_bound
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        K * min X Y * Real.log Q := by
  obtain ⟨C, hC, hphysical⟩ :=
    dfiEquation30_physical_le_min w hf hbox hφ hscale
  obtain ⟨K₀, hK₀, hkernelAll⟩ :=
    integral_abs_dfiDeltaKernel_Icc_le_log w hQ hU
  let K := C * K₀
  have hK : 0 < K := mul_pos hC hK₀
  refine ⟨K, hK, ?_⟩
  intro h q hq
  have hkernel := hkernelAll q hq
  exact (hphysical h q hq).trans (by
    have hmin : 0 ≤ min X Y := le_min
      (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
    calc
      min X Y * C * (∫ u : ℝ in Set.Icc (-U) U,
          |dfiDeltaKernel w q u|) ≤
          min X Y * C * (K₀ * Real.log Q) :=
        mul_le_mul_of_nonneg_left hkernel (mul_nonneg hmin hC.le)
      _ = K * min X Y * Real.log Q := by simp [K]; ring)

/-- Scale-family-uniform logarithmic form of DFI equation (30).  Every
The constant is an explicit function of the three fixed derivative profiles. -/
theorem dfiEquation30_physical_log_bound_of_profiles
    {Q P X Y U : ℝ} {w : DFIDeltaWeight Q}
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∀ (h : ℝ) (q : ℕ), 0 < q →
      dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
        ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4))) *
          min X Y * Real.log Q := by
  intro h q hq
  have hphysical := dfiEquation30_physical_le_min_of_profiles
    w hf hfC hbox hφ hφC hscale h q hq
  have hkernel := integral_abs_dfiDeltaKernel_Icc_le_log_of_profile
    hwC hQ hU q hq
  let C : ℝ := dfiEquation2FiniteConstant Cf 0 *
    dfiCutoffFiniteConstant Cφ 0
  let K : ℝ := (24 * max (Cw 0) (Cw 1)) *
    (2 / Real.log 2 + 4)
  have hC : 0 ≤ C := by
    exact mul_nonneg (hfC.finiteConstant_pos 0).le
      (by
        unfold dfiCutoffFiniteConstant
        exact Finset.sum_nonneg (fun k _hk ↦ (hφC.positive k).le))
  have hmin : 0 ≤ min X Y := le_min
    (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  calc
    dfiEquation30PhysicalAbsoluteIntegral w q
        (dfiLocalizedWeight f φ h) h ≤
      min X Y * C * (∫ u : ℝ in Set.Icc (-U) U,
        |dfiDeltaKernel w q u|) := by
        simpa only [C] using hphysical
    _ ≤ min X Y * C * (K * Real.log Q) :=
      mul_le_mul_of_nonneg_left (by simpa only [K] using hkernel)
        (mul_nonneg hmin hC)
    _ = ((dfiEquation2FiniteConstant Cf 0 *
          dfiCutoffFiniteConstant Cφ 0) *
        ((24 * max (Cw 0) (Cw 1)) *
          (2 / Real.log 2 + 4))) * min X Y * Real.log Q := by
      simp only [C, K]
      ring

/-- Scale-independent constant for the physical double-main integral. -/
noncomputable def dfiEquation27PhysicalMainProfileConstant
    (Cf : ℕ → ℕ → ℝ) (Cφ Cw : ℕ → ℝ) : ℝ :=
  (dfiEquation2FiniteConstant Cf 0 * dfiCutoffFiniteConstant Cφ 0) *
    ((24 * max (Cw 0) (Cw 1)) * (2 / Real.log 2 + 4))

theorem dfiEquation27PhysicalMainProfileConstant_pos
    {P X Y U Q : ℝ} {w : DFIDeltaWeight Q}
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hfC : DFIEquation2Profile f P X Y Cf)
    {hφ : DFIRedundantCutoff φ U}
    (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hwC : DFIDeltaWeightProfile w Cw) :
    0 < dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw := by
  have hf0 : 0 < dfiEquation2FiniteConstant Cf 0 := hfC.finiteConstant_pos 0
  have hφ0 : 0 < dfiCutoffFiniteConstant Cφ 0 := by
    simpa [dfiCutoffFiniteConstant] using hφC.positive 0
  have hw0 : 0 < max (Cw 0) (Cw 1) :=
    (hwC.positive 0).trans_le (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold dfiEquation27PhysicalMainProfileConstant
  exact mul_pos (mul_pos hf0 hφ0)
    (mul_pos (mul_pos (by norm_num) hw0) (by positivity))

/-- The logarithmic double-main integral occurring in DFI equation (27) is
bounded by the equation-(30) physical mass.  This is the missing norm bridge
between the raw localized weight and the actual two Voronoi main terms. -/
theorem norm_dfiEquation27PhysicalMainIntegral_le_of_profiles
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∀ (h : ℝ) (a b q : ℕ), 0 < q → ∀ qx qy : ℕ,
      ‖dfiEquation27PhysicalMainIntegral w q a b qx qy
          (dfiLocalizedWeight f φ h) h‖ ≤
        dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw *
          (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          min X Y * Real.log Q := by
  let K₀ : ℝ := dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw
  have hK₀ : 0 < K₀ := by
    simpa only [K₀] using
      dfiEquation27PhysicalMainProfileConstant_pos hfC hφC hwC
  have hphysical :=
    dfiEquation30_physical_log_bound_of_profiles
      hf hfC hbox hφ hφC hscale hwC hQ hU
  intro h a b q hq qx qy
  let F : ℝ → ℝ → ℂ := dfiLocalizedWeight f φ h
  let G : ℝ × ℝ → ℂ := fun p =>
    dfiEquation27C a b qx qy F p.1 p.2 *
      (dfiDeltaKernel w q (p.1 - p.2 - h) : ℂ)
  let H : ℝ × ℝ → ℝ := fun p =>
    ‖F p.1 p.2‖ * |dfiDeltaKernel w q (p.1 - p.2 - h)|
  let LX : ℝ := Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|
  let LY : ℝ := Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|
  let B : ℝ := LX * LY
  have hLX : 0 ≤ LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hB : 0 ≤ B := mul_nonneg hLX hLY
  have hGsmooth : Continuous G := by
    dsimp [G, F]
    exact (contDiff_uncurry_dfiEquation27C_source hf hbox hφ a b qx qy).continuous.mul
      (Complex.ofRealCLM.continuous.comp
        ((contDiff_dfiDeltaKernel w q hq).continuous.comp (by fun_prop)))
  have hGsupport : Function.support G ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hFne : F p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [G, dfiEquation27C, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hFne
  have hGint : Integrable G (volume.prod volume) :=
    hGsmooth.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) hGsupport)
  have hHsmooth : Continuous H := by
    dsimp [H, F]
    exact (contDiff_uncurry_dfiLocalizedWeight hf hφ).continuous.norm.mul
      ((contDiff_dfiDeltaKernel w q hq).continuous.abs.comp (by fun_prop))
  have hHsupport : Function.support H ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
    intro p hp
    have hFne : F p.1 p.2 ≠ 0 := by
      intro hz
      exact hp (by simp [H, hz])
    exact support_uncurry_dfiLocalizedWeight_subset hbox hFne
  have hHint : Integrable H (volume.prod volume) :=
    hHsmooth.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc) hHsupport)
  have hpoint (p : ℝ × ℝ) : ‖G p‖ ≤ B * H p := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hFzero : F p.1 p.2 = 0
    · simp [H, dfiEquation27C, hFzero]
    · have hxy : (p.1, p.2) ∈
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
        support_uncurry_dfiLocalizedWeight_subset hbox hFzero
      have hxlog :=
        abs_log_le_log_two_mul_of_mem_Icc hf.one_le_X hxy.1
      have hylog :=
        abs_log_le_log_two_mul_of_mem_Icc hf.one_le_Y hxy.2
      have hcb := norm_dfiEquation27C_le a b qx qy F p.1 p.2
      have hCtoB :
          ‖dfiEquation27C a b qx qy F p.1 p.2‖ ≤
            B * ‖F p.1 p.2‖ := by
        dsimp [B, LX, LY]
        calc
          ‖dfiEquation27C a b qx qy F p.1 p.2‖ ≤
              (|Real.log p.1| + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (|Real.log p.2| + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                ‖F p.1 p.2‖ := hcb
          _ ≤ (Real.log (2 * X) + |Real.log a| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
                (Real.log (2 * Y) + |Real.log b| +
                  2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
                ‖F p.1 p.2‖ := by gcongr
      simpa [H, mul_assoc] using
        mul_le_mul_of_nonneg_right hCtoB
          (abs_nonneg (dfiDeltaKernel w q (p.1 - p.2 - h)))
  have hproduct :
      ‖∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G p
          ∂(volume.prod volume)‖ ≤
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), B * H p
          ∂(volume.prod volume) := by
    exact MeasureTheory.norm_integral_le_of_norm_le
      ((hHint.const_mul B).integrableOn)
      (Filter.Eventually.of_forall hpoint)
  have hnonneg (p : ℝ × ℝ) : 0 ≤ B * H p := by
    exact mul_nonneg hB (mul_nonneg (norm_nonneg _) (abs_nonneg _))
  have hwhole :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), B * H p
          ∂(volume.prod volume)) ≤
        ∫ p : ℝ × ℝ, B * H p ∂(volume.prod volume) :=
    MeasureTheory.integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hnonneg) (hHint.const_mul B)
  have hmainRewrite :
      dfiEquation27PhysicalMainIntegral w q a b qx qy F h =
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G p
          ∂(volume.prod volume) := by
    unfold dfiEquation27PhysicalMainIntegral
    exact (MeasureTheory.setIntegral_prod G hGint.integrableOn).symm
  have hmassRewrite :
      (∫ p : ℝ × ℝ, B * H p ∂(volume.prod volume)) =
        B * dfiEquation30PhysicalAbsoluteIntegral w q F h := by
    rw [MeasureTheory.integral_const_mul]
    unfold dfiEquation30PhysicalAbsoluteIntegral
    rw [MeasureTheory.integral_prod H hHint]
  rw [hmainRewrite]
  calc
    ‖∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), G p
        ∂(volume.prod volume)‖ ≤
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), B * H p
          ∂(volume.prod volume) := hproduct
    _ ≤ ∫ p : ℝ × ℝ, B * H p ∂(volume.prod volume) := hwhole
    _ = B * dfiEquation30PhysicalAbsoluteIntegral w q F h := hmassRewrite
    _ ≤ B * (K₀ * min X Y * Real.log Q) :=
      mul_le_mul_of_nonneg_left (hphysical h q hq) hB
    _ = dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw *
        LX * LY * min X Y * Real.log Q := by
      dsimp [B]
      simp only [K₀]
      ring

/-- Compatibility form of the explicit physical-main estimate. -/
theorem exists_norm_dfiEquation27PhysicalMainIntegral_le
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ) (a b q : ℕ), 0 < q → ∀ qx qy : ℕ,
      ‖dfiEquation27PhysicalMainIntegral w q a b qx qy
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qx|) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * |Real.log qy|) *
          min X Y * Real.log Q := by
  refine ⟨dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw,
    dfiEquation27PhysicalMainProfileConstant_pos hfC hφC hwC, ?_⟩
  exact norm_dfiEquation27PhysicalMainIntegral_le_of_profiles
    w hf hfC hbox hφ hφC hscale hwC hQ hU

/-- Uniform equation-(27) physical-main bound after substituting the two
reduced Voronoi denominators.  For every retained delta modulus `q ≤ 2Q`,
both reduced logarithms are absorbed into `log (2Q)`. -/
theorem norm_dfiEquation27PhysicalMainIntegral_reduced_le_of_profiles
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∀ (h : ℝ) (a b q : ℕ),
      0 < q → (q : ℝ) ≤ 2 * Q →
      ‖dfiEquation27PhysicalMainIntegral w q a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw *
          (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
          min X Y * Real.log Q := by
  have hmain := norm_dfiEquation27PhysicalMainIntegral_le_of_profiles
    w hf hfC hbox hφ hφC hscale hwC hQ hU
  intro h a b q hq hqQ
  have hqlog : Real.log (q : ℝ) ≤ Real.log (2 * Q) := by
    exact Real.log_le_log (by exact_mod_cast hq) hqQ
  have hqa := abs_log_dfiReducedDenominator_le a q hq
  have hqb := abs_log_dfiReducedDenominator_le b q hq
  have hlogQ : 0 ≤ Real.log Q :=
    Real.log_nonneg (by linarith)
  have hmin : 0 ≤ min X Y := by
    exact le_min (zero_le_one.trans hf.one_le_X)
      (zero_le_one.trans hf.one_le_Y)
  have hLX : 0 ≤ Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator a q : ℝ)| := by
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| +
        2 * |Real.log (dfiReducedDenominator b q : ℝ)| := by
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  refine (hmain h a b q hq
    (dfiReducedDenominator a q) (dfiReducedDenominator b q)).trans ?_
  have hqaQ :
      |Real.log (dfiReducedDenominator a q : ℝ)| ≤ Real.log (2 * Q) :=
    hqa.trans hqlog
  have hqbQ :
      |Real.log (dfiReducedDenominator b q : ℝ)| ≤ Real.log (2 * Q) :=
    hqb.trans hqlog
  have hlog2Q : 0 ≤ Real.log (2 * Q) :=
    Real.log_nonneg (by nlinarith)
  have hLXQ : 0 ≤ Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) := by
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLYQ : 0 ≤ Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q) := by
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hC : 0 ≤ dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw :=
    (dfiEquation27PhysicalMainProfileConstant_pos hfC hφC hwC).le
  gcongr

/-- Compatibility form of the explicit reduced physical-main estimate. -/
theorem exists_norm_dfiEquation27PhysicalMainIntegral_reduced_le
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ) (a b q : ℕ),
      0 < q → (q : ℝ) ≤ 2 * Q →
      ‖dfiEquation27PhysicalMainIntegral w q a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
          (Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
          min X Y * Real.log Q := by
  refine ⟨dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw,
    dfiEquation27PhysicalMainProfileConstant_pos hfC hφC hwC, ?_⟩
  exact norm_dfiEquation27PhysicalMainIntegral_reduced_le_of_profiles
    w hf hfC hbox hφ hφC hscale hwC hQ hU

/-- Large-modulus physical-main contribution in the source equation-(27)
split.  The delta approximation is not used here: equation (30) supplies a
uniform physical integral bound, while equation (26) supplies the sparse
arithmetic tail. -/
theorem exists_norm_sum_Ioo_dfiEquation27PhysicalMain_le_epsilon
    {Q P X Y U hR : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hmod : ∀ q ∈ Finset.Ioo K L, (q : ℝ) ≤ 2 * Q)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ‖∑ q ∈ Finset.Ioo K L,
          (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
            dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ hR) hR‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant delta * (h : ℝ) ^ delta) *
            ((1 / (K + 1 : ℝ)) *
              ((1 + delta⁻¹) * max 1 ((L : ℝ) ^ delta)))) *
          (C *
            (Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            (Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            min X Y * Real.log Q) := by
  obtain ⟨C, hC, hphysical⟩ :=
    exists_norm_dfiEquation27PhysicalMainIntegral_reduced_le
      w hf hfC hbox hφ hφC hscale hwC hQ hU
  refine ⟨C, hC, ?_⟩
  let I : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ hR) hR
  let B : ℝ := C *
    (Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
    (Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
    min X Y * Real.log Q
  have hlogX : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith [hf.one_le_X])
  have hlogY : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith [hf.one_le_Y])
  have hlog2Q : 0 ≤ Real.log (2 * Q) :=
    Real.log_nonneg (by nlinarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hmin : 0 ≤ min X Y := le_min
    (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : ∀ q ∈ Finset.Ioo K L, ‖I q‖ ≤ B := by
    intro q hq
    have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp hq).1
    exact hphysical hR a b q hqpos (hmod q hq)
  have hsum :=
    norm_sum_Ioo_dfiEquation27ArithmeticCoefficient_mul_le_epsilon
      a b h K L ha hb hh hdelta I B hB hI
  let c : ℂ := ((a : ℂ) * b)⁻¹
  have hfactor :
      (∑ q ∈ Finset.Ioo K L,
          (c * dfiEquation27ArithmeticCoefficient a b h q) * I q) =
        c * ∑ q ∈ Finset.Ioo K L,
          dfiEquation27ArithmeticCoefficient a b h q * I q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  change ‖∑ q ∈ Finset.Ioo K L,
      (c * dfiEquation27ArithmeticCoefficient a b h q) * I q‖ ≤ _
  rw [hfactor, norm_mul]
  have hout := mul_le_mul_of_nonneg_left hsum (norm_nonneg c)
  dsimp [c, B] at hout ⊢
  convert hout using 1
  all_goals ring

/-- Large-modulus physical-main estimate with the exact external `(ab)⁻¹`
factor kept inside the arithmetic summation.  Interpolating
`gcd(ab,q)` prevents the logarithmic main kernels from introducing any
dependence of the final DFI constant on `a` or `b`. -/
theorem norm_sum_Ioo_dfiEquation27PhysicalMain_le_interpolated_of_profiles
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
      ∀ (hR : ℝ) (a b h K L : ℕ), 0 < a → 0 < b → 0 < h →
      (∀ q ∈ Finset.Ioo K L, (q : ℝ) ≤ 2 * Q) →
      ‖∑ q ∈ Finset.Ioo K L,
          (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
            dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ hR) hR‖ ≤
        ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          (((K + 1 : ℕ) : ℝ) ^ (-delta) *
            ((harmonic L : ℚ) : ℝ))) *
          (dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw *
            (Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            (Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            min X Y * Real.log Q) := by
  let C : ℝ := dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw
  have hC : 0 < C := by
    simpa only [C] using dfiEquation27PhysicalMainProfileConstant_pos hfC hφC hwC
  have hphysical := norm_dfiEquation27PhysicalMainIntegral_reduced_le_of_profiles
    w hf hfC hbox hφ hφC hscale hwC hQ hU
  intro hR a b h K L ha hb hh hmod
  let I : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ hR) hR
  let B : ℝ := C *
    (Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
    (Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
    min X Y * Real.log Q
  let A : ℝ := (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
    (h.divisors.card : ℝ) *
    (((K + 1 : ℕ) : ℝ) ^ (-delta) * ((harmonic L : ℚ) : ℝ))
  have hlogX : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by nlinarith [hf.one_le_X])
  have hlogY : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by nlinarith [hf.one_le_Y])
  have hlog2Q : 0 ≤ Real.log (2 * Q) :=
    Real.log_nonneg (by nlinarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hmin : 0 ≤ min X Y := le_min
    (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hI : ∀ q ∈ Finset.Ioo K L, ‖I q‖ ≤ B := by
    intro q hq
    have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le K)
      (Finset.mem_Ioo.mp hq).1
    exact hphysical hR a b q hqpos (hmod q hq)
  have htail :=
    sum_Ioo_norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
      a b h K L ha hb hh delta hdelta0 hdelta1
  calc
    ‖∑ q ∈ Finset.Ioo K L,
        (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
          I q‖ ≤
      ∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹ *
          dfiEquation27ArithmeticCoefficient a b h q) * I q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖ * B := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hI q hq) (norm_nonneg _)
    _ = (∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖) * B := by
      rw [Finset.sum_mul]
    _ ≤ A * B := mul_le_mul_of_nonneg_right htail hB
    _ = ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          (((K + 1 : ℕ) : ℝ) ^ (-delta) *
            ((harmonic L : ℚ) : ℝ))) *
          (dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw *
            (Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            (Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            min X Y * Real.log Q) := rfl

/-- Compatibility form of the explicit interpolated physical branch. -/
theorem exists_norm_sum_Ioo_dfiEquation27PhysicalMain_le_interpolated
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hR : ℝ) (a b h K L : ℕ), 0 < a → 0 < b → 0 < h →
      (∀ q ∈ Finset.Ioo K L, (q : ℝ) ≤ 2 * Q) →
      ‖∑ q ∈ Finset.Ioo K L,
          (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
            dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ hR) hR‖ ≤
        ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          (((K + 1 : ℕ) : ℝ) ^ (-delta) *
            ((harmonic L : ℚ) : ℝ))) *
          (C *
            (Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            (Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            min X Y * Real.log Q) := by
  refine ⟨dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw,
    dfiEquation27PhysicalMainProfileConstant_pos hfC hφC hwC, ?_⟩
  exact norm_sum_Ioo_dfiEquation27PhysicalMain_le_interpolated_of_profiles
    w hf hfC hbox hφ hφC hscale hwC hQ hU hdelta0 hdelta1

/-- Small-modulus delta-approximation error with the exact `(ab)⁻¹`
Jacobian included before the equation-(26) summation.  The analytic
equation-(18) envelope is unchanged, while the arithmetic factor retains
the negative power of `ab` needed for a source-uniform final constant. -/
theorem exists_norm_sum_Icc_inv_ab_dfiEquation27_reduced_main_error_le_interpolated
    {Q P X Y U : ℝ} (hQ : 0 < Q) (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (j : ℕ) (hj : 2 ≤ j)
    {delta : ℝ} (hdelta0 : 0 < delta)
    (hdelta1 : delta ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b h K : ℕ), 0 < a → 0 < b → 0 < h → 1 ≤ K →
      ‖∑ q ∈ Finset.Icc 1 K,
          ((((a : ℂ) * b)⁻¹) *
            dfiEquation27ArithmeticCoefficient a b h q) *
            (dfiEquation27PhysicalMainIntegral w q a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        C * ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          ((harmonic (K + 1) : ℚ) : ℝ)) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
  obtain ⟨C, hC, hmain⟩ :=
    norm_sum_Icc_dfiEquation27_reduced_main_error_le
      hQ w hf hfC hbox hφ hφC hscale j hj
  refine ⟨C, hC, ?_⟩
  intro a b h K ha hb hh hK
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let E : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
      dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ)
  have hfactor :
      (∑ q ∈ Finset.Icc 1 K,
          (c * dfiEquation27ArithmeticCoefficient a b h q) * E q) =
        c * ∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q * E q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have harithRaw :=
    sum_Ioo_norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
      a b h 0 (K + 1) ha hb hh delta hdelta0 hdelta1
  have hinterval : Finset.Ioo 0 (K + 1) = Finset.Icc 1 K := by
    ext q
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  rw [hinterval] at harithRaw
  have harith :
      ‖c‖ * (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) ≤
        (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          ((harmonic (K + 1) : ℚ) : ℝ) := by
    calc
      ‖c‖ * (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) =
        ∑ q ∈ Finset.Icc 1 K,
          ‖c * dfiEquation27ArithmeticCoefficient a b h q‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [norm_mul]
      _ ≤ (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          (((0 + 1 : ℕ) : ℝ) ^ (-delta) *
            ((harmonic (K + 1) : ℚ) : ℝ)) := by
        simpa only [c] using harithRaw
      _ = _ := by norm_num
  have henv := dfiEquation27IntegratedErrorEnvelope_nonneg
    hQ hf.one_le_X hf.one_le_Y hφ.U_pos a b K j hK
  change ‖∑ q ∈ Finset.Icc 1 K,
      (c * dfiEquation27ArithmeticCoefficient a b h q) * E q‖ ≤ _
  rw [hfactor, norm_mul]
  have hbase := hmain a b h K hK
  change ‖∑ q ∈ Finset.Icc 1 K,
      dfiEquation27ArithmeticCoefficient a b h q * E q‖ ≤ _ at hbase
  calc
    ‖c‖ * ‖∑ q ∈ Finset.Icc 1 K,
        dfiEquation27ArithmeticCoefficient a b h q * E q‖ ≤
      ‖c‖ * (C * (∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
        dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) :=
      mul_le_mul_of_nonneg_left hbase (norm_nonneg c)
    _ = C * (‖c‖ * (∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖)) *
        dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by ring
    _ ≤ C * ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (h.divisors.card : ℝ) *
        ((harmonic (K + 1) : ℚ) : ℝ)) *
        dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
      gcongr
    _ = _ := by ring

/-- Scale-independent small-modulus constant obtained from the delta-weight
and source derivative profiles. -/
noncomputable def dfiEquation27SmallProfileConstant
    (D Eprofile : ℕ → ℝ) (j : ℕ) (Cpsi CpsiSucc : ℝ)
    (Cf : ℕ → ℕ → ℝ) (Cφ : ℕ → ℝ) : ℝ :=
  (2 * dfiEquation18ProfileConstant D Eprofile j Cpsi CpsiSucc) *
    dfiEquation27SourceMajorantConstant Cf Cφ j

theorem dfiEquation27SmallProfileConstant_pos
    {Q P X Y U : ℝ} {w : DFIDeltaWeight Q}
    {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hfC : DFIEquation2Profile f P X Y Cf)
    {hφ : DFIRedundantCutoff φ U}
    (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (j : ℕ) {Cpsi CpsiSucc : ℝ}
    (hCpsi : 0 < Cpsi) (hCpsiSucc : 0 < CpsiSucc) :
    0 < dfiEquation27SmallProfileConstant
      D Eprofile j Cpsi CpsiSucc Cf Cφ := by
  unfold dfiEquation27SmallProfileConstant
  exact mul_pos
    (mul_pos two_pos (dfiEquation18ProfileConstant_pos
      hD.positive hEprofile.positive j hCpsi hCpsiSucc))
    (dfiEquation27SourceMajorantConstant_pos hfC hφC j)

/-- Uniform-in-scale form of the interpolated small-modulus branch of DFI
equation (27). -/
theorem norm_sum_Icc_inv_ab_dfiEquation27_reduced_main_error_le_interpolated_of_profiles
    {Q P X Y U : ℝ} (hQ : 0 < Q) {w : DFIDeltaWeight Q}
    {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ∀ (a b h K : ℕ), 0 < a → 0 < b → 0 < h → 1 ≤ K →
      ‖∑ q ∈ Finset.Icc 1 K,
          ((((a : ℂ) * b)⁻¹) *
            dfiEquation27ArithmeticCoefficient a b h q) *
            (dfiEquation27PhysicalMainIntegral w q a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
              dfiEquation27CentralIntegral a b
                (dfiReducedDenominator a q) (dfiReducedDenominator b q)
                (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ))‖ ≤
        dfiEquation27SmallProfileConstant
          D Eprofile j Cpsi CpsiSucc Cf Cφ *
          ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
            (h.divisors.card : ℝ) *
            ((harmonic (K + 1) : ℚ) : ℝ)) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
  have hmain := norm_sum_Icc_dfiEquation27_reduced_main_error_le_of_profiles
    hQ hD hEprofile hf hfC hbox hφ hφC hscale j hj
      hCpsi hpsi hCpsiSucc hpsiSucc
  intro a b h K ha hb hh hK
  let C : ℝ := dfiEquation27SmallProfileConstant
    D Eprofile j Cpsi CpsiSucc Cf Cφ
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let E : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) -
      dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ)
  have hfactor :
      (∑ q ∈ Finset.Icc 1 K,
          (c * dfiEquation27ArithmeticCoefficient a b h q) * E q) =
        c * ∑ q ∈ Finset.Icc 1 K,
          dfiEquation27ArithmeticCoefficient a b h q * E q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  have harithRaw :=
    sum_Ioo_norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_le_interpolated
      a b h 0 (K + 1) ha hb hh delta hdelta0 hdelta1
  have hinterval : Finset.Ioo 0 (K + 1) = Finset.Icc 1 K := by
    ext q
    simp only [Finset.mem_Ioo, Finset.mem_Icc]
    omega
  rw [hinterval] at harithRaw
  have harith :
      ‖c‖ * (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) ≤
        (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          ((harmonic (K + 1) : ℚ) : ℝ) := by
    calc
      ‖c‖ * (∑ q ∈ Finset.Icc 1 K,
          ‖dfiEquation27ArithmeticCoefficient a b h q‖) =
        ∑ q ∈ Finset.Icc 1 K,
          ‖c * dfiEquation27ArithmeticCoefficient a b h q‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [norm_mul]
      _ ≤ (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (h.divisors.card : ℝ) *
          (((0 + 1 : ℕ) : ℝ) ^ (-delta) *
            ((harmonic (K + 1) : ℚ) : ℝ)) := by
        simpa only [c] using harithRaw
      _ = _ := by norm_num
  have henv := dfiEquation27IntegratedErrorEnvelope_nonneg
    hQ hf.one_le_X hf.one_le_Y hφ.U_pos a b K j hK
  change ‖∑ q ∈ Finset.Icc 1 K,
      (c * dfiEquation27ArithmeticCoefficient a b h q) * E q‖ ≤ _
  rw [hfactor, norm_mul]
  have hbase := hmain a b h K hK
  change ‖∑ q ∈ Finset.Icc 1 K,
      dfiEquation27ArithmeticCoefficient a b h q * E q‖ ≤ _ at hbase
  calc
    ‖c‖ * ‖∑ q ∈ Finset.Icc 1 K,
        dfiEquation27ArithmeticCoefficient a b h q * E q‖ ≤
      ‖c‖ * (C * (∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖) *
        dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [C,
        dfiEquation27SmallProfileConstant] using hbase) (norm_nonneg c)
    _ = C * (‖c‖ * (∑ q ∈ Finset.Icc 1 K,
        ‖dfiEquation27ArithmeticCoefficient a b h q‖)) *
        dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by ring
    _ ≤ C * ((((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (h.divisors.card : ℝ) *
        ((harmonic (K + 1) : ℚ) : ℝ)) *
        dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j := by
      have hC : 0 ≤ C := (dfiEquation27SmallProfileConstant_pos
        hD hEprofile hfC hφC j hCpsi hCpsiSucc).le
      gcongr
    _ = _ := by rfl

/-- Scale-independent constant for the central integral in equation (27). -/
noncomputable def dfiEquation27CentralProfileConstant
    (Cf : ℕ → ℕ → ℝ) (Cφ : ℕ → ℝ) : ℝ :=
  dfiEquation27SourceDerivativeConstant Cf Cφ 0 *
    dfiEquation27LogLeibnizConstant 0

theorem dfiEquation27CentralProfileConstant_pos
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hfC : DFIEquation2Profile f P X Y Cf)
    {hφ : DFIRedundantCutoff φ U}
    (hφC : DFIRedundantCutoffProfile hφ Cφ) :
    0 < dfiEquation27CentralProfileConstant Cf Cφ := by
  unfold dfiEquation27CentralProfileConstant
  exact mul_pos (dfiEquation27SourceDerivativeConstant_pos hfC hφC 0)
    (dfiEquation27LogLeibnizConstant_pos 0)

/-- The central integral in equation (27), with the reduced Voronoi
denominators substituted, has the same logarithmic envelope as the physical
main integral but no delta-kernel loss.  Both dyadic support projections are
used, giving the sharp factor `min X Y`. -/
theorem norm_dfiEquation27CentralIntegral_reduced_uniform_shift_le_of_profiles
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∀ (h : ℝ) (a b q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        dfiEquation27CentralProfileConstant Cf Cφ *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          min X Y := by
  let C : ℝ := dfiEquation27SourceDerivativeConstant Cf Cφ 0
  let K : ℝ := dfiEquation27CentralProfileConstant Cf Cφ
  have hC : 0 < C := by
    simpa only [C] using dfiEquation27SourceDerivativeConstant_pos hfC hφC 0
  have hK : 0 < K := by
    simpa only [K] using dfiEquation27CentralProfileConstant_pos hfC hφC
  have hpoint := norm_iteratedDeriv_dfiEquation27_sourceSliceFamily_le
    hf hfC hbox hφ hφC hscale 0
  intro h a b q hq
  let g : ℝ → ℂ := fun x =>
    dfiEquation27SourceSliceFamily a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) h x 0
  let LX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log q
  let LY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 2 * Real.log q
  let B : ℝ := K * LX * LY
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hLX : 0 ≤ LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 ≤ LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hB : 0 ≤ B := by positivity
  have hgInt : Integrable g := by
    simpa only [g] using integrable_dfiEquation27_source_center
      hf hbox hφ a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q)
  have hgContinuous : Continuous g := by
    have hcenterCD := (contDiff_uncurry_dfiEquation27_sourceSliceFamily
      (h := h)
      hf hbox hφ a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q)).comp (contDiff_prodMk_left (0 : ℝ))
    simpa only [g, Function.comp_apply, Function.uncurry_apply_pair] using
      hcenterCD.continuous
  have hgCont : Continuous (fun x => ‖g x‖) := hgContinuous.norm
  have hgBound (x : ℝ) : |‖g x‖| ≤ B := by
    rw [abs_of_nonneg (norm_nonneg _)]
    have hp := hpoint h a b (dfiReducedDenominator a q)
      (dfiReducedDenominator b q) x 0
    have hqa := abs_log_dfiReducedDenominator_le a q hq
    have hqb := abs_log_dfiReducedDenominator_le b q hq
    have hLXred : 0 ≤ 1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator a q : ℝ)| := by
      have : 0 ≤ Real.log (2 * X) :=
        Real.log_nonneg (by nlinarith [hf.one_le_X])
      positivity
    have hLYred : 0 ≤ 1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| +
          2 * |Real.log (dfiReducedDenominator b q : ℝ)| := by
      have : 0 ≤ Real.log (2 * Y) :=
        Real.log_nonneg (by nlinarith [hf.one_le_Y])
      positivity
    dsimp [g, B, K, LX, LY]
    simp only [iteratedDeriv_zero, pow_zero, mul_one] at hp
    calc
      ‖dfiEquation27SourceSliceFamily a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h x 0‖ ≤
          (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| +
                2 * |Real.log (dfiReducedDenominator a q : ℝ)|) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| +
                2 * |Real.log (dfiReducedDenominator b q : ℝ)|) *
            C * dfiEquation27LogLeibnizConstant 0 := hp
      _ ≤ (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
            C * dfiEquation27LogLeibnizConstant 0 := by
          gcongr
          exact (dfiEquation27LogLeibnizConstant_pos 0).le
      _ = (C * dfiEquation27LogLeibnizConstant 0) *
            (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) := by ring
  have hsuppX : Function.support (fun x => ‖g x‖) ⊆ Set.Icc X (2 * X) := by
    intro x hx
    exact support_dfiEquation27_source_center_subset
      (h := h) hbox a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q) (by simpa using hx)
  have hsuppY : Function.support (fun x => ‖g x‖) ⊆
      Set.Icc (Y + h) (2 * Y + h) := by
    intro x hx
    have hgx : g x ≠ 0 := by simpa using hx
    have hlocal : dfiLocalizedWeight f φ h x (x - h) ≠ 0 := by
      intro hz
      exact hgx (by simp [g, dfiEquation27SourceSliceFamily,
        dfiEquation27Slice, dfiEquation27C, hz])
    have hpMem : (x, x - h) ∈ Function.support
        (Function.uncurry (dfiLocalizedWeight f φ h)) := hlocal
    have hp := support_uncurry_dfiLocalizedWeight_subset hbox hpMem
    constructor <;> linarith [hp.2.1, hp.2.2]
  have hXbound : (∫ x : ℝ, ‖g x‖) ≤ X * B := by
    have h := integral_abs_le_interval_length_mul
      (fun x => ‖g x‖) hgCont
      (show X ≤ 2 * X by linarith [hf.one_le_X]) hsuppX hgBound
    calc
      (∫ x : ℝ, ‖g x‖) ≤ (2 * X - X) * B := by
        simpa [abs_of_nonneg, norm_nonneg] using h
      _ = X * B := by ring
  have hYbound : (∫ x : ℝ, ‖g x‖) ≤ Y * B := by
    have hraw := integral_abs_le_interval_length_mul
      (fun x => ‖g x‖) hgCont
      (show Y + h ≤ 2 * Y + h by linarith [hf.one_le_Y]) hsuppY hgBound
    calc
      (∫ x : ℝ, ‖g x‖) ≤ (2 * Y + h - (Y + h)) * B := by
        simpa [abs_of_nonneg, norm_nonneg] using hraw
      _ = Y * B := by ring
  have hnorm : ‖∫ x : ℝ, g x‖ ≤ ∫ x : ℝ, ‖g x‖ :=
    MeasureTheory.norm_integral_le_integral_norm _
  unfold dfiEquation27CentralIntegral
  have hfun : (fun x : ℝ =>
      dfiEquation27C a b (dfiReducedDenominator a q)
        (dfiReducedDenominator b q) (dfiLocalizedWeight f φ h) x (x - h)) =
      g := by
    funext x
    simp [g, dfiEquation27SourceSliceFamily, dfiEquation27Slice]
  rw [hfun]
  calc
    ‖∫ x : ℝ, g x‖ ≤ ∫ x : ℝ, ‖g x‖ := hnorm
    _ ≤ min (X * B) (Y * B) := le_min hXbound hYbound
    _ = min X Y * B := (min_mul_of_nonneg X Y hB).symm
    _ = dfiEquation27CentralProfileConstant Cf Cφ *
        LX * LY * min X Y := by
      ring

/-- Compatibility form of the explicit central-integral estimate. -/
theorem exists_norm_dfiEquation27CentralIntegral_reduced_uniform_shift_le
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : ℝ) (a b q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          min X Y := by
  refine ⟨dfiEquation27CentralProfileConstant Cf Cφ,
    dfiEquation27CentralProfileConstant_pos hfC hφC, ?_⟩
  exact norm_dfiEquation27CentralIntegral_reduced_uniform_shift_le_of_profiles
    hf hfC hbox hφ hφC hscale

/-- Fixed-shift projection of the uniform central-integral estimate. -/
theorem exists_norm_dfiEquation27CentralIntegral_reduced_le
    {P X Y U h : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 2 * Real.log q) *
          min X Y := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_uniform_shift_le
      hf hfC hbox hφ hφC hscale
  exact ⟨K, hK, hbound h⟩

/-- The two logarithmic factors in the reduced central integral cost an
arbitrarily small positive power of the modulus.  The constant is chosen
before `q` and the shift, which is the uniformity needed in the tail of
source equation (27). -/
theorem exists_norm_dfiEquation27CentralIntegral_reduced_le_rpow
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ) (q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤ C * (q : ℝ) ^ beta := by
  obtain ⟨K, hK, hcentral⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_uniform_shift_le
      hf hfC hbox hφ hφC hscale
  let AX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant|
  let AY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant|
  let E : ℝ := 4 * beta⁻¹
  let C : ℝ := K * (AX + E) * (AY + E) * min X Y
  have hAX : 0 < AX := by
    dsimp [AX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hAY : 0 < AY := by
    dsimp [AY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hE : 0 < E := by
    dsimp [E]
    positivity
  have hmin : 0 < min X Y := by
    exact lt_min (zero_lt_one.trans_le hf.one_le_X)
      (zero_lt_one.trans_le hf.one_le_Y)
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  intro h q hq
  have hraw := hcentral (h : ℝ) a b q hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hhalf : (0 : ℝ) < beta / 2 := by positivity
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ (beta / 2) :=
    Real.one_le_rpow hqOne hhalf.le
  have hlog := Real.log_natCast_le_rpow_div q hhalf
  have hlog' : 2 * Real.log q ≤ E * (q : ℝ) ^ (beta / 2) := by
    calc
      2 * Real.log q ≤ 2 * ((q : ℝ) ^ (beta / 2) / (beta / 2)) := by
        gcongr
      _ = E * (q : ℝ) ^ (beta / 2) := by
        dsimp [E]
        field_simp [ne_of_gt hbeta]
        ring
  have hAXpow : AX + 2 * Real.log q ≤
      (AX + E) * (q : ℝ) ^ (beta / 2) := by
    have hbase : AX ≤ AX * (q : ℝ) ^ (beta / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAX.le]
    nlinarith
  have hAYpow : AY + 2 * Real.log q ≤
      (AY + E) * (q : ℝ) ^ (beta / 2) := by
    have hbase : AY ≤ AY * (q : ℝ) ^ (beta / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAY.le]
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrpow : (q : ℝ) ^ (beta / 2) * (q : ℝ) ^ (beta / 2) =
      (q : ℝ) ^ beta := by
    rw [← Real.rpow_add hqR]
    congr 1
    ring
  calc
    ‖dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) h‖ ≤
        K * (AX + 2 * Real.log q) * (AY + 2 * Real.log q) * min X Y :=
      hraw
    _ ≤ K * ((AX + E) * (q : ℝ) ^ (beta / 2)) *
        ((AY + E) * (q : ℝ) ^ (beta / 2)) * min X Y := by
      gcongr
    _ = C * (q : ℝ) ^ beta := by
      dsimp [C]
      rw [← hrpow]
      ring

/-- Uniform-in-`a,b` version of the reduced central-integral power bound.
The constant is selected before the arithmetic parameters; their logarithms
remain explicit so that the negative `(ab)` power from equation (26) can
absorb them in the final source theorem. -/
theorem norm_dfiEquation27CentralIntegral_reduced_uniform_ab_le_rpow_of_profiles
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ (a b h q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        dfiEquation27CentralProfileConstant Cf Cφ *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          min X Y * (q : ℝ) ^ beta := by
  let K : ℝ := dfiEquation27CentralProfileConstant Cf Cφ
  have hK : 0 < K := by
    simpa only [K] using dfiEquation27CentralProfileConstant_pos hfC hφC
  have hcentral :=
    norm_dfiEquation27CentralIntegral_reduced_uniform_shift_le_of_profiles
      hf hfC hbox hφ hφC hscale
  intro a b h q hq
  change ‖dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) h‖ ≤
    K *
      (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
      min X Y * (q : ℝ) ^ beta
  let AX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant|
  let AY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant|
  let E : ℝ := 4 * beta⁻¹
  have hAX : 0 < AX := by
    dsimp [AX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hAY : 0 < AY := by
    dsimp [AY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hhalf : (0 : ℝ) < beta / 2 := by positivity
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ (beta / 2) :=
    Real.one_le_rpow hqOne hhalf.le
  have hlog := Real.log_natCast_le_rpow_div q hhalf
  have hlog' : 2 * Real.log q ≤ E * (q : ℝ) ^ (beta / 2) := by
    calc
      2 * Real.log q ≤ 2 * ((q : ℝ) ^ (beta / 2) / (beta / 2)) := by
        gcongr
      _ = E * (q : ℝ) ^ (beta / 2) := by
        dsimp [E]
        field_simp [ne_of_gt hbeta]
        ring
  have hAXpow : AX + 2 * Real.log q ≤
      (AX + E) * (q : ℝ) ^ (beta / 2) := by
    have hbase : AX ≤ AX * (q : ℝ) ^ (beta / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAX.le]
    nlinarith
  have hAYpow : AY + 2 * Real.log q ≤
      (AY + E) * (q : ℝ) ^ (beta / 2) := by
    have hbase : AY ≤ AY * (q : ℝ) ^ (beta / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAY.le]
    nlinarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrpow : (q : ℝ) ^ (beta / 2) * (q : ℝ) ^ (beta / 2) =
      (q : ℝ) ^ beta := by
    rw [← Real.rpow_add hqR]
    congr 1
    ring
  have hmin : 0 ≤ min X Y := le_min
    (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hraw := hcentral (h : ℝ) a b q hq
  calc
    ‖dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) h‖ ≤
        K * (AX + 2 * Real.log q) * (AY + 2 * Real.log q) * min X Y :=
      hraw
    _ ≤ K * ((AX + E) * (q : ℝ) ^ (beta / 2)) *
        ((AY + E) * (q : ℝ) ^ (beta / 2)) * min X Y := by
      gcongr
    _ = K *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          min X Y * (q : ℝ) ^ beta := by
      dsimp [AX, AY, E]
      rw [← hrpow]
      ring

/-- Compatibility form of the profile-uniform central-integral power bound. -/
theorem exists_norm_dfiEquation27CentralIntegral_reduced_uniform_ab_le_rpow
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a b h q : ℕ), 0 < q →
      ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ ≤
        K *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          min X Y * (q : ℝ) ^ beta := by
  refine ⟨dfiEquation27CentralProfileConstant Cf Cφ,
    dfiEquation27CentralProfileConstant_pos hfC hφC, ?_⟩
  exact norm_dfiEquation27CentralIntegral_reduced_uniform_ab_le_rpow_of_profiles
    hf hfC hbox hφ hφC hscale hbeta

/-- The elementary comparison series used for the logarithmic equation-(27)
tail is a `p`-series of exponent `3/2`. -/
theorem summable_natCast_inv_sq_mul_rpow_half :
    Summable (fun q : ℕ =>
      (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ))) := by
  have hsum : Summable (fun q : ℕ => (q : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  convert hsum using 1
  funext q
  by_cases hq : q = 0
  · simp [hq]
  · have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
    calc
      ((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ) =
          (q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ (1 / 2 : ℝ) := by
        congr 1
        calc
          ((q : ℝ) ^ 2)⁻¹ = ((q : ℝ) ^ (2 : ℝ))⁻¹ :=
            congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (q : ℝ) 2).symm
          _ = (q : ℝ) ^ (-(2 : ℝ)) :=
            (Real.rpow_neg hqpos.le (2 : ℝ)).symm
      _ = (q : ℝ) ^ (-(2 : ℝ) + (1 / 2 : ℝ)) := by
        rw [Real.rpow_add hqpos]
      _ = (q : ℝ) ^ (-(3 / 2 : ℝ)) := by norm_num

/-- The exact integrated summand of DFI equation (3)/(27), including the
external Jacobian `(ab)⁻¹`. -/
noncomputable def dfiEquation27CentralSummand
    (a b h : ℕ) (F : ℝ → ℝ → ℂ) (q : ℕ) : ℂ :=
  (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q) F h

/-- DFI's infinite Ramanujan main term after integration against the source
test function.  Absolute summability is proved below. -/
noncomputable def dfiEquation27CentralSeries
    (a b h : ℕ) (F : ℝ → ℝ → ℂ) : ℂ :=
  ∑' q : ℕ, dfiEquation27CentralSummand a b h F q

/-- The redundant equation-(21) cutoff disappears identically on the
central line `x-y=h`.  Thus the Ramanujan main series produced by the delta
method is exactly the source equation-(3) main term, not a smoothed proxy. -/
theorem dfiEquation27CentralSeries_localizedWeight_eq
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U) (a b h : ℕ) :
    dfiEquation27CentralSeries a b h (dfiLocalizedWeight f φ h) =
      dfiEquation27CentralSeries a b h f := by
  unfold dfiEquation27CentralSeries
  apply tsum_congr
  intro q
  unfold dfiEquation27CentralSummand
  congr 1
  unfold dfiEquation27CentralIntegral
  apply integral_congr_ae
  filter_upwards with x
  unfold dfiEquation27C
  rw [dfiLocalizedWeight_eq_of_sub_eq hφ]
  ring

/-- Absolute convergence of the literal equation-(27) central series.  The
two logarithms cost only `q^(1/2)`, leaving the summable exponent `-3/2`
after the inverse-square arithmetic coefficient. -/
theorem summable_dfiEquation27CentralSummand
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) :
    Summable (fun q : ℕ =>
      dfiEquation27CentralSummand a b h
        (dfiLocalizedWeight f φ h) q) := by
  obtain ⟨K, hK, hcentral⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_le
      (h := (h : ℝ)) hf hfC hbox hφ hφC hscale
  let AX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant|
  let AY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant|
  let D : ℝ :=
    ‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
      (AX + 8) * (AY + 8) * min X Y
  have hAX : 0 ≤ AX := by
    dsimp [AX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hAY : 0 ≤ AY := by
    dsimp [AY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hmin : 0 ≤ min X Y :=
    le_min (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hD : 0 ≤ D := by positivity
  have hmajor : Summable (fun q : ℕ =>
      D * (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ))) :=
    summable_natCast_inv_sq_mul_rpow_half.mul_left D
  apply Summable.of_norm_bounded hmajor
  intro q
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_le_rpow hqOne (by norm_num)
    have hlog := Real.log_natCast_le_rpow_div q
      (by norm_num : (0 : ℝ) < 1 / 4)
    have hLXpow : AX + 2 * Real.log q ≤
        (AX + 8) * (q : ℝ) ^ (1 / 4 : ℝ) := by
      have hAXpow : AX ≤ AX * (q : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAX]
      have hlog' : 2 * Real.log q ≤
          8 * (q : ℝ) ^ (1 / 4 : ℝ) := by
        norm_num at hlog ⊢
        linarith
      nlinarith
    have hLYpow : AY + 2 * Real.log q ≤
        (AY + 8) * (q : ℝ) ^ (1 / 4 : ℝ) := by
      have hAYpow : AY ≤ AY * (q : ℝ) ^ (1 / 4 : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAY]
      have hlog' : 2 * Real.log q ≤
          8 * (q : ℝ) ^ (1 / 4 : ℝ) := by
        norm_num at hlog ⊢
        linarith
      nlinarith
    have hhalf :
        (q : ℝ) ^ (1 / 4 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ) =
          (q : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < q)]
      norm_num
    rw [dfiEquation27CentralSummand, norm_mul, norm_mul]
    have hprod := mul_le_mul
      (norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
        a b h q ha hb hh)
      (hcentral a b q hq)
      (norm_nonneg (dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) h)) (by positivity)
    calc
      ‖((a : ℂ) * b)⁻¹‖ * ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖ =
        ‖((a : ℂ) * b)⁻¹‖ *
          (‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            ‖dfiEquation27CentralIntegral a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ h) h‖) := by ring
      _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
          ((((a * b * h ^ 2 : ℕ) : ℝ)) * ((q : ℝ) ^ 2)⁻¹ *
            (K * (AX + 2 * Real.log q) * (AY + 2 * Real.log q) * min X Y)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ = (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
            min X Y) * ((q : ℝ) ^ 2)⁻¹ *
          (AX + 2 * Real.log q) * (AY + 2 * Real.log q) := by ring
      _ ≤ (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
            min X Y) * ((q : ℝ) ^ 2)⁻¹ *
          ((AX + 8) * (q : ℝ) ^ (1 / 4 : ℝ)) *
          ((AY + 8) * (q : ℝ) ^ (1 / 4 : ℝ)) := by
        gcongr
      _ = D * (((q : ℝ) ^ 2)⁻¹ *
          ((q : ℝ) ^ (1 / 4 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ))) := by
        dsimp [D]
        ring
      _ = D * (((q : ℝ) ^ 2)⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [hhalf]

/-- Source-strength pointwise majorant for the integrated equation-(27)
central summand.  For every `0 < ε < 1`, the two logarithms in the central
integral cost only `q^ε`; the arithmetic coefficient still supplies
`q⁻²`.  This is the quantitative input for truncating the infinite
Ramanujan main term at modulus `Q`. -/
theorem exists_norm_dfiEquation27CentralSummand_le_epsilon
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ q : ℕ, 0 < q →
      ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) q‖ ≤
        D * (q : ℝ) ^ (-(2 - ε)) := by
  obtain ⟨K, hK, hcentral⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_le
      (h := (h : ℝ)) hf hfC hbox hφ hφC hscale
  let AX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant|
  let AY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant|
  let E : ℝ := 4 * ε⁻¹
  let D : ℝ :=
    ‖(((a : ℂ) * b)⁻¹)‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
      (AX + E) * (AY + E) * min X Y
  have hAX : 0 ≤ AX := by
    dsimp [AX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hAY : 0 ≤ AY := by
    dsimp [AY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hmin : 0 ≤ min X Y :=
    le_min (zero_le_one.trans hf.one_le_X) (zero_le_one.trans hf.one_le_Y)
  have hD : 0 ≤ D := by positivity
  refine ⟨D, hD, ?_⟩
  intro q hq
  letI : NeZero q := ⟨hq.ne'⟩
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hδ0 : (0 : ℝ) < ε / 2 := by positivity
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ (ε / 2) :=
    Real.one_le_rpow hqOne hδ0.le
  have hlog := Real.log_natCast_le_rpow_div q hδ0
  have hlog' : 2 * Real.log q ≤ E * (q : ℝ) ^ (ε / 2) := by
    calc
      2 * Real.log q ≤ 2 * ((q : ℝ) ^ (ε / 2) / (ε / 2)) := by
        gcongr
      _ = E * (q : ℝ) ^ (ε / 2) := by
        dsimp [E]
        field_simp [ne_of_gt hε0]
        ring
  have hLXpow : AX + 2 * Real.log q ≤
      (AX + E) * (q : ℝ) ^ (ε / 2) := by
    have hAXpow : AX ≤ AX * (q : ℝ) ^ (ε / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAX]
    nlinarith
  have hLYpow : AY + 2 * Real.log q ≤
      (AY + E) * (q : ℝ) ^ (ε / 2) := by
    have hAYpow : AY ≤ AY * (q : ℝ) ^ (ε / 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hqPowOne hAY]
    nlinarith
  have hεpow :
      (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ ε := by
    rw [← Real.rpow_add hqreal]
    congr 1
    ring
  have hinvSq : ((q : ℝ) ^ 2)⁻¹ = (q : ℝ) ^ (-(2 : ℝ)) := by
    calc
      ((q : ℝ) ^ 2)⁻¹ = ((q : ℝ) ^ (2 : ℝ))⁻¹ :=
        congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast (q : ℝ) 2).symm
      _ = (q : ℝ) ^ (-(2 : ℝ)) :=
        (Real.rpow_neg hqreal.le (2 : ℝ)).symm
  rw [dfiEquation27CentralSummand, norm_mul, norm_mul]
  have hprod := mul_le_mul
    (norm_dfiEquation27ArithmeticCoefficient_le_inv_sq
      a b h q ha hb hh)
    (hcentral a b q hq)
    (norm_nonneg (dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) h)) (by positivity)
  calc
    ‖((a : ℂ) * b)⁻¹‖ * ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
        ‖dfiEquation27CentralIntegral a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q)
          (dfiLocalizedWeight f φ h) h‖ =
      ‖((a : ℂ) * b)⁻¹‖ *
        (‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖) := by ring
    _ ≤ ‖((a : ℂ) * b)⁻¹‖ *
        ((((a * b * h ^ 2 : ℕ) : ℝ)) * ((q : ℝ) ^ 2)⁻¹ *
          (K * (AX + 2 * Real.log q) * (AY + 2 * Real.log q) * min X Y)) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
          min X Y) * ((q : ℝ) ^ 2)⁻¹ *
        (AX + 2 * Real.log q) * (AY + 2 * Real.log q) := by ring
    _ ≤ (‖((a : ℂ) * b)⁻¹‖ * (((a * b * h ^ 2 : ℕ) : ℝ)) * K *
          min X Y) * ((q : ℝ) ^ 2)⁻¹ *
        ((AX + E) * (q : ℝ) ^ (ε / 2)) *
        ((AY + E) * (q : ℝ) ^ (ε / 2)) := by
      gcongr
    _ = D * (((q : ℝ) ^ 2)⁻¹ *
        ((q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (ε / 2))) := by
      dsimp [D]
      ring
    _ = D * ((q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ ε) := by
      rw [hεpow, hinvSq]
    _ = D * (q : ℝ) ^ (-(2 : ℝ) + ε) := by
      rw [Real.rpow_add hqreal]
    _ = D * (q : ℝ) ^ (-(2 - ε)) := by
      congr 2
      ring

/-- Quantitative tail of the integrated central series in DFI equation
(27).  This is the exact `Q⁻¹⁺ε` truncation estimate used in the passage
from the finite delta-symbol sum to the infinite Ramanujan main term. -/
theorem exists_tsum_norm_dfiEquation27CentralSummand_tail_le_epsilon
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (L : ℕ) (hL : 0 < L) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (L + (j + 1))‖ ≤
        D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := by
  obtain ⟨D, hD, hpoint⟩ :=
    exists_norm_dfiEquation27CentralSummand_le_epsilon
      hf hfC hbox hφ hφC hscale a b h ha hb hh hε0 hε1
  refine ⟨D, hD, ?_⟩
  have hp : 1 < 2 - ε := by linarith
  have hSeries := tsum_nat_add_one_rpow_neg_le
    (L := (L : ℝ)) (p := 2 - ε) (Nat.cast_pos.mpr hL) hp
  have hSeries' :
      ∑' j : ℕ, ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) ≤
        (L : ℝ) ^ (-(1 - ε)) / (1 - ε) := by
    convert hSeries using 1
    all_goals ring_nf
  have hPowerSummable : Summable (fun j : ℕ =>
      ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 - ε))) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hshift := (summable_nat_add_iff (L + 1)).2 hbase
    simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hshift
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (L + (j + 1))‖ ≤
          ∑ j ∈ Finset.range N,
            D * ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) := by
        gcongr with j hj
        have hq : 0 < L + (j + 1) := by omega
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
          add_left_comm] using hpoint (L + (j + 1)) hq
      _ = D * ∑ j ∈ Finset.range N,
          ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) := by
        rw [Finset.mul_sum]
      _ ≤ D * ∑' j : ℕ,
          ((L : ℝ) + (j + 1 : ℕ)) ^ (-(2 - ε)) := by
        gcongr
        exact hPowerSummable.sum_le_tsum (Finset.range N)
          (fun j _ => Real.rpow_nonneg (by positivity) _)
      _ ≤ D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) :=
        mul_le_mul_of_nonneg_left hSeries' hD

/-- Source-sharp tail of the integrated Ramanujan main series.  Unlike the
older convergence majorant, this theorem uses equation (26) before summing
over the modulus.  Hence the shift contributes only `h^delta`, and the
strict cutoff retains the full negative power supplied by the sparse
multiples. -/
theorem exists_tsum_norm_dfiEquation27CentralSummand_tail_le_source_sharp
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (alpha theta beta delta : ℝ)
    (halpha : 0 < alpha) (htheta : 0 < theta)
    (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hexp : 2 - beta = 1 + alpha + theta) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ,
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        C * (h : ℝ) ^ delta * ((K : ℝ) + 1) ^ (-alpha) *
          (1 + theta⁻¹) := by
  obtain ⟨C₀, hC₀, hcentral⟩ :=
    exists_norm_dfiEquation27CentralIntegral_reduced_le_rpow
      hf hfC hbox hφ hφC hscale a b hbeta
  let D : ℝ := ‖(((a : ℂ) * b)⁻¹)‖ * C₀
  let C : ℝ := D * ((a * b : ℕ) : ℝ) * divisorEpsilonConstant delta
  have hD : 0 < D := by
    dsimp [D]
    have hab : ((a : ℂ) * b) ≠ 0 := by
      exact mul_ne_zero (Nat.cast_ne_zero.mpr ha.ne')
        (Nat.cast_ne_zero.mpr hb.ne')
    exact mul_pos (norm_pos_iff.mpr (inv_ne_zero hab)) hC₀
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos hD (by exact_mod_cast Nat.mul_pos ha hb))
      (divisorEpsilonConstant_pos delta)
  refine ⟨C, hC, ?_⟩
  intro K
  let A : ℕ → ℝ := fun q =>
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
  have hAtail : Summable (fun q : ℕ => if K < q then A q else 0) := by
    dsimp [A]
    exact summable_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail
      K a b h ha hb hh alpha theta beta halpha htheta hexp
  have hAshift : Summable (fun j : ℕ => A (K + (j + 1))) :=
    (summable_nat_add_one_iff_if_nat_lt A K).2 hAtail
  have hpoint (j : ℕ) :
      ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        D * A (K + (j + 1)) := by
    let q := K + (j + 1)
    have hq : 0 < q := by dsimp [q]; omega
    have hint := hcentral h q hq
    dsimp [dfiEquation27CentralSummand, A, D]
    rw [norm_mul, norm_mul]
    calc
      ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖ ≤
        ‖((a : ℂ) * b)⁻¹‖ *
          ‖dfiEquation27ArithmeticCoefficient a b h q‖ *
          (C₀ * (q : ℝ) ^ beta) := by
        gcongr
      _ = (‖((a : ℂ) * b)⁻¹‖ * C₀) *
          (‖dfiEquation27ArithmeticCoefficient a b h q‖ *
            (q : ℝ) ^ beta) := by ring
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N,
          ‖dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        ∑ j ∈ Finset.range N, D * A (K + (j + 1)) := by
          gcongr with j hj
          exact hpoint j
      _ = D * ∑ j ∈ Finset.range N, A (K + (j + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ D * ∑' j : ℕ, A (K + (j + 1)) := by
        gcongr
        exact hAshift.sum_le_tsum (Finset.range N)
          (fun j _ => by dsimp [A]; positivity)
      _ = D * (∑' q : ℕ, if K < q then A q else 0) := by
        rw [tsum_if_nat_lt_eq_tsum_nat_add_one]
      _ ≤ D * (((a * b : ℕ) : ℝ) * divisorEpsilonConstant delta *
          (h : ℝ) ^ delta * ((K : ℝ) + 1) ^ (-alpha) *
            (1 + theta⁻¹)) := by
        gcongr
        dsimp [A]
        exact
          tsum_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le_epsilon
            K a b h ha hb hh alpha theta beta delta
              halpha htheta hdelta hexp
      _ = C * (h : ℝ) ^ delta * ((K : ℝ) + 1) ^ (-alpha) *
          (1 + theta⁻¹) := by
        dsimp [C]
        ring

/-- Source-uniform central-series tail with the exact external `(ab)⁻¹`
factor incorporated before summation.  The constant is selected before
`a,b,h`; all arithmetic dependence remains in the displayed expression. -/
theorem tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated_of_profiles
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (rho alpha theta beta : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (htheta : 0 < theta) (hbeta : 0 < beta)
    (hexp : rho - beta = alpha + theta) :
    ∀ (a b h K : ℕ),
      0 < a → 0 < b → 0 < h →
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        dfiEquation27CentralProfileConstant Cf Cφ *
          (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
          (h.divisors.card : ℝ) *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          min X Y * ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
  let C : ℝ := dfiEquation27CentralProfileConstant Cf Cφ
  have hC : 0 < C := by
    simpa only [C] using dfiEquation27CentralProfileConstant_pos hfC hφC
  have hcentral :=
    norm_dfiEquation27CentralIntegral_reduced_uniform_ab_le_rpow_of_profiles
      hf hfC hbox hφ hφC hscale hbeta
  intro a b h K ha hb hh
  change ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
      (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
    C * (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
      (h.divisors.card : ℝ) *
      (1 + Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
      (1 + Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
      min X Y * ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹)
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let LX : ℝ := 1 + Real.log (2 * X) + |Real.log a| +
    2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹
  let LY : ℝ := 1 + Real.log (2 * Y) + |Real.log b| +
    2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹
  let D : ℝ := C * LX * LY * min X Y
  let A : ℕ → ℝ := fun q =>
    ‖c * dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
  have hLX : 0 < LX := by
    dsimp [LX]
    have : 0 ≤ Real.log (2 * X) :=
      Real.log_nonneg (by nlinarith [hf.one_le_X])
    positivity
  have hLY : 0 < LY := by
    dsimp [LY]
    have : 0 ≤ Real.log (2 * Y) :=
      Real.log_nonneg (by nlinarith [hf.one_le_Y])
    positivity
  have hmin : 0 < min X Y := lt_min
    (zero_lt_one.trans_le hf.one_le_X) (zero_lt_one.trans_le hf.one_le_Y)
  have hD : 0 < D := by dsimp [D]; positivity
  let alpha0 : ℝ := alpha + (1 - rho)
  have halpha0 : 0 < alpha0 := by dsimp [alpha0]; linarith
  have hexp0 : 2 - beta = 1 + alpha0 + theta := by
    dsimp [alpha0]
    linarith
  have hbase : Summable (fun q : ℕ => if K < q then
      ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) :=
    summable_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail
      K a b h ha hb hh alpha0 theta beta halpha0 htheta hexp0
  have hAtail : Summable (fun q : ℕ => if K < q then A q else 0) := by
    have hs := hbase.mul_left ‖c‖
    apply hs.congr
    intro q
    by_cases hKq : K < q
    · simp only [hKq, if_true, A, norm_mul]
      ring
    · simp [hKq]
  have hAshift : Summable (fun j : ℕ => A (K + (j + 1))) :=
    (summable_nat_add_one_iff_if_nat_lt A K).2 hAtail
  have hpoint (j : ℕ) :
      ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        D * A (K + (j + 1)) := by
    let q : ℕ := K + (j + 1)
    have hq : 0 < q := by dsimp [q]; omega
    have hint := hcentral a b h q hq
    dsimp [dfiEquation27CentralSummand, A, D, LX, LY, c]
    rw [norm_mul]
    calc
      ‖((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q‖ *
          ‖dfiEquation27CentralIntegral a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            (dfiLocalizedWeight f φ h) h‖ ≤
        ‖((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q‖ *
          (C *
            (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
            min X Y * (q : ℝ) ^ beta) := by
          gcongr
      _ = (C *
            (1 + Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
            (1 + Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
            min X Y) *
          (‖((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q‖ *
            (q : ℝ) ^ beta) := by ring
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact norm_nonneg _
  · intro N
    calc
      ∑ j ∈ Finset.range N,
          ‖dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        ∑ j ∈ Finset.range N, D * A (K + (j + 1)) := by
          gcongr with j hj
          exact hpoint j
      _ = D * ∑ j ∈ Finset.range N, A (K + (j + 1)) := by
        rw [Finset.mul_sum]
      _ ≤ D * ∑' j : ℕ, A (K + (j + 1)) := by
        gcongr
        exact hAshift.sum_le_tsum (Finset.range N)
          (fun j _ => by dsimp [A]; positivity)
      _ = D * (∑' q : ℕ, if K < q then A q else 0) := by
        rw [tsum_if_nat_lt_eq_tsum_nat_add_one]
      _ ≤ D *
          (((a * b : ℕ) : ℝ) ^ (-1 + rho) * h.divisors.card *
            ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹)) := by
        gcongr
        dsimp [A, c]
        exact
          tsum_norm_inv_ab_mul_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le
            K a b h ha hb hh rho alpha theta beta
              hrho0 hrho1 halpha htheta hexp
      _ = C *
          (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
          (h.divisors.card : ℝ) *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          min X Y * ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
        dsimp [D, LX, LY]
        ring

/-- Compatibility form of the profile-uniform central-series tail bound. -/
theorem exists_tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated
    {P X Y U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y)
    (rho alpha theta beta : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (htheta : 0 < theta) (hbeta : 0 < beta)
    (hexp : rho - beta = alpha + theta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b h K : ℕ),
      0 < a → 0 < b → 0 < h →
      ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
          (dfiLocalizedWeight f φ h) (K + (j + 1))‖ ≤
        C *
          (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
          (h.divisors.card : ℝ) *
          (1 + Real.log (2 * X) + |Real.log a| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          (1 + Real.log (2 * Y) + |Real.log b| +
            2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
          min X Y * ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
  refine ⟨dfiEquation27CentralProfileConstant Cf Cφ,
    dfiEquation27CentralProfileConstant_pos hfC hφC, ?_⟩
  exact tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated_of_profiles
    hf hfC hbox hφ hφC hscale rho alpha theta beta
      hrho0 hrho1 halpha htheta hbeta hexp

/-- The divisor-variable integral `||I||` of DFI equation (30), including
the two positive scaling Jacobians. -/
noncomputable def dfiEquation30DivisorAbsoluteIntegral
    {Q : ℝ} (w : DFIDeltaWeight Q) (q a b : ℕ)
    (F : ℝ → ℝ → ℂ) (h : ℝ) : ℝ :=
  ((a : ℝ) * b)⁻¹ * dfiEquation30PhysicalAbsoluteIntegral w q F h

/-- Literal source equation (30):
`||I|| ≪ (ab)⁻¹ min(X,Y) log Q`. -/
theorem dfiEquation30
    {Q P X Y U h : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ), 0 < q →
      dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h ≤
        K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
  obtain ⟨K, hK, hphysical⟩ :=
    dfiEquation30_physical_log_bound w hf hbox hφ hscale hQ hU
  refine ⟨K, hK, ?_⟩
  intro q hq
  unfold dfiEquation30DivisorAbsoluteIntegral
  have hab : 0 ≤ ((a : ℝ) * b)⁻¹ := by positivity
  calc
    ((a : ℝ) * b)⁻¹ *
        dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
      ((a : ℝ) * b)⁻¹ * (K * min X Y * Real.log Q) :=
        mul_le_mul_of_nonneg_left (hphysical h q hq) hab
    _ = K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by ring

/-- Source-uniform quantifier order for DFI equation (30).  The physical
The constant is chosen before the shift and both divisor dilations. -/
theorem exists_dfiEquation30_uniform_all
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (h : ℝ) (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q →
      dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h ≤
        K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
  obtain ⟨K, hK, hphysical⟩ :=
    dfiEquation30_physical_log_bound w hf hbox hφ hscale hQ hU
  refine ⟨K, hK, ?_⟩
  intro h a b ha hb q hq
  unfold dfiEquation30DivisorAbsoluteIntegral
  have hab : 0 ≤ ((a : ℝ) * b)⁻¹ := by positivity
  calc
    ((a : ℝ) * b)⁻¹ *
        dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
      ((a : ℝ) * b)⁻¹ * (K * min X Y * Real.log Q) :=
        mul_le_mul_of_nonneg_left (hphysical h q hq) hab
    _ = K * ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by ring

/-- Profile-explicit source-uniform form of DFI equation (30), with the
The constant chosen before the physical scales, shift, divisor dilations, and
delta modulus. -/
theorem dfiEquation30_uniform_all_of_profiles
    {Q P X Y U : ℝ} {w : DFIDeltaWeight Q}
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2) :
    ∀ (h : ℝ) (a b : ℕ), 0 < a → 0 < b →
      ∀ (q : ℕ), 0 < q →
      dfiEquation30DivisorAbsoluteIntegral w q a b
          (dfiLocalizedWeight f φ h) h ≤
        ((dfiEquation2FiniteConstant Cf 0 *
            dfiCutoffFiniteConstant Cφ 0) *
          ((24 * max (Cw 0) (Cw 1)) *
            (2 / Real.log 2 + 4))) *
          ((a : ℝ) * b)⁻¹ * min X Y * Real.log Q := by
  intro h a b ha hb q hq
  have hphysical := dfiEquation30_physical_log_bound_of_profiles
    hf hfC hbox hφ hφC hscale hwC hQ hU h q hq
  unfold dfiEquation30DivisorAbsoluteIntegral
  have hab : 0 ≤ ((a : ℝ) * b)⁻¹ := by positivity
  calc
    ((a : ℝ) * b)⁻¹ *
        dfiEquation30PhysicalAbsoluteIntegral w q
          (dfiLocalizedWeight f φ h) h ≤
      ((a : ℝ) * b)⁻¹ *
        (((dfiEquation2FiniteConstant Cf 0 *
              dfiCutoffFiniteConstant Cφ 0) *
            ((24 * max (Cw 0) (Cw 1)) *
              (2 / Real.log 2 + 4))) *
            min X Y * Real.log Q) :=
      mul_le_mul_of_nonneg_left hphysical hab
    _ = _ := by ring

/-- The totalized equation-(24) main branch is exactly the equation-(27)
arithmetic coefficient times the physical main integral, including the
two divisor-variable Jacobians.  This is the source-entry bridge needed to
apply the analytic equation-(27) estimate to equation (22). -/
theorem dfiEquation24MainTotal_eq_equation27_summand
    {Q : ℝ} (w : DFIDeltaWeight Q) (a b h q : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℝ → ℝ → ℂ) :
    dfiEquation24MainTotal q a b (h : ℤ)
        (dfiEquation23Weight w F a b (h : ℤ) q) =
      (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
        dfiEquation27PhysicalMainIntegral w q a b
          (dfiReducedDenominator a q) (dfiReducedDenominator b q) F (h : ℝ) := by
  by_cases hq0 : q = 0
  · subst q
    simp [dfiEquation24MainTotal, dfiEquation27ArithmeticCoefficient]
  · have hq : 0 < q := Nat.pos_of_ne_zero hq0
    letI : NeZero q := ⟨hq0⟩
    rw [dfiEquation24MainTotal, dif_neg hq0]
    rw [dfiEquation27_main_summand_exact w a b q ha hb hab F (h : ℤ)]
    rw [dfiEquation27ArithmeticCoefficient_eq]
    rw [ramanujanSumInt_neg]
    rw [ramanujanSumInt_ofNat_eq_ramanujanSum, star_ramanujanSum]
    rw [dfiReducedModulus_denominator_eq,
      dfiReducedModulus_denominator_eq]
    push_cast
    field_simp

/-- The complete finite double-main contribution in equations (22)--(24)
is the finite physical equation-(27) sum. -/
theorem sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
    {Q : ℝ} (w : DFIDeltaWeight Q) (a b h : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (F : ℝ → ℝ → ℂ) :
    (∑ q ∈ dfiEquation22Moduli Q,
      dfiEquation24MainTotal q a b (h : ℤ)
        (dfiEquation23Weight w F a b (h : ℤ) q)) =
      ∑ q ∈ dfiEquation22Moduli Q,
        (((a : ℂ) * b)⁻¹ * dfiEquation27ArithmeticCoefficient a b h q) *
          dfiEquation27PhysicalMainIntegral w q a b
            (dfiReducedDenominator a q) (dfiReducedDenominator b q)
            F (h : ℝ) := by
  apply Finset.sum_congr rfl
  intro q _
  exact dfiEquation24MainTotal_eq_equation27_summand
    w a b h q ha hb hab F

/-- Faithful source assembly of DFI equation (27).  The moduli are split at
an arbitrary `K < ceil (2Q)`: equation (18) controls only the small range,
equation (30) controls the remaining physical main terms, and the
divisor-expanded infinite central tail is subtracted exactly.  This is the
three-part decomposition used in the paper, rather than an all-moduli delta
approximation. -/
theorem exists_norm_sum_dfiEquation24Main_sub_centralSeries_le_source_split
    {P X Y U Q : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (a b h K : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hab : a.Coprime b) (hK : 1 ≤ K) (hKQ : K < ⌈2 * Q⌉₊)
    (j : ℕ) (hj : 2 ≤ j)
    (alpha theta beta delta : ℝ)
    (halpha : 0 < alpha) (htheta : 0 < theta)
    (hbeta : 0 < beta) (hdelta : 0 < delta)
    (hexp : 2 - beta = 1 + alpha + theta) :
    ∃ Cs Cp Ct : ℝ, 0 < Cs ∧ 0 < Cp ∧ 0 < Ct ∧
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (Cs * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant delta * (h : ℝ) ^ delta) *
            ((1 + delta⁻¹) *
              max 1 ((((K + 1 : ℕ) : ℝ) ^ delta)))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) +
        ‖(((a : ℂ) * b)⁻¹)‖ *
          ((((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant delta * (h : ℝ) ^ delta) *
            ((1 / (K + 1 : ℝ)) *
              ((1 + delta⁻¹) *
                max 1 (((⌈2 * Q⌉₊ : ℕ) : ℝ) ^ delta)))) *
          (Cp *
            (Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            (Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            min X Y * Real.log Q)) +
        Ct * (h : ℝ) ^ delta * ((K : ℝ) + 1) ^ (-alpha) *
          (1 + theta⁻¹) := by
  have hQpos : 0 < Q := by linarith
  obtain ⟨Cs, hCs, hsmallAll⟩ :=
    norm_sum_Icc_dfiEquation27_reduced_main_error_le_epsilon
      hQpos w hf hfC hbox hφ hφC hscale j hj hdelta
  have hsmall := hsmallAll a b h K ha hb hh hK
  have hmod : ∀ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, (q : ℝ) ≤ 2 * Q := by
    intro q hq
    exact (Nat.lt_ceil.mp (Finset.mem_Ioo.mp hq).2).le
  obtain ⟨Cp, hCp, hlarge⟩ :=
    exists_norm_sum_Ioo_dfiEquation27PhysicalMain_le_epsilon
      (hR := (h : ℝ)) w hf hfC hbox hφ hφC hscale hwC hQ hU
      a b h K ⌈2 * Q⌉₊ ha hb hh hmod hdelta
  obtain ⟨Ct, hCt, htail⟩ :=
    exists_tsum_norm_dfiEquation27CentralSummand_tail_le_source_sharp
      hf hfC hbox hφ hφC hscale a b h ha hb hh alpha theta beta delta
        halpha htheta hbeta hdelta hexp
  refine ⟨Cs, Cp, Ct, hCs, hCp, hCt, ?_⟩
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let physical : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let central : ℕ → ℂ := fun q =>
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let F : ℕ → ℂ := fun q =>
    ((((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q) *
      dfiEquation27PhysicalMainIntegral w q a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) (h : ℝ)
  let G : ℕ → ℂ := fun q =>
    ((((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q) *
      dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) (h : ℝ)
  have hG : Summable G := by
    simpa [G, c, central, dfiEquation27CentralSummand] using
      summable_dfiEquation27CentralSummand
        hf hfC hbox hφ hφC hscale a b h ha hb hh
  have hG0 : G 0 = 0 := by
    simp [G, dfiEquation27ArithmeticCoefficient]
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 ⌈2 * Q⌉₊ := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  have hMain :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) =
        ∑ q ∈ Finset.Ioo 0 ⌈2 * Q⌉₊, F q := by
    rw [sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
      w a b h ha hb hab (dfiLocalizedWeight f φ h), hset]
  have hSeries : dfiEquation27CentralSeries a b h
      (dfiLocalizedWeight f φ h) = ∑' q : ℕ, G q := by
    rfl
  have hdecomp :=
    sum_Ioo_zero_sub_tsum_eq_small_error_add_large_sub_tail
      F G K ⌈2 * Q⌉₊ hKQ hG hG0
  have hsmall' :
      ‖∑ q ∈ Finset.Icc 1 K, (F q - G q)‖ ≤
        ‖c‖ *
          (Cs * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant delta * (h : ℝ) ^ delta) *
            ((1 + delta⁻¹) * max 1 ((((K + 1 : ℕ) : ℝ) ^ delta)))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j) := by
    have hfactor :
        (∑ q ∈ Finset.Icc 1 K, (F q - G q)) =
          c * ∑ q ∈ Finset.Icc 1 K,
            dfiEquation27ArithmeticCoefficient a b h q *
              (physical q - central q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [F, G]
      ring
    rw [hfactor, norm_mul]
    exact mul_le_mul_of_nonneg_left hsmall (norm_nonneg c)
  have hlarge' :
      ‖∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q‖ ≤
        ‖c‖ *
          ((((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant delta * (h : ℝ) ^ delta) *
            ((1 / (K + 1 : ℝ)) *
              ((1 + delta⁻¹) *
                max 1 (((⌈2 * Q⌉₊ : ℕ) : ℝ) ^ delta)))) *
          (Cp *
            (Real.log (2 * X) + |Real.log a| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            (Real.log (2 * Y) + |Real.log b| +
              2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
            min X Y * Real.log Q)) := by
    dsimp [F, c, physical]
    convert hlarge using 1
    all_goals ring
  have hGshift : Summable (fun n : ℕ => G (K + (n + 1))) := by
    have hs := (summable_nat_add_iff (K + 1)).2 hG
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have htailNorm :
      ‖∑' n : ℕ, G (K + (n + 1))‖ ≤
        ∑' n : ℕ, ‖G (K + (n + 1))‖ :=
    norm_tsum_le_tsum_norm hGshift.norm
  have htail' :
      ‖∑' n : ℕ, G (K + (n + 1))‖ ≤
        Ct * (h : ℝ) ^ delta * ((K : ℝ) + 1) ^ (-alpha) *
          (1 + theta⁻¹) := by
    exact htailNorm.trans (by
      simpa [G, c, central, dfiEquation27CentralSummand] using htail K)
  rw [hMain, hSeries, hdecomp]
  calc
    ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
        (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) -
        ∑' n : ℕ, G (K + (n + 1))‖ ≤
      ‖∑ q ∈ Finset.Icc 1 K, (F q - G q)‖ +
        ‖∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q‖ +
        ‖∑' n : ℕ, G (K + (n + 1))‖ := by
      calc
        ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) -
            ∑' n : ℕ, G (K + (n + 1))‖ ≤
          ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)‖ +
            ‖∑' n : ℕ, G (K + (n + 1))‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le
              ((∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
                ∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)
              (-(∑' n : ℕ, G (K + (n + 1))))
        _ ≤ _ := add_le_add
          (norm_add_le
            (∑ q ∈ Finset.Icc 1 K, (F q - G q))
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)) le_rfl
    _ ≤ _ := add_le_add (add_le_add hsmall' hlarge') htail'

/-- Displayed small-modulus contribution in the source-uniform equation-(27)
split. -/
noncomputable def dfiEquation27InterpolatedSmallError
    (Cs Q X Y U rho : ℝ) (a b h K j : ℕ) : ℝ :=
  Cs * ((((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
    (h.divisors.card : ℝ) * ((harmonic (K + 1) : ℚ) : ℝ)) *
    dfiEquation27IntegratedErrorEnvelope Q X Y U a b K j

/-- Displayed large-modulus physical contribution in the source-uniform
equation-(27) split. -/
noncomputable def dfiEquation27InterpolatedPhysicalError
    (Cp Q X Y rho : ℝ) (a b h K : ℕ) : ℝ :=
  ((((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
    (h.divisors.card : ℝ) *
    (((K + 1 : ℕ) : ℝ) ^ (-rho) *
      ((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
    (Cp *
      (Real.log (2 * X) + |Real.log a| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
      (Real.log (2 * Y) + |Real.log b| +
        2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
      min X Y * Real.log Q)

/-- Displayed infinite central-tail contribution in the source-uniform
equation-(27) split. -/
noncomputable def dfiEquation27InterpolatedCentralTail
    (Ct X Y rho alpha theta beta : ℝ) (a b h K : ℕ) : ℝ :=
  Ct * (((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
    (h.divisors.card : ℝ) *
    (1 + Real.log (2 * X) + |Real.log a| +
      2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
    (1 + Real.log (2 * Y) + |Real.log b| +
      2 * |Real.eulerMascheroniConstant| + 4 * beta⁻¹) *
    min X Y * ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹)

set_option maxHeartbeats 1000000 in
/-- Fully source-uniform form of the equation-(27) split.  All three
constants are selected before `a,b,h` and the cutoff.  The negative
`(ab)^(-1+rho)` factor is retained in the small branch, the equation-(30)
physical branch, and the infinite central tail. -/
theorem exists_norm_sum_dfiEquation24Main_sub_centralSeries_le_source_split_interpolated
    {P X Y U Q : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (j : ℕ) (hj : 2 ≤ j)
    (rho alpha theta beta : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (htheta : 0 < theta) (hbeta : 0 < beta)
    (hexp : rho - beta = alpha + theta) :
    ∃ Cs Cp Ct : ℝ, 0 < Cs ∧ 0 < Cp ∧ 0 < Ct ∧
      ∀ (a b h K : ℕ), 0 < a → 0 < b → 0 < h →
      a.Coprime b → 1 ≤ K → K < ⌈2 * Q⌉₊ →
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        dfiEquation27InterpolatedSmallError Cs Q X Y U rho a b h K j +
        dfiEquation27InterpolatedPhysicalError Cp Q X Y rho a b h K +
        dfiEquation27InterpolatedCentralTail
          Ct X Y rho alpha theta beta a b h K := by
  have hQpos : 0 < Q := by linarith
  obtain ⟨Cs, hCs, hsmallAll⟩ :=
    exists_norm_sum_Icc_inv_ab_dfiEquation27_reduced_main_error_le_interpolated
      hQpos w hf hfC hbox hφ hφC hscale j hj hrho0 hrho1
  obtain ⟨Cp, hCp, hlargeAll⟩ :=
    exists_norm_sum_Ioo_dfiEquation27PhysicalMain_le_interpolated
      w hf hfC hbox hφ hφC hscale hwC hQ hU hrho0 hrho1
  obtain ⟨Ct, hCt, htailAll⟩ :=
    exists_tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated
      hf hfC hbox hφ hφC hscale rho alpha theta beta
        hrho0 hrho1 halpha htheta hbeta hexp
  refine ⟨Cs, Cp, Ct, hCs, hCp, hCt, ?_⟩
  intro a b h K ha hb hh hab hK hKQ
  have hsmall := hsmallAll a b h K ha hb hh hK
  have hmod : ∀ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, (q : ℝ) ≤ 2 * Q := by
    intro q hq
    exact (Nat.lt_ceil.mp (Finset.mem_Ioo.mp hq).2).le
  have hlarge := hlargeAll (h : ℝ) a b h K ⌈2 * Q⌉₊ ha hb hh hmod
  have htail := htailAll a b h K ha hb hh
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let physical : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let central : ℕ → ℂ := fun q =>
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let F : ℕ → ℂ := fun q =>
    ((((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q) *
      dfiEquation27PhysicalMainIntegral w q a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) (h : ℝ)
  let G : ℕ → ℂ := fun q =>
    ((((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q) *
      dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) (h : ℝ)
  have hG : Summable G := by
    simpa [G, c, central, dfiEquation27CentralSummand] using
      summable_dfiEquation27CentralSummand
        hf hfC hbox hφ hφC hscale a b h ha hb hh
  have hG0 : G 0 = 0 := by
    simp [G, dfiEquation27ArithmeticCoefficient]
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 ⌈2 * Q⌉₊ := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  have hMain :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) =
        ∑ q ∈ Finset.Ioo 0 ⌈2 * Q⌉₊, F q := by
    rw [sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
      w a b h ha hb hab (dfiLocalizedWeight f φ h), hset]
  have hSeries : dfiEquation27CentralSeries a b h
      (dfiLocalizedWeight f φ h) = ∑' q : ℕ, G q := by
    rfl
  have hdecomp :=
    sum_Ioo_zero_sub_tsum_eq_small_error_add_large_sub_tail
      F G K ⌈2 * Q⌉₊ hKQ hG hG0
  have hsmall' :
      ‖∑ q ∈ Finset.Icc 1 K, (F q - G q)‖ ≤
        dfiEquation27InterpolatedSmallError Cs Q X Y U rho a b h K j := by
    have heq :
        (∑ q ∈ Finset.Icc 1 K, (F q - G q)) =
          ∑ q ∈ Finset.Icc 1 K,
            (c * dfiEquation27ArithmeticCoefficient a b h q) *
              (physical q - central q) := by
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [F, G]
      ring
    rw [heq]
    simpa only [dfiEquation27InterpolatedSmallError, c, physical, central]
      using hsmall
  have hlarge' :
      ‖∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q‖ ≤
        dfiEquation27InterpolatedPhysicalError Cp Q X Y rho a b h K := by
    have hFeq : (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) =
        ∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊,
          (((a : ℂ) * b)⁻¹ *
            dfiEquation27ArithmeticCoefficient a b h q) *
            dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) := by
      rfl
    rw [hFeq]
    have hErrEq :
        dfiEquation27InterpolatedPhysicalError Cp Q X Y rho a b h K =
          ((((a * b : ℕ) : ℝ) ^ (-1 + rho)) *
            (h.divisors.card : ℝ) *
            (((K + 1 : ℕ) : ℝ) ^ (-rho) *
              ((harmonic ⌈2 * Q⌉₊ : ℚ) : ℝ))) *
            (Cp *
              (Real.log (2 * X) + |Real.log a| +
                2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
              (Real.log (2 * Y) + |Real.log b| +
                2 * |Real.eulerMascheroniConstant| + 2 * Real.log (2 * Q)) *
              min X Y * Real.log Q) := rfl
    rw [hErrEq]
    exact hlarge
  have hGshift : Summable (fun n : ℕ => G (K + (n + 1))) := by
    have hs := (summable_nat_add_iff (K + 1)).2 hG
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have htailNorm :
      ‖∑' n : ℕ, G (K + (n + 1))‖ ≤
        ∑' n : ℕ, ‖G (K + (n + 1))‖ :=
    norm_tsum_le_tsum_norm hGshift.norm
  have htail' :
      ‖∑' n : ℕ, G (K + (n + 1))‖ ≤
        dfiEquation27InterpolatedCentralTail
          Ct X Y rho alpha theta beta a b h K := by
    exact htailNorm.trans (by
      simpa only [dfiEquation27InterpolatedCentralTail,
        G, c, central, dfiEquation27CentralSummand] using htail)
  rw [hMain, hSeries, hdecomp]
  calc
    ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
        (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) -
        ∑' n : ℕ, G (K + (n + 1))‖ ≤
      ‖∑ q ∈ Finset.Icc 1 K, (F q - G q)‖ +
        ‖∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q‖ +
        ‖∑' n : ℕ, G (K + (n + 1))‖ := by
      calc
        ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) -
            ∑' n : ℕ, G (K + (n + 1))‖ ≤
          ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)‖ +
            ‖∑' n : ℕ, G (K + (n + 1))‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le
              ((∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
                ∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)
              (-∑' n : ℕ, G (K + (n + 1)))
        _ ≤ _ := add_le_add
          (norm_add_le
            (∑ q ∈ Finset.Icc 1 K, (F q - G q))
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)) le_rfl
    _ ≤ _ := add_le_add (add_le_add hsmall' hlarge') htail'

set_option maxHeartbeats 1000000 in
/-- Profile-uniform source equation-(27) split.  Its three displayed
constants depend only on the fixed delta, quotient, source, and cutoff
profiles (and on the fixed differentiation order and Euler-factor bounds),
not on any DFI physical scale or arithmetic variable. -/
theorem norm_sum_dfiEquation24Main_sub_centralSeries_le_source_split_interpolated_of_profiles
    {P X Y U Q : ℝ} {w : DFIDeltaWeight Q}
    {D Eprofile : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D)
    (hEprofile : DFIWeightQuotientProfile w Eprofile)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ Cw : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hwC : DFIDeltaWeightProfile w Cw)
    (hQ : 2 ≤ Q) (hU : U = Q ^ 2)
    (j : ℕ) (hj : 2 ≤ j)
    {Cpsi CpsiSucc : ℝ} (hCpsi : 0 < Cpsi)
    (hpsi : ∀ x : ℝ, |dfiPsi j x| ≤ Cpsi)
    (hCpsiSucc : 0 < CpsiSucc)
    (hpsiSucc : ∀ x : ℝ, |dfiPsi (j + 1) x| ≤ CpsiSucc)
    (rho alpha theta beta : ℝ)
    (hrho0 : 0 < rho) (hrho1 : rho ≤ 1)
    (halpha : 0 < alpha) (htheta : 0 < theta) (hbeta : 0 < beta)
    (hexp : rho - beta = alpha + theta) :
    ∀ (a b h K : ℕ), 0 < a → 0 < b → 0 < h →
      a.Coprime b → 1 ≤ K → K < ⌈2 * Q⌉₊ →
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        dfiEquation27InterpolatedSmallError
          (dfiEquation27SmallProfileConstant
            D Eprofile j Cpsi CpsiSucc Cf Cφ)
          Q X Y U rho a b h K j +
        dfiEquation27InterpolatedPhysicalError
          (dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw)
          Q X Y rho a b h K +
        dfiEquation27InterpolatedCentralTail
          (dfiEquation27CentralProfileConstant Cf Cφ)
          X Y rho alpha theta beta a b h K := by
  have hQpos : 0 < Q := by linarith
  have hsmallAll :=
    norm_sum_Icc_inv_ab_dfiEquation27_reduced_main_error_le_interpolated_of_profiles
      hQpos hD hEprofile hf hfC hbox hφ hφC hscale j hj
        hCpsi hpsi hCpsiSucc hpsiSucc hrho0 hrho1
  have hlargeAll :=
    norm_sum_Ioo_dfiEquation27PhysicalMain_le_interpolated_of_profiles
      w hf hfC hbox hφ hφC hscale hwC hQ hU hrho0 hrho1
  have htailAll :=
    tsum_norm_dfiEquation27CentralSummand_tail_le_interpolated_of_profiles
      hf hfC hbox hφ hφC hscale rho alpha theta beta
        hrho0 hrho1 halpha htheta hbeta hexp
  intro a b h K ha hb hh hab hK hKQ
  have hsmall := hsmallAll a b h K ha hb hh hK
  have hmod : ∀ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, (q : ℝ) ≤ 2 * Q := by
    intro q hq
    exact (Nat.lt_ceil.mp (Finset.mem_Ioo.mp hq).2).le
  have hlarge := hlargeAll (h : ℝ) a b h K ⌈2 * Q⌉₊ ha hb hh hmod
  have htail := htailAll a b h K ha hb hh
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let physical : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let central : ℕ → ℂ := fun q =>
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let F : ℕ → ℂ := fun q =>
    ((((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q) *
      dfiEquation27PhysicalMainIntegral w q a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) (h : ℝ)
  let G : ℕ → ℂ := fun q =>
    ((((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q) *
      dfiEquation27CentralIntegral a b
        (dfiReducedDenominator a q) (dfiReducedDenominator b q)
        (dfiLocalizedWeight f φ h) (h : ℝ)
  have hG : Summable G := by
    simpa [G, c, central, dfiEquation27CentralSummand] using
      summable_dfiEquation27CentralSummand
        hf hfC hbox hφ hφC hscale a b h ha hb hh
  have hG0 : G 0 = 0 := by
    simp [G, dfiEquation27ArithmeticCoefficient]
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 ⌈2 * Q⌉₊ := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  have hMain :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) =
        ∑ q ∈ Finset.Ioo 0 ⌈2 * Q⌉₊, F q := by
    rw [sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
      w a b h ha hb hab (dfiLocalizedWeight f φ h), hset]
  have hSeries : dfiEquation27CentralSeries a b h
      (dfiLocalizedWeight f φ h) = ∑' q : ℕ, G q := by
    rfl
  have hdecomp :=
    sum_Ioo_zero_sub_tsum_eq_small_error_add_large_sub_tail
      F G K ⌈2 * Q⌉₊ hKQ hG hG0
  have hsmall' :
      ‖∑ q ∈ Finset.Icc 1 K, (F q - G q)‖ ≤
        dfiEquation27InterpolatedSmallError
          (dfiEquation27SmallProfileConstant
            D Eprofile j Cpsi CpsiSucc Cf Cφ)
          Q X Y U rho a b h K j := by
    have heq :
        (∑ q ∈ Finset.Icc 1 K, (F q - G q)) =
          ∑ q ∈ Finset.Icc 1 K,
            (c * dfiEquation27ArithmeticCoefficient a b h q) *
              (physical q - central q) := by
      apply Finset.sum_congr rfl
      intro q hq
      dsimp [F, G]
      ring
    rw [heq]
    simpa only [dfiEquation27InterpolatedSmallError, c, physical, central]
      using hsmall
  have hlarge' :
      ‖∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q‖ ≤
        dfiEquation27InterpolatedPhysicalError
          (dfiEquation27PhysicalMainProfileConstant Cf Cφ Cw)
          Q X Y rho a b h K := by
    have hFeq : (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) =
        ∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊,
          (((a : ℂ) * b)⁻¹ *
            dfiEquation27ArithmeticCoefficient a b h q) *
            dfiEquation27PhysicalMainIntegral w q a b
              (dfiReducedDenominator a q) (dfiReducedDenominator b q)
              (dfiLocalizedWeight f φ (h : ℝ)) (h : ℝ) := by
      rfl
    rw [hFeq]
    exact hlarge
  have hGshift : Summable (fun n : ℕ => G (K + (n + 1))) := by
    have hs := (summable_nat_add_iff (K + 1)).2 hG
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have htailNorm :
      ‖∑' n : ℕ, G (K + (n + 1))‖ ≤
        ∑' n : ℕ, ‖G (K + (n + 1))‖ :=
    norm_tsum_le_tsum_norm hGshift.norm
  have htail' :
      ‖∑' n : ℕ, G (K + (n + 1))‖ ≤
        dfiEquation27InterpolatedCentralTail
          (dfiEquation27CentralProfileConstant Cf Cφ)
          X Y rho alpha theta beta a b h K := by
    exact htailNorm.trans (by
      simpa only [dfiEquation27InterpolatedCentralTail,
        G, c, central, dfiEquation27CentralSummand] using htail)
  rw [hMain, hSeries, hdecomp]
  calc
    ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
        (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) -
        ∑' n : ℕ, G (K + (n + 1))‖ ≤
      ‖∑ q ∈ Finset.Icc 1 K, (F q - G q)‖ +
        ‖∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q‖ +
        ‖∑' n : ℕ, G (K + (n + 1))‖ := by
      calc
        ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q) -
            ∑' n : ℕ, G (K + (n + 1))‖ ≤
          ‖(∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)‖ +
            ‖∑' n : ℕ, G (K + (n + 1))‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le
              ((∑ q ∈ Finset.Icc 1 K, (F q - G q)) +
                ∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)
              (-∑' n : ℕ, G (K + (n + 1)))
        _ ≤ _ := add_le_add
          (norm_add_le
            (∑ q ∈ Finset.Icc 1 K, (F q - G q))
            (∑ q ∈ Finset.Ioo K ⌈2 * Q⌉₊, F q)) le_rfl
    _ ≤ _ := add_le_add (add_le_add hsmall' hlarge') htail'

/-- The finite central equation-(27) sum over the delta-symbol moduli
approximates the infinite Ramanujan main series with the precise
`Q⁻¹⁺ε` tail.  The cutoff is handled exactly as `[1, ceil(2Q))`, so no
endpoint convention is hidden in this estimate. -/
theorem exists_norm_sum_dfiEquation27Central_sub_series_le_epsilon
    {P X Y U Q : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ D : ℝ, 0 ≤ D ∧
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
  let K : ℕ := ⌈2 * Q⌉₊
  let L : ℕ := K - 1
  have hceil : 2 * Q ≤ (K : ℝ) := by
    exact Nat.le_ceil (2 * Q)
  have hK : 1 < K := by
    have : (2 : ℝ) < K := by nlinarith
    have htwo : 2 < K := by exact_mod_cast this
    omega
  have hL : 0 < L := by
    dsimp [L]
    omega
  obtain ⟨D, hD, htail⟩ :=
    exists_tsum_norm_dfiEquation27CentralSummand_tail_le_epsilon
      hf hfC hbox hφ hφC hscale a b h ha hb hh hε0 hε1 L hL
  refine ⟨D, hD, ?_⟩
  let F : ℕ → ℂ := fun q =>
    dfiEquation27CentralSummand a b h (dfiLocalizedWeight f φ h) q
  have hF : Summable F :=
    summable_dfiEquation27CentralSummand
      hf hfC hbox hφ hφC hscale a b h ha hb hh
  have hSplit := hF.sum_add_tsum_nat_add K
  have hFinite : ∑ q ∈ Finset.range K, F q =
      ∑ q ∈ dfiEquation22Moduli Q, F q := by
    rw [dfiEquation22Moduli_eq_Ico]
    change ∑ q ∈ Finset.range K, F q = ∑ q ∈ Finset.Ico 1 K, F q
    rw [show Finset.range K = insert 0 (Finset.Ico 1 K) by
      ext q
      simp
      omega]
    simp [F, dfiEquation27CentralSummand,
      dfiEquation27ArithmeticCoefficient]
  have hShift : Summable (fun j : ℕ => F (j + K)) :=
    (summable_nat_add_iff K).2 hF
  have hTailNorm :
      ‖∑' j : ℕ, F (j + K)‖ ≤ ∑' j : ℕ, ‖F (j + K)‖ :=
    norm_tsum_le_tsum_norm hShift.norm
  have hIndex : ∀ j : ℕ, j + K = L + (j + 1) := by
    intro j
    dsimp [L]
    omega
  have hTailBound :
      ∑' j : ℕ, ‖F (j + K)‖ ≤
        D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := by
    calc
      ∑' j : ℕ, ‖F (j + K)‖ =
          ∑' j : ℕ, ‖dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) (L + (j + 1))‖ := by
        apply tsum_congr
        intro j
        rw [← hIndex j]
      _ ≤ D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := htail
  have hLQ : Q ≤ (L : ℝ) := by
    have hKone : 1 ≤ K := hK.le
    have hcast : (L : ℝ) = (K : ℝ) - 1 := by
      dsimp [L]
      rw [Nat.cast_sub hKone, Nat.cast_one]
    rw [hcast]
    nlinarith
  have hQpos : 0 < Q := by linarith
  have hpow : (L : ℝ) ^ (-(1 - ε)) ≤ Q ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_nonpos hQpos hLQ (by linarith)
  have hden : 0 ≤ (1 - ε)⁻¹ := by positivity
  have hTailScale :
      D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) ≤
        D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
    apply mul_le_mul_of_nonneg_left _ hD
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hpow hden
  unfold dfiEquation27CentralSeries
  change ‖(∑ q ∈ dfiEquation22Moduli Q, F q) - ∑' q : ℕ, F q‖ ≤
    D * (Q ^ (-(1 - ε)) / (1 - ε))
  calc
    ‖(∑ q ∈ dfiEquation22Moduli Q, F q) - ∑' q : ℕ, F q‖ =
        ‖∑' j : ℕ, F (j + K)‖ := by
      rw [← hSplit, hFinite]
      simp
    _ ≤ ∑' j : ℕ, ‖F (j + K)‖ := hTailNorm
    _ ≤ D * ((L : ℝ) ^ (-(1 - ε)) / (1 - ε)) := hTailBound
    _ ≤ D * (Q ^ (-(1 - ε)) / (1 - ε)) := hTailScale

/-- Equations (27)--(30), main branch: the finite double-main contribution
from the delta method differs from DFI's infinite Ramanujan main term by
the sum of the integrated small-modulus delta-kernel error and the exact
`Q⁻¹⁺ε` central tail.  No provisional error certificate occurs in this
statement: both terms are the concrete envelopes proved from equation (2). -/
theorem exists_norm_sum_dfiEquation24Main_sub_centralSeries_le
    {P X Y U Q : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (hQ : 2 ≤ Q)
    (a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (hab : a.Coprime b) (j : ℕ) (hj : 2 ≤ j)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        ‖(((a : ℂ) * b)⁻¹)‖ *
          (C * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
            ((1 + ε⁻¹) * max 1
              ((((⌈2 * Q⌉₊ - 1) + 1 : ℕ) : ℝ) ^ ε))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b
              (⌈2 * Q⌉₊ - 1) j) +
          D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
  let K : ℕ := ⌈2 * Q⌉₊
  let L : ℕ := K - 1
  have hQpos : 0 < Q := by linarith
  have hceil : 2 * Q ≤ (K : ℝ) := Nat.le_ceil (2 * Q)
  have hKtwo : 2 < K := by
    exact_mod_cast (show (2 : ℝ) < K by nlinarith)
  have hL : 1 ≤ L := by
    dsimp [L]
    omega
  have hset : Finset.Icc 1 L = dfiEquation22Moduli Q := by
    rw [dfiEquation22Moduli_eq_Ico]
    change Finset.Icc 1 L = Finset.Ico 1 K
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    dsimp [L]
    omega
  obtain ⟨C, hC, hsmall⟩ :=
    norm_sum_Icc_dfiEquation27_reduced_main_error_le_epsilon
      hQpos w hf hfC hbox hφ hφC hscale j hj hε0
  obtain ⟨D, hD, htail⟩ :=
    exists_norm_sum_dfiEquation27Central_sub_series_le_epsilon
      hf hfC hbox hφ hφC hscale hQ a b h ha hb hh hε0 hε1
  refine ⟨C, D, hC, hD, ?_⟩
  let c : ℂ := ((a : ℂ) * b)⁻¹
  let physical : ℕ → ℂ := fun q =>
    dfiEquation27PhysicalMainIntegral w q a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  let central : ℕ → ℂ := fun q =>
    dfiEquation27CentralIntegral a b
      (dfiReducedDenominator a q) (dfiReducedDenominator b q)
      (dfiLocalizedWeight f φ h) (h : ℝ)
  have hsmallApply := hsmall a b h L ha hb hh hL
  rw [hset] at hsmallApply
  have hPhysCentral :
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
        ∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * central q‖ ≤
      ‖c‖ *
        (C * (((a * b : ℕ) : ℝ) *
          (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
          ((1 + ε⁻¹) * max 1 ((((L + 1 : ℕ) : ℝ) ^ ε)))) *
          dfiEquation27IntegratedErrorEnvelope Q X Y U a b L j) := by
    rw [← Finset.sum_sub_distrib]
    have hfactor :
        (∑ q ∈ dfiEquation22Moduli Q,
          (c * dfiEquation27ArithmeticCoefficient a b h q * physical q -
            c * dfiEquation27ArithmeticCoefficient a b h q * central q)) =
          c * ∑ q ∈ dfiEquation22Moduli Q,
            dfiEquation27ArithmeticCoefficient a b h q *
              (physical q - central q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [hfactor, norm_mul]
    exact mul_le_mul_of_nonneg_left hsmallApply (norm_nonneg c)
  have hMain :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) =
        ∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * physical q := by
    rw [sum_dfiEquation24MainTotal_eq_sum_dfiEquation27Physical
      w a b h ha hb hab (dfiLocalizedWeight f φ h)]
  have hCentral :
      (∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation27CentralSummand a b h
            (dfiLocalizedWeight f φ h) q) =
        ∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * central q := by
    apply Finset.sum_congr rfl
    intro q _
    rfl
  have hTriangle :
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          dfiEquation24MainTotal q a b (h : ℤ)
            (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
              a b (h : ℤ) q)) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ ≤
        ‖(∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
          ∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * central q‖ +
        ‖(∑ q ∈ dfiEquation22Moduli Q,
            dfiEquation27CentralSummand a b h
              (dfiLocalizedWeight f φ h) q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ := by
    rw [hMain, hCentral]
    calc
      ‖(∑ q ∈ dfiEquation22Moduli Q,
          c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h)‖ =
        ‖((∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * physical q) -
          ∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * central q) +
          ((∑ q ∈ dfiEquation22Moduli Q,
            c * dfiEquation27ArithmeticCoefficient a b h q * central q) -
          dfiEquation27CentralSeries a b h
            (dfiLocalizedWeight f φ h))‖ := by
          congr 1
          ring
      _ ≤ _ := norm_add_le _ _
  calc
    ‖(∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24MainTotal q a b (h : ℤ)
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h)
            a b (h : ℤ) q)) -
        dfiEquation27CentralSeries a b h
          (dfiLocalizedWeight f φ h)‖ ≤ _ := hTriangle
    _ ≤ ‖c‖ *
          (C * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
            ((1 + ε⁻¹) * max 1 ((((L + 1 : ℕ) : ℝ) ^ ε)))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b L j) +
        D * (Q ^ (-(1 - ε)) / (1 - ε)) :=
      add_le_add hPhysCentral htail
    _ = ‖(((a : ℂ) * b)⁻¹)‖ *
          (C * (((a * b : ℕ) : ℝ) *
            (divisorEpsilonConstant ε * (h : ℝ) ^ ε) *
            ((1 + ε⁻¹) * max 1
              ((((⌈2 * Q⌉₊ - 1) + 1 : ℕ) : ℝ) ^ ε))) *
            dfiEquation27IntegratedErrorEnvelope Q X Y U a b
              (⌈2 * Q⌉₊ - 1) j) +
          D * (Q ^ (-(1 - ε)) / (1 - ε)) := by
      rfl

end RiemannZeta.GuthMaynard
