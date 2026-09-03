import GafniTao.PintzEquation414
import GafniTao.FordQualitativeFiniteZeta

/-!
# Ford bounds for the finite partial-zeta correlations in Pintz (4.12)

The off-diagonal Gram entry is a sharp partial zeta sum.  This file extends
the already proved Ford dyadic estimate from the canonical cutoff to an
arbitrary positive cutoff not exceeding the physical frequency.  This is one
of the two cutoff regimes needed by the Pintz consumer.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Exact `u = 0` identification at an arbitrary finite cutoff. -/
theorem fordFiniteHurwitzSum_zero_eq_partialSum_general
    (sigma t : ℝ) (M : ℕ) :
    fordFiniteHurwitzSum sigma M 0 t =
      ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  unfold fordFiniteHurwitzSum fordComplexHeight
  simp

/-- The proved qualitative Ford exponential-sum estimate, transferred to
every positive cutoff `M <= t`. -/
theorem norm_fordPartialSum_le_qualitative_general
    {sigma t : ℝ} {M : ℕ}
    (hsigmaLower : 0 <= sigma) (hsigmaUpper : sigma <= 1)
    (ht : 1 < t) (hMPos : 1 <= M) (hMt : (M : ℝ) <= t) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ <=
      1 + fordQualitativeCoefficient *
        (t ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log t ^ ((2 : ℝ) / 3))) := by
  rw [← fordFiniteHurwitzSum_zero_eq_partialSum_general]
  let u : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have huLim : Tendsto u atTop (𝓝 0) := by
    simpa [u, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsumLim : Tendsto
      (fun k => fordFiniteHurwitzSum sigma M (u k) t)
        atTop (𝓝 (fordFiniteHurwitzSum sigma M 0 t)) :=
    (continuousAt_fordFiniteHurwitzSum_zero (sigma := sigma) (t := t) M).tendsto.comp huLim
  apply le_of_tendsto hsumLim.norm
  exact Filter.Eventually.of_forall fun k => by
    apply norm_fordFiniteHurwitzSum_le_general (r := M)
      ford_exponential_sum_qualitative fordQualitativeCoefficient_nonneg
      (by norm_num : (0 : ℝ) < 3000000) hsigmaLower hsigmaUpper
    · dsimp [u]
      positivity
    · dsimp [u]
      rw [div_le_one (by positivity)]
      norm_num
    · exact ht
    · exact hMPos
    · exact hMt
    · exact (Nat.le_succ M).trans
        (RiemannZeta.GuthMaynard.nat_succ_le_two_pow M)

/-- Conjugation changes the sign of the height in a finite partial zeta sum
without changing its norm. -/
theorem norm_partialZeta_height_abs
    (sigma t : ℝ) (M : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ =
      ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma |t|)‖ := by
  by_cases ht : 0 <= t
  · rw [abs_of_nonneg ht]
  · have htNeg : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg htNeg]
    have heq :
        (starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma (-t))) =
        ∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma t) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      have hnArg : Complex.arg (n : ℂ) ≠ Real.pi := by
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm
      let z : ℂ := -fordComplexHeight sigma (-t)
      have hExp : -fordComplexHeight sigma t = star z := by
        dsimp only [z]
        apply Complex.ext <;> simp [fordComplexHeight]
      rw [hExp]
      simpa [z, Complex.star_def] using
        (Complex.cpow_conj (n : ℂ) z hnArg).symm
    calc
      ‖∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma t)‖ =
          ‖(starRingEnd ℂ) (∑ n ∈ Finset.Icc 1 M,
            (n : ℂ) ^ (-fordComplexHeight sigma (-t)))‖ :=
        congrArg norm heq |>.symm
      _ = ‖∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma (-t))‖ := by
        change ‖star (∑ n ∈ Finset.Icc 1 M,
          (n : ℂ) ^ (-fordComplexHeight sigma (-t)))‖ = _
        exact norm_star _

/-- Signed-height form of the arbitrary-cutoff Ford estimate. -/
theorem norm_fordPartialSum_le_qualitative_general_abs
    {sigma t : ℝ} {M : ℕ}
    (hsigmaLower : 0 <= sigma) (hsigmaUpper : sigma <= 1)
    (ht : 1 < |t|) (hMPos : 1 <= M) (hMt : (M : ℝ) <= |t|) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ <=
      1 + fordQualitativeCoefficient *
        (|t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          (1 + 1.569 * (3000000 : ℝ) ^ ((1 : ℝ) / 3) *
            Real.log |t| ^ ((2 : ℝ) / 3))) := by
  rw [norm_partialZeta_height_abs]
  exact norm_fordPartialSum_le_qualitative_general
    hsigmaLower hsigmaUpper ht hMPos hMt

/-- First-order Euler--Maclaurin control of an arbitrary finite partial zeta
sum.  The two correction terms are kept explicit because Pintz's physical
cutoff can exceed the shifted height in the near-diagonal regime. -/
theorem norm_partialZeta_le_zeta_add_euler
    {sigma t : ℝ} {M : ℕ}
    (hsigma : 0 < sigma) (ht : t ≠ 0) (hM : 1 ≤ M) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      ‖riemannZeta (fordComplexHeight sigma t)‖ +
        (M : ℝ) ^ (1 - sigma) / |t| +
        ‖fordComplexHeight sigma t‖ *
          ((M : ℝ) ^ (-sigma) / sigma) := by
  let s : ℂ := fordComplexHeight sigma t
  have hsRe : s.re = sigma := by simp [s, fordComplexHeight]
  have hsPos : 0 < s.re := by simpa [hsRe] using hsigma
  have hsOne : s ≠ 1 := by
    intro h
    have him : s.im = (1 : ℂ).im := congrArg Complex.im h
    simp [s, fordComplexHeight, ht] at him
  rw [RiemannZeta.GuthMaynard.riemannZeta_truncation hM hsPos hsOne]
  have hMReal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMPos : (0 : ℝ) < M := zero_lt_one.trans_le hMReal
  have hboundaryNorm :
      ‖(M : ℂ) ^ (1 - s) / (1 - s)‖ ≤
        (M : ℝ) ^ (1 - sigma) / |t| := by
    rw [norm_div]
    change ‖((M : ℝ) : ℂ) ^ (1 - s)‖ / ‖1 - s‖ ≤
      (M : ℝ) ^ (1 - sigma) / |t|
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hMPos]
    have hnum : (1 - s).re = 1 - sigma := by rw [sub_re, hsRe]; simp
    rw [hnum]
    have hden : |t| ≤ ‖1 - s‖ := by
      calc
        |t| = |(1 - s).im| := by simp [s, fordComplexHeight]
        _ ≤ ‖1 - s‖ := abs_im_le_norm _
    exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr ht)
      hden
  have htailNorm :
      ‖s * RiemannZeta.GuthMaynard.abelZetaTail M s‖ ≤
        ‖s‖ * ((M : ℝ) ^ (-sigma) / sigma) := by
    rw [norm_mul]
    gcongr
    simpa [hsRe] using
      (RiemannZeta.GuthMaynard.norm_abelZetaTail_le hMReal hsPos)
  calc
    ‖riemannZeta s + (M : ℂ) ^ (1 - s) / (1 - s) +
        s * RiemannZeta.GuthMaynard.abelZetaTail M s‖ ≤
      ‖riemannZeta s‖ + ‖(M : ℂ) ^ (1 - s) / (1 - s)‖ +
        ‖s * RiemannZeta.GuthMaynard.abelZetaTail M s‖ := by
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖riemannZeta s‖ + (M : ℝ) ^ (1 - sigma) / |t| +
        ‖s‖ * ((M : ℝ) ^ (-sigma) / sigma) := by gcongr
    _ = _ := by rfl

/-- In the complementary cutoff regime `|t| < M`, Euler--Maclaurin and the
proved global qualitative Ford bound leave only the literal endpoint cost
`M^(1-sigma)`.  This is harmless in Pintz because `log M` is the selected
Gaussian scale `lambda + O(1)`, rather than `log T`. -/
theorem norm_partialZeta_le_ford_add_endpoint
    {sigma t : ℝ} {M : ℕ}
    (hsigmaLower : 1 / 2 ≤ sigma) (hsigmaUpper : sigma ≤ 1)
    (ht : 3 ≤ |t|) (hMPos : 1 ≤ M) (htM : |t| < (M : ℝ)) :
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      fordQualitativeGlobalCoefficient *
          |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t| ^ (2 / 3 : ℝ) +
        5 * (M : ℝ) ^ (1 - sigma) := by
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le (by norm_num) hsigmaLower
  have htNe : t ≠ 0 := by
    intro h
    subst t
    norm_num at ht
  have hraw := norm_partialZeta_le_zeta_add_euler
    hsigmaPos htNe hMPos
  have hheight :
      fordComplexHeight sigma t = (sigma : ℂ) + I * t := by
    simp [fordComplexHeight, mul_comm]
  have hzeta :
      ‖riemannZeta (fordComplexHeight sigma t)‖ ≤
        fordQualitativeGlobalCoefficient *
          |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t| ^ (2 / 3 : ℝ) := by
    rw [hheight]
    exact ford_qualitative_global_zeta_growth hsigmaLower hsigmaUpper ht
  have hMReal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMPos
  have hMRealPos : (0 : ℝ) < M := zero_lt_one.trans_le hMReal
  have hpowNonneg : 0 ≤ (M : ℝ) ^ (1 - sigma) := by positivity
  have hboundary :
      (M : ℝ) ^ (1 - sigma) / |t| ≤ (M : ℝ) ^ (1 - sigma) := by
    exact div_le_self hpowNonneg (by linarith)
  have hsNorm : ‖fordComplexHeight sigma t‖ ≤ 2 * (M : ℝ) := by
    calc
      ‖fordComplexHeight sigma t‖ ≤ ‖(sigma : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        unfold fordComplexHeight
        exact norm_add_le _ _
      _ = |sigma| + |t| := by simp [Real.norm_eq_abs]
      _ = sigma + |t| := by rw [abs_of_nonneg (by linarith)]
      _ ≤ 1 + (M : ℝ) := by linarith
      _ ≤ 2 * (M : ℝ) := by linarith
  have hInv : 1 / sigma ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hsigmaPos]
    linarith
  have hInv' : sigma⁻¹ ≤ (2 : ℝ) := by simpa [one_div] using hInv
  have htail :
      ‖fordComplexHeight sigma t‖ *
          ((M : ℝ) ^ (-sigma) / sigma) ≤
        4 * (M : ℝ) ^ (1 - sigma) := by
    have hnegPow : 0 ≤ (M : ℝ) ^ (-sigma) := by positivity
    calc
      ‖fordComplexHeight sigma t‖ *
          ((M : ℝ) ^ (-sigma) / sigma) ≤
        (2 * (M : ℝ)) * ((M : ℝ) ^ (-sigma) * 2) := by
          rw [div_eq_mul_inv]
          gcongr
      _ = 4 * ((M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-sigma)) := by
        rw [Real.rpow_one]
        ring
      _ = 4 * (M : ℝ) ^ (1 - sigma) := by
        rw [← Real.rpow_add hMRealPos]
        congr 1
  calc
    ‖∑ n ∈ Finset.Icc 1 M,
        (n : ℂ) ^ (-fordComplexHeight sigma t)‖ ≤
      ‖riemannZeta (fordComplexHeight sigma t)‖ +
        (M : ℝ) ^ (1 - sigma) / |t| +
        ‖fordComplexHeight sigma t‖ *
          ((M : ℝ) ^ (-sigma) / sigma) := hraw
    _ ≤ (fordQualitativeGlobalCoefficient *
          |t| ^ (fordSourceB 3000000 * (1 - sigma) ^ (3 / 2 : ℝ)) *
          Real.log |t| ^ (2 / 3 : ℝ)) +
        (M : ℝ) ^ (1 - sigma) +
        4 * (M : ℝ) ^ (1 - sigma) := by gcongr
    _ = _ := by ring

#print axioms fordFiniteHurwitzSum_zero_eq_partialSum_general
#print axioms norm_fordPartialSum_le_qualitative_general
#print axioms norm_partialZeta_height_abs
#print axioms norm_fordPartialSum_le_qualitative_general_abs
#print axioms norm_partialZeta_le_zeta_add_euler
#print axioms norm_partialZeta_le_ford_add_endpoint

end

end GafniTao
