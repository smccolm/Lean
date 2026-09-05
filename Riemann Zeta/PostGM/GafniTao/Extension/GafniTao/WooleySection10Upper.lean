import GafniTao.WooleySection10HierarchySelection
import GafniTao.WooleySection4Lemma42

/-!
# Uniform upper bounds for the Section 10 iteration

This file performs the constant absorption suppressed by Vinogradov notation
in Wooley's Section 10.  Lemma 4.1 is invoked with half of the final epsilon
margin.  The global hierarchy reserves half of the terminal conditioning
depth, so the other half of epsilon absorbs its uniform constant.
-/

namespace GafniTao

noncomputable section

/-- A fixed positive constant is eventually absorbed by a positive real
power of the prime-power scale. -/
theorem wooley_constant_le_primePower_rpow_eventually
    {p : ℕ} (hp : 1 < p) {eta C : ℝ} (heta : 0 < eta) :
    ∃ H0 : ℕ, ∀ H : ℕ, H0 ≤ H →
      C ≤ (((p ^ H : ℕ) : ℝ) ^ eta) := by
  have hpReal : (1 : ℝ) < p := by exact_mod_cast hp
  have hpTop : Filter.Tendsto (fun H : ℕ ↦ ((p : ℝ) ^ H))
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hpReal
  have hTop : Filter.Tendsto
      (fun H : ℕ ↦ (((p ^ H : ℕ) : ℝ) ^ eta))
      Filter.atTop Filter.atTop := by
    convert (tendsto_rpow_atTop heta).comp hpTop using 1
    ext H
    simp only [Function.comp_apply, Nat.cast_pow]
  exact Filter.eventually_atTop.mp
    (hTop.eventually (Filter.eventually_ge_atTop C))

/-- If a queried depth lies in the first half of `H`, the spare
prime-power scale absorbs any fixed constant into half an epsilon. -/
theorem wooley_constant_absorbed_below_half
    {p H h : ℕ} [NeZero p] (hp : 1 < p)
    {epsilon C : ℝ} (hepsilon : 0 < epsilon)
    {H0 : ℕ}
    (habsorb : ∀ H : ℕ, H0 ≤ H →
      C ≤ (((p ^ H : ℕ) : ℝ) ^ (epsilon / 4)))
    (hH0 : H0 ≤ H) (hhalf : 2 * h ≤ H) :
    C ≤ (((p ^ (H - h) : ℕ) : ℝ) ^ (epsilon / 2)) := by
  have hpPos : 0 < p := by omega
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
  have hdiff : (H : ℝ) / 2 ≤ (H - h : ℕ) := by
    have hhH : h ≤ H := by omega
    have hhalfReal : 2 * (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hhalf
    rw [Nat.cast_sub hhH]
    linarith
  have hexponent :
      (H : ℝ) * (epsilon / 4) ≤
        ((H - h : ℕ) : ℝ) * (epsilon / 2) := by
    nlinarith
  calc
    C ≤ (((p ^ H : ℕ) : ℝ) ^ (epsilon / 4)) := habsorb H hH0
    _ = (p : ℝ) ^ ((H : ℝ) * (epsilon / 4)) :=
      wooley_natPrimePower_rpow p H (epsilon / 4) hpPos
    _ ≤ (p : ℝ) ^ (((H - h : ℕ) : ℝ) * (epsilon / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hpOne hexponent
    _ = (((p ^ (H - h) : ℕ) : ℝ) ^ (epsilon / 2)) :=
      (wooley_natPrimePower_rpow p (H - h) (epsilon / 2) hpPos).symm

/-- The constant-bearing Lemma 4.1 bound becomes the coefficient-one
upper bound required by Sections 9--10 after the explicit absorption. -/
theorem wooley_lemma41_absorb_constant
    {k p B H h : ℕ} [NeZero p] {phi : WooleyPolynomialSystem k}
    {gamma : WooleySourceSequence} {epsilon C : ℝ}
    (hp : 1 < p) (hepsilon : 0 < epsilon)
    (hhalf : 2 * h ≤ H)
    (hC : C ≤ (((p ^ H : ℕ) : ℝ) ^ (epsilon / 4)))
    (hraw :
      wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ h) phi gamma ≤
        C * (((p ^ (H - h) : ℕ) : ℝ) ^
            (wooleyCriticalExponent k p + epsilon / 2)) *
          wooleySourcePolynomialConditionedMean (wooleyTriangular k)
            (p ^ B) (p ^ H) phi gamma) :
    wooleySourcePolynomialConditionedMean (wooleyTriangular k)
        (p ^ B) (p ^ h) phi gamma ≤
      (((p ^ (H - h) : ℕ) : ℝ) ^
          (wooleyCriticalExponent k p + epsilon)) *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ H) phi gamma := by
  have hpPos : 0 < p := by omega
  have hC' : C ≤ (((p ^ (H - h) : ℕ) : ℝ) ^ (epsilon / 2)) := by
    have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.le
    have hhH : h ≤ H := by omega
    have hdiff : (H : ℝ) / 2 ≤ (H - h : ℕ) := by
      have hhalfReal : 2 * (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hhalf
      rw [Nat.cast_sub hhH]
      linarith
    have hexponent :
        (H : ℝ) * (epsilon / 4) ≤
          ((H - h : ℕ) : ℝ) * (epsilon / 2) := by
      nlinarith
    calc
      C ≤ (((p ^ H : ℕ) : ℝ) ^ (epsilon / 4)) := hC
      _ = (p : ℝ) ^ ((H : ℝ) * (epsilon / 4)) :=
        wooley_natPrimePower_rpow p H (epsilon / 4) hpPos
      _ ≤ (p : ℝ) ^ (((H - h : ℕ) : ℝ) * (epsilon / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hpOne hexponent
      _ = (((p ^ (H - h) : ℕ) : ℝ) ^ (epsilon / 2)) :=
        (wooley_natPrimePower_rpow p (H - h) (epsilon / 2) hpPos).symm
  have hmean0 := wooleySourcePolynomialConditionedMean_nonneg
    phi (wooleyTriangular k) (p ^ B) (p ^ H) gamma
  have hbasePos : 0 < (((p ^ (H - h) : ℕ) : ℝ)) := by positivity
  calc
    wooleySourcePolynomialConditionedMean (wooleyTriangular k)
        (p ^ B) (p ^ h) phi gamma ≤
      C * (((p ^ (H - h) : ℕ) : ℝ) ^
          (wooleyCriticalExponent k p + epsilon / 2)) *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ H) phi gamma := hraw
    _ ≤ (((p ^ (H - h) : ℕ) : ℝ) ^ (epsilon / 2)) *
          (((p ^ (H - h) : ℕ) : ℝ) ^
            (wooleyCriticalExponent k p + epsilon / 2)) *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ H) phi gamma := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC'
          (by positivity)) hmean0
    _ = (((p ^ (H - h) : ℕ) : ℝ) ^
          (wooleyCriticalExponent k p + epsilon)) *
        wooleySourcePolynomialConditionedMean (wooleyTriangular k)
          (p ^ B) (p ^ H) phi gamma := by
      rw [← Real.rpow_add hbasePos]
      congr 2
      ring

/-- Uniform coefficient-one form of Lemma 4.1 on the half-height range
reserved by the Section 10 hierarchy.  The threshold is uniform in the
polynomial system, coefficient sequence, and queried depth. -/
theorem wooleySourcePolynomial_lemma_4_1_coefficientOne_half
    {k p : ℕ} [NeZero p]
    (hpPrime : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {tau epsilon delta : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilonTau : epsilon / 2 < tau)
    (htauDelta : tau < delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ∃ B1 : ℕ, ∀ (B : ℕ) (phi : WooleyPolynomialSystem k)
      (gamma : WooleySourceSequence) (h : ℕ),
      B1 ≤ B → phi.InPhiTau p B tau → gamma.Admissible →
      2 * h ≤ B ⌈/⌉ k →
        wooleySourcePolynomialConditionedMean (wooleyTriangular k)
            (p ^ B) (p ^ h) phi gamma ≤
          (((p ^ (B ⌈/⌉ k - h) : ℕ) : ℝ) ^
              (wooleyCriticalExponent k p + epsilon)) *
            wooleySourcePolynomialConditionedMean (wooleyTriangular k)
              (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma := by
  have hp : 1 < p := lt_of_le_of_lt hk hkp
  have hepsilonHalf : 0 < epsilon / 2 := by positivity
  have hdeltaOne : delta < 1 := lt_of_le_of_lt hdeltaHalf (by norm_num)
  obtain ⟨C, hC, B0, hraw⟩ :=
    wooleySourcePolynomial_lemma_4_1 hpPrime hk hkp hepsilonHalf
      hepsilonTau htauDelta hdeltaOne
  obtain ⟨H0, habsorb⟩ :=
    wooley_constant_le_primePower_rpow_eventually hp
      (show 0 < epsilon / 4 by positivity) (C := C)
  refine ⟨max B0 (k * H0), ?_⟩
  intro B phi gamma h hB hphi hgamma hhalf
  have hB0 : B0 ≤ B := (le_max_left _ _).trans hB
  have hkH0B : k * H0 ≤ B := (le_max_right _ _).trans hB
  have hBceil : B ≤ k * (B ⌈/⌉ k) :=
    le_smul_ceilDiv (by omega : 0 < k)
  have hH0 : H0 ≤ B ⌈/⌉ k := by
    exact Nat.le_of_mul_le_mul_left (hkH0B.trans hBceil) (by omega)
  have hhH : h ≤ B ⌈/⌉ k := by omega
  have hdepth : (h : ℝ) ≤ (1 - delta) * (B ⌈/⌉ k : ℕ) := by
    have hhalfReal : 2 * (h : ℝ) ≤ ((B ⌈/⌉ k : ℕ) : ℝ) := by
      exact_mod_cast hhalf
    have hHnonneg : (0 : ℝ) ≤ ((B ⌈/⌉ k : ℕ) : ℝ) := by positivity
    nlinarith
  have hraw' := hraw B phi gamma h hB0 hphi hgamma hdepth
  have hCscale :
      C ≤ (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ (epsilon / 4)) :=
    habsorb (B ⌈/⌉ k) hH0
  exact wooley_lemma41_absorb_constant hp hepsilon hhalf hCscale hraw'

#print axioms wooley_constant_le_primePower_rpow_eventually
#print axioms wooley_constant_absorbed_below_half
#print axioms wooley_lemma41_absorb_constant
#print axioms wooleySourcePolynomial_lemma_4_1_coefficientOne_half

end

end GafniTao
