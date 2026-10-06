import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold

/-! # The actual quadratic coefficient scale and normalized comparability bounds -/

namespace Dubon2026

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The positive square root of the actual sum of squared coefficients. -/
def steinhausScale (b : ι → ℝ) : ℝ := Real.sqrt (∑ i, b i ^ 2)

/-- The coefficients divided by their actual quadratic scale. -/
def normalizedSteinhausCoefficients (b : ι → ℝ) (i : ι) : ℝ := b i / steinhausScale b

/-- The literal minimum in the source's coefficient comparability ratio. -/
def steinhausMinCoefficient [Nonempty ι] (b : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty b

/-- The literal maximum in the source's coefficient comparability ratio. -/
def steinhausMaxCoefficient [Nonempty ι] (b : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty b

theorem steinhausMinCoefficient_pos [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    0 < steinhausMinCoefficient b := by
  obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ) Finset.univ_nonempty b
  change 0 < Finset.univ.inf' Finset.univ_nonempty b
  rw [he]
  exact hb i

theorem steinhaus_pairwise_of_max_min [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    {K : ℝ} (hK : 1 ≤ K) (hcomp : steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K) :
    ∀ i j, b i ≤ K * b j := by
  have hm := (div_le_iff₀ (steinhausMinCoefficient_pos b hb)).mp hcomp
  intro i j
  calc
    b i ≤ steinhausMaxCoefficient b := Finset.le_sup' b (Finset.mem_univ i)
    _ ≤ K * steinhausMinCoefficient b := hm
    _ ≤ K * b j := mul_le_mul_of_nonneg_left (Finset.inf'_le b (Finset.mem_univ j))
      ((by norm_num : (0 : ℝ) ≤ 1).trans hK)

theorem steinhausScale_sq (b : ι → ℝ) : steinhausScale b ^ 2 = ∑ i, b i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (b i))

theorem steinhausScale_pos [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i) :
    0 < steinhausScale b := by
  apply Real.sqrt_pos.2
  exact Finset.sum_pos (fun i _ => sq_pos_of_pos (hb i)) Finset.univ_nonempty

theorem normalizedSteinhausCoefficients_pos [Nonempty ι] (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) (i : ι) : 0 < normalizedSteinhausCoefficients b i :=
  div_pos (hb i) (steinhausScale_pos b hb)

theorem sum_normalizedSteinhausCoefficients_sq [Nonempty ι] (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) : ∑ i, normalizedSteinhausCoefficients b i ^ 2 = 1 := by
  simp only [normalizedSteinhausCoefficients, div_pow]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  rw [← steinhausScale_sq b, ← div_eq_mul_inv,
    div_self (pow_ne_zero _ (steinhausScale_pos b hb).ne')]

theorem steinhausScale_le_comparable [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    {K : ℝ} (hK : 1 ≤ K) (hcomp : ∀ i j, b i ≤ K * b j) (i : ι) :
    steinhausScale b ≤ K * b i * Real.sqrt (Fintype.card ι) := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hbi : 0 ≤ b i := (hb i).le
  have hs : (steinhausScale b) ^ 2 ≤ (Fintype.card ι : ℝ) * (K * b i) ^ 2 := by
    rw [steinhausScale_sq]
    calc
      _ ≤ ∑ _j : ι, (K * b i) ^ 2 :=
        Finset.sum_le_sum fun j _ => (sq_le_sq₀ (hb j).le (mul_nonneg hK0 hbi)).2 (hcomp j i)
      _ = _ := by simp
  have hm : Real.sqrt (Fintype.card ι) ^ 2 = (Fintype.card ι : ℝ) := Real.sq_sqrt (by positivity)
  apply (sq_le_sq₀ (steinhausScale_pos b hb).le (by positivity)).1
  calc
    _ ≤ (Fintype.card ι : ℝ) * (K * b i) ^ 2 := hs
    _ = _ := by simp only [mul_pow, hm]; ring

theorem comparable_le_steinhausScale [Nonempty ι] (b : ι → ℝ) (hb : ∀ i, 0 < b i)
    {K : ℝ} (hK : 1 ≤ K) (hcomp : ∀ i j, b i ≤ K * b j) (i : ι) :
    b i * Real.sqrt (Fintype.card ι) ≤ K * steinhausScale b := by
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  have hbi : 0 ≤ b i := (hb i).le
  have hS : 0 ≤ steinhausScale b := (steinhausScale_pos b hb).le
  have hs : (Fintype.card ι : ℝ) * b i ^ 2 ≤ K ^ 2 * (steinhausScale b) ^ 2 := by
    rw [steinhausScale_sq, Finset.mul_sum]
    calc
      _ = ∑ _j : ι, b i ^ 2 := by simp
      _ ≤ ∑ j : ι, K ^ 2 * b j ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_pow]
        exact (sq_le_sq₀ (hb i).le (mul_nonneg hK0 (hb j).le)).2 (hcomp i j)
  apply (sq_le_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith

theorem normalizedSteinhausCoefficients_bounds [Nonempty ι] (b : ι → ℝ)
    (hb : ∀ i, 0 < b i) {K : ℝ} (hK : 1 ≤ K) (hcomp : ∀ i j, b i ≤ K * b j)
    (i : ι) :
    1 / (K * Real.sqrt (Fintype.card ι)) ≤ normalizedSteinhausCoefficients b i ∧
      normalizedSteinhausCoefficients b i ≤ K / Real.sqrt (Fintype.card ι) := by
  have hS := steinhausScale_pos b hb
  have hm : 0 < Real.sqrt (Fintype.card ι) :=
    Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  constructor
  · rw [normalizedSteinhausCoefficients, div_le_div_iff₀ (mul_pos hK0 hm) hS]
    have hh := steinhausScale_le_comparable b hb hK hcomp i
    nlinarith
  · rw [normalizedSteinhausCoefficients, div_le_div_iff₀ hS hm]
    exact comparable_le_steinhausScale b hb hK hcomp i

end

end Dubon2026
