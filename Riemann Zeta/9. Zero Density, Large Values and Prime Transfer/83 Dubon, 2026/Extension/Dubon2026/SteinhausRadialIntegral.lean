import Dubon2026.SteinhausRegions
import Dubon2026.ThreeRegionIntegral

/-! # A dimension-uniform radial L1 estimate for the genuine Steinhaus law -/

namespace Dubon2026

open MeasureTheory Set
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The radial modulus of the genuine Bessel-product characteristic function. -/
def steinhausRadialProfile (c : ι → ℝ) (r : ℝ) : ℝ := ∏ i, |besselJ0 (c i * r)|

theorem steinhausRadialProfile_nonneg (c : ι → ℝ) (r : ℝ) :
    0 ≤ steinhausRadialProfile c r := Finset.prod_nonneg (fun _ _ => abs_nonneg _)

theorem continuous_steinhausRadialProfile (c : ι → ℝ) : Continuous (steinhausRadialProfile c) := by
  unfold steinhausRadialProfile
  apply continuous_finsetProd
  intro i _
  exact (continuous_besselJ0.comp (continuous_const.mul continuous_id)).abs

theorem norm_charFun_eq_radialProfile (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ξ : ℂ) :
    ‖charFun (steinhausLaw c) ξ‖ = steinhausRadialProfile c ‖ξ‖ :=
  norm_charFun_steinhausLaw c hc ξ

theorem normalized_steinhaus_radial_integral_le [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) (hm : 5 ≤ Fintype.card ι)
    {K R ρ D : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R) (hCR : (4 + 1 / Real.pi) ^ 2 ≤ R)
    (hcomp : steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K)
    (hρ : 0 ≤ ρ) (hgap : ∀ u ∈ Icc (1 / K ^ 2) (R * K ^ 2), |besselJ0 u| ≤ ρ)
    (hD : ∀ n : ℕ, (n : ℝ) * ρ ^ n ≤ D) :
    IntegrableOn (fun r : ℝ => r * steinhausRadialProfile (normalizedSteinhausCoefficients b) r)
      (Ioi (0 : ℝ)) ∧
    (∫ r : ℝ in Ioi 0, r * steinhausRadialProfile (normalizedSteinhausCoefficients b) r) ≤
      Real.pi ^ 2 / 2 + R ^ 2 * K ^ 2 * D / 2 + 10 * K ^ 2 * R ^ 2 := by
  let c := normalizedSteinhausCoefficients b
  let s := Real.sqrt (Fintype.card ι)
  let a := s / K
  let B := R * K * s
  let A := 1 / (K * s)
  let C := 4 + 1 / Real.pi
  let f := fun r : ℝ => r * steinhausRadialProfile c r
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hm0 : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : 0 < s := Real.sqrt_pos.2 hm0
  have hA : 0 < A := by dsimp [A]; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have haB : a ≤ B := by
    dsimp [a, B]
    rw [div_le_iff₀ hK0]
    have hKK : 1 ≤ R * K ^ 2 := by nlinarith
    nlinarith
  have hc : ∀ i, 0 ≤ c i := fun i => (normalizedSteinhausCoefficients_pos b hb i).le
  have hbnd := normalizedSteinhausCoefficients_bounds b hb hK
    (steinhaus_pairwise_of_max_min b hb hK hcomp)
  have henergy := sum_normalizedSteinhausCoefficients_sq b hb
  have hf : Continuous f := continuous_id.mul (continuous_steinhausRadialProfile c)
  have hf0 : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ f r :=
    fun r hr => mul_nonneg hr.le (steinhausRadialProfile_nonneg c r)
  have hg : IntegrableOn (fun r : ℝ => r * Real.exp (-(1 / Real.pi ^ 2) * r ^ 2))
      (Ioi (0 : ℝ)) := (integrable_mul_exp_neg_mul_sq (by positivity)).integrableOn
  have hh : IntegrableOn (fun r : ℝ => r * ρ ^ Fintype.card ι) (Ioc (0 : ℝ) B) :=
    (continuous_id.mul_const _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hj : IntegrableOn (fun r : ℝ => r * (C / Real.sqrt (A * r)) ^ Fintype.card ι) (Ioi B) := by
    have he : B = R / A := by dsimp [B, A]; field_simp
    rw [he]
    exact radial_tail_scaled_integrable C hm hR0 hA
  have hnear : ∀ r ∈ Ioc (0 : ℝ) a, f r ≤ r * Real.exp (-(1 / Real.pi ^ 2) * r ^ 2) := by
    intro r hr
    have ht := bessel_product_gaussian c r henergy
      (fun i => comparable_argument_small hK0 hm0 (hc i) (hbnd i).2 hr.1.le hr.2)
    have he : -r ^ 2 / Real.pi ^ 2 = -(1 / Real.pi ^ 2) * r ^ 2 := by ring
    rw [he] at ht
    exact mul_le_mul_of_nonneg_left ht hr.1.le
  have hmiddle : ∀ r ∈ Ioc a B, f r ≤ r * ρ ^ Fintype.card ι := by
    intro r hr
    exact mul_le_mul_of_nonneg_left
      (bessel_product_compact_bound c r ρ _ _ hgap (fun i =>
        comparable_argument_middle hK0 hm0 (hbnd i).1 (hbnd i).2 hr.1.le hr.2))
      (ha.trans hr.1.le)
  have htail : ∀ r ∈ Ioi B, f r ≤ r * (C / Real.sqrt (A * r)) ^ Fintype.card ι := by
    intro r hr
    exact mul_le_mul_of_nonneg_left
      (bessel_product_tail_bound c hA (hB.trans hr) (fun i => (hbnd i).1)
        (comparable_argument_tail hK0 hm0 hR hr.le)) (hB.trans hr).le
  obtain ⟨hi, hint⟩ := nonnegative_three_region_integral hf hf0 ha haB hg
    (fun r hr => mul_nonneg hr.le (Real.exp_pos _).le) hh
    (fun r hr => mul_nonneg hr.1.le (pow_nonneg hρ _)) hj hnear hmiddle htail
  refine ⟨hi, hint.trans ?_⟩
  have hgauss : (∫ r : ℝ in Ioi 0, r * Real.exp (-(1 / Real.pi ^ 2) * r ^ 2)) =
      Real.pi ^ 2 / 2 := by
    rw [integral_radial_gaussian (by positivity)]
    field_simp
  rw [hgauss]
  exact add_le_add (add_le_add le_rfl (integral_radial_annulus_bound hK0.le hR0.le hD _))
    (integral_radial_tail_comparable_le (by positivity) hR0 hCR hK0 hm)

theorem exists_uniform_steinhaus_radial_bound {K : ℝ} (hK : 1 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K →
      IntegrableOn (fun r : ℝ => r * steinhausRadialProfile (normalizedSteinhausCoefficients b) r)
        (Ioi (0 : ℝ)) ∧
      (∫ r : ℝ in Ioi 0, r * steinhausRadialProfile (normalizedSteinhausCoefficients b) r) ≤ L := by
  let R : ℝ := (4 + 1 / Real.pi) ^ 2 + 1
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [sq_nonneg (4 + 1 / Real.pi)]
  have hCR : (4 + 1 / Real.pi) ^ 2 ≤ R := by dsimp [R]; linarith
  obtain ⟨ρ, hρ0, hρ1, hgap⟩ := exists_besselJ0_comparable_gap hK hR
  obtain ⟨D, hD0, hD⟩ := exists_dimension_geometric_bound hρ0 hρ1
  refine ⟨Real.pi ^ 2 / 2 + R ^ 2 * K ^ 2 * D / 2 + 10 * K ^ 2 * R ^ 2,
    by positivity, ?_⟩
  intro κ _ _ b hb hm hcomp
  exact normalized_steinhaus_radial_integral_le b hb hm hK hR hCR hcomp hρ0 hgap hD

end

end Dubon2026
