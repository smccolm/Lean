import Dubon2026.SourceEllipticCharTwoAuxiliaryRootUnits
import Dubon2026.SourceEllipticCharTwoThreeDivisionRelation

/-! DUB-17/18 -> characteristic-two weighted census -> full inertia image.
The exact eighth-power factorization is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo.
Existing monic integrality, flex and division-polynomial proofs replace repeated
valuation growth and affine doubling calculations. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve WeierstrassCurve.Affine Polynomial IsLocalRing
noncomputable section
variable {M : Type*} [Field M]

theorem exists_unit_mul_eighth_power [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A))
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  obtain ⟨htx, hpsi, heq⟩ := psi3_of_order_three hP h3P
  have hx0 : x₀ ≠ 0 := fun h => htx (by rw [h, mul_zero])

  have hvt : A.valuation t < 1 := by
    have : (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr htu
    exact (A.valuation_lt_one_iff ⟨t, ht⟩).mp this

  set z : M := t ^ 2 / x₀ with hz_def
  set η : M := t * y₀ / x₀ ^ 2 with hη_def
  have hzx : z * x₀ = t ^ 2 := by rw [hz_def]; exact div_mul_cancel₀ _ hx0
  have hηx : η * x₀ ^ 2 = t * y₀ := by rw [hη_def]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hx0)
  have hz : z ^ 4 = t * z + t := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hx0)
    linear_combination (z ^ 3 * x₀ ^ 3 + t ^ 2 * z ^ 2 * x₀ ^ 2 + t ^ 4 * z * x₀ + t ^ 6 - t * x₀ ^ 3) * hzx
      - t * hpsi + t ^ 8 * h2
  have hη : η ^ 2 + z * η + 1 = 0 := by
    have h1 : (η ^ 2 + z * η + 1) * x₀ ^ 4 = 0 := by
      linear_combination (η * x₀ ^ 2 + t * y₀ + x₀ * t ^ 2) * hηx + (x₀ * η * x₀ ^ 2) * hzx +
        hpsi + t ^ 2 * heq
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 4 hx0)
  have hvz : A.valuation z < 1 := val_lt_one_of_z A hvt hz
  have hvη : A.valuation η = 1 := val_eq_one_of_eta A hvz.le hη
  have hzA : z ∈ A := (A.valuation_le_one_iff z).mp hvz.le
  have hηA : η ∈ A := (A.valuation_le_one_iff η).mp hvη.le

  have hv1z : A.valuation (1 + z) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left]
    · exact Valuation.map_one _
    · rw [Valuation.map_one]; exact hvz
  have h1zA : 1 + z ∈ A := add_mem A.one_mem hzA
  let w : A := ⟨(1 + z) * η ^ 4, mul_mem h1zA (pow_mem hηA 4)⟩
  have hw : IsUnit w := by
    rw [A.valuation_eq_one_iff]
    show A.valuation ((1 + z) * η ^ 4) = 1
    rw [Valuation.map_mul, Valuation.map_pow, hv1z, hvη, one_pow, one_mul]

  refine ⟨η + 1, (hw.unit⁻¹ : Aˣ), (hw.unit⁻¹).isUnit, ?_⟩
  have hμ2 : (η + 1) ^ 2 = z * η := by
    linear_combination hη + (η - z * η) * h2
  have hμ8 : (η + 1) ^ 8 = t * ((1 + z) * η ^ 4) := by
    calc (η + 1) ^ 8 = ((η + 1) ^ 2) ^ 4 := by ring
      _ = z ^ 4 * η ^ 4 := by rw [hμ2]; ring
      _ = t * ((1 + z) * η ^ 4) := by rw [hz]; ring
  have hwM : ((hw.unit⁻¹ : Aˣ) : A) * w = 1 := hw.unit.inv_mul
  have hwM' : (((hw.unit⁻¹ : Aˣ) : A) : M) * ((1 + z) * η ^ 4) = 1 :=
    congrArg Subtype.val hwM
  calc t = t * ((((hw.unit⁻¹ : Aˣ) : A) : M) * ((1 + z) * η ^ 4)) := by rw [hwM', mul_one]
    _ = (((hw.unit⁻¹ : Aˣ) : A) : M) * (t * ((1 + z) * η ^ 4)) := by ring
    _ = (((hw.unit⁻¹ : Aˣ) : A) : M) * (η + 1) ^ 8 := by rw [hμ8]

end
end Dubon2026.SourceEllipticCharTwo
