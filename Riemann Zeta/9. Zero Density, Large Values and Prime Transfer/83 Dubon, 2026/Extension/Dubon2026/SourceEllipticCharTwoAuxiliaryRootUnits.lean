import Dubon2026.SourceEllipticTorsionIntegralCoordinates
import Mathlib.Tactic

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

theorem val_lt_one_of_z (A : ValuationSubring M) {t z : M}
    (ht : A.valuation t < 1) (hz : z ^ 4 = t * z + t) : A.valuation z < 1 := by
  let tA : A := ⟨t, (A.valuation_le_one_iff t).mp ht.le⟩
  have hzA : z ∈ A := by
    apply SourceEllipticFunctionField.mem_valuationSubring_of_integral A
    refine ⟨X ^ 4 - (C tA * X + C tA), by monicity!, ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_add, eval₂_mul, eval₂_C]
    exact sub_eq_zero.mpr hz
  let zA : A := ⟨z, hzA⟩
  have he : zA ^ 4 = tA * zA + tA := Subtype.ext hz
  have ht0 : residue A tA = 0 := (residue_eq_zero_iff tA).mpr
    ((A.valuation_lt_one_iff tA).mpr ht)
  have hr := congrArg (residue A) he
  simp only [map_pow, map_add, map_mul, ht0, zero_mul, zero_add] at hr
  have hz0 : residue A zA = 0 := (pow_eq_zero_iff (n := 4) (by norm_num)).mp hr
  exact (A.valuation_lt_one_iff zA).mp ((residue_eq_zero_iff zA).mp hz0)

theorem val_eq_one_of_eta (A : ValuationSubring M) {z η : M}
    (hz : A.valuation z ≤ 1) (hη : η ^ 2 + z * η + 1 = 0) : A.valuation η = 1 := by
  let zA : A := ⟨z, (A.valuation_le_one_iff z).mp hz⟩
  have hηA : η ∈ A := by
    apply SourceEllipticFunctionField.mem_valuationSubring_of_integral A
    refine ⟨X ^ 2 + C zA * X + 1, by monicity!, ?_⟩
    simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, eval₂_one]
    exact hη
  let ηA : A := ⟨η, hηA⟩
  have he : ηA * (ηA + zA) = -1 := by
    apply Subtype.val_injective
    change η * (η + z) = -1
    linear_combination hη
  have hu : IsUnit (ηA * (ηA + zA)) := by rw [he]; exact isUnit_one.neg
  exact (A.valuation_eq_one_iff ηA).mp (isUnit_of_mul_isUnit_left hu)

end
end Dubon2026.SourceEllipticCharTwo
