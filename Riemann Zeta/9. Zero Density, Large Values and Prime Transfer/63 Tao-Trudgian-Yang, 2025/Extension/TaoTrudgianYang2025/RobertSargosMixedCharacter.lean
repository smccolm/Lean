import TaoTrudgianYang2025.RobertSargosCubicPhase
import TaoTrudgianYang2025.SargosKernelTranslation

/-! Removal of the actual constant Taylor phase by a unit-modulus
factor. The mixed remainder stays inside the exponential. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem norm_sum_character_add_constant {ι : Type*} (S : Finset ι)
    (w : ι → ℂ) (φ : ι → ℝ) (c : ℝ) :
    ‖∑ i ∈ S, w i*fordAdditiveCharacter (c+φ i)‖ =
      ‖∑ i ∈ S, w i*fordAdditiveCharacter (φ i)‖ := by
  have he : (∑ i ∈ S, w i*fordAdditiveCharacter (c+φ i)) =
      fordAdditiveCharacter c*(∑ i ∈ S, w i*fordAdditiveCharacter (φ i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [fordAdditiveCharacter_add]
    ring
  rw [he,norm_mul,sargos_character_norm,one_mul]

theorem norm_robertSargos_mixed_sum_eq {ι : Type*} (S : Finset ι)
    (w : ι → ℂ) (q h n : ι → ℝ) (f : ℝ → ℝ) (m r : ℝ) :
    ‖∑ i ∈ S, w i*fordAdditiveCharacter
      (robertSargosSymmetricDifference f (m+n i+q i) (h i)-
        robertSargosSymmetricDifference f (m+n i) (h i+r))‖ =
      ‖∑ i ∈ S, w i*fordAdditiveCharacter
        (2*iteratedDeriv 2 f m*robertSargosLinear (-r) (q i) (h i) (n i)+
          iteratedDeriv 3 f m*robertSargosTaylorQuadratic r (q i) (h i) (n i)+
          robertSargosMixedRemainder f m r (q i) (h i) (n i))‖ := by
  let φ : ι → ℝ := fun i =>
    2*iteratedDeriv 2 f m*robertSargosLinear (-r) (q i) (h i) (n i)+
      iteratedDeriv 3 f m*robertSargosTaylorQuadratic r (q i) (h i) (n i)+
      robertSargosMixedRemainder f m r (q i) (h i) (n i)
  let c : ℝ := -2*r*deriv f m-r^3/3*iteratedDeriv 3 f m
  have he (i : ι) :
      robertSargosSymmetricDifference f (m+n i+q i) (h i)-
        robertSargosSymmetricDifference f (m+n i) (h i+r) = c+φ i := by
    rw [robertSargos_mixed_taylor_identity]
    dsimp [c,φ]
    ring
  simp only [he]
  exact norm_sum_character_add_constant S w φ c

end TaoTrudgianYang2025

