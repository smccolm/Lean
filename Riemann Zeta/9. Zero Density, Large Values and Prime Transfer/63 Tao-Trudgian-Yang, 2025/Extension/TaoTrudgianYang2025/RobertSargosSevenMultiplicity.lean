import TaoTrudgianYang2025.RobertSargosSevenSystem
import TaoTrudgianYang2025.IntegerIntervalCount

/-! Exact n2 multiplicity in the seven-to-six variable displacement map. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_displacement_fiber_card_le
    (S : Finset RobertSargosSevenPoint) {R H Q N δ : ℝ} {z : RobertSargosPoint}
    (hN : 1 ≤ N) (hmem : ∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p)
    (hfix : ∀ p ∈ S, robertSargosDisplacementPoint p = z) :
    (S.card:ℝ) ≤ N := by
  classical
  let T := S.image RobertSargosSevenPoint.n₂
  have hinj : Set.InjOn RobertSargosSevenPoint.n₂ S := by
    intro p hp q hq he
    exact robertSargos_displacement_joint_injective ((hfix p hp).trans (hfix q hq).symm) he
  have hcard : T.card = S.card := Finset.card_image_of_injOn hinj
  have ht : ∀ n ∈ T, (n:ℝ) ∈ Set.Icc 1 N := by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact (hmem p hp).n₂_support
  have hb := integer_card_le_interval_length_add_one T hN ht
  rw [hcard] at hb
  linarith

theorem robertSargos_seven_card_le_displacement_image
    (S : Finset RobertSargosSevenPoint) {R H Q N δ : ℝ}
    (hN : 1 ≤ N) (hmem : ∀ p ∈ S, RobertSargosSevenSystem R H Q N δ p) :
    (S.card:ℝ) ≤ N*((S.image robertSargosDisplacementPoint).card:ℝ) := by
  classical
  let U := S.image robertSargosDisplacementPoint
  have hmaps : Set.MapsTo robertSargosDisplacementPoint S U := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hf : ∀ z : RobertSargosPoint,
      ((S.filter (fun p => robertSargosDisplacementPoint p = z)).card:ℝ) ≤ N := by
    intro z
    exact robertSargos_displacement_fiber_card_le _ hN
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ U, ((S.filter (fun p => robertSargosDisplacementPoint p = z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcardR
    _ ≤ ∑ _z ∈ U, N := Finset.sum_le_sum (fun z _ => hf z)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,mul_comm]; rfl

theorem robertSargos_count_multiplicity_algebra {N B ε : ℝ}
    (hN : 1 ≤ N) (hB : 0 ≤ B) (hε : 0 ≤ ε) :
    N*B^(1+ε) ≤ (N*B)^(1+ε) := by
  have hNp : 0 < N := by linarith
  have hp : N ≤ N^(1+ε) := by
    rw [Real.rpow_add hNp,Real.rpow_one]
    exact le_mul_of_one_le_right hNp.le (Real.one_le_rpow hN hε)
  rw [Real.mul_rpow hNp.le hB]
  exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hB _)

end TaoTrudgianYang2025

