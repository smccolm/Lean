import TaoTrudgianYang2025.RobertSargosTaylorSystem
import TaoTrudgianYang2025.RobertSargosSevenCount

/-! The proved seven-variable theorem applied to the actual Taylor
coordinates. No count of Taylor coincidences is supplied as a premise. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem exists_robertSargos_taylor_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N E : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 ≤ E → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosTaylorSystem R H Q N E p) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+(E+12*R*H^2)/(H*Q)) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_seven_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N E hR hH hQ hN hE hRH hS
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  let δ := (E+12*R*H^2)/(H*Q^2)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hscale : E+12*R*H^2 = δ*H*Q^2 := by
    dsimp [δ]
    field_simp
  have hcard : (S.image robertSargosReverseR).card = S.card :=
    Finset.card_image_of_injective S robertSargos_reverseR_injective
  have ht := hcount (S.image robertSargosReverseR) R H Q N δ hR hH hQ hN hδ hRH
    (by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact (hS q hq).to_counting (by linarith) hHp.le (by linarith) hscale.le)
  have hfactor : 1+δ*Q = 1+(E+12*R*H^2)/(H*Q) := by
    dsimp [δ]
    field_simp
  rwa [hcard,hfactor] at ht

theorem exists_robertSargos_taylor_count_small_correction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosSevenPoint) (R H Q N E : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 1 ≤ N → 0 ≤ E → R ≤ H/2 →
      R*H^2 ≤ E → (∀ p ∈ S, RobertSargosTaylorSystem R H Q N E p) →
      (S.card:ℝ) ≤ C*(R*N*H*Q)^(1+ε)*(1+13*E/(H*Q)) := by
  obtain ⟨C,hC,hcount⟩ := exists_robertSargos_taylor_count ε hε
  refine ⟨C,hC,?_⟩
  intro S R H Q N E hR hH hQ hN hE hRH hsmall hS
  apply (hcount S R H Q N E hR hH hQ hN hE hRH hS).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hd : 0 < H*Q := by positivity
  have he : E+12*R*H^2 ≤ 13*E := by nlinarith only [hsmall]
  exact add_le_add_right (div_le_div_of_nonneg_right he hd.le) 1

end TaoTrudgianYang2025
