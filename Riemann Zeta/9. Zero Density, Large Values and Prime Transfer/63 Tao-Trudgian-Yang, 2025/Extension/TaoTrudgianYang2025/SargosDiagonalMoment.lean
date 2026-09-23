import TaoTrudgianYang2025.SargosMomentCentral
import Mathlib.Data.Fintype.BigOperators

/-! Literal diagonal solutions give the true source near-count lower bound. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem card_sargosSourceInterval (N : ℕ) :
    (sargosSourceInterval N).card = N := by
  rw [sargosSourceInterval,Int.card_Ioc]
  have he : (2*(N : ℤ)-(N : ℤ)) = N := by ring
  rw [he,Int.toNat_natCast]

theorem card_sargosMomentTuple (N p : ℕ) :
    Fintype.card (SargosMomentTuple N p) = N^p := by
  change Fintype.card (Fin p → ↥(sargosSourceInterval N)) = N^p
  rw [Fintype.card_pi_const,Fintype.card_coe,card_sargosSourceInterval]

theorem sargosMomentNearPairs_card_ge_diagonal (N p : ℕ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    N^p ≤ (sargosMomentNearPairs N p A B).card := by
  classical
  let D : Finset (SargosMomentTuple N p × SargosMomentTuple N p) :=
    Finset.univ.image (fun t => (t,t))
  have hD : D.card = N^p := by
    dsimp only [D]
    rw [Finset.card_image_of_injective _ (fun t u h => congrArg Prod.fst h),
      Finset.card_univ,card_sargosMomentTuple]
  rw [← hD]
  apply Finset.card_le_card
  intro q hq
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
  rw [mem_sargosMomentNearPairs]
  simpa only [sub_self,abs_zero] using And.intro hA hB

theorem sargosMomentNearCount_ge_diagonal (N p : ℕ) {δ lambda : ℝ}
    (hδ : 0 ≤ δ) (hlambda : 0 ≤ lambda) :
    N^p ≤ sargosMomentNearCount N p δ lambda := by
  unfold sargosMomentNearCount
  exact sargosMomentNearPairs_card_ge_diagonal N p (by positivity) (by positivity)

theorem sargosQuartic_central_even_moment_lower {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) {Δ μ : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ) :
    (Δ*μ/64)*(N : ℝ)^p ≤
      ∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p) := by
  have hcount : (N : ℝ)^p ≤
      ((sargosMomentNearPairs N p (1/Δ) (1/μ)).card : ℝ) := by
    exact_mod_cast sargosMomentNearPairs_card_ge_diagonal N p (by positivity) (by positivity)
  have hc := sargosMomentNearCount_le_central hN p hΔ hμ
  rw [sargosMomentNearCount_physical hN p hΔ hμ] at hc
  have h := hcount.trans hc
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ Δ*μ/64)
  have he : (Δ*μ/64)*(64/(Δ*μ)) = 1 := by field_simp
  simpa only [← mul_assoc,he,one_mul] using hm

end TaoTrudgianYang2025
