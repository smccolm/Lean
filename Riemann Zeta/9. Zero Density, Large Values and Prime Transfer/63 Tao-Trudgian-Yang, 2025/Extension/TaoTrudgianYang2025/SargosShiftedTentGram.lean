import TaoTrudgianYang2025.SargosDualTentWindow

/-! Shifted frequency windows are controlled by the same unshifted physical moment. -/

noncomputable section

open MeasureTheory GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosShiftedNearPairs {ι : Type*} (S : Finset ι) (u v : ι → ℝ)
    (c d A B : ℝ) : Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter
    (fun p => |u p.1-u p.2-c| ≤ A ∧ |v p.1-v p.2-d| ≤ B)

theorem sargosTentKernelTerm_eq_product (a b ξ η : ℝ) (p : ℝ × ℝ) :
    sargosTentKernelTerm a b ξ η p =
      (sargosRealTent a p.1 : ℂ)*(sargosRealTent b p.2 : ℂ)*
        fordAdditiveCharacter (ξ*p.1+η*p.2) := by
  rw [fordAdditiveCharacter_add]
  unfold sargosTentKernelTerm
  ring

theorem sargosTentKernelTerm_shift (a b ξ η c d : ℝ) (p : ℝ × ℝ) :
    sargosTentKernelTerm a b (ξ-c) (η-d) p =
      sargosTentKernelTerm a b ξ η p*
        fordAdditiveCharacter (-(c*p.1+d*p.2)) := by
  rw [sargosTentKernelTerm_eq_product,sargosTentKernelTerm_eq_product]
  rw [show (ξ-c)*p.1+(η-d)*p.2 = ξ*p.1+η*p.2+(-(c*p.1+d*p.2)) by ring,
    fordAdditiveCharacter_add]
  ring

theorem sargos_shifted_tent_gram_eq {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) (a b c d : ℝ) (p : ℝ × ℝ) :
    (∑ q ∈ S ×ˢ S,
      sargosTentKernelTerm a b (u q.1-u q.2-c) (v q.1-v q.2-d) p) =
      (sargosTentPlanarIntegrand S u v a b p : ℂ)*
        fordAdditiveCharacter (-(c*p.1+d*p.2)) := by
  have hterm (q : ι × ι) :=
    sargosTentKernelTerm_shift a b (u q.1-u q.2) (v q.1-v q.2) c d p
  simp_rw [hterm]
  rw [← Finset.sum_mul,sargosTentPlanarIntegrand_eq_gram]

theorem sargos_shifted_tent_gram_le_integral {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    (∑ q ∈ S ×ˢ S,
      sargosSincKernel a (u q.1-u q.2-c)*sargosSincKernel b (v q.1-v q.2-d)) ≤
      ∫ p : ℝ × ℝ, sargosTentPlanarIntegrand S u v a b p ∂(volume.prod volume) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    ∑ q ∈ S ×ˢ S, sargosTentKernelTerm a b (u q.1-u q.2-c) (v q.1-v q.2-d) p
  let G : ℝ := ∑ q ∈ S ×ˢ S,
    sargosSincKernel a (u q.1-u q.2-c)*sargosSincKernel b (v q.1-v q.2-d)
  have he : (∫ p, F p ∂(volume.prod volume)) = (G:ℂ) := by
    dsimp [F,G]
    rw [integral_finsetSum _ (fun q _ => integrable_sargosTentKernelTerm ha hb _ _)]
    simp_rw [integral_sargosTentKernelTerm ha hb]
    push_cast
    rfl
  have hG : 0 ≤ G := Finset.sum_nonneg (fun q _ =>
    mul_nonneg (sargosSincKernel_nonneg ha.le _) (sargosSincKernel_nonneg hb.le _))
  have hn (p : ℝ × ℝ) : ‖F p‖ = sargosTentPlanarIntegrand S u v a b p := by
    dsimp [F]
    rw [sargos_shifted_tent_gram_eq,norm_mul,sargos_character_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sargosTentPlanarIntegrand_nonneg S u v a b p)]
  have h := norm_integral_le_integral_norm (μ := volume.prod volume) F
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hG] at h
  simpa only [hn] using h

end TaoTrudgianYang2025
