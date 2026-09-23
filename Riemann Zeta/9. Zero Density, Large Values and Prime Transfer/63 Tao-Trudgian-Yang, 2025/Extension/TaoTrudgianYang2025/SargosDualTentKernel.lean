import TaoTrudgianYang2025.SargosPlanarGram
import Mathlib.MeasureTheory.Integral.Prod

/-! The dual tent kernel: exact compact physical windows and nonnegative frequency weights. -/

noncomputable section

open MeasureTheory GafniTao
open scoped BigOperators ComplexConjugate

namespace TaoTrudgianYang2025

theorem integral_sargosRealTent_character_positive {w : ℝ}
    (hw : 0 < w) (ξ : ℝ) :
    (∫ x : ℝ, (sargosRealTent w x : ℂ)*fordAdditiveCharacter (ξ*x)) =
      (sargosSincKernel w ξ : ℂ) := by
  have h := fourier_sargosRealTent hw (-ξ)
  rw [sargos_fourier_eq_character] at h
  simpa only [neg_mul,neg_neg,sargosSincKernel,mul_neg,Real.sinc_neg] using h

theorem integrable_sargosRealTent_character_positive {w : ℝ}
    (hw : 0 < w) (ξ : ℝ) :
    Integrable (fun x : ℝ => (sargosRealTent w x : ℂ)*fordAdditiveCharacter (ξ*x)) := by
  have hc : Continuous (fun x : ℝ =>
      (sargosRealTent w x : ℂ)*fordAdditiveCharacter (ξ*x)) := by
    have ht := continuous_sargosRealTent w
    unfold fordAdditiveCharacter
    fun_prop
  apply (integrable_sargosRealTent hw).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [norm_mul,sargos_character_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sargosRealTent_nonneg w x)])

def sargosTentKernelTerm (a b ξ η : ℝ) (p : ℝ × ℝ) : ℂ :=
  ((sargosRealTent a p.1 : ℂ)*fordAdditiveCharacter (ξ*p.1))*
    ((sargosRealTent b p.2 : ℂ)*fordAdditiveCharacter (η*p.2))

theorem integrable_sargosTentKernelTerm {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ξ η : ℝ) :
    Integrable (sargosTentKernelTerm a b ξ η) (volume.prod volume) :=
  (integrable_sargosRealTent_character_positive ha ξ).mul_prod
    (integrable_sargosRealTent_character_positive hb η)

theorem integral_sargosTentKernelTerm {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ξ η : ℝ) :
    (∫ p : ℝ × ℝ, sargosTentKernelTerm a b ξ η p ∂(volume.prod volume)) =
      (sargosSincKernel a ξ : ℂ)*(sargosSincKernel b η : ℂ) := by
  unfold sargosTentKernelTerm
  rw [integral_prod_mul
    (fun x : ℝ => (sargosRealTent a x : ℂ)*fordAdditiveCharacter (ξ*x))
    (fun y : ℝ => (sargosRealTent b y : ℂ)*fordAdditiveCharacter (η*y)),
    integral_sargosRealTent_character_positive ha ξ,
    integral_sargosRealTent_character_positive hb η]

def sargosTentPlanarIntegrand {ι : Type*} (S : Finset ι) (u v : ι → ℝ)
    (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  sargosRealTent a p.1*sargosRealTent b p.2*
    ‖sargosPlanarSum S (fun _ => 1) u v p.1 p.2‖^2

theorem sargosTentPlanarIntegrand_eq_gram {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) (a b : ℝ) (p : ℝ × ℝ) :
    (sargosTentPlanarIntegrand S u v a b p : ℂ) =
      ∑ q ∈ S ×ˢ S, sargosTentKernelTerm a b (u q.1-u q.2) (v q.1-v q.2) p := by
  unfold sargosTentPlanarIntegrand
  rw [Complex.ofReal_mul,Complex.ofReal_mul,sargosPlanarSum_norm_sq,Finset.mul_sum]
  simp only [map_one,mul_one,one_mul]
  apply Finset.sum_congr rfl
  intro q hq
  unfold sargosTentKernelTerm
  rw [fordAdditiveCharacter_add]
  ring

theorem sargosTentPlanarIntegrand_nonneg {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) (a b : ℝ) (p : ℝ × ℝ) :
    0 ≤ sargosTentPlanarIntegrand S u v a b p :=
  mul_nonneg (mul_nonneg (sargosRealTent_nonneg a p.1) (sargosRealTent_nonneg b p.2))
    (sq_nonneg _)

end TaoTrudgianYang2025
