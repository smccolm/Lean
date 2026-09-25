import TaoTrudgianYang2025.SargosPlanarIntegral
import TaoTrudgianYang2025.BetaBufferedCutoff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Algebra.Order.Chebyshev
import TaoTrudgianYang2025.SargosPlanarRegularity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Pi
import TaoTrudgianYang2025.SargosQuarticKernelJets
import GafniTao.WooleyNative
import TaoTrudgianYang2025.IntegerFourierWindows

/-!
# Finite separated-parabola localization

This proves the finite, sinc-weighted cancellation and bounded-overlap step
underlying the Fefferman--Cordoba argument in Li, arXiv:1805.10551, Lemma 2.7.
Both frequency coordinates, arbitrary coefficients, all finite multiplicities,
and translations of the integration kernel are retained. The final factor
7/nu is derived from the actual integer block count.

The rapid-cutoff and averaging continuations prove finite source-weighted
localization on arbitrary separated intervals. An interval-adapted Fourier band
is proved stable under actual parabolic rescaling and contains the constructed
nonzero cutoff. Actual weighted moments satisfy rescaling and localization;
closed grids, bilinear reduction, product-grid composition and dyadic iteration
are proved using strictly smaller linear scales. An explicit numerical majorant
and strong induction prove dyadic finite weighted decoupling for every positive
epsilon. An actual cubic/quartic cutoff, uniform Fourier bounds and sixth-moment
transfer now prove physical-box decoupling with a bounded variable remainder.
The actual four-coordinate source curve has an exact quartic entry, a derived
frame Jacobian and product reduction, and linked-scale Fourier-averaged
decoupling. The inverse multiplier and transverse averaging return the
parabolic cell norms to actual four-dimensional radial curve-cell moments,
giving a linked-scale local bilinear source-curve decoupling theorem.
Actual four-dimensional shift averaging and a genuine all-scale polynomial
starting bound are also proved; its normalized dyadic growth is N^22.
The actual-source smaller-grid recurrence and strong induction now prove
global dyadic bilinear source-curve decoupling with every positive epsilon
loss. The constant depends only on epsilon and positive root-frequency
separation; the polynomial base and all scale conditions are derived.
The original-source global larger-anisotropic bilinear moment is now proved
at T=2^(4*j), with bound C(epsilon,nu)*2^(epsilon*j)*T^12*B^6*H^6.
Actual middle-coordinate averaging and canonical fine cells consume the
native quadratic VMVT through exact weighted Fourier periods. Multiplicities
are retained through coefficient-fiber masses B,H. Exact integer dilation
and the physical Jacobian extend the bilinear estimate to every real T>=1
on the comparable-frequency annulus [T/2,T]. The localized shifted-phase
estimate, bilinear-to-linear first spacing and the Bourgain pair remain open;
no continuous or general-curve theorem is claimed.
-/

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

theorem parabola_sixth_frequency_gap
    {x x' y₁ y₂ y₃ y₄ w ρ b : ℝ}
    (hw : 0 ≤ w) (hρ : 0 < ρ)
    (h₁ : y₁ ∈ Icc 0 w) (h₂ : y₂ ∈ Icc 0 w)
    (h₃ : y₃ ∈ Icc 0 w) (h₄ : y₄ ∈ Icc 0 w)
    (hsep : ρ ≤ |x+x'|)
    (hgap : (b+2*w^2)/ρ < |x-x'|) :
    b < |x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2)| := by
  have hs₁ : y₁^2 ≤ w^2 := by nlinarith [h₁.1,h₁.2]
  have hs₂ : y₂^2 ≤ w^2 := by nlinarith [h₂.1,h₂.2]
  have hs₃ : y₃^2 ≤ w^2 := by nlinarith [h₃.1,h₃.2]
  have hs₄ : y₄^2 ≤ w^2 := by nlinarith [h₄.1,h₄.2]
  by_contra hn
  have hf := abs_le.mp (le_of_not_gt hn)
  have hd : |x^2-x'^2| ≤ b+2*w^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg y₁,sq_nonneg y₂,sq_nonneg y₃,sq_nonneg y₄]
  have he : |x-x'| * |x+x'| = |x^2-x'^2| := by
    rw [← abs_mul]
    congr 1
    ring
  have hg := (div_lt_iff₀ hρ).mp hgap
  have hm := mul_le_mul_of_nonneg_left hsep (abs_nonneg (x-x'))
  nlinarith only [hd,he,hg,hm]

theorem parabola_same_interval_separation
    {x x' d u ν : ℝ} (hν : 0 ≤ ν)
    (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : x ∈ Icc d (d+u)) (hx' : x' ∈ Icc d (d+u)) :
    4*ν ≤ |x+x'| := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h] at hd
    have hp : 0 ≤ x+x' := by linarith [hx.1,hx'.1]
    rw [abs_of_nonneg hp]
    linarith [hx.1,hx'.1]
  · rw [abs_of_nonpos h] at hd
    have hp : x+x' ≤ 0 := by linarith [hx.2,hx'.2]
    rw [abs_of_nonpos hp]
    linarith [hx.2,hx'.2]

theorem integral_parabola_sixth_kernel_eq_zero
    {x x' y₁ y₂ y₃ y₄ w d u ν a b : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (ha : 0 < a) (hb : 0 < b)
    (hwidth : b ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : x ∈ Icc d (d+u)) (hx' : x' ∈ Icc d (d+u))
    (h₁ : y₁ ∈ Icc 0 w) (h₂ : y₂ ∈ Icc 0 w)
    (h₃ : y₃ ∈ Icc 0 w) (h₄ : y₄ ∈ Icc 0 w)
    (hgap : 2*w^2/ν ≤ |x-x'|) (c e : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ,
      sargosPlanarKernelTerm a b c e
        (x+y₁+y₂-(x'+y₃+y₄))
        (x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2)) α γ) = 0 := by
  apply integral_sargosPlanarKernelTerm_eq_zero ha hb (Or.inr ?_)
  apply le_of_lt
  apply parabola_sixth_frequency_gap hw.le (by positivity : 0 < 4*ν)
    h₁ h₂ h₃ h₄ (parabola_same_interval_separation hν.le hu hd hx hx')
  have hg := (div_le_iff₀ hν).mp hgap
  apply (div_lt_iff₀ (by positivity : 0 < 4*ν)).mpr
  nlinarith [sq_pos_of_pos hw]

private theorem planarSum_mul {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) (α γ : ℝ) :
    sargosPlanarSum S z u v α γ * sargosPlanarSum T w p q α γ =
      sargosPlanarSum (S ×ˢ T) (fun i => z i.1*w i.2)
        (fun i => u i.1+p i.2) (fun i => v i.1+q i.2) α γ := by
  unfold sargosPlanarSum
  rw [Finset.sum_mul_sum,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (z i*w j)*(fordAdditiveCharacter (u i*α+v i*γ)*
        fordAdditiveCharacter (p j*α+q j*γ)) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 2
      ring

private def planarCross {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) (a b c d α γ : ℝ) : ℂ :=
  ((sargosSincKernel a (α-c)*sargosSincKernel b (γ-d) : ℝ) : ℂ)*
    sargosPlanarSum S z u v α γ * conj (sargosPlanarSum T w p q α γ)

private theorem planarCross_expand {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) (a b c d α γ : ℝ) :
    planarCross S T z w u v p q a b c d α γ =
      ∑ ij ∈ S ×ˢ T, (z ij.1*conj (w ij.2))*
        sargosPlanarKernelTerm a b c d (u ij.1-p ij.2) (v ij.1-q ij.2) α γ := by
  unfold planarCross sargosPlanarSum
  rw [map_sum,mul_assoc,Finset.sum_mul_sum,Finset.sum_product]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,conj_fordAdditiveCharacter]
  unfold sargosPlanarKernelTerm
  rw [Complex.ofReal_mul]
  calc
    _ = (z i*conj (w j))*
        ((sargosSincKernel a (α-c) : ℂ)*(sargosSincKernel b (γ-d) : ℂ)*
          (fordAdditiveCharacter (u i*α+v i*γ)*
            fordAdditiveCharacter (-(p j*α+q j*γ)))) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 3
      ring

private theorem integral_planarCross {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, planarCross S T z w u v p q a b c d α γ) =
      ∑ ij ∈ S ×ˢ T, (z ij.1*conj (w ij.2))*
        ∫ α : ℝ, ∫ γ : ℝ,
          sargosPlanarKernelTerm a b c d (u ij.1-p ij.2) (v ij.1-q ij.2) α γ := by
  simp_rw [planarCross_expand]
  have hi (α : ℝ) (ij : ι × κ) : Integrable (fun γ : ℝ =>
      (z ij.1*conj (w ij.2))*
        sargosPlanarKernelTerm a b c d (u ij.1-p ij.2) (v ij.1-q ij.2) α γ) :=
    (integrable_sargosPlanarKernelTerm_inner hb a c d
      (u ij.1-p ij.2) (v ij.1-q ij.2) α).const_mul _
  simp_rw [integral_finsetSum (S ×ˢ T) (fun ij _ => hi _ ij), integral_const_mul]
  rw [integral_finsetSum (S ×ˢ T) (fun ij _ =>
    (integrable_sargosPlanarKernelTerm_outer ha hb c d
      (u ij.1-p ij.2) (v ij.1-q ij.2)).const_mul _)]
  simp_rw [integral_const_mul]


private theorem planarCross_inner_integrable {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) {b : ℝ}
    (hb : 0 < b) (a c d α : ℝ) :
    Integrable (planarCross S T z w u v p q a b c d α) := by
  change Integrable (fun γ => planarCross S T z w u v p q a b c d α γ)
  simp_rw [planarCross_expand]
  apply integrable_finsetSum
  intro ij hij
  exact (integrable_sargosPlanarKernelTerm_inner hb a c d
    (u ij.1-p ij.2) (v ij.1-q ij.2) α).const_mul _

private theorem planarCross_outer_integrable {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    Integrable (fun α : ℝ => ∫ γ : ℝ,
      planarCross S T z w u v p q a b c d α γ) := by
  simp_rw [planarCross_expand]
  have hi (α : ℝ) (ij : ι × κ) : Integrable (fun γ : ℝ =>
      (z ij.1*conj (w ij.2))*
        sargosPlanarKernelTerm a b c d (u ij.1-p ij.2) (v ij.1-q ij.2) α γ) :=
    (integrable_sargosPlanarKernelTerm_inner hb a c d
      (u ij.1-p ij.2) (v ij.1-q ij.2) α).const_mul _
  simp_rw [integral_finsetSum (S ×ˢ T) (fun ij _ => hi _ ij),integral_const_mul]
  apply integrable_finsetSum
  intro ij hij
  exact (integrable_sargosPlanarKernelTerm_outer ha hb c d
    (u ij.1-p ij.2) (v ij.1-q ij.2)).const_mul _

private theorem doubleIntegral_re (f : ℝ → ℝ → ℂ)
    (hi : ∀ x, Integrable (f x))
    (ho : Integrable (fun x => ∫ y, f x y)) :
    (∫ x, ∫ y, f x y).re = ∫ x, ∫ y, (f x y).re := by
  calc
    _ = ∫ x, (∫ y, f x y).re := (integral_re ho).symm
    _ = _ := by
      congr 1
      funext x
      exact (integral_re (hi x)).symm

private theorem planarCross_self {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (a b c d α γ : ℝ) :
    planarCross S S z z u v u v a b c d α γ =
      (sargosWeightedPlanarIntegrand S z u v a b c d α γ : ℂ) := by
  unfold planarCross sargosWeightedPlanarIntegrand
  rw [mul_assoc,Complex.mul_conj']
  push_cast
  ring

private theorem planarCross_real_le {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (u v : ι → ℝ) (p q : κ → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    2*(∫ α : ℝ, ∫ γ : ℝ, planarCross S T z w u v p q a b c d α γ).re ≤
      (∫ α : ℝ, ∫ γ : ℝ, sargosWeightedPlanarIntegrand S z u v a b c d α γ)+
      (∫ α : ℝ, ∫ γ : ℝ, sargosWeightedPlanarIntegrand T w p q a b c d α γ) := by
  rw [doubleIntegral_re _
    (planarCross_inner_integrable S T z w u v p q hb a c d)
    (planarCross_outer_integrable S T z w u v p q ha hb c d)]
  have hpoint (α γ : ℝ) :
      2*(planarCross S T z w u v p q a b c d α γ).re ≤
        sargosWeightedPlanarIntegrand S z u v a b c d α γ+
        sargosWeightedPlanarIntegrand T w p q a b c d α γ := by
    let A := sargosPlanarSum S z u v α γ
    let B := sargosPlanarSum T w p q α γ
    let W := sargosSincKernel a (α-c)*sargosSincKernel b (γ-d)
    have hW : 0 ≤ W := mul_nonneg (sargosSincKernel_nonneg ha.le _)
      (sargosSincKernel_nonneg hb.le _)
    have hab : (A*conj B).re ≤ ‖A‖*‖B‖ := by
      simpa only [norm_mul,Complex.norm_conj] using Complex.re_le_norm (A*conj B)
    have hc : 2*(A*conj B).re ≤ ‖A‖^2+‖B‖^2 := by
      nlinarith [sq_nonneg (‖A‖-‖B‖)]
    have hm := mul_le_mul_of_nonneg_left hc hW
    change 2*((W : ℂ)*A*conj B).re ≤ W*‖A‖^2+W*‖B‖^2
    rw [mul_assoc,Complex.re_ofReal_mul]
    nlinarith only [hm]
  have hi (α : ℝ) : Integrable (fun γ =>
      (planarCross S T z w u v p q a b c d α γ).re) :=
    (planarCross_inner_integrable S T z w u v p q hb a c d α).re
  have ho : Integrable (fun α => ∫ γ,
      (planarCross S T z w u v p q a b c d α γ).re) := by
    have hr (α : ℝ) :
        (∫ γ, planarCross S T z w u v p q a b c d α γ).re =
          ∫ γ, (planarCross S T z w u v p q a b c d α γ).re :=
      (integral_re (planarCross_inner_integrable S T z w u v p q hb a c d α)).symm
    simp_rw [← hr]
    exact (planarCross_outer_integrable S T z w u v p q ha hb c d).re
  have hinner (α : ℝ) :
      2*(∫ γ, (planarCross S T z w u v p q a b c d α γ).re) ≤
      (∫ γ, sargosWeightedPlanarIntegrand S z u v a b c d α γ)+
      (∫ γ, sargosWeightedPlanarIntegrand T w p q a b c d α γ) := by
    rw [← integral_const_mul,← integral_add
      (integrable_sargosWeightedPlanarIntegrand_inner S z u v hb a c d α)
      (integrable_sargosWeightedPlanarIntegrand_inner T w p q hb a c d α)]
    exact integral_mono ((hi α).const_mul 2)
      ((integrable_sargosWeightedPlanarIntegrand_inner S z u v hb a c d α).add
        (integrable_sargosWeightedPlanarIntegrand_inner T w p q hb a c d α))
      (hpoint α)
  rw [← integral_const_mul,← integral_add
    (integrable_sargosWeightedPlanarIntegrand_outer S z u v ha hb c d)
    (integrable_sargosWeightedPlanarIntegrand_outer T w p q ha hb c d)]
  exact integral_mono (ho.const_mul 2)
    ((integrable_sargosWeightedPlanarIntegrand_outer S z u v ha hb c d).add
      (integrable_sargosWeightedPlanarIntegrand_outer T w p q ha hb c d)) hinner

theorem integral_parabola_cross_moment_eq_zero
    {ι κ τ : Type*} (S : Finset ι) (T : Finset κ) (V : Finset τ)
    (z : ι → ℂ) (z' : κ → ℂ) (a₀ : τ → ℂ)
    (x : ι → ℝ) (x' : κ → ℝ) (y : τ → ℝ)
    {w d u ν a b : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (ha : 0 < a) (hb : 0 < b)
    (hwidth : b ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : ∀ i ∈ S, x i ∈ Icc d (d+u))
    (hx' : ∀ j ∈ T, x' j ∈ Icc d (d+u))
    (hy : ∀ k ∈ V, y k ∈ Icc 0 w)
    (hgap : ∀ i ∈ S, ∀ j ∈ T, 2*w^2/ν ≤ |x i-x' j|)
    (c e : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ,
      ((sargosSincKernel a (α-c)*sargosSincKernel b (γ-e) : ℝ) : ℂ)*
        sargosPlanarSum S z x (fun i => (x i)^2) α γ *
        conj (sargosPlanarSum T z' x' (fun j => (x' j)^2) α γ) *
        (‖sargosPlanarSum V a₀ y (fun k => (y k)^2) α γ‖^4 : ℝ)) = 0 := by
  let Z := fun ij : (ι × τ) × τ => (z ij.1.1*a₀ ij.1.2)*a₀ ij.2
  let Z' := fun ij : (κ × τ) × τ => (z' ij.1.1*a₀ ij.1.2)*a₀ ij.2
  let X := fun ij : (ι × τ) × τ => (x ij.1.1+y ij.1.2)+y ij.2
  let X' := fun ij : (κ × τ) × τ => (x' ij.1.1+y ij.1.2)+y ij.2
  let Y := fun ij : (ι × τ) × τ => ((x ij.1.1)^2+(y ij.1.2)^2)+(y ij.2)^2
  let Y' := fun ij : (κ × τ) × τ => ((x' ij.1.1)^2+(y ij.1.2)^2)+(y ij.2)^2
  have heq (α γ : ℝ) :
      ((sargosSincKernel a (α-c)*sargosSincKernel b (γ-e) : ℝ) : ℂ)*
        sargosPlanarSum S z x (fun i => (x i)^2) α γ *
        conj (sargosPlanarSum T z' x' (fun j => (x' j)^2) α γ) *
        (‖sargosPlanarSum V a₀ y (fun k => (y k)^2) α γ‖^4 : ℝ) =
      planarCross ((S ×ˢ V) ×ˢ V) ((T ×ˢ V) ×ˢ V) Z Z' X Y X' Y' a b c e α γ := by
    dsimp [planarCross,Z,Z',X,X',Y,Y']
    rw [← planarSum_mul (S ×ˢ V) V (fun ij => z ij.1*a₀ ij.2) a₀
      (fun ij => x ij.1+y ij.2) (fun ij => (x ij.1)^2+(y ij.2)^2) y
      (fun k => (y k)^2) α γ,
      ← planarSum_mul (T ×ˢ V) V (fun ij => z' ij.1*a₀ ij.2) a₀
      (fun ij => x' ij.1+y ij.2) (fun ij => (x' ij.1)^2+(y ij.2)^2) y
      (fun k => (y k)^2) α γ,
      ← planarSum_mul S V z a₀ x (fun i => (x i)^2) y (fun k => (y k)^2) α γ,
      ← planarSum_mul T V z' a₀ x' (fun j => (x' j)^2) y (fun k => (y k)^2) α γ]
    rw [map_mul,map_mul]
    let A := sargosPlanarSum V a₀ y (fun k => (y k)^2) α γ
    have hn : (‖A‖^4 : ℝ) = ((A*conj A)^2 : ℂ) := by
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [show (‖sargosPlanarSum V a₀ y (fun k => (y k)^2) α γ‖^4 : ℝ) =
      ((A*conj A)^2 : ℂ) from hn]
    dsimp [A]
    ring
  simp_rw [heq]
  rw [integral_planarCross _ _ _ _ _ _ _ _ ha hb]
  apply Finset.sum_eq_zero
  intro ij hij
  have hi := Finset.mem_product.mp (Finset.mem_product.mp hij).1
  have hj := Finset.mem_product.mp (Finset.mem_product.mp hij).2
  have his := Finset.mem_product.mp hi.1
  have hjt := Finset.mem_product.mp hj.1
  have hz := integral_parabola_sixth_kernel_eq_zero hw hν ha hb hwidth hu hd
    (hx _ his.1) (hx' _ hjt.1) (hy _ his.2) (hy _ hi.2)
    (hy _ hjt.2) (hy _ hj.2) (hgap _ his.1 _ hjt.1) c e
  dsimp [X,Y,X',Y']
  rw [hz,mul_zero]


private theorem banded_real_sum_le (J : Finset ℤ) (G : ℤ → ℤ → ℝ)
    (E : ℤ → ℝ) (m : ℕ)
    (hE : ∀ i ∈ J, 0 ≤ E i)
    (hG : ∀ i ∈ J, ∀ j ∈ J, 2*G i j ≤ E i+E j)
    (hzero : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| → G i j = 0) :
    ∑ i ∈ J, ∑ j ∈ J, G i j ≤ (2*(m : ℝ)+1)*∑ i ∈ J, E i := by
  classical
  have hcard (i : ℤ) : ((J.filter (fun j => |i-j| ≤ (m : ℤ))).card : ℝ) ≤
      2*(m : ℝ)+1 := by
    have hs : J.filter (fun j => |i-j| ≤ (m : ℤ)) ⊆
        Finset.Icc (i-(m : ℤ)) (i+(m : ℤ)) := by
      intro j hj
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      apply Finset.mem_Icc.mpr
      constructor <;> omega
    have hn : (J.filter (fun j => |i-j| ≤ (m : ℤ))).card ≤ 2*m+1 := by
      calc
        _ ≤ (Finset.Icc (i-(m : ℤ)) (i+(m : ℤ))).card := Finset.card_le_card hs
        _ = 2*m+1 := by rw [Int.card_Icc]; omega
    exact_mod_cast hn
  let A : ℤ → ℤ → ℝ := fun i j => if |i-j| ≤ (m : ℤ) then E i else 0
  have ha : (∑ i ∈ J, ∑ j ∈ J, A i j) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, E i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = ((J.filter (fun j => |i-j| ≤ (m : ℤ))).card : ℝ)*E i := by
        dsimp [A]
        rw [← Finset.sum_filter]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (hcard i) (hE i hi)
  have hab : 2*(∑ i ∈ J, ∑ j ∈ J, G i j) ≤
      (∑ i ∈ J, ∑ j ∈ J, A i j)+(∑ i ∈ J, ∑ j ∈ J, A j i) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    dsimp [A]
    rw [abs_sub_comm j i]
    by_cases h : |i-j| ≤ (m : ℤ)
    · simp only [if_pos h]
      exact hG i hi j hj
    · simp only [if_neg h,hzero i hi j hj (lt_of_not_ge h),mul_zero,add_zero,le_refl]
  have hswap : (∑ i ∈ J, ∑ j ∈ J, A j i) = ∑ i ∈ J, ∑ j ∈ J, A i j :=
    Finset.sum_comm
  rw [hswap] at hab
  linarith


private theorem planarFamily_integral_gram {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι)
    (z : ℤ → ι → ℂ) (u v : ℤ → ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    ((∫ α : ℝ, ∫ γ : ℝ,
      sargosWeightedPlanarIntegrand (J.sigma S)
        (fun ij => z ij.1 ij.2) (fun ij => u ij.1 ij.2) (fun ij => v ij.1 ij.2)
        a b c d α γ : ℝ) : ℂ) =
    ∑ i ∈ J, ∑ j ∈ J, ∫ α : ℝ, ∫ γ : ℝ,
      planarCross (S i) (S j) (z i) (z j) (u i) (v i) (u j) (v j) a b c d α γ := by
  rw [integral_sargosWeightedPlanarIntegrand_eq_gram _ _ _ _ ha hb]
  simp only [Finset.sum_product,Finset.sum_sigma]
  simp_rw [integral_planarCross _ _ _ _ _ _ _ _ ha hb,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]

private theorem planarFamily_banded_bound {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι)
    (z : ℤ → ι → ℂ) (u v : ℤ → ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d : ℝ) (m : ℕ)
    (hzero : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ α : ℝ, ∫ γ : ℝ,
        planarCross (S i) (S j) (z i) (z j) (u i) (v i) (u j) (v j)
          a b c d α γ) = 0) :
    (∫ α : ℝ, ∫ γ : ℝ,
      sargosWeightedPlanarIntegrand (J.sigma S)
        (fun ij => z ij.1 ij.2) (fun ij => u ij.1 ij.2) (fun ij => v ij.1 ij.2)
        a b c d α γ) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, ∫ α : ℝ, ∫ γ : ℝ,
        sargosWeightedPlanarIntegrand (S i) (z i) (u i) (v i) a b c d α γ := by
  have he := congrArg Complex.re (planarFamily_integral_gram J S z u v ha hb c d)
  simp only [Complex.ofReal_re,Complex.re_sum] at he
  rw [he]
  apply banded_real_sum_le
  · intro i hi
    apply integral_nonneg
    intro α
    apply integral_nonneg
    intro γ
    exact sargosWeightedPlanarIntegrand_nonneg _ _ _ _ ha.le hb.le c d α γ
  · intro i hi j hj
    exact planarCross_real_le _ _ _ _ _ _ _ _ ha hb c d
  · intro i hi j hj hgap
    rw [hzero i hi j hj hgap]
    rfl


private theorem parabola_product_sum {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum ((S ×ˢ V) ×ˢ V)
      (fun ij => z ij.1.1*c ij.1.2*c ij.2)
      (fun ij => x ij.1.1+y ij.1.2+y ij.2)
      (fun ij => (x ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2) α γ =
    sargosPlanarSum S z x (fun i => (x i)^2) α γ *
      (sargosPlanarSum V c y (fun k => (y k)^2) α γ)^2 := by
  rw [← planarSum_mul (S ×ˢ V) V (fun ij => z ij.1*c ij.2) c
    (fun ij => x ij.1+y ij.2) (fun ij => (x ij.1)^2+(y ij.2)^2) y
    (fun k => (y k)^2) α γ,
    ← planarSum_mul S V z c x (fun i => (x i)^2) y (fun k => (y k)^2) α γ]
  ring

def parabolaBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (a b r t : ℝ) : ℝ :=
  ∫ α : ℝ, ∫ γ : ℝ,
    sargosSincKernel a (α-r)*sargosSincKernel b (γ-t)*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) α γ‖^2 *
      ‖sargosPlanarSum V c y (fun k => (y k)^2) α γ‖^4

private theorem parabolaMoment_flat {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (a b r t : ℝ) :
    parabolaBilinearMoment S V z c x y a b r t =
      ∫ α : ℝ, ∫ γ : ℝ,
        sargosWeightedPlanarIntegrand ((S ×ˢ V) ×ˢ V)
          (fun ij => z ij.1.1*c ij.1.2*c ij.2)
          (fun ij => x ij.1.1+y ij.1.2+y ij.2)
          (fun ij => (x ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2) a b r t α γ := by
  unfold parabolaBilinearMoment sargosWeightedPlanarIntegrand
  congr 1
  funext α
  congr 1
  funext γ
  rw [parabola_product_sum,norm_mul,norm_pow]
  ring

private theorem parabola_family_product_sum {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ) (α γ : ℝ) :
    sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
      (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
      (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
      (fun ij => (x ij.1 ij.2.1.1)^2+(y ij.2.1.2)^2+(y ij.2.2)^2) α γ =
    sargosPlanarSum (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2) (fun ij => (x ij.1 ij.2)^2) α γ *
      (sargosPlanarSum V c y (fun k => (y k)^2) α γ)^2 := by
  change (∑ ij ∈ J.sigma (fun i => (S i ×ˢ V) ×ˢ V), _) = _
  rw [Finset.sum_sigma]
  change (∑ i ∈ J, sargosPlanarSum ((S i ×ˢ V) ×ˢ V)
    (fun ij => z i ij.1.1*c ij.1.2*c ij.2)
    (fun ij => x i ij.1.1+y ij.1.2+y ij.2)
    (fun ij => (x i ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2) α γ) = _
  simp_rw [parabola_product_sum]
  rw [← Finset.sum_mul]
  congr 1
  simp only [sargosPlanarSum,Finset.sum_sigma]

private theorem parabolaMoment_family_flat {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ) (a b r t : ℝ) :
    parabolaBilinearMoment (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y a b r t =
      ∫ α : ℝ, ∫ γ : ℝ,
        sargosWeightedPlanarIntegrand (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
          (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
          (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
          (fun ij => (x ij.1 ij.2.1.1)^2+(y ij.2.1.2)^2+(y ij.2.2)^2)
          a b r t α γ := by
  unfold parabolaBilinearMoment sargosWeightedPlanarIntegrand
  congr 1
  funext α
  congr 1
  funext γ
  rw [parabola_family_product_sum,norm_mul,norm_pow]
  ring


private theorem parabola_block_gap_closed {i j : ℤ} {m : ℕ} {x x' d w ν : ℝ}
    (hm : 2/ν ≤ (m : ℝ))
    (hx : x ∈ Icc (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (hx' : x' ∈ Icc (d+w^2*(j : ℝ)) (d+w^2*((j : ℝ)+1)))
    (hij : (m : ℤ) < |i-j|) :
    2*w^2/ν ≤ |x-x'| := by
  have hm' : 2*w^2/ν ≤ w^2*(m : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hm (sq_nonneg w)
    convert h using 1
    ring
  rcases le_total i j with h | h
  · have hji : (m : ℤ)+1 ≤ j-i := by
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
      omega
    have hji' : (m : ℝ)+1 ≤ (j : ℝ)-(i : ℝ) := by exact_mod_cast hji
    have hp := mul_le_mul_of_nonneg_left hji' (sq_nonneg w)
    have hd : w^2*(m : ℝ) ≤ x'-x := by nlinarith [hx.2,hx'.1]
    exact (hm'.trans hd).trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hij' : (m : ℤ)+1 ≤ i-j := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
      omega
    have hij'' : (m : ℝ)+1 ≤ (i : ℝ)-(j : ℝ) := by exact_mod_cast hij'
    have hp := mul_le_mul_of_nonneg_left hij'' (sq_nonneg w)
    have hd : w^2*(m : ℝ) ≤ x-x' := by nlinarith [hx.1,hx'.2]
    exact (hm'.trans hd).trans (le_abs_self _)

private theorem parabola_block_gap {i j : ℤ} {m : ℕ} {x x' d w ν : ℝ}
    (hm : 2/ν ≤ (m : ℝ))
    (hx : x ∈ Ico (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (hx' : x' ∈ Ico (d+w^2*(j : ℝ)) (d+w^2*((j : ℝ)+1)))
    (hij : (m : ℤ) < |i-j|) :
    2*w^2/ν ≤ |x-x'| :=
  parabola_block_gap_closed hm (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hx') hij

theorem parabolaBilinearMoment_localization {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {w d u ν a b : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hwidth : b ≤ w^2)
    (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : ∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc d (d+u))
    (hy : ∀ k ∈ V, y k ∈ Icc 0 w)
    (hblock : ∀ i ∈ J, ∀ k ∈ S i,
      x i k ∈ Ico (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (r t : ℝ) :
    parabolaBilinearMoment (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y a b r t ≤
      (7/ν)*∑ i ∈ J, parabolaBilinearMoment (S i) V (z i) c (x i) y a b r t := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν ≤ (m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ) < 2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1 ≤ 7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1 < 2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let F := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    (x i ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2
  have hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ α : ℝ, ∫ γ : ℝ,
        planarCross (F i) (F j) (Z i) (Z j) (X i) (Y i) (X j) (Y j)
          a b r t α γ) = 0 := by
    intro i hi j hj hij
    rw [integral_planarCross _ _ _ _ _ _ _ _ ha hb]
    apply Finset.sum_eq_zero
    intro ij hij'
    have hleft := Finset.mem_product.mp (Finset.mem_product.mp hij').1
    have hright := Finset.mem_product.mp (Finset.mem_product.mp hij').2
    have hl := Finset.mem_product.mp hleft.1
    have hr := Finset.mem_product.mp hright.1
    have hgap := parabola_block_gap hm
      (hblock i hi _ hl.1) (hblock j hj _ hr.1) hij
    have he := integral_parabola_sixth_kernel_eq_zero hw hν ha hb hwidth hu hd
      (hx i hi _ hl.1) (hx j hj _ hr.1) (hy _ hl.2) (hy _ hleft.2)
      (hy _ hr.2) (hy _ hright.2) hgap r t
    dsimp [X,Y]
    rw [he,mul_zero]
  have hmain := planarFamily_banded_bound J F Z X Y ha hb r t m hz
  rw [parabolaMoment_family_flat]
  have hsum : (∑ i ∈ J, ∫ α : ℝ, ∫ γ : ℝ,
      sargosWeightedPlanarIntegrand (F i) (Z i) (X i) (Y i) a b r t α γ) =
      ∑ i ∈ J, parabolaBilinearMoment (S i) V (z i) c (x i) y a b r t := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (parabolaMoment_flat _ _ _ _ _ _ _ _ _ _).symm
  rw [hsum] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  unfold parabolaBilinearMoment
  apply integral_nonneg
  intro α
  apply integral_nonneg
  intro γ
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (sargosSincKernel_nonneg ha.le _) (sargosSincKernel_nonneg hb.le _))
    (sq_nonneg _)) (by positivity)


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory FourierTransform SchwartzMap Set GafniTao
open scoped ComplexConjugate Convolution ContDiff
namespace TaoTrudgianYang2025

private def cutoffConjReflect (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv g)

private theorem cutoffConjReflect_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutoffConjReflect g x = conj (g (-x)) := rfl

private theorem fourier_cutoffConjReflect (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (cutoffConjReflect g) x = conj (𝓕 g x) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_conj]
  rw [← integral_neg_eq_self (fun y : ℝ =>
    Complex.exp (↑(-2 * Real.pi * y * x) * Complex.I) •
      cutoffConjReflect g y) volume]
  apply integral_congr_ae
  filter_upwards with y
  simp only [cutoffConjReflect_apply, neg_neg, smul_eq_mul, map_mul,
    ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

private theorem fourier_fourier_cutoff (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (𝓕 g) x = g (-x) := by
  have h := congrFun (g.continuous.fourierInv_fourier_eq
    g.integrable (𝓕 g).integrable) (-x)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
  exact h

private def cutoffSquare (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (𝓕 g) (𝓕 (cutoffConjReflect g))

private theorem cutoffSquare_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    cutoffSquare g x = (‖𝓕 g x‖^2 : ℝ) := by
  simp only [cutoffSquare, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', fourier_cutoffConjReflect,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem fourier_cutoffSquare (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    𝓕 (cutoffSquare g) x =
      (g ⋆[ContinuousLinearMap.mul ℂ ℂ] cutoffConjReflect g) (-x) := by
  have h : cutoffSquare g =
      𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        g (cutoffConjReflect g)) :=
    (SchwartzMap.fourier_convolution _ _ _).symm
  rw [h, fourier_fourier_cutoff, SchwartzMap.convolution_apply]

private theorem fourier_cutoffSquare_eq_zero
    (g : 𝓢(ℝ, ℂ)) {R x : ℝ}
    (hs : ∀ y, R < |y| → g y = 0) (hx : 2*R < |x|) :
    𝓕 (cutoffSquare g) x = 0 := by
  rw [fourier_cutoffSquare]
  apply Function.notMem_support.mp
  intro h
  obtain ⟨u,hu,v,hv,huv⟩ :=
    support_convolution_subset (ContinuousLinearMap.mul ℂ ℂ) h
  have hu' : |u| ≤ R := le_of_not_gt (fun hn => hu (hs u hn))
  have hv' : |v| ≤ R := by
    apply le_of_not_gt
    intro hn
    apply hv
    rw [cutoffConjReflect_apply, hs (-v) (by simpa only [abs_neg] using hn), map_zero]
  have hsum := abs_add_le u v
  change u+v = -x at huv
  rw [huv, abs_neg] at hsum
  linarith

private def parabolaFrequencyBumpReal : ℝ → ℝ :=
  modelPhaseBufferedCutoff (-1) 1 (1/4)

private theorem parabolaFrequencyBumpReal_smooth :
    ContDiff ℝ ∞ parabolaFrequencyBumpReal :=
  modelPhaseBufferedCutoff_contDiff _ _ _

private theorem parabolaFrequencyBumpReal_compact :
    HasCompactSupport parabolaFrequencyBumpReal :=
  modelPhaseBufferedCutoff_hasCompactSupport (by norm_num)

private def parabolaFrequencyBump : 𝓢(ℝ, ℂ) :=
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (parabolaFrequencyBumpReal_compact.toSchwartzMap
      parabolaFrequencyBumpReal_smooth)

private theorem parabolaFrequencyBump_apply (x : ℝ) :
    parabolaFrequencyBump x = (parabolaFrequencyBumpReal x : ℂ) := rfl

private theorem parabolaFrequencyBump_zero {x : ℝ} (hx : 1 < |x|) :
    parabolaFrequencyBump x = 0 := by
  rw [parabolaFrequencyBump_apply]
  apply Complex.ofReal_eq_zero.mpr
  rcases lt_abs.mp hx with h | h
  · exact modelPhaseBufferedCutoff_zero_right (by norm_num) (by linarith)
  · exact modelPhaseBufferedCutoff_zero_left (by norm_num) (by linarith)

private theorem parabolaFrequencyBump_fourier_zero_pos :
    0 < (𝓕 parabolaFrequencyBump 0).re := by
  have hi : Integrable parabolaFrequencyBumpReal :=
    parabolaFrequencyBumpReal_smooth.continuous.integrable_of_hasCompactSupport
      parabolaFrequencyBumpReal_compact
  have hz : parabolaFrequencyBumpReal 0 = 1 :=
    modelPhaseBufferedCutoff_one (by norm_num) (by norm_num) (by norm_num)
  have hp := integral_pos_of_integrable_nonneg_nonzero
    parabolaFrequencyBumpReal_smooth.continuous hi
    (fun x => modelPhaseBufferedCutoff_nonneg _ _ _ x)
    (show parabolaFrequencyBumpReal 0 ≠ 0 by rw [hz]; norm_num)
  have he : (𝓕 parabolaFrequencyBump 0).re = ∫ x, parabolaFrequencyBumpReal x := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_smul, parabolaFrequencyBump_apply]
    exact (integral_re (show Integrable (fun x => (parabolaFrequencyBumpReal x : ℂ))
      from parabolaFrequencyBump.integrable)).symm
  rwa [he]

private def cutoffRescale (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) :
    𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
      (Units.mk0 a ha)) f

private theorem cutoffRescale_apply
    (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    cutoffRescale f a ha x = f (a*x) := rfl

private theorem fourier_cutoffRescale
    (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    𝓕 (cutoffRescale f a ha) ξ = |a⁻¹| • 𝓕 f (ξ/a) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ x : ℝ, (fun y : ℝ =>
      Complex.exp (↑(-2*Real.pi*y*(ξ/a))*Complex.I) • f y) (a*x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [cutoffRescale_apply]
      congr 3
      field_simp
    _ = _ := by
      simpa using Measure.integral_comp_mul_left
        (fun y : ℝ => Complex.exp (↑(-2*Real.pi*y*(ξ/a))*Complex.I) • f y) a

private theorem cutoff_polynomial_decay (f : 𝓢(ℝ, ℂ)) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, (1+|x|)^n*‖f x‖ ≤ C := by
  let B : ℝ := 2^n * (Finset.Iic (n,0)).sup
    (fun p => SchwartzMap.seminorm ℝ p.1 p.2) f
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (n,0)) (k := n) (n := 0) le_rfl le_rfl f x
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

theorem exists_parabola_rapid_cutoff :
    ∃ η : 𝓢(ℝ, ℂ),
      (∀ x : ℝ, 0 ≤ (η x).re ∧ (η x).im = 0) ∧
      (∀ x : ℝ, |x| ≤ 1 → 1 ≤ (η x).re) ∧
      (∀ ξ : ℝ, 1/100 ≤ |ξ| → 𝓕 η ξ = 0) ∧
      (∀ n : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, (1+|x|)^n*‖η x‖ ≤ C) := by
  let f := cutoffSquare parabolaFrequencyBump
  have hf (x : ℝ) : f x = (‖𝓕 parabolaFrequencyBump x‖^2 : ℝ) :=
    cutoffSquare_apply _ _
  have hfn (x : ℝ) : 0 ≤ (f x).re := by rw [hf]; exact sq_nonneg _
  have hfi (x : ℝ) : (f x).im = 0 := by rw [hf]; rfl
  have hf₀ : 0 < (f 0).re := by
    rw [hf,Complex.ofReal_re]
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hz
    have h := parabolaFrequencyBump_fourier_zero_pos
    rw [hz] at h
    simp at h
  let m : ℝ := (f 0).re/2
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : {x : ℝ | m < (f x).re} ∈ nhds 0 :=
    ((Complex.continuous_re.comp f.continuous).continuousAt).preimage_mem_nhds
      (Ioi_mem_nhds (by dsimp [m]; linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hn
  let a : ℝ := min (δ/2) (1/400)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  let η : 𝓢(ℝ, ℂ) := (m⁻¹ : ℂ) • cutoffRescale f a ha.ne'
  have he (x : ℝ) : η x = (m⁻¹ : ℂ)*f (a*x) := rfl
  have her (x : ℝ) : (η x).re = m⁻¹*(f (a*x)).re := by
    rw [he,Complex.mul_re]
    simp
  have hei (x : ℝ) : (η x).im = 0 := by
    rw [he,Complex.mul_im,hfi]
    simp
  refine ⟨η,fun x => ⟨?_,hei x⟩,?_,?_,cutoff_polynomial_decay η⟩
  · rw [her]
    exact mul_nonneg (inv_nonneg.mpr hm.le) (hfn _)
  · intro x hx
    have hxδ : a*|x| < δ := by
      have hax := mul_le_mul_of_nonneg_left hx ha.le
      have haδ : a ≤ δ/2 := min_le_left _ _
      nlinarith
    have hmx := hball (show a*x ∈ Metric.ball 0 δ by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_mul,abs_of_pos ha]
        using hxδ)
    rw [her]
    apply (le_inv_mul_iff₀ hm).mpr
    simpa only [mul_one] using le_of_lt hmx
  · intro ξ hξ
    change 𝓕 ((m⁻¹ : ℂ) • cutoffRescale f a ha.ne') ξ = 0
    rw [fourier_smul]
    change (m⁻¹ : ℂ) • 𝓕 (cutoffRescale f a ha.ne') ξ = 0
    rw [fourier_cutoffRescale,
      fourier_cutoffSquare_eq_zero parabolaFrequencyBump
        (fun y hy => parabolaFrequencyBump_zero hy)]
    · simp
    · rw [abs_div,abs_of_pos ha]
      apply (lt_div_iff₀ ha).mpr
      have hab : a ≤ 1/400 := min_le_right _ _
      linarith

def parabolaRapidProfile : 𝓢(ℝ, ℂ) :=
  Classical.choose exists_parabola_rapid_cutoff

private theorem parabolaRapidProfile_nonneg (x : ℝ) :
    0 ≤ (parabolaRapidProfile x).re :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).1 x |>.1

private theorem parabolaRapidProfile_real (x : ℝ) :
    (parabolaRapidProfile x).im = 0 :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).1 x |>.2

private theorem parabolaRapidProfile_one_le (x : ℝ) (hx : |x| ≤ 1) :
    1 ≤ (parabolaRapidProfile x).re :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).2.1 x hx

private theorem parabolaRapidProfile_fourier_zero (ξ : ℝ) (hξ : 1/100 ≤ |ξ|) :
    𝓕 parabolaRapidProfile ξ = 0 :=
  (Classical.choose_spec exists_parabola_rapid_cutoff).2.2.1 ξ hξ

private theorem parabolaRapidProfile_coe_re (x : ℝ) :
    ((parabolaRapidProfile x).re : ℂ) = parabolaRapidProfile x := by
  apply Complex.ext
  · rfl
  · simpa using (parabolaRapidProfile_real x).symm

def parabolaRapidKernel (R c x : ℝ) : ℝ :=
  (parabolaRapidProfile ((x-c)/R)).re

theorem parabolaRapidKernel_nonneg (R c x : ℝ) :
    0 ≤ parabolaRapidKernel R c x := parabolaRapidProfile_nonneg _

theorem parabolaRapidKernel_one_le {R c x : ℝ}
    (hR : 0 < R) (hx : |x-c| ≤ R) :
    1 ≤ parabolaRapidKernel R c x := by
  apply parabolaRapidProfile_one_le
  rw [abs_div,abs_of_pos hR]
  exact (div_le_one hR).mpr hx

theorem integrable_parabolaRapidKernel {R : ℝ} (hR : 0 < R) (c : ℝ) :
    Integrable (parabolaRapidKernel R c) := by
  have h₀ : Integrable (cutoffRescale parabolaRapidProfile R⁻¹
    (inv_ne_zero hR.ne')) := (cutoffRescale parabolaRapidProfile R⁻¹
      (inv_ne_zero hR.ne')).integrable
  have h := h₀.re.comp_add_right (-c)
  convert h using 1
  ext x
  simp only [parabolaRapidKernel,cutoffRescale_apply,sub_eq_add_neg,div_eq_mul_inv,mul_comm]
  rfl

theorem parabolaRapidKernel_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R c x : ℝ,
      (1+|(x-c)/R|)^n*parabolaRapidKernel R c x ≤ C := by
  obtain ⟨C,hC,h⟩ := cutoff_polynomial_decay parabolaRapidProfile n
  refine ⟨C,hC,fun R c x => ?_⟩
  have he : ‖parabolaRapidProfile ((x-c)/R)‖ = parabolaRapidKernel R c x := by
    rw [← parabolaRapidProfile_coe_re,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (parabolaRapidProfile_nonneg _)]
    rfl
  simpa only [he] using h ((x-c)/R)

private theorem integral_parabolaRapidKernel_character_zero_origin
    {R ξ : ℝ} (hR : 0 < R) (hξ : 1/(100*R) ≤ |ξ|) :
    (∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) = 0 := by
  have he : (∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) =
      𝓕 (cutoffRescale parabolaRapidProfile R⁻¹ (inv_ne_zero hR.ne')) (-ξ) := by
    rw [SchwartzMap.fourier_coe,Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [parabolaRapidKernel,sub_zero,parabolaRapidProfile_coe_re,
      cutoffRescale_apply,fordAdditiveCharacter,smul_eq_mul]
    rw [show R⁻¹*x = x/R by ring]
    rw [mul_comm (parabolaRapidProfile (x/R))]
    congr 2
    push_cast
    ring
  rw [he,fourier_cutoffRescale,parabolaRapidProfile_fourier_zero]
  · simp
  · rw [div_inv_eq_mul,abs_mul,abs_neg,abs_of_pos hR]
    have h := (div_le_iff₀ (by positivity : 0 < 100*R)).mp hξ
    nlinarith

theorem integral_parabolaRapidKernel_character_zero
    {R ξ : ℝ} (hR : 0 < R) (hξ : 1/(100*R) ≤ |ξ|) (c : ℝ) :
    (∫ x : ℝ, (parabolaRapidKernel R c x : ℂ)*fordAdditiveCharacter (ξ*x)) = 0 := by
  let f : ℝ → ℂ := fun x =>
    (parabolaRapidKernel R c x : ℂ)*fordAdditiveCharacter (ξ*x)
  have ht := integral_add_right_eq_self (μ := volume) f c
  calc
    _ = ∫ x : ℝ, f (x+c) := ht.symm
    _ = ∫ x : ℝ, fordAdditiveCharacter (ξ*c)*
      ((parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [f,parabolaRapidKernel]
      rw [add_sub_cancel_right,sub_zero,
        show ξ*(x+c) = ξ*c+ξ*x by ring,fordAdditiveCharacter_add]
      ring
    _ = fordAdditiveCharacter (ξ*c)*
      ∫ x : ℝ, (parabolaRapidKernel R 0 x : ℂ)*fordAdditiveCharacter (ξ*x) :=
        integral_const_mul _ _
    _ = 0 := by rw [integral_parabolaRapidKernel_character_zero_origin hR hξ,mul_zero]

def parabolaRapidWeight (R r t α γ : ℝ) : ℝ :=
  parabolaRapidKernel R r α * parabolaRapidKernel R t γ

theorem parabolaRapidWeight_nonneg (R r t α γ : ℝ) :
    0 ≤ parabolaRapidWeight R r t α γ :=
  mul_nonneg (parabolaRapidKernel_nonneg _ _ _) (parabolaRapidKernel_nonneg _ _ _)

theorem parabolaRapidWeight_one_le {R r t α γ : ℝ}
    (hR : 0 < R) (hα : |α-r| ≤ R) (hγ : |γ-t| ≤ R) :
    1 ≤ parabolaRapidWeight R r t α γ := by
  exact one_le_mul_of_one_le_of_one_le
    (parabolaRapidKernel_one_le hR hα) (parabolaRapidKernel_one_le hR hγ)

theorem parabolaRapidWeight_decay (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R r t α γ : ℝ,
      (1+|(α-r)/R|+|(γ-t)/R|)^n*parabolaRapidWeight R r t α γ ≤ C := by
  obtain ⟨C,hC,h⟩ := parabolaRapidKernel_decay n
  refine ⟨C^2,sq_pos_of_pos hC,fun R r t α γ => ?_⟩
  have hp : 1+|(α-r)/R|+|(γ-t)/R| ≤
      (1+|(α-r)/R|)*(1+|(γ-t)/R|) := by
    nlinarith [mul_nonneg (abs_nonneg ((α-r)/R)) (abs_nonneg ((γ-t)/R))]
  have hpn := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|(α-r)/R|+|(γ-t)/R|) hp n
  have hprod := mul_le_mul (h R r α) (h R t γ)
    (mul_nonneg (by positivity) (parabolaRapidKernel_nonneg _ _ _)) hC.le
  have hm := mul_le_mul_of_nonneg_right hpn (parabolaRapidWeight_nonneg R r t α γ)
  rw [mul_pow] at hm
  unfold parabolaRapidWeight at hm ⊢
  nlinarith only [hm,hprod]

theorem integral_parabolaRapidWeight_character_zero
    {R u v : ℝ} (hR : 0 < R)
    (hgap : 1/(100*R) ≤ |u| ∨ 1/(100*R) ≤ |v|) (r t : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, (parabolaRapidWeight R r t α γ : ℂ)*
      fordAdditiveCharacter (u*α+v*γ)) = 0 := by
  have he (α γ : ℝ) :
      (parabolaRapidWeight R r t α γ : ℂ)*fordAdditiveCharacter (u*α+v*γ) =
      ((parabolaRapidKernel R r α : ℂ)*fordAdditiveCharacter (u*α))*
      ((parabolaRapidKernel R t γ : ℂ)*fordAdditiveCharacter (v*γ)) := by
    rw [fordAdditiveCharacter_add]
    unfold parabolaRapidWeight
    push_cast
    ring
  simp_rw [he,integral_const_mul]
  rw [integral_mul_const]
  rcases hgap with h | h
  · rw [integral_parabolaRapidKernel_character_zero hR h,zero_mul]
  · rw [integral_parabolaRapidKernel_character_zero hR h,mul_zero]

theorem integral_parabolaRapidWeight_sixth_zero
    {x x' y₁ y₂ y₃ y₄ w d u ν R : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (hR : 0 < R)
    (hwidth : 1/(100*R) ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : x ∈ Icc d (d+u)) (hx' : x' ∈ Icc d (d+u))
    (h₁ : y₁ ∈ Icc 0 w) (h₂ : y₂ ∈ Icc 0 w)
    (h₃ : y₃ ∈ Icc 0 w) (h₄ : y₄ ∈ Icc 0 w)
    (hgap : 2*w^2/ν ≤ |x-x'|) (r t : ℝ) :
    (∫ α : ℝ, ∫ γ : ℝ, (parabolaRapidWeight R r t α γ : ℂ)*
      fordAdditiveCharacter ((x+y₁+y₂-(x'+y₃+y₄))*α+
        (x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2))*γ)) = 0 := by
  apply integral_parabolaRapidWeight_character_zero hR (Or.inr ?_)
  apply le_of_lt
  apply parabola_sixth_frequency_gap hw.le (by positivity : 0 < 4*ν)
    h₁ h₂ h₃ h₄ (parabola_same_interval_separation hν.le hu hd hx hx')
  have hg := (div_le_iff₀ hν).mp hgap
  apply (div_lt_iff₀ (by positivity : 0 < 4*ν)).mpr
  nlinarith [sq_pos_of_pos hw]

private theorem continuous_rapidWeight (R r t : ℝ) :
    Continuous (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) := by
  unfold parabolaRapidWeight parabolaRapidKernel
  exact (Complex.continuous_re.comp
    (parabolaRapidProfile.continuous.comp (by fun_prop))).mul
    (Complex.continuous_re.comp
      (parabolaRapidProfile.continuous.comp (by fun_prop)))

private theorem rapid_weighted_integrable {f : ℝ × ℝ → ℂ}
    (hf : Continuous f) {M R : ℝ} (hR : 0 < R)
    (hM : ∀ p, ‖f p‖ ≤ M) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (parabolaRapidWeight R r t p.1 p.2 : ℂ)*f p) := by
  have hw : Integrable (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have hc := (Complex.continuous_ofReal.comp (continuous_rapidWeight R r t)).mul hf
  apply (hw.mul_const M).mono' hc.aestronglyMeasurable
  filter_upwards with p
  change ‖(parabolaRapidWeight R r t p.1 p.2 : ℂ)*f p‖ ≤ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (parabolaRapidWeight_nonneg R r t p.1 p.2)]
  exact mul_le_mul_of_nonneg_left (hM p) (parabolaRapidWeight_nonneg R r t p.1 p.2)

private theorem weighted_family_banded (J : Finset ℤ)
    (F : ℤ → (ℝ × ℝ) → ℂ) (W : (ℝ × ℝ) → ℝ) (m : ℕ)
    (hW : ∀ p, 0 ≤ W p)
    (hi : ∀ i ∈ J, ∀ j ∈ J, Integrable (fun p => (W p : ℂ)*F i p*conj (F j p)))
    (hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ p, (W p : ℂ)*F i p*conj (F j p)) = 0) :
    (∫ p, W p*‖∑ i ∈ J, F i p‖^2) ≤
      (2*(m : ℝ)+1)*∑ i ∈ J, ∫ p, W p*‖F i p‖^2 := by
  classical
  have hself (i : ℤ) (p : ℝ × ℝ) :
      (W p : ℂ)*F i p*conj (F i p) = (W p*‖F i p‖^2 : ℝ) := by
    rw [mul_assoc,Complex.mul_conj']
    push_cast
    ring
  have hdiag (i : ℤ) (hiJ : i ∈ J) : Integrable (fun p => W p*‖F i p‖^2) := by
    have h := (hi i hiJ i hiJ).re
    simpa only [hself,RCLike.ofReal_re] using h
  have hexpand (p : ℝ × ℝ) :
      (W p*‖∑ i ∈ J, F i p‖^2 : ℝ) =
        ∑ i ∈ J, ∑ j ∈ J, (W p : ℂ)*F i p*conj (F j p) := by
    rw [Complex.ofReal_mul,Complex.ofReal_pow,← Complex.mul_conj']
    rw [map_sum,Finset.sum_mul_sum]
    simp only [Finset.mul_sum,mul_assoc]
  have he : ((∫ p, W p*‖∑ i ∈ J, F i p‖^2 : ℝ) : ℂ) =
      ∑ i ∈ J, ∑ j ∈ J, ∫ p, (W p : ℂ)*F i p*conj (F j p) := by
    rw [← integral_complex_ofReal]
    simp_rw [hexpand]
    rw [integral_finsetSum J (fun i hiJ =>
      integrable_finsetSum J (fun j hj => hi i hiJ j hj))]
    apply Finset.sum_congr rfl
    intro i hiJ
    exact integral_finsetSum J (hi i hiJ)
  have hre := congrArg Complex.re he
  simp only [Complex.ofReal_re,Complex.re_sum] at hre
  rw [hre]
  apply banded_real_sum_le
  · intro i hiJ
    exact integral_nonneg (fun p => mul_nonneg (hW p) (sq_nonneg _))
  · intro i hiJ j hj
    have hpoint (p : ℝ × ℝ) :
        2*((W p : ℂ)*F i p*conj (F j p)).re ≤
          W p*‖F i p‖^2+W p*‖F j p‖^2 := by
      have hn : (F i p*conj (F j p)).re ≤ ‖F i p‖*‖F j p‖ := by
        simpa only [norm_mul,Complex.norm_conj] using
          Complex.re_le_norm (F i p*conj (F j p))
      have hc : 2*(F i p*conj (F j p)).re ≤ ‖F i p‖^2+‖F j p‖^2 := by
        nlinarith [sq_nonneg (‖F i p‖-‖F j p‖)]
      have hm := mul_le_mul_of_nonneg_left hc (hW p)
      rw [mul_assoc,Complex.re_ofReal_mul]
      nlinarith only [hm]
    have hre' : (∫ p, (W p : ℂ)*F i p*conj (F j p)).re =
        ∫ p, ((W p : ℂ)*F i p*conj (F j p)).re :=
      (integral_re (hi i hiJ j hj)).symm
    rw [hre',← integral_const_mul,← integral_add (hdiag i hiJ) (hdiag j hj)]
    exact integral_mono ((hi i hiJ j hj).re.const_mul 2)
      ((hdiag i hiJ).add (hdiag j hj)) hpoint
  · intro i hiJ j hj hij
    rw [hz i hiJ j hj hij]
    rfl

private theorem rapidCross_integrable {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hn (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)‖ ≤
        (∑ i ∈ S, ‖z i‖)*(∑ j ∈ T, ‖z' j‖) := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (norm_sargosPlanarSum_le_sum_norm S z u v p.1 p.2)
      (norm_sargosPlanarSum_le_sum_norm T z' u' v' p.1 p.2)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  simpa only [mul_assoc] using rapid_weighted_integrable hf hR hn r t

private theorem rapidCharacter_integrable {R : ℝ} (hR : 0 < R) (r t u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2)) :=
  rapid_weighted_integrable (by unfold fordAdditiveCharacter; fun_prop) hR
    (fun p => (sargos_character_norm _).le) r t

private theorem rapidCross_expand {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) (W α γ : ℝ) :
    (W : ℂ)*sargosPlanarSum S z u v α γ*
      conj (sargosPlanarSum T z' u' v' α γ) =
      ∑ ij ∈ S ×ˢ T, (z ij.1*conj (z' ij.2))*
        ((W : ℂ)*fordAdditiveCharacter
          ((u ij.1-u' ij.2)*α+(v ij.1-v' ij.2)*γ)) := by
  unfold sargosPlanarSum
  rw [map_sum,mul_assoc,Finset.sum_mul_sum,Finset.sum_product]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,conj_fordAdditiveCharacter]
  calc
    _ = (z i*conj (z' j))*((W : ℂ)*
      (fordAdditiveCharacter (u i*α+v i*γ)*fordAdditiveCharacter (-(u' j*α+v' j*γ)))) := by ring
    _ = _ := by
      rw [← fordAdditiveCharacter_add]
      congr 3
      ring

private theorem integral_rapidCross_zero {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {R : ℝ} (hR : 0 < R)
    (hgap : ∀ i ∈ S, ∀ j ∈ T, 1/(100*R) ≤ |u i-u' j| ∨
      1/(100*R) ≤ |v i-v' j|) (r t : ℝ) :
    (∫ p : ℝ × ℝ, (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) = 0 := by
  simp_rw [rapidCross_expand]
  rw [integral_finsetSum (S ×ˢ T) (fun ij _ =>
    (rapidCharacter_integrable hR r t (u ij.1-u' ij.2) (v ij.1-v' ij.2)).const_mul _)]
  apply Finset.sum_eq_zero
  intro ij hij
  have hprod := integral_prod
    (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter ((u ij.1-u' ij.2)*p.1+(v ij.1-v' ij.2)*p.2))
    (rapidCharacter_integrable hR r t (u ij.1-u' ij.2) (v ij.1-v' ij.2))
  have he := hprod.trans (integral_parabolaRapidWeight_character_zero hR
    (hgap ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2) r t)
  rw [integral_const_mul]
  exact congrArg (fun a : ℂ => (z ij.1*conj (z' ij.2))*a) he |>.trans (mul_zero _)

def parabolaRapidBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, parabolaRapidWeight R r t p.1 p.2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

theorem parabolaRapidBilinearMoment_localization {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {w d u ν R : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hR : 0 < R)
    (hwidth : 1/(100*R) ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |d|)
    (hx : ∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc d (d+u))
    (hy : ∀ k ∈ V, y k ∈ Icc 0 w)
    (hblock : ∀ i ∈ J, ∀ k ∈ S i,
      x i k ∈ Ico (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1)))
    (r t : ℝ) :
    parabolaRapidBilinearMoment (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y R r t ≤
      (7/ν)*∑ i ∈ J, parabolaRapidBilinearMoment (S i) V (z i) c (x i) y R r t := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν ≤ (m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ) < 2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1 ≤ 7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1 < 2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let A := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    (x i ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2
  let F := fun i : ℤ => fun p : ℝ × ℝ => sargosPlanarSum (A i) (Z i) (X i) (Y i) p.1 p.2
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ p, (W p : ℂ)*F i p*conj (F j p)) = 0 := by
    intro i hi j hj hij
    apply integral_rapidCross_zero _ _ _ _ _ _ _ _ hR _ r t
    intro a ha b hb
    have hal := Finset.mem_product.mp (Finset.mem_product.mp ha).1
    have har := (Finset.mem_product.mp ha).2
    have hbl := Finset.mem_product.mp (Finset.mem_product.mp hb).1
    have hbr := (Finset.mem_product.mp hb).2
    right
    apply le_of_lt
    apply parabola_sixth_frequency_gap hw.le (by positivity : 0 < 4*ν)
      (hy _ hal.2) (hy _ har) (hy _ hbl.2) (hy _ hbr)
      (parabola_same_interval_separation hν.le hu hd (hx i hi _ hal.1) (hx j hj _ hbl.1))
    have hg := (div_le_iff₀ hν).mp
      (parabola_block_gap hm (hblock i hi _ hal.1) (hblock j hj _ hbl.1) hij)
    apply (div_lt_iff₀ (by positivity : 0 < 4*ν)).mpr
    nlinarith [sq_pos_of_pos hw]
  have hmain := weighted_family_banded J F W m
    (fun p => parabolaRapidWeight_nonneg _ _ _ _ _)
    (fun i _ j _ => rapidCross_integrable (A i) (A j) (Z i) (Z j)
      (X i) (Y i) (X j) (Y j) hR r t) hz
  have hsingle (i : ℤ) :
      (∫ p, W p*‖F i p‖^2) =
        parabolaRapidBilinearMoment (S i) V (z i) c (x i) y R r t := by
    unfold parabolaRapidBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp [W,F,A,Z,X,Y]
    rw [parabola_product_sum,norm_mul,norm_pow]
    ring
  have htotal :
      (∫ p, W p*‖∑ i ∈ J, F i p‖^2) =
        parabolaRapidBilinearMoment (J.sigma S) V
          (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y R r t := by
    unfold parabolaRapidBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    have hs : (∑ i ∈ J, F i p) =
      sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
        (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
        (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
        (fun ij => (x ij.1 ij.2.1.1)^2+(y ij.2.1.2)^2+(y ij.2.2)^2) p.1 p.2 := by
      simp only [F,A,Z,X,Y,sargosPlanarSum,Finset.sum_sigma]
    rw [hs,parabola_family_product_sum,norm_mul,norm_pow]
    dsimp [W]
    ring
  simp_rw [hsingle] at hmain
  rw [htotal] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  rw [← hsingle]
  exact integral_nonneg (fun p => mul_nonneg (parabolaRapidWeight_nonneg _ _ _ _ _) (sq_nonneg _))

def parabolaSourceWeight (R r t α γ : ℝ) : ℝ :=
  1/(1+‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖)^100

theorem parabolaSourceWeight_nonneg (R r t α γ : ℝ) :
    0 ≤ parabolaSourceWeight R r t α γ := by
  unfold parabolaSourceWeight
  positivity

private theorem continuous_sourceWeight (R r t : ℝ) :
    Continuous (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) := by
  unfold parabolaSourceWeight
  exact continuous_const.div (by fun_prop) (fun p => by positivity)

theorem integrable_parabolaSourceWeight {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    Integrable (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) := by
  have hb := integrable_one_add_norm (E := ℝ × ℝ) (μ := volume) (r := 100)
    (by norm_num)
  have hi := (hb.comp_smul (inv_ne_zero hR.ne')).comp_add_right (-(r,t))
  apply hi.mono' (continuous_sourceWeight R r t).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)]
  have hnorm : ‖R⁻¹ • (p + -(r,t))‖ ≤
      ‖(((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I‖ := by
    rw [Prod.norm_def]
    apply max_le
    · have h := Complex.abs_re_le_norm
        ((((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I)
      simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] at h
      change |R⁻¹*(p.1 + -r)| ≤ _
      simpa only [sub_eq_add_neg,div_eq_mul_inv,mul_comm] using h
    · have h := Complex.abs_im_le_norm
        ((((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I)
      simp only [Complex.add_im,Complex.ofReal_re,Complex.mul_im,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero] at h
      change |R⁻¹*(p.2 + -t)| ≤ _
      simpa only [sub_eq_add_neg,div_eq_mul_inv,mul_comm] using h
  rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]
  change 1/(1+‖(((p.1-r)/R : ℝ) : ℂ)+((p.2-t)/R : ℝ)*Complex.I‖)^100 ≤ _
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

theorem parabolaRapidWeight_le_sourceWeight :
    ∃ C : ℝ, 0 < C ∧ ∀ R r t α γ : ℝ,
      parabolaRapidWeight R r t α γ ≤ C*parabolaSourceWeight R r t α γ := by
  obtain ⟨C,hC,h⟩ := parabolaRapidWeight_decay 100
  refine ⟨C,hC,fun R r t α γ => ?_⟩
  have hn : ‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖ ≤
      |(α-r)/R|+|(γ-t)/R| := by
    simpa using Complex.norm_le_abs_re_add_abs_im
      ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I)
  have hp : (1+‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖)^100 ≤
      (1+|(α-r)/R|+|(γ-t)/R|)^100 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hm := mul_le_mul_of_nonneg_right hp (parabolaRapidWeight_nonneg R r t α γ)
  unfold parabolaSourceWeight
  rw [mul_one_div,le_div_iff₀ (by positivity)]
  rw [mul_comm]
  exact hm.trans (h R r t α γ)

private def parabolaMomentFunction {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
  ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabolaMomentFunction_nonneg {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (p : ℝ × ℝ) :
    0 ≤ parabolaMomentFunction S V z c x y p := by
  unfold parabolaMomentFunction
  positivity

private theorem parabolaMomentFunction_continuous {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    Continuous (parabolaMomentFunction S V z c x y) := by
  unfold parabolaMomentFunction sargosPlanarSum fordAdditiveCharacter
  fun_prop

private theorem parabolaMomentFunction_integrable {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W p*parabolaMomentFunction S V z c x y p) := by
  apply hW.mul_bdd (parabolaMomentFunction_continuous S V z c x y).aestronglyMeasurable
    (c := (∑ i ∈ S, ‖z i‖)^2*(∑ j ∈ V, ‖c j‖)^4)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)]
  unfold parabolaMomentFunction
  have hS := norm_sargosPlanarSum_le_sum_norm S z x (fun i => (x i)^2) p.1 p.2
  have hV := norm_sargosPlanarSum_le_sum_norm V c y (fun j => (y j)^2) p.1 p.2
  gcongr

def parabolaSourceBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, parabolaSourceWeight R r t p.1 p.2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

def parabolaBoxBilinearMoment {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabolaBox_le_rapid {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    parabolaBoxBilinearMoment S V z c x y R r t ≤
      parabolaRapidBilinearMoment S V z c x y R r t := by
  let F := parabolaMomentFunction S V z c x y
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  have hiF : IntegrableOn F B := ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
    (parabolaMomentFunction_continuous S V z c x y).continuousOn
  have hiW : Integrable W :=
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t)
  have hi := parabolaMomentFunction_integrable S V z c x y hiW
  have hpoint (p : ℝ × ℝ) (hp : p ∈ B) : F p ≤ W p*F p := by
    have hα : |p.1-r| ≤ R := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
    have hγ : |p.2-t| ≤ R := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    have hW := parabolaRapidWeight_one_le hR hα hγ
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hW
      (parabolaMomentFunction_nonneg S V z c x y p)
  have hlocal := setIntegral_mono_on hiF hi.integrableOn
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  have hwhole := setIntegral_le_integral (s := B) hi
    (Filter.Eventually.of_forall (fun p =>
      mul_nonneg (parabolaRapidWeight_nonneg _ _ _ _ _)
        (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)))
  simpa only [parabolaBoxBilinearMoment,parabolaRapidBilinearMoment,F,W,B,
    parabolaMomentFunction,mul_assoc] using hlocal.trans hwhole

private theorem parabolaRapid_le_source {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {C R : ℝ} (hR : 0 < R)
    (hC : ∀ R r t α γ : ℝ,
      parabolaRapidWeight R r t α γ ≤ C*parabolaSourceWeight R r t α γ)
    (r t : ℝ) :
    parabolaRapidBilinearMoment S V z c x y R r t ≤
      C*parabolaSourceBilinearMoment S V z c x y R r t := by
  have hiR := parabolaMomentFunction_integrable S V z c x y
    ((integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t))
  have hiS := parabolaMomentFunction_integrable S V z c x y
    (integrable_parabolaSourceWeight hR r t)
  have hb := integral_mono hiR (hiS.const_mul C)
    (fun p => by
      have h := mul_le_mul_of_nonneg_right (hC R r t p.1 p.2)
        (parabolaMomentFunction_nonneg S V z c x y p)
      simpa only [parabolaRapidWeight,mul_assoc] using h)
  rw [integral_const_mul] at hb
  simpa only [parabolaRapidBilinearMoment,parabolaSourceBilinearMoment,
    parabolaMomentFunction,parabolaRapidWeight,mul_assoc] using hb

theorem exists_parabola_source_bilinear_localization {ι τ : Type*} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
        (z : ℤ → ι → ℂ) (c : τ → ℂ)
        (x : ℤ → ι → ℝ) (y : τ → ℝ)
        (w d u ν R : ℝ),
        0 < w → 0 < ν → ν ≤ 1 → 0 < R →
        1/(100*R) ≤ w^2 → u ≤ ν → 3*ν ≤ |d| →
        (∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc d (d+u)) →
        (∀ k ∈ V, y k ∈ Icc 0 w) →
        (∀ i ∈ J, ∀ k ∈ S i,
          x i k ∈ Ico (d+w^2*(i : ℝ)) (d+w^2*((i : ℝ)+1))) →
        ∀ r t : ℝ,
        parabolaBoxBilinearMoment (J.sigma S) V
          (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y R r t ≤
          (C/ν)*∑ i ∈ J, parabolaSourceBilinearMoment (S i) V (z i) c (x i) y R r t := by
  obtain ⟨C,hC,h⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨7*C,by positivity,?_⟩
  intro J S V z c x y w d u ν R hw hν hν₁ hR hwidth hu hd hx hy hblock r t
  have hl := (parabolaBox_le_rapid (J.sigma S) V
    (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y hR r t).trans
    (parabolaRapidBilinearMoment_localization J S V z c x y hw hν hν₁ hR hwidth hu hd hx hy hblock r t)
  have hm := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := J) (fun i _ => parabolaRapid_le_source (S i) V (z i) c (x i) y hR h r t))
    (show 0 ≤ 7/ν by positivity)
  refine hl.trans (hm.trans_eq ?_)
  rw [← Finset.mul_sum]
  ring

end TaoTrudgianYang2025



noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

private def parabolaShear (β : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1+2*β*p.2,p.2)
  invFun p := (p.1-2*β*p.2,p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem parabolaShear_measurePreserving (β : ℝ) :
    MeasurePreserving (parabolaShear β) volume volume := by
  have hs : MeasurePreserving (fun p : ℝ × ℝ => (p.1,2*β*p.1+p.2))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id (volume : Measure ℝ)).skew_product
      (by fun_prop) (Filter.Eventually.of_forall (fun x =>
        map_add_left_eq_self (volume : Measure ℝ) (2*β*x)))
  have h := Measure.measurePreserving_swap.comp (hs.comp Measure.measurePreserving_swap)
  convert h using 1
  ext p <;> simp [parabolaShear,add_comm]

theorem parabola_sum_shift {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → ℝ) (β α γ : ℝ) :
    sargosPlanarSum S z x (fun i => (x i)^2) α γ =
      fordAdditiveCharacter (β*α+β^2*γ)*
      sargosPlanarSum S z (fun i => x i-β)
        (fun i => (x i-β)^2) (α+2*β*γ) γ := by
  unfold sargosPlanarSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm (fordAdditiveCharacter _),← fordAdditiveCharacter_add]
  congr 2
  ring

private theorem parabola_norm_shift {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → ℝ) (β α γ : ℝ) :
    ‖sargosPlanarSum S z x (fun i => (x i)^2) α γ‖ =
      ‖sargosPlanarSum S z (fun i => x i-β)
        (fun i => (x i-β)^2) (α+2*β*γ) γ‖ := by
  rw [parabola_sum_shift S z x β α γ,norm_mul,sargos_character_norm,one_mul]

private theorem parabolaShear_box {β R r t : ℝ} (hR : 0 ≤ R) (hβ : |β| ≤ 1) :
    (Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)) ⊆
      (parabolaShear β) ⁻¹'
        (Icc (r+2*β*t-3*R) (r+2*β*t+3*R) ×ˢ Icc (t-3*R) (t+3*R)) := by
  intro p hp
  have hα : |p.1-r| ≤ R := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  have hγ : |p.2-t| ≤ R := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
  have hmul : |β| * |p.2-t| ≤ R :=
    (mul_le_mul hβ hγ (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have ha : |p.1+2*β*p.2-(r+2*β*t)| ≤ 3*R := by
    rw [show p.1+2*β*p.2-(r+2*β*t) = (p.1-r)+2*β*(p.2-t) by ring]
    have h := abs_add_le (p.1-r) (2*β*(p.2-t))
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at h
    nlinarith
  have hg : |p.2-t| ≤ 3*R := by linarith
  change (p.1+2*β*p.2,p.2) ∈
    Icc (r+2*β*t-3*R) (r+2*β*t+3*R) ×ˢ Icc (t-3*R) (t+3*R)
  exact ⟨⟨by linarith [(abs_le.mp ha).1],by linarith [(abs_le.mp ha).2]⟩,
    ⟨by linarith [(abs_le.mp hg).1],by linarith [(abs_le.mp hg).2]⟩⟩

private theorem parabola_norm_unshear {β a b : ℝ} (hβ : |β| ≤ 1) :
    ‖(a : ℂ)+(b : ℂ)*Complex.I‖ ≤
      3*‖((a+2*β*b : ℝ) : ℂ)+(b : ℂ)*Complex.I‖ := by
  let Z : ℂ := ((a+2*β*b : ℝ) : ℂ)+(b : ℂ)*Complex.I
  have he : (a : ℂ)+(b : ℂ)*Complex.I = Z-((2*β*b : ℝ) : ℂ) := by
    dsimp [Z]
    push_cast
    ring
  have hb : |b| ≤ ‖Z‖ := by
    simpa [Z] using Complex.abs_im_le_norm Z
  have hm : |β| * |b| ≤ |b| :=
    (mul_le_mul_of_nonneg_right hβ (abs_nonneg b)).trans_eq (one_mul _)
  have hn := norm_sub_le Z ((2*β*b : ℝ) : ℂ)
  rw [← he,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2)] at hn
  change ‖(a : ℂ)+(b : ℂ)*Complex.I‖ ≤ 3*‖Z‖
  nlinarith

private theorem parabolaSourceWeight_shear_le
    {R β : ℝ} (hβ : |β| ≤ 1) (r t α γ : ℝ) :
    parabolaSourceWeight (3*R) (r+2*β*t) t (α+2*β*γ) γ ≤
      9^100*parabolaSourceWeight R r t α γ := by
  let Z : ℂ := (((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I
  let Z' : ℂ := (((α+2*β*γ-(r+2*β*t))/(3*R) : ℝ) : ℂ)+
    ((γ-t)/(3*R) : ℝ)*Complex.I
  have hs : ((((α-r)/R+2*β*((γ-t)/R) : ℝ) : ℂ)+
      ((γ-t)/R : ℝ)*Complex.I) = (3:ℂ)*Z' := by
    dsimp [Z']
    push_cast
    field_simp
    ring
  have hn := parabola_norm_unshear (a := (α-r)/R) (b := (γ-t)/R) hβ
  rw [hs,norm_mul] at hn
  have hn₃ : ‖(3:ℂ)‖ = (3:ℝ) := by norm_num
  rw [hn₃] at hn
  have hb : 1+‖Z‖ ≤ 9*(1+‖Z'‖) := by dsimp [Z]; linarith only [hn]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+‖Z‖) hb 100
  rw [mul_pow] at hp
  change 1/(1+‖Z'‖)^100 ≤ 9^100*(1/(1+‖Z‖)^100)
  rw [mul_one_div,div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  exact hp

private theorem parabolaMomentFunction_shift {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (β : ℝ) (p : ℝ × ℝ) :
    parabolaMomentFunction S V z c x y p =
      parabolaMomentFunction S V z c (fun i => x i-β) (fun j => y j-β)
        (parabolaShear β p) := by
  unfold parabolaMomentFunction
  rw [parabola_norm_shift S z x β p.1 p.2,parabola_norm_shift V c y β p.1 p.2]
  rfl

private theorem parabolaBox_shear {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R β : ℝ}
    (hR : 0 < R) (hβ : |β| ≤ 1) (r t : ℝ) :
    parabolaBoxBilinearMoment S V z c x y R r t ≤
      parabolaBoxBilinearMoment S V z c
        (fun i => x i-β) (fun j => y j-β) (3*R) (r+2*β*t) t := by
  let F := parabolaMomentFunction S V z c (fun i => x i-β) (fun j => y j-β)
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  let B' := Icc (r+2*β*t-3*R) (r+2*β*t+3*R) ×ˢ Icc (t-3*R) (t+3*R)
  have hi : IntegrableOn F B' := ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
    (parabolaMomentFunction_continuous _ _ _ _ _ _).continuousOn
  have hemp := (parabolaShear β).measurableEmbedding
  have hmp := parabolaShear_measurePreserving β
  have hic := (hmp.integrableOn_comp_preimage hemp).mpr hi
  have hb := setIntegral_mono_set hic
    (Filter.Eventually.of_forall (fun p => parabolaMomentFunction_nonneg _ _ _ _ _ _ _))
    (Filter.Eventually.of_forall (fun p hp => parabolaShear_box hR.le hβ (a := p) hp))
  have he := hmp.setIntegral_preimage_emb hemp F B'
  change (∫ p in B, F (parabolaShear β p)) ≤
    ∫ p in (parabolaShear β) ⁻¹' B', F (parabolaShear β p) at hb
  rw [he] at hb
  have heB : parabolaBoxBilinearMoment S V z c x y R r t =
      ∫ p in B, F (parabolaShear β p) := by
    apply integral_congr_ae
    filter_upwards with p
    exact parabolaMomentFunction_shift S V z c x y β p
  rw [heB]
  exact hb

private theorem parabolaSource_shear {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R β : ℝ}
    (hR : 0 < R) (hβ : |β| ≤ 1) (r t : ℝ) :
    parabolaSourceBilinearMoment S V z c
      (fun i => x i-β) (fun j => y j-β) (3*R) (r+2*β*t) t ≤
        9^100*parabolaSourceBilinearMoment S V z c x y R r t := by
  let F := parabolaMomentFunction S V z c x y
  let F' := parabolaMomentFunction S V z c (fun i => x i-β) (fun j => y j-β)
  let W := fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2
  let W' := fun p : ℝ × ℝ => parabolaSourceWeight (3*R) (r+2*β*t) t p.1 p.2
  have hi := parabolaMomentFunction_integrable S V z c x y
    (integrable_parabolaSourceWeight hR r t)
  have hi' := parabolaMomentFunction_integrable S V z c (fun i => x i-β) (fun j => y j-β)
    (integrable_parabolaSourceWeight (by positivity : 0 < 3*R) (r+2*β*t) t)
  have hmp := parabolaShear_measurePreserving β
  have hemp := (parabolaShear β).measurableEmbedding
  have hic := (hmp.integrable_comp_emb hemp).mpr hi'
  have hbound (p : ℝ × ℝ) : W' (parabolaShear β p)*F' (parabolaShear β p) ≤
      9^100*(W p*F p) := by
    have hs : F' (parabolaShear β p) = F p := (parabolaMomentFunction_shift S V z c x y β p).symm
    rw [hs]
    have h := mul_le_mul_of_nonneg_right (parabolaSourceWeight_shear_le (R := R) hβ r t p.1 p.2)
      (parabolaMomentFunction_nonneg S V z c x y p)
    simpa only [W,W',parabolaShear,mul_assoc] using h
  have h := integral_mono hic (hi.const_mul (9^100)) hbound
  have he := hmp.integral_comp hemp (fun p => W' p*F' p)
  change (∫ p, W' (parabolaShear β p)*F' (parabolaShear β p)) ≤
    ∫ p, 9^100*(W p*F p) at h
  rw [he,integral_const_mul] at h
  simpa only [parabolaSourceBilinearMoment,F,F',W,W',parabolaMomentFunction,mul_assoc] using h

theorem exists_parabola_source_localization_arbitrary_intervals {ι τ : Type*} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
        (z : ℤ → ι → ℂ) (c : τ → ℂ)
        (x : ℤ → ι → ℝ) (y : τ → ℝ)
        (w a β u ν R : ℝ),
        0 < w → 0 < ν → ν ≤ 1 → 0 < R →
        |β| ≤ 1 → 1/(100*R) ≤ w^2 → u ≤ ν → 3*ν ≤ |a-β| →
        (∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc a (a+u)) →
        (∀ k ∈ V, y k ∈ Icc β (β+w)) →
        (∀ i ∈ J, ∀ k ∈ S i,
          x i k ∈ Ico (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) →
        ∀ r t : ℝ,
        parabolaBoxBilinearMoment (J.sigma S) V
          (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y R r t ≤
          (C/ν)*∑ i ∈ J, parabolaSourceBilinearMoment (S i) V (z i) c (x i) y R r t := by
  obtain ⟨C,hC,h⟩ := exists_parabola_source_bilinear_localization (ι := ι) (τ := τ)
  refine ⟨C*9^100,by positivity,?_⟩
  intro J S V z c x y w a β u ν R hw hν hν₁ hR hβ hwidth hu hd hx hy hblock r t
  have hw' : 1/(100*(3*R)) ≤ w^2 := by
    apply le_trans _ hwidth
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hx' : ∀ i ∈ J, ∀ k ∈ S i, x i k-β ∈ Icc (a-β) (a-β+u) := by
    intro i hi k hk
    have h := hx i hi k hk
    constructor <;> linarith [h.1,h.2]
  have hy' : ∀ k ∈ V, y k-β ∈ Icc 0 w := by
    intro k hk
    have h := hy k hk
    constructor <;> linarith [h.1,h.2]
  have hblock' : ∀ i ∈ J, ∀ k ∈ S i,
      x i k-β ∈ Ico (a-β+w^2*(i : ℝ)) (a-β+w^2*((i : ℝ)+1)) := by
    intro i hi k hk
    have h := hblock i hi k hk
    constructor <;> linarith [h.1,h.2]
  have hl := (parabolaBox_shear (J.sigma S) V
    (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y hR hβ r t).trans
    (h J S V z c (fun i k => x i k-β) (fun k => y k-β)
      w (a-β) u ν (3*R) hw hν hν₁ (by positivity) hw' hu hd hx' hy' hblock' (r+2*β*t) t)
  have hm := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := J)
    (fun i _ => parabolaSource_shear (S i) V (z i) c (x i) y hR hβ r t))
    (show 0 ≤ C/ν by positivity)
  refine hl.trans (hm.trans_eq ?_)
  rw [← Finset.mul_sum]
  ring

end TaoTrudgianYang2025


/-! Source-weight averaging and finite weighted localization.
Both Fubini changes use proved integrability of the actual finite moments.
The square convention throughout is half-width R. -/

noncomputable section
namespace TaoTrudgianYang2025
open MeasureTheory Set
open scoped BigOperators

private theorem radius_weight_product {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : c ≤ a+b) :
    (1/(1+a)^100)*(1/(1+b)^100) ≤
      (2:ℝ)^100*(1/(1+c)^100)*(1/(1+a)^100+1/(1+b)^100) := by
  have hlarge {v : ℝ} (hv : 0 ≤ v) (hcv : c ≤ 2*v) :
      1/(1+v)^100 ≤ (2:ℝ)^100*(1/(1+c)^100) := by
    have hden : (1+c)^100 ≤ (2:ℝ)^100*(1+v)^100 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    apply (div_le_iff₀ (by positivity : 0 < (1+v)^100)).mpr
    rw [mul_one_div,div_mul_eq_mul_div]
    exact (le_div_iff₀ (by positivity : 0 < (1+c)^100)).mpr (by simpa only [one_mul] using hden)
  rcases le_total a b with hab' | hab'
  · have h := mul_le_mul_of_nonneg_left (hlarge hb (by linarith)) (by positivity : 0 ≤ 1/(1+a)^100)
    calc
      _ ≤ (2:ℝ)^100*(1/(1+c)^100)*(1/(1+a)^100) := by nlinarith only [h]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have h := mul_le_mul_of_nonneg_right (hlarge ha (by linarith)) (by positivity : 0 ≤ 1/(1+b)^100)
    exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity))

private theorem sourceWeight_triangle (R r t α γ β δ : ℝ) :
    ‖(((β-r)/R : ℝ) : ℂ)+((δ-t)/R : ℝ)*Complex.I‖ ≤
      ‖(((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I‖+
      ‖(((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I‖ := by
  have heq :
      (((β-r)/R : ℝ) : ℂ)+((δ-t)/R : ℝ)*Complex.I =
        ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I)+
        ((((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I) := by
    push_cast
    ring
  rw [heq]
  exact norm_add_le _ _

theorem parabolaSourceWeight_product_bound (R r t α γ β δ : ℝ) :
    parabolaSourceWeight R r t α γ * parabolaSourceWeight R α γ β δ ≤
      (2:ℝ)^100 * parabolaSourceWeight R r t β δ *
        (parabolaSourceWeight R r t α γ + parabolaSourceWeight R α γ β δ) :=
  radius_weight_product (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (sourceWeight_triangle R r t α γ β δ)

theorem integral_parabolaSourceWeight (R r t : ℝ) :
    (∫ p : ℝ × ℝ, parabolaSourceWeight R r t p.1 p.2) =
      R^2 * ∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2 := by
  let F := fun p : ℝ × ℝ => parabolaSourceWeight 1 0 0 p.1 p.2
  have heq (p : ℝ × ℝ) :
      parabolaSourceWeight R r t p.1 p.2 = F (R⁻¹ • (p-(r,t))) := by
    simp only [F,parabolaSourceWeight,Prod.smul_fst,Prod.smul_snd,
      Prod.fst_sub,Prod.snd_sub,smul_eq_mul,sub_zero,div_eq_mul_inv,inv_one,mul_one,mul_comm]
  simp_rw [heq]
  rw [integral_sub_right_eq_self (fun p : ℝ × ℝ => F (R⁻¹ • p)) (r,t),
    Measure.integral_comp_inv_smul]
  norm_num [Module.finrank_prod,abs_of_nonneg (sq_nonneg R),F]

private theorem parabolaSourceWeight_le_one (R r t α γ : ℝ) :
    parabolaSourceWeight R r t α γ ≤ 1 := by
  unfold parabolaSourceWeight
  apply div_le_one_of_le₀ ?_ (by positivity)
  exact one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))

private theorem parabolaSourceWeight_symm (R r t α γ : ℝ) :
    parabolaSourceWeight R r t α γ = parabolaSourceWeight R α γ r t := by
  have heq :
      (((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I =
        -((((r-α)/R : ℝ) : ℂ)+((t-γ)/R : ℝ)*Complex.I) := by
    push_cast
    ring
  simp only [parabolaSourceWeight,heq,norm_neg]

private theorem integrable_sourceWeight_product {R : ℝ} (hR : 0 < R)
    (r t β δ : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      parabolaSourceWeight R r t p.1 p.2 * parabolaSourceWeight R p.1 p.2 β δ) := by
  have heq : (fun p : ℝ × ℝ => parabolaSourceWeight R p.1 p.2 β δ) =
      fun p => parabolaSourceWeight R β δ p.1 p.2 := by
    funext p
    exact parabolaSourceWeight_symm R p.1 p.2 β δ
  change Integrable ((fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) *
    (fun p => parabolaSourceWeight R p.1 p.2 β δ))
  rw [heq]
  apply (integrable_parabolaSourceWeight hR r t).mul_bdd
    (continuous_sourceWeight R β δ).aestronglyMeasurable (c := 1)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)]
  exact parabolaSourceWeight_le_one _ _ _ _ _

theorem parabolaSourceWeight_convolution_bound {R : ℝ} (hR : 0 < R)
    (r t β δ : ℝ) :
    (∫ p : ℝ × ℝ,
      parabolaSourceWeight R r t p.1 p.2 * parabolaSourceWeight R p.1 p.2 β δ) ≤
        (2:ℝ)^101*R^2*
          (∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2) *
          parabolaSourceWeight R r t β δ := by
  have hb := integral_mono
    (integrable_sourceWeight_product hR r t β δ)
    (((integrable_parabolaSourceWeight hR r t).add
      (integrable_parabolaSourceWeight hR β δ)).const_mul
        ((2:ℝ)^100*parabolaSourceWeight R r t β δ))
    (fun p => by
      change _ ≤ (2:ℝ)^100*parabolaSourceWeight R r t β δ *
        (parabolaSourceWeight R r t p.1 p.2+parabolaSourceWeight R β δ p.1 p.2)
      conv_rhs => rw [parabolaSourceWeight_symm R β δ p.1 p.2]
      exact parabolaSourceWeight_product_bound R r t p.1 p.2 β δ)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul,
    integral_add (integrable_parabolaSourceWeight hR r t)
      (integrable_parabolaSourceWeight hR β δ),
    integral_parabolaSourceWeight R r t,integral_parabolaSourceWeight R β δ] at hb
  apply hb.trans_eq
  rw [show (101 : ℕ) = 100+1 from rfl,pow_succ]
  ring


private theorem parabolaSourceWeight_triangle_lower (R r t α γ β δ : ℝ) :
    parabolaSourceWeight R r t α γ * parabolaSourceWeight R α γ β δ ≤
      parabolaSourceWeight R r t β δ := by
  have h := sourceWeight_triangle R r t α γ β δ
  have hm := mul_nonneg
    (norm_nonneg ((((α-r)/R : ℝ) : ℂ)+((γ-t)/R : ℝ)*Complex.I))
    (norm_nonneg ((((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I))
  unfold parabolaSourceWeight
  rw [div_mul_div_comm,one_mul,← mul_pow]
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by nlinarith only [h,hm]) _

private theorem parabolaSourceWeight_box_lower {R : ℝ} (hR : 0 < R)
    {α γ β δ : ℝ} (hα : |β-α| ≤ R) (hγ : |δ-γ| ≤ R) :
    1/(3:ℝ)^100 ≤ parabolaSourceWeight R α γ β δ := by
  have ha : |(β-α)/R| ≤ 1 := by
    rw [abs_div,abs_of_pos hR]
    exact (div_le_one hR).mpr hα
  have hb : |(δ-γ)/R| ≤ 1 := by
    rw [abs_div,abs_of_pos hR]
    exact (div_le_one hR).mpr hγ
  have hn :
      ‖(((β-α)/R : ℝ) : ℂ)+((δ-γ)/R : ℝ)*Complex.I‖ ≤ 2 := by
    calc
      _ ≤ ‖(((β-α)/R : ℝ) : ℂ)‖+‖((δ-γ)/R : ℝ)*Complex.I‖ := norm_add_le _ _
      _ = |(β-α)/R|+|(δ-γ)/R| := by
        rw [norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_I,mul_one,
          Real.norm_eq_abs,Real.norm_eq_abs]
      _ ≤ 2 := by linarith
  unfold parabolaSourceWeight
  apply one_div_le_one_div_of_le (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) _

theorem parabolaSourceWeight_box_average_lower {R : ℝ} (hR : 0 < R)
    (r t α γ : ℝ) :
    (4*R^2/(3:ℝ)^100)*parabolaSourceWeight R r t α γ ≤
      ∫ p : ℝ × ℝ in Icc (α-R) (α+R) ×ˢ Icc (γ-R) (γ+R),
        parabolaSourceWeight R r t p.1 p.2 := by
  let B := Icc (α-R) (α+R) ×ˢ Icc (γ-R) (γ+R)
  have hb : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hi := (integrable_parabolaSourceWeight hR r t).integrableOn (s := B)
  have hconst : IntegrableOn (fun _ : ℝ × ℝ =>
      (1/(3:ℝ)^100)*parabolaSourceWeight R r t α γ) B :=
    integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  have hle := setIntegral_mono_on hconst hi hb (fun p hp => by
    have hα : |p.1-α| ≤ R := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
    have hγ : |p.2-γ| ≤ R := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
    have h1 := mul_le_mul_of_nonneg_left (parabolaSourceWeight_box_lower hR hα hγ)
      (parabolaSourceWeight_nonneg R r t α γ)
    have h2 := parabolaSourceWeight_triangle_lower R r t α γ p.1 p.2
    exact (by simpa only [mul_comm] using h1.trans h2))
  have hv : volume.real B = 4*R^2 := by
    change (volume.prod volume).real (Icc (α-R) (α+R) ×ˢ Icc (γ-R) (γ+R)) = _
    rw [measureReal_prod_prod,Real.volume_real_Icc_of_le (by linarith),
      Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [setIntegral_const,hv,smul_eq_mul] at hle
  convert hle using 1
  ring


private theorem bounded_weighted_convolution_integrable
    {F W K : (ℝ × ℝ) → ℝ} (hF : Continuous F)
    (hbound : ∃ M : ℝ, ∀ p, ‖F p‖ ≤ M) (hW : Integrable W) (hK : Integrable K) :
    Integrable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) =>
      W pq.2 * K (pq.1-pq.2) * F pq.1) := by
  obtain ⟨M,hM⟩ := hbound
  have hc := hW.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hK
  apply hc.mul_bdd (hF.comp continuous_fst).aestronglyMeasurable (c := M)
  filter_upwards with pq
  exact hM pq.1

private theorem bounded_weighted_convolution_swap
    {F W K : (ℝ × ℝ) → ℝ} (hF : Continuous F)
    (hbound : ∃ M : ℝ, ∀ p, ‖F p‖ ≤ M) (hW : Integrable W) (hK : Integrable K) :
    (∫ q : ℝ × ℝ, W q * ∫ p : ℝ × ℝ, K (p-q)*F p) =
      ∫ p : ℝ × ℝ, (∫ q : ℝ × ℝ, W q*K (p-q))*F p := by
  have hi := bounded_weighted_convolution_integrable hF hbound hW hK
  have hs := integral_integral_swap (μ := volume) (ν := volume)
    (f := fun (p q : ℝ × ℝ) => W q*K (p-q)*F p) hi
  calc
    _ = ∫ q : ℝ × ℝ, ∫ p : ℝ × ℝ, W q*K (p-q)*F p := by
      simp_rw [mul_assoc,integral_const_mul]
    _ = ∫ p : ℝ × ℝ, ∫ q : ℝ × ℝ, W q*K (p-q)*F p := hs.symm
    _ = _ := by simp_rw [integral_mul_const]

private theorem parabolaMomentFunction_bounded {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    ∃ M : ℝ, ∀ p : ℝ × ℝ, ‖parabolaMomentFunction S V z c x y p‖ ≤ M := by
  refine ⟨(∑ i ∈ S, ‖z i‖)^2*(∑ j ∈ V, ‖c j‖)^4,fun p => ?_⟩
  rw [Real.norm_eq_abs,abs_of_nonneg (parabolaMomentFunction_nonneg _ _ _ _ _ _ _)]
  unfold parabolaMomentFunction
  have hS := norm_sargosPlanarSum_le_sum_norm S z x (fun i => (x i)^2) p.1 p.2
  have hV := norm_sargosPlanarSum_le_sum_norm V c y (fun j => (y j)^2) p.1 p.2
  gcongr

private theorem sourceWeight_translation (R : ℝ) (p q : ℝ × ℝ) :
    parabolaSourceWeight R 0 0 (p-q).1 (p-q).2 =
      parabolaSourceWeight R q.1 q.2 p.1 p.2 := by
  simp only [parabolaSourceWeight,Prod.fst_sub,Prod.snd_sub,sub_zero]

theorem parabolaSourceBilinearMoment_average_bound {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    (∫ q : ℝ × ℝ, parabolaSourceWeight R r t q.1 q.2*
      parabolaSourceBilinearMoment S V z c x y R q.1 q.2) ≤
        (2:ℝ)^101*R^2*
          (∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2) *
          parabolaSourceBilinearMoment S V z c x y R r t := by
  let F := parabolaMomentFunction S V z c x y
  let W := fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2
  let K := fun p : ℝ × ℝ => parabolaSourceWeight R 0 0 p.1 p.2
  have hF := parabolaMomentFunction_continuous S V z c x y
  have hb := parabolaMomentFunction_bounded S V z c x y
  have hW : Integrable W := integrable_parabolaSourceWeight hR r t
  have hK : Integrable K := integrable_parabolaSourceWeight hR 0 0
  have heq (q : ℝ × ℝ) :
      parabolaSourceBilinearMoment S V z c x y R q.1 q.2 =
        ∫ p : ℝ × ℝ, K (p-q)*F p := by
    simp only [parabolaSourceBilinearMoment,K,F,parabolaMomentFunction,
      sourceWeight_translation,mul_assoc]
  simp_rw [heq]
  rw [bounded_weighted_convolution_swap hF hb hW hK]
  have hi := (bounded_weighted_convolution_integrable hF hb hW hK).integral_prod_left
  simp_rw [integral_mul_const] at hi
  have hWF := parabolaMomentFunction_integrable S V z c x y hW
  have hle := integral_mono hi (hWF.const_mul
    ((2:ℝ)^101*R^2*(∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2)))
    (fun p => by
      have hconv := parabolaSourceWeight_convolution_bound hR r t p.1 p.2
      simpa only [W,K,F,sourceWeight_translation,mul_assoc] using
        mul_le_mul_of_nonneg_right hconv
        (parabolaMomentFunction_nonneg S V z c x y p))
  rw [integral_const_mul] at hle
  simpa only [parabolaSourceBilinearMoment,W,F,parabolaMomentFunction,mul_assoc] using hle


private def parabolaBoxKernel (R : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ => 1) p

private theorem parabolaBoxKernel_integrable (R : ℝ) :
    Integrable (parabolaBoxKernel R) := by
  exact (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top).integrable_indicator
    (measurableSet_Icc.prod measurableSet_Icc)

private theorem parabolaBoxKernel_translate (R : ℝ) (p q : ℝ × ℝ) :
    parabolaBoxKernel R (p-q) =
      (Icc (q.1-R) (q.1+R) ×ˢ Icc (q.2-R) (q.2+R)).indicator (fun _ => 1) p := by
  have hi : p-q ∈ Icc (-R) R ×ˢ Icc (-R) R ↔
      p ∈ Icc (q.1-R) (q.1+R) ×ˢ Icc (q.2-R) (q.2+R) := by
    simp only [mem_prod,mem_Icc,Prod.fst_sub,Prod.snd_sub]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  simp only [parabolaBoxKernel,Set.indicator,hi]

private theorem parabolaBoxKernel_symm (R : ℝ) (p q : ℝ × ℝ) :
    parabolaBoxKernel R (p-q) = parabolaBoxKernel R (q-p) := by
  have hi : p-q ∈ Icc (-R) R ×ˢ Icc (-R) R ↔
      q-p ∈ Icc (-R) R ×ˢ Icc (-R) R := by
    simp only [mem_prod,mem_Icc,Prod.fst_sub,Prod.snd_sub]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨by linarith,by linarith⟩,by linarith,by linarith⟩
  simp only [parabolaBoxKernel,Set.indicator,hi]

private theorem parabolaBoxKernel_integral (F : ℝ × ℝ → ℝ)
    (R : ℝ) (q : ℝ × ℝ) :
    (∫ p : ℝ × ℝ, parabolaBoxKernel R (p-q)*F p) =
      ∫ p : ℝ × ℝ in Icc (q.1-R) (q.1+R) ×ˢ Icc (q.2-R) (q.2+R), F p := by
  simp_rw [parabolaBoxKernel_translate,← Set.indicator_mul_left,one_mul]
  exact integral_indicator (measurableSet_Icc.prod measurableSet_Icc)

theorem parabolaBoxBilinearMoment_average_lower {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    (4*R^2/(3:ℝ)^100)*parabolaSourceBilinearMoment S V z c x y R r t ≤
      ∫ q : ℝ × ℝ, parabolaSourceWeight R r t q.1 q.2*
        parabolaBoxBilinearMoment S V z c x y R q.1 q.2 := by
  let F := parabolaMomentFunction S V z c x y
  let W := fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2
  have hF := parabolaMomentFunction_continuous S V z c x y
  have hb := parabolaMomentFunction_bounded S V z c x y
  have hW : Integrable W := integrable_parabolaSourceWeight hR r t
  have hK := parabolaBoxKernel_integrable R
  have heq (q : ℝ × ℝ) :
      parabolaBoxBilinearMoment S V z c x y R q.1 q.2 =
        ∫ p : ℝ × ℝ, parabolaBoxKernel R (p-q)*F p :=
    (parabolaBoxKernel_integral F R q).symm
  simp_rw [heq]
  rw [bounded_weighted_convolution_swap hF hb hW hK]
  have hi := (bounded_weighted_convolution_integrable hF hb hW hK).integral_prod_left
  simp_rw [integral_mul_const] at hi
  have hWF := parabolaMomentFunction_integrable S V z c x y hW
  have hinner (p : ℝ × ℝ) :
      (∫ q : ℝ × ℝ, W q*parabolaBoxKernel R (p-q)) =
        ∫ q : ℝ × ℝ in Icc (p.1-R) (p.1+R) ×ˢ Icc (p.2-R) (p.2+R), W q := by
    simp_rw [parabolaBoxKernel_symm R p,mul_comm (W _)]
    exact parabolaBoxKernel_integral W R p
  have hle := integral_mono (hWF.const_mul (4*R^2/(3:ℝ)^100)) hi
    (fun p => by
      rw [hinner]
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (parabolaSourceWeight_box_average_lower hR r t p.1 p.2)
          (parabolaMomentFunction_nonneg S V z c x y p))
  rw [integral_const_mul] at hle
  simpa only [parabolaSourceBilinearMoment,W,F,parabolaMomentFunction,mul_assoc] using hle


private theorem bounded_weighted_convolution_outer_integrable
    {F W K : (ℝ × ℝ) → ℝ} (hF : Continuous F)
    (hbound : ∃ M : ℝ, ∀ p, ‖F p‖ ≤ M) (hW : Integrable W) (hK : Integrable K) :
    Integrable (fun q : ℝ × ℝ => W q * ∫ p : ℝ × ℝ, K (p-q)*F p) := by
  have hi := (bounded_weighted_convolution_integrable hF hbound hW hK).integral_prod_right
  simpa only [mul_assoc,integral_const_mul] using hi

private theorem weighted_sourceMoment_integrable {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    Integrable (fun q : ℝ × ℝ => parabolaSourceWeight R r t q.1 q.2 *
      parabolaSourceBilinearMoment S V z c x y R q.1 q.2) := by
  have hi := bounded_weighted_convolution_outer_integrable
    (parabolaMomentFunction_continuous S V z c x y)
    (parabolaMomentFunction_bounded S V z c x y)
    (integrable_parabolaSourceWeight hR r t)
    (integrable_parabolaSourceWeight hR 0 0)
  simpa only [sourceWeight_translation,parabolaMomentFunction,
    parabolaSourceBilinearMoment,mul_assoc] using hi

private theorem weighted_boxMoment_integrable {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    Integrable (fun q : ℝ × ℝ => parabolaSourceWeight R r t q.1 q.2 *
      parabolaBoxBilinearMoment S V z c x y R q.1 q.2) := by
  have hi := bounded_weighted_convolution_outer_integrable
    (parabolaMomentFunction_continuous S V z c x y)
    (parabolaMomentFunction_bounded S V z c x y)
    (integrable_parabolaSourceWeight hR r t)
    (parabolaBoxKernel_integrable R)
  simpa only [parabolaBoxKernel_integral,parabolaMomentFunction,
    parabolaBoxBilinearMoment] using hi

private theorem parabolaSourceBilinearMoment_nonneg {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) (R r t : ℝ) :
    0 ≤ parabolaSourceBilinearMoment S V z c x y R r t := by
  apply integral_nonneg
  intro p
  exact mul_nonneg
    (mul_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) _)

/-- Weighted finite localization for actual separated frequency intervals.
The physical scale, shifts, coefficients and indexed multiplicities are all
quantified after one uniform numerical loss. -/
theorem exists_parabola_weighted_localization {ι τ : Type*} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
        (z : ℤ → ι → ℂ) (c : τ → ℂ)
        (x : ℤ → ι → ℝ) (y : τ → ℝ)
        (w a β u ν R : ℝ),
        0 < w → 0 < ν → ν ≤ 1 → 0 < R →
        |β| ≤ 1 → 1/(100*R) ≤ w^2 → u ≤ ν → 3*ν ≤ |a-β| →
        (∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc a (a+u)) →
        (∀ k ∈ V, y k ∈ Icc β (β+w)) →
        (∀ i ∈ J, ∀ k ∈ S i,
          x i k ∈ Ico (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) →
        ∀ r t : ℝ,
        parabolaSourceBilinearMoment (J.sigma S) V
          (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y R r t ≤
          (C/ν)*∑ i ∈ J, parabolaSourceBilinearMoment (S i) V (z i) c (x i) y R r t := by
  obtain ⟨C,hC,hbox⟩ := exists_parabola_source_localization_arbitrary_intervals (ι := ι) (τ := τ)
  let M := ∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2
  have hM : 0 ≤ M := integral_nonneg (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
  let C' := C*(2:ℝ)^101*(3:ℝ)^100*(M+1)
  refine ⟨C',by dsimp [C']; positivity,?_⟩
  intro J S V z c x y w a β u ν R hw hν hν₁ hR hβ hwidth hu hd hx hy hblock r t
  let W := fun q : ℝ × ℝ => parabolaSourceWeight R r t q.1 q.2
  let F := fun q : ℝ × ℝ => parabolaBoxBilinearMoment (J.sigma S) V
    (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y R q.1 q.2
  let G := fun i (q : ℝ × ℝ) => parabolaSourceBilinearMoment (S i) V (z i) c (x i) y R q.1 q.2
  have hWF : Integrable (fun q => W q*F q) :=
    weighted_boxMoment_integrable _ _ _ _ _ _ hR r t
  have hWG (i : ℤ) : Integrable (fun q => W q*G i q) :=
    weighted_sourceMoment_integrable _ _ _ _ _ _ hR r t
  have hsum : Integrable (fun q : ℝ × ℝ => ∑ i ∈ J, W q*G i q) :=
    integrable_finsetSum J (fun i _ => hWG i)
  have havg := integral_mono hWF (hsum.const_mul (C/ν)) (fun q => by
    have h := mul_le_mul_of_nonneg_left
      (hbox J S V z c x y w a β u ν R hw hν hν₁ hR hβ hwidth hu hd hx hy hblock q.1 q.2)
      (parabolaSourceWeight_nonneg R r t q.1 q.2)
    simpa only [W,F,G,Finset.mul_sum,mul_assoc,mul_left_comm] using h)
  rw [integral_const_mul,integral_finsetSum J (fun i _ => hWG i)] at havg
  have hupp := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := J)
    (fun i _ => parabolaSourceBilinearMoment_average_bound (S i) V (z i) c (x i) y hR r t))
    (show 0 ≤ C/ν by positivity)
  have hlow := parabolaBoxBilinearMoment_average_lower (J.sigma S) V
    (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y hR r t
  have hcombined := hlow.trans (havg.trans hupp)
  rw [← Finset.mul_sum] at hcombined
  have hbudget : (C/ν)*((2:ℝ)^101*R^2*M) ≤
      (4*R^2/(3:ℝ)^100)*(C'/ν) := by
    have hm : M ≤ 4*(M+1) := by linarith
    have hh := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ (C/ν)*((2:ℝ)^101*R^2) by positivity)
    calc
      _ ≤ (C/ν)*((2:ℝ)^101*R^2)*(4*(M+1)) := by simpa only [mul_assoc] using hh
      _ = _ := by dsimp [C']; field_simp
  have hnn : 0 ≤ ∑ i ∈ J, parabolaSourceBilinearMoment (S i) V (z i) c (x i) y R r t :=
    Finset.sum_nonneg (fun i _ => parabolaSourceBilinearMoment_nonneg _ _ _ _ _ _ _ _ _)
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4*R^2/(3:ℝ)^100)).mp
  exact hcombined.trans (by
    simpa only [mul_assoc,M] using mul_le_mul_of_nonneg_right hbudget hnn)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators NNReal ENNReal
namespace TaoTrudgianYang2025

def parabolaBandGauge (ξ κ : ℝ) : ℝ := max |κ| |κ-2*ξ|

theorem parabolaBandGauge_nonneg (ξ κ : ℝ) : 0 ≤ parabolaBandGauge ξ κ :=
  le_trans (abs_nonneg _) (le_max_left _ _)

theorem parabolaBandGauge_slope_le {a : ℝ} (ha : a ∈ Icc 0 1) (ξ κ : ℝ) :
    |κ-2*a*ξ| ≤ parabolaBandGauge ξ κ := by
  have heq : κ-2*a*ξ = (1-a)*κ+a*(κ-2*ξ) := by ring
  rw [heq]
  calc
    _ ≤ |(1-a)*κ|+|a*(κ-2*ξ)| := abs_add_le _ _
    _ = (1-a)*|κ|+a*|κ-2*ξ| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by linarith [ha.2] : 0 ≤ 1-a),abs_of_nonneg ha.1]
    _ ≤ (1-a)*parabolaBandGauge ξ κ+a*parabolaBandGauge ξ κ :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [ha.2]))
        (mul_le_mul_of_nonneg_left (le_max_right _ _) ha.1)
    _ = _ := by ring

/-- Exact stability of the adapted Fourier band under subinterval rescaling. -/
theorem parabolaBandGauge_rescale_le {a σ : ℝ}
    (hσ : 0 ≤ σ) (ha : 0 ≤ a) (haσ : a+σ ≤ 1) (ξ κ : ℝ) :
    σ^2*parabolaBandGauge ξ κ ≤
      parabolaBandGauge (σ*ξ) (2*a*σ*ξ+σ^2*κ) := by
  have h1 := parabolaBandGauge_slope_le
    (show a ∈ Icc 0 1 from ⟨ha,by linarith⟩) (σ*ξ) (2*a*σ*ξ+σ^2*κ)
  have h2 := parabolaBandGauge_slope_le
    (show a+σ ∈ Icc 0 1 from ⟨by linarith,haσ⟩) (σ*ξ) (2*a*σ*ξ+σ^2*κ)
  have he1 : 2*a*σ*ξ+σ^2*κ-2*a*(σ*ξ) = σ^2*κ := by ring
  have he2 : 2*a*σ*ξ+σ^2*κ-2*(a+σ)*(σ*ξ) = σ^2*(κ-2*ξ) := by ring
  rw [he1,abs_mul,abs_of_nonneg (sq_nonneg σ)] at h1
  rw [he2,abs_mul,abs_of_nonneg (sq_nonneg σ)] at h2
  unfold parabolaBandGauge
  rw [mul_max_of_nonneg _ _ (sq_nonneg σ)]
  exact max_le h1 h2

theorem parabolaBandGauge_rescale_gap {a σ δ ξ κ : ℝ}
    (hσ : 0 < σ) (ha : 0 ≤ a) (haσ : a+σ ≤ 1)
    (hgap : (δ/σ)^2 ≤ parabolaBandGauge ξ κ) :
    δ^2 ≤ parabolaBandGauge (σ*ξ) (2*a*σ*ξ+σ^2*κ) := by
  have h := (mul_le_mul_of_nonneg_left hgap (sq_nonneg σ)).trans
    (parabolaBandGauge_rescale_le hσ.le ha haσ ξ κ)
  have he : σ^2*(δ/σ)^2 = δ^2 := by field_simp
  simpa only [he] using h


private def parabolaRescaling (a σ : ℝ) (hσ : σ ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) where
  toFun p := (σ*p.1+2*a*σ*p.2,σ^2*p.2)
  invFun p := (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)
  left_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  right_inv p := by
    ext <;> dsimp <;> field_simp
    ring
  map_add' p q := by
    ext <;> dsimp <;> ring
  map_smul' c p := by
    ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem parabolaRescaling_haar_factor (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ≥0, 0 < c ∧
      Measure.map e (volume : Measure (ℝ × ℝ)) = (c : ℝ≥0∞) • volume := by
  haveI : (Measure.map e (volume : Measure (ℝ × ℝ))).IsAddHaarMeasure :=
    e.isAddHaarMeasure_map volume
  refine ⟨Measure.addHaarScalarFactor (Measure.map e volume) volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _,?_⟩
  exact Measure.isAddLeftInvariant_eq_smul _ _

private theorem parabolaRescaling_integrable
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p => W (e p)) := by
  obtain ⟨c,hc,he⟩ := parabolaRescaling_haar_factor e
  apply (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv W).mp
  change Integrable W (Measure.map e volume)
  rw [he]
  exact hW.smul_measure ENNReal.coe_ne_top

private theorem parabolaRescaling_integral
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ × ℝ → F,
      (∫ p : ℝ × ℝ, f (e p)) = c • ∫ p : ℝ × ℝ, f p := by
  obtain ⟨c,hc,he⟩ := parabolaRescaling_haar_factor e
  refine ⟨c,hc,fun f => ?_⟩
  calc
    (∫ p : ℝ × ℝ, f (e p)) = ∫ p, f p ∂Measure.map e volume :=
      (integral_map_equiv (μ := volume) e.toHomeomorph.toMeasurableEquiv f).symm
    _ = _ := by rw [he,integral_smul_measure,ENNReal.coe_toReal]

/-- Literal Fourier-vanishing condition adapted to the two endpoint tangents.
This is a support condition on an actual integrable weight, not a moment bound. -/
def ParabolaWeightBand (δ : ℝ) (W : ℝ × ℝ → ℝ) : Prop :=
  (∀ p, 0 ≤ W p) ∧ Integrable W ∧
    ∀ ξ κ : ℝ, δ^2 ≤ parabolaBandGauge ξ κ →
      (∫ p : ℝ × ℝ, (W p : ℂ)*fordAdditiveCharacter (ξ*p.1+κ*p.2)) = 0

theorem ParabolaWeightBand.rescale {δ a σ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W) (hσ : 0 < σ) (ha : 0 ≤ a) (haσ : a+σ ≤ 1) :
    ParabolaWeightBand (δ/σ)
      (fun p : ℝ × ℝ => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) := by
  let e := parabolaRescaling a σ hσ.ne'
  refine ⟨fun p => hW.1 _,parabolaRescaling_integrable e.symm hW.2.1,?_⟩
  intro ξ κ hgap
  obtain ⟨c,hc,hint⟩ := parabolaRescaling_integral (F := ℂ) e.symm
  let f := fun p : ℝ × ℝ => (W p : ℂ)*
    fordAdditiveCharacter (ξ*(e p).1+κ*(e p).2)
  have heq : (∫ p : ℝ × ℝ,
      ((W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) : ℂ)*fordAdditiveCharacter (ξ*p.1+κ*p.2)) =
      ∫ p : ℝ × ℝ, f (e.symm p) := by
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [f]
    rw [e.apply_symm_apply]
    rfl
  rw [heq,hint f]
  have hchar := hW.2.2 (σ*ξ) (2*a*σ*ξ+σ^2*κ)
    (parabolaBandGauge_rescale_gap hσ ha haσ hgap)
  have he (p : ℝ × ℝ) :
      ξ*(e p).1+κ*(e p).2 = (σ*ξ)*p.1+(2*a*σ*ξ+σ^2*κ)*p.2 := by
    dsimp [e,parabolaRescaling]
    ring
  dsimp only [f]
  simp_rw [he]
  rw [hchar,smul_zero]

/-- The already constructed nonzero rapid cutoff lies in the adapted band. -/
theorem parabolaRapidWeight_band {δ R : ℝ} (hR : 0 < R)
    (hwidth : 3/(100*R) ≤ δ^2) (r t : ℝ) :
    ParabolaWeightBand δ (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2) := by
  refine ⟨fun p => parabolaRapidWeight_nonneg _ _ _ _ _,
    (integrable_parabolaRapidKernel hR r).mul_prod (integrable_parabolaRapidKernel hR t),?_⟩
  intro ξ κ hgap
  have hgap' : 1/(100*R) ≤ |ξ| ∨ 1/(100*R) ≤ |κ| := by
    by_contra h
    push Not at h
    have hh : 3*(1/(100*R)) ≤ δ^2 := by
      simpa only [div_eq_mul_inv,one_mul] using hwidth
    have ht : |κ-2*ξ| ≤ |κ|+2*|ξ| := by
      simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] using abs_sub κ (2*ξ)
    have hm : parabolaBandGauge ξ κ < δ^2 :=
      max_lt (by linarith [h.2,show 0 < 1/(100*R) by positivity])
        (by linarith [h.1,h.2])
    exact (not_lt_of_ge hgap) hm
  have hi := rapidCharacter_integrable hR r t ξ κ
  have he := integral_prod
    (fun p : ℝ × ℝ => (parabolaRapidWeight R r t p.1 p.2 : ℂ)*
      fordAdditiveCharacter (ξ*p.1+κ*p.2)) hi
  exact he.trans (integral_parabolaRapidWeight_character_zero hR hgap' r t)

theorem exists_parabolaWeightBand_nonzero {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : ℝ × ℝ → ℝ, ParabolaWeightBand δ W ∧ 1 ≤ W (0,0) := by
  let R := 1/δ^2
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨fun p => parabolaRapidWeight R 0 0 p.1 p.2,
    parabolaRapidWeight_band hR ?_ 0 0,?_⟩
  · dsimp [R]
    field_simp
    nlinarith [sq_nonneg δ]
  · exact parabolaRapidWeight_one_le hR (by simp; positivity) (by simp; positivity)

/-- Exact finite sum entry for parabolic rescaling. -/
theorem parabola_sum_rescale {ι : Type*} (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ)
    (a σ α γ : ℝ) (hσ : σ ≠ 0) :
    sargosPlanarSum S z x (fun i => (x i)^2) α γ =
      fordAdditiveCharacter (a*α+a^2*γ)*
        sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => ((x i-a)/σ)^2) (σ*α+2*a*σ*γ) (σ^2*γ) := by
  rw [parabola_sum_shift S z x a α γ]
  congr 1
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  field_simp

def parabolaWeightedBilinearMoment {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (S : Finset ι) (V : Finset τ)
    (z : ι → ℂ) (c : τ → ℂ) (x : ι → ℝ) (y : τ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, W p*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4

private theorem parabola_norm_rescale {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x : ι → ℝ) (a σ α γ : ℝ) (hσ : σ ≠ 0) :
    ‖sargosPlanarSum S z x (fun i => (x i)^2) α γ‖ =
      ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
        (fun i => ((x i-a)/σ)^2) (σ*α+2*a*σ*γ) (σ^2*γ)‖ := by
  rw [parabola_sum_rescale S z x a σ α γ hσ,norm_mul,sargos_character_norm,one_mul]

/-- One positive measure factor rescales every actual weighted moment.
No norm comparison, integrability condition or rescaled moment estimate is assumed. -/
theorem exists_parabolaWeightedBilinearMoment_rescale {ι τ : Type*}
    (a σ : ℝ) (hσ : σ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ℝ × ℝ → ℝ)
      (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
      (x : ι → ℝ) (y : τ → ℝ),
      parabolaWeightedBilinearMoment
        (fun p => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) S V z c
        (fun i => (x i-a)/σ) (fun j => (y j-a)/σ) =
      C*parabolaWeightedBilinearMoment W S V z c x y := by
  let e := parabolaRescaling a σ hσ
  obtain ⟨C,hC,hint⟩ := parabolaRescaling_integral (F := ℝ) e.symm
  refine ⟨C,hC,fun W S V z c x y => ?_⟩
  let f := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2 *
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^4
  have hnS (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z x (fun i => (x i)^2) (e.symm p).1 (e.symm p).2‖ =
        ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => ((x i-a)/σ)^2) p.1 p.2‖ := by
    have h := parabola_norm_rescale S z x a σ (e.symm p).1 (e.symm p).2 hσ
    change _ = ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
      (fun i => ((x i-a)/σ)^2) (e (e.symm p)).1 (e (e.symm p)).2‖ at h
    simpa only [e.apply_symm_apply] using h
  have hnV (p : ℝ × ℝ) :
      ‖sargosPlanarSum V c y (fun j => (y j)^2) (e.symm p).1 (e.symm p).2‖ =
        ‖sargosPlanarSum V c (fun j => (y j-a)/σ)
          (fun j => ((y j-a)/σ)^2) p.1 p.2‖ := by
    have h := parabola_norm_rescale V c y a σ (e.symm p).1 (e.symm p).2 hσ
    change _ = ‖sargosPlanarSum V c (fun j => (y j-a)/σ)
      (fun j => ((y j-a)/σ)^2) (e (e.symm p)).1 (e (e.symm p)).2‖ at h
    simpa only [e.apply_symm_apply] using h
  calc
    _ = ∫ p : ℝ × ℝ, f (e.symm p) := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [f]
      rw [hnS,hnV]
      rfl
    _ = _ := by
      simpa only [f,parabolaWeightedBilinearMoment,smul_eq_mul] using hint f

private theorem band_weighted_integrable {f : ℝ × ℝ → ℂ} {W : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hW : Integrable W) {M : ℝ} (hM : ∀ p, ‖f p‖ ≤ M) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*f p) := by
  have hw : Integrable (fun p : ℝ × ℝ => (W p : ℂ)) := hW.ofReal
  exact hw.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hM)

private theorem bandCross_integrable {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {W : ℝ × ℝ → ℝ} (hW : Integrable W) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hn (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z u v p.1 p.2*conj (sargosPlanarSum T z' u' v' p.1 p.2)‖ ≤
        (∑ i ∈ S, ‖z i‖)*(∑ j ∈ T, ‖z' j‖) := by
    rw [norm_mul,Complex.norm_conj]
    exact mul_le_mul (norm_sargosPlanarSum_le_sum_norm S z u v p.1 p.2)
      (norm_sargosPlanarSum_le_sum_norm T z' u' v' p.1 p.2)
      (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  simpa only [mul_assoc] using band_weighted_integrable hf hW hn

private theorem bandCharacter_integrable {W : ℝ × ℝ → ℝ} (hW : Integrable W)
    (u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (W p : ℂ)*fordAdditiveCharacter (u*p.1+v*p.2)) :=
  band_weighted_integrable (by unfold fordAdditiveCharacter; fun_prop) hW
    (fun p => (sargos_character_norm _).le)

private theorem integral_bandCross_zero {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (z' : κ → ℂ)
    (u v : ι → ℝ) (u' v' : κ → ℝ) {δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hgap : ∀ i ∈ S, ∀ j ∈ T, δ^2 ≤ parabolaBandGauge (u i-u' j) (v i-v' j)) :
    (∫ p : ℝ × ℝ, (W p : ℂ)*sargosPlanarSum S z u v p.1 p.2*
      conj (sargosPlanarSum T z' u' v' p.1 p.2)) = 0 := by
  simp_rw [rapidCross_expand]
  rw [integral_finsetSum (S ×ˢ T) (fun ij _ =>
    (bandCharacter_integrable hW.2.1 (u ij.1-u' ij.2) (v ij.1-v' ij.2)).const_mul _)]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [integral_const_mul,hW.2.2 _ _
    (hgap ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2),mul_zero]

private theorem parabola_band_sixth_gap
    {x x' y₁ y₂ y₃ y₄ w a β u ν δ : ℝ}
    (hw : 0 < w) (hν : 0 < ν) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : x ∈ Icc a (a+u)) (hx' : x' ∈ Icc a (a+u))
    (h₁ : y₁ ∈ Icc β (β+w)) (h₂ : y₂ ∈ Icc β (β+w))
    (h₃ : y₃ ∈ Icc β (β+w)) (h₄ : y₄ ∈ Icc β (β+w))
    (hgap : 2*w^2/ν ≤ |x-x'|) :
    δ^2 ≤ parabolaBandGauge (x+y₁+y₂-(x'+y₃+y₄))
      (x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2)) := by
  have hmem {v : ℝ} (hv : v ∈ Icc β (β+w)) : v-β ∈ Icc 0 w :=
    ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have hxp : x-β ∈ Icc (a-β) (a-β+u) :=
    ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hxp' : x'-β ∈ Icc (a-β) (a-β+u) :=
    ⟨by linarith [hx'.1],by linarith [hx'.2]⟩
  have hsep := parabola_same_interval_separation hν.le hu hd hxp hxp'
  have hgap' : (δ^2+2*w^2)/(4*ν) < |(x-β)-(x'-β)| := by
    rw [show (x-β)-(x'-β) = x-x' by ring]
    have hg := (div_le_iff₀ hν).mp hgap
    apply (div_lt_iff₀ (by positivity : 0 < 4*ν)).mpr
    nlinarith [sq_pos_of_pos hw]
  have hs := parabola_sixth_frequency_gap hw.le (by positivity : 0 < 4*ν)
    (hmem h₁) (hmem h₂) (hmem h₃) (hmem h₄) hsep hgap'
  have he : (x-β)^2+(y₁-β)^2+(y₂-β)^2-
      ((x'-β)^2+(y₃-β)^2+(y₄-β)^2) =
      (x^2+y₁^2+y₂^2-(x'^2+y₃^2+y₄^2))-2*β*(x+y₁+y₂-(x'+y₃+y₄)) := by ring
  rw [he] at hs
  exact hs.le.trans (parabolaBandGauge_slope_le hβ _ _)

/-- Finite bilinear localization for an actual rescaling-stable band weight.
Only literal interval membership, scale separation and Fourier support are
assumed; all moments and multiplicities are retained. -/
theorem parabolaWeightedBilinearMoment_localization_closed {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc a (a+u))
    (hy : ∀ k ∈ V, y k ∈ Icc β (β+w))
    (hblock : ∀ i ∈ J, ∀ k ∈ S i,
      x i k ∈ Icc (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) :
    parabolaWeightedBilinearMoment W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y ≤
      (7/ν)*∑ i ∈ J, parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
  classical
  let m := ⌈2/ν⌉₊
  have hm : 2/ν ≤ (m : ℝ) := Nat.le_ceil _
  have hceil : (m : ℝ) < 2/ν+1 := Nat.ceil_lt_add_one (by positivity)
  have hfac : 2*(m : ℝ)+1 ≤ 7/ν := by
    have hn := (lt_div_iff₀ hν).mp (show (m : ℝ)-1 < 2/ν by linarith)
    apply (le_div_iff₀ hν).mpr
    nlinarith
  let A := fun i : ℤ => (S i ×ˢ V) ×ˢ V
  let Z := fun i : ℤ => fun ij : (ι × τ) × τ => z i ij.1.1*c ij.1.2*c ij.2
  let X := fun i : ℤ => fun ij : (ι × τ) × τ => x i ij.1.1+y ij.1.2+y ij.2
  let Y := fun i : ℤ => fun ij : (ι × τ) × τ =>
    (x i ij.1.1)^2+(y ij.1.2)^2+(y ij.2)^2
  let F := fun i : ℤ => fun p : ℝ × ℝ => sargosPlanarSum (A i) (Z i) (X i) (Y i) p.1 p.2
  have hz : ∀ i ∈ J, ∀ j ∈ J, (m : ℤ) < |i-j| →
      (∫ p, (W p : ℂ)*F i p*conj (F j p)) = 0 := by
    intro i hi j hj hij
    apply integral_bandCross_zero _ _ _ _ _ _ _ _ hW
    intro a ha b hb
    have hal := Finset.mem_product.mp (Finset.mem_product.mp ha).1
    have har := (Finset.mem_product.mp ha).2
    have hbl := Finset.mem_product.mp (Finset.mem_product.mp hb).1
    have hbr := (Finset.mem_product.mp hb).2
    exact parabola_band_sixth_gap hw hν hβ hwidth hu hd
      (hx i hi _ hal.1) (hx j hj _ hbl.1)
      (hy _ hal.2) (hy _ har) (hy _ hbl.2) (hy _ hbr)
      (parabola_block_gap_closed hm (hblock i hi _ hal.1) (hblock j hj _ hbl.1) hij)
  have hmain := weighted_family_banded J F W m
    hW.1
    (fun i _ j _ => bandCross_integrable (A i) (A j) (Z i) (Z j)
      (X i) (Y i) (X j) (Y j) hW.2.1) hz
  have hsingle (i : ℤ) :
      (∫ p, W p*‖F i p‖^2) =
        parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
    unfold parabolaWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    dsimp [F,A,Z,X,Y]
    rw [parabola_product_sum,norm_mul,norm_pow]
    ring
  have htotal :
      (∫ p, W p*‖∑ i ∈ J, F i p‖^2) =
        parabolaWeightedBilinearMoment W (J.sigma S) V
          (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y := by
    unfold parabolaWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    have hs : (∑ i ∈ J, F i p) =
      sargosPlanarSum (J.sigma (fun i => (S i ×ˢ V) ×ˢ V))
        (fun ij => z ij.1 ij.2.1.1*c ij.2.1.2*c ij.2.2)
        (fun ij => x ij.1 ij.2.1.1+y ij.2.1.2+y ij.2.2)
        (fun ij => (x ij.1 ij.2.1.1)^2+(y ij.2.1.2)^2+(y ij.2.2)^2) p.1 p.2 := by
      simp only [F,A,Z,X,Y,sargosPlanarSum,Finset.sum_sigma]
    rw [hs,parabola_family_product_sum,norm_mul,norm_pow]
    ring
  simp_rw [hsingle] at hmain
  rw [htotal] at hmain
  refine hmain.trans (mul_le_mul_of_nonneg_right hfac ?_)
  apply Finset.sum_nonneg
  intro i hi
  rw [← hsingle]
  exact integral_nonneg (fun p => mul_nonneg (hW.1 p) (sq_nonneg _))

theorem parabolaWeightedBilinearMoment_localization {ι τ : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (V : Finset τ)
    (z : ℤ → ι → ℂ) (c : τ → ℂ)
    (x : ℤ → ι → ℝ) (y : τ → ℝ)
    {w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i ∈ J, ∀ k ∈ S i, x i k ∈ Icc a (a+u))
    (hy : ∀ k ∈ V, y k ∈ Icc β (β+w))
    (hblock : ∀ i ∈ J, ∀ k ∈ S i,
      x i k ∈ Ico (a+w^2*(i : ℝ)) (a+w^2*((i : ℝ)+1))) :
    parabolaWeightedBilinearMoment W (J.sigma S) V
      (fun ij => z ij.1 ij.2) c (fun ij => x ij.1 ij.2) y ≤
      (7/ν)*∑ i ∈ J, parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
  exact parabolaWeightedBilinearMoment_localization_closed J S V z c x y
    hW hw hν hν₁ hβ hwidth hu hd hx hy
    (fun i hi k hk => Ico_subset_Icc_self (hblock i hi k hk))

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025
open MeasureTheory Set
open scoped BigOperators

private theorem weighted_integral_cauchy_square
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {W P Q : α → ℝ}
    (hW : ∀ x, 0 ≤ W x)
    (hPP : Integrable (fun x => W x*(P x)^2) μ)
    (hPQ : Integrable (fun x => W x*P x*Q x) μ)
    (hQQ : Integrable (fun x => W x*(Q x)^2) μ) :
    (∫ x, W x*P x*Q x ∂μ)^2 ≤
      (∫ x, W x*(P x)^2 ∂μ)*(∫ x, W x*(Q x)^2 ∂μ) := by
  have hquad (a : ℝ) :
      0 ≤ (∫ x, W x*(P x)^2 ∂μ)*(a*a) +
        (-2*(∫ x, W x*P x*Q x ∂μ))*a +
        (∫ x, W x*(Q x)^2 ∂μ) := by
    have heq (x : α) : W x*(a*P x-Q x)^2 =
        a^2*(W x*(P x)^2) - (2*a)*(W x*P x*Q x) + W x*(Q x)^2 := by ring
    have hp : 0 ≤ ∫ x, W x*(a*P x-Q x)^2 ∂μ :=
      integral_nonneg (fun x => mul_nonneg (hW x) (sq_nonneg _))
    simp_rw [heq] at hp
    have hA : Integrable (fun x => a^2*(W x*(P x)^2)) μ := hPP.const_mul _
    have hB : Integrable (fun x => (2*a)*(W x*P x*Q x)) μ := hPQ.const_mul _
    have hAB : Integrable (fun x => a^2*(W x*(P x)^2)-(2*a)*(W x*P x*Q x)) μ := hA.sub hB
    rw [integral_add hAB hQQ,
      integral_sub hA hB,
      integral_const_mul,integral_const_mul] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

/-- The actual squared Hölder swap for the asymmetric sixth moment.
Every weighted integral is derived from the finite sums, not supplied. -/
theorem parabolaWeightedBilinearMoment_holder_swap {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    (parabolaWeightedBilinearMoment W S V z c x y)^2 ≤
      parabolaWeightedBilinearMoment W V S c z y x *
        parabolaWeightedBilinearMoment W V V c c y y := by
  let P := fun p : ℝ × ℝ => ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
    ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖
  let Q := fun p : ℝ × ℝ => ‖sargosPlanarSum V c y (fun j => (y j)^2) p.1 p.2‖^3
  have hePP (p : ℝ × ℝ) :
      W p*(P p)^2 = W p*parabolaMomentFunction V S c z y x p := by
    dsimp [P,parabolaMomentFunction]
    ring
  have hePQ (p : ℝ × ℝ) :
      W p*P p*Q p = W p*parabolaMomentFunction S V z c x y p := by
    dsimp [P,Q,parabolaMomentFunction]
    ring
  have heQQ (p : ℝ × ℝ) :
      W p*(Q p)^2 = W p*parabolaMomentFunction V V c c y y p := by
    dsimp [Q,parabolaMomentFunction]
    ring
  have hPP : Integrable (fun p => W p*(P p)^2) := by
    exact (parabolaMomentFunction_integrable V S c z y x hW).congr
      (Filter.Eventually.of_forall (fun p => (hePP p).symm))
  have hPQ : Integrable (fun p => W p*P p*Q p) := by
    exact (parabolaMomentFunction_integrable S V z c x y hW).congr
      (Filter.Eventually.of_forall (fun p => (hePQ p).symm))
  have hQQ : Integrable (fun p => W p*(Q p)^2) := by
    exact (parabolaMomentFunction_integrable V V c c y y hW).congr
      (Filter.Eventually.of_forall (fun p => (heQQ p).symm))
  have h := weighted_integral_cauchy_square (W := W) (P := P) (Q := Q)
    hW₀ hPP hPQ hQQ
  simp_rw [hePP,hePQ,heQQ] at h
  simpa only [parabolaMomentFunction,parabolaWeightedBilinearMoment,mul_assoc] using h


theorem parabolaSourceBilinearMoment_holder_swap {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) {R : ℝ} (hR : 0 < R) (r t : ℝ) :
    (parabolaSourceBilinearMoment S V z c x y R r t)^2 ≤
      parabolaSourceBilinearMoment V S c z y x R r t *
        parabolaSourceBilinearMoment V V c c y y R r t := by
  exact parabolaWeightedBilinearMoment_holder_swap
    (fun p => parabolaSourceWeight R r t p.1 p.2)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
    (integrable_parabolaSourceWeight hR r t) S V z c x y


/-- The actual weighted L6 norm of the finite parabola sum. -/
def parabolaWeightedSixNorm {ι : Type*} (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) : ℝ :=
  lpNorm (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2)
    6 (volume.withDensity (fun p => ENNReal.ofReal (W p)))

private theorem parabolaWeighted_memLp {ι : Type*} {W : ℝ × ℝ → ℝ}
    (hW : Integrable W) (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    MemLp (fun p : ℝ × ℝ => sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2)
      6 (volume.withDensity (fun p => ENNReal.ofReal (W p))) := by
  letI := isFiniteMeasure_withDensity_ofReal hW.2
  have hc : Continuous (fun p : ℝ × ℝ =>
      sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  exact MemLp.of_bound hc.aestronglyMeasurable (∑ i ∈ S, ‖z i‖)
    (Filter.Eventually.of_forall fun p =>
      norm_sargosPlanarSum_le_sum_norm S z x (fun i => (x i)^2) p.1 p.2)

theorem parabolaWeightedSixNorm_nonneg {ι : Type*} (W : ℝ × ℝ → ℝ)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    0 ≤ parabolaWeightedSixNorm W S z x := lpNorm_nonneg

theorem parabolaWeightedSixNorm_pow_six {ι : Type*} (W : ℝ × ℝ → ℝ)
    (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (parabolaWeightedSixNorm W S z x)^6 =
      parabolaWeightedBilinearMoment W S S z z x x := by
  unfold parabolaWeightedSixNorm
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    (parabolaWeighted_memLp hW S z x).aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, show (6:ℝ) = ((6:ℕ):ℝ) from rfl,
    Real.rpow_natCast]
  simp only [one_div]
  have hroot (m : ℝ) (hm : 0 ≤ m) : (m^((6:ℝ)⁻¹))^6 = m := by
    simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hm (by norm_num : (6:ℕ) ≠ 0)
  rw [hroot _ (integral_nonneg fun _ => by positivity)]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hW.1.aemeasurable.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold parabolaWeightedBilinearMoment
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    rw [ENNReal.toReal_ofReal (hW₀ p)]
    dsimp only [smul_eq_mul]
    norm_num only [Real.rpow_ofNat]
    ring

theorem parabolaWeightedSixNorm_sum_le {κ ι : Type*} (J : Finset κ)
    (S : κ → Finset ι) (z : κ → ι → ℂ) (x : κ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW : Integrable W) :
    parabolaWeightedSixNorm W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2) ≤
        ∑ i ∈ J, parabolaWeightedSixNorm W (S i) (z i) (x i) := by
  unfold parabolaWeightedSixNorm
  have he : (fun p : ℝ × ℝ =>
      sargosPlanarSum (J.sigma S) (fun ij => z ij.1 ij.2)
        (fun ij => x ij.1 ij.2) (fun ij => (x ij.1 ij.2)^2) p.1 p.2) =
      ∑ i ∈ J, fun p : ℝ × ℝ =>
        sargosPlanarSum (S i) (z i) (x i) (fun k => (x i k)^2) p.1 p.2 := by
    ext p
    simp only [sargosPlanarSum,Finset.sum_sigma,Finset.sum_apply]
  rw [he]
  exact lpNorm_sum_le (fun i _ => parabolaWeighted_memLp hW (S i) (z i) (x i))
    (by norm_num)

theorem parabolaWeightedSixNorm_sq_le_card {κ ι : Type*} (J : Finset κ)
    (S : κ → Finset ι) (z : κ → ι → ℂ) (x : κ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW : Integrable W) :
    (parabolaWeightedSixNorm W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^2 ≤
        (J.card:ℝ)*∑ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^2 := by
  calc
    _ ≤ (∑ i ∈ J, parabolaWeightedSixNorm W (S i) (z i) (x i))^2 := by
      exact pow_le_pow_left₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
        (parabolaWeightedSixNorm_sum_le J S z x W hW) 2
    _ ≤ _ := sq_sum_le_card_mul_sum_sq

theorem parabolaWeightedBilinearMoment_le_sixNorm {ι τ : Type*}
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (x : ι → ℝ) (y : τ → ℝ) :
    parabolaWeightedBilinearMoment W S V z c x y ≤
      (parabolaWeightedSixNorm W S z x)^2*(parabolaWeightedSixNorm W V c y)^4 := by
  let M := parabolaWeightedBilinearMoment W S V z c x y
  let N := parabolaWeightedBilinearMoment W V S c z y x
  let A := parabolaWeightedSixNorm W S z x
  let B := parabolaWeightedSixNorm W V c y
  have hM : 0 ≤ M := integral_nonneg fun p => by
    exact mul_nonneg (mul_nonneg (hW₀ p) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hA : 0 ≤ A := parabolaWeightedSixNorm_nonneg _ _ _ _
  have hB : 0 ≤ B := parabolaWeightedSixNorm_nonneg _ _ _ _
  have hMN : M^2 ≤ N*B^6 := by
    simpa only [M,N,A,B,parabolaWeightedSixNorm_pow_six W hW₀ hW] using
      parabolaWeightedBilinearMoment_holder_swap W hW₀ hW S V z c x y
  have hNM : N^2 ≤ M*A^6 := by
    simpa only [M,N,A,B,parabolaWeightedSixNorm_pow_six W hW₀ hW] using
      parabolaWeightedBilinearMoment_holder_swap W hW₀ hW V S c z y x
  have hfour : M^4 ≤ M*A^6*B^12 := by
    calc
      M^4 = (M^2)^2 := by ring
      _ ≤ (N*B^6)^2 := pow_le_pow_left₀ (sq_nonneg M) hMN 2
      _ = N^2*B^12 := by ring
      _ ≤ M*A^6*B^12 := mul_le_mul_of_nonneg_right hNM (pow_nonneg hB 12)
  change M ≤ A^2*B^4
  by_cases hz : M = 0
  · rw [hz]
    positivity
  have hMp := lt_of_le_of_ne hM (Ne.symm hz)
  have hcube : M^3 ≤ (A^2*B^4)^3 := by
    apply (mul_le_mul_iff_right₀ hMp).mp
    nlinarith only [hfour]
  exact (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (3:ℕ) ≠ 0)).mp hcube

universe u

/-- One positive factor acts on every finite weighted L6 norm at the rescaled coordinates. -/
theorem exists_parabolaWeightedSixNorm_rescale (a σ : ℝ) (hσ : σ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ι : Type u) (W : ℝ × ℝ → ℝ),
      (∀ p, 0 ≤ W p) → Integrable W →
      ∀ (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      parabolaWeightedSixNorm
        (fun p => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)) S z (fun i => (x i-a)/σ) =
        C*parabolaWeightedSixNorm W S z x := by
  let e := parabolaRescaling a σ hσ
  obtain ⟨d,hd,hint⟩ := parabolaRescaling_integral (F:=ℝ) e.symm
  let C := d^((6:ℝ)⁻¹)
  have hC : 0 < C := Real.rpow_pos_of_pos hd _
  have hCpow : C^6 = d := by
    simpa only [C,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hd.le (by norm_num : (6:ℕ) ≠ 0)
  refine ⟨C,hC,fun ι W hW₀ hW S z x => ?_⟩
  let W' : ℝ × ℝ → ℝ := fun p => W (e.symm p)
  have hW' : Integrable W' := parabolaRescaling_integrable e.symm hW
  have hW'₀ : ∀ p, 0 ≤ W' p := fun p => hW₀ (e.symm p)
  change parabolaWeightedSixNorm W' S z (fun i => (x i-a)/σ) =
    C*parabolaWeightedSixNorm W S z x
  apply (pow_left_inj₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
    (mul_nonneg hC.le (parabolaWeightedSixNorm_nonneg _ _ _ _))
    (by norm_num : (6:ℕ) ≠ 0)).mp
  rw [parabolaWeightedSixNorm_pow_six W' hW'₀ hW',mul_pow,hCpow,
    parabolaWeightedSixNorm_pow_six W hW₀ hW]
  let f := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
    ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^4
  have hn (p : ℝ × ℝ) :
      ‖sargosPlanarSum S z x (fun i => (x i)^2) (e.symm p).1 (e.symm p).2‖ =
        ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
          (fun i => ((x i-a)/σ)^2) p.1 p.2‖ := by
    have h := parabola_norm_rescale S z x a σ (e.symm p).1 (e.symm p).2 hσ
    change _ = ‖sargosPlanarSum S z (fun i => (x i-a)/σ)
      (fun i => ((x i-a)/σ)^2) (e (e.symm p)).1 (e (e.symm p)).2‖ at h
    simpa only [e.apply_symm_apply] using h
  calc
    _ = ∫ p : ℝ × ℝ, f (e.symm p) := by
      apply integral_congr_ae
      filter_upwards with p
      dsimp only [f,parabolaWeightedBilinearMoment]
      rw [hn]
    _ = _ := by
      simpa only [f,parabolaWeightedBilinearMoment,smul_eq_mul] using hint f

/-- The actual finite weighted L6 decoupling contract at a uniform n-cell grid.
This definition is a bound to be proved; it is not analytic provenance. -/
def ParabolaDecouplingBound (n : ℕ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (ι : Type u) (W : ℝ × ℝ → ℝ), ParabolaWeightBand (1/(n:ℝ)) W →
    ∀ (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ),
      (∀ j, ∀ k ∈ S j, x j k ∈ Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ))) →
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
        D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2

theorem parabolaDecouplingBound_trivial (n : ℕ) :
    ParabolaDecouplingBound.{u} n (Real.sqrt n) := by
  refine ⟨Real.sqrt_nonneg _,fun ι W hW S z x _ => ?_⟩
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa only [Finset.card_univ,Fintype.card_fin] using
    parabolaWeightedSixNorm_sq_le_card Finset.univ S z x W hW.2.1

/-- Actual subinterval rescaling consumes the unit-grid bound at n cells.
The same positive Haar factor multiplies all cells and the full sum, then cancels. -/
theorem ParabolaDecouplingBound.rescale {n : ℕ} {D a σ : ℝ}
    (hD : ParabolaDecouplingBound.{u} n D) (hσ : 0 < σ)
    (ha : 0 ≤ a) (haσ : a+σ ≤ 1)
    (ι : Type u) (W : ℝ × ℝ → ℝ) (hW : ParabolaWeightBand (σ/(n:ℝ)) W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k ∈ S j,
      x j k ∈ Icc (a+σ*((j:ℕ)/(n:ℝ))) (a+σ*(((j:ℕ)+1)/(n:ℝ)))) :
    (parabolaWeightedSixNorm W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
      D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2 := by
  let W' : ℝ × ℝ → ℝ := fun p => W (p.1/σ-2*a*p.2/σ^2,p.2/σ^2)
  have hW' : ParabolaWeightBand (1/(n:ℝ)) W' := by
    have he : (σ/(n:ℝ))/σ = 1/(n:ℝ) := by
      rw [div_right_comm,div_self hσ.ne']
    simpa only [he,W'] using hW.rescale hσ ha haσ
  have hx' (j : Fin n) (k : ι) (hk : k ∈ S j) :
      (x j k-a)/σ ∈ Icc ((j:ℕ)/(n:ℝ)) (((j:ℕ)+1)/(n:ℝ)) := by
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hx j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hx j k hk).2]
  have h := hD.2 ι W' hW' S z (fun j k => (x j k-a)/σ) hx'
  obtain ⟨C,hC,hscale⟩ := exists_parabolaWeightedSixNorm_rescale.{u} a σ hσ.ne'
  have ht := hscale (Sigma fun _ : Fin n => ι) W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have hi (j : Fin n) := hscale ι W hW.1 hW.2.1 (S j) (z j) (x j)
  change parabolaWeightedSixNorm W' _ _ _ = _ at ht
  change ∀ j, parabolaWeightedSixNorm W' _ _ _ = _ at hi
  rw [ht] at h
  simp_rw [hi,mul_pow] at h
  rw [← Finset.mul_sum] at h
  have hC₂ : 0 < C^2 := sq_pos_of_pos hC
  apply (mul_le_mul_iff_right₀ hC₂).mp
  nlinarith only [h]


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem add_sixth_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a+b)^6 ≤ 64*(a^6+b^6) := by
  rcases le_total a b with h | h
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a+b)
      (show a+b ≤ 2*b by linarith) 6
    nlinarith only [hs,pow_nonneg ha 6]
  · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ a+b)
      (show a+b ≤ 2*a by linarith) 6
    nlinarith only [hs,pow_nonneg hb 6]

private theorem parabola_near_card (J : Finset ℤ) (i : ℤ) :
    ((J.filter (fun j => |i-j| ≤ 3)).card : ℝ) ≤ 7 := by
  have hs : J.filter (fun j => |i-j| ≤ 3) ⊆ Finset.Icc (i-3) (i+3) := by
    intro j hj
    have hh := abs_le.mp (Finset.mem_filter.mp hj).2
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  have hc : (J.filter (fun j => |i-j| ≤ 3)).card ≤ 7 := by
    calc
      _ ≤ (Finset.Icc (i-3) (i+3)).card := Finset.card_le_card hs
      _ = 7 := by rw [Int.card_Icc]; omega
  exact_mod_cast hc

theorem parabola_bilinear_reduction_pointwise (J : Finset ℤ) (f : ℤ → ℂ) :
    ‖∑ i ∈ J, f i‖^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, ‖f i‖^6 +
      64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖f j‖^2*‖f i‖^4 := by
  classical
  rcases J.eq_empty_or_nonempty with rfl | hJ
  · simp
  obtain ⟨i,hi,hmax⟩ := J.exists_max_image (fun j => ‖f j‖) hJ
  let K := J.filter (fun j => |i-j| ≤ 3)
  let L := J.filter (fun j => 3 < |i-j|)
  let A := ∑ j ∈ K, ‖f j‖
  let B := ∑ j ∈ L, ‖f j‖
  let M := ‖f i‖
  let n := (J.card:ℝ)
  have hM : 0 ≤ M := norm_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hK : (K.card:ℝ) ≤ 7 := parabola_near_card J i
  have hL : (L.card:ℝ) ≤ n := by
    dsimp only [L,n]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun j => 3 < |i-j|) J)
  have hnear : A ≤ 7*M := by
    calc
      A ≤ ∑ _j ∈ K, M := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
      _ = (K.card:ℝ)*M := by simp
      _ ≤ 7*M := mul_le_mul_of_nonneg_right hK hM
  have hfar : B ≤ n*M := by
    calc
      B ≤ ∑ _j ∈ L, M := Finset.sum_le_sum fun j hj => hmax j (Finset.mem_filter.mp hj).1
      _ = (L.card:ℝ)*M := by simp
      _ ≤ n*M := mul_le_mul_of_nonneg_right hL hM
  have hfar₂ : B^2 ≤ n*∑ j ∈ L, ‖f j‖^2 :=
    (sq_sum_le_card_mul_sum_sq (s:=L) (f:=fun j => ‖f j‖)).trans
      (mul_le_mul_of_nonneg_right hL (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hfar₆ : B^6 ≤ n^5*∑ j ∈ L, ‖f j‖^2*M^4 := by
    calc
      B^6 = B^4*B^2 := by ring
      _ ≤ (n*M)^4*(n*∑ j ∈ L, ‖f j‖^2) :=
        mul_le_mul (pow_le_pow_left₀ hB hfar 4) hfar₂ (sq_nonneg B) (by positivity)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hdiag : M^6 ≤ ∑ j ∈ J, ‖f j‖^6 :=
    Finset.single_le_sum (fun j _ => pow_nonneg (norm_nonneg _) 6) hi
  have hcross : (∑ j ∈ L, ‖f j‖^2*M^4) ≤
      ∑ k ∈ J, ∑ j ∈ J.filter (fun j => 3 < |k-j|), ‖f j‖^2*‖f k‖^4 :=
by
    dsimp only [L,M]
    exact Finset.single_le_sum (f := fun k =>
      ∑ j ∈ J.filter (fun j => 3 < |k-j|), ‖f j‖^2*‖f k‖^4)
      (fun k _ => Finset.sum_nonneg fun j _ => by positivity) hi
  have hsplit : (∑ j ∈ J, ‖f j‖) = A+B := by
    dsimp [A,B,K,L]
    simpa only [not_le] using
      (Finset.sum_filter_add_sum_filter_not J (fun j => |i-j| ≤ 3) (fun j => ‖f j‖)).symm
  have hsum : ‖∑ j ∈ J, f j‖ ≤ A+B := by
    rw [← hsplit]
    exact norm_sum_le _ _
  have hnear₆ : A^6 ≤ 7^6*M^6 := by
    simpa only [mul_pow] using pow_le_pow_left₀ hA hnear 6
  calc
    _ ≤ (A+B)^6 := pow_le_pow_left₀ (norm_nonneg _) hsum 6
    _ ≤ 64*(A^6+B^6) := add_sixth_le A B hA hB
    _ ≤ 64*(7^6*M^6+n^5*∑ j ∈ L, ‖f j‖^2*M^4) := by
      gcongr
    _ ≤ _ := by
      dsimp only [n]
      have hd := mul_le_mul_of_nonneg_left hdiag (by positivity : (0:ℝ) ≤ 64*7^6)
      have hc := mul_le_mul_of_nonneg_left hcross (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
      nlinarith only [hd,hc]

theorem parabolaWeightedSixNorm_bilinear_reduction {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W) :
    (parabolaWeightedSixNorm W (J.sigma S) (fun ij => z ij.1 ij.2)
      (fun ij => x ij.1 ij.2))^6 ≤
      (64*7^6:ℝ)*∑ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^6 +
      64*(J.card:ℝ)^5*∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
        parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i) := by
  classical
  let F := fun i => fun p : ℝ × ℝ =>
    sargosPlanarSum (S i) (z i) (x i) (fun k => (x i k)^2) p.1 p.2
  let G := fun i j => fun p : ℝ × ℝ => W p*‖F i p‖^2*‖F j p‖^4
  let T := J.sigma S
  let Z := fun ij : (i : ℤ) × ι => z ij.1 ij.2
  let X := fun ij : (i : ℤ) × ι => x ij.1 ij.2
  let H := fun p : ℝ × ℝ => W p*
    ‖sargosPlanarSum T Z X (fun ij => (X ij)^2) p.1 p.2‖^2*
    ‖sargosPlanarSum T Z X (fun ij => (X ij)^2) p.1 p.2‖^4
  have hG (i j : ℤ) : Integrable (G i j) := by
    simpa only [G,F,parabolaMomentFunction,mul_assoc] using
      parabolaMomentFunction_integrable (S i) (S j) (z i) (z j) (x i) (x j) hW
  have hH : Integrable H := by
    simpa only [H,parabolaMomentFunction,mul_assoc] using
      parabolaMomentFunction_integrable T T Z Z X X hW
  have hs (p : ℝ × ℝ) :
      sargosPlanarSum T Z X (fun ij => (X ij)^2) p.1 p.2 = ∑ i ∈ J, F i p := by
    simp only [T,Z,X,F,sargosPlanarSum,Finset.sum_sigma]
  have hpoint (p : ℝ × ℝ) :
      H p ≤ (64*7^6:ℝ)*(∑ i ∈ J, G i i p) +
        64*(J.card:ℝ)^5*(∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) := by
    have hp := mul_le_mul_of_nonneg_left
      (parabola_bilinear_reduction_pointwise J (fun i => F i p)) (hW₀ p)
    have he (v : ℂ) : ‖v‖^6 = ‖v‖^2*‖v‖^4 := by ring
    dsimp only [H]
    rw [hs]
    simp_rw [he] at hp
    have hd : W p*((64*7^6:ℝ)*∑ i ∈ J, ‖F i p‖^2*‖F i p‖^4) =
        (64*7^6:ℝ)*∑ i ∈ J, G i i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc,Finset.mul_sum]
      simp only [G,mul_assoc]
    have hc : W p*(64*(J.card:ℝ)^5*
        ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), ‖F j p‖^2*‖F i p‖^4) =
        64*(J.card:ℝ)^5*
          ∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p := by
      rw [← mul_assoc,mul_comm (W p),mul_assoc]
      simp only [Finset.mul_sum,G,mul_assoc]
    rw [mul_add,hd,hc] at hp
    simpa only [mul_assoc] using hp
  have hdiag : Integrable (fun p => ∑ i ∈ J, G i i p) :=
    integrable_finsetSum J (fun i _ => hG i i)
  have hcross : Integrable (fun p => ∑ i ∈ J,
      ∑ j ∈ J.filter (fun j => 3 < |i-j|), G j i p) :=
    integrable_finsetSum J (fun i _ =>
      integrable_finsetSum _ (fun j _ => hG j i))
  have h := integral_mono hH
    ((hdiag.const_mul (64*7^6:ℝ)).add (hcross.const_mul (64*(J.card:ℝ)^5))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hdiag.const_mul _) (hcross.const_mul _),
    integral_const_mul,integral_const_mul,
    integral_finsetSum J (fun i _ => hG i i),
    integral_finsetSum J (fun i _ => integrable_finsetSum _ (fun j _ => hG j i))] at h
  simp_rw [integral_finsetSum _ (fun j _ => hG j _)] at h
  simpa only [parabolaWeightedSixNorm_pow_six W hW₀ hW,
    parabolaWeightedBilinearMoment,H,T,Z,X,G,F] using h


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem parabolaWeightBand_mono {δ η : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W) (h : δ^2 ≤ η^2) : ParabolaWeightBand η W :=
  ⟨hW.1,hW.2.1,fun ξ κ hg => hW.2.2 ξ κ (h.trans hg)⟩

private theorem finGrid_sum {k l : ℕ} {A : Type*} [AddCommMonoid A]
    (f : Fin (k*l) → A) :
    ∑ r, f r = ∑ i : Fin k, ∑ j : Fin l, f (finProdFinEquiv (i,j)) := by
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp finProdFinEquiv f).symm

private theorem finGrid_cell {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (i : Fin k) (j : Fin l) :
    ((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*((j:ℕ)/(l:ℝ)) ∧
    (((finProdFinEquiv (i,j) : Fin (k*l)):ℕ)+1)/(k*l:ℝ) =
      (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((j:ℕ)+1)/(l:ℝ)) := by
  have hk' : (k:ℝ) ≠ 0 := by positivity
  have hl' : (l:ℝ) ≠ 0 := by positivity
  simp only [finProdFinEquiv,Equiv.coe_fn_mk,Nat.cast_add,Nat.cast_mul]
  constructor <;> field_simp <;> ring

/-- Composing genuine coarse and fine grid estimates proves the product-grid bound. -/
theorem ParabolaDecouplingBound.mul {k l : ℕ} {A B : ℝ}
    (hk : 0 < k) (hl : 0 < l)
    (hA : ParabolaDecouplingBound.{u} k A) (hB : ParabolaDecouplingBound.{u} l B) :
    ParabolaDecouplingBound.{u} (k*l) (A*B) := by
  refine ⟨mul_nonneg hA.1 hB.1,fun ι W hW S z x hx => ?_⟩
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let Z := fun i : Fin k => fun jk : (j : Fin l) × ι => z (e (i,jk.1)) jk.2
  let X := fun i : Fin k => fun jk : (j : Fin l) × ι => x (e (i,jk.1)) jk.2
  have hk' : (0:ℝ) < k := by positivity
  have hl' : (0:ℝ) < l := by positivity
  have hwidth : 1/((k*l:ℕ):ℝ) = (1/(k:ℝ))/(l:ℝ) := by
    rw [Nat.cast_mul,div_div]
  have hsmall : 1/((k*l:ℕ):ℝ) ≤ 1/(k:ℝ) := by
    apply one_div_le_one_div_of_le hk'
    have hl₁ : (1:ℝ) ≤ l := by exact_mod_cast hl
    rw [Nat.cast_mul]
    nlinarith
  have hWk : ParabolaWeightBand (1/(k:ℝ)) W :=
    parabolaWeightBand_mono hW (pow_le_pow_left₀ (by positivity) hsmall 2)
  have hfine (i : Fin k) (j : Fin l) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc
        ((i:ℕ)/(k:ℝ)+(1/(k:ℝ))*((j:ℕ)/(l:ℝ)))
        ((i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((j:ℕ)+1)/(l:ℝ))) := by
    have h := hx (e (i,j)) v hv
    simpa only [Nat.cast_mul,(finGrid_cell hk hl i j).1,
      (finGrid_cell hk hl i j).2,e] using h
  have hcoarse (i : Fin k) (v : (j : Fin l) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc ((i:ℕ)/(k:ℝ)) (((i:ℕ)+1)/(k:ℝ)) := by
    have hf := hfine i v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ)+1)/(l:ℝ) ≤ 1 := by
      apply (div_le_iff₀ hl').mpr
      simpa only [one_mul] using (show ((v.1:ℕ):ℝ)+1 ≤ l by exact_mod_cast v.1.isLt)
    have hz : 0 ≤ (v.1:ℕ)/(l:ℝ) := by positivity
    have hp : 0 ≤ 1/(k:ℝ) := by positivity
    change x (e (i,v.1)) v.2 ∈ _
    constructor
    · nlinarith [hf.1,mul_nonneg hp hz]
    · have hu := mul_le_mul_of_nonneg_left hj hp
      have he : (((i:ℕ):ℝ)+1)/(k:ℝ) = (i:ℕ)/(k:ℝ)+1/(k:ℝ) := by ring
      rw [he]
      nlinarith [hf.2]
  have h := hA.2 ((j : Fin l) × ι) W hWk T Z X hcoarse
  have hpart (i : Fin k) :
      (parabolaWeightedSixNorm W (T i) (Z i) (X i))^2 ≤
        B^2*∑ j : Fin l,
          (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2 := by
    apply hB.rescale (a := (i:ℕ)/(k:ℝ)) (σ := 1/(k:ℝ))
      (by positivity) (by positivity) ?_ ι W
      (by simpa only [hwidth] using hW)
      (fun j => S (e (i,j))) (fun j => z (e (i,j))) (fun j => x (e (i,j)))
      (hfine i)
    rw [← add_div]
    apply (div_le_iff₀ hk').mpr
    have hi : ((i:ℕ):ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    simpa only [one_mul,← add_div] using hi
  have htotal :
      parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun rv => z rv.1 rv.2) (fun rv => x rv.1 rv.2) =
      parabolaWeightedSixNorm W (Finset.univ.sigma T)
        (fun iv => Z iv.1 iv.2) (fun iv => X iv.1 iv.2) := by
    unfold parabolaWeightedSixNorm
    congr 1
    funext p
    simp only [sargosPlanarSum,Finset.sum_sigma,T,Z,X]
    exact finGrid_sum _
  rw [htotal]
  refine h.trans ?_
  have hp := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpart i)
  have hm := mul_le_mul_of_nonneg_left hp (sq_nonneg A)
  rw [← Finset.mul_sum] at hm
  have he := finGrid_sum (fun r =>
    (parabolaWeightedSixNorm W (S r) (z r) (x r))^2)
  rw [he]
  nlinarith only [hm]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The actual asymmetric sixth-moment grid bound. K is the sixth-power
constant. Separation is between whole closed intervals, so subdivision preserves it. -/
def ParabolaBilinearSixBound (δ : ℝ) (p q : ℕ) (ν K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (ι τ : Type u) (W : ℝ × ℝ → ℝ), ParabolaWeightBand δ W →
    ∀ (a b : ℝ), 0 ≤ a → a+δ*p ≤ 1 → 0 ≤ b → b+δ*q ≤ 1 →
      (a+δ*p+3*ν ≤ b ∨ b+δ*q+3*ν ≤ a) →
      ∀ (S : Fin p → Finset ι) (V : Fin q → Finset τ)
        (z : Fin p → ι → ℂ) (c : Fin q → τ → ℂ)
        (x : Fin p → ι → ℝ) (y : Fin q → τ → ℝ),
      (∀ j, ∀ k ∈ S j, x j k ∈ Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) →
      (∀ j, ∀ k ∈ V j, y j k ∈ Icc (b+δ*(j:ℕ)) (b+δ*((j:ℕ)+1))) →
      parabolaWeightedBilinearMoment W (Finset.univ.sigma S) (Finset.univ.sigma V)
        (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
        (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2) ≤
          K*(∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2)*
            (∑ j, (parabolaWeightedSixNorm W (V j) (c j) (y j))^2)^2

private theorem parabola_grid_rescale_bound {n : ℕ} {D δ a : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hD : ParabolaDecouplingBound.{u} n D)
    (ha : 0 ≤ a) (haδ : a+δ*n ≤ 1)
    (ι : Type u) (W : ℝ × ℝ → ℝ) (hW : ParabolaWeightBand δ W)
    (S : Fin n → Finset ι) (z : Fin n → ι → ℂ) (x : Fin n → ι → ℝ)
    (hx : ∀ j, ∀ k ∈ S j, x j k ∈ Icc (a+δ*(j:ℕ)) (a+δ*((j:ℕ)+1))) :
    (parabolaWeightedSixNorm W (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^2 ≤
      D^2*∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2 := by
  have hn' : (n:ℝ) ≠ 0 := by positivity
  apply hD.rescale (a:=a) (σ:=δ*n) (by positivity) ha haδ ι W
    (by simpa only [mul_div_cancel_right₀ _ hn'] using hW) S z x
  intro j k hk
  have h := hx j k hk
  have hleft : δ*n*((j:ℕ)/(n:ℝ)) = δ*(j:ℕ) := by field_simp
  have hright : δ*n*(((j:ℕ)+1)/(n:ℝ)) = δ*((j:ℕ)+1) := by field_simp
  simpa only [hleft,hright] using h

/-- Rescaled genuine linear bounds control the actual asymmetric moment. -/
theorem parabolaBilinearSixBound_of_linear {p q : ℕ} {δ ν A B : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ)
    (hA : ParabolaDecouplingBound.{u} p A) (hB : ParabolaDecouplingBound.{u} q B) :
    ParabolaBilinearSixBound.{u} δ p q ν (A^2*B^4) := by
  refine ⟨by positivity,fun ι τ W hW a b ha haδ hb hbδ _ S V z c x y hx hy => ?_⟩
  have hS := parabola_grid_rescale_bound hp hδ hA ha haδ ι W hW S z x hx
  have hV := parabola_grid_rescale_bound hq hδ hB hb hbδ τ W hW V c y hy
  have hm := parabolaWeightedBilinearMoment_le_sixNorm W hW.1 hW.2.1
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  refine hm.trans ?_
  have hV₂ := pow_le_pow_left₀ (sq_nonneg _) hV 2
  have hs := mul_le_mul hS hV₂ (sq_nonneg _) (by positivity)
  convert hs using 1 <;> ring

theorem parabolaBilinearSixBound_trivial {p q : ℕ} {δ ν : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hδ : 0 < δ) :
    ParabolaBilinearSixBound.{u} δ p q ν ((p:ℝ)*(q:ℝ)^2) := by
  have h := parabolaBilinearSixBound_of_linear (ν:=ν) hp hq hδ
    (parabolaDecouplingBound_trivial.{u} p) (parabolaDecouplingBound_trivial.{u} q)
  have he : (Real.sqrt (p:ℝ))^2*(Real.sqrt (q:ℝ))^4 = (p:ℝ)*(q:ℝ)^2 := by
    rw [show (Real.sqrt (q:ℝ))^4 = ((Real.sqrt (q:ℝ))^2)^2 by ring,
      Real.sq_sqrt (Nat.cast_nonneg p),Real.sq_sqrt (Nat.cast_nonneg q)]
  simpa only [he] using h

/-- The asymmetric recurrence uses the swapped, narrower moment bound and
the actual secondary-interval linear estimate. -/
theorem ParabolaBilinearSixBound.holder_swap {p q : ℕ} {δ ν K B : ℝ}
    (hq : 0 < q) (hδ : 0 < δ)
    (hK : ParabolaBilinearSixBound.{u} δ q p ν K)
    (hB : ParabolaDecouplingBound.{u} q B) :
    ParabolaBilinearSixBound.{u} δ p q ν (Real.sqrt K*B^3) := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hB.1 3),
    fun ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  let ES := ∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2
  let EV := ∑ j, (parabolaWeightedSixNorm W (V j) (c j) (y j))^2
  let M := parabolaWeightedBilinearMoment W (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  let N := parabolaWeightedBilinearMoment W (Finset.univ.sigma V) (Finset.univ.sigma S)
    (fun jk => c jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => y jk.1 jk.2) (fun jk => x jk.1 jk.2)
  let Q := parabolaWeightedSixNorm W (Finset.univ.sigma V)
    (fun jk => c jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hES : 0 ≤ ES := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEV : 0 ≤ EV := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM : 0 ≤ M := integral_nonneg fun r =>
    mul_nonneg (mul_nonneg (hW.1 r) (sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hN : N ≤ K*EV*ES^2 :=
    hK.2 τ ι W hW b a hb hbδ ha haδ hsep.symm V S c z y x hy hx
  have hQ : Q^2 ≤ B^2*EV :=
    parabola_grid_rescale_bound hq hδ hB hb hbδ τ W hW V c y hy
  have hMN : M^2 ≤ N*Q^6 := by
    simpa only [M,N,Q,parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1] using
      parabolaWeightedBilinearMoment_holder_swap W hW.1 hW.2.1
        (Finset.univ.sigma S) (Finset.univ.sigma V)
        (fun jk => z jk.1 jk.2) (fun jk => c jk.1 jk.2)
        (fun jk => x jk.1 jk.2) (fun jk => y jk.1 jk.2)
  have hQ₆ : Q^6 ≤ B^6*EV^3 := by
    convert pow_le_pow_left₀ (sq_nonneg Q) hQ 3 using 1 <;> ring
  have hprod := mul_le_mul hN hQ₆ (by positivity : 0 ≤ Q^6)
    (mul_nonneg (mul_nonneg hK.1 hEV) (sq_nonneg ES))
  have he : (Real.sqrt K*B^3*ES*EV^2)^2 = (K*EV*ES^2)*(B^6*EV^3) := by
    rw [show (Real.sqrt K*B^3*ES*EV^2)^2 =
      (Real.sqrt K)^2*B^6*ES^2*EV^4 by ring,Real.sq_sqrt hK.1]
    ring
  have hB₀ := hB.1
  change M ≤ Real.sqrt K*B^3*ES*EV^2
  apply (pow_le_pow_iff_left₀ hM (by positivity) (by norm_num : (2:ℕ) ≠ 0)).mp
  rw [he]
  exact hMN.trans hprod


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private def parabolaIntGridIndex (k : ℕ) (hk : 0 < k) (i : ℤ) : Fin k :=
  ⟨i.toNat % k,Nat.mod_lt _ hk⟩

private theorem parabolaIntGridIndex_cast {k : ℕ} (hk : 0 < k) (i : Fin k) :
    parabolaIntGridIndex k hk (i:ℕ) = i := by
  apply Fin.ext
  simp [parabolaIntGridIndex,Nat.mod_eq_of_lt i.isLt]

private theorem parabolaIntGridIndex_val {k : ℕ} (hk : 0 < k) {i : ℤ}
    (hi : i ∈ Finset.Ico 0 (k:ℤ)) :
    ((parabolaIntGridIndex k hk i : Fin k):ℕ) = i.toNat := by
  have hh := Finset.mem_Ico.mp hi
  simp only [parabolaIntGridIndex]
  exact Nat.mod_eq_of_lt (by omega)

private theorem parabola_intGrid_sum {k : ℕ} (hk : 0 < k)
    {A : Type*} [AddCommMonoid A] (f : Fin k → A) :
    ∑ i ∈ Finset.Ico 0 (k:ℤ), f (parabolaIntGridIndex k hk i) = ∑ j, f j := by
  classical
  symm
  refine Finset.sum_bij (fun j _ => (j:ℤ)) ?_ ?_ ?_ ?_
  · intro j _
    dsimp only
    apply Finset.mem_Ico.mpr
    constructor
    · exact_mod_cast (Nat.zero_le (j:ℕ))
    · exact_mod_cast j.isLt
  · intro i _ j _ h
    dsimp only at h
    apply Fin.ext
    exact_mod_cast h
  · intro i hi
    have hh := Finset.mem_Ico.mp hi
    refine ⟨⟨i.toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rw [parabolaIntGridIndex_cast]

private theorem parabolaWeightedBilinearMoment_fin_localization {k : ℕ}
    (hk : 0 < k) {ι τ : Type*}
    (S : Fin k → Finset ι) (V : Finset τ)
    (z : Fin k → ι → ℂ) (c : τ → ℂ) (x : Fin k → ι → ℝ) (y : τ → ℝ)
    {w a β u ν δ : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : ParabolaWeightBand δ W)
    (hw : 0 < w) (hν : 0 < ν) (hν₁ : ν ≤ 1) (hβ : β ∈ Icc 0 1)
    (hwidth : δ^2 ≤ w^2) (hu : u ≤ ν) (hd : 3*ν ≤ |a-β|)
    (hx : ∀ i, ∀ v ∈ S i, x i v ∈ Icc a (a+u))
    (hy : ∀ v ∈ V, y v ∈ Icc β (β+w))
    (hblock : ∀ i, ∀ v ∈ S i,
      x i v ∈ Icc (a+w^2*(i:ℕ)) (a+w^2*((i:ℕ)+1))) :
    parabolaWeightedBilinearMoment W (Finset.univ.sigma S) V
      (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y ≤
      (7/ν)*∑ i, parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y := by
  let R := parabolaIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := parabolaIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have h := parabolaWeightedBilinearMoment_localization_closed J
    (fun i => S (R i)) V (fun i => z (R i)) c (fun i => x (R i)) y
    hW hw hν hν₁ hβ hwidth hu hd
    (fun i _ => hx (R i)) hy (fun i hi v hv => by
      simpa only [hR i hi] using hblock (R i) v hv)
  have he (α γ : ℝ) :
      sargosPlanarSum (J.sigma (fun i => S (R i)))
        (fun iv => z (R iv.1) iv.2) (fun iv => x (R iv.1) iv.2)
        (fun iv => (x (R iv.1) iv.2)^2) α γ =
      sargosPlanarSum (Finset.univ.sigma S) (fun iv => z iv.1 iv.2)
        (fun iv => x iv.1 iv.2) (fun iv => (x iv.1 iv.2)^2) α γ := by
    simp only [sargosPlanarSum,Finset.sum_sigma]
    exact parabola_intGrid_sum hk (fun i => ∑ v ∈ S i,
      z i v*fordAdditiveCharacter (x i v*α+(x i v)^2*γ))
  have hm : parabolaWeightedBilinearMoment W (J.sigma (fun i => S (R i))) V
      (fun iv => z (R iv.1) iv.2) c (fun iv => x (R iv.1) iv.2) y =
      parabolaWeightedBilinearMoment W (Finset.univ.sigma S) V
        (fun iv => z iv.1 iv.2) c (fun iv => x iv.1 iv.2) y := by
    unfold parabolaWeightedBilinearMoment
    simp_rw [he]
  rw [hm] at h
  have hsum := parabola_intGrid_sum hk (fun i =>
    parabolaWeightedBilinearMoment W (S i) V (z i) c (x i) y)
  change (∑ i ∈ J, parabolaWeightedBilinearMoment W (S (R i)) V (z (R i)) c (x (R i)) y) = _ at hsum
  rw [hsum] at h
  exact h

universe u

/-- Localization at the linked square scale consumes the smaller primary-grid
bound. The whole-interval separation and all original coefficients are retained. -/
theorem ParabolaBilinearSixBound.localization {k m q : ℕ} {δ ν K : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : ParabolaBilinearSixBound.{u} δ m q ν K) :
    ParabolaBilinearSixBound.{u} δ (k*m) q ν ((7/ν)*K) := by
  refine ⟨mul_nonneg (by positivity) hK.1,
    fun ι τ W hW a b ha haδ hb hbδ hsep S V z c x y hx hy => ?_⟩
  simp only [Nat.cast_mul] at haδ hsep
  let e : Fin k × Fin m ≃ Fin (k*m) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin m => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin m) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin m) × ι => x (e (i,jv.1)) jv.2
  let U := Finset.univ.sigma V
  let C := fun jv : (j : Fin q) × τ => c jv.1 jv.2
  let Y := fun jv : (j : Fin q) × τ => y jv.1 jv.2
  let ai := fun i : Fin k => a+δ*m*(i:ℕ)
  have heval (i : Fin k) (j : Fin m) :
      ((e (i,j):Fin (k*m)):ℝ) = (j:ℕ)+(m:ℝ)*(i:ℕ) := by
    simp [e,finProdFinEquiv,Nat.cast_add,Nat.cast_mul]
  have hai (i : Fin k) : a ≤ ai i ∧ ai i+δ*m ≤ a+δ*(k*m) := by
    have hi : ((i:ℕ):ℝ)+1 ≤ k := by exact_mod_cast i.isLt
    have hp := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ δ*m)
    have hzero : 0 ≤ δ*m*(i:ℕ) := by positivity
    dsimp only [ai]
    constructor
    · linarith
    · nlinarith only [hp]
  have hfine (i : Fin k) (j : Fin m) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have hf := hx (e (i,j)) v hv
    change x (e (i,j)) v ∈ Icc (a+δ*((e (i,j):Fin (k*m)):ℝ))
      (a+δ*(((e (i,j):Fin (k*m)):ℝ)+1)) at hf
    rw [heval] at hf
    dsimp only [ai]
    constructor <;> nlinarith [hf.1,hf.2]
  have hblock (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc (ai i) (ai i+δ*m) := by
    have hf := hfine i v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ m := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [X] <;> nlinarith [hf.1,hf.2]
  have hglobal (i : Fin k) (v : (j : Fin m) × ι) (hv : v ∈ T i) :
      X i v ∈ Icc a (a+δ*(k*m)) :=
    ⟨(hai i).1.trans (hblock i v hv).1,(hblock i v hv).2.trans (hai i).2⟩
  have hsecondary (v : (j : Fin q) × τ) (hv : v ∈ U) :
      Y v ∈ Icc b (b+δ*q) := by
    have hf := hy v.1 v.2 (Finset.mem_sigma.mp hv).2
    have hj : ((v.1:ℕ):ℝ)+1 ≤ q := by exact_mod_cast v.1.isLt
    have hp := mul_le_mul_of_nonneg_left hj hδ.le
    have hn : 0 ≤ δ*(v.1:ℕ) := by positivity
    constructor <;> dsimp only [Y] <;> nlinarith [hf.1,hf.2]
  have hd : 3*ν ≤ |a-b| := by
    rcases hsep with hs | hs
    · have hz : 0 ≤ δ*(k*m) := by positivity
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hz : 0 ≤ δ*q := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hq₁ : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hwidth : δ^2 ≤ (δ*q)^2 :=
    pow_le_pow_left₀ hδ.le (by nlinarith) 2
  have hloc := parabolaWeightedBilinearMoment_fin_localization hk T U Z C X Y
    hW (by positivity : 0 < δ*q) hν hν₁
    (show b ∈ Icc 0 1 from ⟨hb,by nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg q)]⟩)
    hwidth hsmall hd hglobal hsecondary (fun i v hv => by
      have h := hblock i v hv
      dsimp only [ai] at h
      simpa only [← hscale,mul_add,mul_one,mul_assoc,add_assoc] using h)

  let EV := ∑ j, (parabolaWeightedSixNorm W (V j) (c j) (y j))^2
  have hpiece (i : Fin k) :
      parabolaWeightedBilinearMoment W (T i) U (Z i) C (X i) Y ≤
        K*(∑ j : Fin m,
          (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2 := by
    have hsep' : ai i+δ*m+3*ν ≤ b ∨ b+δ*q+3*ν ≤ ai i := by
      rcases hsep with hs | hs
      · exact Or.inl (by linarith [(hai i).2])
      · exact Or.inr (by linarith [(hai i).1])
    exact hK.2 ι τ W hW (ai i) b (ha.trans (hai i).1) ((hai i).2.trans haδ)
      hb hbδ hsep' (fun j => S (e (i,j))) V (fun j => z (e (i,j))) c
      (fun j => x (e (i,j))) y (hfine i) hy
  have ht :
      parabolaWeightedBilinearMoment W (Finset.univ.sigma S) U
        (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y =
      parabolaWeightedBilinearMoment W (Finset.univ.sigma T) U
        (fun iv => Z iv.1 iv.2) C (fun iv => X iv.1 iv.2) Y := by
    unfold parabolaWeightedBilinearMoment
    apply integral_congr_ae
    filter_upwards with r
    have he :
        sargosPlanarSum (Finset.univ.sigma S) (fun rv => z rv.1 rv.2)
          (fun rv => x rv.1 rv.2) (fun rv => (x rv.1 rv.2)^2) r.1 r.2 =
        sargosPlanarSum (Finset.univ.sigma T) (fun iv => Z iv.1 iv.2)
          (fun iv => X iv.1 iv.2) (fun iv => (X iv.1 iv.2)^2) r.1 r.2 := by
      simp only [sargosPlanarSum,Finset.sum_sigma,T,Z,X]
      exact finGrid_sum _
    rw [he]
  change parabolaWeightedBilinearMoment W (Finset.univ.sigma S) U
    (fun rv => z rv.1 rv.2) C (fun rv => x rv.1 rv.2) Y ≤ _
  rw [ht]
  refine hloc.trans ?_
  have hp := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpiece i)
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 7/ν)
  have he : (∑ i : Fin k, K*(∑ j : Fin m,
      (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2)*EV^2) =
      K*(∑ r, (parabolaWeightedSixNorm W (S r) (z r) (x r))^2)*EV^2 := by
    rw [← Finset.sum_mul,← Finset.mul_sum,finGrid_sum]
  rw [he] at hp'
  simpa only [EV,mul_assoc] using hp'

/-- The linked localization/Holder step consumes the genuinely swapped
smaller-grid bound, rather than the original interval conclusion. -/
theorem ParabolaBilinearSixBound.localization_holder {k m q : ℕ} {δ ν K B : ℝ}
    (hk : 0 < k) (hq : 0 < q) (hδ : 0 < δ) (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hsmall : δ*(k*m) ≤ ν) (hscale : δ*m = (δ*q)^2)
    (hK : ParabolaBilinearSixBound.{u} δ q m ν K)
    (hB : ParabolaDecouplingBound.{u} q B) :
    ParabolaBilinearSixBound.{u} δ (k*m) q ν ((7/ν)*(Real.sqrt K*B^3)) :=
  (hK.holder_swap hq hδ hB).localization hk hq hδ hν hν₁ hsmall hscale


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem sum_nonneg_powers_le {ι : Type*} (J : Finset ι) (E : ι → ℝ)
    (hE : ∀ i ∈ J, 0 ≤ E i) {n : ℕ} (hn : n ≠ 0) :
    ∑ i ∈ J, (E i)^n ≤ (∑ i ∈ J, E i)^n := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [zero_pow hn]
  | @insert a J ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    have hJ : ∀ i ∈ J, 0 ≤ E i := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    calc
      E a^n+(∑ i ∈ J, (E i)^n) ≤ E a^n+(∑ i ∈ J, E i)^n :=
        add_le_add le_rfl (ih hJ)
      _ ≤ _ := pow_add_pow_le (hE a (Finset.mem_insert_self a J))
        (Finset.sum_nonneg hJ) hn

private theorem parabolaWeightedSixNorm_bilinear_budget {ι : Type*}
    (J : Finset ℤ) (S : ℤ → Finset ι) (z : ℤ → ι → ℂ) (x : ℤ → ι → ℝ)
    (W : ℝ × ℝ → ℝ) (hW₀ : ∀ p, 0 ≤ W p) (hW : Integrable W)
    (E : ℤ → ℝ) (A K : ℝ) (hE : ∀ i ∈ J, 0 ≤ E i) (hK : 0 ≤ K)
    (hdiag : ∀ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^2 ≤ A^2*E i)
    (hfar : ∀ i ∈ J, ∀ j ∈ J, 3 < |i-j| →
      parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i) ≤ K*E j*(E i)^2) :
    (parabolaWeightedSixNorm W (J.sigma S)
      (fun iv => z iv.1 iv.2) (fun iv => x iv.1 iv.2))^6 ≤
      ((64*7^6:ℝ)*A^6+64*(J.card:ℝ)^5*K)*(∑ i ∈ J, E i)^3 := by
  have hmain := parabolaWeightedSixNorm_bilinear_reduction J S z x W hW₀ hW
  have hds : (∑ i ∈ J, (parabolaWeightedSixNorm W (S i) (z i) (x i))^6) ≤
      A^6*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, A^6*(E i)^3 := by
        apply Finset.sum_le_sum
        intro i hi
        convert pow_le_pow_left₀ (sq_nonneg _) (hdiag i hi) 3 using 1 <;> ring
      _ = A^6*∑ i ∈ J, (E i)^3 := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_nonneg_powers_le J E hE (by norm_num : (3:ℕ) ≠ 0)) (by positivity)
  have hc (i : ℤ) (hi : i ∈ J) :
      (∑ j ∈ J.filter (fun j => 3 < |i-j|),
        parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ j ∈ J, E j)*(E i)^2 := by
    calc
      _ ≤ ∑ j ∈ J.filter (fun j => 3 < |i-j|), K*E j*(E i)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        exact hfar i hi j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
      _ ≤ ∑ j ∈ J, K*E j*(E i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j hj _ => mul_nonneg (mul_nonneg hK (hE j hj)) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]
  have hcs : (∑ i ∈ J, ∑ j ∈ J.filter (fun j => 3 < |i-j|),
      parabolaWeightedBilinearMoment W (S j) (S i) (z j) (z i) (x j) (x i)) ≤
      K*(∑ i ∈ J, E i)^3 := by
    calc
      _ ≤ ∑ i ∈ J, K*(∑ j ∈ J, E j)*(E i)^2 := Finset.sum_le_sum hc
      _ = (K*(∑ j ∈ J, E j))*∑ i ∈ J, (E i)^2 := (Finset.mul_sum ..).symm
      _ ≤ (K*(∑ j ∈ J, E j))*(∑ i ∈ J, E i)^2 :=
        mul_le_mul_of_nonneg_left
          (sum_nonneg_powers_le J E hE (by norm_num : (2:ℕ) ≠ 0))
          (mul_nonneg hK (Finset.sum_nonneg hE))
      _ = _ := by ring
  have hd := mul_le_mul_of_nonneg_left hds (by positivity : (0:ℝ) ≤ 64*7^6)
  have hf := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 64*(J.card:ℝ)^5)
  nlinarith only [hmain,hd,hf]

private theorem parabola_sixth_budget_to_square {L E A K k : ℝ}
    (hE : 0 ≤ E) (hA : 0 ≤ A) (hK : 0 ≤ K) (hk : 1 ≤ k)
    (h : L^6 ≤ ((64*7^6:ℝ)*A^6+64*k^5*K)*E^3) :
    L^2 ≤ (14*A+2*k*K^((6:ℝ)⁻¹))^2*E := by
  let R := K^((6:ℝ)⁻¹)
  have hR : 0 ≤ R := Real.rpow_nonneg hK _
  have hR₆ : R^6 = K := by
    simpa only [R,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hK (by norm_num : (6:ℕ) ≠ 0)
  have hk₀ : 0 ≤ k := by linarith
  have hkp : k^5 ≤ k^6 := by
    have hp := mul_le_mul_of_nonneg_left hk (pow_nonneg hk₀ 5)
    simpa only [mul_one,← pow_succ] using hp
  have hab := pow_add_pow_le (by positivity : 0 ≤ 14*A)
    (by positivity : 0 ≤ 2*k*R) (by norm_num : (6:ℕ) ≠ 0)
  have hb : (64*7^6:ℝ)*A^6+64*k^5*K ≤ (14*A+2*k*R)^6 := by
    have he : (14*A)^6+(2*k*R)^6 = (64*7^6:ℝ)*A^6+64*k^6*K := by
      rw [mul_pow, mul_pow, mul_pow,hR₆]
      ring
    rw [he] at hab
    have hp := mul_le_mul_of_nonneg_right hkp (mul_nonneg (by norm_num : (0:ℝ) ≤ 64) hK)
    nlinarith only [hab,hp]
  have hc := h.trans (mul_le_mul_of_nonneg_right hb (pow_nonneg hE 3))
  apply (pow_le_pow_iff_left₀ (sq_nonneg L) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  change (L^2)^3 ≤ ((14*A+2*k*R)^2*E)^3
  convert hc using 1 <;> ring

universe u

set_option maxHeartbeats 1000000 in
/-- The genuine coarse/fine grid and whole-interval bilinear contracts imply
the linear bound, with an explicit constant and no target-grid assumption. -/
theorem ParabolaDecouplingBound.of_bilinear {k l : ℕ} {A K : ℝ}
    (hk : 0 < k) (hl : 0 < l) (hA : ParabolaDecouplingBound.{u} l A)
    (hK : ParabolaBilinearSixBound.{u} (1/((k*l:ℕ):ℝ)) l l (1/(k:ℝ)) K) :
    ParabolaDecouplingBound.{u} (k*l) (14*A+2*k*K^((6:ℝ)⁻¹)) := by
  have hA₀ := hA.1
  have hK₀ := hK.1
  refine ⟨by positivity,fun ι W hW S z x hx => ?_⟩
  let δ : ℝ := 1/((k*l:ℕ):ℝ)
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let Z := fun i : Fin k => fun jv : (j : Fin l) × ι => z (e (i,jv.1)) jv.2
  let X := fun i : Fin k => fun jv : (j : Fin l) × ι => x (e (i,jv.1)) jv.2
  let E := fun i : Fin k => ∑ j : Fin l,
    (parabolaWeightedSixNorm W (S (e (i,j))) (z (e (i,j))) (x (e (i,j))))^2
  let ai := fun i : Fin k => (i:ℕ)/(k:ℝ)
  let R := parabolaIntGridIndex k hk
  let J := Finset.Ico 0 (k:ℤ)
  have hk' : (0:ℝ) < k := by positivity
  have hl' : (0:ℝ) < l := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδl : δ*l = 1/(k:ℝ) := by
    dsimp [δ]
    push_cast
    field_simp
  have hfine (i : Fin k) (j : Fin l) (v : ι) (hv : v ∈ S (e (i,j))) :
      x (e (i,j)) v ∈ Icc (ai i+δ*(j:ℕ)) (ai i+δ*((j:ℕ)+1)) := by
    have h := hx (e (i,j)) v hv
    simp only [Nat.cast_mul] at h
    have hcell := finGrid_cell hk hl i j
    change x (e (i,j)) v ∈ Icc
      (((e (i,j):Fin (k*l)):ℝ)/(k*l:ℝ))
      ((((e (i,j):Fin (k*l)):ℝ)+1)/(k*l:ℝ)) at h
    rw [hcell.1,hcell.2] at h
    convert h using 1
    dsimp [ai,δ]
    push_cast
    field_simp
  have hai (i : Fin k) : 0 ≤ ai i := by dsimp [ai]; positivity
  have htop (i : Fin k) : ai i+δ*l ≤ 1 := by
    rw [hδl]
    dsimp only [ai]
    rw [← add_div]
    apply (div_le_iff₀ hk').mpr
    simpa only [one_mul] using
      (show ((i:ℕ):ℝ)+1 ≤ k by exact_mod_cast i.isLt)
  have hlin (i : Fin k) :
      (parabolaWeightedSixNorm W (T i) (Z i) (X i))^2 ≤ A^2*E i :=
    parabola_grid_rescale_bound hl hδ hA (hai i) (htop i) ι W hW
      (fun j => S (e (i,j))) (fun j => z (e (i,j))) (fun j => x (e (i,j))) (hfine i)
  have hR (i : ℤ) (hi : i ∈ J) : ((R i:Fin k):ℝ) = (i:ℝ) := by
    have hv := parabolaIntGridIndex_val hk hi
    have hn : 0 ≤ i := (Finset.mem_Ico.mp hi).1
    change (((R i:Fin k):ℕ):ℝ) = _
    rw [hv]
    exact_mod_cast Int.toNat_of_nonneg hn
  have hfar (i : ℤ) (hi : i ∈ J) (j : ℤ) (hj : j ∈ J) (hij : 3 < |i-j|) :
      parabolaWeightedBilinearMoment W (T (R j)) (T (R i))
        (Z (R j)) (Z (R i)) (X (R j)) (X (R i)) ≤ K*E (R j)*(E (R i))^2 := by
    have hsep : ai (R j)+δ*l+3*(1/(k:ℝ)) ≤ ai (R i) ∨
        ai (R i)+δ*l+3*(1/(k:ℝ)) ≤ ai (R j) := by
      dsimp only [ai]
      rw [hδl,hR i hi,hR j hj]
      rcases le_total i j with h | h
      · right
        have hh : i+4 ≤ j := by
          rw [abs_of_nonpos (sub_nonpos.mpr h)] at hij
          omega
        have hh' : (i:ℝ)+4 ≤ j := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
      · left
        have hh : j+4 ≤ i := by
          rw [abs_of_nonneg (sub_nonneg.mpr h)] at hij
          omega
        have hh' : (j:ℝ)+4 ≤ i := by exact_mod_cast hh
        convert div_le_div_of_nonneg_right hh' hk'.le using 1
        ring
    exact hK.2 ι ι W hW (ai (R j)) (ai (R i)) (hai _) (htop _) (hai _) (htop _) hsep
      (fun v => S (e (R j,v))) (fun v => S (e (R i,v)))
      (fun v => z (e (R j,v))) (fun v => z (e (R i,v)))
      (fun v => x (e (R j,v))) (fun v => x (e (R i,v))) (hfine (R j)) (hfine (R i))

  have hE : ∀ i ∈ J, 0 ≤ E (R i) := fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hbudget := parabolaWeightedSixNorm_bilinear_budget J
    (fun i => T (R i)) (fun i => Z (R i)) (fun i => X (R i)) W hW.1 hW.2.1
    (fun i => E (R i)) A K hE hK.1 (fun i _ => hlin (R i)) hfar
  have hcard : (J.card:ℝ) = k := by simp [J,Int.card_Ico]
  rw [hcard] at hbudget
  have hsq := parabola_sixth_budget_to_square (Finset.sum_nonneg hE) hA.1 hK.1
    (show (1:ℝ) ≤ k by exact_mod_cast hk) hbudget
  have hsum : (∑ i ∈ J, E (R i)) =
      ∑ r, (parabolaWeightedSixNorm W (S r) (z r) (x r))^2 := by
    calc
      _ = ∑ i : Fin k, E i := parabola_intGrid_sum hk E
      _ = _ := by
        dsimp only [E,e]
        exact (finGrid_sum (fun r => (parabolaWeightedSixNorm W (S r) (z r) (x r))^2)).symm
  rw [hsum] at hsq
  have htotal :
      parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun rv => z rv.1 rv.2) (fun rv => x rv.1 rv.2) =
      parabolaWeightedSixNorm W (J.sigma (fun i => T (R i)))
        (fun iv => Z (R iv.1) iv.2) (fun iv => X (R iv.1) iv.2) := by
    unfold parabolaWeightedSixNorm
    congr 1
    funext r
    simp only [sargosPlanarSum,Finset.sum_sigma]
    have hs := parabola_intGrid_sum hk (fun i => ∑ v ∈ T i,
      Z i v*fordAdditiveCharacter (X i v*r.1+(X i v)^2*r.2))
    rw [hs]
    simp only [T,Z,X,Finset.sum_sigma]
    exact finGrid_sum _
  rw [htotal]
  exact hsq

/-- Exact dyadic specialization of the genuine linear/bilinear comparison. -/
theorem ParabolaDecouplingBound.of_bilinear_dyadic {n r : ℕ} {A K : ℝ}
    (hr : r ≤ n) (hA : ParabolaDecouplingBound.{u} (2^(n-r)) A)
    (hK : ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-r)) (2^(n-r)) (1/(2:ℝ)^r) K) :
    ParabolaDecouplingBound.{u} (2^n) (14*A+2*(2:ℝ)^r*K^((6:ℝ)⁻¹)) := by
  have hcount : (2:ℕ)^r*2^(n-r) = 2^n := by
    rw [← pow_add]
    congr 1
    omega
  have hK' : ParabolaBilinearSixBound.{u} (1/(((2:ℕ)^r*2^(n-r):ℕ):ℝ))
      (2^(n-r)) (2^(n-r)) (1/((2^r:ℕ):ℝ)) K := by
    simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using hK
  have h := ParabolaDecouplingBound.of_bilinear
    (by positivity : 0 < (2:ℕ)^r) (by positivity : 0 < (2:ℕ)^(n-r)) hA hK'
  simpa only [hcount,Nat.cast_pow,Nat.cast_ofNat] using h


end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem dyadic_width_mul_cells {a n : ℕ} (ha : a ≤ n) :
    (1/(2:ℝ)^n)*(2:ℝ)^(n-a) = 1/(2:ℝ)^a := by
  rw [pow_sub₀ (2:ℝ) (by norm_num) ha]
  field_simp

private theorem dyadic_width_sq (b : ℕ) :
    (1/(2:ℝ)^b)^2 = 1/(2:ℝ)^(2*b) := by
  rw [div_pow,one_pow,← pow_mul]
  congr 2
  omega

/-- The actual square-scale recurrence on exact dyadic grids. -/
theorem ParabolaBilinearSixBound.dyadic_step {n a b r : ℕ} {K B : ℝ}
    (ha : a ≤ 2*b) (hb : 2*b ≤ n) (hr : r ≤ a)
    (hK : ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-b)) (2^(n-2*b)) (1/(2:ℝ)^r) K)
    (hB : ParabolaDecouplingBound.{u} (2^(n-b)) B) :
    ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n)
      (2^(n-a)) (2^(n-b)) (1/(2:ℝ)^r)
      ((7/(1/(2:ℝ)^r))*(Real.sqrt K*B^3)) := by
  have hcount : (2:ℕ)^(2*b-a)*2^(n-2*b) = 2^(n-a) := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : (1/(2:ℝ)^n)*((2:ℕ)^(2*b-a)*(2:ℕ)^(n-2*b)) ≤ 1/(2:ℝ)^r := by
    push_cast
    rw [← pow_add,show (2*b-a)+(n-2*b) = n-a by omega,
      dyadic_width_mul_cells (ha.trans hb)]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr)
  have hscale : (1/(2:ℝ)^n)*(((2:ℕ)^(n-2*b):ℕ):ℝ) =
      ((1/(2:ℝ)^n)*(((2:ℕ)^(n-b):ℕ):ℝ))^2 := by
    push_cast
    rw [dyadic_width_mul_cells hb,dyadic_width_mul_cells (by omega : b ≤ n),
      dyadic_width_sq]
  have hν₁ : 1/(2:ℝ)^r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^r)).mpr
    simpa only [one_mul] using one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n:=r)
  have h := hK.localization_holder (k:=2^(2*b-a)) (by positivity) (by positivity)
    (by positivity) (by positivity) hν₁ (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsmall) hscale hB
  simpa only [hcount] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The literal constants produced by finitely iterating the actual bilinear process. -/
def parabolaDyadicBilinearBudget (D : ℕ → ℝ) (n r : ℕ) : ℕ → ℕ → ℕ → ℝ
  | 0,a,b => (D (n-a))^2*(D (n-b))^4
  | t+1,_,b => (7/(1/(2:ℝ)^r))*
      (Real.sqrt (parabolaDyadicBilinearBudget D n r t b (2*b))*(D (n-b))^3)

/-- Iteration only uses linear estimates at grid exponents strictly below n. -/
theorem parabolaBilinearSixBound_dyadic_iterate (D : ℕ → ℝ)
    {n r a b t : ℕ} (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (hb : b*2^t ≤ n)
    (hD : ∀ j < n, ParabolaDecouplingBound.{u} (2^j) (D j)) :
    ParabolaBilinearSixBound.{u} (1/(2:ℝ)^n) (2^(n-a)) (2^(n-b))
      (1/(2:ℝ)^r) (parabolaDyadicBilinearBudget D n r t a b) := by
  induction t generalizing a b with
  | zero =>
    simp only [pow_zero,mul_one] at hb
    exact parabolaBilinearSixBound_of_linear (by positivity) (by positivity)
      (by positivity) (hD (n-a) (by omega)) (hD (n-b) (by omega))
  | succ t ih =>
    have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^t = b*2^(t+1) := by rw [pow_succ]; ring
    have hnext : (2*b)*2^t ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^t by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (Nat.zero_le (2*b))).trans hnext
    have hprev := ih (hra.trans hab) (by omega : b ≤ 2*b) hnext
    have h := hprev.dyadic_step (a:=a) (by omega) hb₂ hra (hD (n-b) (by omega))
    simpa only [parabolaDyadicBilinearBudget] using h

/-- The actual iterated linear estimate is obtained from strictly smaller grids.
This finite theorem is not yet the numerical epsilon-loss bound. -/
theorem parabolaDecouplingBound_dyadic_iterate (D : ℕ → ℝ)
    {n r t : ℕ} (hr : 0 < r) (hn : r*2^t ≤ n)
    (hD : ∀ j < n, ParabolaDecouplingBound.{u} (2^j) (D j)) :
    ParabolaDecouplingBound.{u} (2^n)
      (14*D (n-r)+2*(2:ℝ)^r*
        (parabolaDyadicBilinearBudget D n r t r r)^((6:ℝ)⁻¹)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  exact ParabolaDecouplingBound.of_bilinear_dyadic hrn (hD (n-r) (by omega))
    (parabolaBilinearSixBound_dyadic_iterate D hr le_rfl le_rfl hn hD)

end TaoTrudgianYang2025

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem two_rpow_product (C x y : ℝ) (m k : ℕ) :
    (C*(2:ℝ)^x)^m*(C*(2:ℝ)^y)^k =
      C^(m+k)*(2:ℝ)^(x*m+y*k) := by
  rw [Real.rpow_add (by norm_num), Real.rpow_mul_natCast (by norm_num),
    Real.rpow_mul_natCast (by norm_num), pow_add]
  ring

/-- An explicit numerical bound for the actual finite bilinear recurrence. -/
theorem parabolaDyadicBilinearBudget_exponential {C ε : ℝ} (hC : 0 ≤ C)
    {n r a b t : ℕ} (ht : 1 ≤ t) (hb : b*2^t ≤ n) :
    parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t a b ≤
      49*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*b+2*r) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le ht
  induction s generalizing a b with
  | zero =>
    have hb₂ : 2*b ≤ n := by simpa [mul_comm] using hb
    have hb₁ : b ≤ n := by omega
    have hx : 0 ≤ C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)) := by positivity
    have hy : 0 ≤ C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)) := by positivity
    simp only [Nat.add_zero,parabolaDyadicBilinearBudget]
    rw [show (C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))^2*
        (C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)))^4 =
        ((C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))*
          (C*(2:ℝ)^(ε*((n-2*b:ℕ):ℝ)))^2)^2 by ring,
      Real.sqrt_sq (by positivity)]
    have hp := two_rpow_product C (ε*((n-b:ℕ):ℝ))
      (ε*((n-2*b:ℕ):ℝ)) 4 2
    simp only [Nat.cast_sub hb₁,Nat.cast_sub hb₂,Nat.cast_mul,Nat.cast_ofNat] at hp ⊢
    have he : (ε*((n:ℝ)-b))*4+(ε*((n:ℝ)-2*b))*2 =
        6*ε*n-8*ε*b := by ring
    norm_num only [show (4+2:ℕ)=6 by omega] at hp
    rw [he] at hp
    have hmain :
        7/(1/(2:ℝ)^r)*
          (C*(2:ℝ)^(ε*((n:ℝ)-b))*
            (C*(2:ℝ)^(ε*((n:ℝ)-2*b)))^2*
              (C*(2:ℝ)^(ε*((n:ℝ)-b)))^3) =
        7*(2:ℝ)^r*(C^6*(2:ℝ)^(6*ε*n-8*ε*b)) := by
      rw [div_div_eq_mul_div,div_one]
      calc
        _ = 7*(2:ℝ)^r*((C*(2:ℝ)^(ε*((n:ℝ)-b)))^4*
          (C*(2:ℝ)^(ε*((n:ℝ)-2*b)))^2) := by ring
        _ = _ := by rw [hp]
    rw [hmain]
    have hrpow : (2:ℝ)^r ≤ (2:ℝ)^(2*(r:ℝ)) := by
      rw [←Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith)
    have he' : 6*ε*n-(3*(1:ℝ)+5)*ε*b+2*r =
        (6*ε*n-8*ε*b)+2*r := by ring
    simp only [Nat.cast_one]
    rw [he',Real.rpow_add (by norm_num)]
    have hmul := mul_le_mul_of_nonneg_right hrpow
      (show 0 ≤ C^6*(2:ℝ)^(6*ε*n-8*ε*b) by positivity)
    nlinarith [mul_nonneg (show 0 ≤ C^6*(2:ℝ)^(6*ε*n-8*ε*b) by positivity)
      (show 0 ≤ (2:ℝ)^(2*(r:ℝ)) by positivity)]
  | succ s ih =>
    have hp : (1:ℕ) ≤ 2^(1+s) := Nat.succ_le_iff.mpr (by positivity)
    have he : (2*b)*2^(1+s)=b*2^(1+(s+1)) := by
      rw [show 1+(s+1)=(1+s)+1 by omega,pow_succ]; ring
    have hbnext : (2*b)*2^(1+s) ≤ n := by rw [he]; exact hb
    have hb₂ : 2*b ≤ n :=
      (show 2*b ≤ (2*b)*2^(1+s) by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (Nat.zero_le (2*b))).trans hbnext
    have hb₁ : b ≤ n := by omega
    have hprev := ih (a:=b) (by omega) hbnext
    have hsquare :
        (7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r))^2 =
        49*C^6*(2:ℝ)^(6*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*(2*b)+2*r) := by
      rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_mul_natCast (by norm_num)]
      norm_num only [show (3*2:ℕ)=6 by omega,show (7:ℝ)^2=49 by norm_num,Nat.cast_ofNat]
      congr 1
      congr 1
      ring
    have hsqrt : Real.sqrt
        (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r (1+s) b (2*b)) ≤
        7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      rw [hsquare]
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hprev
    rw [show 1+(s+1)=(1+s)+1 by omega,parabolaDyadicBilinearBudget]
    calc
      _ ≤ (7/(1/(2:ℝ)^r))*
          ((7*C^3*(2:ℝ)^(3*ε*n-(3*((1+s:ℕ):ℝ)+5)*ε*b+r))*
            (C*(2:ℝ)^(ε*((n-b:ℕ):ℝ)))^3) := by
        gcongr
      _ = _ := by
        rw [div_div_eq_mul_div,div_one,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
        rw [←Real.rpow_natCast (2:ℝ) r]
        simp only [Nat.cast_sub hb₁,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
        have he' : 6*ε*n-(3*(1+(s:ℝ)+1)+5)*ε*b+2*r =
            (r:ℝ)+(3*ε*n-(3*(1+s:ℝ)+5)*ε*b+r)+(ε*((n:ℝ)-b))*3 := by ring
        rw [he']
        conv_rhs =>
          rw [Real.rpow_add (by norm_num),Real.rpow_add (by norm_num)]
        ring
end TaoTrudgianYang2025

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Enlarging a proved constant preserves the actual finite-grid estimate. -/
theorem ParabolaDecouplingBound.mono {n : ℕ} {A B : ℝ}
    (hA : ParabolaDecouplingBound.{u} n A) (hAB : A ≤ B) :
    ParabolaDecouplingBound.{u} n B := by
  refine ⟨hA.1.trans hAB,fun ι W hW S z x hx => ?_⟩
  exact (hA.2 ι W hW S z x hx).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA.1 hAB 2)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

private theorem parabola_dyadic_exponential_root {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n) :
    (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
      2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) := by
  have hbudget : 0 ≤
      parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r := by
    cases t <;> simp only [parabolaDyadicBilinearBudget] <;> positivity
  have hmajor := parabolaDyadicBilinearBudget_exponential (ε:=ε) (r:=r) hC (a:=r) ht hn
  have hpower :
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3))^6 =
        64*C^6*(2:ℝ)^(6*ε*n-(3*(t:ℝ)+5)*ε*r+2*r) := by
    rw [mul_pow,mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    norm_num only [show (2:ℝ)^6=64 by norm_num,Nat.cast_ofNat]
    congr 1
    congr 1
    ring
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (6:ℕ) ≠ 0)).mp
  have hroot := Real.rpow_inv_natCast_pow hbudget (by norm_num : (6:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot,hpower]
  exact hmajor.trans (by gcongr; norm_num)

private theorem parabola_dyadic_exponential_iteration {C ε : ℝ} (hC : 0 ≤ C)
    {n r t : ℕ} (ht : 1 ≤ t) (hn : r*2^t ≤ n)
    (hεt : 8 ≤ (3*(t:ℝ)-1)*ε) :
    14*(C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)))+2*(2:ℝ)^r*
      (parabolaDyadicBilinearBudget (fun j => C*(2:ℝ)^(ε*j)) n r t r r)^((6:ℝ)⁻¹) ≤
        18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
  have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
  have hrn : r ≤ n :=
    (show r ≤ r*2^t by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
  have hroot := parabola_dyadic_exponential_root (ε:=ε) hC ht hn
  have hexp : ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r ≤ ε*((n:ℝ)-r) := by
    have hmul := mul_le_mul_of_nonneg_right hεt (Nat.cast_nonneg r : (0:ℝ) ≤ r)
    nlinarith
  have hterm : 2*(2:ℝ)^r*
      (2*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3)) ≤
        4*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
    rw [Nat.cast_sub hrn]
    calc
      _ = 4*C*(2:ℝ)^(ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3+r) := by
        rw [Real.rpow_add (by norm_num)
          (ε*n-((3*(t:ℝ)+5)/6)*ε*r+(r:ℝ)/3) (r:ℝ),
          Real.rpow_natCast]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp) (by positivity)
  have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2*(2:ℝ)^r by positivity)
  linarith

end TaoTrudgianYang2025

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Genuine dyadic finite weighted parabola decoupling with arbitrary positive
epsilon loss. The proof starts from the actual trivial bound and uses strong
induction; no decoupling estimate is an input. -/
theorem exists_parabolaDecouplingBound_dyadic {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ n : ℕ,
      ParabolaDecouplingBound.{u} (2^n) (C*(2:ℝ)^(ε*n)) := by
  obtain ⟨s,hs⟩ := exists_nat_gt ((8:ℝ)/ε)
  let t := s+1
  have ht : 1 ≤ t := by omega
  have hεt : 8 ≤ (3*(t:ℝ)-1)*ε := by
    have h := (div_lt_iff₀ hε).mp hs
    dsimp only [t]
    push_cast
    nlinarith
  obtain ⟨r,hr'⟩ := exists_nat_gt ((5:ℝ)/ε)
  have hr0 : (0:ℝ) < r := (div_pos (by norm_num) hε).trans hr'
  have hr : 0 < r := by exact_mod_cast hr0
  have hεr : 5 ≤ ε*r := by
    have h := (div_lt_iff₀ hε).mp hr'
    nlinarith
  have hcontract : (18:ℝ) ≤ (2:ℝ)^(ε*r) := by
    calc
      18 ≤ (2:ℝ)^(5:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hεr
  let N := r*2^t
  let C : ℝ := (2:ℝ)^N
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : N ≤ n
    · have hactual := parabolaDecouplingBound_dyadic_iterate
        (fun j => C*(2:ℝ)^(ε*j)) hr hn ih
      apply hactual.mono
      have hnum := parabola_dyadic_exponential_iteration hC.le ht hn hεt
      have hpow : (1:ℕ) ≤ 2^t := Nat.succ_le_iff.mpr (by positivity)
      have hrn : r ≤ n :=
        (show r ≤ r*2^t by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpow (Nat.zero_le r)).trans hn
      have he : ε*(n:ℝ)=ε*((n-r:ℕ):ℝ)+ε*r := by
        rw [Nat.cast_sub hrn]; ring
      calc
        _ ≤ 18*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := hnum
        _ ≤ (2:ℝ)^(ε*r)*C*(2:ℝ)^(ε*((n-r:ℕ):ℝ)) := by
          gcongr
        _ = C*(2:ℝ)^(ε*n) := by
          rw [he,Real.rpow_add (by norm_num) (ε*((n-r:ℕ):ℝ)) (ε*r)]
          ring
    · have hnN : n ≤ N := by omega
      have htrivial : ParabolaDecouplingBound.{u} (2^n) (Real.sqrt ((2:ℝ)^n)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaDecouplingBound_trivial.{u} (2^n)
      apply htrivial.mono
      have hpow : (1:ℝ) ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
      calc
        Real.sqrt ((2:ℝ)^n) ≤ (2:ℝ)^n := by
          apply Real.sqrt_le_iff.mpr
          exact ⟨by positivity,by nlinarith⟩
        _ ≤ C := pow_le_pow_right₀ (by norm_num) hnN
        _ ≤ C*(2:ℝ)^(ε*n) := by
          have h := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2)
            (show 0 ≤ ε*(n:ℝ) by positivity)
          nlinarith
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- A genuine finite physical-box sixth-moment estimate with the constructed
rapid cutoff on each cell. Only the explicit geometric scale and cell
conditions are inputs; the Fourier band and epsilon estimate are proved. -/
theorem exists_parabolaBox_dyadic_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := exists_parabolaDecouplingBound_dyadic.{u}
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : ParabolaWeightBand (1/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaRapidWeight_band hR hwidth r t
  have hnorm := (hD n).2 ι W hW S z x hx
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hbox := parabolaBox_le_rapid (Finset.univ.sigma S) (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t
  have hid := parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have he : parabolaRapidBilinearMoment
      (Finset.univ.sigma S) (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t =
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^6 := by
    simpa only [parabolaRapidBilinearMoment,parabolaWeightedBilinearMoment,W] using hid.symm
  exact hbox.trans (he.le.trans hcube)
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem parabola_sixNorm_weight_comparison {ι : Type*}
    {V W : ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hV₀ : ∀ p, 0 ≤ V p) (hW₀ : ∀ p, 0 ≤ W p)
    (hV : Integrable V) (hW : Integrable W) (hVW : ∀ p, V p ≤ C*W p)
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) :
    (parabolaWeightedSixNorm V S z x)^2 ≤
      C^((3:ℝ)⁻¹)*(parabolaWeightedSixNorm W S z x)^2 := by
  have hm : parabolaWeightedBilinearMoment V S S z z x x ≤
      C*parabolaWeightedBilinearMoment W S S z z x x := by
    have h := integral_mono
      (parabolaMomentFunction_integrable S S z z x x hV)
      ((parabolaMomentFunction_integrable S S z z x x hW).const_mul C)
      (fun p => (mul_le_mul_of_nonneg_right (hVW p)
        (parabolaMomentFunction_nonneg S S z z x x p)).trans_eq (by ring))
    rw [integral_const_mul] at h
    simpa only [parabolaWeightedBilinearMoment,parabolaMomentFunction,mul_assoc] using h
  apply (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity)
    (by norm_num : (3:ℕ) ≠ 0)).mp
  rw [mul_pow,←pow_mul,←pow_mul]
  have hroot := Real.rpow_inv_natCast_pow hC (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot]
  norm_num only [show (2*3:ℕ)=6 by omega]
  rw [parabolaWeightedSixNorm_pow_six V hV₀ hV,
    parabolaWeightedSixNorm_pow_six W hW₀ hW]
  exact hm

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Physical-box decoupling with the actual radial source weight on each cell. -/
theorem exists_parabolaBox_sourceWeight_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 0 < R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨C,hC,hbox⟩ := exists_parabolaBox_dyadic_decoupling.{u} hε
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨C*K,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx
  have hm := hbox n R r t hR hwidth ι S z x hx
  have hnorm (j : Fin (2^n)) :=
    parabola_sixNorm_weight_comparison hK.le
      (fun p : ℝ × ℝ => parabolaRapidWeight_nonneg R r t p.1 p.2)
      (fun p : ℝ × ℝ => parabolaSourceWeight_nonneg R r t p.1 p.2)
      (parabolaRapidWeight_band hR hwidth r t).2.1
      (integrable_parabolaSourceWeight hR r t)
      (fun p => hcomp R r t p.1 p.2) (S j) (z j) (x j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hs
  have hcube := pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
  rw [mul_pow] at hcube
  have hroot := Real.rpow_inv_natCast_pow hK.le (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot] at hcube
  calc
    _ ≤ _ := hm
    _ ≤ C*(2:ℝ)^(ε*n)*(K*
        (∑ j, (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
          (S j) (z j) (x j))^2)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring
end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem parabola_sourceWeight_horizontal_translate {R : ℝ} (hR : 0 < R)
    (r t α γ u : ℝ) :
    parabolaSourceWeight R r t (α-u) γ ≤
      (1+|u|/R)^100*parabolaSourceWeight R r t α γ := by
  have h := parabolaSourceWeight_triangle_lower R r t (α-u) γ α γ
  have he : parabolaSourceWeight R (α-u) γ α γ = 1/(1+|u|/R)^100 := by
    unfold parabolaSourceWeight
    have hx : (α-(α-u))/R=u/R := by ring
    rw [hx,sub_self,zero_div,Complex.ofReal_zero,zero_mul,add_zero,
      Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos hR]
  rw [he,mul_one_div] at h
  rw [div_le_iff₀ (by positivity)] at h
  simpa only [mul_comm] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff
namespace TaoTrudgianYang2025

private def bourgainCubicQuarticCutoff (a b s : ℝ) : ℂ :=
  (modelPhaseBufferedCutoff (-2) 2 (1/2) s : ℂ)*
    fordAdditiveCharacter (a*s^3+b*s^4)

private def bourgainCubicQuarticJoint (p : (ℝ × ℝ) × ℝ) : ℂ :=
  bourgainCubicQuarticCutoff p.1.1 p.1.2 p.2

private theorem bourgainCubicQuarticJoint_smooth :
    ContDiff ℝ ∞ bourgainCubicQuarticJoint := by
  have hc : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ =>
      (modelPhaseBufferedCutoff (-2) 2 (1/2) p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((modelPhaseBufferedCutoff_contDiff (-2) 2 (1/2)).comp contDiff_snd)
  unfold bourgainCubicQuarticJoint bourgainCubicQuarticCutoff fordAdditiveCharacter
  apply hc.mul
  have hp : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => p.1.1*p.2^3+p.1.2*p.2^4) :=
    ((contDiff_fst.fst).mul (contDiff_snd.pow 3)).add
      ((contDiff_fst.snd).mul (contDiff_snd.pow 4))
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hp)).cexp

private theorem bourgainCubicQuarticCutoff_smooth (a b : ℝ) :
    ContDiff ℝ ∞ (bourgainCubicQuarticCutoff a b) := by
  have hmap : ContDiff ℝ ∞ (fun s : ℝ => ((a,b),s)) :=
    contDiff_const.prodMk contDiff_id
  simpa only [Function.comp_def,bourgainCubicQuarticJoint] using
    bourgainCubicQuarticJoint_smooth.comp hmap

private theorem bourgainCubicQuarticCutoff_support (a b : ℝ) :
    tsupport (bourgainCubicQuarticCutoff a b) ⊆ Icc (-2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hk : s ∈ tsupport (modelPhaseBufferedCutoff (-2) 2 (1/2)) := by
    apply subset_closure
    intro hz
    exact hs (by rw [bourgainCubicQuarticCutoff,hz,Complex.ofReal_zero,zero_mul])
  have hb := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/2) hk
  constructor <;> linarith [hb.1,hb.2]


private theorem norm_vertical_slice_iteratedFDeriv
    (F : (ℝ × ℝ) × ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (s : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun x => F (p,x)) s‖ ≤
      ‖iteratedFDeriv ℝ j F (p,s)‖ := by
  let L : ℝ →L[ℝ] (ℝ × ℝ) × ℝ := ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
  have hL : ‖L‖=1 := ContinuousLinearMap.norm_inr ℝ (ℝ × ℝ) ℝ
  have hshift : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => (p,0)+q) :=
    contDiff_const.add contDiff_id
  have hf : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => F ((p,0)+q)) :=
    hF.comp hshift
  have he : (fun x => F (p,x)) = (fun q => F ((p,0)+q)) ∘ L := by
    ext x; simp [L]
  rw [he,L.iteratedFDeriv_comp_right hf s (i:=j)
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)),iteratedFDeriv_comp_add_left]
  have hp : (p,0)+L s = (p,s) := by simp [L]
  rw [hp]
  have h := (iteratedFDeriv ℝ j F (p,s)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => L)
  simpa only [hL,Finset.prod_const_one,mul_one] using h

private theorem bourgainCubicQuarticCutoff_derivative_bound (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ s : ℝ, ∀ j ≤ Q,
        ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ ≤ C := by
  let F := bourgainCubicQuarticJoint
  let B := fun p : (ℝ × ℝ) × ℝ =>
    ∑ j ∈ Finset.range (Q+1), ‖iteratedFDeriv ℝ j F p‖
  have hB : Continuous B := continuous_finsetSum _ fun j _ =>
    (bourgainCubicQuarticJoint_smooth.continuous_iteratedFDeriv (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1) ×ˢ Icc (-2:ℝ) 2) hB.continuousOn
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro a ha b hb s j hj
  by_cases hs : s ∈ Icc (-2:ℝ) 2
  · have hnorm : ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ ≤
        ‖iteratedFDeriv ℝ j F ((a,b),s)‖ := by
      simpa only [F,bourgainCubicQuarticJoint] using
        norm_vertical_slice_iteratedFDeriv F bourgainCubicQuarticJoint_smooth (a,b) s j
    have hsum : ‖iteratedFDeriv ℝ j F ((a,b),s)‖ ≤ B ((a,b),s) := by
      dsimp only [B]
      exact Finset.single_le_sum (fun k _ => norm_nonneg (iteratedFDeriv ℝ k F ((a,b),s)))
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    exact hnorm.trans (hsum.trans ((le_abs_self _).trans
      ((hM _ ⟨⟨ha,hb⟩,hs⟩).trans (le_max_left _ _))))
  · have hz : iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hs (bourgainCubicQuarticCutoff_support a b
        ((tsupport_iteratedFDeriv_subset j) (subset_closure h)))
    rw [hz,norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainCubicQuarticCutoff_derivative_integrable (a b : ℝ) (j : ℕ) :
    Integrable (fun s : ℝ => ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖) := by
  have hc : HasCompactSupport (bourgainCubicQuarticCutoff a b) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainCubicQuarticCutoff_support a b)
  exact ((bourgainCubicQuarticCutoff_smooth a b).continuous_iteratedFDeriv
    (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm.integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j).norm

private theorem bourgainCubicQuarticCutoff_derivative_integrals (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ j ≤ Q, (∫ s : ℝ, ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖) ≤ C := by
  obtain ⟨C,hC,h⟩ := bourgainCubicQuarticCutoff_derivative_bound Q
  refine ⟨4*C,by positivity,?_⟩
  intro a ha b hb j hj
  have hz (s : ℝ) (hs : s ∉ Icc (-2:ℝ) 2) :
      ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ = 0 := by
    have hd : iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s = 0 :=
      Function.notMem_support.mp (fun hh => hs
        (bourgainCubicQuarticCutoff_support a b ((support_iteratedFDeriv_subset j) hh)))
    rw [hd,norm_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hmain := norm_setIntegral_le_of_norm_le_const
    (μ:=volume) (s:=Icc (-2:ℝ) 2)
    (f:=fun s : ℝ => ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖)
    (by simp)
    (fun s _ => by simpa only [norm_norm] using h a ha b hb s j hj)
  have hnorm := le_abs_self
    (∫ s : ℝ in Icc (-2:ℝ) 2, ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖)
  have hmeasure : volume.real (Icc (-2:ℝ) 2) = 4 := by
    norm_num [Measure.real,Real.volume_Icc]
  rw [hmeasure] at hmain
  simpa only [mul_comm] using hnorm.trans hmain

private theorem bourgainCubicQuarticCutoff_fourier_moment (a b ξ : ℝ) (m : ℕ) :
    |ξ|^m*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤
      (2:ℝ)^m*∑ j ∈ Finset.range (m+1),
        ∫ s : ℝ, ‖iteratedFDeriv ℝ j (bourgainCubicQuarticCutoff a b) s‖ := by
  have hI (k n : ℕ) (hk : (k:ℕ∞) ≤ 0) (_hn : (n:ℕ∞) ≤ ⊤) :
      Integrable (fun s : ℝ => ‖s‖^k*
        ‖iteratedFDeriv ℝ n (bourgainCubicQuarticCutoff a b) s‖) := by
    have hk0 : k=0 := by
      have hk' : k ≤ 0 := by exact_mod_cast hk
      omega
    subst k
    simpa using bourgainCubicQuarticCutoff_derivative_integrable a b n
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K:=0) (N:=(⊤:ℕ∞)) (bourgainCubicQuarticCutoff_smooth a b) hI
    (k:=0) (n:=m) (by simp) (by simp) ξ
  simpa [Finset.sum_product,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainCubicQuarticCutoff_fourier_decay (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ ξ : ℝ, (1+|ξ|)^Q*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤ C := by
  obtain ⟨D,hD,hjet⟩ := bourgainCubicQuarticCutoff_derivative_integrals Q
  let E := (2:ℝ)^Q*((Q+1:ℕ):ℝ)*D
  refine ⟨(2:ℝ)^Q*(D+E),by dsimp [E]; positivity,?_⟩
  intro a ha b hb ξ
  have hz : ‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤ D := by
    have h := bourgainCubicQuarticCutoff_fourier_moment a b ξ 0
    simpa using h.trans (by simpa using hjet a ha b hb 0 (Nat.zero_le Q))
  have hp : |ξ|^Q*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ ≤ E := by
    apply (bourgainCubicQuarticCutoff_fourier_moment a b ξ Q).trans
    calc
      _ ≤ (2:ℝ)^Q*∑ _j ∈ Finset.range (Q+1), D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun j hj => hjet a ha b hb j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = E := by simp [E,mul_assoc]
  have hscale : (1+|ξ|)^Q ≤ (2:ℝ)^Q*(1+|ξ|^Q) := by
    by_cases hξ : |ξ| ≤ 1
    · have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+|ξ|)
        (by linarith : 1+|ξ| ≤ 2) Q
      have hnonneg : 0 ≤ (2:ℝ)^Q*|ξ|^Q := by positivity
      nlinarith
    · have hξ' : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
      calc
        _ ≤ (2*|ξ|)^Q := pow_le_pow_left₀ (by positivity) (by linarith) Q
        _ = (2:ℝ)^Q*|ξ|^Q := mul_pow _ _ _
        _ ≤ _ := by nlinarith [show (0:ℝ)≤(2:ℝ)^Q by positivity]
  calc
    _ ≤ (2:ℝ)^Q*(1+|ξ|^Q)*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ = (2:ℝ)^Q*(‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖+
        |ξ|^Q*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hz hp) (by positivity)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainCubicQuarticCutoff_uniform_fourierL1 :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖) ∧
      (∫ ξ : ℝ, (1+|ξ|)^100*‖𝓕 (bourgainCubicQuarticCutoff a b) ξ‖) ≤ C := by
  obtain ⟨C,hC,hdec⟩ := bourgainCubicQuarticCutoff_fourier_decay 102
  refine ⟨C*Real.pi,by positivity,?_⟩
  intro a ha b hb
  let f := bourgainCubicQuarticCutoff a b
  have hdom (ξ : ℝ) :
      (1+|ξ|)^100*‖𝓕 f ξ‖ ≤ C*(1+ξ^2)⁻¹ := by
    have hs : 1+ξ^2 ≤ (1+|ξ|)^2 := by
      nlinarith [sq_abs ξ,abs_nonneg ξ]
    have hp : (1+ξ^2)*((1+|ξ|)^100*‖𝓕 f ξ‖) ≤ C := by
      calc
        _ ≤ (1+|ξ|)^2*((1+|ξ|)^100*‖𝓕 f ξ‖) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _ = (1+|ξ|)^102*‖𝓕 f ξ‖ := by
          rw [show (102:ℕ)=2+100 by omega,pow_add]
          exact (mul_assoc _ _ _).symm
        _ ≤ C := hdec a ha b hb ξ
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using hp
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainCubicQuarticCutoff_support a b)
  have hi : Integrable f :=
    (bourgainCubicQuarticCutoff_smooth a b).continuous.integrable_of_hasCompactSupport hc
  have hhat : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hcont : Continuous (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 f ξ‖) :=
    ((continuous_const.add continuous_abs).pow 100).mul hhat.norm
  have hint : Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 f ξ‖) :=
    (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤
          (1+|ξ|)^100*‖𝓕 f ξ‖ by positivity)] using hdom ξ))
  refine ⟨hint,?_⟩
  have hmain := integral_mono hint (integrable_inv_one_add_sq.const_mul C) hdom
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hmain
  exact hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

/-- The actual cubic/quartic remainder has a uniformly integrable Fourier
multiplier representation on the unit interval. No Fourier estimate is assumed. -/
theorem exists_bourgainCubicQuartic_multiplier_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∃ K : ℝ → ℂ,
        Continuous K ∧ Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
        (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C ∧
        (∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) ∧
        ∀ s ∈ Icc (-1:ℝ) 1,
          fordAdditiveCharacter (a*s^3+b*s^4) =
            ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  obtain ⟨C,hC,h⟩ := bourgainCubicQuarticCutoff_uniform_fourierL1
  obtain ⟨D,hD,hdec⟩ := bourgainCubicQuarticCutoff_fourier_decay 102
  refine ⟨max C D,hC.trans_le (le_max_left _ _),?_⟩
  intro a ha b hb
  let f := bourgainCubicQuarticCutoff a b
  let K : ℝ → ℂ := 𝓕 f
  have hkernel := h a ha b hb
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainCubicQuarticCutoff_support a b)
  have hi : Integrable f :=
    (bourgainCubicQuarticCutoff_smooth a b).continuous.integrable_of_hasCompactSupport hc
  have hhat : Continuous K :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hKi : Integrable K :=
    hkernel.1.mono' hhat.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  refine ⟨K,hhat,hkernel.1,hkernel.2.trans (le_max_left _ _),?_,?_⟩
  · intro ξ
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (hdec a ha b hb ξ).trans (le_max_right C D)
  intro s hs
  have hcut : f s = fordAdditiveCharacter (a*s^3+b*s^4) := by
    dsimp only [f,bourgainCubicQuarticCutoff]
    rw [modelPhaseBufferedCutoff_one (by norm_num)
      (by linarith [hs.1]) (by linarith [hs.2]),Complex.ofReal_one,one_mul]
  have hinv := congrFun
    ((bourgainCubicQuarticCutoff_smooth a b).continuous.fourierInv_fourier_eq hi hKi) s
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  calc
    _ = f s := hcut.symm
    _ = _ := hinv.symm
    _ = ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [smul_eq_mul,fordAdditiveCharacter]
      have he : (↑(-2*Real.pi*ξ*(-s)) : ℂ)*Complex.I =
          2*(Real.pi:ℂ)*Complex.I*↑(ξ*s) := by push_cast; ring
      rw [he]
      exact mul_comm _ _
end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem weighted_integral_sixth_power
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {W f : α → ℝ}
    (hW : ∀ x, 0 ≤ W x)
    (hI : ∀ j ≤ 6, Integrable (fun x => W x*(f x)^j) μ) :
    (∫ x, W x*f x ∂μ)^6 ≤
      (∫ x, W x ∂μ)^5*(∫ x, W x*(f x)^6 ∂μ) := by
  let I := fun j : ℕ => ∫ x, W x*(f x)^j ∂μ
  have h0 : 0 ≤ I 0 := integral_nonneg (fun x => by simp [hW x])
  have h2 : 0 ≤ I 2 := integral_nonneg (fun x => mul_nonneg (hW x) (by positivity))
  have h6 : 0 ≤ I 6 := integral_nonneg (fun x => mul_nonneg (hW x) (by positivity))
  have h01 : (I 1)^2 ≤ I 0*I 2 := by
    simpa only [I,pow_zero,pow_one,one_pow,mul_one,one_mul] using
      (weighted_integral_cauchy_square (W:=W) (P:=fun _ => 1) (Q:=f) hW
        (by simpa using hI 0 (by omega))
        (by simpa using hI 1 (by omega))
        (hI 2 (by omega)))
  have h02 : (I 2)^2 ≤ I 0*I 4 := by
    have h := weighted_integral_cauchy_square (W:=W) (P:=fun _ => 1)
      (Q:=fun x => (f x)^2) hW
      (by simpa using hI 0 (by omega))
      (by simpa using hI 2 (by omega))
      (by simpa only [←pow_mul] using hI 4 (by omega))
    simpa only [I,pow_zero,one_pow,mul_one,one_mul,←pow_mul] using h
  have h24 : (I 4)^2 ≤ I 2*I 6 := by
    have hcross : Integrable (fun x => W x*f x*(f x)^3) μ := by
      convert hI 4 (by omega) using 1
      ext x
      ring
    have h := weighted_integral_cauchy_square (W:=W) (P:=f)
      (Q:=fun x => (f x)^3) hW (hI 2 (by omega)) hcross
      (by simpa only [←pow_mul] using hI 6 (by omega))
    have he (x : α) : W x*f x*(f x)^3 = W x*(f x)^4 := by ring
    simpa only [I,he,←pow_mul] using h
  have hcube : (I 2)^3 ≤ (I 0)^2*I 6 := by
    by_cases hz : I 2=0
    · simpa only [hz,zero_pow (by norm_num : (3:ℕ) ≠ 0)] using
        mul_nonneg (sq_nonneg (I 0)) h6
    have hpos : 0 < I 2 := lt_of_le_of_ne h2 (Ne.symm hz)
    have hs := pow_le_pow_left₀ (sq_nonneg (I 2)) h02 2
    have hs' : (I 2)^4 ≤ (I 0)^2*(I 4)^2 := by
      convert hs using 1 <;> ring
    have hprod := hs'.trans
      (mul_le_mul_of_nonneg_left h24 (sq_nonneg (I 0)))
    by_contra! hbad
    have hp := mul_pos hpos (sub_pos.mpr hbad)
    nlinarith only [hprod,hp]
  have hmain : (I 1)^6 ≤ (I 0)^5*I 6 := by
    calc
      _ = ((I 1)^2)^3 := by ring
      _ ≤ (I 0*I 2)^3 := pow_le_pow_left₀ (sq_nonneg (I 1)) h01 3
      _ = (I 0)^3*(I 2)^3 := mul_pow _ _ _
      _ ≤ (I 0)^3*((I 0)^2*I 6) :=
        mul_le_mul_of_nonneg_left hcube (pow_nonneg h0 3)
      _ = _ := by ring
  simpa only [I,pow_zero,pow_one,mul_one] using hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainRemainderEnvelope_integrable :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) := by
  have hc : Continuous (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹) :=
    (show Continuous (fun ξ : ℝ => (1+|ξ|)^102) from
      (continuous_const.add continuous_abs).pow 102).inv₀
      (fun ξ => ne_of_gt (by positivity : (0:ℝ) < (1+|ξ|)^102))
  apply integrable_inv_one_add_sq.mono' hc.aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hs : 1+ξ^2 ≤ (1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
  exact inv_anti₀ (by positivity) (hs.trans
    (pow_le_pow_right₀ (by linarith [abs_nonneg ξ]) (by omega : (2:ℕ) ≤ 102)))

private theorem bourgain_finite_multiplier_moment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ)
    {K : ℝ → ℂ} (hKc : Continuous K)
    (hKi : Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖))
    {C : ℝ} (hC : 0 < C)
    (hmass : (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C)
    (henv : ∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) :
    ‖∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i))‖^6 ≤
      C^6*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  let F := fun ξ : ℝ => ∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)
  let M := ∑ i ∈ S, ‖z i‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hFc : Continuous F := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) : ‖F ξ‖ ≤ M := by
    calc
      _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (ξ*s i)‖ := norm_sum_le _ _
      _ = M := by simp only [M,norm_mul,sargos_character_norm,mul_one]
  have hweight (ξ : ℝ) : ‖K ξ‖ ≤ (1+|ξ|)^100*‖K ξ‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by linarith [abs_nonneg ξ]) : (1:ℝ) ≤ (1+|ξ|)^100)
      (norm_nonneg (K ξ))
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall hweight)
  have hJ (j : ℕ) : Integrable (fun ξ => ‖K ξ‖*‖F ξ‖^j) :=
    hK.norm.mul_bdd (hFc.norm.pow j).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ) j))
  have hV : Integrable (fun ξ => ((1+|ξ|)^102)⁻¹*‖F ξ‖^6) :=
    bourgainRemainderEnvelope_integrable.mul_bdd (hFc.norm.pow 6).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ) 6))
  have hmass' : (∫ ξ : ℝ, ‖K ξ‖) ≤ C :=
    (integral_mono hK.norm hKi hweight).trans hmass
  have hm0 : 0 ≤ ∫ ξ : ℝ, ‖K ξ‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hJ0 : 0 ≤ ∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6 :=
    integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (by positivity))
  have hpow := weighted_integral_sixth_power (W:=fun ξ => ‖K ξ‖)
    (f:=fun ξ => ‖F ξ‖) (fun _ => norm_nonneg _) (fun j _ => hJ j)
  have hmajor : (∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) ≤
      C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖F ξ‖^6) := by
    rw [←integral_const_mul]
    apply integral_mono (hJ 6) (hV.const_mul C)
    intro ξ
    simpa only [div_eq_mul_inv,mul_assoc] using
      mul_le_mul_of_nonneg_right (henv ξ) (pow_nonneg (norm_nonneg _) 6)
  calc
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖)^6 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 6
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun ξ => K ξ*F ξ)
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖)^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) := hpow
    _ ≤ C^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ‖^6) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0 hmass' 5) hJ0
    _ ≤ C^5*(C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*‖F ξ‖^6)) :=
      mul_le_mul_of_nonneg_left hmajor (pow_nonneg hC.le 5)
    _ = _ := by ring

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- A uniform positive sixth-moment transfer for the actual cubic/quartic
remainder on a finite sum. Coefficients and repeated frequencies are unrestricted. -/
theorem exists_bourgainCubicQuartic_finite_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (a*(s i)^3+b*(s i)^4)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  obtain ⟨C,hC,hkern⟩ := exists_bourgainCubicQuartic_multiplier_kernel
  refine ⟨C^6,by positivity,?_⟩
  intro a ha b hb ι S z s hs
  obtain ⟨K,hKc,hKi,hmass,henv,hrep⟩ := hkern a ha b hb
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  have hterm (i : ι) :
      Integrable (fun ξ : ℝ => z i*(K ξ*fordAdditiveCharacter (ξ*s i))) := by
    have hc : Continuous (fun ξ : ℝ => fordAdditiveCharacter (ξ*s i)) := by
      unfold fordAdditiveCharacter
      fun_prop
    exact (hK.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (sargos_character_norm (ξ*s i)).le))).const_mul _
  have he : (∑ i ∈ S, z i*fordAdditiveCharacter (a*(s i)^3+b*(s i)^4)) =
      ∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)) := by
    calc
      _ = ∑ i ∈ S, z i*(∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i)) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun v => z i*v) (hrep (s i) (hs i hi)))
      _ = ∑ i ∈ S, ∫ ξ : ℝ, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) := by
        simp only [integral_const_mul]
      _ = ∫ ξ : ℝ, ∑ i ∈ S, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) :=
        (integral_finsetSum S (fun i _ => hterm i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [he]
  exact bourgain_finite_multiplier_moment S z s hKc hKi hC hmass henv

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025


private theorem parabola_sum_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ) (ξ α γ : ℝ) :
    sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*x i))
      x (fun i => (x i)^2) α γ =
    sargosPlanarSum S z x (fun i => (x i)^2) (α+ξ) γ := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

private theorem parabola_sourceWeight_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ)
    {R : ℝ} (hR : 0 < R) (r t ξ : ℝ) :
    (parabolaWeightedSixNorm
      (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
      S (fun i => z i*fordAdditiveCharacter (ξ*x i)) x)^2 ≤
      ((1+|ξ|/R)^100)^((3:ℝ)⁻¹)*
        (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) S z x)^2 := by
  let W := fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2
  let V := fun p : ℝ × ℝ => parabolaSourceWeight R r t (p.1-ξ) p.2
  have hW : Integrable W := integrable_parabolaSourceWeight hR r t
  have hV : Integrable V := by
    simpa only [V,W,Prod.fst_add,Prod.snd_add,add_zero,sub_eq_add_neg] using
      hW.comp_add_right (-ξ,0)
  have he := parabola_sum_modulation S z x ξ
  have hm :
      parabolaWeightedBilinearMoment W S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x =
      parabolaWeightedBilinearMoment V S S z z x x := by
    let F := fun p : ℝ × ℝ => V p*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^2*
      ‖sargosPlanarSum S z x (fun i => (x i)^2) p.1 p.2‖^4
    calc
      _ = ∫ p : ℝ × ℝ, F (p+(ξ,0)) := by
        unfold parabolaWeightedBilinearMoment
        apply integral_congr_ae
        filter_upwards with p
        simp only [F,V,W,Prod.fst_add,Prod.snd_add,add_zero,add_sub_cancel_right,he]
      _ = ∫ p : ℝ × ℝ, F p := integral_add_right_eq_self F (ξ,0)
      _ = _ := rfl
  have hn :
      parabolaWeightedSixNorm W S (fun i => z i*fordAdditiveCharacter (ξ*x i)) x =
      parabolaWeightedSixNorm V S z x := by
    apply (pow_left_inj₀ (parabolaWeightedSixNorm_nonneg _ _ _ _)
      (parabolaWeightedSixNorm_nonneg _ _ _ _) (by norm_num : (6:ℕ) ≠ 0)).mp
    rw [parabolaWeightedSixNorm_pow_six W
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hW,
      parabolaWeightedSixNorm_pow_six V
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hV]
    exact hm
  change (parabolaWeightedSixNorm W S _ x)^2 ≤ _
  rw [hn]
  exact parabola_sixNorm_weight_comparison (by positivity)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
    (fun p => parabolaSourceWeight_nonneg _ _ _ _ _) hV hW
    (fun p => parabola_sourceWeight_horizontal_translate hR r t p.1 p.2 ξ) S z x

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgain_box_multiplier_transfer :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type u} (S : Finset ι)
      (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (R r t : ℝ) (a b : ℝ × ℝ → ℝ), Continuous a → Continuous b →
      (∀ p ∈ Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R), a p ∈ Icc (-1:ℝ) 1) →
      (∀ p ∈ Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R), b p ∈ Icc (-1:ℝ) 1) →
      Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment S S
          (fun i => z i*fordAdditiveCharacter (ξ*s i))
          (fun i => z i*fordAdditiveCharacter (ξ*s i)) s s R r t) ∧
      (∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (s i*p.1+(s i)^2*p.2+a p*(s i)^3+b p*(s i)^4)‖^6) ≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          parabolaBoxBilinearMoment S S
            (fun i => z i*fordAdditiveCharacter (ξ*s i))
            (fun i => z i*fordAdditiveCharacter (ξ*s i)) s s R r t) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs R r t a b ha hb haB hbB
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  let P := fun p : ℝ × ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (s i*p.1+(s i)^2*p.2+a p*(s i)^3+b p*(s i)^4)‖^6
  let F := fun (ξ : ℝ) (p : ℝ × ℝ) =>
    ‖sargosPlanarSum S z s (fun i => (s i)^2) (p.1+ξ) p.2‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hPi : IntegrableOn P B := hPc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hFc : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2) := by
    unfold F sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) (p : ℝ × ℝ) :
      ‖F ξ p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_sargosPlanarSum_le_sum_norm S z s (fun i => (s i)^2) (p.1+ξ) p.2) 6
  have hiV : Integrable V := bourgainRemainderEnvelope_integrable
  have hiF : Integrable (fun q : ℝ × (ℝ × ℝ) => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict B)) := by
    have hiConst : IntegrableOn (fun _p : ℝ × ℝ => (1:ℝ)) B :=
      integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
    have hprod := hiV.mul_prod hiConst
    have h := hprod.mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using h
  have hpoint (p : ℝ × ℝ) (hp : p ∈ B) :
      P p ≤ C*(∫ ξ : ℝ, V ξ*F ξ p) := by
    have h := hbound (a p) (haB p hp) (b p) (hbB p hp) S
      (fun i => z i*fordAdditiveCharacter (s i*p.1+(s i)^2*p.2)) s hs
    have hleft :
        (∑ i ∈ S, (z i*fordAdditiveCharacter (s i*p.1+(s i)^2*p.2))*
          fordAdditiveCharacter (a p*(s i)^3+b p*(s i)^4)) =
        ∑ i ∈ S, z i*fordAdditiveCharacter
          (s i*p.1+(s i)^2*p.2+a p*(s i)^3+b p*(s i)^4) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc,←fordAdditiveCharacter_add]
      congr 2
      ring
    have hright (ξ : ℝ) :
        (∑ i ∈ S, (z i*fordAdditiveCharacter (s i*p.1+(s i)^2*p.2))*
          fordAdditiveCharacter (ξ*s i)) =
        sargosPlanarSum S z s (fun i => (s i)^2) (p.1+ξ) p.2 := by
      unfold sargosPlanarSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_assoc,←fordAdditiveCharacter_add]
      congr 2
      ring
    simpa only [hleft,hright,P,V,F] using h
  have hiRight := hiF.integral_prod_right.const_mul C
  have hmain := setIntegral_mono_on hPi hiRight
    (measurableSet_Icc.prod measurableSet_Icc) hpoint
  rw [integral_const_mul] at hmain
  have hswap := integral_integral_swap (μ:=volume) (ν:=volume.restrict B)
    (f:=fun ξ p => V ξ*F ξ p) hiF
  rw [←hswap] at hmain
  have he (ξ : ℝ) :
      (∫ p in B, V ξ*F ξ p) =
        V ξ*parabolaBoxBilinearMoment S S
          (fun i => z i*fordAdditiveCharacter (ξ*s i))
          (fun i => z i*fordAdditiveCharacter (ξ*s i)) s s R r t := by
    rw [integral_const_mul]
    congr 1
    unfold parabolaBoxBilinearMoment
    apply integral_congr_ae
    filter_upwards with p
    rw [parabola_sum_modulation]
    dsimp [F]
    ring
  constructor
  · simpa only [he,V] using hiF.integral_prod_left
  · simpa only [he,P,V,B] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem bourgain_modulation_envelope {R : ℝ} (hR : 1 ≤ R) (ξ : ℝ) :
    ((1+|ξ|)^102)⁻¹*(1+|ξ|/R)^100 ≤ (1+ξ^2)⁻¹ := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hdiv : |ξ|/R ≤ |ξ| := (div_le_self (abs_nonneg ξ) hR)
  have hloss : (1+|ξ|/R)^100 ≤ (1+|ξ|)^100 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 100
  have he : ((1+|ξ|)^102)⁻¹*(1+|ξ|)^100 = ((1+|ξ|)^2)⁻¹ := by
    rw [show (102:ℕ)=2+100 by omega,pow_add,mul_inv_rev]
    calc
      _ = ((1+|ξ|)^2)⁻¹*(((1+|ξ|)^100)⁻¹*(1+|ξ|)^100) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (by positivity),mul_one]
  calc
    _ ≤ ((1+|ξ|)^102)⁻¹*(1+|ξ|)^100 :=
      mul_le_mul_of_nonneg_left hloss (by positivity)
    _ = ((1+|ξ|)^2)⁻¹ := he
    _ ≤ (1+ξ^2)⁻¹ := inv_anti₀ (by positivity)
      (by nlinarith [sq_abs ξ,abs_nonneg ξ])

/-- Finite physical-box decoupling survives an actual bounded cubic/quartic
Taylor remainder. All Fourier kernels and moment estimates are derived. -/
theorem exists_bourgainCubicQuartic_box_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (R r t : ℝ), 1 ≤ R →
      3/(100*R) ≤ (1/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
      ∀ (a b : ℝ × ℝ → ℝ), Continuous a → Continuous b →
      (∀ p ∈ Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R), a p ∈ Icc (-1:ℝ) 1) →
      (∀ p ∈ Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R), b p ∈ Icc (-1:ℝ) 1) →
      (∫ p : ℝ × ℝ in Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R),
        ‖∑ jk ∈ Finset.univ.sigma S, z jk.1 jk.2*fordAdditiveCharacter
          (x jk.1 jk.2*p.1+(x jk.1 jk.2)^2*p.2+
            a p*(x jk.1 jk.2)^3+b p*(x jk.1 jk.2)^4)‖^6) ≤
        C*(2:ℝ)^(ε*n)*
          (∑ j, (parabolaWeightedSixNorm
            (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
            (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_sourceWeight_decoupling.{u} hε
  obtain ⟨E,hE,htransfer⟩ := exists_bourgain_box_multiplier_transfer.{u}
  refine ⟨E*D*Real.pi,by positivity,?_⟩
  intro n R r t hR hwidth ι S z x hx a b ha hb haB hbB
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let Z := fun jk : (j : Fin (2^n)) × ι => z jk.1 jk.2
  let X := fun jk : (j : Fin (2^n)) × ι => x jk.1 jk.2
  let Q := ∑ j, (parabolaWeightedSixNorm
    (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2) (S j) (z j) (x j))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hX : ∀ jk ∈ Finset.univ.sigma S, X jk ∈ Icc (-1:ℝ) 1 := by
    intro jk hjk
    have hk := (Finset.mem_sigma.mp hjk).2
    have h := hx jk.1 jk.2 hk
    have hn : (0:ℝ) < ((2^n:ℕ):ℝ) := by positivity
    have hlow : (0:ℝ) ≤ (jk.1:ℕ)/((2^n:ℕ):ℝ) := by positivity
    have hhigh : ((jk.1:ℕ)+1:ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
      apply (div_le_one hn).mpr
      exact_mod_cast (show (jk.1:ℕ)+1 ≤ 2^n from jk.1.isLt)
    exact ⟨by dsimp [X]; linarith [h.1],by dsimp [X]; linarith [h.2]⟩
  have ht := htransfer (Finset.univ.sigma S) Z X hX R r t a b ha hb haB hbB
  have hpoint (ξ : ℝ) :
      parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
        (fun jk => Z jk*fordAdditiveCharacter (ξ*X jk))
        (fun jk => Z jk*fordAdditiveCharacter (ξ*X jk)) X X R r t ≤
        D*(2:ℝ)^(ε*n)*(1+|ξ|/R)^100*Q^3 := by
    have hd := hdec n R r t hRpos hwidth ι S
      (fun j i => z j i*fordAdditiveCharacter (ξ*x j i)) x hx
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
      parabola_sourceWeight_modulation (S j) (z j) (x j) hRpos r t ξ)
    rw [←Finset.mul_sum] at hs
    have hc := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
    rw [mul_pow] at hc
    have hroot := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/R)^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hroot
    rw [hroot] at hc
    calc
      _ ≤ _ := hd
      _ ≤ D*(2:ℝ)^(ε*n)*((1+|ξ|/R)^100*Q^3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have hi := integrable_inv_one_add_sq.const_mul (D*(2:ℝ)^(ε*n)*Q^3)
  have hm := integral_mono ht.1 hi (fun ξ => by
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(D*(2:ℝ)^(ε*n)*(1+|ξ|/R)^100*Q^3) :=
        mul_le_mul_of_nonneg_left (hpoint ξ) (by positivity)
      _ = D*(2:ℝ)^(ε*n)*Q^3*(((1+|ξ|)^102)⁻¹*(1+|ξ|/R)^100) := by ring
      _ ≤ D*(2:ℝ)^(ε*n)*Q^3*(1+ξ^2)⁻¹ :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope hR ξ) (by positivity))
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hm
  calc
    _ ≤ E*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => Z jk*fordAdditiveCharacter (ξ*X jk))
          (fun jk => Z jk*fordAdditiveCharacter (ξ*X jk)) X X R r t) := ht.2
    _ ≤ E*(D*(2:ℝ)^(ε*n)*Q^3*Real.pi) :=
      mul_le_mul_of_nonneg_left hm hE.le
    _ = _ := by dsimp [Q]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory
open scoped Matrix
namespace TaoTrudgianYang2025

private def bourgainQuadraticFrame (a b : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,2*a,3*a^2,4*a^3;
     0,1,3*a,6*a^2;
     1,2*b,3*b^2,4*b^3;
     0,1,3*b,6*b^2]

private theorem bourgainQuadraticFrame_det (a b : ℝ) : (bourgainQuadraticFrame a b).det = 6*(b-a)^4 := by
  unfold bourgainQuadraticFrame
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix,
    show (1:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (2:Fin 4).succAbove (2:Fin 3)=3 by decide,
    show (3:Fin 4).succAbove (2:Fin 3)=2 by decide]
  ring

private theorem bourgainQuadraticFrame_map_volume {a b : ℝ} (hab : a ≠ b) :
    Measure.map ((bourgainQuadraticFrame a b).mulVec)
      (volume : Measure (Fin 4 → ℝ)) =
      ENNReal.ofReal ((6*(b-a)^4)⁻¹) • volume := by
  have hn : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hp : 0 < 6*(b-a)^4 := by
    have h := sq_pos_of_ne_zero (pow_ne_zero 2 hn)
    nlinarith
  have hdet : (bourgainQuadraticFrame a b).det ≠ 0 := by
    rw [bourgainQuadraticFrame_det]
    exact hp.ne'
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  simpa only [Matrix.toLin'_apply,bourgainQuadraticFrame_det,
    abs_of_pos (inv_pos.mpr hp)] using hm

private theorem bourgainQuadraticFrame_integral {a b : ℝ} (hab : a ≠ b)
    (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ x : Fin 4 → ℝ, f ((bourgainQuadraticFrame a b).mulVec x)) =
      (6*(b-a)^4)⁻¹*(∫ y : Fin 4 → ℝ, f y) := by
  have hc : Continuous ((bourgainQuadraticFrame a b).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hi := integral_map (μ:=volume) hc.aemeasurable hf.aestronglyMeasurable
  rw [bourgainQuadraticFrame_map_volume hab,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity),smul_eq_mul] at hi
  exact hi.symm

end TaoTrudgianYang2025



noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private def bourgainFourCoordinates :
    (Fin 4 → ℝ) ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm.trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).trans
        (MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow))

private theorem bourgainFourCoordinates_apply (x : Fin 4 → ℝ) :
    bourgainFourCoordinates x = ((x 0,x 1),(x 2,x 3)) := rfl

private theorem bourgainFourCoordinates_measurePreserving :
    MeasurePreserving bourgainFourCoordinates volume volume := by
  exact ((volume_preserving_finTwoArrow ℝ).prod (volume_preserving_finTwoArrow ℝ)).comp
    ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 2 ⊕ Fin 2 => ℝ)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
        (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)).symm)

private theorem bourgainFourCoordinates_integral_product
    (f g : ℝ × ℝ → ℝ) :
    (∫ y : Fin 4 → ℝ, f (y 0,y 1)*g (y 2,y 3)) =
      (∫ p : ℝ × ℝ, f p)*(∫ q : ℝ × ℝ, g q) := by
  have h := bourgainFourCoordinates_measurePreserving.integral_comp
    bourgainFourCoordinates.measurableEmbedding
    (fun p : (ℝ × ℝ) × (ℝ × ℝ) => f p.1*g p.2)
  calc
    _ = ∫ p : (ℝ × ℝ) × (ℝ × ℝ), f p.1*g p.2 := by
      simpa only [bourgainFourCoordinates_apply] using h
    _ = _ := integral_prod_mul f g

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_cube_bound {a b R : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hR : 0 ≤ R)
    (x : Fin 4 → ℝ) (hx : ∀ j, |x j| ≤ R) :
    ∀ i, |(bourgainQuadraticFrame a b).mulVec x i| ≤ 10*R := by
  have ha2 : |a|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  have ha3 : |a|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) ha
  have hb2 : |b|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have hb3 : |b|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hb
  have hrow (i : Fin 4) : (∑ j, |bourgainQuadraticFrame a b i j|) ≤ 10 := by
    fin_cases i <;>
      norm_num [bourgainQuadraticFrame,Fin.sum_univ_succ,abs_mul,abs_pow] <;>
      nlinarith [sq_abs a,sq_abs b]
  intro i
  calc
    _ ≤ ∑ j, |bourgainQuadraticFrame a b i j*x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |bourgainQuadraticFrame a b i j| *|x j| := by simp only [abs_mul]
    _ ≤ ∑ j, |bourgainQuadraticFrame a b i j| *R :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
    _ = (∑ j, |bourgainQuadraticFrame a b i j|)*R := (Finset.sum_mul _ _ _).symm
    _ ≤ 10*R := mul_le_mul_of_nonneg_right (hrow i) hR

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuadraticFrame_box_product
    {a b R : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hab : a ≠ b) (hR : 0 ≤ R)
    (f g : ℝ × ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ p, 0 ≤ g p) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f ((bourgainQuadraticFrame a b).mulVec x 0,
        (bourgainQuadraticFrame a b).mulVec x 1)*
      g ((bourgainQuadraticFrame a b).mulVec x 2,
        (bourgainQuadraticFrame a b).mulVec x 3)) ≤
      (6*(b-a)^4)⁻¹*
        (∫ p : ℝ × ℝ in Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R), f p)*
        (∫ q : ℝ × ℝ in Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R), g q) := by
  let B := Icc (-10*R) (10*R) ×ˢ Icc (-10*R) (10*R)
  let C := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  let F := (bourgainQuadraticFrame a b).mulVec
  let G := fun y : Fin 4 → ℝ => B.indicator f (y 0,y 1)*B.indicator g (y 2,y 3)
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hBcompact : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hi1 : Integrable (B.indicator f) :=
    (hf.continuousOn.integrableOn_compact hBcompact).integrable_indicator hB
  have hi2 : Integrable (B.indicator g) :=
    (hg.continuousOn.integrableOn_compact hBcompact).integrable_indicator hB
  have hGm : StronglyMeasurable G := by
    apply Measurable.stronglyMeasurable
    exact ((hf.measurable.indicator hB).comp (by fun_prop)).mul
      ((hg.measurable.indicator hB).comp (by fun_prop))
  have hiG : Integrable G := by
    have h := bourgainFourCoordinates_measurePreserving.integrable_comp_of_integrable
      (hi1.mul_prod hi2)
    simpa only [G,Function.comp_def,bourgainFourCoordinates_apply] using h
  have hFc : Continuous F := by
    change Continuous (Matrix.toLin' (bourgainQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hiGF : Integrable (fun x : Fin 4 → ℝ => G (F x)) := by
    have h : Integrable G (Measure.map F volume) := by
      rw [bourgainQuadraticFrame_map_volume hab]
      exact hiG.smul_measure ENNReal.ofReal_ne_top
    exact h.comp_measurable hFc.measurable
  have hG0 (y : Fin 4 → ℝ) : 0 ≤ G y := by
    apply mul_nonneg
    · exact Set.indicator_nonneg (fun p _ => hf0 p) _
    · exact Set.indicator_nonneg (fun p _ => hg0 p) _
  have he (x : Fin 4 → ℝ) (hx : x ∈ C) :
      f (F x 0,F x 1)*g (F x 2,F x 3) = G (F x) := by
    have hbound := bourgainQuadraticFrame_cube_bound ha hb hR x
      (fun j => abs_le.mpr ⟨hx.1 j,hx.2 j⟩)
    have hmem (i j : Fin 4) : (F x i,F x j) ∈ B := by
      exact ⟨⟨by linarith [(abs_le.mp (hbound i)).1],
        (abs_le.mp (hbound i)).2⟩,
        ⟨by linarith [(abs_le.mp (hbound j)).1],
        (abs_le.mp (hbound j)).2⟩⟩
    simp only [G,Set.indicator_of_mem (hmem 0 1),Set.indicator_of_mem (hmem 2 3)]
  calc
    _ = ∫ x : Fin 4 → ℝ in C, G (F x) :=
      setIntegral_congr_fun measurableSet_Icc he
    _ ≤ ∫ x : Fin 4 → ℝ, G (F x) :=
      setIntegral_le_integral hiGF (Filter.Eventually.of_forall (fun x => hG0 (F x)))
    _ = (6*(b-a)^4)⁻¹*(∫ y : Fin 4 → ℝ, G y) :=
      bourgainQuadraticFrame_integral hab G hGm
    _ = (6*(b-a)^4)⁻¹*((∫ p : ℝ × ℝ, B.indicator f p)*
        (∫ q : ℝ × ℝ, B.indicator g q)) := by
      rw [show (∫ y : Fin 4 → ℝ, G y) =
        (∫ p : ℝ × ℝ, B.indicator f p)*(∫ q : ℝ × ℝ, B.indicator g q) from
        bourgainFourCoordinates_integral_product (B.indicator f) (B.indicator g)]
    _ = _ := by rw [integral_indicator hB,integral_indicator hB]; ring

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainQuartic_remainder_bounds
    {c σ R : ℝ} (hc : |c| ≤ 1) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hR : 0 ≤ R) (hsmall : 5*R*σ^3 ≤ 1)
    (x : Fin 4 → ℝ) (hx : ∀ j, |x j| ≤ R) :
    |(x 2+4*c*x 3)*σ^3| ≤ 1 ∧ |x 3*σ^4| ≤ 1 := by
  have hcprod : |c| *|x 3| ≤ R :=
    (mul_le_mul hc (hx 3) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hs : |x 2+4*c*x 3| ≤ 5*R := by
    have h := abs_add_le (x 2) (4*c*x 3)
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<4)] at h
    nlinarith [hx 2]
  constructor
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hσ 3)]
    exact (mul_le_mul_of_nonneg_right hs (pow_nonneg hσ 3)).trans hsmall
  · rw [abs_mul,abs_of_nonneg (pow_nonneg hσ 4)]
    have hpow : σ^4 ≤ σ^3 := by
      have h := mul_le_mul_of_nonneg_left hσ1 (pow_nonneg hσ 3)
      nlinarith only [h]
    calc
      _ ≤ R*σ^4 := mul_le_mul_of_nonneg_right (hx 3) (pow_nonneg hσ 4)
      _ ≤ R*σ^3 := mul_le_mul_of_nonneg_left hpow hR
      _ ≤ 1 := by nlinarith [mul_nonneg hR (pow_nonneg hσ 3)]

universe u
/-- Exact finite quartic source entry. The physical size and interval width
derive both remainder coefficient bounds before the proved multiplier is used. -/
theorem exists_bourgainQuartic_scaled_moment :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (c σ R : ℝ), |c| ≤ 1 → 0 ≤ σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      ∀ x : Fin 4 → ℝ, (∀ j, |x j| ≤ R) →
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+σ*s i)+x 1*(c+σ*s i)^2+
          x 2*(c+σ*s i)^3+x 3*(c+σ*s i)^4)‖^6 ≤
        C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            ((σ*s i)*(x 0+2*c*x 1+3*c^2*x 2+4*c^3*x 3)+
              (σ*s i)^2*(x 1+3*c*x 2+6*c^2*x 3)+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs c σ R hc hσ hσ1 hR hsmall x hx
  have hb := bourgainQuartic_remainder_bounds hc hσ hσ1 hR hsmall x hx
  let L := x 0+2*c*x 1+3*c^2*x 2+4*c^3*x 3
  let Q := x 1+3*c*x 2+6*c^2*x 3
  let A := (x 2+4*c*x 3)*σ^3
  let B := x 3*σ^4
  let Z := fun i => z i*fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q)
  have hmain := h A (abs_le.mp hb.1) B (abs_le.mp hb.2) S Z s hs
  have he :
      (∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+σ*s i)+x 1*(c+σ*s i)^2+
          x 2*(c+σ*s i)^3+x 3*(c+σ*s i)^4)) =
      fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
        ∑ i ∈ S, Z i*fordAdditiveCharacter (A*(s i)^3+B*(s i)^4) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Z]
    rw [show fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
        ((z i*fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q))*
          fordAdditiveCharacter (A*(s i)^3+B*(s i)^4)) =
        z i*(fordAdditiveCharacter (x 0*c+x 1*c^2+x 2*c^3+x 3*c^4)*
          (fordAdditiveCharacter ((σ*s i)*L+(σ*s i)^2*Q)*
            fordAdditiveCharacter (A*(s i)^3+B*(s i)^4))) by ring]
    rw [←fordAdditiveCharacter_add,←fordAdditiveCharacter_add]
    congr 2
    dsimp [L,Q,A,B]
    ring
  rw [he,norm_mul,sargos_character_norm,one_mul]
  have hr (ξ : ℝ) :
      (∑ i ∈ S, Z i*fordAdditiveCharacter (ξ*s i)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((σ*s i)*L+(σ*s i)^2*Q+ξ*s i) := by
    simp only [Z,mul_assoc,←fordAdditiveCharacter_add]
  simpa only [hr,L,Q] using hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

/-- The separated quartic quadratic frame bounds the actual product of two
finite parabolic sixth moments, with its exact Jacobian and a derived box image. -/
private theorem bourgainQuadraticFrame_finite_product {ι τ : Type*}
    (S : Finset ι) (V : Finset τ) (z : ι → ℂ) (c : τ → ℂ)
    (u : ι → ℝ) (v : τ → ℝ) {a b R : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≠ b) (hR : 0 ≤ R) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      ‖sargosPlanarSum S z u (fun i => (u i)^2)
        ((bourgainQuadraticFrame a b).mulVec x 0)
        ((bourgainQuadraticFrame a b).mulVec x 1)‖^6*
      ‖sargosPlanarSum V c v (fun j => (v j)^2)
        ((bourgainQuadraticFrame a b).mulVec x 2)
        ((bourgainQuadraticFrame a b).mulVec x 3)‖^6) ≤
      (6*(b-a)^4)⁻¹*
        parabolaBoxBilinearMoment S S z z u u (10*R) 0 0*
        parabolaBoxBilinearMoment V V c c v v (10*R) 0 0 := by
  have hf : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum S z u (fun i => (u i)^2) p.1 p.2‖^6) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hg : Continuous (fun p : ℝ × ℝ =>
      ‖sargosPlanarSum V c v (fun j => (v j)^2) p.1 p.2‖^6) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have h := bourgainQuadraticFrame_box_product ha hb hab hR
    (fun p => ‖sargosPlanarSum S z u (fun i => (u i)^2) p.1 p.2‖^6)
    (fun p => ‖sargosPlanarSum V c v (fun j => (v j)^2) p.1 p.2‖^6)
    hf hg (fun _ => by positivity) (fun _ => by positivity)
  have he (w : ℝ) : w^2*w^4=w^6 := by ring
  simpa only [parabolaBoxBilinearMoment,he,zero_sub,zero_add,neg_mul] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem integrable_bourgain_modulated_box {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s u : ι → ℝ) (R r t : ℝ) :
    Integrable (fun ξ : ℝ => ((1+|ξ|)^102)⁻¹*
      parabolaBoxBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*s i))
        (fun i => z i*fordAdditiveCharacter (ξ*s i)) u u R r t) := by
  let B := Icc (r-R) (r+R) ×ˢ Icc (t-R) (t+R)
  let F := fun (ξ : ℝ) (p : ℝ × ℝ) =>
    ‖sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
      u (fun i => (u i)^2) p.1 p.2‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  have hFc : Continuous (fun q : ℝ × (ℝ × ℝ) => F q.1 q.2) := by
    unfold F sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hFb (ξ : ℝ) (p : ℝ × ℝ) :
      ‖F ξ p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 := by
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [F]; positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 6
    have h := norm_sargosPlanarSum_le_sum_norm S
      (fun i => z i*fordAdditiveCharacter (ξ*s i))
      u (fun i => (u i)^2) p.1 p.2
    simpa only [norm_mul,sargos_character_norm,mul_one] using h
  have hiV : Integrable V := bourgainRemainderEnvelope_integrable
  have hiF : Integrable (fun q : ℝ × (ℝ × ℝ) => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict B)) := by
    have hiConst : IntegrableOn (fun _p : ℝ × ℝ => (1:ℝ)) B :=
      integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top
    have hprod := hiV.mul_prod hiConst
    have h := hprod.mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using h
  have he (w : ℝ) : w^2*w^4=w^6 := by ring
  simpa only [integral_const_mul,F,V,B,parabolaBoxBilinearMoment,he] using
    hiF.integral_prod_left

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgain_character_six_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (θ : ι → ℝ) :
    ‖(‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖^6:ℝ)‖ ≤
      (∑ i ∈ S, ‖z i‖)^6 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 6
  calc
    _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (θ i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]

private theorem bourgain_frame_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (σ ξ α γ : ℝ) :
    sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
      (fun i => σ*s i) (fun i => (σ*s i)^2) α γ =
    ∑ i ∈ S, z i*fordAdditiveCharacter
      ((σ*s i)*α+(σ*s i)^2*γ+ξ*s i) := by
  unfold sargosPlanarSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

private theorem bourgainQuadraticFrame_apply (a b : ℝ) (x : Fin 4 → ℝ) :
    (bourgainQuadraticFrame a b).mulVec x =
      ![x 0+2*a*x 1+3*a^2*x 2+4*a^3*x 3,
        x 1+3*a*x 2+6*a^2*x 3,
        x 0+2*b*x 1+3*b^2*x 2+4*b^3*x 3,
        x 1+3*b*x 2+6*b^2*x 3] := by
  funext i
  fin_cases i <;>
    simp [bourgainQuadraticFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring


private theorem bourgain_kernel_setIntegral_bound
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {B : Set α} {f : α → ℝ} {H : β → α → ℝ} {C : ℝ}
    (hB : MeasurableSet B) (hf : IntegrableOn f B μ)
    (hH : Integrable (Function.uncurry H) (ν.prod (μ.restrict B)))
    (hp : ∀ x ∈ B, f x ≤ C*(∫ y, H y x ∂ν)) :
    (∫ x in B, f x ∂μ) ≤ C*(∫ y, ∫ x in B, H y x ∂μ ∂ν) := by
  have h := setIntegral_mono_on hf (hH.integral_prod_right.const_mul C) hB hp
  rw [integral_const_mul] at h
  dsimp only [Function.uncurry] at h
  have hswap := integral_integral_swap (μ:=ν) (ν:=μ.restrict B) hH
  rw [←hswap] at h
  exact h

universe u
set_option maxHeartbeats 400000 in
/-- The original finite quartic bilinear moment reduces to a product of
parabolic Fourier averages. All Taylor, Jacobian, box and Fubini inputs are derived. -/
theorem exists_bourgainQuartic_bilinear_reduction :
    ∃ C > (0:ℝ), ∀ (ι τ : Type u) (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (s : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      (∀ j ∈ V, v j ∈ Icc (-1:ℝ) 1) →
      ∀ (a b σ R : ℝ), |a| ≤ 1 → |b| ≤ 1 → a ≠ b →
      0 ≤ σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*(a+σ*s i)+x 1*(a+σ*s i)^2+
            x 2*(a+σ*s i)^3+x 3*(a+σ*s i)^4)‖^6*
        ‖∑ j ∈ V, c j*fordAdditiveCharacter
          (x 0*(b+σ*v j)+x 1*(b+σ*v j)^2+
            x 2*(b+σ*v j)^3+x 3*(b+σ*v j)^4)‖^6) ≤
        C*(6*(b-a)^4)⁻¹*
          (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            parabolaBoxBilinearMoment S S
              (fun i => z i*fordAdditiveCharacter (ξ*s i))
              (fun i => z i*fordAdditiveCharacter (ξ*s i))
              (fun i => σ*s i) (fun i => σ*s i) (10*R) 0 0)*
          (∫ η : ℝ, ((1+|η|)^102)⁻¹*
            parabolaBoxBilinearMoment V V
              (fun j => c j*fordAdditiveCharacter (η*v j))
              (fun j => c j*fordAdditiveCharacter (η*v j))
              (fun j => σ*v j) (fun j => σ*v j) (10*R) 0 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainQuartic_scaled_moment.{u}
  refine ⟨C^2,by positivity,?_⟩
  intro ι τ S V z c s v hs hv a b σ R ha hb hab hσ hσ1 hR hsmall
  let B := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let A := fun x : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*(a+σ*s i)+x 1*(a+σ*s i)^2+x 2*(a+σ*s i)^3+x 3*(a+σ*s i)^4)‖^6
  let D := fun x : Fin 4 → ℝ => ‖∑ j ∈ V, c j*fordAdditiveCharacter
    (x 0*(b+σ*v j)+x 1*(b+σ*v j)^2+x 2*(b+σ*v j)^3+x 3*(b+σ*v j)^4)‖^6
  let F := fun (ξ : ℝ) (x : Fin 4 → ℝ) =>
    ‖∑ i ∈ S, z i*fordAdditiveCharacter
      ((σ*s i)*(x 0+2*a*x 1+3*a^2*x 2+4*a^3*x 3)+
        (σ*s i)^2*(x 1+3*a*x 2+6*a^2*x 3)+ξ*s i)‖^6
  let G := fun (η : ℝ) (x : Fin 4 → ℝ) =>
    ‖∑ j ∈ V, c j*fordAdditiveCharacter
      ((σ*v j)*(x 0+2*b*x 1+3*b^2*x 2+4*b^3*x 3)+
        (σ*v j)^2*(x 1+3*b*x 2+6*b^2*x 3)+η*v j)‖^6
  let J := fun ξ : ℝ => parabolaBoxBilinearMoment S S
    (fun i => z i*fordAdditiveCharacter (ξ*s i))
    (fun i => z i*fordAdditiveCharacter (ξ*s i))
    (fun i => σ*s i) (fun i => σ*s i) (10*R) 0 0
  let K := fun η : ℝ => parabolaBoxBilinearMoment V V
    (fun j => c j*fordAdditiveCharacter (η*v j))
    (fun j => c j*fordAdditiveCharacter (η*v j))
    (fun j => σ*v j) (fun j => σ*v j) (10*R) 0 0
  have hF0 (ξ : ℝ) (x : Fin 4 → ℝ) : 0 ≤ F ξ x := by dsimp [F]; positivity
  have hG0 (η : ℝ) (x : Fin 4 → ℝ) : 0 ≤ G η x := by dsimp [G]; positivity
  have hcont : Continuous (fun qx : (ℝ × ℝ) × (Fin 4 → ℝ) =>
      F qx.1.1 qx.2*G qx.1.2 qx.2) := by
    unfold F G fordAdditiveCharacter
    fun_prop
  have hfinite (qx : (ℝ × ℝ) × (Fin 4 → ℝ)) :
      ‖F qx.1.1 qx.2*G qx.1.2 qx.2‖ ≤
        (∑ i ∈ S, ‖z i‖)^6*(∑ j ∈ V, ‖c j‖)^6 := by
    rw [norm_mul]
    exact mul_le_mul (bourgain_character_six_bound S z _)
      (bourgain_character_six_bound V c _) (norm_nonneg _) (by positivity)
  have hW : Integrable W := bourgainRemainderEnvelope_integrable
  have hiH : Integrable (fun qx : (ℝ × ℝ) × (Fin 4 → ℝ) =>
      W qx.1.1*W qx.1.2*(F qx.1.1 qx.2*G qx.1.2 qx.2))
      (volume.prod (volume.restrict B)) := by
    have hconst : IntegrableOn (fun _x : Fin 4 → ℝ => (1:ℝ)) B :=
      integrableOn_const isCompact_Icc.measure_ne_top
    have hprod := (hW.mul_prod hW).mul_prod hconst
    have h := hprod.mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hfinite)
    simpa only [mul_one] using h
  have hAD : IntegrableOn (fun x => A x*D x) B := by
    have hc : Continuous (fun x => A x*D x) := by
      unfold A D fordAdditiveCharacter
      fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (x : Fin 4 → ℝ) (hx : x ∈ B) :
      A x*D x ≤ C^2*(∫ q : ℝ × ℝ, W q.1*W q.2*(F q.1 x*G q.2 x)) := by
    have hxc : ∀ j, |x j| ≤ R := fun j => abs_le.mpr ⟨hx.1 j,hx.2 j⟩
    have hA := hbound S z s hs a σ R ha hσ hσ1 hR hsmall x hxc
    have hD := hbound V c v hv b σ R hb hσ hσ1 hR hsmall x hxc
    have hpos : 0 ≤ C*(∫ ξ : ℝ, W ξ*F ξ x) :=
      mul_nonneg hC.le (integral_nonneg (fun ξ => mul_nonneg (by dsimp [W]; positivity) (hF0 ξ x)))
    have hprod := mul_le_mul hA hD (by positivity) hpos
    have he : (∫ q : ℝ × ℝ, W q.1*W q.2*(F q.1 x*G q.2 x)) =
        (∫ ξ : ℝ, W ξ*F ξ x)*(∫ η : ℝ, W η*G η x) := by
      calc
        _ = ∫ q : ℝ × ℝ, (W q.1*F q.1 x)*(W q.2*G q.2 x) := by
          apply integral_congr_ae
          filter_upwards with q
          ring
        _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
          (fun ξ : ℝ => W ξ*F ξ x) (fun η : ℝ => W η*G η x)
    rw [he]
    calc
      _ ≤ (C*(∫ ξ : ℝ, W ξ*F ξ x))*(C*(∫ η : ℝ, W η*G η x)) := hprod
      _ = _ := by ring
  have hm := bourgain_kernel_setIntegral_bound (α:=Fin 4 → ℝ) (β:=ℝ × ℝ)
    (μ:=volume) (ν:=volume) (B:=B) (C:=C^2)
    (f:=fun x => A x*D x)
    (H:=fun q x => W q.1*W q.2*(F q.1 x*G q.2 x))
    measurableSet_Icc hAD hiH hpoint
  have hFframe (ξ : ℝ) (x : Fin 4 → ℝ) :
      F ξ x = ‖sargosPlanarSum S (fun i => z i*fordAdditiveCharacter (ξ*s i))
        (fun i => σ*s i) (fun i => (σ*s i)^2)
        ((bourgainQuadraticFrame a b).mulVec x 0)
        ((bourgainQuadraticFrame a b).mulVec x 1)‖^6 := by
    rw [bourgain_frame_modulation,bourgainQuadraticFrame_apply]
    rfl
  have hGframe (η : ℝ) (x : Fin 4 → ℝ) :
      G η x = ‖sargosPlanarSum V (fun j => c j*fordAdditiveCharacter (η*v j))
        (fun j => σ*v j) (fun j => (σ*v j)^2)
        ((bourgainQuadraticFrame a b).mulVec x 2)
        ((bourgainQuadraticFrame a b).mulVec x 3)‖^6 := by
    rw [bourgain_frame_modulation,bourgainQuadraticFrame_apply]
    rfl
  have hinner (q : ℝ × ℝ) :
      (∫ x : Fin 4 → ℝ in B, F q.1 x*G q.2 x) ≤
        (6*(b-a)^4)⁻¹*J q.1*K q.2 := by
    simpa only [hFframe,hGframe,J,K,B] using
      bourgainQuadraticFrame_finite_product S V
        (fun i => z i*fordAdditiveCharacter (q.1*s i))
        (fun j => c j*fordAdditiveCharacter (q.2*v j))
        (fun i => σ*s i) (fun j => σ*v j) ha hb hab hR
  have hJ : Integrable (fun ξ => W ξ*J ξ) :=
    integrable_bourgain_modulated_box S z s (fun i => σ*s i) (10*R) 0 0
  have hK : Integrable (fun η => W η*K η) :=
    integrable_bourgain_modulated_box V c v (fun j => σ*v j) (10*R) 0 0
  have hmajor := integral_mono hiH.integral_prod_left
    ((hJ.mul_prod hK).const_mul ((6*(b-a)^4)⁻¹)) (fun q => by
      dsimp only [Prod.fst,Prod.snd]
      rw [integral_const_mul]
      calc
        _ ≤ (W q.1*W q.2)*((6*(b-a)^4)⁻¹*J q.1*K q.2) :=
          mul_le_mul_of_nonneg_left (hinner q) (by dsimp [W]; positivity)
        _ = _ := by ring)
  rw [integral_const_mul] at hmajor
  have heProduct : (∫ q : ℝ × ℝ, (W q.1*J q.1)*(W q.2*K q.2)) =
      (∫ ξ : ℝ, W ξ*J ξ)*(∫ η : ℝ, W η*K η) :=
    integral_prod_mul (μ:=volume) (ν:=volume)
      (fun ξ : ℝ => W ξ*J ξ) (fun η : ℝ => W η*K η)
  rw [heProduct] at hmajor
  calc
    _ ≤ C^2*(∫ q : ℝ × ℝ, ∫ x : Fin 4 → ℝ in B,
        W q.1*W q.2*(F q.1 x*G q.2 x)) := hm
    _ ≤ C^2*((6*(b-a)^4)⁻¹*
        ((∫ ξ : ℝ, W ξ*J ξ)*(∫ η : ℝ, W η*K η))) :=
      mul_le_mul_of_nonneg_left hmajor (sq_nonneg C)
    _ = _ := by dsimp [W,J,K]; ring

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025

/-- The specific four-coordinate source curve is exactly a reordered quartic
moment curve under the nonnegative square-root parameter. -/
private theorem bourgain_source_quartic_phase {t : ℝ} (ht : 0 ≤ t) (x : Fin 4 → ℝ) :
    x 0*t+x 1*t^2+x 2*t^((3:ℝ)/2)+x 3*Real.sqrt t =
      x 3*Real.sqrt t+x 0*(Real.sqrt t)^2+
        x 2*(Real.sqrt t)^3+x 1*(Real.sqrt t)^4 := by
  have h3 : (Real.sqrt t)^3 = t^((3:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul ht]
    congr 1
    norm_num
  have h4 : (Real.sqrt t)^4 = t^2 := by
    calc
      _ = ((Real.sqrt t)^2)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt ht]
  rw [Real.sq_sqrt ht,h3,h4]
  ring

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private def bourgainSourcePermutation : (Fin 4 → ℝ) ≃ᵐ (Fin 4 → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 4 => ℝ)
    ((Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 1 3))

private theorem bourgainSourcePermutation_apply (x : Fin 4 → ℝ) :
    bourgainSourcePermutation x = ![x 3,x 0,x 2,x 1] := by
  funext i
  fin_cases i <;> rfl

private theorem bourgainSourcePermutation_measurePreserving :
    MeasurePreserving bourgainSourcePermutation volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin 4 => ℝ)
    ((Equiv.swap (0:Fin 4) 3).trans (Equiv.swap 1 3))

private theorem bourgainSourcePermutation_preimage_cube (R : ℝ) :
    bourgainSourcePermutation ⁻¹' Icc (fun _ => -R) (fun _ => R) =
      Icc (fun _ => -R) (fun _ => R) := by
  ext x
  change ((∀ i, -R ≤ bourgainSourcePermutation x i) ∧
    ∀ i, bourgainSourcePermutation x i ≤ R) ↔
    ((∀ i, -R ≤ x i) ∧ ∀ i, x i ≤ R)
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> intro i <;> fin_cases i <;>
    first | exact h1 0 | exact h1 1 | exact h1 2 | exact h1 3 |
      exact h2 0 | exact h2 1 | exact h2 2 | exact h2 3

private theorem bourgainSourcePermutation_cube_integral (R : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) :
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f (bourgainSourcePermutation x)) =
    ∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f y := by
  let B := Icc (fun _ : Fin 4 => -R) (fun _ : Fin 4 => R)
  have h := bourgainSourcePermutation_measurePreserving.integral_comp
    bourgainSourcePermutation.measurableEmbedding (B.indicator f)
  rw [integral_indicator measurableSet_Icc] at h
  have he (x : Fin 4 → ℝ) :
      B.indicator f (bourgainSourcePermutation x) =
        B.indicator (fun y => f (bourgainSourcePermutation y)) x := by
    have hx : bourgainSourcePermutation x ∈ B ↔ x ∈ B := by
      change x ∈ bourgainSourcePermutation ⁻¹' B ↔ x ∈ B
      rw [bourgainSourcePermutation_preimage_cube]
    by_cases hmem : x ∈ B
    · rw [indicator_of_mem hmem,indicator_of_mem (hx.mpr hmem)]
    · rw [indicator_of_notMem hmem,indicator_of_notMem (mt hx.mp hmem)]
  simp_rw [he] at h
  rw [integral_indicator measurableSet_Icc] at h
  exact h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Exact bilinear entry for the source curve (t,t²,t^(3/2),sqrt(t)).
The square-root reparametrization, coefficient permutation and physical measure
are derived, not additional analytic hypotheses. -/
theorem exists_bourgainSourceCurve_bilinear_reduction :
    ∃ C > (0:ℝ), ∀ (ι τ : Type u) (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
      ∀ (a b σ R : ℝ), |a| ≤ 1 → |b| ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 ≤ R → 5*R*σ^3 ≤ 1 →
      (∀ i ∈ S, |Real.sqrt (w i)-a| ≤ σ) →
      (∀ j ∈ V, |Real.sqrt (v j)-b| ≤ σ) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6*
        ‖∑ j ∈ V, c j*fordAdditiveCharacter
          (x 0*v j+x 1*(v j)^2+x 2*(v j)^((3:ℝ)/2)+x 3*Real.sqrt (v j))‖^6) ≤
        C*(6*(b-a)^4)⁻¹*
          (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            parabolaBoxBilinearMoment S S
              (fun i => z i*fordAdditiveCharacter (ξ*((Real.sqrt (w i)-a)/σ)))
              (fun i => z i*fordAdditiveCharacter (ξ*((Real.sqrt (w i)-a)/σ)))
              (fun i => Real.sqrt (w i)-a) (fun i => Real.sqrt (w i)-a) (10*R) 0 0)*
          (∫ η : ℝ, ((1+|η|)^102)⁻¹*
            parabolaBoxBilinearMoment V V
              (fun j => c j*fordAdditiveCharacter (η*((Real.sqrt (v j)-b)/σ)))
              (fun j => c j*fordAdditiveCharacter (η*((Real.sqrt (v j)-b)/σ)))
              (fun j => Real.sqrt (v j)-b) (fun j => Real.sqrt (v j)-b) (10*R) 0 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainQuartic_bilinear_reduction.{u}
  refine ⟨C,hC,?_⟩
  intro ι τ S V z c w v hw hv a b σ R ha hb hab hσ hσ1 hR hsmall hwc hvc
  let s := fun i => (Real.sqrt (w i)-a)/σ
  let t := fun j => (Real.sqrt (v j)-b)/σ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    apply abs_le.mp
    dsimp [s]
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hwc i hi)
  have ht : ∀ j ∈ V, t j ∈ Icc (-1:ℝ) 1 := by
    intro j hj
    apply abs_le.mp
    dsimp [t]
    rw [abs_div,abs_of_pos hσ]
    exact (div_le_one hσ).mpr (hvc j hj)
  have hsbase (i : ι) : σ*s i = Real.sqrt (w i)-a := by
    dsimp [s]
    field_simp
  have htbase (j : τ) : σ*t j = Real.sqrt (v j)-b := by
    dsimp [t]
    field_simp
  have hscenter (i : ι) : a+σ*s i = Real.sqrt (w i) := by rw [hsbase]; ring
  have htcenter (j : τ) : b+σ*t j = Real.sqrt (v j) := by rw [htbase]; ring
  let QS := fun y : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (y 0*(a+σ*s i)+y 1*(a+σ*s i)^2+y 2*(a+σ*s i)^3+y 3*(a+σ*s i)^4)‖^6
  let QV := fun y : Fin 4 → ℝ => ‖∑ j ∈ V, c j*fordAdditiveCharacter
    (y 0*(b+σ*t j)+y 1*(b+σ*t j)^2+y 2*(b+σ*t j)^3+y 3*(b+σ*t j)^4)‖^6
  have heS (x : Fin 4 → ℝ) :
      (∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((bourgainSourcePermutation x) 0*(a+σ*s i)+
          (bourgainSourcePermutation x) 1*(a+σ*s i)^2+
          (bourgainSourcePermutation x) 2*(a+σ*s i)^3+
          (bourgainSourcePermutation x) 3*(a+σ*s i)^4) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hscenter,bourgainSourcePermutation_apply]
    exact congrArg (fun q => z i*fordAdditiveCharacter q)
      (bourgain_source_quartic_phase (hw i hi) x)
  have heV (x : Fin 4 → ℝ) :
      (∑ j ∈ V, c j*fordAdditiveCharacter
        (x 0*v j+x 1*(v j)^2+x 2*(v j)^((3:ℝ)/2)+x 3*Real.sqrt (v j))) =
      ∑ j ∈ V, c j*fordAdditiveCharacter
        ((bourgainSourcePermutation x) 0*(b+σ*t j)+
          (bourgainSourcePermutation x) 1*(b+σ*t j)^2+
          (bourgainSourcePermutation x) 2*(b+σ*t j)^3+
          (bourgainSourcePermutation x) 3*(b+σ*t j)^4) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [htcenter,bourgainSourcePermutation_apply]
    exact congrArg (fun q => c j*fordAdditiveCharacter q)
      (bourgain_source_quartic_phase (hv j hj) x)
  have hmain := hbound ι τ S V z c s t hs ht a b σ R ha hb hab hσ.le hσ1 hR hsmall
  calc
    _ = ∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        QS (bourgainSourcePermutation x)*QV (bourgainSourcePermutation x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [heS,heV]
    _ = ∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), QS y*QV y :=
      bourgainSourcePermutation_cube_integral R (fun y => QS y*QV y)
    _ ≤ _ := by
      simpa only [QS,QV,hsbase,htbase,s,t] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_parabolaBox_scaled_rapid_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 0 < R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨D,hDpos,hD⟩ := exists_parabolaDecouplingBound_dyadic.{u}
    (ε:=ε/6) (by positivity)
  refine ⟨D^6,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  let W := fun p : ℝ × ℝ => parabolaRapidWeight R r t p.1 p.2
  have hW : ParabolaWeightBand (σ/((2^n:ℕ):ℝ)) W := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using parabolaRapidWeight_band hR hwidth r t
  have hnorm := (hD n).rescale hσ (a:=0) (by norm_num)
    (by simpa using hσ₁) ι W hW S z x (by simpa only [zero_add] using hx)
  have hcube := pow_le_pow_left₀ (sq_nonneg _) hnorm 3
  simp only [mul_pow,←pow_mul] at hcube
  have hcoef : (D*(2:ℝ)^((ε/6)*n))^6 = D^6*(2:ℝ)^(ε*n) := by
    rw [mul_pow,←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    congr 1
    push_cast
    ring
  norm_num only [show (2*3:ℕ)=6 by omega] at hcube
  rw [←mul_pow,hcoef] at hcube
  have hbox := parabolaBox_le_rapid (Finset.univ.sigma S) (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
    (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) hR r t
  have hid := parabolaWeightedSixNorm_pow_six W hW.1 hW.2.1
    (Finset.univ.sigma S) (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2)
  have he : parabolaRapidBilinearMoment
      (Finset.univ.sigma S) (Finset.univ.sigma S)
      (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
      (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t =
      (parabolaWeightedSixNorm W (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2) (fun jk => x jk.1 jk.2))^6 := by
    simpa only [parabolaRapidBilinearMoment,parabolaWeightedBilinearMoment,W] using hid.symm
  exact hbox.trans (he.le.trans hcube)

private theorem exists_parabolaBox_scaled_source_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 0 < R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, x j k ∈ Icc
          (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun jk => z jk.1 jk.2) (fun jk => z jk.1 jk.2)
          (fun jk => x jk.1 jk.2) (fun jk => x jk.1 jk.2) R r t ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (x j))^2)^3 := by
  obtain ⟨C,hC,hbox⟩ := exists_parabolaBox_scaled_rapid_decoupling.{u} hε
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨C*K,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  have hm := hbox n σ R r t hσ hσ₁ hR hwidth ι S z x hx
  have hnorm (j : Fin (2^n)) :=
    parabola_sixNorm_weight_comparison hK.le
      (fun p : ℝ × ℝ => parabolaRapidWeight_nonneg R r t p.1 p.2)
      (fun p : ℝ × ℝ => parabolaSourceWeight_nonneg R r t p.1 p.2)
      (parabolaRapidWeight_band hR hwidth r t).2.1
      (integrable_parabolaSourceWeight hR r t)
      (fun p => hcomp R r t p.1 p.2) (S j) (z j) (x j)
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hs
  have hcube := pow_le_pow_left₀
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 3
  rw [mul_pow] at hcube
  have hroot := Real.rpow_inv_natCast_pow hK.le (by norm_num : (3:ℕ) ≠ 0)
  simp only [Nat.cast_ofNat] at hroot
  rw [hroot] at hcube
  calc
    _ ≤ _ := hm
    _ ≤ C*(2:ℝ)^(ε*n)*(K*
        (∑ j, (parabolaWeightedSixNorm
          (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
          (S j) (z j) (x j))^2)^3) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Decoupling of the actual Fourier-averaged quadratic moments returned by
the four-dimensional source reduction. The physical and frequency scales are
linked, and no decoupling or multiplier estimate is assumed. -/
theorem exists_parabolaBox_scaled_modulation_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (σ R r t : ℝ), 0 < σ → σ ≤ 1 → 1 ≤ σ*R →
      3/(100*R) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (s : Fin (2^n) → ι → ℝ),
        (∀ j, ∀ k ∈ S j, s j k ∈ Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
          parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
            (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
            (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
            (fun jk => σ*s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t) ≤
          C*(2:ℝ)^(ε*n)*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
              (S j) (z j) (fun i => σ*s j i))^2)^3 := by
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_scaled_source_decoupling.{u} hε
  refine ⟨D*Real.pi,by positivity,?_⟩
  intro n σ R r t hσ hσ₁ hσR hwidth ι S z s hs
  have hR : 0 < R := (mul_pos_iff_of_pos_left hσ).mp (lt_of_lt_of_le zero_lt_one hσR)
  let Q := ∑ j, (parabolaWeightedSixNorm
    (fun p : ℝ × ℝ => parabolaSourceWeight R r t p.1 p.2)
    (S j) (z j) (fun i => σ*s j i))^2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hx : ∀ j, ∀ k ∈ S j, σ*s j k ∈ Icc
      (σ*((j:ℕ)/((2^n:ℕ):ℝ))) (σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ))) := by
    intro j k hk
    exact ⟨mul_le_mul_of_nonneg_left (hs j k hk).1 hσ.le,
      mul_le_mul_of_nonneg_left (hs j k hk).2 hσ.le⟩
  have hpoint (ξ : ℝ) :
      parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
        (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
        (fun jk => z jk.1 jk.2*fordAdditiveCharacter (ξ*s jk.1 jk.2))
        (fun jk => σ*s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t ≤
        D*(2:ℝ)^(ε*n)*(1+|ξ|/(σ*R))^100*Q^3 := by
    have hd := hdec n σ R r t hσ hσ₁ hR hwidth ι S
      (fun j i => z j i*fordAdditiveCharacter (ξ*s j i)) (fun j i => σ*s j i) hx
    have hmod (v : ℝ) : (ξ/σ)*(σ*v) = ξ*v := by field_simp
    have hratio : |ξ/σ|/R = |ξ|/(σ*R) := by rw [abs_div,abs_of_pos hσ,div_div]
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ =>
      parabola_sourceWeight_modulation (S j) (z j) (fun i => σ*s j i) hR r t (ξ/σ))
    simp_rw [hmod,hratio] at hsum
    rw [←Finset.mul_sum] at hsum
    have hc := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hsum 3
    rw [mul_pow] at hc
    have hroot := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/(σ*R))^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hroot
    rw [hroot] at hc
    calc
      _ ≤ _ := hd
      _ ≤ D*(2:ℝ)^(ε*n)*((1+|ξ|/(σ*R))^100*Q^3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have hi := integrable_bourgain_modulated_box (Finset.univ.sigma S)
    (fun jk => z jk.1 jk.2) (fun jk => s jk.1 jk.2) (fun jk => σ*s jk.1 jk.2) R r t
  have hj := integrable_inv_one_add_sq.const_mul (D*(2:ℝ)^(ε*n)*Q^3)
  have hm := integral_mono hi hj (fun ξ => by
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(D*(2:ℝ)^(ε*n)*(1+|ξ|/(σ*R))^100*Q^3) :=
        mul_le_mul_of_nonneg_left (hpoint ξ) (by positivity)
      _ = D*(2:ℝ)^(ε*n)*Q^3*(((1+|ξ|)^102)⁻¹*(1+|ξ|/(σ*R))^100) := by ring
      _ ≤ D*(2:ℝ)^(ε*n)*Q^3*(1+ξ^2)⁻¹ :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope hσR ξ) (by positivity))
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hm
  calc
    _ ≤ _ := hm
    _ = _ := by dsimp [Q]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The original finite source-curve bilinear moment decouples to actual
source-weighted quadratic cell norms. This is the source-entry and parabola
decoupling composition, not yet the return to four-dimensional curve-cell norms. -/
theorem exists_bourgainSourceCurve_parabolic_cell_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (a b σ R : ℝ),
      |a| ≤ 1 → |b| ≤ 1 → a ≠ b → 0 < σ → σ ≤ 1 → 0 ≤ R →
      5*R*σ^3 ≤ 1 → 1 ≤ σ*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
              x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
          ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
            (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
              x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
          C*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (S j) (z j) (fun i => Real.sqrt (w j i)-a))^2)^3*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (V j) (c j) (fun k => Real.sqrt (v j k)-b))^2)^3 := by
  obtain ⟨E,hE,hsource⟩ := exists_bourgainSourceCurve_bilinear_reduction.{u}
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_scaled_modulation_decoupling.{u}
    (ε:=ε/2) (by positivity)
  refine ⟨E*D^2,by positivity,?_⟩
  intro n a b σ R ha hb hab hσ hσ₁ hR hrem hσR hwidth ι τ S V z c w v hw hv hwgrid hvgrid
  let s := fun j i => (Real.sqrt (w j i)-a)/σ
  let t := fun j k => (Real.sqrt (v j k)-b)/σ
  have hsbase (j : Fin (2^n)) (i : ι) : σ*s j i = Real.sqrt (w j i)-a := by
    dsimp [s]
    field_simp
  have htbase (j : Fin (2^n)) (k : τ) : σ*t j k = Real.sqrt (v j k)-b := by
    dsimp [t]
    field_simp
  have hsgrid : ∀ j, ∀ i ∈ S j, s j i ∈ Icc
      ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    intro j i hi
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hwgrid j i hi).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hwgrid j i hi).2]
  have htgrid : ∀ j, ∀ k ∈ V j, t j k ∈ Icc
      ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ)) := by
    intro j k hk
    constructor
    · apply (le_div_iff₀ hσ).mpr
      nlinarith [(hvgrid j k hk).1]
    · apply (div_le_iff₀ hσ).mpr
      nlinarith [(hvgrid j k hk).2]
  have hunit (j : Fin (2^n)) {y : ℝ}
      (hy : y ∈ Icc ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      y ∈ Icc (0:ℝ) 1 := by
    have hl : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ) := by positivity
    have hh : ((j:ℕ)+1:ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast (show (j:ℕ)+1 ≤ 2^n from j.isLt)
    exact ⟨hl.trans hy.1,hy.2.trans hh⟩
  have hwindowS : ∀ ji ∈ Finset.univ.sigma S, |Real.sqrt (w ji.1 ji.2)-a| ≤ σ := by
    intro ji hji
    have hh := hunit ji.1 (hsgrid ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    rw [←hsbase,abs_of_nonneg (mul_nonneg hσ.le hh.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hσ.le
  have hwindowV : ∀ jk ∈ Finset.univ.sigma V, |Real.sqrt (v jk.1 jk.2)-b| ≤ σ := by
    intro jk hjk
    have hh := hunit jk.1 (htgrid jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    rw [←htbase,abs_of_nonneg (mul_nonneg hσ.le hh.1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh.2 hσ.le
  have hmain := hsource ((j : Fin (2^n)) × ι) ((j : Fin (2^n)) × τ)
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun jk => c jk.1 jk.2)
    (fun ji => w ji.1 ji.2) (fun jk => v jk.1 jk.2)
    (fun ji hji => hw ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => hv jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    a b σ R ha hb hab hσ hσ₁ hR hrem hwindowS hwindowV
  have hS := hdec n σ (10*R) 0 0 hσ hσ₁ hσR hwidth ι S z s hsgrid
  have hV := hdec n σ (10*R) 0 0 hσ hσ₁ hσR hwidth τ V c t htgrid
  simp_rw [hsbase] at hS
  simp_rw [htbase] at hV
  have hnonnegV : 0 ≤ ∫ η : ℝ, ((1+|η|)^102)⁻¹*
      parabolaBoxBilinearMoment (Finset.univ.sigma V) (Finset.univ.sigma V)
        (fun jk => c jk.1 jk.2*fordAdditiveCharacter (η*t jk.1 jk.2))
        (fun jk => c jk.1 jk.2*fordAdditiveCharacter (η*t jk.1 jk.2))
        (fun jk => Real.sqrt (v jk.1 jk.2)-b)
        (fun jk => Real.sqrt (v jk.1 jk.2)-b) (10*R) 0 0 := by
    apply integral_nonneg
    intro η
    apply mul_nonneg (by positivity)
    unfold parabolaBoxBilinearMoment
    exact integral_nonneg (fun p => mul_nonneg (sq_nonneg _)
      (pow_nonneg (norm_nonneg _) 4))
  have hprod := mul_le_mul hS hV hnonnegV (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ E*(6*(b-a)^4)⁻¹ by positivity)
  have he : ((2:ℝ)^((ε/2)*n))^2 = (2:ℝ)^(ε*n) := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ _ := hmain
    _ ≤ _ := by simpa only [s,t,mul_assoc] using hm
    _ = _ := by
      have he' : (2:ℝ)^((ε/2)*n)*(2:ℝ)^((ε/2)*n) = (2:ℝ)^(ε*n) := by
        rw [←pow_two,he]
      calc
        _ = E*D^2*((2:ℝ)^((ε/2)*n)*(2:ℝ)^((ε/2)*n))*(6*(b-a)^4)⁻¹*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (S j) (z j) (fun i => Real.sqrt (w j i)-a))^2)^3*
            (∑ j, (parabolaWeightedSixNorm
              (fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2)
              (V j) (c j) (fun k => Real.sqrt (v j k)-b))^2)^3 := by ring
        _ = _ := by rw [he']

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainCubicQuartic_inverse_moment :
    ∃ C > (0:ℝ), ∀ a ∈ Icc (-1:ℝ) 1, ∀ b ∈ Icc (-1:ℝ) 1,
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s θ : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter
              (θ i+a*(s i)^3+b*(s i)^4+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro a ha b hb ι S z s θ hs
  have hna : -a ∈ Icc (-1:ℝ) 1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hnb : -b ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hb.2],by linarith [hb.1]⟩
  have hm := h (-a) hna (-b) hnb S
    (fun i => z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4)) s hs
  have hleft :
      (∑ i ∈ S, (z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4))*
        fordAdditiveCharacter (-a*(s i)^3+-b*(s i)^4)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter (θ i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    ring
  have hright (ξ : ℝ) :
      (∑ i ∈ S, (z i*fordAdditiveCharacter (θ i+a*(s i)^3+b*(s i)^4))*
        fordAdditiveCharacter (ξ*s i)) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        (θ i+a*(s i)^3+b*(s i)^4+ξ*s i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
  simpa only [hleft,hright] using hm

private def bourgainCurveCellFrame (a c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,-2*a,3*c^2,8*c^3;
     0,1,-3*c,-6*c^2;
     0,0,1,0;
     0,0,0,1]

private theorem bourgainCurveCellFrame_apply (a c : ℝ) (y : Fin 4 → ℝ) :
    (bourgainCurveCellFrame a c).mulVec y =
      ![y 0-2*a*y 1+3*c^2*y 2+8*c^3*y 3,
        y 1-3*c*y 2-6*c^2*y 3,y 2,y 3] := by
  funext i
  fin_cases i <;>
    simp [bourgainCurveCellFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

private theorem bourgainCurveCellFrame_det (a c : ℝ) :
    (bourgainCurveCellFrame a c).det = 1 := by
  unfold bourgainCurveCellFrame
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix]

private theorem bourgainCurveCellFrame_measurePreserving (a c : ℝ) :
    MeasurePreserving ((bourgainCurveCellFrame a c).mulVec)
      (volume : Measure (Fin 4 → ℝ)) volume := by
  have hc : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  refine ⟨hc.measurable,?_⟩
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (show (bourgainCurveCellFrame a c).det ≠ 0 by rw [bourgainCurveCellFrame_det]; norm_num)
  simpa only [Matrix.toLin'_apply,bourgainCurveCellFrame_det,inv_one,abs_one,
    ENNReal.ofReal_one,one_smul] using hm

private theorem bourgainCurveCellFrame_phase (a c δ s : ℝ) (y : Fin 4 → ℝ) :
    let x := (bourgainCurveCellFrame a c).mulVec y
    x 0*(c+δ*s)+x 1*(c+δ*s)^2+x 2*(c+δ*s)^3+x 3*(c+δ*s)^4 =
      (c+δ*s-a)*y 0+(c+δ*s-a)^2*y 1+
        ((y 2+4*c*y 3)*δ^3)*s^3+(y 3*δ^4)*s^4+
        (a*y 0-a^2*y 1+c^3*y 2+3*c^4*y 3) := by
  rw [bourgainCurveCellFrame_apply]
  dsimp
  ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

private theorem norm_bourgain_character_sum_add {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (θ : ι → ℝ) (k : ℝ) :
    ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i+k)‖ =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter (θ i)‖ := by
  have he :
      (∑ i ∈ S, z i*fordAdditiveCharacter (θ i+k)) =
        (∑ i ∈ S, z i*fordAdditiveCharacter (θ i))*fordAdditiveCharacter k := by
    rw [Finset.sum_mul]
    simp only [fordAdditiveCharacter_add,mul_assoc]
  rw [he,norm_mul,sargos_character_norm,mul_one]

private theorem exists_bourgainCurveCell_inverse_pointwise :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |c| ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ R → 5*R*δ^3 ≤ 1 →
      ∀ y : Fin 4 → ℝ, |y 2| ≤ R → |y 3| ≤ R →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*y 0+(c+δ*s i-a)^2*y 1)‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter
              ((bourgainCurveCellFrame a c).mulVec y 0*(c+δ*s i)+
                (bourgainCurveCellFrame a c).mulVec y 1*(c+δ*s i)^2+
                (bourgainCurveCellFrame a c).mulVec y 2*(c+δ*s i)^3+
                (bourgainCurveCellFrame a c).mulVec y 3*(c+δ*s i)^4+ξ*s i)‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainCubicQuartic_inverse_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z s hs a c δ R hc hδ hδ₁ hR hrem y hy₂ hy₃
  have hcoeff := bourgainQuartic_remainder_bounds hc hδ hδ₁ hR hrem
    ![0,0,y 2,y 3] (by
      intro j
      fin_cases j
      · simpa using hR
      · simpa using hR
      · exact hy₂
      · exact hy₃)
  change |(y 2+4*c*y 3)*δ^3| ≤ 1 ∧ |y 3*δ^4| ≤ 1 at hcoeff
  let P := fun i => (c+δ*s i-a)*y 0+(c+δ*s i-a)^2*y 1
  let A := (y 2+4*c*y 3)*δ^3
  let B := y 3*δ^4
  let K := a*y 0-a^2*y 1+c^3*y 2+3*c^4*y 3
  have hm := h A (abs_le.mp hcoeff.1) B (abs_le.mp hcoeff.2) S z s P hs
  have he (ξ : ℝ) :
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((bourgainCurveCellFrame a c).mulVec y 0*(c+δ*s i)+
          (bourgainCurveCellFrame a c).mulVec y 1*(c+δ*s i)^2+
          (bourgainCurveCellFrame a c).mulVec y 2*(c+δ*s i)^3+
          (bourgainCurveCellFrame a c).mulVec y 3*(c+δ*s i)^4+ξ*s i)‖ =
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (P i+A*(s i)^3+B*(s i)^4+ξ*s i)‖ := by
    calc
      _ = ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((P i+A*(s i)^3+B*(s i)^4+ξ*s i)+K)‖ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        congr 2
        have hp := bourgainCurveCellFrame_phase a c δ (s i) y
        dsimp only at hp
        rw [hp]
        dsimp [P,A,B,K]
        ring
      _ = _ := norm_bourgain_character_sum_add S z _ K
  simpa only [he,P] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private theorem bourgainCurveCellFrame_norm_bound {a c R : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 ≤ R)
    (y : Fin 4 → ℝ) (hy₂ : |y 2| ≤ R) (hy₃ : |y 3| ≤ R) :
    ‖(bourgainCurveCellFrame a c).mulVec y‖ ≤ 14*(|y 0|+|y 1|+R) := by
  have hc2 : |c|^2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  have hc3 : |c|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
  have hrow (i : Fin 4) : (∑ j, |bourgainCurveCellFrame a c i j|) ≤ 14 := by
    fin_cases i <;>
      norm_num [bourgainCurveCellFrame,Fin.sum_univ_succ,abs_mul,abs_pow] <;>
      nlinarith [sq_abs c]
  have hy (j : Fin 4) : |y j| ≤ |y 0|+|y 1|+R := by
    fin_cases j
    · change |y 0| ≤ _
      linarith [abs_nonneg (y 1)]
    · change |y 1| ≤ _
      linarith [abs_nonneg (y 0)]
    · change |y 2| ≤ _
      linarith [abs_nonneg (y 0),abs_nonneg (y 1)]
    · change |y 3| ≤ _
      linarith [abs_nonneg (y 0),abs_nonneg (y 1)]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |bourgainCurveCellFrame a c i j*y j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |bourgainCurveCellFrame a c i j| * |y j| := by simp only [abs_mul]
    _ ≤ ∑ j, |bourgainCurveCellFrame a c i j| * (|y 0|+|y 1|+R) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hy j) (abs_nonneg _))
    _ = (∑ j, |bourgainCurveCellFrame a c i j|)*(|y 0|+|y 1|+R) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i) (by positivity)

private theorem bourgainCurveCellFrame_weight_bound {a c R δ : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 < R) (hδ : 0 < δ)
    (y : Fin 4 → ℝ) (hy₂ : |y 2| ≤ R) (hy₃ : |y 3| ≤ R) (ξ : ℝ) :
    parabolaSourceWeight R 0 0 (y 0) (y 1) ≤
      (32:ℝ)^100*(1+|ξ|/(δ*R))^100*
        ((1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖)^100)⁻¹ := by
  let q := ‖(((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)‖
  let L := |ξ|/(δ*R)
  have hq : 0 ≤ q := norm_nonneg _
  have hL : 0 ≤ L := by positivity
  have hy₀ : |y 0| ≤ R*q := by
    have h := Complex.abs_re_le_norm (((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
      abs_div,abs_of_pos hR] at h
    exact (div_le_iff₀ hR).mp h |>.trans_eq (mul_comm _ _)
  have hy₁ : |y 1| ≤ R*q := by
    have h := Complex.abs_im_le_norm (((y 0/R:ℝ):ℂ)+(y 1/R:ℝ)*Complex.I)
    simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero,
      abs_div,abs_of_pos hR] at h
    exact (div_le_iff₀ hR).mp h |>.trans_eq (mul_comm _ _)
  have hshift : ‖(![ξ/δ,0,0,0] : Fin 4 → ℝ)‖ ≤ |ξ|/δ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs,abs_of_pos hδ] <;> positivity
  have hf := bourgainCurveCellFrame_norm_bound ha hc hR.le y hy₂ hy₃
  have hn : ‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖ ≤
      28*q+14+L := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
    have hadd := norm_add_le ((bourgainCurveCellFrame a c).mulVec y) ![ξ/δ,0,0,0]
    have hb : ‖(bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]‖ ≤
        R*(28*q+14+L) := by
      have hRL : R*L = |ξ|/δ := by dsimp [L]; field_simp
      nlinarith only [hadd,hf,hshift,hy₀,hy₁,hRL]
    have h := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hR.le)
    simpa only [←mul_assoc,inv_mul_cancel₀ hR.ne',one_mul] using h
  have hb : 1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖ ≤
      32*(1+q)*(1+L) := by nlinarith [mul_nonneg hq hL]
  have hp := pow_le_pow_left₀ (by positivity) hb 100
  rw [mul_pow,mul_pow] at hp
  simp only [parabolaSourceWeight,sub_zero]
  change 1/(1+q)^100 ≤ (32:ℝ)^100*(1+L)^100*
    ((1+‖R⁻¹ • ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])‖)^100)⁻¹
  rw [←div_eq_mul_inv,le_div_iff₀ (by positivity),one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (1+q)^100)).mpr
  calc
    _ ≤ _ := hp
    _ = _ := by ac_rfl

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private def bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*u i+x 1*(u i)^2+x 2*(u i)^3+x 3*(u i)^4)‖^6

private theorem continuous_bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) :
    Continuous (bourgainCurveCellMoment S z u) := by
  unfold bourgainCurveCellMoment fordAdditiveCharacter
  fun_prop

private theorem integrable_bourgainCurveCellWeight {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹) := by
  have h := integrable_one_add_norm (E:=Fin 4 → ℝ) (μ:=volume) (r:=100) (by norm_num)
  have hi := h.comp_smul (inv_ne_zero hR.ne')
  have he (x : Fin 4 → ℝ) : (1+‖R⁻¹ • x‖)^(-(100:ℝ)) =
      ((1+‖R⁻¹ • x‖)^100)⁻¹ := by
    rw [Real.rpow_neg (by positivity),Real.rpow_ofNat]
  simpa only [he] using hi

private theorem integrable_bourgainCurveCellMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ =>
      ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
  exact (integrable_bourgainCurveCellWeight hR).mul_bdd
    (continuous_bourgainCurveCellMoment S z u).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => bourgain_character_six_bound S z
      (fun i => x 0*u i+x 1*(u i)^2+x 2*(u i)^3+x 3*(u i)^4)))

private theorem bourgainCurveCellFrame_shift_measurePreserving (a c δ ξ : ℝ) :
    MeasurePreserving
      (fun y : Fin 4 → ℝ => (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])
      volume volume :=
  (measurePreserving_add_right volume ![ξ/δ,0,0,0]).comp
    (bourgainCurveCellFrame_measurePreserving a c)

private theorem bourgainCurveCellFrame_shift_integral (a c δ ξ : ℝ)
    (f : (Fin 4 → ℝ) → ℝ) (hf : StronglyMeasurable f) :
    (∫ y : Fin 4 → ℝ, f ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])) =
      ∫ x : Fin 4 → ℝ, f x := by
  have hT := bourgainCurveCellFrame_shift_measurePreserving a c δ ξ
  have h := integral_map (μ:=volume) hT.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hT.map_eq] at h
  exact h.symm

private theorem bourgainCurveCellMoment_shift {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (c ξ : ℝ) {δ : ℝ} (hδ : δ ≠ 0)
    (x : Fin 4 → ℝ) :
    bourgainCurveCellMoment S z (fun i => c+δ*s i) (x+![ξ/δ,0,0,0]) =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        (x 0*(c+δ*s i)+x 1*(c+δ*s i)^2+x 2*(c+δ*s i)^3+
          x 3*(c+δ*s i)^4+ξ*s i)‖^6 := by
  unfold bourgainCurveCellMoment
  have he :
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((x+![ξ/δ,0,0,0]) 0*(c+δ*s i)+(x+![ξ/δ,0,0,0]) 1*(c+δ*s i)^2+
          (x+![ξ/δ,0,0,0]) 2*(c+δ*s i)^3+(x+![ξ/δ,0,0,0]) 3*(c+δ*s i)^4)‖ =
      ‖∑ i ∈ S, z i*fordAdditiveCharacter
        ((x 0*(c+δ*s i)+x 1*(c+δ*s i)^2+x 2*(c+δ*s i)^3+
          x 3*(c+δ*s i)^4+ξ*s i)+ξ*c/δ)‖ := by
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only [Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
      add_zero]
    field_simp
    ring
  rw [he,norm_bourgain_character_sum_add]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025

private def bourgainCurveCellBaseWeight (R : ℝ) (y : Fin 4 → ℝ) : ℝ :=
  parabolaSourceWeight R 0 0 (y 0) (y 1)*
    (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3)

private theorem bourgainCurveCellBaseWeight_nonneg (R : ℝ) (y : Fin 4 → ℝ) :
    0 ≤ bourgainCurveCellBaseWeight R y :=
  mul_nonneg (parabolaSourceWeight_nonneg _ _ _ _ _)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

private theorem integrable_bourgainCurveCellBaseWeight {R : ℝ} (hR : 0 < R) :
    Integrable (bourgainCurveCellBaseWeight R) := by
  let B := Icc (-R) R ×ˢ Icc (-R) R
  have hi : Integrable (B.indicator (fun _ : ℝ × ℝ => (1:ℝ))) :=
    (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top).integrable_indicator
      (measurableSet_Icc.prod measurableSet_Icc)
  have h := bourgainFourCoordinates_measurePreserving.integrable_comp_of_integrable
    ((integrable_parabolaSourceWeight hR 0 0).mul_prod hi)
  simpa only [bourgainFourCoordinates_apply,bourgainCurveCellBaseWeight,B,Function.comp_def] using h

private theorem bourgainCurveCell_transverse_mass {R : ℝ} (hR : 0 ≤ R) :
    (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
      (fun _ : ℝ × ℝ => (1:ℝ)) q) = 4*R^2 := by
  rw [integral_indicator (measurableSet_Icc.prod measurableSet_Icc),integral_const,
    smul_eq_mul,mul_one,measureReal_restrict_apply_univ]
  change (volume.prod volume).real (Icc (-R) R ×ˢ Icc (-R) R) = _
  rw [measureReal_prod_prod,Real.volume_real_Icc_of_le (by linarith),
    sub_neg_eq_add]
  ring

private theorem bourgainCurveCell_inner_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (u : ι → ℝ) {a c R δ : ℝ}
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hR : 0 < R) (hδ : 0 < δ) (ξ : ℝ) :
    (∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
      bourgainCurveCellMoment S z u
        ((bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0])) ≤
      (32:ℝ)^100*(1+|ξ|/(δ*R))^100*
        (∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
  let T := fun y : Fin 4 → ℝ => (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let K := (32:ℝ)^100*(1+|ξ|/(δ*R))^100
  have hcF : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous T := hcF.add continuous_const
  have hi₁ : Integrable (fun y => bourgainCurveCellBaseWeight R y*
      bourgainCurveCellMoment S z u (T y)) :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      ((continuous_bourgainCurveCellMoment S z u).comp hcT).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => bourgain_character_six_bound S z
        (fun i => T y 0*u i+T y 1*(u i)^2+T y 2*(u i)^3+T y 3*(u i)^4)))
  have hi₂ : Integrable (fun y => ((1+‖R⁻¹ • T y‖)^100)⁻¹*
      bourgainCurveCellMoment S z u (T y)) :=
    (bourgainCurveCellFrame_shift_measurePreserving a c δ ξ).integrable_comp_of_integrable
      (integrable_bourgainCurveCellMoment S z u hR)
  have hp (y : Fin 4 → ℝ) :
      bourgainCurveCellBaseWeight R y ≤ K*((1+‖R⁻¹ • T y‖)^100)⁻¹ := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · simp only [bourgainCurveCellBaseWeight,Set.indicator_of_mem hy,mul_one]
      exact bourgainCurveCellFrame_weight_bound ha hc hR hδ y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2) ξ
    · simp only [bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,mul_zero]
      dsimp [K]
      positivity
  have hm := integral_mono hi₁ (hi₂.const_mul K) (fun y => by
    have h := mul_le_mul_of_nonneg_right (hp y)
      (show 0 ≤ bourgainCurveCellMoment S z u (T y) by unfold bourgainCurveCellMoment; positivity)
    simpa only [mul_assoc] using h)
  rw [integral_const_mul] at hm
  have hf : StronglyMeasurable (fun x : Fin 4 → ℝ =>
      ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x) := by
    have hwc : Continuous (fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹) := by
      apply Continuous.inv₀
      · fun_prop
      · intro x
        positivity
    exact (hwc.mul (continuous_bourgainCurveCellMoment S z u)).stronglyMeasurable
  have he := bourgainCurveCellFrame_shift_integral a c δ ξ _ hf
  change (∫ y : Fin 4 → ℝ, ((1+‖R⁻¹ • T y‖)^100)⁻¹*
    bourgainCurveCellMoment S z u (T y)) = _ at he
  rw [he] at hm
  exact hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainQuartic_cell_return :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 → 1 ≤ δ*R →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*p.1+(c+δ*s i-a)^2*p.2)‖^6) ≤
        C/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          bourgainCurveCellMoment S z (fun i => c+δ*s i) x) := by
  obtain ⟨E,hE,hInv⟩ := exists_bourgainCurveCell_inverse_pointwise.{u}
  refine ⟨E*(32:ℝ)^100*Real.pi/4,by positivity,?_⟩
  intro ι S z s hs a c δ R ha hc hδ hδ₁ hR hrem hδR
  let u := fun i => c+δ*s i
  let T := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let P := fun p : ℝ × ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    ((u i-a)*p.1+(u i-a)^2*p.2)‖^6
  let F := fun y : Fin 4 → ℝ => bourgainCurveCellBaseWeight R y*P (y 0,y 1)
  let H := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    W ξ*bourgainCurveCellBaseWeight R y*bourgainCurveCellMoment S z u (T ξ y)
  let J := ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x
  have hJ : 0 ≤ J := integral_nonneg (fun x => by
    apply mul_nonneg (by positivity)
    unfold bourgainCurveCellMoment
    positivity)
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => (u i-a)*p.1+(u i-a)^2*p.2)
  have hiF : Integrable F :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      (hPc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hPb (y 0,y 1)))
  have hcFrame : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous (fun q : ℝ × (Fin 4 → ℝ) => T q.1 q.2) := by
    exact (hcFrame.comp continuous_snd).add (by dsimp [T]; fun_prop)
  have hcM : Continuous (fun q : ℝ × (Fin 4 → ℝ) =>
      bourgainCurveCellMoment S z u (T q.1 q.2)) :=
    (continuous_bourgainCurveCellMoment S z u).comp hcT
  have hiH : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hp := bourgainRemainderEnvelope_integrable.mul_prod
      (integrable_bourgainCurveCellBaseWeight hR)
    exact hp.mul_bdd hcM.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => bourgain_character_six_bound S z
        (fun i => T q.1 q.2 0*u i+T q.1 q.2 1*(u i)^2+
          T q.1 q.2 2*(u i)^3+T q.1 q.2 3*(u i)^4)))
  have hp (y : Fin 4 → ℝ) : F y ≤ E*(∫ ξ : ℝ, H ξ y) := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · have hm := hInv S z s hs a c δ R hc hδ.le hδ₁ hR.le hrem y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2)
      have he (ξ : ℝ) := bourgainCurveCellMoment_shift S z s c ξ hδ.ne'
        ((bourgainCurveCellFrame a c).mulVec y)
      have hmi : P (y 0,y 1) ≤ E*(∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        simpa only [P,W,u,T,he] using hm
      have hm' := mul_le_mul_of_nonneg_left hmi (bourgainCurveCellBaseWeight_nonneg R y)
      have heH : (∫ ξ : ℝ, H ξ y) = bourgainCurveCellBaseWeight R y*
          (∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp [H]
        ring
      rw [heH]
      simpa only [F,mul_left_comm] using hm'
    · simp only [F,H,bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,
        mul_zero,zero_mul,integral_zero,le_refl]
  have hmain := bourgain_kernel_setIntegral_bound
    (α:=Fin 4 → ℝ) (β:=ℝ) (μ:=volume) (ν:=volume)
    (B:=Set.univ) (C:=E) (f:=F) (H:=H)
    MeasurableSet.univ hiF.integrableOn
    (by simpa only [Measure.restrict_univ] using hiH) (fun y _ => hp y)
  simp only [setIntegral_univ] at hmain

  have hinner (ξ : ℝ) : (∫ y : Fin 4 → ℝ, H ξ y) ≤
      (32:ℝ)^100*J*(1+ξ^2)⁻¹ := by
    have hb := bourgainCurveCell_inner_bound S z u ha hc hR hδ ξ
    have heH : (∫ y : Fin 4 → ℝ, H ξ y) =
        W ξ*(∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
          bourgainCurveCellMoment S z u (T ξ y)) := by
      simp only [H,mul_assoc,integral_const_mul]
    rw [heH]
    calc
      _ ≤ W ξ*((32:ℝ)^100*(1+|ξ|/(δ*R))^100*J) :=
        mul_le_mul_of_nonneg_left hb (by dsimp [W]; positivity)
      _ = (32:ℝ)^100*J*(W ξ*(1+|ξ|/(δ*R))^100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (bourgain_modulation_envelope hδR ξ)
        (mul_nonneg (by positivity) hJ)
  have hiOuter : Integrable (fun ξ : ℝ => ∫ y : Fin 4 → ℝ, H ξ y) :=
    hiH.integral_prod_left
  have hout := integral_mono hiOuter
    (integrable_inv_one_add_sq.const_mul ((32:ℝ)^100*J)) hinner
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hout
  have hleft : (∫ y : Fin 4 → ℝ, F y) =
      4*R^2*(∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p) := by
    calc
      _ = ∫ y : Fin 4 → ℝ,
          (parabolaSourceWeight R 0 0 (y 0) (y 1)*P (y 0,y 1))*
            (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3) := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F,bourgainCurveCellBaseWeight]
        ring
      _ = (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*
          (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
            (fun _ : ℝ × ℝ => (1:ℝ)) q) :=
        bourgainFourCoordinates_integral_product
          (fun p : ℝ × ℝ => parabolaSourceWeight R 0 0 p.1 p.2*P p)
          ((Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)))
      _ = _ := by rw [bourgainCurveCell_transverse_mass hR.le]; ring
  rw [hleft] at hmain
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left hout hE.le)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  change (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*R^2 ≤ _
  nlinarith only [hfinal]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem bourgainSourcePermutation_norm (x : Fin 4 → ℝ) :
    ‖bourgainSourcePermutation x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    fin_cases i <;>
      first | exact norm_le_pi_norm x 3 | exact norm_le_pi_norm x 0 |
        exact norm_le_pi_norm x 2 | exact norm_le_pi_norm x 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (bourgainSourcePermutation x))).mpr
    intro i
    fin_cases i <;>
      first | exact norm_le_pi_norm (bourgainSourcePermutation x) 1 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 3 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 2 |
        exact norm_le_pi_norm (bourgainSourcePermutation x) 0

/-- Return each actual parabolic cell moment to the literal four-dimensional
source-curve moment. The inverse remainder multiplier, radial-weight
comparison and transverse averaging are derived, including the R^-2 factor. -/
theorem exists_bourgainSourceCurve_cell_return :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ),
      (∀ i ∈ S, 0 ≤ w i) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 → 1 ≤ δ*R →
      (∀ i ∈ S, |Real.sqrt (w i)-c| ≤ δ) →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((Real.sqrt (w i)-a)*p.1+(Real.sqrt (w i)-a)^2*p.2)‖^6) ≤
        C/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainQuartic_cell_return.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z w hw a c δ R ha hc hδ hδ₁ hR hrem hδR hwindow
  let s := fun i => (Real.sqrt (w i)-c)/δ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    have hh := abs_le.mp (hwindow i hi)
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith [hh.1]
    · apply (div_le_iff₀ hδ).mpr
      linarith [hh.2]
  have hbase (i : ι) : c+δ*s i = Real.sqrt (w i) := by
    dsimp [s]
    field_simp
    ring
  have hmain := h S z s hs a c δ R ha hc hδ hδ₁ hR hrem hδR
  simp_rw [hbase] at hmain
  let f := fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*
    bourgainCurveCellMoment S z (fun i => Real.sqrt (w i)) x
  have he : (∫ x : Fin 4 → ℝ, f x) =
      ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6 := by
    calc
      _ = ∫ x : Fin 4 → ℝ, f (bourgainSourcePermutation x) :=
        (bourgainSourcePermutation_measurePreserving.integral_comp
          bourgainSourcePermutation.measurableEmbedding f).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [f]
        rw [norm_smul,bourgainSourcePermutation_norm,←norm_smul]
        apply congrArg (fun v : ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*v)
        unfold bourgainCurveCellMoment
        apply congrArg (fun v : ℂ => ‖v‖^6)
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
        simpa only [bourgainSourcePermutation_apply,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val] using
          (bourgain_source_quartic_phase (hw i hi) x).symm
  change _ ≤ C/R^2*(∫ x : Fin 4 → ℝ, f x) at hmain
  rw [he] at hmain
  exact hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
/-- Local bilinear decoupling for the literal source curve, with actual
four-dimensional radial curve-cell moments on the right. Both Taylor scales,
the frequency partition and the physical scale are explicitly linked. -/
theorem exists_bourgainSourceCurve_local_cell_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ (n : ℕ) (a b σ R : ℝ),
      0 ≤ a → a+σ ≤ 1 → 0 ≤ b → b+σ ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 < R → 5*R*σ^3 ≤ 1 →
      5*(10*R)*(σ/(2:ℝ)^n)^3 ≤ 1 → 1 ≤ (σ/(2:ℝ)^n)*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
              x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
          ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
            (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
              x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
          C*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*
            (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
              ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
                (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+
                  x 3*Real.sqrt (w j i))‖^6)*
            (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
              ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
                (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+
                  x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨D,hD,hSource⟩ := exists_bourgainSourceCurve_parabolic_cell_bound.{u} hε
  obtain ⟨E,hE,hReturn⟩ := exists_bourgainSourceCurve_cell_return.{u}
  refine ⟨D*E^2,by positivity,?_⟩
  intro n a b σ R ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth
    ι τ S V z c w v hw hv hwgrid hvgrid
  let δ := σ/(2:ℝ)^n
  let W := fun p : ℝ × ℝ => parabolaSourceWeight (10*R) 0 0 p.1 p.2
  let J {κ : Type u} (K : Finset κ) (q : κ → ℂ) (f : κ → ℝ) :=
    ∫ x : Fin 4 → ℝ, ((1+‖(10*R)⁻¹ • x‖)^100)⁻¹*
      ‖∑ i ∈ K, q i*fordAdditiveCharacter
        (x 0*f i+x 1*(f i)^2+x 2*(f i)^((3:ℝ)/2)+x 3*Real.sqrt (f i))‖^6
  have hδ : 0 < δ := div_pos hσ (by positivity)
  have hδσ : δ ≤ σ := div_le_self hσ.le (one_le_pow₀ (by norm_num))
  have hδ₁ : δ ≤ 1 := hδσ.trans hσ₁
  have hσR : 1 ≤ σ*(10*R) :=
    hδR.trans (mul_le_mul_of_nonneg_right hδσ (by positivity))
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hbabs : |b| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hmain := hSource n a b σ R haabs hbabs hab hσ hσ₁ hR.le hrem hσR hwidth
    ι τ S V z c w v hw hv hwgrid hvgrid
  have hQ (κ : Type u) (K : Fin (2^n) → Finset κ)
      (q : Fin (2^n) → κ → ℂ) (f : Fin (2^n) → κ → ℝ)
      (d : ℝ) (hd : 0 ≤ d) (hdσ : d+σ ≤ 1)
      (hf : ∀ j, ∀ i ∈ K j, 0 ≤ f j i)
      (hgrid : ∀ j, ∀ i ∈ K j, Real.sqrt (f j i) ∈ Icc
        (d+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (d+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) :
      (∑ j, (parabolaWeightedSixNorm W (K j) (q j)
        (fun i => Real.sqrt (f j i)-d))^2)^3 ≤
        ((2:ℝ)^n)^2*(E/(10*R)^2)*(∑ j, J (K j) (q j) (f j)) := by
    have hdabs : |d| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    have hcell (j : Fin (2^n)) :
        (parabolaWeightedSixNorm W (K j) (q j)
          (fun i => Real.sqrt (f j i)-d))^6 ≤ E/(10*R)^2*J (K j) (q j) (f j) := by
      let e := d+σ*((j:ℕ)/((2^n:ℕ):ℝ))
      have hj : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ) := by positivity
      have hj₁ : ((j:ℕ):ℝ)/((2^n:ℕ):ℝ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Nat.le_of_lt j.isLt
      have he₀ : 0 ≤ e := add_nonneg hd (mul_nonneg hσ.le hj)
      have he₁ : e ≤ 1 := by
        have hh := mul_le_mul_of_nonneg_left hj₁ hσ.le
        dsimp [e]
        linarith
      have heabs : |e| ≤ 1 := abs_le.mpr ⟨by linarith,he₁⟩
      have heupper : d+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)) = e+δ := by
        dsimp [e,δ]
        push_cast
        ring
      have hwindow : ∀ i ∈ K j, |Real.sqrt (f j i)-e| ≤ δ := by
        intro i hi
        have hl := (hgrid j i hi).1
        have hh := (hgrid j i hi).2
        rw [heupper] at hh
        change e ≤ Real.sqrt (f j i) at hl
        rw [abs_of_nonneg (sub_nonneg.mpr hl)]
        linarith
      have hr := hReturn (K j) (q j) (f j) (hf j) d e δ (10*R) hdabs heabs
        hδ hδ₁ (by positivity) hfine hδR hwindow
      have hn := parabolaWeightedSixNorm_pow_six W
        (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
        (integrable_parabolaSourceWeight (by positivity : 0 < 10*R) 0 0)
        (K j) (q j) (fun i => Real.sqrt (f j i)-d)
      have hepow (x : ℝ) : x^2*x^4=x^6 := by ring
      rw [hn]
      simpa only [parabolaWeightedBilinearMoment,sargosPlanarSum,mul_assoc,hepow,W,J] using hr
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
      (f:=fun j => (parabolaWeightedSixNorm W (K j) (q j)
        (fun i => Real.sqrt (f j i)-d))^2) (fun _ _ => sq_nonneg _) 2
    norm_num only [show (2+1:ℕ)=3 by omega,←pow_mul,
      show (2*3:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin,
      Nat.cast_pow,Nat.cast_ofNat] at hh
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcell j)
    rw [←Finset.mul_sum] at hsum
    calc
      _ ≤ ((2:ℝ)^n)^2*∑ j, (parabolaWeightedSixNorm W (K j) (q j)
          (fun i => Real.sqrt (f j i)-d))^6 := by
        simpa only [pow_mul] using hh
      _ ≤ ((2:ℝ)^n)^2*(E/(10*R)^2*(∑ j, J (K j) (q j) (f j))) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg ((2:ℝ)^n))
      _ = _ := by ring

  have hS := hQ ι S z w a ha haσ hw hwgrid
  have hV := hQ τ V c v b hb hbσ hv hvgrid
  have hJV : 0 ≤ ∑ j, J (V j) (c j) (v j) := by
    apply Finset.sum_nonneg
    intro j hj
    apply integral_nonneg
    intro x
    positivity
  have hprod := mul_le_mul hS hV (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ D*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹ by positivity)
  have hpow : (2:ℝ)^(ε*n)*((2:ℝ)^n)^4 = (2:ℝ)^((ε+4)*n) := by
    have he : ((2:ℝ)^n)^4 = (2:ℝ)^((4:ℝ)*n) := by
      rw [←Real.rpow_natCast (2:ℝ) n,←Real.rpow_mul_natCast (by norm_num)]
      congr 1
      push_cast
      ring
    rw [he,←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have halg (A B : ℝ) :
      (D*(2:ℝ)^(ε*n)*(6*(b-a)^4)⁻¹)*
        ((((2:ℝ)^n)^2*(E/(10*R)^2)*A)*(((2:ℝ)^n)^2*(E/(10*R)^2)*B)) =
      (D*E^2)*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*A*B := by
    rw [←hpow]
    ring
  calc
    _ ≤ _ := hmain
    _ ≤ _ := by simpa only [W,mul_assoc] using hm
    _ = _ := halg _ _

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private def bourgainRadialWeight (R : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ((1+‖R⁻¹ • x‖)^100)⁻¹

private theorem bourgainRadialWeight_nonneg (R : ℝ) (x : Fin 4 → ℝ) :
    0 ≤ bourgainRadialWeight R x := by
  unfold bourgainRadialWeight
  positivity

private theorem bourgainRadialWeight_le_one (R : ℝ) (x : Fin 4 → ℝ) :
    bourgainRadialWeight R x ≤ 1 := by
  unfold bourgainRadialWeight
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by linarith [norm_nonneg (R⁻¹ • x)])

private theorem continuous_bourgainRadialWeight (R : ℝ) :
    Continuous (bourgainRadialWeight R) := by
  unfold bourgainRadialWeight
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

private theorem bourgainRadialWeight_distance {R : ℝ} (hR : 0 < R) (x : Fin 4 → ℝ) :
    bourgainRadialWeight R x = ((1+‖x‖/R)^100)⁻¹ := by
  unfold bourgainRadialWeight
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR]
  congr 2
  rw [div_eq_mul_inv,mul_comm]

private theorem integral_bourgainRadialWeight {R : ℝ} (hR : 0 ≤ R) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x) =
      R^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg
    (volume : Measure (Fin 4 → ℝ)) (fun x : Fin 4 → ℝ => ((1+‖x‖)^100)⁻¹) hR
  simpa only [Module.finrank_pi_fintype,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.cast_ofNat,mul_one,
    bourgainRadialWeight,inv_one,one_smul] using h

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgain_inverse_power_ratio {p q L : ℝ}
    (hp : 0 < p) (hq : 0 < q) (h : q ≤ L*p) :
    (p^100)⁻¹ ≤ L^100*(q^100)⁻¹ := by
  rw [←div_eq_mul_inv,le_div_iff₀ (pow_pos hq 100),inv_mul_eq_div,
    div_le_iff₀ (pow_pos hp 100)]
  simpa only [mul_pow] using pow_le_pow_left₀ hq.le h 100

private theorem bourgain_scalar_weight_product {K R X A B : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (hX : 0 ≤ X) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htriangle : X ≤ A+B) :
    ((1+A/K)^100)⁻¹*((1+B/R)^100)⁻¹ ≤
      (4:ℝ)^100*((1+X/R)^100)⁻¹*
        (((1+A/K)^100)⁻¹+(K/R)^4*((1+B/R)^100)⁻¹) := by
  have hR : 0 < R := hK.trans_le hKR
  have hp : 0 < 1+A/K := by positivity
  have hq : 0 < 1+B/R := by positivity
  have hr : 0 < 1+X/R := by positivity
  have hratio₀ : 0 ≤ K/R := by positivity
  have hratio₁ : K/R ≤ 1 := (div_le_one hR).mpr hKR
  have hW : ((1+B/R)^100)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [div_nonneg hB hR.le]))
  have hfirst (hh : ((1+B/R)^100)⁻¹ ≤ (4:ℝ)^100*((1+X/R)^100)⁻¹) :
      ((1+A/K)^100)⁻¹*((1+B/R)^100)⁻¹ ≤
        (4:ℝ)^100*((1+X/R)^100)⁻¹*
          (((1+A/K)^100)⁻¹+(K/R)^4*((1+B/R)^100)⁻¹) := by
    calc
      _ ≤ ((1+A/K)^100)⁻¹*((4:ℝ)^100*((1+X/R)^100)⁻¹) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = (4:ℝ)^100*((1+X/R)^100)⁻¹*((1+A/K)^100)⁻¹ := by ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  by_cases hXB : X ≤ 2*B
  · have hdiv : X/R ≤ 2*(B/R) := by
      calc
        _ ≤ (2*B)/R := div_le_div_of_nonneg_right hXB hR.le
        _ = _ := by ring
    apply hfirst
    have hh := bourgain_inverse_power_ratio hq hr
      (show 1+X/R ≤ 4*(1+B/R) by nlinarith [div_nonneg hB hR.le])
    exact hh
  by_cases hXR : X ≤ R
  · have hxdiv : X/R ≤ 1 := (div_le_one hR).mpr hXR
    have hh := bourgain_inverse_power_ratio (by norm_num : (0:ℝ)<1) hr
      (show 1+X/R ≤ (4:ℝ)*1 by linarith)
    simp only [one_pow,inv_one] at hh
    exact hfirst (hW.trans hh)
  have hXA : X ≤ 2*A := by linarith
  have hden : 1+X/R ≤ (4*K/R)*(1+A/K) := by
    have he : (4*K/R)*(1+A/K) = (4*K+4*A)/R := by field_simp
    rw [he]
    apply (le_div_iff₀ hR).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hR.ne']
    linarith
  have hh := bourgain_inverse_power_ratio hp hr hden
  have hpow : (K/R)^100 ≤ (K/R)^4 := by
    rw [show (100:ℕ)=4+96 by omega,pow_add]
    have h := pow_le_one₀ hratio₀ hratio₁ (n:=96)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (pow_nonneg hratio₀ 4)
  have hlast : ((1+A/K)^100)⁻¹ ≤ (4:ℝ)^100*(K/R)^4*((1+X/R)^100)⁻¹ := by
    calc
      _ ≤ _ := hh
      _ = (4:ℝ)^100*(K/R)^100*((1+X/R)^100)⁻¹ := by
        rw [show 4*K/R=4*(K/R) by ring,mul_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  calc
    _ ≤ ((4:ℝ)^100*(K/R)^4*((1+X/R)^100)⁻¹)*((1+B/R)^100)⁻¹ :=
      mul_le_mul_of_nonneg_right hlast (by positivity)
    _ = (4:ℝ)^100*((1+X/R)^100)⁻¹*((K/R)^4*((1+B/R)^100)⁻¹) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainRadialWeight_product {K R : ℝ}
    (hK : 0 < K) (hKR : K ≤ R) (x y : Fin 4 → ℝ) :
    bourgainRadialWeight K y*bourgainRadialWeight R (x-y) ≤
      (4:ℝ)^100*bourgainRadialWeight R x*
        (bourgainRadialWeight K y+(K/R)^4*bourgainRadialWeight R (x-y)) := by
  have hR : 0 < R := hK.trans_le hKR
  have ht : ‖x‖ ≤ ‖y‖+‖x-y‖ := by
    calc
      _ = ‖y+(x-y)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  simpa only [bourgainRadialWeight_distance hK,bourgainRadialWeight_distance hR] using
    bourgain_scalar_weight_product hK hKR (norm_nonneg x) (norm_nonneg y)
      (norm_nonneg (x-y)) ht

private theorem exists_bourgainRadialWeight_convolution :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R → ∀ x : Fin 4 → ℝ,
      (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*bourgainRadialWeight R (x-y)) ≤
        C*K^4*bourgainRadialWeight R x := by
  let M := ∫ y : Fin 4 → ℝ, bourgainRadialWeight 1 y
  have hM : 0 ≤ M := integral_nonneg (bourgainRadialWeight_nonneg 1)
  refine ⟨2*(4:ℝ)^100*(M+1),by positivity,?_⟩
  intro K R hK hKR x
  have hR : 0 < R := hK.trans_le hKR
  have hiK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hiR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hiShift := hiR.comp_sub_left x
  have hiProd : Integrable (fun y : Fin 4 → ℝ =>
      bourgainRadialWeight K y*bourgainRadialWeight R (x-y)) :=
    hiK.mul_bdd ((continuous_bourgainRadialWeight R).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by
        rw [Real.norm_eq_abs,abs_of_nonneg (bourgainRadialWeight_nonneg _ _)]
        exact bourgainRadialWeight_le_one _ _))
  have hm := integral_mono hiProd
    ((hiK.add (hiShift.const_mul ((K/R)^4))).const_mul
      ((4:ℝ)^100*bourgainRadialWeight R x))
    (bourgainRadialWeight_product hK hKR x)
  simp only [Pi.add_apply] at hm
  rw [integral_const_mul,integral_add hiK (hiShift.const_mul ((K/R)^4)),
    integral_const_mul,integral_sub_left_eq_self _ volume x,
    integral_bourgainRadialWeight hK.le,integral_bourgainRadialWeight hR.le] at hm
  have he : (K/R)^4*R^4 = K^4 := by
    rw [←mul_pow,div_mul_cancel₀ _ hR.ne']
  calc
    _ ≤ _ := hm
    _ = 2*(4:ℝ)^100*M*K^4*bourgainRadialWeight R x := by
      rw [←mul_assoc ((K/R)^4) (R^4) M,he]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (bourgainRadialWeight_nonneg _ _)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hK.le 4)
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem exists_bourgainRadialWeight_shift_average :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ (f : (Fin 4 → ℝ) → ℝ) (M : ℝ), Continuous f →
      (∀ x, 0 ≤ f x) → (∀ x, ‖f x‖ ≤ M) →
      (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+z))) ≤
        C*K^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f x) := by
  obtain ⟨C,hC,hconv⟩ := exists_bourgainRadialWeight_convolution
  refine ⟨C,hC,?_⟩
  intro K R hK hKR f M hf hf₀ hfM
  have hR : 0 < R := hK.trans_le hKR
  have hiK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hiR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hiBase : Integrable (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K q.1*bourgainRadialWeight R (q.2-q.1)) (volume.prod volume) := by
    have h := (measurePreserving_prod_neg_add
      (volume : Measure (Fin 4 → ℝ)) (volume : Measure (Fin 4 → ℝ))).integrable_comp_of_integrable
        (hiK.mul_prod hiR)
    simpa only [Function.comp_def,sub_eq_add_neg,add_comm] using h
  have hiH : Integrable (fun q : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K q.1*bourgainRadialWeight R (q.2-q.1)*f q.2)
      (volume.prod volume) :=
    hiBase.mul_bdd (hf.comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hfM q.2))
  have he (z : Fin 4 → ℝ) :
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+z)) =
        ∫ y : Fin 4 → ℝ, bourgainRadialWeight R (y-z)*f y := by
    calc
      _ = ∫ x : Fin 4 → ℝ, bourgainRadialWeight R ((x+z)-z)*f (x+z) := by
        simp only [add_sub_cancel_right]
      _ = _ := integral_add_right_eq_self
        (fun y : Fin 4 → ℝ => bourgainRadialWeight R (y-z)*f y) z
  have hiLeft : Integrable (fun y : Fin 4 → ℝ =>
      (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*bourgainRadialWeight R (y-z))*f y) := by
    simpa only [integral_mul_const] using hiH.integral_prod_right
  have hiRight := (hiR.mul_bdd hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hfM)).const_mul (C*K^4)
  have hm := integral_mono hiLeft hiRight (fun y => by
    have h := mul_le_mul_of_nonneg_right (hconv K R hK hKR y) (hf₀ y)
    simpa only [mul_assoc] using h)
  rw [integral_const_mul] at hm
  calc
    _ = ∫ z : Fin 4 → ℝ, ∫ y : Fin 4 → ℝ,
        bourgainRadialWeight K z*bourgainRadialWeight R (y-z)*f y := by
      apply integral_congr_ae
      filter_upwards with z
      rw [he,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = ∫ y : Fin 4 → ℝ, ∫ z : Fin 4 → ℝ,
        bourgainRadialWeight K z*bourgainRadialWeight R (y-z)*f y :=
      integral_integral_swap hiH
    _ = ∫ y : Fin 4 → ℝ,
        (∫ z : Fin 4 → ℝ, bourgainRadialWeight K z*bourgainRadialWeight R (y-z))*f y := by
      simp only [integral_mul_const]
    _ ≤ _ := hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Averaging actual translated source-curve cell moments across a smaller
physical scale costs its derived four-dimensional volume factor. -/
theorem exists_bourgainSourceCurve_weighted_average :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ),
      (∫ y : Fin 4 → ℝ, ((1+‖K⁻¹ • y‖)^100)⁻¹*
        (∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, (z i*fordAdditiveCharacter
            (y 0*w i+y 1*(w i)^2+y 2*(w i)^((3:ℝ)/2)+y 3*Real.sqrt (w i)))*
              fordAdditiveCharacter
                (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6)) ≤
        C*K^4*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainRadialWeight_shift_average
  refine ⟨C,hC,?_⟩
  intro K R hK hKR ι S z w
  let F := fun x : Fin 4 → ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6
  have hFc : Continuous F := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hF₀ (x : Fin 4 → ℝ) : 0 ≤ F x := by dsimp [F]; positivity
  have hFb (x : Fin 4 → ℝ) : ‖F x‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z
      (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))
  have hsum (x y : Fin 4 → ℝ) :
      (∑ i ∈ S, (z i*fordAdditiveCharacter
        (y 0*w i+y 1*(w i)^2+y 2*(w i)^((3:ℝ)/2)+y 3*Real.sqrt (w i)))*
          fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))) =
      ∑ i ∈ S, z i*fordAdditiveCharacter
        ((x+y) 0*w i+(x+y) 1*(w i)^2+(x+y) 2*(w i)^((3:ℝ)/2)+
          (x+y) 3*Real.sqrt (w i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_assoc,←fordAdditiveCharacter_add]
    apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
    simp only [Pi.add_apply]
    ring
  have hm := h K R hK hKR F ((∑ i ∈ S, ‖z i‖)^6) hFc hF₀ hFb
  simpa only [bourgainRadialWeight,F,hsum] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgain_modulation_envelope_general {L : ℝ} (hL : 0 < L) (ξ : ℝ) :
    ((1+|ξ|)^102)⁻¹*(1+|ξ|/L)^100 ≤
      (1+L⁻¹)^100*(1+ξ^2)⁻¹ := by
  have hbase : 1+|ξ|/L ≤ (1+L⁻¹)*(1+|ξ|) := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hL,abs_nonneg ξ]
  have hp := pow_le_pow_left₀ (by positivity) hbase 100
  rw [mul_pow] at hp
  have henv := bourgain_modulation_envelope (R:=1) (by norm_num) ξ
  simp only [div_one] at henv
  calc
    _ ≤ ((1+|ξ|)^102)⁻¹*((1+L⁻¹)^100*(1+|ξ|)^100) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (1+L⁻¹)^100*(((1+|ξ|)^102)⁻¹*(1+|ξ|)^100) := by ac_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left henv (by positivity)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators Matrix
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainQuartic_cell_return_quantitative :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
      (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((c+δ*s i-a)*p.1+(c+δ*s i-a)^2*p.2)‖^6) ≤
        C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          bourgainCurveCellMoment S z (fun i => c+δ*s i) x) := by
  obtain ⟨E,hE,hInv⟩ := exists_bourgainCurveCell_inverse_pointwise.{u}
  refine ⟨E*(32:ℝ)^100*Real.pi/4,by positivity,?_⟩
  intro ι S z s hs a c δ R ha hc hδ hδ₁ hR hrem
  let u := fun i => c+δ*s i
  let T := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    (bourgainCurveCellFrame a c).mulVec y+![ξ/δ,0,0,0]
  let W := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let P := fun p : ℝ × ℝ => ‖∑ i ∈ S, z i*fordAdditiveCharacter
    ((u i-a)*p.1+(u i-a)^2*p.2)‖^6
  let F := fun y : Fin 4 → ℝ => bourgainCurveCellBaseWeight R y*P (y 0,y 1)
  let H := fun (ξ : ℝ) (y : Fin 4 → ℝ) =>
    W ξ*bourgainCurveCellBaseWeight R y*bourgainCurveCellMoment S z u (T ξ y)
  let J := ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*bourgainCurveCellMoment S z u x
  let L := (1+(δ*R)⁻¹)^100
  have hJ : 0 ≤ J := integral_nonneg (fun x => by
    apply mul_nonneg (by positivity)
    unfold bourgainCurveCellMoment
    positivity)
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hPb (p : ℝ × ℝ) : ‖P p‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => (u i-a)*p.1+(u i-a)^2*p.2)
  have hiF : Integrable F :=
    (integrable_bourgainCurveCellBaseWeight hR).mul_bdd
      (hPc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => hPb (y 0,y 1)))
  have hcFrame : Continuous ((bourgainCurveCellFrame a c).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainCurveCellFrame a c))
    exact LinearMap.continuous_on_pi _
  have hcT : Continuous (fun q : ℝ × (Fin 4 → ℝ) => T q.1 q.2) := by
    exact (hcFrame.comp continuous_snd).add (by dsimp [T]; fun_prop)
  have hcM : Continuous (fun q : ℝ × (Fin 4 → ℝ) =>
      bourgainCurveCellMoment S z u (T q.1 q.2)) :=
    (continuous_bourgainCurveCellMoment S z u).comp hcT
  have hiH : Integrable (Function.uncurry H) (volume.prod volume) := by
    have hp := bourgainRemainderEnvelope_integrable.mul_prod
      (integrable_bourgainCurveCellBaseWeight hR)
    exact hp.mul_bdd hcM.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => bourgain_character_six_bound S z
        (fun i => T q.1 q.2 0*u i+T q.1 q.2 1*(u i)^2+
          T q.1 q.2 2*(u i)^3+T q.1 q.2 3*(u i)^4)))
  have hp (y : Fin 4 → ℝ) : F y ≤ E*(∫ ξ : ℝ, H ξ y) := by
    by_cases hy : (y 2,y 3) ∈ Icc (-R) R ×ˢ Icc (-R) R
    · have hm := hInv S z s hs a c δ R hc hδ.le hδ₁ hR.le hrem y
        (abs_le.mpr hy.1) (abs_le.mpr hy.2)
      have he (ξ : ℝ) := bourgainCurveCellMoment_shift S z s c ξ hδ.ne'
        ((bourgainCurveCellFrame a c).mulVec y)
      have hmi : P (y 0,y 1) ≤ E*(∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        simpa only [P,W,u,T,he] using hm
      have hm' := mul_le_mul_of_nonneg_left hmi (bourgainCurveCellBaseWeight_nonneg R y)
      have heH : (∫ ξ : ℝ, H ξ y) = bourgainCurveCellBaseWeight R y*
          (∫ ξ : ℝ, W ξ*bourgainCurveCellMoment S z u (T ξ y)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with ξ
        dsimp [H]
        ring
      rw [heH]
      simpa only [F,mul_left_comm] using hm'
    · simp only [F,H,bourgainCurveCellBaseWeight,Set.indicator_of_notMem hy,
        mul_zero,zero_mul,integral_zero,le_refl]
  have hmain := bourgain_kernel_setIntegral_bound
    (α:=Fin 4 → ℝ) (β:=ℝ) (μ:=volume) (ν:=volume)
    (B:=Set.univ) (C:=E) (f:=F) (H:=H)
    MeasurableSet.univ hiF.integrableOn
    (by simpa only [Measure.restrict_univ] using hiH) (fun y _ => hp y)
  simp only [setIntegral_univ] at hmain

  have hinner (ξ : ℝ) : (∫ y : Fin 4 → ℝ, H ξ y) ≤
      (32:ℝ)^100*J*L*(1+ξ^2)⁻¹ := by
    have hb := bourgainCurveCell_inner_bound S z u ha hc hR hδ ξ
    have heH : (∫ y : Fin 4 → ℝ, H ξ y) =
        W ξ*(∫ y : Fin 4 → ℝ, bourgainCurveCellBaseWeight R y*
          bourgainCurveCellMoment S z u (T ξ y)) := by
      simp only [H,mul_assoc,integral_const_mul]
    rw [heH]
    calc
      _ ≤ W ξ*((32:ℝ)^100*(1+|ξ|/(δ*R))^100*J) :=
        mul_le_mul_of_nonneg_left hb (by dsimp [W]; positivity)
      _ = (32:ℝ)^100*J*(W ξ*(1+|ξ|/(δ*R))^100) := by ring
      _ ≤ (32:ℝ)^100*J*(L*(1+ξ^2)⁻¹) :=
        mul_le_mul_of_nonneg_left (bourgain_modulation_envelope_general (mul_pos hδ hR) ξ)
          (mul_nonneg (by positivity) hJ)
      _ = _ := by ring
  have hiOuter : Integrable (fun ξ : ℝ => ∫ y : Fin 4 → ℝ, H ξ y) :=
    hiH.integral_prod_left
  have hout := integral_mono hiOuter
    (integrable_inv_one_add_sq.const_mul ((32:ℝ)^100*J*L)) hinner
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hout
  have hleft : (∫ y : Fin 4 → ℝ, F y) =
      4*R^2*(∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p) := by
    calc
      _ = ∫ y : Fin 4 → ℝ,
          (parabolaSourceWeight R 0 0 (y 0) (y 1)*P (y 0,y 1))*
            (Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (y 2,y 3) := by
        apply integral_congr_ae
        filter_upwards with y
        dsimp [F,bourgainCurveCellBaseWeight]
        ring
      _ = (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*
          (∫ q : ℝ × ℝ, (Icc (-R) R ×ˢ Icc (-R) R).indicator
            (fun _ : ℝ × ℝ => (1:ℝ)) q) :=
        bourgainFourCoordinates_integral_product
          (fun p : ℝ × ℝ => parabolaSourceWeight R 0 0 p.1 p.2*P p)
          ((Icc (-R) R ×ˢ Icc (-R) R).indicator (fun _ : ℝ × ℝ => (1:ℝ)))
      _ = _ := by rw [bourgainCurveCell_transverse_mass hR.le]; ring
  rw [hleft] at hmain
  have hfinal := hmain.trans (mul_le_mul_of_nonneg_left hout hE.le)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  change (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*P p)*R^2 ≤
    (E*(32:ℝ)^100*Real.pi/4)*L*J
  nlinarith only [hfinal]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainSourceCurve_cell_return_quantitative :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ),
      (∀ i ∈ S, 0 ≤ w i) →
      ∀ (a c δ R : ℝ), |a| ≤ 1 → |c| ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < R → 5*R*δ^3 ≤ 1 →
      (∀ i ∈ S, |Real.sqrt (w i)-c| ≤ δ) →
      (∫ p : ℝ × ℝ, parabolaSourceWeight R 0 0 p.1 p.2*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          ((Real.sqrt (w i)-a)*p.1+(Real.sqrt (w i)-a)^2*p.2)‖^6) ≤
        C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter
            (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainQuartic_cell_return_quantitative.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z w hw a c δ R ha hc hδ hδ₁ hR hrem hwindow
  let s := fun i => (Real.sqrt (w i)-c)/δ
  have hs : ∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1 := by
    intro i hi
    have hh := abs_le.mp (hwindow i hi)
    constructor
    · apply (le_div_iff₀ hδ).mpr
      linarith [hh.1]
    · apply (div_le_iff₀ hδ).mpr
      linarith [hh.2]
  have hbase (i : ι) : c+δ*s i = Real.sqrt (w i) := by
    dsimp [s]
    field_simp
    ring
  have hmain := h S z s hs a c δ R ha hc hδ hδ₁ hR hrem
  simp_rw [hbase] at hmain
  let f := fun x : Fin 4 → ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*
    bourgainCurveCellMoment S z (fun i => Real.sqrt (w i)) x
  have he : (∫ x : Fin 4 → ℝ, f x) =
      ∫ x : Fin 4 → ℝ, ((1+‖R⁻¹ • x‖)^100)⁻¹*
        ‖∑ i ∈ S, z i*fordAdditiveCharacter
          (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6 := by
    calc
      _ = ∫ x : Fin 4 → ℝ, f (bourgainSourcePermutation x) :=
        (bourgainSourcePermutation_measurePreserving.integral_comp
          bourgainSourcePermutation.measurableEmbedding f).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [f]
        rw [norm_smul,bourgainSourcePermutation_norm,←norm_smul]
        apply congrArg (fun v : ℝ => ((1+‖R⁻¹ • x‖)^100)⁻¹*v)
        unfold bourgainCurveCellMoment
        apply congrArg (fun v : ℂ => ‖v‖^6)
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
        simpa only [bourgainSourcePermutation_apply,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val] using
          (bourgain_source_quartic_phase (hw i hi) x).symm
  change _ ≤ C*(1+(δ*R)⁻¹)^100/R^2*(∫ x : Fin 4 → ℝ, f x) at hmain
  rw [he] at hmain
  exact hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainParabola_unit_average :
    ∃ C > (0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (x : ι → ℝ),
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment S S
          (fun i => z i*fordAdditiveCharacter (ξ*x i))
          (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0) ≤
        C*(∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2*
          ‖∑ i ∈ S, z i*fordAdditiveCharacter (x i*p.1+(x i)^2*p.2)‖^6) := by
  obtain ⟨K,hK,hcomp⟩ := parabolaRapidWeight_le_sourceWeight
  refine ⟨K*Real.pi,by positivity,?_⟩
  intro ι S z x
  let W := fun p : ℝ × ℝ => parabolaSourceWeight 1 0 0 p.1 p.2
  let J := parabolaSourceBilinearMoment S S z z x x 1 0 0
  have hW₀ : ∀ p, 0 ≤ W p := fun p => parabolaSourceWeight_nonneg _ _ _ _ _
  have hW : Integrable W := integrable_parabolaSourceWeight (by norm_num) 0 0
  have hJ : 0 ≤ J := integral_nonneg (fun p => by
    apply mul_nonneg
    · exact mul_nonneg (hW₀ p) (by positivity)
    · positivity)
  have hm (ξ : ℝ) :
      parabolaSourceBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0 ≤
          (1+|ξ|)^100*J := by
    have hn := pow_le_pow_left₀ (sq_nonneg _)
      (parabola_sourceWeight_modulation S z x (by norm_num : (0:ℝ)<1) 0 0 ξ) 3
    rw [mul_pow,←pow_mul,←pow_mul] at hn
    have hr := Real.rpow_inv_natCast_pow
      (by positivity : (0:ℝ) ≤ (1+|ξ|/1)^100) (by norm_num : (3:ℕ) ≠ 0)
    simp only [Nat.cast_ofNat] at hr
    rw [hr] at hn
    norm_num only [show (2*3:ℕ)=6 by omega,div_one] at hn
    rw [parabolaWeightedSixNorm_pow_six W hW₀ hW,
      parabolaWeightedSixNorm_pow_six W hW₀ hW] at hn
    exact hn
  have hp (ξ : ℝ) :
      ((1+|ξ|)^102)⁻¹*parabolaBoxBilinearMoment S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x 1 0 0 ≤
          K*J*(1+ξ^2)⁻¹ := by
    have hb := (parabolaBox_le_rapid S S
      (fun i => z i*fordAdditiveCharacter (ξ*x i))
      (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x (by norm_num : (0:ℝ)<1) 0 0).trans
      (parabolaRapid_le_source S S
        (fun i => z i*fordAdditiveCharacter (ξ*x i))
        (fun i => z i*fordAdditiveCharacter (ξ*x i)) x x (by norm_num : (0:ℝ)<1) hcomp 0 0)
    have he := bourgain_modulation_envelope (R:=1) (by norm_num) ξ
    simp only [div_one] at he
    calc
      _ ≤ ((1+|ξ|)^102)⁻¹*(K*((1+|ξ|)^100*J)) :=
        mul_le_mul_of_nonneg_left
          (hb.trans (mul_le_mul_of_nonneg_left (hm ξ) hK.le)) (by positivity)
      _ = K*J*(((1+|ξ|)^102)⁻¹*(1+|ξ|)^100) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg hK.le hJ)
  have hi := integrable_bourgain_modulated_box S z x x 1 0 0
  have hh := integral_mono hi (integrable_inv_one_add_sq.const_mul (K*J)) hp
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hh
  have he (r : ℝ) : r^2*r^4=r^6 := by ring
  have hJe : J = ∫ p : ℝ × ℝ, parabolaSourceWeight 1 0 0 p.1 p.2*
      ‖∑ i ∈ S, z i*fordAdditiveCharacter (x i*p.1+(x i)^2*p.2)‖^6 := by
    simp only [J,parabolaSourceBilinearMoment,mul_assoc,he,sargosPlanarSum]
  rw [←hJe]
  exact hh.trans_eq (by ring)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_cube_mass {R : ℝ} (hR : 0 ≤ R) :
    volume.real (Icc (fun _ : Fin 4 => -R) (fun _ => R)) = (2*R)^4 := by
  change (volume (Icc (fun _ : Fin 4 => -R) (fun _ => R))).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun _ => by linarith)]
  simp only [sub_neg_eq_add,←two_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

private theorem bourgain_finite_box_average {K R : ℝ}
    (hK : 0 ≤ K) (hKR : K ≤ R) (f : (Fin 4 → ℝ) → ℝ)
    (hfc : Continuous f) (hf₀ : ∀ x, 0 ≤ f x) :
    (2*K)^4*(∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f x) ≤
      ∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R),
        ∫ y : Fin 4 → ℝ in Icc (fun _ => -K) (fun _ => K), f (q+y) := by
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  have hpoint (y : Fin 4 → ℝ) (hy : y ∈ B K) :
      (∫ x in B R, f x) ≤ ∫ q in B (2*R), f (q+y) := by
    have hsub : (fun q => q+y) ⁻¹' B R ⊆ B (2*R) := by
      intro q hq
      constructor
      · intro i
        have hl := hq.1 i
        have hu := hy.2 i
        change -R ≤ q i+y i at hl
        change y i ≤ K at hu
        linarith
      · intro i
        have hu := hq.2 i
        have hl := hy.1 i
        change q i+y i ≤ R at hu
        change -K ≤ y i at hl
        linarith
    have hi : IntegrableOn (fun q => f (q+y)) (B (2*R)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hfc.comp (continuous_id.add continuous_const)).continuousOn
    calc
      _ = ∫ q in (fun q => q+y) ⁻¹' B R, f (q+y) :=
        ((measurePreserving_add_right volume y).setIntegral_preimage_emb
          (Homeomorph.addRight y).measurableEmbedding f (B R)).symm
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun q => hf₀ (q+y)))
        (Filter.Eventually.of_forall hsub)
  have hc : Continuous (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2)) :=
    hfc.comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B K))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc) hc.continuousOn
  have hconst : IntegrableOn (fun _y : Fin 4 → ℝ => ∫ x in B R, f x) (B K) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hconst hi.integral_prod_right measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change volume.real (B K)*(∫ x in B R, f x) ≤ _ at hh
  rw [bourgain_cube_mass hK] at hh
  have hswap := integral_integral_swap (f:=fun q y => f (q+y)) hi
  exact hh.trans_eq hswap.symm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private def bourgainSourceSixMoment {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) : ℝ :=
  ‖∑ i ∈ S, z i*fordAdditiveCharacter
    (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))‖^6

private theorem exists_bourgainSourceCurve_small_box :
    ∃ C > (0:ℝ), ∀ {ι τ : Type u} (S : Finset ι) (V : Finset τ)
      (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
      (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
      (∀ i ∈ S, Real.sqrt (w i) ∈ Icc 0 1) →
      (∀ j ∈ V, Real.sqrt (v j) ∈ Icc 0 1) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -(1/10:ℝ)) (fun _ => (1/10:ℝ)),
        bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
        C*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment S z w x)*
          (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment V c v x) := by
  obtain ⟨D,hD,hframe⟩ := exists_bourgainSourceCurve_bilinear_reduction.{u}
  obtain ⟨P,hP,hpar⟩ := exists_bourgainParabola_unit_average.{u}
  obtain ⟨Q,hQ,hret⟩ := exists_bourgainSourceCurve_cell_return_quantitative.{u}
  let A := P*Q*(3:ℝ)^100
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨D*(6:ℝ)⁻¹*A^2,by positivity,?_⟩
  intro ι τ S V z c w v hw hv hs ht
  have hsingle {κ : Type u} (U : Finset κ) (d : κ → ℂ) (u : κ → ℝ)
      (hu : ∀ i ∈ U, 0 ≤ u i) (hr : ∀ i ∈ U, Real.sqrt (u i) ∈ Icc 0 1)
      (a : ℝ) (ha : |a| ≤ 1) :
      (∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        parabolaBoxBilinearMoment U U
          (fun i => d i*fordAdditiveCharacter (ξ*(Real.sqrt (u i)-a)))
          (fun i => d i*fordAdditiveCharacter (ξ*(Real.sqrt (u i)-a)))
          (fun i => Real.sqrt (u i)-a) (fun i => Real.sqrt (u i)-a) 1 0 0) ≤
        A*(∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*bourgainSourceSixMoment U d u x) := by
    have hb := hpar U d (fun i => Real.sqrt (u i)-a)
    have hc := hret U d u hu a (1/2) (1/2) 1 ha
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun i hi => abs_le.mpr ⟨by linarith [(hr i hi).1],by linarith [(hr i hi).2]⟩)
    rw [show (1+((1/2:ℝ)*1)⁻¹)=3 by norm_num] at hc
    simp only [one_pow,div_one] at hc
    have hh := hb.trans (mul_le_mul_of_nonneg_left hc hP.le)
    change _ ≤ A*_
    exact hh.trans_eq (by dsimp [A,bourgainRadialWeight,bourgainSourceSixMoment]; ring)
  have hS := hsingle S z w hw hs 0 (by norm_num)
  have hV := hsingle V c v hv ht 1 (by norm_num)
  have hframe' := hframe ι τ S V z c w v hw hv 0 1 1 (1/10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (fun i hi => abs_le.mpr ⟨by linarith [(hs i hi).1],by linarith [(hs i hi).2]⟩)
    (fun j hj => abs_le.mpr ⟨by linarith [(ht j hj).1],by linarith [(ht j hj).2]⟩)
  simp only [div_one,show (10:ℝ)*(1/10)=1 by norm_num,
    sub_zero,one_pow,mul_one] at hframe' hS
  have hV₀ : 0 ≤ ∫ η : ℝ, ((1+|η|)^102)⁻¹*
      parabolaBoxBilinearMoment V V
        (fun j => c j*fordAdditiveCharacter (η*(Real.sqrt (v j)-1)))
        (fun j => c j*fordAdditiveCharacter (η*(Real.sqrt (v j)-1)))
        (fun j => Real.sqrt (v j)-1) (fun j => Real.sqrt (v j)-1) 1 0 0 :=
    integral_nonneg (fun η => mul_nonneg (by positivity)
      (integral_nonneg (fun p => by positivity)))
  have hSJ₀ : 0 ≤ A*(∫ x : Fin 4 → ℝ,
      bourgainRadialWeight 1 x*bourgainSourceSixMoment S z w x) :=
    mul_nonneg hA.le (integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg 1 x) (by
        unfold bourgainSourceSixMoment
        positivity)))
  have hprod := mul_le_mul hS hV hV₀ hSJ₀
  have hmain := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ D*(6:ℝ)⁻¹)
  change _ ≤ _ at hframe'
  calc
    _ ≤ _ := hframe'
    _ = D*(6:ℝ)⁻¹*(_*_) := by ring
    _ ≤ _ := hmain
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgainRadialWeight_translate_large {R : ℝ}
    (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ 2*R) (x : Fin 4 → ℝ) :
    bourgainRadialWeight 1 (x-q) ≤ (2:ℝ)^100*bourgainRadialWeight (20*R) x := by
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h20 : 0 < 20*R := by positivity
  rw [bourgainRadialWeight_distance (by norm_num : (0:ℝ)<1),
    bourgainRadialWeight_distance h20,div_one]
  apply bourgain_inverse_power_ratio (by positivity) (by positivity)
  have hn : ‖x‖ ≤ ‖x-q‖+2*R := by
    calc
      _ = ‖(x-q)+q‖ := by rw [sub_add_cancel]
      _ ≤ ‖x-q‖+‖q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hd : ‖x‖/(20*R) ≤ 1+‖x-q‖ := by
    apply (div_le_iff₀ h20).mpr
    nlinarith [norm_nonneg (x-q),mul_nonneg (sub_nonneg.mpr hR) (norm_nonneg (x-q))]
  linarith [norm_nonneg (x-q)]

private theorem bourgainRadialWeight_translated_integral {R : ℝ}
    (hR : 1 ≤ R) {q : Fin 4 → ℝ} (hq : ‖q‖ ≤ 2*R)
    (f : (Fin 4 → ℝ) → ℝ) (M : ℝ) (hc : Continuous f)
    (h₀ : ∀ x, 0 ≤ f x) (hb : ∀ x, ‖f x‖ ≤ M) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*f (x+q)) ≤
      (2:ℝ)^100*(∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*f x) := by
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hw1 : Integrable (bourgainRadialWeight 1) :=
    integrable_bourgainCurveCellWeight (by norm_num)
  have hwR : Integrable (bourgainRadialWeight (20*R)) :=
    integrable_bourgainCurveCellWeight (by positivity)
  have hi1 := (hw1.comp_sub_right q).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hiR := hwR.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hh := integral_mono hi1 (hiR.const_mul ((2:ℝ)^100))
    (fun x => (mul_le_mul_of_nonneg_right
      (bourgainRadialWeight_translate_large hR hq x) (h₀ x)).trans_eq (by ring))
  rw [integral_const_mul] at hh
  calc
    _ = ∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 (x-q)*f x := by
      have he := integral_add_right_eq_self (μ:=volume)
        (fun x : Fin 4 → ℝ => bourgainRadialWeight 1 (x-q)*f x) q
      simpa only [add_sub_cancel_right] using he
    _ ≤ _ := hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem bourgainSourceSixMoment_nonneg {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) :
    0 ≤ bourgainSourceSixMoment S z w x := by
  unfold bourgainSourceSixMoment
  positivity

private theorem continuous_bourgainSourceSixMoment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) :
    Continuous (bourgainSourceSixMoment S z w) := by
  unfold bourgainSourceSixMoment fordAdditiveCharacter
  fun_prop

private theorem bourgainSourceSixMoment_translate {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (q x : Fin 4 → ℝ) :
    bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
      (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))) w x =
        bourgainSourceSixMoment S z w (x+q) := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun v : ℂ => ‖v‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  apply congrArg (fun v : ℝ => z i*fordAdditiveCharacter v)
  simp only [Pi.add_apply]
  ring

private theorem exists_bourgainSourceCurve_box_base :
    ∃ C > (0:ℝ), ∀ R : ℝ, 1 ≤ R →
      ∀ {ι τ : Type u} (S : Finset ι) (V : Finset τ)
        (z : ι → ℂ) (c : τ → ℂ) (w : ι → ℝ) (v : τ → ℝ),
        (∀ i ∈ S, 0 ≤ w i) → (∀ j ∈ V, 0 ≤ v j) →
        (∀ i ∈ S, Real.sqrt (w i) ∈ Icc 0 1) →
        (∀ j ∈ V, Real.sqrt (v j) ∈ Icc 0 1) →
        (∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
          C*R^4*(∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
            bourgainSourceSixMoment S z w x)*
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
              bourgainSourceSixMoment V c v x) := by
  obtain ⟨D,hD,hsmall⟩ := exists_bourgainSourceCurve_small_box.{u}
  refine ⟨D*(2:ℝ)^200*20^4,by positivity,?_⟩
  intro R hR ι τ S V z c w v hw hv hs ht
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  let F := fun x : Fin 4 → ℝ => bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x
  let JS := ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment S z w x
  let JV := ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment V c v x
  have hJS : 0 ≤ JS := integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hJV : 0 ≤ JV := integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hFc : Continuous F :=
    (continuous_bourgainSourceSixMoment S z w).mul (continuous_bourgainSourceSixMoment V c v)
  have hF₀ (x : Fin 4 → ℝ) : 0 ≤ F x :=
    mul_nonneg (bourgainSourceSixMoment_nonneg _ _ _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)
  have havg := bourgain_finite_box_average (K:=1/10) (R:=R)
    (by norm_num) (by linarith) F hFc hF₀
  have hpoint (q : Fin 4 → ℝ) (hq : q ∈ B (2*R)) :
      (∫ y in B (1/10), F (q+y)) ≤ D*(2:ℝ)^200*JS*JV := by
    have hqnorm : ‖q‖ ≤ 2*R := (pi_norm_le_iff_of_nonneg (by linarith)).mpr
      (fun i => by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨hq.1 i,hq.2 i⟩)
    have hmoment {κ : Type u} (U : Finset κ) (d : κ → ℂ) (u : κ → ℝ) :
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight 1 x*
          bourgainSourceSixMoment U (fun i => d i*fordAdditiveCharacter
            (q 0*u i+q 1*(u i)^2+q 2*(u i)^((3:ℝ)/2)+q 3*Real.sqrt (u i))) u x) ≤
          (2:ℝ)^100*(∫ x : Fin 4 → ℝ,
            bourgainRadialWeight (20*R) x*bourgainSourceSixMoment U d u x) := by
      simp_rw [bourgainSourceSixMoment_translate]
      exact bourgainRadialWeight_translated_integral hR hqnorm
        (bourgainSourceSixMoment U d u) ((∑ i ∈ U, ‖d i‖)^6)
        (continuous_bourgainSourceSixMoment U d u)
        (bourgainSourceSixMoment_nonneg U d u)
        (fun x => bourgain_character_six_bound U d
          (fun i => x 0*u i+x 1*(u i)^2+x 2*(u i)^((3:ℝ)/2)+x 3*Real.sqrt (u i)))
    have hlocal := hsmall S V
      (fun i => z i*fordAdditiveCharacter
        (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i)))
      (fun j => c j*fordAdditiveCharacter
        (q 0*v j+q 1*(v j)^2+q 2*(v j)^((3:ℝ)/2)+q 3*Real.sqrt (v j)))
      w v hw hv hs ht
    have hmS := hmoment S z w
    have hmV := hmoment V c v
    have hleft : (∫ y in B (1/10), F (q+y)) =
        ∫ y in B (1/10),
          bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
            (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))) w y*
          bourgainSourceSixMoment V (fun j => c j*fordAdditiveCharacter
            (q 0*v j+q 1*(v j)^2+q 2*(v j)^((3:ℝ)/2)+q 3*Real.sqrt (v j))) v y := by
      simp only [bourgainSourceSixMoment_translate,F,add_comm]
    rw [hleft]
    refine hlocal.trans ?_
    have hh := mul_le_mul hmS hmV
      (integral_nonneg (fun x => mul_nonneg (bourgainRadialWeight_nonneg _ _)
        (bourgainSourceSixMoment_nonneg _ _ _ _)))
      (mul_nonneg (by positivity) hJS)
    have hh' := mul_le_mul_of_nonneg_left hh hD.le
    change D*_ * _ ≤ D*(2:ℝ)^200*JS*JV
    calc
      _ = D*(_*_) := by ring
      _ ≤ D*(((2:ℝ)^100*JS)*((2:ℝ)^100*JV)) := hh'
      _ = _ := by ring
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => F (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B (1/10)))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      (hFc.comp (continuous_fst.add continuous_snd)).continuousOn
  have hconst : IntegrableOn (fun _q : Fin 4 → ℝ => D*(2:ℝ)^200*JS*JV) (B (2*R)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hi.integral_prod_left hconst measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change _ ≤ volume.real (B (2*R))*(D*(2:ℝ)^200*JS*JV) at hh
  rw [bourgain_cube_mass (by linarith : 0 ≤ 2*R)] at hh
  have hfinal := havg.trans hh
  apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<(2*(1/10:ℝ))^4)).mp
  change (2*(1/10:ℝ))^4*(∫ x in B R, F x) ≤
    (2*(1/10:ℝ))^4*((D*(2:ℝ)^200*20^4)*R^4*JS*JV)
  exact hfinal.trans_eq (by ring)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem integrable_bourgainSource_weighted {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : Fin 4 → ℝ => bourgainRadialWeight R x*bourgainSourceSixMoment S z w x) :=
  (integrable_bourgainCurveCellWeight hR).mul_bdd
    (continuous_bourgainSourceSixMoment S z w).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => bourgain_character_six_bound S z
      (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))))

private theorem bourgainSourceSixMoment_finite_sum {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ)
    (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
      (fun ji => w ji.1 ji.2) x ≤
        (N:ℝ)^5*∑ j, bourgainSourceSixMoment (S j) (z j) (w j) x := by
  let A := fun j : Fin N => ∑ i ∈ S j, z j i*fordAdditiveCharacter
    (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))
  have hn := pow_le_pow_left₀ (norm_nonneg (∑ j, A j)) (norm_sum_le Finset.univ A) 6
  have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => ‖A j‖) (fun _ _ => norm_nonneg _) 5
  simp only [show (5+1:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin] at hh
  simpa only [bourgainSourceSixMoment,Finset.sum_sigma,A] using hn.trans hh

private theorem bourgainSource_weighted_finite_sum {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) x) ≤
      (N:ℝ)^5*∑ j, ∫ x : Fin 4 → ℝ,
        bourgainRadialWeight R x*bourgainSourceSixMoment (S j) (z j) (w j) x := by
  have hi (j : Fin N) := integrable_bourgainSource_weighted (S j) (z j) (w j) hR
  have hsum : Integrable (fun x : Fin 4 → ℝ =>
      ∑ j, bourgainRadialWeight R x*bourgainSourceSixMoment (S j) (z j) (w j) x) :=
    integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hh := integral_mono
    (integrable_bourgainSource_weighted (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) hR)
    (hsum.const_mul ((N:ℝ)^5))
    (fun x => by
      have hp := mul_le_mul_of_nonneg_left (bourgainSourceSixMoment_finite_sum S z w x)
        (bourgainRadialWeight_nonneg R x)
      simpa only [Finset.mul_sum,mul_left_comm] using hp)
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hi j)] at hh
  exact hh

/-- A genuine polynomial starting bound for the source-curve bootstrap.
It is proved from the analytic remainder multiplier and finite physical-box
averaging, for arbitrary finite coefficients and multiplicities. No spacing
or current-scale decoupling estimate is assumed. With N=2^n and R=N² the
displayed normalized constant grows as N^22. -/
theorem exists_bourgainSourceCurve_polynomial_base :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ι τ : Type u)
      (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
      (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
      (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
      (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
      (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc 0 1) →
      (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc 0 1) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -((2:ℝ)^n)^2) (fun _ => ((2:ℝ)^n)^2),
        ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
          (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
            x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
        ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
          (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
            x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
        C*((2:ℝ)^n)^22/(((2:ℝ)^n)^2)^2*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
              (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))‖^6)*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
              (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨C,hC,hbase⟩ := exists_bourgainSourceCurve_box_base.{u}
  refine ⟨C,hC,?_⟩
  intro n ι τ S V z c w v hw hv hs ht
  let N := (2:ℝ)^n
  let R := N^2
  let JS := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) x
  let JV := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) x
  have hN : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hR : 1 ≤ R := one_le_pow₀ hN
  have hR₀ : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have h20 : 0 < 20*R := by positivity
  have hm := hbase R hR (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun jk => c jk.1 jk.2)
    (fun ji => w ji.1 ji.2) (fun jk => v jk.1 jk.2)
    (fun ji hji => hw ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => hv jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
    (fun ji hji => hs ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun jk hjk => ht jk.1 jk.2 (Finset.mem_sigma.mp hjk).2)
  have hS := bourgainSource_weighted_finite_sum S z w h20
  have hV := bourgainSource_weighted_finite_sum V c v h20
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hS hV
  have hJS : 0 ≤ JS := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)))
  have hprod := mul_le_mul hS hV
    (integral_nonneg (fun x => mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (bourgainSourceSixMoment_nonneg _ _ _ _)))
    (mul_nonneg (by positivity) hJS)
  have hprod' := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ C*R^4)
  change _ ≤ C*N^22/R^2*JS*JV
  calc
    _ ≤ _ := hm
    _ = C*R^4*(_*_) := by ring
    _ ≤ C*R^4*((N^5*JS)*(N^5*JV)) := hprod'
    _ = C*N^22/R^2*JS*JV := by
      dsimp [R]
      field_simp

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_radial_bilinear_fubini
    {K R : ℝ} (hK : 0 < K) (f g : (Fin 4 → ℝ) → ℝ) (Mf Mg : ℝ)
    (hfc : Continuous f) (hgc : Continuous g)
    (hfb : ∀ x, ‖f x‖ ≤ Mf) (hgb : ∀ x, ‖g x‖ ≤ Mg) :
    Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
        (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f (q+p.1)*g (q+p.2))) ∧
    ((∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y))) =
      ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
          (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R), f (q+p.1)*g (q+p.2))) ∧
    IntegrableOn (fun q : Fin 4 → ℝ =>
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y)))
      (Icc (fun _ => -R) (fun _ => R)) := by
  let B := Icc (fun _ : Fin 4 => -R) (fun _ => R)
  let H := fun (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) (q : Fin 4 → ℝ) =>
    bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*(f (q+p.1)*g (q+p.2))
  have hMf : 0 ≤ Mf := (norm_nonneg (f 0)).trans (hfb 0)
  have hw : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hconst : IntegrableOn (fun _q : Fin 4 → ℝ => (1:ℝ)) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hc : Continuous (fun p : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × (Fin 4 → ℝ) =>
      f (p.2+p.1.1)*g (p.2+p.1.2)) :=
    (hfc.comp (continuous_snd.add continuous_fst.fst)).mul
      (hgc.comp (continuous_snd.add continuous_fst.snd))
  have hiH : Integrable (Function.uncurry H)
      ((volume.prod volume).prod (volume.restrict B)) := by
    have hwprod := (hw.mul_prod hw).mul_prod hconst
    have hi := hwprod.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul (hfb _) (hgb _) (norm_nonneg _) hMf))
    simpa only [Function.uncurry,H,mul_one] using hi
  have he (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) :
      (∫ q in B, H p q) =
        bourgainRadialWeight K p.1*bourgainRadialWeight K p.2*
          (∫ q in B, f (q+p.1)*g (q+p.2)) := by
    simp only [H,integral_const_mul]
  have heq (q : Fin 4 → ℝ) : (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q) =
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*f (q+x))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*g (q+y)) := by
    calc
      _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
          (bourgainRadialWeight K p.1*f (q+p.1))*
            (bourgainRadialWeight K p.2*g (q+p.2)) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [H]
        ring
      _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
        (fun x : Fin 4 → ℝ => bourgainRadialWeight K x*f (q+x))
        (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*g (q+y))
  refine ⟨?_,?_,?_⟩
  · simpa only [Function.uncurry,he,B] using hiH.integral_prod_left
  · have hswap := integral_integral_swap (f:=H) hiH
    calc
      _ = ∫ q in B, ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q := by
        simp only [heq,B]
      _ = ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), ∫ q in B, H p q := hswap.symm
      _ = _ := by simp only [he,B]

  · have hiR : Integrable (fun q : Fin 4 → ℝ =>
        ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ), H p q) (volume.restrict B) :=
      hiH.integral_prod_right
    simpa only [heq,B,IntegrableOn] using hiR

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem integrable_bourgainRadial_shift_average
    {K R : ℝ} (hK : 0 < K) (hR : 0 < R)
    (f : (Fin 4 → ℝ) → ℝ) (M : ℝ) (hc : Continuous f)
    (hb : ∀ x, ‖f x‖ ≤ M) :
    Integrable (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*f (x+y))) := by
  have hwK : Integrable (bourgainRadialWeight K) := integrable_bourgainCurveCellWeight hK
  have hwR : Integrable (bourgainRadialWeight R) := integrable_bourgainCurveCellWeight hR
  have hprod := hwK.mul_prod hwR
  have hi := hprod.mul_bdd
    (hc.comp (continuous_snd.add continuous_fst)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => hb (p.2+p.1)))
  simpa only [mul_assoc,integral_const_mul] using hi.integral_prod_left

private theorem integrable_bourgainSource_shift_sum
    {K R : ℝ} (hK : 0 < K) (hR : 0 < R) {N : ℕ} {ι : Type*}
    (S : Fin N → Finset ι) (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ) :
    Integrable (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*
      (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
        bourgainSourceSixMoment (S j) (z j) (w j) (x+y))) := by
  have hi (j : Fin N) := integrable_bourgainRadial_shift_average hK hR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))
  simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hi j)

private theorem exists_bourgainSource_shift_sum :
    ∃ C > (0:ℝ), ∀ K R : ℝ, 0 < K → K ≤ R →
      ∀ (N : ℕ) {ι : Type u} (S : Fin N → Finset ι)
        (z : Fin N → ι → ℂ) (w : Fin N → ι → ℝ),
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
          (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
            bourgainSourceSixMoment (S j) (z j) (w j) (x+y))) ≤
          C*K^4*(∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight R x*
            bourgainSourceSixMoment (S j) (z j) (w j) x) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainRadialWeight_shift_average
  refine ⟨C,hC,?_⟩
  intro K R hK hKR N ι S z w
  have hR : 0 < R := hK.trans_le hKR
  have hi (j : Fin N) := integrable_bourgainRadial_shift_average hK hR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  apply Finset.sum_le_sum
  intro j hj
  exact h K R hK hKR
    (bourgainSourceSixMoment (S j) (z j) (w j)) ((∑ i ∈ S j, ‖z j i‖)^6)
    (continuous_bourgainSourceSixMoment (S j) (z j) (w j))
    (bourgainSourceSixMoment_nonneg (S j) (z j) (w j))
    (fun x => bourgain_character_six_bound (S j) (z j)
      (fun i => x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i)))

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u


private theorem bourgainSourceSixMoment_norm_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (x : Fin 4 → ℝ) :
    ‖bourgainSourceSixMoment S z w x‖ ≤ (∑ i ∈ S, ‖z i‖)^6 :=
  bourgain_character_six_bound S z
    (fun i => x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSourceCurve_averaged_local_decoupling {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (a b σ R K : ℝ),
      0 ≤ a → a+σ ≤ 1 → 0 ≤ b → b+σ ≤ 1 → a ≠ b →
      0 < σ → σ ≤ 1 → 0 < R → 5*R*σ^3 ≤ 1 →
      5*(10*R)*(σ/(2:ℝ)^n)^3 ≤ 1 → 1 ≤ (σ/(2:ℝ)^n)*(10*R) →
      3/(100*(10*R)) ≤ (σ/(2:ℝ)^n)^2 → 0 < K → K ≤ 10*R →
      ∀ (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
        (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          (a+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (a+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
          (b+σ*((j:ℕ)/((2^n:ℕ):ℝ))) (b+σ*(((j:ℕ)+1)/((2^n:ℕ):ℝ)))) →
        (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma S)
              (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) (q+y))*
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma V)
              (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2) (q+y))) ≤
          C*K^8*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*
            (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
              bourgainSourceSixMoment (S j) (z j) (w j) x)*
            (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
              bourgainSourceSixMoment (V j) (c j) (v j) x) := by
  obtain ⟨D,hD,hlocal⟩ := exists_bourgainSourceCurve_local_cell_decoupling.{u} hε
  obtain ⟨E,hE,havg⟩ := exists_bourgainSource_shift_sum.{u}
  refine ⟨D*E^2,by positivity,?_⟩
  intro n a b σ R K ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth hK hKR
    ι τ S V z c w v hw hv hs ht
  let F := bourgainSourceSixMoment (Finset.univ.sigma S)
    (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  let G := bourgainSourceSixMoment (Finset.univ.sigma V)
    (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  let JS := fun y : Fin 4 → ℝ => ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) (x+y)
  let JV := fun y : Fin 4 → ℝ => ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) (x+y)
  let AS := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (S j) (z j) (w j) x
  let AV := ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
    bourgainSourceSixMoment (V j) (c j) (v j) x
  let A := D*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h10 : 0 < 10*R := by positivity
  have hFub := bourgain_radial_bilinear_fubini (R:=R) hK F G
    ((∑ ji ∈ Finset.univ.sigma S, ‖z ji.1 ji.2‖)^6)
    ((∑ ji ∈ Finset.univ.sigma V, ‖c ji.1 ji.2‖)^6)
    (continuous_bourgainSourceSixMoment (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2))
    (continuous_bourgainSourceSixMoment (Finset.univ.sigma V)
      (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2))
    (bourgainSourceSixMoment_norm_bound (Finset.univ.sigma S)
      (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2))
    (bourgainSourceSixMoment_norm_bound (Finset.univ.sigma V)
      (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2))
  have hp (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) :
      (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
        F (q+p.1)*G (q+p.2)) ≤ A*JS p.1*JV p.2 := by
    have hh := hlocal n a b σ R ha haσ hb hbσ hab hσ hσ₁ hR hrem hfine hδR hwidth
      ι τ S V
      (fun j i => z j i*fordAdditiveCharacter
        (p.1 0*w j i+p.1 1*(w j i)^2+p.1 2*(w j i)^((3:ℝ)/2)+p.1 3*Real.sqrt (w j i)))
      (fun j i => c j i*fordAdditiveCharacter
        (p.2 0*v j i+p.2 1*(v j i)^2+p.2 2*(v j i)^((3:ℝ)/2)+p.2 3*Real.sqrt (v j i)))
      w v hw hv hs ht
    change (∫ q : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      bourgainSourceSixMoment (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2*fordAdditiveCharacter
          (p.1 0*w ji.1 ji.2+p.1 1*(w ji.1 ji.2)^2+
            p.1 2*(w ji.1 ji.2)^((3:ℝ)/2)+p.1 3*Real.sqrt (w ji.1 ji.2)))
        (fun ji => w ji.1 ji.2) q*
      bourgainSourceSixMoment (Finset.univ.sigma V)
        (fun ji => c ji.1 ji.2*fordAdditiveCharacter
          (p.2 0*v ji.1 ji.2+p.2 1*(v ji.1 ji.2)^2+
            p.2 2*(v ji.1 ji.2)^((3:ℝ)/2)+p.2 3*Real.sqrt (v ji.1 ji.2)))
        (fun ji => v ji.1 ji.2) q) ≤
      A*(∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
        bourgainSourceSixMoment (S j)
          (fun i => z j i*fordAdditiveCharacter
            (p.1 0*w j i+p.1 1*(w j i)^2+p.1 2*(w j i)^((3:ℝ)/2)+p.1 3*Real.sqrt (w j i))) (w j) x)*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (10*R) x*
          bourgainSourceSixMoment (V j)
            (fun i => c j i*fordAdditiveCharacter
              (p.2 0*v j i+p.2 1*(v j i)^2+p.2 2*(v j i)^((3:ℝ)/2)+p.2 3*Real.sqrt (v j i))) (v j) x) at hh
    simpa only [bourgainSourceSixMoment_translate,F,G,JS,JV] using hh
  have hiS := integrable_bourgainSource_shift_sum hK h10 S z w
  have hiV := integrable_bourgainSource_shift_sum hK h10 V c v
  have hiRight : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      A*((bourgainRadialWeight K p.1*JS p.1)*(bourgainRadialWeight K p.2*JV p.2))) :=
    (hiS.mul_prod hiV).const_mul A
  have hout := integral_mono hFub.1 hiRight
    (fun p => by
      have hh := mul_le_mul_of_nonneg_left (hp p)
        (mul_nonneg (bourgainRadialWeight_nonneg K p.1) (bourgainRadialWeight_nonneg K p.2))
      exact hh.trans_eq (by ring))
  have hfactor : (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
      (bourgainRadialWeight K p.1*JS p.1)*(bourgainRadialWeight K p.2*JV p.2)) =
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*JS x)*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*JV y) :=
    integral_prod_mul (μ:=volume) (ν:=volume)
      (fun x : Fin 4 → ℝ => bourgainRadialWeight K x*JS x)
      (fun y : Fin 4 → ℝ => bourgainRadialWeight K y*JV y)
  rw [integral_const_mul,hfactor] at hout
  have hmS := havg K (10*R) hK hKR (2^n) S z w
  have hmV := havg K (10*R) hK hKR (2^n) V c v
  have hAS : 0 ≤ AS := Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg (10*R) x) (bourgainSourceSixMoment_nonneg (S j) (z j) (w j) x)))
  have hJV : 0 ≤ ∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*JV y :=
    integral_nonneg (fun y => mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
        mul_nonneg (bourgainRadialWeight_nonneg (10*R) x) (bourgainSourceSixMoment_nonneg (V j) (c j) (v j) (x+y))))))
  have hprod := mul_le_mul hmS hmV hJV (mul_nonneg (by positivity) hAS)
  have hmain := hout.trans (mul_le_mul_of_nonneg_left hprod hA)
  rw [hFub.2.1]
  change _ ≤ (D*E^2)*K^8*(2:ℝ)^((ε+4)*n)/(10*R)^4*(6*(b-a)^4)⁻¹*AS*AV
  exact hmain.trans_eq (by dsimp [A]; ring)

end TaoTrudgianYang2025


noncomputable section
open Set
namespace TaoTrudgianYang2025

private theorem bourgain_coarse_center_separation {a b σ ν u v : ℝ}
    (hν : 0 < ν) (hσ : σ ≤ ν/2)
    (hu : u ∈ Icc a (a+σ)) (hv : v ∈ Icc b (b+σ))
    (hsep : ν ≤ |u-v|) :
    ν/2 ≤ |b-a| ∧ a ≠ b ∧ (6*(b-a)^4)⁻¹ ≤ (6*(ν/2)^4)⁻¹ := by
  have hh : |u-v| ≤ |a-b|+σ := by
    apply abs_le.mpr
    constructor
    · linarith [hu.1,hv.2,neg_abs_le (a-b)]
    · linarith [hu.2,hv.1,le_abs_self (a-b)]
  have hd : ν/2 ≤ |b-a| := by
    rw [abs_sub_comm a b] at hh
    linarith
  have hab : a ≠ b := by
    intro he
    rw [he,sub_self,abs_zero] at hd
    linarith
  have hp : (ν/2)^4 ≤ (b-a)^4 := by
    have h := pow_le_pow_left₀ (by positivity) hd 4
    simpa only [show (4:ℕ)=2*2 by omega,pow_mul,sq_abs] using h
  exact ⟨hd,hab,inv_anti₀ (by positivity)
    (mul_le_mul_of_nonneg_left hp (by norm_num))⟩

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025

private theorem bourgain_bootstrap_depth {n : ℕ} (hn : 9 ≤ n) :
    let m := (2*n+2)/3+2
    m < n ∧ 2*n+6 ≤ 3*m ∧ n ≤ 2*m := by
  dsimp
  omega

private theorem bourgain_bootstrap_scale_conditions {n m : ℕ}
    (hm : m ≤ n) (hlarge : 2*n+6 ≤ 3*m) (hn : 7 ≤ n) :
    let N := (2:ℝ)^n
    let M := (2:ℝ)^m
    let σ := 1/M
    let δ := σ/(2:ℝ)^(n-m)
    0 < σ ∧ σ ≤ 1 ∧ δ=1/N ∧
      5*(2*N^2)*σ^3 ≤ 1 ∧
      5*(10*(2*N^2))*δ^3 ≤ 1 ∧
      1 ≤ δ*(10*(2*N^2)) ∧
      3/(100*(10*(2*N^2))) ≤ δ^2 ∧
      0 < 20*M^2 ∧ 20*M^2 ≤ 10*(2*N^2) := by
  let N := (2:ℝ)^n
  let M := (2:ℝ)^m
  have hN : 0 < N := by dsimp [N]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hN₁ : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hM₁ : 1 ≤ M := one_le_pow₀ (by norm_num)
  have hMN : M ≤ N := pow_le_pow_right₀ (by norm_num) hm
  have hN128 : (128:ℝ) ≤ N := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn
    norm_num only [show (2:ℝ)^7=128 by norm_num] at h
    exact h
  have hpow : N^2*64 ≤ M^3 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      (by omega : n*2+6 ≤ m*3)
    rw [pow_add,pow_mul,pow_mul] at h
    norm_num only [show (2:ℝ)^6=64 by norm_num] at h
    exact h
  have hδ : (1/M)/(2:ℝ)^(n-m)=1/N := by
    dsimp [M,N]
    rw [pow_sub₀ (2:ℝ) (by norm_num) hm]
    field_simp
  change 0 < 1/M ∧ 1/M ≤ 1 ∧ (1/M)/(2:ℝ)^(n-m)=1/N ∧ _
  refine ⟨by positivity,(div_le_one hM).mpr hM₁,hδ,?_,?_,?_,?_,by positivity,?_⟩
  · have he : 5*(2*N^2)*(1/M)^3 = 10*N^2/M^3 := by ring
    rw [he]
    apply (div_le_one (pow_pos hM 3)).mpr
    nlinarith [sq_nonneg N]
  · rw [hδ]
    have he : 5*(10*(2*N^2))*(1/N)^3 = 100/N := by field_simp; ring
    rw [he]
    exact (div_le_one hN).mpr (by linarith)
  · rw [hδ]
    have he : (1/N)*(10*(2*N^2)) = 20*N := by field_simp; ring
    rw [he]
    linarith
  · rw [hδ,div_pow,one_pow]
    apply (div_le_div_iff₀ (by positivity) (sq_pos_of_pos hN)).mpr
    nlinarith [sq_nonneg N]
  · have hp := pow_le_pow_left₀ hM.le hMN 2
    nlinarith

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The real finite source-curve grid contract. This private proposition is
a bound to be proved, not analytic provenance or an induction hypothesis at
the target scale. -/
private def BourgainSourceGridBound (N : ℕ) (ν D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ (ι τ : Type u)
    (S : Fin N → Finset ι) (V : Fin N → Finset τ)
    (z : Fin N → ι → ℂ) (c : Fin N → τ → ℂ)
    (w : Fin N → ι → ℝ) (v : Fin N → τ → ℝ),
    (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
    (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc ((j:ℕ)/(N:ℝ)) (((j:ℕ)+1)/(N:ℝ))) →
    (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc ((j:ℕ)/(N:ℝ)) (((j:ℕ)+1)/(N:ℝ))) →
    (∀ j k, ∀ i ∈ S j, ∀ l ∈ V k, ν ≤ |Real.sqrt (w j i)-Real.sqrt (v k l)|) →
    (∫ x : Fin 4 → ℝ in Icc (fun _ => -(N:ℝ)^2) (fun _ => (N:ℝ)^2),
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) x*
      bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
        (fun ji => v ji.1 ji.2) x) ≤
      D/((N:ℝ)^2)^2*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
          bourgainSourceSixMoment (S j) (z j) (w j) x)*
        (∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
          bourgainSourceSixMoment (V j) (c j) (v j) x)

private theorem bourgainSourceGridBound_mono {N : ℕ} {ν D E : ℝ}
    (hD : BourgainSourceGridBound.{u} N ν D) (hDE : D ≤ E) :
    BourgainSourceGridBound.{u} N ν E := by
  refine ⟨hD.1.trans hDE,?_⟩
  intro ι τ S V z c w v hw hv hs ht hsep
  have hm := hD.2 ι τ S V z c w v hw hv hs ht hsep
  have hS : 0 ≤ ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
      bourgainSourceSixMoment (S j) (z j) (w j) x :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg (S j) (z j) (w j) x)))
  have hV : 0 ≤ ∑ j, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(N:ℝ)^2) x*
      bourgainSourceSixMoment (V j) (c j) (v j) x :=
    Finset.sum_nonneg (fun j _ => integral_nonneg (fun x =>
      mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg (V j) (c j) (v j) x)))
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hDE (by positivity)) hS) hV)

private theorem exists_bourgainSourceGridBound_polynomial :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ν : ℝ),
      BourgainSourceGridBound.{u} (2^n) ν (C*((2:ℝ)^n)^22) := by
  obtain ⟨C,hC,hbase⟩ := exists_bourgainSourceCurve_polynomial_base.{u}
  refine ⟨C,hC,?_⟩
  intro n ν
  refine ⟨by positivity,?_⟩
  intro ι τ S V z c w v hw hv hs ht _hsep
  have hunit {κ : Type u} (U : Fin (2^n) → Finset κ) (u : Fin (2^n) → κ → ℝ)
      (hu : ∀ j, ∀ i ∈ U j, Real.sqrt (u j i) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      ∀ j, ∀ i ∈ U j, Real.sqrt (u j i) ∈ Icc 0 1 := by
    intro j i hi
    refine ⟨(by positivity : (0:ℝ) ≤ (j:ℕ)/((2^n:ℕ):ℝ)).trans (hu j i hi).1,?_⟩
    apply (hu j i hi).2.trans
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hm := hbase n ι τ S V z c w v hw hv (hunit S w hs) (hunit V v ht)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,bourgainRadialWeight,bourgainSourceSixMoment] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem bourgainSource_grid_coarse_interval {k l : ℕ}
  (hk : 0 < k) (hl : 0 < l) {κ : Type u} (A : Fin (k*l) → Finset κ) (f : Fin (k*l) → κ → ℝ)
    (hgrid : ∀ j, ∀ i ∈ A j, Real.sqrt (f j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ))) :
    ∀ i : Fin k, ∀ ji ∈ Finset.univ.sigma (fun j : Fin l => A (finProdFinEquiv (i,j))),
      Real.sqrt (f (finProdFinEquiv (i,ji.1)) ji.2) ∈ Icc ((i:ℕ)/(k:ℝ)) (((i:ℕ)+1)/(k:ℝ)) := by
  intro i ji hji
  have hf := hgrid (finProdFinEquiv (i,ji.1)) ji.2 (Finset.mem_sigma.mp hji).2
  have hcell := finGrid_cell hk hl i ji.1
  simp only [Nat.cast_mul] at hf
  change Real.sqrt (f (finProdFinEquiv (i,ji.1)) ji.2) ∈ Icc
    (((finProdFinEquiv (i,ji.1) : Fin (k*l)):ℕ)/(k*l:ℝ))
    ((((finProdFinEquiv (i,ji.1) : Fin (k*l)):ℕ)+1)/(k*l:ℝ)) at hf
  rw [hcell.1,hcell.2] at hf
  have hj₀ : (0:ℝ) ≤ (ji.1:ℕ)/(l:ℝ) := by positivity
  have hj₁ : ((ji.1:ℕ)+1)/(l:ℝ) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast Nat.succ_le_of_lt ji.1.isLt
  refine ⟨(le_add_of_nonneg_right (mul_nonneg (by positivity) hj₀)).trans hf.1,?_⟩
  calc
    _ ≤ (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*(((ji.1:ℕ)+1)/(l:ℝ)) := hf.2
    _ ≤ (i:ℕ)/(k:ℝ)+(1/(k:ℝ))*1 := add_le_add_right
      (mul_le_mul_of_nonneg_left hj₁ (by positivity)) _
    _ = ((i:ℕ)+1)/(k:ℝ) := by ring

private theorem bourgainSourceSixMoment_grid_reindex {k l : ℕ} {ι : Type*}
    (S : Fin (k*l) → Finset ι) (z : Fin (k*l) → ι → ℂ) (w : Fin (k*l) → ι → ℝ)
    (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ri => z ri.1 ri.2)
      (fun ri => w ri.1 ri.2) x =
    bourgainSourceSixMoment
      (Finset.univ.sigma (fun i : Fin k => Finset.univ.sigma
        (fun j : Fin l => S (finProdFinEquiv (i,j)))))
      (fun ijv => z (finProdFinEquiv (ijv.1,ijv.2.1)) ijv.2.2)
      (fun ijv => w (finProdFinEquiv (ijv.1,ijv.2.1)) ijv.2.2) x := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun q : ℂ => ‖q‖^6)
  simp only [Finset.sum_sigma]
  exact finGrid_sum (fun r => ∑ i ∈ S r, z r i*fordAdditiveCharacter
    (x 0*w r i+x 1*(w r i)^2+x 2*(w r i)^((3:ℝ)/2)+x 3*Real.sqrt (w r i)))

set_option maxHeartbeats 400000 in
private theorem bourgainSourceGridBound_coarse_shift_entry
    {k l : ℕ} {ν D : ℝ} (hk : 0 < k) (hl : 0 < l)
    (hD : BourgainSourceGridBound.{u} k ν D)
    (ι τ : Type u) (S : Fin (k*l) → Finset ι) (V : Fin (k*l) → Finset τ)
    (z : Fin (k*l) → ι → ℂ) (c : Fin (k*l) → τ → ℂ)
    (w : Fin (k*l) → ι → ℝ) (v : Fin (k*l) → τ → ℝ)
    (hw : ∀ j, ∀ i ∈ S j, 0 ≤ w j i) (hv : ∀ j, ∀ i ∈ V j, 0 ≤ v j i)
    (hs : ∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ)))
    (ht : ∀ j, ∀ i ∈ V j, Real.sqrt (v j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ)))
    (hsep : ∀ j h, ∀ i ∈ S j, ∀ t ∈ V h, ν ≤ |Real.sqrt (w j i)-Real.sqrt (v h t)|) :
    let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
    let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
    let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => V (e (i,j)))
    let Z := fun i : Fin k => fun ji : (_j : Fin l) × ι => z (e (i,ji.1)) ji.2
    let C := fun i : Fin k => fun ji : (_j : Fin l) × τ => c (e (i,ji.1)) ji.2
    let X := fun i : Fin k => fun ji : (_j : Fin l) × ι => w (e (i,ji.1)) ji.2
    let Y := fun i : Fin k => fun ji : (_j : Fin l) × τ => v (e (i,ji.1)) ji.2
    ∀ q : Fin 4 → ℝ,
      (∫ y : Fin 4 → ℝ in Icc (fun _ => -(k:ℝ)^2) (fun _ => (k:ℝ)^2),
        bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
          (fun ji => w ji.1 ji.2) (q+y)*
        bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
          (fun ji => v ji.1 ji.2) (q+y)) ≤
        D/((k:ℝ)^2)^2*
          (∑ i, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
            bourgainSourceSixMoment (T i) (Z i) (X i) (q+x))*
          (∑ i, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
            bourgainSourceSixMoment (U i) (C i) (Y i) (q+x)) := by
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => V (e (i,j)))
  let Z := fun i : Fin k => fun ji : (_j : Fin l) × ι => z (e (i,ji.1)) ji.2
  let C := fun i : Fin k => fun ji : (_j : Fin l) × τ => c (e (i,ji.1)) ji.2
  let X := fun i : Fin k => fun ji : (_j : Fin l) × ι => w (e (i,ji.1)) ji.2
  let Y := fun i : Fin k => fun ji : (_j : Fin l) × τ => v (e (i,ji.1)) ji.2
  dsimp only
  intro q
  guard_hyp q : Fin 4 → ℝ
  have hmain := hD.2 ((_j : Fin l) × ι) ((_j : Fin l) × τ) T U
    (fun i ji => Z i ji*fordAdditiveCharacter
      (q 0*X i ji+q 1*(X i ji)^2+q 2*(X i ji)^((3:ℝ)/2)+q 3*Real.sqrt (X i ji)))
    (fun i ji => C i ji*fordAdditiveCharacter
      (q 0*Y i ji+q 1*(Y i ji)^2+q 2*(Y i ji)^((3:ℝ)/2)+q 3*Real.sqrt (Y i ji)))
    X Y
    (fun i ji hji => hw (e (i,ji.1)) ji.2 (Finset.mem_sigma.mp hji).2)
    (fun i ji hji => hv (e (i,ji.1)) ji.2 (Finset.mem_sigma.mp hji).2)
    (bourgainSource_grid_coarse_interval hk hl S w hs)
    (bourgainSource_grid_coarse_interval hk hl V v ht)
    (fun i j si hsi vi hvi => hsep (e (i,si.1)) (e (j,vi.1))
      si.2 (Finset.mem_sigma.mp hsi).2 vi.2 (Finset.mem_sigma.mp hvi).2)
  have heS := bourgainSourceSixMoment_grid_reindex S z w
  have heV := bourgainSourceSixMoment_grid_reindex V c v
  calc
    _ = ∫ y : Fin 4 → ℝ in Icc (fun _ => -(k:ℝ)^2) (fun _ => (k:ℝ)^2),
        bourgainSourceSixMoment (Finset.univ.sigma T)
          (fun iji => Z iji.1 iji.2) (fun iji => X iji.1 iji.2) (q+y)*
        bourgainSourceSixMoment (Finset.univ.sigma U)
          (fun iji => C iji.1 iji.2) (fun iji => Y iji.1 iji.2) (q+y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [heS (q+y),heV (q+y)]
    _ ≤ _ := by
      simpa only [bourgainSourceSixMoment_translate,add_comm] using hmain

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem bourgainSourceGridBound_coarse_average_entry
    {k l : ℕ} {ν D : ℝ} (hk : 0 < k) (hl : 0 < l)
    (hD : BourgainSourceGridBound.{u} k ν D)
    {R : ℝ} (hKR : (k:ℝ)^2 ≤ R)
    (ι τ : Type u) (S : Fin (k*l) → Finset ι) (V : Fin (k*l) → Finset τ)
    (z : Fin (k*l) → ι → ℂ) (c : Fin (k*l) → τ → ℂ)
    (w : Fin (k*l) → ι → ℝ) (v : Fin (k*l) → τ → ℝ)
    (hw : ∀ j, ∀ i ∈ S j, 0 ≤ w j i) (hv : ∀ j, ∀ i ∈ V j, 0 ≤ v j i)
    (hs : ∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ)))
    (ht : ∀ j, ∀ i ∈ V j, Real.sqrt (v j i) ∈ Icc
      ((j:ℕ)/((k*l:ℕ):ℝ)) (((j:ℕ)+1)/((k*l:ℕ):ℝ)))
    (hsep : ∀ j h, ∀ i ∈ S j, ∀ t ∈ V h, ν ≤ |Real.sqrt (w j i)-Real.sqrt (v h t)|) :
    let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
    let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
    let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => V (e (i,j)))
    let Z := fun i : Fin k => fun ji : (_j : Fin l) × ι => z (e (i,ji.1)) ji.2
    let C := fun i : Fin k => fun ji : (_j : Fin l) × τ => c (e (i,ji.1)) ji.2
    let X := fun i : Fin k => fun ji : (_j : Fin l) × ι => w (e (i,ji.1)) ji.2
    let Y := fun i : Fin k => fun ji : (_j : Fin l) × τ => v (e (i,ji.1)) ji.2
    (2*(k:ℝ)^2)^4*(∫ y : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
      bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) y*
      bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
        (fun ji => v ji.1 ji.2) y) ≤
      D/((k:ℝ)^2)^2*∑ i : Fin k, ∑ j : Fin k,
        ∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R),
          (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
            bourgainSourceSixMoment (T i) (Z i) (X i) (q+x))*
          (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
            bourgainSourceSixMoment (U j) (C j) (Y j) (q+x)) := by
  let e : Fin k × Fin l ≃ Fin (k*l) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => S (e (i,j)))
  let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin l => V (e (i,j)))
  let Z := fun i : Fin k => fun ji : (_j : Fin l) × ι => z (e (i,ji.1)) ji.2
  let C := fun i : Fin k => fun ji : (_j : Fin l) × τ => c (e (i,ji.1)) ji.2
  let X := fun i : Fin k => fun ji : (_j : Fin l) × ι => w (e (i,ji.1)) ji.2
  let Y := fun i : Fin k => fun ji : (_j : Fin l) × τ => v (e (i,ji.1)) ji.2
  let B := fun r : ℝ => Icc (fun _ : Fin 4 => -r) (fun _ => r)
  let F := bourgainSourceSixMoment (Finset.univ.sigma S)
    (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  let G := bourgainSourceSixMoment (Finset.univ.sigma V)
    (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  let JS := fun (i : Fin k) (q : Fin 4 → ℝ) =>
    ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
      bourgainSourceSixMoment (T i) (Z i) (X i) (q+x)
  let JV := fun (j : Fin k) (q : Fin 4 → ℝ) =>
    ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
      bourgainSourceSixMoment (U j) (C j) (Y j) (q+x)
  have hK : 0 < (k:ℝ)^2 := by positivity
  have hW : 0 < 20*(k:ℝ)^2 := by positivity
  have hFc : Continuous F := continuous_bourgainSourceSixMoment
    (Finset.univ.sigma S) (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  have hGc : Continuous G := continuous_bourgainSourceSixMoment
    (Finset.univ.sigma V) (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  have hiPair (i j : Fin k) : IntegrableOn (fun q : Fin 4 → ℝ => JS i q*JV j q) (B (2*R)) :=
    (bourgain_radial_bilinear_fubini (R:=2*R) hW
      (bourgainSourceSixMoment (T i) (Z i) (X i))
      (bourgainSourceSixMoment (U j) (C j) (Y j))
      ((∑ si ∈ T i, ‖Z i si‖)^6) ((∑ vi ∈ U j, ‖C j vi‖)^6)
      (continuous_bourgainSourceSixMoment (T i) (Z i) (X i))
      (continuous_bourgainSourceSixMoment (U j) (C j) (Y j))
      (bourgainSourceSixMoment_norm_bound (T i) (Z i) (X i))
      (bourgainSourceSixMoment_norm_bound (U j) (C j) (Y j))).2.2
  have hiRow (i : Fin k) : IntegrableOn (fun q : Fin 4 → ℝ => ∑ j, JS i q*JV j q) (B (2*R)) :=
    integrable_finsetSum Finset.univ (fun j _ => hiPair i j)
  have hiSum : IntegrableOn (fun q : Fin 4 → ℝ => ∑ i, ∑ j, JS i q*JV j q) (B (2*R)) :=
    integrable_finsetSum Finset.univ (fun i _ => hiRow i)
  have hiLeft : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      F (p.1+p.2)*G (p.1+p.2))
      ((volume.restrict (B (2*R))).prod (volume.restrict (B ((k:ℝ)^2)))) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((hFc.mul hGc).comp (continuous_fst.add continuous_snd)).continuousOn
  have hpoint (q : Fin 4 → ℝ) :
      (∫ y in B ((k:ℝ)^2), F (q+y)*G (q+y)) ≤
        D/((k:ℝ)^2)^2*(∑ i, ∑ j, JS i q*JV j q) := by
    have hh := bourgainSourceGridBound_coarse_shift_entry hk hl hD
      ι τ S V z c w v hw hv hs ht hsep q
    change (∫ y in B ((k:ℝ)^2), F (q+y)*G (q+y)) ≤
      D/((k:ℝ)^2)^2*(∑ i, JS i q)*(∑ j, JV j q) at hh
    have he : (∑ i, JS i q)*(∑ j, JV j q) = ∑ i, ∑ j, JS i q*JV j q := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    exact hh.trans_eq (by rw [mul_assoc,he])
  have hcomp := setIntegral_mono_on hiLeft.integral_prod_left
    (hiSum.const_mul (D/((k:ℝ)^2)^2)) measurableSet_Icc (fun q _ => hpoint q)
  have hsumIntegral :
      (∫ q in B (2*R), ∑ i, ∑ j, JS i q*JV j q) =
        ∑ i, ∑ j, ∫ q in B (2*R), JS i q*JV j q := by
    rw [integral_finsetSum Finset.univ (fun i _ => hiRow i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j _ => hiPair i j)
  rw [integral_const_mul,hsumIntegral] at hcomp
  have havg := bourgain_finite_box_average hK.le hKR
    (fun x : Fin 4 → ℝ => F x*G x) (hFc.mul hGc)
    (fun x => mul_nonneg
      (bourgainSourceSixMoment_nonneg (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) x)
      (bourgainSourceSixMoment_nonneg (Finset.univ.sigma V)
        (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2) x))
  exact havg.trans hcomp

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSourceCurve_coarse_pair_bound {ε ν : ℝ}
    (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C > (0:ℝ), ∀ (k d : ℕ) (R : ℝ), 0 < k → 0 < R → (k:ℝ)^2 ≤ R →
      1/(k:ℝ) ≤ ν/2 →
      5*(2*R)*(1/(k:ℝ))^3 ≤ 1 →
      5*(20*R)*((1/(k:ℝ))/(2:ℝ)^d)^3 ≤ 1 →
      1 ≤ ((1/(k:ℝ))/(2:ℝ)^d)*(20*R) →
      3/(100*(20*R)) ≤ ((1/(k:ℝ))/(2:ℝ)^d)^2 →
      ∀ (ι τ : Type u) (S : Fin (k*2^d) → Finset ι) (V : Fin (k*2^d) → Finset τ)
        (z : Fin (k*2^d) → ι → ℂ) (c : Fin (k*2^d) → τ → ℂ)
        (w : Fin (k*2^d) → ι → ℝ) (v : Fin (k*2^d) → τ → ℝ),
        (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ i ∈ V j, 0 ≤ v j i) →
        (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
          ((j:ℕ)/((k*2^d:ℕ):ℝ)) (((j:ℕ)+1)/((k*2^d:ℕ):ℝ))) →
        (∀ j, ∀ i ∈ V j, Real.sqrt (v j i) ∈ Icc
          ((j:ℕ)/((k*2^d:ℕ):ℝ)) (((j:ℕ)+1)/((k*2^d:ℕ):ℝ))) →
        (∀ j h, ∀ i ∈ S j, ∀ t ∈ V h, ν ≤ |Real.sqrt (w j i)-Real.sqrt (v h t)|) →
        let e : Fin k × Fin (2^d) ≃ Fin (k*2^d) := finProdFinEquiv
        let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin (2^d) => S (e (i,j)))
        let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin (2^d) => V (e (i,j)))
        let Z := fun i : Fin k => fun ji : (_j : Fin (2^d)) × ι => z (e (i,ji.1)) ji.2
        let Q := fun i : Fin k => fun ji : (_j : Fin (2^d)) × τ => c (e (i,ji.1)) ji.2
        let X := fun i : Fin k => fun ji : (_j : Fin (2^d)) × ι => w (e (i,ji.1)) ji.2
        let Y := fun i : Fin k => fun ji : (_j : Fin (2^d)) × τ => v (e (i,ji.1)) ji.2
        ∀ i j : Fin k,
          (∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R),
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
              bourgainSourceSixMoment (T i) (Z i) (X i) (q+x))*
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*
              bourgainSourceSixMoment (U j) (Q j) (Y j) (q+x))) ≤
            C*(20*(k:ℝ)^2)^8*(2:ℝ)^((ε+4)*d)/(20*R)^4*
              (∑ r : Fin (2^d), ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
                bourgainSourceSixMoment (S (e (i,r))) (z (e (i,r))) (w (e (i,r))) x)*
              (∑ r : Fin (2^d), ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
                bourgainSourceSixMoment (V (e (j,r))) (c (e (j,r))) (v (e (j,r))) x) := by
  obtain ⟨E,hE,hlocal⟩ := exists_bourgainSourceCurve_averaged_local_decoupling.{u} hε
  let Dν := (6*(ν/2)^4)⁻¹
  have hDν : 0 < Dν := by dsimp [Dν]; positivity
  refine ⟨E*Dν,by positivity,?_⟩
  intro k d R hk hR hKR hσν hrem hfine hδR hwidth ι τ S V z c w v hw hv hs ht hsep
  let e : Fin k × Fin (2^d) ≃ Fin (k*2^d) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin (2^d) => S (e (i,j)))
  let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin (2^d) => V (e (i,j)))
  let Z := fun i : Fin k => fun ji : (_j : Fin (2^d)) × ι => z (e (i,ji.1)) ji.2
  let Q := fun i : Fin k => fun ji : (_j : Fin (2^d)) × τ => c (e (i,ji.1)) ji.2
  let X := fun i : Fin k => fun ji : (_j : Fin (2^d)) × ι => w (e (i,ji.1)) ji.2
  let Y := fun i : Fin k => fun ji : (_j : Fin (2^d)) × τ => v (e (i,ji.1)) ji.2
  let JS := fun (i : Fin k) (q : Fin 4 → ℝ) =>
    ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*bourgainSourceSixMoment (T i) (Z i) (X i) (q+x)
  let JV := fun (i : Fin k) (q : Fin 4 → ℝ) =>
    ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*(k:ℝ)^2) x*bourgainSourceSixMoment (U i) (Q i) (Y i) (q+x)
  let AS := fun i : Fin k => ∑ r : Fin (2^d), ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (S (e (i,r))) (z (e (i,r))) (w (e (i,r))) x
  let AV := fun i : Fin k => ∑ r : Fin (2^d), ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (V (e (i,r))) (c (e (i,r))) (v (e (i,r))) x
  let P := E*(20*(k:ℝ)^2)^8*(2:ℝ)^((ε+4)*d)/(20*R)^4
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hAS (i : Fin k) : 0 ≤ AS i := Finset.sum_nonneg (fun r _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (bourgainSourceSixMoment_nonneg (S (e (i,r))) (z (e (i,r))) (w (e (i,r))) x)))
  have hAV (i : Fin k) : 0 ≤ AV i := Finset.sum_nonneg (fun r _ => integral_nonneg (fun x =>
    mul_nonneg (bourgainRadialWeight_nonneg _ _)
      (bourgainSourceSixMoment_nonneg (V (e (i,r))) (c (e (i,r))) (v (e (i,r))) x)))
  dsimp only
  intro i j
  change (∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R), JS i q*JV j q) ≤
    (E*Dν)*(20*(k:ℝ)^2)^8*(2:ℝ)^((ε+4)*d)/(20*R)^4*AS i*AV j
  have hright : 0 ≤ (E*Dν)*(20*(k:ℝ)^2)^8*(2:ℝ)^((ε+4)*d)/(20*R)^4*AS i*AV j :=
    mul_nonneg (mul_nonneg (by positivity) (hAS i)) (hAV j)
  by_cases hTi : (T i).Nonempty
  swap
  · have he : T i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTi
    have hz (q : Fin 4 → ℝ) : JS i q = 0 := by simp [JS,he,bourgainSourceSixMoment]
    simpa only [hz,zero_mul,integral_zero] using hright
  by_cases hUj : (U j).Nonempty
  swap
  · have he : U j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hUj
    have hz (q : Fin 4 → ℝ) : JV j q = 0 := by simp [JV,he,bourgainSourceSixMoment]
    simpa only [hz,mul_zero,integral_zero] using hright
  obtain ⟨si,hsi⟩ := hTi
  obtain ⟨vi,hvi⟩ := hUj
  let a := (i:ℕ)/(k:ℝ)
  let b := (j:ℕ)/(k:ℝ)
  let σ := 1/(k:ℝ)
  have hsiRange : Real.sqrt (X i si) ∈ Icc a (a+σ) := by
    have hh := bourgainSource_grid_coarse_interval hk (by positivity : 0 < 2^d) S w hs i si hsi
    have he : ((i:ℕ)+1)/(k:ℝ)=a+σ := by dsimp [a,σ]; ring
    rw [he] at hh
    exact hh
  have hviRange : Real.sqrt (Y j vi) ∈ Icc b (b+σ) := by
    have hh := bourgainSource_grid_coarse_interval hk (by positivity : 0 < 2^d) V v ht j vi hvi
    have he : ((j:ℕ)+1)/(k:ℝ)=b+σ := by dsimp [b,σ]; ring
    rw [he] at hh
    exact hh
  have hseparated := hsep (e (i,si.1)) (e (j,vi.1)) si.2
    (Finset.mem_sigma.mp hsi).2 vi.2 (Finset.mem_sigma.mp hvi).2
  have hcenter := bourgain_coarse_center_separation hν hσν hsiRange hviRange hseparated
  have hcent (r : Fin k) : 0 ≤ (r:ℕ)/(k:ℝ) ∧ (r:ℕ)/(k:ℝ)+σ ≤ 1 := by
    refine ⟨by positivity,?_⟩
    have htop : ((r:ℕ)+1)/(k:ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast Nat.succ_le_of_lt r.isLt
    convert htop using 1
    dsimp [σ]
    ring
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ₁ : σ ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<k)).mpr
    exact_mod_cast Nat.one_le_of_lt hk
  have hgrid {κ : Type u} (A : Fin (k*2^d) → Finset κ) (f : Fin (k*2^d) → κ → ℝ)
      (hh : ∀ h, ∀ s ∈ A h, Real.sqrt (f h s) ∈ Icc
        ((h:ℕ)/((k*2^d:ℕ):ℝ)) (((h:ℕ)+1)/((k*2^d:ℕ):ℝ))) (r : Fin k) :
      ∀ t, ∀ s ∈ A (e (r,t)), Real.sqrt (f (e (r,t)) s) ∈ Icc
        ((r:ℕ)/(k:ℝ)+σ*((t:ℕ)/((2^d:ℕ):ℝ)))
        ((r:ℕ)/(k:ℝ)+σ*(((t:ℕ)+1)/((2^d:ℕ):ℝ))) := by
    intro t s hts
    have hh' := hh (e (r,t)) s hts
    have hc := finGrid_cell hk (by positivity : 0 < 2^d) r t
    simp only [e,Nat.cast_mul] at hh'
    rw [hc.1,hc.2] at hh'
    exact hh'
  have hscale : 10*(2*R)=20*R := by ring
  have hh := hlocal d a b σ (2*R) (20*(k:ℝ)^2)
    (hcent i).1 (hcent i).2 (hcent j).1 (hcent j).2 hcenter.2.1 hσ hσ₁
    (by positivity) hrem (by simpa only [hscale] using hfine)
    (by simpa only [hscale] using hδR) (by simpa only [hscale] using hwidth)
    (by positivity) (by nlinarith) ι τ
    (fun r => S (e (i,r))) (fun r => V (e (j,r)))
    (fun r => z (e (i,r))) (fun r => c (e (j,r)))
    (fun r => w (e (i,r))) (fun r => v (e (j,r)))
    (fun r => hw (e (i,r))) (fun r => hv (e (j,r)))
    (hgrid S w hs i) (hgrid V v ht j)
  simp only [hscale] at hh
  change (∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R), JS i q*JV j q) ≤
    P*(6*(b-a)^4)⁻¹*AS i*AV j at hh
  calc
    _ ≤ _ := hh
    _ ≤ P*Dν*AS i*AV j := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcenter.2.2 hP) (hAS i)) (hAV j)
    _ = _ := by dsimp [P]; ring

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025

private theorem bourgain_bootstrap_coefficient {x : ℝ} (hx : 0 < x)
    (d : ℕ) (ε D E : ℝ) :
    D/(x^2)^2*(E*(20*x^2)^8*(2:ℝ)^((ε+4)*d)/(20*(x*(2:ℝ)^d)^2)^4) =
      (2*x^2)^4*((E*20^4/16)*D*(2:ℝ)^(ε*d)/((x*(2:ℝ)^d)^2)^2) := by
  have he : (ε+4)*(d:ℝ)=ε*d+((d*4:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_add (by norm_num),Real.rpow_natCast,pow_mul]
  field_simp
  ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSourceGridBound_step {ε ν : ℝ}
    (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C > (0:ℝ), ∀ (k d : ℕ) (D : ℝ), 0 < k → 0 < d →
      let R := ((k*2^d:ℕ):ℝ)^2
      1/(k:ℝ) ≤ ν/2 →
      5*(2*R)*(1/(k:ℝ))^3 ≤ 1 →
      5*(20*R)*((1/(k:ℝ))/(2:ℝ)^d)^3 ≤ 1 →
      1 ≤ ((1/(k:ℝ))/(2:ℝ)^d)*(20*R) →
      3/(100*(20*R)) ≤ ((1/(k:ℝ))/(2:ℝ)^d)^2 →
      BourgainSourceGridBound.{u} k ν D →
        k < k*2^d ∧ BourgainSourceGridBound.{u} (k*2^d) ν (C*D*(2:ℝ)^(ε*d)) := by
  obtain ⟨E,hE,hpair⟩ := exists_bourgainSourceCurve_coarse_pair_bound.{u} hε hν
  let Cstep := E*20^4/16
  have hCstep : 0 < Cstep := by dsimp [Cstep]; positivity
  refine ⟨Cstep,hCstep,?_⟩
  intro k d D hk hd
  dsimp only
  intro hσν hrem hfine hδR hwidth hD
  have htwo : 2 ≤ (2:ℕ)^d := by
    have h := pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) (Nat.succ_le_of_lt hd)
    simpa only [pow_one] using h
  have hkN : k < k*2^d := by nlinarith [Nat.mul_le_mul_left k htwo]
  refine ⟨hkN,⟨mul_nonneg (mul_nonneg hCstep.le hD.1) (by positivity),?_⟩⟩
  intro ι τ S V z c w v hw hv hs ht hsep
  let R := ((k*2^d:ℕ):ℝ)^2
  let K := (k:ℝ)^2
  let e : Fin k × Fin (2^d) ≃ Fin (k*2^d) := finProdFinEquiv
  let T := fun i : Fin k => Finset.univ.sigma (fun j : Fin (2^d) => S (e (i,j)))
  let U := fun i : Fin k => Finset.univ.sigma (fun j : Fin (2^d) => V (e (i,j)))
  let Z := fun i : Fin k => fun ji : (_j : Fin (2^d)) × ι => z (e (i,ji.1)) ji.2
  let Q := fun i : Fin k => fun ji : (_j : Fin (2^d)) × τ => c (e (i,ji.1)) ji.2
  let X := fun i : Fin k => fun ji : (_j : Fin (2^d)) × ι => w (e (i,ji.1)) ji.2
  let Y := fun i : Fin k => fun ji : (_j : Fin (2^d)) × τ => v (e (i,ji.1)) ji.2
  let I := fun i j : Fin k => ∫ q : Fin 4 → ℝ in Icc (fun _ => -(2*R)) (fun _ => 2*R),
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*K) x*bourgainSourceSixMoment (T i) (Z i) (X i) (q+x))*
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*K) x*bourgainSourceSixMoment (U j) (Q j) (Y j) (q+x))
  let AS := fun i : Fin k => ∑ r : Fin (2^d), ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (S (e (i,r))) (z (e (i,r))) (w (e (i,r))) x
  let AV := fun i : Fin k => ∑ r : Fin (2^d), ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (V (e (i,r))) (c (e (i,r))) (v (e (i,r))) x
  let JS := ∑ r, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (S r) (z r) (w r) x
  let JV := ∑ r, ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
    bourgainSourceSixMoment (V r) (c r) (v r) x
  let J := ∫ x : Fin 4 → ℝ in Icc (fun _ => -R) (fun _ => R),
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) x*
    bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2) x
  let L := E*(20*K)^8*(2:ℝ)^((ε+4)*d)/(20*R)^4
  have hR : 0 < R := by dsimp [R]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hKR : K ≤ R := by
    have hp : (1:ℝ) ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
    have hn := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    simp only [mul_one] at hn
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg k : (0:ℝ) ≤ k) hn 2
    simpa only [K,R,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hi (i j : Fin k) : I i j ≤ L*AS i*AV j := by
    exact hpair k d R hk hR hKR hσν hrem hfine hδR hwidth
      ι τ S V z c w v hw hv hs ht hsep i j
  have hsumS : (∑ i, AS i)=JS :=
    (finGrid_sum (k:=k) (l:=2^d) (fun r => ∫ x : Fin 4 → ℝ,
      bourgainRadialWeight (20*R) x*bourgainSourceSixMoment (S r) (z r) (w r) x)).symm
  have hsumV : (∑ j, AV j)=JV :=
    (finGrid_sum (k:=k) (l:=2^d) (fun r => ∫ x : Fin 4 → ℝ,
      bourgainRadialWeight (20*R) x*bourgainSourceSixMoment (V r) (c r) (v r) x)).symm
  have hfactor : (∑ i, ∑ j, L*AS i*AV j)=L*(∑ i, AS i)*(∑ j, AV j) := by
    calc
      _ = L*(∑ i, ∑ j, AS i*AV j) := by simp only [Finset.mul_sum,mul_assoc]
      _ = L*((∑ i, AS i)*(∑ j, AV j)) :=
        congrArg (fun q : ℝ => L*q) (Finset.sum_mul_sum Finset.univ Finset.univ AS AV).symm
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hi i j))
  rw [hfactor,hsumS,hsumV] at hsum
  have havg := bourgainSourceGridBound_coarse_average_entry hk
    (by positivity : 0 < 2^d) hD hKR ι τ S V z c w v hw hv hs ht hsep
  change (2*K)^4*J ≤ D/K^2*(∑ i, ∑ j, I i j) at havg
  have htotal := havg.trans (mul_le_mul_of_nonneg_left hsum (div_nonneg hD.1 (sq_nonneg K)))
  have hcoef : D/K^2*L=(2*K)^4*(Cstep*D*(2:ℝ)^(ε*d)/R^2) := by
    have h := bourgain_bootstrap_coefficient (by positivity : (0:ℝ)<k) d ε D E
    simpa only [K,L,R,Cstep,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h
  change J ≤ Cstep*D*(2:ℝ)^(ε*d)/R^2*JS*JV
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<(2*K)^4)).mp
  calc
    _ ≤ D/K^2*(L*JS*JV) := htotal
    _ = (D/K^2*L)*JS*JV := by ring
    _ = ((2*K)^4*(Cstep*D*(2:ℝ)^(ε*d)/R^2))*JS*JV := by rw [hcoef]
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainSourceGridBound_dyadic_step {ε ν : ℝ}
    (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (D : ℝ), 9 ≤ n →
      let m := (2*n+2)/3+2
      1/(2:ℝ)^m ≤ ν/2 →
      BourgainSourceGridBound.{u} (2^m) ν D →
        m < n ∧ BourgainSourceGridBound.{u} (2^n) ν (C*D*(2:ℝ)^(ε*(n-m:ℕ))) := by
  obtain ⟨C,hC,hstep⟩ := exists_bourgainSourceGridBound_step.{u} hε hν
  refine ⟨C,hC,?_⟩
  intro n D hn
  dsimp only
  intro hsep hD
  let m := (2*n+2)/3+2
  have hm := bourgain_bootstrap_depth hn
  change m < n ∧ 2*n+6 ≤ 3*m ∧ n ≤ 2*m at hm
  have he : 2^m*2^(n-m)=(2:ℕ)^n := by
    rw [←pow_add,Nat.add_sub_of_le hm.1.le]
  have hsc := bourgain_bootstrap_scale_conditions hm.1.le hm.2.1 (by omega : 7 ≤ n)
  dsimp only at hsc
  have hR : (((2^m)*(2^(n-m)):ℕ):ℝ)^2=((2:ℝ)^n)^2 := by
    rw [he]
    norm_cast
  have hh := hstep (2^m) (n-m) D (by positivity) (by omega)
  dsimp only at hh
  rw [hR] at hh
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hh
  have hs : 10*(2*((2:ℝ)^n)^2)=20*((2:ℝ)^n)^2 := by ring
  have hresult := hh hsep hsc.2.2.2.1
    (by simpa only [hs] using hsc.2.2.2.2.1)
    (by simpa only [hs] using hsc.2.2.2.2.2.1)
    (by simpa only [hs] using hsc.2.2.2.2.2.2.1) hD
  exact ⟨hm.1,by simpa only [he] using hresult.2⟩

end TaoTrudgianYang2025

noncomputable section
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainSourceGridBound_epsilon {ε ν : ℝ}
    (hε : 0 < ε) (hν : 0 < ν) :
    ∃ A > (0:ℝ), ∀ n : ℕ,
      BourgainSourceGridBound.{u} (2^n) ν (A*(2:ℝ)^(ε*n)) := by
  let η := ε/2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨C,hC,hstep⟩ := exists_bourgainSourceGridBound_dyadic_step.{u} hη hν
  obtain ⟨C₀,hC₀,hbase⟩ := exists_bourgainSourceGridBound_polynomial.{u}
  obtain ⟨q,hq⟩ := pow_unbounded_of_one_lt (2/ν) (by norm_num : (1:ℝ)<2)
  obtain ⟨s,hs⟩ := pow_unbounded_of_one_lt C
    (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hη)
  rw [←Real.rpow_mul_natCast (by norm_num)] at hs
  let N₀ := 18+2*q+3*s
  let A := C₀*((2:ℝ)^N₀)^22
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,hA,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : N₀ ≤ n
    · have hn9 : 9 ≤ n := by dsimp [N₀] at hn; omega
      let m := (2*n+2)/3+2
      have hm := bourgain_bootstrap_depth hn9
      change m<n ∧ 2*n+6≤3*m ∧ n≤2*m at hm
      have hqm : q ≤ m := by dsimp [N₀] at hn; omega
      have hsd : s ≤ n-m := by dsimp [N₀] at hn; dsimp [m]; omega
      have hsep : 1/(2:ℝ)^m ≤ ν/2 := by
        apply (div_le_iff₀ (by positivity : (0:ℝ)<(2:ℝ)^m)).mpr
        have hq' := (div_lt_iff₀ hν).mp hq
        have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hqm
        have hmul := mul_le_mul_of_nonneg_right hpow hν.le
        nlinarith
      have hcontract : C ≤ (2:ℝ)^(η*(n-m:ℕ)) := by
        apply hs.le.trans
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hsd) hη.le)
      have hactual := (hstep n (A*(2:ℝ)^(ε*m)) hn9 hsep (ih m hm.1)).2
      apply bourgainSourceGridBound_mono hactual
      have he : ε*(n:ℝ)=η*((n-m:ℕ):ℝ)+ε*m+η*((n-m:ℕ):ℝ) := by
        rw [Nat.cast_sub hm.1.le]
        dsimp [η]
        ring
      calc
        C*(A*(2:ℝ)^(ε*m))*(2:ℝ)^(η*(n-m:ℕ)) ≤
            (2:ℝ)^(η*(n-m:ℕ))*(A*(2:ℝ)^(ε*m))*(2:ℝ)^(η*(n-m:ℕ)) := by
          gcongr
        _ = A*(2:ℝ)^(ε*n) := by
          rw [he,Real.rpow_add (by norm_num),Real.rpow_add (by norm_num)]
          ring
    · apply bourgainSourceGridBound_mono (hbase n ν)
      have hnN : n ≤ N₀ := by omega
      have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hnN
      have hbaseA : C₀*((2:ℝ)^n)^22 ≤ A := by
        dsimp [A]
        gcongr
      have hone : (1:ℝ)≤(2:ℝ)^(ε*n) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      exact hbaseA.trans (by nlinarith)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- Global dyadic bilinear decoupling for the literal four-coordinate source
curve, with every positive epsilon loss. The constant depends only on epsilon
and the positive cross-family root-frequency separation. All finite arrays,
complex coefficients, multiplicities and closed-grid endpoints are retained.
The proof derives the strictly smaller-grid recurrence and starts strong
induction from a genuine polynomial moment estimate; no decoupling estimate
at any scale is assumed. -/
theorem exists_bourgainSourceCurve_dyadic_decoupling {ε ν : ℝ} (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C > (0:ℝ), ∀ (n : ℕ) (ι τ : Type u)
      (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
      (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
      (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
      (∀ j, ∀ i ∈ S j, 0 ≤ w j i) → (∀ j, ∀ k ∈ V j, 0 ≤ v j k) →
      (∀ j, ∀ i ∈ S j, Real.sqrt (w j i) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
      (∀ j, ∀ k ∈ V j, Real.sqrt (v j k) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
      (∀ j k, ∀ i ∈ S j, ∀ l ∈ V k,
        ν ≤ |Real.sqrt (w j i)-Real.sqrt (v k l)|) →
      (∫ x : Fin 4 → ℝ in Icc (fun _ => -((2:ℝ)^n)^2) (fun _ => ((2:ℝ)^n)^2),
        ‖∑ ji ∈ Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
          (x 0*w ji.1 ji.2+x 1*(w ji.1 ji.2)^2+
            x 2*(w ji.1 ji.2)^((3:ℝ)/2)+x 3*Real.sqrt (w ji.1 ji.2))‖^6*
        ‖∑ jk ∈ Finset.univ.sigma V, c jk.1 jk.2*fordAdditiveCharacter
          (x 0*v jk.1 jk.2+x 1*(v jk.1 jk.2)^2+
            x 2*(v jk.1 jk.2)^((3:ℝ)/2)+x 3*Real.sqrt (v jk.1 jk.2))‖^6) ≤
        C*(2:ℝ)^(ε*n)/(((2:ℝ)^n)^2)^2*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ i ∈ S j, z j i*fordAdditiveCharacter
              (x 0*w j i+x 1*(w j i)^2+x 2*(w j i)^((3:ℝ)/2)+x 3*Real.sqrt (w j i))‖^6)*
          (∑ j, ∫ x : Fin 4 → ℝ, ((1+‖(20*((2:ℝ)^n)^2)⁻¹ • x‖)^100)⁻¹*
            ‖∑ k ∈ V j, c j k*fordAdditiveCharacter
              (x 0*v j k+x 1*(v j k)^2+x 2*(v j k)^((3:ℝ)/2)+x 3*Real.sqrt (v j k))‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSourceGridBound_epsilon.{u} hε hν
  refine ⟨C,hC,?_⟩
  intro n ι τ S V z c w v hw hv hs ht hsep
  have hm := (hbound n).2 ι τ S V z c w v hw hv hs ht hsep
  simpa only [Nat.cast_pow,Nat.cast_ofNat,bourgainRadialWeight,bourgainSourceSixMoment] using hm

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_finite_rectangle_average {K : ℝ}
    (hK : 0 ≤ K) (Q : Fin 4 → ℝ) (f : (Fin 4 → ℝ) → ℝ)
    (hfc : Continuous f) (hf₀ : ∀ x, 0 ≤ f x) :
    (2*K)^4*(∫ x : Fin 4 → ℝ in Icc (-Q) Q, f x) ≤
      ∫ q : Fin 4 → ℝ in Icc (fun i => -(Q i+K)) (fun i => Q i+K),
        ∫ y : Fin 4 → ℝ in Icc (fun _ => -K) (fun _ => K), f (q+y) := by
  let B := Icc (fun _ : Fin 4 => -K) (fun _ => K)
  let U := Icc (-Q) Q
  let V := Icc (fun i => -(Q i+K)) (fun i => Q i+K)
  have hpoint (y : Fin 4 → ℝ) (hy : y ∈ B) :
      (∫ x in U, f x) ≤ ∫ q in V, f (q+y) := by
    have hsub : (fun q => q+y) ⁻¹' U ⊆ V := by
      intro q hq
      constructor
      · intro i
        have hl := hq.1 i
        have hu := hy.2 i
        change -Q i ≤ q i+y i at hl
        change y i ≤ K at hu
        change -(Q i+K) ≤ q i
        linarith
      · intro i
        have hu := hq.2 i
        have hl := hy.1 i
        change q i+y i ≤ Q i at hu
        change -K ≤ y i at hl
        change q i ≤ Q i+K
        linarith
    have hi : IntegrableOn (fun q => f (q+y)) V :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hfc.comp (continuous_id.add continuous_const)).continuousOn
    calc
      _ = ∫ q in (fun q => q+y) ⁻¹' U, f (q+y) :=
        ((measurePreserving_add_right volume y).setIntegral_preimage_emb
          (Homeomorph.addRight y).measurableEmbedding f U).symm
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun q => hf₀ (q+y)))
        (Filter.Eventually.of_forall hsub)
  have hc : Continuous (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2)) :=
    hfc.comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) => f (p.1+p.2))
      ((volume.restrict V).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc) hc.continuousOn
  have hconst : IntegrableOn (fun _y : Fin 4 → ℝ => ∫ x in U, f x) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hconst hi.integral_prod_right measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change volume.real B*(∫ x in U, f x) ≤ _ at hh
  rw [bourgain_cube_mass hK] at hh
  have hswap := integral_integral_swap (f:=fun q y => f (q+y)) hi
  exact hh.trans_eq hswap.symm

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSourceCurve_rectangle_entry {ε ν : ℝ}
    (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ (n : ℕ) (Q : Fin 4 → ℝ)
      (ι τ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset τ)
      (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → τ → ℂ)
      (w : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → τ → ℝ),
      (∀ j, ∀ i∈S j, 0≤w j i) → (∀ j, ∀ i∈V j, 0≤v j i) →
      (∀ j, ∀ i∈S j, Real.sqrt (w j i) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
      (∀ j, ∀ i∈V j, Real.sqrt (v j i) ∈ Icc
        ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
      (∀ j k, ∀ i∈S j, ∀ l∈V k, ν≤|Real.sqrt (w j i)-Real.sqrt (v k l)|) →
      let R := ((2:ℝ)^n)^2
      (2*R)^4*(∫ x : Fin 4 → ℝ in Icc (-Q) Q,
        bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
          (fun ji => w ji.1 ji.2) x*
        bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
          (fun ji => v ji.1 ji.2) x) ≤
        C*(2:ℝ)^(ε*n)/R^2*∑ i, ∑ j,
          ∫ q : Fin 4 → ℝ in Icc (fun t => -(Q t+R)) (fun t => Q t+R),
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
              bourgainSourceSixMoment (S i) (z i) (w i) (q+x))*
            (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*
              bourgainSourceSixMoment (V j) (c j) (v j) (q+x)) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSourceGridBound_epsilon.{u} hε hν
  refine ⟨C,hC,?_⟩
  intro n Q ι τ S V z c w v hw hv hs ht hsep
  let R := ((2:ℝ)^n)^2
  let U := Icc (fun t => -(Q t+R)) (fun t => Q t+R)
  let B := Icc (fun _ : Fin 4 => -R) (fun _ => R)
  let F := bourgainSourceSixMoment (Finset.univ.sigma S)
    (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  let G := bourgainSourceSixMoment (Finset.univ.sigma V)
    (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  let JS := fun (i : Fin (2^n)) (q : Fin 4 → ℝ) =>
    ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment (S i) (z i) (w i) (q+x)
  let JV := fun (j : Fin (2^n)) (q : Fin 4 → ℝ) =>
    ∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*R) x*bourgainSourceSixMoment (V j) (c j) (v j) (q+x)
  have hR : 0<R := by dsimp [R]; positivity
  have hFc := continuous_bourgainSourceSixMoment (Finset.univ.sigma S)
    (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2)
  have hGc := continuous_bourgainSourceSixMoment (Finset.univ.sigma V)
    (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2)
  have hiPair (i j : Fin (2^n)) : IntegrableOn (fun q => JS i q*JV j q) U := by
    let L := (∑ t : Fin 4, |Q t|)+R
    have hQi (t : Fin 4) : Q t≤∑ s : Fin 4, |Q s| :=
      (le_abs_self _).trans (Finset.single_le_sum (fun s _ => abs_nonneg (Q s)) (Finset.mem_univ t))
    have hsub : U ⊆ Icc (fun _ : Fin 4 => -L) (fun _ => L) := by
      intro q hq
      constructor
      · intro t
        have hh := hq.1 t
        have ht' := hQi t
        change -(Q t+R)≤q t at hh
        dsimp [L]
        linarith
      · intro t
        have hh := hq.2 t
        have ht' := hQi t
        change q t≤Q t+R at hh
        dsimp [L]
        linarith
    exact ((bourgain_radial_bilinear_fubini (R:=L) (by positivity : 0<20*R)
      (bourgainSourceSixMoment (S i) (z i) (w i))
      (bourgainSourceSixMoment (V j) (c j) (v j))
      ((∑ si∈S i, ‖z i si‖)^6) ((∑ vi∈V j, ‖c j vi‖)^6)
      (continuous_bourgainSourceSixMoment (S i) (z i) (w i))
      (continuous_bourgainSourceSixMoment (V j) (c j) (v j))
      (bourgainSourceSixMoment_norm_bound (S i) (z i) (w i))
      (bourgainSourceSixMoment_norm_bound (V j) (c j) (v j))).2.2).mono_set hsub
  have hiRow (i : Fin (2^n)) : IntegrableOn (fun q => ∑ j, JS i q*JV j q) U :=
    integrable_finsetSum Finset.univ (fun j _ => hiPair i j)
  have hiSum : IntegrableOn (fun q => ∑ i, ∑ j, JS i q*JV j q) U :=
    integrable_finsetSum Finset.univ (fun i _ => hiRow i)
  have hiLeft : Integrable (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      F (p.1+p.2)*G (p.1+p.2)) ((volume.restrict U).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((hFc.mul hGc).comp (continuous_fst.add continuous_snd)).continuousOn
  have hpoint (q : Fin 4 → ℝ) :
      (∫ y in B, F (q+y)*G (q+y)) ≤
        C*(2:ℝ)^(ε*n)/R^2*(∑ i, ∑ j, JS i q*JV j q) := by
    let zq := fun j i => z j i*fordAdditiveCharacter
      (q 0*w j i+q 1*(w j i)^2+q 2*(w j i)^((3:ℝ)/2)+q 3*Real.sqrt (w j i))
    let cq := fun j i => c j i*fordAdditiveCharacter
      (q 0*v j i+q 1*(v j i)^2+q 2*(v j i)^((3:ℝ)/2)+q 3*Real.sqrt (v j i))
    have hh := (hbound n).2 ι τ S V zq cq w v hw hv hs ht hsep
    dsimp only [zq,cq] at hh
    simp only [bourgainSourceSixMoment_translate,Nat.cast_pow,Nat.cast_ofNat] at hh
    have he : (∑ i, JS i q)*(∑ j, JV j q)=∑ i, ∑ j, JS i q*JV j q := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    have hh' : (∫ y in B, F (q+y)*G (q+y)) ≤
        C*(2:ℝ)^(ε*n)/R^2*(∑ i, JS i q)*(∑ j, JV j q) := by
      simpa only [F,G,B,R,JS,JV,add_comm] using hh
    exact hh'.trans_eq (by rw [mul_assoc,he])
  have hcomp := setIntegral_mono_on hiLeft.integral_prod_left
    (hiSum.const_mul (C*(2:ℝ)^(ε*n)/R^2)) measurableSet_Icc (fun q _ => hpoint q)
  have hsumIntegral : (∫ q in U, ∑ i, ∑ j, JS i q*JV j q)=
      ∑ i, ∑ j, ∫ q in U, JS i q*JV j q := by
    rw [integral_finsetSum Finset.univ (fun i _ => hiRow i)]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum Finset.univ (fun j _ => hiPair i j)
  rw [integral_const_mul,hsumIntegral] at hcomp
  have havg := bourgain_finite_rectangle_average hR.le Q
    (fun x => F x*G x) (hFc.mul hGc)
    (fun x => mul_nonneg
      (bourgainSourceSixMoment_nonneg (Finset.univ.sigma S)
        (fun ji => z ji.1 ji.2) (fun ji => w ji.1 ji.2) x)
      (bourgainSourceSixMoment_nonneg (Finset.univ.sigma V)
        (fun ji => c ji.1 ji.2) (fun ji => v ji.1 ji.2) x))
  exact havg.trans hcomp

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_periodic_weighted_average {T C : ℝ} (hT : 0<T)
    (W f : ℝ → ℝ) (hf : Continuous f)
    (hW : Integrable W)
    (hf₀ : ∀ x, 0≤f x) (M : ℝ) (hb : ∀ x, ‖f x‖≤M)
    (hp : Function.Periodic f T)
    (hshift : ∀ x, ∀ t∈Icc (0:ℝ) T, W (x+t)≤C*W x) :
    T*(∫ x : ℝ, W x*f x) ≤
      C*(∫ x : ℝ, W x)*(∫ t : ℝ in Icc (0:ℝ) T, f t) := by
  let I := Icc (0:ℝ) T
  have hiWf := hW.mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hpoint (t : ℝ) (ht : t∈I) :
      (∫ x : ℝ, W x*f x) ≤ C*(∫ x : ℝ, W x*f (x+t)) := by
    have hc : AEStronglyMeasurable (fun x : ℝ => f (x+t)) volume :=
      (hf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
    have hiR := hW.mul_bdd hc (Filter.Eventually.of_forall (fun x => hb (x+t)))
    calc
      _ = ∫ x : ℝ, W (x+t)*f (x+t) :=
        (integral_add_right_eq_self (μ:=volume) (fun x : ℝ => W x*f x) t).symm
      _ ≤ ∫ x : ℝ, C*(W x*f (x+t)) := integral_mono
        (hiWf.comp_add_right t) (hiR.const_mul C)
        (fun x => (mul_le_mul_of_nonneg_right (hshift x t ht) (hf₀ (x+t))).trans_eq (by ring))
      _ = _ := integral_const_mul C _
  have hi1 : IntegrableOn (fun _t : ℝ => (1:ℝ)) I :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiH : Integrable (fun p : ℝ × ℝ => W p.1*f (p.1+p.2))
      (volume.prod (volume.restrict I)) := by
    have hprod := hW.mul_prod hi1
    have hm := hprod.mul_bdd
      ((hf.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p : ℝ × ℝ => hb (p.1+p.2)))
    simpa only [mul_one] using hm
  have hiConst : IntegrableOn (fun _t : ℝ => ∫ x : ℝ, W x*f x) I :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hiConst
    (hiH.integral_prod_right.const_mul C) measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ,integral_const_mul] at hh
  have hmass : volume.real I=T := by
    dsimp [I,Measure.real]
    rw [Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0≤T-0)]
    ring
  rw [hmass] at hh
  have hswap := integral_integral_swap (f:=fun x t : ℝ => W x*f (x+t)) hiH
  have hperiod (x : ℝ) : (∫ t in I, f (x+t))=∫ t in I, f t := by
    dsimp [I]
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le hT.le,←intervalIntegral.integral_of_le hT.le]
    rw [intervalIntegral.integral_comp_add_left]
    simpa only [zero_add,add_zero,add_comm] using hp.intervalIntegral_add_eq x 0
  have he : (∫ t in I, ∫ x : ℝ, W x*f (x+t))=
      (∫ x : ℝ, W x)*(∫ t in I, f t) := by
    rw [←hswap]
    simp only [integral_const_mul,hperiod]
    exact integral_mul_const _ _
  exact hh.trans_eq (by rw [he]; ring)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_periodic_lorentz_average {T K : ℝ} (hT : 0<T) (hTK : T≤K)
    (f : ℝ → ℝ) (hf : Continuous f) (hf₀ : ∀ x, 0≤f x)
    (M : ℝ) (hb : ∀ x, ‖f x‖≤M) (hp : Function.Periodic f T) :
    T*(∫ x : ℝ, (1+(x/K)^2)⁻¹*f x) ≤
      3*Real.pi*K*(∫ t : ℝ in Icc (0:ℝ) T, f t) := by
  have hK : 0<K := hT.trans_le hTK
  let W := fun x : ℝ => (1+(x/K)^2)⁻¹
  have hW : Integrable W := integrable_inv_one_add_sq.comp_div hK.ne'
  have hshift (x : ℝ) (t : ℝ) (ht : t∈Icc (0:ℝ) T) :
      W (x+t)≤3*W x := by
    have ht₀ : 0≤t/K := div_nonneg ht.1 hK.le
    have ht₁ : t/K≤1 := (div_le_one hK).mpr (ht.2.trans hTK)
    dsimp [W]
    rw [add_div,←one_div,←one_div,mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (x/K+2*(t/K))]
  have hh := bourgain_periodic_weighted_average hT W f hf hW hf₀ M hb hp hshift
  have hmass : (∫ x : ℝ, W x)=K*Real.pi := by
    have he := Measure.integral_comp_div (fun y : ℝ => (1+y^2)⁻¹) K
    simpa only [W,integral_univ_inv_one_add_sq,abs_of_pos hK,smul_eq_mul] using he
  rw [hmass] at hh
  exact hh.trans_eq (by ring)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgain_integer_phase_periodic_average {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (a : ι → ℝ)
    {T K : ℝ} (hT : 0<T) (hTK : T≤K) :
    (∫ x : ℝ, (1+(x/K)^2)⁻¹*
      ‖∑ i∈S, z i*fordAdditiveCharacter (x*((m i:ℝ)/T)+a i)‖^6) ≤
      3*Real.pi*K*(∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter (u*(m i:ℝ)+a i)‖^6) := by
  let F := fun x : ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter (x*((m i:ℝ)/T)+a i)‖^6
  let G := fun u : ℝ => ‖∑ i∈S, z i*fordAdditiveCharacter (u*(m i:ℝ)+a i)‖^6
  have hchar (k : ℤ) : fordAdditiveCharacter (k:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((k:ℝ):ℂ)=(k:ℂ)*(2*Real.pi*Complex.I) := by
      push_cast
      ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  have hp : Function.Periodic F T := by
    intro x
    dsimp [F]
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    have he : (x+T)*((m i:ℝ)/T)+a i =
        (x*((m i:ℝ)/T)+a i)+(m i:ℝ) := by
      field_simp
      ring
    rw [he,fordAdditiveCharacter_add,hchar,mul_one]
  have hc : Continuous F := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hh := bourgain_periodic_lorentz_average hT hTK F hc (by intro x; dsimp [F]; positivity)
    ((∑ i∈S, ‖z i‖)^6)
    (fun x => bourgain_character_six_bound S z (fun i => x*((m i:ℝ)/T)+a i)) hp
  have he (x : ℝ) : F x=G (x/T) := by
    dsimp [F,G]
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun q : ℝ => z i*fordAdditiveCharacter q)
    ring
  have hscale : (∫ x in Icc (0:ℝ) T, F x)=T*(∫ u in Icc (0:ℝ) 1, G u) := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hT.le]
    simp only [he]
    rw [intervalIntegral.integral_comp_div G hT.ne',zero_div,div_self hT.ne',smul_eq_mul,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Icc_eq_integral_Ioc]
  rw [hscale] at hh
  apply (mul_le_mul_iff_right₀ hT).mp
  exact hh.trans_eq (by ring)

end TaoTrudgianYang2025


noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgain_radial_le_lorentz_product (T : ℝ) (x : Fin 4 → ℝ) :
    ((1+‖T⁻¹ • x‖)^100)⁻¹ ≤ ∏ i : Fin 4, (1+(x i/T)^2)⁻¹ := by
  let r := ‖T⁻¹ • x‖
  have hr : 0≤r := norm_nonneg _
  have hcoord (i : Fin 4) : (x i/T)^2≤r^2 := by
    have hh := norm_le_pi_norm (T⁻¹ • x) i
    change ‖T⁻¹*x i‖≤r at hh
    have ha : |x i/T|≤r := by simpa only [Real.norm_eq_abs,div_eq_mul_inv,mul_comm] using hh
    have hp := pow_le_pow_left₀ (abs_nonneg (x i/T)) ha 2
    simpa only [sq_abs] using hp
  have hprod : (∏ i : Fin 4, (1+(x i/T)^2)) ≤ (1+r)^100 := by
    calc
      _ ≤ ∏ _i : Fin 4, (1+r^2) :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => by linarith [hcoord i])
      _ = (1+r^2)^4 := by simp
      _ ≤ ((1+r)^2)^4 := pow_le_pow_left₀ (by positivity) (by nlinarith) 4
      _ = (1+r)^8 := by rw [←pow_mul]
      _ ≤ (1+r)^100 := pow_le_pow_right₀ (by linarith) (by decide)
  have hh := one_div_le_one_div_of_le
    (Finset.prod_pos (fun (i : Fin 4) (_ : i∈Finset.univ) => by positivity)) hprod
  simpa only [one_div,Finset.prod_inv_distrib] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

set_option maxHeartbeats 400000 in
private theorem bourgainSource_integer_coordinate_average {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {T K : ℝ}
    (hT : 0<T) (hTK : T≤K) :
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*
      bourgainSourceSixMoment S z (fun i => (m i:ℝ)/T) x) ≤
      3*Real.pi*K*(∫ y : Fin 3 → ℝ, (∏ j : Fin 3, (1+(y j/K)^2)⁻¹)*
        (∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter
            (u*(m i:ℝ)+y 0*((m i:ℝ)/T)^2+
              y 1*((m i:ℝ)/T)^((3:ℝ)/2)+y 2*Real.sqrt ((m i:ℝ)/T))‖^6)) := by
  have hK : 0<K := hT.trans_le hTK
  let w := fun i => (m i:ℝ)/T
  let F := bourgainSourceSixMoment S z w
  let L := fun t : ℝ => (1+(t/K)^2)⁻¹
  let P := fun y : Fin 3 → ℝ => ∏ j, L (y j)
  let A := fun (y : Fin 3 → ℝ) (i : ι) =>
    y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i)
  let G := fun (y : Fin 3 → ℝ) (u : ℝ) =>
    ‖∑ i∈S, z i*fordAdditiveCharacter (u*(m i:ℝ)+A y i)‖^6
  let H := fun p : ℝ × (Fin 3 → ℝ) => L p.1*P p.2*F (Fin.cons p.1 p.2)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  have hmp : MeasurePreserving e.symm := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).symm
  have he (p : ℝ × (Fin 3 → ℝ)) : e.symm p=Fin.cons p.1 p.2 := by
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Equiv.coe_fn_mk,Fin.insertNth_zero,cast_eq]
  have hFc : Continuous F := continuous_bourgainSourceSixMoment S z w
  have hL : Integrable L := integrable_inv_one_add_sq.comp_div hK.ne'
  have hP : Integrable P := Integrable.fintype_prod (fun _ : Fin 3 => hL)
  have hP4 : Integrable (fun x : Fin 4 → ℝ => ∏ j, L (x j)) :=
    Integrable.fintype_prod (fun _ : Fin 4 => hL)
  have hiPF := hP4.mul_bdd hFc.aestronglyMeasurable
    (Filter.Eventually.of_forall (bourgainSourceSixMoment_norm_bound S z w))
  have hid (p : ℝ × (Fin 3 → ℝ)) :
      (∏ j : Fin 4, L ((e.symm p) j))*F (e.symm p)=H p := by
    rw [he,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,H,P]
  have hiH : Integrable H := by
    have hh := (hmp.integrable_comp_emb e.symm.measurableEmbedding).mpr hiPF
    simpa only [Function.comp_def,hid] using hh
  have hmajor :
      (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*F x) ≤
        ∫ x : Fin 4 → ℝ, (∏ j, L (x j))*F x :=
    integral_mono (integrable_bourgainSource_weighted S z w hK) hiPF (fun x =>
      mul_le_mul_of_nonneg_right (bourgain_radial_le_lorentz_product K x)
        (bourgainSourceSixMoment_nonneg S z w x))
  have hchange : (∫ x : Fin 4 → ℝ, (∏ j, L (x j))*F x)=
      ∫ p : ℝ × (Fin 3 → ℝ), H p := by
    have hh := hmp.integral_comp e.symm.measurableEmbedding
      (fun x : Fin 4 → ℝ => (∏ j, L (x j))*F x)
    simpa only [hid] using hh.symm
  have hGc : Continuous (fun p : (Fin 3 → ℝ) × ℝ => G p.1 p.2) := by
    unfold G A fordAdditiveCharacter
    fun_prop
  have hGb (p : (Fin 3 → ℝ) × ℝ) :
      ‖G p.1 p.2‖≤(∑ i∈S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => p.2*(m i:ℝ)+A p.1 i)
  have hi1 : IntegrableOn (fun _u : ℝ => (1:ℝ)) (Icc (0:ℝ) 1) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiPG : Integrable (fun p : (Fin 3 → ℝ) × ℝ => P p.1*G p.1 p.2)
      (volume.prod (volume.restrict (Icc (0:ℝ) 1))) := by
    have hh := (hP.mul_prod hi1).mul_bdd hGc.aestronglyMeasurable
      (Filter.Eventually.of_forall hGb)
    simpa only [mul_one] using hh
  have hiRight : Integrable (fun y : Fin 3 → ℝ =>
      P y*(∫ u : ℝ in Icc (0:ℝ) 1, G y u)) := by
    have hh := hiPG.integral_prod_left
    simpa only [integral_const_mul] using hh
  have hFcons (y : Fin 3 → ℝ) (t : ℝ) :
      F (Fin.cons t y)=‖∑ i∈S, z i*fordAdditiveCharacter (t*((m i:ℝ)/T)+A y i)‖^6 := by
    dsimp only [F,bourgainSourceSixMoment]
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun q : ℝ => z i*fordAdditiveCharacter q)
    change t*w i+y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i) =
      t*((m i:ℝ)/T)+A y i
    dsimp [A,w]
    ring
  have hpoint (y : Fin 3 → ℝ) :
      (∫ t : ℝ, H (t,y)) ≤ 3*Real.pi*K*(P y*(∫ u in Icc (0:ℝ) 1, G y u)) := by
    have hh := bourgain_integer_phase_periodic_average S z m (A y) hT hTK
    have hPy : 0≤P y := Finset.prod_nonneg (fun j _ => by dsimp [L]; positivity)
    calc
      _ = P y*(∫ t : ℝ, L t*
          ‖∑ i∈S, z i*fordAdditiveCharacter (t*((m i:ℝ)/T)+A y i)‖^6) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with t
        dsimp only [H]
        rw [hFcons]
        ring
      _ ≤ P y*(3*Real.pi*K*(∫ u in Icc (0:ℝ) 1, G y u)) :=
        mul_le_mul_of_nonneg_left hh hPy
      _ = _ := by ring
  have hlast := integral_mono hiH.integral_prod_right
    (hiRight.const_mul (3*Real.pi*K)) hpoint
  rw [integral_const_mul] at hlast
  have hfinal := hmajor.trans (hchange.le.trans ((integral_prod_symm H hiH).le.trans hlast))
  have hGphase (y : Fin 3 → ℝ) (u : ℝ) :
      G y u=‖∑ i∈S, z i*fordAdditiveCharacter
        (u*(m i:ℝ)+y 0*((m i:ℝ)/T)^2+
          y 1*((m i:ℝ)/T)^((3:ℝ)/2)+y 2*Real.sqrt ((m i:ℝ)/T))‖^6 := by
    dsimp only [G]
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun q : ℝ => z i*fordAdditiveCharacter q)
    dsimp [A,w]
    ring
  simpa only [hGphase,F,w,P,L] using hfinal

end TaoTrudgianYang2025

noncomputable section
namespace TaoTrudgianYang2025

private theorem bourgain_sqrt_quadratic_remainder (a u : ℝ)
    (ha : a≠0) (hs : u+a≠0) :
    u=a+(u^2-a^2)/(2*a)-(u^2-a^2)^2/(8*a^3)+
      (u^2-a^2)^3*(u+3*a)/(8*a^3*(u+a)^3) := by
  field_simp
  ring

private theorem bourgain_three_halves_quadratic_remainder (a u : ℝ)
    (ha : a≠0) (hs : u+a≠0) :
    u^3=a^3+(3*a/2)*(u^2-a^2)+(3/(8*a))*(u^2-a^2)^2-
      (u^2-a^2)^3*(3*u+a)/(8*a*(u+a)^3) := by
  field_simp
  ring

private theorem bourgainSource_quadratic_phase_exact {b t : ℝ}
    (hb : 0<b) (ht : 0≤t) (x : Fin 4 → ℝ) :
    let a := Real.sqrt b
    let u := Real.sqrt t
    let h := t-b
    x 0*t+x 1*t^2+x 2*t^((3:ℝ)/2)+x 3*Real.sqrt t =
      (x 0*b+x 1*b^2+x 2*a^3+x 3*a)+
      h*(x 0+2*b*x 1+(3*a/2)*x 2+x 3/(2*a))+
      h^2*(x 1+(3/(8*a))*x 2-x 3/(8*a^3))+
      h^3*(-x 2*(3*u+a)/(8*a*(u+a)^3)+
        x 3*(u+3*a)/(8*a^3*(u+a)^3)) := by
  dsimp only
  let a := Real.sqrt b
  let u := Real.sqrt t
  have ha : 0<a := Real.sqrt_pos.mpr hb
  have hu : 0≤u := Real.sqrt_nonneg t
  have hab : a^2=b := Real.sq_sqrt hb.le
  have hut : u^2=t := Real.sq_sqrt ht
  have hs : u+a≠0 := by positivity
  have hroot := bourgain_sqrt_quadratic_remainder a u ha.ne' hs
  have hcub := bourgain_three_halves_quadratic_remainder a u ha.ne' hs
  rw [hut,hab] at hroot hcub
  have hpower : t^((3:ℝ)/2)=u^3 := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul ht]
    congr 1
    norm_num
  rw [hpower]
  change x 0*t+x 1*t^2+x 2*u^3+x 3*u = _
  dsimp only [a,u] at hroot hcub ⊢
  linear_combination x 2*hcub+x 3*hroot

end TaoTrudgianYang2025

noncomputable section
open GafniTao Set
open scoped ContDiff
namespace TaoTrudgianYang2025

private def bourgainOriginalRemainderPhase (p : Fin 4 → ℝ) (s : ℝ) : ℝ :=
  let a := p 0
  let u := Real.sqrt (a^2+p 1*s)
  show ℝ from
    -s^3*p 2*(3*u+a)/(8*a*(u+a)^3)-s^2*p 3/(2*a*(u+a)^2)

private def bourgainOriginalRemainderCutoff (p : Fin 4 → ℝ) (s : ℝ) : ℂ :=
  (modelPhaseBufferedCutoff (-2) 2 (1/2) s : ℂ)*
    fordAdditiveCharacter (bourgainOriginalRemainderPhase p s)

private theorem bourgainOriginalRemainderPhase_contDiffAt
    (q : (Fin 4 → ℝ) × ℝ) (ha : 0<q.1 0) (hu : 0<(q.1 0)^2+q.1 1*q.2) :
    ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ =>
      bourgainOriginalRemainderPhase r.1 r.2) q := by
  have hA : ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ => r.1 0) q := by fun_prop
  have hD : ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ => r.1 1) q := by fun_prop
  have hX : ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ => r.1 2) q := by fun_prop
  have hY : ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ => r.1 3) q := by fun_prop
  have hU := ((hA.pow 2).add (hD.mul contDiffAt_snd)).sqrt hu.ne'
  have hsum : Real.sqrt ((q.1 0)^2+q.1 1*q.2)+q.1 0≠0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) ha)
  have hd₁ : 8*q.1 0*(Real.sqrt ((q.1 0)^2+q.1 1*q.2)+q.1 0)^3≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero _ hsum)
  have hd₂ : 2*q.1 0*(Real.sqrt ((q.1 0)^2+q.1 1*q.2)+q.1 0)^2≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha.ne') (pow_ne_zero _ hsum)
  exact ((((contDiffAt_snd.pow 3).neg.mul hX).mul
    ((contDiffAt_const.mul hU).add hA)).div
      ((contDiffAt_const.mul hA).mul ((hU.add hA).pow 3)) hd₁).sub
        (((contDiffAt_snd.pow 2).mul hY).div
          ((contDiffAt_const.mul hA).mul ((hU.add hA).pow 2)) hd₂)

private theorem bourgainOriginalRemainderCutoff_contDiffAt
    (q : (Fin 4 → ℝ) × ℝ) (ha : 0<q.1 0) (hu : 0<(q.1 0)^2+q.1 1*q.2) :
    ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ =>
      bourgainOriginalRemainderCutoff r.1 r.2) q := by
  have hc : ContDiffAt ℝ ∞ (fun r : (Fin 4 → ℝ) × ℝ =>
      (modelPhaseBufferedCutoff (-2) 2 (1/2) r.2 : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
      ((modelPhaseBufferedCutoff_contDiff (-2) 2 (1/2)).contDiffAt.comp q contDiffAt_snd)
  have hp := bourgainOriginalRemainderPhase_contDiffAt q ha hu
  unfold bourgainOriginalRemainderCutoff fordAdditiveCharacter
  exact hc.mul ((contDiffAt_const.mul
    (Complex.ofRealCLM.contDiff.contDiffAt.comp q hp)).cexp)

private theorem bourgainOriginalRemainderCutoff_support (p : Fin 4 → ℝ) :
    tsupport (bourgainOriginalRemainderCutoff p) ⊆ Icc (-2:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hk : s ∈ tsupport (modelPhaseBufferedCutoff (-2) 2 (1/2)) := by
    apply subset_closure
    intro hz
    exact hs (by rw [bourgainOriginalRemainderCutoff,hz,Complex.ofReal_zero,zero_mul])
  have hb := modelPhaseBufferedCutoff_tsupport (by norm_num : (0:ℝ)<1/2) hk
  constructor <;> linarith [hb.1,hb.2]

private theorem bourgainOriginalRemainder_parameter_positive
    (p : Fin 4 → ℝ) (s : ℝ) (ha : (1/2:ℝ)≤p 0)
    (hδ : p 1 ∈ Icc (0:ℝ) (1/16)) (hs : s∈Icc (-2:ℝ) 2) :
    0<p 0 ∧ 0<(p 0)^2+p 1*s := by
  have hs' : (0:ℝ) ≤ s + 2 := by linarith [hs.1]
  have hp := mul_nonneg hδ.1 hs'
  constructor <;> nlinarith [hδ.2,sq_nonneg (p 0-1/2)]

end TaoTrudgianYang2025


noncomputable section
open GafniTao Set
open scoped ContDiff
namespace TaoTrudgianYang2025

private theorem bourgainOriginalRemainderCutoff_smooth
    (p : Fin 4 → ℝ) (ha : (1/2:ℝ)≤p 0)
    (hδ : p 1 ∈ Icc (0:ℝ) (1/16)) :
    ContDiff ℝ ∞ (bourgainOriginalRemainderCutoff p) := by
  apply contDiff_iff_contDiffAt.mpr
  intro s
  by_cases hs : s∈Icc (-2:ℝ) 2
  · have hp := bourgainOriginalRemainder_parameter_positive p s ha hδ hs
    exact (bourgainOriginalRemainderCutoff_contDiffAt (p,s) hp.1 hp.2).comp s
      (contDiffAt_const.prodMk contDiffAt_id)
  · have hz : s∉tsupport (bourgainOriginalRemainderCutoff p) :=
      fun h => hs (bourgainOriginalRemainderCutoff_support p h)
    exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hz)

end TaoTrudgianYang2025


noncomputable section
open Set
open scoped ContDiff Topology
namespace TaoTrudgianYang2025

private theorem bourgain_partial_iteratedDeriv_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E × ℝ → ℂ) {V : Set (E × ℝ)} (hV : IsOpen V)
    (hf : ∀ q∈V, ContDiffAt ℝ ∞ F q) (j : ℕ) :
    ∀ q∈V, ContDiffAt ℝ ∞
      (fun r : E × ℝ => iteratedDeriv j (fun s : ℝ => F (r.1,s)) r.2) q := by
  induction j with
  | zero =>
    simpa only [iteratedDeriv_zero] using hf
  | succ j ih =>
    let H := fun r : E × ℝ => iteratedDeriv j (fun s : ℝ => F (r.1,s)) r.2
    have heq (q : E × ℝ) (hq : q∈V) :
        iteratedDeriv (j+1) (fun s : ℝ => F (q.1,s)) q.2 =
          (fderiv ℝ H q) (0,1) := by
      rw [iteratedDeriv_succ]
      have hd : DifferentiableAt ℝ H q := (ih q hq).differentiableAt (by simp)
      have hm : HasDerivAt (fun t : ℝ => (q.1,t)) (0,1) q.2 :=
        (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
      have hh := (hd.hasFDerivAt.comp_hasDerivAt q.2 hm).deriv
      simpa only [Function.comp_def,H] using hh
    intro q hq
    have hc : ContDiffAt ℝ ∞ (fun r : E × ℝ => (fderiv ℝ H r) (0,1)) q :=
      ((ih q hq).fderiv_right (by simp)).clm_apply contDiffAt_const
    apply hc.congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hq] with r hr
    exact heq r hr

end TaoTrudgianYang2025


noncomputable section
open Set
open scoped ContDiff BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainOriginalRemainderCutoff_derivative_bound (Q : ℕ) :
    ∃ C : ℝ, 1≤C ∧
      ∀ p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32],
      ∀ s : ℝ, ∀ j≤Q,
        ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖≤C := by
  let V : Set ((Fin 4 → ℝ) × ℝ) :=
    {q | 0<q.1 0 ∧ 0<(q.1 0)^2+q.1 1*q.2}
  let P := Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32]
  let K := P ×ˢ Icc (-2:ℝ) 2
  let F := fun q : (Fin 4 → ℝ) × ℝ => bourgainOriginalRemainderCutoff q.1 q.2
  let B := fun q : (Fin 4 → ℝ) × ℝ =>
    ∑ j∈Finset.range (Q+1), ‖iteratedDeriv j (fun s : ℝ => F (q.1,s)) q.2‖
  have hV : IsOpen V :=
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun q : (Fin 4 → ℝ) × ℝ => q.1 0))).inter
      (isOpen_lt continuous_const (by fun_prop : Continuous
        (fun q : (Fin 4 → ℝ) × ℝ => (q.1 0)^2+q.1 1*q.2)))
  have hf : ∀ q∈V, ContDiffAt ℝ ∞ F q :=
    fun q hq => bourgainOriginalRemainderCutoff_contDiffAt q hq.1 hq.2
  have hKV : K⊆V := by
    intro q hq
    have ha : (1/2:ℝ)≤q.1 0 := hq.1.1 0
    have hδ : q.1 1∈Icc (0:ℝ) (1/16) := ⟨hq.1.1 1,hq.1.2 1⟩
    exact bourgainOriginalRemainder_parameter_positive q.1 q.2 ha hδ hq.2
  have hB : ContinuousOn B K := by
    apply continuousOn_finsetSum
    intro j hj q hq
    exact ((bourgain_partial_iteratedDeriv_contDiffAt F hV hf j q (hKV hq)).continuousAt.norm).continuousWithinAt
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s:=K) hB
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro p hp s j hj
  by_cases hs : s∈Icc (-2:ℝ) 2
  · have he : ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖=
        ‖iteratedDeriv j (fun t : ℝ => F (p,t)) s‖ :=
      norm_iteratedFDeriv_eq_norm_iteratedDeriv
    rw [he]
    have hsum : ‖iteratedDeriv j (fun t : ℝ => F (p,t)) s‖≤B (p,s) := by
      exact Finset.single_le_sum (fun k _ => norm_nonneg
        (iteratedDeriv k (fun t : ℝ => F (p,t)) s))
        (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    exact hsum.trans ((le_abs_self _).trans
      ((hM (p,s) ⟨hp,hs⟩).trans (le_max_left _ _)))
  · have hz : iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s=0 := by
      apply Function.notMem_support.mp
      intro h
      exact hs (bourgainOriginalRemainderCutoff_support p
        ((tsupport_iteratedFDeriv_subset j) (subset_closure h)))
    rw [hz,norm_zero]
    exact zero_le_one.trans (le_max_right _ _)

end TaoTrudgianYang2025


noncomputable section
namespace TaoTrudgianYang2025

private theorem bourgain_sqrt_linear_remainder (a u : ℝ)
    (ha : a≠0) (hs : u+a≠0) :
    u=a+(u^2-a^2)/(2*a)-(u^2-a^2)^2/(2*a*(u+a)^2) := by
  field_simp
  ring

private theorem bourgainSource_mixed_phase_exact {b t : ℝ}
    (hb : 0<b) (ht : 0≤t) (x : Fin 4 → ℝ) :
    let a := Real.sqrt b
    let u := Real.sqrt t
    let h := t-b
    x 0*t+x 1*t^2+x 2*t^((3:ℝ)/2)+x 3*Real.sqrt t =
      (x 0*b+x 1*b^2+x 2*a^3+x 3*a)+
      h*(x 0+2*b*x 1+(3*a/2)*x 2+x 3/(2*a))+
      h^2*(x 1+(3/(8*a))*x 2)-
      h^3*x 2*(3*u+a)/(8*a*(u+a)^3)-
      h^2*x 3/(2*a*(u+a)^2) := by
  dsimp only
  let a := Real.sqrt b
  let u := Real.sqrt t
  have ha : 0<a := Real.sqrt_pos.mpr hb
  have hu : 0≤u := Real.sqrt_nonneg t
  have hab : a^2=b := Real.sq_sqrt hb.le
  have hut : u^2=t := Real.sq_sqrt ht
  have hs : u+a≠0 := by positivity
  have hroot := bourgain_sqrt_linear_remainder a u ha.ne' hs
  have hcub := bourgain_three_halves_quadratic_remainder a u ha.ne' hs
  rw [hut,hab] at hroot hcub
  have hpower : t^((3:ℝ)/2)=u^3 := by
    dsimp [u]
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast,←Real.rpow_mul ht]
    congr 1
    norm_num
  rw [hpower]
  dsimp only [a,u] at hroot hcub ⊢
  linear_combination x 2*hcub+x 3*hroot

private theorem bourgainSource_scaled_mixed_phase {b δ s : ℝ}
    (hb : 0<b) (ht : 0≤b+δ*s) (x : Fin 4 → ℝ) :
    let t := b+δ*s
    let a := Real.sqrt b
    let p : Fin 4 → ℝ := ![a,δ,x 2*δ^3,x 3*δ^2]
    x 0*t+x 1*t^2+x 2*t^((3:ℝ)/2)+x 3*Real.sqrt t =
      (x 0*b+x 1*b^2+x 2*a^3+x 3*a)+
      δ*s*(x 0+2*b*x 1+(3*a/2)*x 2+x 3/(2*a))+
      (δ*s)^2*(x 1+(3/(8*a))*x 2)+bourgainOriginalRemainderPhase p s := by
  have hh := bourgainSource_mixed_phase_exact hb ht x
  dsimp only at hh ⊢
  rw [hh]
  simp only [add_sub_cancel_left,bourgainOriginalRemainderPhase,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Real.sq_sqrt hb.le]
  ring

end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainOriginalRemainderCutoff_derivative_integrable (p : Fin 4 → ℝ)
    (hp : p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32]) (j : ℕ) :
    Integrable (fun s : ℝ => ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖) := by
  have hc : HasCompactSupport (bourgainOriginalRemainderCutoff p) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainOriginalRemainderCutoff_support p)
  exact ((bourgainOriginalRemainderCutoff_smooth p (hp.1 0) ⟨hp.1 1,hp.2 1⟩).continuous_iteratedFDeriv
    (m:=j) (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))).norm.integrable_of_hasCompactSupport
      (hc.iteratedFDeriv j).norm

private theorem bourgainOriginalRemainderCutoff_derivative_integrals (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32],
      ∀ j ≤ Q, (∫ s : ℝ, ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖) ≤ C := by
  obtain ⟨C,hC,h⟩ := bourgainOriginalRemainderCutoff_derivative_bound Q
  refine ⟨4*C,by positivity,?_⟩
  intro p hp j hj
  have hz (s : ℝ) (hs : s ∉ Icc (-2:ℝ) 2) :
      ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖ = 0 := by
    have hd : iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s = 0 :=
      Function.notMem_support.mp (fun hh => hs
        (bourgainOriginalRemainderCutoff_support p ((support_iteratedFDeriv_subset j) hh)))
    rw [hd,norm_zero]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hmain := norm_setIntegral_le_of_norm_le_const
    (μ:=volume) (s:=Icc (-2:ℝ) 2)
    (f:=fun s : ℝ => ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖)
    (by simp)
    (fun s _ => by simpa only [norm_norm] using h p hp s j hj)
  have hnorm := le_abs_self
    (∫ s : ℝ in Icc (-2:ℝ) 2, ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖)
  have hmeasure : volume.real (Icc (-2:ℝ) 2) = 4 := by
    norm_num [Measure.real,Real.volume_Icc]
  rw [hmeasure] at hmain
  simpa only [mul_comm] using hnorm.trans hmain

private theorem bourgainOriginalRemainderCutoff_fourier_moment (p : Fin 4 → ℝ)
    (hp : p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32]) (ξ : ℝ) (m : ℕ) :
    |ξ|^m*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖ ≤
      (2:ℝ)^m*∑ j ∈ Finset.range (m+1),
        ∫ s : ℝ, ‖iteratedFDeriv ℝ j (bourgainOriginalRemainderCutoff p) s‖ := by
  have hI (k n : ℕ) (hk : (k:ℕ∞) ≤ 0) (_hn : (n:ℕ∞) ≤ ⊤) :
      Integrable (fun s : ℝ => ‖s‖^k*
        ‖iteratedFDeriv ℝ n (bourgainOriginalRemainderCutoff p) s‖) := by
    have hk0 : k=0 := by
      have hk' : k ≤ 0 := by exact_mod_cast hk
      omega
    subst k
    simpa using bourgainOriginalRemainderCutoff_derivative_integrable p hp n
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    (K:=0) (N:=(⊤:ℕ∞)) (bourgainOriginalRemainderCutoff_smooth p (hp.1 0) ⟨hp.1 1,hp.2 1⟩) hI
    (k:=0) (n:=m) (by simp) (by simp) ξ
  simpa [Finset.sum_product,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainOriginalRemainderCutoff_fourier_decay (Q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32],
      ∀ ξ : ℝ, (1+|ξ|)^Q*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖ ≤ C := by
  obtain ⟨D,hD,hjet⟩ := bourgainOriginalRemainderCutoff_derivative_integrals Q
  let E := (2:ℝ)^Q*((Q+1:ℕ):ℝ)*D
  refine ⟨(2:ℝ)^Q*(D+E),by dsimp [E]; positivity,?_⟩
  intro p hp ξ
  have hz : ‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖ ≤ D := by
    have h := bourgainOriginalRemainderCutoff_fourier_moment p hp ξ 0
    simpa using h.trans (by simpa using hjet p hp 0 (Nat.zero_le Q))
  have hp : |ξ|^Q*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖ ≤ E := by
    apply (bourgainOriginalRemainderCutoff_fourier_moment p hp ξ Q).trans
    calc
      _ ≤ (2:ℝ)^Q*∑ _j ∈ Finset.range (Q+1), D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum (fun j hj => hjet p hp j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = E := by simp [E,mul_assoc]
  have hscale : (1+|ξ|)^Q ≤ (2:ℝ)^Q*(1+|ξ|^Q) := by
    by_cases hξ : |ξ| ≤ 1
    · have h := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+|ξ|)
        (by linarith : 1+|ξ| ≤ 2) Q
      have hnonneg : 0 ≤ (2:ℝ)^Q*|ξ|^Q := by positivity
      nlinarith
    · have hξ' : 1 ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
      calc
        _ ≤ (2*|ξ|)^Q := pow_le_pow_left₀ (by positivity) (by linarith) Q
        _ = (2:ℝ)^Q*|ξ|^Q := mul_pow _ _ _
        _ ≤ _ := by nlinarith [show (0:ℝ)≤(2:ℝ)^Q by positivity]
  calc
    _ ≤ (2:ℝ)^Q*(1+|ξ|^Q)*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ = (2:ℝ)^Q*(‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖+
        |ξ|^Q*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hz hp) (by positivity)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem bourgainOriginalRemainderCutoff_uniform_fourierL1 :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32],
      Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖) ∧
      (∫ ξ : ℝ, (1+|ξ|)^100*‖𝓕 (bourgainOriginalRemainderCutoff p) ξ‖) ≤ C := by
  obtain ⟨C,hC,hdec⟩ := bourgainOriginalRemainderCutoff_fourier_decay 102
  refine ⟨C*Real.pi,by positivity,?_⟩
  intro p hp
  let f := bourgainOriginalRemainderCutoff p
  have hdom (ξ : ℝ) :
      (1+|ξ|)^100*‖𝓕 f ξ‖ ≤ C*(1+ξ^2)⁻¹ := by
    have hs : 1+ξ^2 ≤ (1+|ξ|)^2 := by
      nlinarith [sq_abs ξ,abs_nonneg ξ]
    have hp : (1+ξ^2)*((1+|ξ|)^100*‖𝓕 f ξ‖) ≤ C := by
      calc
        _ ≤ (1+|ξ|)^2*((1+|ξ|)^100*‖𝓕 f ξ‖) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _ = (1+|ξ|)^102*‖𝓕 f ξ‖ := by
          rw [show (102:ℕ)=2+100 by omega,pow_add]
          exact (mul_assoc _ _ _).symm
        _ ≤ C := hdec p hp ξ
    rw [←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    simpa only [mul_comm] using hp
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainOriginalRemainderCutoff_support p)
  have hi : Integrable f :=
    (bourgainOriginalRemainderCutoff_smooth p (hp.1 0) ⟨hp.1 1,hp.2 1⟩).continuous.integrable_of_hasCompactSupport hc
  have hhat : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hcont : Continuous (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 f ξ‖) :=
    ((continuous_const.add continuous_abs).pow 100).mul hhat.norm
  have hint : Integrable (fun ξ : ℝ => (1+|ξ|)^100*‖𝓕 f ξ‖) :=
    (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => by
        simpa only [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤
          (1+|ξ|)^100*‖𝓕 f ξ‖ by positivity)] using hdom ξ))
  refine ⟨hint,?_⟩
  have hmain := integral_mono hint (integrable_inv_one_add_sq.const_mul C) hdom
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hmain
  exact hmain

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ContDiff FourierTransform
namespace TaoTrudgianYang2025

/-- The actual mixed-order original-parameter remainder has a uniformly integrable Fourier
multiplier representation on the unit interval. No Fourier estimate is assumed. -/
private theorem exists_bourgainOriginalRemainder_multiplier_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32],
      ∃ K : ℝ → ℂ,
        Continuous K ∧ Integrable (fun ξ => (1+|ξ|)^100*‖K ξ‖) ∧
        (∫ ξ : ℝ, (1+|ξ|)^100*‖K ξ‖) ≤ C ∧
        (∀ ξ : ℝ, ‖K ξ‖ ≤ C/(1+|ξ|)^102) ∧
        ∀ s ∈ Icc (-1:ℝ) 1,
          fordAdditiveCharacter (bourgainOriginalRemainderPhase p s) =
            ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
  obtain ⟨C,hC,h⟩ := bourgainOriginalRemainderCutoff_uniform_fourierL1
  obtain ⟨D,hD,hdec⟩ := bourgainOriginalRemainderCutoff_fourier_decay 102
  refine ⟨max C D,hC.trans_le (le_max_left _ _),?_⟩
  intro p hp
  let f := bourgainOriginalRemainderCutoff p
  let K : ℝ → ℂ := 𝓕 f
  have hkernel := h p hp
  have hc : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (bourgainOriginalRemainderCutoff_support p)
  have hi : Integrable f :=
    (bourgainOriginalRemainderCutoff_smooth p (hp.1 0) ⟨hp.1 1,hp.2 1⟩).continuous.integrable_of_hasCompactSupport hc
  have hhat : Continuous K :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hKi : Integrable K :=
    hkernel.1.mono' hhat.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  refine ⟨K,hhat,hkernel.1,hkernel.2.trans (le_max_left _ _),?_,?_⟩
  · intro ξ
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using (hdec p hp ξ).trans (le_max_right C D)
  intro s hs
  have hcut : f s = fordAdditiveCharacter (bourgainOriginalRemainderPhase p s) := by
    dsimp only [f,bourgainOriginalRemainderCutoff]
    rw [modelPhaseBufferedCutoff_one (by norm_num)
      (by linarith [hs.1]) (by linarith [hs.2]),Complex.ofReal_one,one_mul]
  have hinv := congrFun
    ((bourgainOriginalRemainderCutoff_smooth p (hp.1 0) ⟨hp.1 1,hp.2 1⟩).continuous.fourierInv_fourier_eq hi hKi) s
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  calc
    _ = f s := hcut.symm
    _ = _ := hinv.symm
    _ = ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [smul_eq_mul,fordAdditiveCharacter]
      have he : (↑(-2*Real.pi*ξ*(-s)) : ℂ)*Complex.I =
          2*(Real.pi:ℂ)*Complex.I*↑(ξ*s) := by push_cast; ring
      rw [he]
      exact mul_comm _ _
end TaoTrudgianYang2025
noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainOriginalRemainder_finite_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32],
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i ∈ S, s i ∈ Icc (-1:ℝ) 1) →
        ‖∑ i ∈ S, z i*fordAdditiveCharacter (bourgainOriginalRemainderPhase p (s i))‖^6 ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)‖^6) := by
  obtain ⟨C,hC,hkern⟩ := exists_bourgainOriginalRemainder_multiplier_kernel
  refine ⟨C^6,by positivity,?_⟩
  intro p hp ι S z s hs
  obtain ⟨K,hKc,hKi,hmass,henv,hrep⟩ := hkern p hp
  have hK : Integrable K :=
    hKi.mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => by
      have hp : (1:ℝ) ≤ (1+|ξ|)^100 := one_le_pow₀ (by linarith [abs_nonneg ξ])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (K ξ))))
  have hterm (i : ι) :
      Integrable (fun ξ : ℝ => z i*(K ξ*fordAdditiveCharacter (ξ*s i))) := by
    have hc : Continuous (fun ξ : ℝ => fordAdditiveCharacter (ξ*s i)) := by
      unfold fordAdditiveCharacter
      fun_prop
    exact (hK.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => (sargos_character_norm (ξ*s i)).le))).const_mul _
  have he : (∑ i ∈ S, z i*fordAdditiveCharacter (bourgainOriginalRemainderPhase p (s i))) =
      ∫ ξ : ℝ, K ξ*(∑ i ∈ S, z i*fordAdditiveCharacter (ξ*s i)) := by
    calc
      _ = ∑ i ∈ S, z i*(∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i)) :=
        Finset.sum_congr rfl (fun i hi => congrArg (fun v => z i*v) (hrep (s i) (hs i hi)))
      _ = ∑ i ∈ S, ∫ ξ : ℝ, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) := by
        simp only [integral_const_mul]
      _ = ∫ ξ : ℝ, ∑ i ∈ S, z i*(K ξ*fordAdditiveCharacter (ξ*s i)) :=
        (integral_finsetSum S (fun i _ => hterm i)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with ξ
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  rw [he]
  exact bourgain_finite_multiplier_moment S z s hKc hKi hC hmass henv



end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainOriginalSource_quadratic_moment :
    ∃ C>(0:ℝ), ∀ (b δ : ℝ) (x : Fin 4 → ℝ),
      b∈Icc (1/4:ℝ) 1 → δ∈Icc (0:ℝ) (1/16) →
      |x 2*δ^3|≤32 → |x 3*δ^2|≤32 →
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ),
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        bourgainSourceSixMoment S z (fun i => b+δ*s i) x ≤
          C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
            ‖sargosPlanarSum S z s (fun i => (s i)^2)
              (δ*(x 0+2*b*x 1+(3*Real.sqrt b/2)*x 2+x 3/(2*Real.sqrt b))+ξ)
              (δ^2*(x 1+(3/(8*Real.sqrt b))*x 2))‖^6) := by
  obtain ⟨C,hC,hfinite⟩ := exists_bourgainOriginalRemainder_finite_moment.{u}
  refine ⟨C,hC,?_⟩
  intro b δ x hb hδ hx₂ hx₃ ι S z s hs
  have hb₀ : 0<b := by linarith [hb.1]
  let a := Real.sqrt b
  have ha₀ : (1/2:ℝ)≤a := Real.le_sqrt_of_sq_le (by nlinarith [hb.1])
  have ha₁ : a≤1 := Real.sqrt_le_one.mpr hb.2
  let p : Fin 4 → ℝ := ![a,δ,x 2*δ^3,x 3*δ^2]
  have hp : p∈Icc (![1/2,0,-32,-32] : Fin 4 → ℝ) ![1,1/16,32,32] := by
    constructor
    · intro j
      fin_cases j
      · exact ha₀
      · exact hδ.1
      · exact (abs_le.mp hx₂).1
      · exact (abs_le.mp hx₃).1
    · intro j
      fin_cases j
      · exact ha₁
      · exact hδ.2
      · exact (abs_le.mp hx₂).2
      · exact (abs_le.mp hx₃).2
  let A := x 0*b+x 1*b^2+x 2*a^3+x 3*a
  let L := δ*(x 0+2*b*x 1+(3*a/2)*x 2+x 3/(2*a))
  let Q := δ^2*(x 1+(3/(8*a))*x 2)
  let θ := fun i => A+L*s i+Q*(s i)^2
  let zθ := fun i => z i*fordAdditiveCharacter (θ i)
  have hphase (i : ι) (hi : i∈S) :
      x 0*(b+δ*s i)+x 1*(b+δ*s i)^2+
        x 2*(b+δ*s i)^((3:ℝ)/2)+x 3*Real.sqrt (b+δ*s i) =
          θ i+bourgainOriginalRemainderPhase p (s i) := by
    have hs' : (0:ℝ) ≤ (s i) + 1 := by linarith [(hs i hi).1]
    have ht : 0≤b+δ*s i := by
      nlinarith [mul_nonneg hδ.1 hs',hδ.2,hb.1]
    have hh := bourgainSource_scaled_mixed_phase hb₀ ht x
    dsimp only at hh
    calc
      _ = A+δ*s i*(x 0+2*b*x 1+(3*a/2)*x 2+x 3/(2*a))+
          (δ*s i)^2*(x 1+(3/(8*a))*x 2)+bourgainOriginalRemainderPhase p (s i) := hh
      _ = _ := by dsimp [θ,L,Q]; ring
  have hleft :
      (∑ i∈S, z i*fordAdditiveCharacter
        (x 0*(b+δ*s i)+x 1*(b+δ*s i)^2+
          x 2*(b+δ*s i)^((3:ℝ)/2)+x 3*Real.sqrt (b+δ*s i))) =
      ∑ i∈S, zθ i*fordAdditiveCharacter (bourgainOriginalRemainderPhase p (s i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hphase i hi,fordAdditiveCharacter_add]
    exact (mul_assoc _ _ _).symm
  have hmain := hfinite p hp S zθ s hs
  rw [←hleft] at hmain
  have hright (ξ : ℝ) :
      ‖∑ i∈S, zθ i*fordAdditiveCharacter (ξ*s i)‖^6 =
        ‖sargosPlanarSum S z s (fun i => (s i)^2) (L+ξ) Q‖^6 := by
    have he :
        (∑ i∈S, zθ i*fordAdditiveCharacter (ξ*s i)) =
          fordAdditiveCharacter A*sargosPlanarSum S z s (fun i => (s i)^2) (L+ξ) Q := by
      unfold sargosPlanarSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [zθ]
      rw [mul_assoc,←fordAdditiveCharacter_add]
      have he' : θ i+ξ*s i=A+(s i*(L+ξ)+(s i)^2*Q) := by dsimp [θ]; ring
      rw [he',fordAdditiveCharacter_add]
      ring
    rw [he,norm_mul,sargos_character_norm,one_mul]
  calc
    _ ≤ C*(∫ ξ : ℝ, ((1+|ξ|)^102)⁻¹*
        ‖∑ i∈S, zθ i*fordAdditiveCharacter (ξ*s i)‖^6) := hmain
    _ = _ := by
      apply congrArg (fun v : ℝ => C*v)
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hright]

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgain_integer_cell_linear_shift {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (s : ι → ℝ)
    {t c : ℝ} (ht : t≠0) (hs : ∀ i∈S, t*s i=(m i:ℝ)-c) (η θ : ℝ) :
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+η*s i+θ*(s i)^2)‖^6) =
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+θ*(s i)^2)‖^6) := by
  let F := fun u : ℝ =>
    ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+θ*(s i)^2)‖^6
  have hchar (k : ℤ) : fordAdditiveCharacter (k:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((k:ℝ):ℂ)=(k:ℂ)*(2*Real.pi*Complex.I) := by
      push_cast
      ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  have hp : Function.Periodic F 1 := by
    intro u
    dsimp [F]
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    have he : (m i:ℝ)*(u+1)+θ*(s i)^2=((m i:ℝ)*u+θ*(s i)^2)+(m i:ℝ) := by ring
    rw [he,fordAdditiveCharacter_add,hchar,mul_one]
  have hpoint (u : ℝ) :
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+η*s i+θ*(s i)^2)‖^6=F (u+η/t) := by
    have he :
        (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+η*s i+θ*(s i)^2)) =
          fordAdditiveCharacter (-η*c/t)*
            (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*(u+η/t)+θ*(s i)^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have heη : η*s i=(η/t)*((m i:ℝ)-c) := by
        rw [←hs i hi]
        field_simp
      have hephase : (m i:ℝ)*u+η*s i+θ*(s i)^2 =
          -η*c/t+((m i:ℝ)*(u+η/t)+θ*(s i)^2) := by
        rw [heη]
        ring
      rw [hephase,fordAdditiveCharacter_add]
      ring
    rw [he,norm_mul,sargos_character_norm,one_mul]
  simp only [hpoint]
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add,add_zero,add_comm] using hp.intervalIntegral_add_eq (η/t) 0

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
open scoped Matrix
namespace TaoTrudgianYang2025

private def bourgainOriginalQuadraticFrame (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1,3/(8*a);1,3/(8*b)]

private theorem bourgainOriginalQuadraticFrame_det {a b : ℝ}
    (ha : a≠0) (hb : b≠0) :
    (bourgainOriginalQuadraticFrame a b).det=3*(a-b)/(8*a*b) := by
  rw [Matrix.det_fin_two]
  change 1*(3/(8*b))-(3/(8*a))*1=3*(a-b)/(8*a*b)
  field_simp

private theorem bourgainOriginalQuadraticFrame_integral_bound {a b ν : ℝ}
    (ha : a∈Icc (1/2:ℝ) 1) (hb : b∈Icc (1/2:ℝ) 1)
    (hν : 0<ν) (hsep : ν≤|a-b|)
    (f : (Fin 2 → ℝ) → ℝ) (hf : StronglyMeasurable f) (hf₀ : ∀ x, 0≤f x) :
    (∫ x : Fin 2 → ℝ, f ((bourgainOriginalQuadraticFrame a b).mulVec x)) ≤
      (8/(3*ν))*(∫ y : Fin 2 → ℝ, f y) := by
  have ha₀ : 0<a := by linarith [ha.1]
  have hb₀ : 0<b := by linarith [hb.1]
  have hab : a*b≤1 := by nlinarith [hb.2,mul_nonneg (sub_nonneg.mpr ha.2) hb₀.le]
  have hnorm : (3*ν/8)≤|(bourgainOriginalQuadraticFrame a b).det| := by
    have he : |(bourgainOriginalQuadraticFrame a b).det|=3*|a-b|/(8*a*b) := by
      rw [bourgainOriginalQuadraticFrame_det ha₀.ne' hb₀.ne',abs_div,
        abs_mul (3:ℝ) (a-b),abs_of_pos (by norm_num : (0:ℝ)<3),
        abs_of_pos (by positivity : 0<8*a*b)]
    rw [he]
    calc
      3*ν/8 ≤ 3*|a-b|/8 := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (by nlinarith)
  have hdet : (bourgainOriginalQuadraticFrame a b).det≠0 :=
    abs_pos.mp ((by positivity : (0:ℝ)<3*ν/8).trans_le hnorm)
  have hi : |(bourgainOriginalQuadraticFrame a b).det⁻¹|≤8/(3*ν) := by
    rw [abs_inv]
    have hh := inv_anti₀ (by positivity : (0:ℝ)<3*ν/8) hnorm
    exact hh.trans_eq (by field_simp)
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hc : Continuous ((bourgainOriginalQuadraticFrame a b).mulVec) := by
    change Continuous (Matrix.toLin' (bourgainOriginalQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have hh := integral_map (μ:=volume) hc.aemeasurable hf.aestronglyMeasurable
  change Measure.map ((bourgainOriginalQuadraticFrame a b).mulVec) volume =
    ENNReal.ofReal |(bourgainOriginalQuadraticFrame a b).det⁻¹| • volume at hmap
  rw [hmap,integral_smul_measure,ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul] at hh
  exact hh.symm.le.trans (mul_le_mul_of_nonneg_right hi (integral_nonneg hf₀))

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainOriginalSource_periodic_quadratic_moment :
    ∃ C>(0:ℝ), ∀ (b δ T : ℝ) (x : Fin 3 → ℝ),
      b∈Icc (1/4:ℝ) 1 → δ∈Ioc (0:ℝ) (1/16) → 0<T →
      |x 1*δ^3|≤32 → |x 2*δ^2|≤32 →
      ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ) (s : ι → ℝ) (m : ι → ℤ),
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ i∈S, T*(b+δ*s i)=(m i:ℝ)) →
        (∫ u : ℝ in Icc (0:ℝ) 1,
          bourgainSourceSixMoment S z (fun i => b+δ*s i) ![T*u,x 0,x 1,x 2]) ≤
          C*(∫ u : ℝ in Icc (0:ℝ) 1,
            ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+
              (δ^2*(x 0+(3/(8*Real.sqrt b))*x 1))*(s i)^2)‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainOriginalSource_quadratic_moment.{u}
  refine ⟨C*Real.pi,mul_pos hC Real.pi_pos,?_⟩
  intro b δ T x hb hδ hT hx₁ hx₂ ι S z s m hs hm
  let I := Icc (0:ℝ) 1
  let P := fun u : ℝ =>
    bourgainSourceSixMoment S z (fun i => b+δ*s i) ![T*u,x 0,x 1,x 2]
  let η := δ*(2*b*x 0+(3*Real.sqrt b/2)*x 1+x 2/(2*Real.sqrt b))
  let θ := δ^2*(x 0+(3/(8*Real.sqrt b))*x 1)
  let F := fun (ξ u : ℝ) =>
    ‖sargosPlanarSum S z s (fun i => (s i)^2) (T*δ*u+η+ξ) θ‖^6
  let V := fun ξ : ℝ => ((1+|ξ|)^102)⁻¹
  let J := ∫ u : ℝ in I, ‖∑ i∈S, z i*
    fordAdditiveCharacter ((m i:ℝ)*u+θ*(s i)^2)‖^6
  have ht : T*δ≠0 := ne_of_gt (mul_pos hT hδ.1)
  have hcell (i : ι) (hi : i∈S) : T*δ*s i=(m i:ℝ)-T*b := by
    linarith [hm i hi]
  have hFc : Continuous (fun q : ℝ × ℝ => F q.1 q.2) := by
    unfold F sargosPlanarSum fordAdditiveCharacter
    fun_prop
  have hFb (ξ u : ℝ) : ‖F ξ u‖≤(∑ i∈S, ‖z i‖)^6 := by
    exact bourgain_character_six_bound S z
      (fun i => s i*(T*δ*u+η+ξ)+(s i)^2*θ)
  have hiV : Integrable V := bourgainRemainderEnvelope_integrable
  have hiF : Integrable (fun q : ℝ × ℝ => V q.1*F q.1 q.2)
      (volume.prod (volume.restrict I)) := by
    have hi1 : IntegrableOn (fun _u : ℝ => (1:ℝ)) I :=
      integrableOn_const isCompact_Icc.measure_ne_top
    have hh := (hiV.mul_prod hi1).mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hFb q.1 q.2))
    simpa only [mul_one] using hh
  have hPc : Continuous P := by
    unfold P bourgainSourceSixMoment fordAdditiveCharacter
    fun_prop
  have hpoint (u : ℝ) (_hu : u∈I) : P u≤C*(∫ ξ : ℝ, V ξ*F ξ u) := by
    have hh := hbound b δ (![T*u,x 0,x 1,x 2] : Fin 4 → ℝ)
      hb ⟨hδ.1.le,hδ.2⟩ hx₁ hx₂ S z s hs
    have he : δ*(T*u+2*b*x 0+(3*Real.sqrt b/2)*x 1+x 2/(2*Real.sqrt b)) =
        T*δ*u+η := by dsimp [η]; ring
    change P u≤C*(∫ ξ : ℝ, V ξ*
      ‖sargosPlanarSum S z s (fun i => (s i)^2)
        (δ*(T*u+2*b*x 0+(3*Real.sqrt b/2)*x 1+x 2/(2*Real.sqrt b))+ξ) θ‖^6) at hh
    simpa only [he,F] using hh
  have hmain := setIntegral_mono_on
    (hPc.continuousOn.integrableOn_compact isCompact_Icc)
    (hiF.integral_prod_right.const_mul C) measurableSet_Icc hpoint
  rw [integral_const_mul] at hmain
  have hswap := integral_integral_swap (μ:=volume) (ν:=volume.restrict I)
    (f:=fun ξ u => V ξ*F ξ u) hiF
  rw [←hswap] at hmain
  have heF (ξ u : ℝ) : F ξ u=
      ‖∑ i∈S, z i*fordAdditiveCharacter
        ((m i:ℝ)*u+(η+ξ)*s i+θ*(s i)^2)‖^6 := by
    have he :
        sargosPlanarSum S z s (fun i => (s i)^2) (T*δ*u+η+ξ) θ =
          fordAdditiveCharacter (-T*b*u)*
            (∑ i∈S, z i*fordAdditiveCharacter
              ((m i:ℝ)*u+(η+ξ)*s i+θ*(s i)^2)) := by
      unfold sargosPlanarSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have he' : s i*(T*δ*u+η+ξ)+(s i)^2*θ =
          -T*b*u+((m i:ℝ)*u+(η+ξ)*s i+θ*(s i)^2) := by
        linear_combination u*(hcell i hi)
      rw [he',fordAdditiveCharacter_add]
      ring
    dsimp only [F]
    rw [he,norm_mul,sargos_character_norm,one_mul]
  have hperiod (ξ : ℝ) : (∫ u : ℝ in I, F ξ u)=J := by
    simp only [heF]
    exact bourgain_integer_cell_linear_shift S z m s ht hcell (η+ξ) θ
  have hmass : (∫ ξ : ℝ, V ξ)≤Real.pi := by
    have hh := integral_mono hiV integrable_inv_one_add_sq (fun ξ => ?_)
    · simpa only [integral_univ_inv_one_add_sq] using hh
    · have hs' : 1+ξ^2≤(1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
      exact inv_anti₀ (by positivity) (hs'.trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg ξ]) (by omega : (2:ℕ)≤102)))
  have hJ : 0≤J := integral_nonneg (fun u => by positivity)
  calc
    _ ≤ C*(∫ ξ : ℝ, ∫ u : ℝ in I, V ξ*F ξ u) := hmain
    _ = C*(∫ ξ : ℝ, V ξ)*J := by
      simp only [integral_const_mul,hperiod,integral_mul_const]
      ring
    _ ≤ C*Real.pi*J := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass hC.le) hJ

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
open scoped Matrix
namespace TaoTrudgianYang2025

private theorem bourgainOriginalQuadraticFrame_apply (a b : ℝ) (x : Fin 2 → ℝ) :
    (bourgainOriginalQuadraticFrame a b).mulVec x =
      ![x 0+(3/(8*a))*x 1,x 0+(3/(8*b))*x 1] := by
  funext i
  fin_cases i <;>
    simp [bourgainOriginalQuadraticFrame,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

private theorem bourgainOriginalQuadraticFrame_box_product {a b ν R : ℝ}
    (ha : a∈Icc (1/2:ℝ) 1) (hb : b∈Icc (1/2:ℝ) 1)
    (hν : 0<ν) (hsep : ν≤|a-b|)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf₀ : ∀ y, 0≤f y) (hg₀ : ∀ y, 0≤g y) :
    (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
      f (x 0+(3/(8*a))*x 1)*g (x 0+(3/(8*b))*x 1)) ≤
      (8/(3*ν))*(∫ y : ℝ in Icc (-2*R) (2*R), f y)*
        (∫ y : ℝ in Icc (-2*R) (2*R), g y) := by
  let B := Icc (-2*R) (2*R)
  let C := Icc (fun _ : Fin 2 => -R) (fun _ => R)
  let F := (bourgainOriginalQuadraticFrame a b).mulVec
  let G := fun y : Fin 2 → ℝ => B.indicator f (y 0)*B.indicator g (y 1)
  have hB : MeasurableSet B := measurableSet_Icc
  have hi1 : Integrable (B.indicator f) :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator hB
  have hi2 : Integrable (B.indicator g) :=
    (hg.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator hB
  have hGm : StronglyMeasurable G := by
    apply Measurable.stronglyMeasurable
    exact ((hf.measurable.indicator hB).comp (by fun_prop)).mul
      ((hg.measurable.indicator hB).comp (by fun_prop))
  have hiG : Integrable G := by
    have hh := (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable
      (hi1.mul_prod hi2)
    exact hh
  have hFc : Continuous F := by
    change Continuous (Matrix.toLin' (bourgainOriginalQuadraticFrame a b))
    exact LinearMap.continuous_on_pi _
  have ha₀ : 0<a := by linarith [ha.1]
  have hb₀ : 0<b := by linarith [hb.1]
  have hdet : (bourgainOriginalQuadraticFrame a b).det≠0 := by
    rw [bourgainOriginalQuadraticFrame_det ha₀.ne' hb₀.ne']
    exact div_ne_zero (mul_ne_zero (by norm_num)
      (abs_pos.mp (hν.trans_le hsep))) (by positivity)
  have hiGF : Integrable (fun x : Fin 2 → ℝ => G (F x)) := by
    have hh : Integrable G (Measure.map F volume) := by
      have he := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
      change Measure.map F volume =
        ENNReal.ofReal |(bourgainOriginalQuadraticFrame a b).det⁻¹| • volume at he
      rw [he]
      exact hiG.smul_measure ENNReal.ofReal_ne_top
    exact hh.comp_measurable hFc.measurable
  have hG₀ (y : Fin 2 → ℝ) : 0≤G y :=
    mul_nonneg (Set.indicator_nonneg (fun q _ => hf₀ q) _)
      (Set.indicator_nonneg (fun q _ => hg₀ q) _)
  have hcoord (c : ℝ) (hc : c∈Icc (1/2:ℝ) 1)
      (x : Fin 2 → ℝ) (hx : x∈C) : x 0+(3/(8*c))*x 1∈B := by
    have hc₀ : 0<c := by linarith [hc.1]
    have hq₀ : 0≤3/(8*c) := by positivity
    have hq₁ : 3/(8*c)≤1 := (div_le_one (by positivity)).mpr (by linarith [hc.1])
    have hx₀ : |x 0|≤R := abs_le.mpr ⟨hx.1 0,hx.2 0⟩
    have hx₁ : |x 1|≤R := abs_le.mpr ⟨hx.1 1,hx.2 1⟩
    have hh : |x 0+(3/(8*c))*x 1|≤2*R := by
      calc
        _ ≤ |x 0|+|(3/(8*c))*x 1| := abs_add_le _ _
        _ = |x 0|+(3/(8*c))*|x 1| := by rw [abs_mul,abs_of_nonneg hq₀]
        _ ≤ R+1*R := add_le_add hx₀ (mul_le_mul hq₁ hx₁ (abs_nonneg _) (by norm_num))
        _ = 2*R := by ring
    exact ⟨by linarith [(abs_le.mp hh).1],(abs_le.mp hh).2⟩
  have he (x : Fin 2 → ℝ) (hx : x∈C) :
      f (x 0+(3/(8*a))*x 1)*g (x 0+(3/(8*b))*x 1)=G (F x) := by
    change _ = B.indicator f (F x 0)*B.indicator g (F x 1)
    dsimp only [F]
    rw [bourgainOriginalQuadraticFrame_apply]
    change _ = B.indicator f (x 0+(3/(8*a))*x 1)*
      B.indicator g (x 0+(3/(8*b))*x 1)
    rw [Set.indicator_of_mem (hcoord a ha x hx),Set.indicator_of_mem (hcoord b hb x hx)]
  have hprod : (∫ y : Fin 2 → ℝ, G y)=
      (∫ y : ℝ, B.indicator f y)*(∫ y : ℝ, B.indicator g y) := by
    have hh := (volume_preserving_finTwoArrow ℝ).integral_comp
      MeasurableEquiv.finTwoArrow.measurableEmbedding
      (fun p : ℝ × ℝ => B.indicator f p.1*B.indicator g p.2)
    exact hh.trans (integral_prod_mul _ _)
  calc
    _ = ∫ x : Fin 2 → ℝ in C, G (F x) :=
      setIntegral_congr_fun measurableSet_Icc he
    _ ≤ ∫ x : Fin 2 → ℝ, G (F x) :=
      setIntegral_le_integral hiGF (Filter.Eventually.of_forall (fun x => hG₀ (F x)))
    _ ≤ (8/(3*ν))*(∫ y : Fin 2 → ℝ, G y) :=
      bourgainOriginalQuadraticFrame_integral_bound ha hb hν hsep G hGm hG₀
    _ = _ := by rw [hprod,integral_indicator hB,integral_indicator hB]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainOriginalSource_periodic_box_factorization :
    ∃ C>(0:ℝ), ∀ (b d δ T R q ν : ℝ),
      b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
      δ∈Ioc (0:ℝ) (1/16) → 0<T →
      R*δ^3≤32 → |q*δ^2|≤32 → 0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
      ∀ {ι κ : Type u} (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (s : ι → ℝ) (v : κ → ℝ)
        (m : ι → ℤ) (n : κ → ℤ),
        (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
        (∀ j∈V, v j∈Icc (-1:ℝ) 1) →
        (∀ i∈S, T*(b+δ*s i)=(m i:ℝ)) →
        (∀ j∈V, T*(d+δ*v j)=(n j:ℝ)) →
        (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
          (∫ u : ℝ in Icc (0:ℝ) 1,
            bourgainSourceSixMoment S z (fun i => b+δ*s i) ![T*u,x 0,x 1,q])*
          (∫ u : ℝ in Icc (0:ℝ) 1,
            bourgainSourceSixMoment V c (fun j => d+δ*v j) ![T*u,x 0,x 1,q])) ≤
          (C/ν)*
            (∫ y : ℝ in Icc (-2*R) (2*R), ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+δ^2*y*(s i)^2)‖^6)*
            (∫ y : ℝ in Icc (-2*R) (2*R), ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ j∈V, c j*fordAdditiveCharacter ((n j:ℝ)*u+δ^2*y*(v j)^2)‖^6) := by
  obtain ⟨E,hE,hperiod⟩ := exists_bourgainOriginalSource_periodic_quadratic_moment.{u}
  refine ⟨E^2*8/3,by positivity,?_⟩
  intro b d δ T R q ν hb hd hδ hT hR hq hν hsep ι κ S V z c s v m n hs hv hm hn
  let B := Icc (fun _ : Fin 2 => -R) (fun _ => R)
  let I := Icc (0:ℝ) 1
  let f := fun y : ℝ => ∫ u : ℝ in I,
    ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+δ^2*y*(s i)^2)‖^6
  let g := fun y : ℝ => ∫ u : ℝ in I,
    ‖∑ j∈V, c j*fordAdditiveCharacter ((n j:ℝ)*u+δ^2*y*(v j)^2)‖^6
  let P := fun x : Fin 2 → ℝ => ∫ u : ℝ in I,
    bourgainSourceSixMoment S z (fun i => b+δ*s i) ![T*u,x 0,x 1,q]
  let Q := fun x : Fin 2 → ℝ => ∫ u : ℝ in I,
    bourgainSourceSixMoment V c (fun j => d+δ*v j) ![T*u,x 0,x 1,q]
  have hcontinuous {X : Type} [TopologicalSpace X] (F : X → ℝ → ℝ)
      (hF : Continuous F.uncurry) :
      Continuous (fun x => ∫ u : ℝ in I, F x u) := by
    have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=volume) hF 0 1
    simpa only [I,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hh
  have hf : Continuous f := by
    dsimp only [f]
    apply hcontinuous
    unfold Function.uncurry fordAdditiveCharacter
    fun_prop
  have hg : Continuous g := by
    dsimp only [g]
    apply hcontinuous
    unfold Function.uncurry fordAdditiveCharacter
    fun_prop
  have hP : Continuous P := by
    dsimp only [P]
    apply hcontinuous
    unfold Function.uncurry bourgainSourceSixMoment fordAdditiveCharacter
    fun_prop
  have hQ : Continuous Q := by
    dsimp only [Q]
    apply hcontinuous
    unfold Function.uncurry bourgainSourceSixMoment fordAdditiveCharacter
    fun_prop
  have hf₀ (y : ℝ) : 0≤f y := integral_nonneg (fun u => by positivity)
  have hg₀ (y : ℝ) : 0≤g y := integral_nonneg (fun u => by positivity)
  have hQ₀ (x : Fin 2 → ℝ) : 0≤Q x := integral_nonneg (fun u =>
    bourgainSourceSixMoment_nonneg V c _ _)
  let a := Real.sqrt b
  let e := Real.sqrt d
  have ha : a∈Icc (1/2:ℝ) 1 :=
    ⟨Real.le_sqrt_of_sq_le (by nlinarith [hb.1]),Real.sqrt_le_one.mpr hb.2⟩
  have he : e∈Icc (1/2:ℝ) 1 :=
    ⟨Real.le_sqrt_of_sq_le (by nlinarith [hd.1]),Real.sqrt_le_one.mpr hd.2⟩
  let F := fun x : Fin 2 → ℝ => f (x 0+(3/(8*a))*x 1)*g (x 0+(3/(8*e))*x 1)
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hpoint (x : Fin 2 → ℝ) (hx : x∈B) : P x*Q x≤E^2*F x := by
    have hx₁ : |x 1*δ^3|≤32 := by
      rw [abs_mul,abs_of_nonneg (pow_nonneg hδ.1.le 3)]
      exact (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hx.1 1,hx.2 1⟩)
        (pow_nonneg hδ.1.le 3)).trans hR
    have h₁ := hperiod b δ T (![x 0,x 1,q] : Fin 3 → ℝ)
      hb hδ hT hx₁ hq S z s m hs hm
    have h₂ := hperiod d δ T (![x 0,x 1,q] : Fin 3 → ℝ)
      hd hδ hT hx₁ hq V c v n hv hn
    change P x≤E*f (x 0+(3/(8*a))*x 1) at h₁
    change Q x≤E*g (x 0+(3/(8*e))*x 1) at h₂
    exact (mul_le_mul h₁ h₂ (hQ₀ x) (mul_nonneg hE.le (hf₀ _))).trans_eq (by dsimp [F]; ring)
  have hmain := setIntegral_mono_on (μ:=volume)
    ((hP.mul hQ).continuousOn.integrableOn_compact isCompact_Icc)
    ((continuous_const.mul hF).continuousOn.integrableOn_compact isCompact_Icc)
    measurableSet_Icc hpoint
  simp only [Pi.mul_apply] at hmain
  rw [integral_const_mul] at hmain
  have hframe := bourgainOriginalQuadraticFrame_box_product (R:=R) ha he hν hsep f g hf hg hf₀ hg₀
  calc
    _ ≤ E^2*(∫ x : Fin 2 → ℝ in B, F x) := hmain
    _ ≤ E^2*((8/(3*ν))*(∫ y : ℝ in Icc (-2*R) (2*R), f y)*
        (∫ y : ℝ in Icc (-2*R) (2*R), g y)) :=
      mul_le_mul_of_nonneg_left hframe (sq_nonneg E)
    _ = _ := by dsimp [f,g,I]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped ContDiff FourierTransform
namespace TaoTrudgianYang2025

private theorem exists_bourgainQuadratic_sargos_kernel :
    ∃ C>(0:ℝ), ∀ β : ℝ, ∃ K : ℝ → ℂ,
      Continuous K ∧ Integrable K ∧
      (∫ ξ : ℝ, ‖K ξ‖)≤C*(1+|β|)^2 ∧
      ∀ t∈Icc (5/4:ℝ) (7/4),
        fordAdditiveCharacter (β*t^2)=
          ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*t) := by
  obtain ⟨D,hD,hjets⟩ := sargosQuarticBufferedKernel_uniform_second_derivative
  refine ⟨512*D*Real.pi,by positivity,?_⟩
  intro β
  let χ := modelPhaseBufferedCutoff 1 2 (1/8)
  let f := sargosQuarticWeightedKernel χ 1 β (β*0)
  let K : ℝ → ℂ := 𝓕 f
  have hχ : ContDiff ℝ ∞ χ := modelPhaseBufferedCutoff_contDiff 1 2 (1/8)
  have hs : tsupport χ⊆Ioo (1:ℝ) 2 :=
    modelPhaseBufferedCutoff_tsupport_model (by norm_num) le_rfl le_rfl
  have hf : ContDiff ℝ ∞ f := sargosQuarticWeightedKernel_contDiff hχ 1 β (β*0)
  have hc : HasCompactSupport f := sargosQuarticWeightedKernel_hasCompactSupport hs (by norm_num) β (β*0)
  have hi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hKc : Continuous K := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hi
  have hsupport : Function.support f⊆Icc (1:ℝ) 2 := by
    intro t ht
    by_contra hn
    exact ht (sargosQuarticWeightedKernel_zero_of_not_mem hs (by norm_num)
      (by simpa only [mul_one] using hn) β (β*0))
  have h₀ (t : ℝ) : ‖iteratedDeriv 0 f t‖≤1 :=
    sargosQuarticBufferedKernel_norm_le_one 1 2 (1/8) 1 β (β*0) t
  have h₂ := hjets 1 2 (1/8) le_rfl le_rfl (by norm_num) (by norm_num) 0 β (by norm_num)
  have hdec (ξ : ℝ) : (1+|ξ|)^2*‖K ξ‖≤512*D*(1+|β|)^2 := by
    have hh := RiemannZeta.GuthMaynard.one_add_abs_fourier_decay_of_support_of_bounds_order
      2 hf (by norm_num : (1:ℝ)≤2) hsupport (by norm_num)
      (by positivity : 0≤D*((1/8:ℝ)⁻¹)^2*(1+|β|)^2) h₀ h₂ ξ
    have hβ : 1≤(1+|β|)^2 := one_le_pow₀ (by linarith [abs_nonneg β])
    have hhD : 1≤D*(1+|β|)^2 := one_le_mul_of_one_le_of_one_le hD hβ
    norm_num only [one_div,inv_inv,show (8:ℝ)^2=64 by norm_num,
      show (2:ℝ)^2=4 by norm_num,show (2:ℝ)-1=1 by norm_num,mul_one] at hh
    change (1+|ξ|)^2*‖K ξ‖≤4*(1+D*64*(1+|β|)^2) at hh
    nlinarith
  have henv (ξ : ℝ) : ‖K ξ‖≤(512*D*(1+|β|)^2)*(1+ξ^2)⁻¹ := by
    have hs' : 1+ξ^2≤(1+|ξ|)^2 := by nlinarith [sq_abs ξ,abs_nonneg ξ]
    have hh := (mul_le_mul_of_nonneg_right hs' (norm_nonneg (K ξ))).trans (hdec ξ)
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hh)
  have hKi : Integrable K := (integrable_inv_one_add_sq.const_mul
    (512*D*(1+|β|)^2)).mono' hKc.aestronglyMeasurable (Filter.Eventually.of_forall henv)
  have hmass := integral_mono hKi.norm
    (integrable_inv_one_add_sq.const_mul (512*D*(1+|β|)^2)) henv
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hmass
  refine ⟨K,hKc,hKi,hmass.trans_eq (by ring),?_⟩
  intro t ht
  have hcut : f t=fordAdditiveCharacter (β*t^2) := by
    dsimp only [f,sargosQuarticWeightedKernel,χ,sargosQuarticPhase]
    rw [div_one,modelPhaseBufferedCutoff_one (by norm_num)
      (by linarith [ht.1]) (by linarith [ht.2])]
    simp only [Complex.ofReal_one,one_mul,mul_zero,zero_mul,add_zero,
      sargos_ford_character_eq_fourier]
  have hinv := congrFun (hf.continuous.fourierInv_fourier_eq hi hKi) t
  rw [Real.fourierInv_eq_fourier_neg,Real.fourier_real_eq_integral_exp_smul] at hinv
  calc
    _ = f t := hcut.symm
    _ = _ := hinv.symm
    _ = ∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*t) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [smul_eq_mul,fordAdditiveCharacter]
      have he : (↑(-2*Real.pi*ξ*(-t)) : ℂ)*Complex.I =
          2*(Real.pi:ℂ)*Complex.I*↑(ξ*t) := by push_cast; ring
      rw [he]
      exact mul_comm _ _

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

set_option maxHeartbeats 400000 in
private theorem bourgain_integer_cell_kernel_moment {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (s : ι → ℝ)
    {t c : ℝ} (ht : t≠0) (hs : ∀ i∈S, t*s i=(m i:ℝ)-c)
    (K : ℝ → ℂ) (hKi : Integrable K) :
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, (z i*fordAdditiveCharacter ((m i:ℝ)*u))*
        (∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i))‖^6) ≤
      (∫ ξ : ℝ, ‖K ξ‖)^6*
        (∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6) := by
  let I := Icc (0:ℝ) 1
  let M := ∑ i∈S, ‖z i‖
  let A := ∫ ξ : ℝ, ‖K ξ‖
  let F := fun (ξ u : ℝ) => ∑ i∈S,
    z i*fordAdditiveCharacter ((m i:ℝ)*u+ξ*s i)
  let P := fun u : ℝ => ‖∑ i∈S, (z i*fordAdditiveCharacter ((m i:ℝ)*u))*
    (∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i))‖^6
  let J := ∫ u : ℝ in I, ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6
  have hFc : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
    unfold F fordAdditiveCharacter
    fun_prop
  have hFb (ξ u : ℝ) : ‖F ξ u‖≤M := by
    calc
      _ ≤ ∑ i∈S, ‖z i*fordAdditiveCharacter ((m i:ℝ)*u+ξ*s i)‖ := norm_sum_le _ _
      _ = M := by simp only [M,norm_mul,sargos_character_norm,mul_one]
  have hPc : Continuous P := by
    unfold P fordAdditiveCharacter
    fun_prop
  have hiF : Integrable (fun p : ℝ × ℝ => ‖K p.1‖*‖F p.1 p.2‖^6)
      (volume.prod (volume.restrict I)) := by
    have hi1 : IntegrableOn (fun _u : ℝ => (1:ℝ)) I :=
      integrableOn_const isCompact_Icc.measure_ne_top
    have hh := (hKi.norm.mul_prod hi1).mul_bdd (hFc.norm.pow 6).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hFb p.1 p.2) 6))
    simpa only [mul_one] using hh
  have hpoint (u : ℝ) (_hu : u∈I) :
      P u≤A^5*(∫ ξ : ℝ, ‖K ξ‖*‖F ξ u‖^6) := by
    have hFu : Continuous (fun ξ : ℝ => F ξ u) := by
      unfold F fordAdditiveCharacter
      fun_prop
    have hiJ (j : ℕ) : Integrable (fun ξ => ‖K ξ‖*‖F ξ u‖^j) :=
      hKi.norm.mul_bdd (hFu.norm.pow j).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ξ => by
          rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hFb ξ u) j))
    have he : (∑ i∈S, (z i*fordAdditiveCharacter ((m i:ℝ)*u))*
        (∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*s i))) =
        ∫ ξ : ℝ, K ξ*F ξ u := by
      have hterm (i : ι) :
          Integrable (fun ξ : ℝ => (z i*fordAdditiveCharacter ((m i:ℝ)*u))*
            (K ξ*fordAdditiveCharacter (ξ*s i))) := by
        apply Integrable.const_mul
        exact hKi.mul_bdd (by unfold fordAdditiveCharacter; fun_prop)
          (Filter.Eventually.of_forall (fun ξ => (sargos_character_norm (ξ*s i)).le))
      simp_rw [←integral_const_mul]
      rw [←integral_finsetSum S (fun i hi => hterm i)]
      apply integral_congr_ae
      filter_upwards with ξ
      dsimp only [F]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [fordAdditiveCharacter_add]
      ring
    have hp := weighted_integral_sixth_power (W:=fun ξ => ‖K ξ‖)
      (f:=fun ξ => ‖F ξ u‖) (fun _ => norm_nonneg _) (fun j _ => hiJ j)
    calc
      P u = ‖∫ ξ : ℝ, K ξ*F ξ u‖^6 := by dsimp [P]; rw [he]
      _ ≤ (∫ ξ : ℝ, ‖K ξ‖*‖F ξ u‖)^6 := by
        apply pow_le_pow_left₀ (norm_nonneg _) _ 6
        simpa only [norm_mul] using norm_integral_le_integral_norm (fun ξ => K ξ*F ξ u)
      _ ≤ _ := hp
  have hm := setIntegral_mono_on (μ:=volume)
    (hPc.continuousOn.integrableOn_compact isCompact_Icc)
    (hiF.integral_prod_right.const_mul (A^5)) measurableSet_Icc hpoint
  rw [integral_const_mul] at hm
  have hswap := integral_integral_swap (μ:=volume) (ν:=volume.restrict I)
    (f:=fun ξ u => ‖K ξ‖*‖F ξ u‖^6) hiF
  rw [←hswap] at hm
  have hperiod (ξ : ℝ) : (∫ u : ℝ in I, ‖F ξ u‖^6)=J := by
    have hh := bourgain_integer_cell_linear_shift S z m s ht hs ξ 0
    simpa only [zero_mul,add_zero,F,J,I] using hh
  calc
    _ ≤ A^5*(∫ ξ : ℝ, ∫ u : ℝ in I, ‖K ξ‖*‖F ξ u‖^6) := hm
    _ = A^6*J := by
      simp only [integral_const_mul,hperiod,integral_mul_const]
      dsimp [A]
      ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgain_integer_cell_quadratic_moment :
    ∃ C>(0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ)
      (m : ι → ℤ) (s : ι → ℝ) (t c β : ℝ),
      t≠0 → (∀ i∈S, t*s i=(m i:ℝ)-c) →
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+β*(s i)^2)‖^6) ≤
        C*(1+|β|)^12*(∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6) := by
  obtain ⟨D,hD,hkern⟩ := exists_bourgainQuadratic_sargos_kernel
  refine ⟨(D*16^2)^6,by positivity,?_⟩
  intro ι S z m s t c β ht hs hsI
  let r := fun i => (3/2:ℝ)+s i/4
  let z' := fun i => z i*fordAdditiveCharacter (-48*β*r i+36*β)
  have hr (i : ι) (hi : i∈S) : r i∈Icc (5/4:ℝ) (7/4) := by
    dsimp [r]
    constructor <;> linarith [(hsI i hi).1,(hsI i hi).2]
  have hrt : 4*t≠0 := mul_ne_zero (by norm_num) ht
  have hrc (i : ι) (hi : i∈S) : (4*t)*r i=(m i:ℝ)-(c-6*t) := by
    dsimp [r]
    linear_combination hs i hi
  obtain ⟨K,_hKc,hKi,hmass,hrep⟩ := hkern (16*β)
  have hkernel := bourgain_integer_cell_kernel_moment S z' m r hrt hrc K hKi
  have hleft (u : ℝ) :
      (∑ i∈S, (z' i*fordAdditiveCharacter ((m i:ℝ)*u))*
        (∫ ξ : ℝ, K ξ*fordAdditiveCharacter (ξ*r i))) =
      ∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+β*(s i)^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [←hrep (r i) (hr i hi)]
    dsimp only [z']
    rw [mul_assoc,mul_assoc,←fordAdditiveCharacter_add,←fordAdditiveCharacter_add]
    congr 2
    dsimp [r]
    ring
  have hright (u : ℝ) :
      ‖∑ i∈S, z' i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6 =
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(-48*β)*r i)‖^6 := by
    have he : (∑ i∈S, z' i*fordAdditiveCharacter ((m i:ℝ)*u)) =
        fordAdditiveCharacter (36*β)*
          (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+(-48*β)*r i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [z']
      rw [mul_assoc,←fordAdditiveCharacter_add]
      have he' : -48*β*r i+36*β+(m i:ℝ)*u =
          36*β+((m i:ℝ)*u+(-48*β)*r i) := by ring
      rw [he',fordAdditiveCharacter_add]
      ring
    rw [he,norm_mul,sargos_character_norm,one_mul]
  simp only [hleft,hright] at hkernel
  have heJ := bourgain_integer_cell_linear_shift S z m r hrt hrc (-48*β) 0
  simp only [zero_mul,add_zero] at heJ
  rw [heJ] at hkernel
  have hβ : 1+|16*β|≤16*(1+|β|) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16)]
    linarith
  have hmass' : (∫ ξ : ℝ, ‖K ξ‖)≤D*16^2*(1+|β|)^2 := by
    exact hmass.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hβ 2) hD.le).trans_eq (by ring))
  have hpow := pow_le_pow_left₀ (integral_nonneg (fun ξ => norm_nonneg (K ξ))) hmass' 6
  have hJ : 0≤∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6 :=
    integral_nonneg (fun u => by positivity)
  calc
    _ ≤ (∫ ξ : ℝ, ‖K ξ‖)^6*
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6) := hkernel
    _ ≤ (D*16^2*(1+|β|)^2)^6*
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6) :=
      mul_le_mul_of_nonneg_right hpow hJ
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_parabola_weight_product (K α γ : ℝ) :
    parabolaSourceWeight K 0 0 α γ ≤
      (1+(α/K)^2)⁻¹*((1+|γ/K|)^14)⁻¹ := by
  let r := ‖((α/K:ℝ):ℂ)+(γ/K:ℝ)*Complex.I‖
  have ha : |α/K|≤r := by
    have hh := Complex.abs_re_le_norm (((α/K:ℝ):ℂ)+(γ/K:ℝ)*Complex.I)
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero] using hh
  have hg : |γ/K|≤r := by
    have hh := Complex.abs_im_le_norm (((α/K:ℝ):ℂ)+(γ/K:ℝ)*Complex.I)
    simpa only [Complex.add_im,Complex.ofReal_re,Complex.mul_im,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero] using hh
  have hr : 0≤r := norm_nonneg _
  have ha₂ : 1+(α/K)^2≤(1+r)^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (α/K)) ha 2
    rw [sq_abs] at hh
    nlinarith
  have hg₁ : 1+|γ/K|≤1+r := by linarith
  have hden : (1+(α/K)^2)*(1+|γ/K|)^14≤(1+r)^100 := by
    calc
      _ ≤ (1+r)^2*(1+r)^14 :=
        mul_le_mul ha₂ (pow_le_pow_left₀ (by positivity) hg₁ 14) (by positivity) (by positivity)
      _ = (1+r)^16 := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega : (16:ℕ)≤100)
  have hh := inv_anti₀ (by positivity : (0:ℝ)<(1+(α/K)^2)*(1+|γ/K|)^14) hden
  simpa only [parabolaSourceWeight,sub_zero,one_div,mul_inv_rev,r,mul_comm] using hh

private theorem bourgain_quadratic_tail_absorption {K h : ℝ}
    (hK : 0<K) (hh : K*h^2≤1) (γ : ℝ) :
    ((1+|γ/K|)^14)⁻¹*(1+|γ*h^2|)^12 ≤ (1+(γ/K)^2)⁻¹ := by
  have hh' : h^2≤1/K := (le_div_iff₀ hK).mpr (by simpa only [mul_comm] using hh)
  have habs : |γ*h^2|≤|γ/K| := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg h),abs_div,abs_of_pos hK]
    simpa only [div_eq_mul_inv,mul_assoc,one_mul] using
      mul_le_mul_of_nonneg_left hh' (abs_nonneg γ)
  have he : ((1+|γ/K|)^14)⁻¹*(1+|γ/K|)^12=((1+|γ/K|)^2)⁻¹ := by
    have hp : 1+|γ/K|≠0 := ne_of_gt (by positivity)
    field_simp
  calc
    _ ≤ ((1+|γ/K|)^14)⁻¹*(1+|γ/K|)^12 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (by linarith : 1+|γ*h^2|≤1+|γ/K|) 12) (by positivity)
    _ = ((1+|γ/K|)^2)⁻¹ := he
    _ ≤ _ := inv_anti₀ (by positivity)
      (by nlinarith [sq_abs (γ/K),abs_nonneg (γ/K)])

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem bourgain_integer_parabola_average {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (w : ι → ℝ)
    {T K c : ℝ} (hT : 0<T) (hTK : T≤K)
    (hw : ∀ i∈S, T*w i=(m i:ℝ)-c) (γ : ℝ) :
    (∫ α : ℝ, (1+(α/K)^2)⁻¹*
      ‖sargosPlanarSum S z w (fun i => (w i)^2) α γ‖^6) ≤
      3*Real.pi*K*(∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+γ*(w i)^2)‖^6) := by
  have he (α : ℝ) :
      ‖sargosPlanarSum S z w (fun i => (w i)^2) α γ‖^6 =
      ‖∑ i∈S, z i*fordAdditiveCharacter (α*((m i:ℝ)/T)+γ*(w i)^2)‖^6 := by
    have hh : sargosPlanarSum S z w (fun i => (w i)^2) α γ =
        fordAdditiveCharacter (-c*α/T)*
          (∑ i∈S, z i*fordAdditiveCharacter (α*((m i:ℝ)/T)+γ*(w i)^2)) := by
      unfold sargosPlanarSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hp : w i*α+(w i)^2*γ =
          -c*α/T+(α*((m i:ℝ)/T)+γ*(w i)^2) := by
        apply (mul_right_cancel₀ hT.ne')
        field_simp
        linear_combination α*(hw i hi)
      rw [hp,fordAdditiveCharacter_add]
      ring
    rw [hh,norm_mul,sargos_character_norm,one_mul]
  simp only [he]
  have hh := bourgain_integer_phase_periodic_average S z m
    (fun i => γ*(w i)^2) hT hTK
  simpa only [mul_comm] using hh

private theorem exists_bourgain_integer_parabola_period :
    ∃ C>(0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ)
      (m : ι → ℤ) (s : ι → ℝ) (T a h c γ : ℝ),
      0<T → h≠0 → (∀ i∈S, T*(a+h*s i)=(m i:ℝ)-c) →
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+γ*(a+h*s i)^2)‖^6) ≤
        C*(1+|γ*h^2|)^12*(∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgain_integer_cell_quadratic_moment.{u}
  refine ⟨C,hC,?_⟩
  intro ι S z m s T a h c γ hT hh hm hs
  have ht : T*h≠0 := mul_ne_zero hT.ne' hh
  have hc (i : ι) (hi : i∈S) : (T*h)*s i=(m i:ℝ)-(c+T*a) := by
    linear_combination hm i hi
  have he (u : ℝ) :
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+γ*(a+h*s i)^2)‖^6 =
      ‖∑ i∈S, z i*fordAdditiveCharacter
        ((m i:ℝ)*u+(2*γ*a*h)*s i+(γ*h^2)*(s i)^2)‖^6 := by
    have he' : (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+γ*(a+h*s i)^2)) =
        fordAdditiveCharacter (γ*a^2)*
          (∑ i∈S, z i*fordAdditiveCharacter
            ((m i:ℝ)*u+(2*γ*a*h)*s i+(γ*h^2)*(s i)^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hp : (m i:ℝ)*u+γ*(a+h*s i)^2 =
          γ*a^2+((m i:ℝ)*u+(2*γ*a*h)*s i+(γ*h^2)*(s i)^2) := by ring
      rw [hp,fordAdditiveCharacter_add]
      ring
    rw [he',norm_mul,sargos_character_norm,one_mul]
  simp only [he]
  rw [bourgain_integer_cell_linear_shift S z m s ht hc (2*γ*a*h) (γ*h^2)]
  exact hbound S z m s (T*h) (c+T*a) (γ*h^2) ht hc hs

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgain_integer_parabola_weighted_cell :
    ∃ C>(0:ℝ), ∀ {ι : Type u} (S : Finset ι) (z : ι → ℂ)
      (m : ι → ℤ) (s : ι → ℝ) (T K a h c : ℝ),
      0<T → T≤K → h≠0 → K*h^2≤1 →
      (∀ i∈S, T*(a+h*s i)=(m i:ℝ)-c) →
      (∀ i∈S, s i∈Icc (-1:ℝ) 1) →
      (∫ p : ℝ × ℝ, parabolaSourceWeight K 0 0 p.1 p.2*
        ‖sargosPlanarSum S z (fun i => a+h*s i)
          (fun i => (a+h*s i)^2) p.1 p.2‖^6) ≤
        C*K^2*(∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6) := by
  obtain ⟨D,hD,hperiod⟩ := exists_bourgain_integer_parabola_period.{u}
  refine ⟨3*Real.pi^2*D,by positivity,?_⟩
  intro ι S z m s T K a h c hT hTK hh hscale hm hs
  have hK : 0<K := hT.trans_le hTK
  let w := fun i => a+h*s i
  let F := fun p : ℝ × ℝ => ‖sargosPlanarSum S z w (fun i => (w i)^2) p.1 p.2‖^6
  let L := fun x : ℝ => (1+(x/K)^2)⁻¹
  let B := fun x : ℝ => ((1+|x/K|)^14)⁻¹
  let J := ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6
  have hJ : 0≤J := integral_nonneg (fun u => by positivity)
  have hFc : Continuous F := by unfold F sargosPlanarSum fordAdditiveCharacter; fun_prop
  have hF₀ (p : ℝ × ℝ) : 0≤F p := by dsimp [F]; positivity
  have hFb (p : ℝ × ℝ) : ‖F p‖≤(∑ i∈S, ‖z i‖)^6 :=
    bourgain_character_six_bound S z (fun i => w i*p.1+(w i)^2*p.2)
  have hiL : Integrable L := integrable_inv_one_add_sq.comp_div hK.ne'
  have hBc : Continuous B := by
    apply Continuous.inv₀
    · dsimp [B]; fun_prop
    · intro x
      positivity
  have hBL (x : ℝ) : B x≤L x := by
    apply inv_anti₀ (by positivity)
    have hh' : 1+(x/K)^2≤(1+|x/K|)^2 := by nlinarith [sq_abs (x/K),abs_nonneg (x/K)]
    exact hh'.trans (pow_le_pow_right₀ (by linarith [abs_nonneg (x/K)])
      (by omega : (2:ℕ)≤14))
  have hiB : Integrable B := hiL.mono' hBc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [B]; positivity)]
      exact hBL x))
  have hiWF : Integrable (fun p : ℝ × ℝ => parabolaSourceWeight K 0 0 p.1 p.2*F p) :=
    (integrable_parabolaSourceWeight hK 0 0).mul_bdd hFc.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb)
  have hiV : Integrable (fun p : ℝ × ℝ => L p.1*B p.2*F p) :=
    (hiL.mul_prod hiB).mul_bdd hFc.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
  have hmajor := integral_mono hiWF hiV (fun p =>
    mul_le_mul_of_nonneg_right (bourgain_parabola_weight_product K p.1 p.2) (hF₀ p))
  have hpoint (γ : ℝ) :
      (∫ α : ℝ, L α*B γ*F (α,γ))≤
        (3*Real.pi*K*D)*L γ*J := by
    have havg := bourgain_integer_parabola_average S z m w hT hTK hm γ
    have hper := hperiod S z m s T a h c γ hT hh hm hs
    have hB₀ : 0≤B γ := by dsimp [B]; positivity
    have h₁ := mul_le_mul_of_nonneg_left hper (by positivity : 0≤3*Real.pi*K)
    have h₂ := mul_le_mul_of_nonneg_left (havg.trans h₁) hB₀
    have habs := bourgain_quadratic_tail_absorption hK hscale γ
    have h₃ := mul_le_mul_of_nonneg_left habs
      (show 0≤3*Real.pi*K*D*J by positivity)
    calc
      _ = B γ*(∫ α : ℝ, L α*F (α,γ)) := by
        rw [←integral_const_mul]
        apply integral_congr_ae
        filter_upwards with α
        ring
      _ ≤ B γ*(3*Real.pi*K*(D*(1+|γ*h^2|)^12*J)) := h₂
      _ = (3*Real.pi*K*D*J)*(B γ*(1+|γ*h^2|)^12) := by ring
      _ ≤ (3*Real.pi*K*D*J)*L γ := h₃
      _ = _ := by ring
  have hright : Integrable (fun γ : ℝ => (3*Real.pi*K*D)*L γ*J) :=
    (hiL.const_mul _).mul_const _
  have hlast := integral_mono hiV.integral_prod_right hright hpoint
  have hswap := integral_prod_symm (fun p : ℝ × ℝ => L p.1*B p.2*F p) hiV
  have hmass : (∫ x : ℝ, L x)=K*Real.pi := by
    have he := Measure.integral_comp_div (fun y : ℝ => (1+y^2)⁻¹) K
    simpa only [L,integral_univ_inv_one_add_sq,abs_of_pos hK,smul_eq_mul] using he
  calc
    _ ≤ ∫ p : ℝ × ℝ, L p.1*B p.2*F p := hmajor
    _ = ∫ γ : ℝ, ∫ α : ℝ, L α*B γ*F (α,γ) := hswap
    _ ≤ ∫ γ : ℝ, (3*Real.pi*K*D)*L γ*J := hlast
    _ = _ := by rw [integral_mul_const,integral_const_mul,hmass]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgain_integer_parabola_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (n : ℕ) (K T c : ℝ), 0<T → T≤K →
      3/(100*K)≤(1/(2:ℝ)^n)^2 → K≤((2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ)
        (m : Fin (2^n) → ι → ℤ),
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ i∈S j, T*x j i=(m j i:ℝ)-c) →
        parabolaBoxBilinearMoment (Finset.univ.sigma S) (Finset.univ.sigma S)
          (fun ji => z ji.1 ji.2) (fun ji => z ji.1 ji.2)
          (fun ji => x ji.1 ji.2) (fun ji => x ji.1 ji.2) K 0 0 ≤
          C*(2:ℝ)^((ε+2)*n)*K^2*
            (∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ i∈S j, z j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6) := by
  obtain ⟨D,hD,hdec⟩ := exists_parabolaBox_sourceWeight_decoupling.{u} hε
  obtain ⟨E,hE,hcell⟩ := exists_bourgain_integer_parabola_weighted_cell.{u}
  refine ⟨D*E,mul_pos hD hE,?_⟩
  intro n K T c hT hTK hwidth hsmall ι S z x m hx hm
  have hK : 0<K := hT.trans_le hTK
  let N : ℝ := (2:ℝ)^n
  have hN : 0<N := by dsimp [N]; positivity
  let W := fun p : ℝ × ℝ => parabolaSourceWeight K 0 0 p.1 p.2
  let J := fun j : Fin (2^n) => ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S j, z j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6
  have hnorm (j : Fin (2^n)) :
      (parabolaWeightedSixNorm W (S j) (z j) (x j))^6≤E*K^2*J j := by
    let a : ℝ := (j:ℕ)/N
    let h : ℝ := 1/N
    let s := fun i => N*x j i-(j:ℕ)
    have hh : h≠0 := by dsimp [h]; positivity
    have hscale : K*h^2≤1 := by
      have he : K*h^2=K/N^2 := by dsimp [h]; ring
      rw [he]
      exact (div_le_one (sq_pos_of_pos hN)).mpr hsmall
    have he (i : ι) : a+h*s i=x j i := by
      dsimp [a,h,s]
      field_simp
      ring
    have hs (i : ι) (hi : i∈S j) : s i∈Icc (-1:ℝ) 1 := by
      have hl := (hx j i hi).1
      have hu := (hx j i hi).2
      norm_num only [Nat.cast_pow,Nat.cast_ofNat] at hl hu
      change (j:ℕ)/N≤x j i at hl
      change ((j:ℕ)+1)/N≥x j i at hu
      have hl' := (div_le_iff₀ hN).mp hl
      have hu' := (le_div_iff₀ hN).mp hu
      dsimp [s]
      constructor <;> nlinarith
    have hphysical := hcell (S j) (z j) (m j) s T K a h c
      hT hTK hh hscale (fun i hi => by rw [he]; exact hm j i hi) hs
    simp_rw [he] at hphysical
    have hn := parabolaWeightedSixNorm_pow_six W
      (fun p => parabolaSourceWeight_nonneg _ _ _ _ _)
      (integrable_parabolaSourceWeight hK 0 0) (S j) (z j) (x j)
    rw [hn]
    have halg (v : ℝ) : v^2*v^4=v^6 := by ring
    simpa only [parabolaWeightedBilinearMoment,mul_assoc,halg,W,J] using hphysical
  have hsum := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hnorm j)
  rw [←Finset.mul_sum] at hsum
  have hp := pow_sum_le_card_mul_sum_pow (s:=Finset.univ)
    (f:=fun j => (parabolaWeightedSixNorm W (S j) (z j) (x j))^2)
    (fun _ _ => sq_nonneg _) 2
  norm_num only [show (2+1:ℕ)=3 by omega,←pow_mul,
    show (2*3:ℕ)=6 by omega,Finset.card_univ,Fintype.card_fin,
    Nat.cast_pow,Nat.cast_ofNat] at hp
  have hs : (∑ j, (parabolaWeightedSixNorm W (S j) (z j) (x j))^2)^3≤
      N^2*(E*K^2*∑ j, J j) :=
    hp.trans (by simpa only [N,pow_mul] using
      mul_le_mul_of_nonneg_left hsum (sq_nonneg N))
  have hd := hdec n K 0 0 hK hwidth ι S z x hx
  have hcoef : (2:ℝ)^(ε*n)*N^2=(2:ℝ)^((ε+2)*n) := by
    have he : N^2=(2:ℝ)^((2:ℝ)*n) := by
      dsimp [N]
      rw [←Real.rpow_natCast (2:ℝ) n,←Real.rpow_mul_natCast (by norm_num)]
      congr 1
      push_cast
      ring
    rw [he,←Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc
    _ ≤ D*(2:ℝ)^(ε*n)*(∑ j,
      (parabolaWeightedSixNorm W (S j) (z j) (x j))^2)^3 := hd
    _ ≤ D*(2:ℝ)^(ε*n)*(N^2*(E*K^2*∑ j, J j)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = D*E*((2:ℝ)^(ε*n)*N^2)*K^2*(∑ j, J j) := by ring
    _ = _ := by rw [hcoef]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgain_integer_parabola_periodic_box {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (w : ι → ℝ)
    {T K H c : ℝ} (hT : 0<T) (hTK : T≤K) (hHK : H≤K)
    (hw : ∀ i∈S, T*w i=(m i:ℝ)-c) :
    T*(∫ β : ℝ in Icc (-H) H, ∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+β*(w i)^2)‖^6) ≤
      parabolaBoxBilinearMoment S S z z w w K 0 0 := by
  let F := fun p : ℝ × ℝ => ‖sargosPlanarSum S z w (fun i => (w i)^2) p.1 p.2‖^6
  have hFc : Continuous F := by unfold F sargosPlanarSum fordAdditiveCharacter; fun_prop
  have hF₀ (p : ℝ × ℝ) : 0≤F p := by dsimp [F]; positivity
  have he (u β : ℝ) :
      ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+β*(w i)^2)‖^6=F (T*u,β) := by
    have hh : (∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u+β*(w i)^2)) =
        fordAdditiveCharacter (c*u)*sargosPlanarSum S z w (fun i => (w i)^2) (T*u) β := by
      unfold sargosPlanarSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hp : (m i:ℝ)*u+β*(w i)^2 =
          c*u+(w i*(T*u)+(w i)^2*β) := by linear_combination -u*(hw i hi)
      rw [hp,fordAdditiveCharacter_add]
      ring
    rw [hh,norm_mul,sargos_character_norm,one_mul]
  have hscale (β : ℝ) :
      T*(∫ u : ℝ in Icc (0:ℝ) 1, F (T*u,β))=
        ∫ α : ℝ in Icc (0:ℝ) T, F (α,β) := by
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
      ←intervalIntegral.integral_of_le hT.le]
    have hh := intervalIntegral.smul_integral_comp_mul_left (fun α : ℝ => F (α,β)) T
      (a:=0) (b:=1)
    simpa only [smul_eq_mul,mul_zero,mul_one] using hh
  let B := Icc (0:ℝ) T ×ˢ Icc (-H) H
  let Q := Icc (-K) K ×ˢ Icc (-K) K
  have hiB : IntegrableOn F B := hFc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hiQ : IntegrableOn F Q := hFc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hswap : (∫ p : ℝ × ℝ in B, F p)=
      ∫ β : ℝ in Icc (-H) H, ∫ α : ℝ in Icc (0:ℝ) T, F (α,β) := by
    have hi : Integrable F ((volume.restrict (Icc (0:ℝ) T)).prod
        (volume.restrict (Icc (-H) H))) := by
      rw [Measure.prod_restrict]
      exact hiB
    have hh := integral_prod_symm F hi
    rw [Measure.prod_restrict] at hh
    exact hh
  have hsub : B⊆Q := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1],hp.1.2.trans hTK⟩,
      ⟨by linarith [hp.2.1],hp.2.2.trans hHK⟩⟩
  have hmajor := setIntegral_mono_set (s:=B) hiQ
    (Filter.Eventually.of_forall hF₀) (Filter.Eventually.of_forall (fun _ hp => hsub hp))
  calc
    _ = T*(∫ β : ℝ in Icc (-H) H, ∫ u : ℝ in Icc (0:ℝ) 1, F (T*u,β)) := by
      simp only [he]
    _ = ∫ β : ℝ in Icc (-H) H, ∫ α : ℝ in Icc (0:ℝ) T, F (α,β) := by
      rw [←integral_const_mul]
      simp only [hscale]
    _ = ∫ p : ℝ × ℝ in B, F p := hswap.symm
    _ ≤ ∫ p : ℝ × ℝ in Q, F p := hmajor
    _ = _ := by
      unfold parabolaBoxBilinearMoment
      simp only [zero_sub,zero_add]
      apply integral_congr_ae
      filter_upwards with p
      dsimp [F]
      ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgain_integer_periodic_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (n : ℕ) (K T H c : ℝ), 0<T → T≤K → H≤K →
      3/(100*K)≤(1/(2:ℝ)^n)^2 → K≤((2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ)
        (m : Fin (2^n) → ι → ℤ),
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ i∈S j, T*x j i=(m j i:ℝ)-c) →
        T*(∫ β : ℝ in Icc (-H) H, ∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ ji∈Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            ((m ji.1 ji.2:ℝ)*u+β*(x ji.1 ji.2)^2)‖^6) ≤
          C*(2:ℝ)^((ε+2)*n)*K^2*
            (∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ i∈S j, z j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgain_integer_parabola_refinement.{u} hε
  refine ⟨C,hC,?_⟩
  intro n K T H c hT hTK hHK hwidth hsmall ι S z x m hx hm
  have hentry := bourgain_integer_parabola_periodic_box
    (Finset.univ.sigma S) (fun ji => z ji.1 ji.2) (fun ji => m ji.1 ji.2)
    (fun ji => x ji.1 ji.2) hT hTK hHK
    (fun ji hji => hm ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
  exact hentry.trans (hbound n K T c hT hTK hwidth hsmall ι S z x m hx hm)

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgain_integer_scaled_periodic_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (n : ℕ) (K T R δ c : ℝ), 0<T → T≤K → 0≤R →
      2*R*δ^2≤K → 3/(100*K)≤(1/(2:ℝ)^n)^2 → K≤((2:ℝ)^n)^2 →
      ∀ (ι : Type u) (S : Fin (2^n) → Finset ι)
        (z : Fin (2^n) → ι → ℂ) (x : Fin (2^n) → ι → ℝ)
        (m : Fin (2^n) → ι → ℤ),
        (∀ j, ∀ i∈S j, x j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ i∈S j, T*x j i=(m j i:ℝ)-c) →
        (T*δ^2)*(∫ y : ℝ in Icc (-2*R) (2*R), ∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ ji∈Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
            ((m ji.1 ji.2:ℝ)*u+δ^2*y*(x ji.1 ji.2)^2)‖^6) ≤
          C*(2:ℝ)^((ε+2)*n)*K^2*
            (∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ i∈S j, z j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgain_integer_periodic_refinement.{u} hε
  refine ⟨C,hC,?_⟩
  intro n K T R δ c hT hTK hR hscale hwidth hsmall ι S z x m hx hm
  let G := fun β : ℝ => ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ ji∈Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
      ((m ji.1 ji.2:ℝ)*u+β*(x ji.1 ji.2)^2)‖^6
  have hchange : δ^2*(∫ y : ℝ in Icc (-2*R) (2*R), G (δ^2*y)) =
      ∫ β : ℝ in Icc (-(2*R*δ^2)) (2*R*δ^2), G β := by
    have hle : -2*R≤2*R := by linarith
    have hle' : -(2*R*δ^2)≤2*R*δ^2 := by
      nlinarith [mul_nonneg hR (sq_nonneg δ)]
    rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
      ←intervalIntegral.integral_of_le hle,←intervalIntegral.integral_of_le hle']
    have hh := intervalIntegral.smul_integral_comp_mul_left G (δ^2) (a:= -2*R) (b:=2*R)
    have he₁ : δ^2*(-2*R)= -(2*R*δ^2) := by ring
    have he₂ : δ^2*(2*R)=2*R*δ^2 := by ring
    simpa only [smul_eq_mul,he₁,he₂] using hh
  have hh := hbound n K T (2*R*δ^2) c hT hTK hscale hwidth hsmall ι S z x m hx hm
  change T*(∫ β : ℝ in Icc (-(2*R*δ^2)) (2*R*δ^2), G β)≤_ at hh
  rw [←hchange] at hh
  simpa only [mul_assoc,G] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainOriginalSource_periodic_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (n : ℕ) (b d δ T R q ν K : ℝ),
      b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
      δ∈Ioc (0:ℝ) (1/16) → 0<T → 0≤R →
      R*δ^3≤32 → |q*δ^2|≤32 → 0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
      T*δ≤K → 2*R*δ^2≤K →
      3/(100*K)≤(1/(2:ℝ)^n)^2 → K≤((2:ℝ)^n)^2 →
      ∀ (ι κ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset κ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → κ → ℂ)
        (s : Fin (2^n) → ι → ℝ) (v : Fin (2^n) → κ → ℝ)
        (m : Fin (2^n) → ι → ℤ) (l : Fin (2^n) → κ → ℤ),
        (∀ j, ∀ i∈S j, s j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ i∈V j, v j i∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ i∈S j, T*(b+δ*s j i)=(m j i:ℝ)) →
        (∀ j, ∀ i∈V j, T*(d+δ*v j i)=(l j i:ℝ)) →
        (T*δ^3)^2*(∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
          (∫ u : ℝ in Icc (0:ℝ) 1,
            bourgainSourceSixMoment (Finset.univ.sigma S)
              (fun ji => z ji.1 ji.2) (fun ji => b+δ*s ji.1 ji.2) ![T*u,x 0,x 1,q])*
          (∫ u : ℝ in Icc (0:ℝ) 1,
            bourgainSourceSixMoment (Finset.univ.sigma V)
              (fun ji => c ji.1 ji.2) (fun ji => d+δ*v ji.1 ji.2) ![T*u,x 0,x 1,q])) ≤
          (C/ν)*(2:ℝ)^((ε+4)*n)*K^4*
            (∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ i∈S j, z j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6)*
            (∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
              ‖∑ i∈V j, c j i*fordAdditiveCharacter ((l j i:ℝ)*u)‖^6) := by
  obtain ⟨E,hE,hframe⟩ := exists_bourgainOriginalSource_periodic_box_factorization.{u}
  obtain ⟨D,hD,hdec⟩ := exists_bourgain_integer_scaled_periodic_refinement.{u}
    (ε:=ε/2) (by positivity)
  refine ⟨E*D^2,by positivity,?_⟩
  intro n b d δ T R q ν K hb hd hδ hT hR hrem hq hν hsep hTK hscale hwidth hsmall
    ι κ S V z c s v m l hs hv hm hl
  have hδ₀ : 0<δ := hδ.1
  have hunit (j : Fin (2^n)) (y : ℝ)
      (hy : y∈Icc ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) :
      y∈Icc (-1:ℝ) 1 := by
    have hn : (0:ℝ)<((2^n:ℕ):ℝ) := by positivity
    have hj₀ : (0:ℝ)≤(j:ℕ)/((2^n:ℕ):ℝ) := by positivity
    have hj₁ : ((j:ℕ):ℝ)+1≤((2^n:ℕ):ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt j.isLt
    have hh := (div_le_one hn).mpr hj₁
    exact ⟨by linarith [hy.1],hy.2.trans hh⟩
  have hsflat : ∀ ji∈Finset.univ.sigma S, s ji.1 ji.2∈Icc (-1:ℝ) 1 :=
    fun ji hji => hunit ji.1 _ (hs ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
  have hvflat : ∀ ji∈Finset.univ.sigma V, v ji.1 ji.2∈Icc (-1:ℝ) 1 :=
    fun ji hji => hunit ji.1 _ (hv ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
  have hf := hframe b d δ T R q ν hb hd hδ hT hrem hq hν hsep
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun ji => c ji.1 ji.2)
    (fun ji => s ji.1 ji.2) (fun ji => v ji.1 ji.2)
    (fun ji => m ji.1 ji.2) (fun ji => l ji.1 ji.2) hsflat hvflat
    (fun ji hji => hm ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
    (fun ji hji => hl ji.1 ji.2 (Finset.mem_sigma.mp hji).2)
  let J₁ := ∫ y : ℝ in Icc (-2*R) (2*R), ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ ji∈Finset.univ.sigma S, z ji.1 ji.2*fordAdditiveCharacter
      ((m ji.1 ji.2:ℝ)*u+δ^2*y*(s ji.1 ji.2)^2)‖^6
  let J₂ := ∫ y : ℝ in Icc (-2*R) (2*R), ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ ji∈Finset.univ.sigma V, c ji.1 ji.2*fordAdditiveCharacter
      ((l ji.1 ji.2:ℝ)*u+δ^2*y*(v ji.1 ji.2)^2)‖^6
  let L₁ := ∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S j, z j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6
  let L₂ := ∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈V j, c j i*fordAdditiveCharacter ((l j i:ℝ)*u)‖^6
  have hJ₂ : 0≤J₂ := integral_nonneg (fun y => integral_nonneg (fun u => by positivity))
  have hL₁ : 0≤L₁ := Finset.sum_nonneg (fun j _ => integral_nonneg (fun u => by positivity))
  have h₁ := hdec n K (T*δ) R δ (T*b) (mul_pos hT hδ.1) hTK hR hscale hwidth hsmall
    ι S z s m hs (fun j i hi => by linear_combination hm j i hi)
  have h₂ := hdec n K (T*δ) R δ (T*d) (mul_pos hT hδ.1) hTK hR hscale hwidth hsmall
    κ V c v l hv (fun j i hi => by linear_combination hl j i hi)
  have he : (T*δ)*δ^2=T*δ^3 := by ring
  rw [he] at h₁ h₂
  change (T*δ^3)*J₁≤D*(2:ℝ)^((ε/2+2)*n)*K^2*L₁ at h₁
  change (T*δ^3)*J₂≤D*(2:ℝ)^((ε/2+2)*n)*K^2*L₂ at h₂
  have hprod := mul_le_mul h₁ h₂ (by positivity : 0≤(T*δ^3)*J₂)
    (by positivity : 0≤D*(2:ℝ)^((ε/2+2)*n)*K^2*L₁)
  have hcoef : ((2:ℝ)^((ε/2+2)*n))^2=(2:ℝ)^((ε+4)*n) := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (T*δ^3)^2*((E/ν)*J₁*J₂) := mul_le_mul_of_nonneg_left hf (sq_nonneg _)
    _ = (E/ν)*(((T*δ^3)*J₁)*((T*δ^3)*J₂)) := by ring
    _ ≤ (E/ν)*((D*(2:ℝ)^((ε/2+2)*n)*K^2*L₁)*
        (D*(2:ℝ)^((ε/2+2)*n)*K^2*L₂)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = (E*D^2/ν)*((2:ℝ)^((ε/2+2)*n))^2*K^4*L₁*L₂ := by ring
    _ = _ := by rw [hcoef]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainSource_integer_period_shift {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (w : ι → ℝ)
    {T : ℝ} (hT : T≠0) (hw : ∀ i∈S, T*w i=(m i:ℝ))
    (x : Fin 3 → ℝ) (r : ℝ) :
    (∫ u : ℝ in Icc (0:ℝ) 1,
      bourgainSourceSixMoment S z w ![T*u+r,x 0,x 1,x 2]) =
    (∫ u : ℝ in Icc (0:ℝ) 1,
      bourgainSourceSixMoment S z w ![T*u,x 0,x 1,x 2]) := by
  let A := fun i => x 0*(w i)^2+x 1*(w i)^((3:ℝ)/2)+x 2*Real.sqrt (w i)
  let z' := fun i => z i*fordAdditiveCharacter (A i)
  have he (u r : ℝ) :
      bourgainSourceSixMoment S z w ![T*u+r,x 0,x 1,x 2] =
        ‖∑ i∈S, z' i*fordAdditiveCharacter ((m i:ℝ)*u+r*w i)‖^6 := by
    unfold bourgainSourceSixMoment
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [z']
    rw [mul_assoc,←fordAdditiveCharacter_add]
    congr 2
    change (T*u+r)*w i+x 0*(w i)^2+x 1*(w i)^((3:ℝ)/2)+x 2*Real.sqrt (w i) =
      A i+((m i:ℝ)*u+r*w i)
    dsimp [A]
    linear_combination u*(hw i hi)
  have he₀ (u : ℝ) :
      bourgainSourceSixMoment S z w ![T*u,x 0,x 1,x 2] =
        ‖∑ i∈S, z' i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6 := by
    simpa only [add_zero,zero_mul] using he u 0
  simp only [he,he₀]
  have hh := bourgain_integer_cell_linear_shift S z' m w hT
    (c:=0) (fun i hi => by simpa only [sub_zero] using hw i hi) r 0
  simpa only [zero_mul,add_zero] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

set_option maxHeartbeats 400000 in
private theorem bourgainSource_shifted_radial_period_entry {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {T K : ℝ}
    (hT : 0<T) (hTK : T≤K) (q : Fin 4 → ℝ) :
    let w := fun i => (m i:ℝ)/T
    (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*bourgainSourceSixMoment S z w (q+x)) ≤
      3*Real.pi*K*(∫ y : Fin 3 → ℝ, (∏ j : Fin 3, (1+(y j/K)^2)⁻¹)*
        (∫ u : ℝ in Icc (0:ℝ) 1,
          bourgainSourceSixMoment S
            (fun i => z i*fordAdditiveCharacter
              (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i)))
            w ![T*u,q 1,q 2,q 3])) := by
  let w := fun i => (m i:ℝ)/T
  let zq := fun i => z i*fordAdditiveCharacter
    (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))
  let zy := fun (y : Fin 3 → ℝ) (i : ι) => z i*fordAdditiveCharacter
    (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))
  have hw (i : ι) : T*w i=(m i:ℝ) := by dsimp [w]; field_simp
  have hh := bourgainSource_integer_coordinate_average S zq m hT hTK
  have hleft (x : Fin 4 → ℝ) :
      bourgainSourceSixMoment S zq w x=bourgainSourceSixMoment S z w (q+x) := by
    rw [bourgainSourceSixMoment_translate]
    rw [add_comm x q]
  have he (y : Fin 3 → ℝ) (u : ℝ) :
      ‖∑ i∈S, zq i*fordAdditiveCharacter
        (u*(m i:ℝ)+y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))‖^6 =
      bourgainSourceSixMoment S (zy y) w ![T*u+q 0,q 1,q 2,q 3] := by
    unfold bourgainSourceSixMoment
    apply congrArg (fun v : ℂ => ‖v‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [zq,zy]
    rw [mul_assoc,mul_assoc,←fordAdditiveCharacter_add,←fordAdditiveCharacter_add]
    apply congrArg (fun t : ℝ => z i*fordAdditiveCharacter t)
    change
      (q 0*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))+
        (u*(m i:ℝ)+y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i)) =
      (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))+
        ((T*u+q 0)*w i+q 1*(w i)^2+q 2*(w i)^((3:ℝ)/2)+q 3*Real.sqrt (w i))
    linear_combination -u*(hw i)
  change (∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*bourgainSourceSixMoment S zq w x) ≤
    3*Real.pi*K*(∫ y : Fin 3 → ℝ, (∏ j : Fin 3, (1+(y j/K)^2)⁻¹)*
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, zq i*fordAdditiveCharacter
          (u*(m i:ℝ)+y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))‖^6)) at hh
  simp only [hleft,he] at hh
  have hperiod (y : Fin 3 → ℝ) :
      (∫ u : ℝ in Icc (0:ℝ) 1,
        bourgainSourceSixMoment S (zy y) w ![T*u+q 0,q 1,q 2,q 3]) =
      ∫ u : ℝ in Icc (0:ℝ) 1,
        bourgainSourceSixMoment S (zy y) w ![T*u,q 1,q 2,q 3] :=
    bourgainSource_integer_period_shift S (zy y) m w hT.ne'
      (fun i _ => hw i) (![q 1,q 2,q 3] : Fin 3 → ℝ) (q 0)
  simpa only [hperiod,zy,w] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private def bourgainSourcePeriod {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (w : ι → ℝ) (T : ℝ) (q : Fin 3 → ℝ) : ℝ :=
  ∫ u : ℝ in Icc (0:ℝ) 1, bourgainSourceSixMoment S z w ![T*u,q 0,q 1,q 2]

private def bourgainSourceShiftedPeriod {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (w : ι → ℝ) (T : ℝ) (y q : Fin 3 → ℝ) : ℝ :=
  bourgainSourcePeriod S
    (fun i => z i*fordAdditiveCharacter
      (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))) w T q

private theorem continuous_bourgainSourceShiftedPeriod {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (T : ℝ) :
    Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      bourgainSourceShiftedPeriod S z w T p.1 p.2) := by
  let F := fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (u : ℝ) =>
    bourgainSourceSixMoment S (fun i => z i*fordAdditiveCharacter
      (p.1 0*(w i)^2+p.1 1*(w i)^((3:ℝ)/2)+p.1 2*Real.sqrt (w i)))
      w ![T*u,p.2 0,p.2 1,p.2 2]
  have hF : Continuous F.uncurry := by
    unfold F Function.uncurry bourgainSourceSixMoment fordAdditiveCharacter
    fun_prop
  have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ:=volume) hF 0 1
  simpa only [bourgainSourceShiftedPeriod,bourgainSourcePeriod,F,
    integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hh

private theorem bourgainSourceShiftedPeriod_nonneg {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (T : ℝ)
    (y q : Fin 3 → ℝ) : 0≤bourgainSourceShiftedPeriod S z w T y q :=
  integral_nonneg (fun _ => bourgainSourceSixMoment_nonneg _ _ _ _)

private theorem bourgainSourceShiftedPeriod_norm_bound {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (T : ℝ)
    (y q : Fin 3 → ℝ) :
    ‖bourgainSourceShiftedPeriod S z w T y q‖≤(∑ i∈S, ‖z i‖)^6 := by
  let zy := fun i => z i*fordAdditiveCharacter
    (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))
  have hb (u : ℝ) : ‖bourgainSourceSixMoment S zy w ![T*u,q 0,q 1,q 2]‖≤
      (∑ i∈S, ‖z i‖)^6 := by
    have hh := bourgainSourceSixMoment_norm_bound S zy w ![T*u,q 0,q 1,q 2]
    simpa only [zy,norm_mul,sargos_character_norm,mul_one] using hh
  have hh := norm_setIntegral_le_of_norm_le_const
    (μ:=volume) (s:=Icc (0:ℝ) 1) isCompact_Icc.measure_lt_top (fun u _ => hb u)
  simpa only [Real.volume_real_Icc,sub_zero,max_eq_left (by norm_num : (0:ℝ)≤1),
    one_mul,mul_one,bourgainSourceShiftedPeriod,bourgainSourcePeriod,zy] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem continuous_bourgainSource_radial_average {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) {K : ℝ} (hK : 0<K) :
    Continuous (fun q : Fin 4 → ℝ =>
      ∫ x : Fin 4 → ℝ, bourgainRadialWeight K x*bourgainSourceSixMoment S z w (q+x)) := by
  let W := bourgainRadialWeight K
  let F := bourgainSourceSixMoment S z w
  let M := (∑ i∈S, ‖z i‖)^6
  have hWc : Continuous W := continuous_bourgainRadialWeight K
  have hFc : Continuous F := continuous_bourgainSourceSixMoment S z w
  have hFb : ∀ x, ‖F x‖≤M := bourgainSourceSixMoment_norm_bound S z w
  have hiW : Integrable W := integrable_bourgainCurveCellWeight hK
  apply continuous_of_dominated
    (bound:=fun x : Fin 4 → ℝ => W x*M)
  · intro q
    exact (hWc.mul (hFc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · intro q
    filter_upwards with x
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (bourgainRadialWeight_nonneg K x)]
    exact mul_le_mul_of_nonneg_left (hFb (q+x)) (bourgainRadialWeight_nonneg K x)
  · exact hiW.mul_const M
  · filter_upwards with x
    exact continuous_const.mul (hFc.comp (continuous_id.add continuous_const))

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

set_option maxHeartbeats 400000 in
private theorem bourgainSource_radial_pair_period_entry {ι κ : Type*}
    (S : Finset ι) (V : Finset κ) (z : ι → ℂ) (c : κ → ℂ)
    (m : ι → ℤ) (l : κ → ℤ) {T K R : ℝ}
    (hT : 0<T) (hTK : T≤K) (r q : ℝ) :
    let w := fun i => (m i:ℝ)/T
    let v := fun j => (l j:ℝ)/T
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      (∏ j : Fin 3, (1+(p.1 j/K)^2)⁻¹)*(∏ j : Fin 3, (1+(p.2 j/K)^2)⁻¹)*
        (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
          bourgainSourceShiftedPeriod S z w T p.1 ![x 0,x 1,q]*
          bourgainSourceShiftedPeriod V c v T p.2 ![x 0,x 1,q])) ∧
    (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
      (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
        bourgainSourceSixMoment S z w (![r,x 0,x 1,q]+y))*
      (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
        bourgainSourceSixMoment V c v (![r,x 0,x 1,q]+y))) ≤
      (3*Real.pi*K)^2*(∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
        (∏ j : Fin 3, (1+(p.1 j/K)^2)⁻¹)*(∏ j : Fin 3, (1+(p.2 j/K)^2)⁻¹)*
          (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
            bourgainSourceShiftedPeriod S z w T p.1 ![x 0,x 1,q]*
            bourgainSourceShiftedPeriod V c v T p.2 ![x 0,x 1,q])) := by
  let w := fun i => (m i:ℝ)/T
  let v := fun j => (l j:ℝ)/T
  let B := Icc (fun _ : Fin 2 => -R) (fun _ => R)
  let W := fun y : Fin 3 → ℝ => ∏ j, (1+(y j/K)^2)⁻¹
  let F := bourgainSourceShiftedPeriod S z w T
  let G := bourgainSourceShiftedPeriod V c v T
  let H := fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (x : Fin 2 → ℝ) =>
    W p.1*W p.2*(F p.1 ![x 0,x 1,q]*G p.2 ![x 0,x 1,q])
  let JS := fun x : Fin 2 → ℝ => ∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
    bourgainSourceSixMoment S z w (![r,x 0,x 1,q]+y)
  let JV := fun x : Fin 2 → ℝ => ∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
    bourgainSourceSixMoment V c v (![r,x 0,x 1,q]+y)
  have hK : 0<K := hT.trans_le hTK
  have hW : Integrable W :=
    Integrable.fintype_prod (fun _ : Fin 3 => integrable_inv_one_add_sq.comp_div hK.ne')
  have hF : Continuous (Function.uncurry F) :=
    continuous_bourgainSourceShiftedPeriod S z w T
  have hG : Continuous (Function.uncurry G) :=
    continuous_bourgainSourceShiftedPeriod V c v T
  have hmap₁ : Continuous (fun p : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      (p.1.1, (![p.2 0,p.2 1,q] : Fin 3 → ℝ))) := by fun_prop
  have hmap₂ : Continuous (fun p : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      (p.1.2, (![p.2 0,p.2 1,q] : Fin 3 → ℝ))) := by fun_prop
  have hFc := hF.comp hmap₁
  have hGc := hG.comp hmap₂
  have hc := hFc.mul hGc
  have hi1 : IntegrableOn (fun _x : Fin 2 → ℝ => (1:ℝ)) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiH : Integrable (Function.uncurry H) ((volume.prod volume).prod (volume.restrict B)) := by
    have hh := ((hW.mul_prod hW).mul_prod hi1).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        change ‖F p.1.1 ![p.2 0,p.2 1,q]*G p.1.2 ![p.2 0,p.2 1,q]‖≤_
        rw [norm_mul]
        exact mul_le_mul
          (bourgainSourceShiftedPeriod_norm_bound S z w T p.1.1 ![p.2 0,p.2 1,q])
          (bourgainSourceShiftedPeriod_norm_bound V c v T p.1.2 ![p.2 0,p.2 1,q])
          (norm_nonneg _) (by positivity)))
    simpa only [H,Function.uncurry,mul_one] using hh
  have hmap : Continuous (fun x : Fin 2 → ℝ => (![r,x 0,x 1,q] : Fin 4 → ℝ)) := by fun_prop
  have hJS : Continuous JS :=
    (continuous_bourgainSource_radial_average S z w hK).comp hmap
  have hJV : Continuous JV :=
    (continuous_bourgainSource_radial_average V c v hK).comp hmap
  have hiLeft : IntegrableOn (fun x => JS x*JV x) B :=
    (hJS.mul hJV).continuousOn.integrableOn_compact isCompact_Icc
  have he (x : Fin 2 → ℝ) :
      (∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), H p x)=
        (∫ y : Fin 3 → ℝ, W y*F y ![x 0,x 1,q])*
        (∫ y : Fin 3 → ℝ, W y*G y ![x 0,x 1,q]) := by
    calc
      _ = ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
          (W p.1*F p.1 ![x 0,x 1,q])*(W p.2*G p.2 ![x 0,x 1,q]) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [H]
        ring
      _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
        (fun y : Fin 3 → ℝ => W y*F y ![x 0,x 1,q])
        (fun y : Fin 3 → ℝ => W y*G y ![x 0,x 1,q])
  have hpoint (x : Fin 2 → ℝ) (_hx : x∈B) :
      JS x*JV x≤(3*Real.pi*K)^2*(∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), H p x) := by
    have hs := bourgainSource_shifted_radial_period_entry S z m hT hTK ![r,x 0,x 1,q]
    have hv := bourgainSource_shifted_radial_period_entry V c l hT hTK ![r,x 0,x 1,q]
    change JS x≤3*Real.pi*K*(∫ y : Fin 3 → ℝ, W y*F y ![x 0,x 1,q]) at hs
    change JV x≤3*Real.pi*K*(∫ y : Fin 3 → ℝ, W y*G y ![x 0,x 1,q]) at hv
    have hJV₀ : 0≤JV x := integral_nonneg (fun y => mul_nonneg
      (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _))
    have hR₀ : 0≤3*Real.pi*K*(∫ y : Fin 3 → ℝ, W y*F y ![x 0,x 1,q]) := by
      apply mul_nonneg (by positivity)
      apply integral_nonneg
      intro y
      exact mul_nonneg (by dsimp [W]; positivity)
        (bourgainSourceShiftedPeriod_nonneg S z w T y _)
    have hp := mul_le_mul hs hv hJV₀ hR₀
    rw [he]
    have halg (A B C : ℝ) : (A*B)*(A*C)=A^2*(B*C) := by ring
    exact hp.trans_eq (halg _ _ _)
  have hm := bourgain_kernel_setIntegral_bound measurableSet_Icc hiLeft hiH hpoint
  have heInner (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) :
      (∫ x : Fin 2 → ℝ in B, H p x)=
        W p.1*W p.2*(∫ x : Fin 2 → ℝ in B,
          F p.1 ![x 0,x 1,q]*G p.2 ![x 0,x 1,q]) := by
    dsimp only [H]
    rw [integral_const_mul]
  have hiOuter : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      ∫ x : Fin 2 → ℝ in B, H p x) := hiH.integral_prod_left
  change (∫ x : Fin 2 → ℝ in B, JS x*JV x)≤
    (3*Real.pi*K)^2*(∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
      ∫ x : Fin 2 → ℝ in B, H p x) at hm
  constructor
  · simpa only [heInner] using hiOuter
  · simpa only [heInner] using hm

end TaoTrudgianYang2025

noncomputable section
open Set
namespace TaoTrudgianYang2025

private theorem bourgain_anisotropic_dyadic_scales (j : ℕ) (hj : 3≤j) :
    let N := (2:ℝ)^(2*j)
    let T := N^2
    let δ := 2/N
    let R := 2*N^3
    let P := 16*N
    δ∈Ioc (0:ℝ) (1/16) ∧ 0<T ∧ 0≤R ∧
    R*δ^3=16 ∧ (2*T)*δ^2=8 ∧
    T*δ≤P ∧ 2*R*δ^2=P ∧
    3/(100*P)≤(1/(2:ℝ)^(j+2))^2 ∧
    P=((2:ℝ)^(j+2))^2 ∧
    (T*δ^3)^2=64/N^2 := by
  let N := (2:ℝ)^(2*j)
  have hN : 0<N := by dsimp [N]; positivity
  have hlarge : (64:ℝ)≤N := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
      (show (6:ℕ)≤2*j by omega)
    norm_num only [show (2:ℝ)^6=64 by norm_num] at hh
    exact hh
  have hP : 16*N=((2:ℝ)^(j+2))^2 := by
    dsimp [N]
    rw [pow_add]
    ring
  have hδ₀ : (0:ℝ)<2/N := by positivity
  have hδ₁ : 2/N≤(1/16:ℝ) := (div_le_iff₀ hN).mpr (by linarith)
  have hR : (2*N^3)*(2/N)^3=16 := by field_simp; ring
  have hq : (2*N^2)*(2/N)^2=8 := by field_simp; ring
  have hTδ : N^2*(2/N)=2*N := by field_simp
  have hβ : 2*(2*N^3)*(2/N)^2=16*N := by field_simp; ring
  have hwidth : 3/(100*(16*N))≤(1/(2:ℝ)^(j+2))^2 := by
    rw [hP]
    have hh : (1/(2:ℝ)^(j+2))^2=1/((2:ℝ)^(j+2))^2 := by ring
    rw [hh]
    have hp : (0:ℝ)<((2:ℝ)^(j+2))^2 := by positivity
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<100*((2:ℝ)^(j+2))^2) hp).mpr
    nlinarith
  have hnormal : (N^2*(2/N)^3)^2=64/N^2 := by field_simp; ring
  exact ⟨⟨hδ₀,hδ₁⟩,by positivity,by positivity,hR,hq,
    by rw [hTδ]; linarith,hβ,hwidth,hP,hnormal⟩

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainSourcePeriod_integer {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (w : ι → ℝ) (T : ℝ)
    (hw : ∀ i∈S, T*w i=(m i:ℝ)) :
    bourgainSourcePeriod S z w T 0 =
      ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter ((m i:ℝ)*u)‖^6 := by
  unfold bourgainSourcePeriod bourgainSourceSixMoment
  apply integral_congr_ae
  filter_upwards with u
  apply congrArg (fun v : ℂ => ‖v‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun a : ℝ => z i*fordAdditiveCharacter a)
  change (T*u)*w i+0*(w i)^2+0*(w i)^((3:ℝ)/2)+0*Real.sqrt (w i)=(m i:ℝ)*u
  linear_combination u*(hw i hi)

private theorem integrable_bourgainSourceShiftedPeriod {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (T : ℝ) (q : Fin 3 → ℝ)
    {K : ℝ} (hK : 0<K) :
    Integrable (fun y : Fin 3 → ℝ => (∏ j : Fin 3, (1+(y j/K)^2)⁻¹)*
      bourgainSourceShiftedPeriod S z w T y q) := by
  have hmap : Continuous (fun y : Fin 3 → ℝ => (y,q)) := continuous_id.prodMk continuous_const
  have hc := (continuous_bourgainSourceShiftedPeriod S z w T).comp hmap
  have hW : Integrable (fun y : Fin 3 → ℝ => ∏ j : Fin 3, (1+(y j/K)^2)⁻¹) :=
    Integrable.fintype_prod (fun _ : Fin 3 => integrable_inv_one_add_sq.comp_div hK.ne')
  exact hW.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => bourgainSourceShiftedPeriod_norm_bound S z w T y q))

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_radial_cell_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (n : ℕ) (b d δ T R r q ν K P : ℝ),
      b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
      δ∈Ioc (0:ℝ) (1/16) → 0<T → T≤K → 0≤R →
      R*δ^3≤32 → |q*δ^2|≤32 → 0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
      T*δ≤P → 2*R*δ^2≤P →
      3/(100*P)≤(1/(2:ℝ)^n)^2 → P≤((2:ℝ)^n)^2 →
      ∀ (ι κ : Type u) (S : Fin (2^n) → Finset ι) (V : Fin (2^n) → Finset κ)
        (z : Fin (2^n) → ι → ℂ) (c : Fin (2^n) → κ → ℂ)
        (m : Fin (2^n) → ι → ℤ) (l : Fin (2^n) → κ → ℤ),
        (∀ j, ∀ i∈S j, (((m j i:ℝ)/T-b)/δ)∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (∀ j, ∀ i∈V j, (((l j i:ℝ)/T-d)/δ)∈Icc
          ((j:ℕ)/((2^n:ℕ):ℝ)) (((j:ℕ)+1)/((2^n:ℕ):ℝ))) →
        (T*δ^3)^2*(∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
              (fun ji => (m ji.1 ji.2:ℝ)/T) (![r,x 0,x 1,q]+y))*
          (∫ y : Fin 4 → ℝ, bourgainRadialWeight K y*
            bourgainSourceSixMoment (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
              (fun ji => (l ji.1 ji.2:ℝ)/T) (![r,x 0,x 1,q]+y))) ≤
          (C/ν)*(2:ℝ)^((ε+4)*n)*K^2*P^4*
            (∑ j, ∫ y : Fin 3 → ℝ, (∏ k : Fin 3, (1+(y k/K)^2)⁻¹)*
              bourgainSourceShiftedPeriod (S j) (z j) (fun i => (m j i:ℝ)/T) T y 0)*
            (∑ j, ∫ y : Fin 3 → ℝ, (∏ k : Fin 3, (1+(y k/K)^2)⁻¹)*
              bourgainSourceShiftedPeriod (V j) (c j) (fun i => (l j i:ℝ)/T) T y 0) := by
  obtain ⟨D,hD,href⟩ := exists_bourgainOriginalSource_periodic_refinement.{u} hε
  refine ⟨9*Real.pi^2*D,by positivity,?_⟩
  intro n b d δ T R r q ν K P hb hd hδ hT hTK hR hrem hq hν hsep hTP hscale hwidth hsmall
    ι κ S V z c m l hs hv
  have hK : 0<K := hT.trans_le hTK
  have hδ₀ : 0<δ := hδ.1
  let w := fun j i => (m j i:ℝ)/T
  let v := fun j i => (l j i:ℝ)/T
  let s := fun j i => (w j i-b)/δ
  let t := fun j i => (v j i-d)/δ
  let W := fun y : Fin 3 → ℝ => ∏ j, (1+(y j/K)^2)⁻¹
  let LS := fun y : Fin 3 → ℝ => ∑ j, bourgainSourceShiftedPeriod (S j) (z j) (w j) T y 0
  let LV := fun y : Fin 3 → ℝ => ∑ j, bourgainSourceShiftedPeriod (V j) (c j) (v j) T y 0
  let zy := fun (y : Fin 3 → ℝ) j i => z j i*fordAdditiveCharacter
    (y 0*(w j i)^2+y 1*(w j i)^((3:ℝ)/2)+y 2*Real.sqrt (w j i))
  let cy := fun (y : Fin 3 → ℝ) j i => c j i*fordAdditiveCharacter
    (y 0*(v j i)^2+y 1*(v j i)^((3:ℝ)/2)+y 2*Real.sqrt (v j i))
  let B := Icc (fun _ : Fin 2 => -R) (fun _ => R)
  let J := fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    ∫ x : Fin 2 → ℝ in B,
      bourgainSourceShiftedPeriod (Finset.univ.sigma S) (fun ji => z ji.1 ji.2)
        (fun ji => w ji.1 ji.2) T p.1 ![x 0,x 1,q]*
      bourgainSourceShiftedPeriod (Finset.univ.sigma V) (fun ji => c ji.1 ji.2)
        (fun ji => v ji.1 ji.2) T p.2 ![x 0,x 1,q]
  let A := (T*δ^3)^2
  let E := (D/ν)*(2:ℝ)^((ε+4)*n)*P^4
  have heS (j : Fin (2^n)) (i : ι) : b+δ*s j i=w j i := by
    dsimp [s]
    field_simp
    ring
  have heV (j : Fin (2^n)) (i : κ) : d+δ*t j i=v j i := by
    dsimp [t]
    field_simp
    ring
  have hm (j : Fin (2^n)) (i : ι) : T*w j i=(m j i:ℝ) := by dsimp [w]; field_simp
  have hl (j : Fin (2^n)) (i : κ) : T*v j i=(l j i:ℝ) := by dsimp [v]; field_simp
  have hLS (y : Fin 3 → ℝ) :
      LS y=∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S j, zy y j i*fordAdditiveCharacter ((m j i:ℝ)*u)‖^6 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact bourgainSourcePeriod_integer (S j) (zy y j) (m j) (w j) T (fun i _ => hm j i)
  have hLV (y : Fin 3 → ℝ) :
      LV y=∑ j, ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈V j, cy y j i*fordAdditiveCharacter ((l j i:ℝ)*u)‖^6 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact bourgainSourcePeriod_integer (V j) (cy y j) (l j) (v j) T (fun i _ => hl j i)
  have hpoint (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : A*J p≤E*LS p.1*LV p.2 := by
    have hh := href n b d δ T R q ν P hb hd hδ hT hR hrem hq hν hsep
      hTP hscale hwidth hsmall ι κ S V (zy p.1) (cy p.2) s t m l hs hv
      (fun j i _ => by rw [heS]; exact hm j i)
      (fun j i _ => by rw [heV]; exact hl j i)
    simp_rw [heS,heV] at hh
    rw [←hLS,←hLV] at hh
    exact hh
  have hiS (j : Fin (2^n)) :
      Integrable (fun y : Fin 3 → ℝ => W y*bourgainSourceShiftedPeriod (S j) (z j) (w j) T y 0) :=
    integrable_bourgainSourceShiftedPeriod (S j) (z j) (w j) T 0 hK
  have hiV (j : Fin (2^n)) :
      Integrable (fun y : Fin 3 → ℝ => W y*bourgainSourceShiftedPeriod (V j) (c j) (v j) T y 0) :=
    integrable_bourgainSourceShiftedPeriod (V j) (c j) (v j) T 0 hK
  have hiLS : Integrable (fun y : Fin 3 → ℝ => W y*LS y) := by
    simpa only [LS,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hiS j)
  have hiLV : Integrable (fun y : Fin 3 → ℝ => W y*LV y) := by
    simpa only [LV,Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => hiV j)
  have heLS : (∫ y : Fin 3 → ℝ, W y*LS y)=
      ∑ j, ∫ y : Fin 3 → ℝ, W y*bourgainSourceShiftedPeriod (S j) (z j) (w j) T y 0 := by
    simp only [LS,Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun j _ => hiS j)
  have heLV : (∫ y : Fin 3 → ℝ, W y*LV y)=
      ∑ j, ∫ y : Fin 3 → ℝ, W y*bourgainSourceShiftedPeriod (V j) (c j) (v j) T y 0 := by
    simp only [LV,Finset.mul_sum]
    exact integral_finsetSum Finset.univ (fun j _ => hiV j)
  have hentry := bourgainSource_radial_pair_period_entry (R:=R)
    (Finset.univ.sigma S) (Finset.univ.sigma V)
    (fun ji => z ji.1 ji.2) (fun ji => c ji.1 ji.2)
    (fun ji => m ji.1 ji.2) (fun ji => l ji.1 ji.2) hT hTK r q
  have hiJ : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => W p.1*W p.2*J p) := hentry.1
  have hiRight : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      E*((W p.1*LS p.1)*(W p.2*LV p.2))) := (hiLS.mul_prod hiLV).const_mul E
  have hmajor := integral_mono (hiJ.const_mul A) hiRight (fun p => by
    have hh := mul_le_mul_of_nonneg_left (hpoint p)
      (show 0≤W p.1*W p.2 by dsimp [W]; positivity)
    calc
      _ = (W p.1*W p.2)*(A*J p) := by ring
      _ ≤ (W p.1*W p.2)*(E*LS p.1*LV p.2) := hh
      _ = _ := by ring)
  rw [integral_const_mul,integral_const_mul] at hmajor
  have heProd := integral_prod_mul (μ:=volume) (ν:=volume)
    (fun y : Fin 3 → ℝ => W y*LS y) (fun y : Fin 3 → ℝ => W y*LV y)
  change (∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), (W p.1*LS p.1)*(W p.2*LV p.2)) =
    (∫ y : Fin 3 → ℝ, W y*LS y)*(∫ y : Fin 3 → ℝ, W y*LV y) at heProd
  rw [heProd,heLS,heLV,←mul_assoc] at hmajor
  calc
    _ ≤ A*((3*Real.pi*K)^2*(∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), W p.1*W p.2*J p)) :=
      mul_le_mul_of_nonneg_left hentry.2 (sq_nonneg _)
    _ = (3*Real.pi*K)^2*(A*(∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ), W p.1*W p.2*J p)) := by ring
    _ ≤ (3*Real.pi*K)^2*(E*
        (∑ j, ∫ y : Fin 3 → ℝ, W y*bourgainSourceShiftedPeriod (S j) (z j) (w j) T y 0)*
        (∑ j, ∫ y : Fin 3 → ℝ, W y*bourgainSourceShiftedPeriod (V j) (c j) (v j) T y 0)) :=
      mul_le_mul_of_nonneg_left hmajor (sq_nonneg _)
    _ = _ := by dsimp [E,W,w,v]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_dyadic_radial_cell_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      ∀ (b d r q ν : ℝ), b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
        |q|≤2*T → 0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
        ∀ (ι κ : Type u) (S : Fin (2^(j+2)) → Finset ι) (V : Fin (2^(j+2)) → Finset κ)
          (z : Fin (2^(j+2)) → ι → ℂ) (c : Fin (2^(j+2)) → κ → ℂ)
          (m : Fin (2^(j+2)) → ι → ℤ) (l : Fin (2^(j+2)) → κ → ℤ),
          (∀ k, ∀ i∈S k, (((m k i:ℝ)/T-b)/δ)∈Icc
            ((k:ℕ)/((2^(j+2):ℕ):ℝ)) (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ))) →
          (∀ k, ∀ i∈V k, (((l k i:ℝ)/T-d)/δ)∈Icc
            ((k:ℕ)/((2^(j+2):ℕ):ℝ)) (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ))) →
          (∫ x : Fin 2 → ℝ in Icc (fun _ => -(2*N^3)) (fun _ => 2*N^3),
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment (Finset.univ.sigma S) (fun ki => z ki.1 ki.2)
                (fun ki => (m ki.1 ki.2:ℝ)/T) (![r,x 0,x 1,q]+y))*
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment (Finset.univ.sigma V) (fun ki => c ki.1 ki.2)
                (fun ki => (l ki.1 ki.2:ℝ)/T) (![r,x 0,x 1,q]+y))) ≤
            (C/ν)*(2:ℝ)^(ε*j)*N^12*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod (S k) (z k) (fun i => (m k i:ℝ)/T) T y 0)*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod (V k) (c k) (fun i => (l k i:ℝ)/T) T y 0) := by
  obtain ⟨D,hD,hbound⟩ := exists_bourgainSource_radial_cell_refinement.{u} hε
  let C := D*(2:ℝ)^((ε+4)*2)*400*16^4/64
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro j hj
  let N := (2:ℝ)^(2*j)
  let T := N^2
  let δ := 2/N
  change ∀ (b d r q ν : ℝ), _ 
  intro b d r q ν hb hd hq hν hsep ι κ S V z c m l hs hv
  have hN : 0<N := by dsimp [N]; positivity
  have hscales := bourgain_anisotropic_dyadic_scales j hj
  change δ∈Ioc (0:ℝ) (1/16) ∧ 0<T ∧ 0≤2*N^3 ∧
    (2*N^3)*δ^3=16 ∧ (2*T)*δ^2=8 ∧ T*δ≤16*N ∧
    2*(2*N^3)*δ^2=16*N ∧ 3/(100*(16*N))≤(1/(2:ℝ)^(j+2))^2 ∧
    16*N=((2:ℝ)^(j+2))^2 ∧ (T*δ^3)^2=64/N^2 at hscales
  obtain ⟨hδ,hT,hR,hrem,hqscale,hTδ,hβ,hwidth,hP,hnormal⟩ := hscales
  have hq' : |q*δ^2|≤32 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg δ)]
    have hh := mul_le_mul_of_nonneg_right hq (sq_nonneg δ)
    rw [hqscale] at hh
    linarith
  have hh := hbound (j+2) b d δ T (2*N^3) r q ν (20*T) (16*N)
    hb hd hδ hT (by nlinarith) hR (by rw [hrem]; norm_num) hq' hν hsep
    hTδ hβ.le hwidth hP.le ι κ S V z c m l hs hv
  rw [hnormal] at hh
  have hNpow : N^2=(2:ℝ)^((4:ℝ)*j) := by
    dsimp [N]
    rw [←Real.rpow_natCast (2:ℝ) (2*j),←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  have hcoef : (2:ℝ)^((ε+4)*(j+2))=(2:ℝ)^((ε+4)*2)*(2:ℝ)^(ε*j)*N^2 := by
    rw [hNpow,←Real.rpow_add (by norm_num),←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcoef' : (D/ν)*(2:ℝ)^((ε+4)*(j+2))*(20*T)^2*(16*N)^4 =
      (64/N^2)*((C/ν)*(2:ℝ)^(ε*j)*N^12) := by
    rw [hcoef]
    dsimp [C,T]
    field_simp
    ring
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hh
  rw [hcoef'] at hh
  apply (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<64/N^2)).mp
  simpa only [mul_assoc] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainSourceShiftedPeriod_integer {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {T : ℝ}
    (hT : T≠0) (y : Fin 3 → ℝ) :
    bourgainSourceShiftedPeriod S z (fun i => (m i:ℝ)/T) T y 0 =
      ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S, z i*fordAdditiveCharacter
          ((m i:ℝ)*u+y 0*((m i:ℝ)/T)^2+
            y 1*((m i:ℝ)/T)^((3:ℝ)/2)+y 2*Real.sqrt ((m i:ℝ)/T))‖^6 := by
  unfold bourgainSourceShiftedPeriod
  rw [bourgainSourcePeriod_integer S _ m _ T (fun i _ => by field_simp)]
  apply integral_congr_ae
  filter_upwards with u
  apply congrArg (fun v : ℂ => ‖v‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  congr 2
  ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The actual weighted anisotropic coarse-cell refinement at the paper's
dyadic physical scales. Integer periods, quadratic refinement, kernel tails
and every scale condition are derived. Arbitrary coefficients, finite
multiplicities, closed cell endpoints and both unbounded shift phases are retained.
This is the coarse-cell estimate; the global first-spacing theorem is not claimed. -/
theorem exists_bourgainSourceCurve_anisotropic_cell_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      ∀ (b d r q ν : ℝ), b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
        |q|≤2*T → 0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
        ∀ (ι κ : Type u) (S : Fin (2^(j+2)) → Finset ι) (V : Fin (2^(j+2)) → Finset κ)
          (z : Fin (2^(j+2)) → ι → ℂ) (c : Fin (2^(j+2)) → κ → ℂ)
          (m : Fin (2^(j+2)) → ι → ℤ) (l : Fin (2^(j+2)) → κ → ℤ),
          (∀ k, ∀ i∈S k, (((m k i:ℝ)/T-b)/δ)∈Icc
            ((k:ℕ)/((2^(j+2):ℕ):ℝ)) (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ))) →
          (∀ k, ∀ i∈V k, (((l k i:ℝ)/T-d)/δ)∈Icc
            ((k:ℕ)/((2^(j+2):ℕ):ℝ)) (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ))) →
          (∫ x : Fin 2 → ℝ in Icc (fun _ => -(2*N^3)) (fun _ => 2*N^3),
            (∫ y : Fin 4 → ℝ, ((1+‖(20*T)⁻¹ • y‖)^100)⁻¹*
              ‖∑ ki∈Finset.univ.sigma S, z ki.1 ki.2*fordAdditiveCharacter
                ((r+y 0)*((m ki.1 ki.2:ℝ)/T)+(x 0+y 1)*((m ki.1 ki.2:ℝ)/T)^2+
                  (x 1+y 2)*((m ki.1 ki.2:ℝ)/T)^((3:ℝ)/2)+
                  (q+y 3)*Real.sqrt ((m ki.1 ki.2:ℝ)/T))‖^6)*
            (∫ y : Fin 4 → ℝ, ((1+‖(20*T)⁻¹ • y‖)^100)⁻¹*
              ‖∑ ki∈Finset.univ.sigma V, c ki.1 ki.2*fordAdditiveCharacter
                ((r+y 0)*((l ki.1 ki.2:ℝ)/T)+(x 0+y 1)*((l ki.1 ki.2:ℝ)/T)^2+
                  (x 1+y 2)*((l ki.1 ki.2:ℝ)/T)^((3:ℝ)/2)+
                  (q+y 3)*Real.sqrt ((l ki.1 ki.2:ℝ)/T))‖^6)) ≤
            (C/ν)*(2:ℝ)^(ε*j)*N^12*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                (∫ u : ℝ in Icc (0:ℝ) 1,
                  ‖∑ i∈S k, z k i*fordAdditiveCharacter
                    ((m k i:ℝ)*u+y 0*((m k i:ℝ)/T)^2+
                      y 1*((m k i:ℝ)/T)^((3:ℝ)/2)+y 2*Real.sqrt ((m k i:ℝ)/T))‖^6))*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                (∫ u : ℝ in Icc (0:ℝ) 1,
                  ‖∑ i∈V k, c k i*fordAdditiveCharacter
                    ((l k i:ℝ)*u+y 0*((l k i:ℝ)/T)^2+
                      y 1*((l k i:ℝ)/T)^((3:ℝ)/2)+y 2*Real.sqrt ((l k i:ℝ)/T))‖^6)) := by
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSource_dyadic_radial_cell_refinement.{u} hε
  refine ⟨C,hC,?_⟩
  intro j hj
  dsimp only
  intro b d r q ν hb hd hq hν hsep ι κ S V z c m l hs hv
  have hh := hbound j hj b d r q ν hb hd hq hν hsep ι κ S V z c m l hs hv
  have hT : (((2:ℝ)^(2*j))^2)≠0 := by positivity
  simp_rw [bourgainSourceShiftedPeriod_integer _ _ _ hT] at hh
  exact hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_rectangle_integral_coordinate {n : ℕ}
    (Q : Fin (n+1) → ℝ) (i : Fin (n+1))
    (f : (Fin (n+1) → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x in Icc (-Q) Q, f x) =
      ∫ r : ℝ in Icc (-Q i) (Q i),
        ∫ y : Fin n → ℝ in Icc (fun j => -Q (i.succAbove j)) (fun j => Q (i.succAbove j)),
          f (i.insertNth r y) := by
  let μ := fun j : Fin (n+1) => volume.restrict (Icc (-Q j) (Q j))
  have hmeasure {k : ℕ} (P : Fin k → ℝ) :
      volume.restrict (Icc (-P) P) =
        Measure.pi (fun j => volume.restrict (Icc (-P j) (P j))) := by
    rw [← Set.pi_univ_Icc]
    exact Measure.restrict_pi_pi (fun _ => volume) _
  have hi : Integrable f (Measure.pi μ) := by
    rw [←hmeasure Q]
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hmp := (measurePreserving_piFinSuccAbove μ i).symm
  have hi' := hmp.integrable_comp_of_integrable hi
  have he (p : ℝ × (Fin n → ℝ)) : e.symm p=i.insertNth p.1 p.2 := by
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Equiv.coe_fn_mk]
  have hint := hmp.integral_comp' f
  have hprod := integral_prod (fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) hi'
  rw [hmeasure Q]
  change (∫ x, f x ∂Measure.pi μ)=_
  rw [←hint,hprod]
  simp only [he,μ]
  rw [←hmeasure (fun j => Q (i.succAbove j))]
  rfl
end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_anisotropic_rectangle_integral
    (Q R : ℝ) (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x : Fin 4 → ℝ in Icc (-![Q,R,R,Q]) ![Q,R,R,Q], f x) =
      ∫ r : ℝ in Icc (-Q) Q, ∫ q : ℝ in Icc (-Q) Q,
        ∫ y : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
          f ![r,y 0,y 1,q] := by
  rw [bourgain_rectangle_integral_coordinate ![Q,R,R,Q] 0 f hf]
  simp only [Fin.insertNth_zero',Fin.zero_succAbove]
  apply integral_congr_ae
  filter_upwards with r
  have hc : Continuous (fun y : Fin 3 → ℝ => f (Fin.cons r y)) :=
    hf.comp (by fun_prop)
  have hh := bourgain_rectangle_integral_coordinate ![R,R,Q] (Fin.last 2)
    (fun y => f (Fin.cons r y)) hc
  have hQ : (fun j : Fin 2 => (![R,R,Q] : Fin 3 → ℝ) ((Fin.last 2).succAbove j)) =
      (fun _ => R) := by
    funext j
    fin_cases j <;> rfl
  have he (q : ℝ) (y : Fin 2 → ℝ) :
      Fin.cons r ((Fin.last 2).insertNth q y) = ![r,y 0,y 1,q] := by
    rw [Fin.insertNth_last']
    funext j
    fin_cases j <;> rfl
  change (∫ y : Fin 3 → ℝ in Icc (-![R,R,Q]) ![R,R,Q], f (Fin.cons r y)) =
    ∫ q : ℝ in Icc (-Q) Q,
      ∫ y : Fin 2 → ℝ in Icc
        (-(fun j => (![R,R,Q] : Fin 3 → ℝ) ((Fin.last 2).succAbove j)))
        (fun j => (![R,R,Q] : Fin 3 → ℝ) ((Fin.last 2).succAbove j)),
        f (Fin.cons r ((Fin.last 2).insertNth q y)) at hh
  simpa only [hQ,he] using hh

private theorem bourgain_anisotropic_rectangle_bound
    {Q R M : ℝ} (hQ : 0≤Q) (f : (Fin 4 → ℝ) → ℝ)
    (hf : Continuous f) (hn : ∀ x, 0≤f x)
    (hbound : ∀ r : ℝ, ∀ q∈Icc (-Q) Q,
      (∫ y : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
        f ![r,y 0,y 1,q])≤M) :
    (∫ x : Fin 4 → ℝ in Icc (-![Q,R,R,Q]) ![Q,R,R,Q], f x)≤(2*Q)^2*M := by
  rw [bourgain_anisotropic_rectangle_integral Q R f hf]
  have hinner (r : ℝ) (q : ℝ) :
      0≤∫ y : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
        f ![r,y 0,y 1,q] := integral_nonneg (fun _ => hn _)
  have hmiddle (r : ℝ) :
      ‖∫ q : ℝ in Icc (-Q) Q,
        ∫ y : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R), f ![r,y 0,y 1,q]‖≤M*(2*Q) := by
    have hh := norm_setIntegral_le_of_norm_le_const
      (μ:=volume) (s:=Icc (-Q) Q) isCompact_Icc.measure_lt_top
      (fun q hq => by rw [Real.norm_of_nonneg (hinner r q)]; exact hbound r q hq)
    simpa only [Real.volume_real_Icc_of_le (by linarith : -Q≤Q),sub_neg_eq_add,←two_mul] using hh
  have hh := norm_setIntegral_le_of_norm_le_const
    (μ:=volume) (s:=Icc (-Q) Q) isCompact_Icc.measure_lt_top (fun r _ => hmiddle r)
  have hlength : volume.real (Icc (-Q) Q)=2*Q := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hlength] at hh
  exact (le_abs_self _).trans (hh.trans_eq (by ring))

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_dyadic_radial_rectangle_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      ∀ (b d ν : ℝ), b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
        0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
        ∀ (ι κ : Type u) (S : Fin (2^(j+2)) → Finset ι) (V : Fin (2^(j+2)) → Finset κ)
          (z : Fin (2^(j+2)) → ι → ℂ) (c : Fin (2^(j+2)) → κ → ℂ)
          (m : Fin (2^(j+2)) → ι → ℤ) (l : Fin (2^(j+2)) → κ → ℤ),
          (∀ k, ∀ i∈S k, (((m k i:ℝ)/T-b)/δ)∈Icc
            ((k:ℕ)/((2^(j+2):ℕ):ℝ)) (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ))) →
          (∀ k, ∀ i∈V k, (((l k i:ℝ)/T-d)/δ)∈Icc
            ((k:ℕ)/((2^(j+2):ℕ):ℝ)) (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ))) →
          (∫ x : Fin 4 → ℝ in Icc (-![2*T,2*N^3,2*N^3,2*T]) ![2*T,2*N^3,2*N^3,2*T],
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment (Finset.univ.sigma S) (fun ki => z ki.1 ki.2)
                (fun ki => (m ki.1 ki.2:ℝ)/T) (x+y))*
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment (Finset.univ.sigma V) (fun ki => c ki.1 ki.2)
                (fun ki => (l ki.1 ki.2:ℝ)/T) (x+y))) ≤
            (C/ν)*(2:ℝ)^(ε*j)*N^16*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod (S k) (z k) (fun i => (m k i:ℝ)/T) T y 0)*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod (V k) (c k) (fun i => (l k i:ℝ)/T) T y 0) := by
  obtain ⟨D,hD,hbound⟩ := exists_bourgainSource_dyadic_radial_cell_refinement.{u} hε
  refine ⟨16*D,by positivity,?_⟩
  intro j hj
  let N := (2:ℝ)^(2*j)
  let T := N^2
  let δ := 2/N
  change ∀ (b d ν : ℝ), _
  intro b d ν hb hd hν hsep ι κ S V z c m l hs hv
  let FS := fun x : Fin 4 → ℝ => ∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
    bourgainSourceSixMoment (Finset.univ.sigma S) (fun ki => z ki.1 ki.2)
      (fun ki => (m ki.1 ki.2:ℝ)/T) (x+y)
  let FV := fun x : Fin 4 → ℝ => ∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
    bourgainSourceSixMoment (Finset.univ.sigma V) (fun ki => c ki.1 ki.2)
      (fun ki => (l ki.1 ki.2:ℝ)/T) (x+y)
  have hK : 0<20*T := by dsimp [T,N]; positivity
  have hFS : Continuous FS := continuous_bourgainSource_radial_average
    (Finset.univ.sigma S) (fun ki => z ki.1 ki.2) (fun ki => (m ki.1 ki.2:ℝ)/T) hK
  have hFV : Continuous FV := continuous_bourgainSource_radial_average
    (Finset.univ.sigma V) (fun ki => c ki.1 ki.2) (fun ki => (l ki.1 ki.2:ℝ)/T) hK
  have hn (x : Fin 4 → ℝ) : 0≤FS x*FV x := by
    apply mul_nonneg
    · exact integral_nonneg (fun y => mul_nonneg (by dsimp [bourgainRadialWeight]; positivity)
        (bourgainSourceSixMoment_nonneg _ _ _ _))
    · exact integral_nonneg (fun y => mul_nonneg (by dsimp [bourgainRadialWeight]; positivity)
        (bourgainSourceSixMoment_nonneg _ _ _ _))
  have hh := bourgain_anisotropic_rectangle_bound (Q:=2*T) (R:=2*N^3)
    (by dsimp [T,N]; positivity) (fun x => FS x*FV x) (hFS.mul hFV) hn
    (fun r q hq => hbound j hj b d r q ν hb hd (abs_le.mpr hq)
      hν hsep ι κ S V z c m l hs hv)
  dsimp only [FS,FV] at hh
  exact hh.trans_eq (by dsimp [T]; ring)

end TaoTrudgianYang2025

noncomputable section
open Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private def bourgainClosedFineCell (n : ℕ) (x : ℝ) : Fin (2^n) :=
  ⟨min ⌊((2^n:ℕ):ℝ)*x⌋₊ (2^n-1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by decide))⟩

private theorem bourgainClosedFineCell_mem (n : ℕ) {x : ℝ}
    (hx : x∈Icc (0:ℝ) 1) :
    x∈Icc (((bourgainClosedFineCell n x:ℕ):ℝ)/((2^n:ℕ):ℝ))
      ((((bourgainClosedFineCell n x:ℕ):ℝ)+1)/((2^n:ℕ):ℝ)) := by
  let M := 2^n
  have hM : 0<M := by dsimp [M]; positivity
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hlo := Nat.floor_le (mul_nonneg hMr.le hx.1)
  have hmin : ((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)≤⌊(M:ℝ)*x⌋₊ := by
    exact_mod_cast min_le_left ⌊(M:ℝ)*x⌋₊ (M-1)
  change x∈Icc (((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)/M)
    ((((min ⌊(M:ℝ)*x⌋₊ (M-1):ℕ):ℝ)+1)/M)
  constructor
  · apply (div_le_iff₀ hMr).mpr
    nlinarith [hmin.trans hlo]
  · apply (le_div_iff₀ hMr).mpr
    by_cases hc : ⌊(M:ℝ)*x⌋₊≤M-1
    · rw [min_eq_left hc]
      have hh := Nat.lt_floor_add_one ((M:ℝ)*x)
      linarith
    · rw [min_eq_right (le_of_not_ge hc)]
      have hm : M-1+1=M := Nat.sub_add_cancel hM
      have hm' : ((M-1:ℕ):ℝ)+1=M := by exact_mod_cast hm
      rw [hm']
      nlinarith [hx.2]

private theorem bourgain_fine_cell_sum {ι : Type*} (S : Finset ι)
    (n : ℕ) (g : ι → Fin (2^n)) (F : ι → ℂ) :
    (∑ j : Fin (2^n), ∑ i∈S.filter (fun i => g i=j), F i)=∑ i∈S,F i :=
  Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) F

end TaoTrudgianYang2025

noncomputable section
open Set
namespace TaoTrudgianYang2025

private theorem bourgain_root_cell_original_coordinate {N : ℕ} (hN : 0<N)
    (i : Fin N) {w : ℝ} (hw : 0≤w)
    (hs : Real.sqrt w∈Icc ((i:ℕ)/(N:ℝ)) (((i:ℕ)+1)/(N:ℝ))) :
    (w-((i:ℕ)/(N:ℝ))^2)/(2/(N:ℝ))∈Icc (0:ℝ) 1 := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hi : ((i:ℕ):ℝ)+1≤N := by exact_mod_cast i.isLt
  have ha : (0:ℝ)≤(i:ℕ)/(N:ℝ) := by positivity
  have hb : (0:ℝ)≤((i:ℕ)+1)/(N:ℝ) := by positivity
  have hsqrt := Real.sq_sqrt hw
  have hlo : ((i:ℕ)/(N:ℝ))^2≤w := by nlinarith [hs.1,Real.sqrt_nonneg w]
  have hup : w≤(((i:ℕ)+1)/(N:ℝ))^2 := by nlinarith [hs.2,Real.sqrt_nonneg w]
  have hwidth : (((i:ℕ)+1)/(N:ℝ))^2≤((i:ℕ)/(N:ℝ))^2+2/(N:ℝ) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hNr)).mp
    field_simp
    nlinarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlo) (by positivity)
  · apply (div_le_one (by positivity : (0:ℝ)<2/(N:ℝ))).mpr
    linarith

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

private theorem bourgainSourceSixMoment_fine_fibers {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (n : ℕ)
    (g : ι → Fin (2^n)) (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment (Finset.univ.sigma (fun k => S.filter (fun i => g i=k)))
      (fun ki => z ki.2) (fun ki => w ki.2) x =
        bourgainSourceSixMoment S z w x := by
  unfold bourgainSourceSixMoment
  congr 2
  rw [Finset.sum_sigma]
  exact bourgain_fine_cell_sum S n g (fun i => z i*fordAdditiveCharacter
    (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i)))

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_dyadic_radial_fiber_refinement {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      ∀ (b d ν : ℝ), b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
        0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
        ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
          (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (l : κ → ℤ),
          (∀ i∈S, (((m i:ℝ)/T-b)/δ)∈Icc (0:ℝ) 1) →
          (∀ i∈V, (((l i:ℝ)/T-d)/δ)∈Icc (0:ℝ) 1) →
          (∫ x : Fin 4 → ℝ in Icc (-![2*T,2*N^3,2*N^3,2*T]) ![2*T,2*N^3,2*N^3,2*T],
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment S z (fun i => (m i:ℝ)/T) (x+y))*
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment V c (fun i => (l i:ℝ)/T) (x+y))) ≤
            (C/ν)*(2:ℝ)^(ε*j)*N^16*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod
                  (S.filter (fun i => bourgainClosedFineCell (j+2) (((m i:ℝ)/T-b)/δ)=k))
                  z (fun i => (m i:ℝ)/T) T y 0)*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod
                  (V.filter (fun i => bourgainClosedFineCell (j+2) (((l i:ℝ)/T-d)/δ)=k))
                  c (fun i => (l i:ℝ)/T) T y 0) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSource_dyadic_radial_rectangle_refinement.{u} hε
  refine ⟨C,hC,?_⟩
  intro j hj
  dsimp only
  intro b d ν hb hd hν hsep ι κ S V z c m l hs hv
  let T := ((2:ℝ)^(2*j))^2
  let δ := 2/(2:ℝ)^(2*j)
  let g := fun i => bourgainClosedFineCell (j+2) (((m i:ℝ)/T-b)/δ)
  let h := fun i => bourgainClosedFineCell (j+2) (((l i:ℝ)/T-d)/δ)
  have hS (k : Fin (2^(j+2))) (i : ι) (hi : i∈S.filter (fun i => g i=k)) :
      (((m i:ℝ)/T-b)/δ)∈Icc ((k:ℕ)/((2^(j+2):ℕ):ℝ))
        (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ)) := by
    obtain ⟨hi,hki⟩ := Finset.mem_filter.mp hi
    have hh := bourgainClosedFineCell_mem (j+2) (hs i hi)
    change (((m i:ℝ)/T-b)/δ)∈Icc (((g i:ℕ):ℝ)/((2^(j+2):ℕ):ℝ))
      ((((g i:ℕ):ℝ)+1)/((2^(j+2):ℕ):ℝ)) at hh
    rwa [hki] at hh
  have hV (k : Fin (2^(j+2))) (i : κ) (hi : i∈V.filter (fun i => h i=k)) :
      (((l i:ℝ)/T-d)/δ)∈Icc ((k:ℕ)/((2^(j+2):ℕ):ℝ))
        (((k:ℕ)+1)/((2^(j+2):ℕ):ℝ)) := by
    obtain ⟨hi,hki⟩ := Finset.mem_filter.mp hi
    have hh := bourgainClosedFineCell_mem (j+2) (hv i hi)
    change (((l i:ℝ)/T-d)/δ)∈Icc (((h i:ℕ):ℝ)/((2^(j+2):ℕ):ℝ))
      ((((h i:ℕ):ℝ)+1)/((2^(j+2):ℕ):ℝ)) at hh
    rwa [hki] at hh
  have hh := hbound j hj b d ν hb hd hν hsep ι κ
    (fun k => S.filter (fun i => g i=k)) (fun k => V.filter (fun i => h i=k))
    (fun _ => z) (fun _ => c) (fun _ => m) (fun _ => l) hS hV
  have heS := bourgainSourceSixMoment_fine_fibers S z (fun i => (m i:ℝ)/T) (j+2) g
  have heV := bourgainSourceSixMoment_fine_fibers V c (fun i => (l i:ℝ)/T) (j+2) h
  dsimp only [T] at heS heV
  simp_rw [heS,heV] at hh
  exact hh

end TaoTrudgianYang2025

noncomputable section
open Set
namespace TaoTrudgianYang2025

private theorem bourgain_root_cell_base {N : ℕ} (hN : 0<N)
    (i : Fin N) (hi : N≤2*(i:ℕ)) :
    ((i:ℕ)/(N:ℝ))^2∈Icc (1/4:ℝ) 1 ∧
      Real.sqrt (((i:ℕ)/(N:ℝ))^2)=(i:ℕ)/(N:ℝ) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hi' : (N:ℝ)≤2*(i:ℕ) := by exact_mod_cast hi
  have hit : ((i:ℕ):ℝ)<N := by exact_mod_cast i.isLt
  have ha : (0:ℝ)≤(i:ℕ)/(N:ℝ) := by positivity
  have hlo : (1/2:ℝ)≤(i:ℕ)/(N:ℝ) := by
    apply (le_div_iff₀ hNr).mpr
    linarith
  have hup : (i:ℕ)/(N:ℝ)≤(1:ℝ) := (div_le_one hNr).mpr hit.le
  refine ⟨⟨by nlinarith,by nlinarith⟩,Real.sqrt_sq ha⟩

private theorem bourgain_root_grid_center_separation {N : ℕ} (hN : 0<N)
    {ν : ℝ} (hν : 0<ν) (hscale : 1/(N:ℝ)≤ν/2)
    (i k : Fin N) {u v : ℝ}
    (hu : u∈Icc ((i:ℕ)/(N:ℝ)) (((i:ℕ)+1)/(N:ℝ)))
    (hv : v∈Icc ((k:ℕ)/(N:ℝ)) (((k:ℕ)+1)/(N:ℝ)))
    (hsep : ν≤|u-v|) :
    ν/2≤|Real.sqrt (((i:ℕ)/(N:ℝ))^2)-Real.sqrt (((k:ℕ)/(N:ℝ))^2)| := by
  have hi : (0:ℝ)≤(i:ℕ)/(N:ℝ) := by positivity
  have hk : (0:ℝ)≤(k:ℕ)/(N:ℝ) := by positivity
  rw [Real.sqrt_sq hi,Real.sqrt_sq hk,abs_sub_comm]
  have hui : u∈Icc ((i:ℕ)/(N:ℝ)) ((i:ℕ)/(N:ℝ)+1/(N:ℝ)) := by
    refine ⟨hu.1,hu.2.trans_eq ?_⟩
    ring
  have hvk : v∈Icc ((k:ℕ)/(N:ℝ)) ((k:ℕ)/(N:ℝ)+1/(N:ℝ)) := by
    refine ⟨hv.1,hv.2.trans_eq ?_⟩
    ring
  exact (bourgain_coarse_center_separation hν hscale hui hvk hsep).1

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_root_cell_rectangle {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      ∀ (ν : ℝ), 0<ν → 1/N≤ν/2 →
        ∀ (i k : Fin (2^(2*j))),
          let b := ((i:ℕ)/N)^2
          let d := ((k:ℕ)/N)^2
        ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
          (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (l : κ → ℤ),
          (S.Nonempty → 2^(2*j)≤2*(i:ℕ)) →
          (V.Nonempty → 2^(2*j)≤2*(k:ℕ)) →
          (∀ a∈S, 0≤(m a:ℝ)/T) → (∀ a∈V, 0≤(l a:ℝ)/T) →
          (∀ a∈S, Real.sqrt ((m a:ℝ)/T)∈Icc ((i:ℕ)/N) (((i:ℕ)+1)/N)) →
          (∀ a∈V, Real.sqrt ((l a:ℝ)/T)∈Icc ((k:ℕ)/N) (((k:ℕ)+1)/N)) →
          (∀ a∈S, ∀ a'∈V, ν≤|Real.sqrt ((m a:ℝ)/T)-Real.sqrt ((l a':ℝ)/T)|) →
          (∫ x : Fin 4 → ℝ in Icc (-![2*T,N^3+T,N^3+T,2*T]) ![2*T,N^3+T,N^3+T,2*T],
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment S z (fun i => (m i:ℝ)/T) (x+y))*
            (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
              bourgainSourceSixMoment V c (fun i => (l i:ℝ)/T) (x+y))) ≤
            (C/ν)*(2:ℝ)^(ε*j)*N^16*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod
                  (S.filter (fun i => bourgainClosedFineCell (j+2) (((m i:ℝ)/T-b)/δ)=k))
                  z (fun i => (m i:ℝ)/T) T y 0)*
              (∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
                bourgainSourceShiftedPeriod
                  (V.filter (fun i => bourgainClosedFineCell (j+2) (((l i:ℝ)/T-d)/δ)=k))
                  c (fun i => (l i:ℝ)/T) T y 0) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSource_dyadic_radial_fiber_refinement.{u} hε
  refine ⟨2*C,by positivity,?_⟩
  intro j hj
  dsimp only
  intro ν hν hscale i k ι κ S V z c m l hhalfS hhalfV hw hv hs ht hsep
  let N := (2:ℝ)^(2*j)
  let T := N^2
  let δ := 2/N
  let b := ((i:ℕ)/N)^2
  let d := ((k:ℕ)/N)^2
  have hN : 0<N := by dsimp [N]; positivity
  have hNnat : 0<2^(2*j) := by positivity
  by_cases hS : S.Nonempty
  · by_cases hV : V.Nonempty
    · have hb : b∈Icc (1/4:ℝ) 1 := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using
          (bourgain_root_cell_base hNnat i (hhalfS hS)).1
      have hd : d∈Icc (1/4:ℝ) 1 := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using
          (bourgain_root_cell_base hNnat k (hhalfV hV)).1
      obtain ⟨a,ha⟩ := hS
      obtain ⟨a',ha'⟩ := hV
      have hcent : ν/2≤|Real.sqrt b-Real.sqrt d| := by
        have hh := bourgain_root_grid_center_separation hNnat hν
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hscale) i k
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hs a ha)
          (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht a' ha')
          (hsep a ha a' ha')
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
      have hcoordS (a : ι) (ha : a∈S) :
          (((m a:ℝ)/T-b)/δ)∈Icc (0:ℝ) 1 := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using
          bourgain_root_cell_original_coordinate hNnat i (hw a ha)
            (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hs a ha)
      have hcoordV (a : κ) (ha : a∈V) :
          (((l a:ℝ)/T-d)/δ)∈Icc (0:ℝ) 1 := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using
          bourgain_root_cell_original_coordinate hNnat k (hv a ha)
            (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht a ha)
      have hh := hbound j hj b d (ν/2) hb hd (by positivity) hcent
        ι κ S V z c m l hcoordS hcoordV
      let F := fun x : Fin 4 → ℝ =>
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
          bourgainSourceSixMoment S z (fun a => (m a:ℝ)/T) (x+y))*
        (∫ y : Fin 4 → ℝ, bourgainRadialWeight (20*T) y*
          bourgainSourceSixMoment V c (fun a => (l a:ℝ)/T) (x+y))
      have hK : 0<20*T := by dsimp [T]; positivity
      have hFc : Continuous F :=
        (continuous_bourgainSource_radial_average S z _ hK).mul
          (continuous_bourgainSource_radial_average V c _ hK)
      have hF₀ (x : Fin 4 → ℝ) : 0≤F x := by
        apply mul_nonneg <;> apply integral_nonneg
        · intro y
          exact mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)
        · intro y
          exact mul_nonneg (bourgainRadialWeight_nonneg _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)
      have hN₁ : 1≤N := one_le_pow₀ (by norm_num) 
      have hNT : T≤N^3 := by dsimp [T]; nlinarith [sq_nonneg N]
      have hbox : (![2*T,N^3+T,N^3+T,2*T] : Fin 4 → ℝ) ≤
          ![2*T,2*N^3,2*N^3,2*T] := by
        intro t
        fin_cases t
        · change 2*T≤2*T
          exact le_rfl
        · change N^3+T≤2*N^3
          linarith
        · change N^3+T≤2*N^3
          linarith
        · change 2*T≤2*T
          exact le_rfl
      have hsub : Icc (-![2*T,N^3+T,N^3+T,2*T]) ![2*T,N^3+T,N^3+T,2*T] ⊆
          Icc (-![2*T,2*N^3,2*N^3,2*T]) ![2*T,2*N^3,2*N^3,2*T] :=
        Set.Icc_subset_Icc (neg_le_neg hbox) hbox
      have hm := setIntegral_mono_set (μ:=volume)
        (hFc.continuousOn.integrableOn_compact isCompact_Icc)
        (Filter.Eventually.of_forall hF₀)
        (Filter.Eventually.of_forall (fun x hx => hsub hx))
      exact (hm.trans hh).trans_eq (by ring)
    · have he : V=∅ := Finset.not_nonempty_iff_eq_empty.mp hV
      subst V
      simp [bourgainSourceSixMoment,bourgainSourceShiftedPeriod,bourgainSourcePeriod]
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [bourgainSourceSixMoment,bourgainSourceShiftedPeriod,bourgainSourcePeriod]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_small_anisotropic_refinement
    {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      1/N≤ν/2 →
      ∀ (ι κ : Type u) (S : Fin (2^(2*j)) → Finset ι) (V : Fin (2^(2*j)) → Finset κ)
        (z : Fin (2^(2*j)) → ι → ℂ) (c : Fin (2^(2*j)) → κ → ℂ)
        (m : Fin (2^(2*j)) → ι → ℤ) (l : Fin (2^(2*j)) → κ → ℤ),
        (∀ i, (S i).Nonempty → 2^(2*j)≤2*(i:ℕ)) →
        (∀ i, (V i).Nonempty → 2^(2*j)≤2*(i:ℕ)) →
        (∀ i, ∀ a∈S i, 0≤(m i a:ℝ)/T) →
        (∀ i, ∀ a∈V i, 0≤(l i a:ℝ)/T) →
        (∀ i, ∀ a∈S i, Real.sqrt ((m i a:ℝ)/T)∈Icc ((i:ℕ)/N) (((i:ℕ)+1)/N)) →
        (∀ i, ∀ a∈V i, Real.sqrt ((l i a:ℝ)/T)∈Icc ((i:ℕ)/N) (((i:ℕ)+1)/N)) →
        (∀ i k, ∀ a∈S i, ∀ a'∈V k,
          ν≤|Real.sqrt ((m i a:ℝ)/T)-Real.sqrt ((l k a':ℝ)/T)|) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,N^3,N^3,T]) ![T,N^3,N^3,T],
          bourgainSourceSixMoment (Finset.univ.sigma S) (fun ia => z ia.1 ia.2)
            (fun ia => (m ia.1 ia.2:ℝ)/T) x*
          bourgainSourceSixMoment (Finset.univ.sigma V) (fun ia => c ia.1 ia.2)
            (fun ia => (l ia.1 ia.2:ℝ)/T) x) ≤
          C*(2:ℝ)^(ε*j)*N^4*
          (∑ i, ∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
            bourgainSourceShiftedPeriod
              ((S i).filter (fun a => bourgainClosedFineCell (j+2)
                ((((m i a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k))
              (z i) (fun a => (m i a:ℝ)/T) T y 0)*
          (∑ i, ∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
            bourgainSourceShiftedPeriod
              ((V i).filter (fun a => bourgainClosedFineCell (j+2)
                ((((l i a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k))
              (c i) (fun a => (l i a:ℝ)/T) T y 0) := by
  classical
  obtain ⟨D,hD,hglobal⟩ := exists_bourgainSourceCurve_rectangle_entry.{u}
    (show 0<ε/4 by positivity) hν
  obtain ⟨E,hE,hcell⟩ := exists_bourgainSource_root_cell_rectangle.{u}
    (show 0<ε/2 by positivity)
  let C := D*E/(16*ν)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro j hj
  dsimp only
  intro hscale ι κ S V z c m l hhalfS hhalfV hw hv hs ht hsep
  let N := (2:ℝ)^(2*j)
  let T := N^2
  let δ := 2/N
  let Q : Fin 4 → ℝ := ![T,N^3,N^3,T]
  let LS := fun i : Fin (2^(2*j)) => ∑ k, ∫ y : Fin 3 → ℝ,
    (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
      bourgainSourceShiftedPeriod
        ((S i).filter (fun a => bourgainClosedFineCell (j+2)
          ((((m i a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k))
        (z i) (fun a => (m i a:ℝ)/T) T y 0
  let LV := fun i : Fin (2^(2*j)) => ∑ k, ∫ y : Fin 3 → ℝ,
    (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
      bourgainSourceShiftedPeriod
        ((V i).filter (fun a => bourgainClosedFineCell (j+2)
          ((((l i a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k))
        (c i) (fun a => (l i a:ℝ)/T) T y 0
  have hN : 0<N := by dsimp [N]; positivity
  have hpoint (i k : Fin (2^(2*j))) :
      (∫ q : Fin 4 → ℝ in Icc (fun t => -(Q t+T)) (fun t => Q t+T),
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*T) x*
          bourgainSourceSixMoment (S i) (z i) (fun a => (m i a:ℝ)/T) (q+x))*
        (∫ x : Fin 4 → ℝ, bourgainRadialWeight (20*T) x*
          bourgainSourceSixMoment (V k) (c k) (fun a => (l k a:ℝ)/T) (q+x))) ≤
        (E/ν)*(2:ℝ)^((ε/2)*j)*N^16*LS i*LV k := by
    have hh := hcell j hj ν hν hscale i k ι κ (S i) (V k) (z i) (c k) (m i) (l k)
      (hhalfS i) (hhalfV k) (hw i) (hv k) (hs i) (ht k) (hsep i k)
    have hQ : (fun t => Q t+T)=![2*T,N^3+T,N^3+T,2*T] := by
      funext t
      fin_cases t
      · change T+T=2*T
        ring
      · rfl
      · rfl
      · change T+T=2*T
        ring
    have hneg : (fun t => -(Q t+T))= -![2*T,N^3+T,N^3+T,2*T] :=
      congrArg Neg.neg hQ
    rw [hQ,hneg]
    exact hh
  have hh := hglobal (2*j) Q ι κ S V z c (fun i a => (m i a:ℝ)/T)
    (fun i a => (l i a:ℝ)/T) hw hv
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hs)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using ht) hsep
  have hsum := Finset.sum_le_sum (fun i (_hi : i∈(Finset.univ : Finset (Fin (2^(2*j))))) =>
    Finset.sum_le_sum (fun k (_hk : k∈(Finset.univ : Finset (Fin (2^(2*j))))) => hpoint i k))
  have hmajor := mul_le_mul_of_nonneg_left hsum
    (by positivity : 0≤D*(2:ℝ)^((ε/4)*(2*j))/T^2)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at hh
  have hfull := hh.trans hmajor
  have hfactor : (∑ i, ∑ k, (E/ν)*(2:ℝ)^((ε/2)*j)*N^16*LS i*LV k)=
      (E/ν)*(2:ℝ)^((ε/2)*j)*N^16*(∑ i,LS i)*(∑ k,LV k) := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hfactor] at hfull
  have hexp : (2:ℝ)^((ε/4)*(2*j))*(2:ℝ)^((ε/2)*j)=(2:ℝ)^(ε*j) := by
    rw [←Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hcoef : D*(2:ℝ)^((ε/4)*(2*j))/T^2*
      ((E/ν)*(2:ℝ)^((ε/2)*j)*N^16*(∑ i,LS i)*(∑ k,LV k)) =
      (2*T)^4*(C*(2:ℝ)^(ε*j)*N^4*(∑ i,LS i)*(∑ k,LV k)) := by
    calc
      _ = D*E/ν/T^2*
          ((2:ℝ)^((ε/4)*(2*j))*(2:ℝ)^((ε/2)*j))*N^16*(∑ i,LS i)*(∑ k,LV k) := by ring
      _ = _ := by rw [hexp]; dsimp [C,T]; field_simp; ring
  rw [hcoef] at hfull
  exact (mul_le_mul_iff_right₀ (by positivity : (0:ℝ)<(2*T)^4)).mp hfull

end TaoTrudgianYang2025

noncomputable section
open Set
namespace TaoTrudgianYang2025

private theorem bourgainClosedFineCell_half {n : ℕ} (hn : 1≤n)
    {x : ℝ} (hx : (1/2:ℝ)≤x) :
    2^n≤2*(bourgainClosedFineCell n x:ℕ) := by
  let K := 2^(n-1)
  have hK : 0<K := by dsimp [K]; positivity
  have hM : 2^n=2*K := by
    calc
      2^n=2^(n-1+1) := by congr 1; omega
      _ = 2*K := by rw [pow_succ]; dsimp [K]; omega
  have hMr : ((2^n:ℕ):ℝ)=2*(K:ℝ) := by exact_mod_cast hM
  have hfloor : K≤⌊((2^n:ℕ):ℝ)*x⌋₊ := by
    apply Nat.le_floor
    rw [hMr]
    have hK₀ : (0:ℝ)≤K := Nat.cast_nonneg K
    nlinarith
  have hlast : K≤2^n-1 := by omega
  have hm := le_min hfloor hlast
  change 2^n≤2*min ⌊((2^n:ℕ):ℝ)*x⌋₊ (2^n-1)
  omega

private theorem bourgainClosedFineCell_sqrt_half {n : ℕ} (hn : 1≤n)
    {w : ℝ} (hw : (1/4:ℝ)≤w) :
    2^n≤2*(bourgainClosedFineCell n (Real.sqrt w):ℕ) := by
  apply bourgainClosedFineCell_half hn
  apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
  nlinarith

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_small_anisotropic_original
    {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      1/N≤ν/2 →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (l : κ → ℤ),
        (∀ a∈S, (m a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈V, (l a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈S, ∀ a'∈V, ν≤|Real.sqrt ((m a:ℝ)/T)-Real.sqrt ((l a':ℝ)/T)|) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,N^3,N^3,T]) ![T,N^3,N^3,T],
          bourgainSourceSixMoment S z (fun a => (m a:ℝ)/T) x*
          bourgainSourceSixMoment V c (fun a => (l a:ℝ)/T) x) ≤
          C*(2:ℝ)^(ε*j)*N^4*
          (∑ i : Fin (2^(2*j)), ∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
            bourgainSourceShiftedPeriod
              ((S.filter (fun a => bourgainClosedFineCell (2*j) (Real.sqrt ((m a:ℝ)/T))=i)).filter (fun a => bourgainClosedFineCell (j+2)
                ((((m a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k))
              z (fun a => (m a:ℝ)/T) T y 0)*
          (∑ i : Fin (2^(2*j)), ∑ k, ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
            bourgainSourceShiftedPeriod
              ((V.filter (fun a => bourgainClosedFineCell (2*j) (Real.sqrt ((l a:ℝ)/T))=i)).filter (fun a => bourgainClosedFineCell (j+2)
                ((((l a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k))
              c (fun a => (l a:ℝ)/T) T y 0) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSource_small_anisotropic_refinement.{u} hε hν
  refine ⟨C,hC,?_⟩
  intro j hj
  dsimp only
  intro hscale ι κ S V z c m l hw hv hsep
  let N := (2:ℝ)^(2*j)
  let T := N^2
  let g := fun a => bourgainClosedFineCell (2*j) (Real.sqrt ((m a:ℝ)/T))
  let h := fun a => bourgainClosedFineCell (2*j) (Real.sqrt ((l a:ℝ)/T))
  let U := fun i => S.filter (fun a => g a=i)
  let W := fun i => V.filter (fun a => h a=i)
  have hhalfS (i : Fin (2^(2*j))) (hi : (U i).Nonempty) : 2^(2*j)≤2*(i:ℕ) := by
    obtain ⟨a,ha⟩ := hi
    obtain ⟨ha,hga⟩ := Finset.mem_filter.mp ha
    have hh := bourgainClosedFineCell_sqrt_half (by omega : 1≤2*j) (hw a ha).1
    change 2^(2*j)≤2*(g a:ℕ) at hh
    rwa [hga] at hh
  have hhalfV (i : Fin (2^(2*j))) (hi : (W i).Nonempty) : 2^(2*j)≤2*(i:ℕ) := by
    obtain ⟨a,ha⟩ := hi
    obtain ⟨ha,hga⟩ := Finset.mem_filter.mp ha
    have hh := bourgainClosedFineCell_sqrt_half (by omega : 1≤2*j) (hv a ha).1
    change 2^(2*j)≤2*(h a:ℕ) at hh
    rwa [hga] at hh
  have hS (i : Fin (2^(2*j))) (a : ι) (ha : a∈U i) :
      Real.sqrt ((m a:ℝ)/T)∈Icc ((i:ℕ)/N) (((i:ℕ)+1)/N) := by
    obtain ⟨ha,hga⟩ := Finset.mem_filter.mp ha
    have hh := bourgainClosedFineCell_mem (2*j)
      (show Real.sqrt ((m a:ℝ)/T)∈Icc (0:ℝ) 1 from
        ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (hw a ha).2⟩)
    change _∈Icc (((g a:ℕ):ℝ)/((2^(2*j):ℕ):ℝ))
      ((((g a:ℕ):ℝ)+1)/((2^(2*j):ℕ):ℝ)) at hh
    rw [hga] at hh
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hV (i : Fin (2^(2*j))) (a : κ) (ha : a∈W i) :
      Real.sqrt ((l a:ℝ)/T)∈Icc ((i:ℕ)/N) (((i:ℕ)+1)/N) := by
    obtain ⟨ha,hga⟩ := Finset.mem_filter.mp ha
    have hh := bourgainClosedFineCell_mem (2*j)
      (show Real.sqrt ((l a:ℝ)/T)∈Icc (0:ℝ) 1 from
        ⟨Real.sqrt_nonneg _,Real.sqrt_le_one.mpr (hv a ha).2⟩)
    change _∈Icc (((h a:ℕ):ℝ)/((2^(2*j):ℕ):ℝ))
      ((((h a:ℕ):ℝ)+1)/((2^(2*j):ℕ):ℝ)) at hh
    rw [hga] at hh
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  have hw₀ (i : Fin (2^(2*j))) (a : ι) (ha : a∈U i) : 0≤(m a:ℝ)/T :=
    (by norm_num : (0:ℝ)≤1/4).trans (hw a (Finset.mem_filter.mp ha).1).1
  have hv₀ (i : Fin (2^(2*j))) (a : κ) (ha : a∈W i) : 0≤(l a:ℝ)/T :=
    (by norm_num : (0:ℝ)≤1/4).trans (hv a (Finset.mem_filter.mp ha).1).1
  have hh := hbound j hj hscale ι κ U W (fun _ => z) (fun _ => c)
    (fun _ => m) (fun _ => l) hhalfS hhalfV hw₀ hv₀ hS hV
    (fun i k a ha a' ha' => hsep a (Finset.mem_filter.mp ha).1 a' (Finset.mem_filter.mp ha').1)
  have heS := bourgainSourceSixMoment_fine_fibers S z (fun a => (m a:ℝ)/T) (2*j) g
  have heV := bourgainSourceSixMoment_fine_fibers V c (fun a => (l a:ℝ)/T) (2*j) h
  dsimp only [T,N] at heS heV
  dsimp only [U,W] at hh
  simp_rw [heS,heV] at hh
  exact hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The actual small-anisotropic bilinear source refinement. Both closed-grid
partitions and active coarse-cell conditions are constructed from the original
integer frequencies. The weighted fine periods retain every phase, coefficient
and indexed multiplicity. This is not the larger-domain first-spacing theorem. -/
theorem exists_bourgainSourceCurve_small_anisotropic_refinement
    {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      1/N≤ν/2 →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (l : κ → ℤ),
        (∀ a∈S, (m a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈V, (l a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈S, ∀ a'∈V, ν≤|Real.sqrt ((m a:ℝ)/T)-Real.sqrt ((l a':ℝ)/T)|) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,N^3,N^3,T]) ![T,N^3,N^3,T],
          ‖∑ a∈S, z a*fordAdditiveCharacter
            (x 0*((m a:ℝ)/T)+x 1*((m a:ℝ)/T)^2+
              x 2*((m a:ℝ)/T)^((3:ℝ)/2)+x 3*Real.sqrt ((m a:ℝ)/T))‖^6*
          ‖∑ a∈V, c a*fordAdditiveCharacter
            (x 0*((l a:ℝ)/T)+x 1*((l a:ℝ)/T)^2+
              x 2*((l a:ℝ)/T)^((3:ℝ)/2)+x 3*Real.sqrt ((l a:ℝ)/T))‖^6) ≤
          C*(2:ℝ)^(ε*j)*N^4*
          (∑ i : Fin (2^(2*j)), ∑ k : Fin (2^(j+2)),
            ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
              (∫ u : ℝ in Icc (0:ℝ) 1,
                ‖∑ a∈((S.filter (fun a =>
                    min ⌊N*Real.sqrt ((m a:ℝ)/T)⌋₊ (2^(2*j)-1)=(i:ℕ))).filter
                  (fun a => min ⌊((2^(j+2):ℕ):ℝ)*
                    ((((m a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)⌋₊ (2^(j+2)-1)=(k:ℕ))),
                  z a*fordAdditiveCharacter ((m a:ℝ)*u+
                    y 0*((m a:ℝ)/T)^2+y 1*((m a:ℝ)/T)^((3:ℝ)/2)+
                    y 2*Real.sqrt ((m a:ℝ)/T))‖^6))*
          (∑ i : Fin (2^(2*j)), ∑ k : Fin (2^(j+2)),
            ∫ y : Fin 3 → ℝ, (∏ a : Fin 3, (1+(y a/(20*T))^2)⁻¹)*
              (∫ u : ℝ in Icc (0:ℝ) 1,
                ‖∑ a∈((V.filter (fun a =>
                    min ⌊N*Real.sqrt ((l a:ℝ)/T)⌋₊ (2^(2*j)-1)=(i:ℕ))).filter
                  (fun a => min ⌊((2^(j+2):ℕ):ℝ)*
                    ((((l a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)⌋₊ (2^(j+2)-1)=(k:ℕ))),
                  c a*fordAdditiveCharacter ((l a:ℝ)*u+
                    y 0*((l a:ℝ)/T)^2+y 1*((l a:ℝ)/T)^((3:ℝ)/2)+
                    y 2*Real.sqrt ((l a:ℝ)/T))‖^6)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := exists_bourgainSource_small_anisotropic_original.{u} hε hν
  refine ⟨C,hC,?_⟩
  intro j hj
  dsimp only
  intro hscale ι κ S V z c m l hw hv hsep
  have hh := hbound j hj hscale ι κ S V z c m l hw hv hsep
  have hT : (((2:ℝ)^(2*j))^2)≠0 := by positivity
  simp_rw [bourgainSourceShiftedPeriod_integer _ _ _ hT] at hh
  simpa only [bourgainSourceSixMoment,bourgainClosedFineCell,Fin.ext_iff,
    Nat.cast_pow,Nat.cast_ofNat] using hh

end TaoTrudgianYang2025

/-! Native quadratic VMVT and its exact finite weighted physical-period consumer. -/

noncomputable section
open MeasureTheory GafniTao Set
namespace TaoTrudgianYang2025

private theorem exists_bourgain_quadratic_vinogradov_count {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ Q : ℕ, 1≤Q →
      (fordVinogradovMomentNat 3 2 Q:ℝ)≤C*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := heathBrownVMVTMainConjecture_native 2 3 ε
    (by decide) (by decide) hε
  refine ⟨C,hC,?_⟩
  intro Q hQ
  have hh := h Q hQ
  norm_num [fordLambda34] at hh
  exact hh

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

private theorem bourgain_weighted_vinogradov_power (s k Q : ℕ)
    (z : Fin Q → ℂ) (α : UnitAddTorus (Fin k)) :
    (∑ n : Fin Q, z n*fordVinogradovMonomial n α)^s =
      ∑ x : FordVinogradovTuple s Q, (∏ i : Fin s, z (x i))*
        UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib,ford_prod_monomial_eq]

private theorem bourgain_weighted_vinogradov_complex_mean (s k Q : ℕ)
    (z : Fin Q → ℂ) :
    (((∫ α : UnitAddTorus (Fin k), ‖∑ n : Fin Q, z n*fordVinogradovMonomial n α‖^(2*s)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)):ℝ):ℂ) =
      ∑ x : FordVinogradovTuple s Q, ∑ y : FordVinogradovTuple s Q,
        if fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y=0
        then (∏ i : Fin s,z (x i))*conj (∏ i : Fin s,z (y i)) else 0 := by
  classical
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  let A := fun x : FordVinogradovTuple s Q => ∏ i : Fin s,z (x i)
  let S := fun α : UnitAddTorus (Fin k) => ∑ n : Fin Q,z n*fordVinogradovMonomial n α
  have hc (α : UnitAddTorus (Fin k)) : conj (S α)^s =
      ∑ y : FordVinogradovTuple s Q, conj (A y)*
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α := by
    have hh := congrArg conj (bourgain_weighted_vinogradov_power s k Q z α)
    simpa only [S,A,map_pow,map_sum,map_mul,UnitAddTorus.mFourier_neg] using hh
  have hphase (α : UnitAddTorus (Fin k)) :
      S α^s*conj (S α)^s =
        ∑ x : FordVinogradovTuple s Q, ∑ y : FordVinogradovTuple s Q,
          (A x*conj (A y))*
            UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x-
              fordVinogradovPowerVector s k Q y) α := by
    rw [hc]
    change (∑ n : Fin Q,z n*fordVinogradovMonomial n α)^s*_ = _
    rw [bourgain_weighted_vinogradov_power,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [←ford_pair_character x y α]
    dsimp [A]
    ring
  have hi (x y : FordVinogradovTuple s Q) :
      Integrable (fun α : UnitAddTorus (Fin k) =>
        (A x*conj (A y))*UnitAddTorus.mFourier
          (fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y) α) μ :=
    (ford_integrable_mFourier_pi_haar _).const_mul _
  have hiRow (x : FordVinogradovTuple s Q) :
      Integrable (fun α : UnitAddTorus (Fin k) =>
        ∑ y : FordVinogradovTuple s Q,
          (A x*conj (A y))*UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y) α) μ :=
    integrable_finsetSum Finset.univ (fun y _ => hi x y)
  have hcast :
      (((∫ α : UnitAddTorus (Fin k), ‖S α‖^(2*s) ∂μ):ℝ):ℂ)=
        ∫ α : UnitAddTorus (Fin k), S α^s*conj (S α)^s ∂μ := by
    have hcast' :
        (∫ α : UnitAddTorus (Fin k), ((‖S α‖^(2*s):ℝ):ℂ) ∂μ) =
          ((∫ α : UnitAddTorus (Fin k), ‖S α‖^(2*s) ∂μ : ℝ):ℂ) := integral_ofReal
    rw [←hcast']
    apply integral_congr_ae
    filter_upwards with α
    simpa only [Complex.ofReal_pow] using (ford_pow_mul_conj_pow (S α) s).symm
  change (((∫ α : UnitAddTorus (Fin k), ‖S α‖^(2*s) ∂μ):ℝ):ℂ)=_
  rw [hcast]
  simp_rw [hphase]
  rw [integral_finsetSum Finset.univ (fun x _ => hiRow x)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [integral_finsetSum Finset.univ (fun y _ => hi x y)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [integral_const_mul]
  have ho := ford_integral_mFourier_pi_haar_eq
    (fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y)
  change (∫ α : UnitAddTorus (Fin k),
    UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x-
      fordVinogradovPowerVector s k Q y) α ∂μ)=_ at ho
  rw [ho]
  split_ifs <;> simp only [mul_one,mul_zero,A]

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

private theorem bourgain_weighted_vinogradov_mean_le (s k Q : ℕ)
    (z : Fin Q → ℂ) {B : ℝ} (hB : 0≤B) (hz : ∀ n, ‖z n‖≤B) :
    (∫ α : UnitAddTorus (Fin k), ‖∑ n : Fin Q,z n*fordVinogradovMonomial n α‖^(2*s)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) ≤
        B^(2*s)*(fordVinogradovMomentNat s k Q:ℝ) := by
  classical
  let A := fun x : FordVinogradovTuple s Q => ∏ i : Fin s,z (x i)
  let H := fun (x y : FordVinogradovTuple s Q) =>
    if fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y=0
    then A x*conj (A y) else 0
  have hA (x : FordVinogradovTuple s Q) : ‖A x‖≤B^s := by
    dsimp [A]
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin s,B := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hz (x i))
      _ = _ := by simp
  have hterm (x y : FordVinogradovTuple s Q) : ‖H x y‖≤
      if fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y=0
      then B^(2*s) else 0 := by
    dsimp [H]
    split_ifs with he
    · rw [norm_mul,Complex.norm_conj]
      calc
        _ ≤ B^s*B^s := mul_le_mul (hA x) (hA y) (norm_nonneg _) (pow_nonneg hB s)
        _ = _ := by rw [←pow_add]; congr 1; omega
    · simp only [norm_zero,le_refl]
  have hc := bourgain_weighted_vinogradov_complex_mean s k Q z
  have hn : 0≤∫ α : UnitAddTorus (Fin k),
      ‖∑ n : Fin Q,z n*fordVinogradovMonomial n α‖^(2*s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) :=
    integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hcount : (∑ x : FordVinogradovTuple s Q, ∑ y : FordVinogradovTuple s Q,
      if fordVinogradovPowerVector s k Q x-fordVinogradovPowerVector s k Q y=0
      then B^(2*s) else 0) =
        B^(2*s)*(fordVinogradovMomentNat s k Q:ℝ) := by
    simp only [fordVinogradovMomentNat,fordVinogradovShiftedCountNat,
      fordRepresentationCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
      Nat.cast_one,Nat.cast_zero]
    rw [Finset.sum_product]
    simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero]
  calc
    _ = ‖(((∫ α : UnitAddTorus (Fin k),
        ‖∑ n : Fin Q,z n*fordVinogradovMonomial n α‖^(2*s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)):ℝ):ℂ)‖ := by
      rw [Complex.norm_real,Real.norm_of_nonneg hn]
    _ = ‖∑ x : FordVinogradovTuple s Q, ∑ y : FordVinogradovTuple s Q,H x y‖ :=
      congrArg norm hc
    _ ≤ ∑ x : FordVinogradovTuple s Q, ∑ y : FordVinogradovTuple s Q,‖H x y‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ _ := (Finset.sum_le_sum (fun x _ =>
      Finset.sum_le_sum (fun y _ => hterm x y))).trans_eq hcount

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

private theorem bourgain_vinogradov_monomial_real {k Q : ℕ}
    (n : Fin Q) (α : Fin k → ℝ) :
    fordVinogradovMonomial n (fun j => (α j : UnitAddCircle)) =
      fordAdditiveCharacter (∑ j : Fin k, α j*((n:ℕ)+1:ℝ)^((j:ℕ)+1)) := by
  unfold fordVinogradovMonomial UnitAddTorus.mFourier
    fordVinogradovExponent fordAdditiveCharacter
  simp only [ContinuousMap.coe_mk, fourier_coe_apply]
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf

private theorem exists_bourgain_quadratic_weighted_cube {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (Q : ℕ), 1≤Q → ∀ (z : Fin Q → ℂ) (B : ℝ), 0≤B →
      (∀ n, ‖z n‖≤B) →
      (∫ α : Fin 2 → ℝ in {α | ∀ j, α j∈Ioc (0:ℝ) 1},
        ‖∑ n : Fin Q, z n*fordAdditiveCharacter
          (α 0*((n:ℕ)+1:ℝ)+α 1*((n:ℕ)+1:ℝ)^2)‖^6) ≤
        C*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,hcount⟩ := exists_bourgain_quadratic_vinogradov_count hε
  refine ⟨C,hC,?_⟩
  intro Q hQ z B hB hz
  have hm := bourgain_weighted_vinogradov_mean_le 3 2 Q z hB hz
  have hpre := UnitAddTorus.integral_preimage
    (fun α : UnitAddTorus (Fin 2) =>
      ‖∑ n : Fin Q,z n*fordVinogradovMonomial n α‖^6) (fun _ => 0)
  change (∫ α : UnitAddTorus (Fin 2),
    ‖∑ n : Fin Q,z n*fordVinogradovMonomial n α‖^6
      ∂Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) =
    ∫ α : Fin 2 → ℝ in {α | ∀ j, α j∈Ioc (0:ℝ) (0+1)},
      ‖∑ n : Fin Q,z n*fordVinogradovMonomial n
        (fun j => (α j : UnitAddCircle))‖^6 at hpre
  simp only [zero_add,bourgain_vinogradov_monomial_real,
    Fin.sum_univ_two,Fin.val_zero,Fin.val_one,zero_add,pow_one] at hpre
  change (∫ α : UnitAddTorus (Fin 2),
    ‖∑ n : Fin Q,z n*fordVinogradovMonomial n α‖^6
      ∂Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)) ≤ _ at hm
  rw [hpre] at hm
  calc
    _ ≤ B^6*(fordVinogradovMomentNat 3 2 Q:ℝ) := hm
    _ ≤ B^6*(C*(Q:ℝ)^((3:ℝ)+ε)) :=
      mul_le_mul_of_nonneg_left (hcount Q hQ) (pow_nonneg hB 6)
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

private theorem bourgain_unit_square_integral (f : (Fin 2 → ℝ) → ℝ)
    (hf : Continuous f) :
    (∫ α : Fin 2 → ℝ in {α | ∀ j, α j∈Ioc (0:ℝ) 1}, f α) =
      ∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1, f ![u,v] := by
  let μ : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
  have hset : {α : Fin 2 → ℝ | ∀ j, α j∈Ioc (0:ℝ) 1} =
      Set.pi Set.univ (fun _ : Fin 2 => Ioc (0:ℝ) 1) := by ext α; simp
  have hmeasure : volume.restrict (Icc (0 : Fin 2 → ℝ) 1) =
      Measure.pi (fun _ : Fin 2 => μ) := by
    rw [←Set.pi_univ_Icc]
    exact Measure.restrict_pi_pi (fun _ => volume) _
  have hi : Integrable f (Measure.pi (fun _ : Fin 2 => μ)) := by
    rw [←hmeasure]
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  let e := (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ))
  have hmp := (measurePreserving_finTwoArrow μ).symm
  have hi' := hmp.integrable_comp_of_integrable hi
  have he (p : ℝ × ℝ) : e.symm p=![p.1,p.2] := rfl
  have hint := hmp.integral_comp' f
  have hprod := integral_prod (fun p : ℝ × ℝ => f (e.symm p)) hi'
  have hae : (Set.pi Set.univ (fun _ : Fin 2 => Ioc (0:ℝ) 1)) =ᵐ[volume]
      Icc (0 : Fin 2 → ℝ) 1 := Measure.univ_pi_Ioc_ae_eq_Icc
  rw [hset,setIntegral_congr_set hae,hmeasure]
  rw [←hint,hprod]
  simp only [he]
  exact integral_integral_swap (μ:=μ) (ν:=μ)
    (f:=fun u v => f ![u,v]) hi'

private theorem bourgain_quadratic_period_integer_translate {Q : ℕ}
    (z : Fin Q → ℂ) (a v : ℝ) :
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ n : Fin Q,z n*fordAdditiveCharacter
        ((a+((n:ℕ)+1:ℝ))*u+(a+((n:ℕ)+1:ℝ))^2*v)‖^6) =
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ n : Fin Q,z n*fordAdditiveCharacter
        (((n:ℕ)+1:ℝ)*u+((n:ℕ)+1:ℝ)^2*v)‖^6) := by
  have he (u : ℝ) :
      (∑ n : Fin Q,z n*fordAdditiveCharacter
        ((a+((n:ℕ)+1:ℝ))*u+(a+((n:ℕ)+1:ℝ))^2*v)) =
      fordAdditiveCharacter (a*u+a^2*v)*
        ∑ n : Fin Q,z n*fordAdditiveCharacter
          (((n:ℕ)+1:ℝ)*u+(2*a*v)*((n:ℕ)+1:ℝ)+v*((n:ℕ)+1:ℝ)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hp : (a+((n:ℕ)+1:ℝ))*u+(a+((n:ℕ)+1:ℝ))^2*v =
      (a*u+a^2*v)+(((n:ℕ)+1:ℝ)*u+(2*a*v)*((n:ℕ)+1:ℝ)+v*((n:ℕ)+1:ℝ)^2) := by ring
    rw [hp,fordAdditiveCharacter_add]
    ring
  simp only [he,norm_mul,sargos_character_norm,one_mul]
  have hh := bourgain_integer_cell_linear_shift Finset.univ z
    (fun n : Fin Q => ((n:ℕ):ℤ)+1) (fun n : Fin Q => ((n:ℕ)+1:ℝ))
    (t:=1) (c:=0) (by norm_num) (by intro n hn; push_cast; ring) (2*a*v) v
  simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one,mul_comm] using hh

private theorem exists_bourgain_quadratic_weighted_integer_interval {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (Q : ℕ), 1≤Q → ∀ (z : Fin Q → ℂ) (B a : ℝ), 0≤B →
      (∀ n, ‖z n‖≤B) →
      (∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ n : Fin Q,z n*fordAdditiveCharacter
          ((a+((n:ℕ)+1:ℝ))*u+(a+((n:ℕ)+1:ℝ))^2*v)‖^6) ≤
        C*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_bourgain_quadratic_weighted_cube hε
  refine ⟨C,hC,?_⟩
  intro Q hQ z B a hB hz
  simp_rw [bourgain_quadratic_period_integer_translate]
  have hc : Continuous (fun α : Fin 2 → ℝ =>
      ‖∑ n : Fin Q,z n*fordAdditiveCharacter
        (α 0*((n:ℕ)+1:ℝ)+α 1*((n:ℕ)+1:ℝ)^2)‖^6) := by
    unfold fordAdditiveCharacter
    fun_prop
  have hh := h Q hQ z B hB hz
  rw [bourgain_unit_square_integral _ hc] at hh
  change (∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ n : Fin Q,z n*fordAdditiveCharacter
      (u*((n:ℕ)+1:ℝ)+v*((n:ℕ)+1:ℝ)^2)‖^6) ≤ _ at hh
  simpa only [mul_comm] using hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025
universe u

private theorem bourgain_integer_interval_fiber_sum {ι : Type u}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (A : ℤ) (Q : ℕ)
    (hm : ∀ i∈S, A < m i ∧ m i≤A+Q) (F : ℤ → ℂ) :
    (∑ n : Fin Q, (∑ i∈S.filter (fun i => m i=A+((n:ℕ):ℤ)+1), z i)*
      F (A+((n:ℕ):ℤ)+1)) = ∑ i∈S,z i*F (m i) := by
  classical
  let g := fun k : ℤ => (∑ i∈S.filter (fun i => m i=k),z i)*F k
  have hlen : ((A+(Q:ℤ)-A).toNat)=Q := by omega
  have hr := sum_int_Ioc_eq_forward_range g (a:=A) (b:=A+Q) (by omega)
  rw [hlen,←Fin.sum_univ_eq_sum_range] at hr
  have he : (∑ n : Fin Q,(∑ i∈S.filter (fun i => m i=A+((n:ℕ):ℤ)+1),z i)*
      F (A+((n:ℕ):ℤ)+1)) = ∑ k∈Finset.Ioc A (A+Q),g k := by
    rw [hr]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [g,Nat.cast_add,Nat.cast_one,add_assoc]
  rw [he]
  have hm' : ∀ i∈S,m i∈Finset.Ioc A (A+Q) := by
    intro i hi
    exact Finset.mem_Ioc.mpr (hm i hi)
  calc
    _ = ∑ k∈Finset.Ioc A (A+Q), ∑ i∈S.filter (fun i => m i=k),z i*F (m i) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [g]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to hm' (fun i => z i*F (m i))

private theorem exists_bourgain_quadratic_weighted_finite_interval {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (Q : ℕ), 1≤Q →
      ∀ (ι : Type u) (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (A : ℤ) (B : ℝ),
        0≤B → (∀ i∈S,A < m i ∧ m i≤A+Q) →
        (∀ k : ℤ, (∑ i∈S.filter (fun i => m i=k), ‖z i‖)≤B) →
        (∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
          ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v)‖^6) ≤
            C*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
  classical
  obtain ⟨C,hC,h⟩ := exists_bourgain_quadratic_weighted_integer_interval hε
  refine ⟨C,hC,?_⟩
  intro Q hQ ι S z m A B hB hm hz
  let c := fun n : Fin Q => ∑ i∈S.filter (fun i => m i=A+((n:ℕ):ℤ)+1),z i
  have hc (n : Fin Q) : ‖c n‖≤B :=
    (norm_sum_le _ _).trans (hz (A+((n:ℕ):ℤ)+1))
  have hh := h Q hQ c B (A:ℝ) hB hc
  have he (u v : ℝ) :
      (∑ n : Fin Q,c n*fordAdditiveCharacter
        (((A:ℝ)+((n:ℕ)+1:ℝ))*u+((A:ℝ)+((n:ℕ)+1:ℝ))^2*v)) =
      ∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+(m i:ℝ)^2*v) := by
    have hf := bourgain_integer_interval_fiber_sum S z m A Q hm
      (fun k => fordAdditiveCharacter ((k:ℝ)*u+(k:ℝ)^2*v))
    simpa only [c,Int.cast_add,Int.cast_natCast,Int.cast_one,add_assoc] using hf
  simp_rw [he] at hh
  exact hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025

private theorem bourgain_periodic_eight_periods (f : ℝ → ℝ)
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ v : ℝ in Icc (-4:ℝ) 4,f v)=8*(∫ v : ℝ in Icc (0:ℝ) 1,f v) := by
  have hh := hp.intervalIntegral_add_zsmul_eq (8:ℤ) (-4)
    (fun a b => hf.intervalIntegrable a b)
  rw [hp.intervalIntegral_add_eq (-4) 0] at hh
  norm_num only [zsmul_eq_mul,Int.cast_ofNat,mul_one,zero_add] at hh
  simpa only [integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by norm_num : (-4:ℝ)≤4),
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hh

private theorem bourgain_periodic_physical_eight_periods
    (f : ℝ → ℝ) (hf : Continuous f) (hp : Function.Periodic f 1)
    {T : ℝ} (hT : 0<T) :
    (∫ y : ℝ in Icc (-4*T^2) (4*T^2),f (y/T^2)) =
      8*T^2*(∫ v : ℝ in Icc (0:ℝ) 1,f v) := by
  have hT₂ : 0<T^2 := sq_pos_of_pos hT
  rw [integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by nlinarith : -4*T^2≤4*T^2),
    intervalIntegral.integral_comp_div f hT₂.ne']
  have hneg : (-4*T^2)/T^2=(-4:ℝ) := by field_simp [hT.ne']
  have hpos : (4*T^2)/T^2=(4:ℝ) := by field_simp [hT.ne']
  rw [hneg,hpos,smul_eq_mul,
    intervalIntegral.integral_of_le (by norm_num : (-4:ℝ)≤4),
    ←integral_Icc_eq_integral_Ioc,bourgain_periodic_eight_periods f hf hp]
  ring

private theorem bourgain_centered_quadratic_period {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) (c v : ℝ) :
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*((m i:ℝ)-c)^2)‖^6) =
    (∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*(m i:ℝ)^2)‖^6) := by
  have he (u : ℝ) :
      (∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*((m i:ℝ)-c)^2)) =
      fordAdditiveCharacter (v*c^2)*
        ∑ i∈S,z i*fordAdditiveCharacter
          ((m i:ℝ)*u+(-2*v*c)*(m i:ℝ)+v*(m i:ℝ)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hp : (m i:ℝ)*u+v*((m i:ℝ)-c)^2 =
      v*c^2+((m i:ℝ)*u+(-2*v*c)*(m i:ℝ)+v*(m i:ℝ)^2) := by ring
    rw [hp,fordAdditiveCharacter_add]
    ring
  simp only [he,norm_mul,sargos_character_norm,one_mul]
  exact bourgain_integer_cell_linear_shift S z m (fun i => (m i:ℝ))
    (t:=1) (c:=0) (by norm_num) (by intro i hi; ring) (-2*v*c) v

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025
universe u

private theorem bourgain_integer_quadratic_period_continuous {ι : Type u}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    Continuous (fun v : ℝ => ∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*(m i:ℝ)^2)‖^6) := by
  have hc : Continuous (fun p : ℝ × ℝ =>
      ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*p.2+p.1*(m i:ℝ)^2)‖^6) := by
    unfold fordAdditiveCharacter
    fun_prop
  change Continuous (Function.uncurry (fun v u : ℝ =>
    ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*(m i:ℝ)^2)‖^6)) at hc
  have hh := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ:=volume) hc 0 1
  simpa only [integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hh

private theorem bourgain_integer_quadratic_period_periodic {ι : Type u}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) :
    Function.Periodic (fun v : ℝ => ∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*(m i:ℝ)^2)‖^6) 1 := by
  have hchar (k : ℤ) : fordAdditiveCharacter (k:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((k:ℝ):ℂ)=(k:ℂ)*(2*Real.pi*Complex.I) := by
      push_cast
      ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  intro v
  apply integral_congr_ae
  filter_upwards with u
  apply congrArg (fun w : ℂ => ‖w‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  have he : (m i:ℝ)*u+(v+1)*(m i:ℝ)^2 =
      ((m i:ℝ)*u+v*(m i:ℝ)^2)+((m i)^2:ℤ) := by push_cast; ring
  rw [he,fordAdditiveCharacter_add,hchar,mul_one]

private theorem bourgain_integer_quadratic_physical_period {ι : Type u}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ)
    (s : ι → ℝ) {T δ c : ℝ} (hT : 0<T)
    (hm : ∀ i∈S,T*δ*s i=(m i:ℝ)-c) :
    (∫ y : ℝ in Icc (-4*T^2) (4*T^2), ∫ u : ℝ in Icc (0:ℝ) 1,
      ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+δ^2*y*(s i)^2)‖^6) =
      8*T^2*(∫ v : ℝ in Icc (0:ℝ) 1, ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*(m i:ℝ)^2)‖^6) := by
  have he (y : ℝ) :
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+δ^2*y*(s i)^2)‖^6) =
      (∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+(y/T^2)*(m i:ℝ)^2)‖^6) := by
    rw [←bourgain_centered_quadratic_period S z m c (y/T^2)]
    apply integral_congr_ae
    filter_upwards with u
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun q : ℝ => z i*fordAdditiveCharacter q)
    rw [←hm i hi]
    field_simp [hT.ne']
  simp_rw [he]
  exact bourgain_periodic_physical_eight_periods _
    (bourgain_integer_quadratic_period_continuous S z m)
    (bourgain_integer_quadratic_period_periodic S z m) hT

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025
universe u

private theorem exists_bourgainOriginalSource_large_plane_vmvt {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (b d δ T q ν : ℝ),
      b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
      δ∈Ioc (0:ℝ) (1/16) → 0<T →
      (2*T^2)*δ^3≤32 → |q*δ^2|≤32 → 0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
      ∀ (Q P : ℕ), 1≤Q → 1≤P →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (s : ι → ℝ) (v : κ → ℝ)
        (m : ι → ℤ) (n : κ → ℤ) (A D : ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ i∈S,s i∈Icc (-1:ℝ) 1) →
        (∀ i∈V,v i∈Icc (-1:ℝ) 1) →
        (∀ i∈S,T*(b+δ*s i)=(m i:ℝ)) →
        (∀ i∈V,T*(d+δ*v i)=(n i:ℝ)) →
        (∀ i∈S,A < m i ∧ m i≤A+Q) →
        (∀ i∈V,D < n i ∧ n i≤D+P) →
        (∀ k : ℤ,(∑ i∈S.filter (fun i => m i=k),‖z i‖)≤B) →
        (∀ k : ℤ,(∑ i∈V.filter (fun i => n i=k),‖c i‖)≤H) →
        (∫ x : Fin 2 → ℝ in Icc (fun _ => -2*T^2) (fun _ => 2*T^2),
          (∫ u : ℝ in Icc (0:ℝ) 1,
            bourgainSourceSixMoment S z (fun i => b+δ*s i) ![T*u,x 0,x 1,q])*
          (∫ u : ℝ in Icc (0:ℝ) 1,
            bourgainSourceSixMoment V c (fun i => d+δ*v i) ![T*u,x 0,x 1,q])) ≤
          (C/ν)*T^4*B^6*H^6*(Q:ℝ)^((3:ℝ)+ε)*(P:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨K,hK,hframe⟩ := exists_bourgainOriginalSource_periodic_box_factorization.{u}
  obtain ⟨E,hE,hvmvt⟩ := exists_bourgain_quadratic_weighted_finite_interval.{u} hε
  refine ⟨64*K*E^2,by positivity,?_⟩
  intro b d δ T q ν hb hd hδ hT hscale hq hν hsep Q P hQ hP
    ι κ S V z c s v m n A D B H hB hH hs hv hm hn hSm hVn hz hc
  let JS := ∫ v : ℝ in Icc (0:ℝ) 1,∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+v*(m i:ℝ)^2)‖^6
  let JV := ∫ v : ℝ in Icc (0:ℝ) 1,∫ u : ℝ in Icc (0:ℝ) 1,
    ‖∑ i∈V,c i*fordAdditiveCharacter ((n i:ℝ)*u+v*(n i:ℝ)^2)‖^6
  have hJS : JS≤E*B^6*(Q:ℝ)^((3:ℝ)+ε) := by
    simpa only [JS,mul_comm] using hvmvt Q hQ ι S z m A B hB hSm hz
  have hJV : JV≤E*H^6*(P:ℝ)^((3:ℝ)+ε) := by
    simpa only [JV,mul_comm] using hvmvt P hP κ V c n D H hH hVn hc
  have hJV₀ : 0≤JV := integral_nonneg (fun _ => integral_nonneg (fun _ => by positivity))
  have hprod := mul_le_mul hJS hJV hJV₀ (by positivity)
  have hms (i : ι) (hi : i∈S) : T*δ*s i=(m i:ℝ)-T*b := by linarith [hm i hi]
  have hnv (i : κ) (hi : i∈V) : T*δ*v i=(n i:ℝ)-T*d := by linarith [hn i hi]
  have hmain := hframe b d δ T (2*T^2) q ν hb hd hδ hT hscale hq hν hsep
    S V z c s v m n hs hv hm hn
  have heL : -2*(2*T^2)=(-4*T^2) := by ring
  have heR : 2*(2*T^2)=4*T^2 := by ring
  rw [heL,heR,bourgain_integer_quadratic_physical_period S z m s hT hms,
    bourgain_integer_quadratic_physical_period V c n v hT hnv] at hmain
  change _ ≤ (K/ν)*(8*T^2*JS)*(8*T^2*JV) at hmain
  calc
    _ ≤ (K/ν)*(8*T^2*JS)*(8*T^2*JV) := by
      simpa only [neg_mul] using hmain
    _ = (64*K/ν)*T^4*(JS*JV) := by ring
    _ ≤ (64*K/ν)*T^4*((E*B^6*(Q:ℝ)^((3:ℝ)+ε))*
        (E*H^6*(P:ℝ)^((3:ℝ)+ε))) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators ComplexConjugate
namespace TaoTrudgianYang2025
universe u

/-- The actual large-plane fine-cell moment, with the quadratic sixth moments
discharged by the already-proved native degree-two VMVT. Coefficient fibers
retain repeated integer frequencies. No moment estimate is a hypothesis. -/
theorem exists_bourgainSourceCurve_large_plane_quadratic_bound
    {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (b d δ T q ν : ℝ),
      b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
      δ∈Ioc (0:ℝ) (1/16) → 0<T →
      (2*T^2)*δ^3≤32 → 2*T*δ^2≤32 → |q|≤2*T →
      0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
      ∀ (Q P : ℕ), 1≤Q → 1≤P →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ)
        (A D : ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ i∈S,(m i:ℝ)/T∈Icc b (b+δ)) →
        (∀ i∈V,(n i:ℝ)/T∈Icc d (d+δ)) →
        (∀ i∈S,A < m i ∧ m i≤A+Q) →
        (∀ i∈V,D < n i ∧ n i≤D+P) →
        (∀ k : ℤ,(∑ i∈S.filter (fun i => m i=k),‖z i‖)≤B) →
        (∀ k : ℤ,(∑ i∈V.filter (fun i => n i=k),‖c i‖)≤H) →
        (∫ x : Fin 2 → ℝ in Icc (fun _ => -2*T^2) (fun _ => 2*T^2),
          (∫ u : ℝ in Icc (0:ℝ) 1,
            ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+
              x 0*((m i:ℝ)/T)^2+x 1*((m i:ℝ)/T)^((3:ℝ)/2)+
              q*Real.sqrt ((m i:ℝ)/T))‖^6)*
          (∫ u : ℝ in Icc (0:ℝ) 1,
            ‖∑ i∈V,c i*fordAdditiveCharacter ((n i:ℝ)*u+
              x 0*((n i:ℝ)/T)^2+x 1*((n i:ℝ)/T)^((3:ℝ)/2)+
              q*Real.sqrt ((n i:ℝ)/T))‖^6)) ≤
          (C/ν)*T^4*B^6*H^6*(Q:ℝ)^((3:ℝ)+ε)*(P:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨C,hC,h⟩ := exists_bourgainOriginalSource_large_plane_vmvt.{u} hε
  refine ⟨C,hC,?_⟩
  intro b d δ T q ν hb hd hδ hT hscale hsmall hq hν hsep Q P hQ hP
    ι κ S V z c m n A D B H hB hH hSw hVw hSm hVn hz hc
  let s := fun i => ((m i:ℝ)/T-b)/δ
  let v := fun i => ((n i:ℝ)/T-d)/δ
  have hs (i : ι) (hi : i∈S) : s i∈Icc (-1:ℝ) 1 := by
    have hw := hSw i hi
    constructor
    · exact (by norm_num : (-1:ℝ)≤0).trans (div_nonneg (sub_nonneg.mpr hw.1) hδ.1.le)
    · exact (div_le_one hδ.1).mpr (by linarith [hw.2])
  have hv (i : κ) (hi : i∈V) : v i∈Icc (-1:ℝ) 1 := by
    have hw := hVw i hi
    constructor
    · exact (by norm_num : (-1:ℝ)≤0).trans (div_nonneg (sub_nonneg.mpr hw.1) hδ.1.le)
    · exact (div_le_one hδ.1).mpr (by linarith [hw.2])
  have hes (i : ι) : b+δ*s i=(m i:ℝ)/T := by dsimp [s]; field_simp [hδ.1.ne']; ring
  have hev (i : κ) : d+δ*v i=(n i:ℝ)/T := by dsimp [v]; field_simp [hδ.1.ne']; ring
  have hm (i : ι) (_hi : i∈S) : T*(b+δ*s i)=(m i:ℝ) := by
    rw [hes]; field_simp
  have hn (i : κ) (_hi : i∈V) : T*(d+δ*v i)=(n i:ℝ) := by
    rw [hev]; field_simp
  have hq' : |q*δ^2|≤32 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg δ)]
    exact (mul_le_mul_of_nonneg_right hq (sq_nonneg δ)).trans hsmall
  have hh := h b d δ T q ν hb hd hδ hT hscale hq' hν hsep Q P hQ hP
    ι κ S V z c s v m n A D B H hB hH hs hv hm hn hSm hVn hz hc
  have heS (u : ℝ) (x : Fin 2 → ℝ) :
      bourgainSourceSixMoment S z (fun i => b+δ*s i) ![T*u,x 0,x 1,q] =
        ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+
          x 0*((m i:ℝ)/T)^2+x 1*((m i:ℝ)/T)^((3:ℝ)/2)+
          q*Real.sqrt ((m i:ℝ)/T))‖^6 := by
    simp only [bourgainSourceSixMoment,hes]
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun r : ℝ => z i*fordAdditiveCharacter r)
    change T*u*((m i:ℝ)/T)+x 0*((m i:ℝ)/T)^2+
      x 1*((m i:ℝ)/T)^((3:ℝ)/2)+q*Real.sqrt ((m i:ℝ)/T)=_
    field_simp [hT.ne']
  have heV (u : ℝ) (x : Fin 2 → ℝ) :
      bourgainSourceSixMoment V c (fun i => d+δ*v i) ![T*u,x 0,x 1,q] =
        ‖∑ i∈V,c i*fordAdditiveCharacter ((n i:ℝ)*u+
          x 0*((n i:ℝ)/T)^2+x 1*((n i:ℝ)/T)^((3:ℝ)/2)+
          q*Real.sqrt ((n i:ℝ)/T))‖^6 := by
    simp only [bourgainSourceSixMoment,hev]
    apply congrArg (fun w : ℂ => ‖w‖^6)
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun r : ℝ => c i*fordAdditiveCharacter r)
    change T*u*((n i:ℝ)/T)+x 0*((n i:ℝ)/T)^2+
      x 1*((n i:ℝ)/T)^((3:ℝ)/2)+q*Real.sqrt ((n i:ℝ)/T)=_
    field_simp [hT.ne']
  simp_rw [heS,heV] at hh
  exact hh

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
namespace TaoTrudgianYang2025

private theorem bourgain_fine_cell_integer_interval {T a h : ℝ} {K : ℕ}
    (hT : 0<T) (hwidth : T*h=(K:ℝ)) {m : ℤ}
    (hm : (m:ℝ)/T∈Icc a (a+h)) :
    ⌊T*a⌋-1 < m ∧ m≤(⌊T*a⌋-1:ℤ)+(K+2:ℕ) := by
  have hlo : T*a≤(m:ℝ) := by
    have hh := (le_div_iff₀ hT).mp hm.1
    nlinarith
  have hhi : (m:ℝ)≤T*a+(K:ℝ) := by
    have hh := (div_le_iff₀ hT).mp hm.2
    nlinarith [hwidth]
  have hfloor := Int.floor_le (T*a)
  have hceil := Int.lt_floor_add_one (T*a)
  constructor
  · have hh : ((⌊T*a⌋:ℤ):ℝ)-1<(m:ℝ) := by linarith
    exact_mod_cast hh
  · have hh : (m:ℝ)≤((⌊T*a⌋:ℤ):ℝ)-1+((K:ℝ)+2) := by linarith
    exact_mod_cast hh

private theorem bourgain_fine_cell_base {a h w : ℝ}
    (ha : (1/4:ℝ)≤a) (hw : w∈Icc a (a+h)) (hw₁ : w≤1) :
    a∈Icc (1/4:ℝ) 1 := ⟨ha,hw.1.trans hw₁⟩

private theorem bourgain_sqrt_cell_distance {a h w : ℝ}
    (ha : (1/4:ℝ)≤a) (hw : w∈Icc a (a+h)) :
    0≤Real.sqrt w-Real.sqrt a ∧ Real.sqrt w-Real.sqrt a≤h := by
  have ha₀ : 0≤a := by linarith
  have hw₀ : 0≤w := ha₀.trans hw.1
  have hsa : (1/2:ℝ)≤Real.sqrt a := by
    have he : Real.sqrt ((1/2:ℝ)^2)=(1/2:ℝ) := Real.sqrt_sq (by norm_num)
    rw [←he]
    exact Real.sqrt_le_sqrt (by norm_num; exact ha)
  have hsw : Real.sqrt a≤Real.sqrt w := Real.sqrt_le_sqrt hw.1
  have hsqa := Real.sq_sqrt ha₀
  have hsqw := Real.sq_sqrt hw₀
  constructor
  · linarith
  · have hx : 0≤(Real.sqrt w-Real.sqrt a)*(Real.sqrt w+Real.sqrt a-1) :=
      mul_nonneg (sub_nonneg.mpr hsw) (by linarith)
    nlinarith [hw.2]

private theorem bourgain_fine_base_separation {a b h w v ν : ℝ}
    (ha : (1/4:ℝ)≤a) (hb : (1/4:ℝ)≤b)
    (hw : w∈Icc a (a+h)) (hv : v∈Icc b (b+h))
    (hwidth : 2*h≤ν/2) (hsep : ν≤|Real.sqrt w-Real.sqrt v|) :
    ν/2≤|Real.sqrt a-Real.sqrt b| := by
  have hs := bourgain_sqrt_cell_distance ha hw
  have ht := bourgain_sqrt_cell_distance hb hv
  have hab := abs_add_three (Real.sqrt w-Real.sqrt a)
    (Real.sqrt a-Real.sqrt b) (Real.sqrt b-Real.sqrt v)
  have he : (Real.sqrt w-Real.sqrt a)+(Real.sqrt a-Real.sqrt b)+
      (Real.sqrt b-Real.sqrt v)=Real.sqrt w-Real.sqrt v := by ring
  rw [he,abs_of_nonneg hs.1,abs_of_nonpos (show Real.sqrt b-Real.sqrt v≤0 by linarith [ht.1])] at hab
  linarith [hs.2,ht.2]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
namespace TaoTrudgianYang2025

private theorem bourgain_fine_dyadic_physics {j : ℕ} (hj : 3≤j) :
    let N := (2:ℝ)^(2*j)
    let T := N^2
    let F := (2:ℝ)^(j+2)
    let h := 2/(N*F)
    let K : ℕ := 2^(j-1)
    h∈Ioc (0:ℝ) (1/16) ∧
      (2*T^2)*h^3≤32 ∧ 2*T*h^2≤32 ∧
      T*h=(K:ℝ) ∧ 1≤K+2 ∧ K+2≤2^j ∧ 2*h≤1/N := by
  dsimp only
  let k := (2:ℝ)^(j-1)
  have hk₀ : 0<k := by dsimp [k]; positivity
  have hk₁ : 1≤k := one_le_pow₀ (by norm_num) 
  have hk₂ : 2≤k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 1≤j-1)
    simpa only [pow_one] using hh
  have hN : (2:ℝ)^(2*j)=4*k^2 := by
    have he : 2*j=(j-1)*2+2 := by omega
    rw [he,pow_add,pow_mul]
    dsimp [k]
    ring
  have hF : (2:ℝ)^(j+2)=8*k := by
    have he : j+2=(j-1)+3 := by omega
    rw [he,pow_add]
    dsimp [k]
    ring
  have hjpow : (2:ℝ)^j=2*k := by
    have he : j=(j-1)+1 := by omega
    rw [he,pow_add]
    dsimp [k]
    ring
  have hwidth : 2/((2:ℝ)^(2*j)*(2:ℝ)^(j+2))=1/(16*k^3) := by
    rw [hN,hF]
    field_simp
    ring
  have hscale₃ : (2*((2:ℝ)^(2*j))^4)*(1/(16*k^3))^3=1/(8*k) := by
    rw [hN]
    field_simp
    ring
  have hscale₂ : (2*((2:ℝ)^(2*j))^2)*(1/(16*k^3))^2=1/(8*k^2) := by
    rw [hN]
    field_simp
    ring
  rw [hwidth]
  refine ⟨⟨by positivity,?_⟩,?_,?_,?_,by have h0 := Nat.zero_le (2^(j-1)); omega,?_,?_⟩
  · apply (div_le_iff₀ (by positivity : 0<16*k^3)).mpr
    have hpow : 1≤k^3 := one_le_pow₀ hk₁
    nlinarith
  · rw [←pow_mul]
    change (2*((2:ℝ)^(2*j))^4)*(1/(16*k^3))^3≤32
    rw [hscale₃]
    apply (div_le_iff₀ (by positivity : 0<8*k)).mpr
    nlinarith
  · rw [hscale₂]
    apply (div_le_iff₀ (by positivity : 0<8*k^2)).mpr
    nlinarith [sq_nonneg (k-1)]
  · rw [hN]
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    change (4*k^2)^2*(1/(16*k^3))=k
    field_simp
    ring
  · have hh : ((2^(j-1)+2:ℕ):ℝ)≤((2^j:ℕ):ℝ) := by
      simp only [Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,hjpow]
      change k+2≤2*k
      linarith
    exact_mod_cast hh
  · rw [hN]
    apply (le_div_iff₀ (by positivity : 0<4*k^2)).mpr
    have he : 2*(1/(16*k^3))*(4*k^2)=1/(2*k) := by field_simp; ring
    rw [he]
    exact (div_le_one (by positivity : 0<2*k)).mpr (by linarith)

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_middle_rectangle_average {K : ℝ}
    (hK : 0 ≤ K) (Q : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ)
    (hfc : Continuous f) (hf₀ : ∀ x, 0 ≤ f x) :
    (2*K)^2*(∫ x : Fin 2 → ℝ in Icc (-Q) Q, f x) ≤
      ∫ q : Fin 2 → ℝ in Icc (fun i => -(Q i+K)) (fun i => Q i+K),
        ∫ y : Fin 2 → ℝ in Icc (fun _ => -K) (fun _ => K), f (q+y) := by
  let B := Icc (fun _ : Fin 2 => -K) (fun _ => K)
  let U := Icc (-Q) Q
  let V := Icc (fun i => -(Q i+K)) (fun i => Q i+K)
  have hpoint (y : Fin 2 → ℝ) (hy : y ∈ B) :
      (∫ x in U, f x) ≤ ∫ q in V, f (q+y) := by
    have hsub : (fun q => q+y) ⁻¹' U ⊆ V := by
      intro q hq
      constructor
      · intro i
        have hl := hq.1 i
        have hu := hy.2 i
        change -Q i ≤ q i+y i at hl
        change y i ≤ K at hu
        change -(Q i+K) ≤ q i
        linarith
      · intro i
        have hu := hq.2 i
        have hl := hy.1 i
        change q i+y i ≤ Q i at hu
        change -K ≤ y i at hl
        change q i ≤ Q i+K
        linarith
    have hi : IntegrableOn (fun q => f (q+y)) V :=
      ContinuousOn.integrableOn_compact isCompact_Icc
        (hfc.comp (continuous_id.add continuous_const)).continuousOn
    calc
      _ = ∫ q in (fun q => q+y) ⁻¹' U, f (q+y) :=
        ((measurePreserving_add_right volume y).setIntegral_preimage_emb
          (Homeomorph.addRight y).measurableEmbedding f U).symm
      _ ≤ _ := setIntegral_mono_set hi
        (Filter.Eventually.of_forall (fun q => hf₀ (q+y)))
        (Filter.Eventually.of_forall hsub)
  have hc : Continuous (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => f (p.1+p.2)) :=
    hfc.comp (continuous_fst.add continuous_snd)
  have hi : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => f (p.1+p.2))
      ((volume.restrict V).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc) hc.continuousOn
  have hconst : IntegrableOn (fun _y : Fin 2 → ℝ => ∫ x in U, f x) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hh := setIntegral_mono_on hconst hi.integral_prod_right measurableSet_Icc hpoint
  rw [integral_const,measureReal_restrict_apply_univ] at hh
  change volume.real B*(∫ x in U, f x) ≤ _ at hh
  have hmass : volume.real B=(2*K)^2 := by
    change (volume (Icc (fun _ : Fin 2 => -K) (fun _ => K))).toReal=_
    rw [Real.volume_Icc_pi_toReal (by intro i; change -K≤K; linarith)]
    simp only [Fin.prod_univ_two]
    ring
  rw [hmass] at hh
  have hswap := integral_integral_swap (f:=fun q y => f (q+y)) hi
  exact hh.trans_eq hswap.symm

end TaoTrudgianYang2025


noncomputable section
open MeasureTheory Set
namespace TaoTrudgianYang2025

private theorem bourgain_anisotropic_rectangle_integral_middle
    (T R : ℝ) (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) :
    (∫ x : Fin 4 → ℝ in Icc (-![T,R,R,T]) ![T,R,R,T],f x) =
      ∫ y : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
        ∫ r : ℝ in Icc (-T) T,∫ q : ℝ in Icc (-T) T,f ![r,y 0,y 1,q] := by
  let I := Icc (-T) T
  let B := Icc (fun _ : Fin 2 => -R) (fun _ => R)
  have hq (r : ℝ) : Integrable
      (fun p : ℝ × (Fin 2 → ℝ) => f ![r,p.2 0,p.2 1,p.1])
      ((volume.restrict I).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact (hf.comp (by fun_prop)).continuousOn
  have hc : Continuous (Function.uncurry (fun (p : ℝ × (Fin 2 → ℝ)) (q : ℝ) =>
      f ![p.1,p.2 0,p.2 1,q])) :=
    hf.comp (by fun_prop)
  have hg := continuous_parametric_integral_of_continuous (μ:=volume) hc
    (show IsCompact I from isCompact_Icc)
  have hr : Integrable
      (fun p : ℝ × (Fin 2 → ℝ) => ∫ q : ℝ in I,f ![p.1,p.2 0,p.2 1,q])
      ((volume.restrict I).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hg.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [bourgain_anisotropic_rectangle_integral T R f hf]
  change (∫ r : ℝ in I,∫ q : ℝ in I,∫ y : Fin 2 → ℝ in B,f ![r,y 0,y 1,q])=_
  have heq (r : ℝ) := integral_integral_swap
    (f:=fun q (y : Fin 2 → ℝ) => f ![r,y 0,y 1,q]) (hq r)
  simp_rw [heq]
  exact integral_integral_swap (f:=fun r (y : Fin 2 → ℝ) =>
    ∫ q : ℝ in I,f ![r,y 0,y 1,q]) hr

private theorem bourgain_anisotropic_middle_average {K : ℝ} (hK : 0≤K)
    (T R : ℝ) (f : (Fin 4 → ℝ) → ℝ) (hf : Continuous f) (hf₀ : ∀ x,0≤f x) :
    (2*K)^2*(∫ x : Fin 4 → ℝ in Icc (-![T,R,R,T]) ![T,R,R,T],f x) ≤
      ∫ p : Fin 2 → ℝ in Icc (fun _ => -(R+K)) (fun _ => R+K),
        ∫ x : Fin 4 → ℝ in Icc (-![T,K,K,T]) ![T,K,K,T],
          f ![x 0,x 1+p 0,x 2+p 1,x 3] := by
  let I := Icc (-T) T
  let g := fun y : Fin 2 → ℝ => ∫ r : ℝ in I,∫ q : ℝ in I,f ![r,y 0,y 1,q]
  have hc : Continuous (Function.uncurry (fun (p : (Fin 2 → ℝ) × ℝ) (q : ℝ) =>
      f ![p.2,p.1 0,p.1 1,q])) :=
    hf.comp (by fun_prop)
  have hg₁ := continuous_parametric_integral_of_continuous (μ:=volume) hc
    (show IsCompact I from isCompact_Icc)
  have hg : Continuous g := by
    exact continuous_parametric_integral_of_continuous (μ:=volume) hg₁ isCompact_Icc
  have hg₀ (y : Fin 2 → ℝ) : 0≤g y :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => hf₀ _))
  have hh := bourgain_middle_rectangle_average hK (fun _ => R) g hg hg₀
  rw [bourgain_anisotropic_rectangle_integral_middle T R f hf]
  change (2*K)^2*(∫ y : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),g y)≤_
  apply hh.trans_eq
  apply integral_congr_ae
  filter_upwards with p
  have hfp : Continuous (fun x : Fin 4 → ℝ => f ![x 0,x 1+p 0,x 2+p 1,x 3]) :=
    hf.comp (by fun_prop)
  rw [bourgain_anisotropic_rectangle_integral_middle T K _ hfp]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with r
  apply integral_congr_ae
  filter_upwards with q
  change f ![r,p 0+y 0,p 1+y 1,q]=f ![r,y 0+p 0,y 1+p 1,q]
  simp only [add_comm]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
namespace TaoTrudgianYang2025

private theorem bourgain_affine_fine_cell {b δ w : ℝ} (hδ : 0<δ)
    (n : ℕ) (k : Fin (2^n))
    (hw : (w-b)/δ∈Icc (((k:ℕ):ℝ)/((2^n:ℕ):ℝ))
      ((((k:ℕ):ℝ)+1)/((2^n:ℕ):ℝ))) :
    w∈Icc (b+(δ/((2^n:ℕ):ℝ))*((k:ℕ):ℝ))
      (b+(δ/((2^n:ℕ):ℝ))*((k:ℕ):ℝ)+δ/((2^n:ℕ):ℝ)) := by
  have hlo := (le_div_iff₀ hδ).mp hw.1
  have hhi := (div_le_iff₀ hδ).mp hw.2
  have hleft : (((k:ℕ):ℝ)/((2^n:ℕ):ℝ))*δ =
      (δ/((2^n:ℕ):ℝ))*((k:ℕ):ℝ) := by ring
  have hright : ((((k:ℕ):ℝ)+1)/((2^n:ℕ):ℝ))*δ =
      (δ/((2^n:ℕ):ℝ))*((k:ℕ):ℝ)+δ/((2^n:ℕ):ℝ) := by ring
  rw [hleft] at hlo
  rw [hright] at hhi
  constructor <;> linarith

private theorem bourgain_canonical_fine_cell_mem {j : ℕ} (hj : 3≤j)
    (i : Fin (2^(2*j))) (k : Fin (2^(j+2))) {w : ℝ}
    (hw : w∈Icc (1/4:ℝ) 1)
    (hi : bourgainClosedFineCell (2*j) (Real.sqrt w)=i)
    (hk : bourgainClosedFineCell (j+2)
      ((w-(((i:ℕ):ℝ)/(2:ℝ)^(2*j))^2)/(2/(2:ℝ)^(2*j)))=k) :
    let N := (2:ℝ)^(2*j)
    let h := 2/(N*(2:ℝ)^(j+2))
    let a := (((i:ℕ):ℝ)/N)^2+h*((k:ℕ):ℝ)
    a∈Icc (1/4:ℝ) 1 ∧ w∈Icc a (a+h) := by
  let N := (2:ℝ)^(2*j)
  let b := (((i:ℕ):ℝ)/N)^2
  let δ := 2/N
  let h := 2/(N*(2:ℝ)^(j+2))
  have hN : 0<N := by dsimp [N]; positivity
  have hNnat : 0<(2^(2*j):ℕ) := by positivity
  have hn : 1≤2*j := by omega
  have hhalf := bourgainClosedFineCell_sqrt_half hn hw.1
  rw [hi] at hhalf
  have hb := bourgain_root_cell_base hNnat i hhalf
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hb
  have hw₀ : 0≤w := by linarith [hw.1]
  have hsqrt : Real.sqrt w∈Icc (0:ℝ) 1 :=
    ⟨Real.sqrt_nonneg w,by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw.2⟩
  have hroot := bourgainClosedFineCell_mem (2*j) hsqrt
  rw [hi] at hroot
  have hcoord := bourgain_root_cell_original_coordinate hNnat i hw₀ hroot
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hcoord
  have hcell := bourgainClosedFineCell_mem (j+2) hcoord
  change ((w-b)/δ)∈Icc
    (((bourgainClosedFineCell (j+2) ((w-b)/δ):ℕ):ℝ)/((2^(j+2):ℕ):ℝ))
    ((((bourgainClosedFineCell (j+2) ((w-b)/δ):ℕ):ℝ)+1)/((2^(j+2):ℕ):ℝ)) at hcell
  change bourgainClosedFineCell (j+2) ((w-b)/δ)=k at hk
  rw [hk] at hcell
  have ha := bourgain_affine_fine_cell (by dsimp [δ]; positivity) (j+2) k hcell
  have heh : δ/((2^(j+2):ℕ):ℝ)=h := by
    simp only [Nat.cast_pow,Nat.cast_ofNat]
    dsimp [δ,h]
    ring
  rw [heh] at ha
  have hbase : (1/4:ℝ)≤b+h*((k:ℕ):ℝ) :=
    le_add_of_le_of_nonneg hb.1.1 (by dsimp [h]; positivity)
  exact ⟨⟨hbase,ha.1.trans hw.2⟩,ha⟩

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

set_option maxHeartbeats 400000 in
private theorem bourgainSource_weighted_period_pair_fubini {ι κ : Type*}
    (S : Finset ι) (V : Finset κ) (z : ι → ℂ) (c : κ → ℂ)
    (w : ι → ℝ) (v : κ → ℝ) (T K R q : ℝ) (hK : 0<K) :
    let W := fun y : Fin 3 → ℝ => ∏ j, (1+(y j/K)^2)⁻¹
    (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
      (∫ y : Fin 3 → ℝ,W y*bourgainSourceShiftedPeriod S z w T y ![x 0,x 1,q])*
      (∫ y : Fin 3 → ℝ,W y*bourgainSourceShiftedPeriod V c v T y ![x 0,x 1,q])) =
    ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),W p.1*W p.2*
      (∫ x : Fin 2 → ℝ in Icc (fun _ => -R) (fun _ => R),
        bourgainSourceShiftedPeriod S z w T p.1 ![x 0,x 1,q]*
        bourgainSourceShiftedPeriod V c v T p.2 ![x 0,x 1,q]) := by
  let B := Icc (fun _ : Fin 2 => -R) (fun _ => R)
  let W := fun y : Fin 3 → ℝ => ∏ j, (1+(y j/K)^2)⁻¹
  let F := bourgainSourceShiftedPeriod S z w T
  let G := bourgainSourceShiftedPeriod V c v T
  let H := fun (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) (x : Fin 2 → ℝ) =>
    W p.1*W p.2*(F p.1 ![x 0,x 1,q]*G p.2 ![x 0,x 1,q])
  have hW : Integrable W :=
    Integrable.fintype_prod (fun _ : Fin 3 => integrable_inv_one_add_sq.comp_div hK.ne')
  have hmap₁ : Continuous (fun p : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      (p.1.1, (![p.2 0,p.2 1,q] : Fin 3 → ℝ))) := by fun_prop
  have hmap₂ : Continuous (fun p : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 2 → ℝ) =>
      (p.1.2, (![p.2 0,p.2 1,q] : Fin 3 → ℝ))) := by fun_prop
  have hFc := (continuous_bourgainSourceShiftedPeriod S z w T).comp hmap₁
  have hGc := (continuous_bourgainSourceShiftedPeriod V c v T).comp hmap₂
  have hc := hFc.mul hGc
  have hi1 : IntegrableOn (fun _x : Fin 2 → ℝ => (1:ℝ)) B :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hiH : Integrable (Function.uncurry H) ((volume.prod volume).prod (volume.restrict B)) := by
    have hh := ((hW.mul_prod hW).mul_prod hi1).mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        change ‖F p.1.1 ![p.2 0,p.2 1,q]*G p.1.2 ![p.2 0,p.2 1,q]‖≤_
        rw [norm_mul]
        exact mul_le_mul
          (bourgainSourceShiftedPeriod_norm_bound S z w T p.1.1 ![p.2 0,p.2 1,q])
          (bourgainSourceShiftedPeriod_norm_bound V c v T p.1.2 ![p.2 0,p.2 1,q])
          (norm_nonneg _) (by positivity)))
    simpa only [H,Function.uncurry,mul_one] using hh
  have he (x : Fin 2 → ℝ) :
      (∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),H p x)=
        (∫ y : Fin 3 → ℝ,W y*F y ![x 0,x 1,q])*
        (∫ y : Fin 3 → ℝ,W y*G y ![x 0,x 1,q]) := by
    calc
      _ = ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),
          (W p.1*F p.1 ![x 0,x 1,q])*(W p.2*G p.2 ![x 0,x 1,q]) := by
        apply integral_congr_ae
        filter_upwards with p
        dsimp [H]
        ring
      _ = _ := integral_prod_mul (μ:=volume) (ν:=volume)
        (fun y : Fin 3 → ℝ => W y*F y ![x 0,x 1,q])
        (fun y : Fin 3 → ℝ => W y*G y ![x 0,x 1,q])
  change (∫ x : Fin 2 → ℝ in B,
    (∫ y : Fin 3 → ℝ,W y*F y ![x 0,x 1,q])*
    (∫ y : Fin 3 → ℝ,W y*G y ![x 0,x 1,q]))=_
  simp_rw [←he]
  have hswap := integral_integral_swap (f:=H) hiH
  change (∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),∫ x : Fin 2 → ℝ in B,H p x)=
    (∫ x : Fin 2 → ℝ in B,∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),H p x) at hswap
  rw [←hswap]
  apply integral_congr_ae
  filter_upwards with p
  exact integral_const_mul _ _

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

private theorem bourgainSourcePeriod_integer_at {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {T : ℝ}
    (hT : T≠0) (q : Fin 3 → ℝ) :
    bourgainSourcePeriod S z (fun i => (m i:ℝ)/T) T q =
      ∫ u : ℝ in Icc (0:ℝ) 1,
        ‖∑ i∈S,z i*fordAdditiveCharacter ((m i:ℝ)*u+
          q 0*((m i:ℝ)/T)^2+q 1*((m i:ℝ)/T)^((3:ℝ)/2)+
          q 2*Real.sqrt ((m i:ℝ)/T))‖^6 := by
  unfold bourgainSourcePeriod bourgainSourceSixMoment
  apply integral_congr_ae
  filter_upwards with u
  apply congrArg (fun a : ℂ => ‖a‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun a : ℝ => z i*fordAdditiveCharacter a)
  change T*u*((m i:ℝ)/T)+q 0*((m i:ℝ)/T)^2+
    q 1*((m i:ℝ)/T)^((3:ℝ)/2)+q 2*Real.sqrt ((m i:ℝ)/T)=_
  field_simp

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_weighted_large_plane {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (b d δ T K ν : ℝ),
      b∈Icc (1/4:ℝ) 1 → d∈Icc (1/4:ℝ) 1 →
      δ∈Ioc (0:ℝ) (1/16) → 0<T → T≤K →
      (2*T^2)*δ^3≤32 → 2*T*δ^2≤32 →
      0<ν → ν≤|Real.sqrt b-Real.sqrt d| →
      ∀ (Q P : ℕ), 1≤Q → 1≤P →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ)
        (A D : ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ i∈S,(m i:ℝ)/T∈Icc b (b+δ)) →
        (∀ i∈V,(n i:ℝ)/T∈Icc d (d+δ)) →
        (∀ i∈S,A < m i ∧ m i≤A+Q) →
        (∀ i∈V,D < n i ∧ n i≤D+P) →
        (∀ k : ℤ,(∑ i∈S.filter (fun i => m i=k),‖z i‖)≤B) →
        (∀ k : ℤ,(∑ i∈V.filter (fun i => n i=k),‖c i‖)≤H) →
        (∫ x : Fin 2 → ℝ in Icc (fun _ => -2*T^2) (fun _ => 2*T^2),
          (∫ y : Fin 3 → ℝ,(∏ j : Fin 3,(1+(y j/K)^2)⁻¹)*
            bourgainSourceShiftedPeriod S z (fun i => (m i:ℝ)/T) T y ![x 0,x 1,0])*
          (∫ y : Fin 3 → ℝ,(∏ j : Fin 3,(1+(y j/K)^2)⁻¹)*
            bourgainSourceShiftedPeriod V c (fun i => (n i:ℝ)/T) T y ![x 0,x 1,0])) ≤
          (C/ν)*T^4*K^6*B^6*H^6*(Q:ℝ)^((3:ℝ)+ε)*(P:ℝ)^((3:ℝ)+ε) := by
  obtain ⟨E,hE,hbound⟩ := exists_bourgainSourceCurve_large_plane_quadratic_bound.{u} hε
  refine ⟨E*Real.pi^6,by positivity,?_⟩
  intro b d δ T K ν hb hd hδ hT hTK hscale hsmall hν hsep Q P hQ hP
    ι κ S V z c m n A D B H hB hH hSw hVw hSm hVn hz hc
  let w := fun i => (m i:ℝ)/T
  let v := fun i => (n i:ℝ)/T
  let W := fun y : Fin 3 → ℝ => ∏ j, (1+(y j/K)^2)⁻¹
  let L := Icc (fun _ : Fin 2 => -2*T^2) (fun _ => 2*T^2)
  let J := fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    ∫ x : Fin 2 → ℝ in L,
      bourgainSourceShiftedPeriod S z w T p.1 ![x 0,x 1,0]*
      bourgainSourceShiftedPeriod V c v T p.2 ![x 0,x 1,0]
  let M := (E/ν)*T^4*B^6*H^6*(Q:ℝ)^((3:ℝ)+ε)*(P:ℝ)^((3:ℝ)+ε)
  let zy := fun (y : Fin 3 → ℝ) i => z i*fordAdditiveCharacter
    (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))
  let cy := fun (y : Fin 3 → ℝ) i => c i*fordAdditiveCharacter
    (y 0*(v i)^2+y 1*(v i)^((3:ℝ)/2)+y 2*Real.sqrt (v i))
  have hK : 0<K := hT.trans_le hTK
  have hpoint (p : (Fin 3 → ℝ) × (Fin 3 → ℝ)) : J p≤M := by
    have hzy (k : ℤ) : (∑ i∈S.filter (fun i => m i=k),‖zy p.1 i‖)≤B := by
      simpa only [zy,norm_mul,sargos_character_norm,mul_one] using hz k
    have hcy (k : ℤ) : (∑ i∈V.filter (fun i => n i=k),‖cy p.2 i‖)≤H := by
      simpa only [cy,norm_mul,sargos_character_norm,mul_one] using hc k
    have hh := hbound b d δ T 0 ν hb hd hδ hT hscale hsmall (by simpa only [abs_zero] using mul_nonneg (by norm_num : (0:ℝ)≤2) hT.le)
      hν hsep Q P hQ hP ι κ S V (zy p.1) (cy p.2) m n A D B H
      hB hH hSw hVw hSm hVn hzy hcy
    dsimp only [J,bourgainSourceShiftedPeriod,w,v]
    simp_rw [bourgainSourcePeriod_integer_at _ _ _ hT.ne']
    exact hh
  have hW : Integrable W :=
    Integrable.fintype_prod (fun _ : Fin 3 => integrable_inv_one_add_sq.comp_div hK.ne')
  have hiJ : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => W p.1*W p.2*J p) := by
    have hh := (bourgainSource_radial_pair_period_entry (R:=2*T^2)
      S V z c m n hT hTK 0 0).1
    simpa only [W,J,L,w,v,neg_mul] using hh
  have hmajor := integral_mono hiJ ((hW.mul_prod hW).mul_const M)
    (fun p => mul_le_mul_of_nonneg_left (hpoint p) (by dsimp [W]; positivity))
  have hmass₁ : (∫ x : ℝ,(1+(x/K)^2)⁻¹)=K*Real.pi := by
    have hh := Measure.integral_comp_div (fun x : ℝ => (1+x^2)⁻¹) K
    simpa only [integral_univ_inv_one_add_sq,abs_of_pos hK,smul_eq_mul] using hh
  have hmass : (∫ y : Fin 3 → ℝ,W y)=(K*Real.pi)^3 := by
    dsimp only [W]
    change (∫ y : Fin 3 → ℝ,∏ j : Fin 3,(1+(y j/K)^2)⁻¹
      ∂Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)))=_
    rw [integral_fintype_prod_eq_prod (fun _ : Fin 3 => fun x : ℝ => (1+(x/K)^2)⁻¹)]
    simp only [hmass₁,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [integral_mul_const] at hmajor
  have he := integral_prod_mul (μ:=volume) (ν:=volume) W W
  change (∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),W p.1*W p.2)=
    (∫ y : Fin 3 → ℝ,W y)*(∫ y : Fin 3 → ℝ,W y) at he
  rw [he,hmass] at hmajor
  have hf := bourgainSource_weighted_period_pair_fubini S V z c w v T K (2*T^2) 0 hK
  dsimp only at hf
  calc
    _ = ∫ p : (Fin 3 → ℝ) × (Fin 3 → ℝ),W p.1*W p.2*J p := by
      simpa only [W,J,L,w,v,neg_mul] using hf
    _ ≤ ((K*Real.pi)^3*(K*Real.pi)^3)*M := hmajor
    _ = _ := by dsimp [M]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_canonical_fine_pair_bound {ε : ℝ} (hε : 0<ε) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j → ∀ (ν : ℝ), 0<ν →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      let δ := 2/N
      let Q : ℕ := 2^(j-1)+2
      1/N≤ν/2 →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ a∈S,(m a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈V,(n a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈S,∀ a'∈V,ν≤|Real.sqrt ((m a:ℝ)/T)-Real.sqrt ((n a':ℝ)/T)|) →
        (∀ k : ℤ,(∑ a∈S.filter (fun a => m a=k),‖z a‖)≤B) →
        (∀ k : ℤ,(∑ a∈V.filter (fun a => n a=k),‖c a‖)≤H) →
        ∀ (i i' : Fin (2^(2*j))) (k k' : Fin (2^(j+2))),
          let Sc := (S.filter (fun a => bourgainClosedFineCell (2*j)
            (Real.sqrt ((m a:ℝ)/T))=i)).filter (fun a => bourgainClosedFineCell (j+2)
              ((((m a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k)
          let Vc := (V.filter (fun a => bourgainClosedFineCell (2*j)
            (Real.sqrt ((n a:ℝ)/T))=i')).filter (fun a => bourgainClosedFineCell (j+2)
              ((((n a:ℝ)/T)-(((i':ℕ):ℝ)/N)^2)/δ)=k')
          (∫ x : Fin 2 → ℝ in Icc (fun _ => -2*T^2) (fun _ => 2*T^2),
            (∫ y : Fin 3 → ℝ,(∏ a : Fin 3,(1+(y a/(20*T))^2)⁻¹)*
              bourgainSourceShiftedPeriod Sc z (fun a => (m a:ℝ)/T) T y ![x 0,x 1,0])*
            (∫ y : Fin 3 → ℝ,(∏ a : Fin 3,(1+(y a/(20*T))^2)⁻¹)*
              bourgainSourceShiftedPeriod Vc c (fun a => (n a:ℝ)/T) T y ![x 0,x 1,0])) ≤
            (C/ν)*T^10*B^6*H^6*((Q:ℝ)^((3:ℝ)+ε))^2 := by
  classical
  obtain ⟨E,hE,hbound⟩ := exists_bourgainSource_weighted_large_plane.{u} hε
  refine ⟨2*E*20^6,by positivity,?_⟩
  intro j hj ν hν
  let N := (2:ℝ)^(2*j)
  let T := N^2
  let δ := 2/N
  let Q : ℕ := 2^(j-1)+2
  dsimp only
  intro hscale ι κ S V z c m n B H hB hH hw hv hsep hz hc i i' k k'
  let Sc := (S.filter (fun a => bourgainClosedFineCell (2*j)
    (Real.sqrt ((m a:ℝ)/T))=i)).filter (fun a => bourgainClosedFineCell (j+2)
      ((((m a:ℝ)/T)-(((i:ℕ):ℝ)/N)^2)/δ)=k)
  let Vc := (V.filter (fun a => bourgainClosedFineCell (2*j)
    (Real.sqrt ((n a:ℝ)/T))=i')).filter (fun a => bourgainClosedFineCell (j+2)
      ((((n a:ℝ)/T)-(((i':ℕ):ℝ)/N)^2)/δ)=k')
  let h := 2/(N*(2:ℝ)^(j+2))
  let b := (((i:ℕ):ℝ)/N)^2+h*((k:ℕ):ℝ)
  let d := (((i':ℕ):ℝ)/N)^2+h*((k':ℕ):ℝ)
  change (∫ x : Fin 2 → ℝ in Icc (fun _ => -2*T^2) (fun _ => 2*T^2),
    (∫ y : Fin 3 → ℝ,(∏ a : Fin 3,(1+(y a/(20*T))^2)⁻¹)*
      bourgainSourceShiftedPeriod Sc z (fun a => (m a:ℝ)/T) T y ![x 0,x 1,0])*
    (∫ y : Fin 3 → ℝ,(∏ a : Fin 3,(1+(y a/(20*T))^2)⁻¹)*
      bourgainSourceShiftedPeriod Vc c (fun a => (n a:ℝ)/T) T y ![x 0,x 1,0]))≤
    ((2*E*20^6)/ν)*T^10*B^6*H^6*((Q:ℝ)^((3:ℝ)+ε))^2
  have hSS : Sc⊆S := fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hVV : Vc⊆V := fun a ha => (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hSc (a : ι) (ha : a∈Sc) : b∈Icc (1/4:ℝ) 1 ∧ (m a:ℝ)/T∈Icc b (b+h) := by
    obtain ⟨ha,hka⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha,hia⟩ := Finset.mem_filter.mp ha
    exact bourgain_canonical_fine_cell_mem hj i k (hw a ha) hia hka
  have hVc (a : κ) (ha : a∈Vc) : d∈Icc (1/4:ℝ) 1 ∧ (n a:ℝ)/T∈Icc d (d+h) := by
    obtain ⟨ha,hka⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha,hia⟩ := Finset.mem_filter.mp ha
    exact bourgain_canonical_fine_cell_mem hj i' k' (hv a ha) hia hka
  by_cases hSe : Sc.Nonempty
  · by_cases hVe : Vc.Nonempty
    · obtain ⟨a,ha⟩ := hSe
      obtain ⟨a',ha'⟩ := hVe
      have hb := (hSc a ha).1
      have hd := (hVc a' ha').1
      have hp := bourgain_fine_dyadic_physics hj
      change h∈Ioc (0:ℝ) (1/16) ∧ (2*T^2)*h^3≤32 ∧
        2*T*h^2≤32 ∧ T*h=((2^(j-1):ℕ):ℝ) ∧
        1≤Q ∧ Q≤2^j ∧ 2*h≤1/N at hp
      have hT : 0<T := by dsimp [T,N]; positivity
      have hbd : ν/2≤|Real.sqrt b-Real.sqrt d| :=
        bourgain_fine_base_separation hb.1 hd.1 (hSc a ha).2 (hVc a' ha').2
          (hp.2.2.2.2.2.2.trans hscale) (hsep a (hSS ha) a' (hVV ha'))
      have hSm (a : ι) (ha : a∈Sc) :
          ⌊T*b⌋-1 < m a ∧ m a≤(⌊T*b⌋-1:ℤ)+Q :=
        bourgain_fine_cell_integer_interval hT hp.2.2.2.1 (hSc a ha).2
      have hVn (a : κ) (ha : a∈Vc) :
          ⌊T*d⌋-1 < n a ∧ n a≤(⌊T*d⌋-1:ℤ)+Q :=
        bourgain_fine_cell_integer_interval hT hp.2.2.2.1 (hVc a ha).2
      have hz' (l : ℤ) : (∑ a∈Sc.filter (fun a => m a=l),‖z a‖)≤B := by
        apply le_trans _ (hz l)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          have hh := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨hSS hh.1,hh.2⟩
        · intro a ha hna
          exact norm_nonneg _
      have hc' (l : ℤ) : (∑ a∈Vc.filter (fun a => n a=l),‖c a‖)≤H := by
        apply le_trans _ (hc l)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          have hh := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨hVV hh.1,hh.2⟩
        · intro a ha hna
          exact norm_nonneg _
      have hh := hbound b d h T (20*T) (ν/2) hb hd hp.1 hT (by linarith)
        hp.2.1 hp.2.2.1 (by positivity) hbd Q Q hp.2.2.2.2.1 hp.2.2.2.2.1
        ι κ Sc Vc z c m n (⌊T*b⌋-1) (⌊T*d⌋-1) B H hB hH
        (fun a ha => (hSc a ha).2) (fun a ha => (hVc a ha).2) hSm hVn hz' hc'
      exact hh.trans_eq (by ring)
    · have he : Vc=∅ := Finset.not_nonempty_iff_eq_empty.mp hVe
      rw [he]
      simp only [bourgainSourceShiftedPeriod,bourgainSourcePeriod,bourgainSourceSixMoment,
        Finset.sum_empty,norm_zero,zero_pow (by decide : (6:ℕ)≠0),mul_zero,integral_zero]
      positivity
  · have he : Sc=∅ := Finset.not_nonempty_iff_eq_empty.mp hSe
    rw [he]
    simp only [bourgainSourceShiftedPeriod,bourgainSourcePeriod,bourgainSourceSixMoment,
      Finset.sum_empty,norm_zero,zero_pow (by decide : (6:ℕ)≠0),mul_zero,zero_mul,integral_zero]
    positivity

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

set_option maxHeartbeats 400000 in
private theorem continuous_bourgainSource_weighted_period {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (T K : ℝ) (hK : 0<K) :
    Continuous (fun q : Fin 3 → ℝ => ∫ y : Fin 3 → ℝ,
      (∏ j : Fin 3,(1+(y j/K)^2)⁻¹)*bourgainSourceShiftedPeriod S z w T y q) := by
  let W := fun y : Fin 3 → ℝ => ∏ j, (1+(y j/K)^2)⁻¹
  have hWc : Continuous W := by
    dsimp only [W]
    apply continuous_finsetProd
    intro i hi
    apply Continuous.inv₀
    · fun_prop
    · intro y
      positivity
  have hW₀ (y : Fin 3 → ℝ) : 0≤W y := by dsimp [W]; positivity
  have hiW : Integrable W :=
    Integrable.fintype_prod (fun _ : Fin 3 => integrable_inv_one_add_sq.comp_div hK.ne')
  have hc := continuous_bourgainSourceShiftedPeriod S z w T
  apply continuous_of_dominated (bound:=fun y : Fin 3 → ℝ => W y*(∑ i∈S,‖z i‖)^6)
  · intro q
    exact (hWc.mul (hc.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro q
    filter_upwards with y
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hW₀ y)]
    exact mul_le_mul_of_nonneg_left (bourgainSourceShiftedPeriod_norm_bound S z w T y q) (hW₀ y)
  · exact hiW.mul_const _
  · filter_upwards with y
    have hmap : Continuous (fun q : Fin 3 → ℝ => (y,q)) := continuous_const.prodMk continuous_id
    have hcy := hc.comp hmap
    exact continuous_const.mul hcy

private theorem bourgainSourceSixMoment_middle_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (p : Fin 2 → ℝ) (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment S
      (fun i => z i*fordAdditiveCharacter (p 0*(w i)^2+p 1*(w i)^((3:ℝ)/2))) w x =
    bourgainSourceSixMoment S z w ![x 0,x 1+p 0,x 2+p 1,x 3] := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun a : ℂ => ‖a‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,←fordAdditiveCharacter_add]
  apply congrArg (fun a : ℝ => z i*fordAdditiveCharacter a)
  change (p 0*(w i)^2+p 1*(w i)^((3:ℝ)/2))+
    (x 0*w i+x 1*(w i)^2+x 2*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i))=
    x 0*w i+(x 1+p 0)*(w i)^2+(x 2+p 1)*(w i)^((3:ℝ)/2)+x 3*Real.sqrt (w i)
  ring

private theorem bourgainSourceShiftedPeriod_middle_modulation {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) (T : ℝ)
    (p : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    bourgainSourceShiftedPeriod S
      (fun i => z i*fordAdditiveCharacter (p 0*(w i)^2+p 1*(w i)^((3:ℝ)/2))) w T y 0 =
    bourgainSourceShiftedPeriod S z w T y ![p 0,p 1,0] := by
  unfold bourgainSourceShiftedPeriod bourgainSourcePeriod bourgainSourceSixMoment
  apply integral_congr_ae
  filter_upwards with u
  apply congrArg (fun a : ℂ => ‖a‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_assoc,←fordAdditiveCharacter_add]
  apply congrArg (fun a : ℝ => z i*fordAdditiveCharacter a)
  change ((p 0*(w i)^2+p 1*(w i)^((3:ℝ)/2))+
    (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i)))+
      (T*u*w i+0*(w i)^2+0*(w i)^((3:ℝ)/2)+0*Real.sqrt (w i))=
    (y 0*(w i)^2+y 1*(w i)^((3:ℝ)/2)+y 2*Real.sqrt (w i))+
      (T*u*w i+p 0*(w i)^2+p 1*(w i)^((3:ℝ)/2)+0*Real.sqrt (w i))
  ring

end TaoTrudgianYang2025

noncomputable section
open Set
namespace TaoTrudgianYang2025

private theorem bourgain_fine_count_scale {ε : ℝ} (hε : 0<ε)
    (j Q : ℕ) (hQ : Q≤2^j) :
    let N := (2:ℝ)^(2*j)
    ((((2^(2*j):ℕ):ℝ)*((2^(j+2):ℕ):ℝ))^2)*
      (((Q:ℝ)^((3:ℝ)+ε/4))^2) ≤
        16*N^6*(2:ℝ)^((ε/2)*j) := by
  let X := (2:ℝ)^j
  have hX : 0<X := by dsimp [X]; positivity
  have hN : (2:ℝ)^(2*j)=X^2 := by
    rw [Nat.mul_comm 2 j,pow_mul]
  have hF : (2:ℝ)^(j+2)=4*X := by
    rw [pow_add]
    dsimp [X]
    ring
  have hQ' : (Q:ℝ)≤X := by dsimp [X]; exact_mod_cast hQ
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg Q) hQ' (by positivity : 0≤(3:ℝ)+ε/4)
  have hXe : X^(ε/4)=(2:ℝ)^((ε/4)*j) := by
    dsimp [X]
    rw [←Real.rpow_natCast (2:ℝ) j,←Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have he : X^((3:ℝ)+ε/4)=X^3*(2:ℝ)^((ε/4)*j) := by
    rw [Real.rpow_add hX,hXe]
    norm_num
  have he₂ : ((2:ℝ)^((ε/4)*j))^2=(2:ℝ)^((ε/2)*j) := by
    rw [←Real.rpow_mul_natCast (by norm_num)]
    congr 1
    push_cast
    ring
  dsimp only
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [hN,hF]
  calc
    _ ≤ (X^2*(4*X))^2*(X^((3:ℝ)+ε/4))^2 := by
      gcongr
    _ = _ := by simp only [he,mul_pow,he₂]; ring

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

set_option maxHeartbeats 400000 in
private theorem exists_bourgainSource_large_anisotropic_original
    {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      1/N≤ν/2 →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ a∈S,(m a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈V,(n a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈S,∀ a'∈V,ν≤|Real.sqrt ((m a:ℝ)/T)-Real.sqrt ((n a':ℝ)/T)|) →
        (∀ k : ℤ,(∑ a∈S.filter (fun a => m a=k),‖z a‖)≤B) →
        (∀ k : ℤ,(∑ a∈V.filter (fun a => n a=k),‖c a‖)≤H) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,T^2,T^2,T]) ![T,T^2,T^2,T],
          bourgainSourceSixMoment S z (fun a => (m a:ℝ)/T) x*
          bourgainSourceSixMoment V c (fun a => (n a:ℝ)/T) x) ≤
          C*(2:ℝ)^(ε*j)*T^12*B^6*H^6 := by
  classical
  obtain ⟨A,hA,hsmall⟩ := exists_bourgainSource_small_anisotropic_original.{u}
    (by positivity : 0<ε/2) hν
  obtain ⟨D,hD,hfine⟩ := exists_bourgainSource_canonical_fine_pair_bound.{u}
    (by positivity : 0<ε/4)
  refine ⟨4*A*D/ν,by positivity,?_⟩
  intro j hj
  let N := (2:ℝ)^(2*j)
  let T := N^2
  dsimp only
  intro hscale ι κ S V z c m n B H hB hH hw hv hsep hz hc
  let Q : ℕ := 2^(j-1)+2
  let I := Fin (2^(2*j)) × Fin (2^(j+2))
  let w := fun a => (m a:ℝ)/T
  let v := fun a => (n a:ℝ)/T
  let Sc := fun a : I =>
    (S.filter (fun i => bourgainClosedFineCell (2*j) (Real.sqrt (w i))=a.1)).filter
      (fun i => bourgainClosedFineCell (j+2)
        ((w i-(((a.1:ℕ):ℝ)/N)^2)/(2/N))=a.2)
  let Vc := fun a : I =>
    (V.filter (fun i => bourgainClosedFineCell (2*j) (Real.sqrt (v i))=a.1)).filter
      (fun i => bourgainClosedFineCell (j+2)
        ((v i-(((a.1:ℕ):ℝ)/N)^2)/(2/N))=a.2)
  let W := fun y : Fin 3 → ℝ => ∏ a, (1+(y a/(20*T))^2)⁻¹
  let LS := fun (a : I) (p : Fin 2 → ℝ) => ∫ y : Fin 3 → ℝ,
    W y*bourgainSourceShiftedPeriod (Sc a) z w T y ![p 0,p 1,0]
  let LV := fun (a : I) (p : Fin 2 → ℝ) => ∫ y : Fin 3 → ℝ,
    W y*bourgainSourceShiftedPeriod (Vc a) c v T y ![p 0,p 1,0]
  let F := fun x : Fin 4 → ℝ =>
    bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x
  let G := fun p : Fin 2 → ℝ => (∑ a : I,LS a p)*(∑ a : I,LV a p)
  let U := Icc (-![T,N^3,N^3,T]) ![T,N^3,N^3,T]
  let P := Icc (fun _ : Fin 2 => -(T^2+N^3)) (fun _ => T^2+N^3)
  let L := Icc (fun _ : Fin 2 => -2*T^2) (fun _ => 2*T^2)
  let M := (D/ν)*T^10*B^6*H^6*((Q:ℝ)^((3:ℝ)+ε/4))^2
  let C₀ := A*(2:ℝ)^((ε/2)*j)*N^4
  let zp := fun (p : Fin 2 → ℝ) i =>
    z i*fordAdditiveCharacter (p 0*(w i)^2+p 1*(w i)^((3:ℝ)/2))
  let cp := fun (p : Fin 2 → ℝ) i =>
    c i*fordAdditiveCharacter (p 0*(v i)^2+p 1*(v i)^((3:ℝ)/2))
  have hN : 0<N := by dsimp [N]; positivity
  have hT : 0<T := by dsimp [T]; positivity
  have hK : 0<20*T := by positivity
  have hLS (a : I) : Continuous (LS a) :=
    (continuous_bourgainSource_weighted_period (Sc a) z w T (20*T) hK).comp (by fun_prop)
  have hLV (a : I) : Continuous (LV a) :=
    (continuous_bourgainSource_weighted_period (Vc a) c v T (20*T) hK).comp (by fun_prop)
  have hGc : Continuous G :=
    (continuous_finsetSum _ (fun a _ => hLS a)).mul (continuous_finsetSum _ (fun a _ => hLV a))
  have hG₀ (p : Fin 2 → ℝ) : 0≤G p := by
    apply mul_nonneg
    · apply Finset.sum_nonneg
      intro a ha
      exact integral_nonneg (fun y => mul_nonneg (by dsimp [W]; positivity)
        (bourgainSourceShiftedPeriod_nonneg _ _ _ _ _ _))
    · apply Finset.sum_nonneg
      intro a ha
      exact integral_nonneg (fun y => mul_nonneg (by dsimp [W]; positivity)
        (bourgainSourceShiftedPeriod_nonneg _ _ _ _ _ _))
  have hFc : Continuous F :=
    (continuous_bourgainSourceSixMoment S z w).mul (continuous_bourgainSourceSixMoment V c v)
  have hF₀ (x : Fin 4 → ℝ) : 0≤F x :=
    mul_nonneg (bourgainSourceSixMoment_nonneg _ _ _ _) (bourgainSourceSixMoment_nonneg _ _ _ _)
  have hpoint (p : Fin 2 → ℝ) :
      (∫ x : Fin 4 → ℝ in U,F ![x 0,x 1+p 0,x 2+p 1,x 3])≤C₀*G p := by
    have hh := hsmall j hj hscale ι κ S V (zp p) (cp p) m n hw hv hsep
    have heS := bourgainSourceSixMoment_middle_modulation S z w p
    have heV := bourgainSourceSixMoment_middle_modulation V c v p
    have hePS (Scell : Finset ι) := bourgainSourceShiftedPeriod_middle_modulation Scell z w T p
    have hePV (Vcell : Finset κ) := bourgainSourceShiftedPeriod_middle_modulation Vcell c v T p
    dsimp only [w,v,T,N] at heS heV hePS hePV
    dsimp only [zp,cp,w,v,T,N] at hh
    simp_rw [heS,heV,hePS,hePV] at hh
    simpa only [G,LS,LV,Sc,Vc,W,F,U,C₀,I,w,v,T,N,Fintype.sum_prod_type,mul_assoc] using hh
  have hshiftc : Continuous (Function.uncurry (fun (p : Fin 2 → ℝ) (x : Fin 4 → ℝ) =>
      F ![x 0,x 1+p 0,x 2+p 1,x 3])) := hFc.comp (by fun_prop)
  have houterc := continuous_parametric_integral_of_continuous (μ:=volume) hshiftc
    (show IsCompact U from isCompact_Icc)
  have hmain : (∫ p : Fin 2 → ℝ in P,
      ∫ x : Fin 4 → ℝ in U,F ![x 0,x 1+p 0,x 2+p 1,x 3])≤
      ∫ p : Fin 2 → ℝ in P,C₀*G p := setIntegral_mono_on
    (houterc.continuousOn.integrableOn_compact (show IsCompact P from isCompact_Icc))
    ((continuous_const.mul hGc).continuousOn.integrableOn_compact (show IsCompact P from isCompact_Icc))
    measurableSet_Icc (fun p _ => hpoint p)
  rw [integral_const_mul] at hmain
  have havg := bourgain_anisotropic_middle_average (K:=N^3) (by positivity) T (T^2) F hFc hF₀
  have hNP : N^3≤T^2 := by
    have hN₁ : 1≤N := one_le_pow₀ (by norm_num)
    calc
      N^3 ≤ N^4 := pow_le_pow_right₀ hN₁ (by decide : 3≤4)
      _ = T^2 := by dsimp only [T]; ring
  have hPL : P⊆L := by
    intro p hp
    constructor
    · intro a
      have ha := hp.1 a
      change -(T^2+N^3)≤p a at ha
      change -2*T^2≤p a
      linarith
    · intro a
      have ha := hp.2 a
      change p a≤T^2+N^3 at ha
      change p a≤2*T^2
      linarith
  have hmono : (∫ p : Fin 2 → ℝ in P,G p)≤∫ p : Fin 2 → ℝ in L,G p := setIntegral_mono_set
    (hGc.continuousOn.integrableOn_compact (show IsCompact L from isCompact_Icc))
    (Filter.Eventually.of_forall hG₀) (Filter.Eventually.of_forall hPL)
  have hi (a b : I) : IntegrableOn (fun p : Fin 2 → ℝ => LS a p*LV b p) L :=
    ((hLS a).mul (hLV b)).continuousOn.integrableOn_compact isCompact_Icc
  have hexpand : (∫ p : Fin 2 → ℝ in L,G p)=
      ∑ a : I,∑ b : I,∫ p : Fin 2 → ℝ in L,LS a p*LV b p := by
    dsimp only [G]
    simp_rw [Finset.sum_mul_sum]
    rw [integral_finsetSum Finset.univ (fun a _ =>
      integrable_finsetSum Finset.univ (fun b _ => hi a b))]
    apply Finset.sum_congr rfl
    intro a ha
    exact integral_finsetSum Finset.univ (fun b _ => hi a b)
  have hcell (a b : I) : (∫ p : Fin 2 → ℝ in L,LS a p*LV b p)≤M := by
    exact hfine j hj ν hν hscale ι κ S V z c m n B H hB hH hw hv hsep hz hc a.1 b.1 a.2 b.2
  have hcells : (∫ p : Fin 2 → ℝ in L,G p)≤
      ((((2^(2*j):ℕ):ℝ)*((2^(j+2):ℕ):ℝ))^2)*M := by
    rw [hexpand]
    calc
      _ ≤ ∑ _a : I,∑ _b : I,M :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hcell a b))
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_mul,I]
        ring
  have hcoef := bourgain_fine_count_scale hε j Q (bourgain_fine_dyadic_physics hj).2.2.2.2.2.1
  change ((((2^(2*j):ℕ):ℝ)*((2^(j+2):ℕ):ℝ))^2)*((Q:ℝ)^((3:ℝ)+ε/4))^2≤
    16*N^6*(2:ℝ)^((ε/2)*j) at hcoef
  have hpow : (2:ℝ)^((ε/2)*j)*(2:ℝ)^((ε/2)*j)=(2:ℝ)^(ε*j) := by
    rw [←Real.rpow_add (by norm_num)]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (by positivity : 0<(2*N^3)^2)).mp
  calc
    _ ≤ C₀*(∫ p : Fin 2 → ℝ in P,G p) := havg.trans hmain
    _ ≤ C₀*(((((2^(2*j):ℕ):ℝ)*((2^(j+2):ℕ):ℝ))^2)*M) :=
      mul_le_mul_of_nonneg_left (hmono.trans hcells) (by dsimp [C₀]; positivity)
    _ = C₀*((D/ν)*T^10*B^6*H^6)*
        (((((2^(2*j):ℕ):ℝ)*((2^(j+2):ℕ):ℝ))^2)*((Q:ℝ)^((3:ℝ)+ε/4))^2) := by
      dsimp [M]
      ring
    _ ≤ C₀*((D/ν)*T^10*B^6*H^6)*(16*N^6*(2:ℝ)^((ε/2)*j)) :=
      mul_le_mul_of_nonneg_left hcoef (by dsimp [C₀]; positivity)
    _ = (2*N^3)^2*((4*A*D/ν)*
        ((2:ℝ)^((ε/2)*j)*(2:ℝ)^((ε/2)*j))*T^12*B^6*H^6) := by
      dsimp [C₀,T]
      ring
    _ = _ := by rw [hpow]

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The original-source global larger-anisotropic bilinear moment. All cell
assignments, quadratic moments, unbounded shifts and physical scale losses
are derived. This is the dyadic bilinear large-rectangle estimate, not the
bilinear-to-linear first-spacing theorem or the analytic Bourgain pair. -/
theorem exists_bourgainSourceCurve_large_anisotropic_bilinear_bound
    {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ (j : ℕ), 3≤j →
      let N := (2:ℝ)^(2*j)
      let T := N^2
      1/N≤ν/2 →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ a∈S,(m a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈V,(n a:ℝ)/T∈Icc (1/4:ℝ) 1) →
        (∀ a∈S,∀ a'∈V,ν≤|Real.sqrt ((m a:ℝ)/T)-Real.sqrt ((n a':ℝ)/T)|) →
        (∀ k : ℤ,(∑ a∈S.filter (fun a => m a=k),‖z a‖)≤B) →
        (∀ k : ℤ,(∑ a∈V.filter (fun a => n a=k),‖c a‖)≤H) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,T^2,T^2,T]) ![T,T^2,T^2,T],
          ‖∑ a∈S,z a*fordAdditiveCharacter (x 0*((m a:ℝ)/T)+
            x 1*((m a:ℝ)/T)^2+x 2*((m a:ℝ)/T)^((3:ℝ)/2)+
            x 3*Real.sqrt ((m a:ℝ)/T))‖^6*
          ‖∑ a∈V,c a*fordAdditiveCharacter (x 0*((n a:ℝ)/T)+
            x 1*((n a:ℝ)/T)^2+x 2*((n a:ℝ)/T)^((3:ℝ)/2)+
            x 3*Real.sqrt ((n a:ℝ)/T))‖^6) ≤
          C*(2:ℝ)^(ε*j)*T^12*B^6*H^6 := by
  simpa only [bourgainSourceSixMoment] using
    exists_bourgainSource_large_anisotropic_original.{u} hε hν

end TaoTrudgianYang2025

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace TaoTrudgianYang2025
private theorem bourgain_rectangle_diagonal_integral
    {n : ℕ} (D a b : Fin n → ℝ) (hD : ∀ i, 0<D i)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ x in Icc (fun i => D i*a i) (fun i => D i*b i), f x) =
      (∏ i,D i)*(∫ x in Icc a b, f (fun i => D i*x i)) := by
  let L := (Matrix.toLin' (Matrix.diagonal D)).toContinuousLinearMap
  have hL (x : Fin n → ℝ) : L x = fun i => D i*x i := by
    ext i
    simp [L,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Matrix.diagonal]
  have hd : L.det=∏ i,D i := by
    simp [L,LinearMap.det_toLin']
  have hinj : Function.Injective L := by
    intro x y hxy
    funext i
    have hi := congrFun hxy i
    rw [hL,hL] at hi
    exact mul_left_cancel₀ (hD i).ne' hi
  have himg : L '' Icc a b=Icc (fun i => D i*a i) (fun i => D i*b i) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hL]
      exact ⟨fun i => mul_le_mul_of_nonneg_left (hx.1 i) (hD i).le,
        fun i => mul_le_mul_of_nonneg_left (hx.2 i) (hD i).le⟩
    · intro hy
      refine ⟨fun i => y i/D i,⟨?_,?_⟩,?_⟩
      · intro i
        exact (le_div_iff₀ (hD i)).mpr (by simpa only [mul_comm] using hy.1 i)
      · intro i
        exact (div_le_iff₀ (hD i)).mpr (by simpa only [mul_comm] using hy.2 i)
      · rw [hL]
        funext i
        exact mul_div_cancel₀ (y i) (hD i).ne'
  have h : (∫ x in L '' Icc a b,f x) =
      ∫ x in Icc a b, |L.det| • f (L x) :=
    integral_image_eq_integral_abs_det_fderiv_smul volume
      measurableSet_Icc (fun x _ => L.hasFDerivAt.hasFDerivWithinAt) hinj.injOn f
  rw [himg] at h
  simpa only [hd,hL,abs_of_pos (Finset.prod_pos (fun i _ => hD i)),
    smul_eq_mul,integral_const_mul] using h
end TaoTrudgianYang2025



noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
private theorem bourgainSourceSixMoment_dilate {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (w : ι → ℝ) {α : ℝ} (hα : 0<α)
    (hw : ∀ i∈S, 0≤w i) (x : Fin 4 → ℝ) :
    bourgainSourceSixMoment S z (fun i => α*w i) x =
      bourgainSourceSixMoment S z w
        ![α*x 0,α^2*x 1,α^((3:ℝ)/2)*x 2,Real.sqrt α*x 3] := by
  unfold bourgainSourceSixMoment
  apply congrArg (fun a : ℂ => ‖a‖^6)
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  congr 1
  change x 0*(α*w i)+x 1*(α*w i)^2+x 2*(α*w i)^((3:ℝ)/2)+
      x 3*Real.sqrt (α*w i)=
    α*x 0*w i+α^2*x 1*(w i)^2+α^((3:ℝ)/2)*x 2*(w i)^((3:ℝ)/2)+
      Real.sqrt α*x 3*Real.sqrt (w i)
  rw [Real.mul_rpow hα.le (hw i hi),Real.sqrt_mul hα.le,mul_pow]
  ring

private theorem bourgain_source_dilation_geometry {α : ℝ} (hα : α∈Icc (1/2:ℝ) 1) :
    let D : Fin 4 → ℝ := ![α,α^2,α^((3:ℝ)/2),Real.sqrt α]
    (∀ i, (1/4:ℝ)≤D i ∧ D i≤1) ∧ 0<(∏ i,D i) ∧ (∏ i,D i)≤1 := by
  have hα₀ : 0<α := by linarith [hα.1]
  have hs := Real.sq_sqrt hα₀.le
  have hs₀ := Real.sqrt_nonneg α
  have hslo : (1/2:ℝ)≤Real.sqrt α := by nlinarith [hα.1]
  have hshi : Real.sqrt α≤1 := by nlinarith [hα.2]
  have hr : α^((3:ℝ)/2)=α*Real.sqrt α := by
    calc
      _ = α^((1:ℝ)+1/2) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hα₀,Real.rpow_one,←Real.sqrt_eq_rpow]
  dsimp only
  have hd (i : Fin 4) :
      (1/4:ℝ)≤(![α,α^2,α^((3:ℝ)/2),Real.sqrt α] : Fin 4 → ℝ) i ∧
      (![α,α^2,α^((3:ℝ)/2),Real.sqrt α] : Fin 4 → ℝ) i≤1 := by
    fin_cases i
    · change (1/4:ℝ)≤α ∧ α≤1
      constructor <;> linarith [hα.1,hα.2]
    · change (1/4:ℝ)≤α^2 ∧ α^2≤1
      constructor <;> nlinarith [hα.1,hα.2]
    · change (1/4:ℝ)≤α^((3:ℝ)/2) ∧ α^((3:ℝ)/2)≤1
      rw [hr]
      constructor
      · nlinarith [hα.1,mul_nonneg (show 0≤α-1/2 by linarith [hα.1])
          (show 0≤Real.sqrt α-1/2 by linarith)]
      · nlinarith [mul_nonneg (show 0≤1-α by linarith [hα.2]) hs₀]
    · change (1/4:ℝ)≤Real.sqrt α ∧ Real.sqrt α≤1
      constructor <;> linarith
  refine ⟨hd,Finset.prod_pos (fun i _ => lt_of_lt_of_le (by norm_num) (hd i).1),?_⟩
  exact Finset.prod_le_one (fun i _ => le_trans (by norm_num) (hd i).1) (fun i _ => (hd i).2)
end TaoTrudgianYang2025



noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
private theorem bourgainSource_large_rectangle_dilate {ι κ : Type*}
    (S : Finset ι) (V : Finset κ) (z : ι → ℂ) (c : κ → ℂ)
    (w : ι → ℝ) (v : κ → ℝ) {α T R : ℝ}
    (hα : α∈Icc (1/2:ℝ) 1) (hT : 0<T) (hTR : 4*T≤R)
    (hw : ∀ i∈S,0≤w i) (hv : ∀ i∈V,0≤v i) :
    (∫ x : Fin 4 → ℝ in Icc (-![T,T^2,T^2,T]) ![T,T^2,T^2,T],
      bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x) ≤
    ∫ x : Fin 4 → ℝ in Icc (-![R,R^2,R^2,R]) ![R,R^2,R^2,R],
      bourgainSourceSixMoment S z (fun i => α*w i) x*
      bourgainSourceSixMoment V c (fun i => α*v i) x := by
  let D : Fin 4 → ℝ := ![α,α^2,α^((3:ℝ)/2),Real.sqrt α]
  let U : Fin 4 → ℝ := ![T,T^2,T^2,T]
  let W : Fin 4 → ℝ := ![R,R^2,R^2,R]
  let F := fun x : Fin 4 → ℝ =>
    bourgainSourceSixMoment S z w x*bourgainSourceSixMoment V c v x
  have hd := bourgain_source_dilation_geometry hα
  change (∀ i,(1/4:ℝ)≤D i ∧ D i≤1) ∧ 0<(∏ i,D i) ∧ (∏ i,D i)≤1 at hd
  have hα₀ : 0<α := by linarith [hα.1]
  have hR : 0<R := by linarith
  have hD (i : Fin 4) : 0<D i := lt_of_lt_of_le (by norm_num) (hd.1 i).1
  have hFc : Continuous F :=
    (continuous_bourgainSourceSixMoment S z w).mul (continuous_bourgainSourceSixMoment V c v)
  have hF₀ (x : Fin 4 → ℝ) : 0≤F x := by dsimp [F,bourgainSourceSixMoment]; positivity
  have hwidth (i : Fin 4) : U i≤D i*W i := by
    have hi := (hd.1 i).1
    have h₁ : T≤D i*R := by nlinarith
    have h₂ : T^2≤D i*R^2 := by
      have hRR : 16*T^2≤R^2 := by nlinarith
      nlinarith [mul_nonneg (show 0≤D i-1/4 by linarith) (sq_nonneg R)]
    fin_cases i
    · exact h₁
    · exact h₂
    · exact h₂
    · exact h₁
  have hsub : Icc (-U) U⊆Icc (fun i => D i*(-W i)) (fun i => D i*W i) := by
    intro x hx
    constructor
    · intro i
      have hi := hx.1 i
      change -U i≤x i at hi
      nlinarith [hwidth i]
    · intro i
      exact (hx.2 i).trans (hwidth i)
  have hmono : (∫ x in Icc (-U) U,F x)≤
      ∫ x in Icc (fun i => D i*(-W i)) (fun i => D i*W i),F x :=
    setIntegral_mono_set (hFc.continuousOn.integrableOn_compact isCompact_Icc)
      (Filter.Eventually.of_forall hF₀) (Filter.Eventually.of_forall hsub)
  have he (x : Fin 4 → ℝ) :
      F (fun i => D i*x i)=
        bourgainSourceSixMoment S z (fun i => α*w i) x*
        bourgainSourceSixMoment V c (fun i => α*v i) x := by
    rw [bourgainSourceSixMoment_dilate S z w hα₀ hw,
      bourgainSourceSixMoment_dilate V c v hα₀ hv]
    rfl
  have hj := bourgain_rectangle_diagonal_integral D (-W) W hD F
  have hI₀ : 0≤∫ x in Icc (-W) W,F (fun i => D i*x i) :=
    integral_nonneg (fun x => hF₀ _)
  have hle := mul_le_mul_of_nonneg_right hd.2.2 hI₀
  rw [one_mul] at hle
  have hh := hmono.trans (hj.le.trans hle)
  simpa only [U,W,he,F] using hh
end TaoTrudgianYang2025


noncomputable section
open Set
namespace TaoTrudgianYang2025
private theorem exists_bourgain_dyadic_scale {ν : ℝ} (hν : 0<ν) :
    ∃ L≥(1:ℝ), ∀ T : ℝ, 1≤T →
      ∃ j k : ℕ, 3≤j ∧ 0<k ∧
        let N := (2:ℝ)^(2*j)
        let R := N^2
        4*T≤R ∧ R≤L*T ∧ 1/N≤ν/4 ∧ ((k:ℝ)*T/R)∈Icc (1/2:ℝ) 1 := by
  obtain ⟨b,hb⟩ := pow_unbounded_of_one_lt (4/ν) (by norm_num : (1:ℝ)<4)
  let j₀ := max 3 b
  have hj₀ : 3≤j₀ := le_max_left _ _
  have hb₀ : b≤j₀ := le_max_right _ _
  have hbase : 4/ν≤(4:ℝ)^j₀ :=
    hb.le.trans (pow_le_pow_right₀ (by norm_num) hb₀)
  let L := (16:ℝ)^(j₀+1)
  have hL : 1≤L := one_le_pow₀ (by norm_num)
  refine ⟨L,hL,?_⟩
  intro T hT
  have hT₀ : 0<T := by linarith
  obtain ⟨a,ha,hTa⟩ := exists_nat_pow_near hT (by norm_num : (1:ℝ)<16)
  let j := j₀+a+1
  have hj : 3≤j := by dsimp [j]; omega
  have hj₀j : j₀≤j := by dsimp [j]; omega
  let N := (2:ℝ)^(2*j)
  let R := N^2
  have hN₀ : 0<N := by dsimp [N]; positivity
  have hR₀ : 0<R := by dsimp [R]; positivity
  have hN : N=(4:ℝ)^j := by
    dsimp only [N]
    rw [pow_mul]
    norm_num
  have hR : R=(16:ℝ)^j := by
    dsimp only [R]
    rw [hN,←pow_mul, Nat.mul_comm j 2,pow_mul]
    norm_num
  have hsplit : R=L*(16:ℝ)^a := by
    rw [hR]
    dsimp only [L,j]
    rw [show j₀+a+1=(j₀+1)+a by omega,pow_add]
  have hsplit' : R=(16:ℝ)^j₀*(16:ℝ)^(a+1) := by
    rw [hR]
    dsimp only [j]
    rw [show j₀+a+1=j₀+(a+1) by omega,pow_add]
  have hlarge : 4≤(16:ℝ)^j₀ := by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤16) (show 1≤j₀ by omega)
    norm_num at hp
    linarith
  have h4T : 4*T≤R := by
    rw [hsplit']
    exact (mul_le_mul_of_nonneg_right hlarge hT₀.le).trans
      (mul_le_mul_of_nonneg_left hTa.le (by positivity))
  have hRT : R≤L*T := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left ha (by positivity)
  have hsep : 1/N≤ν/4 := by
    have hNbase : 4/ν≤N := by
      rw [hN]
      exact hbase.trans (pow_le_pow_right₀ (by norm_num) hj₀j)
    have hx := (div_le_iff₀ hν).mp hNbase
    apply (div_le_iff₀ hN₀).mpr
    nlinarith
  have hratio : 1≤R/T := (le_div_iff₀ hT₀).mpr (by nlinarith)
  obtain ⟨d,hd,hrd⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hk : 0<(2^d:ℕ) := by positivity
  have hαlo : (1/2:ℝ)≤((2^d:ℕ):ℝ)*T/R := by
    push_cast
    apply (le_div_iff₀ hR₀).mpr
    have hx := (div_lt_iff₀ hT₀).mp hrd
    rw [pow_succ] at hx
    nlinarith
  have hαhi : ((2^d:ℕ):ℝ)*T/R≤1 := by
    push_cast
    apply (div_le_one hR₀).mpr
    exact (le_div_iff₀ hT₀).mp hd
  exact ⟨j,2^d,hj,hk,h4T,hRT,hsep,hαlo,hαhi⟩
end TaoTrudgianYang2025


noncomputable section
open Set
open scoped BigOperators
namespace TaoTrudgianYang2025
private theorem bourgain_integer_dilation_fiber_mass {ι : Type*}
    (S : Finset ι) (z : ι → ℂ) (m : ι → ℤ) {B : ℝ} (hB : 0≤B)
    (hm : ∀ q : ℤ,(∑ i∈S.filter (fun i => m i=q),‖z i‖)≤B)
    {k : ℤ} (hk : k≠0) (q : ℤ) :
    (∑ i∈S.filter (fun i => k*m i=q),‖z i‖)≤B := by
  classical
  by_cases he : (S.filter (fun i => k*m i=q)).Nonempty
  · obtain ⟨a,ha⟩ := he
    have ha' := (Finset.mem_filter.mp ha).2
    have hf : S.filter (fun i => k*m i=q)=S.filter (fun i => m i=m a) := by
      apply Finset.filter_congr
      intro i hi
      rw [←ha']
      exact mul_right_inj' hk
    rw [hf]
    exact hm (m a)
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact hB

private theorem bourgain_dyadic_epsilon_scale (ε : ℝ) (j : ℕ) :
    let N := (2:ℝ)^(2*j)
    let R := N^2
    (2:ℝ)^((4*ε)*j)*R^12=R^((12:ℝ)+ε) := by
  dsimp only
  have hR : ((2:ℝ)^(2*j))^2=(2:ℝ)^(4*j) := by
    rw [←pow_mul]
    congr 1
    omega
  have he : ((2:ℝ)^(4*j))^ε=(2:ℝ)^((4*ε)*j) := by
    rw [←Real.rpow_natCast (2:ℝ) (4*j),←Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hR,Real.rpow_add (by positivity),he]
  norm_num only [Real.rpow_ofNat]
  ring
end TaoTrudgianYang2025



noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u
private theorem exists_bourgainSource_all_real_scales {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ T : ℝ, 1≤T →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ i∈S,(m i:ℝ)/T∈Icc (1/2:ℝ) 1) →
        (∀ i∈V,(n i:ℝ)/T∈Icc (1/2:ℝ) 1) →
        (∀ i∈S,∀ a∈V,ν≤|Real.sqrt ((m i:ℝ)/T)-Real.sqrt ((n a:ℝ)/T)|) →
        (∀ q : ℤ,(∑ i∈S.filter (fun i => m i=q),‖z i‖)≤B) →
        (∀ q : ℤ,(∑ i∈V.filter (fun i => n i=q),‖c i‖)≤H) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,T^2,T^2,T]) ![T,T^2,T^2,T],
          bourgainSourceSixMoment S z (fun i => (m i:ℝ)/T) x*
          bourgainSourceSixMoment V c (fun i => (n i:ℝ)/T) x) ≤
            C*T^((12:ℝ)+ε)*B^6*H^6 := by
  obtain ⟨A,hA,hbound⟩ := exists_bourgainSourceCurve_large_anisotropic_bilinear_bound
    (show 0<4*ε by positivity) (show 0<ν/2 by positivity)
  obtain ⟨L,hL,hscale⟩ := exists_bourgain_dyadic_scale hν
  refine ⟨A*L^((12:ℝ)+ε),by positivity,?_⟩
  intro T hT ι κ S V z c m n B H hB hH hm hn hsep hz hc
  classical
  obtain ⟨j,k,hj,hk,h4T,hRT,hNsep,hα⟩ := hscale T hT
  let N := (2:ℝ)^(2*j)
  let R := N^2
  let α := (k:ℝ)*T/R
  let w := fun i => (m i:ℝ)/T
  let v := fun i => (n i:ℝ)/T
  change 4*T≤R at h4T
  change R≤L*T at hRT
  change 1/N≤ν/4 at hNsep
  change α∈Icc (1/2:ℝ) 1 at hα
  have hT₀ : 0<T := by linarith
  have hR₀ : 0<R := by dsimp [R,N]; positivity
  have hα₀ : 0<α := by linarith [hα.1]
  have he (a : ℤ) : (((k:ℤ)*a:ℤ):ℝ)/R=α*((a:ℝ)/T) := by
    dsimp only [α]
    push_cast
    field_simp
  have hfreq {s : ℝ} (hs : s∈Icc (1/2:ℝ) 1) : α*s∈Icc (1/4:ℝ) 1 := by
    constructor
    · have hh := mul_le_mul hα.1 hs.1 (by norm_num) hα₀.le
      norm_num at hh
      exact hh
    · exact mul_le_one₀ hα.2 (by linarith [hs.1]) hs.2
  have hm' (i : ι) (hi : i∈S) : (((k:ℤ)*m i:ℤ):ℝ)/R∈Icc (1/4:ℝ) 1 := by
    rw [he]
    exact hfreq (hm i hi)
  have hn' (i : κ) (hi : i∈V) : (((k:ℤ)*n i:ℤ):ℝ)/R∈Icc (1/4:ℝ) 1 := by
    rw [he]
    exact hfreq (hn i hi)
  have hsqrt : (1/2:ℝ)≤Real.sqrt α := by
    have hh := Real.sq_sqrt hα₀.le
    have hp := Real.sqrt_nonneg α
    nlinarith [hα.1]
  have hs (i : ι) (hi : i∈S) (a : κ) (ha : a∈V) :
      ν/2≤|Real.sqrt ((((k:ℤ)*m i:ℤ):ℝ)/R)-
        Real.sqrt ((((k:ℤ)*n a:ℤ):ℝ)/R)| := by
    rw [he,he,Real.sqrt_mul hα₀.le,Real.sqrt_mul hα₀.le,
      ←mul_sub,abs_mul,abs_of_nonneg (Real.sqrt_nonneg α)]
    have hh := mul_le_mul hsqrt (hsep i hi a ha) hν.le (Real.sqrt_nonneg α)
    nlinarith
  have hkz : (k:ℤ)≠0 := by exact_mod_cast hk.ne'
  have hh := hbound j hj (by simpa only [N,div_div,show (2:ℝ)*2=4 by norm_num] using hNsep)
    ι κ S V z c (fun i => (k:ℤ)*m i) (fun i => (k:ℤ)*n i) B H hB hH
    hm' hn' hs (bourgain_integer_dilation_fiber_mass S z m hB hz hkz)
      (bourgain_integer_dilation_fiber_mass V c n hH hc hkz)
  change (∫ x : Fin 4 → ℝ in Icc (-![R,R^2,R^2,R]) ![R,R^2,R^2,R],
      bourgainSourceSixMoment S z (fun i => (((k:ℤ)*m i:ℤ):ℝ)/R) x*
      bourgainSourceSixMoment V c (fun i => (((k:ℤ)*n i:ℤ):ℝ)/R) x) ≤
        A*(2:ℝ)^((4*ε)*j)*R^12*B^6*H^6 at hh
  simp_rw [he] at hh
  have hcompare := bourgainSource_large_rectangle_dilate S V z c w v hα hT₀ h4T
    (fun i hi => le_trans (by norm_num) (hm i hi).1)
    (fun i hi => le_trans (by norm_num) (hn i hi).1)
  have hpre := hcompare.trans hh
  have heps := bourgain_dyadic_epsilon_scale ε j
  change (2:ℝ)^((4*ε)*j)*R^12=R^((12:ℝ)+ε) at heps
  have hrpow : R^((12:ℝ)+ε)≤L^((12:ℝ)+ε)*T^((12:ℝ)+ε) := by
    calc
      _ ≤ (L*T)^((12:ℝ)+ε) := Real.rpow_le_rpow hR₀.le hRT (by positivity)
      _ = _ := Real.mul_rpow (by linarith) hT₀.le
  calc
    _ ≤ A*(2:ℝ)^((4*ε)*j)*R^12*B^6*H^6 := hpre
    _ = A*R^((12:ℝ)+ε)*B^6*H^6 := by rw [mul_assoc A _ _,heps]
    _ ≤ A*(L^((12:ℝ)+ε)*T^((12:ℝ)+ε))*B^6*H^6 := by gcongr
    _ = _ := by ring
end TaoTrudgianYang2025


noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025
universe u

/-- The literal original-source bilinear moment on comparable-frequency annuli,
for every real scale T>=1. Integer dilation, separation, coefficient fibers and
the actual rectangle Jacobian are derived; no dyadic or large-T restriction
remains. This is not the localized shifted-phase or linear first-spacing theorem. -/
theorem exists_bourgainSourceCurve_all_scale_bilinear_bound {ε ν : ℝ} (hε : 0<ε) (hν : 0<ν) :
    ∃ C>(0:ℝ), ∀ T : ℝ, 1≤T →
      ∀ (ι κ : Type u) (S : Finset ι) (V : Finset κ)
        (z : ι → ℂ) (c : κ → ℂ) (m : ι → ℤ) (n : κ → ℤ) (B H : ℝ),
        0≤B → 0≤H →
        (∀ i∈S,(m i:ℝ)/T∈Icc (1/2:ℝ) 1) →
        (∀ i∈V,(n i:ℝ)/T∈Icc (1/2:ℝ) 1) →
        (∀ i∈S,∀ a∈V,ν≤|Real.sqrt ((m i:ℝ)/T)-Real.sqrt ((n a:ℝ)/T)|) →
        (∀ q : ℤ,(∑ i∈S.filter (fun i => m i=q),‖z i‖)≤B) →
        (∀ q : ℤ,(∑ i∈V.filter (fun i => n i=q),‖c i‖)≤H) →
        (∫ x : Fin 4 → ℝ in Icc (-![T,T^2,T^2,T]) ![T,T^2,T^2,T],
          ‖∑ i∈S,z i*fordAdditiveCharacter (x 0*((m i:ℝ)/T)+
            x 1*((m i:ℝ)/T)^2+x 2*((m i:ℝ)/T)^((3:ℝ)/2)+
            x 3*Real.sqrt ((m i:ℝ)/T))‖^6*
          ‖∑ i∈V,c i*fordAdditiveCharacter (x 0*((n i:ℝ)/T)+
            x 1*((n i:ℝ)/T)^2+x 2*((n i:ℝ)/T)^((3:ℝ)/2)+
            x 3*Real.sqrt ((n i:ℝ)/T))‖^6) ≤
            C*T^((12:ℝ)+ε)*B^6*H^6 := by
  simpa only [bourgainSourceSixMoment] using
    exists_bourgainSource_all_real_scales.{u} hε hν

end TaoTrudgianYang2025
