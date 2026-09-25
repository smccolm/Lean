import TaoTrudgianYang2025.SargosDualTentKernel
import TaoTrudgianYang2025.SargosPlanarWindow
import GuthMaynard.ClassicalLargeValues
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.Chebyshev

/-! Two-sided finite large sieve via exact tent smoothing and literal near-pair counts. -/

noncomputable section
open MeasureTheory GafniTao Set
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem integrable_sargosRealTent_shift {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun x : ℝ => sargosRealTent a (x-c)) := by
  simpa only [sub_eq_add_neg] using (integrable_sargosRealTent ha).comp_add_right (-c)

theorem integral_sargosRealTent_shift {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (∫ x : ℝ, sargosRealTent a (x-c)) = a := by
  have h := integral_sargosRealTent_character_positive ha 0
  simp [fordAdditiveCharacter,sargosSincKernel] at h
  have ht : (∫ x : ℝ, sargosRealTent a x) = a := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    exact h
  simpa only [sub_eq_add_neg] using (integral_add_right_eq_self
    (μ := volume) (sargosRealTent a) (-c)).trans ht

theorem integral_sargosRealTent_shift_character {a : ℝ}
    (ha : 0 < a) (c u : ℝ) :
    (∫ x : ℝ, (sargosRealTent a (x-c):ℂ)*fordAdditiveCharacter (u*x)) =
      fordAdditiveCharacter (u*c)*(sargosSincKernel a u:ℂ) := by
  let F := fun x : ℝ => (sargosRealTent a (x-c):ℂ)*fordAdditiveCharacter (u*x)
  calc
    _ = ∫ x : ℝ, F (x+c) := (integral_add_right_eq_self (μ := volume) F c).symm
    _ = ∫ x : ℝ, fordAdditiveCharacter (u*c)*
        ((sargosRealTent a x:ℂ)*fordAdditiveCharacter (u*x)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [F]
        rw [add_sub_cancel_right,show u*(x+c)=u*c+u*x by ring,
          fordAdditiveCharacter_add]
        ring)
    _ = _ := by
      rw [integral_const_mul,integral_sargosRealTent_character_positive ha]

theorem integrable_sargosRealTent_shift_character {a : ℝ}
    (ha : 0 < a) (c u : ℝ) :
    Integrable (fun x : ℝ =>
      (sargosRealTent a (x-c):ℂ)*fordAdditiveCharacter (u*x)) := by
  have hc : Continuous (fun x : ℝ =>
      (sargosRealTent a (x-c):ℂ)*fordAdditiveCharacter (u*x)) := by
    have ht := continuous_sargosRealTent a
    unfold fordAdditiveCharacter
    fun_prop
  apply (integrable_sargosRealTent_shift ha c).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [norm_mul,sargos_character_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sargosRealTent_nonneg _ _)])

def sargosTentPacket (a b c d : ℝ) (p : ℝ × ℝ) : ℝ :=
  sargosRealTent a (p.1-c)*sargosRealTent b (p.2-d)

theorem continuous_sargosTentPacket (a b c d : ℝ) :
    Continuous (sargosTentPacket a b c d) := by
  have ha := continuous_sargosRealTent a
  have hb := continuous_sargosRealTent b
  unfold sargosTentPacket
  fun_prop

theorem integrable_sargosTentPacket {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    Integrable (sargosTentPacket a b c d) (volume.prod volume) :=
  (integrable_sargosRealTent_shift ha c).mul_prod
    (integrable_sargosRealTent_shift hb d)

theorem integral_sargosTentPacket {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (c d : ℝ) :
    (∫ p : ℝ × ℝ, sargosTentPacket a b c d p ∂(volume.prod volume)) = a*b := by
  unfold sargosTentPacket
  rw [integral_prod_mul (fun x : ℝ => sargosRealTent a (x-c))
    (fun y : ℝ => sargosRealTent b (y-d)),
    integral_sargosRealTent_shift ha,integral_sargosRealTent_shift hb]

theorem sargosTentPacket_nonneg (a b c d : ℝ) (p : ℝ × ℝ) :
    0 ≤ sargosTentPacket a b c d p :=
  mul_nonneg (sargosRealTent_nonneg _ _) (sargosRealTent_nonneg _ _)

theorem sargosTentPacket_le_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (c d : ℝ) (p : ℝ × ℝ) : sargosTentPacket a b c d p ≤ 1 := by
  have h := mul_le_mul (sargosRealTent_le_one ha (p.1-c))
    (sargosRealTent_le_one hb (p.2-d)) (sargosRealTent_nonneg _ _) (by norm_num : (0:ℝ) ≤ 1)
  simpa only [one_mul] using h

theorem sargosTentPacket_mul_eq_zero {a b c d c' d' : ℝ}
    (ha : 0 < a) (hb : 0 < b) (p : ℝ × ℝ)
    (hfar : 2*a ≤ |c-c'| ∨ 2*b ≤ |d-d'|) :
    sargosTentPacket a b c d p*sargosTentPacket a b c' d' p = 0 := by
  have hx {w u v x : ℝ} (hw : 0 < w) (h : 2*w ≤ |u-v|) :
      sargosRealTent w (x-u)*sargosRealTent w (x-v) = 0 := by
    by_cases h₁ : w ≤ |x-u|
    · rw [sargosRealTent_zero_of_le_abs hw h₁,zero_mul]
    · have h₂ : w ≤ |x-v| := by
        have ht : |u-v| ≤ |x-u|+|x-v| := by
          calc
            _ = |-(x-u)+(x-v)| := by congr 1; ring
            _ ≤ |-(x-u)|+|x-v| := abs_add_le _ _
            _ = _ := by rw [abs_neg]
        linarith
      rw [sargosRealTent_zero_of_le_abs hw h₂,mul_zero]
  unfold sargosTentPacket
  rcases hfar with h | h
  · have he := hx ha h (x := p.1)
    calc
      _ = (sargosRealTent a (p.1-c)*sargosRealTent a (p.1-c'))*
        (sargosRealTent b (p.2-d)*sargosRealTent b (p.2-d')) := by ring
      _ = 0 := by rw [he,zero_mul]
  · have he := hx hb h (x := p.2)
    calc
      _ = (sargosRealTent a (p.1-c)*sargosRealTent a (p.1-c'))*
        (sargosRealTent b (p.2-d)*sargosRealTent b (p.2-d')) := by ring
      _ = 0 := by rw [he,mul_zero]

theorem integrable_sargosTentPacket_character {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d u v : ℝ) :
    Integrable (fun p : ℝ × ℝ => (sargosTentPacket a b c d p:ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2)) (volume.prod volume) := by
  have h := (integrable_sargosRealTent_shift_character ha c u).mul_prod
    (integrable_sargosRealTent_shift_character hb d v)
  convert h using 1
  ext p
  simp only [sargosTentPacket,Complex.ofReal_mul,fordAdditiveCharacter_add]
  ring

theorem integral_sargosTentPacket_character {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (c d u v : ℝ) :
    (∫ p : ℝ × ℝ, (sargosTentPacket a b c d p:ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2) ∂(volume.prod volume)) =
      fordAdditiveCharacter (u*c+v*d)*
        ((sargosSincKernel a u*sargosSincKernel b v:ℝ):ℂ) := by
  have he (p : ℝ × ℝ) : (sargosTentPacket a b c d p:ℂ)*
      fordAdditiveCharacter (u*p.1+v*p.2) =
      ((sargosRealTent a (p.1-c):ℂ)*fordAdditiveCharacter (u*p.1))*
      ((sargosRealTent b (p.2-d):ℂ)*fordAdditiveCharacter (v*p.2)) := by
    simp only [sargosTentPacket,Complex.ofReal_mul,fordAdditiveCharacter_add]
    ring
  simp_rw [he]
  rw [integral_prod_mul
    (fun x : ℝ => (sargosRealTent a (x-c):ℂ)*fordAdditiveCharacter (u*x))
    (fun y : ℝ => (sargosRealTent b (y-d):ℂ)*fordAdditiveCharacter (v*y)),
    integral_sargosRealTent_shift_character ha,
    integral_sargosRealTent_shift_character hb,fordAdditiveCharacter_add,Complex.ofReal_mul]
  ring


def sargosTentCloud {ι : Type*} (S : Finset ι) (z : ι → ℂ) (x y : ι → ℝ)
    (a b : ℝ) (p : ℝ × ℝ) : ℂ :=
  ∑ i ∈ S, z i*(sargosTentPacket a b (x i) (y i) p:ℂ)

theorem continuous_sargosTentCloud {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x y : ι → ℝ) (a b : ℝ) :
    Continuous (sargosTentCloud S z x y a b) := by
  unfold sargosTentCloud
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_sargosTentPacket a b (x i) (y i)))

theorem sargosTentCloud_sq_pointwise {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x y : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (p : ℝ × ℝ) :
    ‖sargosTentCloud S z x y a b p‖^2 ≤
      ∑ ij ∈ sargosNearPairs S x y (2*a) (2*b),
        sargosTentPacket a b (x ij.1) (y ij.1) p := by
  classical
  let w := fun i => sargosTentPacket a b (x i) (y i) p
  have hw i : 0 ≤ w i := sargosTentPacket_nonneg _ _ _ _ _
  have hw1 i : w i ≤ 1 := sargosTentPacket_le_one ha hb _ _ _
  have hn : ‖sargosTentCloud S z x y a b p‖ ≤ ∑ i ∈ S, w i := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw i)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hz i hi) (hw i)
  calc
    _ ≤ (∑ i ∈ S, w i)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = ∑ ij ∈ S ×ˢ S, w ij.1*w ij.2 := by
      rw [pow_two,Finset.sum_mul_sum,Finset.sum_product]
    _ ≤ ∑ ij ∈ S ×ˢ S,
        if |x ij.1-x ij.2| ≤ 2*a ∧ |y ij.1-y ij.2| ≤ 2*b then w ij.1 else 0 := by
      apply Finset.sum_le_sum
      intro ij _
      split_ifs with h
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hw1 ij.2) (hw ij.1)
      · have hfar : 2*a ≤ |x ij.1-x ij.2| ∨ 2*b ≤ |y ij.1-y ij.2| := by
          by_cases hx : |x ij.1-x ij.2| ≤ 2*a
          · exact Or.inr (le_of_lt (lt_of_not_ge (fun hy => h ⟨hx,hy⟩)))
          · exact Or.inl (le_of_lt (lt_of_not_ge hx))
        exact le_of_eq (sargosTentPacket_mul_eq_zero ha hb p hfar)
    _ = _ := by
      simp only [sargosNearPairs,Finset.sum_filter,w]

theorem sargosTentCloud_energy_le_nearPairs {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x y : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) :
    Integrable (fun p : ℝ × ℝ => ‖sargosTentCloud S z x y a b p‖^2)
      (volume.prod volume) ∧
    (∫ p : ℝ × ℝ, ‖sargosTentCloud S z x y a b p‖^2 ∂(volume.prod volume)) ≤
      a*b*((sargosNearPairs S x y (2*a) (2*b)).card:ℝ) := by
  let P := sargosNearPairs S x y (2*a) (2*b)
  let W := fun p : ℝ × ℝ => ∑ ij ∈ P, sargosTentPacket a b (x ij.1) (y ij.1) p
  have hW : Integrable W (volume.prod volume) :=
    integrable_finsetSum _ (fun ij _ => integrable_sargosTentPacket ha hb _ _)
  have he : (∫ p : ℝ × ℝ, W p ∂(volume.prod volume)) = a*b*(P.card:ℝ) := by
    dsimp only [W]
    rw [integral_finsetSum _ (fun ij _ => integrable_sargosTentPacket ha hb _ _)]
    simp only [integral_sargosTentPacket ha hb,Finset.sum_const,nsmul_eq_mul]
    ring
  have hpt p := sargosTentCloud_sq_pointwise S z x y ha hb hz p
  have hi : Integrable (fun p : ℝ × ℝ => ‖sargosTentCloud S z x y a b p‖^2)
      (volume.prod volume) := by
    apply hW.mono' ((continuous_sargosTentCloud S z x y a b).norm.pow 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact hpt p)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ p : ℝ × ℝ, W p ∂(volume.prod volume) :=
      integral_mono_ae hi hW (Filter.Eventually.of_forall hpt)
    _ = _ := he

theorem sargosTentCloud_fourier_pairing {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (x y : ι → ℝ) (u v : κ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ p : ℝ × ℝ, sargosTentCloud S z x y a b p*
      sargosPlanarSum T w u v p.1 p.2 ∂(volume.prod volume)) =
      ∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (u j*x i+v j*y i)*
        ((sargosSincKernel a (u j)*sargosSincKernel b (v j):ℝ):ℂ) := by
  have he (p : ℝ × ℝ) :
      sargosTentCloud S z x y a b p*sargosPlanarSum T w u v p.1 p.2 =
      ∑ i ∈ S, ∑ j ∈ T, (z i*w j)*
        ((sargosTentPacket a b (x i) (y i) p:ℂ)*
          fordAdditiveCharacter (u j*p.1+v j*p.2)) := by
    unfold sargosTentCloud sargosPlanarSum
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (integrable_sargosTentPacket_character ha hb
      (x i) (y i) (u j) (v j)).const_mul (z i*w j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable_sargosTentPacket_character
    ha hb (x i) (y i) (u j) (v j)).const_mul (z i*w j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_sargosTentPacket_character ha hb]
  ring


private theorem sargos_norm_integral_mul_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F G : α → ℂ}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ)
    (hiF : Integrable (fun p => ‖F p‖^2) μ)
    (hiG : Integrable (fun p => ‖G p‖^2) μ) :
    ‖∫ p, F p*G p ∂μ‖^2 ≤
      (∫ p, ‖F p‖^2 ∂μ)*(∫ p, ‖G p‖^2 ∂μ) := by
  have hF2 := (memLp_two_iff_integrable_sq_norm hF).mpr hiF
  have hG2 := (memLp_two_iff_integrable_sq_norm hG).mpr hiG
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF2) (by simpa using hG2)
  have hn := norm_integral_le_integral_norm (μ := μ) (fun p => F p*G p)
  simp only [norm_mul] at hn
  have hs :
      ‖∫ p, F p*G p ∂μ‖ ≤
        Real.sqrt (∫ p, ‖F p‖^2 ∂μ)*Real.sqrt (∫ p, ‖G p‖^2 ∂μ) := by
    apply hn.trans
    simpa only [Real.rpow_two,← Real.sqrt_eq_rpow] using hh
  calc
    _ ≤ (Real.sqrt (∫ p, ‖F p‖^2 ∂μ)*Real.sqrt (∫ p, ‖G p‖^2 ∂μ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hs 2
    _ = _ := by
      rw [mul_pow,Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
        Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

theorem sargosTentCloud_zero_outside {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (x y : ι → ℝ) {a b c d δ lambda : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : ∀ i ∈ S, x i ∈ Icc c (c+δ))
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+lambda))
    (p : ℝ × ℝ)
    (hp : p ∉ Icc (c-a) (c+δ+a) ×ˢ Icc (d-b) (d+lambda+b)) :
    sargosTentCloud S z x y a b p = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  suffices hz : sargosTentPacket a b (x i) (y i) p = 0 by rw [hz]; simp
  unfold sargosTentPacket
  by_cases hxp : a ≤ |p.1-x i|
  · rw [sargosRealTent_zero_of_le_abs ha hxp,zero_mul]
  by_cases hyp : b ≤ |p.2-y i|
  · rw [sargosRealTent_zero_of_le_abs hb hyp,mul_zero]
  have hxp' := abs_lt.mp (lt_of_not_ge hxp)
  have hyp' := abs_lt.mp (lt_of_not_ge hyp)
  have hxi := hx i hi
  have hyi := hy i hi
  exfalso
  apply hp
  exact ⟨⟨by linarith [hxi.1,hxi.2],by linarith [hxi.1,hxi.2]⟩,
    ⟨by linarith [hyi.1,hyi.2],by linarith [hyi.1,hyi.2]⟩⟩

theorem sargos_tent_weighted_bilinear_bound {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (x y : ι → ℝ) (u v : κ → ℝ) {a b c d δ lambda : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hlambda : 0 < lambda)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, x i ∈ Icc c (c+δ))
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+lambda)) :
    ‖∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (u j*x i+v j*y i)*
        ((sargosSincKernel a (u j)*sargosSincKernel b (v j):ℝ):ℂ)‖^2 ≤
      16*a*b*(δ+2*a)*(lambda+2*b)*
        ((sargosNearPairs S x y (2*a) (2*b)).card:ℝ)*
        ((sargosNearPairs T u v (1/(δ+2*a)) (1/(lambda+2*b))).card:ℝ) := by
  let F := sargosTentCloud S z x y a b
  let G := fun p : ℝ × ℝ => sargosPlanarSum T w u v p.1 p.2
  let D := δ+2*a
  let L := lambda+2*b
  let U := Icc (c-a) (c-a+D) ×ˢ Icc (d-b) (d-b+L)
  let ν := (volume.prod volume).restrict U
  have hD : 0 < D := by dsimp [D]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have he : (∫ p : ℝ × ℝ, F p*G p ∂(volume.prod volume)) =
      ∫ p : ℝ × ℝ, F p*G p ∂ν := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    have heU : U = Icc (c-a) (c+δ+a) ×ˢ Icc (d-b) (d+lambda+b) := by
      dsimp [U,D,L]
      congr 2 <;> ring
    rw [heU] at hp
    have hf := sargosTentCloud_zero_outside S z x y ha hb hx hy p hp
    change F p*G p = 0
    rw [show F p = 0 from hf,zero_mul]
  obtain ⟨hiF,hFB⟩ := sargosTentCloud_energy_le_nearPairs S z x y ha hb hz
  have hiG : Integrable (fun p : ℝ × ℝ => ‖G p‖^2) ν := by
    simpa only [ν,U,Measure.prod_restrict] using
      integrable_sargosPlanarNormSq_rectangle T w u v (c-a) D (d-b) L
  have hG : Continuous G := by
    dsimp [G,sargosPlanarSum,fordAdditiveCharacter]
    fun_prop
  have hcs := sargos_norm_integral_mul_sq
    (continuous_sargosTentCloud S z x y a b).aestronglyMeasurable
    hG.aestronglyMeasurable hiF.integrableOn hiG
  have hFbound :
      (∫ p : ℝ × ℝ, ‖F p‖^2 ∂ν) ≤
        a*b*((sargosNearPairs S x y (2*a) (2*b)).card:ℝ) := by
    apply (setIntegral_le_integral hiF
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).trans hFB
  have hGbound :
      (∫ p : ℝ × ℝ, ‖G p‖^2 ∂ν) ≤
        16*D*L*((sargosNearPairs T u v (1/D) (1/L)).card:ℝ) := by
    change (∫ p in U, ‖G p‖^2 ∂(volume.prod volume)) ≤ _
    rw [setIntegral_prod (fun p : ℝ × ℝ => ‖G p‖^2) hiG]
    exact sargosPlanar_window_le_nearPairs T w u v hw hD hL (c-a) (d-b)
  rw [← sargosTentCloud_fourier_pairing S T z w x y u v ha hb,he]
  apply hcs.trans
  have hbnd := mul_le_mul hFbound hGbound
    (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)
  convert hbnd using 1
  dsimp [D,L]
  ring


/-- A finite two-dimensional double large sieve with literal near-pair counts. -/
theorem sargos_double_large_sieve_rectangle {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (z : ι → ℂ) (w : κ → ℂ)
    (x y : ι → ℝ) (u v : κ → ℝ) {a b c d δ lambda : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hlambda : 0 < lambda)
    (hz : ∀ i ∈ S, ‖z i‖ ≤ 1) (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, x i ∈ Icc c (c+δ))
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+lambda))
    (hu : ∀ j ∈ T, a*|u j| ≤ 1/2)
    (hv : ∀ j ∈ T, b*|v j| ≤ 1/2) :
    ‖∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (u j*x i+v j*y i)‖^2 ≤
      (4096*(δ+2*a)*(lambda+2*b)/(a*b))*
        ((sargosNearPairs S x y (2*a) (2*b)).card:ℝ)*
        ((sargosNearPairs T u v (1/(δ+2*a)) (1/(lambda+2*b))).card:ℝ) := by
  let t := a*b/16
  let K := fun j => sargosSincKernel a (u j)*sargosSincKernel b (v j)
  let w' := fun j => (t:ℂ)*w j/(K j:ℂ)
  have ht : 0 < t := by dsimp [t]; positivity
  have hK j (hj : j ∈ T) : t ≤ K j :=
    sargosSincKernel_rectangle_lower ha hb (hu j hj) (hv j hj)
  have hw' : ∀ j ∈ T, ‖w' j‖ ≤ 1 := by
    intro j hj
    have hk : 0 < K j := ht.trans_le (hK j hj)
    dsimp only [w']
    rw [norm_div,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos ht,abs_of_pos hk]
    apply (div_le_one hk).mpr
    exact (mul_le_mul_of_nonneg_left (hw j hj) ht.le).trans
      (by simpa only [mul_one] using hK j hj)
  have hbound := sargos_tent_weighted_bilinear_bound
    S T z w' x y u v ha hb hδ hlambda hz hw' hx hy
  have he :
      (∑ i ∈ S, ∑ j ∈ T, z i*w' j*fordAdditiveCharacter (u j*x i+v j*y i)*
        ((sargosSincKernel a (u j)*sargosSincKernel b (v j):ℝ):ℂ)) =
      (t:ℂ)*(∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (u j*x i+v j*y i)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    have hk : (K j:ℂ) ≠ 0 := by exact_mod_cast (ht.trans_le (hK j hj)).ne'
    change z i*((t:ℂ)*w j/(K j:ℂ))*fordAdditiveCharacter
        (u j*x i+v j*y i)*(K j:ℂ) =
      (t:ℂ)*(z i*w j*fordAdditiveCharacter (u j*x i+v j*y i))
    field_simp
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,mul_pow] at hbound
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp
  apply hbound.trans_eq
  dsimp only [t]
  field_simp
  ring


/-- The absolute outer sum is handled by the foundation's exact phase alignment. -/
theorem sargos_double_large_sieve_sum_norm {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
    (x y : ι → ℝ) (u v : κ → ℝ) {a b c d δ lambda : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ) (hlambda : 0 < lambda)
    (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hx : ∀ i ∈ S, x i ∈ Icc c (c+δ))
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+lambda))
    (hu : ∀ j ∈ T, a*|u j| ≤ 1/2)
    (hv : ∀ j ∈ T, b*|v j| ≤ 1/2) :
    (∑ i ∈ S, ‖∑ j ∈ T, w j*fordAdditiveCharacter (u j*x i+v j*y i)‖)^2 ≤
      (4096*(δ+2*a)*(lambda+2*b)/(a*b))*
        ((sargosNearPairs S x y (2*a) (2*b)).card:ℝ)*
        ((sargosNearPairs T u v (1/(δ+2*a)) (1/(lambda+2*b))).card:ℝ) := by
  let A := fun i => ∑ j ∈ T, w j*fordAdditiveCharacter (u j*x i+v j*y i)
  let z := fun i => RiemannZeta.GuthMaynard.phaseAlign (A i)
  have hz : ∀ i ∈ S, ‖z i‖ ≤ 1 := fun i _ =>
    RiemannZeta.GuthMaynard.norm_phaseAlign_le_one (A i)
  have h := sargos_double_large_sieve_rectangle
    S T z w x y u v ha hb hδ hlambda hz hw hx hy hu hv
  have he : (∑ i ∈ S, ∑ j ∈ T, z i*w j*fordAdditiveCharacter (u j*x i+v j*y i)) =
      ((∑ i ∈ S, ‖A i‖:ℝ):ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = z i*A i := by
        dsimp only [A]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := RiemannZeta.GuthMaynard.phaseAlign_mul (A i)
  rw [he,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at h
  exact h


def sargosIntegerNearPairs {ι : Type*} (S : Finset ι) (u : ι → ℤ)
    (v : ι → ℝ) (B : ℝ) : Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter (fun p => u p.1 = u p.2 ∧ |v p.1-v p.2| ≤ B)

def sargosPeriodicNearPairs {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (A B : ℝ) : Finset (ι × ι) := by
  classical
  exact (S ×ˢ S).filter
    (fun p => (∃ k : ℤ, |x p.1-x p.2-k| ≤ A) ∧ |y p.1-y p.2| ≤ B)

private theorem sargos_character_integer (n : ℤ) : fordAdditiveCharacter n = 1 := by
  unfold fordAdditiveCharacter
  have he : 2*Real.pi*Complex.I*((n:ℝ):ℂ) =
      (n:ℂ)*(2*Real.pi*Complex.I) := by
    push_cast
    ring
  rw [he,Complex.exp_int_mul_two_pi_mul_I]

theorem sargos_character_integer_fract (n : ℤ) (x : ℝ) :
    fordAdditiveCharacter ((n:ℝ)*Int.fract x) = fordAdditiveCharacter ((n:ℝ)*x) := by
  have he : (n:ℝ)*x = (n:ℝ)*Int.fract x+(n*⌊x⌋:ℤ) := by
    rw [Int.fract]
    push_cast
    ring
  conv_rhs => rw [he,fordAdditiveCharacter_add,sargos_character_integer,mul_one]

theorem sargos_fract_nearPairs_subset_periodic {ι : Type*}
    (S : Finset ι) (x y : ι → ℝ) (A B : ℝ) :
    sargosNearPairs S (fun i => Int.fract (x i)) y A B ⊆
      sargosPeriodicNearPairs S x y A B := by
  classical
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp'.1,⟨?_,hp'.2.2⟩⟩
  refine ⟨⌊x p.1⌋-⌊x p.2⌋,?_⟩
  have he : x p.1-x p.2-((⌊x p.1⌋-⌊x p.2⌋:ℤ):ℝ) =
      Int.fract (x p.1)-Int.fract (x p.2) := by
    simp only [Int.fract,Int.cast_sub]
    ring
  rw [he]
  exact hp'.2.1

theorem sargos_integer_nearPairs_subset {ι : Type*} (S : Finset ι)
    (u : ι → ℤ) (v : ι → ℝ) {A B E : ℝ} (hA : A < 1) (hB : B ≤ E) :
    sargosNearPairs S (fun i => (u i:ℝ)) v A B ⊆ sargosIntegerNearPairs S u v E := by
  classical
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  apply Finset.mem_filter.mpr
  refine ⟨hp'.1,⟨?_,hp'.2.2.trans hB⟩⟩
  have h : |((u p.1-u p.2:ℤ):ℝ)| < 1 := by
    rw [Int.cast_sub]
    exact hp'.2.1.trans_lt hA
  have hi : |u p.1-u p.2| < (1:ℤ) := by exact_mod_cast h
  have hi' := abs_lt.mp hi
  omega

/-- Periodic first coordinate and exact integer first-frequency collisions. -/
theorem sargos_double_large_sieve_integer {ι κ : Type*}
    (S : Finset ι) (T : Finset κ) (w : κ → ℂ)
    (x y : ι → ℝ) (u : κ → ℤ) (v : κ → ℝ) {X₁ X₂ d mu : ℝ}
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hmu : 0 < mu)
    (hw : ∀ j ∈ T, ‖w j‖ ≤ 1)
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+mu))
    (hu : ∀ j ∈ T, |(u j:ℝ)| ≤ X₁)
    (hv : ∀ j ∈ T, |v j| ≤ X₂) :
    (∑ i ∈ S, ‖∑ j ∈ T, w j*fordAdditiveCharacter ((u j:ℝ)*x i+v j*y i)‖)^2 ≤
      (16384*(1+X₁)*(1+mu*X₂))*
        ((sargosPeriodicNearPairs S x y (1/X₁) (1/X₂)).card:ℝ)*
        ((sargosIntegerNearPairs T u v (1/mu)).card:ℝ) := by
  let a := 1/(2*X₁)
  let b := 1/(2*X₂)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have h2a : 2*a = 1/X₁ := by dsimp [a]; ring
  have h2b : 2*b = 1/X₂ := by dsimp [b]; ring
  have hu' j (hj : j ∈ T) : a*|(u j:ℝ)| ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left (hu j hj) ha.le
    have he : a*X₁ = 1/2 := by dsimp [a]; field_simp
    rwa [he] at h
  have hv' j (hj : j ∈ T) : b*|v j| ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left (hv j hj) hb.le
    have he : b*X₂ = 1/2 := by dsimp [b]; field_simp
    rwa [he] at h
  have hx : ∀ i ∈ S, Int.fract (x i) ∈ Icc (0:ℝ) (0+1) :=
    fun i _ => ⟨Int.fract_nonneg _,by simpa using (Int.fract_lt_one (x i)).le⟩
  have h := sargos_double_large_sieve_sum_norm S T w
    (fun i => Int.fract (x i)) y (fun j => (u j:ℝ)) v ha hb
    (by norm_num : (0:ℝ) < 1) hmu hw hx hy hu' hv'
  have he i j : fordAdditiveCharacter ((u j:ℝ)*Int.fract (x i)+v j*y i) =
      fordAdditiveCharacter ((u j:ℝ)*x i+v j*y i) := by
    rw [fordAdditiveCharacter_add,fordAdditiveCharacter_add,sargos_character_integer_fract]
  simp only [he,h2a,h2b] at h
  have hthin : 1/(1+1/X₁) < 1 := by
    apply (div_lt_one (by positivity : 0 < 1+1/X₁)).mpr
    have hi : 0 < 1/X₁ := by positivity
    linarith
  have hvthin : 1/(mu+1/X₂) ≤ 1/mu :=
    one_div_le_one_div_of_le hmu (by
      have hi : 0 < 1/X₂ := by positivity
      linarith)
  have hcard₁ :
      ((sargosNearPairs S (fun i => Int.fract (x i)) y (1/X₁) (1/X₂)).card:ℝ) ≤
      ((sargosPeriodicNearPairs S x y (1/X₁) (1/X₂)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (sargos_fract_nearPairs_subset_periodic S x y _ _)
  have hcard₂ :
      ((sargosNearPairs T (fun j => (u j:ℝ)) v (1/(1+1/X₁)) (1/(mu+1/X₂))).card:ℝ) ≤
      ((sargosIntegerNearPairs T u v (1/mu)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (sargos_integer_nearPairs_subset T u v hthin hvthin)
  have hconstant : 4096*(1+1/X₁)*(mu+1/X₂)/(a*b) =
      16384*(1+X₁)*(1+mu*X₂) := by
    dsimp [a,b]
    field_simp
    ring
  rw [hconstant] at h
  apply h.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hcard₁ (by positivity)
  · exact hcard₂
  · positivity
  · positivity


/-- Summing the r-family retains the sum of the actual collision counts. -/
theorem sargos_double_large_sieve_family {ρ ι κ : Type*}
    (R : Finset ρ) (S : Finset ι) (T : ρ → Finset κ) (w : ρ → κ → ℂ)
    (x y : ι → ℝ) (u : ρ → κ → ℤ) (v : ρ → κ → ℝ) {X₁ X₂ d mu : ℝ}
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hmu : 0 < mu)
    (hw : ∀ r ∈ R, ∀ j ∈ T r, ‖w r j‖ ≤ 1)
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+mu))
    (hu : ∀ r ∈ R, ∀ j ∈ T r, |(u r j:ℝ)| ≤ X₁)
    (hv : ∀ r ∈ R, ∀ j ∈ T r, |v r j| ≤ X₂) :
    (∑ r ∈ R, ∑ i ∈ S,
      ‖∑ j ∈ T r, w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i)‖)^2 ≤
      (16384*(R.card:ℝ)*(1+X₁)*(1+mu*X₂))*
        ((sargosPeriodicNearPairs S x y (1/X₁) (1/X₂)).card:ℝ)*
        ∑ r ∈ R, ((sargosIntegerNearPairs (T r) (u r) (v r) (1/mu)).card:ℝ) := by
  let A := fun r => ∑ i ∈ S,
    ‖∑ j ∈ T r, w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i)‖
  let C := 16384*(1+X₁)*(1+mu*X₂)*
    ((sargosPeriodicNearPairs S x y (1/X₁) (1/X₂)).card:ℝ)
  let N := fun r => ((sargosIntegerNearPairs (T r) (u r) (v r) (1/mu)).card:ℝ)
  have hbound r (hr : r ∈ R) : (A r)^2 ≤ C*N r :=
    sargos_double_large_sieve_integer S (T r) (w r) x y (u r) (v r)
      hX₁ hX₂ hmu (hw r hr) hy (hu r hr) (hv r hr)
  have hcs := sq_sum_le_card_mul_sum_sq (s := R) (f := A)
  calc
    _ ≤ (R.card:ℝ)*∑ r ∈ R, (A r)^2 := hcs
    _ ≤ (R.card:ℝ)*∑ r ∈ R, C*N r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum]
      dsimp only [C,N]
      ring

/-- Exact finite partitioning before the sieve; no cross-block collisions are counted. -/
theorem sargos_double_large_sieve_partition {ρ ι κ : Type*}
    (R : Finset ρ) (S : Finset ι) (T : ρ → Finset κ) (w : ρ → κ → ℂ)
    (label : ρ → κ → ℕ) (J : ℕ)
    (x y : ι → ℝ) (u : ρ → κ → ℤ) (v : ρ → κ → ℝ) {X₁ X₂ d mu : ℝ}
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hmu : 0 < mu)
    (hw : ∀ r ∈ R, ∀ j ∈ T r, ‖w r j‖ ≤ 1)
    (hy : ∀ i ∈ S, y i ∈ Icc d (d+mu))
    (hu : ∀ r ∈ R, ∀ j ∈ T r, |(u r j:ℝ)| ≤ X₁)
    (hv : ∀ r ∈ R, ∀ j ∈ T r, |v r j| ≤ X₂)
    (hlabel : ∀ r ∈ R, ∀ j ∈ T r, label r j < J) :
    (∑ r ∈ R, ∑ i ∈ S,
      ‖∑ j ∈ T r, w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i)‖)^2 ≤
      (16384*(J:ℝ)*(R.card:ℝ)*(1+X₁)*(1+mu*X₂))*
        ((sargosPeriodicNearPairs S x y (1/X₁) (1/X₂)).card:ℝ)*
        ∑ k ∈ Finset.range J, ∑ r ∈ R,
          ((sargosIntegerNearPairs ((T r).filter (fun j => label r j = k))
            (u r) (v r) (1/mu)).card:ℝ) := by
  classical
  let A := fun k => ∑ r ∈ R, ∑ i ∈ S,
    ‖∑ j ∈ (T r).filter (fun j => label r j = k),
      w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i)‖
  let C := 16384*(R.card:ℝ)*(1+X₁)*(1+mu*X₂)*
    ((sargosPeriodicNearPairs S x y (1/X₁) (1/X₂)).card:ℝ)
  let N := fun k => ∑ r ∈ R,
    ((sargosIntegerNearPairs ((T r).filter (fun j => label r j = k))
      (u r) (v r) (1/mu)).card:ℝ)
  have hb (k : ℕ) : (A k)^2 ≤ C*N k :=
    sargos_double_large_sieve_family R S (fun r => (T r).filter (fun j => label r j = k))
      w x y u v hX₁ hX₂ hmu
      (fun r hr j hj => hw r hr j (Finset.mem_filter.mp hj).1) hy
      (fun r hr j hj => hu r hr j (Finset.mem_filter.mp hj).1)
      (fun r hr j hj => hv r hr j (Finset.mem_filter.mp hj).1)
  have hs :
      (∑ r ∈ R, ∑ i ∈ S,
        ‖∑ j ∈ T r, w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i)‖) ≤
      ∑ k ∈ Finset.range J, A k := by
    calc
      _ ≤ ∑ r ∈ R, ∑ i ∈ S, ∑ k ∈ Finset.range J,
          ‖∑ j ∈ (T r).filter (fun j => label r j = k),
            w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i)‖ := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro i _
        have he := Finset.sum_fiberwise_of_maps_to
          (fun j hj => Finset.mem_range.mpr (hlabel r hr j hj))
          (fun j => w r j*fordAdditiveCharacter ((u r j:ℝ)*x i+v r j*y i))
        rw [← he]
        exact norm_sum_le _ _
      _ = _ := by
        dsimp only [A]
        simp_rw [Finset.sum_comm (s := S) (t := Finset.range J)]
        rw [Finset.sum_comm]
  calc
    _ ≤ (∑ k ∈ Finset.range J, A k)^2 :=
      pow_le_pow_left₀
        (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))) hs 2
    _ ≤ (J:ℝ)*∑ k ∈ Finset.range J, (A k)^2 := by
      simpa only [Finset.card_range] using sq_sum_le_card_mul_sum_sq
        (s := Finset.range J) (f := A)
    _ ≤ (J:ℝ)*∑ k ∈ Finset.range J, C*N k :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hb k)) (Nat.cast_nonneg _)
    _ = _ := by
      rw [← Finset.mul_sum]
      dsimp only [C,N]
      ring

end TaoTrudgianYang2025
