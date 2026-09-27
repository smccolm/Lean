import TaoTrudgianYang2025.BetaCanonicalLegendre
import TaoTrudgianYang2025.BetaCanonicalTaylorLegendre
import TaoTrudgianYang2025.ExponentPairShiftUniformity
import TaoTrudgianYang2025.SargosWithinDerivativeCalculus
import TaoTrudgianYang2025.ExponentPairAllHeights
import TaoTrudgianYang2025.SargosDoubleLargeSieve
import TaoTrudgianYang2025.SargosQuarticPoisson
import TaoTrudgianYang2025.PositiveSlopeCharts
import TaoTrudgianYang2025.SquareProductCount
import TaoTrudgianYang2025.BourgainDyadicBands

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025.CubicNearCurvePrototype

private theorem finite_near_integer_count_fourier
    {ι : Type*} [DecidableEq ι] (S T : Finset ι) (φ : ι → ℝ)
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2) (hTS : T ⊆ S)
    (hnear : ∀ i∈T, ∃ e : ℤ, |φ i-(e:ℝ)| ≤ B/2) :
    (T.card:ℝ) ≤ 2*∑' r : ℤ, GafniTao.heathBrownHatFourierCoefficient B r *
      ‖∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ := by
  let c := GafniTao.heathBrownHatFourierCoefficient B
  let Z := fun r : ℤ => ∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hcS : Summable c := by
    have hh := GafniTao.summable_norm_heathBrownHatFourierTerm hB 0
    simpa only [mul_zero, GafniTao.fordAdditiveCharacter, Complex.ofReal_zero,
      zero_mul, Complex.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le _)] using hh
  have hZ r : ‖Z r‖ ≤ (S.card:ℝ) := by
    calc
      _ ≤ ∑ i∈S, ‖GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ := norm_sum_le _ _
      _ = _ := by
        simp [GafniTao.fordAdditiveCharacter, Complex.norm_exp]
  have habs : Summable (fun r => c r * ‖Z r‖) :=
    (hcS.mul_right (S.card:ℝ)).of_nonneg_of_le
      (fun r => mul_nonneg (hc r) (norm_nonneg _))
      (fun r => mul_le_mul_of_nonneg_left (hZ r) (hc r))
  have hnorm r : ‖(c r:ℂ)*Z r‖=c r*‖Z r‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc r)]
  have hseries : HasSum (fun r : ℤ => (c r:ℂ)*Z r)
      (∑ i∈S, (GafniTao.heathBrownHat B (φ i):ℂ)) := by
    simpa only [c,Z,Finset.mul_sum] using
      hasSum_sum (s:=S) (fun i _hi => GafniTao.hasSum_heathBrownHatFourierSeries hB hBHalf (φ i))
  have hsumpos : 0 ≤ ∑ i∈S, GafniTao.heathBrownHat B (φ i) :=
    Finset.sum_nonneg (fun i _hi => GafniTao.heathBrownHat_nonneg B (φ i))
  have hupper : (∑ i∈S, GafniTao.heathBrownHat B (φ i)) ≤
      ∑' r : ℤ, c r*‖Z r‖ := by
    have hh := norm_tsum_le_tsum_norm (habs.congr (fun r => (hnorm r).symm))
    rw [hseries.tsum_eq] at hh
    simpa only [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hsumpos,hnorm] using hh
  have hlower : (T.card:ℝ)/2 ≤ ∑ i∈S, GafniTao.heathBrownHat B (φ i) := by
    calc
      _ = ∑ _i∈T, (1/2:ℝ) := by simp; ring
      _ ≤ ∑ i∈T, GafniTao.heathBrownHat B (φ i) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨e,he⟩ := hnear i hi
        apply GafniTao.one_half_le_heathBrownHat hB
        exact (round_le (φ i) e).trans he
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hTS
        (fun i _hi _hnot => GafniTao.heathBrownHat_nonneg B (φ i))
  change (T.card:ℝ) ≤ 2*∑' r : ℤ, c r*‖Z r‖
  linarith only [hlower,hupper]

private theorem integer_rpow_tail
    {p : ℝ} (hp : p < -1) {R : ℕ} (hR : 0 < R) :
    let g := fun r : ℤ => if R < r.natAbs then |(r:ℝ)|^p else 0
    Summable g ∧ (∑' r : ℤ, g r) ≤ 2*(R:ℝ)^(p+1)/(-p-1) := by
  intro g
  let f := fun n : ℕ => if R < n then (n:ℝ)^p else 0
  have hf : Summable f := by
    apply ((Real.summable_nat_rpow.mpr hp).indicator {n | R < n}).congr
    intro n
    by_cases hn : R < n <;> simp [f,hn]
  have hg : Summable g := by
    have hs : Summable (fun r : ℤ => |(r:ℝ)|^p) := by
      simpa only [neg_neg] using Real.summable_abs_int_rpow (by linarith only [hp] : 1 < -p)
    apply (hs.indicator {r | R < r.natAbs}).congr
    intro r
    by_cases hr : R < r.natAbs <;> simp [g,hr]
  have hfinite : ∑ n∈Finset.range (R+1), f n=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hh := Finset.mem_range.mp hn
    simp only [f,if_neg (by omega : ¬ R < n)]
  have hshift := hf.sum_add_tsum_nat_add (R+1)
  rw [hfinite,zero_add] at hshift
  have hfun : (fun j : ℕ => f (j+(R+1)))=(fun j => ((j+R+1:ℕ):ℝ)^p) := by
    funext j
    simp only [f,if_pos (by omega : R < j+(R+1)),Nat.add_assoc]
  rw [hfun] at hshift
  have hnat : (∑' n : ℕ, f n) ≤ (R:ℝ)^(p+1)/(-p-1) := by
    rw [←hshift]
    exact tsum_nat_rpow_tail_le hp hR
  have hpS := hg.comp_injective (show Function.Injective (fun n : ℕ => (n:ℤ)) from Nat.cast_injective)
  have hmS := hg.comp_injective
    (show Function.Injective (fun n : ℕ => -((n:ℤ)+1)) from by
      intro a b he
      simp only [neg_inj,add_left_inj] at he
      exact_mod_cast he)
  have hplus : (fun n : ℕ => g n)=f := by
    funext n
    simp only [g,f,Int.natAbs_natCast,Int.cast_natCast,Nat.abs_cast]
  have hminus : (fun n : ℕ => g (-((n:ℤ)+1)))=(fun n => f (n+1)) := by
    funext n
    change g (-((n+1:ℕ):ℤ))=f (n+1)
    simp only [g,f,Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast,abs_neg,Nat.abs_cast]
  have hz : f 0=0 := by simp [f]
  have hshiftOne : (∑' n : ℕ, f (n+1))=∑' n : ℕ, f n := by
    simpa only [hz,zero_add] using hf.tsum_eq_zero_add.symm
  refine ⟨hg,?_⟩
  rw [tsum_of_nat_of_neg_add_one hpS hmS,hplus,hminus,hshiftOne]
  calc
    _ ≤ (R:ℝ)^(p+1)/(-p-1)+(R:ℝ)^(p+1)/(-p-1) := add_le_add hnat hnat
    _ = _ := by ring

private theorem hat_fourier_mass_and_decay
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2) :
    HasSum (GafniTao.heathBrownHatFourierCoefficient B) 1 ∧
    ∀ r : ℤ, r ≠ 0 → GafniTao.heathBrownHatFourierCoefficient B r ≤ 1/(B*(r:ℝ)^2) := by
  constructor
  · apply Complex.hasSum_ofReal.mp
    have hh := GafniTao.hasSum_heathBrownHatFourierSeries hB hBHalf 0
    simpa [GafniTao.fordAdditiveCharacter,GafniTao.heathBrownHat,
      GafniTao.heathBrownDistanceToInteger] using hh
  · intro r hr
    have hrR : (r:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hr
    have he := GafniTao.heathBrownHatFourierCoefficient_eq_fordTent hB r
    rw [GafniTao.fordTentFourierCoefficient_of_ne_zero hB.ne' hr] at he
    have heR : GafniTao.heathBrownHatFourierCoefficient B r=
        (Real.sin (Real.pi*(r:ℝ)*B))^2/(Real.pi^2*B*(r:ℝ)^2) :=
      Complex.ofReal_injective he
    rw [heR]
    have hsin : (Real.sin (Real.pi*(r:ℝ)*B))^2 ≤ 1 := by
      nlinarith only [Real.neg_one_le_sin (Real.pi*(r:ℝ)*B),
        Real.sin_le_one (Real.pi*(r:ℝ)*B)]
    have hpi : 1 ≤ Real.pi^2 := by nlinarith only [Real.pi_gt_three]
    exact div_le_div₀ (by norm_num) hsin (by positivity)
      (by have hh := mul_le_mul_of_nonneg_right hpi (by positivity : 0 ≤ B*(r:ℝ)^2)
          nlinarith only [hh])

private theorem hat_fourier_positive_moment
    {B p : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2)
    (hp : 0 ≤ p) (hp1 : p < 1) {R : ℕ} (hR : 0 < R) :
    let c := GafniTao.heathBrownHatFourierCoefficient B
    Summable (fun r : ℤ => c r*|(r:ℝ)|^p) ∧
    (∑' r : ℤ, c r*|(r:ℝ)|^p) ≤ (R:ℝ)^p+
      (2/B)*(R:ℝ)^(p-1)/(1-p) := by
  intro c
  let g := fun r : ℤ => if R < r.natAbs then |(r:ℝ)|^(p-2) else 0
  have htail := integer_rpow_tail (p:=p-2) (by linarith only [hp1]) hR
  have hmass := (hat_fourier_mass_and_decay hB hBHalf).1
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hmajor : Summable (fun r : ℤ => c r*(R:ℝ)^p+(1/B)*g r) :=
    (hmass.summable.mul_right _).add (htail.1.mul_left _)
  have hpoint r : c r*|(r:ℝ)|^p ≤ c r*(R:ℝ)^p+(1/B)*g r := by
    by_cases hr : R < r.natAbs
    · have hr0 : r ≠ 0 := by intro he; subst r; simp at hr
      have hx : 0 < |(r:ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hr0)
      have hdecay := (hat_fourier_mass_and_decay hB hBHalf).2 r hr0
      have heq : 1/(B*(r:ℝ)^2)*|(r:ℝ)|^p=(1/B)*|(r:ℝ)|^(p-2) := by
        rw [Real.rpow_sub hx,Real.rpow_two,sq_abs]
        ring
      have hh := mul_le_mul_of_nonneg_right hdecay (Real.rpow_nonneg (abs_nonneg (r:ℝ)) p)
      rw [heq] at hh
      change c r*|(r:ℝ)|^p ≤ c r*(R:ℝ)^p+(1/B)*(if R < r.natAbs then |(r:ℝ)|^(p-2) else 0)
      rw [if_pos hr]
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg (hc r) (by positivity)))
    · have hle : |(r:ℝ)| ≤ (R:ℝ) := by
        have hh : r.natAbs ≤ R := Nat.le_of_not_gt hr
        have hh' : (r.natAbs:ℝ) ≤ R := by exact_mod_cast hh
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'
      change c r*|(r:ℝ)|^p ≤ c r*(R:ℝ)^p+(1/B)*(if R < r.natAbs then |(r:ℝ)|^(p-2) else 0)
      rw [if_neg hr,mul_zero,add_zero]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hle hp) (hc r)
  have hsum : Summable (fun r : ℤ => c r*|(r:ℝ)|^p) :=
    hmajor.of_nonneg_of_le (fun r => mul_nonneg (hc r) (by positivity)) hpoint
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' r : ℤ, (c r*(R:ℝ)^p+(1/B)*g r) := Summable.tsum_le_tsum hpoint hsum hmajor
    _ = (R:ℝ)^p+(1/B)*(∑' r : ℤ, g r) := by
      rw [Summable.tsum_add (hmass.summable.mul_right _) (htail.1.mul_left _),
        tsum_mul_right,tsum_mul_left,hmass.tsum_eq,one_mul]
    _ ≤ (R:ℝ)^p+(1/B)*(2*(R:ℝ)^((p-2)+1)/(-(p-2)-1)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htail.2 (by positivity : 0 ≤ 1/B))
    _ = _ := by
      rw [show p-2+1=p-1 by ring,show -(p-2)-1=1-p by ring]
      ring


/-- Uniform Fourier power moment; the smoothing width remains free. -/
theorem cubic_hat_fourier_power_moment
    {B p : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2)
    (hp : 0 ≤ p) (hp1 : p < 1) :
    let c := GafniTao.heathBrownHatFourierCoefficient B
    Summable (fun r : ℤ => c r*|(r:ℝ)|^p) ∧
    (∑' r : ℤ, c r*|(r:ℝ)|^p) ≤ (2+2/(1-p))*B^(-p) := by
  intro c
  let R : ℕ := ⌈1/B⌉₊
  have hRlo : 1/B ≤ (R:ℝ) := Nat.le_ceil _
  have hR : 0 < R := by
    have hh : (0:ℝ) < R := (one_div_pos.mpr hB).trans_le hRlo
    exact_mod_cast hh
  have hRhi : (R:ℝ) ≤ 2/B := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 1/B by positivity)
    change (R:ℝ) < 1/B+1 at hh
    have h1 : 1 ≤ 1/B := (le_div_iff₀ hB).mpr (by linarith)
    calc
      _ ≤ 1/B+1/B := hh.le.trans (add_le_add le_rfl h1)
      _ = _ := by ring
  have hm := hat_fourier_positive_moment hB hBHalf hp hp1 hR
  have hhead : (R:ℝ)^p ≤ 2*B^(-p) := by
    calc
      _ ≤ (2/B)^p := Real.rpow_le_rpow (Nat.cast_nonneg R) hRhi hp
      _ = (2:ℝ)^p*B^(-p) := by
        rw [Real.div_rpow (by norm_num) hB.le,Real.rpow_neg hB.le]
        ring
      _ ≤ _ := by
        have hh : (2:ℝ)^p ≤ 2 := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1:ℝ) ≤ 2) hp1.le
        exact mul_le_mul_of_nonneg_right hh (by positivity)
  have htailpow : (R:ℝ)^(p-1) ≤ B^(1-p) := by
    calc
      _ ≤ (1/B)^(p-1) := Real.rpow_le_rpow_of_nonpos
        (one_div_pos.mpr hB) hRlo (by linarith)
      _ = _ := by
        rw [one_div,Real.inv_rpow hB.le,←Real.rpow_neg hB.le]
        congr 1
        ring
  have htail : (2/B)*(R:ℝ)^(p-1)/(1-p) ≤ (2/(1-p))*B^(-p) := by
    calc
      _ ≤ (2/B)*B^(1-p)/(1-p) := by gcongr
      _ = _ := by
        have he : B^(1-p)/B=B^(-p) := by
          rw [←Real.rpow_sub_one hB.ne']
          congr 1
          ring
        calc
          _ = (2/(1-p))*(B^(1-p)/B) := by ring
          _ = _ := by rw [he]
  exact ⟨hm.1,(hm.2.trans (add_le_add hhead htail)).trans_eq (by ring)⟩

/-- A free smoothing width, not tied to the physical Taylor length.
Only nonzero Fourier sums are inputs; zero frequency and the entire
absolutely convergent Fourier tail are proved here. -/
theorem cubic_near_integer_count_power
    {ι : Type*} [DecidableEq ι] (S T : Finset ι) (φ : ι → ℝ)
    {B A D p : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1/2)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hp : 0 ≤ p) (hp1 : p < 1)
    (hTS : T ⊆ S)
    (hnear : ∀ i∈T, ∃ e : ℤ, |φ i-(e:ℝ)| ≤ B/2)
    (hfreq : ∀ r : ℤ, r ≠ 0 →
      ‖∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)‖ ≤ A*|(r:ℝ)|^p+D) :
    (T.card:ℝ) ≤ 2*B*S.card+(4+4/(1-p))*A*B^(-p)+2*D := by
  let c := GafniTao.heathBrownHatFourierCoefficient B
  let Z := fun r : ℤ => ∑ i∈S, GafniTao.fordAdditiveCharacter ((r:ℝ)*φ i)
  let e := fun r : ℤ => if r=0 then B*(S.card:ℝ) else 0
  have hc r : 0 ≤ c r := GafniTao.heathBrownHatFourierCoefficient_nonneg hB.le r
  have hm := cubic_hat_fourier_power_moment hB hBHalf hp hp1
  have hmass := (hat_fourier_mass_and_decay hB hBHalf).1
  have he : HasSum e (B*(S.card:ℝ)) := hasSum_ite_eq _ _
  have hmajor : Summable (fun r : ℤ => e r+A*(c r*|(r:ℝ)|^p)+D*c r) :=
    (he.summable.add (hm.1.mul_left A)).add (hmass.summable.mul_left D)
  have hpoint r : c r*‖Z r‖ ≤ e r+A*(c r*|(r:ℝ)|^p)+D*c r := by
    by_cases hr : r=0
    · subst r
      have hZ : Z 0=(S.card:ℂ) := by simp [Z,GafniTao.fordAdditiveCharacter]
      rw [hZ]
      simp only [c,GafniTao.heathBrownHatFourierCoefficient_zero,
        Complex.norm_natCast,e,if_pos rfl]
      exact le_add_of_nonneg_right (add_nonneg
        (mul_nonneg hA (mul_nonneg hB.le (Real.rpow_nonneg (abs_nonneg _) p)))
        (mul_nonneg hD hB.le)) |>.trans_eq (by ring)
    · have hh := mul_le_mul_of_nonneg_left (hfreq r hr) (hc r)
      change c r*‖Z r‖ ≤ _ at hh
      change c r*‖Z r‖ ≤ (if r=0 then B*(S.card:ℝ) else 0)+
        A*(c r*|(r:ℝ)|^p)+D*c r
      rw [if_neg hr,zero_add]
      convert hh using 1
      ring
  have hs : Summable (fun r : ℤ => c r*‖Z r‖) :=
    hmajor.of_nonneg_of_le (fun r => mul_nonneg (hc r) (norm_nonneg _)) hpoint
  have hupper : (∑' r : ℤ, c r*‖Z r‖) ≤ B*S.card+(2+2/(1-p))*A*B^(-p)+D := by
    calc
      _ ≤ ∑' r : ℤ, (e r+A*(c r*|(r:ℝ)|^p)+D*c r) :=
        Summable.tsum_le_tsum hpoint hs hmajor
      _ = B*S.card+A*(∑' r : ℤ, c r*|(r:ℝ)|^p)+D := by
        rw [Summable.tsum_add (he.summable.add (hm.1.mul_left A)) (hmass.summable.mul_left D),
          Summable.tsum_add he.summable (hm.1.mul_left A),tsum_mul_left,tsum_mul_left,
          he.tsum_eq,hmass.tsum_eq,mul_one]
      _ ≤ B*S.card+A*((2+2/(1-p))*B^(-p))+D :=
        add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hm.2 hA)) le_rfl
      _ = _ := by ring
  have hcount := finite_near_integer_count_fourier S T φ hB hBHalf hTS hnear
  change (T.card:ℝ) ≤ 2*∑' r : ℤ, c r*‖Z r‖ at hcount
  exact hcount.trans ((mul_le_mul_of_nonneg_left hupper (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring))

#print axioms cubic_hat_fourier_power_moment
#print axioms cubic_near_integer_count_power

end TaoTrudgianYang2025.CubicNearCurvePrototype


noncomputable section
open Set Expdb Filter GafniTao
open scoped Topology ContDiff
open scoped BigOperators
namespace TaoTrudgianYang2025.DisplacementDualPrototype

/-- The actual normalized negative first derivative retains the complete
closed-interval model contract, including both endpoints. -/
theorem negative_first_derivative_model
    {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ} (hσ : 0 < σ)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ) :
    IsApproximateModelPhaseFunction
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u)
      (σ+1) P (δ/σ) := by
  refine ⟨contDiffOn_const.mul
    (sargos_contDiffOn_iteratedDerivWithin hF.1 uniqueDiffOn_phaseInterval 1),?_⟩
  intro p hp u
  have hu : 0 < (u:ℝ) := lt_of_lt_of_le zero_lt_one u.property.1
  have hw (τ : ℝ) (n : ℕ) :
      iteratedDerivWithin n (modelPhase τ) phaseInterval u =
        iteratedDeriv n (modelPhase τ) u :=
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval
      (Real.contDiffAt_rpow_const_of_ne hu.ne') u.property
  have hm : -σ⁻¹*iteratedDerivWithin (p+1) (modelPhase σ) phaseInterval u =
      iteratedDerivWithin p (modelPhase (σ+1)) phaseInterval u := by
    rw [hw,hw,modelPhase_iteratedDeriv_succ_parameter σ hu]
    field_simp
  have he : modelPhaseErrorAt
      (fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u) (σ+1) p u =
      -σ⁻¹*modelPhaseErrorAt F σ (p+1) u := by
    rw [modelPhaseErrorAt,iteratedDerivWithin_const_mul_field,
      sargos_iteratedDerivWithin_comp_order,← hm,← mul_sub]
    rfl
  rw [he,norm_mul,Real.norm_eq_abs,abs_neg,
    abs_of_pos (inv_pos.mpr hσ)]
  have h := mul_le_mul_of_nonneg_left (hF.2 (p+1) (by omega) u)
    (inv_nonneg.mpr hσ.le)
  simpa only [div_eq_mul_inv,mul_comm] using h

/-- Reuse of the completed Legendre and shift APIs, with both actual retained
slope windows and all uniform tolerances. This is not the D-process bound. -/
theorem double_dual_shift_uniformity
    {σ a b c d : ℝ} (hσ : 0 < σ)
    (ha : (2:ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1) (hba : b < 2*a)
    (hc : (2:ℝ)^(-(σ⁻¹+1)) < c) (hcd : c ≤ d) (hd : d < 1) (hdc : d < 2*c) :
    ∃ A B : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧ 0 < B ∧ B < c ∧ d < 2*B ∧
      ∃ χ ψ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        (∀ v∈Icc a b, χ v=1) ∧ (∀ w∈Icc c d, ψ w=1) ∧
        ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
        ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
          ∃ P : ℕ, 1 ≤ P ∧ ∀ (F : ℝ → ℝ) (η : ℝ),
            IsApproximateModelPhaseFunction F σ P δ → 0 < η → η ≤ η₀ →
            let L := canonicalLegendrePhase χ F σ A a
            let J := aProcessShiftPhase L σ⁻¹ η
            let G := canonicalLegendrePhase ψ J (σ⁻¹+1) B c
            Icc a b ⊆ modelPhaseSlopeRange F ∧
            Icc c d ⊆ modelPhaseSlopeRange J ∧
            IsApproximateModelPhaseFunction G (σ⁻¹+1)⁻¹ Q ε ∧
            (∀ v∈Icc a b, v/A∈Ioo (1:ℝ) 2 ∧
              L (v/A)=A^(σ⁻¹-1)*(modelPhaseLegendreDual F v-modelPhaseLegendreDual F a)+
                referenceModelPrimitive σ⁻¹ (a/A)) ∧
            (∀ w∈Icc c d, w/B∈Ioo (1:ℝ) 2 ∧
              G (w/B)=B^((σ⁻¹+1)⁻¹-1)*
                (modelPhaseLegendreDual J w-modelPhaseLegendreDual J c)+
                referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B)) := by
  have hs : 0 < σ⁻¹ := inv_pos.mpr hσ
  obtain ⟨A,hA,hAa,hbA,χ,hχ,hχc,hχone,hfirst⟩ :=
    modelPhaseLegendreDual_canonical_extension hσ ha hab hb hba
  obtain ⟨B,hB,hBc,hdB,ψ,hψ,hψc,hψone,hsecond⟩ :=
    modelPhaseLegendreDual_canonical_extension (show 0 < σ⁻¹+1 by linarith) hc hcd hd hdc
  refine ⟨A,B,hA,hAa,hbA,hB,hBc,hdB,χ,ψ,hχ,hχc,hψ,hψc,hχone,hψone,?_⟩
  intro Q ε hε
  obtain ⟨δ₂,hδ₂,_hδ₂small,hsecondModel⟩ := hsecond Q ε hε
  let Q₂ := legendreFiniteInputOrder (Q+1)
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model hs Q₂ hδ₂
  obtain ⟨δ,hδ,_hδsmall,hfirstModel⟩ := hfirst (Q₂+1) δ₁ hδ₁
  let P := max 1 (legendreFiniteInputOrder ((Q₂+1)+1))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,le_max_left _ _,?_⟩
  intro F η hF hη hηle L J G
  have hsource := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  obtain ⟨hwindow₁,hL,hLvalues⟩ := hfirstModel F hsource
  have hJ := hshift L η hL hη hηle
  obtain ⟨hwindow₂,hG,hGvalues⟩ := hsecondModel J hJ
  exact ⟨hwindow₁,hwindow₂,hG,hLvalues,hGvalues⟩

/-- The stationary phase of the actual difference of inverse slopes is
exactly the negative double Legendre phase; the displacement is derived. -/
theorem inverse_slope_shift_stationary_identity
    {σ δ k u : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hu : u∈modelPhaseSlopeRange F) (huk : u+k∈modelPhaseSlopeRange F) :
    let c := modelPhaseInverseSlope F
    let K := fun v => modelPhaseLegendreDual F v-modelPhaseLegendreDual F (v+k)
    let d := c u-c (u+k)
    HasDerivAt K d u ∧
      2*(F (c (u+k))-F (c u)-k*c (u+k)) = -2*(d*u-K u) := by
  intro c K d
  have hleft := modelPhaseLegendreDual_hasDerivAt hσ hδ hF hu
  have hright := (modelPhaseLegendreDual_hasDerivAt hσ hδ hF huk).comp u
    ((hasDerivAt_id u).add_const k)
  refine ⟨?_,?_⟩
  · simpa only [mul_one] using hleft.sub hright
  · dsimp only [c,K,d,modelPhaseLegendreDual]
    ring

/-- Exact parameter returned by the reused B-A-B model construction when
the incoming phase is the normalized negative first derivative. -/
theorem derivative_double_dual_parameter {σ : ℝ} (hσ : 0 < σ) :
    ((σ+1)⁻¹+1)⁻¹=(σ+1)/(σ+2) := by
  have h1 : σ+1 ≠ 0 := by positivity
  have h2 : σ+2 ≠ 0 := by positivity
  field_simp
  ring

/-- On a retained open window the canonical phase has the actual inverse
slope as its derivative, with the exact physical scaling factor. -/
theorem canonical_legendre_hasDerivAt
    {σ δ A a b v : ℝ} {F χ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hv : v ∈ Ioo a b)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1) :
    HasDerivAt (canonicalLegendrePhase χ F σ A a)
      (A^(σ⁻¹-1)*modelPhaseInverseSlope F v*A) (v/A) := by
  have he : canonicalLegendrePhase χ F σ A a =ᶠ[𝓝 (v/A)]
      fun x => A^(σ⁻¹-1)*(modelPhaseLegendreDual F (A*x)-modelPhaseLegendreDual F a)+
        referenceModelPrimitive σ⁻¹ (a/A) := by
    have hc : ContinuousAt (fun x:ℝ => A*x) (v/A) := by fun_prop
    have hn : Ioo a b ∈ 𝓝 (A*(v/A)) := by
      rw [mul_div_cancel₀ _ hA.ne']
      exact isOpen_Ioo.mem_nhds hv
    filter_upwards [hc.preimage_mem_nhds hn] with x hx
    have hz : 0 < A*x := ha.trans hx.1
    have hh := canonicalLegendrePhase_agrees (F:=F) (σ:=σ) hA ha hz
      (hχ (A*x) ⟨hx.1.le,hx.2.le⟩)
    simpa only [mul_div_cancel_left₀ _ hA.ne'] using hh
  have hd₀ : HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v)
      (A*(v/A)) := by
    simpa only [mul_div_cancel₀ _ hA.ne'] using
      modelPhaseLegendreDual_hasDerivAt hσ hδ hF (hwindow ⟨hv.1.le,hv.2.le⟩)
  have hd := hd₀.comp (v/A) ((hasDerivAt_id (v/A)).const_mul A)
  simp only [mul_one] at hd
  convert (((hd.sub_const (modelPhaseLegendreDual F a)).const_mul
    (A^(σ⁻¹-1))).add_const (referenceModelPrimitive σ⁻¹ (a/A))).congr_of_eventuallyEq
      he using 1
  ring

/-- The compressed shift of the actual first dual retains both its literal
value and its displacement derivative; no independent curve is supplied. -/
theorem canonical_shift_displacement
    {σ δ A a b η y : ℝ} {F χ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1)
    (hu : A*aProcessShiftPoint η 0 y ∈ Ioo a b)
    (huk : A*aProcessShiftPoint η 1 y ∈ Ioo a b) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let H := modelPhaseLegendreDual F
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalLegendrePhase χ F σ A a) σ⁻¹ η
    J y=s*(H u-H (u+k)) ∧ HasDerivAt J (s*A*(1-η)*d) y := by
  intro u k H d s J
  have hcoords : A*aProcessShiftPoint η 1 y = u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  have hval (t:ℝ) (ht:A*aProcessShiftPoint η t y∈Ioo a b) :=
    canonicalLegendrePhase_agrees (F:=F) (σ:=σ) hA ha (ha.trans ht.1)
      (hχ _ ⟨ht.1.le,ht.2.le⟩)
  constructor
  · have h0 := hval 0 hu
    have h1 := hval 1 huk
    simp only [mul_div_cancel_left₀ _ hA.ne'] at h0 h1
    dsimp only [J,aProcessShiftPhase]
    rw [h0,h1,hcoords]
    dsimp [s,u,H]
    ring
  · have hd (t:ℝ) (ht:A*aProcessShiftPoint η t y∈Ioo a b) :
        HasDerivAt (fun x => canonicalLegendrePhase χ F σ A a (aProcessShiftPoint η t x))
          (A^(σ⁻¹-1)*modelPhaseInverseSlope F (A*aProcessShiftPoint η t y)*A*(1-η)) y := by
      have hh := canonical_legendre_hasDerivAt hσ hδ hF hA ha ht hwindow hχ
      rw [mul_div_cancel_left₀ _ hA.ne'] at hh
      convert hh.comp y
        (((hasDerivAt_id y).const_mul (1-η)).add_const ((1+t)*η)) using 1
      simp
    have h0 := hd 0 hu
    have h1 := hd 1 huk
    have hj := (h0.sub h1).div_const (σ⁻¹*η)
    rw [hcoords] at hj
    convert hj using 1
    dsimp [J,aProcessShiftPhase,aProcessShiftPoint,s,d,u]
    ring

/-- Exact retained double-dual value for the actual displacement resonance.
The compression contributes the explicit linear term, which is not dropped. -/
theorem canonical_double_dual_resonance
    {σ δ δJ A B a b c η y : ℝ} {F χ ψ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1) (hy : y∈Ioo (1:ℝ) 2)
    (hu : A*aProcessShiftPoint η 0 y ∈ Ioo a b)
    (huk : A*aProcessShiftPoint η 1 y ∈ Ioo a b) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalLegendrePhase χ F σ A a) σ⁻¹ η
    let w := s*A*(1-η)*d
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w → ψ w=1 →
    canonicalLegendrePhase ψ J (σ⁻¹+1) B c (w/B) =
      B^((σ⁻¹+1)⁻¹-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
        referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  intro u k d s J w R hJ hw hψ
  have hcoords : A*aProcessShiftPoint η 1 y=u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  obtain ⟨hval,hderiv⟩ := canonical_shift_displacement hσ hδ hF hA ha
    hwindow hχ hu huk
  change J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) at hval
  change HasDerivAt J w y at hderiv
  have hinv : modelPhaseInverseSlope J w=y := by
    rw [← hderiv.deriv]
    exact modelPhaseInverseSlope_deriv (by positivity) hδJ hJ hy
  have hR := (inverse_slope_shift_stationary_identity hσ hδ hF
    (hwindow ⟨hu.1.le,hu.2.le⟩)
    (show u+k∈modelPhaseSlopeRange F by
      rw [← hcoords]
      exact hwindow ⟨huk.1.le,huk.2.le⟩)).2
  change R = -2*(d*u-(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k))) at hR
  have hdual : modelPhaseLegendreDual J w = -s/2*R-s*k*d := by
    rw [modelPhaseLegendreDual,hinv,hval,hR]
    dsimp [w,u,k,aProcessShiftPoint]
    ring
  rw [canonicalLegendrePhase_agrees hB hc hw hψ,hdual]

/-- An analytic exponent pair applies to the double dual computed from the
original model, with all constants chosen before the phase and physical scales.
The separate chart identity above is still needed for the resonance sum. -/
theorem source_double_dual_exponent_pair_bound
    {σ a b c d k l ε : ℝ} (hσ : 0 < σ) (hpair : ExponentPair k l) (hε : 0 < ε)
    (ha : (2:ℝ)^(-(σ+1)) < a) (hab : a ≤ b) (hb : b < 1) (hba : b < 2*a)
    (hc : (2:ℝ)^(-((σ+1)⁻¹+1)) < c) (hcd : c ≤ d) (hd : d < 1) (hdc : d < 2*c) :
    ∃ A B : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧ 0 < B ∧ B < c ∧ d < 2*B ∧
      ∃ χ ψ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
        (∀ v∈Icc a b, χ v=1) ∧ (∀ w∈Icc c d, ψ w=1) ∧
        ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
          ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
            ∀ (F : ℝ → ℝ) (η T N : ℝ) (m n : ℕ),
              IsApproximateModelPhaseFunction F σ P δ → 0 < η → η ≤ η₀ →
              0 < T → 1 ≤ N → N ≤ (m:ℝ) → (n:ℝ) ≤ 2*N →
              let F₁ := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
              let L := canonicalLegendrePhase χ F₁ (σ+1) A a
              let J := aProcessShiftPhase L (σ+1)⁻¹ η
              let G := canonicalLegendrePhase ψ J ((σ+1)⁻¹+1) B c
              Icc a b ⊆ modelPhaseSlopeRange F₁ ∧
              Icc c d ⊆ modelPhaseSlopeRange J ∧
              ‖exponentialSumAt G T N m n‖ ≤
                C*((T/N)^(k+ε)*N^(l+ε)+N/T) := by
  have hs : 0 < σ+1 := by positivity
  have ht : 0 < ((σ+1)⁻¹+1)⁻¹ := by positivity
  obtain ⟨A,B,hA,hAa,hbA,hB,hBc,hdB,χ,ψ,hχ,hχc,hψ,hψc,hχone,hψone,hmodels⟩ :=
    double_dual_shift_uniformity hs ha hab hb hba hc hcd hd hdc
  obtain ⟨δG,hδG,Q,_hQ,C,hC,hbound⟩ := hpair.allPositiveHeight_bound ht hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,P,hP,hall⟩ := hmodels Q δG hδG
  refine ⟨A,B,hA,hAa,hbA,hB,hBc,hdB,χ,ψ,hχ,hχc,hψ,hψc,hχone,hψone,
    σ*δ,η₀,mul_pos hσ hδ,hη₀,hηhalf,P+1,by omega,C,hC,?_⟩
  intro F η T N m n hF hη hηle hT hN hm hn F₁ L J G
  have hF₁ := negative_first_derivative_model hσ hF
  rw [mul_div_cancel_left₀ _ hσ.ne'] at hF₁
  obtain ⟨hwindow₁,hwindow₂,hG,_hLvalues,_hGvalues⟩ := hall F₁ η hF₁ hη hηle
  exact ⟨hwindow₁,hwindow₂,hbound T N G m n hT hN hm hn hG⟩

/-- The dual length, height and integer-displacement argument are tied to
the original physical scales; none is an independently supplied certificate. -/
theorem double_dual_physical_scales
    {P V A B τ θ η : ℝ} (hP : 0 < P) (hV : 0 < V)
    (hA : 0 < A) (hB : 0 < B) (hτ : 0 < τ) (hη : 0 < η) (hηone : η < 1) :
    let s := A^(τ-1)/(τ*η)
    let M := B*P/(s*A*(1-η))
    let H := 2*V/(s*B^(θ-1))
    let K := V*A*η/P
    0 < M ∧ 0 < H ∧ 0 < K ∧
      H/M=(2*V/P)*A*(1-η)*B^(-θ) ∧
      M=(B*τ/(A^(τ+1)*(1-η)))*(P^2/V)*K ∧
      ∀ d:ℝ, (s*A*(1-η)*(d/P))/B=d/M ∧
        2*V*(A*η)*(d/P)=2*K*d := by
  intro s M H K
  have hs : 0 < s := by dsimp [s]; positivity
  have h1 : 0 < 1-η := by linarith
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hE : B^(θ-1)*B=B^θ := by
    calc
      _ = B^(θ-1)*B^(1:ℝ) := by rw [Real.rpow_one]
      _ = B^((θ-1)+1) := (Real.rpow_add hB _ _).symm
      _ = _ := by congr 1; ring
  have hAexp : A^(τ-1)*A^2=A^(τ+1) := by
    calc
      _ = A^(τ-1)*A^(2:ℝ) := by rw [Real.rpow_two]
      _ = A^((τ-1)+2) := (Real.rpow_add hA _ _).symm
      _ = _ := by congr 1; ring
  refine ⟨hM,hH,hK,?_,?_,?_⟩
  · rw [Real.rpow_neg hB.le]
    dsimp [H,M]
    field_simp
    nlinarith only [hE]
  · rw [← hAexp]
    dsimp [M,K,s]
    field_simp
  · intro d
    dsimp [M,K]
    constructor <;> field_simp

/-- Reuse the moving Taylor extension twice. Source tolerance and shift cap
are independent of both shrinking endpoint buffers and both actual anchors.
Unlike the fixed-window construction, no reference-slope interior assumption
is imposed on a retained value. This is model uniformity, not a D estimate. -/
theorem moving_double_dual_uniformity
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (hB : 0 < B) (hB₂ : B ≤ 2) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ P Q₁ : ℕ, 1 ≤ P ∧
        ∀ (F : ℝ → ℝ) (η w h : ℝ),
          IsApproximateModelPhaseFunction F σ P δ →
          0 < η → η ≤ η₀ → w ∈ modelPhaseSlopeRange F →
          0 < h → h ≤ 1 →
          modelPhaseClosedSlope F 2+4*h < modelPhaseClosedSlope F 1 →
          let L := canonicalTaylorLegendrePhase F σ A Q₁ w h
          let J := aProcessShiftPhase L σ⁻¹ η
          ∀ (v g : ℝ), v ∈ modelPhaseSlopeRange J → 0 < g → g ≤ 1 →
            modelPhaseClosedSlope J 2+4*g < modelPhaseClosedSlope J 1 →
            IsApproximateModelPhaseFunction
              (canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q v g)
              (σ⁻¹+1)⁻¹ Q ε := by
  have hs : 0 < σ⁻¹ := inv_pos.mpr hσ
  obtain ⟨δ₂,hδ₂,_hsmall₂,_hpos₂,hsecond⟩ :=
    canonicalTaylorLegendrePhase_uniformity (show 0 < σ⁻¹+1 by positivity)
      hB hB₂ Q hε
  let Q₂ := legendreFiniteInputOrder (Q+2)
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model hs Q₂ hδ₂
  obtain ⟨δ,hδ,_hsmall,_hpos,hfirst⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ (Q₂+1) hδ₁
  let P := max 1 (legendreFiniteInputOrder ((Q₂+1)+2))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,Q₂+1,le_max_left _ _,?_⟩
  intro F η w h hF hη hηle hw hh hh₁ hgap L J v g hv hg hg₁ hgap₂
  have hsource := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hL := hfirst F hsource w hw h hh hh₁ hgap
  have hJ := hshift L η hL hη hηle
  exact hsecond J hJ v hv g hg hg₁ hgap₂

/-- A finite family of actual interior slope values admits one positive
Taylor buffer. It can shrink with the family; the preceding analytic
uniformity does not depend on this choice. -/
theorem finite_slope_values_retained
    {ι : Type*} (S : Finset ι) {lo hi : ℝ} (hlohi : lo < hi)
    (v : ι → ℝ) (hv : ∀ i∈S, v i ∈ Ioo lo hi) :
    ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ lo+4*h < hi ∧
      ∀ i∈S, v i ∈ Icc (lo+2*h) (hi-2*h) := by
  classical
  let t := S.image (fun i => min (v i-lo) (hi-v i))
  let b := min 1 (hi-lo)
  have hb : 0 < b := lt_min zero_lt_one (sub_pos.mpr hlohi)
  let m := (insert b t).min' (Finset.insert_nonempty b t)
  have hm : 0 < m := by
    have hx : m ∈ insert b t := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [hx]
      exact hb
    · obtain ⟨i,hiS,he⟩ := Finset.mem_image.mp hx
      rw [← he]
      exact lt_min (sub_pos.mpr (hv i hiS).1) (sub_pos.mpr (hv i hiS).2)
  have hmb : m ≤ b := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hm₁ : m ≤ 1 := hmb.trans (min_le_left _ _)
  have hmspan : m ≤ hi-lo := hmb.trans (min_le_right _ _)
  refine ⟨m/8,by positivity,by linarith,by linarith,?_⟩
  intro i hiS
  have hmi : m ≤ min (v i-lo) (hi-v i) :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hiS,rfl⟩))
  have hl := hmi.trans (min_le_left _ _)
  have hr := hmi.trans (min_le_right _ _)
  constructor <;> linarith

/-- All values in a finite family from the actual open slope image can be
realized by one closed model phase, even arbitrarily near its moving endpoints.
The tolerance precedes the original phase and the finite family. -/
theorem finite_actual_legendre_realization
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧
      ∀ F : ℝ → ℝ, IsApproximateModelPhaseFunction F σ P δ →
        ∀ (ι : Type*) (S : Finset ι) (v : ι → ℝ),
          (∀ i∈S, v i ∈ modelPhaseSlopeRange F) →
          ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
            IsApproximateModelPhaseFunction
              (canonicalTaylorLegendrePhase F σ A Q (deriv F (3/2)) h) σ⁻¹ Q ε ∧
            ∀ i∈S,
              canonicalTaylorLegendrePhase F σ A Q (deriv F (3/2)) h (v i/A) =
                A^(σ⁻¹-1)*(modelPhaseLegendreDual F (v i)-
                  modelPhaseLegendreDual F (deriv F (3/2)))+
                  referenceModelPrimitive σ⁻¹ (deriv F (3/2)/A) := by
  obtain ⟨δ,hδ,hsmall,hpos,hmodel⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ Q hε
  let P := max 1 (legendreFiniteInputOrder (Q+2))
  refine ⟨δ,hδ,P,le_max_left _ _,?_⟩
  intro F hF ι S v hv
  have hF₁ := approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  have hFQ := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hwin := modelPhaseSlopeRange_eq_endpoint_Ioo hσ hsmall hF₁
  have hw : deriv F (3/2) ∈ modelPhaseSlopeRange F :=
    ⟨3/2,by norm_num,rfl⟩
  have hwi := hw
  rw [hwin] at hwi
  have hlo : 0 < modelPhaseClosedSlope F 2 :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-σ)/2)
      (modelPhaseClosedSlope_positive_window hσ hpos hF
        (u:=2) (by norm_num [phaseInterval])).1
  obtain ⟨h,hh,hh₁,hgap,hvalues⟩ := finite_slope_values_retained S
    (lt_trans hwi.1 hwi.2) v (fun i hi => by simpa only [hwin] using hv i hi)
  refine ⟨h,hh,hh₁,hmodel F hFQ _ hw h hh hh₁ hgap,?_⟩
  intro i hi
  have hvi := hv i hi
  rw [hwin] at hvi
  exact canonicalTaylorLegendrePhase_agrees Q hA (hlo.trans hwi.1)
    (hlo.trans hvi.1) hh (hvalues i hi)

/-- The compression term disappears from the actual integer-frequency
character only after its physical coefficient and displacement have both
been identified as integers. The anchor phase remains explicit. -/
theorem canonical_double_dual_physical_character
    {σ δ δJ A B a b c η y P V : ℝ} {F χ ψ : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hP : 0 < P) (hV : 0 < V) (hη : 0 < η) (hηone : η < 1)
    (hwindow : Icc a b ⊆ modelPhaseSlopeRange F)
    (hχ : ∀ z∈Icc a b, χ z=1) (hy : y∈Ioo (1:ℝ) 2)
    (hu : A*aProcessShiftPoint η 0 y ∈ Ioo a b)
    (huk : A*aProcessShiftPoint η 1 y ∈ Ioo a b)
    (K n r : ℤ) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalLegendrePhase χ F σ A a) σ⁻¹ η
    let w := s*A*(1-η)*d
    let θ := (σ⁻¹+1)⁻¹
    let G := canonicalLegendrePhase ψ J (σ⁻¹+1) B c
    let M := B*P/(s*A*(1-η))
    let H := 2*V/(s*B^(θ-1))
    let C := -2*V/s*modelPhaseLegendreDual J c+H*referenceModelPrimitive θ (c/B)
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w → ψ w=1 →
      V*k/P=(K:ℝ) → P*d=(n:ℝ) →
      fordAdditiveCharacter ((r:ℝ)*V*R) =
        fordAdditiveCharacter ((r:ℝ)*C)*
          star (fordAdditiveCharacter ((r:ℝ)*H*G ((n:ℝ)/M))) := by
  intro u k d s J w θ G M H C R hJ hw hψ hK hn
  have hs : 0 < s := by dsimp [s]; positivity
  have hz : 0 < B^(θ-1) := Real.rpow_pos_of_pos hB _
  have hG := canonical_double_dual_resonance hσ hδ hδJ hF hA hB ha hc
    hwindow hχ hy hu huk hJ hw hψ
  change G (w/B)=B^(θ-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
    referenceModelPrimitive θ (c/B) at hG
  have hd : d=(n:ℝ)/P := by apply (eq_div_iff hP.ne').mpr; nlinarith only [hn]
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have harg := (hscales.2.2.2.2.2 (n:ℝ)).1
  change (s*A*(1-η)*((n:ℝ)/P))/B=(n:ℝ)/M at harg
  have hwarg : w/B=(n:ℝ)/M := by dsimp only [w]; rw [hd]; exact harg
  rw [hwarg] at hG
  have hR : V*R=C-H*G ((n:ℝ)/M)-2*(K:ℝ)*(n:ℝ) := by
    rw [hG,← hK,← hn]
    dsimp only [H,C]
    field_simp
    ring
  have he : (r:ℝ)*V*R =
      ((r:ℝ)*C+-((r:ℝ)*H*G ((n:ℝ)/M)))+((-2*r*K*n:ℤ):ℝ) := by
    push_cast
    rw [mul_assoc, hR]
    ring
  have hint (z : ℤ) : fordAdditiveCharacter (z:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have hz' : 2*Real.pi*Complex.I*((z:ℝ):ℂ) =
        (z:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [hz',Complex.exp_int_mul_two_pi_mul_I]
  rw [he,fordAdditiveCharacter_add,hint,mul_one,
    fordAdditiveCharacter_add,← conj_fordAdditiveCharacter]
  rfl

/-- The moving Taylor extension has the derivative of the literal dual at
every strictly retained slope value. Its buffer may depend on the finite
physical family; no fixed reference-slope window is used. -/
theorem moving_legendre_hasDerivAt
    {σ δ A a v h : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hv : 0 < v) (hh : 0 < h)
    (hret : v ∈ Ioo (modelPhaseClosedSlope F 2+2*h)
      (modelPhaseClosedSlope F 1-2*h)) :
    HasDerivAt (canonicalTaylorLegendrePhase F σ A Q a h)
      (A^(σ⁻¹-1)*modelPhaseInverseSlope F v*A) (v/A) := by
  have hvwin : v ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret.1,hret.2]
  have he : canonicalTaylorLegendrePhase F σ A Q a h =ᶠ[𝓝 (v/A)]
      fun x => A^(σ⁻¹-1)*(modelPhaseLegendreDual F (A*x)-modelPhaseLegendreDual F a)+
        referenceModelPrimitive σ⁻¹ (a/A) := by
    have hc : ContinuousAt (fun x:ℝ => A*x) (v/A) := by fun_prop
    have hn : Ioo (max 0 (modelPhaseClosedSlope F 2+2*h))
        (modelPhaseClosedSlope F 1-2*h) ∈ 𝓝 (A*(v/A)) := by
      rw [mul_div_cancel₀ _ hA.ne']
      exact isOpen_Ioo.mem_nhds ⟨max_lt hv hret.1,hret.2⟩
    filter_upwards [hc.preimage_mem_nhds hn] with x hx
    have hpos : 0 < A*x := lt_of_le_of_lt (le_max_left _ _) hx.1
    have hlow := lt_of_le_of_lt (le_max_right _ _) hx.1
    have hval := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hpos hh
      ⟨hlow.le,hx.2.le⟩
    simpa only [mul_div_cancel_left₀ _ hA.ne'] using hval
  have hd₀ : HasDerivAt (modelPhaseLegendreDual F) (modelPhaseInverseSlope F v)
      (A*(v/A)) := by
    simpa only [mul_div_cancel₀ _ hA.ne'] using
      modelPhaseLegendreDual_hasDerivAt hσ hδ hF hvwin
  have hd := hd₀.comp (v/A) ((hasDerivAt_id (v/A)).const_mul A)
  simp only [mul_one] at hd
  convert (((hd.sub_const (modelPhaseLegendreDual F a)).const_mul
    (A^(σ⁻¹-1))).add_const (referenceModelPrimitive σ⁻¹ (a/A))).congr_of_eventuallyEq
      he using 1
  ring

/-- Literal values and displacement derivative for the actual shifted moving
dual. In particular, changing the Taylor buffer introduces no phase error. -/
theorem moving_shift_displacement
    {σ δ A a h η y : ℝ} {F : ℝ → ℝ} (Q : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (ha : 0 < a) (hh : 0 < h)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q a h) σ⁻¹ η
    J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) ∧
      HasDerivAt J (s*A*(1-η)*d) y := by
  intro u k d s J
  have hcoords : A*aProcessShiftPoint η 1 y = u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  have h0 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha hu hh
    ⟨hret₀.1.le,hret₀.2.le⟩
  have h1 := canonicalTaylorLegendrePhase_agrees (σ:=σ) Q hA ha huk hh
    ⟨hret₁.1.le,hret₁.2.le⟩
  simp only [mul_div_cancel_left₀ _ hA.ne'] at h0 h1
  constructor
  · dsimp only [J,aProcessShiftPhase]
    rw [h0,h1,hcoords]
    dsimp [s,u]
    ring
  · have hd (t:ℝ) (ht:0 < A*aProcessShiftPoint η t y)
        (hr:A*aProcessShiftPoint η t y ∈
          Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
        HasDerivAt
          (fun x => canonicalTaylorLegendrePhase F σ A Q a h (aProcessShiftPoint η t x))
          (A^(σ⁻¹-1)*modelPhaseInverseSlope F (A*aProcessShiftPoint η t y)*A*(1-η)) y := by
      have hv := moving_legendre_hasDerivAt Q hσ hδ hF hA ha ht hh hr
      rw [mul_div_cancel_left₀ _ hA.ne'] at hv
      convert hv.comp y
        (((hasDerivAt_id y).const_mul (1-η)).add_const ((1+t)*η)) using 1
      simp
    have hj := ((hd 0 hu hret₀).sub (hd 1 huk hret₁)).div_const (σ⁻¹*η)
    rw [hcoords] at hj
    convert hj using 1
    dsimp [J,aProcessShiftPhase,aProcessShiftPoint,s,d,u]
    ring

/-- The exact double-dual resonance formula survives both moving Taylor
extensions. Both buffers are explicit and no fixed reference chart occurs. -/
theorem moving_double_dual_resonance
    {σ δ δJ A B a c h g η y : ℝ} {F : ℝ → ℝ} (Q₁ Q₂ : ℕ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hδJ : δJ ≤ min (modelPhaseCurvatureLower (σ⁻¹+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hc : 0 < c)
    (hh : 0 < h) (hg : 0 < g) (hy : y ∈ Ioo (1:ℝ) 2)
    (hu : 0 < A*aProcessShiftPoint η 0 y)
    (huk : 0 < A*aProcessShiftPoint η 1 y)
    (hret₀ : A*aProcessShiftPoint η 0 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h))
    (hret₁ : A*aProcessShiftPoint η 1 y ∈
      Ioo (modelPhaseClosedSlope F 2+2*h) (modelPhaseClosedSlope F 1-2*h)) :
    let u := A*aProcessShiftPoint η 0 y
    let k := A*η
    let d := modelPhaseInverseSlope F u-modelPhaseInverseSlope F (u+k)
    let s := A^(σ⁻¹-1)/(σ⁻¹*η)
    let J := aProcessShiftPhase (canonicalTaylorLegendrePhase F σ A Q₁ a h) σ⁻¹ η
    let w := s*A*(1-η)*d
    let R := 2*(F (modelPhaseInverseSlope F (u+k))-F (modelPhaseInverseSlope F u)-
      k*modelPhaseInverseSlope F (u+k))
    IsApproximateModelPhaseFunction J (σ⁻¹+1) 1 δJ → 0 < w →
      w ∈ Icc (modelPhaseClosedSlope J 2+2*g) (modelPhaseClosedSlope J 1-2*g) →
      canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q₂ c g (w/B) =
        B^((σ⁻¹+1)⁻¹-1)*(-s/2*R-s*k*d-modelPhaseLegendreDual J c)+
          referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  intro u k d s J w R hJ hw hwret
  have hcoords : A*aProcessShiftPoint η 1 y=u+k := by
    dsimp [u,k,aProcessShiftPoint]
    ring
  obtain ⟨hval,hderiv⟩ := moving_shift_displacement Q₁ hσ hδ hF hA ha hh
    hu huk hret₀ hret₁
  change J y=s*(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k)) at hval
  change HasDerivAt J w y at hderiv
  have hinv : modelPhaseInverseSlope J w=y := by
    rw [← hderiv.deriv]
    exact modelPhaseInverseSlope_deriv (by positivity) hδJ hJ hy
  have huwin : u ∈ modelPhaseSlopeRange F := by
    rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₀.1,hret₀.2]
  have hukwin : u+k ∈ modelPhaseSlopeRange F := by
    rw [← hcoords,modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
    constructor <;> linarith [hret₁.1,hret₁.2]
  have hR := (inverse_slope_shift_stationary_identity hσ hδ hF huwin hukwin).2
  change R = -2*(d*u-(modelPhaseLegendreDual F u-modelPhaseLegendreDual F (u+k))) at hR
  have hdual : modelPhaseLegendreDual J w = -s/2*R-s*k*d := by
    rw [modelPhaseLegendreDual,hinv,hval,hR]
    dsimp [w,u,k,aProcessShiftPoint]
    ring
  rw [canonicalTaylorLegendrePhase_agrees Q₂ hB hc hw hg hwret,hdual]

/-- One pair of moving buffers realizes an entire finite family of actual
displacement resonances by a single closed double-dual model. Constants and
orders precede the phase, the shift and the finite family. This proves the
model/value bridge, not a sharp source-count estimate. -/
theorem finite_moving_double_dual_realization
    {σ A B : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2)
    (hB : 0 < B) (hB₂ : B ≤ 2) (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ P Q₁ : ℕ, 1 ≤ P ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ P δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i ∈ Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i) ∈ modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i) ∈ modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let R := fun i => 2*(F (modelPhaseInverseSlope F (u i+k))-
            F (modelPhaseInverseSlope F (u i))-k*modelPhaseInverseSlope F (u i+k))
          ∃ h g : ℝ, 0 < h ∧ h ≤ 1 ∧ 0 < g ∧ g ≤ 1 ∧
            let L := canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h
            let J := aProcessShiftPhase L σ⁻¹ η
            let c := deriv J (3/2)
            let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B Q c g
            IsApproximateModelPhaseFunction G (σ⁻¹+1)⁻¹ Q ε ∧
              (∀ i∈S, s*A*(1-η)*d i∈Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2) ∧
              ∀ i∈S, G (s*A*(1-η)*d i/B) =
                B^((σ⁻¹+1)⁻¹-1)*(-s/2*R i-s*k*d i-modelPhaseLegendreDual J c)+
                  referenceModelPrimitive (σ⁻¹+1)⁻¹ (c/B) := by
  classical
  have hτ : 0 < σ⁻¹+1 := by positivity
  obtain ⟨δ₂,hδ₂,hsmall₂,hpos₂,hsecond⟩ :=
    canonicalTaylorLegendrePhase_uniformity hτ hB hB₂ Q hε
  let QJ := max 1 (legendreFiniteInputOrder (Q+2))
  obtain ⟨δ₁,η₀,hδ₁,hη₀,hηhalf,hshift⟩ :=
    aProcessShiftPhase_uniform_model (inv_pos.mpr hσ) QJ hδ₂
  obtain ⟨δ,hδ,hsmall,hpos,hfirst⟩ :=
    canonicalTaylorLegendrePhase_uniformity hσ hA hA₂ (QJ+1) hδ₁
  let P := max 1 (legendreFiniteInputOrder ((QJ+1)+2))
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,P,QJ+1,le_max_left _ _,?_⟩
  intro F η hF hη hηle ι S y hy hu huk u k d s R
  have hF₁ := approximateModelPhase_mono hF (le_max_left _ _) le_rfl
  have hFQ := approximateModelPhase_mono hF (le_max_right _ _) le_rfl
  have hwin := modelPhaseSlopeRange_eq_endpoint_Ioo hσ hsmall hF₁
  have hpositive {v:ℝ} (hv:v∈modelPhaseSlopeRange F) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-σ)/2)
      (modelPhaseSlopeRange_positive_window hσ hpos hF hv).1
  have ha : deriv F (3/2) ∈ modelPhaseSlopeRange F := ⟨3/2,by norm_num,rfl⟩
  have hai := ha
  rw [hwin] at hai
  let U := S.image u ∪ S.image (fun i => A*aProcessShiftPoint η 1 (y i))
  have hU : ∀ v∈U, v ∈ Ioo (modelPhaseClosedSlope F 2) (modelPhaseClosedSlope F 1) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa only [hwin] using hu i hi
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
      simpa only [hwin] using huk i hi
  obtain ⟨b,hb,hb₁,hgap,hvalues⟩ := finite_slope_values_retained U
    (lt_trans hai.1 hai.2) id hU
  have hh : 0 < b/2 := by positivity
  have hh₁ : b/2 ≤ 1 := by linarith
  have hhgap : modelPhaseClosedSlope F 2+4*(b/2) < modelPhaseClosedSlope F 1 := by
    linarith
  have hret₀ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 0 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues (u i) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ u i ∧ u i ≤ modelPhaseClosedSlope F 1-2*b at hv
    change modelPhaseClosedSlope F 2+2*(b/2) < u i ∧ u i < modelPhaseClosedSlope F 1-2*(b/2)
    constructor <;> linarith [hv.1,hv.2]
  have hret₁ (i:ι) (hi:i∈S) : A*aProcessShiftPoint η 1 (y i) ∈
      Ioo (modelPhaseClosedSlope F 2+2*(b/2)) (modelPhaseClosedSlope F 1-2*(b/2)) := by
    have hv := hvalues _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
    change modelPhaseClosedSlope F 2+2*b ≤ A*aProcessShiftPoint η 1 (y i) ∧
      A*aProcessShiftPoint η 1 (y i) ≤ modelPhaseClosedSlope F 1-2*b at hv
    constructor <;> linarith [hv.1,hv.2]
  let L := canonicalTaylorLegendrePhase F σ A (QJ+1) (deriv F (3/2)) (b/2)
  let J := aProcessShiftPhase L σ⁻¹ η
  have hL := hfirst F hFQ _ ha (b/2) hh hh₁ hhgap
  have hJ := hshift L η hL hη hηle
  have hJ₁ := approximateModelPhase_mono hJ (le_max_left _ _) le_rfl
  have hJQ := approximateModelPhase_mono hJ (le_max_right _ _) le_rfl
  let w := fun i => s*A*(1-η)*d i
  have hw (i:ι) (hi:i∈S) : w i ∈ modelPhaseSlopeRange J := by
    have hd := (moving_shift_displacement (QJ+1) hσ hsmall hF₁ hA
      (hpositive ha) hh (hpositive (hu i hi)) (hpositive (huk i hi))
      (hret₀ i hi) (hret₁ i hi)).2
    exact ⟨y i,hy i hi,hd.deriv⟩
  let c := deriv J (3/2)
  have hc : c ∈ modelPhaseSlopeRange J := ⟨3/2,by norm_num,rfl⟩
  have hwinJ := modelPhaseSlopeRange_eq_endpoint_Ioo hτ hsmall₂ hJ₁
  change modelPhaseSlopeRange J = Ioo (modelPhaseClosedSlope J 2)
    (modelPhaseClosedSlope J 1) at hwinJ
  have hci := hc
  rw [hwinJ] at hci
  have hpositiveJ {v:ℝ} (hv:v∈modelPhaseSlopeRange J) : 0 < v :=
    lt_of_lt_of_le (by positivity : (0:ℝ) < (2:ℝ)^(-(σ⁻¹+1))/2)
      (modelPhaseSlopeRange_positive_window hτ hpos₂ hJ hv).1
  obtain ⟨g,hg,hg₁,hgapJ,hvaluesJ⟩ := finite_slope_values_retained S
    (lt_trans hci.1 hci.2) w (fun i hi => by simpa only [hwinJ] using hw i hi)
  refine ⟨b/2,g,hh,hh₁,hg,hg₁,?_,?_,?_⟩
  · exact hsecond J hJQ c hc g hg hg₁ hgapJ
  · intro i hi
    exact modelPhaseSlopeRange_positive_window hτ hpos₂ hJ (hw i hi)
  · intro i hi
    exact moving_double_dual_resonance (QJ+1) Q hσ hsmall hsmall₂ hF₁
      hA hB (hpositive ha) (hpositiveJ hc) hh hg (hy i hi)
      (hpositive (hu i hi)) (hpositive (huk i hi)) (hret₀ i hi) (hret₁ i hi)
      hJ₁ (hpositiveJ (hw i hi)) (hvaluesJ i hi)

/-- A genuine exponent-pair bound for the physical resonance sum, not for
an independently supplied dual phase. Both moving buffers and the actual
closed model are constructed from the original phase and finite interval.
The remaining chart-selection and source-count estimates are not assumed. -/
theorem actual_displacement_interval_exponent_pair_bound
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ r : ℤ, r ≠ 0 →
            ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
              C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := by
  have hθ : 0 < (σ⁻¹+1)⁻¹ := by positivity
  obtain ⟨δG,hδG,QG,_hQG,C,hC,hbound⟩ := hpair.allPositiveHeight_bound hθ hε
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ hB hB₂ QG hδG
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn
  obtain ⟨h,g,_hh,_hh₁,_hg,_hg₁,hG,_hwindow,hvalues⟩ :=
    hrealize F η hF hη hηle ℕ (Finset.Icc a b) y hy hu huk
  let J := aProcessShiftPhase
    (canonicalTaylorLegendrePhase F σ A Q₁ (deriv F (3/2)) h) σ⁻¹ η
  let c := deriv J (3/2)
  let G := canonicalTaylorLegendrePhase J (σ⁻¹+1) B QG c g
  let C₀ := -2*V/s*modelPhaseLegendreDual J c+H*referenceModelPrimitive θ (c/B)
  have hs : 0 < s := by dsimp [s]; positivity
  have hz : 0 < B^(θ-1) := Real.rpow_pos_of_pos hB _
  have hH : 0 < H := by dsimp [H]; positivity
  have hηone : η < 1 := by linarith
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have hphase (n:ℕ) (hni:n∈Finset.Icc a b) :
      V*R n=C₀-H*G ((n:ℝ)/M)-2*(K:ℝ)*(n:ℝ) := by
    have hd : d n=(n:ℝ)/P := by
      apply (eq_div_iff hP.ne').mpr
      nlinarith only [hn n hni]
    have hv := hvalues n hni
    change G (s*A*(1-η)*d n/B)=
      B^(θ-1)*(-s/2*R n-s*k*d n-modelPhaseLegendreDual J c)+
        referenceModelPrimitive θ (c/B) at hv
    have harg := (hscales.2.2.2.2.2 (n:ℝ)).1
    change s*A*(1-η)*((n:ℝ)/P)/B=(n:ℝ)/M at harg
    rw [hd,harg] at hv
    rw [hv,← hK]
    dsimp only [H,C₀]
    field_simp
    ring
  have hint (z:ℤ) : fordAdditiveCharacter (z:ℝ)=1 := by
    unfold fordAdditiveCharacter
    have he : 2*Real.pi*Complex.I*((z:ℝ):ℂ) =
        (z:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [he,Complex.exp_int_mul_two_pi_mul_I]
  intro r hr
  have hchar (n:ℕ) (hni:n∈Finset.Icc a b) :
      fordAdditiveCharacter ((r:ℝ)*V*R n) =
        fordAdditiveCharacter ((r:ℝ)*C₀)*
          star (fordAdditiveCharacter ((r:ℝ)*H*G ((n:ℝ)/M))) := by
    have he : (r:ℝ)*V*R n =
        ((r:ℝ)*C₀+-((r:ℝ)*H*G ((n:ℝ)/M)))+
          ((-2*r*K*(n:ℤ):ℤ):ℝ) := by
      push_cast
      rw [mul_assoc,hphase n hni]
      ring
    rw [he,fordAdditiveCharacter_add,hint,mul_one,
      fordAdditiveCharacter_add,← conj_fordAdditiveCharacter]
    rfl
  have hsum : (∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)) =
      fordAdditiveCharacter ((r:ℝ)*C₀)*star (exponentialSumAt G ((r:ℝ)*H) M a b) := by
    rw [exponentialSumAt,star_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hni
    simp only [hchar n hni,sargos_ford_character_eq_fourier,oscillatory]
  rw [hsum,norm_mul,sargos_character_norm,one_mul,norm_star]
  have hnormheight : ‖exponentialSumAt G ((r:ℝ)*H) M a b‖ =
      ‖exponentialSumAt G (|(r:ℝ)| * H) M a b‖ := by
    by_cases hrpos : 0 ≤ (r:ℝ)
    · rw [abs_of_nonneg hrpos]
    · have hrneg : (r:ℝ) < 0 := lt_of_not_ge hrpos
      have he : exponentialSumAt G ((r:ℝ)*H) M a b =
          star (exponentialSumAt G (|(r:ℝ)| * H) M a b) := by
        simp only [exponentialSumAt,star_sum]
        apply Finset.sum_congr rfl
        intro n _hn
        simp only [oscillatory,←sargos_ford_character_eq_fourier,abs_of_neg hrneg]
        have harg : (r:ℝ)*H*G ((n:ℝ)/M) = -(-(r:ℝ)*H*G ((n:ℝ)/M)) := by ring
        rw [harg,←conj_fordAdditiveCharacter]
        rfl
      rw [he,norm_star]
  rw [hnormheight]
  exact hbound (|(r:ℝ)| * H) M G a b
    (mul_pos (abs_pos.mpr (Int.cast_ne_zero.mpr hr)) hH)
    hM ha hb hG

/-- Reuse the existing finite positive-slope grid for compressed shifts.
The original point and its shifted partner are represented exactly, with
uniform interior room even on a grid-cell boundary. -/
theorem positive_slope_chart_compressed_coordinate
    {d v k : ℝ} (hd : 0 < d) (hv : v ∈ Icc (4*d) 2)
    (hk : 0 ≤ k) (hkd : k ≤ d) :
    let j := positiveSlopeChartIndex d v
    let A := positiveSlopeChartScale d j
    let η := k/A
    let y := (v/A-η)/(1-η)
    j ∈ positiveSlopeChartIndices d ∧ 0 < A ∧ A ≤ 3/2 ∧
      0 ≤ η ∧ η ≤ 1/3 ∧ y ∈ Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 y=v ∧ A*aProcessShiftPoint η 1 y=v+k := by
  intro j A η y
  have hj : j ∈ positiveSlopeChartIndices d := positiveSlopeChartIndex_mem hd hv
  obtain ⟨hA,hA₂⟩ := positiveSlopeChartScale_bounds hd hj
  have hj₄ : (4:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjd := mul_le_mul_of_nonneg_right hj₄ hd.le
  have hAd : 3*d ≤ A := by dsimp [A,positiveSlopeChartScale]; nlinarith only [hjd]
  have hη : 0 ≤ η := div_nonneg hk hA.le
  have hη₁ : η ≤ 1/3 := by
    apply (div_le_iff₀ hA).mpr
    linarith only [hkd,hAd]
  have hden : 0 < 1-η := by linarith
  have hvpos : 0 ≤ v := (by positivity : (0:ℝ) ≤ 4*d).trans hv.1
  have hcell := (positiveSlopeChartIndex_eq_iff hd hvpos j).mp (show _=j from rfl)
  have hcoord := positiveSlopeChart_coordinate hd (Finset.mem_Icc.mp hj).1 hcell
  have hupper : v+k < 2*A := by
    dsimp [A,positiveSlopeChartScale]
    nlinarith only [hcell.2,hkd,hjd]
  have hy : y ∈ Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hden).mpr
      linarith only [hcoord.1]
    · apply (div_lt_iff₀ hden).mpr
      have hdiv : v/A+η < 2 := by
        dsimp only [η]
        rw [← add_div]
        exact (div_lt_iff₀ hA).mpr hupper
      linarith only [hdiv]
  have hzero : A*aProcessShiftPoint η 0 y=v := by
    dsimp only [aProcessShiftPoint,y]
    field_simp [show A ≠ 0 from hA.ne',hden.ne']
    ring
  refine ⟨hj,hA,hA₂,hη,hη₁,hy,hzero,?_⟩
  have hkA : A*η=k := mul_div_cancel₀ k (show A ≠ 0 from hA.ne')
  calc
    A*aProcessShiftPoint η 1 y=A*aProcessShiftPoint η 0 y+A*η := by
      dsimp [aProcessShiftPoint]
      ring
    _ = v+k := by rw [hzero,hkA]

/-- A diagnostic for the unmodified Robert--Sargos reduction, even if its
sample-pair count were reduced to its unavoidable diagonal. With lengths
N^h, N^q, N^r and fourth derivative N^(-d), these are four of the surviving
losses in the eighth power. Rebalancing them cannot improve 1/13.
This is not an obstruction to the desired D theorem or to a sharper sieve. -/
theorem robertSargos_relaxed_loss_floor {d h q r t : ℝ}
    (hH : t ≤ 4*h) (hQR : t ≤ 2*q+2*r)
    (hHQ : t ≤ d-h-q) (hRH : t ≤ d-r-2*h) :
    13*t ≤ 8*d := by
  linarith only [hH,hQR,hHQ,hRH]

/-- At alpha=2/5, the desired D(Bourgain) saving strictly exceeds the
best saving allowed by the four unchanged relaxed RS losses. -/
theorem robertSargos_relaxed_losses_do_not_close_d_bourgain :
    ¬ ∃ h q r : ℝ,
      (190:ℝ)/199 ≤ 4*h ∧ 190/199 ≤ 2*q+2*r ∧
        190/199 ≤ 3/2-h-q ∧ 190/199 ≤ 3/2-r-2*h := by
  rintro ⟨h,q,r,hH,hQR,hHQ,hRH⟩
  have hn := robertSargos_relaxed_loss_floor hH hQR hHQ hRH
  norm_num at hn

#print axioms robertSargos_relaxed_loss_floor
#print axioms moving_legendre_hasDerivAt
#print axioms moving_shift_displacement
#print axioms moving_double_dual_resonance
#print axioms finite_moving_double_dual_realization
#print axioms actual_displacement_interval_exponent_pair_bound
#print axioms positive_slope_chart_compressed_coordinate
#print axioms finite_actual_legendre_realization
#print axioms canonical_double_dual_physical_character
#print axioms robertSargos_relaxed_losses_do_not_close_d_bourgain
#print axioms moving_double_dual_uniformity
#print axioms finite_slope_values_retained
#print axioms inverse_slope_shift_stationary_identity
#print axioms negative_first_derivative_model
#print axioms derivative_double_dual_parameter
#print axioms double_dual_shift_uniformity
#print axioms canonical_legendre_hasDerivAt
#print axioms canonical_shift_displacement
#print axioms canonical_double_dual_resonance
#print axioms source_double_dual_exponent_pair_bound
#print axioms double_dual_physical_scales

-- Smallest chart, exact cell boundary, and the largest permitted physical shift.
example :
    let A := positiveSlopeChartScale (1/4) (positiveSlopeChartIndex (1/4) 1)
    let η := (1/4)/A
    let y := (1/A-η)/(1-η)
    A=3/4 ∧ η=1/3 ∧ y=3/2 ∧ A*aProcessShiftPoint η 0 y=1 ∧
      A*aProcessShiftPoint η 1 y=5/4 := by
  norm_num [positiveSlopeChartScale,positiveSlopeChartIndex,aProcessShiftPoint]

-- The closed upper endpoint of the existing slope grid is not discarded.
example :
    let A := positiveSlopeChartScale (1/4) (positiveSlopeChartIndex (1/4) 2)
    let η := (1/4)/A
    let y := (2/A-η)/(1-η)
    A=3/2 ∧ η=1/6 ∧ y=7/5 ∧ A*aProcessShiftPoint η 0 y=2 ∧
      A*aProcessShiftPoint η 1 y=9/4 := by
  norm_num [positiveSlopeChartScale,positiveSlopeChartIndex,aProcessShiftPoint]

-- Zero shift is valid for chart geometry only; the analytic consumer requires positivity.
example :
    let A := positiveSlopeChartScale (1/4) (positiveSlopeChartIndex (1/4) 1)
    A*aProcessShiftPoint 0 0 (4/3)=1 ∧ A*aProcessShiftPoint 0 1 (4/3)=1 := by
  norm_num [positiveSlopeChartScale,positiveSlopeChartIndex,aProcessShiftPoint]
end TaoTrudgianYang2025.DisplacementDualPrototype


namespace TaoTrudgianYang2025.DisplacementDualPrototype

theorem actual_displacement_interval_near_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (a b : ℕ) (K : ℤ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈Finset.Icc a b, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → M ≤ (a:ℝ) → (b:ℝ) ≤ 2*M → V*k/P=(K:ℝ) →
          (∀ n∈Finset.Icc a b, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          ∀ (I : Finset ℕ), I ⊆ Finset.Icc a b →
          (∀ n∈I, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (I.card:ℝ) ≤ 2*W*(Finset.Icc a b).card+
              (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
              2*(C*M/H) := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,hbound⟩ :=
    actual_displacement_interval_exponent_pair_bound hσ hA hA₂ hB hB₂ hpair hε
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V a b K y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM ha hb hK hn W hW hWhalf I hI hnear
  have hηone : η < 1 := by linarith
  have hs : 0 < s := by dsimp [s]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hp0 : 0 ≤ k₀+ε := by linarith [hpair.1.1]
  have hfreq (r:ℤ) (hr : r ≠ 0) :
      ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*(V*R n))‖ ≤
        (C*(H/M)^(k₀+ε)*M^(l₀+ε))*|(r:ℝ)|^(k₀+ε)+C*M/H := by
    have hh := hbound F η P V a b K y hF hη hηle hP hV hy hu huk
      hM ha hb hK hn r hr
    change ‖∑ n∈Finset.Icc a b, fordAdditiveCharacter ((r:ℝ)*V*R n)‖ ≤
      C*(((|(r:ℝ)| * H)/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) at hh
    have hr1 : 1 ≤ |(r:ℝ)| := by exact_mod_cast Int.one_le_abs hr
    have htail : M/(|(r:ℝ)| * H) ≤ M/H :=
      div_le_div_of_nonneg_left hMpos.le hH (by nlinarith)
    have he : ((|(r:ℝ)| * H)/M)^(k₀+ε)=
        |(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε) := by
      rw [show |(r:ℝ)| * H/M=|(r:ℝ)| * (H/M) by ring,
        Real.mul_rpow (abs_nonneg _) (div_nonneg hH.le hMpos.le)]
    simp only [mul_assoc] at hh ⊢
    rw [he] at hh
    calc
      _ ≤ C*(|(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε)*M^(l₀+ε)+M/(|(r:ℝ)| * H)) := hh
      _ ≤ C*(|(r:ℝ)|^(k₀+ε)*(H/M)^(k₀+ε)*M^(l₀+ε)+M/H) := by gcongr
      _ = _ := by ring
  exact CubicNearCurvePrototype.cubic_near_integer_count_power
    (Finset.Icc a b) I (fun n => V*R n) hW hWhalf
    (by positivity) (by positivity) hp0 hp hI hnear hfreq

#print axioms actual_displacement_interval_near_count


/-- Fill the integer holes of a finite actual displacement chart.
The phase values at all source labels are preserved exactly. -/
theorem finite_actual_displacement_interval_completion
    {σ δ A η P : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hA : 0 < A) (hη : η < 1)
    (S : Finset ℕ) (hne : S.Nonempty) (y : ℕ → ℝ)
    (hy : ∀ n∈S, y n∈Ioo (1:ℝ) 2)
    (hu : ∀ n∈S, A*aProcessShiftPoint η 0 (y n)∈modelPhaseSlopeRange F)
    (huk : ∀ n∈S, A*aProcessShiftPoint η 1 (y n)∈modelPhaseSlopeRange F)
    (hn : ∀ n∈S, P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (y n))-
      modelPhaseInverseSlope F (A*aProcessShiftPoint η 1 (y n)))=(n:ℝ)) :
    ∃ z : ℕ → ℝ,
      (∀ n∈S, z n=y n) ∧
      ∀ n∈Finset.Icc (S.min' hne) (S.max' hne),
        z n∈Ioo (1:ℝ) 2 ∧
        A*aProcessShiftPoint η 0 (z n)∈modelPhaseSlopeRange F ∧
        A*aProcessShiftPoint η 1 (z n)∈modelPhaseSlopeRange F ∧
        P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n))-
          modelPhaseInverseSlope F (A*aProcessShiftPoint η 1 (z n)))=(n:ℝ) := by
  classical
  let a := S.min' hne
  let b := S.max' hne
  have ha : a∈S := Finset.min'_mem S hne
  have hb : b∈S := Finset.max'_mem S hne
  let U := fun t v => A*aProcessShiftPoint η t v
  let D := fun v => P*(modelPhaseInverseSlope F (U 0 v)-modelPhaseInverseSlope F (U 1 v))
  have hmono (t : ℝ) : Monotone (U t) := by
    intro v w hvw
    dsimp [U,aProcessShiftPoint]
    gcongr
  have hpoint (v : ℝ) (hv : v∈uIcc (y a) (y b)) :
      v∈Ioo (1:ℝ) 2 ∧ U 0 v∈modelPhaseSlopeRange F ∧ U 1 v∈modelPhaseSlopeRange F := by
    have hconv : Set.OrdConnected (modelPhaseSlopeRange F) := by
      rw [modelPhaseSlopeRange_eq_endpoint_Ioo hσ hδ hF]
      exact (convex_Ioo _ _).ordConnected
    refine ⟨(convex_Ioo (1:ℝ) 2).ordConnected.uIcc_subset (hy a ha) (hy b hb) hv,?_,?_⟩
    · exact hconv.uIcc_subset (hu a ha) (hu b hb) ((hmono 0).image_uIcc_subset ⟨v,hv,rfl⟩)
    · exact hconv.uIcc_subset (huk a ha) (huk b hb) ((hmono 1).image_uIcc_subset ⟨v,hv,rfl⟩)
  have hD : ContinuousOn D (uIcc (y a) (y b)) := by
    intro v hv
    have hc (t : ℝ) (ht : U t v∈modelPhaseSlopeRange F) :
        ContinuousAt (fun w => modelPhaseInverseSlope F (U t w)) v := by
      exact ((modelPhaseInverseSlope_contDiffAt hσ hδ hF ht).continuousAt).comp
        (by dsimp [U,aProcessShiftPoint]; fun_prop)
    exact ((hc 0 (hpoint v hv).2.1).sub (hc 1 (hpoint v hv).2.2)).const_mul P
      |>.continuousWithinAt
  have hex (n : ℕ) (hni : n∈Finset.Icc a b) :
      ∃ v : ℝ, v∈Ioo (1:ℝ) 2 ∧ U 0 v∈modelPhaseSlopeRange F ∧
        U 1 v∈modelPhaseSlopeRange F ∧ D v=(n:ℝ) ∧ (n∈S → v=y n) := by
    by_cases hns : n∈S
    · exact ⟨y n,hy n hns,hu n hns,huk n hns,hn n hns,fun _ => rfl⟩
    have hna : a ≤ n := (Finset.mem_Icc.mp hni).1
    have hnb : n ≤ b := (Finset.mem_Icc.mp hni).2
    have hab : (a:ℝ) ≤ b := by exact_mod_cast hna.trans hnb
    have htarget : (n:ℝ)∈uIcc (D (y a)) (D (y b)) := by
      change (n:ℝ)∈uIcc (P*(_-_)) (P*(_-_))
      rw [hn a ha,hn b hb,uIcc_of_le hab]
      exact ⟨by exact_mod_cast hna,by exact_mod_cast hnb⟩
    obtain ⟨v,hv,he⟩ := intermediate_value_uIcc hD htarget
    exact ⟨v,(hpoint v hv).1,(hpoint v hv).2.1,(hpoint v hv).2.2,he,
      fun hh => False.elim (hns hh)⟩
  let z := fun n => if hni : n∈Finset.Icc a b then Classical.choose (hex n hni) else y n
  refine ⟨z,?_,?_⟩
  · intro n hns
    have hni : n∈Finset.Icc a b := Finset.mem_Icc.mpr
      ⟨Finset.min'_le S n hns,Finset.le_max' S n hns⟩
    simp only [z,dif_pos hni]
    exact (Classical.choose_spec (hex n hni)).2.2.2.2 hns
  · intro n hni
    change n∈Finset.Icc a b at hni
    simp only [z,dif_pos hni]
    have hh := Classical.choose_spec (hex n hni)
    exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩

#print axioms finite_actual_displacement_interval_completion

theorem actual_displacement_finite_near_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let θ := (σ⁻¹+1)⁻¹
          let M := B*P/(s*A*(1-η))
          let H := 2*V/(s*B^(θ-1))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → (∀ n∈S, M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ 4*W*M+
              (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
              2*(C*M/H) := by
  obtain ⟨δ₀,η₀,hδ₀,hη₀,hηhalf,Q,hQ,C,hC,hbound⟩ :=
    actual_displacement_interval_near_count hσ hA hA₂ hB hB₂ hpair hε hp
  let δ := min δ₀ (min (modelPhaseCurvatureLower σ) 1)
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one)
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V K S y hF hη hηle hP hV hy hu huk u k d s θ M H R
    hM hbox hK hn W hW hWhalf hnear
  have hs : 0 < s := by dsimp [s]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hFlarge := approximateModelPhase_mono hF (le_refl Q) (min_le_left δ₀ _)
  have hFone := approximateModelPhase_mono hF hQ (le_refl δ)
  have hshift (v : ℝ) : A*aProcessShiftPoint η 1 v=A*aProcessShiftPoint η 0 v+k := by
    dsimp [aProcessShiftPoint,k]
    ring
  by_cases hne : S.Nonempty
  · obtain ⟨z,hagree,hcomplete⟩ := finite_actual_displacement_interval_completion
      hσ (min_le_right δ₀ _) hFone hA (by linarith) S hne y hy hu huk
      (by intro n hni; rw [hshift]; exact hn n hni)
    let a := S.min' hne
    let b := S.max' hne
    have ha : a∈S := Finset.min'_mem S hne
    have hb : b∈S := Finset.max'_mem S hne
    have hab : a ≤ b := Finset.min'_le S b hb
    have hsubset : S ⊆ Finset.Icc a b := fun n hni => Finset.mem_Icc.mpr
      ⟨Finset.min'_le S n hni,Finset.le_max' S n hni⟩
    have hMa : M ≤ (a:ℝ) := (hbox a ha).1
    have hbM : (b:ℝ) ≤ 2*M := (hbox b hb).2
    have hz₀ : ∀ n∈Finset.Icc a b, z n∈Ioo (1:ℝ) 2 :=
      fun n hni => (hcomplete n hni).1
    have hz₁ : ∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 0 (z n)∈modelPhaseSlopeRange F :=
      fun n hni => (hcomplete n hni).2.1
    have hz₂ : ∀ n∈Finset.Icc a b, A*aProcessShiftPoint η 1 (z n)∈modelPhaseSlopeRange F :=
      fun n hni => (hcomplete n hni).2.2.1
    have hz₃ : ∀ n∈Finset.Icc a b,
        P*(modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n))-
          modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))=(n:ℝ) := by
      intro n hni
      have hh := (hcomplete n hni).2.2.2
      rwa [hshift] at hh
    let Rz := fun n => 2*(F (modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))-
      F (modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)))-
      k*modelPhaseInverseSlope F (A*aProcessShiftPoint η 0 (z n)+k))
    have hznear : ∀ n∈S, ∃ e : ℤ, |V*Rz n-(e:ℝ)| ≤ W/2 := by
      intro n hni
      have he : Rz n=R n := by
        dsimp only [Rz,R,u]
        rw [hagree n hni]
      rw [he]
      exact hnear n hni
    have hh := hbound F η P V a b K z hFlarge hη hηle hP hV hz₀ hz₁ hz₂
      hM hMa hbM hK hz₃ W hW hWhalf S hsubset hznear
    change (S.card:ℝ) ≤ 2*W*(Finset.Icc a b).card+
      (4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
      2*(C*M/H) at hh
    have hcard : ((Finset.Icc a b).card:ℝ) ≤ 2*M := by
      rw [Nat.card_Icc,Nat.cast_sub (by omega : a ≤ b+1),Nat.cast_add,Nat.cast_one]
      linarith
    calc
      _ ≤ _ := hh
      _ ≤ 2*W*(2*M)+(4+4/(1-(k₀+ε)))*(C*(H/M)^(k₀+ε)*M^(l₀+ε))*W^(-(k₀+ε))+
          2*(C*M/H) := by gcongr
      _ = _ := by ring
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms actual_displacement_finite_near_count


/-- The second chart coordinate is in a fixed compact positive window,
derived from the actual moving first dual rather than assumed. -/
theorem finite_moving_displacement_window
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) (hA₂ : A ≤ 2) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧
        ∀ (F : ℝ → ℝ) (η : ℝ), IsApproximateModelPhaseFunction F σ Q δ →
          0 < η → η ≤ η₀ → ∀ (ι : Type*) (S : Finset ι) (y : ι → ℝ),
          (∀ i∈S, y i∈Ioo (1:ℝ) 2) →
          (∀ i∈S, A*aProcessShiftPoint η 0 (y i)∈modelPhaseSlopeRange F) →
          (∀ i∈S, A*aProcessShiftPoint η 1 (y i)∈modelPhaseSlopeRange F) →
          let u := fun i => A*aProcessShiftPoint η 0 (y i)
          let k := A*η
          let d := fun i => modelPhaseInverseSlope F (u i)-modelPhaseInverseSlope F (u i+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          ∀ i∈S, s*A*(1-η)*d i∈Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2 := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,Q₁,hQ,hrealize⟩ :=
    finite_moving_double_dual_realization hσ hA hA₂ (by norm_num : (0:ℝ)<1)
      (by norm_num : (1:ℝ)≤2) 0 (by norm_num : (0:ℝ)<1)
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,?_⟩
  intro F η hF hη hηle ι S y hy hu huk u k d s
  obtain ⟨h,g,_hh,_hh1,_hg,_hg1,_hG,hwindow,_hvalues⟩ :=
    hrealize F η hF hη hηle ι S y hy hu huk
  exact hwindow

/-- A second slope-grid cell supplies the physical exponent-pair length.
The hypotheses contain only the actual displacement coordinate. -/
theorem displacement_second_chart_geometry
    {mesh w L P n : ℝ} (hd : 0 < mesh) (hL : 0 < L) (hP : 0 < P)
    (hw : w∈Icc (4*mesh) 2) (hn : 2 ≤ n) (he : w=L*n/P) :
    let j := positiveSlopeChartIndex mesh w
    let B := positiveSlopeChartScale mesh j
    let M := B*P/L
    j∈positiveSlopeChartIndices mesh ∧ 0 < B ∧ B ≤ 3/2 ∧
      1 ≤ M ∧ M ≤ n ∧ n ≤ 2*M := by
  intro j B M
  have hj := positiveSlopeChartIndex_mem hd hw
  have hBj := positiveSlopeChartScale_bounds hd hj
  have hw0 : 0 ≤ w := (by positivity : (0:ℝ) ≤ 4*mesh).trans hw.1
  have hcell := (positiveSlopeChartIndex_eq_iff hd hw0 j).mp (show _=j from rfl)
  have hc := positiveSlopeChart_coordinate hd (Finset.mem_Icc.mp hj).1 hcell
  have hB : 0 < B := hBj.1
  have hM : 0 < M := by dsimp [M]; positivity
  have harg : w/B=n/M := by
    rw [he]
    dsimp only [M]
    field_simp
  change w/B∈Ioo (1:ℝ) 2 at hc
  rw [harg] at hc
  have hlo : M < n := (one_lt_div hM).mp hc.1
  have hhi : n < 2*M := (div_lt_iff₀ hM).mp hc.2
  exact ⟨hj,hB,hBj.2,by linarith,hlo.le,hhi.le⟩

#print axioms finite_moving_displacement_window
#print axioms displacement_second_chart_geometry
/-- Normalize a genuine finite displacement chart to the original physical
frequency V/P and the original dyadic length N. -/
theorem actual_displacement_physical_chart_count
    {σ A B k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2) (hB : 0 < B) (hB₂ : B ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V N : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let s := A^(σ⁻¹-1)/(σ⁻¹*η)
          let M := B*P/(s*A*(1-η))
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          1 ≤ M → (∀ n∈S, M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M) →
          (∀ n∈S, (n:ℝ) ≤ 2*N) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  obtain ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C₀,hC₀,hcount⟩ :=
    actual_displacement_finite_near_count hσ hA hA₂ hB hB₂ hpair hε hp
  let p := k₀+ε
  let q := l₀+ε
  let θ := (σ⁻¹+1)⁻¹
  let c := A*B^(-θ)
  let D := (4+4/(1-p))*C₀*(2*c)^p*(2:ℝ)^q
  let E := 2*C₀/c
  let C := 8+D+E
  have hp₀ : 0 ≤ p := by dsimp [p]; linarith [hpair.1.1]
  have hq₀ : 0 ≤ q := by dsimp [q]; linarith [hpair.1.2.2.1]
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 ≤ D := by dsimp [D,p]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V N K S y hF hη hηle hP hV hN hy hu huk u k d s M R
    hM hbox hNbox hK hn W hW hWhalf hnear
  let H := 2*V/(s*B^(θ-1))
  have hηh : η ≤ 1/2 := hηle.trans hηhalf
  have hηone : η < 1 := by linarith
  have hscales := double_dual_physical_scales (θ:=θ) hP hV hA hB
    (inv_pos.mpr hσ) hη hηone
  have hMpos : 0 < M := hscales.1
  have hH : 0 < H := hscales.2.1
  have heq : H/M=2*c*(1-η)*(V/P) := by
    calc
      _ = (2*V/P)*A*(1-η)*B^(-θ) := hscales.2.2.2.1
      _ = _ := by dsimp [c]; ring
  have hlo : c*(V/P) ≤ H/M := by rw [heq]; nlinarith [mul_pos hc (div_pos hV hP)]
  have hhi : H/M ≤ (2*c)*(V/P) := by rw [heq]; nlinarith [mul_pos hc (div_pos hV hP)]
  have htail : M/H ≤ (1/c)*(P/V) := by
    have hh := one_div_le_one_div_of_le (mul_pos hc (div_pos hV hP)) hlo
    convert hh using 1 <;> field_simp
  by_cases hne : S.Nonempty
  · obtain ⟨n,hns⟩ := hne
    have hMN : M ≤ 2*N := (hbox n hns).1.trans (hNbox n hns)
    have hfreq : (H/M)^p ≤ (2*c)^p*(V/P)^p := by
      rw [← Real.mul_rpow (by positivity : 0 ≤ 2*c) (div_nonneg hV.le hP.le)]
      exact Real.rpow_le_rpow (div_nonneg hH.le hMpos.le) hhi hp₀
    have hlength : M^q ≤ (2:ℝ)^q*N^q := by
      rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hN.le]
      exact Real.rpow_le_rpow hMpos.le hMN hq₀
    have hh := hcount F η P V K S y hF hη hηle hP hV hy hu huk
      hM hbox hK hn W hW hWhalf hnear
    change (S.card:ℝ) ≤ 4*W*M+
      (4+4/(1-p))*(C₀*(H/M)^p*M^q)*W^(-p)+2*(C₀*M/H) at hh
    have hmain : (4+4/(1-p))*(C₀*(H/M)^p*M^q)*W^(-p) ≤
        D*((V/P)^p*N^q*W^(-p)) := by
      calc
        _ ≤ (4+4/(1-p))*(C₀*((2*c)^p*(V/P)^p)*((2:ℝ)^q*N^q))*W^(-p) := by
          gcongr
        _ = _ := by dsimp [D]; ring
    have htail' : 2*(C₀*M/H) ≤ E*(P/V) := by
      calc
        _ = 2*C₀*(M/H) := by ring
        _ ≤ 2*C₀*((1/c)*(P/V)) := by gcongr
        _ = _ := by dsimp [E]; ring
    have hvolume : 4*W*M ≤ 8*(W*N) := by nlinarith [mul_le_mul_of_nonneg_left hMN hW.le]
    have hbig₀ : 8 ≤ C := by dsimp [C]; linarith
    have hbig₁ : D ≤ C := by dsimp [C]; linarith
    have hbig₂ : E ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ 8*(W*N)+D*((V/P)^p*N^q*W^(-p))+E*(P/V) := by linarith
      _ ≤ C*(W*N)+C*((V/P)^p*N^q*W^(-p))+C*(P/V) := by gcongr
      _ = _ := by dsimp [p,q]; ring
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms actual_displacement_physical_chart_count
/-- Remove the second slope chart by a finite cover chosen before the source
phase, retaining the actual displacement, the exact integral resonance,
and the freely chosen near-integer width. -/
theorem actual_displacement_first_chart_count
    {σ A k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hA : 0 < A) (hA₂ : A ≤ 2)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ η₀ : ℝ, 0 < δ ∧ 0 < η₀ ∧ η₀ ≤ 1/2 ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (η P V N : ℝ) (K : ℤ) (S : Finset ℕ) (y : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < η → η ≤ η₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, y n ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, A*aProcessShiftPoint η 0 (y n) ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, A*aProcessShiftPoint η 1 (y n) ∈ modelPhaseSlopeRange F) →
          let u := fun n => A*aProcessShiftPoint η 0 (y n)
          let k := A*η
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+k)
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+k))-
            F (modelPhaseInverseSlope F (u n))-k*modelPhaseInverseSlope F (u n+k))
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → V*k/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  classical
  let mesh := (2:ℝ)^(-(σ⁻¹+1))/8
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hmesh₂ : 4*mesh ≤ 2 := by
    have hh : (2:ℝ)^(-(σ⁻¹+1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by have := inv_pos.mpr hσ; linarith)
    dsimp [mesh]
    linarith
  let J := positiveSlopeChartIndices mesh
  have hJ : J.Nonempty := ⟨positiveSlopeChartIndex mesh (4*mesh),
    positiveSlopeChartIndex_mem hmesh ⟨le_rfl,hmesh₂⟩⟩
  have ht : J.attach.Nonempty := hJ.attach
  let B := fun j : {j // j∈J} => positiveSlopeChartScale mesh j.val
  have hBj (j : {j // j∈J}) : 0 < B j ∧ B j ≤ 2 := by
    have hh := positiveSlopeChartScale_bounds hmesh j.property
    exact ⟨hh.1,hh.2.trans (by norm_num)⟩
  have hlocal (j : {j // j∈J}) := actual_displacement_physical_chart_count
    hσ hA hA₂ (hBj j).1 (hBj j).2 hpair hε hp
  choose δj ηj hδj hηj hηhalfj Qj hQj Cj hCj hcount using hlocal
  obtain ⟨δw,ηw,hδw,hηw,hηhalfw,Qw,hQw,hwindow⟩ :=
    finite_moving_displacement_window hσ hA hA₂
  let δ := min δw (J.attach.inf' ht δj)
  let η₀ := min ηw (J.attach.inf' ht ηj)
  let Q := max Qw (J.attach.sup Qj)
  let C := 1+∑ j∈J.attach, Cj j
  have hδ : 0 < δ := lt_min hδw ((Finset.lt_inf'_iff ht).mpr (fun j _ => hδj j))
  have hη₀ : 0 < η₀ := lt_min hηw ((Finset.lt_inf'_iff ht).mpr (fun j _ => hηj j))
  have hηhalf : η₀ ≤ 1/2 := (min_le_left _ _).trans hηhalfw
  have hQ : 1 ≤ Q := hQw.trans (le_max_left _ _)
  have hC : 1 ≤ C := by
    have hh : 0 ≤ ∑ j∈J.attach, Cj j := Finset.sum_nonneg (fun j _ => by linarith [hCj j])
    dsimp [C]
    linarith
  refine ⟨δ,η₀,hδ,hη₀,hηhalf,Q,hQ,C,hC,?_⟩
  intro F η P V N K S y hF hη hηle hP hV hN hy hu huk u k d R hbox hK hn W hW hWhalf hnear
  let s := A^(σ⁻¹-1)/(σ⁻¹*η)
  let L := s*A*(1-η)
  let w := fun n => L*d n
  have hηwle : η ≤ ηw := hηle.trans (min_le_left _ _)
  have hηone : η < 1 := by linarith [hηwle,hηhalfw]
  have hL : 0 < L := by dsimp [L,s]; positivity
  have hFwindow := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hw₀ := hwindow F η hFwindow hη hηwle ℕ S y hy hu huk
  have hw (n : ℕ) (hns : n∈S) : w n∈Icc (4*mesh) 2 := by
    have hh := hw₀ n hns
    change L*d n ∈ Icc ((2:ℝ)^(-(σ⁻¹+1))/2) 2 at hh
    change L*d n∈Icc (4*mesh) 2
    rw [show 4*mesh=(2:ℝ)^(-(σ⁻¹+1))/2 by dsimp [mesh]; ring]
    exact hh
  let label := fun n => positiveSlopeChartIndex mesh (w n)
  have hlabel : ∀ n∈S, label n∈J := fun n hns => positiveSlopeChartIndex_mem hmesh (hw n hns)
  let cell := fun j : {j // j∈J} => S.filter (fun n => label n=j.val)
  have hcell (j : {j // j∈J}) :
      ((cell j).card:ℝ) ≤ Cj j*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
    let M := B j*P/L
    have hgeom (n : ℕ) (hni : n∈cell j) : 1 ≤ M ∧ M ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*M := by
      have hns := (Finset.mem_filter.mp hni).1
      have he : w n=L*(n:ℝ)/P := by
        dsimp only [w]
        have hd : d n=(n:ℝ)/P := by
          apply (eq_div_iff hP.ne').mpr
          simpa [mul_comm] using hn n hns
        rw [hd]
        ring
      have hh := displacement_second_chart_geometry hmesh hL hP (hw n hns) (hbox n hns).1 he
      change label n∈J ∧ 0 < positiveSlopeChartScale mesh (label n) ∧
        positiveSlopeChartScale mesh (label n) ≤ 3/2 ∧
        1 ≤ positiveSlopeChartScale mesh (label n)*P/L ∧
        positiveSlopeChartScale mesh (label n)*P/L ≤ (n:ℝ) ∧
        (n:ℝ) ≤ 2*(positiveSlopeChartScale mesh (label n)*P/L) at hh
      rw [(Finset.mem_filter.mp hni).2] at hh
      exact hh.2.2.2
    by_cases hne : (cell j).Nonempty
    · obtain ⟨n,hni⟩ := hne
      have hFj := approximateModelPhase_mono hF
        ((Finset.le_sup (Finset.mem_attach J j)).trans (le_max_right _ _))
        ((min_le_right _ _).trans (Finset.inf'_le δj (Finset.mem_attach J j)))
      have hηjle : η ≤ ηj j := hηle.trans
        ((min_le_right _ _).trans (Finset.inf'_le ηj (Finset.mem_attach J j)))
      exact hcount j F η P V N K (cell j) y hFj hη hηjle hP hV hN
        (fun n hn => hy n (Finset.mem_filter.mp hn).1)
        (fun n hn => hu n (Finset.mem_filter.mp hn).1)
        (fun n hn => huk n (Finset.mem_filter.mp hn).1)
        (hgeom n hni).1 (fun n hn => (hgeom n hn).2)
        (fun n hn => (hbox n (Finset.mem_filter.mp hn).1).2) hK
        (fun n hni => hn n (Finset.mem_filter.mp hni).1) W hW hWhalf
        (fun n hn => hnear n (Finset.mem_filter.mp hn).1)
    · have he : cell j=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,Finset.card_empty,Nat.cast_zero]
      have hCj₀ : 0 ≤ Cj j := (by norm_num : (0:ℝ)≤1).trans (hCj j)
      positivity
  have hcard : (S.card:ℝ)=∑ j∈J.attach, ((cell j).card:ℝ) := by
    dsimp only [cell]
    rw [Finset.sum_attach J (fun j : ℕ => ((S.filter (fun n => label n=j)).card:ℝ))]
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hlabel
  let X := W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V
  have hX : 0 ≤ X := by dsimp [X]; positivity
  calc
    _ = ∑ j∈J.attach, ((cell j).card:ℝ) := hcard
    _ ≤ ∑ j∈J.attach, Cj j*X := Finset.sum_le_sum (fun j _ => hcell j)
    _ = (∑ j∈J.attach, Cj j)*X := (Finset.sum_mul _ _ _).symm
    _ ≤ C*X := by dsimp only [C]; nlinarith

#print axioms actual_displacement_first_chart_count
/-- A source-phase near-curve estimate with both auxiliary slope charts
eliminated. Tolerances, shift cap, derivative order and constant are all
chosen before the source phase and physical parameters. -/
theorem actual_displacement_near_curve_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 1 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (κ P V N : ℝ) (K : ℤ) (S : Finset ℕ) (u : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ → 0 < κ → κ ≤ κ₀ →
          0 < P → 0 < V → 0 < N →
          (∀ n∈S, u n ∈ modelPhaseSlopeRange F) →
          (∀ n∈S, u n+κ ∈ modelPhaseSlopeRange F) →
          let d := fun n => modelPhaseInverseSlope F (u n)-modelPhaseInverseSlope F (u n+κ)
          let R := fun n => 2*(F (modelPhaseInverseSlope F (u n+κ))-
            F (modelPhaseInverseSlope F (u n))-κ*modelPhaseInverseSlope F (u n+κ))
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) → V*κ/P=(K:ℝ) →
          (∀ n∈S, P*d n=(n:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ, |V*R n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
  classical
  let mesh := (2:ℝ)^(-σ)/8
  have hmesh : 0 < mesh := by dsimp [mesh]; positivity
  have hmesh₂ : 4*mesh ≤ 2 := by
    have hh : (2:ℝ)^(-σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    dsimp [mesh]
    linarith
  let J := positiveSlopeChartIndices mesh
  have hJ : J.Nonempty := ⟨positiveSlopeChartIndex mesh (4*mesh),
    positiveSlopeChartIndex_mem hmesh ⟨le_rfl,hmesh₂⟩⟩
  have ht : J.attach.Nonempty := hJ.attach
  let A := fun j : {j // j∈J} => positiveSlopeChartScale mesh j.val
  have hAj (j : {j // j∈J}) : 0 < A j ∧ A j ≤ 2 := by
    have hh := positiveSlopeChartScale_bounds hmesh j.property
    exact ⟨hh.1,hh.2.trans (by norm_num)⟩
  have hlocal (j : {j // j∈J}) := actual_displacement_first_chart_count
    hσ (hAj j).1 (hAj j).2 hpair hε hp
  choose δj ηj hδj hηj hηhalfj Qj hQj Cj hCj hcount using hlocal
  let δ := min (min ((2:ℝ)^(-σ)/2) 1) (J.attach.inf' ht δj)
  let ηmin := J.attach.inf' ht ηj
  let κ₀ := min mesh (3*mesh*ηmin)
  let Q := max 1 (J.attach.sup Qj)
  let C := 1+∑ j∈J.attach, Cj j
  have hδ : 0 < δ := lt_min (lt_min (by positivity) zero_lt_one)
    ((Finset.lt_inf'_iff ht).mpr (fun j _ => hδj j))
  have hηmin : 0 < ηmin := (Finset.lt_inf'_iff ht).mpr (fun j _ => hηj j)
  have hκ₀ : 0 < κ₀ := lt_min hmesh (by positivity)
  have hQ : 1 ≤ Q := le_max_left _ _
  have hC : 1 ≤ C := by
    have hh : 0 ≤ ∑ j∈J.attach, Cj j := Finset.sum_nonneg (fun j _ => by linarith [hCj j])
    dsimp [C]
    linarith
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F κ P V N K S u hF hκ hκle hP hV hN hu huk d R hbox hK hn W hW hWhalf hnear
  have hκmesh : κ ≤ mesh := hκle.trans (min_le_left _ _)
  have hw (n : ℕ) (hns : n∈S) : u n∈Icc (4*mesh) 2 := by
    rw [show 4*mesh=(2:ℝ)^(-σ)/2 by dsimp [mesh]; ring]
    exact modelPhaseSlopeRange_positive_window hσ (min_le_left _ _) hF (hu n hns)
  let label := fun n => positiveSlopeChartIndex mesh (u n)
  have hlabel : ∀ n∈S, label n∈J := fun n hns => positiveSlopeChartIndex_mem hmesh (hw n hns)
  let cell := fun j : {j // j∈J} => S.filter (fun n => label n=j.val)
  have hcell (j : {j // j∈J}) :
      ((cell j).card:ℝ) ≤ Cj j*(W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V) := by
    let η := κ/A j
    let y := fun n => (u n/A j-η)/(1-η)
    have hη : 0 < η := div_pos hκ (hAj j).1
    have hk : A j*η=κ := mul_div_cancel₀ κ (hAj j).1.ne'
    have hηle : η ≤ ηj j := by
      have hAmesh : 3*mesh ≤ A j := by
        have hj4 : (4:ℝ) ≤ j.val := by exact_mod_cast (Finset.mem_Icc.mp j.property).1
        dsimp [A,positiveSlopeChartScale]
        nlinarith [mul_le_mul_of_nonneg_right hj4 hmesh.le]
      have hcap : κ ≤ 3*mesh*ηmin := hκle.trans (min_le_right _ _)
      have hmin : ηmin ≤ ηj j := Finset.inf'_le ηj (Finset.mem_attach J j)
      apply (div_le_iff₀ (hAj j).1).mpr
      calc
        κ ≤ 3*mesh*ηmin := hcap
        _ ≤ A j*ηj j := mul_le_mul hAmesh hmin hηmin.le (hAj j).1.le
        _ = ηj j*A j := by ring
    have hgeom (n : ℕ) (hni : n∈cell j) :
        y n∈Ioo (1:ℝ) 2 ∧
          A j*aProcessShiftPoint η 0 (y n)=u n ∧
          A j*aProcessShiftPoint η 1 (y n)=u n+κ := by
      have hns := (Finset.mem_filter.mp hni).1
      have hh := positive_slope_chart_compressed_coordinate hmesh (hw n hns) hκ.le hκmesh
      dsimp only at hh
      have he : positiveSlopeChartIndex mesh (u n)=j.val := (Finset.mem_filter.mp hni).2
      rw [he] at hh
      exact hh.2.2.2.2.2
    have hFj := approximateModelPhase_mono hF
      ((Finset.le_sup (Finset.mem_attach J j)).trans (le_max_right _ _))
      ((min_le_right _ _).trans (Finset.inf'_le δj (Finset.mem_attach J j)))
    have huj : ∀ n∈cell j, A j*aProcessShiftPoint η 0 (y n)∈modelPhaseSlopeRange F := by
      intro n hni
      rw [(hgeom n hni).2.1]
      exact hu n (Finset.mem_filter.mp hni).1
    have hukj : ∀ n∈cell j, A j*aProcessShiftPoint η 1 (y n)∈modelPhaseSlopeRange F := by
      intro n hni
      rw [(hgeom n hni).2.2]
      exact huk n (Finset.mem_filter.mp hni).1
    have hnj : ∀ n∈cell j, P*(modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n))-
        modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η))=(n:ℝ) := by
      intro n hni
      rw [(hgeom n hni).2.1,hk]
      exact hn n (Finset.mem_filter.mp hni).1
    have hnearj : ∀ n∈cell j, ∃ e : ℤ,
        |V*(2*(F (modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η))-
          F (modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)))-
          (A j*η)*modelPhaseInverseSlope F (A j*aProcessShiftPoint η 0 (y n)+A j*η)))-(e:ℝ)| ≤ W/2 := by
      intro n hni
      rw [(hgeom n hni).2.1,hk]
      exact hnear n (Finset.mem_filter.mp hni).1
    exact hcount j F η P V N K (cell j) y hFj hη hηle hP hV hN
      (fun n hn => (hgeom n hn).1) huj hukj
      (fun n hn => hbox n (Finset.mem_filter.mp hn).1)
      (by rw [hk]; exact hK) hnj W hW hWhalf hnearj
  have hcard : (S.card:ℝ)=∑ j∈J.attach, ((cell j).card:ℝ) := by
    dsimp only [cell]
    rw [Finset.sum_attach J (fun j : ℕ => ((S.filter (fun n => label n=j)).card:ℝ))]
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hlabel
  let X := W*N+(V/P)^(k₀+ε)*N^(l₀+ε)*W^(-(k₀+ε))+P/V
  have hX : 0 ≤ X := by dsimp [X]; positivity
  calc
    _ = ∑ j∈J.attach, ((cell j).card:ℝ) := hcard
    _ ≤ ∑ j∈J.attach, Cj j*X := Finset.sum_le_sum (fun j _ => hcell j)
    _ = (∑ j∈J.attach, Cj j)*X := (Finset.sum_mul _ _ _).symm
    _ ≤ C*X := by dsimp only [C]; nlinarith

#print axioms actual_displacement_near_curve_count
/-- The derivative-model phase agrees with the ordinary derivatives on the
actual open source interval. -/
theorem negative_first_derivative_point
    {σ δ z : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hz : z∈Ioo (1:ℝ) 2) :
    let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
    G z=-σ⁻¹*deriv F z ∧ deriv G z=-σ⁻¹*deriv (deriv F) z := by
  intro G
  have he : G =ᶠ[𝓝 z] (fun u => -σ⁻¹*deriv F u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with u hu
    dsimp [G]
    rw [iteratedDerivWithin_one]
    have hd : derivWithin F phaseInterval u=deriv F u :=
      derivWithin_of_mem_nhds (Icc_mem_nhds hu.1 hu.2)
    rw [hd]
  refine ⟨he.eq_of_nhds,?_⟩
  rw [he.deriv_eq]
  exact ((approximateModelPhase_deriv_contDiffAt hF hz).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.const_mul (-σ⁻¹) |>.deriv

/-- The exact original second-derivative level produces the actual inverse-
slope displacement and stationary near-integer phase, with all physical
scales and signs linked. No independent dual phase is supplied. -/
theorem original_derivative_resonance_displacement
    {σ δ T N x q : ℝ} {P : ℕ} {F : ℝ → ℝ} {K : ℤ}
    (hσ : 0 < σ) (hT : 0 < T) (hN : 0 < N) (hP : 1 ≤ P)
    (hδ : δ/σ ≤ min (modelPhaseCurvatureLower (σ+1)) 1)
    (hF : IsApproximateModelPhaseFunction F σ (P+1) δ)
    (hx : x/N∈Ioo (1:ℝ) 2) (hxq : (x+q)/N∈Ioo (1:ℝ) 2) :
    let f := fun z => T*F (z/N)
    let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
    let κ := 2*(K:ℝ)*N^2/(σ*T)
    let V := σ*T/(2*N)
    let u := deriv G ((x+q)/N)
    (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ) →
    u∈modelPhaseSlopeRange G ∧ u+κ∈modelPhaseSlopeRange G ∧
      modelPhaseInverseSlope G u=(x+q)/N ∧
      modelPhaseInverseSlope G (u+κ)=x/N ∧
      N*(modelPhaseInverseSlope G u-modelPhaseInverseSlope G (u+κ))=q ∧
      V*κ/N=(K:ℝ) ∧
      V*(2*(G (modelPhaseInverseSlope G (u+κ))-G (modelPhaseInverseSlope G u)-
          κ*modelPhaseInverseSlope G (u+κ)))=
        iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x := by
  intro f G κ V u hlevel
  have hG := negative_first_derivative_model hσ hF
  have hG₁ := approximateModelPhase_mono hG hP (le_refl (δ/σ))
  have hσ₁ : 0 < σ+1 := by linarith
  have hf : modelPhaseFrequencyPhase F T N 0=f := by
    funext z
    simp [modelPhaseFrequencyPhase,f]
  have hd (z : ℝ) (hz : z/N∈Ioo (1:ℝ) 2) :
      iteratedDeriv 1 f z=T/N*deriv F (z/N) ∧
      iteratedDeriv 2 f z=T/N^2*deriv (deriv F) (z/N) := by
    constructor
    · simpa only [hf,iteratedDeriv_one,sub_zero] using
        (modelPhaseFrequencyPhase_hasDerivAt (T:=T) (r:=0) hF hz).deriv
    · simpa only [hf,
        iteratedDeriv_succ,iteratedDeriv_zero] using
        (modelPhaseFrequencyPhase_secondDeriv (T:=T) (r:=0) hF hz)
  have hκeq : u+κ=deriv G (x/N) := by
    dsimp only [u]
    rw [(negative_first_derivative_point hF hxq).2,(negative_first_derivative_point hF hx).2]
    rw [(hd (x+q) hxq).2,(hd x hx).2] at hlevel
    dsimp only [κ]
    field_simp [hσ.ne',hT.ne',hN.ne'] at hlevel ⊢
    nlinarith only [hlevel]
  have hu : u∈modelPhaseSlopeRange G := ⟨(x+q)/N,hxq,rfl⟩
  have huk : u+κ∈modelPhaseSlopeRange G := by rw [hκeq]; exact ⟨x/N,hx,rfl⟩
  have hi : modelPhaseInverseSlope G u=(x+q)/N :=
    modelPhaseInverseSlope_deriv hσ₁ hδ hG₁ hxq
  have hik : modelPhaseInverseSlope G (u+κ)=x/N := by
    rw [hκeq]
    exact modelPhaseInverseSlope_deriv hσ₁ hδ hG₁ hx
  refine ⟨hu,huk,hi,hik,?_,?_,?_⟩
  · rw [hi,hik]
    field_simp
    ring
  · dsimp [V,κ]
    field_simp
  · have hGx : G (x/N)=-σ⁻¹*deriv F (x/N) := (negative_first_derivative_point hF hx).1
    have hGxq : G ((x+q)/N)=-σ⁻¹*deriv F ((x+q)/N) :=
      (negative_first_derivative_point hF hxq).1
    rw [hi,hik,hGx,hGxq,(hd (x+q) hxq).1,(hd x hx).1]
    dsimp [V,κ]
    field_simp
    ring

#print axioms negative_first_derivative_point
#print axioms original_derivative_resonance_displacement
/-- Count actual original-source stationary derivative resonances.
The exact second-derivative level is the geometric input; the estimate
itself is derived from the exponent pair through the chart-free double
dual and Fourier count. -/
theorem original_second_level_near_curve_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D : ℝ) (K : ℤ) (S : Finset ℕ) (x : ℕ → ℝ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 0 < D → 0 < K →
          2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ →
          (∀ n∈S, x n/N ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, (x n+(n:ℝ))/N ∈ Ioo (1:ℝ) 2) →
          (∀ n∈S, 2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*D) →
          let f := fun z => T*F (z/N)
          (∀ n∈S, (iteratedDeriv 2 f (x n+(n:ℝ))-iteratedDeriv 2 f (x n))/2=(K:ℝ)) →
          ∀ (W : ℝ), 0 < W → W ≤ 1/2 →
          (∀ n∈S, ∃ e : ℤ,
            |iteratedDeriv 1 f (x n+(n:ℝ))-iteratedDeriv 1 f (x n)-
              2*(K:ℝ)*x n-(e:ℝ)| ≤ W/2) →
            (S.card:ℝ) ≤ C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T) := by
  have hσ₁ : 0 < σ+1 := by linarith
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q,hQ,C₀,hC₀,hcount⟩ :=
    actual_displacement_near_curve_count hσ₁ hpair hε hp
  let δg := min δ₀ (min (modelPhaseCurvatureLower (σ+1)) 1)
  let δ := σ*δg
  let p := k₀+ε
  let a := (σ/2)^p
  let b := 2/σ
  let L := 1+a+b
  let C := C₀*L
  have hδg : 0 < δg := lt_min hδ₀
    (lt_min (modelPhaseCurvatureLower_pos hσ₁) zero_lt_one)
  have hδ : 0 < δ := mul_pos hσ hδg
  have hquot : δ/σ=δg := by dsimp [δ]; field_simp
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC₀) (sub_nonneg.mpr hL)]
  refine ⟨δ,κ₀,hδ,hκ₀,Q+1,by omega,C,hC,?_⟩
  intro F T N D K S x hF hT hN hD hK hκle hx hxq hbox f hlevel W hW hWhalf hnear
  let G := fun u => -σ⁻¹*iteratedDerivWithin 1 F phaseInterval u
  let κ := 2*(K:ℝ)*N^2/(σ*T)
  let V := σ*T/(2*N)
  let u := fun n => deriv G ((x n+(n:ℝ))/N)
  have hκ : 0 < κ := by
    have hKr : 0 < (K:ℝ) := by exact_mod_cast hK
    dsimp [κ]
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hG : IsApproximateModelPhaseFunction G (σ+1) Q δ₀ := by
    have hh := negative_first_derivative_model hσ hF
    rw [hquot] at hh
    exact approximateModelPhase_mono hh le_rfl (min_le_left _ _)
  have hgeom (n : ℕ) (hns : n∈S) :=
    original_derivative_resonance_displacement hσ hT hN hQ
      (by rw [hquot]; exact min_le_right _ _)
      hF (hx n hns) (hxq n hns) (hlevel n hns)
  have hu : ∀ n∈S, u n∈modelPhaseSlopeRange G := fun n hns => (hgeom n hns).1
  have huk : ∀ n∈S, u n+κ∈modelPhaseSlopeRange G := fun n hns => (hgeom n hns).2.1
  have hdis : ∀ n∈S, N*(modelPhaseInverseSlope G (u n)-modelPhaseInverseSlope G (u n+κ))=(n:ℝ) :=
    fun n hns => (hgeom n hns).2.2.2.2.1
  have hres : V*κ/N=(K:ℝ) := by dsimp [V,κ]; field_simp
  have hnear' : ∀ n∈S, ∃ e : ℤ,
      |V*(2*(G (modelPhaseInverseSlope G (u n+κ))-G (modelPhaseInverseSlope G (u n))-
          κ*modelPhaseInverseSlope G (u n+κ)))-(e:ℝ)| ≤ W/2 := by
    intro n hns
    have hh := (hgeom n hns).2.2.2.2.2.2
    change V*(2*(G (modelPhaseInverseSlope G (u n+κ))-G (modelPhaseInverseSlope G (u n))-
      κ*modelPhaseInverseSlope G (u n+κ)))=
        iteratedDeriv 1 f (x n+(n:ℝ))-iteratedDeriv 1 f (x n)-2*(K:ℝ)*x n at hh
    rw [hh]
    exact hnear n hns
  have hh := hcount G κ N V D K S u hG hκ hκle hN hV hD hu huk hbox hres hdis W hW hWhalf hnear'
  have hfreq : (V/N)^p=a*(T/N^2)^p := by
    have he : V/N=(σ/2)*(T/N^2) := by dsimp [V]; field_simp
    rw [he,Real.mul_rpow (by positivity : 0 ≤ σ/2) (by positivity : 0 ≤ T/N^2)]
  have htail : N/V=b*(N^2/T) := by dsimp [V,b]; field_simp
  change (S.card:ℝ) ≤ C₀*(W*D+(V/N)^p*D^(l₀+ε)*W^(-p)+N/V) at hh
  rw [hfreq,htail] at hh
  have haL : a ≤ L := by dsimp [L]; linarith
  have hbL : b ≤ L := by dsimp [L]; linarith
  have hv : W*D ≤ L*(W*D) := le_mul_of_one_le_left (by positivity) hL
  calc
    _ ≤ C₀*(W*D+a*((T/N^2)^p*D^(l₀+ε)*W^(-p))+b*(N^2/T)) := by
      convert hh using 1; ring
    _ ≤ C₀*(L*(W*D)+L*((T/N^2)^p*D^(l₀+ε)*W^(-p))+L*(N^2/T)) := by gcongr
    _ = _ := by dsimp [C,p]; ring

#print axioms original_second_level_near_curve_count

end TaoTrudgianYang2025.DisplacementDualPrototype

noncomputable section
open Set MeasureTheory GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025.CubicNearCurveGeometry

/-- The actual second-derivative difference has a signed derivative with
the correct displacement factor. -/
theorem cubic_second_difference_derivative
    (f : ℝ → ℝ) {x q B lam : ℝ} (hq : 0 < q)
    (hf : ∀ t∈Icc x (x+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc x (x+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) :
    HasDerivAt (fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2)
      ((iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2) x ∧
    -(B*q/2) ≤ (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ∧
      (iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x)/2 ≤ -(lam*q/2) := by
  have hxx : x ≤ x+q := by linarith
  have hd (t : ℝ) (ht : t∈Icc x (x+q)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  have hd₀ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf x ⟨le_rfl,hxx⟩)
  have hd₁ := hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 4)
    (hf (x+q) ⟨hxx,le_rfl⟩)
  constructor
  · convert ((hd₁.comp x ((hasDerivAt_id x).add_const q)).sub hd₀).div_const 2 using 1; ring
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) (show x < x+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' : iteratedDeriv 4 f t*q=iteratedDeriv 3 f (x+q)-iteratedDeriv 3 f x := by
    have hh := (eq_div_iff (show x+q-x ≠ 0 by linarith)).mp he
    nlinarith only [hh]
  have hlo := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩).1 hq.le
  have hhi := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩).2 hq.le
  constructor <;> nlinarith only [he',hlo,hhi]

/-- A near-resonant second derivative is moved to its exact integer
level inside the prescribed physical buffer. -/
theorem cubic_exact_second_difference_level
    (f : ℝ → ℝ) {n q B lam R δ K : ℝ}
    (hq : 0 < q) (hR : 0 < R)
    (hbudget : δ ≤ lam*q*R/2)
    (hf : ∀ t∈Icc (n-R) (n+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc (n-R) (n+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    ∃ x∈Icc (n-R) (n+R),
      (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=K ∧ |x-n| ≤ R := by
  let g := fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2
  let dg := fun t => (iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t)/2
  have hsub (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      Icc x (x+q) ⊆ Icc (n-R) (n+R+q) := by
    intro t ht
    constructor <;> linarith [hx.1,hx.2,ht.1,ht.2]
  have hd (x : ℝ) (hx : x∈Icc (n-R) (n+R)) :
      HasDerivAt g (dg x) x ∧ dg x ≤ -(lam*q/2) := by
    have hh := cubic_second_difference_derivative f hq
      (fun t ht => hf t (hsub x hx ht)) (fun t ht => hfour t (hsub x hx ht))
    exact ⟨hh.1,hh.2.2⟩
  have hdec {a b : ℝ} (hab : a < b)
      (ha : n-R ≤ a) (hb : b ≤ n+R) :
      g b-g a ≤ -(lam*q/2)*(b-a) := by
    have hi (t : ℝ) (ht : t∈Icc a b) : t∈Icc (n-R) (n+R) :=
      ⟨ha.trans ht.1,ht.2.trans hb⟩
    obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g dg hab
      (fun t ht => (hd t (hi t ht)).1.continuousAt.continuousWithinAt)
      (fun t ht => (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).1)
    have he' := (eq_div_iff (sub_pos.mpr hab).ne').mp he
    have hh := mul_le_mul_of_nonneg_right (hd t (hi t ⟨ht.1.le,ht.2.le⟩)).2
      (sub_nonneg.mpr hab.le)
    nlinarith only [he',hh]
  have hleft := hdec (a:=n-R) (b:=n) (by linarith) le_rfl (by linarith)
  have hright := hdec (a:=n) (b:=n+R) (by linarith) (by linarith) le_rfl
  have hnear' : |g n-K| ≤ δ := hnear
  have hK : K∈Icc (g (n+R)) (g (n-R)) := by
    have hh := abs_le.mp hnear'
    constructor <;> nlinarith only [hleft,hright,hbudget,hh.1,hh.2]
  obtain ⟨x,hx,he⟩ := intermediate_value_Icc' (by linarith : n-R ≤ n+R)
    (fun t ht => (hd t ht).1.continuousAt.continuousWithinAt) hK
  exact ⟨x,hx,he,abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩⟩

/-- The exact level curve preserves the first-derivative integer
resonance up to a quadratic error, not a first-order displacement loss. -/
theorem cubic_stationary_curve_near_integer
    (f : ℝ → ℝ) (n K e : ℤ) {x q B lam R δ : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hR : 0 ≤ R)
    (hx : x∈Icc ((n:ℝ)-R) ((n:ℝ)+R))
    (hf : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((n:ℝ)-R) ((n:ℝ)+R+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hlevel : (iteratedDeriv 2 f (x+q)-iteratedDeriv 2 f x)/2=(K:ℝ))
    (hnear : |iteratedDeriv 1 f ((n:ℝ)+q)-iteratedDeriv 1 f n-(e:ℝ)| ≤ δ) :
    |(iteratedDeriv 1 f (x+q)-iteratedDeriv 1 f x-2*(K:ℝ)*x)-
      ((e-2*K*n:ℤ):ℝ)| ≤ δ+B*q*R^2 := by
  let G := fun t => iteratedDeriv 1 f (t+q)-iteratedDeriv 1 f t-2*(K:ℝ)*t
  let G₁ := fun t => iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t-2*(K:ℝ)
  let G₂ := fun t => iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t
  have hsub (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : t∈Icc ((n:ℝ)-R) ((n:ℝ)+R) :=
    (convex_Icc _ _).ordConnected.uIcc_subset hx ⟨by linarith,by linarith⟩ ht
  have hseg (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      Icc t (t+q) ⊆ Icc ((n:ℝ)-R) ((n:ℝ)+R+q) := by
    intro z hz
    have hh := hsub t ht
    constructor <;> linarith [hh.1,hh.2,hz.1,hz.2]
  have hjets (t : ℝ) (ht : t∈uIcc x (n:ℝ)) :
      HasDerivAt G (G₁ t) t ∧ HasDerivAt G₁ (G₂ t) t ∧ |G₂ t| ≤ B*q := by
    have hI := hseg t ht
    have ht₀ := hf t (hI ⟨le_rfl,by linarith⟩)
    have ht₁ := hf (t+q) (hI ⟨by linarith,le_rfl⟩)
    have hd (j : ℕ) (hj : j < 4) :
        HasDerivAt (fun z => iteratedDeriv j f (z+q)-iteratedDeriv j f z)
          (iteratedDeriv (j+1) f (t+q)-iteratedDeriv (j+1) f t) t := by
      have h₀ := hasDerivAt_iteratedDeriv_finite hj ht₀
      have h₁ := hasDerivAt_iteratedDeriv_finite hj ht₁
      convert (h₁.comp t ((hasDerivAt_id t).add_const q)).sub h₀ using 1; ring
    constructor
    · convert (hd 1 (by norm_num)).sub ((hasDerivAt_id t).const_mul (2*(K:ℝ))) using 1; ring
    constructor
    · exact (hd 2 (by norm_num)).sub_const (2*(K:ℝ))
    · have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hI hz)) (fun z hz => hfour z (hI hz))
      dsimp only [G₂]
      apply abs_le.mpr
      constructor <;> nlinarith [hh.2.1,hh.2.2,mul_pos hlam hq]
  have hB : 0 ≤ B := by
    have hh := hfour n ⟨by linarith,by linarith⟩
    linarith [hh.1,hh.2]
  have hG₁x : G₁ x=0 := by dsimp only [G₁]; linarith only [hlevel]
  have hdist : |(n:ℝ)-x| ≤ R := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  have hfirst (t : ℝ) (ht : t∈uIcc x (n:ℝ)) : |G₁ t| ≤ B*q*R := by
    have hh := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hjets z hz).2.1.hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using (hjets z hz).2.2)
      left_mem_uIcc ht
    rw [hG₁x,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      ((abs_sub_left_of_mem_uIcc ht).trans hdist) (mul_nonneg hB hq.le))
  have herror := (convex_uIcc x (n:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hjets z hz).1.hasDerivWithinAt)
    (fun z hz => by simpa only [Real.norm_eq_abs] using hfirst z hz)
    left_mem_uIcc right_mem_uIcc
  rw [Real.norm_eq_abs,Real.norm_eq_abs] at herror
  have herror' : |G x-G n| ≤ B*q*R^2 := by
    rw [abs_sub_comm]
    exact herror.trans ((mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ B*q*R)).trans_eq (by ring))
  have hnear' : |G n-((e-2*K*n:ℤ):ℝ)| ≤ δ := by
    convert hnear using 1
    congr 1
    dsimp only [G]
    push_cast
    ring
  have hh := (abs_sub_le (G x) (G n) ((e-2*K*n:ℤ):ℝ)).trans (add_le_add herror' hnear')
  change |G x-((e-2*K*n:ℤ):ℝ)| ≤ _
  exact hh.trans_eq (by ring)

#print axioms cubic_second_difference_derivative
#print axioms cubic_exact_second_difference_level
#print axioms cubic_stationary_curve_near_integer

open SquareProductCount.CubicSource

/-- Integer resonances extracted from the actual source-label pair set.
The third coordinate is not reduced modulo integers. -/
theorem cubicDerivativePairs_integer_resonances
    (f : ℝ → ℝ) {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈cubicDerivativePairs f M H) :
    p.1 < M ∧ p.2 < M ∧
    ∃ e K : ℤ,
      |iteratedDeriv 1 f ((p.2:ℝ)+1)-iteratedDeriv 1 f ((p.1:ℝ)+1)-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
      |(iteratedDeriv 2 f ((p.2:ℝ)+1)-iteratedDeriv 2 f ((p.1:ℝ)+1))/2-(K:ℝ)| ≤
        1/(4*(H:ℝ)^2) ∧
      |iteratedDeriv 3 f ((p.2:ℝ)+1)-iteratedDeriv 3 f ((p.1:ℝ)+1)| ≤
        3/(2*(H:ℝ)^3) := by
  obtain ⟨hmem,hnear⟩ := Finset.mem_filter.mp hp
  have hmem' := Finset.mem_product.mp hmem
  refine ⟨Finset.mem_range.mp hmem'.1,Finset.mem_range.mp hmem'.2,
    ⌊deriv f ((p.2:ℝ)+1)⌋-⌊deriv f ((p.1:ℝ)+1)⌋,
    ⌊iteratedDeriv 2 f ((p.2:ℝ)+1)/2⌋-⌊iteratedDeriv 2 f ((p.1:ℝ)+1)/2⌋,
    ?_,?_,?_⟩
  · have hh := hnear 0
    change |Int.fract (deriv f ((p.1:ℝ)+1))-Int.fract (deriv f ((p.2:ℝ)+1))| ≤
      2*(1/(8*(H:ℝ))) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub,iteratedDeriv_one]
      ring
    · ring
  · have hh := hnear 1
    change |Int.fract (iteratedDeriv 2 f ((p.1:ℝ)+1)/2)-
      Int.fract (iteratedDeriv 2 f ((p.2:ℝ)+1)/2)| ≤ 2*(1/(8*(H:ℝ)^2)) at hh
    rw [abs_sub_comm] at hh
    convert hh using 1
    · congr 1
      simp only [Int.fract,Int.cast_sub]
      ring
    · ring
  · have hh := hnear 2
    change |iteratedDeriv 3 f ((p.1:ℝ)+1)/6-iteratedDeriv 3 f ((p.2:ℝ)+1)/6| ≤
      2*(1/(8*(H:ℝ)^3)) at hh
    rw [abs_sub_comm,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<6)] at hh
    have he := (div_le_iff₀ (by norm_num : (0:ℝ)<6)).mp hh
    exact he.trans_eq (by ring)

/-- Fourth-derivative separation bounds the actual integer displacement. -/
theorem cubicDerivativePairs_displacement
    (f : ℝ → ℝ) {M H : ℕ} {p : ℕ × ℕ} {lam : ℝ}
    (hH : 1 ≤ H) (hlam : 0 < lam)
    (hp : p∈cubicDerivativePairs f M H) (hlt : p.1 < p.2)
    (hf : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 f t ≤ -lam) :
    (p.2:ℝ)-p.1 ≤ 3/(2*lam*(H:ℝ)^3) := by
  obtain ⟨_,_,e,K,_hfirst,_hsecond,hthird⟩ := cubicDerivativePairs_integer_resonances f hp
  have hHpos : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hxy : (p.1:ℝ)+1 < (p.2:ℝ)+1 := by exact_mod_cast Nat.add_lt_add_right hlt 1
  have hd (t : ℝ) (ht : t∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) :
      HasDerivAt (iteratedDeriv 3 f) (iteratedDeriv 4 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=3) (by norm_num : 3 < 4) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 3 f)
    (iteratedDeriv 4 f) hxy
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (sub_pos.mpr hxy).ne').mp he
  have hlow := mul_le_mul_of_nonneg_right (hfour t ⟨ht.1.le,ht.2.le⟩) (sub_pos.mpr hxy).le
  have hprod : lam*((p.2:ℝ)-p.1) ≤ 3/(2*(H:ℝ)^3) := by
    have hab := abs_le.mp hthird
    nlinarith only [he',hlow,hab.1]
  have hh : (p.2:ℝ)-p.1 ≤ (3/(2*(H:ℝ)^3))/lam :=
    (le_div_iff₀ hlam).mpr (by nlinarith only [hprod])
  exact hh.trans_eq (by ring)

/-- Multiplicity of one exact displacement/level label; this controls
actual integer source points, including both closed endpoints. -/
theorem cubic_second_difference_fiber_card
    (f : ℝ → ℝ) (S : Finset ℤ) {a b q B lam δ K : ℝ}
    (hq : 0 < q) (hlam : 0 < lam) (hδ : 0 ≤ δ)
    (hf : ∀ t∈Icc a (b+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc a (b+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hS : ∀ n∈S, (n:ℝ)∈Icc a b)
    (hnear : ∀ n∈S, |(iteratedDeriv 2 f ((n:ℝ)+q)-iteratedDeriv 2 f n)/2-K| ≤ δ) :
    (S.card:ℝ) ≤ 4*δ/(lam*q)+1 := by
  classical
  by_cases hne : S.Nonempty
  · let n₀ := S.min' hne
    have hn₀ : n₀∈S := Finset.min'_mem S hne
    let g := fun t => (iteratedDeriv 2 f (t+q)-iteratedDeriv 2 f t)/2
    let dg := fun t => (iteratedDeriv 3 f (t+q)-iteratedDeriv 3 f t)/2
    have hd (t : ℝ) (ht : t∈Icc a b) : HasDerivAt g (dg t) t ∧ dg t ≤ -(lam*q/2) := by
      have hsub : Icc t (t+q) ⊆ Icc a (b+q) := by
        intro z hz
        constructor <;> linarith [ht.1,ht.2,hz.1,hz.2]
      have hh := cubic_second_difference_derivative f hq
        (fun z hz => hf z (hsub hz)) (fun z hz => hfour z (hsub hz))
      exact ⟨hh.1,hh.2.2⟩
    have hbound (n : ℤ) (hn : n∈S) :
        (n₀:ℝ) ≤ n ∧ (n:ℝ) ≤ n₀+4*δ/(lam*q) := by
      have hle : n₀ ≤ n := Finset.min'_le S n hn
      have hleR : (n₀:ℝ) ≤ n := by exact_mod_cast hle
      refine ⟨hleR,?_⟩
      rcases eq_or_lt_of_le hleR with heq|hlt
      · rw [←heq]
        exact le_add_of_nonneg_right (by positivity)
      have hsub (t : ℝ) (ht : t∈Icc (n₀:ℝ) n) : t∈Icc a b :=
        ⟨(hS n₀ hn₀).1.trans ht.1,ht.2.trans (hS n hn).2⟩
      obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope g dg hlt
        (fun t ht => (hd t (hsub t ht)).1.continuousAt.continuousWithinAt)
        (fun t ht => (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).1)
      have he' := (eq_div_iff (sub_pos.mpr hlt).ne').mp he
      have hdec := mul_le_mul_of_nonneg_right (hd t (hsub t ⟨ht.1.le,ht.2.le⟩)).2
        (sub_pos.mpr hlt).le
      have hnear₀ : |g n₀-K| ≤ δ := hnear n₀ hn₀
      have hnear₁ : |g n-K| ≤ δ := hnear n hn
      have hp : ((n:ℝ)-n₀)*(lam*q) ≤ 4*δ := by
        have hh₀ := abs_le.mp hnear₀
        have hh₁ := abs_le.mp hnear₁
        nlinarith only [he',hdec,hh₀.2,hh₁.1]
      have hh := (le_div_iff₀ (mul_pos hlam hq)).mpr hp
      linarith
    have hinterval : (n₀:ℝ) ≤ n₀+4*δ/(lam*q) :=
      le_add_of_nonneg_right (by positivity)
    have hcount := integer_card_le_interval_length_add_one S hinterval
      hbound
    exact hcount.trans_eq (by ring)
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

#print axioms cubicDerivativePairs_integer_resonances
#print axioms cubicDerivativePairs_displacement
#print axioms cubic_second_difference_fiber_card

/-- In the short-source regime an off-diagonal integer second-derivative
level is positive. Its displacement is at least the reciprocal third-
derivative scale; this controls the exact-level buffer near the source edges. -/
theorem cubic_second_level_positive
    (f : ℝ → ℝ) (K : ℤ) {n q L U δ : ℝ}
    (hq : 1 ≤ q) (hL : 0 < L)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc n (n+q), ContDiffAt ℝ 3 f t)
    (hthree : ∀ t∈Icc n (n+q),
      L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hnear : |(iteratedDeriv 2 f (n+q)-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ) :
    0 < K ∧ 0 < U ∧ 1/U ≤ q ∧ (K:ℝ) ≤ U*q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hU : 0 < U := hL.trans_le ((hthree n ⟨le_rfl,by linarith⟩).1.trans
    (hthree n ⟨le_rfl,by linarith⟩).2)
  have hd (t : ℝ) (ht : t∈Icc n (n+q)) :
      HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f t) t :=
    hasDerivAt_iteratedDeriv_finite (j:=2) (by norm_num : 2 < 3) (hf t ht)
  obtain ⟨t,ht,he⟩ := exists_hasDerivAt_eq_slope (iteratedDeriv 2 f)
    (iteratedDeriv 3 f) (show n < n+q by linarith)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t ⟨ht.1.le,ht.2.le⟩)
  have he' := (eq_div_iff (show n+q-n ≠ 0 by linarith)).mp he
  have hlo := mul_le_mul_of_nonneg_right (hthree t ⟨ht.1.le,ht.2.le⟩).1 hqpos.le
  have hhi := mul_le_mul_of_nonneg_right (hthree t ⟨ht.1.le,ht.2.le⟩).2 hqpos.le
  have hab := abs_le.mp hnear
  have hLq : L ≤ L*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hL.le]
  have hKpos : (0:ℝ) < K := by nlinarith only [he',hlo,hab.2,hδL,hLq,hL]
  have hKi : 0 < K := by exact_mod_cast hKpos
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast (show (1:ℤ) ≤ K by omega)
  refine ⟨hKi,hU,?_,?_⟩
  · apply (div_le_iff₀ hU).mpr
    nlinarith only [he',hhi,hab.1,hδhalf,hK1]
  · have hLU : L ≤ U := (hthree t ⟨ht.1.le,ht.2.le⟩).1.trans
      (hthree t ⟨ht.1.le,ht.2.le⟩).2
    have hUq : U ≤ U*q := by nlinarith only [mul_le_mul_of_nonneg_left hq hU.le]
    nlinarith only [he',hhi,hab.1,hδL,hLU,hUq,hU]

-- The actual diagonal is retained for every source label.
example (f : ℝ → ℝ) {M H n : ℕ} (hH : 1 ≤ H) (hn : n < M) :
    (n,n)∈cubicDerivativePairs f M H := by
  unfold cubicDerivativePairs cubicSamplePairs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hn,Finset.mem_range.mpr hn⟩,?_⟩
  intro d
  simp only [sub_self,abs_zero]
  exact (mul_pos (by norm_num : (0:ℝ)<2) (cubicSamplingScale_pos hH d)).le

-- A zero-width level fiber has at most one integer source point.
example (f : ℝ → ℝ) (S : Finset ℤ) {a b q B lam K : ℝ}
    (hq : 0 < q) (hlam : 0 < lam)
    (hf : ∀ t∈Icc a (b+q), ContDiffAt ℝ 4 f t)
    (hfour : ∀ t∈Icc a (b+q),
      -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hS : ∀ n∈S, (n:ℝ)∈Icc a b)
    (hlevel : ∀ n∈S, (iteratedDeriv 2 f ((n:ℝ)+q)-iteratedDeriv 2 f n)/2=K) :
    S.card ≤ 1 := by
  have hh := cubic_second_difference_fiber_card f S (K:=K) hq hlam (le_refl (0:ℝ))
    hf hfour hS (fun n hn => by rw [hlevel n hn]; simp)
  norm_num only [mul_zero,zero_div,zero_add] at hh
  exact_mod_cast hh

#print axioms cubic_second_level_positive

end TaoTrudgianYang2025.CubicNearCurveGeometry

namespace TaoTrudgianYang2025.DisplacementDualPrototype
/-- One actual integer level and dyadic displacement block, including every
integer source-point multiplicity. The fourth-derivative and buffer
hypotheses are explicit local geometric inputs, not a count assumption. -/
theorem original_joint_level_block_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 2 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D a b R B lam δ₁ δ₂ W : ℝ)
          (K : ℤ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ D → 0 < R → 0 ≤ B → 0 < lam → 0 ≤ δ₂ →
          N < a-R → b+R+2*D < 2*N →
          δ₂ ≤ lam*D*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          0 < K → 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ t∈Icc (a-R) (b+R+2*D),
            -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam) →
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc D (2*D)) →
          (∀ p∈S, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            (S.card:ℝ) ≤ (4*δ₂/(lam*D)+1)*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,hcount⟩ :=
    original_second_level_near_curve_count hσ hpair hε hp
  refine ⟨δ,κ₀,hδ,hκ₀,Q,hQ,C,hC,?_⟩
  intro F T N D a b R B lam δ₁ δ₂ W K S hF hT hN hD hR hB hlam hδ₂
    hleft hright hbuffer hwidth hK hκle hW hWhalf f hfour hbox hsecond hfirst
  have hDpos : 0 < D := by linarith
  let J := S.image Prod.snd
  have hmem (q : ℕ) (hq : q∈J) : D ≤ (q:ℝ) ∧ (q:ℝ) ≤ 2*D := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hbox p hp).2
  have hnorm (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) :
      t/N∈Ioo (1:ℝ) 2 := by
    constructor
    · apply (one_lt_div hN).mpr
      linarith [ht.1]
    · apply (div_lt_iff₀ hN).mpr
      linarith [ht.2]
  have hf (t : ℝ) (ht : t∈Icc (a-R) (b+R+2*D)) : ContDiffAt ℝ 4 f t := by
    have hc := (approximateModelPhase_contDiffAt hF (hnorm t ht)).comp t
      (show ContDiffAt ℝ ∞ (fun z : ℝ => z/N) t by fun_prop)
    exact (contDiffAt_const.mul hc).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)
  have hex (q : ℕ) (hq : q∈J) :
      ∃ x : ℝ, x/N∈Ioo (1:ℝ) 2 ∧ (x+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x+(q:ℝ))-iteratedDeriv 2 f x)/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x+(q:ℝ))-iteratedDeriv 1 f x-
          2*(K:ℝ)*x-(e:ℝ)| ≤ W/2 := by
    obtain ⟨p,hps,hpq⟩ := Finset.mem_image.mp hq
    have hpos : 0 < (q:ℝ) := hDpos.trans_le (hmem q hq).1
    have hpab : (p.1:ℝ)∈Icc a b := (hbox p hps).1
    have hsub : Icc ((p.1:ℝ)-R) ((p.1:ℝ)+R+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,hpab.1,hpab.2,(hmem q hq).2]
    have hbudget : δ₂ ≤ lam*(q:ℝ)*R/2 := hbuffer.trans (by gcongr; exact (hmem q hq).1)
    have hnear₂ : |(iteratedDeriv 2 f ((p.1:ℝ)+(q:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      simpa only [hpq] using hsecond p hps
    obtain ⟨x,hx,hlevel,_hdist⟩ := CubicNearCurveGeometry.cubic_exact_second_difference_level
      f hpos hR hbudget (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hnear₂
    obtain ⟨e,he⟩ := hfirst p hps
    rw [hpq] at he
    have hnear := CubicNearCurveGeometry.cubic_stationary_curve_near_integer
      f p.1 K e hpos hlam hR.le hx (fun t ht => hf t (hsub ht))
      (fun t ht => hfour t (hsub ht)) hlevel he
    have hxx : x∈Icc (a-R) (b+R+2*D) := hsub ⟨hx.1,by linarith [hx.2]⟩
    have hxxq : x+(q:ℝ)∈Icc (a-R) (b+R+2*D) :=
      hsub ⟨by linarith [hx.1],by linarith [hx.2]⟩
    refine ⟨x,hnorm x hxx,hnorm (x+q) hxxq,hlevel,e-2*K*p.1,?_⟩
    exact hnear.trans ((show δ₁+B*(q:ℝ)*R^2 ≤ δ₁+2*B*D*R^2 by
      nlinarith [mul_le_mul_of_nonneg_left (hmem q hq).2
        (mul_nonneg hB (sq_nonneg R))]).trans hwidth)
  let x := fun q => if hq : q∈J then Classical.choose (hex q hq) else 0
  have hx (q : ℕ) (hq : q∈J) :
      x q/N∈Ioo (1:ℝ) 2 ∧ (x q+(q:ℝ))/N∈Ioo (1:ℝ) 2 ∧
        (iteratedDeriv 2 f (x q+(q:ℝ))-iteratedDeriv 2 f (x q))/2=(K:ℝ) ∧
        ∃ e : ℤ, |iteratedDeriv 1 f (x q+(q:ℝ))-iteratedDeriv 1 f (x q)-
          2*(K:ℝ)*x q-(e:ℝ)| ≤ W/2 := by
    simp only [x,dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hcountJ := hcount F T N D K J x hF hT hN hDpos hK hκle
    (fun q hq => (hx q hq).1) (fun q hq => (hx q hq).2.1)
    (fun q hq => ⟨hD.trans (hmem q hq).1,(hmem q hq).2⟩)
    (fun q hq => (hx q hq).2.2.1) W hW hWhalf (fun q hq => (hx q hq).2.2.2)
  have hfiber (q : ℕ) (hq : q∈J) :
      ((S.filter (fun p => p.2=q)).card:ℝ) ≤ 4*δ₂/(lam*D)+1 := by
    let U := S.filter (fun p => p.2=q)
    let Y := U.image Prod.fst
    have hinj : Set.InjOn (Prod.fst : ℤ × ℕ → ℤ) U := by
      intro p hp r hr he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm)
    have hcard : Y.card=U.card := Finset.card_image_of_injOn hinj
    have hsub : Icc a (b+(q:ℝ)) ⊆ Icc (a-R) (b+R+2*D) := by
      intro t ht
      constructor <;> linarith [ht.1,ht.2,(hmem q hq).2]
    have hY : ∀ n∈Y, (n:ℝ)∈Icc a b := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      exact (hbox p (Finset.mem_filter.mp hp).1).1
    have hnear : ∀ n∈Y,
        |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ₂ := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      simpa only [(Finset.mem_filter.mp hp).2] using hsecond p (Finset.mem_filter.mp hp).1
    have hh := CubicNearCurveGeometry.cubic_second_difference_fiber_card f Y
      (hDpos.trans_le (hmem q hq).1) hlam hδ₂
      (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht)) hY hnear
    rw [hcard] at hh
    have hquot : 4*δ₂/(lam*(q:ℝ)) ≤ 4*δ₂/(lam*D) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hlam hDpos)
        (mul_le_mul_of_nonneg_left (hmem q hq).1 hlam.le)
    linarith only [hh,hquot]
  have hmaps : Set.MapsTo (Prod.snd : ℤ × ℕ → ℕ) S J := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard : (S.card:ℝ)=∑ q∈J, ((S.filter (fun p => p.2=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcard
    _ ≤ ∑ _q∈J, (4*δ₂/(lam*D)+1) := Finset.sum_le_sum hfiber
    _ = (4*δ₂/(lam*D)+1)*(J.card:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcountJ (by positivity)

#print axioms original_joint_level_block_count

-- Existing production derivative-data proof; scratch copy for composition.
private theorem model_displacement_derivative_data {σ : ℝ} (hσ : 0 < σ) :
    ∃ δ > (0:ℝ), ∀ (F : ℝ → ℝ) (T P : ℝ), 0 < T → 0 < P →
      Expdb.IsApproximateModelPhaseFunction F σ 3 δ →
      let f := fun x => T*F (x/P)
      (∀ x∈Ioo P (2*P), ContDiffAt ℝ 5 f x) ∧
      (∀ x∈Ioo P (2*P),
        modelPhaseJetLower σ 2*T/P^3 ≤ iteratedDeriv 3 f x ∧
        iteratedDeriv 3 f x ≤ (modelPhaseJetCoefficient σ 2+1)*T/P^3) ∧
      (∀ x∈Ioo P (2*P),
        -((modelPhaseJetCoefficient σ 3+1)*T/P^4) ≤ iteratedDeriv 4 f x ∧
        iteratedDeriv 4 f x ≤ -(modelPhaseJetLower σ 3*T/P^4)) ∧
      (∀ x∈Ioo P (2*P), |iteratedDeriv 2 f x/2| ≤
        (modelPhaseJetCoefficient σ 1+1)*T/P^2/2) := by
  let δ := min 1 (min (modelPhaseJetLower σ 2) (modelPhaseJetLower σ 3))
  have hδ : 0 < δ := lt_min (by norm_num)
    (lt_min (modelPhaseJetLower_pos hσ 2) (modelPhaseJetLower_pos hσ 3))
  refine ⟨δ,hδ,?_⟩
  intro F T P hT hP hF f
  have hpoint x (hx : x∈Ioo P (2*P)) : x/P∈Ioo (1:ℝ) 2 := by
    constructor
    · exact (lt_div_iff₀ hP).mpr (by simpa only [one_mul] using hx.1)
    · exact (div_lt_iff₀ hP).mpr hx.2
  have hfc x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ ∞ F (x/P) :=
    approximateModelPhase_contDiffAt hF (hpoint x hx)
  have hfd x (hx : x∈Ioo P (2*P)) : ContDiffAt ℝ ∞ f x := by
    dsimp only [f]
    exact contDiffAt_const.mul ((hfc x hx).comp x (by fun_prop))
  have hd x (hx : x∈Ioo P (2*P)) (n : ℕ) :
      iteratedDeriv n f x=T/P^n*iteratedDeriv n F (x/P) := by
    have hh : ∀ y∈Ioo P (2*P), ContDiffAt ℝ ∞ F (P⁻¹*y+0) := by
      intro y hy
      simpa only [add_zero,div_eq_mul_inv,mul_comm] using hfc y hy
    have ha := sargos_iteratedDeriv_comp_affine_local hh hx n
    simp only [add_zero] at ha
    have he : (fun y => F (y/P))=(fun y => F (P⁻¹*y)) := by
      funext y
      rw [div_eq_mul_inv,mul_comm]
    dsimp only [f]
    rw [iteratedDeriv_const_mul_field,he,ha,inv_pow]
    simp only [div_eq_mul_inv,mul_assoc,mul_comm P⁻¹ x]
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ min (modelPhaseJetLower σ 2) 1 :=
    le_min ((min_le_right _ _).trans (min_le_left _ _)) hδ1
  have hδ3 : δ ≤ min (modelPhaseJetLower σ 3) 1 :=
    le_min ((min_le_right _ _).trans (min_le_right _ _)) hδ1
  have hsign2 : modelPhaseJetSign σ 2=1 := by
    have he : (descPochhammer ℝ 2).eval (-σ)=σ*(σ+1) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one]
      ring
    unfold modelPhaseJetSign
    rw [he,if_pos (by positivity)]
  have hsign3 : modelPhaseJetSign σ 3= -1 := by
    have he : (descPochhammer ℝ 3).eval (-σ)= -(σ*(σ+1)*(σ+2)) := by
      simp only [descPochhammer_eval_eq_prod_range,Finset.prod_range_succ,
        Finset.prod_range_zero,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      ring
    unfold modelPhaseJetSign
    have hh : 0 < σ*(σ+1)*(σ+2) := by positivity
    rw [he,if_neg (by linarith only [hh])]
  refine ⟨fun x hx => (hfd x hx).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 5),?_,?_,?_⟩
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 2 (by norm_num) hδ2
    rw [hsign2,one_mul] at hh
    rw [hd x hx 3]
    constructor
    · convert mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^3 by positivity) using 1; ring
    · convert mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^3 by positivity) using 1; ring
  · intro x hx
    have hh := approximateModelPhase_signedJet_bounds hσ hF (hpoint x hx) 3 le_rfl hδ3
    rw [hsign3,neg_one_mul] at hh
    change modelPhaseJetLower σ 3 ≤ -iteratedDeriv 4 F (x/P) ∧
      -iteratedDeriv 4 F (x/P) ≤ modelPhaseJetCoefficient σ 3+1 at hh
    rw [hd x hx 4]
    have hlo := mul_le_mul_of_nonneg_left hh.1 (show 0 ≤ T/P^4 by positivity)
    have hhi := mul_le_mul_of_nonneg_left hh.2 (show 0 ≤ T/P^4 by positivity)
    constructor
    · convert neg_le_neg hhi using 1 <;> ring
    · convert neg_le_neg hlo using 1 <;> ring
  · intro x hx
    have hh := approximateModelPhase_iteratedDeriv_error hF (hpoint x hx) 1 (by norm_num)
    have hr := iteratedDeriv_modelPhase_abs_le hσ.le (hpoint x hx) 1
    have hb : |iteratedDeriv 2 F (x/P)| ≤ modelPhaseJetCoefficient σ 1+1 := by
      have he := abs_add_le (iteratedDeriv 2 F (x/P)-iteratedDeriv 1 (Expdb.modelPhase σ) (x/P))
        (iteratedDeriv 1 (Expdb.modelPhase σ) (x/P))
      rw [sub_add_cancel] at he
      linarith only [he,hh,hr,hδ1]
    rw [hd x hx 2,abs_div,abs_mul,abs_of_pos (by positivity : 0<T/P^2)]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact div_le_div_of_nonneg_right
      (by convert mul_le_mul_of_nonneg_left hb (show 0 ≤ T/P^2 by positivity) using 1; ring)
      (by norm_num)
/-- The dyadic joint derivative count for an actual original model phase.
All integer second-derivative levels and all original source labels are
counted; signed derivative data are derived from the existing model theorem. -/
theorem original_joint_dyadic_block_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N D a b R δ₁ δ₂ W : ℝ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ D → 0 < R → 0 ≤ δ₂ →
          N < a-R → b+R+2*D < 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          δ₂ ≤ lam*D*R/2 → δ₁+2*B*D*R^2 ≤ W/2 →
          δ₂ ≤ L/4 → δ₂ ≤ 1/2 →
          4*U*D*N^2/(σ*T) ≤ κ₀ → 0 < W → W ≤ 1/2 →
          let f := fun z => T*F (z/N)
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc D (2*D)) →
          (∀ p∈S, ∃ K : ℤ, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ δ₁) →
            (S.card:ℝ) ≤ (2*U*D)*(4*δ₂/(lam*D)+1)*
              (C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C,hC,hcount⟩ :=
    original_joint_level_block_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N D a b R δ₁ δ₂ W S hF hT hN hD hR hδ₂ hleft hright
    lam B L U hbuffer hwidth hδL hδhalf hshift hW hWhalf f hbox hsecond hfirst
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  have hDpos : 0 < D := by linarith
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 ≤ B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hsegment : Icc (a-R) (b+R+2*D) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  let level := fun p => if hp : p∈S then Classical.choose (hsecond p hp) else 0
  have hlevel (p : ℤ × ℕ) (hps : p∈S) :
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(level p:ℝ)| ≤ δ₂ := by
    simp only [level,dif_pos hps]
    exact Classical.choose_spec (hsecond p hps)
  have hlevels (p : ℤ × ℕ) (hps : p∈S) :
      0 < level p ∧ (level p:ℝ) ≤ 2*U*D := by
    have hprange := hbox p hps
    have hq : 1 ≤ (p.2:ℝ) := by linarith [hprange.2.1]
    have hsub : Icc (p.1:ℝ) ((p.1:ℝ)+(p.2:ℝ)) ⊆ Ioo N (2*N) := by
      intro t ht
      apply hsegment
      constructor <;> linarith [ht.1,ht.2,hprange.1.1,hprange.1.2,hprange.2.2]
    have hh := CubicNearCurveGeometry.cubic_second_level_positive f (level p) hq hL hδL hδhalf
      (fun t ht => (hreg t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (hlevel p hps)
    exact ⟨hh.1,hh.2.2.2.trans (by nlinarith [mul_le_mul_of_nonneg_left hprange.2.2 hU.le])⟩
  let J := S.image level
  have hJbound : (J.card:ℝ) ≤ 2*U*D := by
    by_cases hne : J.Nonempty
    · have hJ (K : ℤ) (hK : K∈J) : (1:ℝ) ≤ K ∧ (K:ℝ) ≤ 2*U*D := by
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
        have hh := hlevels p hp
        exact ⟨by exact_mod_cast (show (1:ℤ)≤level p by omega),hh.2⟩
      obtain ⟨K,hK⟩ := hne
      have hb := integer_card_le_interval_length_add_one J ((hJ K hK).1.trans (hJ K hK).2) hJ
      exact hb.trans_eq (by ring)
    · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.card_empty,Nat.cast_zero]
      positivity
  let X := C*(W*D+(T/N^2)^(k₀+ε)*D^(l₀+ε)*W^(-(k₀+ε))+N^2/T)
  let Z := 4*δ₂/(lam*D)+1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hcell (K : ℤ) (hK : K∈J) :
      ((S.filter (fun p => level p=K)).card:ℝ) ≤ Z*X := by
    obtain ⟨p,hps,hpK⟩ := Finset.mem_image.mp hK
    have hKpos : 0 < K := by rw [← hpK]; exact (hlevels p hps).1
    have hKbound : (K:ℝ) ≤ 2*U*D := by rw [← hpK]; exact (hlevels p hps).2
    have hκle : 2*(K:ℝ)*N^2/(σ*T) ≤ κ₀ := by
      calc
        _ ≤ 2*(2*U*D)*N^2/(σ*T) := by gcongr
        _ = 4*U*D*N^2/(σ*T) := by ring
        _ ≤ κ₀ := hshift
    have hsec : ∀ p∈S.filter (fun p => level p=K),
        |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ₂ := by
      intro p hp
      rw [← (Finset.mem_filter.mp hp).2]
      exact hlevel p (Finset.mem_filter.mp hp).1
    exact hcount F T N D a b R B lam δ₁ δ₂ W K (S.filter (fun p => level p=K))
      hF₀ hT hN hD hR hB hlam hδ₂ hleft hright hbuffer hwidth hKpos hκle hW hWhalf
      (fun t ht => hfour t (hsegment ht))
      (fun p hp => hbox p (Finset.mem_filter.mp hp).1) hsec
      (fun p hp => hfirst p (Finset.mem_filter.mp hp).1)
  have hmaps : Set.MapsTo level S J := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard : (S.card:ℝ)=∑ K∈J, ((S.filter (fun p => level p=K)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcard
    _ ≤ ∑ _K∈J, Z*X := Finset.sum_le_sum hcell
    _ = (J.card:ℝ)*(Z*X) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (2*U*D)*(Z*X) := mul_le_mul_of_nonneg_right hJbound (mul_nonneg hZ hX)
    _ = _ := by dsimp [Z,X]; ring

#print axioms original_joint_dyadic_block_count
/-- Short positive displacements need no oscillatory estimate: the
second-derivative level fibers alone give the sharp volume-scale count. -/
theorem cubic_short_displacement_count
    (f : ℝ → ℝ) (S : Finset (ℤ × ℕ)) {a b D B lam L U δ : ℝ}
    (hD : 1 ≤ D) (hlam : 0 < lam) (hL : 0 < L) (hU : 0 < U) (hδ : 0 ≤ δ)
    (hδL : δ ≤ L/4) (hδhalf : δ ≤ 1/2)
    (hf : ∀ t∈Icc a (b+D), ContDiffAt ℝ 4 f t)
    (hthree : ∀ t∈Icc a (b+D), L ≤ iteratedDeriv 3 f t ∧ iteratedDeriv 3 f t ≤ U)
    (hfour : ∀ t∈Icc a (b+D), -B ≤ iteratedDeriv 4 f t ∧ iteratedDeriv 4 f t ≤ -lam)
    (hbox : ∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc 1 D)
    (hsecond : ∀ p∈S, ∃ K : ℤ,
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ δ) :
    (S.card:ℝ) ≤ D*(4*U*δ/lam+U*D) := by
  classical
  let level := fun p => if hp : p∈S then Classical.choose (hsecond p hp) else 0
  have hlevel (p : ℤ × ℕ) (hps : p∈S) :
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(level p:ℝ)| ≤ δ := by
    simp only [level,dif_pos hps]
    exact Classical.choose_spec (hsecond p hps)
  have hlevels (p : ℤ × ℕ) (hps : p∈S) :
      0 < level p ∧ (level p:ℝ) ≤ U*(p.2:ℝ) := by
    have hb := hbox p hps
    have hsub : Icc (p.1:ℝ) ((p.1:ℝ)+(p.2:ℝ)) ⊆ Icc a (b+D) := by
      intro t ht
      constructor <;> linarith [hb.1.1,hb.1.2,hb.2.2,ht.1,ht.2]
    have hh := CubicNearCurveGeometry.cubic_second_level_positive f (level p) hb.2.1 hL hδL hδhalf
      (fun t ht => (hf t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (hlevel p hps)
    exact ⟨hh.1,hh.2.2.2⟩
  let J := S.image Prod.snd
  have hqbox (q : ℕ) (hq : q∈J) : 1 ≤ (q:ℝ) ∧ (q:ℝ) ≤ D := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hbox p hp).2
  have hJ : (J.card:ℝ) ≤ D := by
    let I := J.image (fun q : ℕ => (q:ℤ))
    have hcard : I.card=J.card := Finset.card_image_of_injective J Int.ofNat_injective
    have hh := integer_card_le_interval_length_add_one I hD (by
      intro z hz
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
      simpa only [Int.cast_natCast] using hqbox q hq)
    rw [hcard] at hh
    linarith
  have hfiber (q : ℕ) (hq : q∈J) :
      ((S.filter (fun p => p.2=q)).card:ℝ) ≤ 4*U*δ/lam+U*D := by
    let T := S.filter (fun p => p.2=q)
    let I := T.image level
    have hqpos : 0 < (q:ℝ) := zero_lt_one.trans_le (hqbox q hq).1
    have hI : (I.card:ℝ) ≤ U*(q:ℝ) := by
      by_cases hne : I.Nonempty
      · have hi (K : ℤ) (hK : K∈I) : (1:ℝ) ≤ K ∧ (K:ℝ) ≤ U*(q:ℝ) := by
          obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hK
          have hh := hlevels p (Finset.mem_filter.mp hp).1
          rw [(Finset.mem_filter.mp hp).2] at hh
          exact ⟨by exact_mod_cast (show (1:ℤ)≤level p by omega),hh.2⟩
        obtain ⟨K,hK⟩ := hne
        have hh := integer_card_le_interval_length_add_one I ((hi K hK).1.trans (hi K hK).2) hi
        exact hh.trans_eq (by ring)
      · have he : I=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp only [he,Finset.card_empty,Nat.cast_zero]
        positivity
    have hsub : Icc a (b+(q:ℝ)) ⊆ Icc a (b+D) := by
      intro t ht
      exact ⟨ht.1,ht.2.trans (by linarith [(hqbox q hq).2])⟩
    have hcell (K : ℤ) :
        ((T.filter (fun p => level p=K)).card:ℝ) ≤ 4*δ/(lam*(q:ℝ))+1 := by
      let Z := T.filter (fun p => level p=K)
      let Y := Z.image Prod.fst
      have hinj : Set.InjOn (Prod.fst : ℤ × ℕ → ℤ) Z := by
        intro p hp r hr he
        exact Prod.ext he ((Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.trans
          (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2.symm)
      have hcard : Y.card=Z.card := Finset.card_image_of_injOn hinj
      have hY : ∀ n∈Y, (n:ℝ)∈Icc a b := by
        intro n hn
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        exact (hbox p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1
      have hnear : ∀ n∈Y,
          |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ δ := by
        intro n hn
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
        have hh := hlevel p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        rwa [(Finset.mem_filter.mp hp).2,
          (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2] at hh
      have hh := CubicNearCurveGeometry.cubic_second_difference_fiber_card f Y hqpos hlam hδ
        (fun t ht => hf t (hsub ht)) (fun t ht => hfour t (hsub ht)) hY hnear
      rwa [hcard] at hh
    have hmaps : Set.MapsTo level T I := by
      intro p hp
      exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    have hcard : (T.card:ℝ)=∑ K∈I, ((T.filter (fun p => level p=K)).card:ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
    calc
      _ = _ := hcard
      _ ≤ ∑ _K∈I, (4*δ/(lam*(q:ℝ))+1) := Finset.sum_le_sum (fun K _ => hcell K)
      _ = (I.card:ℝ)*(4*δ/(lam*(q:ℝ))+1) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (U*(q:ℝ))*(4*δ/(lam*(q:ℝ))+1) := mul_le_mul_of_nonneg_right hI (by positivity)
      _ = 4*U*δ/lam+U*(q:ℝ) := by field_simp
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (hqbox q hq).2 hU.le]
  have hmaps : Set.MapsTo (Prod.snd : ℤ × ℕ → ℕ) S J := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hcard : (S.card:ℝ)=∑ q∈J, ((S.filter (fun p => p.2=q)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  calc
    _ = _ := hcard
    _ ≤ ∑ _q∈J, (4*U*δ/lam+U*D) := Finset.sum_le_sum hfiber
    _ = (J.card:ℝ)*(4*U*δ/lam+U*D) := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ (by positivity)

#print axioms cubic_short_displacement_count
/-- Independent Fourier width and exact-level buffer for the long
displacement blocks. These choices retain the low-frequency term. -/
theorem cubic_free_width_and_buffer
    {H Y lam B D : ℝ} (hH : 2 ≤ H) (hY : 2 ≤ Y)
    (hlam : 0 < lam) (hB : lam ≤ B) (hD : 2 ≤ D)
    (hthreshold : 4*B/(lam^2*H^4) ≤ D) :
    let R := 1/(2*lam*D*H^2)
    let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
    0 < R ∧ R ≤ H^2 ∧ 0 < W ∧ W ≤ 1/2 ∧
      1/(4*H^2)=lam*D*R/2 ∧
      1/(4*H)+2*B*D*R^2 ≤ W/2 ∧
      W*D ≤ D/(2*H)+B/(lam^2*H^4)+D/Y ∧
      ∀ p : ℝ, 0 ≤ p → W^(-p) ≤ Y^p := by
  intro R W
  have hHpos : 0 < H := by linarith
  have hYpos : 0 < Y := by linarith
  have hDpos : 0 < D := by linarith
  have hBpos : 0 < B := hlam.trans_le hB
  have hR : 0 < R := by dsimp [R]; positivity
  have hraw : 4*B ≤ D*(lam^2*H^4) :=
    (div_le_iff₀ (by positivity : 0 < lam^2*H^4)).mp hthreshold
  have hsize : 4 ≤ lam*D*H^4 := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hraw,hB]
  have hRsmall : R ≤ H^2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*lam*D*H^2)).mpr
    nlinarith only [hsize]
  have hW : 0 < W := (one_div_pos.mpr hYpos).trans_le (le_max_right _ _)
  have hquarter : 1/(2*H) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2*H) (by norm_num : (0:ℝ)<4)).mpr
    linarith
  have hother : B/(lam^2*D*H^4) ≤ 1/4 := by
    apply (div_le_div_iff₀ (by positivity : 0 < lam^2*D*H^4) (by norm_num : (0:ℝ)<4)).mpr
    nlinarith only [hraw]
  have hWhalf : W ≤ 1/2 := by
    apply max_le
    · linarith
    · exact one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hY
  have hbuffer : 1/(4*H^2)=lam*D*R/2 := by dsimp [R]; field_simp; norm_num
  have hwidth : 1/(4*H)+2*B*D*R^2 ≤ W/2 := by
    have he : 1/(4*H)+2*B*D*R^2=(1/(2*H)+B/(lam^2*D*H^4))/2 := by
      dsimp [R]
      field_simp
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by norm_num)
  have hWD : W*D ≤ D/(2*H)+B/(lam^2*H^4)+D/Y := by
    have hsum : W ≤ (1/(2*H)+B/(lam^2*D*H^4))+1/Y := by
      apply max_le
      · linarith [one_div_pos.mpr hYpos]
      · have hpos : 0 ≤ 1/(2*H)+B/(lam^2*D*H^4) := by positivity
        linarith
    calc
      _ ≤ ((1/(2*H)+B/(lam^2*D*H^4))+1/Y)*D := mul_le_mul_of_nonneg_right hsum hDpos.le
      _ = _ := by field_simp
  refine ⟨hR,hRsmall,hW,hWhalf,hbuffer,hwidth,hWD,?_⟩
  intro p hp
  have hh := Real.rpow_le_rpow_of_nonpos (one_div_pos.mpr hYpos)
    (show 1/Y ≤ W from le_max_right _ _) (neg_nonpos.mpr hp)
  have he : (1/Y)^(-p)=Y^p := by
    rw [one_div,Real.inv_rpow hYpos.le,Real.rpow_neg hYpos.le,inv_inv]
  exact hh.trans_eq he

#print axioms cubic_free_width_and_buffer
private theorem cubic_long_block_majorant
    {H Y lam B U D Qcut Freq Tail C p q : ℝ}
    (hH : 2 ≤ H) (hY : 2 ≤ Y) (hlam : 0 < lam) (hB : lam ≤ B)
    (hD : 2 ≤ D) (hthreshold : 4*B/(lam^2*H^4) ≤ D)
    (hU : 0 ≤ U) (hDQ : D ≤ Qcut) (hthin : lam*Qcut*H^2 ≤ 1)
    (hFreq : 0 ≤ Freq) (hTail : 0 ≤ Tail) (hC : 1 ≤ C) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
    (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1)*
      (C*(W*D+Freq*D^q*W^(-p)+Tail)) ≤
      4*C*(U/(lam*H^2))*
        (1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+Freq*Qcut^q*Y^p+Tail) := by
  intro W
  have hHpos : 0 < H := by linarith only [hH]
  have hYpos : 0 < Y := by linarith only [hY]
  have hDpos : 0 < D := by linarith only [hD]
  have hQpos : 0 < Qcut := hDpos.trans_le hDQ
  have hBpos : 0 < B := hlam.trans_le hB
  let V := U/(lam*H^2)
  let X := 1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+Freq*Qcut^q*Y^p+Tail
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  obtain ⟨_hR,_hRsmall,hW,_hWhalf,_hbuf,_hwidth,hWD,hWp⟩ :=
    cubic_free_width_and_buffer hH hY hlam hB hD hthreshold
  have hUQ : U*Qcut ≤ V := by
    apply (le_div_iff₀ (by positivity : 0 < lam*H^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hthin hU]
  have hfactorEq : (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1)=2*V+2*U*D := by
    dsimp [V]
    field_simp
  have hfactor : (2*U*D)*(4*(1/(4*H^2))/(lam*D)+1) ≤ 4*V := by
    rw [hfactorEq]
    have hh := (mul_le_mul_of_nonneg_left hDQ hU).trans hUQ
    linarith only [hh]
  have hlen : D^q ≤ Qcut^q := Real.rpow_le_rpow hDpos.le hDQ hq
  have hosc : Freq*D^q*W^(-p) ≤ Freq*Qcut^q*Y^p := by
    gcongr
    exact hWp p hp
  have hvolume : W*D ≤ Qcut/H+B/(lam^2*H^4)+Qcut/Y := by
    calc
      _ ≤ D/(2*H)+B/(lam^2*H^4)+D/Y := hWD
      _ ≤ Qcut/(2*H)+B/(lam^2*H^4)+Qcut/Y := by gcongr
      _ ≤ _ := by
        have hh : Qcut/(2*H) ≤ Qcut/H :=
          div_le_div_of_nonneg_left hQpos.le hHpos (by linarith only [hHpos])
        linarith only [hh]
  have hinner : W*D+Freq*D^q*W^(-p)+Tail ≤ X := by
    dsimp [X]
    linarith only [hvolume,hosc]
  calc
    _ ≤ (4*V)*(C*X) := by gcongr
    _ = _ := by change (4*V)*(C*X)=4*C*V*X; ring

/-- Full positive-displacement joint count, including the short branch and
every dyadic block. The only logarithmic cost is the explicit cutoff
index M; no source cardinality or exponential-sum estimate is assumed. -/
theorem original_full_joint_derivative_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N H Y a b Qcut : ℝ) (M : ℕ) (S : Finset (ℤ × ℕ)),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y → 1 ≤ Qcut → Qcut ≤ (2:ℝ)^M →
          N < a-H^2 → b+H^2+2*Qcut < 2*N →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          lam*Qcut*H^2 ≤ 1 → 1/(4*H^2) ≤ L/4 →
          4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          let f := fun z => T*F (z/N)
          (∀ p∈S, (p.1:ℝ)∈Icc a b ∧ (p.2:ℝ)∈Icc 1 Qcut) →
          (∀ p∈S, ∃ K : ℤ, |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ 1/(4*H^2)) →
          (∀ p∈S, ∃ e : ℤ, |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-
            iteratedDeriv 1 f p.1-(e:ℝ)| ≤ 1/(4*H)) →
            (S.card:ℝ) ≤ C*((M:ℝ)+2)*(U/(lam*H^2))*
              (1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+
                (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C₀,hC₀,hcount⟩ :=
    original_joint_dyadic_block_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  let C := 8+4*C₀
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC8 : 8 ≤ C := by dsimp [C]; linarith
  have hC4 : 4*C₀ ≤ C := by dsimp [C]; linarith
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N H Y a b Qcut M S hF hT hN hH hY hQcut hQpow hleft hright
    lam B L U hthin hδL hshift f hbox hsecond hfirst
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  have hHpos : 0 < H := by linarith
  have hYpos : 0 < Y := by linarith
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hBpos : 0 < B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hB : lam ≤ B := by
    have hh := modelPhase_signed_referenceJet_bounds hσ (by norm_num : (3/2:ℝ)∈Ioo 1 2) 3
    have hc : modelPhaseJetLower σ 3 ≤ modelPhaseJetCoefficient σ 3+1 := by
      linarith only [hh.1,hh.2,modelPhaseJetLower_pos hσ 3]
    dsimp [lam,B]
    gcongr
  have hδhalf : 1/(4*H^2) ≤ 1/2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4*H^2) (by norm_num : (0:ℝ)<2)).mpr
    nlinarith only [hH]
  have hp₀ : 0 ≤ k₀+ε := by linarith [hpair.1.1]
  have hq₀ : 0 ≤ l₀+ε := by linarith [hpair.1.2.2.1]
  let V := U/(lam*H^2)
  let X := 1+B/(lam^2*H^4)+Qcut/H+Qcut/Y+
    (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T
  let A := C*V*X
  let D₀ := 2+4*B/(lam^2*H^4)
  have hV : 0 < V := by dsimp [V]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD₀ : 2 ≤ D₀ := by
    have hh : 0 ≤ 4*B/(lam^2*H^4) := by positivity
    dsimp [D₀]
    linarith
  have hUQ : U*Qcut ≤ V := by
    apply (le_div_iff₀ (by positivity : 0 < lam*H^2)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hthin hU.le]
  have hsegment : Icc a (b+Qcut) ⊆ Ioo N (2*N) := by
    intro t ht
    constructor <;> linarith only [ht.1,ht.2,sq_nonneg H,hleft,hright,hQpos]
  let short := S.filter (fun p => (p.2:ℝ)<D₀)
  have hshort : (short.card:ℝ) ≤ A := by
    let d := min D₀ Qcut
    have hd : 1 ≤ d := le_min (by linarith) hQcut
    have hdQ : d ≤ Qcut := min_le_right _ _
    have hd₀ : d ≤ D₀ := min_le_left _ _
    have hsub : Icc a (b+d) ⊆ Ioo N (2*N) := by
      intro t ht
      exact hsegment ⟨ht.1,ht.2.trans (by linarith)⟩
    have hh := cubic_short_displacement_count f short hd hlam hL hU (by positivity)
      hδL hδhalf
      (fun t ht => (hreg t (hsub ht)).of_le (by norm_num))
      (fun t ht => hthree t (hsub ht)) (fun t ht => hfour t (hsub ht))
      (by
        intro p hp
        have hb := hbox p (Finset.mem_filter.mp hp).1
        exact ⟨hb.1,hb.2.1,le_min (Finset.mem_filter.mp hp).2.le hb.2.2⟩)
      (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
    have he : 4*U*(1/(4*H^2))/lam=V := by dsimp [V]; field_simp
    rw [he] at hh
    have hUd : U*d ≤ V := (mul_le_mul_of_nonneg_left hdQ hU.le).trans hUQ
    have hsmall : (short.card:ℝ) ≤ 2*D₀*V := by
      calc
        _ ≤ d*(V+U*d) := hh
        _ ≤ D₀*(V+V) := by gcongr
        _ = _ := by ring
    have hDX : 2*D₀ ≤ 8*X := by
      have hterms : 0 ≤ Qcut/H+Qcut/Y+
          (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T := by positivity
      dsimp [D₀,X]
      ring_nf at hterms ⊢
      linarith only [hterms]
    calc
      _ ≤ 2*D₀*V := hsmall
      _ ≤ (8*X)*V := mul_le_mul_of_nonneg_right hDX hV.le
      _ ≤ (C*X)*V := by gcongr
      _ = A := by dsimp [A]; ring
  let scale := fun j : ℕ => D₀*(2:ℝ)^j
  let block := fun j : ℕ => S.filter (fun p => scale j ≤ (p.2:ℝ) ∧ (p.2:ℝ)<2*scale j)
  have hblock (j : ℕ) : ((block j).card:ℝ) ≤ A := by
    by_cases hne : (block j).Nonempty
    · obtain ⟨p,hps⟩ := hne
      let D := scale j
      have hDlow : D₀ ≤ D := by
        have hh : (1:ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
        dsimp [D,scale]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
          (show 0 ≤ D₀ by linarith only [hD₀])
      have hD : 2 ≤ D := hD₀.trans hDlow
      have hDpos : 0 < D := by linarith
      have hDQ : D ≤ Qcut := (Finset.mem_filter.mp hps).2.1.trans (hbox p (Finset.mem_filter.mp hps).1).2.2
      have hthreshold : 4*B/(lam^2*H^4) ≤ D := by
        dsimp [D₀] at hDlow
        linarith
      let R := 1/(2*lam*D*H^2)
      let W := max (1/(2*H)+B/(lam^2*D*H^4)) (1/Y)
      obtain ⟨hR,hRsmall,hW,hWhalf,hbuf,hwidth,_hWD,_hWp⟩ :=
        cubic_free_width_and_buffer hH hY hlam hB hD hthreshold
      have hshiftD : 4*U*D*N^2/(σ*T) ≤ κ₀ := by
        calc
          _ ≤ 4*U*Qcut*N^2/(σ*T) := by gcongr
          _ ≤ κ₀ := hshift
      have hh := hcount F T N D a b R (1/(4*H)) (1/(4*H^2)) W (block j)
        hF₀ hT hN hD hR (by positivity)
        (by linarith only [hleft,hRsmall])
        (by linarith only [hright,hRsmall,hDQ])
        hbuf.le hwidth hδL hδhalf hshiftD hW hWhalf
        (by
          intro p hp
          have hb := hbox p (Finset.mem_filter.mp hp).1
          exact ⟨hb.1,(Finset.mem_filter.mp hp).2.1,(Finset.mem_filter.mp hp).2.2.le⟩)
        (fun p hp => hsecond p (Finset.mem_filter.mp hp).1)
        (fun p hp => hfirst p (Finset.mem_filter.mp hp).1)
      have hmajor := cubic_long_block_majorant hH hY hlam hB hD hthreshold
        hU.le hDQ hthin (by positivity : 0 ≤ (T/N^2)^(k₀+ε))
        (by positivity : 0 ≤ N^2/T) hC₀ hp₀ hq₀
      have hbound : ((block j).card:ℝ) ≤ 4*C₀*V*X := hh.trans hmajor
      calc
        _ ≤ 4*C₀*V*X := hbound
        _ ≤ C*V*X := by gcongr
    · have he : block j=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.card_empty,Nat.cast_zero]
      exact hA
  have hcover : S ⊆ short ∪ (Finset.range (M+1)).biUnion block := by
    intro p hp
    by_cases hs : (p.2:ℝ)<D₀
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,hs⟩)
    have hterminal : (p.2:ℝ)<D₀*(2:ℝ)^(M+1) := by
      have hh := (hbox p hp).2.2.trans hQpow
      have hpowpos : (0:ℝ)<2^M := by positivity
      rw [pow_succ]
      nlinarith only [hh,hpowpos,hD₀]
    obtain ⟨j,hj,hlo,hhi⟩ := exists_bourgain_dyadic_amplitude (le_of_not_gt hs) hterminal
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_filter.mpr ⟨hp,hlo,hhi⟩⟩)
  have hcard : (S.card:ℝ) ≤ (short.card:ℝ)+∑ j∈Finset.range (M+1), ((block j).card:ℝ) := by
    have hh := (Finset.card_le_card hcover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))
    exact_mod_cast hh
  calc
    _ ≤ (short.card:ℝ)+∑ j∈Finset.range (M+1), ((block j).card:ℝ) := hcard
    _ ≤ A+∑ _j∈Finset.range (M+1), A := add_le_add hshort (Finset.sum_le_sum (fun j _ => hblock j))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
      dsimp only [A]
      ring

#print axioms original_full_joint_derivative_count
/-- The actual derivative-pair set retains the diagonal and both orders.
Bounding its positive-displacement half therefore suffices. -/
theorem cubicDerivativePairs_card_le_positive
    (f : ℝ → ℝ) (M H : ℕ) :
    (SquareProductCount.CubicSource.cubicDerivativePairs f M H).card ≤ M+
      2*((SquareProductCount.CubicSource.cubicDerivativePairs f M H).filter
        (fun p => p.1<p.2)).card := by
  classical
  let S := SquareProductCount.CubicSource.cubicDerivativePairs f M H
  let diag := S.filter (fun p => p.1=p.2)
  let up := S.filter (fun p => p.1<p.2)
  let down := S.filter (fun p => p.2<p.1)
  have hswap (p : ℕ × ℕ) (hp : p∈S) : p.swap∈S := by
    unfold S SquareProductCount.CubicSource.cubicDerivativePairs
      SquareProductCount.CubicSource.cubicSamplePairs at hp ⊢
    obtain ⟨hbox,hnear⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hbox).2,(Finset.mem_product.mp hbox).1⟩,?_⟩
    intro d
    simpa only [Prod.swap,abs_sub_comm] using hnear d
  have hd : diag.card ≤ M := by
    have hinj : Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) diag := by
      intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.symm.trans
        (he.trans (Finset.mem_filter.mp hq).2))
    have hsub : diag.image Prod.fst ⊆ Finset.range M := by
      intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      have hm := (CubicNearCurveGeometry.cubicDerivativePairs_integer_resonances f
        (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_range.mpr hm
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injOn hinj,Finset.card_range] at hh
  have hdown : down.card ≤ up.card := by
    have hsub : down.image Prod.swap ⊆ up := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨hswap q (Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective down Prod.swap_injective] at hh
  have hcover : S ⊆ (diag∪up)∪down := by
    intro p hp
    rcases lt_trichotomy p.1 p.2 with hlt|heq|hgt
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hlt⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,heq⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,hgt⟩)
  have hh := (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  change S.card ≤ M+2*up.card
  omega

/-- Reindex an actual shifted source pair by its absolute integer source
point and positive displacement. The two integer resonances are preserved. -/
theorem cubic_shifted_positive_pair_resonances
    (f : ℝ → ℝ) (A : ℤ) {M H : ℕ} {p : ℕ × ℕ}
    (hp : p∈SquareProductCount.CubicSource.cubicDerivativePairs
      (fun x => f ((A:ℝ)+x)) M H) (hlt : p.1<p.2) :
    let n : ℤ := A+(p.1:ℤ)+1
    let q : ℕ := p.2-p.1
    (A:ℝ)+1 ≤ n ∧ (n:ℝ) ≤ (A:ℝ)+M ∧ 1 ≤ q ∧
      ∃ e K : ℤ,
        |iteratedDeriv 1 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 1 f n-(e:ℝ)| ≤ 1/(4*(H:ℝ)) ∧
        |(iteratedDeriv 2 f ((n:ℝ)+(q:ℝ))-iteratedDeriv 2 f n)/2-(K:ℝ)| ≤ 1/(4*(H:ℝ)^2) := by
  intro n q
  obtain ⟨hm₀,_hm₁,e,K,hfirst,hsecond,_hthird⟩ :=
    CubicNearCurveGeometry.cubicDerivativePairs_integer_resonances
      (fun x => f ((A:ℝ)+x)) hp
  have hder (j : ℕ) (x : ℝ) :
      iteratedDeriv j (fun y => f ((A:ℝ)+y)) x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hn : (n:ℝ)=(A:ℝ)+(p.1:ℝ)+1 := by dsimp [n]; push_cast; ring
  have hq : (q:ℝ)=(p.2:ℝ)-(p.1:ℝ) := Nat.cast_sub hlt.le
  have he₀ : (A:ℝ)+((p.1:ℝ)+1)=(n:ℝ) := by rw [hn]; ring
  have he₁ : (A:ℝ)+((p.2:ℝ)+1)=(n:ℝ)+(q:ℝ) := by rw [hn,hq]; ring
  rw [hder,hder,he₀,he₁] at hfirst hsecond
  refine ⟨?_,?_,by dsimp [q]; omega,e,K,hfirst,hsecond⟩
  · rw [hn]
    have hh : (0:ℝ) ≤ p.1 := Nat.cast_nonneg _
    linarith only [hh]
  · rw [hn]
    have hh : (p.1:ℝ)+1 ≤ M := by exact_mod_cast (show p.1+1 ≤ M by omega)
    linarith only [hh]

#print axioms cubicDerivativePairs_card_le_positive
#print axioms cubic_shifted_positive_pair_resonances
/-- The sharp joint count now consumes the literal derivative-pair set
returned by the original C4 source reduction. Integer translation,
both pair orders, the diagonal and all source multiplicities are retained. -/
theorem original_cubicDerivativePairs_count
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          let g := fun x => T*F (((A:ℝ)+x)/N)
          ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
            M+2*(C*((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
              (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
                (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)) := by
  classical
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C,hC,hcount⟩ :=
    original_full_joint_derivative_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift g
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,_hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  let f := fun x => T*F (x/N)
  let pairs := SquareProductCount.CubicSource.cubicDerivativePairs g M H
  let up := pairs.filter (fun p => p.1<p.2)
  let label := fun p : ℕ × ℕ => (A+(p.1:ℤ)+1,p.2-p.1)
  let S := up.image label
  have hHr : (2:ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0:ℝ) < H := by linarith only [hHr]
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hder (j : ℕ) (x : ℝ) : iteratedDeriv j g x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hphysical (x : ℝ) (hx : x∈Icc 1 (M:ℝ)) : (A:ℝ)+x∈Ioo N (2*N) := by
    constructor <;> linarith only [hx.1,hx.2,hleft,hright,sq_nonneg (H:ℝ),hQpos]
  have hdisp (p : ℕ × ℕ) (hps : p∈up) : ((p.2-p.1:ℕ):ℝ) ≤ Qcut := by
    have hpairs := (Finset.mem_filter.mp hps).1
    have hlt := (Finset.mem_filter.mp hps).2
    obtain ⟨hm₀,hm₁,_he,_hK,_hfirst,_hsecond,_hthird⟩ :=
      CubicNearCurveGeometry.cubicDerivativePairs_integer_resonances g hpairs
    have hsub (x : ℝ) (hx : x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1)) : x∈Icc 1 (M:ℝ) := by
      have hm : (p.2:ℝ)+1 ≤ M := by exact_mod_cast (show p.2+1≤M by omega)
      have hp0 : (0:ℝ) ≤ p.1 := Nat.cast_nonneg _
      constructor <;> linarith only [hx.1,hx.2,hm,hp0]
    have hgc : ∀ x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), ContDiffAt ℝ 4 g x := by
      intro x hx
      exact ((hreg ((A:ℝ)+x) (hphysical x (hsub x hx))).comp x
        (show ContDiffAt ℝ 5 (fun y : ℝ => (A:ℝ)+y) x by fun_prop)).of_le (by norm_num)
    have hgf : ∀ x∈Icc ((p.1:ℝ)+1) ((p.2:ℝ)+1), iteratedDeriv 4 g x ≤ -lam := by
      intro x hx
      rw [hder]
      exact (hfour ((A:ℝ)+x) (hphysical x (hsub x hx))).2
    rw [Nat.cast_sub hlt.le]
    exact CubicNearCurveGeometry.cubicDerivativePairs_displacement g (by omega) hlam hpairs hlt hgc hgf
  have hinj : Set.InjOn label up := by
    intro p hp q hq he
    have hfst := congrArg Prod.fst he
    have hsnd := congrArg Prod.snd he
    dsimp only [label] at hfst hsnd
    have hp := (Finset.mem_filter.mp hp).2
    have hq := (Finset.mem_filter.mp hq).2
    have he₁ : p.1=q.1 := by omega
    exact Prod.ext he₁ (by omega)
  have hcard : S.card=up.card := Finset.card_image_of_injOn hinj
  have hboxS : ∀ p∈S, (p.1:ℝ)∈Icc ((A:ℝ)+1) ((A:ℝ)+M) ∧
      (p.2:ℝ)∈Icc 1 Qcut := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hh := cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2
    exact ⟨⟨hh.1,hh.2.1⟩,by exact_mod_cast hh.2.2.1,hdisp q hq⟩
  have hsecondS : ∀ p∈S, ∃ K : ℤ,
      |(iteratedDeriv 2 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 2 f p.1)/2-(K:ℝ)| ≤ 1/(4*(H:ℝ)^2) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e,K,_hfirst,hsecond⟩ := (cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2).2.2.2
    exact ⟨K,hsecond⟩
  have hfirstS : ∀ p∈S, ∃ e : ℤ,
      |iteratedDeriv 1 f ((p.1:ℝ)+(p.2:ℝ))-iteratedDeriv 1 f p.1-(e:ℝ)| ≤ 1/(4*(H:ℝ)) := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨e,K,hfirst,_hsecond⟩ := (cubic_shifted_positive_pair_resonances f A
      (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2).2.2.2
    exact ⟨e,hfirst⟩
  have hthin : lam*Qcut*(H:ℝ)^2 ≤ 1 := by
    have he : lam*Qcut*(H:ℝ)^2=3/(2*(H:ℝ)) := by dsimp [Qcut]; field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2*(H:ℝ))).mpr
    linarith only [hHr]
  have hh := hcount F T N (H:ℝ) Y ((A:ℝ)+1) ((A:ℝ)+M) Qcut J S
    hF₀ hT hN hHr hY hQcut hQpow hleft hright hthin hδL hshift hboxS hsecondS hfirstS
  rw [hcard] at hh
  have hsplit : (pairs.card:ℝ) ≤ (M:ℝ)+2*(up.card:ℝ) := by
    exact_mod_cast cubicDerivativePairs_card_le_positive g M H
  exact hsplit.trans (by gcongr)

#print axioms original_cubicDerivativePairs_count
/-- Original-model eighth-power estimate from the literal C4 reduction
and the proved joint derivative count. Every C4/third-derivative hypothesis
is derived from the same original model phase. -/
theorem exists_original_cubic_eighth_estimate
    {σ k₀ l₀ ε : ℝ} (hσ : 0 < σ)
    (hpair : ExponentPair k₀ l₀) (hε : 0 < ε) (hp : k₀+ε < 1) :
    ∃ δ κ₀ : ℝ, 0 < δ ∧ 0 < κ₀ ∧
      ∃ Q : ℕ, 3 ≤ Q ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (F : ℝ → ℝ) (T N Y : ℝ) (A : ℤ) (M H J : ℕ),
          IsApproximateModelPhaseFunction F σ Q δ →
          0 < T → 0 < N → 2 ≤ H → 2 ≤ Y →
          let lam := modelPhaseJetLower σ 3*T/N^4
          let B := (modelPhaseJetCoefficient σ 3+1)*T/N^4
          let L := modelPhaseJetLower σ 2*T/N^3
          let U := (modelPhaseJetCoefficient σ 2+1)*T/N^3
          let Qcut := 3/(2*lam*(H:ℝ)^3)
          1 ≤ Qcut → Qcut ≤ (2:ℝ)^J →
          N < (A:ℝ)+1-(H:ℝ)^2 → (A:ℝ)+M+(H:ℝ)^2+2*Qcut < 2*N →
          1/(4*(H:ℝ)^2) ≤ L/4 → 4*U*Qcut*N^2/(σ*T) ≤ κ₀ →
          B*((H:ℝ)+1)^4 ≤ 1 →
          let E := ((J:ℝ)+2)*(U/(lam*(H:ℝ)^2))*
            (1+B/(lam^2*(H:ℝ)^4)+Qcut/(H:ℝ)+Qcut/Y+
              (T/N^2)^(k₀+ε)*Qcut^(l₀+ε)*Y^(k₀+ε)+N^2/T)
          ‖∑ m∈Finset.range M,
            fordAdditiveCharacter (T*F (((A:ℝ)+(m:ℝ)+1)/N))‖^8 ≤
              C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
  obtain ⟨δ₀,κ₀,hδ₀,hκ₀,Q₀,hQ₀,C₀,hC₀,hcount⟩ :=
    original_cubicDerivativePairs_count hσ hpair hε hp
  obtain ⟨δd,hδd,hdata⟩ := model_displacement_derivative_data hσ
  obtain ⟨C₁,hC₁,hsource⟩ := SquareProductCount.CubicSource.exists_C4_source_eighth_reduction hε
  let δ := min δ₀ δd
  let Q := max Q₀ 3
  let C := C₁*(1+2*C₀)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨δ,κ₀,lt_min hδ₀ hδd,hκ₀,Q,le_max_right _ _,C,hC,?_⟩
  intro F T N Y A M H J hF hT hN hH hY lam B L U Qcut hQcut hQpow hleft hright hδL hshift hTaylor E
  have hF₀ := approximateModelPhase_mono hF (le_max_left _ _) (min_le_left _ _)
  have hFd := approximateModelPhase_mono hF (le_max_right _ _) (min_le_right _ _)
  obtain ⟨hreg,hthree,hfour,_hsecondabs⟩ := hdata F T N hT hN hFd
  let f := fun x => T*F (x/N)
  let g := fun x => f ((A:ℝ)+x)
  have hHr : (2:ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0:ℝ) < H := by linarith only [hHr]
  have hlam : 0 < lam := by dsimp [lam]; positivity [modelPhaseJetLower_pos hσ 3]
  have hL : 0 < L := by dsimp [L]; positivity [modelPhaseJetLower_pos hσ 2]
  have hU : 0 < U := by dsimp [U]; positivity [modelPhaseJetCoefficient_pos hσ 2]
  have hB : 0 < B := by dsimp [B]; positivity [modelPhaseJetCoefficient_pos hσ 3]
  have hQpos : 0 < Qcut := zero_lt_one.trans_le hQcut
  have hder (j : ℕ) (x : ℝ) : iteratedDeriv j g x=iteratedDeriv j f ((A:ℝ)+x) :=
    congrFun (iteratedDeriv_comp_const_add j f (A:ℝ)) x
  have hHbuf : (H:ℝ)+1 ≤ (H:ℝ)^2 := by nlinarith only [hHr]
  have hpoint (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : (A:ℝ)+y∈Ioo N (2*N) := by
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg _
    have hmM : (m:ℝ)+1 ≤ M := by
      exact_mod_cast (show m+1≤M by have := Finset.mem_range.mp hm; omega)
    constructor <;> linarith only [hy.1,hy.2,hm0,hmM,hHbuf,hleft,hright,hQpos]
  have hg (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : ContDiffAt ℝ 4 g y := by
    exact ((hreg ((A:ℝ)+y) (hpoint m hm y hy)).comp y
      (show ContDiffAt ℝ 5 (fun z : ℝ => (A:ℝ)+z) y by fun_prop)).of_le (by norm_num)
  have hfour' (m : ℕ) (hm : m∈Finset.range M) (y : ℝ)
      (hy : y∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2)) : |iteratedDeriv 4 g y| ≤ B := by
    rw [hder]
    have hh := hfour ((A:ℝ)+y) (hpoint m hm y hy)
    apply abs_le.mpr
    exact ⟨hh.1,by linarith only [hh.2,hlam,hB]⟩
  have hthree' (m : ℕ) (hm : m∈Finset.range M) :
      iteratedDeriv 3 g ((m:ℝ)+1)/6∈Icc (0:ℝ) (0+U/6) := by
    rw [hder]
    have hcenter : (m:ℝ)+1∈Icc ((m:ℝ)-H) ((m:ℝ)+H+2) := by
      constructor <;> linarith only [hHpos]
    have hh := hthree ((A:ℝ)+((m:ℝ)+1)) (hpoint m hm ((m:ℝ)+1) hcenter)
    constructor <;> linarith only [hh.1,hh.2,hL]
  have hnear := hcount F T N Y A M H J hF₀ hT hN hH hY hQcut hQpow hleft hright hδL hshift
  have hsum := hsource g M H (by omega) B 0 (U/6) hB.le (by positivity)
    hTaylor hg hfour' hthree'
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hnear' : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
      (1+2*C₀)*((M:ℝ)+E) := by
    have hh : ((SquareProductCount.CubicSource.cubicDerivativePairs g M H).card:ℝ) ≤
        (M:ℝ)+2*C₀*E := by
      convert hnear using 1
      dsimp [E]
      ring
    have hm : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hx : 0 ≤ 2*C₀*(M:ℝ) := by positivity
    nlinarith only [hh,hE,hx]
  have hUwidth : 1+(U/6)*(H:ℝ)^2 ≤ 1+U*(H:ℝ)^2 := by
    nlinarith only [mul_nonneg hU.le (sq_nonneg (H:ℝ))]
  have hb : ‖∑ m∈Finset.range M, fordAdditiveCharacter (g ((m:ℝ)+1))‖^8 ≤
      C*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by
    calc
      _ ≤ C₁*((M:ℝ)^6*(SquareProductCount.CubicSource.cubicDerivativePairs g M H).card*
          (1+(U/6)*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := hsum
      _ ≤ C₁*((M:ℝ)^6*((1+2*C₀)*((M:ℝ)+E))*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8) := by gcongr
      _ ≤ C₁*((1+2*C₀)*((M:ℝ)^6*((M:ℝ)+E)*(1+U*(H:ℝ)^2)*(H:ℝ)^ε+(H:ℝ)^8)) := by
        apply mul_le_mul_of_nonneg_left _ hC₁.le
        nlinarith only [mul_nonneg (show 0 ≤ 2*C₀ by positivity) (pow_nonneg hHpos.le 8)]
      _ = _ := by dsimp [C]; ring
  simpa only [g,f,add_assoc] using hb

#print axioms exists_original_cubic_eighth_estimate





-- Distinct Fourier and Taylor scales; both the buffer equality and
-- the closed half-width threshold are tested exactly.
example :
    let R : ℝ := 1/(2*(1/16)*2*4^2)
    let W : ℝ := max (1/(2*4)+(1/16)/((1/16)^2*2*4^4)) (1/3)
    R=1/4 ∧ W=1/3 ∧ 1/(4*4^2)=(1/16)*2*R/2 := by norm_num

example :
    let W : ℝ := max (1/(2*2)+1/(1^2*2*2^4)) (1/2)
    W=1/2 := by norm_num













end TaoTrudgianYang2025.DisplacementDualPrototype
