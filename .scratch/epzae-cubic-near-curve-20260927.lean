import TaoTrudgianYang2025.SquareProductCount

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
