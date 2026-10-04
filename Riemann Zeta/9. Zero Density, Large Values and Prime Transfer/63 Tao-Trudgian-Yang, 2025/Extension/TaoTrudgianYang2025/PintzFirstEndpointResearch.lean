import TaoTrudgianYang2025.PintzEndpointResearch
import TaoTrudgianYang2025.ParabolaBilinearLocalization
import GafniTao.HeathBrownRefinedCountFinal
import Mathlib.Algebra.Order.Chebyshev

/-!
Original research for the unchanged first Pintz endpoint.
The actual mixed-cell counts, original-difference multiplicities, joint critical
moment, Taylor/Abel source entry and Gram absorption prove the frozen 16/21
endpoint. This is an owner-authorized research strengthening, not a claim that
Pintz's strict source cell includes its boundary. Every source contract is preserved.
-/

open Set Finset MeasureTheory
open scoped BigOperators ENNReal

namespace TaoTrudgianYang2025.PintzFirstEndpointResearch

noncomputable section

def reciprocalCubic (A x : ℝ) : ℝ := A*x^(-(1:ℝ)/3)

def reciprocalCubicNearIntegers (A Q : ℝ) (N : ℕ) (η : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun n =>
    GafniTao.heathBrownDistanceToInteger (reciprocalCubic A (Q+n)) ≤ η)

theorem reciprocalCubic_derivative (A : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (reciprocalCubic A) (-(A/3)*x^(-(4:ℝ)/3)) x := by
  convert (Real.hasDerivAt_rpow_const
    (p := -(1:ℝ)/3) (Or.inl hx.ne')).const_mul A using 1
  norm_num
  ring

theorem reciprocalCubic_second_derivative (A : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(A/3)*x^(-(4:ℝ)/3))
      ((4*A/9)*x^(-(7:ℝ)/3)) x := by
  convert (Real.hasDerivAt_rpow_const
    (p := -(4:ℝ)/3) (Or.inl hx.ne')).const_mul (-(A/3)) using 1
  norm_num
  ring

theorem reciprocalCubic_curvature_bounds {A Q x : ℝ}
    (hA : 0 < A) (hQ : 0 < Q) (hx : x ∈ Icc Q (2*Q)) :
    let μ := (4*A/9)*(2*Q)^(-(7:ℝ)/3)
    μ ≤ (4*A/9)*x^(-(7:ℝ)/3) ∧ (4*A/9)*x^(-(7:ℝ)/3) ≤ 8*μ := by
  intro μ
  have hxpos : 0 < x := hQ.trans_le hx.1
  have hpow : Q^(-(7:ℝ)/3) ≤ 8*(2*Q)^(-(7:ℝ)/3) := by
    have he : Q^(-(7:ℝ)/3) =
        (2:ℝ)^((7:ℝ)/3)*(2*Q)^(-(7:ℝ)/3) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hQ.le,
        ←mul_assoc,←Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      (2:ℝ)^((7:ℝ)/3) ≤ (2:ℝ)^(3:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 8 := by norm_num
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hxpos hx.2 (by norm_num)) (by positivity)
  · have hp := Real.rpow_le_rpow_of_nonpos hQ hx.1 (by norm_num : -(7:ℝ)/3 ≤ 0)
    have hh := mul_le_mul_of_nonneg_left (hp.trans hpow)
      (by positivity : 0 ≤ 4*A/9)
    dsimp only [μ]
    nlinarith only [hh]

/-- The integer labels near the actual reciprocal-cubic stationary curve
obey a curvature-saving count on every positive dyadic interval. -/
theorem reciprocalCubicNearIntegers_card {A Q η : ℝ} {N : ℕ}
    (hA : 0 < A) (hQ : 0 < Q) (hN : (N:ℝ) ≤ Q) (hη : 0 ≤ η) :
    let μ := (4*A/9)*(2*Q)^(-(7:ℝ)/3)
    ((reciprocalCubicNearIntegers A Q N η).card:ℝ) ≤
      1204*((N:ℝ)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  intro μ
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  have hdom x (hx : x ∈ Icc Q (Q+N)) : x ∈ Icc Q (2*Q) :=
    ⟨hx.1, by linarith only [hx.2,hN]⟩
  have hh := positive_second_derivative_count_optimized
    (reciprocalCubic A) (fun x => -(A/3)*x^(-(4:ℝ)/3))
    (fun x => (4*A/9)*x^(-(7:ℝ)/3)) Q N
    (reciprocalCubicNearIntegers A Q N η) (C:=8) (by norm_num) hμ hη
    (fun x hx => reciprocalCubic_derivative A (hQ.trans_le hx.1))
    (fun x hx => reciprocalCubic_second_derivative A (hQ.trans_le hx.1))
    (fun x hx => (reciprocalCubic_curvature_bounds hA hQ (hdom x hx)).1)
    (fun x hx => (reciprocalCubic_curvature_bounds hA hQ (hdom x hx)).2)
    (Finset.filter_subset _ _) (fun n hn =>
      ⟨round (reciprocalCubic A (Q+n)), (Finset.mem_filter.mp hn).2⟩)
  norm_num only [show (52:ℝ)+144*8=1204 by norm_num] at hh
  simpa only [neg_div] using hh

#print axioms reciprocalCubic_derivative
#print axioms reciprocalCubic_second_derivative
#print axioms reciprocalCubic_curvature_bounds
#print axioms reciprocalCubicNearIntegers_card

def quarticLogCell (H : ℕ) (t n : ℝ) : Set (GafniTao.HeathBrownCoefficientTorus 5) :=
  GafniTao.heathBrownCoefficientCell 5 H (PintzEndpointResearch.logarithmicTaylorPhase t) n

theorem quarticLogCell_mixed_coordinate {H : ℕ} {t u n m : ℝ}
    (hn : 0 < n) (hm : 0 < m)
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty)
    (j : Fin 4) :
    GafniTao.heathBrownDistanceToInteger
      ((-1 : ℝ)^((j : ℕ)+1)*t/(2*Real.pi*(((j : ℕ)+1 : ℕ) : ℝ)*n^((j : ℕ)+1)) -
       (-1 : ℝ)^((j : ℕ)+1)*u/(2*Real.pi*(((j : ℕ)+1 : ℕ) : ℝ)*m^((j : ℕ)+1))) ≤
      2/((H : ℝ)^((j : ℕ)+1)) := by
  obtain ⟨α,ht,hu⟩ := hover
  have htj := ht j (Set.mem_univ j)
  have huj := hu j (Set.mem_univ j)
  have hdist := dist_triangle
    (GafniTao.heathBrownCoefficientCenter 5
      (PintzEndpointResearch.logarithmicTaylorPhase t) n j) (α j)
    (GafniTao.heathBrownCoefficientCenter 5
      (PintzEndpointResearch.logarithmicTaylorPhase u) m j)
  unfold GafniTao.heathBrownCoefficientCenter at hdist
  rw [PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ t hn,
    PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ u hm,
    GafniTao.unitAddCircle_dist_real_coe] at hdist
  change dist (α j) _ ≤ _ at htj huj
  rw [dist_comm (α j)] at htj
  change dist _ _ ≤ ((H : ℝ)^((j : ℕ)+1))⁻¹ at htj huj
  unfold GafniTao.heathBrownCoefficientCenter at htj huj
  rw [PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ t hn] at htj
  rw [PintzEndpointResearch.logarithmicTaylorPhase_coordinate _ u hm] at huj
  simpa only [div_eq_mul_inv] using
    hdist.trans (show _ ≤ 2*((H : ℝ)^((j : ℕ)+1))⁻¹ by linarith only [htj,huj])

def quarticLogLabel (t u n m : ℝ) : ℤ := round ((u/m^3-t/n^3)/(6*Real.pi))

/-- The fourth coordinate has no winding when the actual kernel heights are
at most N^4. The third coordinate retains its literal nearest-integer label. -/
theorem quarticLogCell_raw_coordinates {H : ℕ} {N T t u n m : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T) (hn : N ≤ n) (hm : N ≤ m)
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty) :
    |t/n^4-u/m^4| ≤ 16*Real.pi/(H:ℝ)^4 ∧
    |u/m^3-t/n^3-6*Real.pi*(quarticLogLabel t u n m:ℝ)| ≤ 12*Real.pi/(H:ℝ)^3 := by
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  have h4 := quarticLogCell_mixed_coordinate hnp hmp hover ⟨3,by decide⟩
  have h3 := quarticLogCell_mixed_coordinate hnp hmp hover ⟨2,by decide⟩
  norm_num at h4 h3
  have he4 : t/(2*Real.pi*4*n^4)-u/(2*Real.pi*4*m^4) =
      (t/n^4-u/m^4)/(8*Real.pi) := by ring
  have he3 : -t/(2*Real.pi*3*n^3)- -u/(2*Real.pi*3*m^3) =
      (u/m^3-t/n^3)/(6*Real.pi) := by ring
  rw [he4] at h4
  rw [he3] at h3
  have ht2 : t/n^4 ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hp := pow_le_pow_left₀ hN.le hn 4
    linarith only [hp,hT,htT]
  have hu2 : u/m^4 ≤ 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hp := pow_le_pow_left₀ hN.le hm 4
    linarith only [hp,hT,huT]
  have hsize : |t/n^4-u/m^4| ≤ 2 := by
    have htn : 0 ≤ t/n^4 := by positivity
    have hun : 0 ≤ u/m^4 := by positivity
    exact abs_le.mpr ⟨by linarith only [htn,hu2],by linarith only [hun,ht2]⟩
  have hhalf : |(t/n^4-u/m^4)/(8*Real.pi)| ≤ 1/2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 8*Real.pi)]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hr := GafniTao.abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half h4 hhalf
  rw [abs_div,abs_of_pos (by positivity : 0 < 8*Real.pi)] at hr
  have hr' := (div_le_iff₀ (by positivity : 0 < 8*Real.pi)).mp hr
  constructor
  · convert hr' using 1
    ring
  · have hh := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 6*Real.pi by positivity)
    change 6*Real.pi*|(u/m^3-t/n^3)/(6*Real.pi)-
      (quarticLogLabel t u n m:ℝ)| ≤ _ at hh
    have he : u/m^3-t/n^3-6*Real.pi*(quarticLogLabel t u n m:ℝ) =
        6*Real.pi*((u/m^3-t/n^3)/(6*Real.pi)-(quarticLogLabel t u n m:ℝ)) := by
      field_simp
    rw [he,abs_mul,abs_of_pos (show 0 < 6*Real.pi by positivity)]
    convert hh using 1
    ring

#print axioms quarticLogCell_mixed_coordinate
#print axioms quarticLogCell_raw_coordinates

/-- Positive remainder in the stationary cubic displacement identity. -/
def quarticStationaryRemainder (a b : ℝ) : ℝ :=
  b^2+2*a*b+3*a^2+3*a^3+a^4+6*a^2*b+2*a^3*b+3*a*b^2+3*a^2*b^2

theorem quartic_stationary_identity (r w : ℝ) :
    w^3*(r-1)^4-(r^4-w^3)*(w-1)^3 =
      (w-r)^2*quarticStationaryRemainder (w-1) (r-1) := by
  unfold quarticStationaryRemainder
  ring

theorem quarticStationaryRemainder_bounds {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ 2*b) (hb1 : b ≤ 1) :
    0 ≤ quarticStationaryRemainder a b ∧ quarticStationaryRemainder a b ≤ 115*b^2 := by
  constructor
  · unfold quarticStationaryRemainder
    positivity
  · have h3 : b^3 ≤ b^2 := pow_le_pow_of_le_one hb hb1 (by omega)
    have h4 : b^4 ≤ b^2 := pow_le_pow_of_le_one hb hb1 (by omega)
    calc
      quarticStationaryRemainder a b ≤ quarticStationaryRemainder (2*b) b := by
        unfold quarticStationaryRemainder
        gcongr
      _ = 17*b^2+54*b^3+44*b^4 := by unfold quarticStationaryRemainder; ring
      _ ≤ 115*b^2 := by linarith only [h3,h4]

/-- A quantitative stationary displacement estimate. Both residuals are the
literal cubic and quartic reciprocal phases; no spacing conclusion is assumed. -/
theorem quartic_stationary_displacement {t r n m q p E : ℝ}
    (ht : 0 < t) (hn : 0 < n) (hq : 0 < q) (hp : 0 ≤ p)
    (hr : 1 < r) (hr2 : r ≤ 2)
    (hm : n*(1+(r-1)/2) ≤ m) (hm' : m ≤ n*(1+2*(r-1)))
    (hp3 : p^3=t*(r-1)^4/q)
    (hcubic : |t*r^4/m^3-t/n^3-q| ≤ E) :
    |p-(m-n)| ≤ 460*t*(m/n-r)^2/(q*n^2)+E*(m-n)/q := by
  let w := m/n
  let b := r-1
  let a := w-1
  have hb : 0 < b := by dsimp only [b]; linarith only [hr]
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [hr2]
  have hwlo : 1+b/2 ≤ w := (le_div_iff₀ hn).mpr (by dsimp only [b]; nlinarith only [hm])
  have hwhi : w ≤ 1+2*b := (div_le_iff₀ hn).mpr (by dsimp only [b]; nlinarith only [hm'])
  have ha : 0 ≤ a := by dsimp only [a]; linarith only [hwlo,hb]
  have hab : a ≤ 2*b := by dsimp only [a]; linarith only [hwhi]
  have hmp : 0 < m := by nlinarith only [hm,hn,mul_pos hn hb]
  have hd : 0 < m-n := by nlinarith only [hm,hn,mul_pos hn hb]
  have hw : 1 ≤ w := by linarith only [hwlo,hb]
  have hwn : w*n=m := by dsimp only [w]; field_simp
  have hdn : a*n=m-n := by dsimp only [a]; nlinarith only [hwn]
  have hB := quarticStationaryRemainder_bounds ha hb.le hab hb1
  have hid' : t*b^4-(t*r^4/m^3-t/n^3)*(m-n)^3 =
      t*(w-r)^2*quarticStationaryRemainder a b/w^3 := by
    dsimp only [a,b,w,quarticStationaryRemainder]
    field_simp
    ring
  have hBnonneg := hB.1
  have hmain : |t*b^4-(t*r^4/m^3-t/n^3)*(m-n)^3| ≤
      115*t*b^2*(w-r)^2 := by
    rw [hid',abs_of_nonneg (by positivity)]
    have hw3 : 1 ≤ w^3 := one_le_pow₀ hw
    calc
      _ ≤ t*(w-r)^2*quarticStationaryRemainder a b :=
        div_le_self (by positivity) hw3
      _ ≤ t*(w-r)^2*(115*b^2) := mul_le_mul_of_nonneg_left hB.2 (by positivity)
      _ = _ := by ring
  have hc : |q*(p^3-(m-n)^3)| ≤ 115*t*b^2*(w-r)^2+E*(m-n)^3 := by
    have he : q*(p^3-(m-n)^3) =
        (t*b^4-(t*r^4/m^3-t/n^3)*(m-n)^3)+
        (t*r^4/m^3-t/n^3-q)*(m-n)^3 := by
      dsimp only [b]
      rw [hp3]
      field_simp
      ring
    rw [he]
    apply (abs_add_le _ _).trans (add_le_add hmain _)
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (m-n)^3)]
    exact mul_le_mul_of_nonneg_right hcubic (by positivity)
  have hlower : q*|p-(m-n)| *(m-n)^2 ≤ |q*(p^3-(m-n)^3)| := by
    have he : p^3-(m-n)^3 = (p-(m-n))*(p^2+p*(m-n)+(m-n)^2) := by ring
    rw [he,abs_mul,abs_mul,abs_of_pos hq,
      abs_of_nonneg (by positivity : 0 ≤ p^2+p*(m-n)+(m-n)^2)]
    nlinarith only [mul_nonneg (mul_nonneg hq.le (abs_nonneg (p-(m-n))))
      (show 0 ≤ p^2+p*(m-n) by positivity)]
  have hscale : b^2*n^2 ≤ 4*(m-n)^2 := by
    have hbn : b*n ≤ 2*(m-n) := by nlinarith only [hm]
    have hh := pow_le_pow_left₀ (mul_nonneg hb.le hn.le) hbn 2
    nlinarith only [hh]
  have hbound : |p-(m-n)| ≤ 460*t*(w-r)^2/(q*n^2)+E*(m-n)/q := by
    apply (mul_le_mul_iff_left₀ (mul_pos hq (sq_pos_of_pos hd))).mp
    have he : (460*t*(w-r)^2/(q*n^2)+E*(m-n)/q)*(q*(m-n)^2) =
        460*t*(w-r)^2*(m-n)^2/n^2+E*(m-n)^3 := by field_simp
    rw [he]
    have hs := mul_le_mul_of_nonneg_left hscale
      (by positivity : 0 ≤ 115*t*(w-r)^2)
    have hs' : 115*t*b^2*(w-r)^2 ≤ 460*t*(w-r)^2*(m-n)^2/n^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
      nlinarith only [hs]
    nlinarith only [hlower,hc,hs']
  exact hbound

#print axioms quartic_stationary_identity
#print axioms quarticStationaryRemainder_bounds
#print axioms quartic_stationary_displacement

def quarticHeightRatio (t u : ℝ) : ℝ := (u/t)^((1:ℝ)/4)

theorem quarticHeightRatio_bounds {t u : ℝ} (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    1 < quarticHeightRatio t u ∧ quarticHeightRatio t u ≤ 2 ∧
      t*(quarticHeightRatio t u)^4=u := by
  have hratio : 0 < u/t := div_pos (ht.trans htu) ht
  have hrp : 0 < quarticHeightRatio t u := Real.rpow_pos_of_pos hratio _
  have hpow : (quarticHeightRatio t u)^4=u/t := by
    unfold quarticHeightRatio
    rw [←Real.rpow_mul_natCast hratio.le]
    norm_num
  have hlo : 1 < u/t := (lt_div_iff₀ ht).mpr (by linarith only [htu])
  have hhi : u/t ≤ 2 := (div_le_iff₀ ht).mpr hu
  refine ⟨?_,?_,?_⟩
  · by_contra! hh
    have hh' := pow_le_pow_left₀ hrp.le hh 4
    rw [hpow] at hh'
    norm_num at hh'
    linarith only [hlo,hh']
  · by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by norm_num : (0:ℝ) ≤ 2) (by decide : 4 ≠ 0)
    rw [hpow] at hh'
    norm_num at hh'
    linarith only [hhi,hh']
  · rw [hpow]
    field_simp

theorem quartic_ratio_distance {r w : ℝ} (hr : 1 ≤ r) (hw : 0 ≤ w) :
    |w-r| ≤ |w^4-r^4| := by
  have hrp : 0 ≤ r := by linarith only [hr]
  have hr3 : 1 ≤ r^3 := one_le_pow₀ hr
  have hs : 1 ≤ w^3+w^2*r+w*r^2+r^3 := by
    nlinarith only [hr3,show 0 ≤ w^3+w^2*r+w*r^2 by positivity]
  have he : w^4-r^4=(w-r)*(w^3+w^2*r+w*r^2+r^3) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ w^3+w^2*r+w*r^2+r^3)]
  nlinarith only [mul_le_mul_of_nonneg_left hs (abs_nonneg (w-r))]

/-- The literal fourth-coordinate error controls the displacement from the
stationary height ratio. -/
theorem quarticLogCell_ratio_error {H : ℕ} {N T t u n m : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty) :
    |m/n-quarticHeightRatio t u| ≤ 256*Real.pi*N^4/(t*(H:ℝ)^4) := by
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  obtain ⟨hr,_,hrpow⟩ := quarticHeightRatio_bounds ht htu hu
  have he4 := (quarticLogCell_raw_coordinates hN hT ht.le (ht.trans htu).le
    htT huT hn hm hover).1
  have he : (m/n)^4-(quarticHeightRatio t u)^4 =
      (m^4/t)*(t/n^4-u/m^4) := by
    conv_rhs => rw [←hrpow]
    field_simp
  calc
    _ ≤ |(m/n)^4-(quarticHeightRatio t u)^4| :=
      quartic_ratio_distance hr.le (by positivity)
    _ = (m^4/t)*|t/n^4-u/m^4| := by rw [he,abs_mul,abs_of_pos (by positivity)]
    _ ≤ ((2*N)^4/t)*(16*Real.pi/(H:ℝ)^4) := by gcongr
    _ = _ := by ring

def quarticStationaryAmplitude (t u : ℝ) : ℝ :=
  (t*(quarticHeightRatio t u-1)^4/(6*Real.pi))^((1:ℝ)/3)

theorem quarticStationaryAmplitude_pos {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    0 < quarticStationaryAmplitude t u := by
  have hr := (quarticHeightRatio_bounds ht htu hu).1
  unfold quarticStationaryAmplitude
  exact Real.rpow_pos_of_pos (by positivity) _

theorem quartic_stationary_curve_cube {t u q : ℝ} (ht : 0 < t) (hq : 0 < q) :
    (reciprocalCubic (quarticStationaryAmplitude t u) q)^3 =
      t*(quarticHeightRatio t u-1)^4/(6*Real.pi*q) := by
  unfold reciprocalCubic quarticStationaryAmplitude
  rw [mul_pow,←Real.rpow_mul_natCast (by positivity :
      0 ≤ t*(quarticHeightRatio t u-1)^4/(6*Real.pi)),←Real.rpow_mul_natCast hq.le]
  norm_num
  rw [Real.rpow_neg_one]
  ring

#print axioms quarticHeightRatio_bounds
#print axioms quartic_ratio_distance
#print axioms quarticLogCell_ratio_error
#print axioms quarticStationaryAmplitude_pos
#print axioms quartic_stationary_curve_cube

/-- Source entry into reciprocal-cubic spacing, with the fourth-coordinate
error squared. The label is the actual third-coordinate nearest integer. -/
theorem quarticLogCell_stationary_near_integer {H : ℕ} {N T t u n m : ℝ}
    (hH : 0 < H) (hN : 0 < N) (hT : T ≤ N^4)
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hnN : n ≤ 2*N) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/2)
    (hq : 0 < (quarticLogLabel t u n m:ℝ))
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty) :
    |reciprocalCubic (quarticStationaryAmplitude t u) (quarticLogLabel t u n m)-(m-n)| ≤
      6000000*Real.pi*N^6/(t*(H:ℝ)^8*(quarticLogLabel t u n m:ℝ))+
        8*N*(quarticHeightRatio t u-1)/((H:ℝ)^3*(quarticLogLabel t u n m:ℝ)) := by
  let r := quarticHeightRatio t u
  let q : ℝ := quarticLogLabel t u n m
  let δ := 256*Real.pi*N^4/(t*(H:ℝ)^4)
  let E := 12*Real.pi/(H:ℝ)^3
  have hHp : 0 < (H:ℝ) := by exact_mod_cast hH
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  obtain ⟨hr,hr2,hrpow⟩ := quarticHeightRatio_bounds ht htu hu
  have herr := quarticLogCell_ratio_error hN hT ht htu hu htT huT hn hm hmN hover
  change |m/n-r| ≤ δ at herr
  have hb : 0 < r-1 := by dsimp only [r]; linarith only [hr]
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hsmall' : δ ≤ (r-1)/2 := hsmall
  have hwlo : 1+(r-1)/2 ≤ m/n := by
    have hh := (abs_le.mp herr).1
    linarith only [hh,hsmall']
  have hwhi : m/n ≤ 1+2*(r-1) := by
    have hh := (abs_le.mp herr).2
    linarith only [hh,hsmall',hb]
  have hmlo : n*(1+(r-1)/2) ≤ m := by
    have hh := (le_div_iff₀ hnp).mp hwlo
    nlinarith only [hh]
  have hmhi : m ≤ n*(1+2*(r-1)) := by
    have hh := (div_le_iff₀ hnp).mp hwhi
    nlinarith only [hh]
  have hcubic := (quarticLogCell_raw_coordinates hN hT ht.le (ht.trans htu).le
    htT huT hn hm hover).2
  change |u/m^3-t/n^3-6*Real.pi*q| ≤ E at hcubic
  rw [←hrpow] at hcubic
  have hp := Real.rpow_nonneg (show 0 ≤ q by exact hq.le) (-(1:ℝ)/3)
  have hcurvenon : 0 ≤ reciprocalCubic (quarticStationaryAmplitude t u) q :=
    mul_nonneg (quarticStationaryAmplitude_pos ht htu hu).le hp
  have hbnd := quartic_stationary_displacement ht hnp
    (by positivity : 0 < 6*Real.pi*q) hcurvenon hr hr2 hmlo hmhi
    (quartic_stationary_curve_cube ht hq) hcubic
  change |reciprocalCubic (quarticStationaryAmplitude t u) q-(m-n)| ≤
    460*t*(m/n-r)^2/(6*Real.pi*q*n^2)+E*(m-n)/(6*Real.pi*q) at hbnd
  have hsquare : (m/n-r)^2 ≤ δ^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) herr 2
    simpa only [sq_abs] using hh
  have hfirst : 460*t*(m/n-r)^2/(6*Real.pi*q*n^2) ≤
      6000000*Real.pi*N^6/(t*(H:ℝ)^8*q) := by
    calc
      _ ≤ 460*t*δ^2/(6*Real.pi*q*N^2) := by gcongr
      _ = (15073280/3:ℝ)*Real.pi*N^6/(t*(H:ℝ)^8*q) := by
        dsimp only [δ]
        field_simp
        ring
      _ ≤ _ := by gcongr; norm_num
  have hdiff : m-n ≤ 4*N*(r-1) := by
    have hh := mul_le_mul_of_nonneg_right hnN hb.le
    nlinarith only [hmhi,hh]
  have hsecond : E*(m-n)/(6*Real.pi*q) ≤ 8*N*(r-1)/((H:ℝ)^3*q) := by
    calc
      _ ≤ E*(4*N*(r-1))/(6*Real.pi*q) := by
        gcongr
      _ = _ := by dsimp only [E]; field_simp; ring
  exact hbnd.trans (add_le_add hfirst hsecond)

#print axioms quarticLogCell_stationary_near_integer

theorem quarticHeightRatio_gap {t u : ℝ} (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    (u-t)/15 ≤ t*(quarticHeightRatio t u-1) ∧
      t*(quarticHeightRatio t u-1) ≤ (u-t)/4 := by
  obtain ⟨hr,hr2,hrpow⟩ := quarticHeightRatio_bounds ht htu hu
  let r := quarticHeightRatio t u
  have hrp : 0 ≤ r := by dsimp only [r]; linarith only [hr]
  have hr1 : 1 ≤ r := hr.le
  have h2lo : 1 ≤ r^2 := one_le_pow₀ hr1
  have h3lo : 1 ≤ r^3 := one_le_pow₀ hr1
  have h2hi : r^2 ≤ 4 := by nlinarith only [pow_le_pow_left₀ hrp hr2 2]
  have h3hi : r^3 ≤ 8 := by nlinarith only [pow_le_pow_left₀ hrp hr2 3]
  have hgap : t*(r-1)*(r^3+r^2+r+1)=u-t := by
    change t*r^4=u at hrpow
    nlinarith only [hrpow]
  have hp : 0 ≤ t*(r-1) := mul_nonneg ht.le (sub_nonneg.mpr hr1)
  have hlo := mul_le_mul_of_nonneg_left
    (show 4 ≤ r^3+r^2+r+1 by linarith only [h2lo,h3lo,hr1]) hp
  have hhi := mul_le_mul_of_nonneg_left
    (show r^3+r^2+r+1 ≤ 15 by linarith only [h2hi,h3hi,hr2]) hp
  change (u-t)/15 ≤ t*(r-1) ∧ t*(r-1) ≤ (u-t)/4
  constructor <;> nlinarith only [hgap,hlo,hhi]

theorem cubic_distance_le {r w : ℝ} (hr : 0 ≤ r) (hr2 : r ≤ 2)
    (hw : 0 ≤ w) (hw2 : w ≤ 2) : |w^3-r^3| ≤ 12*|w-r| := by
  have he : w^3-r^3=(w-r)*(w^2+w*r+r^2) := by ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ w^2+w*r+r^2)]
  have hb : w^2+w*r+r^2 ≤ (2:ℝ)^2+2*2+2^2 := by gcongr
  have hh := mul_le_mul_of_nonneg_left hb (abs_nonneg (w-r))
  nlinarith only [hh]

/-- All far-overlap labels are positive and lie at the physical scale
(u-t)/N^3. In particular the zero label is excluded by derived geometry. -/
theorem quarticLogCell_label_bounds {H : ℕ} {N T t u n m : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4)
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3))
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty) :
    t*(quarticHeightRatio t u-1)/(32*N^3) ≤
      6*Real.pi*(quarticLogLabel t u n m:ℝ) ∧
    6*Real.pi*(quarticLogLabel t u n m:ℝ) ≤
      10*t*(quarticHeightRatio t u-1)/N^3 := by
  let r := quarticHeightRatio t u
  let w := m/n
  let b := r-1
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  obtain ⟨hr,hr2,hrpow⟩ := quarticHeightRatio_bounds ht htu hu
  have hrp : 0 ≤ r := by dsimp only [r]; linarith only [hr]
  have hb : 0 < b := by dsimp only [b,r]; linarith only [hr]
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hw2 : w ≤ 2 := (div_le_iff₀ hnp).mpr (by linarith only [hmN,hn])
  have herr := (quarticLogCell_ratio_error hN hT ht htu hu htT huT hn hm hmN hover).trans hsmall
  have hc := cubic_distance_le hrp hr2 hw hw2
  have hc' : |w^3-r^3| ≤ b/2 := by nlinarith only [hc,herr]
  have hr3lo : 1 ≤ r^3 := one_le_pow₀ hr.le
  have hr3hi : r^3 ≤ 8 := by nlinarith only [pow_le_pow_left₀ hrp hr2 3]
  have hnumlo : b/2 ≤ r^4-w^3 := by
    have hh := (abs_le.mp hc').2
    have hbmul := mul_le_mul_of_nonneg_right hr3lo hb.le
    dsimp only [b] at *
    nlinarith only [hh,hbmul]
  have hnumhi : r^4-w^3 ≤ 9*b := by
    have hh := (abs_le.mp hc').1
    have hbmul := mul_le_mul_of_nonneg_right hr3hi hb.le
    dsimp only [b] at *
    nlinarith only [hh,hbmul,hb]
  have hnumpos : 0 ≤ r^4-w^3 := by linarith only [hnumlo,hb]
  have he : u/m^3-t/n^3 = t*(r^4-w^3)/m^3 := by
    change t*r^4=u at hrpow
    rw [←hrpow]
    dsimp only [w]
    field_simp
  have hlo : t*b/(16*N^3) ≤ u/m^3-t/n^3 := by
    rw [he]
    calc
      _ = t*(b/2)/(2*N)^3 := by ring
      _ ≤ _ := by gcongr
  have hhi : u/m^3-t/n^3 ≤ 9*t*b/N^3 := by
    rw [he]
    calc
      _ ≤ t*(9*b)/N^3 := by gcongr
      _ = _ := by ring
  have he3 := (quarticLogCell_raw_coordinates hN hT ht.le (ht.trans htu).le
    htT huT hn hm hover).2
  have he3' := (abs_le.mp he3)
  change 12*Real.pi/(H:ℝ)^3 ≤ t*b/(32*N^3) at hsmall3
  change t*b/(32*N^3) ≤ _ ∧ _ ≤ 10*t*b/N^3
  have hpos : 0 ≤ t*b/N^3 := by positivity
  ring_nf at hlo hhi he3' hsmall3 hpos ⊢
  constructor <;> nlinarith only [hlo,hhi,he3'.1,he3'.2,hsmall3,hpos]

#print axioms quarticHeightRatio_gap
#print axioms cubic_distance_le
#print axioms quarticLogCell_label_bounds

def quarticMixedPairs (S : Finset ℕ) (H : ℕ) (t u : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (S.product S).filter (fun p =>
    (quarticLogCell H t p.1 ∩ quarticLogCell H u p.2).Nonempty)

def quarticLabelShell (S : Finset ℕ) (H : ℕ) (t u : ℝ) (Q : ℕ) : Finset ℤ := by
  classical
  exact ((quarticMixedPairs S H t u).image (fun p => quarticLogLabel t u p.1 p.2)).filter
    (fun q => (Q:ℤ) ≤ q ∧ q < 2*Q)

/-- Actual mixed-cell labels in a positive dyadic shell satisfy the
reciprocal-cubic curvature count. No frequency-sum or spacing bound is supplied. -/
theorem quarticLabelShell_card (S : Finset ℕ) {H Q : ℕ} {N T t u : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hN : 0 < N) (hT : T ≤ N^4)
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/2) :
    let A := quarticStationaryAmplitude t u
    let μ := (4*A/9)*(2*(Q:ℝ))^(-(7:ℝ)/3)
    let η := 6000000*Real.pi*N^6/(t*(H:ℝ)^8*Q)+
      8*N*(quarticHeightRatio t u-1)/((H:ℝ)^3*Q)
    ((quarticLabelShell S H t u Q).card:ℝ) ≤
      1204*((Q:ℝ)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  classical
  intro A μ η
  let J := quarticLabelShell S H t u Q
  let I := J.image (fun q => (q-(Q:ℤ)).toNat)
  have hQp : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hHp : 0 < (H:ℝ) := by exact_mod_cast hH
  have hA : 0 < A := quarticStationaryAmplitude_pos ht htu hu
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hspec q (hq : q∈J) :
      (Q:ℤ) ≤ q ∧ q < 2*Q ∧ ∃ n∈S, ∃ m∈S,
        (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty ∧ quarticLogLabel t u n m=q := by
    obtain ⟨hqim,hlo,hhi⟩ := Finset.mem_filter.mp hq
    obtain ⟨⟨n,m⟩,hnm,hlabel⟩ := Finset.mem_image.mp hqim
    obtain ⟨hmem,hover⟩ := Finset.mem_filter.mp hnm
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hmem
    exact ⟨hlo,hhi,n,hn,m,hm,hover,hlabel⟩
  have hcast q (hq : q∈J) : (Q:ℝ)+((q-(Q:ℤ)).toNat:ℝ)=(q:ℝ) := by
    have hh := Int.toNat_of_nonneg (sub_nonneg.mpr (hspec q hq).1)
    have hh' : ((q-(Q:ℤ)).toNat:ℝ)=(q:ℝ)-(Q:ℝ) := by exact_mod_cast hh
    linarith only [hh']
  have hcard : I.card=J.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb he
    have hca := hcast a ha
    have hcb := hcast b hb
    change (a-(Q:ℤ)).toNat=(b-(Q:ℤ)).toNat at he
    have hh : (a:ℝ)=(b:ℝ) := by rw [←hca,←hcb,he]
    exact_mod_cast hh
  have hsubset : I ⊆ reciprocalCubicNearIntegers A Q Q η := by
    intro j hj
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hqlo,hqhi,n,hn,m,hm,hover,hlabel⟩ := hspec q hq
    have hqpos : 0 < (q:ℝ) := hQp.trans_le (by exact_mod_cast hqlo)
    have hnb := hS n hn
    have hmb := hS m hm
    have hh := quarticLogCell_stationary_near_integer hH hN hT ht htu hu htT huT
      hnb.1 hnb.2 hmb.1 hmb.2 hsmall (by rwa [hlabel]) hover
    rw [hlabel] at hh
    have hupper : 6000000*Real.pi*N^6/(t*(H:ℝ)^8*(q:ℝ))+
        8*N*(quarticHeightRatio t u-1)/((H:ℝ)^3*(q:ℝ)) ≤ η := by
      dsimp only [η]
      have hqQ : (Q:ℝ) ≤ q := by exact_mod_cast hqlo
      gcongr
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · rw [hcast q hq]
      have hrnd := round_le (reciprocalCubic A (q:ℝ)) ((m:ℤ)-(n:ℤ))
      simp only [Int.cast_sub,Int.cast_natCast] at hrnd
      exact hrnd.trans (hh.trans hupper)
  have hc := (Nat.cast_le (α:=ℝ)).mpr (Finset.card_le_card hsubset)
  rw [hcard] at hc
  exact hc.trans (reciprocalCubicNearIntegers_card hA hQp le_rfl hη)

#print axioms quarticLabelShell_card

theorem inverse_cubic_distance {x y B : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxB : x ≤ B) (hyB : y ≤ B) :
    |x-y| ≤ B^4*|1/x^3-1/y^3| := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [abs_sub_comm] using this hy hx hyB hxB (le_of_not_ge hxy)
  have hB : 0 < B := hx.trans_le hxB
  have hpow : x^3 ≤ y^3 := pow_le_pow_left₀ hx.le hxy 3
  rw [abs_of_nonpos (sub_nonpos.mpr hxy),
    abs_of_nonneg (sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) hpow))]
  have hprod : x^2*y^2 ≤ B^4 := by
    calc
      _ ≤ B^2*B^2 := by gcongr
      _ = _ := by ring
  have hsum : x*y ≤ x^2+x*y+y^2 := by nlinarith only [sq_nonneg x,sq_nonneg y]
  have hh := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hx.le hy.le))
  have hh' := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (show 0 ≤ B^4 by positivity) (sub_nonneg.mpr hxy))
  have he : B^4*(1/x^3-1/y^3)=B^4*(y^3-x^3)/(x^3*y^3) := by field_simp
  rw [he]
  apply (le_div_iff₀ (mul_pos (pow_pos hx 3) (pow_pos hy 3))).mpr
  nlinarith only [hh,hh']

theorem quarticLogCell_cubic_projection {H : ℕ} {N T t u n m : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty) :
    |t*(quarticHeightRatio t u-1)/n^3-6*Real.pi*(quarticLogLabel t u n m:ℝ)| ≤
      6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3 := by
  let r := quarticHeightRatio t u
  let w := m/n
  have hnp : 0 < n := hN.trans_le hn
  have hmp : 0 < m := hN.trans_le hm
  obtain ⟨hr,hr2,hrpow⟩ := quarticHeightRatio_bounds ht htu hu
  have hrp : 0 ≤ r := by dsimp only [r]; linarith only [hr]
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hw2 : w ≤ 2 := (div_le_iff₀ hnp).mpr (by linarith only [hmN,hn])
  have herr := quarticLogCell_ratio_error hN hT ht htu hu htT huT hn hm hmN hover
  have hc := cubic_distance_le hrp hr2 hw hw2
  have hc' : |w^3-r^3| ≤ 12*(256*Real.pi*N^4/(t*(H:ℝ)^4)) :=
    hc.trans (mul_le_mul_of_nonneg_left herr (by norm_num))
  have he : t*(r-1)/n^3-(u/m^3-t/n^3)=t*r*(w^3-r^3)/m^3 := by
    change t*r^4=u at hrpow
    rw [←hrpow]
    dsimp only [w]
    field_simp
    ring
  have hproj : |t*(r-1)/n^3-(u/m^3-t/n^3)| ≤ 6144*Real.pi*N/(H:ℝ)^4 := by
    rw [he,abs_div,abs_mul,abs_of_pos (pow_pos hmp 3),abs_of_nonneg (mul_nonneg ht.le hrp)]
    calc
      _ ≤ t*2*(12*(256*Real.pi*N^4/(t*(H:ℝ)^4)))/N^3 := by gcongr
      _ = _ := by field_simp; ring
  have h3 := (quarticLogCell_raw_coordinates hN hT ht.le (ht.trans htu).le
    htT huT hn hm hover).2
  exact (abs_sub_le _ (u/m^3-t/n^3) _).trans (add_le_add hproj h3)

#print axioms inverse_cubic_distance
#print axioms quarticLogCell_cubic_projection

theorem quarticLogCell_label_diameter {H : ℕ} {N T t u n m n' m' : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ n) (hnN : n ≤ 2*N) (hm : N ≤ m) (hmN : m ≤ 2*N)
    (hn' : N ≤ n') (hnN' : n' ≤ 2*N) (hm' : N ≤ m') (hmN' : m' ≤ 2*N)
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty)
    (hover' : (quarticLogCell H t n' ∩ quarticLogCell H u m').Nonempty)
    (hlabel : quarticLogLabel t u n m=quarticLogLabel t u n' m') :
    |n-n'| ≤ 32*N^4*(6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3)/
      (t*(quarticHeightRatio t u-1)) := by
  let b := quarticHeightRatio t u-1
  let B := 6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3
  have hb : 0 < b := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hnp : 0 < n := hN.trans_le hn
  have hnp' : 0 < n' := hN.trans_le hn'
  have hp := quarticLogCell_cubic_projection hN hT ht htu hu htT huT hn hm hmN hover
  have hp' := quarticLogCell_cubic_projection hN hT ht htu hu htT huT hn' hm' hmN' hover'
  rw [hlabel] at hp
  have hdiff : |t*b/n^3-t*b/n'^3| ≤ 2*B := by
    have hh := abs_sub_le (t*b/n^3) (6*Real.pi*(quarticLogLabel t u n' m':ℝ)) (t*b/n'^3)
    rw [abs_sub_comm (6*Real.pi*(quarticLogLabel t u n' m':ℝ))] at hh
    linarith only [hh,hp,hp']
  have he : |t*b/n^3-t*b/n'^3|=t*b*|1/n^3-1/n'^3| := by
    rw [show t*b/n^3-t*b/n'^3=t*b*(1/n^3-1/n'^3) by ring,
      abs_mul,abs_of_pos (mul_pos ht hb)]
  rw [he] at hdiff
  have hinv := inverse_cubic_distance hnp hnp' hnN hnN'
  apply (le_div_iff₀ (mul_pos ht hb)).mpr
  have hh := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ (2*N)^4)
  have hh' := mul_le_mul_of_nonneg_right hinv (mul_pos ht hb).le
  nlinarith only [hh,hh']

theorem quarticLogCell_same_label_unique_second {H n m m' : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 ≤ t) (hu : 0 < u)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hn : N ≤ (n:ℝ)) (hm : N ≤ (m:ℝ)) (hmN : (m:ℝ) ≤ 2*N)
    (hm' : N ≤ (m':ℝ)) (hmN' : (m':ℝ) ≤ 2*N)
    (hsmall : 384*Real.pi*N^4/(u*(H:ℝ)^3) < 1)
    (hover : (quarticLogCell H t n ∩ quarticLogCell H u m).Nonempty)
    (hover' : (quarticLogCell H t n ∩ quarticLogCell H u m').Nonempty)
    (hlabel : quarticLogLabel t u n m=quarticLogLabel t u n m') : m=m' := by
  have hp := (quarticLogCell_raw_coordinates hN hT ht hu.le htT huT hn hm hover).2
  have hp' := (quarticLogCell_raw_coordinates hN hT ht hu.le htT huT hn hm' hover').2
  rw [hlabel] at hp
  have hc : |u/(m:ℝ)^3-u/(m':ℝ)^3| ≤ 24*Real.pi/(H:ℝ)^3 := by
    have hh := abs_sub_le (u/(m:ℝ)^3-t/(n:ℝ)^3)
      (6*Real.pi*(quarticLogLabel t u n m':ℝ)) (u/(m':ℝ)^3-t/(n:ℝ)^3)
    rw [abs_sub_comm (6*Real.pi*(quarticLogLabel t u n m':ℝ))] at hh
    have he : (u/(m:ℝ)^3-t/(n:ℝ)^3)-(u/(m':ℝ)^3-t/(n:ℝ)^3) =
        u/(m:ℝ)^3-u/(m':ℝ)^3 := by ring
    rw [he] at hh
    exact (hh.trans (add_le_add hp hp')).trans_eq (by ring)
  have he : |u/(m:ℝ)^3-u/(m':ℝ)^3|=u*|1/(m:ℝ)^3-1/(m':ℝ)^3| := by
    rw [show u/(m:ℝ)^3-u/(m':ℝ)^3=u*(1/(m:ℝ)^3-1/(m':ℝ)^3) by ring,
      abs_mul,abs_of_pos hu]
  rw [he] at hc
  have hinv := inverse_cubic_distance (hN.trans_le hm) (hN.trans_le hm') hmN hmN'
  have hdist : |(m:ℝ)-m'| ≤ 384*Real.pi*N^4/(u*(H:ℝ)^3) := by
    have hbound : |(m:ℝ)-m'| *u ≤ 384*Real.pi*N^4/(H:ℝ)^3 := by
      have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (2*N)^4)
      have hh' := mul_le_mul_of_nonneg_right hinv hu.le
      calc
        _ ≤ (2*N)^4*|1/(m:ℝ)^3-1/(m':ℝ)^3| *u := hh'
        _ = (2*N)^4*(u*|1/(m:ℝ)^3-1/(m':ℝ)^3|) := by ring
        _ ≤ (2*N)^4*(24*Real.pi/(H:ℝ)^3) := hh
        _ = _ := by ring
    have hh := (le_div_iff₀ hu).mpr hbound
    convert hh using 1
    ring
  have hh : |(m:ℝ)-m'| < 1 := hdist.trans_lt hsmall
  have hh' : |(m:ℤ)-(m':ℤ)| < 1 := by exact_mod_cast hh
  have hab := abs_lt.mp hh'
  omega

#print axioms quarticLogCell_label_diameter
#print axioms quarticLogCell_same_label_unique_second

def quarticLabelPairs (S : Finset ℕ) (H : ℕ) (t u : ℝ) (q : ℤ) : Finset (ℕ × ℕ) := by
  classical
  exact (quarticMixedPairs S H t u).filter (fun p => quarticLogLabel t u p.1 p.2=q)

theorem quarticLabelPairs_card (S : Finset ℕ) {H : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 384*Real.pi*N^4/(u*(H:ℝ)^3) < 1) (q : ℤ) :
    ((quarticLabelPairs S H t u q).card:ℝ) ≤
      1+64*N^4*(6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3)/
        (t*(quarticHeightRatio t u-1)) := by
  classical
  let F := quarticLabelPairs S H t u q
  let D := 32*N^4*(6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3)/
    (t*(quarticHeightRatio t u-1))
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hspec p (hp : p∈F) : p.1∈S ∧ p.2∈S ∧
      (quarticLogCell H t p.1 ∩ quarticLogCell H u p.2).Nonempty ∧
      quarticLogLabel t u p.1 p.2=q := by
    obtain ⟨hp,hlabel⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hover⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hp
    exact ⟨hn,hm,hover,hlabel⟩
  by_cases hF : F.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hF
    let J : Finset ℤ := F.image (fun p => (p.1:ℤ))
    have hcard : J.card=F.card := by
      apply Finset.card_image_iff.mpr
      rintro ⟨n,m⟩ ha ⟨n',m'⟩ hb he
      change (n:ℤ)=(n':ℤ) at he
      have hnn : n=n' := by exact_mod_cast he
      subst n'
      obtain ⟨hn,hm,hover,hl⟩ := hspec (n,m) ha
      obtain ⟨_,hm',hover',hl'⟩ := hspec (n,m') hb
      have heq := quarticLogCell_same_label_unique_second hN hT ht.le (ht.trans htu)
        htT huT (hS n hn).1 (hS m hm).1 (hS m hm).2 (hS m' hm').1 (hS m' hm').2
        hsmall hover hover' (hl.trans hl'.symm)
      exact congrArg (fun z : ℕ => (n,z)) heq
    have hbound := integer_card_le_of_abs_sub_le J (a:=(p₀.1:ℝ)) hD (by
      intro z hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hn,hm,hover,hl⟩ := hspec p hp
      obtain ⟨hn',hm',hover',hl'⟩ := hspec p₀ hp₀
      have hh := quarticLogCell_label_diameter hN hT ht htu hu htT huT
        (hS _ hn).1 (hS _ hn).2 (hS _ hm).1 (hS _ hm).2
        (hS _ hn').1 (hS _ hn').2 (hS _ hm').1 (hS _ hm').2
        hover hover' (hl.trans hl'.symm)
      simpa only [Int.cast_natCast] using hh)
    rw [hcard] at hbound
    convert hbound using 1
    dsimp only [D]
    ring
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (F.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

def quarticMixedShell (S : Finset ℕ) (H : ℕ) (t u : ℝ) (Q : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (quarticMixedPairs S H t u).filter (fun p =>
    (Q:ℤ) ≤ quarticLogLabel t u p.1 p.2 ∧ quarticLogLabel t u p.1 p.2 < 2*Q)

/-- The first nontrivial far-correlation count: actual overlapping index pairs,
not just labels, in one dyadic label shell. -/
theorem quarticMixedShell_card (S : Finset ℕ) {H Q : ℕ} {N T t u : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hN : 0 < N) (hT : T ≤ N^4)
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/2)
    (hsmall3 : 384*Real.pi*N^4/(u*(H:ℝ)^3) < 1) :
    let A := quarticStationaryAmplitude t u
    let μ := (4*A/9)*(2*(Q:ℝ))^(-(7:ℝ)/3)
    let η := 6000000*Real.pi*N^6/(t*(H:ℝ)^8*Q)+
      8*N*(quarticHeightRatio t u-1)/((H:ℝ)^3*Q)
    let D := 1+64*N^4*(6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3)/
      (t*(quarticHeightRatio t u-1))
    ((quarticMixedShell S H t u Q).card:ℝ) ≤
      D*1204*((Q:ℝ)*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) := by
  classical
  intro A μ η D
  let J := quarticLabelShell S H t u Q
  have hcover : quarticMixedShell S H t u Q ⊆ J.biUnion (quarticLabelPairs S H t u) := by
    intro p hp
    obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_biUnion.mpr
    refine ⟨quarticLogLabel t u p.1 p.2,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,hlo,hhi⟩
    · exact Finset.mem_filter.mpr ⟨hp,rfl⟩
  have hcount : ((quarticMixedShell S H t u Q).card:ℝ) ≤
      ∑ q∈J, ((quarticLabelPairs S H t u q).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hbound : ((quarticMixedShell S H t u Q).card:ℝ) ≤ (J.card:ℝ)*D := by
    calc
      _ ≤ ∑ q∈J, ((quarticLabelPairs S H t u q).card:ℝ) := hcount
      _ ≤ ∑ _q∈J, D := Finset.sum_le_sum (fun q _ =>
        quarticLabelPairs_card S hN hT ht htu hu htT huT hS hsmall3 q)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  have hlabels := quarticLabelShell_card S hH hQ hN hT ht htu hu htT huT hS hsmall
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  exact hbound.trans ((mul_le_mul_of_nonneg_right hlabels hD).trans_eq (by ring))

#print axioms quarticLabelPairs_card
#print axioms quarticMixedShell_card

def quarticLabelLevels (S : Finset ℕ) (H : ℕ) (t u : ℝ) : Finset ℕ :=
  (quarticMixedPairs S H t u).image (fun p => Nat.log 2 (quarticLogLabel t u p.1 p.2).toNat)

/-- Every actual mixed pair enters a positive dyadic label shell. -/
theorem quarticMixedPairs_dyadic_cover (S : Finset ℕ) {H : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3)) :
    quarticMixedPairs S H t u ⊆ (quarticLabelLevels S H t u).biUnion
      (fun j => quarticMixedShell S H t u (2^j)) := by
  classical
  intro p hp
  have hp' := hp
  obtain ⟨hmem,hover⟩ := Finset.mem_filter.mp hp'
  obtain ⟨hn,hm⟩ := Finset.mem_product.mp hmem
  have hq := (quarticLogCell_label_bounds hN hT ht htu hu htT huT
    (hS _ hn).1 (hS _ hm).1 (hS _ hm).2 hsmall hsmall3 hover).1
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hqp : 0 < (quarticLogLabel t u p.1 p.2:ℝ) := by
    have hh : 0 < 6*Real.pi*(quarticLogLabel t u p.1 p.2:ℝ) :=
      (by positivity : 0 < t*(quarticHeightRatio t u-1)/(32*N^3)).trans_le hq
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 6*Real.pi)).mp hh
  have hqZ : 0 < quarticLogLabel t u p.1 p.2 := by exact_mod_cast hqp
  let q := quarticLogLabel t u p.1 p.2
  have hqNat : q.toNat ≠ 0 := by omega
  have hqcast : (q.toNat:ℤ)=q := Int.toNat_of_nonneg hqZ.le
  have hlo := Nat.pow_log_le_self 2 hqNat
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q.toNat
  apply Finset.mem_biUnion.mpr
  refine ⟨Nat.log 2 q.toNat,Finset.mem_image.mpr ⟨p,hp,rfl⟩,?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_,?_⟩
  · have hh : ((2^(Nat.log 2 q.toNat):ℕ):ℤ) ≤ q.toNat := by exact_mod_cast hlo
    rwa [hqcast] at hh
  · have hh : (q.toNat:ℤ) < 2*((2^(Nat.log 2 q.toNat):ℕ):ℤ) := by
      rw [pow_succ] at hhi
      exact_mod_cast (by omega : q.toNat < 2*2^(Nat.log 2 q.toNat))
    rwa [hqcast] at hh

/-- Explicit, unconditional finite far-overlap estimate, summed over the
actual dyadic labels. All summands come from the proved curvature count. -/
theorem quarticMixedPairs_card_curvature_sum (S : Finset ℕ) {H : ℕ} {N T t u : ℝ}
    (hH : 0 < H) (hN : 0 < N) (hT : T ≤ N^4)
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3))
    (hunique : 384*Real.pi*N^4/(u*(H:ℝ)^3) < 1) :
    let A := quarticStationaryAmplitude t u
    let μ := fun j : ℕ => (4*A/9)*(2*(2:ℝ)^j)^(-(7:ℝ)/3)
    let η := fun j : ℕ => 6000000*Real.pi*N^6/(t*(H:ℝ)^8*(2:ℝ)^j)+
      8*N*(quarticHeightRatio t u-1)/((H:ℝ)^3*(2:ℝ)^j)
    let D := 1+64*N^4*(6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3)/
      (t*(quarticHeightRatio t u-1))
    ((quarticMixedPairs S H t u).card:ℝ) ≤
      ∑ j∈quarticLabelLevels S H t u,
        D*1204*((2:ℝ)^j*(η j+(μ j)^((1:ℝ)/3))+(μ j)^(-(1:ℝ)/2)) := by
  classical
  intro A μ η D
  have hcover := quarticMixedPairs_dyadic_cover S hN hT ht htu hu htT huT hS hsmall hsmall3
  have hcount : ((quarticMixedPairs S H t u).card:ℝ) ≤
      ∑ j∈quarticLabelLevels S H t u, ((quarticMixedShell S H t u (2^j)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  apply hcount.trans (Finset.sum_le_sum _)
  intro j _
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hsmall' : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/2 := by
    linarith only [hsmall,hb]
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using quarticMixedShell_card S hH
    (pow_pos (by decide : 0 < 2) j) hN hT ht htu hu htT huT hS hsmall' hunique

#print axioms quarticMixedPairs_dyadic_cover
#print axioms quarticMixedPairs_card_curvature_sum

/-- Every occupied shell lies at the gap scale, with absolute constants. -/
theorem quarticLabelLevels_scale (S : Finset ℕ) {H j : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3))
    (hj : j∈quarticLabelLevels S H t u) :
    (u-t)/(32768*N^3) ≤ (2:ℝ)^j ∧ (2:ℝ)^j ≤ (u-t)/N^3 := by
  classical
  obtain ⟨⟨n,m⟩,hp,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hmem,hover⟩ := Finset.mem_filter.mp hp
  obtain ⟨hn,hm⟩ := Finset.mem_product.mp hmem
  let q := quarticLogLabel t u n m
  let b := quarticHeightRatio t u-1
  have hb : 0 < b := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  have hq := quarticLogCell_label_bounds hN hT ht htu hu htT huT
    (hS _ hn).1 (hS _ hm).1 (hS _ hm).2 hsmall hsmall3 hover
  change t*b/(32*N^3) ≤ 6*Real.pi*(q:ℝ) ∧ 6*Real.pi*(q:ℝ) ≤ 10*t*b/N^3 at hq
  have hqp : 0 < (q:ℝ) := by
    have hh : 0 < 6*Real.pi*(q:ℝ) := (by positivity : 0 < t*b/(32*N^3)).trans_le hq.1
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 6*Real.pi)).mp hh
  have hqZ : 0 < q := by exact_mod_cast hqp
  have hqcast : (q.toNat:ℤ)=q := Int.toNat_of_nonneg hqZ.le
  have hqreal : (q.toNat:ℝ)=(q:ℝ) := by exact_mod_cast hqcast
  have hlo : (2:ℝ)^(Nat.log 2 q.toNat) ≤ (q:ℝ) := by
    have hh : (2:ℝ)^(Nat.log 2 q.toNat) ≤ (q.toNat:ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : q.toNat ≠ 0)
    rwa [hqreal] at hh
  have hhi : (q:ℝ) < 2*(2:ℝ)^(Nat.log 2 q.toNat) := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) q.toNat
    rw [pow_succ] at hh
    have hh' : (q.toNat:ℝ) < 2*(2:ℝ)^(Nat.log 2 q.toNat) := by
      exact_mod_cast (by omega : q.toNat < 2*2^(Nat.log 2 q.toNat))
    rwa [hqreal] at hh'
  have hgap := quarticHeightRatio_gap ht htu hu
  change (u-t)/15 ≤ t*b ∧ t*b ≤ (u-t)/4 at hgap
  have hqlo := (div_le_iff₀ (by positivity : 0 < 32*N^3)).mp hq.1
  have hqhi := (le_div_iff₀ (by positivity : 0 < N^3)).mp hq.2
  have hqscale : 0 < N^3*(q:ℝ) := by positivity
  have hQ : 0 < (2:ℝ)^(Nat.log 2 q.toNat) := by positivity
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 32768*N^3)).mpr
    have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hqscale.le
    have hq' := mul_le_mul_of_nonneg_left hhi.le (by positivity : 0 ≤ N^3)
    have hNQ : 0 ≤ N^3*(2:ℝ)^(Nat.log 2 q.toNat) := by positivity
    nlinarith only [hqlo,hgap.1,hπ,hq',hNQ]
  · apply (le_div_iff₀ (by positivity : 0 < N^3)).mpr
    have hπ := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hqscale.le
    have hq' := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ N^3)
    nlinarith only [hqhi,hgap.2,hπ,hq',hqscale]

theorem quarticLabelLevels_card (S : Finset ℕ) {H : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (hT : T ≤ N^4) (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t)
    (htT : t ≤ 2*T) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3)) :
    ((quarticLabelLevels S H t u).card:ℝ) ≤ 31 := by
  classical
  let J := quarticLabelLevels S H t u
  have hb j (hj : j∈J) := quarticLabelLevels_scale S hN hT ht htu hu htT huT hS hsmall hsmall3 hj
  have hd i (hi : i∈J) j (hj : j∈J) : i ≤ j+15 := by
    have h1 := (hb i hi).2
    have h2 := (hb j hj).1
    have hp : (2:ℝ)^i ≤ 32768*(2:ℝ)^j := by
      have hh := (div_le_iff₀ (by positivity : 0 < 32768*N^3)).mp h2
      have hh' := (le_div_iff₀ (by positivity : 0 < N^3)).mp h1
      apply (mul_le_mul_iff_left₀ (pow_pos hN 3)).mp
      nlinarith only [hh,hh']
    have he : 32768*(2:ℝ)^j=(2:ℝ)^(j+15) := by rw [pow_add]; norm_num; ring
    rw [he] at hp
    have hp' : (2:ℕ)^i ≤ (2:ℕ)^(j+15) := by exact_mod_cast hp
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp'
  by_cases hJ : J.Nonempty
  · obtain ⟨j₀,hj₀⟩ := hJ
    let K : Finset ℤ := J.image (fun j : ℕ => (j:ℤ))
    have hcard : K.card=J.card := Finset.card_image_of_injective J Int.ofNat_injective
    have hc := integer_card_le_of_abs_sub_le K (a:=(j₀:ℝ)) (B:=15) (by norm_num) (by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hz
      have ha : (j:ℝ) ≤ (j₀:ℝ)+15 := by exact_mod_cast hd j hj j₀ hj₀
      have hb : (j₀:ℝ) ≤ (j:ℝ)+15 := by exact_mod_cast hd j₀ hj₀ j hj
      simp only [Int.cast_natCast]
      exact abs_le.mpr ⟨by linarith only [hb],by linarith only [ha]⟩)
    rw [hcard] at hc
    norm_num at hc
    exact_mod_cast hc
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    change (J.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    norm_num

#print axioms quarticLabelLevels_scale
#print axioms quarticLabelLevels_card

theorem quarticStationaryAmplitude_cube {t u : ℝ} (ht : 0 < t) :
    (quarticStationaryAmplitude t u)^3=t*(quarticHeightRatio t u-1)^4/(6*Real.pi) := by
  unfold quarticStationaryAmplitude
  rw [←Real.rpow_mul_natCast (by positivity :
    0 ≤ t*(quarticHeightRatio t u-1)^4/(6*Real.pi))]
  norm_num

theorem quarticStationaryAmplitude_identity {t u : ℝ}
    (ht : 0 < t) (htu : t < u) (hu : u ≤ 2*t) :
    quarticStationaryAmplitude t u =
      (t*(quarticHeightRatio t u-1))^((4:ℝ)/3)/((6*Real.pi)^((1:ℝ)/3)*t) := by
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds ht htu hu).1
  apply (pow_left_inj₀ (quarticStationaryAmplitude_pos ht htu hu).le
    (by positivity : 0 ≤ (t*(quarticHeightRatio t u-1))^((4:ℝ)/3)/
      ((6*Real.pi)^((1:ℝ)/3)*t)) (by decide : 3 ≠ 0)).mp
  rw [quarticStationaryAmplitude_cube ht,div_pow,mul_pow,
    ←Real.rpow_mul_natCast (by positivity : 0 ≤ t*(quarticHeightRatio t u-1)),
    ←Real.rpow_mul_natCast (by positivity : 0 ≤ 6*Real.pi)]
  norm_num
  field_simp

theorem quarticStationaryAmplitude_scale {T t u : ℝ}
    (hT : 0 < T) (ht : T ≤ t) (htT : t ≤ 2*T) (htu : t < u) (hu : u ≤ 2*t) :
    (u-t)^((4:ℝ)/3)/(16384*T) ≤ quarticStationaryAmplitude t u ∧
      quarticStationaryAmplitude t u ≤ (u-t)^((4:ℝ)/3)/T := by
  have htp : 0 < t := hT.trans_le ht
  have hΔ : 0 < u-t := sub_pos.mpr htu
  have hgap := quarticHeightRatio_gap htp htu hu
  have hb : 0 < t*(quarticHeightRatio t u-1) := mul_pos htp (sub_pos.mpr (quarticHeightRatio_bounds htp htu hu).1)
  have hπ1 : 1 ≤ 6*Real.pi := by linarith [Real.pi_gt_three]
  have hClo : 1 ≤ (6*Real.pi)^((1:ℝ)/3) := Real.one_le_rpow hπ1 (by norm_num)
  have hChi : (6*Real.pi)^((1:ℝ)/3) ≤ 24 := by
    calc
      _ ≤ (6*Real.pi)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hπ1 (by norm_num)
      _ ≤ 24 := by rw [Real.rpow_one]; linarith [Real.pi_lt_four]
  have h15 : (15:ℝ)^((4:ℝ)/3) ≤ 225 := by
    calc
      _ ≤ (15:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  rw [quarticStationaryAmplitude_identity htp htu hu]
  constructor
  · calc
      _ ≤ (u-t)^((4:ℝ)/3)/(10800*T) := by gcongr; norm_num
      _ = ((u-t)^((4:ℝ)/3)/225)/(24*(2*T)) := by ring
      _ ≤ ((u-t)/15)^((4:ℝ)/3)/(24*(2*T)) := by
        rw [Real.div_rpow hΔ.le (by norm_num : (0:ℝ) ≤ 15)]
        gcongr
      _ ≤ _ := by gcongr; exact hgap.1
  · have hBhi : t*(quarticHeightRatio t u-1) ≤ u-t := by linarith only [hgap.2,hΔ]
    calc
      _ ≤ (u-t)^((4:ℝ)/3)/(1*T) := by gcongr
      _ = _ := by ring

#print axioms quarticStationaryAmplitude_cube
#print axioms quarticStationaryAmplitude_identity
#print axioms quarticStationaryAmplitude_scale

private theorem quartic_curvature_monomial {N T Δ c d : ℝ}
    (hN : 0 < N) (hΔ : 0 < Δ) (hd : 0 < d) :
    (4*(Δ^((4:ℝ)/3)/(c*T))/9)*(2*(Δ/(d*N^3)))^(-(7:ℝ)/3) =
      (4/(9*c))*(d/2)^((7:ℝ)/3)*N^7/(T*Δ) := by
  have he : 2*(Δ/(d*N^3))=((d/2)*(N^3/Δ))⁻¹ := by field_simp
  have hr : (2*(Δ/(d*N^3)))^(-(7:ℝ)/3) = (d/2)^((7:ℝ)/3)*N^7/Δ^((7:ℝ)/3) := by
    rw [he,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
    rw [show -(-(7:ℝ)/3)=(7:ℝ)/3 by ring,
      Real.mul_rpow (by positivity : 0 ≤ d/2) (by positivity : 0 ≤ N^3/Δ),
      Real.div_rpow (by positivity : 0 ≤ N^3) hΔ.le,
      ←Real.rpow_natCast N 3,←Real.rpow_mul hN.le]
    norm_num
    ring
  have hcancel : Δ^((4:ℝ)/3)/Δ^((7:ℝ)/3)=Δ⁻¹ := by
    rw [←Real.rpow_sub hΔ]
    norm_num
    rw [Real.rpow_neg_one]
  rw [hr]
  calc
    _ = (4/(9*c))*(d/2)^((7:ℝ)/3)*N^7/T*(Δ^((4:ℝ)/3)/Δ^((7:ℝ)/3)) := by ring
    _ = _ := by rw [hcancel]; ring

/-- Curvature on every occupied label shell is comparable to N^7/(T*(u-t)). -/
theorem quarticLabelLevels_curvature (S : Finset ℕ) {H j : ℕ} {N T t u : ℝ}
    (hN : 0 < N) (hT : 0 < T) (hT4 : T ≤ N^4)
    (ht : T ≤ t) (htT : t ≤ 2*T) (htu : t < u) (hu : u ≤ 2*t) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3))
    (hj : j∈quarticLabelLevels S H t u) :
    let μ := (4*quarticStationaryAmplitude t u/9)*(2*(2:ℝ)^j)^(-(7:ℝ)/3)
    N^7/(524288*T*(u-t)) ≤ μ ∧ μ ≤ 4398046511104*N^7/(T*(u-t)) := by
  intro μ
  have htp : 0 < t := hT.trans_le ht
  have hΔ : 0 < u-t := sub_pos.mpr htu
  have hA := quarticStationaryAmplitude_scale hT ht htT htu hu
  have hQ := quarticLabelLevels_scale S hN hT4 htp htu hu htT huT hS hsmall hsmall3 hj
  have hAp : 0 < quarticStationaryAmplitude t u := quarticStationaryAmplitude_pos htp htu hu
  have hlower : (4*((u-t)^((4:ℝ)/3)/(16384*T))/9)*
      (2*((u-t)/(1*N^3)))^(-(7:ℝ)/3) ≤ μ := by
    dsimp only [μ]
    have hq : 2*(2:ℝ)^j ≤ 2*((u-t)/(1*N^3)) := by simpa only [one_mul] using mul_le_mul_of_nonneg_left hQ.2 (by norm_num : (0:ℝ) ≤ 2)
    apply mul_le_mul
    · gcongr
      exact hA.1
    · exact Real.rpow_le_rpow_of_nonpos (by positivity) hq (by norm_num)
    · positivity
    · positivity
  have hupper : μ ≤ (4*((u-t)^((4:ℝ)/3)/(1*T))/9)*
      (2*((u-t)/(32768*N^3)))^(-(7:ℝ)/3) := by
    dsimp only [μ]
    apply mul_le_mul
    · gcongr
      simpa only [one_mul] using hA.2
    · exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (mul_le_mul_of_nonneg_left hQ.1 (by norm_num : (0:ℝ) ≤ 2)) (by norm_num)
    · positivity
    · positivity
  rw [quartic_curvature_monomial hN hΔ (by norm_num : (0:ℝ) < 1)] at hlower
  rw [quartic_curvature_monomial hN hΔ (by norm_num : (0:ℝ) < 32768)] at hupper
  have hhalf : (1/8:ℝ) ≤ (1/2:ℝ)^((7:ℝ)/3) := by
    calc
      _ = (1/2:ℝ)^(3:ℝ) := by norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
  have hbig : (32768/2:ℝ)^((7:ℝ)/3) ≤ 4398046511104 := by
    calc
      _ ≤ (32768/2:ℝ)^(3:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := by norm_num
  constructor
  · apply le_trans _ hlower
    have hh := mul_le_mul_of_nonneg_right hhalf
      (by positivity : 0 ≤ (4/(9*(16384:ℝ)))*N^7/(T*(u-t)))
    calc
      _ = (1/524288:ℝ)*(N^7/(T*(u-t))) := by field_simp
      _ ≤ (1/294912:ℝ)*(N^7/(T*(u-t))) := by gcongr; norm_num
      _ ≤ _ := by convert hh using 1 <;> ring
  · apply hupper.trans
    have hh := mul_le_mul_of_nonneg_right hbig
      (by positivity : 0 ≤ (4/(9*(1:ℝ)))*N^7/(T*(u-t)))
    have hp : 0 ≤ N^7/(T*(u-t)) := by positivity
    ring_nf at hh hp ⊢
    nlinarith only [hh,hp]

#print axioms quarticLabelLevels_curvature

def quarticFarCountScale (N T Δ H : ℝ) : ℝ :=
  (1+N^5/(Δ*H^4))*(N^6/(T*H^8)+Δ*N/(T*H^3)+
    (Δ/N^3)*(N^7/(T*Δ))^((1:ℝ)/3)+(T*Δ/N^7)^((1:ℝ)/2))

/-- Physical-scale far-overlap estimate assembled from the actual stationary
curve and all label fibers. This is the counting input to the Gram moment. -/
theorem quarticMixedPairs_card_physical (S : Finset ℕ) {H : ℕ} {N T t u : ℝ}
    (hH : 0 < H) (hHN : (H:ℝ) ≤ N) (hN : 0 < N) (hT : 0 < T) (hT4 : T ≤ N^4)
    (ht : T ≤ t) (htT : t ≤ 2*T) (htu : t < u) (hu : u ≤ 2*t) (huT : u ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N)
    (hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24)
    (hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3))
    (hunique : 384*Real.pi*N^4/(u*(H:ℝ)^3) < 1) :
    ((quarticMixedPairs S H t u).card:ℝ) ≤
      100000000000000000000*quarticFarCountScale N T (u-t) H := by
  classical
  let Δ := u-t
  let M := N^7/(T*Δ)
  let X := N^5/(Δ*(H:ℝ)^4)
  let Y := N^6/(T*(H:ℝ)^8)+Δ*N/(T*(H:ℝ)^3)+
    (Δ/N^3)*M^((1:ℝ)/3)+(T*Δ/N^7)^((1:ℝ)/2)
  let D := 1+64*N^4*(6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3)/
    (t*(quarticHeightRatio t u-1))
  have hHp : 0 < (H:ℝ) := by exact_mod_cast hH
  have htp : 0 < t := hT.trans_le ht
  have hΔ : 0 < Δ := sub_pos.mpr htu
  have hMp : 0 < M := by dsimp only [M]; positivity
  have hX : 0 ≤ X := by dsimp only [X]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds htp htu hu).1
  have hgap := quarticHeightRatio_gap htp htu hu
  have hD : D ≤ 30000000*(1+X) := by
    have hB : 6144*Real.pi*N/(H:ℝ)^4+12*Real.pi/(H:ℝ)^3 ≤ 24624*N/(H:ℝ)^4 := by
      calc
        _ = (6144*Real.pi*N+12*Real.pi*(H:ℝ))/(H:ℝ)^4 := by field_simp
        _ ≤ (6144*4*N+12*4*N)/(H:ℝ)^4 := by gcongr <;> exact Real.pi_lt_four.le
        _ = _ := by ring
    have hD' : D ≤ 1+23639040*X := by
      calc
        _ ≤ 1+64*N^4*(24624*N/(H:ℝ)^4)/(Δ/15) := by
          dsimp only [D]
          gcongr
          exact hgap.1
        _ = _ := by dsimp only [X]; field_simp; ring
    nlinarith only [hD',hX]
  have hDp : 0 ≤ D := by dsimp only [D]; positivity
  have hsummand j (hj : j∈quarticLabelLevels S H t u) :
      let μ := (4*quarticStationaryAmplitude t u/9)*(2*(2:ℝ)^j)^(-(7:ℝ)/3)
      let η := 6000000*Real.pi*N^6/(t*(H:ℝ)^8*(2:ℝ)^j)+
        8*N*(quarticHeightRatio t u-1)/((H:ℝ)^3*(2:ℝ)^j)
      D*1204*((2:ℝ)^j*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2)) ≤
        1000000000000000000*((1+X)*Y) := by
    intro μ η
    have hμ := quarticLabelLevels_curvature S hN hT hT4 ht htT htu hu huT hS hsmall hsmall3 hj
    have hQ := quarticLabelLevels_scale S hN hT4 htp htu hu htT huT hS hsmall hsmall3 hj
    have hμp : 0 < μ := by
      have hA := quarticStationaryAmplitude_pos htp htu hu
      dsimp only [μ]
      positivity
    have hμhi : μ ≤ 4398046511104*M := by
      convert hμ.2 using 1
      dsimp only [M,Δ]
      ring
    have hμlo : M/1048576 ≤ μ := by
      calc
        _ ≤ M/524288 := by gcongr; norm_num
        _ = N^7/(524288*T*(u-t)) := by dsimp only [M,Δ]; field_simp
        _ ≤ μ := hμ.1
    have hcuberoot : (4398046511104:ℝ)^((1:ℝ)/3)=16384 := by
      rw [show (4398046511104:ℝ)=(16384:ℝ)^3 by norm_num,
        ←Real.rpow_natCast (16384:ℝ) 3,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16384)]
      norm_num
    have hroot : μ^((1:ℝ)/3) ≤ 16384*M^((1:ℝ)/3) := by
      calc
        _ ≤ (4398046511104*M)^((1:ℝ)/3) := Real.rpow_le_rpow hμp.le hμhi (by norm_num)
        _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4398046511104) hMp.le,hcuberoot]
    have htail : μ^(-(1:ℝ)/2) ≤ 1024*(T*Δ/N^7)^((1:ℝ)/2) := by
      calc
        _ ≤ (M/1048576)^(-(1:ℝ)/2) := Real.rpow_le_rpow_of_nonpos (by positivity) hμlo (by norm_num)
        _ = _ := by
          have he : M/1048576=((1024:ℝ)^2*(T*Δ/N^7))⁻¹ := by
            dsimp only [M]
            field_simp
            norm_num
          rw [he,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
          rw [show -(-(1:ℝ)/2)=(1:ℝ)/2 by ring,
            Real.mul_rpow (by positivity : 0 ≤ (1024:ℝ)^2) (by positivity : 0 ≤ T*Δ/N^7),
            ←Real.rpow_natCast (1024:ℝ) 2,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1024)]
          norm_num
    have hwidth : (2:ℝ)^j*η ≤ 24000000*(N^6/(T*(H:ℝ)^8))+2*(Δ*N/(T*(H:ℝ)^3)) := by
      calc
        _ = 6000000*Real.pi*N^6/(t*(H:ℝ)^8)+8*N*(quarticHeightRatio t u-1)/(H:ℝ)^3 := by
          dsimp only [η]
          field_simp
        _ ≤ 6000000*4*N^6/(T*(H:ℝ)^8)+8*N*(Δ/(4*T))/(H:ℝ)^3 := by
          apply add_le_add
          · gcongr
            exact Real.pi_lt_four.le
          · have hbgap : quarticHeightRatio t u-1 ≤ Δ/(4*T) := by
              have hh := (le_div_iff₀ htp).mpr (show (quarticHeightRatio t u-1)*t ≤ (u-t)/4 by nlinarith only [hgap.2])
              calc
                _ ≤ ((u-t)/4)/t := hh
                _ ≤ ((u-t)/4)/T := by gcongr
                _ = _ := by dsimp only [Δ]; ring
            gcongr
        _ = _ := by ring
    have hroot' : (2:ℝ)^j*μ^((1:ℝ)/3) ≤ 16384*((Δ/N^3)*M^((1:ℝ)/3)) := by
      have hh := mul_le_mul hQ.2 hroot (Real.rpow_nonneg hμp.le _) (by positivity)
      convert hh using 1
      ring
    have hinner : (2:ℝ)^j*(η+μ^((1:ℝ)/3))+μ^(-(1:ℝ)/2) ≤ 24000000*Y := by
      have hx : 0 ≤ N^6/(T*(H:ℝ)^8) := by positivity
      have hy : 0 ≤ Δ*N/(T*(H:ℝ)^3) := by positivity
      have hz : 0 ≤ (Δ/N^3)*M^((1:ℝ)/3) := by positivity
      have hw : 0 ≤ (T*Δ/N^7)^((1:ℝ)/2) := by positivity
      dsimp only [Y]
      nlinarith only [hwidth,hroot',htail,hx,hy,hz,hw]
    calc
      _ ≤ (30000000*(1+X))*1204*(24000000*Y) := by gcongr
      _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ 1+X by positivity) hY]
  have hcount := quarticMixedPairs_card_curvature_sum S hH hN hT4 htp htu hu htT huT hS hsmall hsmall3 hunique
  have hlevels := quarticLabelLevels_card S hN hT4 htp htu hu htT huT hS hsmall hsmall3
  have hbound : ((quarticMixedPairs S H t u).card:ℝ) ≤
      ((quarticLabelLevels S H t u).card:ℝ)*(1000000000000000000*((1+X)*Y)) := by
    apply hcount.trans
    calc
      _ ≤ ∑ _j∈quarticLabelLevels S H t u, 1000000000000000000*((1+X)*Y) :=
        Finset.sum_le_sum hsummand
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]
  change ((quarticMixedPairs S H t u).card:ℝ) ≤ 100000000000000000000*((1+X)*Y)
  have hh := mul_le_mul_of_nonneg_right hlevels
    (by positivity : 0 ≤ 1000000000000000000*((1+X)*Y))
  nlinarith only [hbound,hh,mul_nonneg (show 0 ≤ 1+X by positivity) hY]

#print axioms quarticMixedPairs_card_physical

private theorem adaptive_quartic_monomial {N T : ℝ} (hN : 0 < N) (hT : 0 < T)
    (a b : ℝ) (k : ℕ) :
    N^a/(T^b*(N/T^((1:ℝ)/5))^k)=N^(a-(k:ℝ))*T^((k:ℝ)/5-b) := by
  rw [div_pow,←Real.rpow_mul_natCast hT.le,←Real.rpow_natCast N k]
  have hNpow : N^(k:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  have hTpow : T^((1:ℝ)/5*(k:ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
  have hTb : T^b ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
  calc
    _ = (N^a/N^(k:ℝ))*(T^((1:ℝ)/5*(k:ℝ))/T^b) := by field_simp
    _ = _ := by rw [←Real.rpow_sub hN,←Real.rpow_sub hT]; congr 2; ring

theorem quarticFarCountScale_le_power {N T Δ H : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hΔ : 0 < Δ)
    (hTupper : T ≤ N^((79:ℝ)/20)) (hΔlower : N^((18:ℝ)/5) ≤ Δ)
    (hΔT : Δ ≤ T) (hH : N/T^((1:ℝ)/5) ≤ H) :
    quarticFarCountScale N T Δ H ≤ 8*N^((293:ℝ)/300) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hHp : 0 < H := (by positivity : 0 < N/T^((1:ℝ)/5)).trans_le hH
  let X := N^5/(Δ*H^4)
  let a := N^6/(T*H^8)
  let b := Δ*N/(T*H^3)
  let c := (Δ/N^3)*(N^7/(T*Δ))^((1:ℝ)/3)
  let d := (T*Δ/N^7)^((1:ℝ)/2)
  have hXpos : 0 ≤ X := by dsimp only [X]; positivity
  have haPos : 0 ≤ a := by dsimp only [a]; positivity
  have hbPos : 0 ≤ b := by dsimp only [b]; positivity
  have hcPos : 0 ≤ c := by dsimp only [c]; positivity
  have hdPos : 0 ≤ d := by dsimp only [d]; positivity
  have hX : X ≤ N^((14:ℝ)/25) := by
    calc
      _ ≤ (N^((5:ℝ))/(T^(0:ℝ)*(N/T^((1:ℝ)/5))^4))/Δ := by
        norm_num only [Real.rpow_ofNat,Real.rpow_natCast,Real.rpow_zero,one_mul]
        dsimp only [X]
        rw [div_div]
        rw [mul_comm ((N/T^((1:ℝ)/5))^4) Δ]
        gcongr
      _ = N*T^((4:ℝ)/5)/Δ := by rw [adaptive_quartic_monomial hNp hT]; norm_num
      _ ≤ N*(N^((79:ℝ)/20))^((4:ℝ)/5)/N^((18:ℝ)/5) := by gcongr
      _ = _ := by
        rw [←Real.rpow_mul hNp.le]
        nth_rw 1 [←Real.rpow_one N]
        rw [←Real.rpow_add hNp,←Real.rpow_sub hNp]
        norm_num
  have ha : a ≤ N^((37:ℝ)/100) := by
    calc
      _ ≤ N^((6:ℝ))/(T^(1:ℝ)*(N/T^((1:ℝ)/5))^8) := by
        norm_num only [Real.rpow_ofNat,Real.rpow_natCast,Real.rpow_one]
        dsimp only [a]
        gcongr
      _ = N^(-(2:ℝ))*T^((3:ℝ)/5) := by rw [adaptive_quartic_monomial hNp hT]; norm_num
      _ ≤ N^(-(2:ℝ))*(N^((79:ℝ)/20))^((3:ℝ)/5) := by gcongr
      _ = _ := by rw [←Real.rpow_mul hNp.le,←Real.rpow_add hNp]; norm_num
  have hb : b ≤ N^((37:ℝ)/100) := by
    calc
      _ ≤ Δ*(N^((1:ℝ))/(T^(1:ℝ)*(N/T^((1:ℝ)/5))^3)) := by
        norm_num only [Real.rpow_one]
        dsimp only [b]
        rw [mul_div_assoc]
        gcongr
      _ = Δ*(N^(-(2:ℝ))*T^(-(2:ℝ)/5)) := by rw [adaptive_quartic_monomial hNp hT]; norm_num
      _ ≤ T*(N^(-(2:ℝ))*T^(-(2:ℝ)/5)) := by gcongr
      _ = N^(-(2:ℝ))*T^((3:ℝ)/5) := by
        rw [show T*(N^(-(2:ℝ))*T^(-(2:ℝ)/5))=N^(-(2:ℝ))*(T*T^(-(2:ℝ)/5)) by ring]
        nth_rw 1 [←Real.rpow_one T]
        rw [←Real.rpow_add hT]
        norm_num
      _ ≤ N^(-(2:ℝ))*(N^((79:ℝ)/20))^((3:ℝ)/5) := by gcongr
      _ = _ := by rw [←Real.rpow_mul hNp.le,←Real.rpow_add hNp]; norm_num
  have hc3 : c^3 ≤ N^((39:ℝ)/20) := by
    have he : c^3=Δ^2/(N^2*T) := by
      dsimp only [c]
      rw [mul_pow,div_pow,←Real.rpow_mul_natCast (by positivity : 0 ≤ N^7/(T*Δ))]
      norm_num
      field_simp
    rw [he]
    calc
      _ ≤ T^2/(N^2*T) := by gcongr
      _ = T/N^2 := by field_simp
      _ ≤ N^((79:ℝ)/20)/N^2 := by gcongr
      _ = _ := by rw [←Real.rpow_natCast N 2,←Real.rpow_sub hNp]; norm_num
  have hc : c ≤ N^((13:ℝ)/20) := by
    by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by positivity) (by decide : 3 ≠ 0)
    rw [←Real.rpow_mul_natCast hNp.le] at hh'
    norm_num at hh'
    exact (not_lt_of_ge hc3) hh'
  have hd2 : d^2 ≤ N^((9:ℝ)/10) := by
    dsimp only [d]
    rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ T*Δ/N^7)]
    norm_num
    calc
      _ ≤ T*T/N^7 := by gcongr
      _ ≤ (N^((79:ℝ)/20))^2/N^7 := by rw [pow_two]; gcongr
      _ = _ := by rw [←Real.rpow_mul_natCast hNp.le,←Real.rpow_natCast N 7,←Real.rpow_sub hNp]; norm_num
  have hd : d ≤ N^((9:ℝ)/20) := by
    by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by positivity) (by decide : 2 ≠ 0)
    rw [←Real.rpow_mul_natCast hNp.le] at hh'
    norm_num at hh'
    exact (not_lt_of_ge hd2) hh'
  have hXc3 : (X*c)^3 ≤ N^((293:ℝ)/100) := by
    have he : (X*c)^3=N^13/(T*Δ*H^12) := by
      dsimp only [X,c]
      rw [mul_pow,mul_pow,div_pow,div_pow,←Real.rpow_mul_natCast (by positivity : 0 ≤ N^7/(T*Δ))]
      norm_num
      field_simp
    rw [he]
    calc
      _ ≤ (N^((13:ℝ))/(T^(1:ℝ)*(N/T^((1:ℝ)/5))^12))/Δ := by
        norm_num only [Real.rpow_ofNat,Real.rpow_natCast,Real.rpow_one]
        rw [div_div]
        rw [show (T*(N/T^((1:ℝ)/5))^12)*Δ=T*Δ*(N/T^((1:ℝ)/5))^12 by ring]
        gcongr
      _ = N*T^((7:ℝ)/5)/Δ := by rw [adaptive_quartic_monomial hNp hT]; norm_num
      _ ≤ N*(N^((79:ℝ)/20))^((7:ℝ)/5)/N^((18:ℝ)/5) := by gcongr
      _ = _ := by
        rw [←Real.rpow_mul hNp.le]
        nth_rw 1 [←Real.rpow_one N]
        rw [←Real.rpow_add hNp,←Real.rpow_sub hNp]
        norm_num
  have hXc : X*c ≤ N^((293:ℝ)/300) := by
    by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by positivity) (by decide : 3 ≠ 0)
    rw [←Real.rpow_mul_natCast hNp.le] at hh'
    norm_num at hh'
    exact (not_lt_of_ge hXc3) hh'
  have hXd2 : (X*d)^2 ≤ N^((167:ℝ)/100) := by
    have he : (X*d)^2=N^3*T/(Δ*H^8) := by
      dsimp only [X,d]
      rw [mul_pow,div_pow,←Real.rpow_mul_natCast (by positivity : 0 ≤ T*Δ/N^7)]
      norm_num
      field_simp
    rw [he]
    calc
      _ ≤ N^3*T/(Δ*(N/T^((1:ℝ)/5))^8) := by gcongr
      _ = T*(N^((3:ℝ))/(T^(0:ℝ)*(N/T^((1:ℝ)/5))^8))/Δ := by
        norm_num only [Real.rpow_ofNat,Real.rpow_zero,one_mul]
        ring
      _ = N^(-(5:ℝ))*T^((13:ℝ)/5)/Δ := by
        rw [adaptive_quartic_monomial hNp hT]
        norm_num
        rw [mul_left_comm T]
        nth_rw 1 [←Real.rpow_one T]
        rw [←Real.rpow_add hT]
        norm_num
      _ ≤ N^(-(5:ℝ))*(N^((79:ℝ)/20))^((13:ℝ)/5)/N^((18:ℝ)/5) := by gcongr
      _ = _ := by rw [←Real.rpow_mul hNp.le,←Real.rpow_add hNp,←Real.rpow_sub hNp]; norm_num
  have hXd : X*d ≤ N^((167:ℝ)/200) := by
    by_contra! hh
    have hh' := pow_lt_pow_left₀ hh (by positivity) (by decide : 2 ≠ 0)
    rw [←Real.rpow_mul_natCast hNp.le] at hh'
    norm_num at hh'
    exact (not_lt_of_ge hXd2) hh'
  have hXa : X*a ≤ N^((93:ℝ)/100) := by
    have hh := mul_le_mul hX ha haPos (by positivity)
    simpa only [←Real.rpow_add hNp,show (14:ℝ)/25+37/100=93/100 by norm_num] using hh
  have hXb : X*b ≤ N^((93:ℝ)/100) := by
    have hh := mul_le_mul hX hb hbPos (by positivity)
    simpa only [←Real.rpow_add hNp,show (14:ℝ)/25+37/100=93/100 by norm_num] using hh
  have h37 := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (37:ℝ)/100 ≤ 293/300)
  have h13 := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (13:ℝ)/20 ≤ 293/300)
  have h9 := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (9:ℝ)/20 ≤ 293/300)
  have h93 := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (93:ℝ)/100 ≤ 293/300)
  have h167 := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (167:ℝ)/200 ≤ 293/300)
  change (1+X)*(a+b+c+d) ≤ _
  nlinarith only [ha.trans h37,hb.trans h37,hc.trans h13,hd.trans h9,
    hXa.trans h93,hXb.trans h93,hXc,hXd.trans h167]

#print axioms quarticFarCountScale_le_power

/-- A uniform power saving for the actual far mixed logarithmic cells.
All geometric smallness requirements of the curvature count are discharged. -/
theorem quarticMixedPairs_card_far :
    ∃ C : ℝ, 2 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T t u : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → (H:ℝ) ≤ N →
      T ≤ t → t ≤ 2*T → T ≤ u → u ≤ 2*T → N^((18:ℝ)/5) ≤ u-t →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ((quarticMixedPairs S H t u).card:ℝ) ≤ N^((99:ℝ)/100) := by
  have hev : ∀ᶠ N : ℝ in Filter.atTop,
      1000000000000000000000 ≤ N^((1:ℝ)/75) := by
    simpa only [pow_zero,mul_one] using
      eventually_const_log_pow_le_rpow 1000000000000000000000 (by norm_num) 0
        (η:=(1:ℝ)/75) (by norm_num)
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 2 C,le_max_left _ _,?_⟩
  intro S H N T t u hNC hTlo hThi hHlo hHhi ht htT hu huT hfar hS
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hNC
  have hN : 1 ≤ N := by linarith only [hN2]
  have hNp : 0 < N := by linarith only [hN2]
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hTlo
  have hHp : 0 < (H:ℝ) := (by positivity : 0 < N/T^((1:ℝ)/5)).trans_le hHlo
  have hH : 0 < H := by exact_mod_cast hHp
  have htp : 0 < t := hTp.trans_le ht
  have hup : 0 < u := hTp.trans_le hu
  have hΔ : 0 < u-t := (Real.rpow_pos_of_pos hNp _).trans_le hfar
  have htu : t < u := sub_pos.mp hΔ
  have hu2t : u ≤ 2*t := by linarith only [ht,huT]
  have hT4 : T ≤ N^4 := hThi.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hN
      (by norm_num : (79:ℝ)/20 ≤ 4))
  have hgap := quarticHeightRatio_gap htp htu hu2t
  have hb : 0 < quarticHeightRatio t u-1 := sub_pos.mpr (quarticHeightRatio_bounds htp htu hu2t).1
  have hconst := hC N ((le_max_right _ _).trans hNC)
  have hconst' : 1000000 ≤ N^((11:ℝ)/25) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1:ℝ)/75 ≤ 11/25)
    linarith only [hconst,hh]
  have hHpow (k : ℕ) : N^k/(H:ℝ)^k ≤ T^((k:ℝ)/5) := by
    calc
      _ ≤ N^(k:ℝ)/(T^(0:ℝ)*(N/T^((1:ℝ)/5))^k) := by
        rw [Real.rpow_natCast,Real.rpow_zero,one_mul]
        gcongr
      _ = _ := by rw [adaptive_quartic_monomial hNp hTp]; simp
  have hscale4 : 1000000*(N^4/(H:ℝ)^4) ≤ u-t := by
    calc
      _ ≤ N^((11:ℝ)/25)*T^((4:ℝ)/5) := mul_le_mul hconst' (hHpow 4) (by positivity) (by positivity)
      _ ≤ N^((11:ℝ)/25)*(N^((79:ℝ)/20))^((4:ℝ)/5) := by gcongr
      _ = N^((18:ℝ)/5) := by rw [←Real.rpow_mul hNp.le,←Real.rpow_add hNp]; norm_num
      _ ≤ _ := hfar
  have hscale3 : 1000000*(N^3/(H:ℝ)^3) ≤ u-t := by
    calc
      _ ≤ N^((11:ℝ)/25)*T^((3:ℝ)/5) := mul_le_mul hconst' (hHpow 3) (by positivity) (by positivity)
      _ ≤ N^((11:ℝ)/25)*(N^((79:ℝ)/20))^((3:ℝ)/5) := by gcongr
      _ = N^((281:ℝ)/100) := by rw [←Real.rpow_mul hNp.le,←Real.rpow_add hNp]; norm_num
      _ ≤ N^((18:ℝ)/5) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
      _ ≤ _ := hfar
  have hsmall : 256*Real.pi*N^4/(t*(H:ℝ)^4) ≤ (quarticHeightRatio t u-1)/24 := by
    have hh : 256*Real.pi*(N^4/(H:ℝ)^4) ≤ (u-t)/360 := by
      have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le
        (by positivity : 0 ≤ N^4/(H:ℝ)^4)
      have hp : 0 ≤ N^4/(H:ℝ)^4 := by positivity
      nlinarith only [hscale4,hπ,hp]
    calc
      _ = (256*Real.pi*(N^4/(H:ℝ)^4))/t := by ring
      _ ≤ ((u-t)/360)/t := div_le_div_of_nonneg_right hh htp.le
      _ ≤ ((t*(quarticHeightRatio t u-1))/24)/t := by
        apply div_le_div_of_nonneg_right _ htp.le
        linarith only [hgap.1]
      _ = _ := by field_simp
  have hsmall3 : 12*Real.pi/(H:ℝ)^3 ≤ t*(quarticHeightRatio t u-1)/(32*N^3) := by
    have hh : 384*Real.pi*(N^3/(H:ℝ)^3) ≤ t*(quarticHeightRatio t u-1) := by
      have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_four.le
        (by positivity : 0 ≤ N^3/(H:ℝ)^3)
      have hp : 0 ≤ N^3/(H:ℝ)^3 := by positivity
      nlinarith only [hscale3,hπ,hp,hgap.1]
    apply (le_div_iff₀ (by positivity : 0 < 32*N^3)).mpr
    convert hh using 1
    ring
  have hunique : 384*Real.pi*N^4/(u*(H:ℝ)^3) < 1 := by
    have hbound : N^4/(u*(H:ℝ)^3) ≤ N^(-((11:ℝ)/25)) := by
      calc
        _ ≤ N^(4:ℝ)/(T^(1:ℝ)*(N/T^((1:ℝ)/5))^3) := by
          norm_num only [Real.rpow_ofNat,Real.rpow_one]
          gcongr
        _ = N*T^(-(2:ℝ)/5) := by rw [adaptive_quartic_monomial hNp hTp]; norm_num
        _ ≤ N*(N^((18:ℝ)/5))^(-(2:ℝ)/5) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < N^((18:ℝ)/5)) hTlo
              (by norm_num : -(2:ℝ)/5 ≤ 0)) hNp.le
        _ = _ := by
          rw [←Real.rpow_mul hNp.le]
          nth_rw 1 [←Real.rpow_one N]
          rw [←Real.rpow_add hNp]
          norm_num
    calc
      _ = (384*Real.pi)*(N^4/(u*(H:ℝ)^3)) := by ring
      _ ≤ (384*Real.pi)*N^(-((11:ℝ)/25)) := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 384*Real.pi/N^((11:ℝ)/25) := by rw [Real.rpow_neg hNp.le]; ring
      _ < 1 := (div_lt_one (by positivity)).mpr (by linarith [Real.pi_lt_four,hconst'])
  have hc := quarticMixedPairs_card_physical S hH hHhi hNp hTp hT4 ht htT htu hu2t huT hS
    hsmall hsmall3 hunique
  have hscale := quarticFarCountScale_le_power hN hTp hΔ hThi hfar
    (by linarith only [huT,ht] : u-t ≤ T) hHlo
  calc
    _ ≤ 100000000000000000000*quarticFarCountScale N T (u-t) H := hc
    _ ≤ 100000000000000000000*(8*N^((293:ℝ)/300)) := by gcongr
    _ ≤ N^((1:ℝ)/75)*N^((293:ℝ)/300) := by
      have hh := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ N^((293:ℝ)/300))
      have hp : 0 ≤ N^((293:ℝ)/300) := by positivity
      nlinarith only [hh,hp]
    _ = _ := by rw [←Real.rpow_add hNp]; norm_num

#print axioms quarticMixedPairs_card_far

def positiveShiftedLogPhase (t a x : ℝ) : ℝ :=
  -PintzEndpointResearch.logarithmicTaylorPhase t (a+x)

theorem positiveShiftedLogPhase_coordinate (j : ℕ) (t a x : ℝ) :
    GafniTao.heathBrownDerivativeCoordinate (positiveShiftedLogPhase t a) j x =
      -GafniTao.heathBrownDerivativeCoordinate (PintzEndpointResearch.logarithmicTaylorPhase t) j (a+x) := by
  unfold positiveShiftedLogPhase GafniTao.heathBrownDerivativeCoordinate
  rw [iteratedDeriv_fun_neg,iteratedDeriv_comp_const_add]
  simp only [neg_div]

theorem positiveShiftedLogPhase_contDiffAt (t a : ℝ) {x : ℝ} (hx : 0 < a+x) (k : ℕ) :
    ContDiffAt ℝ k (positiveShiftedLogPhase t a) x := by
  unfold positiveShiftedLogPhase PintzEndpointResearch.logarithmicTaylorPhase
  have hlog : ContDiffAt ℝ k (fun y : ℝ => Real.log (a+y)) x :=
    (contDiffAt_const.add contDiffAt_id).log hx.ne'
  exact (contDiffAt_const.mul hlog).neg

theorem positiveShiftedLogPhase_fifth (t a : ℝ) {x : ℝ} (hx : 0 < a+x) :
    iteratedDeriv 5 (positiveShiftedLogPhase t a) x=12*t/(Real.pi*(a+x)^5) := by
  have hc := positiveShiftedLogPhase_coordinate 5 t a x
  unfold GafniTao.heathBrownDerivativeCoordinate at hc
  have ho := PintzEndpointResearch.logarithmicTaylorPhase_coordinate 4 t hx
  norm_num at ho hc
  rw [ho] at hc
  field_simp at hc ⊢
  nlinarith only [hc]

/-- Translation and conjugation send the actual same-height cell pairs into
the native Heath-Brown finite derivative count, preserving cardinality. -/
theorem quarticMixedPairs_self_le_native_count (S : Finset ℕ) {H H₀ a M : ℕ} {t : ℝ}
    (hH₀ : 0 < H₀) (hH : H₀ ≤ H)
    (hS : ∀ n∈S, a < n ∧ n-a ≤ M) :
    (quarticMixedPairs S H t t).card ≤
      (GafniTao.heathBrownPairCount M 5 H₀ (positiveShiftedLogPhase t a)).card := by
  classical
  let F := quarticMixedPairs S H t t
  let f := fun p : ℕ × ℕ => (p.1-a,p.2-a)
  have hmem p (hp : p∈F) : p.1∈S ∧ p.2∈S ∧
      (quarticLogCell H t p.1 ∩ quarticLogCell H t p.2).Nonempty := by
    obtain ⟨hmem,hover⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn,hm⟩ := Finset.mem_product.mp hmem
    exact ⟨hn,hm,hover⟩
  have hinj : Set.InjOn f (↑F:Set (ℕ×ℕ)) := by
    rintro ⟨n,m⟩ hp ⟨n',m'⟩ hp' he
    have hn := (hS n (hmem _ hp).1).1
    have hm := (hS m (hmem _ hp).2.1).1
    have hn' := (hS n' (hmem _ hp').1).1
    have hm' := (hS m' (hmem _ hp').2.1).1
    have he1 : n-a=n'-a := congrArg Prod.fst he
    have he2 : m-a=m'-a := congrArg Prod.snd he
    have hnn : n=n' := by omega
    have hmm : m=m' := by omega
    simp only [hnn,hmm]
  have hsub : F.image f ⊆ GafniTao.heathBrownPairCount M 5 H₀ (positiveShiftedLogPhase t a) := by
    intro p hp
    obtain ⟨⟨n,m⟩,hnm,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hn,hm,hover⟩ := hmem _ hnm
    have hnb := hS n hn
    have hmb := hS m hm
    have hnp : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hmp : 0 < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hncast : (a:ℝ)+((n-a:ℕ):ℝ)=(n:ℝ) := by
      rw [Nat.cast_sub (by omega)]
      ring
    have hmcast : (a:ℝ)+((m-a:ℕ):ℝ)=(m:ℝ) := by
      rw [Nat.cast_sub (by omega)]
      ring
    apply GafniTao.mem_heathBrownPairCount.mpr
    refine ⟨by dsimp only [f]; omega,hnb.2,by dsimp only [f]; omega,hmb.2,?_⟩
    intro j hj
    have hjb := Finset.mem_Icc.mp hj
    have hjlo : 1 ≤ j := hjb.1
    have hjhi : j ≤ 4 := hjb.2
    let k : Fin 4 := ⟨j-1,by omega⟩
    have hk : (k:ℕ)+1=j := by dsimp only [k]; omega
    have hc := quarticLogCell_mixed_coordinate hnp hmp hover k
    rw [hk] at hc
    have hncoord := PintzEndpointResearch.logarithmicTaylorPhase_coordinate (j-1) t hnp
    have hmcoord := PintzEndpointResearch.logarithmicTaylorPhase_coordinate (j-1) t hmp
    rw [Nat.sub_add_cancel hjlo] at hncoord hmcoord
    change GafniTao.heathBrownDistanceToInteger
      (GafniTao.heathBrownDerivativeCoordinate (positiveShiftedLogPhase t a) j ((n-a:ℕ):ℝ) -
        GafniTao.heathBrownDerivativeCoordinate (positiveShiftedLogPhase t a) j ((m-a:ℕ):ℝ)) ≤ _
    rw [positiveShiftedLogPhase_coordinate,positiveShiftedLogPhase_coordinate,hncast,hmcast]
    unfold GafniTao.heathBrownDerivativeCoordinate
    rw [hncoord,hmcoord,show (-((-1:ℝ)^j*t/(2*Real.pi*(j:ℝ)*(n:ℝ)^j)))-
      (-((-1:ℝ)^j*t/(2*Real.pi*(j:ℝ)*(m:ℝ)^j))) =
      -(((-1:ℝ)^j*t/(2*Real.pi*(j:ℝ)*(n:ℝ)^j))-
        ((-1:ℝ)^j*t/(2*Real.pi*(j:ℝ)*(m:ℝ)^j))) by ring,
      GafniTao.heathBrownDistanceToInteger_neg]
    apply hc.trans
    have hHpos : 0 < (H₀:ℝ) := by exact_mod_cast hH₀
    have hHcast : (H₀:ℝ) ≤ H := by exact_mod_cast hH
    have hh := one_div_le_one_div_of_le (pow_pos hHpos j) (pow_le_pow_left₀ hHpos.le hHcast j)
    simpa only [one_div,div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ) ≤ 2)
  rw [←Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

#print axioms positiveShiftedLogPhase_coordinate
#print axioms positiveShiftedLogPhase_contDiffAt
#print axioms positiveShiftedLogPhase_fifth
#print axioms quarticMixedPairs_self_le_native_count

theorem positiveShiftedLogPhase_fifth_bounds {N t a x : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hxlo : N/4 ≤ a+x) (hxhi : a+x ≤ 3*N) :
    t/(65536*N^5) ≤ iteratedDeriv 5 (positiveShiftedLogPhase t a) x ∧
      iteratedDeriv 5 (positiveShiftedLogPhase t a) x ≤
        268435456*(t/(65536*N^5)) := by
  have hx : 0 < a+x := lt_of_lt_of_le (by positivity) hxlo
  rw [positiveShiftedLogPhase_fifth t a hx]
  have hdenlo : (3:ℝ)*(N/4)^5 ≤ Real.pi*(a+x)^5 := by
    exact mul_le_mul (le_of_lt Real.pi_gt_three)
      (pow_le_pow_left₀ (by positivity) hxlo 5) (by positivity) (by positivity)
  have hdenhi : Real.pi*(a+x)^5 ≤ 4*(3*N)^5 := by
    exact mul_le_mul (le_of_lt Real.pi_lt_four)
      (pow_le_pow_left₀ hx.le hxhi 5) (by positivity) (by positivity)
  constructor
  · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hdenhi ht.le,
      mul_pos ht (pow_pos hN 5)]
  · have hh := (div_le_div_iff₀ (by positivity : 0 < Real.pi*(a+x)^5)
      (by positivity : 0 < 3*(N/4)^5)).mpr
      (mul_le_mul_of_nonneg_left hdenlo (by positivity : 0 ≤ 12*t))
    have he : 12*t/(3*(N/4)^5)=268435456*(t/(65536*N^5)) := by ring
    exact hh.trans_eq he

/-- The native refined count applies to the genuine shifted logarithm.
Only its literal physical scale conditions remain in this finite lemma. -/
theorem quarticMixedPairs_self_le_native_scale (S : Finset ℕ) {H a M : ℕ} {N t : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hM : 1 ≤ M)
    (ha : N/4 ≤ (a:ℝ)) (haM : (a:ℝ)+M ≤ 3*N)
    (hS : ∀ n∈S, a < n ∧ n-a ≤ M)
    (hlambda : t/(65536*N^5) ≤ 1)
    (hsmall : 268435456*(t/(65536*N^5)) ≤ 1/4)
    (hlarge : 8 ≤ GafniTao.heathBrownHChoice 5 268435456 (t/(65536*N^5)))
    (hH : GafniTao.heathBrownHChoice 5 268435456 (t/(65536*N^5)) ≤ H) :
    ((quarticMixedPairs S H t t).card : ℝ) ≤
      GafniTao.heathBrownRefinedCountConstant 5 268435456 *
        (1+268435456*(t/(65536*N^5))*M) *
        ((M:ℝ)+(t/(65536*N^5))^(-(2/(5:ℝ)))) * (1+Real.log M) := by
  have hsmooth (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
      ContDiffAt ℝ 1 (iteratedDeriv j (positiveShiftedLogPhase t a)) x := by
    apply contDiffAt_iteratedDeriv_finite
    exact positiveShiftedLogPhase_contDiffAt t a (by linarith) (1+j)
  have hc (j : ℕ) : ContinuousOn
      (GafniTao.heathBrownDerivativeCoordinate (positiveShiftedLogPhase t a) j)
      (Set.Icc 0 (M:ℝ)) := by
    intro x hx
    exact ((hsmooth j hx.1).continuousAt.div_const _).continuousWithinAt
  have hd (j : ℕ) : DifferentiableOn ℝ
      (GafniTao.heathBrownDerivativeCoordinate (positiveShiftedLogPhase t a) j)
      (Set.Ioo 0 (M:ℝ)) := by
    intro x hx
    exact (((hsmooth j hx.1.le).differentiableAt (by norm_num)).div_const _).differentiableWithinAt
  have hraw : ContinuousOn (iteratedDeriv 4 (positiveShiftedLogPhase t a))
      (Set.Icc 0 (M:ℝ)) := fun _ hx => (hsmooth 4 hx.1).continuousAt.continuousWithinAt
  have hrawd : DifferentiableOn ℝ (iteratedDeriv 4 (positiveShiftedLogPhase t a))
      (Set.Ioo 0 (M:ℝ)) := fun _ hx =>
    ((hsmooth 4 hx.1.le).differentiableAt (by norm_num)).differentiableWithinAt
  have hb : ∀ x∈Set.Ioo (0:ℝ) (M:ℝ),
      t/(65536*N^5) ≤ iteratedDeriv 5 (positiveShiftedLogPhase t a) x ∧
        iteratedDeriv 5 (positiveShiftedLogPhase t a) x ≤ 268435456*(t/(65536*N^5)) := by
    intro x hx
    exact positiveShiftedLogPhase_fifth_bounds hN ht (by linarith [hx.1]) (by linarith [hx.2])
  have hn := GafniTao.heathBrownPairCount_card_cast_le_source_scale (k:=5)
    (A:=268435456) (lambda:=t/(65536*N^5)) (f:=positiveShiftedLogPhase t a)
    (by norm_num) hM (by norm_num) (by positivity) hlambda hsmall hlarge
    (hc 3) (hd 3) (hc 4) (hd 4) hraw hrawd hb
  have hcard := quarticMixedPairs_self_le_native_count S (t:=t) (by omega) hH hS
  exact (Nat.cast_le.mpr hcard).trans hn

#print axioms positiveShiftedLogPhase_fifth_bounds
#print axioms quarticMixedPairs_self_le_native_scale

theorem quarticSelf_native_parameters {H : ℕ} {N T t : ℝ}
    (hN : 1 ≤ N) (hbig : 1099511627776 ≤ N^((1:ℝ)/20))
    (hTlo : N^((18:ℝ)/5) ≤ T) (hThi : T ≤ N^((79:ℝ)/20))
    (ht : T ≤ t) (htT : t ≤ 2*T) (hH : N/T^((1:ℝ)/5) ≤ (H:ℝ)) :
    268435456*(t/(65536*N^5)) ≤ 1/32768 ∧
    268435456*(t/(65536*N^5))*(3*N) ≤ 1 ∧
    (t/(65536*N^5))^(-(2/(5:ℝ))) ≤ N ∧
    8 ≤ GafniTao.heathBrownHChoice 5 268435456 (t/(65536*N^5)) ∧
    GafniTao.heathBrownHChoice 5 268435456 (t/(65536*N^5)) ≤ H := by
  have hNp : 0 < N := by linarith only [hN]
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hTlo
  have htp : 0 < t := hTp.trans_le ht
  let lam : ℝ := t/(65536*N^5)
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hscale : 268435456*lam*N ≤ 8192/N^((1:ℝ)/20) := by
    calc
      _ = 4096*t/N^4 := by dsimp only [lam]; field_simp; ring
      _ ≤ 8192*N^((79:ℝ)/20)/N^4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [htT,hThi]
      _ = _ := by
        rw [←Real.rpow_ofNat,div_eq_mul_inv,←Real.rpow_neg hNp.le,
          mul_assoc,←Real.rpow_add hNp]
        norm_num
        rw [Real.rpow_neg hNp.le,div_eq_mul_inv]
        ring
  have hscale' : 268435456*lam*N ≤ 1/134217728 := by
    apply hscale.trans
    exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hbig])
  have hsmall : 268435456*lam ≤ 1/32768 := by
    have hh : 268435456*lam ≤ 268435456*lam*N :=
      le_mul_of_one_le_right (by positivity) hN
    linarith only [hh,hscale']
  have hmass : 268435456*lam*(3*N) ≤ 1 := by nlinarith only [hscale']
  have hlower : N^(-(2:ℝ)) ≤ lam := by
    have hc : 65536 ≤ N^((3:ℝ)/5) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1:ℝ)/20 ≤ 3/5)
      linarith only [hbig,hh]
    apply (le_div_iff₀ (by positivity : 0 < 65536*N^5)).mpr
    calc
      _ = 65536*N^(3:ℝ) := by
        rw [←Real.rpow_ofNat,mul_left_comm,←Real.rpow_add hNp]
        norm_num
      _ ≤ N^((3:ℝ)/5)*N^(3:ℝ) := by gcongr
      _ = N^((18:ℝ)/5) := by rw [←Real.rpow_add hNp]; norm_num
      _ ≤ t := hTlo.trans ht
  have hinverse : lam^(-(2/(5:ℝ))) ≤ N := by
    calc
      _ ≤ (N^(-(2:ℝ)))^(-(2/(5:ℝ))) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hlower (by norm_num)
      _ = N^((4:ℝ)/5) := by rw [←Real.rpow_mul hNp.le]; norm_num
      _ ≤ N := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN
          (by norm_num : (4:ℝ)/5 ≤ 1)
  have hlarge : 8 ≤ GafniTao.heathBrownHChoice 5 268435456 lam := by
    unfold GafniTao.heathBrownHChoice
    apply Nat.le_floor
    have he : ((1:ℝ)/32768)^(-(1/(5:ℝ)))=8 := by
      have he0 : (1:ℝ)/32768=(8:ℝ)^(-(5:ℝ)) := by norm_num
      rw [he0,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 8)]
      norm_num
    norm_num only [Nat.cast_ofNat]
    rw [←he]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hsmall (by norm_num)
  have hchosen : (GafniTao.heathBrownHChoice 5 268435456 lam : ℝ) ≤ N/T^((1:ℝ)/5) := by
    have hb : T/N^5 ≤ 268435456*lam := by
      dsimp only [lam]
      apply (div_le_iff₀ (by positivity : 0 < N^5)).mpr
      field_simp
      nlinarith only [ht,htp]
    calc
      _ ≤ (268435456*lam)^(-(1/(5:ℝ))) :=
        GafniTao.heathBrownHChoice_cast_le_rpow (by norm_num) hlam
      _ ≤ (T/N^5)^(-(1/(5:ℝ))) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hb (by norm_num)
      _ = _ := by
        rw [Real.div_rpow hTp.le (by positivity),←Real.rpow_natCast,
          ←Real.rpow_mul hNp.le]
        norm_num only [Nat.cast_ofNat]
        rw [Real.rpow_neg_one,
          div_inv_eq_mul,Real.rpow_neg hTp.le]
        ring
  exact ⟨hsmall,hmass,hinverse,hlarge,Nat.cast_le.mp (hchosen.trans hH)⟩

#print axioms quarticSelf_native_parameters

/-- The actual same-height quartic cells have essentially linear overlap
count, uniformly throughout the endpoint's physical height range. -/
theorem quarticMixedPairs_card_self {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T t : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → T ≤ t → t ≤ 2*T →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ((quarticMixedPairs S H t t).card:ℝ) ≤ N^(1+ε) := by
  let K := GafniTao.heathBrownRefinedCountConstant 5 268435456
  have hK : 0 < K := GafniTao.heathBrownRefinedCountConstant_pos 5 (by norm_num)
  have hev : ∀ᶠ N : ℝ in Filter.atTop,
      1099511627776 ≤ N^((1:ℝ)/20) ∧ 48*K ≤ N^ε ∧ 48*K*Real.log N ≤ N^ε := by
    filter_upwards [eventually_const_log_pow_le_rpow 1099511627776 (by norm_num) 0
        (η:=(1:ℝ)/20) (by norm_num),
      eventually_const_log_pow_le_rpow (48*K) (by positivity) 0 hε,
      eventually_const_log_pow_le_rpow (48*K) (by positivity) 1 hε] with N h1 h2 h3
    simpa only [pow_zero,mul_one,pow_one] using And.intro h1 (And.intro h2 h3)
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 4 C,le_max_left _ _,?_⟩
  intro S H N T t hNC hTlo hThi hH ht htT hS
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNC
  have hN : 1 ≤ N := by linarith only [hN4]
  have hNp : 0 < N := by linarith only [hN4]
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hTlo
  have htp : 0 < t := hTp.trans_le ht
  have hconst := hC N ((le_max_right _ _).trans hNC)
  obtain ⟨hsmall,hmass,hinv,hlarge,hchosen⟩ :=
    quarticSelf_native_parameters hN hconst.1 hTlo hThi ht htT hH
  let a : ℕ := ⌊N/2⌋₊
  let M : ℕ := ⌈2*N⌉₊
  have haHi : (a:ℝ) ≤ N/2 := Nat.floor_le (by positivity)
  have haLo : N/2 < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hMLo : 2*N ≤ (M:ℝ) := Nat.le_ceil _
  have hMHi : (M:ℝ) < 2*N+1 := Nat.ceil_lt_add_one (by positivity)
  have hM : 1 ≤ M := by exact_mod_cast (show (1:ℝ) ≤ M by linarith only [hN4,hMLo])
  have hM3 : (M:ℝ) ≤ 3*N := by linarith only [hN4,hMHi]
  have hsupp : ∀ n∈S, a < n ∧ n-a ≤ M := by
    intro n hn
    have hnb := hS n hn
    have han : a < n := by exact_mod_cast (show (a:ℝ) < n by linarith only [haHi,hnb.1,hNp])
    have hnM : n ≤ M := by exact_mod_cast hnb.2.trans hMLo
    exact ⟨han,(Nat.sub_le n a).trans hnM⟩
  have hlam : 0 < t/(65536*N^5) := by positivity
  have hcount := quarticMixedPairs_self_le_native_scale S hNp htp hM
    (by linarith only [haLo,hN4]) (by linarith only [haHi,hMHi,hN4]) hsupp
    (by linarith only [hsmall,hlam]) (by linarith only [hsmall]) hlarge hchosen
  have hmassM : 268435456*(t/(65536*N^5))*(M:ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hM3 (by positivity)).trans hmass
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogM : 1+Real.log (M:ℝ) ≤ 3+Real.log N := by
    have hMp : 0 < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    have hh := Real.log_le_log hMp hM3
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hNp.ne'] at hh
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
    linarith only [hh,h3]
  have hsum : 24*K*(1+Real.log N) ≤ N^ε := by
    nlinarith only [hconst.2.1,hconst.2.2]
  calc
    _ ≤ K*(1+268435456*(t/(65536*N^5))*M)*
        ((M:ℝ)+(t/(65536*N^5))^(-(2/(5:ℝ))))*(1+Real.log M) := hcount
    _ ≤ K*2*(4*N)*(3+Real.log N) := by gcongr <;> linarith only [hmassM,hM3,hinv,hlogM]
    _ ≤ 24*K*N*(1+Real.log N) := by nlinarith only [mul_nonneg (mul_pos hK hNp).le hlogN]
    _ = N*(24*K*(1+Real.log N)) := by ring
    _ ≤ N*N^ε := mul_le_mul_of_nonneg_left hsum hNp.le
    _ = N^(1+ε) := by rw [Real.rpow_add hNp,Real.rpow_one]

#print axioms quarticMixedPairs_card_self

def quarticNuAt (S : Finset ℕ) (H : ℕ) (t : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 5) : ℝ :=
  ∑ n∈S, GafniTao.heathBrownCellIndicator 5 H
    (PintzEndpointResearch.logarithmicTaylorPhase t) n α

def quarticOverlapIndicator (H : ℕ) (t u : ℝ) (p : ℕ×ℕ) :
    GafniTao.HeathBrownCoefficientTorus 5 → ℝ :=
  (quarticLogCell H t p.1 ∩ quarticLogCell H u p.2).indicator (fun _ => 1)

theorem integrable_quarticOverlapIndicator (H : ℕ) (t u : ℝ) (p : ℕ×ℕ) :
    Integrable (quarticOverlapIndicator H t u p) (GafniTao.heathBrownCoefficientMeasure 5) := by
  letI : IsFiniteMeasure (GafniTao.heathBrownCoefficientMeasure 5) := by
    unfold GafniTao.heathBrownCoefficientMeasure
    infer_instance
  exact (integrable_const (1:ℝ)).indicator
    ((GafniTao.measurableSet_heathBrownCoefficientCell 5 _ _ _).inter
      (GafniTao.measurableSet_heathBrownCoefficientCell 5 _ _ _))

theorem quarticNuAt_mul (S : Finset ℕ) (H : ℕ) (t u : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 5) :
    quarticNuAt S H t α*quarticNuAt S H u α =
      ∑ p∈S.product S, quarticOverlapIndicator H t u p α := by
  classical
  unfold quarticNuAt
  rw [Finset.sum_mul_sum,Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  by_cases ha : α∈quarticLogCell H t n
  <;> by_cases hb : α∈quarticLogCell H u m
  <;> simp only [quarticLogCell] at ha hb
  <;> simp [GafniTao.heathBrownCellIndicator,quarticOverlapIndicator,quarticLogCell,ha,hb]

theorem integrable_quarticNuAt_mul (S : Finset ℕ) (H : ℕ) (t u : ℝ) :
    Integrable (fun α => quarticNuAt S H t α*quarticNuAt S H u α)
      (GafniTao.heathBrownCoefficientMeasure 5) := by
  have hh := integrable_finsetSum (S.product S)
    (fun p _ => integrable_quarticOverlapIndicator H t u p)
  apply hh.congr
  filter_upwards [] with α
  exact (quarticNuAt_mul S H t u α).symm

theorem quarticLogCell_measureReal {H : ℕ} (hH : 2 ≤ H) (t : ℝ) (n : ℕ) :
    (GafniTao.heathBrownCoefficientMeasure 5).real (quarticLogCell H t n)=16/(H:ℝ)^10 := by
  unfold GafniTao.heathBrownCoefficientMeasure quarticLogCell
  rw [GafniTao.measureReal_heathBrownCoefficientCell_exact hH]
  norm_num [GafniTao.heathBrownCriticalMoment,div_eq_mul_inv]

theorem integral_quarticNuAt_mul_le (S : Finset ℕ) {H : ℕ} (hH : 2 ≤ H) (t u : ℝ) :
    (∫ α, quarticNuAt S H t α*quarticNuAt S H u α
      ∂(GafniTao.heathBrownCoefficientMeasure 5)) ≤
      ((quarticMixedPairs S H t u).card:ℝ)*(16/(H:ℝ)^10) := by
  classical
  letI : IsFiniteMeasure (GafniTao.heathBrownCoefficientMeasure 5) := by
    unfold GafniTao.heathBrownCoefficientMeasure
    infer_instance
  let A := quarticMixedPairs S H t u
  let μ := GafniTao.heathBrownCoefficientMeasure 5
  let v : ℝ := 16/(H:ℝ)^10
  have hint (p : ℕ×ℕ) : (∫ α, quarticOverlapIndicator H t u p α ∂μ) =
      μ.real (quarticLogCell H t p.1 ∩ quarticLogCell H u p.2) :=
    integral_indicator_one
      ((GafniTao.measurableSet_heathBrownCoefficientCell 5 _ _ _).inter
        (GafniTao.measurableSet_heathBrownCoefficientCell 5 _ _ _))
  have hterm (p : ℕ×ℕ) (hp : p∈S.product S) :
      (∫ α, quarticOverlapIndicator H t u p α ∂μ) ≤ if p∈A then v else 0 := by
    rw [hint]
    by_cases hover : (quarticLogCell H t p.1 ∩ quarticLogCell H u p.2).Nonempty
    · have hpA : p∈A := Finset.mem_filter.mpr ⟨hp,hover⟩
      rw [if_pos hpA]
      exact (measureReal_mono Set.inter_subset_left).trans_eq (quarticLogCell_measureReal hH t p.1)
    · have hpA : p∉A := fun hh => hover (Finset.mem_filter.mp hh).2
      rw [if_neg hpA,Set.not_nonempty_iff_eq_empty.mp hover]
      simp
  have hAS : A ⊆ S.product S := fun _ hp => (Finset.mem_filter.mp hp).1
  simp_rw [quarticNuAt_mul]
  rw [integral_finsetSum _ (fun p _ => integrable_quarticOverlapIndicator H t u p)]
  calc
    _ ≤ ∑ p∈S.product S, (if p∈A then v else 0) := Finset.sum_le_sum hterm
    _ = (A.card:ℝ)*v := by
      rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.inter_eq_right.mpr hAS,
        Finset.sum_const,nsmul_eq_mul]

theorem quarticNuAt_nonneg (S : Finset ℕ) (H : ℕ) (t : ℝ)
    (α : GafniTao.HeathBrownCoefficientTorus 5) : 0 ≤ quarticNuAt S H t α :=
  Finset.sum_nonneg (fun n _ => GafniTao.heathBrownCellIndicator_nonneg 5 H n _ α)

theorem integrable_quarticNuAt (S : Finset ℕ) (H : ℕ) (t : ℝ) :
    Integrable (quarticNuAt S H t) (GafniTao.heathBrownCoefficientMeasure 5) :=
  integrable_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator 5 H n _)

theorem integral_quarticNuAt (S : Finset ℕ) {H : ℕ} (hH : 2 ≤ H) (t : ℝ) :
    (∫ α, quarticNuAt S H t α ∂(GafniTao.heathBrownCoefficientMeasure 5)) =
      (S.card:ℝ)*(16/(H:ℝ)^10) := by
  unfold quarticNuAt
  rw [integral_finsetSum _ (fun n _ => GafniTao.integrable_heathBrownCellIndicator 5 H n _)]
  simp_rw [GafniTao.integral_heathBrownCellIndicator]
  change (∑ n∈S, (GafniTao.heathBrownCoefficientMeasure 5).real (quarticLogCell H t n)) = _
  simp_rw [quarticLogCell_measureReal hH t]
  rw [Finset.sum_const,nsmul_eq_mul]

#print axioms integrable_quarticOverlapIndicator
#print axioms quarticNuAt_mul
#print axioms integrable_quarticNuAt_mul
#print axioms quarticLogCell_measureReal
#print axioms integral_quarticNuAt_mul_le
#print axioms quarticNuAt_nonneg
#print axioms integrable_quarticNuAt
#print axioms integral_quarticNuAt

theorem integral_quarticNuAt_mul_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T t u : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → (H:ℝ) ≤ N → 2 ≤ H →
      T ≤ t → t ≤ 2*T → T ≤ u → u ≤ 2*T →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      (∫ α, quarticNuAt S H t α*quarticNuAt S H u α
        ∂(GafniTao.heathBrownCoefficientMeasure 5)) ≤
      ((if |t-u| ≤ N^((18:ℝ)/5) then N^(1+ε) else 0)+N^((99:ℝ)/100))*(16/(H:ℝ)^10) := by
  classical
  obtain ⟨C₀,hC₀,hself⟩ := quarticMixedPairs_card_self hε
  obtain ⟨C₁,_,hfar⟩ := quarticMixedPairs_card_far
  refine ⟨max C₀ C₁,hC₀.trans (le_max_left _ _),?_⟩
  intro S H N T t u hNC hTlo hThi hHlo hHhi hH ht htT hu huT hS
  have hN : 0 < N := by linarith [(le_max_left C₀ C₁).trans hNC]
  let μ := GafniTao.heathBrownCoefficientMeasure 5
  let v : ℝ := 16/(H:ℝ)^10
  by_cases hnear : |t-u| ≤ N^((18:ℝ)/5)
  · rw [if_pos hnear]
    have hst : (∫ α, quarticNuAt S H t α*quarticNuAt S H t α ∂μ) ≤ N^(1+ε)*v :=
      (integral_quarticNuAt_mul_le S hH t t).trans
        (mul_le_mul_of_nonneg_right
          (hself S H N T t ((le_max_left _ _).trans hNC) hTlo hThi hHlo ht htT hS) (by positivity))
    have hsu : (∫ α, quarticNuAt S H u α*quarticNuAt S H u α ∂μ) ≤ N^(1+ε)*v :=
      (integral_quarticNuAt_mul_le S hH u u).trans
        (mul_le_mul_of_nonneg_right
          (hself S H N T u ((le_max_left _ _).trans hNC) hTlo hThi hHlo hu huT hS) (by positivity))
    have hh := integral_mono (integrable_quarticNuAt_mul S H t u)
      (((integrable_quarticNuAt_mul S H t t).add (integrable_quarticNuAt_mul S H u u)).div_const 2)
      (fun α => show quarticNuAt S H t α*quarticNuAt S H u α ≤
        (quarticNuAt S H t α*quarticNuAt S H t α+quarticNuAt S H u α*quarticNuAt S H u α)/2
        by nlinarith only [sq_nonneg (quarticNuAt S H t α-quarticNuAt S H u α)])
    simp only [Pi.add_apply] at hh
    rw [integral_div,integral_add (integrable_quarticNuAt_mul S H t t)
      (integrable_quarticNuAt_mul S H u u)] at hh
    have hp : 0 ≤ N^((99:ℝ)/100)*v := by dsimp only [v]; positivity
    change (∫ α, quarticNuAt S H t α*quarticNuAt S H u α ∂μ) ≤ _ at hh ⊢
    change (∫ α, quarticNuAt S H t α*quarticNuAt S H u α ∂μ) ≤ (N^(1+ε)+N^((99:ℝ)/100))*v
    nlinarith only [hh,hst,hsu,hp]
  · rw [if_neg hnear,zero_add]
    have hgap : N^((18:ℝ)/5) < |t-u| := lt_of_not_ge hnear
    rcases le_total t u with htu | hut
    · have hfar' : N^((18:ℝ)/5) ≤ u-t := by
        rw [abs_of_nonpos (sub_nonpos.mpr htu)] at hgap
        linarith only [hgap]
      exact (integral_quarticNuAt_mul_le S hH t u).trans
        (mul_le_mul_of_nonneg_right
          (hfar S H N T t u ((le_max_right _ _).trans hNC) hTlo hThi hHlo hHhi ht htT hu huT hfar' hS)
          (by positivity))
    · have hfar' : N^((18:ℝ)/5) ≤ t-u := by
        rw [abs_of_nonneg (sub_nonneg.mpr hut)] at hgap
        exact hgap.le
      simp_rw [mul_comm (quarticNuAt S H t _) (quarticNuAt S H u _)]
      exact (integral_quarticNuAt_mul_le S hH u t).trans
        (mul_le_mul_of_nonneg_right
          (hfar S H N T u t ((le_max_right _ _).trans hNC) hTlo hThi hHlo hHhi hu huT ht htT hfar' hS)
          (by positivity))

/-- Fixing one difference and the first coordinate of another leaves at
most one near difference. Repeated differences are not discarded. -/
theorem separated_difference_near_card (W : Finset ℝ) (E : Finset (ℝ×ℝ)) {L : ℝ}
    (hE : E ⊆ W.product W)
    (hsep : (W:Set ℝ).Pairwise (fun x y => 2*L < |x-y|)) (t : ℝ) :
    (E.filter (fun p => |t-(p.2-p.1)| ≤ L)).card ≤ W.card := by
  classical
  let A := E.filter (fun p => |t-(p.2-p.1)| ≤ L)
  have hinj : Set.InjOn Prod.fst (↑A : Set (ℝ×ℝ)) := by
    intro p hp q hq he
    have hpE := Finset.mem_filter.mp hp
    have hqE := Finset.mem_filter.mp hq
    have hpW := Finset.mem_product.mp (hE hpE.1)
    have hqW := Finset.mem_product.mp (hE hqE.1)
    apply Prod.ext he
    by_contra hne
    have hh := hsep hpW.2 hqW.2 hne
    have hpabs := abs_le.mp hpE.2
    have hqabs := abs_le.mp hqE.2
    have hclose : |p.2-q.2| ≤ 2*L := by
      apply abs_le.mpr
      constructor <;> linarith only [hpabs.1,hpabs.2,hqabs.1,hqabs.2,he]
    exact (not_lt_of_ge hclose) hh
  have hsub : A.image Prod.fst ⊆ W := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_product.mp (hE (Finset.mem_filter.mp hp).1)).1
  rw [←Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

theorem difference_near_card_le_local (W : Finset ℝ) (E : Finset (ℝ×ℝ)) {L B : ℝ}
    (hE : E ⊆ W.product W)
    (hlocal : ∀ x : ℝ, ((W.filter (fun y => |x-y| ≤ L)).card:ℝ) ≤ B) (t : ℝ) :
    ((E.filter (fun p => |t-(p.2-p.1)| ≤ L)).card:ℝ) ≤ (W.card:ℝ)*B := by
  classical
  let Q (x : ℝ) := W.filter (fun y => |(t+x)-y| ≤ L)
  let F (x : ℝ) := (Q x).image (fun y => (x,y))
  have hsub : E.filter (fun p => |t-(p.2-p.1)| ≤ L) ⊆ W.biUnion F := by
    intro p hp
    have hpE := Finset.mem_filter.mp hp
    have hpW := Finset.mem_product.mp (hE hpE.1)
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hpW.1,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2,Finset.mem_filter.mpr ⟨hpW.2,?_⟩,rfl⟩
    simpa only [show t+p.1-p.2=t-(p.2-p.1) by ring] using hpE.2
  have hcard : ((E.filter (fun p => |t-(p.2-p.1)| ≤ L)).card:ℝ) ≤
      ∑ x∈W, ((F x).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  calc
    _ ≤ ∑ x∈W, ((F x).card:ℝ) := hcard
    _ ≤ ∑ x∈W, B := Finset.sum_le_sum (fun x _ =>
      (Nat.cast_le.mpr (Finset.card_image_le)).trans (hlocal (t+x)))
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

#print axioms difference_near_card_le_local

def quarticDifferenceNu (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ))
    (α : GafniTao.HeathBrownCoefficientTorus 5) : ℝ :=
  ∑ p∈E, quarticNuAt S H (p.2-p.1) α

theorem quarticDifferenceNu_sq (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ))
    (α : GafniTao.HeathBrownCoefficientTorus 5) :
    (quarticDifferenceNu S H E α)^2 =
      ∑ p∈E, ∑ q∈E, quarticNuAt S H (p.2-p.1) α*quarticNuAt S H (q.2-q.1) α := by
  unfold quarticDifferenceNu
  rw [pow_two,Finset.sum_mul_sum]

theorem integrable_quarticDifferenceNu_sq (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ)) :
    Integrable (fun α => (quarticDifferenceNu S H E α)^2) (GafniTao.heathBrownCoefficientMeasure 5) := by
  have hh := integrable_finsetSum E (fun p _ => integrable_finsetSum E
    (fun q _ => integrable_quarticNuAt_mul S H (p.2-p.1) (q.2-q.1)))
  apply hh.congr
  filter_upwards [] with α
  exact (quarticDifferenceNu_sq S H E α).symm

/-- The genuine difference ensemble has a cubic near contribution and a
quartic far contribution with a power saving. -/
theorem integral_quarticDifferenceNu_sq_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → (H:ℝ) ≤ N → 2 ≤ H →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y => |x-y| ≤ N^((18:ℝ)/5))).card:ℝ) ≤ N^((11:ℝ)/200)) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      (∫ α, (quarticDifferenceNu S H E α)^2 ∂(GafniTao.heathBrownCoefficientMeasure 5)) ≤
        ((W.card:ℝ)^3*N^((211:ℝ)/200+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*(16/(H:ℝ)^10) := by
  classical
  obtain ⟨C,hC,hpair⟩ := integral_quarticNuAt_mul_uniform hε
  refine ⟨C,hC,?_⟩
  intro S H N T hNC hTlo hThi hHlo hHhi hH hS W E hE hlocal hheight
  have hNp : 0 < N := by linarith only [hC,hNC]
  let v : ℝ := 16/(H:ℝ)^10
  have hEc : (E.card:ℝ) ≤ (W.card:ℝ)^2 := by
    have hh := Finset.card_le_card hE
    rw [Finset.product_eq_sprod,Finset.card_product] at hh
    exact_mod_cast (show E.card ≤ W.card^2 by simpa only [pow_two] using hh)
  have hrow (p : ℝ×ℝ) (hp : p∈E) :
      (∑ q∈E, (∫ α, quarticNuAt S H (p.2-p.1) α*quarticNuAt S H (q.2-q.1) α
        ∂(GafniTao.heathBrownCoefficientMeasure 5))) ≤
        ((W.card:ℝ)*N^((211:ℝ)/200+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := by
    have hnear := difference_near_card_le_local W E hE hlocal (p.2-p.1)
    calc
      _ ≤ ∑ q∈E, ((if |(p.2-p.1)-(q.2-q.1)| ≤ N^((18:ℝ)/5)
          then N^(1+ε) else 0)+N^((99:ℝ)/100))*v := by
        apply Finset.sum_le_sum
        intro q hq
        exact hpair S H N T _ _ hNC hTlo hThi hHlo hHhi hH
          (hheight p hp).1 (hheight p hp).2 (hheight q hq).1 (hheight q hq).2 hS
      _ = (((E.filter (fun q => |(p.2-p.1)-(q.2-q.1)| ≤ N^((18:ℝ)/5))).card:ℝ)*
          N^(1+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := by
        rw [←Finset.sum_mul,Finset.sum_add_distrib,←Finset.sum_filter]
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (((W.card:ℝ)*N^((11:ℝ)/200))*N^(1+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := by gcongr
      _ = _ := by
        have he : N^((11:ℝ)/200)*N^(1+ε)=N^((211:ℝ)/200+ε) := by
          rw [←Real.rpow_add hNp]
          congr 1
          ring
        simp only [mul_assoc,he]
  simp_rw [quarticDifferenceNu_sq]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum E
    (fun q _ => integrable_quarticNuAt_mul S H (p.2-p.1) (q.2-q.1)))]
  simp_rw [integral_finsetSum E (fun (q : ℝ×ℝ) _ => integrable_quarticNuAt_mul S H _ (q.2-q.1))]
  calc
    _ ≤ ∑ _p∈E, ((W.card:ℝ)*N^((211:ℝ)/200+ε)+(E.card:ℝ)*N^((99:ℝ)/100))*v := Finset.sum_le_sum hrow
    _ = ((E.card:ℝ)*(W.card:ℝ)*N^((211:ℝ)/200+ε)+(E.card:ℝ)^2*N^((99:ℝ)/100))*v := by
      rw [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ ((W.card:ℝ)^2*(W.card:ℝ)*N^((211:ℝ)/200+ε)+((W.card:ℝ)^2)^2*N^((99:ℝ)/100))*v := by gcongr
    _ = _ := by dsimp only [v]; ring

#print axioms integral_quarticNuAt_mul_uniform
#print axioms separated_difference_near_card
#print axioms quarticDifferenceNu_sq
#print axioms integrable_quarticDifferenceNu_sq
#print axioms integral_quarticDifferenceNu_sq_uniform

theorem quarticDifferenceNu_nonneg (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ))
    (α : GafniTao.HeathBrownCoefficientTorus 5) : 0 ≤ quarticDifferenceNu S H E α :=
  Finset.sum_nonneg (fun p _ => quarticNuAt_nonneg S H (p.2-p.1) α)

theorem integrable_quarticDifferenceNu (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ)) :
    Integrable (quarticDifferenceNu S H E) (GafniTao.heathBrownCoefficientMeasure 5) :=
  integrable_finsetSum E (fun p _ => integrable_quarticNuAt S H (p.2-p.1))

theorem measurable_quarticDifferenceNu (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ)) :
    Measurable (quarticDifferenceNu S H E) := by
  unfold quarticDifferenceNu quarticNuAt
  exact Finset.measurable_sum E (fun p _ => Finset.measurable_sum S
    (fun n _ => GafniTao.measurable_heathBrownCellIndicator 5 H n
      (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1))))

theorem integral_quarticDifferenceNu (S : Finset ℕ) {H : ℕ} (hH : 2 ≤ H) (E : Finset (ℝ×ℝ)) :
    (∫ α, quarticDifferenceNu S H E α ∂(GafniTao.heathBrownCoefficientMeasure 5)) =
      (E.card:ℝ)*(S.card:ℝ)*(16/(H:ℝ)^10) := by
  unfold quarticDifferenceNu
  rw [integral_finsetSum E (fun p _ => integrable_quarticNuAt S H (p.2-p.1))]
  simp_rw [integral_quarticNuAt S hH]
  rw [Finset.sum_const,nsmul_eq_mul,mul_assoc]

def quarticIntegratedWeyl (S : Finset ℕ) (H : ℕ) (E : Finset (ℝ×ℝ)) (Q : ℕ) : ENNReal :=
  ∫⁻ α : GafniTao.HeathBrownCoefficientTorus 5,
    ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 5 Q α‖*
      ENNReal.ofReal (quarticDifferenceNu S H E α) ∂(GafniTao.heathBrownCoefficientMeasure 5)

def quarticJointMajorant (S : Finset ℕ) (H : ℕ) (W : Finset ℝ) (E : Finset (ℝ×ℝ)) (N ε : ℝ) : ℝ :=
  (GafniTao.fordVinogradovMomentNat 10 4 H : ℝ)^((1:ℝ)/20)*
    (((W.card:ℝ)^3*N^((211:ℝ)/200+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*(16/(H:ℝ)^10))^((1:ℝ)/20)*
    ((E.card:ℝ)*(S.card:ℝ)*(16/(H:ℝ)^10))^((9:ℝ)/10)

theorem quartic_joint_weyl_mean {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → (H:ℝ) ≤ N → 2 ≤ H →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y => |x-y| ≤ N^((18:ℝ)/5))).card:ℝ) ≤ N^((11:ℝ)/200)) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      ∀ Q : ℕ, Q ≤ H → quarticIntegratedWeyl S H E Q ≤ ENNReal.ofReal (quarticJointMajorant S H W E N ε) := by
  obtain ⟨C,hC,hsecond⟩ := integral_quarticDifferenceNu_sq_uniform hε
  refine ⟨C,hC,?_⟩
  intro S H N T hNC hTlo hThi hHlo hHhi hH hS W E hE hlocal hheight Q hQ
  have hNp : 0 < N := by linarith only [hC,hNC]
  let μ := GafniTao.heathBrownCoefficientMeasure 5
  let A : GafniTao.HeathBrownCoefficientTorus 5 → ENNReal :=
    fun α => ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 5 Q α‖
  let B : GafniTao.HeathBrownCoefficientTorus 5 → ENNReal :=
    fun α => ENNReal.ofReal (quarticDifferenceNu S H E α)
  have hA : AEMeasurable A μ :=
    (ENNReal.continuous_ofReal.comp (GafniTao.continuous_fordVinogradovWeylSum 4 Q).norm).aemeasurable
  have hB : AEMeasurable B μ := (integrable_quarticDifferenceNu S H E).aemeasurable.ennreal_ofReal
  have hholder := GafniTao.heathBrown_lintegral_mul_le_three_moments hA hB (by norm_num : 1 ≤ (10:ℕ))
  have hAI : (∫⁻ α, A α^20 ∂μ) = (GafniTao.fordVinogradovMomentNat 10 4 Q : ENNReal) :=
    GafniTao.ford_vinogradov_lintegral_mean_eq 10 4 Q
  have hBI : (∫⁻ α, B α ∂μ) = ENNReal.ofReal ((E.card:ℝ)*(S.card:ℝ)*(16/(H:ℝ)^10)) := by
    rw [←integral_quarticDifferenceNu S hH E]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_quarticDifferenceNu S H E)
      (Filter.Eventually.of_forall (quarticDifferenceNu_nonneg S H E))).symm
  have hBII : (∫⁻ α, B α^2 ∂μ) ≤ ENNReal.ofReal
      (((W.card:ℝ)^3*N^((211:ℝ)/200+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*(16/(H:ℝ)^10)) := by
    calc
      _ = ∫⁻ α, ENNReal.ofReal ((quarticDifferenceNu S H E α)^2) ∂μ := by
        apply lintegral_congr
        intro α
        exact (ENNReal.ofReal_pow (quarticDifferenceNu_nonneg S H E α) 2).symm
      _ = ENNReal.ofReal (∫ α, (quarticDifferenceNu S H E α)^2 ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_quarticDifferenceNu_sq S H E)
          (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hsecond S H N T hNC hTlo hThi hHlo hHhi hH hS W E hE hlocal hheight)
  have hmono : (GafniTao.fordVinogradovMomentNat 10 4 Q : ENNReal) ≤
      (GafniTao.fordVinogradovMomentNat 10 4 H : ENNReal) := by
    exact_mod_cast GafniTao.fordVinogradovMomentNat_mono 10 4 hQ
  norm_num at hholder
  rw [hAI,hBI] at hholder
  have hmajor : ENNReal.ofReal (quarticJointMajorant S H W E N ε) =
      (GafniTao.fordVinogradovMomentNat 10 4 H : ENNReal)^((1:ℝ)/20)*
        ENNReal.ofReal (((W.card:ℝ)^3*N^((211:ℝ)/200+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*(16/(H:ℝ)^10))^((1:ℝ)/20)*
        ENNReal.ofReal ((E.card:ℝ)*(S.card:ℝ)*(16/(H:ℝ)^10))^((9:ℝ)/10) := by
    unfold quarticJointMajorant
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity)]
    rw [←ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ←ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ←ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),ENNReal.ofReal_natCast]
  apply hholder.trans
  rw [hmajor]
  gcongr

#print axioms quarticDifferenceNu_nonneg
#print axioms integrable_quarticDifferenceNu
#print axioms measurable_quarticDifferenceNu
#print axioms integral_quarticDifferenceNu
#print axioms quartic_joint_weyl_mean

theorem quartic_joint_cellwise_le (S : Finset ℕ) (E : Finset (ℝ×ℝ))
    {H : ℕ} (hH : 2 ≤ H) {Q : ℕ} (hQ : 1 ≤ Q)
    (hQH : Q ≤ H)
    (α : GafniTao.HeathBrownCoefficientTorus 5) :
    (∑ t ∈ E, ∑ n ∈ S,
      GafniTao.heathBrownCellIndicator 5 (H)
        (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n α *
      ‖GafniTao.heathBrownWeylSum 5 Q
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖) ≤
      ‖GafniTao.heathBrownWeylSum 5 Q α‖*quarticDifferenceNu S H E α+
      (50*Real.pi/(H : ℝ))*
        ∑ j ∈ Finset.Ico 1 Q,
          ‖GafniTao.heathBrownWeylSum 5 j α‖*quarticDifferenceNu S H E α := by
  classical
  let c : ℝ := 50*Real.pi/(H : ℝ)
  let F (j : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum 5 j α‖
  let I (t : ℝ×ℝ) (n : ℕ) : ℝ :=
    GafniTao.heathBrownCellIndicator 5 H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n α
  have hpoint (t : ℝ×ℝ) (n : ℕ) :
      I t n*‖GafniTao.heathBrownWeylSum 5 Q
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖ ≤
        I t n*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) := by
    by_cases hα : α ∈ GafniTao.heathBrownCoefficientCell 5 H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n
    · have hi : I t n = 1 := by simp [I,GafniTao.heathBrownCellIndicator,hα]
      rw [hi,one_mul,one_mul]
      have hh := GafniTao.norm_heathBrown_centerWeyl_le hH hQ hQH hα
      norm_num only [Nat.cast_ofNat] at hh
      have he : 2*Real.pi*(25/(H : ℝ)) = c := by dsimp only [c]; ring
      simpa only [he,F] using hh
    · have hi : I t n = 0 := by simp [I,GafniTao.heathBrownCellIndicator,hα]
      simp only [hi,zero_mul,le_refl]
  calc
    _ ≤ ∑ t ∈ E, ∑ n ∈ S, I t n*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) :=
      Finset.sum_le_sum (fun t _ => Finset.sum_le_sum (fun n _ => hpoint t n))
    _ = (quarticDifferenceNu S H E α)*(F Q+c*∑ j ∈ Finset.Ico 1 Q, F j) := by
      simp_rw [← Finset.sum_mul]
      rfl
    _ = _ := by
      rw [mul_add]
      simp_rw [← Finset.sum_mul]
      dsimp only [c,F]
      ring

#print axioms quartic_joint_cellwise_le

theorem quartic_joint_center_integral (S : Finset ℕ) (E : Finset (ℝ×ℝ))
    {H : ℕ} (hH : 2 ≤ H) {Q : ℕ} (hQ : 1 ≤ Q)
    (hQH : Q ≤ H) :
    ENNReal.ofReal (16/(H : ℝ)^10)*
      (∑ t ∈ E, ∑ n ∈ S,
        ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 5 Q
          (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖) ≤
      quarticIntegratedWeyl S H E Q+
        ENNReal.ofReal (50*Real.pi/(H : ℝ))*
          ∑ j ∈ Finset.Ico 1 Q, quarticIntegratedWeyl S H E j := by
  classical
  let μ := GafniTao.heathBrownCoefficientMeasure 5
  let c : ℝ := 50*Real.pi/(H : ℝ)
  let v : ℝ := 16/(H : ℝ)^10
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  let F (j : ℕ) (α : GafniTao.HeathBrownCoefficientTorus 5) : ENNReal :=
    ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 5 j α‖*
      ENNReal.ofReal (quarticDifferenceNu S H E α)
  let I (t : ℝ×ℝ) (n : ℕ) (α : GafniTao.HeathBrownCoefficientTorus 5) : ℝ :=
    GafniTao.heathBrownCellIndicator 5 H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n α
  let K (t : ℝ×ℝ) (n : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum 5 Q
    (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)‖
  have hI (t : ℝ×ℝ) (n : ℕ) (α : GafniTao.HeathBrownCoefficientTorus 5) : 0 ≤ I t n α :=
    GafniTao.heathBrownCellIndicator_nonneg 5 H n (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) α
  have hK (t : ℝ×ℝ) (n : ℕ) : 0 ≤ K t n := norm_nonneg _
  have hpoint (α : GafniTao.HeathBrownCoefficientTorus 5) :
      (∑ t ∈ E, ∑ n ∈ S, ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n)) ≤
        F Q α+ENNReal.ofReal c*∑ j ∈ Finset.Ico 1 Q, F j α := by
    have hh := ENNReal.ofReal_le_ofReal (quartic_joint_cellwise_le S E hH hQ hQH α)
    change ENNReal.ofReal (∑ t ∈ E, ∑ n ∈ S, I t n α*K t n) ≤ _ at hh
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => Finset.sum_nonneg
      (fun n _ => mul_nonneg (hI t n α) (hK t n)))] at hh
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => mul_nonneg (hI _ n α) (hK _ n)),
      ENNReal.ofReal_mul (hI _ _ α)] at hh
    have hprod (j : ℕ) : 0 ≤ ‖GafniTao.heathBrownWeylSum 5 j α‖*quarticDifferenceNu S H E α :=
      mul_nonneg (norm_nonneg _) (quarticDifferenceNu_nonneg S H E α)
    rw [ENNReal.ofReal_add (hprod Q) (mul_nonneg hc (Finset.sum_nonneg (fun j _ => hprod j))),
      ENNReal.ofReal_mul (norm_nonneg _),ENNReal.ofReal_mul hc,
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hprod j)] at hh
    simp_rw [ENNReal.ofReal_mul (norm_nonneg _)] at hh
    exact hh
  have hcell (t : ℝ×ℝ) (n : ℕ) : μ (GafniTao.heathBrownCoefficientCell 5 H (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n) =
      ENNReal.ofReal v := by
    have hh := GafniTao.measure_heathBrownCoefficientCell_exact (k := 5) hH (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) (n : ℝ)
    simpa only [μ,v,GafniTao.heathBrownCoefficientMeasure,GafniTao.heathBrownCriticalMoment,
      show 5-1 = (4 : ℕ) by norm_num,show 5*4/2 = (10 : ℕ) by norm_num,
      show (2 : ℝ)^4 = 16 by norm_num,div_eq_mul_inv] using hh
  have hmeas (t : ℝ×ℝ) (n : ℕ) : Measurable (fun α => ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n)) :=
    (GafniTao.measurable_heathBrownCellIndicator 5 H n (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1))).ennreal_ofReal.mul measurable_const
  have hleft : (∫⁻ α, ∑ t ∈ E, ∑ n ∈ S,
      ENNReal.ofReal (I t n α)*ENNReal.ofReal (K t n) ∂μ) =
      ENNReal.ofReal v*(∑ t ∈ E, ∑ n ∈ S, ENNReal.ofReal (K t n)) := by
    rw [lintegral_finsetSum E (fun t _ => Finset.measurable_sum S (fun n _ => hmeas t n))]
    simp_rw [lintegral_finsetSum S (fun n _ => hmeas _ n)]
    simp_rw [I,μ,GafniTao.lintegral_heathBrownCellIndicator_mul_const]
    change (∑ t ∈ E, ∑ n ∈ S, μ (GafniTao.heathBrownCoefficientCell 5 H
      (PintzEndpointResearch.logarithmicTaylorPhase (t.2-t.1)) n)*ENNReal.ofReal (K t n)) = _
    simp_rw [hcell,← Finset.mul_sum]
  have hF (j : ℕ) : Measurable (F j) :=
    (ENNReal.continuous_ofReal.comp (GafniTao.continuous_fordVinogradovWeylSum 4 j).norm).measurable.mul
      (measurable_quarticDifferenceNu S H E).ennreal_ofReal
  have hh := lintegral_mono (μ := μ) hpoint
  rw [hleft,lintegral_add_left (hF Q),lintegral_const_mul _
    (Finset.measurable_sum (Finset.Ico 1 Q) (fun j _ => hF j)),
    lintegral_finsetSum (Finset.Ico 1 Q) (fun j _ => hF j)] at hh
  exact hh

#print axioms quartic_joint_center_integral

theorem quartic_joint_center_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → (H:ℝ) ≤ N → 2 ≤ H →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y => |x-y| ≤ N^((18:ℝ)/5))).card:ℝ) ≤ N^((11:ℝ)/200)) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      ∀ Q : ℕ, 1 ≤ Q → Q ≤ H →
      (16/(H:ℝ)^10)*(∑ p∈E, ∑ n∈S, ‖GafniTao.heathBrownWeylSum 5 Q
        (GafniTao.heathBrownCoefficientCenter 5
          (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖) ≤
      (1+50*Real.pi)*quarticJointMajorant S H W E N ε := by
  classical
  obtain ⟨C,hC,hmean⟩ := quartic_joint_weyl_mean hε
  refine ⟨C,hC,?_⟩
  intro S H N T hNC hTlo hThi hHlo hHhi hH hS W E hE hlocal hheight Q hQ hQH
  have hNp : 0 < N := by linarith only [hC,hNC]
  have hHp : 0 < (H:ℝ) := by exact_mod_cast (by omega : 0 < H)
  let v : ℝ := 16/(H:ℝ)^10
  let c : ℝ := 50*Real.pi/(H:ℝ)
  let M : ℝ := quarticJointMajorant S H W E N ε
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hM : 0 ≤ M := by dsimp only [M,quarticJointMajorant]; positivity
  have hI (j : ℕ) (hj : j ≤ H) : quarticIntegratedWeyl S H E j ≤ ENNReal.ofReal M :=
    hmean S H N T hNC hTlo hThi hHlo hHhi hH hS W E hE hlocal hheight j hj
  have htail : (∑ j∈Finset.Ico 1 Q, quarticIntegratedWeyl S H E j) ≤
      (H:ENNReal)*ENNReal.ofReal M := by
    calc
      _ ≤ ∑ _j∈Finset.Ico 1 Q, ENNReal.ofReal M := Finset.sum_le_sum
        (fun j hj => hI j ((Finset.mem_Ico.mp hj).2.le.trans hQH))
      _ = ((Finset.Ico 1 Q).card:ENNReal)*ENNReal.ofReal M := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul_left
        exact_mod_cast (show (Finset.Ico 1 Q).card ≤ H by simp only [Nat.card_Ico]; omega)
  have hh := (quartic_joint_center_integral S E hH hQ hQH).trans
    (add_le_add (hI Q hQH) (mul_le_mul_right htail (ENNReal.ofReal c)))
  let U : ℝ := ∑ p∈E, ∑ n∈S, ‖GafniTao.heathBrownWeylSum 5 Q
    (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have heleft : ENNReal.ofReal (v*U) = ENNReal.ofReal v*
      (∑ p∈E, ∑ n∈S, ENNReal.ofReal ‖GafniTao.heathBrownWeylSum 5 Q
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖) := by
    rw [ENNReal.ofReal_mul hv]
    congr 1
    dsimp only [U]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  change ENNReal.ofReal v*_ ≤ ENNReal.ofReal M+ENNReal.ofReal c*((H:ENNReal)*ENNReal.ofReal M) at hh
  rw [←heleft] at hh
  have hr := ENNReal.toReal_mono
    (show ENNReal.ofReal M+ENNReal.ofReal c*((H:ENNReal)*ENNReal.ofReal M) ≠ ∞ by finiteness) hh
  rw [ENNReal.toReal_ofReal (mul_nonneg hv hU),
    ENNReal.toReal_add (by finiteness) (by finiteness)] at hr
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hM,ENNReal.toReal_ofReal hc,
    ENNReal.toReal_natCast] at hr
  have he : M+c*((H:ℝ)*M)=(1+50*Real.pi)*M := by dsimp only [c]; field_simp
  exact hr.trans_eq he

#print axioms quartic_joint_center_uniform

def quarticLogKernel (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ n∈S, GafniTao.heathBrownPhase (PintzEndpointResearch.logarithmicTaylorPhase t n)

theorem logarithmicTaylorPhase_fifth_norm {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ‖iteratedDeriv 5 (PintzEndpointResearch.logarithmicTaylorPhase t) x‖ = 12*t/(Real.pi*x^5) := by
  have hh := PintzEndpointResearch.logarithmicTaylorPhase_coordinate 4 t hx
  norm_num at hh
  have he : iteratedDeriv 5 (PintzEndpointResearch.logarithmicTaylorPhase t) x = -(12*t/(Real.pi*x^5)) := by
    have he := (div_eq_iff (by norm_num : (120:ℝ) ≠ 0)).mp hh
    calc
      _ = _ := he
      _ = _ := by ring
  rw [he,norm_neg,Real.norm_eq_abs,abs_of_pos (by positivity)]

theorem quartic_shifted_Abel {N T t : ℝ} {n H : ℕ}
    (hN : 0 < N) (hT : 0 < T) (ht : 0 < t) (htT : t ≤ 2*T)
    (hn : N ≤ (n:ℝ)) (hH : 1 ≤ H) :
    ‖∑ h∈Finset.Icc 1 H, GafniTao.heathBrownPhase
      (PintzEndpointResearch.logarithmicTaylorPhase t ((n+h:ℕ):ℝ))‖ ≤
      ‖GafniTao.heathBrownWeylSum 5 H
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖+
      (48*T/N^5*(H:ℝ)^4)*∑ j∈Finset.Ico 1 H, ‖GafniTao.heathBrownWeylSum 5 j
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖ := by
  have hnp : 0 < (n:ℝ) := hN.trans_le hn
  have hsmooth : ContDiffOn ℝ (5:ℕ) (PintzEndpointResearch.logarithmicTaylorPhase t) (Set.Ioi 0) := by
    intro x hx
    have hl : ContDiffAt ℝ (5:ℕ) Real.log x := Real.contDiffAt_log.mpr (ne_of_gt hx)
    exact (contDiffAt_const.mul hl).contDiffWithinAt
  have hsmoothD : ContDiffOn ℝ (4:ℕ) (deriv (PintzEndpointResearch.logarithmicTaylorPhase t)) (Set.Ioi 0) :=
    hsmooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hfat : ContDiffAt ℝ (3:ℕ) (deriv (PintzEndpointResearch.logarithmicTaylorPhase t)) n :=
    (hsmoothD.contDiffAt (Ioi_mem_nhds hnp)).of_le (by norm_num)
  have hfd (x : ℝ) (hx : x∈Set.Icc (1:ℝ) H) :
      HasDerivAt (PintzEndpointResearch.logarithmicTaylorPhase t)
        (deriv (PintzEndpointResearch.logarithmicTaylorPhase t) ((n:ℝ)+x)) ((n:ℝ)+x) := by
    have hnx : 0 < (n:ℝ)+x := by linarith only [hnp,hx.1]
    exact ((hsmooth.contDiffAt (Ioi_mem_nhds hnx)).differentiableAt (by norm_num)).hasDerivAt
  have hfon (x : ℝ) (_hx : x∈Set.Icc (1:ℝ) H) :
      ContDiffOn ℝ (4:ℕ) (deriv (PintzEndpointResearch.logarithmicTaylorPhase t)) (Set.Icc (n:ℝ) ((n:ℝ)+x)) :=
    hsmoothD.mono (fun _ hξ => hnp.trans_le hξ.1)
  have hderiv (x : ℝ) (_hx : x∈Set.Icc (1:ℝ) H) (ξ : ℝ)
      (hξ : ξ∈Set.Ioo (n:ℝ) ((n:ℝ)+x)) :
      ‖iteratedDeriv 5 (PintzEndpointResearch.logarithmicTaylorPhase t) ξ‖ ≤ 24*(T/(Real.pi*N^5)) := by
    have hξp : 0 < ξ := hnp.trans hξ.1
    rw [logarithmicTaylorPhase_fifth_norm ht hξp]
    calc
      _ ≤ 12*(2*T)/(Real.pi*N^5) := by
        apply div_le_div₀ (by positivity) (by linarith only [htT]) (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN.le (hn.trans hξ.1.le) 5) Real.pi_pos.le
      _ = _ := by ring
  have hh := GafniTao.heathBrown_shifted_source_sum_norm_le_partial
    (k:=5) (H:=H) (A:=24) (lambda:=T/(Real.pi*N^5))
    (by norm_num) hH hfat hfd hfon hderiv
  simp only [show (5:ℕ)-1=4 by norm_num,Nat.cast_add] at hh ⊢
  simp_rw [GafniTao.norm_heathBrownWeylSum_center_eq_TaylorPolynomialSum (by norm_num : 1 ≤ (5:ℕ))]
  have hc : 2*Real.pi*(24*(T/(Real.pi*N^5))*(H:ℝ)^4)=48*T/N^5*(H:ℝ)^4 := by field_simp; norm_num
  rw [hc] at hh
  exact hh

theorem quartic_actual_Abel (S : Finset ℕ) {N T t : ℝ} {H : ℕ}
    (hN : 0 < N) (hT : 0 < T) (ht : 0 < t) (htT : t ≤ 2*T)
    (hS : ∀ n∈S, N ≤ (n:ℝ)) (hinterval : ∃ a b : ℕ, S=Finset.Icc a b) (hH : 1 ≤ H) :
    (H:ℝ)*‖quarticLogKernel S t‖ ≤
      (∑ n∈S, ‖GafniTao.heathBrownWeylSum 5 H
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖)+
      (48*T/N^5*(H:ℝ)^4)*(∑ j∈Finset.Ico 1 H, ∑ n∈S, ‖GafniTao.heathBrownWeylSum 5 j
        (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖)+
      (H:ℝ)*((H:ℝ)+1) := by
  classical
  by_cases hempty : S=∅
  · simp only [hempty,quarticLogKernel,Finset.sum_empty,norm_zero,mul_zero,zero_add]
    positivity
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨a,b,habS⟩ := hinterval
  have hab : a ≤ b := by
    obtain ⟨n,hn⟩ := hnonempty
    rw [habS] at hn
    exact (Finset.mem_Icc.mp hn).1.trans (Finset.mem_Icc.mp hn).2
  have ha : 1 ≤ a := by
    have hh := hS a (by rw [habS]; exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩)
    have hap : 0 < a := by exact_mod_cast hN.trans_le hh
    omega
  let U : ℂ := ∑ n∈S, ∑ h∈Finset.Icc 1 H,
    GafniTao.heathBrownPhase (PintzEndpointResearch.logarithmicTaylorPhase t ((n+h:ℕ):ℝ))
  have hboundary : ‖U-(H:ℂ)*quarticLogKernel S t‖ ≤ (H:ℝ)*((H:ℝ)+1) := by
    have hh := PintzEndpointResearch.norm_interval_phase_average_sub_le
      (PintzEndpointResearch.logarithmicTaylorPhase t) ha hab H
    rw [Finset.sum_comm] at hh
    simpa only [U,quarticLogKernel,habS] using hh
  have hentry : (H:ℝ)*‖quarticLogKernel S t‖ ≤ ‖U‖+(H:ℝ)*((H:ℝ)+1) := by
    calc
      _ = ‖(H:ℂ)*quarticLogKernel S t‖ := by rw [norm_mul,Complex.norm_natCast]
      _ = ‖U-(U-(H:ℂ)*quarticLogKernel S t)‖ := by congr 1; ring
      _ ≤ ‖U‖+‖U-(H:ℂ)*quarticLogKernel S t‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hboundary
  let c : ℝ := 48*T/N^5*(H:ℝ)^4
  let F (j n : ℕ) : ℝ := ‖GafniTao.heathBrownWeylSum 5 j
    (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase t) n)‖
  have hsum : ‖U‖ ≤ (∑ n∈S, F H n)+c*(∑ j∈Finset.Ico 1 H, ∑ n∈S, F j n) := by
    calc
      _ ≤ ∑ n∈S, ‖∑ h∈Finset.Icc 1 H, GafniTao.heathBrownPhase
          (PintzEndpointResearch.logarithmicTaylorPhase t ((n+h:ℕ):ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ n∈S, (F H n+c*∑ j∈Finset.Ico 1 H, F j n) :=
        Finset.sum_le_sum (fun n hn => quartic_shifted_Abel hN hT ht htT (hS n hn) hH)
      _ = _ := by
        rw [Finset.sum_add_distrib,←Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
  exact hentry.trans (add_le_add hsum le_rfl)

#print axioms logarithmicTaylorPhase_fifth_norm
#print axioms quartic_shifted_Abel
#print axioms quartic_actual_Abel

theorem quartic_joint_source {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ (S : Finset ℕ) (H : ℕ) (N T : ℝ), C ≤ N →
      N^((18:ℝ)/5) ≤ T → T ≤ N^((79:ℝ)/20) →
      N/T^((1:ℝ)/5) ≤ (H:ℝ) → (H:ℝ) ≤ N → 2 ≤ H →
      (∀ n∈S, N ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*N) →
      (∃ a b : ℕ, S=Finset.Icc a b) →
      ∀ (W : Finset ℝ) (E : Finset (ℝ×ℝ)), E ⊆ W.product W →
      (∀ x : ℝ, ((W.filter (fun y => |x-y| ≤ N^((18:ℝ)/5))).card:ℝ) ≤ N^((11:ℝ)/200)) →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      (16/(H:ℝ)^10)*(H:ℝ)*(∑ p∈E, ‖quarticLogKernel S (p.2-p.1)‖) ≤
        (1+48*T/N^5*(H:ℝ)^5)*(1+50*Real.pi)*quarticJointMajorant S H W E N ε+
        (16/(H:ℝ)^10)*(E.card:ℝ)*(H:ℝ)*((H:ℝ)+1) := by
  classical
  obtain ⟨C,hC,hcenter⟩ := quartic_joint_center_uniform hε
  refine ⟨C,hC,?_⟩
  intro S H N T hNC hTlo hThi hHlo hHhi hH hS hinterval W E hE hlocal hheight
  have hNp : 0 < N := by linarith only [hC,hNC]
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hTlo
  let v : ℝ := 16/(H:ℝ)^10
  let c : ℝ := 48*T/N^5*(H:ℝ)^4
  let M := (1+50*Real.pi)*quarticJointMajorant S H W E N ε
  let A (p : ℝ×ℝ) (j : ℕ) : ℝ := ∑ n∈S, ‖GafniTao.heathBrownWeylSum 5 j
    (GafniTao.heathBrownCoefficientCenter 5 (PintzEndpointResearch.logarithmicTaylorPhase (p.2-p.1)) n)‖
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hM : 0 ≤ M := by dsimp only [M,quarticJointMajorant]; positivity
  have hpartial (j : ℕ) (hj : 1 ≤ j) (hjH : j ≤ H) : v*(∑ p∈E, A p j) ≤ M :=
    hcenter S H N T hNC hTlo hThi hHlo hHhi hH hS W E hE hlocal hheight j hj hjH
  have htail : (∑ j∈Finset.Ico 1 H, v*(∑ p∈E, A p j)) ≤ (H:ℝ)*M := by
    calc
      _ ≤ ∑ _j∈Finset.Ico 1 H, M := Finset.sum_le_sum (fun j hj =>
        hpartial j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2.le)
      _ = ((Finset.Ico 1 H).card:ℝ)*M := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast
        (show (Finset.Ico 1 H).card ≤ H by simp only [Nat.card_Ico]; omega)) hM
  have hsum : (H:ℝ)*(∑ p∈E, ‖quarticLogKernel S (p.2-p.1)‖) ≤
      (∑ p∈E, A p H)+c*(∑ j∈Finset.Ico 1 H, ∑ p∈E, A p j)+
      (E.card:ℝ)*((H:ℝ)*((H:ℝ)+1)) := by
    have hh := Finset.sum_le_sum (fun p hp => quartic_actual_Abel S (H:=H) hNp hTp
      (hTp.trans_le (hheight p hp).1) (hheight p hp).2 (fun n hn => (hS n hn).1) hinterval (by omega))
    change (∑ p∈E, (H:ℝ)*‖quarticLogKernel S (p.2-p.1)‖) ≤
      ∑ p∈E, (A p H+c*(∑ j∈Finset.Ico 1 H, A p j)+(H:ℝ)*((H:ℝ)+1)) at hh
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hh
    rw [Finset.sum_comm (s:=E) (t:=Finset.Ico 1 H) (f:=A)] at hh
    exact hh
  calc
    _ = v*((H:ℝ)*(∑ p∈E, ‖quarticLogKernel S (p.2-p.1)‖)) := by ring
    _ ≤ v*((∑ p∈E, A p H)+c*(∑ j∈Finset.Ico 1 H, ∑ p∈E, A p j)+
        (E.card:ℝ)*((H:ℝ)*((H:ℝ)+1))) := mul_le_mul_of_nonneg_left hsum hv
    _ = v*(∑ p∈E, A p H)+c*(∑ j∈Finset.Ico 1 H, v*(∑ p∈E, A p j))+
        v*(E.card:ℝ)*(H:ℝ)*((H:ℝ)+1) := by rw [←Finset.mul_sum]; ring
    _ ≤ M+c*((H:ℝ)*M)+v*(E.card:ℝ)*(H:ℝ)*((H:ℝ)+1) :=
      add_le_add (add_le_add (hpartial H (by omega) le_rfl) (mul_le_mul_of_nonneg_left htail hc)) le_rfl
    _ = _ := by dsimp only [M,c,v]; ring

theorem quarticJointMajorant_pow (S : Finset ℕ) (H : ℕ) (W : Finset ℝ) (E : Finset (ℝ×ℝ))
    {N ε : ℝ} (hN : 0 ≤ N) :
    (quarticJointMajorant S H W E N ε)^20 =
      (GafniTao.fordVinogradovMomentNat 10 4 H:ℝ)*
        (((W.card:ℝ)^3*N^((211:ℝ)/200+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*(16/(H:ℝ)^10))*
        ((E.card:ℝ)*(S.card:ℝ)*(16/(H:ℝ)^10))^18 := by
  let J := GafniTao.fordVinogradovMomentNat 10 4 H
  let A : ℝ := ((W.card:ℝ)^3*N^((211:ℝ)/200+ε)+(W.card:ℝ)^4*N^((99:ℝ)/100))*(16/(H:ℝ)^10)
  let B : ℝ := (E.card:ℝ)*(S.card:ℝ)*(16/(H:ℝ)^10)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hJpow : ((J:ℝ)^((1:ℝ)/20))^20=J := by
    rw [←Real.rpow_mul_natCast (Nat.cast_nonneg J)]
    norm_num
  have hApow : (A^((1:ℝ)/20))^20=A := by rw [←Real.rpow_mul_natCast hA]; norm_num
  have hBpow : (B^((9:ℝ)/10))^20=B^18 := by rw [←Real.rpow_mul_natCast hB]; norm_num
  change ((J:ℝ)^((1:ℝ)/20)*A^((1:ℝ)/20)*B^((9:ℝ)/10))^20=(J:ℝ)*A*B^18
  rw [mul_pow,mul_pow,hJpow,hApow,hBpow]

#print axioms quartic_joint_source
#print axioms quarticJointMajorant_pow

/-- The local occupancy required by the difference moment comes from
the already proved fourth analytic exponent pair, for the original pattern. -/
theorem quartic_first_endpoint_local_occupancy :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100000 ∧ ∃ C : ℝ, 4 ≤ C ∧
      ∀ P : LargeValuePattern, C ≤ P.N → P.N^(39/40-δ : ℝ) ≤ P.V →
      ∀ x : ℝ, ((P.ordinates.filter (fun y => |x-y| ≤ P.N^((18:ℝ)/5))).card:ℝ) ≤
        P.N^((11:ℝ)/200) := by
  classical
  have hbound : IsLargeValueBound (39/40) (18/5) (1/20) := by
    have hh := pintz_first_endpoint_pair_largeValueBound (18/5)
    norm_num at hh
    exact hh
  obtain ⟨K,hK,δ₀,hδ₀,hcount⟩ := hbound (1/1000) (by norm_num)
  let δ : ℝ := min δ₀ (1/100000)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδle : δ ≤ δ₀ := min_le_left _ _
  have hev : ∀ᶠ N : ℝ in Filter.atTop, K ≤ N^((1:ℝ)/250) ∧ 2 ≤ N^δ₀ := by
    filter_upwards [eventually_const_log_pow_le_rpow K (by linarith only [hK]) 0
        (η:=(1:ℝ)/250) (by norm_num),eventually_const_log_pow_le_rpow 2 (by norm_num) 0 hδ₀]
      with N h1 h2
    simpa only [pow_zero,mul_one] using And.intro h1 h2
  obtain ⟨C,hC⟩ := Filter.eventually_atTop.mp hev
  refine ⟨δ,hδ,min_le_right _ _,max 4 (max K C),le_max_left _ _,?_⟩
  intro P hPN hV x
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hPK : K ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hPN)
  have hconst := hC P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  let L : ℝ := P.N^((18:ℝ)/5)
  have hL : 0 < L := by dsimp only [L]; positivity
  let Q : LargeValuePattern := { P with
    T := 2*L
    T_pos := by positivity
    V := P.N^(39/40-δ : ℝ)
    V_pos := by positivity
    intervalLeft := x-L
    intervalRight := x+L
    ordinates := P.ordinates.filter (fun y => |x-y| ≤ L)
    interval_length := by ring
    ordinates_in_interval := by
      intro y hy
      have hh := abs_le.mp (Finset.mem_filter.mp hy).2
      constructor <;> linarith only [hh.1,hh.2]
    ordinates_oneSeparated := fun y hy z hz hyz =>
      P.ordinates_oneSeparated y (Finset.mem_filter.mp hy).1 z (Finset.mem_filter.mp hz).1 hyz
    large := fun y hy => hV.trans (P.large y (Finset.mem_filter.mp hy).1) }
  have hTlo : Q.N^(18/5-δ₀ : ℝ) ≤ Q.T := by
    change P.N^(18/5-δ₀ : ℝ) ≤ 2*L
    have hh := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (show (18:ℝ)/5-δ₀ ≤ 18/5 by linarith only [hδ₀])
    change P.N^(18/5-δ₀ : ℝ) ≤ L at hh
    linarith only [hh,hL]
  have hThi : Q.T ≤ Q.N^(18/5+δ₀ : ℝ) := by
    change 2*L ≤ P.N^(18/5+δ₀ : ℝ)
    calc
      _ ≤ P.N^δ₀*L := mul_le_mul_of_nonneg_right hconst.2 hL.le
      _ = _ := by dsimp only [L]; rw [←Real.rpow_add hNp]; congr 1; ring
  have hVlo : Q.N^(39/40-δ₀ : ℝ) ≤ Q.V :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδle])
  have hVhi : Q.V ≤ Q.N^(39/40+δ₀ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδ,hδ₀])
  have hh := hcount Q hPK hTlo hThi hVlo hVhi
  change ((P.ordinates.filter (fun y => |x-y| ≤ L)).card:ℝ) ≤ K*P.N^(1/20+1/1000 : ℝ) at hh
  calc
    _ ≤ K*P.N^(1/20+1/1000 : ℝ) := hh
    _ ≤ P.N^((1:ℝ)/250)*P.N^(1/20+1/1000 : ℝ) := by gcongr; exact hconst.1
    _ = _ := by rw [←Real.rpow_add hNp]; norm_num

#print axioms quartic_first_endpoint_local_occupancy

theorem quartic_adaptive_block_scales {N T : ℝ} (hN : 1 < N)
    (hconst : 2 ≤ N^((1:ℝ)/5))
    (hTlo : N^((18:ℝ)/5) ≤ T) (hThi : T ≤ N^((79:ℝ)/20)) :
    let H := Nat.ceil (N/T^((1:ℝ)/5))
    2 ≤ H ∧ (H:ℝ) ≤ N ∧ (H:ℝ) ≤ 2*N^((7:ℝ)/25) ∧
      48*T/N^5*(H:ℝ)^5 ≤ 1536 := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hTlo
  let X : ℝ := N/T^((1:ℝ)/5)
  let H := Nat.ceil X
  have hXlo : N^((21:ℝ)/100) ≤ X := by
    calc
      _ = N/(N^((79:ℝ)/20))^((1:ℝ)/5) := by
        rw [←Real.rpow_mul hNp.le]
        nth_rw 2 [←Real.rpow_one N]
        rw [←Real.rpow_sub hNp]
        norm_num
      _ ≤ X := by dsimp only [X]; gcongr
  have hXhi : X ≤ N^((7:ℝ)/25) := by
    calc
      _ ≤ N/(N^((18:ℝ)/5))^((1:ℝ)/5) := by dsimp only [X]; gcongr
      _ = _ := by
        rw [←Real.rpow_mul hNp.le]
        nth_rw 1 [←Real.rpow_one N]
        rw [←Real.rpow_sub hNp]
        norm_num
  have hX : 1 < X := (Real.one_lt_rpow hN (by norm_num : (0:ℝ) < 21/100)).trans_le hXlo
  have hH : 2 ≤ H := by
    have hh : (1:ℝ) < H := hX.trans_le (Nat.le_ceil X)
    have hh' : 1 < H := by exact_mod_cast hh
    omega
  have hHX : (H:ℝ) ≤ 2*X := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ X by linarith only [hX])
    linarith only [hh,hX]
  have hHhi : (H:ℝ) ≤ 2*N^((7:ℝ)/25) := hHX.trans (by gcongr)
  have hHN : (H:ℝ) ≤ N := by
    calc
      _ ≤ 2*N^((7:ℝ)/25) := hHhi
      _ ≤ N^((1:ℝ)/5)*N^((7:ℝ)/25) := by gcongr
      _ = N^((12:ℝ)/25) := by rw [←Real.rpow_add hNp]; norm_num
      _ ≤ N := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le
          (by norm_num : (12:ℝ)/25 ≤ 1)
  have hXpow : X^5=N^5/T := by
    dsimp only [X]
    rw [div_pow,←Real.rpow_mul_natCast hTp.le]
    norm_num
  have hscale : 48*T/N^5*(H:ℝ)^5 ≤ 1536 := by
    calc
      _ ≤ 48*T/N^5*(2*X)^5 := by gcongr
      _ = 1536 := by rw [mul_pow,hXpow]; field_simp; ring
  exact ⟨hH,hHN,hHhi,hscale⟩

#print axioms quartic_adaptive_block_scales

set_option maxHeartbeats 1200000 in
/-- Critical twentieth moment for actual dyadic Gram differences of the
original pattern. The local occupancy hypothesis is discharged internally. -/
theorem quartic_first_endpoint_kernel_moment :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100000 ∧ ∃ C : ℝ, 4 ≤ C ∧ ∃ K : ℝ, 0 < K ∧
      ∀ P : LargeValuePattern, C ≤ P.N → P.N^(39/40-δ : ℝ) ≤ P.V →
      ∀ T : ℝ, P.N^((18:ℝ)/5) ≤ T → T ≤ P.N^((79:ℝ)/20) →
      ∀ E : Finset (ℝ×ℝ), E ⊆ P.ordinates.product P.ordinates →
      (∀ p∈E, T ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*T) →
      (∑ p∈E, ‖quarticLogKernel P.indices (p.2-p.1)‖)^20 ≤
        K*P.N^((1:ℝ)/10000)*
          ((P.ordinates.card:ℝ)^39*P.N^(3811/200+1/10000 : ℝ)+
            (P.ordinates.card:ℝ)^40*P.N^((1899:ℝ)/100)) := by
  obtain ⟨δ,hδ,hδle,C₀,hC₀,hlocal⟩ := quartic_first_endpoint_local_occupancy
  obtain ⟨C₁,_,hsource⟩ := quartic_joint_source (ε:=(1:ℝ)/10000) (by norm_num)
  obtain ⟨C₂,hC₂⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow 2 (by norm_num) 0 (η:=(1:ℝ)/5) (by norm_num))
  obtain ⟨J₀,hJ₀,hvmvt⟩ := GafniTao.heathBrownVMVTMainConjecture_native.critical
    (by norm_num : 2 ≤ (5:ℕ)) (by norm_num : (0:ℝ) < 1/10000)
  let D : ℝ := 1537*(1+50*Real.pi)
  let K₀ : ℝ := D^20*J₀/16*2^18
  let K : ℝ := 2^19*(K₀+3^20)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hK₀ : 0 < K₀ := by dsimp only [K₀]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨δ,hδ,hδle,max C₀ (max C₁ C₂),hC₀.trans (le_max_left _ _),K,hK,?_⟩
  intro P hPN hV T hTlo hThi E hE hheight
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hTp : 0 < T := (Real.rpow_pos_of_pos hNp _).trans_le hTlo
  have hconst : 2 ≤ P.N^((1:ℝ)/5) := by
    simpa only [pow_zero,mul_one] using hC₂ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  let H := Nat.ceil (P.N/T^((1:ℝ)/5))
  let v : ℝ := 16/(H:ℝ)^10
  let R : ℝ := P.ordinates.card
  let I : ℝ := P.indices.card
  let A : ℝ := E.card
  let B : ℝ := R^3*P.N^(211/200+1/10000 : ℝ)+R^4*P.N^((99:ℝ)/100)
  let F : ℝ := R^39*P.N^(3811/200+1/10000 : ℝ)+R^40*P.N^((1899:ℝ)/100)
  let U : ℝ := ∑ p∈E, ‖quarticLogKernel P.indices (p.2-p.1)‖
  let M := quarticJointMajorant P.indices H P.ordinates E P.N (1/10000)
  let J := GafniTao.fordVinogradovMomentNat 10 4 H
  have hR : 0 ≤ R := Nat.cast_nonneg _
  have hI : 0 ≤ I := Nat.cast_nonneg _
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hU : 0 ≤ U := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 0 ≤ M := by dsimp only [M,quarticJointMajorant]; positivity
  obtain ⟨hH,hHN,hHscale,hTscale⟩ := quartic_adaptive_block_scales P.one_lt_N hconst hTlo hThi
  have hHp : 0 < (H:ℝ) := by exact_mod_cast (by omega : 0 < H)
  have hv : 0 < v := by dsimp only [v]; positivity
  have hAI : A ≤ R^2 := by
    dsimp only [A,R]
    have hh := Finset.card_le_card hE
    rw [Finset.product_eq_sprod,Finset.card_product] at hh
    exact_mod_cast (show E.card ≤ P.ordinates.card^2 by simpa only [pow_two] using hh)
  have hIN : I ≤ 2*P.N := P.indices_card_cast_le_two_mul_N
  have hsource' := hsource P.indices H P.N T
    ((le_max_left _ _).trans ((le_max_right _ _).trans hPN)) hTlo hThi (Nat.le_ceil _)
    hHN hH (fun n hn => (P.mem_indices_iff n).mp hn)
    ⟨P.scale,2*P.scale,P.indices_eq_dyadicInterval⟩ P.ordinates E hE
    (hlocal P ((le_max_left _ _).trans hPN) hV) hheight
  have hmain : v*(H:ℝ)*U ≤ D*M+v*A*(H:ℝ)*((H:ℝ)+1) := by
    apply hsource'.trans
    change (1+48*T/P.N^5*(H:ℝ)^5)*(1+50*Real.pi)*M+_ ≤ D*M+_
    apply add_le_add _ le_rfl
    dsimp only [D]
    gcongr
    linarith only [hTscale]
  have hentry : U ≤ D*M/(v*(H:ℝ))+A*((H:ℝ)+1) := by
    apply (mul_le_mul_iff_left₀ (mul_pos hv hHp)).mp
    convert hmain using 1 <;> field_simp
  have hMpow : M^20=(J:ℝ)*(B*v)*(A*I*v)^18 := quarticJointMajorant_pow _ _ _ _ hNp.le
  have hJbound : (J:ℝ) ≤ J₀*(H:ℝ)^(10+1/10000 : ℝ) := by
    have hh := GafniTao.heathBrownCriticalMoment_bound (by norm_num : 2 ≤ (5:ℕ)) (by omega : 1 ≤ H) hvmvt
    norm_num only [GafniTao.heathBrownCriticalMoment] at hh
    simpa only [show (10+1/10000 : ℝ)=100001/10000 by norm_num] using hh
  have hcoef : D^20*(J:ℝ)/(v*(H:ℝ)^20) ≤ (D^20*J₀/16)*P.N^((1:ℝ)/10000) := by
    calc
      _ ≤ D^20*(J₀*(H:ℝ)^(10+1/10000 : ℝ))/(v*(H:ℝ)^20) := by gcongr
      _ = (D^20*J₀/16)*(H:ℝ)^((1:ℝ)/10000) := by
        rw [Real.rpow_add hHp,Real.rpow_ofNat]
        dsimp only [v]
        field_simp
      _ ≤ _ := by gcongr
  have hfarPow : (D*M/(v*(H:ℝ)))^20 ≤ K₀*P.N^((1:ℝ)/10000)*F := by
    calc
      _ = (D^20*(J:ℝ)/(v*(H:ℝ)^20))*(A^18*I^18*B) := by
        rw [div_pow,mul_pow,hMpow]
        field_simp
      _ ≤ ((D^20*J₀/16)*P.N^((1:ℝ)/10000))*((R^2)^18*(2*P.N)^18*B) := by gcongr
      _ = K₀*P.N^((1:ℝ)/10000)*F := by
        have he1 : P.N^18*P.N^(211/200+1/10000 : ℝ)=P.N^(3811/200+1/10000 : ℝ) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hNp]
          congr 1
          norm_num
        have he2 : P.N^18*P.N^((99:ℝ)/100)=P.N^((1899:ℝ)/100) := by
          rw [←Real.rpow_natCast,←Real.rpow_add hNp]
          norm_num
        have heB : P.N^18*B=R^3*P.N^(3811/200+1/10000 : ℝ)+R^4*P.N^((1899:ℝ)/100) := by
          calc
            _ = R^3*(P.N^18*P.N^(211/200+1/10000 : ℝ))+R^4*(P.N^18*P.N^((99:ℝ)/100)) := by
              dsimp only [B]
              ring
            _ = _ := by rw [he1,he2]
        have heF : R^36*(P.N^18*B)=F := by rw [heB]; dsimp only [F]; ring
        calc
          _ = K₀*P.N^((1:ℝ)/10000)*(R^36*(P.N^18*B)) := by dsimp only [K₀]; ring
          _ = _ := by rw [heF]
  have hboundary : (A*((H:ℝ)+1))^20 ≤ 3^20*P.N^((1:ℝ)/10000)*F := by
    have h1 : 1 ≤ P.N^((7:ℝ)/25) := Real.one_le_rpow P.one_lt_N.le (by norm_num)
    have hHplus : (H:ℝ)+1 ≤ 3*P.N^((7:ℝ)/25) := by linarith only [hHscale,h1]
    have hpow : (P.N^((7:ℝ)/25))^20=P.N^((28:ℝ)/5) := by
      rw [←Real.rpow_mul_natCast hNp.le]
      norm_num
    calc
      _ ≤ (R^2*(3*P.N^((7:ℝ)/25)))^20 := by gcongr
      _ = 3^20*R^40*P.N^((28:ℝ)/5) := by rw [mul_pow,mul_pow,hpow]; ring
      _ ≤ 3^20*R^40*P.N^((1899:ℝ)/100) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)) (by positivity)
      _ ≤ 3^20*F := by
        dsimp only [F]
        nlinarith only [mul_nonneg (pow_nonneg hR 39)
          (Real.rpow_nonneg hNp.le (3811/200+1/10000 : ℝ))]
      _ ≤ _ := by
        have hh := Real.one_le_rpow P.one_lt_N.le (by norm_num : (0:ℝ) ≤ 1/10000)
        nlinarith only [mul_nonneg hF (sub_nonneg.mpr hh)]
  calc
    _ ≤ (D*M/(v*(H:ℝ))+A*((H:ℝ)+1))^20 := pow_le_pow_left₀ hU hentry 20
    _ ≤ 2^19*((D*M/(v*(H:ℝ)))^20+(A*((H:ℝ)+1))^20) :=
      add_pow_le (by positivity) (by positivity) 20
    _ ≤ 2^19*(K₀*P.N^((1:ℝ)/10000)*F+3^20*P.N^((1:ℝ)/10000)*F) := by gcongr
    _ = _ := by dsimp only [K,F,R]; ring

#print axioms quartic_first_endpoint_kernel_moment

def quarticFarPairs (P : LargeValuePattern) : Finset (ℝ×ℝ) :=
  (P.ordinates.product P.ordinates).filter (fun p => P.N^((18:ℝ)/5) < p.2-p.1)

def quarticDyadicPairs (P : LargeValuePattern) (j : ℕ) : Finset (ℝ×ℝ) :=
  (P.ordinates.product P.ordinates).filter (fun p =>
    P.N^((18:ℝ)/5)*(2:ℝ)^j ≤ p.2-p.1 ∧ p.2-p.1 ≤ 2*(P.N^((18:ℝ)/5)*(2:ℝ)^j))

def quarticFarKernelSum (P : LargeValuePattern) : ℝ :=
  ∑ p∈quarticFarPairs P, ‖quarticLogKernel P.indices (p.2-p.1)‖

theorem quarticFarKernelSum_le_dyadic (P : LargeValuePattern) :
    quarticFarKernelSum P ≤ ∑ j : Fin (⌊Real.logb 2 P.T⌋₊+1),
      ∑ p∈quarticDyadicPairs P j, ‖quarticLogKernel P.indices (p.2-p.1)‖ := by
  classical
  let F := quarticFarPairs P
  let J := Fin (⌊Real.logb 2 P.T⌋₊+1)
  let g (p : ℝ×ℝ) := ‖quarticLogKernel P.indices (p.2-p.1)‖
  have hpoint (p : ℝ×ℝ) (hp : p∈F) : g p ≤ ∑ j:J, if p∈quarticDyadicPairs P j then g p else 0 := by
    obtain ⟨hmem,hgap⟩ := Finset.mem_filter.mp hp
    have hpW := Finset.mem_product.mp hmem
    have hheight : p.2-p.1 ≤ P.T := (le_abs_self _).trans (P.ordinate_gap_le_height hpW.1 hpW.2)
    obtain ⟨j,_,hjlo,hjhi⟩ := exists_bounded_dyadic_slab (P.N^((18:ℝ)/5)) P.T (p.2-p.1)
      (Real.one_le_rpow P.one_lt_N.le (by norm_num)) hgap.le hheight
    have hpj : p∈quarticDyadicPairs P j := Finset.mem_filter.mpr ⟨hmem,hjlo,hjhi⟩
    have hh := Finset.single_le_sum (s:=Finset.univ) (a:=j)
      (f:=fun i:J => if p∈quarticDyadicPairs P i then g p else 0)
      (fun i _ => by dsimp only [g]; split_ifs <;> positivity) (Finset.mem_univ j)
    simpa only [if_pos hpj] using hh
  calc
    _ ≤ ∑ p∈F, ∑ j:J, if p∈quarticDyadicPairs P j then g p else 0 := Finset.sum_le_sum hpoint
    _ = ∑ j:J, ∑ p∈F, if p∈quarticDyadicPairs P j then g p else 0 := Finset.sum_comm
    _ ≤ ∑ j:J, ∑ p∈quarticDyadicPairs P j, g p := by
      apply Finset.sum_le_sum
      intro j _
      rw [←Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p _ _
        exact norm_nonneg _

#print axioms quarticFarKernelSum_le_dyadic

theorem quartic_first_endpoint_far_moment :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100000 ∧ ∃ C : ℝ, 4 ≤ C ∧
      ∀ P : LargeValuePattern, C ≤ P.N → P.N^(39/40-δ : ℝ) ≤ P.V →
      P.N^((18:ℝ)/5) ≤ P.T → P.T ≤ P.N^((79:ℝ)/20) →
      (quarticFarKernelSum P)^20 ≤ P.N^((1:ℝ)/500)*
        ((P.ordinates.card:ℝ)^39*P.N^(3811/200+1/10000 : ℝ)+
          (P.ordinates.card:ℝ)^40*P.N^((1899:ℝ)/100)) := by
  classical
  obtain ⟨δ,hδ,hδle,C₀,hC₀,K,hK,hstep⟩ := quartic_first_endpoint_kernel_moment
  let D : ℝ := 4/Real.log 2+1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp only [D]; positivity
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (K*D^20) (by positivity) 20 (η:=(19:ℝ)/10000) (by norm_num))
  refine ⟨δ,hδ,hδle,max 8 (max C₀ C₁),by exact (by norm_num : (4:ℝ) ≤ 8).trans (le_max_left _ _),?_⟩
  intro P hPN hV hTlo hThi
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN8 : 8 ≤ P.N := (le_max_left _ _).trans hPN
  have hPN₀ : C₀ ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hPN)
  have hconst := hC₁ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  have hT1 : 1 ≤ P.T := (Real.one_le_rpow P.one_lt_N.le (by norm_num : (0:ℝ) ≤ 18/5)).trans hTlo
  have hlogN : 1 ≤ Real.log P.N := by
    have he : Real.exp 1 ≤ P.N := Real.exp_one_lt_three.le.trans (by linarith only [hN8])
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  let J := Fin (⌊Real.logb 2 P.T⌋₊+1)
  let F : ℝ := (P.ordinates.card:ℝ)^39*P.N^(3811/200+1/10000 : ℝ)+
    (P.ordinates.card:ℝ)^40*P.N^((1899:ℝ)/100)
  let U (j:J) : ℝ := ∑ p∈quarticDyadicPairs P j, ‖quarticLogKernel P.indices (p.2-p.1)‖
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hJ : (Fintype.card J:ℝ) ≤ D*Real.log P.N := by
    have hh := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hT1)
    rw [Real.logb] at hh
    have hh' := (le_div_iff₀ hlog2).mp hh
    have htlog := Real.log_le_log P.T_pos hThi
    rw [Real.log_rpow hNp] at htlog
    simp only [J,Fintype.card_fin]
    push_cast
    apply (mul_le_mul_iff_left₀ hlog2).mp
    dsimp only [D]
    field_simp
    rw [Real.logb]
    nlinarith only [hh',htlog,hlogN,mul_le_mul_of_nonneg_right hlogN hlog2.le]
  have hU (j:J) : 0 ≤ U j := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hstep' (j:J) : (U j)^20 ≤ K*P.N^((1:ℝ)/10000)*F := by
    by_cases he : (quarticDyadicPairs P j).Nonempty
    · obtain ⟨p,hp⟩ := he
      have hp' := Finset.mem_filter.mp hp
      have hpW := Finset.mem_product.mp hp'.1
      have hlow : P.N^((18:ℝ)/5) ≤ P.N^((18:ℝ)/5)*(2:ℝ)^(j:ℕ) :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
      have hhigh : P.N^((18:ℝ)/5)*(2:ℝ)^(j:ℕ) ≤ P.N^((79:ℝ)/20) :=
        hp'.2.1.trans (((le_abs_self _).trans (P.ordinate_gap_le_height hpW.1 hpW.2)).trans hThi)
      exact hstep P hPN₀ hV _ hlow hhigh (quarticDyadicPairs P j)
        (Finset.filter_subset _ _) (fun _ hq => (Finset.mem_filter.mp hq).2)
    · have hz : quarticDyadicPairs P j=∅ := Finset.not_nonempty_iff_eq_empty.mp he
      simp only [U,hz,Finset.sum_empty,zero_pow (by decide : 20 ≠ 0)]
      positivity
  have hsum : (∑ j:J, U j)^20 ≤ (Fintype.card J:ℝ)^20*(K*P.N^((1:ℝ)/10000)*F) := by
    have hh := pow_sum_le_card_mul_sum_pow (s:=Finset.univ) (f:=U) (fun j _ => hU j) 19
    norm_num only [show 19+1=(20:ℕ) by norm_num,Finset.card_univ] at hh
    calc
      _ ≤ (Fintype.card J:ℝ)^19*∑ j:J, (U j)^20 := hh
      _ ≤ (Fintype.card J:ℝ)^19*∑ _j:J, (K*P.N^((1:ℝ)/10000)*F) := by gcongr with j; exact hstep' j
      _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  calc
    _ ≤ (∑ j:J, U j)^20 := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (quarticFarKernelSum_le_dyadic P) 20
    _ ≤ (Fintype.card J:ℝ)^20*(K*P.N^((1:ℝ)/10000)*F) := hsum
    _ ≤ (D*Real.log P.N)^20*(K*P.N^((1:ℝ)/10000)*F) := by gcongr
    _ = (K*D^20*(Real.log P.N)^20)*P.N^((1:ℝ)/10000)*F := by ring
    _ ≤ P.N^((19:ℝ)/10000)*P.N^((1:ℝ)/10000)*F := by gcongr
    _ = _ := by rw [←Real.rpow_add hNp]; dsimp only [F]; norm_num

#print axioms quartic_first_endpoint_far_moment

theorem quarticLogKernel_eq_dirichlet (P : LargeValuePattern) (t : ℝ) :
    quarticLogKernel P.indices t = ∑ n∈P.indices, dirichletPhase n t := by
  apply Finset.sum_congr rfl
  intro n hn
  exact PintzEndpointResearch.logarithmicTaylorPhase_character (P.index_pos hn) t

#print axioms quarticLogKernel_eq_dirichlet

theorem quarticLogKernel_norm_sub_swap (P : LargeValuePattern) (t u : ℝ) :
    ‖quarticLogKernel P.indices (t-u)‖ = ‖quarticLogKernel P.indices (u-t)‖ := by
  rw [quarticLogKernel_eq_dirichlet,quarticLogKernel_eq_dirichlet,
    ←norm_sum_dirichletPhase_abs P.indices (fun _ hn => P.index_pos hn) (t-u),
    ←norm_sum_dirichletPhase_abs P.indices (fun _ hn => P.index_pos hn) (u-t),abs_sub_comm]

#print axioms quarticLogKernel_norm_sub_swap

/-- Exact near/far decomposition of the Gram norm sum, retaining all ordered pairs. -/
theorem quartic_gram_near_far (P : LargeValuePattern) :
    (∑ t∈P.ordinates, ∑ u∈P.ordinates, ‖quarticLogKernel P.indices (u-t)‖) =
      (∑ t∈P.ordinates, ∑ u∈P.ordinates,
        if |u-t| ≤ P.N^((18:ℝ)/5) then ‖quarticLogKernel P.indices (u-t)‖ else 0)+
        2*quarticFarKernelSum P := by
  classical
  let L := P.N^((18:ℝ)/5)
  let f (t u : ℝ) := ‖quarticLogKernel P.indices (u-t)‖
  have hL : 0 < L := Real.rpow_pos_of_pos (zero_lt_one.trans P.one_lt_N) _
  have hp (t u : ℝ) : f t u =
      (if |u-t| ≤ L then f t u else 0)+
      (if L < u-t then f t u else 0)+(if L < t-u then f t u else 0) := by
    by_cases h : |u-t| ≤ L
    · have h₁ : ¬L < u-t := not_lt.mpr ((le_abs_self _).trans h)
      have h₂ : ¬L < t-u := by rw [abs_sub_comm] at h; exact not_lt.mpr ((le_abs_self _).trans h)
      simp only [if_pos h,if_neg h₁,if_neg h₂,add_zero]
    · have hh : L < u-t ∨ L < t-u := by
        have := lt_of_not_ge h
        rcases le_total t u with ht|ht
        · rw [abs_of_nonneg (sub_nonneg.mpr ht)] at this
          exact Or.inl this
        · rw [abs_of_nonpos (sub_nonpos.mpr ht)] at this
          exact Or.inr (by linarith)
      rcases hh with hh|hh
      · have h₂ : ¬L < t-u := by linarith
        simp only [if_neg h,if_pos hh,if_neg h₂,zero_add,add_zero]
      · have h₁ : ¬L < u-t := by linarith
        simp only [if_neg h,if_neg h₁,if_pos hh,zero_add]
  have hpos : (∑ t∈P.ordinates, ∑ u∈P.ordinates, if L < u-t then f t u else 0)=quarticFarKernelSum P := by
    unfold quarticFarKernelSum quarticFarPairs
    rw [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
  have hneg : (∑ t∈P.ordinates, ∑ u∈P.ordinates, if L < t-u then f t u else 0)=quarticFarKernelSum P := by
    rw [Finset.sum_comm]
    simpa only [f,quarticLogKernel_norm_sub_swap P] using hpos
  calc
    _ = ∑ t∈P.ordinates, ∑ u∈P.ordinates,
        ((if |u-t| ≤ L then f t u else 0)+(if L < u-t then f t u else 0)+
          (if L < t-u then f t u else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      exact Finset.sum_congr rfl (fun u _ => hp t u)
    _ = _ := by simp only [Finset.sum_add_distrib,hpos,hneg]; dsimp only [L,f]; ring

#print axioms quartic_gram_near_far

theorem quartic_near_far_gram_source {k l ε : ℝ}
    (hpair : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ P : LargeValuePattern,
      ((P.ordinates.card:ℝ)*P.V)^2 ≤ 2*P.N*
        ((P.ordinates.card:ℝ)*(2*P.N+C*(P.ordinates.card:ℝ)*
          ((2*P.N^((18:ℝ)/5))/P.N)^(k+ε)*P.N^(l+ε)+
          4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*P.N^((18:ℝ)/5))) : ℝ))+
          2*quarticFarKernelSum P) := by
  classical
  obtain ⟨C,hC,hrow⟩ := PintzEndpointResearch.exponentPair_nearMatrix_row hpair hε
  refine ⟨C,hC,?_⟩
  intro P
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hr (t : ℝ) (ht : t∈P.ordinates) := hrow P (P.N^((18:ℝ)/5)) (by positivity) ⟨t,ht⟩
  have he (t : ℝ) (ht : t∈P.ordinates) :
      (∑ u : P.ordinates, ‖PintzEndpointResearch.nearMatrix P (P.N^((18:ℝ)/5)) ⟨t,ht⟩ u‖) =
      ∑ u∈P.ordinates, if |u-t| ≤ P.N^((18:ℝ)/5) then ‖quarticLogKernel P.indices (u-t)‖ else 0 := by
    simp only [PintzEndpointResearch.nearMatrix,PintzEndpointResearch.gramKernel,
      apply_ite norm,norm_zero,quarticLogKernel_eq_dirichlet]
    exact Finset.sum_attach P.ordinates (fun u : ℝ =>
      if |u-t| ≤ P.N^((18:ℝ)/5) then ‖∑ n∈P.indices, dirichletPhase n (u-t)‖ else 0)
  have hnear : (∑ t∈P.ordinates, ∑ u∈P.ordinates,
      if |u-t| ≤ P.N^((18:ℝ)/5) then ‖quarticLogKernel P.indices (u-t)‖ else 0) ≤
      ∑ _t∈P.ordinates, (2*P.N+C*(P.ordinates.card:ℝ)*
        ((2*P.N^((18:ℝ)/5))/P.N)^(k+ε)*P.N^(l+ε)+
        4*Real.pi*C*P.N*(harmonic (Nat.ceil (2*P.N^((18:ℝ)/5))) : ℝ)) := by
    apply Finset.sum_le_sum
    intro t ht
    have hh := hr t ht
    rw [he t ht] at hh
    exact hh
  have hg := P.sharp_gram
  simp_rw [←quarticLogKernel_eq_dirichlet P] at hg
  rw [quartic_gram_near_far P] at hg
  apply hg.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add _ le_rfl
  simpa only [Finset.sum_const,nsmul_eq_mul] using hnear

#print axioms quartic_near_far_gram_source

theorem eventually_quartic_near_scales {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ N : ℝ in Filter.atTop,
      4*N*(C*((2*N^((18:ℝ)/5))/N)^(89/3478+1/100000 : ℝ)*
        N^(15327/17390+1/100000 : ℝ)) ≤ N^((1949:ℝ)/1000) ∧
      4*N*(2*N+4*Real.pi*C*N*(harmonic (Nat.ceil (2*N^((18:ℝ)/5))) : ℝ)) ≤
        N^(2+1/1000 : ℝ) := by
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  filter_upwards [eventually_const_log_pow_le_rpow (8*C) (by positivity) 0
      (η:=(1:ℝ)/2000) (by norm_num),
    eventually_exponentPair_gram_diagonal hC (τ:=(18:ℝ)/5) (by norm_num)
      (η:=(1:ℝ)/1000) (by norm_num),Filter.eventually_ge_atTop (2:ℝ)] with N hc hd hN
  have hNp : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  constructor
  · have hs : (2*N^((18:ℝ)/5))/N=2*N^((13:ℝ)/5) := by
      rw [mul_div_assoc]
      nth_rw 2 [←Real.rpow_one N]
      rw [←Real.rpow_sub hNp]
      norm_num
    have htwo : (2:ℝ)^(89/3478+1/100000 : ℝ) ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ) ≤ 2) (by norm_num : (89/3478+1/100000 : ℝ) ≤ 1)
    have hf : ((2*N^((18:ℝ)/5))/N)^(89/3478+1/100000 : ℝ)*
        N^(15327/17390+1/100000 : ℝ) ≤ 2*N^((1897:ℝ)/2000) := by
      rw [hs,Real.mul_rpow (by norm_num) (Real.rpow_nonneg hNp.le _),
        ←Real.rpow_mul hNp.le,mul_assoc,←Real.rpow_add hNp]
      exact mul_le_mul htwo (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
        (by positivity) (by norm_num)
    have hc' : 8*C ≤ N^((1:ℝ)/2000) := by simpa only [pow_zero,mul_one] using hc
    calc
      _ = 4*N*C*(((2*N^((18:ℝ)/5))/N)^(89/3478+1/100000 : ℝ)*
          N^(15327/17390+1/100000 : ℝ)) := by ring
      _ ≤ 4*N*C*(2*N^((1897:ℝ)/2000)) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (8*C)*(N*N^((1897:ℝ)/2000)) := by ring
      _ ≤ N^((1:ℝ)/2000)*(N*N^((1897:ℝ)/2000)) := mul_le_mul_of_nonneg_right hc' (by positivity)
      _ = _ := by
        nth_rw 2 [←Real.rpow_one N]
        rw [←Real.rpow_add hNp,←Real.rpow_add hNp]
        norm_num
  · apply hd _ (by positivity)
    calc
      _ ≤ N*N^((18:ℝ)/5) := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by rw [Real.rpow_add hNp,Real.rpow_one]; ring

#print axioms eventually_quartic_near_scales

/-- Near frequencies are absorbed using the existing analytic fourth exponent pair. -/
theorem quartic_first_endpoint_gram :
    ∃ C : ℝ, 4 ≤ C ∧ ∀ P : LargeValuePattern, C ≤ P.N →
      P.N^((97499:ℝ)/100000) ≤ P.V →
      (P.ordinates.card:ℝ)^2*P.V^2 ≤
        (P.ordinates.card:ℝ)*P.N^(2+1/1000 : ℝ)+8*P.N*quarticFarKernelSum P := by
  obtain ⟨C₀,hC₀,hsource⟩ := quartic_near_far_gram_source
    exponentPair_taoTrudgianYang_fourthNew (ε:=(1:ℝ)/100000) (by norm_num)
  obtain ⟨C₁,hC₁⟩ := Filter.eventually_atTop.mp (eventually_quartic_near_scales hC₀)
  refine ⟨max 4 C₁,le_max_left _ _,?_⟩
  intro P hPN hV
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨hf,hd⟩ := hC₁ P.N ((le_max_right _ _).trans hPN)
  have hv : P.N^((1949:ℝ)/1000) ≤ P.V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hV 2
    rw [←Real.rpow_mul_natCast hNp.le] at hh
    exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by norm_num)).trans hh
  let R : ℝ := P.ordinates.card
  let D := 2*P.N+4*Real.pi*C₀*P.N*(harmonic (Nat.ceil (2*P.N^((18:ℝ)/5))) : ℝ)
  let F := C₀*((2*P.N^((18:ℝ)/5))/P.N)^(89/3478+1/100000 : ℝ)*
    P.N^(15327/17390+1/100000 : ℝ)
  have hh : 4*P.N*F ≤ P.V^2 := hf.trans hv
  have hg : (R*P.V)^2 ≤ 2*P.N*(R*(D+R*F)+2*quarticFarKernelSum P) := by
    convert hsource P using 1
    dsimp only [R,D,F]
    ring
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg R)
  have hdiag := mul_le_mul_of_nonneg_left hd (show 0 ≤ R by positivity)
  change R^2*P.V^2 ≤ R*P.N^(2+1/1000 : ℝ)+8*P.N*quarticFarKernelSum P
  dsimp only [D] at hg
  nlinarith only [hg,hmul,hdiag]

#print axioms quartic_first_endpoint_gram

/-- Unconditional physical large-values estimate from the actual far-correlation moment. -/
theorem quartic_first_endpoint_card :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/100000 ∧ ∃ C : ℝ, 4 ≤ C ∧
      ∀ P : LargeValuePattern, C ≤ P.N → P.N^(39/40-δ : ℝ) ≤ P.V →
      P.N^((18:ℝ)/5) ≤ P.T → P.T ≤ P.N^((79:ℝ)/20) →
      (P.ordinates.card:ℝ) ≤ P.N^((7:ℝ)/100) := by
  obtain ⟨δ,hδ,hδle,C₀,hC₀,hfar⟩ := quartic_first_endpoint_far_moment
  obtain ⟨C₁,hC₁,hgram⟩ := quartic_first_endpoint_gram
  obtain ⟨C₂,hC₂⟩ := Filter.eventually_atTop.mp
    (eventually_const_log_pow_le_rpow (2*16^20) (by norm_num) 0
      (η:=(1:ℝ)/1000) (by norm_num))
  refine ⟨δ,hδ,hδle,max C₀ (max C₁ C₂),hC₀.trans (le_max_left _ _),?_⟩
  intro P hPN hV hTlo hThi
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN1 := P.one_lt_N.le
  have hv : P.N^((97499:ℝ)/100000) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith only [hδle])).trans hV
  have hv2 : P.N^((97499:ℝ)/50000) ≤ P.V^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hv 2
    rw [←Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh ⊢
    exact hh
  have hv40 : P.N^((97499:ℝ)/2500) ≤ P.V^40 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hv 40
    rw [←Real.rpow_mul_natCast hNp.le] at hh
    norm_num at hh ⊢
    exact hh
  have hc : 2*16^20 ≤ P.N^((1:ℝ)/1000) := by
    simpa only [pow_zero,mul_one] using
      hC₂ P.N ((le_max_right _ _).trans ((le_max_right _ _).trans hPN))
  have hc2 : 2 ≤ P.N^((1:ℝ)/1000) := (by norm_num : (2:ℝ) ≤ 2*16^20).trans hc
  let R : ℝ := P.ordinates.card
  let U := quarticFarKernelSum P
  have hR0 : 0 ≤ R := by positivity
  have hU0 : 0 ≤ U := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  change R ≤ P.N^((7:ℝ)/100)
  by_contra hRbound
  have hR : P.N^((7:ℝ)/100) < R := lt_of_not_ge hRbound
  have hRp : 0 < R := (Real.rpow_pos_of_pos hNp _).trans hR
  have hd : 2*P.N^(2+1/1000 : ℝ) ≤ R*P.V^2 := by
    calc
      _ ≤ P.N^((1:ℝ)/1000)*P.N^(2+1/1000 : ℝ) :=
        mul_le_mul_of_nonneg_right hc2 (by positivity)
      _ = P.N^((1001:ℝ)/500) := by rw [←Real.rpow_add hNp]; norm_num
      _ ≤ P.N^((7:ℝ)/100)*P.N^((97499:ℝ)/50000) := by
        rw [←Real.rpow_add hNp]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ ≤ R*P.V^2 := mul_le_mul hR.le hv2 (by positivity) hR0
  have hg := hgram P ((le_max_left _ _).trans ((le_max_right _ _).trans hPN)) hv
  have hg' : R^2*P.V^2 ≤ 16*P.N*U := by
    change R^2*P.V^2 ≤ R*P.N^(2+1/1000 : ℝ)+8*P.N*U at hg
    have hh := mul_le_mul_of_nonneg_left hd hR0
    nlinarith only [hg,hh]
  have hm := hfar P ((le_max_left _ _).trans hPN) hV hTlo hThi
  change U^20 ≤ P.N^((1:ℝ)/500)*
    (R^39*P.N^(3811/200+1/10000 : ℝ)+R^40*P.N^((1899:ℝ)/100)) at hm
  have hnear : R^39*P.N^(3811/200+1/10000 : ℝ) ≤ R^40*P.N^((1899:ℝ)/100) := by
    have hr : P.N^((651:ℝ)/10000) ≤ R :=
      (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)).trans hR.le
    calc
      _ = (R^39*P.N^((1899:ℝ)/100))*P.N^((651:ℝ)/10000) := by
        rw [mul_assoc,←Real.rpow_add hNp]
        norm_num
      _ ≤ (R^39*P.N^((1899:ℝ)/100))*R := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  have hm' : U^20 ≤ 2*R^40*P.N^((2374:ℝ)/125) := by
    calc
      _ ≤ P.N^((1:ℝ)/500)*(2*(R^40*P.N^((1899:ℝ)/100))) :=
        hm.trans (mul_le_mul_of_nonneg_left (by linarith only [hnear]) (by positivity))
      _ = _ := by
        calc
          _ = 2*R^40*(P.N^((1:ℝ)/500)*P.N^((1899:ℝ)/100)) := by ring
          _ = _ := by rw [←Real.rpow_add hNp]; norm_num
  have hp := pow_le_pow_left₀ (mul_nonneg (sq_nonneg R) (sq_nonneg P.V)) hg' 20
  have hp' : R^40*P.V^40 ≤ 16^20*P.N^20*U^20 := by
    simpa only [mul_pow,←pow_mul,show 2*20=(40:ℕ) by norm_num] using hp
  have hfinal : R^40*P.N^((97499:ℝ)/2500) ≤ R^40*P.N^((38993:ℝ)/1000) := by
    calc
      _ ≤ R^40*P.V^40 := mul_le_mul_of_nonneg_left hv40 (by positivity)
      _ ≤ 16^20*P.N^20*U^20 := hp'
      _ ≤ 16^20*P.N^20*(2*R^40*P.N^((2374:ℝ)/125)) :=
        mul_le_mul_of_nonneg_left hm' (by positivity)
      _ = (2*16^20)*R^40*P.N^((4874:ℝ)/125) := by
        calc
          _ = (2*16^20)*R^40*(P.N^20*P.N^((2374:ℝ)/125)) := by ring
          _ = _ := by rw [←Real.rpow_natCast P.N 20,←Real.rpow_add hNp]; norm_num
      _ ≤ P.N^((1:ℝ)/1000)*R^40*P.N^((4874:ℝ)/125) := by gcongr
      _ = _ := by
        calc
          _ = R^40*(P.N^((1:ℝ)/1000)*P.N^((4874:ℝ)/125)) := by ring
          _ = _ := by rw [←Real.rpow_add hNp]; norm_num
  have hh := (mul_le_mul_iff_right₀ (pow_pos hRp 40)).mp hfinal
  exact (not_le_of_gt (Real.rpow_lt_rpow_of_exponent_lt P.one_lt_N (by norm_num))) hh

#print axioms quartic_first_endpoint_card

theorem pintz_first_endpoint_research_largeValueBound {τ : ℝ}
    (hτlo : 135765/36668 < τ) (hτhi : τ ≤ 63/16) :
    IsLargeValueBound (39/40) τ (2*τ/105) := by
  intro ε hε
  obtain ⟨δ₀,hδ₀,_hδ₀le,C,hC,hcard⟩ := quartic_first_endpoint_card
  let δ : ℝ := min δ₀ (min ((τ-18/5)/2) ((79/20-τ)/2))
  have hlo : 18/5 < τ := by linarith only [hτlo]
  have hhi : τ < 79/20 := by linarith only [hτhi]
  have hδ : 0 < δ := lt_min hδ₀ (lt_min (by linarith only [hlo]) (by linarith only [hhi]))
  have hδsmall : δ ≤ δ₀ := min_le_left _ _
  have hδlo : δ ≤ (τ-18/5)/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδhi : δ ≤ (79/20-τ)/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hC1 : 1 ≤ C := (by norm_num : (1:ℝ) ≤ 4).trans hC
  refine ⟨C,hC1,δ,hδ,?_⟩
  intro P hPN hTlo hThi hVlo _hVhi
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT₀ : P.N^((18:ℝ)/5) ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδlo,hlo])).trans hTlo
  have hT₁ : P.T ≤ P.N^((79:ℝ)/20) := hThi.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδhi,hhi]))
  have hV : P.N^(39/40-δ₀ : ℝ) ≤ P.V :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith only [hδsmall])).trans hVlo
  calc
    _ ≤ P.N^((7:ℝ)/100) := hcard P hPN hV hT₀ hT₁
    _ ≤ P.N^(2*τ/105+ε) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith only [hτlo,hε])
    _ ≤ C*P.N^(2*τ/105+ε) := le_mul_of_one_le_left (by positivity) hC1

#print axioms pintz_first_endpoint_research_largeValueBound

theorem pintz_first_endpoint_research_exponent {τ : ℝ}
    (hτlo : 21/8 ≤ τ) (hτhi : τ ≤ 63/16) :
    largeValueExponent (39/40) τ ≤ ((2*τ/105 : ℝ) : EReal) := by
  by_cases hlo : τ ≤ 135765/36668
  · exact largeValueExponent_le_pintz_first_endpoint_pair_range hτlo hlo
  · exact largeValueExponent_le_of_bound
      (pintz_first_endpoint_research_largeValueBound (lt_of_not_ge hlo) hτhi)

#print axioms pintz_first_endpoint_research_exponent

/-- The unchanged frozen first endpoint, by an original far-correlation argument. -/
theorem pintz_first_endpoint_research_density :
    zeroDensityExponent (39/40) ≤ ((16/21 : ℝ) : EReal) := by
  have hh := zeroDensityExponent_le_of_two_thirds_largeValue_ranges
    (39/40) (2/105) (63/16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at hh
  apply hh
  · intro τ hτlo hτhi
    rw [zetaLargeValueExponent_eq_bot_pintz_first_endpoint hτlo hτhi]
    exact bot_le
  · intro τ hτlo hτhi
    have hb := pintz_first_endpoint_research_exponent hτlo hτhi
    rw [←EReal.coe_mul,show (2/105:ℝ)*τ=2*τ/105 by ring]
    exact hb

#print axioms pintz_first_endpoint_research_density

/-- Complete frozen finite table, now including both formerly disputed endpoints. -/
theorem zeroDensityExponent_le_printedFinite {σ : ℝ}
    (hσ : 1/2 ≤ σ) (hσhi : σ < 59/60) :
    zeroDensityExponent σ ≤ ((LiteratureTable.printedFiniteDensityTable σ):EReal) := by
  by_cases h39 : σ=39/40
  · subst σ
    norm_num [LiteratureTable.printedFiniteDensityTable]
    exact pintz_first_endpoint_research_density
  by_cases h41 : σ=41/42
  · subst σ
    norm_num [LiteratureTable.printedFiniteDensityTable]
    exact PintzEndpointResearch.pintz_second_endpoint_research_density
  exact LiteratureTable.zeroDensityExponent_le_printedFinite_regular hσ hσhi h39 h41

#print axioms zeroDensityExponent_le_printedFinite

end

end TaoTrudgianYang2025.PintzFirstEndpointResearch
