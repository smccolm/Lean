import TaoTrudgianYang2025.SargosQuarticDualRange

/-! Exact positive quadratic coordinates for the normalized quartic phase.
The larger interval [0,3] supplies uniform margins around [1,2]. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosQuarticMorseCoefficient (ε r u : ℝ) : ℝ :=
  1+ε*(u^2+2*u*r+3*r^2)

def sargosQuarticMorseNumerator (ε r u : ℝ) : ℝ :=
  2+4*ε*(u^2+u*r+r^2)

def sargosQuarticMorseCoordinate (ε r u : ℝ) : ℝ :=
  (u-r)*Real.sqrt (2*sargosQuarticMorseCoefficient ε r u)

theorem sargosQuartic_stationary_factor (ε r u : ℝ) :
    sargosQuarticPhase 1 ε u-sargosQuarticPhase 1 ε r-
        sargosQuarticSlope 1 ε r*(u-r) =
      (u-r)^2*sargosQuarticMorseCoefficient ε r u := by
  unfold sargosQuarticPhase sargosQuarticSlope sargosQuarticMorseCoefficient
  ring

theorem sargosQuarticMorseCoefficient_bounds {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    7/16 ≤ sargosQuarticMorseCoefficient ε r u ∧
      sargosQuarticMorseCoefficient ε r u ≤ 25/16 := by
  have hur : u*r ≤ 9 := by nlinarith [mul_le_mul hu.2 hr.2 hr.1 (by norm_num : (0:ℝ) ≤ 3)]
  have huu : u^2 ≤ 9 := by nlinarith [pow_le_pow_left₀ hu.1 hu.2 2]
  have hrr : r^2 ≤ 9 := by nlinarith [pow_le_pow_left₀ hr.1 hr.2 2]
  have hp0 : 0 ≤ u^2+2*u*r+3*r^2 := by nlinarith [mul_nonneg hu.1 hr.1,sq_nonneg u,sq_nonneg r]
  have hp : u^2+2*u*r+3*r^2 ≤ 54 := by nlinarith
  have he : |ε*(u^2+2*u*r+3*r^2)| ≤ 9/16 := by
    rw [abs_mul,abs_of_nonneg hp0]
    calc
      _ ≤ (1/96:ℝ)*54 := mul_le_mul hε hp hp0 (by norm_num)
      _ = _ := by norm_num
  have hh := abs_le.mp he
  unfold sargosQuarticMorseCoefficient
  constructor <;> linarith [hh.1,hh.2]

theorem sargosQuarticMorseNumerator_bounds {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    7/8 ≤ sargosQuarticMorseNumerator ε r u ∧
      sargosQuarticMorseNumerator ε r u ≤ 25/8 := by
  have hur : u*r ≤ 9 := by nlinarith [mul_le_mul hu.2 hr.2 hr.1 (by norm_num : (0:ℝ) ≤ 3)]
  have huu : u^2 ≤ 9 := by nlinarith [pow_le_pow_left₀ hu.1 hu.2 2]
  have hrr : r^2 ≤ 9 := by nlinarith [pow_le_pow_left₀ hr.1 hr.2 2]
  have hp0 : 0 ≤ u^2+u*r+r^2 := by nlinarith [mul_nonneg hu.1 hr.1,sq_nonneg u,sq_nonneg r]
  have hp : u^2+u*r+r^2 ≤ 27 := by nlinarith
  have he : |4*ε*(u^2+u*r+r^2)| ≤ 9/8 := by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 4),abs_of_nonneg hp0]
    calc
      _ ≤ (4*(1/96):ℝ)*27 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hε (by norm_num)) hp hp0 (by norm_num)
      _ = _ := by norm_num
  have hh := abs_le.mp he
  unfold sargosQuarticMorseNumerator
  constructor <;> linarith [hh.1,hh.2]

theorem sargosQuarticMorseCoefficient_hasDerivAt (ε r u : ℝ) :
    HasDerivAt (sargosQuarticMorseCoefficient ε r) (ε*(2*u+2*r)) u := by
  change HasDerivAt (fun x : ℝ => 1+ε*(x^2+2*x*r+3*r^2)) (ε*(2*u+2*r)) u
  convert (hasDerivAt_const u 1).add
    (((((hasDerivAt_id u).pow 2).add
      (((hasDerivAt_id u).const_mul 2).mul_const r)).add_const (3*r^2)).const_mul ε) using 1
  dsimp only [id_eq]
  ring

theorem sargosQuarticMorseCoordinate_hasDerivAt {ε r u : ℝ}
    (hp : 0 < sargosQuarticMorseCoefficient ε r u) :
    HasDerivAt (sargosQuarticMorseCoordinate ε r)
      (sargosQuarticMorseNumerator ε r u/Real.sqrt (2*sargosQuarticMorseCoefficient ε r u)) u := by
  have hs : Real.sqrt (2*sargosQuarticMorseCoefficient ε r u) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*sargosQuarticMorseCoefficient ε r u by positivity)
  have hd := ((sargosQuarticMorseCoefficient_hasDerivAt ε r u).const_mul 2).sqrt
    (ne_of_gt (show 0 < 2*sargosQuarticMorseCoefficient ε r u by positivity))
  convert ((hasDerivAt_id u).sub_const r).mul hd using 1
  dsimp only [id_eq]
  field_simp
  unfold sargosQuarticMorseNumerator sargosQuarticMorseCoefficient at hs2 ⊢
  nlinarith only [hs2]

theorem sargosQuarticMorseCoordinate_contDiffAt {ε r u : ℝ}
    (hp : 0 < sargosQuarticMorseCoefficient ε r u) :
    ContDiffAt ℝ ∞ (sargosQuarticMorseCoordinate ε r) u := by
  have hc : ContDiff ℝ ∞ (fun x => 2*sargosQuarticMorseCoefficient ε r x) := by
    unfold sargosQuarticMorseCoefficient
    fun_prop
  exact (contDiffAt_id.sub contDiffAt_const).mul
    (hc.contDiffAt.sqrt (ne_of_gt (show 0 < 2*sargosQuarticMorseCoefficient ε r u by positivity)))

theorem sargosQuarticMorseCoordinate_normalForm {ε r u : ℝ}
    (hp : 0 ≤ sargosQuarticMorseCoefficient ε r u) :
    sargosQuarticPhase 1 ε u-sargosQuarticPhase 1 ε r-
        sargosQuarticSlope 1 ε r*(u-r) =
      (sargosQuarticMorseCoordinate ε r u)^2/2 := by
  rw [sargosQuartic_stationary_factor]
  unfold sargosQuarticMorseCoordinate
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*sargosQuarticMorseCoefficient ε r u)]
  ring

theorem sargosQuarticMorseCoordinate_at_center (ε r : ℝ) :
    sargosQuarticMorseCoordinate ε r r = 0 := by
  simp only [sargosQuarticMorseCoordinate,sub_self,zero_mul]


theorem sargosQuarticMorseCoordinate_sqrt_bounds {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    1/2 ≤ Real.sqrt (2*sargosQuarticMorseCoefficient ε r u) ∧
      Real.sqrt (2*sargosQuarticMorseCoefficient ε r u) ≤ 2 := by
  have hb := sargosQuarticMorseCoefficient_bounds hε hr hu
  have hp : 0 ≤ 2*sargosQuarticMorseCoefficient ε r u := by linarith [hb.1]
  have hs := Real.sq_sqrt hp
  have hs0 := Real.sqrt_nonneg (2*sargosQuarticMorseCoefficient ε r u)
  constructor <;> nlinarith [hb.1,hb.2]

theorem sargosQuarticMorseCoordinate_deriv_bounds {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    7/16 ≤ deriv (sargosQuarticMorseCoordinate ε r) u ∧
      deriv (sargosQuarticMorseCoordinate ε r) u ≤ 25/4 := by
  have hb := sargosQuarticMorseCoefficient_bounds hε hr hu
  have hp : 0 < sargosQuarticMorseCoefficient ε r u := by linarith [hb.1]
  have hs := sargosQuarticMorseCoordinate_sqrt_bounds hε hr hu
  have hn := sargosQuarticMorseNumerator_bounds hε hr hu
  have hs0 : 0 < Real.sqrt (2*sargosQuarticMorseCoefficient ε r u) := by linarith [hs.1]
  rw [(sargosQuarticMorseCoordinate_hasDerivAt hp).deriv]
  constructor
  · apply (le_div_iff₀ hs0).mpr
    nlinarith [hs.2,hn.1]
  · apply (div_le_iff₀ hs0).mpr
    nlinarith [hs.1,hn.2]

theorem sargosQuarticMorseCoordinate_strictMonoOn {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    StrictMonoOn (sargosQuarticMorseCoordinate ε r) (Icc 0 3) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 3)
  · intro u hu
    have hb := (sargosQuarticMorseCoefficient_bounds hε hr hu).1
    exact (sargosQuarticMorseCoordinate_contDiffAt (by linarith)).continuousAt.continuousWithinAt
  · intro u hu
    have hb := (sargosQuarticMorseCoordinate_deriv_bounds hε hr (interior_subset hu)).1
    linarith


end TaoTrudgianYang2025
