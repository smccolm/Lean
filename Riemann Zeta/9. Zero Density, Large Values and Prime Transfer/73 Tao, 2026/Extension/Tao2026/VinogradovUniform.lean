import Tao2026.VinogradovMeanValue

namespace Tao2026

open scoped BigOperators NNReal

theorem source_bilinear_critical_root_bound_quarter_of_meanValue
    {X F α C : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1)
    (hC : 0 < C)
    (hJ : ∀ V : ℕ, 1 ≤ V →
      (vinogradovMeanValueCount
        (GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F))
        (vinogradovTaylorDegree X F) V : ℝ) ≤
      C * (V : ℝ) ^
        ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) : ℕ) +
          (255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632) / 128)) :
    ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
      (vinogradovAveragingRange X)‖ ≤
      (C ^ 2 *
        (((3 * GafniTao.fordVinogradovKappa
          (vinogradovTaylorDegree X F) : ℕ) : ℝ) ^
            (2 * vinogradovTaylorDegree X F))) ^
          (1 / ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
            (2 * GafniTao.fordVinogradovKappa
              (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) *
        (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
        (vinogradovAveragingRange X : ℝ) ^
          (-(16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 12648448) /
            ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
              (2 * GafniTao.fordVinogradovKappa
                (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) := by
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let K := GafniTao.fordVinogradovKappa R
  let m := K * (2 * K)
  let δ : ℝ := 255 * (R : ℝ) ^ 2 / 197632
  let d : ℝ := 16065 * (R : ℝ) ^ 2 / 12648448
  let D : ℝ := C ^ 2 * (((3 * K : ℕ) : ℝ)) ^ (2 * R)
  have hR : 1 ≤ R := by
    have hforty := forty_le_vinogradovTaylorDegree hX hFhigh
    dsimp only [R]
    omega
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hK : 1 ≤ K := by
    have hk := two_mul_fordVinogradovKappa R
    have : 2 ≤ R * (R + 1) := by nlinarith
    rw [← hk] at this
    omega
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (mul_ne_zero (by omega) (by omega)))
  have hP := source_prod_coordinateSums_le_quarterSaving_mul_criticalPower
    (ell := K) hX hFhigh hα hn hK hcoeff hsmall
  dsimp only [R, V, K, δ] at hJ hP
  rw [show (-(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2)) / 197632 =
      -(255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632) by ring] at hP
  have hassembled :=
    powered_bilinear_critical_bound_of_meanValue_and_coordinate_bounds
      c (vinogradovTaylorDegree X F) (vinogradovAveragingRange X)
        (by simpa only [R] using hR) (by simpa only [V] using hV) hC.le
        (ε := (255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632) / 128)
        (δ := 255 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 197632)
        (A := (((3 * GafniTao.fordVinogradovKappa
          (vinogradovTaylorDegree X F) : ℕ) : ℝ)) ^
            (2 * vinogradovTaylorDegree X F))
        (hJ (vinogradovAveragingRange X) (by simpa only [V] using hV)) hP
  have hpow :
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ m ≤
        D * (V : ℝ) ^ (((2 * m : ℕ) : ℝ) - d) := by
    dsimp only [R, V, K, m, δ, d, D] at hassembled ⊢
    convert hassembled using 1
    congr 2
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hVpos : 0 < (V : ℝ) := by exact_mod_cast hV
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hroot := le_root_mul_sq_mul_saving_of_pow_le hm
    (norm_nonneg _) hD hVpos hpow
  dsimp only [R, V, K, m, δ, d, D] at hroot ⊢
  exact hroot

def VinogradovCriticalRootCoefficientBoundAt (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, 40 ≤ R →
    ∃ C : ℝ, 0 < C ∧
      (∀ V : ℕ, 1 ≤ V →
        (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
          C * (V : ℝ) ^
            ((GafniTao.fordVinogradovKappa R : ℕ) +
              (255 * (R : ℝ) ^ 2 / 197632) / 128)) ∧
      (C ^ 2 * (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
          (1 / ((GafniTao.fordVinogradovKappa R *
            (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) ≤ A

theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_rootCoefficient
    {A : ℝ} (hA : VinogradovCriticalRootCoefficientBoundAt A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt (2 * A) := by
  refine ⟨by nlinarith [hA.1], ?_⟩
  intro X F α n c hX hFhigh hα hn hcoeff hsmall
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let T := Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 / (Real.log F) ^ 2)
  have hT : 0 < T := Real.exp_pos _
  have hsmallTwo : 2 * α * T < 1 := by
    calc
      2 * α * T ≤ (2 * A) * α * T := by gcongr; nlinarith [hA.1]
      _ < 1 := by simpa only [T, mul_assoc] using hsmall
  have hR : 40 ≤ R := by
    dsimp only [R]
    exact forty_le_vinogradovTaylorDegree hX hFhigh
  obtain ⟨C, hC, hJ, hrootCoefficient⟩ := hA.2 R hR
  have hroot := source_bilinear_critical_root_bound_quarter_of_meanValue
    hX hFhigh hα hn hcoeff (by simpa only [T] using hsmallTwo) hC
      (by simpa only [R] using hJ)
  have hXsixteen : 16 ≤ X :=
    (sixteen_lt_of_nontrivialScale hX hFhigh hα
      (by simpa only [T] using hsmallTwo)).le
  have hsaving := quarter_root_scale_saving_le_sourceDecay hXsixteen hFhigh
  have hVnonneg : 0 ≤ (V : ℝ) ^ (2 : ℕ) := by positivity
  have hAnonneg : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA.1
  have hαnonneg : 0 ≤ α := (zero_le_one.trans hα)
  dsimp only [R, V] at hrootCoefficient hroot hsaving ⊢
  change ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
      (vinogradovAveragingRange X)‖ ≤
    ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * ((2 * A) * α * T))
  calc
    ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      (C ^ 2 *
        (((3 * GafniTao.fordVinogradovKappa
          (vinogradovTaylorDegree X F) : ℕ) : ℝ) ^
            (2 * vinogradovTaylorDegree X F))) ^
          (1 / ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
            (2 * GafniTao.fordVinogradovKappa
              (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) *
        (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
        (vinogradovAveragingRange X : ℝ) ^
          (-(16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 12648448) /
            ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
              (2 * GafniTao.fordVinogradovKappa
                (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) := hroot
    _ ≤ A * (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
        (vinogradovAveragingRange X : ℝ) ^
          (-(16065 * (vinogradovTaylorDegree X F : ℝ) ^ 2 / 12648448) /
            ((GafniTao.fordVinogradovKappa (vinogradovTaylorDegree X F) *
              (2 * GafniTao.fordVinogradovKappa
                (vinogradovTaylorDegree X F)) : ℕ) : ℝ)) := by
      gcongr
    _ ≤ A * (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) * (2 * T) := by
      gcongr
    _ ≤ A * (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) * (2 * α * T) := by
      gcongr
      nlinarith [hα]
    _ = ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        ((2 * A) * α * T)) := by
      norm_num only [Nat.cast_pow]
      ring

end Tao2026
