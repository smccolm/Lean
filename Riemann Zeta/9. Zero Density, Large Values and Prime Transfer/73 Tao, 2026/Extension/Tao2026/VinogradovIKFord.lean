import Tao2026.VinogradovIKMeanValue
import Tao2026.VinogradovFord

/-!
# Explicit Ford moment at the effective IK degree

The explicit full-range Ford moment is now applied to
`vinogradovIKDegree`, while the coordinate saving comes from the effective
quarter window.  This is the uniform high-degree branch of the classical
Vinogradov estimate.
-/

namespace Tao2026

open scoped BigOperators NNReal

/-- Net effective-degree scale saving after paying twice for Ford's
permissible exponent. -/
noncomputable def vinogradovIKFordSaving (K : ℕ) : ℝ :=
  (255 / 25600 - 3 / 4000 : ℝ) * (K : ℝ) ^ 2

theorem vinogradovIKFordSaving_pos {K : ℕ} (hK : 1 ≤ K) :
    0 < vinogradovIKFordSaving K := by
  unfold vinogradovIKFordSaving
  positivity

/-- Equation (18), the effective quarter-window coordinate bound, and the
explicit full-range Ford moment. -/
theorem source_powered_bilinear_IKFord_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hKlarge : 10000 ≤ vinogradovIKDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let K := vinogradovIKDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier K * K
    ‖vinogradovBilinearPolynomialSum c K V‖ ^ (ell * (2 * ell)) ≤
      (GafniTao.fordMomentCoefficient36 K
          (vinogradovFordFullMultiplier K - 1)) ^ 2 *
        (((3 * ell : ℕ) : ℝ) ^ (2 * K)) *
        (V : ℝ) ^
          ((4 * ell ^ 2 : ℕ) +
            2 * ((3 / 8000 : ℝ) * (K : ℝ) ^ 2) -
              255 * (K : ℝ) ^ 2 / 25600) := by
  dsimp only
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier K * K
  let C := GafniTao.fordMomentCoefficient36 K
    (vinogradovFordFullMultiplier K - 1)
  let Δ : ℝ := (3 / 8000) * (K : ℝ) ^ 2
  let δ : ℝ := 255 * (K : ℝ) ^ 2 / 25600
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hell : 1 ≤ ell := by
    dsimp only [ell, vinogradovFordFullMultiplier]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))
  have hmoment : GafniTao.FordVinogradovMomentBound ell K C Δ := by
    dsimp only [ell, K, C, Δ]
    exact vinogradovFord_full_moment hKlarge
  have hJraw := vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
    hmoment V hV
  have hJ : (vinogradovMeanValueCount ell K V : ℝ) ≤
      C * (V : ℝ) ^
        (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa K + Δ) := by
    simpa only [GafniTao.fordLambda34,
      GafniTao.fordVinogradovKappa_cast] using hJraw
  have hP :=
    source_prod_coordinateSums_le_IKDegree_quarterSaving_mul_criticalPower
      (ell := ell) hX hFhigh hα hn hell hcoeff hsmall
  have hassembled :=
    powered_bilinear_supercritical_bound_of_meanValue_and_coordinate_bounds
      c K V ell hV hell (C := C) (Δ := Δ) (δ := δ)
        (A := (((3 * ell : ℕ) : ℝ) ^ (2 * K)))
        (zero_le_one.trans hmoment.one_le_coefficient) hJ
        (by simpa only [K, V, δ, neg_div] using hP)
  dsimp only [K, V, ell, C, Δ, δ] at hassembled ⊢
  exact hassembled

/-- Exact root extraction from the effective-degree Ford moment. -/
theorem source_bilinear_IKFord_root_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hKlarge : 10000 ≤ vinogradovIKDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let K := vinogradovIKDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier K * K
    let m := ell * (2 * ell)
    let D :=
      (GafniTao.fordMomentCoefficient36 K
          (vinogradovFordFullMultiplier K - 1)) ^ 2 *
        (((3 * ell : ℕ) : ℝ) ^ (2 * K))
    ‖vinogradovBilinearPolynomialSum c K V‖ ≤
      D ^ (1 / (m : ℝ)) * (V : ℝ) ^ (2 : ℕ) *
        (V : ℝ) ^ (-vinogradovIKFordSaving K / (m : ℝ)) := by
  dsimp only
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier K * K
  let m := ell * (2 * ell)
  let D : ℝ :=
    (GafniTao.fordMomentCoefficient36 K
        (vinogradovFordFullMultiplier K - 1)) ^ 2 *
      (((3 * ell : ℕ) : ℝ) ^ (2 * K))
  have hpow := source_powered_bilinear_IKFord_bound_quarter
    hX hFhigh hα hn hKlarge hcoeff hsmall
  have hm : 1 ≤ m := by
    dsimp only [m, ell, vinogradovFordFullMultiplier]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))
        (mul_ne_zero (by norm_num)
          (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))))
  have hV : (0 : ℝ) < V := by
    exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpow' :
      ‖vinogradovBilinearPolynomialSum c K V‖ ^ m ≤
        D * (V : ℝ) ^ (((2 * m : ℕ) : ℝ) - vinogradovIKFordSaving K) := by
    dsimp only [K, V, ell, m, D] at hpow ⊢
    convert hpow using 1
    congr 2
    unfold vinogradovIKFordSaving
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hroot := le_root_mul_sq_mul_saving_of_pow_le hm
    (norm_nonneg _) hD hV hpow'
  dsimp only [K, V, ell, m, D] at hroot ⊢
  exact hroot

/-- The coefficient extracted from the effective Ford moment is bounded by
the same absolute universal constant. -/
theorem source_bilinear_IKFord_uniform_root_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hKlarge : 10000 ≤ vinogradovIKDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let K := vinogradovIKDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier K * K
    let m := ell * (2 * ell)
    ‖vinogradovBilinearPolynomialSum c K V‖ ≤
      GafniTao.fordUniversalRootCoefficient * (V : ℝ) ^ (2 : ℕ) *
        (V : ℝ) ^ (-vinogradovIKFordSaving K / (m : ℝ)) := by
  dsimp only
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier K * K
  let m := ell * (2 * ell)
  let D : ℝ :=
    (GafniTao.fordMomentCoefficient36 K
        (vinogradovFordFullMultiplier K - 1)) ^ 2 *
      (((3 * ell : ℕ) : ℝ) ^ (2 * K))
  have hroot := source_bilinear_IKFord_root_bound_quarter
    hX hFhigh hα hn hKlarge hcoeff hsmall
  have hDroot : D ^ (1 / (m : ℝ)) ≤
      GafniTao.fordUniversalRootCoefficient := by
    dsimp only [D, m, ell, K]
    exact vinogradovFord_full_root_coefficient_le_absolute hKlarge
  dsimp only [K, V, ell, m, D] at hroot ⊢
  exact hroot.trans (by gcongr)

/-- In the nontrivial branch, the effective Ford root saving dominates the
literal source exponent `2^-18 log(X)^3/log(F)^2`. -/
theorem vinogradovIKFord_log_saving_ge_sourceTarget
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hKlarge : 10000 ≤ vinogradovIKDegree X F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let K := vinogradovIKDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier K * K
    let m := ell * (2 * ell)
    (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 / (Real.log F) ^ 2 ≤
      vinogradovIKFordSaving K / (m : ℝ) * Real.log V := by
  dsimp only
  let s := Real.log F / Real.log X
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier K * K
  let m := ell * (2 * ell)
  let d := (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
    (Real.log F) ^ 2
  let q : ℝ := (2 : ℝ) ^ (-18 : ℝ)
  let c₀ : ℝ := 255 / 25600 - 3 / 4000
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := by
    apply Real.log_pos
    calc
      1 < (2 : ℝ) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
      _ ≤ F := hFhigh
  have hs : 4 ≤ s := by
    simpa only [s] using four_le_vinogradov_log_ratio hX hFhigh
  have hspos : 0 < s := by linarith
  have hlogIdentity : Real.log F = s * Real.log X := by
    dsimp only [s]
    field_simp
  have hdIdentity : d = q * Real.log X / s ^ 2 := by
    dsimp only [d, q]
    rw [hlogIdentity]
    field_simp
  have htwoSmall : 1 * 2 * Real.exp (-d) < 1 := by
    calc
      1 * 2 * Real.exp (-d) = 2 * 1 * Real.exp (-d) := by ring
      _ ≤ 2 * α * Real.exp (-d) := by gcongr
      _ < 1 := by
        convert hsmall using 1
        dsimp only [d]
        ring_nf
  have hlogTwoD : Real.log 2 < d :=
    log_lt_of_nontrivial_exponential_scale
      (C := (1 : ℝ)) (α := (2 : ℝ)) (d := d)
      (by norm_num) (by norm_num) htwoSmall
  have hq : q = (1 / 262144 : ℝ) := by
    dsimp only [q]
    norm_num
  have hsSq : 16 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 4)]
  have hdUpper : d ≤ q * Real.log X / 16 := by
    rw [hdIdentity]
    have hinv : 1 / s ^ 2 ≤ (1 / 16 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hsSq
    rw [div_eq_mul_inv, div_eq_mul_inv]
    simpa only [one_div] using
      mul_le_mul_of_nonneg_left hinv (mul_nonneg (by positivity) hlogX.le)
  have hXsixteen : 16 ≤ X := by
    by_contra hnot
    have hXlt : X < 16 := lt_of_not_ge hnot
    have hlogLt : Real.log X < 4 * Real.log 2 := by
      have hmono := Real.strictMonoOn_log
        (Set.mem_Ioi.mpr hXpos) (by norm_num : (16 : ℝ) ∈ Set.Ioi 0) hXlt
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hmono
      norm_num at hmono ⊢
      exact hmono
    rw [hq] at hdUpper
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have hlogVbounds := log_vinogradovAveragingRange_bounds hXsixteen
  have hlogV : (9 / 40 : ℝ) * Real.log X < Real.log (V : ℝ) := by
    have hlower : Real.log X / 4 - Real.log 2 < Real.log (V : ℝ) := by
      simpa only [V] using hlogVbounds.1
    have htwoUpper : Real.log 2 < q * Real.log X / 16 :=
      hlogTwoD.trans_le hdUpper
    rw [hq] at htwoUpper
    nlinarith
  have hK : (K : ℝ) ≤ 4 * s := by
    simpa only [K, s] using vinogradovIKDegree_cast_le hX hFhigh
  have hKpos : (0 : ℝ) < K := by positivity
  have hKsq : (K : ℝ) ^ 2 ≤ 16 * s ^ 2 := by
    nlinarith [pow_le_pow_left₀ hKpos.le hK 2]
  have hmIdentity : (m : ℝ) = 32 * (K : ℝ) ^ 4 := by
    dsimp only [m, ell, vinogradovFordFullMultiplier]
    push_cast
    ring
  have hsavingIdentity : vinogradovIKFordSaving K / (m : ℝ) =
      c₀ / (32 * (K : ℝ) ^ 2) := by
    rw [hmIdentity]
    unfold vinogradovIKFordSaving
    dsimp only [c₀]
    field_simp
  have hden : 32 * (K : ℝ) ^ 2 ≤ 512 * s ^ 2 := by nlinarith
  have hinv : 1 / (512 * s ^ 2) ≤ 1 / (32 * (K : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hc : 0 ≤ c₀ := by dsimp only [c₀]; norm_num
  have hratio : c₀ / (512 * s ^ 2) ≤
      vinogradovIKFordSaving K / (m : ℝ) := by
    rw [hsavingIdentity]
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc
  have hnumeric : q ≤ c₀ / 512 * (9 / 40 : ℝ) := by
    rw [hq]
    dsimp only [c₀]
    norm_num
  have htarget : q * Real.log X / s ^ 2 ≤
      (c₀ / (512 * s ^ 2)) * ((9 / 40 : ℝ) * Real.log X) := by
    have hscale : 0 ≤ Real.log X / s ^ 2 := by positivity
    calc
      q * Real.log X / s ^ 2 = q * (Real.log X / s ^ 2) := by ring
      _ ≤ (c₀ / 512 * (9 / 40 : ℝ)) *
          (Real.log X / s ^ 2) :=
        mul_le_mul_of_nonneg_right hnumeric hscale
      _ = (c₀ / (512 * s ^ 2)) *
          ((9 / 40 : ℝ) * Real.log X) := by ring
  have hlogVnonneg : 0 ≤ Real.log (V : ℝ) := by
    have hV : 1 ≤ V := by
      dsimp only [V]
      exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
    exact Real.log_nonneg (by exact_mod_cast hV)
  dsimp only [d] at hdIdentity ⊢
  rw [hdIdentity]
  calc
    q * Real.log X / s ^ 2 ≤
        (c₀ / (512 * s ^ 2)) * ((9 / 40 : ℝ) * Real.log X) := htarget
    _ ≤ (c₀ / (512 * s ^ 2)) * Real.log (V : ℝ) := by
      gcongr
    _ ≤ (vinogradovIKFordSaving K / (m : ℝ)) * Real.log (V : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hlogVnonneg

/-- High-degree coefficient-only estimate with the exact source decay. -/
theorem source_bilinear_IKFord_target_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hKlarge : 10000 ≤ vinogradovIKDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (GafniTao.fordUniversalRootCoefficient * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier K * K
  let m := ell * (2 * ell)
  let d := (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
    (Real.log F) ^ 2
  have hroot := source_bilinear_IKFord_uniform_root_bound_quarter
    hX hFhigh hα hn hKlarge hcoeff hsmall
  have hlogsaving := vinogradovIKFord_log_saving_ge_sourceTarget
    hX hFhigh hα hKlarge hsmall
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hlogsaving' : d ≤
      vinogradovIKFordSaving K / (m : ℝ) * Real.log (V : ℝ) := by
    simpa only [K, V, ell, m, d] using hlogsaving
  have hdecay : (V : ℝ) ^ (-vinogradovIKFordSaving K / (m : ℝ)) ≤
      Real.exp (-d) := by
    rw [Real.rpow_def_of_pos hVpos, Real.exp_le_exp]
    calc
      Real.log (V : ℝ) * (-vinogradovIKFordSaving K / (m : ℝ)) =
          -(vinogradovIKFordSaving K / (m : ℝ) * Real.log (V : ℝ)) := by ring
      _ ≤ -d := neg_le_neg hlogsaving'
  have hαexp : Real.exp (-d) ≤ α * Real.exp (-d) := by
    simpa only [one_mul] using
      (show 1 * Real.exp (-d) ≤ α * Real.exp (-d) by gcongr)
  have hdecayAlpha :
      (vinogradovAveragingRange X : ℝ) ^
          (-vinogradovIKFordSaving (vinogradovIKDegree X F) /
            (((vinogradovFordFullMultiplier (vinogradovIKDegree X F) *
              vinogradovIKDegree X F) *
              (2 * (vinogradovFordFullMultiplier (vinogradovIKDegree X F) *
                vinogradovIKDegree X F)) : ℕ) : ℝ)) ≤
        α * Real.exp (-d) := by
    simpa only [K, V, ell, m] using hdecay.trans hαexp
  have hfront0 : 0 ≤ GafniTao.fordUniversalRootCoefficient *
      (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) := by
    unfold GafniTao.fordUniversalRootCoefficient
    positivity
  have hexpD : Real.exp (-d) = Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) := by
    congr 1
    dsimp only [d]
    ring
  dsimp only [K, V, ell, m] at hroot
  calc
    ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      GafniTao.fordUniversalRootCoefficient *
          (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
        (vinogradovAveragingRange X : ℝ) ^
          (-vinogradovIKFordSaving (vinogradovIKDegree X F) /
            (((vinogradovFordFullMultiplier (vinogradovIKDegree X F) *
              vinogradovIKDegree X F) *
              (2 * (vinogradovFordFullMultiplier (vinogradovIKDegree X F) *
                vinogradovIKDegree X F)) : ℕ) : ℝ)) := hroot
    _ ≤ GafniTao.fordUniversalRootCoefficient *
          (vinogradovAveragingRange X : ℝ) ^ (2 : ℕ) *
        (α * Real.exp (-d)) :=
      mul_le_mul_of_nonneg_left hdecayAlpha hfront0
    _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (GafniTao.fordUniversalRootCoefficient * α * Real.exp (-d)) := by
      norm_num
      ring
    _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (GafniTao.fordUniversalRootCoefficient * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by rw [hexpD]

end Tao2026
