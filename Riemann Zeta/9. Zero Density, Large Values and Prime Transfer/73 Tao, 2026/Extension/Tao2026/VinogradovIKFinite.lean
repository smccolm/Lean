import Tao2026.VinogradovIKFord
import Tao2026.VinogradovFiniteDegree

/-!
# Finite effective-degree branch

For `16 ≤ k < 10000`, the native critical VMVT coefficients form a finite
family.  This module absorbs their rooted coefficients into one explicit
finite sum and combines them with the stronger effective-degree coordinate
saving.
-/

namespace Tao2026

open scoped BigOperators NNReal

/-- Net scale saving in the effective-degree critical-moment argument. -/
noncomputable def vinogradovIKCriticalSaving (K : ℕ) : ℝ :=
  255 * (K : ℝ) ^ 2 / 25600 - 2 * vinogradovCriticalEpsilon K

theorem vinogradovIKCriticalSaving_pos {K : ℕ} (hK : 1 ≤ K) :
    0 < vinogradovIKCriticalSaving K := by
  unfold vinogradovIKCriticalSaving vinogradovCriticalEpsilon
  rw [show 255 * (K : ℝ) ^ 2 / 25600 -
      2 * ((255 * (K : ℝ) ^ 2 / 197632) / 128) =
      (255 / 25600 - 2 * (255 / 197632 / 128) : ℝ) * (K : ℝ) ^ 2 by ring]
  exact mul_pos (by norm_num) (sq_pos_of_pos (by positivity))

/-- Critical VMVT root extraction at the effective degree. -/
theorem source_bilinear_IKCritical_root_bound_of_meanValue
    {X F α C : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1)
    (hC : 0 < C)
    (hJ : ∀ V : ℕ, 1 ≤ V →
      (vinogradovMeanValueCount
        (GafniTao.fordVinogradovKappa (vinogradovIKDegree X F))
        (vinogradovIKDegree X F) V : ℝ) ≤
      C * (V : ℝ) ^
        ((GafniTao.fordVinogradovKappa (vinogradovIKDegree X F) : ℕ) +
          vinogradovCriticalEpsilon (vinogradovIKDegree X F))) :
    let K := vinogradovIKDegree X F
    let V := vinogradovAveragingRange X
    let ell := GafniTao.fordVinogradovKappa K
    let m := ell * (2 * ell)
    ‖vinogradovBilinearPolynomialSum c K V‖ ≤
      (C ^ 2 * (((3 * ell : ℕ) : ℝ) ^ (2 * K))) ^ (1 / (m : ℝ)) *
        (V : ℝ) ^ (2 : ℕ) *
        (V : ℝ) ^ (-vinogradovIKCriticalSaving K / (m : ℝ)) := by
  dsimp only
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := GafniTao.fordVinogradovKappa K
  let m := ell * (2 * ell)
  let δ : ℝ := 255 * (K : ℝ) ^ 2 / 25600
  let ε : ℝ := vinogradovCriticalEpsilon K
  let D : ℝ := C ^ 2 * (((3 * ell : ℕ) : ℝ) ^ (2 * K))
  have hKone : 1 ≤ K := by
    dsimp only [K]
    exact (show 1 ≤ 16 by norm_num).trans
      (sixteen_le_vinogradovIKDegree hX hFhigh)
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hell : 1 ≤ ell := GafniTao.fordVinogradovKappa_pos hKone
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (mul_ne_zero (by omega) (by omega)))
  have hP :=
    source_prod_coordinateSums_le_IKDegree_quarterSaving_mul_criticalPower
      (ell := ell) hX hFhigh hα hn hell hcoeff hsmall
  have hassembled :=
    powered_bilinear_critical_bound_of_meanValue_and_coordinate_bounds
      c K V hKone hV hC.le (ε := ε) (δ := δ)
        (A := (((3 * ell : ℕ) : ℝ) ^ (2 * K)))
        (by simpa only [K, V, ell, ε] using hJ V hV)
        (by
          rw [show (-(255 * (K : ℝ) ^ 2)) / 25600 = -δ by
            dsimp only [δ]; ring] at hP
          simpa only [K, V, ell, δ] using hP)
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hpow : ‖vinogradovBilinearPolynomialSum c K V‖ ^ m ≤
      D * (V : ℝ) ^ (((2 * m : ℕ) : ℝ) - vinogradovIKCriticalSaving K) := by
    dsimp only [K, V, ell, m, δ, ε, D] at hassembled ⊢
    convert hassembled using 1
    congr 2
    unfold vinogradovIKCriticalSaving
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hroot := le_root_mul_sq_mul_saving_of_pow_le hm
    (norm_nonneg _) hD hVpos hpow
  dsimp only [K, V, ell, m, D] at hroot ⊢
  exact hroot

/-- The finite rooted coefficient envelope for all effective degrees below
the explicit Ford cutoff. -/
noncomputable def vinogradovIKFiniteRootEnvelope : ℝ :=
  1 + ∑ K ∈ Finset.Ico 16 10000,
    vinogradovOptimalCriticalRootCoefficient K

theorem one_le_vinogradovIKFiniteRootEnvelope :
    1 ≤ vinogradovIKFiniteRootEnvelope := by
  unfold vinogradovIKFiniteRootEnvelope
  have hsum : 0 ≤ ∑ K ∈ Finset.Ico 16 10000,
      vinogradovOptimalCriticalRootCoefficient K :=
    Finset.sum_nonneg fun K _ =>
      vinogradovOptimalCriticalRootCoefficient_nonneg K
  linarith

theorem vinogradovOptimalCriticalRootCoefficient_le_IKFiniteEnvelope
    {K : ℕ} (hKlow : 16 ≤ K) (hKhigh : K < 10000) :
    vinogradovOptimalCriticalRootCoefficient K ≤
      vinogradovIKFiniteRootEnvelope := by
  have hmem : K ∈ Finset.Ico 16 10000 := Finset.mem_Ico.mpr ⟨hKlow, hKhigh⟩
  have hterm : vinogradovOptimalCriticalRootCoefficient K ≤
      ∑ r ∈ Finset.Ico 16 10000,
        vinogradovOptimalCriticalRootCoefficient r :=
    Finset.single_le_sum
      (fun r hr => vinogradovOptimalCriticalRootCoefficient_nonneg r) hmem
  unfold vinogradovIKFiniteRootEnvelope
  linarith

/-- The critical-moment effective-degree saving dominates the exact source
decay throughout the finite branch. -/
theorem vinogradovIKCritical_log_saving_ge_sourceTarget
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let K := vinogradovIKDegree X F
    let V := vinogradovAveragingRange X
    let ell := GafniTao.fordVinogradovKappa K
    let m := ell * (2 * ell)
    (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 / (Real.log F) ^ 2 ≤
      vinogradovIKCriticalSaving K / (m : ℝ) * Real.log V := by
  dsimp only
  let s := Real.log F / Real.log X
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := GafniTao.fordVinogradovKappa K
  let m := ell * (2 * ell)
  let d := (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
    (Real.log F) ^ 2
  let q : ℝ := (2 : ℝ) ^ (-18 : ℝ)
  let c₁ : ℝ := 255 / 25600 - 2 * (255 / 197632 / 128)
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
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
  have hnegD : -d =
      -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2 := by
    dsimp only [d]
    ring
  have htwoSmall : 1 * 2 * Real.exp (-d) < 1 := by
    calc
      1 * 2 * Real.exp (-d) = 2 * 1 * Real.exp (-d) := by ring
      _ ≤ 2 * α * Real.exp (-d) := by gcongr
      _ < 1 := by rw [hnegD]; exact hsmall
  have hlogTwoD : Real.log 2 < d :=
    log_lt_of_nontrivial_exponential_scale
      (C := (1 : ℝ)) (α := (2 : ℝ)) (d := d)
      (by norm_num) (by norm_num) htwoSmall
  have hq : q = (1 / 262144 : ℝ) := by dsimp only [q]; norm_num
  have hsSq : 16 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 4)]
  have hdUpper : d ≤ q * Real.log X / 16 := by
    rw [hdIdentity]
    have hinv : 1 / s ^ 2 ≤ (1 / 16 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hsSq
    rw [div_eq_mul_inv, div_eq_mul_inv]
    simpa only [one_div] using
      mul_le_mul_of_nonneg_left hinv (mul_nonneg (by positivity) hlogX.le)
  have hXsixteen : 16 ≤ X :=
    (sixteen_lt_of_nontrivialScale hX hFhigh hα hsmall).le
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
  have hKone : (1 : ℝ) ≤ K := by
    exact_mod_cast (show 1 ≤ K by
      dsimp only [K]
      exact (show 1 ≤ 16 by norm_num).trans
        (sixteen_le_vinogradovIKDegree hX hFhigh))
  have hKplus : (K : ℝ) + 1 ≤ 5 * s := by nlinarith
  have hellIdentity : (2 : ℝ) * (ell : ℝ) =
      (K : ℝ) * ((K : ℝ) + 1) := by
    dsimp only [ell]
    exact_mod_cast two_mul_fordVinogradovKappa K
  have hmIdentity : (m : ℝ) =
      (K : ℝ) ^ 2 * ((K : ℝ) + 1) ^ 2 / 2 := by
    dsimp only [m]
    push_cast
    nlinarith [sq_nonneg ((K : ℝ) * ((K : ℝ) + 1))]
  have hsavingIdentity : vinogradovIKCriticalSaving K / (m : ℝ) =
      2 * c₁ / ((K : ℝ) + 1) ^ 2 := by
    rw [hmIdentity]
    unfold vinogradovIKCriticalSaving vinogradovCriticalEpsilon
    dsimp only [c₁]
    field_simp
  have hplusSq : ((K : ℝ) + 1) ^ 2 ≤ 25 * s ^ 2 := by
    nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)
      hKplus 2]
  have hden : 0 < ((K : ℝ) + 1) ^ 2 := by positivity
  have hinv : 1 / (25 * s ^ 2) ≤ 1 / ((K : ℝ) + 1) ^ 2 :=
    one_div_le_one_div_of_le hden hplusSq
  have hc : 0 ≤ 2 * c₁ := by dsimp only [c₁]; norm_num
  have hratio : 2 * c₁ / (25 * s ^ 2) ≤
      vinogradovIKCriticalSaving K / (m : ℝ) := by
    rw [hsavingIdentity]
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hc
  have hnumeric : q ≤ (2 * c₁ / 25) * (9 / 40 : ℝ) := by
    rw [hq]
    dsimp only [c₁]
    norm_num
  have hscale : 0 ≤ Real.log X / s ^ 2 := by positivity
  have htarget : q * Real.log X / s ^ 2 ≤
      (2 * c₁ / (25 * s ^ 2)) * ((9 / 40 : ℝ) * Real.log X) := by
    calc
      q * Real.log X / s ^ 2 = q * (Real.log X / s ^ 2) := by ring
      _ ≤ ((2 * c₁ / 25) * (9 / 40 : ℝ)) *
          (Real.log X / s ^ 2) :=
        mul_le_mul_of_nonneg_right hnumeric hscale
      _ = (2 * c₁ / (25 * s ^ 2)) *
          ((9 / 40 : ℝ) * Real.log X) := by ring
  have hlogVnonneg : 0 ≤ Real.log (V : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast
      vinogradovAveragingRange_pos (show 1 ≤ X by linarith))
  dsimp only [d] at hdIdentity ⊢
  rw [hdIdentity]
  calc
    q * Real.log X / s ^ 2 ≤
        (2 * c₁ / (25 * s ^ 2)) * ((9 / 40 : ℝ) * Real.log X) := htarget
    _ ≤ (2 * c₁ / (25 * s ^ 2)) * Real.log (V : ℝ) := by
      gcongr
    _ ≤ (vinogradovIKCriticalSaving K / (m : ℝ)) * Real.log (V : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hlogVnonneg

/-- Finite-degree coefficient-only estimate with the exact source decay. -/
theorem source_bilinear_IKFinite_target_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hKsmall : vinogradovIKDegree X F < 10000)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (vinogradovIKFiniteRootEnvelope * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
  let K := vinogradovIKDegree X F
  let V := vinogradovAveragingRange X
  let ell := GafniTao.fordVinogradovKappa K
  let m := ell * (2 * ell)
  let d := (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
    (Real.log F) ^ 2
  let C := vinogradovOptimalCriticalCoefficient K
  have hKlow : 16 ≤ K := by
    dsimp only [K]
    exact sixteen_le_vinogradovIKDegree hX hFhigh
  have hKone : 1 ≤ K := by omega
  have hroot := source_bilinear_IKCritical_root_bound_of_meanValue
    hX hFhigh hα hn hcoeff hsmall
    (vinogradovOptimalCriticalCoefficient_pos hKone)
    (fun W hW => by
      simpa only [K, C] using
        vinogradovMeanValueCount_le_optimalCriticalCoefficient hKone hW)
  have hrootCoefficient :
      (C ^ 2 * (((3 * ell : ℕ) : ℝ) ^ (2 * K))) ^ (1 / (m : ℝ)) ≤
        vinogradovIKFiniteRootEnvelope := by
    have hfinite :=
      vinogradovOptimalCriticalRootCoefficient_le_IKFiniteEnvelope
        hKlow (by simpa only [K] using hKsmall)
    simpa only [vinogradovOptimalCriticalRootCoefficient, C, ell, m] using hfinite
  have hlogsaving := vinogradovIKCritical_log_saving_ge_sourceTarget
    hX hFhigh hα hsmall
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hlogsaving' : d ≤
      vinogradovIKCriticalSaving K / (m : ℝ) * Real.log (V : ℝ) := by
    simpa only [K, V, ell, m, d] using hlogsaving
  have hdecay : (V : ℝ) ^ (-vinogradovIKCriticalSaving K / (m : ℝ)) ≤
      Real.exp (-d) := by
    rw [Real.rpow_def_of_pos hVpos, Real.exp_le_exp]
    calc
      Real.log (V : ℝ) * (-vinogradovIKCriticalSaving K / (m : ℝ)) =
          -(vinogradovIKCriticalSaving K / (m : ℝ) * Real.log (V : ℝ)) := by ring
      _ ≤ -d := neg_le_neg hlogsaving'
  have hdecayAlpha : (V : ℝ) ^
      (-vinogradovIKCriticalSaving K / (m : ℝ)) ≤
      α * Real.exp (-d) :=
    hdecay.trans (by
      simpa only [one_mul] using
        (show 1 * Real.exp (-d) ≤ α * Real.exp (-d) by gcongr))
  have hA0 : 0 ≤ vinogradovIKFiniteRootEnvelope :=
    zero_le_one.trans one_le_vinogradovIKFiniteRootEnvelope
  dsimp only [K, V, ell, m] at hroot
  calc
    ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      (C ^ 2 * (((3 * ell : ℕ) : ℝ) ^ (2 * K))) ^ (1 / (m : ℝ)) *
        (V : ℝ) ^ (2 : ℕ) *
        (V : ℝ) ^ (-vinogradovIKCriticalSaving K / (m : ℝ)) := by
      simpa only [K, V, ell, m] using hroot
    _ ≤ vinogradovIKFiniteRootEnvelope * (V : ℝ) ^ (2 : ℕ) *
        (α * Real.exp (-d)) := by
      gcongr
    _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (vinogradovIKFiniteRootEnvelope * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
      dsimp only [V, d]
      norm_num
      ring_nf

/-- One absolute coefficient covering both the finite critical branch and
the explicit high-degree Ford branch. -/
noncomputable def vinogradovIKBilinearConstant : ℝ :=
  2 * max vinogradovIKFiniteRootEnvelope
    GafniTao.fordUniversalRootCoefficient

theorem one_le_vinogradovIKBilinearConstant :
    1 ≤ vinogradovIKBilinearConstant := by
  unfold vinogradovIKBilinearConstant
  have hmax : 1 ≤ max vinogradovIKFiniteRootEnvelope
      GafniTao.fordUniversalRootCoefficient :=
    one_le_vinogradovIKFiniteRootEnvelope.trans (le_max_left _ _)
  nlinarith

/-- Unconditional coefficient-only bilinear estimate at the effective
degree.  The complementary branch is the trivial cardinality estimate. -/
theorem source_bilinear_IK_uniform_bound
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovIKDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F) :
    ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (vinogradovIKBilinearConstant * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
  let E := Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2)
  let A := max vinogradovIKFiniteRootEnvelope
    GafniTao.fordUniversalRootCoefficient
  have hA : 1 ≤ A := by
    dsimp only [A]
    exact one_le_vinogradovIKFiniteRootEnvelope.trans (le_max_left _ _)
  have hE : 0 < E := Real.exp_pos _
  by_cases hsmall : 2 * α * E < 1
  · by_cases hK : 10000 ≤ vinogradovIKDegree X F
    · have hbound := source_bilinear_IKFord_target_bound_quarter
        hX hFhigh hα hn hK hcoeff (by simpa only [E] using hsmall)
      calc
        ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
            (vinogradovAveragingRange X)‖ ≤
          (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
            (GafniTao.fordUniversalRootCoefficient * α * E) := by
          simpa only [E] using hbound
        _ ≤ (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
            ((2 * A) * α * E) := by
          gcongr
          exact (le_max_right _ _).trans (by nlinarith [hA])
        _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
            (vinogradovIKBilinearConstant * α * Real.exp
              (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
                (Real.log F) ^ 2)) := by
          dsimp only [vinogradovIKBilinearConstant, A, E]
    · have hbound := source_bilinear_IKFinite_target_bound_quarter
        hX hFhigh hα hn (by omega) hcoeff (by simpa only [E] using hsmall)
      calc
        ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
            (vinogradovAveragingRange X)‖ ≤
          (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
            (vinogradovIKFiniteRootEnvelope * α * E) := by
          simpa only [E] using hbound
        _ ≤ (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
            ((2 * A) * α * E) := by
          gcongr
          exact (le_max_left _ _).trans (by nlinarith [hA])
        _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
            (vinogradovIKBilinearConstant * α * Real.exp
              (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
                (Real.log F) ^ 2)) := by
          dsimp only [vinogradovIKBilinearConstant, A, E]
  · have hOne : 1 ≤ 2 * α * E := le_of_not_gt hsmall
    calc
      ‖vinogradovBilinearPolynomialSum c (vinogradovIKDegree X F)
          (vinogradovAveragingRange X)‖ ≤
        (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) :=
        norm_vinogradovBilinearPolynomialSum_le _ _ _
      _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * 1 := by ring
      _ ≤ (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
          ((2 * A) * α * E) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg (show 0 ≤ A by linarith) (show 0 ≤ 2 * α * E by linarith)]
      _ = (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
          (vinogradovIKBilinearConstant * α * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log F) ^ 2)) := by
        dsimp only [vinogradovIKBilinearConstant, A, E]

end Tao2026
