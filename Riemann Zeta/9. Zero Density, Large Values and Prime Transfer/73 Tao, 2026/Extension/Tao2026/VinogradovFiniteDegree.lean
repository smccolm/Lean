import Tao2026.VinogradovUniform

/-!
# Finite Taylor-degree absorption

The native critical VMVT may have degree-dependent constants.  On the finite
range `40 ≤ R < 1000`, these constants can be combined into one literal real
envelope.  Consequently the genuinely quantitative residual begins only at
degree `R ≥ 1000`.
-/

namespace Tao2026

noncomputable section

open scoped BigOperators NNReal

def vinogradovCriticalEpsilon (R : ℕ) : ℝ :=
  (255 * (R : ℝ) ^ 2 / 197632) / 128

theorem vinogradovCriticalEpsilon_pos {R : ℕ} (hR : 1 ≤ R) :
    0 < vinogradovCriticalEpsilon R := by
  unfold vinogradovCriticalEpsilon
  positivity

/-- A canonical native critical-VMVT coefficient in each positive degree. -/
noncomputable def vinogradovNativeCriticalCoefficient (R : ℕ) : ℝ :=
  if hR : 1 ≤ R then
    Classical.choose
      (native_critical_vinogradovMeanValueCount_bound hR
        (vinogradovCriticalEpsilon_pos hR))
  else 1

theorem vinogradovNativeCriticalCoefficient_pos {R : ℕ} (hR : 1 ≤ R) :
    0 < vinogradovNativeCriticalCoefficient R := by
  rw [vinogradovNativeCriticalCoefficient, dif_pos hR]
  exact (Classical.choose_spec
    (native_critical_vinogradovMeanValueCount_bound hR
      (vinogradovCriticalEpsilon_pos hR))).1

theorem vinogradovMeanValueCount_le_nativeCriticalCoefficient
    {R V : ℕ} (hR : 1 ≤ R) (hV : 1 ≤ V) :
    (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
      vinogradovNativeCriticalCoefficient R * (V : ℝ) ^
        ((GafniTao.fordVinogradovKappa R : ℕ) +
          vinogradovCriticalEpsilon R) := by
  rw [vinogradovNativeCriticalCoefficient, dif_pos hR]
  exact (Classical.choose_spec
    (native_critical_vinogradovMeanValueCount_bound hR
      (vinogradovCriticalEpsilon_pos hR))).2 V hV

/-- All normalized coefficients required by the critical VMVT in degree `R`.
The supremum of this set is the least closed coefficient, avoiding any
dependence on which existential witness `Classical.choose` happens to select. -/
def vinogradovCriticalNormalizedCoefficientSet (R : ℕ) : Set ℝ :=
  {x | ∃ V : ℕ, 1 ≤ V ∧
    x = (vinogradovMeanValueCount
        (GafniTao.fordVinogradovKappa R) R V : ℝ) /
      (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) +
        vinogradovCriticalEpsilon R)}

theorem vinogradovCriticalNormalizedCoefficientSet_nonempty (R : ℕ) :
    (vinogradovCriticalNormalizedCoefficientSet R).Nonempty := by
  refine ⟨1, 1, by norm_num, ?_⟩
  simp [vinogradovMeanValueCount_one]

theorem vinogradovCriticalNormalizedCoefficientSet_bddAbove
    {R : ℕ} (hR : 1 ≤ R) :
    BddAbove (vinogradovCriticalNormalizedCoefficientSet R) := by
  refine ⟨vinogradovNativeCriticalCoefficient R, ?_⟩
  rintro x ⟨V, hV, rfl⟩
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hden : 0 < (V : ℝ) ^
      ((GafniTao.fordVinogradovKappa R : ℕ) +
        vinogradovCriticalEpsilon R) := Real.rpow_pos_of_pos hVpos _
  rw [div_le_iff₀ hden]
  exact vinogradovMeanValueCount_le_nativeCriticalCoefficient hR hV

/-- The optimal native critical-VMVT coefficient in degree `R`. -/
noncomputable def vinogradovOptimalCriticalCoefficient (R : ℕ) : ℝ :=
  sSup (vinogradovCriticalNormalizedCoefficientSet R)

theorem one_le_vinogradovOptimalCriticalCoefficient
    {R : ℕ} (hR : 1 ≤ R) :
    1 ≤ vinogradovOptimalCriticalCoefficient R := by
  unfold vinogradovOptimalCriticalCoefficient
  have hmem : (1 : ℝ) ∈ vinogradovCriticalNormalizedCoefficientSet R := by
    refine ⟨1, by norm_num, ?_⟩
    simp [vinogradovMeanValueCount_one]
  exact le_csSup (vinogradovCriticalNormalizedCoefficientSet_bddAbove hR) hmem

theorem vinogradovOptimalCriticalCoefficient_pos
    {R : ℕ} (hR : 1 ≤ R) :
    0 < vinogradovOptimalCriticalCoefficient R :=
  zero_lt_one.trans_le (one_le_vinogradovOptimalCriticalCoefficient hR)

theorem vinogradovMeanValueCount_le_optimalCriticalCoefficient
    {R V : ℕ} (hR : 1 ≤ R) (hV : 1 ≤ V) :
    (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
      vinogradovOptimalCriticalCoefficient R * (V : ℝ) ^
        ((GafniTao.fordVinogradovKappa R : ℕ) +
          vinogradovCriticalEpsilon R) := by
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hden : 0 < (V : ℝ) ^
      ((GafniTao.fordVinogradovKappa R : ℕ) +
        vinogradovCriticalEpsilon R) := Real.rpow_pos_of_pos hVpos _
  have hmem : (vinogradovMeanValueCount
      (GafniTao.fordVinogradovKappa R) R V : ℝ) /
      (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) +
        vinogradovCriticalEpsilon R) ∈
        vinogradovCriticalNormalizedCoefficientSet R := ⟨V, hV, rfl⟩
  have hs := le_csSup
    (vinogradovCriticalNormalizedCoefficientSet_bddAbove hR) hmem
  rw [div_le_iff₀ hden] at hs
  exact hs

theorem vinogradovOptimalCriticalCoefficient_le_of_meanValueBound
    {R : ℕ} {C : ℝ}
    (hmean : ∀ V : ℕ, 1 ≤ V →
      (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
        C * (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) +
          vinogradovCriticalEpsilon R)) :
    vinogradovOptimalCriticalCoefficient R ≤ C := by
  unfold vinogradovOptimalCriticalCoefficient
  apply csSup_le (vinogradovCriticalNormalizedCoefficientSet_nonempty R)
  rintro x ⟨V, hV, rfl⟩
  have hVpos : (0 : ℝ) < V := by exact_mod_cast hV
  have hden : 0 < (V : ℝ) ^
      ((GafniTao.fordVinogradovKappa R : ℕ) +
        vinogradovCriticalEpsilon R) := Real.rpow_pos_of_pos hVpos _
  rw [div_le_iff₀ hden]
  exact hmean V hV

/-- The least rooted coefficient actually consumed after the two critical
moments and the equation-(18) coordinate-box expansion. -/
noncomputable def vinogradovOptimalCriticalRootCoefficient (R : ℕ) : ℝ :=
  (vinogradovOptimalCriticalCoefficient R ^ 2 *
    (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
      (1 / ((GafniTao.fordVinogradovKappa R *
        (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ))

theorem vinogradovOptimalCriticalRootCoefficient_nonneg (R : ℕ) :
    0 ≤ vinogradovOptimalCriticalRootCoefficient R := by
  unfold vinogradovOptimalCriticalRootCoefficient
  positivity

theorem degree_le_fordVinogradovKappa {R : ℕ} (hR : 1 ≤ R) :
    R ≤ GafniTao.fordVinogradovKappa R := by
  have hid := two_mul_fordVinogradovKappa R
  have hprod : 2 * R ≤ R * (R + 1) := by nlinarith
  omega

/-- The coordinate-box part of the critical root is at most the absolute
factor `3`; it contributes no degree-dependent growth. -/
theorem vinogradovCriticalCoordinateRoot_le_three
    {R : ℕ} (hR : 1 ≤ R) :
    ((((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
        (1 / ((GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) ≤ 3 := by
  let K := GafniTao.fordVinogradovKappa R
  let m := K * (2 * K)
  have hK : 1 ≤ K := GafniTao.fordVinogradovKappa_pos hR
  have hm : 1 ≤ m := by
    dsimp only [m]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (by omega) (mul_ne_zero (by omega) (by omega)))
  have hinner : (((3 * K : ℕ) : ℝ) ^ (2 * R)) ≤ (3 : ℝ) ^ m := by
    have hRK : R ≤ K := by
      dsimp only [K]
      exact degree_le_fordVinogradovKappa hR
    have hbaseNat : 3 * K ≤ 3 ^ K := Nat.mul_le_pow (by norm_num) K
    have hbase : ((3 * K : ℕ) : ℝ) ≤ (3 : ℝ) ^ K := by
      exact_mod_cast hbaseNat
    calc
      ((3 * K : ℕ) : ℝ) ^ (2 * R) ≤ ((3 : ℝ) ^ K) ^ (2 * R) := by
        gcongr
      _ = (3 : ℝ) ^ (K * (2 * R)) := by rw [← pow_mul]
      _ ≤ (3 : ℝ) ^ (K * (2 * K)) := by
        gcongr
        norm_num
      _ = (3 : ℝ) ^ m := by rfl
  calc
    (((3 * K : ℕ) : ℝ) ^ (2 * R)) ^ (1 / (m : ℝ)) ≤
        ((3 : ℝ) ^ m) ^ (1 / (m : ℝ)) := by
      exact Real.rpow_le_rpow (by positivity) hinner (by positivity)
    _ = ((3 : ℝ) ^ (m : ℝ)) ^ (1 / (m : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = (3 : ℝ) ^ ((m : ℝ) * (1 / (m : ℝ))) := by
      rw [Real.rpow_mul (by positivity)]
    _ = 3 := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ _ hm0, Real.rpow_one]

/-- The coefficient-only part of the optimal critical root. -/
noncomputable def vinogradovOptimalCriticalVMVTRootCoefficient (R : ℕ) : ℝ :=
  (vinogradovOptimalCriticalCoefficient R ^ 2) ^
    (1 / ((GafniTao.fordVinogradovKappa R *
      (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ))

theorem vinogradovOptimalCriticalVMVTRootCoefficient_nonneg (R : ℕ) :
    0 ≤ vinogradovOptimalCriticalVMVTRootCoefficient R := by
  unfold vinogradovOptimalCriticalVMVTRootCoefficient
  positivity

/-- The coefficient-only critical root is exactly the `κ_R⁻²` power of the
optimal VMVT coefficient. -/
theorem vinogradovOptimalCriticalVMVTRootCoefficient_eq
    {R : ℕ} (hR : 1 ≤ R) :
    vinogradovOptimalCriticalVMVTRootCoefficient R =
      (vinogradovOptimalCriticalCoefficient R) ^
        (1 / ((GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ 2) := by
  let K := GafniTao.fordVinogradovKappa R
  have hK : 1 ≤ K := GafniTao.fordVinogradovKappa_pos hR
  have hopt : 0 ≤ vinogradovOptimalCriticalCoefficient R :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_vinogradovOptimalCriticalCoefficient hR)
  unfold vinogradovOptimalCriticalVMVTRootCoefficient
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hopt]
  congr 1
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  field_simp

/-- Consequently a uniform critical-root bound by `A` is exactly exponential
coefficient growth bounded by `A^(κ_R²)`. -/
theorem vinogradovOptimalCriticalVMVTRootCoefficient_le_iff
    {R : ℕ} (hR : 1 ≤ R) {A : ℝ} (hA : 1 ≤ A) :
    vinogradovOptimalCriticalVMVTRootCoefficient R ≤ A ↔
      vinogradovOptimalCriticalCoefficient R ≤
        A ^ (GafniTao.fordVinogradovKappa R ^ 2) := by
  rw [vinogradovOptimalCriticalVMVTRootCoefficient_eq hR]
  let K := GafniTao.fordVinogradovKappa R
  have hK : 1 ≤ K := GafniTao.fordVinogradovKappa_pos hR
  have hKsq : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
  have hopt : 0 ≤ vinogradovOptimalCriticalCoefficient R :=
    (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_vinogradovOptimalCriticalCoefficient hR)
  constructor
  · intro hroot
    have hp := Real.rpow_le_rpow (by positivity) hroot hKsq.le
    rw [← Real.rpow_mul (by positivity)] at hp
    have hcancel : (1 / (K : ℝ) ^ 2) * (K : ℝ) ^ 2 = 1 := by
      field_simp
    rw [hcancel, Real.rpow_one] at hp
    simpa only [K, ← Nat.cast_pow, Real.rpow_natCast] using hp
  · intro hcoefficient
    have hcoefficient' : vinogradovOptimalCriticalCoefficient R ≤
        A ^ ((K ^ 2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      simpa only [K] using hcoefficient
    have hp := Real.rpow_le_rpow hopt hcoefficient' (by positivity :
      0 ≤ 1 / (K : ℝ) ^ 2)
    rw [← Real.rpow_mul (zero_le_one.trans hA)] at hp
    norm_num only [Nat.cast_pow] at hp
    have hcancel : ((K : ℝ) ^ 2) * (1 / (K : ℝ) ^ 2) = 1 := by
      field_simp
    rw [hcancel, Real.rpow_one] at hp
    simpa only [K] using hp

theorem vinogradovOptimalCriticalRootCoefficient_le_three_mul_vmvtRoot
    {R : ℕ} (hR : 1 ≤ R) :
    vinogradovOptimalCriticalRootCoefficient R ≤
      3 * vinogradovOptimalCriticalVMVTRootCoefficient R := by
  unfold vinogradovOptimalCriticalRootCoefficient
    vinogradovOptimalCriticalVMVTRootCoefficient
  rw [Real.mul_rpow (sq_nonneg _ ) (by positivity)]
  have hcoordinate := vinogradovCriticalCoordinateRoot_le_three hR
  have hcoefficient :
      0 ≤ (vinogradovOptimalCriticalCoefficient R ^ 2) ^
        (1 / ((GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) := by positivity
  nlinarith

theorem one_le_vinogradovCriticalCoordinateRoot
    {R : ℕ} (hR : 1 ≤ R) :
    1 ≤ ((((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
      (1 / ((GafniTao.fordVinogradovKappa R *
        (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) := by
  have hK := GafniTao.fordVinogradovKappa_pos hR
  have hbaseNat : 1 ≤
      (3 * GafniTao.fordVinogradovKappa R) ^ (2 * R) :=
    Nat.one_le_pow _ _ (by omega)
  have hbase : (1 : ℝ) ≤
      (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R)) := by
    exact_mod_cast hbaseNat
  exact Real.one_le_rpow hbase (by positivity)

theorem vinogradovOptimalCriticalVMVTRootCoefficient_le_rootCoefficient
    {R : ℕ} (hR : 1 ≤ R) :
    vinogradovOptimalCriticalVMVTRootCoefficient R ≤
      vinogradovOptimalCriticalRootCoefficient R := by
  unfold vinogradovOptimalCriticalRootCoefficient
    vinogradovOptimalCriticalVMVTRootCoefficient
  rw [Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hcoordinate := one_le_vinogradovCriticalCoordinateRoot hR
  have hcoefficient :
      0 ≤ (vinogradovOptimalCriticalCoefficient R ^ 2) ^
        (1 / ((GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) := by positivity
  nlinarith

theorem vinogradovOptimalCriticalRootCoefficient_le_of_meanValueBound
    {R : ℕ} (hR : 1 ≤ R) {C : ℝ}
    (hmean : ∀ V : ℕ, 1 ≤ V →
      (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
        C * (V : ℝ) ^ ((GafniTao.fordVinogradovKappa R : ℕ) +
          vinogradovCriticalEpsilon R)) :
    vinogradovOptimalCriticalRootCoefficient R ≤
      (C ^ 2 * (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
        (1 / ((GafniTao.fordVinogradovKappa R *
          (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) := by
  unfold vinogradovOptimalCriticalRootCoefficient
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  gcongr
  · exact (show (0 : ℝ) ≤ 1 by norm_num).trans
      (one_le_vinogradovOptimalCriticalCoefficient hR)
  · exact vinogradovOptimalCriticalCoefficient_le_of_meanValueBound hmean

/-- One explicit finite envelope for every native critical coefficient below
degree `M`.  A sum is used instead of a finite maximum to keep membership
bookkeeping elementary. -/
noncomputable def vinogradovFiniteDegreeRootEnvelopeBelow (M : ℕ) : ℝ :=
  1 + ∑ R ∈ Finset.Ico 40 M,
    vinogradovOptimalCriticalRootCoefficient R

theorem one_le_vinogradovFiniteDegreeRootEnvelopeBelow (M : ℕ) :
    1 ≤ vinogradovFiniteDegreeRootEnvelopeBelow M := by
  unfold vinogradovFiniteDegreeRootEnvelopeBelow
  have hsum : 0 ≤ ∑ R ∈ Finset.Ico 40 M,
      vinogradovOptimalCriticalRootCoefficient R := by
    exact Finset.sum_nonneg fun R _ =>
      vinogradovOptimalCriticalRootCoefficient_nonneg R
  linarith

theorem vinogradovOptimalCriticalRootCoefficient_le_finiteEnvelopeBelow
    {R M : ℕ} (hRlow : 40 ≤ R) (hRhigh : R < M) :
    vinogradovOptimalCriticalRootCoefficient R ≤
      vinogradovFiniteDegreeRootEnvelopeBelow M := by
  have hmem : R ∈ Finset.Ico 40 M := by
    exact Finset.mem_Ico.mpr ⟨hRlow, hRhigh⟩
  have hterm : vinogradovOptimalCriticalRootCoefficient R ≤
      ∑ r ∈ Finset.Ico 40 M, vinogradovOptimalCriticalRootCoefficient r := by
    exact Finset.single_le_sum
      (fun r hr => vinogradovOptimalCriticalRootCoefficient_nonneg r) hmem
  unfold vinogradovFiniteDegreeRootEnvelopeBelow
  linarith

/-- The exact tail, starting at `M`, of the rooted coefficient problem. -/
def VinogradovCriticalRootCoefficientBoundFromAt (M : ℕ) (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, M ≤ R →
    ∃ C : ℝ, 0 < C ∧
      (∀ V : ℕ, 1 ≤ V →
        (vinogradovMeanValueCount (GafniTao.fordVinogradovKappa R) R V : ℝ) ≤
          C * (V : ℝ) ^
            ((GafniTao.fordVinogradovKappa R : ℕ) +
              vinogradovCriticalEpsilon R)) ∧
      (C ^ 2 * (((3 * GafniTao.fordVinogradovKappa R : ℕ) : ℝ) ^ (2 * R))) ^
          (1 / ((GafniTao.fordVinogradovKappa R *
            (2 * GafniTao.fordVinogradovKappa R) : ℕ) : ℝ)) ≤ A

/-- Finite-degree absorption glues a rooted tail estimate at any cutoff to the
full coefficient contract required in the source argument. -/
theorem vinogradovCriticalRootCoefficientBoundAt_of_from
    {M : ℕ} {A : ℝ} (hA : VinogradovCriticalRootCoefficientBoundFromAt M A) :
    VinogradovCriticalRootCoefficientBoundAt
      (max (vinogradovFiniteDegreeRootEnvelopeBelow M) A) := by
  refine ⟨((one_le_vinogradovFiniteDegreeRootEnvelopeBelow M).trans
    (le_max_left _ _)), ?_⟩
  intro R hR
  by_cases hRhigh : R < M
  · let C := vinogradovOptimalCriticalCoefficient R
    have hRone : 1 ≤ R := by omega
    refine ⟨C, vinogradovOptimalCriticalCoefficient_pos hRone, ?_, ?_⟩
    · intro V hV
      simpa only [C, vinogradovCriticalEpsilon] using
        vinogradovMeanValueCount_le_optimalCriticalCoefficient hRone hV
    · exact (vinogradovOptimalCriticalRootCoefficient_le_finiteEnvelopeBelow
        hR hRhigh).trans (le_max_left _ _)
  · obtain ⟨C, hC, hmean, hroot⟩ := hA.2 R (by omega)
    refine ⟨C, hC, ?_, hroot.trans (le_max_right _ _)⟩
    intro V hV
    simpa only [vinogradovCriticalEpsilon] using hmean V hV

/-- The scalar core of the remaining problem: the optimal rooted critical
coefficients are uniformly bounded on the tail. -/
def VinogradovOptimalCriticalRootCoefficientBoundFromAt
    (M : ℕ) (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, M ≤ R →
    vinogradovOptimalCriticalRootCoefficient R ≤ A

/-- The strictly VMVT part of the scalar tail residual, after removing the
uniformly bounded coordinate-box root. -/
def VinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt
    (M : ℕ) (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, M ≤ R →
    vinogradovOptimalCriticalVMVTRootCoefficient R ≤ A

/-- Equivalent unrooted formulation: the optimal coefficient may grow
exponentially in `κ_R²`, with one fixed base. -/
def VinogradovOptimalCriticalCoefficientGrowthBoundFromAt
    (M : ℕ) (A : ℝ) : Prop :=
  1 ≤ A ∧ ∀ R : ℕ, M ≤ R →
    vinogradovOptimalCriticalCoefficient R ≤
      A ^ (GafniTao.fordVinogradovKappa R ^ 2)

theorem vinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt_iff_growth
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M) :
    VinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt M A ↔
      VinogradovOptimalCriticalCoefficientGrowthBoundFromAt M A := by
  constructor
  · intro hA
    refine ⟨hA.1, ?_⟩
    intro R hR
    exact (vinogradovOptimalCriticalVMVTRootCoefficient_le_iff
      (hM.trans hR) hA.1).mp (hA.2 R hR)
  · intro hA
    refine ⟨hA.1, ?_⟩
    intro R hR
    exact (vinogradovOptimalCriticalVMVTRootCoefficient_le_iff
      (hM.trans hR) hA.1).mpr (hA.2 R hR)

theorem vinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt_of_full
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M)
    (hA : VinogradovOptimalCriticalRootCoefficientBoundFromAt M A) :
    VinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt M A := by
  refine ⟨hA.1, ?_⟩
  intro R hR
  exact (vinogradovOptimalCriticalVMVTRootCoefficient_le_rootCoefficient
    (hM.trans hR)).trans (hA.2 R hR)

theorem vinogradovOptimalCriticalRootCoefficientBoundFromAt_of_vmvt
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M)
    (hA : VinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt M A) :
    VinogradovOptimalCriticalRootCoefficientBoundFromAt M (3 * A) := by
  refine ⟨by nlinarith [hA.1], ?_⟩
  intro R hR
  calc
    vinogradovOptimalCriticalRootCoefficient R ≤
        3 * vinogradovOptimalCriticalVMVTRootCoefficient R :=
      vinogradovOptimalCriticalRootCoefficient_le_three_mul_vmvtRoot
        (hM.trans hR)
    _ ≤ 3 * A := by gcongr; exact hA.2 R hR

/-- The optimal coefficients turn the scalar tail bound into the full
existential tail contract. -/
theorem vinogradovCriticalRootCoefficientBoundFromAt_of_optimal
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M)
    (hA : VinogradovOptimalCriticalRootCoefficientBoundFromAt M A) :
    VinogradovCriticalRootCoefficientBoundFromAt M A := by
  refine ⟨hA.1, ?_⟩
  intro R hR
  have hRone : 1 ≤ R := hM.trans hR
  refine ⟨vinogradovOptimalCriticalCoefficient R,
    vinogradovOptimalCriticalCoefficient_pos hRone, ?_, hA.2 R hR⟩
  intro V hV
  simpa only [vinogradovCriticalEpsilon] using
    vinogradovMeanValueCount_le_optimalCriticalCoefficient hRone hV

/-- Conversely, any witness-based tail contract bounds the optimal rooted
coefficient. Thus the scalar formulation loses no mathematical content. -/
theorem vinogradovOptimalCriticalRootCoefficientBoundFromAt_of_contract
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M)
    (hA : VinogradovCriticalRootCoefficientBoundFromAt M A) :
    VinogradovOptimalCriticalRootCoefficientBoundFromAt M A := by
  refine ⟨hA.1, ?_⟩
  intro R hR
  have hRone : 1 ≤ R := hM.trans hR
  obtain ⟨C, hC, hmean, hroot⟩ := hA.2 R hR
  exact (vinogradovOptimalCriticalRootCoefficient_le_of_meanValueBound
    hRone hmean).trans hroot

theorem vinogradovCriticalRootCoefficientBoundFromAt_iff_optimal
    {M : ℕ} {A : ℝ} (hM : 1 ≤ M) :
    VinogradovCriticalRootCoefficientBoundFromAt M A ↔
      VinogradovOptimalCriticalRootCoefficientBoundFromAt M A :=
  ⟨vinogradovOptimalCriticalRootCoefficientBoundFromAt_of_contract hM,
    vinogradovCriticalRootCoefficientBoundFromAt_of_optimal hM⟩

/-- The concrete cutoff used by the current Tao development. -/
noncomputable abbrev vinogradovFiniteDegreeRootEnvelope : ℝ :=
  vinogradovFiniteDegreeRootEnvelopeBelow 1000

theorem one_le_vinogradovFiniteDegreeRootEnvelope :
    1 ≤ vinogradovFiniteDegreeRootEnvelope :=
  one_le_vinogradovFiniteDegreeRootEnvelopeBelow 1000

theorem vinogradovOptimalCriticalRootCoefficient_le_finiteEnvelope
    {R : ℕ} (hRlow : 40 ≤ R) (hRhigh : R < 1000) :
    vinogradovOptimalCriticalRootCoefficient R ≤
      vinogradovFiniteDegreeRootEnvelope :=
  vinogradovOptimalCriticalRootCoefficient_le_finiteEnvelopeBelow hRlow hRhigh

/-- The exact large-degree remainder at the concrete cutoff `1000`. -/
abbrev VinogradovCriticalRootCoefficientBoundFrom1000At (A : ℝ) : Prop :=
  VinogradovCriticalRootCoefficientBoundFromAt 1000 A

abbrev VinogradovOptimalCriticalRootCoefficientBoundFrom1000At (A : ℝ) : Prop :=
  VinogradovOptimalCriticalRootCoefficientBoundFromAt 1000 A

abbrev VinogradovOptimalCriticalVMVTRootCoefficientBoundFrom1000At
    (A : ℝ) : Prop :=
  VinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt 1000 A

abbrev VinogradovOptimalCriticalCoefficientGrowthBoundFrom1000At
    (A : ℝ) : Prop :=
  VinogradovOptimalCriticalCoefficientGrowthBoundFromAt 1000 A

theorem vinogradovCriticalRootCoefficientBoundAt_of_from1000
    {A : ℝ} (hA : VinogradovCriticalRootCoefficientBoundFrom1000At A) :
    VinogradovCriticalRootCoefficientBoundAt
      (max vinogradovFiniteDegreeRootEnvelope A) :=
  vinogradovCriticalRootCoefficientBoundAt_of_from hA

/-- Therefore the large-degree rooted estimate alone closes the nontrivial
polynomial bilinear contract, with one explicit finite-prefix envelope. -/
theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_from1000
    {A : ℝ} (hA : VinogradovCriticalRootCoefficientBoundFrom1000At A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt
      (2 * max vinogradovFiniteDegreeRootEnvelope A) :=
  vinogradovBilinearPolynomialNontrivialEstimateAt_of_rootCoefficient
    (vinogradovCriticalRootCoefficientBoundAt_of_from1000 hA)

/-- Source-facing conclusion from only the scalar rooted bound on the optimal
coefficient sequence for `R ≥ 1000`. -/
theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_optimal_from1000
    {A : ℝ}
    (hA : VinogradovOptimalCriticalRootCoefficientBoundFrom1000At A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt
      (2 * max vinogradovFiniteDegreeRootEnvelope A) :=
  vinogradovBilinearPolynomialNontrivialEstimateAt_of_from1000
    (vinogradovCriticalRootCoefficientBoundFromAt_of_optimal (by norm_num) hA)

/-- The final bilinear consumer needs only the coefficient part of the
critical root; the coordinate-box root costs the absolute factor `3`. -/
theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_vmvtRoot_from1000
    {A : ℝ}
    (hA : VinogradovOptimalCriticalVMVTRootCoefficientBoundFrom1000At A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt
      (2 * max vinogradovFiniteDegreeRootEnvelope (3 * A)) :=
  vinogradovBilinearPolynomialNontrivialEstimateAt_of_optimal_from1000
    (vinogradovOptimalCriticalRootCoefficientBoundFromAt_of_vmvt
      (by norm_num) hA)

/-- Source-facing conclusion in the exact unrooted growth formulation. -/
theorem vinogradovBilinearPolynomialNontrivialEstimateAt_of_coefficientGrowth_from1000
    {A : ℝ}
    (hA : VinogradovOptimalCriticalCoefficientGrowthBoundFrom1000At A) :
    VinogradovBilinearPolynomialNontrivialEstimateAt
      (2 * max vinogradovFiniteDegreeRootEnvelope (3 * A)) :=
  vinogradovBilinearPolynomialNontrivialEstimateAt_of_vmvtRoot_from1000
    ((vinogradovOptimalCriticalVMVTRootCoefficientBoundFromAt_iff_growth
      (by norm_num)).mpr hA)

end

end Tao2026
