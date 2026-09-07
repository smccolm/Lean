import PrimeShell.XiSourceBoundary
import Zeta23.XiPrime.FamilyHyps
import Zeta23.XiPrime.ExplicitFormula.FamilyFacts

namespace PrimeShell

noncomputable section

open Filter Function MeasureTheory Set
open Zeta23

/-- Window regularity for the complete explicit-formula range.  This is
the released `XiPrime.FamilyHyps` with its hard-coded `λ < 1` field
replaced by the inequality actually required by the contour displacement,
`3λ < 4`.  No source theorem is asserted merely by defining this class. -/
structure ExtendedFamilyHyps (Pf : ℝ → Params) : Prop where
  lam_const : ∃ lam : ℝ, 0 < lam ∧ 3 * lam < 4 ∧ ∀ T, (Pf T).lam = lam
  window : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ContDiff ℝ 3 ((Pf T).phi T) ∧
    tsupport ((Pf T).phi T) ⊆ Icc (-((Pf T).L T / 2)) ((Pf T).L T / 2) ∧
    (∀ u : ℝ, (Pf T).phi T (-u) = (Pf T).phi T u) ∧
    (∀ u : ℝ, |(Pf T).phi T u| ≤ 1) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 3 →
      Integrable (iteratedDeriv j ((Pf T).phi T)) ∧
      ∫ u : ℝ, |iteratedDeriv j ((Pf T).phi T) u| ≤ C)

/-- The actual smoothstep family at every full-chain-admissible fixed
parameter satisfies the extended window class.  The proof uses only taper
regularity, `w ≥ 1`, eventual `8w ≤ L`, and positivity of `λ`. -/
theorem extendedFamilyHyps_flat (A : PrimeShellFullChainAdmissible) :
    ExtendedFamilyHyps (fun _ => A.toPrimeShellAdmissible.P) := by
  let P := A.toPrimeShellAdmissible.P
  have hTaper : TaperProfile P.ϱ := A.toPrimeShellAdmissible.taper
  have hLamPos : 0 < P.lam := A.toPrimeShellAdmissible.lambda_pos
  have hThree : 3 * P.lam < 4 := A.three_mul_lam_lt_four
  have hWOne : 1 ≤ P.w := A.toPrimeShellAdmissible.one_le_w
  have hWPos : 0 < P.w := one_pos.trans_le hWOne
  obtain ⟨B, hB0, hB⟩ :=
    Zeta23.XiPrime.FamilyHypsC3.exists_deriv_bound hTaper
  refine ⟨⟨P.lam, hLamPos, hThree, fun _ => rfl⟩, ?_⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    ((Zeta23.Assembly.tendsto_L_atTop P hLamPos).eventually_ge_atTop (8 * P.w))
  refine ⟨2 * B, T₀, fun T hT => ?_⟩
  have hEight : 8 * P.w ≤ P.L T := hT₀ T hT
  have hTwo : 2 * P.w ≤ P.L T := by linarith [hWOne]
  have hcd : ContDiff ℝ 3 (P.phi T) :=
    Taper.phi_contDiff hTaper hWPos hTwo
  refine ⟨hcd,
    closure_minimal (Taper.phi_support_subset hTaper hWPos) isClosed_Icc,
    fun u => Taper.phi_even u,
    fun u => abs_le.mpr ⟨by
      have hnonneg : 0 ≤ P.phi T u :=
        Taper.phi_nonneg hTaper (L := P.L T) (w := P.w) u
      change -(1 : ℝ) ≤ P.phi T u
      linarith,
      by
        change P.phi T u ≤ 1
        exact Taper.phi_le_one hTaper u⟩,
    fun j hjOne hjThree => ⟨?_, ?_⟩⟩
  · exact (hcd.continuous_iteratedDeriv j (by exact_mod_cast hjThree)).integrable_of_hasCompactSupport
      (Zeta23.XiPrime.FamilyHypsC3.hasCompactSupport_iteratedDeriv'
        (Taper.phi_hasCompactSupport hTaper hWPos) j)
  · have hbound :=
      Zeta23.XiPrime.FamilyHypsC3.integral_abs_iteratedDeriv_phi_le
        (L := P.L T) (w := P.w) hTaper hB0 hB hWPos hTwo hjOne hjThree
    refine hbound.trans ?_
    have hpow : (P.w⁻¹) ^ j * P.w ≤ 1 := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hWPos.ne', mul_one]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hWOne)
    nlinarith

theorem concrete_extendedFamilyHyps :
    ExtendedFamilyHyps (fun _ => concretePrimeShellParams) := by
  simpa [concretePrimeShellMRTFullChainAdmissible,
    concretePrimeShellFullChainAdmissible, concretePrimeShellAdmissible] using
    extendedFamilyHyps_flat
      concretePrimeShellMRTFullChainAdmissible.toPrimeShellFullChainAdmissible

/-- Per-height consequences of the extended family.  Unlike the released
`FamilyHyps.perT`, the logarithmic support estimate retains the factor
`λ`; this is the exact statement valid when `1 < λ < 4/3`. -/
theorem ExtendedFamilyHyps.perT {Pf : ℝ → Params}
    (hPf : ExtendedFamilyHyps Pf) :
    ∃ lam C T₁ : ℝ, 0 < lam ∧ 3 * lam < 4 ∧ 0 ≤ C ∧ 0 < T₁ ∧
      ∀ T : ℝ, T₁ ≤ T →
        (Pf T).lam = lam ∧
        1 ≤ (Pf T).L T ∧
        (Pf T).L T = lam * l T ∧
        (Pf T).X T = Real.exp ((Pf T).L T) ∧
        (Pf T).L T ≤ lam * Real.log T ∧
        (Pf T).X T ^ (3 / 4 : ℝ) ≤ T ^ (3 * lam / 4) ∧
        ContDiff ℝ 2 (fun u : ℝ => (((Pf T).phi T u : ℝ) : ℂ)) ∧
        tsupport ((Pf T).phi T) ⊆
          Icc (-((Pf T).L T / 2)) ((Pf T).L T / 2) ∧
        0 < (Pf T).L T ∧
        (∀ u : ℝ, (Pf T).phi T (-u) = (Pf T).phi T u) ∧
        (∀ u : ℝ, |(Pf T).phi T u| ≤ 1) ∧
        (∀ j : ℕ, 1 ≤ j → j ≤ 3 →
          Integrable (iteratedDeriv j ((Pf T).phi T)) ∧
          ∫ u : ℝ, |iteratedDeriv j ((Pf T).phi T) u| ≤ C) := by
  obtain ⟨lam, hlam0, hlam4, hlam⟩ := hPf.lam_const
  obtain ⟨C, T₀, hwin⟩ := hPf.window
  have hC0 : 0 ≤ C := by
    have h := (hwin (max T₀ 0) (le_max_left _ _)).2.2.2.2
      1 le_rfl (by norm_num)
    exact le_trans (integral_nonneg fun u => abs_nonneg _) h.2
  set T₁ : ℝ := max (max T₀ 1) (2 * Real.pi * Real.exp (1 / lam))
  have hTwoPi : 0 < 2 * Real.pi := by positivity
  refine ⟨lam, C, T₁, hlam0, hlam4, hC0, ?_, fun T hT => ?_⟩
  · exact lt_of_lt_of_le one_pos
      (le_trans (le_max_right _ _) (le_max_left _ _))
  have hT₀ : T₀ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTOne : 1 ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hTpos : 0 < T := by linarith
  have hTexp : 2 * Real.pi * Real.exp (1 / lam) ≤ T :=
    le_trans (le_max_right _ _) hT
  obtain ⟨hcd, hsupp, heven, hleOne, hderiv⟩ := hwin T hT₀
  have hLdef : (Pf T).L T = lam * l T := by
    rw [Params.L, hlam T]
  have hl : 1 / lam ≤ l T := by
    rw [l, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hTwoPi]
    linarith
  have hLOne : 1 ≤ (Pf T).L T := by
    rw [hLdef]
    have hmul := mul_le_mul_of_nonneg_left hl hlam0.le
    rw [mul_one_div_cancel hlam0.ne'] at hmul
    exact hmul
  have hlLog : l T ≤ Real.log T := by
    rw [l, Real.log_div hTpos.ne' hTwoPi.ne']
    have hlogTwoPi : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  have hLLog : (Pf T).L T ≤ lam * Real.log T := by
    rw [hLdef]
    exact mul_le_mul_of_nonneg_left hlLog hlam0.le
  have hX : (Pf T).X T = Real.exp ((Pf T).L T) := rfl
  have hXThreeFourths :
      (Pf T).X T ^ (3 / 4 : ℝ) ≤ T ^ (3 * lam / 4) := by
    rw [hX, ← Real.exp_mul, Real.rpow_def_of_pos hTpos]
    apply Real.exp_le_exp.mpr
    rw [hLdef]
    have hmul := mul_le_mul_of_nonneg_left hlLog hlam0.le
    nlinarith
  have hcdTwo :
      ContDiff ℝ 2 (fun u : ℝ => (((Pf T).phi T u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hcd.of_le (by norm_num))
  exact ⟨hlam T, hLOne, hLdef, hX, hLLog, hXThreeFourths,
    hcdTwo, hsupp, by linarith, heven, hleOne, hderiv⟩

/-- The released explicit-formula power/log absorption in its actual
range `3λ < 4`.  This is the quantitative reason the interval
`33/25 < λ < 4/3` is analytically nonempty. -/
theorem pow_log_absorb_fullChain
    (lam : ℝ) (hThree : 3 * lam < 4) {A : ℝ} (hA : 0 ≤ A) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ T : ℝ, T₁ ≤ T →
      T ^ (3 * lam / 4) * Real.log T ^ 2 * A / (T * Real.log T)
          ≤ C * T ^ (-((1 - 3 * lam / 4) / 2)) ∧
      T ^ (3 * lam / 4) * Real.log T ^ 2 * A / T ^ 2
          ≤ C * T ^ (-((1 - 3 * lam / 4) / 2)) / T := by
  set delta : ℝ := (1 - 3 * lam / 4) / 2 with hdelta
  have hdeltaPos : 0 < delta := by
    rw [hdelta]
    linarith
  refine ⟨A * (1 / delta) + A * (2 / delta) ^ 2 + 1, 2, by positivity,
    fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  have hlogPos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogOne : Real.log T ≤ (1 / delta) * T ^ delta :=
    Zeta23.XiPrime.log_le_const_mul_rpow hdeltaPos hTpos.le
  have hlogTwo : Real.log T ^ 2 ≤ (2 / delta) ^ 2 * T ^ delta := by
    have h := Zeta23.XiPrime.log_le_const_mul_rpow
      (ε := delta / 2) (by positivity) hTpos.le
    have hsquare : Real.log T ^ 2 ≤
        ((1 / (delta / 2)) * T ^ (delta / 2)) ^ 2 :=
      pow_le_pow_left₀ hlogPos.le h 2
    calc
      Real.log T ^ 2 ≤
          ((1 / (delta / 2)) * T ^ (delta / 2)) ^ 2 := hsquare
      _ = (2 / delta) ^ 2 * (T ^ (delta / 2)) ^ 2 := by
        rw [mul_pow]
        congr 1
        field_simp
      _ = (2 / delta) ^ 2 * T ^ delta := by
        rw [← Real.rpow_natCast (T ^ (delta / 2)) 2,
          ← Real.rpow_mul hTpos.le]
        push_cast
        ring_nf
  have hexponent : 3 * lam / 4 = 1 - 2 * delta := by
    rw [hdelta]
    ring
  have hTdelta : 0 < T ^ delta := Real.rpow_pos_of_pos hTpos _
  have hTneg : T ^ (-delta) = (T ^ delta)⁻¹ :=
    Real.rpow_neg hTpos.le delta
  have hpower : T ^ (3 * lam / 4) =
      T * (T ^ delta)⁻¹ * (T ^ delta)⁻¹ := by
    rw [hexponent,
      show (1 : ℝ) - 2 * delta = 1 + (-delta) + (-delta) by ring,
      Real.rpow_add hTpos, Real.rpow_add hTpos, Real.rpow_one, hTneg]
  constructor
  · have hequality :
        T ^ (3 * lam / 4) * Real.log T ^ 2 * A /
            (T * Real.log T) =
          A * ((T ^ delta)⁻¹ * ((T ^ delta)⁻¹ * Real.log T)) := by
      rw [hpower]
      field_simp
    rw [hequality,
      show -((1 - 3 * lam / 4) / 2) = -delta by rw [hdelta], hTneg]
    have hOne : (T ^ delta)⁻¹ * Real.log T ≤ 1 / delta := by
      rw [inv_mul_le_iff₀ hTdelta]
      linarith
    have hTwo :
        (T ^ delta)⁻¹ * ((T ^ delta)⁻¹ * Real.log T) ≤
          (T ^ delta)⁻¹ * (1 / delta) :=
      mul_le_mul_of_nonneg_left hOne (inv_nonneg.mpr hTdelta.le)
    calc
      A * ((T ^ delta)⁻¹ * ((T ^ delta)⁻¹ * Real.log T)) ≤
          A * ((T ^ delta)⁻¹ * (1 / delta)) :=
        mul_le_mul_of_nonneg_left hTwo hA
      _ = (A * (1 / delta)) * (T ^ delta)⁻¹ := by ring
      _ ≤ (A * (1 / delta) + A * (2 / delta) ^ 2 + 1) *
          (T ^ delta)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hTdelta.le)
        nlinarith [sq_nonneg (2 / delta)]
  · have hequality :
        T ^ (3 * lam / 4) * Real.log T ^ 2 * A / T ^ 2 =
          A * ((T ^ delta)⁻¹ *
            ((T ^ delta)⁻¹ * Real.log T ^ 2)) / T := by
      rw [hpower]
      field_simp
    rw [hequality,
      show -((1 - 3 * lam / 4) / 2) = -delta by rw [hdelta], hTneg]
    apply div_le_div_of_nonneg_right _ hTpos.le
    have hOne : (T ^ delta)⁻¹ * Real.log T ^ 2 ≤ (2 / delta) ^ 2 := by
      rw [inv_mul_le_iff₀ hTdelta]
      linarith
    have hTwo :
        (T ^ delta)⁻¹ * ((T ^ delta)⁻¹ * Real.log T ^ 2) ≤
          (T ^ delta)⁻¹ * (2 / delta) ^ 2 :=
      mul_le_mul_of_nonneg_left hOne (inv_nonneg.mpr hTdelta.le)
    calc
      A * ((T ^ delta)⁻¹ * ((T ^ delta)⁻¹ * Real.log T ^ 2)) ≤
          A * ((T ^ delta)⁻¹ * (2 / delta) ^ 2) :=
        mul_le_mul_of_nonneg_left hTwo hA
      _ = (A * (2 / delta) ^ 2) * (T ^ delta)⁻¹ := by ring
      _ ≤ (A * (1 / delta) + A * (2 / delta) ^ 2 + 1) *
          (T ^ delta)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hTdelta.le)
        nlinarith [hdeltaPos]

end

end PrimeShell
