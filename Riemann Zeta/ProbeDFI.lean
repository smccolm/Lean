import RiemannZeta.GuthMaynard.DFIErrorTerms

open Complex Set
open scoped ContDiff

namespace RiemannZeta.GuthMaynard

noncomputable def probeMixedSliceTestFunction
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ) (y : ℝ) :
    DFIVoronoiTestFunction (fun x ↦ iteratedDeriv j (E x) y) where
  lower := A
  upper := B
  lower_pos := hA
  lower_le_upper := hAB
  smooth := contDiff_iteratedDeriv_slice_right hE j y
  support_subset := by
    intro x hx
    by_contra hnot
    have hzero : E x = fun _ ↦ 0 := by
      funext y'
      by_contra hne
      exact hnot (hSupport (show
        (x, y') ∈ Function.support (Function.uncurry E) by
          simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne)).1
    change iteratedDeriv j (E x) y ≠ 0 at hx
    rw [hzero] at hx
    exact hx (by simp)

theorem probeMixedSlice_deriv
    {E : ℝ → ℝ → ℂ}
    (i j : ℕ) (x y : ℝ) :
    iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x =
      dfiMixedDeriv i j E x y := by
  rfl

theorem probe_iteratedDeriv_mellin_transpose
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (j : ℕ) (y : ℝ) (z : ℂ) :
    iteratedDeriv j (fun y' ↦ mellin (fun x ↦ E x y') z) y =
      mellin (fun x ↦ iteratedDeriv j (E x) y) z := by
  let F : ℝ → ℝ → ℂ := fun y x ↦ E x y
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    exact hE.comp (contDiff_snd.prodMk contDiff_fst)
  have hFSupport : Function.support (Function.uncurry F) ⊆
      Set.Icc C D ×ˢ Set.Icc A B := by
    intro p hp
    have hne : E p.2 p.1 ≠ 0 := by
      simpa [F, Function.mem_support, Function.uncurry_apply_pair] using hp
    have hs : (p.2, p.1) ∈ Function.support (Function.uncurry E) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hne
    exact ⟨(hSupport hs).2, (hSupport hs).1⟩
  have h := iteratedDeriv_mellin_slice hF hA hFSupport j y z
  simpa only [F, dfiMixedDeriv, Function.uncurry_apply_pair] using h

noncomputable def probeMellinProfileMajorant
    (lower upper σ : ℝ) (p : ℕ) (A B : ℝ) : ℝ :=
  let D := max 1 (max upper lower⁻¹)
  (1 + 2 * Real.pi) ^ p *
    ((2 : ℝ) ^ p * ((-Real.log lower) - (-Real.log upper)) *
      (D ^ |σ| * A + D ^ |σ| *
        (A * (|σ| + (p : ℝ) + D * B) ^ p)))

theorem probe_mellin_line_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (σ : ℝ) (p : ℕ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hDeriv : ∀ j ≤ p, ∀ x : ℝ,
      ‖iteratedDeriv j g x‖ ≤ A * B ^ j) (u : ℝ) :
    (1 + |u|) ^ p *
        ‖mellin g ((σ : ℂ) + (u : ℂ) * I)‖ ≤
      probeMellinProfileMajorant hg.lower hg.upper σ p A B := by
  exact hg.mellin_line_bound_of_physical_profile_order
    σ p hA hB hDeriv u

theorem probeMellinProfileMajorant_mul_amplitude
    (lower upper σ : ℝ) (p j : ℕ) (A B : ℝ) :
    probeMellinProfileMajorant lower upper σ p (A * B ^ j) B =
      probeMellinProfileMajorant lower upper σ p A B * B ^ j := by
  simp only [probeMellinProfileMajorant]
  ring

theorem probeMellinProfileMajorant_scale_amplitude
    (lower upper σ : ℝ) (p : ℕ) (A B r : ℝ) :
    probeMellinProfileMajorant lower upper σ p (A * r) B =
      probeMellinProfileMajorant lower upper σ p A B * r := by
  simp only [probeMellinProfileMajorant]
  ring

theorem probe_biMellin_line_bound_of_mixed_profile
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (σ τ : ℝ) (p : ℕ) {M R : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hDeriv : ∀ i ≤ p, ∀ j ≤ p, ∀ x y : ℝ,
      ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j))
    (u v : ℝ) :
    (1 + |u|) ^ p * (1 + |v|) ^ p *
        ‖dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
          ((τ : ℂ) + (v : ℂ) * I)‖ ≤
      probeMellinProfileMajorant C D τ p
        (probeMellinProfileMajorant A B σ p M R) R := by
  let X : ℝ := probeMellinProfileMajorant A B σ p M R
  let wu : ℝ := (1 + |u|) ^ p
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hInner (j : ℕ) (hj : j ≤ p) (y : ℝ) :
      wu * ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ X * R ^ j := by
    have hProfile : ∀ i ≤ p, ∀ x : ℝ,
        ‖iteratedDeriv i (fun x' ↦ iteratedDeriv j (E x') y) x‖ ≤
          (M * R ^ j) * R ^ i := by
      intro i hi x
      rw [probeMixedSlice_deriv]
      calc
        ‖dfiMixedDeriv i j E x y‖ ≤ M * R ^ (i + j) :=
          hDeriv i hi j hj x y
        _ = (M * R ^ j) * R ^ i := by rw [pow_add]; ring
    have hBound := probe_mellin_line_bound
      (probeMixedSliceTestFunction hE hA hAB hSupport j y)
      σ p (mul_nonneg hM (pow_nonneg hR j)) hR hProfile u
    simpa only [X, wu,
      probeMellinProfileMajorant_mul_amplitude] using hBound
  have hX : 0 ≤ X := by
    have h0 := hInner 0 (Nat.zero_le p) 0
    have hleft : 0 ≤ wu *
        ‖mellin (fun x ↦ iteratedDeriv 0 (E x) 0)
          ((σ : ℂ) + (u : ℂ) * I)‖ := by positivity
    exact hleft.trans (by simpa using h0)
  let G : ℝ → ℂ := fun y ↦
    mellin (fun x ↦ E x y) ((σ : ℂ) + (u : ℂ) * I)
  have hGDeriv : ∀ j ≤ p, ∀ y : ℝ,
      ‖iteratedDeriv j G y‖ ≤ (X * wu⁻¹) * R ^ j := by
    intro j hj y
    rw [show iteratedDeriv j G y =
        mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I) by
      exact probe_iteratedDeriv_mellin_transpose hE hA hSupport j y _]
    calc
      ‖mellin (fun x ↦ iteratedDeriv j (E x) y)
          ((σ : ℂ) + (u : ℂ) * I)‖ ≤ (X * R ^ j) / wu := by
        apply (le_div_iff₀ hwu).2
        simpa [mul_comm] using hInner j hj y
      _ = (X * wu⁻¹) * R ^ j := by
        rw [div_eq_mul_inv]
        ring
  have hOuter := probe_mellin_line_bound
    (dfiMellinTransposeTestFunction hE hA hC hCD hSupport
      ((σ : ℂ) + (u : ℂ) * I))
    τ p (mul_nonneg hX (inv_nonneg.mpr hwu.le)) hR hGDeriv v
  change (1 + |v|) ^ p *
      ‖mellin G ((τ : ℂ) + (v : ℂ) * I)‖ ≤
        probeMellinProfileMajorant C D τ p (X * wu⁻¹) R at hOuter
  have hComm := mellin_mellin_comm_of_rectangular_support
    hE hA hC hSupport
      ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I)
  rw [show dfiBiMellin E ((σ : ℂ) + (u : ℂ) * I)
      ((τ : ℂ) + (v : ℂ) * I) =
        mellin G ((τ : ℂ) + (v : ℂ) * I) by
    exact hComm]
  have hScaled := mul_le_mul_of_nonneg_left hOuter hwu.le
  rw [probeMellinProfileMajorant_scale_amplitude] at hScaled
  have hCancel : wu *
      (probeMellinProfileMajorant C D τ p X R * wu⁻¹) =
        probeMellinProfileMajorant C D τ p X R := by
    field_simp [ne_of_gt hwu]
  rw [hCancel] at hScaled
  simpa only [wu, X, mul_assoc] using hScaled

theorem probe_two_frequency_quadratic_decay
    {a b c Cx Cy M u v : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy) (hM : 0 ≤ M)
    (hA : a ≤ Cx * (1 + |u|) ^ 2)
    (hB : b ≤ Cy * (1 + |v|) ^ 2)
    (hC : (1 + |u|) ^ 6 * (1 + |v|) ^ 6 * c ≤ M) :
    a * b * c ≤
      Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
  let wu : ℝ := 1 + |u|
  let wv : ℝ := 1 + |v|
  have hwu : 0 < wu := by dsimp [wu]; positivity
  have hwv : 0 < wv := by dsimp [wv]; positivity
  have hc' : c ≤ M / (wu ^ 6 * wv ^ 6) := by
    apply (le_div_iff₀ (mul_pos (pow_pos hwu 6) (pow_pos hwv 6))).2
    simpa only [wu, wv, mul_comm, mul_left_comm, mul_assoc] using hC
  have huDen : 0 < 1 + u ^ 2 := by positivity
  have hvDen : 0 < 1 + v ^ 2 := by positivity
  have huPow : 1 + u ^ 2 ≤ wu ^ 4 := by
    dsimp [wu]
    nlinarith [abs_nonneg u, sq_abs u]
  have hvPow : 1 + v ^ 2 ≤ wv ^ 4 := by
    dsimp [wv]
    nlinarith [abs_nonneg v, sq_abs v]
  have huInv : (wu ^ 4)⁻¹ ≤ (1 + u ^ 2)⁻¹ :=
    inv_anti₀ huDen huPow
  have hvInv : (wv ^ 4)⁻¹ ≤ (1 + v ^ 2)⁻¹ :=
    inv_anti₀ hvDen hvPow
  calc
    a * b * c ≤
        (Cx * wu ^ 2) * (Cy * wv ^ 2) *
          (M / (wu ^ 6 * wv ^ 6)) := by gcongr
    _ = Cx * Cy * M * (wu ^ 4)⁻¹ * (wv ^ 4)⁻¹ := by
      field_simp [ne_of_gt hwu, ne_of_gt hwv]
    _ ≤ Cx * Cy * M * (1 + u ^ 2)⁻¹ * (1 + v ^ 2)⁻¹ := by
      gcongr

theorem probe_divisor_three_half_summable :
    Summable (fun n : ℕ ↦
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖) := by
  have h := periodicDivisorCoeff_LSeriesSummable
    1 (fun _ : ZMod 1 ↦ (1 : ℂ)) (s := (3 / 2 : ℂ)) (by norm_num)
  have hEq : periodicDivisorCoeff 1 (fun _ : ZMod 1 ↦ (1 : ℂ)) =
      divisorWeight := by
    funext n
    simp [periodicDivisorCoeff, divisorWeight]
  rw [hEq] at h
  exact summable_norm_iff.mpr h

theorem probe_integral_norm_amplitude_eq
    {E : ℝ → ℝ → ℂ}
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (m n : ℕ) :
    (∫ p : ℝ × ℝ,
      ‖dfiEquation24DoubleDualAmplitudeIntegrand
        qx xBranch qy yBranch E m n p‖) =
      ‖LSeries.term divisorWeight (3 / 2 : ℂ) m‖ *
        ‖LSeries.term divisorWeight (3 / 2 : ℂ) n‖ *
        ∫ p : ℝ × ℝ,
          ‖dfiDualBranchMultiplier qx xBranch
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I) *
            dfiDualBranchMultiplier qy yBranch
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I) *
            dfiBiMellin E
              (-(1 / 2 : ℂ) + (p.1 : ℂ) * I)
              (-(1 / 2 : ℂ) + (p.2 : ℂ) * I)‖ := by
  have hx : periodicDivisorCoeff qx (fun _ ↦ 1) = divisorWeight := by
    funext k
    simp [periodicDivisorCoeff, divisorWeight]
  have hy : periodicDivisorCoeff qy (fun _ ↦ 1) = divisorWeight := by
    funext k
    simp [periodicDivisorCoeff, divisorWeight]
  have h := integral_norm_dfiEquation24DoubleMellinTerm
    (E := E) qx (fun _ ↦ 1) xBranch qy (fun _ ↦ 1) yBranch m n
  rw [hx, hy] at h
  simpa only [dfiEquation24DoubleMellinTerm_one_eq_amplitudeIntegrand] using h

end RiemannZeta.GuthMaynard
