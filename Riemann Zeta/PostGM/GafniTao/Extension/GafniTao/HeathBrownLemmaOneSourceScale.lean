import GafniTao.HeathBrownSpacingMonomials

/-!
# Heath-Brown Lemma 1 at the source scale

This file combines the exact normalized finite inequality with Lemma 2,
the critical-moment identity, and an explicit epsilon budget.  The floor
remainder `H` is intentionally retained for the final case split in the
proof of Theorem 1.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownLemmaOneSourceConstant
    (k : ℕ) (A C epsilon : ℝ) : ℝ :=
  let r := heathBrownCriticalReciprocal k
  heathBrownLemmaOneCoreConstant k C *
    (heathBrownLemmaTwoConstant k A) ^ r *
    (heathBrownLogConstant epsilon) ^ r *
    (3 : ℝ) ^ r

theorem heathBrown_vmvt_epsilon_identity
    {k : ℕ} (hk : 2 ≤ k) (epsilon : ℝ) :
    (epsilon * (heathBrownCriticalMoment k : ℝ)) *
        heathBrownCriticalReciprocal k = epsilon / 2 := by
  rw [heathBrownCriticalMoment_cast (by omega : 1 ≤ k)]
  unfold heathBrownCriticalReciprocal
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by linarith
  have hkm10 : (k : ℝ) - 1 ≠ 0 := by linarith
  field_simp

theorem heathBrown_H_vmvt_loss_le
    {N k : ℕ} {A lambda epsilon : ℝ}
    (hk : 2 ≤ k) (hHleN : heathBrownHChoice k A lambda ≤ N)
    (hepsilon : 0 < epsilon) :
    (heathBrownHChoice k A lambda : ℝ) ^
        ((epsilon * (heathBrownCriticalMoment k : ℝ)) *
          heathBrownCriticalReciprocal k) ≤
      (N : ℝ) ^ (epsilon / 2) := by
  rw [heathBrown_vmvt_epsilon_identity hk epsilon]
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hHleN)
    (by positivity)

theorem heathBrown_epsilon_halves
    {N : ℕ} (hN : 1 ≤ N) (epsilon : ℝ) :
    (N : ℝ) ^ (epsilon / 2) * (N : ℝ) ^ (epsilon / 2) =
      (N : ℝ) ^ epsilon := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [← Real.rpow_add hNpos]
  congr 1
  ring

theorem heathBrownLemmaOneSourceConstant_pos
    {k : ℕ} {A C epsilon : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    0 < heathBrownLemmaOneSourceConstant k A C epsilon := by
  unfold heathBrownLemmaOneSourceConstant
  have htwo := heathBrownLemmaTwoConstant_pos (k := k) hA
  have hlog := heathBrownLogConstant_pos hepsilon
  have hcore := heathBrownLemmaOneCoreConstant_pos hk hC
  positivity

/-- Exact source-scale consequence of the normalized Lemma 1 calculation.
The critical VMVT is requested with epsilon `epsilon*s`, so its `H` loss and
the logarithmic loss each consume one half of the final epsilon. -/
theorem heathBrownLemmaOneNormalized_le_sourceScale
    {N k : ℕ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hepsilon : 0 < epsilon) (hsmall : A * lambda ≤ 1 / 4)
    (hHleN : heathBrownHChoice k A lambda ≤ N) (hC : 0 < C) :
    heathBrownLemmaOneNormalizedRealBound N k A lambda
        (epsilon * (heathBrownCriticalMoment k : ℝ)) C ≤
      heathBrownLemmaOneSourceConstant k A C epsilon *
          (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda +
        heathBrownHChoice k A lambda := by
  let s := heathBrownCriticalMoment k
  let r := heathBrownCriticalReciprocal k
  let H := heathBrownHChoice k A lambda
  let B := heathBrownSpacingBase N k lambda
  let L := 1 + Real.log (N : ℝ)
  have hcore := heathBrownLemmaOneNormalized_le_core
    (N := N) (k := k) (A := A) (lambda := lambda)
    (epsilon := epsilon * (s : ℝ)) (C := C)
    hk hN hA hlambda hsmall hC
  dsimp only at hcore
  rw [heathBrown_half_critical_eq_reciprocal (by omega : 2 ≤ k),
    heathBrown_critical_core_exponent (by omega : 2 ≤ k)] at hcore
  change _ ≤
    heathBrownLemmaOneCoreConstant k C *
        ((H : ℝ) ^ ((epsilon * (s : ℝ)) * r) *
          (heathBrownLemmaTwoConstant k A * B * L) ^ r *
          (N : ℝ) ^ (1 - 2 * r)) + H at hcore
  have hr0 : 0 ≤ r :=
    (heathBrownCriticalReciprocal_pos (by omega : 2 ≤ k)).le
  have hr1 : r ≤ 1 :=
    (heathBrownCriticalReciprocal_le_half
      (by omega : 2 ≤ k)).trans (by norm_num)
  have hB0 : 0 ≤ B := by
    dsimp only [B, heathBrownSpacingBase]
    positivity
  have hL0 : 0 ≤ L := by
    dsimp only [L]
    have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := Real.log_nonneg hNReal
    linarith
  have hCtwo0 : 0 ≤ heathBrownLemmaTwoConstant k A :=
    (heathBrownLemmaTwoConstant_pos (k := k) hA).le
  have hPExpansion :
      (heathBrownLemmaTwoConstant k A * B * L) ^ r =
        (heathBrownLemmaTwoConstant k A) ^ r * B ^ r * L ^ r := by
    rw [Real.mul_rpow (mul_nonneg hCtwo0 hB0) hL0,
      Real.mul_rpow hCtwo0 hB0]
  have hHL :
      (H : ℝ) ^ ((epsilon * (s : ℝ)) * r) * L ^ r ≤
        (heathBrownLogConstant epsilon) ^ r *
          (N : ℝ) ^ epsilon := by
    have hHloss := heathBrown_H_vmvt_loss_le
      (N := N) (k := k) (A := A) (lambda := lambda)
      (by omega : 2 ≤ k) hHleN hepsilon
    change (H : ℝ) ^ ((epsilon * (s : ℝ)) * r) ≤
      (N : ℝ) ^ (epsilon / 2) at hHloss
    have hLogLoss := heathBrown_one_add_log_rpow_le
      (N := N) (epsilon := epsilon) (r := r) hN hepsilon hr0 hr1
    change L ^ r ≤ (heathBrownLogConstant epsilon) ^ r *
      (N : ℝ) ^ (epsilon / 2) at hLogLoss
    calc
      (H : ℝ) ^ ((epsilon * (s : ℝ)) * r) * L ^ r ≤
          (N : ℝ) ^ (epsilon / 2) *
            ((heathBrownLogConstant epsilon) ^ r *
              (N : ℝ) ^ (epsilon / 2)) :=
        mul_le_mul hHloss hLogLoss (by positivity) (by positivity)
      _ = (heathBrownLogConstant epsilon) ^ r *
          (N : ℝ) ^ epsilon := by
        rw [← heathBrown_epsilon_halves hN epsilon]
        ring
  have hBN :
      (N : ℝ) ^ (1 - 2 * r) * B ^ r ≤
        (3 : ℝ) ^ r * heathBrownThreeTerm N k lambda := by
    have hspacing := heathBrownSpacingBase_rpow_le
      (N := N) (k := k) (lambda := lambda) hlambda hr0
    change B ^ r ≤ (3 : ℝ) ^ r *
      ((N : ℝ) ^ r +
        (lambda * (N : ℝ) ^ 2) ^ r +
        (lambda ^ (-(2 / (k : ℝ)))) ^ r) at hspacing
    calc
      (N : ℝ) ^ (1 - 2 * r) * B ^ r ≤
          (N : ℝ) ^ (1 - 2 * r) *
            ((3 : ℝ) ^ r *
              ((N : ℝ) ^ r +
                (lambda * (N : ℝ) ^ 2) ^ r +
                (lambda ^ (-(2 / (k : ℝ)))) ^ r)) := by
        gcongr
      _ = (3 : ℝ) ^ r * heathBrownThreeTerm N k lambda := by
        rw [← heathBrown_spacing_monomial_identity hN
          (by omega : 2 ≤ k) hlambda]
        ring
  have hMain :
      heathBrownLemmaOneCoreConstant k C *
          ((H : ℝ) ^ ((epsilon * (s : ℝ)) * r) *
            (heathBrownLemmaTwoConstant k A * B * L) ^ r *
            (N : ℝ) ^ (1 - 2 * r)) ≤
        heathBrownLemmaOneSourceConstant k A C epsilon *
          (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda := by
    rw [hPExpansion]
    have hCore0 := (heathBrownLemmaOneCoreConstant_pos hk hC).le
    have hCtwoPower0 :
        0 ≤ (heathBrownLemmaTwoConstant k A) ^ r := by positivity
    have hPrefix0 : 0 ≤
        heathBrownLemmaOneCoreConstant k C *
          (heathBrownLemmaTwoConstant k A) ^ r :=
      mul_nonneg hCore0 hCtwoPower0
    have hHLRight0 : 0 ≤
        (heathBrownLogConstant epsilon) ^ r *
          (N : ℝ) ^ epsilon :=
      mul_nonneg
        (Real.rpow_nonneg (heathBrownLogConstant_pos hepsilon).le _)
        (Real.rpow_nonneg (by positivity) _)
    have hBNLeft0 : 0 ≤
        (N : ℝ) ^ (1 - 2 * r) * B ^ r :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hB0 _)
    calc
      heathBrownLemmaOneCoreConstant k C *
          ((H : ℝ) ^ ((epsilon * (s : ℝ)) * r) *
            ((heathBrownLemmaTwoConstant k A) ^ r * B ^ r * L ^ r) *
            (N : ℝ) ^ (1 - 2 * r)) =
          heathBrownLemmaOneCoreConstant k C *
            (heathBrownLemmaTwoConstant k A) ^ r *
            ((H : ℝ) ^ ((epsilon * (s : ℝ)) * r) * L ^ r) *
            ((N : ℝ) ^ (1 - 2 * r) * B ^ r) := by ring
      _ ≤ heathBrownLemmaOneCoreConstant k C *
            (heathBrownLemmaTwoConstant k A) ^ r *
            ((heathBrownLogConstant epsilon) ^ r *
              (N : ℝ) ^ epsilon) *
            ((3 : ℝ) ^ r * heathBrownThreeTerm N k lambda) := by
        calc
          heathBrownLemmaOneCoreConstant k C *
                (heathBrownLemmaTwoConstant k A) ^ r *
                ((H : ℝ) ^ ((epsilon * (s : ℝ)) * r) * L ^ r) *
                ((N : ℝ) ^ (1 - 2 * r) * B ^ r) ≤
              heathBrownLemmaOneCoreConstant k C *
                (heathBrownLemmaTwoConstant k A) ^ r *
                ((heathBrownLogConstant epsilon) ^ r *
                  (N : ℝ) ^ epsilon) *
                ((N : ℝ) ^ (1 - 2 * r) * B ^ r) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hHL hPrefix0) hBNLeft0
          _ ≤ heathBrownLemmaOneCoreConstant k C *
                (heathBrownLemmaTwoConstant k A) ^ r *
                ((heathBrownLogConstant epsilon) ^ r *
                  (N : ℝ) ^ epsilon) *
                ((3 : ℝ) ^ r * heathBrownThreeTerm N k lambda) :=
            mul_le_mul_of_nonneg_left hBN (mul_nonneg hPrefix0 hHLRight0)
      _ = heathBrownLemmaOneSourceConstant k A C epsilon *
          (N : ℝ) ^ epsilon * heathBrownThreeTerm N k lambda := by
        unfold heathBrownLemmaOneSourceConstant
        dsimp only
        ring
  exact hcore.trans (add_le_add hMain le_rfl)

#print axioms heathBrown_vmvt_epsilon_identity
#print axioms heathBrown_H_vmvt_loss_le
#print axioms heathBrown_epsilon_halves
#print axioms heathBrownLemmaOneSourceConstant_pos
#print axioms heathBrownLemmaOneNormalized_le_sourceScale

end

end GafniTao
