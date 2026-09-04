import GafniTao.HeathBrownInteriorShift

/-!
# Real-valued form of the assembled Heath-Brown Lemma 1

The preceding argument was carried out in `ENNReal` so that Hölder and
integration remained monotone without side conditions.  This file converts
the result back to the literal nonnegative real expression, retaining every
factor before the source exponent algebra is applied.
-/

open Set
open scoped ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownLemmaOneExpandedRealBound
    (N k : ℕ) (A lambda epsilon C : ℝ) : ℝ :=
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let V := (2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹)
  let P := heathBrownLemmaTwoConstant k A *
    (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
    (1 + Real.log N)
  ((1 + (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) * H) *
      (1 + (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) *
      ((C * (H : ℝ) ^ ((s : ℝ) + epsilon)) ^ (1 / (2 * (s : ℝ))) *
        (P * V) ^ (1 / (2 * (s : ℝ))) *
        ((N : ℝ) * V) ^ (1 - 1 / (s : ℝ))) +
    V * (H : ℝ) ^ 2) / (V * H)

theorem heathBrownLemmaTwoConstant_pos
    (k : ℕ) {A : ℝ} (hA : 0 < A) :
    0 < heathBrownLemmaTwoConstant k A := by
  unfold heathBrownLemmaTwoConstant
  exact mul_pos (heathBrownRefinedCountConstant_pos k hA) (by linarith)

theorem heathBrownLemmaOne_source_P_pos
    {N k : ℕ} {A lambda : ℝ}
    (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda) :
    0 < heathBrownLemmaTwoConstant k A *
      (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
      (1 + Real.log N) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hmiddle : 0 < (N : ℝ) + lambda * N ^ 2 +
      lambda ^ (-(2 / (k : ℝ))) := by positivity
  exact mul_pos (mul_pos (heathBrownLemmaTwoConstant_pos k hA) hmiddle)
    (by linarith)

theorem heathBrownLemmaOneRawBound_toReal
    {N k : ℕ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) (hC : 0 < C) :
    (heathBrownLemmaOneRawBound N k A lambda epsilon C).toReal =
      heathBrownLemmaOneExpandedRealBound N k A lambda epsilon C := by
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let V := (2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹)
  let P := heathBrownLemmaTwoConstant k A *
    (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
    (1 + Real.log N)
  have hH : 0 < H := heathBrownHChoice_pos (by omega) hA hlambda hsmall
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hs : 0 < s := by
    dsimp only [s, heathBrownCriticalMoment]
    have hprod : 2 ≤ k * (k - 1) := by
      calc
        2 = 2 * 1 := by omega
        _ ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos hprod (by omega)
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  have hV : 0 < V := by
    dsimp only [V]
    positivity
  have hP : 0 < P := by
    dsimp only [P]
    exact heathBrownLemmaOne_source_P_pos hN hA hlambda
  have hvmvtBase : 0 < C * (H : ℝ) ^ ((s : ℝ) + epsilon) := by positivity
  have hPV : 0 < P * V := mul_pos hP hV
  have hNV : 0 < (N : ℝ) * V := by positivity
  have hfirst : 0 ≤
      2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1)) := by positivity
  have hsecond : 0 ≤ 2 * Real.pi * ((k : ℝ) ^ 2 / H) := by positivity
  unfold heathBrownLemmaOneRawBound heathBrownLemmaOneInsertedTerm
    heathBrownLemmaOneExpandedRealBound
  dsimp only
  rw [ENNReal.toReal_div,
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ← ENNReal.toReal_rpow]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  rw [ENNReal.toReal_ofReal hfirst, ENNReal.toReal_ofReal hsecond,
    ENNReal.toReal_ofReal hvmvtBase.le, ENNReal.toReal_ofReal hPV.le,
    ENNReal.toReal_ofReal hNV.le, ENNReal.toReal_ofReal hV.le,
    ENNReal.toReal_ofReal (sq_nonneg (H : ℝ))]
  rfl

/-- The exact real normalized inequality on a compact interior interval. -/
theorem norm_heathBrownExponentialSum_le_expanded_of_source
    {U : Set ℝ} (hU : IsOpen U)
    {N k : ℕ} {f : ℝ → ℝ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hHN : heathBrownHChoice k A lambda ≤ N)
    (hf : ContDiffOn ℝ k f U)
    (hsub : Set.Icc (0 : ℝ) (N : ℝ) ⊆ U)
    (hkBounds : ∀ x ∈ U,
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda)
    (hC : 0 < C)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C epsilon) :
    ‖heathBrownExponentialSum N f‖ ≤
      heathBrownLemmaOneExpandedRealBound N k A lambda epsilon C := by
  have hraw := heathBrown_lemma_one_raw_of_source hU hk hN hA hlambda
    hlambdaOne hsmall hlargeH hHN hf hsub hkBounds hVMVT
  have hfinite : heathBrownLemmaOneRawBound N k A lambda epsilon C ≠ ∞ := by
    unfold heathBrownLemmaOneRawBound heathBrownLemmaOneInsertedTerm
    finiteness
  have htoReal := ENNReal.toReal_mono hfinite hraw
  rw [heathBrownLemmaOneRawBound_toReal hk hN hA hlambda hsmall hC] at htoReal
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at htoReal
  exact htoReal

#print axioms heathBrownLemmaTwoConstant_pos
#print axioms heathBrownLemmaOne_source_P_pos
#print axioms heathBrownLemmaOneRawBound_toReal
#print axioms norm_heathBrownExponentialSum_le_expanded_of_source

end

end GafniTao
