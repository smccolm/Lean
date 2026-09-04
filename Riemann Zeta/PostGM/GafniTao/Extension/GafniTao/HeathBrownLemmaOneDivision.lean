import GafniTao.HeathBrownSourceRegularity

/-!
# Normalizing Heath-Brown Lemma 1

This module divides the assembled coefficient-cell inequality by its exact
positive volume and averaging factor.  The resulting bound is still literal:
no fixed `k`, `A`, or epsilon factor is hidden in asymptotic notation.
-/

open Set
open scoped ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownLemmaOneInsertedTerm
    (N k : ℕ) (A lambda epsilon C : ℝ) : ENNReal :=
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let V := (2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹)
  let P := heathBrownLemmaTwoConstant k A *
    (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
    (1 + Real.log N)
  (1 + ENNReal.ofReal
      (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) * H) *
    (1 + ENNReal.ofReal
      (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) *
    (ENNReal.ofReal (C * (H : ℝ) ^ ((s : ℝ) + epsilon)) ^
        (1 / (2 * (s : ℝ))) *
      ENNReal.ofReal (P * V) ^ (1 / (2 * (s : ℝ))) *
      ENNReal.ofReal ((N : ℝ) * V) ^ (1 - 1 / (s : ℝ)))

/-- The exact normalized right side obtained from the finite coefficient-cell
argument.  This definition is an explicit expression, not an assumed
estimate. -/
noncomputable def heathBrownLemmaOneRawBound
    (N k : ℕ) (A lambda epsilon C : ℝ) : ENNReal :=
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let V : ENNReal := ENNReal.ofReal
    ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹))
  (heathBrownLemmaOneInsertedTerm N k A lambda epsilon C +
      V * ENNReal.ofReal ((H : ℝ) ^ 2)) /
    (V * H)

theorem heathBrown_cellVolume_pos
    {k H : ℕ} (hH : 1 ≤ H) :
    0 < ENNReal.ofReal
      ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) := by
  rw [ENNReal.ofReal_pos]
  positivity

theorem heathBrown_cellVolume_ne_top (k H : ℕ) :
    ENNReal.ofReal
      ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Division of the compact-interior assembled inequality by the exact
nonzero cell-volume and averaging factor. -/
theorem heathBrown_lemma_one_raw_of_source
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
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C epsilon) :
    ENNReal.ofReal ‖heathBrownExponentialSum N f‖ ≤
      heathBrownLemmaOneRawBound N k A lambda epsilon C := by
  let H := heathBrownHChoice k A lambda
  let s := heathBrownCriticalMoment k
  let V : ENNReal := ENNReal.ofReal
    ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹))
  have hassembled := heathBrown_lemma_one_assembled_of_source
    hU hk hN hA hlambda hlambdaOne hsmall hlargeH hHN hf hsub hkBounds hVMVT
  dsimp only at hassembled
  have hV0 : V ≠ 0 := by
    exact (heathBrown_cellVolume_pos (k := k) (H := H) (by omega)).ne'
  have hVtop : V ≠ ∞ := heathBrown_cellVolume_ne_top k H
  have hH0 : (H : ENNReal) ≠ 0 := by exact_mod_cast (by omega : H ≠ 0)
  have hHtop : (H : ENNReal) ≠ ∞ := ENNReal.coe_ne_top
  apply (ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hV0 hH0))
    (Or.inl (ENNReal.mul_ne_top hVtop hHtop))).2
  simpa only [heathBrownLemmaOneRawBound, heathBrownLemmaOneInsertedTerm,
    H, s, V, mul_comm, mul_left_comm, mul_assoc] using hassembled

#print axioms heathBrown_cellVolume_pos
#print axioms heathBrown_cellVolume_ne_top
#print axioms heathBrown_lemma_one_raw_of_source

end

end GafniTao
