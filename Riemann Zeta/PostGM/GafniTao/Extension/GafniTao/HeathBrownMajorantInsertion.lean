import GafniTao.HeathBrownLemmaOneFinite
import GafniTao.HeathBrownRefinedCountFinal

/-!
# Heath-Brown Lemma 1: insertion of the two source estimates

This module substitutes the critical Vinogradov mean-value estimate and the
literal derivative-pair count into the exact finite majorant from Lemma 1.
The result intentionally retains all three source factors.  In particular,
the critical VMVT is an explicit theorem argument here; it is not postulated
or hidden in a structure field.
-/

open Finset
open scoped ENNReal

namespace GafniTao

noncomputable section

/-- Insert a concrete critical VMVT estimate and a concrete bound for
`mathcal N` into the literal majorant produced by the coefficient-cell
argument.  This is the monotone analytic step between Heath-Brown Lemmas 1
and 2. -/
theorem heathBrownIntegratedMajorant_le_of_bounds
    {N k H s : ℕ} {f : ℝ → ℝ} {CJ JP : ℝ}
    (hs : 1 ≤ s)
    (hMoment : (fordVinogradovMomentNat s (k - 1) H : ℝ) ≤ CJ)
    (hPairs : ((heathBrownPairCount N k H f).card : ℝ) ≤ JP) :
    heathBrownIntegratedMajorant N k H s f ≤
      ENNReal.ofReal CJ ^ (1 / (2 * (s : ℝ))) *
      ENNReal.ofReal
          (JP * ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ^
        (1 / (2 * (s : ℝ))) *
      ENNReal.ofReal
          ((N : ℝ) * ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ^
        (1 - 1 / (s : ℝ)) := by
  have hMomentE :
      (fordVinogradovMomentNat s (k - 1) H : ENNReal) ≤
        ENNReal.ofReal CJ := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hMoment
  have hPairE :
      ENNReal.ofReal
          (((heathBrownPairCount N k H f).card : ℝ) *
            ((2 : ℝ) ^ (k - 1) *
              (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ≤
        ENNReal.ofReal
          (JP * ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
  have hInterior : ((N - H : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.sub_le N H
  have hInteriorE :
      ENNReal.ofReal
          (((N - H : ℕ) : ℝ) *
            ((2 : ℝ) ^ (k - 1) *
              (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ≤
        ENNReal.ofReal
          ((N : ℝ) * ((2 : ℝ) ^ (k - 1) *
            (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) := by
    apply ENNReal.ofReal_le_ofReal
    gcongr
  have hsReal : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hLastExponent : 0 ≤ 1 - 1 / (s : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < s)]
    exact hsReal
  unfold heathBrownIntegratedMajorant
  gcongr

/-- Critical-VMVT specialization of the first factor in the preceding
insertion theorem.  The exponent is simplified to the exact source value
`s + epsilon`. -/
theorem heathBrownCriticalMoment_bound
    {k H : ℕ} {epsilon C : ℝ}
    (hk : 2 ≤ k) (hH : 1 ≤ H)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C epsilon) :
    (fordVinogradovMomentNat (heathBrownCriticalMoment k) (k - 1) H : ℝ) ≤
      C * (H : ℝ) ^ ((heathBrownCriticalMoment k : ℝ) + epsilon) := by
  have h := hVMVT H hH
  rw [heathBrownCriticalMoment_lambda (by omega) epsilon] at h
  exact h

/-- Fully source-linked insertion at Heath-Brown's critical moment.  The
right side still displays the exact VMVT coefficient, Lemma 2 coefficient,
cell volume, and endpoint count; subsequent algebra may absorb only these
visible factors. -/
theorem heathBrownIntegratedMajorant_le_critical
    {N k : ℕ} {f : ℝ → ℝ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C epsilon)
    (hcoordLow : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLowD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hcoordLast : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLastD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let H := heathBrownHChoice k A lambda
    let s := heathBrownCriticalMoment k
    let V := (2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹)
    let P := heathBrownLemmaTwoConstant k A *
      (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
      (1 + Real.log N)
    heathBrownIntegratedMajorant N k H s f ≤
      ENNReal.ofReal (C * (H : ℝ) ^ ((s : ℝ) + epsilon)) ^
          (1 / (2 * (s : ℝ))) *
        ENNReal.ofReal (P * V) ^ (1 / (2 * (s : ℝ))) *
        ENNReal.ofReal ((N : ℝ) * V) ^ (1 - 1 / (s : ℝ)) := by
  dsimp only
  have hs : 1 ≤ heathBrownCriticalMoment k := by
    unfold heathBrownCriticalMoment
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    exact Nat.mul_le_mul (by omega) (by omega)
  apply heathBrownIntegratedMajorant_le_of_bounds hs
  · exact heathBrownCriticalMoment_bound (by omega) (by omega) hVMVT
  · exact heathBrownPairCount_card_cast_le_lemma_two
      hk hN hA hlambda hlambdaOne hsmall hlargeH hcoordLow hcoordLowD
      hcoordLast hcoordLastD hraw hrawd hkBounds

/-- Heath-Brown Lemma 1 after inserting both of its genuine number-theoretic
inputs.  The statement deliberately keeps the two Abel factors, the
coefficient-cell volume, and the common-range endpoint error separate.  Thus
the subsequent source-scale algebra cannot accidentally absorb a term that
has not first been bounded. -/
theorem heathBrown_lemma_one_assembled_critical
    {N k : ℕ} {f : ℝ → ℝ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hlambdaOne : lambda ≤ 1) (hsmall : A * lambda ≤ 1 / 4)
    (hlargeH : 8 ≤ heathBrownHChoice k A lambda)
    (hHN : heathBrownHChoice k A lambda ≤ N)
    (hVMVT : FordVinogradovMomentBound
      (heathBrownCriticalMoment k) (k - 1) C epsilon)
    (hlocal : ∀ n ∈ heathBrownInteriorIndices N
        (heathBrownHChoice k A lambda),
      ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n ∧
      (∀ x ∈ Set.Icc (1 : ℝ) (heathBrownHChoice k A lambda),
        HasDerivAt f (deriv f ((n : ℝ) + x)) ((n : ℝ) + x)) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) (heathBrownHChoice k A lambda),
        ContDiffOn ℝ (k - 1 : ℕ) (deriv f)
          (Set.Icc (n : ℝ) ((n : ℝ) + x))) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) (heathBrownHChoice k A lambda),
        ∀ ξ ∈ Set.Ioo (n : ℝ) ((n : ℝ) + x),
        ‖iteratedDeriv k f ξ‖ ≤ A * lambda))
    (hcoordLow : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLowD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hcoordLast : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Icc 0 (N : ℝ)))
    (hcoordLastD : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 1))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let H := heathBrownHChoice k A lambda
    let s := heathBrownCriticalMoment k
    let V : ENNReal := ENNReal.ofReal
      ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹))
    let P := heathBrownLemmaTwoConstant k A *
      (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
      (1 + Real.log N)
    V * H * ENNReal.ofReal ‖heathBrownExponentialSum N f‖ ≤
      (1 + ENNReal.ofReal
          (2 * Real.pi * (A * lambda * (H : ℝ) ^ (k - 1))) * H) *
        (1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * H) *
        (ENNReal.ofReal (C * (H : ℝ) ^ ((s : ℝ) + epsilon)) ^
            (1 / (2 * (s : ℝ))) *
          ENNReal.ofReal (P *
            ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹))) ^
              (1 / (2 * (s : ℝ))) *
          ENNReal.ofReal ((N : ℝ) *
            ((2 : ℝ) ^ (k - 1) * (((H : ℝ) ^ s)⁻¹))) ^
              (1 - 1 / (s : ℝ))) +
      V * ENNReal.ofReal ((H : ℝ) ^ 2) := by
  dsimp only
  have hpre := heathBrown_lemma_one_finite_preVMVT
    (N := N) (k := k) (H := heathBrownHChoice k A lambda)
    (s := heathBrownCriticalMoment k) (by omega) (by omega) hHN
    (mul_nonneg hA.le hlambda.le) (by
      unfold heathBrownCriticalMoment
      apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
      exact Nat.mul_le_mul (by omega) (by omega)) hlocal
  have hins := heathBrownIntegratedMajorant_le_critical
    (N := N) (k := k) (f := f) (A := A) (lambda := lambda)
    (epsilon := epsilon) (C := C) hk hN hA hlambda hlambdaOne hsmall
    hlargeH hVMVT hcoordLow hcoordLowD hcoordLast hcoordLastD hraw hrawd
    hkBounds
  dsimp only at hpre hins ⊢
  calc
    _ ≤ (1 + ENNReal.ofReal
          (2 * Real.pi * (A * lambda *
            (heathBrownHChoice k A lambda : ℝ) ^ (k - 1))) *
            heathBrownHChoice k A lambda) *
        (1 + ENNReal.ofReal
          (2 * Real.pi * ((k : ℝ) ^ 2 /
            heathBrownHChoice k A lambda)) *
            heathBrownHChoice k A lambda) *
        heathBrownIntegratedMajorant N k
          (heathBrownHChoice k A lambda) (heathBrownCriticalMoment k) f +
        ENNReal.ofReal
            ((2 : ℝ) ^ (k - 1) *
              (((heathBrownHChoice k A lambda : ℝ) ^
                heathBrownCriticalMoment k)⁻¹)) *
          ENNReal.ofReal ((heathBrownHChoice k A lambda : ℝ) ^ 2) := hpre
    _ ≤ _ := by gcongr

#print axioms heathBrownIntegratedMajorant_le_of_bounds
#print axioms heathBrownCriticalMoment_bound
#print axioms heathBrownIntegratedMajorant_le_critical
#print axioms heathBrown_lemma_one_assembled_critical

end

end GafniTao
