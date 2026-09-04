import GafniTao.HeathBrownShiftFiberBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Summation over Heath-Brown's shifts

The fixed-shift estimate is summed with its literal `1/d` weight.  The
result exposes the harmonic number before the later logarithmic and scale
simplifications.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem heathBrownPositiveShiftFiber_card_cast_le_harmonic_total
    {N k H K D d : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hd : 1 ≤ d) (hDN : D ≤ N) (hdD : d ≤ D)
    (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hcoord : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
      ((D : ℝ) + c) * (b + a * D) / d := by
  dsimp only
  have hdN : d ≤ N := hdD.trans hDN
  by_cases hdStrict : d < N
  · have hNsub : 1 ≤ N - d := by omega
    exact heathBrownPositiveShiftFiber_card_cast_le_harmonic
      hk hNsub hd hdN hdD hA hlambda
      hcoord hcoordd hraw hrawd hkBounds
  · have hdEq : d = N := Nat.le_antisymm hdN (Nat.le_of_not_gt hdStrict)
    have hempty : heathBrownPositiveShiftFiber N k H K f d = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hne
      obtain ⟨n, hn⟩ := hne
      have hn' := mem_heathBrownPositiveShiftFiber.mp hn
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem heathBrown_positiveShiftFiber_sum_cast_le_harmonic
    {N k H K D : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hDN : D ≤ N) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hcoord : ContinuousOn
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Icc 0 (N : ℝ)))
    (hcoordd : DifferentiableOn ℝ
      (heathBrownDerivativeCoordinate f (k - 2))
      (Set.Ioo 0 (N : ℝ)))
    (hraw : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc 0 (N : ℝ)))
    (hrawd : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo 0 (N : ℝ)))
    (hkBounds : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      lambda ≤ iteratedDeriv k f x ∧
        iteratedDeriv k f x ≤ A * lambda) :
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    (∑ d ∈ Finset.Icc 1 D,
        ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ)) ≤
      ((D : ℝ) + c) * (b + a * D) * (harmonic D : ℝ) := by
  dsimp only
  let Q : ℝ :=
    ((D : ℝ) +
      8 * ((k - 2).factorial : ℝ) *
        (((H : ℝ) ^ (k - 2))⁻¹) / lambda) *
      (8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3 +
        (A * lambda * N / ((k - 2).factorial : ℝ)) * D)
  have hterm : ∀ d ∈ Finset.Icc 1 D,
      ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ) ≤
        Q * (d : ℝ)⁻¹ := by
    intro d hdmem
    have hd' := Finset.mem_Icc.mp hdmem
    have h := heathBrownPositiveShiftFiber_card_cast_le_harmonic_total
      (H := H) (K := K) hk hd'.1 hDN hd'.2 hA hlambda hcoord hcoordd
      hraw hrawd hkBounds
    dsimp only at h
    simpa only [Q, div_eq_mul_inv] using h
  calc
    (∑ d ∈ Finset.Icc 1 D,
        ((heathBrownPositiveShiftFiber N k H K f d).card : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 D, Q * (d : ℝ)⁻¹ := by
      exact Finset.sum_le_sum fun d hd => hterm d hd
    _ = Q * ∑ d ∈ Finset.Icc 1 D, (d : ℝ)⁻¹ := by
      simp only [Finset.mul_sum]
    _ = Q * (harmonic D : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      congr 2
    _ = ((D : ℝ) +
          8 * ((k - 2).factorial : ℝ) *
            (((H : ℝ) ^ (k - 2))⁻¹) / lambda) *
        (8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3 +
          (A * lambda * N / ((k - 2).factorial : ℝ)) * D) *
        (harmonic D : ℝ) := by rfl

theorem heathBrownPairCountTwo_card_cast_le_harmonic
    {N k H : ℕ} {f : ℝ → ℝ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 ≤ A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4)
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
    let D := heathBrownShiftBound N k H lambda
    let c := 8 * ((k - 2).factorial : ℝ) *
      (((H : ℝ) ^ (k - 2))⁻¹) / lambda
    let b := 8 * (((H : ℝ) ^ (k - 2))⁻¹) + 3
    let a := A * lambda * N / ((k - 2).factorial : ℝ)
    ((heathBrownPairCountTwo N k H
      (heathBrownBlockParameter A lambda N) f).card : ℝ) ≤
      N + 2 * (((D : ℝ) + c) * (b + a * D) * (harmonic D : ℝ)) := by
  dsimp only
  let D := heathBrownShiftBound N k H lambda
  have hcountNat := heathBrownPairCountTwo_card_le_restricted_shift_sum
    N k H f (by omega : 1 ≤ k) hA hlambda hsmall
    hcoordLast hcoordLastD hkBounds
  have hcount :
      ((heathBrownPairCountTwo N k H
        (heathBrownBlockParameter A lambda N) f).card : ℝ) ≤
        N + 2 * ∑ d ∈ Finset.Icc 1 D,
          ((heathBrownPositiveShiftFiber N k H
            (heathBrownBlockParameter A lambda N) f d).card : ℝ) := by
    exact_mod_cast hcountNat
  have hsum := heathBrown_positiveShiftFiber_sum_cast_le_harmonic
    (H := H) (K := heathBrownBlockParameter A lambda N) hk
    (heathBrownShiftBound_le_N N k H lambda) hA hlambda
    hcoordLow hcoordLowD hraw hrawd hkBounds
  dsimp only at hsum
  have hsum' := add_le_add_right
    (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)) (N : ℝ)
  simpa only [D] using hcount.trans hsum'

#print axioms heathBrownPositiveShiftFiber_card_cast_le_harmonic_total
#print axioms heathBrown_positiveShiftFiber_sum_cast_le_harmonic
#print axioms heathBrownPairCountTwo_card_cast_le_harmonic

end

end GafniTao
