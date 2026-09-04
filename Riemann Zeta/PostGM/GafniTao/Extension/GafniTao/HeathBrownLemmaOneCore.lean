import GafniTao.HeathBrownLemmaOneAlgebra

/-!
# Uniform control of the two Abel factors in Heath-Brown Lemma 1

The source choice `H = floor ((A*lambda)^(-1/k))` makes the first Abel
variation uniformly bounded; the second one simplifies exactly because its
factor `1/H` is multiplied by the averaging length `H`.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownLemmaOneCoreConstant
    (k : ℕ) (C : ℝ) : ℝ :=
  let s := heathBrownCriticalMoment k
  let r := 1 / (2 * (s : ℝ))
  (1 + 2 * Real.pi) * (1 + 2 * Real.pi * (k : ℝ) ^ 2) *
    C ^ r * ((2 : ℝ) ^ (k - 1)) ^ (-r)

theorem heathBrown_first_Abel_factor_le
    {k : ℕ} {A lambda : ℝ}
    (hk : 3 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda) :
    1 + 2 * Real.pi *
        (A * lambda * (heathBrownHChoice k A lambda : ℝ) ^ (k - 1)) *
        heathBrownHChoice k A lambda ≤
      1 + 2 * Real.pi := by
  have hscale := heathBrownHChoice_scale_pow_le_one
    (by omega : 1 ≤ k) hA hlambda
  have hsucc : k - 1 + 1 = k := by omega
  have hpow :
      (heathBrownHChoice k A lambda : ℝ) ^ (k - 1) *
          heathBrownHChoice k A lambda =
        (heathBrownHChoice k A lambda : ℝ) ^ k := by
    rw [← pow_succ, hsucc]
  calc
    1 + 2 * Real.pi *
        (A * lambda * (heathBrownHChoice k A lambda : ℝ) ^ (k - 1)) *
        heathBrownHChoice k A lambda =
      1 + 2 * Real.pi *
        (A * lambda * (heathBrownHChoice k A lambda : ℝ) ^ k) := by
          rw [← hpow]
          ring
    _ ≤ 1 + 2 * Real.pi * 1 := by gcongr
    _ = 1 + 2 * Real.pi := by ring

theorem heathBrown_second_Abel_factor_eq
    {k : ℕ} {A lambda : ℝ}
    (hk : 1 ≤ k) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) :
    1 + 2 * Real.pi *
        ((k : ℝ) ^ 2 / heathBrownHChoice k A lambda) *
        heathBrownHChoice k A lambda =
      1 + 2 * Real.pi * (k : ℝ) ^ 2 := by
  have hHnat := heathBrownHChoice_pos hk hA hlambda hsmall
  have hH : (heathBrownHChoice k A lambda : ℝ) ≠ 0 := by
    exact_mod_cast hHnat.ne'
  field_simp

theorem heathBrownLemmaOneCoreConstant_pos
    {k : ℕ} {C : ℝ} (hk : 3 ≤ k) (hC : 0 < C) :
    0 < heathBrownLemmaOneCoreConstant k C := by
  unfold heathBrownLemmaOneCoreConstant
  positivity

theorem heathBrownLemmaOneNormalized_le_core
    {N k : ℕ} {A lambda epsilon C : ℝ}
    (hk : 3 ≤ k) (hN : 1 ≤ N) (hA : 0 < A) (hlambda : 0 < lambda)
    (hsmall : A * lambda ≤ 1 / 4) (hC : 0 < C) :
    heathBrownLemmaOneNormalizedRealBound N k A lambda epsilon C ≤
      let H := heathBrownHChoice k A lambda
      let s := heathBrownCriticalMoment k
      let r := 1 / (2 * (s : ℝ))
      let P := heathBrownLemmaTwoConstant k A *
        (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
        (1 + Real.log N)
      heathBrownLemmaOneCoreConstant k C *
          ((H : ℝ) ^ (epsilon * r) * P ^ r *
            (N : ℝ) ^ (1 - 1 / (s : ℝ))) + H := by
  dsimp only
  have hfirst := heathBrown_first_Abel_factor_le hk hA hlambda
  have hsecond := heathBrown_second_Abel_factor_eq
    (by omega : 1 ≤ k) hA hlambda hsmall
  have hP : 0 < heathBrownLemmaTwoConstant k A *
      (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
      (1 + Real.log N) :=
    heathBrownLemmaOne_source_P_pos hN hA hlambda
  have hs : 0 < heathBrownCriticalMoment k := by
    unfold heathBrownCriticalMoment
    have hprod : 2 ≤ k * (k - 1) := by
      calc
        2 = 2 * 1 := by omega
        _ ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
    exact Nat.div_pos hprod (by omega)
  have hsReal : (0 : ℝ) < heathBrownCriticalMoment k := by exact_mod_cast hs
  have hnonneg : 0 ≤
      C ^ (1 / (2 * (heathBrownCriticalMoment k : ℝ))) *
        (heathBrownLemmaTwoConstant k A *
          (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
          (1 + Real.log N)) ^
            (1 / (2 * (heathBrownCriticalMoment k : ℝ))) *
        (N : ℝ) ^ (1 - 1 / (heathBrownCriticalMoment k : ℝ)) *
        ((2 : ℝ) ^ (k - 1)) ^
          (-(1 / (2 * (heathBrownCriticalMoment k : ℝ)))) *
        (heathBrownHChoice k A lambda : ℝ) ^
          (epsilon * (1 / (2 * (heathBrownCriticalMoment k : ℝ)))) := by
    positivity
  unfold heathBrownLemmaOneNormalizedRealBound
    heathBrownLemmaOneCoreConstant
  dsimp only
  rw [hsecond]
  calc
    _ ≤ (1 + 2 * Real.pi) *
          (1 + 2 * Real.pi * (k : ℝ) ^ 2) *
          (C ^ (1 / (2 * (heathBrownCriticalMoment k : ℝ))) *
            (heathBrownLemmaTwoConstant k A *
              (N + lambda * N ^ 2 + lambda ^ (-(2 / (k : ℝ)))) *
              (1 + Real.log N)) ^
                (1 / (2 * (heathBrownCriticalMoment k : ℝ))) *
            (N : ℝ) ^ (1 - 1 / (heathBrownCriticalMoment k : ℝ)) *
            ((2 : ℝ) ^ (k - 1)) ^
              (-(1 / (2 * (heathBrownCriticalMoment k : ℝ)))) *
            (heathBrownHChoice k A lambda : ℝ) ^
              (epsilon * (1 / (2 * (heathBrownCriticalMoment k : ℝ))))) +
          heathBrownHChoice k A lambda := by
      gcongr
    _ = _ := by ring

#print axioms heathBrown_first_Abel_factor_le
#print axioms heathBrown_second_Abel_factor_eq
#print axioms heathBrownLemmaOneCoreConstant_pos
#print axioms heathBrownLemmaOneNormalized_le_core

end

end GafniTao
