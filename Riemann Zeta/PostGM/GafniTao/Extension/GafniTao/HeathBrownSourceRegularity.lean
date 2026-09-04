import GafniTao.HeathBrownMajorantInsertion

/-!
# Source regularity for Heath-Brown's derivative estimate

The published theorem assumes continuous derivatives on the open source
interval.  The finite coefficient and spacing arguments use ordinary
iterated derivatives on compact subintervals.  This file supplies that
entry bridge explicitly; endpoint differentiability is never assumed.
-/

open Set

namespace GafniTao

noncomputable section

theorem continuousOn_iteratedDeriv_of_contDiffOn_isOpen
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {k j : ℕ}
    (hf : ContDiffOn ℝ k f U) (hj : j ≤ k) :
    ContinuousOn (iteratedDeriv j f) U := by
  have h := hf.continuousOn_iteratedDerivWithin
    (by exact_mod_cast hj) hU.uniqueDiffOn
  exact h.congr (iteratedDerivWithin_of_isOpen hU).symm

theorem differentiableOn_iteratedDeriv_of_contDiffOn_isOpen
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {k j : ℕ}
    (hf : ContDiffOn ℝ k f U) (hj : j < k) :
    DifferentiableOn ℝ (iteratedDeriv j f) U := by
  have h := hf.differentiableOn_iteratedDerivWithin
    (by exact_mod_cast hj) hU.uniqueDiffOn
  exact h.congr (iteratedDerivWithin_of_isOpen hU).symm

/-- The two derivative-coordinate regularity packages needed by the literal
pair-count argument, restricted to any compact interval lying inside the
published open differentiability interval. -/
theorem heathBrown_coordinate_data_of_source
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {k N : ℕ}
    (hk : 3 ≤ k) (hf : ContDiffOn ℝ k f U)
    (hsub : Set.Icc (0 : ℝ) (N : ℝ) ⊆ U) :
    ContinuousOn (heathBrownDerivativeCoordinate f (k - 2))
        (Set.Icc 0 (N : ℝ)) ∧
      DifferentiableOn ℝ (heathBrownDerivativeCoordinate f (k - 2))
        (Set.Ioo 0 (N : ℝ)) ∧
      ContinuousOn (heathBrownDerivativeCoordinate f (k - 1))
        (Set.Icc 0 (N : ℝ)) ∧
      DifferentiableOn ℝ (heathBrownDerivativeCoordinate f (k - 1))
        (Set.Ioo 0 (N : ℝ)) ∧
      ContinuousOn (iteratedDeriv (k - 1) f)
        (Set.Icc 0 (N : ℝ)) ∧
      DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
        (Set.Ioo 0 (N : ℝ)) := by
  have hcLow : ContinuousOn (iteratedDeriv (k - 2) f)
      (Set.Icc (0 : ℝ) N) :=
    (continuousOn_iteratedDeriv_of_contDiffOn_isOpen hU hf (by omega)).mono hsub
  have hdLow : DifferentiableOn ℝ (iteratedDeriv (k - 2) f)
      (Set.Ioo (0 : ℝ) N) :=
    (differentiableOn_iteratedDeriv_of_contDiffOn_isOpen hU hf (by omega)).mono
      (fun x hx => hsub ⟨hx.1.le, hx.2.le⟩)
  have hcLast : ContinuousOn (iteratedDeriv (k - 1) f)
      (Set.Icc (0 : ℝ) N) :=
    (continuousOn_iteratedDeriv_of_contDiffOn_isOpen hU hf (by omega)).mono hsub
  have hdLast : DifferentiableOn ℝ (iteratedDeriv (k - 1) f)
      (Set.Ioo (0 : ℝ) N) :=
    (differentiableOn_iteratedDeriv_of_contDiffOn_isOpen hU hf (by omega)).mono
      (fun x hx => hsub ⟨hx.1.le, hx.2.le⟩)
  refine ⟨?_, ?_, ?_, ?_, hcLast, hdLast⟩
  · exact hcLow.div_const _
  · exact hdLow.div_const _
  · exact hcLast.div_const _
  · exact hdLast.div_const _

/-- The detailed Taylor hypotheses in the finite Lemma 1 follow from the
single source assumption of `C^k` regularity on an open interval containing
the compact working range. -/
theorem heathBrown_local_data_of_source
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {k N H : ℕ}
    (hk : 2 ≤ k) (hf : ContDiffOn ℝ k f U)
    (hsub : Set.Icc (0 : ℝ) (N : ℝ) ⊆ U)
    {A lambda : ℝ}
    (hkBounds : ∀ x ∈ U,
      0 ≤ iteratedDeriv k f x ∧ iteratedDeriv k f x ≤ A * lambda) :
    ∀ n ∈ heathBrownInteriorIndices N H,
      ContDiffAt ℝ (k - 2 : ℕ) (deriv f) n ∧
      (∀ x ∈ Set.Icc (1 : ℝ) H,
        HasDerivAt f (deriv f ((n : ℝ) + x)) ((n : ℝ) + x)) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) H,
        ContDiffOn ℝ (k - 1 : ℕ) (deriv f)
          (Set.Icc (n : ℝ) ((n : ℝ) + x))) ∧
      (∀ x ∈ Set.Icc (1 : ℝ) H,
        ∀ ξ ∈ Set.Ioo (n : ℝ) ((n : ℝ) + x),
        ‖iteratedDeriv k f ξ‖ ≤ A * lambda) := by
  intro n hn
  have hnmem := Finset.mem_Icc.mp hn
  have hnN : n ≤ N := hnmem.2.trans (Nat.sub_le N H)
  have hnU : (n : ℝ) ∈ U := hsub ⟨by positivity,
    by exact_mod_cast hnN⟩
  have hderivSource : ContDiffOn ℝ (k - 1 : ℕ) (deriv f) U := by
    apply hf.deriv_of_isOpen hU
    exact_mod_cast (by omega : k - 1 + 1 ≤ k)
  refine ⟨(hderivSource.contDiffAt (hU.mem_nhds hnU)).of_le ?_, ?_, ?_, ?_⟩
  · exact_mod_cast (by omega : k - 2 ≤ k - 1)
  · intro x hx
    have hHN : H ≤ N := by omega
    have hnxN : (n : ℝ) + x ≤ N := by
      have hnupper : n ≤ N - H := hnmem.2
      have hcast : (n : ℝ) ≤ ((N - H : ℕ) : ℝ) := by
        exact_mod_cast hnupper
      rw [Nat.cast_sub hHN] at hcast
      calc
        (n : ℝ) + x ≤ (N - H : ℝ) + H := add_le_add hcast hx.2
        _ = N := by ring
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hnmem.1
    have hnxU : (n : ℝ) + x ∈ U := hsub ⟨by linarith [hx.1], hnxN⟩
    exact (hf.differentiableOn (by exact_mod_cast (by omega : k ≠ 0))
      ((n : ℝ) + x) hnxU).differentiableAt
      (hU.mem_nhds hnxU) |>.hasDerivAt
  · intro x hx
    apply hderivSource.mono
    intro y hy
    have hHN : H ≤ N := by omega
    have hnxN : (n : ℝ) + x ≤ N := by
      have hnupper : n ≤ N - H := hnmem.2
      have hcast : (n : ℝ) ≤ ((N - H : ℕ) : ℝ) := by
        exact_mod_cast hnupper
      rw [Nat.cast_sub hHN] at hcast
      calc
        (n : ℝ) + x ≤ (N - H : ℝ) + H := add_le_add hcast hx.2
        _ = N := by ring
    exact hsub ⟨(by positivity : (0 : ℝ) ≤ n).trans hy.1,
      hy.2.trans hnxN⟩
  · intro x hx ξ hξ
    have hHN : H ≤ N := by omega
    have hnxN : (n : ℝ) + x ≤ N := by
      have hnupper : n ≤ N - H := hnmem.2
      have hcast : (n : ℝ) ≤ ((N - H : ℕ) : ℝ) := by
        exact_mod_cast hnupper
      rw [Nat.cast_sub hHN] at hcast
      calc
        (n : ℝ) + x ≤ (N - H : ℝ) + H := add_le_add hcast hx.2
        _ = N := by ring
    have hξU : ξ ∈ U := hsub ⟨(by positivity : (0 : ℝ) ≤ n).trans hξ.1.le,
      hξ.2.le.trans hnxN⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hkBounds ξ hξU).1]
    exact (hkBounds ξ hξU).2

/-- Source-facing compact-interior form of the fully assembled Lemma 1.
All auxiliary differentiability hypotheses are discharged here from a
single `C^k` hypothesis on the surrounding open set. -/
theorem heathBrown_lemma_one_assembled_of_source
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
  have hcoord := heathBrown_coordinate_data_of_source hU hk hf hsub
  have hlocal := heathBrown_local_data_of_source
    (H := heathBrownHChoice k A lambda) hU (by omega) hf hsub
    (fun x hx => ⟨hlambda.le.trans (hkBounds x hx).1,
      (hkBounds x hx).2⟩)
  exact heathBrown_lemma_one_assembled_critical
    hk hN hA hlambda hlambdaOne hsmall hlargeH hHN hVMVT hlocal
    hcoord.1 hcoord.2.1 hcoord.2.2.1 hcoord.2.2.2.1 hcoord.2.2.2.2.1
    hcoord.2.2.2.2.2
    (fun x hx => hkBounds x (hsub ⟨hx.1.le, hx.2.le⟩))

#print axioms continuousOn_iteratedDeriv_of_contDiffOn_isOpen
#print axioms differentiableOn_iteratedDeriv_of_contDiffOn_isOpen
#print axioms heathBrown_coordinate_data_of_source
#print axioms heathBrown_local_data_of_source
#print axioms heathBrown_lemma_one_assembled_of_source

end

end GafniTao
