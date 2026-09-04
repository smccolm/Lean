import GafniTao.WooleyConditioning

/-!
# Finite weighted means in Wooley Section 3

This file upgrades the coefficient-one grid model to the finite weighted
model used by nested efficient congruencing.  A coefficient family is kept
on the literal source box `1, ..., Q`; hence every sum is finite and no
summability convention is hidden in the definitions.  The normalizations
are those of equations (3.2)--(3.8).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The square of Wooley's global `rho_0` for a finite coefficient family. -/
def wooleyWeightedMassSq {Q : ℕ} (gamma : Fin Q → ℂ) : ℝ :=
  ∑ n, ‖gamma n‖ ^ 2

/-- The square of `rho_h(xi)` in equation (3.2). -/
def wooleyWeightedResidueMassSq {Q q : ℕ}
    (gamma : Fin Q → ℂ) (xi : ZMod q) : ℝ :=
  ∑ n ∈ wooleyResidueClass Q q xi, ‖gamma n‖ ^ 2

def wooleyWeightedGridSum {Q : ℕ} (q k : ℕ) [NeZero q]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) : ℂ :=
  ∑ n, gamma n * wooleyMonomialGridPhase q k Q alpha n

def wooleyWeightedResidueGridSum {Q qH : ℕ} (qB k : ℕ) [NeZero qB]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB) (xi : ZMod qH) : ℂ :=
  ∑ n ∈ wooleyResidueClass Q qH xi,
    gamma n * wooleyMonomialGridPhase qB k Q alpha n

/-- The finite weighted version of `f_gamma` from (3.4). -/
def wooleyWeightedNormalizedGridSum {Q : ℕ} (q k : ℕ) [NeZero q]
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod q) : ℂ :=
  if wooleyWeightedMassSq gamma = 0 then 0
  else ((Real.sqrt (wooleyWeightedMassSq gamma) : ℂ)⁻¹) *
    wooleyWeightedGridSum q k gamma alpha

/-- The finite weighted residue-class sum `f_h(alpha; xi)` from (3.4). -/
def wooleyWeightedNormalizedResidueGridSum {Q qH : ℕ}
    (qB k : ℕ) [NeZero qB] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) (xi : ZMod qH) : ℂ :=
  if wooleyWeightedResidueMassSq gamma xi = 0 then 0
  else ((Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ)⁻¹) *
    wooleyWeightedResidueGridSum qB k gamma alpha xi

/-- The weighted finite-grid mean `U^B_{s,k}` in (3.6). -/
def wooleyWeightedGridMean {Q : ℕ} (s k q : ℕ) [NeZero q]
    (gamma : Fin Q → ℂ) : ℝ :=
  ((q ^ k : ℕ) : ℝ)⁻¹ *
    ∑ alpha : Fin k → ZMod q,
      ‖wooleyWeightedNormalizedGridSum q k gamma alpha‖ ^ (2 * s)

/-- The weighted conditioned mean `U^{B,h}_{s,k}` in (3.8). -/
def wooleyWeightedConditionedGridMean {Q : ℕ} (s k qB qH : ℕ)
    [NeZero qB] [NeZero qH] (gamma : Fin Q → ℂ) : ℝ :=
  if wooleyWeightedMassSq gamma = 0 then 0
  else (wooleyWeightedMassSq gamma)⁻¹ *
    ∑ xi : ZMod qH,
      wooleyWeightedResidueMassSq gamma xi *
        (((qB ^ k : ℕ) : ℝ)⁻¹ *
          ∑ alpha : Fin k → ZMod qB,
            ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha xi‖ ^ (2 * s))

theorem wooleyWeightedMassSq_nonneg {Q : ℕ} (gamma : Fin Q → ℂ) :
    0 ≤ wooleyWeightedMassSq gamma := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem wooleyWeightedResidueMassSq_nonneg {Q q : ℕ}
    (gamma : Fin Q → ℂ) (xi : ZMod q) :
    0 ≤ wooleyWeightedResidueMassSq gamma xi := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Residue classes partition the coefficient `L²` mass exactly. -/
theorem wooley_sum_weightedResidueMassSq {Q q : ℕ} [NeZero q]
    (gamma : Fin Q → ℂ) :
    ∑ xi : ZMod q, wooleyWeightedResidueMassSq gamma xi =
      wooleyWeightedMassSq gamma := by
  unfold wooleyWeightedResidueMassSq wooleyWeightedMassSq
    wooleyResidueClass
  rw [Finset.sum_fiberwise
    (s := (Finset.univ : Finset (Fin Q)))
    (g := fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod q)))
    (f := fun n : Fin Q => ‖gamma n‖ ^ 2)]

theorem wooleyWeightedResidueGridSum_eq_zero_of_massSq_eq_zero
    {Q qH qB k : ℕ} [NeZero qB] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) (xi : ZMod qH)
    (hmass : wooleyWeightedResidueMassSq gamma xi = 0) :
    wooleyWeightedResidueGridSum qB k gamma alpha xi = 0 := by
  have hterm : ∀ n ∈ wooleyResidueClass Q qH xi, ‖gamma n‖ ^ 2 = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => sq_nonneg _)).mp
    simpa [wooleyWeightedResidueMassSq] using hmass
  unfold wooleyWeightedResidueGridSum
  apply Finset.sum_eq_zero
  intro n hn
  have hnzero : ‖gamma n‖ = 0 := (sq_eq_zero_iff).mp (hterm n hn)
  rw [norm_eq_zero] at hnzero
  simp [hnzero]

/-- Multiplying a normalized residue sum by its `rho_h` recovers the
unnormalized residue sum, including the zero-mass convention. -/
theorem wooley_sqrt_mass_mul_normalizedResidueGridSum
    {Q qH qB k : ℕ} [NeZero qB] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) (xi : ZMod qH) :
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyWeightedNormalizedResidueGridSum qB k gamma alpha xi =
      wooleyWeightedResidueGridSum qB k gamma alpha xi := by
  by_cases hmass : wooleyWeightedResidueMassSq gamma xi = 0
  · simp [wooleyWeightedNormalizedResidueGridSum, hmass,
      wooleyWeightedResidueGridSum_eq_zero_of_massSq_eq_zero
        gamma alpha xi hmass]
  · have hmassPos : 0 < wooleyWeightedResidueMassSq gamma xi :=
      lt_of_le_of_ne (wooleyWeightedResidueMassSq_nonneg gamma xi)
        (Ne.symm hmass)
    simp [wooleyWeightedNormalizedResidueGridSum, hmass,
      Real.sqrt_ne_zero'.mpr hmassPos]

/-- Summing the unnormalized residue pieces recovers the global weighted
exponential sum exactly. -/
theorem wooley_sum_weightedResidueGridSum
    {Q qB qH k : ℕ} [NeZero qB] [NeZero qH] (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) :
    ∑ xi : ZMod qH, wooleyWeightedResidueGridSum qB k gamma alpha xi =
      wooleyWeightedGridSum qB k gamma alpha := by
  unfold wooleyWeightedResidueGridSum wooleyWeightedGridSum
    wooleyResidueClass
  rw [Finset.sum_fiberwise
    (s := (Finset.univ : Finset (Fin Q)))
    (g := fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod qH)))
    (f := fun n : Fin Q =>
      gamma n * wooleyMonomialGridPhase qB k Q alpha n)]

/-- The exact finite form of the residue-class decomposition preceding
equation (3.9). -/
theorem wooley_weighted_normalizedGridSum_decomposition
    {Q qB qH k : ℕ} [NeZero qB] [NeZero qH]
    (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB)
    (hmass : wooleyWeightedMassSq gamma ≠ 0) :
    wooleyWeightedNormalizedGridSum qB k gamma alpha =
      ((Real.sqrt (wooleyWeightedMassSq gamma) : ℂ)⁻¹) *
        ∑ xi : ZMod qH,
          (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
            wooleyWeightedNormalizedResidueGridSum
              qB k gamma alpha xi := by
  simp_rw [wooley_sqrt_mass_mul_normalizedResidueGridSum gamma alpha]
  rw [wooley_sum_weightedResidueGridSum]
  simp [wooleyWeightedNormalizedGridSum, hmass]

#print axioms wooleyWeightedMassSq_nonneg
#print axioms wooleyWeightedResidueMassSq_nonneg
#print axioms wooley_sum_weightedResidueMassSq
#print axioms wooleyWeightedResidueGridSum_eq_zero_of_massSq_eq_zero
#print axioms wooley_sqrt_mass_mul_normalizedResidueGridSum
#print axioms wooley_sum_weightedResidueGridSum
#print axioms wooley_weighted_normalizedGridSum_decomposition

end

end GafniTao
