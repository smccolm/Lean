import GafniTao.WooleyWeightedComplexHolder
import GafniTao.WooleyWeightedMean

/-!
# Residue refinement for Wooley Lemma 6.2

This file proves the exact size of a fibre of the reduction map
`ZMod (p^b) -> ZMod (p^a)`.  It is the finite arithmetic fact denoted
`U_1 = p^(b-a)` in equation (6.11).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def wooleyResidueRefinementFiber (p a b : ℕ) [NeZero p] (hab : a ≤ b)
    (xi : ZMod (p ^ a)) : Finset (ZMod (p ^ b)) :=
  Finset.univ.filter fun z =>
    ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi

theorem wooleyResidueRefinementFiber_card
    {p a b : ℕ} [NeZero p] (hab : a ≤ b) (xi : ZMod (p ^ a)) :
    (wooleyResidueRefinementFiber p a b hab xi).card = p ^ (b - a) := by
  let f : ZMod (p ^ b) →+ ZMod (p ^ a) :=
    (ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))).toAddMonoidHom
  have hf : Function.Surjective f :=
    ZMod.castHom_surjective (pow_dvd_pow p hab)
  have hfiber (y : ZMod (p ^ a)) :
      (Finset.univ.filter fun z : ZMod (p ^ b) => f z = y).card =
        (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card := by
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf xi)
  have htotal :
      ∑ y : ZMod (p ^ a),
          (Finset.univ.filter fun z : ZMod (p ^ b) => f z = y).card =
        p ^ b := by
    rw [← Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (ZMod (p ^ b))))
      (t := (Finset.univ : Finset (ZMod (p ^ a))))
      (f := f) (by simp)]
    simp
  have hmul : p ^ a *
      (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card =
      p ^ b := by
    calc
      p ^ a *
          (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card =
          Fintype.card (ZMod (p ^ a)) *
            (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card := by
        rw [ZMod.card]
      _ = ∑ y : ZMod (p ^ a),
          (Finset.univ.filter fun z : ZMod (p ^ b) => f z = y).card := by
        simp_rw [hfiber]
        simp
      _ = p ^ b := htotal
  have hpPow : 0 < p ^ a := pow_pos (NeZero.pos p) a
  have hcanonical : p ^ a * p ^ (b - a) = p ^ b := by
    rw [Nat.mul_comm, Nat.pow_sub_mul_pow p hab]
  have hcard :
      (Finset.univ.filter fun z : ZMod (p ^ b) => f z = xi).card =
        p ^ (b - a) := by
    exact Nat.eq_of_mul_eq_mul_left (by omega) (hmul.trans hcanonical.symm)
  simpa [wooleyResidueRefinementFiber, f] using hcard

theorem wooley_sum_refined_residue_mass
    {Q p a b : ℕ} [NeZero p] (hab : a ≤ b)
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ a)) :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleyWeightedResidueMassSq gamma z =
      wooleyWeightedResidueMassSq gamma xi := by
  unfold wooleyWeightedResidueMassSq wooleyResidueClass
    wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n : Fin Q,
            if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              ‖gamma n‖ ^ 2 else 0
        else 0) =
        ∑ n : Fin Q,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              ‖gamma n‖ ^ 2 else 0)
          else 0 := by
    by_cases hz : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi <;> simp [hz]
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Fintype.sum_eq_single
    (((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))]
  · have hcast :
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))
            ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) =
          ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) :=
      ZMod.cast_natCast (pow_dvd_pow p hab) ((n : ℕ) + 1)
    rw [hcast]
    by_cases hxi : ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) = xi <;>
      simp [hxi]
  · intro z hzne
    by_cases hzxi : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi
    · rw [if_pos hzxi, if_neg (Ne.symm hzne)]
    · rw [if_neg hzxi]

theorem wooley_sum_refined_residue_grid
    {Q p a b qB k : ℕ} [NeZero p] [NeZero qB]
    (hab : a ≤ b) (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) (xi : ZMod (p ^ a)) :
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        wooleyWeightedResidueGridSum qB k gamma alpha z =
      wooleyWeightedResidueGridSum qB k gamma alpha xi := by
  unfold wooleyWeightedResidueGridSum wooleyResidueClass
    wooleyResidueRefinementFiber
  simp_rw [Finset.sum_filter]
  have hdistribute (z : ZMod (p ^ b)) :
      (if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
          ∑ n : Fin Q,
            if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              gamma n * wooleyMonomialGridPhase qB k Q alpha n else 0
        else 0) =
        ∑ n : Fin Q,
          if ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a)) z = xi then
            (if ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) = z then
              gamma n * wooleyMonomialGridPhase qB k Q alpha n else 0)
          else 0 := by
    by_cases hz : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi <;> simp [hz]
  simp_rw [hdistribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Fintype.sum_eq_single
    (((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))]
  · have hcast :
        ZMod.castHom (pow_dvd_pow p hab) (ZMod (p ^ a))
            ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ b))) =
          ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) :=
      ZMod.cast_natCast (pow_dvd_pow p hab) ((n : ℕ) + 1)
    rw [hcast]
    by_cases hxi : ((((n : ℕ) + 1 : ℕ) : ZMod (p ^ a))) = xi <;>
      simp [hxi]
  · intro z hzne
    by_cases hzxi : ZMod.castHom (pow_dvd_pow p hab)
        (ZMod (p ^ a)) z = xi
    · rw [if_pos hzxi, if_neg (Ne.symm hzne)]
    · rw [if_neg hzxi]

/-- The exact refinement identity used before Wooley (6.11). -/
theorem wooley_refined_normalized_residue_decomposition
    {Q p a b qB k : ℕ} [NeZero p] [NeZero qB]
    (hab : a ≤ b) (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) (xi : ZMod (p ^ a)) :
    (Real.sqrt (wooleyWeightedResidueMassSq gamma xi) : ℂ) *
        wooleyWeightedNormalizedResidueGridSum qB k gamma alpha xi =
      ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
        (Real.sqrt (wooleyWeightedResidueMassSq gamma z) : ℂ) *
          wooleyWeightedNormalizedResidueGridSum qB k gamma alpha z := by
  rw [wooley_sqrt_mass_mul_normalizedResidueGridSum gamma alpha]
  simp_rw [wooley_sqrt_mass_mul_normalizedResidueGridSum gamma alpha]
  exact (wooley_sum_refined_residue_grid hab gamma alpha xi).symm

/-- Wooley Lemma 6.2 for the integral exponents used in the nested
efficient-congruencing iteration. -/
theorem wooley_lemma_6_2
    {Q p a b qB k w : ℕ} [NeZero p] [NeZero qB]
    (hab : a ≤ b) (hw : 1 ≤ w) (gamma : Fin Q → ℂ)
    (alpha : Fin k → ZMod qB) (xi : ZMod (p ^ a)) :
    wooleyWeightedResidueMassSq gamma xi *
        ‖wooleyWeightedNormalizedResidueGridSum
            qB k gamma alpha xi‖ ^ (2 * w) ≤
      (p ^ (b - a) : ℝ) ^ w *
        ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
          wooleyWeightedResidueMassSq gamma z *
            ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha z‖ ^ (2 * w) := by
  let M := wooleyWeightedResidueMassSq gamma xi
  let R : ℝ :=
    ∑ z ∈ wooleyResidueRefinementFiber p a b hab xi,
      wooleyWeightedResidueMassSq gamma z *
        ‖wooleyWeightedNormalizedResidueGridSum
            qB k gamma alpha z‖ ^ (2 * w)
  by_cases hMzero : M = 0
  · have hR : 0 ≤ R := by
      dsimp [R]
      exact Finset.sum_nonneg fun z hz => mul_nonneg
        (wooleyWeightedResidueMassSq_nonneg gamma z) (by positivity)
    dsimp [M] at hMzero
    rw [hMzero, zero_mul]
    exact mul_nonneg (by positivity) hR
  · have hMpos : 0 < M := lt_of_le_of_ne
      (wooleyWeightedResidueMassSq_nonneg gamma xi) (Ne.symm hMzero)
    have hholder := wooley_weighted_complex_sum_pow_le
      (wooleyResidueRefinementFiber p a b hab xi)
      (fun z => wooleyWeightedResidueMassSq gamma z)
      (fun z => wooleyWeightedNormalizedResidueGridSum
        qB k gamma alpha z) hw
      (fun z => wooleyWeightedResidueMassSq_nonneg gamma z)
    have hdecomp := wooley_refined_normalized_residue_decomposition
      hab gamma alpha xi
    have hsource :
        M ^ w *
            ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha xi‖ ^ (2 * w) ≤
          (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := by
      rw [← hdecomp] at hholder
      simpa only [M, R, wooleyResidueRefinementFiber_card hab xi,
        wooley_sum_refined_residue_mass hab gamma xi,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, pow_mul,
        Real.sq_sqrt hMpos.le, Nat.cast_pow] using hholder
    have hpow : M ^ w = M ^ (w - 1) * M := by
      conv_lhs => rw [← Nat.sub_add_cancel hw, pow_add, pow_one]
    have hfactorPos : 0 < M ^ (w - 1) := pow_pos hMpos _
    have hfactored :
        M ^ (w - 1) *
            (M * ‖wooleyWeightedNormalizedResidueGridSum
              qB k gamma alpha xi‖ ^ (2 * w)) ≤
          M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by
      rw [← mul_assoc, ← hpow]
      calc
        M ^ w *
            ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha xi‖ ^ (2 * w) ≤
            (p ^ (b - a) : ℝ) ^ w * M ^ (w - 1) * R := hsource
        _ = M ^ (w - 1) * ((p ^ (b - a) : ℝ) ^ w * R) := by ring
    exact le_of_mul_le_mul_left hfactored hfactorPos

#print axioms wooleyResidueRefinementFiber_card
#print axioms wooley_sum_refined_residue_mass
#print axioms wooley_sum_refined_residue_grid
#print axioms wooley_refined_normalized_residue_decomposition
#print axioms wooley_lemma_6_2

end

end GafniTao
