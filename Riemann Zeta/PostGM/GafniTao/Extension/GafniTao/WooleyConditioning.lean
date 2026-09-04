import GafniTao.WooleyFiniteMean

/-!
# Coefficient-one conditioning in Wooley (3.8)

This file models the residue-class normalized sums in equation (3.8).  It
also proves the exact terminal fact used in Section 12: when the source box
has length smaller than the conditioning modulus, each occupied residue
class contains one integer and the conditioned mean is exactly one.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def wooleyResidueClass (Q q : ℕ) (xi : ZMod q) : Finset (Fin Q) :=
  Finset.univ.filter fun n => ((((n : ℕ) + 1 : ℕ) : ZMod q) = xi)

def wooleyResidueMassSq (Q q : ℕ) (xi : ZMod q) : ℕ :=
  (wooleyResidueClass Q q xi).card

def wooleyResidueGridSum (qB k Q qH : ℕ) [NeZero qB]
    (alpha : Fin k → ZMod qB) (xi : ZMod qH) : ℂ :=
  ∑ n ∈ wooleyResidueClass Q qH xi,
    wooleyMonomialGridPhase qB k Q alpha n

/-- The normalized residue-class exponential sum `f_H` in (3.4). -/
def wooleyNormalizedResidueGridSum (qB k Q qH : ℕ) [NeZero qB]
    (alpha : Fin k → ZMod qB) (xi : ZMod qH) : ℂ :=
  if wooleyResidueMassSq Q qH xi = 0 then 0
  else ((Real.sqrt (wooleyResidueMassSq Q qH xi : ℝ) : ℂ)⁻¹) *
    wooleyResidueGridSum qB k Q qH alpha xi

def wooleyResidueRawMoment (s k Q qB qH : ℕ) [NeZero qB]
    (xi : ZMod qH) : ℝ :=
  ∑ alpha : Fin k → ZMod qB,
    ‖wooleyNormalizedResidueGridSum qB k Q qH alpha xi‖ ^ (2 * s)

/-- The coefficient-one specialization of Wooley's conditioned mean
`U^{B,H}_{s,k}` from (3.8). -/
def wooleyConditionedGridMean (s k Q qB qH : ℕ) [NeZero qB]
    [NeZero qH] : ℝ :=
  ((Q : ℝ)⁻¹) *
    ∑ xi : ZMod qH,
      (wooleyResidueMassSq Q qH xi : ℝ) *
        (wooleyResidueRawMoment s k Q qB qH xi /
          ((qB ^ k : ℕ) : ℝ))

theorem wooley_sourceValue_cast_injective
    {Q q : ℕ} [NeZero q] (hQq : Q < q) :
    Function.Injective
      (fun n : Fin Q => ((((n : ℕ) + 1 : ℕ) : ZMod q))) := by
  intro m n hmn
  have hmQ : (m : ℕ) + 1 ≤ Q := Nat.succ_le_iff.mpr m.isLt
  have hnQ : (n : ℕ) + 1 ≤ Q := Nat.succ_le_iff.mpr n.isLt
  have hm : (m : ℕ) + 1 < q := lt_of_le_of_lt hmQ hQq
  have hn : (n : ℕ) + 1 < q := lt_of_le_of_lt hnQ hQq
  have hval := congrArg ZMod.val hmn
  rw [ZMod.val_natCast_of_lt hm, ZMod.val_natCast_of_lt hn] at hval
  exact Fin.ext (by omega)

theorem wooleyResidueClass_card_le_one
    {Q q : ℕ} [NeZero q] (hQq : Q < q) (xi : ZMod q) :
    (wooleyResidueClass Q q xi).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro m hm n hn
  apply wooley_sourceValue_cast_injective hQq
  exact (mem_filter.mp hm).2.trans (mem_filter.mp hn).2.symm

theorem wooley_sum_residueMassSq (Q q : ℕ) [NeZero q] :
    ∑ xi : ZMod q, wooleyResidueMassSq Q q xi = Q := by
  unfold wooleyResidueMassSq wooleyResidueClass
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem wooleyNormalizedResidueGridSum_of_singleton
    {qB k Q qH : ℕ} [NeZero qB]
    {xi : ZMod qH} {n : Fin Q}
    (hclass : wooleyResidueClass Q qH xi = {n})
    (alpha : Fin k → ZMod qB) :
    wooleyNormalizedResidueGridSum qB k Q qH alpha xi =
      wooleyMonomialGridPhase qB k Q alpha n := by
  have hmass : wooleyResidueMassSq Q qH xi = 1 := by
    simp [wooleyResidueMassSq, hclass]
  simp [wooleyNormalizedResidueGridSum, hmass,
    wooleyResidueGridSum, hclass]

theorem wooleyResidueRawMoment_eq_modulusPow_mul_mass
    {s k Q qB qH : ℕ} [NeZero qB] [NeZero qH]
    (hs : 1 ≤ s) (hQqH : Q < qH) (xi : ZMod qH) :
    wooleyResidueRawMoment s k Q qB qH xi =
      ((qB ^ k : ℕ) : ℝ) * (wooleyResidueMassSq Q qH xi : ℝ) := by
  have hcard := wooleyResidueClass_card_le_one hQqH xi
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hzero | hone
  · have hmass : wooleyResidueMassSq Q qH xi = 0 := hzero
    have hs0 : s ≠ 0 := by omega
    simp [wooleyResidueRawMoment, wooleyNormalizedResidueGridSum, hmass,
      hs0]
  · obtain ⟨n, hclass⟩ := card_eq_one.mp hone
    simp_rw [wooleyResidueRawMoment,
      wooleyNormalizedResidueGridSum_of_singleton hclass]
    simp [wooleyResidueMassSq, hclass, wooleyMonomialGridPhase]

theorem wooley_conditioned_grid_mean_eq_one
    {s k Q qB qH : ℕ} [NeZero qB] [NeZero qH]
    (hs : 1 ≤ s) (hQ : 1 ≤ Q) (hQqH : Q < qH) :
    wooleyConditionedGridMean s k Q qB qH = 1 := by
  rw [wooleyConditionedGridMean]
  simp_rw [wooleyResidueRawMoment_eq_modulusPow_mul_mass hs hQqH]
  have hqB : 0 < qB := NeZero.pos qB
  have hqpow : (((qB ^ k : ℕ) : ℝ)) ≠ 0 := by positivity
  have hmassSquare (xi : ZMod qH) :
      (wooleyResidueMassSq Q qH xi : ℝ) ^ 2 =
        (wooleyResidueMassSq Q qH xi : ℝ) := by
    have hc := wooleyResidueClass_card_le_one hQqH xi
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with hz | ho
    · simp [wooleyResidueMassSq, hz]
    · simp [wooleyResidueMassSq, ho]
  have hterm (xi : ZMod qH) :
      (wooleyResidueMassSq Q qH xi : ℝ) *
          (((qB ^ k : ℕ) : ℝ) *
              (wooleyResidueMassSq Q qH xi : ℝ) /
            ((qB ^ k : ℕ) : ℝ)) =
        (wooleyResidueMassSq Q qH xi : ℝ) := by
    field_simp
    simpa [pow_two] using hmassSquare xi
  simp_rw [hterm]
  rw [← Nat.cast_sum, wooley_sum_residueMassSq]
  have hQR : (Q : ℝ) ≠ 0 := by positivity
  field_simp

#print axioms wooley_sourceValue_cast_injective
#print axioms wooleyResidueClass_card_le_one
#print axioms wooley_sum_residueMassSq
#print axioms wooleyResidueRawMoment_eq_modulusPow_mul_mass
#print axioms wooley_conditioned_grid_mean_eq_one

end

end GafniTao
