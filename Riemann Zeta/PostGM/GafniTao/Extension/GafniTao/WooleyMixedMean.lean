import GafniTao.WooleyWeightedMean

/-!
# Mixed finite means for nested efficient congruencing

This file introduces the literal finite-grid specialization of Wooley
equations (3.19)--(3.20).  In particular, separation is tested on the actual
least nonnegative residue representatives modulo `p^nu`; it is not supplied
as an abstract predicate.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Wooley's triangular number `R = r(r+1)/2`. -/
def wooleyTriangular (r : ℕ) : ℕ := r * (r + 1) / 2

/-- Two residue classes at possibly different depths are separated modulo
`p^nu`, as in the condition following equation (3.20). -/
def wooleyResiduesSeparated {p a b : ℕ}
    (nu : ℕ) (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : Prop :=
  xi.val % (p ^ nu) ≠ eta.val % (p ^ nu)

instance {p a b nu : ℕ} :
    DecidableRel (wooleyResiduesSeparated (p := p) (a := a) (b := b) nu) :=
  fun xi eta => Classical.propDecidable
    (wooleyResiduesSeparated nu xi eta)

/-- The local mixed moment in Wooley equation (3.20), specialized to the
monomial phase and a finite coefficient family. -/
def wooleyMixedResidueGridMoment {Q : ℕ}
    (s k r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : ℝ :=
  (((p ^ B) ^ k : ℕ) : ℝ)⁻¹ *
    ∑ alpha : Fin k → ZMod (p ^ B),
      ‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
        ‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha eta‖ ^
            (2 * (s - wooleyTriangular r))

/-- The aggregate separated mixed mean `K^r_{a,b}` from (3.19). -/
def wooleyMixedGridMean {Q : ℕ}
    (s k r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) : ℝ :=
  if wooleyWeightedMassSq gamma = 0 then 0
  else (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
    ∑ xi : ZMod (p ^ a),
      ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
            wooleyMixedResidueGridMoment s k r p B a b gamma xi eta

theorem wooleyTriangular_zero : wooleyTriangular 0 = 0 := by
  simp [wooleyTriangular]

theorem wooleyTriangular_one : wooleyTriangular 1 = 1 := by
  norm_num [wooleyTriangular]

theorem wooleyMixedResidueGridMoment_nonneg {Q : ℕ}
    (s k r p B a b : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) :
    0 ≤ wooleyMixedResidueGridMoment s k r p B a b gamma xi eta := by
  unfold wooleyMixedResidueGridMoment
  positivity

theorem wooleyMixedGridMean_nonneg {Q : ℕ}
    (s k r p B a b nu : ℕ) [NeZero p] [NeZero (p ^ B)]
    (gamma : Fin Q → ℂ) :
    0 ≤ wooleyMixedGridMean s k r p B a b nu gamma := by
  unfold wooleyMixedGridMean
  split_ifs with hmass
  · exact le_rfl
  · have hxi (xi : ZMod (p ^ a)) :
        0 ≤ wooleyWeightedResidueMassSq gamma xi :=
      wooleyWeightedResidueMassSq_nonneg gamma xi
    have heta (eta : ZMod (p ^ b)) :
        0 ≤ wooleyWeightedResidueMassSq gamma eta :=
      wooleyWeightedResidueMassSq_nonneg gamma eta
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro xi hxiMem
    apply Finset.sum_nonneg
    intro eta hetaMem
    exact mul_nonneg (mul_nonneg (hxi xi) (heta eta))
      (wooleyMixedResidueGridMoment_nonneg
        s k r p B a b gamma xi eta)

#print axioms wooleyTriangular_zero
#print axioms wooleyTriangular_one
#print axioms wooleyMixedResidueGridMoment_nonneg
#print axioms wooleyMixedGridMean_nonneg

end

end GafniTao
