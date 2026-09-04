import GafniTao.WooleyEquation723

/-!
# From local equation (7.23) to aggregate equation (7.24)

This is the exact source summation in (3.19).  Zero-mass residue classes
are discharged separately, and the remaining refinement sums are flattened
by the proved one-sided refinement identity.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_equation_7_24_of_local
    {k p B s r a b nu bPrime : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (hnua : nu ≤ a) (haPrime : a ≤ bPrime) (D : ℝ) (hD : 0 ≤ D)
    (hlocal : ∀ (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)),
      wooleyResiduesSeparated nu xi eta →
      wooleySourceResidueMassSq gamma (p ^ a) xi ≠ 0 →
      wooleySourceResidueMassSq gamma (p ^ b) eta ≠ 0 →
      wooleySourceResidueMassSq gamma (p ^ a) xi *
          wooleySourcePolynomialMixedResidueMoment
            phi s r p B a b gamma xi eta ≤
        D *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p a bPrime haPrime xi,
            wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
              wooleySourcePolynomialMixedResidueMoment
                phi s r p B bPrime b gamma xiPrime eta) :
    wooleySourcePolynomialMixedMean phi s r p B a b nu gamma ≤
      D * wooleySourcePolynomialMixedMean
        phi s r p B bPrime b nu gamma := by
  unfold wooleySourcePolynomialMixedMean
  split_ifs with hmass
  · simp
  · have hsum :
      (∑ xi : ZMod (p ^ a),
        ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
          wooleySourceResidueMassSq gamma (p ^ a) xi *
            wooleySourceResidueMassSq gamma (p ^ b) eta *
              wooleySourcePolynomialMixedResidueMoment
                phi s r p B a b gamma xi eta) ≤
        D *
          ∑ xiPrime : ZMod (p ^ bPrime),
            ∑ eta : ZMod (p ^ b) with
                wooleyResiduesSeparated nu xiPrime eta,
              wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
                wooleySourceResidueMassSq gamma (p ^ b) eta *
                  wooleySourcePolynomialMixedResidueMoment
                    phi s r p B bPrime b gamma xiPrime eta := by
      calc
        _ ≤ ∑ xi : ZMod (p ^ a),
            ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
              wooleySourceResidueMassSq gamma (p ^ b) eta *
                (D *
                  ∑ xiPrime ∈
                      wooleyResidueRefinementFiber p a bPrime haPrime xi,
                    wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
                      wooleySourcePolynomialMixedResidueMoment
                        phi s r p B bPrime b gamma xiPrime eta) := by
          apply Finset.sum_le_sum
          intro xi hxi
          apply Finset.sum_le_sum
          intro eta heta
          by_cases hxiMass :
              wooleySourceResidueMassSq gamma (p ^ a) xi = 0
          · rw [hxiMass]
            simp
            exact mul_nonneg
              (wooleySourceResidueMassSq_nonneg gamma (p ^ b) eta)
              (mul_nonneg hD (Finset.sum_nonneg fun _ _ =>
                mul_nonneg
                  (wooleySourceResidueMassSq_nonneg gamma (p ^ bPrime) _)
                  (wooleySourcePolynomialMixedResidueMoment_nonneg
                    phi s r p B bPrime b gamma _ eta)))
          · by_cases hetaMass :
                wooleySourceResidueMassSq gamma (p ^ b) eta = 0
            · rw [hetaMass]
              simp
            · have hbound := hlocal xi eta (Finset.mem_filter.mp heta).2
                  hxiMass hetaMass
              have hmul := mul_le_mul_of_nonneg_left hbound
                (wooleySourceResidueMassSq_nonneg gamma (p ^ b) eta)
              calc
                wooleySourceResidueMassSq gamma (p ^ a) xi *
                    wooleySourceResidueMassSq gamma (p ^ b) eta *
                      wooleySourcePolynomialMixedResidueMoment
                        phi s r p B a b gamma xi eta =
                  wooleySourceResidueMassSq gamma (p ^ b) eta *
                    (wooleySourceResidueMassSq gamma (p ^ a) xi *
                      wooleySourcePolynomialMixedResidueMoment
                        phi s r p B a b gamma xi eta) := by ring
                _ ≤ wooleySourceResidueMassSq gamma (p ^ b) eta *
                    (D *
                      ∑ xiPrime ∈
                          wooleyResidueRefinementFiber p a bPrime haPrime xi,
                        wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
                          wooleySourcePolynomialMixedResidueMoment
                            phi s r p B bPrime b gamma xiPrime eta) := hmul
        _ = D *
          ∑ xiPrime : ZMod (p ^ bPrime),
            ∑ eta : ZMod (p ^ b) with
                wooleyResiduesSeparated nu xiPrime eta,
              wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
                wooleySourceResidueMassSq gamma (p ^ b) eta *
                  wooleySourcePolynomialMixedResidueMoment
                    phi s r p B bPrime b gamma xiPrime eta := by
          rw [← wooley_sum_left_refinement hnua haPrime
            (fun xiPrime eta =>
              wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
                wooleySourceResidueMassSq gamma (p ^ b) eta *
                  wooleySourcePolynomialMixedResidueMoment
                    phi s r p B bPrime b gamma xiPrime eta)]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro xi hxi
          apply Finset.sum_congr rfl
          intro eta heta
          apply Finset.sum_congr rfl
          intro xiPrime hxiPrime
          ring
    have hinv : 0 ≤ (wooleySourceMassSq gamma)⁻¹ ^ 2 := sq_nonneg _
    calc
      (wooleySourceMassSq gamma)⁻¹ ^ 2 * _ ≤
          (wooleySourceMassSq gamma)⁻¹ ^ 2 * (D * _) :=
        mul_le_mul_of_nonneg_left hsum hinv
      _ = D * ((wooleySourceMassSq gamma)⁻¹ ^ 2 * _) := by ring

#print axioms wooley_equation_7_24_of_local

end

end GafniTao
