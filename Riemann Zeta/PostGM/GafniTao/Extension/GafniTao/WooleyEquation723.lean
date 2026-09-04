import GafniTao.WooleyRefinementTower

/-!
# Wooley equation (7.23)

This file combines the local hard-branch estimate, the integrated form of
(7.22), and the exact two-stage refinement bijection.  Consequently the
right side has precisely the single refinement sum appearing in (7.23),
with no spurious fiber cardinality.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_equation_7_23_native
    {k r p c a b B nu s : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : ∀ gammaVal : ℕ, gammaVal < nu → gammaVal * k ≤ a)
    (hBPrime : ∀ gammaVal : ℕ, gammaVal < nu →
      (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (gamma : WooleySourceSequence)
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b))
    (hseparated : wooleyResiduesSeparated nu xi eta)
    (hxiMass : wooleySourceResidueMassSq gamma (p ^ a) xi ≠ 0)
    (hetaMass : wooleySourceResidueMassSq gamma (p ^ b) eta ≠ 0)
    (C loss : ℝ) (hCloss : 0 ≤ C * loss)
    (hpoint : ∀ (gammaVal : ℕ), gammaVal < nu →
      ∀ (Psi : WooleyPolynomialSystem r),
        Psi.Spaced p (a - (k - r) * gammaVal) →
        ∀ alpha : Fin k → ZMod (p ^ B),
          wooleySourcePolynomialMean (wooleyTriangular r)
              (p ^ wooleySection7BPrimeNat k r a b gammaVal) Psi
              (wooleySourceTwist
                (wooleyAffinePullback gamma (p ^ a)
                  (pow_pos hpPrime.pos a) (xi.val : ℤ))
                (fun n => wooleySourcePolynomialPhase
                  (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
                  alpha n)) ≤
            C * loss *
              wooleySourcePolynomialConditionedMean (wooleyTriangular r)
                (p ^ wooleySection7BPrimeNat k r a b gammaVal)
                (p ^ wooleySection7HPrime k r a b gammaVal) Psi
                (wooleySourceTwist
                  (wooleyAffinePullback gamma (p ^ a)
                    (pow_pos hpPrime.pos a) (xi.val : ℤ))
                  (fun n => wooleySourcePolynomialPhase
                    (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
                    alpha n))) :
    ∃ gammaVal : ℕ, ∃ hgammaVal : gammaVal < nu,
      wooleySourceResidueMassSq gamma (p ^ a) xi *
          wooleySourcePolynomialMixedResidueMoment
            phi s r p B a b gamma xi eta ≤
        C * loss *
          (p ^ (wooleySection7NextB k r b -
            (a + wooleySection7HPrime k r a b gammaVal)) : ℝ) ^
              wooleyTriangular r *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p a
              (wooleySection7NextB k r b)
              ((Nat.le_add_right a (wooleySection7HPrime k r a b gammaVal)).trans
                (wooley_section7_a_add_HPrime_le_nextB hr
                  (hBPrime gammaVal hgammaVal))) xi,
            wooleySourceResidueMassSq gamma
                (p ^ wooleySection7NextB k r b) xiPrime *
              wooleySourcePolynomialMixedResidueMoment phi s r p B
                (wooleySection7NextB k r b) b gamma xiPrime eta := by
  obtain ⟨gammaVal, hgammaVal, hlocal⟩ :=
    wooley_equations_7_18_to_7_21_local_bound
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime phi hphi gamma xi eta
      hseparated hxiMass hetaMass C loss hpoint
  let H := wooleySection7HPrime k r a b gammaVal
  let bPrime := wooleySection7NextB k r b
  let hAb : a + H ≤ bPrime :=
    wooley_section7_a_add_HPrime_le_nextB hr (hBPrime gammaVal hgammaVal)
  let haB : a ≤ bPrime := (Nat.le_add_right a H).trans hAb
  let factor : ℝ := (p ^ (bPrime - (a + H)) : ℝ) ^ wooleyTriangular r
  let F : ZMod (p ^ bPrime) → ℝ := fun xiPrime =>
    wooleySourceResidueMassSq gamma (p ^ bPrime) xiPrime *
      wooleySourcePolynomialMixedResidueMoment phi s r p B
        bPrime b gamma xiPrime eta
  have hrefine :
      (∑ zeta : ZMod (p ^ H),
        wooleySourceResidueMassSq gamma (p ^ (a + H))
            (wooleyResidueLift p a H xi zeta) *
          wooleySourcePolynomialMixedResidueMoment phi s r p B
            (a + H) b gamma (wooleyResidueLift p a H xi zeta) eta) ≤
        factor *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p a bPrime haB xi,
            F xiPrime := by
    have hsum :
        (∑ zeta : ZMod (p ^ H),
          wooleySourceResidueMassSq gamma (p ^ (a + H))
              (wooleyResidueLift p a H xi zeta) *
            wooleySourcePolynomialMixedResidueMoment phi s r p B
              (a + H) b gamma (wooleyResidueLift p a H xi zeta) eta) ≤
          ∑ zeta : ZMod (p ^ H), factor *
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p
                (a + H) bPrime hAb (wooleyResidueLift p a H xi zeta),
              F xiPrime := by
      apply Finset.sum_le_sum
      intro zeta hzeta
      simpa only [H, bPrime, hAb, factor, F] using
        (wooley_equation_7_22_integrated_native
          (k := k) (p := p) (r := r) (a := a) (b := b) (nu := nu)
          (gammaVal := gammaVal) (B := B) (s := s) hr
          (hBPrime gammaVal hgammaVal) phi gamma
          (wooleyResidueLift p a H xi zeta) eta)
    calc
      _ ≤ ∑ zeta : ZMod (p ^ H), factor *
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p
                (a + H) bPrime hAb (wooleyResidueLift p a H xi zeta),
              F xiPrime := hsum
      _ = factor *
          ∑ kappa ∈ wooleyResidueRefinementFiber p a (a + H)
              (Nat.le_add_right a H) xi,
            ∑ xiPrime ∈ wooleyResidueRefinementFiber p
                (a + H) bPrime hAb kappa, F xiPrime := by
        rw [← mul_sum]
        congr 1
        exact wooley_sum_residueLift xi (fun kappa =>
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p
              (a + H) bPrime hAb kappa, F xiPrime)
      _ = factor *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p a bPrime haB xi,
            F xiPrime := by
        rw [wooley_sum_refinement_tower]
  have hlocalLift :
      wooleySourceResidueMassSq gamma (p ^ a) xi *
          wooleySourcePolynomialMixedResidueMoment
            phi s r p B a b gamma xi eta ≤
        C * loss *
          ∑ zeta : ZMod (p ^ H),
            wooleySourceResidueMassSq gamma (p ^ (a + H))
                (wooleyResidueLift p a H xi zeta) *
              wooleySourcePolynomialMixedResidueMoment phi s r p B
                (a + H) b gamma (wooleyResidueLift p a H xi zeta) eta := by
    simpa only [H, wooleyResidueLift_eq_section7] using hlocal
  have hscaled := mul_le_mul_of_nonneg_left hrefine hCloss
  refine ⟨gammaVal, hgammaVal, ?_⟩
  calc
    _ ≤ C * loss *
          ∑ zeta : ZMod (p ^ H),
            wooleySourceResidueMassSq gamma (p ^ (a + H))
                (wooleyResidueLift p a H xi zeta) *
              wooleySourcePolynomialMixedResidueMoment phi s r p B
                (a + H) b gamma (wooleyResidueLift p a H xi zeta) eta := hlocalLift
    _ ≤ C * loss * (factor *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p a bPrime haB xi,
            F xiPrime) := hscaled
    _ = C * loss * factor *
          ∑ xiPrime ∈ wooleyResidueRefinementFiber p a bPrime haB xi,
            F xiPrime := by ring
    _ = _ := by
      rfl

#print axioms wooley_equation_7_23_native

end

end GafniTao
