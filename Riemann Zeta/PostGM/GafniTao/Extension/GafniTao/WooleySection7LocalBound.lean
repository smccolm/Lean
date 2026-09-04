import GafniTao.WooleySection7ConditionedExpansion

/-!
# The local hard-branch estimate through equation (7.21)

This theorem consumes the actual separated residue pair, extracts its
`p`-adic valuation, uses the single lower system governing both (7.18) and
(7.21), and expands the conditioned mean into the literal refined mixed
moments.  The lower-degree concentration estimate is kept as the pointwise
input that the induction hypothesis supplies.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_equations_7_18_to_7_21_local_bound
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
    (C loss : ℝ)
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
    ∃ gammaVal : ℕ, gammaVal < nu ∧
      wooleySourceResidueMassSq gamma (p ^ a) xi *
          wooleySourcePolynomialMixedResidueMoment
            phi s r p B a b gamma xi eta ≤
        C * loss *
          ∑ zeta : ZMod (p ^ wooleySection7HPrime k r a b gammaVal),
            wooleySourceResidueMassSq gamma
                (p ^ (a + wooleySection7HPrime k r a b gammaVal))
                ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + (xi.val : ℤ) : ℤ) :
                  ZMod (p ^ (a + wooleySection7HPrime k r a b gammaVal))) *
              wooleySourcePolynomialMixedResidueMoment phi s r p B
                (a + wooleySection7HPrime k r a b gammaVal) b gamma
                ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + (xi.val : ℤ) : ℤ) :
                  ZMod (p ^ (a + wooleySection7HPrime k r a b gammaVal)))
                eta := by
  obtain ⟨gammaVal, omegaVal, hgammaVal, hcop, hfactor⟩ :=
    wooley_padic_separation hpPrime hseparated
  have hdiff : (xi.val : ℤ) - (eta.val : ℤ) ≠ 0 := by
    simpa only [wooleyResidueDifference] using
      (wooleyResidueDifference_ne_zero_of_separated hseparated)
  have homega : omegaVal ≠ 0 := by
    intro hw
    rw [hw, zero_mul] at hfactor
    exact hdiff (by simpa only [wooleyResidueDifference] using hfactor)
  let H := wooleySection7HPrime k r a b gammaVal
  let qPrime := p ^ wooleySection7BPrimeNat k r a b gammaVal
  let left := wooleyAffinePullback gamma (p ^ a)
    (pow_pos hpPrime.pos a) (xi.val : ℤ)
  let right := wooleyAffinePullback gamma (p ^ b)
    (pow_pos hpPrime.pos b) (eta.val : ℤ)
  letI : NeZero qPrime := ⟨pow_ne_zero _ hpPrime.ne_zero⟩
  letI : NeZero (p ^ H) := ⟨pow_ne_zero _ hpPrime.ne_zero⟩
  obtain ⟨Psi, hPsi, horiginal, hreverse⟩ :=
    wooley_equation_7_21_native
      (s := s) (H := H) hpPrime hc hr hrk hkp hMB
      (hgammaK gammaVal hgammaVal) (hBPrime gammaVal hgammaVal)
      omegaVal (xi.val : ℤ) (eta.val : ℤ) homega hcop
      (by simpa only [wooleyResidueDifference] using hfactor) hdiff
      phi hphi gamma (by simpa using hxiMass) (by simpa using hetaMass)
  have houter := wooley_equation_7_19_outer_native
    (q := p ^ B) (qPrime := qPrime) (qH := p ^ H)
    (R := wooleyTriangular r) (S := s - wooleyTriangular r)
    (leftPhi := wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
    (rightPhi := wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
    (Psi := Psi) (left := left) (right := right)
    (C := C) (loss := loss)
    (hpoint gammaVal hgammaVal Psi hPsi)
  have hleftMass : wooleySourceMassSq left =
      wooleySourceResidueMassSq gamma (p ^ a) xi := by
    dsimp only [left]
    rw [wooleySourceMassSq_affinePullback]
    simp
  have hleftNonzero : wooleySourceMassSq left ≠ 0 := by
    rw [hleftMass]
    exact hxiMass
  have hexpand := wooley_equation_7_20_expansion
    (leftPhi := wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
    (rightPhi := wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
    (Psi := Psi) (q := p ^ B) (qPrime := qPrime) (qH := p ^ H)
    (R := wooleyTriangular r) (S := s - wooleyTriangular r)
    (left := left) (right := right) hleftNonzero
  have hlocalIdentity :
      wooleySourcePolynomialMixedResidueMoment
          phi s r p B a b gamma xi eta =
        wooleySourceInsertedNormalizedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
          (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
          Psi (p ^ B) qPrime (wooleyTriangular r)
          (s - wooleyTriangular r) left right := by
    rw [wooleySourcePolynomialMixedResidueMoment_eq_pullbackAverage]
    exact horiginal
  have hmul := mul_le_mul_of_nonneg_left houter
    (wooleySourceMassSq_nonneg left)
  refine ⟨gammaVal, hgammaVal, ?_⟩
  calc
    wooleySourceResidueMassSq gamma (p ^ a) xi *
        wooleySourcePolynomialMixedResidueMoment
          phi s r p B a b gamma xi eta =
      wooleySourceMassSq left *
        wooleySourceInsertedNormalizedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
          (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
          Psi (p ^ B) qPrime (wooleyTriangular r)
          (s - wooleyTriangular r) left right := by
      rw [hleftMass, hlocalIdentity]
    _ ≤ wooleySourceMassSq left *
        (C * loss * wooleySection7ConditionedInsertedAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
          (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
          Psi (p ^ B) qPrime (p ^ H) (wooleyTriangular r)
          (s - wooleyTriangular r) left right) := hmul
    _ = C * loss *
        ∑ zeta : ZMod (p ^ H),
          wooleySourceResidueMassSq left (p ^ H) zeta *
            wooleySourceInsertedNormalizedRealAverage
              (wooleyAffinePolynomialSystem phi (p ^ a) (xi.val : ℤ))
              (wooleyAffinePolynomialSystem phi (p ^ b) (eta.val : ℤ))
              Psi (p ^ B) qPrime (wooleyTriangular r)
           (s - wooleyTriangular r)
               (wooleySourceResidueSequence left (p ^ H) zeta) right := by
      rw [← hexpand]
      ring
    _ = C * loss *
        ∑ zeta : ZMod (p ^ H),
          wooleySourceResidueMassSq gamma (p ^ (a + H))
              ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + (xi.val : ℤ) : ℤ) :
                ZMod (p ^ (a + H))) *
            wooleySourcePolynomialMixedResidueMoment phi s r p B
              (a + H) b gamma
              ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + (xi.val : ℤ) : ℤ) :
                ZMod (p ^ (a + H))) eta := by
      apply congrArg (fun x : ℝ => C * loss * x)
      apply Finset.sum_congr rfl
      intro zeta hzeta
      have hzetaInt :
          ((((zeta.val : ℕ) : ℤ) : ZMod (p ^ H))) = zeta := by
        simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val zeta
      have hetaInt :
          ((((eta.val : ℕ) : ℤ) : ZMod (p ^ b))) = eta := by
        simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val eta
      have hmass := wooleySourceResidueMassSq_affinePullback
        gamma (p ^ a) (p ^ H) (pow_pos hpPrime.pos a)
          (pow_pos hpPrime.pos H) (xi.val : ℤ) (zeta.val : ℤ)
      conv_lhs at hmass => rw [hzetaInt]
      rw [← pow_add] at hmass
      by_cases hkappa :
          wooleySourceResidueMassSq gamma (p ^ (a + H))
              ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + (xi.val : ℤ) : ℤ) :
                ZMod (p ^ (a + H))) = 0
      · rw [hmass, hkappa]
        simp
      · rw [hmass, hreverse zeta hkappa, hetaInt]
  
#print axioms wooley_equations_7_18_to_7_21_local_bound

end

end GafniTao
