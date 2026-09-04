import GafniTao.WooleyAffineComposition

/-!
# Reverse orthogonality in Wooley equation (7.21)

The system produced before (7.17) is uniform in the coefficient sequence.
Consequently it may be applied after restricting that sequence to one class
modulo `p^H`.  This file proves that the resulting outer Fourier average is
literally the original mixed residue moment at
`kappa = p^a zeta + xi` modulo `p^(a+H)`.
-/

namespace GafniTao

noncomputable section

/-- Equation (7.21), with the same lower system `Psi` simultaneously for all
refined residue classes.  Zero-mass classes are excluded here; their weighted
contribution to (7.20) is zero and is handled when the finite sum is assembled.
-/
theorem wooley_equation_7_21_native
    {k r p c a b B nu s gammaVal H : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gammaVal * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gammaVal)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gammaVal)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (gamma : WooleySourceSequence)
    (hxiMass : wooleySourceResidueMassSq gamma (p ^ a)
      (xi : ZMod (p ^ a)) ≠ 0)
    (hetaMass : wooleySourceResidueMassSq gamma (p ^ b)
      (eta : ZMod (p ^ b)) ≠ 0) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gammaVal) ∧
      wooleySourceNormalizedMixedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          (p ^ B) (wooleyTriangular r) (s - wooleyTriangular r)
          (wooleyAffinePullback gamma (p ^ a)
            (pow_pos hpPrime.pos a) xi)
          (wooleyAffinePullback gamma (p ^ b)
            (pow_pos hpPrime.pos b) eta) =
        wooleySourceInsertedNormalizedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gammaVal)
          (wooleyTriangular r) (s - wooleyTriangular r)
          (wooleyAffinePullback gamma (p ^ a)
            (pow_pos hpPrime.pos a) xi)
          (wooleyAffinePullback gamma (p ^ b)
            (pow_pos hpPrime.pos b) eta) ∧
      ∀ zeta : ZMod (p ^ H),
        wooleySourceResidueMassSq gamma (p ^ (a + H))
            ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + xi : ℤ) :
              ZMod (p ^ (a + H))) ≠ 0 →
        wooleySourceInsertedNormalizedRealAverage
            (wooleyAffinePolynomialSystem phi (p ^ a) xi)
            (wooleyAffinePolynomialSystem phi (p ^ b) eta)
            Psi (p ^ B)
            (p ^ wooleySection7BPrimeNat k r a b gammaVal)
            (wooleyTriangular r) (s - wooleyTriangular r)
            (wooleySourceResidueSequence
              (wooleyAffinePullback gamma (p ^ a)
                (pow_pos hpPrime.pos a) xi)
              (p ^ H) zeta)
            (wooleyAffinePullback gamma (p ^ b)
              (pow_pos hpPrime.pos b) eta) =
          wooleySourcePolynomialMixedResidueMoment
            phi s r p B (a + H) b gamma
            ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + xi : ℤ) :
              ZMod (p ^ (a + H)))
            (eta : ZMod (p ^ b)) := by
  letI : NeZero (p ^ wooleySection7BPrimeNat k r a b gammaVal) :=
    ⟨pow_ne_zero _ hpPrime.ne_zero⟩
  letI : NeZero (p ^ H) := ⟨pow_ne_zero _ hpPrime.ne_zero⟩
  obtain ⟨Psi, hPsi, huniform⟩ :=
    wooley_exists_uniform_shifted_normalized_identity
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal xi eta homega hcop hsep hdiff phi hphi
  have hleftBase : wooleySourceMassSq
      (wooleyAffinePullback gamma (p ^ a)
        (pow_pos hpPrime.pos a) xi) ≠ 0 := by
    rw [wooleySourceMassSq_affinePullback]
    simpa using hxiMass
  have hrightBase : wooleySourceMassSq
      (wooleyAffinePullback gamma (p ^ b)
        (pow_pos hpPrime.pos b) eta) ≠ 0 := by
    rw [wooleySourceMassSq_affinePullback]
    simpa using hetaMass
  have horiginal := huniform (wooleyTriangular r)
    (s - wooleyTriangular r)
    (wooleyAffinePullback gamma (p ^ a) (pow_pos hpPrime.pos a) xi)
    (wooleyAffinePullback gamma (p ^ b) (pow_pos hpPrime.pos b) eta)
    hleftBase hrightBase
  refine ⟨Psi, hPsi, ?_, ?_⟩
  · exact horiginal
  intro zeta hkappaMass
  let leftBase := wooleyAffinePullback gamma (p ^ a)
    (pow_pos hpPrime.pos a) xi
  let leftRestricted := wooleySourceResidueSequence leftBase (p ^ H) zeta
  let right := wooleyAffinePullback gamma (p ^ b)
    (pow_pos hpPrime.pos b) eta
  have hzetaInt :
      ((((zeta.val : ℕ) : ℤ) : ZMod (p ^ H))) = zeta := by
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val zeta
  have hkappaMassProd := hkappaMass
  rw [pow_add] at hkappaMassProd
  have hleft : wooleySourceMassSq leftRestricted ≠ 0 := by
    dsimp only [leftRestricted, leftBase]
    rw [wooleySourceMassSq_residueSequence,
      ← hzetaInt,
      wooleySourceResidueMassSq_affinePullback gamma (p ^ a) (p ^ H)
        (pow_pos hpPrime.pos a) (pow_pos hpPrime.pos H) xi (zeta.val : ℤ)]
    exact hkappaMassProd
  have hright : wooleySourceMassSq right ≠ 0 := by
    dsimp only [right]
    rw [wooleySourceMassSq_affinePullback]
    simpa using hetaMass
  have hid := huniform (wooleyTriangular r) (s - wooleyTriangular r)
    leftRestricted right hleft hright
  rw [← hid]
  unfold wooleySourceNormalizedMixedRealAverage
    wooleySourcePolynomialMixedResidueMoment
  dsimp only [leftRestricted, leftBase, right]
  simp_rw [wooleySourceNormalizedPolynomialSum_residueSequence]
  have hleftSum (alpha : Fin k → ZMod (p ^ B)) :
      wooleySourceNormalizedPolynomialResidueSum
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePullback gamma (p ^ a)
            (pow_pos hpPrime.pos a) xi) alpha zeta =
        wooleySourceNormalizedPolynomialResidueSum phi gamma alpha
          ((((p ^ a : ℕ) : ℤ) * (zeta.val : ℤ) + xi : ℤ) :
            ZMod ((p ^ a) * (p ^ H))) := by
    conv_lhs => rw [← hzetaInt]
    exact wooleySourceNormalizedPolynomialResidueSum_affinePullback
      phi gamma alpha (p ^ a) (p ^ H)
        (pow_pos hpPrime.pos a) (pow_pos hpPrime.pos H) xi (zeta.val : ℤ)
  simp_rw [hleftSum]
  simp_rw [wooleySourceNormalizedPolynomialSum_affinePullback]
  rw [pow_add]

#print axioms wooley_equation_7_21_native

end

end GafniTao
