import GafniTao.WooleySection7MomentIdentity
import GafniTao.WooleySection7SourceShift

/-!
# Analytic equation (7.17) with the two source residue representatives

The tuple congruence in `WooleySection7SourceShift` is converted here into
the raw and normalized Fourier-average identities.  This is the source-entry
variant needed for the local mixed moment: its two systems are literally the
pullbacks along `p^a y + xi` and `p^b z + eta`.
-/

namespace GafniTao

noncomputable section

/-- Raw complex equation (7.17) for arbitrary source residue
representatives. -/
theorem wooley_equation_7_17_shifted_raw_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gamma)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleySourceRawMixedComplexAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          (p ^ B) R S left right =
        wooleySourceInsertedComplexAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
  obtain ⟨Psi, hPsi, h717⟩ :=
    wooley_equation_7_17_shifted_spaced_positive_native
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal xi eta homega hcop hsep hdiff phi hphi left right
  refine ⟨Psi, hPsi, ?_⟩
  rw [wooleySourceRawMixedComplexAverage_eq_tuple,
    wooleySourceInsertedComplexAverage_eq_tuple]
  exact h717

/-- Real raw equation (7.17) for arbitrary source residue
representatives. -/
theorem wooley_equation_7_17_shifted_raw_real_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gamma)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleySourceRawMixedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          (p ^ B) R S left right =
        wooleySourceInsertedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
  obtain ⟨Psi, hPsi, hraw⟩ := wooley_equation_7_17_shifted_raw_native
    hpPrime hc hr hrk hkp hMB hgammaK hBPrime
      omegaVal xi eta homega hcop hsep hdiff phi hphi left right
  refine ⟨Psi, hPsi, ?_⟩
  apply Complex.ofReal_injective
  rw [← wooleySourceRawMixedComplexAverage_eq_ofReal,
    ← wooleySourceInsertedComplexAverage_eq_ofReal]
  exact hraw

/-- Normalized source equation (7.17), equivalently the exact identity
preceding (7.18), in the nonzero residue-mass branch. -/
theorem wooley_equation_7_17_shifted_normalized_nonzero_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gamma)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence)
    (hleft : wooleySourceMassSq left ≠ 0)
    (hright : wooleySourceMassSq right ≠ 0) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      wooleySourceNormalizedMixedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          (p ^ B) R S left right =
        wooleySourceInsertedNormalizedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
  obtain ⟨Psi, hPsi, hraw⟩ := wooley_equation_7_17_shifted_raw_real_native
    hpPrime hc hr hrk hkp hMB hgammaK hBPrime
      omegaVal xi eta homega hcop hsep hdiff phi hphi left right
  refine ⟨Psi, hPsi, ?_⟩
  rw [wooleySourceNormalizedMixedRealAverage_eq_mass_mul_raw
    _ _ _ _ _ left right hleft hright]
  rw [wooleySourceInsertedNormalizedRealAverage_eq_mass_mul_raw
    _ _ Psi _ _ _ _ left right hleft hright]
  rw [hraw]

/-- Uniform analytic form of (7.17).  The same lower system `Psi` works for
all coefficient sequences, which is the quantifier order required when the
conditioned mean in (7.19) is expanded residue class by residue class. -/
theorem wooley_exists_uniform_shifted_normalized_identity
    {k r p c a b B nu gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal xi eta : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : xi - eta = omegaVal * (p : ℤ) ^ gamma)
    (hdiff : xi - eta ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      ∀ (R S : ℕ) (left right : WooleySourceSequence),
        wooleySourceMassSq left ≠ 0 → wooleySourceMassSq right ≠ 0 →
        wooleySourceNormalizedMixedRealAverage
            (wooleyAffinePolynomialSystem phi (p ^ a) xi)
            (wooleyAffinePolynomialSystem phi (p ^ b) eta)
            (p ^ B) R S left right =
          wooleySourceInsertedNormalizedRealAverage
            (wooleyAffinePolynomialSystem phi (p ^ a) xi)
            (wooleyAffinePolynomialSystem phi (p ^ b) eta)
            Psi (p ^ B)
            (p ^ wooleySection7BPrimeNat k r a b gamma)
            R S left right := by
  obtain ⟨Psi, hPsi, hforcing⟩ :=
    wooleySection7_exists_uniform_shifted_forcing
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal xi eta homega hcop hsep hdiff phi hphi
  refine ⟨Psi, hPsi, ?_⟩
  intro R S left right hleft hright
  have hrawComplex :
      wooleySourceRawMixedComplexAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          (p ^ B) R S left right =
        wooleySourceInsertedComplexAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
    rw [wooleySourceRawMixedComplexAverage_eq_tuple,
      wooleySourceInsertedComplexAverage_eq_tuple]
    exact wooley_equation_7_17_tuple _ _ _ _ _ _ _ _ _
      (hforcing left right)
  have hrawReal :
      wooleySourceRawMixedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          (p ^ B) R S left right =
        wooleySourceInsertedRealAverage
          (wooleyAffinePolynomialSystem phi (p ^ a) xi)
          (wooleyAffinePolynomialSystem phi (p ^ b) eta)
          Psi (p ^ B)
          (p ^ wooleySection7BPrimeNat k r a b gamma)
          R S left right := by
    apply Complex.ofReal_injective
    rw [← wooleySourceRawMixedComplexAverage_eq_ofReal,
      ← wooleySourceInsertedComplexAverage_eq_ofReal]
    exact hrawComplex
  rw [wooleySourceNormalizedMixedRealAverage_eq_mass_mul_raw
    _ _ _ _ _ left right hleft hright]
  rw [wooleySourceInsertedNormalizedRealAverage_eq_mass_mul_raw
    _ _ Psi _ _ _ _ left right hleft hright]
  rw [hrawReal]

#print axioms wooley_equation_7_17_shifted_raw_native
#print axioms wooley_equation_7_17_shifted_raw_real_native
#print axioms wooley_equation_7_17_shifted_normalized_nonzero_native
#print axioms wooley_exists_uniform_shifted_normalized_identity

end

end GafniTao
