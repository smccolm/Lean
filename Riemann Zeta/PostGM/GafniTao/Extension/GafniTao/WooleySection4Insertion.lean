import GafniTao.WooleySection4Congruence
import GafniTao.WooleySection7MomentIdentity

/-!
# Wooley equation (4.12)

The first Fourier grid imposes the original translated congruences.  The
congruence theorem from `WooleySection4Congruence` shows that the second grid
is redundant.  This file inserts that grid in the literal normalized source
mean, retaining the alpha-dependent coefficient twist used in (4.10)--(4.13).
-/

namespace GafniTao

noncomputable section

theorem wooleySourceNormalizedMixedRealAverage_self_zero
    {k q s : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    wooleySourceNormalizedMixedRealAverage
        phi phi q s 0 gamma gamma =
      wooleySourcePolynomialMean s q phi gamma := by
  unfold wooleySourceNormalizedMixedRealAverage
    wooleySourcePolynomialMean
  simp

theorem wooleySourceInsertedNormalizedRealAverage_self_zero
    {k r q qPrime s : ℕ} [NeZero q] [NeZero qPrime]
    (phi : WooleyPolynomialSystem k) (Psi : WooleyPolynomialSystem r)
    (gamma : WooleySourceSequence) :
    wooleySourceInsertedNormalizedRealAverage
        phi phi Psi q qPrime s 0 gamma gamma =
      (((q ^ k : ℕ) : ℝ)⁻¹) *
        ∑ alpha : Fin k → ZMod q,
          wooleySourcePolynomialMean s qPrime Psi
            (wooleySourceTwist gamma
              (fun n => wooleySourcePolynomialPhase phi alpha n)) := by
  unfold wooleySourceInsertedNormalizedRealAverage
  simp

theorem wooleySourcePolynomialMean_eq_zero_of_massSq_eq_zero
    {k q s : ℕ} [NeZero q]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (hs : 1 ≤ s) (hmass : wooleySourceMassSq gamma = 0) :
    wooleySourcePolynomialMean s q phi gamma = 0 := by
  have h2s : 2 * s ≠ 0 := (Nat.mul_pos (by norm_num) (by omega)).ne'
  have hnormalized : ∀ alpha : Fin k → ZMod q,
      wooleySourceNormalizedPolynomialSum phi gamma alpha = 0 := by
    intro alpha
    simp [wooleySourceNormalizedPolynomialSum, hmass]
  unfold wooleySourcePolynomialMean
  simp_rw [hnormalized]
  simp [zero_pow h2s]

/-- The tuple implication behind equation (4.12). -/
theorem wooleySection4_originalDisplacement_forces_inserted
    {k p c B h s : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hkhB : k * h ≤ B)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (xi : ℤ) :
    ∃ Psi : WooleyPolynomialSystem k,
      Psi.Spaced p (c + h) ∧
      ∀ (gamma : WooleySourceSequence)
        (omega : WooleySourceMixedTuple s 0 gamma gamma),
        wooleyEquation717OriginalDisplacement
            (wooleyAffinePolynomialSystem phi (p ^ h) xi)
            (wooleyAffinePolynomialSystem phi (p ^ h) xi)
            (p ^ B) s 0 gamma gamma omega = 0 →
          wooleyEquation717InsertedDisplacement
            Psi (p ^ (B - k * h)) s 0 gamma gamma omega = 0 := by
  obtain ⟨Psi, hPsi, htransfer⟩ :=
    wooleySection4_exists_dilated_system hpPrime hc hkhB phi hphi xi
  refine ⟨Psi, hPsi, ?_⟩
  intro gamma omega horiginal
  have hleft : wooleySourceTuplePolynomialDisplacement
      (wooleyAffinePolynomialSystem phi (p ^ h) xi)
      (p ^ B) s gamma omega.1 = 0 := by
    funext j
    have hj := congr_fun horiginal j
    simpa [wooleyEquation717OriginalDisplacement,
      wooleySourceTuplePolynomialDisplacement,
      wooleyTupleDisplacement] using hj
  have hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerTupleDisplacement s
        (fun x : ↑gamma.support =>
          (phi j).eval ((p : ℤ) ^ h * (x : ℤ) + xi)) omega.1 := by
    intro j
    have hz :
        (wooleyIntegerTupleDisplacement s
          (fun x : ↑gamma.support =>
            (phi j).eval ((p : ℤ) ^ h * (x : ℤ) + xi)) omega.1 :
            ZMod (p ^ B)) = 0 := by
      calc
        _ = wooleyTupleDisplacement (p ^ B) k s
            (fun x : ↑gamma.support => fun l =>
              (((phi l).eval ((p : ℤ) ^ h * (x : ℤ) + xi) : ℤ) :
                ZMod (p ^ B))) omega.1 j :=
          wooleyIntegerTupleDisplacement_cast (p ^ B) k s
            (fun x : ↑gamma.support => fun l =>
              (phi l).eval ((p : ℤ) ^ h * (x : ℤ) + xi)) omega.1 j
        _ = wooleySourceTuplePolynomialDisplacement
            (wooleyAffinePolynomialSystem phi (p ^ h) xi)
              (p ^ B) s gamma omega.1 j := by
          unfold wooleySourceTuplePolynomialDisplacement
            wooleyPolynomialValue wooleyTupleDisplacement
          simp_rw [wooleyAffinePolynomialSystem_eval]
          norm_num only [Nat.cast_pow]
        _ = 0 := congr_fun hleft j
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    norm_num only [Nat.cast_pow] at hz
    exact hz
  have hnew := htransfer (fun x : ↑gamma.support => (x : ℤ)) omega.1 hdiv
  funext i
  unfold wooleyEquation717InsertedDisplacement
    wooleySourceTuplePolynomialDisplacement wooleyPolynomialValue
  rw [← wooleyIntegerTupleDisplacement_cast]
  change (wooleyIntegerTupleDisplacement s
    (fun x : ↑gamma.support => (Psi i).eval (x : ℤ)) omega.1 :
      ZMod (p ^ (B - k * h))) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num only [Nat.cast_pow]
  exact hnew i

/-- Equation (4.12), in the exact finite Fourier-average model.  The right
side is the alpha average of the lower-modulus mean of the actual twisted
pullback coefficients `c_y(xi;alpha)` from (4.11). -/
theorem wooleySourcePolynomial_equation_4_12
    {k p c B h s : ℕ}
    [NeZero p] [NeZero (p ^ B)] [NeZero (p ^ (B - k * h))]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hkhB : k * h ≤ B)
    (hs : 1 ≤ s)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (xi : ℤ) :
    ∃ Psi : WooleyPolynomialSystem k,
      Psi.Spaced p (c + h) ∧
      ∀ gamma : WooleySourceSequence,
        wooleySourcePolynomialMean s (p ^ B)
            (wooleyAffinePolynomialSystem phi (p ^ h) xi) gamma =
          ((((p ^ B) ^ k : ℕ) : ℝ)⁻¹) *
            ∑ alpha : Fin k → ZMod (p ^ B),
              wooleySourcePolynomialMean s (p ^ (B - k * h)) Psi
                (wooleySourceTwist gamma
                  (fun n => wooleySourcePolynomialPhase
                    (wooleyAffinePolynomialSystem phi (p ^ h) xi)
                      alpha n)) := by
  obtain ⟨Psi, hPsi, hforced⟩ :=
    wooleySection4_originalDisplacement_forces_inserted
      hpPrime hc hkhB phi hphi xi
  refine ⟨Psi, hPsi, ?_⟩
  intro gamma
  let theta := wooleyAffinePolynomialSystem phi (p ^ h) xi
  have htuple := wooley_equation_7_17_tuple
    theta theta Psi (p ^ B) (p ^ (B - k * h)) s 0 gamma gamma
      (hforced gamma)
  have hrawComplex :
      wooleySourceRawMixedComplexAverage
          theta theta (p ^ B) s 0 gamma gamma =
        wooleySourceInsertedComplexAverage
          theta theta Psi (p ^ B) (p ^ (B - k * h)) s 0 gamma gamma := by
    rw [wooleySourceRawMixedComplexAverage_eq_tuple,
      wooleySourceInsertedComplexAverage_eq_tuple]
    exact htuple
  have hrawReal :
      wooleySourceRawMixedRealAverage
          theta theta (p ^ B) s 0 gamma gamma =
        wooleySourceInsertedRealAverage
          theta theta Psi (p ^ B) (p ^ (B - k * h)) s 0 gamma gamma := by
    apply Complex.ofReal_injective
    rw [← wooleySourceRawMixedComplexAverage_eq_ofReal,
      ← wooleySourceInsertedComplexAverage_eq_ofReal]
    exact hrawComplex
  by_cases hmass : wooleySourceMassSq gamma = 0
  · rw [wooleySourcePolynomialMean_eq_zero_of_massSq_eq_zero
      theta gamma hs hmass]
    have hsumsZero : ∀ alpha : Fin k → ZMod (p ^ B),
        wooleySourcePolynomialMean s (p ^ (B - k * h)) Psi
          (wooleySourceTwist gamma
            (fun n => wooleySourcePolynomialPhase theta alpha n)) = 0 := by
      intro alpha
      apply wooleySourcePolynomialMean_eq_zero_of_massSq_eq_zero Psi _ hs
      rw [wooleySourceMassSq_twist]
      · exact hmass
      · exact fun n => wooleySourcePolynomialPhase_norm theta alpha n
    have hsum : (∑ alpha : Fin k → ZMod (p ^ B),
        wooleySourcePolynomialMean s (p ^ (B - k * h)) Psi
          (wooleySourceTwist gamma
            (fun n => wooleySourcePolynomialPhase theta alpha n))) = 0 := by
      exact Finset.sum_eq_zero fun alpha halpha => hsumsZero alpha
    rw [hsum, mul_zero]
  · have hnormalized :
        wooleySourceNormalizedMixedRealAverage
            theta theta (p ^ B) s 0 gamma gamma =
          wooleySourceInsertedNormalizedRealAverage
            theta theta Psi (p ^ B) (p ^ (B - k * h)) s 0 gamma gamma := by
      rw [wooleySourceNormalizedMixedRealAverage_eq_mass_mul_raw
        theta theta (p ^ B) s 0 gamma gamma hmass hmass]
      rw [wooleySourceInsertedNormalizedRealAverage_eq_mass_mul_raw
        theta theta Psi (p ^ B) (p ^ (B - k * h)) s 0
          gamma gamma hmass hmass]
      rw [hrawReal]
    rw [wooleySourceNormalizedMixedRealAverage_self_zero] at hnormalized
    rw [wooleySourceInsertedNormalizedRealAverage_self_zero] at hnormalized
    simpa only [theta] using hnormalized

#print axioms wooleySourceNormalizedMixedRealAverage_self_zero
#print axioms wooleySourceInsertedNormalizedRealAverage_self_zero
#print axioms wooleySourcePolynomialMean_eq_zero_of_massSq_eq_zero
#print axioms wooleySection4_originalDisplacement_forces_inserted
#print axioms wooleySourcePolynomial_equation_4_12

end

end GafniTao
