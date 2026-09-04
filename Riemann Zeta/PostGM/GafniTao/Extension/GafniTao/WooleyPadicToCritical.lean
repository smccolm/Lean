import GafniTao.WooleyPadicScale
import GafniTao.WooleyCriticalBase

/-!
# From Wooley's p-adic concentration to the critical mean value estimate

This is the quantitative passage carried out in Wooley, Section 12.  A
modulus is chosen just above the physical box, so the modular equations have
no wraparound.  The source loss `p^(B * delta)` is then absorbed into the
requested `Q^epsilon` loss, with every fixed factor retained in the constant.
-/

namespace GafniTao

noncomputable section

theorem fordLambda34_critical (k : ℕ) (epsilon : ℝ) :
    fordLambda34 (fordVinogradovKappa k) k epsilon =
      (fordVinogradovKappa k : ℝ) + epsilon := by
  unfold fordLambda34
  rw [fordVinogradovKappa_cast]
  ring

/-- Wooley's modular concentration statement implies the coefficient-one
critical endpoint of the Vinogradov mean value theorem. -/
theorem vinogradovCriticalEndpoint_of_wooleyPadic
    (hconc : WooleyMonomialPadicConcentration) :
    VinogradovCriticalEndpointTheorem := by
  intro k epsilon hk hepsilon
  by_cases hkOne : k = 1
  · subst k
    exact vinogradovCriticalEndpoint_degree_one hepsilon
  obtain ⟨p, hp, hkp⟩ := exists_prime_strictly_above k
  let s := fordVinogradovKappa k
  let delta := epsilon / (k : ℝ)
  have hkPos : 0 < k := by omega
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hkPos
  have hdelta : 0 < delta := div_pos hepsilon hkReal
  obtain ⟨C, hC, B0, hconcentration⟩ :=
    hconc.specialize hp hkp hdelta
  let D : ℕ := p ^ (B0 + 1) * s
  have hsPos : 0 < s := by
    exact fordVinogradovKappa_pos hk
  have hDPos : 0 < D := by
    dsimp [D]
    exact Nat.mul_pos (pow_pos hp.pos (B0 + 1)) hsPos
  refine ⟨C * (D : ℝ) ^ epsilon, mul_pos hC (Real.rpow_pos_of_pos
    (by exact_mod_cast hDPos) _), ?_⟩
  intro Q hQ
  obtain ⟨h, hB, hQph, hnowrap, hphUpper⟩ :=
    exists_wooleyPadicScale hk hp.two_le hQ
  have hmodular := hconcentration Q h hQ hB hQph
  rw [wooleyPadicCount_eq_fordVinogradovMomentNat hQ hnowrap] at hmodular
  have hQPosNat : 0 < Q := by omega
  have hQPos : (0 : ℝ) < Q := by exact_mod_cast hQPosNat
  have hDPosReal : (0 : ℝ) < D := by exact_mod_cast hDPos
  have hphUpperNat : p ^ h ≤ D * Q := by
    simpa [D, s, Nat.mul_assoc] using hphUpper
  have hpowUpperNat : p ^ (k * h) ≤ (D * Q) ^ k := by
    rw [show p ^ (k * h) = (p ^ h) ^ k by rw [← pow_mul, Nat.mul_comm]]
    exact Nat.pow_le_pow_left hphUpperNat k
  have hpowUpperReal :
      ((p ^ (k * h) : ℕ) : ℝ) ≤ ((D * Q : ℕ) : ℝ) ^ k := by
    exact_mod_cast hpowUpperNat
  have hdeltaScale : (k : ℝ) * delta = epsilon := by
    dsimp [delta]
    field_simp
  have hloss :
      ((p ^ (k * h) : ℕ) : ℝ) ^ delta ≤
        (D : ℝ) ^ epsilon * (Q : ℝ) ^ epsilon := by
    calc
      ((p ^ (k * h) : ℕ) : ℝ) ^ delta ≤
          (((D * Q : ℕ) : ℝ) ^ k) ^ delta :=
        Real.rpow_le_rpow (by positivity) hpowUpperReal hdelta.le
      _ = (((D : ℝ) * (Q : ℝ)) ^ (k : ℝ)) ^ delta := by
        norm_num [Real.rpow_natCast]
      _ = ((D : ℝ) * (Q : ℝ)) ^ ((k : ℝ) * delta) := by
        rw [Real.rpow_mul (mul_pos hDPosReal hQPos).le]
      _ = ((D : ℝ) * (Q : ℝ)) ^ epsilon := by rw [hdeltaScale]
      _ = (D : ℝ) ^ epsilon * (Q : ℝ) ^ epsilon := by
        rw [Real.mul_rpow hDPosReal.le hQPos.le]
  have hcriticalExponent :
      fordLambda34 (fordVinogradovKappa k) k epsilon =
        (s : ℝ) + epsilon := by
    simpa [s] using fordLambda34_critical k epsilon
  have hmodular' :
      (fordVinogradovMomentNat (fordVinogradovKappa k) k Q : ℝ) ≤
        C * ((p ^ (k * h) : ℕ) : ℝ) ^ delta *
          (Q : ℝ) ^ fordVinogradovKappa k := by
    simpa only [Nat.cast_pow] using hmodular
  calc
    (fordVinogradovMomentNat (fordVinogradovKappa k) k Q : ℝ) ≤
        C * ((p ^ (k * h) : ℕ) : ℝ) ^ delta *
          (Q : ℝ) ^ fordVinogradovKappa k := hmodular'
    _ ≤ C * ((D : ℝ) ^ epsilon * (Q : ℝ) ^ epsilon) *
          (Q : ℝ) ^ fordVinogradovKappa k := by
      gcongr
    _ = (C * (D : ℝ) ^ epsilon) *
          (Q : ℝ) ^ ((s : ℝ) + epsilon) := by
      rw [Real.rpow_add hQPos, Real.rpow_natCast]
      dsimp [s]
      ring
    _ = (C * (D : ℝ) ^ epsilon) *
          (Q : ℝ) ^ fordLambda34 (fordVinogradovKappa k) k epsilon := by
      rw [hcriticalExponent]

theorem heathBrownVMVTMainConjecture_of_wooleyPadic
    (hconc : WooleyMonomialPadicConcentration) :
    HeathBrownVMVTMainConjecture :=
  heathBrownVMVTMainConjecture_of_critical
    (vinogradovCriticalEndpoint_of_wooleyPadic hconc)

#print axioms fordLambda34_critical
#print axioms vinogradovCriticalEndpoint_of_wooleyPadic
#print axioms heathBrownVMVTMainConjecture_of_wooleyPadic

end

end GafniTao
