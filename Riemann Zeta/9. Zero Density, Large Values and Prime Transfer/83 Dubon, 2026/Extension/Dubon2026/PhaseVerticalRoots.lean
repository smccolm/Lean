import Dubon2026.AnalyticVerticalPolynomial

/-! # Exact real-polynomial multiplicities for the actual torus-twisted zeros -/

namespace Dubon2026

open Complex Polynomial

noncomputable section

theorem phaseVerticalRealPolynomial_ne_zero (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u T σ : ℝ) (x : PrimeCoordinate N → ℝ) :
    phaseVerticalRealPolynomial a N hN ha l u T σ x ≠ 0 := by
  apply realNormPolynomial_ne_zero
  apply verticalLinePolynomial_ne_zero
  exact (rectangleZeroPolynomial_monic _ _ _ _ _ _ _).ne_zero

theorem phaseVerticalRealPolynomial_rootMultiplicity (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u T σ : ℝ) (x : PrimeCoordinate N → ℝ) (t : ℝ) :
    (phaseVerticalRealPolynomial a N hN ha l u T σ x).rootMultiplicity t =
      2 * (if (σ : ℂ) + I * t ∈ zerosInOpenRectangleFinset
        (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N hN
        (by rwa [twistedCoefficients_one]) l u T then
          zeroMultiplicity (twistedCoefficients a N (fun p => (x p : UnitAddCircle)))
            N ((σ : ℂ) + I * t) else 0) := by
  classical
  unfold phaseVerticalRealPolynomial complexPhaseZeroPolynomial
  rw [vertical_realNorm_rootMultiplicity
    (rectangleZeroPolynomial_monic _ _ _ _ _ _ _).ne_zero]
  rw [rectangleZeroPolynomial_rootMultiplicity]
  have hc : complexPhaseCoefficients a N (complexifyPhase x) =
      twistedCoefficients a N (fun p => (x p : UnitAddCircle)) :=
    complexPhaseCoefficients_real a N x
  have hm := congrArg (fun c : ℕ → ℂ => zeroMultiplicity c N ((σ : ℂ) + I * t)) hc
  have hs : ((σ : ℂ) + I * t ∈ zerosInOpenRectangleFinset
      (complexPhaseCoefficients a N (complexifyPhase x)) N hN
      (by rwa [complexPhaseCoefficients_one]) l u T) ↔
    ((σ : ℂ) + I * t ∈ zerosInOpenRectangleFinset
      (twistedCoefficients a N (fun p => (x p : UnitAddCircle))) N hN
      (by rwa [twistedCoefficients_one]) l u T) := by
    simp only [mem_zerosInOpenRectangleFinset, hc]
  dsimp only at hm
  simp only [hm, hs]


theorem phaseVerticalRealPolynomial_rootMultiplicity_interior (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T σ t : ℝ}
    (hl : l < σ) (hu : σ < u) (ht : |t| < T) (x : PrimeCoordinate N → ℝ) :
    (phaseVerticalRealPolynomial a N hN ha l u T σ x).rootMultiplicity t =
      2 * zeroMultiplicity (twistedCoefficients a N (fun p => (x p : UnitAddCircle)))
        N ((σ : ℂ) + I * t) := by
  classical
  rw [phaseVerticalRealPolynomial_rootMultiplicity]
  have hre : ((σ : ℂ) + I * t).re = σ := by simp
  have him : ((σ : ℂ) + I * t).im = t := by simp
  by_cases hz : dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle)))
      N ((σ : ℂ) + I * t) = 0
  · rw [if_pos ((mem_zerosInOpenRectangleFinset _ _ _ _ _ _ _ _).mpr
      ⟨by simpa only [hre] using hl, by simpa only [hre] using hu,
        by simpa only [him] using ht, hz⟩)]
  · have hm : zeroMultiplicity (twistedCoefficients a N (fun p => (x p : UnitAddCircle)))
        N ((σ : ℂ) + I * t) = 0 := by
      exact Nat.eq_zero_of_not_pos (fun h => hz ((zeroMultiplicity_pos_iff (a := twistedCoefficients a N
          (fun p => (x p : UnitAddCircle))) hN
        (by rwa [twistedCoefficients_one]) _).mp h))
    simp only [hm, ite_self]

theorem phaseVerticalRealPolynomial_eval_zero_iff (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {l u T σ t : ℝ}
    (hl : l < σ) (hu : σ < u) (ht : |t| < T) (x : PrimeCoordinate N → ℝ) :
    (phaseVerticalRealPolynomial a N hN ha l u T σ x).eval t = 0 ↔
      dirichletSum (twistedCoefficients a N (fun p => (x p : UnitAddCircle)))
        N ((σ : ℂ) + I * t) = 0 := by
  change (phaseVerticalRealPolynomial a N hN ha l u T σ x).IsRoot t ↔ _
  rw [← Polynomial.rootMultiplicity_pos (phaseVerticalRealPolynomial_ne_zero a N hN ha l u T σ x),
    phaseVerticalRealPolynomial_rootMultiplicity_interior a N hN ha hl hu ht x]
  rw [mul_pos_iff_of_pos_left (by norm_num : 0 < (2 : ℕ))]
  exact zeroMultiplicity_pos_iff (a := twistedCoefficients a N
    (fun p => (x p : UnitAddCircle))) hN (by rwa [twistedCoefficients_one]) _

end

end Dubon2026
