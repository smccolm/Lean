import GafniTao.ExceptionalExponent

/-!
# The ordinary second-moment envelope

The refined fourth-moment theorem must recover the ordinary Gafni--Tao
Theorem 1.2 by forgetting the fourth-moment alternative.  This file defines
the exact ordinary infimum--supremum expression and proves that comparison at
the level of `EReal`, retaining the source epsilon infimum.
-/

namespace GafniTao

/-- The fixed-epsilon supremum in the ordinary second-moment theorem. -/
noncomputable def ordinaryFixedEpsilonExponent (theta eps : ℝ) : EReal :=
  sSup {x | ∃ sigma : ℝ, RefinedSigmaAdmissible theta eps sigma ∧
    x = ordinaryMomentExponent theta sigma}

/-- The literal right side of Gafni--Tao Theorem 1.2. -/
noncomputable def ordinaryExceptionalUpperExponent (theta : ℝ) : EReal :=
  sInf {x | ∃ eps : ℝ, 0 < eps ∧
    x = ordinaryFixedEpsilonExponent theta eps}

/-- Strict-upper-half fixed-epsilon supremum in the alternate display for
the ordinary second-moment theorem. -/
noncomputable def upperHalfOrdinaryFixedEpsilonExponent
    (theta eps : ℝ) : EReal :=
  sSup {x | ∃ sigma : ℝ,
    UpperHalfRefinedSigmaAdmissible theta eps sigma ∧
    x = ordinaryMomentExponent theta sigma}

/-- The epsilon infimum in the source's alternate upper-half ordinary
formula. -/
noncomputable def upperHalfOrdinaryExceptionalUpperExponent
    (theta : ℝ) : EReal :=
  sInf {x | ∃ eps : ℝ, 0 < eps ∧
    x = upperHalfOrdinaryFixedEpsilonExponent theta eps}

theorem ordinaryCandidate_le_fixedEpsilon
    {theta eps sigma : ℝ}
    (h : RefinedSigmaAdmissible theta eps sigma) :
    ordinaryMomentExponent theta sigma ≤
      ordinaryFixedEpsilonExponent theta eps := by
  apply le_sSup
  exact ⟨sigma, h, rfl⟩

theorem upperHalfOrdinaryCandidate_le_fixedEpsilon
    {theta eps sigma : ℝ}
    (h : UpperHalfRefinedSigmaAdmissible theta eps sigma) :
    ordinaryMomentExponent theta sigma ≤
      upperHalfOrdinaryFixedEpsilonExponent theta eps := by
  apply le_sSup
  exact ⟨sigma, h, rfl⟩

theorem upperHalfRefinedExceptionalUpperExponent_le_fixedEpsilon
    {theta eps : ℝ} (heps : 0 < eps) :
    upperHalfRefinedExceptionalUpperExponent theta ≤
      upperHalfRefinedFixedEpsilonExponent theta eps := by
  apply sInf_le
  exact ⟨eps, heps, rfl⟩

/-- Pointwise, the minimum of the second- and fourth-moment exponents is no
larger than the second-moment exponent. -/
theorem refinedFixedEpsilonExponent_le_ordinary
    (theta eps : ℝ) :
    refinedFixedEpsilonExponent theta eps ≤
      ordinaryFixedEpsilonExponent theta eps := by
  unfold refinedFixedEpsilonExponent
  apply sSup_le
  rintro x ⟨sigma, hsigma, rfl⟩
  exact (min_le_left _ _).trans (ordinaryCandidate_le_fixedEpsilon hsigma)

theorem refinedExceptionalUpperExponent_le_ordinary (theta : ℝ) :
    refinedExceptionalUpperExponent theta ≤
      ordinaryExceptionalUpperExponent theta := by
  unfold ordinaryExceptionalUpperExponent
  apply le_sInf
  rintro x ⟨eps, heps, rfl⟩
  exact (refinedExceptionalUpperExponent_le_fixedEpsilon heps).trans
    (refinedFixedEpsilonExponent_le_ordinary theta eps)

theorem upperHalfRefinedFixedEpsilonExponent_le_ordinary
    (theta eps : ℝ) :
    upperHalfRefinedFixedEpsilonExponent theta eps ≤
      upperHalfOrdinaryFixedEpsilonExponent theta eps := by
  unfold upperHalfRefinedFixedEpsilonExponent
  apply sSup_le
  rintro x ⟨sigma, hsigma, rfl⟩
  exact (min_le_left _ _).trans
    (upperHalfOrdinaryCandidate_le_fixedEpsilon hsigma)

theorem upperHalfRefinedExceptionalUpperExponent_le_ordinary
    (theta : ℝ) :
    upperHalfRefinedExceptionalUpperExponent theta ≤
      upperHalfOrdinaryExceptionalUpperExponent theta := by
  unfold upperHalfOrdinaryExceptionalUpperExponent
  apply le_sInf
  rintro x ⟨eps, heps, rfl⟩
  exact (upperHalfRefinedExceptionalUpperExponent_le_fixedEpsilon heps).trans
    (upperHalfRefinedFixedEpsilonExponent_le_ordinary theta eps)

/-- Conditional `max (1-theta, ...)` form of the ordinary second-moment
Gafni--Tao Theorem 1.2, obtained as an exact corollary of the refined
consumer. -/
theorem gafniTaoTheorem12_max_conditional
    (cutoff : RiemannZeta.GuthMaynard.GMSmoothCutoff)
    (hFormula : SharpTruncatedExplicitFormulaBound)
    {C B T₀ c T₁ : ℝ}
    (hDensity : NearOneLogDensityBound C B T₀)
    (hZeroFree : VinogradovKorobovCountVanishing c T₁)
    (hC : 0 < C) (hc : 0 < c)
    {theta : ℝ} (hthetaLower : 0 < theta) (hthetaUpper : theta < 1) :
    exceptionalExponent theta ≤
      max (((1 - theta : ℝ) : EReal))
        (upperHalfOrdinaryExceptionalUpperExponent theta) := by
  exact (gafniTaoTheorem13_conditional cutoff hFormula hDensity
    hZeroFree hC hc hthetaLower hthetaUpper).trans
      ((refinedExceptionalUpperExponent_le_upperHalf_max hthetaUpper).trans
        (max_le_max_left _
          (upperHalfRefinedExceptionalUpperExponent_le_ordinary theta)))

end GafniTao
