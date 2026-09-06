import GafniTao.HeathBrownDyadicSourceOutput

/-!
# Global zero-energy source alternative

This is the first theorem in the Heath--Brown chain whose left-hand side is
the genuine multiplicity-weighted four-zero count.  It consumes the actual
logarithmic shell cover and then exhaustively keeps either the bounded-shell
estimate or the four-coordinate detector output.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The genuine zero energy is reduced to one selected four-shell problem,
with no loss of the small-shell alternative. -/
theorem exists_heathBrownGlobalSourceAlternative
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1) (hdelta2Sigma : delta2 < sigma)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ R0 : Real, 16 ≤ R0 ∧ ∀ T : Real,
      max (Real.exp 2) 8 ≤ 2 * (Nat.ceil T : Real) → 1 ≤ T →
      ∃ coverLabel : Fin 4 → Fin (dyadicZeroShellCount T),
        zeroAdditiveEnergyCount sigma T ≤
          (dyadicZeroShellCount T) ^ 4 *
            weightedMixedAdditiveEnergyOn
              (dyadicZeroShell sigma T (coverLabel 0))
              (dyadicZeroShell sigma T (coverLabel 1))
              (dyadicZeroShell sigma T (coverLabel 2))
              (dyadicZeroShell sigma T (coverLabel 3))
              zeroMultiplicity 1 ∧
        ((weightedMixedAdditiveEnergyOn
              (dyadicZeroShell sigma T (coverLabel 0))
              (dyadicZeroShell sigma T (coverLabel 1))
              (dyadicZeroShell sigma T (coverLabel 2))
              (dyadicZeroShell sigma T (coverLabel 3))
              zeroMultiplicity 1 : Real) ≤
            (zeroCount sigma R0 : Real) *
              (zeroCount sigma (2 * (Nat.ceil T : Real)) : Real) ^ 2 *
              (3 * globalLocalZeroLogConstant *
                Real.log (2 * (Nat.ceil T : Real))) ∨
          Nonempty (HeathBrownDyadicSourceOutput
            sigma T delta delta1 delta2 eta epsilon coverLabel)) := by
  obtain ⟨R0, hR0, hSource⟩ := exists_heathBrownDyadicSourceCutoff
    hsigma hsigmaUpper hdelta hdeltaUpper hdelta1 hdelta2 hdeltaOrder
    hdelta1Upper hdelta2Sigma hCube heta hepsilon
  refine ⟨R0, hR0, ?_⟩
  intro T hTCeil hT
  obtain ⟨coverLabel, hCover⟩ := exists_zero_energy_dyadic_shells sigma T
  refine ⟨coverLabel, hCover, ?_⟩
  rcases hSource T coverLabel with hBounded | hOutput
  · left
    exact weightedMixed_dyadicZeroShells_le_of_bounded
      (by linarith) hTCeil hT coverLabel hBounded
  · exact Or.inr hOutput

#print axioms exists_heathBrownGlobalSourceAlternative

end

end GafniTao
