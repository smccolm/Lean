import GafniTao.HeathBrownUniformDyadicSourceOutput

/-!
# Uniform global zero-energy source alternative

The genuine multiplicity-weighted four-zero count is reduced either to the
bounded-shell estimate or to four detector colours sharing epsilon-only
finite-relation constants.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem exists_heathBrownUniformGlobalSourceAlternative
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaUpper : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1) (hdelta2Sigma : delta2 < sigma)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ C0 C2 C4 B0 R0 : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧ 16 ≤ R0 ∧
      ∀ T : Real,
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
            Nonempty (HeathBrownUniformDyadicSourceOutput sigma T delta
              delta1 delta2 eta epsilon C0 C2 C4 coverLabel)) := by
  obtain ⟨C0, C2, C4, B0, R0, hC0, hC2, hC4, hB0, hR0, hSource⟩ :=
    exists_heathBrownUniformDyadicSourceCutoff hsigma hsigmaUpper hdelta
      hdeltaUpper hdelta1 hdelta2 hdeltaOrder hdelta1Upper hdelta2Sigma
      hCube heta hepsilon
  refine ⟨C0, C2, C4, B0, R0, hC0, hC2, hC4, hB0, hR0, ?_⟩
  intro T hTCeil hT
  obtain ⟨coverLabel, hCover⟩ := exists_zero_energy_dyadic_shells sigma T
  refine ⟨coverLabel, hCover, ?_⟩
  rcases hSource T coverLabel with hBounded | hOutput
  · left
    exact weightedMixed_dyadicZeroShells_le_of_bounded
      (by linarith) hTCeil hT coverLabel hBounded
  · exact Or.inr hOutput

#print axioms exists_heathBrownUniformGlobalSourceAlternative

end

end GafniTao
