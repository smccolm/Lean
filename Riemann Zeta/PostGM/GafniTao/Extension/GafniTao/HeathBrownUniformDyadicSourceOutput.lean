import GafniTao.DyadicZeroShellBounded
import GafniTao.ClassicalBinaryHeathBrownSourceDetector
import GafniTao.HeathBrownUniformMixedSourceOutput

/-!
# Uniform source entry for four dyadic zero shells

This is the logarithmic shell-cover entry with the repaired common
Heath--Brown constants carried through all four coordinates.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

structure HeathBrownUniformDyadicSourceOutput
    (sigma T delta delta1 delta2 eta epsilon C0 C2 C4 : Real)
    (coverLabel : Fin 4 → Fin (dyadicZeroShellCount T)) where
  noncentral : ∀ i : Fin 4, (coverLabel i).val ≠ 0
  d0 : ClassicalBinaryShellDetectorData sigma
    (dyadicZeroShellInnerHeight (coverLabel 0)) delta
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 0) ^ delta1))
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 0) ^ (delta2 / 2)))
    (Nat.floor (sharpZetaCutoff (dyadicZeroShellInnerHeight (coverLabel 0))))
    (dyadicZeroShellInnerHeight (coverLabel 0) ^ (-delta2))
  d1 : ClassicalBinaryShellDetectorData sigma
    (dyadicZeroShellInnerHeight (coverLabel 1)) delta
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 1) ^ delta1))
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 1) ^ (delta2 / 2)))
    (Nat.floor (sharpZetaCutoff (dyadicZeroShellInnerHeight (coverLabel 1))))
    (dyadicZeroShellInnerHeight (coverLabel 1) ^ (-delta2))
  d2 : ClassicalBinaryShellDetectorData sigma
    (dyadicZeroShellInnerHeight (coverLabel 2)) delta
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 2) ^ delta1))
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 2) ^ (delta2 / 2)))
    (Nat.floor (sharpZetaCutoff (dyadicZeroShellInnerHeight (coverLabel 2))))
    (dyadicZeroShellInnerHeight (coverLabel 2) ^ (-delta2))
  d3 : ClassicalBinaryShellDetectorData sigma
    (dyadicZeroShellInnerHeight (coverLabel 3)) delta
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 3) ^ delta1))
    (Nat.floor (dyadicZeroShellInnerHeight (coverLabel 3) ^ (delta2 / 2)))
    (Nat.floor (sharpZetaCutoff (dyadicZeroShellInnerHeight (coverLabel 3))))
    (dyadicZeroShellInnerHeight (coverLabel 3) ^ (-delta2))
  mixed : HeathBrownUniformMixedSourceOutput sigma delta delta1 delta2
    eta epsilon C0 C2 C4
    (dyadicZeroShellInnerHeight (coverLabel 0))
    (dyadicZeroShellInnerHeight (coverLabel 1))
    (dyadicZeroShellInnerHeight (coverLabel 2))
    (dyadicZeroShellInnerHeight (coverLabel 3)) d0 d1 d2 d3

theorem HeathBrownUniformDyadicSourceOutput.shell_eq
    {sigma T delta delta1 delta2 eta epsilon C0 C2 C4 : Real}
    {coverLabel : Fin 4 → Fin (dyadicZeroShellCount T)}
    (out : HeathBrownUniformDyadicSourceOutput sigma T delta delta1 delta2
      eta epsilon C0 C2 C4 coverLabel) (i : Fin 4) :
    dyadicZeroShell sigma T (coverLabel i) =
      absoluteDyadicZeroSlab sigma
        (dyadicZeroShellInnerHeight (coverLabel i)) :=
  dyadicZeroShell_eq_absolute_of_ne_zero (out.noncentral i)

/-- Exhaustive source entry for any four shells, with common epsilon-only
finite-relation constants. -/
theorem exists_heathBrownUniformDyadicSourceCutoff
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
      ∀ (T : Real) (coverLabel : Fin 4 → Fin (dyadicZeroShellCount T)),
        (∃ i : Fin 4, dyadicZeroShellOuterHeight (coverLabel i) ≤ R0) ∨
        Nonempty (HeathBrownUniformDyadicSourceOutput sigma T delta delta1
          delta2 eta epsilon C0 C2 C4 coverLabel) := by
  obtain ⟨Udet, hUdet, hDetector⟩ :=
    exists_heathBrown_source_classicalBinaryShellDetectorData
      (sigma := sigma) (shiftDelta := delta)
      (delta1 := delta1) (delta2 := delta2)
      hsigma hsigmaUpper hdelta hdelta1 hdelta2 hdeltaOrder
      hdelta1Upper hdelta2Sigma
  obtain ⟨C0, C2, C4, B0, Uout, hC0, hC2, hC4, hB0,
      hUout, hOutput⟩ :=
    eventually_heathBrownUniformMixedSourceOutput
      (sigma := sigma) (delta := delta) (delta1 := delta1)
      (delta2 := delta2) (eta := eta) (epsilon := epsilon)
      (by linarith) hdeltaUpper hdelta1 hdelta2 hdeltaOrder
      hdelta1Upper hCube heta hepsilon
  let Ubase := max Udet Uout
  let R0 := 2 * Ubase
  have hUbase : 8 ≤ Ubase := hUdet.trans (le_max_left _ _)
  refine ⟨C0, C2, C4, B0, R0, hC0, hC2, hC4, hB0,
    by dsimp only [R0]; linarith, ?_⟩
  intro T coverLabel
  by_cases hBounded : ∃ i : Fin 4,
      dyadicZeroShellOuterHeight (coverLabel i) ≤ R0
  · exact Or.inl hBounded
  · right
    have hOuter (i : Fin 4) :
        R0 < dyadicZeroShellOuterHeight (coverLabel i) :=
      lt_of_not_ge (fun hi => hBounded ⟨i, hi⟩)
    have hNoncentral (i : Fin 4) : (coverLabel i).val ≠ 0 := by
      intro hi
      have hOuterOne : dyadicZeroShellOuterHeight (coverLabel i) = 1 := by
        simp only [dyadicZeroShellOuterHeight, hi, if_true]
      have hR0 : 1 ≤ R0 := by
        dsimp only [R0, Ubase]
        linarith
      linarith [hOuter i]
    have hHeight (i : Fin 4) :
        Ubase ≤ dyadicZeroShellInnerHeight (coverLabel i) := by
      apply le_dyadicZeroShellInnerHeight_of_two_mul_lt_outer
        (hNoncentral i)
      simpa only [R0] using hOuter i
    have hDetHeight (i : Fin 4) :
        Udet ≤ dyadicZeroShellInnerHeight (coverLabel i) :=
      (le_max_left _ _).trans (hHeight i)
    obtain ⟨d0⟩ := hDetector _ (hDetHeight 0)
    obtain ⟨d1⟩ := hDetector _ (hDetHeight 1)
    obtain ⟨d2⟩ := hDetector _ (hDetHeight 2)
    obtain ⟨d3⟩ := hDetector _ (hDetHeight 3)
    have hOutHeight (i : Fin 4) :
        Uout ≤ dyadicZeroShellInnerHeight (coverLabel i) :=
      (le_max_right _ _).trans (hHeight i)
    obtain ⟨mixed⟩ := hOutput
      (dyadicZeroShellInnerHeight (coverLabel 0))
      (dyadicZeroShellInnerHeight (coverLabel 1))
      (dyadicZeroShellInnerHeight (coverLabel 2))
      (dyadicZeroShellInnerHeight (coverLabel 3))
      (hOutHeight 0) (hOutHeight 1) (hOutHeight 2) (hOutHeight 3)
      d0 d1 d2 d3
    exact ⟨⟨hNoncentral, d0, d1, d2, d3, mixed⟩⟩

#print axioms HeathBrownUniformDyadicSourceOutput.shell_eq
#print axioms exists_heathBrownUniformDyadicSourceCutoff

end

end GafniTao
