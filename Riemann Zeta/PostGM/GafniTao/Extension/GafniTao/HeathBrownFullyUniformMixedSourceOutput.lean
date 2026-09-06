import GafniTao.MixedClassicalBinaryShellExtraction
import GafniTao.ClassicalBinaryFullyUniformSourceAlternative
import GafniTao.HeathBrownUniformMixedSourceOutput

/-!
# Four-coordinate fully uniform source output

The four dyadic zero shells select detector colours independently while all
analytic constants are shared.  Conversion lemmas retain compatibility with
the earlier source-output API without losing the stronger quantifier order.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Forget only the visible equalities of the fully uniform packet, retaining
the same energy and cardinality witnesses. -/
def HeathBrownFullyUniformSourceColorOutput.toUniform
    {sigma U delta delta1 delta2 eta epsilon K C Cp Cmv C0 C2 C4 : Real}
    {d : ClassicalBinaryShellDetectorData sigma U delta
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))}
    {label : Fin (d.kI * 2 + d.kII * 2) × Fin 2}
    (out : HeathBrownFullyUniformSourceColorOutput sigma U delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4 d label)
    (hK : 0 < K) (hC : 0 < C) :
    HeathBrownUniformSourceColorOutput sigma U delta delta1 delta2 eta
      epsilon C0 C2 C4 d label where
  K := K
  C := C
  hK := hK
  hC := hC
  hN := out.hN
  hCoeff := out.hCoeff
  hLarge := out.hLarge
  branch := by
    rcases out.branch with hTypeI | hTypeII
    · exact Or.inl hTypeI
    · right
      obtain ⟨_r, _hlabel, ⟨full⟩⟩ := hTypeII
      exact ⟨⟨full.energy⟩, ⟨full.card⟩, ⟨full.next⟩⟩

/-- Four independently selected source colours carrying fully uniform
Heath--Brown outputs. -/
structure HeathBrownFullyUniformMixedSourceOutput
    (sigma delta delta1 delta2 eta epsilon : Real)
    (K C Cp Cmv C0 C2 C4 : Real)
    (U0 U1 U2 U3 : Real)
    (d0 : ClassicalBinaryShellDetectorData sigma U0 delta
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2)))
    (d1 : ClassicalBinaryShellDetectorData sigma U1 delta
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2)))
    (d2 : ClassicalBinaryShellDetectorData sigma U2 delta
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2)))
    (d3 : ClassicalBinaryShellDetectorData sigma U3 delta
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))) where
  label0 : Fin (d0.kI * 2 + d0.kII * 2) × Fin 2
  label1 : Fin (d1.kI * 2 + d1.kII * 2) × Fin 2
  label2 : Fin (d2.kI * 2 + d2.kII * 2) × Fin 2
  label3 : Fin (d3.kI * 2 + d3.kII * 2) × Fin 2
  separated0 : IsSeparated 1 (classicalBinaryColorFamily d0 label0)
  separated1 : IsSeparated 1 (classicalBinaryColorFamily d1 label1)
  separated2 : IsSeparated 1 (classicalBinaryColorFamily d2 label2)
  separated3 : IsSeparated 1 (classicalBinaryColorFamily d3 label3)
  energy_le :
    weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 ≤
      (((d0.kI * 2 + d0.kII * 2) * 2) *
        ((d1.kI * 2 + d1.kII * 2) * 2) *
        ((d2.kI * 2 + d2.kII * 2) * 2) *
        ((d3.kI * 2 + d3.kII * 2) * 2)) *
        (((2 * ⌈U0 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U0) *
          ((2 * ⌈U1 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U1) *
          ((2 * ⌈U2 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U2) *
          ((2 * ⌈U3 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U3)) *
        MixedApproxAddEnergy
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
          (classicalBinaryColorFamily d0 label0)
          (classicalBinaryColorFamily d1 label1)
          (classicalBinaryColorFamily d2 label2)
          (classicalBinaryColorFamily d3 label3)
  output0 : (classicalBinaryColorFamily d0 label0).Nonempty →
    Nonempty (HeathBrownFullyUniformSourceColorOutput sigma U0 delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4 d0 label0)
  output1 : (classicalBinaryColorFamily d1 label1).Nonempty →
    Nonempty (HeathBrownFullyUniformSourceColorOutput sigma U1 delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4 d1 label1)
  output2 : (classicalBinaryColorFamily d2 label2).Nonempty →
    Nonempty (HeathBrownFullyUniformSourceColorOutput sigma U2 delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4 d2 label2)
  output3 : (classicalBinaryColorFamily d3 label3).Nonempty →
    Nonempty (HeathBrownFullyUniformSourceColorOutput sigma U3 delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4 d3 label3)

/-- Forget the common factorization equalities while preserving the exact
four selected colours and their energy extraction. -/
def HeathBrownFullyUniformMixedSourceOutput.toUniform
    {sigma delta delta1 delta2 eta epsilon K C Cp Cmv C0 C2 C4 : Real}
    {U0 U1 U2 U3 : Real}
    {d0 : ClassicalBinaryShellDetectorData sigma U0 delta
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2))}
    {d1 : ClassicalBinaryShellDetectorData sigma U1 delta
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2))}
    {d2 : ClassicalBinaryShellDetectorData sigma U2 delta
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2))}
    {d3 : ClassicalBinaryShellDetectorData sigma U3 delta
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))}
    (out : HeathBrownFullyUniformMixedSourceOutput sigma delta delta1 delta2
      eta epsilon K C Cp Cmv C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3)
    (hK : 0 < K) (hC : 0 < C) :
    HeathBrownUniformMixedSourceOutput sigma delta delta1 delta2 eta epsilon
      C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3 where
  label0 := out.label0
  label1 := out.label1
  label2 := out.label2
  label3 := out.label3
  separated0 := out.separated0
  separated1 := out.separated1
  separated2 := out.separated2
  separated3 := out.separated3
  energy_le := out.energy_le
  output0 hW := by
    obtain ⟨o⟩ := out.output0 hW
    exact ⟨o.toUniform hK hC⟩
  output1 hW := by
    obtain ⟨o⟩ := out.output1 hW
    exact ⟨o.toUniform hK hC⟩
  output2 hW := by
    obtain ⟨o⟩ := out.output2 hW
    exact ⟨o.toUniform hK hC⟩
  output3 hW := by
    obtain ⟨o⟩ := out.output3 hW
    exact ⟨o.toUniform hK hC⟩

/-- Uniform four-coordinate source output with every analytic constant common
to all heights and colours. -/
theorem eventually_heathBrownFullyUniformMixedSourceOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 ≤ sigma) (hdelta : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ K C Cp Cmv C0 C2 C4 B0 Ubase : Real,
      0 < K ∧ 0 < C ∧ 1 ≤ Cp ∧ 0 < Cmv ∧
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧ 8 ≤ Ubase ∧
      ∀ U0 U1 U2 U3 : Real,
        Ubase ≤ U0 → Ubase ≤ U1 → Ubase ≤ U2 → Ubase ≤ U3 →
        ∀ (d0 : ClassicalBinaryShellDetectorData sigma U0 delta
          (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2)))
          (d1 : ClassicalBinaryShellDetectorData sigma U1 delta
          (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2)))
          (d2 : ClassicalBinaryShellDetectorData sigma U2 delta
          (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2)))
          (d3 : ClassicalBinaryShellDetectorData sigma U3 delta
          (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))),
          Nonempty (HeathBrownFullyUniformMixedSourceOutput sigma delta delta1
            delta2 eta epsilon K C Cp Cmv C0 C2 C4
            U0 U1 U2 U3 d0 d1 d2 d3) := by
  obtain ⟨K, C, Cp, Cmv, C0, C2, C4, B0, Ubase, hK, hC, hCp,
      hCmv, hC0, hC2, hC4, hB0, hUbase, hOutput⟩ :=
    eventually_heathBrownFullyUniformSourceColorOutput hsigma hdelta hdelta1
      hdelta2 hdeltaOrder hdelta1Upper hCube heta hepsilon
  refine ⟨K, C, Cp, Cmv, C0, C2, C4, B0, Ubase, hK, hC, hCp,
    hCmv, hC0, hC2, hC4, hB0, hUbase, ?_⟩
  intro U0 U1 U2 U3 hU0 hU1 hU2 hU3 d0 d1 d2 d3
  obtain ⟨label0, label1, label2, label3, hExtract⟩ :=
    mixed_absoluteSlabs_classical_binary_detector_extraction
      sigma delta U0 U1 U2 U3
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0))
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1))
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2))
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3))
      (U0 ^ (-delta2)) (U1 ^ (-delta2))
      (U2 ^ (-delta2)) (U3 ^ (-delta2))
      d0 d1 d2 d3 (by linarith) (by linarith) (by linarith) (by linarith)
  dsimp only at hExtract
  rcases hExtract with
    ⟨hSep0, hSep1, hSep2, hSep3, _hLarge0, _hLarge1, _hLarge2,
      _hLarge3, _hCard0, _hCard1, _hCard2, _hCard3, hEnergy⟩
  refine ⟨⟨label0, label1, label2, label3,
    hSep0, hSep1, hSep2, hSep3, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [classicalBinaryColorFamily] using hEnergy
  · exact fun hW => hOutput U0 hU0 d0 label0 hW
  · exact fun hW => hOutput U1 hU1 d1 label1 hW
  · exact fun hW => hOutput U2 hU2 d2 label2 hW
  · exact fun hW => hOutput U3 hU3 d3 label3 hW

#print axioms HeathBrownFullyUniformSourceColorOutput.toUniform
#print axioms HeathBrownFullyUniformMixedSourceOutput.toUniform
#print axioms eventually_heathBrownFullyUniformMixedSourceOutput

end

end GafniTao
