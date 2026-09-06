import GafniTao.ClassicalBinarySourceHeathBrownAlternative
import GafniTao.HeathBrownFiniteSelfElimination

/-!
# Packaged source output for one detector colour

This structure names the exact result already proved for one nonempty colour
at the unequal Heath--Brown cutoffs.  It is used to assemble the four
independently selected shell coordinates without replacing any dependent
label, coefficient, threshold, or power by a free variable.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Exact source output attached to one selected detector colour. -/
structure HeathBrownSourceColorOutput
    (sigma U delta delta1 delta2 eta epsilon : Real)
    (d : ClassicalBinaryShellDetectorData sigma U delta
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) where
  K : Real
  C : Real
  hK : 0 < K
  hC : 0 < C
  hN : 0 < classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  hCoeff : forall n, n ∈ dyadicInterval
      (classicalBinarySelectedN
        (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
        d.kI d.kII label.1) ->
    ‖classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma eta C label.1 n‖ <= 1
  hLarge : forall t, t ∈ classicalBinaryColorFamily d label ->
    classicalBinarySelectedThreshold
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma (U ^ (-delta2)) eta C label.1 <=
      ‖sourceDirichletPoly
        (classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1)
        (classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma eta C label.1) t‖
  branch :
    ClassicalBinaryTypeIOutput K sigma U delta (U ^ (-delta2))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) d label ∨
    let N := classicalBinarySelectedN
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII label.1
    let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma eta C label.1
    let L := classicalBinarySelectedThreshold
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
    let p := heathBrownSourcePower N U
    let P := Nat.ceil (4 / delta2)
    let R := 2 * U + U ^ delta
    Nonempty (HeathBrownPoweredEnergyPacket epsilon
        ((2 ^ P : Real) * U) R N p eta L
        (classicalBinaryColorFamily d label) a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket
        ((2 ^ P : Real) * U) R N p eta L
        (classicalBinaryColorFamily d label) a) ∧
      Nonempty (HeathBrownPoweredCardinalityPacket
        ((2 ^ P : Real) * U) R N (p + 1) eta L
        (classicalBinaryColorFamily d label) a)

/-- Uniform construction of the packaged output for every nonempty source
colour. -/
theorem eventually_heathBrownSourceColorOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 <= sigma) (hdelta : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hdelta1Upper : delta1 <= 1)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
        (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
        (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2),
        (classicalBinaryColorFamily d label).Nonempty ->
        Nonempty (HeathBrownSourceColorOutput
          sigma U delta delta1 delta2 eta epsilon d label) := by
  obtain ⟨U0, hU0, hOutput⟩ :=
    eventually_classicalBinaryColorFamily_source_heathBrown_alternative_native
      hsigma hdelta hdelta1 hdelta2 hdeltaOrder hdelta1Upper hCube
      heta hepsilon
  refine ⟨U0, hU0, ?_⟩
  intro U hU d label hW
  obtain ⟨K, C, hK, hC, hN, hCoeff, hLarge, hBranch⟩ :=
    hOutput U hU d label hW
  exact ⟨⟨K, C, hK, hC, hN, hCoeff, hLarge, hBranch⟩⟩

#print axioms eventually_heathBrownSourceColorOutput

end

end GafniTao
