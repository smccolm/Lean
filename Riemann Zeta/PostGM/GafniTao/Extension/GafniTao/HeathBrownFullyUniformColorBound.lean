import GafniTao.HeathBrownFullyUniformMixedSelfReduction
import GafniTao.HeathBrownUniformFiniteSelfElimination

/-!
# Literal one-colour bounds for the fully uniform source output

Both alternatives are converted to explicit finite inequalities.  The
Type-I member uses the actual normalized MHH cardinality bound and the exact
separated-set cubic energy estimate.  The Type-II member uses the actual
powered energy output together with both consecutive cardinality packets.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The literal MHH expression attached to a selected Type-I shell. -/
noncomputable def classicalBinaryTypeIMHHMajorant
    (K sigma U q0 : Real) (Y : Nat) (kI : Nat)
    (r : Fin (kI * 2)) : Real :=
  K * (1 + (((harmonic (classicalTypeIShellScaleN Y r) : Rat) : Real))) *
    ((classicalTypeIShellScaleN Y r : Real) ^ 2 /
        ((classicalTypeIShellScaleN Y r : Real) ^ sigma *
          (((3 / 4 : Real) * (q0 / 2)) / (kI : Real))) ^ 2 +
      (3 * U) * min
        ((classicalTypeIShellScaleN Y r : Real) /
          ((classicalTypeIShellScaleN Y r : Real) ^ sigma *
            (((3 / 4 : Real) * (q0 / 2)) / (kI : Real))) ^ 2)
        ((classicalTypeIShellScaleN Y r : Real) ^ 4 /
          ((classicalTypeIShellScaleN Y r : Real) ^ sigma *
            (((3 / 4 : Real) * (q0 / 2)) / (kI : Real))) ^ 6))

theorem ClassicalBinaryTypeIOutput.energy_le_majorant
    {K sigma U delta q0 : Real} {Y X A : Nat}
    {d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0}
    {label : Fin (d.kI * 2 + d.kII * 2) × Fin 2}
    (hout : ClassicalBinaryTypeIOutput K sigma U delta q0 Y X A d label) :
    ∃ r : Fin (d.kI * 2),
      binaryScaleLabel label.1 = Sum.inl r ∧
      X ≤ classicalTypeIShellScaleN Y r ∧
      classicalTypeIShellScaleN Y r < A ∧
      4 * (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real) ≤
        12 * (classicalBinaryTypeIMHHMajorant K sigma U q0 Y d.kI r) ^ 3 := by
  obtain ⟨r, hrLabel, hrLower, hrUpper, hCard⟩ := hout
  refine ⟨r, hrLabel, hrLower, hrUpper, ?_⟩
  have hEnergyNat : ApproxAddEnergy 1 (classicalBinaryColorFamily d label) ≤
      3 * (classicalBinaryColorFamily d label).card ^ 3 :=
    approxAddEnergy_le_three_card_cubed _
      (classicalBinaryColorFamily_separated d label)
  have hEnergy : (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real) ≤
      3 * ((classicalBinaryColorFamily d label).card : Real) ^ 3 := by
    exact_mod_cast hEnergyNat
  have hCard' : ((classicalBinaryColorFamily d label).card : Real) ≤
      classicalBinaryTypeIMHHMajorant K sigma U q0 Y d.kI r := by
    simpa only [classicalBinaryTypeIMHHMajorant] using hCard
  have hMajorantNonneg : 0 ≤
      classicalBinaryTypeIMHHMajorant K sigma U q0 Y d.kI r :=
    (Nat.cast_nonneg _).trans hCard'
  calc
    4 * (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real) ≤
        4 * (3 * ((classicalBinaryColorFamily d label).card : Real) ^ 3) := by
      gcongr
    _ ≤ 4 * (3 *
        (classicalBinaryTypeIMHHMajorant K sigma U q0 Y d.kI r) ^ 3) := by
      gcongr
    _ = 12 *
        (classicalBinaryTypeIMHHMajorant K sigma U q0 Y d.kI r) ^ 3 := by
      ring

/-- Every fully uniform source colour has a literal finite energy bound in
its actual branch.  The Type-II output retains the common-constant
equalities needed for subsequent rewriting. -/
theorem HeathBrownFullyUniformSourceColorOutput.energy_branch_bound
    {sigma U delta delta1 delta2 eta epsilon : Real}
    {K C Cp Cmv C0 C2 C4 : Real}
    {d : ClassicalBinaryShellDetectorData sigma U delta
      (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))}
    {label : Fin (d.kI * 2 + d.kII * 2) × Fin 2}
    (out : HeathBrownFullyUniformSourceColorOutput sigma U delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4 d label)
    (hU : 0 ≤ U) (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4) :
    (∃ r : Fin (d.kI * 2),
      binaryScaleLabel label.1 = Sum.inl r ∧
      Nat.floor (U ^ (delta2 / 2)) ≤
        classicalTypeIShellScaleN (Nat.floor (U ^ delta1)) r ∧
      classicalTypeIShellScaleN (Nat.floor (U ^ delta1)) r <
        Nat.floor (sharpZetaCutoff U) ∧
      4 * (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real) ≤
        12 * (classicalBinaryTypeIMHHMajorant K sigma U (U ^ (-delta2))
          (Nat.floor (U ^ delta1)) d.kI r) ^ 3) ∨
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
    ∃ full : HeathBrownFullyUniformOutputs epsilon
        ((2 ^ P : Real) * U) R N p eta L
        (classicalBinaryColorFamily d label) a Cp Cmv C0 C2 C4,
      4 * (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real) ≤
        ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteScalarBound epsilon C0 C2 C4
            ((2 ^ P : Real) * U)
            (heathBrownPoweredThreshold N p L Cp eta)
            ((2 ^ p * N ^ p : Nat) : Real)
            (min full.card.bound full.next.bound)) := by
  rcases out.branch with hTypeI | hTypeII
  · left
    exact hTypeI.energy_le_majorant
  · right
    obtain ⟨_r, _hlabel, ⟨full⟩⟩ := hTypeII
    refine ⟨full, ?_⟩
    have hB : 0 ≤ (2 ^ Nat.ceil (4 / delta2) : Real) * U := by positivity
    have hRaw := full.energy.energy_le_two_cardinality_bounds full.card
      full.next hC0 hC2 hC4 hB
      (classicalBinaryColorFamily_separated d label)
    rw [full.energy_Cp] at hRaw
    exact hRaw

#print axioms ClassicalBinaryTypeIOutput.energy_le_majorant
#print axioms HeathBrownFullyUniformSourceColorOutput.energy_branch_bound

end

end GafniTao
