import GafniTao.SourceEnergySplitReassembly
import GafniTao.ClassicalBinaryLongTailFamily
import GafniTao.ClassicalBinaryFullyUniformSourceAlternative

/-!
# Reassembly of the actual Type-I long tail

This is the exact finite bridge from the Type-I member of the frozen binary
detector to four classified source families.  In particular it uses the
long-tail lower bound retained in `ClassicalBinaryShellDetectorData`; it does
not infer source control from the later MHH cardinality projection.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem ClassicalBinaryTypeIOutput.energy_le_of_classified_sources
    {K sigma U delta q0 : Real} {Y X A : Nat}
    {d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0}
    {label : Fin (d.kI * 2 + d.kII * 2) × Fin 2}
    (hout : ClassicalBinaryTypeIOutput K sigma U delta q0 Y X A d label)
    (hY : 1 <= Y) {M : Real}
    (hSource : forall (r : Nat) (W : Finset Real),
      W ⊆ classicalBinaryOrientedFamily label.1
        (classicalBinaryColorFamily d label) ->
      IsSeparated 1 W ->
      (forall t, t ∈ W ->
        q0 * (3 / 8 : Real) / (Nat.clog 2 A + 1 : Nat) <=
          ‖typeISourceSmoothBlock Y A r sigma t‖) ->
      (r < 2 ∨ A < 2 * (2 ^ r * Y) ∨
        (((Y + 1 : Nat) : Real) <= ((2 ^ r * Y : Nat) : Real) / 2 ∧
          2 * (2 ^ r * Y) <= A)) ->
      (ApproxAddEnergy 1 W : Real) <= M) :
    (ApproxAddEnergy 1 (classicalBinaryColorFamily d label) : Real) <=
      (((((Nat.clog 2 A) + 1) ^ 4 : Nat) : Real) *
        (doubleFloorDefectWindow 1).card) * M := by
  obtain ⟨rI, hlabel, _hLower, _hUpper, _hCard⟩ := hout
  let Wpos := classicalBinaryOrientedFamily label.1
    (classicalBinaryColorFamily d label)
  let k := Nat.clog 2 A
  let V : Real := (3 / 4 : Real) * (q0 / 2)
  have hCover : A <= 2 ^ k * Y := by
    simpa only [k] using sharp_source_cutoff_le_clog_cover hY
  have hSep : IsSeparated 1 Wpos := by
    simpa only [Wpos] using
      (classicalBinaryColorFamily_oriented_data d label).2.1
  have hLarge : forall t, t ∈ Wpos ->
      V <= ‖classicalZetaLongTail Y A
        ((sigma : Complex) + Complex.I * (t : Complex))‖ := by
    simpa only [Wpos, V, mul_div_assoc] using
      classicalBinaryColorFamily_longTail_on_oriented d label rI hlabel
  obtain ⟨split⟩ := longTail_source_energy_split Y A k sigma V Wpos
    hY hCover hSep hLarge
  have hEach : forall i : Fin 4,
      (ApproxAddEnergy 1 (split.Ws i) : Real) <= M := by
    intro i
    exact hSource (split.scale i).val (split.Ws i) (split.hSubset i)
      (split.hSeparated i) (by
        intro t ht
        have h := split.hLarge i t ht
        convert h using 1
        simp only [V, k]
        ring)
      (split.hClassified i)
  have hReassembled := split.energy_le_of_all_sources hEach
  have hOrientation := approxAddEnergy_classicalBinaryOrientedFamily
    label.1 (classicalBinaryColorFamily d label)
  simpa only [Wpos, k, hOrientation] using hReassembled

#print axioms ClassicalBinaryTypeIOutput.energy_le_of_classified_sources

end

end GafniTao
