import GafniTao.ClassicalBinaryHeathBrownDetector
import GafniTao.ClassicalBinarySelectedOrdinate

/-!
# Selected Heath--Brown families from the actual binary detector

This is the finite source-entry layer for one detector colour.  It records
the real selected family, its branch-independent unit coefficients and
threshold, and the exhaustive alternative between the exact physical
two-to-four power window and a genuinely long Type-I block.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The raw representative family selected by one complete detector colour. -/
noncomputable def classicalBinaryColorFamily
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) : Finset Real :=
  ((absoluteDyadicZeroSlab sigma U).filter
    (fun rho => detectorColor d.scale d.shift rho = label)).image
      (detectorRepresentative
        (absoluteDyadicZeroSlab sigma U) d.scale d.shift)

theorem classicalBinaryColorFamily_separated
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) :
    IsSeparated 1 (classicalBinaryColorFamily d label) := by
  simpa only [classicalBinaryColorFamily] using d.hSeparated label

theorem classicalBinaryColorFamily_large
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) :
    ∀ t ∈ classicalBinaryColorFamily d label,
      Sum.elim
        (ClassicalTypeIShellScaleLarge A Y d.kI sigma q0)
        (ClassicalTypeIIShellScaleLarge Y X d.kII sigma)
        (binaryScaleLabel label.1) t := by
  intro t ht
  rw [classicalBinaryColorFamily, Finset.mem_image] at ht
  obtain ⟨rho, hrho, rfl⟩ := ht
  have hm := Finset.mem_filter.mp hrho
  have hs : d.scale rho = label.1 := congrArg Prod.fst hm.2
  rw [← hs]
  exact d.hLarge rho hm.1

theorem classicalBinaryColorFamily_card_le_zeroCount
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (hU : 0 ≤ U) :
    (classicalBinaryColorFamily d label).card ≤ zeroCount sigma (2 * U) := by
  simpa only [classicalBinaryColorFamily] using
    image_filter_absoluteDyadicZeroSlab_card_le_zeroCount
      sigma U hU _ _

/-- The positive-ordinate version of a selected colour retains exact
cardinality and separation and lies in the physical shell interval. -/
theorem classicalBinaryColorFamily_oriented_data
    {sigma U delta : Real} {Y X A : Nat} {q0 : Real}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) :
    let W := classicalBinaryColorFamily d label
    let Wpos := classicalBinaryOrientedFamily label.1 W
    Wpos.card = W.card ∧ IsSeparated 1 Wpos ∧
      (∀ t ∈ Wpos, U - U ^ delta ≤ t ∧ t ≤ 2 * U + U ^ delta) := by
  dsimp only
  refine ⟨card_classicalBinaryOrientedFamily label.1 _,
    isSeparated_classicalBinaryOrientedFamily label.1
      (classicalBinaryColorFamily_separated d label), ?_⟩
  simpa only [classicalBinaryColorFamily] using
    classicalBinaryOrientedFamily_in_physical_interval d label

/-- A nonempty selected colour has unit-normalized coefficients and is
either in the exact Heath--Brown physical power window or is an explicitly
labelled long Type-I family. -/
theorem classicalBinaryColorFamily_powerWindow_or_longTypeI
    {sigma U delta D eta : Real} {A : Nat}
    (d : ClassicalBinaryShellDetectorData sigma U delta
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) A (U ^ (-D)))
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (hU : 0 < U)
    (hX : 0 < classicalBinaryHeathBrownCutoff U)
    (heta : 0 < eta)
    (hsigma : 0 ≤ sigma)
    (hW : (classicalBinaryColorFamily d label).Nonempty) :
    ∃ C : Real, 0 < C ∧
      let X := classicalBinaryHeathBrownCutoff U
      let N := classicalBinarySelectedN X X d.kI d.kII label.1
      let a := classicalBinarySelectedCoeff A X X d.kI d.kII
        sigma eta C label.1
      let V := classicalBinarySelectedThreshold X X d.kI d.kII
        sigma (U ^ (-D)) eta C label.1
      0 < N ∧
      (∀ n, n ∈ dyadicInterval N → ‖a n‖ ≤ 1) ∧
      (∀ t ∈ classicalBinaryColorFamily d label,
        V ≤ ‖sourceDirichletPoly N a t‖) ∧
      (((N : Real) ^ 2 ≤ classicalBinaryHeathBrownHeight U ∧
          classicalBinaryHeathBrownHeight U ≤ (N : Real) ^ 4) ∨
        ∃ r : Fin (d.kI * 2),
          binaryScaleLabel label.1 = Sum.inl r ∧
          X ^ 2 < N ∧ N < A) := by
  obtain ⟨C, hC, hCoeff⟩ := sharpMollifiedCoeff_bound eta heta
  refine ⟨C, hC, ?_⟩
  dsimp only
  have hkIProduct : 0 < d.kI * 2 := d.hkI
  have hkI : 0 < d.kI := by omega
  have hAlt := classicalBinarySelectedFamily_alternative
    (A := A) (X := classicalBinaryHeathBrownCutoff U)
    (kI := d.kI) (kII := d.kII)
    hX (Real.rpow_pos_of_pos hU _) hkI d.hkII_eq hC heta.le hsigma
    (fun n hn => hCoeff _ _ n hn) label.1
    (classicalBinaryColorFamily d label) hW
    (classicalBinaryColorFamily_large d label)
  dsimp only at hAlt
  refine ⟨hAlt.1, hAlt.2.1, hAlt.2.2.1, ?_⟩
  have hWindow := classicalBinarySelected_powerWindow_or_longTypeI
    label.1 hAlt.2.2.2
  simpa only [classicalBinaryHeathBrownHeight] using hWindow

#print axioms classicalBinaryColorFamily_oriented_data
#print axioms classicalBinaryColorFamily_powerWindow_or_longTypeI

end

end GafniTao
