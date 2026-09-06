import GafniTao.ClassicalBinaryHeathBrownSourceDetector
import GafniTao.ClassicalBinarySelectedAlternative
import GafniTao.ClassicalBinaryHeathBrownFamily

/-!
# Selected families at the unequal source cutoffs

This is the unequal-cutoff counterpart of the earlier prototype.  It
normalizes the literal family returned by the detector and retains the exact
Type-I / Type-II label and range.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Source-faithful unit-coefficient data and exhaustive branch alternative
for one nonempty detector colour at arbitrary ordered cutoffs `X <= Y`. -/
theorem classicalBinarySourceSelectedFamily_alternative
    {sigma U delta q0 eta C : Real} {Y X A : Nat}
    (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (hY : 0 < Y) (hX : 0 < X)
    (hq0 : 0 < q0) (hC : 0 < C)
    (heta : 0 <= eta) (hsigma : 0 <= sigma)
    (hCoeff : forall n : Nat, 0 < n ->
      ‖sharpMollifiedCoeff Y X n‖ <= C * (n : Real) ^ eta)
    (hW : (classicalBinaryColorFamily d label).Nonempty) :
    let N := classicalBinarySelectedN Y X d.kI d.kII label.1
    let a := classicalBinarySelectedCoeff A Y X d.kI d.kII sigma eta C label.1
    let L := classicalBinarySelectedThreshold Y X d.kI d.kII
      sigma q0 eta C label.1
    0 < N /\
      (forall n, n ∈ dyadicInterval N -> ‖a n‖ <= 1) /\
      (forall t, t ∈ classicalBinaryColorFamily d label ->
        L <= ‖sourceDirichletPoly N a t‖) /\
      ((exists r : Fin (d.kI * 2),
          binaryScaleLabel label.1 = Sum.inl r /\ Y <= N /\ N < A) \/
        (exists r : Fin (d.kII * 2),
          binaryScaleLabel label.1 = Sum.inr r /\ X <= N /\ N < Y * X)) := by
  dsimp only
  have hkIProduct : 0 < d.kI * 2 := d.hkI
  have hkI : 0 < d.kI := by omega
  have hUnit := norm_classicalBinarySelectedCoeff_le_one
    A Y X d.kI d.kII sigma eta C label.1 hY hX hsigma heta hC hCoeff
  have hLarge : forall t, t ∈ classicalBinaryColorFamily d label ->
      classicalBinarySelectedThreshold Y X d.kI d.kII
          sigma q0 eta C label.1 <=
        ‖sourceDirichletPoly
          (classicalBinarySelectedN Y X d.kI d.kII label.1)
          (classicalBinarySelectedCoeff A Y X d.kI d.kII
            sigma eta C label.1) t‖ := by
    intro t ht
    exact classicalBinarySelectedCoeff_large A Y X d.kI d.kII
      sigma q0 eta C t label.1 hY hX hC
      (classicalBinaryColorFamily_large d label t ht)
  refine ⟨classicalBinarySelectedN_pos hY hX label.1, hUnit, hLarge, ?_⟩
  cases hlabel : binaryScaleLabel label.1 with
  | inl r =>
      left
      obtain ⟨t, ht⟩ := hW
      refine ⟨r, rfl, le_classicalBinarySelectedN_of_typeI label.1 r hlabel, ?_⟩
      exact classicalBinarySelectedN_lt_cutoff_of_typeI_large
        hq0 hkI label.1 r hlabel
          (classicalBinaryColorFamily_large d label t ht)
  | inr r =>
      right
      refine ⟨r, rfl, ?_⟩
      exact classicalBinarySelectedN_typeII_range hX
        (by rw [d.hkII_eq]) label.1 r hlabel

#print axioms classicalBinarySourceSelectedFamily_alternative

end

end GafniTao
