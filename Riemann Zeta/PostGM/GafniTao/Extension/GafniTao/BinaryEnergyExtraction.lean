import GafniTao.WeightedSubfamilyEnergy

/-!
# Energy-preserving binary branch extraction

The zero-density detector has a pointwise Type-I/Type-II alternative.  For
additive energy one may not select a single branch by cardinality: each of
the four coordinates can choose its own branch.  This module encodes the
disjoint union of the two scale spaces and applies the existing
four-coordinate weighted-energy pigeonhole theorem once.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Decode the finite color used for a binary branch and its internal dyadic
scale. -/
def binaryScaleLabel {kI kII : Nat} (q : Fin (kI + kII)) :
    Fin kI ⊕ Fin kII :=
  finSumFinEquiv.symm q

/-- Predicate on the combined finite color space. -/
def BinaryScaleLarge {kI kII : Nat}
    (largeI : Fin kI → Real → Prop) (largeII : Fin kII → Real → Prop)
    (q : Fin (kI + kII)) (t : Real) : Prop :=
  Sum.elim largeI largeII (binaryScaleLabel q) t

/-- Exact binary-branch, four-coordinate energy extraction.  The conclusion
keeps every selected branch and scale accessible through `binaryScaleLabel`.
-/
theorem finite_binary_shifted_energy_extraction_on
    (S : Finset Complex) (weight : Complex → Nat)
    (eta H : Real) (kI kII L : Nat) (hkI : 0 < kI)
    (largeI : Fin kI → Real → Prop) (largeII : Fin kII → Real → Prop)
    (choosesI : Complex → Prop) (inInterval : Real → Prop)
    (hEachI : ∀ rho, rho ∈ S →
      ∀ _hbranch : choosesI rho,
        ∃ t : Real, |rho.im - t| ≤ H ∧ inInterval t ∧
          ∃ r : Fin kI, largeI r t)
    (hEachII : ∀ rho, rho ∈ S →
      ∀ _hbranch : ¬ choosesI rho,
        ∃ t : Real, |rho.im - t| ≤ H ∧ inInterval t ∧
          ∃ r : Fin kII, largeII r t)
    (hLocal : ∀ z : Int,
      (∑ rho ∈ S.filter
        (fun y => (z : Real) ≤ y.im ∧ y.im < (z : Real) + 1),
        weight rho) ≤ L) :
    ∃ label : Fin 4 → (Fin (kI + kII) × Fin 2),
      ∃ W : Fin 4 → Finset Real,
        (∀ i : Fin 4, IsSeparated 1 (W i)) ∧
        (∀ i : Fin 4, ∀ t, t ∈ W i →
          Sum.elim largeI largeII (binaryScaleLabel (label i).1) t) ∧
        (∀ i : Fin 4, ∀ t, t ∈ W i → inInterval t) ∧
        (∀ i : Fin 4, (W i).card ≤ S.card) ∧
        weightedAdditiveEnergyOn S weight eta ≤
          (2 * (kI + kII)) ^ 4 * ((2 * ⌈H + 1⌉₊ + 1) * L) ^ 4 *
            MixedApproxAddEnergy (eta + 4 * (H + 1))
              (W 0) (W 1) (W 2) (W 3) := by
  classical
  have hk : 0 < kI + kII := Nat.add_pos_left hkI kII
  let large : Fin (kI + kII) → Real → Prop :=
    BinaryScaleLarge largeI largeII
  have hEach : ∀ rho, rho ∈ S → ∃ t : Real,
      |rho.im - t| ≤ H ∧ inInterval t ∧
        ∃ r : Fin (kI + kII), large r t := by
    intro rho hrho
    by_cases hb : choosesI rho
    · obtain ⟨t, ht, hInterval, r, hr⟩ := hEachI rho hrho hb
      refine ⟨t, ht, hInterval, finSumFinEquiv (Sum.inl r), ?_⟩
      simpa [large, BinaryScaleLarge, binaryScaleLabel]
    · obtain ⟨t, ht, hInterval, r, hr⟩ := hEachII rho hrho hb
      refine ⟨t, ht, hInterval, finSumFinEquiv (Sum.inr r), ?_⟩
      simpa [large, BinaryScaleLarge, binaryScaleLabel]
  obtain ⟨label, hSep, hLarge, hInterval, hEnergy⟩ :=
    finite_shifted_dyadic_energy_extraction_on S weight eta H
      (kI + kII) L hk large inInterval hEach hLocal
  let shift : Complex → Real := fun rho =>
    if h : rho ∈ S then Classical.choose (hEach rho h) else rho.im
  let scale : Complex → Fin (kI + kII) := fun rho =>
    if h : rho ∈ S then
      Classical.choose (Classical.choose_spec (hEach rho h)).2.2
    else ⟨0, hk⟩
  let representative := detectorRepresentative S scale shift
  let W := fun i : Fin 4 =>
    (S.filter (fun rho => detectorColor scale shift rho = label i)).image
      representative
  refine ⟨label, W, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [W, representative, scale, shift] using hSep
  · intro i t ht
    simpa [large, BinaryScaleLarge, binaryScaleLabel, W, representative,
      scale, shift] using hLarge i t ht
  · simpa only [W, representative, scale, shift] using hInterval
  · intro i
    exact (Finset.card_image_le.trans
      (Finset.card_le_card (Finset.filter_subset _ _)))
  · simpa only [W, representative, scale, shift] using hEnergy

#print axioms finite_binary_shifted_energy_extraction_on

end

end GafniTao
