import GafniTao.FiniteWeightedMixedTransfer

/-!
# Detector extraction for four different zero shells

The four coordinates of a resonant zero tuple may live in different dyadic
shells and therefore have different detector color spaces, shifts, and
local multiplicity bounds.  This theorem performs the simultaneous finite
pigeonhole and the exact product-fiber transfer without identifying any of
those data.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Coordinate-dependent, multiplicity-preserving detector extraction. -/
theorem mixed_weighted_energy_detector_extraction
    {K0 K1 K2 K3 : Type*}
    [Fintype K0] [Fintype K1] [Fintype K2] [Fintype K3]
    [DecidableEq K0] [DecidableEq K1] [DecidableEq K2] [DecidableEq K3]
    [Nonempty K0] [Nonempty K1] [Nonempty K2] [Nonempty K3]
    (S0 S1 S2 S3 : Finset Complex) (weight : Complex → Nat)
    (eta H0 H1 H2 H3 : Real)
    (color0 : Complex → K0) (color1 : Complex → K1)
    (color2 : Complex → K2) (color3 : Complex → K3)
    (f0 f1 f2 f3 : Complex → Real) (L0 L1 L2 L3 : Nat)
    (hShift0 : ∀ rho, rho ∈ S0 → |rho.im - f0 rho| ≤ H0)
    (hShift1 : ∀ rho, rho ∈ S1 → |rho.im - f1 rho| ≤ H1)
    (hShift2 : ∀ rho, rho ∈ S2 → |rho.im - f2 rho| ≤ H2)
    (hShift3 : ∀ rho, rho ∈ S3 → |rho.im - f3 rho| ≤ H3)
    (hLocal0 : ∀ t, (∑ rho ∈ S0.filter (fun z => f0 z = t), weight rho) ≤ L0)
    (hLocal1 : ∀ t, (∑ rho ∈ S1.filter (fun z => f1 z = t), weight rho) ≤ L1)
    (hLocal2 : ∀ t, (∑ rho ∈ S2.filter (fun z => f2 z = t), weight rho) ≤ L2)
    (hLocal3 : ∀ t, (∑ rho ∈ S3.filter (fun z => f3 z = t), weight rho) ≤ L3) :
    ∃ label0 : K0, ∃ label1 : K1, ∃ label2 : K2, ∃ label3 : K3,
      let W0 := (S0.filter (fun rho => color0 rho = label0)).image f0
      let W1 := (S1.filter (fun rho => color1 rho = label1)).image f1
      let W2 := (S2.filter (fun rho => color2 rho = label2)).image f2
      let W3 := (S3.filter (fun rho => color3 rho = label3)).image f3
      weightedMixedAdditiveEnergyOn S0 S1 S2 S3 weight eta ≤
        (Fintype.card K0 * Fintype.card K1 *
            Fintype.card K2 * Fintype.card K3) *
          (L0 * L1 * L2 * L3) *
            MixedApproxAddEnergy (eta + H0 + H1 + H2 + H3)
              W0 W1 W2 W3 := by
  classical
  let K := (K0 × K1) × (K2 × K3)
  let colorQ : ((Complex × Complex) × (Complex × Complex)) → K := fun q =>
    ((color0 q.1.1, color1 q.1.2), (color2 q.2.1, color3 q.2.2))
  let R := resonantQuadruplesOnFour S0 S1 S2 S3 eta
  have hColor : ∃ label : K,
      (∑ q ∈ R, weightedQuadruple weight q) ≤
        Fintype.card K *
          ∑ q ∈ R.filter (fun y => colorQ y = label),
            weightedQuadruple weight q := by
    by_cases hR : R.Nonempty
    · obtain ⟨label, -, hlabel⟩ :=
        RiemannZeta.GuthMaynard.weighted_finite_pigeonhole R
          (Finset.univ : Finset K) (weightedQuadruple weight) colorQ hR
          (fun q _ => Finset.mem_univ (colorQ q))
      exact ⟨label, by simpa using hlabel⟩
    · let label : K := Classical.choice inferInstance
      refine ⟨label, ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hR]
      simp
  obtain ⟨label, hlabel⟩ := hColor
  let label0 : K0 := label.1.1
  let label1 : K1 := label.1.2
  let label2 : K2 := label.2.1
  let label3 : K3 := label.2.2
  let W0 := (S0.filter (fun rho => color0 rho = label0)).image f0
  let W1 := (S1.filter (fun rho => color1 rho = label1)).image f1
  let W2 := (S2.filter (fun rho => color2 rho = label2)).image f2
  let W3 := (S3.filter (fun rho => color3 rho = label3)).image f3
  let Q := R.filter (fun y => colorQ y = label)
  let U := mixedApproximateAdditiveQuadruples
    (eta + H0 + H1 + H2 + H3) W0 W1 W2 W3
  have hQ : Q ⊆ quadrupleProductOf S0 S1 S2 S3 := by
    intro q hq
    exact Finset.filter_subset _ _
      ((Finset.filter_subset _ _) hq)
  have hMaps : Set.MapsTo (mappedQuadrupleOf f0 f1 f2 f3)
      (Q : Set _) (U : Set _) := by
    intro q hq
    have hqFilter := Finset.mem_filter.mp hq
    have hqRes := hqFilter.1
    have hqColor := hqFilter.2
    have hm := mem_resonantQuadruplesOnFour.mp hqRes
    have hc0 := congrArg (fun v => v.1.1) hqColor
    have hc1 := congrArg (fun v => v.1.2) hqColor
    have hc2 := congrArg (fun v => v.2.1) hqColor
    have hc3 := congrArg (fun v => v.2.2) hqColor
    have hw0 : f0 q.1.1 ∈ W0 := Finset.mem_image.mpr
      ⟨q.1.1, Finset.mem_filter.mpr ⟨hm.1, hc0⟩, rfl⟩
    have hw1 : f1 q.1.2 ∈ W1 := Finset.mem_image.mpr
      ⟨q.1.2, Finset.mem_filter.mpr ⟨hm.2.1, hc1⟩, rfl⟩
    have hw2 : f2 q.2.1 ∈ W2 := Finset.mem_image.mpr
      ⟨q.2.1, Finset.mem_filter.mpr ⟨hm.2.2.1, hc2⟩, rfl⟩
    have hw3 : f3 q.2.2 ∈ W3 := Finset.mem_image.mpr
      ⟨q.2.2, Finset.mem_filter.mpr ⟨hm.2.2.2.1, hc3⟩, rfl⟩
    have hs0 := hShift0 q.1.1 hm.1
    have hs1 := hShift1 q.1.2 hm.2.1
    have hs2 := hShift2 q.2.1 hm.2.2.1
    have hs3 := hShift3 q.2.2 hm.2.2.2.1
    have hres := hm.2.2.2.2
    rw [abs_le] at hs0 hs1 hs2 hs3 hres
    unfold U mixedApproximateAdditiveQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold quadrupleProductOf
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_product.mpr ⟨hw0, hw1⟩,
        Finset.mem_product.mpr ⟨hw2, hw3⟩⟩
    · change |f0 q.1.1 + f1 q.1.2 - f2 q.2.1 - f3 q.2.2| ≤
        eta + H0 + H1 + H2 + H3
      rw [abs_le]
      constructor <;> linarith
  have hTransfer := weighted_mixed_quadruple_sum_le_fiber_product_mul_card
    S0 S1 S2 S3 Q U weight f0 f1 f2 f3 L0 L1 L2 L3 hQ hMaps
    hLocal0 hLocal1 hLocal2 hLocal3
  refine ⟨label0, label1, label2, label3, ?_⟩
  dsimp only
  change (∑ q ∈ R, weightedQuadruple weight q) ≤ _
  calc
    (∑ q ∈ R, weightedQuadruple weight q) ≤
        Fintype.card K *
          ∑ q ∈ Q, weightedQuadruple weight q := by
      simpa only [Q] using hlabel
    _ ≤ Fintype.card K *
        ((L0 * L1 * L2 * L3) * U.card) :=
      Nat.mul_le_mul_left _ hTransfer
    _ = (Fintype.card K0 * Fintype.card K1 *
          Fintype.card K2 * Fintype.card K3) *
        (L0 * L1 * L2 * L3) *
          MixedApproxAddEnergy (eta + H0 + H1 + H2 + H3)
            W0 W1 W2 W3 := by
      simp only [K, Fintype.card_prod, U, MixedApproxAddEnergy]
      ring

#print axioms mixed_weighted_energy_detector_extraction

end

end GafniTao
