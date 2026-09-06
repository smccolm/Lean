import GafniTao.EnergyDetectorPowering
import GafniTao.RealEnergyDiscretization

/-!
# Four-coordinate powering colors for real additive energy

Choosing a dyadic block after powering pointwise and then retaining merely a
large-cardinality subfamily does not control additive energy.  The source
argument instead pigeonholes the four coordinates of every approximate
additive quadruple simultaneously.  This file proves that exact finite
statement.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Coordinate projection from an ordered real additive quadruple. -/
def realQuadrupleCoord (i : Fin 4)
    (q : (Real × Real) × (Real × Real)) : Real :=
  match i with
  | ⟨0, _⟩ => q.1.1
  | ⟨1, _⟩ => q.1.2
  | ⟨2, _⟩ => q.2.1
  | ⟨3, _⟩ => q.2.2

/-- Exact four-coordinate color extraction for approximate real additive
energy.  The four resulting color classes may differ; that distinction is
essential and is retained as a mixed energy. -/
theorem exists_real_energy_color_classes
    {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa] [Nonempty Kappa]
    (eta : Real) (W : Finset Real) (color : Real → Kappa) :
    ∃ label : Fin 4 → Kappa,
      let Wi := fun i : Fin 4 => W.filter (fun t => color t = label i)
      ApproxAddEnergy eta W ≤
        (Fintype.card Kappa) ^ 4 *
          MixedApproxAddEnergy eta (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
  classical
  let S := approximateAdditiveQuadruples eta W
  let colorQ : ((Real × Real) × (Real × Real)) → Fin 4 → Kappa :=
    fun q i => color (realQuadrupleCoord i q)
  obtain ⟨label, hColor⟩ :=
    exists_four_coordinate_weighted_color_fiber_type S (fun _ => 1) colorQ
  let Q := S.filter (fun q => colorQ q = label)
  let Wi := fun i : Fin 4 => W.filter (fun t => color t = label i)
  have hSubset : Q ⊆
      mixedApproximateAdditiveQuadruples eta (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
    intro q hq
    have hqQ := Finset.mem_filter.mp hq
    have hqS := hqQ.1
    have hqColor := hqQ.2
    have hSource :
        q.1.1 ∈ W ∧ q.1.2 ∈ W ∧ q.2.1 ∈ W ∧ q.2.2 ∈ W ∧
          |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ eta := by
      simpa [S, approximateAdditiveQuadruples, and_assoc] using hqS
    have hc (i : Fin 4) :
        color (realQuadrupleCoord i q) = label i := congrFun hqColor i
    rw [mixedApproximateAdditiveQuadruples, Finset.mem_filter]
    constructor
    · unfold quadrupleProductOf
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_filter.mpr ⟨hSource.1, hc 0⟩,
          Finset.mem_filter.mpr ⟨hSource.2.1, hc 1⟩⟩
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_filter.mpr ⟨hSource.2.2.1, hc 2⟩,
          Finset.mem_filter.mpr ⟨hSource.2.2.2.1, hc 3⟩⟩
    · exact hSource.2.2.2.2
  refine ⟨label, ?_⟩
  dsimp only
  change S.card ≤ (Fintype.card Kappa) ^ 4 *
    MixedApproxAddEnergy eta (Wi 0) (Wi 1) (Wi 2) (Wi 3)
  calc
    S.card = ∑ _q ∈ S, 1 := by simp
    _ ≤ (Fintype.card Kappa) ^ 4 * ∑ _q ∈ Q, 1 := by
      simpa only [Q] using hColor
    _ = (Fintype.card Kappa) ^ 4 * Q.card := by simp
    _ ≤ (Fintype.card Kappa) ^ 4 *
        MixedApproxAddEnergy eta (Wi 0) (Wi 1) (Wi 2) (Wi 3) := by
      exact Nat.mul_le_mul_left _ (Finset.card_le_card hSubset)

#print axioms realQuadrupleCoord
#print axioms exists_real_energy_color_classes

end

end GafniTao
