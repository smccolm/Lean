import GafniTao.FiniteWeightedEnergyTransfer

/-!
# Energy-preserving finite detector extraction

This module combines simultaneous four-coordinate pigeonholing with the
product-multiplicity fiber estimate.  The output is a mixed approximate
energy of four (possibly different) color classes.  This is the faithful
finite form needed before the Heath--Brown large-value energy estimates.
-/

open scoped BigOperators

namespace GafniTao

noncomputable section

def complexQuadrupleCoord (i : Fin 4)
    (q : (Complex × Complex) × (Complex × Complex)) : Complex :=
  match i with
  | ⟨0, _⟩ => q.1.1
  | ⟨1, _⟩ => q.1.2
  | ⟨2, _⟩ => q.2.1
  | ⟨3, _⟩ => q.2.2

/-- Ordered mixed approximate additive quadruples. -/
noncomputable def mixedApproximateAdditiveQuadruples
    (eta : Real) (W0 W1 W2 W3 : Finset Real) :
    Finset ((Real × Real) × (Real × Real)) :=
  (quadrupleProductOf W0 W1 W2 W3).filter fun q =>
    |q.1.1 + q.1.2 - q.2.1 - q.2.2| <= eta

/-- Cardinality of the mixed approximate quadruple family. -/
noncomputable def MixedApproxAddEnergy
    (eta : Real) (W0 W1 W2 W3 : Finset Real) : Nat :=
  (mixedApproximateAdditiveQuadruples eta W0 W1 W2 W3).card

/-- The ordinary approximate energy is the diagonal mixed energy. -/
theorem mixedApproxAddEnergy_self
    (eta : Real) (W : Finset Real) :
    MixedApproxAddEnergy eta W W W W =
      RiemannZeta.GuthMaynard.ApproxAddEnergy eta W := by
  rfl

/-- Exact defect inflation for a resonant distinct-zero quadruple after four
independent shifts of size at most `H`. -/
theorem shifted_zero_quadruple_defect_le
    {sigma T H : Real}
    {q : (Complex × Complex) × (Complex × Complex)}
    (hq : q ∈ resonantZeroQuadruples sigma T)
    (representative : Complex -> Real)
    (hShift : forall i : Fin 4,
      |(complexQuadrupleCoord i q).im -
          representative (complexQuadrupleCoord i q)| <= H) :
    |representative q.1.1 + representative q.1.2 -
        representative q.2.1 - representative q.2.2| <= 1 + 4 * H := by
  have h0 := hShift 0
  have h1 := hShift 1
  have h2 := hShift 2
  have h3 := hShift 3
  have hRes := (mem_resonantZeroQuadruples.mp hq).2.2.2.2
  simp only [complexQuadrupleCoord] at h0 h1 h2 h3
  rw [abs_le] at h0 h1 h2 h3 hRes ⊢
  constructor <;> linarith

/-- The exact finite energy-preserving extraction.  The four output sets may
come from different detector colors; no unjustified same-color assumption is
made.  `L` bounds the total analytic multiplicity in every representative
fiber. -/
theorem exists_mixed_energy_color_classes
    {Kappa : Type*} [Fintype Kappa] [DecidableEq Kappa] [Nonempty Kappa]
    (sigma T H : Real) (L : Nat)
    (color : Complex -> Kappa)
    (representative : Complex -> Real)
    (hShift : forall rho, rho ∈ zeroSet sigma T ->
      |rho.im - representative rho| <= H)
    (hLocal : forall t : Real,
      (∑ rho ∈ (zeroSet sigma T).filter
        (fun z => representative z = t), zeroMultiplicity rho) <= L) :
    exists label : Fin 4 -> Kappa,
      let W := fun i : Fin 4 =>
        ((zeroSet sigma T).filter
          (fun rho => color rho = label i)).image representative
      zeroAdditiveEnergyCount sigma T <=
        (Fintype.card Kappa) ^ 4 * L ^ 4 *
          MixedApproxAddEnergy (1 + 4 * H) (W 0) (W 1) (W 2) (W 3) := by
  classical
  let colorQ : ((Complex × Complex) × (Complex × Complex)) ->
      Fin 4 -> Kappa :=
    fun q i => color (complexQuadrupleCoord i q)
  obtain ⟨label, hColor⟩ :=
    exists_four_coordinate_weighted_color_fiber_type
      (resonantZeroQuadruples sigma T) zeroQuadrupleWeight colorQ
  let Q := (resonantZeroQuadruples sigma T).filter
    (fun q => colorQ q = label)
  let W := fun i : Fin 4 =>
    ((zeroSet sigma T).filter
      (fun rho => color rho = label i)).image representative
  let U := mixedApproximateAdditiveQuadruples (1 + 4 * H)
    (W 0) (W 1) (W 2) (W 3)
  have hQ : Q ⊆ quadrupleProduct (zeroSet sigma T) := by
    intro q hq
    have hqRes := (Finset.mem_filter.mp hq).1
    have hz := (mem_resonantZeroQuadruples.mp hqRes)
    unfold quadrupleProduct
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_product.mpr ⟨hz.1, hz.2.1⟩
    · exact Finset.mem_product.mpr ⟨hz.2.2.1, hz.2.2.2.1⟩
  have hMaps : Set.MapsTo (mappedQuadruple representative)
      (Q : Set _) (U : Set _) := by
    intro q hq
    have hqFilter := Finset.mem_filter.mp hq
    have hqRes := hqFilter.1
    have hqColor := hqFilter.2
    have hz := mem_resonantZeroQuadruples.mp hqRes
    have hcoord (i : Fin 4) :
        color (complexQuadrupleCoord i q) = label i := by
      exact congrFun hqColor i
    have hcoordMem (i : Fin 4) :
        complexQuadrupleCoord i q ∈ zeroSet sigma T := by
      fin_cases i <;> simp only [complexQuadrupleCoord] <;> tauto
    have hW (i : Fin 4) :
        representative (complexQuadrupleCoord i q) ∈ W i := by
      apply Finset.mem_image.mpr
      exact ⟨complexQuadrupleCoord i q,
        Finset.mem_filter.mpr ⟨hcoordMem i, hcoord i⟩, rfl⟩
    have hDefect := shifted_zero_quadruple_defect_le hqRes representative
      (fun i => hShift _ (hcoordMem i))
    unfold U mixedApproximateAdditiveQuadruples
    apply Finset.mem_filter.mpr
    constructor
    · unfold quadrupleProductOf
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_product.mpr ⟨hW 0, hW 1⟩,
        Finset.mem_product.mpr ⟨hW 2, hW 3⟩⟩
    · simpa only [mappedQuadruple, complexQuadrupleCoord] using hDefect
  have hTransfer :
      (∑ q ∈ Q, zeroQuadrupleWeight q) <= L ^ 4 * U.card := by
    simpa only [weightedQuadruple, zeroQuadrupleWeight] using
      (weighted_quadruple_sum_le_fourth_power_mul_card
        (zeroSet sigma T) Q U zeroMultiplicity representative L
        hQ hMaps hLocal)
  refine ⟨label, ?_⟩
  dsimp only
  change zeroAdditiveEnergyCount sigma T <=
    (Fintype.card Kappa) ^ 4 * L ^ 4 *
      MixedApproxAddEnergy (1 + 4 * H) (W 0) (W 1) (W 2) (W 3)
  calc
    zeroAdditiveEnergyCount sigma T =
        ∑ q ∈ resonantZeroQuadruples sigma T,
          zeroQuadrupleWeight q := rfl
    _ <= (Fintype.card Kappa) ^ 4 *
        ∑ q ∈ Q, zeroQuadrupleWeight q := by
      simpa only [Q] using hColor
    _ <= (Fintype.card Kappa) ^ 4 * (L ^ 4 * U.card) :=
      Nat.mul_le_mul_left _ hTransfer
    _ = (Fintype.card Kappa) ^ 4 * L ^ 4 *
        MixedApproxAddEnergy (1 + 4 * H) (W 0) (W 1) (W 2) (W 3) := by
      simp only [U, MixedApproxAddEnergy, mul_assoc]

#print axioms shifted_zero_quadruple_defect_le
#print axioms exists_mixed_energy_color_classes

end

end GafniTao
