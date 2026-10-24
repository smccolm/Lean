import Dubon2026.SourceJointChartIntegralPolynomialCoefficients

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap. Every
jointly integral function has integral rational-coordinate coefficients
in the full lifted chart basis. Native fraction-ring denominator clearing,
the existing simultaneous unit normalizer, and polynomial coefficient
integrality discharge the coordinate integrality requirement. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_integral_coords_of_full_chart_basis
    {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    {n : ℕ} (z : Fin n → F) (hz : ∀ j i, z j ∈ (R i).integers)
    (huniq : ∀ q q' : Fin n → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j) =
        ∑ j, aeval (rv R f hf) (q' j) * rv R (z j) (hz j) → q = q')
    (hd : Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F = n)
    (u : F) (hu : ∀ i, u ∈ (R i).integers) :
    ∃ w : Fin n → F,
      (∀ j, (∀ i, w j ∈ (R i).integers) ∧ w j ∈ IntermediateField.adjoin L ({f} : Set F)) ∧
      u = ∑ j, w j * z j := by
  classical
  let D := Algebra.adjoin L ({f} : Set F)
  let K := IntermediateField.adjoin L ({f} : Set F)
  let B : Module.Basis (Fin n) K F := basisOfLinearIndependentOfCardEqFinrank' z
    (linearIndependent_lifted_chart_basis R f hf z hz huniq) (by rw [Fintype.card_fin, hd])
  let g : Fin n → K := fun j => B.repr u j
  have hsum : u = ∑ j, (g j : F) * z j := by
    conv_lhs => rw [← B.sum_repr u]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D) g
  choose a ha using hb
  obtain ⟨q, hq⟩ := Algebra.adjoin_eq_exists_aeval L f (b : D)
  choose p hp using fun j => Algebra.adjoin_eq_exists_aeval L f (a j)
  have hqeval : aeval f q ≠ 0 := by
    rw [hq]
    intro hzero
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext hzero)
  have hq0 : q ≠ 0 := fun hzero => hqeval (hzero ▸ map_zero _)
  have hpg : ∀ j, aeval f q * (g j : F) = aeval f (p j) := by
    intro j
    rw [hq, hp]
    exact (congrArg Subtype.val (ha j)).symm
  obtain ⟨U, hU, hUr, c, hc, hUq⟩ := Joint.exists_joint_normalize_aeval R f hf htr q hq0
  let P : Fin n → L[X] := fun j => C c⁻¹ * p j
  have hrel : ∀ j, U * (g j : F) = aeval f (P j) := by
    intro j
    rw [hUq, mul_assoc, hpg j]
    simp only [P, map_mul, aeval_C]
  have hU0 : U ≠ 0 := by
    rw [hUq]
    exact mul_ne_zero (by simpa only [map_zero] using
      (algebraMap L F).injective.ne (inv_ne_zero hc)) hqeval
  have hexp : U * u = ∑ j, aeval f (P j) * z j := by
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hrel j]
  have hP := coeff_mem_of_polynomial_sum_integral R f hf z hz huniq P
    (fun i => by rw [← hexp]; exact mul_mem (hU i) (hu i))
  have hUi : ∀ i, U⁻¹ ∈ (R i).integers := inv_mem_integers hUr
  refine ⟨fun j => (g j : F), fun j => ⟨?_, (g j).2⟩, hsum⟩
  have hg : (g j : F) = U⁻¹ * aeval f (P j) := by
    rw [← hrel j, ← mul_assoc, inv_mul_cancel₀ hU0, one_mul]
  intro i
  change (g j : F) ∈ (R i).integers
  rw [hg]
  exact mul_mem (hUi i) ((aeval_mem_Sg R hf (hP j)).1 i)

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
