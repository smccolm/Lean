import Dubon2026.SourceJointChartRootFreeDenominators
import Dubon2026.SourceJointChartRootFactorNormalization
import Dubon2026.SourceJointChartIntegralCoordinates

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap.
Coordinates of an original chart function in the full residue chart basis
have a common good denominator and integral polynomial numerators. Native
fraction-ring clearing, direct residue-basis root cancellation, and the
already proved polynomial integrality criterion discharge these conditions. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_good_coordinate_denominator
    {L F : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    [Field F] [Algebra L F]
    {ι J : Type*} [Nonempty ι] [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (z : J → F) (hz : ∀ j i, z j ∈ (R i).integers)
    (hchart : ∀ j, z j ∈ originalChart L f)
    (huniq : ∀ q q' : J → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j) =
        ∑ j, aeval (rv R f hf) (q' j) * rv R (z j) (hz j) → q = q')
    (hgen : ∀ h ∈ ST R f, ∃ q : J → (ResidueField A)[X],
      h = ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j))
    (s : F) (hs : s ∈ originalChart L f) (w : J → F)
    (hw : ∀ j, (∀ i, w j ∈ (R i).integers) ∧
      w j ∈ IntermediateField.adjoin L ({f} : Set F))
    (hsum : s = ∑ j, w j * z j) :
    ∃ (t : L[X]) (p : J → L[X]), IsGood A t ∧
      (∀ j k, (p j).coeff k ∈ A) ∧ ∀ j, w j * aeval f t = aeval f (p j) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  have htrL : Transcendental L f :=
    transcendental_of_residue_transcendental (R i₀) ⟨f, hf i₀⟩ (htr i₀)
  let D := Algebra.adjoin L ({f} : Set F)
  let K := IntermediateField.adjoin L ({f} : Set F)
  let g : J → K := fun j => ⟨w j, (hw j).2⟩
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D) g
  choose a ha using hb
  obtain ⟨q, hq⟩ := Algebra.adjoin_eq_exists_aeval L f (b : D)
  choose P hP using fun j => Algebra.adjoin_eq_exists_aeval L f (a j)
  have hqeval : aeval f q ≠ 0 := by
    rw [hq]
    intro hzero
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext hzero)
  have hq0 : q ≠ 0 := fun hzero => hqeval (hzero ▸ map_zero _)
  have hrel : ∀ j, w j * aeval f q = aeval f (P j) := by
    intro j
    rw [hq, hP, mul_comm]
    exact (congrArg Subtype.val (ha j)).symm
  obtain ⟨T, Q, hT, hroots, hQ⟩ := exists_denominator_with_roots_outside
    R f hf htrL htr z hz hchart huniq hgen s hs w hsum q P hq0 hrel
  obtain ⟨u, t, hu, ht, hfac⟩ := exists_good_factor_of_roots_outside A hT hroots
  let p : J → L[X] := fun j => C u⁻¹ * Q j
  have hp : ∀ j, w j * aeval f t = aeval f (p j) := by
    intro j
    have h1 : aeval f T = algebraMap L F u * aeval f t := by
      rw [hfac, map_mul, aeval_C]
    have hU : algebraMap L F u⁻¹ * algebraMap L F u = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hu, map_one]
    rw [show p j = C u⁻¹ * Q j from rfl, map_mul, aeval_C, ← hQ j, h1]
    linear_combination (-(w j * aeval f t)) * hU
  refine ⟨t, p, ht, ?_, hp⟩
  intro j k
  apply coeff_mem_of_aeval_mem_integers (R i₀) ⟨f, hf i₀⟩ (htr i₀) (p j) ?_ k
  rw [← hp j]
  exact mul_mem ((hw j).1 i₀)
    ((aeval_mem_Sg R hf (show ∀ k, t.coeff k ∈ A from
      (show IsGoodAt A 0 t from ht).coeff_mem)).1 i₀)

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
