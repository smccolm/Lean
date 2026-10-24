import Dubon2026.SourceJointChartLiftedPolynomialBasis
import Dubon2026.SourceJointReductionCoordinateBasis

/-! DUB-17/18 -> Kummer power lifting -> finite localized overlap -> lifted
chart basis. Unique polynomial residue coordinates give independent power
multiples by native scalar-tower independence. The existing joint-residue
lifting and fraction-ring theorem then give an original coordinate-field
independent family. This avoids repeating coefficient normalization. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial IsLocalRing JointChartAssembly

theorem linearIndependent_powers_of_polynomial_unique
    {k E J : Type*} [Field k] [CommRing E] [Algebra k E] [Fintype J]
    (x : E) (z : J → E)
    (huniq : ∀ q q' : J → k[X],
      ∑ j, aeval x (q j) * z j = ∑ j, aeval x (q' j) * z j → q = q') :
    LinearIndependent k (fun p : ℕ × J => x ^ p.1 * z p.2) := by
  letI : Module k[X] E := Module.compHom E (aeval x).toRingHom
  letI : IsScalarTower k k[X] E := ⟨fun a p y => by
      change aeval x (a • p) * y = a • (aeval x p * y)
      rw [map_smul, smul_mul_assoc]⟩
  have hz : LinearIndependent k[X] z := by
    rw [Fintype.linearIndependent_iff]
    intro q hq j
    change ∑ j, aeval x (q j) * z j = 0 at hq
    have he := huniq q 0 (by simpa using hq)
    exact congrFun he j
  have hpow : LinearIndependent k (fun n : ℕ => (X : k[X]) ^ n) := by
    simpa only [Polynomial.coe_basisMonomials, Polynomial.monomial_one_right_eq_X_pow]
      using (Polynomial.basisMonomials k).linearIndependent
  have he : (fun p : ℕ × J => (X : k[X]) ^ p.1 • z p.2) =
      (fun p : ℕ × J => x ^ p.1 * z p.2) := by
    funext p
    change aeval x (X ^ p.1) * z p.2 = _
    rw [map_pow, aeval_X]
  rw [← he]
  exact linearIndependent_smul hpow hz

theorem linearIndependent_lifted_chart_basis
    {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
    {ι J : Type*} [Fintype J] {Fb : ι → Type*} [∀ i, Field (Fb i)]
    [∀ i, Algebra (ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (z : J → F) (hz : ∀ j i, z j ∈ (R i).integers)
    (huniq : ∀ q q' : J → (ResidueField A)[X],
      ∑ j, aeval (rv R f hf) (q j) * rv R (z j) (hz j) =
        ∑ j, aeval (rv R f hf) (q' j) * rv R (z j) (hz j) → q = q') :
    LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z := by
  let v : ℕ × J → F := fun p => f ^ p.1 * z p.2
  have hv : ∀ p i, v p ∈ (R i).integers :=
    fun p i => mul_mem (pow_mem (hf i) _) (hz p.2 i)
  have hr : Joint.jointRes R v hv =
      (fun p : ℕ × J => rv R f hf ^ p.1 * rv R (z p.2) (hz p.2)) := by
    funext p i
    change (R i).residue (⟨f, hf i⟩ ^ p.1 * ⟨z p.2, hz p.2 i⟩) = _
    rw [map_mul, map_pow]
    rfl
  apply Joint.linearIndependent_adjoinField_of_powers f z
  apply Joint.linearIndependent_coe_joint R v hv
  rw [hr]
  exact linearIndependent_powers_of_polynomial_unique (rv R f hf)
    (fun j => rv R (z j) (hz j)) huniq

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
