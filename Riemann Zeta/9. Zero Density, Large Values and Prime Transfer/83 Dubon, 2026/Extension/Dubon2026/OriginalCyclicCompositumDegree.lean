import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Coset.Card

/-! # Cyclic composita over the actual finite base

Reuse the pinned compositum Galois theorem and injective restriction map.
The degree of the compositum over its base divides the original cyclic
degree. This supplies the relative cyclicity and prime-power degree
conditions needed by DUB-17's auxiliary field construction.
-/
namespace Dubon2026
noncomputable section
open IntermediateField
attribute [-instance] SubfieldClass.instSMulRat

variable (U : Type) [Field U] [Algebra ℚ U]
  (K D : IntermediateField ℚ U) [FiniteDimensional ℚ K] [FiniteDimensional ℚ D]
  [IsGalois ℚ D] [IsCyclic Gal(D/ℚ)]

/-- The literal compositum with a finite cyclic rational extension is cyclic Galois over the original finite base, and its relative degree divides the original cyclic degree. -/
theorem originalCyclicCompositum_galois_cyclic_degree_dvd :
    let N := K ⊔ D
    letI : Algebra K N := (IntermediateField.inclusion (show K ≤ N from le_sup_left)).toAlgebra
    letI : Module K N := Algebra.toModule
    IsGalois K N ∧ IsCyclic Gal(N/K) ∧ Module.finrank K N ∣ Module.finrank ℚ D := by
  let N := K ⊔ D
  letI : Algebra K N := (IntermediateField.inclusion (show K ≤ N from le_sup_left)).toAlgebra
  letI : Module K N := Algebra.toModule
  letI : IsScalarTower ℚ K N := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K N := FiniteDimensional.right ℚ K N
  let D' : IntermediateField ℚ N := D.restrict le_sup_right
  let K' : IntermediateField ℚ N := K.restrict le_sup_left
  let eD := IntermediateField.restrict_algEquiv (show D ≤ N from le_sup_right)
  let eK := IntermediateField.restrict_algEquiv (show K ≤ N from le_sup_left)
  have hs : D' ⊔ K' = ⊤ := by
    rw [← lift_inj, lift_top, lift_sup, lift_restrict le_sup_right, lift_restrict le_sup_left]
    exact sup_comm D K
  letI : IsGalois ℚ D' := IsGalois.of_algEquiv eD
  letI : IsCyclic Gal(D'/ℚ) := eD.autCongr.isCyclic.mp inferInstance
  letI : IsGalois K' N := IsGalois.sup_right D' K' hs
  have hg : IsGalois K N := IsGalois.of_equiv_equiv
    (F := K') (E := N) (f := eK.symm.toRingEquiv) (g := RingEquiv.refl N) (by
      apply RingHom.ext
      intro x
      exact congrArg (fun t : K' => (t : N)) (eK.apply_symm_apply x))
  letI := hg
  let δ : Gal(N/K) →* Gal(N/K') := {
    toFun σ := {
      __ := σ.toRingEquiv
      commutes' x := by
        obtain ⟨y, rfl⟩ := eK.surjective x
        exact σ.commutes y }
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hiδ : Function.Injective δ := by
    intro σ τ h
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun f : Gal(N/K') => f x) h
  let φ := (IntermediateField.restrictRestrictAlgEquivMapHom ℚ D' K' N).comp δ
  have hi : Function.Injective φ :=
    (IntermediateField.restrictRestrictAlgEquivMapHom_injective D' K' hs).comp hiδ
  have hc : IsCyclic Gal(N/K) := isCyclic_of_injective φ hi
  have hd := Subgroup.card_dvd_of_injective φ hi
  rw [IsGalois.card_aut_eq_finrank K N, IsGalois.card_aut_eq_finrank ℚ D',
    ← eD.toLinearEquiv.finrank_eq] at hd
  exact ⟨hg, hc, hd⟩

end
end Dubon2026
