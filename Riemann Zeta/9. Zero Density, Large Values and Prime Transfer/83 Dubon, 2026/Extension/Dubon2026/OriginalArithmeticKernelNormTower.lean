import Dubon2026.OriginalNormRootsAboveStage
import Dubon2026.OriginalClassQuotientKernelNormRoots

/-! # Constructed arithmetic towers satisfy the normal-kernel norm condition

The actual primitive-root base and norm field construct two Galois stages
above the prescribed original stage. Literal restriction has a normal
kernel with order divisible by the coefficient prime. Reindexing the
proved norm roots gives invariant roots for the kernel's actual action
on the original outside-unit quotient. This discharges the field and
norm hypotheses in DUB-17's normal-subgroup relation-extension step.
The cohomological extension argument is not asserted here.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

/-- A constructed literal arithmetic tower has a normal restriction
kernel of prime-divisible order and invariant roots of its quotient norms.
No primitive root, norm field, class normalization or degree is supplied. -/
theorem originalUnramifiedStage_exists_kernel_norm_tower
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a) :
    ∃ E N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      P.val.toIntermediateField ≤ E.val.toIntermediateField ∧
      ∃ hEN : E.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra ℚ E.val := E.val.algebra'
        letI : Algebra ℚ N.val := N.val.algebra'
        letI : Algebra E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
        letI : Module E.val N.val := Algebra.toModule
        letI : SMul E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra.toSMul
        letI : IsScalarTower ℚ E.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
        letI : FiniteDimensional E.val N.val := FiniteDimensional.right ℚ E.val N.val
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        OriginalRestrictionKernelNormCondition ℚ E.val N.val T hT p := by
  obtain ⟨E, N, hPE, hEN, hdegree, hroot⟩ :=
    originalUnramifiedStage_exists_norm_root_tower Ω a ha P p hp2 hpa
  letI : Algebra ℚ E.val := E.val.algebra'
  letI : Algebra ℚ N.val := N.val.algebra'
  letI : Algebra E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra
  letI : Module E.val N.val := Algebra.toModule
  letI : SMul E.val N.val := (IntermediateField.inclusion hEN).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ E.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hEN)
  letI : FiniteDimensional E.val N.val := FiniteDimensional.right ℚ E.val N.val
  letI : IsGalois E.val N.val := IsGalois.tower_top_of_isGalois ℚ E.val N.val
  let S := originalExceptionalIntegerSupport E.val (algebraMap (𝓞 ℚ) (𝓞 E.val) a)
    (originalIntegerMap_ne_zero (L := E.val) a ha)
  let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
    (originalIntegerMap_ne_zero (L := N.val) a ha)
  let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
  let H := (AlgEquiv.restrictNormalHom E.val : Gal(N.val/ℚ) →* Gal(E.val/ℚ)).ker
  letI : Fintype H := Fintype.ofFinite H
  have hST (w : HeightOneSpectrum (𝓞 N.val)) :
      w ∈ T ↔ originalFinitePrimeBelow E.val N.val w ∈ S := by
    rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
    change algebraMap (𝓞 ℚ) (𝓞 N.val) a ∈ w.asIdeal ↔
      algebraMap (𝓞 E.val) (𝓞 N.val) (algebraMap (𝓞 ℚ) (𝓞 E.val) a) ∈ w.asIdeal
    rw [← IsScalarTower.algebraMap_apply (𝓞 ℚ) (𝓞 E.val) (𝓞 N.val)]
  refine ⟨E, N, hPE, hEN, ?_, ?_⟩
  · have hc : Nat.card H = Module.finrank E.val N.val :=
      (Nat.card_congr (galoisTowerKernelEquiv ℚ E.val N.val).toEquiv).trans
        (IsGalois.card_aut_eq_finrank E.val N.val)
    exact hc.symm ▸ hdegree
  · exact originalClassQuotient_kernel_invariant_norm_roots ℚ E.val N.val T hT p
      (hroot T (fun σ v => hT (σ.restrictScalars ℚ) v) hST)

end
end Dubon2026
