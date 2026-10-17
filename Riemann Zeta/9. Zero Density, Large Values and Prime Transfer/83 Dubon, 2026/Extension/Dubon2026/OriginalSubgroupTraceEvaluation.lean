import Dubon2026.OriginalFundamentalSubgroupNormHomology
import Dubon2026.OriginalTrivialSourceInvariants

/-! # Evaluation retains the literal relative trace

Literal evaluation at one identifies subgroup invariants of the
trivial-source internal Hom with actual coefficient invariants. Their
quotient traces agree with the existing invariant-to-morphism comparison. This
connects DUB-17's proved homology image comparison to the arithmetic norm.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable {G : Type} [Group G] (C : Rep.{0} ℤ G) (S : Subgroup G) [S.Normal]

/-- Literal evaluation at one identifies the subgroup-invariant internal
Hom with its coefficient, using the pinned singleton map and scalar linearity. -/
def originalSubgroupTrivialSourceInvariantEquiv :
    ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj C).quotientToInvariants S ≃ₗ[ℤ]
      C.quotientToInvariants S where
  toFun x := ⟨(show ℤ →ₗ[ℤ] C from x.val) 1, fun s =>
    congrArg (fun t : ℤ →ₗ[ℤ] C => t 1) (x.property s)⟩
  invFun x := ⟨LinearMap.toSpanSingleton ℤ C x.val, fun s => by
    apply LinearMap.ext
    intro n
    change C.ρ s.val (C.hV2.smul n x.val) = C.hV2.smul n x.val
    exact ((C.ρ s.val).map_smul n x.val).trans
      (congrArg (C.hV2.smul n) (x.property s))⟩
  left_inv x := by
    apply Subtype.ext
    apply LinearMap.ext
    intro n
    change (LinearMap.toSpanSingleton ℤ C ((show ℤ →ₗ[ℤ] C from x.val) 1)) n =
      (show ℤ →ₗ[ℤ] C from x.val) n
    simpa only [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] using
      ((show ℤ →ₗ[ℤ] C from x.val).map_smul n (1 : ℤ)).symm
  right_inv x := Subtype.ext (LinearMap.toSpanSingleton_apply_one ℤ C x.val)
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The actual subgroup-invariant comparison is evaluation at one. -/
theorem originalSubgroupTrivialSourceInvariantEquiv_apply
    (x : ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj C).quotientToInvariants S) :
    (originalSubgroupTrivialSourceInvariantEquiv C S x).val =
      (show Rep.trivial ℤ G ℤ →ₗ[ℤ] C from x.val) 1 := rfl

/-- Evaluation at one respects the actual quotient action on subgroup
invariants of the trivial integral internal Hom. -/
def originalSubgroupTrivialSourceInvariantIso :
    ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj C).quotientToInvariants S ≅
      C.quotientToInvariants S :=
  Rep.mkIso {
    __ := originalSubgroupTrivialSourceInvariantEquiv C S
    isIntertwining' q := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change (originalSubgroupTrivialSourceInvariantEquiv C S
        ((((Rep.ihom (Rep.trivial ℤ G ℤ)).obj C).quotientToInvariants S).ρ q x)).val =
          ((C.quotientToInvariants S).ρ q (originalSubgroupTrivialSourceInvariantEquiv C S x)).val
      rw [originalSubgroupTrivialSourceInvariantEquiv_apply,
        originalQuotientInvariant_action_out, originalQuotientInvariant_action_out,
        originalSubgroupTrivialSourceInvariantEquiv_apply]
      rfl }

variable [Fintype (G ⧸ S)]

/-- The literal trace morphism evaluates to the literal quotient norm
of the original subgroup-invariant coefficient. -/
theorem originalSubgroupTraceMorphism_eval
    (x : ((Rep.ihom (Rep.trivial ℤ G ℤ)).obj C).quotientToInvariants S) :
    (originalTrivialSourceInvariantEquiv C
      (originalFundamentalSubgroupTraceMorphism (Rep.trivial ℤ G ℤ) C S x)).val =
      ((C.quotientToInvariants S).ρ.norm
        (originalSubgroupTrivialSourceInvariantEquiv C S x)).val := by
  exact congrArg Subtype.val (originalCoefficientMorphism_norm
    (originalSubgroupTrivialSourceInvariantIso C S).hom x)

end
end Dubon2026
