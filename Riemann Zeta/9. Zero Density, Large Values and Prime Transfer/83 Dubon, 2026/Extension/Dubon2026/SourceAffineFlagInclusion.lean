import Dubon2026.SourceAffineFlagHeckeQuotient
import Dubon2026.SourceAffineFunctionInvariants

/-! The actual flag inclusion needed to test survival of the lifted eigenclass.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> survival in the whole affine function representation or its
Eisenstein exception. The inclusion and all good-prime comparisons are
native coefficient and cohomology maps. At the terminal flag it is an isomorphism.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p]
    (hpQ : p ∣ Q) (j : Fin p)

/-- Inclusion of the actual function flag into the original full coefficient representation. -/
def sourceAffineFlagInclusion :
    sourceAffineFlagRep F p Q hpQ j ⟶ sourceAffineFunctionRep p Q F hpQ :=
  Rep.ofHom {
    toLinearMap := (sourceFiniteFunctionFlag F p j.val).subtype
    isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }

/-- The actual flag coefficient inclusion is injective. -/
theorem sourceAffineFlagInclusion_injective :
    Function.Injective (sourceAffineFlagInclusion F p Q hpQ j) := Subtype.val_injective

/-- The range of the original coefficient inclusion is exactly the actual monomial flag. -/
theorem sourceAffineFlagInclusion_range :
    LinearMap.range (sourceAffineFlagInclusion F p Q hpQ j).hom.toLinearMap =
      sourceFiniteFunctionFlag F p j.val := Submodule.range_subtype _

/-- Inclusion of the original flag induces its native H1 comparison map. -/
def sourceAffineFlagInclusionH1 :
    groupCohomology.H1 (sourceAffineFlagRep F p Q hpQ j) →ₗ[F]
      groupCohomology.H1 (sourceAffineFunctionRep p Q F hpQ) :=
  ((groupCohomology.functor F (Gamma0 Q) 1).map
    (sourceAffineFlagInclusion F p Q hpQ j)).hom

private local instance affineInclusionPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- The native inclusion on H1 preserves every original good-prime Hecke eigenvalue. -/
theorem sourceAffineFlagInclusionH1_hecke (ell : sourceBinaryHeckePrime Q)
    (x : groupCohomology.H1 (sourceAffineFlagRep F p Q hpQ j)) :
    sourceAffineFlagInclusionH1 F p Q hpQ j (sourceAffineFlagHeckeOperators F p Q hpQ j ell x) =
      sourceAffineFunctionHeckeOperators F p Q hpQ ell (sourceAffineFlagInclusionH1 F p Q hpQ j x) :=
  sourcePrimeHeckeH1_naturality ell.property.1 _ _ (sourceAffineFlagInclusion F p Q hpQ j)
    (sourceAffineFlagDiagonal F p j ell.val) (sourceAffineFunctionDiagonal p F ell.val)
    (sourceAffineFlagDiagonal_intertwine F p Q hpQ j ell)
    (sourceAffineFunctionDiagonal_intertwine F p Q hpQ ell)
    (LinearMap.ext fun _ => rfl) x

/-- At the terminal actual flag, coefficient inclusion is an isomorphism,
so its native H1 map is injective without any cohomological vanishing assumption. -/
theorem sourceAffineFlagInclusionH1_top_injective (hj : p - 1 ≤ j.val) :
    Function.Injective (sourceAffineFlagInclusionH1 F p Q hpQ j) := by
  letI : IsIso (sourceAffineFlagInclusion F p Q hpQ j) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨sourceAffineFlagInclusion_injective F p Q hpQ j, fun f => by
        refine ⟨⟨f, ?_⟩, rfl⟩
        change f ∈ sourceFiniteFunctionFlag F p j.val
        rw [sourceFiniteFunctionFlag_eq_top F p hj]
        trivial⟩
  exact (ConcreteCategory.bijective_of_isIso
    ((groupCohomology.functor F (Gamma0 Q) 1).map
      (sourceAffineFlagInclusion F p Q hpQ j))).injective

end
end Dubon2026
