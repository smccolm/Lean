import Dubon2026.LocalFieldFiniteCyclicReciprocityNorm
import Dubon2026.LocalFieldFrobeniusCharacterImage
import Dubon2026.LocalFieldUniformizerOrder

/-! # Normed original uniformizers give restricted arithmetic Frobenius

Combine the original field-norm compatibility with the original positive
unramified Frobenius normalization. The arithmetic-Frobenius image of a
uniformizer norm is then derived. This is the application bridge needed for
the actual changed-uniformizer auxiliary field in DUB-17's still-open
ramified cyclotomic formula, principal product and arithmetic sum-zero.
The auxiliary field, its unramified compositum and the normed element remain
genuine field-construction obligations; they are not manufactured here.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]
  (L : FiniteGaloisIntermediateField K Ω) (M : FiniteGaloisIntermediateField E Ω)
  [IsCyclic Gal(L/K)]
  [Algebra K M] [IsScalarTower K E M]
  [Algebra L M] [IsScalarTower K L M] [IsScalarTower L M Ω]

variable [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]

attribute [local instance] IsCyclic.commGroup

/-- Cyclicity comes from the actual unramified local extension over E. -/
local instance normedUniformizerRelativeCyclic : IsCyclic Gal(M/E) :=
  (unramifiedLocalFieldResidueGaloisEquiv E M).isCyclic.mpr inferInstance

/-- The original reciprocity image of an actual norm is the corresponding power of the literal restricted arithmetic Frobenius of an unramified auxiliary extension. -/
theorem localFieldFiniteCyclicReciprocity_norm_frobenius (u : Eˣ) :
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (Units.map (Algebra.norm K (S := E)) u))).toMul =
      galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M) ^
        localFieldUnitOrder E (Additive.ofMul u) := by
  have hn := localFieldFiniteCyclicReciprocity_norm K Ω E L M u
  have hf := localFieldFiniteCyclicReciprocity_frobenius_image E Ω M
    (galoisBaseChangeRestriction K E L M) u
  exact hn.symm.trans hf

/-- An actual original auxiliary integer uniformizer has order one, so its field norm maps to the literal restricted positive arithmetic Frobenius. -/
theorem localFieldFiniteCyclicReciprocity_norm_uniformizer
    (θ : 𝒪[E]) (hθ : Irreducible θ) :
    (localFieldFiniteCyclicReciprocity K Ω L
      (Additive.ofMul (Units.map (Algebra.norm K (S := E))
        (Units.mk0 (algebraMap 𝒪[E] E θ) (by intro h; exact hθ.ne_zero (Subtype.ext h)))))).toMul =
      galoisBaseChangeRestriction K E L M (localFieldArithmeticFrobenius E M) := by
  have h := localFieldFiniteCyclicReciprocity_norm_frobenius K Ω E L M
    (Units.mk0 (algebraMap 𝒪[E] E θ) (by intro h; exact hθ.ne_zero (Subtype.ext h)))
  rw [localFieldUnitOrder_irreducible E θ hθ, zpow_one] at h
  exact h

end
end Dubon2026
