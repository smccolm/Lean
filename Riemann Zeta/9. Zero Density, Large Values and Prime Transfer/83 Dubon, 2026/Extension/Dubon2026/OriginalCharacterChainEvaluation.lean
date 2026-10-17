import Dubon2026.OriginalCharacterNormDetection
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Algebra.Module.CharacterModule

/-! # Character evaluation on the original low-degree chains

For DUB-17's finite class/Ext duality, evaluation of a character-valued
one-cochain is the literal sum over the original homology chain. The
cocycle condition is exactly annihilation of the second differential.
This supplies the chain-level compatibility needed before descending
to the actual first homology and cohomology groups.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {k G : Type} [CommRing k] [Group G]
variable (Q : Type) [AddCommGroup Q] [Module k Q] (M : Rep.{0} k G)

/-- The actual linear character representation with trivial target coefficient. -/
abbrev originalLinearCharacterRep : Rep.{0} k G :=
  (Rep.ihom M).obj (Rep.trivial k G Q)

/-- Evaluation of a character-valued one-cochain on a finitely supported original chain. -/
def originalCharacterChainEvaluation (c : G → M →ₗ[k] Q) : (G →₀ M) →ₗ[k] Q :=
  Finsupp.lsum k c

/-- Evaluation of a single chain is the corresponding original character value. -/
theorem originalCharacterChainEvaluation_single (c : G → M →ₗ[k] Q) (g : G) (x : M) :
    originalCharacterChainEvaluation Q M c (Finsupp.single g x) = c g x :=
  Finsupp.lsum_single k c g x

/-- Evaluation of a two-boundary has the original inhomogeneous cocycle expression. -/
theorem originalCharacterChainEvaluation_boundary_single
    (c : G → M →ₗ[k] Q) (g h : G) (x : M) :
    originalCharacterChainEvaluation Q M c
      (groupHomology.d₂₁ M (Finsupp.single (g, h) x)) =
        c h (M.ρ g⁻¹ x) - c (g * h) x + c g x := by
  calc
    _ = originalCharacterChainEvaluation Q M c
        (Finsupp.single h (M.ρ g⁻¹ x) - Finsupp.single (g * h) x +
          Finsupp.single g x) :=
      congrArg (originalCharacterChainEvaluation Q M c)
        (groupHomology.d₂₁_single (A := M) (g, h) x)
    _ = _ := by simp only [map_add, map_sub, originalCharacterChainEvaluation_single]

/-- The character-valued cocycle identity is exactly annihilation of original two-boundaries. -/
theorem originalCharacter_cocycle_iff_boundary_annihilation (c : G → M →ₗ[k] Q) :
    c ∈ groupCohomology.cocycles₁ (originalLinearCharacterRep Q M) ↔
      ∀ z : G × G →₀ M,
        originalCharacterChainEvaluation Q M c (groupHomology.d₂₁ M z) = 0 := by
  constructor
  · intro hc₀
    have hc := (groupCohomology.mem_cocycles₁_iff
      (A := originalLinearCharacterRep Q M) c).mp hc₀
    have he : originalCharacterChainEvaluation Q M c ∘ₗ (groupHomology.d₂₁ M).hom = 0 := by
      apply Finsupp.lhom_ext
      intro gh x
      change originalCharacterChainEvaluation Q M c
        (groupHomology.d₂₁ M (Finsupp.single gh x)) = 0
      rw [originalCharacterChainEvaluation_boundary_single]
      have h := congrArg (fun f : M →ₗ[k] Q => f x) (hc gh.1 gh.2)
      change c (gh.1 * gh.2) x = c gh.2 (M.ρ gh.1⁻¹ x) + c gh.1 x at h
      rw [h]
      abel
    intro z
    exact congrArg (fun f : (G × G →₀ M) →ₗ[k] Q => f z) he
  · intro hc
    apply (groupCohomology.mem_cocycles₁_iff
      (A := originalLinearCharacterRep Q M) c).mpr
    intro g h
    apply LinearMap.ext
    intro x
    have he := hc (Finsupp.single (g, h) x)
    rw [originalCharacterChainEvaluation_boundary_single] at he
    change c (g * h) x = c h (M.ρ g⁻¹ x) + c g x
    exact (sub_eq_zero.mp (by simpa only [sub_add_eq_add_sub] using he)).symm

/-- A character coboundary evaluates by the original first differential. -/
theorem originalCharacter_coboundary_evaluation (η : M →ₗ[k] Q) (z : G →₀ M) :
    originalCharacterChainEvaluation Q M
      (groupCohomology.d₀₁ (originalLinearCharacterRep Q M) η) z =
        η (groupHomology.d₁₀ M z) := by
  have he : originalCharacterChainEvaluation Q M
      (groupCohomology.d₀₁ (originalLinearCharacterRep Q M) η) =
        η ∘ₗ (groupHomology.d₁₀ M).hom := by
    apply Finsupp.lhom_ext
    intro g x
    change originalCharacterChainEvaluation Q M
      (groupCohomology.d₀₁ (originalLinearCharacterRep Q M) η) (Finsupp.single g x) =
        η (groupHomology.d₁₀ M (Finsupp.single g x))
    rw [originalCharacterChainEvaluation_single]
    change η (M.ρ g⁻¹ x) - η x = _
    exact (η.map_sub _ _).symm.trans
      (congrArg η (groupHomology.d₁₀_single (A := M) g x).symm)
  exact congrArg (fun f : (G →₀ M) →ₗ[k] Q => f z) he

end
end Dubon2026
