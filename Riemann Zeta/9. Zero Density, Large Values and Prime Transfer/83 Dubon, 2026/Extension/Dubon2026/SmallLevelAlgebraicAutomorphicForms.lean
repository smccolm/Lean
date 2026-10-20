import Dubon2026.SmallLevelDoubleCosetCoordinates
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Finiteness.Basic

/-! # Weighted algebraic automorphic forms at a small level

The functions and their right transformation law are those of CHT Section 3.3.
Evaluation on the actual double-coset representatives gives their coefficient
module. This supports the auxiliary Hecke-module obligation for DUB-17.
The arithmetic group, weight lattice, finite double cosets and smallness are
explicit inputs here; they are not constructed by this algebraic lemma.
-/

namespace Dubon2026

noncomputable section

variable {R G W : Type*} [CommRing R] [Group G] [AddCommGroup W] [Module R W]
variable (Γ U : Subgroup G) (ρ : Representation R U W)

/-- Actual left invariant functions with the inverse weight action on the right. -/
def algebraicAutomorphicForms : Submodule R (G → W) where
  carrier := {f | (∀ (γ : Γ) (g : G), f (γ * g) = f g) ∧
    ∀ (g : G) (u : U), f (g * u) = ρ u⁻¹ (f g)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro γ x
      simp only [Pi.add_apply, hf.1, hg.1]
    · intro x u
      simp only [Pi.add_apply, hf.2, hg.2, map_add]
  smul_mem' := by
    intro a f hf
    constructor
    · intro γ x
      simp only [Pi.smul_apply, hf.1]
    · intro x u
      simp only [Pi.smul_apply, hf.2, map_smul]

/-- Evaluation determines a weighted function from its actual right coordinates. -/
theorem algebraicAutomorphicForms_coordinate (f : algebraicAutomorphicForms Γ U ρ)
    (g : G) : f.val g = ρ (smallLevelRightFactor Γ U g)⁻¹
      (f.val (DoubleCoset.mk Γ U g : DoubleCoset.Quotient (G := G) Γ U).out) := by
  obtain ⟨γ, he⟩ := smallLevelRightFactor_spec Γ U g
  calc
    f.val g = f.val (γ * (DoubleCoset.mk Γ U g).out * smallLevelRightFactor Γ U g) :=
      congrArg f.val he
    _ = _ := by rw [f.property.2, f.property.1]

/-- Smallness gives the actual evaluation isomorphism, without an assumed basis of forms. -/
def smallLevelAutomorphicEvaluation
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1) :
    algebraicAutomorphicForms Γ U ρ ≃ₗ[R] (DoubleCoset.Quotient (G := G) Γ U → W) where
  toFun f q := f.val q.out
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun g => ρ (smallLevelRightFactor Γ U g)⁻¹
      (w (DoubleCoset.mk Γ U g)), by
    constructor
    · intro γ g
      simp only [smallLevelRightFactor_left Γ U hsmall, smallLevel_doubleCoset_left]
    · intro g u
      simp only [smallLevelRightFactor_right Γ U hsmall, smallLevel_doubleCoset_right,
        mul_inv_rev, map_mul, Module.End.mul_apply]⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    exact (algebraicAutomorphicForms_coordinate Γ U ρ f g).symm
  right_inv w := by
    funext q
    simp only [smallLevelRightFactor_out Γ U hsmall, inv_one, map_one,
      Module.End.one_apply, DoubleCoset.out_eq']

/-- Finite actual double cosets and a finite coefficient module give finiteness of forms. -/
theorem smallLevelAutomorphic_finite
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    [Finite (DoubleCoset.Quotient (G := G) Γ U)] [Module.Finite R W] :
    Module.Finite R (algebraicAutomorphicForms Γ U ρ) :=
  Module.Finite.equiv (smallLevelAutomorphicEvaluation Γ U ρ hsmall).symm

/-- Finite actual double cosets and a free weight lattice give freeness of forms. -/
theorem smallLevelAutomorphic_free
    (hsmall : ∀ (s : G) (u : U), s * u * s⁻¹ ∈ Γ → u = 1)
    [Finite (DoubleCoset.Quotient (G := G) Γ U)] [Module.Free R W] :
    Module.Free R (algebraicAutomorphicForms Γ U ρ) :=
  Module.Free.of_equiv (smallLevelAutomorphicEvaluation Γ U ρ hsmall).symm

end
end Dubon2026
