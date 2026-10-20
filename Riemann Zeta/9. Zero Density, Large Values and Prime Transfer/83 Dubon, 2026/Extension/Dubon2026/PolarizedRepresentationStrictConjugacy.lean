import Dubon2026.PolarizedCoefficientConjugacy
import Dubon2026.PolarizationCongruenceInvolution
import Dubon2026.PolarizedIdentityRestriction
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! Actual strict equivalence in the source polarized deformation problem:
conjugators are original general linear matrices reducing to the identity.
This relation is needed for DUB-17's full unframed trace-ring universality. -/

namespace Dubon2026
open Matrix

variable {G ι R k : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing R] [CommRing k]

/-- Strict equivalence of the whole original polarized representations,
through the source general linear identity component. -/
def PolarizedStrictlyConjugate (r : R →+* k)
    (σ τ : G →* PolarizedGaloisGroup ι R) : Prop :=
  ∃ U : GeneralLinearGroup ι R, GeneralLinearGroup.map r U = 1 ∧
    ∀ g, τ g = polarizedLinearInclusion U * σ g * (polarizedLinearInclusion U)⁻¹

/-- The original identity basis change gives polarized strict reflexivity. -/
theorem polarizedStrictlyConjugate_refl (r : R →+* k) (σ : G →* PolarizedGaloisGroup ι R) :
    PolarizedStrictlyConjugate r σ σ := by
  refine ⟨1, map_one _, ?_⟩
  intro g
  simp only [map_one, one_mul, inv_one, mul_one]

/-- Reversing a genuine strict basis change preserves the full polarized relation. -/
theorem polarizedStrictlyConjugate_symm (r : R →+* k) (σ τ : G →* PolarizedGaloisGroup ι R)
    (h : PolarizedStrictlyConjugate r σ τ) : PolarizedStrictlyConjugate r τ σ := by
  obtain ⟨U, hU, he⟩ := h
  refine ⟨U⁻¹, by rw [map_inv, hU, inv_one], ?_⟩
  intro g
  rw [he, map_inv]
  group

/-- Composing actual strict linear changes of basis gives polarized transitivity. -/
theorem polarizedStrictlyConjugate_trans (r : R →+* k)
    (σ τ υ : G →* PolarizedGaloisGroup ι R)
    (h₁ : PolarizedStrictlyConjugate r σ τ) (h₂ : PolarizedStrictlyConjugate r τ υ) :
    PolarizedStrictlyConjugate r σ υ := by
  obtain ⟨U, hU, he⟩ := h₁
  obtain ⟨V, hV, hf⟩ := h₂
  refine ⟨V * U, by rw [map_mul, hV, hU, one_mul], ?_⟩
  intro g
  rw [hf, he, map_mul]
  group

/-- Original coefficient change transports the entire strict polarized
conjugacy through its actual residue-compatible coefficient map. -/
theorem polarizedStrictlyConjugate_map {A : Type} [CommRing A]
    (rR : R →+* k) (rA : A →+* k) (f : R →+* A) (hr : rA.comp f = rR)
    (σ τ : G →* PolarizedGaloisGroup ι R) (h : PolarizedStrictlyConjugate rR σ τ) :
    PolarizedStrictlyConjugate rA ((polarizedCoefficientMap f).comp σ)
      ((polarizedCoefficientMap f).comp τ) := by
  obtain ⟨U, hU, he⟩ := h
  refine ⟨GeneralLinearGroup.map f U, ?_, ?_⟩
  · change GeneralLinearGroup.map (rA.comp f) U = 1
    rw [hr]
    exact hU
  · intro g
    have hmap := congrArg (polarizedCoefficientMap f) (he g)
    rw [map_mul, map_mul, map_inv, polarizedCoefficientMap_linear] at hmap
    exact hmap

/-- Restricting the original group preserves the same strict conjugator. -/
theorem polarizedStrictlyConjugate_comp {H : Type} [Group H]
    (r : R →+* k) (σ τ : G →* PolarizedGaloisGroup ι R)
    (h : PolarizedStrictlyConjugate r σ τ) (q : H →* G) :
    PolarizedStrictlyConjugate r (σ.comp q) (τ.comp q) := by
  obtain ⟨U, hU, he⟩ := h
  exact ⟨U, hU, fun g => he (q g)⟩

/-- On the original identity component, full polarized strict equivalence
implies ordinary strict equivalence of its actual matrix coordinates. -/
theorem polarizedStrictlyConjugate_identityMatrices (r : R →+* k)
    (σ τ : G →* PolarizedGaloisGroup ι R)
    (hσ : ∀ g, polarizedComponent (σ g) = 1) (hτ : ∀ g, polarizedComponent (τ g) = 1)
    (h : PolarizedStrictlyConjugate r σ τ) :
    MatrixStrictlyConjugate r (polarizedIdentityMatrices σ hσ) (polarizedIdentityMatrices τ hτ) := by
  obtain ⟨U, hU, he⟩ := h
  refine ⟨U, hU, ?_⟩
  intro g
  have hg : σ g = polarizedIdentityComponent (σ g).left := SemidirectProduct.ext rfl (hσ g)
  have ht := he g
  rw [hg, polarizedLinear_conjugate_identity] at ht
  exact congrArg (fun z : PolarizedGaloisGroup ι R => z.left.1) ht

end Dubon2026
