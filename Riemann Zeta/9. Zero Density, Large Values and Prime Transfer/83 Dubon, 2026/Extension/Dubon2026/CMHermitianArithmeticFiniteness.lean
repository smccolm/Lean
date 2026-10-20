import Dubon2026.CMHermitianUnitaryGroup
import Dubon2026.PositiveHermitianUnitaryCompact
import Dubon2026.NumberFieldAdelicCompactFiniteness

/-! # Finite arithmetic intersections for the specified definite CM unitary form

This removes the identity-form restriction from the DUB-17 stabilizer
argument. All original complex embeddings must make the supplied form
positive definite. Finite local compactness then gives finiteness of the
original arithmetic intersection, using the actual principal embedding.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField ComplexOrder

variable {K ι : Type*} [Field K] [NumberField K] [IsCMField K]
variable [Fintype ι] [DecidableEq ι]

/-- A compact finite-adelic matrix set meets the original definite Hermitian unitary group finitely. -/
theorem cmHermitian_compactArithmetic_finite
    (H : Matrix ι ι K) (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (C : Set (Matrix ι ι (FiniteAdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    {U : cmHermitianUnitaryGroup H |
      (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix U.val.val ∈ C}.Finite := by
  let D : Set (Matrix ι ι ℂ) := ⋃ φ : K →+* ℂ,
    {M | star M * φ.mapMatrix H * M = φ.mapMatrix H}
  have hD : IsCompact D := isCompact_iUnion fun φ =>
    positiveHermitianUnitary_isCompact (φ.mapMatrix H) (hH φ)
  let S (i j : ι) : Set K := {x |
    algebraMap K (FiniteAdeleRing (𝓞 K) K) x ∈ (fun M => M i j) '' C ∧
      ∀ φ : K →+* ℂ, φ x ∈ (fun M => M i j) '' D}
  have hS (i j : ι) : (S i j).Finite := by
    obtain ⟨B, hB⟩ := (hD.image
      ((continuous_apply j).comp (continuous_apply i))).isBounded.exists_norm_le
    apply (numberField_compactFinite_boundedInfinite_finite K ((fun M => M i j) '' C)
      (hC.image ((continuous_apply j).comp (continuous_apply i))) B).subset
    intro x hx
    refine ⟨hx.1, fun v => ?_⟩
    rw [← v.norm_embedding_eq]
    exact hB _ (hx.2 v.embedding)
  letI (i j : ι) : Finite (S i j) := (hS i j).to_subtype
  let T : Set (cmHermitianUnitaryGroup H) := {U |
    (algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix U.val.val ∈ C}
  let F : T → (i j : ι) → S i j := fun U i j => ⟨U.val.val.val i j, by
    constructor
    · exact ⟨(algebraMap K (FiniteAdeleRing (𝓞 K) K)).mapMatrix U.val.val.val,
        U.property, rfl⟩
    · intro φ
      refine ⟨φ.mapMatrix U.val.val.val, ?_, rfl⟩
      exact Set.mem_iUnion.mpr ⟨φ, cmHermitianUnitaryGroup_complex_preserves H U.val φ⟩⟩
  have hF : Function.Injective F := by
    intro U V h
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact congrArg (fun f : (i j : ι) → S i j => (f i j).val) h
  letI : Finite T := Finite.of_injective F hF
  exact Set.toFinite T

end
end Dubon2026
