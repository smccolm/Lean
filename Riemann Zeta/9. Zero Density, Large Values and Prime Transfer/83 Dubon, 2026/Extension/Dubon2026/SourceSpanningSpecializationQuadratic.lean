import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Span.Defs

/-! DUB-17/18 -> specialization of the actual original Tate quadratic
identity. Isolate the finite linear-algebra calculation from the large
original Tate type. This lemma is consumed by the original specialization
theorem; the two intertwining identities and the upstream endomorphism
identity remain explicit until that consumer supplies them. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {L E V : Type*} [Field L] [Field E] [Algebra L E]
variable [AddCommGroup V] [Module L V]

theorem quadratic_identity_on_spanning_specialization
    (π : V →ₗ[L] (Fin 2 → E)) (M : Matrix (Fin 2) (Fin 2) E)
    (S T : Module.End L V) (a : E) (p : ℕ)
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hact : ∀ x, M *ᵥ π x = π (S x))
    (hhecke : ∀ x, π (T x) = a • π x)
    (hquad : T * S = S * S + p • 1) :
    M * M + p • (1 : Matrix (Fin 2) (Fin 2) E) = a • M := by
  have hi (x : V) : a • (M *ᵥ π x) = M *ᵥ (M *ᵥ π x) + p • π x := by
    rw [hact, hact]
    have h := congrArg π (LinearMap.congr_fun hquad x)
    change π (T (S x)) = π (S (S x) + p • x) at h
    rw [hhecke, map_add, map_nsmul] at h
    exact h
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on_range hspan
  intro x
  change (M * M + p • (1 : Matrix (Fin 2) (Fin 2) E)) *ᵥ π x = (a • M) *ᵥ π x
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec]
  exact (hi x).symm

end
end Dubon2026
