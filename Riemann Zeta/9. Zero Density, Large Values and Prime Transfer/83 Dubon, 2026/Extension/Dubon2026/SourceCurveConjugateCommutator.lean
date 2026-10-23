import Dubon2026.SourceCurveFiniteRankTrace

/-! Transport the two exact multiplication-operator identities to their
commutator. This small linear-algebra step lets the actual completed
integral-basis proof use matrix trace without expanding its field towers
during rewriting; it serves DUB-17/18 local residue/field-trace compatibility. -/

namespace Dubon2026.SourceCurve.ResidueTrace

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- Two operator conjugacy identities imply the exact commutator conjugacy. -/
theorem conjugate_commutator_eq (e : M ≃ₗ[K] N)
    (A B : M →ₗ[K] M) (C D : N →ₗ[K] N)
    (hA : e.conj A = C) (hB : e.conj B = D) :
    e.conj (A ∘ₗ B - B ∘ₗ A) = C ∘ₗ D - D ∘ₗ C := by
  rw [map_sub e.conj (A ∘ₗ B) (B ∘ₗ A), LinearEquiv.conj_comp,
    LinearEquiv.conj_comp, hA, hB]

end Dubon2026.SourceCurve.ResidueTrace
