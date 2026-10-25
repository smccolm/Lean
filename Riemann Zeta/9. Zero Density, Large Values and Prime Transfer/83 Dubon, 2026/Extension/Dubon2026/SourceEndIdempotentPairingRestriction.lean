import Dubon2026.SourceIdempotentBilinearRestriction

/-! DUB-17/18 -> original primitive Tate pairing. A ring evaluation maps
an arithmetic idempotent to an endomorphism idempotent; if its evaluated
operator is self-adjoint, the actual restricted pairing stays injective. -/
namespace Dubon2026
noncomputable section

theorem mapped_idempotent_pairing_restriction
    {R A V W : Type*} [CommRing R] [Ring A]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (B : V →ₗ[R] V →ₗ[R] W) (hB : Function.Injective B)
    (φ : A →+* Module.End R V) (e : A) (he : IsIdempotentElem e)
    (hBe : B.IsSelfAdjoint (φ e)) :
    IsIdempotentElem (φ e) ∧ B.IsSelfAdjoint (φ e) ∧
      Function.Injective (B.compl₁₂ (φ e).range.subtype (φ e).range.subtype) :=
  ⟨he.map φ, hBe, idempotent_bilinear_restriction_injective B hB (φ e) (he.map φ) hBe⟩

end
end Dubon2026
