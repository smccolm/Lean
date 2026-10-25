import Mathlib.Algebra.Module.Submodule.Equiv

/-! DUB-17/18 -> primitive determinant -> identify the actual projector
image. Restrict the existing ambient coordinate equivalence using its
proved operator intertwining, with no dimension or image hypothesis. -/
namespace Dubon2026
noncomputable section
variable {E V W : Type*} [Field E]
variable [AddCommGroup V] [Module E V] [AddCommGroup W] [Module E W]

/-- An intertwining ambient equivalence identifies the literal operator images. -/
def intertwinedRangeEquiv (e : V ≃ₗ[E] W) (Q : Module.End E V) (R : Module.End E W)
    (h : ∀ v, e (Q v) = R (e v)) : Q.range ≃ₗ[E] R.range :=
  e.ofSubmodules Q.range R.range (by
    rw [← LinearMap.range_comp]
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨e v, (h v).symm⟩
    · rintro ⟨w, rfl⟩
      exact ⟨e.symm w, (h (e.symm w)).trans (congrArg R (e.apply_symm_apply w))⟩)

theorem intertwinedRangeEquiv_apply (e : V ≃ₗ[E] W) (Q : Module.End E V) (R : Module.End E W)
    (h : ∀ v, e (Q v) = R (e v)) (x : Q.range) :
    (intertwinedRangeEquiv e Q R h x).val = e x.val := rfl

end
end Dubon2026
