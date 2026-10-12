import Mathlib.RepresentationTheory.Coinduced

/-! # Original coefficients coinduced from the actual trivial subgroup -/

namespace Dubon2026
noncomputable section

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G)

/-- The actual coinduction of the original coefficient module restricted
to the original trivial subgroup. -/
abbrev originalCoinducedFunctionRep : Rep k G :=
  Rep.coind (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A)

/-- Every original coefficient-valued function satisfies the genuine
equivariance condition for the trivial subgroup. -/
def originalCoinducedFunction (f : G → A) : originalCoinducedFunctionRep A :=
  ⟨f, by
    intro h g
    have hh : (h : G) = 1 := h.property
    change f ((h : G) * g) = A.ρ (h : G) (f g)
    rw [hh, one_mul, map_one, Module.End.one_apply]⟩

/-- The actual coinduced function retains every original coefficient value. -/
theorem originalCoinducedFunction_apply (f : G → A) (g : G) :
    (originalCoinducedFunction A f).val g = f g := by
  rfl

/-- The actual action is right translation of the original function argument. -/
theorem originalCoinducedFunctionRep_action
    (f : originalCoinducedFunctionRep A) (h g : G) :
    ((originalCoinducedFunctionRep A).ρ h f).val g = f.val (g * h) := by
  rfl

end
end Dubon2026
