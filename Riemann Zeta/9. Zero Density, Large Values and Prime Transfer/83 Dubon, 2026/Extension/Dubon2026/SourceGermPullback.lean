import Mathlib.Order.Filter.Germ.Basic

/-! DUB-17/18 -> original Picard-period Hecke comparison -> analytic
realization of beta, the actual dilation map. Pullback of punctured germs
preserves the ring operations. The original consumer supplies the proved
punctured-neighborhood convergence of its nonzero linear dilation.
-/
namespace Dubon2026
noncomputable section
open Filter
variable {A B R : Type*} [Semiring R] {l : Filter A} {m : Filter B}

/-- Pullback of ring-valued germs along a map tending to the target filter. -/
def germPullback (g : A → B) (hg : Tendsto g l m) : Germ m R →+* Germ l R where
  toFun f := f.compTendsto g hg
  map_one' := rfl
  map_zero' := rfl
  map_add' f h := Quotient.inductionOn₂ f h fun _ _ => rfl
  map_mul' f h := Quotient.inductionOn₂ f h fun _ _ => rfl

theorem germPullback_coe (g : A → B) (hg : Tendsto g l m) (f : B → R) :
    germPullback g hg (f : Germ m R) = ((f ∘ g : A → R) : Germ l R) := rfl

end
end Dubon2026
