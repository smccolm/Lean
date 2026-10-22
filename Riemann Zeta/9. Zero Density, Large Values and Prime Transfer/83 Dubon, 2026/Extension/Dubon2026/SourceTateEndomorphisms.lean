import Dubon2026.SourceTateFunctor

/-! DUB-17/18 -> actual original Tate Galois representation. The Tate functor
preserves addition, composition and identity on genuine group endomorphisms.
This will apply directly to the already constructed original Picard action.
-/
namespace Dubon2026.TateModule
noncomputable section
variable (p : ℕ) [Fact p.Prime] (M : Type*) [AddCommGroup M]

/-- The ring homomorphism on actual compatible torsion sequences. -/
def mapEnd : AddMonoid.End M →+* Module.End ℤ_[p] (TateModule p M) where
  toFun := tateMap p
  map_zero' := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_one' := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext (funext fun _ => rfl)

theorem mapEnd_apply (f : AddMonoid.End M) (x : TateModule p M) (n : ℕ) :
    ((mapEnd p M f x : TateModule p M) : ℕ → M) n = f ((x : ℕ → M) n) := rfl

end
end Dubon2026.TateModule
