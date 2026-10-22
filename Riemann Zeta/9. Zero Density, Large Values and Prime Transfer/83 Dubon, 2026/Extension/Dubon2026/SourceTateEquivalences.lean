import Dubon2026.SourceTateFunctor

/-! DUB-17/18 -> original Tate/period comparison. Transport along the actual
additive Picard-period equivalence, with its coordinate formula. Isolating this
formal transport avoids unfolding concrete function fields during elaboration.
-/
namespace Dubon2026.TateModule
noncomputable section
variable (p : ℕ) [Fact p.Prime] {M M' : Type*} [AddCommGroup M] [AddCommGroup M']

/-- The functor applied to an additive equivalence. -/
def ofAddEquiv (e : M ≃+ M') : TateModule p M ≃ₗ[ℤ_[p]] TateModule p M' :=
  tateEquivOfInjective e.toAddMonoidHom e.injective (fun y _ => e.surjective y)

theorem ofAddEquiv_apply (e : M ≃+ M') (x : TateModule p M) (n : ℕ) :
    ((ofAddEquiv p e x : TateModule p M') : ℕ → M') n = e ((x : ℕ → M) n) := rfl

end
end Dubon2026.TateModule
