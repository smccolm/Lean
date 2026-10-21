import Dubon2026.SourceSL2CocycleSection

/-! A native SL2(Z) cocycle for the required Eisenstein cusp functional.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> actual nonzero
cusp-evaluation functional. The original semidirect-product section supplies
the native cocycle directly; no separate custom cohomology model is used.
-/

namespace Dubon2026
noncomputable section
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup groupCohomology

/-- Prescribed values satisfying the actual modular-generator relations
extend to a native cocycle of the original SL2(Z) representation. -/
theorem sourceSL2Cocycle_exists
    {F V : Type} [CommRing F] [AddCommGroup V] [Module F V]
    (ρ : Representation F SL(2, ℤ) V) (x y : V)
    (hx : x + ρ S x = 0)
    (hy : y + ρ (S * T) y + ρ (S * T) (ρ (S * T) y) = 0) :
    ∃ z : cocycles₁ (Rep.of ρ), z S = x ∧ z (S * T) = y := by
  let s := SourceSL2Cocycle.sec hx hy
  have hz : (fun g : SL(2, ℤ) => Multiplicative.toAdd (s g).left) ∈
      cocycles₁ (Rep.of ρ) := by
    apply (mem_cocycles₁_iff _).mpr
    intro g h
    change (s (g * h)).left.toAdd = ρ g (s h).left.toAdd + (s g).left.toAdd
    rw [map_mul, SemidirectProduct.mul_left, toAdd_mul]
    change (s g).left.toAdd + ρ (s g).right (s h).left.toAdd = _
    rw [SourceSL2Cocycle.sec_right]
    exact add_comm _ _
  refine ⟨⟨_, hz⟩, ?_, ?_⟩
  · change (SourceSL2Cocycle.sec hx hy S).left.toAdd = x
    rw [SourceSL2Cocycle.sec_S]
    rfl
  · change (SourceSL2Cocycle.sec hx hy SourceSL2Cocycle.U).left.toAdd = y
    rw [SourceSL2Cocycle.sec_U]
    rfl

end
end Dubon2026
