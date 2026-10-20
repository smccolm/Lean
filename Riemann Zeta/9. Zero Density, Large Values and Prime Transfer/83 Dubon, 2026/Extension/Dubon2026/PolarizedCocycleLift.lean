import Dubon2026.PolarizedFirstOrderCocycles

/-! Reconstruction of an actual fixed-similitude polarized representation
from its full adjoint cocycle, inverse to the original-coordinate tangent
map. This gives the exact algebraic source fiber needed for DUB-17. -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- An original full adjoint cocycle gives an actual dual-number polarized representation. -/
def polarizedCocycleHom (ρ : G →* PolarizedGaloisGroup ι R)
    (c : groupCohomology.cocycles₁ (polarizedAdjointRep ρ)) :
    G →* PolarizedGaloisGroup ι (DualNumber R) where
  toFun g := polarizedStrictPoint (c g) * polarizedDualConstant (ρ g)
  map_one' := by simp [polarizedStrictPoint_zero]
  map_mul' g h := by
    have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.property g h
    change c (g * h) = polarizedAdjointRepresentation (ρ g) (c h) + c g at hc
    have hconj := polarizedStrictPoint_conjugate (polarizedDualConstant (ρ g)) (c h)
    rw [polarizedDualReduction_constant] at hconj
    rw [hc, add_comm, polarizedStrictPoint_add, ← hconj, map_mul, map_mul]
    simp only [mul_assoc, inv_mul_cancel_left]

/-- The actual reconstructed representation has the original reduction and exactly fixed similitude. -/
def polarizedFirstOrderLiftFromCocycle (ρ : G →* PolarizedGaloisGroup ι R)
    (c : groupCohomology.cocycles₁ (polarizedAdjointRep ρ)) : PolarizedFirstOrderLift ρ := by
  refine ⟨polarizedCocycleHom ρ c, ?_, ?_⟩
  · apply MonoidHom.ext
    intro g
    change polarizedDualReduction (polarizedStrictPoint (c g) * polarizedDualConstant (ρ g)) = ρ g
    rw [map_mul, polarizedStrictPoint_reduction, one_mul, polarizedDualReduction_constant]
  · apply MonoidHom.ext
    intro g
    change polarizedSimilitude (polarizedStrictPoint (c g) * polarizedDualConstant (ρ g)) = _
    rw [map_mul, polarizedStrictPoint_similitude, one_mul]
    exact polarizedCoefficientMap_similitude (TrivSqZeroExt.inlHom R R) (ρ g)

/-- The reconstructed representation retains its original infinitesimal-times-constant point. -/
theorem polarizedFirstOrderLiftFromCocycle_apply (ρ : G →* PolarizedGaloisGroup ι R)
    (c : groupCohomology.cocycles₁ (polarizedAdjointRep ρ)) (g : G) :
    (polarizedFirstOrderLiftFromCocycle ρ c).val g =
      polarizedStrictPoint (c g) * polarizedDualConstant (ρ g) := rfl

/-- Extracting the actual first-order cocycle from the reconstructed original representation recovers its input. -/
theorem polarizedFirstOrderCocycle_fromCocycle (ρ : G →* PolarizedGaloisGroup ι R)
    (c : groupCohomology.cocycles₁ (polarizedAdjointRep ρ)) :
    polarizedFirstOrderCocycle ρ (polarizedFirstOrderLiftFromCocycle ρ c) = c := by
  apply groupCohomology.cocycles₁_ext
  intro g
  apply polarizedStrictPoint_injective
  apply mul_right_cancel (b := polarizedDualConstant (ρ g))
  exact polarizedFirstOrderCoordinate_reconstruct ρ (polarizedFirstOrderLiftFromCocycle ρ c) g

/-- Reconstructing the original polarized lift from its actual cocycle recovers the entire representation. -/
theorem polarizedFirstOrderLiftFromCocycle_cocycle (ρ : G →* PolarizedGaloisGroup ι R)
    (τ : PolarizedFirstOrderLift ρ) :
    polarizedFirstOrderLiftFromCocycle ρ (polarizedFirstOrderCocycle ρ τ) = τ := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro g
  exact polarizedFirstOrderCoordinate_reconstruct ρ τ g

/-- The genuine fixed-similitude polarized first-order fiber is equivalent to the full adjoint cocycle module. -/
def polarizedFirstOrderLiftEquiv (ρ : G →* PolarizedGaloisGroup ι R) :
    PolarizedFirstOrderLift ρ ≃ groupCohomology.cocycles₁ (polarizedAdjointRep ρ) where
  toFun := polarizedFirstOrderCocycle ρ
  invFun := polarizedFirstOrderLiftFromCocycle ρ
  left_inv := polarizedFirstOrderLiftFromCocycle_cocycle ρ
  right_inv := polarizedFirstOrderCocycle_fromCocycle ρ

end
end Dubon2026
