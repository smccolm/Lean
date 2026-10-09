import Dubon2026.MatrixAdjointCocycles

/-! # Genuine first-order representations constructed from original adjoint cocycles -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- An original adjoint cocycle gives the literal matrix rho(g)+epsilon c(g)rho(g). -/
def firstOrderMatrixHom (ρ : G →* GeneralLinearGroup ι R)
    (c : groupCohomology.cocycles₁ (matrixAdjointRep ρ)) :
    G →* Matrix ι ι (DualNumber R) where
  toFun g := Matrix.dualNumberEquiv.symm ⟨(ρ g).val, c g * (ρ g).val⟩
  map_one' := by
    apply Matrix.dualNumberEquiv.injective
    rw [AlgEquiv.apply_symm_apply, map_one Matrix.dualNumberEquiv]
    apply TrivSqZeroExt.ext <;> simp
  map_mul' g h := by
    apply Matrix.dualNumberEquiv.injective
    rw [map_mul Matrix.dualNumberEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    apply TrivSqZeroExt.ext
    · simp
    · change c (g * h) * (ρ (g * h)).val =
        (ρ g).val * (c h * (ρ h).val) + (c g * (ρ g).val) * (ρ h).val
      have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.property g h
      change c (g * h) = (ρ g).val * c h * (ρ g⁻¹).val + c g at hc
      have hi : (ρ g⁻¹).val * (ρ g).val = 1 := by
        simpa only [map_inv] using (ρ g).inv_mul
      rw [hc, map_mul, Units.val_mul]
      calc
        _ = (ρ g).val * c h * ((ρ g⁻¹).val * (ρ g).val) * (ρ h).val +
            c g * (ρ g).val * (ρ h).val := by noncomm_ring
        _ = _ := by rw [hi]; noncomm_ring

/-- The literal matrices from the cocycle form a genuine invertible representation reducing exactly to the original one. -/
def firstOrderLiftFromCocycle (ρ : G →* GeneralLinearGroup ι R)
    (c : groupCohomology.cocycles₁ (matrixAdjointRep ρ)) : MatrixFirstOrderLift ρ := by
  refine ⟨(firstOrderMatrixHom ρ c).toHomUnits, ?_⟩
  apply MonoidHom.ext
  intro g
  apply Units.ext
  rfl

/-- The actual infinitesimal cocycle of the constructed original lift is exactly the input adjoint cocycle. -/
theorem matrixFirstOrderCocycle_fromCocycle (ρ : G →* GeneralLinearGroup ι R)
    (c : groupCohomology.cocycles₁ (matrixAdjointRep ρ)) :
    matrixFirstOrderCocycle ρ (firstOrderLiftFromCocycle ρ c) = c := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change (c g * (ρ g).val) * (ρ g⁻¹).val = c g
  rw [map_inv, mul_assoc, Units.mul_inv, mul_one]

end
end Dubon2026
