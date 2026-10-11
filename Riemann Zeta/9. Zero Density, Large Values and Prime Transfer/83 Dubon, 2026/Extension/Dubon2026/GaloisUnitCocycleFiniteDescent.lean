import Dubon2026.ContinuousGaloisCocycleFiniteField

/-! # Descent of the original nontrivial Galois unit cocycle to its actual finite field -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)
  (c : groupCohomology.cocycles₁ (Rep.ofAlgebraAutOnUnits K Ω))
  (hvalues : ∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c g)) : Ωˣ) : Ω) ∈ F.toIntermediateField)
  (hperiod : ∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → c (g * u) = c g)

/-- Each original unit cocycle value becomes a genuine unit of its actual
finite coefficient field, using its original nonzero value. -/
def finiteFieldCocycleUnitAt (g : Gal(Ω/K)) : Fˣ :=
  Units.mk0 ⟨((Additive.toMul (Rep.toAdditive (c g)) : Ωˣ) : Ω), hvalues g⟩ (by
    intro hz
    exact Units.ne_zero (Additive.toMul (Rep.toAdditive (c g)))
      (congrArg (fun x : F => (x : Ω)) hz))

omit [IsGalois K Ω] in
/-- The original coefficient-field inclusion recovers the exact original unit. -/
theorem finiteFieldCocycleUnitAt_map (g : Gal(Ω/K)) :
    Units.map F.toIntermediateField.val.toMonoidHom (finiteFieldCocycleUnitAt F c hvalues g) =
      Additive.toMul (Rep.toAdditive (c g)) := by
  apply Units.ext
  rfl

include hperiod in
omit [IsGalois K Ω] in
/-- Equal original restrictions give equal original cocycle values through
the actual period relation, without treating the cocycle as a homomorphism. -/
theorem galoisUnitCocycle_eq_of_restriction_eq (g h : Gal(Ω/K))
    (he : AlgEquiv.restrictNormalHom F g = AlgEquiv.restrictNormalHom F h) : c g = c h := by
  have hk : AlgEquiv.restrictNormalHom F (g⁻¹ * h) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hp := hperiod g (g⁻¹ * h) hk
  simpa only [mul_inv_cancel_left] using hp.symm

include hvalues hperiod in
/-- The actual finite-field-valued descended function is a cocycle for the
original nontrivial finite Galois action, and its original embedding recovers
every original infinite-Galois cocycle value exactly. -/
theorem galoisUnitCocycle_exists_finite_descent :
    ∃ f : Gal(F/K) → Fˣ, groupCohomology.IsMulCocycle₁ f ∧
      ∀ g : Gal(Ω/K), Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g)) = Additive.toMul (Rep.toAdditive (c g)) := by
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Function.Surjective j := AlgEquiv.restrictNormalHom_surjective Ω
  let i := Units.map F.toIntermediateField.val.toMonoidHom
  let f : Gal(F/K) → Fˣ := fun σ => finiteFieldCocycleUnitAt F c hvalues (Function.surjInv hj σ)
  have hfactor : ∀ g : Gal(Ω/K), i (f (j g)) = Additive.toMul (Rep.toAdditive (c g)) := by
    intro g
    change Units.map F.toIntermediateField.val.toMonoidHom
      (finiteFieldCocycleUnitAt F c hvalues (Function.surjInv hj (j g))) = _
    rw [finiteFieldCocycleUnitAt_map]
    have he := galoisUnitCocycle_eq_of_restriction_eq F c hperiod
      (Function.surjInv hj (j g)) g (Function.surjInv_eq hj (j g))
    exact congrArg (fun v => Additive.toMul (Rep.toAdditive v)) he
  refine ⟨f, ?_, hfactor⟩
  intro σ τ
  obtain ⟨g, rfl⟩ := hj σ
  obtain ⟨h, rfl⟩ := hj τ
  apply Units.map_injective F.toIntermediateField.val.injective
  have haction : ∀ u : Fˣ, i (j g • u) = g • i u := by
    intro u
    apply Units.ext
    exact AlgEquiv.restrictNormal_commutes g F u.val
  change i (f (j g * j h)) = i (j g • f (j h) * f (j g))
  rw [← map_mul j, map_mul i, haction, hfactor, hfactor, hfactor]
  exact groupCohomology.isMulCocycle₁_of_mem_cocycles₁ _ c.property g h

end
end Dubon2026
