import Dubon2026.ContinuousGaloisTwoCocycleFiniteField

/-! # Descent of the original Galois unit two-cocycle to its actual finite field -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)
  (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K Ω))
  (hvalues : ∀ g h : Gal(Ω/K),
    ((Additive.toMul (Rep.toAdditive (c (g, h))) : Ωˣ) : Ω) ∈ F.toIntermediateField)
  (hperiod : ∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
    AlgEquiv.restrictNormalHom F v = 1 → c (g * u, h * v) = c (g, h))

/-- Each original unit value lies in the actual finite coefficient field and
therefore defines a genuine unit there. -/
def finiteFieldTwoCocycleUnitAt (g h : Gal(Ω/K)) : Fˣ :=
  Units.mk0 ⟨((Additive.toMul (Rep.toAdditive (c (g, h))) : Ωˣ) : Ω), hvalues g h⟩ (by
    intro hz
    exact Units.ne_zero (Additive.toMul (Rep.toAdditive (c (g, h))))
      (congrArg (fun x : F => (x : Ω)) hz))

omit [IsGalois K Ω] in
/-- The original field inclusion recovers the exact original two-cocycle value. -/
theorem finiteFieldTwoCocycleUnitAt_map (g h : Gal(Ω/K)) :
    Units.map F.toIntermediateField.val.toMonoidHom
      (finiteFieldTwoCocycleUnitAt F c hvalues g h) =
      Additive.toMul (Rep.toAdditive (c (g, h))) := by
  apply Units.ext
  rfl

include hperiod in
omit [IsGalois K Ω] in
/-- Equality of both actual restrictions gives equality of original values. -/
theorem galoisUnitTwoCocycle_eq_of_restriction_eq (g h g' h' : Gal(Ω/K))
    (hg : AlgEquiv.restrictNormalHom F g = AlgEquiv.restrictNormalHom F g')
    (hh : AlgEquiv.restrictNormalHom F h = AlgEquiv.restrictNormalHom F h') :
    c (g, h) = c (g', h') := by
  have hgu : AlgEquiv.restrictNormalHom F (g⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, hg, inv_mul_cancel]
  have hhv : AlgEquiv.restrictNormalHom F (h⁻¹ * h') = 1 := by
    rw [map_mul, map_inv, hh, inv_mul_cancel]
  have hp := hperiod g h (g⁻¹ * g') (h⁻¹ * h') hgu hhv
  simpa only [mul_inv_cancel_left] using hp.symm

include hvalues hperiod in
/-- Actual restriction and field inclusion descend the original two-cocycle
with its original nontrivial Galois action. Both arguments retain exact values. -/
theorem galoisUnitTwoCocycle_exists_finite_descent :
    ∃ f : Gal(F/K) × Gal(F/K) → Fˣ, groupCohomology.IsMulCocycle₂ f ∧
      ∀ g h : Gal(Ω/K), Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
        Additive.toMul (Rep.toAdditive (c (g, h))) := by
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Function.Surjective j := AlgEquiv.restrictNormalHom_surjective Ω
  let i := Units.map F.toIntermediateField.val.toMonoidHom
  let f : Gal(F/K) × Gal(F/K) → Fˣ := fun z =>
    finiteFieldTwoCocycleUnitAt F c hvalues (Function.surjInv hj z.1) (Function.surjInv hj z.2)
  have hfactor : ∀ g h : Gal(Ω/K),
      i (f (j g, j h)) = Additive.toMul (Rep.toAdditive (c (g, h))) := by
    intro g h
    change Units.map F.toIntermediateField.val.toMonoidHom
      (finiteFieldTwoCocycleUnitAt F c hvalues
        (Function.surjInv hj (j g)) (Function.surjInv hj (j h))) = _
    rw [finiteFieldTwoCocycleUnitAt_map]
    have he := galoisUnitTwoCocycle_eq_of_restriction_eq F c hperiod
      (Function.surjInv hj (j g)) (Function.surjInv hj (j h)) g h
      (Function.surjInv_eq hj (j g)) (Function.surjInv_eq hj (j h))
    exact congrArg (fun v => Additive.toMul (Rep.toAdditive v)) he
  refine ⟨f, ?_, hfactor⟩
  intro σ τ υ
  obtain ⟨g, rfl⟩ := hj σ
  obtain ⟨h, rfl⟩ := hj τ
  obtain ⟨t, rfl⟩ := hj υ
  apply Units.map_injective F.toIntermediateField.val.injective
  have haction : ∀ u : Fˣ, i (j g • u) = g • i u := by
    intro u
    apply Units.ext
    exact AlgEquiv.restrictNormal_commutes g F u.val
  change i (f (j g * j h, j t) * f (j g, j h)) =
    i (j g • f (j h, j t) * f (j g, j h * j t))
  rw [← map_mul j, ← map_mul j, map_mul i, map_mul i, haction,
    hfactor, hfactor, hfactor, hfactor]
  exact groupCohomology.isMulCocycle₂_of_mem_cocycles₂ _ c.property g h t

end
end Dubon2026
