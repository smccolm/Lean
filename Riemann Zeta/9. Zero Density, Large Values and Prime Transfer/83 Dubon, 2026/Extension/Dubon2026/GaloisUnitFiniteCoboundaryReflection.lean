import Dubon2026.GaloisUnitCochainFiniteDescent

/-! # Original finite-stage coboundaries reflected from actual descended witnesses -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω)

/-- If an actual inflated two-cochain is a coboundary and its original
witness has values and periods in the displayed finite field, the original
finite two-cochain has the genuine descended coboundary witness there. -/
theorem galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq
    (c : Gal(F/K) × Gal(F/K) → Fˣ) (b : Gal(Ω/K) → Ωˣ)
    (hvalues : ∀ g, (b g).val ∈ F.toIntermediateField)
    (hperiod : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)
    (hc : ∀ g h : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (c (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
          g • b h / b (g * h) * b g) :
    ∃ f : Gal(F/K) → Fˣ, ∀ σ τ : Gal(F/K),
      c (σ, τ) = Units.map σ (f τ) / f (σ * τ) * f σ := by
  obtain ⟨f, hf⟩ := galoisUnitCochain_exists_finite_descent F b hvalues hperiod
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Function.Surjective j := AlgEquiv.restrictNormalHom_surjective Ω
  let i := Units.map F.toIntermediateField.val.toMonoidHom
  refine ⟨f, fun σ τ => ?_⟩
  obtain ⟨g, rfl⟩ := hj σ
  obtain ⟨h, rfl⟩ := hj τ
  apply Units.map_injective F.toIntermediateField.val.injective
  have haction (u : Fˣ) : i (j g • u) = g • i u := by
    apply Units.ext
    exact AlgEquiv.restrictNormal_commutes g F u.val
  change i (c (j g, j h)) = i (j g • f (j h) / f (j g * j h) * f (j g))
  rw [map_mul, map_div, haction, ← map_mul j, hf, hf, hf]
  exact hc g h

end
end Dubon2026
