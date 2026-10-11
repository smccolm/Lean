import Dubon2026.ContinuousGaloisCochainFiniteField

/-! # Exact finite descent of original Galois unit cochains -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (F : FiniteGaloisIntermediateField K Ω) (b : Gal(Ω/K) → Ωˣ)
  (hvalues : ∀ g, (b g).val ∈ F.toIntermediateField)
  (hperiod : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)

include hvalues hperiod in
/-- Actual finite coefficient values and actual restriction periods descend
the original cochain through genuine Galois restriction, retaining every value. -/
theorem galoisUnitCochain_exists_finite_descent :
    ∃ f : Gal(F/K) → Fˣ, ∀ g : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (f (AlgEquiv.restrictNormalHom F g)) = b g := by
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Function.Surjective j := AlgEquiv.restrictNormalHom_surjective Ω
  let v (g : Gal(Ω/K)) : Fˣ := Units.mk0 ⟨(b g).val, hvalues g⟩ (by
    intro hz
    exact (b g).ne_zero (congrArg (fun x : F => (x : Ω)) hz))
  let f : Gal(F/K) → Fˣ := fun σ => v (Function.surjInv hj σ)
  refine ⟨f, fun g => ?_⟩
  have he : j (Function.surjInv hj (j g)) = j g := Function.surjInv_eq hj (j g)
  have hp : j ((Function.surjInv hj (j g))⁻¹ * g) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hb := hperiod (Function.surjInv hj (j g))
    ((Function.surjInv hj (j g))⁻¹ * g) hp
  have hb' : b (Function.surjInv hj (j g)) = b g := by
    simpa only [mul_inv_cancel_left] using hb.symm
  apply Units.ext
  change (b (Function.surjInv hj (j g))).val = (b g).val
  exact congrArg (fun u : Ωˣ => u.val) hb'

end
end Dubon2026
