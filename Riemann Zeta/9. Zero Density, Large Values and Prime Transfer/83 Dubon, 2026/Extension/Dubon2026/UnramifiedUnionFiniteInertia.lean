import Dubon2026.NumberFieldInertiaRamification
import Dubon2026.UnramifiedUnionFiniteFieldCriterion

/-! # Actual finite-stage inertia in the original arithmetic unramified union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- At every original prime outside the exceptional element, every actual finite Galois subfield of the constructed unramified union has trivial original inertia subgroup. -/
theorem originalUnramifiedUnion_finiteGalois_inertia_eq_bot
    (a : 𝓞 K) (ha : a ≠ 0) (F : FiniteGaloisIntermediateField K Ω)
    (hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal) :
    w.asIdeal.inertia Gal(F/K) = ⊥ := by
  let v := w.under (𝓞 K)
  letI : w.asIdeal.LiesOver v.asIdeal :=
    inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)))
  exact numberField_inertia_eq_bot_of_ramificationIdx_one v w
    ((originalUnramifiedUnion_finiteGalois_le_iff a ha F).mp hF w hw)

/-- Every original inertia automorphism outside the exceptional element fixes every element of the original finite Galois stage in the actual arithmetic union. -/
theorem originalUnramifiedUnion_finiteGalois_inertia_fixes
    (a : 𝓞 K) (ha : a ≠ 0) (F : FiniteGaloisIntermediateField K Ω)
    (hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal)
    (σ : Gal(F/K)) (hσ : σ ∈ w.asIdeal.inertia Gal(F/K)) (x : F) : σ x = x := by
  rw [originalUnramifiedUnion_finiteGalois_inertia_eq_bot a ha F hF w hw] at hσ
  have hσone : σ = 1 := hσ
  rw [hσone]
  rfl

end
end Dubon2026
