import Dubon2026.IntegralInertiaRestriction
import Dubon2026.NumberFieldInertiaRamification
import Dubon2026.UnramifiedUnionFiniteRamification

/-! # Actual inertia in the whole original arithmetic unramified union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Every actual inertia automorphism of the original infinite arithmetic extension restricts to the identity on each original finite Galois subfield away from the exceptional integer. -/
theorem originalUnramifiedUnion_inertia_finite_restriction
    (a : 𝓞 K) (ha : a ≠ 0)
    (P : Ideal (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)))
    [P.IsPrime] (hP : P ≠ ⊥)
    (haP : algebraMap (𝓞 K) (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)) a ∉ P)
    (σ : Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K))
    (hσ : σ ∈ P.inertia Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K))
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    σ.restrictNormal F = 1 := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  let w : HeightOneSpectrum (𝓞 F) :=
    ⟨P.under (𝓞 F), inferInstance, Ideal.under_ne_bot (𝓞 F) hP⟩
  have hw : algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal := by
    intro h
    apply haP
    change algebraMap (𝓞 F) (𝓞 U) (algebraMap (𝓞 K) (𝓞 F) a) ∈ P at h
    simpa only [← IsScalarTower.algebraMap_apply] using h
  let v := w.under (𝓞 K)
  letI : w.asIdeal.LiesOver v.asIdeal :=
    inferInstanceAs (w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)))
  have htrivial := numberField_inertia_eq_bot_of_ramificationIdx_one v w
    (originalUnramifiedUnion_finite_ramification a ha F.toIntermediateField w hw)
  have hmem := integral_inertia_restrictNormal_mem (E := F) P σ hσ
  change σ.restrictNormal F ∈ w.asIdeal.inertia Gal(F/K) at hmem
  rw [htrivial] at hmem
  exact hmem

/-- The genuine inertia subgroup of every original nonzero prime outside the exceptional integer is trivial in the entire constructed arithmetic extension. -/
theorem originalUnramifiedUnion_inertia_eq_bot
    (a : 𝓞 K) (ha : a ≠ 0)
    (P : Ideal (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)))
    [P.IsPrime] (hP : P ≠ ⊥)
    (haP : algebraMap (𝓞 K) (𝓞 (originalUnramifiedGaloisUnion (Ω := Ω) a)) a ∉ P) :
    P.inertia Gal((originalUnramifiedGaloisUnion (Ω := Ω) a)/K) = ⊥ := by
  apply le_antisymm _ bot_le
  intro σ hσ
  change σ = 1
  apply AlgEquiv.ext
  intro x
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois K U := originalUnramifiedGaloisUnion_isGalois a
  let F := FiniteGaloisIntermediateField.adjoin K ({x} : Set U)
  have hx : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K {x} (Set.mem_singleton x)
  have hF := originalUnramifiedUnion_inertia_finite_restriction a ha P hP haP σ hσ F
  have h := σ.restrictNormal_commutes F (⟨x, hx⟩ : F)
  rw [hF] at h
  exact h.symm

end
end Dubon2026
