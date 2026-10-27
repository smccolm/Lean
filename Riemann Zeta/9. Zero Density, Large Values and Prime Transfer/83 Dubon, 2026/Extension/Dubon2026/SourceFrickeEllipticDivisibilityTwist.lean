import Dubon2026.SourceFrickeHolomorphicDivisionTwist

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> elliptic divisibility transport. Convert the actual power-divisibility
identity into holomorphic division by the original j-coordinate factor,
apply the proved quotient closure and coefficient twist, then restore the
discriminant powers. All cusp-growth and coordinate-invariance assumptions
of the longer external transport argument are unnecessary on this route. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem frickeCoefficientTwist_transport_elliptic_divisibility
    (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (J : (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) (hJ0 : (J : ℍ → ℂ) ≠ 0)
    (E : ℍ → ℂ) (m p q : ℕ)
    (hEJ : ∀ τ : ℍ, E τ ^ p = (J : ℍ → ℂ) τ * CuspForm.discriminant τ)
    (hdiv : ∃ G : ℍ → ℂ, MDiff G ∧ ∀ τ : ℍ,
      ((F : ℍ → ℂ) τ * CuspForm.discriminant τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDiff G' ∧ ∀ τ : ℍ,
      ((frickeCoefficientTwist N σ F : ℍ → ℂ) τ * CuspForm.discriminant τ ^ m) ^ p =
        E τ ^ (p * q) * G' τ := by
  obtain ⟨G, hG, he⟩ := hdiv
  let D : ℍ → ℂ := CuspForm.discriminant
  have hEJ' : ∀ τ : ℍ, E τ ^ p = (J : ℍ → ℂ) τ * D τ := hEJ
  have hD : MDiff D := CuspForm.discriminant.holo'
  have hD0 : ∀ τ : ℍ, D τ ≠ 0 := ModularForm.discriminant_ne_zero
  let W : ℍ → ℂ := G * D ^ q / D ^ (m * p)
  have hW : MDiff W := (hG.mul (hD.pow q)).div (hD.pow (m * p))
    (fun τ => pow_ne_zero _ (hD0 τ))
  let Jq : (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule :=
    ⟨(J : ℍ → ℂ) ^ q, (cyclotomicHolomorphicFrickeAlgebra N).pow_mem J.property q⟩
  have hJq0 : (Jq : ℍ → ℂ) ≠ 0 := by
    intro hz
    apply hJ0
    funext τ
    exact eq_zero_of_pow_eq_zero (congrFun hz τ)
  have hrel : W * (Jq : ℍ → ℂ) = (frickeSpanPow N F p : ℍ → ℂ) := by
    funext τ
    change (G τ * D τ ^ q / D τ ^ (m * p)) * (J : ℍ → ℂ) τ ^ q = (F : ℍ → ℂ) τ ^ p
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (pow_ne_zero _ (hD0 τ))).mpr
    have h1 : (F : ℍ → ℂ) τ ^ p * D τ ^ (m * p) = (J : ℍ → ℂ) τ ^ q * D τ ^ q * G τ := by
      calc (F : ℍ → ℂ) τ ^ p * D τ ^ (m * p) = ((F : ℍ → ℂ) τ * D τ ^ m) ^ p := by rw [mul_pow, pow_mul]
           _ = E τ ^ (p * q) * G τ := he τ
           _ = (J : ℍ → ℂ) τ ^ q * D τ ^ q * G τ := by rw [pow_mul, hEJ', mul_pow]
    calc G τ * D τ ^ q * (J : ℍ → ℂ) τ ^ q = (J : ℍ → ℂ) τ ^ q * D τ ^ q * G τ := by ring
         _ = (F : ℍ → ℂ) τ ^ p * D τ ^ (m * p) := h1.symm
  obtain ⟨W', hW', ht⟩ := exists_twisted_holomorphic_quotient N σ
    (frickeSpanPow N F p) Jq hJq0 hW hrel
  rw [frickeCoefficientTwist_pow] at ht
  refine ⟨W' * D ^ (m * p) / D ^ q,
    (hW'.mul (hD.pow (m * p))).div (hD.pow q) (fun τ => pow_ne_zero _ (hD0 τ)), ?_⟩
  intro τ
  have htτ : W' τ * (J : ℍ → ℂ) τ ^ q = (frickeCoefficientTwist N σ F : ℍ → ℂ) τ ^ p := congrFun ht τ
  change ((frickeCoefficientTwist N σ F : ℍ → ℂ) τ * D τ ^ m) ^ p =
    E τ ^ (p * q) * (W' τ * D τ ^ (m * p) / D τ ^ q)
  rw [mul_pow, pow_mul, ← htτ, pow_mul, hEJ', mul_pow]
  field_simp [hD0 τ]

end
end Dubon2026.SourceFricke