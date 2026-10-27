import Dubon2026.SourceCyclotomicHolomorphicDivision

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> elliptic divisibility under nontrivial cyclotomic conjugation.
Reuse the already proved source power identities and holomorphic division
inside the original fraction algebra. The actual conjugate satisfies the
same E4/E6 divisibility conditions; no new growth premise is introduced. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem CyclotomicConjugates.elliptic_divisibility
    {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N} {F F' : ℍ → ℂ}
    (hFF' : CyclotomicConjugates σ F F')
    (hF : F ∈ holomorphicCyclotomicFrickeFractions N)
    (hF' : F' ∈ holomorphicCyclotomicFrickeFractions N)
    (J : (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) (hJ0 : (J : ℍ → ℂ) ≠ 0)
    (hJJ : CyclotomicConjugates σ (J : ℍ → ℂ) (J : ℍ → ℂ))
    (E : ℍ → ℂ) (m p q : ℕ)
    (hEJ : ∀ τ : ℍ, E τ ^ p = (J : ℍ → ℂ) τ * CuspForm.discriminant τ)
    (hdiv : ∃ G : ℍ → ℂ, MDiff G ∧ ∀ τ : ℍ,
      (F τ * CuspForm.discriminant τ ^ m) ^ p = E τ ^ (p * q) * G τ) :
    ∃ G' : ℍ → ℂ, MDiff G' ∧ ∀ τ : ℍ,
      (F' τ * CuspForm.discriminant τ ^ m) ^ p = E τ ^ (p * q) * G' τ := by
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
  have hrel : W * (Jq : ℍ → ℂ) = (F ^ p : ℍ → ℂ) := by
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
  obtain ⟨W', hW', ht⟩ := (hFF'.pow p).holomorphic_division (hJJ.pow q)
    ((cyclotomicHolomorphicFrickeAlgebra N).pow_mem hF p)
    ((cyclotomicHolomorphicFrickeAlgebra N).pow_mem hF' p) Jq.property hJq0 hW hrel
  refine ⟨W' * D ^ (m * p) / D ^ q,
    (hW'.mul (hD.pow (m * p))).div (hD.pow q) (fun τ => pow_ne_zero _ (hD0 τ)), ?_⟩
  intro τ
  have htτ : W' τ * (J : ℍ → ℂ) τ ^ q = (F' : ℍ → ℂ) τ ^ p := congrFun ht τ
  change ((F' : ℍ → ℂ) τ * D τ ^ m) ^ p =
    E τ ^ (p * q) * (W' τ * D τ ^ (m * p) / D τ ^ q)
  rw [mul_pow, pow_mul, ← htτ, pow_mul, hEJ', mul_pow]
  field_simp [hD0 τ]


end
end Dubon2026.SourceFricke
