import Dubon2026.ArithmeticSupportRestriction

/-! DUB-17/18 -> residual Galois association -> restore original support.
The actual weight descent gives Q ∣ M ∣ Q p². The arithmetic extensions
for Qp and Mp are equal because powers do not change exceptional primes.
This uses the original finite-stage definition, without an additional
ramification theorem or auxiliary descent assumption.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- Divisibility by a power gives inclusion of the original unramified unions. -/
theorem sourceUnramifiedUnion_mono_dvd_pow
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
    {a b : 𝓞 K} (n : ℕ) (hab : a ∣ b ^ n) :
    originalUnramifiedGaloisUnion (Ω := Ω) a ≤ originalUnramifiedGaloisUnion b := by
  apply iSup_le
  intro F
  apply originalUnramifiedGaloisStage_le_union b
    (⟨F.val, ?_⟩ : OriginalUnramifiedGaloisStage b)
  intro w hw
  apply F.property w
  intro ha
  apply hw
  apply w.isPrime.mem_of_pow_mem n
  obtain ⟨c, hc⟩ := hab
  rw [← map_pow, hc, map_mul]
  exact w.asIdeal.mul_mem_right _ ha

/-- The original level and the actual weight-two level have the same
arithmetic extension after adjoining the coefficient prime to the support. -/
theorem sourceWeightTwo_arithmeticExtension_eq
    {Q M p : ℕ} (hQM : Q ∣ M) (hM : M ∣ Q * p ^ 2) :
    rationalUnramifiedExtension (Q * p : ℕ) =
      rationalUnramifiedExtension (M * p : ℕ) := by
  apply le_antisymm
  · apply originalUnramifiedGaloisUnion_mono_dvd
    obtain ⟨c, hc⟩ := Nat.mul_dvd_mul_right hQM p
    exact ⟨(c : 𝓞 ℚ), by exact_mod_cast hc⟩
  · apply sourceUnramifiedUnion_mono_dvd_pow 3
    have h : M * p ∣ (Q * p) ^ 3 := by
      calc
        M * p ∣ Q * p ^ 2 * p := Nat.mul_dvd_mul_right hM p
        _ ∣ (Q * p) ^ 3 := ⟨Q ^ 2, by ring⟩
    obtain ⟨c, hc⟩ := h
    exact ⟨(c : 𝓞 ℚ), by exact_mod_cast hc⟩

/-- Equality of the actual arithmetic extensions makes the existing
restriction map injective, in addition to its proved surjectivity. -/
theorem sourceArithmeticSupportRestriction_injective
    (a b : 𝓞 ℚ) (hab : a ∣ b)
    (heq : rationalUnramifiedExtension a = rationalUnramifiedExtension b) :
    Function.Injective (rationalArithmeticSupportRestriction a b hab) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro y
  let x : rationalUnramifiedExtension a := ⟨y.val, by rw [heq]; exact y.property⟩
  have hx : rationalArithmeticSupportInclusion a b hab x = y := rfl
  rw [← hx]
  have hσ := rationalArithmeticSupportRestriction_commutes a b hab σ x
  have hτ := rationalArithmeticSupportRestriction_commutes a b hab τ x
  apply hσ.symm.trans
  rw [h]
  exact hτ

/-- Continuous representations descend along the proved equality of the
actual arithmetic extensions, with exact whole-representation comparison. -/
theorem sourceArithmeticSupport_exists_representation
    {T : Type} [Group T] [TopologicalSpace T]
    (a b : 𝓞 ℚ) (hab : a ∣ b)
    (heq : rationalUnramifiedExtension a = rationalUnramifiedExtension b)
    (ρ : rationalArithmeticGaloisGroup b →ₜ* T) :
    ∃ η : rationalArithmeticGaloisGroup a →ₜ* T,
      ∀ g, η (rationalArithmeticSupportRestriction a b hab g) = ρ g := by
  let π := rationalArithmeticSupportRestriction a b hab
  have hs := rationalArithmeticSupportRestriction_surjective a b hab
  let e := MulEquiv.ofBijective π.toMonoidHom
    ⟨sourceArithmeticSupportRestriction_injective a b hab heq, hs⟩
  let f := ρ.toMonoidHom.comp e.symm.toMonoidHom
  have hf (g) : f (π g) = ρ g := congrArg ρ (e.symm_apply_apply g)
  have hfc : Continuous f := by
    apply (IsQuotientMap.of_surjective_continuous hs π.continuous).continuous_iff.mpr
    exact ρ.continuous.congr fun g => (hf g).symm
  exact ⟨⟨f, hfc⟩, hf⟩

end
end Dubon2026
