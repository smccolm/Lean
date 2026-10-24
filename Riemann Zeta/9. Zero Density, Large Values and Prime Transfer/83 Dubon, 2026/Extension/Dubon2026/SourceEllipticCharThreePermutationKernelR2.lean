import Dubon2026.SourceEllipticCharThreeRootPermutationR2

/-! The kernel of the actual action on the three roots consists only of
identity and elliptic negation. This is the quotient-kernel input for the
DUB-17/18 characteristic-three order-dividing-six extension.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isGalois_ord_jqModC_dvd_six_of_char_three, AutHom. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

theorem eq_one_or_negation_of_charThreeRootPermHom_eq_one
    {γ : MulAction.stabilizer (VariableChange K) (EA (-1 : K))}
    (h : charThreeRootPermHom K γ = 1) :
    γ.val = 1 ∨ γ.val = negationChange (EA (-1 : K)) := by
  obtain ⟨hs, ht, _, _⟩ := char_three_stabilizer_coordinates γ.property
  have hv : ((γ.val.u⁻¹ : Kˣ) : K) ≠ 0 := (γ.val.u⁻¹).ne_zero
  have h0 : ((γ.val.u⁻¹ : Kˣ) : K) ^ 2 * (0 - γ.val.r) = 0 := by
    exact congrArg (fun e : Equiv.Perm (charThreeRoots K) => (e ⟨0, by ring⟩).val) h
  have hr : γ.val.r = 0 := by
    have hz := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hv)
    linear_combination -hz
  have h1 : ((γ.val.u⁻¹ : Kˣ) : K) ^ 2 * (1 - γ.val.r) = 1 := by
    exact congrArg (fun e : Equiv.Perm (charThreeRoots K) => (e ⟨1, by ring⟩).val) h
  rw [hr, sub_zero, mul_one, Units.val_inv_eq_inv_val, inv_pow, inv_eq_one] at h1
  rcases sq_eq_one_iff.mp h1 with hu | hu
  · left
    have hu' : γ.val.u = 1 := Units.ext hu
    ext <;> simp [VariableChange.one_def, hu', hr, hs, ht]
  · right
    have hu' : γ.val.u = -1 := Units.ext (by simpa using hu)
    ext <;> simp [negationChange, hu', hr, hs, ht]

/-- Compose a stabilizing action with its literal action on the three roots. -/
def charThreeInertiaPermHom {I : Type*} [Group I]
    (ρ : I →* VariableChange K) (hfix : ∀ σ, ρ σ • EA (-1 : K) = EA (-1 : K)) :
    I →* Equiv.Perm (charThreeRoots K) :=
  (charThreeRootPermHom K).comp
    { toFun := fun σ => ⟨ρ σ, MulAction.mem_stabilizer_iff.mpr (hfix σ)⟩
      map_one' := Subtype.ext ρ.map_one
      map_mul' := fun σ τ => Subtype.ext (ρ.map_mul σ τ) }

theorem charThreeInertiaPermHom_kernel {I : Type*} [Group I]
    (ρ : I →* VariableChange K) (hfix : ∀ σ, ρ σ • EA (-1 : K) = EA (-1 : K))
    (σ : I) (hσ : charThreeInertiaPermHom ρ hfix σ = 1) :
    ρ σ = 1 ∨ ρ σ = negationChange (EA (-1 : K)) :=
  eq_one_or_negation_of_charThreeRootPermHom_eq_one hσ

end
end Dubon2026.SourceEllipticExceptional
