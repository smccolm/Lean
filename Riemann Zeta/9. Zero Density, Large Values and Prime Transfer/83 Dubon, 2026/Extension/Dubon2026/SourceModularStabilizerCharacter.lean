import Dubon2026.SourceAnalyticJOrbitSeparation
import Mathlib.RingTheory.IntegralDomain
import Mathlib.NumberTheory.ModularForms.ProperlyDiscontinuous

/-! DUB-17/18 -> numerical modular genus -> actual normalized ramification
equals half the Gamma0 stabilizer cardinality. The stabilizer character is
the actual Mobius denominator. Its injectivity and finite cyclic image
turn invariance of meromorphic germs into divisibility of their orders.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, selected proofs from
S_ModularCurve_ComplexPlaceDictionary_two_mul_ramification_eq_card_stabilizer
and S_UpperHalfPlane_natCard_stabilizer_dvd_two_mul_of_meromorphicOrderAt_eq.
-/
namespace Dubon2026.SourceFunctionField.StabilizerCharacter
noncomputable section
open UpperHalfPlane Filter
open scoped MatrixGroups Topology
theorem coe_mul_GL (γ δ : SL(2, ℤ)) :
    ((γ * δ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * δ := by
  simp only [map_mul]

theorem denom_mul_of_smul_eq (γ δ : SL(2, ℤ)) (τ : ℍ) (hδ : δ • τ = τ) :
    denom ((γ * δ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = denom γ τ * denom δ τ := by
  have h := denom_cocycle (γ : GL (Fin 2) ℝ) (δ : GL (Fin 2) ℝ) τ.im_ne_zero
  have h2 : ((δ • τ : ℍ) : ℂ) = num (δ : GL (Fin 2) ℝ) τ / denom (δ : GL (Fin 2) ℝ) τ := by
    rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]
  rw [← h2, hδ] at h
  rw [coe_mul_GL]
  exact h

theorem bottom_row_eq {c d c' d' : ℤ} (τ : ℍ)
    (h : (c : ℂ) * τ + d = (c' : ℂ) * τ + d') : c = c' ∧ d = d' := JOrbitSeparation.int_indep τ h

/-- The actual Mobius denominator on the full stabilizer. -/
def chi (τ : ℍ) : MulAction.stabilizer SL(2, ℤ) τ →* ℂ where
  toFun γ := denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ
  map_one' := by simp
  map_mul' γ δ := by
    rw [Subgroup.coe_mul, denom_mul_of_smul_eq _ _ _ δ.2]

theorem chi_apply (τ : ℍ) (γ : MulAction.stabilizer SL(2, ℤ) τ) :
    chi τ γ = denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) τ := rfl

theorem eq_one_of_denom_eq_one (τ : ℍ) (γ : SL(2, ℤ)) (hγ : γ • τ = τ)
    (h1 : denom (γ : GL (Fin 2) ℝ) τ = 1) : γ = 1 := by
  have hrow : (γ 1 0 : ℤ) = 0 ∧ (γ 1 1 : ℤ) = 1 := by
    have := bottom_row_eq (c := γ 1 0) (d := γ 1 1) (c' := 0) (d' := 1) τ
      (by rw [ModularGroup.denom_apply] at h1; push_cast; simpa using h1)
    exact this
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two, hrow.1, hrow.2] at hdet
  simp only [mul_one, mul_zero, sub_zero] at hdet

  have hfix := congrArg (fun z : ℍ => (z : ℂ)) hγ
  simp only [coe_specialLinearGroup_apply] at hfix
  rw [hrow.1, hrow.2, hdet] at hfix
  simp only [eq_intCast, Int.cast_zero, Complex.ofReal_zero, zero_mul, Int.cast_one,
    Complex.ofReal_one, zero_add, div_one, one_mul] at hfix
  have h01 : ((γ 0 1 : ℤ) : ℂ) = 0 := by
    have := hfix

    have h' : (τ : ℂ) + ((γ 0 1 : ℤ) : ℝ) = τ := by exact_mod_cast this
    have h'' := add_left_cancel (h'.trans (add_zero (τ : ℂ)).symm)
    exact_mod_cast h''
  have h01' : (γ 0 1 : ℤ) = 0 := by exact_mod_cast h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hrow.1, hrow.2, hdet, h01']

theorem chi_injective (τ : ℍ) : Function.Injective (chi τ) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro γ hγ
  rw [MonoidHom.mem_ker, chi_apply] at hγ
  exact Subtype.ext (eq_one_of_denom_eq_one τ γ γ.2 hγ)

theorem finite_stabilizer (τ : ℍ) : Finite (MulAction.stabilizer SL(2, ℤ) τ) := by
  have hfin := ProperlyDiscontinuousSMul.finite_stabilizer (Γ := 𝒮ℒ) τ
  have : Finite (MulAction.stabilizer (𝒮ℒ) τ) := hfin
  refine Finite.of_injective
    (fun γ => (⟨⟨Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ)), ⟨γ, rfl⟩⟩, γ.2⟩ :
      MulAction.stabilizer (𝒮ℒ) τ)) ?_
  intro a b h
  have := congrArg (fun x : MulAction.stabilizer (𝒮ℒ) τ => ((x : 𝒮ℒ) : GL (Fin 2) ℝ)) h
  exact Subtype.ext (Matrix.SpecialLinearGroup.mapGL_injective this)

scoped instance stabilizerFinite (τ : ℍ) : Finite (MulAction.stabilizer SL(2, ℤ) τ) := finite_stabilizer τ

theorem isCyclic_stabilizer (τ : ℍ) : IsCyclic (MulAction.stabilizer SL(2, ℤ) τ) :=
  isCyclic_of_injective_ringHom (chi τ) (chi_injective τ)

/-- The central negative identity fixes every upper-half-plane point. -/
def negOne (τ : ℍ) : MulAction.stabilizer SL(2, ℤ) τ :=
  ⟨-1, by rw [MulAction.mem_stabilizer_iff, ModularGroup.SL_neg_smul, one_smul]⟩

theorem orderOf_negOne (τ : ℍ) : orderOf (negOne τ) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    simp [negOne]
  · intro h
    have := congrArg (fun γ : MulAction.stabilizer SL(2, ℤ) τ => ((γ : SL(2, ℤ)) 0 0)) h
    simp [negOne] at this

theorem two_dvd_card_stabilizer (τ : ℍ) :
    2 ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ) := by
  have h := orderOf_dvd_natCard (negOne τ)
  rwa [orderOf_negOne] at h

theorem card_stabilizer_pos (τ : ℍ) : 0 < Nat.card (MulAction.stabilizer SL(2, ℤ) τ) :=
  Nat.card_pos

theorem exists_orderOf_eq (τ : ℍ) {m : ℕ}
    (hm : m ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ)) :
    ∃ γ : MulAction.stabilizer SL(2, ℤ) τ, orderOf γ = m := by
  haveI := isCyclic_stabilizer τ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := MulAction.stabilizer SL(2, ℤ) τ)
  have hord := orderOf_eq_card_of_forall_mem_zpowers hg
  refine ⟨g ^ (orderOf g / m), orderOf_pow_orderOf_div ?_ (hord ▸ hm)⟩
  rw [hord]; exact (card_stabilizer_pos τ).ne'

theorem orderOf_chi (τ : ℍ) (γ : MulAction.stabilizer SL(2, ℤ) τ) :
    orderOf (chi τ γ) = orderOf γ :=
  orderOf_injective _ (chi_injective τ) γ

theorem two_mul_dvd_of_dvd_div_two {e s : ℕ} (h2 : 2 ∣ s) (he : e ∣ s / 2) : 2 * e ∣ s := by
  obtain ⟨t, rfl⟩ := h2
  rw [Nat.mul_div_cancel_left _ two_pos] at he
  exact Nat.mul_dvd_mul_left 2 he


end
end Dubon2026.SourceFunctionField.StabilizerCharacter
