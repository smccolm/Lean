import Dubon2026.SourceCurveGenusMaximum

/-! DUB-17/18 -> modular good reduction -> genus inequality. A maximizing
divisor need not be supported on the j poles. A nonzero section supplies a
principal shift, so multiples of any positive-degree divisor eventually
reach the same maximum. Adapted from the DeuringLE argument in
S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar_of_five_le,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. The existing principal-shift
equivalence avoids a new family of translated-maximizer lemmas. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F]
variable [∀ v : Place K F, Module.Finite K v.ResidueField]
variable [FiniteDimensional K (LSpace (0 : Divisor K F))]

theorem RiemannGenusReachedAt.exists_forall_degree_nsmul_sub_ell_eq
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : 0 < Divisor.degree D) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Divisor.degree (m • D) - (ell (m • D) : ℤ) = γ - 1 := by
  obtain ⟨m₁, hm₁⟩ : ∃ m₁ : ℕ, Divisor.degree D₀ + γ ≤ (m₁ : ℤ) * Divisor.degree D := by
    refine ⟨(Divisor.degree D₀ + γ).toNat, ?_⟩
    calc Divisor.degree D₀ + γ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) := Int.self_le_toNat _
      _ = ((Divisor.degree D₀ + γ).toNat : ℤ) * 1 := (mul_one _).symm
      _ ≤ ((Divisor.degree D₀ + γ).toNat : ℤ) * Divisor.degree D :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
  refine ⟨m₁, fun m hm => ?_⟩
  have hdegm : Divisor.degree (m • D) = (m : ℤ) * Divisor.degree D := by
    rw [map_nsmul, nsmul_eq_mul]
  have hineq := h.isMax (m • D - D₀)
  have hmm : (m₁ : ℤ) * Divisor.degree D ≤ (m : ℤ) * Divisor.degree D :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hD.le
  have hellpos : 0 < ell (m • D - D₀) := by
    rw [map_sub, hdegm] at hineq
    omega
  have hnebot : LSpace (m • D - D₀) ≠ ⊥ := by
    intro hb
    rw [ell, hb, finrank_bot] at hellpos
    omega
  obtain ⟨f, hfmem, hf0⟩ := (Submodule.ne_bot_iff _).mp hnebot
  obtain ⟨P, hP, hP0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hle : D₀ ≤ m • D + P := by
    intro v
    have hv := (mem_lSpace_iff_ord.mp hfmem).resolve_left hf0 v
    simp only [Finsupp.sub_apply, Finsupp.add_apply] at hv ⊢
    rw [hP]
    linarith
  have he := h.eq_of_ge hle
  have hell : ell (m • D + P) = ell (m • D) :=
    (LinearEquiv.finrank_eq (lSpaceShiftEquiv (m • D) hf0 hP)).symm
  rw [map_add, hP0, add_zero, hell] at he
  exact he

end
end Dubon2026.SourceCurve
