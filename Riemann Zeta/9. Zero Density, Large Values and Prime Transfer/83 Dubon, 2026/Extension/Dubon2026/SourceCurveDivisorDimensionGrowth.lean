import Dubon2026.SourceCurveAdeleQuotientDimension

/-! DUB-17/18 -> function-field Riemann--Roch -> stabilization of degree
minus divisor-space dimension. The diagonal map injects each global
divisor-space increment into the corresponding local quotient, giving the
required monotonicity bound. Adapted from the selected argument in
S_AlgebraicCurve_finiteDimensional_lSpace, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The dimension of the actual divisor space, in the source notation. -/
abbrev ell (D : Divisor K F) : ℕ := Module.finrank K (LSpace D)

/-- The quotient of global divisor spaces embeds into the local bound quotient. -/
def lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} :
    (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      →ₗ[K] (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
  Submodule.mapQ _ _
    ((diagonalHom K F).restrict
      (p := (LSpace D₂ : Submodule K F)) (q := (adeleBdd D₂ : Submodule K _))
      (fun f hf => diagonal_mem_adeleBdd_iff.mpr hf))
    (fun f hf => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hf ⊢
      exact diagonal_mem_adeleBdd_iff.mpr hf)

theorem lSpaceQuotientToAdeleBddQuotient_injective {D₁ D₂ : Divisor K F} :
    Function.Injective (lSpaceQuotientToAdeleBddQuotient (D₁ := D₁) (D₂ := D₂)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]

  rw [show (lSpaceQuotientToAdeleBddQuotient (D₁ := D₁) (D₂ := D₂)) (Submodule.Quotient.mk f)
        = Submodule.Quotient.mk ((diagonalHom K F).restrict
            (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f) from rfl,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at hx
  exact diagonal_mem_adeleBdd_iff.mp hx


theorem ell_sub_ell_le_degree_sub_degree [∀ v : Place K F, Module.Finite K v.ResidueField] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)] :
    (ell D₂ : ℤ) - (ell D₁ : ℤ) ≤ Divisor.degree D₂ - Divisor.degree D₁ := by
  haveI := (finrank_adeleBdd_quotient hD).1

  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    rw [hℓ₁]; exact (Submodule.finrank_quotient_add_finrank _).symm

  have hemb : finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype)
      ≤ finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) :=
    LinearMap.finrank_le_finrank_of_injective (lSpaceQuotientToAdeleBddQuotient_injective (D₁ := D₁) (D₂ := D₂))
  have hloc := (finrank_adeleBdd_quotient hD).2
  have : (ell D₂ : ℤ) - (ell D₁ : ℤ)
      = (finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) : ℤ) := by
    rw [hL]; push_cast; ring
  rw [this, ← hloc]
  exact_mod_cast hemb

theorem adeleBdd_inf_sup_globalSub {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F)
      = adeleBdd D₁ ⊔ adeleBdd D₂ ⊓ globalSub K F := by
  rw [inf_comm, sup_inf_assoc_of_le _ (adeleBdd_mono hD), inf_comm]

theorem map_diagonal_lSpace_inf_adeleBdd {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    (LSpace D₂).map (diagonalHom K F) ⊓ adeleBdd D₁ = (LSpace D₁).map (diagonalHom K F) := by
  rw [map_diagonal_lSpace, map_diagonal_lSpace, inf_right_comm,
    inf_eq_right.mpr (adeleBdd_mono hD)]


end
end Dubon2026.SourceCurve
