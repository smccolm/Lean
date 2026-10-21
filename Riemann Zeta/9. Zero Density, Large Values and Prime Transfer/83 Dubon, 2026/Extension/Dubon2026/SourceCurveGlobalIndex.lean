import Dubon2026.SourceCurveAdelicBoundGrowth
import Dubon2026.SourceCurveAdelicIndex
import Dubon2026.SourceCurveGenusMaximum

/-! DUB-17/18 -> original parabolic Hecke realization -> period surjectivity
-> matching cusp-form dimension -> regular differential dimension ->
function-field Riemann--Roch. These proofs establish the actual global
repartition index formula from the already proved degree-dimension maximum.
Residue duality and identification with canonical genus remain required.
Selected proofs adapted from S_AlgebraicCurve_finiteDimensional_lSpace,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. No imported proof options.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem globalSub_le_adeleSpace [HasPrincipalDivisors K F] :
    globalSub K F ≤ adeleSpace K F := by
  rintro _ ⟨f, rfl⟩
  exact diagonal_mem_adeleSpace f

theorem adeleBdd_sup_globalSub_le_adeleSpace [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBdd D ⊔ globalSub K F ≤ adeleSpace K F :=
  sup_le adeleBdd_le_adeleSpace globalSub_le_adeleSpace

theorem adeleBddPrincipal_eq_comap [HasPrincipalDivisors K F] (D : Divisor K F) :
    adeleBddPrincipal K F D = (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype :=
by
  apply Eq.symm
  apply Submodule.comap_sup_of_injective (adeleSpace K F).subtype_injective
  · simpa only [Submodule.range_subtype] using (adeleBdd_le_adeleSpace (D := D))
  · simpa only [Submodule.range_subtype] using (globalSub_le_adeleSpace (K := K) (F := F))

theorem adeleBddPrincipal_mono {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    adeleBddPrincipal K F D₁ ≤ adeleBddPrincipal K F D₂ :=
  sup_le_sup_right (Submodule.comap_mono (adeleBdd_mono hD)) _

theorem adeleBddSup_eq_of_degree_sub_ell_eq
    [∀ v : Place K F, Module.Finite K v.ResidueField] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂)
    [FiniteDimensional K (LSpace D₂)]
    (heq : Divisor.degree D₂ - ell D₂ = Divisor.degree D₁ - ell D₁) :
    adeleBdd D₂ ⊔ globalSub K F = adeleBdd D₁ ⊔ globalSub K F := by
  obtain ⟨hfin, hdim⟩ := finrank_adeleBddSup_quotient hD
  rw [heq, sub_self] at hdim

  refine le_antisymm ?_ (sup_le_sup_right (adeleBdd_mono hD) _)
  haveI := hfin
  have hd0 : finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) = 0 := by
    exact_mod_cast hdim
  have hsub : Subsingleton (↥(adeleBdd D₂ ⊔ globalSub K F)
      ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) :=
    Module.finrank_zero_iff.mp hd0
  have htop := Submodule.Quotient.subsingleton_iff.mp hsub
  intro x hx
  have hxc : (⟨x, hx⟩ : ↥(adeleBdd D₂ ⊔ globalSub K F)) ∈
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hxc

theorem adeleSpace_eq_of_genusReached [HasPrincipalDivisors K F]
    [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    adeleSpace K F = adeleBdd D₀ ⊔ globalSub K F := by
  refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace D₀)

  rw [adeleSpace, iSup_le_iff]
  intro D
  refine le_trans (adeleBdd_mono (le_sup_left : D ≤ D ⊔ D₀)) ?_
  haveI := finite_lSpace (K := K) (D ⊔ D₀)
  have heq : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = Divisor.degree D₀ - ell D₀ :=
    (h.eq_of_ge le_sup_right).trans h.eq.symm
  have hsup := adeleBddSup_eq_of_degree_sub_ell_eq (K := K)
    (le_sup_right : D₀ ≤ D ⊔ D₀) heq
  rw [← hsup]
  exact le_sup_left

theorem indexOfSpecialty_eq_zero_of_genusReached [HasPrincipalDivisors K F]
    [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) :
    indexOfSpecialty D₀ = 0 := by
  rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap, ← adeleSpace_eq_of_genusReached h,
    Submodule.comap_subtype_self]
  haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
    Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Module.finrank_zero_of_subsingleton


theorem indexOfSpecialty_eq_of_genusReached [HasPrincipalDivisors K F]
    [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) ∧
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - γ) := by
  classical

  have hDD' : D ≤ D ⊔ D₀ := le_sup_left
  have hD0D' : D₀ ≤ D ⊔ D₀ := le_sup_right
  haveI := finite_lSpace (K := K) (D ⊔ D₀)

  have heqD' : Divisor.degree (D ⊔ D₀) - ell (D ⊔ D₀) = γ - 1 := h.eq_of_ge hD0D'
  have hsa : adeleSpace K F = adeleBdd (D ⊔ D₀) ⊔ globalSub K F := by
    refine le_antisymm ?_ (adeleBdd_sup_globalSub_le_adeleSpace _)
    rw [adeleSpace_eq_of_genusReached h]
    exact sup_le_sup_right (adeleBdd_mono hD0D') _

  have hABsub : adeleBdd D ⊔ globalSub K F ≤ adeleBdd (D ⊔ D₀) ⊔ globalSub K F :=
    sup_le_sup_right (adeleBdd_mono hDD') _
  have hBCsub : adeleBdd (D ⊔ D₀) ⊔ globalSub K F ≤ adeleSpace K F :=
    adeleBdd_sup_globalSub_le_adeleSpace _

  have hCB : (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype = ⊤ := by
    rw [← hsa, Submodule.comap_subtype_self]
  haveI hfinCB : Module.Finite K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [hCB]
    haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.Finite.of_finite
  have hdimCB : finrank K (adeleSpace K F ⧸
      (adeleBdd (D ⊔ D₀) ⊔ globalSub K F).comap (adeleSpace K F).subtype) = 0 := by
    rw [hCB]
    haveI : Subsingleton (adeleSpace K F ⧸ (⊤ : Submodule K (adeleSpace K F))) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Module.finrank_zero_of_subsingleton

  obtain ⟨hfinBA, hdimBA⟩ := finrank_adeleBddSup_quotient (K := K) hDD'

  haveI := hfinBA
  obtain ⟨hfinCA, hdimCA⟩ := LinearQuotient.finrank_quotient_chain
    (A := adeleBdd D ⊔ globalSub K F) (B := adeleBdd (D ⊔ D₀) ⊔ globalSub K F)
    (C := adeleSpace K F) hABsub hBCsub

  have hieq : indexOfSpecialty D
      = finrank K (adeleSpace K F ⧸
        (adeleBdd D ⊔ globalSub K F).comap (adeleSpace K F).subtype) := by
    rw [indexOfSpecialty_eq, adeleBddPrincipal_eq_comap]
  rw [adeleBddPrincipal_eq_comap]
  refine ⟨hfinCA, ?_⟩
  rw [hieq]
  push_cast [hdimCA, hdimCB]
  linarith [hdimBA, heqD']

end
end Dubon2026.SourceCurve
