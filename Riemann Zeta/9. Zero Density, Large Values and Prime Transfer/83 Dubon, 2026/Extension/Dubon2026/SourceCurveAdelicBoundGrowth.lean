import Dubon2026.SourceCurveDivisorDimensionGrowth

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

theorem range_lSpaceQuotientToAdeleBddQuotient {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    LinearMap.range (lSpaceQuotientToAdeleBddQuotient (D₁ := D₁) (D₂ := D₂))
      = ((adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype).map
          ((adeleBdd D₁).comap (adeleBdd D₂).subtype).mkQ := by
  classical
  ext z
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  simp only [LinearMap.mem_range, Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.mkQ_apply]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x

    have hxeq : Submodule.Quotient.mk
        ((diagonalHom K F).restrict (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) f)
        = (Submodule.Quotient.mk α :
            adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) := hx
    refine ⟨α, ?_, rfl⟩

    have hdiag2 : (diagonalHom K F (f : F)) ∈ adeleBdd D₂ := diagonal_mem_adeleBdd_iff.mpr f.2
    have hsub : (α : Place K F → F) - diagonalHom K F (f : F) ∈ adeleBdd D₁ := by
      have hq := (Submodule.Quotient.eq _).mp hxeq.symm
      simpa using hq
    refine Submodule.mem_sup.mpr ⟨(α : Place K F → F) - diagonalHom K F (f : F), hsub,
      diagonalHom K F (f : F), diagonal_mem_globalSub _, ?_⟩
    abel
  · rintro ⟨β, hβ, hβeq⟩

    have hβ' : (β : Place K F → F) ∈ adeleBdd D₂ ⊓ (adeleBdd D₁ ⊔ globalSub K F) :=
      Submodule.mem_inf.mpr ⟨β.2, hβ⟩
    rw [adeleBdd_inf_sup_globalSub hD, ← map_diagonal_lSpace] at hβ'
    obtain ⟨γ, hγ, δ, ⟨f, hf, hfδ⟩, hsum⟩ := Submodule.mem_sup.mp hβ'
    refine ⟨Submodule.Quotient.mk ⟨f, hf⟩, ?_⟩
    rw [show (lSpaceQuotientToAdeleBddQuotient (D₁ := D₁) (D₂ := D₂)) (Submodule.Quotient.mk ⟨f, hf⟩)
          = Submodule.Quotient.mk ((diagonalHom K F).restrict
              (fun g hg => diagonal_mem_adeleBdd_iff.mpr hg) ⟨f, hf⟩) from rfl,
      ← hβeq, Submodule.Quotient.eq]

    refine Submodule.mem_comap.mpr ?_
    show diagonalHom K F f - (β : Place K F → F) ∈ adeleBdd D₁
    have hβsub : diagonalHom K F f - (β : Place K F → F) = -γ := by
      rw [← hsum, hfδ]; ring
    rw [hβsub]; exact (adeleBdd D₁).neg_mem hγ


theorem finrank_adeleBddSup_quotient [∀ v : Place K F, Module.Finite K v.ResidueField]
    {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) [hL : FiniteDimensional K (LSpace D₂)] :
    Module.Finite K (↥(adeleBdd D₂ ⊔ globalSub K F)
        ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) ∧
      (finrank K (↥(adeleBdd D₂ ⊔ globalSub K F)
          ⧸ (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂ ⊔ globalSub K F).subtype) : ℤ)
        = (Divisor.degree D₂ - ell D₂) - (Divisor.degree D₁ - ell D₁) := by
  classical

  let A : Submodule K (adeleBdd D₂) := (adeleBdd D₁).comap (adeleBdd D₂).subtype
  let B : Submodule K (adeleBdd D₂) :=
    (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype
  have hAB : A ≤ B := Submodule.comap_mono le_sup_left

  haveI hfinA : Module.Finite K (adeleBdd D₂ ⧸ A) := (finrank_adeleBdd_quotient hD).1
  have hdimA : (finrank K (adeleBdd D₂ ⧸ A) : ℤ) = Divisor.degree D₂ - Divisor.degree D₁ :=
    (finrank_adeleBdd_quotient hD).2

  have hran : LinearMap.range (lSpaceQuotientToAdeleBddQuotient (D₁ := D₁) (D₂ := D₂)) = B.map A.mkQ :=
    range_lSpaceQuotientToAdeleBddQuotient hD
  have hℓ₁ : ell D₁ = finrank K ((LSpace D₁).comap (LSpace D₂).subtype) :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (lSpace_mono hD))).symm
  have hdimL : ell D₂
      = finrank K (LSpace D₂ ⧸ (LSpace D₁).comap (LSpace D₂).subtype) + ell D₁ := by
    have h := Submodule.finrank_quotient_add_finrank (R := K)
      ((LSpace D₁).comap (LSpace D₂).subtype)
    rw [← hℓ₁] at h; exact h.symm
  have hdimB : ell D₂ = finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) + ell D₁ := by
    rw [← hran, LinearMap.finrank_range_of_inj
      (lSpaceQuotientToAdeleBddQuotient_injective (D₁ := D₁) (D₂ := D₂))]
    exact hdimL

  have e3 := Submodule.quotientQuotientEquivQuotient A B hAB
  haveI hfinB : Module.Finite K (adeleBdd D₂ ⧸ B) := Module.Finite.equiv e3
  have hdim2 : finrank K (adeleBdd D₂ ⧸ A)
      = finrank K (adeleBdd D₂ ⧸ B) + finrank K (B.map A.mkQ : Submodule K _) := by
    have h := Submodule.finrank_quotient_add_finrank (R := K) (M := adeleBdd D₂ ⧸ A)
      (B.map A.mkQ)
    rw [LinearEquiv.finrank_eq e3] at h; omega

  have e2 := LinearMap.quotientInfEquivSupQuotient (R := K)
    (adeleBdd D₂) (adeleBdd D₁ ⊔ globalSub K F)

  have hsup : adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F) = adeleBdd D₂ ⊔ globalSub K F := by
    rw [← sup_assoc, sup_eq_left.mpr (adeleBdd_mono hD)]
  have hB' : (adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
      (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype = B := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  let eL : (adeleBdd D₂ ⧸ B) ≃ₗ[K]
      (adeleBdd D₂ ⧸ ((adeleBdd D₂).comap (adeleBdd D₂).subtype ⊓
        (adeleBdd D₁ ⊔ globalSub K F).comap (adeleBdd D₂).subtype)) :=
    Submodule.quotEquivOfEq _ _ hB'.symm

  have hfin_iso : Module.Finite K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype) :=
    Module.Finite.equiv (eL.trans e2)
  have hdim_iso : finrank K (↥(adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)) ⧸
        (adeleBdd D₁ ⊔ globalSub K F).comap
          (adeleBdd D₂ ⊔ (adeleBdd D₁ ⊔ globalSub K F)).subtype)
      = finrank K (adeleBdd D₂ ⧸ B) :=
    (LinearEquiv.finrank_eq (eL.trans e2)).symm

  have hcast : (finrank K (adeleBdd D₂ ⧸ A) : ℤ)
      = (finrank K (adeleBdd D₂ ⧸ B) : ℤ) + ((ell D₂ : ℤ) - (ell D₁ : ℤ)) := by
    have hb : (ell D₂ : ℤ)
        = (finrank K (B.map A.mkQ : Submodule K (adeleBdd D₂ ⧸ A)) : ℤ) + (ell D₁ : ℤ) := by
      exact_mod_cast hdimB
    push_cast [hdim2]; linarith
  have hgoal : (finrank K (adeleBdd D₂ ⧸ B) : ℤ)
      = Divisor.degree D₂ - ↑(ell D₂) - (Divisor.degree D₁ - ↑(ell D₁)) := by
    linarith [hdimA, hcast]

  clear_value eL
  exact hsup ▸ ⟨hfin_iso, by rw [hdim_iso]; exact hgoal⟩

end
end Dubon2026.SourceCurve
