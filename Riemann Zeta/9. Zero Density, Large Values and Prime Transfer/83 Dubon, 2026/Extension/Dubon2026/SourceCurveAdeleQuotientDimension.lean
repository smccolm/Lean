import Dubon2026.SourceCurveAdeleLocalQuotient
import Dubon2026.SourceCurveLinearQuotient
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> function-field Riemann--Roch -> index formula. The
quotient between two actual divisor bounds is finite and its dimension
is exactly their degree difference. Induction consumes the proved local
residue-field quotient and the pinned quotient-chain dimension identity.
Adapted from the selected argument in S_AlgebraicCurve_finiteDimensional_lSpace,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finrank_adeleBdd_quotient [∀ v : Place K F, Module.Finite K v.ResidueField] {D₁ D₂ : Divisor K F} (hD : D₁ ≤ D₂) :
    Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
      (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
        = Divisor.degree D₂ - Divisor.degree D₁ := by
  classical

  suffices H : ∀ m : ℕ, ∀ D₁ D₂ : Divisor K F, D₁ ≤ D₂ →
      (Divisor.degree (D₂ - D₁)).toNat = m →
      Module.Finite K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) ∧
        (finrank K (adeleBdd D₂ ⧸ (adeleBdd D₁).comap (adeleBdd D₂).subtype) : ℤ)
          = Divisor.degree D₂ - Divisor.degree D₁ from
    H _ D₁ D₂ hD rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro D₁ D₂ hD hm
    have hEeff : ∀ v, 0 ≤ (D₂ - D₁) v := fun v => by
      rw [Finsupp.sub_apply]; have := hD v; omega
    by_cases hD0 : D₂ - D₁ = 0
    ·
      have hD12 : D₁ = D₂ := (sub_eq_zero.mp hD0).symm
      subst hD12
      rw [Submodule.comap_subtype_self]
      haveI : Subsingleton (adeleBdd D₁ ⧸ (⊤ : Submodule K (adeleBdd D₁))) :=
        Submodule.Quotient.subsingleton_iff.mpr rfl
      exact ⟨Module.Finite.of_finite, by simp [Module.finrank_zero_of_subsingleton]⟩
    ·
      obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD0
      have hPpos : 1 ≤ (D₂ - D₁) P := by
        have hne : (D₂ - D₁) P ≠ 0 := Finsupp.mem_support_iff.mp hP
        have := hEeff P; omega
      set D₂' : Divisor K F := D₂ - Finsupp.single P 1 with hD₂'
      have h12' : D₁ ≤ D₂' := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]
          have := hPpos; rw [Finsupp.sub_apply] at this; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]; exact hD v
      have h2'2 : D₂' ≤ D₂ := by
        intro v; rw [hD₂', Finsupp.sub_apply]
        by_cases hv : v = P
        · subst v; rw [Finsupp.single_eq_same]; omega
        · rw [Finsupp.single_eq_of_ne hv, sub_zero]

      have hdegD₂' : Divisor.degree D₂' = Divisor.degree D₂ - (Module.finrank K P.ResidueField) := by
        rw [hD₂', map_sub, Divisor.degree_single, one_mul]
      have hPdeg1 : 1 ≤ ((Module.finrank K P.ResidueField) : ℤ) := by exact_mod_cast (Module.finrank_pos (R := K) (M := P.ResidueField))
      have hEnn : 0 ≤ Divisor.degree (D₂ - D₁) := Divisor.degree_nonneg_of_nonneg hEeff
      have hE'nn : 0 ≤ Divisor.degree (D₂' - D₁) := Divisor.degree_nonneg_of_nonneg
        (fun v => by rw [Finsupp.sub_apply]; have := h12' v; omega)
      have hdegdiff : Divisor.degree (D₂' - D₁) = Divisor.degree (D₂ - D₁) - (Module.finrank K P.ResidueField) := by
        simp only [hD₂', map_sub, Divisor.degree_single, one_mul]; ring

      have hmlt : (Divisor.degree (D₂' - D₁)).toNat < m := by rw [← hm]; omega
      obtain ⟨hfin', hrank'⟩ := IH _ hmlt D₁ D₂' h12' rfl

      obtain ⟨hfinS, hrankS⟩ := finrank_adeleBdd_quotient_single (K := K) D₂ P
      rw [← hD₂'] at hfinS hrankS

      haveI := hfin'; haveI := hfinS
      obtain ⟨hfin, hrank⟩ := LinearQuotient.finrank_quotient_chain
        (A := adeleBdd D₁) (B := adeleBdd D₂') (C := adeleBdd D₂)
        (adeleBdd_mono h12') (adeleBdd_mono h2'2)
      refine ⟨hfin, ?_⟩
      rw [hrank, hrankS]
      push_cast
      linarith [hrank', hdegD₂']


end
end Dubon2026.SourceCurve
