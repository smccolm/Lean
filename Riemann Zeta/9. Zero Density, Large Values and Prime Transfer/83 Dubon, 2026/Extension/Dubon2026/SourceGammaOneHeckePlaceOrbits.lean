import Dubon2026.SourceGammaOneHeckeAllFibers

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> geometric
fiber multiplicities. The all-fiber bijection now identifies actual
intersection-field places with actual intersection-subgroup orbits at
every point. Central signs act trivially and are removed by the existing
plus/minus orbit lemma. No generic-point assumption remains. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceCurve
open scoped MatrixGroups StabilizerCharacter GammaOne
variable (M d : ℕ) [NeZero M] [NeZero d]
  (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M))

omit [NeZero M] [NeZero d] in
theorem toFiber_mk_val (τ σ : ℍ) (hσ : σ ∈ MulAction.orbit SL(2, ℤ) τ) :
    (toFiber M d hT τ (Quotient.mk _ (⟨σ, hσ⟩ : MulAction.orbit SL(2, ℤ) τ))).val =
      analyticPlace hT σ := by
  obtain ⟨γ, hγ, hγσ⟩ :=
    OrbitCounting.exists_smul_out_eq (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) τ ⟨σ, hσ⟩
  change analyticPlace hT (rep M d τ (Quotient.mk _ ⟨σ, hσ⟩)) = _
  rw [← analyticPlace_smul_plusMinus hT hγ]
  exact congrArg (analyticPlace hT) hγσ

theorem analyticHeckePlace_eq_iff_orbit (τ τ' : ℍ) :
    analyticPlace hT τ = analyticPlace hT τ' ↔
      ∃ γ : ↥(Gamma1 M ⊓ Gamma0 (d * M)), (γ : SL(2, ℤ)) • τ = τ' := by
  constructor
  · intro he
    have hΓ : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
    have hα := congrArg
      (Place.restrictAlong (heckeAlpha ℂ M d) (heckeAlpha_finite ℂ M d)) he
    rw [analyticPlace_restrict_heckeAlpha M d hΓ hT,
      analyticPlace_restrict_heckeAlpha M d hΓ hT] at hα
    obtain ⟨g, hg⟩ := (analyticPlace_eq_iff_gamma1_orbit M hΓ τ τ').mp hα
    have hτ : τ ∈ MulAction.orbit SL(2, ℤ) τ := MulAction.mem_orbit_self τ
    have hτ' : τ' ∈ MulAction.orbit SL(2, ℤ) τ :=
      MulAction.mem_orbit_iff.mpr ⟨g.val, hg⟩
    let u : MulAction.orbit SL(2, ℤ) τ := ⟨τ, hτ⟩
    let v : MulAction.orbit SL(2, ℤ) τ := ⟨τ', hτ'⟩
    have hq : (Quotient.mk _ u : OrbitQuot M d τ) = Quotient.mk _ v := by
      apply (toFiber_bijective M d hT τ).injective
      apply Subtype.ext
      exact (toFiber_mk_val M d hT τ τ hτ).trans
        (he.trans (toFiber_mk_val M d hT τ τ' hτ').symm)
    have hrel := Quotient.exact hq.symm
    change v ∈ MulAction.orbit (plusMinus (Gamma1 M ⊓ Gamma0 (d * M))) u at hrel
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hrel
    obtain ⟨δ, hδ⟩ := exists_gamma_smul_eq_of_mem_plusMinus
      (Gamma1 M ⊓ Gamma0 (d * M)) γ.property τ
    exact ⟨δ, hδ.trans (congrArg Subtype.val hγ)⟩
  · rintro ⟨γ, rfl⟩
    exact (analyticPlace_smul hT γ τ).symm

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
