import Dubon2026.SourceCurveTameUniformizerData
import Dubon2026.SourceCurveOrderFiltration
import Dubon2026.SourceCurveClosedConstantResidue
import Dubon2026.SourceCurveLocalJetDimension
import Dubon2026.TameInertiaCharacter

/-! The actual valuation-ring decomposition group has a residue-unit
character whose kernel moves the chosen uniformizer by order at least two.
Existing constant-residue inertia, tame-character and ideal-power order
theorems discharge the character and displacement inputs of the DUB-17/18
wild different criterion. No finite-residue-field hypothesis is used. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing IntermediateField
variable {K F M : Type*} [Field K] [IsAlgClosed K] [Field F] [Field M]
variable [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]
variable (t : M) [FiniteDimensional K⟮t⟯ M] (v : Place K M)

include t

theorem decomposition_mem_maximalIdeal_inertia
    (σ : v.toValuationSubring.decompositionSubgroup F) :
    σ ∈ (maximalIdeal v.toValuationSubring).inertia
      (v.toValuationSubring.decompositionSubgroup F) := by
  have hσ := mem_inertia_of_decomposition_of_finite_coordinate t v σ.property
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hσ
  intro b
  apply (residue_eq_zero_iff _).mp
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [IsLocalRing.ResidueField.residue_smul]
  exact congrArg (fun e : v.ResidueField ≃+* v.ResidueField => e (residue _ b)) hσ

theorem exists_decomposition_residue_character :
    ∃ χ : v.toValuationSubring.decompositionSubgroup F →* Kˣ,
      ∀ σ, χ σ = 1 →
        v.OrdGe 2 (v.uniformizer - (σ : M ≃ₐ[F] M) v.uniformizer) := by
  let G := v.toValuationSubring.decompositionSubgroup F
  let m := maximalIdeal v.toValuationSubring
  let i : G →* m.inertia G :=
    { toFun := fun σ => ⟨σ, decomposition_mem_maximalIdeal_inertia t v σ⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let θ := TameKernel.tameChar (G := G) m v.uniformizer_mem_maximalIdeal
    v.uniformizer_generates_mod_square v.uniformizer_regular_mod_square
  let e := Units.mapEquiv (residueConstantEquiv t v).toMulEquiv
  refine ⟨e.toMonoidHom.comp (θ.comp i), ?_⟩
  intro σ hσ
  have hθ : θ (i σ) = 1 := e.injective (hσ.trans e.map_one.symm)
  have hm := (TameKernel.tameChar_eq_one_iff m v.uniformizer_mem_maximalIdeal
    v.uniformizer_generates_mod_square v.uniformizer_regular_mod_square (i σ)).mp hθ
  have horder := v.le_ord_of_mem_maximalIdeal_pow 2
    (σ • v.uniformizerSubring - v.uniformizerSubring) hm
  have hpos : v.OrdGe 2 ((σ : M ≃ₐ[F] M) v.uniformizer - v.uniformizer) := horder
  simpa only [neg_sub] using hpos.neg

end
end Dubon2026.SourceCurve.Place
