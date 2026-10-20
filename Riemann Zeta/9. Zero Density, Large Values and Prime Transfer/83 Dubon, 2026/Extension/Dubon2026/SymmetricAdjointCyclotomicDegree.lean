import Dubon2026.SymmetricAdjointCyclotomicSeparation
import Dubon2026.CyclotomicCharacterOrder

/-! BLGG Lemma 6.1.2's actual cyclotomic degree conclusion on the full-SL2
residual-image route. The existing scalar witness gives the factor-two
bound directly, without a separate projective-simple-group development. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- Actual central-scalar lifts of squared root-character values bound the cyclotomic degree over the original symmetric-adjoint fixed field. -/
theorem symmetricAdjoint_cyclotomic_degree_bound_of_scalar_lifts
    (K Ω k : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Field k]
    (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k) (n l : ℕ) [Fact l.Prime]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (hlift : ∀ g : Gal(Ω/K), ∃ σ : Gal(Ω/K), ∃ v : kˣ,
      hz.autToPow K σ = hz.autToPow K g ^ 2 ∧ ρ σ = GeneralLinearGroup.scalar (Fin 2) v) :
    let E := IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
    Module.finrank K (originalPrimitiveRootStage K Ω hz) ≤
      2 * Module.finrank E (originalPrimitiveRootStage E Ω hz) := by
  let adρ := (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom
  let E := IntermediateField.fixedField adρ.ker
  change Module.finrank K (originalPrimitiveRootStage K Ω hz) ≤
    2 * Module.finrank E (originalPrimitiveRootStage E Ω hz)
  obtain ⟨g, hg⟩ := primitiveRoot_exists_character_order_eq_degree K Ω l hz
  obtain ⟨σ, v, hχ, hρ⟩ := hlift g
  have hσ : σ ∈ adρ.ker := by
    apply matrixAdjointRepresentation_asGroupHom_eq_one_of_scalar
      ((homogeneousSymmetricGL n).comp ρ) σ (v ^ n)
    change homogeneousSymmetricGL n (ρ σ) = _
    rw [hρ, homogeneousSymmetricGL_scalar_ring]
  have hfix : σ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hx σ hσ
  let σE : Gal(Ω/E) := IntermediateField.fixingSubgroupEquiv E ⟨σ, hfix⟩
  have he : hz.autToPow E σE = hz.autToPow K σ := by
    apply Units.ext
    apply ZMod.val_injective
    apply hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
    rw [hz.autToPow_spec E σE, hz.autToPow_spec K σ]
    rfl
  have hb := primitiveRoot_character_order_le_degree E Ω l hz σE
  rw [he, hχ] at hb
  have htwo : orderOf (hz.autToPow K g) ≤ 2 * orderOf (hz.autToPow K g ^ 2) := by
    rw [orderOf_pow]
    have hd : Nat.gcd (orderOf (hz.autToPow K g)) 2 ≤ 2 :=
      Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right _ _)
    calc
      orderOf (hz.autToPow K g) =
          (orderOf (hz.autToPow K g) / Nat.gcd (orderOf (hz.autToPow K g)) 2) *
            Nat.gcd (orderOf (hz.autToPow K g)) 2 :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      _ ≤ (orderOf (hz.autToPow K g) / Nat.gcd (orderOf (hz.autToPow K g)) 2) * 2 :=
        Nat.mul_le_mul_left _ hd
      _ = _ := Nat.mul_comm _ _
  rw [hg] at htwo
  exact htwo.trans (Nat.mul_le_mul_left 2 hb)

/-- Full SL2 image gives the factor-two bound over the original symmetric-adjoint fixed field. -/
theorem symmetricAdjoint_cyclotomic_degree_bound
    (K Ω k : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Field k]
    [NeZero (2 : k)] [NeZero (3 : k)]
    (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k) (n l : ℕ) [Fact l.Prime]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range ≤ ρ.range) :
    let E := IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
    Module.finrank K (originalPrimitiveRootStage K Ω hz) ≤
      2 * Module.finrank E (originalPrimitiveRootStage E Ω hz) := by
  apply symmetricAdjoint_cyclotomic_degree_bound_of_scalar_lifts K Ω k ρ n l hz
  intro g
  obtain ⟨σ, hχ, hρ⟩ := residualGL2_exists_scalar_character_square ρ (hz.autToPow K) himage g
  exact ⟨σ, GeneralLinearGroup.det (ρ g), hχ, hρ⟩

/-- The source degree hypothesis gives BLGG's strict cyclotomic degree bound over the actual symmetric-adjoint fixed field. -/
theorem symmetricAdjoint_cyclotomic_degree_gt
    (K Ω k : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Field k]
    [NeZero (2 : k)] [NeZero (3 : k)]
    (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k) (n l m : ℕ) [Fact l.Prime]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range ≤ ρ.range)
    (hdegree : 2 * m < Module.finrank K (originalPrimitiveRootStage K Ω hz)) :
    let E := IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
    m < Module.finrank E (originalPrimitiveRootStage E Ω hz) := by
  have h := symmetricAdjoint_cyclotomic_degree_bound K Ω k ρ n l hz himage
  dsimp only at h ⊢
  omega

/-- An explicit large-prime bound over the original number field supplies the source strict cyclotomic degree condition over the actual adjoint fixed field. -/
theorem numberField_symmetricAdjoint_cyclotomic_degree_gt
    (K Ω k : Type) [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsGalois K Ω] [Field k]
    [NeZero (2 : k)] [NeZero (3 : k)]
    (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k) (n l m : ℕ) [Fact l.Prime]
    {z : Ω} (hz : IsPrimitiveRoot z l)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range ≤ ρ.range)
    (hlarge : (2 * m) * Module.finrank ℚ K < l - 1) :
    let E := IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
    m < Module.finrank E (originalPrimitiveRootStage E Ω hz) := by
  apply symmetricAdjoint_cyclotomic_degree_gt K Ω k ρ n l m hz himage
  let F := originalPrimitiveRootStage K Ω hz
  letI : NumberField F := NumberField.of_module_finite K F
  exact numberField_cyclotomic_degree_gt K F l (2 * m) Fact.out hlarge
    (originalPrimitiveRootStageRoot K Ω hz) (originalPrimitiveRootStageRoot_isPrimitive K Ω hz)

end
end Dubon2026
