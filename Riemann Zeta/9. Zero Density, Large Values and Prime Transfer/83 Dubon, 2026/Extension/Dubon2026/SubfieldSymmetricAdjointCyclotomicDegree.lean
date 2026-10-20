import Dubon2026.SymmetricAdjointCyclotomicDegree
import Dubon2026.ResidualSubfieldCentralScalar

/-! BLGG Lemma 6.1.2 with its original coefficient-subfield image bounds.
The exact factor-two cyclotomic degree conclusion follows from original
scalar witnesses; no equality of the ambient and image coefficient fields
or projective-simple-group result is assumed. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- The source coefficient-subfield image bounds imply the original factor-two cyclotomic degree bound. -/
theorem subfieldSymmetricAdjoint_cyclotomic_degree_bound
    (K Ω k k' : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Field k] [Field k'] [NeZero (2 : k')] [NeZero (3 : k')]
    (f : k' →+* k) (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k)
    (n l : ℕ) [Fact l.Prime] {z : Ω} (hz : IsPrimitiveRoot z l)
    (hlower : ((GeneralLinearGroup.map f).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := k'))).range ≤ ρ.range)
    (hupper : ∀ g : Gal(Ω/K), ∃ u : kˣ, ∃ a : GeneralLinearGroup (Fin 2) k',
      ρ g = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map f a) :
    let E := IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
    Module.finrank K (originalPrimitiveRootStage K Ω hz) ≤
      2 * Module.finrank E (originalPrimitiveRootStage E Ω hz) := by
  apply symmetricAdjoint_cyclotomic_degree_bound_of_scalar_lifts K Ω k ρ n l hz
  intro g
  obtain ⟨u, a, hga⟩ := hupper g
  exact residualSubfieldGL2_exists_scalar_character_square f ρ (hz.autToPow K) hlower g u a hga

/-- BLGG Lemma 6.1.2's original strict degree conclusion, with the original subfield image conditions and source degree hypothesis; the small-characteristic exclusions are derived. -/
theorem subfieldSymmetricAdjoint_cyclotomic_degree_gt
    (K Ω k k' : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Field k] [Field k'] (l : ℕ) [Fact l.Prime] [CharP k' l]
    (f : k' →+* k) (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k)
    (n m : ℕ) (hm : 0 < m) {z : Ω} (hz : IsPrimitiveRoot z l)
    (hlower : ((GeneralLinearGroup.map f).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := k'))).range ≤ ρ.range)
    (hupper : ∀ g : Gal(Ω/K), ∃ u : kˣ, ∃ a : GeneralLinearGroup (Fin 2) k',
      ρ g = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map f a)
    (hdegree : 2 * m < Module.finrank K (originalPrimitiveRootStage K Ω hz)) :
    let E := IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
    m < Module.finrank E (originalPrimitiveRootStage E Ω hz) := by
  have hp : l.Prime := Fact.out
  have hd := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt)
    (originalPrimitiveRootStage_finrank_dvd K Ω hz)
  have hl3 : 3 < l := by omega
  letI : NeZero (2 : k') := ⟨fun h => by
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((CharP.cast_eq_zero_iff k' l 2).mp h)
    omega⟩
  letI : NeZero (3 : k') := ⟨fun h => by
    have hle := Nat.le_of_dvd (by decide : 0 < 3) ((CharP.cast_eq_zero_iff k' l 3).mp h)
    omega⟩
  have hb := subfieldSymmetricAdjoint_cyclotomic_degree_bound K Ω k k' f ρ n l hz hlower hupper
  dsimp only at hb ⊢
  omega

/-- The original source subfield image conditions and cyclotomic degree greater than two discharge the primitive-root noncontainment input of the smallness-prime construction. -/
theorem subfieldSymmetricAdjoint_primitiveRoot_not_mem_fixedField
    (K Ω k k' : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    [Field k] [Field k'] (l : ℕ) [Fact l.Prime] [CharP k' l]
    (f : k' →+* k) (ρ : Gal(Ω/K) →* GeneralLinearGroup (Fin 2) k)
    (n : ℕ) {z : Ω} (hz : IsPrimitiveRoot z l)
    (hlower : ((GeneralLinearGroup.map f).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := k'))).range ≤ ρ.range)
    (hupper : ∀ g : Gal(Ω/K), ∃ u : kˣ, ∃ a : GeneralLinearGroup (Fin 2) k',
      ρ g = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map f a)
    (hdegree : 2 < Module.finrank K (originalPrimitiveRootStage K Ω hz)) :
    z ∉ IntermediateField.fixedField
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker := by
  let E := IntermediateField.fixedField
    (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp ρ)).asGroupHom.ker
  have hd : 1 < Module.finrank E (originalPrimitiveRootStage E Ω hz) :=
    subfieldSymmetricAdjoint_cyclotomic_degree_gt K Ω k k' l f ρ n 1 (by decide)
      hz hlower hupper (by simpa only [mul_one] using hdegree)
  intro hfixed
  have hzbot : z ∈ (⊥ : IntermediateField E Ω) :=
    IntermediateField.mem_bot.mpr ⟨⟨z, hfixed⟩, rfl⟩
  have hstage : (originalPrimitiveRootStage E Ω hz).toIntermediateField = ⊥ := by
    change IntermediateField.adjoin E ({z} : Set Ω) = ⊥
    exact IntermediateField.adjoin_eq_bot_iff.mpr (Set.singleton_subset_iff.mpr hzbot)
  change 1 < Module.finrank E (originalPrimitiveRootStage E Ω hz).toIntermediateField at hd
  rw [hstage, IntermediateField.finrank_bot] at hd
  exact (lt_irrefl 1) hd

end
end Dubon2026
