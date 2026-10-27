import Dubon2026.SourceFrickeStableEmbeddingV2

/-! DUB-17/18 -> original all-weight arithmetic association -> actual finite Gamma1
character realization -> Picard/H1 and diamond comparison -> cusp differential
realization -> rational Fourier structure -> fraction realization of modularly
stable finite-pole families. This uses the actual Fricke algebra and native
finite fixed-field degree; no rational representation is assumed.
Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache License 2.0. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SourceFunctionField Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Manifold IntermediateField
local notation "j" => JMultiplicity.jf

namespace LevelGens
variable {N : ℕ} [NeZero N] (D : LevelGens N)

theorem finrank_ratJN_field : Module.finrank ↥(ℂ⟮Dubon2026.SourceFricke.jK N⟯) D.field = (levelFixer N).index := by
  rw [← D.finrank_ratJ]
  refine Algebra.finrank_eq_of_equiv_equiv D.ratJEquiv.toRingEquiv (RingEquiv.refl D.field) ?_
  ext x
  rfl

theorem finrank_levelField_field : Module.finrank (levelField N) D.field = 1 := by
  haveI : Module.Free (levelField N) D.field := Module.Free.of_divisionRing _ _
  haveI : Module.Free ↥(ℂ⟮Dubon2026.SourceFricke.jK N⟯) (levelField N) := Module.Free.of_divisionRing _ _
  have h := Module.finrank_mul_finrank ↥(ℂ⟮Dubon2026.SourceFricke.jK N⟯) (levelField N) D.field
  rw [finrank_ratJN_field, finrank_adjoin_j_levelField] at h
  have hpos : 0 < (levelFixer N).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have : (levelFixer N).index * Module.finrank (levelField N) D.field = (levelFixer N).index * 1 := by
    rw [h, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem toField_surjective : Function.Surjective D.toField := by
  intro x
  haveI : Module.Free (levelField N) D.field := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional (levelField N) D.field :=
    Module.finite_of_finrank_pos (by rw [finrank_levelField_field]; exact one_pos)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : D.field) one_ne_zero).mp
    D.finrank_levelField_field x
  refine ⟨c, ?_⟩
  rw [← hc, Algebra.smul_def, mul_one]
  rfl

theorem exists_frac {F : ℍ → ℂ} (hF : F ∈ D.S) :
    ∃ a b : ↥(levelRing N), b ≠ 0 ∧ F * b = a := by
  obtain ⟨y, hy⟩ := D.toField_surjective (algebraMap ↥D.ring D.field ⟨F, Algebra.subset_adjoin hF⟩)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ↥(levelRing N)) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨a, b, hb0, ?_⟩
  rw [map_div₀, toField_algebraMap, toField_algebraMap, div_eq_iff
    ((map_ne_zero_iff _ (IsFractionRing.injective ↥D.ring D.field)).mpr
      ((map_ne_zero_iff _ D.incl_injective).mpr hb0)), ← map_mul] at hy
  have := congrArg Subtype.val (IsFractionRing.injective ↥D.ring D.field hy)
  rw [Subalgebra.coe_mul, coe_incl, coe_incl] at this
  exact this.symm

end LevelGens

theorem exists_levelRing_frac {N : ℕ} [NeZero N] {S : Set (ℍ → ℂ)}
    (hpb : ∀ G ∈ S, PoleBounded G) (hst : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, γ • G ∈ S)
    (hinv : ∀ G ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    {F : ℍ → ℂ} (hF : F ∈ S) : ∃ a b : ↥(levelRing N), b ≠ 0 ∧ F * b = a := by
  let D : LevelGens N :=
    { S := levelGen N ∪ S
      levelGen_subset := Set.subset_union_left
      poleBounded := fun f hf ↦ hf.elim (levelGen_poleBounded N f) (hpb f)
      smul_mem := fun γ f hf ↦ hf.elim (fun h ↦ Or.inl (smul_mem_levelGen γ h))
        (fun h ↦ Or.inr (hst γ f h))
      invariant := fun f hf ↦ hf.elim ((LevelGens.std N).invariant f) (hinv f) }
  exact D.exists_frac (Or.inr hF)

end
end Dubon2026.SourceFricke
