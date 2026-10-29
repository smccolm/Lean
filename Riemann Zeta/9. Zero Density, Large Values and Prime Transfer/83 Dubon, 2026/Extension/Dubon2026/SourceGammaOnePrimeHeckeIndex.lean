import Dubon2026.SourcePrincipalCoprimeReduction
import Dubon2026.SourceLevelIndexFormula
import Dubon2026.SourceLevelPsiPrimeStep
import Dubon2026.SourceGammaOnePlusMinus

/-! DUB-17/18 -> original arithmetic association -> Gamma1 Picard/Tate
Frobenius -> actual Hecke norm identity -> completeness of the embedding
list. Native coprime principal-level lifting and the proved Gamma0 index
give the exact lower correspondence index. No field-degree equality,
embedding completeness or norm formula is assumed or asserted here.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup SourceLevelProjective
open scoped MatrixGroups

theorem gammaOneReduction_surjective (M n : ℕ) [NeZero M] [NeZero n]
    (h : Nat.Coprime M n) :
    Function.Surjective
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))).comp (Gamma1 M).subtype) := by
  intro B
  obtain ⟨a, ha⟩ := sourcePrincipalReduction_surjective M n h B
  have hg := Gamma_mem.mp a.property
  exact ⟨⟨a.val, (Gamma1_mem _ _).mpr ⟨hg.1, hg.2.2.2, hg.2.2.1⟩⟩, ha⟩

private theorem borel_index_eq_gamma0 (n : ℕ) [NeZero n] :
    (borel (ZMod n)).index = (Gamma0 n).index := by
  have he : Gamma0 n = (borel (ZMod n)).comap
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod n))) := by
    ext g
    rw [Gamma0_mem, Subgroup.mem_comap, mem_borel_iff]
    rfl
  rw [he]
  exact (Subgroup.index_comap_of_surjective _ (SL2Reduction.SL2_reduction_surjective n)).symm

theorem gammaOne_lower_subgroup_eq_borel_comap (M n : ℕ)
    (h : Nat.Coprime n M) :
    (Gamma1 M ⊓ Gamma0 (n * M)).subgroupOf (Gamma1 M) =
      (borel (ZMod n)).comap
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))).comp (Gamma1 M).subtype) := by
  ext g
  change (g.val ∈ Gamma1 M ∧ g.val ∈ Gamma0 (n * M)) ↔ _
  rw [and_iff_right g.property]
  change g.val ∈ Gamma0 (n * M) ↔ ((g.val 1 0 : ℤ) : ZMod n) = 0
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Nat.cast_mul]
  have hM : (M : ℤ) ∣ g.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem M g.val).mp g.property).2.2
  exact ⟨fun hn => dvd_trans (dvd_mul_right (n : ℤ) M) hn,
    fun hn => (Nat.isCoprime_iff_coprime.mpr h).mul_dvd hn hM⟩

theorem gammaOne_prime_lower_relIndex (M p : ℕ) [NeZero M] [Fact p.Prime]
    (h : Nat.Coprime p M) :
    (Gamma1 M ⊓ Gamma0 (p * M)).relIndex (Gamma1 M) = p + 1 := by
  rw [Subgroup.relIndex, gammaOne_lower_subgroup_eq_borel_comap M p h,
    Subgroup.index_comap_of_surjective _ (gammaOneReduction_surjective M p h.symm),
    borel_index_eq_gamma0, gamma0_index, dedekindPsi_prime p Fact.out]

end
end Dubon2026.SourceFunctionField.GammaOne
