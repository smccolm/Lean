import Dubon2026.CyclotomicPrimeDegree
import Dubon2026.FiniteBaseGaloisTopology
import Dubon2026.CoprimeIndexCharacterRestriction
import Mathlib.Topology.Instances.ZMod

/-! # Actual continuous prime-order characters descend from the genuine cyclotomic base -/

namespace Dubon2026

noncomputable section

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- Original continuous prime-order character finiteness over an actual prime cyclotomic intermediate field implies the same finiteness over the original base field. -/
theorem cyclotomic_continuous_prime_characters_finite
    (p : ℕ) (hp : p.Prime) (F : IntermediateField K Ω)
    [IsCyclotomicExtension {p} K F]
    [Finite (Gal(Ω/F) →ₜ* Multiplicative (ZMod p))] :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI := IsCyclotomicExtension.finiteDimensional {p} K F
  letI := IsCyclotomicExtension.isGalois {p} K F
  letI : F.fixingSubgroup.Normal := (InfiniteGalois.normal_iff_isGalois F).mpr inferInstance
  letI := finiteBase_fixingSubgroup_characters_finite
    (T := Multiplicative (ZMod p)) F
  apply coprime_quotient_continuous_characters_finite F.fixingSubgroup
  have hcard : Nat.card (Gal(Ω/K) ⧸ F.fixingSubgroup) = Module.finrank K F := by
    rw [← Subgroup.index_eq_card, ← F.finrank_eq_fixingSubgroup_index]
  have htarget : Nat.card (Multiplicative (ZMod p)) = p := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [hcard, htarget]
  exact cyclotomic_prime_finrank_coprime (K := K) (L := F) p hp

end
end Dubon2026
