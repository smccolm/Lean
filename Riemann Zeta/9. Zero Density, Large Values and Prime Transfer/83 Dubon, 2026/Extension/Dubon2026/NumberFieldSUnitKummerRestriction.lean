/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Cardinality argument adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/KummerTheory/Concrete/SUnitPreparation/Core.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.FiniteAbelianSUnitKummerContainment
import Dubon2026.NumberFieldSUnitKummerDegree

/-! # Actual S-unit Kummer restriction and its exact kernel

The field and its containment are produced from the prescribed extension.
The map is literal restriction of automorphisms along the original field
inclusion. Its surjectivity and the proved Kummer degree calculate the
kernel, removing those hypotheses from DUB-17's global prime-selection
and cyclic norm-index dependency.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField IsMulCommutative
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

/-- A finite enlargement produces the actual surjective Kummer restriction, rank bound and exact kernel size. -/
theorem numberField_exists_sUnit_kummer_restriction
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ) (hn : 1 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n)
    (hexp : ∀ g : Gal(E/K), g ^ n = 1)
    (r : ℕ) (hcard : Nat.card Gal(E/K) = n ^ r)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K)))
      (hE : E ≤ originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)),
      S₀ ⊆ S ∧
      let N := originalKummerRadicalField (Ω := Ω) n
        ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)
      letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
      letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
      let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
      Function.Surjective f ∧
        r ≤ Fintype.card (NumberField.InfinitePlace K) + S.card ∧
        Nat.card f.ker = n ^ (Fintype.card (NumberField.InfinitePlace K) + S.card - r) := by
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  have hroot : (primitiveRoots n K).Nonempty := ⟨ζ, (mem_primitiveRoots hn0).mpr hζ⟩
  obtain ⟨S, hS, hE⟩ := finiteAbelian_exists_sUnit_kummer_containment E n hn0 hroot hexp S₀
  refine ⟨S, hE, hS, ?_⟩
  let N := originalKummerRadicalField (Ω := Ω) n
    ((S : Set (HeightOneSpectrum (𝓞 K))).unit K ⊔ (powMonoidHom (α := Kˣ) n).range)
  letI : Algebra E N := (IntermediateField.inclusion hE).toAlgebra
  letI : IsScalarTower K E N := IsScalarTower.of_algHom (IntermediateField.inclusion hE)
  letI : IsGalois K N := originalKummerRadicalField_isGalois n _
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet n hn0 hroot
  let f : Gal(N/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hf : Function.Surjective f := AlgEquiv.restrictNormalHom_surjective N
  have hN : Nat.card Gal(N/K) = n ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) := by
    simpa only [Set.ncard_coe_finset] using
      numberField_sUnit_kummerField_galois_card K Ω S S.finite_toSet n hn0 ζ hζ
  have hr : r ≤ Fintype.card (NumberField.InfinitePlace K) + S.card := by
    have hle := Nat.card_le_card_of_surjective f hf
    rw [hcard, hN] at hle
    exact (Nat.pow_le_pow_iff_right hn).mp hle
  refine ⟨hf, hr, ?_⟩
  have hquot : Nat.card (Gal(N/K) ⧸ f.ker) = Nat.card Gal(E/K) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have hfactor : n ^ (Fintype.card (NumberField.InfinitePlace K) + S.card) =
      n ^ r * Nat.card f.ker := by
    rw [← hN, ← hcard, ← hquot]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hn0 r)
  rw [← hfactor, ← pow_add, Nat.add_sub_of_le hr]

end
end Dubon2026
