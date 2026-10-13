import Dubon2026.FiniteGaloisCharacterRadicals
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Actual radicals generating a prescribed finite abelian Galois extension

Existing Hilbert 90 constructs a radical for every original character.
Pinned finite character separation and the actual Galois correspondence
prove these radicals generate the given field. This removes a generation
assumption from containment in the full S-unit Kummer extension needed
for DUB-17's cyclic global norm-index argument.
-/

namespace Dubon2026
noncomputable section
open scoped IsMulCommutative
variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative Gal(L/K)]

/-- Actual Hilbert-90 radicals generate the original finite abelian Galois extension. -/
theorem finiteAbelianGalois_exists_generating_radicals
    (n : ℕ) (hn : 0 < n) (hζ : (primitiveRoots n K).Nonempty)
    (hexp : ∀ g : Gal(L/K), g ^ n = 1) :
    ∃ (a : (Gal(L/K) →* Kˣ) → Kˣ) (β : (Gal(L/K) →* Kˣ) → Lˣ),
      (∀ χ, β χ ^ n = Units.map (algebraMap K L).toMonoidHom (a χ)) ∧
      (∀ χ g, g • β χ / β χ = Units.map (algebraMap K L).toMonoidHom (χ g)) ∧
      IntermediateField.adjoin K (Set.range fun χ => (β χ).val) = ⊤ := by
  letI : NeZero n := ⟨hn.ne'⟩
  letI : HasEnoughRootsOfUnity K n := {
    prim := ⟨hζ.choose, isPrimitiveRoot_of_mem_primitiveRoots hζ.choose_spec⟩
    cyc := rootsOfUnity.isCyclic K n }
  letI : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)
  have hχ (χ : Gal(L/K) →* Kˣ) : ∀ g, χ g ^ n = 1 := by
    intro g
    rw [← map_pow, hexp, map_one]
  choose a β hp hβ using fun χ => finiteGaloisCharacter_exists_radical χ n (hχ χ)
  refine ⟨a, β, hp, hβ, ?_⟩
  let F := IntermediateField.adjoin K (Set.range fun χ => (β χ).val)
  have hf : F.fixingSubgroup = ⊥ := by
    apply le_antisymm _ bot_le
    intro σ hσ
    change σ = 1
    apply (CommGroup.forall_apply_eq_apply_iff Gal(L/K) (M := K)).mp
    intro χ
    have hfixed : σ ((β χ).val) = (β χ).val :=
      hσ ⟨(β χ).val, IntermediateField.subset_adjoin K _ ⟨χ, rfl⟩⟩
    have hunit : σ • β χ = β χ := Units.ext hfixed
    have he := hβ χ σ
    rw [hunit, div_self'] at he
    have hχone : χ σ = 1 := by
      apply Units.map_injective (algebraMap K L).injective
      rw [map_one]
      exact he.symm
    simpa only [map_one] using hχone
  change F = ⊤
  rw [← IsGalois.fixedField_fixingSubgroup F, hf, IntermediateField.fixedField_bot]

end
end Dubon2026
