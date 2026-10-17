import Dubon2026.OriginalFiniteFundamentalNormHomologyEquiv
import Dubon2026.OriginalFiniteFundamentalConverseNorm
import Dubon2026.OriginalLatticeDualHomologyFinite
import Dubon2026.RationalCircleFiniteCyclicEmbedding

/-! # Surjectivity of the actual fundamental H2 coefficient map

The existing converse norm theorem injects literal morphism norm classes
into the actual H2-functional space. The proved norm/homology equivalence,
ordinary integral lattice duality and pinned finite-character duality
give the opposite cardinality bound. Thus every actual H2 functional is
induced by an actual coefficient morphism. This is the required input to
DUB-17's relation-obstruction surjectivity, without a Tate-pairing comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module

/-- Every actual H2 functional is induced by an original coefficient
morphism under full fundamental order, subgroup vanishing and a finite
cyclic target H2. No pairing-identification hypothesis is supplied. -/
theorem originalFiniteFundamental_h2_map_surjective
    {G : Type} [Group G] [Fintype G] (M C : Rep.{0} ℤ G)
    [Module.Finite ℤ M] [Module.Projective ℤ M]
    [Finite (groupCohomology M 2)] [Finite (groupCohomology C 2)]
    [IsAddCyclic (groupCohomology C 2)]
    (φ : groupCohomology.cocycles₂ C)
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology
        (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2)) :
    Function.Surjective (fun χ : M ⟶ C => (groupCohomology.functor ℤ G 2).map χ) := by
  let Q := OriginalCoefficientNormQuotient M C
  let H := groupCohomology M 2
  let T := H ⟶ groupCohomology C 2
  let f : Q →ₗ[ℤ] T := originalNormQuotientCohomologyMap M C 1
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro q hq
    obtain ⟨χ, rfl⟩ := (originalCoefficientNormLinearMap M C).range.mkQ_surjective q
    have hχ : (groupCohomology.functor ℤ G 2).map χ = 0 := hq
    obtain ⟨η, hη⟩ := originalFiniteFundamental_h2_zero_norm M C φ ho h χ hχ
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨η, hη⟩
  obtain ⟨j, hj⟩ := originalFiniteCyclic_exists_injective_circle_character
    (groupCohomology C 2)
  let e := originalRationalCircleFiniteCharacterEquiv H
  letI : Finite (H →ₗ[ℤ] AddCircle (1 : ℚ)) := Finite.of_injective e e.injective
  let i : T → (H →ₗ[ℤ] AddCircle (1 : ℚ)) := fun t => j.comp t.hom
  have hi : Function.Injective i := by
    intro x y hxy
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact hj (LinearMap.congr_fun hxy a)
  letI : Finite T := Finite.of_injective i hi
  have hT : Nat.card T ≤ Nat.card H :=
    (Nat.card_le_card_of_injective i hi).trans_eq (Nat.card_congr e)
  have hQ : Nat.card Q = Nat.card H :=
    (Nat.card_congr (originalFiniteFundamentalNormHomologyEquiv M C φ h).toEquiv).trans
      (originalLatticeDualHomology_card M)
  have hcard : Nat.card Q = Nat.card T :=
    le_antisymm (Nat.card_le_card_of_injective f hf) (hT.trans_eq hQ.symm)
  have hsurj := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩).2
  intro t
  obtain ⟨q, hq⟩ := hsurj t
  obtain ⟨χ, rfl⟩ := (originalCoefficientNormLinearMap M C).range.mkQ_surjective q
  exact ⟨χ, hq⟩

end
end Dubon2026
