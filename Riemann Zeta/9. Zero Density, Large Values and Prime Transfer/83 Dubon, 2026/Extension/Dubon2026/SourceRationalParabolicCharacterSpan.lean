import Dubon2026.SourceWeightTwoParabolicPeriods
import Dubon2026.SourceTrivialIntegralHecke

/-! DUB-17/18 -> rational rank-two Hecke descent -> rational structure
of the actual parabolic character space. Finite generation of Gamma0
gives finite support in a Q-basis of C for every character. Coordinate
projection preserves the literal trace-four vanishing conditions.
Adapted from the RationalStructure argument in
S_CuspForm_linearIndependent_complex_of_linearIndependent_int,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup SourceCuspBoundary
open scoped MatrixGroups

/-- The actual rational characters with the same trace-four parabolic vanishing condition. -/
def sourceRationalParabolicHoms (N : ℕ) : Submodule ℚ (Additive (Gamma0 N) →+ ℚ) where
  carrier := {φ | ∀ γ : Gamma0 N, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro f g hf hg γ hγ
    simp only [AddMonoidHom.add_apply, hf γ hγ, hg γ hγ, add_zero]
  smul_mem' := by
    intro c f hf γ hγ
    simp only [AddMonoidHom.smul_apply, hf γ hγ, smul_zero]

/-- Literal coefficient inclusion on the original rational characters. -/
def sourceRationalCharacterComplex (N : ℕ) (φ : Additive (Gamma0 N) →+ ℚ) :
    Additive (Gamma0 N) →+ ℂ := (Rat.castHom ℂ).toAddMonoidHom.comp φ

theorem sourceRationalCharacterComplex_apply (N : ℕ) (φ : Additive (Gamma0 N) →+ ℚ)
    (γ : Additive (Gamma0 N)) : sourceRationalCharacterComplex N φ γ = (φ γ : ℂ) := rfl

theorem sourceRationalCharacterComplex_parabolic (N : ℕ) (φ : Additive (Gamma0 N) →+ ℚ)
    (hφ : φ ∈ sourceRationalParabolicHoms N) :
    sourceRationalCharacterComplex N φ ∈ parabolicHoms N := by
  intro γ hγ
  change (φ (Additive.ofMul γ) : ℂ) = 0
  rw [hφ γ hγ, Rat.cast_zero]

theorem sourceParabolicCharacter_mem_rational_span (N : ℕ) [NeZero N]
    (φ : Additive (Gamma0 N) →+ ℂ) (hφ : φ ∈ parabolicHoms N) :
    φ ∈ Submodule.span ℂ (sourceRationalCharacterComplex N ''
      (sourceRationalParabolicHoms N : Set (Additive (Gamma0 N) →+ ℚ))) := by
  classical
  letI : Group.FG SL(2, ℤ) := Group.fg_iff.mpr
    ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  let bC := Module.Basis.ofVectorSpace ℚ ℂ
  obtain ⟨Sg, hSg, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG (Gamma0 N))
  let F := hfin.toFinset.biUnion fun s => (bC.repr (φ (Additive.ofMul s))).support
  have hsupp : ∀ g : Gamma0 N, (bC.repr (φ (Additive.ofMul g))).support ⊆ F := by
    intro g
    have hg : g ∈ Subgroup.closure Sg := hSg ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      exact Finset.subset_biUnion_of_mem (fun s => (bC.repr (φ (Additive.ofMul s))).support)
        (hfin.mem_toFinset.mpr hx)
    | one => simp
    | mul x y _ _ ihx ihy =>
      rw [ofMul_mul, map_add, map_add]
      exact Finsupp.support_add.trans (Finset.union_subset ihx ihy)
    | inv x _ ih =>
      rw [ofMul_inv, map_neg, map_neg, Finsupp.support_neg]
      exact ih
  let φβ : Module.Basis.ofVectorSpaceIndex ℚ ℂ → (Additive (Gamma0 N) →+ ℚ) :=
    fun β => (bC.coord β).toAddMonoidHom.comp φ
  have hφβ : ∀ β γ, φβ β γ = bC.repr (φ γ) β := fun _ _ => rfl
  have hφβ_par : ∀ β, φβ β ∈ sourceRationalParabolicHoms N := by
    intro β γ hγ
    rw [hφβ, hφ γ hγ, map_zero, Finsupp.zero_apply]
  have hexp : φ = ∑ β ∈ F, (bC β : ℂ) • sourceRationalCharacterComplex N (φβ β) := by
    apply AddMonoidHom.ext
    intro γ
    obtain ⟨g, rfl⟩ : ∃ g, Additive.ofMul g = γ := ⟨γ.toMul, rfl⟩
    rw [AddMonoidHom.finsetSum_apply]
    simp only [AddMonoidHom.smul_apply, sourceRationalCharacterComplex_apply, hφβ, smul_eq_mul]
    conv_lhs => rw [← bC.linearCombination_repr (φ (Additive.ofMul g))]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hsupp g) _ (by simp)]
    exact Finset.sum_congr rfl fun β _ => by rw [Rat.smul_def, mul_comm]
  rw [hexp]
  exact Submodule.sum_mem _ fun β _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨φβ β, hφβ_par β, rfl⟩)

end
end Dubon2026
