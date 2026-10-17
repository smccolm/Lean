import Dubon2026.OriginalInfiniteEmbeddingExtension
import Dubon2026.OriginalGlobalInfiniteH2
import Mathlib.LinearAlgebra.Complex.Module

/-! # Original infinite localization controls the same complex embedding

An equivariant original field embedding induces a map from the literal
original completion. The resulting H2 square proves the vanishing needed
for each real Mackey term on DUB-17's full-idele class-generator chain.
The arithmetic orbit application must still construct its field-level square.
-/
namespace Dubon2026
noncomputable section
open NumberField CategoryTheory
attribute [local instance 1100] Rep.hV2
attribute [local instance] Units.mulDistribMulActionRight

private theorem originalComplexAut_norm (σ : Gal(ℂ/ℝ)) (z : ℂ) : ‖σ z‖ = ‖z‖ := by
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => ‖f z‖) h
  · exact (congrArg (fun f : ℂ →ₐ[ℝ] ℂ => ‖f z‖) h).trans (Complex.norm_conj z)

variable (K L G : Type) [Field K] [Field L] [Algebra K L] [Group G]
  (j : L →+* ℂ) (ρ : G →* Gal(L/K)) (σ : G →* Gal(ℂ/ℝ))
  (hcomm : ∀ g x, j (ρ g x) = σ g (j x))

include hcomm in
/-- The original field square forces the actual infinite place to be fixed. -/
theorem originalInfiniteEmbedding_fixed (g : G) :
    ρ g • InfinitePlace.mk j = InfinitePlace.mk j := by
  apply InfinitePlace.ext
  intro x
  change ‖j ((ρ g).symm x)‖ = ‖j x‖
  have h := congrArg norm (hcomm g ((ρ g).symm x))
  simpa only [AlgEquiv.apply_symm_apply, originalComplexAut_norm] using h.symm

/-- The given field action lands in the original infinite decomposition group. -/
def originalInfiniteEmbeddingStabilizerHom :
    G →* OriginalInfiniteDecompositionGroup K L (InfinitePlace.mk j) where
  toFun g := ⟨ρ g, originalInfiniteEmbedding_fixed K L G j ρ σ hcomm g⟩
  map_one' := Subtype.ext (map_one ρ)
  map_mul' g h := Subtype.ext (map_mul ρ g h)

/-- The original completion embedding is equivariant for the derived
decomposition action and the specified complex action. -/
def originalInfiniteEmbeddingCompletionRepHom :
    Rep.res (originalInfiniteEmbeddingStabilizerHom K L G j ρ σ hcomm)
      (originalInfiniteUnitRep K L (InfinitePlace.mk j)) ⟶
        Rep.res σ (Rep.ofAlgebraAutOnUnits ℝ ℂ) :=
  Rep.ofHom ⟨(Units.map (originalInfiniteEmbeddingExtension j).toMonoidHom).toAdditive.toIntLinearMap, by
    intro g
    apply LinearMap.ext
    intro x
    apply congrArg Additive.ofMul
    apply Units.ext
    exact (originalInfiniteEmbeddingExtension_transport K j (ρ g)
      (originalInfiniteEmbedding_fixed K L G j ρ σ hcomm g) (σ g) (hcomm g) x.toMul.val)⟩

/-- The field-level coefficient map retains the same original embedding. -/
def originalInfiniteEmbeddingFieldRepHom :
    Rep.res ρ (Rep.ofAlgebraAutOnUnits K L) ⟶ Rep.res σ (Rep.ofAlgebraAutOnUnits ℝ ℂ) :=
  Rep.ofHom ⟨(Units.map j.toMonoidHom).toAdditive.toIntLinearMap, by
    intro g
    apply LinearMap.ext
    intro x
    apply congrArg Additive.ofMul
    apply Units.ext
    exact hcomm g x.toMul.val⟩

/-- Restriction through the literal original completion equals the direct
H2 map of the same original field embedding. -/
theorem originalInfiniteEmbeddingH2_comparison
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    groupCohomology.map (originalInfiniteEmbeddingStabilizerHom K L G j ρ σ hcomm)
      (originalInfiniteEmbeddingCompletionRepHom K L G j ρ σ hcomm) 2
      (originalGlobalInfiniteH2 K L (InfinitePlace.mk j) x) =
        groupCohomology.map ρ (originalInfiniteEmbeddingFieldRepHom K L G j ρ σ hcomm) 2 x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) = _
    simp only [groupCohomology.H2π_comp_map_apply]
    congr 1
    apply Subtype.ext
    funext gh
    apply congrArg Additive.ofMul
    apply Units.ext
    exact originalInfiniteEmbeddingExtension_algebraMap j (c ((ρ gh.1), (ρ gh.2))).toMul.val

/-- Vanishing at the actual original infinite completion forces vanishing
after the same complex embedding, with no completed-square premise. -/
theorem originalInfiniteEmbeddingH2_zero
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalInfiniteH2 K L (InfinitePlace.mk j) x = 0) :
    groupCohomology.map ρ (originalInfiniteEmbeddingFieldRepHom K L G j ρ σ hcomm) 2 x = 0 := by
  rw [← originalInfiniteEmbeddingH2_comparison K L G j ρ σ hcomm, hx, map_zero]

end
end Dubon2026
