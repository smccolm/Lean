import Dubon2026.SUnitFiniteIndexPermutationComparison
import Dubon2026.SUnitExtendedLatticeRepresentation
import Dubon2026.FiniteIndexHerbrandComparison

/-! # The constructed S-unit permutation sublattice as an actual representation

Consume the existing finite-index permutation sublattice of the actual
extended logarithmic lattice. Its displayed basis proves stability,
and the literal subtype restriction supplies the original representation.
This connects the geometric lattice construction to the finite-index
cohomology comparison required for DUB-17's S-unit Herbrand formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual extended S-unit representation contains an original stable finite-index submodule whose basis is permuted by the original place action. -/
theorem sUnitExtended_exists_permutation_subrepresentation :
    letI := sUnitLogPlaceAction K L S hS
    ∃ W : Submodule ℤ (sUnitExtendedLogRep K L S hS),
      ∃ hW : ∀ σ, W ≤ W.comap ((sUnitExtendedLogRep K L S hS).ρ σ),
        Finite ((sUnitExtendedLogRep K L S hS) ⧸ W) ∧
        ∃ b : Module.Basis (SUnitLogPlace L S) ℤ W,
          ∀ (σ : Gal(L/K)) p,
            ((sUnitExtendedLogRep K L S hS).subrepresentation W hW).ρ σ (b p) =
              b (σ • p) := by
  letI := sUnitLogPlaceAction K L S hS
  letI := sUnitFullLogSpaceAction K L S hS
  obtain ⟨T, hT, _, _, hfinite, b, hb⟩ :=
    sUnit_exists_finiteIndex_permutation_sublattice K L S hS
  let A := sUnitExtendedLogRep K L S hS
  let W : Submodule ℤ A := T.comap (sUnitExtendedLogLattice L S).subtype
  let e := (Submodule.comapSubtypeEquivOfLe hT).symm
  let bW : Module.Basis (SUnitLogPlace L S) ℤ W := b.map e
  have hperm (σ : Gal(L/K)) (p : SUnitLogPlace L S) :
      A.ρ σ (bW p).val = (bW (σ • p)).val := by
    apply Subtype.ext
    exact hb σ p
  have hW (σ : Gal(L/K)) : W ≤ W.comap (A.ρ σ) := by
    intro x hx
    let y : W := ⟨x, hx⟩
    have hy : x = ∑ p, bW.repr y p • (bW p).val := by
      simpa only [map_sum, map_smul] using (congrArg W.subtype (bW.sum_repr y)).symm
    change A.ρ σ x ∈ W
    rw [hy, map_sum]
    apply Submodule.sum_mem
    intro p _
    rw [map_smul, hperm]
    exact W.smul_mem _ (bW (σ • p)).property
  refine ⟨W, hW, hfinite, bW, ?_⟩
  intro σ p
  apply Subtype.ext
  exact hperm σ p

end
end Dubon2026
