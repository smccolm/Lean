import Dubon2026.SourceCurveFiniteRankTraceBlocks

/-! The matrix trace calculation used to compare local residues with the
field trace in an integral basis. Every finite-image hypothesis concerns
an entry commutator, which the actual local Tate theorem supplies. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

/-- A finite matrix of linear operators, acting on the product space. -/
def blockEnd (T : ι → ι → V →ₗ[K] V) : (ι → V) →ₗ[K] (ι → V) :=
  LinearMap.pi (fun i => ∑ j, T i j ∘ₗ LinearMap.proj j)

/-- A common operator acting in each coordinate. -/
def diagonalEnd (u : V →ₗ[K] V) : (ι → V) →ₗ[K] (ι → V) :=
  LinearMap.pi (fun i => u ∘ₗ LinearMap.proj i)

omit [DecidableEq ι] in
/-- The product-space operator is the literal sum of its matrix entries. -/
theorem blockEnd_apply (T : ι → ι → V →ₗ[K] V) (x : ι → V) (i : ι) :
    blockEnd T x i = ∑ j, T i j (x j) := by
  simp only [blockEnd, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- The diagonal operator applies the same map in each coordinate. -/
theorem diagonalEnd_apply (u : V →ₗ[K] V) (x : ι → V) (i : ι) :
    diagonalEnd u x i = u (x i) := rfl

/-- Commuting a matrix with a scalar diagonal operator gives the entry commutators. -/
theorem blockEnd_commutator (T : ι → ι → V →ₗ[K] V) (u : V →ₗ[K] V) :
    blockEnd T ∘ₗ diagonalEnd u - diagonalEnd u ∘ₗ blockEnd T =
      ∑ i, ∑ j, LinearMap.single K (fun _ : ι => V) i ∘ₗ
        (T i j ∘ₗ u - u ∘ₗ T i j) ∘ₗ (LinearMap.proj j : (ι → V) →ₗ[K] V) := by
  apply LinearMap.ext
  intro x
  funext i
  have hR : ((∑ i', ∑ j, LinearMap.single K (fun _ : ι => V) i' ∘ₗ
      (T i' j ∘ₗ u - u ∘ₗ T i' j) ∘ₗ (LinearMap.proj j : (ι → V) →ₗ[K] V)) x) i =
        ∑ j, (T i j ∘ₗ u - u ∘ₗ T i j) (x j) := by
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finset.sum_apply, LinearMap.single_apply]
    rw [Finset.sum_eq_single i (fun i' _ hi' => ?_)
      (fun h => absurd (Finset.mem_univ i) h)]
    · simp only [Pi.single_eq_same]
    · exact Finset.sum_eq_zero fun j _ => Pi.single_eq_of_ne' hi' _
  rw [hR]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Pi.sub_apply,
    blockEnd_apply, diagonalEnd_apply, map_sum, Finset.sum_sub_distrib]

/-- The matrix commutator is finite rank and its trace is the diagonal sum. -/
theorem blockEnd_commutator_trace (T : ι → ι → V →ₗ[K] V) (u : V →ₗ[K] V)
    [∀ i j, FiniteDimensional K (LinearMap.range (T i j ∘ₗ u - u ∘ₗ T i j))] :
    FiniteDimensional K (LinearMap.range
      (blockEnd T ∘ₗ diagonalEnd u - diagonalEnd u ∘ₗ blockEnd T)) ∧
    finrankTrace (blockEnd T ∘ₗ diagonalEnd u - diagonalEnd u ∘ₗ blockEnd T) =
      ∑ i, finrankTrace (T i i ∘ₗ u - u ∘ₗ T i i) := by
  haveI : ∀ i j, FiniteDimensional K (LinearMap.range
      (LinearMap.single K (fun _ : ι => V) i ∘ₗ (T i j ∘ₗ u - u ∘ₗ T i j) ∘ₗ
        (LinearMap.proj j : (ι → V) →ₗ[K] V))) :=
    fun i j => finite_range_comp_middle _ _ _
  haveI : ∀ i, FiniteDimensional K (LinearMap.range
      (∑ j, LinearMap.single K (fun _ : ι => V) i ∘ₗ (T i j ∘ₗ u - u ∘ₗ T i j) ∘ₗ
        (LinearMap.proj j : (ι → V) →ₗ[K] V))) := fun i => finite_range_sum _ _
  constructor
  · exact (blockEnd_commutator T u).symm ▸ finite_range_sum Finset.univ _
  · rw [blockEnd_commutator, finrankTrace_blockSum]

end Dubon2026.SourceCurve.ResidueTrace
