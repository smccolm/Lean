/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Lattice transport adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/LogLattice.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitLogHyperplaneEquivalence

/-! # The actual full S-unit logarithmic image is a complete lattice

The exact original coordinate equivalence transports the proved reduced
lattice. The transported subgroup is proved equal to the actual full
logarithmic image. This discharges the full-lattice input, but not the
equivariant Herbrand calculation, in DUB-17's global norm-index route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K : Type*) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- The actual logarithmic coordinate equivalence with its finite-dimensional continuity. -/
def sUnitLogHyperplaneContinuousEquiv :
    SUnitLogHyperplane K S ≃L[ℝ] SUnitReducedLogSpace K S :=
  (sUnitLogHyperplaneEquiv K S).toContinuousLinearEquiv

/-- The full original logarithmic lattice, obtained by the exact original coordinate pullback. -/
def sUnitFullLogLattice : Submodule ℤ (SUnitLogHyperplane K S) :=
  ZLattice.comap ℝ (sUnitReducedLogLattice K S)
    (sUnitLogHyperplaneContinuousEquiv K S).toLinearMap

/-- The transported lattice is precisely the image of the original full logarithm. -/
theorem sUnitFullLogLattice_eq_range :
    sUnitFullLogLattice K S = (sUnitFullLog K S).toIntLinearMap.range := by
  ext z
  constructor
  · intro hz
    change sUnitLogHyperplaneEquiv K S z ∈ sUnitReducedLogLattice K S at hz
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    apply (sUnitLogHyperplaneEquiv K S).injective
    change sUnitLogHyperplaneEquiv K S (sUnitFullLog K S x) = _
    rw [sUnitLogHyperplaneEquiv_fullLog]
    exact hx
  · rintro ⟨x, rfl⟩
    change sUnitLogHyperplaneEquiv K S (sUnitFullLog K S x) ∈ sUnitReducedLogLattice K S
    rw [sUnitLogHyperplaneEquiv_fullLog]
    exact LinearMap.mem_range_self _ x

/-- The actual full original logarithmic image is discrete. -/
theorem sUnitFullLogLattice_discrete : DiscreteTopology (sUnitFullLogLattice K S) := by
  letI := sUnitReducedLogLattice_discrete K S
  unfold sUnitFullLogLattice
  infer_instance

/-- The actual full original logarithmic image is a full integer lattice in the sum-zero hyperplane. -/
theorem sUnitFullLogLattice_isZLattice :
    letI := sUnitFullLogLattice_discrete K S
    IsZLattice ℝ (sUnitFullLogLattice K S) := by
  letI := sUnitReducedLogLattice_discrete K S
  letI := sUnitReducedLogLattice_isZLattice K S
  unfold sUnitFullLogLattice
  infer_instance

/-- The original full logarithm vanishes exactly on the original ordinary roots of unity. -/
theorem sUnitFullLog_eq_zero_iff
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)) :
    sUnitFullLog K S x = 0 ↔
      ∃ u : (𝓞 K)ˣ, u ∈ Units.torsion K ∧
        sUnitOrdinaryUnitEmbedding (R := 𝓞 K) (K := K) S u = x.toMul := by
  rw [← sUnitReducedLog_eq_zero_iff K S x,
    ← sUnitLogHyperplaneEquiv_fullLog K S x,
    map_eq_zero_iff _ (sUnitLogHyperplaneEquiv K S).injective]

end
end Dubon2026
