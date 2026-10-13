/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Integral diagonal extension adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/{GaloisAction,Herbrand}.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitLogDiagonalSplit

/-! # The original logarithmic lattice with its integral diagonal

A real basis is obtained from the proved full original integer lattice.
Adjoining the unit diagonal gives a complete product lattice with an
exact membership criterion. This is the required integral extension for
DUB-17's comparison with the permutation representation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (L : Type) [Field L] [NumberField L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))

local instance : DiscreteTopology (sUnitFullLogLattice L S) := sUnitFullLogLattice_discrete L S
local instance : IsZLattice ℝ (sUnitFullLogLattice L S) := sUnitFullLogLattice_isZLattice L S
local instance : Module.Finite ℤ (sUnitFullLogLattice L S) := ZLattice.module_finite ℝ _
local instance : Module.Free ℤ (sUnitFullLogLattice L S) := ZLattice.module_free ℝ _

/-- A real basis of the original hyperplane coming from the actual complete integer lattice. -/
def sUnitLogLatticeRealBasis :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (sUnitFullLogLattice L S)) ℝ
      (SUnitLogHyperplane L S) :=
  (Module.Free.chooseBasis ℤ (sUnitFullLogLattice L S)).ofZLatticeBasis ℝ (sUnitFullLogLattice L S)

/-- The actual integral logarithmic basis together with the unit diagonal basis. -/
def sUnitLogProductBasis :
    Module.Basis (Module.Free.ChooseBasisIndex ℤ (sUnitFullLogLattice L S) ⊕ Unit) ℝ
      (SUnitLogHyperplane L S × ℝ) :=
  (sUnitLogLatticeRealBasis L S).prod (Module.Basis.singleton Unit ℝ)

/-- The original logarithmic lattice together with one integral diagonal direction. -/
def sUnitLogProductLattice : Submodule ℤ (SUnitLogHyperplane L S × ℝ) :=
  Submodule.span ℤ (Set.range (sUnitLogProductBasis L S))

/-- Product-lattice membership means an actual logarithmic lattice vector and an integer diagonal. -/
theorem sUnitLogProductLattice_mem (z : SUnitLogHyperplane L S × ℝ) :
    z ∈ sUnitLogProductLattice L S ↔ z.1 ∈ sUnitFullLogLattice L S ∧ ∃ n : ℤ, (n : ℝ) = z.2 := by
  let b := sUnitLogProductBasis L S
  constructor
  · intro hz
    have hr := (b.mem_span_iff_repr_mem ℤ z).mp hz
    have hfirst : z.1 ∈ sUnitFullLogLattice L S := by
      rw [← (Module.Free.chooseBasis ℤ (sUnitFullLogLattice L S)).ofZLatticeBasis_span ℝ]
      apply ((sUnitLogLatticeRealBasis L S).mem_span_iff_repr_mem ℤ z.1).mpr
      intro j
      simpa only [b, sUnitLogProductBasis, Module.Basis.prod_repr_inl] using hr (Sum.inl j)
    have hsecond := hr (Sum.inr ())
    simp only [b, sUnitLogProductBasis, Module.Basis.prod_repr_inr,
      Module.Basis.singleton_repr] at hsecond
    exact ⟨hfirst, hsecond⟩
  · rintro ⟨hfirst, n, hn⟩
    apply (b.mem_span_iff_repr_mem ℤ z).mpr
    intro i
    cases i with
    | inl j =>
      have hs : z.1 ∈ Submodule.span ℤ (Set.range (sUnitLogLatticeRealBasis L S)) := by
        simpa only [sUnitLogLatticeRealBasis, Module.Basis.ofZLatticeBasis_span] using hfirst
      simpa only [b, sUnitLogProductBasis, Module.Basis.prod_repr_inl] using
        ((sUnitLogLatticeRealBasis L S).mem_span_iff_repr_mem ℤ z.1).mp hs j
    | inr j =>
      refine ⟨n, ?_⟩
      simpa only [b, sUnitLogProductBasis, Module.Basis.prod_repr_inr,
        Module.Basis.singleton_repr] using hn

/-- The actual original logarithmic lattice plus integral diagonal is discrete. -/
theorem sUnitLogProductLattice_discrete : DiscreteTopology (sUnitLogProductLattice L S) := by
  unfold sUnitLogProductLattice
  infer_instance

/-- The actual original logarithmic lattice plus integral diagonal is complete. -/
theorem sUnitLogProductLattice_isZLattice :
    letI := sUnitLogProductLattice_discrete L S
    IsZLattice ℝ (sUnitLogProductLattice L S) := by
  unfold sUnitLogProductLattice
  infer_instance

end
end Dubon2026
