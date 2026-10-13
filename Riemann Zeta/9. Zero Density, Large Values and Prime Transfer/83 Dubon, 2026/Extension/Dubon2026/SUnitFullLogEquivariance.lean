/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Equivariance adapted from NYLL ClassFieldTheory, commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/GaloisAction.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.SUnitLogPlaceAction

/-! # Equivariance of the actual original S-unit logarithmic lattice

The normalized original logarithm intertwines the actual field Galois
action with the original place permutation. Its full image is therefore
a stable complete lattice. This supplies the original representation,
not only its rank, for DUB-17's S-unit Herbrand calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original normalized logarithmic map intertwines the actual S-unit and place actions. -/
theorem sUnitFullLogAmbient_galois (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitFullLogSpaceAction K L S hS
    sUnitFullLogAmbient L S (σ • x) = σ • sUnitFullLogAmbient L S x := by
  funext p
  cases p with
  | inl w =>
    change w.mult * Real.log (w (σ x.toMul.val.val)) =
      (σ⁻¹ • w).mult * Real.log ((σ⁻¹ • w) x.toMul.val.val)
    rw [numberFieldGaloisInfinitePlace_mult]
    rfl
  | inr v =>
    change Real.log (NumberField.HeightOneSpectrum.adicAbv L v.val (σ x.toMul.val.val)) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv L
        (numberFieldGaloisPlaceEquiv K L σ⁻¹ v.val) x.toMul.val.val)
    congr 1
    have h := numberFieldGaloisPlace_adicAbv K L σ
      (numberFieldGaloisPlaceEquiv K L σ⁻¹ v.val) x.toMul.val.val
    rw [← numberFieldGaloisPlaceEquiv_mul, mul_inv_cancel,
      numberFieldGaloisPlaceEquiv_one] at h
    exact h

/-- The actual place-permutation action restricted to its invariant original sum-zero hyperplane. -/
@[reducible]
def sUnitLogHyperplaneAction : DistribMulAction Gal(L/K) (SUnitLogHyperplane L S) := by
  letI := sUnitFullLogSpaceAction K L S hS
  exact {
    smul := fun σ z => ⟨σ • z.val, by
      apply LinearMap.mem_ker.mpr
      rw [sUnitLogCoordinateSum_galois]
      exact z.property⟩
    one_smul := fun z => Subtype.ext (one_smul Gal(L/K) z.val)
    mul_smul := fun σ τ z => Subtype.ext (mul_smul σ τ z.val)
    smul_zero := fun σ => Subtype.ext (smul_zero σ)
    smul_add := fun σ z z' => Subtype.ext (smul_add σ z.val z'.val) }

/-- The actual full logarithm is equivariant as a map to the original sum-zero hyperplane. -/
theorem sUnitFullLog_galois (σ : Gal(L/K))
    (x : Additive ((S : Set (HeightOneSpectrum (𝓞 L))).unit L)) :
    letI := sUnitAdditiveGaloisAction K L S hS
    letI := sUnitLogHyperplaneAction K L S hS
    sUnitFullLog L S (σ • x) = σ • sUnitFullLog L S x := by
  apply Subtype.ext
  exact sUnitFullLogAmbient_galois K L S hS σ x

/-- The actual complete original logarithmic lattice is stable under the actual Galois action. -/
theorem sUnitFullLogLattice_galois_mem (σ : Gal(L/K)) (z : SUnitLogHyperplane L S)
    (hz : z ∈ sUnitFullLogLattice L S) :
    letI := sUnitLogHyperplaneAction K L S hS
    σ • z ∈ sUnitFullLogLattice L S := by
  letI := sUnitAdditiveGaloisAction K L S hS
  rw [sUnitFullLogLattice_eq_range] at hz ⊢
  obtain ⟨x, rfl⟩ := hz
  exact ⟨σ • x, sUnitFullLog_galois K L S hS σ x⟩

end
end Dubon2026
