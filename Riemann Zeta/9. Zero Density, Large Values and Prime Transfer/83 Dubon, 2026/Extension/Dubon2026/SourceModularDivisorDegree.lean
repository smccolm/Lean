/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the archived LICENSE.
Adapted from TauCetiProject/TauCeti at 199786c594817a82fdd2fab04d3ae4cc5eb837d5,
Algebra/MonoidAlgebra/Basis.lean and RepresentationTheory/Augmentation/Basic.lean.
-/
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Dual.Basis

/-! Degree-zero divisors for the actual integral modular symbols.
DUB-17 Theorem 2.6 and DUB-18 Corollary 8.2 require modular Galois association
along the higher symmetric-power continuation route. Integral Hecke finiteness
through periods uses the degree-zero cusp divisors. Only their invariant
degree map and spanning differences are needed here; no general representation
category, character formula or splitting theorem is imported.
-/

namespace Dubon2026
noncomputable section

variable (R X : Type*) [Semiring R]

/-- The actual degree of a finite divisor is the sum of its coefficients. -/
def sourceModularDivisorDegree : MonoidAlgebra R X →ₗ[R] R :=
  (MonoidAlgebra.basis X R).sumCoords

/-- A one-point divisor has its actual coefficient as degree. -/
theorem sourceModularDivisorDegree_single (x : X) (r : R) :
    sourceModularDivisorDegree R X (Finsupp.single x r) = r := by
  change (Finsupp.single x r).sum (fun _ a => a) = r
  simp

variable {R X}

/-- Permuting cusp divisors preserves their actual degree. -/
theorem sourceModularDivisorDegree_action {G : Type*} [Monoid G] [MulAction G X]
    (g : G) (v : MonoidAlgebra R X) :
    sourceModularDivisorDegree R X (Representation.ofMulAction R G X g v) =
      sourceModularDivisorDegree R X v := by
  have he : (sourceModularDivisorDegree R X).comp (Representation.ofMulAction R G X g) =
      sourceModularDivisorDegree R X := by
    apply (MonoidAlgebra.basis X R).ext
    intro x
    change sourceModularDivisorDegree R X
      (Representation.ofMulAction R G X g (Finsupp.single x 1)) =
        sourceModularDivisorDegree R X (Finsupp.single x 1)
    rw [Representation.ofMulAction_single, sourceModularDivisorDegree_single,
      sourceModularDivisorDegree_single]
  exact LinearMap.congr_fun he v

/-- The degree-zero divisors form the actual invariant subrepresentation. -/
def sourceModularDivisorAugmentation (R : Type*) [Semiring R]
    (G X : Type*) [Monoid G] [MulAction G X] :
    Subrepresentation (Representation.ofMulAction R G X) where
  toSubmodule := LinearMap.ker (sourceModularDivisorDegree R X)
  apply_mem_toSubmodule g v hv := by
    change sourceModularDivisorDegree R X (Representation.ofMulAction R G X g v) = 0
    rw [sourceModularDivisorDegree_action]
    exact hv

section Ring
variable {A : Type*} [Ring A] (X : Type*)

/-- Every degree-zero divisor is spanned by differences from one fixed cusp. -/
theorem sourceModularDivisorDegree_ker_span (x₀ : X) :
    LinearMap.ker (sourceModularDivisorDegree A X) =
      Submodule.span A (Set.range fun x : X =>
        (Finsupp.single x 1 - Finsupp.single x₀ 1 : MonoidAlgebra A X)) := by
  classical
  refine le_antisymm (fun v hv => ?_) (Submodule.span_le.mpr ?_)
  · change sourceModularDivisorDegree A X v = 0 at hv
    have hs : ∑ x ∈ v.support, v x = 0 := hv
    have hb : ∑ x ∈ v.support, Finsupp.single x (v x) = v := Finsupp.sum_single v
    have he : ∑ x ∈ v.support, v x •
        (Finsupp.single x 1 - Finsupp.single x₀ 1 : MonoidAlgebra A X) = v := by
      have heach (x : X) : v x •
          (Finsupp.single x 1 - Finsupp.single x₀ 1 : MonoidAlgebra A X) =
          v x • (Finsupp.single x 1 : MonoidAlgebra A X) -
            v x • (Finsupp.single x₀ 1 : MonoidAlgebra A X) :=
        smul_sub (v x) _ _
      simp_rw [heach]
      calc
        _ = (∑ x ∈ v.support, v x • (Finsupp.single x 1 : MonoidAlgebra A X)) -
            ∑ x ∈ v.support, v x • (Finsupp.single x₀ 1 : MonoidAlgebra A X) :=
          Finset.sum_sub_distrib _ _
        _ = (∑ x ∈ v.support, Finsupp.single x (v x)) -
            (∑ x ∈ v.support, v x) • (Finsupp.single x₀ 1 : MonoidAlgebra A X) := by
          congr 1
          · apply Finset.sum_congr rfl
            intro x _
            exact (Finsupp.smul_single (v x) x (1 : A)).trans (by simp)
          · exact Finset.sum_smul.symm
        _ = v := by rw [hs, zero_smul, sub_zero, hb]
    rw [← he]
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    change sourceModularDivisorDegree A X (Finsupp.single x 1 - Finsupp.single x₀ 1) = 0
    calc
      _ = sourceModularDivisorDegree A X (Finsupp.single x 1) -
          sourceModularDivisorDegree A X (Finsupp.single x₀ 1) :=
        (sourceModularDivisorDegree A X).map_sub _ _
      _ = 0 := by rw [sourceModularDivisorDegree_single,
        sourceModularDivisorDegree_single, sub_self]

end Ring
end
end Dubon2026
