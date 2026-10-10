import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.MulAction

/-! # Closedness of actual integral inertia in the original Krull topology -/

namespace Dubon2026

noncomputable section
open scoped NumberField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]

/-- The original Galois action on the actual integral closure, with its discrete topology, is continuous for the genuine Krull topology on the automorphism group. -/
theorem integral_krull_continuousSMul
    [TopologicalSpace (𝓞 L)] [DiscreteTopology (𝓞 L)] :
    ContinuousSMul Gal(L/K) (𝓞 L) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  have h := stabilizer_isOpen_of_isIntegral (K := K) (x : L)
  convert h using 1
  ext σ
  change (σ • x = x) ↔ σ (x : L) = (x : L)
  exact NumberField.RingOfIntegers.ext_iff

/-- The original inertia subgroup of any actual integral ideal is closed in the original Krull topology; the whole field extension may be infinite. -/
theorem integral_inertia_isClosed (P : Ideal (𝓞 L)) :
    IsClosed (P.inertia Gal(L/K) : Set Gal(L/K)) := by
  letI : TopologicalSpace (𝓞 L) := ⊥
  letI : DiscreteTopology (𝓞 L) := ⟨rfl⟩
  letI : ContinuousSMul Gal(L/K) (𝓞 L) := integral_krull_continuousSMul
  change IsClosed {σ : Gal(L/K) | ∀ x : 𝓞 L, σ • x - x ∈ P}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  exact (isClosed_discrete (P : Set (𝓞 L))).preimage
    ((continuous_id.smul continuous_const).sub continuous_const)

end
end Dubon2026
