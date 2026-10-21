import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> actual regular differential dimension -> global residue
identity -> Galois trace comparison. The native sum-of-automorphisms formula
reduces vanishing of a linear functional to its restriction to the base
field and its Galois invariance. This is a conditional reduction only:
the residue functional's invariance and the auxiliary finite Galois field
must be constructed before applying it to the original modular field.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E] [CharZero K]
variable [Algebra K E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

theorem linearMap_eq_zero_of_galois_invariant
    (φ : E →ₗ[K] K)
    (hbase : ∀ f : F, φ (algebraMap F E f) = 0)
    (hinvariant : ∀ (σ : E ≃ₐ[F] E) (x : E), φ (σ x) = φ x) : φ = 0 := by
  classical
  ext x
  have htrace := congrArg φ (trace_eq_sum_automorphisms (K := F) x)
  rw [hbase, map_sum] at htrace
  simp only [hinvariant, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htrace
  exact (mul_eq_zero.mp htrace.symm).resolve_left
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end
end Dubon2026.SourceCurve
