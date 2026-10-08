import Dubon2026.PolynomialEndIntertwiner
import Mathlib.LinearAlgebra.Charpoly.Basic

/-! # A genuine nonzero polynomial annihilator from an actual finite invariant subspace -/

namespace Dubon2026

noncomputable section
open Polynomial

/-- Every vector in a genuine finite-dimensional invariant subspace has an actual nonzero polynomial annihilator for the original ambient operator. -/
theorem finiteInvariant_polynomial_annihilator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ v ∈ W, T v ∈ W) (v : V) (hv : v ∈ W) :
    ∃ p : ℂ[X], p ≠ 0 ∧ aeval T p v = 0 := by
  let S : Module.End ℂ W := T.restrict hW
  refine ⟨S.charpoly, S.charpoly_monic.ne_zero, ?_⟩
  have he := polynomialEnd_intertwine S T W.subtype (fun _ => rfl) S.charpoly ⟨v, hv⟩
  have hz := congrArg (fun A : Module.End ℂ W => A ⟨v, hv⟩) S.aeval_self_charpoly
  change aeval S S.charpoly ⟨v, hv⟩ = 0 at hz
  rw [hz, map_zero] at he
  exact he.symm

end
end Dubon2026
