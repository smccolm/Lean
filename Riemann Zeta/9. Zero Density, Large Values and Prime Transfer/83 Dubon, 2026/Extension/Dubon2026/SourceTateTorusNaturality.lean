import Dubon2026.SourceTateTorusBasis
import Dubon2026.SourceTateFunctor
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! DUB-17/18 -> original Jacobian Tate realization -> period-lattice comparison.
The explicit tensor comparison intertwines every genuine linear endomorphism preserving the same lattice. The actual Hecke endomorphisms remain to be instantiated.
Adapt the corresponding pinned Apache-2.0 FLT proof on the existing toolchain.
-/
namespace Dubon2026.TateModule.Period
noncomputable section
open scoped TensorProduct
open TateModule

open Module

variable {K : Type*} [Field K] [CharZero K] {V : Type*} [AddCommGroup V] [Module K V]
variable (K) (p : ℕ) [Fact p.Prime] (Λ : Submodule ℤ V)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ Λ)

variable (T : V →ₗ[K] V) (hT : ∀ v ∈ Λ, T v ∈ Λ)

/-- The quotient endomorphism induced by a linear map preserving the lattice. -/
def quotEnd : V ⧸ Λ →+ V ⧸ Λ :=
  (Λ.mapQ Λ T.toAddMonoidHom.toIntLinearMap fun v hv => hT v hv).toAddMonoidHom

omit [CharZero K] in
@[scoped simp] theorem quotEnd_mk (v : V) :
    quotEnd K Λ T hT (Submodule.Quotient.mk v) = Submodule.Quotient.mk (T v) := rfl

omit [CharZero K] [Fact p.Prime] in
theorem quotEnd_divLevel (n : ℕ) (v : V) :
    quotEnd K Λ T hT (divLevel K p Λ n v) = divLevel K p Λ n (T v) := by
  rw [divLevel_apply, divLevel_apply, quotEnd_mk, LinearMap.map_smul]

variable (TΛ : Λ →ₗ[ℤ] Λ)

theorem iota_restrict (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (l : Λ) :
    iota K p Λ (TΛ l) = tateMap p (quotEnd K Λ T hT) (iota K p Λ l) :=
  Subtype.ext (funext fun n => by
    rw [coe_iota_apply, coe_tateMap_apply, coe_iota_apply, hTΛ, quotEnd_divLevel])

theorem phi2_baseChange (hTΛ : ∀ l : Λ, ((TΛ l : Λ) : V) = T l) (z : ℤ_[p] ⊗[ℤ] Λ) :
    phi2 K p Λ b (TΛ.baseChange ℤ_[p] z) = tateMap p (quotEnd K Λ T hT) (phi2 K p Λ b z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a l =>
      rw [LinearMap.baseChange_tmul, phi2_tmul, phi2_tmul, iota_restrict K p Λ T hT TΛ hTΛ, map_smul]
  | add z w hz hw => simp only [map_add, hz, hw]


end
end Dubon2026.TateModule.Period
