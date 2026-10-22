import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Analysis.Complex.Basic

/-! DUB-17/18 -> original torsion cardinality -> complex period quotient.
The existing native ModN cardinality theorem counts a free integral lattice
modulo n. Division in the ambient complex vector space identifies that quotient
with the actual n-torsion of the period quotient. Only this missing bridge is
adapted; no new finite abelian-group classification is developed.
Adapted from S_Submodule_natCard_torsionBy_quotient_eq_pow_finrank,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.ComplexLatticeTorsion
noncomputable section
open Submodule
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Division by the natural number in the ambient complex vector space. -/
noncomputable def divN (n : ℕ) : V →+ V :=
  DistribSMul.toAddMonoidHom V ((n : ℂ)⁻¹)

theorem natCast_smul_divN {n : ℕ} (hn : n ≠ 0) (v : V) :
    (n : ℤ) • divN  n v = v := by
  have hK : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hK, one_smul]

theorem divN_natCast_smul {n : ℕ} (hn : n ≠ 0) (v : V) :
    divN  n ((n : ℤ) • v) = v := by
  have hK : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [divN, DistribSMul.toAddMonoidHom_apply]
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hK, one_smul]

variable (L : Submodule ℤ V)

/-- Divide an integral lattice element and take its torsion class in the ambient quotient. -/
noncomputable def latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    L →ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) where
  toFun w := ⟨Submodule.Quotient.mk (divN  n (w : V)), by
    rw [mem_torsionBy_iff]
    change (Submodule.Quotient.mk ((n : ℤ) • divN  n (w : V)) : V ⧸ L) = 0
    rw [natCast_smul_divN  hn]
    exact (Submodule.Quotient.mk_eq_zero L).mpr w.2⟩
  map_add' a b := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN  n ((a + b : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (divN  n (a : V))
        + Submodule.Quotient.mk (divN  n (b : V))
    rw [Submodule.coe_add, map_add, Submodule.Quotient.mk_add]
  map_smul' m a := by
    apply Subtype.ext
    change (Submodule.Quotient.mk (divN  n ((m • a : L) : V)) : V ⧸ L) =
      Submodule.Quotient.mk (m • divN  n (a : V))
    rw [Submodule.coe_smul, map_zsmul]

theorem coe_latticeDivQuot {n : ℕ} (hn : n ≠ 0) (w : L) :
    ((latticeDivQuot  L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
      = Submodule.Quotient.mk (divN  n (w : V)) := rfl

theorem latticeDivQuot_surjective {n : ℕ} (hn : n ≠ 0) :
    Function.Surjective (latticeDivQuot  L hn) := by
  rintro ⟨x, hx⟩
  rw [mem_torsionBy_iff] at hx
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L x
  have hvL : (n : ℤ) • v ∈ L := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨⟨(n : ℤ) • v, hvL⟩, Subtype.ext ?_⟩
  rw [coe_latticeDivQuot]
  change (Submodule.Quotient.mk (divN  n ((n : ℤ) • v)) : V ⧸ L)
      = Submodule.Quotient.mk v
  rw [divN_natCast_smul  hn]

theorem ker_latticeDivQuot {n : ℕ} (hn : n ≠ 0) :
    LinearMap.ker (latticeDivQuot  L hn)
      = LinearMap.range (LinearMap.lsmul ℤ L (n : ℤ)) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hker
    have hcoe : ((latticeDivQuot  L hn w : torsionBy ℤ (V ⧸ L) (n : ℤ)) : V ⧸ L)
        = 0 := by
      rw [hker]; rfl
    rw [coe_latticeDivQuot, Submodule.Quotient.mk_eq_zero] at hcoe
    refine ⟨⟨divN  n (w : V), hcoe⟩, ?_⟩
    apply Subtype.ext
    change (n : ℤ) • divN  n (w : V) = (w : V)
    exact natCast_smul_divN  hn (w : V)
  · rintro ⟨μ, rfl⟩
    apply Subtype.ext
    rw [coe_latticeDivQuot, LinearMap.lsmul_apply]
    change (Submodule.Quotient.mk (divN  n ((n : ℤ) • (μ : V))) : V ⧸ L) = 0
    rw [divN_natCast_smul  hn, Submodule.Quotient.mk_eq_zero]
    exact μ.2

/-- The quotient lattice modulo n identified with n-torsion of the ambient quotient. -/
noncomputable def latticeQuotTorsionEquiv {n : ℕ} (hn : n ≠ 0) :
    ModN L n ≃ₗ[ℤ] torsionBy ℤ (V ⧸ L) (n : ℤ) :=
  (Submodule.quotEquivOfEq _ _ (ker_latticeDivQuot  L hn).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (latticeDivQuot_surjective  L hn))

theorem natCard_torsion_quotient (L : Submodule ℤ V)
    [Module.Free ℤ L] [Module.Finite ℤ L] (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ L) (n : ℤ)) = n ^ Module.finrank ℤ L := by
  letI : NeZero n := ⟨hn⟩
  rw [← Nat.card_congr (latticeQuotTorsionEquiv L hn).toEquiv, ModN.natCard_eq]

end
end Dubon2026.ComplexLatticeTorsion
