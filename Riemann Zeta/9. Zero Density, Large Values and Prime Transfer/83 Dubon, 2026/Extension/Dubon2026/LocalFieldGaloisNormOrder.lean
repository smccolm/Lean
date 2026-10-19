import Dubon2026.LocalFieldGaloisUnitOrder
import Dubon2026.LocalFieldUnitOrderBaseChange
import Mathlib.RingTheory.Norm.Transitivity

/-! The norm of a cyclotomic uniformizer has order one. The formula proved
here will force residue degree one, so every automorphism of that actual
finite cyclotomic extension is inertia. Together with inertia restriction
surjectivity this supplies the tame quotient used by the auxiliary local
deformation rings on the Dubon Theorem 2.6 dependency chain. -/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

/-- In a finite Galois local extension, the original normalized order of
the field norm is residue degree times the original extension order. -/
theorem localField_galois_norm_order
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [ValuativeRel K] [ValuativeRel L]
    [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (v : Lˣ) :
    localFieldUnitOrder K (Additive.ofMul (Units.map (Algebra.norm K (S := L)) v)) =
      (Module.finrank 𝓀[K] 𝓀[L] : ℤ) * localFieldUnitOrder L (Additive.ofMul v) := by
  classical
  let e := (IsLocalRing.maximalIdeal 𝒪[K]).ramificationIdx (IsLocalRing.maximalIdeal 𝒪[L])
  have hef : e * Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L :=
    localField_ramification_mul_residue_degree K L
  have he : (e : ℤ) ≠ 0 := by
    exact_mod_cast (show e ≠ 0 from fun h => by
      rw [h, zero_mul] at hef
      exact Module.finrank_pos.ne' hef.symm)
  have hnorm : Units.map (algebraMap K L).toMonoidHom
      (Units.map (Algebra.norm K (S := L)) v) = ∏ σ : Gal(L/K), σ • v := by
    apply Units.ext
    simpa using Algebra.norm_eq_prod_automorphisms K v.val
  have h := congrArg (fun w : Lˣ => localFieldUnitOrder L (Additive.ofMul w)) hnorm
  dsimp only at h
  rw [localFieldUnitOrder_algebraMap K L] at h
  have hsum : localFieldUnitOrder L (Additive.ofMul (∏ σ : Gal(L/K), σ • v)) =
      (Module.finrank K L : ℤ) * localFieldUnitOrder L (Additive.ofMul v) := by
    change localFieldUnitOrder L (∑ σ : Gal(L/K), Additive.ofMul (σ • v)) = _
    rw [map_sum]
    simp only [localFieldUnitOrder_galois_invariant K L, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank K L]
  rw [hsum, ← hef, Nat.cast_mul, mul_assoc] at h
  exact mul_left_cancel₀ he h

end
end Dubon2026
