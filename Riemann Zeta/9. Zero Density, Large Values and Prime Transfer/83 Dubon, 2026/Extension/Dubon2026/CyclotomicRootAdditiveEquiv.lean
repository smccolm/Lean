import Dubon2026.PrimitiveRootCyclotomicContinuity
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # The actual root-of-unity group and the finite cyclotomic coefficient action -/

namespace Dubon2026
noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {n : ℕ} [NeZero n] {μ : K}

/-- A genuine primitive root identifies the actual root-of-unity group with the
additive finite coefficient group, using the pinned power equivalence. -/
def primitiveRootAdditiveEquiv (hμ : IsPrimitiveRoot μ n) :
    ZMod n ≃+ Additive (rootsOfUnity n K) :=
  (hμ.isUnit_unit (NeZero.ne n)).zmodEquivZPowers.trans
    (MulEquiv.toAdditive (MulEquiv.subgroupCongr
      (hμ.isUnit_unit (NeZero.ne n)).zpowers_eq))

/-- The additive identification sends an original residue class to the literal
power of the chosen original primitive root in the original field. -/
theorem primitiveRootAdditiveEquiv_apply (hμ : IsPrimitiveRoot μ n) (x : ZMod n) :
    (((Additive.toMul (primitiveRootAdditiveEquiv hμ x) : rootsOfUnity n K) : Kˣ) : K) =
      μ ^ x.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  simp only [primitiveRootAdditiveEquiv, AddEquiv.trans_apply,
    IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  change (((hμ.isUnit (NeZero.ne n)).unit : K) ^ x.val) = μ ^ x.val
  rw [(hμ.isUnit (NeZero.ne n)).unit_spec]

/-- The original automorphism action on actual roots of unity is multiplication
by the genuine cyclotomic character under the same additive identification. -/
theorem primitiveRootAdditiveEquiv_galois
    (hμ : IsPrimitiveRoot μ n) (g : K ≃ₐ[F] K) (x : ZMod n) :
    restrictRootsOfUnity g n (Additive.toMul (primitiveRootAdditiveEquiv hμ x)) =
      Additive.toMul (primitiveRootAdditiveEquiv hμ ((hμ.autToPow F g : ZMod n) * x)) := by
  apply Subtype.ext
  apply Units.ext
  change g (((Additive.toMul (primitiveRootAdditiveEquiv hμ x) : rootsOfUnity n K) : Kˣ) : K) =
    (((Additive.toMul (primitiveRootAdditiveEquiv hμ ((hμ.autToPow F g : ZMod n) * x)) :
      rootsOfUnity n K) : Kˣ) : K)
  rw [primitiveRootAdditiveEquiv_apply, primitiveRootAdditiveEquiv_apply, map_pow,
    ← hμ.autToPow_spec F g, ← pow_mul, ZMod.val_mul]
  simpa only [← hμ.eq_orderOf] using
    (pow_mod_orderOf μ ((hμ.autToPow F g : ZMod n).val * x.val)).symm

end
end Dubon2026
