import Dubon2026.SourceCyclicPairOrder

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> good reduction
-> reverse genus -> finite exceptional fibers -> elliptic cyclic-subgroup
inertia -> actual number of cyclic subgroups. Reuse the already proved
projective-line cardinality and Dedekind psi function without redefining
either. Primitive pairs use native IsCoprime. The actual torsion structure
transports these subgroups into the original elliptic point group.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ZMod_natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi.lean and
S_AddCommGroup_natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy.lean. -/
namespace Dubon2026.SourceEllipticCyclicCount
open AddSubgroup Dubon2026.SourceLevelProjective
noncomputable section
variable (N : ℕ) [NeZero N]

theorem zmultiples_unit_mul (u : (ZMod N)ˣ) (x : ZMod N × ZMod N) :
    AddSubgroup.zmultiples ((((u : ZMod N) * x.1, (u : ZMod N) * x.2)) : ZMod N × ZMod N)
      = AddSubgroup.zmultiples x := by
  have key : ∀ (w : (ZMod N)ˣ) (y : ZMod N × ZMod N),
      (((w : ZMod N) * y.1, (w : ZMod N) * y.2) : ZMod N × ZMod N) ∈ AddSubgroup.zmultiples y := by
    intro w y
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((w : ZMod N).val : ℤ), ?_⟩
    refine Prod.ext ?_ ?_
    · show ((((w : ZMod N).val : ℤ)) • y).1 = (w : ZMod N) * y.1
      rw [Prod.smul_fst, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
    · show ((((w : ZMod N).val : ℤ)) • y).2 = (w : ZMod N) * y.2
      rw [Prod.smul_snd, zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  refine le_antisymm (AddSubgroup.zmultiples_le.mpr (key u x)) (AddSubgroup.zmultiples_le.mpr ?_)

  have hmem := key u⁻¹ (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N)
  have hx : ((((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).1,
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (((u : ZMod N) * x.1, (u : ZMod N) * x.2) : ZMod N × ZMod N).2)
        : ZMod N × ZMod N) = x := by
    have h1 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.1) = x.1 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    have h2 : ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * ((u : ZMod N) * x.2) = x.2 := by
      rw [← mul_assoc, u.inv_mul, one_mul]
    exact Prod.ext h1 h2
  rwa [hx] at hmem

omit [NeZero N] in

theorem eq_of_mul_unimodularRow_eq {a c : ZMod N} (h : IsCoprime a c) {r s : ZMod N}
    (h1 : r * a = s * a) (h2 : r * c = s * c) : r = s := by
  obtain ⟨x, y, hxy⟩ := h
  calc r = r * (x * a + y * c) := by rw [hxy, mul_one]
    _ = x * (r * a) + y * (r * c) := by ring
    _ = x * (s * a) + y * (s * c) := by rw [h1, h2]
    _ = s * (x * a + y * c) := by ring
    _ = s := by rw [hxy, mul_one]


end
end Dubon2026.SourceEllipticCyclicCount
