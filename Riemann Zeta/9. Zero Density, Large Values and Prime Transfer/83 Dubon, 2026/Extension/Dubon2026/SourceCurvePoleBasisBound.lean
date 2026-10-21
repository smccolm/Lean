import Dubon2026.SourceCurvePoleDivisor

/-! DUB-17/18 -> function-field Riemann--Roch -> bounded global index.
A finite family regular away from the coordinate poles has a common pole
bound which is a multiple of the actual coordinate pole divisor. This
supplies the uniform bound for the pinned integral basis, without a
ramification-fiber enumeration.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_forall_mem_lSpace_nsmul_poleDivisor (t : F)
    (ht : {v : Place K F | v.ord t ≠ 0}.Finite) {n : ℕ} (u : Fin n → F)
    (hreg : ∀ i (v : Place K F), 0 ≤ v.ord t → 0 ≤ v.ord (u i)) :
    ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • poleDivisor t ht) := by
  classical
  let B := poleDivisor t ht
  let c := (Finset.univ : Finset (Fin n)).sup fun i =>
    B.support.sup fun v => (-v.ord (u i)).toNat
  refine ⟨c, fun i => mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)⟩
  change -(c • B) v ≤ v.ord (u i)
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  by_cases hv : v ∈ B.support
  · have h1 : (-v.ord (u i)).toNat ≤ B.support.sup fun w => (-w.ord (u i)).toNat :=
      Finset.le_sup (f := fun w => (-w.ord (u i)).toNat) hv
    have h2 : (B.support.sup fun w => (-w.ord (u i)).toNat) ≤ c :=
      Finset.le_sup (f := fun j => B.support.sup fun w => (-w.ord (u j)).toNat)
        (Finset.mem_univ i)
    have hc : -v.ord (u i) ≤ (c : ℤ) :=
      (Int.self_le_toNat _).trans (by exact_mod_cast h1.trans h2)
    have hb : 1 ≤ B v := by
      have hne := Finsupp.mem_support_iff.mp hv
      have hn := poleDivisor_nonneg t ht v
      change 0 ≤ B v at hn
      omega
    nlinarith [Int.natCast_nonneg c]
  · have hb : B v = 0 := by
      by_contra h
      exact hv (Finsupp.mem_support_iff.mpr h)
    have htv : 0 ≤ v.ord t := by
      change max (-v.ord t) 0 = 0 at hb
      have := le_max_left (-v.ord t) 0
      omega
    rw [hb, mul_zero, neg_zero]
    exact hreg i v htv

end
end Dubon2026.SourceCurve
