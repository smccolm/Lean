import Dubon2026.SourceCurveKummerRootPullback

/-! DUB-17/18 -> the detecting norm divisor -> finite support bookkeeping.
Avoiding two cover points and the divisor support discharges the exact
disjointness and norm-fiber conditions of the detecting-ratio calculation. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Algebra.IsSeparable F E]

theorem kummer_norm_avoidance (n : ℕ) (w w' : Place K E) (D : Divisor K F)
    (B : Divisor K E) (u : E)
    (hU : ∀ q : Place K E, q.ord u =
      (Finsupp.single w' (1 : ℤ)) q - (Finsupp.single w (1 : ℤ)) q + n * B q)
    (hw : D (w.restrict F) = 0) (hw' : D (w'.restrict F) = 0)
    (hB : ∀ q ∈ B.support, D (q.restrict F) = 0) :
    (∀ v, D v = 0 ∨ Divisor.geometricPushforward F B v = 0) ∧
    (∀ q ∈ (Finsupp.single w' (1 : ℤ) - Finsupp.single w 1).support, D (q.restrict F) = 0) ∧
    (∀ v ∈ D.support, ∀ q : Place K E, q.restrict F = v → q.ord u = 0) ∧
    ∀ q : Place K E, q.ord u ≠ 0 → D (q.restrict F) = 0 := by
  classical
  have hzero (q : Place K E) (hq : D (q.restrict F) ≠ 0) : q.ord u = 0 := by
    have hqw : q ≠ w := fun he => hq (he.symm ▸ hw)
    have hqw' : q ≠ w' := fun he => hq (he.symm ▸ hw')
    have hBq : B q = 0 := by
      by_contra hb
      exact hq (hB q (Finsupp.mem_support_iff.mpr hb))
    rw [hU, Finsupp.single_eq_of_ne hqw',
      Finsupp.single_eq_of_ne hqw, hBq, mul_zero, sub_self, zero_add]
  refine ⟨disjoint_geometricPushforward_of_avoiding D B hB, ?_, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_union.mp (Finsupp.support_sub hq) with hq | hq
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
      exact hw'
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hq)]
      exact hw
  · intro v hv q hq
    exact hzero q (hq.symm ▸ Finsupp.mem_support_iff.mp hv)
  · intro q hq
    by_contra hd
    exact hq (hzero q hd)

theorem exists_kummer_norm_avoiding (n : ℕ) (D : Divisor.degZero (K := K) (F := F))
    (w w' : Place K E) (B : Divisor K E) (u : E)
    (hU : ∀ q : Place K E, q.ord u =
      (Finsupp.single w' (1 : ℤ)) q - (Finsupp.single w (1 : ℤ)) q + n * B q)
    (hmove : ∀ S : Finset (Place K F),
      ∃ D' : Divisor.degZero (K := K) (F := F), ∃ r : F, r ≠ 0 ∧
        Pic0.mk D' = Pic0.mk D ∧ (∀ v ∈ S, D'.val v = 0) ∧
        ∀ v : Place K F, v.ord r = D'.val v - D.val v) :
    let ι : Place K E → Place K F := fun q : Place K E => q.restrict F
    ∃ D' : Divisor.degZero (K := K) (F := F), ∃ r : F, r ≠ 0 ∧
      Pic0.mk D' = Pic0.mk D ∧
      (∀ v : Place K F, v.ord r = D'.val v - D.val v) ∧
      (∀ v : Place K F, D'.val v = 0 ∨ Divisor.geometricPushforward F B v = 0) ∧
      (∀ q : Place K E, q ∈ (Finsupp.single w' (1 : ℤ) - Finsupp.single w 1).support →
        D'.val (ι q) = 0) ∧
      (∀ q : Place K E, q ∈ B.support → D'.val (ι q) = 0) ∧
      D'.val (ι w) = 0 ∧
      (∀ v : Place K F, v ∈ D'.val.support → ∀ q : Place K E, ι q = v → q.ord u = 0) ∧
      ∀ q : Place K E, q.ord u ≠ 0 → D'.val (ι q) = 0 := by
  classical
  let T : Finset (Place K E) := insert w' (insert w B.support)
  let S : Finset (Place K F) := T.image (fun q : Place K E => q.restrict F)
  obtain ⟨D', r, hr, hD', hav, hrD⟩ := hmove S
  have hT (q : Place K E) (hq : q ∈ T) : D'.val (q.restrict F) = 0 :=
    hav _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
  have hw : D'.val (w.restrict F) = 0 :=
    hT w (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hw' : D'.val (w'.restrict F) = 0 := hT w' (Finset.mem_insert_self _ _)
  have hB : ∀ q ∈ B.support, D'.val (q.restrict F) = 0 :=
    fun q hq => hT q (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hq))
  have hc := kummer_norm_avoidance n w w' D'.val B u hU hw hw' hB
  exact ⟨D', r, hr, hD', hrD, hc.1, hc.2.1, hB, hw, hc.2.2.1, hc.2.2.2⟩

end
end Dubon2026.SourceCurve
