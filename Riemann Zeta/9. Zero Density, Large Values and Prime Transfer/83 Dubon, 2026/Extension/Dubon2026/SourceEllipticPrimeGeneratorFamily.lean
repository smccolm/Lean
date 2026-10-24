import Dubon2026.SourceEllipticCyclicGenerators

/-! Reuse the actual cyclic-subgroup count to enumerate all prime kernels while
retaining a prescribed original generator. Replacing one generator of the same
kernel preserves the exact subgroup family. This lets the proved quotient
product detect each original quotient without assuming generator independence. -/

namespace Dubon2026.SourceEllipticCyclicCount
open WeierstrassCurve
noncomputable section

/-- A complete distinct prime-kernel family can contain any prescribed point of that exact order. -/
theorem exists_prime_cyclic_generators_containing
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp : (p : K) ≠ 0)
    (P : W.toAffine.Point) (hP : addOrderOf P = p) :
    ∃ Q : Fin (p + 1) → W.toAffine.Point,
      (∀ i, addOrderOf (Q i) = p) ∧
      Function.Injective (fun i => AddSubgroup.zmultiples (Q i)) ∧ ∃ i, Q i = P := by
  classical
  have hex := exists_prime_cyclic_generators (K := K) W p hp
  simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] at hex
  obtain ⟨Q, hQ, hinj, hcomplete⟩ := hex
  obtain ⟨i, hi⟩ := hcomplete (AddSubgroup.zmultiples P)
    ((AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top _).mpr ⟨P, rfl⟩)
    ((Nat.card_zmultiples P).trans hP)
  let R := Function.update Q i P
  have hR (j : Fin (p + 1)) : addOrderOf (R j) = p := by
    by_cases h : j = i
    · subst j
      simpa only [R, Function.update_self] using hP
    · simpa only [R, Function.update_of_ne h] using hQ j
  have hker : (fun j => AddSubgroup.zmultiples (R j)) =
      (fun j => AddSubgroup.zmultiples (Q j)) := by
    funext j
    by_cases h : j = i
    · subst j
      simpa only [R, Function.update_self] using hi.symm
    · simp only [R, Function.update_of_ne h]
  refine ⟨R, hR, ?_, i, ?_⟩
  · simpa only [hker] using hinj
  · exact Function.update_self i P Q

end
end Dubon2026.SourceEllipticCyclicCount
