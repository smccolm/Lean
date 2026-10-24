import Dubon2026.SourceEllipticStandardCyclicDistinct
import Dubon2026.SourceEllipticCyclicCount

/-! The literal p+1 standard cyclic subgroups exhaust the actual elliptic
prime-order cyclic subgroups. The previously proved elliptic torsion count
is reused; no new torsion classification is introduced. This provides the
complete indexing family for the DUB-17/18 odd-prime quotient product. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve UpperHalfPlane SourceFunctionField

theorem standardTorsionPoint_zmultiples_complete (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [hp : Fact p.Prime]
    (H : AddSubgroup (C • periodCurve (PeriodLattice.ofTau τ)).toAffine.Point)
    (hH : IsAddCyclic H) (hcardH : Nat.card H = p) :
    ∃ i, AddSubgroup.zmultiples (standardTorsionPoint τ C p i) = H := by
  classical
  let W := C • periodCurve (PeriodLattice.ofTau τ)
  let A := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}
  have hcard : Nat.card A = p + 1 := by
    have h := SourceEllipticCyclicCount.actual_cyclic_subgroup_cardinality
      (K := ℂ) W (Nat.cast_ne_zero.mpr hp.out.ne_zero : (p : ℂ) ≠ 0)
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] at h
    change Nat.card A = SourceLevelProjective.dedekindPsi p at h
    rw [h]
    simpa using SourceLevelProjective.dedekindPsi_prime_pow p 1 hp.out (by decide)
  letI : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  let f : Fin (p + 1) → A := fun i =>
    ⟨AddSubgroup.zmultiples (standardTorsionPoint τ C p i), inferInstance,
      (Nat.card_zmultiples _).trans (standardTorsionPoint_order τ C p i)⟩
  have hf : Function.Injective f := fun i j h =>
    standardTorsionPoint_zmultiples_injective τ C p (congrArg Subtype.val h)
  have hs : Function.Surjective f :=
    (hf.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])).2
  obtain ⟨i, hi⟩ := hs ⟨H, hH, hcardH⟩
  exact ⟨i, congrArg Subtype.val hi⟩

end Dubon2026.SourceEllipticPeriod
