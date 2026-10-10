import Mathlib.NumberTheory.RamificationInertia.Ramification

/-! # Unramified original prime indices in genuine Dedekind towers -/

namespace Dubon2026

variable {R S T : Type*} [CommRing R] [IsDomain R]
  [CommRing S] [IsDedekindDomain S] [CommRing T] [IsDedekindDomain T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Module.IsTorsionFree R S] [Module.IsTorsionFree S T]

/-- A genuine total ramification index of one forces both original tower indices to be one. -/
theorem unramifiedIdealTower_indices
    (p : Ideal R) (P : Ideal S) (Q : Ideal T)
    [Q.IsPrime] [Q.LiesOver P] [P.LiesOver p]
    (h : p.ramificationIdx Q = 1) :
    p.ramificationIdx P = 1 ∧ P.ramificationIdx Q = 1 := by
  have hprod := (Ideal.ramificationIdx_algebra_tower' p P Q).symm.trans h
  exact ⟨Nat.eq_one_of_mul_eq_one_right hprod, Nat.eq_one_of_mul_eq_one_left hprod⟩

end Dubon2026
