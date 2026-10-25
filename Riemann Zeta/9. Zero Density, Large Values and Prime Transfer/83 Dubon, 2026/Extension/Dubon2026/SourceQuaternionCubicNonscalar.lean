import Dubon2026.SourcePrimeTorsionCommonScalar

/-! DUB-17/18 -> characteristic-two fixed cyclic-subgroup count nuThree.
A commutator squaring to negation rules out a common scalar on odd prime
torsion. Existing common-scalar linear algebra replaces the repeated source
coordinates. The actual elliptic actions must still supply the relations.
Source: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, characteristic-two nuThree solution. -/
namespace Dubon2026.SourceEllipticExceptional
noncomputable section
variable {A : Type*} [AddCommGroup A]

theorem cubic_nonscalar_of_quaternion_commutator
    (α β : A ≃+ A) (δ : A →+ A)
    (hδ : ∀ T, δ (δ T) = -T)
    (hcomp : ∀ T, δ T = β.symm (α (β (α.symm T))))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ZMod p × ZMod p ≃+ Submodule.torsionBy ℤ A p) :
    ∃ T : A, addOrderOf T = p ∧ ∀ k : ℕ, β T ≠ k • T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, P, hord, hscalar⟩ := prime_torsion_scalar_data β.toAddMonoidHom p hp e hcon
  have hδT : ∀ T : A, (p : ℤ) • T = 0 → δ T = T := by
    intro T hT
    have hαT : (p : ℤ) • α.symm T = 0 := by rw [← map_zsmul, hT, map_zero]
    change ∀ T : A, (p : ℤ) • T = 0 → β T = c • T at hscalar
    rw [hcomp, hscalar (α.symm T) hαT, map_zsmul, α.apply_symm_apply,
      ← hscalar T hT, β.symm_apply_apply]
  have hpP : (p : ℤ) • P = 0 := by
    rw [natCast_zsmul, ← hord]
    exact addOrderOf_nsmul_eq_zero P
  have hneg : P = -P := by
    calc P = δ (δ P) := by rw [hδT P hpP, hδT P hpP]
      _ = -P := hδ P
  have htwo : (2 : ℕ) • P = 0 := by
    rw [two_nsmul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  have hd : p ∣ 2 := by
    rw [← hord]
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

end
end Dubon2026.SourceEllipticExceptional
