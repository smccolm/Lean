import Dubon2026.SourcePrimeTorsionCommonScalar

/-! DUB-17/18 -> characteristic-two fixed cyclic-subgroup count nuTwo.
The source quaternion relation forces a nonscalar action on odd prime
torsion. Existing common-scalar linear algebra avoids repeating coordinates.
The actual elliptic automorphisms must still supply these displayed relations.
Source: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, characteristic-two nuTwo solution. -/
namespace Dubon2026.SourceEllipticExceptional
noncomputable section
variable {A : Type*} [AddCommGroup A]

theorem quartic_nonscalar_of_quaternion_relations
    (α : A →+ A) (β : A ≃+ A) (δ : A →+ A)
    (hα : ∀ T, α (α T) = -T) (hδ : ∀ T, δ (δ T) = -T)
    (hcomp : ∀ T, δ T = α (β (α (β.symm T))))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (e : ZMod p × ZMod p ≃+ Submodule.torsionBy ℤ A p) :
    ∃ T : A, addOrderOf T = p ∧ ∀ k : ℕ, α T ≠ k • T := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, P, hord, hscalar⟩ := prime_torsion_scalar_data α p hp e hcon
  have hδT : ∀ T : A, (p : ℤ) • T = 0 → δ T = -T := by
    intro T hT
    have hβT : (p : ℤ) • β.symm T = 0 := by rw [← map_zsmul, hT, map_zero]
    rw [hcomp, hscalar (β.symm T) hβT, map_zsmul, β.apply_symm_apply,
      ← hscalar T hT, hα]
  have hpP : (p : ℤ) • P = 0 := by
    rw [natCast_zsmul, ← hord]
    exact addOrderOf_nsmul_eq_zero P
  have hneg : P = -P := by
    calc P = δ (δ P) := by rw [hδT P hpP, map_neg, hδT P hpP, neg_neg]
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
