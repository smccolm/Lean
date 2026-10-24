import Dubon2026.SourcePrimeTorsionScalarAction
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.OrderOfElement

/-! DUB-17/18 -> characteristic-three genus -> cubic fixed cyclic count.
The existing common-scalar theorem avoids repeating rank-two coordinates
in the source nonscalar argument. The concrete elliptic automorphisms
must still supply the two displayed algebraic relations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_ord_jqModC_census_of_char_three. -/
namespace Dubon2026.SourceEllipticExceptional
noncomputable section
variable {A : Type*} [AddCommGroup A]

theorem cubic_nonscalar_of_dihedral_relations
    (α : A ≃+ A) (β : A →+ A)
    (hβ : ∀ T, β (β T) + β T + T = 0)
    (hαβ : ∀ T, α (β T) = β (β (α T)))
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (e : ZMod p × ZMod p ≃+ Submodule.torsionBy ℤ A p) :
    ∃ T : A, addOrderOf T = p ∧ ∀ k : ℕ, β T ≠ k • T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  let V := Submodule.torsionBy ℤ A p
  have hmem : ∀ T : V, (p : ℤ) • (T : A) = 0 :=
    fun T => (Submodule.mem_torsionBy_iff _ _).mp T.2
  let σ : V →+ V :=
    { toFun := fun T => ⟨β T, by
        rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hmem, map_zero]⟩
      map_zero' := Subtype.ext (map_zero β)
      map_add' := fun T U => Subtype.ext (map_add β (T : A) (U : A)) }
  have heig : ∀ T : V, ∃ a : ℤ, σ T = a • T := by
    intro T
    by_cases hT : (T : A) = 0
    · exact ⟨0, Subtype.ext (by
        change β (T : A) = (0 : ℤ) • (T : A)
        rw [zero_smul, hT, map_zero])⟩
    · have hord : addOrderOf (T : A) = p := by
        apply addOrderOf_eq_prime _ hT
        rw [← natCast_zsmul]
        exact hmem T
      obtain ⟨k, hk⟩ := hcon T hord
      exact ⟨k, Subtype.ext (by change β (T : A) = (k : ℤ) • (T : A); simpa using hk)⟩
  obtain ⟨c, hc⟩ := exists_common_scalar e σ heig
  have hscalar : ∀ T : A, (p : ℤ) • T = 0 → β T = c • T := by
    intro T hT
    exact congrArg Subtype.val (hc ⟨T, (Submodule.mem_torsionBy_iff _ _).mpr hT⟩)
  let P : A := e (1, 0)
  have hP0 : P ≠ 0 := by
    intro h
    have he : e (1, 0) = e 0 := by rw [map_zero]; exact Subtype.ext h
    have h10 := e.injective he
    exact one_ne_zero (congrArg Prod.fst h10)
  have hpP : (p : ℤ) • P = 0 := hmem (e (1, 0))
  have hpαP : (p : ℤ) • α P = 0 := by rw [← map_zsmul, hpP, map_zero]
  have hord : addOrderOf P = p :=
    addOrderOf_eq_prime (by rwa [← natCast_zsmul]) hP0
  have hordα : addOrderOf (α P) = p :=
    addOrderOf_eq_prime (by rwa [← natCast_zsmul]) (fun h => hP0 (α.injective (h.trans α.map_zero.symm)))
  have hrel : (c * c - c) • α P = 0 := by
    have h := hαβ P
    rw [hscalar P hpP, map_zsmul, hscalar (α P) hpαP, map_zsmul,
      hscalar (α P) hpαP, ← mul_zsmul] at h
    rw [sub_zsmul, ← h, add_neg_cancel]
  have hpoly : (c * c + c + 1) • P = 0 := by
    have h := hβ P
    rw [hscalar P hpP, map_zsmul, hscalar P hpP, ← mul_zsmul] at h
    rw [add_zsmul, add_zsmul, one_zsmul]
    exact h
  have hd1 : (c : ZMod p) * c - c = 0 := by
    have h := (addOrderOf_dvd_iff_zsmul_eq_zero (x := α P)).mpr hrel
    rw [hordα] at h
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (c * c - c) p).mpr h
  have hd2 : (c : ZMod p) * c + c + 1 = 0 := by
    have h := (addOrderOf_dvd_iff_zsmul_eq_zero (x := P)).mpr hpoly
    rw [hord] at h
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (c * c + c + 1) p).mpr h
  have h3 : (3 : ZMod p) = 0 := by
    have h2 : 2 * (c : ZMod p) + 1 = 0 := by linear_combination hd2 - hd1
    linear_combination 4 * hd2 - (2 * (c : ZMod p) + 1) * h2
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdvd)

end
end Dubon2026.SourceEllipticExceptional
