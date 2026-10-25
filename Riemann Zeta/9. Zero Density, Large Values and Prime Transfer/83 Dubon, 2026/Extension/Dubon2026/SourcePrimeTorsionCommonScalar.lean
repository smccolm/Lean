import Dubon2026.SourceDihedralCubicNonscalar

/-! DUB-17/18 -> characteristic-two weighted census -> elliptic fixed-subgroup
counts -> nonscalar prime-torsion actions. The existing common-scalar theorem
replaces the source's repeated rank-two coordinate calculations. The witness
and scalar are extracted from the actual prime-torsion equivalence. -/
namespace Dubon2026.SourceEllipticExceptional
noncomputable section
variable {A : Type*} [AddCommGroup A]

theorem prime_torsion_scalar_data (σ : A →+ A) (p : ℕ) (hp : p.Prime)
    (e : ZMod p × ZMod p ≃+ Submodule.torsionBy ℤ A p)
    (heigen : ∀ T : A, addOrderOf T = p → ∃ k : ℕ, σ T = k • T) :
    ∃ (c : ℤ) (P : A), addOrderOf P = p ∧
      ∀ T : A, (p : ℤ) • T = 0 → σ T = c • T := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let V := Submodule.torsionBy ℤ A p
  have hmem : ∀ T : V, (p : ℤ) • (T : A) = 0 :=
    fun T => (Submodule.mem_torsionBy_iff _ _).mp T.2
  let σT : V →+ V :=
    { toFun := fun T => ⟨σ T, by
        rw [Submodule.mem_torsionBy_iff, ← map_zsmul, hmem, map_zero]⟩
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun T U => Subtype.ext (map_add σ (T : A) (U : A)) }
  have heig : ∀ T : V, ∃ a : ℤ, σT T = a • T := by
    intro T
    by_cases hT : (T : A) = 0
    · exact ⟨0, Subtype.ext (by
        change σ (T : A) = (0 : ℤ) • (T : A)
        rw [zero_smul, hT, map_zero])⟩
    · have hord : addOrderOf (T : A) = p := by
        apply addOrderOf_eq_prime _ hT
        rw [← natCast_zsmul]
        exact hmem T
      obtain ⟨k, hk⟩ := heigen T hord
      exact ⟨k, Subtype.ext (by change σ (T : A) = (k : ℤ) • (T : A); simpa using hk)⟩
  obtain ⟨c, hc⟩ := exists_common_scalar e σT heig
  let P : A := e (1, 0)
  have hP0 : P ≠ 0 := by
    intro h
    have he : e (1, 0) = e 0 := by rw [map_zero]; exact Subtype.ext h
    exact one_ne_zero (congrArg Prod.fst (e.injective he))
  have hpP : (p : ℤ) • P = 0 := hmem (e (1, 0))
  have hord : addOrderOf P = p :=
    addOrderOf_eq_prime (by rwa [← natCast_zsmul]) hP0
  refine ⟨c, P, hord, ?_⟩
  intro T hT
  exact congrArg Subtype.val (hc ⟨T, (Submodule.mem_torsionBy_iff _ _).mpr hT⟩)

end
end Dubon2026.SourceEllipticExceptional
