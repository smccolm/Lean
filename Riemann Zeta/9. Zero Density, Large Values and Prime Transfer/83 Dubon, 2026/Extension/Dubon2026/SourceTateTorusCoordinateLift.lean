import Dubon2026.SourceTateTorusCoordinates

/-! DUB-17/18 -> nondegeneracy of the original Tate pairing -> lifting a
detecting finite torsion class. The existing divided-lattice sequence gives
the required lift directly; no general inverse-limit surjectivity is needed. -/
namespace Dubon2026.TateModule.Period
noncomputable section
variable (K : Type*) [Field K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable (p : ℕ) [Fact p.Prime] (Λ : Submodule ℤ V)

include K in
theorem exists_tate_coordinate_of_torsion (k : ℕ) (q : V ⧸ Λ)
    (hq : ((p ^ k : ℕ) : ℤ) • q = 0) :
    ∃ x : TateModule p (V ⧸ Λ), (x : ℕ → V ⧸ Λ) k = q := by
  obtain ⟨v, rfl⟩ := Λ.mkQ_surjective q
  have hv : ((p ^ k : ℕ) : ℤ) • v ∈ Λ := by
    apply (Submodule.Quotient.mk_eq_zero Λ).mp
    change Λ.mkQ (((p ^ k : ℕ) : ℤ) • v) = 0
    rw [map_zsmul]
    exact hq
  refine ⟨iota K p Λ ⟨_, hv⟩, ?_⟩
  rw [coe_iota_apply, divLevel_natCast_pow_smul]
  rfl

include K in
theorem exists_tate_coordinate_of_torsion_image {M : Type*} [AddCommGroup M]
    (f : M →+ V ⧸ Λ) (k : ℕ) (q : M) (hq : (p ^ k) • q = 0) :
    ∃ x : TateModule p (V ⧸ Λ), (x : ℕ → V ⧸ Λ) k = f q := by
  apply exists_tate_coordinate_of_torsion K p Λ
  rw [Nat.cast_smul_eq_nsmul ℤ, ← map_nsmul, hq, map_zero]

end
end Dubon2026.TateModule.Period
