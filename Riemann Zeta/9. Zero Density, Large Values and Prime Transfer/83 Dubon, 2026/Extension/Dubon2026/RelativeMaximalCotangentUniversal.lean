import Dubon2026.RelativeMaximalCotangentDerivation

/-! # The universal property of the actual relative maximal-ideal quotient -/

namespace Dubon2026

noncomputable section

variable {O R M : Type*} [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R]
  [AddCommGroup M] [Module R M] [Module O M]

/-- The original maximal-ideal elements killed by a genuine relative derivation form an actual ideal when that maximal ideal annihilates its coefficient module. -/
def relativeResidueDerivationZeroIdeal (d : Derivation O R M)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) : Ideal R where
  carrier := {r | r ∈ IsLocalRing.maximalIdeal R ∧ d r = 0}
  zero_mem' := ⟨(IsLocalRing.maximalIdeal R).zero_mem, map_zero d⟩
  add_mem' hx hy := ⟨(IsLocalRing.maximalIdeal R).add_mem hx.1 hy.1,
    by rw [map_add, hx.2, hy.2, add_zero]⟩
  smul_mem' r x hx := by
    refine ⟨(IsLocalRing.maximalIdeal R).mul_mem_left r hx.1, ?_⟩
    change d (r * x) = 0
    rw [d.leibniz, hx.2, smul_zero, @hM (d r) ⟨x, hx.1⟩, add_zero]

/-- The genuine square and original coefficient maximal-ideal relations vanish under every original relative residue derivation. -/
theorem relativeMaximalCotangentRelations_le_zeroIdeal
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : Derivation O R M)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    (IsLocalRing.maximalIdeal R) ^ 2 ⊔
      (IsLocalRing.maximalIdeal O).map (algebraMap O R) ≤
        relativeResidueDerivationZeroIdeal d hM := by
  apply sup_le
  · rw [pow_two, Ideal.mul_le]
    intro x hx y hy
    refine ⟨(IsLocalRing.maximalIdeal R).mul_mem_left x hy, ?_⟩
    rw [d.leibniz, @hM (d y) ⟨x, hx⟩, @hM (d x) ⟨y, hy⟩, add_zero]
  · apply Ideal.map_le_iff_le_comap.mpr
    intro o ho
    refine ⟨?_, d.map_algebraMap o⟩
    apply (localCoefficientReduction_eq_zero_iff eR _).mp
    rw [AlgHom.commutes]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ho

/-- Restrict an original relative residue derivation to the actual original maximal ideal; it is genuinely linear over the original ring. -/
def relativeResidueDerivationOnMaximal (d : Derivation O R M)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    IsLocalRing.maximalIdeal R →ₗ[R] M where
  toFun x := d x.val
  map_add' x y := map_add d x.val y.val
  map_smul' r x := by
    change d (r * x.val) = r • d x.val
    rw [d.leibniz, @hM (d r) x, add_zero]

/-- Every genuine original relative residue derivation descends through the actual relative maximal-ideal quotient. -/
def relativeMaximalCotangentLift
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : Derivation O R M)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    RelativeMaximalCotangent O R →ₗ[R] M :=
  (relativeMaximalCotangentRelations O R).liftQ
    (relativeResidueDerivationOnMaximal d hM) (by
      intro x hx
      exact (relativeMaximalCotangentRelations_le_zeroIdeal eR d hM hx).2)

/-- The descended map retains every original maximal-ideal derivative value. -/
theorem relativeMaximalCotangentLift_mk
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : Derivation O R M)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (x : IsLocalRing.maximalIdeal R) :
    relativeMaximalCotangentLift eR d hM (relativeMaximalCotangentMk O R x) = d x.val := rfl

/-- Descending through the genuine maximal-ideal quotient and applying its original universal derivation recovers the entire original derivation. -/
theorem relativeMaximalCotangentLift_derivation
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (d : Derivation O R M)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) (r : R) :
    relativeMaximalCotangentLift eR d hM (relativeMaximalCotangentDerivation eR r) = d r := by
  change d (r - algebraMap O R (originalResidueRepresentative eR r)) = d r
  rw [map_sub, d.map_algebraMap, sub_zero]

variable [IsScalarTower O R M]

/-- Genuine relative residue derivations are precisely the linear maps from the actual relative maximal-ideal quotient. -/
def relativeMaximalCotangentDerivationEquiv
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    (RelativeMaximalCotangent O R →ₗ[R] M) ≃ₗ[R] Derivation O R M :=
  { Derivation.llcomp.flip (relativeMaximalCotangentDerivation eR) with
    invFun := fun d => relativeMaximalCotangentLift eR d hM
    left_inv := by
      intro f
      apply LinearMap.ext
      intro y
      obtain ⟨x, rfl⟩ := relativeMaximalCotangentMk_surjective O R y
      rw [relativeMaximalCotangentLift_mk]
      change f (relativeMaximalCotangentDerivation eR x.val) = _
      rw [relativeMaximalCotangentDerivation_maximal]
    right_inv := by
      intro d
      apply Derivation.ext
      intro r
      exact relativeMaximalCotangentLift_derivation eR d hM r }

/-- The universal comparison uses the genuine original ring derivation on every element. -/
theorem relativeMaximalCotangentDerivationEquiv_apply
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (hM : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (f : RelativeMaximalCotangent O R →ₗ[R] M) (r : R) :
    relativeMaximalCotangentDerivationEquiv eR hM f r =
      f (relativeMaximalCotangentDerivation eR r) := rfl

end
end Dubon2026
