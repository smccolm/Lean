import Dubon2026.SourceEllipticSpecializationTorsionRange

/-! The literal torsion specialization identifies actual cyclic subgroups
of order N. Existing injective subgroup image equivalences are composed
with the source torsion inclusion; the proved torsion lifting removes the
target range restriction. This is the finite-field version required by
DUB-17/18, without an algebraically closed generic-field assumption. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve SourceEllipticCyclicCount
noncomputable section

/-- An injective actual torsion specialization reaching all target torsion identifies cyclic subgroups. -/
def cyclicTorsionSpecializationEquiv
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] (N : ℕ)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ H) (hθ : Function.Injective θ)
    (hr : ∀ x : H, N • x = 0 → x ∈ θ.range) :
    {S : AddSubgroup G // IsAddCyclic S ∧ Nat.card S = N} ≃
      {S : AddSubgroup H // IsAddCyclic S ∧ Nat.card S = N} := by
  let T := Submodule.torsionBy ℤ G (N : ℤ)
  let ι := T.subtype.toAddMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hs : ∀ x : G, N • x = 0 → x ∈ ι.range := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    change x ∈ Submodule.torsionBy ℤ G (N : ℤ)
    simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hx
  let es := (cyclicAddSubgroupMapEquiv N ι hι).trans
    (Equiv.subtypeEquivRight fun S => show
      (IsAddCyclic S ∧ Nat.card S = N ∧ S ≤ ι.range) ↔
        (IsAddCyclic S ∧ Nat.card S = N) from
      ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, le_of_card_eq_of_nsmul_mem N h.2 hs⟩⟩)
  let er := (cyclicAddSubgroupMapEquiv N θ hθ).trans
    (Equiv.subtypeEquivRight fun S => show
      (IsAddCyclic S ∧ Nat.card S = N ∧ S ≤ θ.range) ↔
        (IsAddCyclic S ∧ Nat.card S = N) from
      ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, le_of_card_eq_of_nsmul_mem N h.2 hr⟩⟩)
  exact es.symm.trans er

theorem cyclicTorsionSpecializationEquiv_apply_coe
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] (N : ℕ)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ H) (hθ : Function.Injective θ)
    (hr : ∀ x : H, N • x = 0 → x ∈ θ.range)
    (S : {S : AddSubgroup G // IsAddCyclic S ∧ Nat.card S = N}) :
    (cyclicTorsionSpecializationEquiv N θ hθ hr S).val =
      (S.val.comap (Submodule.torsionBy ℤ G (N : ℤ)).subtype.toAddMonoidHom).map θ := rfl

/-- The full N-squared torsion count supplies the actual elliptic cyclic-subgroup specialization. -/
def ellipticCyclicSpecializationEquiv
    {G K : Type*} [AddCommGroup G] [Field K] [IsAlgClosed K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (N : ℕ) (hNK : (N : K) ≠ 0)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ E₀.toAffine.Point) (hθ : Function.Injective θ)
    (hcard : Nat.card {P : G // N • P = 0} = N ^ 2) :
    {S : AddSubgroup G // IsAddCyclic S ∧ Nat.card S = N} ≃
      {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} :=
  cyclicTorsionSpecializationEquiv N θ hθ (torsion_mem_specialization_range E₀ N hNK θ hθ hcard)

theorem mem_ellipticCyclicSpecializationEquiv
    {G K : Type*} [AddCommGroup G] [Field K] [IsAlgClosed K] [DecidableEq K]
    (E₀ : WeierstrassCurve K) [E₀.IsElliptic] (N : ℕ) (hNK : (N : K) ≠ 0)
    (θ : Submodule.torsionBy ℤ G (N : ℤ) →+ E₀.toAffine.Point) (hθ : Function.Injective θ)
    (hcard : Nat.card {P : G // N • P = 0} = N ^ 2)
    (S : {S : AddSubgroup G // IsAddCyclic S ∧ Nat.card S = N}) (Q : E₀.toAffine.Point) :
    Q ∈ (ellipticCyclicSpecializationEquiv E₀ N hNK θ hθ hcard S).val ↔
      ∃ P : Submodule.torsionBy ℤ G (N : ℤ), P.val ∈ S.val ∧ θ P = Q := by
  rw [ellipticCyclicSpecializationEquiv, cyclicTorsionSpecializationEquiv_apply_coe,
    AddSubgroup.mem_map]
  rfl

end
end Dubon2026.SourceEllipticReduction
