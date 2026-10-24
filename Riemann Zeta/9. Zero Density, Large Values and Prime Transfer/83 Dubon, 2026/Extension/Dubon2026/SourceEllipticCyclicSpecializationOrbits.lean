import Dubon2026.SourceEllipticSubgroupSpecializationTransport
import Dubon2026.SourceEllipticGaloisTorsionMap

/-! The pointwise specialization inputs give the exact source cyclic
subgroup relation if and only if the original field action relates the
generic subgroups. The full image up to sign loses no subgroup orbit,
because negation fixes every additive subgroup. The next consumer derives
all inputs from the actual finite Galois ofJ(X) specialization. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticStabilizer
noncomputable section
variable {F M K : Type*} [Field F] [Field M] [Field K]
variable [Algebra F M] [DecidableEq M] [DecidableEq K]

theorem cyclic_specialization_orbit_iff
    (E : WeierstrassCurve F) (E₀ : WeierstrassCurve K) (N : ℕ) (hN : N ≠ 0)
    (I : Type*) [Group I] (σGal : I → M ≃ₐ[F] M)
    (θ : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ) →+ E₀.toAffine.Point)
    (hθ : Function.Injective θ) (ρ : I →* VariableChange K)
    (hfix : ∀ σ, ρ σ • E₀ = E₀)
    (heq : ∀ σ P, HEq (SourceEllipticVariableChange.vcInvFun (ρ σ) E₀.toAffine (θ P))
      (θ (galoisTorsionMap E N (σGal σ) P)))
    (hfull : ∀ δ : VariableChange K, δ • E₀ = E₀ → ∃ σ : I,
      (∀ P, HEq (SourceEllipticVariableChange.vcInvFun δ E₀.toAffine (θ P))
        (θ (galoisTorsionMap E N (σGal σ) P))) ∨
      (∀ P, HEq (SourceEllipticVariableChange.vcInvFun δ E₀.toAffine (θ P))
        (-(θ (galoisTorsionMap E N (σGal σ) P)))))
    (Ψ : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N} ≃
      {S : AddSubgroup E₀.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N})
    (hΨ : ∀ S Q, Q ∈ (Ψ S).val ↔
      ∃ P : Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ),
        P.val ∈ S.val ∧ θ P = Q)
    (S T : {S : AddSubgroup (E.baseChange M).toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    cyclicStabilizerRelated E₀ (Ψ S).val (Ψ T).val ↔
      ∃ σ : I, S.val.map (Point.map ((σGal σ) : M →ₐ[F] M)) = T.val := by
  let A := Submodule.torsionBy ℤ (E.baseChange M).toAffine.Point (N : ℤ)
  let ι := A.subtype.toAddMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hr : ∀ U : {S : AddSubgroup (E.baseChange M).toAffine.Point //
      IsAddCyclic S ∧ Nat.card S = N}, U.val ≤ ι.range := by
    intro U
    apply SourceEllipticCyclicCount.le_of_card_eq_of_nsmul_mem N U.property.2
    intro P hP
    exact ⟨⟨P, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP⟩, rfl⟩
  have hm : ∀ U, (Ψ U).val = (U.val.comap ι).map θ := by
    intro U
    ext Q
    rw [hΨ, AddSubgroup.mem_map]
    rfl
  have transfer (σ : I) (δ : VariableChange K) (hδ : δ • E₀ = E₀)
      (h : (∀ P, HEq (SourceEllipticVariableChange.vcInvFun δ E₀.toAffine (θ P))
          (θ (galoisTorsionMap E N (σGal σ) P))) ∨
        (∀ P, HEq (SourceEllipticVariableChange.vcInvFun δ E₀.toAffine (θ P))
          (-(θ (galoisTorsionMap E N (σGal σ) P))))) :
      (Ψ S).val.map (stabilizerPointEquiv E₀ δ hδ).toAddMonoidHom = (Ψ T).val ↔
        S.val.map (Point.map ((σGal σ) : M →ₐ[F] M)) = T.val := by
    rw [hm S, hm T]
    apply specialization_subgroup_map_eq_iff ι hι θ hθ S.val T.val (hr S) (hr T)
      (galoisTorsionMap E N (σGal σ)) _ _ (fun _ => rfl)
    rcases h with h | h
    · exact Or.inl fun P => (stabilizerPointEquiv_eq_iff_heq E₀ δ hδ _ _).mpr (h P)
    · exact Or.inr fun P => (stabilizerPointEquiv_eq_iff_heq E₀ δ hδ _ _).mpr (h P)
  rw [cyclicStabilizerRelated_iff_map_eq E₀ N hN]
  constructor
  · rintro ⟨δ, hδ, hmap⟩
    obtain ⟨σ, hσ⟩ := hfull δ hδ
    exact ⟨σ, (transfer σ δ hδ hσ).mp hmap⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨ρ σ, hfix σ, (transfer σ (ρ σ) (hfix σ) (Or.inl (heq σ))).mpr hσ⟩

end
end Dubon2026.SourceEllipticReduction
