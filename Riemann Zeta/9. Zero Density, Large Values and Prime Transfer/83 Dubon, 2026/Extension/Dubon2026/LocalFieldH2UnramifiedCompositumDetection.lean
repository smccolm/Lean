import Dubon2026.FiniteGaloisH2DescentUnderBaseChange
import Dubon2026.LocalFieldInvariantBaseChange
import Dubon2026.LocalFieldUnramifiedCompositum
import Dubon2026.LocalFieldFiniteContinuousH2Bound

/-! # Every original finite local H2 class is detected by an actual unramified compositum -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

private theorem reverse_range_lift_of_card_bound
    {A B C : Type*} [Finite B] (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hcard : Nat.card B ≤ Nat.card A)
    (h : ∀ a, ∃ b, g b = f a) : ∀ b, ∃ a, g b = f a := by
  choose j hj using h
  have hinj : Function.Injective j := by
    intro x y hxy
    apply hf
    rw [← hj, ← hj, hxy]
  have hsurj := (hinj.bijective_of_nat_card_le hcard).2
  intro b
  obtain ⟨a, rfl⟩ := hsurj b
  exact ⟨a, hj a⟩

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [IsGalois K E] [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

/-- If L/K is the actual unramified extension of the same degree as E/K,
every original E/K unit H2 class agrees with a genuine L/K class after
inflation to the literal compositum. Unramifiedness over E and all H2 order
bounds are proved from the original fields, rather than assumed as certificates. -/
theorem localFieldH2_exists_unramified_compositum_representative
    (htop : (algebraMap E M).fieldRange ⊔ (algebraMap L M).fieldRange = ⊤)
    (hdegree : Module.finrank K L = Module.finrank K E)
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E)) :
    letI : FiniteDimensional K M := localField_field_module_finite
    ∃ y : GaloisUnitContinuousH2 (K := K) (Ω := L),
      finiteGaloisUnitTowerH2Inflation K E M x = finiteGaloisUnitTowerH2Inflation K L M y := by
  haveI : FiniteDimensional K E := localField_field_module_finite
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : FiniteDimensional K M := localField_field_module_finite
  haveI : FiniteDimensional E M := localField_field_module_finite
  haveI : IsGalois E M := IsGalois.tower_top_of_isGalois K E M
  haveI : Algebra.FormallyUnramified 𝒪[E] 𝒪[M] :=
    localField_integer_unramified_of_compositum K E L M htop
  obtain ⟨hfinite, hdvd⟩ := localField_finite_continuous_h2_card_dvd K E
  haveI := hfinite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  have hcardL : Nat.card (GaloisUnitContinuousH2 (K := K) (Ω := L)) =
      Module.finrank K L := by
    rw [Nat.card_congr (localFieldPeriodH2Equiv K L).toEquiv, Nat.card_zmod]
  have hcard : Nat.card (GaloisUnitContinuousH2 (K := K) (Ω := E)) ≤
      Nat.card (GaloisUnitContinuousH2 (K := K) (Ω := L)) := by
    rw [hcardL, hdegree]
    exact Nat.le_of_dvd Module.finrank_pos hdvd
  apply reverse_range_lift_of_card_bound
    (finiteGaloisUnitTowerH2Inflation K L M) (finiteGaloisUnitTowerH2Inflation K E M)
    (finiteGaloisUnitTowerH2Inflation_injective K L M) hcard _ x
  intro y
  apply (finiteGaloisH2_exists_inflation_eq_iff_baseChange_zero K E L M y).mpr
  apply (finiteGaloisUnitBaseChangeH2_eq_zero_iff K E L M y).mpr
  rw [← hdegree]
  exact (localFieldPeriodRationalInvariant_mem_range_iff K L _).mp ⟨y, rfl⟩

end
end Dubon2026
