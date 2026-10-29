import Dubon2026.SourceMarkedOriginalOfJChart
import Dubon2026.SourceMarkedChartPlaceOrbits

/-! DUB-17/18 -> reverse genus -> finite elliptic fibers -> original Gamma1
place chart. Assemble the actual ofJ marked chart with native finite
embedding restriction and the inertia-orbit criterion. Original Laurent
j transcendence proves every embedding finite. Equal restricted places
are exactly actual inertia orbits on marked points modulo sign; the chart
retains exact diamond covariance and exhaustion. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve CongruenceSubgroup GammaOne GammaOne.ToricCoordinates IntegralDiamond SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem exists_original_ofJ_place_chart
    (hℓN : ¬ ℓ ∣ N) (hN : 2 ≤ N) [DecidableEq (RatFunc kk)]
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (M : Type*) [Field M] [DecidableEq M] [Algebra kk M] [Algebra (RatFunc kk) M]
    [IsScalarTower kk (RatFunc kk) M] [FiniteDimensional (RatFunc kk) M] [IsGalois (RatFunc kk) M]
    (hfull : Nat.card {P : ((ofJ (RatFunc.X : RatFunc kk)).baseChange M).toAffine.Point //
      N • P = 0} = N ^ 2) :
    let E := ofJ (RatFunc.X : RatFunc kk)
    ∃ (Ψ : {P : (E.baseChange M).toAffine.Point // addOrderOf P = N} →
        {ψ : F →ₐ[kk] M // ψ x = algebraMap (RatFunc kk) M RatFunc.X})
      (hfinite : ∀ P, (Ψ P).val.toRingHom.Finite),
      (∀ (σ : M ≃ₐ[RatFunc kk] M) P P', P'.val = Affine.Point.map (W' := E) σ.toAlgHom P.val →
        (Ψ P').val = (σ.toAlgHom.restrictScalars kk).comp (Ψ P).val) ∧
      (∀ (γ : Gamma0 N) P P',
        P'.val = (((gamma0Unit N γ)⁻¹ : (ZMod N)ˣ) : ZMod N).val • P.val →
        (Ψ P').val = (Ψ P).val.comp (originalResidueDiamondAction A N ℓ hℓN γ).toAlgHom) ∧
      (∀ P P', P'.val = -P.val → Ψ P' = Ψ P) ∧
      (∀ P P', Ψ P' = Ψ P → P'.val = P.val ∨ P'.val = -P.val) ∧
      Function.Surjective Ψ ∧
      ∀ (w : Place kk M) P P',
        Place.restrictAlongFinite (Ψ P').val (hfinite P') w =
          Place.restrictAlongFinite (Ψ P).val (hfinite P) w ↔
        ∃ σ : w.toValuationSubring.inertiaSubgroup (RatFunc kk),
          P'.val = Affine.Point.map (W' := E) σ.val.val.toAlgHom P.val ∨
            P'.val = -(Affine.Point.map (W' := E) σ.val.val.toAlgHom P.val) := by
  obtain ⟨Ψ, hnat, hdia, hneg, hsep, hsurj⟩ :=
    exists_original_ofJ_full_torsion_chart A N ℓ hℓN hN x hx M hfull
  letI := valuation_residue_isAlgClosed A
  have hxtr : Transcendental kk x := by
    intro h
    apply transcendental_jqModC kk
    rw [← hx]
    exact h.algHom (F).val
  let hfinite := fun P => (finite_galois_along_coordinate x hxtr (Ψ P).val (Ψ P).property).1
  have hi : ∀ P P', Ψ P' = Ψ P ↔ P'.val = P.val ∨ P'.val = -P.val := by
    intro P P'
    refine ⟨hsep P P', ?_⟩
    rintro (h | h)
    · exact congrArg Ψ (Subtype.ext h)
    · exact hneg P P' h
  refine ⟨Ψ, hfinite, hnat, hdia, hneg, hsep, hsurj, ?_⟩
  intro w P P'
  exact marked_chart_restrict_eq_iff_inertia_sign (ofJ (RatFunc.X : RatFunc kk)) N x hxtr
    Ψ hnat hi w P P'

end
end Dubon2026.SourceFunctionField.MarkedChart
