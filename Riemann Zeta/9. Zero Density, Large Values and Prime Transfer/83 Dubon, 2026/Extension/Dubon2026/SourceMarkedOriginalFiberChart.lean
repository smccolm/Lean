import Dubon2026.SourceMarkedOriginalPlaceChart
import Dubon2026.SourceMarkedFullTorsionNonempty
import Dubon2026.SourceMarkedChartFiberSurjection

/-! DUB-17/18 -> reverse genus -> finite elliptic residue fibers. The actual
original Gamma1 j fiber is exhausted by exact-order points in the source
finite Galois torsion field. Equality is precisely inertia transport up to
sign, and the original diamond action is exact on the resulting places.
The existing torsion-field and prescribed-place constructions supply the
explicit upstream finite Galois, full-torsion and positive-order inputs. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open WeierstrassCurve CongruenceSubgroup GammaOne GammaOne.ToricCoordinates IntegralDiamond SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem exists_original_marked_fiber_chart
    (hℓN : ¬ ℓ ∣ N) (hN : 2 ≤ N) [DecidableEq (RatFunc kk)]
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (M : Type*) [Field M] [DecidableEq M] [Algebra kk M] [Algebra (RatFunc kk) M]
    [IsScalarTower kk (RatFunc kk) M] [FiniteDimensional (RatFunc kk) M] [IsGalois (RatFunc kk) M]
    (hfull : Nat.card {P : ((ofJ (RatFunc.X : RatFunc kk)).baseChange M).toAffine.Point //
      N • P = 0} = N ^ 2)
    (w : Place kk M) (c : kk)
    (hw : 0 < w.ord (algebraMap (RatFunc kk) M RatFunc.X - algebraMap kk M c)) :
    let E := ofJ (RatFunc.X : RatFunc kk)
    ∃ f : {P : (E.baseChange M).toAffine.Point // addOrderOf P = N} →
        {v : Place kk F // 0 < v.ord (x - algebraMap kk F c)},
      Function.Surjective f ∧
      (∀ P P', f P' = f P ↔
        ∃ σ : w.toValuationSubring.inertiaSubgroup (RatFunc kk),
          P'.val = Affine.Point.map (W' := E) σ.val.val.toAlgHom P.val ∨
            P'.val = -(Affine.Point.map (W' := E) σ.val.val.toAlgHom P.val)) ∧
      ∀ (γ : Gamma0 N) P P',
        P'.val = (((gamma0Unit N γ)⁻¹ : (ZMod N)ˣ) : ZMod N).val • P.val →
        (f P').val = (f P).val.comapEquiv (originalResidueDiamondAction A N ℓ hℓN γ) := by
  classical
  letI := valuation_residue_isAlgClosed A
  let E := ofJ (RatFunc.X : RatFunc kk)
  obtain ⟨Φ, hfinite, _, hdia, _, _, hsurj, horbit⟩ :=
    exists_original_ofJ_place_chart A N ℓ hℓN hN x hx M hfull
  have hxtr : Transcendental kk x := by
    intro h
    apply transcendental_jqModC kk
    rw [← hx]
    exact h.algHom (F).val
  have hNK : (N : kk) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff kk ℓ N).mp h)
  have hNM : (N : M) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap kk M)).mpr hNK
  obtain ⟨P₀, hP₀⟩ := exists_exactOrder_point_of_full_torsion (E.baseChange M) N hNM hfull
  obtain ⟨f, hf, hfsurj⟩ := exists_marked_fiber_surjection_of_embedding_exhaustion
    E N x hxtr P₀ hP₀ Φ hsurj hfinite w c hw
  refine ⟨f, hfsurj, ?_, ?_⟩
  · intro P P'
    have he : f P' = f P ↔ (f P').val = (f P).val := Subtype.ext_iff
    rw [he, hf, hf]
    exact horbit w P P'
  · intro γ P P' h
    rw [hf, hf]
    apply Place.ext
    ext z
    rw [Place.mem_restrictAlongFinite_iff, Place.mem_comapEquiv_iff,
      Place.mem_restrictAlongFinite_iff]
    have he := AlgHom.congr_fun (hdia γ P P' h) z
    change (Φ P').val z ∈ w.toValuationSubring ↔
      (Φ P).val (originalResidueDiamondAction A N ℓ hℓN γ z) ∈ w.toValuationSubring
    rw [he]
    rfl

end
end Dubon2026.SourceFunctionField.MarkedChart
