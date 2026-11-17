import Dubon2026.SourceMarkedOriginalLocalDifferentials
import Dubon2026.SourceCurveUnramifiedDifferentialAllChar
import Dubon2026.SourceRatFuncWildDifferent
import Dubon2026.SourceCurveFiniteEmbeddingRestriction

/-! DUB-17/18 -> reverse original genus -> strong wild local orders.
The normal auxiliary field's order divisibility forces ramification index
one above a place attaining that order. The native all-characteristic
different estimate then descends to the actual original Gamma1 field.
The constructed order bounds twelve and six instantiate this single
argument with characteristic powers four and three respectively. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open CongruenceSubgroup GammaOne SourceCurve KaehlerDifferential IntermediateField
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

theorem original_wild_different_of_normal_order_bound
    (hℓN : ¬ ℓ ∣ N) (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (L : Type*) [Field L] [Algebra kk L] [Algebra (RatFunc kk) L]
    [IsScalarTower kk (RatFunc kk) L] [FiniteDimensional (RatFunc kk) L] [IsGalois (RatFunc kk) L]
    (ι : F →ₐ[kk] L) (hι : ι x = algebraMap (RatFunc kk) L RatFunc.X)
    (n : ℤ) (hn : 0 < n) (a : ℕ) (ha : (ℓ : ℤ) ^ a ∣ n)
    (hdvd : ∀ w : Place kk L, 0 < w.ord (algebraMap (RatFunc kk) L RatFunc.X) →
      w.ord (algebraMap (RatFunc kk) L RatFunc.X) ∣ n)
    (v : Place kk F) (hv : v.ord x = n) :
    n - 1 + ((ℓ : ℤ) ^ a - 1) ≤ v.ordDifferential (D kk F x) := by
  classical
  letI := valuation_residue_isAlgClosed A
  letI := algebraAlong ι
  haveI := scalarTower_along ι
  have hxtr : Transcendental kk x := by
    intro h
    apply transcendental_jqModC kk
    rw [← hx]
    exact h.algHom (F).val
  have hfg := finite_galois_along_coordinate x hxtr ι hι
  haveI : FiniteDimensional F L := hfg.1
  haveI : IsGalois F L := hfg.2
  have hfinite : ι.toRingHom.Finite := hfg.1
  obtain ⟨w, hw⟩ := Place.restrictAlongFinite_surjective ι hfinite inferInstance v
  change w.restrict F = v at hw
  have hscale : w.ord (algebraMap (RatFunc kk) L RatFunc.X) =
      n * w.ord (algebraMap F L (w.restrict F).uniformizer) := by
    rw [← hι]
    change w.ord (algebraMap F L x) = _
    rw [w.ord_algebraMap_restrict, hw, hv]
  have hepos := w.ord_restricted_uniformizer_pos («F» := F)
  have hwpos : 0 < w.ord (algebraMap (RatFunc kk) L RatFunc.X) := by
    rw [hscale]
    exact mul_pos hn hepos
  have hnord : w.ord (algebraMap (RatFunc kk) L RatFunc.X) = n := by
    apply Int.dvd_antisymm hwpos.le hn.le (hdvd w hwpos)
    exact ⟨_, hscale⟩
  have heord : w.ord (algebraMap F L (w.restrict F).uniformizer) = 1 := by
    rw [hnord] at hscale
    exact mul_left_cancel₀ hn.ne' (by simpa only [mul_one] using hscale.symm)
  have he : w.ramificationIndex («F» := F) = 1 := by
    have hecast := w.ramificationIndex_cast («F» := F)
    rw [heord] at hecast
    exact_mod_cast hecast
  have hbound := w.rational_wild_different_bound ℓ hwpos a (by rw [hnord]; exact ha)
  haveI := finite_positive_rational_place_differentials w hwpos
  haveI := positive_rational_place_dCoordGenerates w hwpos
  haveI := original_positive_place_dCoordGenerates A N ℓ hℓN x hx (w.restrict F)
    (by rw [hw, hv]; exact hn)
  haveI : Nontrivial Ω[F⁄kk] := nontrivial_of_ne _ _ (original_j_D_ne_zero A N x hx)
  haveI : Nontrivial Ω[L⁄kk] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_rationalExtension_differentials kk L)
  haveI := (finite_galois_coordinateField kk (M := L)).1
  have hres := place_residue_bijective_of_finite_coordinate
    (algebraMap (RatFunc kk) L RatFunc.X) w
  haveI : Module.Finite kk w.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap kk w.ResidueField) hres.surjective
  haveI : Algebra.IsSeparable kk w.ResidueField := inferInstance
  have htransfer := w.ordDifferential_map_of_ramificationIndex_one_all_char he
    (original_j_D_ne_zero A N x hx)
  rw [KaehlerDifferential.map_D] at htransfer
  change w.ordDifferential (D kk L (ι x)) = _ at htransfer
  rw [hι, hw] at htransfer
  rwa [hnord, htransfer] at hbound

end
end Dubon2026.SourceFunctionField.MarkedChart
