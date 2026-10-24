import Dubon2026.SourceCurveUnramifiedDifferentialAllChar
import Dubon2026.SourceRatFuncWildDifferent
import Dubon2026.SourceModularCharTwoNormalField
import Dubon2026.SourceNormalFieldCoordinateOrder
import Dubon2026.SourceModularCoefficientLocalDifferentials

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> wild local bound.
At modular j-order twelve, the constructed auxiliary normal field forces
ramification index one. The existing all-characteristic wild bound at
2^2 gives 12 - 1 + (4 - 1) = 14, which descends for the actual differential.
The weighted census and genus comparison remain separate obligations. -/
namespace Dubon2026.SourceFunctionField
open SourceCurve SourceEllipticDivisionField KaehlerDifferential
open CoefficientPresentation IntermediateField
noncomputable section

theorem coeff_place_fourteen_le_D_j_of_char_two_auxiliary
    (K L : Type*) [Field K] [IsAlgClosed K] [Field L]
    [Algebra (RatFunc K) L] [Algebra K L] [IsScalarTower K (RatFunc K) L]
    [FiniteDimensional (RatFunc K) L] [IsGalois (RatFunc K) L]
    [CharP K 2] (N : ℕ) [NeZero N]
    (ι : modularFunctionFieldCoeff N K →ₐ[K] L)
    (hι : ι (jCoeff N K) = algebraMap (RatFunc K) L RatFunc.X)
    (hdvd : ∀ w : Place K L, 0 < w.ord (algebraMap (RatFunc K) L RatFunc.X) →
      w.ord (algebraMap (RatFunc K) L RatFunc.X) ∣ (12 : ℤ))
    (v : Place K (modularFunctionFieldCoeff N K)) (hv : v.ord (jCoeff N K) = 12) :
    14 ≤ v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) := by
  classical
  let F : Type _ := modularFunctionFieldCoeff N K
  letI := algebraAlong ι
  haveI := scalarTower_along ι
  have hfg := finite_galois_along_coordinate (jCoeff N K)
    (transcendental_jCoeff N K) ι hι
  haveI : FiniteDimensional F L := hfg.1
  haveI : IsGalois F L := hfg.2
  have hfinite : ι.toRingHom.Finite := hfg.1
  obtain ⟨w, hw⟩ := Place.restrictAlongFinite_surjective ι hfinite inferInstance v
  change w.restrict F = v at hw
  have hscale : w.ord (algebraMap (RatFunc K) L RatFunc.X) =
      12 * w.ord (algebraMap F L (w.restrict F).uniformizer) := by
    rw [← hι]
    change w.ord (algebraMap F L (jCoeff N K)) = _
    rw [w.ord_algebraMap_restrict, hw, hv]
  have hepos := w.ord_restricted_uniformizer_pos (F := F)
  have hwpos : 0 < w.ord (algebraMap (RatFunc K) L RatFunc.X) := by
    rw [hscale]
    positivity
  have hd := hdvd w hwpos
  have h12 : w.ord (algebraMap (RatFunc K) L RatFunc.X) = 12 := by
    apply Int.dvd_antisymm hwpos.le (by norm_num) hd
    exact ⟨_, hscale⟩
  have heord : w.ord (algebraMap F L (w.restrict F).uniformizer) = 1 := by
    rw [h12] at hscale
    omega
  have he : w.ramificationIndex (F := F) = 1 := by
    have hecast := w.ramificationIndex_cast (F := F)
    rw [heord] at hecast
    exact_mod_cast hecast
  have hbound := w.rational_wild_different_bound 2 hwpos 2 (by rw [h12]; norm_num)
  haveI := finite_positive_rational_place_differentials w hwpos
  haveI := positive_rational_place_dCoordGenerates w hwpos
  haveI := coeff_place_dCoordGenerates N K (w.restrict F)
  haveI : Nontrivial Ω[F⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  haveI : Nontrivial Ω[L⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_rationalExtension_differentials K L)
  haveI := (finite_galois_coordinateField K (M := L)).1
  have hres := place_residue_bijective_of_finite_coordinate
    (algebraMap (RatFunc K) L RatFunc.X) w
  haveI : Module.Finite K w.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap K w.ResidueField) hres.surjective
  haveI : Algebra.IsSeparable K w.ResidueField := inferInstance
  have htransfer := w.ordDifferential_map_of_ramificationIndex_one_all_char he
    (D_jCoeff_ne_zero N K)
  rw [KaehlerDifferential.map_D] at htransfer
  change w.ordDifferential (D K L (ι (jCoeff N K))) = _ at htransfer
  rw [hι, hw] at htransfer
  rw [h12, htransfer] at hbound
  norm_num at hbound
  exact hbound

end
end Dubon2026.SourceFunctionField
