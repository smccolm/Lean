import Dubon2026.SourceReductionChartPlaceExistence
import Dubon2026.SourceCurveIntegralChartPlaceEquality
import Dubon2026.SourceCurveFiniteCoordinateResidues
import Dubon2026.SourceConstantFieldOrderResidues

/-! DUB-17/18 -> original Frobenius/inertia -> modular good reduction ->
reduction-place comparison. Integral-chart lifting and the exact original
residue values determine a unique reduction place. Existing finite-coordinate
residue surjectivity and Dedekind-chart centers replace the external
separating-function argument. The chart-lifting hypothesis is the strictly
upstream theorem already proved for the actual tame modular Gauss reduction;
the next modular consumer must supply it. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem constant_eq_zero_of_mem_nonunits
    {K E : Type*} [Field K] [Field E] [Algebra K E]
    (W : Place K E) (b : K) (hb : algebraMap K E b ∈ W.toValuationSubring.nonunits) :
    algebraMap K E b = 0 := by
  by_contra h0
  have hb0 : b ≠ 0 := fun he => h0 (by rw [he, map_zero])
  have hm : algebraMap K W.toValuationSubring b ∈ maximalIdeal W.toValuationSubring :=
    ValuationSubring.coe_mem_nonunits_iff.mp hb
  exact (IsLocalRing.mem_maximalIdeal _).mp hm
    ((isUnit_iff_ne_zero.mpr hb0).map (algebraMap K W.toValuationSubring))

theorem existsUnique_reduction_chart_place [IsAlgClosed L]
    (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    [Algebra.IsSeparable (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar]
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ g : Fbar, IsIntegral (Algebra.adjoin (ResidueField A) {R.residue x}) g →
      ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = g)
    (P : Place L F) (hP : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) :
    ∃! Q : Place (ResidueField A) Fbar,
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits := by
  obtain ⟨a₀, ha₀⟩ := hP
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (by rw [hdeg]; exact hfin)
  have hxint : IsIntegral (Algebra.adjoin L {(x : F)}) (x : F) :=
    isIntegral_algebraMap (x := (⟨x, Algebra.self_mem_adjoin_singleton L (x : F)⟩ :
      Algebra.adjoin L {(x : F)}))
  obtain ⟨Q, hQ⟩ := exists_reduction_chart_place R x hx hfin hdeg P ha₀
  refine ⟨Q, hQ, fun Q' hQ' => ?_⟩
  have hxP : (x : F) ∈ P.toValuationSubring := mem_of_sub_algebraMap_mem_nonunits P ha₀
  have hxQ := mem_of_sub_algebraMap_mem_nonunits Q (hQ x hxint a₀ ha₀)
  have hxQ' := mem_of_sub_algebraMap_mem_nonunits Q' (hQ' x hxint a₀ ha₀)
  apply Place.eq_of_integral_chart_nonunits (R.residue x) hx Q' Q hxQ' hxQ
  intro g hg
  obtain ⟨f, hfint, hfres⟩ := hchart g hg
  have hfP : (f : F) ∈ P.toValuationSubring := P.mem_of_integral_adjoin hxP hfint
  obtain ⟨b, hb⟩ := ConstantField.exists_sub_algebraMap_mem_maximalIdeal P
    (place_residue_bijective_of_finite_coordinate (x : F) P).surjective ⟨f, hfP⟩
  have hbP : (f : F) - algebraMap L F b ∈ P.toValuationSubring.nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr hb
  have hbA : b ∈ A := mem_of_sub_mem_nonunits R x hx hfin hdeg P ha₀ f.2 hfint hbP
  have hbQ := hQ f hfint ⟨b, hbA⟩ hbP
  have hbQ' := hQ' f hfint ⟨b, hbA⟩ hbP
  rw [hfres] at hbQ hbQ'
  constructor
  · intro hgQ'
    have hβ : algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨b, hbA⟩) ∈
        Q'.toValuationSubring.nonunits := by
      simpa only [sub_sub_cancel] using sub_mem hgQ' hbQ'
    have hβ0 := constant_eq_zero_of_mem_nonunits Q' _ hβ
    rwa [hβ0, sub_zero] at hbQ
  · intro hgQ
    have hβ : algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨b, hbA⟩) ∈
        Q.toValuationSubring.nonunits := by
      simpa only [sub_sub_cancel] using sub_mem hgQ hbQ
    have hβ0 := constant_eq_zero_of_mem_nonunits Q _ hβ
    rwa [hβ0, sub_zero] at hbQ'

end
end Dubon2026.SourceCurve.RegularProlongation
