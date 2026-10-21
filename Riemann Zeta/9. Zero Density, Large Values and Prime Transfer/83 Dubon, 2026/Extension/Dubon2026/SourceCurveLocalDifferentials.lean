import Dubon2026.SourceCurvePlaces
import Mathlib.RingTheory.Kaehler.Basic

/-! DUB-17/18 -> regular differential realization -> actual local coordinates.
The regular differential space is defined using every actual place and its
uniformizer. Generic coefficient lemmas expose the local spanning property;
SourceOriginalLocalDifferentials proves it for the original modular field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_CanonicalDivisor.lean and
Definitions/Def_AlgebraicCurve_RegularDifferentials.lean.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}
variable (v : Place K F)

/-- An actual irreducible element of the place's discrete valuation ring. -/
def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

/-- The actual relative differential of the chosen local uniformizer. -/
def dCoord : Ω[F⁄K] := KaehlerDifferential.D K F v.uniformizer

/-- The explicit local-coordinate spanning property, proved for the original field downstream. -/
class DCoordGenerates : Prop where
  span_eq_top : Submodule.span F {v.dCoord} = ⊤

theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 := by
  intro h0
  have htop := DCoordGenerates.span_eq_top (v := v)
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have hx_mem : x ∈ Submodule.span F {v.dCoord} := htop ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hx_mem
  exact hx hx_mem

/-- The coefficient of the actual differential in its local coordinate when it exists. -/
def differentialCoeff (ω : Ω[F⁄K]) : F :=
  letI := Classical.propDecidable
  if h : ∃ f : F, ω = f • v.dCoord then h.choose else 0

theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • v.dCoord := by
  have hω : ω ∈ (⊤ : Submodule F Ω[F⁄K]) := Submodule.mem_top
  rw [← DCoordGenerates.span_eq_top (v := v), Submodule.mem_span_singleton] at hω
  exact hω.imp fun _ hf => hf.symm

theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    v.differentialCoeff ω • v.dCoord = ω := by
  rw [differentialCoeff, dif_pos (v.exists_eq_smul_dCoord ω)]
  exact (v.exists_eq_smul_dCoord ω).choose_spec.symm

theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f := by
  have key : (v.differentialCoeff ω - f) • v.dCoord = 0 := by
    rw [sub_smul, v.differentialCoeff_smul_dCoord ω, hf, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h v.dCoord_ne_zero

@[simp]
theorem differentialCoeff_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff v.dCoord = 1 :=
  v.differentialCoeff_unique (one_smul F v.dCoord).symm

@[simp]
theorem differentialCoeff_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff (0 : Ω[F⁄K]) = 0 :=
  v.differentialCoeff_unique (zero_smul F v.dCoord).symm

theorem differentialCoeff_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (c : F) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = c * v.differentialCoeff ω :=
  v.differentialCoeff_unique
    (by rw [mul_smul, v.differentialCoeff_smul_dCoord])

/-- The actual place order of the local differential coefficient. -/
def ordDifferential (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)

theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.ordDifferential v.dCoord = 0 := by
  rw [ordDifferential, v.differentialCoeff_dCoord, v.ord_one]

theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : v.differentialCoeff ω ≠ 0) :
    v.ordDifferential (c • ω) = v.ord c + v.ordDifferential ω := by
  rw [ordDifferential, ordDifferential, v.differentialCoeff_smul, v.ord_mul hc hω]

end Place

namespace Place
variable {K F}

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, v.ord_zero]
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) :=
      (isUnit_iff_ne_zero.mpr hc).map _
    obtain ⟨u, hu⟩ := hu
    have he : algebraMap K F c = ((u : v.toValuationSubring) : F) := by
      rw [← v.coe_algebraMap c, ← hu]
    rw [he, v.ord_coe_unit]

end Place

/-- Relative differentials whose local coefficient belongs to every actual place valuation ring. -/
def regularDifferentials : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord}
  zero_mem' v := ⟨0, v.toValuationSubring.zero_mem, by rw [zero_smul]⟩
  add_mem' {ω η} hω hη v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    obtain ⟨g, hg, hη'⟩ := hη v
    exact ⟨f + g, v.toValuationSubring.add_mem _ _ hf hg, by rw [hη', add_smul]⟩
  smul_mem' c {ω} hω v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    refine ⟨algebraMap K F c * f, v.toValuationSubring.mul_mem _ _ (v.algebraMap_mem' c) hf, ?_⟩
    rw [mul_smul, algebraMap_smul]

variable {K F} in
theorem mem_regularDifferentials_iff {ω : Ω[F⁄K]} :
    ω ∈ regularDifferentials K F ↔
      ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord :=
  Iff.rfl

end
end Dubon2026.SourceCurve
