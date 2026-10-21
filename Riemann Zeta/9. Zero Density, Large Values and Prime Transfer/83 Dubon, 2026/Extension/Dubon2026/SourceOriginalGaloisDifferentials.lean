import Dubon2026.SourceOriginalGaloisCoordinates
import Dubon2026.SourceOriginalDifferentialRank
import Dubon2026.SourceCurveTranscendence
import Dubon2026.SourceCurveLocalDifferentials
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! DUB-17/18 -> global residue identity -> auxiliary Galois geometry.
The original one-dimensional differential space stays one-dimensional under
the actual finite separable normal-closure extension. Native etale base change
and the existing finite-coordinate spanning theorem then give every genuine
place its uniformizer coordinate. No rank or local-spanning premise remains.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve SourceDifferential KaehlerDifferential

private theorem differential_finrank_baseChange
    (K F E : Type*) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.FormallyEtale F E] :
    Module.finrank E Ω[E⁄K] = Module.finrank F Ω[F⁄K] := by
  rw [← (tensorKaehlerEquivOfFormallyEtale K F E).finrank_eq, Module.finrank_baseChange]

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The native function-field module structure on the auxiliary differentials. -/
instance originalGaloisDifferentialModule :
    Module (originalGaloisClosure N L) Ω[originalGaloisClosure N L⁄L] :=
  KaehlerDifferential.module' (R := L) (S := originalGaloisClosure N L)

theorem finrank_originalGaloisClosure_differentials :
    Module.finrank (originalGaloisClosure N L) Ω[originalGaloisClosure N L⁄L] = 1 := by
  let F := modularFunctionFieldOver N L
  let G := originalGaloisClosure N L
  letI : Algebra F G := originalGaloisClosureOriginalAlgebra N L
  letI : Module F G := originalGaloisClosureOriginalModule N L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap L F).injective
  haveI : FiniteDimensional F G := finite_originalGaloisClosure_over_original N L
  haveI : Algebra.FormallyEtale F G := Algebra.FormallyEtale.of_isSeparable F G
  rw [differential_finrank_baseChange L F G]
  exact finrank_original_differentials N L

theorem originalGaloisClosure_place_dCoordGenerates (v : Place L (originalGaloisClosure N L)) :
    v.DCoordGenerates := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  let J := IntermediateField.adjoin L {v.uniformizer}
  letI : Algebra L J := J.toSubalgebra.algebra
  haveI : CharZero J := charZero_of_injective_algebraMap (algebraMap L J).injective
  have ht := v.transcendental_of_ord_ne_zero (by rw [v.ord_uniformizer]; exact one_ne_zero)
  haveI : FiniteDimensional J (originalGaloisClosure N L) :=
    finite_originalGaloisClosure_over_transcendental N L ht
  exact ⟨span_D_eq_top_of_transcendental L v.uniformizer ht⟩

end
end Dubon2026.SourceFunctionField
