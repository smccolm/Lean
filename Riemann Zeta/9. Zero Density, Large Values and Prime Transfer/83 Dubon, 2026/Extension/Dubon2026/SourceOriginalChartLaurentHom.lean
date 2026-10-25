import Dubon2026.SourceMeromorphicLaurentRealization
import Dubon2026.SourceOriginalChartGermHom

/-! DUB-17/18 -> auxiliary torsion-cover analytic entry.
Realize the actual original chart readings in the existing field of
convergent Laurent quotients. Uniqueness of the represented Laurent series
and the proved chart germ laws give the algebra homomorphism. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldOver N ℂ

/-- The convergent Laurent quotient of the actual original chart reading. -/
def chartLaurent (v : Place ℂ FF) (f : FF) : realizedField :=
  (exists_realized_represents (meromorphicAt_chartRead N v f
    (mem_ball_self (place_spec N v).1))).choose

theorem chartLaurent_represents (v : Place ℂ FF) (f : FF) :
    Represents (chartLaurent N v f).val (chartRead N v f) :=
  (exists_realized_represents (meromorphicAt_chartRead N v f
    (mem_ball_self (place_spec N v).1))).choose_spec

theorem chartLaurent_algebraMap (v : Place ℂ FF) (c : ℂ) :
    chartLaurent N v (algebraMap ℂ FF c) = algebraMap ℂ realizedField c := by
  apply Subtype.ext
  apply (chartLaurent_represents N v _).eq_series
  rw [chartRead_algebraMap]
  exact represents_const c

theorem chartLaurent_add (v : Place ℂ FF) (f g : FF) :
    chartLaurent N v (f + g) = chartLaurent N v f + chartLaurent N v g := by
  apply Subtype.ext
  exact (chartLaurent_represents N v _).eq_series
    (((chartLaurent_represents N v f).add (chartLaurent_represents N v g)).congr (chartRead_add N v f g))

theorem chartLaurent_mul (v : Place ℂ FF) (f g : FF) :
    chartLaurent N v (f * g) = chartLaurent N v f * chartLaurent N v g := by
  apply Subtype.ext
  exact (chartLaurent_represents N v _).eq_series
    (((chartLaurent_represents N v f).mul (chartLaurent_represents N v g)).congr (chartRead_mul N v f g))

/-- The original function field embedded by its actual convergent local readings. -/
def chartLaurentHom (v : Place ℂ FF) : FF →ₐ[ℂ] realizedField where
  toFun := chartLaurent N v
  map_zero' := by simpa only [map_zero] using chartLaurent_algebraMap N v 0
  map_one' := by simpa only [map_one] using chartLaurent_algebraMap N v 1
  map_add' := chartLaurent_add N v
  map_mul' := chartLaurent_mul N v
  commutes' := chartLaurent_algebraMap N v

theorem chartLaurentHom_order (v : Place ℂ FF) (f : FF) (hf : f ≠ 0) :
    ((chartLaurentHom N v f : realizedField) : LaurentSeries ℂ).order = v.ord f := by
  have hne : (chartLaurent N v f).val ≠ 0 := by
    intro he
    exact ((map_ne_zero (chartLaurentHom N v)).mpr hf) (Subtype.ext he)
  have ho := (chartLaurent_represents N v f).order hne
  change meromorphicOrderAt (fun z => originalPlaceEval N ℂ (placeFamily N v z) f) 0 = _ at ho
  rw [meromorphicOrderAt_place_reading N v hf] at ho
  exact WithTop.coe_injective ho.symm

end
end Dubon2026.SourceFunctionField.OriginalChart
