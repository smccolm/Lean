import Dubon2026.SourceEllipticPeriodQuotientCoordinates
import Dubon2026.SourceEllipticPeriodLocalScalar
import Dubon2026.SourceEllipticWeierstrassNonconstant

/-! The actual odd point norm has a holomorphic affine germ with nonzero
target y-coordinate. Surjectivity chooses the germ, the exact kernel formula
excludes its denominators, and the literal finite Velu formulas prove
analyticity. This discharges the local hypothesis in the DUB-17/18 complex
quotient compatibility route; no local-lift assumption remains here. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set WeierstrassCurve WeierstrassCurve.Affine
open SourceEllipticVariableChange SourceEllipticFunctionField SourceEllipticVelu
open SourceEllipticVelu.OddDiscriminant.Algebra
open scoped Topology PeriodPair

theorem exists_periodOddNorm_affine_germ
    (L M : PeriodPair) [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (C D : VariableChange ℂ) {Q : (C • periodCurve L).toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1)
    (hD : veluQuotient (C • periodCurve L)
      (oddOrderSummingSet (C • periodCurve L) Q n) = D • periodCurve M) :
    ∃ (z₀ : ℂ) (U : Set ℂ), U ∈ 𝓝 z₀ ∧ ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, Y z ≠ 0 ∧ ∃ h,
        periodOddNorm L M C D hQ hD (periodHom L z) = Point.some (X z) (Y z) h := by
  classical
  let W := C • periodCurve L
  let S := oddOrderSummingSet W Q n
  let x : ℂ → ℂ := fun z => vcXInv C (℘[L] z)
  let y : ℂ → ℂ := fun z => vcYInv C (℘[L] z) (℘'[L] z / 2)
  let X : ℂ → ℂ := fun z => vcX D (veluAffineX W S (x z))
  let Y : ℂ → ℂ := fun z => vcY D (veluAffineX W S (x z)) (veluAffineY W S (x z) (y z))
  let ψ := periodOddNorm L M C D hQ hD
  have hxa {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ x z := by
    have hp := L.analyticOnNhd_weierstrassP z hz
    dsimp [x, vcXInv]
    fun_prop
  have hya {z : ℂ} (hz : z ∉ L.lattice) : AnalyticAt ℂ y z := by
    have hp := L.analyticOnNhd_weierstrassP z hz
    have hpd := L.analyticOnNhd_derivWeierstrassP z hz
    dsimp [y, vcYInv]
    fun_prop
  have hXY {z : ℂ} (hz : z ∉ L.lattice) (hd : (hP S Prod.fst).eval (x z) ≠ 0) :
      AnalyticAt ℂ X z ∧ AnalyticAt ℂ Y z := by
    have hx := analyticAt_veluAffineX W S (hxa hz) hd
    have hy := analyticAt_veluAffineY W S (hxa hz) (hya hz) hd
    constructor
    · dsimp [X, vcX]; fun_prop
    · dsimp [Y, vcY]; fun_prop
  obtain ⟨w, hw, hwd⟩ := exists_derivWeierstrassP_ne_zero M
  have hw0 : periodHom M w ≠ 0 := by
    exact fun h => hw ((periodPoint_eq_zero_iff M w).mp h)
  obtain ⟨z₀, hz₀⟩ := ((periodOddNorm_surjective L M C D hQ hD).comp
    (periodHom_surjective L)) (periodHom M w)
  have hz₀L : z₀ ∉ L.lattice := by
    intro h
    have hp : periodHom L z₀ = 0 := periodPoint_of_mem L h
    rw [Function.comp_apply, hp, map_zero] at hz₀
    exact hw0 hz₀.symm
  have hd₀ : (hP S Prod.fst).eval (x z₀) ≠ 0 := by
    intro h
    have heq := (periodOddNorm_eq_zero_iff L M C D hQ hD hz₀L).mpr h
    exact hw0 (hz₀.symm.trans heq)
  have hy₀ : Y z₀ ≠ 0 := by
    obtain ⟨hns, heq⟩ := periodOddNorm_affine L M C D hQ hD hz₀L hd₀
    have hpt : periodPoint M w = Point.some (X z₀) (Y z₀) hns := hz₀.symm.trans heq
    rw [periodPoint_of_notMem M hw, Point.some.injEq] at hpt
    rw [← hpt.2]
    exact div_ne_zero hwd two_ne_zero
  have hevL : ∀ᶠ z in 𝓝 z₀, z ∉ L.lattice :=
    L.isClosed_lattice.isOpen_compl.mem_nhds hz₀L
  have hevD : ∀ᶠ z in 𝓝 z₀, (hP S Prod.fst).eval (x z) ≠ 0 :=
    ((hP S Prod.fst).continuousAt.comp (hxa hz₀L).continuousAt).eventually
      (isOpen_ne.mem_nhds hd₀)
  have hevY : ∀ᶠ z in 𝓝 z₀, Y z ≠ 0 :=
    (hXY hz₀L hd₀).2.continuousAt.eventually (isOpen_ne.mem_nhds hy₀)
  let U : Set ℂ := {z | z ∉ L.lattice ∧ (hP S Prod.fst).eval (x z) ≠ 0 ∧ Y z ≠ 0}
  refine ⟨z₀, U, hevL.and (hevD.and hevY), X, Y, ?_, ?_, ?_⟩
  · exact fun z hz => (hXY hz.1 hz.2.1).1.differentiableAt.differentiableWithinAt
  · exact fun z hz => (hXY hz.1 hz.2.1).2.differentiableAt.differentiableWithinAt
  · intro z hz
    exact ⟨hz.2.2, periodOddNorm_affine L M C D hQ hD hz.1 hz.2.1⟩

end Dubon2026.SourceEllipticPeriod
