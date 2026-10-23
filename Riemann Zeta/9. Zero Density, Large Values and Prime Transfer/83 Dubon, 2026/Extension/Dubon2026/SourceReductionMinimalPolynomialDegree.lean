import Dubon2026.SourceReductionReciprocalPolynomial

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison -> preservation of pole bounds. Polynomial degree at a
transcendental coordinate is controlled by integrality on its inverse chart.
The minimal-polynomial coefficient bound uses the actual integral function on
both charts. This defers the source's general valuation-subring formulation:
the required original modular consumer can use the proved chart-integrality
criterion directly. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, with native transcendence,
polynomial equivalence and principal-ideal transport. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem natDegree_minpoly_coordinate_coeff_le
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (hinv : IsIntegral (Algebra.adjoin L ({x⁻¹} : Set F)) (f * (x ^ m)⁻¹))
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by
  classical

  set q : Polynomial (Algebra.adjoin L ({x} : Set F)) :=
    minpoly (Algebra.adjoin L ({x} : Set F)) f with hq
  set d : ℕ := q.natDegree with hd
  set n : ℕ := (d - j) * m with hn
  set y : F := x⁻¹ with hy
  have hyL : Transcendental L y := fun h => hxL (IsAlgebraic.inv_iff.mp h)
  set g : F := f * (x ^ m)⁻¹ with hg

  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({x} : Set F)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental L x hxL).toRingHom
      (Polynomial.algEquivOfTranscendental L x hxL).surjective
  haveI : IsPrincipalIdealRing (Algebra.adjoin L ({y} : Set F)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental L y hyL).toRingHom
      (Polynomial.algEquivOfTranscendental L y hyL).surjective
  have hgint : IsIntegral (Algebra.adjoin L ({y} : Set F)) g := hinv

  have hxK : x ∈ IntermediateField.adjoin L ({y} : Set F) := by
    rw [show x = y⁻¹ from (inv_inv x).symm ▸ congrArg Inv.inv hy.symm]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self L y)
  have hyKx : y ∈ IntermediateField.adjoin L ({x} : Set F) := by
    rw [hy]; exact inv_mem (IntermediateField.mem_adjoin_simple_self L x)
  have hKeq : IntermediateField.adjoin L ({x} : Set F) = IntermediateField.adjoin L ({y} : Set F) :=
    le_antisymm
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxK))
      (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hyKx))

  have hmpgLy : ∀ i, ((minpoly (IntermediateField.adjoin L ({y} : Set F)) g).coeff i : F) ∈
      Algebra.adjoin L ({y} : Set F) := by
    intro i
    have heq := minpoly.isIntegrallyClosed_eq_field_fractions'
      (R := Algebra.adjoin L ({y} : Set F)) (IntermediateField.adjoin L ({y} : Set F)) hgint
    rw [heq, Polynomial.coeff_map]
    exact ((minpoly (Algebra.adjoin L ({y} : Set F)) g).coeff i).2

  have hmpfq : minpoly (IntermediateField.adjoin L ({x} : Set F)) f =
      q.map (algebraMap (Algebra.adjoin L ({x} : Set F))
        (IntermediateField.adjoin L ({x} : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hint
  have hmpfd : (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).natDegree = d := by
    rw [hmpfq, (minpoly.monic hint).natDegree_map, hd]

  have hxKmem : x ∈ IntermediateField.adjoin L ({x} : Set F) :=
    IntermediateField.mem_adjoin_simple_self L x
  set xK : IntermediateField.adjoin L ({x} : Set F) := ⟨x, hxKmem⟩ with hxK
  have hxK0 : xK ≠ 0 := fun h => hx0 (congrArg Subtype.val h)

  have hgsmul : g = (xK ^ m)⁻¹ • f := by
    rw [hg, Algebra.smul_def, map_inv₀, map_pow, mul_comm]
    rfl

  have hfintK : IsIntegral (IntermediateField.adjoin L ({x} : Set F)) f := hint.tower_top

  letI : Module.IsTorsionFree (IntermediateField.adjoin L ({x} : Set F)) F :=
    DivisionSemiring.to_moduleIsTorsionFree

  have hmpg_scale : minpoly (IntermediateField.adjoin L ({x} : Set F)) g =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).scaleRoots ((xK ^ m)⁻¹) := by
    rw [hgsmul]
    exact IsIntegrallyClosed.minpoly_smul (inv_ne_zero (pow_ne_zero m hxK0)) hfintK

  have hcoefj : (minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j =
      (minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j * ((xK ^ m)⁻¹) ^ (d - j) := by
    rw [hmpg_scale, Polynomial.coeff_scaleRoots, hmpfd]

  have hcoefF : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F) =
      ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
    have hcast1 : ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) =
        ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) := by
      rw [hmpfq, Polynomial.coeff_map]; rfl
    have hcast2 : (((xK ^ m)⁻¹ ^ (d - j) :
        IntermediateField.adjoin L ({x} : Set F)) : F) = (x ^ n)⁻¹ := by
      push_cast
      rw [show ((xK : IntermediateField.adjoin L ({x} : Set F)) : F) = x from rfl,
        ← inv_pow, ← pow_mul, hn, mul_comm m (d - j), inv_pow]
    calc ((minpoly (IntermediateField.adjoin L ({x} : Set F)) g).coeff j : F)
        = ((minpoly (IntermediateField.adjoin L ({x} : Set F)) f).coeff j : F) *
            (((xK ^ m)⁻¹ ^ (d - j) : IntermediateField.adjoin L ({x} : Set F)) : F) := by
          rw [hcoefj]; push_cast; ring
      _ = ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ := by
          rw [hcast1, hcast2]

  have hkey : ((q.coeff j : Algebra.adjoin L ({x} : Set F)) : F) * (x ^ n)⁻¹ ∈
      Algebra.adjoin L ({y} : Set F) := by
    rw [← hcoefF, hKeq]
    exact hmpgLy j

  rw [← hc] at hkey
  have hy2 : ({x⁻¹} : Set F) = {y} := by rw [hy]
  rw [← hy2] at hkey
  exact natDegree_le_of_aeval_mul_inv_pow_mem_adjoin_inv x hxL hx0 c n hkey

end
end Dubon2026.SourceCurve.RegularProlongation
