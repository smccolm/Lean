import Dubon2026.SourceReductionIndependent
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> arithmetic automorphy and residual association -> original
weight-two Frobenius/inertia -> actual good reduction -> genus comparison ->
preservation of dimensions under coefficient reduction. These lemmas serve
that finite-space dimension theorem; no genus or good-reduction claim is made.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Native polynomial monomial independence
replaces the external custom coefficient linear-combination equivalence. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem transcendental_powers_linearIndependent {K B : Type*} [Field K] [CommRing B]
    [Algebra K B] {x : B} (hx : Transcendental K x) :
    LinearIndependent K (fun j : ℕ => x ^ j) := by
  have h := (Polynomial.basisMonomials K).linearIndependent.map'
    (Polynomial.aeval x).toLinearMap
    (LinearMap.ker_eq_bot.mpr (transcendental_iff_injective.mp hx))
  simpa [Polynomial.coe_basisMonomials, Function.comp_def, Polynomial.aeval_monomial] using h

section frame

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

/-- Products of coordinate powers and lifted residue-basis elements. -/
def frame (p : ℕ × Fin n) : R.integers := x ^ p.1 * y p.2

@[simp] theorem coe_frame (p : ℕ × Fin n) :
    ((frame R x y p : R.integers) : F) = (x : F) ^ p.1 * (y p.2 : F) := by
  simp [frame]

include hx in

theorem linearIndependent_residue_pow :
    LinearIndependent (ResidueField A) (fun j : ℕ => R.residue (x ^ j)) := by
  have : (fun j : ℕ => R.residue (x ^ j)) = fun j => (R.residue x) ^ j := by
    funext j; rw [map_pow]
  rw [this]
  exact transcendental_powers_linearIndependent hx

include hx hy in

theorem linearIndependent_residue_frame :
    LinearIndependent (ResidueField A) (fun p : ℕ × Fin n => R.residue (frame R x y p)) := by
  set k := ResidueField A
  set xb := R.residue x
  have hgen : LinearIndependent k
      (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) := by
    apply LinearIndependent.of_comp
      ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap)
    have : ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap : _ → Fbar) ∘
        (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) = fun j : ℕ => xb ^ j := by
      funext j
      simp
    rw [this]
    exact transcendental_powers_linearIndependent hx
  have h := linearIndependent_smul hgen hy
  have hfun : (fun p : ℕ × Fin n => R.residue (frame R x y p)) =
      fun p : ℕ × Fin n => xb ^ p.1 * R.residue (y p.2) := by
    funext p
    simp [frame, map_mul, map_pow, xb]
  rw [hfun]
  convert h using 1

include hx hy in

theorem linearIndependent_coe_frame :
    LinearIndependent L (fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F)) := by
  have h := linearIndependent_coe R (frame R x y) (linearIndependent_residue_frame R x hx y hy)
  have hfun : (fun p : ℕ × Fin n => ((frame R x y p : R.integers) : F)) =
      fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F) := by
    funext p; exact coe_frame R x y p
  rwa [hfun] at h

include hx hy in

theorem linearIndependent_adjoin :
    LinearIndependent (Algebra.adjoin L ({(x : F)} : Set F)) (fun i : Fin n => (y i : F)) := by
  have h2 := linearIndependent_coe_frame R x hx y hy
  rw [linearIndependent_iff']
  intro t g hsum
  have hg : ∀ i, ∃ p : Polynomial L, Polynomial.aeval (x : F) p = (g i : F) := fun i => by
    have h : (g i : F) ∈ (Polynomial.aeval (R := L) (x : F)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hg
  set N := t.sup (fun i => (p i).natDegree) + 1 with hN
  have hlt : ∀ i ∈ t, (p i).natDegree < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
  have hzero := linearIndependent_iff'.mp h2 (Finset.range N ×ˢ t)
    (fun q => (p q.2).coeff q.1) ?_
  · intro i hi
    have hpi : p i = 0 := by
      ext j
      by_cases hj : j < N
      · exact hzero (j, i) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hi)
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le (hlt i hi) (not_lt.mp hj))
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  · rw [Finset.sum_product_right, ← hsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Subalgebra.smul_def, ← hp i, Polynomial.aeval_eq_sum_range' (hlt i hi),
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    exact (smul_mul_assoc _ _ _).symm

include hx hy in
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem linearIndependent_adjoinField :
    LinearIndependent (IntermediateField.adjoin L ({(x : F)} : Set F))
      (fun i : Fin n => (y i : F)) :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({(x : F)} : Set F))
    (IntermediateField.adjoin L ({(x : F)} : Set F))).mp (linearIndependent_adjoin R x hx y hy)

include hx hy in

theorem exists_repr_adjoinField
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n) (f : F) :
    ∃ r : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F),
      f = ∑ i, (r i : F) * (y i : F) := by
  set E := IntermediateField.adjoin L ({(x : F)} : Set F)
  let B : Module.Basis (Fin n) E F :=
    basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_adjoinField R x hx y hy)
      (by rw [Fintype.card_fin, hcard])
  refine ⟨fun i => B.repr f i, ?_⟩
  conv_lhs => rw [← B.sum_repr f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]

end frame


end
end Dubon2026.SourceCurve.RegularProlongation
