import GafniTao.FordEquation34AMGM
import GafniTao.FordS6Setup
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
# Ford equation (3.4): source Weyl sums and torus integral

The objects below are the literal finite Fourier sums in Ford's proof.  The
polynomial sum is restricted by the nonsingular head condition, while
`fordResidueWeylSum` is the source `g(alpha;c)`.  Normalized Haar measure on
the `k`-torus replaces the paper's integral over the half-open unit cube.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

abbrev FordS3PolynomialBox
    (k d P p : ℕ) (hdk : d ≤ k) :=
  {z : FordBox k P //
    Function.Injective (fun i : Fin (k - d) =>
      (fordBoxValue z (fordHeadIndex hdk i) : ZMod p))}

instance fordS3PolynomialBoxFinite
    (k d P p : ℕ) (hdk : d ≤ k) :
    Finite (FordS3PolynomialBox k d P p hdk) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance fordS3PolynomialBoxFintype
    (k d P p : ℕ) (hdk : d ≤ k) :
    Fintype (FordS3PolynomialBox k d P p hdk) := Fintype.ofFinite _

def fordPolynomialMoment
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (z : FordBox k P) : Fin k → ℤ :=
  fun j => fordPolynomialSumInt Ψ z j

def fordPolynomialWeylSum
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ z : FordS3PolynomialBox k d P p hdk,
    UnitAddTorus.mFourier (fordPolynomialMoment Ψ z.1) α

abbrev FordResidueInterval (Q p : ℕ) (c : ZMod p) :=
  {x : Fin Q // (((x : ℕ) + 1 : ℕ) : ZMod p) = c}

instance fordResidueIntervalFinite (Q p : ℕ) (c : ZMod p) :
    Finite (FordResidueInterval Q p c) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance fordResidueIntervalFintype
    (Q p : ℕ) (c : ZMod p) :
    Fintype (FordResidueInterval Q p c) := Fintype.ofFinite _

/-- Ford's `g(alpha;c)`, with `1 <= x <= Q` and `x == c (mod p)`. -/
def fordResidueWeylSum
    (k Q q p : ℕ) (c : ZMod p) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ x : FordResidueInterval Q p c,
    UnitAddTorus.mFourier
      (fun j : Fin k => ((q ^ ((j : ℕ) + 1) *
        ((x.1 : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)) α

abbrev fordTorusMeasure (k : ℕ) : Measure (UnitAddTorus (Fin k)) :=
  Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)

def fordS3ResidueMajorant
    {k d T P p : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (s Q q : ℕ) (hds : d ≤ s) : ℝ :=
  ∫ α : UnitAddTorus (Fin k),
    ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
      ∑ v : Fin d → ZMod p,
        ‖fordResidueFiberProduct hds
          (fun c => fordResidueWeylSum k Q q p c α) v‖ ^ 2
    ∂fordTorusMeasure k

def fordS4Fourier
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (s Q q : ℕ) (c : ZMod p) : ℝ :=
  ∫ α : UnitAddTorus (Fin k),
    ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
      ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s)
    ∂fordTorusMeasure k

theorem continuous_fordPolynomialWeylSum
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) :
    Continuous (fordPolynomialWeylSum (P := P) (p := p) Ψ hdk) := by
  unfold fordPolynomialWeylSum
  fun_prop

theorem continuous_fordResidueWeylSum
    (k Q q p : ℕ) (c : ZMod p) :
    Continuous (fordResidueWeylSum k Q q p c) := by
  unfold fordResidueWeylSum
  fun_prop

theorem continuous_fordResidueFiberProduct
    {k d s Q q p : ℕ} [NeZero p] (hds : d ≤ s)
    (v : Fin d → ZMod p) :
    Continuous (fun α : UnitAddTorus (Fin k) =>
      fordResidueFiberProduct hds
        (fun c => fordResidueWeylSum k Q q p c α) v) := by
  unfold fordResidueFiberProduct
  apply continuous_finsetSum
  intro c hc
  apply continuous_finsetProd
  intro i hi
  exact continuous_fordResidueWeylSum k Q q p _

theorem integrable_fordS4_integrand
    {k d T P p : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (s Q q : ℕ) (c : ZMod p) :
    Integrable (fun α : UnitAddTorus (Fin k) =>
      ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
        ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s))
      (fordTorusMeasure k) := by
  rw [← integrableOn_univ]
  apply ContinuousOn.integrableOn_compact isCompact_univ
  exact ((continuous_fordPolynomialWeylSum Ψ hdk).norm.pow 2).mul
    ((continuous_fordResidueWeylSum k Q q p c).norm.pow (2 * s)) |>.continuousOn

/-- Ford equation (3.4) before replacing the residue sum by its maximum. -/
theorem ford_equation_3_4_sum
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (hs : 0 < s) (hds : d ≤ s)
    (hp : Nat.Prime p) (hdp : d < p) :
    fordS3ResidueMajorant (P := P) (p := p) Ψ hdk s Q q hds ≤
      ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
        (p : ℝ) ^ (s - 1) *
          ∑ c : ZMod p, fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c := by
  let D : ℝ := ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ)
  have hpoint (α : UnitAddTorus (Fin k)) :
      ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
          ∑ v : Fin d → ZMod p,
            ‖fordResidueFiberProduct hds
              (fun c => fordResidueWeylSum k Q q p c α) v‖ ^ 2 ≤
        D * (p : ℝ) ^ (s - 1) *
          ∑ c : ZMod p,
            (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
              ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s)) := by
    have h := ford_equation_3_4_pointwise hs hds hp hdp
      (fun c => fordResidueWeylSum k Q q p c α)
    have hnonneg : 0 ≤
        ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 :=
      sq_nonneg _
    calc
      _ ≤ ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
          (D * (p : ℝ) ^ (s - 1) *
            ∑ c : ZMod p,
              ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s)) :=
        mul_le_mul_of_nonneg_left h hnonneg
      _ = _ := by
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        ring
  have hleft : Integrable (fun α : UnitAddTorus (Fin k) =>
      ‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
        ∑ v : Fin d → ZMod p,
          ‖fordResidueFiberProduct hds
            (fun c => fordResidueWeylSum k Q q p c α) v‖ ^ 2)
      (fordTorusMeasure k) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply ((continuous_fordPolynomialWeylSum Ψ hdk).norm.pow 2).mul
    apply continuous_finsetSum
    intro v hv
    exact (continuous_fordResidueFiberProduct (k := k) hds v).norm.pow 2
  have hright : Integrable (fun α : UnitAddTorus (Fin k) =>
      D * (p : ℝ) ^ (s - 1) *
        ∑ c : ZMod p,
          (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
            ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s)))
      (fordTorusMeasure k) := by
    have hsum := integrable_finsetSum Finset.univ fun c hc =>
      integrable_fordS4_integrand (P := P) (p := p) Ψ hdk s Q q c
    simpa [mul_assoc] using
      (hsum.const_mul ((p : ℝ) ^ (s - 1))).const_mul D
  unfold fordS3ResidueMajorant
  change (∫ α : UnitAddTorus (Fin k), _ ∂fordTorusMeasure k) ≤ _
  calc
    _ ≤ ∫ α : UnitAddTorus (Fin k),
        D * (p : ℝ) ^ (s - 1) *
          ∑ c : ZMod p,
            (‖fordPolynomialWeylSum (P := P) (p := p) Ψ hdk α‖ ^ 2 *
              ‖fordResidueWeylSum k Q q p c α‖ ^ (2 * s))
        ∂fordTorusMeasure k := integral_mono hleft hright hpoint
    _ = D * (p : ℝ) ^ (s - 1) *
        ∑ c : ZMod p, fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c := by
      rw [integral_const_mul]
      rw [MeasureTheory.integral_finsetSum Finset.univ
        (fun c hc => integrable_fordS4_integrand (P := P) (p := p)
          Ψ hdk s Q q c)]
      rfl

#print axioms ford_equation_3_4_sum

/-- The finite residue-class maximum in Ford's equation (3.4), before
combining its three powers of `p`. -/
theorem ford_equation_3_4_max_pre
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (hs : 0 < s) (hds : d ≤ s)
    (hp : Nat.Prime p) (hdp : d < p) :
    ∃ c : ZMod p,
      fordS3ResidueMajorant (P := P) (p := p) Ψ hdk s Q q hds ≤
        ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
          (p : ℝ) ^ (s - 1) *
            ((p : ℝ) * fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c) := by
  let F : ZMod p → ℝ := fun c =>
    fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c
  obtain ⟨c, hc, hcmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ZMod p)) F Finset.univ_nonempty
  refine ⟨c, (ford_equation_3_4_sum Ψ hdk hs hds hp hdp).trans ?_⟩
  have hsum : ∑ a : ZMod p, F a ≤ (Fintype.card (ZMod p)) • F c :=
    Finset.sum_le_card_nsmul Finset.univ F (F c)
      (fun a ha => hcmax a (Finset.mem_univ a))
  have hsum' : ∑ a : ZMod p, F a ≤ (p : ℝ) * F c := by
    simpa [ZMod.card, nsmul_eq_mul] using hsum
  have hcoef : 0 ≤
      ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) * (p : ℝ) ^ (s - 1) := by
    positivity
  exact mul_le_mul_of_nonneg_left hsum' hcoef

theorem ford_equation_3_4_power_identity
    {d p s : ℕ} (hs : 0 < s) (hds : d ≤ s) :
    ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
          (p : ℝ) ^ (s - 1) * (p : ℝ) =
      (Nat.factorial d : ℝ) * (p : ℝ) ^ (2 * s - d) := by
  norm_num [Nat.cast_mul, Nat.cast_pow]
  calc
    (Nat.factorial d : ℝ) * (p : ℝ) ^ (s - d) *
        (p : ℝ) ^ (s - 1) * (p : ℝ) =
      (Nat.factorial d : ℝ) *
        (p : ℝ) ^ ((s - d) + (s - 1) + 1) := by
          rw [pow_add, pow_add, pow_one]
          ring
    _ = (Nat.factorial d : ℝ) * (p : ℝ) ^ (2 * s - d) := by
      congr 2
      omega

/-- Ford's equation (3.4), with the exact exponent `2s-d`. -/
theorem ford_equation_3_4
    {k d T P p s Q q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hdk : d ≤ k) (hs : 0 < s) (hds : d ≤ s)
    (hp : Nat.Prime p) (hdp : d < p) :
    ∃ c : ZMod p,
      fordS3ResidueMajorant (P := P) (p := p) Ψ hdk s Q q hds ≤
        (Nat.factorial d : ℝ) * (p : ℝ) ^ (2 * s - d) *
          fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c := by
  obtain ⟨c, hc⟩ := ford_equation_3_4_max_pre Ψ hdk hs hds hp hdp
  refine ⟨c, hc.trans_eq ?_⟩
  calc
    ((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
          (p : ℝ) ^ (s - 1) *
            ((p : ℝ) * fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c) =
      (((Nat.factorial d * p ^ (s - d) : ℕ) : ℝ) *
          (p : ℝ) ^ (s - 1) * (p : ℝ)) *
            fordS4Fourier (P := P) (p := p) Ψ hdk s Q q c := by ring
    _ = _ := by rw [ford_equation_3_4_power_identity hs hds]

#print axioms ford_equation_3_4

end

end GafniTao
