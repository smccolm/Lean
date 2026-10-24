import Dubon2026.SourceReductionIntegralMultiples
import Dubon2026.SourceReductionIntegralFiberEquality

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward.
The exact fiber-order identity now holds for every Gauss-integral function
with nonzero reduction, without chart integrality. The proved normalized
denominator and its integral product reduce the identity to the two integral
cases; native finite-support subtraction retains all multiplicities and signs.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [HasPrincipalDivisors (ResidueField A) Fbar]

theorem sum_fiber_orders_eq_residue_order (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    [Algebra.IsSeparable
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar]
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hchart : ∀ h : Fbar, IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue x}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (f : F) ∧ R.residue f = h)
    (f : R.integers) (hf : R.residue f ≠ 0)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧ ChartDomain A P (x : F) ∧ ChartReducesTo A R (x : F) P Q)) :
    ∑ P ∈ T, D P = Q.ord (R.residue f) := by
  classical

  obtain ⟨q₀, hres_q₀_ne, hq₀_int, hg_int⟩ :=
    exists_regular_chart_integral_multiple R x hx (hdeg ▸ hfin) f
  let g : R.integers := q₀ * f
  have hres_g_ne : R.residue g ≠ 0 := by
    simp only [g, map_mul]
    exact mul_ne_zero hres_q₀_ne hf
  have hq₀0 : (q₀ : F) ≠ 0 := fun h =>
    hres_q₀_ne (by rw [show q₀ = 0 from Subtype.ext h, map_zero])
  have hg0 : (g : F) ≠ 0 := fun h =>
    hres_g_ne (by rw [show g = 0 from Subtype.ext h, map_zero])

  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (g : F) hg0
  obtain ⟨Dq, hDq, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (q₀ : F) hq₀0
  have hDeq : D = Dg - Dq := by
    ext P
    rw [Finsupp.sub_apply, hD, hDg, hDq]
    have : (f : F) = (g : F) * (q₀ : F)⁻¹ := by
      simp only [g]
      push_cast
      field_simp
    rw [this, P.ord_mul hg0 (inv_ne_zero hq₀0), P.ord_inv]
    ring
  have hres_eq : Q.ord (R.residue f) = Q.ord (R.residue g) - Q.ord (R.residue q₀) := by
    have : R.residue f = R.residue g * (R.residue q₀)⁻¹ := by
      simp only [g, map_mul]
      field_simp
    rw [this, Q.ord_mul hres_g_ne (inv_ne_zero hres_q₀_ne), Q.ord_inv]
    ring
  let c' : Place L F → Prop := fun P => ChartDomain A P (x : F) ∧ ChartReducesTo A R (x : F) P Q
  let Φ : Divisor L F → ℤ := fun E => ∑ P ∈ E.support.filter c', E P
  have hΦ : ∀ E : Divisor L F, Φ E = E.sum fun P n => if c' P then n else 0 := fun E => by
    simp only [Φ, Finsupp.sum, Finset.sum_filter]
  have hΦsub : Φ (Dg - Dq) = Φ Dg - Φ Dq := by
    rw [hΦ, hΦ, hΦ, Finsupp.sum_sub_index]
    intro P b₁ b₂
    split_ifs <;> simp
  have hmemT : ∀ (E : Divisor L F) (P : Place L F), P ∈ E.support.filter c' ↔
      (E P ≠ 0 ∧ ChartDomain A P (x : F) ∧ ChartReducesTo A R (x : F) P Q) := fun E P => by
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, c']
  have hTeq : ∑ P ∈ T, D P = Φ D := by
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext P
    rw [hT, hmemT]
  rw [hTeq, hDeq, hΦsub, hres_eq]
  exact congrArg₂ (· - ·)
    (sum_fiber_orders_eq_residue_order_of_integral_chart R x hx hfin hdeg hchart g hg_int hres_g_ne Q hQ Dg hDg _ (hmemT Dg))
    (sum_fiber_orders_eq_residue_order_of_integral_chart R x hx hfin hdeg hchart q₀ hq₀_int hres_q₀_ne Q hQ Dq hDq _ (hmemT Dq))

end
end Dubon2026.SourceCurve.RegularProlongation
