import Dubon2026.SourceModularGenusPoleLifting
import Dubon2026.SourceIntegralChartPoleBound

/-! DUB-17/18 -> modular good reduction -> integral-chart comparison.
Equality of the actual modular genera gives surjectivity of coefficient
reduction on both the j and inverse-j integral closures. The inverse chart
uses the same j-pole lifting theorem after multiplication by a power of j;
no second reduction or genus argument is needed. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]
variable (A : ValuationSubring L) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N L
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_integral_j_lift_of_genus_eq
    (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0)
    (hgen : genusFF kk Fb = genusFF L FF)
    (g : Fb) (hg : IsIntegral (Algebra.adjoin kk {jCoeff N kk}) g) :
    ∃ f : gaussRing A N, IsIntegral (Algebra.adjoin L {jCoeff N L}) (f : FF) ∧
      modularResidueHom A N hNL hNk f = g := by
  haveI := finiteDimensional_coeff_field N L
  obtain ⟨m₀, hm₀⟩ := exists_pole_bound_of_integral_adjoin _ _ hg
    (modularJPole N kk) (modularJPole_apply N kk)
  obtain ⟨m₁, hm₁⟩ := exists_modular_pole_space_lifts_of_genus_eq A N hNL hNk hgen
  obtain ⟨f, hf, hfg⟩ := hm₁ (max m₀ m₁) (le_max_right _ _) g
    (hm₀ _ (le_max_left _ _))
  exact ⟨f, (RegularProlongation.integral_charts_of_pole_bound
    (jCoeff N L) (transcendental_jCoeff N L) (modularJPole N L)
    (modularJPole_apply N L) _ hf).1, hfg⟩

theorem exists_modular_integral_inverse_j_lift_of_genus_eq
    (hNL : (N : L) ≠ 0) (hNk : (N : kk) ≠ 0)
    (hgen : genusFF kk Fb = genusFF L FF)
    (g : Fb) (hg : IsIntegral (Algebra.adjoin kk {(jCoeff N kk)⁻¹}) g) :
    ∃ f : gaussRing A N, IsIntegral (Algebra.adjoin L {(jCoeff N L)⁻¹}) (f : FF) ∧
      modularResidueHom A N hNL hNk f = g := by
  haveI := finiteDimensional_coeff_field N L
  let Di : Divisor kk Fb := poleDivisor (jCoeff N kk)⁻¹
    (finite_coeff_divisor_support N kk (jCoeff N kk)⁻¹)
  have hDi (v : Place kk Fb) : Di v = max 0 (v.ord (jCoeff N kk)) := by
    change max (-v.ord (jCoeff N kk)⁻¹) 0 = _
    rw [v.ord_inv, neg_neg, max_comm]
  obtain ⟨m₀, hm₀⟩ := exists_pole_bound_of_integral_adjoin _ _ hg Di (fun v => by
    rw [hDi, v.ord_inv, neg_neg])
  obtain ⟨m₁, hm₁⟩ := exists_modular_pole_space_lifts_of_genus_eq A N hNL hNk hgen
  let m := max m₀ m₁
  have hjb : jCoeff N kk ≠ 0 := fun h => transcendental_jCoeff N kk (h ▸ isAlgebraic_zero)
  have hgp := mul_pow_mem_pole_space_of_inverse_bound (jCoeff N kk) hjb
    (modularJPole N kk) Di (modularJPole_apply N kk) hDi m
    (hm₀ m (le_max_left _ _))
  obtain ⟨f, hf, hfg⟩ := hm₁ m (le_max_right _ _) (g * jCoeff N kk ^ m) hgp
  let R := modularRegularProlongation A N hNL hNk
  let J : gaussRing A N := ⟨jCoeff N L, jCoeff_mem_gaussRing A N⟩
  have hJ : modularResidueHom A N hNL hNk J = jCoeff N kk :=
    modularResidueHom_jCoeff A N hNL hNk
  have hJU : IsUnit J := R.isUnit_of_residue_ne_zero (f := J) (hJ.trans_ne hjb)
  obtain ⟨u, hu⟩ := hJU
  have huF : ((↑u⁻¹ : gaussRing A N) : FF) = (jCoeff N L)⁻¹ := by
    rw [show ((↑u⁻¹ : gaussRing A N) : FF) =
      (gaussRing A N).subtype ↑u⁻¹ from rfl, map_units_inv, hu]
    rfl
  refine ⟨f * (↑u⁻¹ : gaussRing A N) ^ m, ?_, ?_⟩
  · have hi := (RegularProlongation.integral_charts_of_pole_bound
      (jCoeff N L) (transcendental_jCoeff N L) (modularJPole N L)
      (modularJPole_apply N L) m hf).2
    change IsIntegral (Algebra.adjoin L {(jCoeff N L)⁻¹})
      ((f : FF) * ((↑u⁻¹ : gaussRing A N) : FF) ^ m)
    rw [huF, inv_pow]
    exact hi
  · rw [map_mul, map_pow, map_units_inv, hu, hJ, hfg, inv_pow,
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero m hjb), mul_one]

end
end Dubon2026.SourceFunctionField.GaussReduction
