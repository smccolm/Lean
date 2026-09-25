import TaoTrudgianYang2025.RobertSargosAffineBand

/-! The actual six-coordinate primitive system from Robert--Sargos (2002).
Closed support gives an overcount of the paper's half-open boxes. -/

noncomputable section
namespace TaoTrudgianYang2025

structure RobertSargosPoint where
  r : ℤ
  q₁ : ℤ
  q₂ : ℤ
  h₁ : ℤ
  h₂ : ℤ
  d : ℤ
  deriving DecidableEq

structure RobertSargosPrimitiveSystem (R H Q δ : ℝ) (p : RobertSargosPoint) : Prop where
  r_ne_zero : p.r ≠ 0
  r_bound : |(p.r:ℝ)| ≤ R
  q₁_support : |(p.q₁:ℝ)| ∈ Set.Icc Q (2*Q)
  q₂_support : |(p.q₂:ℝ)| ∈ Set.Icc Q (2*Q)
  h₁_support : (p.h₁:ℝ) ∈ Set.Icc H (2*H)
  h₂_support : (p.h₂:ℝ) ∈ Set.Icc H (2*H)
  same_sign : 0 < p.q₁*p.q₂
  d_ne_zero : p.d ≠ 0
  coordinate_primitive : Int.gcd (Int.gcd p.d p.q₁ : ℤ) p.q₂ = 1
  coefficient_primitive : Int.gcd (Int.gcd p.r p.h₁ : ℤ) p.h₂ = 1
  linear : p.r*p.d+p.h₁*p.q₁-p.h₂*p.q₂ = 0
  near : |robertSargosReduced p.r p.q₁ p.q₂ p.h₁ p.h₂ p.d| ≤ δ*H*Q^2

theorem RobertSargosPrimitiveSystem.linear_real {R H Q δ : ℝ} {p : RobertSargosPoint}
    (h : RobertSargosPrimitiveSystem R H Q δ p) :
    (p.r:ℝ)*p.d+(p.h₁:ℝ)*p.q₁-(p.h₂:ℝ)*p.q₂ = 0 := by
  exact_mod_cast h.linear

theorem RobertSargosPrimitiveSystem.displacement_le {R H Q δ : ℝ} {p : RobertSargosPoint}
    (h : RobertSargosPrimitiveSystem R H Q δ p) (hH : 0 < H) (hQ : 0 < Q) :
    |(p.d:ℝ)| ≤ (δ+8)*Q :=
  robertSargos_displacement_same_sign hH hQ h.h₁_support h.h₂_support
    h.q₁_support h.q₂_support (by exact_mod_cast h.same_sign) h.linear_real h.near

theorem RobertSargosPrimitiveSystem.affine_band {R H Q δ : ℝ} {p : RobertSargosPoint}
    (h : RobertSargosPrimitiveSystem R H Q δ p) (hH : 0 < H) (hQ : 0 < Q)
    (hδ : δ ≤ 1) :
    |2*(p.d:ℝ)+(p.q₁:ℝ)-(p.q₂:ℝ)| ≤ δ*Q+99*R*Q/H :=
  robertSargos_affine_band hH hQ hδ h.r_bound h.h₁_support h.h₂_support
    h.q₁_support h.q₂_support (by exact_mod_cast h.same_sign) h.linear_real h.near

end TaoTrudgianYang2025

