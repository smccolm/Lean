import Dubon2026.SourceIntegralCosetParabolic
import Dubon2026.SourceIntegralCosetWord
import Dubon2026.SourceIntegralPeriodCuspLimits

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> principal-divisor converse ->
integral Petersson duality. Every actual period generator is represented by
an integer parabolic character in the exact ray/arc side pairing. The native
cocycle, proved parabolic classification and word expansion are consumed with
the actual normalized cusp primitive and its already proved integrals.
Adapted from the pinned Apache-2.0 primary recorded in route 957. -/
namespace Dubon2026.SourceIntegralPeriodDual
noncomputable section
open UpperHalfPlane MeasureTheory Filter
open SourceParabolicEdgePeriod SourceModularGreenPairing SourceModularSidePairing SourcePeriodUntwist
open scoped MatrixGroups Topology
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
local notation "Q" => SL(2, ℤ) ⧸ Γ
local notation "q₀" => ((1 : SL(2, ℤ)) : Q)

theorem exists_parabolic_character_eq_period [Fintype Q]
    (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) (δ : Γ) :
    ∃ φ : Additive Γ →+ ℤ,
      (∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
        φ (Additive.ofMul γ) = 0) ∧
      ∀ g : CuspForm (Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)) 2,
        Complex.I * (∑ q : Q, (φ (Additive.ofMul (transition Γ ModularGroup.T q)) : ℂ) *
          (∫ y in Set.Ioi (Real.sqrt 3 / 2), tilePull g (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I))) +
        1 / 2 * (∑ q : Q, (φ (Additive.ofMul (transition Γ ModularGroup.S q)) : ℂ) *
          (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            tilePull g (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
              (Complex.I * Complex.exp (θ * Complex.I)))) = sourceWeightTwoPeriodValue Γ g δ := by
  classical
  obtain ⟨a, n, hflux, hword⟩ := wordProp (Γ := Γ) hΓ (δ : SL(2, ℤ))
  have hδq₀ : (δ : SL(2, ℤ))⁻¹ • (q₀ : SL(2, ℤ) ⧸ Γ) = q₀ :=
    smul_identity_coset_of_mem (inv_mem δ.2)
  obtain ⟨c, hc⟩ : ∃ c : SL(2, ℤ) ⧸ Γ → ℤ, ∀ q, c q = -a q :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : SL(2, ℤ) ⧸ Γ → ℤ, ∀ q, m q = -n q :=
    ⟨_, fun _ => rfl⟩
  have hfl : ∀ q, c (ModularGroup.S • q) - c q = m (ModularGroup.T • q) - m q := fun q => by
    have h := hflux q
    rw [hδq₀, sub_self] at h
    rw [hc, hc, hm, hm]
    linear_combination -h

  obtain ⟨Z, hZS, hZU⟩ := exists_adapted_cocycle hΓ c
  refine ⟨hom Z, hom_parabolic hΓ hZS hZU hfl, fun g => ?_⟩

  choose L hL using Ek_exists_cusp_limit g
  let G : Q → ℂ → ℂ := fun q => tilePull g (Quotient.out q)⁻¹
  have hGf : ∀ q, G q = tilePull g (Quotient.out q)⁻¹ := fun _ => rfl

  obtain ⟨ray, hray⟩ : ∃ ray : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      ray q = ∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I) := ⟨_, fun _ => rfl⟩
  obtain ⟨arc, harc⟩ : ∃ arc : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      arc q = ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      x q = Ek g (((Quotient.out q)⁻¹ • ρ : ℍ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      y q = Ek g (((Quotient.out q)⁻¹ • (ModularGroup.T • ρ) : ℍ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨Lq, hLq⟩ : ∃ Lq : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      Lq q = L (Quotient.out q)⁻¹ := ⟨_, fun _ => rfl⟩
  obtain ⟨LS, hLS⟩ : ∃ LS : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      LS q = L ((Quotient.out q)⁻¹ * ModularGroup.S) := ⟨_, fun _ => rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      cc q = ((c q : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨mm, hmm⟩ : ∃ mm : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      mm q = ((em Z q : ℤ) : ℂ) := ⟨_, fun _ => rfl⟩
  obtain ⟨PTi, hPTi⟩ : ∃ PTi : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      PTi q = sourceWeightTwoPeriodValue Γ g (transition Γ ModularGroup.T⁻¹ q) := ⟨_, fun _ => rfl⟩
  obtain ⟨PS, hPS⟩ : ∃ PS : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      PS q = sourceWeightTwoPeriodValue Γ g (transition Γ ModularGroup.S q) := ⟨_, fun _ => rfl⟩
  obtain ⟨PU, hPU⟩ : ∃ PU : SL(2, ℤ) ⧸ Γ → ℂ, ∀ q,
      PU q = sourceWeightTwoPeriodValue Γ g (transition Γ (ModularGroup.S * ModularGroup.T)⁻¹ q) :=
    ⟨_, fun _ => rfl⟩

  have haT : ∀ q, ((hom Z (Additive.ofMul (transition Γ ModularGroup.T q)) : ℤ) : ℂ) =
      cc q - cc ((ModularGroup.S * ModularGroup.T) • q) + mm (ModularGroup.T • q) - mm q := by
    intro q
    rw [hom_transition_T hZS hZU, hcc, hcc, hmm, hmm]
    push_cast
    ring
  have haS : ∀ q, ((hom Z (Additive.ofMul (transition Γ ModularGroup.S q)) : ℤ) : ℂ) =
      mm (ModularGroup.S • q) - mm q := by
    intro q
    rw [hom_transition_S hZS, hmm, hmm]
    push_cast
    ring
  simp only [← hGf, ← hray, ← harc, haT, haS]

  have hrayv : ∀ q, Complex.I * ray q = Lq q - x q := fun q => by
    rw [hray, hGf q, hLq, hx]
    exact I_mul_integral_ray_corner g _ (hL _)
  have harcv : ∀ q, arc q = x q - y q := fun q => by
    rw [harc, hGf q, hx, hy]
    exact integral_arc_corner g _

  have hR1 : ∀ q, Lq (ModularGroup.T⁻¹ • q) = Lq q + PTi q := fun q => by
    rw [hLq, hLq, hPTi, lim_out_smul g hL, inv_inv, lim_mul_T g hL]
  have hx1 : ∀ q, x (ModularGroup.T⁻¹ • q) = y q + PTi q := fun q => by
    rw [hx, hy, hPTi, Ek_out_inv_smul g, inv_inv]
  have hx2 : ∀ q, x (ModularGroup.S • q) = y q + PS q := fun q => by
    rw [hx, hy, hPS, Ek_out_inv_smul g ModularGroup.S q ρ,
      inv_smul_eq_iff.mpr S_smul_T_rho.symm]
  have hy2 : ∀ q, y (ModularGroup.S • q) = x q + PS q := fun q => by
    rw [hy, hx, hPS, Ek_out_inv_smul g ModularGroup.S q (ModularGroup.T • ρ),
      inv_smul_eq_iff.mpr S_smul_rho.symm]
  have hR3 : ∀ q, Lq ((ModularGroup.S * ModularGroup.T)⁻¹ • q) = LS q + PU q := fun q => by
    rw [hLq, hLS, hPU, lim_out_smul g hL, inv_inv, ← mul_assoc, lim_mul_T g hL]
  have hx3 : ∀ q, x ((ModularGroup.S * ModularGroup.T)⁻¹ • q) = x q + PU q := fun q => by
    rw [hx, hx, hPU, Ek_out_inv_smul g, inv_inv, mul_smul, S_smul_T_rho]

  have E1 : Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
        (cc q - cc ((ModularGroup.S * ModularGroup.T) • q) + mm (ModularGroup.T • q) - mm q) * ray q =
      ∑ q : SL(2, ℤ) ⧸ Γ, cc q * (Lq q - x q) -
        ∑ q : SL(2, ℤ) ⧸ Γ,
          cc ((ModularGroup.S * ModularGroup.T) • q) * (Lq q - x q) +
        ∑ q : SL(2, ℤ) ⧸ Γ, mm (ModularGroup.T • q) * (Lq q - x q) -
        ∑ q : SL(2, ℤ) ⧸ Γ, mm q * (Lq q - x q) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [mul_left_comm, hrayv]
    ring
  have E2a : ∑ q : SL(2, ℤ) ⧸ Γ,
        cc ((ModularGroup.S * ModularGroup.T) • q) * (Lq q - x q) =
      ∑ q : SL(2, ℤ) ⧸ Γ, cc q * (LS q - x q) := by
    rw [← Equiv.sum_comp (MulAction.toPerm (ModularGroup.S * ModularGroup.T)⁻¹)
      (fun q => cc ((ModularGroup.S * ModularGroup.T) • q) * (Lq q - x q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [smul_inv_smul, hR3, hx3]
    ring
  have E2b : ∑ q : SL(2, ℤ) ⧸ Γ, mm (ModularGroup.T • q) * (Lq q - x q) =
      ∑ q : SL(2, ℤ) ⧸ Γ, mm q * (Lq q - y q) := by
    rw [← Equiv.sum_comp (MulAction.toPerm ModularGroup.T⁻¹)
      (fun q => mm (ModularGroup.T • q) * (Lq q - x q))]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [smul_inv_smul, hR1, hx1]
    ring
  have E3 : ∑ q : SL(2, ℤ) ⧸ Γ, (mm (ModularGroup.S • q) - mm q) * arc q =
      ∑ q : SL(2, ℤ) ⧸ Γ, mm (ModularGroup.S • q) * (x q - y q) -
        ∑ q : SL(2, ℤ) ⧸ Γ, mm q * (x q - y q) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [harcv]
    ring
  have E3a : ∑ q : SL(2, ℤ) ⧸ Γ, mm (ModularGroup.S • q) * (x q - y q) =
      -∑ q : SL(2, ℤ) ⧸ Γ, mm q * (x q - y q) := by
    rw [← Equiv.sum_comp (MulAction.toPerm ModularGroup.S)
      (fun q => mm (ModularGroup.S • q) * (x q - y q)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply]
    rw [S_smul_S_smul hΓ, hx2, hy2]
    ring
  have E5 : ∑ q : SL(2, ℤ) ⧸ Γ, cc q * (Lq q - x q) -
        ∑ q : SL(2, ℤ) ⧸ Γ, cc q * (LS q - x q) =
      ∑ q : SL(2, ℤ) ⧸ Γ, (a q : ℂ) * (LS q - Lq q) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hcc, hc]
    push_cast
    ring
  have E6 : ∑ q : SL(2, ℤ) ⧸ Γ, mm q * (Lq q - y q) -
        ∑ q : SL(2, ℤ) ⧸ Γ, mm q * (Lq q - x q) =
      ∑ q : SL(2, ℤ) ⧸ Γ, mm q * (x q - y q) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring

  have hEq : ∀ γ, γ ∈ Γ → ∀ X : SL(2, ℤ),
      L (γ * X * ModularGroup.S) - L (γ * X) = L (X * ModularGroup.S) - L X := by
    intro γ hγ X
    rw [mul_assoc, lim_coe_mul g hL ⟨γ, hγ⟩ (X * ModularGroup.S), lim_coe_mul g hL ⟨γ, hγ⟩ X]
    ring
  have Wd : L δ - L 1 =
      ∑ q : SL(2, ℤ) ⧸ Γ, (a q : ℂ) * (LS q - Lq q) := by
    rw [hword L (lim_mul_T g hL) (lim_neg g hL) hEq]
    exact Finset.sum_congr rfl fun q _ => by rw [hLS, hLq]
  have E7 : sourceWeightTwoPeriodValue Γ g δ = L δ - L 1 := by
    have h := lim_coe_mul g hL δ 1
    rw [mul_one] at h
    linear_combination -h
  linear_combination E1 + (1 / 2 : ℂ) * E3 - E2a + E2b + (1 / 2 : ℂ) * E3a + E5 + E6 - Wd - E7

end
end Dubon2026.SourceIntegralPeriodDual
