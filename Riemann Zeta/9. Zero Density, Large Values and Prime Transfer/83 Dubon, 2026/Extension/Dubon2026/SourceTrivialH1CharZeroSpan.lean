import Dubon2026.SourceTrivialH1IntegralAlternative

/-! DUB-17/18 -> residual Galois association -> characteristic-zero
weight-two Hecke lift. The complex H1 space is already spanned by integral
classes, so the external auxiliary complex-span representation is unnecessary.
This uses the proved integral-span consumer and characteristic-zero torsion
vanishing, preserving the actual full native H1.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

/-- In characteristic zero the entire original native trivial-coefficient
H1 lies in the span of the actual integral classes. -/
theorem sourceTrivialH1_mem_integralSpan_charZero
    (M : ℕ) [NeZero M] (F : Type) [Field F] [CharZero F]
    (x : H1 (Rep.trivial F (Gamma0 M) F)) :
    x ∈ Submodule.span F (Set.range fun y : Additive (Gamma0 M) →+ ℤ =>
      (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 M) F)).inv ((Int.castAddHom F).comp y)) := by
  apply sourceTrivialH1_mem_integralSpan
  intro g hg
  let φ := (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 M) F)).hom x
  obtain ⟨n, hn, hgn⟩ := hg.exists_pow_eq_one
  have h := map_nsmul φ n (Additive.ofMul g)
  change φ (Additive.ofMul (g ^ n)) = n • φ (Additive.ofMul g) at h
  rw [hgn, ofMul_one, map_zero, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast hn.ne')

end
end Dubon2026
