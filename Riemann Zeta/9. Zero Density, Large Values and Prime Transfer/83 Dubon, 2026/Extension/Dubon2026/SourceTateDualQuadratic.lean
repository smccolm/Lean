import Dubon2026.SourceTateEndomorphisms

/-! DUB-17/18 -> original Gamma1 Frobenius realization -> normalization
on the original coefficient-valued Tate dual. This linear calculation is
consumed with the native Picard operators and homogeneous coefficient maps.
-/
namespace Dubon2026
noncomputable section
variable {R S T V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup T] [Module R T] [AddCommGroup V]
  [Module R V] [Module S V] [IsScalarTower R S V]

theorem sourceTateDual_quadratic (b c : Module.End S V) (H F D : Module.End R T)
    (ell w : ℕ) (hquad : H * F = F * F + ell • D)
    (hcoeff : b.comp b = (ell : S) ^ w • c) (φ : T →ₗ[R] V) :
    (b.restrictScalars R).comp (((b.restrictScalars R).comp (φ.comp H)).comp F) =
      (b.restrictScalars R).comp (((b.restrictScalars R).comp (φ.comp F)).comp F) +
        (ell : S) ^ (w + 1) • (c.restrictScalars R).comp (φ.comp D) := by
  apply LinearMap.ext
  intro x
  change b (b (φ (H (F x)))) = b (b (φ (F (F x)))) +
    (ell : S) ^ (w + 1) • c (φ (D x))
  have hx : H (F x) = F (F x) + ell • D x := LinearMap.congr_fun hquad x
  rw [hx, map_add, map_add, map_add, map_nsmul, map_nsmul, map_nsmul]
  congr 1
  have hc : b (b (φ (D x))) = (ell : S) ^ w • c (φ (D x)) := LinearMap.congr_fun hcoeff _
  rw [hc, ← Nat.cast_smul_eq_nsmul S, smul_smul, pow_succ']

end
end Dubon2026
