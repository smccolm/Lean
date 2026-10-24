import Dubon2026.SourceEllipticPrimeAbscissaHomX
import Dubon2026.SourceEllipticAbscissaSubgroupEquality

/-! The image under the specific prime quotient commutes with field
embeddings. Equality of the actual image subgroups follows from the proved
zero fibers and intrinsic abscissa formulas. This discharges image
compatibility for composite iteration on the DUB-17/18 inertia-census chain,
without requiring the stronger pointwise ordinate comparison. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticFunctionField OddDiscriminant
open SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
variable [IsAlgClosed F] [IsAlgClosed K]

/-- The actual finite subgroup image under the specific prime quotient commutes with field maps. -/
theorem primeAbscissaHom_image_map (f : F →+* K)
    (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime]
    (hpF : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p})
    (J : AddSubgroup W.toAffine.Point) [Finite J] :
    let hpK : (p : K) ≠ 0 := by simpa only [map_natCast] using (_root_.map_ne_zero f).mpr hpF
    let H' := primeCyclicKernelMap f W p H
    let e := AddEquiv.cast (M := fun V : WeierstrassCurve K => V.toAffine.Point)
      (primeAbscissaQuotient_map f W p H)
    (J.map (primeAbscissaHom W p hpF H)).map (pointMapHom f (primeAbscissaQuotient W p H)) =
      ((J.map (pointMapHom f W)).map (primeAbscissaHom (W.map f) p hpK H')).map e.toAddMonoidHom := by
  intro hpK H' e
  let φ := (pointMapHom f (primeAbscissaQuotient W p H)).comp (primeAbscissaHom W p hpF H)
  let ψ := e.toAddMonoidHom.comp ((primeAbscissaHom (W.map f) p hpK H').comp (pointMapHom f W))
  have hmem (R : W.toAffine.Point) : pointMapHom f W R ∈ H'.1 ↔ R ∈ H.1 := by
    change pointMapHom f W R ∈ H.1.map (pointMapHom f W) ↔ R ∈ H.1
    constructor
    · rintro ⟨S, hS, he⟩
      exact (pointMapHom_injective f W he) ▸ hS
    · intro hR
      exact ⟨R, hR, rfl⟩
  have hφ (R : W.toAffine.Point) : φ R = 0 ↔ R ∈ H.1 := by
    change pointMapHom f (primeAbscissaQuotient W p H) (primeAbscissaHom W p hpF H R) = 0 ↔ _
    rw [← (pointMapHom f (primeAbscissaQuotient W p H)).map_zero,
      (pointMapHom_injective f (primeAbscissaQuotient W p H)).eq_iff,
      ← AddMonoidHom.mem_ker, primeAbscissaHom_ker]
  have hψ (R : W.toAffine.Point) : ψ R = 0 ↔ R ∈ H.1 := by
    change e (primeAbscissaHom (W.map f) p hpK H' (pointMapHom f W R)) = 0 ↔ _
    rw [← e.map_zero, e.injective.eq_iff, ← AddMonoidHom.mem_ker, primeAbscissaHom_ker]
    exact hmem R
  have hz (R : W.toAffine.Point) : φ R = 0 ↔ ψ R = 0 := (hφ R).trans (hψ R).symm
  have hx (R : W.toAffine.Point) (hR : φ R ≠ 0) :
      (coordsOrZero (φ R)).1 = (coordsOrZero (ψ R)).1 := by
    have hRH : R ∉ H.1 := fun he => hR ((hφ R).mpr he)
    have hRH' : pointMapHom f W R ∉ H'.1 := fun he => hRH ((hmem R).mp he)
    change (coordsOrZero (pointMapHom f (primeAbscissaQuotient W p H)
      (primeAbscissaHom W p hpF H R))).1 =
        (coordsOrZero (e (primeAbscissaHom (W.map f) p hpK H' (pointMapHom f W R)))).1
    rw [coordsOrZero_pointMapHom, coordsOrZero_cast]
    change f (coordsOrZero (primeAbscissaHom W p hpF H R)).1 =
      (coordsOrZero (primeAbscissaHom (W.map f) p hpK H' (pointMapHom f W R))).1
    rw [primeAbscissaHom_x W p hpF H R hRH,
      primeAbscissaHom_x (W.map f) p hpK H' (pointMapHom f W R) hRH', coordsOrZero_pointMapHom]
    exact (primeAbscissaQuotientX_map f W p H (coordsOrZero R).1).symm
  have he := subgroup_map_eq_of_nonzero_abscissae ((primeAbscissaQuotient W p H).map f) J φ ψ hz hx
  simpa only [AddSubgroup.map_map, φ, ψ, AddMonoidHom.comp_assoc] using he

end
end Dubon2026.SourceEllipticVelu
