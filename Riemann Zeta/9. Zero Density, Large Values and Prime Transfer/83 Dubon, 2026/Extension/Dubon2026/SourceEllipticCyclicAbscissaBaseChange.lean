import Dubon2026.SourceEllipticAbscissaBaseChange
import Dubon2026.SourceEllipticCyclicRootBaseChange
import Dubon2026.SourceEllipticPrimeAbscissaQuotient

/-! The actual finite kernel abscissae commute with the original point map.
Consequently the intrinsic prime quotient curve commutes with field
embeddings. This supplies coefficient compatibility for the successive
composite cyclic quotients on the DUB-17/18 inertia-census chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve OddDiscriminant SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
variable (f : F →+* K) (W : WeierstrassCurve F)

/-- The whole finite subgroup's abscissae are transported by the actual coefficient embedding. -/
theorem cyclicAbscissae_map (H : AddSubgroup W.toAffine.Point) [Finite H] :
    letI : Finite (H.map (pointMapHom f W)) := Finite.of_surjective
      ((pointMapHom f W).addSubgroupMap H) ((pointMapHom f W).addSubgroupMap_surjective H)
    cyclicAbscissae (W.map f) (H.map (pointMapHom f W)) = (cyclicAbscissae W H).image f := by
  letI : Finite (H.map (pointMapHom f W)) := Finite.of_surjective
    ((pointMapHom f W).addSubgroupMap H) ((pointMapHom f W).addSubgroupMap_surjective H)
  ext x
  rw [mem_cyclicAbscissae, Finset.mem_image]
  constructor
  · rintro ⟨R', hR'H, hR'0, hx⟩
    obtain ⟨R, hRH, rfl⟩ := hR'H
    have hR0 : R ≠ 0 := by intro hz; apply hR'0; rw [hz, map_zero]
    refine ⟨(coordsOrZero R).1, (mem_cyclicAbscissae W H _).mpr ⟨R, hRH, hR0, rfl⟩, ?_⟩
    rw [coordsOrZero_pointMapHom] at hx
    exact hx
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨R, hRH, hR0, hRy⟩ := (mem_cyclicAbscissae W H y).mp hy
    refine ⟨pointMapHom f W R, ⟨R, hRH, rfl⟩, ?_, ?_⟩
    · intro hz
      apply hR0
      exact (pointMapHom_injective f W) (hz.trans (map_zero (pointMapHom f W)).symm)
    · rw [coordsOrZero_pointMapHom]
      change f (coordsOrZero R).1 = x
      rw [hRy, hyx]

/-- The literal intrinsic prime quotient curve commutes with the original field embedding. -/
theorem primeAbscissaQuotient_map (p : ℕ) [hp : Fact p.Prime]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    primeAbscissaQuotient (W.map f) p (primeCyclicKernelMap f W p H) =
      (primeAbscissaQuotient W p H).map f := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  have he := cyclicAbscissae_map f W H.1
  simp only [primeAbscissaQuotient, primeCyclicKernelMap]
  split_ifs with hp2
  · rw [he]
    exact twoAbscissaQuotient_map f W _
  · rw [he]
    exact abscissaQuotient_map f W _

end
end Dubon2026.SourceEllipticVelu
