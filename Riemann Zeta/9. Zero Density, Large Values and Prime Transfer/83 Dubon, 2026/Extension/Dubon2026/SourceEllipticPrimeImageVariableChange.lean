import Dubon2026.SourceEllipticPrimeVariableX
import Dubon2026.SourceEllipticAbscissaSubgroupEquality

/-! Actual prime quotient images respect the original coordinate change.
The existing exact kernel and abscissa equality up to sign identify the
image subgroups. This supplies the necessary step in composite quotient
transport for the DUB-17/18 cyclic-root bijection and inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticVariableChange OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- The actual finite subgroup image under the specific quotient commutes with change of model. -/
theorem primeAbscissaHom_image_variableChange
    (C : VariableChange F) (W : WeierstrassCurve F) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hpF : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p})
    (J : AddSubgroup W.toAffine.Point) [Finite J] :
    let d := (variableChangeAddEquiv C W.toAffine).symm
    let H' := cyclicKernelVariableChange C W p H
    let V := primeAbscissaQuotient W p H
    let v := (variableChangeAddEquiv C V.toAffine).symm
    let e := AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point)
      (primeAbscissaQuotient_variableChange C W p hpF H)
    (J.map (primeAbscissaHom W p hpF H)).map v.toAddMonoidHom =
      ((J.map d.toAddMonoidHom).map (primeAbscissaHom (C • W) p hpF H')).map e.toAddMonoidHom := by
  intro d H' V v e
  let φ := v.toAddMonoidHom.comp (primeAbscissaHom W p hpF H)
  let ψ := e.toAddMonoidHom.comp ((primeAbscissaHom (C • W) p hpF H').comp d.toAddMonoidHom)
  have hmem (R : W.toAffine.Point) : d R ∈ H'.1 ↔ R ∈ H.1 := by
    change d R ∈ H.1.map d.toAddMonoidHom ↔ R ∈ H.1
    constructor
    · rintro ⟨S, hS, he⟩
      exact (d.injective he) ▸ hS
    · intro hR
      exact ⟨R, hR, rfl⟩
  have hφ (R : W.toAffine.Point) : φ R = 0 ↔ R ∈ H.1 := by
    change v (primeAbscissaHom W p hpF H R) = 0 ↔ _
    rw [← v.map_zero, v.injective.eq_iff, ← AddMonoidHom.mem_ker, primeAbscissaHom_ker]
  have hψ (R : W.toAffine.Point) : ψ R = 0 ↔ R ∈ H.1 := by
    change e (primeAbscissaHom (C • W) p hpF H' (d R)) = 0 ↔ _
    rw [← e.map_zero, e.injective.eq_iff, ← AddMonoidHom.mem_ker, primeAbscissaHom_ker]
    exact hmem R
  have hz (R : W.toAffine.Point) : φ R = 0 ↔ ψ R = 0 := (hφ R).trans (hψ R).symm
  have hx (R : W.toAffine.Point) (hR : φ R ≠ 0) :
      (coordsOrZero (φ R)).1 = (coordsOrZero (ψ R)).1 := by
    have hRH : R ∉ H.1 := fun he => hR ((hφ R).mpr he)
    have hRH' : d R ∉ H'.1 := fun he => hRH ((hmem R).mp he)
    have hR0 : R ≠ 0 := by rintro rfl; exact hRH H.1.zero_mem
    have hQ0 : primeAbscissaHom W p hpF H R ≠ 0 := by
      intro hq
      apply hR
      change v (primeAbscissaHom W p hpF H R) = 0
      rw [hq, map_zero]
    change (coordsOrZero (v (primeAbscissaHom W p hpF H R))).1 =
      (coordsOrZero (e (primeAbscissaHom (C • W) p hpF H' (d R)))).1
    rw [coordsOrZero_cast]
    change (coordsOrZero (vcInvFun C V.toAffine (primeAbscissaHom W p hpF H R))).1 = _
    rw [coordsOrZero_vcInvFun_of_ne_zero C V hQ0]
    change vcXInv C (coordsOrZero (primeAbscissaHom W p hpF H R)).1 =
      (coordsOrZero (primeAbscissaHom (C • W) p hpF H' (d R))).1
    rw [primeAbscissaHom_x W p hpF H R hRH,
      primeAbscissaHom_x (C • W) p hpF H' (d R) hRH']
    have hcoord : (coordsOrZero (d R)).1 = vcXInv C (coordsOrZero R).1 :=
      congrArg Prod.fst (coordsOrZero_vcInvFun_of_ne_zero C W hR0)
    rw [hcoord]
    exact (primeAbscissaQuotientX_variableChange C W p hpF H (coordsOrZero R).1).symm
  have he := subgroup_map_eq_of_nonzero_abscissae (C • V) J φ ψ hz hx
  simpa only [AddSubgroup.map_map, φ, ψ, AddMonoidHom.comp_assoc] using he

end
end Dubon2026.SourceEllipticVelu
