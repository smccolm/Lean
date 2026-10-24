import Dubon2026.SourceEllipticAbscissaVariableQuotient
import Dubon2026.SourceEllipticCyclicAbscissaBaseChange
import Dubon2026.SourceEllipticOddVariableSummingSet

/-! Transport the original finite cyclic kernel by the already proved
coordinate-change additive equivalence. Its abscissae and intrinsic prime
quotient transform literally. This removes the curve-model assumption in
the composite cyclic-root argument serving DUB-17/18 and the inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceEllipticVariableChange OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
variable (C : VariableChange F) (W : WeierstrassCurve F)

/-- The actual cyclic subgroup transported by the original coordinate change. -/
def cyclicKernelVariableChange (N : ℕ)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = N}) :
    {H : AddSubgroup (C • W).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} :=
  let e := (variableChangeAddEquiv C W.toAffine).symm
  let h := SourceEllipticCyclicCount.isAddCyclic_map_and_card_of_injective N
    e.toAddMonoidHom e.injective H.2
  ⟨H.1.map e.toAddMonoidHom, h.1, h.2.1⟩

/-- Every nonzero kernel abscissa transforms by the actual inverse affine coordinate. -/
theorem cyclicAbscissae_variableChange (H : AddSubgroup W.toAffine.Point) [Finite H] :
    let e := (variableChangeAddEquiv C W.toAffine).symm
    letI : Finite (H.map e.toAddMonoidHom) := Finite.of_surjective
      (e.toAddMonoidHom.addSubgroupMap H) (e.toAddMonoidHom.addSubgroupMap_surjective H)
    cyclicAbscissae (C • W) (H.map e.toAddMonoidHom) =
      (cyclicAbscissae W H).image (vcXInv C) := by
  intro e
  letI : Finite (H.map e.toAddMonoidHom) := Finite.of_surjective
    (e.toAddMonoidHom.addSubgroupMap H) (e.toAddMonoidHom.addSubgroupMap_surjective H)
  have hcoord (P : W.toAffine.Point) (hP : P ≠ 0) :
      (coordsOrZero (e P)).1 = vcXInv C (coordsOrZero P).1 :=
    congrArg Prod.fst (coordsOrZero_vcInvFun_of_ne_zero C W hP)
  ext x
  rw [mem_cyclicAbscissae, Finset.mem_image]
  constructor
  · rintro ⟨P', hPH, hP'0, hx⟩
    obtain ⟨P, hPH, rfl⟩ := hPH
    have hP0 : P ≠ 0 := by intro hz; apply hP'0; rw [hz, map_zero]
    refine ⟨(coordsOrZero P).1, (mem_cyclicAbscissae W H _).mpr ⟨P, hPH, hP0, rfl⟩, ?_⟩
    exact (hcoord P hP0).symm.trans hx
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨P, hPH, hP0, hPy⟩ := (mem_cyclicAbscissae W H y).mp hy
    refine ⟨e P, ⟨P, hPH, rfl⟩, ?_, ?_⟩
    · exact fun hz => hP0 (e.injective (hz.trans e.map_zero.symm))
    · rw [hcoord P hP0, hPy, hyx]

/-- The intrinsic prime quotient is compatible with the actual change of Weierstrass model. -/
theorem primeAbscissaQuotient_variableChange (p : ℕ) [hp : Fact p.Prime]
    (hpF : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    primeAbscissaQuotient (C • W) p (cyclicKernelVariableChange C W p H) =
      C • primeAbscissaQuotient W p H := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  have he := cyclicAbscissae_variableChange C W H.1
  simp only [primeAbscissaQuotient, cyclicKernelVariableChange]
  split_ifs with hp2
  · rw [he]
    exact variableChange_twoAbscissaQuotient C W _ (by simpa only [hp2] using hpF)
  · rw [he]
    exact variableChange_abscissaQuotient C W _

end
end Dubon2026.SourceEllipticVelu
