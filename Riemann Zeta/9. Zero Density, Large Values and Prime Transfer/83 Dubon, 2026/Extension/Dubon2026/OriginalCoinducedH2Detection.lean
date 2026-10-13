import Dubon2026.CoinducedSubgroupCoordinates
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Coinduced

/-! # Actual H2 detection by subgroup restriction and identity evaluation

The existing explicit prism argument is used only in degree two, now
for an arbitrary subgroup coefficient. Completion stabilizer coefficients
need not extend to the full global Galois group. The result supplies
literal local restriction maps, rather than merely an abstract Shapiro
isomorphism, in DUB-17's global H2 detection and invariant sum-zero chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G] (S : Subgroup G) (B : Rep R S)

private def originalCoinducedTriangle
    (c : G × G → Rep.coind S.subtype B) (x y z : G) : B :=
  (c (x⁻¹ * y, y⁻¹ * z)).val x


private theorem originalCoinducedTriangle_cocycle
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype B))
    (x y z t : G) :
    originalCoinducedTriangle S B c x z t + originalCoinducedTriangle S B c x y z =
      originalCoinducedTriangle S B c y z t + originalCoinducedTriangle S B c x y t := by
  have hc := congrArg (fun f : Rep.coind S.subtype B => f.val x)
    ((groupCohomology.mem_cocycles₂_iff _).mp c.property (x⁻¹ * y) (y⁻¹ * z) (z⁻¹ * t))
  change (c ((x⁻¹ * y) * (y⁻¹ * z), z⁻¹ * t)).val x + (c (x⁻¹ * y, y⁻¹ * z)).val x =
    (c (y⁻¹ * z, z⁻¹ * t)).val (x * (x⁻¹ * y)) + (c (x⁻¹ * y, (y⁻¹ * z) * (z⁻¹ * t))).val x at hc
  simpa only [originalCoinducedTriangle, mul_assoc, mul_inv_cancel_left] using hc


private theorem originalCoinducedTriangle_equivariant
    (c : G × G → Rep.coind S.subtype B) (s : S) (x y z : G) :
    originalCoinducedTriangle S B c ((s : G) * x) ((s : G) * y) ((s : G) * z) =
      B.ρ s (originalCoinducedTriangle S B c x y z) := by
  have hxy : ((s : G) * x)⁻¹ * ((s : G) * y) = x⁻¹ * y := by group
  have hyz : ((s : G) * y)⁻¹ * ((s : G) * z) = y⁻¹ * z := by group
  change (c ((((s : G) * x)⁻¹ * ((s : G) * y)),
    (((s : G) * y)⁻¹ * ((s : G) * z)))).val ((s : G) * x) = _
  rw [hxy, hyz]
  exact (c (x⁻¹ * y, y⁻¹ * z)).property s x

private theorem originalCoinducedTriangle_prism
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype B))
    (x y z px py pz : G) :
    (originalCoinducedTriangle S B c y py pz - originalCoinducedTriangle S B c y z pz) -
      (originalCoinducedTriangle S B c x px pz - originalCoinducedTriangle S B c x z pz) +
      (originalCoinducedTriangle S B c x px py - originalCoinducedTriangle S B c x y py) =
        originalCoinducedTriangle S B c px py pz - originalCoinducedTriangle S B c x y z := by
  have h₁ := originalCoinducedTriangle_cocycle S B c x y py pz
  have h₂ := originalCoinducedTriangle_cocycle S B c x px py pz
  have h₃ := originalCoinducedTriangle_cocycle S B c x y z pz
  have he := congrArg₂ (fun a b : B => a - b)
    (congrArg₂ (fun a b : B => a + b) h₂ h₃) h₁
  apply sub_eq_zero.mp
  calc
    _ = ((originalCoinducedTriangle S B c x py pz + originalCoinducedTriangle S B c x px py) +
          (originalCoinducedTriangle S B c x z pz + originalCoinducedTriangle S B c x y z) -
          (originalCoinducedTriangle S B c x py pz + originalCoinducedTriangle S B c x y py)) -
        ((originalCoinducedTriangle S B c px py pz + originalCoinducedTriangle S B c x px pz) +
          (originalCoinducedTriangle S B c y z pz + originalCoinducedTriangle S B c x y pz) -
          (originalCoinducedTriangle S B c y py pz + originalCoinducedTriangle S B c x y pz)) := by abel
    _ = 0 := sub_eq_zero.mpr he

private def originalCoinducedBoundaryLift (b : S → B) (g : G) : Rep.coind S.subtype B :=
  ⟨fun t => B.ρ (coinducedSubgroupCoordinate S t)
      (b ((coinducedSubgroupCoordinate S t)⁻¹ * coinducedSubgroupCoordinate S (t * g))), by
    intro s t
    change B.ρ (coinducedSubgroupCoordinate S ((s : G) * t))
        (b ((coinducedSubgroupCoordinate S ((s : G) * t))⁻¹ *
          coinducedSubgroupCoordinate S (((s : G) * t) * g))) = _
    rw [mul_assoc, coinducedSubgroupCoordinate_mul, coinducedSubgroupCoordinate_mul,
      mul_inv_rev, mul_assoc, inv_mul_cancel_left, map_mul]
    rfl⟩

private def originalCoinducedPrismBoundary
    (c : G × G → Rep.coind S.subtype B) (g : G) : Rep.coind S.subtype B :=
  ⟨fun t => originalCoinducedTriangle S B c t (coinducedSubgroupCoordinate S t)
      (coinducedSubgroupCoordinate S (t * g)) -
    originalCoinducedTriangle S B c t (t * g) (coinducedSubgroupCoordinate S (t * g)), by
    intro s t
    change originalCoinducedTriangle S B c ((s : G) * t)
        (coinducedSubgroupCoordinate S ((s : G) * t))
        (coinducedSubgroupCoordinate S (((s : G) * t) * g)) -
      originalCoinducedTriangle S B c ((s : G) * t) (((s : G) * t) * g)
        (coinducedSubgroupCoordinate S (((s : G) * t) * g)) = _
    rw [mul_assoc, coinducedSubgroupCoordinate_mul, coinducedSubgroupCoordinate_mul]
    change originalCoinducedTriangle S B c ((s : G) * t)
        ((s : G) * (coinducedSubgroupCoordinate S t : G))
        ((s : G) * (coinducedSubgroupCoordinate S (t * g) : G)) -
      originalCoinducedTriangle S B c ((s : G) * t) ((s : G) * (t * g))
        ((s : G) * (coinducedSubgroupCoordinate S (t * g) : G)) = _
    rw [originalCoinducedTriangle_equivariant, originalCoinducedTriangle_equivariant, map_sub]
    ⟩

/-- A boundary for the actual restricted identity-evaluation cocycle yields a boundary for the original coinduced cocycle. -/
theorem originalCoinduced_twoCocycle_boundary_of_evaluation
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype B))
    (b : S → B) (hb : groupCohomology.d₁₂ B b = fun z : S × S => (c (z.1, z.2)).val 1) :
    c.val ∈ groupCohomology.coboundaries₂ (Rep.coind S.subtype B) := by
  refine ⟨originalCoinducedBoundaryLift S B b - originalCoinducedPrismBoundary S B c, ?_⟩
  rw [map_sub]
  funext z
  rcases z with ⟨g, h⟩
  apply Subtype.ext
  funext t
  let p := coinducedSubgroupCoordinate S
  have hq := originalCoinducedTriangle_prism S B c t (t * g) ((t * g) * h)
    (p t) (p (t * g)) (p ((t * g) * h))
  have ho : originalCoinducedTriangle S B c t (t * g) ((t * g) * h) =
      (c (g, h)).val t := by
    simp only [originalCoinducedTriangle, inv_mul_cancel_left]
  rw [ho] at hq
  have he := congrFun hb ((p t)⁻¹ * p (t * g), (p (t * g))⁻¹ * p ((t * g) * h))
  have hv := (c (((p t : G)⁻¹ * (p (t * g) : G)),
    ((p (t * g) : G)⁻¹ * (p ((t * g) * h) : G)))).property (p t) 1
  have hl : (groupCohomology.d₁₂ (Rep.coind S.subtype B)
      (originalCoinducedBoundaryLift S B b) (g, h)).val t =
        originalCoinducedTriangle S B c (p t) (p (t * g)) (p ((t * g) * h)) := by
    change B.ρ (p (t * g)) (b ((p (t * g))⁻¹ * p ((t * g) * h))) -
      B.ρ (p t) (b ((p t)⁻¹ * p (t * (g * h)))) +
      B.ρ (p t) (b ((p t)⁻¹ * p (t * g))) = _
    change B.ρ ((p t)⁻¹ * p (t * g)) (b ((p (t * g))⁻¹ * p ((t * g) * h))) -
      b (((p t)⁻¹ * p (t * g)) * ((p (t * g))⁻¹ * p ((t * g) * h))) +
      b ((p t)⁻¹ * p (t * g)) = _ at he
    have he' := congrArg (B.ρ (p t)) he
    rw [map_add, map_sub, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left] at he'
    simp only [mul_assoc, mul_inv_cancel_left] at he'
    change _ = (c (((p t : G)⁻¹ * (p (t * g) : G)),
      ((p (t * g) : G)⁻¹ * (p ((t * g) * h) : G)))).val (p t)
    rw [mul_one] at hv
    simp only [mul_assoc, Subgroup.coe_mul, Subgroup.coe_inv] at he' hv
    simpa only [mul_assoc] using he'.trans hv.symm
  have hq' : (groupCohomology.d₁₂ (Rep.coind S.subtype B)
      (originalCoinducedPrismBoundary S B c) (g, h)).val t =
        originalCoinducedTriangle S B c (p t) (p (t * g)) (p ((t * g) * h)) -
          (c (g, h)).val t := by
    change (originalCoinducedPrismBoundary S B c h).val (t * g) -
      (originalCoinducedPrismBoundary S B c (g * h)).val t +
      (originalCoinducedPrismBoundary S B c g).val t = _
    simpa only [originalCoinducedPrismBoundary, p, mul_assoc] using hq
  change (groupCohomology.d₁₂ (Rep.coind S.subtype B)
      (originalCoinducedBoundaryLift S B b) (g, h)).val t -
    (groupCohomology.d₁₂ (Rep.coind S.subtype B)
      (originalCoinducedPrismBoundary S B c) (g, h)).val t = (c (g, h)).val t
  rw [hl, hq']
  abel

/-- The original coinduced coefficient evaluated at the identity after actual subgroup restriction. -/
def originalCoinducedEvaluationRepHom : Rep.res S.subtype (Rep.coind S.subtype B) ⟶ B :=
  Rep.ofHom ⟨{
    toFun := fun f => f.val 1
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }, by
    intro s
    apply LinearMap.ext
    intro f
    change f.val (1 * (s : G)) = B.ρ s (f.val 1)
    simpa only [one_mul, mul_one] using f.property s 1⟩

/-- Actual subgroup restriction followed by identity evaluation detects original coinduced H2. -/
theorem originalCoinducedH2Evaluation_injective :
    Function.Injective (groupCohomology.map S.subtype (originalCoinducedEvaluationRepHom S B) 2) := by
  have hz (x : groupCohomology (Rep.coind S.subtype B) 2)
      (hx : groupCohomology.map S.subtype (originalCoinducedEvaluationRepHom S B) 2 x = 0) :
      x = 0 := by
    induction x using groupCohomology.H2_induction_on with
    | h c =>
      rw [groupCohomology.H2π_comp_map_apply] at hx
      obtain ⟨b, hb⟩ := (groupCohomology.H2π_eq_zero_iff _).mp hx
      exact (groupCohomology.H2π_eq_zero_iff c).mpr
        (originalCoinduced_twoCocycle_boundary_of_evaluation S B c b hb)
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

end
end Dubon2026
