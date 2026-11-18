import WideE.AffineDominanceExtension
import Mathlib.Algebra.MvPolynomial.Rename

/-! Points of a polynomial relation transfer between ground-field
solutions and solutions over algebraically closed extensions. -/

noncomputable section

open scoped Ideal

namespace WideE

section RelationPoints

variable {k A ν : Type*} [Field k] [CommRing A] [Algebra k A]

/-- Coordinate algebra of a polynomial relation. -/
abbrev PolynomialRelationAlgebra (S : Set (MvPolynomial ν k)) :=
  MvPolynomial ν k ⧸ Ideal.span S

/-- An actual point of the coordinate algebra of a polynomial relation
is precisely a tuple satisfying the given equations. -/
def polynomialRelationPointEquiv (S : Set (MvPolynomial ν k)) :
    (PolynomialRelationAlgebra S →ₐ[k] A) ≃
      {x : ν → A // ∀ p ∈ S, MvPolynomial.aeval x p = 0} := by
  let I := Ideal.span S
  let π := Ideal.Quotient.mkₐ k I
  have hEval (p : PolynomialRelationAlgebra S →ₐ[k] A) :
      MvPolynomial.aeval (fun i => p (π (MvPolynomial.X i))) = p.comp π :=
    MvPolynomial.algHom_ext fun i => MvPolynomial.aeval_X _ i
  refine {
    toFun := fun p => ⟨fun i => p (π (MvPolynomial.X i)), fun f hf => ?_⟩
    invFun := fun x => Ideal.Quotient.liftₐ I (MvPolynomial.aeval x.val) (by
      have hK : I ≤ RingHom.ker (MvPolynomial.aeval x.val).toRingHom :=
        Ideal.span_le.mpr fun f hf => RingHom.mem_ker.mpr (x.prop f hf)
      exact fun f hf => RingHom.mem_ker.mp (hK hf))
    left_inv := fun p => ?_
    right_inv := fun x => ?_ }
  · rw [hEval, AlgHom.comp_apply, show π f = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hf), map_zero]
  · apply AlgHom.ext
    intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I z
    exact DFunLike.congr_fun (hEval p) f
  · apply Subtype.ext
    funext i
    change MvPolynomial.aeval x.val (MvPolynomial.X i) = x.val i
    exact MvPolynomial.aeval_X _ _

@[simp]
theorem polynomialRelationPointEquiv_apply_coordinate (S : Set (MvPolynomial ν k))
    (p : PolynomialRelationAlgebra S →ₐ[k] A) (i : ν) :
    (polynomialRelationPointEquiv S p).val i =
      p (Ideal.Quotient.mkₐ k (Ideal.span S) (MvPolynomial.X i)) := rfl

@[simp]
theorem polynomialRelationPointEquiv_symm_mk (S : Set (MvPolynomial ν k))
    (x : {x : ν → A // ∀ p ∈ S, MvPolynomial.aeval x p = 0}) (p : MvPolynomial ν k) :
    (polynomialRelationPointEquiv S).symm x (Ideal.Quotient.mkₐ k (Ideal.span S) p) =
      MvPolynomial.aeval x.val p := rfl

end RelationPoints

section Witnesses

variable {k ι κ : Type*} [Field k] [IsAlgClosed k] [Finite ι] [Finite κ]

universe uΩ

/-- A polynomial relation that can be solved on a nonempty ground-field
principal open can be solved on a refined principal open over every
algebraically closed coefficient field. -/
theorem exists_refined_polynomial_solution_open_to_algClosed
    (S : Set (MvPolynomial (ι ⊕ κ) k)) (d₀ : MvPolynomial ι k) (hd₀ : d₀ ≠ 0)
    (hLift : ∀ x : ι → k, MvPolynomial.aeval x d₀ ≠ 0 →
      ∃ y : κ → k, ∀ p ∈ S, MvPolynomial.aeval (Sum.elim x y) p = 0) :
    ∃ d : MvPolynomial ι k, d ≠ 0 ∧ d₀ ∣ d ∧
      ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
        (x : ι → Ω), MvPolynomial.aeval x d ≠ 0 →
        ∃ y : κ → Ω, ∀ p ∈ S, MvPolynomial.aeval (Sum.elim x y) p = 0 := by
  let Q := PolynomialRelationAlgebra S
  let I := Ideal.span S
  let π : MvPolynomial (ι ⊕ κ) k →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let f : MvPolynomial ι k →ₐ[k] Q := π.comp (MvPolynomial.rename Sum.inl)
  letI : Algebra.FiniteType k (MvPolynomial (ι ⊕ κ) k) := Algebra.FiniteType.mvPolynomial k _
  have hF : ∀ p : MvPolynomial ι k →ₐ[k] k, p d₀ ≠ 0 → ∃ q : Q →ₐ[k] k, q.comp f = p := by
    intro p hp
    let x (i : ι) := p (MvPolynomial.X i)
    have hx : MvPolynomial.aeval x = p := MvPolynomial.algHom_ext fun i => MvPolynomial.aeval_X x i
    obtain ⟨y, hy⟩ := hLift x (by rwa [hx])
    let q := (polynomialRelationPointEquiv S).symm ⟨Sum.elim x y, hy⟩
    refine ⟨q, MvPolynomial.algHom_ext fun i => ?_⟩
    change q (π (MvPolynomial.rename Sum.inl (MvPolynomial.X i))) = _
    rw [MvPolynomial.rename_X, polynomialRelationPointEquiv_symm_mk, MvPolynomial.aeval_X]
    rfl
  obtain ⟨d, hd, hDiv, hQ⟩ := exists_refined_principal_open_lift_to_algClosed f d₀ hd₀ hF
  refine ⟨d, hd, hDiv, ?_⟩
  intro Ω _ _ _ x hx
  obtain ⟨q, hq⟩ := hQ Ω (MvPolynomial.aeval x) hx
  let z := polynomialRelationPointEquiv S q
  let y (j : κ) := z.val (Sum.inr j)
  have hz : z.val = Sum.elim x y := by
    funext i
    cases i with
    | inl i =>
      change q (π (MvPolynomial.X (Sum.inl i))) = x i
      have h := DFunLike.congr_fun hq (MvPolynomial.X i)
      change q (π (MvPolynomial.rename Sum.inl (MvPolynomial.X i))) =
        MvPolynomial.aeval x (MvPolynomial.X i) at h
      rwa [MvPolynomial.rename_X, MvPolynomial.aeval_X] at h
    | inr j => rfl
  exact ⟨y, hz ▸ z.prop⟩

end Witnesses

section AffineGroundField

variable {k R Ω : Type*} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] [CommRing Ω] [Nontrivial Ω] [Algebra k Ω]

/-- A point of a relation in a finite-type affine scheme under a unit condition
gives a ground-field point of the same relation with nonzero value there. -/
theorem exists_ground_relation_point_of_extension_point
    (S : Set R) (h : R) (p : R →ₐ[k] Ω) (hEq : ∀ a ∈ S, p a = 0)
    (hUnit : IsUnit (p h)) : ∃ q : R →ₐ[k] k, q h ≠ 0 ∧ ∀ a ∈ S, q a = 0 := by
  let I := Ideal.span S
  let Q := R ⧸ I
  let π : R →ₐ[k] Q := Ideal.Quotient.mkₐ k I
  let pQ : Q →ₐ[k] Ω := Ideal.Quotient.liftₐ I p (by
    have hK : I ≤ RingHom.ker p.toRingHom :=
      Ideal.span_le.mpr fun a ha => RingHom.mem_ker.mpr (hEq a ha)
    exact fun a ha => RingHom.mem_ker.mp (hK ha))
  let L := Localization.Away (π h)
  have hpQ : IsUnit (pQ (π h)) := hUnit
  let pL : L →ₐ[k] Ω := localizationAwayUnitEval pQ (π h) hpQ
  letI : Nontrivial L := pL.toRingHom.domain_nontrivial
  letI : Algebra.FiniteType Q L := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (π h)) L
  letI : Algebra.FiniteType k L := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType k Q) (inferInstance : Algebra.FiniteType Q L)
  obtain ⟨z⟩ := StrictEUnit.nonempty_algebraic_point (k := k) (S := L)
  let g : Q →ₐ[k] k := z.comp (IsScalarTower.toAlgHom k Q L)
  refine ⟨g.comp π, ((IsLocalization.Away.algebraMap_isUnit (S := L) (π h)).map z).ne_zero, ?_⟩
  intro a ha
  change g (π a) = 0
  rw [show π a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ha), map_zero]

end AffineGroundField

section AffineGeometricVanishing

variable {k R Ω : Type*} [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] [Field Ω] [Algebra k Ω]

/-- An affine equation holding on the ground-field points of a relation
holds on its points over any extension field. -/
theorem relation_point_apply_eq_zero_of_forall_ground
    (S : Set R) (h : R) (hGround : ∀ q : R →ₐ[k] k, (∀ a ∈ S, q a = 0) → q h = 0)
    (p : R →ₐ[k] Ω) (hEq : ∀ a ∈ S, p a = 0) : p h = 0 := by
  by_contra hp
  obtain ⟨q, hq, hEq'⟩ :=
    exists_ground_relation_point_of_extension_point S h p hEq (isUnit_iff_ne_zero.mpr hp)
  exact hq (hGround q hEq')

end AffineGeometricVanishing

section GroundField

variable {k Ω ν : Type*} [Field k] [IsAlgClosed k] [CommRing Ω] [Nontrivial Ω] [Algebra k Ω] [Finite ν]

/-- If a system of polynomial equations with one nonvanishing condition
has a solution in an extension algebra, it has a ground-field solution. -/
theorem exists_ground_polynomial_solution_of_extension_solution
    (S : Set (MvPolynomial ν k)) (h : MvPolynomial ν k) (x : ν → Ω)
    (hEq : ∀ p ∈ S, MvPolynomial.aeval x p = 0)
    (hUnit : IsUnit (MvPolynomial.aeval x h)) :
    ∃ y : ν → k, MvPolynomial.aeval y h ≠ 0 ∧ ∀ p ∈ S, MvPolynomial.aeval y p = 0 := by
  letI : Algebra.FiniteType k (MvPolynomial ν k) := Algebra.FiniteType.mvPolynomial k ν
  obtain ⟨q, hq, hqEq⟩ :=
    exists_ground_relation_point_of_extension_point S h (MvPolynomial.aeval x) hEq hUnit
  let y (i : ν) := q (MvPolynomial.X i)
  have hy : MvPolynomial.aeval y = q := MvPolynomial.algHom_ext fun i => MvPolynomial.aeval_X y i
  exact ⟨y, hy.symm ▸ hq, hy.symm ▸ hqEq⟩

end GroundField

section GeometricVanishing

variable {k Ω ν : Type*} [Field k] [IsAlgClosed k] [Field Ω] [Algebra k Ω] [Finite ν]

/-- A polynomial that vanishes on every ground-field solution also vanishes
on every solution with coefficients in an extension field. -/
theorem aeval_eq_zero_of_forall_ground_polynomial_solution
    (S : Set (MvPolynomial ν k)) (h : MvPolynomial ν k)
    (hGround : ∀ y : ν → k, (∀ p ∈ S, MvPolynomial.aeval y p = 0) → MvPolynomial.aeval y h = 0)
    (x : ν → Ω) (hEq : ∀ p ∈ S, MvPolynomial.aeval x p = 0) :
    MvPolynomial.aeval x h = 0 := by
  by_contra hx
  obtain ⟨y, hy, hEq'⟩ := exists_ground_polynomial_solution_of_extension_solution
    S h x hEq (isUnit_iff_ne_zero.mpr hx)
  exact hy (hGround y hEq')

end GeometricVanishing

end WideE
