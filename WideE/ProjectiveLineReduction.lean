import WideE.ProjectiveOrbitIdeal

/-!
# The affine reduction determined by a primitive orbit line

The line equations define a quotient of the torsor algebra. Its frame vector
is a unit multiple of the chosen vector, and the original generic point
factors through the quotient.
-/

open scoped Matrix TensorProduct

noncomputable section

namespace WideE

variable {ι A : Type*} [CommRing A]

private theorem ideal_span_range_mulVec_le [Fintype ι]
    (M : Matrix ι ι A) (x : ι → A) :
    Ideal.span (Set.range (M *ᵥ x)) ≤ Ideal.span (Set.range x) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change ∑ j, M i j * x j ∈ Ideal.span (Set.range x)
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _
    (Ideal.subset_span (Set.mem_range_self j))

theorem ideal_span_range_mulVec_unit [Fintype ι] [DecidableEq ι]
    (g : (Matrix ι ι A)ˣ) (x : ι → A) :
    Ideal.span (Set.range (g.val *ᵥ x)) = Ideal.span (Set.range x) := by
  apply le_antisymm (ideal_span_range_mulVec_le g.val x)
  have h := ideal_span_range_mulVec_le (g⁻¹).val (g.val *ᵥ x)
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h

theorem ideal_span_range_comp_ringHom {B : Type*} [CommRing B] (f : A →+* B) (x : ι → A) :
    Ideal.span (Set.range (f ∘ x)) = (Ideal.span (Set.range x)).map f := by
  rw [Ideal.map_span, Set.range_comp]

section Line

variable {k R S : Type*} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]

/-- The equations stipulating that the vector of functions `w` lies on the
line of `v`, where `v pivot` is a nonzero coordinate. -/
def projectiveLineIdeal (v : ι → k) (pivot : ι) (w : ι → S) : Ideal S :=
  Ideal.span (Set.range fun j => w j - algebraMap k S (v j / v pivot) * w pivot)

abbrev ProjectiveLineReduction (v : ι → k) (pivot : ι) (w : ι → S) :=
  S ⧸ projectiveLineIdeal v pivot w

/-- The actual quotient map of the closed subscheme cut out by the line. -/
abbrev projectiveLineQuotient (v : ι → k) (pivot : ι) (w : ι → S) :
    S →ₐ[R] ProjectiveLineReduction v pivot w :=
  Ideal.Quotient.mkₐ R (projectiveLineIdeal v pivot w)

theorem projectiveLineIdeal_le_ker [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0) (w : ι → S)
    (f : S →ₐ[R] A) (c : A) (h : f.toRingHom ∘ w = c • (algebraMap k A ∘ v)) :
    projectiveLineIdeal v pivot w ≤ RingHom.ker f := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change f (w j - algebraMap k S (v j / v pivot) * w pivot) = 0
  rw [map_sub, map_mul,
    show f (algebraMap k S (v j / v pivot)) = algebraMap k A (v j / v pivot)
      from (f.restrictScalars k).commutes _]
  have h' (i : ι) : f (w i) = c * algebraMap k A (v i) := congrFun h i
  rw [h' j, h' pivot, mul_left_comm _ c, ← map_mul, div_mul_cancel₀ _ hpivot, sub_self]

/-- Every point whose frame vector lies on the chosen line factors through
the line equations, including the supplied point over the fraction field. -/
theorem existsUnique_projectiveLinePoint [Algebra R A] [Algebra k A] [IsScalarTower k R A]
    (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0) (w : ι → S)
    (f : S →ₐ[R] A) (c : A) (h : f.toRingHom ∘ w = c • (algebraMap k A ∘ v)) :
    ∃! p : ProjectiveLineReduction v pivot w →ₐ[R] A,
      p.comp (projectiveLineQuotient (R := R) v pivot w) = f := by
  let hI := projectiveLineIdeal_le_ker v pivot hpivot w f c h
  let lift := Ideal.Quotient.liftₐ (projectiveLineIdeal v pivot w) f
    (fun _ hx => RingHom.mem_ker.mp (hI hx))
  have hLift : lift.comp (projectiveLineQuotient (R := R) v pivot w) = f :=
    Ideal.Quotient.liftₐ_comp _ _ _
  refine ⟨lift, hLift, ?_⟩
  intro p hp
  apply AlgHom.ext
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (projectiveLineIdeal v pivot w) x
  exact DFunLike.congr_fun (hp.trans hLift.symm) s

omit [Algebra k R] [IsScalarTower k R S] in
theorem projectiveLineQuotient_vector (v : ι → k) (pivot : ι)
    (w : ι → S) :
    ∃ c : ProjectiveLineReduction v pivot w,
      (projectiveLineQuotient (R := R) v pivot w).toRingHom ∘ w =
        c • (algebraMap k (ProjectiveLineReduction v pivot w) ∘ v) := by
  let Q := ProjectiveLineReduction v pivot w
  let π := projectiveLineQuotient (R := R) v pivot w
  refine ⟨algebraMap k Q (v pivot)⁻¹ * π (w pivot), funext ?_⟩
  intro j
  have hmem : w j - algebraMap k S (v j / v pivot) * w pivot ∈ projectiveLineIdeal v pivot w :=
    Ideal.subset_span (Set.mem_range_self j)
  have hz : π (w j - algebraMap k S (v j / v pivot) * w pivot) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub, map_mul, show π (algebraMap k S (v j / v pivot)) =
    algebraMap k Q (v j / v pivot) from Ideal.Quotient.mk_algebraMap k _ _,
    sub_eq_zero] at hz
  change π (w j) = algebraMap k Q (v pivot)⁻¹ * π (w pivot) * algebraMap k Q (v j)
  rw [hz, div_eq_mul_inv, map_mul]
  ac_rfl

omit [Algebra k R] [IsScalarTower k R S] in
/-- Primitivity on the original algebra means the line scalar on this
quotient is invertible, over arbitrary coefficient rings. -/
theorem projectiveLineQuotient_unit_vector (v : ι → k) (pivot : ι)
    (w : ι → S) (hPrimitive : Ideal.span (Set.range w) = ⊤) :
    ∃ c : (ProjectiveLineReduction v pivot w)ˣ,
      (projectiveLineQuotient (R := R) v pivot w).toRingHom ∘ w =
        (c : ProjectiveLineReduction v pivot w) •
          (algebraMap k (ProjectiveLineReduction v pivot w) ∘ v) := by
  let Q := ProjectiveLineReduction v pivot w
  let π := projectiveLineQuotient (R := R) v pivot w
  obtain ⟨c, hc⟩ := projectiveLineQuotient_vector (R := R) v pivot w
  have hTop : Ideal.span (Set.range (π.toRingHom ∘ w)) = ⊤ := by
    rw [ideal_span_range_comp_ringHom, hPrimitive, Ideal.map_top]
  have hle : Ideal.span (Set.range (π.toRingHom ∘ w)) ≤ Ideal.span ({c} : Set Q) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [hc]
    exact Ideal.mem_span_singleton.mpr ⟨algebraMap k Q (v i), rfl⟩
  have hOne : (1 : Q) ∈ Ideal.span ({c} : Set Q) := hle (hTop.symm ▸ Submodule.mem_top)
  have hu := isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hOne)
  exact ⟨hu.unit, by rw [hu.unit_spec]; exact hc⟩

end Line

section Frame

variable {k R S F : Type*} [Field k] [CommRing R] [CommRing S] [CommRing F]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
  [Algebra R F] [Algebra k F] [IsScalarTower k R F] [Fintype ι] [DecidableEq ι]

/-- The primitive vector in torsor coordinates defined by the comparison frame. -/
def projectiveFrameVector (g : (Matrix ι ι S)ˣ) (y : ι → R) : ι → S :=
  g.val *ᵥ (algebraMap R S ∘ y)

theorem projectiveFrameVector_primitive
    (g : (Matrix ι ι S)ˣ) (y : ι → R) (hy : Ideal.span (Set.range y) = ⊤) :
    Ideal.span (Set.range (projectiveFrameVector g y)) = ⊤ := by
  rw [projectiveFrameVector, ideal_span_range_mulVec_unit, ideal_span_range_comp_ringHom,
    hy, Ideal.map_top]

theorem exists_genericProjectiveLinePoint (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0)
    (g : (Matrix ι ι S)ˣ) (y : ι → R) (f : S →ₐ[R] F) (c : F)
    (hf : g.val.map f.toRingHom *ᵥ (algebraMap R F ∘ y) = c • (algebraMap k F ∘ v)) :
    ∃! p : ProjectiveLineReduction v pivot (projectiveFrameVector g y) →ₐ[R] F,
      p.comp (projectiveLineQuotient v pivot (projectiveFrameVector g y)) = f := by
  apply existsUnique_projectiveLinePoint v pivot hpivot _ f c
  have hScalar : f.toRingHom.comp (algebraMap R S) = algebraMap R F := RingHom.ext f.commutes
  funext i
  change f.toRingHom ((g.val *ᵥ (algebraMap R S ∘ y)) i) = (c • (algebraMap k F ∘ v)) i
  rw [RingHom.map_mulVec,
    show f.toRingHom ∘ (algebraMap R S ∘ y) = algebraMap R F ∘ y from
      congrArg (fun r : R →+* F => r ∘ y) hScalar, hf]

omit [Algebra k R] [IsScalarTower k R S] in
/-- The vanishing of the descended polynomial equations implies the
corresponding cone equations for the vector in torsor coordinates. -/
theorem projectiveFrameVector_vanishes
    (I : Ideal (MvPolynomial ι k)) (J : Ideal (MvPolynomial ι R))
    (g : (Matrix ι ι S)ˣ) (y : ι → R)
    (hJ : J.map (MvPolynomial.map (algebraMap R S)) = twistedPolynomialIdeal I g.val)
    (hy : ∀ q ∈ J, q.eval y = 0) :
    ∀ p ∈ I, p.eval₂ (algebraMap k S) (projectiveFrameVector g y) = 0 := by
  let ev := MvPolynomial.eval₂Hom (RingHom.id S) (algebraMap R S ∘ y)
  have hKer : J.map (MvPolynomial.map (algebraMap R S)) ≤ RingHom.ker ev := by
    apply (Ideal.map_le_iff_le_comap).mpr
    intro q hq
    change (MvPolynomial.map (algebraMap R S) q).eval₂ (RingHom.id S)
      (algebraMap R S ∘ y) = 0
    rw [MvPolynomial.eval₂_map, RingHom.id_comp, ← MvPolynomial.eval₂_comp, hy q hq, map_zero]
  intro p hp
  have hMem : matrixPolynomialSubstitution g.val (MvPolynomial.map (algebraMap k S) p) ∈
      twistedPolynomialIdeal I g.val :=
    Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp)
  rw [← hJ] at hMem
  have hz := RingHom.mem_ker.mp (hKer hMem)
  change (matrixPolynomialSubstitution g.val (MvPolynomial.map (algebraMap k S) p)).eval₂
    (RingHom.id S) (algebraMap R S ∘ y) = 0 at hz
  rw [eval₂_matrixPolynomialSubstitution, MvPolynomial.eval₂_map, RingHom.id_comp,
    show g.val.map (RingHom.id S) = g.val from rfl] at hz
  exact hz

omit [Algebra k R] [IsScalarTower k R S] in
/-- The morphism of affine coordinate rings associated to a frame vector
satisfying the equations of a closed cone. -/
def projectiveFramePoint
    (I : Ideal (MvPolynomial ι k)) (g : (Matrix ι ι S)ˣ) (y : ι → R)
    (h : ∀ p ∈ I, p.eval₂ (algebraMap k S) (projectiveFrameVector g y) = 0) :
    (MvPolynomial ι k ⧸ I) →ₐ[k] S :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (projectiveFrameVector g y))
    (fun p hp => (MvPolynomial.aeval_eq_eval₂Hom _ _).trans (h p hp))

omit [Algebra k R] [IsScalarTower k R S] in
@[simp]
theorem projectiveFramePoint_coordinate
    (I : Ideal (MvPolynomial ι k)) (g : (Matrix ι ι S)ˣ) (y : ι → R)
    (h : ∀ p ∈ I, p.eval₂ (algebraMap k S) (projectiveFrameVector g y) = 0) (i : ι) :
    projectiveFramePoint I g y h (Ideal.Quotient.mk I (MvPolynomial.X i)) =
      projectiveFrameVector g y i := by
  rw [projectiveFramePoint, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact MvPolynomial.aeval_X _ _

end Frame

section TorsorLine

variable {k R S H F : Type*} [Field k] [CommRing R] [CommRing S] [CommRing H]
  [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra k F] [IsScalarTower k R F] [HopfAlgebra k H] [Fintype ι] [DecidableEq ι]

local notation "ιS" => (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] H)
local notation "ιH" => (Algebra.TensorProduct.includeRight : H →ₐ[k] S ⊗[k] H)

/-- A generically pointed torsor admits a primitive vector satisfying the
orbit cone equations, with equivariant coordinates over the torsor algebra.
The closed subscheme imposing the chosen line retains the generic point. -/
theorem AffineHopfTorsor.exists_genericallyPointedLineReduction
    (T : AffineHopfTorsor k R S H) (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hOne : U.val.map (Bialgebra.counitAlgHom k H).toRingHom = 1)
    (v : ι → k) (pivot : ι) (hpivot : v pivot ≠ 0) (f : S →ₐ[R] F) :
    ∃ (g : (Matrix ι ι S)ˣ) (y : ι → R),
      let w := projectiveFrameVector g y
      let Q := ProjectiveLineReduction v pivot w
      let π := projectiveLineQuotient (R := R) v pivot w
      g.val.map T.coaction.toRingHom = (U⁻¹).val.map (ιH).toRingHom * g.val.map (ιS).toRingHom ∧
      Ideal.span (Set.range w) = ⊤ ∧
      (∀ p ∈ orbitConeIdeal U.val v, p.eval₂ (algebraMap k S) w = 0) ∧
      (∃ c : Qˣ, π.toRingHom ∘ w = (c : Q) • (algebraMap k Q ∘ v)) ∧
      ∃ fQ : Q →ₐ[R] F, fQ.comp π = f := by
  have hv : v ≠ 0 := fun h => hpivot (congrFun h pivot)
  obtain ⟨g, J, y, c, _, hJ, hg, hy, hf, hEq⟩ := T.exists_primitiveOrbitConePoint U hU hOne v hv f
  have hPrimitive := projectiveFrameVector_primitive g y hy
  obtain ⟨fQ, hF, _⟩ := exists_genericProjectiveLinePoint v pivot hpivot g y f (c : F) hf
  exact ⟨g, y, T.representationFrame_coaction U g hg, hPrimitive,
    projectiveFrameVector_vanishes _ J g y hJ hEq,
    projectiveLineQuotient_unit_vector v pivot _ hPrimitive, fQ, hF⟩

end TorsorLine

end WideE
