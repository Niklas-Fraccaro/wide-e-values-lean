import WideE.PVTorsor
import WideE.GaloisPoints

/-!
# Galois cocycles of affine torsor points

The canonical torsor chart gives a unique group point carrying one torsor
point to another. The Galois cocycle of a point records these group points
for its Galois conjugates.
-/

noncomputable section

open scoped TensorProduct

namespace WideE

section TensorEvaluation

variable {k F A B L : Type*} [CommRing k] [CommRing F] [CommRing A] [CommRing B] [CommRing L]
variable [Algebra k F] [Algebra k A] [Algebra F A] [IsScalarTower k F A]
variable [Algebra k B] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

private def tensorPoint (p : A →ₐ[F] L) (q : B →ₐ[k] L) : A ⊗[k] B →ₐ[F] L :=
  Algebra.TensorProduct.lift p q fun _ _ => Commute.all _ _

@[simp] private theorem tensorPoint_tmul (p : A →ₐ[F] L) (q : B →ₐ[k] L) (a : A) (b : B) :
    tensorPoint p q (a ⊗ₜ[k] b) = p a * q b :=
  Algebra.TensorProduct.lift_tmul p q _ a b

private theorem tensorPoint_postcompose (σ : L →ₐ[F] L)
    (p : A →ₐ[F] L) (q : B →ₐ[k] L) (z : A ⊗[k] B) :
    σ (tensorPoint p q z) = tensorPoint (σ.comp p) ((σ.restrictScalars k).comp q) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
      simp only [tensorPoint_tmul, map_mul, AlgHom.comp_apply, AlgHom.restrictScalars_apply]

private theorem tensorPoint_assoc {C : Type*} [CommRing C] [Algebra k C]
    (p : A →ₐ[F] L) (q : B →ₐ[k] L) (r : C →ₐ[k] L) (z : (A ⊗[k] B) ⊗[k] C) :
    tensorPoint (tensorPoint p q) r z =
      tensorPoint p (tensorPoint q r) (Algebra.TensorProduct.assoc k A B C z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z c =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul a b =>
          simp only [Algebra.TensorProduct.assoc_tmul, tensorPoint_tmul, mul_assoc]

end TensorEvaluation

section HopfPoints

variable {k H L : Type*} [CommRing k] [CommRing H] [CommRing L]
variable [Bialgebra k H] [Algebra k L]

/-- Multiplication of points of the affine group, induced by comultiplication. -/
def hopfPointMul (g h : H →ₐ[k] L) : H →ₐ[k] L :=
  (tensorPoint g h).comp (Bialgebra.comulAlgHom k H)

/-- The identity point, induced by the counit. -/
def hopfPointOne : H →ₐ[k] L :=
  (Algebra.ofId k L).comp (Bialgebra.counitAlgHom k H)

end HopfPoints

section Action

variable {k F S H L : Type*} [CommRing k] [CommRing F] [CommRing S] [CommRing H] [CommRing L]
variable [Algebra k F] [Algebra k S] [Algebra F S] [IsScalarTower k F S]
variable [HopfAlgebra k H] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

namespace AffineHopfTorsor

/-- The right action on points is evaluation of the coaction. -/
def actPoint (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) (g : H →ₐ[k] L) : S →ₐ[F] L :=
  (tensorPoint p g).comp T.coaction

private theorem actPoint_apply (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (g : H →ₐ[k] L) (s : S) :
    T.actPoint p g s = tensorPoint p g (T.coaction s) := rfl

theorem actPoint_one (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) :
    T.actPoint p hopfPointOne = p := by
  have h (z : S ⊗[k] H) : tensorPoint p hopfPointOne z = p (coactionCounit z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a =>
        simp only [tensorPoint_tmul, coactionCounit, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply,
          AlgHom.comp_apply, Algebra.ofId_apply, hopfPointOne, map_mul]
        have hScalar (x : k) : p (algebraMap k S x) = algebraMap k L x :=
          (p.restrictScalars k).commutes x
        rw [hScalar]
  apply AlgHom.ext
  intro s
  rw [actPoint_apply, h, T.counital]

theorem actPoint_mul (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (g h : H →ₐ[k] L) :
    T.actPoint (T.actPoint p g) h = T.actPoint p (hopfPointMul g h) := by
  have hLeft (z : S ⊗[k] H) :
      tensorPoint (T.actPoint p g) h z =
        tensorPoint (tensorPoint p g) h
          (Algebra.TensorProduct.map (T.coaction.restrictScalars k) (AlgHom.id k H) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a =>
        simp only [tensorPoint_tmul, Algebra.TensorProduct.map_tmul, AlgHom.restrictScalars_apply,
          AlgHom.id_apply, actPoint_apply]
  have hRight (z : S ⊗[k] H) :
      tensorPoint p (tensorPoint g h)
        (Algebra.TensorProduct.map (AlgHom.id S S) (Bialgebra.comulAlgHom k H) z) =
      tensorPoint p (hopfPointMul g h) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s a =>
        simp only [tensorPoint_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
          hopfPointMul, AlgHom.comp_apply]
  apply AlgHom.ext
  intro s
  rw [actPoint_apply, hLeft, tensorPoint_assoc, T.coassociative, hRight, actPoint_apply]

theorem postcompose_actPoint (T : AffineHopfTorsor k F S H)
    (σ : L →ₐ[F] L) (p : S →ₐ[F] L) (g : H →ₐ[k] L) :
    σ.comp (T.actPoint p g) = T.actPoint (σ.comp p) ((σ.restrictScalars k).comp g) := by
  apply AlgHom.ext
  intro s
  simp only [AlgHom.comp_apply, actPoint_apply, tensorPoint_postcompose]

private theorem chart_left (T : AffineHopfTorsor k F S H) (s : S) :
    T.chart (s ⊗ₜ[k] (1 : H)) = s ⊗ₜ[F] (1 : S) := by
  apply T.chart.symm.injective
  rw [AlgEquiv.symm_apply_apply, T.chart_symm_apply, map_one, mul_one]

private theorem chart_coaction (T : AffineHopfTorsor k F S H) (s : S) :
    T.chart (T.coaction s) = (1 : S) ⊗ₜ[F] s := by
  apply T.chart.symm.injective
  rw [AlgEquiv.symm_apply_apply, T.chart_symm_apply, ← Algebra.TensorProduct.one_def, one_mul]

private def chartPoint (T : AffineHopfTorsor k F S H)
    (p q : S →ₐ[F] L) : S ⊗[k] H →ₐ[k] L :=
  ((tensorPoint p q).restrictScalars k).comp (T.chart.restrictScalars k).toAlgHom

/-- The group point carrying the first torsor point to the second. -/
def pointDifference (T : AffineHopfTorsor k F S H)
    (p q : S →ₐ[F] L) : H →ₐ[k] L :=
  (chartPoint T p q).comp Algebra.TensorProduct.includeRight

private theorem eval_chartPoint (T : AffineHopfTorsor k F S H)
    (p q : S →ₐ[F] L) (z : S ⊗[k] H) :
    tensorPoint p (T.pointDifference p q) z = chartPoint T p q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s h =>
      have hleft : chartPoint T p q (s ⊗ₜ[k] (1 : H)) = p s := by
        change tensorPoint p q (T.chart (s ⊗ₜ[k] (1 : H))) = p s
        rw [chart_left, tensorPoint_tmul, map_one, mul_one]
      have hright : chartPoint T p q ((1 : S) ⊗ₜ[k] h) = T.pointDifference p q h := rfl
      have hsplit : (s ⊗ₜ[k] (1 : H)) * ((1 : S) ⊗ₜ[k] h) = s ⊗ₜ[k] h := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      calc
        tensorPoint p (T.pointDifference p q) (s ⊗ₜ[k] h) =
            p s * T.pointDifference p q h := tensorPoint_tmul p _ s h
        _ = chartPoint T p q ((s ⊗ₜ[k] (1 : H)) * ((1 : S) ⊗ₜ[k] h)) := by
          rw [map_mul, hleft, hright]
        _ = chartPoint T p q (s ⊗ₜ[k] h) := congrArg (chartPoint T p q) hsplit

@[simp] theorem actPoint_pointDifference (T : AffineHopfTorsor k F S H)
    (p q : S →ₐ[F] L) : T.actPoint p (T.pointDifference p q) = q := by
  apply AlgHom.ext
  intro s
  rw [actPoint_apply, eval_chartPoint]
  change tensorPoint p q (T.chart (T.coaction s)) = q s
  rw [chart_coaction, tensorPoint_tmul, map_one, one_mul]

private theorem eval_chart_symm (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (g : H →ₐ[k] L) (z : S ⊗[F] S) :
    tensorPoint p (T.actPoint p g) z = tensorPoint p g (T.chart.symm z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t =>
      rw [tensorPoint_tmul, T.chart_symm_apply, map_mul, tensorPoint_tmul, map_one, mul_one,
        actPoint_apply]

@[simp] theorem pointDifference_actPoint (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (g : H →ₐ[k] L) : T.pointDifference p (T.actPoint p g) = g := by
  apply AlgHom.ext
  intro h
  change tensorPoint p (T.actPoint p g) (T.chart ((1 : S) ⊗ₜ[k] h)) = g h
  rw [eval_chart_symm, AlgEquiv.symm_apply_apply, tensorPoint_tmul, map_one, one_mul]

theorem actPoint_injective (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) :
    Function.Injective (T.actPoint p) :=
  Function.LeftInverse.injective (T.pointDifference_actPoint p)

/-- Over any target algebra, the action carries a point to any other point uniquely. -/
theorem existsUnique_groupPoint (T : AffineHopfTorsor k F S H) (p q : S →ₐ[F] L) :
    ∃! g : H →ₐ[k] L, T.actPoint p g = q :=
  ⟨T.pointDifference p q, T.actPoint_pointDifference p q,
    fun _ hg => T.actPoint_injective p (hg.trans (T.actPoint_pointDifference p q).symm)⟩

end AffineHopfTorsor

end Action

section FiniteType

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

private def extendInclusion (C : Subalgebra R S) : A ⊗[R] C →ₐ[A] A ⊗[R] S :=
  Algebra.TensorProduct.map (AlgHom.id A A) C.val

private theorem extendInclusion_range_mono {C D : Subalgebra R S} (h : C ≤ D) :
    (extendInclusion (A := A) C).range ≤ (extendInclusion (A := A) D).range := by
  rintro _ ⟨x, rfl⟩
  let j := Subalgebra.inclusion h
  refine ⟨Algebra.TensorProduct.map (AlgHom.id A A) j x, ?_⟩
  have he : D.val.comp j = C.val := rfl
  change ((Algebra.TensorProduct.map (AlgHom.id A A) D.val).comp
    (Algebra.TensorProduct.map (AlgHom.id A A) j)) x =
      Algebra.TensorProduct.map (AlgHom.id A A) C.val x
  rw [← Algebra.TensorProduct.map_id_comp, he]

private theorem exists_finset_tensors (z : A ⊗[R] S) :
    ∃ g : Finset S, z ∈ (extendInclusion (A := A) (Algebra.adjoin R (g : Set S))).range := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨∅, (AlgHom.range _).zero_mem⟩
  | tmul a s =>
      refine ⟨{s}, ⟨a ⊗ₜ[R] ⟨s, Algebra.subset_adjoin (by simp)⟩, rfl⟩⟩
  | add x y hx hy =>
      obtain ⟨g, hg⟩ := hx
      obtain ⟨h, hh⟩ := hy
      have gx : (g : Set S) ⊆ ↑(g ∪ h) := Finset.subset_union_left
      have gy : (h : Set S) ⊆ ↑(g ∪ h) := Finset.subset_union_right
      exact ⟨g ∪ h, (AlgHom.range _).add_mem
        (extendInclusion_range_mono (Algebra.adjoin_mono gx) hg)
        (extendInclusion_range_mono (Algebra.adjoin_mono gy) hh)⟩

/-- Finite generation of an algebra descends along a faithfully flat scalar extension. -/
theorem finiteType_of_faithfullyFlat_baseChange [Module.FaithfullyFlat R A]
    [Algebra.FiniteType A (A ⊗[R] S)] : Algebra.FiniteType R S := by
  classical
  obtain ⟨g, hg⟩ := (inferInstance : Algebra.FiniteType A (A ⊗[R] S)).out
  choose q hq using (fun i : g => exists_finset_tensors (i : A ⊗[R] S))
  let f := g.attach.biUnion q
  let C := Algebra.adjoin R (f : Set S)
  have hRange : (extendInclusion (A := A) C).range = ⊤ := by
    apply top_unique
    rw [← hg, Algebra.adjoin_le_iff]
    intro x hx
    let i : g := ⟨x, hx⟩
    have hsub : (q i : Set S) ⊆ f := fun z hz =>
      Finset.mem_biUnion.mpr ⟨i, g.mem_attach i, hz⟩
    exact extendInclusion_range_mono (Algebra.adjoin_mono hsub) (hq i)
  have hSurj : Function.Surjective (C.val.toLinearMap.lTensor A) := by
    exact (AlgHom.range_eq_top _).mp hRange
  have hC : Function.Surjective C.val.toLinearMap :=
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R A C.val.toLinearMap).mp hSurj
  refine ⟨⟨f, top_unique ?_⟩⟩
  intro x _
  obtain ⟨y, hy⟩ := hC x
  exact hy ▸ y.property

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
variable [Algebra k R] [Algebra k S] [IsScalarTower k R S]

/-- Finite generation of a torsor ring follows from that of the group and the
faithfully flat canonical chart. -/
theorem AffineHopfTorsor.finiteType (T : AffineHopfTorsor k R S H) :
    Algebra.FiniteType R S := by
  letI := T.group_finiteType
  letI : Algebra.FiniteType S (S ⊗[k] H) := Algebra.FiniteType.baseChange (R := k) S
  letI : Algebra.FiniteType S (S ⊗[R] S) :=
    (inferInstance : Algebra.FiniteType S (S ⊗[k] H)).equiv T.chart
  letI := T.faithfullyFlat
  exact finiteType_of_faithfullyFlat_baseChange (A := S)

end FiniteType

section Galois

variable {k F S H L : Type*} [CommRing k] [Field F] [CommRing S] [CommRing H] [Field L]
variable [Algebra k F] [Algebra k S] [Algebra F S] [IsScalarTower k F S]
variable [HopfAlgebra k H] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

/-- The normalized nonabelian cocycle equations for automorphisms of an extension. -/
def IsHopfPointCocycle (c : (L ≃ₐ[F] L) → H →ₐ[k] L) : Prop :=
  c 1 = hopfPointOne ∧
    ∀ σ τ, c (σ * τ) = hopfPointMul (c σ) ((σ.toAlgHom.restrictScalars k).comp (c τ))

/-- The coboundary equation for the right action convention. -/
def IsHopfPointCoboundary (c : (L ≃ₐ[F] L) → H →ₐ[k] L) : Prop :=
  ∃ b : H →ₐ[k] L, ∀ σ, hopfPointMul (c σ) ((σ.toAlgHom.restrictScalars k).comp b) = b

namespace AffineHopfTorsor

/-- The group point determined by the equation `p ⋅ c(σ) = σ p`. -/
def galoisCocycle (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (σ : L ≃ₐ[F] L) : H →ₐ[k] L :=
  T.pointDifference p (σ.toAlgHom.comp p)

@[simp] theorem actPoint_galoisCocycle (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (σ : L ≃ₐ[F] L) :
    T.actPoint p (T.galoisCocycle p σ) = σ.toAlgHom.comp p :=
  T.actPoint_pointDifference p _

@[simp] theorem galoisCocycle_one (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) :
    T.galoisCocycle p 1 = hopfPointOne := by
  apply T.actPoint_injective p
  rw [actPoint_galoisCocycle, actPoint_one]
  apply AlgHom.ext
  intro s
  rfl

theorem galoisCocycle_mul (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) (σ τ : L ≃ₐ[F] L) :
    T.galoisCocycle p (σ * τ) =
      hopfPointMul (T.galoisCocycle p σ)
        ((σ.toAlgHom.restrictScalars k).comp (T.galoisCocycle p τ)) := by
  apply T.actPoint_injective p
  rw [actPoint_galoisCocycle, ← actPoint_mul, actPoint_galoisCocycle, ← postcompose_actPoint,
    actPoint_galoisCocycle]
  apply AlgHom.ext
  intro s
  rfl

theorem isHopfPointCocycle_galoisCocycle (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) :
    IsHopfPointCocycle (T.galoisCocycle p) :=
  ⟨T.galoisCocycle_one p, T.galoisCocycle_mul p⟩

/-- Twisting a torsor point by a coboundary makes it Galois invariant. -/
theorem exists_basePoint_of_galoisCocycle_coboundary [IsGalois F L]
    (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) (b : H →ₐ[k] L)
    (hb : ∀ σ : L ≃ₐ[F] L, hopfPointMul (T.galoisCocycle p σ)
      ((σ.toAlgHom.restrictScalars k).comp b) = b) :
    ∃ q : S →ₐ[F] F, (Algebra.ofId F L).comp q = T.actPoint p b := by
  apply exists_basePoint_of_galois_fixed (T.actPoint p b)
  intro σ s
  have h : σ.toAlgHom.comp (T.actPoint p b) = T.actPoint p b := by
    rw [T.postcompose_actPoint σ.toAlgHom p b, ← T.actPoint_galoisCocycle p σ, actPoint_mul, hb σ]
  exact DFunLike.congr_fun h s

/-- A point over the base field gives a coboundary for any chosen extension point. -/
theorem exists_coboundary_of_basePoint (T : AffineHopfTorsor k F S H)
    (p : S →ₐ[F] L) (q : S →ₐ[F] F) :
    ∃ b : H →ₐ[k] L, ∀ σ : L ≃ₐ[F] L, hopfPointMul (T.galoisCocycle p σ)
      ((σ.toAlgHom.restrictScalars k).comp b) = b := by
  let f := (Algebra.ofId F L).comp q
  refine ⟨T.pointDifference p f, fun σ => T.actPoint_injective p ?_⟩
  rw [← actPoint_mul, actPoint_galoisCocycle, ← postcompose_actPoint, actPoint_pointDifference]
  apply AlgHom.ext
  intro s
  exact σ.commutes (q s)

/-- The torsor has a base point precisely when its Galois cocycle is a coboundary. -/
theorem nonempty_basePoint_iff_galoisCocycle_coboundary [IsGalois F L]
    (T : AffineHopfTorsor k F S H) (p : S →ₐ[F] L) :
    Nonempty (S →ₐ[F] F) ↔ IsHopfPointCoboundary (T.galoisCocycle p) := by
  constructor
  · rintro ⟨q⟩
    exact T.exists_coboundary_of_basePoint p q
  · rintro ⟨b, hb⟩
    obtain ⟨q, _⟩ := T.exists_basePoint_of_galoisCocycle_coboundary p b hb
    exact ⟨q⟩

/-- Finite Galois cocycle triviality implies that a characteristic-zero affine
torsor has a point over the base field. -/
theorem nonempty_basePoint_of_finiteGalois_cocycle_triviality [CharZero F]
    (T : AffineHopfTorsor k F S H)
    (hTrivial : ∀ (E : IntermediateField F (AlgebraicClosure F))
      [FiniteDimensional F E] [IsGalois F E] (c : (E ≃ₐ[F] E) → H →ₐ[k] E),
      IsHopfPointCocycle c → IsHopfPointCoboundary c) :
    Nonempty (S →ₐ[F] F) := by
  letI := T.faithfullyFlat
  letI := T.finiteType
  letI : Nontrivial S := (Algebra.TensorProduct.lid F S).symm.toEquiv.nontrivial
  obtain ⟨E, hFinite, hGalois, ⟨p⟩⟩ := exists_finiteGalois_point (K := F) (S := S)
  letI := hFinite
  letI := hGalois
  exact (T.nonempty_basePoint_iff_galoisCocycle_coboundary p).mpr
    (hTrivial E (T.galoisCocycle p) (T.isHopfPointCocycle_galoisCocycle p))

end AffineHopfTorsor

end Galois

end WideE
