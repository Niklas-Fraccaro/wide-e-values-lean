import WideE.BlockSchurDiagonal
import WideE.WeightCentralizer
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Localization.Away.Basic

/-! A dense block-unitriangular product identifies the actual block centralizer
with its middle closed subgroup. -/

noncomputable section

open scoped Ideal Matrix TensorProduct

namespace WideE

section LeadingMinors

variable {H R ι β : Type*} [CommRing H] [CommRing R] [Fintype ι] [DecidableEq ι]
  [LinearOrder β]

/-- The principal chart on which all strictly preceding blocks are invertible. -/
def blockLeadingDetProduct (w : ι → β) (M : Matrix ι ι H) : H :=
  ∏ i, (M.toBlock (fun j => w j < w i) (fun j => w j < w i)).det

theorem blockLeadingDetProduct_map (w : ι → β) (f : H →+* R) (M : Matrix ι ι H) :
    f (blockLeadingDetProduct w M) = blockLeadingDetProduct w (M.map f) := by
  unfold blockLeadingDetProduct
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => RingHom.map_det f _

private theorem blockLeadingDetProduct_isUnit (w : ι → β) (M : Matrix ι ι H)
    (hM : ∀ i, IsUnit (M.toBlock (fun j => w j < w i) (fun j => w j < w i)).det) :
    IsUnit (blockLeadingDetProduct w M) := by
  classical
  unfold blockLeadingDetProduct
  let u : ι → Hˣ := fun i => (hM i).unit
  refine ⟨∏ i, u i, ?_⟩
  change Units.coeHom H (∏ i, u i) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => (hM i).unit_spec

private theorem blockLeadingDetProduct_isUnit_of_product
    (w : ι → β) (L T U : (Matrix ι ι H)ˣ)
    (hL : L.val.BlockTriangular (OrderDual.toDual ∘ w))
    (hT : T.val.BlockTriangular w) (hU : U.val.BlockTriangular w) :
    IsUnit (blockLeadingDetProduct w (L.val * T.val * U.val)) := by
  apply blockLeadingDetProduct_isUnit
  intro i
  let p (j : ι) := w j < w i
  have hpT : T.val.toBlock (fun j => ¬p j) p = 0 := Matrix.ext fun r s => hT
    (i := r.val) (j := s.val) (lt_of_lt_of_le s.prop (le_of_not_gt r.prop))
  have hpU : U.val.toBlock (fun j => ¬p j) p = 0 := Matrix.ext fun r s => hU
    (i := r.val) (j := s.val) (lt_of_lt_of_le s.prop (le_of_not_gt r.prop))
  change IsUnit (((L.val * T.val * U.val).toBlock p p).det)
  simp only [Matrix.toBlock_mul_eq_add p p p, hpT, hpU, Matrix.mul_zero, add_zero, Matrix.det_mul]
  exact ((prefixDet_isUnit_of_lowerBlockTriangular w L.val hL (Matrix.isUnits_det_units L) (w i)).mul
    (prefixDet_isUnit_of_blockTriangular w T.val hT (Matrix.isUnits_det_units T) (w i))).mul
      (prefixDet_isUnit_of_blockTriangular w U.val hU (Matrix.isUnits_det_units U) (w i))

end LeadingMinors

section Localization

variable {k H R : Type*} [CommRing k] [CommRing H] [CommRing R] [Algebra k H] [Algebra k R]

/-- Evaluation of the localization at an arbitrary algebra-valued point
where the chosen coordinate is invertible. -/
def localizationAwayUnitEval (f : H →ₐ[k] R) (a : H) (ha : IsUnit (f a)) :
    Localization.Away a →ₐ[k] R where
  toRingHom := IsLocalization.Away.lift a ha
  commutes' c := by
    change IsLocalization.Away.lift (g := f.toRingHom) a ha
      (algebraMap k (Localization.Away a) c) = algebraMap k R c
    rw [IsScalarTower.algebraMap_apply k H (Localization.Away a), IsLocalization.Away.lift_eq]
    exact f.commutes c

@[simp]
theorem localizationAwayUnitEval_algebraMap (f : H →ₐ[k] R) (a : H) (ha : IsUnit (f a))
    (x : H) : localizationAwayUnitEval f a ha (algebraMap H (Localization.Away a) x) = f x :=
  IsLocalization.Away.lift_eq a ha x

private theorem localizationAwayUnitEval_injective (f : H →ₐ[k] R) (a : H) (ha : IsUnit (f a))
    (hf : Function.Injective f) : Function.Injective (localizationAwayUnitEval f a ha) := by
  apply IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers a) (Localization.Away a)
    (localizationAwayUnitEval f a ha).toRingHom
  intro x hx
  change localizationAwayUnitEval f a ha (algebraMap H (Localization.Away a) x) = 0 at hx
  rw [localizationAwayUnitEval_algebraMap] at hx
  exact (hf (hx.trans (map_zero f).symm)) ▸ map_zero _

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder β]

private theorem blockSchurDiagonal_chart_eval (w : ι → β) (M : Matrix ι ι H)
    (f : H →ₐ[k] R) (ha : IsUnit (f (blockLeadingDetProduct w M))) :
    let L := Localization.Away (blockLeadingDetProduct w M)
    (blockSchurDiagonal w (M.map (algebraMap H L))).map
      (localizationAwayUnitEval f (blockLeadingDetProduct w M) ha) = blockSchurDiagonal w (M.map f) := by
  let a := blockLeadingDetProduct w M
  let L := Localization.Away a
  have hPrefix (i : ι) : IsUnit ((M.map (algebraMap H L)).toBlock
      (fun j => w j < w i) (fun j => w j < w i)).det := by
    let b := (M.toBlock (fun j => w j < w i) (fun j => w j < w i)).det
    have hb : b ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    rw [show ((M.map (algebraMap H L)).toBlock (fun j => w j < w i) (fun j => w j < w i)).det =
      algebraMap H L b from (RingHom.map_det _ _).symm]
    exact IsLocalization.Away.isUnit_of_dvd a hb
  let e := localizationAwayUnitEval f a ha
  change (blockSchurDiagonal w (M.map (algebraMap H L))).map e.toRingHom = _
  rw [blockSchurDiagonal_map w e.toRingHom _ hPrefix]
  exact congrArg (blockSchurDiagonal w) (Matrix.ext fun i j => localizationAwayUnitEval_algebraMap f a ha _)

end Localization

section Kernel

variable {k H Q B R ι β : Type*} [CommRing k] [CommRing H] [CommRing Q] [CommRing B] [CommRing R]
  [Algebra k H] [Algebra k Q] [Algebra k B] [Algebra k R] [Fintype ι] [DecidableEq ι]
  [LinearOrder β]

/-- On any block-diagonal point, every relation of the middle factor
holds. The dense product is encoded by the injective coordinate map `f`. -/
theorem ker_le_ker_of_dense_blockProduct
    (w : ι → β) (U : (Matrix ι ι H)ˣ)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (π : H →ₐ[k] Q) (t : Q →ₐ[k] B) (f : H →ₐ[k] B) (hf : Function.Injective f)
    (hπ : ∀ i j, w i ≠ w j → π (U.val i j) = 0)
    (Mlower Mupper : (Matrix ι ι B)ˣ)
    (hLower : Mlower.val.BlockTriangular (OrderDual.toDual ∘ w))
    (hLowerDiag : ∀ i j, w i = w j → Mlower.val i j = (1 : Matrix ι ι B) i j)
    (hUpper : Mupper.val.BlockTriangular w)
    (hUpperDiag : ∀ i j, w i = w j → Mupper.val i j = (1 : Matrix ι ι B) i j)
    (hProd : U.val.map f = Mlower.val * U.val.map (t.comp π) * Mupper.val)
    (p : H →ₐ[k] R) (hp : ∀ i j, w i ≠ w j → p (U.val i j) = 0) :
    RingHom.ker π.toRingHom ≤ RingHom.ker p.toRingHom := by
  let T := U.map (t.comp π).toRingHom.mapMatrix.toMonoidHom
  let a := blockLeadingDetProduct w U.val
  let L := Localization.Away a
  have hT (i j : ι) (h : w i ≠ w j) : T.val i j = 0 := by
    change t (π (U.val i j)) = 0
    rw [hπ i j h, map_zero]
  have hfUnit : IsUnit (f a) := by
    change IsUnit (f.toRingHom (blockLeadingDetProduct w U.val))
    rw [blockLeadingDetProduct_map, show U.val.map f.toRingHom = U.val.map f from rfl, hProd]
    exact blockLeadingDetProduct_isUnit_of_product w Mlower T Mupper hLower (fun i j h => hT i j (ne_of_gt h)) hUpper
  have hpUnit : IsUnit (p a) := by
    change IsUnit (p.toRingHom (blockLeadingDetProduct w U.val))
    rw [blockLeadingDetProduct_map]
    apply blockLeadingDetProduct_isUnit
    intro i
    exact prefixDet_isUnit_of_blockTriangular w _ (fun j l h => hp j l (ne_of_gt h))
      (Matrix.isUnits_det_units (U.map p.toRingHom.mapMatrix.toMonoidHom)) (w i)
  let e := localizationAwayUnitEval f a hfUnit
  let q := localizationAwayUnitEval p a hpUnit
  have heInj := localizationAwayUnitEval_injective f a hfUnit hf
  let V := blockSchurDiagonal w (U.val.map (algebraMap H L))
  have heV : V.map e = U.val.map (t.comp π) := by
    exact (blockSchurDiagonal_chart_eval w U.val f hfUnit).trans
      ((congrArg (blockSchurDiagonal w) hProd).trans
        (blockSchurDiagonal_mul w Mlower T Mupper hLower hLowerDiag hT hUpper hUpperDiag))
  have hqV : V.map q = U.val.map p :=
    (blockSchurDiagonal_chart_eval w U.val p hpUnit).trans
      (blockSchurDiagonal_eq_self w _ hp)
  let F : MvPolynomial (ι × ι) k →ₐ[k] H := MvPolynomial.aeval fun ij => U.val ij.1 ij.2
  let G : MvPolynomial (ι × ι) k →ₐ[k] L := MvPolynomial.aeval fun ij => V ij.1 ij.2
  have hF : Function.Surjective F := by
    apply (AlgHom.range_eq_top _).mp
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact hGen
  have hcompE : e.comp G = (t.comp π).comp F := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    change e (G (MvPolynomial.X (i, j))) = t (π (F (MvPolynomial.X (i, j))))
    rw [show G (MvPolynomial.X (i, j)) = V i j from MvPolynomial.aeval_X _ _,
      show F (MvPolynomial.X (i, j)) = U.val i j from MvPolynomial.aeval_X _ _]
    exact congrArg (fun M : Matrix ι ι B => M i j) heV
  have hcompQ : q.comp G = p.comp F := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    change q (G (MvPolynomial.X (i, j))) = p (F (MvPolynomial.X (i, j)))
    rw [show G (MvPolynomial.X (i, j)) = V i j from MvPolynomial.aeval_X _ _,
      show F (MvPolynomial.X (i, j)) = U.val i j from MvPolynomial.aeval_X _ _]
    exact congrArg (fun M : Matrix ι ι R => M i j) hqV
  intro x hx
  obtain ⟨P, rfl⟩ := hF x
  change π (F P) = 0 at hx
  have hG : G P = 0 := by
    apply heInj
    rw [map_zero, ← AlgHom.comp_apply, hcompE, AlgHom.comp_apply, AlgHom.comp_apply, hx, map_zero]
  change p (F P) = 0
  rw [← AlgHom.comp_apply, ← hcompQ, AlgHom.comp_apply, hG, map_zero]

end Kernel

section Universal

variable {k H Q B ι β : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H] [CommRing Q]
  [CommRing B] [Algebra k Q] [Algebra k B] [Fintype ι] [DecidableEq ι] [LinearOrder β]

/-- A dense product with a block-diagonal middle subgroup identifies the
scheme-theoretic block centralizer. -/
theorem weightCentralizerIdeal_eq_ker_of_dense_blockProduct
    (w : ι → β) (U : (Matrix ι ι H)ˣ)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (π : H →ₐ[k] Q) (t : Q →ₐ[k] B) (f : H →ₐ[k] B) (hf : Function.Injective f)
    (hπ : ∀ i j, w i ≠ w j → π (U.val i j) = 0)
    (Mlower Mupper : (Matrix ι ι B)ˣ)
    (hLower : Mlower.val.BlockTriangular (OrderDual.toDual ∘ w))
    (hLowerDiag : ∀ i j, w i = w j → Mlower.val i j = (1 : Matrix ι ι B) i j)
    (hUpper : Mupper.val.BlockTriangular w)
    (hUpperDiag : ∀ i j, w i = w j → Mupper.val i j = (1 : Matrix ι ι B) i j)
    (hProd : U.val.map f = Mlower.val * U.val.map (t.comp π) * Mupper.val) :
    weightCentralizerIdeal w U.val = RingHom.ker π.toRingHom := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, j, h, rfl⟩
    exact hπ i j h
  · let J := weightCentralizerIdeal w U.val
    let p := Ideal.Quotient.mkₐ k J
    have hPJ : ∀ i j, w i ≠ w j → p (U.val i j) = 0 := fun i j h =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, j, h, rfl⟩)
    change RingHom.ker π.toRingHom ≤ J
    rw [← show RingHom.ker p.toRingHom = J from Ideal.mk_ker]
    exact ker_le_ker_of_dense_blockProduct w U hGen π t f hf hπ Mlower Mupper hLower hLowerDiag hUpper hUpperDiag hProd p hPJ

end Universal

section QuotientEquivalence

variable {k H Q : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H] [CommRing Q]
  [Bialgebra k Q]

/-- A surjective bialgebra map identifies its actual kernel quotient with its target. -/
def bialgEquiv_quotientOfKerEq {J : Ideal H} (hJ : IsHopfIdeal k J)
    (π : H →ₐc[k] Q) (hSurj : Function.Surjective π) (hKer : J = RingHom.ker (π : H →ₐ[k] Q).toRingHom) :
    letI := hJ.quotientHopf
    (H ⧸ J) ≃ₐc[k] Q := by
  letI := hJ.quotientHopf
  let p : H →ₐc[k] H ⧸ J := hJ.quotientBialgHom
  let F : (H ⧸ J) →ₐ[k] Q := Ideal.Quotient.liftₐ J (π : H →ₐ[k] Q) fun a ha =>
    RingHom.mem_ker.mp (hKer ▸ ha)
  have hF (a : H) : F (p a) = π a := rfl
  have hp : Function.Surjective p := Ideal.Quotient.mkₐ_surjective k J
  let e : (H ⧸ J) ≃ₐ[k] Q := AlgEquiv.ofBijective F ⟨by
    rw [injective_iff_map_eq_zero F]
    intro z hz
    obtain ⟨a, rfl⟩ := hp z
    rw [hF] at hz
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hKer]
    exact RingHom.mem_ker.mpr hz,
    fun q => by obtain ⟨a, ha⟩ := hSurj q; exact ⟨p a, (hF a).trans ha⟩⟩
  have hCounit : (Coalgebra.counit (R := k)).comp F.toLinearMap = Coalgebra.counit := by
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := hp z
    change Coalgebra.counit (R := k) (F (p a)) = Coalgebra.counit (R := k) (p a)
    rw [hF, CoalgHomClass.counit_comp_apply π, CoalgHomClass.counit_comp_apply p]
  have hComul : (TensorProduct.map F.toLinearMap F.toLinearMap).comp (Coalgebra.comul (R := k)) =
      (Coalgebra.comul (R := k)).comp F.toLinearMap := by
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := hp z
    change TensorProduct.map F.toLinearMap F.toLinearMap (Coalgebra.comul (R := k) (p a)) =
      Coalgebra.comul (R := k) (F (p a))
    have hFp : F.toLinearMap.comp (p : H →ₗ[k] H ⧸ J) = (π : H →ₗ[k] Q) := LinearMap.ext hF
    rw [hF, ← CoalgHomClass.map_comp_comul_apply p, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hFp]
    exact CoalgHomClass.map_comp_comul_apply π a
  let f := BialgHom.ofAlgHom F hCounit hComul
  exact { toCoalgEquiv := { f.toCoalgHom, e.toLinearEquiv with }, map_mul' := map_mul F }

@[simp]
theorem bialgEquiv_quotientOfKerEq_mk {J : Ideal H} (hJ : IsHopfIdeal k J)
    (π : H →ₐc[k] Q) (hSurj : Function.Surjective π) (hKer : J = RingHom.ker (π : H →ₐ[k] Q).toRingHom)
    (a : H) :
    bialgEquiv_quotientOfKerEq hJ π hSurj hKer (Ideal.Quotient.mk J a) = π a := rfl

end QuotientEquivalence

end WideE
