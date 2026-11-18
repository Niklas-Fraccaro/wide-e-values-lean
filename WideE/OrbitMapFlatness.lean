import WideE.EquivariantOrbitFlatness
import WideE.HopfSmoothLocus
import WideE.PuncturedOrbitEvaluation

/-!
# Translations and flatness of the scaled orbit map

The map to the affine cone sends a matrix point and a Laurent unit to
the corresponding scaled vector. The source translations induce
automorphisms of the cone algebra and act transitively on closed points.
-/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

open LaurentPolynomial

section LaurentTranslations

variable {k H A : Type*} [Field k] [CommRing H] [Algebra k H]
  [CommRing A] [Algebra k A]

/-- A Laurent algebra homomorphism is determined on coefficients and the invertible variable. -/
theorem laurentAlgHom_ext_C_T (f g : LaurentPolynomial H →ₐ[k] A)
    (hC : ∀ a : H, f (C a) = g (C a)) (hT : f (T 1) = g (T 1)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial H))
  apply Polynomial.ringHom_ext
  · intro a
    simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_C] using hC a
  · simpa only [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      Polynomial.toLaurent_X] using hT

private def laurentCoordinateUnit (H : Type*) [CommRing H] : (LaurentPolynomial H)ˣ :=
  (LaurentPolynomial.isUnit_T (R := H) 1).unit

@[simp]
private theorem laurentCoordinateUnit_val :
    (laurentCoordinateUnit H : LaurentPolynomial H) = T 1 :=
  (LaurentPolynomial.isUnit_T (R := H) 1).unit_spec

private def laurentTranslateHom (f : H →ₐ[k] H) (c : kˣ) :
    LaurentPolynomial H →ₐ[k] LaurentPolynomial H where
  toRingHom := LaurentPolynomial.eval₂ (C.comp f.toRingHom)
    (c.map (algebraMap k (LaurentPolynomial H)).toMonoidHom * laurentCoordinateUnit H)
  commutes' r := by
    change LaurentPolynomial.eval₂ (C.comp f.toRingHom)
      (c.map (algebraMap k (LaurentPolynomial H)).toMonoidHom * laurentCoordinateUnit H)
      (C (algebraMap k H r)) = C (algebraMap k H r)
    rw [LaurentPolynomial.eval₂_C, RingHom.comp_apply]
    exact congrArg C (f.commutes r)

@[simp]
private theorem laurentTranslateHom_C (f : H →ₐ[k] H) (c : kˣ) (a : H) :
    laurentTranslateHom f c (C a) = C (f a) :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp]
private theorem laurentTranslateHom_T (f : H →ₐ[k] H) (c : kˣ) :
    laurentTranslateHom f c (T 1) = C (algebraMap k H (c : k)) * T 1 := by
  change LaurentPolynomial.eval₂ (C.comp f.toRingHom)
    (c.map (algebraMap k (LaurentPolynomial H)).toMonoidHom * laurentCoordinateUnit H)
    (T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one, Units.val_mul, laurentCoordinateUnit_val]
  rfl

private theorem laurentTranslateHom_comp (f g : H →ₐ[k] H) (c d : kˣ) :
    (laurentTranslateHom f c).comp (laurentTranslateHom g d) =
      laurentTranslateHom (f.comp g) (c * d) := by
  apply laurentAlgHom_ext_C_T
  · intro a
    simp only [AlgHom.comp_apply, laurentTranslateHom_C]
  · simp only [AlgHom.comp_apply, laurentTranslateHom_T, map_mul, laurentTranslateHom_C,
      AlgHom.commutes, Units.val_mul]
    ac_rfl

private theorem laurentTranslateHom_one :
    laurentTranslateHom (AlgHom.id k H) 1 = AlgHom.id k (LaurentPolynomial H) := by
  apply laurentAlgHom_ext_C_T
  · intro a
    simp only [laurentTranslateHom_C, AlgHom.id_apply]
  · simp only [laurentTranslateHom_T, Units.val_one, map_one, one_mul, AlgHom.id_apply]

/-- Simultaneous coefficient automorphism and multiplication of the Laurent
variable by a scalar unit. -/
def laurentTranslation (e : H ≃ₐ[k] H) (c : kˣ) :
    LaurentPolynomial H ≃ₐ[k] LaurentPolynomial H :=
  AlgEquiv.ofAlgHom (laurentTranslateHom e.toAlgHom c)
    (laurentTranslateHom e.symm.toAlgHom c⁻¹)
    (by rw [laurentTranslateHom_comp, mul_inv_cancel,
      show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id k H from AlgHom.ext e.apply_symm_apply,
      laurentTranslateHom_one])
    (by rw [laurentTranslateHom_comp, inv_mul_cancel,
      show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k H from AlgHom.ext e.symm_apply_apply,
      laurentTranslateHom_one])

@[simp]
theorem laurentTranslation_C (e : H ≃ₐ[k] H) (c : kˣ) (a : H) :
    laurentTranslation e c (C a) = C (e a) :=
  laurentTranslateHom_C _ _ _

@[simp]
theorem laurentTranslation_T (e : H ≃ₐ[k] H) (c : kˣ) :
    laurentTranslation e c (T 1) = C (algebraMap k H (c : k)) * T 1 :=
  laurentTranslateHom_T _ _

end LaurentTranslations

section OrbitTranslations

variable {k H ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem hopfTranslation_matrix_entry (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (p : H →ₐ[k] k) (i j : ι) :
    hopfTranslation p (U i j) = ∑ l, algebraMap k H (p (U i l)) * U l j := by
  change Algebra.TensorProduct.lid k H (Algebra.TensorProduct.map p (AlgHom.id k H)
    (Coalgebra.comul (R := k) (U i j))) = _
  rw [hU, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply,
    Algebra.smul_def]

omit [DecidableEq ι] in
private theorem hopfTranslation_orbitVector (U : Matrix ι ι H)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U i j) = ∑ l, U i l ⊗ₜ[k] U l j)
    (p : H →ₐ[k] k) (v : ι → k) (i : ι) :
    hopfTranslation p (orbitVector U v i) =
      ∑ j, algebraMap k H (p (U i j)) * orbitVector U v j := by
  have hM : U.map (hopfTranslation p).toRingEquiv.toRingHom =
      (U.map p.toRingHom).map (algebraMap k H) * U := by
    apply Matrix.ext
    intro i j
    exact hopfTranslation_matrix_entry U hU p i j
  have hC : (hopfTranslation p).toRingEquiv.toRingHom ∘ (algebraMap k H ∘ v) =
      algebraMap k H ∘ v := funext fun j => (hopfTranslation p).commutes (v j)
  change (hopfTranslation p).toRingEquiv.toRingHom ((U *ᵥ (algebraMap k H ∘ v)) i) = _
  rw [RingHom.map_mulVec, hM, hC, ← Matrix.mulVec_mulVec]
  rfl

private def orbitTranslationMatrix (U : (Matrix ι ι H)ˣ) (p : H →ₐ[k] k) (c : kˣ) :
    (Matrix ι ι k)ˣ :=
  c.map (Matrix.scalar ι).toMonoidHom * U.map p.toRingHom.mapMatrix.toMonoidHom

private theorem orbitTranslationMatrix_val (U : (Matrix ι ι H)ˣ)
    (p : H →ₐ[k] k) (c : kˣ) :
    (orbitTranslationMatrix U p c).val = (c : k) • U.val.map p.toRingHom := by
  change Matrix.scalar ι (c : k) * U.val.map p.toRingHom = _
  rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]

/-- Translation by a matrix point and a scalar unit is substitution on the
variables of the orbit cone. -/
private theorem laurentTranslation_comp_orbitEvaluation
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) (f : MvPolynomial ι k →ₐ[k] LaurentPolynomial H)
    (hf : ∀ i, f (MvPolynomial.X i) = C (orbitVector U.val v i) * T 1)
    (p : H →ₐ[k] k) (c : kˣ) :
    (laurentTranslation (hopfTranslation p) c).toAlgHom.comp f =
      f.comp (matrixPolynomialSubstitution (orbitTranslationMatrix U p c).val) := by
  apply MvPolynomial.algHom_ext
  intro i
  have hCoeffs :
      (((orbitTranslationMatrix U p c).val).map MvPolynomial.C).map f.toRingHom =
        (orbitTranslationMatrix U p c).val.map (algebraMap k (LaurentPolynomial H)) :=
    Matrix.ext fun j l => f.commutes _
  have hVars : f.toRingHom ∘ (MvPolynomial.X : ι → MvPolynomial ι k) =
      fun j => C (orbitVector U.val v j) * T 1 := funext hf
  change laurentTranslation (hopfTranslation p) c (f (MvPolynomial.X i)) =
    f.toRingHom (matrixPolynomialSubstitution (orbitTranslationMatrix U p c).val (MvPolynomial.X i))
  rw [hf, map_mul, laurentTranslation_C, laurentTranslation_T, hopfTranslation_orbitVector U.val hU,
    matrixPolynomialSubstitution_X, RingHom.map_mulVec, hCoeffs, hVars,
    orbitTranslationMatrix_val]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Function.comp_apply, map_sum, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  change C (algebraMap k H (p (U.val i j))) * C (orbitVector U.val v j) *
      (C (algebraMap k H (c : k)) * T 1) =
    (C (algebraMap k H (c : k)) * C (algebraMap k H (p (U.val i j)))) *
      (C (orbitVector U.val v j) * T 1)
  ac_rfl

/-- The affine coordinate algebra of the orbit cone. -/
abbrev OrbitConeAlgebra (U : Matrix ι ι H) (v : ι → k) :=
  MvPolynomial ι k ⧸ orbitConeIdeal U v

abbrev orbitConeCoordinate (U : Matrix ι ι H) (v : ι → k) (i : ι) :
    OrbitConeAlgebra U v := Ideal.Quotient.mk (orbitConeIdeal U v) (MvPolynomial.X i)

/-- The orbit morphism on its actual coordinate rings. -/
def orbitConeMap (U : Matrix ι ι H) (v : ι → k) : OrbitConeAlgebra U v →ₐ[k] LaurentPolynomial H :=
  Ideal.Quotient.liftₐ (orbitConeIdeal U v) (puncturedOrbitEvaluation U v)
    (fun _ h => RingHom.mem_ker.mp (puncturedOrbitEvaluation_ker U v ▸ h))

omit [DecidableEq ι] in
theorem orbitConeMap_comp_quotient (U : Matrix ι ι H) (v : ι → k) :
    (orbitConeMap U v).comp (Ideal.Quotient.mkₐ k (orbitConeIdeal U v)) =
      puncturedOrbitEvaluation U v :=
  Ideal.Quotient.liftₐ_comp _ _ _

omit [DecidableEq ι] in
@[simp]
theorem orbitConeMap_coordinate (U : Matrix ι ι H) (v : ι → k) (i : ι) :
    orbitConeMap U v (orbitConeCoordinate U v i) = C (orbitVector U v i) * T 1 := by
  rw [← puncturedOrbitEvaluation_X]
  exact DFunLike.congr_fun (orbitConeMap_comp_quotient U v) (MvPolynomial.X i)

omit [DecidableEq ι] in
theorem orbitConeMap_injective (U : Matrix ι ι H) (v : ι → k) :
    Function.Injective (orbitConeMap U v) := by
  apply (injective_iff_map_eq_zero (orbitConeMap U v)).mpr
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (orbitConeIdeal U v) x
  change (orbitConeMap U v).comp (Ideal.Quotient.mkₐ k (orbitConeIdeal U v)) p = 0 at hx
  rw [orbitConeMap_comp_quotient] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (puncturedOrbitEvaluation_ker U v ▸ RingHom.mem_ker.mpr hx)

private theorem matrixPolynomialSubstitution_unit_surjective (M : (Matrix ι ι k)ˣ) :
    Function.Surjective (matrixPolynomialSubstitution M.val) := by
  have h : (matrixPolynomialSubstitution M.val).comp (matrixPolynomialSubstitution (M⁻¹).val) =
      AlgHom.id k (MvPolynomial ι k) := by
    rw [← matrixPolynomialSubstitution_mul, Units.inv_mul]
    apply MvPolynomial.algHom_ext
    intro i
    rw [matrixPolynomialSubstitution_X, AlgHom.id_apply,
      Matrix.map_one _ (map_zero MvPolynomial.C) (map_one MvPolynomial.C), Matrix.one_mulVec]
  exact Function.RightInverse.surjective (fun x => DFunLike.congr_fun h x)

private theorem exists_orbitConeMap_translation
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) (p : H →ₐ[k] k) (c : kˣ) :
    ∃ e : OrbitConeAlgebra U.val v ≃ₐ[k] OrbitConeAlgebra U.val v,
      (laurentTranslation (hopfTranslation p) c).toAlgHom.comp (orbitConeMap U.val v) =
        (orbitConeMap U.val v).comp e.toAlgHom := by
  let I := orbitConeIdeal U.val v
  let F := orbitConeMap U.val v
  let π := Ideal.Quotient.mkₐ k I
  let M := orbitTranslationMatrix U p c
  let a := matrixPolynomialSubstitution M.val
  let b := laurentTranslation (hopfTranslation p) c
  have hF : F.comp π = puncturedOrbitEvaluation U.val v := orbitConeMap_comp_quotient _ _
  have hE : b.toAlgHom.comp (F.comp π) = (F.comp π).comp a := by
    rw [hF]
    exact laurentTranslation_comp_orbitEvaluation U hU v _
      (puncturedOrbitEvaluation_X U.val v) p c
  have hkill (x : MvPolynomial ι k) (hx : x ∈ I) : (π.comp a) x = 0 := by
    apply orbitConeMap_injective U.val v
    have hZero : π x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
    have h := DFunLike.congr_fun hE x
    change b (F (π x)) = F (π (a x)) at h
    change F (π (a x)) = F 0
    rw [← h, hZero, map_zero, map_zero]
  let e := Ideal.Quotient.liftₐ I (π.comp a) hkill
  have hq : e.comp π = π.comp a := Ideal.Quotient.liftₐ_comp _ _ _
  have he (x : OrbitConeAlgebra U.val v) : b (F x) = F (e x) := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I x
    rw [show e (π s) = π (a s) from DFunLike.congr_fun hq s]
    exact DFunLike.congr_fun hE s
  have heInjective : Function.Injective e := by
    intro x y hxy
    apply orbitConeMap_injective U.val v
    apply b.injective
    rw [he, he, hxy]
  have heSurjective : Function.Surjective e := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I x
    obtain ⟨s, rfl⟩ := matrixPolynomialSubstitution_unit_surjective M r
    exact ⟨π s, DFunLike.congr_fun hq s⟩
  exact ⟨AlgEquiv.ofBijective e ⟨heInjective, heSurjective⟩, AlgHom.ext he⟩

/-- A point of the group and a scalar unit give a point of the Laurent
coordinate algebra over the same coefficient algebra. -/
abbrev laurentOrbitPoint {A : Type*} [CommRing A] [Algebra k A]
    (p : H →ₐ[k] A) (c : Aˣ) : LaurentPolynomial H →ₐ[k] A :=
  evalLaurentPoint p c

@[simp]
theorem laurentOrbitPoint_C {A : Type*} [CommRing A] [Algebra k A]
    (p : H →ₐ[k] A) (c : Aˣ) (a : H) :
    laurentOrbitPoint p c (C a) = p a :=
  evalLaurentPoint_C p c a

@[simp]
theorem laurentOrbitPoint_T {A : Type*} [CommRing A] [Algebra k A]
    (p : H →ₐ[k] A) (c : Aˣ) :
    laurentOrbitPoint p c (T 1) = (c : A) :=
  evalLaurentPoint_T_one p c

omit [DecidableEq ι] in
/-- The coordinates of a point of the cone satisfy its defining ideal. -/
theorem orbitConePoint_vanishes (U : Matrix ι ι H) (v : ι → k)
    (p : OrbitConeAlgebra U v →ₐ[k] k) :
    ∀ P ∈ orbitConeIdeal U v, MvPolynomial.aeval (p ∘ orbitConeCoordinate U v) P = 0 := by
  let I := orbitConeIdeal U v
  let π := Ideal.Quotient.mkₐ k I
  let x := p ∘ orbitConeCoordinate U v
  have hx : MvPolynomial.aeval x = p.comp π := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (MvPolynomial.aeval_X x j).trans rfl
  intro P hP
  rw [hx, AlgHom.comp_apply, show π P = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hP, map_zero]

omit [DecidableEq ι] in
/-- A scaled group point lifting the cone coordinates lifts the point on the
whole cone algebra. -/
theorem orbitConeMap_lift_of_coordinates (U : Matrix ι ι H) (v : ι → k)
    (p : OrbitConeAlgebra U v →ₐ[k] k) (q : H →ₐ[k] k) (c : kˣ)
    (hEq : p ∘ orbitConeCoordinate U v = (c : k) • (U.map q.toRingHom *ᵥ v)) :
    (laurentOrbitPoint q c).comp (orbitConeMap U v) = p := by
  let I := orbitConeIdeal U v
  let π := Ideal.Quotient.mkₐ k I
  let x := p ∘ orbitConeCoordinate U v
  have hComp : ((laurentOrbitPoint q c).comp (orbitConeMap U v)).comp π = p.comp π := by
    apply MvPolynomial.algHom_ext
    intro j
    change laurentOrbitPoint q c (orbitConeMap U v (orbitConeCoordinate U v j)) = x j
    rw [orbitConeMap_coordinate, map_mul, laurentOrbitPoint_C, laurentOrbitPoint_T, mul_comm]
    have hxj : x j = (c : k) * (U.map q.toRingHom *ᵥ v) j := congrFun hEq j
    rw [hxj]
    congr 1
    change q.toRingHom ((U *ᵥ (algebraMap k H ∘ v)) j) = _
    rw [RingHom.map_mulVec,
      show q.toRingHom ∘ (algebraMap k H ∘ v) = v from funext fun l => q.commutes (v l)]
  apply AlgHom.ext
  intro z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mkₐ_surjective k I z
  exact DFunLike.congr_fun hComp P

private def laurentOrbitPoint_coeff (p : LaurentPolynomial H →ₐ[k] k) : H →ₐ[k] k :=
  p.comp (IsScalarTower.toAlgHom k H (LaurentPolynomial H))

private def laurentOrbitPoint_unit (p : LaurentPolynomial H →ₐ[k] k) : kˣ :=
  (laurentCoordinateUnit H).map p.toRingHom.toMonoidHom

private def augmentationTranslation (p : LaurentPolynomial H →ₐ[k] k) :
    LaurentPolynomial H ≃ₐ[k] LaurentPolynomial H :=
  laurentTranslation (hopfTranslation (laurentOrbitPoint_coeff p)) (laurentOrbitPoint_unit p)

private theorem augmentationTranslation_point (p : LaurentPolynomial H →ₐ[k] k) :
    (laurentOrbitPoint (Bialgebra.counitAlgHom k H) 1).comp (augmentationTranslation p).toAlgHom = p := by
  apply laurentAlgHom_ext_C_T
  · intro a
    change laurentOrbitPoint (Bialgebra.counitAlgHom k H) 1
      (laurentTranslation (hopfTranslation (laurentOrbitPoint_coeff p)) (laurentOrbitPoint_unit p)
        (C a)) = p (C a)
    rw [laurentTranslation_C, laurentOrbitPoint_C, hopfTranslation_counit]
    rfl
  · change laurentOrbitPoint (Bialgebra.counitAlgHom k H) 1
      (laurentTranslation (hopfTranslation (laurentOrbitPoint_coeff p)) (laurentOrbitPoint_unit p)
        (T 1)) = p (T 1)
    rw [laurentTranslation_T, map_mul, laurentOrbitPoint_C, laurentOrbitPoint_T, Units.val_one,
      mul_one, AlgHom.commutes]
    change p (laurentCoordinateUnit H : LaurentPolynomial H) = p (T 1)
    rw [laurentCoordinateUnit_val]

private theorem exists_orbitConeMap_point_translation
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) (p q : LaurentPolynomial H →ₐ[k] k) :
    ∃ (eA : OrbitConeAlgebra U.val v ≃ₐ[k] OrbitConeAlgebra U.val v)
      (eB : LaurentPolynomial H ≃ₐ[k] LaurentPolynomial H),
      eB.toAlgHom.comp (orbitConeMap U.val v) = (orbitConeMap U.val v).comp eA.toAlgHom ∧
      p.comp eB.toAlgHom = q := by
  obtain ⟨pA, hpA⟩ := exists_orbitConeMap_translation U hU v
    (laurentOrbitPoint_coeff p) (laurentOrbitPoint_unit p)
  obtain ⟨qA, hqA⟩ := exists_orbitConeMap_translation U hU v
    (laurentOrbitPoint_coeff q) (laurentOrbitPoint_unit q)
  let F := orbitConeMap U.val v
  let pB := augmentationTranslation p
  let qB := augmentationTranslation q
  refine ⟨qA.trans pA.symm, qB.trans pB.symm, ?_, ?_⟩
  · apply AlgHom.ext
    intro x
    change pB.symm (qB (F x)) = F (pA.symm (qA x))
    apply pB.injective
    rw [AlgEquiv.apply_symm_apply,
      show qB (F x) = F (qA x) from DFunLike.congr_fun hqA x,
      show pB (F (pA.symm (qA x))) = F (pA (pA.symm (qA x))) from
        DFunLike.congr_fun hpA _, AlgEquiv.apply_symm_apply]
  · apply AlgHom.ext
    intro z
    change p (pB.symm (qB z)) = q z
    rw [← augmentationTranslation_point p, AlgHom.comp_apply]
    change laurentOrbitPoint (Bialgebra.counitAlgHom k H) 1 (pB (pB.symm (qB z))) = q z
    rw [AlgEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (augmentationTranslation_point q) z

end OrbitTranslations

section Flatness

universe u

variable {k H ι : Type u} [Field k] [IsAlgClosed k] [CommRing H] [IsDomain H]
  [HopfAlgebra k H] [Algebra.FiniteType k H] [Fintype ι] [DecidableEq ι]

/-- The scaled orbit map is flat over its affine closure. -/
theorem orbitConeMap_flat
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) :
    (orbitConeMap U.val v).toRingHom.Flat := by
  letI : IsDomain (OrbitConeAlgebra U.val v) :=
    Function.Injective.isDomain (orbitConeMap U.val v) (orbitConeMap_injective U.val v)
  letI : Algebra.FiniteType k (LaurentPolynomial H) := laurentPolynomial_finiteType
  exact flat_of_transitive_closedPoints (orbitConeMap U.val v)
    (orbitConeMap_injective U.val v) (exists_orbitConeMap_point_translation U hU v)

/-- A chart of the cone where its rational points lie in the orbit is
faithfully flat under the scaled orbit morphism. -/
theorem orbitConeMap_faithfullyFlat_away
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (v : ι → k) (i : ι)
    (hOrbit : ∀ x : ι → k, x i ≠ 0 →
      (∀ P ∈ orbitConeIdeal U.val v, MvPolynomial.aeval x P = 0) →
      ∃ (p : H →ₐ[k] k) (c : kˣ), x = (c : k) • (U.val.map p.toRingHom *ᵥ v)) :
    let a := orbitConeCoordinate U.val v i
    let F := orbitConeMap U.val v
    letI : Algebra (Localization.Away a) (Localization.Away (F a)) :=
      (localizationAwayAlgHom F a).toRingHom.toAlgebra
    Module.FaithfullyFlat (Localization.Away a) (Localization.Away (F a)) := by
  letI : Algebra.FiniteType k (OrbitConeAlgebra U.val v) :=
    Algebra.FiniteType.quotient k (orbitConeIdeal U.val v)
  apply faithfullyFlat_localizationAway_of_lift_kPoints _ (orbitConeMap_flat U hU v) _
  intro p hp
  obtain ⟨q, c, hEq⟩ := hOrbit _ hp (orbitConePoint_vanishes U.val v p)
  exact ⟨laurentOrbitPoint q c, orbitConeMap_lift_of_coordinates U.val v p q c hEq⟩

end Flatness

end WideE
