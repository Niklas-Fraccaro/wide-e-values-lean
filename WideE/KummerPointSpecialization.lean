import WideE.TorsorReduction
import AlgebraicPoint
import Mathlib.Analysis.Complex.Polynomial.Basic
import WideE.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Laurent-valued points over an extension of an algebraically closed
constant field specialize to Laurent-valued points over the field itself. -/

noncomputable section

open LaurentPolynomial
open scoped TensorProduct

namespace WideE

open StrictEUnit

set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 70000

private def laurentCoordinateUnit (A : Type*) [CommRing A] : (LaurentPolynomial A)ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add, add_neg_cancel, T_zero]
  inv_val := by rw [← T_add, neg_add_cancel, T_zero]

private theorem laurentCoordinateUnit_zpow {A : Type*} [CommRing A] (n : ℤ) :
    ((laurentCoordinateUnit A ^ n : (LaurentPolynomial A)ˣ) : LaurentPolynomial A) = T n := by
  cases n with
  | ofNat n =>
    change ((laurentCoordinateUnit A ^ ((n : ℕ) : ℤ) : (LaurentPolynomial A)ˣ) :
      LaurentPolynomial A) = T (Int.ofNat n)
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
    change (T 1 : LaurentPolynomial A) ^ n = T (Int.ofNat n)
    rw [T_pow, mul_one]
    rfl
  | negSucc n =>
    change ((laurentCoordinateUnit A ^ (-((n + 1 : ℕ) : ℤ)) : (LaurentPolynomial A)ˣ) :
      LaurentPolynomial A) = T (Int.negSucc n)
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    change (T (-1) : LaurentPolynomial A) ^ (n + 1) = T (Int.negSucc n)
    rw [T_pow, mul_neg_one]
    rfl

/-- Apply a ring homomorphism to the finite coefficients of a Laurent polynomial. -/
def mapLaurentCoefficients {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) :
    LaurentPolynomial A →+* LaurentPolynomial B :=
  LaurentPolynomial.eval₂ (C.comp f) (laurentCoordinateUnit B)

@[simp] theorem mapLaurentCoefficients_C {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (a : A) : mapLaurentCoefficients f (C a) = C (f a) :=
  LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem mapLaurentCoefficients_T {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℤ) : mapLaurentCoefficients f (T n) = T n := by
  rw [mapLaurentCoefficients, LaurentPolynomial.eval₂_T, laurentCoordinateUnit_zpow]

@[simp] theorem mapLaurentCoefficients_coeff {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    mapLaurentCoefficients f p n = f (p n) := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add]
    change mapLaurentCoefficients f a n + mapLaurentCoefficients f b n = f (a n + b n)
    rw [ha, hb, map_add]
  | C_mul_T m a =>
    rw [map_mul, mapLaurentCoefficients_C, mapLaurentCoefficients_T, ← single_eq_C_mul_T,
      ← single_eq_C_mul_T]
    by_cases h : m = n
    · subst n
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne h, map_zero]

/-- The target of a Kummer pullback after enlarging the constant ring. -/
def KummerCoefficientExtension (K A : Type*) [CommRing K] [CommRing A] (_q : ℕ) :=
  LaurentPolynomial A

instance kummerCoefficientExtensionCommRing {K A : Type*} [CommRing K] [CommRing A] {q : ℕ} :
    CommRing (KummerCoefficientExtension K A q) :=
  inferInstanceAs (CommRing (LaurentPolynomial A))

instance kummerCoefficientExtensionAlgebra {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] {q : ℕ} : Algebra (LaurentPolynomial K) (KummerCoefficientExtension K A q) :=
  ((mapLaurentCoefficients (algebraMap K A)).comp (kummer K q)).toAlgebra

def KummerCoefficientExtension.toLaurent {K A : Type*} [CommRing K] [CommRing A] {q : ℕ} :
    KummerCoefficientExtension K A q ≃+* LaurentPolynomial A :=
  RingEquiv.refl _

theorem KummerCoefficientExtension.algebraMap_apply {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] {q : ℕ} (p : LaurentPolynomial K) :
    KummerCoefficientExtension.toLaurent (algebraMap (LaurentPolynomial K)
      (KummerCoefficientExtension K A q) p) =
      mapLaurentCoefficients (algebraMap K A) (kummer K q p) := rfl

/-- A homomorphism of constant algebras induces a homomorphism between the
Kummer algebras with the same exponent. -/
def kummerCoefficientExtensionMap {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (q : ℕ) (f : A →ₐ[K] B) :
    KummerCoefficientExtension K A q →ₐ[LaurentPolynomial K] KummerCoefficientExtension K B q where
  toRingHom := mapLaurentCoefficients f.toRingHom
  commutes' p := by
    apply KummerCoefficientExtension.toLaurent.injective
    ext n
    change mapLaurentCoefficients f.toRingHom (mapLaurentCoefficients (algebraMap K A) (kummer K q p)) n =
      mapLaurentCoefficients (algebraMap K B) (kummer K q p) n
    rw [mapLaurentCoefficients_coeff, mapLaurentCoefficients_coeff, mapLaurentCoefficients_coeff]
    exact f.commutes _

/-- With the original constants the coefficient extension is the ordinary
Kummer target. -/
def kummerCoefficientExtensionSelf {K : Type*} [CommRing K] (q : ℕ) :
    KummerCoefficientExtension K K q →ₐ[LaurentPolynomial K] KummerExtension K q where
  toRingHom := RingHom.id _
  commutes' p := by
    apply (KummerExtension.toLaurent K q).injective
    ext n
    change mapLaurentCoefficients (algebraMap K K) (kummer K q p) n = kummer K q p n
    rw [mapLaurentCoefficients_coeff]
    rfl

private theorem kummerCoefficientExtensionMap_injective {K A B : Type*}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (q : ℕ) (f : A →ₐ[K] B) (hf : Function.Injective f) :
    Function.Injective (kummerCoefficientExtensionMap q f) := by
  intro a b h
  apply KummerCoefficientExtension.toLaurent.injective
  ext n
  apply hf
  have h' := congrArg (fun z : KummerCoefficientExtension K B q =>
    KummerCoefficientExtension.toLaurent z n) h
  change mapLaurentCoefficients f.toRingHom (KummerCoefficientExtension.toLaurent a) n =
    mapLaurentCoefficients f.toRingHom (KummerCoefficientExtension.toLaurent b) n at h'
  simpa only [mapLaurentCoefficients_coeff, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h'

private theorem mem_kummerCoefficientExtensionMap_range {K A : Type*} [CommRing K] [CommRing A]
    [Algebra K A] (q : ℕ) (D : Subalgebra K A) (z : KummerCoefficientExtension K A q)
    (hz : ∀ n : ℤ, KummerCoefficientExtension.toLaurent z n ∈ D) :
    z ∈ (kummerCoefficientExtensionMap q D.val).range := by
  let p := KummerCoefficientExtension.toLaurent z
  let p' : LaurentPolynomial D :=
    Finsupp.onFinset p.support (fun n => ⟨p n, hz n⟩)
      (fun n hn => Finsupp.mem_support_iff.mpr (fun h => hn (Subtype.ext h)))
  refine ⟨KummerCoefficientExtension.toLaurent.symm p', ?_⟩
  apply KummerCoefficientExtension.toLaurent.injective
  ext n
  change mapLaurentCoefficients D.val.toRingHom p' n = p n
  rw [mapLaurentCoefficients_coeff]
  rfl

private theorem exists_finiteTypeKummerFactor
    {K A S : Type*} [Field K] [CommRing A] [Algebra K A]
    [CommRing S] [Algebra (LaurentPolynomial K) S] [Algebra.FiniteType (LaurentPolynomial K) S]
    (q : ℕ) (f : S →ₐ[LaurentPolynomial K] KummerCoefficientExtension K A q) :
    ∃ D : Subalgebra K A, Algebra.FiniteType K D ∧
      ∃ g : S →ₐ[LaurentPolynomial K] KummerCoefficientExtension K D q,
        ∀ x, kummerCoefficientExtensionMap q D.val (g x) = f x := by
  classical
  let R := LaurentPolynomial K
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := R) (A := S))
  let p (x : S) := KummerCoefficientExtension.toLaurent (f x)
  let c : Finset A := s.biUnion (fun x => (p x).support.image (p x))
  let D : Subalgebra K A := Algebra.adjoin K (c : Set A)
  letI : Algebra.FiniteType K D := (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_adjoin_finset c)
  have hc (x : S) (hx : x ∈ s) (n : ℤ) : p x n ∈ D := by
    by_cases hn : n ∈ (p x).support
    · apply Algebra.subset_adjoin
      exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨n, hn, rfl⟩⟩
    · rw [Finsupp.not_mem_support_iff.mp hn]
      exact D.zero_mem
  let j := kummerCoefficientExtensionMap q D.val
  have hj : Function.Injective j :=
    kummerCoefficientExtensionMap_injective q D.val Subtype.val_injective
  have hs' : Algebra.adjoin R (s : Set S) ≤ j.range.comap f := by
    apply Algebra.adjoin_le
    intro x hx
    exact mem_kummerCoefficientExtensionMap_range q D (f x) (hc x hx)
  have hAll (x : S) : f x ∈ j.range := by
    apply hs'
    rw [hs]
    exact Set.mem_univ x
  let e := AlgEquiv.ofInjective j hj
  let f' := f.codRestrict j.range hAll
  let g := e.symm.toAlgHom.comp f'
  refine ⟨D, inferInstance, g, fun x => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply (f' x))

/-- A Laurent point after enlarging constants descends over an algebraically
closed field. Only the finitely many coefficients of finitely many generator
images are needed for the Nullstellensatz. -/
theorem nonempty_kummerPoint_of_coefficientExtension
    {K A S : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    [CommRing S] [Algebra (LaurentPolynomial K) S] [Algebra.FiniteType (LaurentPolynomial K) S]
    (q : ℕ) (f : S →ₐ[LaurentPolynomial K] KummerCoefficientExtension K A q) :
    Nonempty (S →ₐ[LaurentPolynomial K] KummerExtension K q) := by
  obtain ⟨D, hD, g, _⟩ := exists_finiteTypeKummerFactor q f
  letI := hD
  obtain ⟨a⟩ := StrictEUnit.nonempty_algebraic_point (k := K) (S := D)
  exact ⟨(kummerCoefficientExtensionSelf q).comp ((kummerCoefficientExtensionMap q a).comp g)⟩

@[simp] theorem evalAtOne_mapLaurentCoefficients
    {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) :
    evalAtOne B (mapLaurentCoefficients f p) = f (evalAtOne A p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n c => simp

/-- Coefficient specialization preserves any prescribed values at one that
are already in the original constant field. -/
theorem exists_kummerPoint_preserving_evaluation
    {K A S : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Nontrivial A] [Algebra K A]
    [CommRing S] [Algebra (LaurentPolynomial K) S] [Algebra.FiniteType (LaurentPolynomial K) S]
    (q : ℕ) (f : S →ₐ[LaurentPolynomial K] KummerCoefficientExtension K A q)
    (e : S → K)
    (he : ∀ x, evalAtOne A (KummerCoefficientExtension.toLaurent (f x)) = algebraMap K A (e x)) :
    ∃ g : S →ₐ[LaurentPolynomial K] KummerExtension K q,
      ∀ x, evalAtOne K (KummerExtension.toLaurent K q (g x)) = e x := by
  obtain ⟨D, hD, g, hg⟩ := exists_finiteTypeKummerFactor q f
  letI := hD
  obtain ⟨a⟩ := StrictEUnit.nonempty_algebraic_point (k := K) (S := D)
  refine ⟨(kummerCoefficientExtensionSelf q).comp ((kummerCoefficientExtensionMap q a).comp g),
    fun x => ?_⟩
  have hEval : D.val (evalAtOne D (KummerCoefficientExtension.toLaurent (g x))) =
      algebraMap K A (e x) := by
    change D.val.toRingHom (evalAtOne D (KummerCoefficientExtension.toLaurent (g x))) = _
    rw [← evalAtOne_mapLaurentCoefficients D.val.toRingHom]
    change evalAtOne A (KummerCoefficientExtension.toLaurent
      (kummerCoefficientExtensionMap q D.val (g x))) = _
    rw [hg, he]
  have hEval' : evalAtOne D (KummerCoefficientExtension.toLaurent (g x)) =
      algebraMap K D (e x) :=
    Subtype.val_injective (hEval.trans (D.val.commutes (e x)).symm)
  change evalAtOne K (mapLaurentCoefficients a.toRingHom
    (KummerCoefficientExtension.toLaurent (g x))) = e x
  rw [evalAtOne_mapLaurentCoefficients, hEval']
  exact a.commutes (e x)

open scoped WideE in
/-- In particular a complex Laurent point for an algebra over the
algebraic numbers supplies a Laurent point with algebraic coefficients. -/
theorem nonempty_kummerPoint_of_complexLaurentPoint {S : Type*} [CommRing S]
    [Algebra (LaurentPolynomial AlgebraicComplex) S]
    [Algebra.FiniteType (LaurentPolynomial AlgebraicComplex) S]
    (q : ℕ) (f : S →ₐ[LaurentPolynomial AlgebraicComplex]
      KummerCoefficientExtension AlgebraicComplex ℂ q) :
    Nonempty (S →ₐ[LaurentPolynomial AlgebraicComplex] KummerExtension AlgebraicComplex q) := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  exact nonempty_kummerPoint_of_coefficientExtension q f

section BaseChange

variable (K E : Type*) [CommRing K] [CommRing E] [Algebra K E]

/-- The Laurent scalar extension acts by applying the inclusion of the
coefficient ring to the finitely supported coefficients. -/
def laurentCoefficientAlgebra : Algebra (LaurentPolynomial K) (LaurentPolynomial E) :=
  (mapLaurentCoefficients (algebraMap K E)).toAlgebra

/-- Extending Laurent coefficients is the ordinary scalar extension of
the coefficient ring, with the original Laurent variable unchanged. -/
def laurentCoefficientBaseChange :
    letI := laurentCoefficientAlgebra K E
    (LaurentPolynomial K ⊗[K] E) ≃ₐ[LaurentPolynomial K] LaurentPolynomial E := by
  let R := LaurentPolynomial K
  let L := LaurentPolynomial E
  let P := R ⊗[K] E
  let c := mapLaurentCoefficients (algebraMap K E)
  letI := laurentCoefficientAlgebra K E
  letI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq (fun a =>
    (mapLaurentCoefficients_C (algebraMap K E) a).symm)
  let i : R →ₐ[R] P := Algebra.TensorProduct.includeLeft
  let j : E →ₐ[K] P := Algebra.TensorProduct.includeRight
  let F : P →ₐ[R] L :=
    Algebra.TensorProduct.lift (Algebra.ofId R L) (IsScalarTower.toAlgHom K E L)
      (fun _ _ => Commute.all _ _)
  have hF (p : R) (a : E) : F (p ⊗ₜ[K] a) = c p * C a := rfl
  have hFi (p : R) : F (i p) = c p := F.commutes p
  have hFj (a : E) : F (j a) = C a := by
    change F ((1 : R) ⊗ₜ[K] a) = _
    rw [hF, map_one, one_mul]
  let v := Units.map i.toRingHom.toMonoidHom (laurentCoordinateUnit K)
  let G := LaurentPolynomial.eval₂ j.toRingHom v
  have hGC (a : E) : G (C a) = j a := LaurentPolynomial.eval₂_C _ _ _
  have hGT (n : ℤ) : G (T n) = i (T n) := by
    change LaurentPolynomial.eval₂ j.toRingHom
      (Units.map i.toRingHom.toMonoidHom (laurentCoordinateUnit K)) (T n) = _
    rw [LaurentPolynomial.eval₂_T, ← map_zpow]
    change i ((laurentCoordinateUnit K ^ n : Rˣ) : R) = _
    rw [laurentCoordinateUnit_zpow]
  have hG (p : R) : G (c p) = i p := by
    induction p using LaurentPolynomial.induction_on' with
    | add p a hp ha => simp only [map_add, hp, ha]
    | C_mul_T n a =>
      rw [map_mul c, map_mul G, map_mul i]
      change G (mapLaurentCoefficients (algebraMap K E) (C a)) *
        G (mapLaurentCoefficients (algebraMap K E) (T n)) = _
      rw [mapLaurentCoefficients_C, mapLaurentCoefficients_T, hGC, hGT]
      exact congrArg (· * i (T n)) ((j.commutes a).trans ((i.restrictScalars K).commutes a).symm)
  let G' : L →ₐ[R] P := { toRingHom := G, commutes' := hG }
  refine AlgEquiv.ofAlgHom F G' (AlgHom.ext (fun p => ?_)) ?_
  · change F (G p) = p
    induction p using LaurentPolynomial.induction_on' with
    | add a b ha hb => simp only [map_add, ha, hb]
    | C_mul_T n a =>
      rw [map_mul G, hGC, hGT, map_mul F, hFj, hFi]
      exact congrArg (C a * ·) (mapLaurentCoefficients_T (algebraMap K E) n)
  · apply Algebra.TensorProduct.ext'
    intro p a
    change G (F (p ⊗ₜ[K] a)) = p ⊗ₜ[K] a
    rw [hF, map_mul, hG, hGC]
    change (p ⊗ₜ[K] (1 : E)) * ((1 : R) ⊗ₜ[K] a) = p ⊗ₜ[K] a
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end BaseChange

/-- A nontrivial Laurent algebra remains nontrivial after a nontrivial
extension of the constant field. -/
theorem laurentCoefficientTensor_nontrivial (K E Q : Type*)
    [Field K] [CommRing E] [Nontrivial E] [Algebra K E] [CommRing Q] [Nontrivial Q]
    [Algebra (LaurentPolynomial K) Q] :
    letI := laurentCoefficientAlgebra K E
    Nontrivial (LaurentPolynomial E ⊗[LaurentPolynomial K] Q) := by
  let R := LaurentPolynomial K
  let L := LaurentPolynomial E
  letI := laurentCoefficientAlgebra K E
  letI : Algebra K Q := ((algebraMap R Q).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.FaithfullyFlat K E := inferInstance
  letI : Nontrivial (E ⊗[K] Q) := Module.FaithfullyFlat.lTensor_nontrivial K E Q
  let e := (Algebra.TensorProduct.congr (laurentCoefficientBaseChange K E).symm
    (AlgEquiv.refl (R := R) (A₁ := Q))).trans (Algebra.TensorProduct.comm R (R ⊗[K] E) Q)
  let h := (e.trans (Algebra.TensorProduct.cancelBaseChange K R R Q E)).toRingEquiv.trans
    (Algebra.TensorProduct.comm K Q E).toRingEquiv
  exact h.toEquiv.nontrivial

private theorem mapLaurentCoefficients_kummer {K E : Type*} [CommRing K] [CommRing E]
    (c : K →+* E) (q : ℕ) (p : LaurentPolynomial K) :
    kummer E q (mapLaurentCoefficients c p) = mapLaurentCoefficients c (kummer K q p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n a =>
    simp only [map_mul, mapLaurentCoefficients_C, mapLaurentCoefficients_T, kummer_C, kummer_T]

/-- Restrict a Kummer map after extension of the Laurent coefficients. -/
def restrictKummerPointCoefficients {K E Q : Type*}
    [CommRing K] [CommRing E] [Algebra K E] [CommRing Q] [Algebra (LaurentPolynomial K) Q]
    (q : ℕ) :
    letI := laurentCoefficientAlgebra K E
    (LaurentPolynomial E ⊗[LaurentPolynomial K] Q →ₐ[LaurentPolynomial E] KummerExtension E q) →
      Q →ₐ[LaurentPolynomial K] KummerCoefficientExtension K E q := by
  let R := LaurentPolynomial K
  let L := LaurentPolynomial E
  letI := laurentCoefficientAlgebra K E
  let A := L ⊗[R] Q
  intro f
  let j : Q →ₐ[R] A := Algebra.TensorProduct.includeRight
  refine { toRingHom := f.toRingHom.comp j.toRingHom, commutes' := fun p => ?_ }
  have hj : j (algebraMap R Q p) = algebraMap L A (algebraMap R L p) := by
    rw [j.commutes, ← IsScalarTower.algebraMap_apply R L A]
  change KummerExtension.toLaurent E q (f (j (algebraMap R Q p))) =
    mapLaurentCoefficients (algebraMap K E) (kummer K q p)
  rw [hj, f.commutes, KummerExtension.algebraMap_apply]
  exact mapLaurentCoefficients_kummer (algebraMap K E) q p

open scoped WideE in
/-- A theorem producing Laurent-valued Kummer maps for nonzero finite
étale complex algebras gives the same statement over the algebraic numbers. -/
theorem finiteLaurentCoverHasKummerMap_of_complex (h : FiniteLaurentCoverHasKummerMap ℂ) :
    FiniteLaurentCoverHasKummerMap AlgebraicComplex := by
  intro Q _ _ _ _ _
  let K := AlgebraicComplex
  let R := LaurentPolynomial K
  let L := LaurentPolynomial ℂ
  letI := laurentCoefficientAlgebra K ℂ
  let A := L ⊗[R] Q
  letI : Nontrivial A := laurentCoefficientTensor_nontrivial K ℂ Q
  letI : Module.Finite L A :=
    inferInstanceAs (Module.Finite L (L ⊗[R] Q))
  letI : Algebra.Etale L A :=
    inferInstanceAs (Algebra.Etale L (L ⊗[R] Q))
  obtain ⟨q, hq, ⟨f⟩⟩ := h A
  exact ⟨q, hq, nonempty_kummerPoint_of_complexLaurentPoint q
    (restrictKummerPointCoefficients q f)⟩

universe u

/-- A Kummer map through a prescribed point of the ordinary fiber at one. -/
def FiniteLaurentCoverHasPointedKummerMap (K : Type u) [Field K] : Prop :=
  ∀ (Q : Type u) [CommRing Q] [Nontrivial Q] [Algebra (LaurentPolynomial K) Q]
    [Module.Finite (LaurentPolynomial K) Q] [Algebra.Etale (LaurentPolynomial K) Q],
    ∀ e : Q →+* K, (∀ p, e (algebraMap (LaurentPolynomial K) Q p) = evalAtOne K p) →
      ∃ q : ℕ, 0 < q ∧ ∃ f : Q →ₐ[LaurentPolynomial K] KummerExtension K q,
        ∀ x, evalAtOne K (KummerExtension.toLaurent K q (f x)) = e x

open scoped WideE in
theorem finiteLaurentCoverHasPointedKummerMap_of_complex
    (h : FiniteLaurentCoverHasPointedKummerMap ℂ) :
    FiniteLaurentCoverHasPointedKummerMap AlgebraicComplex := by
  intro Q _ _ _ _ _ e he
  let K := AlgebraicComplex
  let R := LaurentPolynomial K
  let L := LaurentPolynomial ℂ
  letI := laurentCoefficientAlgebra K ℂ
  let A := L ⊗[R] Q
  letI : Nontrivial A := laurentCoefficientTensor_nontrivial K ℂ Q
  letI : Module.Finite L A := inferInstanceAs (Module.Finite L (L ⊗[R] Q))
  letI : Algebra.Etale L A := inferInstanceAs (Algebra.Etale L (L ⊗[R] Q))
  letI : Algebra R ℂ := ((evalAtOne ℂ).comp (mapLaurentCoefficients (algebraMap K ℂ))).toAlgebra
  letI : Module R L := Algebra.toModule
  letI : Module R R := Semiring.toModule
  letI : IsScalarTower R R L := ⟨fun r s x => by
    change algebraMap R L (r * s) * x = algebraMap R L r * (algebraMap R L s * x)
    rw [map_mul, mul_assoc]⟩
  let eL : L →ₐ[R] ℂ := { toRingHom := evalAtOne ℂ, commutes' := fun _ => rfl }
  let eQ : Q →ₐ[R] ℂ :=
    { toRingHom := (algebraMap K ℂ).comp e
      commutes' := fun p => by
        change algebraMap K ℂ (e (algebraMap R Q p)) =
          evalAtOne ℂ (mapLaurentCoefficients (algebraMap K ℂ) p)
        rw [he, evalAtOne_mapLaurentCoefficients] }
  let eA : A →ₐ[R] ℂ :=
    Algebra.TensorProduct.lift (R := R) (S := R) eL eQ (fun _ _ => Commute.all _ _)
  have heA (p : L) : eA (algebraMap L A p) = evalAtOne ℂ p := by
    change eL p * eQ 1 = _
    rw [map_one, mul_one]
    rfl
  obtain ⟨q, hq, f, hf⟩ := h A eA.toRingHom heA
  let g := restrictKummerPointCoefficients q f
  letI : IsAlgClosed K := IsAlgClosure.isAlgClosed ℚ
  refine ⟨q, hq, exists_kummerPoint_preserving_evaluation q g e ?_⟩
  intro x
  change evalAtOne ℂ (KummerExtension.toLaurent ℂ q (f ((1 : L) ⊗ₜ[R] x))) = _
  rw [hf]
  change eL 1 * eQ x = _
  rw [map_one, one_mul]
  rfl

end WideE
