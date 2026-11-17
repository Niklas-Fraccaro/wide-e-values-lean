import WideE.Fiber
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.Basic

/-! The Kummer base change of the Laurent coefficient ring in §7.1. -/

noncomputable section

namespace WideE

open LaurentPolynomial

/-- The target Laurent ring, viewed as an algebra over a separate copy of the Laurent ring. -/
def KummerExtension (K : Type*) [Semiring K] (_q : ℕ) := LaurentPolynomial K

namespace KummerExtension

variable (K : Type*) [CommRing K] (q : ℕ)

instance : CommRing (KummerExtension K q) :=
  inferInstanceAs (CommRing (LaurentPolynomial K))

instance : Algebra K (KummerExtension K q) :=
  inferInstanceAs (Algebra K (LaurentPolynomial K))

instance : Algebra (LaurentPolynomial K) (KummerExtension K q) :=
  (kummer K q : LaurentPolynomial K →+* KummerExtension K q).toAlgebra

instance : IsScalarTower K (LaurentPolynomial K) (KummerExtension K q) :=
  IsScalarTower.of_algebraMap_eq fun a => (kummer_C K q a).symm

theorem algebraMap_apply (f : LaurentPolynomial K) :
    algebraMap (LaurentPolynomial K) (KummerExtension K q) f = kummer K q f :=
  rfl

/-- Identify the target ring with Laurent polynomials in the new coordinate. -/
def toLaurent : KummerExtension K q ≃+* LaurentPolynomial K where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- An integer power of the new coordinate. -/
def power (i : ℤ) : KummerExtension K q :=
  (toLaurent K q).symm (T i)

@[simp] theorem toLaurent_power (i : ℤ) :
    toLaurent K q (power K q i) = T i :=
  (toLaurent K q).apply_symm_apply _

@[simp] theorem coordinate_pow (i : ℕ) :
    power K q 1 ^ i = power K q (i : ℤ) := by
  apply (toLaurent K q).injective
  simp [T_pow]

@[simp] theorem algebraMap_coordinate :
    algebraMap (LaurentPolynomial K) (KummerExtension K q) (T 1) = power K q (q : ℤ) := by
  apply (toLaurent K q).injective
  change kummer K q (T 1) = T (q : ℤ)
  simp

@[simp] theorem toLaurent_smul (f : LaurentPolynomial K) (g : KummerExtension K q) :
    toLaurent K q (f • g) = kummer K q f * toLaurent K q g :=
  rfl

private theorem smul_T_apply (f : LaurentPolynomial K) (i : ℤ) :
    toLaurent K q (f • power K q i) = Finsupp.mapDomain (fun m : ℤ => (q : ℤ) * m + i) f := by
  rw [toLaurent_smul, toLaurent_power]
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, add_mul, Finsupp.mapDomain_add, hf, hg]
  | C_mul_T m a =>
    rw [map_mul, kummer_C, kummer_T, mul_T_assoc, ← single_eq_C_mul_T,
      ← single_eq_C_mul_T, Finsupp.mapDomain_single]

private def exponent (i : ℤ × Fin q) : ℤ :=
  (q : ℤ) * i.1 + (i.2.val : ℤ)

private theorem exponent_bijective (hq : 0 < q) : Function.Bijective (exponent q) := by
  have hq' : (0 : ℤ) < q := Int.ofNat_pos.mpr hq
  constructor
  · rintro ⟨m, i⟩ ⟨n, j⟩ h
    have hrep (n : ℤ) (i : Fin q) :
        exponent q (n, i) / q = n ∧ exponent q (n, i) % q = (i.val : ℤ) :=
      (Int.ediv_emod_unique hq').mpr
        ⟨add_comm _ _, Int.ofNat_zero_le _, Int.ofNat_lt.mpr i.isLt⟩
    have hmn := (hrep m i).1.symm.trans ((congrArg (· / (q : ℤ)) h).trans (hrep n j).1)
    have hij := (hrep m i).2.symm.trans ((congrArg (· % (q : ℤ)) h).trans (hrep n j).2)
    exact Prod.ext hmn (Fin.ext (Int.ofNat.inj hij))
  · intro n
    have hr0 := Int.emod_nonneg n (ne_of_gt hq')
    have hrq : (n % (q : ℤ)).toNat < q := by
      rw [← Int.ofNat_lt, Int.toNat_of_nonneg hr0]
      exact Int.emod_lt_of_pos n hq'
    refine ⟨(n / (q : ℤ), ⟨(n % (q : ℤ)).toNat, hrq⟩), ?_⟩
    simp only [exponent, Int.toNat_of_nonneg hr0, Int.ediv_add_emod]

private theorem linearIndependent_powers (hq : 0 < q) :
    LinearIndependent (LaurentPolynomial K)
      (fun i : Fin q => power K q (i.val : ℤ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  ext n
  have h := congrArg (fun x : KummerExtension K q => (toLaurent K q x) (exponent q (n, i))) hf
  change (toLaurent K q (∑ j, f j • power K q (j.val : ℤ))) (exponent q (n, i)) =
    (toLaurent K q 0) (exponent q (n, i)) at h
  simp only [map_sum, map_zero, smul_T_apply, Finsupp.zero_apply] at h
  change (∑ x, Finsupp.mapDomain (fun m : ℤ => (q : ℤ) * m + (x.val : ℤ)) (f x) :
    ℤ →₀ K) (exponent q (n, i)) = 0 at h
  rw [Finsupp.finset_sum_apply] at h
  have hcoeff (j : Fin q) (hji : j ≠ i) :
      Finsupp.mapDomain (fun m : ℤ => (q : ℤ) * m + (j.val : ℤ)) (f j)
        (exponent q (n, i)) = 0 := by
    apply Finsupp.mapDomain_notin_range
    rintro ⟨m, hm⟩
    change exponent q (m, j) = exponent q (n, i) at hm
    exact hji (congrArg Prod.snd ((exponent_bijective q hq).injective hm))
  rw [Finset.sum_eq_single i (fun j _ hj => hcoeff j hj) (by simp)] at h
  have hinj : Function.Injective (fun m : ℤ => (q : ℤ) * m + (i.val : ℤ)) :=
    fun m n hm => congrArg Prod.fst ((exponent_bijective q hq).injective
      (show exponent q (m, i) = exponent q (n, i) from hm))
  simpa only [Finsupp.zero_apply] using (Finsupp.mapDomain_apply hinj (f i) n).symm.trans h

private theorem span_powers (hq : 0 < q) :
    ⊤ ≤ Submodule.span (LaurentPolynomial K)
      (Set.range (fun i : Fin q => power K q (i.val : ℤ))) := by
  intro f _
  rw [← (toLaurent K q).symm_apply_apply f]
  refine LaurentPolynomial.induction_on' (motive := fun g =>
    (toLaurent K q).symm g ∈ Submodule.span (LaurentPolynomial K)
      (Set.range (fun i : Fin q => power K q (i.val : ℤ)))) _ ?_ ?_
  · intro f g hf hg
    rw [map_add]
    exact Submodule.add_mem _ hf hg
  · intro n a
    obtain ⟨⟨m, i⟩, hi⟩ := (exponent_bijective q hq).surjective n
    change (q : ℤ) * m + (i.val : ℤ) = n at hi
    have h : (C a * T m : LaurentPolynomial K) • power K q (i.val : ℤ) =
        (toLaurent K q).symm (C a * T n) := by
      apply (toLaurent K q).injective
      rw [toLaurent_smul, toLaurent_power, RingEquiv.apply_symm_apply,
        map_mul, kummer_C, kummer_T, mul_T_assoc, hi]
    rw [← h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The Kummer extension is free with basis the powers from zero to `q - 1`. -/
def basis (hq : 0 < q) : Basis (Fin q) (LaurentPolynomial K) (KummerExtension K q) :=
  Basis.mk (linearIndependent_powers K q hq) (span_powers K q hq)

@[simp] theorem basis_apply (hq : 0 < q) (i : Fin q) :
    basis K q hq i = power K q (i.val : ℤ) :=
  Basis.mk_apply _ _ _

theorem free (hq : 0 < q) : Module.Free (LaurentPolynomial K) (KummerExtension K q) :=
  Module.Free.of_basis (basis K q hq)

theorem finite (hq : 0 < q) : Module.Finite (LaurentPolynomial K) (KummerExtension K q) :=
  Module.Finite.of_basis (basis K q hq)

section Fiber

open scoped TensorProduct

/-- Specialize the new Laurent coordinate at one. -/
scoped instance evaluationAlgebra : Algebra (KummerExtension K q) K :=
  ((evalAtOne K).comp (toLaurent K q).toRingHom).toAlgebra

scoped instance evaluationTower : IsScalarTower (LaurentPolynomial K) (KummerExtension K q) K :=
  IsScalarTower.of_algebraMap_eq fun f => (evalAtOne_kummer K q f).symm

variable (M : Type*) [AddCommGroup M] [Module (LaurentPolynomial K) M]

/-- The fiber at one of the Kummer pullback is canonically the original fiber at one. -/
def fiberAtOneBaseChange :
    K ⊗[KummerExtension K q] (KummerExtension K q ⊗[LaurentPolynomial K] M) ≃ₗ[K]
      FiberAtOne K M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange (LaurentPolynomial K)
    (KummerExtension K q) K K M

@[simp] theorem fiberAtOneBaseChange_tmul (a : K) (p : KummerExtension K q) (x : M) :
    fiberAtOneBaseChange K q M
      (a ⊗ₜ[KummerExtension K q] (p ⊗ₜ[LaurentPolynomial K] x)) =
        (evalAtOne K (toLaurent K q p) * a) ⊗ₜ[LaurentPolynomial K] x :=
  rfl

@[simp] theorem fiberAtOneBaseChange_class (x : M) :
    fiberAtOneBaseChange K q M (1 ⊗ₜ[KummerExtension K q] (1 ⊗ₜ[LaurentPolynomial K] x)) =
      fiberClass K M x := by
  simp only [fiberAtOneBaseChange_tmul, map_one, one_mul]
  rfl

end Fiber

/-- The defining polynomial for the new Laurent coordinate. -/
def polynomial : Polynomial (LaurentPolynomial K) :=
  Polynomial.X ^ q - Polynomial.C (T 1)

@[simp] theorem aeval_polynomial {A : Type*} [CommRing A] [Algebra (LaurentPolynomial K) A] (x : A) :
    Polynomial.aeval x (polynomial K q) =
      x ^ q - algebraMap (LaurentPolynomial K) A (T 1) := by
  simp [polynomial]

/-- The Kummer extension is generated by a root of the polynomial defining the power map. -/
def adjoinRootEquiv [Nontrivial K] (hq : 0 < q) : AdjoinRoot (polynomial K q) ≃ₐ[LaurentPolynomial K]
    KummerExtension K q := by
  have hmonic : (polynomial K q).Monic := Polynomial.monic_X_pow_sub_C _ hq.ne'
  let pb := AdjoinRoot.powerBasis' hmonic
  have hdim : pb.dim = q := Polynomial.natDegree_X_pow_sub_C
  let e : Fin pb.dim ≃ Fin q := finCongr hdim
  let φ := AdjoinRoot.liftHom (polynomial K q) (power K q 1) (by simp)
  let E := pb.basis.equiv (basis K q hq) e
  have hφ : φ.toLinearMap = E.toLinearMap := by
    apply pb.basis.ext
    intro i
    change φ (pb.basis i) = pb.basis.equiv (basis K q hq) e (pb.basis i)
    rw [Basis.equiv_apply, pb.basis_eq_pow, map_pow]
    change (AdjoinRoot.liftHom _ _ _) (AdjoinRoot.root _) ^ (i.val) = _
    rw [AdjoinRoot.liftHom_root, coordinate_pow, basis_apply]
    rfl
  refine AlgEquiv.ofBijective φ ?_
  have h : (φ : AdjoinRoot (polynomial K q) → KummerExtension K q) = E := by
    funext x
    exact LinearMap.congr_fun hφ x
  rw [h]
  exact E.bijective

@[simp] theorem adjoinRootEquiv_root [Nontrivial K] (hq : 0 < q) :
    adjoinRootEquiv K q hq (AdjoinRoot.root (polynomial K q)) = power K q 1 :=
  AdjoinRoot.liftHom_root (polynomial K q) (by simp)

private theorem add_pow_of_square_zero {B : Type*} [CommRing B] (r d : B)
    (hd : d ^ 2 = 0) (n : ℕ) :
    (r + d) ^ n = r ^ n + (n : B) * r ^ (n - 1) * d := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [pow_succ (r + d), ih]
      simp only [Nat.succ_sub_one, Nat.cast_succ]
      linear_combination ((n : B) + 1) * r ^ n * hd

private theorem lift_power_root {B : Type*} [CommRing B]
    (I : Ideal B) (hI : I ^ 2 = ⊥) {q : ℕ} (hq : 0 < q) (hqB : IsUnit (q : B))
    (b : B) (hb : IsUnit b) (v : B ⧸ I) (hv : v ^ q = Ideal.Quotient.mk I b) :
    ∃! x : B, Ideal.Quotient.mk I x = v ∧ x ^ q = b := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective v
  have hrq : Ideal.Quotient.mk I (r ^ q) = Ideal.Quotient.mk I b := by
    rw [map_pow, hr, hv]
  have hrUnit : IsUnit r := by
    apply (IsNilpotent.isUnit_quotient_mk_iff (I := I) ⟨2, hI⟩).mp
    apply (isUnit_pow_iff hq.ne').mp
    rw [← map_pow, hrq]
    exact hb.map (Ideal.Quotient.mk I)
  let u := (hqB.mul (hrUnit.pow (q - 1))).unit
  have hu : (u : B) = (q : B) * r ^ (q - 1) := IsUnit.unit_spec _
  let d := (↑u⁻¹ : B) * (b - r ^ q)
  have hd : d ∈ I := by
    apply I.mul_mem_left
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, hrq, sub_self]
  have hsq (x : B) (hx : x ∈ I) : x ^ 2 = 0 := by
    have h := Ideal.pow_mem_pow hx 2
    rw [hI, Submodule.mem_bot] at h
    exact h
  have hud : (u : B) * d = b - r ^ q := by
    simp [d, ← mul_assoc]
  refine ⟨r + d, ⟨?_, ?_⟩, ?_⟩
  · rw [map_add, hr, Ideal.Quotient.eq_zero_iff_mem.mpr hd, add_zero]
  · rw [add_pow_of_square_zero r d (hsq d hd), ← hu, hud]
    ring
  · intro y hy
    have hdiff : y - r ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hy.1, hr, sub_self]
    have hrep : r + (y - r) = y := by ring
    have hpow := add_pow_of_square_zero r (y - r) (hsq _ hdiff) q
    rw [hrep, hy.2, ← hu] at hpow
    have heq : y - r = d := u.mul_right_inj.mp <| by
      rw [hud, hpow, add_sub_cancel_left]
    rw [← heq, hrep]

end KummerExtension

namespace KummerExtension

variable (K : Type*) [Field K] [CharZero K] (q : ℕ)

omit [CharZero K] in
private theorem adjoinRoot_hom_root_pow {A : Type*} [CommRing A] [Algebra (LaurentPolynomial K) A]
    (f : AdjoinRoot (polynomial K q) →ₐ[LaurentPolynomial K] A) :
    f (AdjoinRoot.root (polynomial K q)) ^ q = algebraMap (LaurentPolynomial K) A (T 1) :=
  sub_eq_zero.mp ((aeval_polynomial K q _).symm.trans (AdjoinRoot.aeval_algHom_eq_zero _ f))

private theorem formallyEtale_adjoinRoot (hq : 0 < q) :
    Algebra.FormallyEtale (LaurentPolynomial K) (AdjoinRoot (polynomial K q)) := by
  constructor
  intro B _ _ I hI
  let b := algebraMap (LaurentPolynomial K) B (T 1)
  let s := AdjoinRoot.root (polynomial K q)
  have hb : IsUnit b := (isUnit_T (R := K) 1).map (algebraMap (LaurentPolynomial K) B)
  have hqB : IsUnit (q : B) := by
    let ψ := (algebraMap (LaurentPolynomial K) B).comp (C : K →+* LaurentPolynomial K)
    rw [← map_natCast ψ q]
    exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hq.ne')).map ψ
  constructor
  · intro f g hfg
    have hf : f s ^ q = b := adjoinRoot_hom_root_pow K q f
    have hg : g s ^ q = b := adjoinRoot_hom_root_pow K q g
    have hqv : (Ideal.Quotient.mk I (f s)) ^ q = Ideal.Quotient.mk I b := by
      rw [← map_pow, hf]
    obtain ⟨_, _, hunique⟩ := lift_power_root I hI hq hqB b hb (Ideal.Quotient.mk I (f s)) hqv
    have hgf : Ideal.Quotient.mk I (g s) = Ideal.Quotient.mk I (f s) :=
      (DFunLike.congr_fun hfg s).symm
    apply AdjoinRoot.algHom_ext
    exact (hunique (f s) ⟨rfl, hf⟩).trans (hunique (g s) ⟨hgf, hg⟩).symm
  · intro f
    have hf : f s ^ q = Ideal.Quotient.mk I b := adjoinRoot_hom_root_pow K q f
    obtain ⟨x, hx, _⟩ := lift_power_root I hI hq hqB b hb (f s) hf
    have hroot : Polynomial.aeval x (polynomial K q) = 0 := by
      rw [aeval_polynomial, sub_eq_zero]
      exact hx.2
    refine ⟨AdjoinRoot.liftHom (polynomial K q) x hroot, AdjoinRoot.algHom_ext ?_⟩
    rw [AlgHom.comp_apply, AdjoinRoot.liftHom_root]
    exact hx.1

/-- In characteristic zero the explicit positive-degree Kummer extension is étale. -/
theorem etale (hq : 0 < q) : Algebra.Etale (LaurentPolynomial K) (KummerExtension K q) := by
  letI := formallyEtale_adjoinRoot K q hq
  letI := finite K q hq
  exact ⟨Algebra.FormallyEtale.of_equiv (adjoinRootEquiv K q hq),
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

end KummerExtension

end WideE
