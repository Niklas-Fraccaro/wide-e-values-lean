import WideE.Kummer
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The coordinate normalization in the two-branch Kummer argument. -/

noncomputable section

namespace WideE

open LaurentPolynomial

section CoordinateMaps

variable {K : Type*} [CommRing K]

/-- An algebra map out of the Laurent line is determined by its value on its coordinate. -/
theorem laurentAlgHom_ext {S : Type*} [CommRing S] [Algebra K S]
    {f g : LaurentPolynomial K →ₐ[K] S} (h : f (T 1) = g (T 1)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial K))
  change (f.comp Polynomial.toLaurentAlg).toRingHom = (g.comp Polynomial.toLaurentAlg).toRingHom
  congr 1
  apply Polynomial.algHom_ext
  simpa only [AlgHom.comp_apply, Polynomial.toLaurentAlg_apply, Polynomial.toLaurent_X] using h

private def coordinateUnit (K : Type*) [CommRing K] : (LaurentPolynomial K)ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add, add_neg_cancel, T_zero]
  inv_val := by rw [← T_add, neg_add_cancel, T_zero]

private def scalingHom (a : Kˣ) : LaurentPolynomial K →ₐ[K] LaurentPolynomial K where
  toRingHom := LaurentPolynomial.eval₂ C (Units.map C.toMonoidHom a * coordinateUnit K)
  commutes' b := LaurentPolynomial.eval₂_C _ _ b

@[simp] private theorem scalingHom_T_one (a : Kˣ) : scalingHom a (T 1) = C (a : K) * T 1 := by
  change LaurentPolynomial.eval₂ C _ (T 1) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

@[simp] private theorem scalingHom_C (a : Kˣ) (b : K) : scalingHom a (C b) = C b :=
  LaurentPolynomial.eval₂_C _ _ _

private theorem scalingHom_comp_inv (a : Kˣ) :
    (scalingHom a).comp (scalingHom a⁻¹) = AlgHom.id K (LaurentPolynomial K) := by
  apply laurentAlgHom_ext
  simp only [AlgHom.comp_apply, scalingHom_T_one, map_mul, scalingHom_C, AlgHom.id_apply]
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

/-- Scale the Laurent coordinate by a unit of the coefficient ring. -/
def laurentScale (a : Kˣ) : LaurentPolynomial K ≃ₐ[K] LaurentPolynomial K :=
  AlgEquiv.ofAlgHom (scalingHom a) (scalingHom a⁻¹) (scalingHom_comp_inv a)
    (by simpa only [inv_inv] using scalingHom_comp_inv a⁻¹)

@[simp] theorem laurentScale_C (a : Kˣ) (b : K) : laurentScale a (C b) = C b :=
  scalingHom_C a b

@[simp] theorem laurentScale_T_nat (a : Kˣ) (q : ℕ) :
    laurentScale a (T (q : ℤ)) = C ((a : K) ^ q) * T (q : ℤ) := by
  have ht : (T 1 : LaurentPolynomial K) ^ q = T (q : ℤ) := by rw [T_pow, mul_one]
  rw [← ht, map_pow, show laurentScale a (T 1) = _ from scalingHom_T_one a,
    mul_pow, ← map_pow]

private def reversalHom (K : Type*) [CommRing K] :
    LaurentPolynomial K →ₐ[K] LaurentPolynomial K where
  toRingHom := AddMonoidAlgebra.mapDomainRingHom K
    ({ toFun := (fun n : ℤ => -n), map_zero' := neg_zero, map_add' := neg_add } : ℤ →+ ℤ)
  commutes' a := by
    change Finsupp.mapDomain (fun n : ℤ => -n) (Finsupp.single 0 a) = Finsupp.single 0 a
    rw [Finsupp.mapDomain_single, neg_zero]

private theorem reversalHom_T (n : ℤ) : reversalHom K (T n) = T (-n) := by
  change Finsupp.mapDomain (fun n : ℤ => -n) (Finsupp.single n (1 : K)) =
    Finsupp.single (-n) (1 : K)
  rw [Finsupp.mapDomain_single]

/-- Reverse the Laurent coordinate by sending it to its inverse. -/
def laurentReverse (K : Type*) [CommRing K] : LaurentPolynomial K ≃ₐ[K] LaurentPolynomial K :=
  AlgEquiv.ofAlgHom (reversalHom K) (reversalHom K)
    (laurentAlgHom_ext (by simp only [AlgHom.comp_apply, reversalHom_T, neg_neg, AlgHom.id_apply]))
    (laurentAlgHom_ext (by simp only [AlgHom.comp_apply, reversalHom_T, neg_neg, AlgHom.id_apply]))

@[simp] theorem laurentReverse_T (n : ℤ) : laurentReverse K (T n) = T (-n) :=
  reversalHom_T n

@[simp] theorem laurentReverse_C (a : K) : laurentReverse K (C a) = C a :=
  (laurentReverse K).commutes a

end CoordinateMaps

section Normalization

variable {K : Type*} [Field K] [IsAlgClosed K]

private theorem normalize_positive_power (φ : LaurentPolynomial K →ₐ[K] LaurentPolynomial K)
    {q : ℕ} (hq : 0 < q) {a : K} (ha : a ≠ 0) (hφ : φ (T 1) = C a * T (q : ℤ)) :
    ∃ e : LaurentPolynomial K ≃ₐ[K] LaurentPolynomial K,
      e.toAlgHom.comp φ = kummerAlgHom K q := by
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ hq
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne'] at hu
    exact (inv_ne_zero ha) hu.symm
  refine ⟨laurentScale (Units.mk0 u hu0), laurentAlgHom_ext ?_⟩
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hφ, map_mul, laurentScale_C,
    laurentScale_T_nat, Units.val_mk0, hu, kummerAlgHom_apply, kummer_T, mul_one]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

/-- Any injective map between Laurent coordinate rings is a power map after changing
the target coordinate. -/
theorem normalize_laurent_map (φ : LaurentPolynomial K →ₐ[K] LaurentPolynomial K)
    (hφ : Function.Injective φ) :
    ∃ (q : ℕ) (e : LaurentPolynomial K ≃ₐ[K] LaurentPolynomial K),
      0 < q ∧ e.toAlgHom.comp φ = kummerAlgHom K q := by
  obtain ⟨a, n, ha, h⟩ := (laurent_isUnit_iff _).mp ((isUnit_T 1).map φ)
  have hn : n ≠ 0 := by
    intro hn0
    rw [hn0, T_zero, mul_one, LaurentPolynomial.C_eq_algebraMap, ← φ.commutes,
      ← LaurentPolynomial.C_eq_algebraMap] at h
    have hc := congrArg (fun p : LaurentPolynomial K => p 1) (hφ h)
    change Finsupp.single 1 (1 : K) 1 = Finsupp.single 0 a 1 at hc
    simp at hc
  cases n with
  | ofNat q =>
    have hq : 0 < q := Nat.pos_of_ne_zero (fun hq => hn (by subst q; rfl))
    obtain ⟨e, he⟩ := normalize_positive_power φ hq ha.ne_zero h
    exact ⟨q, e, hq, he⟩
  | negSucc q =>
    let ψ := (laurentReverse K).toAlgHom.comp φ
    have hψ : ψ (T 1) = C a * T ((q + 1 : ℕ) : ℤ) := by
      change laurentReverse K (φ (T 1)) = _
      rw [h, map_mul, laurentReverse_C, laurentReverse_T]
      rfl
    obtain ⟨e, he⟩ := normalize_positive_power ψ (Nat.succ_pos q) ha.ne_zero hψ
    exact ⟨q + 1, (laurentReverse K).trans e, Nat.succ_pos q, he⟩

variable {Q : Type*} [CommRing Q] [Algebra K Q] [Algebra (LaurentPolynomial K) Q]
  [IsScalarTower K (LaurentPolynomial K) Q]

/-- Once a component has a Laurent coordinate, its original structure map is isomorphic to
the Kummer map of its actual degree. -/
theorem exists_kummerEquiv_of_laurentCoordinate (coordinate : Q ≃ₐ[K] LaurentPolynomial K)
    (hBase : Function.Injective (algebraMap (LaurentPolynomial K) Q)) :
    ∃ q : ℕ, 0 < q ∧ q = Module.finrank (LaurentPolynomial K) Q ∧
      Nonempty (Q ≃ₐ[LaurentPolynomial K] KummerExtension K q) := by
  let φ := coordinate.toAlgHom.comp (IsScalarTower.toAlgHom K (LaurentPolynomial K) Q)
  obtain ⟨q, e, hq, he⟩ := normalize_laurent_map φ (coordinate.injective.comp hBase)
  let e' : Q ≃ₐ[LaurentPolynomial K] KummerExtension K q :=
    { (coordinate.trans e).toRingEquiv.trans (KummerExtension.toLaurent K q).symm with
      commutes' := fun p => DFunLike.congr_fun he p }
  refine ⟨q, hq, ?_, ⟨e'⟩⟩
  rw [Module.finrank_eq_card_basis ((KummerExtension.basis K q hq).map e'.symm.toLinearEquiv),
    Fintype.card_fin]

end Normalization

/-- The two-branch Riemann–Hurwitz degree equality forces genus zero and one point
over each of the two boundary points. -/
theorem genus_zero_two_branches {g r₀ rInf : ℕ} (h₀ : 0 < r₀) (hInf : 0 < rInf)
    (h : (2 : ℤ) * g - 2 = -(r₀ : ℤ) - rInf) :
    g = 0 ∧ r₀ = 1 ∧ rInf = 1 := by omega

end WideE
