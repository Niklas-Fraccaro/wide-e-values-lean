import WideE.ConnectedKummerClassification

/-! A prescribed point over one normalizes the coordinate of a connected Kummer cover. -/

noncomputable section

open LaurentPolynomial

namespace WideE

private def scaleKummerRoot {K : Type*} [CommRing K] {q : ℕ} (a : Kˣ) (ha : (a : K) ^ q = 1) :
    KummerExtension K q ≃ₐ[LaurentPolynomial K] KummerExtension K q := by
  have hc : (laurentScale a).toAlgHom.comp (kummerAlgHom K q) = kummerAlgHom K q := by
    apply laurentAlgHom_ext
    simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, kummerAlgHom_apply, kummer_T, mul_one,
      laurentScale_T_nat, ha, map_one, one_mul]
  exact { (KummerExtension.toLaurent K q).trans
      ((laurentScale a).toRingEquiv.trans (KummerExtension.toLaurent K q).symm) with
    commutes' := fun p => DFunLike.congr_fun hc p }

private theorem scaleKummerRoot_coordinate {K : Type*} [CommRing K] {q : ℕ}
    (a : Kˣ) (ha : (a : K) ^ q = 1) :
    scaleKummerRoot a ha (KummerExtension.power K q 1) =
      algebraMap K (KummerExtension K q) (a : K) * KummerExtension.power K q 1 := by
  apply (KummerExtension.toLaurent K q).injective
  change laurentScale a (T 1) = C (a : K) * T 1
  simpa only [Nat.cast_one, pow_one] using laurentScale_T_nat a 1

/-- The Kummer isomorphism can send its coordinate to a unit taking the value
one at a prescribed algebraic point over one. -/
theorem exists_normalizedKummerCoordinate (A : Type) [CommRing A]
    [Algebra AlgebraicComplex A] [Algebra (LaurentPolynomial AlgebraicComplex) A]
    [IsScalarTower AlgebraicComplex (LaurentPolynomial AlgebraicComplex) A]
    [ConnectedSpace (PrimeSpectrum A)] [Module.Finite (LaurentPolynomial AlgebraicComplex) A]
    [Algebra.Etale (LaurentPolynomial AlgebraicComplex) A]
    (p : A →ₐ[AlgebraicComplex] AlgebraicComplex)
    (hp : p (algebraMap (LaurentPolynomial AlgebraicComplex) A (T 1)) = 1) :
    ∃ q : ℕ, 0 < q ∧ q = Module.finrank (LaurentPolynomial AlgebraicComplex) A ∧
      ∃ e : KummerExtension AlgebraicComplex q ≃ₐ[LaurentPolynomial AlgebraicComplex] A,
        p (e (KummerExtension.power AlgebraicComplex q 1)) = 1 := by
  let K := AlgebraicComplex
  let R := LaurentPolynomial K
  obtain ⟨q, hq, hRank, ⟨e⟩⟩ := exists_kummerEquiv_of_connected_finiteEtaleLaurent A
  let t := e.symm (KummerExtension.power K q 1)
  have ht : t ^ q = algebraMap R A (T 1) := by
    rw [show t = _ from rfl, ← map_pow, KummerExtension.coordinate_pow,
      ← KummerExtension.algebraMap_coordinate, e.symm.commutes]
  let a := p t
  have ha : a ^ q = 1 := by rw [show a = p t from rfl, ← map_pow, ht, hp]
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne'] at ha
    exact zero_ne_one ha
  let b := (Units.mk0 a ha0)⁻¹
  have hbVal : (b : K) = a⁻¹ := rfl
  have hb : (b : K) ^ q = 1 := by rw [hbVal, inv_pow, ha, inv_one]
  have hscalar (c : K) : e.symm (algebraMap K (KummerExtension K q) c) = algebraMap K A c :=
    (e.symm.restrictScalars K).commutes c
  refine ⟨q, hq, hRank, (scaleKummerRoot b hb).trans e.symm, ?_⟩
  rw [AlgEquiv.trans_apply, scaleKummerRoot_coordinate, map_mul, hscalar, map_mul, p.commutes]
  change (b : K) * a = 1
  rw [hbVal, inv_mul_cancel₀ ha0]

end WideE
