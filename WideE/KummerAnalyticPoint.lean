import WideE.Kummer
import WideE.LaurentAnalyticRigidity

/-! A holomorphic lift of the Kummer map through a finite algebra is algebraic. -/

noncomputable section

namespace WideE

open scoped Topology

/-- The power map on the complex punctured line. -/
def complexPuncturedPower (q : ℕ) (z : ComplexPuncturedLine) : ComplexPuncturedLine :=
  ⟨(z : ℂ) ^ q, pow_ne_zero q z.property⟩

theorem complexLaurentFunctions_kummer (q : ℕ) (r : LaurentPolynomial ℂ)
    (z : ComplexPuncturedLine) :
    complexLaurentFunctions (kummer ℂ q r) z = complexLaurentFunctions r (complexPuncturedPower q z) := by
  let w := Units.mk0 (z : ℂ) z.property
  have h : w ^ q = Units.mk0 (complexPuncturedPower q z : ℂ) (complexPuncturedPower q z).property :=
    Units.ext rfl
  change (LaurentPolynomial.eval₂ (RingHom.id ℂ) w |>.comp (kummer ℂ q)) r =
    LaurentPolynomial.eval₂ (RingHom.id ℂ) _ r
  rw [eval₂_comp_kummer, h]

/-- A family of points with holomorphic evaluations and the prescribed base
coordinate defines a section over the algebraic Kummer cover with the same
evaluation at every point of the punctured line. -/
theorem exists_kummerPoint_of_holomorphic_points {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra (LaurentPolynomial ℂ) A] [Module.Finite (LaurentPolynomial ℂ) A]
    (q : ℕ) (p : ComplexPuncturedLine → A →ₐ[ℂ] ℂ)
    (hp : ∀ z (r : LaurentPolynomial ℂ), p z (algebraMap (LaurentPolynomial ℂ) A r) =
      complexLaurentFunctions r (complexPuncturedPower q z))
    (hhol : ∀ a : A, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({0}ᶜ : Set ℂ) ∧
      ∀ z : ComplexPuncturedLine, f z = p z a) :
    ∃ f : A →ₐ[LaurentPolynomial ℂ] KummerExtension ℂ q,
      ∀ (z : ComplexPuncturedLine) (a : A),
        complexLaurentFunctions (KummerExtension.toLaurent ℂ q (f a)) z = p z a := by
  let φ : A →+* (ComplexPuncturedLine → ℂ) := {
    toFun := fun a z => p z a
    map_one' := funext fun _ => map_one _
    map_zero' := funext fun _ => map_zero _
    map_mul' := fun a b => funext fun _ => map_mul _ a b
    map_add' := fun a b => funext fun _ => map_add _ a b }
  have hφ : φ.comp (algebraMap (LaurentPolynomial ℂ) A) = complexLaurentFunctions.comp (kummer ℂ q) :=
    RingHom.ext fun r => funext fun z => (hp z r).trans (complexLaurentFunctions_kummer q r z).symm
  letI : Algebra (LaurentPolynomial ℂ) (ComplexPuncturedLine → ℂ) := complexLaurentFunctions.toAlgebra
  have hIntegral (a : A) : IsIntegral (LaurentPolynomial ℂ) (φ a) := by
    obtain ⟨P, hP, hPa⟩ := IsIntegral.of_finite (LaurentPolynomial ℂ) a
    refine ⟨P.map (kummer ℂ q), hP.map _, ?_⟩
    have h := congrArg φ hPa
    rw [Polynomial.hom_eval₂, map_zero, hφ] at h
    rw [Polynomial.eval₂_map]
    exact h
  have hRange (a : A) : φ a ∈ complexLaurentFunctions.range := by
    obtain ⟨f, hf, hfa⟩ := hhol a
    have h₀ : (fun z : ComplexPuncturedLine => f z) = φ a := funext hfa
    obtain ⟨g, hg⟩ := exists_laurent_of_holomorphic_integral hf (h₀ ▸ hIntegral a)
    exact RingHom.mem_range.mpr ⟨g, funext fun z => (hg z).trans (hfa z)⟩
  let e := RingEquiv.ofBijective complexLaurentFunctions.rangeRestrict
    ⟨fun _ _ h => complexLaurentFunctions_injective (congrArg Subtype.val h),
      complexLaurentFunctions.rangeRestrict_surjective⟩
  let j := (KummerExtension.toLaurent ℂ q).symm.toRingHom.comp
    (e.symm.toRingHom.comp (φ.codRestrict _ hRange))
  refine ⟨{ toRingHom := j, commutes' := fun r => ?_ }, ?_⟩
  · apply (KummerExtension.toLaurent ℂ q).injective
    apply complexLaurentFunctions_injective
    change complexLaurentFunctions (e.symm (φ.codRestrict _ hRange (algebraMap (LaurentPolynomial ℂ) A r))) =
      complexLaurentFunctions (kummer ℂ q r)
    exact (congrArg Subtype.val (e.apply_symm_apply _)).trans (congrFun (congrArg DFunLike.coe hφ) r)
  · intro z a
    change complexLaurentFunctions (e.symm (φ.codRestrict _ hRange a)) z = φ a z
    exact congrFun (congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict _ hRange a))) z

/-- A holomorphic lift gives a Laurent-algebra point of the Kummer cover. -/
theorem nonempty_kummerPoint_of_holomorphic_points {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra (LaurentPolynomial ℂ) A] [Module.Finite (LaurentPolynomial ℂ) A]
    (q : ℕ) (p : ComplexPuncturedLine → A →ₐ[ℂ] ℂ)
    (hp : ∀ z (r : LaurentPolynomial ℂ), p z (algebraMap (LaurentPolynomial ℂ) A r) =
      complexLaurentFunctions r (complexPuncturedPower q z))
    (hhol : ∀ a : A, ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({0}ᶜ : Set ℂ) ∧
      ∀ z : ComplexPuncturedLine, f z = p z a) :
    Nonempty (A →ₐ[LaurentPolynomial ℂ] KummerExtension ℂ q) :=
  Nonempty.intro (exists_kummerPoint_of_holomorphic_points q p hp hhol).choose

end WideE
