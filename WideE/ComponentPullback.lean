import WideE.Kummer
import FiberTensorChart

/-! Pull back the connected-group torsor to a chosen quotient component in §7.2. -/

noncomputable section

open scoped TensorProduct

namespace WideE

section Components

variable (Q A S : Type*) [CommRing Q] [CommRing A] [CommRing S]
  [Algebra Q A] [Algebra Q S]

/-- The coordinate algebra of the inverse image of a component over the finite quotient. -/
abbrev ComponentPullback := A ⊗[Q] S

/-- Sections of the pullback are precisely maps from the torsor algebra over the component. -/
def componentSections : (ComponentPullback Q A S →ₐ[A] A) ≃ (S →ₐ[Q] A) where
  toFun σ := (σ.restrictScalars Q).comp Algebra.TensorProduct.includeRight
  invFun f := Algebra.TensorProduct.lift (AlgHom.id A A) f (fun _ _ => Commute.all _ _)
  left_inv σ := by
    apply Algebra.TensorProduct.ext'
    intro a s
    change a * σ (1 ⊗ₜ[Q] s) = σ (a ⊗ₜ[Q] s)
    have hσ : σ (a ⊗ₜ[Q] (1 : S)) = a := σ.commutes a
    calc
      a * σ (1 ⊗ₜ[Q] s) = σ (a ⊗ₜ[Q] (1 : S)) * σ (1 ⊗ₜ[Q] s) := by rw [hσ]
      _ = σ (a ⊗ₜ[Q] s) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  right_inv f := by
    apply AlgHom.ext
    intro s
    change 1 * f s = f s
    exact one_mul _

@[simp] theorem componentSections_apply (σ : ComponentPullback Q A S →ₐ[A] A) (s : S) :
    componentSections Q A S σ s = σ (1 ⊗ₜ[Q] s) :=
  rfl

@[simp] theorem componentSections_symm_tmul (f : S →ₐ[Q] A) (a : A) (s : S) :
    (componentSections Q A S).symm f (a ⊗ₜ[Q] s) = a * f s :=
  rfl

end Components

section KummerSection

variable {K Q S : Type*} [CommRing K] [CommRing Q] [CommRing S] {q : ℕ}
  [Algebra (LaurentPolynomial K) Q] [Algebra Q S] [Algebra (LaurentPolynomial K) S]
  [IsScalarTower (LaurentPolynomial K) Q S]

/-- The algebra of the inverse image after choosing a Kummer component of the quotient. -/
abbrev KummerComponentPullback (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q)
    (S : Type*) [CommRing S] [Algebra Q S] :=
  letI := j.toRingHom.toAlgebra
  ComponentPullback Q (KummerExtension K q) S

/-- A section over that component is a map of algebras over the new Laurent ring. -/
abbrev KummerComponentSection (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q)
    (S : Type*) [CommRing S] [Algebra Q S] :=
  letI := j.toRingHom.toAlgebra
  KummerComponentPullback j S →ₐ[KummerExtension K q] KummerExtension K q

/-- Compose a section over the component with the projection to the original torsor. -/
def kummerSectionAlgHom (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q)
    (σ : KummerComponentSection j S) : S →ₐ[LaurentPolynomial K] KummerExtension K q := by
  letI := j.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom j
  exact (componentSections Q (KummerExtension K q) S σ).restrictScalars (LaurentPolynomial K)

@[simp] theorem kummerSectionAlgHom_algebraMap (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q)
    (σ : KummerComponentSection j S) (x : Q) :
    kummerSectionAlgHom j σ (algebraMap Q S x) = j x := by
  letI := j.toRingHom.toAlgebra
  exact (componentSections Q (KummerExtension K q) S σ).commutes x

/-- The section written in the new Laurent coordinate. -/
def kummerSection (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q)
    (σ : KummerComponentSection j S) : S →+* LaurentPolynomial K :=
  (KummerExtension.toLaurent K q).toRingHom.comp (kummerSectionAlgHom j σ).toRingHom

@[simp] theorem kummerSection_comp_algebraMap (j : Q →ₐ[LaurentPolynomial K] KummerExtension K q)
    (σ : KummerComponentSection j S) :
    (kummerSection j σ).comp (algebraMap (LaurentPolynomial K) S) = kummer K q := by
  apply RingHom.ext
  intro f
  change KummerExtension.toLaurent K q
    (kummerSectionAlgHom j σ (algebraMap (LaurentPolynomial K) S f)) = kummer K q f
  rw [AlgHom.commutes]
  rfl

end KummerSection

section Chart

variable {K Q A S H : Type*} [CommRing K] [CommRing Q] [CommRing A] [CommRing S] [CommRing H]
  [Algebra K Q] [Algebra K A] [Algebra K S] [Algebra K H]
  [Algebra Q A] [Algebra Q S] [IsScalarTower K Q A] [IsScalarTower K Q S]

/-- Over the quotient component the group algebra is the scalar extension of the same
coordinate algebra over the constant field. -/
def componentTorsorChart (e : S ⊗[K] H ≃ₐ[S] S ⊗[Q] S) :
    ComponentPullback Q A S ⊗[A] (A ⊗[K] H) ≃ₐ[ComponentPullback Q A S]
      ComponentPullback Q A S ⊗[A] ComponentPullback Q A S :=
  (Algebra.TensorProduct.cancelBaseChange K A (ComponentPullback Q A S)
    (ComponentPullback Q A S) H).trans (StrictEUnit.fiberMultiplicationChart e)

end Chart

end WideE
