import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Finite equations for the points of an algebra in prescribed generators. -/

noncomputable section

namespace WideE

universe w

variable {k H ι : Type*} [CommRing k] [IsNoetherianRing k] [CommRing H] [Algebra k H] [Finite ι]

omit [IsNoetherianRing k] [Finite ι] in
/-- A finite set of generators of the evaluation kernel presents the points
over every coefficient algebra. -/
theorem finiteAlgHomPresentation_iff {A : Type*} [CommRing A] [Algebra k A]
    (x : ι → H) (hGen : Algebra.adjoin k (Set.range x) = ⊤)
    (Γ : Finset (MvPolynomial ι k)) (hΓ : Ideal.span (↑Γ : Set _) =
      RingHom.ker (MvPolynomial.aeval (R := k) x).toRingHom) (a : ι → A) :
    (∀ P ∈ Γ, MvPolynomial.aeval a P = 0) ↔ ∃! p : H →ₐ[k] A, ∀ i, p (x i) = a i := by
  let f : MvPolynomial ι k →ₐ[k] H := MvPolynomial.aeval x
  have hf : Function.Surjective f := (AlgHom.range_eq_top f).mp
    ((Algebra.adjoin_range_eq_range_aeval k x).symm.trans hGen)
  let I := RingHom.ker f.toRingHom
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  have hΓ' : Ideal.span (↑Γ : Set _) = I := hΓ
  let v : MvPolynomial ι k →ₐ[k] A := MvPolynomial.aeval a
  constructor
  · intro hv
    have hI : I ≤ RingHom.ker v.toRingHom := by
      rw [← hΓ']
      apply Ideal.span_le.mpr
      intro P hP
      exact hv P hP
    let p := (Ideal.Quotient.liftₐ I v hI).comp e.symm.toAlgHom
    have hp (P : MvPolynomial ι k) : p (f P) = v P := by
      change Ideal.Quotient.liftₐ I v hI (e.symm (e (Ideal.Quotient.mk I P))) = v P
      rw [AlgEquiv.symm_apply_apply]
      rfl
    have hPx (i : ι) : p (x i) = a i := by
      simpa only [f, v, MvPolynomial.aeval_X] using hp (MvPolynomial.X i)
    refine ⟨p, hPx, fun q hQ => ?_⟩
    apply AlgHom.ext_of_adjoin_eq_top hGen
    rintro _ ⟨i, rfl⟩
    exact (hQ i).trans (hPx i).symm
  · intro h
    obtain ⟨p, hp, _⟩ := h
    have hv : v = p.comp f := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [v, f, AlgHom.comp_apply, MvPolynomial.aeval_X, hp i]
    intro P hP
    have hKer : f P = 0 := by
      change P ∈ I
      rw [← hΓ']
      exact Ideal.subset_span hP
    change v P = 0
    rw [hv, AlgHom.comp_apply, hKer, map_zero]


/-- Over a Noetherian base, the given finite algebra generators identify every point
with the unique tuple satisfying the finite equations for their evaluation kernel. -/
theorem exists_finiteAlgHomPresentation (x : ι → H)
    (hGen : Algebra.adjoin k (Set.range x) = ⊤) :
    ∃ Γ : Finset (MvPolynomial ι k), ∀ (A : Type w) [CommRing A] [Algebra k A] (a : ι → A),
      (∀ P ∈ Γ, MvPolynomial.aeval a P = 0) ↔ ∃! p : H →ₐ[k] A, ∀ i, p (x i) = a i := by
  obtain ⟨Γ, hΓ⟩ := IsNoetherian.noetherian (RingHom.ker (MvPolynomial.aeval (R := k) x).toRingHom)
  exact ⟨Γ, fun A _ _ a => finiteAlgHomPresentation_iff x hGen Γ hΓ a⟩

end WideE
