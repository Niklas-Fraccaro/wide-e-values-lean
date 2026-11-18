import WideE.PolynomialIdealDescent
import WideE.TorsorRepresentationDescent

/-! Equations for a projective subvariety after twisting by an affine torsor. -/

open scoped TensorProduct Matrix

noncomputable section

namespace WideE

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000

section MatrixSubstitution

variable {ι A B : Type*} [Fintype ι] [CommRing A] [CommRing B]

/-- Replace the variables by the linear forms given by the rows of a matrix. -/
def matrixPolynomialSubstitution (M : Matrix ι ι A) : MvPolynomial ι A →ₐ[A] MvPolynomial ι A :=
  MvPolynomial.aeval (M.map MvPolynomial.C *ᵥ MvPolynomial.X)

@[simp] theorem matrixPolynomialSubstitution_X (M : Matrix ι ι A) (i : ι) :
    matrixPolynomialSubstitution M (MvPolynomial.X i) = (M.map MvPolynomial.C *ᵥ MvPolynomial.X) i :=
  MvPolynomial.aeval_X _ _

@[simp] theorem matrixPolynomialSubstitution_C (M : Matrix ι ι A) (a : A) :
    matrixPolynomialSubstitution M (MvPolynomial.C a) = MvPolynomial.C a :=
  (matrixPolynomialSubstitution M).commutes a

theorem matrixPolynomialSubstitution_mul (M N : Matrix ι ι A) :
    matrixPolynomialSubstitution (M * N) =
      (matrixPolynomialSubstitution N).comp (matrixPolynomialSubstitution M) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, matrixPolynomialSubstitution_X, matrixPolynomialSubstitution_X]
  have h := RingHom.map_mulVec (matrixPolynomialSubstitution N).toRingHom
    (M.map MvPolynomial.C) MvPolynomial.X i
  change matrixPolynomialSubstitution N ((M.map MvPolynomial.C *ᵥ MvPolynomial.X) i) = _ at h
  have hConst : (M.map MvPolynomial.C).map (matrixPolynomialSubstitution N).toRingHom =
      M.map MvPolynomial.C := Matrix.ext fun _ _ => matrixPolynomialSubstitution_C N _
  rw [hConst] at h
  have hVar : (matrixPolynomialSubstitution N).toRingHom ∘ MvPolynomial.X =
      N.map MvPolynomial.C *ᵥ MvPolynomial.X := funext (matrixPolynomialSubstitution_X N)
  rw [hVar, Matrix.mulVec_mulVec, ← Matrix.map_mul] at h
  exact h.symm

theorem matrixPolynomialSubstitution_map (f : A →+* B) (M : Matrix ι ι A) :
    (MvPolynomial.map f).comp (matrixPolynomialSubstitution M).toRingHom =
      (matrixPolynomialSubstitution (M.map f)).toRingHom.comp (MvPolynomial.map f) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.map f (matrixPolynomialSubstitution M (MvPolynomial.C a)) =
      matrixPolynomialSubstitution (M.map f) (MvPolynomial.map f (MvPolynomial.C a))
    rw [matrixPolynomialSubstitution_C, MvPolynomial.map_C, matrixPolynomialSubstitution_C]
  · intro i
    change MvPolynomial.map f (matrixPolynomialSubstitution M (MvPolynomial.X i)) =
      matrixPolynomialSubstitution (M.map f) (MvPolynomial.map f (MvPolynomial.X i))
    rw [MvPolynomial.map_X, matrixPolynomialSubstitution_X, matrixPolynomialSubstitution_X,
      RingHom.map_mulVec]
    have hConst : (M.map (MvPolynomial.C : A →+* MvPolynomial ι A)).map (MvPolynomial.map f) =
        (M.map f).map MvPolynomial.C :=
      Matrix.ext fun i j => MvPolynomial.map_C f (M i j)
    have hX : MvPolynomial.map f ∘ (MvPolynomial.X : ι → MvPolynomial ι A) = MvPolynomial.X :=
      funext (MvPolynomial.map_X f)
    rw [hConst, hX]

theorem eval₂_matrixPolynomialSubstitution (f : A →+* B) (M : Matrix ι ι A) (x : ι → B)
    (p : MvPolynomial ι A) :
    (matrixPolynomialSubstitution M p).eval₂ f x = p.eval₂ f (M.map f *ᵥ x) := by
  have h : (MvPolynomial.eval₂Hom f x).comp (matrixPolynomialSubstitution M).toRingHom =
      MvPolynomial.eval₂Hom f (M.map f *ᵥ x) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (matrixPolynomialSubstitution M (MvPolynomial.C a)).eval₂ f x =
        (MvPolynomial.C a).eval₂ f (M.map f *ᵥ x)
      rw [matrixPolynomialSubstitution_C, MvPolynomial.eval₂_C, MvPolynomial.eval₂_C]
    · intro i
      change (MvPolynomial.eval₂Hom f x) (matrixPolynomialSubstitution M (MvPolynomial.X i)) =
        (MvPolynomial.X i).eval₂ f (M.map f *ᵥ x)
      rw [matrixPolynomialSubstitution_X, RingHom.map_mulVec, MvPolynomial.eval₂_X]
      have hConst : (M.map MvPolynomial.C).map (MvPolynomial.eval₂Hom f x) = M.map f :=
        Matrix.ext fun i j => MvPolynomial.eval₂_C f x (M i j)
      have hX : MvPolynomial.eval₂Hom f x ∘ MvPolynomial.X = x := funext (MvPolynomial.eval₂_X f x)
      rw [hConst, hX]
  exact DFunLike.congr_fun h p

/-- Linear substitution preserves the degree of a homogeneous polynomial. -/
theorem matrixPolynomialSubstitution_isHomogeneous (M : Matrix ι ι A) {p : MvPolynomial ι A} {d : ℕ}
    (hp : p.IsHomogeneous d) : (matrixPolynomialSubstitution M p).IsHomogeneous d := by
  have hLinear (i : ι) : ((M.map MvPolynomial.C *ᵥ MvPolynomial.X) i).IsHomogeneous 1 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    simpa only [zero_add] using (MvPolynomial.isHomogeneous_C (σ := ι) (M i j)).mul
      (MvPolynomial.isHomogeneous_X (R := A) j)
  simpa only [matrixPolynomialSubstitution, one_mul] using hp.aeval _ hLinear

end MatrixSubstitution

section HomogeneousIdeals

attribute [local instance] MvPolynomial.gradedAlgebra

variable {ι A B : Type*} [CommRing A] [CommRing B]

private theorem polynomialIdeal_map_isHomogeneous (f : MvPolynomial ι A →+* MvPolynomial ι B)
    (hF : ∀ (p : MvPolynomial ι A) (d : ℕ), p.IsHomogeneous d → (f p).IsHomogeneous d)
    {I : Ideal (MvPolynomial ι A)} (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι A)) :
    (I.map f).IsHomogeneous (MvPolynomial.homogeneousSubmodule ι B) := by
  rw [← hI.toIdeal_homogeneousCore_eq_self]
  change ((I.homogeneousCore' (MvPolynomial.homogeneousSubmodule ι A)).map f).IsHomogeneous _
  rw [Ideal.homogeneousCore', Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨_, ⟨p, _, rfl⟩, rfl⟩
  obtain ⟨d, hd⟩ := p.property
  exact ⟨d, hF p.val d hd⟩

end HomogeneousIdeals

section ScalarExtension

variable {k H L ι : Type*} [CommRing k] [CommRing H] [CommRing L]
  [Algebra k H] [Algebra k L] [Fintype ι]

/-- Extend the coefficient ring of a polynomial ideal. -/
def scalarExtendedPolynomialIdeal (A : Type*) [CommRing A] [Algebra k A]
    (I : Ideal (MvPolynomial ι k)) : Ideal (MvPolynomial ι A) :=
  I.map (MvPolynomial.map (algebraMap k A))

omit [Fintype ι] in
private theorem coefficientIdeal_map (I : Ideal (MvPolynomial ι k)) (f : H →ₐ[k] L) :
    (I.map (MvPolynomial.map (algebraMap k H))).map (MvPolynomial.map f.toRingHom) =
      I.map (MvPolynomial.map (algebraMap k L)) := by
  have hScalar : f.toRingHom.comp (algebraMap k H) = algebraMap k L := RingHom.ext f.commutes
  have h : (MvPolynomial.map (σ := ι) f.toRingHom).comp (MvPolynomial.map (algebraMap k H)) =
      MvPolynomial.map (algebraMap k L) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.map f.toRingHom (MvPolynomial.map (algebraMap k H) p) = _
    rw [MvPolynomial.map_map, hScalar]
  rw [Ideal.map_map, h]

private theorem coefficientIdeal_after_substitution (I : Ideal (MvPolynomial ι k)) (M : Matrix ι ι H)
    (f : H →ₐ[k] L) :
    ((I.map (MvPolynomial.map (algebraMap k H))).map (matrixPolynomialSubstitution M).toRingHom).map
      (MvPolynomial.map f.toRingHom) =
    (I.map (MvPolynomial.map (algebraMap k L))).map
      (matrixPolynomialSubstitution (M.map f.toRingHom)).toRingHom := by
  rw [Ideal.map_map, matrixPolynomialSubstitution_map, ← Ideal.map_map, coefficientIdeal_map I f]

end ScalarExtension

section TwistedIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k R S H ι : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing H]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [HopfAlgebra k H] [Fintype ι] [DecidableEq ι]

/-- Pull back the invariant equations by the trivializing frame over the torsor. -/
def twistedPolynomialIdeal (I : Ideal (MvPolynomial ι k)) (g : Matrix ι ι S) : Ideal (MvPolynomial ι S) :=
  (I.map (MvPolynomial.map (algebraMap k S))).map (matrixPolynomialSubstitution g).toRingHom

local notation "q₁" => (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
local notation "q₂" => (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)

namespace AffineHopfTorsor

variable (T : AffineHopfTorsor k R S H)

omit [DecidableEq ι] in
/-- Invariance of the original equations under the universal group element
makes the two pullbacks of the twisted ideal agree. -/
theorem twistedPolynomialIdeal_equal_pulls (U : Matrix ι ι H) (g : Matrix ι ι S)
    (hg : g.map (q₁).toRingHom = U.map T.overlapPoint.toRingHom * g.map (q₂).toRingHom)
    (I : Ideal (MvPolynomial ι k))
    (hI : (scalarExtendedPolynomialIdeal H I).map (matrixPolynomialSubstitution U).toRingHom = scalarExtendedPolynomialIdeal H I) :
    (twistedPolynomialIdeal I g).map (MvPolynomial.map (q₁).toRingHom) =
      (twistedPolynomialIdeal I g).map (MvPolynomial.map (q₂).toRingHom) := by
  have hLeft := coefficientIdeal_after_substitution I g ((q₁).restrictScalars k)
  have hRight := coefficientIdeal_after_substitution I g ((q₂).restrictScalars k)
  change (twistedPolynomialIdeal I g).map (MvPolynomial.map (q₁).toRingHom) = _ at hLeft
  change (twistedPolynomialIdeal I g).map (MvPolynomial.map (q₂).toRingHom) = _ at hRight
  rw [hLeft, hRight]
  change (scalarExtendedPolynomialIdeal (S ⊗[R] S) I).map (matrixPolynomialSubstitution (g.map (q₁).toRingHom)).toRingHom =
    (scalarExtendedPolynomialIdeal (S ⊗[R] S) I).map (matrixPolynomialSubstitution (g.map (q₂).toRingHom)).toRingHom
  rw [hg, matrixPolynomialSubstitution_mul]
  have hInvariant := congrArg (Ideal.map (MvPolynomial.map T.overlapPoint.toRingHom)) hI
  unfold scalarExtendedPolynomialIdeal at hInvariant
  rw [coefficientIdeal_after_substitution I U T.overlapPoint, coefficientIdeal_map I T.overlapPoint]
    at hInvariant
  change (scalarExtendedPolynomialIdeal (S ⊗[R] S) I).map
      ((matrixPolynomialSubstitution (g.map (q₂).toRingHom)).toRingHom.comp
        (matrixPolynomialSubstitution (U.map T.overlapPoint.toRingHom)).toRingHom) = _
  unfold scalarExtendedPolynomialIdeal
  rw [← Ideal.map_map, hInvariant]

/-- The actual torsor frame descends the invariant homogeneous equations over a PID. -/
theorem exists_twistedPolynomialIdeal [IsDomain R] [IsPrincipalIdealRing R]
    (U : (Matrix ι ι H)ˣ)
    (hU : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (I : Ideal (MvPolynomial ι k)) (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι k))
    (hI : (scalarExtendedPolynomialIdeal H I).map (matrixPolynomialSubstitution U.val).toRingHom = scalarExtendedPolynomialIdeal H I) :
    ∃ (g : (Matrix ι ι S)ˣ) (J : Ideal (MvPolynomial ι R)),
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι R) ∧
      J.map (MvPolynomial.map (algebraMap R S)) = twistedPolynomialIdeal I g.val ∧
      g.val.map (q₁).toRingHom = U.val.map T.overlapPoint.toRingHom * g.val.map (q₂).toRingHom := by
  letI := T.faithfullyFlat
  obtain ⟨g, hg⟩ := T.exists_trivializingRepresentationMatrix U hU
  let I' := twistedPolynomialIdeal I g.val
  have hHom' : I'.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι S) :=
    polynomialIdeal_map_isHomogeneous (matrixPolynomialSubstitution g.val).toRingHom
      (fun _ _ h => matrixPolynomialSubstitution_isHomogeneous g.val h)
      (polynomialIdeal_map_isHomogeneous (MvPolynomial.map (algebraMap k S))
        (fun _ _ h => h.map (algebraMap k S)) hHom)
  refine ⟨g, I'.comap (MvPolynomial.map (algebraMap R S)),
    polynomialIdeal_comap_isHomogeneous _ hHom', ?_, hg⟩
  exact polynomialIdeal_descends_of_equal_pulls I'
    (T.twistedPolynomialIdeal_equal_pulls U.val g.val hg I hI)

end AffineHopfTorsor

end TwistedIdeal

end WideE
