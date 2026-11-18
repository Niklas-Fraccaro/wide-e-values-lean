import WideE.TorusHilbert90
import WideE.GaloisTorsor
import BialgebraBaseChangeLaws
import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Hopf points of a torus with a specified Galois splitting

The semilinear action on the scalar extension preserves group-like elements.
In a split torus the group-like elements are precisely the lattice monomials.
-/

noncomputable section

open scoped TensorProduct
open TensorProduct StrictEUnit

set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 90000

attribute [local instance 2000] Algebra.toModule

namespace WideE

section Monomials

variable {K G : Type*} [Field K]

private def monomialTensorCoefficient (i j : G) :
    (MonoidAlgebra K G ⊗[K] MonoidAlgebra K G) →ₗ[K] K :=
  (TensorProduct.lid K K).toLinearMap.comp
    (TensorProduct.map (Finsupp.lapply i) (Finsupp.lapply j))

private theorem monomialTensorCoefficient_tmul (i j : G) (x y : MonoidAlgebra K G) :
    monomialTensorCoefficient (K := K) i j (x ⊗ₜ[K] y) = x i * y j := rfl

private theorem monomialTensorCoefficient_comul (i j : G) (hij : i ≠ j)
    (x : MonoidAlgebra K G) :
    monomialTensorCoefficient (K := K) i j (Coalgebra.comul (R := K) x) = 0 := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single g a =>
    rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
      monomialTensorCoefficient_tmul]
    change (Finsupp.single g (1 : K)) i * (Finsupp.single g a) j = 0
    by_cases hi : g = i
    · subst g
      simp [Finsupp.single_eq_of_ne hij]
    · simp [Finsupp.single_eq_of_ne hi]

variable [CommGroup G]

theorem comul_monoidAlgebra_of (g : G) :
    Coalgebra.comul (R := K) (MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G g ⊗ₜ[K] MonoidAlgebra.of K G g := by
  change Coalgebra.comul (R := K) (MonoidAlgebra.single g (1 : K)) = _
  rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  rfl

theorem counit_monoidAlgebra_of (g : G) :
    Coalgebra.counit (R := K) (MonoidAlgebra.of K G g) = 1 := by
  change Coalgebra.counit (R := K) (MonoidAlgebra.single g (1 : K)) = _
  rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]

/-- The normalized group-like elements in a group algebra are the group monomials. -/
theorem exists_monoidAlgebra_of_of_grouplike (x : MonoidAlgebra K G)
    (hΔ : Coalgebra.comul (R := K) x = x ⊗ₜ[K] x)
    (hε : Coalgebra.counit (R := K) x = 1) :
    ∃ g : G, MonoidAlgebra.of K G g = x := by
  classical
  have hx : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hε
    exact zero_ne_one hε
  obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hx
  have hCoeff (j : G) (hj : g ≠ j) : x j = 0 := by
    have h := congrArg (monomialTensorCoefficient (K := K) g j) hΔ
    rw [monomialTensorCoefficient_comul g j hj, monomialTensorCoefficient_tmul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Finsupp.mem_support_iff.mp hg)
  have hSingle : x = Finsupp.single g (x g) := by
    ext j
    by_cases h : g = j
    · subst j
      simp
    · rw [hCoeff j h, Finsupp.single_eq_of_ne h]
  have hOne : x g = 1 := by
    calc
      x g = Coalgebra.counit (R := K) (MonoidAlgebra.single g (x g)) := by
        rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
      _ = 1 := (congrArg (Coalgebra.counit (R := K)) hSingle).symm.trans hε
  refine ⟨g, ?_⟩
  change Finsupp.single g 1 = x
  rw [← hOne, ← hSingle]

end Monomials

section ScalarGalois

variable {F E H : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Algebra F H]

private abbrev scalarGal (σ : E ≃ₐ[F] E) : E ⊗[F] H ≃ₐ[F] E ⊗[F] H :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : H ≃ₐ[F] H)

private theorem scalarGal_tmul (σ : E ≃ₐ[F] E) (a : E) (h : H) :
    scalarGal σ (a ⊗ₜ[F] h) = σ a ⊗ₜ[F] h := rfl

private theorem scalarGal_one (x : E ⊗[F] H) : scalarGal (1 : E ≃ₐ[F] E) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a h => rfl

private theorem scalarGal_mul (σ τ : E ≃ₐ[F] E) (x : E ⊗[F] H) :
    scalarGal (σ * τ) x = scalarGal σ (scalarGal τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a h => rfl

private def scalarGalPair (σ : E ≃ₐ[F] E) :
    ((E ⊗[F] H) ⊗[E] (E ⊗[F] H)) ≃ₐ[F] ((E ⊗[F] H) ⊗[E] (E ⊗[F] H)) :=
  let t := (algebraTensorBaseChangeEquiv (k := F) E H H).restrictScalars F
  t.trans ((scalarGal (H := H ⊗[F] H) σ).trans t.symm)

private theorem scalarGalPair_tmul (σ : E ≃ₐ[F] E) (x y : E ⊗[F] H) :
    scalarGalPair σ (x ⊗ₜ[E] y) = scalarGal σ x ⊗ₜ[E] scalarGal σ y := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [zero_tmul, map_zero]
  | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
  | tmul a h =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, map_zero]
    | add b c hb hc => simp only [tmul_add, map_add, hb, hc]
    | tmul b j =>
      apply (algebraTensorBaseChangeEquiv (k := F) E H H).injective
      change algebraTensorBaseChangeEquiv (k := F) E H H
          ((algebraTensorBaseChangeEquiv (k := F) E H H).symm
            (scalarGal σ (algebraTensorBaseChangeEquiv (k := F) E H H
              ((a ⊗ₜ[F] h) ⊗ₜ[E] (b ⊗ₜ[F] j))))) = _
      simp only [AlgEquiv.apply_symm_apply, algebraTensorBaseChangeEquiv_tmul,
        scalarGal_tmul, map_mul]

end ScalarGalois

section BialgebraGalois

variable {F E H : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Bialgebra F H]

private theorem scalarGal_comul (σ : E ≃ₐ[F] E) (x : E ⊗[F] H) :
    baseChangeComul E (scalarGal σ x) = scalarGalPair σ (baseChangeComul E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a h =>
    apply (algebraTensorBaseChangeEquiv (k := F) E H H).injective
    change algebraTensorBaseChangeEquiv (k := F) E H H (baseChangeComul E (scalarGal σ (a ⊗ₜ[F] h))) =
      algebraTensorBaseChangeEquiv (k := F) E H H
        ((algebraTensorBaseChangeEquiv (k := F) E H H).symm
          (scalarGal σ (algebraTensorBaseChangeEquiv (k := F) E H H
            (baseChangeComul E (a ⊗ₜ[F] h)))))
    simp only [scalarGal_tmul, baseChangeComul_tmul, AlgEquiv.apply_symm_apply]

private theorem scalarGal_counit (σ : E ≃ₐ[F] E) (x : E ⊗[F] H) :
    baseChangeCounit E (scalarGal σ x) = σ (baseChangeCounit E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a h => simp only [scalarGal_tmul, baseChangeCounit_tmul, map_mul, AlgEquiv.commutes]

end BialgebraGalois

/-- Use the actual scalar-extended coalgebra on the group being split. -/
local instance torusScalarBialgebra {F E H : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing H] [Bialgebra F H] : Bialgebra E (E ⊗[F] H) :=
  baseChangeBialgebra E

/-- A splitting isomorphism of the base-changed coordinate algebra with the
group algebra of the character group. -/
abbrev TorusHopfSplitting (F E H G : Type*) [Field F] [Field E] [Algebra F E]
    [CommRing H] [Bialgebra F H] [CommGroup G] :=
  (E ⊗[F] H) ≃ₐc[E] MonoidAlgebra E G

section SplitAction

variable {F E H G : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Bialgebra F H] [CommGroup G]
variable (e : TorusHopfSplitting F E H G)

private def splitMonomial : G →* (E ⊗[F] H) :=
  e.symm.toAlgEquiv.toAlgHom.toMonoidHom.comp (MonoidAlgebra.of E G)

private theorem splitMonomial_injective : Function.Injective (splitMonomial e) :=
  e.symm.toAlgEquiv.injective.comp MonoidAlgebra.of_injective

private theorem splitMonomial_comul (g : G) :
    baseChangeComul E (splitMonomial e g) =
      splitMonomial e g ⊗ₜ[E] splitMonomial e g := by
  have h := CoalgHomClass.map_comp_comul_apply (R := E) e.symm (MonoidAlgebra.of E G g)
  rw [comul_monoidAlgebra_of, TensorProduct.map_tmul] at h
  exact h.symm

private theorem splitMonomial_counit (g : G) : baseChangeCounit E (splitMonomial e g) = 1 :=
  (CoalgHomClass.counit_comp_apply e.symm (MonoidAlgebra.of E G g)).trans
    (counit_monoidAlgebra_of g)

private theorem exists_splitMonomial_scalarGal (σ : E ≃ₐ[F] E) (g : G) :
    ∃ h : G, splitMonomial e h = scalarGal σ (splitMonomial e g) := by
  let x := scalarGal σ (splitMonomial e g)
  have hΔ : baseChangeComul E x = x ⊗ₜ[E] x := by
    dsimp only [x]
    rw [scalarGal_comul, splitMonomial_comul, scalarGalPair_tmul]
  have hε : baseChangeCounit E x = 1 := by
    dsimp only [x]
    rw [scalarGal_counit, splitMonomial_counit, map_one]
  have hΔ' : Coalgebra.comul (R := E) (e x) = e x ⊗ₜ[E] e x := by
    have hΔ₀ : Coalgebra.comul (R := E) x = x ⊗ₜ[E] x := hΔ
    have h := CoalgHomClass.map_comp_comul_apply (R := E) e x
    rw [hΔ₀, TensorProduct.map_tmul] at h
    exact h.symm
  have hε' : Coalgebra.counit (R := E) (e x) = 1 :=
    (CoalgHomClass.counit_comp_apply e x).trans hε
  obtain ⟨h, hh⟩ := exists_monoidAlgebra_of_of_grouplike (e x) hΔ' hε'
  refine ⟨h, ?_⟩
  change e.symm (MonoidAlgebra.of E G h) = x
  rw [hh]
  exact e.symm_apply_apply x

/-- The Galois action permutes the normalized group-like monomials of the
chosen splitting. It is an action by automorphisms of the character group. -/
def torusHopfLatticeAction : (E ≃ₐ[F] E) →* MulAut G := by
  let act (σ : E ≃ₐ[F] E) (g : G) := (exists_splitMonomial_scalarGal e σ g).choose
  have hAct (σ : E ≃ₐ[F] E) (g : G) :
      splitMonomial e (act σ g) = scalarGal σ (splitMonomial e g) :=
    (exists_splitMonomial_scalarGal e σ g).choose_spec
  let aut (σ : E ≃ₐ[F] E) : MulAut G :=
    { toFun := act σ
      invFun := act σ⁻¹
      left_inv := fun g => splitMonomial_injective e (by
        rw [hAct, hAct, ← scalarGal_mul, inv_mul_cancel, scalarGal_one])
      right_inv := fun g => splitMonomial_injective e (by
        rw [hAct, hAct, ← scalarGal_mul, mul_inv_cancel, scalarGal_one])
      map_mul' := fun g h => splitMonomial_injective e (by
        rw [map_mul, hAct, hAct, hAct, map_mul]
        exact map_mul (scalarGal σ) _ _) }
  exact
    { toFun := aut
      map_one' := MulEquiv.ext fun g => splitMonomial_injective e (by
        change splitMonomial e (act 1 g) = splitMonomial e g
        rw [hAct, scalarGal_one])
      map_mul' := fun σ τ => MulEquiv.ext fun g => splitMonomial_injective e (by
        change splitMonomial e (act (σ * τ) g) = splitMonomial e (act σ (act τ g))
        rw [hAct, hAct, hAct, scalarGal_mul]) }

private theorem torusHopfLatticeAction_monomial (σ : E ≃ₐ[F] E) (g : G) :
    splitMonomial e (torusHopfLatticeAction e σ g) = scalarGal σ (splitMonomial e g) :=
  (exists_splitMonomial_scalarGal e σ g).choose_spec

end SplitAction

section ScalarPoints

variable {F E H : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Algebra F H]

private def evalBaseChangePoint (p : H →ₐ[F] E) : E ⊗[F] H →ₐ[E] E :=
  Algebra.TensorProduct.lift (AlgHom.id E E) p fun _ _ => Commute.all _ _

private theorem evalBaseChangePoint_tmul (p : H →ₐ[F] E) (a : E) (h : H) :
    evalBaseChangePoint p (a ⊗ₜ[F] h) = a * p h := rfl

private def baseChangePointEquiv : (H →ₐ[F] E) ≃ (E ⊗[F] H →ₐ[E] E) where
  toFun := evalBaseChangePoint
  invFun q := (q.restrictScalars F).comp Algebra.TensorProduct.includeRight
  left_inv p := AlgHom.ext fun h => one_mul (p h)
  right_inv q := by
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a h =>
      change a * q ((1 : E) ⊗ₜ[F] h) = q (a ⊗ₜ[F] h)
      have hh : a ⊗ₜ[F] h =
          algebraMap E (E ⊗[F] H) a * ((1 : E) ⊗ₜ[F] h) := by
        change a ⊗ₜ[F] h = (a ⊗ₜ[F] (1 : H)) * ((1 : E) ⊗ₜ[F] h)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hh, map_mul, q.commutes]
      rfl

private theorem evalBaseChangePoint_postcompose (σ : E ≃ₐ[F] E) (p : H →ₐ[F] E)
    (z : E ⊗[F] H) :
    evalBaseChangePoint ((σ.toAlgHom.restrictScalars F).comp p) z =
      σ (evalBaseChangePoint p (scalarGal σ⁻¹ z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a h =>
    rw [scalarGal_tmul, evalBaseChangePoint_tmul, evalBaseChangePoint_tmul, map_mul]
    change a * σ (p h) = σ ((σ⁻¹) a) * σ (p h)
    exact congrArg (· * σ (p h)) (σ.apply_symm_apply a).symm

end ScalarPoints

section PairEvaluation

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
variable [Algebra K A] [Algebra K B]

private def evalPointPair (p q : A →ₐ[K] B) : A ⊗[K] A →ₐ[K] B :=
  Algebra.TensorProduct.lift p q fun _ _ => Commute.all _ _

private theorem evalPointPair_tmul (p q : A →ₐ[K] B) (x y : A) :
    evalPointPair p q (x ⊗ₜ[K] y) = p x * q y := rfl

end PairEvaluation

section Multiplication

variable {F E H : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Bialgebra F H]

private theorem evalPointPair_baseChange (p q : H →ₐ[F] E) (a : E) (z : H ⊗[F] H) :
    evalPointPair (evalBaseChangePoint p) (evalBaseChangePoint q)
      ((algebraTensorBaseChangeEquiv (k := F) E H H).symm (a ⊗ₜ[F] z)) =
      a * evalPointPair p q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero, mul_zero]
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy, mul_add]
  | tmul x y =>
    simp only [algebraTensorBaseChangeEquiv_symm_tmul, evalPointPair_tmul,
      evalBaseChangePoint_tmul, one_mul, mul_assoc]

private theorem evalBaseChangePoint_mul (p q : H →ₐ[F] E) (z : E ⊗[F] H) :
    evalBaseChangePoint (hopfPointMul p q) z =
      evalPointPair (evalBaseChangePoint p) (evalBaseChangePoint q) (baseChangeComul E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a h => exact (evalPointPair_baseChange p q a (Coalgebra.comul (R := F) h)).symm

end Multiplication

section SplitPointEquiv

variable {F E H G : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Bialgebra F H] [CommGroup G]

private def monoidHomUnitEquiv : (G →* E) ≃ (G →* Eˣ) where
  toFun f := f.toHomUnits
  invFun f := (Units.coeHom E).comp f
  left_inv _ := MonoidHom.ext fun _ => rfl
  right_inv _ := MonoidHom.ext fun _ => Units.ext rfl

variable (e : TorusHopfSplitting F E H G)

/-- The splitting identifies points with homomorphisms from the character group to units. -/
def torusHopfPointCoords : (H →ₐ[F] E) ≃ (G →* Eˣ) :=
  baseChangePointEquiv.trans
    (({ toFun := fun q : E ⊗[F] H →ₐ[E] E => q.comp e.symm.toAlgEquiv.toAlgHom
        invFun := fun q => q.comp e.toAlgEquiv.toAlgHom
        left_inv := fun q => AlgHom.ext fun z => congrArg q (e.symm_apply_apply z)
        right_inv := fun q => AlgHom.ext fun z => congrArg q (e.apply_symm_apply z) } :
      (E ⊗[F] H →ₐ[E] E) ≃ (MonoidAlgebra E G →ₐ[E] E)).trans
        ((MonoidAlgebra.lift E G E).symm.trans monoidHomUnitEquiv))

/-- Evaluation on the monomials takes the Hopf point product to coordinatewise multiplication. -/
theorem torusHopfPointCoords_mul (p q : H →ₐ[F] E) :
    torusHopfPointCoords e (hopfPointMul p q) =
      torusHopfPointCoords e p * torusHopfPointCoords e q := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change evalBaseChangePoint (hopfPointMul p q) (splitMonomial e g) =
    evalBaseChangePoint p (splitMonomial e g) * evalBaseChangePoint q (splitMonomial e g)
  rw [evalBaseChangePoint_mul, splitMonomial_comul, evalPointPair_tmul]

end SplitPointEquiv

section Equivariance

variable {F E H Λ : Type*} [Field F] [Field E] [Algebra F E]
variable [CommRing H] [Bialgebra F H] [AddCommGroup Λ]

/-- The point coordinates transport Galois conjugation to the semilinear lattice action. -/
theorem torusHopfPointCoords_galois
    (e : TorusHopfSplitting F E H (Multiplicative Λ))
    (σ : E ≃ₐ[F] E) (p : H →ₐ[F] E) :
    torusHopfPointCoords e ((σ.toAlgHom.restrictScalars F).comp p) =
      torusLatticeAct (torusHopfLatticeAction e) σ (torusHopfPointCoords e p) := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  change evalBaseChangePoint ((σ.toAlgHom.restrictScalars F).comp p) (splitMonomial e g) =
    σ (evalBaseChangePoint p (splitMonomial e ((torusHopfLatticeAction e σ)⁻¹ g)))
  rw [evalBaseChangePoint_postcompose, ← torusHopfLatticeAction_monomial e σ⁻¹,
    map_inv (torusHopfLatticeAction e)]

end Equivariance

section Hilbert90

variable {F Ω H Λ ι : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω]
variable [IsAlgClosed Ω] [IsGalois F Ω] [CommRing H] [HopfAlgebra F H]
variable [AddCommGroup Λ] [Finite ι]

/-- Actual Hopf point cocycles of a torus with a specified finite Galois splitting
are coboundaries over a C₁ field containing all primitive roots of unity. -/
theorem isHopfPointCoboundary_of_torusHopfSplitting
    (hF : IsC1 F) (hRoots : ∀ n : ℕ, 0 < n → (primitiveRoots n F).Nonempty)
    (basis : Basis ι ℤ Λ) (E : FiniteGaloisIntermediateField F Ω)
    (e : TorusHopfSplitting F E H (Multiplicative Λ))
    (c : (E ≃ₐ[F] E) → H →ₐ[F] E) (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary c := by
  let ρ := torusHopfLatticeAction e
  let co := torusHopfPointCoords e
  let d (σ : E ≃ₐ[F] E) := co (c σ)
  have hd : IsTorusLatticeCocycle ρ d := by
    intro σ τ
    change torusHopfPointCoords e (c (σ * τ)) =
      torusHopfPointCoords e (c σ) * torusLatticeAct ρ σ (torusHopfPointCoords e (c τ))
    rw [hc.2, torusHopfPointCoords_mul, torusHopfPointCoords_galois]
  obtain ⟨b, hb⟩ := torusLatticeHilbert90_of_isC1 hF hRoots basis E ρ d hd
  refine ⟨co.symm b, fun σ => co.injective ?_⟩
  change torusHopfPointCoords e
      (hopfPointMul (c σ) ((σ.toAlgHom.restrictScalars F).comp (co.symm b))) =
    co (co.symm b)
  rw [torusHopfPointCoords_mul, torusHopfPointCoords_galois, co.apply_symm_apply]
  exact hb σ

end Hilbert90

/-- The same torus theorem over the rational function field of algebraically
closed constants. -/
theorem isHopfPointCoboundary_of_torusHopfSplitting_over_ratFunc
    {k H Λ ι : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing H] [HopfAlgebra (RatFunc k) H] [AddCommGroup Λ] [Finite ι]
    (basis : Basis ι ℤ Λ)
    (E : FiniteGaloisIntermediateField (RatFunc k) (AlgebraicClosure (RatFunc k)))
    (e : TorusHopfSplitting (RatFunc k) E H (Multiplicative Λ))
    (c : (E ≃ₐ[RatFunc k] E) → H →ₐ[RatFunc k] E) (hc : IsHopfPointCocycle c) :
    IsHopfPointCoboundary c := by
  letI : CharZero (RatFunc k) := charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  exact isHopfPointCoboundary_of_torusHopfSplitting (ratFunc_isC1 k)
    (fun _ hn => primitiveRoots_nonempty_of_algClosed_subfield (k := k) hn) basis E e c hc

end WideE
