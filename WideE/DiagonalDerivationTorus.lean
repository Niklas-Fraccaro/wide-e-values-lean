import WideE.HopfLieDerivation
import WideE.TorusHopfCoordinates
import WideE.GeneralizedDerivationWeights
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# Tori from diagonal infinitesimal matrices

A derivation satisfying the diagonal matrix equation separates polynomial
relations into eigencomponents. Evaluating each component at the counit
gives the relations of a genuine diagonal subgroup.
-/

noncomputable section

open scoped Ideal Matrix TensorProduct

namespace WideE

section WeightedEvaluation

variable {k A σ Λ : Type*} [Field k] [CommRing A] [Algebra k A] [AddCommGroup Λ]

private def weightCharacter (k : Type*) [Field k] (a : Λ) :
    MonoidAlgebra k (Multiplicative Λ) :=
  MonoidAlgebra.of k (Multiplicative Λ) (Multiplicative.ofAdd a)

@[simp] private theorem weightCharacter_zero :
    weightCharacter k (0 : Λ) = 1 :=
  map_one (MonoidAlgebra.of k (Multiplicative Λ))

private theorem weightCharacter_add (a b : Λ) :
    weightCharacter k (a + b) = weightCharacter k a * weightCharacter k b :=
  map_mul (MonoidAlgebra.of k (Multiplicative Λ)) _ _

private theorem weightCharacter_nsmul (n : ℕ) (a : Λ) :
    weightCharacter k (n • a) = weightCharacter k a ^ n :=
  map_pow (MonoidAlgebra.of k (Multiplicative Λ)) _ _

private def monomialWeight (w : σ → Λ) (m : σ →₀ ℕ) : Λ :=
  m.sum fun i n => n • w i

private theorem weightedCharacter_prod (u : σ → k) (w : σ → Λ) (m : σ →₀ ℕ)
    (s : Finset σ) :
    (∏ i ∈ s, (u i • weightCharacter k (w i)) ^ m i) =
      (∏ i ∈ s, u i ^ m i) • weightCharacter k (∑ i ∈ s, m i • w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      smul_pow, ih, smul_mul_smul_comm, weightCharacter_add, weightCharacter_nsmul]

private theorem weighted_aeval_monomial (x : σ → A) (ε : A →ₐ[k] k) (w : σ → Λ)
    (m : σ →₀ ℕ) (c : k) :
    MvPolynomial.aeval (fun i => ε (x i) • weightCharacter k (w i)) (MvPolynomial.monomial m c) =
      ε (MvPolynomial.aeval x (MvPolynomial.monomial m c)) • weightCharacter k (monomialWeight w m) := by
  simp only [MvPolynomial.aeval_monomial, Finsupp.prod, monomialWeight, Finsupp.sum]
  rw [weightedCharacter_prod, ← Algebra.smul_def, smul_smul, map_mul, map_prod]
  simp only [AlgHom.commutes, Algebra.id.map_eq_id, RingHom.id_apply, map_pow]

/-- Evaluation at a scalar point respects polynomial relations after separating independent weights. -/
private theorem weighted_aeval_eq_zero_of_aeval_eq_zero (x : σ → A)
    (ε : A →ₐ[k] k) (w : σ → Λ) (V : Λ → Submodule k A) (hV : iSupIndep V)
    (hWeights : ∀ m (c : k), MvPolynomial.aeval x (MvPolynomial.monomial m c) ∈ V (monomialWeight w m))
    (p : MvPolynomial σ k)
    (hp : MvPolynomial.aeval x p = 0) :
    MvPolynomial.aeval (fun i => ε (x i) • weightCharacter k (w i)) p = 0 := by
  classical
  let z (m : σ →₀ ℕ) : V (monomialWeight w m) :=
    ⟨MvPolynomial.aeval x (MvPolynomial.monomial m (p.coeff m)), hWeights m (p.coeff m)⟩
  let Z : Π₀ t, V t := ∑ m ∈ p.support, DFinsupp.single (monomialWeight w m) (z m)
  let f : (Π₀ t, V t) →ₗ[k] A := DFinsupp.lsum ℕ (fun t => (V t).subtype)
  have hf : Function.Injective f := hV.dfinsupp_lsum_injective
  have hZ : Z = 0 := by
    apply hf
    rw [map_zero]
    change f (∑ m ∈ p.support, DFinsupp.single (monomialWeight w m) (z m)) = 0
    simpa only [map_sum, f, DFinsupp.lsum_single, Submodule.subtype_apply, z] using
      (show (∑ m ∈ p.support, MvPolynomial.aeval x (MvPolynomial.monomial m (p.coeff m))) = 0 from
        (map_sum (MvPolynomial.aeval x) _ _).symm.trans
          ((congrArg (MvPolynomial.aeval x) p.as_sum.symm).trans hp))
  let g : (Π₀ t, V t) →ₗ[k] MonoidAlgebra k (Multiplicative Λ) := DFinsupp.lsum ℕ
    (fun t => (LinearMap.toSpanSingleton k _ (weightCharacter k t)).comp
      (ε.toLinearMap.comp (V t).subtype))
  have hg := congrArg g hZ
  rw [map_zero] at hg
  change g (∑ m ∈ p.support, DFinsupp.single (monomialWeight w m) (z m)) = 0 at hg
  simp only [map_sum, g, DFinsupp.lsum_single, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
    AlgHom.toLinearMap_apply, Submodule.subtype_apply, z] at hg
  rw [p.as_sum, map_sum]
  simpa only [weighted_aeval_monomial] using hg

private theorem algHom_ext_of_aeval_surjective {C : Type*} [CommRing C] [Algebra k C]
    (x : σ → A) (hEv : Function.Surjective (MvPolynomial.aeval (R := k) x))
    {g₁ g₂ : A →ₐ[k] C} (hg : ∀ i, g₁ (x i) = g₂ (x i)) : g₁ = g₂ := by
  have h : g₁.comp (MvPolynomial.aeval x) = g₂.comp (MvPolynomial.aeval x) :=
    MvPolynomial.algHom_ext fun i => by simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X] using hg i
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := hEv a
  exact DFunLike.congr_fun h p

end WeightedEvaluation

section Diagonal

variable {k H ι W : Type*} [Field k] [CommRing H] [Bialgebra k H] [AddCommGroup W]

/-- The additive character lattice generated by the diagonal entries of an
infinitesimal matrix. -/
def diagonalCharacterLattice (d : ι → W) : AddSubgroup W :=
  AddSubgroup.closure (Set.range d)

/-- A distinguished character corresponding to a diagonal entry. -/
def diagonalCharacter (d : ι → W) (i : ι) : diagonalCharacterLattice d :=
  ⟨d i, AddSubgroup.subset_closure (Set.mem_range_self i)⟩

/-- The coordinate algebra of the diagonal subgroup attached to the
infinitesimal weights. -/
abbrev diagonalWeightAlgebra (k : Type*) [Field k] (d : ι → W) :=
  MonoidAlgebra k (Multiplicative (diagonalCharacterLattice d))

/-- The coordinate algebra for scalar weights. -/
abbrev diagonalCharacterAlgebra (d : ι → k) :=
  diagonalWeightAlgebra k d

/-- The distinguished character as a monomial of the diagonal coordinate algebra. -/
def diagonalWeightMonomial (k : Type*) [Field k] (d : ι → W) (i : ι) : diagonalWeightAlgebra k d :=
  MonoidAlgebra.of k _ (Multiplicative.ofAdd (diagonalCharacter d i))

/-- The distinguished character for a scalar weight. -/
abbrev diagonalCharacterMonomial (d : ι → k) (i : ι) : diagonalCharacterAlgebra d :=
  diagonalWeightMonomial k d i

/-- In characteristic zero the finitely generated subgroup of infinitesimal
weights is a finite free character lattice. -/
theorem diagonalWeightLattice_exists_basis [NoZeroSMulDivisors ℤ W] [Finite ι] (d : ι → W) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) ℤ (diagonalCharacterLattice d)) := by
  letI : Finite (Set.range d) := Finite.of_surjective
    (fun i => ⟨d i, Set.mem_range_self i⟩) (by rintro ⟨_, i, rfl⟩; exact ⟨i, rfl⟩)
  letI : AddGroup.FG (diagonalCharacterLattice d) := AddGroup.closure_finite_fg (Set.range d)
  letI : Module.Finite ℤ (diagonalCharacterLattice d) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : NoZeroSMulDivisors ℤ (diagonalCharacterLattice d) := ⟨fun {n a} h => by
    have h' : n • (a : W) = 0 := congrArg Subtype.val h
    exact (smul_eq_zero.mp h').imp id Subtype.ext⟩
  letI : Module.Free ℤ (diagonalCharacterLattice d) := Module.free_of_finite_type_torsion_free'
  exact ⟨_, ⟨Module.finBasis ℤ (diagonalCharacterLattice d)⟩⟩

theorem diagonalCharacterLattice_exists_basis [CharZero k] [Finite ι] (d : ι → k) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) ℤ (diagonalCharacterLattice d)) := by
  letI := NoZeroSMulDivisors.int_of_charZero k k
  exact diagonalWeightLattice_exists_basis d

/-- The infinitesimal point associated to an additive functional on the weights. -/
def diagonalWeightInfinitesimalPoint (d : ι → W) (q : W →+ k) :
    diagonalWeightAlgebra k d →ₐ[k] DualNumber k :=
  MonoidAlgebra.lift k _ _ {
    toFun := fun a => (1, q ((Multiplicative.toAdd a : diagonalCharacterLattice d) : W))
    map_one' := by
      change (1, q 0) = (1 : DualNumber k)
      rw [map_zero]
      rfl
    map_mul' := fun a b => by
      apply TrivSqZeroExt.ext
      · change (1 : k) = 1 * 1
        simp only [mul_one]
      · rw [DualNumber.snd_mul]
        change q (a.toAdd.val + b.toAdd.val) = 1 * q b.toAdd.val + q a.toAdd.val * 1
        rw [map_add, one_mul, mul_one, add_comm] }

@[simp] theorem diagonalWeightInfinitesimalPoint_of (d : ι → W) (q : W →+ k)
    (a : Multiplicative (diagonalCharacterLattice d)) :
    diagonalWeightInfinitesimalPoint d q (MonoidAlgebra.of k _ a) = (1, q a.toAdd.val) :=
  MonoidAlgebra.lift_of _ _

@[simp] theorem diagonalWeightInfinitesimalPoint_monomial (d : ι → W) (q : W →+ k) (i : ι) :
    diagonalWeightInfinitesimalPoint d q (diagonalWeightMonomial k d i) = (1, q (d i)) :=
  diagonalWeightInfinitesimalPoint_of d q (Multiplicative.ofAdd (diagonalCharacter d i))

@[simp] theorem diagonalWeightInfinitesimalPoint_fst (d : ι → W) (q : W →+ k)
    (a : diagonalWeightAlgebra k d) :
    (diagonalWeightInfinitesimalPoint d q a).fst = Coalgebra.counit (R := k) a := by
  let f := (TrivSqZeroExt.fstHom k k k).comp (diagonalWeightInfinitesimalPoint d q)
  have h : f = Bialgebra.counitAlgHom k (diagonalWeightAlgebra k d) := by
    apply MonoidAlgebra.algHom_ext
    intro g
    change (diagonalWeightInfinitesimalPoint d q (MonoidAlgebra.of k _ g)).fst = _
    rw [diagonalWeightInfinitesimalPoint_of]
    exact (counit_monoidAlgebra_of g).symm
  exact DFunLike.congr_fun h a

/-- The infinitesimal torus point for scalar weights sends λ to 1 + ελ. -/
abbrev diagonalCharacterInfinitesimalPoint (d : ι → k) :
    diagonalCharacterAlgebra d →ₐ[k] DualNumber k :=
  diagonalWeightInfinitesimalPoint d (AddMonoidHom.id k)

@[simp] theorem diagonalCharacterInfinitesimalPoint_of (d : ι → k)
    (a : Multiplicative (diagonalCharacterLattice d)) :
    diagonalCharacterInfinitesimalPoint d (MonoidAlgebra.of k _ a) =
      (1, (a.toAdd : diagonalCharacterLattice d).val) :=
  diagonalWeightInfinitesimalPoint_of d (AddMonoidHom.id k) a

@[simp] theorem diagonalCharacterInfinitesimalPoint_monomial (d : ι → k) (i : ι) :
    diagonalCharacterInfinitesimalPoint d (diagonalCharacterMonomial d i) = (1, d i) :=
  diagonalCharacterInfinitesimalPoint_of d (Multiplicative.ofAdd (diagonalCharacter d i))

@[simp] theorem diagonalCharacterInfinitesimalPoint_fst (d : ι → k)
    (a : diagonalCharacterAlgebra d) :
    (diagonalCharacterInfinitesimalPoint d a).fst = Coalgebra.counit (R := k) a :=
  diagonalWeightInfinitesimalPoint_fst d (AddMonoidHom.id k) a

/-- The actual Lie vector of the diagonal torus associated to its weights. -/
def diagonalCharacterLieVector (d : ι → k) :
    HopfLieVector k (diagonalCharacterAlgebra d) k :=
  (hopfInfinitesimalPointEquiv k (diagonalCharacterAlgebra d) k).symm
    ⟨diagonalCharacterInfinitesimalPoint d, fun a => diagonalCharacterInfinitesimalPoint_fst d a⟩

@[simp] theorem diagonalCharacterLieVector_projection (d : ι → k) (a : diagonalCharacterAlgebra d) :
    diagonalCharacterLieVector d (hopfCotangentProjection k (diagonalCharacterAlgebra d) a) =
      (diagonalCharacterInfinitesimalPoint d a).snd := by
  let p : HopfInfinitesimalPoint k (diagonalCharacterAlgebra d) k :=
    ⟨diagonalCharacterInfinitesimalPoint d, fun a => diagonalCharacterInfinitesimalPoint_fst d a⟩
  exact congrArg (fun z : HopfInfinitesimalPoint k (diagonalCharacterAlgebra d) k => (z.val a).snd)
    ((hopfInfinitesimalPointEquiv k (diagonalCharacterAlgebra d) k).apply_symm_apply p)

variable [Fintype ι] [DecidableEq ι]

private theorem exists_diagonalWeightQuotient
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (d : ι → W) (V : diagonalCharacterLattice d → Submodule k H) (hV : iSupIndep V)
    (hWeights : ∀ (m : (ι × ι) →₀ ℕ) (c : k), MvPolynomial.aeval (fun ij : ι × ι => U.val ij.1 ij.2)
      (MvPolynomial.monomial m c) ∈ V (monomialWeight (fun ij => diagonalCharacter d ij.2) m)) :
    ∃ f : H →ₐc[k] diagonalWeightAlgebra k d, Function.Surjective f ∧
      ∀ i j, f (U.val i j) = if i = j then diagonalWeightMonomial k d i else 0 := by
  classical
  let Λ := diagonalCharacterLattice d
  let B := diagonalWeightAlgebra k d
  let x (ij : ι × ι) := U.val ij.1 ij.2
  let w (ij : ι × ι) := diagonalCharacter d ij.2
  let ε := Bialgebra.counitAlgHom k H
  let ev := MvPolynomial.aeval (R := k) x
  let eχ : MvPolynomial (ι × ι) k →ₐ[k] B :=
    MvPolynomial.aeval (fun ij => ε (x ij) • weightCharacter k (w ij))
  have hEv : Function.Surjective ev := by
    apply (AlgHom.range_eq_top _).mp
    exact (Algebra.adjoin_range_eq_range_aeval k x).symm.trans hGen
  let I : Ideal (MvPolynomial (ι × ι) k) := RingHom.ker ev
  have hKer (p : MvPolynomial (ι × ι) k) (hp : p ∈ I) : eχ p = 0 :=
    weighted_aeval_eq_zero_of_aeval_eq_zero x ε w V hV hWeights p (RingHom.mem_ker.mp hp)
  let e : (MvPolynomial (ι × ι) k ⧸ I) ≃ₐ[k] H :=
    Ideal.quotientKerAlgEquivOfSurjective (f := ev) hEv
  let f : H →ₐ[k] B := (Ideal.Quotient.liftₐ I eχ hKer).comp e.symm.toAlgHom
  have hf (p : MvPolynomial (ι × ι) k) : f (ev p) = eχ p := by
    change Ideal.Quotient.liftₐ I eχ hKer (e.symm (ev p)) = _
    rw [show e.symm (ev p) = Ideal.Quotient.mkₐ k I p from e.symm_apply_eq.mpr (Ideal.kerLiftAlg_mk ev p)]
    exact DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I eχ hKer) p
  have hfU (i j : ι) : f (U.val i j) =
      if i = j then diagonalWeightMonomial k d i else 0 := by
    have h := hf (MvPolynomial.X (i, j))
    simp only [ev, eχ, MvPolynomial.aeval_X, x, w] at h
    change f (U.val i j) = Coalgebra.counit (R := k) (U.val i j) •
      weightCharacter k (diagonalCharacter d j) at h
    rw [h, hε]
    by_cases hij : i = j
    · subst j
      simp only [if_true, one_smul]
      rfl
    · simp only [if_neg hij, zero_smul]
  have hCounit : (Bialgebra.counitAlgHom k B).comp f = ε := by
    apply algHom_ext_of_aeval_surjective x hEv
    rintro ⟨i, j⟩
    change Coalgebra.counit (R := k) (f (U.val i j)) = Coalgebra.counit (R := k) (U.val i j)
    rw [hfU, hε]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos hij]
      exact counit_monoidAlgebra_of _
    · rw [if_neg hij, if_neg hij, map_zero]
  have hComul : (Bialgebra.comulAlgHom k B).comp f =
      (Algebra.TensorProduct.map f f).comp (Bialgebra.comulAlgHom k H) := by
    apply algHom_ext_of_aeval_surjective x hEv
    rintro ⟨i, j⟩
    change Coalgebra.comul (R := k) (f (U.val i j)) =
      Algebra.TensorProduct.map f f (Coalgebra.comul (R := k) (U.val i j))
    rw [hΔ, map_sum]
    simp_rw [Algebra.TensorProduct.map_tmul, hfU]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, Finset.sum_eq_single i]
      · simp only [if_pos rfl]
        exact comul_monoidAlgebra_of _
      · intro l _ hl
        rw [if_neg (Ne.symm hl), TensorProduct.zero_tmul]
      · exact fun h => (h (Finset.mem_univ _)).elim
    · rw [if_neg hij, map_zero]
      symm
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : i = l
      · subst l
        simp only [if_true, if_neg hij, TensorProduct.tmul_zero]
      · rw [if_neg hil, TensorProduct.zero_tmul]
  let ψ : H →ₐc[k] B := BialgHom.ofAlgHom f
    (LinearMap.ext fun a => DFunLike.congr_fun hCounit a)
    (LinearMap.ext fun a => DFunLike.congr_fun hComul.symm a)
  have hNegative (i : ι) : f (U.inv i i) = weightCharacter k (-(diagonalCharacter d i)) := by
    let a := diagonalCharacter d i
    have h := congrArg (fun M : Matrix ι ι H => f (M i i)) U.val_inv
    change f (∑ l, U.val i l * U.inv l i) = f ((1 : Matrix ι ι H) i i) at h
    simp only [map_sum, map_mul, Matrix.one_apply_eq, map_one, hfU] at h
    rw [Finset.sum_eq_single i] at h
    · rw [if_pos rfl] at h
      change weightCharacter k a * f (U.inv i i) = 1 at h
      calc
        f (U.inv i i) = (weightCharacter k (-a) * weightCharacter k a) * f (U.inv i i) := by
          rw [← weightCharacter_add, neg_add_cancel, weightCharacter_zero, one_mul]
        _ = weightCharacter k (-a) := by rw [mul_assoc, h, mul_one]
    · intro l _ hl
      rw [if_neg (Ne.symm hl), zero_mul]
    · exact fun hn => (hn (Finset.mem_univ _)).elim
  have hRange (a : Λ) : weightCharacter k a ∈ f.range := by
    refine AddSubgroup.closure_induction_left
      (p := fun a ha => weightCharacter k (⟨a, ha⟩ : Λ) ∈ f.range) ?_ ?_ ?_ a.prop
    · change weightCharacter k (0 : Λ) ∈ f.range
      rw [weightCharacter_zero]
      exact f.range.one_mem
    · rintro _ ⟨i, rfl⟩ y hy ih
      change weightCharacter k (diagonalCharacter d i + (⟨y, hy⟩ : Λ)) ∈ f.range
      rw [weightCharacter_add]
      exact f.range.mul_mem ⟨U.val i i, (hfU i i).trans (if_pos rfl)⟩ ih
    · rintro _ ⟨i, rfl⟩ y hy ih
      change weightCharacter k (-(diagonalCharacter d i) + (⟨y, hy⟩ : Λ)) ∈ f.range
      rw [weightCharacter_add]
      exact f.range.mul_mem ⟨U.inv i i, hNegative i⟩ ih
  have hSurj : Function.Surjective f := by
    intro a
    change a ∈ f.range
    exact MonoidAlgebra.induction_on a (fun g => hRange (Multiplicative.toAdd g))
      (fun _ _ => f.range.add_mem) (fun r _ h => f.range.smul_mem h r)
  exact ⟨ψ, hSurj, hfU⟩

/-- Generalized column weights determine a diagonal subgroup of the actual group. -/
theorem exists_diagonalTorus_of_genEigenspace
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : Derivation k H H) (d : ι → k)
    (hD : ∀ i j, U.val i j ∈ Module.End.maxGenEigenspace D.toLinearMap (d j)) :
    ∃ f : H →ₐc[k] diagonalCharacterAlgebra d, Function.Surjective f ∧
      ∀ i j, f (U.val i j) = if i = j then diagonalCharacterMonomial d i else 0 := by
  let V (a : diagonalCharacterLattice d) := Module.End.maxGenEigenspace D.toLinearMap (a : k)
  have hV : iSupIndep V := (Module.End.independent_maxGenEigenspace D.toLinearMap).comp Subtype.val_injective
  apply exists_diagonalWeightQuotient U hΔ hε hGen d V hV
  intro m c
  let a : diagonalCharacterLattice d →+ k := (diagonalCharacterLattice d).subtype
  change _ ∈ Module.End.maxGenEigenspace D.toLinearMap
    (a (monomialWeight (fun ij : ι × ι => diagonalCharacter d ij.2) m))
  simpa only [monomialWeight, Finsupp.sum, map_sum, map_nsmul] using
    aeval_monomial_mem_derivation_maxGenEigenspace D (fun ij : ι × ι => hD ij.1 ij.2) m c

/-- Simultaneous generalized weights of commuting derivations determine a single diagonal subgroup. -/
theorem exists_diagonalTorus_of_simultaneousWeights {τ : Type*}
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : τ → Derivation k H H) (d : ι → τ → k)
    (hComm : ∀ r s, Commute (D r).toLinearMap (D s).toLinearMap)
    (hD : ∀ r i j, U.val i j ∈ Module.End.maxGenEigenspace (D r).toLinearMap (d j r)) :
    ∃ f : H →ₐc[k] diagonalWeightAlgebra k d, Function.Surjective f ∧
      ∀ i j, f (U.val i j) = if i = j then diagonalWeightMonomial k d i else 0 := by
  let V (a : diagonalCharacterLattice d) := ⨅ r : τ,
    Module.End.maxGenEigenspace (D r).toLinearMap ((a : τ → k) r)
  have hV : iSupIndep V := (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun r => (D r).toLinearMap) fun r s a =>
      Module.End.mapsTo_maxGenEigenspace_of_comm (hComm s r) a).comp Subtype.val_injective
  apply exists_diagonalWeightQuotient U hΔ hε hGen d V hV
  intro m c
  rw [show V (monomialWeight (fun ij : ι × ι => diagonalCharacter d ij.2) m) = _ from rfl,
    Submodule.mem_iInf]
  intro r
  let a : diagonalCharacterLattice d →+ k :=
    (Pi.evalAddMonoidHom (fun _ : τ => k) r).comp (diagonalCharacterLattice d).subtype
  change _ ∈ Module.End.maxGenEigenspace (D r).toLinearMap
    (a (monomialWeight (fun ij : ι × ι => diagonalCharacter d ij.2) m))
  simpa only [monomialWeight, Finsupp.sum, map_sum, map_nsmul] using
    aeval_monomial_mem_derivation_maxGenEigenspace (D r) (fun ij : ι × ι => hD r ij.1 ij.2) m c

/-- A diagonal infinitesimal matrix in a generating representation determines a
surjective map to the actual coordinate bialgebra of a diagonal subgroup. -/
theorem exists_diagonalDerivationTorus
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (D : Derivation k H H) (d : ι → k)
    (hD : ∀ i j, D (U.val i j) = d j • U.val i j) :
    ∃ f : H →ₐc[k] diagonalCharacterAlgebra d, Function.Surjective f ∧
      ∀ i j, f (U.val i j) = if i = j then diagonalCharacterMonomial d i else 0 := by
  apply exists_diagonalTorus_of_genEigenspace U hΔ hε hGen D d
  intro i j
  refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨1, ?_⟩
  rw [pow_one]
  change D (U.val i j) - d j • U.val i j = 0
  rw [hD, sub_self]

omit [Fintype ι] in
/-- On the original generating matrix, the tangent vector of the diagonal
subgroup is the prescribed diagonal matrix. -/
theorem diagonalCharacterLieVector_on_matrix
    (U : Matrix ι ι H) (d : ι → k) (f : H →ₐc[k] diagonalCharacterAlgebra d)
    (hf : ∀ i j, f (U i j) = if i = j then diagonalCharacterMonomial d i else 0)
    (i j : ι) :
    diagonalCharacterLieVector d (hopfCotangentProjection k (diagonalCharacterAlgebra d) (f (U i j))) =
      if i = j then d i else 0 := by
  rw [diagonalCharacterLieVector_projection, hf]
  by_cases hij : i = j
  · simp only [if_pos hij, diagonalCharacterInfinitesimalPoint_monomial, TrivSqZeroExt.snd_mk]
  · simp only [if_neg hij, map_zero, TrivSqZeroExt.snd_zero]

end Diagonal

end WideE
