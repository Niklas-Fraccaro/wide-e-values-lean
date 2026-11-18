import WideE.AdjointSliceDescent
import WideE.FinitePointPresentation
import WideE.FinitePointTransfer
import WideE.LieMatrixCentralizer

/-! The normalization of a Cartan term to an affine adjoint slice as a
finite polynomial relation over the original field. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section Matrices

variable {k A B ι τ : Type*} [Field k] [CommRing A] [Algebra k A]
  [CommRing B] [Algebra k B] [Fintype τ]

/-- A linear family of constant matrices evaluated with coefficients in an extension algebra. -/
def linearMatrixFamily (m : τ → Matrix ι ι k) (a : τ → A) : Matrix ι ι A :=
  ∑ j, a j • (m j).map (algebraMap k A)

private theorem linearMatrixFamily_map (m : τ → Matrix ι ι k) (a : τ → A) (p : A →ₐ[k] B) :
    (linearMatrixFamily m a).map p = linearMatrixFamily m (p ∘ a) := by
  apply Matrix.ext
  intro i j
  simp only [linearMatrixFamily, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, AlgHom.commutes, Function.comp_apply]

variable {H : Type*} [CommRing H] [HopfAlgebra k H]

private theorem hopfCotangentMatrix_slice {E : Type*} [Field E] [Algebra k E] (U : Matrix ι ι H) (e : HopfLieVector k H k)
    (v : τ → HopfLieVector k H k) (a : τ → E) :
    hopfCotangentMatrix U (hopfAdjointSlice e v a) =
      (hopfCotangentMatrix U e).map (algebraMap k E) +
        linearMatrixFamily (fun j => hopfCotangentMatrix U (v j)) a := by
  apply Matrix.ext
  intro i j
  simp only [hopfCotangentMatrix, hopfAdjointSlice, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, Algebra.ofId_apply,
    Matrix.add_apply, Matrix.map_apply, linearMatrixFamily, Matrix.sum_apply, Matrix.smul_apply]

variable [Fintype ι] [DecidableEq ι]

/-- An adjoint equation is a matrix intertwining equation in a generating representation. -/
theorem hopfAdjoint_eq_iff_matrix_intertwines (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (p : H →ₐ[k] A) (x y : HopfLieVector k H A) :
    hopfAdjoint p x = y ↔
      U.val.map p * hopfCotangentMatrix U.val x = hopfCotangentMatrix U.val y * U.val.map p := by
  let M := hopfPointMatrix U hΔ hε p
  let X := hopfCotangentMatrix U.val x
  let Y := hopfCotangentMatrix U.val y
  have hAd : hopfCotangentMatrix U.val (hopfAdjoint p x) = M.val * X * M.inv :=
    hopfCotangentMatrix_adjoint U hΔ hε p x
  change hopfAdjoint p x = y ↔ M.val * X = Y * M.val
  constructor
  · intro h
    rw [h] at hAd
    simpa only [Matrix.mul_assoc, M.inv_val, Matrix.mul_one] using
      (congrArg (fun T : Matrix ι ι A => T * M.val) hAd).symm
  · intro h
    apply hopfCotangentMatrix_injective U.val hGen
    rw [hAd, h, Matrix.mul_assoc, M.val_inv, Matrix.mul_one]

end Matrices

section Normalization

variable {k H ι τ η ν : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype η] [Fintype ν]

local notation "𝔤" => HopfLieVector k H
local notation "W" => τ ⊕ (η ⊕ (ν ⊕ ((ι × ι) ⊕ (ι × ι))))
local notation "W'" => η ⊕ (ν ⊕ ((ι × ι) ⊕ (ι × ι)))

/-- Both points witnessing a negative normalization and its Cartan conjugacy. -/
def HopfSliceNormalization {A : Type*} [Field A] [Algebra k A]
    (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k)
    (N : ν → Matrix ι ι k) (a : τ → A) (s : η → A) : Prop :=
  ∃ (p q : H →ₐ[k] A) (n : ν → A),
    U.val.map p = 1 + linearMatrixFamily N n ∧
    hopfAdjoint p (hopfAdjointSlice e v a) = hopfAdjointSlice e w s ∧
    hopfAdjoint q (hopfAdjointSlice e w s) = hopfAdjointSlice 0 v a

private def normalizationCartanIndex (i : τ) : W := Sum.inl i
private def normalizationSliceIndex (i : η) : W := Sum.inr (Sum.inl i)
private def normalizationNegativeIndex (i : ν) : W := Sum.inr (Sum.inr (Sum.inl i))
private def normalizationFirstPointIndex (i : ι × ι) : W := Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
private def normalizationSecondPointIndex (i : ι × ι) : W := Sum.inr (Sum.inr (Sum.inr (Sum.inr i)))

private def polynomialMatrixVariables {V : Type*} (f : ι × ι → V) : Matrix ι ι (MvPolynomial V k) :=
  fun i j => MvPolynomial.X (f (i, j))

private def polynomialSliceMatrix (U : Matrix ι ι H) (e : 𝔤 k) {σ V : Type*} [Fintype σ]
    (v : σ → 𝔤 k) (f : σ → V) : Matrix ι ι (MvPolynomial V k) :=
  (hopfCotangentMatrix U e).map (algebraMap k _) +
    linearMatrixFamily (fun j => hopfCotangentMatrix U (v j)) (MvPolynomial.X (R := k) ∘ f)

omit [Fintype ι] [DecidableEq ι] in
private theorem polynomialSliceMatrix_aeval {A V σ : Type*}
    [Field A] [Algebra k A] [Fintype σ]
    (U : Matrix ι ι H) (e : 𝔤 k) (v : σ → 𝔤 k) (f : σ → V) (a : V → A) :
    (polynomialSliceMatrix U e v f).map (MvPolynomial.aeval a) =
      hopfCotangentMatrix U (hopfAdjointSlice e v (a ∘ f)) := by
  have hEval : ⇑(MvPolynomial.aeval a) ∘ MvPolynomial.X (R := k) ∘ f = a ∘ f :=
    funext fun j => MvPolynomial.aeval_X a (f j)
  rw [polynomialSliceMatrix, Matrix.map_add _ (map_add _), linearMatrixFamily_map, hEval,
    hopfCotangentMatrix_slice]
  congr 1
  exact Matrix.ext fun _ _ => AlgHom.commutes (MvPolynomial.aeval a) _

private def matrixEntryRange {R : Type*} (M : Matrix ι ι R) : Set R :=
  Set.range fun ij : ι × ι => M ij.1 ij.2

omit [Fintype ι] [DecidableEq ι] in
private theorem matrixEntryRange_aeval_eq_zero {V A : Type*} [Field A] [Algebra k A]
    (M : Matrix ι ι (MvPolynomial V k)) (a : V → A) :
    (∀ P ∈ matrixEntryRange M, MvPolynomial.aeval a P = 0) ↔ M.map (MvPolynomial.aeval a) = 0 := by
  constructor
  · intro h
    exact Matrix.ext fun i j => h _ ⟨(i, j), rfl⟩
  · rintro h _ ⟨⟨i, j⟩, rfl⟩
    exact congrArg (fun T : Matrix ι ι A => T i j) h

omit [DecidableEq ι] in
private theorem algHom_map_matrix_mul {A V : Type*} [CommRing A] [Algebra k A]
    (f : MvPolynomial V k →ₐ[k] A) (M N : Matrix ι ι (MvPolynomial V k)) :
    (M * N).map f = M.map f * N.map f :=
  Matrix.map_mul (f := f.toRingHom)

omit [Fintype ι] [DecidableEq ι] in
private theorem linearMatrixFamily_aeval {A V σ : Type*} [CommRing A] [Algebra k A] [Fintype σ]
    (N : σ → Matrix ι ι k) (f : σ → V) (z : V → A) :
    (linearMatrixFamily N (MvPolynomial.X (R := k) ∘ f)).map (MvPolynomial.aeval z) =
      linearMatrixFamily N (z ∘ f) := by
  rw [linearMatrixFamily_map]
  exact congrArg (linearMatrixFamily N) (funext fun j => MvPolynomial.aeval_X z (f j))

private def normalizationEquations (Γ : Finset (MvPolynomial (ι × ι) k))
    (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) :
    Set (MvPolynomial W k) :=
  let Pneg := polynomialMatrixVariables (k := k) (normalizationFirstPointIndex : ι × ι → W)
  let Ppos := polynomialMatrixVariables (k := k) (normalizationSecondPointIndex : ι × ι → W)
  let C := polynomialSliceMatrix U.val 0 v (normalizationCartanIndex : τ → W)
  let Cₑ := polynomialSliceMatrix U.val e v (normalizationCartanIndex : τ → W)
  let S := polynomialSliceMatrix U.val e w (normalizationSliceIndex : η → W)
  let B := linearMatrixFamily N (MvPolynomial.X (R := k) ∘ (normalizationNegativeIndex : ν → W))
  (MvPolynomial.rename normalizationFirstPointIndex '' (↑Γ : Set _)) ∪
    (MvPolynomial.rename normalizationSecondPointIndex '' (↑Γ : Set _)) ∪
    matrixEntryRange (Pneg - (1 + B)) ∪
    matrixEntryRange (Pneg * Cₑ - S * Pneg) ∪ matrixEntryRange (Ppos * S - C * Ppos)

private theorem normalizationEquations_iff {A : Type*} [Field A] [Algebra k A]
    (Γ : Finset (MvPolynomial (ι × ι) k)) (U : (Matrix ι ι H)ˣ)
    (hΓ : ∀ a : ι × ι → A, (∀ P ∈ Γ, MvPolynomial.aeval a P = 0) ↔
      ∃! p : H →ₐ[k] A, ∀ ij, p (U.val ij.1 ij.2) = a ij)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) (z : W → A)
    (hz : ∀ P ∈ normalizationEquations Γ U e v w N, MvPolynomial.aeval z P = 0) :
    HopfSliceNormalization U e v w N (z ∘ normalizationCartanIndex) (z ∘ normalizationSliceIndex) := by
  simp only [normalizationEquations, Set.mem_union, or_imp, forall_and, Set.forall_mem_image,
    MvPolynomial.aeval_rename, Finset.mem_coe, hΓ, matrixEntryRange_aeval_eq_zero] at hz
  obtain ⟨⟨⟨⟨⟨p, hp, _⟩, ⟨q, hq, _⟩⟩, hB⟩, hpC⟩, hqC⟩ := hz
  have hP : (polynomialMatrixVariables (k := k) (normalizationFirstPointIndex : ι × ι → W)).map
      (MvPolynomial.aeval z) = U.val.map p :=
    Matrix.ext fun i j => (MvPolynomial.aeval_X z _).trans (hp (i, j)).symm
  have hQ : (polynomialMatrixVariables (k := k) (normalizationSecondPointIndex : ι × ι → W)).map
      (MvPolynomial.aeval z) = U.val.map q :=
    Matrix.ext fun i j => (MvPolynomial.aeval_X z _).trans (hq (i, j)).symm
  simp only [Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), hP, linearMatrixFamily_aeval, sub_eq_zero] at hB
  simp only [Matrix.map_sub _ (map_sub _), algHom_map_matrix_mul,
    hP, hQ, polynomialSliceMatrix_aeval, sub_eq_zero] at hpC hqC
  exact ⟨p, q, _, hB, (hopfAdjoint_eq_iff_matrix_intertwines U hΔ hε hGen _ _ _).mpr hpC,
    (hopfAdjoint_eq_iff_matrix_intertwines U hΔ hε hGen _ _ _).mpr hqC⟩

private theorem normalizationEquations_of_normalization {A : Type*} [Field A] [Algebra k A]
    (Γ : Finset (MvPolynomial (ι × ι) k)) (U : (Matrix ι ι H)ˣ)
    (hΓ : ∀ a : ι × ι → A, (∀ P ∈ Γ, MvPolynomial.aeval a P = 0) ↔
      ∃! p : H →ₐ[k] A, ∀ ij, p (U.val ij.1 ij.2) = a ij)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) (a : τ → A) (s : η → A)
    (h : HopfSliceNormalization U e v w N a s) :
    ∃ z : W' → A, z ∘ Sum.inl = s ∧
      ∀ P ∈ normalizationEquations Γ U e v w N, MvPolynomial.aeval (Sum.elim a z) P = 0 := by
  obtain ⟨p, q, n, hB, hp, hq⟩ := h
  let u (ij : ι × ι) := p (U.val ij.1 ij.2)
  let t (ij : ι × ι) := q (U.val ij.1 ij.2)
  let z : W' → A := Sum.elim s (Sum.elim n (Sum.elim u t))
  let r : W → A := Sum.elim a z
  have hU (g : H →ₐ[k] A) : ∃! g' : H →ₐ[k] A, ∀ ij : ι × ι, g' (U.val ij.1 ij.2) = g (U.val ij.1 ij.2) := by
    refine ⟨g, fun _ => rfl, fun g' h => ?_⟩
    apply AlgHom.ext_of_adjoin_eq_top hGen
    rintro _ ⟨ij, rfl⟩
    exact h ij
  refine ⟨z, rfl, ?_⟩
  change ∀ P ∈ normalizationEquations Γ U e v w N, MvPolynomial.aeval r P = 0
  have hP : (polynomialMatrixVariables (k := k) (normalizationFirstPointIndex : ι × ι → W)).map
      (MvPolynomial.aeval r) = U.val.map p :=
    Matrix.ext fun i j => MvPolynomial.aeval_X r _
  have hQ : (polynomialMatrixVariables (k := k) (normalizationSecondPointIndex : ι × ι → W)).map
      (MvPolynomial.aeval r) = U.val.map q :=
    Matrix.ext fun i j => MvPolynomial.aeval_X r _
  simp only [normalizationEquations, Set.mem_union, or_imp, forall_and, Set.forall_mem_image,
    MvPolynomial.aeval_rename, Finset.mem_coe, hΓ, matrixEntryRange_aeval_eq_zero,
    Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
    Matrix.map_one _ (map_zero _) (map_one _), algHom_map_matrix_mul,
    hP, hQ, linearMatrixFamily_aeval, polynomialSliceMatrix_aeval, sub_eq_zero]
  exact ⟨⟨⟨⟨hU p, hU q⟩, hB⟩, (hopfAdjoint_eq_iff_matrix_intertwines U hΔ hε hGen _ _ _).mp hp⟩,
    (hopfAdjoint_eq_iff_matrix_intertwines U hΔ hε hGen _ _ _).mp hq⟩

/-- Normalization on a principal open over the algebraically closed ground
field extends to every algebraically closed coefficient field on that open. -/
theorem exists_hopfSliceNormalization_to_algClosed {A : Type*}
    [IsAlgClosed k] [Field A] [IsAlgClosed A] [Algebra k A]
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k)
    (d : MvPolynomial τ k)
    (hLift : ∀ a : τ → k, MvPolynomial.aeval a d ≠ 0 →
      ∃ s : η → k, HopfSliceNormalization U e v w N a s)
    (a : τ → A) (ha : MvPolynomial.aeval a d ≠ 0) :
    ∃ s : η → A, HopfSliceNormalization U e v w N a s := by
  let u (ij : ι × ι) := U.val ij.1 ij.2
  obtain ⟨Γ, hΓ⟩ := IsNoetherian.noetherian (RingHom.ker (MvPolynomial.aeval (R := k) u).toRingHom)
  let S := normalizationEquations Γ U e v w N
  have hF (b : τ → k) (hb : MvPolynomial.aeval b d ≠ 0) :
      ∃ z : W' → k, ∀ P ∈ S, MvPolynomial.aeval (Sum.elim b z) P = 0 := by
    obtain ⟨s, hs⟩ := hLift b hb
    obtain ⟨z, _, hz⟩ := normalizationEquations_of_normalization Γ U
      (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N b s hs
    exact ⟨z, hz⟩
  obtain ⟨z, hz⟩ := exists_polynomial_solution_to_algClosed S d hF a ha
  let r : W → A := Sum.elim a z
  exact ⟨r ∘ normalizationSliceIndex,
    normalizationEquations_iff Γ U (finiteAlgHomPresentation_iff u hGen Γ hΓ)
      hΔ hε hGen e v w N r hz⟩

/-- The part of the affine slice represented by normalizations of Cartan points
in the selected principal open. -/
def normalizedHopfSlice {A : Type*} [Field A] [Algebra k A]
    (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k)
    (N : ν → Matrix ι ι k) (d : MvPolynomial τ k) : Set (𝔤 A) :=
  {y | ∃ (a : τ → A) (s : η → A), MvPolynomial.aeval a d ≠ 0 ∧
    HopfSliceNormalization U e v w N a s ∧ y = hopfAdjointSlice e w s}

private theorem hopfAdjointSlice_postcompose {A B : Type*} [Field A] [Algebra k A]
    [Field B] [Algebra k B] {σ : Type*} [Fintype σ]
    (p : A →ₐ[k] B) (e : 𝔤 k) (v : σ → 𝔤 k) (a : σ → A) :
    p.toLinearMap.comp (hopfAdjointSlice e v a) = hopfAdjointSlice e v (p ∘ a) := by
  apply LinearMap.ext
  intro z
  simp only [hopfAdjointSlice, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_add, map_sum, smul_eq_mul, map_mul,
    Algebra.ofId_apply, AlgHom.commutes, Function.comp_apply]

/-- Every injective scalar change preserves membership in the normalized slice. -/
theorem normalizedHopfSlice_postcompose {A B : Type*} [Field A] [Algebra k A]
    [Field B] [Algebra k B] (f : A →ₐ[k] B) (hf : Function.Injective f)
    (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k)
    (N : ν → Matrix ι ι k) (d : MvPolynomial τ k) {y : 𝔤 A}
    (hy : y ∈ normalizedHopfSlice U e v w N d) :
    f.toLinearMap.comp y ∈ normalizedHopfSlice U e v w N d := by
  rcases hy with ⟨a, s, ha, ⟨p, q, n, hB, hp, hq⟩, rfl⟩
  refine ⟨f ∘ a, f ∘ s, ?_, ⟨f.comp p, f.comp q, f ∘ n, ?_, ?_, ?_⟩,
    hopfAdjointSlice_postcompose f e w s⟩
  · change MvPolynomial.aeval (fun i => f (a i)) d ≠ 0
    rw [← MvPolynomial.comp_aeval_apply]
    exact fun h => ha (hf (h.trans (map_zero f).symm))
  · have h := congrArg (fun M : Matrix ι ι A => M.map f) hB
    simpa only [Matrix.map_map, Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _),
      linearMatrixFamily_map, AlgHom.coe_comp] using h
  · have h := congrArg (fun x : 𝔤 A => f.toLinearMap.comp x) hp
    change f.toLinearMap.comp (hopfAdjoint p (hopfAdjointSlice e v a)) =
      f.toLinearMap.comp (hopfAdjointSlice e w s) at h
    rw [hopfAdjoint_postcompose, hopfAdjointSlice_postcompose, hopfAdjointSlice_postcompose] at h
    exact h
  · have h := congrArg (fun x : 𝔤 A => f.toLinearMap.comp x) hq
    change f.toLinearMap.comp (hopfAdjoint q (hopfAdjointSlice e w s)) =
      f.toLinearMap.comp (hopfAdjointSlice 0 v a) at h
    rw [hopfAdjoint_postcompose, hopfAdjointSlice_postcompose, hopfAdjointSlice_postcompose] at h
    exact h

local notation "W₂" => W ⊕ (W ⊕ (ι × ι))

private def normalizationConjugacyPointIndex (i : ι × ι) : W₂ := Sum.inr (Sum.inr i)
private def normalizationConjugacySecondIndex (i : W) : W₂ := Sum.inr (Sum.inl i)

private def normalizationConjugacyEquations (Γ : Finset (MvPolynomial (ι × ι) k))
    (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) :
    Set (MvPolynomial W₂ k) :=
  let T := normalizationEquations Γ U e v w N
  let G := polynomialMatrixVariables (k := k) (normalizationConjugacyPointIndex : ι × ι → W₂)
  let S := polynomialSliceMatrix U.val e w
    ((Sum.inl : W → W₂) ∘ normalizationSliceIndex)
  let S' := polynomialSliceMatrix U.val e w
    (normalizationConjugacySecondIndex ∘ (normalizationSliceIndex : η → W))
  (MvPolynomial.rename Sum.inl '' T) ∪ (MvPolynomial.rename normalizationConjugacySecondIndex '' T) ∪
    (MvPolynomial.rename normalizationConjugacyPointIndex '' (↑Γ : Set _)) ∪
    matrixEntryRange (G * S - S' * G)

private theorem normalizationConjugacyEquations_iff {A : Type*} [Field A] [Algebra k A]
    (Γ : Finset (MvPolynomial (ι × ι) k)) (U : (Matrix ι ι H)ˣ)
    (hΓ : ∀ a : ι × ι → A, (∀ P ∈ Γ, MvPolynomial.aeval a P = 0) ↔
      ∃! p : H →ₐ[k] A, ∀ ij, p (U.val ij.1 ij.2) = a ij)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) (z : W₂ → A) :
    (∀ P ∈ normalizationConjugacyEquations Γ U e v w N, MvPolynomial.aeval z P = 0) ↔
      ((∀ P ∈ normalizationEquations Γ U e v w N, MvPolynomial.aeval (z ∘ Sum.inl) P = 0) ∧
       (∀ P ∈ normalizationEquations Γ U e v w N,
          MvPolynomial.aeval (z ∘ normalizationConjugacySecondIndex) P = 0)) ∧
      ∃ g : H →ₐ[k] A, (∀ ij : ι × ι, g (U.val ij.1 ij.2) = z (normalizationConjugacyPointIndex ij)) ∧
        hopfAdjoint g (hopfAdjointSlice e w (z ∘ Sum.inl ∘ normalizationSliceIndex)) =
          hopfAdjointSlice e w (z ∘ normalizationConjugacySecondIndex ∘ normalizationSliceIndex) := by
  let G := polynomialMatrixVariables (k := k) (normalizationConjugacyPointIndex : ι × ι → W₂)
  let S := polynomialSliceMatrix U.val e w ((Sum.inl : W → W₂) ∘ normalizationSliceIndex)
  let S' := polynomialSliceMatrix U.val e w (normalizationConjugacySecondIndex ∘
    (normalizationSliceIndex : η → W))
  have hIntertwine (g : H →ₐ[k] A)
      (hg : ∀ ij : ι × ι, g (U.val ij.1 ij.2) = z (normalizationConjugacyPointIndex ij)) :
      (G * S - S' * G).map (MvPolynomial.aeval z) = 0 ↔
        hopfAdjoint g (hopfAdjointSlice e w (z ∘ Sum.inl ∘ normalizationSliceIndex)) =
          hopfAdjointSlice e w (z ∘ normalizationConjugacySecondIndex ∘ normalizationSliceIndex) := by
    have hG : G.map (MvPolynomial.aeval z) = U.val.map g :=
      Matrix.ext fun i j => (MvPolynomial.aeval_X z _).trans (hg (i, j)).symm
    simp only [Matrix.map_sub _ (map_sub _), algHom_map_matrix_mul,
      hG, S, S', polynomialSliceMatrix_aeval, sub_eq_zero]
    exact (hopfAdjoint_eq_iff_matrix_intertwines U hΔ hε hGen _ _ _).symm
  simp only [normalizationConjugacyEquations, Set.mem_union, or_imp, forall_and, Set.forall_mem_image,
    MvPolynomial.aeval_rename, Finset.mem_coe, hΓ, matrixEntryRange_aeval_eq_zero]
  constructor
  · rintro ⟨⟨hEq, ⟨g, hg, _⟩⟩, h⟩
    exact ⟨hEq, g, hg, (hIntertwine g hg).mp h⟩
  · rintro ⟨hEq, g, hg, h⟩
    refine ⟨⟨hEq, ⟨g, hg, fun p hp => ?_⟩⟩, (hIntertwine g hg).mpr h⟩
    apply AlgHom.ext_of_adjoin_eq_top hGen
    rintro _ ⟨ij, rfl⟩
    exact (hp ij).trans (hg ij).symm

private def normalizationConjugacyWitness (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (w : η → 𝔤 k)
    (d : MvPolynomial τ k) (i j : ι) : MvPolynomial W₂ k :=
  let S := polynomialSliceMatrix U.val e w ((Sum.inl : W → W₂) ∘ normalizationSliceIndex)
  let S' := polynomialSliceMatrix U.val e w (normalizationConjugacySecondIndex ∘
    (normalizationSliceIndex : η → W))
  MvPolynomial.rename ((Sum.inl : W → W₂) ∘ normalizationCartanIndex) d *
    MvPolynomial.rename (normalizationConjugacySecondIndex ∘ (normalizationCartanIndex : τ → W)) d *
    (S i j - S' i j)

omit [Fintype τ] [Fintype ν] in
private theorem normalizationConjugacyWitness_aeval {A : Type*} [Field A] [Algebra k A]
    (U : (Matrix ι ι H)ˣ) (e : 𝔤 k) (w : η → 𝔤 k) (d : MvPolynomial τ k) (i j : ι) (z : W₂ → A) :
    MvPolynomial.aeval z (normalizationConjugacyWitness U e w d i j) =
      MvPolynomial.aeval (z ∘ Sum.inl ∘ normalizationCartanIndex) d *
        MvPolynomial.aeval (z ∘ normalizationConjugacySecondIndex ∘ normalizationCartanIndex) d *
        (hopfCotangentMatrix U.val (hopfAdjointSlice e w (z ∘ Sum.inl ∘ normalizationSliceIndex)) i j -
          hopfCotangentMatrix U.val (hopfAdjointSlice e w
            (z ∘ normalizationConjugacySecondIndex ∘ normalizationSliceIndex)) i j) := by
  simp only [normalizationConjugacyWitness, map_mul, map_sub, MvPolynomial.aeval_rename]
  have h₁ := congrArg (fun M : Matrix ι ι A => M i j)
    (polynomialSliceMatrix_aeval U.val e w ((Sum.inl : W → W₂) ∘ normalizationSliceIndex) z)
  have h₂ := congrArg (fun M : Matrix ι ι A => M i j)
    (polynomialSliceMatrix_aeval U.val e w
      (normalizationConjugacySecondIndex ∘ (normalizationSliceIndex : η → W)) z)
  exact congrArg₂ (fun u v : A => _ * (u - v)) h₁ h₂

/-- Pairwise uniqueness of the normalized representatives of geometric adjoint
orbits follows from the same assertion over the algebraically closed ground field. -/
theorem normalizedHopfSlice_eq_of_adjoint_to_extension {A : Type*}
    [IsAlgClosed k] [Field A] [Algebra k A]
    (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) (d : MvPolynomial τ k)
    (hUnique : ∀ {y y' : 𝔤 k}, y ∈ normalizedHopfSlice U e v w N d →
      y' ∈ normalizedHopfSlice U e v w N d → ∀ g : H →ₐ[k] k, hopfAdjoint g y = y' → y = y')
    {y y' : 𝔤 A} (hy : y ∈ normalizedHopfSlice U e v w N d)
    (hy' : y' ∈ normalizedHopfSlice U e v w N d) (g : H →ₐ[k] A) (hg : hopfAdjoint g y = y') :
    y = y' := by
  classical
  rcases hy with ⟨a, s, ha, hs, rfl⟩
  rcases hy' with ⟨a', s', ha', hs', rfl⟩
  by_contra hne
  obtain ⟨i, j, hij⟩ : ∃ i j, hopfCotangentMatrix U.val (hopfAdjointSlice e w s) i j ≠
      hopfCotangentMatrix U.val (hopfAdjointSlice e w s') i j := by
    by_contra! h
    exact hne (hopfCotangentMatrix_injective U.val hGen (Matrix.ext h))
  let u (ij : ι × ι) := U.val ij.1 ij.2
  obtain ⟨Γ, hΓ⟩ := IsNoetherian.noetherian (RingHom.ker (MvPolynomial.aeval (R := k) u).toRingHom)
  obtain ⟨b, hb, hB⟩ := normalizationEquations_of_normalization Γ U
    (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N a s hs
  obtain ⟨b', hb', hB'⟩ := normalizationEquations_of_normalization Γ U
    (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N a' s' hs'
  let z : W₂ → A := Sum.elim (Sum.elim a b) (Sum.elim (Sum.elim a' b') (g ∘ u))
  let E := normalizationConjugacyEquations Γ U e v w N
  let h := normalizationConjugacyWitness (ν := ν) U e w d i j
  obtain hz : ∀ P ∈ E, MvPolynomial.aeval z P = 0 := by
    apply (normalizationConjugacyEquations_iff Γ U
      (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N z).mpr
    refine ⟨⟨hB, hB'⟩, g, fun _ => rfl, ?_⟩
    change hopfAdjoint g (hopfAdjointSlice e w (b ∘ Sum.inl)) = hopfAdjointSlice e w (b' ∘ Sum.inl)
    rwa [hb, hb']
  have hNz : MvPolynomial.aeval z h ≠ 0 := by
    simp only [h, normalizationConjugacyWitness_aeval]
    change MvPolynomial.aeval a d * MvPolynomial.aeval a' d *
      (hopfCotangentMatrix U.val (hopfAdjointSlice e w (b ∘ Sum.inl)) i j -
        hopfCotangentMatrix U.val (hopfAdjointSlice e w (b' ∘ Sum.inl)) i j) ≠ 0
    rw [hb, hb']
    exact mul_ne_zero (mul_ne_zero ha ha') (sub_ne_zero.mpr hij)
  obtain ⟨r, hrNz, hr⟩ := exists_ground_polynomial_solution_of_extension_solution
    E h z hz (isUnit_iff_ne_zero.mpr hNz)
  obtain ⟨⟨hR, hR'⟩, g₀, _, hg₀⟩ := (normalizationConjugacyEquations_iff Γ U
    (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N r).mp hr
  let a₀ : τ → k := r ∘ Sum.inl ∘ normalizationCartanIndex
  let a₀' : τ → k := r ∘ normalizationConjugacySecondIndex ∘ normalizationCartanIndex
  let s₀ : η → k := r ∘ Sum.inl ∘ normalizationSliceIndex
  let s₀' : η → k := r ∘ normalizationConjugacySecondIndex ∘ normalizationSliceIndex
  have hs₀ : HopfSliceNormalization U e v w N a₀ s₀ := normalizationEquations_iff Γ U
    (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N (r ∘ Sum.inl) hR
  have hs₀' : HopfSliceNormalization U e v w N a₀' s₀' := normalizationEquations_iff Γ U
    (finiteAlgHomPresentation_iff u hGen Γ hΓ) hΔ hε hGen e v w N
    (r ∘ normalizationConjugacySecondIndex) hR'
  simp only [h, normalizationConjugacyWitness_aeval] at hrNz
  change MvPolynomial.aeval a₀ d * MvPolynomial.aeval a₀' d *
    (hopfCotangentMatrix U.val (hopfAdjointSlice e w s₀) i j -
      hopfCotangentMatrix U.val (hopfAdjointSlice e w s₀') i j) ≠ 0 at hrNz
  have hd₀ : MvPolynomial.aeval a₀ d ≠ 0 := fun hh => hrNz (by rw [hh, zero_mul, zero_mul])
  have hd₀' : MvPolynomial.aeval a₀' d ≠ 0 := fun hh => hrNz (by rw [hh, mul_zero, zero_mul])
  have h0 := hUnique ⟨a₀, s₀, hd₀, hs₀, rfl⟩ ⟨a₀', s₀', hd₀', hs₀', rfl⟩ g₀ hg₀
  exact hrNz (by rw [h0, sub_self, mul_zero])

/-- The affine parameterization over the ground field is the original affine linear combination. -/
theorem hopfAdjointSlice_ground {σ : Type*} [Fintype σ] (e : 𝔤 k) (v : σ → 𝔤 k) (a : σ → k) :
    hopfAdjointSlice e v a = e + ∑ i, a i • v i := by
  apply LinearMap.ext
  intro x
  simp only [hopfAdjointSlice, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, Algebra.ofId_apply, Algebra.id.map_eq_id,
    RingHom.id_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- Ground-field coefficients in a basis give exactly the matrices in the submodule. -/
theorem exists_linearMatrixFamily_of_basis_iff {σ : Type*} [Fintype σ]
    (V : Submodule k (Matrix ι ι k)) (B : Basis σ k V) (X : Matrix ι ι k) :
    (∃ a : σ → k, linearMatrixFamily (fun i => (B i : Matrix ι ι k)) a = X) ↔ X ∈ V := by
  have h (a : σ → k) : linearMatrixFamily (fun i => (B i : Matrix ι ι k)) a =
      ∑ i, a i • (B i : Matrix ι ι k) := by
    apply Matrix.ext
    intro i j
    simp only [linearMatrixFamily, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
      Algebra.id.map_eq_id, RingHom.id_apply]
  constructor
  · rintro ⟨a, rfl⟩
    rw [h]
    exact V.sum_mem fun i _ => V.smul_mem (a i) (B i).property
  · intro hx
    let x : V := ⟨X, hx⟩
    refine ⟨B.repr x, ?_⟩
    rw [h]
    have hs := congrArg V.subtype (B.sum_repr x)
    simpa only [map_sum, map_smul, Submodule.subtype_apply, x] using hs

/-- A geometric orbit meeting the selected Cartan open has a unique representative
in the normalized slice once uniqueness is known on the ground field. -/
theorem existsUnique_normalizedHopfSlice_of_cartanConjugacy {A κ : Type*}
    [IsAlgClosed k] [Field A] [IsAlgClosed A] [Algebra k A] [Fintype κ]
    (b : Basis κ k (HopfCotangent k H)) (U : (Matrix ι ι H)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (e : 𝔤 k) (v : τ → 𝔤 k) (w : η → 𝔤 k) (N : ν → Matrix ι ι k) (d : MvPolynomial τ k)
    (hLift : ∀ a : τ → k, MvPolynomial.aeval a d ≠ 0 →
      ∃ s : η → k, HopfSliceNormalization U e v w N a s)
    (hUnique : ∀ {y y' : 𝔤 k}, y ∈ normalizedHopfSlice U e v w N d →
      y' ∈ normalizedHopfSlice U e v w N d → ∀ g : H →ₐ[k] k, hopfAdjoint g y = y' → y = y')
    (x : 𝔤 A) (a : τ → A) (ha : MvPolynomial.aeval a d ≠ 0)
    (g : H →ₐ[k] A) (hg : hopfAdjoint g (hopfAdjointSlice 0 v a) = x) :
    ∃! y : 𝔤 A, y ∈ normalizedHopfSlice U e v w N d ∧
      ∃ t : H →ₐ[k] A, hopfAdjoint t y = x := by
  classical
  letI : Group (H →ₐ[k] A) := hopfPointGroup
  have hOne (y : 𝔤 A) : hopfAdjoint (1 : H →ₐ[k] A) y = y := by
    apply (hopfAdjoint_eq_iff_matrix_intertwines U hΔ hε hGen 1 y y).mpr
    have hM : U.val.map (1 : H →ₐ[k] A) = 1 := congrArg Units.val
      (hopfPointMatrix (A := A) U hΔ hε).map_one
    rw [hM, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨s, hs⟩ := exists_hopfSliceNormalization_to_algClosed U hΔ hε hGen e v w N d hLift a ha
  have hy : hopfAdjointSlice e w s ∈ normalizedHopfSlice U e v w N d := ⟨a, s, ha, hs, rfl⟩
  obtain ⟨_, q, _, _, _, hq⟩ := hs
  let t := g * q
  have ht : hopfAdjoint t (hopfAdjointSlice e w s) = x := by
    change hopfAdjoint (g * q) (hopfAdjointSlice e w s) = x
    rw [hopfAdjoint_mul b, hq, hg]
  refine ⟨hopfAdjointSlice e w s, ⟨hy, t, ht⟩, ?_⟩
  rintro y' ⟨hy', p, hp⟩
  apply normalizedHopfSlice_eq_of_adjoint_to_extension U hΔ hε hGen e v w N d hUnique hy' hy (t⁻¹ * p)
  rw [hopfAdjoint_mul b, hp, ← ht, ← hopfAdjoint_mul b, inv_mul_cancel]
  exact hOne _

end Normalization

end WideE
