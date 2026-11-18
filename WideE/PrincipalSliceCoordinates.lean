import WideE.CartanSliceGround
import WideE.PolynomialNormalizationSlice
import WideE.ReductiveCartanOrbit

/-! Ground-field normalization and uniqueness in finite coordinates
for the principal slice of the reductive Lie algebra. -/

noncomputable section

open scoped Matrix TensorProduct
open LieAlgebra LieAlgebra.IsKilling LieModule Module

namespace WideE

variable {k H ι η τ : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsDomain H] [Fintype ι] [DecidableEq ι] [Fintype η] [Fintype τ]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "J" => (hopfLieVectorInvariantDerivations (k := k) (H := H))
local notation "S" => (derivedSeries k (hopfInvariantDerivations k H) 1)
local notation "Z" => center k 𝔤
local notation "Bfil" => kostantWeightFiltration (k := k)
local notation "L" => HopfLieVector k H k

variable [IsKilling k (derivedSeries k (hopfInvariantDerivations k H) 1)]
  [FiniteDimensional k (derivedSeries k (hopfInvariantDerivations k H) 1)]
  {C : LieSubalgebra k (derivedSeries k (hopfInvariantDerivations k H) 1)}
  [C.IsCartanSubalgebra] [IsTriangularizable k C (derivedSeries k (hopfInvariantDerivations k H) 1)]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem C

set_option maxHeartbeats 1800000 in
set_option synthInstance.maxHeartbeats 120000 in
/-- The Cartan and central coordinates, a basis of the slice directions,
and a basis of the negative matrix submodule satisfy the two ground-field
conditions for geometric normalization and uniqueness. -/
theorem exists_ground_principalSliceNormalization (bC : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hCompl : IsCompl S Z) (B : (Φ).Base) [Fintype B.support] (e f : B.support → S)
    (hE : ∀ i : B.support, e i ∈ rootSpace C (((Φ).root i : C →ₗ[k] k) : C → k))
    (hF : ∀ i : B.support, f i ∈ rootSpace C (-(((Φ).root i : C →ₗ[k] k) : C → k)))
    (ht : ∀ i : B.support, IsSl2Triple ((Φ).coroot i : S) (e i) (f i))
    {f₀ : S} (ht₀ : IsSl2Triple (principalCartanElement B : S) (∑ i, e i) f₀)
    (hPrincipal : ∀ p : H →ₐ[k] k,
      hopfAdjoint p ((J).symm ((principalCartanElement B : S) : 𝔤)) =
        (J).symm ((principalCartanElement B : S) : 𝔤) →
      ∀ x : C, hopfAdjoint p ((J).symm ((x : S) : 𝔤)) = (J).symm ((x : S) : 𝔤))
    (cB : Basis τ k (C × Z)) (d : MvPolynomial τ k)
    (hReg : ∀ a : τ → k, MvPolynomial.aeval a d ≠ 0 →
      ∀ α : C.root, (Φ).root α (∑ i, a i • cB i).1 ≠ 0) :
    let v : τ → L := cartanCenterLieEmbedding (Q := H) C ∘ cB
    ∃ (r n : ℕ) (e₀ : L) (w : Fin r → L) (N : Fin n → Matrix ι ι k),
      (∀ a : τ → k, MvPolynomial.aeval a d ≠ 0 →
        ∃ s : Fin r → k, HopfSliceNormalization U e₀ v w N a s) ∧
      (∀ {y y' : L}, y ∈ normalizedHopfSlice U e₀ v w N d →
        y' ∈ normalizedHopfSlice U e₀ v w N d → ∀ g : H →ₐ[k] k,
        hopfAdjoint g y = y' → y = y') := by
  classical
  letI : FiniteDimensional k (HopfCotangent k H) := hopfCotangent_finiteDimensional k H
  letI : FiniteDimensional k 𝔤 := FiniteDimensional.of_surjective (J).toLinearMap (J).surjective
  let h : S := principalCartanElement B
  let E : S := ∑ i, e i
  let e₀ : L := (J).symm (E : 𝔤)
  let V : Submodule k S := Bfil h 0 ⊓ LinearMap.ker (LieModule.toEnd k S S f₀)
  let M : Submodule k (Matrix ι ι k) := Bfil (hopfLieMatrix U.val (h : 𝔤)) 1
  let β := Module.finBasis k (V × Z)
  let μ := Module.finBasis k M
  let G : (V × Z) →ₗ[k] L := (J).symm.toLinearMap.comp
    (((S).toSubmodule.subtype.comp V.subtype).coprod (Z).toSubmodule.subtype)
  let v : τ → L := cartanCenterLieEmbedding (Q := H) C ∘ cB
  let w : Fin (finrank k (V × Z)) → L := G ∘ β
  let N (i : Fin (finrank k M)) : Matrix ι ι k := μ i
  let c (a : τ → k) : C × Z := ∑ i, (a i • cB i : C × Z)
  let s (b : Fin (finrank k (V × Z)) → k) : V × Z := ∑ i, b i • β i
  have hCartanSum (a : τ → k) :
      (∑ i, a i • v i) = derivedCenterLieVector ((c a).1 : S) (c a).2 := by
    let F : C × Z →ₗ[k] L := cartanCenterLieEmbedding (Q := H) C
    change (∑ i, a i • F (cB i)) = F (∑ i, (a i • cB i : C × Z))
    rw [map_sum]
    simp_rw [map_smul]
  have hCartan (a : τ → k) :
      hopfAdjointSlice 0 v a = derivedCenterLieVector ((c a).1 : S) (c a).2 := by
    rw [hopfAdjointSlice_ground, zero_add, hCartanSum]
  have hCartanAffine (a : τ → k) :
      hopfAdjointSlice e₀ v a = derivedCenterLieVector (E + ((c a).1 : S)) (c a).2 := by
    rw [hopfAdjointSlice_ground, hCartanSum]
    change (J).symm (E : 𝔤) + (J).symm ((((c a).1 : S) : 𝔤) + ((c a).2 : 𝔤)) =
      (J).symm (((E + ((c a).1 : S)) : 𝔤) + ((c a).2 : 𝔤))
    rw [← map_add]
    exact congrArg (J).symm (add_assoc _ _ _).symm
  have hSlice (b : Fin (finrank k (V × Z)) → k) :
      hopfAdjointSlice e₀ w b = derivedCenterLieVector (E + ((s b).1 : S)) (s b).2 := by
    have hSum : (∑ i, b i • w i) = G (s b) := by
      change (∑ i, b i • G (β i)) = G (∑ i, b i • β i)
      rw [map_sum]
      simp_rw [map_smul]
    rw [hopfAdjointSlice_ground, hSum]
    change (J).symm (E : 𝔤) + (J).symm ((((s b).1 : S) : 𝔤) + ((s b).2 : 𝔤)) =
      (J).symm (((E + ((s b).1 : S)) : 𝔤) + ((s b).2 : 𝔤))
    rw [← map_add]
    exact congrArg (J).symm (add_assoc _ _ _).symm
  have hNegMatrix (p : H →ₐ[k] k) :
      (∃ a : Fin (finrank k M) → k, U.val.map p = 1 + linearMatrixFamily N a) ↔ U.val.map p - 1 ∈ M := by
    rw [← exists_linearMatrixFamily_of_basis_iff M μ (U.val.map p - 1)]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [ha, add_comm, add_sub_cancel_right]
    · rintro ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [show linearMatrixFamily N a = U.val.map p - 1 from ha, add_comm, sub_add_cancel]
  refine ⟨_, _, e₀, w, N, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, p, q, hx, hfx, hp, hpA, hqA⟩ :=
      exists_principalKostantSlice_reductive (C := C) bC U hD he hGen B e hE ht₀
        (c a).1 (c a).2 (hReg a ha)
    let xZ : V × Z := (⟨x, hx, hfx⟩, (c a).2)
    let b (i : Fin (finrank k (V × Z))) := β.repr xZ i
    have hb : s b = xZ := β.sum_repr xZ
    obtain ⟨n, hn⟩ := (hNegMatrix p).mpr hp
    refine ⟨b, p, q, n, hn, ?_, ?_⟩
    · rw [hCartanAffine, hSlice, hb]
      exact hpA
    · rw [hSlice, hb, hCartan]
      exact hqA
  · rintro _ _ ⟨a, b, ha, ⟨p, q, n, hN, hP, hQ⟩, rfl⟩
      ⟨a', b', ha', ⟨p', q', n', hN', hP', hQ'⟩, rfl⟩ g hg
    rw [hCartanAffine, hSlice] at hP hP'
    rw [hSlice, hCartan] at hQ hQ'
    rw [hSlice, hSlice] at hg ⊢
    have hs : ((s b).1 : S) ∈ Bfil h 0 := (s b).1.property.1
    have hs' : ((s b').1 : S) ∈ Bfil h 0 := (s b').1.property.1
    have hf : ⁅f₀, ((s b).1 : S)⁆ = 0 := (s b).1.property.2
    have hf' : ⁅f₀, ((s b').1 : S)⁆ = 0 := (s b').1.property.2
    obtain ⟨heS, heZ⟩ := principalKostantSlice_reductive_eq_of_conjugate (C := C) bC U hD he hGen hCompl
      B e f hE hF ht ht₀ hPrincipal (c a).1 (c a').1 (c a).2 (c a').2 (s b).2 (s b').2
      (s b).1 (s b').1 (hReg a ha) (hReg a' ha') hs hs' hf hf'
      p p' q q' g ((hNegMatrix p).mp ⟨n, hN⟩) ((hNegMatrix p').mp ⟨n', hN'⟩)
      hP hP' hQ hQ' hg
    rw [heS, heZ]

end WideE
