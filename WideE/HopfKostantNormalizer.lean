import WideE.KostantSl2Filtration
import WideE.HopfAdjointExponential
import WideE.NegativeWeightSubgroup

/-!
# Kostant normalization by a point of the group

Each correction in a strictly negative degree has a nilpotent matrix in
the given Hopf representation. The corresponding polynomial group
points realize the finite sequence of adjoint exponentials.
-/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section AdjointIdentity

variable {k H η : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [Fintype η] [DecidableEq η]

/-- The counit point acts trivially on the cotangent dual. -/
theorem hopfAdjoint_one (b : Basis η k (HopfCotangent k H))
    (x : HopfLieVector k H k) : hopfAdjoint (hopfPointOne (k := k) (H := H) (L := k)) x = x := by
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  let ρ := hopfPointMatrix (A := k) (hopfAdjointMatrixUnit b)
    (hopfAdjointMatrix_comul b) (hopfAdjointMatrix_counit b)
  have hM : (hopfAdjointMatrix b).map (hopfPointOne (k := k) (H := H) (L := k)) = 1 :=
    congrArg Units.val ρ.map_one
  apply b.ext
  intro i
  have h := hopfAdjoint_apply_basis b (hopfPointOne (k := k) (H := H) (L := k)) x
  rw [hM, Matrix.one_mulVec] at h
  exact congrFun h i

end AdjointIdentity

section Normalizer

variable {k H ι L : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [LieRing L] [LieAlgebra k L] [LieAlgebra ℚ L]
  [IsScalarTower ℚ k L]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := H)

omit [IsScalarTower ℚ k L] in
/-- Finite adjoint exponentials with nilpotent matrices are realized by one group point in the subgroup containing their matrices. -/
theorem exists_hopfPoint_applyAdjointExponentials_in_subgroup (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (l : List (NilpotentAdjoint k L))
    (C : Subgroup (Matrix ι ι k)ˣ)
    (hNil : ∀ u ∈ l, IsNilpotent (hopfLieMatrix U.val (j u.val)))
    (hC : ∀ u ∈ l, ∀ M : (Matrix ι ι k)ˣ,
      M.val = IsNilpotent.exp (hopfLieMatrix U.val (j u.val)) → M ∈ C) :
    ∃ p : H →ₐ[k] k, hopfPointMatrix U hD he p ∈ C ∧ ∀ x : L,
      hopfAdjoint p ((J).symm (j x)) = (J).symm (j (applyAdjointExponentials l x)) := by
  classical
  letI : LieAlgebra ℚ 𝔤 := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k 𝔤))
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  letI : Algebra.FiniteType k H := ⟨⟨(Set.finite_range
    (fun ij : ι × ι => U.val ij.1 ij.2)).toFinset, by simpa using hGen⟩⟩
  letI : FiniteDimensional k (HopfCotangent k H) := hopfCotangent_finiteDimensional k H
  let b := Module.finBasis k (HopfCotangent k H)
  induction l with
  | nil =>
    exact ⟨1, by simpa only [map_one] using C.one_mem, fun x => hopfAdjoint_one b ((J).symm (j x))⟩
  | cons u l ih =>
    obtain ⟨q, hqC, hq⟩ := ih (fun v hv => hNil v (List.mem_cons_of_mem u hv))
      (fun v hv => hC v (List.mem_cons_of_mem u hv))
    obtain ⟨hn, p, hpM, hp⟩ := exists_hopfPoint_lieAdjointExp_with_matrix U hD he hGen (j u.val)
      (hNil u (List.mem_cons_self ..))
    refine ⟨q * p, ?_, fun x => ?_⟩
    · rw [map_mul]
      exact C.mul_mem hqC (hC u (List.mem_cons_self ..) _ hpM)
    · have hpx : hopfAdjoint p ((J).symm (j x)) =
          (J).symm (j (LieDerivation.exp (leftAdjointDerivation k u.val) u.property x)) := by
        apply (J).injective
        rw [(J).apply_symm_apply, hp, (J).apply_symm_apply]
        exact (map_leftAdjointExp j u.val x u.property hn).symm
      rw [hopfAdjoint_mul b, hpx, hq]
      rfl

omit [IsScalarTower ℚ k L] in
/-- Finite adjoint exponentials with nilpotent matrices are realized by one group point. -/
theorem exists_hopfPoint_applyAdjointExponentials (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (l : List (NilpotentAdjoint k L))
    (hNil : ∀ u ∈ l, IsNilpotent (hopfLieMatrix U.val (j u.val))) :
    ∃ p : H →ₐ[k] k, ∀ x : L,
      hopfAdjoint p ((J).symm (j x)) = (J).symm (j (applyAdjointExponentials l x)) := by
  obtain ⟨p, _, hp⟩ := exists_hopfPoint_applyAdjointExponentials_in_subgroup U hD he hGen j l ⊤
    hNil (fun _ _ _ _ => by simp)
  exact ⟨p, hp⟩

/-- Normalization of `e+b` takes place in the actual Hopf group, including
when the `sl₂` data belongs to a Lie subalgebra mapped into its Lie algebra.
The normalizing point lies in the strictly negative subgroup. -/
theorem exists_hopfPoint_kostantNormalizer_negative [FiniteDimensional k L]
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) {h e f : L} (t : IsSl2Triple h e f)
    (b : kostantWeightFiltration (k := k) h 0) :
    ∃ (p : H →ₐ[k] k) (s : L),
      U.val.map p - 1 ∈ kostantWeightFiltration (k := k) (hopfLieMatrix U.val (j h)) 1 ∧
      s ∈ kostantWeightFiltration (k := k) h 0 ∧ ⁅f, s⁆ = 0 ∧
      hopfAdjoint p ((J).symm (j (e + b.val))) = (J).symm (j (e + s)) := by
  obtain ⟨l, s, hWeights, hSlice, hs, hExp⟩ := exists_kostantNormalizer_of_sl2Triple_with_weights t b
  let ρ := (hopfLieMatrixHom U.val hD).comp j
  let a := ρ h
  let C := negativeWeightUnitSubgroup (k := k) a
  have hNegative (u : NilpotentAdjoint k L) (hu : u ∈ l) :
      hopfLieMatrix U.val (j u.val) ∈ kostantWeightFiltration (k := k) a 1 := by
    obtain ⟨r, hr⟩ := hWeights u hu
    exact negativeEvenWeightSpace_le_filtration a (Nat.succ_le_succ (Nat.zero_le r))
      (lieHom_mem_negativeEvenWeightSpace ρ h hr)
  have hNil (u : NilpotentAdjoint k L) (hu : u ∈ l) :
      IsNilpotent (hopfLieMatrix U.val (j u.val)) :=
    isNilpotent_of_mem_kostantWeightFiltration a (by decide : 0 < 1) (hNegative u hu)
  have hC (u : NilpotentAdjoint k L) (hu : u ∈ l) (M : (Matrix ι ι k)ˣ)
      (hM : M.val = IsNilpotent.exp (hopfLieMatrix U.val (j u.val))) : M ∈ C := by
    change M.val - 1 ∈ kostantWeightFiltration (k := k) a 1
    rw [hM]
    exact exp_sub_one_mem_kostantWeightFiltration a (by decide : 0 < 1) (hNegative u hu)
  obtain ⟨p, hpC, hp⟩ := exists_hopfPoint_applyAdjointExponentials_in_subgroup U hD he hGen j l C hNil hC
  refine ⟨p, s, hpC, hSlice, hs, ?_⟩
  rw [hp, hExp]

/-- Normalization of `e+b` takes place in the actual Hopf group, including
when the `sl₂` data belongs to a Lie subalgebra mapped into its Lie algebra. -/
theorem exists_hopfPoint_kostantNormalizer [FiniteDimensional k L]
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) {h e f : L} (t : IsSl2Triple h e f)
    (b : kostantWeightFiltration (k := k) h 0) :
    ∃ (p : H →ₐ[k] k) (s : L), s ∈ kostantWeightFiltration (k := k) h 0 ∧ ⁅f, s⁆ = 0 ∧
      hopfAdjoint p ((J).symm (j (e + b.val))) = (J).symm (j (e + s)) := by
  obtain ⟨p, s, _, hs, hk, hp⟩ := exists_hopfPoint_kostantNormalizer_negative U hD he hGen j t b
  exact ⟨p, s, hs, hk, hp⟩

end Normalizer

end WideE
