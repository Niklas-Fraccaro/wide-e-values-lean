import WideE.LieCompositionFlag

/-! Coordinates and induced matrix action on the successive quotients of an adapted flag. -/

noncomputable section

open scoped BigOperators Matrix

namespace WideE

section Coordinates

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {n r : ℕ}
  (v : Basis (Fin n) k V) (b : Fin n → Fin r) (W : Fin (r + 1) → Submodule k V)
  (hW : ∀ s : Fin (r + 1), Submodule.span k (v '' {i | (b i).val < s.val}) = W s)
  (t : Fin r)

/-- The earlier step of the flag, viewed in the next one. -/
abbrev flagLowerSubmodule : Submodule k (W t.succ) :=
  (W t.castSucc).comap (W t.succ).subtype

local notation "N" => flagLowerSubmodule W t
local notation "J" => {i : Fin n // b i = t}

private def flagBlockCoordinates : (W t.succ) →ₗ[k] (J → k) :=
  LinearMap.pi fun j => (v.coord j.val).comp (W t.succ).subtype

include hW in
private theorem flagBlockCoordinates_lower_le_ker :
    N ≤ LinearMap.ker (flagBlockCoordinates v b W t) := by
  intro x hx
  apply funext
  intro j
  change v.repr x.val j.val = 0
  apply basis_repr_zero_of_mem_flag v b W hW _ hx
  change ¬ (b j.val).val < t.val
  rw [j.property]
  exact lt_irrefl _

private def flagSubquotientCoordinateMap : ((W t.succ) ⧸ N) →ₗ[k] (J → k) :=
  (N).liftQ (flagBlockCoordinates v b W t) (flagBlockCoordinates_lower_le_ker v b W hW t)

/-- The coordinates in a block give an exact linear equivalence from the corresponding
successive quotient of the flag to the vector space indexed by that block. -/
def flagSubquotientCoordinates : ((W t.succ) ⧸ N) ≃ₗ[k] (J → k) := by
  classical
  let f := flagSubquotientCoordinateMap v b W hW t
  refine LinearEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).mpr ?_, ?_⟩
  · intro z hz
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change x.val ∈ W t.castSucc
    have hSum : ∑ j, v.repr x.val j • v j ∈ W t.castSucc := by
      apply (W t.castSucc).sum_mem
      intro j _
      by_cases hj : (b j).val < t.val
      · apply (W t.castSucc).smul_mem
        rw [← hW]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      · have hzj : v.repr x.val j = 0 := by
          by_cases hEq : b j = t
          · exact congrFun hz ⟨j, hEq⟩
          · have hlt : t < b j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hEq)
            exact basis_repr_zero_of_mem_flag v b W hW
              (Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hlt)) x.property
        rw [hzj, zero_smul]
        exact (W t.castSucc).zero_mem
    rwa [v.sum_repr] at hSum
  · intro y
    let x : V := ∑ j : J, y j • v j.val
    have hx : x ∈ W t.succ := by
      apply (W t.succ).sum_mem
      intro j _
      apply (W t.succ).smul_mem
      rw [← hW]
      refine Submodule.subset_span ⟨j.val, ?_, rfl⟩
      change (b j.val).val < t.succ.val
      rw [j.property]
      exact Nat.lt_succ_self _
    refine ⟨Submodule.Quotient.mk (p := N) ⟨x, hx⟩, funext fun j => ?_⟩
    change v.repr x j.val = y j
    have hEval (i : J) : (v.repr (y i • v i.val)) j.val = if i = j then y j else 0 := by
      by_cases hi : i = j
      · subst i
        simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
          smul_eq_mul, mul_one, if_pos rfl, if_true]
      · have hne : i.val ≠ j.val := fun hh => hi (Subtype.ext hh)
        simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_of_ne hne,
          smul_zero, if_neg hi]
    simp only [x, map_sum, Finsupp.finset_sum_apply, hEval, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]

@[simp] theorem flagSubquotientCoordinates_mk (x : W t.succ) (j : J) :
    flagSubquotientCoordinates v b W hW t (Submodule.Quotient.mk (p := N) x) j =
      v.repr x.val j.val := rfl

/-- A flag-preserving map acts on the corresponding quotient via its actual diagonal block. -/
theorem flagSubquotientCoordinates_apply_map
    (f : V →ₗ[k] V) (hf : ∀ s, W s ≤ (W s).comap f)
    (x : W t.succ) :
    flagSubquotientCoordinates v b W hW t
      (Submodule.Quotient.mk (p := N) ⟨f x.val, hf t.succ x.property⟩) =
      ((LinearMap.toMatrix v v f).submatrix (fun j : J => j.val) (fun j : J => j.val)) *ᵥ
        flagSubquotientCoordinates v b W hW t (Submodule.Quotient.mk (p := N) x) := by
  classical
  let A := LinearMap.toMatrix v v f
  have hA : A.BlockTriangular b := toMatrix_blockTriangular_of_preserves_flag v b W hW f hf
  funext i
  have h := congrFun (LinearMap.toMatrix_mulVec_repr v v f x.val) i.val
  change (∑ j, A i.val j * v.repr x.val j) = v.repr (f x.val) i.val at h
  change v.repr (f x.val) i.val = ∑ j : J, A i.val j.val * v.repr x.val j.val
  rw [← h]
  symm
  refine Fintype.sum_of_injective (fun j : J => j.val) Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro j hj
  have hne : b j ≠ t := fun he => hj ⟨⟨j, he⟩, rfl⟩
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hZero : A i.val j = 0 := hA (i.property.symm ▸ hlt)
    rw [hZero, zero_mul]
  · have hZero := basis_repr_zero_of_mem_flag v b W hW (i := j)
      (Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hgt)) x.property
    rw [hZero, mul_zero]

end Coordinates

section Irreducibility

variable {k L L' V V' : Type*} [Field k] [LieRing L] [LieAlgebra k L] [LieRing L'] [LieAlgebra k L']
  [AddCommGroup V] [Module k V] [LieRingModule L V]
  [AddCommGroup V'] [Module k V'] [LieRingModule L' V']

/-- An action is irreducible if its restriction along a Lie homomorphism is already irreducible. -/
theorem lieModule_isIrreducible_of_equivariant_equiv [LieModule.IsIrreducible k L V]
    (φ : L →ₗ⁅k⁆ L') (e : V ≃ₗ[k] V') (h : ∀ x v, e ⁅x, v⁆ = ⁅φ x, e v⁆) :
    LieModule.IsIrreducible k L' V' := by
  let pull (S : LieSubmodule k L' V') : LieSubmodule k L V :=
    { S.toSubmodule.comap e.toLinearMap with
      lie_mem := fun {x v} hv => by
        change e ⁅x, v⁆ ∈ S
        rw [h]
        exact S.lie_mem (x := φ x) hv }
  have hinj : Function.Injective pull := by
    intro A B hab
    ext r
    obtain ⟨v, rfl⟩ := e.surjective r
    change v ∈ pull A ↔ v ∈ pull B
    rw [hab]
  have hBot : pull ⊥ = ⊥ := by
    ext v
    change e v = 0 ↔ v = 0
    exact ⟨(injective_iff_map_eq_zero e).mp e.injective v, fun hv => by rw [hv, map_zero]⟩
  have hTop : pull ⊤ = ⊤ := by
    ext v
    change e v ∈ (⊤ : LieSubmodule k L' V') ↔ v ∈ (⊤ : LieSubmodule k L V)
    simp
  have hNe : (⊥ : LieSubmodule k L' V') ≠ ⊤ := by
    intro hEq
    exact bot_ne_top (hBot.symm.trans ((congrArg pull hEq).trans hTop))
  refine { toNontrivial := ⟨⟨⊥, ⊤, hNe⟩⟩, eq_bot_or_eq_top := ?_ }
  intro S
  rcases IsSimpleOrder.eq_bot_or_eq_top (pull S) with hS | hS
  · exact Or.inl (hinj (hS.trans hBot.symm))
  · exact Or.inr (hinj (hS.trans hTop.symm))

end Irreducibility

end WideE
