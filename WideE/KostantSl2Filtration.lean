import WideE.KostantNormalForm
import WideE.Sl2WeightSplitting
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! The Kostant filtration and its grade decompositions from a finite-dimensional `sl₂` triple. -/

noncomputable section

namespace WideE

section Filtration

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]

/-- The adjoint weight `-2r`. -/
abbrev negativeEvenWeightSpace (h : L) (r : ℕ) : Submodule k L :=
  sl2WeightSpace (k := k) (M := L) h (-(2 : ℤ) * (r : ℤ))

local notation "W" => negativeEvenWeightSpace (k := k)

/-- The descending filtration by nonpositive even adjoint weight. -/
def kostantWeightFiltration (h : L) (r : ℕ) : Submodule k L :=
  ⨆ i : {i : ℕ // r ≤ i}, W h i.val

local notation "B" => kostantWeightFiltration (k := k)

private theorem scalar_negativeEvenWeight_injective :
    Function.Injective (fun i : ℕ => ((-(2 : ℤ) * (i : ℤ) : ℤ) : k)) := by
  intro i j h
  have h' := Int.cast_injective h
  omega

omit [CharZero k] in
/-- Each eigenspace lies in all preceding stages of the weight filtration. -/
theorem negativeEvenWeightSpace_le_filtration (h : L) {r i : ℕ} (hri : r ≤ i) :
    W h i ≤ B h r := le_iSup (fun j : {i : ℕ // r ≤ i} => W h j.val) ⟨i, hri⟩

omit [CharZero k] in
/-- The weight filtration decreases with its depth. -/
theorem kostantWeightFiltration_antitone (h : L) : Antitone (B h) := by
  intro r s hrs
  apply iSup_le
  intro i
  exact negativeEvenWeightSpace_le_filtration h (hrs.trans i.property)

omit [CharZero k] in
/-- A filtration stage is the sum of its leading weight space and the next stage. -/
theorem negativeEvenWeightSpace_sup_filtration_succ (h : L) (r : ℕ) :
    W h r ⊔ B h (r + 1) = B h r := by
  apply le_antisymm
  · exact sup_le (negativeEvenWeightSpace_le_filtration h le_rfl)
      (kostantWeightFiltration_antitone h (Nat.le_succ r))
  · apply iSup_le
    intro j
    by_cases hj : j.val = r
    · rw [hj]
      exact le_sup_left
    · exact (negativeEvenWeightSpace_le_filtration h (show r + 1 ≤ j.val by have := j.property; omega)).trans le_sup_right

/-- The leading weight space is disjoint from the next filtration stage. -/
theorem negativeEvenWeightSpace_disjoint_filtration_succ (h : L) (r : ℕ) :
    Disjoint (W h r) (B h (r + 1)) := by
  let D := LieModule.toEnd k L L h
  have hIndependent : iSupIndep (W h) :=
    D.eigenspaces_iSupIndep.comp scalar_negativeEvenWeight_injective
  refine (iSupIndep_def.mp hIndependent r).mono_right ?_
  apply iSup_le
  intro i
  have hr : i.val ≠ r := by have := i.property; omega
  exact le_iSup₂ (f := fun j (_ : j ≠ r) => W h j) i.val hr

/-- The next-step quotient of the filtration is exactly the indicated weight space. -/
def kostantWeightGradeEquiv (h : L) (r : ℕ) :
    W h r ≃ₗ[k] (B h r ⧸ (B h (r + 1)).comap (B h r).subtype) := by
  let Q := (B h (r + 1)).comap (B h r).subtype
  let j : W h r →ₗ[k] B h r :=
    Submodule.inclusion (negativeEvenWeightSpace_le_filtration (k := k) h (r := r) (i := r) le_rfl)
  let m : W h r →ₗ[k] B h r ⧸ Q := Q.mkQ.comp j
  refine LinearEquiv.ofBijective m ⟨?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    refine eq_bot_iff.mpr fun x hx => ?_
    apply (Submodule.mem_bot k).mpr
    apply Subtype.ext
    have hx' : j x ∈ Q := (Submodule.Quotient.mk_eq_zero Q).mp hx
    exact Submodule.disjoint_def.mp (negativeEvenWeightSpace_disjoint_filtration_succ h r) x.val x.property hx'
  · intro q
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective Q q
    have ha : a.val ∈ W h r ⊔ B h (r + 1) := by
      rw [negativeEvenWeightSpace_sup_filtration_succ]
      exact a.property
    obtain ⟨u, hu, v, hv, hsum⟩ := Submodule.mem_sup.mp ha
    refine ⟨⟨u, hu⟩, ?_⟩
    change Q.mkQ (j ⟨u, hu⟩) = Q.mkQ a
    apply (Submodule.Quotient.eq Q).mpr
    change u - a.val ∈ B h (r + 1)
    rw [← hsum, sub_add_eq_sub_sub, sub_self, zero_sub]
    exact neg_mem hv

@[simp] theorem kostantWeightGradeEquiv_apply (h : L) (r : ℕ) (x : W h r) :
    kostantWeightGradeEquiv h r x = ((B h (r + 1)).comap (B h r).subtype).mkQ
      (Submodule.inclusion (negativeEvenWeightSpace_le_filtration (k := k) h le_rfl) x) := rfl

/-- The negative-weight filtration has a zero stage in finite dimension. -/
theorem exists_kostantWeightFiltration_eq_bot [FiniteDimensional k L] (h : L) :
    ∃ N : ℕ, B h N = ⊥ := by
  classical
  let D := LieModule.toEnd k L L h
  let s : Set ℕ := {n | W h n ≠ ⊥}
  letI : Fintype {μ : k // D.HasEigenvalue μ} := Set.Finite.fintype (D.finite_hasEigenvalue)
  letI : Finite s := Finite.of_injective
    (fun n : s => (⟨_, Module.End.hasEigenvalue_iff.mpr n.property⟩ : D.Eigenvalues))
    (fun x y hEq => Subtype.ext (scalar_negativeEvenWeight_injective (congrArg Subtype.val hEq)))
  letI : Fintype s := Fintype.ofFinite s
  let S := Set.toFinset s
  let N := S.sup id + 1
  refine ⟨N, eq_bot_iff.mpr ?_⟩
  apply iSup_le
  intro i
  by_cases hb : W h i.val = ⊥
  · exact hb.le
  · have hi : i.val ∈ s := hb
    have hI : i.val ∈ S := Set.mem_toFinset.mpr hi
    have hBound : i.val ≤ S.sup id := Finset.le_sup (f := id) hI
    have hiN := i.property
    change S.sup id + 1 ≤ i.val at hiN
    omega

end Filtration

section Construction

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [FiniteDimensional k L]

local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

omit [FiniteDimensional k L] [CharZero k] in
/-- An adjoint bracket adds the two weight degrees. -/
theorem lie_mem_negativeEvenWeightSpace (h : L) {a b : ℕ} {u x : L}
    (hu : u ∈ W h a) (hx : x ∈ W h b) : ⁅u, x⁆ ∈ W h (a + b) := by
  rw [Module.End.mem_eigenspace_iff] at hu hx ⊢
  change ⁅h, u⁆ = _ at hu
  change ⁅h, x⁆ = _ at hx
  change ⁅h, ⁅u, x⁆⁆ = _
  rw [leibniz_lie, hu, hx, smul_lie, lie_smul, ← add_smul]
  congr 1
  push_cast
  ring

omit [FiniteDimensional k L] [CharZero k] in
private theorem bracket_weight_mem_filtration (h : L) {r : ℕ} (u : W h r)
    (x : L) (hx : x ∈ B h 0) : ⁅(u : L), x⁆ ∈ B h r := by
  let D := (leftAdjointDerivation k (u : L)).toLinearMap
  have hIncl : B h 0 ≤ (B h r).comap D := by
    apply iSup_le
    intro j y hy
    change D y ∈ B h r
    rw [show D y = ⁅(u : L), y⁆ from leftAdjointDerivation_apply k (u : L) y]
    exact negativeEvenWeightSpace_le_filtration h (Nat.le_add_right r j.val) (lie_mem_negativeEvenWeightSpace h u.property hy)
  have hy : D x ∈ B h r := hIncl hx
  change leftAdjointDerivation k (u : L) x ∈ B h r at hy
  rwa [leftAdjointDerivation_apply] at hy

/-- A strictly negative weight vector acts by a nilpotent adjoint derivation. -/
theorem isNilpotent_leftAdjoint_of_weight_succ (h : L) (r : ℕ) (u : W h (r + 1)) :
    IsNilpotent (leftAdjointDerivation k (u : L)).toLinearMap := by
  let ρ := LieModule.toEnd k L L
  have hρ : (leftAdjointDerivation k (u : L)).toLinearMap = ρ (u : L) :=
    LinearMap.ext fun x => leftAdjointDerivation_apply k (u : L) x
  rw [hρ]
  let c := ((-(2 : ℤ) * ((r + 1 : ℕ) : ℤ) : ℤ) : k)
  have hc : c ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have hu : ⁅h, (u : L)⁆ = c • (u : L) := Module.End.mem_eigenspace_iff.mp u.property
  apply isNilpotent_of_lie_eq_smul_ne_zero (ρ h) (ρ (u : L)) c hc
  change ⁅LieModule.toEnd k L L h, LieModule.toEnd k L L (u : L)⁆ = _
  rw [← LieHom.map_lie, hu, LieHom.map_smul]

private abbrev negativeWeightDegree (r : ℕ) : ℤ := -(2 : ℤ) * (r : ℤ)

private theorem adjacent_weight_eq (r : ℕ) :
    negativeWeightDegree (r + 1) = negativeWeightDegree r - 2 := by
  simp only [negativeWeightDegree, Nat.cast_add, Nat.cast_one]
  ring

private def negativeEvenWeightShift (h : L) (r : ℕ) :
    W h (r + 1) ≃ₗ[k] sl2WeightSpace (k := k) (M := L) h (negativeWeightDegree r - 2) :=
  LinearEquiv.ofEq _ _ (congrArg (sl2WeightSpace (k := k) (M := L) h) (adjacent_weight_eq r))

omit [CharZero k] [FiniteDimensional k L] in
private theorem negativeEvenWeightShift_coe (h : L) (r : ℕ) (u : W h (r + 1)) :
    ((negativeEvenWeightShift h r u : _) : L) = (u : L) := by
  unfold negativeEvenWeightShift
  exact LinearEquiv.coe_ofEq_apply _ _

private def kostantWeightSlice {h e f : L} (t : IsSl2Triple h e f) (r : ℕ) :
    Submodule k L :=
  (LinearMap.ker (sl2WeightLower (k := k) (M := L) t (negativeWeightDegree r))).map (W h r).subtype

private def kostantWeightSliceEquiv {h e f : L} (t : IsSl2Triple h e f) (r : ℕ) :
    LinearMap.ker (sl2WeightLower (k := k) (M := L) t (negativeWeightDegree r)) ≃ₗ[k]
      kostantWeightSlice (k := k) t r :=
  Submodule.equivMapOfInjective (W h r).subtype Subtype.val_injective _

omit [CharZero k] [FiniteDimensional k L] in
private theorem kostantWeightSliceEquiv_symm_coe {h e f : L} (t : IsSl2Triple h e f) (r : ℕ)
    (s : kostantWeightSlice (k := k) t r) :
    (((kostantWeightSliceEquiv (k := k) t r).symm s).val : L) = (s : L) :=
  congrArg (fun x : kostantWeightSlice (k := k) t r => (x : L))
    ((kostantWeightSliceEquiv (k := k) t r).apply_symm_apply s)

private def kostantWeightSplit {h e f : L} (t : IsSl2Triple h e f) (r : ℕ) :
    (W h (r + 1) × kostantWeightSlice (k := k) t r) ≃ₗ[k] W h r :=
  (LinearEquiv.prodCongr (negativeEvenWeightShift h r) (kostantWeightSliceEquiv (k := k) t r).symm).trans
    (sl2WeightSplit t (negativeWeightDegree r) (by dsimp [negativeWeightDegree]; omega))

private theorem kostantWeightSplit_coe {h e f : L} (t : IsSl2Triple h e f) (r : ℕ)
    (u : W h (r + 1)) (s : kostantWeightSlice (k := k) t r) :
    ((kostantWeightSplit (k := k) t r (u, s) : W h r) : L) = ⁅e, (u : L)⁆ + (s : L) := by
  simp only [kostantWeightSplit, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    sl2WeightSplit_apply, negativeEvenWeightShift_coe, kostantWeightSliceEquiv_symm_coe]

omit [CharZero k] [FiniteDimensional k L] in
private theorem kostantWeightSlice_le {h e f : L} (t : IsSl2Triple h e f) (r : ℕ) :
    kostantWeightSlice (k := k) t r ≤ B h r := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact negativeEvenWeightSpace_le_filtration h le_rfl y.property

private theorem bracket_weight_e_mem {h e f : L} (t : IsSl2Triple h e f) (r : ℕ)
    (u : W h (r + 1)) : ⁅(u : L), e⁆ ∈ B h r := by
  apply negativeEvenWeightSpace_le_filtration h le_rfl
  have hu := (W h r).neg_mem ((kostantWeightSplit (k := k) t r (u, 0)).property)
  change -((kostantWeightSplit (k := k) t r (u, 0) : W h r) : L) ∈ W h r at hu
  rwa [kostantWeightSplit_coe, Submodule.coe_zero, add_zero, lie_skew] at hu

private theorem kostantWeightQuotientSplit_apply {h e f : L} (t : IsSl2Triple h e f) (r : ℕ)
    (u : W h (r + 1)) (s : kostantWeightSlice (k := k) t r) :
    kostantWeightGradeEquiv h r (kostantWeightSplit (k := k) t r (u, s)) =
      ((B h (r + 1)).comap (B h r).subtype).mkQ ⟨(s : L) - ⁅(u : L), e⁆,
         (B h r).sub_mem (kostantWeightSlice_le (k := k) t r s.property) (bracket_weight_e_mem (k := k) t r u)⟩ := by
  rw [kostantWeightGradeEquiv_apply]
  apply congrArg ((B h (r + 1)).comap (B h r).subtype).mkQ
  apply Subtype.ext
  change ((kostantWeightSplit (k := k) t r (u, s) : W h r) : L) = (s : L) - ⁅(u : L), e⁆
  rw [kostantWeightSplit_coe, sub_eq_add_neg, lie_skew, add_comm]

/-- The direct split of a Kostant filtration grade follows from the actual `sl₂` relations. -/
def kostantGradeOfSl2 {h e f : L} (t : IsSl2Triple h e f) (r : ℕ) :
    KostantGrade e (B h 0) (B h r) (B h (r + 1)) where
  correction := W h (r + 1)
  slice := kostantWeightSlice (k := k) t r
  slice_le := kostantWeightSlice_le (k := k) t r
  bracket_e := bracket_weight_e_mem (k := k) t r
  bracket_higher := bracket_weight_mem_filtration h
  nilpotent := isNilpotent_leftAdjoint_of_weight_succ h r
  split := (kostantWeightSplit (k := k) t r).trans (kostantWeightGradeEquiv h r)
  split_apply := kostantWeightQuotientSplit_apply (k := k) t r

private theorem kostantGradeOfSl2_slice_le_ker {h e f : L} (t : IsSl2Triple h e f) (r : ℕ) :
    (kostantGradeOfSl2 t r).slice ≤ LinearMap.ker (leftAdjointDerivation k f).toLinearMap := by
  intro x hx
  change x ∈ kostantWeightSlice (k := k) t r at hx
  unfold kostantWeightSlice at hx
  obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
  change leftAdjointDerivation k f (y : L) = 0
  rw [leftAdjointDerivation_apply]
  exact congrArg Subtype.val hy

variable [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

/-- The normalizer corrections all have strictly negative adjoint weight. -/
theorem exists_kostantNormalizer_of_sl2Triple_with_weights {h e f : L}
    (t : IsSl2Triple h e f) (b : B h 0) :
    ∃ (l : List (NilpotentAdjoint k L)) (s : L), (∀ u ∈ l, ∃ r : ℕ, u.val ∈ W h (r + 1)) ∧
      s ∈ B h 0 ∧ ⁅f, s⁆ = 0 ∧ applyAdjointExponentials l (e + b.val) = e + s := by
  obtain ⟨N, hN⟩ := exists_kostantWeightFiltration_eq_bot (k := k) h
  let G (r : Fin N) := kostantGradeOfSl2 (k := k) t r.val
  have hCorrection (r : Fin N) (u : (G r).correction) :
      ∃ n : ℕ, u.val ∈ W h (n + 1) := ⟨r.val, u.property⟩
  obtain ⟨l, s, _, hWeights, hS, hs, he⟩ := exists_kostantNormalizer_of_graded_split_with
    e f (B h) N (kostantWeightFiltration_antitone h) hN G
    (fun r => kostantGradeOfSl2_slice_le_ker t r.val) (fun u => ∃ r, u ∈ W h (r + 1))
    hCorrection b
  exact ⟨l, s, hWeights, hS, hs, he⟩

/-- Every `e+b` in the weight filtration has a normalized representative in `e+ker(ad f)`. -/
theorem exists_kostantNormalizer_of_sl2Triple {h e f : L} (t : IsSl2Triple h e f)
    (b : B h 0) :
    ∃ (l : List (NilpotentAdjoint k L)) (s : L), ⁅f, s⁆ = 0 ∧
      applyAdjointExponentials l (e + b.val) = e + s := by
  obtain ⟨l, s, _, _, hs, he⟩ := exists_kostantNormalizer_of_sl2Triple_with_weights t b
  exact ⟨l, s, hs, he⟩

end Construction

end WideE
