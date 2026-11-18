import WideE.KostantSl2Filtration
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Algebra of the adjoint weight filtration

Weights add under multiplication in an associative representation.
A faithful Lie representation reflects each filtration stage.
-/

noncomputable section

namespace WideE

section Multiplication

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

private theorem mul_mem_negativeEvenWeightSpace (h : R) {r s : ℕ}
    {x y : R} (hx : x ∈ W h r) (hy : y ∈ W h s) : x * y ∈ W h (r + s) := by
  rw [Module.End.mem_eigenspace_iff] at hx hy ⊢
  change ⁅h, x⁆ = _ at hx
  change ⁅h, y⁆ = _ at hy
  change ⁅h, x * y⁆ = _
  have hLeibniz : ⁅h, x * y⁆ = ⁅h, x⁆ * y + x * ⁅h, y⁆ := by
    simp only [LieRing.of_associative_ring_bracket, sub_mul, mul_sub, mul_assoc]
    abel
  rw [hLeibniz, hx, hy, smul_mul_assoc, mul_smul_comm, ← add_smul]
  congr 1
  push_cast
  ring

/-- The filtration of an associative algebra is multiplicative. -/
theorem mul_mem_kostantWeightFiltration (h : R) {r s : ℕ} {x y : R}
    (hx : x ∈ B h r) (hy : y ∈ B h s) : x * y ∈ B h (r + s) := by
  refine Submodule.iSup_induction (motive := fun v => v * y ∈ B h (r + s))
    (fun i : {i : ℕ // r ≤ i} => W h i.val) hx ?_ (by
      change 0 * y ∈ B h (r + s)
      rw [zero_mul]
      exact zero_mem _) ?_
  · intro i a ha
    refine Submodule.iSup_induction (motive := fun v => a * v ∈ B h (r + s))
      (fun j : {j : ℕ // s ≤ j} => W h j.val) hy ?_ (by
        change a * 0 ∈ B h (r + s)
        rw [mul_zero]
        exact zero_mem _) ?_
    · intro j b hb
      exact negativeEvenWeightSpace_le_filtration h (add_le_add i.property j.property)
        (mul_mem_negativeEvenWeightSpace h ha hb)
    · intro b c hb hc
      rw [mul_add]
      exact add_mem hb hc
  · intro a b ha hb
    rw [add_mul]
    exact add_mem ha hb

/-- The (n)-th power of a positive filtration term has depth at least (n) times the depth. -/
theorem pow_mem_kostantWeightFiltration (h : R) {r : ℕ} {x : R}
    (hx : x ∈ B h r) (n : ℕ) : x ^ n ∈ B h (n * r) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul]
    apply negativeEvenWeightSpace_le_filtration h (i := 0) le_rfl
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅h, (1 : R)⁆ = ((-(2 : ℤ) * (0 : ℤ) : ℤ) : k) • (1 : R)
    simp [LieRing.of_associative_ring_bracket]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact mul_mem_kostantWeightFiltration h ih hx

variable [CharZero k] [FiniteDimensional k R]

/-- In finite dimension every strictly negative filtration term is nilpotent. -/
theorem isNilpotent_of_mem_kostantWeightFiltration (h : R) {r : ℕ} {x : R}
    (hr : 0 < r) (hx : x ∈ B h r) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := exists_kostantWeightFiltration_eq_bot (k := k) h
  refine ⟨n, (Submodule.mem_bot k).mp ?_⟩
  rw [← hn]
  have hnr : n ≤ n * r := by simpa using Nat.mul_le_mul_left n hr
  exact kostantWeightFiltration_antitone h hnr (pow_mem_kostantWeightFiltration h hx n)

end Multiplication

section Representation

variable {k L M : Type*} [Field k] [LieRing L] [LieAlgebra k L]
  [LieRing M] [LieAlgebra k M]

local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

theorem lieHom_mem_negativeEvenWeightSpace (f : L →ₗ⁅k⁆ M) (h : L) {r : ℕ} {x : L}
    (hx : x ∈ W h r) : f x ∈ W (f h) r := by
  apply Module.End.mem_eigenspace_iff.mpr
  have h' := Module.End.mem_eigenspace_iff.mp hx
  change ⁅h, x⁆ = _ at h'
  change ⁅f h, f x⁆ = _
  rw [← LieHom.map_lie, h', LieHom.map_smul]

theorem lieHom_mem_kostantWeightFiltration (f : L →ₗ⁅k⁆ M) (h : L) {r : ℕ} {x : L}
    (hx : x ∈ B h r) : f x ∈ B (f h) r := by
  refine Submodule.iSup_induction (motive := fun x => f x ∈ B (f h) r)
    (fun i : {i : ℕ // r ≤ i} => W h i.val) hx ?_ ?_ ?_
  · intro i y hy
    exact negativeEvenWeightSpace_le_filtration (f h) i.property (lieHom_mem_negativeEvenWeightSpace f h hy)
  · change f 0 ∈ B (f h) r
    rw [LieHom.map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [LieHom.map_add]
    exact add_mem ha hb

private theorem lie_h_mem_kostantWeightFiltration (h : M) {r : ℕ} {x : M}
    (hx : x ∈ B h r) : ⁅h, x⁆ ∈ B h r := by
  refine Submodule.iSup_induction (motive := fun x => ⁅h, x⁆ ∈ B h r)
    (fun i : {i : ℕ // r ≤ i} => W h i.val) hx ?_ ?_ ?_
  · intro i y hy
    have hW := Module.End.mem_eigenspace_iff.mp hy
    change ⁅h, y⁆ = _ at hW
    rw [hW]
    exact (B h r).smul_mem _ (negativeEvenWeightSpace_le_filtration h i.property hy)
  · change ⁅h, (0 : M)⁆ ∈ B h r
    rw [lie_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [lie_add]
    exact add_mem ha hb

/-- The filtration in a faithful representation restricts to the Lie algebra filtration. -/
theorem mem_kostantWeightFiltration_of_lieHom [FiniteDimensional k M]
    (f : L →ₗ⁅k⁆ M) (hf : Function.Injective f) (h : L) {r : ℕ} {x : L}
    (hx : f x ∈ B (f h) r) : x ∈ B h r := by
  classical
  let D := LieModule.toEnd k M M (f h)
  let S := LinearMap.range f.toLinearMap ⊓ B (f h) r
  have hS (v : M) (hv : v ∈ S) : D v ∈ S := by
    have h₂ := lie_h_mem_kostantWeightFiltration (f h) hv.2
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hv.1
    exact ⟨⟨⁅h, y⁆, LieHom.map_lie f h y⟩, h₂⟩
  have hSpan : S ≤ ⨆ μ : k, D.eigenspace μ := by
    refine inf_le_right.trans (iSup_le fun i => ?_)
    exact le_iSup (fun μ : k => D.eigenspace μ) ((-(2 : ℤ) * (i.val : ℤ) : ℤ) : k)
  have hS' : S = ⨆ μ : k, S ⊓ D.eigenspace μ := by
    simpa only [Module.End.eigenspace] using
      ((inf_eq_left.mpr hSpan).symm.trans (Submodule.inf_iSup_genEigenspace hS 1))
  have hContained : S ≤ (B h r).map f.toLinearMap := by
    rw [hS']
    apply iSup_le
    intro μ v hv
    by_cases hμ : ∃ i : {i : ℕ // r ≤ i}, ((-(2 : ℤ) * (i.val : ℤ) : ℤ) : k) = μ
    · obtain ⟨i, hi⟩ := hμ
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hv.1.1
      refine Submodule.mem_map.mpr ⟨y, negativeEvenWeightSpace_le_filtration h i.property ?_, rfl⟩
      apply Module.End.mem_eigenspace_iff.mpr
      have hV := Module.End.mem_eigenspace_iff.mp hv.2
      change ⁅f h, f y⁆ = μ • f y at hV
      change ⁅h, y⁆ = ((-(2 : ℤ) * (i.val : ℤ) : ℤ) : k) • y
      apply hf
      rw [LieHom.map_lie, LieHom.map_smul, hi]
      exact hV
    · have hDisj : Disjoint (D.eigenspace μ) (B (f h) r) := by
        refine (iSupIndep_def.mp D.eigenspaces_iSupIndep μ).mono_right ?_
        apply iSup_le
        intro i
        exact le_iSup₂ (f := fun c (_ : c ≠ μ) => D.eigenspace c) _
          (fun hi => hμ ⟨i, hi⟩)
      have hZero := Submodule.disjoint_def.mp hDisj v hv.2 hv.1.2
      rw [hZero]
      exact zero_mem _
  have hv : f x ∈ S := ⟨⟨x, rfl⟩, hx⟩
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hContained hv)
  exact (hf hyx) ▸ hy

end Representation

section EntrywiseScalarChange

variable {k K ι : Type*} [Field k] [Field K] [Fintype ι] [DecidableEq ι]

/-- Mapping the entries of matrices along a field homomorphism preserves the
adjoint weight filtration, with the grading matrix transported entrywise. -/
theorem mapMatrix_mem_kostantWeightFiltration (f : k →+* K) (a : Matrix ι ι k)
    {r : ℕ} {x : Matrix ι ι k} (hx : x ∈ kostantWeightFiltration (k := k) a r) :
    f.mapMatrix x ∈ kostantWeightFiltration (k := K) (f.mapMatrix a) r := by
  let B := kostantWeightFiltration (k := K) (f.mapMatrix a) r
  refine Submodule.iSup_induction (motive := fun x => f.mapMatrix x ∈ B)
    (fun i : {i : ℕ // r ≤ i} => negativeEvenWeightSpace (k := k) a i.val) hx ?_ ?_ ?_
  · intro i y hy
    apply negativeEvenWeightSpace_le_filtration (f.mapMatrix a) i.property
    apply Module.End.mem_eigenspace_iff.mpr
    let n : ℤ := -(2 : ℤ) * (i.val : ℤ)
    have hWeight : ⁅a, y⁆ = (n : k) • y := Module.End.mem_eigenspace_iff.mp hy
    have hCoeff : f.mapMatrix ((n : k) • y) = (n : K) • f.mapMatrix y := by
      apply Matrix.ext
      intro l m
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        map_mul, map_intCast]
    have h := congrArg (f.mapMatrix (m := ι)) hWeight
    rw [LieRing.of_associative_ring_bracket, map_sub, map_mul, map_mul, hCoeff] at h
    exact h
  · change f.mapMatrix (0 : Matrix ι ι k) ∈ B
    rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

end EntrywiseScalarChange

end WideE
