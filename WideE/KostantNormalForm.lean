import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Algebra.Lie.BaseChange

/-!
# Normalization by positive-filtration adjoint exponentials

The finite normalization step in the construction of a Kostant slice.
The coefficient in each grade is split by a linear equivalence into the
image of the adjoint correction and the slice direction. Exponentiating
the correction changes the linear calculation only in higher grades.
-/

noncomputable section

open scoped LieAlgebra

namespace WideE

section Adjoint

variable (k : Type*) [CommRing k] {L : Type*} [LieRing L] [LieAlgebra k L]

/-- The inner derivation `x ↦ [u,x]`. -/
def leftAdjointDerivation (u : L) : LieDerivation k L L := -LieDerivation.inner k L L u

@[simp] theorem leftAdjointDerivation_apply (u x : L) :
    leftAdjointDerivation k u x = ⁅u, x⁆ := by
  change -⁅x, u⁆ = ⁅u, x⁆
  exact lie_skew u x

/-- An endomorphism that strictly raises a bounded filtration is nilpotent. -/
theorem isNilpotent_of_raises_filtration (B : ℕ → Submodule k L) (n : ℕ)
    (hFirst : B 0 = ⊤) (hLast : B n = ⊥) (D : Module.End k L)
    (hD : ∀ i : ℕ, ∀ x ∈ B i, D x ∈ B (i + 1)) : IsNilpotent D := by
  have hPow (x : L) (i : ℕ) : (D ^ i) x ∈ B i := by
    induction i with
    | zero => rw [pow_zero, hFirst]; exact Submodule.mem_top
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hD i _ ih
  refine ⟨n, LinearMap.ext fun x => ?_⟩
  have hx := hPow x n
  rw [hLast, Submodule.mem_bot] at hx
  exact hx

end Adjoint

section Step

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

/-- On `e+b`, the true nilpotent adjoint exponential has the asserted linear
correction modulo the next filtration submodule. -/
theorem leftAdjointExp_sub_linear_mem (B M : Submodule k L) (hMB : M ≤ B)
    (u e b : L) (hb : b ∈ B) (he : ⁅u, e⁆ ∈ B)
    (hRaise : ∀ x ∈ B, ⁅u, x⁆ ∈ M)
    (hnil : IsNilpotent (leftAdjointDerivation k u).toLinearMap) :
    LieDerivation.exp (leftAdjointDerivation k u) hnil (e + b) - (e + b + ⁅u, e⁆) ∈ M := by
  let D := (leftAdjointDerivation k u).toLinearMap
  have hD (x : L) : D x = ⁅u, x⁆ := leftAdjointDerivation_apply k u x
  have hD₁ : D (e + b) ∈ B := by
    rw [map_add, hD, hD]
    exact B.add_mem he (hMB (hRaise b hb))
  have hTail (i : ℕ) : (D ^ (i + 2)) (e + b) ∈ M := by
    induction i with
    | zero =>
      rw [Nat.zero_add, pow_succ', pow_one, Module.End.mul_apply, hD]
      exact hRaise _ hD₁
    | succ i ih =>
      rw [show i + 1 + 2 = (i + 2) + 1 by omega, pow_succ', Module.End.mul_apply, hD]
      exact hRaise _ (hMB ih)
  have hnil' : IsNilpotent D := hnil
  obtain ⟨n, hn⟩ := hnil'
  have hBound : D ^ (2 + n) = 0 := pow_eq_zero_of_le (by omega) hn
  have hExp : LieDerivation.exp (leftAdjointDerivation k u) hnil (e + b) =
      ∑ i ∈ Finset.range (2 + n), (i.factorial : ℚ)⁻¹ • (D ^ i) (e + b) := by
    rw [LieDerivation.exp_map_apply]
    change IsNilpotent.exp D (e + b) = _
    rw [IsNilpotent.exp_eq_sum hBound, LinearMap.sum_apply]
    rfl
  rw [hExp, Finset.sum_range_add]
  have hHead : (∑ i ∈ Finset.range 2, (i.factorial : ℚ)⁻¹ • (D ^ i) (e + b)) =
      e + b + ⁅u, e⁆ + ⁅u, b⁆ := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [zero_add, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
      pow_zero, pow_one, Module.End.one_apply, hD, lie_add, add_assoc]
  rw [hHead]
  have hRest : (∑ i ∈ Finset.range n, ((2 + i).factorial : ℚ)⁻¹ • (D ^ (2 + i)) (e + b)) ∈ M := by
    refine M.sum_mem fun i _ => ?_
    rw [← IsScalarTower.algebraMap_smul k, add_comm 2 i]
    exact M.smul_mem _ (hTail i)
  convert M.add_mem (hRaise b hb) hRest using 1; abel

end Step

section Grade

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

/-- One grade of the Kostant reduction, with its linear direct decomposition. -/
structure KostantGrade (e : L) (B₀ B M : Submodule k L) where
  correction : Submodule k L
  slice : Submodule k L
  slice_le : slice ≤ B
  bracket_e (u : correction) : ⁅(u : L), e⁆ ∈ B
  bracket_higher (u : correction) (x : L) : x ∈ B₀ → ⁅(u : L), x⁆ ∈ M
  nilpotent (u : correction) : IsNilpotent (leftAdjointDerivation k (u : L)).toLinearMap
  split : (correction × slice) ≃ₗ[k] (B ⧸ M.comap B.subtype)
  split_apply (u : correction) (s : slice) :
    split (u, s) = (M.comap B.subtype).mkQ ⟨(s : L) - ⁅(u : L), e⁆,
      B.sub_mem (slice_le s.property) (bracket_e u)⟩

namespace KostantGrade

variable {e : L} {B₀ B M : Submodule k L} (g : KostantGrade e B₀ B M)

/-- The uniquely determined correction and slice term for this grade. -/
def choose (x : B) : g.correction × g.slice :=
  g.split.symm ((M.comap B.subtype).mkQ x)

/-- The chosen correction makes the remainder lie in the next grade. -/
theorem choose_mem (x : B) :
    (x : L) + ⁅((g.choose x).1 : L), e⁆ - ((g.choose x).2 : L) ∈ M := by
  let u := (g.choose x).1
  let s := (g.choose x).2
  have h : g.split (u, s) = (M.comap B.subtype).mkQ x :=
    g.split.apply_symm_apply _
  rw [g.split_apply] at h
  have hDiff := (Submodule.Quotient.eq _).mp h.symm
  change (x : L) - ((s : L) - ⁅(u : L), e⁆) ∈ M at hDiff
  convert hDiff using 1; abel

/-- Any correction satisfying the next-grade condition is the chosen one. -/
theorem choose_unique (x : B) (u : g.correction) (s : g.slice)
    (h : (x : L) + ⁅(u : L), e⁆ - (s : L) ∈ M) : (u, s) = g.choose x := by
  apply g.split.injective
  rw [g.split_apply, choose, LinearEquiv.apply_symm_apply]
  apply (Submodule.Quotient.eq _).mpr
  change (s : L) - ⁅(u : L), e⁆ - (x : L) ∈ M
  convert M.neg_mem h using 1; abel

variable [CharZero k] [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

/-- The adjoint exponential realizes the chosen correction on an entire element,
while the previously normalized terms stay in their grades. -/
theorem exp_choose_mem (hB : B ≤ B₀) (hM : M ≤ B₀) (a : L) (ha : a ∈ B₀) (x : B) :
    LieDerivation.exp (leftAdjointDerivation k (((g.choose x).1 : g.correction) : L))
      (g.nilpotent (g.choose x).1) (e + (a + x.val)) - (e + (a + ((g.choose x).2 : L))) ∈ M := by
  let u := (g.choose x).1
  let s := (g.choose x).2
  have h := leftAdjointExp_sub_linear_mem B₀ M hM (u : L) e (a + x.val)
    (B₀.add_mem ha (hB x.property)) (hB (g.bracket_e u)) (g.bracket_higher u) (g.nilpotent u)
  convert M.add_mem h (g.choose_mem x) using 1; abel

end KostantGrade

end Grade

section Iteration

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

/-- A correction by a nilpotent inner derivation. -/
abbrev NilpotentAdjoint (k L : Type*) [CommRing k] [LieRing L] [LieAlgebra k L] :=
  {u : L // IsNilpotent (leftAdjointDerivation k u).toLinearMap}

/-- Apply the adjoint exponentials in the order of the corrections. -/
def applyAdjointExponentials (l : List (NilpotentAdjoint k L)) (x : L) : L :=
  l.foldl (fun y u => LieDerivation.exp (leftAdjointDerivation k u.val) u.property y) x

omit [CharZero k] [IsScalarTower ℚ k L] in
/-- Adding a correction to the end applies its adjoint exponential last. -/
theorem applyAdjointExponentials_append_singleton
    (l : List (NilpotentAdjoint k L)) (u : NilpotentAdjoint k L) (x : L) :
    applyAdjointExponentials (l ++ [u]) x =
      LieDerivation.exp (leftAdjointDerivation k u.val) u.property (applyAdjointExponentials l x) := by
  rw [applyAdjointExponentials, List.foldl_append]
  rfl

/-- Finite elimination records a property shared by the grade corrections and keeps
the slice term in the initial filtration submodule. -/
theorem exists_kostantNormalizer_of_graded_split_with (e f : L)
    (B : ℕ → Submodule k L) (N : ℕ) (hAnti : Antitone B) (hLast : B N = ⊥)
    (g : ∀ r : Fin N, KostantGrade e (B 0) (B r.val) (B (r.val + 1)))
    (hSlice : ∀ r, (g r).slice ≤ LinearMap.ker (leftAdjointDerivation k f).toLinearMap)
    (p : L → Prop) (hCorrection : ∀ (r : Fin N) (u : (g r).correction), p u.val)
    (b : B 0) :
    ∃ (l : List (NilpotentAdjoint k L)) (s : L), l.length = N ∧
      (∀ u ∈ l, p u.val) ∧ s ∈ B 0 ∧ ⁅f, s⁆ = 0 ∧
      applyAdjointExponentials l (e + b.val) = e + s := by
  let S := LinearMap.ker (leftAdjointDerivation k f).toLinearMap
  let S₀ : Submodule k L := S ⊓ B 0
  have hPartial (n : ℕ) (hn : n ≤ N) :
      ∃ (l : List (NilpotentAdjoint k L)) (s : S₀) (x : B n),
        l.length = n ∧ (∀ u ∈ l, p u.val) ∧
          applyAdjointExponentials l (e + b.val) = e + (s.val + x.val) := by
    induction n with
    | zero => exact ⟨[], 0, b, rfl, by simp, by simp [applyAdjointExponentials]⟩
    | succ n ih =>
      obtain ⟨l, s, x, hLen, hP, hX⟩ := ih (Nat.le_of_succ_le hn)
      let i : Fin N := ⟨n, Nat.lt_of_succ_le hn⟩
      let w := g i
      let u := (w.choose x).1
      let t := (w.choose x).2
      let v : NilpotentAdjoint k L := ⟨u, w.nilpotent u⟩
      let s' : S₀ := ⟨s + t, ⟨S.add_mem s.property.1 (hSlice i t.property),
        (B 0).add_mem s.property.2 (hAnti (Nat.zero_le n) (w.slice_le t.property))⟩⟩
      let d := LieDerivation.exp (leftAdjointDerivation k v.val) v.property
      let y : B (n + 1) := ⟨d (e + (s.val + x.val)) - (e + s'.val),
        w.exp_choose_mem (hAnti (Nat.zero_le n)) (hAnti (Nat.zero_le (n + 1))) s.val s.property.2 x⟩
      refine ⟨l ++ [v], s', y, ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton, hLen]
      · intro u' hu'
        rcases List.mem_append.mp hu' with hu' | hu'
        · exact hP u' hu'
        · rw [List.mem_singleton] at hu'
          subst u'
          exact hCorrection i u
      · rw [applyAdjointExponentials_append_singleton, hX]
        change d (e + (s.val + x.val)) = e + (s'.val + (d (e + (s.val + x.val)) - (e + s'.val)))
        abel
  obtain ⟨l, s, x, hLen, hP, hX⟩ := hPartial N le_rfl
  have hx0 : x.val = 0 := (Submodule.mem_bot k).mp (hLast ▸ x.property)
  refine ⟨l, s, hLen, hP, s.property.2, ?_, ?_⟩
  · have hs : leftAdjointDerivation k f s.val = 0 := s.property.1
    rwa [leftAdjointDerivation_apply] at hs
  · rwa [hx0, add_zero] at hX

/-- Finite elimination of the adjoint-image part of every grade sends `e+b`
to `e+s` with `[f,s]=0`. The corrections use the supplied direct sums grade by grade. -/
theorem exists_kostantNormalizer_of_graded_split (e f : L)
    (B : ℕ → Submodule k L) (N : ℕ) (hAnti : Antitone B) (hLast : B N = ⊥)
    (g : ∀ r : Fin N, KostantGrade e (B 0) (B r.val) (B (r.val + 1)))
    (hSlice : ∀ r, (g r).slice ≤ LinearMap.ker (leftAdjointDerivation k f).toLinearMap)
    (b : B 0) :
    ∃ (l : List (NilpotentAdjoint k L)) (s : L), l.length = N ∧ ⁅f, s⁆ = 0 ∧
      applyAdjointExponentials l (e + b.val) = e + s := by
  obtain ⟨l, s, hLen, _, _, hs, hNorm⟩ :=
    exists_kostantNormalizer_of_graded_split_with e f B N hAnti hLast g hSlice
      (fun _ => True) (fun _ _ => trivial) b
  exact ⟨l, s, hLen, hs, hNorm⟩

end Iteration

section Naturality

variable {k k' L L' : Type*} [Field k] [Field k']
variable [LieRing L] [LieRing L'] [LieAlgebra k L] [LieAlgebra k L'] [LieAlgebra k' L']
variable [LieAlgebra ℚ L] [LieAlgebra ℚ L']

/-- Finite adjoint exponentials commute with a bracket-preserving scalar extension. -/
theorem map_leftAdjointExp (j : L →ₗ⁅k⁆ L') (u x : L)
    (h : IsNilpotent (leftAdjointDerivation k u).toLinearMap)
    (h' : IsNilpotent (leftAdjointDerivation k' (j u)).toLinearMap) :
    j (LieDerivation.exp (leftAdjointDerivation k u) h x) =
      LieDerivation.exp (leftAdjointDerivation k' (j u)) h' (j x) := by
  let D := (leftAdjointDerivation k u).toLinearMap
  let D' := (leftAdjointDerivation k' (j u)).toLinearMap
  change j (IsNilpotent.exp D x) = IsNilpotent.exp D' (j x)
  obtain ⟨n, hn⟩ : IsNilpotent D := h
  obtain ⟨n', hn'⟩ : IsNilpotent D' := h'
  let N := max n n'
  have hN : D ^ N = 0 := pow_eq_zero_of_le (le_max_left n n') hn
  have hN' : D' ^ N = 0 := pow_eq_zero_of_le (le_max_right n n') hn'
  have hPow (i : ℕ) : j ((D ^ i) x) = (D' ^ i) (j x) := by
    induction i with
    | zero => simp only [pow_zero, Module.End.one_apply]
    | succ i ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      change j (leftAdjointDerivation k u ((D ^ i) x)) =
        leftAdjointDerivation k' (j u) ((D' ^ i) (j x))
      rw [leftAdjointDerivation_apply, leftAdjointDerivation_apply, LieHom.map_lie, ih]
  change j.toLinearMap (IsNilpotent.exp D x) = IsNilpotent.exp D' (j x)
  rw [IsNilpotent.exp_eq_sum hN, IsNilpotent.exp_eq_sum hN', LinearMap.sum_apply, LinearMap.sum_apply,
    map_sum]
  simp only [LinearMap.smul_apply, map_rat_smul, LieHom.coe_toLinearMap, hPow]

omit [LieAlgebra ℚ L] [LieAlgebra ℚ L'] in
/-- The uniquely determined linear correction is preserved under scalar extension of the grades. -/
theorem KostantGrade.map_choose (j : L →ₗ⁅k⁆ L') {e : L}
    {A B M : Submodule k L} {A' B' M' : Submodule k' L'}
    (g : KostantGrade e A B M) (g' : KostantGrade (j e) A' B' M')
    (hU : ∀ u ∈ g.correction, j u ∈ g'.correction)
    (hS : ∀ s ∈ g.slice, j s ∈ g'.slice) (hM : ∀ x ∈ M, j x ∈ M')
    (x : B) (hx : j x.val ∈ B') :
    ((⟨j (g.choose x).1, hU _ (g.choose x).1.property⟩ : g'.correction),
      (⟨j (g.choose x).2, hS _ (g.choose x).2.property⟩ : g'.slice)) = g'.choose ⟨j x.val, hx⟩ := by
  apply g'.choose_unique
  change j x.val + ⁅j (g.choose x).1, j e⁆ - j (g.choose x).2 ∈ M'
  rw [← LieHom.map_lie, ← LieHom.map_add, ← LieHom.map_sub]
  exact hM _ (g.choose_mem x)

end Naturality

end WideE
