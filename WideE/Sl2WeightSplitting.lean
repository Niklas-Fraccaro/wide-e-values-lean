import Mathlib.Algebra.Lie.Sl2
import WideE.AdjointWeightNilpotence
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The nonpositive-weight split for an `sl₂` triple

On a negative weight space, lowering after raising is injective. The proof
uses the lowering recurrence on a vector killed by that composite. In finite
dimension this gives a direct decomposition of a nonpositive weight space
into the image from two degrees below and the slice in the kernel of lowering.
-/

noncomputable section

namespace WideE

section WeightShifts

variable {k L M : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M]

local notation "ρ" => LieModule.toEnd k L M

omit [CharZero k] in
private theorem lie_h_lie_f_of_weight {h e f : L} (t : IsSl2Triple h e f)
    (c : k) (x : M) (hx : ⁅h, x⁆ = c • x) : ⁅h, ⁅f, x⁆⁆ = (c - 2) • ⁅f, x⁆ := by
  rw [leibniz_lie, t.lie_lie_smul_f k, neg_lie, smul_lie, hx, lie_smul, sub_smul, sub_eq_add_neg, add_comm]

omit [CharZero k] in
private theorem lie_h_lie_e_of_weight {h e f : L} (t : IsSl2Triple h e f)
    (c : k) (x : M) (hx : ⁅h, x⁆ = c • x) : ⁅h, ⁅e, x⁆⁆ = (c + 2) • ⁅e, x⁆ := by
  rw [leibniz_lie, t.lie_h_e_smul k, smul_lie, hx, lie_smul, add_smul, add_comm]

/-- If lowering is nilpotent, the composite of raising then lowering has
trivial kernel on each strictly negative integer weight space. -/
theorem sl2_raise_lower_kernel_of_negative_weight {h e f : L} (t : IsSl2Triple h e f)
    (hNil : IsNilpotent (ρ f)) (m : ℤ) (hm : m < 0) (x : M)
    (hx : ⁅h, x⁆ = (m : k) • x) (hKer : ⁅f, ⁅e, x⁆⁆ = 0) : x = 0 := by
  let F : Module.End k M := ρ f
  have hSucc (n : ℕ) : (F ^ (n + 1)) x = ⁅f, (F ^ n) x⁆ := by
    rw [pow_succ', Module.End.mul_apply]
    rfl
  have hWeight (n : ℕ) : ⁅h, (F ^ n) x⁆ = ((m : k) - 2 * (n : k)) • (F ^ n) x := by
    induction n with
    | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, sub_zero] using hx
    | succ n ih =>
      rw [hSucc, lie_h_lie_f_of_weight t _ _ ih]
      congr 1
      push_cast
      ring
  have hRec (n : ℕ) : ⁅e, (F ^ (n + 1)) x⁆ =
      (((n + 1 : ℕ) : k) * ((m : k) - (n : k))) • (F ^ n) x := by
    induction n with
    | zero =>
      rw [hSucc, pow_zero, Module.End.one_apply, leibniz_lie, t.lie_e_f, hKer, add_zero, hx]
      norm_num
    | succ n ih =>
      rw [hSucc, leibniz_lie, t.lie_e_f, hWeight, ih, lie_smul, ← hSucc, ← add_smul]
      congr 1
      push_cast
      ring
  have hNonzero (n : ℕ) : ((m : k) - (n : k)) ≠ 0 := by
    rw [← Int.cast_natCast, ← Int.cast_sub]
    intro hc
    have hz : m - (n : ℤ) = 0 := Int.cast_eq_zero.mp hc
    omega
  have hBack (n : ℕ) (hn : (F ^ n) x = 0) : x = 0 := by
    induction n with
    | zero => simpa only [pow_zero, Module.End.one_apply] using hn
    | succ n ih =>
      apply ih
      have h := hRec n
      rw [hn, lie_zero] at h
      exact (smul_eq_zero.mp h.symm).resolve_left
        (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (hNonzero n))
  obtain ⟨n, hn⟩ := hNil
  exact hBack n (DFunLike.congr_fun hn x)

/-- The integer weight space of `h` in a representation. -/
abbrev sl2WeightSpace (h : L) (m : ℤ) : Submodule k M := (ρ h).eigenspace (m : k)

local notation "W" => sl2WeightSpace (k := k) (M := M)

/-- Raising from weight `m - 2` to weight `m`. -/
def sl2WeightRaise {h e f : L} (t : IsSl2Triple h e f) (m : ℤ) :
    W h (m - 2) →ₗ[k] W h m :=
  (ρ e).restrict fun x hx => by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change ⁅h, ⁅e, x⁆⁆ = (m : k) • ⁅e, x⁆
    rw [lie_h_lie_e_of_weight t _ _ hx]
    congr 1
    push_cast
    ring

/-- Lowering from weight `m` to weight `m - 2`. -/
def sl2WeightLower {h e f : L} (t : IsSl2Triple h e f) (m : ℤ) :
    W h m →ₗ[k] W h (m - 2) :=
  (ρ f).restrict fun x hx => by
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    change ⁅h, ⁅f, x⁆⁆ = ((m - 2 : ℤ) : k) • ⁅f, x⁆
    rw [lie_h_lie_f_of_weight t _ _ hx]
    push_cast
    rfl

/-- The nonpositive-weight decomposition needed for the graded normalization. -/
def sl2WeightRaisePlusKernelEquiv [FiniteDimensional k M] {h e f : L}
    (t : IsSl2Triple h e f) (hNil : IsNilpotent (ρ f)) (m : ℤ) (hm : m ≤ 0) :
    (W h (m - 2) × LinearMap.ker (sl2WeightLower (k := k) (M := M) t m))
      ≃ₗ[k] W h m := by
  let U := W h (m - 2)
  let V := W h m
  let E : U →ₗ[k] V := sl2WeightRaise t m
  let F : V →ₗ[k] U := sl2WeightLower t m
  let S := LinearMap.ker F
  let T := F.comp E
  have hI : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    refine eq_bot_iff.mpr fun x hx => ?_
    apply (Submodule.mem_bot k).mpr
    apply Subtype.ext
    have hxF : T x = 0 := hx
    have h0 : ⁅f, ⁅e, (x : M)⁆⁆ = 0 := congrArg Subtype.val hxF
    have he : ⁅h, (x : M)⁆ = ((m - 2 : ℤ) : k) • (x : M) :=
      Module.End.mem_eigenspace_iff.mp x.property
    exact sl2_raise_lower_kernel_of_negative_weight t hNil (m - 2) (by omega) x he h0
  have hSurj := LinearMap.injective_iff_surjective.mp hI
  let g : U × S →ₗ[k] V := E.comp (LinearMap.fst k U S) + S.subtype.comp (LinearMap.snd k U S)
  refine LinearEquiv.ofBijective g ⟨?_, ?_⟩
  · intro ⟨u,s⟩ ⟨u',s'⟩ hEq
    change E u + s.val = E u' + s'.val at hEq
    have hCompare := congrArg F hEq
    have hs : F s.val = 0 := s.property
    have hs' : F s'.val = 0 := s'.property
    rw [map_add, map_add, hs, hs', add_zero, add_zero] at hCompare
    have hU : u = u' := hI hCompare
    subst u'
    exact Prod.ext rfl (Subtype.ext (add_left_cancel hEq))
  · intro v
    obtain ⟨u, hu⟩ := hSurj (F v)
    have hS : v - E u ∈ S := by
      change F (v - E u) = 0
      rw [map_sub, show F (E u) = F v from hu, sub_self]
    refine ⟨(u, ⟨v - E u, hS⟩), ?_⟩
    change E u + (v - E u) = v
    rw [add_comm, sub_add_cancel]

/-- The lowering operator of an `sl₂` triple is nilpotent in every finite-dimensional representation. -/
theorem sl2_lower_isNilpotent [FiniteDimensional k M] {h e f : L} (t : IsSl2Triple h e f) :
    IsNilpotent (ρ f) := by
  apply isNilpotent_of_lie_eq_smul_ne_zero (ρ h) (ρ f) (-(2 : k)) (by norm_num)
  rw [← LieHom.map_lie, t.lie_lie_smul_f k, LieHom.map_neg, LieHom.map_smul, neg_smul]

/-- The nonpositive weight splitting for any finite-dimensional representation. -/
def sl2WeightSplit [FiniteDimensional k M] {h e f : L}
    (t : IsSl2Triple h e f) (m : ℤ) (hm : m ≤ 0) :
    (W h (m - 2) × LinearMap.ker (sl2WeightLower (k := k) (M := M) t m)) ≃ₗ[k] W h m :=
  sl2WeightRaisePlusKernelEquiv t (sl2_lower_isNilpotent t) m hm

@[simp] theorem sl2WeightSplit_apply [FiniteDimensional k M] {h e f : L}
    (t : IsSl2Triple h e f) (m : ℤ) (hm : m ≤ 0)
    (u : W h (m - 2)) (s : LinearMap.ker (sl2WeightLower (k := k) (M := M) t m)) :
    ((sl2WeightSplit t m hm (u, s) : W h m) : M) = ⁅e, (u : M)⁆ + (s.val : M) := rfl

end WeightShifts

end WideE
