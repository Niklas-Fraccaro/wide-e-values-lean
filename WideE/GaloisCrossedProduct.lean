/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Tau Ceti contributors

Adapted from TauCeti/Algebra/CrossedProduct/{Basic,CentralSimple,Injectivity}.lean
at cd41bffcb343151b3e58c89392e206b11fe78c1c. This version works with normalized
Galois cocycles on mathlib 4.19 and uses the C₁ matrix splitting theorem.
-/
import WideE.CentralSimpleC1
import Mathlib.Algebra.Equiv.TransferInstance
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Crossed products of normalized Galois 2-cocycles

Over a Galois extension `E/F`, a 2-cocycle `c` specifies the multiplication
`(x u_σ) (y u_τ) = x σ(y) c(σ,τ) u_(στ)` on the space with basis `u_σ`.
-/

noncomputable section

namespace WideE

/-- A normalized multiplicative 2-cocycle for field automorphisms acting on units. -/
structure GaloisTwoCocycle (F E : Type*) [Field F] [Field E] [Algebra F E] where
  value : (E ≃ₐ[F] E) → (E ≃ₐ[F] E) → Eˣ
  one_left : ∀ σ, value 1 σ = 1
  one_right : ∀ σ, value σ 1 = 1
  cocycle : ∀ σ τ ρ, value σ τ * value (σ * τ) ρ = (σ • value τ ρ) * value σ (τ * ρ)

attribute [simp] GaloisTwoCocycle.one_left GaloisTwoCocycle.one_right

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A multiplicative 2-cocycle is trivial if it is the coboundary of a unit-valued cochain. -/
def GaloisTwoCocycle.IsCoboundary (c : GaloisTwoCocycle F E) : Prop :=
  ∃ b : (E ≃ₐ[F] E) → Eˣ, ∀ σ τ, c.value σ τ = b σ * (σ • b τ) / b (σ * τ)

variable (c : GaloisTwoCocycle F E)

/-- The crossed product with multiplication twisted by the cocycle. -/
structure GaloisCrossedProduct (c : GaloisTwoCocycle F E) : Type _ where
  ofFinsupp ::
  toFinsupp : (E ≃ₐ[F] E) →₀ E

namespace GaloisCrossedProduct

/-- Coordinates in the basis indexed by the automorphisms. -/
def coordinates : GaloisCrossedProduct c ≃ ((E ≃ₐ[F] E) →₀ E) :=
  ⟨toFinsupp, ofFinsupp, fun _ => rfl, fun _ => rfl⟩

instance : AddCommGroup (GaloisCrossedProduct c) := (coordinates c).addCommGroup
instance : Module E (GaloisCrossedProduct c) := (coordinates c).module E
instance : Module F (GaloisCrossedProduct c) := (coordinates c).module F

instance : IsScalarTower F E (GaloisCrossedProduct c) where
  smul_assoc r x a := (coordinates c).injective (smul_assoc r x a.toFinsupp)

/-- The basis element at `σ` will satisfy `u_σ x = σ(x) u_σ`. -/
def basis : Basis (E ≃ₐ[F] E) E (GaloisCrossedProduct c) :=
  Basis.ofRepr ((coordinates c).linearEquiv E)

instance : Mul (GaloisCrossedProduct c) where
  mul a b := ((basis c).repr a).sum fun σ x => ((basis c).repr b).sum fun τ y =>
    (x * σ y * c.value σ τ) • basis c (σ * τ)

instance : One (GaloisCrossedProduct c) where
  one := basis c 1

variable {c}

/-- Multiplication in coordinates. -/
theorem mul_def (a b : GaloisCrossedProduct c) :
    a * b = ((basis c).repr a).sum (fun σ x => ((basis c).repr b).sum fun τ y =>
      (x * σ y * c.value σ τ) • basis c (σ * τ)) :=
  rfl

theorem basis_one : basis c 1 = (1 : GaloisCrossedProduct c) := rfl

@[simp] theorem smul_basis_mul_smul_basis (σ τ : E ≃ₐ[F] E) (x y : E) :
    (x • basis c σ) * (y • basis c τ) = (x * σ y * c.value σ τ) • basis c (σ * τ) := by
  simp [mul_def, Finsupp.smul_single]

@[elab_as_elim]
theorem induction_on {motive : GaloisCrossedProduct c → Prop}
    (a : GaloisCrossedProduct c) (zero : motive 0)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (smul_basis : ∀ (σ : E ≃ₐ[F] E) (x : E), motive (x • basis c σ)) : motive a := by
  rw [← (basis c).repr.symm_apply_apply a]
  induction (basis c).repr a using Finsupp.induction_linear with
  | zero => simpa using zero
  | add f g hf hg => simpa using add _ _ hf hg
  | single σ x => simpa using smul_basis σ x

instance : NonUnitalNonAssocRing (GaloisCrossedProduct c) where
  zero_mul a := by simp [mul_def]
  mul_zero a := by simp [mul_def]
  left_distrib a b d := by
    simp only [mul_def, map_add, ← Finsupp.sum_add]
    refine Finsupp.sum_congr fun σ _ => Finsupp.sum_add_index' (fun _ => by simp) fun τ x y => ?_
    simp only [map_add, mul_add, add_mul, add_smul]
  right_distrib a b d := by
    simp only [mul_def, map_add]
    refine Finsupp.sum_add_index' (fun _ => by simp) fun σ x y => ?_
    simp only [add_mul, add_smul, Finsupp.sum_add]

instance : NonUnitalRing (GaloisCrossedProduct c) where
  mul_assoc a b d := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a a' ha ha' => simp only [add_mul, ha, ha']
    | smul_basis σ x =>
    induction b using induction_on with
    | zero => simp only [zero_mul, mul_zero]
    | add b b' hb hb' => simp only [add_mul, mul_add, hb, hb']
    | smul_basis τ y =>
    induction d using induction_on with
    | zero => simp only [mul_zero]
    | add d d' hd hd' => simp only [mul_add, hd, hd']
    | smul_basis ρ z =>
      have h := congrArg Units.val (c.cocycle σ τ ρ)
      change (c.value σ τ : E) * (c.value (σ * τ) ρ : E) =
        σ (c.value τ ρ) * (c.value σ (τ * ρ) : E) at h
      simp only [smul_basis_mul_smul_basis, map_mul, AlgEquiv.mul_apply, mul_assoc]
      congr 1
      linear_combination (x * σ y * σ (τ z)) * h

instance : NonAssocRing (GaloisCrossedProduct c) where
  one_mul a := by
    induction a using induction_on with
    | zero => simp only [mul_zero]
    | add a b ha hb => simp only [mul_add, ha, hb]
    | smul_basis σ x =>
      rw [← basis_one, ← one_smul E (basis c 1)]
      simp only [smul_basis_mul_smul_basis, GaloisTwoCocycle.one_left,
        GaloisTwoCocycle.one_right, Units.val_one, AlgEquiv.one_apply, map_one, one_mul, mul_one]
  mul_one a := by
    induction a using induction_on with
    | zero => simp only [zero_mul]
    | add a b ha hb => simp only [add_mul, ha, hb]
    | smul_basis σ x =>
      rw [← basis_one, ← one_smul E (basis c 1)]
      simp only [smul_basis_mul_smul_basis, GaloisTwoCocycle.one_left,
        GaloisTwoCocycle.one_right, Units.val_one, AlgEquiv.one_apply, map_one, one_mul, mul_one]

instance : Ring (GaloisCrossedProduct c) where
  __ := (inferInstance : NonUnitalRing (GaloisCrossedProduct c))
  __ := (inferInstance : NonAssocRing (GaloisCrossedProduct c))

instance : IsScalarTower E (GaloisCrossedProduct c) (GaloisCrossedProduct c) where
  smul_assoc x a b := by
    simp only [smul_eq_mul]
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [smul_add, add_mul, ha, ha']
    | smul_basis σ y =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, smul_add, hb, hb']
    | smul_basis τ z => simp only [smul_smul, smul_basis_mul_smul_basis, mul_assoc]

instance : SMulCommClass F (GaloisCrossedProduct c) (GaloisCrossedProduct c) where
  smul_comm r a b := by
    simp only [smul_eq_mul]
    induction a using induction_on with
    | zero => simp
    | add a a' ha ha' => simp only [add_mul, smul_add, ha, ha']
    | smul_basis σ y =>
    induction b using induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [mul_add, smul_add, hb, hb']
    | smul_basis τ z =>
      simp only [← algebraMap_smul (A := E) r, smul_smul, smul_basis_mul_smul_basis, map_mul,
        AlgEquiv.commutes]
      ring_nf

instance : Algebra F (GaloisCrossedProduct c) :=
  Algebra.ofModule
    (fun r a b => by rw [← algebraMap_smul E r a, smul_mul_assoc, algebraMap_smul])
    fun r a b => mul_smul_comm r a b

variable (c) in
/-- The embedding of the coefficient field, `x ↦ x u_1`. -/
def inc : E →ₐ[F] GaloisCrossedProduct c where
  toFun x := x • basis c 1
  map_one' := by rw [one_smul, basis_one]
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp [add_smul]
  commutes' r := by
    rw [algebraMap_smul, basis_one, Algebra.algebraMap_eq_smul_one]

theorem inc_apply (x : E) : inc c x = x • basis c 1 := rfl

/-- Left scalar multiplication by `E` agrees with multiplication by the coefficient subfield. -/
theorem smul_def (x : E) (a : GaloisCrossedProduct c) : x • a = inc c x * a := by
  rw [inc_apply, smul_mul_assoc, basis_one, one_mul]

/-- The semilinearity rule for the basis elements. -/
@[simp] theorem basis_mul_inc (σ : E ≃ₐ[F] E) (x : E) :
    basis c σ * inc c x = inc c (σ x) * basis c σ := by
  rw [← smul_def, inc_apply, ← one_smul E (basis c σ), smul_basis_mul_smul_basis]
  simp

/-- The cocycle rule for the basis elements. -/
theorem basis_mul_basis (σ τ : E ≃ₐ[F] E) :
    basis c σ * basis c τ = inc c (c.value σ τ) * basis c (σ * τ) := by
  rw [← smul_def]
  simpa only [one_smul, map_one, one_mul, smul_basis_mul_smul_basis] using
    (smul_basis_mul_smul_basis (c := c) σ τ 1 1)

/-- The coefficient formula for right multiplication by the coefficient subfield. -/
@[simp] theorem repr_mul_inc (a : GaloisCrossedProduct c) (x : E) (σ : E ≃ₐ[F] E) :
    (basis c).repr (a * inc c x) σ = (basis c).repr a σ * σ x := by
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp only [add_mul, map_add, Finsupp.add_apply, ha, hb]
  | smul_basis τ y =>
    rw [smul_mul_assoc, basis_mul_inc, ← smul_def, smul_smul]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
    by_cases h : τ = σ
    · subst h
      ring
    · simp [h]

instance : Nontrivial (GaloisCrossedProduct c) := (coordinates c).nontrivial

/-- A nonzero element of a two-sided ideal gives a nonzero single term in that ideal. -/
private theorem exists_smul_basis_mem (I : TwoSidedIdeal (GaloisCrossedProduct c)) (n : ℕ) :
    ∀ a ∈ I, a ≠ 0 → ((basis c).repr a).support.card ≤ n →
      ∃ (σ : E ≃ₐ[F] E) (y : E), y ≠ 0 ∧ y • basis c σ ∈ I := by
  induction n with
  | zero =>
    intro a _ ha hcard
    simp_all
  | succ n ih =>
    classical
    intro a haI ha hcard
    have hpos : 0 < ((basis c).repr a).support.card :=
      Finset.card_pos.mpr (Finsupp.support_nonempty_iff.mpr
        (fun h => ha ((basis c).repr.injective (h.trans (map_zero _).symm))))
    rcases (Nat.succ_le_of_lt hpos).eq_or_lt with h1 | h1
    · obtain ⟨σ, y, hy, hσ⟩ := Finsupp.card_support_eq_one'.mp h1.symm
      refine ⟨σ, y, hy, ?_⟩
      rwa [← (basis c).repr_symm_single, ← hσ, LinearEquiv.symm_apply_apply]
    · obtain ⟨σ, hσ, ρ, hρ, hne⟩ := Finset.one_lt_card.mp h1
      obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hne
      let b := a * inc c x - inc c (ρ x) * a
      have hb (τ : E ≃ₐ[F] E) :
          (basis c).repr b τ = (basis c).repr a τ * (τ x - ρ x) := by
        dsimp only [b]
        rw [← smul_def, map_sub, Finsupp.sub_apply, repr_mul_inc, map_smul, Finsupp.smul_apply,
          smul_eq_mul]
        ring
      have hbI : b ∈ I := I.sub_mem (I.mul_mem_right _ _ haI) (I.mul_mem_left _ _ haI)
      have hbne : b ≠ 0 := by
        intro h0
        have h := hb σ
        rw [h0, map_zero, Finsupp.zero_apply] at h
        exact mul_ne_zero (Finsupp.mem_support_iff.mp hσ) (sub_ne_zero.mpr hx) h.symm
      refine ih b hbI hbne ?_
      have hsub : ((basis c).repr b).support ⊆ ((basis c).repr a).support.erase ρ := by
        intro τ hτ
        rw [Finsupp.mem_support_iff, hb] at hτ
        refine Finset.mem_erase.mpr ⟨?_, Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hτ)⟩
        rintro rfl
        simp at hτ
      have h := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hρ] at h
      omega

/-- A nonzero two-sided ideal contains a nonzero element of the coefficient field. -/
theorem exists_ne_zero_and_inc_mem (c : GaloisTwoCocycle F E)
    {I : TwoSidedIdeal (GaloisCrossedProduct c)} (hI : I ≠ ⊥) :
    ∃ y : E, y ≠ 0 ∧ inc c y ∈ I := by
  have hLt : (⊥ : TwoSidedIdeal (GaloisCrossedProduct c)) < I := bot_lt_iff_ne_bot.mpr hI
  obtain ⟨a, haI, ha⟩ := SetLike.exists_of_lt hLt
  obtain ⟨σ, y, hy, hmem⟩ := exists_smul_basis_mem I _ a haI
    (fun h => ha ((TwoSidedIdeal.mem_bot (R := GaloisCrossedProduct c) (x := a)).mpr h)) le_rfl
  refine ⟨y * c.value σ σ⁻¹, mul_ne_zero hy (c.value σ σ⁻¹).ne_zero, ?_⟩
  simpa only [smul_def, mul_assoc, basis_mul_basis, mul_inv_cancel, basis_one, mul_one, ← map_mul]
    using I.mul_mem_right _ (basis c σ⁻¹) hmem

instance : IsSimpleRing (GaloisCrossedProduct c) :=
  IsSimpleRing.of_eq_bot_or_eq_top fun I => or_iff_not_imp_left.mpr fun hI => by
    obtain ⟨y, hy, hmem⟩ := exists_ne_zero_and_inc_mem c hI
    apply I.one_mem_iff.mp
    simpa [← map_mul, hy] using I.mul_mem_left (inc c y⁻¹) _ hmem

instance [IsGalois F E] : Algebra.IsCentral F (GaloisCrossedProduct c) where
  out := by
    intro a ha
    rw [Subalgebra.mem_center_iff] at ha
    have hOff (σ : E ≃ₐ[F] E) (hσ : σ ≠ 1) : (basis c).repr a σ = 0 := by
      obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hσ
      rw [AlgEquiv.one_apply] at hx
      have h := congrArg (fun b => (basis c).repr b σ) (ha (inc c x))
      simp only [← smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, repr_mul_inc] at h
      exact (mul_eq_zero.mp (by linear_combination h)).resolve_right (sub_ne_zero.mpr hx.symm)
    let y := (basis c).repr a 1
    have hCoeff : a = inc c y := by
      apply (basis c).repr.injective
      ext σ
      rw [inc_apply, map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
      by_cases hσ : σ = 1
      · simp [hσ, y]
      · simp [hOff σ hσ, Ne.symm hσ]
    have hFix (τ : E ≃ₐ[F] E) : τ y = y := by
      have h := ha (basis c τ)
      rw [hCoeff, basis_mul_inc, ← smul_def, ← smul_def] at h
      simpa only [map_smul, Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_eq_same, mul_one] using congrArg (fun b => (basis c).repr b τ) h
    have hMem : y ∈ IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) :=
      (IntermediateField.mem_fixedField_iff _ _).mpr (fun τ _ => hFix τ)
    rw [InfiniteGalois.fixedField_bot] at hMem
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hMem
    exact ⟨r, ((inc c).commutes r).symm.trans ((congrArg (inc c) hr).trans hCoeff.symm)⟩

instance [FiniteDimensional F E] : FiniteDimensional F (GaloisCrossedProduct c) :=
  Module.Finite.of_surjective ((coordinates c).linearEquiv F).symm.toLinearMap
    ((coordinates c).linearEquiv F).symm.surjective

theorem finrank_eq [FiniteDimensional F E] [IsGalois F E] :
    Module.finrank F (GaloisCrossedProduct c) = Module.finrank F E * Module.finrank F E := by
  rw [((coordinates c).linearEquiv F).finrank_eq, Module.finrank_finsupp,
    IsGalois.card_aut_eq_finrank]

end GaloisCrossedProduct

namespace GaloisTwoCocycle

open GaloisCrossedProduct

/-- A representation of the crossed product on a vector space of dimension
`[E : F]` gives a coboundary. The orbit of any nonzero vector under the
coefficient field identifies the space with `E`. -/
theorem isCoboundary_of_algHom_end [FiniteDimensional F E]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : GaloisCrossedProduct c →ₐ[F] Module.End F V)
    (hV : Module.finrank F V = Module.finrank F E) : c.IsCoboundary := by
  classical
  have hpos : 0 < Module.finrank F V := hV ▸ Module.finrank_pos
  letI : FiniteDimensional F V := Module.finite_of_finrank_pos hpos
  letI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let φ : E →ₗ[F] V := (LinearMap.applyₗ v).comp (ρ.comp (inc c)).toLinearMap
  have hφ (x : E) : φ x = ρ (inc c x) v := rfl
  have hρ (a b : GaloisCrossedProduct c) (w : V) :
      ρ (a * b) w = ρ a (ρ b w) := by simp
  have hOrbit (x y : E) : ρ (inc c x) (φ y) = φ (x * y) := by simp [hφ]
  have hInj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).mpr fun x hx => ?_
    by_contra hxne
    apply hv
    simpa [hx, hxne, hφ] using (hOrbit x⁻¹ x).symm
  have hSurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hV.symm).mp hInj
  choose b₀ hb₀ using fun σ : E ≃ₐ[F] E => hSurj (ρ (basis c σ) v)
  have hSemi (σ : E ≃ₐ[F] E) (x : E) :
      ρ (basis c σ) (φ x) = φ (σ x * b₀ σ) := by
    rw [hφ x, ← hρ, basis_mul_inc, hρ, ← hb₀, hOrbit]
  have hb₀ne (σ : E ≃ₐ[F] E) : b₀ σ ≠ 0 := by
    intro hZero
    have h : ρ (basis c σ⁻¹ * basis c σ) v = 0 := by
      rw [hρ, ← hb₀, hZero, map_zero, map_zero]
    rw [basis_mul_basis, inv_mul_cancel, basis_one, mul_one, ← hφ, ← map_zero φ] at h
    exact (c.value σ⁻¹ σ).ne_zero (hInj h)
  refine ⟨fun σ => Units.mk0 (b₀ σ) (hb₀ne σ), fun σ τ => ?_⟩
  have hEq : (c.value σ τ : E) * b₀ (σ * τ) = σ (b₀ τ) * b₀ σ := by
    apply hInj
    rw [← hOrbit, hb₀, ← hρ, ← basis_mul_basis, hρ, ← hb₀, hSemi]
  rw [eq_div_iff_mul_eq']
  apply Units.ext
  change (c.value σ τ : E) * b₀ (σ * τ) = b₀ σ * σ (b₀ τ)
  exact hEq.trans (mul_comm _ _)

/-- The relative multiplicative second Galois cohomology is trivial over a
characteristic-zero C₁ field. -/
theorem isCoboundary_of_isC1 [CharZero F] [FiniteDimensional F E] [IsGalois F E]
    (hF : IsC1 F) : c.IsCoboundary := by
  obtain ⟨m, _, ⟨e⟩⟩ := centralSimple_splits_of_isC1 F (GaloisCrossedProduct c) hF
  have h := e.toLinearEquiv.finrank_eq
  rw [GaloisCrossedProduct.finrank_eq (c := c), Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  have hm : m = Module.finrank F E := Nat.mul_self_inj.mp h.symm
  let ρ : GaloisCrossedProduct c →ₐ[F] Module.End F (Fin m → F) :=
    Matrix.toLinAlgEquiv'.toAlgHom.comp e.toAlgHom
  exact c.isCoboundary_of_algHom_end ρ ((Module.finrank_fin_fun (R := F) (n := m)).trans hm)

end GaloisTwoCocycle

end WideE
