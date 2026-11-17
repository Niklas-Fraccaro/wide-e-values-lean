import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.Ring

/-! Affine gluing along principal opens, as used to extend a Zariski-locally
trivial torsor from the punctured line to the affine line. -/

noncomputable section

namespace WideE

section Patch

variable {R B C E : Type*} [CommRing R] [CommRing B] [CommRing C] [CommRing E]
  [Algebra R B] [Algebra R C] [Algebra R E]

/-- The algebra of pairs that agree on the overlap. -/
def affinePatchAlgebra (f : B →ₐ[R] E) (g : C →ₐ[R] E) : Subalgebra R (B × C) where
  carrier := {x | f x.1 = g x.2}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change f x.1 = g x.2 at hx
    change f y.1 = g y.2 at hy
    change f (x.1 + y.1) = g (x.2 + y.2)
    simp only [map_add, hx, hy]
  mul_mem' := by
    intro x y hx hy
    change f x.1 = g x.2 at hx
    change f y.1 = g y.2 at hy
    change f (x.1 * y.1) = g (x.2 * y.2)
    simp only [map_mul, hx, hy]
  algebraMap_mem' a := by
    change f (algebraMap R B a) = g (algebraMap R C a)
    simp

abbrev AffinePatch (f : B →ₐ[R] E) (g : C →ₐ[R] E) := ↥(affinePatchAlgebra f g)

def affinePatchLeft (f : B →ₐ[R] E) (g : C →ₐ[R] E) : AffinePatch f g →ₐ[R] B where
  toFun x := x.val.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def affinePatchSwap (f : B →ₐ[R] E) (g : C →ₐ[R] E) : AffinePatch f g ≃ₐ[R] AffinePatch g f where
  toFun x := ⟨x.val.swap, x.property.symm⟩
  invFun x := ⟨x.val.swap, x.property.symm⟩
  left_inv _ := Subtype.ext (Prod.ext rfl rfl)
  right_inv _ := Subtype.ext (Prod.ext rfl rfl)
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

variable [Algebra C E] [IsScalarTower R C E]

local notation "overlap" => IsScalarTower.toAlgHom R C E

/-- Localizing the glued algebra at a base element already invertible in the
left piece recovers the left piece, provided the overlap is the corresponding
localization of the right piece. -/
theorem affinePatch_isLocalizationAtLeft (f : B →ₐ[R] E) (a : R)
    (hUnit : IsUnit (algebraMap R B a)) [IsLocalization.Away (algebraMap R C a) E] :
    letI := (affinePatchLeft f overlap).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (AffinePatch f overlap) a) B := by
  let G := AffinePatch f overlap
  letI := (affinePatchLeft f overlap).toRingHom.toAlgebra
  let t := algebraMap R G a
  constructor
  · rintro ⟨_, n, rfl⟩
    change IsUnit (affinePatchLeft f overlap (t ^ n))
    rw [map_pow]
    exact hUnit.pow n
  · intro b
    obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R C a)) (f b)
    obtain ⟨n, hn⟩ := s.property
    change (algebraMap R C a) ^ n = (s : C) at hn
    have hb : f (b * (algebraMap R B a) ^ n) = algebraMap C E c := by
      rw [map_mul, map_pow, AlgHom.commutes, IsScalarTower.algebraMap_apply R C E a, ← map_pow, hn]
      exact hs
    let x : G := ⟨(b * (algebraMap R B a) ^ n, c), hb⟩
    exact ⟨(x, ⟨t ^ n, ⟨n, rfl⟩⟩), rfl⟩
  · intro x y h
    have hLeft : x.val.1 = y.val.1 := h
    have hRight : algebraMap C E x.val.2 = algebraMap C E y.val.2 :=
      x.property.symm.trans ((congrArg f hLeft).trans y.property)
    obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R C a)) hRight
    obtain ⟨n, hn⟩ := s.property
    change (algebraMap R C a) ^ n = (s : C) at hn
    refine ⟨⟨t ^ n, ⟨n, rfl⟩⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · change (algebraMap R B a) ^ n * x.val.1 = (algebraMap R B a) ^ n * y.val.1
      rw [hLeft]
    · change (algebraMap R C a) ^ n * x.val.2 = (algebraMap R C a) ^ n * y.val.2
      rwa [hn]

omit [Algebra C E] [IsScalarTower R C E] in
/-- The same glued algebra localizes to the right piece. -/
theorem affinePatch_isLocalizationAtRight [Algebra B E] [IsScalarTower R B E]
    (g : C →ₐ[R] E) (a : R)
    (hUnit : IsUnit (algebraMap R C a)) [IsLocalization.Away (algebraMap R B a) E] :
    let f := IsScalarTower.toAlgHom R B E
    letI := ((affinePatchLeft g f).comp (affinePatchSwap f g).toAlgHom).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (AffinePatch f g) a) C := by
  let f := IsScalarTower.toAlgHom R B E
  let e := affinePatchSwap g f
  letI := (affinePatchLeft g f).toRingHom.toAlgebra
  letI : IsLocalization.Away (algebraMap R (AffinePatch g f) a) C :=
    affinePatch_isLocalizationAtLeft (B := C) (C := B) g a hUnit
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers (algebraMap R (AffinePatch g f) a)) C e.toRingEquiv
  have hMap : (Submonoid.powers (algebraMap R (AffinePatch g f) a)).map e.toRingEquiv =
      Submonoid.powers (algebraMap R (AffinePatch f g) a) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (e.commutes a)
  rw [hMap] at h
  exact h

end Patch

/-- The coordinate and any polynomial with nonzero value at the origin give
the two principal opens covering the affine line in the extension argument. -/
theorem polynomial_X_coprime_of_constant_nonzero {K : Type*} [Field K]
    (p : Polynomial K) (h₀ : p.coeff 0 ≠ 0) : IsCoprime Polynomial.X p := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  let c := Polynomial.C (p.coeff 0)⁻¹
  refine ⟨-(c * q), c, ?_⟩
  calc
    _ = c * (p - Polynomial.X * q) := by ring
    _ = c * Polynomial.C (p.coeff 0) := by rw [← hq, sub_sub_cancel]
    _ = 1 := by
      change Polynomial.C ((p.coeff 0)⁻¹) * Polynomial.C (p.coeff 0) = 1
      rw [← map_mul, inv_mul_cancel₀ h₀, map_one]

end WideE
