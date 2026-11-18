import WideE.FlagStabilizer
import WideE.ProjectiveLineReduction

/-! The Hopf algebra of the stabilizer of a line in a matrix representation. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

variable {k H A ι : Type*} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommRing A] [Algebra k A] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Scalar evaluation sends the universal orbit vector to the evaluated matrix action. -/
theorem orbitVector_map (f : H →ₐ[k] A) (M : Matrix ι ι H) (v : ι → k) :
    f.toRingHom ∘ orbitVector M v = M.map f *ᵥ (algebraMap k A ∘ v) := by
  funext i
  have h := RingHom.map_mulVec f.toRingHom M (algebraMap k H ∘ v) i
  rw [show f.toRingHom ∘ (algebraMap k H ∘ v) = algebraMap k A ∘ v from
    funext fun j => f.commutes (v j)] at h
  exact h

variable (U : (Matrix ι ι H)ˣ) (v : ι → k) (i : ι)

/-- The equations requiring the universal orbit vector to lie on the original line. -/
abbrev projectiveLineStabilizerIdeal : Ideal H := projectiveLineIdeal v i (orbitVector U.val v)

local notation "J" => (projectiveLineStabilizerIdeal U v i)
local notation "Q" => H ⧸ J
local notation "π" => (Ideal.Quotient.mkₐ k J)
local notation "Δ" => (Bialgebra.comulAlgHom k H)
local notation "ε" => (Bialgebra.counitAlgHom k H)
local notation "l" => (Algebra.TensorProduct.includeLeft : Q →ₐ[k] Q ⊗[k] Q)
local notation "r" => (Algebra.TensorProduct.includeRight : Q →ₐ[k] Q ⊗[k] Q)

private theorem orbitVector_primitive (hi : v i ≠ 0) : Ideal.span (Set.range (orbitVector U.val v)) = ⊤ := by
  rw [orbitVector, ideal_span_range_mulVec_unit]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_range_self i))
    ((isUnit_iff_ne_zero.mpr hi).map (algebraMap k H))

theorem projectiveLineStabilizer_scale (hi : v i ≠ 0) :
    ∃ c : Qˣ, (U.val.map π) *ᵥ (algebraMap k Q ∘ v) = (c : Q) • (algebraMap k Q ∘ v) := by
  obtain ⟨c, hc⟩ := projectiveLineQuotient_unit_vector (R := k) v i (orbitVector U.val v)
    (orbitVector_primitive U v i hi)
  rw [orbitVector_map] at hc
  exact ⟨c, hc⟩

omit [DecidableEq ι] in
/-- A coefficient map carries a line and its scaling relation to the same line over the target. -/
theorem lineScale_map {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (M : Matrix ι ι A) (c : A)
    (h : M *ᵥ (algebraMap k A ∘ v) = c • (algebraMap k A ∘ v)) :
    (M.map f) *ᵥ (algebraMap k B ∘ v) = f c • (algebraMap k B ∘ v) := by
  funext j
  have hMap := RingHom.map_mulVec f.toRingHom M (algebraMap k A ∘ v) j
  change f ((M *ᵥ (algebraMap k A ∘ v)) j) = _ at hMap
  rw [h, show f.toRingHom ∘ (algebraMap k A ∘ v) = algebraMap k B ∘ v from
    funext fun a => f.commutes (v a)] at hMap
  simpa only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, map_mul, AlgHom.commutes] using hMap.symm

/-- Preservation of a line gives a closed subgroup, over arbitrary coefficient algebras. -/
theorem projectiveLineStabilizerIdeal_isHopf (hi : v i ≠ 0)
    (hD : ∀ a b, Coalgebra.comul (R := k) (U.val a b) = ∑ j, U.val a j ⊗ₜ[k] U.val j b)
    (he : ∀ a b, Coalgebra.counit (R := k) (U.val a b) = if a = b then 1 else 0) :
    IsHopfIdeal k J := by
  obtain ⟨c, hc⟩ := projectiveLineStabilizer_scale U v i hi
  constructor
  · let f := (Algebra.TensorProduct.map π π).comp Δ
    have hM : U.val.map f = U.val.map ((l).comp π) * U.val.map ((r).comp π) := by
      ext a b
      change Algebra.TensorProduct.map π π (Coalgebra.comul (R := k) (U.val a b)) =
        ∑ j, (π (U.val a j) ⊗ₜ[k] (1 : Q)) * ((1 : Q) ⊗ₜ[k] π (U.val j b))
      rw [hD, map_sum]
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have hL : U.val.map ((l).comp π) *ᵥ (algebraMap k (Q ⊗[k] Q) ∘ v) =
        l (c : Q) • (algebraMap k (Q ⊗[k] Q) ∘ v) := lineScale_map v l _ _ hc
    have hR : U.val.map ((r).comp π) *ᵥ (algebraMap k (Q ⊗[k] Q) ∘ v) =
        r (c : Q) • (algebraMap k (Q ⊗[k] Q) ∘ v) := lineScale_map v r _ _ hc
    apply projectiveLineIdeal_le_ker (R := k) v i hi _ f (r (c : Q) * l (c : Q))
    rw [orbitVector_map, hM, ← Matrix.mulVec_mulVec, hR, Matrix.mulVec_smul, hL, smul_smul]
  · have hCounit : U.val.map ε = 1 := Matrix.ext fun a b => (he a b).trans Matrix.one_apply.symm
    apply projectiveLineIdeal_le_ker (R := k) v i hi _ ε (1 : k)
    rw [orbitVector_map, hCounit, Matrix.one_mulVec, one_smul]
  · let V : (Matrix ι ι Q)ˣ := U.map ((π).toRingHom.mapMatrix).toMonoidHom
    let f := (π).comp (hopfAntipodeAlgHom k H)
    have hInv : U.val.map f = V.inv := by
      ext a b
      change π (hopfAntipodeAlgHom k H (U.val a b)) = π (U.inv a b)
      rw [hopfAntipodeAlgHom_apply, hopfMatrix_inv_eq_map_antipode U hD he]
      rfl
    have h := congrArg (V.inv *ᵥ ·) hc
    change V.inv *ᵥ (V.val *ᵥ (algebraMap k Q ∘ v)) =
      V.inv *ᵥ ((c : Q) • (algebraMap k Q ∘ v)) at h
    rw [Matrix.mulVec_mulVec, V.inv_val, Matrix.one_mulVec, Matrix.mulVec_smul] at h
    apply projectiveLineIdeal_le_ker (R := k) v i hi _ f ((c⁻¹ : Qˣ) : Q)
    rw [orbitVector_map, hInv]
    symm
    calc
      ((c⁻¹ : Qˣ) : Q) • (algebraMap k Q ∘ v) =
          ((c⁻¹ : Qˣ) : Q) • ((c : Q) • (V.inv *ᵥ (algebraMap k Q ∘ v))) :=
        congrArg (((c⁻¹ : Qˣ) : Q) • ·) h
      _ = _ := by rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

end WideE
