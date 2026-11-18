import WideE.HopfPolynomialPower

/-! Uniqueness on the Kostant slice under strictly negative group transformations. -/

noncomputable section

open scoped Matrix TensorProduct

namespace WideE

section FiltrationShifts

variable {k L : Type*} [Field k] [LieRing L] [LieAlgebra k L]

local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

private theorem lie_right_positiveWeight_mem (h e : L) (he : ⁅h, e⁆ = (2 : k) • e)
    (r : ℕ) {x : L} (hx : x ∈ W h (r + 1)) : ⁅x, e⁆ ∈ W h r := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change ⁅h, x⁆ = _ at hx
  change ⁅h, ⁅x, e⁆⁆ = _
  rw [leibniz_lie, hx, he, smul_lie, lie_smul, ← add_smul]
  congr 1
  push_cast
  ring

private theorem lie_right_positiveFiltration_mem (h e : L) (he : ⁅h, e⁆ = (2 : k) • e)
    (r : ℕ) {x : L} (hx : x ∈ B h (r + 1)) : ⁅x, e⁆ ∈ B h r := by
  refine Submodule.iSup_induction (motive := fun x => ⁅x, e⁆ ∈ B h r)
    (fun i : {i : ℕ // r + 1 ≤ i} => W h i.val) hx ?_ ?_ ?_
  · intro i y hy
    have hi : 0 < i.val := Nat.zero_lt_of_lt (Nat.lt_of_succ_le i.property)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    have hr : r ≤ j := by have := i.property; omega
    change y ∈ W h i.val at hy
    rw [hj] at hy
    exact negativeEvenWeightSpace_le_filtration h hr (lie_right_positiveWeight_mem h e he j hy)
  · change ⁅(0 : L), e⁆ ∈ B h r
    rw [zero_lie]
    exact zero_mem _
  · intro a b ha hb
    rw [add_lie]
    exact add_mem ha hb

private theorem lie_left_negativeFiltration_mem (h f : L) (hf : f ∈ W h 1)
    (r : ℕ) {x : L} (hx : x ∈ B h r) : ⁅f, x⁆ ∈ B h (r + 1) := by
  refine Submodule.iSup_induction (motive := fun x => ⁅f, x⁆ ∈ B h (r + 1))
    (fun i : {i : ℕ // r ≤ i} => W h i.val) hx ?_ ?_ ?_
  · intro i y hy
    refine negativeEvenWeightSpace_le_filtration h (i := 1 + i.val) ?_
      (lie_mem_negativeEvenWeightSpace h hf hy)
    have := i.property
    omega
  · change ⁅f, (0 : L)⁆ ∈ B h (r + 1)
    rw [lie_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [lie_add]
    exact add_mem ha hb

private theorem exists_leading_negative_depth [CharZero k] [FiniteDimensional k L]
    (h : L) {x : L} (hx : x ∈ B h 1) (hne : x ≠ 0) :
    ∃ r : ℕ, x ∈ B h (r + 1) ∧ x ∉ B h (r + 2) := by
  classical
  obtain ⟨N, hN⟩ := exists_kostantWeightFiltration_eq_bot (k := k) h
  have hExit : ∃ n : ℕ, x ∉ B h n := ⟨N, fun hn => hne ((Submodule.mem_bot k).mp (hN ▸ hn))⟩
  let n := Nat.find hExit
  have hn : x ∉ B h n := Nat.find_spec hExit
  have h₀ : ¬n ≤ 1 := fun hle => hn (kostantWeightFiltration_antitone h hle hx)
  let r := n - 2
  have hSucc : r + 2 = n := by dsimp [r]; omega
  refine ⟨r, ?_, fun hv => hn (hSucc ▸ hv)⟩
  by_contra hr
  have hmin := Nat.find_min' hExit hr
  omega

end FiltrationShifts

section ActualUniqueness

variable {k H ι : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := H)
local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

/-- A negative transformation carrying one normalized representative to another
is the identity, and the two slice terms are equal. -/
theorem hopfPoint_eq_one_and_slice_eq_of_kostantAdjoint (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    {h e f : 𝔤} (t : IsSl2Triple h e f) (s s' : 𝔤)
    (hs : s ∈ B h 0) (hs' : s' ∈ B h 0) (hk : ⁅f, s⁆ = 0) (hk' : ⁅f, s'⁆ = 0)
    (p : H →ₐ[k] k) (hp : U.val.map p - 1 ∈ B (hopfLieMatrix U.val h) 1)
    (hAd : hopfAdjoint p ((J).symm (e + s)) = (J).symm (e + s')) :
    p = hopfPointOne ∧ s = s' := by
  classical
  let ρ := hopfLieMatrixHom U.val hD
  have hI : Function.Injective ρ := hopfLieMatrixHom_injective U.val hD hGen
  letI : FiniteDimensional k 𝔤 := FiniteDimensional.of_injective ρ.toLinearMap hI
  let P := hopfPointMatrix U hD he p
  let N := P.val - 1
  have hP : P.val = 1 + N := by dsimp [N]; abel
  have hEp : ⁅h, e⁆ = (2 : k) • e := t.lie_h_e_smul k
  have hEρ : ⁅ρ h, ρ e⁆ = (2 : k) • ρ e := by
    rw [← LieHom.map_lie, hEp, LieHom.map_smul]
  have hF : f ∈ W h 1 := by
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅h, f⁆ = ((-(2 : ℤ) * (1 : ℤ) : ℤ) : k) • f
    simpa only [mul_one, Int.cast_neg, Int.cast_ofNat, neg_smul] using t.lie_lie_smul_f k
  have hConj : ρ (e + s') = P.val * ρ (e + s) * P.inv := by
    have h := hopfCotangentMatrix_adjoint U hD he p ((J).symm (e + s))
    rw [hAd, ← hopfLieMatrix_invariantDerivations, ← hopfLieMatrix_invariantDerivations,
      (J).apply_symm_apply, (J).apply_symm_apply] at h
    exact h
  have hIntertwine : P.val * (ρ e + ρ s) = (ρ e + ρ s') * P.val := by
    have h := congrArg (fun a : Matrix ι ι k => a * P.val) hConj
    change ρ (e + s') * P.val = (P.val * ρ (e + s) * P.inv) * P.val at h
    rw [mul_assoc _ P.inv P.val, P.inv_val, mul_one] at h
    simpa only [LieHom.map_add] using h.symm
  have hNzero : N = 0 := by
    by_contra hNne
    obtain ⟨r, hNmem, hNout⟩ := exists_leading_negative_depth (ρ h) hp hNne
    change N ∈ B (ρ h) (r + 1) at hNmem
    change N ∉ B (ρ h) (r + 2) at hNout
    obtain ⟨v, hv⟩ := exists_hopfLieMatrix_leading_of_mem_kostantWeightFiltration
      U hD he hGen p (ρ h) (Nat.zero_lt_succ r) hNmem
    change ρ v - N ∈ B (ρ h) (r + 2) at hv
    have hvMat : ρ v ∈ B (ρ h) (r + 1) := by
      have hDiff := kostantWeightFiltration_antitone (ρ h) (Nat.le_succ (r + 1)) hv
      simpa only [sub_add_cancel] using (B (ρ h) (r + 1)).add_mem hDiff hNmem
    have hvMem : v ∈ B h (r + 1) := mem_kostantWeightFiltration_of_lieHom ρ hI h hvMat
    rw [← negativeEvenWeightSpace_sup_filtration_succ h (r + 1)] at hvMem
    obtain ⟨u, hu, w, hw, hvEq⟩ := Submodule.mem_sup.mp hvMem
    have hNlead : N - ρ u ∈ B (ρ h) (r + 2) := by
      have hDiff := (B (ρ h) (r + 2)).sub_mem (lieHom_mem_kostantWeightFiltration ρ h hw) hv
      rw [← hvEq, LieHom.map_add] at hDiff
      convert hDiff using 1
      abel
    have hDiff : ρ (s' - s) = ⁅N, ρ e⁆ + (N * ρ s - ρ s' * N) := by
      simp only [hP, add_mul, mul_add, one_mul, mul_one] at hIntertwine
      rw [LieHom.map_sub, LieRing.of_associative_ring_bracket]
      calc
        _ = ((ρ e + ρ s') + (ρ e * N + ρ s' * N)) - (ρ e + ρ s) -
              (ρ e * N + ρ s' * N) := by abel
        _ = _ := by rw [← hIntertwine]; abel
    have hRemMat : ρ (s' - s - ⁅u, e⁆) ∈ B (ρ h) (r + 1) := by
      have hFirst := lie_right_positiveFiltration_mem (ρ h) (ρ e) hEρ (r + 1) hNlead
      have hLeft : N * ρ s ∈ B (ρ h) (r + 1) := by
        simpa only [Nat.add_zero] using
          mul_mem_kostantWeightFiltration (ρ h) hNmem (lieHom_mem_kostantWeightFiltration ρ h hs)
      have hRight : ρ s' * N ∈ B (ρ h) (r + 1) := by
        simpa only [Nat.zero_add] using
          mul_mem_kostantWeightFiltration (ρ h) (lieHom_mem_kostantWeightFiltration ρ h hs') hNmem
      have hSum := (B (ρ h) (r + 1)).add_mem hFirst ((B (ρ h) (r + 1)).sub_mem hLeft hRight)
      rw [LieHom.map_sub, LieHom.map_lie, hDiff]
      rw [sub_lie] at hSum
      convert hSum using 1
      abel
    have hRem : s' - s - ⁅u, e⁆ ∈ B h (r + 1) :=
      mem_kostantWeightFiltration_of_lieHom ρ hI h hRemMat
    have hLow := lie_left_negativeFiltration_mem h f hF (r + 1) hRem
    rw [lie_sub, lie_sub, hk, hk', sub_zero, zero_sub] at hLow
    have hTe : ⁅u, e⁆ ∈ W h r := lie_right_positiveWeight_mem h e hEp r hu
    have hTw : ⁅f, ⁅u, e⁆⁆ ∈ W h (r + 1) := by
      simpa only [Nat.add_comm] using lie_mem_negativeEvenWeightSpace h hF hTe
    have hZero : ⁅f, ⁅u, e⁆⁆ = 0 := Submodule.disjoint_def.mp
      (negativeEvenWeightSpace_disjoint_filtration_succ h (r + 1)) _ hTw
      ((B h (r + 2)).neg_mem_iff.mp hLow)
    have hKernel : ⁅f, ⁅e, u⁆⁆ = 0 := by rw [← lie_skew e u, lie_neg, hZero, neg_zero]
    have huZero : u = 0 := sl2_raise_lower_kernel_of_negative_weight t
      (sl2_lower_isNilpotent (M := 𝔤) t) (-(2 : ℤ) * ((r + 1 : ℕ) : ℤ)) (by omega) u
      (Module.End.mem_eigenspace_iff.mp hu) hKernel
    exact hNout (by simpa only [huZero, LieHom.map_zero, sub_zero] using hNlead)
  have hMatrix : P.val = 1 := sub_eq_zero.mp hNzero
  refine ⟨?_, ?_⟩
  · apply AlgHom.ext_of_adjoin_eq_top hGen
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change (P.val) i j = Bialgebra.counitAlgHom k H (U.val i j)
    rw [hMatrix, Matrix.one_apply]
    exact (he i j).symm
  · have hInv : P.inv = 1 := by simpa only [hMatrix, one_mul] using P.val_inv
    rw [hMatrix, hInv, one_mul, mul_one] at hConj
    exact (add_left_cancel (hI hConj)).symm

end ActualUniqueness

end WideE
