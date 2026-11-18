import WideE.HopfKostantNormalizer
import WideE.PrincipalWeights

/-! A regular Cartan element absorbs a positive-weight perturbation by actual group conjugation. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule
open scoped Matrix TensorProduct

namespace WideE

section Filtration

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [FiniteDimensional k L] [LieAlgebra ℚ L] [IsScalarTower ℚ k L]

local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

omit [CharZero k] [FiniteDimensional k L] [LieAlgebra ℚ L] [IsScalarTower ℚ k L] in
private theorem lie_weight_filtration_succ (h : L) (r : ℕ) (u : W h (r + 1))
    (x : L) (hx : x ∈ B h (r + 1)) : ⁅(u : L), x⁆ ∈ B h (r + 2) := by
  refine Submodule.iSup_induction (motive := fun x => ⁅(u : L), x⁆ ∈ B h (r + 2))
    (fun i : {i : ℕ // r + 1 ≤ i} => W h i.val) hx ?_ ?_ ?_
  · intro i y hy
    refine negativeEvenWeightSpace_le_filtration h (i := r + 1 + i.val) ?_
      (lie_mem_negativeEvenWeightSpace h u.property hy)
    have := i.property
    omega
  · change ⁅(u : L), (0 : L)⁆ ∈ B h (r + 2)
    rw [lie_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [lie_add]
    exact add_mem ha hb

/-- If adjoint action by the fixed term is surjective on each nonzero grade,
finite adjoint exponentials eliminate the higher terms completely. -/
theorem exists_adjointExponentials_eliminate_negative (h z : L)
    (hSurj : ∀ (r : ℕ) (y : W h (r + 1)), ∃ u : W h (r + 1), ⁅z, u.val⁆ = y.val)
    (x : B h 1) :
    ∃ l : List (NilpotentAdjoint k L), (∀ u ∈ l, ∃ r : ℕ, u.val ∈ W h (r + 1)) ∧
      applyAdjointExponentials l (z + x.val) = z := by
  have hStage (r : ℕ) : ∃ (l : List (NilpotentAdjoint k L)) (v : B h (r + 1)),
      (∀ u ∈ l, ∃ n : ℕ, u.val ∈ W h (n + 1)) ∧
      applyAdjointExponentials l (z + x.val) = z + v.val := by
    induction r with
    | zero => exact ⟨[], x, by simp, rfl⟩
    | succ r ih =>
      obtain ⟨l, v, hl, hv⟩ := ih
      have hvEq := congrArg (fun S : Submodule k L => (v : L) ∈ S)
        (negativeEvenWeightSpace_sup_filtration_succ h (r + 1))
      have hvMem := hvEq.mpr v.property
      obtain ⟨y, hy, w, hw, hSum⟩ := Submodule.mem_sup.mp hvMem
      obtain ⟨u, hu⟩ := hSurj r ⟨y, hy⟩
      have hBracket : ⁅(u : L), z⁆ = -y := (lie_skew (u : L) z).symm.trans (congrArg Neg.neg hu)
      have hB : ⁅(u : L), z⁆ ∈ B h (r + 1) := hBracket ▸
        (B h (r + 1)).neg_mem (negativeEvenWeightSpace_le_filtration h le_rfl hy)
      let vU : NilpotentAdjoint k L := ⟨u, isNilpotent_leftAdjoint_of_weight_succ h r u⟩
      let P := LieDerivation.exp (leftAdjointDerivation k vU.val) vU.property
      have hRem := leftAdjointExp_sub_linear_mem (B h (r + 1)) (B h (r + 2))
        (kostantWeightFiltration_antitone h (Nat.le_succ _)) u.val z v.val v.property hB
        (lie_weight_filtration_succ h r u) vU.property
      have hEq : z + v.val + ⁅(u : L), z⁆ = z + w := by
        rw [hBracket, ← hSum]
        abel
      rw [hEq] at hRem
      have hRem' : P (z + v.val) - z ∈ B h (r + 2) := by
        have h := (B h (r + 2)).add_mem hRem hw
        convert h using 1
        change P (z + v.val) - z = P (z + v.val) - (z + w) + w
        abel
      refine ⟨l ++ [vU], ⟨P (z + v.val) - z, hRem'⟩, ?_, ?_⟩
      · intro u' hu'
        rcases List.mem_append.mp hu' with h | hvU
        · exact hl u' h
        · rw [List.mem_singleton] at hvU
          exact ⟨r, hvU.symm ▸ u.property⟩
      · rw [applyAdjointExponentials_append_singleton, hv]
        change P (z + v.val) = z + (P (z + v.val) - z)
        abel
  obtain ⟨N, hN⟩ := exists_kostantWeightFiltration_eq_bot (k := k) h
  obtain ⟨l, v, hl, hv⟩ := hStage N
  have hv0 : v.val = 0 := (Submodule.mem_bot k).mp
    (hN ▸ kostantWeightFiltration_antitone h (Nat.le_succ N) v.property)
  exact ⟨l, hl, by rwa [hv0, add_zero] at hv⟩

end Filtration

section CartanAction

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra.IsKilling k L] [FiniteDimensional k L]
  {H : LieSubalgebra k L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable k H L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem H
local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

private theorem lie_cartan_eq_zero_of_mem (z : H) {x : L} (hx : x ∈ H) : ⁅(z : L), x⁆ = 0 := by
  have hx' : x ∈ rootSpace H 0 := by rw [rootSpace_zero_eq]; exact hx
  simpa using lie_eq_smul_of_mem_rootSpace hx' z

/-- A Cartan element on which every root is nonzero has exactly the Cartan
subalgebra as its Lie centralizer. -/
theorem lie_regularCartan_eq_zero_iff_mem (z : H) (hz : ∀ α : H.root, (Φ).root α z ≠ 0)
    (x : L) : ⁅(z : L), x⁆ = 0 ↔ x ∈ H := by
  classical
  let D : Module.End k L := LieModule.toEnd k L L (z : L)
  let S := ⨆ c : {c : k // c ≠ 0}, D.eigenspace c.val
  have hCartan : H.toSubmodule ≤ D.eigenspace 0 := by
    intro y hy
    exact Module.End.mem_eigenspace_iff.mpr (by simpa using lie_cartan_eq_zero_of_mem z hy)
  have hCover : H.toSubmodule ⊔ S = ⊤ := by
    apply eq_top_iff.mpr
    rw [← LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top k H L)]
    apply iSup_le
    intro α
    by_cases hα : α = 0
    · subst α
      rw [show genWeightSpace L (0 : H → k) = H.toLieSubmodule from rootSpace_zero_eq k L H]
      exact le_sup_left
    · by_cases hSpace : rootSpace H α = ⊥
      · change (rootSpace H α).toSubmodule ≤ _
        rw [hSpace, LieSubmodule.bot_toSubmodule]
        exact bot_le
      · let r : H.root := ⟨⟨α, hSpace⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩
        have hr : α z ≠ 0 := hz r
        intro y hy
        have hyE : y ∈ D.eigenspace (α z) :=
          Module.End.mem_eigenspace_iff.mpr (lie_eq_smul_of_mem_rootSpace hy z)
        exact (show S ≤ H.toSubmodule ⊔ S from le_sup_right) ((le_iSup (fun c : {c : k // c ≠ 0} => D.eigenspace c.val)
          ⟨α z, hr⟩) hyE)
  have hDisj : Disjoint (D.eigenspace 0) S := by
    refine (iSupIndep_def.mp D.eigenspaces_iSupIndep 0).mono_right ?_
    apply iSup_le
    intro c
    exact le_iSup₂ (f := fun c (_ : c ≠ (0 : k)) => D.eigenspace c) c.val c.property
  refine ⟨fun hx => ?_, lie_cartan_eq_zero_of_mem z⟩
  have hxE : x ∈ D.eigenspace 0 := Module.End.mem_eigenspace_iff.mpr (by simpa using hx)
  have hxH : x ∈ H.toSubmodule ⊔ S := by rw [hCover]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hxH
  have hvE : v ∈ D.eigenspace 0 := by
    simpa using (D.eigenspace 0).sub_mem hxE (hCartan hu)
  have hZero := Submodule.disjoint_def.mp hDisj v hvE hv
  simpa [hZero] using hu

/-- On each positive principal weight, a regular Cartan element acts invertibly. -/
theorem exists_regularCartan_lie_eq_of_positiveWeight (b : (Φ).Base) (z : H)
    (hz : ∀ α : H.root, (Φ).root α z ≠ 0) (r : ℕ)
    (y : W (-(principalCartanElement b : L)) (r + 1)) :
    ∃ u : W (-(principalCartanElement b : L)) (r + 1), ⁅(z : L), u.val⁆ = y.val := by
  let h : L := -(principalCartanElement b : L)
  let c : k := ((-(2 : ℤ) * ((r + 1 : ℕ) : ℤ) : ℤ) : k)
  let S := W h (r + 1)
  have hh : ⁅h, (z : L)⁆ = 0 := by
    simp only [h, neg_lie, lie_cartan_eq_zero_of_mem (principalCartanElement b) z.property, neg_zero]
  let D : S →ₗ[k] S := (LieModule.toEnd k L L (z : L)).restrict fun x hx => by
    apply Module.End.mem_eigenspace_iff.mpr
    have hx' : ⁅h, x⁆ = c • x := Module.End.mem_eigenspace_iff.mp hx
    change ⁅h, ⁅(z : L), x⁆⁆ = c • ⁅(z : L), x⁆
    rw [leibniz_lie, hh, zero_lie, zero_add, hx', lie_smul]
  have hInj : Function.Injective D := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    have hxt : ⁅(z : L), (x : L)⁆ = 0 := congrArg Subtype.val hx
    have hxH := (lie_regularCartan_eq_zero_iff_mem z hz x.val).mp hxt
    have hx0 : ⁅h, (x : L)⁆ = 0 := by
      simp only [h, neg_lie, lie_cartan_eq_zero_of_mem (principalCartanElement b) hxH, neg_zero]
    have hxWeight : ⁅h, (x : L)⁆ = c • (x : L) := Module.End.mem_eigenspace_iff.mp x.property
    have hc : c ≠ 0 := Int.cast_ne_zero.mpr (by omega)
    rw [hx0] at hxWeight
    exact (smul_eq_zero.mp hxWeight.symm).resolve_left hc
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hInj y
  exact ⟨u, congrArg Subtype.val hu⟩

end CartanAction

section GroupConjugation

variable {k L A ι : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ k L] [LieAlgebra.IsKilling k L] [FiniteDimensional k L]
  [CommRing A] [HopfAlgebra k A] [Fintype ι] [DecidableEq ι]
  {H : LieSubalgebra k L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable k H L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem H
local notation "𝔤" => hopfInvariantDerivations k A
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := A)
local notation "W" => negativeEvenWeightSpace (k := k)
local notation "B" => kostantWeightFiltration (k := k)

/-- The sum of a regular Cartan element and the principal positive root sum is conjugate
to the Cartan element by an actual Hopf group point. -/
theorem exists_hopfPoint_principalCartan_conjugation (U : (Matrix ι ι A)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (b : (Φ).Base) [Fintype b.support] (e : b.support → L)
    (heRoot : ∀ i : b.support, e i ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k))
    (z : H) (hz : ∀ α : H.root, (Φ).root α z ≠ 0) :
    ∃ p : A →ₐ[k] k,
      hopfAdjoint p ((J).symm (j ((∑ r, e r) + (z : L)))) = (J).symm (j (z : L)) := by
  let h : L := -(principalCartanElement b : L)
  have hW (i : b.support) : e i ∈ W h 1 := by
    apply Module.End.mem_eigenspace_iff.mpr
    have hw := lie_eq_smul_of_mem_rootSpace (heRoot i) (principalCartanElement b)
    change ⁅(principalCartanElement b : L), e i⁆ = (Φ).root i (principalCartanElement b) • e i at hw
    change ⁅h, e i⁆ = ((-(2 : ℤ) * (1 : ℤ) : ℤ) : k) • e i
    rw [principalCartanElement_simpleRoot] at hw
    simp only [h, neg_lie, hw, mul_one, Int.cast_neg, Int.cast_ofNat, neg_smul]
  let x : B h 1 := ⟨∑ r, e r, (B h 1).sum_mem fun i _ =>
    negativeEvenWeightSpace_le_filtration h le_rfl (hW i)⟩
  obtain ⟨l, hl, hExp⟩ := exists_adjointExponentials_eliminate_negative h (z : L)
    (exists_regularCartan_lie_eq_of_positiveWeight b z hz) x
  let ρ := (hopfLieMatrixHom U.val hD).comp j
  have hNil (u : NilpotentAdjoint k L) (hu : u ∈ l) :
      IsNilpotent (hopfLieMatrix U.val (j u.val)) := by
    obtain ⟨r, hr⟩ := hl u hu
    have hMat := lieHom_mem_negativeEvenWeightSpace ρ h hr
    exact isNilpotent_of_mem_kostantWeightFiltration (ρ h) (Nat.zero_lt_succ r)
      (negativeEvenWeightSpace_le_filtration (ρ h) le_rfl hMat)
  obtain ⟨p, hp⟩ := exists_hopfPoint_applyAdjointExponentials U hD he hGen j l hNil
  refine ⟨p, ?_⟩
  change hopfAdjoint p ((J).symm (j (x.val + (z : L)))) = (J).symm (j (z : L))
  rw [add_comm x.val, hp, hExp]

end GroupConjugation

end WideE
