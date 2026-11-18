import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# A principal `sl₂` triple from a root-system base

The two bases of the split Cartan and its dual solve the Cartan equations.
The elementary root triples then combine by the vanishing of brackets
between positive and negative root vectors for distinct simple roots.
-/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule

namespace WideE

variable {k L : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [LieAlgebra.IsKilling k L] [FiniteDimensional k L]
variable {H : LieSubalgebra k L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable k H L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem H

/-- The Cartan element assigning value two to every simple root. -/
def principalCartanElement (b : (Φ).Base) : H :=
  (Module.evalEquiv k H).symm (b.toWeightBasis.constr k fun _ => (2 : k))

@[simp] theorem principalCartanElement_simpleRoot (b : (Φ).Base) (i : b.support) :
    (Φ).root i (principalCartanElement b) = 2 := by
  rw [principalCartanElement, Module.apply_evalEquiv_symm_apply]
  have h : b.toWeightBasis i = (Φ).root i := by
    rw [RootPairing.Base.toWeightBasis, Basis.mk_apply]
  rw [← h, Basis.constr_basis]

/-- Simple-coroot coordinates of the principal Cartan element. -/
def principalCartanCoefficient (b : (Φ).Base) (i : b.support) : k :=
  b.toCoweightBasis.repr (principalCartanElement b) i

@[simp] private theorem coweightBasis_eq_coroot (b : (Φ).Base) (i : b.support) :
    b.toCoweightBasis i = (Φ).coroot i := by
  rw [RootPairing.Base.toCoweightBasis, RootPairing.Base.toWeightBasis, Basis.mk_apply]
  rfl

/-- Expansion in the basis of simple coroots. -/
theorem sum_principalCartanCoefficient_coroot (b : (Φ).Base) [Fintype b.support] :
    ∑ i : b.support, principalCartanCoefficient b i • (Φ).coroot i = principalCartanElement b := by
  simpa only [principalCartanCoefficient, coweightBasis_eq_coroot] using
    b.toCoweightBasis.sum_repr (principalCartanElement b)

/-- The simple-coroot coefficients solve the Cartan equations with right hand side two. -/
theorem sum_principalCartanCoefficient_pairing (b : (Φ).Base) [Fintype b.support]
    (i : b.support) : ∑ j : b.support, (Φ).pairing i j * principalCartanCoefficient b j = 2 := by
  have h := congrArg ((Φ).root i : H →ₗ[k] k) (sum_principalCartanCoefficient_coroot b)
  rw [map_sum, principalCartanElement_simpleRoot] at h
  simpa only [map_smul, smul_eq_mul, mul_comm (principalCartanCoefficient b _),
    LieAlgebra.IsKilling.rootSystem_pairing_apply] using h

/-- Opposite root vectors from distinct simple roots commute. -/
theorem lie_simple_pos_neg_eq_zero (b : (Φ).Base) (i j : b.support) (hij : i ≠ j)
    {x y : L} (hx : x ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k))
    (hy : y ∈ rootSpace H (-(((Φ).root j : H →ₗ[k] k) : H → k))) : ⁅x, y⁆ = 0 := by
  classical
  let α : H →ₗ[k] k := (Φ).root i - (Φ).root j
  have hNonzero : α ≠ 0 := sub_ne_zero.mpr fun h => hij (Subtype.ext ((Φ).root.injective h))
  have hLie : ⁅x, y⁆ ∈ rootSpace H (α : H → k) := by
    have h := lie_mem_genWeightSpace_of_mem_genWeightSpace hx hy
    have hα : (α : H → k) = ((Φ).root i : H → k) + -((Φ).root j : H → k) := by
      funext z
      simp only [α, LinearMap.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg,
        LinearMap.add_apply, LinearMap.neg_apply]
    rwa [hα]
  by_contra h
  have hSpace : rootSpace H (α : H → k) ≠ ⊥ := by
    intro hZero
    apply h
    exact (LieSubmodule.mem_bot (R := k) (L := H) ⁅x, y⁆).mp (hZero ▸ hLie)
  let β : Weight k H L := ⟨(α : H → k), hSpace⟩
  have hβ : β.IsNonZero := by
    intro hβ
    apply hNonzero
    apply LinearMap.ext
    intro z
    exact congrFun hβ z
  let r : H.root := ⟨β, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ⟩⟩
  have hr : (Φ).root r = α := LinearMap.ext fun _ => rfl
  exact b.sub_nmem_range_root i.property j.property ⟨r, hr⟩

/-- The sums over the actual simple-root triples form a principal `sl₂` triple. -/
theorem exists_principalSl2Triple_of_rootBase (b : (Φ).Base)
    [Fintype b.support] [Nonempty b.support] :
    ∃ e f : b.support → L,
      (∀ i : b.support, e i ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k)) ∧
      (∀ i : b.support, f i ∈ rootSpace H (-(((Φ).root i : H →ₗ[k] k) : H → k))) ∧
      (∀ i : b.support, IsSl2Triple ((Φ).coroot i : L) (e i) (f i)) ∧
      IsSl2Triple (principalCartanElement b : L) (∑ i, e i)
        (∑ i, principalCartanCoefficient b i • f i) := by
  classical
  have hTriples (i : b.support) : ∃ e f : L,
      IsSl2Triple ((Φ).coroot i : L) e f ∧
      e ∈ rootSpace H (((Φ).root i : H →ₗ[k] k) : H → k) ∧
      f ∈ rootSpace H (-(((Φ).root i : H →ₗ[k] k) : H → k)) := by
    let α : Weight k H L := i.val.val
    have hα : α.IsNonZero := (Finset.mem_filter.mp i.val.property).2
    obtain ⟨h,e,f,t,he,hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    have hH : h = (Φ).coroot i := t.h_eq_coroot hα he hf
    exact ⟨e,f,hH ▸ t, he, hf⟩
  choose e f ht he hf using hTriples
  let h₀ := principalCartanElement b
  let c := principalCartanCoefficient b
  refine ⟨e,f,he,hf,ht, ?_⟩
  constructor
  · intro hZero
    obtain ⟨i⟩ := ‹Nonempty b.support›
    have h0 : h₀ = 0 := Subtype.ext hZero
    have his := principalCartanElement_simpleRoot b i
    change (Φ).root i h₀ = (2 : k) at his
    rw [h0, map_zero] at his
    exact (by norm_num : (0 : k) ≠ 2) his
  · change ⁅∑ i, e i, ∑ i, c i • f i⁆ = (h₀ : L)
    rw [sum_lie_sum]
    have h : ∑ i : b.support, ∑ j : b.support, ⁅e i, c j • f j⁆ =
        ∑ i : b.support, c i • ((Φ).coroot i : L) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · rw [lie_smul, (ht i).lie_e_f]
      · intro j _ hji
        rw [lie_smul, lie_simple_pos_neg_eq_zero b i j hji.symm (he i) (hf j), smul_zero]
      · simp
    rw [h]
    have hs := congrArg H.incl.toLinearMap (sum_principalCartanCoefficient_coroot b)
    simp only [map_sum, map_smul] at hs
    exact hs
  · rw [lie_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := lie_eq_smul_of_mem_rootSpace (he i) h₀
    change ⁅(h₀ : L), e i⁆ = (Φ).root i h₀ • e i at h
    rw [show (Φ).root i h₀ = (2 : k) from principalCartanElement_simpleRoot b i] at h
    simpa only [two_smul] using h
  · change ⁅(h₀ : L), ∑ i, c i • f i⁆ = -(2 • ∑ i, c i • f i)
    rw [lie_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := lie_eq_smul_of_mem_rootSpace
      ((rootSpace H (-(((Φ).root i : H →ₗ[k] k) : H → k))).smul_mem (c i) (hf i)) h₀
    change ⁅(h₀ : L), c i • f i⁆ = -((Φ).root i h₀) • (c i • f i) at h
    rw [show (Φ).root i h₀ = (2 : k) from principalCartanElement_simpleRoot b i] at h
    simpa only [neg_smul, two_smul] using h

end WideE
