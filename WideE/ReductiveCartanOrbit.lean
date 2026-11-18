import WideE.ReductiveCartanTorus
import WideE.AdjointCartanRank
import WideE.PositiveKostantNormalizer

/-! A uniform open of adjoint conjugates of the Cartan and central directions. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule
open scoped Matrix TensorProduct

namespace WideE

section Parameters

variable {k Q : Type*} [Field k] [CommRing Q] [HopfAlgebra k Q]

local notation "𝔤" => hopfInvariantDerivations k Q
local notation "L" => HopfLieVector k Q k
local notation "θ" => (hopfLieVectorInvariantDerivations (k := k) (H := Q))

/-- The Cartan directions in a semisimple ideal together with the central
directions, viewed in the cotangent dual used by the adjoint action. -/
def cartanCenterLieEmbedding {S : LieIdeal k 𝔤} (C : LieSubalgebra k S) :
    (C × center k 𝔤) →ₗ[k] L :=
  (θ).symm.toLinearMap.comp
    ((S.toSubmodule.subtype.comp C.toSubmodule.subtype).coprod (center k 𝔤).toSubmodule.subtype)

@[simp] theorem cartanCenterLieEmbedding_apply {S : LieIdeal k 𝔤} (C : LieSubalgebra k S)
    (z : C × center k 𝔤) : θ (cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C z) = cartanCenterDirection C z.1 z.2 :=
  (θ).apply_symm_apply _

/-- A complementary semisimple ideal makes the Cartan and central parameters independent. -/
theorem cartanCenterLieEmbedding_injective {S : LieIdeal k 𝔤} (C : LieSubalgebra k S)
    (hS : IsCompl S (center k 𝔤)) : Function.Injective (cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C) := by
  let E := Submodule.prodEquivOfIsCompl S.toSubmodule (center k 𝔤).toSubmodule
    (LieSubmodule.isCompl_toSubmodule.mpr hS)
  intro x y hxy
  have hEq : E (x.1.val, x.2) = E (y.1.val, y.2) := by
    have h := congrArg (θ) hxy
    simpa only [cartanCenterLieEmbedding_apply, cartanCenterDirection,
      E, Submodule.coe_prodEquivOfIsCompl'] using h
  have h := E.injective hEq
  exact Prod.ext (Subtype.ext (congrArg (fun w : S × center k 𝔤 => w.1) h))
    (congrArg (fun w : S × center k 𝔤 => w.2) h)

end Parameters

section RegularRank

variable {k Q : Type*} [Field k] [CharZero k] [CommRing Q] [HopfAlgebra k Q]

local notation "𝔤" => hopfInvariantDerivations k Q
local notation "θ" => (hopfLieVectorInvariantDerivations (k := k) (H := Q))

variable {S : LieIdeal k (hopfInvariantDerivations k Q)} [FiniteDimensional k S] [LieAlgebra.IsKilling k S]
variable {C : LieSubalgebra k S} [C.IsCartanSubalgebra] [LieModule.IsTriangularizable k C S]

set_option maxHeartbeats 1000000 in
/-- The image of the adjoint differential at a regular Cartan point,
together with the Cartan and center directions, spans the actual Hopf Lie algebra. -/
theorem range_ad_regularCartan_sup_cartanCenter (hS : IsCompl S (center k 𝔤))
    (z : C) (hz : ∀ α : C.root, (LieAlgebra.IsKilling.rootSystem C).root α z ≠ 0) :
    LinearMap.range (LieModule.toEnd k 𝔤 𝔤 ((z : S) : 𝔤)) ⊔
      LinearMap.range ((θ).toLinearMap.comp (cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C)) = ⊤ := by
  let D := LieModule.toEnd k S S (z : S)
  have hEigenspaces : (⨆ α : C → k, D.eigenspace (α z)) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← LieSubmodule.iSup_toSubmodule_eq_top.mpr (iSup_genWeightSpace_eq_top k C S)]
    apply iSup_le
    intro α x hx
    refine (le_iSup (fun β : C → k => D.eigenspace (β z)) α) ?_
    exact Module.End.mem_eigenspace_iff.mpr (lie_eq_smul_of_mem_rootSpace hx z)
  have hKernel : LinearMap.ker D ≤ C.toSubmodule := by
    intro x hx
    exact (lie_regularCartan_eq_zero_iff_mem z hz x).mp hx
  have hRank := range_sup_eq_top_of_eigenspaces D (fun α : C → k => α z)
    hEigenspaces C.toSubmodule hKernel
  apply eq_top_iff.mpr
  intro x _
  have hx : x ∈ S ⊔ center k 𝔤 := hS.sup_eq_top ▸ LieSubmodule.mem_top x
  obtain ⟨u, hu, w, hw, hxSum⟩ := (LieSubmodule.mem_sup _ _ _).mp hx
  let u' : S := ⟨u, hu⟩
  have hu' : u' ∈ LinearMap.range D ⊔ C.toSubmodule := by
    rw [hRank]
    exact Submodule.mem_top
  obtain ⟨v, hv, z', hz', hEq⟩ := Submodule.mem_sup.mp hu'
  apply Submodule.mem_sup.mpr
  refine ⟨(v : 𝔤), ?_, (z' : 𝔤) + w, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hv
    exact ⟨(a : 𝔤), congrArg Subtype.val ha⟩
  · refine ⟨(⟨z', hz'⟩, ⟨w, hw⟩), ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, cartanCenterLieEmbedding_apply]
    rfl
  · have huv : (v : 𝔤) + (z' : 𝔤) = u := congrArg Subtype.val hEq
    rw [← add_assoc, huv, hxSum]

end RegularRank

section Open

variable {k Q ι η τ : Type*} [Field k] [CharZero k] [CommRing Q] [HopfAlgebra k Q]
  [IsDomain Q] [Algebra.FiniteType k Q] [Fintype ι] [DecidableEq ι]
  [Fintype η] [DecidableEq η] [Fintype τ]

local notation "𝔤" => hopfInvariantDerivations k Q
local notation "θ" => (hopfLieVectorInvariantDerivations (k := k) (H := Q))

variable {S : LieIdeal k (hopfInvariantDerivations k Q)} [FiniteDimensional k S] [LieAlgebra.IsKilling k S]
variable {C : LieSubalgebra k S} [C.IsCartanSubalgebra] [LieModule.IsTriangularizable k C S]

universe uΩ

set_option maxHeartbeats 1400000 in
/-- On a single principal open, every geometric vector is conjugate to Cartan
and central parameters satisfying the chosen nonzero polynomial condition. -/
theorem exists_reductiveCartan_principal_open_avoiding (U : (Matrix ι ι Q)ˣ)
    (hΔ : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (hε : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (b : Basis η k (HopfCotangent k Q))
    (hS : IsCompl S (center k 𝔤)) (cB : Basis τ k (C × center k 𝔤))
    (z : C) (hz : ∀ α : C.root, (LieAlgebra.IsKilling.rootSystem C).root α z ≠ 0)
    (d₀ : MvPolynomial τ k) (hd₀ : d₀ ≠ 0) :
    ∃ p : MvPolynomial η k, p ≠ 0 ∧ ∀ (Ω : Type uΩ) [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
      (x : HopfLieVector k Q Ω), MvPolynomial.aeval (fun i => x (b i)) p ≠ 0 →
      ∃ (g : Q →ₐ[k] Ω) (c : τ → Ω), MvPolynomial.aeval c d₀ ≠ 0 ∧
        x = hopfAdjoint g (∑ i, c i • (Algebra.ofId k Ω).toLinearMap.comp (cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C (cB i))) := by
  let F := (θ).toLinearMap.comp (cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C)
  let v (i : τ) := cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C (cB i)
  let a (i : τ) := cB.repr (z, 0) i
  have hParam : Submodule.span k (Set.range fun j => θ (v j)) = LinearMap.range F := by
    change Submodule.span k (Set.range (F ∘ cB)) = LinearMap.range F
    have hB : Submodule.span k (Set.range (cB : τ → C × center k 𝔤)) = ⊤ := cB.span_eq
    rw [Set.range_comp, ← Submodule.map_span, hB, Submodule.map_top]
  have hPoint : θ (∑ j, a j • v j) = ((z : S) : 𝔤) := by
    have hCoord : (∑ j, a j • F (cB j)) = F (z, 0) := by
      simpa only [map_sum, map_smul] using congrArg F (cB.sum_repr (z, 0))
    rw [map_sum]
    simp_rw [map_smul]
    change (∑ j, a j • F (cB j)) = _
    rw [hCoord]
    change θ (cartanCenterLieEmbedding (k := k) (Q := Q) (S := S) C (z, 0)) = _
    rw [cartanCenterLieEmbedding_apply, cartanCenterDirection]
    simp
  have hRank : LinearMap.range (LieModule.toEnd k 𝔤 𝔤 (θ (∑ j, a j • v j))) ⊔
      Submodule.span k (Set.range fun j => θ (v j)) = ⊤ := by
    rw [hPoint, hParam]
    exact range_ad_regularCartan_sup_cartanCenter hS z hz
  exact exists_hopfAdjointFamily_principal_open_avoiding_of_adjoint_span
    U hΔ hε hGen b v a hRank d₀ hd₀

end Open

end WideE
