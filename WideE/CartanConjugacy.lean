import WideE.CartanNormalizer
import WideE.HopfAdjointCenter
import WideE.HopfKostantWeyl
import WideE.ReductiveCartanTorus
import WideE.SimpleCoreflectionRepresentative

/-! Conjugate regular Cartan terms differ by simple coreflections, with unchanged center. -/

noncomputable section

open LieAlgebra LieAlgebra.IsKilling LieModule Module
open scoped Matrix TensorProduct

namespace WideE

variable {k H ι η : Type*} [Field k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Fintype ι] [DecidableEq ι] [Fintype η]

local notation "𝔤" => hopfInvariantDerivations k H
local notation "J" => hopfLieVectorInvariantDerivations (k := k) (H := H)
local notation "S" => derivedSeries k 𝔤 1
local notation "Z" => center k 𝔤

section Representatives

variable {L : Type*} [LieRing L] [LieAlgebra k L] [IsKilling k L] [FiniteDimensional k L]
  {C : LieSubalgebra k L} [C.IsCartanSubalgebra] [IsTriangularizable k C L]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem C

set_option maxHeartbeats 1200000 in
/-- Every word of simple coreflections on the Cartan has a constant Hopf group representative. -/
theorem exists_hopfPoint_cartanCoreflection (bC : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (j : L →ₗ⁅k⁆ 𝔤) (B : (Φ).Base) (e f : B.support → L)
    (hE : ∀ i : B.support, e i ∈ rootSpace C (((Φ).root i : C →ₗ[k] k) : C → k))
    (hF : ∀ i : B.support, f i ∈ rootSpace C (-(((Φ).root i : C →ₗ[k] k) : C → k)))
    (ht : ∀ i : B.support, IsSl2Triple ((Φ).coroot i : L) (e i) (f i))
    (w : C ≃ₗ[k] C) (hw : w ∈ principalSimpleCoreflectionSubgroup B) :
    ∃ p : H →ₐ[k] k, ∀ z : C, hopfAdjoint p ((J).symm (j (z : L))) = (J).symm (j (w z : L)) := by
  classical
  letI : LieAlgebra ℚ L := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ k L))
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  let a (z : C) := (J).symm (j (z : L))
  change ∃ p : H →ₐ[k] k, ∀ z : C, hopfAdjoint p (a z) = a (w z)
  refine Subgroup.closure_induction (p := fun v _ => ∃ p : H →ₐ[k] k,
    ∀ z : C, hopfAdjoint p (a z) = a (v z)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨i, rfl⟩
    have h := exists_hopfPoint_simpleCoreflection_on_cartan (H := C) bC U hD he hGen j
      (i.val : C.root) (e i) (f i) (hE i) (hF i) (ht i)
    exact h
  · exact ⟨1, fun z => hopfAdjoint_one_point bC (a z)⟩
  · rintro u v _ _ ⟨p, hp⟩ ⟨q, hq⟩
    refine ⟨p * q, fun z => ?_⟩
    rw [hopfAdjoint_mul bC, hq, hp]
    rfl
  · rintro u _ ⟨p, hp⟩
    refine ⟨p⁻¹, fun z => ?_⟩
    have h := hp (u⁻¹ z)
    rw [show u (u⁻¹ z) = z from u.apply_symm_apply z] at h
    rw [← h, ← hopfAdjoint_mul bC, inv_mul_cancel]
    exact hopfAdjoint_one_point bC _

end Representatives

section CentralPart

variable [Algebra.FiniteType k H] [IsDomain H]

/-- The actual adjoint action fixes the central part of the Lie algebra. -/
theorem hopfAdjoint_fixes_centralDirection (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (p : H →ₐ[k] k) (z : Z) : hopfAdjoint p ((J).symm (z : 𝔤)) = (J).symm (z : 𝔤) := by
  have h := hopfAdjoint_fixes_sum_centralDirections U hD he hGen p (fun _ : Fin 1 => z) (fun _ => 1)
  have hz : (Algebra.ofId k k).toLinearMap.comp ((J).symm (z : 𝔤)) = (J).symm (z : 𝔤) := by
    ext a
    rfl
  simpa only [Fin.sum_univ_one, one_smul, hz] using h

variable [IsKilling k (derivedSeries k (hopfInvariantDerivations k H) 1)]
  [FiniteDimensional k (derivedSeries k (hopfInvariantDerivations k H) 1)]
  {C : LieSubalgebra k (derivedSeries k (hopfInvariantDerivations k H) 1)}
  [C.IsCartanSubalgebra] [IsTriangularizable k C (derivedSeries k (hopfInvariantDerivations k H) 1)]

local notation "Φ" => LieAlgebra.IsKilling.rootSystem C

private def cartanLieVector (C : LieSubalgebra k S) (z : C) : HopfLieVector k H k :=
  (J).symm ((z : S) : 𝔤)

local notation "cartan" => cartanLieVector C

set_option maxHeartbeats 1600000 in
/-- Actual conjugation between regular Cartan terms induces a simple Weyl word and fixes the center. -/
theorem exists_cartanCoreflection_of_regular_conjugate (bC : Basis η k (HopfCotangent k H))
    (U : (Matrix ι ι H)ˣ)
    (hD : ∀ i j, Coalgebra.comul (R := k) (U.val i j) = ∑ l, U.val i l ⊗ₜ[k] U.val l j)
    (he : ∀ i j, Coalgebra.counit (R := k) (U.val i j) = if i = j then 1 else 0)
    (hGen : Algebra.adjoin k (Set.range fun ij : ι × ι => U.val ij.1 ij.2) = ⊤)
    (hCompl : IsCompl S Z) (B : (Φ).Base) (e f : B.support → S)
    (hE : ∀ i : B.support, e i ∈ rootSpace C (((Φ).root i : C →ₗ[k] k) : C → k))
    (hF : ∀ i : B.support, f i ∈ rootSpace C (-(((Φ).root i : C →ₗ[k] k) : C → k)))
    (ht : ∀ i : B.support, IsSl2Triple ((Φ).coroot i : S) (e i) (f i))
    (hPrincipal : ∀ p : H →ₐ[k] k,
      hopfAdjoint p (cartan (principalCartanElement B)) = cartan (principalCartanElement B) →
      ∀ x : C, hopfAdjoint p (cartan x) = cartan x)
    (z z' : C) (v v' : Z) (hz : ∀ α : C.root, (Φ).root α z ≠ 0)
    (hz' : ∀ α : C.root, (Φ).root α z' ≠ 0) (g : H →ₐ[k] k)
    (hg : hopfAdjoint g ((J).symm (cartanCenterDirection C z v)) =
      (J).symm (cartanCenterDirection C z' v')) :
    v = v' ∧ ∃ w : C ≃ₗ[k] C, w ∈ principalSimpleCoreflectionSubgroup B ∧ w z = z' := by
  classical
  letI : Group (H →ₐ[k] k) := hopfPointGroup
  let a := hopfAdjointInvariantDerivationsLieEquiv bC U hD he hGen g
  let aS := lieEquivOnDerived a
  have hFix (c : Z) : a (c : 𝔤) = c := by
    rw [hopfAdjointInvariantDerivationsLieEquiv_apply,
      hopfAdjoint_fixes_centralDirection U hD he hGen, (J).apply_symm_apply]
  have hTot : a (((z : S) : 𝔤) + (v : 𝔤)) = ((z' : S) : 𝔤) + (v' : 𝔤) := by
    rw [hopfAdjointInvariantDerivationsLieEquiv_apply]
    change (J) (hopfAdjoint g ((J).symm (cartanCenterDirection C z v))) = cartanCenterDirection C z' v'
    rw [hg, (J).apply_symm_apply]
  have hAdd : a (((z : S) : 𝔤) + (v : 𝔤)) = a ((z : S) : 𝔤) + a (v : 𝔤) :=
    a.toLieHom.map_add _ _
  rw [hAdd, hFix, ← lieEquivOnDerived_apply_val] at hTot
  change ((aS (z : S) : S) : 𝔤) + (v : 𝔤) = ((z' : S) : 𝔤) + (v' : 𝔤) at hTot
  have hDiff : ((aS (z : S) : S) : 𝔤) - ((z' : S) : 𝔤) = (v' : 𝔤) - (v : 𝔤) := by
    rw [sub_eq_sub_iff_add_eq_add]
    simpa only [add_comm (v' : 𝔤)] using hTot
  have hBot : (v' : 𝔤) - (v : 𝔤) ∈ S ⊓ Z := by
    refine ⟨?_, (Z).toSubmodule.sub_mem v'.property v.property⟩
    rw [← hDiff]
    exact (S).toSubmodule.sub_mem (aS z.val).property z'.val.property
  have hv : v = v' := by
    apply Subtype.ext
    rw [hCompl.inf_eq_bot, LieSubmodule.mem_bot] at hBot
    exact (sub_eq_zero.mp hBot).symm
  refine ⟨hv, ?_⟩
  have hAz : aS (z : S) = (z' : S) := by
    apply Subtype.ext
    rw [hv, add_left_inj] at hTot
    exact hTot
  let c := cartanEquivOfRegularConjugation aS z z' hz hz' hAz
  have hc (x : C) : (c x : S) = aS (x : S) := rfl
  have hAct (x : C) : hopfAdjoint g (cartan x) = cartan (c x) := by
    apply (J).injective
    change (J) (hopfAdjoint g (cartan x)) = (J) ((J).symm (((c x : C) : S) : 𝔤))
    rw [(J).apply_symm_apply, hc, lieEquivOnDerived_apply_val]
    exact (hopfAdjointInvariantDerivationsLieEquiv_apply bC U hD he hGen g _).symm
  let h₀ := principalCartanElement B
  obtain ⟨p, hp⟩ := exists_rootPerm_of_cartanEquiv aS c hc
  obtain ⟨w, hw, hwc⟩ := exists_coreflectionClosure_apply_eq_of_permuted_principal_values Φ B h₀ (c h₀)
    (principalCartanElement_simpleRoot B) (principalCartanElement_root_height B)
    ⟨p, fun i => hp i h₀⟩
  obtain ⟨q, hq⟩ := exists_hopfPoint_cartanCoreflection (C := C) bC U hD he hGen (S).incl
    B e f hE hF ht w hw
  have hAction (x : C) : hopfAdjoint (q * g) (cartan x) = cartan (w (c x)) := by
    rw [hopfAdjoint_mul bC, hAct]
    exact hq (c x)
  have hFixC (x : C) : w (c x) = x := by
    have h := (hAction x).symm.trans (hPrincipal (q * g) (by rw [hAction, hwc]) x)
    exact Subtype.ext (Subtype.ext ((J).symm.injective h))
  have hcEq : c = w⁻¹ := by
    apply LinearEquiv.ext
    intro x
    simpa only [w.symm_apply_apply] using congrArg w.symm (hFixC x)
  refine ⟨c, hcEq.symm ▸ (principalSimpleCoreflectionSubgroup B).inv_mem hw, ?_⟩
  exact Subtype.ext hAz

end CentralPart

end WideE
