import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Testing abelian 1-cocycles on Sylow subgroups

A coboundary on a subgroup gives a coboundary for the cocycle raised to
the subgroup index. Triviality on Sylow subgroups gives triviality on
the whole finite group.
-/

noncomputable section

open scoped BigOperators

namespace WideE

variable {G M : Type*} [Group G] [Finite G] [CommGroup M] [MulDistribMulAction G M]
variable (c : G → M) (hc : ∀ g h, c (g * h) = c g * (g • c h))
include hc

/-- The product of the translates of a subgroup fixed point gives a
coboundary for the cocycle raised to the subgroup index. -/
theorem exists_coboundary_pow_subgroup_index (P : Subgroup G) (b : M)
    (hb : ∀ p : P, c p * ((p : G) • b) = b) :
    ∃ a : M, ∀ g, c g ^ P.index * (g • a) = a := by
  classical
  let qValue : G ⧸ P → M := Quotient.lift (fun g => c g * (g • b)) (by
    intro x y h
    let p : P := ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp h⟩
    have hy : y = x * (p : G) := by simp [p]
    change c x * (x • b) = c y * (y • b)
    rw [hy, hc, mul_smul, mul_assoc, ← smul_mul', hb])
  have hTranslate (g : G) (q : G ⧸ P) : qValue (g • q) = c g * (g • qValue q) := by
    induction q using Quotient.inductionOn' with
    | _ h =>
      change c (g * h) * ((g * h) • b) = c g * (g • (c h * (h • b)))
      rw [hc, mul_smul, smul_mul', mul_assoc]
  letI : Fintype (G ⧸ P) := Fintype.ofFinite _
  let a : M := ∏ q : G ⧸ P, qValue q
  refine ⟨a, fun g => ?_⟩
  calc
    c g ^ P.index * (g • a) = ∏ q : G ⧸ P, qValue (g • q) := by
      simp only [hTranslate, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← Finset.smul_prod', Subgroup.index_eq_card, Nat.card_eq_fintype_card, a]
    _ = a := Fintype.prod_bijective (fun q : G ⧸ P => g • q)
      (MulAction.bijective g) _ _ (fun _ => rfl)

/-- A cocycle of a finite group in an abelian group is a coboundary if its
restriction is a coboundary on a Sylow subgroup for each prime divisor of
the group order. -/
theorem exists_coboundary_of_sylow
    (hSylow : ∀ (p : ℕ) [Fact p.Prime], p ∣ Nat.card G →
      ∃ (P : Sylow p G) (b : M), ∀ g : (P : Subgroup G), c g * ((g : G) • b) = b) :
    ∃ a : M, ∀ g, c g * (g • a) = a := by
  classical
  let D : Ideal ℤ :=
    { carrier := {n | ∃ a : M, ∀ g, c g ^ n * (g • a) = a}
      zero_mem' := ⟨1, by simp⟩
      add_mem' := by
        rintro m n ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a * b, fun g => ?_⟩
        rw [zpow_add, smul_mul', mul_mul_mul_comm (c g ^ m), ha, hb]
      smul_mem' := by
        rintro r n ⟨a, ha⟩
        refine ⟨a ^ r, fun g => ?_⟩
        change c g ^ (r * n) * (g • (a ^ r)) = a ^ r
        have hPow : g • (a ^ r) = (g • a) ^ r :=
          map_zpow (MulDistribMulAction.toMonoidHom M g) a r
        rw [mul_comm r n, zpow_mul, hPow, ← mul_zpow, ha] }
  let d := Submodule.IsPrincipal.generator D
  have hIndex (P : Subgroup G) (b : M) (hb : ∀ g : P, c g * ((g : G) • b) = b) :
      d.natAbs ∣ P.index := by
    have hMem : (P.index : ℤ) ∈ D := by
      change ∃ a : M, ∀ g, c g ^ (P.index : ℤ) * (g • a) = a
      simpa only [zpow_natCast] using exists_coboundary_pow_subgroup_index c hc P b hb
    have hDiv : d ∣ (P.index : ℤ) := by
      apply Ideal.mem_span_singleton.mp
      simpa only [d, Ideal.span_singleton_generator] using hMem
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hDiv
  have hOne : c 1 = 1 := by
    have h : c 1 * 1 = c 1 * c 1 := by simpa only [mul_one, one_smul] using hc 1 1
    exact (mul_left_cancel h).symm
  have hCard : d.natAbs ∣ Nat.card G := by
    rw [← Subgroup.index_bot]
    apply hIndex ⊥ 1
    intro g
    have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.property
    simp [hg, hOne]
  have hd : d.natAbs = 1 := by
    by_contra h
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨P, b, hb⟩ := hSylow p (hpd.trans hCard)
    exact P.not_dvd_index (hpd.trans (hIndex P b hb))
  have hD : D = ⊤ := Ideal.eq_top_of_isUnit_mem D (Submodule.IsPrincipal.generator_mem D)
    (Int.isUnit_iff_natAbs_eq.mpr hd)
  have hMem : (1 : ℤ) ∈ D := by rw [hD]; trivial
  change ∃ a : M, ∀ g, c g ^ (1 : ℤ) * (g • a) = a at hMem
  simpa only [zpow_one] using hMem

end WideE
