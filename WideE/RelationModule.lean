import WideE.FiniteModule
import WideE.MinimalNonvanishing
import WideE.Punctured
import WideE.Values

/-! The finite differential modules and algebraic fiber relation attached to
an actual unit in the wide E-value ring. -/

open scoped BigOperators TensorProduct WideE

noncomputable section

namespace WideE

open LaurentPolynomial

local notation "R" => LaurentPolynomial AlgebraicComplex
local notation "D" => widePuncturedDerivation

local instance (priority := 2000) laurentSelfModule (K : Type*) [CommRing K] :
    Module (LaurentPolynomial K) (LaurentPolynomial K) := Semiring.toModule

private def laurentAddDerivative (K : Type*) [CommRing K] :
    LaurentPolynomial K →+ LaurentPolynomial K :=
  (laurentDerivation (K := K)).toLinearMap.toAddMonoidHom

theorem puncturedEvaluation_smul (z : ℂˣ) (p : R) (x : WidePunctured) :
    puncturedEvaluation z (p • x) =
      eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z p * puncturedEvaluation z x := by
  change puncturedEvaluation z (puncturedLaurentEmbedding p * x) = _
  rw [← puncturedLaurentEmbedding_eval]
  rfl

theorem widePuncturedDerivation_smul (p : R) (x : WidePunctured) :
    D (p • x) = laurentDerivation p • x + p • D x := by
  change D (puncturedLaurentEmbedding p * x) =
    puncturedLaurentEmbedding (laurentDerivation p) * x + puncturedLaurentEmbedding p * D x
  rw [Derivation.leibniz, puncturedLaurentEmbedding_derivation]
  simp only [smul_eq_mul]
  ac_rfl

theorem widePuncturedDerivation_mul (x y : WidePunctured) :
    D (x * y) = D x * y + x * D y := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ac_rfl

theorem wideFiniteSpan_of_operator {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (h : HasLaurentOperator f) :
    ∃ M : Submodule R WidePunctured, M.FG ∧ restrictWide hf ∈ M ∧ ∀ x ∈ M, D x ∈ M := by
  obtain ⟨r, hr, b, hb⟩ := h
  let d := (D).toLinearMap.toAddMonoidHom
  have hRec : d^[r] (restrictWide hf) = ∑ j, b j • d^[j.val] (restrictWide hf) := by
    apply Subtype.ext
    funext z
    change puncturedEvaluation z (D^[r] (restrictWide hf)) =
      puncturedEvaluation z (∑ j, b j • D^[j.val] (restrictWide hf))
    rw [map_sum, widePuncturedDerivation_iterate]
    simp_rw [puncturedEvaluation_smul, widePuncturedDerivation_iterate,
      puncturedEvaluation_apply, restrictWide_apply]
    exact hb z
  exact finite_stable_span_of_monic (laurentAddDerivative AlgebraicComplex) d
    (fun p x => widePuncturedDerivation_smul p x) (restrictWide hf) r hr b hRec

private theorem exists_wideFiniteSpan (hB : WideLaurentOperatorExistence)
    {f : ℂ → ℂ} (hf : IsWideEFunction f) :
    ∃ M : Submodule R WidePunctured, M.FG ∧ restrictWide hf ∈ M ∧ ∀ x ∈ M, D x ∈ M := by
  by_cases h : f = 0
  · subst f
    exact ⟨⊥, Submodule.fg_bot, Submodule.zero_mem _, fun x hx => by
      rw [Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact Submodule.zero_mem _⟩
  exact wideFiniteSpan_of_operator hf (hB f hf h)

private def constantSpan : Submodule R WidePunctured := Submodule.span R {1}

private theorem constantSpan_stable : ∀ x ∈ constantSpan, D x ∈ constantSpan := by
  intro x hx
  apply derivation_mem_span (laurentAddDerivative AlgebraicComplex)
    (D).toLinearMap.toAddMonoidHom (fun p x => widePuncturedDerivation_smul p x) _ hx
  intro y hy
  obtain rfl : y = (1 : WidePunctured) := Set.mem_singleton_iff.mp hy
  change D 1 ∈ constantSpan
  rw [Derivation.map_one_eq_zero]
  exact Submodule.zero_mem _

/-- The same representatives of the original values, their quotient, and the
constant one lie in one finite differential module. -/
structure WideInverseModule (ξ : ℂ) where
  M : Submodule R WidePunctured
  finite : M.FG
  stable : ∀ x ∈ M, D x ∈ M
  one_mem : (1 : WidePunctured) ∈ M
  f : M
  g : M
  h : M
  factor : f.val * g.val - 1 = (T 1 - 1 : R) • h.val
  value_f : puncturedEvaluation 1 f = ξ
  value_g : puncturedEvaluation 1 g = ξ⁻¹

theorem exists_wideInverseModule (hB : WideLaurentOperatorExistence) {ξ : ℂ}
    (hξ : IsWideEValueUnit ξ) : Nonempty (WideInverseModule ξ) := by
  obtain ⟨hn, ⟨f, hf, hvf⟩, ⟨g, hg, hvg⟩⟩ := hξ
  let w (z : ℂ) := f z * g z - 1
  have hw : IsWideEFunction w := (hf.mul hg).sub (isWideEFunction_const 1)
  have hwZero : w 1 = 0 := by simp [w, hvf, hvg, hn]
  obtain ⟨h, hh, hdiv⟩ := wideEFunction_divAtOne_of_laurentOperatorExistence hB hw hwZero
  obtain ⟨F, hFfin, hfF, hFs⟩ := exists_wideFiniteSpan hB hf
  obtain ⟨G, hGfin, hgG, hGs⟩ := exists_wideFiniteSpan hB hg
  obtain ⟨H, hHfin, hhH, hHs⟩ := exists_wideFiniteSpan hB hh
  let M := ((F ⊔ G) ⊔ H) ⊔ constantSpan
  have hMfin : M.FG := ((hFfin.sup hGfin).sup hHfin).sup (Submodule.fg_span_singleton 1)
  let d := (D).toLinearMap.toAddMonoidHom
  have hMs : ∀ x ∈ M, D x ∈ M :=
    stable_sup d (stable_sup d (stable_sup d hFs hGs) hHs) constantSpan_stable
  have hFM : F ≤ M := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hGM : G ≤ M := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hHM : H ≤ M := le_sup_right.trans le_sup_left
  have h1 : (1 : WidePunctured) ∈ M :=
    (le_sup_right : constantSpan ≤ M) (Submodule.subset_span (Set.mem_singleton 1))
  refine ⟨⟨M, hMfin, hMs, h1, ⟨_, hFM hfF⟩, ⟨_, hGM hgG⟩, ⟨_, hHM hhH⟩,
    ?_, hvf, hvg⟩⟩
  apply Subtype.ext
  funext z
  change f z * g z - 1 = puncturedEvaluation z ((T 1 - 1 : R) • restrictWide hh)
  rw [puncturedEvaluation_smul, map_sub, map_one, eval₂_T, zpow_one]
  exact (hdiv z).symm

def WideInverseModule.fiber_relation {ξ : ℂ} (data : WideInverseModule ξ) :=
  inverse_fiber_of_factorization data.M data.one_mem data.f data.g data.h data.factor

end WideE
