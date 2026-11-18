import WideE.GeneratedPVComparison
import WideE.PianzolaCocycleAssembly
import WideE.ReductiveBlockGalois
import WideE.ReductiveCocycle

/-! The connected-group section theorem and the general normalized comparison. -/

noncomputable section

namespace WideE

set_option maxHeartbeats 1200000 in
/-- The connected-group section theorem over the Kummer algebras in the paper. -/
theorem pianzolaForKummerAlgebras : PianzolaForKummerAlgebras AlgebraicComplex := by
  apply pianzolaForKummerAlgebras_of_finiteGalois_coboundary
  intro H _ _ _ _ E c hc
  refine isHopfPointCoboundary_of_reductive_block_quotients ?_ E c hc
  intro Q _ _ _ _ ι _ _ W hD he hGen L hK hCompl hDiag hNil E' d hd
  exact isHopfPointCoboundary_of_reductiveLie W hD he hGen hK hCompl hDiag hNil E' d hd

/-- The Picard–Vessiot algebras of Laurent systems admit sections after a Kummer cover. -/
theorem widePVKummerSectionExistence : WidePVKummerSectionExistence :=
  widePVKummerSectionExistence_of_pianzola pianzolaForKummerAlgebras

/-- Every Laurent system admits the normalized, natural tensor comparison after a Kummer cover. -/
theorem exists_normalizedLaurentComparison {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentPolynomial AlgebraicComplex)) :
    ∃ q : ℕ, 0 < q ∧ Nonempty
      (NormalizedLaurentComparison A (kummerAlgHom AlgebraicComplex q) (evalAtOneAlgHom AlgebraicComplex)) :=
  exists_normalizedLaurentComparison_of_pianzola pianzolaForKummerAlgebras A

end WideE
