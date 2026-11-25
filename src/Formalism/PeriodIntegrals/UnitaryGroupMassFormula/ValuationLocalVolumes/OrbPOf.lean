module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB

@[expose] public section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ExtP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodP σ J ψ v Λ a Y → ∃ G : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = G ∧ IsUnit (colM v Z).det

theorem orbP_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtP σ J ψ v Λ a Y) :
    OrbP σ J ψ v Λ a Y := by
  intro hG
  have h : a ≤ n := hG.2.2.2.2.1
  obtain ⟨G, hGe⟩ := hE h hG
  exact orbQ_of σ J v Λ h Y (PrimT v Λ a) hG.2.2.2.2.2 G hGe

end PI.OmVd
