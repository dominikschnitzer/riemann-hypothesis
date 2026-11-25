module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HRAddSmul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MeasureImageCosets
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OmAtComplZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHI
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def clsP (a : ℕ) (ϖ : Fv F v) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Set (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) :=
  QuotientAddGroup.mk '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
    (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ T}

def MeasP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    MeasurableAdd (TupV (E := E) v n a) ∧ MeasurableSet (LamT v Λ a) ∧
      MeasurableSet (lamP v Λ a ϖ : Set (TupV (E := E) v n a))

def IdxP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a)

def ClsP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ℝ) =
      qv v ^ (2 * n * a - a ^ 2) * prodEtaB (E := E) v n a

theorem countP_of (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasP σ J ψ v Λ a Y)
    (hI : IdxP σ J ψ v Λ a Y) (hC : ClsP σ J ψ v Λ a Y) (hPC : PrimCos σ J ψ v Λ a) : CountP σ J ψ v Λ a Y := by
  intro hG hμ ϖ hϖ
  obtain ⟨hMA, hL, hP⟩ := hM hG ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have hcos : ∀ x ∈ PrimT v Λ a, ∀ Z ∈ LamT v Λ a, x + sc (E := E) v ϖ • Z ∈ PrimT v Λ a := by
    intro x hx Z hZ
    apply hPC hG.1 hG.2.1 hSD hG.2.2.2.1 ϖ hϖ x hx
    refine (PI.VolStabSW.mem_smulSub _ _ _).2 ⟨Z, hZ, ?_⟩
    funext i p
    show ϖ ^ (0 + 1) • Z i p = sc (E := E) v ϖ * Z i p
    rw [zero_add, pow_one, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  exact countQ_of σ J ψ v Λ a Y (PrimT v Λ a) (prodEtaB (E := E) v n a) hSD hG.2.2.2.2.1 hμ ϖ hϖ
    hMA hL hP (fun x hx => hx.1) hcos (by simpa [clsP] using hC hG ϖ hϖ)
    (prod_one_sub_eta_nonneg v (Finset.Icc (n - a) n)) (hI hG ϖ hϖ)

end PI.OmVd
