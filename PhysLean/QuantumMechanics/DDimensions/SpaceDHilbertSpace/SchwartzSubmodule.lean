/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.Basic
/-!

# Schwartz submodule of the Hilbert space

-/

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open MeasureTheory
open InnerProductSpace
open SchwartzMap

variable {d : ℕ}

/-- The continuous linear map including Schwartz functions into `SpaceDHilbertSpace d`. -/
def schwartzIncl : 𝓢(Space d, ℂ) →L[ℂ] SpaceDHilbertSpace d := toLpCLM ℂ (E := Space d) ℂ 2

/-- The submodule of `SpaceDHilbertSpace d` consisting of Schwartz functions. -/
abbrev schwartzSubmodule (d : ℕ) := (schwartzIncl (d := d)).range

instance : CoeFun (schwartzSubmodule d) fun _ ↦ Space d → ℂ := ⟨fun ψ ↦ ψ.val⟩

@[simp]
lemma val_eq_coe (ψ : schwartzSubmodule d) (x : Space d) : ψ.val x = ψ x := rfl

lemma schwartzSubmodule_dense :
    Dense (schwartzSubmodule d : Set (SpaceDHilbertSpace d)) :=
  denseRange_toLpCLM ENNReal.top_ne_ofNat.symm

/-- The linear equivalence between the Schwartz functions `𝓢(Space d, ℂ)`
  and the Schwartz submodule of `SpaceDHilbertSpace d`. -/
def schwartzEquiv : 𝓢(Space d, ℂ) ≃ₗ[ℂ] schwartzSubmodule d :=
  LinearEquiv.ofInjective schwartzIncl.toLinearMap (injective_toLp (E := Space d) 2)

variable (f g : 𝓢(Space d, ℂ))

lemma schwartzEquiv_coe_ae : (schwartzEquiv f) =ᵐ[volume] f := coeFn_toLp f 2 volume

lemma schwartzEquiv_inner :
    ⟪schwartzEquiv f, schwartzEquiv g⟫_ℂ = ∫ x : Space d, starRingEnd ℂ (f x) * g x := by
  apply integral_congr_ae
  filter_upwards [schwartzEquiv_coe_ae f, schwartzEquiv_coe_ae g] with _ hf hg
  simp [hf, hg, mul_comm]

lemma schwartzEquiv_ae_eq (h : schwartzEquiv f =ᵐ[volume] schwartzEquiv g) : f = g :=
  (EmbeddingLike.apply_eq_iff_eq _).mp (SetLike.coe_eq_coe.mp (ext_iff.mpr h))

lemma schwartzEquiv_exists (ψ : schwartzSubmodule d) : ∃ f, ψ = schwartzEquiv f := by
  use schwartzEquiv.symm ψ
  exact (LinearEquiv.apply_symm_apply _ _).symm

end
end SpaceDHilbertSpace
end QuantumMechanics
