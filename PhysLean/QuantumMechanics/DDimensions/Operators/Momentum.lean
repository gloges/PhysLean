/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
import PhysLean.QuantumMechanics.PlanckConstant
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Momentum vector operator

In this module we define:
- The momentum operator on Schwartz maps, component-wise.
- The momentum squared operator on Schwartz maps.

-/

namespace QuantumMechanics
noncomputable section
open Constants
open Space
open ContDiff SchwartzMap

variable {d : ℕ} (i : Fin d)

/-- Component `i` of the momentum operator is the continuous linear map
from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `-iℏ ∂ᵢψ`. -/
def momentumOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (- Complex.I * ℏ) • (SchwartzMap.evalCLM ℂ (Space d) ℂ (basis i)) ∘L
    (SchwartzMap.fderivCLM ℂ (Space d) ℂ)

@[inherit_doc momentumOperator]
macro "𝐩[" i:term "]" : term => `(momentumOperator $i)

lemma momentumOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐩[i] ψ = (- Complex.I * ℏ) • ∂[i] ψ := rfl

@[simp]
lemma momentumOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩[i] ψ x = - Complex.I * ℏ * ∂[i] ψ x := rfl

/-- The square of the momentum operator, `𝐩² ≔ ∑ᵢ 𝐩ᵢ∘𝐩ᵢ`. -/
def momentumOperatorSqr : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) := ∑ i, 𝐩[i] ∘L 𝐩[i]

@[inherit_doc momentumOperatorSqr]
notation "𝐩²" => momentumOperatorSqr

lemma momentumOperatorSqr_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) :
    𝐩² ψ x = ∑ i, 𝐩[i] (𝐩[i] ψ) x := by
  dsimp only [momentumOperatorSqr]
  rw [← SchwartzMap.coe_coeHom]
  simp only [ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_comp', Finset.sum_apply,
    Function.comp_apply, map_sum]

/-!
## Unbounded momentum operators
-/

open SpaceDHilbertSpace

/-- The momentum operators defined on the Schwartz submodule. -/
def momentumOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  (schwartzEquiv (d := d)) ∘ₗ 𝐩[i].toLinearMap ∘ₗ (schwartzEquiv (d := d)).symm

@[sorryful]
lemma momentumOperatorSchwartz_isSymmetric : (momentumOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨f, rfl⟩ := schwartzEquiv_exists ψ
  obtain ⟨f', rfl⟩ := schwartzEquiv_exists ψ'
  unfold momentumOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
    Function.comp_apply, LinearEquiv.symm_apply_apply, schwartzEquiv_inner, momentumOperator_apply,
    neg_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_neg, mul_neg]
  -- Need integration by parts and `starRingEnd ∂[i] = ∂[i] starRingEnd`:
  -- ⊢ ∫ (x : Space d), Complex.I * ↑↑ℏ * (starRingEnd ℂ) (Space.deriv i (⇑f) x) * f' x =
  -- ∫ (x : Space d), -((starRingEnd ℂ) (f x) * (Complex.I * ↑↑ℏ * Space.deriv i (⇑f') x))
  sorry

/-- The symmetric momentum unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
@[sorryful]
def momentumUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (hE := schwartzSubmodule_dense) (momentumOperatorSchwartz i)
    (momentumOperatorSchwartz_isSymmetric i)

end
end QuantumMechanics
