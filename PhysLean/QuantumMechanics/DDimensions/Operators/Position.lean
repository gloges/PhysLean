/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.Unbounded
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
import PhysLean.SpaceAndTime.Space.Derivatives.Basic
/-!

# Position operators

In this module we define:
- `positionOperator i` acting on Schwartz maps `𝓢(Space d, ℂ)` by multiplication by `xᵢ`.
- `radiusRegPowOperator ε s` acting on Schwartz maps `𝓢(Space d, ℂ)` by multiplication
  by `(‖x‖² + ε²)^(s/2)`, a smooth regularization of `‖x‖ˢ`.
- `positionUnboundedOperator i`, a symmetric unbounded operator acting on the Schwartz submodule
  of the Hilbert space `SpaceDHilbertSpace d`.
- `radiusRegPowUnboundedOperator ε s`, a symmetric unbounded operator acting on the Schwartz
  submodule of the Hilbert space `SpaceDHilbertSpace d`. For `s ≤ 0` this operator is bounded
  (by `ε⁻ˢ`) and has natural domain the entire Hilbert space, but for uniformity we use the same
  domain for all `s`.

We also introduce the following notation:
- `𝐱[i]` for `positionOperator i`
- `𝐫[ε,s]` for `radiusRegPowOperator ε s`

-/

namespace QuantumMechanics
noncomputable section
open Space
open Function SchwartzMap ContDiff

variable {d : ℕ} (i : Fin d)

/-!
## Position vector operator
-/

/-- Component `i` of the position operator is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `xᵢψ`. -/
def positionOperator : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofRealCLM ∘L coordCLM i)

@[inherit_doc positionOperator]
macro "𝐱[" i:term "]" : term => `(positionOperator $i)

lemma positionOperator_apply_fun (ψ : 𝓢(Space d, ℂ)) :
    𝐱[i] ψ = smulLeftCLM ℂ (coordCLM i) • ψ := by
  unfold positionOperator
  ext x
  simp [smulLeftCLM_apply_apply (g := Complex.ofRealCLM ∘ (coordCLM i)) (by fun_prop) _ _,
    smulLeftCLM_apply (g := coordCLM i) (by fun_prop) _]

@[simp]
lemma positionOperator_apply (ψ : 𝓢(Space d, ℂ)) (x : Space d) : 𝐱[i] ψ x = x i * ψ x := by
  simp [positionOperator_apply_fun, smulLeftCLM_apply (g := coordCLM i) (by fun_prop) _,
    coordCLM_apply, coord_apply]

/-!

## Radius operator

-/
TODO "ZGCNP" "Incorporate normRegularizedPow into Space.Norm"

/-- Power of regularized norm, `(‖x‖² + ε²)^(s/2)`. -/
private def normRegularizedPow (ε s : ℝ) : Space d → ℝ :=
  fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2)

private lemma normRegularizedPow_hasTemperateGrowth {ε s : ℝ} (hε : 0 < ε) :
    HasTemperateGrowth (normRegularizedPow (d := d) ε s) := by
  -- Write `normRegularizedPow` as the composition of three simple functions
  -- to take advantage of `hasTemperateGrowth_one_add_norm_sq_rpow`.
  let f1 := fun (x : ℝ) ↦ (ε ^ 2) ^ (s / 2) * x
  let f2 := fun (x : Space d) ↦ (1 + ‖x‖ ^ 2) ^ (s / 2)
  let f3 := fun (x : Space d) ↦ ε⁻¹ • x

  have h123 : normRegularizedPow (d := d) ε s = f1 ∘ f2 ∘ f3 := by
    unfold normRegularizedPow f1 f2 f3
    ext x
    simp only [Function.comp_apply, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [← Real.mul_rpow (sq_nonneg _) ?_]
    · rw [mul_pow, mul_add, mul_one, ← mul_assoc, inv_pow, sq_abs]
      rw [IsUnit.mul_inv_cancel ?_]
      · rw [one_mul, add_comm]
      · rw [pow_two, isUnit_mul_self_iff, isUnit_iff_ne_zero]
        exact ne_of_gt hε
    · exact add_nonneg (zero_le_one' _) (sq_nonneg _)

  rw [h123]
  fun_prop

/-- The radius operator to power `s`, regularized by `ε ≠ 0`, is the continuous linear map
  from `𝓢(Space d, ℂ)` to itself which maps `ψ` to `(‖x‖² + ε²)^(s/2) • ψ`. -/
def radiusRegPowOperator (ε s : ℝ) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (Complex.ofReal ∘ normRegularizedPow ε s)

@[inherit_doc radiusRegPowOperator]
macro "𝐫[" ε:term "," s:term "]" : term => `(radiusRegPowOperator $ε $s)

lemma radiusRegPowOperator_apply_fun {ε s : ℝ} (hε : 0 < ε) {ψ : 𝓢(Space d, ℂ)} :
    𝐫[ε,s] ψ = fun x ↦ (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  unfold radiusRegPowOperator
  ext x
  rw [smulLeftCLM_apply_apply]
  · unfold normRegularizedPow
    rw [comp_apply, smul_eq_mul, Complex.real_smul]
  · exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth hε)

lemma radiusRegPowOperator_apply {ε s : ℝ} (hε : 0 < ε) {ψ : 𝓢(Space d, ℂ)}
    {x : Space d} : 𝐫[ε,s] ψ x = (‖x‖ ^ 2 + ε ^ 2) ^ (s / 2) • ψ x := by
  rw [radiusRegPowOperator_apply_fun hε]

@[simp]
lemma radiusRegPowOperator_comp_eq {ε s t : ℝ} (hε : 0 < ε) :
    (radiusRegPowOperator (d := d) ε s) ∘L 𝐫[ε,t] = 𝐫[ε,s+t] := by
  unfold radiusRegPowOperator
  ext ψ x
  simp only [ContinuousLinearMap.coe_comp', comp_apply]
  repeat rw [smulLeftCLM_apply_apply ?_]
  · unfold normRegularizedPow
    simp only [comp_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul]
    rw [← Real.rpow_add]
    · congr
      ring
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  repeat exact HasTemperateGrowth.comp (by fun_prop) (normRegularizedPow_hasTemperateGrowth hε)

@[simp]
lemma radiusRegPowOperator_zero {ε : ℝ} (hε : 0 < ε) :
    𝐫[ε,0] = ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  simp [radiusRegPowOperator_apply hε]

lemma positionOperatorSqr_eq {ε : ℝ} (hε : 0 < ε) : ∑ i, 𝐱[i] ∘L 𝐱[i] =
    𝐫[ε,2] - ε ^ 2 • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  ext ψ x
  simp [radiusRegPowOperator_apply hε, Space.norm_sq_eq, ← mul_assoc, ← Finset.sum_mul,
    add_smul, ← pow_two]

/-!
## Unbounded position operators
-/

open SpaceDHilbertSpace UnboundedOperator
open MeasureTheory

/-- The position operators defined on the Schwartz submodule. -/
def positionOperatorSchwartz : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  (schwartzEquiv (d := d)) ∘ₗ 𝐱[i].toLinearMap ∘ₗ (schwartzEquiv (d := d)).symm

lemma positionOperatorSchwartz_isSymmetric : (positionOperatorSchwartz i).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨_, rfl⟩ := schwartzEquiv_exists ψ
  obtain ⟨_, rfl⟩ := schwartzEquiv_exists ψ'
  unfold positionOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, schwartzEquiv_inner]
  congr with x
  simp only [LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe,
    positionOperator_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The symmetric position unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
def positionUnboundedOperator : UnboundedOperator (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (hE := schwartzSubmodule_dense) (positionOperatorSchwartz i)
    (positionOperatorSchwartz_isSymmetric i)

/-- The (regularized) radius operators defined on the Schwartz submodule. -/
def radiusRegPowOperatorSchwartz (ε s : ℝ) : schwartzSubmodule d →ₗ[ℂ] schwartzSubmodule d :=
  (schwartzEquiv (d := d)) ∘ₗ (radiusRegPowOperator (d := d) ε s).toLinearMap ∘ₗ
  (schwartzEquiv (d := d)).symm

lemma radiusRegPowOperatorSchwartz_isSymmetric (ε s : ℝ) (hε : 0 < ε) :
    (radiusRegPowOperatorSchwartz (d := d) ε s).IsSymmetric := by
  intro ψ ψ'
  obtain ⟨_, rfl⟩ := schwartzEquiv_exists ψ
  obtain ⟨_, rfl⟩ := schwartzEquiv_exists ψ'
  unfold radiusRegPowOperatorSchwartz
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply, schwartzEquiv_inner]
  congr with x
  simp only [LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe,
    radiusRegPowOperator_apply hε, Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

/-- The symmetric (regularized) radius unbounded operators with domain the Schwartz submodule
  of the Hilbert space. -/
def radiusRegPowUnboundedOperator (ε s : ℝ) (hε : 0 < ε) :
    UnboundedOperator (SpaceDHilbertSpace d) :=
  UnboundedOperator.ofSymmetric (hE := schwartzSubmodule_dense) (radiusRegPowOperatorSchwartz ε s)
    (radiusRegPowOperatorSchwartz_isSymmetric ε s hε)

end
end QuantumMechanics
