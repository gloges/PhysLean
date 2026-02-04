/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import PhysLean.QuantumMechanics.DDimensions.Operators.AngularMomentum
/-!

# Commutation relations

-/

namespace QuantumMechanics
noncomputable section
open Constants
open SchwartzMap ContinuousLinearMap

-- TODO: Is there a mathlib way to do this?
def kroneckerDelta {d : ℕ} (i j : Fin d) : ℝ := (if i = j then 1 else 0)

local macro "δ[" i:term "," j:term "]" : term => `(kroneckerDelta $i $j)

lemma kroneckerDelta_symm {d : ℕ} : ∀ (i j : Fin d), δ[i,j] = δ[j,i] := by
  unfold kroneckerDelta
  intro i j
  refine ite_cond_congr ?_
  exact Eq.propIntro Eq.symm Eq.symm

lemma sum_kroneckerDelta [AddCommMonoid M] [Module ℝ M] {d : ℕ} :
    ∀ (f : Fin d → M) (j : Fin d), (∑ (i : Fin d), δ[i,j] • f i = f j) := by
  unfold kroneckerDelta
  intro f j
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma sum_kroneckerDelta' [AddCommMonoid M] [Module ℝ M] {d : ℕ} :
    ∀ (f : Fin d → M) (i : Fin d), (∑ (j : Fin d), δ[i,j] • f j = f i) := by
  unfold kroneckerDelta
  intro f i
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

example (A : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) : ⁅A, A⁆ = 0 := lie_self _
example (A B : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) : -⁅B, A⁆ = ⁅A, B⁆ := lie_skew _ _
example (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
  ⁅A, ⁅B, C⁆⁆ + ⁅B, ⁅C, A⁆⁆ + ⁅C, ⁅A, B⁆⁆ = 0 := lie_jacobi _ _ _

lemma commutator_leibniz_left {d : ℕ} (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A ∘L B, C⁆ = A ∘L ⁅B, C⁆ + ⁅A, C⁆ ∘L B := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel]

lemma commutator_leibniz_right {d : ℕ} (A B C : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :
    ⁅A, B ∘L C⁆ = B ∘L ⁅A, C⁆ + ⁅A, B⁆ ∘L C := by
  dsimp only [Bracket.bracket]
  simp only [ContinuousLinearMap.mul_def, comp_assoc, comp_sub, sub_comp, sub_add_sub_cancel']

/-
## Position / position commutators
-/

/-- `[xᵢ, xⱼ] = 0` -/
lemma position_commutation_position {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐱[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply, positionOperator_apply]
  ring

/-
## Momentum / momentum commutators
-/

/-- `[pᵢ, pⱼ] = 0` -/
lemma momentum_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐩[i], 𝐩[j]⁆ = 0 := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply,
    ContinuousLinearMap.zero_apply, SchwartzMap.zero_apply]
  simp only [momentumOperator_apply_fun]

  rw [Space.deriv_const_smul _ ?_, Space.deriv_const_smul _ ?_]
  rw [Space.deriv_commute _ (ψ.smooth _), sub_self]
  repeat
    refine Space.deriv_differentiable ?_ _
    exact ψ.smooth _

lemma momentum_momentum_eq {d : ℕ} (i j : Fin d) : 𝐩[i] ∘L 𝐩[j] = 𝐩[j] ∘L 𝐩[i] := by
  rw [← sub_eq_zero]
  exact momentum_commutation_momentum i j

/-- `[𝐩², 𝐩ᵢ] = 0` -/
lemma momentumSqr_commutation_momentum {d : ℕ} (i : Fin d) : 𝐩² ∘L 𝐩[i] - 𝐩[i] ∘L 𝐩² = 0 := by
  dsimp only [momentumOperatorSqr]
  simp only [ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum]
  rw [sub_eq_zero]
  congr
  ext j ψ x
  rw [ContinuousLinearMap.comp_assoc]
  rw [momentum_momentum_eq]
  rw [← ContinuousLinearMap.comp_assoc]
  rw [momentum_momentum_eq]
  rfl

/-
## Position / momentum commutators
-/

/-- `[xᵢ, pⱼ] = iℏ δᵢⱼ𝟙` -/
lemma position_commutation_momentum {d : ℕ} (i j : Fin d) : ⁅𝐱[i], 𝐩[j]⁆ =
    (Complex.I * ℏ * δ[i,j]) • ContinuousLinearMap.id ℂ 𝓢(Space d, ℂ) := by
  dsimp only [Bracket.bracket]
  ext ψ x
  simp only [ContinuousLinearMap.smul_apply, SchwartzMap.smul_apply, coe_id', id_eq, smul_eq_mul,
    coe_sub', coe_mul, Pi.sub_apply, Function.comp_apply, SchwartzMap.sub_apply]
  rw [positionOperator_apply, momentumOperator_apply_fun]
  rw [momentumOperator_apply, positionOperator_apply_fun]
  simp only [neg_mul, Pi.smul_apply, smul_eq_mul, mul_neg, sub_neg_eq_add]

  have h : (fun x ↦ ↑(x i) * ψ x) = (fun (x : Space d) ↦ x i) • ψ := rfl
  rw [h]
  rw [Space.deriv_smul (by fun_prop) (SchwartzMap.differentiableAt ψ)]
  rw [Space.deriv_component]
  rw [kroneckerDelta_symm, kroneckerDelta]
  simp only [Complex.real_smul]
  ring

lemma position_position_commutation_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐱[i] ∘L 𝐱[j], 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐱[j] + (Complex.I * ℏ * δ[j,k]) • 𝐱[i] := by
  rw [commutator_leibniz_left]
  rw [position_commutation_momentum, position_commutation_momentum]
  ext ψ x
  simp only [comp_smulₛₗ, RingHom.id_apply, comp_id, smul_comp, id_comp,
    ContinuousLinearMap.add_apply, coe_smul', Pi.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul]
  ring

lemma position_commutation_momentum_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐱[i], 𝐩[j] ∘L 𝐩[k]⁆ =
    (Complex.I * ℏ * δ[i,k]) • 𝐩[j] + (Complex.I * ℏ * δ[i,j]) • 𝐩[k] := by
  rw [commutator_leibniz_right]
  rw [position_commutation_momentum, position_commutation_momentum]
  ext ψ x
  simp only [comp_smulₛₗ, RingHom.id_apply, comp_id, smul_comp, id_comp,
    ContinuousLinearMap.add_apply, coe_smul', Pi.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, smul_eq_mul]

lemma position_commutation_momentumSqr {d : ℕ} (i : Fin d) : ⁅𝐱[i], 𝐩²⁆ =
    (2 * Complex.I * ℏ) • 𝐩[i] := by
  unfold momentumOperatorSqr
  rw [lie_sum]
  conv_lhs =>
    enter [2, i_1]
    rw [commutator_leibniz_right]
    rw [position_commutation_momentum]
    simp only [comp_smulₛₗ, RingHom.id_apply, comp_smul, comp_id, smul_comp, id_comp]
    calc
      _ = (2 * Complex.I * ℏ * δ[i,i_1]) • 𝐩[i_1] := by
        ext ψ x
        simp only [ContinuousLinearMap.add_apply, coe_smul', Pi.smul_apply, SchwartzMap.add_apply,
          SchwartzMap.smul_apply, smul_eq_mul]
        ring
      _ = δ[i,i_1] • ((2 * Complex.I * ℏ) • 𝐩[i_1]) := by
        ext ψ x
        simp only [coe_smul', Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, Complex.real_smul]
        ring
  rw [sum_kroneckerDelta']

/-
## Angular momentum / position commutators
-/

@[sorryful]
lemma angularMomentum_commutation_position {d : ℕ} (i j k : Fin d) : ⁅𝐋[i,j], 𝐱[k]⁆ =
    (Complex.I * ℏ) • ((if i = k then 1 else 0) * 𝐱[j] - (if j = k then 1 else 0) * 𝐱[i]) := by
  sorry

@[sorryful]
lemma angularMomentumSqr_commutation_position {d : ℕ} (i : Fin d) :
    𝐋² ∘L 𝐱[i] - 𝐱[i] ∘L 𝐋² = 0 := by
  sorry

/-
## Angular momentum / momentum commutators
-/

@[sorryful]
lemma angularMomentum_commutation_momentum {d : ℕ} (i j k : Fin d) : ⁅𝐋[i,j], 𝐩[k]⁆ =
    (Complex.I * ℏ) • ((if i = k then 1 else 0) * 𝐩[j] - (if j = k then 1 else 0) * 𝐩[i]) := by
  sorry

/-
## Angular momentum / angular momentum commutators
-/

@[sorryful]
lemma angularMomentum_commutation_angularMomentum {d : ℕ} (i j k l : Fin d) : ⁅𝐋[i,j], 𝐋[k,l]⁆ =
    (Complex.I * ℏ) • ((if i = k then 1 else 0) * 𝐋[j,l]
                      - (if i = l then 1 else 0) * 𝐋[j,k]
                      - (if j = k then 1 else 0) * 𝐋[i,l]
                      + (if j = l then 1 else 0) * 𝐋[i,k]) := by
  sorry

@[sorryful]
lemma angularMomentumSqr_commutation_angularMomentum {d : ℕ} (i j : Fin d) :
    𝐋² ∘L 𝐋[i,j] - 𝐋[i,j] ∘L 𝐋² = 0 := by
  sorry

end
end QuantumMechanics
