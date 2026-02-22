/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import PhysLean.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
/-!

# Unbounded operators

-/

namespace QuantumMechanics

noncomputable section

open LinearPMap

-- Nothing here uses any specific properties of this particular Hilbert space
abbrev hilbSp d := SpaceDHilbertSpace d

/-- An `UnboundedOperator` is a linear map from a submodule of the Hilbert space
  to the Hilbert space, assumed to be both densely defined and closable. -/
@[ext]
structure UnboundedOperator (d : ℕ) where
  /-- The LinearPMap defining the unbounded operator. -/
  toLinearPMap : LinearPMap ℂ (hilbSp d) (hilbSp d)
  /-- The domain of the unbounded operator is dense in the Hilbert space. -/
  dense_domain : Dense (toLinearPMap.domain : Set (hilbSp d))
  /-- The unbounded operator is closable. -/
  is_closable : toLinearPMap.IsClosable

namespace UnboundedOperator

variable {d : ℕ} (U : UnboundedOperator d)

/-- Domain of `UnboundedOperator`. -/
def domain : Submodule ℂ (hilbSp d) := U.toLinearPMap.domain

/-- `UnboundedOperator` as a function. -/
@[coe]
def toFun : U.domain → (hilbSp d) := U.toLinearPMap.toFun

instance : CoeFun (UnboundedOperator d)
  (fun U : UnboundedOperator d ↦ U.domain → (hilbSp d)) := ⟨toFun⟩

@[simp]
lemma toFun_eq_coe (x : U.domain) : U.toFun x = U.toLinearPMap.toFun x := rfl

/-!
## Construction of unbounded operators
-/

variable
  {E : Submodule ℂ (hilbSp d)}
  {hE : Dense (E : Set (hilbSp d))}

/-- An `UnboundedOperator` constructed from a symmetric linear map on a dense submodule `E`. -/
def ofSymmetric (f : E →ₗ[ℂ] E) (hf : f.IsSymmetric) : UnboundedOperator d where
  toLinearPMap := LinearPMap.mk E (E.subtype ∘ₗ f)
  dense_domain := hE
  is_closable := by
    -- TODO: symmetric ∧ dense ⇒ closable
    unfold Dense at hE
    unfold LinearMap.IsSymmetric at hf
    sorry

@[simp]
lemma ofSymmetric_apply {f : E →ₗ[ℂ] E} {hf : f.IsSymmetric} (ψ : E) :
  (ofSymmetric (hE := hE) f hf).toLinearPMap ψ = E.subtypeL (f ψ) := rfl

/-!
## Closure
-/

/-- The closure of an unbounded operator. -/
def closure : UnboundedOperator d where
  toLinearPMap := U.toLinearPMap.closure
  dense_domain := by
    refine Dense.mono ?_ U.dense_domain
    exact HasCore.le_domain (closureHasCore U.toLinearPMap)
  is_closable := IsClosed.isClosable (IsClosable.closure_isClosed U.is_closable)

lemma closure_toLinearPMap : U.closure.toLinearPMap = U.toLinearPMap.closure := rfl

def IsClosed : Prop := U.toLinearPMap.IsClosed

lemma closure_isClosed : U.closure.IsClosed := IsClosable.closure_isClosed U.is_closable

/-!
## Adjoints
-/

/-- The adjoint of an unbounded operator, denoted as `U†`. -/
def adjoint : UnboundedOperator d where
  toLinearPMap := U.toLinearPMap.adjoint
  dense_domain := by sorry
  is_closable := IsClosed.isClosable (adjoint_isClosed U.dense_domain)

@[inherit_doc]
scoped postfix:1024 "†" => UnboundedOperator.adjoint

instance instStar : Star (UnboundedOperator d) where
  star := fun U ↦ U.adjoint

lemma adjoint_toLinearPMap : U†.toLinearPMap = U.toLinearPMap† := rfl

lemma isSelfAdjoint_def : IsSelfAdjoint U ↔ U† = U := Iff.rfl

lemma isSelfAdjoint_iff : IsSelfAdjoint U ↔ IsSelfAdjoint U.toLinearPMap := by
  rw [isSelfAdjoint_def, LinearPMap.isSelfAdjoint_def]
  constructor <;> intro h
  · rw [← adjoint_toLinearPMap, h]
  · rwa [UnboundedOperator.ext_iff, adjoint_toLinearPMap]

lemma adjoint_isClosed : (U†).IsClosed := LinearPMap.adjoint_isClosed U.dense_domain

/-- `hilbSp × hilbSp` with inner product `⟪(f0, f1), (g0, g1)⟫ ≔ ⟪f0, g0⟫ + ⟪f1, g1⟫`
  and induced norm `‖(f0, f1)‖² = ‖f0‖² + ‖f1‖²` (by default `H × H` is given the norm
  `‖(f0, f1)‖ = max { ‖f0‖, ‖f1‖ }`) -/
abbrev hilbSp2 (d : ℕ) := WithLp 2 (hilbSp d × hilbSp d)

def submoduleToLp (E : Submodule ℂ (hilbSp d × hilbSp d)) : Submodule ℂ (hilbSp2 d) where
  carrier := {x | x.ofLp ∈ E}
  add_mem' := by
    intro a b ha hb
    exact Submodule.add_mem E ha hb
  zero_mem' := Submodule.zero_mem E
  smul_mem' := by
    intro c x hx
    exact Submodule.smul_mem E c hx

lemma submoduleToLp_closure (E : Submodule ℂ (hilbSp d × hilbSp d)) :
    (submoduleToLp E.closure) = (submoduleToLp E).topologicalClosure := by
  rw [Submodule.ext_iff]
  simp [← Submodule.mem_closure_iff] -- Is this needed?
  intro x
  -- TODO: `toLp E.closure = (toLp E).closure`
  -- This is nontrivial:
  -- In `submoduleToLp E.closure` the closure is wrt the sup norm (by default `H × H` is equipped
  --   with a norm defined as the supremum of the norms of their components).
  -- In `(submoduleToLp E).closure` the closure is wrt the L² norm introduced above.
  -- Need to use that `Lp` norms induce the same topology in two dimensions (two copies of `H`).
  sorry

lemma mem_submodule_iff_mem_submoduleToLp (E : Submodule ℂ (hilbSp d × hilbSp d)) :
    ∀ f, f ∈ E ↔ (WithLp.toLp 2 f) ∈ submoduleToLp E := fun _ => Eq.to_iff rfl

lemma mem_submodule_closure_iff_mem_submoduleToLp_closure (E : Submodule ℂ (hilbSp d × hilbSp d)) :
    ∀ f, f ∈ E.topologicalClosure ↔ (WithLp.toLp 2 f) ∈ (submoduleToLp E).topologicalClosure := by
  intro f
  rw [← submoduleToLp_closure]
  rfl

lemma mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal
    (E : Submodule ℂ (hilbSp d × hilbSp d)) :
    ∀ f, f ∈ E.adjoint ↔ WithLp.toLp 2 (f.2, -f.1) ∈ (submoduleToLp E)ᗮ := by
  intro f
  constructor <;> intro h
  · rw [Submodule.mem_orthogonal]
    intro u hu
    rw [Submodule.mem_adjoint_iff] at h
    have h' : inner ℂ u.snd f.1 = inner ℂ u.fst f.2 := by
      rw [← sub_eq_zero]
      exact h u.fst u.snd hu
    simp [h']
  · rw [Submodule.mem_adjoint_iff]
    intro a b hab
    rw [Submodule.mem_orthogonal] at h
    have hab' : (WithLp.toLp 2 (a, b)) ∈ submoduleToLp E := by
      exact (mem_submodule_iff_mem_submoduleToLp E (a, b)).mp hab
    have h' : inner ℂ a f.2 = inner ℂ b f.1 := by
      rw [← sub_eq_zero, sub_eq_add_neg, ← inner_neg_right]
      exact h (WithLp.toLp 2 (a, b)) hab'
    simp [h']

lemma mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal
    (E: Submodule ℂ (hilbSp d × hilbSp d)):
    ∀ f, f ∈ E.adjoint.adjoint ↔ WithLp.toLp 2 f ∈ (submoduleToLp E)ᗮᗮ := by
  intro f
  simp only [Submodule.mem_adjoint_iff]
  trans ∀ v, (∀ w ∈ submoduleToLp E, inner ℂ w v = 0) → inner ℂ v (WithLp.toLp 2 f) = 0
  · constructor <;> intro h
    · intro v hw
      have h' := h (-v.snd) v.fst
      rw [inner_neg_left, sub_neg_eq_add] at h'
      apply h'
      intro a b hab
      rw [inner_neg_right, neg_sub_left, neg_eq_zero]
      exact hw (WithLp.toLp 2 (a, b)) ((mem_submodule_iff_mem_submoduleToLp E (a, b)).mp hab)
    · intro a b h'
      rw [sub_eq_add_neg, ← inner_neg_left]
      apply h (WithLp.toLp 2 (b, -a))
      intro w hw
      have hw' := h' w.fst w.snd hw
      rw [sub_eq_zero] at hw'
      simp [hw']
  simp only [← Submodule.mem_orthogonal]

lemma mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal
    (E : Submodule ℂ (hilbSp d × hilbSp d)) :
    ∀ f, f ∈ E.closure.adjoint ↔ WithLp.toLp 2 (f.2, -f.1) ∈ (submoduleToLp E).closureᗮ := by
  intro f
  trans (WithLp.toLp 2 (f.2, -f.1)) ∈ (submoduleToLp E.closure)ᗮ
  · apply mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal E.closure f
  rw [submoduleToLp_closure]
  simp [← ClosedSubmodule.mem_toSubmodule_iff]

lemma closure_adjoint_eq_adjoint : U.closure† = U† := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.closure.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]

  ext f
  trans WithLp.toLp 2 (f.2, -f.1) ∈ (submoduleToLp U.toLinearPMap.graph).topologicalClosureᗮ
  · exact mem_submodule_closure_adjoint_iff_mem_submoduleToLp_closure_orthogonal _ _
  rw [Submodule.orthogonal_closure]
  exact Iff.symm (mem_submodule_adjoint_iff_mem_submoduleToLp_orthogonal _ _)

lemma adjoint_adjoint_eq_closure : U†† = U.closure := by
  -- Reduce to statement about graphs using density and closability assumptions
  apply UnboundedOperator.ext
  apply LinearPMap.eq_of_eq_graph
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U†.dense_domain]
  rw [adjoint_toLinearPMap, adjoint_graph_eq_graph_adjoint U.dense_domain]
  rw [closure_toLinearPMap, ← IsClosable.graph_closure_eq_closure_graph U.is_closable]

  ext f
  trans WithLp.toLp 2 f ∈ (submoduleToLp U.toLinearPMap.graph)ᗮᗮ
  · exact mem_submodule_adjoint_adjoint_iff_mem_submoduleToLp_orthogonal_orthogonal _ _
  rw [Submodule.orthogonal_orthogonal_eq_closure]
  rw [mem_submodule_closure_iff_mem_submoduleToLp_closure]

/-!
## Generalized eigenvectors
-/

/-- A map `F : D(U) →L[ℂ] ℂ` is a generalized eigenvector of an unbounded operator `U`
  if there is an eigenvalue `c` such that for all `ψ ∈ D(U)`, `F (U ψ) = c ⬝ F ψ`. -/
def IsGeneralizedEigenvector (F : U.domain →L[ℂ] ℂ) (c : ℂ) : Prop :=
  ∀ ψ : U.domain, ∃ ψ' : U.domain, ψ' = U ψ ∧ F ψ' = c • F ψ

lemma isGeneralizedEigenvector_ofSymmetric_iff
    {f : E →ₗ[ℂ] E} {hf : f.IsSymmetric} (F : E →L[ℂ] ℂ) (c : ℂ) :
    IsGeneralizedEigenvector (ofSymmetric (hE := hE) f hf) F c ↔ ∀ ψ : E, F (f ψ) = c • F ψ := by
  constructor <;> intro h ψ
  · obtain ⟨ψ', hψ', hψ''⟩ := h ψ
    apply SetLike.coe_eq_coe.mp at hψ'
    subst hψ'
    exact hψ''
  · use f ψ
    exact ⟨by simp, h ψ⟩

end UnboundedOperator

end
end QuantumMechanics
