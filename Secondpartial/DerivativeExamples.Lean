import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
-- import Mathlib.Analysis.Calculus.Fderiv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

import Mathlib.Topology.Order.OrderClosedExtr
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Interval.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Towards a formalization of the Second Partial Derivatives Test

Project members: Asaf, Erin, Janani

 -/


-- Frechet derivative of x ↦ x^2.
example : fderiv ℝ (fun x : ℝ => x*x) =
  fun x => {
    toFun := fun h => 2*h*x
    map_add' := by
      intro x y
      ring
    map_smul' := by
      intro x y
      dsimp
      ring } := by
    ext x
    simp
    ring

-- Frechet Derivative of (x,y) ↦ x^2+y^2.

example : fderiv ℝ (fun p : ℝ × ℝ => p.1^2 + p.2^2) =
  fun p => {
    toFun := fun h => 2*h.1*p.1 + 2 * h.2 * p.2
    map_add' := by
      intro x y
      dsimp
      ring
    map_smul' := by
      intro x y
      dsimp
      ring
  } := by
    ext p
    · rw [fderiv_add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)]
      simp
      rw [show  (fun p : ℝ × ℝ  ↦ p.1 ^ 2)  = (fun u ↦ u^2) ∘ (fun p ↦ p.1) by ext p; simp]
      rw [show (fun p : ℝ × ℝ  ↦ p.2 ^ 2)  = (fun u ↦ u^2) ∘ (fun p ↦ p.2) by ext p; simp]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_fst)]
      rw [ContinuousLinearMap.comp_apply]
      rw [show (fderiv ℝ (fun p : ℝ × ℝ ↦ p.1) p) (1, 0) = 1 by simp [fderiv_fst]]
      rw [show (∀ h, (fderiv ℝ (fun u ↦ u ^ 2) (p.1 : ℝ)) h = 2 * p.1 * h) by intro h; simp; ring]
      simp
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_snd)]
      rw [ContinuousLinearMap.comp_apply]
      rw [show (fderiv ℝ (fun p : ℝ × ℝ ↦ p.2) p) (1, 0) = 0 by simp [fderiv_snd]]
      exact ContinuousLinearMap.map_zero (fderiv ℝ (fun u ↦ u ^ 2) p.2)
    · simp
      rw [fderiv_add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)]
      simp
      rw [show  (fun p : ℝ × ℝ  ↦ p.1 ^ 2)  = (fun u ↦ u^2) ∘ (fun p ↦ p.1) by ext p; simp]
      rw [show (fun p : ℝ × ℝ  ↦ p.2 ^ 2)  = (fun u ↦ u^2) ∘ (fun p ↦ p.2) by ext p; simp]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_fst)]
      rw [ContinuousLinearMap.comp_apply]
      rw [show (fderiv ℝ (fun p : ℝ × ℝ ↦ p.1) p) (0, 1) = 0 by simp [fderiv_fst]]
      rw [show  ∀ h, (fderiv ℝ (fun u ↦ u ^ 2) (p.1 : ℝ)) h = 2 * p.1 * h by intro h; simp; ring]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_snd)]
      rw [ContinuousLinearMap.comp_apply]
      rw [show (fderiv ℝ (fun p : ℝ × ℝ ↦ p.2) p) (0, 1) = 1 by simp [fderiv_snd]]
      rw [show ∀ h, (fderiv ℝ (fun u ↦ u ^ 2) (p.2 : ℝ)) h = 2 * p.2 * h by intro h; simp; ring]
      ring


-- Same example (x,y) ↦ x^2+y^2, but including some notations and simplifications.
notation "D" => fderiv ℝ

example : D (fun p : ℝ × ℝ => p.1^2 + p.2^2) =
  fun p => {
    toFun := fun h => 2*h.1*p.1 + 2 * h.2 * p.2
    map_add' := by
      intro x y
      dsimp
      ring
    map_smul' := by
      intro x y
      dsimp
      ring
  } := by
    ext p
    · rw [fderiv_add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)]
      simp
      set f := fun p : ℝ × ℝ => p.1^2 + p.2^2
      set f₁ := fun p : ℝ × ℝ  ↦ p.1^2
      set f₂ := fun p : ℝ × ℝ  ↦ p.2^2
      set π₁ := fun p : ℝ × ℝ  ↦ p.1
      set π₂ := fun p : ℝ × ℝ  ↦ p.2
      set g := fun (u: ℝ) ↦ u^2
      rw [show  f₁  = g ∘ π₁ by exact rfl, show f₂  = g ∘ π₂ by exact rfl]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_fst)]
      simp
      rw [show (D π₁ p) (1, 0) = 1 by simp [π₁,fderiv_fst]]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_snd)]
      simp
      rw [show (D π₂ p) (1, 0) = 0 by simp [π₂, fderiv_snd]]
      ring
    · simp
      rw [fderiv_add (differentiableAt_fst.pow _) (differentiableAt_snd.pow _)]
      set f := fun p : ℝ × ℝ => p.1^2 + p.2^2
      set f₁ := fun p : ℝ × ℝ  ↦ p.1^2
      set f₂ := fun p : ℝ × ℝ  ↦ p.2^2
      set π₁ := fun p : ℝ × ℝ  ↦ p.1
      set π₂ := fun p : ℝ × ℝ  ↦ p.2
      set g := fun (u: ℝ) ↦ u^2
      rw [show  f₁  = g ∘ π₁ by exact rfl, show f₂  = g ∘ π₂ by exact rfl]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_fst)]
      simp
      rw [show (D π₁ p) (0, 1) = 0 by simp [π₁, fderiv_fst]]
      rw [fderiv_comp _ (differentiableAt_pow 2) (differentiableAt_snd)]
      simp
      rw [show (D π₂ p) (0, 1) = 1 by simp [π₂, fderiv_snd]]
      ring

-- Frechet derivative of (x,y) ↦ x*y.
example : D (fun p : ℝ × ℝ => p.1 * p.2) =
  fun p => {
    toFun := fun h => h.1*p.2 + h.2 * p.1
    map_add' := by
      intro x y
      dsimp
      ring
    map_smul' := by
      intro x y
      dsimp
      ring
  } := by
    ext p
    · simp
      rw [fderiv_mul (differentiableAt_fst) (differentiableAt_snd)]
      simp
      rw [show (D Prod.snd p) (1, 0) = 0 by simp [fderiv_snd]]
      rw [show (D Prod.fst p) (1, 0) = 1 by simp [fderiv_fst]]
      ring
    · simp
      rw [fderiv_mul (differentiableAt_fst) (differentiableAt_snd)]
      simp
      rw [show (D Prod.snd p) (0, 1) = 1 by simp [fderiv_snd]]
      rw [show (D Prod.fst p) (0, 1) = 0 by simp [fderiv_fst]]
      ring
