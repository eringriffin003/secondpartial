import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Towards a formalization of the Second Partial Derivatives Test

Project members: Asaf, Erin, Janani

 -/

noncomputable def part_deriv_x
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) : ℝ → ℝ → ℝ :=
    fun y => deriv fun x => f ![x, y]

noncomputable def partDeriv_x
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
    fun x => part_deriv_x f (x 0) (x 1)

theorem grad_zero_of_extr (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (a : Fin 2 → ℝ) (h₀ : DifferentiableAt ℝ f a)
    (h : IsLocalExtr f a) : gradient f a =0 := by
    apply HasGradientAt.gradient
    have h₁ := (hasFDerivAt_iff_hasGradientAt).mp
        (DifferentiableAt.hasFDerivAt h₀)
    rw [IsLocalExtr.fderiv_eq_zero h] at h₁
    simp at h₁
    exact h₁

example : fderiv ℝ (fun x : ℝ => x) =
  fun _ => {
    toFun := id
    map_add' := by simp
    map_smul' := by simp
  } := by ext x;simp

noncomputable def hessian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single j 1]

-- Correct, but hard to prove things about?
noncomputable def hessianDet (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) := (hessian f x).det


lemma DM₁ {n:ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
  Function.update ![a,b] 1 c = ![a,c] := by
  ext i j
  fin_cases i <;> simp

lemma DM₀ {n:ℕ} (a b c : EuclideanSpace ℝ (Fin n)) :
  Function.update ![a,b] 0 c = ![c,b] := by
  ext i j
  fin_cases i <;> simp

noncomputable def theFun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x₀ : EuclideanSpace ℝ (Fin n))
    (had :
      ∀ (m : Fin 2 → EuclideanSpace ℝ (Fin n)) (i : Fin 2) (x y : EuclideanSpace ℝ (Fin n)),
      (iteratedFDeriv ℝ 2 f x₀).toFun (Function.update m i (x + y)) =
        (iteratedFDeriv ℝ 2 f x₀).toFun (Function.update m i x) +
          (iteratedFDeriv ℝ 2 f x₀).toFun (Function.update m i y))
    (hsm :
      ∀ (m : Fin 2 → EuclideanSpace ℝ (Fin n)) (i : Fin 2) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      (iteratedFDeriv ℝ 2 f x₀).toFun (Function.update m i (c • x)) =
        c • (iteratedFDeriv ℝ 2 f x₀).toFun (Function.update m i x)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := by
  let T := fun y => iteratedFDeriv ℝ 2 f x₀ y
  intro a
  exact {
    toFun := fun b => T ![a,b] + T ![b,a]
    map_add' := by
        intro b c
        have h1 := had ![a, b] 1 b c
        have h2 := had ![b, a] 0 b c
        repeat rw [DM₁] at h1
        repeat rw [DM₀] at h2
        have : T ![a, b + c] = T ![a, b] + T ![a, c] := h1
        have : T ![b + c, a] = T ![b, a] + T ![c, a] := h2
        linarith
    map_smul' := by
      intro m x
      simp [T]
      have h₀ := hsm ![x,a] 0 m x
      repeat rw [DM₀] at h₀
      simp at h₀
      rw [h₀]
      have := hsm ![a,x] 1 m x
      repeat rw [DM₁] at this
      simp at this
      rw [this]
      linarith
  }

noncomputable def hessianForm {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
  QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
    let g := (iteratedFDeriv ℝ 2 f x₀)
    have hsm :
      ∀ (m : Fin 2 → EuclideanSpace ℝ (Fin n)) (i : Fin 2) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)),
      g.toFun (Function.update m i (c • x)) = c • g.toFun (Function.update m i x) :=
      (iteratedFDeriv ℝ 2 f x₀).map_update_smul'

    have had :
      ∀ (m : Fin 2 → EuclideanSpace ℝ (Fin n)) (i : Fin 2) (x y : EuclideanSpace ℝ (Fin n)),
      g.toFun (Function.update m i (x + y)) = g.toFun (Function.update m i x)
    + g.toFun (Function.update m i y) := (iteratedFDeriv ℝ 2 f x₀).map_update_add'

    let Q₁ := fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y]
    exact {
    toFun := Q₁
    exists_companion' := by
      use {
        toFun := by
          apply theFun <;> tauto
        map_add' := by
          intro x y
          simp
          let g := theFun f x₀ had hsm (x+y)
          simp [theFun]
          ext i
          simp
          have : (iteratedFDeriv ℝ 2 f x₀) ![x + y, i]  =
                 (iteratedFDeriv ℝ 2 f x₀) ![x, i] +
                 (iteratedFDeriv ℝ 2 f x₀) ![y, i] := by
            have had₀ := had ![x,i] 0 x y
            repeat rw [DM₀] at had₀
            simp at had₀
            exact had₀
          have : (iteratedFDeriv ℝ 2 f x₀) ![i, x + y] =
                 (iteratedFDeriv ℝ 2 f x₀) ![i, x] +
                 (iteratedFDeriv ℝ 2 f x₀) ![i, y] := by
            have had₁ := had ![i,i] 1 x y
            repeat rw [DM₁] at had₁
            simp at had₁
            exact had₁
          linarith
        map_smul' := by
          intro m x
          simp
          refine LinearMap.ext_iff.mpr ?_
          intro x₁
          simp
          unfold theFun

          have hsm₀ := hsm ![x,x₁] 0 m x
          repeat rw [DM₀] at hsm₀
          simp at hsm₀
          simp
          rw [hsm₀]
          have hsm₁ := hsm ![x₁,x] 1 m x
          repeat rw [DM₁] at hsm₁
          simp at hsm₁
          rw [hsm₁]
          linarith
      }
      intro x y
      simp [Q₁]
      unfold theFun
      simp
      have had₀ := had ![x, x + y] 0 x y
      repeat rw [DM₀] at had₀
      simp at had₀
      rw [had₀]

      have : (iteratedFDeriv ℝ 2 f x₀) ![x, x + y] =
                (iteratedFDeriv ℝ 2 f x₀) ![x, x] +
                (iteratedFDeriv ℝ 2 f x₀) ![x, y] := by
        have had₁ := had ![x,x] 1 x y
        repeat rw [DM₁] at had₁
        simp at had₁
        exact had₁
      have : (iteratedFDeriv ℝ 2 f x₀) ![y, x + y] =
                (iteratedFDeriv ℝ 2 f x₀) ![y, x] +
                (iteratedFDeriv ℝ 2 f x₀) ![y, y] := by
        have had₁ := had ![y,x] 1 x y
        repeat rw [DM₁] at had₁
        simp at had₁
        exact had₁
      linarith
    toFun_smul := by
      intro u v
      simp [Q₁]
      have hsm₀ := hsm ![v, v] 0 u v
      repeat rw [DM₀] at hsm₀
      simp at hsm₀
      rw [mul_assoc]
      rw [← hsm₀]
      have hsm₁ := hsm ![u • v,v] 1 u v
      repeat rw [DM₁] at hsm₁
      convert hsm₁ using 1
  }

/-- A continuous multilinear map is, in particular, bilinear
in the sense needed to consider the `IsCoercive` proposition. -/
noncomputable def getbilin {n : ℕ} (g : ContinuousMultilinearMap ℝ
    (fun _ : Fin 2 ↦ EuclideanSpace ℝ (Fin n)) ℝ) :
    (EuclideanSpace ℝ (Fin n)) →L[ℝ] (EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ := {
        toFun := fun x => {
            toFun := fun y => g.toFun ![x,y]
            map_add' := by
                intro a b
                have := g.map_update_add ![x,b] 1 a b
                repeat rw [DM₁] at this
                exact this
            map_smul' := by
                intro m a
                have := g.map_update_smul ![x,a] 1 m a
                repeat rw [DM₁] at this
                exact this
            cont := by
                have := g.cont
                refine Continuous.comp' this ?_
                simp
                refine Continuous.matrixVecCons ?_ ?_
                · exact continuous_const
                · refine Continuous.matrixVecCons ?_ ?_
                  · exact continuous_id'
                  · exact continuous_const
        }
        map_add' := by
            intro a b
            ext c
            simp
            have := g.map_update_add ![a,c] 0 a b
            repeat rw [DM₀] at this
            exact this
        map_smul' := by
            intro c x
            ext y
            simp
            have := g.map_update_smul ![x,y] 0 c x
            repeat rw [DM₀] at this
            exact this
        cont := by
            simp
            have := g.cont
            refine continuous_clm_apply.mpr ?_
            intro x
            simp
            refine Continuous.comp' this ?_
            simp
            refine Continuous.matrixVecCons ?_ ?_
            · exact continuous_id'
            · exact continuous_const
    }

theorem second_partial_deriv_test_for_deg_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (h : ∀ x, f x = f x₀ + inner ℝ (gradient f x₀) (x - x₀) + (1 / 2) * hessianForm f x₀ (x - x₀))
    (h₀ : gradient f x₀ = 0) (hQQ : (hessianForm f x₀).PosDef) : IsLocalMin f x₀ := by
  unfold IsLocalMin IsMinFilter
  refine Filter.eventually_iff_exists_mem.mpr ?_
  use Set.univ
  constructor
  · simp
  · intro y _
    rw [h y]
    rw [h₀]
    simp
    exact QuadraticMap.PosDef.nonneg hQQ (y - x₀)

example (a b c d : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 2))
    (h : ∀ x y, f ![x, y] = a * x ^ 2 + b * x * y + c * y ^ 2 + d) :
    ∀ x, f x = f x₀ + inner ℝ (gradient f x₀) (x - x₀) + (1 / 2) * hessianForm f x₀ (x - x₀)
    := sorry

example : MvPolynomial (Fin 2) ℝ := {
    toFun := fun p => by
        let c := p.toFun
        let s := p.support
        -- output: the coefficient of x^c 0 y^c 1
        sorry
    support           := sorry
    mem_support_toFun := sorry
}
