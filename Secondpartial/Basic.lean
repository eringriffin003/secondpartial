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

noncomputable def hessianLinearCompanion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := fun a => {
    toFun := fun b => iteratedFDeriv ℝ 2 f x₀ ![a,b]
                    + iteratedFDeriv ℝ 2 f x₀ ![b,a]
    map_add' := fun b c => by
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      have h₀ := had ![b, a] 0 b c
      have h₁ := had ![a, b] 1 b c
      repeat simp [DM₁] at h₁; simp [DM₀] at h₀
      linarith
    map_smul' := by
      intro m x
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have h₀ := hsm ![x,a] 0 m x
      have h₁ := hsm ![a,x] 1 m x
      repeat rw [DM₀] at h₀; rw [DM₁] at h₁
      simp at h₀ h₁ ⊢
      linarith
  }

noncomputable def hessianBilinearCompanion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)): LinearMap.BilinMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ := {
    toFun := hessianLinearCompanion _ _
    map_add' := fun x y => by
        have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
        ext i
        have had₀ := had ![x,i] 0 x y
        have had₁ := had ![i,i] 1 x y
        repeat rw [DM₀] at had₀
        repeat rw [DM₁] at had₁
        simp [hessianLinearCompanion] at had₀ had₁ ⊢
        linarith
    map_smul' := fun m x => LinearMap.ext_iff.mpr <| fun x₁ => by
        have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
        have hsm₀ := hsm ![x,x₁] 0 m x
        have hsm₁ := hsm ![x₁,x] 1 m x
        repeat rw [DM₀] at hsm₀
        repeat rw [DM₁] at hsm₁
        simp [hessianLinearCompanion] at hsm₀ hsm₁ ⊢
        linarith
}

noncomputable def hessianQuadraticMap {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
  QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ :=
  {
    toFun := fun y => iteratedFDeriv ℝ 2 f x₀ ![y,y]
    exists_companion' := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      use hessianBilinearCompanion f x₀
      intro x y
      have had₀ := had ![x, x + y] 0 x y
      have had₁ := had ![x,x] 1 x y
      have had₂ := had ![y,x] 1 x y
      repeat rw [DM₀] at had₀; rw [DM₁] at had₁ had₂
      simp [hessianLinearCompanion, hessianBilinearCompanion] at had₀ had₁ had₂ ⊢
      linarith
    toFun_smul := by
      have hsm := (iteratedFDeriv ℝ 2 f x₀).map_update_smul'
      have had := (iteratedFDeriv ℝ 2 f x₀).map_update_add'
      intro u v
      have hsm₀ := hsm ![v, v] 0 u v
      have hsm₁ := hsm ![u • v,v] 1 u v
      repeat simp [DM₀] at hsm₀; simp [DM₁] at hsm₁
      rw [smul_eq_mul, mul_assoc, ← hsm₀, hsm₁]
  }

/-- A continuous multilinear map is, in particular, bilinear
in the sense needed to consider the `IsCoercive` proposition. -/
noncomputable def continuousBilinearMap_of_continuousMultilinearMap {n : ℕ}
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ EuclideanSpace ℝ (Fin n)) ℝ) :
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
        cont := Continuous.comp' g.cont <| Continuous.matrixVecCons continuous_const
                <| Continuous.matrixVecCons continuous_id' continuous_const
    }
    map_add' := by
        intro a b
        ext c
        have := g.map_update_add ![a,c] 0 a b
        repeat rw [DM₀] at this
        exact this
    map_smul' := by
        intro c x
        ext y
        have := g.map_update_smul ![x,y] 0 c x
        repeat rw [DM₀] at this
        exact this
    cont := continuous_clm_apply.mpr fun x => Continuous.comp' g.cont
        <| Continuous.matrixVecCons continuous_id' continuous_const
}

theorem second_partial_deriv_test_for_deg_two {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (h : ∀ x, f x = f x₀
                     + inner ℝ (gradient f x₀) (x - x₀)
                  + (1 / 2) * hessianQuadraticMap f x₀ (x - x₀))
    (h₀ : gradient f x₀ = 0) (hQQ : (hessianQuadraticMap f x₀).PosDef) :
    IsLocalMin f x₀ := Filter.eventually_iff_exists_mem.mpr <| by
  use Set.univ
  constructor
  · simp
  · intro y _
    rw [h y, h₀]
    simp
    exact QuadraticMap.PosDef.nonneg hQQ (y - x₀)

noncomputable def higher_taylor_coeff {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :=
    fun x =>
    (1 / Nat.factorial k) * (iteratedFDeriv ℝ k f x₀ fun _ => x - x₀)

noncomputable def higher_taylor {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ := by
    intro x
    let h (i) := higher_taylor_coeff f x₀ i x
    exact ∑ i ∈ Finset.range (k+1), h i

theorem second_partial_deriv_test_for_deg_two' {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (h : ∀ x, f x
      = (1 / Nat.factorial 0) * (iteratedFDeriv ℝ 0 f x₀ fun _ => x - x₀)
      + (1 / Nat.factorial 1) * (iteratedFDeriv ℝ 1 f x₀ fun _ => x - x₀)
      + (1 / Nat.factorial 2) * (iteratedFDeriv ℝ 2 f x₀ fun _ => x - x₀))
    (h₀ : gradient f x₀ = 0) (hQQ : (hessianQuadraticMap f x₀).PosDef) :
    IsLocalMin f x₀ := Filter.eventually_iff_exists_mem.mpr <| by
  use Set.univ
  constructor
  · simp
  · intro y _
    have h : ∀ x, f x
      = (1 / Nat.factorial 0) * iteratedFDeriv ℝ 0 f x₀ ![]
      + (1 / Nat.factorial 1) * (iteratedFDeriv ℝ 1 f x₀ (fun _ => x - x₀))
      + (1 / Nat.factorial 2) * (fun y => iteratedFDeriv ℝ 2 f x₀ ![y, y]) (x - x₀)
                  := by
                  intro x
                  convert h x using 2
                  congr
                  simp
                  congr
                  ext i j
                  fin_cases i <;> simp
    have h : ∀ x, f x = (1 / Nat.factorial 0) * iteratedFDeriv ℝ 0 f x₀ ![]
                  + (1 / Nat.factorial 1) * iteratedFDeriv ℝ 1 f x₀ ![x - x₀]
                  + (1 / Nat.factorial 2) * (fun y => iteratedFDeriv ℝ 2 f x₀ ![y, y]) (x - x₀)
                  := by
                  intro x
                  convert h x using 2
                  congr
                  ext;simp
    have h₁ : inner ℝ (gradient f x₀) (y - x₀) = (fderiv ℝ f x₀) (y - x₀) := by
        unfold gradient
        simp

    have h₂ : (iteratedFDeriv ℝ 1 f x₀) ![y - x₀] = (fderiv ℝ f x₀) (y - x₀) := by
        simp
    have h₃ := Eq.trans h₁ h₂.symm
    have := h y
    rw [← h₃] at this
    simp only [iteratedFDeriv_zero_apply] at this

    rw [h₀] at this
    simp at this
    rw [this]
    simp
    exact QuadraticMap.PosDef.nonneg hQQ (y - x₀)

/-- If a multivariate function equals its second Taylor polynomial
then the second derivative test holds for it.
This includes basic examples in multivariable calculus such as
z = y² - x², z = x² + y² and z = 1 - x² - y² + 7x - 9xy.
-/
theorem second_partial_deriv_test_for_deg_two'' {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (h : f = higher_taylor f x₀ 2)
    (h₀ : gradient f x₀ = 0) (hQQ : (hessianQuadraticMap f x₀).PosDef) :
    IsLocalMin f x₀ := by
    exact @second_partial_deriv_test_for_deg_two' n f x₀ (by
        intro x
        nth_rewrite 1 [h]

        simp [higher_taylor, higher_taylor_coeff]
        rw [Finset.range_succ]
        simp
        rw [Finset.range_succ]
        simp
        suffices (2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) fun i ↦ x - x₀) =
        2⁻¹ * (iteratedFDeriv ℝ 2 f x₀) (Fin.repeat 2 ![x - x₀]) by linarith
        congr
        ext i j
        fin_cases i <;> simp) h₀ hQQ

/-!

# WORK CONTAINING SORRIES

-/

example (a b c d : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 2))
    (h : ∀ x y, f ![x, y] = 0) :
    ∀ x, f x = f x₀ + inner ℝ (gradient f x₀) (x - x₀) + (1 / 2) * hessianQuadraticMap f x₀ (x - x₀)
    := by

    sorry


example (a b c d : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 2))
    (h : ∀ x y, f ![x, y] = a * x ^ 2 + b * x * y + c * y ^ 2 + d) :
    ∀ x, f x = f x₀ + inner ℝ (gradient f x₀) (x - x₀) + (1 / 2) * hessianQuadraticMap f x₀ (x - x₀)
    := by
    sorry

theorem getCoercive {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (C : ContinuousMultilinearMap ℝ (fun i : Fin 2 ↦ EuclideanSpace ℝ (Fin n)) ℝ)
    (Q : QuadraticMap ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
    (hQQ : Q.PosDef) (ε : ℝ) (hε : 0 < ε) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        C) := by
    let D := continuousBilinearMap_of_continuousMultilinearMap
        C
    use ε -- add hypotheses about ε
    constructor
    · exact hε
    · intro u
      unfold continuousBilinearMap_of_continuousMultilinearMap
      unfold QuadraticMap.PosDef  at hQQ
      simp at hQQ ⊢

      sorry

theorem getCoercive' {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x₀ : EuclideanSpace ℝ (Fin n)}
    (hQQ : (hessianQuadraticMap f x₀).PosDef) (ε : ℝ) (hε : 0 < ε) :
    IsCoercive (continuousBilinearMap_of_continuousMultilinearMap
        (iteratedFDeriv ℝ 2 f x₀)) := by
    let C := iteratedFDeriv ℝ 2 f x₀
    use ε -- add hypotheses about ε
    constructor
    · exact hε
    · intro u
      unfold continuousBilinearMap_of_continuousMultilinearMap
      unfold QuadraticMap.PosDef hessianQuadraticMap at hQQ
      simp at hQQ ⊢

      sorry
