import Convex.Function.Proximal

noncomputable section

open Set InnerProductSpace Topology Filter

--admm解决问题的基本形式
class Opt_problem (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F]
where
   f₁ : E₁ → ℝ
   f₂ : E₂ → ℝ
   A₁ : E₁ →L[ℝ] F
   A₂ : E₂ →L[ℝ] F
   b  : F
   lscf₁ : LowerSemicontinuous f₁
   lscf₂ : LowerSemicontinuous f₂
   cf₁ : ConvexOn ℝ univ f₁
   cf₂ : ConvexOn ℝ univ f₂
   nonempty : ∃ x₁ x₂ ,(A₁ x₁) + (A₂ x₂) - b = 0 ∧ IsMinOn (fun (x₁,x₂) ↦ f₁ x₁ + f₂ x₂) univ (x₁,x₂)

#check Opt_problem.A₂


--admm子问题有唯一解
noncomputable def Admm_sub_Isunique {E : Type*}(f : E → ℝ )(x : E)( _h : IsMinOn f univ x): Prop :=
   ∃ y , IsMinOn f univ y → x = y

#check ContinuousLinearMap
--增广lagrange函数
def Augmented_Lagrangian_Function (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F]
(opt : Opt_problem E₁ E₂ F)(ρ : ℝ): E₁ × E₂ × F → ℝ :=
   fun (x₁ , x₂ , y) =>  (opt.f₁ x₁) + (opt.f₂ x₂) + inner y  ((opt.A₁ x₁) + (opt.A₂ x₂) - opt.b) + ρ / 2 * ‖(opt.A₁ x₁) + (opt.A₂ x₂) - opt.b‖^2

--ADMM的基本迭代格式
class ADMM (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F]
extends (Opt_problem E₁ E₂ F) where
   x₁ : ℕ → E₁
   x₂ : ℕ → E₂
   y  : ℕ → F
   ρ  : ℝ
   τ  : ℝ
   htau  : 0 < τ ∧ τ < ( 1 + √ 5 ) / 2
   itex₁ : ∀ k, IsMinOn (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ , x₂ k , y k)) univ (x₁ ( k + 1 ))
   uitex₁ : ∀ k , Admm_sub_Isunique (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ , x₂ k , y k)) (x₁ ( k + 1 )) (itex₁ k)
   itex₂ : ∀ k, IsMinOn (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ (k+1) , x₂ , y k)) univ (x₂ ( k + 1 ))
   uitex₂ : ∀ k , Admm_sub_Isunique (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ (k+1) , x₂ , y k)) (x₂ ( k + 1 )) (itex₂ k)
   itey : ∀ k, y (k+1) = y k + (τ * ρ) • ((A₁ <| x₁ (k+1)) + (A₂ <| x₂ (k+1)) - b)

--凸的kkt条件
class Convex_KKT {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F]
(x₁ : E₁ )(x₂ : E₂)(y : F) (opt : Opt_problem E₁ E₂ F) :Prop where
   subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
   subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
   eq       :  (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b


variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F]

variable (admm : ADMM E₁ E₂ F)

/-Existence of kkt points in the admm-/
-- def Existence_of_kkt : Prop :=
--    ∃ (x₁:E₁) (x₂:E₂) (y:F) , Convex_KKT x₁ x₂ y admm.toOpt_problem
-- instance : Fact (Existence_of_kkt E₁ E₂ F admm) := {
--    out := by

--       sorry
-- }

class Existance_of_kkt (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F]
(admm : ADMM E₁ E₂ F)
   where
   x₁ : E₁
   x₂ : E₂
   y : F
   h : Convex_KKT x₁ x₂ y admm.toOpt_problem

--证明存在kky条件（由基本格式存在最优解来证明）
instance : Existance_of_kkt E₁ E₂ F admm := {
   x₁ := sorry
   x₂ := sorry
   y := sorry
   h := sorry
}

open ADMM
--收敛的kkt点x₁* ,x₂* ,y*
def ADMM.x₁' {self : ADMM E₁ E₂ F} : E₁ := by
   letI kkt: Existance_of_kkt E₁ E₂ F self := inferInstance
   exact kkt.x₁

def ADMM.x₂' {self : ADMM E₁ E₂ F} : E₂ := by
   letI kkt: Existance_of_kkt E₁ E₂ F self := inferInstance
   exact kkt.x₂

def ADMM.y' {self : ADMM E₁ E₂ F} : F := by
   letI kkt: Existance_of_kkt E₁ E₂ F self := inferInstance
   exact kkt.y

--误差变量
def ADMM.e₁ {self : ADMM E₁ E₂ F} : ℕ → E₁ := fun n => (self.x₁ n) - self.x₁'

def ADMM.e₂ {self : ADMM E₁ E₂ F} : ℕ → E₂ := fun n => (self.x₂ n) - self.x₂'

def ADMM.ey {self : ADMM E₁ E₂ F} : ℕ → F :=  fun n => (self.y n) - self.y'

--辅助变量
--这里定义域需要是非0自然数
def ADMM.u {self : ADMM E₁ E₂ F} : ℕ+ → E₁ := fun n => -(ContinuousLinearMap.adjoint self.A₁)
(self.y n + (( 1 - self.τ) * self.ρ )•(self.A₁ ((self.e₁) n) + self.A₂ ((self.e₂) n)) + self.ρ • (self.A₂ (self.x₂ (n-1) - self.x₂ n)))

def ADMM.v {self : ADMM E₁ E₂ F} : ℕ → E₂ := fun n => -(ContinuousLinearMap.adjoint self.A₂)
(self.y n + (( 1 - self.τ) * self.ρ )•(self.A₁ ((self.e₁) n) + self.A₂ ((self.e₂) n)))

def ADMM.Ψ {self : ADMM E₁ E₂ F} : ℕ → ℝ  := fun n => 1/(self.τ*self.ρ)*‖self.ey n‖^2 + self.ρ*‖self.A₂ (self.e₂ n)‖^2

def ADMM.Φ {self : ADMM E₁ E₂ F} : ℕ → ℝ  := fun n => (self.Ψ n) + ((max (1-self.τ) (1-1/self.τ))*self.ρ) * ‖self.A₁ ((self.e₁) n) + self.A₂ ((self.e₂) n)‖ ^2

def ADMM.υ {self : ADMM E₁ E₂ F} : ℕ → F  := fun n => (self.y n) + ((1 - self.τ) * self.ρ)•(self.A₁ (self.x₁ n) + self.A₂ (self.x₂ n) - self.b)

def ADMM.M {self : ADMM E₁ E₂ F} : ℕ+→ ℝ  := fun n =>  ((1 - self.τ) * self.ρ)* (inner (self.A₂ ((self.x₂ n) - (self.x₂ (n-1)))) (self.A₁ (self.x₁ (n-1)) + self.A₂ (self.x₂ (n-1)) - self.b))

--lyq pyr
--u在次梯度里面
lemma u_inthesubgradient : ∀ n : ℕ+, (admm.u) n ∈ SubderivAt admm.f₁ (admm.x₁ n) := sorry

--v在次梯度里面
lemma v_inthesubgradient : ∀ n : ℕ+ , (admm.v) n ∈ SubderivAt admm.f₂ (admm.x₂ n) := sorry

--lhj mht
--书430 (8.6.42) 第一个等于号
lemma Φ_isdescending_eq1 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b
= (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y n):= sorry

--书430 (8.6.42) 第二个等于号
lemma Φ_isdescending_eq2 : ∀ n , (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y n)
= (1/(admm.τ * admm.ρ)) • (admm.ey (n+1) - admm.ey n):= sorry

--证明化简时候会用
lemma Φ_isdescending_eq3 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b
= Ae1 + admm.A₂ (admm.e₂ (n+1)) := sorry

--lsr gyq
--书430 (8.6.43)
/-
Thereoms

- theorem ContinuousLinearMap.adjoint_inner_left from https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Adjoint.html#ContinuousLinearMap.adjoint
- subgradientAt_mono

-/
--------------- 书430 (8.6.43) ---------------
lemma subgradientAt_mono_u : ∀ n : ℕ+, (0 : ℝ) ≤
   (inner (admm.u (n) + (ContinuousLinearMap.adjoint admm.A₁) admm.y')
          (admm.x₁ (n) - admm.x₁')) := by
   intro n
   -- naming according to the book Pg 63 about monoticity of sub gradient
   let u := admm.u (n)
   let v := - (ContinuousLinearMap.adjoint admm.A₁) admm.y'
   let x := admm.x₁ (n)
   let y := admm.x₁'
   calc
      _= inner (u - v) (x - y) := by
         simp[v]
      _≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply u_inthesubgradient
         letI kkt: Existance_of_kkt E₁ E₂ F admm := inferInstance
         exact kkt.h.subgrad₁
         -- (Convex_KKT admm.x₁' admm.x₂' admm.y').subgrad₁


         -- apply admm.y'.subgrad₁
-- kkt
#check admm.y'.subgrad₁
#check admm.y'
lemma subgradientAt_mono_v : ∀ n, (0 : ℝ) ≤ (inner (admm.v (n + 1) + (ContinuousLinearMap.adjoint admm.A₂) admm.y') (admm.x₂ (n + 1) - admm.x₂')) := sorry

lemma expended_u_gt_zero : ∀ n, (0 : ℝ) ≤ (
   inner
      (
         -admm.ey (n + 1) - ((1-admm.τ) * admm.ρ) • (admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1)))
         - (admm.ρ • (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))))
      )
      (admm.A₁ (admm.e₁ (n + 1)))) := by
   intro n
   -- let A₁ := admm.A₁
   let A₁' := (ContinuousLinearMap.adjoint admm.A₁)
   let Ae1 := admm.A₁ (admm.e₁ (n + 1))
   let e' := admm.e₁ (n + 1)
   -- block is the first part of the inner product
   -- block = u^{k + 1} + A_1^{T}y*
   let block := -admm.ey (n + 1) - ((1-admm.τ) * admm.ρ) • (admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1))) - (admm.ρ • (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))))

   -- u^{k + 1}
   let u' := - A₁' (admm.y (n + 1) + ((1-admm.τ) * admm.ρ) • (admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1)))
         + (admm.ρ • (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1)))))
   let Aty' := A₁' admm.y' -- A_1^T y*
   let x_diff := admm.x₁ (n + 1) - admm.x₁'
   let succ_n := Nat.toPNat' (n + 1)
   calc
      _= inner (𝕜 := ℝ) block Ae1 := by rfl
      _= inner (A₁' block) (e') := by
         rw [ContinuousLinearMap.adjoint_inner_left]
      _= inner (u' + Aty') (x_diff) := by
         let block₁ := admm.y (n + 1) + ((1-admm.τ) * admm.ρ) • (admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1))) + (admm.ρ • (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))))
         let block₂ := admm.y'
         have split_block : -block = block₁ - block₂ := by
            simp[block, block₁, block₂]
            have split_ey :  ey (n + 1) = (admm.y (n + 1)) - admm.y' := by rfl
            rw [split_ey]
            simp
            rw [sub_eq_add_neg]
            rw [neg_sub (admm.y' - admm.y (n + 1))]
            rw [add_comm]
            rw [sub_eq_add_neg, neg_sub]
            rw [add_assoc]
            rw [← smul_add]
            rw [smul_sub]
            -- simp

            let A := ((1 - admm.τ) * admm.ρ) • ((admm.A₁) (admm.e₁ (n + 1)) + (admm.A₂) (admm.e₂ (n + 1)))
            -- let B := ((1 - admm.τ) * admm.ρ) • (admm.A₂) (admm.e₂ (n + 1))
            let C := admm.y (n + 1)
            let D := admm.ρ • ((admm.A₂) (admm.x₂ n))
            let E := admm.ρ • ((admm.A₂) (admm.x₂ (n + 1)))
            change A + (C - y' + (D - E)) = C + A + (D - E) - y'
            -- simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
            rw [← add_assoc]
            rw [sub_eq_add_neg]
            rw [← add_assoc]
            rw [add_comm A C]
            rw [add_assoc]
            rw [add_comm (-y') (D - E)]
            rw [← add_assoc]
            rw [← sub_eq_add_neg]

         rw [← neg_neg block]
         rw [split_block]
         rw [neg_sub]
         rw [A₁'.map_sub]
         have u'_eq : - A₁' block₁ = u' := by
            simp[u']
            rw [← A₁'.map_smul, ← A₁'.map_smul]
            rw [smul_sub]
            rw [← A₁'.map_smul, ← A₁'.map_smul]
            rw [← A₁'.map_sub]
            rw [← A₁'.map_neg, ← A₁'.map_neg, ← A₁'.map_neg, ← A₁'.map_neg, ← A₁'.map_neg]
            rw [← A₁'.map_add, ← A₁'.map_add, ← A₁'.map_add]
            simp[block₁]
            rw [← smul_neg, neg_sub]
            rw [smul_sub]
         have Aty'_eq : A₁' block₂ = Aty' := by
            rfl
         rw [← u'_eq, Aty'_eq, add_comm, sub_eq_add_neg]
         simp[e', x_diff]
         rfl
      _= (inner (admm.u (succ_n) + (ContinuousLinearMap.adjoint admm.A₁) admm.y') (admm.x₁ (succ_n) - admm.x₁')) := by rfl
      _≥ 0 := by
         -- sorry
         apply subgradientAt_mono_u


#check add_assoc

lemma expended_v_gt_zero : ∀ n, (
   inner (
      -admm.ey (n + 1)
      - ((1 - admm.τ) * admm.ρ) •
         ((admm.A₁ (admm.e₁ (n + 1))) + (admm.A₂ (admm.e₂ (n + 1))))
   ) (
      admm.A₂ (admm.e₂ (n + 1))
   )
) ≥ (0 : ℝ) := by
   intro n
   let ey' := admm.ey (n + 1)
   let τ := admm.τ
   let ρ := admm.ρ
   let A₁ := admm.A₁
   let e₁' := admm.e₁ (n + 1)
   let A₂ := admm.A₂
   let e₂' := admm.e₂ (n + 1)
   let A₂' := (ContinuousLinearMap.adjoint admm.A₂)
   let y' := admm.y'
   let y_k_1 := admm.y (n + 1)
   let v_k_1 := admm.v (n + 1)
   let x_diff := admm.x₂ (n + 1) - admm.x₂'
   #check (-ey' - ((1 - τ) * ρ) • (A₁ e₁'+ A₂ e₂'))
   calc
   _ = inner ( -ey'- ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂'))
             (A₂ e₂') := by rfl
   _ = inner (A₂' (-ey'- ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂')))
             (e₂') := by rw [ContinuousLinearMap.adjoint_inner_left]
   _ = inner (-A₂' (ey'+ ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂')))
             (e₂') := by
               rw [sub_eq_add_neg]
               rw [← neg_add]
               rw [A₂'.map_neg]
   _ = inner (-A₂' (y_k_1 - y' + ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂')))
             (e₂') := by
               have sub : ey' = y_k_1 - y' := by
                  simp [ey']
                  simp [y_k_1, y']
                  rfl
               rw [sub]
   _ = inner (-A₂' (y_k_1 + ((1 - τ) * ρ) • (A₁ e₁' + A₂ e₂')) + A₂' y')
             (e₂') := by
               rw [sub_eq_add_neg, add_comm y_k_1, add_assoc]
               rw [A₂'.map_add]
               simp
   _ = inner (v_k_1 + A₂' y') x_diff := by
             rfl
   _ ≥ (0 : ℝ) := by
            apply subgradientAt_mono_v

lemma starRingEnd_eq_R (x : ℝ) : (starRingEnd ℝ) x = x := rfl

lemma expended_u_v_gt_zero : ∀ n , (inner (admm.ey (n + 1)) (-(admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1)))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))‖^2
+ admm.ρ * (inner (-admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))) (admm.A₁ (admm.e₁ (n+1)))) ≥ 0 := by
   -- this proof has no beauty of math, pure shit
   intro n
   #check inner (E:=ℝ)
   #check norm_sq_eq_inner
   -- set local variable to make everything concise
   let A_e_sum := (admm.A₁ (admm.e₁ (n + 1))) + admm.A₂ (admm.e₂ (n + 1))
   -- let Ae1 := admm.A₁ (admm.e₁ (n+1))
   let A_x_sum := -admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))
   let ρ := admm.ρ
   let τ := admm.τ
   let ey := admm.ey
   let ey' := ey (n + 1)

   let Ae1 := admm.A₁ (admm.e₁ (n + 1))
   let Ae2 := admm.A₂ (admm.e₂ (n + 1))
   calc
   _ =
      inner ey' (-(A_e_sum))
      - (1 - τ) * ρ * (inner A_e_sum A_e_sum)
      + ρ * (inner (A_x_sum) (Ae1)) := by
      -- norm_sq_eq_inner will fail to recongnize the type without (𝕜:=ℝ)
         rw [norm_sq_eq_inner (𝕜:=ℝ) (A_e_sum)]
         rfl
   _ =
      inner ey' (-(A_e_sum))
      + inner (- ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum Ae1) := by
         rw [smul_left]
         rw [starRingEnd_eq_R]
         ring
   _ =
      inner (-ey') A_e_sum
      + inner (- ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum Ae1) := by
      -- Ray is angery up to this point cuz who the f**k knows that 𝕜 is not 𝕂? I spent like three hours on fixing this studpid problem!!
         rw [inner_neg_right (𝕜 := ℝ), inner_neg_left (𝕜 := ℝ), inner_neg_left (𝕜 := ℝ)]
   _ =
      inner (-ey' - ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum Ae1) := by
      rw [← add_left]
      ring
      have sub:
         -ey' + (τ * ρ - ρ) • A_e_sum = -ey' - (-(τ * ρ) + ρ) • A_e_sum
         := by
         rw [← sub_eq_zero]
         rw [sub_eq_add_neg]
         rw [sub_eq_add_neg (G := F) (-ey') ((-(τ * ρ) + ρ) • A_e_sum)]
         rw [← neg_one_smul (R := ℝ) (-ey' + -((-(τ * ρ) + ρ) • A_e_sum))]
         rw [smul_add (-1)  (-ey') (-((-(τ * ρ) + ρ) • A_e_sum))]
         rw [neg_smul_neg, neg_smul_neg]
         rw [one_smul, one_smul]
         rw [add_assoc, add_comm, add_assoc]
         rw [add_comm ey' ((-(τ * ρ) + ρ) • A_e_sum)]
         rw [add_assoc]
         rw [add_neg_self, add_zero]
         rw [← add_smul (τ * ρ - ρ) (-(τ * ρ) + ρ) (A_e_sum)]
         rw [add_comm (-(τ * ρ)) ρ, ← add_assoc]
         rw [sub_eq_add_neg, add_assoc (τ * ρ) (-ρ) ρ, add_comm (-ρ) ρ, add_neg_self, add_zero, add_neg_self, zero_smul]
      rw [sub]
   _ =
         inner (-ey' - ((1 - τ) * ρ) • A_e_sum) (Ae1 + Ae2)
      + ρ * (inner A_x_sum Ae1) := by rfl
   _ =
        inner (-ey' - ((1 - τ) * ρ) • A_e_sum) Ae1
      + inner (-ey' - ((1 - τ) * ρ) • A_e_sum) Ae2
      + ρ * (inner A_x_sum Ae1) := by
      rw [inner_add_right]
   _ =
        inner (-ey' - ((1 - τ) * ρ) • A_e_sum) Ae2
      + inner (-ey' - ((1 - τ) * ρ) • A_e_sum + ρ • A_x_sum) Ae1 := by
      rw [inner_add_left]
      rw [add_assoc]
      rw [inner_smul_left A_x_sum Ae1 ρ, starRingEnd_eq_R, add_comm]
      ring
   _ =
      (inner
         (
            -admm.ey (n + 1)
            - ((1 - admm.τ) * admm.ρ) •
               ((admm.A₁ (admm.e₁ (n + 1))) + (admm.A₂ (admm.e₂ (n + 1))))
         )
         (admm.A₂ (admm.e₂ (n + 1)))
      )
      +
      (inner
         (
            -admm.ey (n + 1) - ((1-admm.τ) * admm.ρ) • (admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1)))
            - (admm.ρ • (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))))
         )
         (admm.A₁ (admm.e₁ (n + 1))))

       := by
         have sub : admm.ρ • (admm.A₂ (admm.x₂ (n + 1)) - admm.A₂ (admm.x₂ (n))) = -1 • admm.ρ • (admm.A₂ (admm.x₂ (n)) - admm.A₂ (admm.x₂ (n + 1))) := by
               rw [smul_comm]
               rw [neg_one_smul]
               rw [neg_sub]
         simp[ey', ey, τ, ρ, A_e_sum, Ae2, A_x_sum, Ae1]
         nth_rw 5 [sub_eq_add_neg]
         rw [← neg_one_smul (R := ℝ)
               (
                  ADMM.ρ E₁ E₂ F • ((Opt_problem.A₂ E₁) (x₂ E₁ F n)
                                    - (Opt_problem.A₂ E₁) (x₂ E₁ F (n + 1)))
               )
            ]
         rw [sub]
         simp only [Int.reduceNeg, neg_smul, one_smul]
   _ ≥ 0 := by
      apply add_nonneg
      apply expended_v_gt_zero
      apply expended_u_gt_zero

#check smul_left
lemma Φ_isdescending_inequ1 : ∀ n , 1/(admm.τ*admm.ρ) * (inner (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
-admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) ) ≥ 0:= sorry

---------------    书430 (8.6.43) end    ---------------
--xzx dyx
--书431 第五行
lemma A'υ_inthesubgradient :∀ n , (- (ContinuousLinearMap.adjoint admm.A₂) ((admm.υ) n)) ∈ SubderivAt admm.f₂ (admm.x₂ n):= sorry

--byf hpf
--书431 第六行
lemma Φ_isdescending_inequ2 :∀ n ,
inner
(-((ContinuousLinearMap.adjoint admm.A₂) ((admm.υ (n+1)) - (admm.υ n))))
((admm.x₂ (n+1)) - (admm.x₂ n))
 ≥ (0:ℝ):= sorry

--书431 第9行
lemma Φ_isdescending_inequ3: ∀ n : ℕ+, admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b)) ≤ admm.M (n+1) := sorry


--书431 第12行
lemma Φ_isdescending_inequ4: ∀ n : ℕ+,
1/(admm.τ*admm.ρ) * (inner (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ admm.M (n+1)
-admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) )
≥ 0:= sorry

--书431 (8.6.45)
lemma Φ_isdescending_inequ5: ∀ n : ℕ+,
1/(admm.τ*admm.ρ) * (‖admm.ey n‖^2 - ‖admm.ey (n+1)‖^2)
- (2-admm.τ)*admm.ρ*‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ 2*(admm.M (n+1))
-admm.ρ * ‖admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)‖^2
-admm.ρ * ‖admm.A₂ (admm.e₂ (n+1))‖^2
+admm.ρ * ‖admm.A₂ (admm.e₂ n)‖^2
≥ 0:= sorry

--书432 (8.6.46)
lemma Φ_isdescending_inequ6(htau : 0<admm.τ ∧ admm.τ ≤ 1 ): ∀ n : ℕ+,
1/(admm.τ*admm.ρ) * ‖admm.ey n‖^2 + admm.ρ * ‖admm.A₂ (admm.e₂ n)‖^2
+(1-admm.τ)*admm.ρ * ‖admm.A₁ (admm.e₁ n) + admm.A₂ (admm.e₂ n)‖^2
-(
   1/(admm.τ*admm.ρ) * ‖admm.ey (n+1)‖^2 + admm.ρ * ‖admm.A₂ (admm.e₂ (n+1))‖^2
   +(1-admm.τ)*admm.ρ * ‖admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))‖^2
)
≥ admm.ρ * ‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ admm.τ * admm.ρ * ‖admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)‖^2
:= sorry
--书432 (8.6.47)
lemma Φ_isdescending_inequ7(htau : 1 < admm.τ ): ∀ n : ℕ+,
1/(admm.τ*admm.ρ) * ‖admm.ey n‖^2 + admm.ρ * ‖admm.A₂ (admm.e₂ n)‖^2
+(1-1/admm.τ)*admm.ρ * ‖admm.A₁ (admm.e₁ n) + admm.A₂ (admm.e₂ n)‖^2
-(
   1/(admm.τ*admm.ρ) * ‖admm.ey (n+1)‖^2 + admm.ρ * ‖admm.A₂ (admm.e₂ (n+1))‖^2
   +(1-1/admm.τ)*admm.ρ * ‖admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))‖^2
)
≥ (1+1/admm.τ-admm.τ) * admm.ρ * ‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ (1+admm.τ-admm.τ^2) * admm.ρ * ‖admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)‖^2
:= sorry

--Φ 的下降估计
lemma Φ_isdescending : ∀ n : ℕ , ((admm.Φ) n ) - ((admm.Φ) n+1 ) ≥ (min admm.τ (1 + admm.τ - admm.τ ^ 2) )* admm.ρ * ‖admm.A₂ (admm.x₂ n - admm.x₂ (n+1))‖^2 + (min 1 (1 + 1/admm.τ - admm.τ )) * admm.ρ * ‖admm.A₁ ((admm.e₁) (n+1)) + admm.A₂ ((admm.e₂) (n+1))‖ ^2 :=sorry

section
-- The image of the subgradient is closed
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → ℝ )(lscf: LowerSemicontinuous f)(cf : ConvexOn ℝ univ f)
variable (x' : E)
variable (x : ℕ → E )(x_converage: Tendsto x atTop (𝓝 x'))
variable (g : ℕ → E)( g' : E)
variable (nonempty :  ∀ n ,(g n) ∈ SubderivAt f (x n))(g_coverage : Tendsto g atTop (𝓝 g') )

-- 参考书P64 定理2.19
theorem Image_subgradient_closed : g' ∈ SubderivAt f x' := sorry
end

#check Function.Surjective
--列满秩等价于满射
variable (fullrank₁: Function.Surjective admm.A₁)(fullrank₂: Function.Surjective admm.A₂)


--ADMM收敛定理
theorem ADMM_convergence :  ∃ (x₁':E₁) (x₂':E₂) (y':F) , Convex_KKT x₁' x₂' y' admm.toOpt_problem
∧ ( Tendsto admm.x₁ atTop (𝓝 x₁')∧ Tendsto admm.x₂ atTop (𝓝 x₂')∧ Tendsto admm.y atTop (𝓝 y')) := by sorry
