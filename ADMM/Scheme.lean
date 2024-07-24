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
lemma v_inthesubgradient : ∀ n ≥ 1 , (admm.v) n ∈ SubderivAt admm.f₂ (admm.x₂ n) := sorry

--lhj mht
--书430 (8.6.42) 第一个等于号
lemma Φ_isdescending_eq1 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b
= (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y n):= sorry

--书430 (8.6.42) 第二个等于号
lemma Φ_isdescending_eq2 : ∀ n , (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y n)
= (1/(admm.τ * admm.ρ)) • (admm.ey (n+1) - admm.ey n):= sorry

--证明化简时候会用
lemma Φ_isdescending_eq3 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b
= A_e_prod + admm.A₂ (admm.e₂ (n+1)) := sorry

--lsr gyq
--书430 (8.6.43)
/-
Thereoms

- theorem ContinuousLinearMap.adjoint_inner_left from https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Adjoint.html#ContinuousLinearMap.adjoint
- subgradientAt_mono

-/
lemma subgradientAt_mono_u : ∀ n, (inner (admm.u (n + 1) + (ContinuousLinearMap.adjoint admm.A₁) admm.y') (admm.x₁ (n + 1) - admm.x₁')) ≥ (0 : ℝ) := sorry

lemma subgradientAt_mono_v : ∀ n, (inner (admm.v (n + 1) + (ContinuousLinearMap.adjoint admm.A₂) admm.y') (admm.x₂ (n + 1) - admm.x₂')) ≥ (0 : ℝ) := sorry

lemma expended_u_gt_zero : ∀ n, (inner
   (
      -admm.ey (n + 1) - ((1-admm.τ) * admm.ρ) • (admm.A₁ (admm.e₁ (n + 1)) + admm.A₂ (admm.e₂ (n + 1)))
      - (admm.ρ • (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))))
   )
   (admm.A₁ (admm.e₁ (n + 1)))) ≥ (0: ℝ) := sorry

lemma expended_v_gt_zero : ∀ n, (
   inner (
      -admm.ey (n + 1)
      - ((1 - admm.τ) * admm.ρ) •
         ((admm.A₁ (admm.e₁ (n + 1))) + (admm.A₂ (admm.e₂ (n + 1))))
   ) (
      admm.A₂ (admm.e₂ (n + 1))
   )
) ≥ (0 : ℝ) := sorry

lemma starRingEnd_eq_R (x : ℝ) : (starRingEnd ℝ) x = x := rfl

#check starRingEnd_self_apply
#check starRingEnd ℝ

lemma expended_u_v_gt_zero : ∀ n , (inner (admm.ey (n + 1)) (-(admm.A₁ (admm.e₁ (n + 1))) + admm.A₂ (admm.e₂ (n + 1))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))‖^2
+ admm.ρ * (inner (-admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))) (admm.A₁ (admm.e₁ (n+1)))) ≥ 0 := by
   intro n
   #check inner (E:=ℝ)
   #check norm_sq_eq_inner
   -- set local variable to make everything concise
   let A_e_sum := (admm.A₁ (admm.e₁ (n + 1))) + admm.A₂ (admm.e₂ (n + 1))
   let A_e_prod := admm.A₁ (admm.e₁ (n+1))
   let A_x_sum := -admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))
   let ρ := admm.ρ
   let τ := admm.τ
   let ey := admm.ey
   let ey' := ey (n + 1)
   calc
      inner ey' (-(A_e_sum))
      - (1 - τ) * ρ * ‖A_e_sum‖^2
      + ρ * (inner (A_x_sum) (A_e_prod))
      =
      inner ey' (-(A_e_sum))
      - (1 - τ) * ρ * (inner A_e_sum A_e_sum)
      + ρ * (inner (A_x_sum) (A_e_prod)) := by
      -- norm_sq_eq_inner will fail to recongnize the type without (𝕜:=ℝ)
         rw [norm_sq_eq_inner (𝕜:=ℝ) (A_e_sum)]
         rfl
   _ =
      inner ey' (-(A_e_sum))
      + inner (- ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum A_e_prod) := by
         rw [smul_left]
         rw [starRingEnd_eq_R]
         ring
   _ =
      inner (-admm.ey (n + 1)) A_e_sum
      + inner (- ((1 - τ) * ρ) • A_e_sum) A_e_sum
      + ρ * (inner A_x_sum A_e_prod) := by
      -- Ray is angery up to this point cuz who the f**k knows that 𝕜 is not 𝕂? I spent like three hours on fixing this studpid problem!!
         rw [inner_neg_right (𝕜 := ℝ), inner_neg_left (𝕜 := ℝ)]
   _ =

#check neg_one_mul
#check admm.A₁ (admm.e₁ (1))
#check neg_one_smul
#check inner_neg_left

               -- exact

   -- have h₂:

   --    (inner (𝕜:=ℝ) (ey (n + 1)) (-((admm.A₁ (e₁ (n + 1))) + admm.A₂ (e₂ (n + 1)))))
   --    - ((1-admm.τ) * admm.ρ) * inner (𝕜:=ℝ) (admm.A₁ (e₁ (n+1)) + admm.A₂ (e₂ (n+1))) (admm.A₁ (e₁ (n+1)) + admm.A₂ (e₂ (n+1)))
   --    + admm.ρ * (inner (𝕜:=ℝ) (A_x_sum) (admm.A₁ (e₁ (n+1))))
   --    = (inner (𝕜:=ℝ) (ey (n + 1)) (-((admm.A₁ (e₁ (n + 1))) + admm.A₂ (e₂ (n + 1)))))
   --       -  inner (𝕜:=ℝ) ( ((1-admm.τ) * admm.ρ) • admm.A₁ (e₁ (n+1)) + admm.A₂ (e₂ (n+1))) (admm.A₁ (e₁ (n+1)) + admm.A₂ (e₂ (n+1)))
   --       + admm.ρ * (inner (𝕜:=ℝ) (A_x_sum) (admm.A₁ (e₁ (n+1)))) :=
   --       smul_left

#check smul_left
lemma Φ_isdescending_inequ1 : ∀ n , 1/(admm.τ*admm.ρ) * (inner (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
-admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) ) ≥ 0:= sorry

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
