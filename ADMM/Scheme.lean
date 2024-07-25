import Convex.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section

open Set InnerProductSpace Topology Filter

--admm解决问题的基本形式
class Opt_problem (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F] [FiniteDimensional ℝ F]
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
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F] [FiniteDimensional ℝ F]
(opt : Opt_problem E₁ E₂ F)(ρ : ℝ): E₁ × E₂ × F → ℝ :=
   fun (x₁ , x₂ , y) =>  (opt.f₁ x₁) + (opt.f₂ x₂) + inner y  ((opt.A₁ x₁) + (opt.A₂ x₂) - opt.b) + ρ / 2 * ‖(opt.A₁ x₁) + (opt.A₂ x₂) - opt.b‖^2

--ADMM的基本迭代格式
class ADMM (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F] [FiniteDimensional ℝ F]
extends (Opt_problem E₁ E₂ F) where
   x₁ : ℕ → E₁
   x₂ : ℕ → E₂
   y  : ℕ → F
   ρ  : ℝ
   τ  : ℝ
   hrho : ρ > 0
   htau  : 0 < τ ∧ τ < ( 1 + √ 5 ) / 2
   itex₁ : ∀ k, IsMinOn (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ , x₂ k , y k)) univ (x₁ ( k + 1 ))
   uitex₁ : ∀ k , Admm_sub_Isunique (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ , x₂ k , y k)) (x₁ ( k + 1 )) (itex₁ k)
   itex₂ : ∀ k, IsMinOn (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ (k+1) , x₂ , y k)) univ (x₂ ( k + 1 ))
   uitex₂ : ∀ k , Admm_sub_Isunique (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOpt_problem ρ) (x₁ (k+1) , x₂ , y k)) (x₂ ( k + 1 )) (itex₂ k)
   itey : ∀ k, y (k+1) = y k + (τ * ρ) • ((A₁ <| x₁ (k+1)) + (A₂ <| x₂ (k+1)) - b)

--凸的kkt条件
class Convex_KKT {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F] [FiniteDimensional ℝ F]
(x₁ : E₁ )(x₂ : E₂)(y : F) (opt : Opt_problem E₁ E₂ F) :Prop where
   subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
   subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
   eq       :  (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b


variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F] [FiniteDimensional ℝ F]

variable( admm : ADMM E₁ E₂ F)


class Existance_of_kkt (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [ProperSpace E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂] [ProperSpace E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [CompleteSpace F ] [ProperSpace F] [FiniteDimensional ℝ F]
(admm : ADMM E₁ E₂ F)
   where
   x₁ : E₁
   x₂ : E₂
   y : F
   h : Convex_KKT x₁ x₂ y admm.toOpt_problem

--证明存在kky条件（由基本格式存在最优解来证明）
def ADMM.kkt : Existance_of_kkt E₁ E₂ F admm := {
   x₁ := sorry
   x₂ := sorry
   y := sorry
   h := sorry
}

open ADMM
--收敛的kkt点x₁* ,x₂* ,y*
def ADMM.x₁' {self : ADMM E₁ E₂ F} : E₁ := self.kkt.x₁

def ADMM.x₂' {self : ADMM E₁ E₂ F} : E₂ := self.kkt.x₂

def ADMM.y' {self : ADMM E₁ E₂ F} : F := self.kkt.y

lemma Satisfaction_ofthekkt : Convex_KKT admm.x₁' admm.x₂' admm.y' admm.toOpt_problem := by
   simp [x₁',x₂',y']
   exact admm.kkt.h

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

noncomputable def ADMM.Φ {self : ADMM E₁ E₂ F} : ℕ → ℝ  :=
fun n =>
(self.Ψ n) + ((max (1-self.τ) (1-1/self.τ))*self.ρ) * ‖self.A₁ ((self.e₁) n) + self.A₂ ((self.e₂) n)‖ ^2

def ADMM.υ {self : ADMM E₁ E₂ F} : ℕ → F  := fun n => (self.y n) + ((1 - self.τ) * self.ρ)•(self.A₁ (self.x₁ n) + self.A₂ (self.x₂ n) - self.b)

def ADMM.M {self : ADMM E₁ E₂ F} : ℕ+→ ℝ  := fun n =>  ((1 - self.τ) * self.ρ)* (inner (self.A₂ ((self.x₂ n) - (self.x₂ (n-1)))) (self.A₁ (self.x₁ (n-1)) + self.A₂ (self.x₂ (n-1)) - self.b))

lemma ADMM_iter_process₁ : ∀ n ,
(-(ContinuousLinearMap.adjoint admm.A₁) (admm.y n)
- admm.ρ •
((ContinuousLinearMap.adjoint admm.A₁) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ n) -admm.b)))
∈ SubderivAt admm.f₁ (admm.x₁ (n+1)) := sorry

lemma ADMM_iter_process₂ : ∀ n ,
(-(ContinuousLinearMap.adjoint admm.A₂) (admm.y n)
- admm.ρ •
((ContinuousLinearMap.adjoint admm.A₂) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) -admm.b)))
∈ SubderivAt admm.f₂ (admm.x₂ (n+1)) := sorry

--lyq pyr
--u在次梯度里面
lemma u_inthesubgradient : ∀ n : ℕ+ , (admm.u) n ∈ SubderivAt admm.f₁ (admm.x₁ n) := sorry

--v在次梯度里面
lemma v_inthesubgradient : ∀ n : ℕ+ , (admm.v) n ∈ SubderivAt admm.f₂ (admm.x₂ n) := sorry

--lhj mht
--书430 (8.6.42) 第一个等于号
lemma Φ_isdescending_eq1 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b
= (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y n):= by
   intro n
   rw [admm.itey n,add_comm (admm.y n)] -- , div_eq_mul_inv, one_mul
   simp only [one_div, mul_inv_rev, add_sub_cancel_right]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   rw [inv_mul_cancel, one_mul, inv_mul_cancel, one_smul]
   apply ne_of_gt admm.hrho
   rcases admm.htau with ⟨h₁, _⟩
   apply ne_of_gt h₁


--书430 (8.6.42) 第二个等于号
lemma Φ_isdescending_eq2 : ∀ n , (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y n)
= (1/(admm.τ * admm.ρ)) • (admm.ey (n+1) - admm.ey n):= by
   intro n
   calc
      _ = (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y' + admm.y' - admm.y n) := by rw [sub_add, sub_self, sub_zero]
      _ = (1/(admm.τ * admm.ρ)) • (admm.y (n+1) - admm.y' - (admm.y n - admm.y')) := by simp only [one_div,
        mul_inv_rev, sub_add_cancel, sub_sub_sub_cancel_right]


--证明化简时候会用
lemma Φ_isdescending_eq3 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b
= admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1)) := by
   intro n
   calc
      _ = admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - (admm.A₁ (admm.x₁') + admm.A₂ (admm.x₂')) := by rw [(Satisfaction_ofthekkt admm).eq]
      _ = admm.A₁ (admm.x₁ (n+1)) - admm.A₁ (admm.x₁') + (admm.A₂ (admm.x₂ (n+1)) - admm.A₂ (admm.x₂')) := by
         exact
           add_sub_add_comm ((Opt_problem.A₁ E₂) (x₁ E₂ F (n + 1)))
             ((Opt_problem.A₂ E₁) (x₂ E₁ F (n + 1))) ((Opt_problem.A₁ E₂) x₁')
             ((Opt_problem.A₂ E₁) x₂')
      _ = admm.A₁ ((admm.x₁ (n+1)) - admm.x₁') + admm.A₂ ((admm.x₂ (n+1)) - admm.x₂') := by simp only [map_sub]
      _ = admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1)) := by rw [e₁, e₂]


lemma Φ_isdescending_eq3' : ∀ n : ℕ+ , admm.A₁ (admm.x₁ n) + admm.A₂ (admm.x₂ n) - admm.b
= admm.A₁ (admm.e₁ n) + admm.A₂ (admm.e₂ n) := by
   intro n
   have := Φ_isdescending_eq3 admm n.natPred
   have h: n = n.natPred+1 := by
      simp only [PNat.natPred_add_one]
   rw[← h] at this
   exact this


lemma expended_u_v_gt_zero : ∀ n , (inner (admm.ey (n + 1)) (-((admm.A₁ (admm.e₁ (n + 1))) + admm.A₂ (admm.e₂ (n + 1)))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))‖^2
+ admm.ρ * (inner (-admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))) (admm.A₁ (admm.e₁ (n+1)))) ≥ 0 := sorry

#check neg_sub
#check neg_mul_eq_neg_mul
#check neg_mul_eq_mul_neg
#check inner_add_right
#check inner_sub_right
#check inner_neg_left
#check real_inner_smul_right
#check map_neg
#check neg_sub_left

lemma substitution1 : ∀ n , - admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) ) = admm.ρ * (inner (admm.A₂ (admm.x₂ n - admm.x₂ (n+1))) (admm.A₂ (admm.e₂ (n+1))) ) := by
   intro n
   rw [neg_mul (admm.ρ) (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))))]
   rw [← mul_neg]
   rw [← inner_neg_left (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1)))]
   rw [← map_neg admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)]
   rw [neg_sub (admm.x₂ (n+1)) (admm.x₂ n)]

lemma substitution2 : ∀ n , admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b - admm.A₂ (admm.e₂ (n+1)) = admm.A₁ (admm.e₁ (n+1)) := by
   intro n
   have h := Φ_isdescending_eq3 admm n
   simp [h]

lemma Φ_isdescending_inequ1 : ∀ n , 1/(admm.τ * admm.ρ) * (inner (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))))
- (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2
+ admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
-admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) ) ≥ 0 := by

   let pm1 := 1/(admm.τ * admm.ρ)

   #check (pm1 : ℝ)

   intro n

   have h1:  1/(admm.τ * admm.ρ) * (inner (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))))
      = (inner (admm.ey (n + 1)) (-((admm.A₁ (admm.e₁ (n + 1))) + admm.A₂ (admm.e₂ (n + 1))))) := by
      calc  1/(admm.τ * admm.ρ) * (inner (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))))
         _ = (inner (admm.ey (n+1)) ( pm1 • ((admm.ey n)-(admm.ey (n+1))) )) := by
            rw [← real_inner_smul_right (admm.ey (n+1)) ((admm.ey n)-(admm.ey (n+1))) pm1]
         _ = (inner (admm.ey (n+1)) ( pm1 • -((admm.ey (n+1))-(admm.ey n)) )) := by
            rw [← neg_sub (admm.ey (n+1)) (admm.ey n)]
         _ = (inner (admm.ey (n+1)) ( -(pm1 • ((admm.ey (n+1))-(admm.ey n))) )) := by
            rw [smul_neg]
         _ = (inner (admm.ey (n+1)) ( -(admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b) )) := by
            rw [← Φ_isdescending_eq2, ← Φ_isdescending_eq1]
         _ = (inner (admm.ey (n+1)) (-(admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))))) := by
            rw [Φ_isdescending_eq3]

   have h2:  (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b‖^2 = (1-admm.τ)*admm.ρ*‖admm.A₁ (admm.e₁ (n+1)) + admm.A₂ (admm.e₂ (n+1))‖^2 := by
      rw [Φ_isdescending_eq3]

   have h3: admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b)) -admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) )
   =  admm.ρ * (inner (-admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))) (admm.A₁ (admm.e₁ (n+1)))) := by

      calc admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
         -admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) )

         _ = admm.ρ * (inner (- (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1)))) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
         - admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) ) := by
            rw [← neg_sub (admm.x₂ n) (admm.x₂ (n+1))]
            rw [map_neg admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))]

         _ = - admm.ρ * (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
         - admm.ρ * (inner (admm.A₂ (admm.x₂ (n+1) - admm.x₂ n)) (admm.A₂ (admm.e₂ (n+1))) ) := by
            rw [inner_neg_left (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b)]
            simp

         _ = - admm.ρ * (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))
         + admm.ρ * (inner (admm.A₂ (admm.x₂ n - admm.x₂ (n+1))) (admm.A₂ (admm.e₂ (n+1))) ) := by
            rw [← substitution1 admm]
            simp only [map_sub, neg_mul];rfl

         _ = admm.ρ * (inner (admm.A₂ (admm.x₂ n - admm.x₂ (n+1))) (admm.A₂ (admm.e₂ (n+1))) )
         - admm.ρ * (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b)) := by
            ring

         _ = admm.ρ * (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₂ (admm.e₂ (n+1)) - (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))):= by
            rw [← mul_sub]
            rw [← inner_sub_right (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₂ (admm.e₂ (n+1))) ((admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b))]

         _ = - admm.ρ * (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b - admm.A₂ (admm.e₂ (n+1)))) := by
            rw [← neg_sub (admm.A₁ (admm.x₁ (n+1)) + admm.A₂ (admm.x₂ (n+1)) - admm.b) (admm.A₂ (admm.e₂ (n+1)))]
            rw [inner_neg_right]
            simp only [map_sub, mul_neg, neg_mul]

         _ = - admm.ρ * (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.e₁ (n+1)))) := by
            rw [substitution2]

         _ = admm.ρ * (inner (-admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))) (admm.A₁ (admm.e₁ (n+1)))) := by
            rw [neg_mul (admm.ρ) (inner (admm.A₂ (admm.x₂ (n) - admm.x₂ (n + 1))) (admm.A₁ (admm.e₁ (n+1))))]
            rw [← mul_neg]
            rw [← inner_neg_left (admm.A₂ (admm.x₂ (n) - admm.x₂ (n+1))) (admm.A₁ (admm.e₁ (n+1)))]

   rw [h1, h2]
   rw [h3]
   exact expended_u_v_gt_zero

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
