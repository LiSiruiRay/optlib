--lsr gyq
--------------- 书430 (8.6.43) Ray---------------
-- TODO: can futher simplify everything.
--A₁†
--A₂†
lemma subgradientAt_mono_u : ∀ n : ℕ+, (0 : ℝ) ≤
   (inner (u (n) + A₁† y')
          (x₁ (n) - x₁')) := by
   intro n
   -- naming according to the book Pg 63 about monoticity of sub gradient
   let u := u (n)
   let v := - A₁† y'
   let x := x₁ (n)
   let y := x₁'
   calc
      _= inner (u - v) (x - y) := by
         simp[v]
      _≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply u_inthesubgradient
         letI kkt: Existance_of_kkt E₁ E₂ F admm := inferInstance
         exact kkt.h.subgrad₁
lemma subgradientAt_mono_v : ∀ n : ℕ+, (0 : ℝ) ≤ (inner (v (n) + A₂† y') (x₂ (n) - x₂')) := by
   intro n
   -- naming according to the book Pg 63 about monoticity of sub gradient
   let u := v (n)
   let v := - A₂† y'
   let x := x₂ (n)
   let y := x₂'
   calc
      _= inner (u - v) (x - y) := by
         simp[v]
      _≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply v_inthesubgradient
         letI kkt: Existance_of_kkt E₁ E₂ F admm := inferInstance
         exact kkt.h.subgrad₂


lemma expended_u_gt_zero : ∀ n, (0 : ℝ) ≤ (
   inner
      (
         -ey (n + 1) - ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
         - (ρ • (A₂ (x₂ (n) - x₂ (n+1))))
      )
      (A₁ (e₁ (n + 1)))) := by
   intro n
   let A₁' := A₁†
   let Ae1 := A₁ (e₁ (n + 1))
   let e' := e₁ (n + 1)
   -- block is the first part of the inner product
   -- block = u^{k + 1} + A_1^{T}y*
   let block := -ey (n + 1) - ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) - (ρ • (A₂ (x₂ (n) - x₂ (n+1))))

   -- u^{k + 1}
   let u' := - A₁' (y (n + 1) + ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
         + (ρ • (A₂ (x₂ (n) - x₂ (n+1)))))
   let Aty' := A₁' y' -- A_1^T y*
   let x_diff := x₁ (n + 1) - x₁'
   let succ_n := Nat.toPNat' (n + 1)
   calc
      _= inner (𝕜 := ℝ) block Ae1 := by rfl
      _= inner (A₁' block) (e') := by
         rw [ContinuousLinearMap.adjoint_inner_left]
      _= inner (u' + Aty') (x_diff) := by
         let block₁ := y (n + 1) + ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) + (ρ • (A₂ (x₂ (n) - x₂ (n+1))))
         let block₂ := y'
         have split_block : -block = block₁ - block₂ := by
            simp[block, block₁, block₂]
            have split_ey :  ey (n + 1) = (y (n + 1)) - y' := by rfl
            rw [split_ey]
            simp
            rw [sub_eq_add_neg]
            rw [neg_sub (y' - y (n + 1))]
            rw [add_comm]
            rw [sub_eq_add_neg, neg_sub]
            rw [add_assoc]
            rw [← smul_add]
            rw [smul_sub]

            let A := ((1 - τ) * ρ) • ((A₁) (e₁ (n + 1)) + (A₂) (e₂ (n + 1)))
            let C := y (n + 1)
            let D := ρ • ((A₂) (x₂ n))
            let E := ρ • ((A₂) (x₂ (n + 1)))
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
      _= (inner (u (succ_n) + A₁† y') (x₁ (succ_n) - x₁')) := by rfl
      _≥ 0 := by
         apply subgradientAt_mono_u



lemma expended_v_gt_zero : ∀ n, (
   inner (
      -ey (n + 1)
      - ((1 - τ) * ρ) •
         ((A₁ (e₁ (n + 1))) + (A₂ (e₂ (n + 1))))
   ) (
      A₂ (e₂ (n + 1))
   )
) ≥ (0 : ℝ) := by
   intro n
   let succ_n := Nat.toPNat' (n + 1)
   let ey' := ey (succ_n)
   let τ := τ
   let ρ := ρ
   let A₁ := A₁
   let e₁' := e₁ (succ_n)
   let A₂ := A₂
   let e₂' := e₂ (succ_n)
   let A₂' := A₂†
   let y' := y'
   let y_k_1 := y (succ_n)
   let v_k_1 := v (succ_n)
   let x_diff := x₂ (succ_n) - x₂'
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

lemma expended_u_v_gt_zero : ∀ n , (inner (ey (n + 1)) (-(A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))))
- (1-τ)*ρ*‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2
+ ρ * (inner (-A₂ (x₂ (n) - x₂ (n + 1))) (A₁ (e₁ (n+1)))) ≥ 0 := by
   -- this proof has no beauty of math, pure shit
   intro n
   #check inner (E:=ℝ)
   #check norm_sq_eq_inner
   -- set local variable to make everything concise
   let A_e_sum := (A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))
   -- let Ae1 := A₁ (e₁ (n+1))
   let A_x_sum := -A₂ (x₂ (n) - x₂ (n + 1))
   let ρ := ρ
   let τ := τ
   let ey := ey
   let ey' := ey (n + 1)

   let Ae1 := A₁ (e₁ (n + 1))
   let Ae2 := A₂ (e₂ (n + 1))
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
            -ey (n + 1)
            - ((1 - τ) * ρ) •
               ((A₁ (e₁ (n + 1))) + (A₂ (e₂ (n + 1))))
         )
         (A₂ (e₂ (n + 1)))
      )
      +
      (inner
         (
            -ey (n + 1) - ((1-τ) * ρ) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
            - (ρ • (A₂ (x₂ (n) - x₂ (n+1))))
         )
         (A₁ (e₁ (n + 1))))

       := by
         have sub : ρ • (A₂ (x₂ (n + 1)) - A₂ (x₂ (n))) = -1 • ρ • (A₂ (x₂ (n)) - A₂ (x₂ (n + 1))) := by
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
