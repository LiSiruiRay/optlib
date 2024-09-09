import Convex.Function.Proximal
import Mathlib.Topology.Instances.EReal

open Set InnerProductSpace Topology Filter

namespace Real_liminf

structure real_liminf where
  x : ℕ → ℝ
  hx : BddBelow (range x)
  hxα : BddAbove (range (fun k => sInf {x n | n ≥ k }))

--有上界的数列满足hxα : inf有上界
section

variable {f : ℕ → ℝ} (hf : BddBelow (range f))

lemma sub_self (f : ℕ → ℝ)(k : ℕ): ∀ n ≥ k , f n ∈ {x | ∃ n ≥ k, f n = x} := by
  intro n hn
  use n

lemma f_sub (k : ℕ) : {y | ∃ n ≥ k, f n = y} ⊆ range f := by
  intro _ hx
  rcases hx with ⟨n , hn⟩
  exact ⟨n , hn.2⟩

lemma f_BddBelow (k : ℕ) : BddBelow {y | ∃ n ≥ k, f n = y} := by
  rcases hf with ⟨w , hw⟩
  exact ⟨w ,mem_of_subset_of_mem (lowerBounds_mono_set $ f_sub k) hw⟩

lemma infle_of_le {y : ℝ} (H : ∀ a ∈ range f, a ≤ y):
∀ k , sInf {x | ∃ n ≥ k, f n = x} ≤ y := by
  intro k
  have hsub : f k ∈ range f :=by use k
  have h : f k ≤ y :=H (f k) hsub
  apply csInf_le_of_le (f_BddBelow hf k) (sub_self f k k (le_refl k)) h

lemma BddAbove_inf_BddAbove (h : BddAbove (range f)):
BddAbove (range fun k ↦ sInf {x | ∃ n ≥ k, f n = x}) := by
  rw[bddAbove_def]
  rw[bddAbove_def] at h
  rcases h with ⟨x , hy⟩
  use x;intro y hy
  dsimp [range] at hy
  rcases hy with ⟨k,hk⟩
  have := infle_of_le hf hy k
  rw[hk] at this
  exact this

end

def bounded_liminf {f : ℕ → ℝ} (hf₁ : BddBelow (range f)) (hf₂ : BddAbove (range f)):
real_liminf where
  x := f
  hx := hf₁
  hxα := BddAbove_inf_BddAbove hf₁ hf₂

noncomputable def real_liminf.α {self : real_liminf} :=
  fun k => sInf {self.x n | n ≥ k }

section

variable {A : real_liminf}
variable(k : ℕ)

lemma A_sub : {y | ∃ n ≥ k, A.x n = y} ⊆ range A.x := by
  intro _ hx
  rcases hx with ⟨n , hn⟩
  exact ⟨n , hn.2⟩

lemma A_BddBelow : BddBelow {y | ∃ n ≥ k, A.x n = y} := by
  rcases A.hx with ⟨w , hw⟩
  exact ⟨w ,mem_of_subset_of_mem (lowerBounds_mono_set $ A_sub k) hw⟩

lemma A_nonempty : {y | ∃ n ≥ k, A.x n = y}.Nonempty:= by
  use A.x k ; use k

lemma A_setisMono {b₁ b₂ : ℕ} (H : b₁ ≤ b₂):
{y | ∃ n ≥ b₂, A.x n = y}  ⊆ {y | ∃ n ≥ b₁, A.x n = y}:= by
  intro _ hx
  rcases hx with ⟨n,hn⟩
  use n ;exact ⟨by linarith,   hn.2⟩

lemma α_isMono : Monotone (A.α):= by
  intro xa b hab
  apply csInf_le_csInf (A_BddBelow xa) (A_nonempty b) (A_setisMono hab)

lemma A_converge : ∃ y , y = (⨆ i, A.α i) ∧ Tendsto A.α atTop (𝓝 y) :=by
  have := tendsto_atTop_ciSup α_isMono A.hxα
  exact ⟨(⨆ i, A.α i) ,rfl , this⟩

variable (A)  in
noncomputable def lim_inf : ℝ :=  Exists.choose (A_converge (A := A))

variable (A)  in
lemma lim_inf_def : Tendsto A.α atTop (𝓝 (lim_inf A)) :=
  (Exists.choose_spec (A_converge (A := A))).2

variable (A)  in
lemma liminf_sup : lim_inf A = iSup A.α :=
  (Exists.choose_spec (A_converge (A := A))).1

end

variable (A)  in
lemma liminf_ge :∀ n , lim_inf A ≥ A.α n := by
  rw[liminf_sup A]
  intro n
  simp only [ge_iff_le]
  apply le_ciSup A.hxα

section

variable {A : real_liminf }{x : ℝ}(H : lim_inf A = x)

lemma succ_ge_zero(k : ℕ) :  1 / k.succ > (0 : ℝ) := by
  simp only [Nat.succ_eq_add_one,Nat.cast_add, Nat.cast_one, one_div, gt_iff_lt, inv_pos]
  linarith


lemma α_Ioc : ∀ k : ℕ , ∃ N ,∀ n ≥ N, (A.α n) ∈ Ioc (x - 1 / k.succ ) x := by
  have := NormedAddCommGroup.tendsto_atTop.1 (lim_inf_def A)
  intro k
  rcases this (1 / k.succ) (succ_ge_zero k) with ⟨N , hN⟩
  use N
  intro n hn
  have := hN n hn
  simp only [Real.norm_eq_abs, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div] at this
  simp[abs] at this
  simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div, mem_Ioc]
  rw[H] at this
  constructor
  · linarith
  · rw[← H]
    apply liminf_ge A n

lemma x_Ioo{ε : ℝ}{k : ℕ}(hε : ε > 0)(h : (A.α k) ∈ Ioc (x - ε) x ) :
∃ n ≥ k , (A.x n) ∈ Ioo (x - ε) (x + ε) :=by
  simp only [mem_Ioc] at h
  simp [real_liminf.α] at h
  simp only [ge_iff_le, mem_Ioo]
  have := (Real.sInf_le_iff (A_BddBelow k) (A_nonempty k)).1 h.2 ε hε
  rcases this with ⟨xn , hxn1 , hxn2⟩
  simp only [ge_iff_le, mem_setOf_eq] at hxn1
  rcases hxn1 with ⟨n , hn⟩
  use n
  rw[← hn.2] at hxn2
  have := csInf_le (A_BddBelow k) (sub_self A.x k n hn.1)
  exact ⟨hn.1, lt_of_lt_of_le h.1 this, hxn2⟩

lemma nat_converge_zero : Tendsto (fun k : ℕ  => 1 / (k.succ : ℝ)) atTop (𝓝 0) := by
  have : (fun k : ℕ  => 1 / (k.succ : ℝ)) = (fun k : ℕ  => 1 / ((k : ℝ) + 1)):=by
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div]
  rw[this]
  apply tendsto_one_div_add_atTop_nhds_zero_nat

lemma α_left_converge: Tendsto (fun k : ℕ => x - 1 / k.succ) atTop (𝓝 x) := by
  nth_rw 2 [← sub_zero x]
  apply Tendsto.const_sub x nat_converge_zero

lemma α_right_converge: Tendsto (fun k : ℕ => x + 1 / k.succ) atTop (𝓝 x) := by
  nth_rw 2 [← add_zero x]
  apply Tendsto.const_add x nat_converge_zero

lemma α_subseq_converge{φ : ℕ → ℝ} (h : ∀ k : ℕ , φ k.succ ∈ Ioo (x - 1 / k.succ) (x + 1 / k.succ)) :
Tendsto φ atTop (𝓝 x) := by
  have α_le : (fun k : ℕ => x - 1 / k.succ ) ≤ (fun k : ℕ =>  φ k.succ ) := by
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div, mem_Ioo] at h
    intro k
    apply le_of_lt (h k).1
  have α_ge : (fun k : ℕ =>  φ k.succ ) ≤ (fun k : ℕ => x + 1 / k.succ)  := by
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, one_div, mem_Ioo] at h
    intro k
    apply le_of_lt (h k).2
  have :=tendsto_of_tendsto_of_tendsto_of_le_of_le α_left_converge α_right_converge α_le α_ge
  rwa[← tendsto_add_atTop_iff_nat 1]

lemma Aφ_n (n :ℕ) (Aφn : ℕ):
∃ m ≥ 1 + Aφn , A.x m ∈ Ioo (x - 1 / n.succ) (x + 1 / n.succ) := by
  obtain h :=α_Ioc (A:=A) (x:=x) H n;
  let N := h.choose
  let hN := h.choose_spec
  let m1 := max (1 + Aφn) N
  have h : m1 ≥ N :=by simp[m1]
  have :=  x_Ioo (succ_ge_zero n) (hN m1 h)
  rcases this with ⟨m , hm⟩
  have h1 : m ≥ 1 + Aφn := by
    apply ge_trans hm.1
    simp[m1]
  use m
  exact ⟨h1 , hm.2⟩

@[simp]
noncomputable def Aφ  : ℕ  → ℕ
  | 0   => 0
  | n + 1 => (Aφ_n (A := A) (x := x) H n (Aφ n)).choose

local notation "A_φ" => Aφ (A := A) (x := x) H

lemma Aφ_sub : ∀ k : ℕ , ( (A.x ∘ A_φ) k.succ) ∈ Ioo (x - 1 / k.succ) (x + 1 / k.succ) := by
  intro k
  have := (Aφ_n (A := A) (x := x) H k (A_φ k)).choose_spec
  have h : (A.x ∘ A_φ) k.succ = A.x (A_φ k.succ):= rfl
  rw[h]
  exact this.2

lemma Aφ_mono : StrictMono  A_φ  := by
  apply strictMono_nat_of_lt_succ
  intro k
  have := (Aφ_n (A := A) (x := x) H k (A_φ k)).choose_spec.1
  rw[ge_iff_le , Nat.one_add_le_iff] at this
  exact this

lemma seq_tendsto_of_liminf :
∃ φ : ℕ → ℕ , StrictMono φ ∧ Tendsto (A.x ∘ φ) atTop (𝓝 x) := by
  use A_φ
  exact ⟨Aφ_mono  (A := A) (x := x) H , α_subseq_converge (Aφ_sub H)⟩

end

--lim_inf 保序
section

variable {A B : real_liminf}
variable (inequ : ∀ n , A.x n ≥ B.x n)

lemma α_inequ''(k : ℕ): ∀ n ≥ k ,B.x n ≥ B.α k := by
  intro n hn
  rw [real_liminf.α]
  apply csInf_le_of_le (A_BddBelow k) (sub_self B.x k n hn)
  simp only [le_refl]

lemma α_inequ' (k : ℕ): ∀ n ≥ k , A.x n ≥ B.α k := by
  intro n hn
  exact ge_trans (inequ n) (α_inequ'' (B:=B) k n hn)

lemma α_inequ : ∀ n , A.α n ≥ B.α n := by
  intro k
  have h := α_inequ' (A:=A) (B:=B)
  rw [real_liminf.α]
  apply le_csInf (a := real_liminf.α k) (A_nonempty k)
  intro b hb
  dsimp at hb
  rcases hb with ⟨n,hn⟩
  have := h inequ k n hn.1
  rw[hn.2] at this
  exact this

variable (A B) in
lemma ge_of_liminf : lim_inf A ≥ lim_inf B := by
  have h1 := lim_inf_def A
  have h2 := lim_inf_def B
  apply le_of_tendsto_of_tendsto' h2 h1 (α_inequ inequ)

end

section

variable {A B : real_liminf}
variable (hAa : BddAbove (range A.x))
variable (hBa : BddAbove (range B.x))

lemma add_BddBelow : BddBelow (range (A.x + B.x)) := BddBelow.range_add A.hx B.hx

lemma add_BddAbove' : BddAbove (range (A.x + B.x)) := BddAbove.range_add hAa hBa

variable (A B) in
def add_real_liminf : real_liminf := bounded_liminf add_BddBelow (add_BddAbove' hAa hBa)

lemma add_eq_add : (add_real_liminf A B hAa hBa).x = A.x + B.x := by
  simp [add_real_liminf,bounded_liminf]

lemma sinf_le_mem (k : ℕ ): ∀ n ≥ k , sInf {x | ∃ n, k ≤ n ∧ A.x n = x} ≤ A.x n := by
  intro n hn
  apply csInf_le
  apply A_BddBelow
  use n

lemma add_le_sinf:  ∀ k , sInf {x | ∃ n, k ≤ n ∧ A.x n = x} + sInf {x | ∃ n, k ≤ n ∧ B.x n = x} ≤
  sInf {x | ∃ n, k ≤ n ∧ (add_real_liminf A B hAa hBa).x n = x} := by
  intro k
  apply le_csInf (A_nonempty (A:=add_real_liminf A B hAa hBa) k)
  intro b hb
  simp only [ge_iff_le, mem_setOf_eq,add_eq_add] at hb
  rcases hb with ⟨n,hn⟩
  rw[← hn.2]
  apply add_le_add
  <;>apply sinf_le_mem ;exact hn.1
  exact hn.1

lemma inf_ge_add : ∀ k , (add_real_liminf A B hAa hBa).α k ≥ A.α k + B.α k :=by
  intro k
  simp[real_liminf.α]
  apply add_le_sinf

lemma tendsto_add : Tendsto (A.α + B.α)  atTop (𝓝 (lim_inf A + lim_inf B)) := by
  have h1 :=lim_inf_def A
  have h2 :=lim_inf_def B
  apply Tendsto.add h1 h2

lemma add_liminf_ge_liminf_add : lim_inf (add_real_liminf A B hAa hBa) ≥ lim_inf A + lim_inf B := by
  have h1 :=lim_inf_def (add_real_liminf A B hAa hBa)
  have h2 := tendsto_add (A:=A) (B:=B)
  apply le_of_tendsto_of_tendsto' h2 h1
  apply inf_ge_add hAa hBa

end

section
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → ℝ )
variable (lscf: LowerSemicontinuous f)(x' : E)
variable (x : ℕ → E )(x_converge: Tendsto x atTop (𝓝 x'))
variable (hfa : BddAbove (range (f ∘ x) ))

lemma point_eventually{b : ℝ}{φ : ℕ → E}(h : ∀ᶠ a in 𝓝 x', f a > b)(hφ : Tendsto φ atTop (𝓝 x')):
∀ᶠ n in atTop, f (φ n) > b := by
  simp only [gt_iff_lt, eventually_atTop, ge_iff_le];
  -- simp only [gt_iff_lt] at h
  rw[Metric.eventually_nhds_iff] at h
  rw[Metric.tendsto_atTop]at hφ
  rcases h with ⟨r, hr ,hy⟩
  rcases hφ r hr with ⟨N , hN⟩
  use N
  intro n hn
  exact hy (hN n hn)

lemma point_tendsto{b : ℝ}(h : ∀ᶠ a in 𝓝 x', f a > b) : ∀ᶠ (a : ℕ) in atTop, (f ∘ x) a ≥ b := by
  have := point_eventually f x' h x_converge
  apply Filter.Eventually.mono this
  intro x1 hx1
  simp only [Function.comp_apply, ge_iff_le]
  linarith

lemma f_IsBoundedUnder : IsBoundedUnder (fun x x_1 ↦ x ≥ x_1) atTop (f ∘ x) := by
  dsimp [IsBoundedUnder , IsBounded ]
  simp only [eventually_map]
  use (f x') - 1
  have : f x' > (f x') - 1 :=by simp only [sub_lt_self_iff, zero_lt_one]
  exact  point_tendsto (E := E) f x' x x_converge (lscf x' ((f x') - 1) this)

def comp_real_liminf : real_liminf :=
bounded_liminf (IsBoundedUnder.bddBelow_range $ f_IsBoundedUnder f lscf x' x x_converge) (hfa)

lemma comp_point_tendsto_eq (φ : ℕ → ℕ)(n : ℕ) :
((comp_real_liminf f lscf x' x x_converge hfa).x ∘ φ) n = f ((x ∘ φ) n) :=rfl

lemma comp_point_tendsto{b : ℝ}{φ : ℕ → ℕ}(h : ∀ᶠ a in 𝓝 x', f a > b)(hφ : StrictMono φ):
∀ᶠ (a : ℕ) in atTop ,((comp_real_liminf f lscf x' x x_converge hfa).x ∘ φ) a > b:=by
  simp only [comp_point_tendsto_eq]
  apply point_eventually f x' h
  apply tendsto_iff_seq_tendsto.1 x_converge
  apply StrictMono.tendsto_atTop hφ

lemma le_liminf_of_lowerSemicontinuous : lim_inf (comp_real_liminf f lscf x' x x_converge hfa) ≥ f x' := by
  by_contra! h
  let subseq := lim_inf (comp_real_liminf f lscf x' x x_converge hfa)
  have : lim_inf (comp_real_liminf f lscf x' x x_converge hfa) =subseq := rfl
  have hsubseq := seq_tendsto_of_liminf this
  rw[this] at h
  have h1 := left_lt_add_div_two.2 h
  have h2 := add_div_two_lt_right.2 h
  let mid := (subseq + f x') / 2;
  rcases hsubseq with ⟨φ , hφ⟩
  have hmid := (tendsto_order.1 hφ.2).2 mid h1
  have hmid':= comp_point_tendsto (E := E) f lscf x' x x_converge hfa (lscf x' mid h2) hφ.1
  obtain hmid'' := Filter.Eventually.and hmid hmid'
  simp only [Function.comp_apply, gt_iff_lt, eventually_atTop, ge_iff_le] at hmid''
  rcases hmid'' with ⟨a ,ha⟩
  obtain hfalse := ha (a + 1) (by linarith)
  linarith

end

--若收敛，则 liminf = lim
section
variable (x' : ℝ )(f : ℕ → ℝ)
variable (x_converge: Tendsto f atTop (𝓝 x'))

lemma f_converge_BddBelow : BddBelow (range f) := Tendsto.bddBelow_range x_converge

lemma f_converge_BddAbove : BddAbove (range f) := Tendsto.bddAbove_range x_converge

def tendsto_real_liminf : real_liminf := {
  x := f
  hx :=f_converge_BddBelow x' f x_converge
  hxα := BddAbove_inf_BddAbove (f_converge_BddBelow x' f x_converge) (Tendsto.bddAbove_range x_converge)
}

lemma liminf_eq :  lim_inf (tendsto_real_liminf x' f x_converge) = x' := by
  let x := lim_inf (tendsto_real_liminf x' f x_converge)
  have h : lim_inf (tendsto_real_liminf x' f x_converge) = x := rfl
  have := seq_tendsto_of_liminf h
  let φ := this.choose
  have hφ := this.choose_spec
  have h1 := (tendsto_iff_seq_tendsto (f := (tendsto_real_liminf x' f x_converge).x) ).1
    x_converge φ (StrictMono.tendsto_atTop hφ.1)
  have h2 := tendsto_nhds_unique hφ.2 h1
  rwa[h]

end

-- liminf x = x
section
variable (x : ℝ)
def fx : ℕ → ℝ := fun _ => x

lemma tendsto_cosnt_real_liminf : Tendsto (fx x) atTop (𝓝 x) := by
  apply tendsto_const_nhds

def const_real_liminf : real_liminf := tendsto_real_liminf
x (fx x) (tendsto_cosnt_real_liminf x)

lemma liminf_const_eq  : lim_inf (const_real_liminf x) = x := by
  apply liminf_eq

end

end Real_liminf
