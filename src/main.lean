import tactic
import data.real.basic
import data.set


noncomputable theory

variable X : Type
variable d : X → X → ℝ


def dist_refl := ∀(x y: X), d x y = 0 ↔ x = y
def dist_symm := ∀(x y : X), d x y = d y x
def dist_triangle := ∀(x y z : X), d x y ≤  d x z + d z y

def is_metric_space := 
dist_refl X d ∧ dist_symm X d ∧ dist_triangle X d 


def dist_real : ℝ → ℝ → ℝ := λ (a b : ℝ), |a - b|

lemma dist_real_to_zero : ∀(x : ℝ), dist_real x 0 = |x| :=
begin 
  intro x,
  unfold dist_real,
  rw sub_zero x,
end

lemma real_is_metric_space : is_metric_space ℝ dist_real := 
begin
  split,
  {
  intros x y,
  unfold dist_real,

  simp only [abs_eq_zero],
  exact sub_eq_zero,
  },

  split,
  {
  intros x y,
  exact abs_sub_comm x y,
  },

  intros x y z,
  exact abs_sub_le x z y,
end

constant hX : is_metric_space X d

lemma dist_nonneg : 
∀(x y : X), d x y  ≥ 0 := 
begin 
  intros x y,
  have h1 := (hX X d).right.right x x y,
  have h2 := ((hX X d).left x x).mpr (by refl),
  rw h2 at h1,
  rw ← (hX X d).right.left x y at h1,
  linarith,
end

lemma abs_of_dist (x y : X) : |d x y| = d x y :=
abs_eq_self.mpr (dist_nonneg X d x y)

def is_cauchy (a : ℕ → X)
:= ∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n m : ℕ)(hn: n ≥ N)
(hm: m ≥ N), d (a n) (a m)  < ε


def seq_lim (a : ℕ → X) (L : X) :=
∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n : ℕ)(hn: n ≥ N),
d (a n) L < ε

def seq_lim2 (a : ℕ → X) (L : X) :=
seq_lim ℝ dist_real (λ(n : ℕ), d (a n) L) 0

lemma seq_lim_defs (a : ℕ → X) (L : X) :
seq_lim X d a L ↔ seq_lim2 X d a L :=
begin 
  split,
  {
    intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    rw dist_real_to_zero,
    rw abs_of_dist X d,
    exact hN n hn,
  },
  {
    intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    rw dist_real_to_zero at hN,
    rw abs_of_dist X d at hN,
    exact hN,
  },
end

lemma lim_of_mult_const_seq (x : ℕ → ℝ) (L : ℝ) 
(hx : seq_lim ℝ dist_real x L) (k : ℝ) : seq_lim ℝ dist_real (λn, k * (x n)) (k*L) :=
begin 
  intros ε hε,
    by_cases |k| = 0,
    {
    use 0,
    intros n hn,
    have : k = 0 := abs_eq_zero.mp h,
    rw this,
    change (λ (n : ℕ), 0 * x n) n with 0 * x n,
    rw zero_mul (x n),
    rw zero_mul L,
    have : dist_real 0 0 = |(0:ℝ)-(0:ℝ)| := by refl,
    rw this,
    have : (0:ℝ)-(0:ℝ)=0 := sub_zero 0,
    rw this,
    rw abs_zero,
    exact hε,
  },
  {
   have hk_pos : |k| > 0 := (ne.symm h).le_iff_lt.mp (abs_nonneg k), 
   cases hx (ε/|k|) (div_pos hε hk_pos) with N hN,
   use N,
   intros n hn,
   change |k * (x n) - (k * L)| < ε,
   ring_nf,
   rw abs_mul (x n - L) k,
   rw (lt_div_iff hk_pos).symm,
   exact hN n hn,
  },
  

end

def seq_converges (a : ℕ → X) :=
∃(L : X), seq_lim X d a L

def is_complete : Prop := ∀(x : ℕ → X)(hx : is_cauchy X d x), seq_converges X d x

def seq_equiv (a b: ℕ → X) :=
∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n : ℕ)(hn: n ≥ N), d (a n) (b n) < ε

def seq_equiv2
 (a b: ℕ → X) :=
seq_lim ℝ dist_real (λ(n: ℕ), d (a n) (b n)) 0

lemma seq_equiv_defs (a b : ℕ → X): seq_equiv X d a b ↔ seq_equiv2 X d a b :=
begin 
  split,
  {
    intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    rw dist_real_to_zero,
    have obv : (λ (n : ℕ), d (a n) (b n)) n = d (a n) (b n) := by refl,
    rw obv,
    rw abs_of_dist,
    exact hN n hn,
  },
  {
      intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    rw dist_real_to_zero at hN,
    have obv : (λ (n : ℕ), d (a n) (b n)) n = d (a n) (b n) := by refl,
    rw obv at hN,
    rw abs_of_dist at hN,
    exact hN
  },
end

lemma seq_equiv_almost_symm (a b: ℕ → X) : 
seq_equiv X d a b → seq_equiv X d b a :=
begin 
  intros h ε hε,
  cases h ε hε with N hN,
  use N,
  intros n hn,
  have d_symm := (hX X d).right.left (b n) (a n),
  rw d_symm,
  exact hN n hn,
end

lemma seq_equiv_symm (a b: ℕ → X) : 
seq_equiv X d a b ↔ seq_equiv X d b a := 
⟨seq_equiv_almost_symm X d a b, seq_equiv_almost_symm X d b a⟩


lemma equiv_is_cauchy (x : ℕ → X) (y : ℕ → X)
(hx : is_cauchy X d x) (hxy: seq_equiv X d x y) : is_cauchy X d y :=
begin 
  intros ε hε,
  unfold is_cauchy at hx,
  cases hx (ε/3) (by linarith) with N₁ hN₁,
  cases hxy (ε/3) (by linarith) with N₂ hN₂,
  let N := max N₁ N₂,
  use N,

  intros n m hn hm,
  
  have hcalc1 := (hX X d).right.right (x n) (y m) (x m),

  have hcalc2 : d (y n) (x n) + d (x n) (x m) + d (x m) (y m) < ε,
  {
    have hn1 : n ≥ N₁ := le_of_max_le_left hn,
    have hn2 : n ≥ N₂ := le_of_max_le_right hn,
    have hm1 : m ≥ N₁ := le_of_max_le_left hm,
    have hm2 : m ≥ N₂ := le_of_max_le_right hm,


    have symm1 := (hX X d).right.left (x n) (y n),
    rw ← symm1,

    have dxy1 := hN₂ n hn2,
    have dxy2 := hN₂ m hm2,
    have dxx := hN₁ n m hn1 hm1,
    linarith,
  },

  exact calc d (y n) (y m) ≤ d(y n) (x n) + d(x n) (y m) 
  : (hX X d).right.right (y n) (y m) (x n)
  ... ≤ d (y n) (x n) + d (x n) (x m) + d (x m) (y m) : by linarith
  ... < ε : hcalc2,
end

lemma seqs_equiv_if_same_limit (x y : ℕ → X) (L : X) 
(hx : seq_lim X d x L) (hy : seq_lim X d y L) : seq_equiv X d x y :=

begin 
  intros ε hε,
  cases hx (ε/2) (by linarith) with N₁ hN₁,
  cases hy (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,

  have t1 := hN₁ n (le_of_max_le_left hn),
  have t2 := hN₂ n (le_of_max_le_right hn),
  have t3 : d (x n) L + d (y n) L < ε := by linarith,
  have t4 := (hX X d).right.right (x n) (y n) L,

  rw (hX X d).right.left (y n) L at t3,

  calc d (x n) (y n) ≤ d (x n) L + d L (y n) : t4
  ... < ε : t3,
end

theorem seq_squeeze (x y z : ℕ → ℝ) (L : ℝ)
 (hx : seq_lim ℝ dist_real x L) (hz : seq_lim ℝ dist_real z L) 
 (hxy : ∀(n : ℕ), x n ≤ y n) (hyz : ∀(n : ℕ), y n ≤ z n) :
 seq_lim ℝ dist_real y L :=
begin
  
  intros ε hε,
  have hxz_equiv := seqs_equiv_if_same_limit ℝ dist_real x z L hx hz,
  cases hxz_equiv (ε/2) (by linarith) with N₁ hN₁,
  cases hx (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  have t1 : 0 ≤ (y n) - (x n) := sub_nonneg.mpr (hxy n),
  have t2 : (y n) - (x n) ≤ (z n) - (x n) := sub_le_sub_right (hyz n) (x n),
  have t3 : 0 ≤ (z n) - (x n) := le_trans t1 t2,
  have t4 : |(y n) - (x n)| = (y n) - (x n) := abs_eq_self.mpr t1,
  have t5 : |(z n) - (x n)| = (z n) - (x n) := abs_eq_self.mpr t3,
  rw ← t5 at t2,
  rw ← t4 at t2,

  have t6 : |(z n) - (x n)| < ε/2,
  {
    specialize hN₁ n,
    have temp1 := hN₁ (le_of_max_le_left hn),
    have temp2 : |(z n) - (x n)| = |(x n) - (z n)| := abs_sub_comm (z n) (x n), 
    rw temp2,
    exact temp1,
  },

  have t7 : |(y n) - (x n)| < ε/2 := gt_of_gt_of_ge t6 t2,
  have t8 : |(x n) - L| < ε/2,
  {
    specialize hN₂ n (le_of_max_le_right hn),
    exact hN₂,
  },
  have t9 : | (y n) - (x n)| + |(x n) - L| < ε := by linarith,
  
  calc dist_real (y n) L ≤ dist_real (y n) (x n) + dist_real (x n) L : 
  real_is_metric_space.right.right (y n) L (x n)
  ... < ε : t9,
end

lemma sum_of_lims_is_lim_of_sum (x y : ℕ → ℝ) (L1 L2 : ℝ)
 (hx : seq_lim ℝ dist_real x L1) (hy : seq_lim ℝ dist_real y L2) :
  seq_lim ℝ dist_real (λ(n : ℕ), (x n) + (y n)) (L1 + L2) :=
begin 
  intros ε hε,
  cases hx (ε/2) (by linarith) with N₁ hN₁,
  cases hy (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,

  specialize hN₁ n (le_of_max_le_left hn),
  specialize hN₂ n (le_of_max_le_right hn),

  have t : (λn, (x n) + (y n)) n = (x n) + (y n) := by refl,
  rw t, 

  have temp : |(x n - L1)| + |(y n - L2)| =
   dist_real (x n) L1 + dist_real (y n) L2 := by refl,

  calc dist_real (x n + y n) (L1 + L2)  = |(x n + y n) - (L1 + L2)| : by refl
  ... = |(x n - L1) + (y n - L2)| : by ring_nf
  ... ≤ |(x n - L1)| + |(y n - L2)| : abs_add (x n - L1) (y n - L2)
  ... < ε : by linarith,
end


lemma equiv_seqs_same_limit (x y : ℕ → X) (hxy : seq_equiv X d x y) (L : X) :
 seq_lim X d x L → seq_lim X d y L
:=
 begin 
   intro hx,
   have dyL_nonneg : ∀(n : ℕ), 0 ≤ d (y n) L,
   {
     intro n,
     apply dist_nonneg,
   },

   have dyL_triangle := 
   λ(n : ℕ), (hX X d).right.right (y n) L (x n),

   let seq1 : ℕ → ℝ := λ(n : ℕ), 0,
   let seq2 : ℕ → ℝ := λ(n : ℕ), d (y n) L,
   let seq3 : ℕ → ℝ  := λ(n : ℕ), d (y n) (x n) + d (x n) L,

  have h12 : ∀(n : ℕ), seq1 n ≤ seq2 n := dyL_nonneg,
  have h23 : ∀(n : ℕ), seq2 n ≤ seq3 n := dyL_triangle,

  have hseq1_to_0 : seq_lim ℝ dist_real seq1 0,
  {
    intros ε hε,
    use 1,
    intros n hn,
    unfold dist_real,
    ring_nf,
    have t : |(0:ℝ)| = 0 := abs_zero,
    rw t,
    exact hε,
  },

  have hseq3_to_0 : seq_lim ℝ dist_real seq3 0,
  {
    let temp1 := λ(n : ℕ), d (y n) (x n),
    let temp2 := λ(n : ℕ), d (x n) L,

    have temp1_to_0 : seq_lim ℝ dist_real temp1 0,
    {
      rw seq_equiv_symm at hxy,
      rw seq_equiv_defs at hxy,
      exact hxy,
    },
    have temp2_to_0 : seq_lim ℝ dist_real temp2 0,
    {
      rw seq_lim_defs at hx,
      exact hx,
    },

    have temp0_plus_temp1 := 
    sum_of_lims_is_lim_of_sum temp1 temp2 0 0 temp1_to_0 temp2_to_0,
    have obv : ((0:ℝ) + (0:ℝ)) = (0:ℝ) := add_zero 0,
    rw obv at temp0_plus_temp1,
    exact temp0_plus_temp1,
  },

  have squeeze := seq_squeeze seq1 seq2 seq3 0 hseq1_to_0 hseq3_to_0 h12 h23,


  have t1 : seq_lim2 ℝ dist_real seq2 0,
  {
    intros ε hε,
    specialize squeeze ε hε,
    cases squeeze with N hN,
    use N,
    intros n hn,
    have t2 : (λ (n : ℕ), dist_real (seq2 n) (seq1 n)) n =
    dist_real (seq2 n) 0 := by refl,
    rw t2,
    rw dist_real_to_zero (seq2 n),
    rw dist_real_to_zero (|seq2 n|),
    rw abs_abs (seq2 n),
    specialize hN n hn,
    rw dist_real_to_zero (seq2 n) at *,
    exact hN,
  },

  rw seq_lim_defs,
  unfold seq_lim2 at *,
  assumption,
 end

def is_bound_for_seq (M : ℝ) (x : ℕ → ℝ) : Prop := ∀n:ℕ, |x n| ≤ M 
def is_upper_bound_for_seq (M : ℝ) (x : ℕ → ℝ) : Prop := ∀n:ℕ, x n ≤ M
def is_lower_bound_for_seq (M : ℝ) (x : ℕ → ℝ) : Prop := ∀n:ℕ, x n ≥ M


def is_bounded_above_seq (x : ℕ → ℝ) : Prop := ∃M:ℝ, (is_upper_bound_for_seq M x)
def is_bounded_below_seq (x : ℕ → ℝ) : Prop := ∃M:ℝ, (is_lower_bound_for_seq M x)
def is_bounded_seq (x : ℕ → ℝ) : Prop := is_bounded_above_seq x ∧ is_bounded_below_seq x
def is_increasing_seq (x : ℕ → ℝ) : Prop := ∀(n m : ℕ) (hnm : n ≤ m), x n ≤ x m
def is_decreasing_seq (x : ℕ → ℝ) : Prop := ∀(n m : ℕ) (hnm : n ≤ m), x n ≥ x m
def is_monotone_seq (x : ℕ → ℝ) : Prop := is_increasing_seq x ∨ is_decreasing_seq x
def is_extraction (φ: ℕ → ℕ) : Prop := ∀(n m : ℕ) (hnm : n < m), φ n < φ m

lemma extraction_geq_id (φ: ℕ → ℕ) (hφ : is_extraction φ) : ∀n:ℕ, n ≤ φ n :=
begin 
  intro n,
  induction n with d hd,
  exact zero_le (φ 0),

  have temp1 := hφ d d.succ (lt_add_one d),
  have temp2 : d < φ d.succ := gt_of_gt_of_ge temp1 hd,
  exact nat.succ_le_iff.mpr temp2,
end

def is_subseq (y x : ℕ → ℝ) : Prop := ∃(φ: ℕ → ℕ) (hφ : is_extraction φ), y = x ∘ φ


theorem monotone_convergence_increasing {x : ℕ → ℝ}
 (hx_increases : is_increasing_seq x)
(hx_bounded_above : is_bounded_above_seq x) : seq_converges ℝ dist_real x :=
begin 
  let xSet := {z : ℝ | ∃n:ℕ, x n = z},
  have xSet_nonempty : xSet.nonempty,
  {
    use x 0,
    use 0,
  },

  have xSet_bounded_above : bdd_above xSet,
  {
    cases hx_bounded_above with M hM,
    use M,
    intros a ha,
    cases ha with n hn,
    rw ← hn,
    exact hM n,
  },

  cases (real.exists_is_lub xSet xSet_nonempty xSet_bounded_above) with s hs,

  use s,
  intros ε hε,

  have : ∃(a : ℝ)(ha : a ∈ xSet), a > s-ε,
  {
    by_contradiction,
    push_neg at h,
    have contr : (s-ε) ∈ upper_bounds xSet := h,
    have : s ≤ s-ε := (is_lub_le_iff hs).mpr contr,
    have t : s-ε < s := by linarith, 
    linarith,
  },

  cases this with a ha,
  cases ha with ha has,
  cases ha with N hN,
  rw ← hN at has,clear hN a,rename has hN,

  use N,
  intros n hn,

  have calc1 : x n ≤ s,
  {
    have : x n ∈ xSet := by use n,
    exact hs.left this,
  },


  have half_1 := calc x n ≤ s: calc1
  ... < s + ε : by linarith,

  have half_2 := calc s-ε < x N : hN
  ... ≤ x n : hx_increases N n hn,

  have t1 : x n - s < ε  := by linarith,
  have t2 : -ε < x n - s := by linarith,
  unfold dist_real,
  have almost : -ε < x n - s ∧ x n - s < ε := ⟨t2, t1⟩,
  exact abs_lt.mpr almost,
end

theorem monotone_convergence_decreasing {x : ℕ → ℝ}
 (hx_decreases : is_decreasing_seq x)
(hx_bounded_below : is_bounded_below_seq x) : seq_converges ℝ dist_real x :=
begin 
  have hnew_seq_increasing : is_increasing_seq (λn, (-1) * (x n)) := sorry,
  have hnew_seq_bdd_above  : is_bounded_above_seq (λn, (-1) * (x n)) := sorry,
  have hnew_seq_converges  := monotone_convergence_increasing 
   hnew_seq_increasing hnew_seq_bdd_above,

  cases hnew_seq_converges with L hL,
  have almost := lim_of_mult_const_seq (λn, (-1) * (x n)) L hL (-1),
  sorry,
end

lemma cauchy_seq_of_reals_is_bounded (x : ℕ → ℝ) (hx : is_cauchy ℝ dist_real x) :
is_bounded_seq x := sorry

def is_peak_term (n : ℕ) (x : ℕ → ℝ) : Prop := ∀m : ℕ, x m ≤ x n

open_locale classical

lemma seq_has_monotone_subseq (x : ℕ → ℝ) : ∃(y:ℕ → ℝ) (hy : is_subseq y x),
is_monotone_seq y := sorry

def subseq_of_bdd {x: ℕ → ℝ} (hx : is_bounded_seq x) {y : ℕ → ℝ}
(hy : is_subseq y x) : is_bounded_seq y := sorry


theorem bolzano_weierstrass (x: ℕ → ℝ) (hx : is_bounded_seq x) : 
 ∃(y : ℕ → ℝ) (hy : is_subseq y x), seq_converges ℝ dist_real y := 
 begin 
   cases seq_has_monotone_subseq x with y hy,
   cases hy with hy_subseq hy_monotone,
   have hy_bounded := subseq_of_bdd hx hy_subseq,

   use y,
   split,
   {exact hy_subseq},
   cases hy_monotone,
   {exact monotone_convergence_increasing hy_monotone hy_bounded.1},
   {exact monotone_convergence_decreasing hy_monotone hy_bounded.2},
 end

theorem reals_are_complete : is_complete ℝ dist_real := 
begin 
  intros x hx,
  have subseq_converges := 
  bolzano_weierstrass x (cauchy_seq_of_reals_is_bounded x hx),

  rcases subseq_converges with ⟨y, hy_subseq, y_lim, hy_lim⟩,
  use y_lim,

  intros ε hε,
  cases hx (ε/2) (by linarith) with N₁ hN₁,
  use N₁,
  intros n hn,

  cases hy_lim (ε/2) (by linarith) with N₂ hN₂,
  let N := max N₁ N₂,

  have calc1 : dist_real (y N) y_lim < ε/2,
  {
    exact hN₂ N (le_max_right N₁ N₂),
  },

  have calc2: dist_real (x n) (y N) < ε/2,
  {
    cases hy_subseq with φ hφ,
    cases hφ with hφ hyxφ,
    have hφN : φ N ≥ N₁,
    {
      have := extraction_geq_id φ hφ N,
      exact le_of_max_le_left this,
    },
    have : y N = x (φ N) := (congr_fun hyxφ N).trans rfl,
    rw this,
    exact hN₁ n (φ N) hn hφN,
  },


  calc dist_real (x n) y_lim ≤ dist_real (x n) (y N) + dist_real (y N) y_lim :
  real_is_metric_space.right.right (x n) y_lim (y N)
  ... < ε : by linarith,
end



lemma cauchy_lim_of_dist (x y : ℕ → X) (hx : is_cauchy X d x) 
 (hx : is_cauchy X d y) : seq_converges ℝ dist_real (λn:ℕ, d (x n) (y n)) :=
 begin 
   sorry,
 end