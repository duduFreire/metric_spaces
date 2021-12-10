import tactic
import data.real.basic
import data.set


noncomputable theory

def dist_refl {X : Type} (d : X → X → ℝ)   := ∀(x y : X), d x y = 0 ↔ x = y
def dist_symm {X : Type} (d : X → X → ℝ)   := ∀(x y : X), d x y = d y x
def dist_triangle{X : Type}(d : X → X → ℝ) := ∀(x y z : X), d x y ≤  d x z + d z y

structure metric_space (X : Type) := 
(d : X → X → ℝ)
(refl     : dist_refl d)
(symm     : dist_symm d)
(triangle : dist_triangle d)

variables {X : Type} (mX : metric_space X)


def dist_real : ℝ → ℝ → ℝ := λ (a b : ℝ), |a - b|

@[simp]lemma dist_real_to_zero : ∀(x : ℝ), dist_real x 0 = |x| :=
begin 
  intro x,
  unfold dist_real,
  rw sub_zero x,
end

def mR : metric_space ℝ := {
  d := dist_real,
  refl := 
  begin 
  intros x y,
  unfold dist_real,

  simp only [abs_eq_zero],
  exact sub_eq_zero,
  end,

  symm := 
  begin 
    intros x y,
    exact abs_sub_comm x y,
  end,

  triangle :=
  begin 
    intros x y z,
    exact abs_sub_le x z y,
  end
}

@[simp] lemma mR_dist_is_dist_real : ∀(x y : ℝ), mR.d x y = |x - y| :=
begin 
  intros x y,
  refl,
end

@[simp] lemma dist_real_is_abs : ∀(x y : ℝ), dist_real x y = |x - y| :=
begin 
  intros x y,
  refl,
end

@[simp]lemma dist_real_metric_to_zero : ∀(x : ℝ), mR.d x 0 = |x| :=
begin 
  intro x,
  change mR.d with dist_real,
  unfold dist_real,
  rw sub_zero x,
end


lemma dist_nonneg : 
∀(x y : X), mX.d x y  ≥ 0 := 
begin 
  intros x y,
  have h1 := mX.triangle x x y,
  have h2 := (mX.refl x x).mpr (by refl),
  rw h2 at h1,
  rw ← mX.symm x y at h1,
  linarith,
end

lemma abs_of_dist (x y : X) : |mX.d x y| = mX.d x y :=
begin 
  simp,
  exact dist_nonneg mX x y,
end

def is_cauchy (a : ℕ → X)
:= ∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n m : ℕ)(hn: n ≥ N)
(hm: m ≥ N), mX.d (a n) (a m)  < ε


def seq_lim (a : ℕ → X) (L : X) :=
∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n : ℕ)(hn: n ≥ N),
mX.d (a n) L < ε

def seq_lim2 (a : ℕ → X) (L : X) :=
seq_lim mR (λ(n : ℕ), mX.d (a n) L) (0:ℝ)

lemma seq_lim_defs (a : ℕ → X) (L : X) :
seq_lim mX a L ↔ seq_lim2 mX a L :=
begin 
  split,
  {
    intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    rw dist_real_metric_to_zero,
    rw abs_of_dist,
    exact hN n hn,
  },
  {
    intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    rw dist_real_metric_to_zero at hN,
    rw abs_of_dist at hN,
    exact hN,
  },
end


lemma lim_of_mult_const_seq (x : ℕ → ℝ) (L : ℝ) 
(hx : seq_lim mR x L) (k : ℝ) : seq_lim mR (λn, k * (x n)) (k*L) :=
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
  simp at *,
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
∃(L : X), @seq_lim X mX a L

def is_complete : Prop := ∀(x : ℕ → X)(hx : is_cauchy mX x), seq_converges mX x

def seq_equiv (a b: ℕ → X) :=
∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n : ℕ)(hn: n ≥ N), mX.d (a n) (b n) < ε

def seq_equiv2
 (a b: ℕ → X) :=
seq_lim mR (λ(n: ℕ), mX.d (a n) (b n)) 0

lemma seq_equiv_defs (a b : ℕ → X): seq_equiv mX a b ↔ seq_equiv2 mX a b :=
begin 
  split,
  {
    intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    simp,
    rw abs_of_dist,
    exact hN n hn,
  },
  {
      intros h ε hε,
    cases h ε hε with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    simp at *,
    rw abs_of_dist at hN,
    exact hN,
  },
end

lemma seq_equiv_almost_symm (a b: ℕ → X) : 
seq_equiv mX a b → seq_equiv mX b a :=
begin 
  intros h ε hε,
  cases h ε hε with N hN,
  use N,
  intros n hn,
  have d_symm := mX.symm (b n) (a n),
  rw d_symm,
  exact hN n hn,
end

lemma seq_equiv_symm (a b: ℕ → X) : 
seq_equiv mX a b ↔ seq_equiv mX b a := 
⟨seq_equiv_almost_symm mX a b, seq_equiv_almost_symm mX b a⟩


lemma equiv_is_cauchy (x : ℕ → X) (y : ℕ → X)
(hx : is_cauchy mX x) (hxy: seq_equiv mX x y) : is_cauchy mX y :=
begin 
  intros ε hε,
  unfold is_cauchy at hx,
  cases hx (ε/3) (by linarith) with N₁ hN₁,
  cases hxy (ε/3) (by linarith) with N₂ hN₂,
  let N := max N₁ N₂,
  use N,

  intros n m hn hm,
  
  have hcalc1 := mX.triangle (x n) (y m) (x m),

  have hcalc2 : mX.d (y n) (x n) + mX.d (x n) (x m) + mX.d (x m) (y m) < ε,
  {
    have hn1 : n ≥ N₁ := le_of_max_le_left hn,
    have hn2 : n ≥ N₂ := le_of_max_le_right hn,
    have hm1 : m ≥ N₁ := le_of_max_le_left hm,
    have hm2 : m ≥ N₂ := le_of_max_le_right hm,


    have symm1 := mX.symm (x n) (y n),
    rw ← symm1,

    have dxy1 := hN₂ n hn2,
    have dxy2 := hN₂ m hm2,
    have dxx := hN₁ n m hn1 hm1,
    linarith,
  },

  exact calc mX.d (y n) (y m) ≤ mX.d (y n) (x n) + mX.d (x n) (y m) 
  : mX.triangle (y n) (y m) (x n)
  ... ≤ mX.d (y n) (x n) + mX.d (x n) (x m) + mX.d (x m) (y m) : by linarith
  ... < ε : hcalc2,
end

lemma seqs_equiv_if_same_limit (x y : ℕ → X) (L : X) 
(hx : seq_lim mX x L) (hy : seq_lim mX y L) : seq_equiv mX x y :=

begin 
  intros ε hε,
  cases hx (ε/2) (by linarith) with N₁ hN₁,
  cases hy (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,

  have t1 := hN₁ n (le_of_max_le_left hn),
  have t2 := hN₂ n (le_of_max_le_right hn),
  have t3 : mX.d (x n) L + mX.d (y n) L < ε := by linarith,
  have t4 := mX.triangle (x n) (y n) L,

  rw mX.symm (y n) L at t3,

  calc mX.d (x n) (y n) ≤ mX.d (x n) L + mX.d L (y n) : t4
  ... < ε : t3,
end

theorem seq_squeeze (x y z : ℕ → ℝ) (L : ℝ)
 (hx : seq_lim mR x L) (hz : seq_lim mR z L) 
 (hxy : ∀(n : ℕ), x n ≤ y n) (hyz : ∀(n : ℕ), y n ≤ z n) :
 seq_lim mR y L :=
begin
  
  intros ε hε,
  have hxz_equiv := seqs_equiv_if_same_limit mR x z L hx hz,
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
  mR.triangle (y n) L (x n)
  ... < ε : t9,
end

lemma sum_of_lims_is_lim_of_sum (x y : ℕ → ℝ) (L1 L2 : ℝ)
 (hx : seq_lim mR x L1) (hy : seq_lim mR y L2) :
  seq_lim mR (λ(n : ℕ), (x n) + (y n)) (L1 + L2) :=
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
  simp at *,

  calc dist_real (x n + y n) (L1 + L2)  = |(x n + y n) - (L1 + L2)| : by refl
  ... = |(x n - L1) + (y n - L2)| : by ring_nf
  ... ≤ |(x n - L1)| + |(y n - L2)| : abs_add (x n - L1) (y n - L2)
  ... < ε : by linarith,
end


lemma equiv_seqs_same_limit (x y : ℕ → X) (hxy : seq_equiv mX x y) (L : X) :
 seq_lim mX x L → seq_lim mX y L
:=
 begin 
   intro hx,
   have dyL_nonneg : ∀(n : ℕ), 0 ≤ mX.d (y n) L,
   {
     intro n,
     apply dist_nonneg,
   },

   have dyL_triangle := λ(n : ℕ), mX.triangle (y n) L (x n),

   let seq1 : ℕ → ℝ := λ(n : ℕ), 0,
   let seq2 : ℕ → ℝ := λ(n : ℕ), mX.d (y n) L,
   let seq3 : ℕ → ℝ  := λ(n : ℕ), mX.d (y n) (x n) + mX.d (x n) L,

  have h12 : ∀(n : ℕ), seq1 n ≤ seq2 n := dyL_nonneg,
  have h23 : ∀(n : ℕ), seq2 n ≤ seq3 n := dyL_triangle,

  have hseq1_to_0 : seq_lim mR seq1 0,
  {
    intros ε hε,
    use 1,
    intros n hn,
    simp,
    exact hε,
  },

  have hseq3_to_0 : seq_lim mR seq3 0,
  {
    let temp1 := λ(n : ℕ), mX.d (y n) (x n),
    let temp2 := λ(n : ℕ), mX.d (x n) L,

    have temp1_to_0 : seq_lim mR temp1 0,
    {
      rw seq_equiv_symm at hxy,
      rw seq_equiv_defs at hxy,
      exact hxy,
    },
    have temp2_to_0 : seq_lim mR temp2 0,
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


  have t1 : seq_lim2 mR seq2 0,
  {
    intros ε hε,
    specialize squeeze ε hε,
    cases squeeze with N hN,
    use N,
    intros n hn,
    have t2 : (λ (n : ℕ), dist_real (seq2 n) (seq1 n)) n =
    dist_real (seq2 n) 0 := by refl,
    simp at *,
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
(hx_bounded_above : is_bounded_above_seq x) : seq_converges mR x :=
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
  simp,
  have almost : -ε < x n - s ∧ x n - s < ε := ⟨t2, t1⟩,
  exact abs_lt.mpr almost,
end

theorem monotone_convergence_decreasing {x : ℕ → ℝ}
 (hx_decreases : is_decreasing_seq x)
(hx_bounded_below : is_bounded_below_seq x) : seq_converges mR x :=
begin 
  have hnew_seq_increasing : is_increasing_seq (λn, (-1) * (x n)),
  {
    intros n m hnm,
    have := hx_decreases n m hnm,
    finish,
  },
  have hnew_seq_bdd_above  : is_bounded_above_seq (λn, (-1) * (x n)),
  {
    cases hx_bounded_below with M hM,
    use (-1) * M,
    intro n,
    unfold is_lower_bound_for_seq at hM,
    finish,
  },
  have hnew_seq_converges  := monotone_convergence_increasing 
   hnew_seq_increasing hnew_seq_bdd_above,

  cases hnew_seq_converges with L hL,
  have almost := lim_of_mult_const_seq (λn, (-1) * (x n)) L hL (-1),
  use (-L),
  intros ε hε,
  specialize almost ε hε,
  cases almost with N hN,
  use N,
  intros n hn,
  specialize hN n hn,
  finish,
end

lemma cauchy_seq_of_reals_is_bounded (x : ℕ → ℝ) (hx : is_cauchy mR x) :
is_bounded_seq x := sorry

def is_peak_term (n : ℕ) (x : ℕ → ℝ) : Prop := ∀(m : ℕ)(hm: m ≥ n), x m ≤ x n


noncomputable def peak_func {x : ℕ → ℝ}(h : ∀(n : ℕ), ∃(m : ℕ)(hmn : m > n),(is_peak_term m x)) :
ℕ → ℕ 
| 0 := classical.some (h 0) 
| (b+1) := classical.some (h (peak_func b)) 

lemma peak_func_is_extraction {x : ℕ → ℝ}
(h : ∀(n : ℕ), ∃(m : ℕ)(hmn : m > n),(is_peak_term m x)):
 is_extraction (peak_func h) := sorry

 lemma peak_func_is_peaks {x : ℕ → ℝ}
(h : ∀(n : ℕ), ∃(m : ℕ)(hmn : m > n),(is_peak_term m x)) : 
∀(n : ℕ), is_peak_term (peak_func h n) x := sorry


lemma seq_has_monotone_subseq (x : ℕ → ℝ) : ∃(y:ℕ → ℝ) (hy : is_subseq y x),
is_monotone_seq y := 
begin 
  by_cases ∀(n : ℕ), ∃(m : ℕ)(hmn : m > n),(is_peak_term m x),
  {
    let φ := peak_func h,
    use x ∘ φ,
    split,
    {
      use φ,
      exact ⟨peak_func_is_extraction h, rfl⟩,
    },
    {
      right,
      intros n m hnm,
      by_cases h1 : m = n,
      rw h1, exact rfl.ge,
      have := peak_func_is_extraction h n m ((ne.symm h1).le_iff_lt.mp hnm),
      exact peak_func_is_peaks h n (φ m) (le_of_lt this),
    },
  },
  {
    unfold is_peak_term at h,
    push_neg at h,
    sorry
  },
end

lemma subseq_of_bdd {x: ℕ → ℝ} (hx : is_bounded_seq x) {y : ℕ → ℝ}
(hy : is_subseq y x) : is_bounded_seq y := 
begin 
  split,
  {
    cases hx.left with M hM,
    use M,
    intros n,
    rcases hy with ⟨φ, hφ, hyx⟩,
    rw hyx,
    exact hM (φ n),
  },
  {
    cases hx.right with M hM,
    use M,
    intros n,
    rcases hy with ⟨φ, hφ, hyx⟩,
    rw hyx,
    exact hM (φ n),
  },
end


theorem bolzano_weierstrass (x: ℕ → ℝ) (hx : is_bounded_seq x) : 
 ∃(y : ℕ → ℝ) (hy : is_subseq y x), seq_converges mR y := 
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

theorem reals_are_complete : is_complete mR := 
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
  mR.triangle (x n) y_lim (y N)
  ... < ε : by linarith,
end



lemma cauchy_lim_of_dist (x y : ℕ → X) (hx : is_cauchy mX x) 
 (hx : is_cauchy mX y) : seq_converges mR (λn:ℕ, mX.d (x n) (y n)) :=
 begin 
   sorry,
 end