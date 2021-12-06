import tactic
import data.real.basic
import data.set


noncomputable theory

variable X : Type
variable d: X → X → ℝ

open set

def dist_refl := ∀(x y: X), d x y = 0 ↔ x = y
def dist_symm := ∀(x y : X), d x y = d y x
def dist_triangle := ∀(x y z : X), d x y ≤  d x z + d z y

def is_metric_space := 
∀(x y z: X), (
  (d x y = 0 ↔ x = y) ∧ 
  (d x y  = d y x ) ∧ 
  d x y ≤ d x z  + d z y
)

def real_dist : ℝ → ℝ → ℝ := λ (a b : ℝ), |a - b|

lemma real_is_metric_space : is_metric_space ℝ real_dist := 
begin 
  intros x y z,
  unfold real_dist,

  split,
  simp only [abs_eq_zero],
  exact sub_eq_zero,

  split,
  exact abs_sub_comm x y,
  exact abs_sub_le x z y,
end

constant hX : is_metric_space X d

lemma dist_nonneg : 
∀(x y : X), d x y  ≥ 0 := 
begin 
  intros x y,
  have h1 : d x x  ≤ d x y  + d y x ,
  from ((hX X d x x y).right).right,
  have h2 : d x x  = 0,
  exact (hX X d x x x).left.mpr rfl,
  rw h2 at h1,
  rw ← (hX X d x y x).right.left at h1,
  linarith,
end

def is_cauchy (a : ℕ → X)
:= ∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n m : ℕ)(hn: n ≥ N)
(hm: m ≥ N), d (a n) (a m)  < ε


def seq_lim (a : ℕ → X) (L : X) :=
∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n : ℕ)(hn: n ≥ N),
d (a n) L < ε


def seq_converges (a : ℕ → X) :=
∃(L : X), seq_lim X d a L

def convergent_seqs :=
{a : ℕ → X | seq_converges X d a}


noncomputable def lim_of_seq : convergent_seqs X d → X :=
λ a, classical.some a.2


def seq_equiv 
 (a : ℕ → X) (b : ℕ → X):=
∀(ε : ℝ)(hε : ε > 0),∃(N : ℕ),∀(n : ℕ)(hn: n ≥ N), d (a n) (b n) < ε

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
  
  have hcalc1 := (hX X d (x n) (y m) (x m)).right.right,

  have hcalc2 : d (y n) (x n) + d (x n) (x m) + d (x m) (y m) < ε,
  {
    have hn1 : n ≥ N₁ := le_of_max_le_left hn,
    have hn2 : n ≥ N₂ := le_of_max_le_right hn,
    have hm1 : m ≥ N₁ := le_of_max_le_left hm,
    have hm2 : m ≥ N₂ := le_of_max_le_right hm,

    have symm1 := (hX X d (x n) (y n) (y n)).right.left,
    rw ← symm1,

    have dxy1 := hN₂ n hn2,
    have dxy2 := hN₂ m hm2,
    have dxx := hN₁ n m hn1 hm1,
    linarith,
  },

  exact calc d (y n) (y m) ≤ d(y n) (x n) + d(x n) (y m) 
  : (hX X d (y n) (y m) (x n)).right.right
  ... ≤ d (y n) (x n) + d (x n) (x m) + d (x m) (y m) : by linarith
  ... < ε : hcalc2,


end

lemma lem_equiv_seqs_same_limit (x y : ℕ → X) (L : X) :
 seq_lim X d x L → seq_lim X d y L
:=
 begin 
   intro hx,
   have dyL_nonneg : ∀(n : ℕ), 0 ≤ d (y n) L,
   {
     sorry
   },

   have dyL_triangle := 
   λ(n : ℕ),(hX X d (y n) L (x n)).right.right,

   sorry,
 end