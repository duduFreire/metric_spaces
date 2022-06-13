import tactic

open set


structure topological_space (X : Type) :=
(is_open : set X → Prop)
(is_open_univ : is_open (univ : set X))
(is_open_inter : ∀(U V : set X), is_open U → is_open V → is_open (U ∩ V))
(is_open_union : ∀s, (∀t∈s, is_open t) → is_open ⋃₀ s)

attribute [class] topological_space
def is_open {X : Type} [t : topological_space X] (U : set X) := topological_space.is_open t U

variables {X Y E B: Type} [topological_space X] [topological_space Y]
[topological_space E] [topological_space B]

def is_continuous (f : X → Y) : Prop := ∀{V : set Y} (hV : is_open V), is_open (f⁻¹' V)
def is_hausdorff (Z : Type) [topological_space Z] : Prop := ∀{x y : Z}, x ≠ y → 
∃(U V : set Z) (hU : is_open U) (hV : is_open V) (hUx : x ∈ U) (hVy : y ∈ V),
U ∩ V = ∅
def is_dense (D : set X) : Prop := ∀{U : set X}(U_open : is_open U) (U_nonempty : U ≠ ∅),
∃(d ∈ D), d ∈ U 

lemma eq_of_agree_on_dense {f g : X → Y} (hY : is_hausdorff Y) (hf : is_continuous f)
(hg : is_continuous g) {D : set X} (D_dense : is_dense D)
(hfg : ∀{d}, d ∈ D → f d = g d) : f = g :=
begin
	-- Assume for contradiction that f(x) ≠ g(x) for some x ∈ X.
	ext,
	by_contra,
	-- Fix disjoint open neighborhoods U and V around f(x) and g(x) respectively.
	rcases hY h with ⟨U, V, U_open, V_open, hxU, hxV, hUV⟩,

	-- By continuity, f⁻¹(U) and g⁻¹(V) are both open,
	have U_inv_open := hf U_open,
	have V_inv_open := hg V_open,

	-- which means their intersection must also be open.
	have  UV_inv_open := _inst_1.is_open_inter (f ⁻¹' U) (g ⁻¹' V) U_inv_open V_inv_open,
	-- It is also nonempty, since it contains x.
	have UV_nonempty : (f ⁻¹' U ∩ g ⁻¹' V) ≠ ∅ := λcontra,
	eq_empty_iff_forall_not_mem.mp contra x ⟨hxU, hxV⟩,

	-- Hence there is some d ∈ D with d ∈ f⁻¹(U) ∩ g⁻¹(V).
	rcases D_dense UV_inv_open UV_nonempty with ⟨d, d_D, d_inter⟩,

	-- Thus f(d) ∈ U and g(d) ∈ V.
	rw mem_inter_iff at d_inter,
	have hfd : f d ∈ U := d_inter.1,
	have hgd : g d ∈ V := d_inter.2,

	-- But f(d) = g(d),
	rw← hfg d_D at hgd,
	-- so f(d) ∈ U ∩ V = ∅,
	have contra : f d ∈ U ∩ V := ⟨hfd, hgd⟩,
	-- which is a contradiction.
	rw hUV at contra,
	exact not_mem_empty (f d) contra,
end

variables {f : X → Y} {hf : is_continuous f}

def converges_to (a : ℕ → X) (L : X) : Prop := 
∀{U : set X} (hU : is_open U) (hUL : L ∈ U), ∃(N : ℕ), ∀{n : ℕ}, n ≥ N → a n ∈ U 

lemma converges_unique_of_hausdorff {a : ℕ → X} {L M : X} (hX : is_hausdorff X) 
(hL : converges_to a L) (hM : converges_to a M) : L = M :=
begin 
	by_cases h : L = M, {exact h}, exfalso,

	rcases hX h with ⟨U, V, hU, hV, hUx, hVy, hUV⟩,
	rcases hL hU hUx with ⟨N, hN⟩,
	rcases hM hV hVy with ⟨M, hM⟩,

	have hcontra1 := hN (le_max_left N M),
	have hcontra2 := hM (le_max_right N M),
	have hcontra : a (max N M) ∈ (U ∩ V) := ⟨hcontra1, hcontra2⟩,
	
	finish,
end

lemma converges_of_continuous {a : ℕ → X} {L : X} (hL : converges_to a L) {f : X → Y} 
(hf : is_continuous f) : converges_to (f∘a) (f L) :=
begin 
	intros U hU hUL,
	have hU' := hf hU,
	cases hL hU' hUL with N hN,
	use N,
	finish,
end


structure continuous_map (A : Type) (B : Type)
[topological_space A] [topological_space B] :=
(f : A → B)
(f_continuous : is_continuous f)

structure homeomorphism :=
(map : continuous_map X Y)
(is_bijection : function.bijective map.f)

def maps_homeomorphically (p : E → B) (U : set E) := (restrict p U)