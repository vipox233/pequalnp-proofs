import PEqualNP.Defs

-- L-meta-25535: list the indices in rank order. A suffix OR S, an initial-segment OR and a
-- two-lit-below-t bit T are shared. For each position p and each low end lo (p itself or one
-- of its at most d later neighbours) one term reads x_p AND S(lo+1) AND T(hi), with hi the next
-- later neighbour above lo (or n): with lit set {p, q}, p < q, it fires iff q lies in (lo, hi).

namespace PEqualNP.Outside.L_meta_25535_aux
open PEqualNP.CircuitLowerBounds

-- copied from src_L_clb_042.lean (clb toolkit)
/-! ### Straight-line circuits given by a gate function -/

theorem wires_snoc (gs : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    (⟨gs ++ [g], o⟩ : Circuit).wires x = (⟨gs, o⟩ : Circuit).wires x
      ++ [g.op.eval (g.inputs.map fun i => ((⟨gs, o⟩ : Circuit).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wires_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    ((⟨gs, o⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => rw [wires_snoc]; simp [ih]; omega

/-- The circuit whose gate number `j` is `g j`, for `j < N`. -/
def prog (g : ℕ → Gate) (N o : ℕ) : Circuit := ⟨(List.range N).map g, o⟩

theorem prog_output (g : ℕ → Gate) (N o : ℕ) : (prog g N o).output = o := rfl

theorem prog_size (g : ℕ → Gate) (N o : ℕ) : (prog g N o).size = N := by
  simp [prog, Circuit.size]

theorem prog_mem (g : ℕ → Gate) (N o : ℕ) (G : Gate) (h : G ∈ (prog g N o).gates) :
    ∃ j < N, g j = G := by
  simpa [prog] using h

/-- A wire valuation that satisfies every gate equation is the wire list. -/
theorem prog_wires (I N o : ℕ) (g : ℕ → Gate) (V : ℕ → Bool) (x : List Bool) (hx : x.length = I)
    (hin : ∀ i < I, x.getD i false = V i)
    (hrb : ∀ j < N, ∀ i ∈ (g j).inputs, i < I + j)
    (heq : ∀ j < N, V (I + j) = (g j).op.eval ((g j).inputs.map V)) :
    ∀ i < I + N, ((prog g N o).wires x).getD i false = V i := by
  induction N with
  | zero => intro i hi; simp only [prog, List.range_zero, List.map_nil, Circuit.wires,
      List.foldl_nil]; exact hin i (by omega)
  | succ N ih =>
    have ih' := ih (fun j hj => hrb j (by omega)) (fun j hj => heq j (by omega))
    have hlen : ((prog g N o).wires x).length = I + N := by
      rw [prog, wires_length]; simp [hx]
    intro i hi
    have hsplit : prog g (N + 1) o = ⟨(List.range N).map g ++ [g N], o⟩ := by
      simp [prog, List.range_succ]
    rw [hsplit, wires_snoc]
    rcases Nat.lt_or_ge i (I + N) with h | h
    · rw [List.getD_append _ _ _ _ (by rw [← prog]; omega)]; exact ih' i h
    · have : i = I + N := by omega
      subst this
      rw [List.getD_append_right _ _ _ _ (by rw [← prog]; omega)]
      rw [← prog, hlen, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [heq N (by omega)]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih' i (hrb N (by omega) i hi)

theorem prog_readsBack (I N o : ℕ) (g : ℕ → Gate) (hrb : ∀ j < N, ∀ i ∈ (g j).inputs, i < I + j) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I (prog g N o) := by
  intro j hj i hi
  have hj' : j < N := by simpa [prog] using hj
  have : PEqualNP.MetaComplexity.NestedCover.gateAt (prog g N o) j = g j := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, prog, hj']
  rw [this] at hi
  exact hrb j hj' i hi

/-! ### Bits -/

/-! ### The layout: suffix OR, initial-segment OR, a two-lit bit, then one term per slot -/

def Sf (n : ℕ) (y : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => y (n - (k + 1)) || Sf n y k

def Pf (y : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => y i || Pf y i

def Tf (y : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => Tf y i || (y i && Pf y i)

def a1 (n d : ℕ) (lo : ℕ → ℕ) (y : ℕ → Bool) (m : ℕ) : Bool :=
  y (m / (d + 1)) && Sf n y (n - (lo m + 1))

def a2 (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (m : ℕ) : Bool :=
  a1 n d lo y m && Tf y (hi m)

def acc (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) : ℕ → Bool
  | 0 => a2 n d lo hi y 0
  | m + 1 => acc n d lo hi y m || a2 n d lo hi y (m + 1)

def gt (n d : ℕ) (yw lo hi : ℕ → ℕ) (j : ℕ) : Gate :=
  if j ≤ n then
    (if j = 0 then ⟨GateOp.or, []⟩ else ⟨GateOp.or, [yw (n - j), n + (j - 1)]⟩)
  else if j ≤ 2 * n + 1 then
    (if j = n + 1 then ⟨GateOp.or, []⟩ else ⟨GateOp.or, [yw (j - (n + 2)), n + (j - 1)]⟩)
  else if j < 4 * n + 3 then
    (if j = 2 * n + 2 then ⟨GateOp.or, []⟩
     else if (j - (2 * n + 2)) % 2 = 1 then
       ⟨GateOp.and, [yw ((j - (2 * n + 2)) / 2), n + (n + 1 + (j - (2 * n + 2)) / 2)]⟩
     else ⟨GateOp.or, [n + (j - 2), n + (j - 1)]⟩)
  else
    (if (j - (4 * n + 3)) % 3 = 0 then
      ⟨GateOp.and, [yw ((j - (4 * n + 3)) / 3 / (d + 1)),
        n + (n - (lo ((j - (4 * n + 3)) / 3) + 1))]⟩
     else if (j - (4 * n + 3)) % 3 = 1 then
      ⟨GateOp.and, [n + (j - 1), n + (2 * n + 2 + 2 * hi ((j - (4 * n + 3)) / 3))]⟩
     else if j - (4 * n + 3) = 2 then ⟨GateOp.or, [n + (j - 1)]⟩
     else ⟨GateOp.or, [n + (j - 3), n + (j - 1)]⟩)

def NN (n d : ℕ) : ℕ := 4 * n + 3 + 3 * (n * (d + 1))

def V' (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (j : ℕ) : Bool :=
  if j ≤ n then Sf n y j
  else if j ≤ 2 * n + 1 then Pf y (j - (n + 1))
  else if j < 4 * n + 3 then
    (if (j - (2 * n + 2)) % 2 = 0 then Tf y ((j - (2 * n + 2)) / 2)
     else (y ((j - (2 * n + 2)) / 2) && Pf y ((j - (2 * n + 2)) / 2)))
  else if (j - (4 * n + 3)) % 3 = 0 then a1 n d lo y ((j - (4 * n + 3)) / 3)
  else if (j - (4 * n + 3)) % 3 = 1 then a2 n d lo hi y ((j - (4 * n + 3)) / 3)
  else acc n d lo hi y ((j - (4 * n + 3)) / 3)

def V (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool) (w : ℕ) : Bool :=
  if w < n then x.getD w false else V' n d lo hi y (w - n)

theorem VS (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool) (k : ℕ) (hk : k ≤ n) :
    V n d lo hi y x (n + k) = Sf n y k := by
  unfold V V'
  simp only [show n + k - n = k by omega]
  split_ifs <;> first | omega | rfl

theorem VP (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool) (i : ℕ) (hi' : i ≤ n) :
    V n d lo hi y x (n + (n + 1 + i)) = Pf y i := by
  unfold V V'
  simp only [show n + (n + 1 + i) - n = n + 1 + i by omega, show n + 1 + i - (n + 1) = i by omega]
  split_ifs <;> first | omega | rfl

theorem VT (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool) (t : ℕ) (h1 : t % 2 = 0)
    (h2 : t ≤ 2 * n) : V n d lo hi y x (n + (2 * n + 2 + t)) = Tf y (t / 2) := by
  unfold V V'
  simp only [show n + (2 * n + 2 + t) - n = 2 * n + 2 + t by omega,
    show 2 * n + 2 + t - (2 * n + 2) = t by omega]
  split_ifs <;> first | omega | rfl

theorem VA (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool) (t : ℕ) (h1 : t % 2 = 1)
    (h2 : t < 2 * n + 1) :
    V n d lo hi y x (n + (2 * n + 2 + t)) = (y (t / 2) && Pf y (t / 2)) := by
  unfold V V'
  simp only [show n + (2 * n + 2 + t) - n = 2 * n + 2 + t by omega,
    show 2 * n + 2 + t - (2 * n + 2) = t by omega]
  split_ifs <;> first | omega | rfl

theorem VB (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool) (m r : ℕ) (hr : r < 3) :
    V n d lo hi y x (n + (4 * n + 3 + (3 * m + r))) =
      (if r = 0 then a1 n d lo y m else if r = 1 then a2 n d lo hi y m else acc n d lo hi y m) := by
  unfold V V'
  simp only [show n + (4 * n + 3 + (3 * m + r)) - n = 4 * n + 3 + (3 * m + r) by omega,
    show 4 * n + 3 + (3 * m + r) - (4 * n + 3) = 3 * m + r by omega,
    show (3 * m + r) / 3 = m by omega, show (3 * m + r) % 3 = r by omega]
  split_ifs <;> first | omega | rfl

theorem gt_reads (n d : ℕ) (yw lo hi : ℕ → ℕ) (hyw : ∀ p, yw p < n ∨ yw p = 0)
    (hhi : ∀ m < n * (d + 1), hi m ≤ n) :
    ∀ j < NN n d, ∀ i ∈ (gt n d yw lo hi j).inputs, i < n + j := by
  intro j hj i hi
  unfold NN at hj
  unfold gt at hi
  split_ifs at hi <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  all_goals first
    | omega
    | (have := hyw (n - j); omega)
    | (have := hyw (j - (n + 2)); omega)
    | (have := hyw ((j - (2 * n + 2)) / 2); omega)
    | (have := hyw ((j - (4 * n + 3)) / 3 / (d + 1)); omega)
    | (have := hhi ((j - (4 * n + 3)) / 3) (by omega); omega)

theorem gt_mono (n d : ℕ) (yw lo hi : ℕ → ℕ) (N o : ℕ) :
    PEqualNP.MetaComplexity.Monotone2 (prog (gt n d yw lo hi) N o) := by
  intro G hG
  obtain ⟨j, _, rfl⟩ := prog_mem _ _ _ G hG
  unfold gt
  split_ifs <;> simp

theorem gt_eqns (n d : ℕ) (yw lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool)
    (hyw : ∀ p < n, yw p < n) (hy : ∀ p < n, x.getD (yw p) false = y p)
    (hhi : ∀ m < n * (d + 1), hi m ≤ n) :
    ∀ j < NN n d, V n d lo hi y x (n + j) =
      (gt n d yw lo hi j).op.eval ((gt n d yw lo hi j).inputs.map (V n d lo hi y x)) := by
  have Vy : ∀ p < n, V n d lo hi y x (yw p) = y p := by
    intro p hp
    unfold V
    rw [if_pos (hyw p hp)]
    exact hy p hp
  intro j hj
  unfold NN at hj
  by_cases hA : j ≤ n
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      have hg : gt n d yw lo hi 0 = ⟨GateOp.or, []⟩ := by unfold gt; simp
      rw [hg, VS n d lo hi y x 0 (by omega)]
      simp [Sf, GateOp.eval]
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hg : gt n d yw lo hi (k + 1) = ⟨GateOp.or, [yw (n - (k + 1)), n + k]⟩ := by
        unfold gt; split_ifs <;> first | omega | contradiction | simp
      rw [hg, VS n d lo hi y x (k + 1) hA]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [Vy _ (by omega), VS n d lo hi y x k (by omega)]
      simp [Sf]
  by_cases hB : j ≤ 2 * n + 1
  · obtain ⟨i, rfl⟩ : ∃ i, j = n + 1 + i := ⟨j - (n + 1), by omega⟩
    rcases i with _ | i
    · have hg : gt n d yw lo hi (n + 1 + 0) = ⟨GateOp.or, []⟩ := by
        unfold gt; split_ifs <;> first | omega | rfl
      rw [hg, VP n d lo hi y x 0 (by omega)]
      simp [Pf, GateOp.eval]
    · have hg : gt n d yw lo hi (n + 1 + (i + 1)) =
          ⟨GateOp.or, [yw i, n + (n + 1 + i)]⟩ := by
        unfold gt
        split_ifs <;> first | omega |
          rw [show n + 1 + (i + 1) - (n + 2) = i by omega,
            show n + 1 + (i + 1) - 1 = n + 1 + i by omega]
      rw [hg, VP n d lo hi y x (i + 1) (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [Vy _ (by omega), VP n d lo hi y x i (by omega)]
      simp [Pf]
  by_cases hC : j < 4 * n + 3
  · obtain ⟨t, rfl⟩ : ∃ t, j = 2 * n + 2 + t := ⟨j - (2 * n + 2), by omega⟩
    by_cases ht0 : t = 0
    · subst ht0
      have hg : gt n d yw lo hi (2 * n + 2 + 0) = ⟨GateOp.or, []⟩ := by
        unfold gt; split_ifs <;> first | omega | rfl
      rw [hg, VT n d lo hi y x 0 (by omega) (by omega)]
      simp [Tf, GateOp.eval]
    by_cases hto : t % 2 = 1
    · have hg : gt n d yw lo hi (2 * n + 2 + t) =
          ⟨GateOp.and, [yw (t / 2), n + (n + 1 + t / 2)]⟩ := by
        unfold gt
        split_ifs <;> first | omega | rw [show 2 * n + 2 + t - (2 * n + 2) = t by omega]
      rw [hg, VA n d lo hi y x t hto (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [Vy _ (by omega), VP n d lo hi y x (t / 2) (by omega)]
      simp
    · have hg : gt n d yw lo hi (2 * n + 2 + t) =
          ⟨GateOp.or, [n + (2 * n + 2 + (t - 2)), n + (2 * n + 2 + (t - 1))]⟩ := by
        unfold gt
        split_ifs <;> first | omega |
          rw [show 2 * n + 2 + t - 2 = 2 * n + 2 + (t - 2) by omega,
            show 2 * n + 2 + t - 1 = 2 * n + 2 + (t - 1) by omega]
      rw [hg, VT n d lo hi y x t (by omega) (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [VT n d lo hi y x (t - 2) (by omega) (by omega),
        VA n d lo hi y x (t - 1) (by omega) (by omega)]
      rw [show t / 2 = (t - 2) / 2 + 1 by omega, show (t - 1) / 2 = (t - 2) / 2 by omega]
      simp [Tf]
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 3 ∧ j = 4 * n + 3 + (3 * m + r) :=
    ⟨(j - (4 * n + 3)) / 3, (j - (4 * n + 3)) % 3, by omega, by omega⟩
  have hm : m < n * (d + 1) := by omega
  have hp : m / (d + 1) < n := (Nat.div_lt_iff_lt_mul (by omega)).2 hm
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
  · have hg : gt n d yw lo hi (4 * n + 3 + (3 * m + 0)) =
        ⟨GateOp.and, [yw (m / (d + 1)), n + (n - (lo m + 1))]⟩ := by
      unfold gt
      split_ifs <;> first | omega |
        rw [show (4 * n + 3 + (3 * m + 0) - (4 * n + 3)) / 3 = m by omega]
    rw [hg, VB n d lo hi y x m 0 (by omega)]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [Vy _ hp, VS n d lo hi y x _ (by omega)]
    simp [a1]
  · have hg : gt n d yw lo hi (4 * n + 3 + (3 * m + 1)) =
        ⟨GateOp.and, [n + (4 * n + 3 + (3 * m + 0)), n + (2 * n + 2 + 2 * hi m)]⟩ := by
      unfold gt
      split_ifs <;> first | omega |
        rw [show (4 * n + 3 + (3 * m + 1) - (4 * n + 3)) / 3 = m by omega,
          show 4 * n + 3 + (3 * m + 1) - 1 = 4 * n + 3 + (3 * m + 0) by omega]
    have hh := hhi m hm
    rw [hg, VB n d lo hi y x m 1 (by omega)]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [VB n d lo hi y x m 0 (by omega), VT n d lo hi y x (2 * hi m) (by omega) (by omega),
      show 2 * hi m / 2 = hi m by omega]
    simp [a2]
  · rcases m with _ | m
    · have hg : gt n d yw lo hi (4 * n + 3 + (3 * 0 + 2)) =
          ⟨GateOp.or, [n + (4 * n + 3 + (3 * 0 + 1))]⟩ := by
        unfold gt
        split_ifs <;> first | omega |
          rw [show 4 * n + 3 + (3 * 0 + 2) - 1 = 4 * n + 3 + (3 * 0 + 1) by omega]
      rw [hg, VB n d lo hi y x 0 2 (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [VB n d lo hi y x 0 1 (by omega)]
      simp [acc]
    · have hg : gt n d yw lo hi (4 * n + 3 + (3 * (m + 1) + 2)) =
          ⟨GateOp.or, [n + (4 * n + 3 + (3 * m + 2)), n + (4 * n + 3 + (3 * (m + 1) + 1))]⟩ := by
        unfold gt
        split_ifs <;> first | omega |
          rw [show 4 * n + 3 + (3 * (m + 1) + 2) - 3 = 4 * n + 3 + (3 * m + 2) by omega,
            show 4 * n + 3 + (3 * (m + 1) + 2) - 1 = 4 * n + 3 + (3 * (m + 1) + 1) by omega]
      rw [hg, VB n d lo hi y x (m + 1) 2 (by omega)]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      rw [VB n d lo hi y x m 2 (by omega), VB n d lo hi y x (m + 1) 1 (by omega)]
      simp [acc]

theorem build_eval (n d : ℕ) (yw lo hi : ℕ → ℕ) (y : ℕ → Bool) (x : List Bool)
    (hx : x.length = n) (hn : 0 < n)
    (hyw : ∀ p < n, yw p < n) (hyw0 : ∀ p, yw p < n ∨ yw p = 0)
    (hy : ∀ p < n, x.getD (yw p) false = y p)
    (hhi : ∀ m < n * (d + 1), hi m ≤ n) :
    (prog (gt n d yw lo hi) (NN n d) (n + NN n d - 1)).eval x =
      acc n d lo hi y (n * (d + 1) - 1) := by
  have hM : 1 ≤ n * (d + 1) := Nat.mul_pos hn (by omega)
  have hw := prog_wires n (NN n d) (n + NN n d - 1) (gt n d yw lo hi) (V n d lo hi y x) x hx
    (fun i hi => by unfold V; rw [if_pos hi]) (gt_reads n d yw lo hi hyw0 hhi)
    (gt_eqns n d yw lo hi y x hyw hy hhi)
  rw [PEqualNP.CircuitLowerBounds.Circuit.eval, prog_output, hw _ (by unfold NN; omega)]
  rw [show n + NN n d - 1 = n + (4 * n + 3 + (3 * (n * (d + 1) - 1) + 2)) by unfold NN; omega,
    VB n d lo hi y x _ 2 (by omega)]
  simp

/-! ### Semantics -/

theorem Sf_iff (n : ℕ) (y : ℕ → Bool) :
    ∀ k, k ≤ n → (Sf n y k = true ↔ ∃ q, n - k ≤ q ∧ q < n ∧ y q = true)
  | 0, _ => by
    constructor
    · intro h; simp [Sf] at h
    · rintro ⟨q, h1, h2, _⟩; omega
  | k + 1, hk => by
    rw [Sf, Bool.or_eq_true, Sf_iff n y k (by omega)]
    constructor
    · rintro (h | ⟨q, h1, h2, h3⟩)
      · exact ⟨n - (k + 1), le_refl _, by omega, h⟩
      · exact ⟨q, by omega, h2, h3⟩
    · rintro ⟨q, h1, h2, h3⟩
      by_cases hq : q = n - (k + 1)
      · left; rw [← hq]; exact h3
      · right; exact ⟨q, by omega, h2, h3⟩

theorem Pf_iff (y : ℕ → Bool) : ∀ i, (Pf y i = true ↔ ∃ p, p < i ∧ y p = true)
  | 0 => by simp [Pf]
  | i + 1 => by
    rw [Pf, Bool.or_eq_true, Pf_iff y i]
    constructor
    · rintro (h | ⟨p, h1, h2⟩)
      · exact ⟨i, by omega, h⟩
      · exact ⟨p, by omega, h2⟩
    · rintro ⟨p, h1, h2⟩
      by_cases hp : p = i
      · left; rw [← hp]; exact h2
      · right; exact ⟨p, by omega, h2⟩

theorem Tf_iff (y : ℕ → Bool) :
    ∀ i, (Tf y i = true ↔ ∃ p q, p < q ∧ q < i ∧ y p = true ∧ y q = true)
  | 0 => by simp [Tf]
  | i + 1 => by
    rw [Tf, Bool.or_eq_true, Tf_iff y i, Bool.and_eq_true, Pf_iff]
    constructor
    · rintro (⟨p, q, h1, h2, h3, h4⟩ | ⟨h, p, h1, h2⟩)
      · exact ⟨p, q, h1, by omega, h3, h4⟩
      · exact ⟨p, i, h1, by omega, h2, h⟩
    · rintro ⟨p, q, h1, h2, h3, h4⟩
      by_cases hq : q = i
      · right; subst hq; exact ⟨h4, p, h1, h3⟩
      · left; exact ⟨p, q, h1, by omega, h3, h4⟩

theorem acc_iff (n d : ℕ) (lo hi : ℕ → ℕ) (y : ℕ → Bool) :
    ∀ m, (acc n d lo hi y m = true ↔ ∃ m', m' ≤ m ∧ a2 n d lo hi y m' = true)
  | 0 => by
    simp only [acc]
    constructor
    · intro h; exact ⟨0, le_refl _, h⟩
    · rintro ⟨m', h1, h2⟩
      rw [show m' = 0 by omega] at h2; exact h2
  | m + 1 => by
    rw [acc, Bool.or_eq_true, acc_iff n d lo hi y m]
    constructor
    · rintro (⟨m', h1, h2⟩ | h)
      · exact ⟨m', by omega, h2⟩
      · exact ⟨m + 1, le_refl _, h⟩
    · rintro ⟨m', h1, h2⟩
      by_cases hm : m' = m + 1
      · right; rw [← hm]; exact h2
      · left; exact ⟨m', by omega, h2⟩

noncomputable def loF (d : ℕ) (NB : ℕ → Finset ℕ) (m : ℕ) : ℕ :=
  if m % (d + 1) = 0 then m / (d + 1)
  else (NB (m / (d + 1))).toList.getD (m % (d + 1) - 1) (m / (d + 1))

theorem hiex (n : ℕ) (NB : ℕ → Finset ℕ) (p lo : ℕ) : ∃ a, lo < a ∧ (n ≤ a ∨ a ∈ NB p) :=
  ⟨n + lo + 1, by omega, Or.inl (by omega)⟩

noncomputable def hiF (n d : ℕ) (NB : ℕ → Finset ℕ) (m : ℕ) : ℕ :=
  Nat.find (hiex n NB (m / (d + 1)) (loF d NB m))

theorem lo_mem (d : ℕ) (NB : ℕ → Finset ℕ) (m : ℕ) :
    loF d NB m = m / (d + 1) ∨ loF d NB m ∈ NB (m / (d + 1)) := by
  unfold loF
  split_ifs with h
  · left; rfl
  · rw [List.getD_eq_getElem?_getD]
    rcases hh : (NB (m / (d + 1))).toList[m % (d + 1) - 1]? with _ | a
    · left; rfl
    · right
      simp only [Option.getD_some]
      exact Finset.mem_toList.1 (List.mem_of_getElem? hh)

theorem hi_spec (n d : ℕ) (NB : ℕ → Finset ℕ) (m : ℕ) :
    loF d NB m < hiF n d NB m ∧ (n ≤ hiF n d NB m ∨ hiF n d NB m ∈ NB (m / (d + 1))) := by
  unfold hiF
  exact Nat.find_spec (hiex n NB (m / (d + 1)) (loF d NB m))

theorem hi_min (n d : ℕ) (NB : ℕ → Finset ℕ) (m a : ℕ) (h1 : loF d NB m < a)
    (h2 : n ≤ a ∨ a ∈ NB (m / (d + 1))) : hiF n d NB m ≤ a := by
  unfold hiF
  exact Nat.find_min' (hiex n NB (m / (d + 1)) (loF d NB m)) ⟨h1, h2⟩

theorem sem (n d : ℕ) (NB : ℕ → Finset ℕ) (hNB : ∀ p a, a ∈ NB p → p < a ∧ a < n)
    (hcard : ∀ p, (NB p).card ≤ d) (y : ℕ → Bool) (pu pv : ℕ) (hpu : pu < n) (hpv : pv < n)
    (hy : ∀ p, y p = true ↔ (p = pu ∨ p = pv)) :
    acc n d (loF d NB) (hiF n d NB) y (n * (d + 1) - 1) = true ↔
      (pu ≠ pv ∧ max pu pv ∉ NB (min pu pv)) := by
  have hM : 1 ≤ n * (d + 1) := Nat.mul_pos (by omega) (by omega)
  rw [acc_iff]
  constructor
  · rintro ⟨m, hm, h⟩
    have hm' : m < n * (d + 1) := by omega
    have hp : m / (d + 1) < n := (Nat.div_lt_iff_lt_mul (by omega)).2 hm'
    have hlo := lo_mem d NB m
    have hlo1 : m / (d + 1) ≤ loF d NB m := by
      rcases hlo with h' | h'
      · omega
      · exact le_of_lt (hNB _ _ h').1
    have hlo2 : loF d NB m < n := by
      rcases hlo with h' | h'
      · omega
      · exact (hNB _ _ h').2
    simp only [a2, a1, Bool.and_eq_true] at h
    obtain ⟨⟨hyp, hS⟩, hT⟩ := h
    rw [Sf_iff n y _ (by omega)] at hS
    obtain ⟨q, hq1, hq2, hyq⟩ := hS
    rw [Tf_iff] at hT
    obtain ⟨a, b, hab, hb, hya, hyb⟩ := hT
    rw [hy] at hyp hyq hya hyb
    have hpq : m / (d + 1) < q := by omega
    refine ⟨by omega, fun hmem => ?_⟩
    rw [show max pu pv = q by omega, show min pu pv = m / (d + 1) by omega] at hmem
    have := hi_min n d NB m q (by omega) (Or.inr hmem)
    omega
  · rintro ⟨hne, hmem⟩
    set p := min pu pv with hpdef
    set q := max pu pv with hqdef
    have hpq : p < q := by omega
    have hpn : p < n := by omega
    have hqn : q < n := by omega
    let F := (insert p (NB p)).filter (fun a => a < q)
    have hpF : p ∈ F := Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hpq⟩
    let lo0 := F.max' ⟨p, hpF⟩
    have hlo0F : lo0 ∈ F := Finset.max'_mem _ _
    have hlo0q : lo0 < q := (Finset.mem_filter.1 hlo0F).2
    have hlo0p : p ≤ lo0 := Finset.le_max' _ _ hpF
    -- a slot whose low end is lo0
    have hslot : ∃ m, m < n * (d + 1) ∧ m / (d + 1) = p ∧ loF d NB m = lo0 := by
      have hdiv : ∀ t, t < d + 1 → (t + p * (d + 1)) / (d + 1) = p := by
        intro t ht
        rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]
      have hmod : ∀ t, t < d + 1 → (t + p * (d + 1)) % (d + 1) = t := by
        intro t ht
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
      have hb : (p + 1) * (d + 1) ≤ n * (d + 1) := Nat.mul_le_mul_right _ hpn
      have hb' : (p + 1) * (d + 1) = p * (d + 1) + (d + 1) := by ring
      rcases Finset.mem_insert.1 (Finset.mem_filter.1 hlo0F).1 with he | he
      · refine ⟨0 + p * (d + 1), by omega, hdiv 0 (by omega), ?_⟩
        unfold loF
        rw [hmod 0 (by omega), if_pos rfl, hdiv 0 (by omega), he]
      · obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 he)
        have hil : i < d := by
          have := Finset.length_toList (NB p)
          have := hcard p
          omega
        refine ⟨(i + 1) + p * (d + 1), by omega, hdiv (i + 1) (by omega), ?_⟩
        unfold loF
        rw [hmod (i + 1) (by omega), if_neg (by omega), hdiv (i + 1) (by omega),
          show i + 1 - 1 = i by omega, List.getD_eq_getElem _ _ hi, hie]
    obtain ⟨m, hm, hmp, hml⟩ := hslot
    refine ⟨m, by omega, ?_⟩
    have hhq : q < hiF n d NB m := by
      rcases Nat.lt_or_ge q (hiF n d NB m) with h | h
      · exact h
      · exfalso
        obtain ⟨hs1, hs2⟩ := hi_spec n d NB m
        rw [hmp] at hs2
        rcases hs2 with hs2 | hs2
        · omega
        · have hne' : hiF n d NB m ≠ q := fun e => hmem (e ▸ hs2)
          have hinF : hiF n d NB m ∈ F :=
            Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem hs2, by omega⟩
          have := Finset.le_max' _ _ hinF
          rw [hml] at hs1
          omega
    have hyp : y p = true := (hy p).2 (by omega)
    have hyq : y q = true := (hy q).2 (by omega)
    simp only [a2, a1, Bool.and_eq_true]
    refine ⟨⟨by rw [hmp]; exact hyp, ?_⟩, ?_⟩
    · rw [Sf_iff n y _ (by omega)]
      exact ⟨q, by omega, hqn, hyq⟩
    · rw [Tf_iff]
      exact ⟨p, q, hpq, hhq, hyp, hyq⟩

/-! ### The graph side -/

def NBf (n : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n)) (p : ℕ) : Finset ℕ :=
  if hp : p < n then
    (Finset.univ.filter (fun j : Fin n => rank (rank.symm ⟨p, hp⟩) < rank j ∧
      (G (rank.symm ⟨p, hp⟩) j = true ∨ G j (rank.symm ⟨p, hp⟩) = true))).image
      (fun j => (rank j).val)
  else ∅

def ywf (n : ℕ) (rank : Equiv.Perm (Fin n)) (p : ℕ) : ℕ :=
  if hp : p < n then (rank.symm ⟨p, hp⟩).val else 0

theorem NB_sub (n : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n)) :
    ∀ p a, a ∈ NBf n G rank p → p < a ∧ a < n := by
  intro p a h
  unfold NBf at h
  split_ifs at h with hp
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
    have h1 := (Finset.mem_filter.1 hj).2.1
    rw [Equiv.apply_symm_apply] at h1
    exact ⟨Fin.lt_def.1 h1, (rank j).isLt⟩
  · simp at h

theorem NB_card (n d : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n))
    (hdeg : ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n =>
      rank i < rank j ∧ (G i j = true ∨ G j i = true))).card ≤ d) :
    ∀ p, (NBf n G rank p).card ≤ d := by
  intro p
  unfold NBf
  split_ifs with hp
  · exact Finset.card_image_le.trans (hdeg _)
  · simp

theorem NB_mem (n : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n)) (a b : Fin n)
    (hab : rank a < rank b) :
    (rank b).val ∈ NBf n G rank (rank a).val ↔ (G a b = true ∨ G b a = true) := by
  unfold NBf
  rw [dif_pos (rank a).isLt]
  simp only [Fin.eta, Equiv.symm_apply_apply]
  constructor
  · intro h
    obtain ⟨j, hj, hjb⟩ := Finset.mem_image.1 h
    have : j = b := rank.injective (Fin.ext hjb)
    subst this
    exact (Finset.mem_filter.1 hj).2.2
  · intro h
    exact Finset.mem_image.2 ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _, hab, h⟩, rfl⟩

end PEqualNP.Outside.L_meta_25535_aux

open PEqualNP.Outside.L_meta_25535_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25535 :
    ∀ (n d : ℕ) (G : Fin n → Fin n → Bool) (rank : Equiv.Perm (Fin n)),
      (∀ i : Fin n, (Finset.univ.filter (fun j : Fin n =>
        rank i < rank j ∧ (G i j = true ∨ G j i = true))).card ≤ d) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
        D.output < n + D.size ∧ D.size ≤ 8 * (n + 1) * (2 * d + 1) + 2 ∧
        ∀ u v : Fin n,
          D.eval (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))) =
            decide (u ≠ v ∧ G u v = false ∧ G v u = false) := by
  intro n d G rank hdeg
  have hNB := NB_sub n G rank
  have hcard := NB_card n d G rank hdeg
  have hlo : ∀ m < n * (d + 1), loF d (NBf n G rank) m < n := by
    intro m hm
    have hp : m / (d + 1) < n := (Nat.div_lt_iff_lt_mul (by omega)).2 hm
    rcases lo_mem d (NBf n G rank) m with h | h
    · omega
    · exact (hNB _ _ h).2
  have hhi : ∀ m < n * (d + 1), hiF n d (NBf n G rank) m ≤ n := by
    intro m hm
    exact hi_min n d _ m n (hlo m hm) (Or.inl le_rfl)
  have hyw0 : ∀ p, ywf n rank p < n ∨ ywf n rank p = 0 := by
    intro p
    unfold ywf
    split_ifs
    · left; exact Fin.isLt _
    · right; rfl
  have hyw : ∀ p < n, ywf n rank p < n := by
    intro p hp
    unfold ywf
    rw [dif_pos hp]
    exact Fin.isLt _
  refine ⟨prog (gt n d (ywf n rank) (loF d (NBf n G rank)) (hiF n d (NBf n G rank))) (NN n d)
    (n + NN n d - 1), gt_mono _ _ _ _ _ _ _, prog_readsBack _ _ _ _ (gt_reads _ _ _ _ _ hyw0 hhi),
    ?_, ?_, ?_⟩
  · rw [prog_output, prog_size]; unfold NN; omega
  · rw [prog_size]
    unfold NN
    have h1 : n * (d + 1) ≤ (n + 1) * (2 * d + 1) := Nat.mul_le_mul (by omega) (by omega)
    have h2 : n + 1 ≤ (n + 1) * (2 * d + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h3 : 8 * (n + 1) * (2 * d + 1) = 8 * ((n + 1) * (2 * d + 1)) := Nat.mul_assoc _ _ _
    omega
  · intro u v
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
    let y : ℕ → Bool := fun p =>
      if hp : p < n then decide (rank.symm ⟨p, hp⟩ = u ∨ rank.symm ⟨p, hp⟩ = v) else false
    have hy : ∀ p < n, (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v))).getD
        (ywf n rank p) false = y p := by
      intro p hp
      simp only [ywf, y, dif_pos hp, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp
    rw [build_eval n d _ _ _ y _ (by simp) hn hyw hyw0 hy hhi]
    have hyy : ∀ p, y p = true ↔ (p = (rank u).val ∨ p = (rank v).val) := by
      intro p
      by_cases hp : p < n
      · simp only [y, dif_pos hp, decide_eq_true_eq, Equiv.symm_apply_eq, Fin.ext_iff]
      · simp only [y, dif_neg hp]
        have := (rank u).isLt
        have := (rank v).isLt
        constructor
        · intro h; exact absurd h (by simp)
        · intro h; omega
    apply Bool.eq_iff_iff.2
    rw [sem n d _ hNB hcard y _ _ (rank u).isLt (rank v).isLt hyy, decide_eq_true_iff]
    rcases lt_trichotomy (rank u) (rank v) with h | h | h
    · have hlt := Fin.lt_def.1 h
      rw [Nat.max_eq_right (le_of_lt hlt), Nat.min_eq_left (le_of_lt hlt), NB_mem n G rank u v h]
      have hne : u ≠ v := fun e => by subst e; exact lt_irrefl _ h
      simp only [ne_eq, not_or, Bool.not_eq_true, hne, not_false_eq_true, true_and]
      constructor
      · rintro ⟨_, h1⟩; exact h1
      · intro h1; exact ⟨by omega, h1⟩
    · have huv : u = v := rank.injective h
      subst huv
      simp
    · have hlt := Fin.lt_def.1 h
      rw [Nat.max_eq_left (le_of_lt hlt), Nat.min_eq_right (le_of_lt hlt), NB_mem n G rank v u h]
      have hne : u ≠ v := fun e => by subst e; exact lt_irrefl _ h
      simp only [ne_eq, not_or, Bool.not_eq_true, hne, not_false_eq_true, true_and]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2, h1⟩
