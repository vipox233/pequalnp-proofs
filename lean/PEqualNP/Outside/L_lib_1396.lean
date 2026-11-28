import Mathlib
import PEqualNP.Defs

-- Detecting an edge of each of several graphs through an interface of r bits computed without NOT from
-- the part of the selection inside S, and decoded without NOT together with the outside part.
--
-- From the two circuits to the colouring: a circuit without NOT is monotone in its inputs (`mono_run`).
-- For an obstruction pair (A, B) the decoder answers true on A and false on B in the same outside
-- context, so some interface bit is true on A and false on B; that bit is the colour. If two pairs
-- (A, B), (P, Q) had the same colour and A inside Q, the bit would be true on Q.
--
-- From the colouring to the circuits: bit c is true on X when some obstruction pair of colour c has its
-- first set inside X. The decoder for graph t is true on (bits, outside set Y) when some inside set A0
-- and outside set B0 inside Y contain an edge of t together and every bit true on A0 is given as true.
-- Both are ORs of ANDs of inputs, built as circuits of AND and OR gates with two inputs: one chain of ANDs
-- per term, one chain of ORs per output, values computed chain by chain (`bank_val`, `dnf_val`).
-- Correctness of the decoder (`dom`): if the bits of A0 are among those of A and A0 with B0 contains an
-- edge of t while A with B does not, the edge has at most one end outside, giving an outside set Y of at
-- most one vertex inside B; shrink A0 to a minimal set that still contains an edge with Y and enlarge A
-- to a maximal subset of S that still does not. This is an obstruction pair (A1, B1); its colour is a bit
-- of A0, hence of A, so some pair (P, Q) of that colour has P inside A, inside B1: excluded.

namespace PEqualNP.Outside.L_lib_1396

open PEqualNP.CircuitLowerBounds

theorem ifT {α : Type} (c : Prop) [Decidable c] (x y : α) (h : c) : (if c then x else y) = x := by
  simp [h]

theorem ifF {α : Type} (c : Prop) [Decidable c] (x y : α) (h : ¬ c) : (if c then x else y) = y := by
  simp [h]

theorem iff_of_eq_decide {b : Bool} {P : Prop} [Decidable P] (h : b = decide P) : (b = true ↔ P) := by
  rw [h]; exact decide_eq_true_iff

theorem eq_decide_of_iff {b : Bool} {P : Prop} [Decidable P] (h : b = true ↔ P) : b = decide P := by
  cases b <;> by_cases hp : P <;> simp_all

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def Run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem Run_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    Run (gs ++ [g]) w = Run gs w ++ [g.op.eval (g.inputs.map fun i => (Run gs w).getD i false)] := by
  simp [Run, List.foldl_append]

theorem Run_append (l1 l2 : List Gate) (w : List Bool) : Run (l1 ++ l2) w = Run l2 (Run l1 w) := by
  simp [Run, List.foldl_append]

theorem Run_len (gs : List Gate) (w : List Bool) : (Run gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Run]
  | append_singleton gs g ih => rw [Run_snoc]; simp [ih]; omega

theorem getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem new_wire (gs : List Gate) (g : Gate) (w : List Bool) :
    (Run (gs ++ [g]) w).getD (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun t => (Run gs w).getD t false) := by
  rw [Run_snoc, getD_snoc]; simp [Run_len]

theorem old_wire (gs : List Gate) (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ≠ w.length + gs.length) :
    (Run (gs ++ [g]) w).getD i false = (Run gs w).getD i false := by
  rw [Run_snoc, getD_snoc]; simp [Run_len, hi]

/-- A list of gates given by a rule computes a table of values if every gate does. -/
theorem Run_spec (Ev : ℕ → Bool) (f : ℕ → Gate) (xs : List Bool)
    (hxs : ∀ w < xs.length, xs.getD w false = Ev w) :
    ∀ m : ℕ, (∀ j < m, (f j).op.eval ((f j).inputs.map Ev) = Ev (xs.length + j)) →
      (∀ j < m, ∀ a ∈ (f j).inputs, a < xs.length + j) →
      ∀ w < xs.length + m, (Run ((List.range m).map f) xs).getD w false = Ev w := by
  intro m
  induction m with
  | zero =>
    intro _ _ w hw
    simpa [Run] using hxs w (by omega)
  | succ m ih =>
    intro hev hin w hw
    have ih' := ih (fun j hj => hev j (by omega)) (fun j hj => hin j (by omega))
    rw [List.range_succ, List.map_append, List.map_singleton]
    have hlen : ((List.range m).map f).length = m := by simp
    by_cases hwm : w = xs.length + m
    · rw [hwm]
      have hnw := new_wire ((List.range m).map f) (f m) xs
      rw [hlen] at hnw
      rw [hnw, ← hev m (by omega)]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih' a (hin m (by omega) a ha)
    · have how := old_wire ((List.range m).map f) (f m) xs w (by rw [hlen]; exact hwm)
      rw [how]
      exact ih' w (by omega)

theorem rb_of (N : ℕ) (C : Circuit)
    (h : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ x ∈ g.inputs, x < N + j) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N C := by
  intro j hj i hi
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hi
  exact h j _ (List.getElem?_eq_getElem hj) i hi

theorem rb_append (L : ℕ) (l1 l2 : List Gate)
    (h1 : ∀ (j : ℕ) (g : Gate), l1[j]? = some g → ∀ x ∈ g.inputs, x < L + j)
    (h2 : ∀ (j : ℕ) (g : Gate), l2[j]? = some g → ∀ x ∈ g.inputs, x < L + l1.length + j) :
    ∀ (j : ℕ) (g : Gate), (l1 ++ l2)[j]? = some g → ∀ x ∈ g.inputs, x < L + j := by
  intro j g hg x hx
  rw [List.getElem?_append] at hg
  split_ifs at hg with c
  · exact h1 j g hg x hx
  · have h3 := h2 (j - l1.length) g hg x hx
    omega

theorem and_eval (l : List Bool) : GateOp.and.eval l = true ↔ ∀ b ∈ l, b = true := by
  simp [GateOp.eval]

theorem or_eval (l : List Bool) : GateOp.or.eval l = true ↔ ∃ b ∈ l, b = true := by
  simp [GateOp.eval]

/-! ### Chains of one operation -/

/-- A chain: an empty gate, then each gate reads the previous one and a chosen wire. -/
def chain (o : GateOp) (L : ℕ) (sel : ℕ → ℕ) : ℕ → Gate
  | 0 => ⟨o, []⟩
  | i + 1 => ⟨o, [L + i, sel i]⟩

theorem eval_snoc (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (l : List Bool) (b : Bool) :
    o.eval [o.eval l, b] = o.eval (l ++ [b]) := by
  rcases ho with rfl | rfl <;> simp [GateOp.eval]

/-- The values after a chain is added to the wire list `xs`. -/
def chEv (o : GateOp) (xs : List Bool) (sel : ℕ → ℕ) (w : ℕ) : Bool :=
  if w < xs.length then xs.getD w false
  else o.eval ((List.range (w - xs.length)).map fun i => xs.getD (sel i) false)

theorem chEv_old (o : GateOp) (xs : List Bool) (sel : ℕ → ℕ) (w : ℕ) (hw : w < xs.length) :
    chEv o xs sel w = xs.getD w false := by
  unfold chEv; rw [ifT _ _ _ hw]

theorem chEv_new (o : GateOp) (xs : List Bool) (sel : ℕ → ℕ) (j : ℕ) :
    chEv o xs sel (xs.length + j) = o.eval ((List.range j).map fun i => xs.getD (sel i) false) := by
  unfold chEv; rw [ifF _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem chain_val (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (xs : List Bool)
    (sel : ℕ → ℕ) (m : ℕ) (hsel : ∀ i < m, sel i < xs.length) :
    ∀ w < xs.length + (m + 1),
      (Run ((List.range (m + 1)).map (chain o xs.length sel)) xs).getD w false = chEv o xs sel w := by
  refine Run_spec (chEv o xs sel) (chain o xs.length sel) xs
    (fun w hw => (chEv_old o xs sel w hw).symm) (m + 1) ?_ ?_
  · intro j hj
    rcases j with _ | i
    · rw [chEv_new]; rfl
    · rw [chEv_new, List.range_succ, List.map_append, List.map_singleton, ← eval_snoc o ho]
      show o.eval ([xs.length + i, sel i].map (chEv o xs sel)) = _
      rw [List.map_cons, List.map_cons, List.map_nil, chEv_new,
        chEv_old o xs sel (sel i) (hsel i (by omega))]
  · intro j hj a ha
    rcases j with _ | i
    · simp [chain] at ha
    · simp [chain] at ha
      rcases ha with rfl | rfl
      · omega
      · have h1 := hsel i (by omega); omega

theorem chain_ops (o : GateOp) (L : ℕ) (sel : ℕ → ℕ) (i : ℕ) :
    (chain o L sel i).op = o ∧ (chain o L sel i).inputs.length ≤ 2 := by
  cases i <;> exact ⟨rfl, by simp [chain]⟩

theorem chain_rb (o : GateOp) (L : ℕ) (sel : ℕ → ℕ) (m : ℕ) (hsel : ∀ i < m, sel i < L) :
    ∀ (j : ℕ) (g : Gate), ((List.range (m + 1)).map (chain o L sel))[j]? = some g →
      ∀ x ∈ g.inputs, x < L + j := by
  intro j g hg x hx
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hg
  simp only [List.getElem_map, List.getElem_range] at hx
  have hj : j < m + 1 := by simpa using hk
  rcases j with _ | i
  · simp [chain] at hx
  · simp [chain] at hx
    rcases hx with rfl | rfl
    · omega
    · have h1 := hsel i (by omega); omega

/-- `N` chains of length `c + 1`, one after the other. -/
def bank (o : GateOp) (L0 c : ℕ) (sel : ℕ → ℕ → ℕ) : ℕ → List Gate
  | 0 => []
  | N + 1 => bank o L0 c sel N ++ (List.range (c + 1)).map (chain o (L0 + N * (c + 1)) (sel N))

theorem bank_len (o : GateOp) (L0 c : ℕ) (sel : ℕ → ℕ → ℕ) :
    ∀ N, (bank o L0 c sel N).length = N * (c + 1) := by
  intro N
  induction N with
  | zero => simp [bank]
  | succ N ih =>
    show (bank o L0 c sel N ++ (List.range (c + 1)).map (chain o (L0 + N * (c + 1)) (sel N))).length = _
    rw [List.length_append, ih, List.length_map, List.length_range, Nat.add_one_mul]

theorem bank_ops (o : GateOp) (L0 c : ℕ) (sel : ℕ → ℕ → ℕ) :
    ∀ N, ∀ g ∈ bank o L0 c sel N, g.op = o ∧ g.inputs.length ≤ 2 := by
  intro N
  induction N with
  | zero => intro g hg; simp [bank] at hg
  | succ N ih =>
    intro g hg
    have hg' : g ∈ bank o L0 c sel N ++
        (List.range (c + 1)).map (chain o (L0 + N * (c + 1)) (sel N)) := hg
    rcases List.mem_append.1 hg' with h | h
    · exact ih g h
    · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
      exact chain_ops _ _ _ i

theorem bank_rb (o : GateOp) (L0 c : ℕ) (sel : ℕ → ℕ → ℕ) (hsel : ∀ a i, i < c → sel a i < L0) :
    ∀ N, ∀ (j : ℕ) (g : Gate), (bank o L0 c sel N)[j]? = some g → ∀ x ∈ g.inputs, x < L0 + j := by
  intro N
  induction N with
  | zero => intro j g hg; simp [bank] at hg
  | succ N ih =>
    show ∀ (j : ℕ) (g : Gate), (bank o L0 c sel N ++
      (List.range (c + 1)).map (chain o (L0 + N * (c + 1)) (sel N)))[j]? = some g →
      ∀ x ∈ g.inputs, x < L0 + j
    apply rb_append L0 _ _ ih
    intro j g hg x hx
    have h1 := chain_rb o (L0 + N * (c + 1)) (sel N) c
      (fun i hi => by have h2 := hsel N i hi; omega) j g hg x hx
    rw [bank_len]
    exact h1

theorem bank_val (o : GateOp) (ho : o = GateOp.and ∨ o = GateOp.or) (xs : List Bool) (c : ℕ)
    (sel : ℕ → ℕ → ℕ) (hsel : ∀ a i, i < c → sel a i < xs.length) :
    ∀ N, (Run (bank o xs.length c sel N) xs).length = xs.length + N * (c + 1) ∧
      (∀ w < xs.length, (Run (bank o xs.length c sel N) xs).getD w false = xs.getD w false) ∧
      (∀ a < N, (Run (bank o xs.length c sel N) xs).getD (xs.length + a * (c + 1) + c) false =
        o.eval ((List.range c).map fun i => xs.getD (sel a i) false)) := by
  intro N
  induction N with
  | zero =>
    refine ⟨?_, fun w _ => rfl, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
    show (Run [] xs).length = _
    simp [Run]
  | succ N ih =>
    obtain ⟨hlen, hold, hterm⟩ := ih
    have hrun : Run (bank o xs.length c sel (N + 1)) xs =
        Run ((List.range (c + 1)).map
          (chain o (Run (bank o xs.length c sel N) xs).length (sel N)))
          (Run (bank o xs.length c sel N) xs) := by
      rw [hlen]
      exact Run_append _ _ _
    have hv := chain_val o ho (Run (bank o xs.length c sel N) xs) (sel N) c
      (fun i hi => by rw [hlen]; have h2 := hsel N i hi; omega)
    rw [hrun]
    refine ⟨?_, ?_, ?_⟩
    · rw [Run_len, hlen, List.length_map, List.length_range, Nat.add_one_mul, Nat.add_assoc]
    · intro w hw
      rw [hv w (by rw [hlen]; omega), chEv_old _ _ _ _ (by rw [hlen]; omega)]
      exact hold w hw
    · intro a ha
      by_cases h : a < N
      · have hmul : (a + 1) * (c + 1) ≤ N * (c + 1) := Nat.mul_le_mul_right _ h
        rw [Nat.add_one_mul] at hmul
        rw [hv _ (by rw [hlen]; omega), chEv_old _ _ _ _ (by rw [hlen]; omega)]
        exact hterm a h
      · have haN : a = N := by omega
        rw [haN, ← hlen, hv _ (by omega), chEv_new]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hold _ (hsel N i (List.mem_range.1 hi))

/-! ### An OR of ANDs for every output -/

/-- `N` AND chains over `c` chosen wires each, then `m` OR chains over the chosen terms. -/
def dnfGates (Lx z c N m : ℕ) (selT : ℕ → ℕ → ℕ) (F : ℕ → ℕ → Bool) : List Gate :=
  bank GateOp.and Lx c selT N ++
    bank GateOp.or (Lx + N * (c + 1)) N
      (fun j a => if F j a = true then Lx + a * (c + 1) + c else z) m

/-- The wire of output `j`. -/
def dnfOut (Lx c N j : ℕ) : ℕ := Lx + N * (c + 1) + j * (N + 1) + N

theorem dnf_ops (Lx z c N m : ℕ) (selT : ℕ → ℕ → ℕ) (F : ℕ → ℕ → Bool) :
    ∀ g ∈ dnfGates Lx z c N m selT F,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · obtain ⟨h1, h2⟩ := bank_ops _ _ _ _ _ g h
    exact ⟨Or.inl h1, h2⟩
  · obtain ⟨h1, h2⟩ := bank_ops _ _ _ _ _ g h
    exact ⟨Or.inr h1, h2⟩

theorem dnf_len (Lx z c N m : ℕ) (selT : ℕ → ℕ → ℕ) (F : ℕ → ℕ → Bool) :
    (dnfGates Lx z c N m selT F).length = N * (c + 1) + m * (N + 1) := by
  unfold dnfGates
  rw [List.length_append, bank_len, bank_len]

theorem dnf_rb (Lx z c N m : ℕ) (selT : ℕ → ℕ → ℕ) (F : ℕ → ℕ → Bool) (hz : z < Lx)
    (hselT : ∀ a i, i < c → selT a i < Lx) :
    ∀ (j : ℕ) (g : Gate), (dnfGates Lx z c N m selT F)[j]? = some g →
      ∀ x ∈ g.inputs, x < Lx + j := by
  unfold dnfGates
  apply rb_append Lx _ _ (bank_rb GateOp.and Lx c selT hselT N)
  rw [bank_len]
  apply bank_rb GateOp.or (Lx + N * (c + 1)) N _ _ m
  intro j a ha
  have hmul : (a + 1) * (c + 1) ≤ N * (c + 1) := Nat.mul_le_mul_right _ ha
  rw [Nat.add_one_mul] at hmul
  split_ifs <;> omega

theorem dnf_out_lt (Lx z c N m : ℕ) (selT : ℕ → ℕ → ℕ) (F : ℕ → ℕ → Bool) (j : ℕ) (hj : j < m) :
    dnfOut Lx c N j < Lx + (dnfGates Lx z c N m selT F).length := by
  rw [dnf_len]
  unfold dnfOut
  have hmul : (j + 1) * (N + 1) ≤ m * (N + 1) := Nat.mul_le_mul_right _ hj
  rw [Nat.add_one_mul] at hmul
  omega

theorem dnf_val (xs : List Bool) (z c N m : ℕ) (hz : z < xs.length) (hz0 : xs.getD z false = false)
    (selT : ℕ → ℕ → ℕ) (hselT : ∀ a i, i < c → selT a i < xs.length) (F : ℕ → ℕ → Bool) (j : ℕ)
    (hj : j < m) :
    ((Run (dnfGates xs.length z c N m selT F) xs).getD (dnfOut xs.length c N j) false = true ↔
      ∃ a < N, F j a = true ∧ ∀ i < c, xs.getD (selT a i) false = true) := by
  obtain ⟨hlen1, hold1, hterm1⟩ := bank_val GateOp.and (Or.inl rfl) xs c selT hselT N
  have hsel2 : ∀ j' a, a < N → (if F j' a = true then xs.length + a * (c + 1) + c else z) <
      (Run (bank GateOp.and xs.length c selT N) xs).length := by
    intro j' a ha
    rw [hlen1]
    have hmul : (a + 1) * (c + 1) ≤ N * (c + 1) := Nat.mul_le_mul_right _ ha
    rw [Nat.add_one_mul] at hmul
    split_ifs <;> omega
  obtain ⟨-, -, hout⟩ := bank_val GateOp.or (Or.inr rfl)
    (Run (bank GateOp.and xs.length c selT N) xs) N
    (fun j' a => if F j' a = true then xs.length + a * (c + 1) + c else z) hsel2 m
  have hrun : Run (dnfGates xs.length z c N m selT F) xs =
      Run (bank GateOp.or (Run (bank GateOp.and xs.length c selT N) xs).length N
        (fun j' a => if F j' a = true then xs.length + a * (c + 1) + c else z) m)
        (Run (bank GateOp.and xs.length c selT N) xs) := by
    rw [hlen1]
    exact Run_append _ _ _
  have hidx : dnfOut xs.length c N j =
      (Run (bank GateOp.and xs.length c selT N) xs).length + j * (N + 1) + N := by
    rw [hlen1]
    rfl
  rw [hrun, hidx, hout j hj, or_eval]
  constructor
  · rintro ⟨b, hb, hbt⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    have haN := List.mem_range.1 ha
    by_cases hF : F j a = true
    · have hbt' : (Run (bank GateOp.and xs.length c selT N) xs).getD
          (xs.length + a * (c + 1) + c) false = true := by
        have h3 := hbt
        rw [ifT _ _ _ hF] at h3
        exact h3
      rw [hterm1 a haN, and_eval] at hbt'
      exact ⟨a, haN, hF, fun i hi => hbt' _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)⟩
    · exfalso
      have h3 := hbt
      rw [ifF _ _ _ hF, hold1 z hz, hz0] at h3
      exact Bool.false_ne_true h3
  · rintro ⟨a, haN, hF, hall⟩
    refine ⟨_, List.mem_map.2 ⟨a, List.mem_range.2 haN, rfl⟩, ?_⟩
    show (Run (bank GateOp.and xs.length c selT N) xs).getD
      (if F j a = true then xs.length + a * (c + 1) + c else z) false = true
    rw [ifT _ _ _ hF, hterm1 a haN, and_eval]
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact hall i (List.mem_range.1 hi)

/-! ### Inputs given by a function -/

theorem ofFn_getD {k : ℕ} (f : Fin k → Bool) (tl : List Bool) (w : ℕ) (hw : w < k) :
    (List.ofFn f ++ tl).getD w false = f ⟨w, hw⟩ := by
  rw [List.getD_append _ _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

theorem ofFn_getD_right {k : ℕ} (f : Fin k → Bool) (tl : List Bool) (d : ℕ) :
    (List.ofFn f ++ tl).getD (k + d) false = tl.getD d false := by
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem inp_mono {k : ℕ} (f g : Fin k → Bool) (tl : List Bool) (h : ∀ i, f i = true → g i = true) :
    ∀ w, (List.ofFn f ++ tl).getD w false = true → (List.ofFn g ++ tl).getD w false = true := by
  intro w hw
  by_cases hk : w < k
  · rw [ofFn_getD f tl w hk] at hw
    rw [ofFn_getD g tl w hk]
    exact h _ hw
  · obtain ⟨d, rfl⟩ : ∃ d, w = k + d := ⟨w - k, by omega⟩
    rw [ofFn_getD_right] at hw ⊢
    exact hw

/-- The wire chosen for position `i` of term `a`: the input itself, or the constant true. -/
def selOf {k : ℕ} (Ts : List (Finset (Fin k))) (a i : ℕ) : ℕ :=
  if (∃ h : i < k, (⟨i, h⟩ : Fin k) ∈ Ts.getD a ∅) then i else k + 1

theorem selOf_lt {k : ℕ} (Ts : List (Finset (Fin k))) (a i : ℕ) (hi : i < k) : selOf Ts a i < k + 2 := by
  unfold selOf; split_ifs <;> omega

/-- The circuit of terms `Ts` and outputs `F` on the inputs `f`. -/
theorem termBank {k : ℕ} (Ts : List (Finset (Fin k))) (m : ℕ) (F : ℕ → ℕ → Bool) (f : Fin k → Bool)
    (j : ℕ) (hj : j < m) :
    ((Run (dnfGates (k + 2) k k Ts.length m (selOf Ts) F) (List.ofFn f ++ [false, true])).getD
        (dnfOut (k + 2) k Ts.length j) false = true ↔
      ∃ a < Ts.length, F j a = true ∧ ∀ i ∈ Ts.getD a ∅, f i = true) := by
  have hx : (List.ofFn f ++ [false, true]).length = k + 2 := by simp
  have h := dnf_val (List.ofFn f ++ [false, true]) k k Ts.length m (by rw [hx]; omega)
    (ofFn_getD_right f [false, true] 0) (selOf Ts)
    (fun a i hi => by rw [hx]; exact selOf_lt Ts a i hi) F j hj
  rw [hx] at h
  rw [h]
  constructor
  · rintro ⟨a, ha, hF, hall⟩
    refine ⟨a, ha, hF, fun i hi => ?_⟩
    have h1 := hall i.val i.isLt
    have hsel : selOf Ts a i.val = i.val := by
      unfold selOf; rw [ifT _ _ _ ⟨i.isLt, hi⟩]
    rw [hsel, ofFn_getD f _ i.val i.isLt] at h1
    exact h1
  · rintro ⟨a, ha, hF, hall⟩
    refine ⟨a, ha, hF, fun i hi => ?_⟩
    by_cases hm : ∃ h : i < k, (⟨i, h⟩ : Fin k) ∈ Ts.getD a ∅
    · obtain ⟨h1, h2⟩ := hm
      have hsel : selOf Ts a i = i := by
        unfold selOf; rw [ifT _ _ _ ⟨h1, h2⟩]
      rw [hsel, ofFn_getD f _ i h1]
      exact hall _ h2
    · have hsel : selOf Ts a i = k + 1 := by
        unfold selOf; rw [ifF _ _ _ hm]
      rw [hsel, ofFn_getD_right f [false, true] 1]
      rfl

theorem idx_of {α : Type} [Fintype α] (x : α) :
    ∃ a < (Finset.univ : Finset α).toList.length, (Finset.univ : Finset α).toList[a]? = some x := by
  have hm : x ∈ (Finset.univ : Finset α).toList := Finset.mem_toList.2 (Finset.mem_univ x)
  obtain ⟨a, ha, e⟩ := List.mem_iff_getElem.1 hm
  exact ⟨a, ha, by rw [List.getElem?_eq_getElem ha, e]⟩

/-! ### Circuits without NOT are monotone -/

theorem mono_run : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ (xs ys : List Bool), xs.length = ys.length →
      (∀ w, xs.getD w false = true → ys.getD w false = true) →
      ∀ w, (Run gs xs).getD w false = true → (Run gs ys).getD w false = true := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil => intro _ xs ys _ hle; exact hle
  | append_singleton gs g ih =>
    intro hops xs ys hlen hle w hw
    have ih' := ih (fun g' hg' => hops g' (List.mem_append_left _ hg')) xs ys hlen hle
    rw [Run_snoc, getD_snoc, Run_len] at hw ⊢
    by_cases hwl : w = xs.length + gs.length
    · rw [ifT _ _ _ hwl] at hw
      rw [ifT _ _ _ (by rw [← hlen]; exact hwl)]
      rcases hops g (by simp) with ho | ho
      · rw [ho, and_eval] at hw ⊢
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        exact ih' i (hw _ (List.mem_map.2 ⟨i, hi, rfl⟩))
      · rw [ho, or_eval] at hw ⊢
        obtain ⟨b, hb, hbt⟩ := hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
        exact ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, ih' i hbt⟩
    · rw [ifF _ _ _ hwl] at hw
      rw [ifF _ _ _ (by rw [← hlen]; exact hwl)]
      exact ih' w hw

theorem ops_of (C : Circuit) (hF : PEqualNP.MetaComplexity.FanInTwo C)
    (hN : PEqualNP.NotBracket.notCount C = 0) :
    ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
  intro g hg
  have h1 := (hF g hg).1
  unfold PEqualNP.NotBracket.notCount at hN
  have h2 := List.filter_eq_nil_iff.1 (List.length_eq_zero_iff.1 hN) g hg
  simp only [decide_eq_true_eq] at h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  rcases h1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h2

theorem fan_of (C : Circuit)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  obtain ⟨h1, h2⟩ := h g hg
  refine ⟨?_, h2⟩
  rcases h1 with h1 | h1 <;> rw [h1] <;> simp

theorem nc_of (C : Circuit)
    (h : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    PEqualNP.NotBracket.notCount C = 0 := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g hg
  simp only [decide_eq_true_eq]
  intro hnot
  rcases (h g hg).1 with h1 | h1 <;> rw [h1] at hnot <;> simp at hnot

/-! ### Graphs -/

variable {n q : ℕ}

/-- `A` contains an edge of graph `t`. -/
abbrev hit (E : Fin q → Fin n → Fin n → Bool) (t : Fin q) (A : Finset (Fin n)) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, E t u v = true

theorem hit_mono {E : Fin q → Fin n → Fin n → Bool} {t : Fin q} {A A' : Finset (Fin n)}
    (h : A ⊆ A') (hA : hit E t A) : hit E t A' := by
  obtain ⟨u, hu, v, hv, e⟩ := hA
  exact ⟨u, h hu, v, h hv, e⟩

/-- The obstruction pairs. -/
def ob (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)) (A B : Finset (Fin n)) : Prop :=
  A ⊆ S ∧ B ⊆ S ∧
    ∃ (t : Fin q) (Y : Finset (Fin n)), Disjoint S Y ∧ Y.card ≤ 1 ∧
      hit E t (A ∪ Y) ∧ (∀ i ∈ A, ¬hit E t (A.erase i ∪ Y)) ∧
      ¬hit E t (B ∪ Y) ∧ (∀ i ∈ S \ B, hit E t (insert i B ∪ Y))

theorem shrink (p : Finset (Fin n) → Prop) :
    ∀ (k : ℕ) (A0 : Finset (Fin n)), A0.card = k → p A0 →
      ∃ A1, A1 ⊆ A0 ∧ p A1 ∧ ∀ i ∈ A1, ¬ p (A1.erase i) := by
  intro k
  induction k with
  | zero =>
    intro A0 hc hp
    refine ⟨A0, Finset.Subset.refl _, hp, fun i hi => ?_⟩
    rw [Finset.card_eq_zero.1 hc] at hi
    exact absurd hi (Finset.notMem_empty i)
  | succ k ih =>
    intro A0 hc hp
    by_cases h : ∃ i ∈ A0, p (A0.erase i)
    · obtain ⟨i, hi, hpi⟩ := h
      obtain ⟨A1, h1, h2, h3⟩ := ih (A0.erase i)
        (by rw [Finset.card_erase_of_mem hi, hc, Nat.add_sub_cancel]) hpi
      exact ⟨A1, h1.trans (Finset.erase_subset _ _), h2, h3⟩
    · exact ⟨A0, Finset.Subset.refl _, hp, fun i hi hpi => h ⟨i, hi, hpi⟩⟩

theorem grow (S : Finset (Fin n)) (p : Finset (Fin n) → Prop) :
    ∀ (k : ℕ) (B0 : Finset (Fin n)), (S \ B0).card = k → B0 ⊆ S → ¬ p B0 →
      ∃ B1, B0 ⊆ B1 ∧ B1 ⊆ S ∧ ¬ p B1 ∧ ∀ i ∈ S \ B1, p (insert i B1) := by
  intro k
  induction k with
  | zero =>
    intro B0 hc hB hp
    refine ⟨B0, Finset.Subset.refl _, hB, hp, fun i hi => ?_⟩
    rw [Finset.card_eq_zero.1 hc] at hi
    exact absurd hi (Finset.notMem_empty i)
  | succ k ih =>
    intro B0 hc hB hp
    by_cases h : ∃ i ∈ S \ B0, ¬ p (insert i B0)
    · obtain ⟨i, hi, hpi⟩ := h
      have hiS : i ∈ S := (Finset.mem_sdiff.1 hi).1
      obtain ⟨B1, h1, h2, h3, h4⟩ := ih (insert i B0)
        (by rw [Finset.sdiff_insert, Finset.card_erase_of_mem hi, hc, Nat.add_sub_cancel])
        (Finset.insert_subset hiS hB) hpi
      exact ⟨B1, (Finset.subset_insert i B0).trans h1, h2, h3, h4⟩
    · refine ⟨B0, Finset.Subset.refl _, hB, hp, fun i hi => ?_⟩
      by_contra hc'
      exact h ⟨i, hi, hc'⟩

/-- If every colour seen below `A0` is seen below `A`, an edge found with `A0` is found with `A`. -/
theorem dom (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n))
    (tag : Finset (Fin n) → Finset (Fin n) → ℕ)
    (hproper : ∀ A B P Q, ob E S A B → ob E S P Q → A ⊆ Q ∨ P ⊆ B → tag A B ≠ tag P Q)
    (t : Fin q) (A A0 B B0 : Finset (Fin n)) (hA : A ⊆ S) (hA0 : A0 ⊆ S) (hB : Disjoint S B)
    (hB0 : B0 ⊆ B)
    (hcode : ∀ c, (∃ P Q, ob E S P Q ∧ tag P Q = c ∧ P ⊆ A0) →
      ∃ P Q, ob E S P Q ∧ tag P Q = c ∧ P ⊆ A)
    (hh : hit E t (A0 ∪ B0)) : hit E t (A ∪ B) := by
  by_contra hnot
  obtain ⟨u, hu, v, hv, e⟩ := hh
  obtain ⟨Y, hYS, hYc, hYB, hYh⟩ : ∃ Y : Finset (Fin n),
      Disjoint S Y ∧ Y.card ≤ 1 ∧ Y ⊆ B ∧ hit E t (A0 ∪ Y) := by
    rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
    · exact ⟨∅, Finset.disjoint_empty_right S, by simp, Finset.empty_subset B,
        u, Finset.mem_union_left _ hu, v, Finset.mem_union_left _ hv, e⟩
    · exact ⟨{v}, Finset.disjoint_singleton_right.2 (Finset.disjoint_right.1 hB (hB0 hv)),
        by simp, Finset.singleton_subset_iff.2 (hB0 hv),
        u, Finset.mem_union_left _ hu, v, Finset.mem_union_right _ (Finset.mem_singleton_self v), e⟩
    · exact ⟨{u}, Finset.disjoint_singleton_right.2 (Finset.disjoint_right.1 hB (hB0 hu)),
        by simp, Finset.singleton_subset_iff.2 (hB0 hu),
        u, Finset.mem_union_right _ (Finset.mem_singleton_self u), v, Finset.mem_union_left _ hv, e⟩
    · exact absurd ⟨u, Finset.mem_union_right _ (hB0 hu), v, Finset.mem_union_right _ (hB0 hv), e⟩
        hnot
  have hnY : ¬ hit E t (A ∪ Y) := fun h =>
    hnot (hit_mono (Finset.union_subset_union (Finset.Subset.refl A) hYB) h)
  obtain ⟨A1, hA1, hA1h, hA1min⟩ := shrink (fun X => hit E t (X ∪ Y)) A0.card A0 rfl hYh
  obtain ⟨B1, hAB1, hB1S, hB1n, hB1max⟩ :=
    grow S (fun X => hit E t (X ∪ Y)) (S \ A).card A rfl hA hnY
  have hob : ob E S A1 B1 :=
    ⟨hA1.trans hA0, hB1S, t, Y, hYS, hYc, hA1h, hA1min, hB1n, hB1max⟩
  obtain ⟨P, Q, hobPQ, htagPQ, hPA⟩ := hcode (tag A1 B1) ⟨A1, B1, hob, rfl, hA1⟩
  exact hproper A1 B1 P Q hob hobPQ (Or.inr (hPA.trans hAB1)) htagPQ.symm

/-! ### The two directions -/

/-- The interface bits of the inside selection `A`. -/
def codeOf (C : Circuit) (r n : ℕ) (tap : Fin r → ℕ) (A : Finset (Fin n)) (i : Fin r) : Bool :=
  (Run C.gates (List.ofFn (fun i : Fin n => decide (i ∈ A)) ++ [false, true])).getD (tap i) false

theorem forward (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)) (r : ℕ)
    (C D : Circuit) (tap : Fin r → ℕ) (out : Fin q → ℕ)
    (hCops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hDops : ∀ g ∈ D.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfit : ∀ A, A ⊆ S → ∀ B, Disjoint S B → ∀ t,
      ((Run D.gates (List.ofFn (codeOf C r n tap A) ++
        List.ofFn (fun i : Fin n => decide (i ∈ B)) ++ [false, true])).getD (out t) false = true ↔
        hit E t (A ∪ B))) :
    ∃ tag : Finset (Fin n) → Finset (Fin n) → ℕ,
      (∀ A B, ob E S A B → tag A B < r) ∧
      ∀ A B P Q, ob E S A B → ob E S P Q → A ⊆ Q ∨ P ⊆ B → tag A B ≠ tag P Q := by
  have monoC : ∀ A A' : Finset (Fin n), A ⊆ A' → ∀ i,
      codeOf C r n tap A i = true → codeOf C r n tap A' i = true := by
    intro A A' hAA i h
    unfold codeOf at h ⊢
    refine mono_run C.gates hCops _ _ (by simp) (inp_mono _ _ _ (fun j hj => ?_)) _ h
    exact decide_eq_true (hAA (of_decide_eq_true hj))
  have key : ∀ A B, ob E S A B →
      ∃ i : Fin r, codeOf C r n tap A i = true ∧ codeOf C r n tap B i = false := by
    rintro A B ⟨hAS, hBS, t, Y, hY, -, hhit, -, hnhit, -⟩
    by_contra hcon
    have hall : ∀ i, codeOf C r n tap A i = true → codeOf C r n tap B i = true := by
      intro i hi
      by_contra hb
      exact hcon ⟨i, hi, by simpa using hb⟩
    have h1 := (hfit A hAS Y hY t).2 hhit
    have h2 : (Run D.gates (List.ofFn (codeOf C r n tap B) ++
        List.ofFn (fun i : Fin n => decide (i ∈ Y)) ++ [false, true])).getD (out t) false = true := by
      refine mono_run D.gates hDops _ _ (by simp) ?_ _ h1
      intro w hw
      rw [List.append_assoc] at hw ⊢
      exact inp_mono _ _ _ hall w hw
    exact hnhit ((hfit B hBS Y hY t).1 h2)
  have key' : ∀ A B, ∃ k : ℕ, ob E S A B →
      ∃ i : Fin r, i.val = k ∧ codeOf C r n tap A i = true ∧ codeOf C r n tap B i = false := by
    intro A B
    by_cases h : ob E S A B
    · obtain ⟨i, h1, h2⟩ := key A B h
      exact ⟨i.val, fun _ => ⟨i, rfl, h1, h2⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose tag htag using key'
  refine ⟨tag, ?_, ?_⟩
  · intro A B hob
    obtain ⟨i, hi, -, -⟩ := htag A B hob
    rw [← hi]
    exact i.isLt
  · intro A B P Q hob hob' hor heq
    obtain ⟨i, hi, hA1, hB0⟩ := htag A B hob
    obtain ⟨i', hi', hP1, hQ0⟩ := htag P Q hob'
    have hii : i' = i := Fin.ext (by rw [hi, hi', heq])
    rw [hii] at hP1 hQ0
    rcases hor with h | h
    · have h3 := monoC A Q h i hA1
      rw [hQ0] at h3
      exact Bool.false_ne_true h3
    · have h3 := monoC P B h i hP1
      rw [hB0] at h3
      exact Bool.false_ne_true h3

theorem backward (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)) (r : ℕ)
    (tag : Finset (Fin n) → Finset (Fin n) → ℕ)
    (hlt : ∀ A B, ob E S A B → tag A B < r)
    (hproper : ∀ A B P Q, ob E S A B → ob E S P Q → A ⊆ Q ∨ P ⊆ B → tag A B ≠ tag P Q) :
    ∃ (C D : Circuit) (tap : Fin r → ℕ) (out : Fin q → ℕ),
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → ∀ x ∈ g.inputs, x < n + 2 + j) ∧
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → ∀ x ∈ g.inputs, x < r + n + 2 + j) ∧
      C.output = 0 ∧ D.output = 0 ∧
      (∀ i, tap i < n + 2 + C.gates.length) ∧ (∀ t, out t < r + n + 2 + D.gates.length) ∧
      ∀ A, A ⊆ S → ∀ B, Disjoint S B → ∀ t,
        ((Run D.gates (List.ofFn (codeOf C r n tap A) ++
          List.ofFn (fun i : Fin n => decide (i ∈ B)) ++ [false, true])).getD (out t) false = true ↔
          hit E t (A ∪ B)) := by
  classical
  -- the bits
  obtain ⟨Ts, hTs⟩ : ∃ Ts : List (Finset (Fin n)),
      Ts = (Finset.univ : Finset (Finset (Fin n))).toList := ⟨_, rfl⟩
  obtain ⟨FC, hFC⟩ : ∃ FC : ℕ → ℕ → Bool, ∀ c a, FC c a = true ↔
      ∃ P Q, ob E S P Q ∧ tag P Q = c ∧ P = Ts.getD a ∅ :=
    ⟨fun c a => decide (∃ P Q, ob E S P Q ∧ tag P Q = c ∧ P = Ts.getD a ∅),
      fun c a => decide_eq_true_iff⟩
  obtain ⟨Cg, hCg⟩ : ∃ Cg : List Gate,
      Cg = dnfGates (n + 2) n n Ts.length r (selOf Ts) FC := ⟨_, rfl⟩
  obtain ⟨tap, htap⟩ : ∃ tap : Fin r → ℕ, ∀ c, tap c = dnfOut (n + 2) n Ts.length c.val :=
    ⟨_, fun _ => rfl⟩
  have codeC : ∀ (A : Finset (Fin n)) (c : Fin r), codeOf ⟨Cg, 0⟩ r n tap A c = true ↔
      ∃ P Q, ob E S P Q ∧ tag P Q = c.val ∧ P ⊆ A := by
    intro A c
    unfold codeOf
    show (Run Cg (List.ofFn (fun i : Fin n => decide (i ∈ A)) ++ [false, true])).getD (tap c) false
      = true ↔ _
    rw [hCg, htap, termBank Ts r FC _ c.val c.isLt]
    constructor
    · rintro ⟨a, ha, hF, hall⟩
      obtain ⟨P, Q, h1, h2, h3⟩ := (hFC _ _).1 hF
      refine ⟨P, Q, h1, h2, ?_⟩
      rw [h3]
      intro i hi
      exact of_decide_eq_true (hall i hi)
    · rintro ⟨P, Q, h1, h2, h3⟩
      obtain ⟨a, ha, e⟩ := idx_of P
      rw [← hTs] at ha e
      have hP : Ts.getD a ∅ = P := by
        rw [List.getD_eq_getElem?_getD, e]
        rfl
      refine ⟨a, ha, (hFC _ _).2 ⟨P, Q, h1, h2, hP.symm⟩, fun i hi => ?_⟩
      rw [hP] at hi
      exact decide_eq_true (h3 hi)
  -- the decoder
  obtain ⟨Ps, hPs⟩ : ∃ Ps : List (Finset (Fin n) × Finset (Fin n)),
      Ps = (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).toList := ⟨_, rfl⟩
  obtain ⟨termOf, htermOf⟩ : ∃ termOf : Finset (Fin n) × Finset (Fin n) → Finset (Fin (r + n)),
      ∀ pr, termOf pr = ((Finset.univ : Finset (Fin r)).filter
        (fun c => ∃ P Q, ob E S P Q ∧ tag P Q = c.val ∧ P ⊆ pr.1)).image (Fin.castAdd n) ∪
        pr.2.image (Fin.natAdd r) := ⟨_, fun _ => rfl⟩
  obtain ⟨FD, hFD⟩ : ∃ FD : ℕ → ℕ → Bool, ∀ t a, FD t a = true ↔
      ∃ ht : t < q, ∃ A0 B0, Ps[a]? = some (A0, B0) ∧ A0 ⊆ S ∧ Disjoint S B0 ∧
        hit E ⟨t, ht⟩ (A0 ∪ B0) :=
    ⟨fun t a => decide (∃ ht : t < q, ∃ A0 B0, Ps[a]? = some (A0, B0) ∧ A0 ⊆ S ∧ Disjoint S B0 ∧
        hit E ⟨t, ht⟩ (A0 ∪ B0)), fun t a => decide_eq_true_iff⟩
  obtain ⟨Dg, hDg⟩ : ∃ Dg : List Gate,
      Dg = dnfGates (r + n + 2) (r + n) (r + n) (Ps.map termOf).length q (selOf (Ps.map termOf)) FD :=
    ⟨_, rfl⟩
  obtain ⟨out, hout⟩ : ∃ out : Fin q → ℕ,
      ∀ t, out t = dnfOut (r + n + 2) (r + n) (Ps.map termOf).length t.val := ⟨_, fun _ => rfl⟩
  refine ⟨⟨Cg, 0⟩, ⟨Dg, 0⟩, tap, out, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · rw [hCg]; exact dnf_ops _ _ _ _ _ _ _
  · rw [hCg]
    exact dnf_rb _ _ _ _ _ _ _ (by omega) (fun a i hi => selOf_lt Ts a i hi)
  · rw [hDg]; exact dnf_ops _ _ _ _ _ _ _
  · rw [hDg]
    exact dnf_rb _ _ _ _ _ _ _ (by omega) (fun a i hi => selOf_lt (Ps.map termOf) a i hi)
  · intro c
    rw [htap]
    show _ < n + 2 + Cg.length
    rw [hCg]
    exact dnf_out_lt _ _ _ _ _ _ _ c.val c.isLt
  · intro t
    rw [hout]
    show _ < r + n + 2 + Dg.length
    rw [hDg]
    exact dnf_out_lt _ _ _ _ _ _ _ t.val t.isLt
  · intro A hA B hB t
    show (Run Dg (List.ofFn (codeOf ⟨Cg, 0⟩ r n tap A) ++
      List.ofFn (fun i : Fin n => decide (i ∈ B)) ++ [false, true])).getD (out t) false = true ↔ _
    rw [← List.ofFn_fin_append, hDg, hout,
      termBank (Ps.map termOf) q FD _ t.val t.isLt]
    constructor
    · rintro ⟨a, ha, hF, hall⟩
      obtain ⟨ht, A0, B0, hPa, hA0, hB0, hh⟩ := (hFD _ _).1 hF
      have hT : (Ps.map termOf).getD a ∅ = termOf (A0, B0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hPa]
        rfl
      rw [hT, htermOf] at hall
      have hcodes : ∀ c, (∃ P Q, ob E S P Q ∧ tag P Q = c ∧ P ⊆ A0) →
          ∃ P Q, ob E S P Q ∧ tag P Q = c ∧ P ⊆ A := by
        rintro c ⟨P, Q, hobPQ, htg, hP⟩
        have hcr : c < r := by rw [← htg]; exact hlt P Q hobPQ
        have h1 := hall (Fin.castAdd n ⟨c, hcr⟩)
          (Finset.mem_union_left _ (Finset.mem_image_of_mem _
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, P, Q, hobPQ, htg, hP⟩)))
        rw [Fin.append_left] at h1
        exact (codeC A ⟨c, hcr⟩).1 h1
      have hBsub : B0 ⊆ B := by
        intro x hx
        have h1 := hall (Fin.natAdd r x) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx))
        rw [Fin.append_right] at h1
        exact of_decide_eq_true h1
      exact dom E S tag hproper t A A0 B B0 hA hA0 hB hBsub hcodes hh
    · intro hh
      obtain ⟨a, ha, e⟩ := idx_of ((A, B) : Finset (Fin n) × Finset (Fin n))
      rw [← hPs] at ha e
      have hT : (Ps.map termOf).getD a ∅ = termOf (A, B) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, e]
        rfl
      refine ⟨a, by rw [List.length_map]; exact ha, (hFD _ _).2 ⟨t.isLt, A, B, e, hA, hB, hh⟩,
        fun i hi => ?_⟩
      rw [hT, htermOf] at hi
      rcases Finset.mem_union.1 hi with hi | hi
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hi
        rw [Fin.append_left]
        exact (codeC A c).2 (Finset.mem_filter.1 hc).2
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
        rw [Fin.append_right]
        exact decide_eq_true hx

end PEqualNP.Outside.L_lib_1396

theorem PEqualNP.Outside.L_lib_1396 :
∀ (n q r : Nat) (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)),
  (∀ t u v, E t u v = E t v u) → (∀ t v, E t v v = false) →
  let hit := fun (t : Fin q) (A : Finset (Fin n)) => ∃ u ∈ A, ∃ v ∈ A, E t u v = true
  let ob := fun (A B : Finset (Fin n)) => A ⊆ S ∧ B ⊆ S ∧
    ∃ (t : Fin q) (Y : Finset (Fin n)), Disjoint S Y ∧ Y.card ≤ 1 ∧
      hit t (A ∪ Y) ∧ (∀ i ∈ A, ¬hit t (A.erase i ∪ Y)) ∧
      ¬hit t (B ∪ Y) ∧ (∀ i ∈ S \ B, hit t (insert i B ∪ Y))
  let valid := fun (k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+2) C ∧
    C.output < k+2+C.size ∧ PEqualNP.NotBracket.notCount C = 0
  (∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin r → Nat) (out : Fin q → Nat),
    valid n C ∧ valid (r+n) D ∧ (∀ i, tap i < n+2+C.size) ∧ (∀ t, out t < r+n+2+D.size) ∧
    ∀ A, A ⊆ S → ∀ B, Disjoint S B →
      let c := C.wires (List.ofFn (fun i : Fin n => decide (i ∈ A)) ++ [false,true])
      let w := D.wires (List.ofFn (fun i => c.getD (tap i) false) ++
        List.ofFn (fun i : Fin n => decide (i ∈ B)) ++ [false,true])
      ∀ t, w.getD (out t) false = decide (hit t (A ∪ B))) ↔
  ∃ tag : Finset (Fin n) → Finset (Fin n) → Nat,
    (∀ A B, ob A B → tag A B < r) ∧
    ∀ A B P Q, ob A B → ob P Q → A ⊆ Q ∨ P ⊆ B → tag A B ≠ tag P Q := by
  intro n q r E S hsym hirr hit ob valid
  constructor
  · rintro ⟨C, D, tap, out, hC, hD, -, -, hfit⟩
    exact PEqualNP.Outside.L_lib_1396.forward E S r C D tap out
      (PEqualNP.Outside.L_lib_1396.ops_of C hC.1 hC.2.2.2)
      (PEqualNP.Outside.L_lib_1396.ops_of D hD.1 hD.2.2.2)
      (fun A hA B hB t => PEqualNP.Outside.L_lib_1396.iff_of_eq_decide (hfit A hA B hB t))
  · rintro ⟨tag, h1, h2⟩
    obtain ⟨C, D, tap, out, c1, c2, d1, d2, co, dout, ht, ho, hfit⟩ :=
      PEqualNP.Outside.L_lib_1396.backward E S r tag h1 h2
    refine ⟨C, D, tap, out,
      ⟨PEqualNP.Outside.L_lib_1396.fan_of C c1, PEqualNP.Outside.L_lib_1396.rb_of _ C c2, ?_,
        PEqualNP.Outside.L_lib_1396.nc_of C c1⟩,
      ⟨PEqualNP.Outside.L_lib_1396.fan_of D d1, PEqualNP.Outside.L_lib_1396.rb_of _ D d2, ?_,
        PEqualNP.Outside.L_lib_1396.nc_of D d1⟩, ht, ho, ?_⟩
    · rw [co]; omega
    · rw [dout]; omega
    · intro A hA B hB c w t
      exact PEqualNP.Outside.L_lib_1396.eq_decide_of_iff (hfit A hA B hB t)
