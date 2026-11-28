import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50292

open PEqualNP.CircuitLowerBounds

def M1 : ℕ := 5
def M2 : ℕ := 36
def M3 : ℕ := 54
def NB : ℕ := 2

def mem (S x : ℕ) : Bool := S.testBit x
def ins (S x : ℕ) : ℕ := S ||| 2 ^ x
def hasAll (S : ℕ) : Bool := mem S M1 && mem S M2 && mem S M3
def missing (S : ℕ) : ℕ :=
  (if mem S M1 = true then 0 else 1) + (if mem S M2 = true then 0 else 1) + (if mem S M3 = true then 0 else 1)
def elems (S : ℕ) : List ℕ := (List.range 64).filter (fun x => mem S x)

def go : ℕ → ℕ → ℕ → Bool
  | 0, _, S => hasAll S
  | k + 1, nn, S => hasAll S || (decide (missing S ≤ k + 1) &&
      (go k nn S || (decide (nn < NB) && go k (nn + 1) S) ||
        (elems S).any (fun a => (elems S).any (fun b =>
          (!mem S ((a &&& (b &&& 63)) &&& 63) && go k nn (ins S ((a &&& (b &&& 63)) &&& 63))) ||
          (!mem S ((a ||| (b ||| 0)) &&& 63) && go k nn (ins S ((a ||| (b ||| 0)) &&& 63))))) ||
        (decide (nn < NB) && (elems S).any (fun a =>
          !mem S ((63 ^^^ a) &&& 63) && go k (nn + 1) (ins S ((63 ^^^ a) &&& 63))))))

theorem mem_ins (S x y : ℕ) : mem (ins S x) y = (mem S y || decide (y = x)) := by
  unfold mem ins
  rw [Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h : y = x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem go_hasAll {k nn S : ℕ} (h : hasAll S = true) : go k nn S = true := by
  cases k with
  | zero => simpa [go] using h
  | succ k => simp [go, h]

theorem missing_le_of_go {k nn S : ℕ} (h : go k nn S = true) : missing S ≤ k := by
  cases k with
  | zero =>
    simp only [go, hasAll, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp [missing, h1, h2, h3]
  | succ k =>
    simp only [go, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h, _⟩
    · simp only [hasAll, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      simp [missing, h1, h2, h3]
    · exact h

theorem missing_ins (S x : ℕ) : missing S ≤ missing (ins S x) + 1 := by
  have d12 : M1 ≠ M2 := by decide
  have d13 : M1 ≠ M3 := by decide
  have d23 : M2 ≠ M3 := by decide
  unfold missing
  simp only [mem_ins]
  by_cases a1 : mem S M1 = true <;> by_cases a2 : mem S M2 = true <;> by_cases a3 : mem S M3 = true <;>
    by_cases b1 : M1 = x <;> by_cases b2 : M2 = x <;> by_cases b3 : M3 = x <;>
    simp_all <;> omega

theorem mem_elems {S a : ℕ} (h1 : a < 64) (h2 : mem S a = true) : a ∈ elems S := by
  simp [elems, h1, h2]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def gm (ms : List ℕ) (g : Gate) : ℕ :=
  (match g.op with
    | .and => (g.inputs.map fun i => ms.getD i 0).foldr (· &&& ·) 63
    | .or => (g.inputs.map fun i => ms.getD i 0).foldr (· ||| ·) 0
    | .not => 63 ^^^ (g.inputs.map fun i => ms.getD i 0).headD 0
    | _ => 0) &&& 63

def mstep (ms : List ℕ) (g : Gate) : List ℕ := ms ++ [gm ms g]

def bstep (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def isNot (g : Gate) : ℕ := match g.op with
  | .not => 1
  | _ => 0

def nots (gs : List Gate) : ℕ := (gs.map isNot).sum

theorem isNot01 (g : Gate) : isNot g = 0 ∨ isNot g = 1 := by
  unfold isNot; split <;> simp

theorem nots_filter (gs : List Gate) : ∀ (p : Gate → Bool), (∀ g, p g = true ↔ g.op = GateOp.not) →
    (gs.filter p).length = nots gs := by
  induction gs with
  | nil => intro p _; rfl
  | cons g gs ih =>
    intro p hp
    simp only [List.filter_cons, nots, List.map_cons, List.sum_cons]
    have ih' := ih p hp
    unfold nots at ih'
    by_cases h : g.op = GateOp.not
    · have : p g = true := (hp g).mpr h
      have hi : isNot g = 1 := by unfold isNot; rw [h]
      simp [this, hi, ih']; omega
    · have : p g = false := by
        cases hq : p g
        · rfl
        · exact absurd ((hp g).mp hq) h
      have hi : isNot g = 0 := by
        unfold isNot; split
        · rename_i hh; exact absurd hh h
        · rfl
      simp [this, hi, ih']

theorem t63 (t : Fin 6) : (63 : ℕ).testBit t.val = true := by
  revert t; decide

theorem t0 (t : ℕ) : (0 : ℕ).testBit t = false := Nat.zero_testBit t

theorem read_bit (ms : List ℕ) (i : ℕ) (t : ℕ) :
    (ms.map fun x => x.testBit t).getD i false = (ms.getD i 0).testBit t := by
  by_cases h : i < ms.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h)]

set_option maxRecDepth 5000 in
theorem gm_bit (ms : List ℕ) (g : Gate) (hg : legal g) (t : Fin 6) :
    (gm ms g).testBit t.val = g.op.eval (g.inputs.map fun i => (ms.getD i 0).testBit t.val) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  have h63 := t63 t
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap <;>
    rcases hop with rfl | rfl | rfl <;>
    simp [gm, GateOp.eval, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, h63]

theorem bits_run (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (t : Fin 6) (ms : List ℕ) :
    (gs.foldl mstep ms).map (fun x => x.testBit t.val) = gs.foldl bstep (ms.map fun x => x.testBit t.val) := by
  induction gs generalizing ms with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h hh => hg h (by simp [hh]))]
    congr 1
    simp only [mstep, bstep, List.map_append, List.map_cons, List.map_nil, read_bit]
    rw [gm_bit ms g (hg g (by simp)) t]

theorem lt64_and (x : ℕ) : x &&& 63 < 64 := by
  have := Nat.and_le_right (n := x) (m := 63)
  omega

theorem run_lt (gs : List Gate) (ms : List ℕ) (h : ∀ x ∈ ms, x < 64) :
    ∀ x ∈ gs.foldl mstep ms, x < 64 := by
  induction gs generalizing ms with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    intro x hx
    simp only [mstep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact lt64_and _

theorem run_sub (gs : List Gate) (ms : List ℕ) : ∀ x ∈ ms, x ∈ gs.foldl mstep ms := by
  induction gs generalizing ms with
  | nil => intro x hx; exact hx
  | cons g gs ih =>
    intro x hx
    exact ih _ x (by simp [mstep, hx])

theorem getD_mem (ms : List ℕ) (i : ℕ) (h0 : 0 ∈ ms) : ms.getD i 0 ∈ ms := by
  by_cases h : i < ms.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]; exact h0

theorem nots_cons (g : Gate) (gs : List Gate) : nots (g :: gs) = isNot g + nots gs := by
  simp [nots]

theorem and63 {a : ℕ} (h : a < 64) : a &&& 63 = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  by_cases hi : i < 6
  · have : (63 : ℕ).testBit i = true := t63 ⟨i, hi⟩
    simp [this]
  · have ha : a.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le h (by
      have : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this))
    simp [ha]

theorem pick {S k nn X : ℕ} (hx : ¬ mem S X = true) (h : go k nn (ins S X) = true) :
    (!mem S X && go k nn (ins S X)) = true := by
  cases hm : mem S X
  · simp [h]
  · exact absurd hm hx

theorem step_cover (ms : List ℕ) (S nn k : ℕ) (g : Gate) (hg : legal g)
    (hS : ∀ x, mem S x = true ↔ x ∈ ms) (h0 : 0 ∈ ms) (h63 : 63 ∈ ms) (hlt : ∀ x ∈ ms, x < 64)
    (hn : nn + isNot g ≤ NB)
    (hnext : go k (nn + isNot g) (ins S (gm ms g)) = true) :
    go (k + 1) nn S = true := by
  have hmiss : missing S ≤ k + 1 := by
    have := missing_le_of_go hnext
    have := missing_ins S (gm ms g)
    omega
  have hins : ∀ x, mem S x = true → ins S x = S := by
    intro x hx
    apply Nat.eq_of_testBit_eq
    intro y
    have := mem_ins S x y
    unfold mem at this hx
    rw [this]
    by_cases hy : y = x
    · subst hy; simp [hx]
    · simp [hy]
  have rd : ∀ i, ms.getD i 0 ∈ ms := fun i => getD_mem ms i h0
  have inS : ∀ i, mem S (ms.getD i 0) = true := fun i => (hS _).mpr (rd i)
  have inE : ∀ i, ms.getD i 0 ∈ elems S := fun i => mem_elems (hlt _ (rd i)) (inS i)
  simp only [go, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  right
  refine ⟨hmiss, ?_⟩
  by_cases hx : mem S (gm ms g) = true
  · rw [hins _ hx] at hnext
    rcases isNot01 g with hnot | hnot
    · rw [hnot, Nat.add_zero] at hnext
      left; left; left; exact hnext
    · rw [hnot] at hnext hn
      left; left; right; exact ⟨by omega, hnext⟩
  · obtain ⟨op, args⟩ := g
    obtain ⟨hop, cap⟩ := hg
    change op = .and ∨ op = .or ∨ op = .not at hop
    change args.length ≤ 2 at cap
    rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
    · exfalso; apply hx
      rcases hop with rfl | rfl | rfl <;> simp [gm]
      · exact (hS 63).mpr h63
      · exact (hS 0).mpr h0
      · exact (hS 63).mpr h63
    · rcases hop with rfl | rfl | rfl
      · exfalso; apply hx
        have e : gm ms ⟨.and, [i]⟩ = (ms.getD i 0 &&& 63) &&& 63 := rfl
        rw [e, and63 (hlt _ (rd i)), and63 (hlt _ (rd i))]; exact inS i
      · exfalso; apply hx
        have e : gm ms ⟨.or, [i]⟩ = (ms.getD i 0 ||| 0) &&& 63 := rfl
        rw [e, Nat.or_zero, and63 (hlt _ (rd i))]; exact inS i
      · have e : gm ms ⟨.not, [i]⟩ = (63 ^^^ ms.getD i 0) &&& 63 := rfl
        simp [isNot] at hnext hn
        rw [e] at hx hnext
        right
        exact ⟨by omega, List.any_eq_true.mpr ⟨ms.getD i 0, inE i, by beta_reduce; exact pick hx hnext⟩⟩
    · rcases hop with rfl | rfl | rfl
      · have e : gm ms ⟨.and, [i, j]⟩ = (ms.getD i 0 &&& (ms.getD j 0 &&& 63)) &&& 63 := rfl
        simp [isNot] at hnext hn
        rw [e] at hx hnext
        left; right
        exact List.any_eq_true.mpr ⟨_, inE i, List.any_eq_true.mpr ⟨_, inE j, by
          beta_reduce; rw [Bool.or_eq_true]; exact Or.inl (pick hx hnext)⟩⟩
      · have e : gm ms ⟨.or, [i, j]⟩ = (ms.getD i 0 ||| (ms.getD j 0 ||| 0)) &&& 63 := rfl
        simp [isNot] at hnext hn
        rw [e] at hx hnext
        left; right
        exact List.any_eq_true.mpr ⟨_, inE i, List.any_eq_true.mpr ⟨_, inE j, by
          beta_reduce; rw [Bool.or_eq_true]; exact Or.inr (pick hx hnext)⟩⟩
      · have e : gm ms ⟨.not, [i, j]⟩ = (63 ^^^ ms.getD i 0) &&& 63 := rfl
        simp [isNot] at hnext hn
        rw [e] at hx hnext
        right
        exact ⟨by omega, List.any_eq_true.mpr ⟨ms.getD i 0, inE i, by beta_reduce; exact pick hx hnext⟩⟩

theorem complete (gs : List Gate) (hg : ∀ g ∈ gs, legal g) :
    ∀ (ms : List ℕ) (S nn k : ℕ), (∀ x, mem S x = true ↔ x ∈ ms) → 0 ∈ ms → 63 ∈ ms →
      (∀ x ∈ ms, x < 64) → gs.length ≤ k → nn + nots gs ≤ NB →
      M1 ∈ gs.foldl mstep ms → M2 ∈ gs.foldl mstep ms → M3 ∈ gs.foldl mstep ms →
      go k nn S = true := by
  induction gs with
  | nil =>
    intro ms S nn k hS _ _ _ _ _ h1 h2 h3
    apply go_hasAll
    simp [hasAll, (hS _).mpr h1, (hS _).mpr h2, (hS _).mpr h3]
  | cons g gs ih =>
    intro ms S nn k hS h0 h63 hlt hk hn h1 h2 h3
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    rw [nots_cons] at hn
    have hgg := hg g (by simp)
    apply step_cover ms S nn k g hgg hS h0 h63 hlt (by omega)
    apply ih (fun h hh => hg h (by simp [hh])) (mstep ms g)
    · intro x
      rw [mem_ins, Bool.or_eq_true, hS, decide_eq_true_eq]
      simp [mstep]
    · simp [mstep, h0]
    · simp [mstep, h63]
    · intro x hx
      simp only [mstep, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact hlt x hx
      · exact lt64_and _
    · simp at hk; omega
    · omega
    · simpa using h1
    · simpa using h2
    · simpa using h3

def ms0 : List ℕ := [62, 60, 56, 48, 32, 0, 63]
def S0 : ℕ := 15060318633198616577

theorem S0_ok : ∀ x, mem S0 x = true ↔ x ∈ ms0 := by
  intro x
  have key : ∀ y, y < 64 → (mem S0 y = true ↔ y ∈ ms0) := by decide
  by_cases hx : x < 64
  · exact key x hx
  · have : mem S0 x = false := by
      have h1 : S0 < 2 ^ 64 := by unfold S0; decide
      have h2 : 2 ^ 64 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold mem
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 h2)
    simp only [this, Bool.false_eq_true, false_iff]
    intro hm
    simp [ms0] at hm
    omega

theorem xs_ok (t : Fin 6) : ms0.map (fun x => x.testBit t.val) =
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] := by
  revert t; decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem search : go 6 0 S0 = false := by
  decide +kernel

theorem target_mem (gs : List Gate) (hg : ∀ g ∈ gs, legal g) (o : ℕ) (M : ℕ) (hM : M < 64)
    (h : ∀ t : Fin 6, (gs.foldl bstep ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD o false =
      M.testBit t.val) : M ∈ gs.foldl mstep ms0 := by
  have hlt := run_lt gs ms0 (by decide)
  have h0 : 0 ∈ gs.foldl mstep ms0 := run_sub gs ms0 0 (by decide)
  have hv : (gs.foldl mstep ms0).getD o 0 = M := by
    have hx := hlt _ (getD_mem _ o h0)
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 6
    · have := h ⟨i, hi⟩
      rw [← xs_ok, ← bits_run gs hg, read_bit] at this
      exact this
    · have p5 : 2 ^ 6 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (by simpa using p5)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hM (by simpa using p5))]
  rw [← hv]
  exact getD_mem _ o h0

end PEqualNP.Outside.L_meta_50292

open PEqualNP.Outside.L_meta_50292 in
theorem PEqualNP.Outside.L_meta_50292 :
    ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (5 : Nat).testBit t.val ∧
    w.getD q.val false = (36 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, h⟩
  have hg : ∀ g ∈ D.gates, legal g := by
    intro g hg
    obtain ⟨op, cap⟩ := hfan g hg
    exact ⟨op, cap⟩
  have hw : ∀ t : Fin 6, ∀ o : ℕ, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD o false =
      (D.gates.foldl bstep ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD o false := fun _ _ => rfl
  have e1 := target_mem D.gates hg p.val M1 (by decide) (fun t => by rw [← hw]; exact (h t).1)
  have e2 := target_mem D.gates hg q.val M2 (by decide) (fun t => by rw [← hw]; exact (h t).2.1)
  have e3 := target_mem D.gates hg r.val M3 (by decide) (fun t => by rw [← hw]; exact (h t).2.2)
  have := complete D.gates hg ms0 S0 0 6 S0_ok (by decide) (by decide) (by decide) hsize
    (by
      unfold PEqualNP.NotBracket.notCount at hnot
      have : nots D.gates ≤ NB := by
        refine le_trans (le_of_eq (nots_filter D.gates _ ?_).symm) hnot
        intro g; simp
      omega) e1 e2 e3
  rw [search] at this
  exact Bool.false_ne_true this
