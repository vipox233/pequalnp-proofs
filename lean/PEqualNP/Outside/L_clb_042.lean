import PEqualNP.Defs

/-! Method: de Bruijn reachability, run once from each start state `s`. Wire layer `k` of start
`s` at state `st` says some binary word starting with `s` reaches `st` after passing the first `k`
window tables; one step costs three gates per state (two ANDs with the table input, one OR). A
final OR chain over `s` asks for a return to the start state after `n` steps (cyclic closing). -/

namespace PEqualNP.Outside.L_clb_042_aux
open PEqualNP.CircuitLowerBounds

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

theorem bit_zero (b x : ℕ) (hb : b < 2) : (b + 2 * x).testBit 0 = decide (b = 1) := by
  rw [Nat.testBit_zero]
  have : (b + 2 * x) % 2 = b := by omega
  rw [this]

theorem bit_succ (b x i : ℕ) (hb : b < 2) : (b + 2 * x).testBit (i + 1) = x.testBit i := by
  rw [Nat.testBit_succ]
  have : (b + 2 * x) / 2 = x := by omega
  rw [this]

theorem bit_high (x w i : ℕ) (hx : x < 2 ^ w) (hi : w ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

theorem bits_eq (x y w : ℕ) (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (h : ∀ i < w, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i w with hi | hi
  · exact h i hi
  · rw [bit_high x w i hx hi, bit_high y w i hy hi]

theorem bits_exist (w : ℕ) : ∀ f : ℕ → Bool, ∃ s < 2 ^ w, ∀ i < w, s.testBit i = f i := by
  induction w with
  | zero => intro f; exact ⟨0, by norm_num, fun i hi => absurd hi (by omega)⟩
  | succ w ih =>
    intro f
    obtain ⟨s, hs, hb⟩ := ih (fun i => f (i + 1))
    refine ⟨(if f 0 then 1 else 0) + 2 * s, ?_, ?_⟩
    · rw [pow_succ]; split <;> omega
    · intro i hi
      rcases i with _ | i
      · rw [bit_zero _ _ (by split <;> omega)]; cases f 0 <;> simp
      · rw [bit_succ _ _ _ (by split <;> omega)]; exact hb i (by omega)

theorem bits_mod (p w i : ℕ) (hi : i < w) : (p % 2 ^ w).testBit i = p.testBit i := by
  rw [Nat.testBit_mod_two_pow]; simp [hi]

/-! ### Window reachability -/

/-- `R s k st`: from start state `s`, state `st` is reached after `k` steps; `inp k p` is the
table input for step `k` and pattern `p`. -/
def R (W : ℕ) (inp : ℕ → ℕ → Bool) (s : ℕ) : ℕ → ℕ → Bool
  | 0, st => decide (st = s)
  | k + 1, st => (R W inp s k ((0 + 2 * st) % W) && inp k (0 + 2 * st)) ||
      (R W inp s k ((1 + 2 * st) % W) && inp k (1 + 2 * st))

theorem R_succ (W : ℕ) (inp : ℕ → ℕ → Bool) (s k st : ℕ) :
    R W inp s (k + 1) st = true ↔
      ∃ b < 2, R W inp s k ((b + 2 * st) % W) = true ∧ inp k (b + 2 * st) = true := by
  simp only [R, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro (h | h)
    · exact ⟨0, by omega, h⟩
    · exact ⟨1, by omega, h⟩
  · rintro ⟨b, hb, h⟩
    interval_cases b
    · exact Or.inl h
    · exact Or.inr h

/-- `st` agrees with the word `y` on positions `j, ..., j + len - 1`. -/
def Agree (y : ℕ → Bool) (j st len : ℕ) : Prop := ∀ i < len, st.testBit i = y (j + i)

theorem R_spec (w n : ℕ) (inp : ℕ → ℕ → Bool) (tb : ℕ → (ℕ → Bool) → Bool)
    (htb : ∀ k f f', (∀ b < w + 1, f b = f' b) → tb k f = tb k f')
    (hinp : ∀ k < n, ∀ p < 2 ^ (w + 1), inp k p = tb k (fun b => p.testBit b)) :
    ∀ k ≤ n, ∀ s < 2 ^ w, ∀ st < 2 ^ w, R (2 ^ w) inp s k st = true ↔
      ∃ y : ℕ → Bool, Agree y 0 s w ∧ Agree y k st w ∧
        ∀ j < k, tb j (fun b => y (j + b)) = true := by
  have hQ : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
  intro k
  induction k with
  | zero =>
    intro _ s hs st hst
    simp only [R, decide_eq_true_eq]
    constructor
    · rintro rfl
      exact ⟨fun i => st.testBit i, fun i _ => by simp, fun i _ => by simp, fun j hj => absurd hj (by omega)⟩
    · rintro ⟨y, h0, hk, _⟩
      apply bits_eq st s w hst hs
      intro i hi
      rw [hk i hi, h0 i hi]
  | succ k ih =>
    intro hk s hs st' hst'
    rw [R_succ]
    constructor
    · rintro ⟨b, hb, hR, hI⟩
      obtain ⟨y, h0, hy, hc⟩ := (ih (by omega) s hs _ (Nat.mod_lt _ (by positivity))).mp hR
      let p := b + 2 * st'
      let y' : ℕ → Bool := fun m => if m < k then y m else p.testBit (m - k)
      have hyy : ∀ m < k + w, y' m = y m := by
        intro m hm
        simp only [y']
        split
        · rfl
        · have := hy (m - k) (by omega)
          rw [bits_mod _ _ _ (by omega)] at this
          rw [this]; congr 1; omega
      refine ⟨y', fun i hi => by rw [Nat.zero_add, hyy i (by omega)]; simpa using h0 i hi, ?_, ?_⟩
      · intro i hi
        simp only [y', show ¬ (k + 1 + i < k) by omega, if_false]
        rw [show k + 1 + i - k = i + 1 by omega, bit_succ _ _ _ hb]
      · intro j hj
        rcases Nat.lt_or_ge j k with hjk | hjk
        · rw [htb j _ (fun b => y (j + b)) (fun b' hb' => hyy _ (by omega))]
          exact hc j hjk
        · have : j = k := by omega
          subst this
          rw [htb j _ (fun b => p.testBit b) (fun b' hb' => by
            simp only [y', show ¬ (j + b' < j) by omega, if_false]; congr 1; omega)]
          rw [← hinp j (by omega) p (by omega)]
          exact hI
    · rintro ⟨y, h0, hy, hc⟩
      let b := if y k then 1 else 0
      have hb : b < 2 := by simp only [b]; split <;> omega
      let p := b + 2 * st'
      have hp : Agree y k p (w + 1) := by
        intro i hi
        rcases i with _ | i
        · rw [bit_zero _ _ hb]; by_cases hyk : y k <;> simp [b, hyk]
        · rw [bit_succ _ _ _ hb, hy i (by omega)]; congr 1; omega
      refine ⟨b, hb, ?_, ?_⟩
      · apply (ih (by omega) s hs _ (Nat.mod_lt _ (by positivity))).mpr
        refine ⟨y, h0, fun i hi => ?_, fun j hj => hc j (by omega)⟩
        rw [bits_mod _ _ _ hi]; exact hp i (by omega)
      · rw [hinp k (by omega) p (by omega)]
        rw [htb k _ (fun b' => y (k + b')) (fun b' hb' => hp b' hb')]
        exact hc k (by omega)


/-! ### The circuit -/

/-- The wire holding layer `k`, state `st`, start `s` (`I` inputs). -/
def lw (I W n s k st : ℕ) : ℕ :=
  if k = 0 then (if st = s then I else I + 1) else I + 2 + 3 * ((s * n + (k - 1)) * W + st) + 2

/-- Gate number `j`: constants, then three gates per (start, step, state), then the OR chain. -/
def gt (I W Q n : ℕ) (j : ℕ) : Gate :=
  if j = 0 then ⟨GateOp.and, []⟩
  else if j = 1 then ⟨GateOp.or, []⟩
  else if j < 2 + 3 * (W * n * W) then
    if (j - 2) % 3 = 2 then ⟨GateOp.or, [I + j - 2, I + j - 1]⟩
    else ⟨GateOp.and, [lw I W n ((j - 2) / 3 / W / n) ((j - 2) / 3 / W % n)
        (((j - 2) % 3 + 2 * ((j - 2) / 3 % W)) % W),
        (j - 2) / 3 / W % n * Q + ((j - 2) % 3 + 2 * ((j - 2) / 3 % W))]⟩
  else ⟨GateOp.or, [if j = 2 + 3 * (W * n * W) then I + 1 else I + j - 1,
      lw I W n (j - (2 + 3 * (W * n * W))) n (j - (2 + 3 * (W * n * W)))]⟩

/-- The intended value of every wire. -/
def val (I W Q n : ℕ) (x : List Bool) (i : ℕ) : Bool :=
  if i < I then x.getD i false
  else if i = I then true
  else if i = I + 1 then false
  else if i < I + 2 + 3 * (W * n * W) then
    if (i - I - 2) % 3 = 2 then
      R W (fun k p => x.getD (k * Q + p) false) ((i - I - 2) / 3 / W / n)
        ((i - I - 2) / 3 / W % n + 1) ((i - I - 2) / 3 % W)
    else R W (fun k p => x.getD (k * Q + p) false) ((i - I - 2) / 3 / W / n)
        ((i - I - 2) / 3 / W % n) (((i - I - 2) % 3 + 2 * ((i - I - 2) / 3 % W)) % W) &&
      x.getD ((i - I - 2) / 3 / W % n * Q + ((i - I - 2) % 3 + 2 * ((i - I - 2) / 3 % W))) false
  else (List.range (i - I - 2 - 3 * (W * n * W) + 1)).any
    (fun s => R W (fun k p => x.getD (k * Q + p) false) s n s)

theorem decode (W n s k st : ℕ) (hst : st < W) (hk : k < n) :
    ((s * n + k) * W + st) % W = st ∧ ((s * n + k) * W + st) / W % n = k ∧
      ((s * n + k) * W + st) / W / n = s := by
  have hW : 0 < W := by omega
  have h1 : ((s * n + k) * W + st) / W = s * n + k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt hst, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hst]
  · rw [h1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  · rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]

theorem tbound (W n s k st : ℕ) (hs : s < W) (hk : k < n) (hst : st < W) :
    (s * n + k) * W + st < W * n * W := by
  have h1 : s * n + k + 1 ≤ W * n := by
    have : (s + 1) * n ≤ W * n := Nat.mul_le_mul_right n hs
    nlinarith
  have h2 : (s * n + k + 1) * W ≤ W * n * W := Nat.mul_le_mul_right W h1
  nlinarith

theorem gt_blk (I W Q n t r : ℕ) (hr : r < 3) (ht : t < W * n * W) :
    gt I W Q n (2 + 3 * t + r) = if r = 2 then ⟨GateOp.or, [I + 2 + 3 * t, I + 2 + 3 * t + 1]⟩
      else ⟨GateOp.and, [lw I W n (t / W / n) (t / W % n) ((r + 2 * (t % W)) % W),
        t / W % n * Q + (r + 2 * (t % W))]⟩ := by
  have h1 : (2 + 3 * t + r - 2) / 3 = t := by omega
  have h2 : (2 + 3 * t + r - 2) % 3 = r := by omega
  unfold gt
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2]
  by_cases h : r = 2
  · subst h; simp only [if_true]
    rw [show I + (2 + 3 * t + 2) - 2 = I + 2 + 3 * t by omega,
      show I + (2 + 3 * t + 2) - 1 = I + 2 + 3 * t + 1 by omega]
  · simp only [h, if_false]

theorem val_blk (I W Q n t r : ℕ) (x : List Bool) (hr : r < 3) (ht : t < W * n * W) :
    val I W Q n x (I + 2 + 3 * t + r) = if r = 2 then
      R W (fun k p => x.getD (k * Q + p) false) (t / W / n) (t / W % n + 1) (t % W)
    else R W (fun k p => x.getD (k * Q + p) false) (t / W / n) (t / W % n) ((r + 2 * (t % W)) % W)
      && x.getD (t / W % n * Q + (r + 2 * (t % W))) false := by
  have h1 : (I + 2 + 3 * t + r - I - 2) / 3 = t := by omega
  have h2 : (I + 2 + 3 * t + r - I - 2) % 3 = r := by omega
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2]

theorem val_in (I W Q n : ℕ) (x : List Bool) (i : ℕ) (hi : i < I) :
    val I W Q n x i = x.getD i false := by
  unfold val; rw [if_pos hi]

theorem val_ch (I W Q n c : ℕ) (x : List Bool) :
    val I W Q n x (I + 2 + 3 * (W * n * W) + c) = (List.range (c + 1)).any
      (fun s => R W (fun k p => x.getD (k * Q + p) false) s n s) := by
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 3; omega

theorem gt_ch (I W Q n c : ℕ) :
    gt I W Q n (2 + 3 * (W * n * W) + c) = ⟨GateOp.or,
      [if c = 0 then I + 1 else I + 2 + 3 * (W * n * W) + (c - 1), lw I W n c n c]⟩ := by
  unfold gt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have : 2 + 3 * (W * n * W) + c - (2 + 3 * (W * n * W)) = c := by omega
  rw [this]
  by_cases hc : c = 0
  · subst hc; simp
  · rw [if_neg (by omega), if_neg hc]; congr 3; omega

theorem val_lw (I W Q n s k st : ℕ) (x : List Bool) (hs : s < W) (hk : k ≤ n) (hst : st < W) :
    val I W Q n x (lw I W n s k st) = R W (fun k p => x.getD (k * Q + p) false) s k st := by
  rcases k with _ | k
  · unfold lw
    by_cases h : st = s
    · simp only [if_true, h]; unfold val; simp [R]
    · simp only [if_true, h, if_false]; unfold val; simp [R, h]
  · have ht := tbound W n s k st hs (by omega) hst
    obtain ⟨d1, d2, d3⟩ := decode W n s k st hst (by omega)
    unfold lw
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    rw [val_blk I W Q n _ 2 x (by omega) ht, if_pos rfl, d1, d2, d3]

theorem gt_reads (I W Q n : ℕ) (hW : 0 < W) (hn : 0 < n) (hI : I = n * Q) (hQ : Q = 2 * W) :
    ∀ j < 2 + 3 * (W * n * W) + W, ∀ i ∈ (gt I W Q n j).inputs, i < I + j := by
  intro j hj i hi
  by_cases h0 : j = 0
  · subst h0; simp [gt] at hi
  by_cases h1 : j = 1
  · subst h1; simp [gt] at hi
  by_cases hb : j < 2 + 3 * (W * n * W)
  · obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 3 ∧ j = 2 + 3 * t + r :=
      ⟨(j - 2) / 3, (j - 2) % 3, by omega, by omega⟩
    have ht : t < W * n * W := by omega
    rw [gt_blk I W Q n t r hr ht] at hi
    by_cases h2 : r = 2
    · simp only [h2, if_true, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      omega
    · simp only [h2, if_false, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
      have htw : t / W / n * n + t / W % n = t / W := Nat.div_add_mod' _ _
      have htw2 : t / W * W ≤ t := Nat.div_mul_le_self t W
      have hk : t / W % n < n := Nat.mod_lt _ hn
      rcases hi with hi | hi
      · unfold lw at hi
        by_cases hk0 : t / W % n = 0
        · simp only [hk0, if_true] at hi; split at hi <;> omega
        · simp only [hk0, if_false] at hi
          have hm : ((r + 2 * (t % W)) % W) < W := Nat.mod_lt _ hW
          have e : (t / W / n * n + (t / W % n - 1)) * W + W = (t / W / n * n + t / W % n) * W := by
            obtain ⟨k', hk'⟩ : ∃ k', t / W % n = k' + 1 := ⟨t / W % n - 1, by omega⟩
            rw [hk', Nat.add_sub_cancel]; ring
          rw [htw] at e
          omega
      · have hst : t % W < W := Nat.mod_lt _ hW
        have e1 : (t / W % n + 1) * Q ≤ n * Q := Nat.mul_le_mul_right Q hk
        have e2 : (t / W % n + 1) * Q = t / W % n * Q + Q := by ring
        omega
  · obtain ⟨c, rfl⟩ : ∃ c, j = 2 + 3 * (W * n * W) + c := ⟨j - (2 + 3 * (W * n * W)), by omega⟩
    have hc : c < W := by omega
    rw [gt_ch] at hi
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hi
    rcases hi with hi | hi
    · split at hi <;> omega
    · unfold lw at hi
      simp only [show n ≠ 0 by omega, if_false] at hi
      have := tbound W n c (n - 1) c hc (by omega) hc
      omega

theorem gt_eqns (I W Q n : ℕ) (x : List Bool) (hW : 0 < W) (hn : 0 < n) (hI : I = n * Q)
    (hQ : Q = 2 * W) :
    ∀ j < 2 + 3 * (W * n * W) + W, val I W Q n x (I + j) =
      (gt I W Q n j).op.eval ((gt I W Q n j).inputs.map (val I W Q n x)) := by
  intro j hj
  by_cases h0 : j = 0
  · subst h0; simp [gt, val, GateOp.eval]
  by_cases h1 : j = 1
  · subst h1; simp [gt, val, GateOp.eval]
  by_cases hb : j < 2 + 3 * (W * n * W)
  · obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 3 ∧ j = 2 + 3 * t + r :=
      ⟨(j - 2) / 3, (j - 2) % 3, by omega, by omega⟩
    have ht : t < W * n * W := by omega
    rw [gt_blk I W Q n t r hr ht, show I + (2 + 3 * t + r) = I + 2 + 3 * t + r by ring,
      val_blk I W Q n t r x hr ht]
    by_cases h2 : r = 2
    · simp only [h2, if_true, List.map_cons, List.map_nil]
      rw [show I + 2 + 3 * t = I + 2 + 3 * t + 0 by rfl, val_blk I W Q n t 0 x (by omega) ht,
        val_blk I W Q n t 1 x (by omega) ht]
      simp [GateOp.eval, R]
    · simp only [h2, if_false, List.map_cons, List.map_nil]
      have hs : t / W / n < W := by
        rw [Nat.div_lt_iff_lt_mul hn, Nat.div_lt_iff_lt_mul hW]; exact ht
      have hk : t / W % n < n := Nat.mod_lt _ hn
      have hst : t % W < W := Nat.mod_lt _ hW
      rw [val_lw I W Q n _ _ _ x hs hk.le (Nat.mod_lt _ hW)]
      have e1 : (t / W % n + 1) * Q ≤ n * Q := Nat.mul_le_mul_right Q hk
      have e2 : (t / W % n + 1) * Q = t / W % n * Q + Q := by ring
      rw [val_in I W Q n x _ (by omega)]
      simp [GateOp.eval]
  · obtain ⟨c, rfl⟩ : ∃ c, j = 2 + 3 * (W * n * W) + c := ⟨j - (2 + 3 * (W * n * W)), by omega⟩
    have hc : c < W := by omega
    rw [gt_ch, show I + (2 + 3 * (W * n * W) + c) = I + 2 + 3 * (W * n * W) + c by ring,
      val_ch]
    simp only [List.map_cons, List.map_nil]
    rw [val_lw I W Q n c n c x hc le_rfl hc]
    by_cases hc0 : c = 0
    · subst hc0
      simp only [if_true]
      unfold val; simp [GateOp.eval]
    · rw [if_neg hc0, val_ch, show c - 1 + 1 = c by omega, List.range_succ]
      simp [GateOp.eval]

end PEqualNP.Outside.L_clb_042_aux

open PEqualNP.Outside.L_clb_042_aux in
theorem PEqualNP.Outside.L_clb_042 : ∀ (n w : ℕ) (hn : 0 < n),
  let I := n * 2 ^ (w + 1)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.Monotone2 C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧
    C.size ≤ 3 * n * 4 ^ w + 2 ^ w + 2 ∧
    ∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := List.ofFn (fun j : Fin I =>
        table ⟨(j.val / 2 ^ (w + 1)) % n, Nat.mod_lt _ hn⟩
          (fun bit => j.val.testBit bit.val))
      C.eval inputs = true ↔
        ∃ word : Fin n → Bool, ∀ i : Fin n,
          table i (fun bit => word ⟨(i.val + bit.val) % n, Nat.mod_lt _ hn⟩) = true := by
  intro n w hn I
  have hW : 0 < 2 ^ w := by positivity
  have hQ : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
  have hI : I = n * 2 ^ (w + 1) := rfl
  refine ⟨prog (gt I (2 ^ w) (2 ^ (w + 1)) n) (2 + 3 * (2 ^ w * n * 2 ^ w) + 2 ^ w)
    (I + (2 + 3 * (2 ^ w * n * 2 ^ w) + (2 ^ w - 1))), ?_, ?_, ?_, ?_⟩
  · intro G hG
    obtain ⟨j, _, rfl⟩ := prog_mem _ _ _ G hG
    unfold gt
    split_ifs <;> simp
  · exact prog_readsBack _ _ _ _ (gt_reads I _ _ n hW hn hI hQ)
  · rw [prog_size]
    have h4 : (4 : ℕ) ^ w = 2 ^ w * 2 ^ w := by rw [← mul_pow]; norm_num
    rw [h4]
    have : 2 + 3 * (2 ^ w * n * 2 ^ w) + 2 ^ w = 3 * n * (2 ^ w * 2 ^ w) + 2 ^ w + 2 := by ring
    omega
  · intro table inputs
    have hx : inputs.length = I := by simp [inputs]
    have hw := prog_wires I (2 + 3 * (2 ^ w * n * 2 ^ w) + 2 ^ w)
      (I + (2 + 3 * (2 ^ w * n * 2 ^ w) + (2 ^ w - 1))) (gt I (2 ^ w) (2 ^ (w + 1)) n)
      (val I (2 ^ w) (2 ^ (w + 1)) n inputs) inputs hx
      (fun i hi => (val_in I _ _ n inputs i hi).symm) (gt_reads I _ _ n hW hn hI hQ)
      (gt_eqns I _ _ n inputs hW hn hI hQ)
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval, prog_output, hw _ (by omega)]
    rw [show I + (2 + 3 * (2 ^ w * n * 2 ^ w) + (2 ^ w - 1)) =
      I + 2 + 3 * (2 ^ w * n * 2 ^ w) + (2 ^ w - 1) by ring, val_ch,
      show 2 ^ w - 1 + 1 = 2 ^ w by omega, List.any_eq_true]
    let tb : ℕ → (ℕ → Bool) → Bool := fun k f =>
      if h : k < n then table ⟨k, h⟩ (fun bit => f bit.val) else false
    have htb : ∀ k f f', (∀ b < w + 1, f b = f' b) → tb k f = tb k f' := by
      intro k f f' h
      simp only [tb]
      split
      · congr 1; funext bit; exact h bit.val bit.isLt
      · rfl
    have hinp : ∀ k < n, ∀ p < 2 ^ (w + 1),
        inputs.getD (k * 2 ^ (w + 1) + p) false = tb k (fun b => p.testBit b) := by
      intro k hk p hp
      have hlt : k * 2 ^ (w + 1) + p < I := by
        have e1 : (k + 1) * 2 ^ (w + 1) ≤ n * 2 ^ (w + 1) := Nat.mul_le_mul_right _ hk
        have e2 : (k + 1) * 2 ^ (w + 1) = k * 2 ^ (w + 1) + 2 ^ (w + 1) := by ring
        omega
      have hdiv : (k * 2 ^ (w + 1) + p) / 2 ^ (w + 1) = k := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hp,
          Nat.zero_add]
      have hmod : (k * 2 ^ (w + 1) + p) % 2 ^ (w + 1) = p := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
      simp only [inputs, tb, dif_pos hk, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [dif_pos hlt, Option.getD_some]
      congr 1
      · exact Fin.ext (by simp only [hdiv, Nat.mod_eq_of_lt hk])
      · funext bit
        rw [← bits_mod (k * 2 ^ (w + 1) + p) (w + 1) bit.val bit.isLt, hmod]
    have spec := R_spec w n (fun k p => inputs.getD (k * 2 ^ (w + 1) + p) false) tb htb hinp
    constructor
    · rintro ⟨s, hs, hR⟩
      rw [List.mem_range] at hs
      obtain ⟨y, h0, hyn, hc⟩ := (spec n le_rfl s hs s hs).mp hR
      have per : ∀ m, m < n + w → y m = y (m % n) := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
          intro hm
          by_cases hmn : m < n
          · rw [Nat.mod_eq_of_lt hmn]
          · have e1 := h0 (m - n) (by omega)
            have e2 := hyn (m - n) (by omega)
            rw [Nat.zero_add] at e1
            rw [show n + (m - n) = m by omega] at e2
            rw [← e2, e1, ih (m - n) (by omega) (by omega)]
            congr 1
            conv_rhs => rw [show m = m - n + n by omega, Nat.add_mod_right]
      refine ⟨fun i => y i.val, fun i => ?_⟩
      have := hc i.val i.isLt
      simp only [tb, dif_pos i.isLt] at this
      convert this using 2
      funext bit
      exact (per _ (by omega)).symm
    · rintro ⟨word, hword⟩
      let y : ℕ → Bool := fun m => word ⟨m % n, Nat.mod_lt _ hn⟩
      obtain ⟨s, hs, hsb⟩ := bits_exist w y
      refine ⟨s, List.mem_range.mpr hs, (spec n le_rfl s hs s hs).mpr ⟨y, ?_, ?_, ?_⟩⟩
      · intro i hi; rw [hsb i hi, Nat.zero_add]
      · intro i hi; rw [hsb i hi]; simp only [y, Nat.add_mod_left]
      · intro j hj
        simp only [tb, dif_pos hj, y]
        exact hword ⟨j, hj⟩
