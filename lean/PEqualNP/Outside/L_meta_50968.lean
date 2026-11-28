import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50968

open PEqualNP.CircuitLowerBounds

/-! A wire is recorded by its mask, a number below 64: bit `t` of the mask is the value of the wire on the
input `t` (t = 0, ..., 5). The input wires have the masks of the thresholds, then 0 and 63. A gate
adds the AND or the OR of two masks that are there, or (a NOT gate) the complement of one. `srch` tries every
way to add new masks; `Play.srch` says that it finds every circuit, and `play` reads a circuit as such a play. -/

def roots : List ℕ := [62, 60, 56, 48, 32, 0, 63]

def mAnd (x y : ℕ) : ℕ := (x &&& y) % 64
def mOr (x y : ℕ) : ℕ := (x ||| y) % 64
def mNot (x : ℕ) : ℕ := (63 ^^^ x) % 64

def tb (t : ℕ) (m : ℕ) : Bool := m.testBit t

theorem bit_and : ∀ (x y : Fin 64) (t : Fin 6),
    tb t.val (mAnd x.val y.val) = (tb t.val x.val && tb t.val y.val) := by decide +kernel

theorem bit_or : ∀ (x y : Fin 64) (t : Fin 6),
    tb t.val (mOr x.val y.val) = (tb t.val x.val || tb t.val y.val) := by decide +kernel

theorem bit_not : ∀ (x : Fin 64) (t : Fin 6), tb t.val (mNot x.val) = !(tb t.val x.val) := by decide +kernel

theorem bit_one : ∀ t : Fin 6, tb t.val 63 = true := by decide

theorem bit_zero (t : ℕ) : tb t 0 = false := by simp [tb]

theorem mAnd_lt (x y : ℕ) : mAnd x y < 64 := Nat.mod_lt _ (by decide)
theorem mOr_lt (x y : ℕ) : mOr x y < 64 := Nat.mod_lt _ (by decide)
theorem mNot_lt (x : ℕ) : mNot x < 64 := Nat.mod_lt _ (by decide)

/-! ## The search -/

def canBin (S : List ℕ) (v : ℕ) : Bool := S.any fun x => S.any fun y => mAnd x y == v || mOr x y == v
def canNeg (S : List ℕ) (v : ℕ) : Bool := S.any fun x => mNot x == v
def have3 (a b c : ℕ) (S : List ℕ) : Bool := S.contains a && S.contains b && S.contains c

def stepB (S : List ℕ) (k : ℕ → Bool) : Bool :=
  (List.range 64).any fun v => (!S.contains v && canBin S v) && k v
def stepN (S : List ℕ) (k : ℕ → Bool) : Bool :=
  (List.range 64).any fun v => (!S.contains v && canNeg S v) && k v

/-- How many of the three masks are still missing. -/
def miss (a b c : ℕ) (S : List ℕ) : ℕ :=
  (if S.contains a then 0 else 1) + (if S.contains b then 0 else 1) + (if S.contains c then 0 else 1)

/-- With at most `f` more gates, at most `n` of them NOT gates, the masks `a`, `b`, `c` can all be made.
A gate adds one mask, so nothing is tried when more masks are missing than gates are left. -/
def srch (a b c : ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, S => have3 a b c S
  | f + 1, n, S =>
    have3 a b c S || (decide (miss a b c S ≤ f + 1) &&
      (stepB S (fun v => srch a b c f n (v :: S)) ||
        (decide (0 < n) && stepN S (fun v => srch a b c f (n - 1) (v :: S)))))

theorem srch_zero (a b c n : ℕ) (S : List ℕ) : srch a b c 0 n S = have3 a b c S := rfl

theorem srch_succ (a b c f n : ℕ) (S : List ℕ) : srch a b c (f + 1) n S =
    (have3 a b c S || (decide (miss a b c S ≤ f + 1) &&
      (stepB S (fun v => srch a b c f n (v :: S)) ||
        (decide (0 < n) && stepN S (fun v => srch a b c f (n - 1) (v :: S)))))) := rfl

theorem stepB_mono {S : List ℕ} {k k' : ℕ → Bool} (h : ∀ v, k v = true → k' v = true)
    (hs : stepB S k = true) : stepB S k' = true := by
  unfold stepB at hs ⊢
  obtain ⟨v, hv, hx⟩ := List.any_eq_true.mp hs
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hx
  exact List.any_eq_true.mpr ⟨v, hv, Bool.and_eq_true_iff.mpr ⟨h1, h v h2⟩⟩

theorem stepN_mono {S : List ℕ} {k k' : ℕ → Bool} (h : ∀ v, k v = true → k' v = true)
    (hs : stepN S k = true) : stepN S k' = true := by
  unfold stepN at hs ⊢
  obtain ⟨v, hv, hx⟩ := List.any_eq_true.mp hs
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hx
  exact List.any_eq_true.mpr ⟨v, hv, Bool.and_eq_true_iff.mpr ⟨h1, h v h2⟩⟩

theorem not_contains {S : List ℕ} {v : ℕ} (hS : v ∉ S) : (!S.contains v) = true := by
  simp [hS]

theorem stepB_intro {S : List ℕ} {k : ℕ → Bool} {v : ℕ} (hv : v < 64) (hS : v ∉ S)
    (hc : canBin S v = true) (hk : k v = true) : stepB S k = true := by
  unfold stepB
  refine List.any_eq_true.mpr ⟨v, List.mem_range.mpr hv, ?_⟩
  rw [hc, hk, not_contains hS]
  rfl

theorem stepN_intro {S : List ℕ} {k : ℕ → Bool} {v : ℕ} (hv : v < 64) (hS : v ∉ S)
    (hc : canNeg S v = true) (hk : k v = true) : stepN S k = true := by
  unfold stepN
  refine List.any_eq_true.mpr ⟨v, List.mem_range.mpr hv, ?_⟩
  rw [hc, hk, not_contains hS]
  rfl

theorem srch_done {a b c f n : ℕ} {S : List ℕ} (h : have3 a b c S = true) : srch a b c f n S = true := by
  cases f with
  | zero => rw [srch_zero]; exact h
  | succ f => rw [srch_succ, h]; rfl

theorem srch_mono (a b c : ℕ) : ∀ (f n : ℕ) (S : List ℕ),
    srch a b c f n S = true → srch a b c (f + 1) n S = true := by
  intro f
  induction f with
  | zero =>
    intro n S h
    rw [srch_zero] at h
    exact srch_done h
  | succ f ih =>
    intro n S h
    rw [srch_succ] at h
    rw [srch_succ]
    rcases Bool.or_eq_true_iff.mp h with h | h
    · rw [h]; rfl
    · obtain ⟨hm, h⟩ := Bool.and_eq_true_iff.mp h
      have hm' : decide (miss a b c S ≤ f + 1 + 1) = true := by
        have := of_decide_eq_true hm
        exact decide_eq_true (by omega)
      rcases Bool.or_eq_true_iff.mp h with h | h
      · have h3 := stepB_mono (k' := fun v => srch a b c (f + 1) n (v :: S))
          (fun v hv => ih n (v :: S) hv) h
        rw [hm', h3]; simp
      · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
        have h3 := stepN_mono (k' := fun v => srch a b c (f + 1) (n - 1) (v :: S))
          (fun v hv => ih (n - 1) (v :: S) hv) h2
        rw [hm', h1, h3]; simp

/-! ### Cutting one search into several kernel checks
The kernel keeps everything it has reduced until one `decide` is done, so a big search is cut at its first steps:
the new masks a state allows are listed (two cheap checks), and every one of them gets its own theorem. -/

theorem stepB_false {S : List ℕ} {k : ℕ → Bool} (L : List ℕ)
    (hL : (List.range 64).filter (fun v => !S.contains v && canBin S v) = L)
    (hk : ∀ v ∈ L, k v = false) : stepB S k = false := by
  cases h : stepB S k with
  | false => rfl
  | true =>
    exfalso
    unfold stepB at h
    obtain ⟨v, hv, hx⟩ := List.any_eq_true.mp h
    obtain ⟨hc, hkv⟩ := Bool.and_eq_true_iff.mp hx
    have hm : v ∈ L := by
      rw [← hL]
      exact List.mem_filter.mpr ⟨hv, hc⟩
    rw [hk v hm] at hkv
    exact Bool.noConfusion hkv

theorem stepN_false {S : List ℕ} {k : ℕ → Bool} (L : List ℕ)
    (hL : (List.range 64).filter (fun v => !S.contains v && canNeg S v) = L)
    (hk : ∀ v ∈ L, k v = false) : stepN S k = false := by
  cases h : stepN S k with
  | false => rfl
  | true =>
    exfalso
    unfold stepN at h
    obtain ⟨v, hv, hx⟩ := List.any_eq_true.mp h
    obtain ⟨hc, hkv⟩ := Bool.and_eq_true_iff.mp hx
    have hm : v ∈ L := by
      rw [← hL]
      exact List.mem_filter.mpr ⟨hv, hc⟩
    rw [hk v hm] at hkv
    exact Bool.noConfusion hkv

theorem split_node (a b c f n : ℕ) (S LB LN : List ℕ)
    (hB : (List.range 64).filter (fun v => !S.contains v && canBin S v) = LB)
    (hN : (List.range 64).filter (fun v => !S.contains v && canNeg S v) = LN)
    (h3 : have3 a b c S = false)
    (kB : ∀ v ∈ LB, srch a b c f n (v :: S) = false)
    (kN : 0 < n → ∀ v ∈ LN, srch a b c f (n - 1) (v :: S) = false) :
    srch a b c (f + 1) n S = false := by
  have eB : stepB S (fun v => srch a b c f n (v :: S)) = false := stepB_false LB hB kB
  rw [srch_succ, h3, eB]
  by_cases hn : 0 < n
  · have eN : stepN S (fun v => srch a b c f (n - 1) (v :: S)) = false := stepN_false LN hN (kN hn)
    rw [eN]
    simp
  · simp [hn]

inductive Play (a b c : ℕ) : ℕ → ℕ → List ℕ → Prop
  | done {f n : ℕ} {S : List ℕ} (h : have3 a b c S = true) : Play a b c f n S
  | skip {f n : ℕ} {S : List ℕ} (p : Play a b c f n S) : Play a b c (f + 1) n S
  | bin {f n : ℕ} {S : List ℕ} (v : ℕ) (hv : v < 64) (hS : v ∉ S) (hc : canBin S v = true)
      (p : Play a b c f n (v :: S)) : Play a b c (f + 1) n S
  | neg {f n : ℕ} {S : List ℕ} (v : ℕ) (hv : v < 64) (hS : v ∉ S) (hc : canNeg S v = true)
      (p : Play a b c f n (v :: S)) : Play a b c (f + 1) (n + 1) S

theorem miss_le_one (S : List ℕ) (x : ℕ) : (if S.contains x then 0 else 1) ≤ 1 := by
  split <;> omega

theorem contains_cons_ne {S : List ℕ} {x v : ℕ} (h : x ≠ v) : (v :: S).contains x = S.contains x := by
  simp [h]

/-- One new mask makes at most one of three different masks appear. -/
theorem miss_cons {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (S : List ℕ) (v : ℕ) :
    miss a b c S ≤ miss a b c (v :: S) + 1 := by
  unfold miss
  have la := miss_le_one S a
  have lb := miss_le_one S b
  have lc := miss_le_one S c
  by_cases ha : a = v
  · subst ha
    rw [contains_cons_ne (Ne.symm hab), contains_cons_ne (Ne.symm hac)]
    omega
  · rw [contains_cons_ne ha]
    by_cases hb : b = v
    · subst hb
      rw [contains_cons_ne (Ne.symm hbc)]
      omega
    · rw [contains_cons_ne hb]
      by_cases hc : c = v
      · subst hc
        omega
      · rw [contains_cons_ne hc]
        omega

theorem miss_done {a b c : ℕ} {S : List ℕ} (h : have3 a b c S = true) : miss a b c S = 0 := by
  unfold have3 at h
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h12
  unfold miss
  rw [h1, h2, h3]
  rfl

theorem play_bound {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {f n : ℕ} {S : List ℕ}
    (p : Play a b c f n S) : miss a b c S ≤ f := by
  induction p with
  | done h => rw [miss_done h]; omega
  | skip p ih => omega
  | @bin f n S v hv hS hc p ih => have := miss_cons hab hac hbc S v; omega
  | @neg f n S v hv hS hc p ih => have := miss_cons hab hac hbc S v; omega

theorem play_srch {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {f n : ℕ} {S : List ℕ}
    (p : Play a b c f n S) : srch a b c f n S = true := by
  induction p with
  | done h => exact srch_done h
  | skip p ih => exact srch_mono a b c _ _ _ ih
  | @bin f n S v hv hS hc p ih =>
    have hm : decide (miss a b c S ≤ f + 1) = true :=
      decide_eq_true (by have := miss_cons hab hac hbc S v; have := play_bound hab hac hbc p; omega)
    rw [srch_succ, hm, stepB_intro (k := fun v => srch a b c f n (v :: S)) hv hS hc ih]
    simp
  | @neg f n S v hv hS hc p ih =>
    have hm : decide (miss a b c S ≤ f + 1) = true :=
      decide_eq_true (by have := miss_cons hab hac hbc S v; have := play_bound hab hac hbc p; omega)
    rw [srch_succ, hm]
    have h2 : stepN S (fun v => srch a b c f (n + 1 - 1) (v :: S)) = true :=
      stepN_intro (k := fun v => srch a b c f (n + 1 - 1) (v :: S)) hv hS hc ih
    rw [h2]
    simp

/-! ## A circuit as a list of masks -/

def Legal (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

/-- The mask of the wire that the gate `g` writes when the earlier wires have the masks `M`. -/
def gmask (M : List ℕ) (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [] => 63
  | GateOp.and, [i] => M.getD i 0
  | GateOp.and, i :: j :: _ => mAnd (M.getD i 0) (M.getD j 0)
  | GateOp.or, [] => 0
  | GateOp.or, [i] => M.getD i 0
  | GateOp.or, i :: j :: _ => mOr (M.getD i 0) (M.getD j 0)
  | GateOp.not, [] => 63
  | GateOp.not, i :: _ => mNot (M.getD i 0)
  | _, _ => 0

def run (M : List ℕ) (gs : List Gate) : List ℕ := gs.foldl (fun M g => M ++ [gmask M g]) M

theorem getD_cases (M : List ℕ) (i : ℕ) : M.getD i 0 ∈ M ∨ M.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : M[i]? with
  | none => exact Or.inr rfl
  | some x => exact Or.inl (List.mem_of_getElem? h)

theorem getD_mem {M : List ℕ} (h0 : 0 ∈ M) (i : ℕ) : M.getD i 0 ∈ M := by
  rcases getD_cases M i with h | h
  · exact h
  · rw [h]; exact h0

theorem getD_lt {M : List ℕ} (hM : ∀ m ∈ M, m < 64) (i : ℕ) : M.getD i 0 < 64 := by
  rcases getD_cases M i with h | h
  · exact hM _ h
  · rw [h]; decide

theorem rd (M : List ℕ) (i t : ℕ) : (M.map (tb t)).getD i false = tb t (M.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases M[i]? with
  | none => simp [tb]
  | some x => rfl

theorem rd' (M : List ℕ) (i t : ℕ) : (Option.map (tb t) M[i]?).getD false = tb t (M[i]?.getD 0) := by
  cases M[i]? <;> simp [tb]

theorem gmask_lt {M : List ℕ} (hM : ∀ m ∈ M, m < 64) (g : Gate) : gmask M g < 64 := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rcases ins with _ | ⟨i, _ | ⟨j, r⟩⟩ <;>
    first
    | exact getD_lt hM _
    | exact mAnd_lt _ _
    | exact mOr_lt _ _
    | exact mNot_lt _
    | simp [gmask]

theorem gmask_bit {M : List ℕ} (hM : ∀ m ∈ M, m < 64) (g : Gate) (hg : Legal g) (t : Fin 6) :
    g.op.eval (g.inputs.map fun i => (M.map (tb t.val)).getD i false) = tb t.val (gmask M g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, r⟩⟩⟩
  · rcases hop with h | h | h <;> simp only at h <;> subst h
    · simp [gmask, GateOp.eval, bit_one t]
    · simp [gmask, GateOp.eval, bit_zero]
    · simp [gmask, GateOp.eval, bit_one t]
  · rcases hop with h | h | h <;> simp only at h <;> subst h
    · simp [gmask, GateOp.eval, rd']
    · simp [gmask, GateOp.eval, rd']
    · have hb := bit_not ⟨M.getD i 0, getD_lt hM i⟩ t
      simp only [List.getD_eq_getElem?_getD] at hb
      simp [gmask, GateOp.eval, rd', hb]
  · rcases hop with h | h | h <;> simp only at h <;> subst h
    · have hb := bit_and ⟨M.getD i 0, getD_lt hM i⟩ ⟨M.getD j 0, getD_lt hM j⟩ t
      simp only [List.getD_eq_getElem?_getD] at hb
      simp [gmask, GateOp.eval, rd', hb]
    · have hb := bit_or ⟨M.getD i 0, getD_lt hM i⟩ ⟨M.getD j 0, getD_lt hM j⟩ t
      simp only [List.getD_eq_getElem?_getD] at hb
      simp [gmask, GateOp.eval, rd', hb]
    · have hb := bit_not ⟨M.getD i 0, getD_lt hM i⟩ t
      simp only [List.getD_eq_getElem?_getD] at hb
      simp [gmask, GateOp.eval, rd', hb]
  · simp at hlen

theorem run_cons (M : List ℕ) (g : Gate) (gs : List Gate) : run M (g :: gs) = run (M ++ [gmask M g]) gs := rfl

theorem append_lt {M : List ℕ} (hM : ∀ m ∈ M, m < 64) (g : Gate) : ∀ m ∈ M ++ [gmask M g], m < 64 := by
  intro m hm
  rcases List.mem_append.mp hm with h | h
  · exact hM m h
  · rw [List.mem_singleton.mp h]; exact gmask_lt hM g

theorem run_lt : ∀ (gs : List Gate) (M : List ℕ), (∀ m ∈ M, m < 64) → ∀ m ∈ run M gs, m < 64 := by
  intro gs
  induction gs with
  | nil => exact fun M hM => hM
  | cons g gs ih =>
    intro M hM
    rw [run_cons]
    exact ih _ (append_lt hM g)

theorem run_sub : ∀ (gs : List Gate) (M : List ℕ), M ⊆ run M gs := by
  intro gs
  induction gs with
  | nil => exact fun M => List.Subset.refl M
  | cons g gs ih =>
    intro M
    rw [run_cons]
    exact fun x hx => ih _ (List.mem_append_left _ hx)

theorem sem (t : Fin 6) : ∀ (gs : List Gate) (M : List ℕ), (∀ g ∈ gs, Legal g) → (∀ m ∈ M, m < 64) →
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (M.map (tb t.val)) =
      (run M gs).map (tb t.val) := by
  intro gs
  induction gs with
  | nil => exact fun M _ _ => rfl
  | cons g gs ih =>
    intro M hg hM
    rw [run_cons, List.foldl_cons, gmask_bit hM g (hg g (List.mem_cons_self ..)) t]
    have e : M.map (tb t.val) ++ [tb t.val (gmask M g)] = (M ++ [gmask M g]).map (tb t.val) := by simp
    rw [e]
    exact ih _ (fun g' h' => hg g' (List.mem_cons_of_mem _ h')) (append_lt hM g)

/-! ## A circuit as a play -/

theorem canBin_intro {S : List ℕ} {x y v : ℕ} (hx : x ∈ S) (hy : y ∈ S) (h : mAnd x y = v ∨ mOr x y = v) :
    canBin S v = true := by
  unfold canBin
  refine List.any_eq_true.mpr ⟨x, hx, List.any_eq_true.mpr ⟨y, hy, ?_⟩⟩
  rcases h with h | h <;> simp [h]

theorem canNeg_intro {S : List ℕ} {x v : ℕ} (hx : x ∈ S) (h : mNot x = v) : canNeg S v = true := by
  unfold canNeg
  exact List.any_eq_true.mpr ⟨x, hx, by simp [h]⟩

theorem classify {M S : List ℕ} (hMS : M ⊆ S) (h0 : 0 ∈ M) (h1 : 63 ∈ M) (g : Gate) (hg : Legal g) :
    gmask M g ∈ S ∨ (g.op ≠ GateOp.not ∧ canBin S (gmask M g) = true) ∨
      (g.op = GateOp.not ∧ canNeg S (gmask M g) = true) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases ins with _ | ⟨i, _ | ⟨j, r⟩⟩
  · rcases hop with h | h | h <;> simp only at h <;> subst h
    · exact Or.inl (hMS h1)
    · exact Or.inl (hMS h0)
    · exact Or.inl (hMS h1)
  · rcases hop with h | h | h <;> simp only at h <;> subst h
    · exact Or.inl (hMS (getD_mem h0 i))
    · exact Or.inl (hMS (getD_mem h0 i))
    · exact Or.inr (Or.inr ⟨rfl, canNeg_intro (hMS (getD_mem h0 i)) rfl⟩)
  · rcases hop with h | h | h <;> simp only at h <;> subst h
    · exact Or.inr (Or.inl ⟨by simp, canBin_intro (hMS (getD_mem h0 i)) (hMS (getD_mem h0 j)) (Or.inl rfl)⟩)
    · exact Or.inr (Or.inl ⟨by simp, canBin_intro (hMS (getD_mem h0 i)) (hMS (getD_mem h0 j)) (Or.inr rfl)⟩)
    · exact Or.inr (Or.inr ⟨rfl, canNeg_intro (hMS (getD_mem h0 i)) rfl⟩)

theorem notCount_cons_not (g : Gate) (gs : List Gate) (o : ℕ) (h : g.op = GateOp.not) :
    PEqualNP.NotBracket.notCount ⟨g :: gs, o⟩ = PEqualNP.NotBracket.notCount ⟨gs, o⟩ + 1 := by
  unfold PEqualNP.NotBracket.notCount
  simp [h]

theorem notCount_cons_other (g : Gate) (gs : List Gate) (o : ℕ) (h : g.op ≠ GateOp.not) :
    PEqualNP.NotBracket.notCount ⟨g :: gs, o⟩ = PEqualNP.NotBracket.notCount ⟨gs, o⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp [h]

theorem notCount_cons_le (g : Gate) (gs : List Gate) (o : ℕ) :
    PEqualNP.NotBracket.notCount ⟨gs, o⟩ ≤ PEqualNP.NotBracket.notCount ⟨g :: gs, o⟩ := by
  unfold PEqualNP.NotBracket.notCount
  simp only [List.filter_cons]
  split <;> simp

theorem play (a b c : ℕ) : ∀ (gs : List Gate) (M S : List ℕ) (f n : ℕ),
    (∀ g ∈ gs, Legal g) → gs.length ≤ f → PEqualNP.NotBracket.notCount ⟨gs, 0⟩ ≤ n →
    M ⊆ S → 0 ∈ M → 63 ∈ M → (∀ m ∈ M, m < 64) →
    a ∈ run M gs → b ∈ run M gs → c ∈ run M gs → Play a b c f n S := by
  intro gs
  induction gs with
  | nil =>
    intro M S f n _ _ _ hMS _ _ _ ha hb hc
    refine Play.done ?_
    have ha' : a ∈ S := hMS ha
    have hb' : b ∈ S := hMS hb
    have hc' : c ∈ S := hMS hc
    simp [have3, ha', hb', hc']
  | cons g gs ih =>
    intro M S f n hg hlen hnot hMS h0 h1 hM ha hb hc
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hlen; omega⟩
    have hlen' : gs.length ≤ f := by simp at hlen; omega
    have hg' : ∀ g' ∈ gs, Legal g' := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    have hgl : Legal g := hg g (List.mem_cons_self ..)
    rw [run_cons] at ha hb hc
    have hnle := notCount_cons_le g gs 0
    have h0' : 0 ∈ M ++ [gmask M g] := List.mem_append_left _ h0
    have h1' : 63 ∈ M ++ [gmask M g] := List.mem_append_left _ h1
    have hM' := append_lt hM g
    by_cases hv : gmask M g ∈ S
    · have hsub : M ++ [gmask M g] ⊆ S := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hMS h
        · rw [List.mem_singleton.mp h]; exact hv
      exact Play.skip (ih _ S f n hg' hlen' (by omega) hsub h0' h1' hM' ha hb hc)
    · have hsub : M ++ [gmask M g] ⊆ gmask M g :: S := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact List.mem_cons_of_mem _ (hMS h)
        · rw [List.mem_singleton.mp h]; exact List.mem_cons_self ..
      rcases classify hMS h0 h1 g hgl with h | ⟨hne, hcb⟩ | ⟨he, hcn⟩
      · exact absurd h hv
      · rw [notCount_cons_other g gs 0 hne] at hnot
        exact Play.bin _ (gmask_lt hM g) hv hcb (ih _ _ f n hg' hlen' (by omega) hsub h0' h1' hM' ha hb hc)
      · rw [notCount_cons_not g gs 0 he] at hnot
        obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        exact Play.neg _ (gmask_lt hM g) hv hcn (ih _ _ f n hg' hlen' (by omega) hsub h0' h1' hM' ha hb hc)

theorem roots_rep : ∀ t : Fin 6,
    (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true] = roots.map (tb t.val) := by decide

theorem roots_lt : ∀ m ∈ roots, m < 64 := by decide

/-- A wire of the circuit whose values on the five inputs are the bits of `A` has the mask `A`. -/
theorem target_mem (A : ℕ) (hA : ∀ m : Fin 64, (∀ t : Fin 6, tb t.val m.val = A.testBit t.val) → m.val = A)
    (gs : List Gate) (hg : ∀ g ∈ gs, Legal g) (p : ℕ)
    (h : ∀ t : Fin 6, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true])).getD p false = A.testBit t.val) :
    A ∈ run roots gs := by
  have hlt := run_lt gs roots roots_lt
  have h0 : 0 ∈ run roots gs := run_sub gs roots (by decide)
  have hm : (run roots gs).getD p 0 < 64 := getD_lt hlt p
  have e := hA ⟨(run roots gs).getD p 0, hm⟩ (by
    intro t
    have ht := h t
    rw [roots_rep t, sem t gs roots hg roots_lt, rd] at ht
    exact ht)
  simp only at e
  rw [← e]
  exact getD_mem h0 p

/-! ## This row: the masks 4, 20, 38, at most 6 gates, at most 2 NOT gates -/

theorem eqA : ∀ m : Fin 64, (∀ t : Fin 6, tb t.val m.val = (4 : ℕ).testBit t.val) → m.val = 4 := by decide
theorem eqB : ∀ m : Fin 64, (∀ t : Fin 6, tb t.val m.val = (20 : ℕ).testBit t.val) → m.val = 20 := by decide
theorem eqC : ∀ m : Fin 64, (∀ t : Fin 6, tb t.val m.val = (38 : ℕ).testBit t.val) → m.val = 38 := by decide

set_option maxRecDepth 100000 in
theorem none_n0 : srch 4 20 38 5 1 [1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n1 : srch 4 20 38 5 1 [3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_b0 : srch 4 20 38 3 1 [6, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_b1 : srch 4 20 38 3 1 [36, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_b2 : srch 4 20 38 3 1 [39, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_b3 : srch 4 20 38 3 1 [52, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_b4 : srch 4 20 38 3 1 [55, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_n0 : srch 4 20 38 3 0 [1, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_n1 : srch 4 20 38 3 0 [3, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_n2 : srch 4 20 38 3 0 [15, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_n3 : srch 4 20 38 3 0 [31, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b0_n4 : srch 4 20 38 3 0 [59, 4, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

theorem none_n2_b0 : srch 4 20 38 4 1 [4, 7, 62, 60, 56, 48, 32, 0, 63] = false :=
  split_node 4 20 38 3 1 [4, 7, 62, 60, 56, 48, 32, 0, 63] [6, 36, 39, 52, 55] [1, 3, 15, 31, 59] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact none_n2_b0_b0
    · exact none_n2_b0_b1
    · exact none_n2_b0_b2
    · exact none_n2_b0_b3
    · exact none_n2_b0_b4)
  (by
    intro _ v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact none_n2_b0_n0
    · exact none_n2_b0_n1
    · exact none_n2_b0_n2
    · exact none_n2_b0_n3
    · exact none_n2_b0_n4)

set_option maxRecDepth 100000 in
theorem none_n2_b1 : srch 4 20 38 4 1 [6, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b2 : srch 4 20 38 4 1 [39, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_b3 : srch 4 20 38 4 1 [55, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_n0 : srch 4 20 38 4 0 [1, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_n1 : srch 4 20 38 4 0 [3, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_n2 : srch 4 20 38 4 0 [15, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n2_n3 : srch 4 20 38 4 0 [31, 7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

theorem none_n2 : srch 4 20 38 5 1 [7, 62, 60, 56, 48, 32, 0, 63] = false :=
  split_node 4 20 38 4 1 [7, 62, 60, 56, 48, 32, 0, 63] [4, 6, 39, 55] [1, 3, 15, 31] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact none_n2_b0
    · exact none_n2_b1
    · exact none_n2_b2
    · exact none_n2_b3)
  (by
    intro _ v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact none_n2_n0
    · exact none_n2_n1
    · exact none_n2_n2
    · exact none_n2_n3)

set_option maxRecDepth 100000 in
theorem none_n3 : srch 4 20 38 5 1 [15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
theorem none_n4 : srch 4 20 38 5 1 [31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

theorem none : srch 4 20 38 6 2 [62, 60, 56, 48, 32, 0, 63] = false :=
  split_node 4 20 38 5 2 [62, 60, 56, 48, 32, 0, 63] [] [1, 3, 7, 15, 31] (by decide +kernel) (by decide +kernel) (by decide +kernel)
  (by intro v hv; cases hv)
  (by
    intro _ v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact none_n0
    · exact none_n1
    · exact none_n2
    · exact none_n3
    · exact none_n4)

end PEqualNP.Outside.L_meta_50968

theorem PEqualNP.Outside.L_meta_50968 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (20 : Nat).testBit t.val ∧
    w.getD r.val false = (38 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hfan, -, hnot, hsize, h⟩
  have hg : ∀ g ∈ D.gates, PEqualNP.Outside.L_meta_50968.Legal g := by
    intro g mem
    obtain ⟨ops, cap⟩ := hfan g mem
    change g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not at ops
    exact ⟨ops, cap⟩
  have ha := PEqualNP.Outside.L_meta_50968.target_mem 4 PEqualNP.Outside.L_meta_50968.eqA D.gates hg p.val (fun t => (h t).1)
  have hb := PEqualNP.Outside.L_meta_50968.target_mem 20 PEqualNP.Outside.L_meta_50968.eqB D.gates hg q.val (fun t => (h t).2.1)
  have hc := PEqualNP.Outside.L_meta_50968.target_mem 38 PEqualNP.Outside.L_meta_50968.eqC D.gates hg r.val (fun t => (h t).2.2)
  have hp := PEqualNP.Outside.L_meta_50968.play 4 20 38 D.gates PEqualNP.Outside.L_meta_50968.roots PEqualNP.Outside.L_meta_50968.roots 6 2 hg hsize hnot
    (List.Subset.refl _) (by decide) (by decide) PEqualNP.Outside.L_meta_50968.roots_lt ha hb hc
  have hs := PEqualNP.Outside.L_meta_50968.play_srch (by decide) (by decide) (by decide) hp
  have hnone : PEqualNP.Outside.L_meta_50968.srch 4 20 38 6 2 PEqualNP.Outside.L_meta_50968.roots = false := PEqualNP.Outside.L_meta_50968.none
  rw [hnone] at hs
  exact Bool.noConfusion hs
