import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

-- No circuit of at most 5 gates, at most two of them NOT, on the 5 thresholds and the two constants
-- has wires carrying the three outputs 4, 16, 54 (read as bits over the six promise inputs).
--
-- Every wire is read as a 6-bit number. A gate makes a number that is the AND or OR of two
-- numbers already there, or 63 minus one of them for a NOT. `srch` tries all ways to add numbers:
-- a gate that repeats a number is dropped, and when as many targets are missing as gates remain the
-- next gate must make a target. `main` shows that a circuit with the three outputs makes `srch`
-- succeed; the search itself is then evaluated and fails.

namespace PEqualNP.Outside.L_meta_51128

open PEqualNP.CircuitLowerBounds

/-- The wire list after running a gate list on a wire list: the fold inside `Circuit.wires`. -/
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem run_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    run (g :: gs) w = run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem run_append (gs hs : List Gate) (w : List Bool) : run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

theorem run_len (gs : List Gate) : ∀ w : List Bool, (run gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [run]
  | cons g gs ih => intro w; rw [run_cons, ih]; simp; omega

theorem run_old (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (run gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [run_cons, ih _ i (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

theorem getD_last (V : List Bool) (e : Bool) : (V ++ [e]).getD V.length false = e := by simp

/-- The value of a gate in the whole run is its operation on the values of the wires it reads. -/
theorem wire_new (pre : List Gate) (g : Gate) (suf : List Gate) (x : List Bool)
    (h : ∀ a ∈ g.inputs, a < x.length + pre.length) :
    (run (pre ++ g :: suf) x).getD (x.length + pre.length) false =
      g.op.eval (g.inputs.map fun a => (run (pre ++ g :: suf) x).getD a false) := by
  rw [run_append, run_cons]
  have hl : (run pre x).length = x.length + pre.length := run_len pre x
  have e1 : (run suf (run pre x ++ [g.op.eval (g.inputs.map fun i => (run pre x).getD i false)])).getD
      (x.length + pre.length) false = g.op.eval (g.inputs.map fun i => (run pre x).getD i false) := by
    rw [run_old _ _ _ (by simp [hl]), ← hl, getD_last]
  rw [e1]
  congr 1
  apply List.map_congr_left
  intro a ha
  have ha' := h a ha
  have e2 : (run suf (run pre x ++ [g.op.eval (g.inputs.map fun i => (run pre x).getD i false)])).getD
      a false = (run pre x).getD a false := by
    rw [run_old suf _ a (by rw [List.length_append, hl]; omega),
      List.getD_append _ _ _ _ (by rw [hl]; exact ha')]
  exact e2.symm

/-- The promise input number `t`: the four thresholds, then false and true. -/
def xs (t : Fin 6) : List Bool := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false, true]

theorem xs_len (t : Fin 6) : (xs t).length = 7 := by simp [xs]

/-- Five bits as a number. -/
def mk (b0 b1 b2 b3 b4 b5 : Bool) : ℕ :=
  b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * b4.toNat + 32 * b5.toNat

theorem mk_lt (b0 b1 b2 b3 b4 b5 : Bool) : mk b0 b1 b2 b3 b4 b5 < 64 := by
  revert b0 b1 b2 b3 b4 b5; decide +kernel

theorem mk_and (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    mk (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5) =
      mk a0 a1 a2 a3 a4 a5 &&& mk b0 b1 b2 b3 b4 b5 := by
  revert a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5; decide +kernel

theorem mk_or (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    mk (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5) =
      mk a0 a1 a2 a3 a4 a5 ||| mk b0 b1 b2 b3 b4 b5 := by
  revert a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5; decide +kernel

theorem mk_not (a0 a1 a2 a3 a4 a5 : Bool) :
    mk (!a0) (!a1) (!a2) (!a3) (!a4) (!a5) = 63 ^^^ mk a0 a1 a2 a3 a4 a5 := by
  revert a0 a1 a2 a3 a4 a5; decide +kernel

theorem mk_bits (a : Fin 64) :
    mk (a.val.testBit 0) (a.val.testBit 1) (a.val.testBit 2) (a.val.testBit 3) (a.val.testBit 4) (a.val.testBit 5) =
      a.val := by
  revert a; decide +kernel

theorem lt_and (a b : Fin 64) : a.val &&& b.val < 64 := by revert a b; decide +kernel
theorem lt_or (a b : Fin 64) : a.val ||| b.val < 64 := by revert a b; decide +kernel
theorem lt_not (a : Fin 64) : 63 ^^^ a.val < 64 := by revert a; decide +kernel

/-- The value of wire `j` on promise input `t`. -/
def col (gs : List Gate) (j : ℕ) (t : Fin 6) : Bool := (run gs (xs t)).getD j false

/-- The five values of wire `j` as a number. -/
def M (gs : List Gate) (j : ℕ) : ℕ :=
  mk (col gs j 0) (col gs j 1) (col gs j 2) (col gs j 3) (col gs j 4) (col gs j 5)

theorem M_lt (gs : List Gate) (j : ℕ) : M gs j < 64 := mk_lt _ _ _ _ _ _

theorem M_and (gs : List Gate) (j u w : ℕ) (h : ∀ t, col gs j t = (col gs u t && col gs w t)) :
    M gs j = M gs u &&& M gs w := by
  unfold M; rw [h 0, h 1, h 2, h 3, h 4, h 5]; exact mk_and _ _ _ _ _ _ _ _ _ _ _ _

theorem M_or (gs : List Gate) (j u w : ℕ) (h : ∀ t, col gs j t = (col gs u t || col gs w t)) :
    M gs j = M gs u ||| M gs w := by
  unfold M; rw [h 0, h 1, h 2, h 3, h 4, h 5]; exact mk_or _ _ _ _ _ _ _ _ _ _ _ _

theorem M_not (gs : List Gate) (j u : ℕ) (h : ∀ t, col gs j t = !col gs u t) :
    M gs j = 63 ^^^ M gs u := by
  unfold M; rw [h 0, h 1, h 2, h 3, h 4, h 5]; exact mk_not _ _ _ _ _ _

theorem M_copy (gs : List Gate) (j u : ℕ) (h : ∀ t, col gs j t = col gs u t) : M gs j = M gs u := by
  unfold M; rw [h 0, h 1, h 2, h 3, h 4, h 5]

theorem M_true (gs : List Gate) (j : ℕ) (h : ∀ t, col gs j t = true) : M gs j = 63 := by
  unfold M; rw [h 0, h 1, h 2, h 3, h 4, h 5]; rfl

theorem M_false (gs : List Gate) (j : ℕ) (h : ∀ t, col gs j t = false) : M gs j = 0 := by
  unfold M; rw [h 0, h 1, h 2, h 3, h 4, h 5]; rfl

theorem col_input (gs : List Gate) (j : ℕ) (hj : j < 7) (t : Fin 6) :
    col gs j t = (xs t).getD j false :=
  run_old gs (xs t) j (by rw [xs_len]; exact hj)

/-- The numbers of the six inputs. -/
def S0 : List ℕ := [62, 60, 56, 48, 32, 0, 63]

theorem M_input (gs : List Gate) (j : ℕ) (hj : j < 7) : M gs j ∈ S0 := by
  unfold M
  rw [col_input gs j hj 0, col_input gs j hj 1, col_input gs j hj 2, col_input gs j hj 3, col_input gs j hj 4, col_input gs j hj 5]
  interval_cases j <;> decide

theorem M_four (gs : List Gate) : M gs 5 = 0 := by
  unfold M
  rw [col_input gs 5 (by omega) 0, col_input gs 5 (by omega) 1, col_input gs 5 (by omega) 2, col_input gs 5 (by omega) 3, col_input gs 5 (by omega) 4, col_input gs 5 (by omega) 5]
  decide

theorem M_five (gs : List Gate) : M gs 6 = 63 := by
  unfold M
  rw [col_input gs 6 (by omega) 0, col_input gs 6 (by omega) 1, col_input gs 6 (by omega) 2, col_input gs 6 (by omega) 3, col_input gs 6 (by omega) 4, col_input gs 6 (by omega) 5]
  decide

/-- The targets `T` can be reached from the numbers `S` with `k` more gates, `n` of them NOT. -/
inductive Reach (T : List ℕ) : ℕ → ℕ → List ℕ → Prop
  | done {k n : ℕ} {S : List ℕ} : (∀ v ∈ T, v ∈ S) → Reach T k n S
  | ao {k n : ℕ} {S : List ℕ} (a b : ℕ) (c : Bool) : a ∈ S → b ∈ S →
      Reach T k n ((if c then a &&& b else a ||| b) :: S) → Reach T (k + 1) n S
  | nt {k n : ℕ} {S : List ℕ} (a : ℕ) : a ∈ S →
      Reach T k n ((63 ^^^ a) :: S) → Reach T (k + 1) (n + 1) S

/-- A circuit gives a way to reach its outputs. -/
theorem reach_of (T : List ℕ) (gs : List Gate) (isNot : Gate → Bool)
    (hisNot : ∀ g, isNot g = true ↔ g.op = GateOp.not)
    (hF : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hout : ∀ v ∈ T, ∃ j, j < 7 + gs.length ∧ M gs j = v) :
    ∀ (suf pre : List Gate), pre ++ suf = gs →
      (∀ (j : ℕ) (g : Gate), suf[j]? = some g → ∀ a ∈ g.inputs, a < 7 + pre.length + j) →
      ∀ (n : ℕ) (S : List ℕ), (∀ j < 7 + pre.length, M gs j ∈ S) →
        (suf.filter isNot).length ≤ n →
        Reach T suf.length n S := by
  intro suf
  induction suf with
  | nil =>
    intro pre hpre _ n S hS _
    rw [List.append_nil] at hpre
    apply Reach.done
    intro v hv
    obtain ⟨j, hj, rfl⟩ := hout v hv
    exact hS j (by rw [hpre]; exact hj)
  | cons g suf ih =>
    intro pre hpre hrb n S hS hn
    have hg := hF g (by rw [← hpre]; simp)
    have hin : ∀ a ∈ g.inputs, a < 7 + pre.length := by
      intro a ha
      have := hrb 0 g (by simp) a ha
      simpa using this
    have hcol : ∀ t : Fin 6, col gs (7 + pre.length) t =
        g.op.eval (g.inputs.map fun a => col gs a t) := by
      intro t
      have e := wire_new pre g suf (xs t) (by rw [xs_len]; exact hin)
      rw [xs_len, hpre] at e
      exact e
    have hS' : ∀ v : ℕ, M gs (7 + pre.length) = v →
        ∀ j < 7 + (pre ++ [g]).length, M gs j ∈ v :: S := by
      intro v hv j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hj' : j = 7 + pre.length
      · rw [hj', hv]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hS j (by omega))
    have hrb' : ∀ (j : ℕ) (g' : Gate), suf[j]? = some g' →
        ∀ a ∈ g'.inputs, a < 7 + (pre ++ [g]).length + j := by
      intro j g' hj a ha
      have := hrb (j + 1) g' (by simpa using hj) a ha
      simp only [List.length_append, List.length_singleton]
      omega
    have hpre' : (pre ++ [g]) ++ suf = gs := by rw [List.append_assoc]; exact hpre
    have h0S : 0 ∈ S := by have := hS 5 (by omega); rwa [M_four] at this
    have h63S : 63 ∈ S := by have := hS 6 (by omega); rwa [M_five] at this
    have key : (g.op ≠ GateOp.not ∧ ∃ a ∈ S, ∃ b ∈ S, ∃ c : Bool,
          M gs (7 + pre.length) = (if c then a &&& b else a ||| b)) ∨
        (g.op = GateOp.not ∧ ∃ a ∈ S, M gs (7 + pre.length) = 63 ^^^ a) := by
      rcases hin' : g.inputs with _ | ⟨u, _ | ⟨w, _ | ⟨z, rest⟩⟩⟩
      · rcases hg.1 with hop | hop | hop
        · refine Or.inl ⟨(by rw [hop]; exact fun h => nomatch h), 63, h63S, 63, h63S, true, ?_⟩
          rw [M_true gs _ (fun t => by rw [hcol t, hin', hop]; rfl)]; rfl
        · refine Or.inl ⟨(by rw [hop]; exact fun h => nomatch h), 0, h0S, 0, h0S, false, ?_⟩
          rw [M_false gs _ (fun t => by rw [hcol t, hin', hop]; rfl)]; rfl
        · refine Or.inr ⟨hop, 0, h0S, ?_⟩
          rw [M_true gs _ (fun t => by rw [hcol t, hin', hop]; rfl)]; rfl
      · have hu : u < 7 + pre.length := hin u (by rw [hin']; simp)
        rcases hg.1 with hop | hop | hop
        · refine Or.inl ⟨(by rw [hop]; exact fun h => nomatch h), M gs u, hS u hu, M gs u, hS u hu, true, ?_⟩
          rw [M_copy gs _ u (fun t => by rw [hcol t, hin', hop]; simp [GateOp.eval])]
          simp
        · refine Or.inl ⟨(by rw [hop]; exact fun h => nomatch h), M gs u, hS u hu, M gs u, hS u hu, false, ?_⟩
          rw [M_copy gs _ u (fun t => by rw [hcol t, hin', hop]; simp [GateOp.eval])]
          simp
        · refine Or.inr ⟨hop, M gs u, hS u hu, ?_⟩
          exact M_not gs _ u (fun t => by rw [hcol t, hin', hop]; simp [GateOp.eval])
      · have hu : u < 7 + pre.length := hin u (by rw [hin']; simp)
        have hw : w < 7 + pre.length := hin w (by rw [hin']; simp)
        rcases hg.1 with hop | hop | hop
        · refine Or.inl ⟨(by rw [hop]; exact fun h => nomatch h), M gs u, hS u hu, M gs w, hS w hw, true, ?_⟩
          rw [M_and gs _ u w (fun t => by rw [hcol t, hin', hop]; simp [GateOp.eval])]
          simp
        · refine Or.inl ⟨(by rw [hop]; exact fun h => nomatch h), M gs u, hS u hu, M gs w, hS w hw, false, ?_⟩
          rw [M_or gs _ u w (fun t => by rw [hcol t, hin', hop]; simp [GateOp.eval])]
          simp
        · refine Or.inr ⟨hop, M gs u, hS u hu, ?_⟩
          exact M_not gs _ u (fun t => by rw [hcol t, hin', hop]; simp [GateOp.eval])
      · exfalso
        have h2 := hg.2
        rw [hin'] at h2
        simp at h2
    rcases key with ⟨hne, a, ha, b, hb, c, hv⟩ | ⟨hop, a, ha, hv⟩
    · have hno : isNot g = false := by
        cases hc : isNot g
        · rfl
        · exact absurd ((hisNot g).1 hc) hne
      have hn' : (suf.filter isNot).length ≤ n := by
        simpa [List.filter_cons, hno] using hn
      exact Reach.ao a b c ha hb (ih (pre ++ [g]) hpre' hrb' n _ (hS' _ hv) hn')
    · have hyes : isNot g = true := (hisNot g).2 hop
      have hn1 : (suf.filter isNot).length + 1 ≤ n := by
        simpa [List.filter_cons, hyes] using hn
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      exact Reach.nt a ha (ih (pre ++ [g]) hpre' hrb' n' _ (hS' _ hv) (by omega))

/-- The targets not yet among the numbers. -/
def missing (T S : List ℕ) : List ℕ := T.filter (fun v => !S.contains v)

def aoOk (S : List ℕ) (v : ℕ) : Bool :=
  S.any (fun a => S.any (fun b => (a &&& b == v) || (a ||| b == v)))

def ntOk (S : List ℕ) (v : ℕ) : Bool := S.any (fun a => (63 ^^^ a) == v)

/-- The exhaustive search: can the targets be reached with `k` more gates, `n` of them NOT?  A gate must
give a new number; when as many targets are missing as gates remain, it must give a target. -/
def srch (T : List ℕ) : ℕ → ℕ → List ℕ → Bool
  | 0, _, S => (missing T S).isEmpty
  | k + 1, n, S =>
    (missing T S).isEmpty ||
    (decide ((missing T S).length ≤ k + 1) &&
      (List.range 64).any (fun v =>
        !S.contains v && (decide ((missing T S).length ≤ k) || (missing T S).contains v) &&
        ((aoOk S v && srch T k n (v :: S)) ||
          (match n with
            | 0 => false
            | n' + 1 => ntOk S v && srch T k n' (v :: S)))))

theorem mem_missing (T S : List ℕ) (v : ℕ) : v ∈ missing T S ↔ v ∈ T ∧ v ∉ S := by
  simp [missing]

theorem missing_empty (T S : List ℕ) : (missing T S).isEmpty = true ↔ ∀ v ∈ T, v ∈ S := by
  rw [List.isEmpty_iff]
  constructor
  · intro h v hv
    by_contra hc
    have hm : v ∈ missing T S := (mem_missing T S v).2 ⟨hv, hc⟩
    rw [h] at hm
    simp at hm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.2
    intro v hv
    exact ((mem_missing T S v).1 hv).2 (h v ((mem_missing T S v).1 hv).1)

theorem aoOk_iff (S : List ℕ) (v : ℕ) :
    aoOk S v = true ↔ ∃ a ∈ S, ∃ b ∈ S, a &&& b = v ∨ a ||| b = v := by
  simp [aoOk]

theorem ntOk_iff (S : List ℕ) (v : ℕ) : ntOk S v = true ↔ ∃ a ∈ S, 63 ^^^ a = v := by
  simp [ntOk]

theorem srch_zero (T : List ℕ) (n : ℕ) (S : List ℕ) :
    srch T 0 n S = (missing T S).isEmpty := by
  rfl

theorem srch_succ (T : List ℕ) (k n : ℕ) (S : List ℕ) : srch T (k + 1) n S = true ↔
    (missing T S).isEmpty = true ∨ ((missing T S).length ≤ k + 1 ∧ ∃ v, v < 64 ∧ v ∉ S ∧
      ((missing T S).length ≤ k ∨ v ∈ missing T S) ∧
      ((aoOk S v = true ∧ srch T k n (v :: S) = true) ∨
        (∃ n', n = n' + 1 ∧ ntOk S v = true ∧ srch T k n' (v :: S) = true))) := by
  cases n with
  | zero =>
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_range, Bool.not_eq_true', List.contains_iff_mem, Bool.or_false]
    constructor
    · rintro (h | ⟨h1, v, hv, ⟨h2, h3⟩, h4⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, v, hv, by simpa using h2, h3, Or.inl h4⟩
    · rintro (h | ⟨h1, v, hv, h2, h3, h4⟩)
      · exact Or.inl h
      · rcases h4 with h4 | ⟨n', hn', -⟩
        · exact Or.inr ⟨h1, v, hv, ⟨by simpa using h2, h3⟩, h4⟩
        · omega
  | succ m =>
    simp only [srch, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
      List.mem_range, Bool.not_eq_true', List.contains_iff_mem]
    constructor
    · rintro (h | ⟨h1, v, hv, ⟨h2, h3⟩, h4⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1, v, hv, by simpa using h2, h3, ?_⟩
        rcases h4 with h4 | h4
        · exact Or.inl h4
        · exact Or.inr ⟨m, rfl, h4⟩
    · rintro (h | ⟨h1, v, hv, h2, h3, h4⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1, v, hv, ⟨by simpa using h2, h3⟩, ?_⟩
        rcases h4 with h4 | ⟨n', hn', h4⟩
        · exact Or.inl h4
        · obtain rfl : n' = m := by omega
          exact Or.inr h4

theorem srch_len (T : List ℕ) (k n : ℕ) (S : List ℕ) (h : srch T k n S = true) :
    (missing T S).length ≤ k := by
  cases k with
  | zero =>
    rw [srch_zero, List.isEmpty_iff] at h
    rw [h]; simp
  | succ k =>
    rcases (srch_succ T k n S).1 h with h | ⟨h, -⟩
    · rw [List.isEmpty_iff] at h
      rw [h]; simp
    · exact h

theorem srch_mono_k (T : List ℕ) : ∀ (k n : ℕ) (S : List ℕ),
    srch T k n S = true → srch T (k + 1) n S = true := by
  intro k
  induction k with
  | zero =>
    intro n S h
    rw [srch_zero] at h
    exact (srch_succ T 0 n S).2 (Or.inl h)
  | succ k ih =>
    intro n S h
    rcases (srch_succ T k n S).1 h with h | ⟨h1, v, hv, h2, h3, h4⟩
    · exact (srch_succ T (k + 1) n S).2 (Or.inl h)
    · refine (srch_succ T (k + 1) n S).2 (Or.inr ⟨by omega, v, hv, h2, Or.inl h1, ?_⟩)
      rcases h4 with ⟨h4, h5⟩ | ⟨n', hn', h4, h5⟩
      · exact Or.inl ⟨h4, ih n _ h5⟩
      · exact Or.inr ⟨n', hn', h4, ih n' _ h5⟩

theorem srch_mono_n (T : List ℕ) : ∀ (k n : ℕ) (S : List ℕ),
    srch T k n S = true → srch T k (n + 1) S = true := by
  intro k
  induction k with
  | zero =>
    intro n S h
    rw [srch_zero] at h ⊢
    exact h
  | succ k ih =>
    intro n S h
    rcases (srch_succ T k n S).1 h with h | ⟨h1, v, hv, h2, h3, h4⟩
    · exact (srch_succ T k (n + 1) S).2 (Or.inl h)
    · refine (srch_succ T k (n + 1) S).2 (Or.inr ⟨h1, v, hv, h2, h3, ?_⟩)
      rcases h4 with ⟨h4, h5⟩ | ⟨n', hn', h4, h5⟩
      · exact Or.inl ⟨h4, ih n _ h5⟩
      · exact Or.inr ⟨n' + 1, by omega, h4, ih n' _ h5⟩

theorem missing_congr (T S S' : List ℕ) (h : ∀ x, x ∈ S ↔ x ∈ S') : missing T S = missing T S' := by
  unfold missing
  apply List.filter_congr
  intro x _
  have e : S.contains x = S'.contains x := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact h x
  rw [e]

/-- The search depends on the set of numbers only. -/
theorem srch_set (T : List ℕ) : ∀ (k n : ℕ) (S S' : List ℕ), (∀ x, x ∈ S ↔ x ∈ S') →
    srch T k n S = true → srch T k n S' = true := by
  intro k
  induction k with
  | zero =>
    intro n S S' hS h
    rw [srch_zero] at h ⊢
    rw [← missing_congr T S S' hS]
    exact h
  | succ k ih =>
    intro n S S' hS h
    have hm := missing_congr T S S' hS
    have hcons : ∀ v x, x ∈ v :: S ↔ x ∈ v :: S' := by
      intro v x
      simp only [List.mem_cons]
      rw [hS x]
    rcases (srch_succ T k n S).1 h with h | ⟨h1, v, hv, h2, h3, h4⟩
    · exact (srch_succ T k n S').2 (Or.inl (by rw [← hm]; exact h))
    · refine (srch_succ T k n S').2 (Or.inr ⟨by rw [← hm]; exact h1, v, hv,
        fun hc => h2 ((hS v).2 hc), by rw [← hm]; exact h3, ?_⟩)
      rcases h4 with ⟨h4, h5⟩ | ⟨n', hn', h4, h5⟩
      · refine Or.inl ⟨?_, ih n _ _ (hcons v) h5⟩
        obtain ⟨a, ha, b, hb, hab⟩ := (aoOk_iff S v).1 h4
        exact (aoOk_iff S' v).2 ⟨a, (hS a).1 ha, b, (hS b).1 hb, hab⟩
      · refine Or.inr ⟨n', hn', ?_, ih n' _ _ (hcons v) h5⟩
        obtain ⟨a, ha, hav⟩ := (ntOk_iff S v).1 h4
        exact (ntOk_iff S' v).2 ⟨a, (hS a).1 ha, hav⟩

theorem missing_cons_len (T S : List ℕ) (hT : T.Nodup) (v : ℕ) :
    (missing T S).length ≤ (missing T (v :: S)).length + 1 := by
  have hnd : (missing T S).Nodup := hT.filter _
  have hsub : missing T S ⊆ v :: missing T (v :: S) := by
    intro x hx
    obtain ⟨hxT, hxS⟩ := (mem_missing T S x).1 hx
    by_cases hxv : x = v
    · rw [hxv]; exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ((mem_missing T (v :: S) x).2 ⟨hxT, ?_⟩)
      intro hc
      rcases List.mem_cons.1 hc with hc | hc
      · exact hxv hc
      · exact hxS hc
  have hle := (List.subperm_of_subset hnd hsub).length_le
  simpa using hle

theorem missing_cons_same (T S : List ℕ) (v : ℕ) (hv : v ∉ missing T S) (hvS : v ∉ S) :
    missing T (v :: S) = missing T S := by
  unfold missing
  apply List.filter_congr
  intro x hx
  have hxv : x ≠ v := by
    intro hc
    apply hv
    rw [← hc]
    exact (mem_missing T S x).2 ⟨hx, by rw [hc]; exact hvS⟩
  have e : (v :: S).contains x = S.contains x := by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact absurd h hxv
      · exact h
    · exact fun h => Or.inr h
  rw [e]

/-- One more gate giving the number `v`. -/
theorem srch_step (T : List ℕ) (hT : T.Nodup) (k n : ℕ) (S : List ℕ) (v : ℕ) (hv : v < 64)
    (hvS : v ∉ S) (h : srch T k n (v :: S) = true)
    (hlast : (aoOk S v = true ∧ srch T k n (v :: S) = true) ∨
      (∃ n', n = n' + 1 ∧ ntOk S v = true ∧ srch T k n' (v :: S) = true)) :
    srch T (k + 1) n S = true := by
  have hl := srch_len T k n (v :: S) h
  have hl2 := missing_cons_len T S hT v
  refine (srch_succ T k n S).2 (Or.inr ⟨by omega, v, hv, hvS, ?_, hlast⟩)
  by_cases hm : v ∈ missing T S
  · exact Or.inr hm
  · left
    rw [missing_cons_same T S v hm hvS] at hl
    exact hl

theorem srch_of_reach (T : List ℕ) (hT : T.Nodup) : ∀ {k n : ℕ} {S : List ℕ}, Reach T k n S →
    (∀ x ∈ S, x < 64) → srch T k n S = true := by
  intro k n S h
  induction h with
  | @done k n S hall =>
    intro _
    have he := (missing_empty T S).2 hall
    cases k with
    | zero => rw [srch_zero]; exact he
    | succ k => exact (srch_succ T k n S).2 (Or.inl he)
  | @ao k n S a b c ha hb _ ih =>
    intro hS
    have hnew : (if c then a &&& b else a ||| b) < 64 := by
      have h1 := lt_and ⟨a, hS a ha⟩ ⟨b, hS b hb⟩
      have h2 := lt_or ⟨a, hS a ha⟩ ⟨b, hS b hb⟩
      cases c
      · exact h2
      · exact h1
    have hrec := ih (by
      intro x hx
      rcases List.mem_cons.1 hx with hx | hx
      · rw [hx]; exact hnew
      · exact hS x hx)
    by_cases hin : (if c then a &&& b else a ||| b) ∈ S
    · apply srch_mono_k
      refine srch_set T k n _ S ?_ hrec
      intro x
      simp only [List.mem_cons]
      constructor
      · rintro (hx | hx)
        · rw [hx]; exact hin
        · exact hx
      · exact fun hx => Or.inr hx
    · refine srch_step T hT k n S _ hnew hin hrec (Or.inl ⟨?_, hrec⟩)
      refine (aoOk_iff S _).2 ⟨a, ha, b, hb, ?_⟩
      cases c
      · exact Or.inr rfl
      · exact Or.inl rfl
  | @nt k n S a ha _ ih =>
    intro hS
    have hnew : 63 ^^^ a < 64 := lt_not ⟨a, hS a ha⟩
    have hrec := ih (by
      intro x hx
      rcases List.mem_cons.1 hx with hx | hx
      · rw [hx]; exact hnew
      · exact hS x hx)
    by_cases hin : (63 ^^^ a) ∈ S
    · apply srch_mono_k
      apply srch_mono_n
      refine srch_set T k n _ S ?_ hrec
      intro x
      simp only [List.mem_cons]
      constructor
      · rintro (hx | hx)
        · rw [hx]; exact hin
        · exact hx
      · exact fun hx => Or.inr hx
    · exact srch_step T hT k (n + 1) S _ hnew hin (srch_mono_n T k n _ hrec)
        (Or.inr ⟨n, rfl, (ntOk_iff S _).2 ⟨a, ha, rfl⟩, hrec⟩)

theorem srch_mono_le (T : List ℕ) (n : ℕ) (S : List ℕ) : ∀ (k d : ℕ),
    srch T k n S = true → srch T (k + d) n S = true := by
  intro k d
  induction d with
  | zero => exact fun h => h
  | succ d ih => exact fun h => srch_mono_k T (k + d) n S (ih h)

/-- A circuit with the three outputs makes the search succeed. -/
theorem main (D : Circuit) (p q r : Fin (7 + D.size)) (a b c : ℕ) (K : ℕ)
    (ha : a < 64) (hb : b < 64) (hc : c < 64) (hnd : [a, b, c].Nodup)
    (hF : PEqualNP.MetaComplexity.FanInTwo D)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D)
    (hN : PEqualNP.NotBracket.notCount D ≤ 2) (hsz : D.size ≤ K)
    (hout : ∀ t : Fin 6,
      (run D.gates (xs t)).getD p.val false = a.testBit t.val ∧
      (run D.gates (xs t)).getD q.val false = b.testBit t.val ∧
      (run D.gates (xs t)).getD r.val false = c.testBit t.val) :
    srch [a, b, c] K 2 S0 = true := by
  have hMp : M D.gates p.val = a := by
    unfold M col
    rw [(hout 0).1, (hout 1).1, (hout 2).1, (hout 3).1, (hout 4).1, (hout 5).1]
    exact mk_bits ⟨a, ha⟩
  have hMq : M D.gates q.val = b := by
    unfold M col
    rw [(hout 0).2.1, (hout 1).2.1, (hout 2).2.1, (hout 3).2.1, (hout 4).2.1, (hout 5).2.1]
    exact mk_bits ⟨b, hb⟩
  have hMr : M D.gates r.val = c := by
    unfold M col
    rw [(hout 0).2.2, (hout 1).2.2, (hout 2).2.2, (hout 3).2.2, (hout 4).2.2, (hout 5).2.2]
    exact mk_bits ⟨c, hc⟩
  have hN2 := hN
  unfold PEqualNP.NotBracket.notCount at hN2
  obtain ⟨isNot, hisNot, hNle⟩ : ∃ isNot : Gate → Bool,
      (∀ g, isNot g = true ↔ g.op = GateOp.not) ∧ (D.gates.filter isNot).length ≤ 2 := by
    refine ⟨_, ?_, hN2⟩
    intro g
    simp only [decide_eq_true_eq]
  have hreach : Reach [a, b, c] D.gates.length 2 S0 := by
    refine reach_of [a, b, c] D.gates isNot hisNot ?_ ?_ D.gates [] rfl ?_ 2 S0 ?_ hNle
    · intro g hg
      obtain ⟨h1, h2⟩ := hF g hg
      refine ⟨?_, h2⟩
      simpa using h1
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨p.val, p.isLt, hMp⟩
      · exact ⟨q.val, q.isLt, hMq⟩
      · exact ⟨r.val, r.isLt, hMr⟩
    · intro j g hj x hx
      have hjl : j < D.gates.length := by
        by_contra hc
        rw [List.getElem?_eq_none (by omega)] at hj
        simp at hj
      have e : PEqualNP.MetaComplexity.NestedCover.gateAt D j = g := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem?_getD, hj]
        rfl
      have := hRB j hjl x (by rw [e]; exact hx)
      simpa using this
    · intro j hj
      exact M_input D.gates j (by simpa using hj)
  have hs := srch_of_reach [a, b, c] hnd hreach (by
    intro x hx
    simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  obtain ⟨d, hd⟩ : ∃ d, K = D.gates.length + d := ⟨K - D.gates.length, by
    have : D.gates.length ≤ K := hsz
    omega⟩
  rw [hd]
  exact srch_mono_le _ 2 S0 _ d hs

end PEqualNP.Outside.L_meta_51128

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_51128 : ¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (4 : Nat).testBit t.val ∧
    w.getD q.val false = (16 : Nat).testBit t.val ∧
    w.getD r.val false = (54 : Nat).testBit t.val) := by
  rintro ⟨D, p, q, r, hF, hRB, hN, hsz, hout⟩
  have h := PEqualNP.Outside.L_meta_51128.main D p q r 4 16 54 5 (by omega) (by omega) (by omega)
    (by decide) hF hRB hN hsz (fun t => hout t)
  have hfalse : PEqualNP.Outside.L_meta_51128.srch [4, 16, 54] 5 2 PEqualNP.Outside.L_meta_51128.S0 = false := by
    decide +kernel
  rw [hfalse] at h
  exact Bool.false_ne_true h
