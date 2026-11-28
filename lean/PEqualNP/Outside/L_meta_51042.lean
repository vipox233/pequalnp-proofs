import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_51042

def aev : PEqualNP.CircuitLowerBounds.GateOp → List ℕ → ℕ
  | .and, l => l.foldr (· &&& ·) 63
  | .or, l => l.foldr (· ||| ·) 0
  | .not, l => 63 - l.headD 0
  | _, _ => 0

def elems (S : ℕ) : List ℕ := (List.range 64).filter (fun v => S.testBit v)

def pmask (S : ℕ) : ℕ :=
  (elems S).foldl (fun acc a =>
    (elems S).foldl (fun acc b => acc ||| (2 ^ (a &&& b) ||| 2 ^ (a ||| b))) acc) 0

def nmask (S : ℕ) : ℕ := (elems S).foldl (fun acc a => acc ||| 2 ^ (63 - a)) 0

def goal (S : ℕ) : Bool := S.testBit 12 && S.testBit 40 && S.testBit 58

def miss (S : ℕ) : ℕ :=
  (if S.testBit 12 then 0 else 1) + (if S.testBit 40 then 0 else 1) + (if S.testBit 58 then 0 else 1)

def anyB : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | k+1, f => f k || anyB k f

def okc : ℕ → ℕ → ℕ → Bool
  | 0, _, S => goal S
  | n+1, b, S =>
    goal S || (decide (miss S ≤ n + 1) &&
    (anyB 64 (fun v => (pmask S).testBit v && !S.testBit v && okc n b (S ||| 2 ^ v)) ||
    (decide (0 < b) &&
      anyB 64 (fun v => (nmask S).testBit v && !S.testBit v && okc n (b-1) (S ||| 2 ^ v)))))

def S0 : ℕ := 2^62 ||| 2^60 ||| 2^56 ||| 2^48 ||| 2^32 ||| 2^0 ||| 2^63

theorem okc_false : okc 6 2 S0 = false := by decide +kernel

theorem anyB_mono (f g : ℕ → Bool) (h : ∀ k, f k = true → g k = true) :
    ∀ n, anyB n f = true → anyB n g = true := by
  intro n; induction n with
  | zero => simp [anyB]
  | succ n ih =>
    simp only [anyB, Bool.or_eq_true]
    rintro (h1 | h1)
    · exact Or.inl (h _ h1)
    · exact Or.inr (ih h1)

theorem anyB_of (f : ℕ → Bool) : ∀ n k, k < n → f k = true → anyB n f = true := by
  intro n; induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk hf
    simp only [anyB, Bool.or_eq_true]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · exact Or.inr (ih k h hf)
    · subst h; exact Or.inl hf

theorem okc_budget : ∀ n b b2 S, b ≤ b2 → okc n b S = true → okc n b2 S = true := by
  intro n; induction n with
  | zero => intro b b2 S _ h; simpa [okc] using h
  | succ n ih =>
    intro b b2 S hb h
    simp only [okc, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨hm, h | ⟨h0, h⟩⟩
    · exact Or.inl h
    · refine Or.inr ⟨hm, Or.inl ?_⟩
      refine anyB_mono _ _ ?_ _ h
      intro k hk
      simp only [Bool.and_eq_true] at hk ⊢
      exact ⟨hk.1, ih _ _ _ hb hk.2⟩
    · refine Or.inr ⟨hm, Or.inr ⟨by omega, ?_⟩⟩
      refine anyB_mono _ _ ?_ _ h
      intro k hk
      simp only [Bool.and_eq_true] at hk ⊢
      exact ⟨hk.1, ih _ _ _ (by omega) hk.2⟩

theorem okc_fuel : ∀ n b S, okc n b S = true → okc (n+1) b S = true := by
  intro n; induction n with
  | zero =>
    intro b S h
    simp only [okc, Bool.or_eq_true] at h ⊢
    exact Or.inl h
  | succ n ih =>
    intro b S h
    rw [okc] at h ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨hm, h | ⟨h0, h⟩⟩
    · exact Or.inl h
    · refine Or.inr ⟨by omega, Or.inl ?_⟩
      refine anyB_mono _ _ ?_ _ h
      intro k hk
      simp only [Bool.and_eq_true] at hk ⊢
      exact ⟨hk.1, ih _ _ hk.2⟩
    · refine Or.inr ⟨by omega, Or.inr ⟨h0, ?_⟩⟩
      refine anyB_mono _ _ ?_ _ h
      intro k hk
      simp only [Bool.and_eq_true] at hk ⊢
      exact ⟨hk.1, ih _ _ hk.2⟩

theorem okc_miss : ∀ n b S, okc n b S = true → miss S ≤ n := by
  intro n; cases n with
  | zero =>
    intro b S h
    simp only [okc, goal, Bool.and_eq_true] at h
    simp [miss, h.1.1, h.1.2, h.2]
  | succ n =>
    intro b S h
    rw [okc] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hm, _⟩
    · simp only [goal, Bool.and_eq_true] at h
      simp [miss, h.1.1, h.1.2, h.2]
    · exact hm

theorem miss_add (S v : ℕ) : miss S ≤ miss (S ||| 2 ^ v) + 1 := by
  simp only [miss, Nat.testBit_or, Nat.testBit_two_pow]
  by_cases h10 : v = 12 <;> by_cases h14 : v = 40 <;> by_cases h18 : v = 58 <;>
    simp_all <;> split_ifs <;> omega
theorem fold_keep (f : ℕ → ℕ → ℕ) (hf : ∀ acc x i, acc.testBit i = true → (f acc x).testBit i = true) :
    ∀ (l : List ℕ) acc i, acc.testBit i = true → (l.foldl f acc).testBit i = true := by
  intro l; induction l with
  | nil => intro acc i h; simpa using h
  | cons y l ih => intro acc i h; exact ih _ _ (hf _ _ _ h)

theorem fold_hit (f : ℕ → ℕ → ℕ) (hf : ∀ acc x i, acc.testBit i = true → (f acc x).testBit i = true)
    (x i : ℕ) (hx : ∀ acc, (f acc x).testBit i = true) :
    ∀ (l : List ℕ), x ∈ l → ∀ acc, (l.foldl f acc).testBit i = true := by
  intro l; induction l with
  | nil => intro h; simp at h
  | cons y l ih =>
    intro h acc
    rcases List.mem_cons.mp h with h | h
    · subst h; exact fold_keep f hf l _ _ (hx acc)
    · exact ih h _

theorem mem_elems (S a : ℕ) (ha : a < 64) (hs : S.testBit a = true) : a ∈ elems S := by
  simp [elems, ha, hs]

theorem pmask_hit (S a b : ℕ) (ha : a ∈ elems S) (hb : b ∈ elems S) :
    (pmask S).testBit (a &&& b) = true ∧ (pmask S).testBit (a ||| b) = true := by
  have kin : ∀ a, ∀ acc x i, acc.testBit i = true →
      (acc ||| (2 ^ (a &&& x) ||| 2 ^ (a ||| x))).testBit i = true := by
    intro a acc x i h; simp [Nat.testBit_or, h]
  have kout : ∀ acc x i, acc.testBit i = true →
      ((elems S).foldl (fun acc b => acc ||| (2 ^ (x &&& b) ||| 2 ^ (x ||| b))) acc).testBit i = true := by
    intro acc x i h; exact fold_keep _ (kin x) _ _ _ h
  constructor
  · refine fold_hit _ kout a _ ?_ _ ha 0
    intro acc
    refine fold_hit _ (kin a) b _ ?_ _ hb acc
    intro acc'; simp [Nat.testBit_or, Nat.testBit_two_pow]
  · refine fold_hit _ kout a _ ?_ _ ha 0
    intro acc
    refine fold_hit _ (kin a) b _ ?_ _ hb acc
    intro acc'; simp [Nat.testBit_or, Nat.testBit_two_pow]

theorem nmask_hit (S a : ℕ) (ha : a ∈ elems S) :
    (nmask S).testBit (63 - a) = true := by
  refine fold_hit _ ?_ a _ ?_ _ ha 0
  · intro acc x i h; simp [Nat.testBit_or, h]
  · intro acc; simp [Nat.testBit_or, Nat.testBit_two_pow]


theorem and_bit (t : ℕ) (ht : t < 6) : ∀ l : List ℕ,
    (l.foldr (· &&& ·) 63).testBit t = l.all (fun a => a.testBit t) := by
  intro l; induction l with
  | nil => simp only [List.foldr_nil, List.all_nil]; interval_cases t <;> rfl
  | cons a l ih => simp [Nat.testBit_and, ih]

theorem or_bit (t : ℕ) : ∀ l : List ℕ,
    (l.foldr (· ||| ·) 0).testBit t = l.any (fun a => a.testBit t) := by
  intro l; induction l with
  | nil => simp
  | cons a l ih => simp [Nat.testBit_or, ih]

theorem not_bit : ∀ a < 64, ∀ t < 6, (63 - a).testBit t = !a.testBit t := by decide

theorem and_lt : ∀ l : List ℕ, l.foldr (· &&& ·) 63 < 64 := by
  intro l; induction l with
  | nil => simp
  | cons a l ih => exact lt_of_le_of_lt Nat.and_le_right ih

theorem or_lt : ∀ l : List ℕ, (∀ a ∈ l, a < 64) → l.foldr (· ||| ·) 0 < 64 := by
  intro l; induction l with
  | nil => simp
  | cons a l ih =>
    intro h
    have h1 : a < 2 ^ 6 := by simpa using h a (by simp)
    have h2 : l.foldr (· ||| ·) 0 < 2 ^ 6 := by simpa using ih (fun b hb => h b (by simp [hb]))
    simpa using Nat.or_lt_two_pow h1 h2

theorem getD_lt (M : List ℕ) (hM : ∀ m ∈ M, m < 64) (i : ℕ) : M.getD i 0 < 64 := by
  rcases lt_or_ge i M.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hM _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; omega

theorem getD_mem (M : List ℕ) (h0 : 0 ∈ M) (i : ℕ) : M.getD i 0 ∈ M := by
  rcases lt_or_ge i M.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · rw [List.getD_eq_default _ _ h]; exact h0

def isAON (o : PEqualNP.CircuitLowerBounds.GateOp) : Prop := o = .and ∨ o = .or ∨ o = .not

theorem aev_lt (o : PEqualNP.CircuitLowerBounds.GateOp) (l : List ℕ) (hl : ∀ a ∈ l, a < 64) : aev o l < 64 := by
  cases o with
  | and => exact and_lt l
  | or => exact or_lt l hl
  | not => simp only [aev]; omega
  | mod m => simp [aev]
  | maj => simp [aev]

theorem aev_bit (o : PEqualNP.CircuitLowerBounds.GateOp) (ho : isAON o) (l : List ℕ) (hl : ∀ a ∈ l, a < 64)
    (t : ℕ) (ht : t < 6) : o.eval (l.map fun a => a.testBit t) = (aev o l).testBit t := by
  rcases ho with rfl | rfl | rfl
  · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, aev, and_bit t ht, List.all_map]; rfl
  · simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, aev, or_bit t, List.any_map]; rfl
  · cases l with
    | nil => simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, aev, List.map_nil, List.headD_nil]; interval_cases t <;> rfl
    | cons a l =>
      simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, aev, List.map_cons, List.headD_cons]
      rw [not_bit a (hl a (by simp)) t ht]

def aw (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List ℕ) : List ℕ :=
  gs.foldl (fun M g => M ++ [aev g.op (g.inputs.map fun i => M.getD i 0)]) M

theorem rel (t : ℕ) (ht : t < 6) : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool) (M : List ℕ),
    (∀ g ∈ gs, isAON g.op) → w.length = M.length → (∀ m ∈ M, m < 64) →
    (∀ i, w.getD i false = (M.getD i 0).testBit t) →
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = ((aw gs M).getD i 0).testBit t := by
  intro gs; induction gs with
  | nil => intro w M _ _ _ h i; exact h i
  | cons g gs ih =>
    intro w M hops hlen hM h
    simp only [List.foldl_cons, aw] at ih ⊢
    have hv : (g.inputs.map fun i => w.getD i false) =
        ((g.inputs.map fun i => M.getD i 0).map fun a => a.testBit t) := by
      simp only [List.map_map]; apply List.map_congr_left; intro i _; exact h i
    have hlt : ∀ a ∈ (g.inputs.map fun i => M.getD i 0), a < 64 := by
      intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact getD_lt M hM i
    apply ih
    · intro g' hg'; exact hops g' (by simp [hg'])
    · simp [hlen]
    · intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hM m hm
      · simp only [List.mem_singleton] at hm; subst hm; exact aev_lt _ _ hlt
    · intro i
      rcases lt_trichotomy i M.length with hi | hi | hi
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hi]; exact h i
      · subst hi
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ le_rfl]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        rw [hv]; exact aev_bit _ (hops g (by simp)) _ hlt t ht
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        simp


theorem and31 : ∀ a < 64, a &&& 63 = a := by decide

theorem vform (o : PEqualNP.CircuitLowerBounds.GateOp) (l : List ℕ) (hl2 : l.length ≤ 2) (M : List ℕ)
    (hl : ∀ a ∈ l, a ∈ M) (hM : ∀ m ∈ M, m < 64) (h0 : 0 ∈ M) (h31 : 63 ∈ M) :
    (o = .and ∨ o = .or) → (aev o l ∈ M ∨ ∃ a ∈ M, ∃ b ∈ M, aev o l = a &&& b ∨ aev o l = a ||| b) := by
  intro ho
  match l, hl2 with
  | [], _ => rcases ho with rfl | rfl <;> simp [aev, h0, h31]
  | [a], _ =>
    have ha : a ∈ M := hl a (by simp)
    rcases ho with rfl | rfl
    · left; simp only [aev, List.foldr_cons, List.foldr_nil]; rw [and31 a (hM a ha)]; exact ha
    · left; simpa [aev] using ha
  | [a, b], _ =>
    have ha : a ∈ M := hl a (by simp)
    have hb : b ∈ M := hl b (by simp)
    right; refine ⟨a, ha, b, hb, ?_⟩
    rcases ho with rfl | rfl
    · left; simp only [aev, List.foldr_cons, List.foldr_nil]; rw [and31 b (hM b hb)]
    · right; simp [aev]

theorem vform_not (l : List ℕ) (M : List ℕ) (hl : ∀ a ∈ l, a ∈ M) (h31 : 63 ∈ M) :
    aev .not l ∈ M ∨ ∃ a ∈ M, aev .not l = 63 - a := by
  cases l with
  | nil => left; simpa [aev] using h31
  | cons a l => right; exact ⟨a, hl a (by simp), by simp [aev]⟩

def isNot : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | .not => true
  | _ => false

theorem search : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List ℕ) (S b : ℕ),
    (∀ g ∈ gs, isAON g.op ∧ g.inputs.length ≤ 2) → (∀ m ∈ M, m < 64) → 0 ∈ M → 63 ∈ M →
    (∀ x, S.testBit x = true ↔ x ∈ M) →
    (gs.filter fun g => isNot g.op).length ≤ b →
    12 ∈ aw gs M → 40 ∈ aw gs M → 58 ∈ aw gs M →
    okc gs.length b S = true := by
  intro gs; induction gs with
  | nil =>
    intro M S b _ _ _ _ hS _ h10 h14 h18
    simp only [aw, List.foldl_nil] at h10 h14 h18
    simp [okc, goal, (hS 12).mpr h10, (hS 40).mpr h14, (hS 58).mpr h18]
  | cons g gs ih =>
    intro M S b hops hM h0 h31 hS hb h10 h14 h18
    set l := g.inputs.map fun i => M.getD i 0 with hl_def
    set v := aev g.op l with hv_def
    have hlM : ∀ a ∈ l, a ∈ M := by
      intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact getD_mem M h0 i
    have hlt : ∀ a ∈ l, a < 64 := fun a ha => hM a (hlM a ha)
    have hv32 : v < 64 := aev_lt _ _ hlt
    have hM' : ∀ m ∈ M ++ [v], m < 64 := by
      intro m hm; rcases List.mem_append.mp hm with hm | hm
      · exact hM m hm
      · simp only [List.mem_singleton] at hm; omega
    have hS' : ∀ x, (S ||| 2 ^ v).testBit x = true ↔ x ∈ M ++ [v] := by
      intro x; simp only [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
        List.mem_append, List.mem_singleton, hS x]; constructor <;> rintro (h | h) <;> simp_all
    have hops' : ∀ g' ∈ gs, isAON g'.op ∧ g'.inputs.length ≤ 2 := fun g' hg' => hops g' (by simp [hg'])
    have hg := hops g (by simp)
    have haw : aw (g :: gs) M = aw gs (M ++ [v]) := rfl
    rw [haw] at h10 h14 h18
    have hlen : (g :: gs).length = gs.length + 1 := rfl
    rw [hlen]
    set b' := if isNot g.op = true then b - 1 else b with hb'
    have hb'le : b' ≤ b := by rw [hb']; split_ifs <;> omega
    have hrest : (gs.filter fun g => isNot g.op).length ≤ b' := by
      rw [List.filter_cons] at hb; rw [hb']
      by_cases h1 : isNot g.op = true <;> simp [h1] at hb ⊢ <;> omega
    have IH := ih (M ++ [v]) (S ||| 2 ^ v) b' hops' hM' (by simp [h0]) (by simp [h31]) hS' hrest h10 h14 h18
    by_cases hvM : v ∈ M
    · have hSeq : S ||| 2 ^ v = S := by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.testBit_or, Nat.testBit_two_pow]
        by_cases hi : v = i
        · subst hi; simp [(hS v).mpr hvM]
        · simp [hi]
      rw [hSeq] at IH
      exact okc_fuel _ _ _ (okc_budget _ _ _ _ hb'le IH)
    · have hmiss : miss S ≤ gs.length + 1 := by
        have := okc_miss _ _ _ IH; have := miss_add S v; omega
      have hSv : S.testBit v = false := by
        cases hh : S.testBit v
        · rfl
        · exact absurd ((hS v).mp hh) hvM
      rw [okc]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      right; refine ⟨hmiss, ?_⟩
      rcases hg.1 with hop | hop | hop
      ·
        rcases vform g.op l (by simpa [hl_def] using hg.2) M hlM hM h0 h31 (Or.inl hop) with h | ⟨a, ha, c, hc, h⟩
        · exact absurd h hvM
        · left
          have hb2 : b' = b := by rw [hb', hop]; simp [isNot]
          rw [hb2] at IH
          refine anyB_of _ 64 v hv32 ?_
          have hpm := pmask_hit S a c (mem_elems S a (hM a ha) ((hS a).mpr ha))
            (mem_elems S c (hM c hc) ((hS c).mpr hc))
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          refine ⟨⟨?_, hSv⟩, IH⟩
          rcases h with h | h <;> rw [← hv_def] at h <;> rw [h]
          · exact hpm.1
          · exact hpm.2
      ·
        rcases vform g.op l (by simpa [hl_def] using hg.2) M hlM hM h0 h31 (Or.inr hop) with h | ⟨a, ha, c, hc, h⟩
        · exact absurd h hvM
        · left
          have hb2 : b' = b := by rw [hb', hop]; simp [isNot]
          rw [hb2] at IH
          refine anyB_of _ 64 v hv32 ?_
          have hpm := pmask_hit S a c (mem_elems S a (hM a ha) ((hS a).mpr ha))
            (mem_elems S c (hM c hc) ((hS c).mpr hc))
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          refine ⟨⟨?_, hSv⟩, IH⟩
          rcases h with h | h <;> rw [← hv_def] at h <;> rw [h]
          · exact hpm.1
          · exact hpm.2
      ·
        have hv' : v = aev .not l := by rw [hv_def, hop]
        rcases vform_not l M hlM h31 with h | ⟨a, ha, h⟩
        · rw [← hv'] at h; exact absurd h hvM
        · right
          have hb1 : 0 < b := by
            rw [List.filter_cons] at hb; simp [hop, isNot] at hb; omega
          have hb2 : b' = b - 1 := by rw [hb', hop]; simp [isNot]
          rw [hb2] at IH
          refine ⟨hb1, anyB_of _ 64 v hv32 ?_⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true']
          refine ⟨⟨?_, hSv⟩, IH⟩
          rw [hv', h]
          exact nmask_hit S a (mem_elems S a (hM a ha) ((hS a).mpr ha))


def base : List ℕ := [62, 60, 56, 48, 32, 0, 63]

theorem aw_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (M : List ℕ), (∀ m ∈ M, m < 64) → ∀ m ∈ aw gs M, m < 64 := by
  intro gs; induction gs with
  | nil => intro M h; simpa [aw] using h
  | cons g gs ih =>
    intro M h
    apply ih
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact h m hm
    · simp only [List.mem_singleton] at hm; subst hm
      apply aev_lt
      intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact getD_lt M h i

theorem S0_iff (x : ℕ) : S0.testBit x = true ↔ x ∈ base := by
  rcases lt_or_ge x 64 with h | h
  · interval_cases x <;> decide
  · have h1 : S0 < 2 ^ x :=
      lt_of_lt_of_le (by decide : S0 < 2 ^ 64) (Nat.pow_le_pow_right (by norm_num) h)
    rw [Nat.testBit_lt_two_pow h1]
    simp only [base, List.mem_cons, List.not_mem_nil, or_false, Bool.false_eq_true, false_iff]
    omega

theorem okc_le : ∀ n m b S, n ≤ m → okc n b S = true → okc m b S = true := by
  intro n m b S hnm h
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact h
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hnm) with h1 | h1
    · exact okc_fuel _ _ _ (ih (by omega))
    · rw [← h1]; exact h

theorem eq_of_bits (m k : ℕ) (hm : m < 64) (hk : k < 64) (h : ∀ t : Fin 6, m.testBit t = k.testBit t) :
    m = k := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases lt_or_ge i 6 with hi | hi
  · exact h ⟨i, hi⟩
  · have h32 : (64 : ℕ) ≤ 2 ^ i := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem mem_of_getD (M : List ℕ) (i k : ℕ) (h : M.getD i 0 = k) (hk : k ≠ 0) : k ∈ M := by
  rcases lt_or_ge i M.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi] at h; rw [← h]; exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ hi] at h; omega

end PEqualNP.Outside.L_meta_51042

theorem PEqualNP.Outside.L_meta_51042 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (12 : Nat).testBit t.val ∧
    w.getD q.val false = (40 : Nat).testBit t.val ∧
    w.getD r.val false = (58 : Nat).testBit t.val)) := by
  rintro ⟨D, p, q, r, hf, _, hn, hs, h⟩
  have hops : ∀ g ∈ D.gates, PEqualNP.Outside.L_meta_51042.isAON g.op ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hf g hg
    refine ⟨?_, h2⟩
    simpa [PEqualNP.Outside.L_meta_51042.isAON] using h1
  have hbase : ∀ t : Fin 6, ∀ i, ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]).getD i false
      = (PEqualNP.Outside.L_meta_51042.base.getD i 0).testBit t := by
    intro t i
    rcases lt_or_ge i 7 with hi | hi
    · fin_cases t <;> interval_cases i <;> decide
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [PEqualNP.Outside.L_meta_51042.base]; omega)]
      simp
  have hbl : ∀ m ∈ PEqualNP.Outside.L_meta_51042.base, m < 64 := by decide
  have hw : ∀ t : Fin 6, ∀ i, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD i false
      = ((PEqualNP.Outside.L_meta_51042.aw D.gates PEqualNP.Outside.L_meta_51042.base).getD i 0).testBit t := by
    intro t i
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    exact PEqualNP.Outside.L_meta_51042.rel t t.2 D.gates _ _ (fun g hg => (hops g hg).1) (by simp [PEqualNP.Outside.L_meta_51042.base]) hbl (hbase t) i
  have hMlt := PEqualNP.Outside.L_meta_51042.aw_lt D.gates PEqualNP.Outside.L_meta_51042.base hbl
  have key : ∀ (k i : ℕ), k < 64 → k ≠ 0 →
      (∀ t : Fin 6, (D.wires ((List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true])).getD i false
        = k.testBit t) → k ∈ PEqualNP.Outside.L_meta_51042.aw D.gates PEqualNP.Outside.L_meta_51042.base := by
    intro k i hk hk0 hb
    apply PEqualNP.Outside.L_meta_51042.mem_of_getD _ i k _ hk0
    apply PEqualNP.Outside.L_meta_51042.eq_of_bits _ _ (PEqualNP.Outside.L_meta_51042.getD_lt _ hMlt i) hk
    intro t; rw [← hw t i]; exact hb t
  have h10 := key 12 p.val (by norm_num) (by norm_num) (fun t => (h t).1)
  have h14 := key 40 q.val (by norm_num) (by norm_num) (fun t => (h t).2.1)
  have h18 := key 58 r.val (by norm_num) (by norm_num) (fun t => (h t).2.2)
  have hnot : (D.gates.filter fun g => PEqualNP.Outside.L_meta_51042.isNot g.op).length ≤ 2 := by
    have e : PEqualNP.NotBracket.notCount D = (D.gates.filter fun g => PEqualNP.Outside.L_meta_51042.isNot g.op).length := by
      unfold PEqualNP.NotBracket.notCount
      congr 1
      apply List.filter_congr
      intro g _
      cases hop : g.op <;> rfl
    omega
  have hs' : D.gates.length ≤ 6 := hs
  have hok := PEqualNP.Outside.L_meta_51042.search D.gates PEqualNP.Outside.L_meta_51042.base PEqualNP.Outside.L_meta_51042.S0 2 hops hbl (by decide) (by decide)
    PEqualNP.Outside.L_meta_51042.S0_iff hnot h10 h14 h18
  have := PEqualNP.Outside.L_meta_51042.okc_le _ 6 _ _ hs' hok
  rw [PEqualNP.Outside.L_meta_51042.okc_false] at this
  exact Bool.false_ne_true this
