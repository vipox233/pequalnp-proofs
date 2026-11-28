import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36527_aux

/-! Lower bound by the signed live-wire search of the merged L-meta-9146 and L-meta-8633 (k-sandhu): with NOT
gates free, no circuit with 8 AND/OR gates computes the table, so a circuit with a NOT gate has at least 10
gates; a circuit without NOT gates is already monotone. The monotone witness has 10 gates. -/

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Signed

/-! livewire_kit.lean -- template (tokens 172 54 1230913571279675231 64 6 Nat.testBit (4008372896 * 2 ^ 32 + 3937067168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) 8 399454291830208958289220863505748506502638661009408 5586856414677169394673072211300146742008061035020287 are filled in by tools/livewire.py).
Signed live-wire search, verbatim from the merged L_meta_9146.lean (k-sandhu), whose namespace Signed came from the
merged L_meta_8633.lean (k-sandhu, after L-meta-8463 and L-meta-1449, Apache-2.0). Changes: the wire width, the number
of (false point, true point) pairs, the goal (the full truth table on top of the pair bits), the table F and the
number of binary gates ruled out are parameters. -/

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- Oppositely labeled assignments are paired across the upper and lower halves.
abbrev W := BitVec 172
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 54 := ((x >>> 54) ^^^ x).setWidth 54
def cuts (ws : List W) : BitVec 54 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (1230913571279675231 : BitVec 64) ++ ((-1 : BitVec 54) ++ (0 : BitVec 54))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 54) (w : W) : Prop :=
  w.getLsbD (54+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 54) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 54+i.val < 172 := by omega
  have hi' : i.val < 172 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 54) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 54)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def step1 (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W) : Bool :=
    let base := cuts r
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

-- 25 Nov: a new wire must be fresh (as in k-sandhu's later searches); the live run gives that for free
def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  (ops a b).any fun w => !((a :: b :: r).contains w) && step1 extra next a b r w

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true)
    (missing : z ∉ a :: b :: r) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simpa using missing, ?_⟩
  unfold step1
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have missing : z ∉ a :: b :: r := fun hm => hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hm))
        refine dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl) ?_ missing
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 172 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 172)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 172) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 172) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 172) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#172)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide +kernel : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide +kernel : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372896 * 2 ^ 32 + 3937067168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 172, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 172) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

/-! Nat mirror of the search (method after the BitVec-to-Nat transfer used by k-sandhu): the kernel evaluates plain
Nat bit operations (GMP accelerated) instead of unfolding BitVec. -/

def maskN : Nat := 2 ^ 54 - 1

def sepN (w : Nat) : Nat := (w >>> 54) % 2 ^ 54 ^^^ w % 2 ^ 54

def cutsN (ws : List Nat) : Nat := ws.foldr (fun w acc => sepN w ||| acc) 0

def opsN (a b : Nat) : List Nat :=
  [a &&& b, a ||| b, a &&& (2 ^ 172 - 1 - b), b &&& (2 ^ 172 - 1 - a)]

def dispatchN (extra : Nat) (next : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  let base := cutsN r
  (opsN a b).any fun w =>
    let v := sepN w ||| base
    !((a :: b :: r).contains w) && (((v == maskN) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepN a == maskN) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sepN b == maskN) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepN a ||| sepN b == maskN) && next (extra - 2) (w :: a :: b :: r)))

def goalN : Nat := 399454291830208958289220863505748506502638661009408

def ngoalN : Nat := 5586856414677169394673072211300146742008061035020287

def reachedN (ws : List Nat) : Bool :=
  ws == [goalN] || ws == [ngoalN]

def optimizeN : Nat → Nat → List Nat → Bool
  | 0, _, ws => reachedN ws
  | k + 1, extra, ws => reachedN ws ||
    (pairs ws).any (fun (a, b, r) => dispatchN extra (optimizeN k) a b r)

def searchN (n : Nat) (inputs : List Nat) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsN ws == maskN) && optimizeN n (n + 1 - ws.length) ws

theorem singleMap (f : W → Nat) (xs : List W) :
    singles (xs.map f) = (singles xs).map (fun (a, r) => (f a, r.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [singles, ih, List.map_map, Function.comp_def]

theorem pairMap (f : W → Nat) (xs : List W) :
    pairs (xs.map f) = (pairs xs).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairs, singleMap, ih, List.map_map, Function.comp_def]

theorem maskMap : maskN = (-1 : BitVec 54).toNat := by decide +kernel

theorem sepMap (w : W) : sepN w.toNat = (sep w).toNat := by
  simp [sepN, sep, BitVec.toNat_setWidth, Nat.xor_mod_two_pow]

theorem cutsMap (ws : List W) : cutsN (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change sepN w.toNat ||| cutsN (ws.map BitVec.toNat) = (sep w ||| cuts ws).toNat
    rw [sepMap, ih, BitVec.toNat_or]

theorem opsMap (a b : W) : (ops a b).map BitVec.toNat = opsN a.toNat b.toNat := by
  simp [ops, opsN, BitVec.toNat_not]

theorem equalBits {n : Nat} (a b : BitVec n) : (a.toNat == b.toNat) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.toNat_inj]

theorem containsMap (ws : List W) (w : W) :
    (ws.map BitVec.toNat).contains w.toNat = ws.contains w := by
  apply Bool.eq_iff_iff.mpr
  simp [List.contains_iff_mem, List.mem_map, BitVec.toNat_inj]

theorem goalMap : goal.toNat = goalN := by decide +kernel

theorem ngoalMap : (~~~goal).toNat = ngoalN := by decide +kernel

theorem reachedMap (ws : List W) : reachedN (ws.map BitVec.toNat) = (ws == [goal] || ws == [~~~goal]) := by
  have same (w : W) : (ws.map BitVec.toNat == [w.toNat]) = (ws == [w]) := by
    change (ws.map BitVec.toNat == ([w] : List W).map BitVec.toNat) = _
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact List.map_inj_right (fun _ _ h => BitVec.toNat_inj.mp h)
  simp only [reachedN, ← goalMap, ← ngoalMap, same]

theorem dispatchMap (extra : Nat) (nextN : Nat → List Nat → Bool) (next : Nat → List W → Bool)
    (agree : ∀ e ws, nextN e (ws.map BitVec.toNat) = next e ws) (a b : W) (r : List W) :
    dispatchN extra nextN a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra next a b r := by
  simp only [dispatchN, dispatch, step1, ← opsMap, List.any_map]
  apply List.any_congr rfl
  intro w
  simpa only [Function.comp_apply, sepMap, cutsMap, ← BitVec.toNat_or, maskMap, equalBits,
    ← List.map_cons, containsMap, agree]

theorem optimizeMap (depth extra : Nat) (ws : List W) :
    optimizeN depth extra (ws.map BitVec.toNat) = optimized depth extra ws := by
  induction depth generalizing extra ws with
  | zero => exact reachedMap ws
  | succ n ih =>
    simp only [optimizeN, optimized, reachedMap, pairMap, List.any_map]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a, b, r⟩
    exact dispatchMap extra (optimizeN n) (optimized n) ih a b r

theorem searchMap (n : Nat) (ws : List W) :
    searchN n (ws.map BitVec.toNat) = search n ws := by
  simp only [searchN, search, List.sublists_map, List.any_map]
  apply List.any_congr rfl
  intro a
  simp only [Function.comp_apply, List.length_map, cutsMap, maskMap, equalBits, optimizeMap]

/-! Splitting the kernel check (25 Nov): one decide on the whole search runs out of kernel memory, so the search is
cut into facts `optimizeN k e ws = false`, each checked by its own decide, and a node is checked against the list of
its children facts (nextF) instead of re-running them. -/

def nextF (facts : List (Nat × List Nat)) (e : Nat) (l : List Nat) : Bool := !(facts.contains (e, l))

theorem dispatchN_mono {next next' : Nat → List Nat → Bool} (hm : ∀ e l, next e l = true → next' e l = true)
    (extra a b : Nat) (r : List Nat) (h : dispatchN extra next a b r = true) : dispatchN extra next' a b r = true := by
  unfold dispatchN at h ⊢
  rw [List.any_eq_true] at h ⊢
  obtain ⟨w, hw, hv⟩ := h
  refine ⟨w, hw, ?_⟩
  have h1 := hm extra (w :: r)
  have h2 := hm (extra - 1) (w :: a :: r)
  have h3 := hm (extra - 1) (w :: b :: r)
  have h4 := hm (extra - 2) (w :: a :: b :: r)
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hv ⊢
  tauto

theorem fact_mem {k : Nat} {facts : List (Nat × List Nat)} (hf : ∀ p ∈ facts, optimizeN k p.1 p.2 = false) :
    ∀ e l, optimizeN k e l = true → nextF facts e l = true := by
  intro e l h
  unfold nextF
  cases hc : facts.contains (e, l)
  · rfl
  · have hmem : (e, l) ∈ facts := by simpa using hc
    have h2 := hf _ hmem
    simp only at h2
    rw [h2] at h
    exact absurd h (by decide)

theorem opt_from_facts (k extra : Nat) (ws : List Nat) (facts : List (Nat × List Nat))
    (hf : ∀ p ∈ facts, optimizeN k p.1 p.2 = false)
    (htop : (reachedN ws || (pairs ws).any (fun (a, b, r) => dispatchN extra (nextF facts) a b r)) = false) :
    optimizeN (k + 1) extra ws = false := by
  have hm := fact_mem hf
  cases h : optimizeN (k + 1) extra ws
  · rfl
  · exfalso
    simp only [optimizeN, Bool.or_eq_true, List.any_eq_true] at h
    simp only [Bool.or_eq_false_iff, List.any_eq_false] at htop
    rcases h with h | ⟨⟨a, b, r⟩, hmem, hd⟩
    · rw [htop.1] at h
      exact absurd h (by decide)
    · exact htop.2 _ hmem (dispatchN_mono hm extra a b r hd)

def searchF (n : Nat) (inputs : List Nat) (facts : List (Nat × List Nat)) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsN ws == maskN) && nextF facts (n + 1 - ws.length) ws

theorem search_from_facts (n : Nat) (inputs : List Nat) (facts : List (Nat × List Nat))
    (hf : ∀ p ∈ facts, optimizeN n p.1 p.2 = false) (htop : searchF n inputs facts = false) :
    searchN n inputs = false := by
  have hm := fact_mem hf
  cases h : searchN n inputs
  · rfl
  · exfalso
    simp only [searchN, List.any_eq_true] at h
    simp only [searchF, List.any_eq_false] at htop
    obtain ⟨ws, hws, hv⟩ := h
    apply htop ws hws
    simp only [Bool.and_eq_true] at hv ⊢
    exact ⟨hv.1, hm _ _ hv.2⟩

theorem facts_flat (k : Nat) (cs : List (List (Nat × List Nat)))
    (h : ∀ c ∈ cs, c.all (fun p => !optimizeN k p.1 p.2) = true) :
    ∀ p ∈ cs.flatten, optimizeN k p.1 p.2 = false := by
  intro p hp
  obtain ⟨c, hc, hpc⟩ := List.mem_flatten.mp hp
  have := List.all_eq_true.mp (h c hc) p hpc
  simpa using this

def rows : List W :=
  [0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]

def c0 : List (Nat × List Nat) :=
  [(1, [0x4444444444444444038ee00ee81182acb300b308440, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0x4444444444444444038ee00ee81182acb300b308440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x4444444444444444038ee00ee81182acb300b308440, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xe0e0e0e0e0e0e0e00000e000e0018334d3c9d3cccf5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xe0e0e0e0e0e0e0e00000e000e0018334d3c9d3cccf5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xfefefefefefefefecfbefffefbfffffffffffffffff, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xe0e0e0e0e0e0e0e038e0fce08fe3ccb2c362c3330a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xe0e0e0e0e0e0e0e038e0fce08fe3ccb2c362c3330a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x1010101010101010cc3010301300400000000000000, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xee00ee00ee00ee00000e000e00fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xee00ee00ee00ee00000e000e00fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xffeeffeeffeeffeef3bfefffebffbffffffffffffff, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xee00ee00ee00ee0380efc0e801bc3702ed02f003f, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xee00ee00ee00ee0380efc0e801bc3702ed02f003f, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x1100110011001100f03100310300000000000000000, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xeeee0000eeee00000380000ee80003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xeeee0000eeee00000380000ee80003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xffffeeeeffffeeeeffceeffffcffbffffffffffffff, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xeeee0000eeee000eefc000ffbc00dddb000eef5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xeeee0000eeee000eefc000ffbc00dddb000eef5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x1111000011110000fc4000311400000000000000000, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xeeeeeeee00000000038eefc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xeeeeeeee00000000038eefc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xffffffffeeeeeeeeffffffcee8ffbffffffffffffff, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xeeeeeeee0000000ee8ffbc000000ddfddff, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xeeeeeeee0000000ee8ffbc000000ddfddff, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0x1111111100000000fc7110000000000000000000000, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xa0a0a0a0a0a0a0a0000000000000011040c940c48b5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xfafafafafafafafacc30fff0f3efff77dfffdffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xa0a0a0a0a0a0a0a00000fc000ee3c430c360c3330a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x5050505050505050cc30f030f301c22493009308440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xaa00aa00aa00aa000000000000ee01404c124c07b80, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xffaaffaaffaaffaaf03f0fff03fe3fdbfdfffdfffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xaa00aa00aa00aa00000fc000003c1300ed00f003f, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x5500550055005500f03f003f03100288b100b108440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xaaaa0000aaaa0000000000000000015300244cf110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xffffaaaaffffaaaaffc00ffffcee3fff6efffff7bbf, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xaaaa0000aaaa00000fc000ee3c004cdb0006ab5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0x5555000055550000ffc0003ffc0002ac2200b300000, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xaaaaaaaa0000000000000fc0000001534cff0002200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xffffffffaaaaaaaaffffffc000ee3fffffff6ef7bbf, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xaaaaaaaa0000000000ee3c0000004cf59bf, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0x5555555500000000fffff000000002acb3002200000, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xf000f000f000f000c030003003000300d100d10ccc0, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xfff0fff0fff0fff0fc3ff03ff3ffc3fcffdbffcfff5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h0 : c0.all (fun p => !optimizeN 6 p.1 p.2) = true := by decide +kernel

def c1 : List (Nat × List Nat) :=
  [(0, [0xf000f000f000f00c00f000f001c03402c902c0035, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xf000f000f000f00300f000f00fe00c82c122c03300, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xf0f00000f0f00000cc000030f00003340200d3c0000, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xfffff0f0fffff0f0fff0f03fff01c3fff3edfffddff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xf0f00000f0f00030f0000301c000d1c9000ccf5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xf0f00000f0f000033c0000f0c0000cb20242c3110a, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xf0f0f0f000000000cc30f00000000334d3c90200000, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xfffffffff0f0f0f0fffffff0f301c3fffffff3ceef5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xf0f0f0f000000030f301c0000000d1cccf5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xf0f0f0f0000000033cf0fc0000000cb2c362002200, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xff000000ff000000f000003f000003c82000fd01100, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xffffff00ffffff00ffff003ffffe03ffff36fffffca, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xff000000ff00003f000003fe0000dd12000eec0, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xff000000ff00000fc00000fc000037022402f000a, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200]), (0, [0xff00ff0000000000f03f0000000003c8fd122002200, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xffffffffff00ff00ffffffff03fe03ffffffff0ffc0, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xff00ff000000003f03fe00000000dd0ddc0, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xff00ff000000000fc0ffc00000003702ed0200000, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (0, [0xffff000000000000ffc00000000003ff22242200000, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0]), (0, [0xffffffffffff0000fffffffffc0003fffffffff330a, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0]), (0, [0xffff00000000003ffc0000000000ddf110a, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0]), (0, [0xffff00000000003fffc000000000dddb0002200, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h1 : c1.all (fun p => !optimizeN 6 p.1 p.2) = true := by decide +kernel

def c2 : List (Nat × List Nat) :=
  [(2, [0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h2 : c2.all (fun p => !optimizeN 7 p.1 p.2) = true := by
  have h : optimizeN 7 2 [0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200] = false :=
    opt_from_facts 6 2 _ ([c0, c1]).flatten (facts_flat 6 [c0, c1] (List.forall_mem_cons.mpr ⟨h0, (List.forall_mem_cons.mpr ⟨h1, (fun _ hx => by simp at hx)⟩)⟩)) (by decide +kernel)
  simp only [c2, List.all_cons, List.all_nil, h, Bool.not_false, Bool.and_true]

def c3 : List (Nat × List Nat) :=
  [(1, [0x888888888888888800000e0000e0300208b808a382c, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h3 : c3.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c4 : List (Nat × List Nat) :=
  [(1, [0xeeeeeeeeeeeeeeee038eefcee8ffbffffffffffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h4 : c4.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c5 : List (Nat × List Nat) :=
  [(1, [0x2222222222222222000001c0000e0d5144474454393, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (2, [0x4444444444444444038ee00ee81182acb300b308440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h5 : c5.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c6 : List (Nat × List Nat) :=
  [(1, [0x4444444444444444038ee00ee81182acb300b308440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xa0a0a0a0a0a0a0a0000000000000011040c940c48b5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h6 : c6.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c7 : List (Nat × List Nat) :=
  [(1, [0xfafafafafafafafacc30fff0f3efff77dfffdffffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xa0a0a0a0a0a0a0a00000fc000ee3c430c360c3330a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0x5050505050505050cc30f030f301c22493009308440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h7 : c7.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c8 : List (Nat × List Nat) :=
  [(1, [0xaa00aa00aa00aa000000000000ee01404c124c07b80, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xffaaffaaffaaffaaf03f0fff03fe3fdbfdfffdfffff, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xaa00aa00aa00aa00000fc000003c1300ed00f003f, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h8 : c8.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c9 : List (Nat × List Nat) :=
  [(1, [0x5500550055005500f03f003f03100288b100b108440, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xaaaa0000aaaa0000000000000000015300244cf110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h9 : c9.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c10 : List (Nat × List Nat) :=
  [(1, [0xffffaaaaffffaaaaffc00ffffcee3fff6efffff7bbf, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xaaaa0000aaaa00000fc000ee3c004cdb0006ab5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0x5555000055550000ffc0003ffc0002ac2200b300000, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h10 : c10.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c11 : List (Nat × List Nat) :=
  [(1, [0xaaaaaaaa0000000000000fc0000001534cff0002200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xffffffffaaaaaaaaffffffc000ee3fffffff6ef7bbf, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h11 : c11.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c12 : List (Nat × List Nat) :=
  [(1, [0xaaaaaaaa0000000000ee3c0000004cf59bf, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0x5555555500000000fffff000000002acb3002200000, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xc0c0c0c0c0c0c0c00000e000e001822493889388c64, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h12 : c12.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c13 : List (Nat × List Nat) :=
  [(1, [0xfcfcfcfcfcfcfcfccfbefe3efbf1f3befbf9fbefcfd, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xc0c0c0c0c0c0c0c038e0e0e08f0308a28302823008, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0x3030303030303030cc3010301300411040414044091, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h13 : c13.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c14 : List (Nat × List Nat) :=
  [(1, [0xcc00cc00cc00cc00000e000e00f00288b910b90bc40, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xffccffccffccffccf3bfee3febffb3eeffbaffaffec, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xcc00cc00cc00cc0380ee00e801b02602a802a002c, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h14 : c14.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c15 : List (Nat × List Nat) :=
  [(1, [0x3300330033003300f0310031030e014044024404380, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xcccc0000cccc00000380000ee80002ae2220bba1008, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xffffccccffffccccffceee3ffcf1b3ffbbbcfffbd6e, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xcccc0000cccc000eee0000f1b0009998000ac64, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h15 : c15.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c16 : List (Nat × List Nat) :=
  [(1, [0x3333000033330000fc4000311400015100044450102, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xcccccccc00000000038eee00000002aebbb82202000, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h16 : c16.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c17 : List (Nat × List Nat) :=
  [(1, [0xffffffffccccccccffffffcee8f1b3ffffffbbabe6c, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xcccccccc0000000ee8f1b000000099a9c6c, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0x3333333300000000fc7111c00000015144470000200, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h17 : c17.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c18 : List (Nat × List Nat) :=
  [(1, [0xf000f000f000f000c030003003000300d100d10ccc0, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xfff0fff0fff0fff0fc3ff03ff3ffc3fcffdbffcfff5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h18 : c18.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c19 : List (Nat × List Nat) :=
  [(1, [0xf000f000f000f00c00f000f001c03402c902c0035, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xf000f000f000f00300f000f00fe00c82c122c03300, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xf0f00000f0f00000cc000030f00003340200d3c0000, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h19 : c19.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c20 : List (Nat × List Nat) :=
  [(1, [0xfffff0f0fffff0f0fff0f03fff01c3fff3edfffddff, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xf0f00000f0f00030f0000301c000d1c9000ccf5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xf0f00000f0f000033c0000f0c0000cb20242c3110a, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h20 : c20.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c21 : List (Nat × List Nat) :=
  [(1, [0xf0f0f0f000000000cc30f00000000334d3c90200000, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xfffffffff0f0f0f0fffffff0f301c3fffffff3ceef5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h21 : c21.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c22 : List (Nat × List Nat) :=
  [(1, [0xf0f0f0f000000030f301c0000000d1cccf5, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xf0f0f0f0000000033cf0fc0000000cb2c362002200, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xff000000ff000000f000003f000003c82000fd01100, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h22 : c22.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c23 : List (Nat × List Nat) :=
  [(1, [0xffffff00ffffff00ffff003ffffe03ffff36fffffca, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xff000000ff00003f000003fe0000dd12000eec0, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200]), (1, [0xff000000ff00000fc00000fc000037022402f000a, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h23 : c23.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c24 : List (Nat × List Nat) :=
  [(1, [0xff00ff0000000000f03f0000000003c8fd122002200, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xffffffffff00ff00ffffffff03fe03ffffffff0ffc0, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h24 : c24.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c25 : List (Nat × List Nat) :=
  [(1, [0xff00ff000000003f03fe00000000dd0ddc0, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xff00ff000000000fc0ffc00000003702ed0200000, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a]), (1, [0xffff000000000000ffc00000000003ff22242200000, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h25 : c25.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c26 : List (Nat × List Nat) :=
  [(1, [0xffffffffffff0000fffffffffc0003fffffffff330a, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0]), (1, [0xffff00000000003ffc0000000000ddf110a, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0]), (1, [0xffff00000000003fffc000000000dddb0002200, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200, 0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h26 : c26.all (fun p => !optimizeN 7 p.1 p.2) = true := by decide +kernel

def c27 : List (Nat × List Nat) :=
  [(3, [0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem h27 : c27.all (fun p => !optimizeN 8 p.1 p.2) = true := by
  have h : optimizeN 8 3 [0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200] = false :=
    opt_from_facts 7 3 _ ([c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26]).flatten (facts_flat 7 [c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26] (List.forall_mem_cons.mpr ⟨h2, (List.forall_mem_cons.mpr ⟨h3, (List.forall_mem_cons.mpr ⟨h4, (List.forall_mem_cons.mpr ⟨h5, (List.forall_mem_cons.mpr ⟨h6, (List.forall_mem_cons.mpr ⟨h7, (List.forall_mem_cons.mpr ⟨h8, (List.forall_mem_cons.mpr ⟨h9, (List.forall_mem_cons.mpr ⟨h10, (List.forall_mem_cons.mpr ⟨h11, (List.forall_mem_cons.mpr ⟨h12, (List.forall_mem_cons.mpr ⟨h13, (List.forall_mem_cons.mpr ⟨h14, (List.forall_mem_cons.mpr ⟨h15, (List.forall_mem_cons.mpr ⟨h16, (List.forall_mem_cons.mpr ⟨h17, (List.forall_mem_cons.mpr ⟨h18, (List.forall_mem_cons.mpr ⟨h19, (List.forall_mem_cons.mpr ⟨h20, (List.forall_mem_cons.mpr ⟨h21, (List.forall_mem_cons.mpr ⟨h22, (List.forall_mem_cons.mpr ⟨h23, (List.forall_mem_cons.mpr ⟨h24, (List.forall_mem_cons.mpr ⟨h25, (List.forall_mem_cons.mpr ⟨h26, (fun _ hx => by simp at hx)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)) (by decide +kernel)
  simp only [c27, List.all_cons, List.all_nil, h, Bool.not_false, Bool.and_true]

def rowsN : List Nat := [0xaaaaaaaaaaaaaaaa00000fc000ee3d534cff4cf7bbf, 0xcccccccccccccccc038eee0ee8f1b2aebbb8bbabc6c, 0xf0f0f0f0f0f0f0f0cc30f030f301c334d3c9d3cccf5, 0xff00ff00ff00ff00f03f003f03fe03c8fd12fd0ffc0, 0xffff0000ffff0000ffc0003ffc0003ff2224fff110a, 0xffffffff00000000ffffffc0000003ffffff2202200]

theorem rowsMap : rows.map BitVec.toNat = rowsN := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem rootN : searchN 8 rowsN = false :=
  search_from_facts 8 rowsN ([c27]).flatten (facts_flat 8 [c27] (List.forall_mem_cons.mpr ⟨h27, (fun _ hx => by simp at hx)⟩)) (by decide +kernel)

theorem reject : search 8 rows = false := by
  rw [← searchMap, rowsMap]
  exact rootN

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 8 < binaryCost gs :=
  bound_from_search rows rfl (by decide +kernel) reject (by decide +kernel) gs o hg he

end Signed

def witness : Circuit := ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.and, [8, 5]⟩, ⟨GateOp.and, [3, 9]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.and, [1, 12]⟩, ⟨GateOp.or, [0, 13]⟩, ⟨GateOp.and, [14, 11]⟩], 15⟩

theorem computes : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = Signed.F x := by decide +kernel

end PEqualNP.Outside.L_meta_36527_aux

open PEqualNP.Outside.L_meta_36527_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_36527 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372896 * 2 ^ 32 + 3937067168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372896 * 2 ^ 32 + 3937067168) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hleg, small, correct⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, hg, op⟩ := hasNot
    have binary : Signed.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr
        ⟨g, hg, by simp [Signed.isBinary, op]⟩
    have low := Signed.bound C.gates C.output
      (fun g h => ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hleg g h).1,
        (hleg g h).2⟩) correct
    change C.gates.length ≤ s at small
    refine ⟨witness, by simp [Monotone2, witness], ?_, computes⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, small, correct⟩
    intro g hg
    refine ⟨?_, (hleg g hg).2⟩
    obtain (hop | hop | hop) : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hleg g hg).1
    · exact Or.inl hop
    · exact Or.inr hop
    · exact (hasNot ⟨g, hg, hop⟩).elim
