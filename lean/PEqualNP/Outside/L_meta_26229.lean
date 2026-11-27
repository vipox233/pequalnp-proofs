import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26229_aux.Signed

-- The signed live-wire search and the compilation of a circuit into it are the library of the merged L_meta_8463 (which follows
-- L-meta-1449, Apache-2.0), with the sample widened from 60 to 64 pairs of assignments (words of 128 bits) for six inputs.
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

-- The upper and lower halves represent opposite target labels on 64 pairs of assignments.
abbrev W := BitVec 128
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

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
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
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

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
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

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
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

set_option maxRecDepth 4000 in
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
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
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
def targetFun (x : Fin 3 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)

-- New here: the sample. Bit j < 64 of the words is a point where the function is true, bit 64 + j one where it is false.
def inputs : List W := [0x6a18602800088070ef3ffffbbb387bf9, 0x108400844a81410cf1d6f75df4c7bf6e, 0x00430500b44622039fedffff7fffd7d7]

set_option maxRecDepth 8000 in
theorem sample_rows : ∀ j : Fin 128,
    targetFun (fun i => (inputs.getD i.val 0)[j.val]) = (~~~goal)[j.val] := by
  decide +kernel

-- As in L_meta_8463, for the sample itself in place of its complement.
theorem bound_from_impossible (n : ℕ)
    (impossible : ∀ t, t = goal ∨ t = ~~~goal → build basicOps t n inputs.toFinset → False)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 3 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = targetFun x) :
    n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 3) : Bool := bit k (inputs.getD i.val 0)
    have width : inputs.length = 3 := rfl
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample_rows k
  obtain ⟨t,ht,run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact impossible t ht (lift low run)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem reject : search 3 inputs = false := by
  decide +kernel

theorem no_small (t : W) (ht : t = goal ∨ t = ~~~goal) (run : build basicOps t 3 inputs.toFinset) : False :=
  Bool.noConfusion (reject.symm.trans (search_complete ht 3 inputs (by decide) run))


end PEqualNP.Outside.L_meta_26229_aux.Signed

namespace PEqualNP.Outside.L_meta_26229_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_26229_aux.Signed (legal isBinary binaryCost)

-- Restriction of a circuit to fixed inputs with one- and two-gate elimination (rcStep … rcCircuit_binCost_two_elim): the library of
-- L_meta_14482 by grigorescu, unchanged; only `step` (private in that file's search section) is restated here.
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rcStep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) : List Gate × List (Bool ⊕ ℕ) :=
  let out := st.1
  let env := st.2
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | [] => (out, env ++ [Sum.inl true])
    | i :: _ =>
      match env.getD i (Sum.inl false) with
      | Sum.inl b => (out, env ++ [Sum.inl (!b)])
      | Sum.inr w' => (out ++ [{ op := GateOp.not, inputs := [w'] }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.and =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) then
      (out, env ++ [Sum.inl false])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl true])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.and, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | GateOp.or =>
    if g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) then
      (out, env ++ [Sum.inl true])
    else
      let ws' := g.inputs.filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
      match ws' with
      | [] => (out, env ++ [Sum.inl false])
      | [w'] => (out, env ++ [Sum.inr w'])
      | _ => (out ++ [{ op := GateOp.or, inputs := ws' }], env ++ [Sum.inr (nOut + out.length)])
  | _ => (out, env ++ [Sum.inl false])

def rcCircuit (nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (gs : List Gate) (o : ℕ) : List Gate × ℕ :=
  let res := gs.foldl (rcStep nOut) ([], env0)
  match res.2.getD o (Sum.inl false) with
  | Sum.inr w' => (res.1, w')
  | Sum.inl false => (res.1, nOut + res.1.length)
  | Sum.inl true => (res.1 ++ [{ op := GateOp.not, inputs := [] }], nOut + res.1.length)

lemma list_filterMap_len_le {α β : Type} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih => cases h : f a <;> simp [h] <;> omega

lemma list_filterMap_len_lt {α β : Type} (f : α → Option β) (l : List α)
    (x : α) (hx : x ∈ l) (hnone : f x = none) :
    (l.filterMap f).length < l.length := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hxt
    · simp only [List.filterMap_cons, hnone, List.length_cons]
      have := list_filterMap_len_le f t; omega
    · have hlt := ih hxt
      cases h : f a with
      | none => simp only [List.filterMap_cons, h, List.length_cons]; omega
      | some b => simp only [List.filterMap_cons, h, List.length_cons]; omega

lemma wfold_len (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]; omega

lemma rcStep_env_len (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    (rcStep nOut st g).2.length = st.2.length + 1 := by
  rcases st with ⟨out, env⟩
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]; split_ifs
    · simp
    · cases g.inputs.filterMap _ with
      | nil => simp
      | cons a t => cases t <;> simp
  · simp only [rcStep, h]
    cases g.inputs with
    | nil => simp
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) <;> simp
  · simp [rcStep, h]
  · simp [rcStep, h]

lemma rcStep_legal (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (h1 : ∀ g' ∈ st.1, legal g') (hg : legal g) :
    ∀ g' ∈ (rcStep nOut st g).1, legal g' := by
  rcases st with ⟨out, env⟩
  dsimp only at h1 ⊢
  obtain ⟨hop, hlen⟩ := hg
  change g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not at hop
  rcases hop with hop | hop | hop
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    split_ifs
    · exact h1
    · cases hins : g.inputs.filterMap _ with
      | nil => exact h1
      | cons a t =>
        cases t with
        | nil => exact h1
        | cons b t2 =>
          intro g' hg'
          simp only [List.mem_append, List.mem_singleton] at hg'
          rcases hg' with h | rfl
          · exact h1 g' h
          · have hl := list_filterMap_len_le (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) g.inputs
            rw [hins] at hl
            exact ⟨by simp, hl.trans hlen⟩
  · simp only [rcStep, hop]
    cases g.inputs with
    | nil => exact h1
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => exact h1
      | inr w' =>
        intro g' hg'
        simp only [List.mem_append, List.mem_singleton] at hg'
        rcases hg' with h | rfl
        · exact h1 g' h
        · exact ⟨by simp, by simp⟩

lemma rcFold_legal (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ))
    (h1 : ∀ g' ∈ st.1, legal g') (hM : ∀ g ∈ gs, legal g) :
    ∀ g' ∈ (gs.foldl (rcStep nOut) st).1, legal g' := by
  induction gs generalizing st with
  | nil => exact h1
  | cons g rest ih =>
    simp only [List.foldl_cons]
    exact ih (rcStep nOut st g) (rcStep_legal nOut st g h1 (hM g List.mem_cons_self))
      (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg'))

lemma binaryCost_append_one (gs : List Gate) (g : Gate) :
    binaryCost (gs ++ [g]) = binaryCost gs + (if isBinary g then 1 else 0) := by
  unfold binaryCost
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isBinary g <;> simp

lemma rcStep_binCost_le (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate) :
    binaryCost (rcStep nOut st g).1 ≤ binaryCost st.1 + (if isBinary g then 1 else 0) := by
  rcases st with ⟨out, env⟩
  dsimp only
  cases h : g.op
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, ite_true]
    split_ifs
    · dsimp only; omega
    · cases g.inputs.filterMap _ with
      | nil => dsimp only; omega
      | cons a t =>
        cases t with
        | nil => dsimp only; omega
        | cons b t2 => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp only [rcStep, h, isBinary, Bool.false_eq_true, ite_false, Nat.add_zero]
    cases g.inputs with
    | nil => dsimp only; exact le_refl _
    | cons i _ =>
      dsimp only
      cases env.getD i (Sum.inl false) with
      | inl b => dsimp only; exact le_refl _
      | inr w' => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  · simp [rcStep, h, isBinary]
  · simp [rcStep, h, isBinary]

lemma rcFold_binCost_le (nOut : ℕ) (gs : List Gate) (st : List Gate × List (Bool ⊕ ℕ)) :
    binaryCost (gs.foldl (rcStep nOut) st).1 ≤ binaryCost st.1 + binaryCost gs := by
  induction gs generalizing st with
  | nil => simp [binaryCost]
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have h1 := ih (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    omega

lemma rcFold_eval_inv (nOut : ℕ) (gs : List Gate) (ys : List Bool) (hyl : ys.length = nOut)
    (hM : ∀ g ∈ gs, legal g) (ws : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hlen_ws : ws.length = st.2.length)
    (hinv : ∀ i, match st.2.getD i (Sum.inl false) with
      | Sum.inl b => ws.getD i false = b
      | Sum.inr w' => w' < nOut + st.1.length ∧ ws.getD i false = (st.1.foldl step ys).getD w' false) :
    let ws' := gs.foldl step ws
    let st' := gs.foldl (rcStep nOut) st
    ws'.length = st'.2.length ∧
    ∀ i, match st'.2.getD i (Sum.inl false) with
      | Sum.inl b => ws'.getD i false = b
      | Sum.inr w' => w' < nOut + st'.1.length ∧ ws'.getD i false = (st'.1.foldl step ys).getD w' false := by
  induction gs generalizing ws st with
  | nil => exact ⟨hlen_ws, hinv⟩
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hg := hM g List.mem_cons_self
    rcases st with ⟨out, env⟩
    dsimp only at hlen_ws hinv
    have hws'_len : (step ws g).length = env.length + 1 := by simp [step, hlen_ws]
    have hget_old : ∀ i < env.length, (step ws g).getD i false = ws.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < ws.length)]
    have hget_last : (step ws g).getD env.length false = g.op.eval (g.inputs.map fun i => ws.getD i false) := by
      rw [← hlen_ws, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_hi : ∀ i, env.length + 1 ≤ i → (step ws g).getD i false = false := fun i hi =>
      List.getD_eq_default _ _ (by omega)
    have hstep_inv :
        (step ws g).length = (rcStep nOut (out, env) g).2.length ∧
        ∀ i, match (rcStep nOut (out, env) g).2.getD i (Sum.inl false) with
          | Sum.inl b => (step ws g).getD i false = b
          | Sum.inr w' => w' < nOut + (rcStep nOut (out, env) g).1.length ∧
              (step ws g).getD i false = ((rcStep nOut (out, env) g).1.foldl step ys).getD w' false := by
      constructor
      · rw [rcStep_env_len]; exact hws'_len
      · have hfold_app : ∀ (gnew : Gate),
            ((out ++ [gnew]).foldl step ys) = step (out.foldl step ys) gnew := fun gnew => by
          rw [List.foldl_append]; rfl
        have hkeep_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + out.length ∧ (step ws g).getD i false = (out.foldl step ys).getD w' false := by
          intro x i hi
          have h1 : (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
            simp [List.getElem_append_left hi]
          rw [h1, hget_old i hi]; exact hinv i
        have hkeep_old_app : ∀ (x : Bool ⊕ ℕ) (gnew : Gate) (i : ℕ) (hi : i < env.length),
            match (env ++ [x]).getD i (Sum.inl false) with
            | Sum.inl b => (step ws g).getD i false = b
            | Sum.inr w' => w' < nOut + (out ++ [gnew]).length ∧
                (step ws g).getD i false = ((out ++ [gnew]).foldl step ys).getD w' false := by
          intro x gnew i hi
          have hk := hkeep_old x i hi
          cases hm : (env ++ [x]).getD i (Sum.inl false) with
          | inl b => rw [hm] at hk; exact hk
          | inr w' =>
            rw [hm] at hk; dsimp only at hk
            have hw' : w' < nOut + out.length := hk.1
            refine ⟨by simp; omega, ?_⟩
            rw [hk.2, hfold_app gnew]
            have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
            have hlen_w : (step (out.foldl step ys) gnew).length = nOut + out.length + 1 := by simp [step, hlen_out]
            rw [List.getD_eq_getElem _ _ (by omega : w' < (out.foldl step ys).length),
                List.getD_eq_getElem _ _ (by omega : w' < (step (out.foldl step ys) gnew).length)]
            simp [step, List.getElem_append_left (by omega : w' < (out.foldl step ys).length)]
        have hkeep_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
            (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
          List.getD_eq_default _ _ (by simp; omega)
        have hget_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
          rw [List.getD_eq_getElem _ _ (by simp)]; simp
        have hmem_bound : ∀ w' ∈ g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none),
            w' < nOut + out.length := by
          intro w' hw'
          obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hw'
          have hij := hinv j
          cases hm : env.getD j (Sum.inl false) with
          | inl b => rw [hm] at hj; cases hj
          | inr w0 =>
            rw [hm] at hj hij; dsimp only at hij
            cases hj; exact hij.1
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl false) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl false), hget_last, hop]
                simp only [GateOp.eval, List.all_eq_false, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjf⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjf hj'; dsimp only at hj'
                  cases b with
                  | false => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, by rw [hj']; decide⟩
                  | true => simp at hjf
                | inr w' => rw [hm] at hjf; simp at hjf
              · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
          · have hand_eq : (g.inputs.map fun j => ws.getD j false).all id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).all id := by
              have hnof : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl false := by
                intro j hj heqf
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqf]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl false) →
                  (l.map fun j => ws.getD j false).all id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).all id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnf
                  have ha := hnf a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnf j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | false => exact absurd hm ha
                    | true =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia, Bool.true_and, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.all_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnof
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hand_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl true) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop]; simpa [GateOp.eval] using hand_eq
                · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hand_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hand_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          split_ifs with hany
          · intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq
                rw [hget_env_last (Sum.inl true), hget_last, hop]
                simp only [GateOp.eval, List.any_eq_true, id_eq]
                rw [List.any_eq_true] at hany
                obtain ⟨j, hj, hjt⟩ := hany
                have hj' := hinv j
                cases hm : env.getD j (Sum.inl false) with
                | inl b =>
                  rw [hm] at hjt hj'; dsimp only at hj'
                  cases b with
                  | true => exact ⟨ws.getD j false, List.mem_map.mpr ⟨j, hj, rfl⟩, hj'⟩
                  | false => simp at hjt
                | inr w' => rw [hm] at hjt; simp at hjt
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          · have hor_eq : (g.inputs.map fun j => ws.getD j false).any id =
                ((g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                  fun w' => (out.foldl step ys).getD w' false).any id := by
              have hnot : ∀ j ∈ g.inputs, env.getD j (Sum.inl false) ≠ Sum.inl true := by
                intro j hj heqt
                apply hany; rw [List.any_eq_true]; exact ⟨j, hj, by rw [heqt]⟩
              have hlist : ∀ l : List ℕ, (∀ j ∈ l, env.getD j (Sum.inl false) ≠ Sum.inl true) →
                  (l.map fun j => ws.getD j false).any id =
                  ((l.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).map
                    fun w' => (out.foldl step ys).getD w' false).any id := by
                intro l
                induction l with
                | nil => intro _; rfl
                | cons a t iht =>
                  intro hnt
                  have ha := hnt a List.mem_cons_self
                  have hia := hinv a
                  have ht := iht (fun j hj => hnt j (List.mem_cons_of_mem _ hj))
                  cases hm : env.getD a (Sum.inl false) with
                  | inl b =>
                    cases b with
                    | true => exact absurd hm ha
                    | false =>
                      rw [hm] at hia; dsimp only at hia
                      simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia, Bool.false_or, ht]
                  | inr w' =>
                    rw [hm] at hia; dsimp only at hia
                    simp only [List.filterMap_cons, hm, List.map_cons, List.any_cons, id_eq, hia.2, ht]
              exact hlist g.inputs hnot
            cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil =>
              rw [hins] at hor_eq
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl false) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl false), hget_last, hop]; simpa [GateOp.eval] using hor_eq
                · rw [hkeep_hi (Sum.inl false) i (by omega)]; exact hget_hi i (by omega)
            | cons a t =>
              cases t with
              | nil =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old (Sum.inr a) i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr a)]
                    refine ⟨hmem_bound a (by rw [hins]; simp), ?_⟩
                    rw [hget_last, hop]; simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr a) i (by omega)]; exact hget_hi i (by omega)
              | cons b t2 =>
                rw [hins] at hor_eq
                intro i
                by_cases hi : i < env.length
                · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
                · by_cases heq : i = env.length
                  · subst heq
                    rw [hget_env_last (Sum.inr (nOut + out.length))]
                    refine ⟨by simp, ?_⟩
                    rw [hget_last, hop, hfold_app]
                    have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                    rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                    simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                    simpa [GateOp.eval] using hor_eq
                  · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
        ·
          simp only [rcStep, hop]
          cases hgi : g.inputs with
          | nil =>
            intro i
            by_cases hi : i < env.length
            · exact hkeep_old (Sum.inl true) i hi
            · by_cases heq : i = env.length
              · subst heq; rw [hget_env_last (Sum.inl true), hget_last, hop, hgi]; rfl
              · rw [hkeep_hi (Sum.inl true) i (by omega)]; exact hget_hi i (by omega)
          | cons j rest_i =>
            dsimp only
            cases hm : env.getD j (Sum.inl false) with
            | inl b =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old (Sum.inl (!b)) i hi
              · by_cases heq : i = env.length
                · subst heq; rw [hget_env_last (Sum.inl (!b)), hget_last, hop, hgi]; simpa [GateOp.eval] using hj'
                · rw [hkeep_hi (Sum.inl (!b)) i (by omega)]; exact hget_hi i (by omega)
            | inr w' =>
              dsimp only
              have hj' := hinv j; rw [hm] at hj'; dsimp only at hj'
              intro i
              by_cases hi : i < env.length
              · exact hkeep_old_app (Sum.inr (nOut + out.length)) _ i hi
              · by_cases heq : i = env.length
                · subst heq
                  rw [hget_env_last (Sum.inr (nOut + out.length))]
                  refine ⟨by simp, ?_⟩
                  rw [hget_last, hop, hgi, hfold_app]
                  have hlen_out : (out.foldl step ys).length = nOut + out.length := by rw [wfold_len, hyl]
                  rw [← hlen_out, List.getD_eq_getElem _ _ (by simp [step])]
                  simp only [step, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
                  simpa [GateOp.eval] using hj'.2
                · rw [hkeep_hi (Sum.inr (nOut + out.length)) i (by omega)]; exact hget_hi i (by omega)
    exact ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step ws g) (rcStep nOut (out, env) g)
      hstep_inv.1 hstep_inv.2

lemma rcFold_inr_agree (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (st : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = st.2.length) (hylen : wy.length = st.2.length)
    (heq_cost : binaryCost (gs.foldl (rcStep nOut) st).1 = binaryCost st.1 + binaryCost gs)
    (hagree : ∀ i w', st.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false) :
    ∀ i w', (gs.foldl (rcStep nOut) st).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false := by
  induction gs generalizing wx wy st with
  | nil => exact hagree
  | cons g rest ih =>
    simp only [List.foldl_cons] at heq_cost ⊢
    have hg := hM g List.mem_cons_self
    have h1 := rcFold_binCost_le nOut rest (rcStep nOut st g)
    have h2 := rcStep_binCost_le nOut st g
    have h3 : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hstep_cost : binaryCost (rcStep nOut st g).1 = binaryCost st.1 + (if isBinary g then 1 else 0) := by omega
    have hrest_cost : binaryCost (rest.foldl (rcStep nOut) (rcStep nOut st g)).1 =
        binaryCost (rcStep nOut st g).1 + binaryCost rest := by omega
    rcases st with ⟨out, env⟩
    dsimp only at hxlen hylen hagree hstep_cost
    refine ih (fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')) (step wx g) (step wy g)
      (rcStep nOut (out, env) g) (by rw [rcStep_env_len]; simp [step, hxlen])
      (by rw [rcStep_env_len]; simp [step, hylen]) hrest_cost ?_
    have hget_old_x : ∀ i < env.length, (step wx g).getD i false = wx.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < env.length, (step wy g).getD i false = wy.getD i false := fun i hi => by
      rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : (step wx g).getD env.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : (step wy g).getD env.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hall_inr_of_len2 :
        (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 →
        ∀ j ∈ g.inputs, ∃ w0, env.getD j (Sum.inl false) = Sum.inr w0 := by
      intro hl2 j hj
      cases hm : env.getD j (Sum.inl false) with
      | inr w0 => exact ⟨w0, rfl⟩
      | inl b =>
        exfalso
        have hlt := list_filterMap_len_lt (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none)
          g.inputs j hj (by rw [hm])
        have hcap := hg.2
        omega
    have hstep_env_old : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : i < env.length),
        (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x i hi => by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
      simp [List.getElem_append_left hi]
    have hstep_env_hi : ∀ (x : Bool ⊕ ℕ) (i : ℕ) (hi : env.length + 1 ≤ i),
        (env ++ [x]).getD i (Sum.inl false) = Sum.inl false := fun x i hi =>
      List.getD_eq_default _ _ (by simp; omega)
    have hstep_env_last : ∀ (x : Bool ⊕ ℕ), (env ++ [x]).getD env.length (Sum.inl false) = x := fun x => by
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    intro i w' hiw'
    by_cases hi : i < env.length
    · have h1 : (rcStep nOut (out, env) g).2.getD i (Sum.inl false) = env.getD i (Sum.inl false) := by
        cases h : g.op
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; split_ifs
          · exact hstep_env_old _ i hi
          · cases g.inputs.filterMap _ with | nil => exact hstep_env_old _ i hi | cons a t => cases t <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; cases g.inputs with
          | nil => exact hstep_env_old _ i hi
          | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
        · simp only [rcStep, h]; exact hstep_env_old _ i hi
      rw [h1] at hiw'
      rw [hget_old_x i hi, hget_old_y i hi]
      exact hagree i w' hiw'
    · by_cases heq : i = env.length
      · subst heq
        rw [hget_last_x, hget_last_y]
        have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
        rcases hop with hop | hop | hop
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop, isBinary, ite_true] at hstep_cost
          split_ifs at hstep_cost with hany
          · dsimp only at hstep_cost; omega
          · cases hins : g.inputs.filterMap (fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
            | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
            | cons a t =>
              cases t with
              | nil => rw [hins] at hstep_cost; dsimp only at hstep_cost; omega
              | cons b t2 =>
                have hl2 : (g.inputs.filterMap fun j => match env.getD j (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length ≥ 2 := by
                  rw [hins]; simp
                congr 1; apply List.map_congr_left
                intro j hj
                obtain ⟨w0, hw0⟩ := hall_inr_of_len2 hl2 j hj
                exact hagree j w0 hw0
        · simp only [rcStep, hop] at hiw'
          cases hgi : g.inputs with
          | nil =>
            rw [hgi] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
          | cons j rest_i =>
            rw [hgi] at hiw'; dsimp only at hiw'
            cases hm : env.getD j (Sum.inl false) with
            | inl b => rw [hm] at hiw'; dsimp only at hiw'; rw [hstep_env_last] at hiw'; cases hiw'
            | inr w0 =>
              rw [hop]
              simp only [GateOp.eval, List.map_cons, List.headD_cons, hagree j w0 hm]
      · exfalso
        have hlen_st : (rcStep nOut (out, env) g).2.length = env.length + 1 := rcStep_env_len nOut (out, env) g
        rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'

lemma rcCircuit_props (nIn nOut : ℕ) (env0 : List (Bool ⊕ ℕ)) (hlen0 : env0.length = nIn)
    (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g) :
    let res := rcCircuit nOut env0 gs o
    (∀ g ∈ res.1, legal g) ∧
    binaryCost res.1 ≤ binaryCost gs ∧
    (∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      Circuit.eval ⟨res.1, res.2⟩ ys = Circuit.eval ⟨gs, o⟩ xs) := by
  dsimp only [rcCircuit]
  have hfold_leg := rcFold_legal nOut gs ([], env0) (by intro g h; cases h) hM
  have hfold_bc : binaryCost (gs.foldl (rcStep nOut) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le nOut gs ([], env0); simpa [binaryCost] using this
  have hcore_eval : ∀ (xs ys : List Bool), xs.length = nIn → ys.length = nOut →
      (∀ i < nIn, match env0.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut ∧ xs.getD i false = ys.getD w' false) →
      ∀ i, match (gs.foldl (rcStep nOut) ([], env0)).2.getD i (Sum.inl false) with
        | Sum.inl b => (gs.foldl step xs).getD i false = b
        | Sum.inr w' => w' < nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length ∧
            (gs.foldl step xs).getD i false = ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD w' false := by
    intro xs ys hxl hyl hinit
    have hinit' : ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
        | Sum.inl b => xs.getD i false = b
        | Sum.inr w' => w' < nOut + (([] : List Gate), env0).1.length ∧ xs.getD i false = ((([] : List Gate), env0).1.foldl step ys).getD w' false := by
      intro i
      by_cases hi : i < nIn
      · simpa using hinit i hi
      · dsimp only
        rw [List.getD_eq_default _ _ (by omega)]
        exact List.getD_eq_default _ _ (by omega)
    exact (rcFold_eval_inv nOut gs ys hyl hM xs ([], env0) (by simp [hlen0, hxl]) hinit').2
  cases hm : (gs.foldl (rcStep nOut) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    refine ⟨hfold_leg, hfold_bc, ?_⟩
    intro xs ys hxl hyl hinit
    have h := hcore_eval xs ys hxl hyl hinit o
    rw [hm] at h; exact h.2.symm
  | inl b =>
    cases b with
    | false =>
      refine ⟨hfold_leg, hfold_bc, ?_⟩
      intro xs ys hxl hyl hinit
      have h := hcore_eval xs ys hxl hyl hinit o
      rw [hm] at h
      change ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).getD (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
        (gs.foldl step xs).getD o false
      rw [h, List.getD_eq_default _ _ (by rw [wfold_len, hyl])]
    | true =>
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with h | rfl
        · exact hfold_leg g h
        · exact ⟨by simp, by decide⟩
      · rw [binaryCost_append_one]; simp [isBinary]; exact hfold_bc
      · intro xs ys hxl hyl hinit
        have h := hcore_eval xs ys hxl hyl hinit o
        rw [hm] at h
        change (((gs.foldl (rcStep nOut) ([], env0)).1 ++ [({ op := GateOp.not, inputs := [] } : Gate)]).foldl step ys).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false =
          (gs.foldl step xs).getD o false
        rw [h, List.foldl_append]
        change (step ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys) ({ op := GateOp.not, inputs := [] } : Gate)).getD
            (nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length) false = true
        have hlen : ((gs.foldl (rcStep nOut) ([], env0)).1.foldl step ys).length =
            nOut + (gs.foldl (rcStep nOut) ([], env0)).1.length := by rw [wfold_len, hyl]
        rw [← hlen, List.getD_eq_getElem _ _ (by simp [step])]
        simp [step, GateOp.eval]


lemma rcCircuit_binCost_lt (n k : ℕ) (hk : k < n) (val : Bool) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = n) (hx2l : x2.length = n)
    (hagree_xy : ∀ i < n, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = n) (hz2l : z2.length = n)
    (hz1k : z1.getD k false = val) (hz2k : z2.getD k false = val)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl val else Sum.inr i.val
    binaryCost (rcCircuit n env0 gs o).1 + 1 ≤ binaryCost gs := by
  intro env0
  have hle_fold : binaryCost (gs.foldl (rcStep n) ([], env0)).1 ≤ binaryCost gs := by
    have := rcFold_binCost_le n gs ([], env0); simpa [binaryCost] using this
  have hbc_rc : binaryCost (rcCircuit n env0 gs o).1 = binaryCost (gs.foldl (rcStep n) ([], env0)).1 := by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep n) ([], env0)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  rw [hbc_rc]
  by_contra hlt
  have hzero : binaryCost ([] : List Gate) = 0 := rfl
  have heq_cost : binaryCost (gs.foldl (rcStep n) ([], env0)).1 = binaryCost ([] : List Gate) + binaryCost gs := by
    rw [hzero, Nat.zero_add]; omega
  cases hm : (gs.foldl (rcStep n) ([], env0)).2.getD o (Sum.inl false) with
  | inr w' =>
    have hinit : ∀ i w0, (([] : List Gate), env0).2.getD i (Sum.inl false) = Sum.inr w0 → x1.getD i false = x2.getD i false := by
      intro i w0 hiw
      by_cases hi : i < n
      · dsimp only at hiw
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])] at hiw
        change (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) = Sum.inr w0 at hiw
        rw [List.getElem_ofFn] at hiw
        by_cases hik : i = k
        · simp [hik] at hiw
        · exact hagree_xy i hi hik
      · dsimp only at hiw
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)] at hiw; cases hiw
    have hsame := rcFold_inr_agree n gs hM x1 x2 ([], env0) (by simp [env0, hx1l]) (by simp [env0, hx2l])
      heq_cost hinit o w' hm
    exact hdiff_xy hsame
  | inl b =>
    have hinit_z : ∀ (z : List Bool), z.length = n → z.getD k false = val →
        ∀ i, match (([] : List Gate), env0).2.getD i (Sum.inl false) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < n + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
      intro z hzl hzk i
      by_cases hi : i < n
      · dsimp only
        rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
        change match (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) with
          | Sum.inl b0 => z.getD i false = b0
          | Sum.inr w' => w' < n + 0 ∧ z.getD i false = z.getD w' false
        rw [List.getElem_ofFn]
        by_cases hik : i = k
        · subst hik; simp only [ite_true]; exact hzk
        · simp [hik, hi]
      · dsimp only
        rw [List.getD_eq_default env0 _ (by simp [env0]; omega)]
        exact List.getD_eq_default z false (by omega)
    have hz1 := (rcFold_eval_inv n gs z1 hz1l hM z1 ([], env0) (by simp [env0, hz1l]) (hinit_z z1 hz1l hz1k)).2 o
    have hz2 := (rcFold_eval_inv n gs z2 hz2l hM z2 ([], env0) (by simp [env0, hz2l]) (hinit_z z2 hz2l hz2k)).2 o
    rw [hm] at hz1 hz2
    dsimp only at hz1 hz2
    exact hdiff_zz (hz1.trans hz2.symm)

lemma rcStep_env_old_getD (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (i : ℕ) (hi : i < st.2.length) :
    (rcStep nOut st g).2.getD i (Sum.inl false) = st.2.getD i (Sum.inl false) := by
  rcases st with ⟨out, env⟩
  dsimp only at hi ⊢
  have h1 : ∀ x : Bool ⊕ ℕ, (env ++ [x]).getD i (Sum.inl false) = env.getD i (Sum.inl false) := fun x => by
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
    simp [List.getElem_append_left hi]
  cases h : g.op
  · simp only [rcStep, h]; split_ifs
    · exact h1 _
    · cases g.inputs.filterMap _ with | nil => exact h1 _ | cons a t => cases t <;> exact h1 _
  · simp only [rcStep, h]; split_ifs
    · exact h1 _
    · cases g.inputs.filterMap _ with | nil => exact h1 _ | cons a t => cases t <;> exact h1 _
  · simp only [rcStep, h]; cases g.inputs with
    | nil => exact h1 _
    | cons j _ => dsimp only; cases env.getD j (Sum.inl false) <;> exact h1 _
  · simp only [rcStep, h]; exact h1 _
  · simp only [rcStep, h]; exact h1 _

lemma rcStep_bin_keep (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', st.2.getD j (Sum.inl false) = Sum.inr w') :
    binaryCost (rcStep nOut st g).1 = binaryCost st.1 + 1 ∧
    ∃ w', (rcStep nOut st g).2.getD st.2.length (Sum.inl false) = Sum.inr w' := by
  rcases st with ⟨out, env⟩
  dsimp only at h2 ⊢
  obtain ⟨hl2, hall⟩ := h2
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · simp [hins] at hl2
  · simp [hins] at hl2
  · obtain ⟨wa, hwa⟩ := hall a (by simp [hins])
    obtain ⟨wb, hwb⟩ := hall b (by simp [hins])
    rcases hop with hop | hop
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, hwa, hwb, Bool.or_false, Bool.false_eq_true, ite_false,
        List.filterMap_cons, List.filterMap_nil]
      refine ⟨by rw [binaryCost_append_one]; simp [isBinary], nOut + out.length, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, hwa, hwb, Bool.or_false, Bool.false_eq_true, ite_false,
        List.filterMap_cons, List.filterMap_nil]
      refine ⟨by rw [binaryCost_append_one]; simp [isBinary], nOut + out.length, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp)]; simp
  · simp [hins] at hl2

lemma rcStep_bin_drop (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hcap : g.inputs.length ≤ 2)
    (hnot2 : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', st.2.getD j (Sum.inl false) = Sum.inr w')) :
    binaryCost (rcStep nOut st g).1 = binaryCost st.1 := by
  rcases st with ⟨out, env⟩
  dsimp only at hnot2 ⊢
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
  · rcases hop with hop | hop <;> simp [rcStep, hop, hins]
  · rcases hop with hop | hop
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, Bool.or_false,
        List.filterMap_cons, List.filterMap_nil]
      cases env.getD a (Sum.inl false) with
      | inl bb => cases bb <;> rfl
      | inr wa => rfl
    · simp only [rcStep, hop, hins, List.any_cons, List.any_nil, Bool.or_false,
        List.filterMap_cons, List.filterMap_nil]
      cases env.getD a (Sum.inl false) with
      | inl bb => cases bb <;> rfl
      | inr wa => rfl
  · have hex : ∃ j ∈ ([a, b] : List ℕ), ∀ w', env.getD j (Sum.inl false) ≠ Sum.inr w' := by
      by_contra hno
      apply hnot2
      refine ⟨by simp [hins], ?_⟩
      intro j hj
      rw [hins] at hj
      by_contra hno2
      exact hno ⟨j, hj, fun w' hw' => hno2 ⟨w', hw'⟩⟩
    obtain ⟨j, hj, hnj⟩ := hex
    have hflt : (([a, b] : List ℕ).filterMap fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none).length < 2 := by
      apply list_filterMap_len_lt _ [a, b] j hj
      cases hm : env.getD j (Sum.inl false) with
      | inl _ => rfl
      | inr w' => exact absurd hm (hnj w')
    rcases hop with hop | hop
    · simp only [rcStep, hop, hins]
      split_ifs
      · rfl
      · cases hf : ([a, b] : List ℕ).filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
        | nil => rfl
        | cons u t =>
          cases t with
          | nil => rfl
          | cons v t2 => rw [hf] at hflt; simp at hflt
    · simp only [rcStep, hop, hins]
      split_ifs
      · rfl
      · cases hf : ([a, b] : List ℕ).filterMap (fun i => match env.getD i (Sum.inl false) with | Sum.inr w' => some w' | Sum.inl _ => none) with
        | nil => rfl
        | cons u t =>
          cases t with
          | nil => rfl
          | cons v t2 => rw [hf] at hflt; simp at hflt
  · simp [hins] at hcap

lemma rcStep_bin_inr_no_kill (nOut : ℕ) (st : List Gate × List (Bool ⊕ ℕ)) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w' : ℕ) (hinr : (rcStep nOut st g).2.getD st.2.length (Sum.inl false) = Sum.inr w') :
    ∀ j ∈ g.inputs, ∀ b, st.2.getD j (Sum.inl false) = Sum.inl b →
      (g.op = GateOp.and → b = true) ∧ (g.op = GateOp.or → b = false) := by
  rcases st with ⟨out, env⟩
  dsimp only at hinr ⊢
  intro j hj b hjb
  rcases hop with hop | hop
  · refine ⟨(fun _ => ?_), (fun h => by rw [hop] at h; cases h)⟩
    cases b with
    | true => rfl
    | false =>
      exfalso
      have hany : g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl false => true | _ => false) = true :=
        List.any_eq_true.mpr ⟨j, hj, by rw [hjb]⟩
      simp only [rcStep, hop, hany, ite_true] at hinr
      rw [List.getD_eq_getElem _ _ (by simp)] at hinr
      simp at hinr
  · refine ⟨(fun h => by rw [hop] at h; cases h), (fun _ => ?_)⟩
    cases b with
    | false => rfl
    | true =>
      exfalso
      have hany : g.inputs.any (fun i => match env.getD i (Sum.inl false) with | Sum.inl true => true | _ => false) = true :=
        List.any_eq_true.mpr ⟨j, hj, by rw [hjb]⟩
      simp only [rcStep, hop, hany, ite_true] at hinr
      rw [List.getD_eq_getElem _ _ (by simp)] at hinr
      simp at hinr

lemma rcFold_two_elim_contra (nOut : ℕ) (gs : List Gate) (hM : ∀ g ∈ gs, legal g)
    (wx wy : List Bool) (stF stT : List Gate × List (Bool ⊕ ℕ))
    (hxlen : wx.length = stF.2.length) (hylen : wy.length = stF.2.length)
    (hlenFT : stT.2.length = stF.2.length)
    (hshape : ∀ i, (∃ b, stF.2.getD i (Sum.inl false) = Sum.inl b) ↔
                   (∃ b, stT.2.getD i (Sum.inl false) = Sum.inl b))
    (hagreeF : ∀ i w', stF.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false)
    (hagreeT : ∀ i w', stT.2.getD i (Sum.inl false) = Sum.inr w' → wx.getD i false = wy.getD i false)
    (hsameInl : ∀ i b, stF.2.getD i (Sum.inl false) = Sum.inl b →
                       stT.2.getD i (Sum.inl false) = Sum.inl b →
                       wx.getD i false = b ∧ wy.getD i false = b)
    (hcostF : binaryCost (gs.foldl (rcStep nOut) stF).1 + 1 = binaryCost stF.1 + binaryCost gs)
    (hcostT : binaryCost (gs.foldl (rcStep nOut) stT).1 + 1 = binaryCost stT.1 + binaryCost gs) :
    (∀ i w', (gs.foldl (rcStep nOut) stF).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false) ∨
    (∀ i w', (gs.foldl (rcStep nOut) stT).2.getD i (Sum.inl false) = Sum.inr w' →
      (gs.foldl step wx).getD i false = (gs.foldl step wy).getD i false) := by
  induction gs generalizing wx wy stF stT with
  | nil =>
    simp [binaryCost] at hcostF
  | cons g rest ih =>
    simp only [List.foldl_cons] at hcostF hcostT ⊢
    have hg := hM g List.mem_cons_self
    have hMrest : ∀ g' ∈ rest, legal g' := fun g' hg' => hM g' (List.mem_cons_of_mem _ hg')
    have hbc_cons : binaryCost (g :: rest) = binaryCost rest + (if isBinary g then 1 else 0) := by
      unfold binaryCost; rw [List.filter_cons]; cases isBinary g <;> simp
    have hshape_inr : ∀ i, (∃ w', stF.2.getD i (Sum.inl false) = Sum.inr w') ↔
                           (∃ w', stT.2.getD i (Sum.inl false) = Sum.inr w') := by
      intro i
      cases hF : stF.2.getD i (Sum.inl false) <;> cases hT : stT.2.getD i (Sum.inl false)
      · simp
      · exfalso; obtain ⟨b, hb⟩ := (hshape i).mp ⟨_, hF⟩; rw [hT] at hb; cases hb
      · exfalso; obtain ⟨b, hb⟩ := (hshape i).mpr ⟨_, hT⟩; rw [hF] at hb; cases hb
      · simp
    set stF' := rcStep nOut stF g with hstF'
    set stT' := rcStep nOut stT g with hstT'
    set wx' := step wx g with hwx'
    set wy' := step wy g with hwy'
    have hlenF' : stF'.2.length = stF.2.length + 1 := rcStep_env_len nOut stF g
    have hlenT' : stT'.2.length = stF.2.length + 1 := by rw [rcStep_env_len, hlenFT]
    have hxlen' : wx'.length = stF'.2.length := by rw [hwx', hlenF']; simp [step, hxlen]
    have hylen' : wy'.length = stF'.2.length := by rw [hwy', hlenF']; simp [step, hylen]
    have hget_old_x : ∀ i < stF.2.length, wx'.getD i false = wx.getD i false := fun i hi => by
      rw [hwx', List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wx.length)]
    have hget_old_y : ∀ i < stF.2.length, wy'.getD i false = wy.getD i false := fun i hi => by
      rw [hwy', List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ (by omega)]
      simp [step, List.getElem_append_left (by omega : i < wy.length)]
    have hget_last_x : wx'.getD stF.2.length false = g.op.eval (g.inputs.map fun j => wx.getD j false) := by
      rw [hwx', ← hxlen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hget_last_y : wy'.getD stF.2.length false = g.op.eval (g.inputs.map fun j => wy.getD j false) := by
      rw [hwy', ← hylen, List.getD_eq_getElem _ _ (by simp [step])]; simp [step]
    have hrc_oldF : ∀ i < stF.2.length, stF'.2.getD i (Sum.inl false) = stF.2.getD i (Sum.inl false) :=
      rcStep_env_old_getD nOut stF g
    have hrc_oldT : ∀ i < stF.2.length, stT'.2.getD i (Sum.inl false) = stT.2.getD i (Sum.inl false) := fun i hi =>
      rcStep_env_old_getD nOut stT g i (by omega)
    have hle_restF := rcFold_binCost_le nOut rest stF'
    have hle_restT := rcFold_binCost_le nOut rest stT'
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := hg.1
    rcases hop with hop | hop | hop
    · have hbin : isBinary g = true := by simp [isBinary, hop]
      by_cases h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stF.2.getD j (Sum.inl false) = Sum.inr w'
      · have h2T : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w' :=
          ⟨h2.1, fun j hj => (hshape_inr j).mp (h2.2 j hj)⟩
        obtain ⟨hcF, wF, hwF⟩ := rcStep_bin_keep nOut stF g (Or.inl hop) h2
        obtain ⟨hcT, wT, hwT⟩ := rcStep_bin_keep nOut stT g (Or.inl hop) h2T
        have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
          rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
          intro j hj; obtain ⟨w0, hw0⟩ := h2.2 j hj; exact hagreeF j w0 hw0
        apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
        · intro i
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF, ← hlenFT, hwT]; simp
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i b hF hT
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
            rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF] at hF; cases hF
            · rw [List.getD_eq_default _ _ (by omega)] at hF
              cases hF
              exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
        · simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        · simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
      · have hnot2T : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w') :=
          fun h2T => h2 ⟨h2T.1, fun j hj => (hshape_inr j).mpr (h2T.2 j hj)⟩
        have hcF := rcStep_bin_drop nOut stF g (Or.inl hop) hg.2 h2
        have hcT := rcStep_bin_drop nOut stT g (Or.inl hop) hg.2 hnot2T
        have hrestF : binaryCost (rest.foldl (rcStep nOut) stF').1 = binaryCost stF'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        have hrestT : binaryCost (rest.foldl (rcStep nOut) stT').1 = binaryCost stT'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
        cases hlastF : stF'.2.getD stF.2.length (Sum.inl false) with
        | inl bf =>
          left
          refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
          intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hlastF] at hiw'; cases hiw'
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        | inr wF =>
          cases hlastT : stT'.2.getD stF.2.length (Sum.inl false) with
          | inl bt =>
            right
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stT' (by omega) (by omega) hrestT ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; rw [hlastT] at hiw'; cases hiw'
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
          | inr wT =>
            left
            have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
              rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
              intro j hj
              cases hjF : stF.2.getD j (Sum.inl false) with
              | inr w0 => exact hagreeF j w0 hjF
              | inl bF =>
                obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
                have hbF : bF = true := (rcStep_bin_inr_no_kill nOut stF g (Or.inl hop) wF hlastF j hj bF hjF).1 hop
                have hbT : bT = true := (rcStep_bin_inr_no_kill nOut stT g (Or.inl hop) wT (by rw [hlenFT]; exact hlastT) j hj bT hjT).1 hop
                subst hbF; subst hbT
                have hxy := hsameInl j true hjF hjT
                exact hxy.1.trans hxy.2.symm
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; exact hlast_eq
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
    · have hbin : isBinary g = true := by simp [isBinary, hop]
      by_cases h2 : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stF.2.getD j (Sum.inl false) = Sum.inr w'
      · have h2T : g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w' :=
          ⟨h2.1, fun j hj => (hshape_inr j).mp (h2.2 j hj)⟩
        obtain ⟨hcF, wF, hwF⟩ := rcStep_bin_keep nOut stF g (Or.inr hop) h2
        obtain ⟨hcT, wT, hwT⟩ := rcStep_bin_keep nOut stT g (Or.inr hop) h2T
        have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
          rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
          intro j hj; obtain ⟨w0, hw0⟩ := h2.2 j hj; exact hagreeF j w0 hw0
        apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
        · intro i
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF, ← hlenFT, hwT]; simp
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; exact hlast_eq
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        · intro i b hF hT
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
            rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hwF] at hF; cases hF
            · rw [List.getD_eq_default _ _ (by omega)] at hF
              cases hF
              exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
        · simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        · simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
      · have hnot2T : ¬ (g.inputs.length = 2 ∧ ∀ j ∈ g.inputs, ∃ w', stT.2.getD j (Sum.inl false) = Sum.inr w') :=
          fun h2T => h2 ⟨h2T.1, fun j hj => (hshape_inr j).mpr (h2T.2 j hj)⟩
        have hcF := rcStep_bin_drop nOut stF g (Or.inr hop) hg.2 h2
        have hcT := rcStep_bin_drop nOut stT g (Or.inr hop) hg.2 hnot2T
        have hrestF : binaryCost (rest.foldl (rcStep nOut) stF').1 = binaryCost stF'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostF; rw [← hstF'] at hcF; omega
        have hrestT : binaryCost (rest.foldl (rcStep nOut) stT').1 = binaryCost stT'.1 + binaryCost rest := by
          simp only [hbc_cons, hbin, ite_true] at hcostT; rw [← hstT'] at hcT; omega
        cases hlastF : stF'.2.getD stF.2.length (Sum.inl false) with
        | inl bf =>
          left
          refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
          intro i w' hiw'
          by_cases hi : i < stF.2.length
          · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
          · by_cases heq : i = stF.2.length
            · subst heq; rw [hlastF] at hiw'; cases hiw'
            · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
        | inr wF =>
          cases hlastT : stT'.2.getD stF.2.length (Sum.inl false) with
          | inl bt =>
            right
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stT' (by omega) (by omega) hrestT ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; rw [hlastT] at hiw'; cases hiw'
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
          | inr wT =>
            left
            have hlast_eq : wx'.getD stF.2.length false = wy'.getD stF.2.length false := by
              rw [hget_last_x, hget_last_y]; congr 1; apply List.map_congr_left
              intro j hj
              cases hjF : stF.2.getD j (Sum.inl false) with
              | inr w0 => exact hagreeF j w0 hjF
              | inl bF =>
                obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
                have hbF : bF = false := (rcStep_bin_inr_no_kill nOut stF g (Or.inr hop) wF hlastF j hj bF hjF).2 hop
                have hbT : bT = false := (rcStep_bin_inr_no_kill nOut stT g (Or.inr hop) wT (by rw [hlenFT]; exact hlastT) j hj bT hjT).2 hop
                subst hbF; subst hbT
                have hxy := hsameInl j false hjF hjT
                exact hxy.1.trans hxy.2.symm
            refine rcFold_inr_agree nOut rest hMrest wx' wy' stF' hxlen' hylen' hrestF ?_
            intro i w' hiw'
            by_cases hi : i < stF.2.length
            · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
            · by_cases heq : i = stF.2.length
              · subst heq; exact hlast_eq
              · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
    · have hbin : isBinary g = false := by simp [isBinary, hop]
      have hcF : binaryCost stF'.1 = binaryCost stF.1 := by
        rw [hstF']
        simp only [rcStep, hop]
        cases g.inputs with
        | nil => rfl
        | cons j _ =>
          dsimp only
          cases stF.2.getD j (Sum.inl false) with
          | inl _ => rfl
          | inr _ => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
      have hcT : binaryCost stT'.1 = binaryCost stT.1 := by
        rw [hstT']
        simp only [rcStep, hop]
        cases g.inputs with
        | nil => rfl
        | cons j _ =>
          dsimp only
          cases stT.2.getD j (Sum.inl false) with
          | inl _ => rfl
          | inr _ => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
      have hlast_cases :
          ((∃ b, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl b) ↔
           (∃ b, stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl b)) ∧
          ((∃ w', stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr w') →
            wx'.getD stF.2.length false = wy'.getD stF.2.length false) ∧
          (∀ b, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl b →
                stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl b →
                wx'.getD stF.2.length false = b ∧ wy'.getD stF.2.length false = b) := by
        cases hgi : g.inputs with
        | nil =>
          have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl true := by
            rw [hstF']; simp only [rcStep, hop, hgi]
            rw [List.getD_eq_getElem _ _ (by simp)]; simp
          have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl true := by
            rw [hstT']; simp only [rcStep, hop, hgi]
            rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
          rw [hlF, hlT]
          refine ⟨(by simp), (fun ⟨_, h⟩ => by cases h), (fun b hb _ => ?_)⟩
          cases hb
          rw [hget_last_x, hget_last_y, hop, hgi]
          exact ⟨rfl, rfl⟩
        | cons j _ =>
          cases hjF : stF.2.getD j (Sum.inl false) with
          | inl bF =>
            obtain ⟨bT, hjT⟩ := (hshape j).mp ⟨bF, hjF⟩
            have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inl (!bF) := by
              rw [hstF']; simp only [rcStep, hop, hgi, hjF]
              rw [List.getD_eq_getElem _ _ (by simp)]; simp
            have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inl (!bT) := by
              rw [hstT']; simp only [rcStep, hop, hgi, hjT]
              rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
            rw [hlF, hlT]
            refine ⟨(by simp), (fun ⟨_, h⟩ => by cases h), (fun b hbF hbT => ?_)⟩
            have he1 : (!bF) = b := Sum.inl.inj hbF
            have he2 : (!bT) = b := Sum.inl.inj hbT
            have hbt : bF = bT := by
              have he : (!bF) = (!bT) := he1.trans he2.symm
              cases bF <;> cases bT <;> first | rfl | cases he
            subst hbt
            have hxy := hsameInl j bF hjF hjT
            rw [hget_last_x, hget_last_y, hop, hgi]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, hxy.1, hxy.2, he1, and_self]
          | inr wF =>
            obtain ⟨wT, hjT⟩ := (hshape_inr j).mp ⟨wF, hjF⟩
            have hlF : stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr (nOut + stF.1.length) := by
              rw [hstF']; simp only [rcStep, hop, hgi, hjF]
              rw [List.getD_eq_getElem _ _ (by simp)]; simp
            have hlT : stT'.2.getD stF.2.length (Sum.inl false) = Sum.inr (nOut + stT.1.length) := by
              rw [hstT']; simp only [rcStep, hop, hgi, hjT]
              rw [← hlenFT, List.getD_eq_getElem _ _ (by simp)]; simp
            rw [hlF, hlT]
            refine ⟨(by simp), (fun _ => ?_), (fun _ h _ => by cases h)⟩
            rw [hget_last_x, hget_last_y, hop, hgi]
            simp only [GateOp.eval, List.map_cons, List.headD_cons, hagreeF j wF hjF]
      apply ih hMrest wx' wy' stF' stT' hxlen' hylen' (by omega)
      · intro i
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi, hrc_oldT i hi]; exact hshape i
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.1
          · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      · intro i w' hiw'
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeF i w' hiw'
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.2.1 ⟨w', hiw'⟩
          · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
      · intro i w' hiw'
        by_cases hi : i < stF.2.length
        · rw [hrc_oldT i hi] at hiw'; rw [hget_old_x i hi, hget_old_y i hi]; exact hagreeT i w' hiw'
        · by_cases heq : i = stF.2.length
          · subst heq
            have hF_inr : ∃ w0, stF'.2.getD stF.2.length (Sum.inl false) = Sum.inr w0 := by
              cases hF : stF'.2.getD stF.2.length (Sum.inl false) with
              | inr w0 => exact ⟨w0, rfl⟩
              | inl b0 =>
                exfalso; obtain ⟨b1, hb1⟩ := hlast_cases.1.mp ⟨b0, hF⟩
                rw [hiw'] at hb1; cases hb1
            exact hlast_cases.2.1 hF_inr
          · rw [List.getD_eq_default _ _ (by omega)] at hiw'; cases hiw'
      · intro i b hF hT
        by_cases hi : i < stF.2.length
        · rw [hrc_oldF i hi] at hF; rw [hrc_oldT i hi] at hT
          rw [hget_old_x i hi, hget_old_y i hi]; exact hsameInl i b hF hT
        · by_cases heq : i = stF.2.length
          · subst heq; exact hlast_cases.2.2 b hF hT
          · rw [List.getD_eq_default _ _ (by omega)] at hF
            cases hF
            exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩
      · simp only [hbc_cons, hbin, Bool.false_eq_true, ite_false, Nat.add_zero] at hcostF; omega
      · simp only [hbc_cons, hbin, Bool.false_eq_true, ite_false, Nat.add_zero] at hcostT; omega

lemma rcCircuit_binCost_two_elim (n k : ℕ) (hk : k < n) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x1 x2 : List Bool) (hx1l : x1.length = n) (hx2l : x2.length = n)
    (hagree_xy : ∀ i < n, i ≠ k → x1.getD i false = x2.getD i false)
    (hdiff_xy : Circuit.eval ⟨gs, o⟩ x1 ≠ Circuit.eval ⟨gs, o⟩ x2)
    (z1 z2 : List Bool) (hz1l : z1.length = n) (hz2l : z2.length = n)
    (hz1k : z1.getD k false = false) (hz2k : z2.getD k false = false)
    (hdiff_zz : Circuit.eval ⟨gs, o⟩ z1 ≠ Circuit.eval ⟨gs, o⟩ z2)
    (w1 w2 : List Bool) (hw1l : w1.length = n) (hw2l : w2.length = n)
    (hw1k : w1.getD k false = true) (hw2k : w2.getD k false = true)
    (hdiff_ww : Circuit.eval ⟨gs, o⟩ w1 ≠ Circuit.eval ⟨gs, o⟩ w2) :
    ∃ val : Bool,
      let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl val else Sum.inr i.val
      binaryCost (rcCircuit n env0 gs o).1 + 2 ≤ binaryCost gs := by
  let envF : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl false else Sum.inr i.val
  let envT : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin n => if i.val = k then Sum.inl true else Sum.inr i.val
  have hltF : binaryCost (rcCircuit n envF gs o).1 + 1 ≤ binaryCost gs :=
    rcCircuit_binCost_lt n k hk false gs o hM x1 x2 hx1l hx2l hagree_xy hdiff_xy z1 z2 hz1l hz2l hz1k hz2k hdiff_zz
  have hltT : binaryCost (rcCircuit n envT gs o).1 + 1 ≤ binaryCost gs :=
    rcCircuit_binCost_lt n k hk true gs o hM x1 x2 hx1l hx2l hagree_xy hdiff_xy w1 w2 hw1l hw2l hw1k hw2k hdiff_ww
  by_cases h2F : binaryCost (rcCircuit n envF gs o).1 + 2 ≤ binaryCost gs
  · exact ⟨false, h2F⟩
  by_cases h2T : binaryCost (rcCircuit n envT gs o).1 + 2 ≤ binaryCost gs
  · exact ⟨true, h2T⟩
  exfalso
  have hbc_rc : ∀ env : List (Bool ⊕ ℕ),
      binaryCost (rcCircuit n env gs o).1 = binaryCost (gs.foldl (rcStep n) ([], env)).1 := fun env => by
    dsimp only [rcCircuit]
    cases (gs.foldl (rcStep n) ([], env)).2.getD o (Sum.inl false) with
    | inr w' => rfl
    | inl b => cases b with
      | false => rfl
      | true => dsimp only; rw [binaryCost_append_one]; simp [isBinary]
  have hcostF : binaryCost (gs.foldl (rcStep n) ([], envF)).1 + 1 = binaryCost ([] : List Gate) + binaryCost gs := by
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    rw [← hbc_rc envF, h0, Nat.zero_add]; omega
  have hcostT : binaryCost (gs.foldl (rcStep n) ([], envT)).1 + 1 = binaryCost ([] : List Gate) + binaryCost gs := by
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    rw [← hbc_rc envT, h0, Nat.zero_add]; omega
  have henv_at : ∀ (val : Bool) (i : ℕ),
      (List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val).getD i (Sum.inl false) =
        if i < n then (if i = k then Sum.inl val else Sum.inr i) else Sum.inl false := fun val i => by
    by_cases hi : i < n
    · rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]; simp [hi]
    · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]
  have hcontra := rcFold_two_elim_contra n gs hM x1 x2 ([], envF) ([], envT)
    (by simp [envF, hx1l]) (by simp [envF, hx2l]) (by simp [envF, envT])
    (by intro i; dsimp only; rw [henv_at false i, henv_at true i]; split_ifs <;> simp)
    (by intro i w' hiw'; dsimp only at hiw'; rw [henv_at false i] at hiw'
        by_cases hi : i < n
        · simp only [hi, ite_true] at hiw'
          by_cases hik : i = k
          · simp [hik] at hiw'
          · exact hagree_xy i hi hik
        · simp [hi] at hiw')
    (by intro i w' hiw'; dsimp only at hiw'; rw [henv_at true i] at hiw'
        by_cases hi : i < n
        · simp only [hi, ite_true] at hiw'
          by_cases hik : i = k
          · simp [hik] at hiw'
          · exact hagree_xy i hi hik
        · simp [hi] at hiw')
    (by intro i b hF hT; dsimp only at hF hT; rw [henv_at false i] at hF; rw [henv_at true i] at hT
        by_cases hi : i < n
        · simp only [hi, ite_true] at hF hT
          by_cases hik : i = k
          · simp only [hik, ite_true] at hF hT; cases hF; cases hT
          · simp [hik] at hF
        · simp only [hi, ite_false] at hF; cases hF
          exact ⟨List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)⟩)
    hcostF hcostT
  have hinit_val : ∀ (val : Bool) (z : List Bool), z.length = n → z.getD k false = val →
      ∀ i, match (([] : List Gate), List.ofFn fun j : Fin n => if j.val = k then Sum.inl val else Sum.inr j.val).2.getD i (Sum.inl false) with
        | Sum.inl b0 => z.getD i false = b0
        | Sum.inr w' => w' < n + ([] : List Gate).length ∧ z.getD i false = (([] : List Gate).foldl step z).getD w' false := by
    intro val z hzl hzk i
    dsimp only; rw [henv_at val i]
    by_cases hi : i < n
    · simp only [hi, ite_true]
      by_cases hik : i = k
      · subst hik; simp only [ite_true]; exact hzk
      · simp [hik, hi]
    · simp only [hi, ite_false]
      exact List.getD_eq_default z false (by omega)
  rcases hcontra with hF_ag | hT_ag
  · cases hm : (gs.foldl (rcStep n) ([], envF)).2.getD o (Sum.inl false) with
    | inr w' => exact hdiff_xy (hF_ag o w' hm)
    | inl b =>
      have hz1 := (rcFold_eval_inv n gs z1 hz1l hM z1 ([], envF) (by simp [envF, hz1l]) (hinit_val false z1 hz1l hz1k)).2 o
      have hz2 := (rcFold_eval_inv n gs z2 hz2l hM z2 ([], envF) (by simp [envF, hz2l]) (hinit_val false z2 hz2l hz2k)).2 o
      rw [hm] at hz1 hz2; dsimp only at hz1 hz2
      exact hdiff_zz (hz1.trans hz2.symm)
  · cases hm : (gs.foldl (rcStep n) ([], envT)).2.getD o (Sum.inl false) with
    | inr w' => exact hdiff_xy (hT_ag o w' hm)
    | inl b =>
      have hw1 := (rcFold_eval_inv n gs w1 hw1l hM w1 ([], envT) (by simp [envT, hw1l]) (hinit_val true w1 hw1l hw1k)).2 o
      have hw2 := (rcFold_eval_inv n gs w2 hw2l hM w2 ([], envT) (by simp [envT, hw2l]) (hinit_val true w2 hw2l hw2k)).2 o
      rw [hm] at hw1 hw2; dsimp only at hw1 hw2
      exact hdiff_ww (hw1.trans hw2.symm)

-- New here: the plan. 2 inputs lose two binary gates each for one of their values, 3 inputs set to false lose one each,
-- and the search above is run on the other 3.
def target (x : Fin 8 → Bool) : Bool :=
  decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

lemma fixEnv_eval (k : ℕ) (hk : k < 8) (val : Bool) (gs : List Gate) (o : ℕ) (hM : ∀ g ∈ gs, legal g)
    (x : Fin 8 → Bool) (hxk : x ⟨k, hk⟩ = val) :
    let env0 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = k then Sum.inl val else Sum.inr i.val
    let C' := rcCircuit 8 env0 gs o
    Circuit.eval ⟨C'.1, C'.2⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
  intro env0 C'
  have hprops := rcCircuit_props 8 8 env0 (by simp [env0]) gs o hM
  refine hprops.2.2 (List.ofFn x) (List.ofFn x) (by simp) (by simp) ?_
  intro i hi
  rw [List.getD_eq_getElem env0 _ (by simp [env0, hi])]
  change match (List.ofFn fun j : Fin 8 => if j.val = k then Sum.inl val else Sum.inr j.val)[i]'(by simp [hi]) with
    | Sum.inl b => (List.ofFn x).getD i false = b
    | Sum.inr w' => w' < 8 ∧ (List.ofFn x).getD i false = (List.ofFn x).getD w' false
  rw [List.getElem_ofFn]
  by_cases hik : i = k
  · subst hik; simp only [ite_true]; rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]; exact hxk
  · simp [hik, hi]

def lift (b3 b4 : Bool) (y : Fin 3 → Bool) : Fin 8 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => y 0
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => y 1
  | ⟨6, _⟩ => false
  | ⟨7, _⟩ => y 2

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem target_lift : ∀ (b3 b4 : Bool) (y : Fin 3 → Bool), target (lift b3 b4 y) = Signed.targetFun y := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem binary_bound (gates : List Gate) (o : ℕ) (hleg' : ∀ g ∈ gates, legal g)
    (heval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = target x) : 10 < binaryCost gates := by
  let env1 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 2 then Sum.inl false else Sum.inr i.val
  let C1 := rcCircuit 8 env1 gates o
  have h1_props := rcCircuit_props 8 8 env1 (by simp [env1]) gates o hleg'
  have h1_eval : ∀ x : Fin 8 → Bool, x 2 = false → Circuit.eval ⟨C1.1, C1.2⟩ (List.ofFn x) = target x :=
    fun x hx2 => (fixEnv_eval 2 (by decide) false gates o hleg' x hx2).trans (heval x)
  have h1_lt : binaryCost C1.1 + 1 ≤ binaryCost gates := by
    let fx1 : Fin 8 → Bool := fun i => decide (i.val = 2 ∨ i.val = 5)
    let fx2 : Fin 8 → Bool := fun i => decide (i.val = 5)
    let fz1 : Fin 8 → Bool := fun _ => false
    let fz2 : Fin 8 → Bool := fun i => decide (i.val = 1 ∨ i.val = 5)
    exact rcCircuit_binCost_lt 8 2 (by decide) false gates o hleg'
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by decide)
      (by rw [heval fx1, heval fx2]; decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by decide) (by decide)
      (by rw [heval fz1, heval fz2]; decide)
  have h2_ex : ∃ b3 : Bool,
      let env2 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 3 then Sum.inl b3 else Sum.inr i.val
      binaryCost (rcCircuit 8 env2 C1.1 C1.2).1 + 2 ≤ binaryCost C1.1 := by
    let fx1 : Fin 8 → Bool := fun i => decide (i.val = 3 ∨ i.val = 6)
    let fx2 : Fin 8 → Bool := fun i => decide (i.val = 6)
    let fz1 : Fin 8 → Bool := fun _ => false
    let fz2 : Fin 8 → Bool := fun i => decide (i.val = 1 ∨ i.val = 5)
    let fw1 : Fin 8 → Bool := fun i => decide (i.val = 3)
    let fw2 : Fin 8 → Bool := fun i => decide (i.val = 3 ∨ i.val = 6)
    exact rcCircuit_binCost_two_elim 8 3 (by decide) C1.1 C1.2 h1_props.1
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by decide)
      (by rw [h1_eval fx1 rfl, h1_eval fx2 rfl]; decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by decide) (by decide)
      (by rw [h1_eval fz1 rfl, h1_eval fz2 rfl]; decide)
      (List.ofFn fw1) (List.ofFn fw2) (by simp) (by simp) (by decide) (by decide)
      (by rw [h1_eval fw1 rfl, h1_eval fw2 rfl]; decide)
  obtain ⟨b3, h2_lt⟩ := h2_ex
  let env2 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 3 then Sum.inl b3 else Sum.inr i.val
  let C2 := rcCircuit 8 env2 C1.1 C1.2
  have h2_lt' : binaryCost C2.1 + 2 ≤ binaryCost C1.1 := h2_lt
  have h2_props := rcCircuit_props 8 8 env2 (by simp [env2]) C1.1 C1.2 h1_props.1
  have h2_eval : ∀ x : Fin 8 → Bool, x 2 = false → x 3 = b3 → Circuit.eval ⟨C2.1, C2.2⟩ (List.ofFn x) = target x :=
    fun x hx2 hx3 => (fixEnv_eval 3 (by decide) b3 C1.1 C1.2 h1_props.1 x hx3).trans (h1_eval x hx2)
  have h3_ex : ∃ b4 : Bool,
      let env3 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 4 then Sum.inl b4 else Sum.inr i.val
      binaryCost (rcCircuit 8 env3 C2.1 C2.2).1 + 2 ≤ binaryCost C2.1 := by
    let fx1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else decide (i.val = 0 ∨ i.val = 4)
    let fx2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else decide (i.val = 0)
    let fz1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else false
    let fz2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else decide (i.val = 1 ∨ i.val = 5)
    let fw1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else decide (i.val = 4)
    let fw2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else decide (i.val = 0 ∨ i.val = 4)
    exact rcCircuit_binCost_two_elim 8 4 (by decide) C2.1 C2.2 h2_props.1
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by cases b3 <;> decide)
      (by rw [h2_eval fx1 rfl rfl, h2_eval fx2 rfl rfl]; cases b3 <;> decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by cases b3 <;> decide) (by cases b3 <;> decide)
      (by rw [h2_eval fz1 rfl rfl, h2_eval fz2 rfl rfl]; cases b3 <;> decide)
      (List.ofFn fw1) (List.ofFn fw2) (by simp) (by simp) (by cases b3 <;> decide) (by cases b3 <;> decide)
      (by rw [h2_eval fw1 rfl rfl, h2_eval fw2 rfl rfl]; cases b3 <;> decide)
  obtain ⟨b4, h3_lt⟩ := h3_ex
  let env3 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 4 then Sum.inl b4 else Sum.inr i.val
  let C3 := rcCircuit 8 env3 C2.1 C2.2
  have h3_lt' : binaryCost C3.1 + 2 ≤ binaryCost C2.1 := h3_lt
  have h3_props := rcCircuit_props 8 8 env3 (by simp [env3]) C2.1 C2.2 h2_props.1
  have h3_eval : ∀ x : Fin 8 → Bool, x 2 = false → x 3 = b3 → x 4 = b4 → Circuit.eval ⟨C3.1, C3.2⟩ (List.ofFn x) = target x :=
    fun x hx2 hx3 hx4 => (fixEnv_eval 4 (by decide) b4 C2.1 C2.2 h2_props.1 x hx4).trans (h2_eval x hx2 hx3)
  let env4 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 0 then Sum.inl false else Sum.inr i.val
  let C4 := rcCircuit 8 env4 C3.1 C3.2
  have h4_props := rcCircuit_props 8 8 env4 (by simp [env4]) C3.1 C3.2 h3_props.1
  have h4_eval : ∀ x : Fin 8 → Bool, x 2 = false → x 3 = b3 → x 4 = b4 → x 0 = false → Circuit.eval ⟨C4.1, C4.2⟩ (List.ofFn x) = target x :=
    fun x hx2 hx3 hx4 hx0 => (fixEnv_eval 0 (by decide) false C3.1 C3.2 h3_props.1 x hx0).trans (h3_eval x hx2 hx3 hx4)
  have h4_lt : binaryCost C4.1 + 1 ≤ binaryCost C3.1 := by
    let fx1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else decide (i.val = 0 ∨ i.val = 7)
    let fx2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else decide (i.val = 7)
    let fz1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else false
    let fz2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else decide (i.val = 1 ∨ i.val = 5)
    exact rcCircuit_binCost_lt 8 0 (by decide) false C3.1 C3.2 h3_props.1
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by cases b3 <;> cases b4 <;> decide)
      (by rw [h3_eval fx1 rfl rfl rfl, h3_eval fx2 rfl rfl rfl]; cases b3 <;> cases b4 <;> decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by cases b3 <;> cases b4 <;> decide) (by cases b3 <;> cases b4 <;> decide)
      (by rw [h3_eval fz1 rfl rfl rfl, h3_eval fz2 rfl rfl rfl]; cases b3 <;> cases b4 <;> decide)
  let env5 : List (Bool ⊕ ℕ) := List.ofFn fun i : Fin 8 => if i.val = 6 then Sum.inl false else Sum.inr i.val
  let C5 := rcCircuit 8 env5 C4.1 C4.2
  have h5_props := rcCircuit_props 8 8 env5 (by simp [env5]) C4.1 C4.2 h4_props.1
  have h5_eval : ∀ x : Fin 8 → Bool, x 2 = false → x 3 = b3 → x 4 = b4 → x 0 = false → x 6 = false → Circuit.eval ⟨C5.1, C5.2⟩ (List.ofFn x) = target x :=
    fun x hx2 hx3 hx4 hx0 hx6 => (fixEnv_eval 6 (by decide) false C4.1 C4.2 h4_props.1 x hx6).trans (h4_eval x hx2 hx3 hx4 hx0)
  have h5_lt : binaryCost C5.1 + 1 ≤ binaryCost C4.1 := by
    let fx1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else decide (i.val = 1 ∨ i.val = 6)
    let fx2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else decide (i.val = 1)
    let fz1 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else false
    let fz2 : Fin 8 → Bool := fun i => if i.val = 3 then b3 else if i.val = 4 then b4 else decide (i.val = 1 ∨ i.val = 5)
    exact rcCircuit_binCost_lt 8 6 (by decide) false C4.1 C4.2 h4_props.1
      (List.ofFn fx1) (List.ofFn fx2) (by simp) (by simp)
      (by cases b3 <;> cases b4 <;> decide)
      (by rw [h4_eval fx1 rfl rfl rfl rfl, h4_eval fx2 rfl rfl rfl rfl]; cases b3 <;> cases b4 <;> decide)
      (List.ofFn fz1) (List.ofFn fz2) (by simp) (by simp) (by cases b3 <;> cases b4 <;> decide) (by cases b3 <;> cases b4 <;> decide)
      (by rw [h4_eval fz1 rfl rfl rfl rfl, h4_eval fz2 rfl rfl rfl rfl]; cases b3 <;> cases b4 <;> decide)
  let envP : List (Bool ⊕ ℕ) := [Sum.inl false, Sum.inr 0, Sum.inl false, Sum.inl b3, Sum.inl b4, Sum.inr 1, Sum.inl false, Sum.inr 2]
  let CP := rcCircuit 3 envP C5.1 C5.2
  have hP_props := rcCircuit_props 8 3 envP (by simp [envP]) C5.1 C5.2 h5_props.1
  have hP_eval : ∀ y : Fin 3 → Bool, Circuit.eval ⟨CP.1, CP.2⟩ (List.ofFn y) = Signed.targetFun y := by
    intro y
    rw [hP_props.2.2 (List.ofFn (lift b3 b4 y)) (List.ofFn y) (by simp) (by simp) ?_,
        h5_eval (lift b3 b4 y) rfl rfl rfl rfl rfl, target_lift b3 b4 y]
    intro i hi
    interval_cases i
    · simp [envP, lift]
    · exact ⟨by decide, by simp [lift]⟩
    · simp [envP, lift]
    · simp [envP, lift]
    · simp [envP, lift]
    · exact ⟨by decide, by simp [lift]⟩
    · simp [envP, lift]
    · exact ⟨by decide, by simp [lift]⟩
  have lb := Signed.bound_from_impossible 3 Signed.no_small CP.1 CP.2 hP_props.1 hP_eval
  have hP_le : binaryCost CP.1 ≤ binaryCost C5.1 := hP_props.2.1
  omega

-- The monotone circuit with 12 gates.
def witness : List Gate := [⟨.or, [5, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [7, 12]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [14, 18]⟩]

theorem witness_mono : ∀ g ∈ witness, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem witness_eval : ∀ x : Fin 8 → Bool, Circuit.eval ⟨witness, 19⟩ (List.ofFn x) = target x := by
  decide +kernel

end PEqualNP.Outside.L_meta_26229_aux

theorem PEqualNP.Outside.L_meta_26229 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_26229_aux.Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_26229_aux.Signed.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_26229_aux.Signed.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_26229_aux.binary_bound gates o (fun g hg => fits g hg) computes
    have hl : PEqualNP.Outside.L_meta_26229_aux.witness.length = 12 := rfl
    exact ⟨PEqualNP.Outside.L_meta_26229_aux.witness, 19, PEqualNP.Outside.L_meta_26229_aux.witness_mono, by omega, PEqualNP.Outside.L_meta_26229_aux.witness_eval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
