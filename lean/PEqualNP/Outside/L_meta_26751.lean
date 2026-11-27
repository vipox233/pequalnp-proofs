import PEqualNP.Defs

-- Signed live-wire lower bound adapted from the merged L_meta_9564 (Apache-2.0).
namespace PEqualNP.Outside.L_meta_26751.Signed

-- The signed live-wire search follows L-meta-8463 and L-meta-1449, Apache-2.0.

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
abbrev W := BitVec 246
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 123 := ((x >>> 123) ^^^ x).setWidth 123
def cuts (ws : List W) : BitVec 123 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 123) ++ (0 : BitVec 123)
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

def differs (i : Fin 123) (w : W) : Prop :=
  w.getLsbD (123+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 123) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 123+i.val < 246 := by omega
  have hi' : i.val < 246 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 123) :
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
  change (cuts ws)[j] = (BitVec.allOnes 123)[j]
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

set_option maxRecDepth 100000 in
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
  · change reachable av (BitVec.allOnes 246 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 246)
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

private def bit (k : Fin 246) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 246) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 246) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#246)[k.val] = false; simp
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


def src (i j : Nat) := if j = i then 0 else if j = 123+i then 123 else j
def proj (i : Nat) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 246 => w.getLsbD (src i j.val)))).cast (List.length_ofFn)
theorem src_lt (i j : Nat) (hj : j < 246) : src i j < 246 := by
  unfold src; split <;> first | split <;> omega | omega
set_option maxRecDepth 16000 in
theorem project_bit (i j : Nat) (w : W) (hj : j < 246) :
    (proj i w).getLsbD j = w.getLsbD (src i j) := by
  rw [proj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]; simp only [List.getElem?_ofFn, dif_pos hj, Option.getD_some]
theorem p_and (i : Nat) (a b : W) : proj i (a &&& b) = proj i a &&& proj i b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit i j _ hj, BitVec.getLsbD_and]
theorem p_or (i : Nat) (a b : W) : proj i (a ||| b) = proj i a ||| proj i b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit i j _ hj, BitVec.getLsbD_or]
theorem p_not (i : Nat) (a : W) : proj i (~~~a) = ~~~proj i a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj; simp only [project_bit i j _ hj, BitVec.getLsbD_not, src_lt i j hj, hj, decide_true, Bool.true_and]

def simple (w : W) := w = 0 ∨ w = ~~~0
def clean (i : Fin 123) (A : Finset W) := ∀ u ∈ A, differs i u → simple (proj i u)
theorem reach_proj (i : Fin 123) {a b z : W} {D : Finset W} (ha : holds D (proj i a))
    (hb : holds D (proj i b)) (hz : z ∈ basicOps a b) : reachable D (proj i z) := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> simp only [p_and,p_or,p_not]
  · exact and_reach ha hb
  · exact or_reach ha hb
  · exact and_reach ha (holds_not hb)
  · exact and_reach hb (holds_not ha)
set_option maxRecDepth 100000 in
theorem free_proj (i : Fin 123) {a b z : W} {D : Finset W} (ha : holds D (proj i a))
    (hb : holds D (proj i b)) (hz : z ∈ basicOps a b)
    (hc : simple (proj i a) ∨ simple (proj i b)) : holds D (proj i z) := by
  have h0 : holds D 0 := .inl rfl
  have h1 : holds D (~~~0) := holds_not h0
  have hna := holds_not ha
  have hnb := holds_not hb
  have t_zero_and (x : W) : (0 : W) &&& x = 0 := BitVec.zero_and
  have t_and_zero (x : W) : x &&& (0 : W) = 0 := BitVec.and_zero
  have t_zero_or (x : W) : (0 : W) ||| x = x := BitVec.zero_or
  have t_or_zero (x : W) : x ||| (0 : W) = x := BitVec.or_zero
  have t_allOnes_and (x : W) : (~~~0 : W) &&& x = x := BitVec.allOnes_and
  have t_and_allOnes (x : W) : x &&& (~~~0 : W) = x := BitVec.and_allOnes
  have t_allOnes_or (x : W) : (~~~0 : W) ||| x = ~~~0 := BitVec.allOnes_or
  have t_or_allOnes (x : W) : x ||| (~~~0 : W) = ~~~0 := BitVec.or_allOnes
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl <;> simp only [p_and,p_or,p_not] <;>
    rcases hc with (hc|hc)|(hc|hc) <;> rw [hc] <;>
    simp only [BitVec.not_not, t_zero_and, t_and_zero, t_zero_or, t_or_zero, t_allOnes_and, t_and_allOnes, t_allOnes_or, t_or_allOnes] <;> assumption

set_option maxRecDepth 100000 in
theorem shrink (i : Fin 123) (fixed : proj i goal = goal)
    {t : W} (ht : t = goal ∨ t = ~~~goal) (hd : differs i t) (k : Nat)
    {A D : Finset W} (mapA : ∀ u ∈ A, holds D (proj i u)) (h : build basicOps t k A) :
    ∃ q m, (q = goal ∨ q = ~~~goal) ∧ build basicOps q m D ∧ m ≤ k ∧ (clean i A → m < k) := by
  induction k generalizing A D with
  | zero =>
    have hv := mapA t h
    have ps : proj i t = goal ∨ proj i t = ~~~goal := by
      rcases ht with rfl|rfl
      · exact .inl fixed
      · exact .inr ((p_not ..).trans (congrArg (fun w : W => ~~~w) fixed))
    have nons : ¬ simple (proj i t) := by
      rcases ps with eq|eq <;> rw [eq] <;> unfold simple <;> decide
    rcases hv with c|c|⟨q,hq,rep⟩
    · exact (nons (.inl c)).elim
    · exact (nons (.inr c)).elim
    have hqg : q = goal ∨ q = ~~~goal := by
      rcases rep with r|r <;> rcases ps with e|e <;> rw [r] at e
      · exact .inl e
      · exact .inr e
      · exact .inr (by simpa using congrArg (fun w : W => ~~~w) e)
      · exact .inl (by simpa using congrArg (fun w : W => ~~~w) e)
    exact ⟨q,0,hqg,hq,le_rfl,fun hcl => (nons (hcl t h hd)).elim⟩
  | succ k ih =>
    rcases h with hs|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · obtain ⟨q,m,hq,hr,hl,_⟩ := ih mapA hs
      exact ⟨q,m,hq,hr,by omega,fun _ => by omega⟩
    by_cases old : holds D (proj i z)
    · have extA : ∀ u ∈ insert z A, holds D (proj i u) := by
        intro u hu; rcases Finset.mem_insert.mp hu with rfl|hu
        · exact old
        · exact mapA u hu
      obtain ⟨q,m,hq,hr,hl,_⟩ := ih extA tail
      exact ⟨q,m,hq,hr,by omega,fun _ => by omega⟩
    · rcases reach_proj i (mapA a ha) (mapA b hb) hz with h0|⟨x,hx,y,hy,ne,w,op,rep⟩
      · contradiction
      have extA : ∀ u ∈ insert z A, holds (insert w D) (proj i u) := by
        intro u hu; rcases Finset.mem_insert.mp hu with rfl|hu
        · exact rep
        · exact holds_insert (mapA u hu)
      obtain ⟨q,m,hq,hr,hl,hcl⟩ := ih extA tail
      refine ⟨q,m+1,hq,.inr ⟨x,hx,y,hy,ne,w,op,hr⟩,by omega,?_⟩
      intro orig
      have next : clean i (insert z A) := by
        intro u hu diff
        rcases Finset.mem_insert.mp hu with rfl|hu
        · rcases ops_differs i a b u hz diff with da|db
          · exact (old (free_proj i (mapA a ha) (mapA b hb) hz (.inl (orig a ha da)))).elim
          · exact (old (free_proj i (mapA a ha) (mapA b hb) hz (.inr (orig b hb db)))).elim
        · exact orig u hu diff
      have := hcl next
      omega


def rows : List W :=
  [0x20008211100528000022224a480025ac03ffffff007f00003fffffff000fff, 0x1000000000000000000000000000000, 0x2000000000000000000000000000000, 0x40042722dd7804b20004d7d01780f8fc07ffff078007ffc001ffff07f01f, 0x8100424248108114044004a2428210fdf81ffff803f87fc1fe00fff87063, 0x4000000000000000000000000000000, 0x1902080c85b2c108684181a1018d18437efbe1fe381c7b8fde3c3f3839b38c, 0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10]

def reduced1 : List W := [0x28008211100528000022224a480025ad03ffffff007f00003fffffff000fff, 0x2000000000000000000000000000000, 0x840042722dd7804b20004d7d01780f9fc07ffff078007ffc001ffff07f01f, 0x8100424248108114044004a2428211fdf81ffff803f87fc1fe00fff87063, 0x4000000000000000000000000000000, 0x1102080c85b2c108684181a1018d18427efbe1fe381c7b8fde3c3f3839b38c, 0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10]

theorem clean0 : clean 120 rows.toFinset := by
  intro u hu
  have huL := List.mem_toFinset.mp hu
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at huL
  rcases huL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs simple <;> decide +kernel

theorem map0 : ∀ u ∈ rows.toFinset, holds reduced1.toFinset (proj 120 u) := by
  intro u hu
  have huL := List.mem_toFinset.mp hu
  simp only [rows, List.mem_cons, List.not_mem_nil, or_false] at huL
  rcases huL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr ⟨0x28008211100528000022224a480025ad03ffffff007f00003fffffff000fff, by decide, .inl (by decide +kernel)⟩)
  · exact .inl (by decide +kernel)
  · exact .inr (.inr ⟨0x2000000000000000000000000000000, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x840042722dd7804b20004d7d01780f9fc07ffff078007ffc001ffff07f01f, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x8100424248108114044004a2428211fdf81ffff803f87fc1fe00fff87063, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x4000000000000000000000000000000, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x1102080c85b2c108684181a1018d18427efbe1fe381c7b8fde3c3f3839b38c, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10, by decide, .inl (by decide +kernel)⟩)

def reduced2 : List W := [0x38008211100528000022224a480025af03ffffff007f00003fffffff000fff, 0x1840042722dd7804b20004d7d01780fbfc07ffff078007ffc001ffff07f01f, 0x8100424248108114044004a2428213fdf81ffff803f87fc1fe00fff87063, 0x4000000000000000000000000000000, 0x102080c85b2c108684181a1018d18407efbe1fe381c7b8fde3c3f3839b38c, 0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10]

theorem clean1 : clean 121 reduced1.toFinset := by
  intro u hu
  have huL := List.mem_toFinset.mp hu
  simp only [reduced1, List.mem_cons, List.not_mem_nil, or_false] at huL
  rcases huL with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs simple <;> decide +kernel

theorem map1 : ∀ u ∈ reduced1.toFinset, holds reduced2.toFinset (proj 121 u) := by
  intro u hu
  have huL := List.mem_toFinset.mp hu
  simp only [reduced1, List.mem_cons, List.not_mem_nil, or_false] at huL
  rcases huL with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr ⟨0x38008211100528000022224a480025af03ffffff007f00003fffffff000fff, by decide, .inl (by decide +kernel)⟩)
  · exact .inl (by decide +kernel)
  · exact .inr (.inr ⟨0x1840042722dd7804b20004d7d01780fbfc07ffff078007ffc001ffff07f01f, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x8100424248108114044004a2428213fdf81ffff803f87fc1fe00fff87063, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x4000000000000000000000000000000, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x102080c85b2c108684181a1018d18407efbe1fe381c7b8fde3c3f3839b38c, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10, by decide, .inl (by decide +kernel)⟩)

def r0 : W := 0x38008211100528000022224a480025af03ffffff007f00003fffffff000fff

def r1 : W := 0x3840042722dd7804b20004d7d01780fffc07ffff078007ffc001ffff07f01f

def r2 : W := 0x8100424248108114044004a2428217fdf81ffff803f87fc1fe00fff87063

def r3 : W := 0x102080c85b2c108684181a1018d18407efbe1fe381c7b8fde3c3f3839b38c

def r4 : W := 0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10

def reduced3 : List W := [r0, r1, r2, r3, r4]


theorem clean2 : clean 122 reduced2.toFinset := by
  intro u hu
  have huL := List.mem_toFinset.mp hu
  simp only [reduced2, List.mem_cons, List.not_mem_nil, or_false] at huL
  rcases huL with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold differs simple <;> decide +kernel

theorem map2 : ∀ u ∈ reduced2.toFinset, holds reduced3.toFinset (proj 122 u) := by
  intro u hu
  have huL := List.mem_toFinset.mp hu
  simp only [reduced2, List.mem_cons, List.not_mem_nil, or_false] at huL
  rcases huL with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr ⟨0x38008211100528000022224a480025af03ffffff007f00003fffffff000fff, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x3840042722dd7804b20004d7d01780fffc07ffff078007ffc001ffff07f01f, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x8100424248108114044004a2428217fdf81ffff803f87fc1fe00fff87063, by decide, .inl (by decide +kernel)⟩)
  · exact .inl (by decide +kernel)
  · exact .inr (.inr ⟨0x102080c85b2c108684181a1018d18407efbe1fe381c7b8fde3c3f3839b38c, by decide, .inl (by decide +kernel)⟩)
  · exact .inr (.inr ⟨0x2041088052282124089090005285000fbf7dfe0c7e0f7fe3de1f8c0e7ce10, by decide, .inl (by decide +kernel)⟩)

def body (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W) : Bool :=
  let base := cuts r
  let v := sep w ||| base
  ((v == -1) && next extra (w :: r)) ||
  ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                     ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
  ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

theorem dispatch_eq (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) :
    dispatch extra next a b r = (ops a b).any (body extra next a b r) := rfl

theorem opt_succ (k extra : ℕ) (ws : List W) : optimized (k + 1) extra ws =
    ((ws == [goal] || ws == [~~~goal]) || (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)) := rfl

theorem body_false0 (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W)
    (h1 : ((sep w ||| cuts r == -1) && next 0 (w :: r)) = false) : body 0 next a b r w = false := by
  simp only [body, h1, show ((0 : ℕ) != 0) = false from rfl, show decide ((0 : ℕ) ≥ 2) = false from rfl,
    Bool.false_and, Bool.or_false]

theorem body_false1 (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W)
    (h1 : ((sep w ||| cuts r == -1) && next 1 (w :: r)) = false)
    (h2 : ((sep w ||| cuts r ||| sep a == -1) && next (1 - 1) (w :: a :: r)) = false)
    (h3 : ((sep w ||| cuts r ||| sep b == -1) && next (1 - 1) (w :: b :: r)) = false) : body 1 next a b r w = false := by
  simp only [body, h1, h2, h3, show decide ((1 : ℕ) ≥ 2) = false from rfl, Bool.false_and, Bool.and_false, Bool.or_false]

theorem body_false2 (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W)
    (h1 : ((sep w ||| cuts r == -1) && next (extra + 2) (w :: r)) = false)
    (h2 : ((sep w ||| cuts r ||| sep a == -1) && next (extra + 2 - 1) (w :: a :: r)) = false)
    (h3 : ((sep w ||| cuts r ||| sep b == -1) && next (extra + 2 - 1) (w :: b :: r)) = false)
    (h4 : ((sep w ||| cuts r ||| sep a ||| sep b == -1) && next (extra + 2 - 2) (w :: a :: b :: r)) = false) :
    body (extra + 2) next a b r w = false := by
  simp only [body, Bool.and_assoc, h1, h2, h3, h4, Bool.and_false, Bool.or_false]

theorem pre_only : ∀ ws ∈ reduced3.sublists, (decide (ws.length ≤ 6 + 1) && (cuts ws == -1)) = true → ws = reduced3 := by
  decide +kernel

theorem h0 : ([r0, r1, r2, r3, r4] == [goal] || [r0, r1, r2, r3, r4] == [~~~goal]) = false := by
  decide +kernel

theorem q0 : pairs [r0, r1, r2, r3, r4] = [(r0, r1, [r2, r3, r4]), (r0, r2, [r1, r3, r4]), (r0, r3, [r1, r2, r4]), (r0, r4, [r1, r2, r3]), (r1, r2, [r0, r3, r4]), (r1, r3, [r0, r2, r4]), (r1, r4, [r0, r2, r3]), (r2, r3, [r0, r1, r4]), (r2, r4, [r0, r1, r3]), (r3, r4, [r0, r1, r2])] := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_0_0 : body 2 (optimized 5) r0 r1 [r2, r3, r4] (r0 &&& r1) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_0_1 : body 2 (optimized 5) r0 r1 [r2, r3, r4] (r0 ||| r1) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_0_2 : body 2 (optimized 5) r0 r1 [r2, r3, r4] (r0 &&& ~~~r1) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_0_3 : body 2 (optimized 5) r0 r1 [r2, r3, r4] (r1 &&& ~~~r0) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_1_0 : body 2 (optimized 5) r0 r2 [r1, r3, r4] (r0 &&& r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_1_1 : body 2 (optimized 5) r0 r2 [r1, r3, r4] (r0 ||| r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_1_2 : body 2 (optimized 5) r0 r2 [r1, r3, r4] (r0 &&& ~~~r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_1_3 : body 2 (optimized 5) r0 r2 [r1, r3, r4] (r2 &&& ~~~r0) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_2_0 : body 2 (optimized 5) r0 r3 [r1, r2, r4] (r0 &&& r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_2_1 : body 2 (optimized 5) r0 r3 [r1, r2, r4] (r0 ||| r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_2_2 : body 2 (optimized 5) r0 r3 [r1, r2, r4] (r0 &&& ~~~r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_2_3 : body 2 (optimized 5) r0 r3 [r1, r2, r4] (r3 &&& ~~~r0) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_3_0 : body 2 (optimized 5) r0 r4 [r1, r2, r3] (r0 &&& r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_3_1 : body 2 (optimized 5) r0 r4 [r1, r2, r3] (r0 ||| r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_3_2 : body 2 (optimized 5) r0 r4 [r1, r2, r3] (r0 &&& ~~~r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_3_3 : body 2 (optimized 5) r0 r4 [r1, r2, r3] (r4 &&& ~~~r0) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_4_0 : body 2 (optimized 5) r1 r2 [r0, r3, r4] (r1 &&& r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_4_1 : body 2 (optimized 5) r1 r2 [r0, r3, r4] (r1 ||| r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_4_2 : body 2 (optimized 5) r1 r2 [r0, r3, r4] (r1 &&& ~~~r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_4_3 : body 2 (optimized 5) r1 r2 [r0, r3, r4] (r2 &&& ~~~r1) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_5_0 : body 2 (optimized 5) r1 r3 [r0, r2, r4] (r1 &&& r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_5_1 : body 2 (optimized 5) r1 r3 [r0, r2, r4] (r1 ||| r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_5_2 : body 2 (optimized 5) r1 r3 [r0, r2, r4] (r1 &&& ~~~r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_5_3 : body 2 (optimized 5) r1 r3 [r0, r2, r4] (r3 &&& ~~~r1) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_6_0 : body 2 (optimized 5) r1 r4 [r0, r2, r3] (r1 &&& r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_6_1 : body 2 (optimized 5) r1 r4 [r0, r2, r3] (r1 ||| r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_6_2 : body 2 (optimized 5) r1 r4 [r0, r2, r3] (r1 &&& ~~~r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_6_3 : body 2 (optimized 5) r1 r4 [r0, r2, r3] (r4 &&& ~~~r1) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_7_0 : body 2 (optimized 5) r2 r3 [r0, r1, r4] (r2 &&& r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_7_1 : body 2 (optimized 5) r2 r3 [r0, r1, r4] (r2 ||| r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_7_2 : body 2 (optimized 5) r2 r3 [r0, r1, r4] (r2 &&& ~~~r3) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_7_3 : body 2 (optimized 5) r2 r3 [r0, r1, r4] (r3 &&& ~~~r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_8_0 : body 2 (optimized 5) r2 r4 [r0, r1, r3] (r2 &&& r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_8_1 : body 2 (optimized 5) r2 r4 [r0, r1, r3] (r2 ||| r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_8_2 : body 2 (optimized 5) r2 r4 [r0, r1, r3] (r2 &&& ~~~r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_8_3 : body 2 (optimized 5) r2 r4 [r0, r1, r3] (r4 &&& ~~~r2) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_9_0 : body 2 (optimized 5) r3 r4 [r0, r1, r2] (r3 &&& r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_9_1 : body 2 (optimized 5) r3 r4 [r0, r1, r2] (r3 ||| r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_9_2 : body 2 (optimized 5) r3 r4 [r0, r1, r2] (r3 &&& ~~~r4) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b0_9_3 : body 2 (optimized 5) r3 r4 [r0, r1, r2] (r4 &&& ~~~r3) = false := by
  decide +kernel

theorem c0 : optimized 6 2 [r0, r1, r2, r3, r4] = false := by
  have t : optimized 6 2 [r0, r1, r2, r3, r4] = (([r0, r1, r2, r3, r4] == [goal] || [r0, r1, r2, r3, r4] == [~~~goal]) ||
      (pairs [r0, r1, r2, r3, r4]).any (fun (a, b, r) => dispatch 2 (optimized 5) a b r)) := opt_succ 5 2 [r0, r1, r2, r3, r4]
  rw [t, q0]
  simp only [List.any_cons, List.any_nil, dispatch_eq, ops, h0, b0_0_0, b0_0_1, b0_0_2, b0_0_3, b0_1_0, b0_1_1, b0_1_2, b0_1_3, b0_2_0, b0_2_1, b0_2_2, b0_2_3, b0_3_0, b0_3_1, b0_3_2, b0_3_3, b0_4_0, b0_4_1, b0_4_2, b0_4_3, b0_5_0, b0_5_1, b0_5_2, b0_5_3, b0_6_0, b0_6_1, b0_6_2, b0_6_3, b0_7_0, b0_7_1, b0_7_2, b0_7_3, b0_8_0, b0_8_1, b0_8_2, b0_8_3, b0_9_0, b0_9_1, b0_9_2, b0_9_3, Bool.or_false, Bool.or_self]

theorem smallReject : search 6 reduced3 = false := by
  unfold search
  apply List.any_eq_false.mpr
  intro ws hws hc
  obtain ⟨hp, ho⟩ : (decide (ws.length ≤ 6 + 1) && (cuts ws == -1)) = true ∧
      optimized 6 (6 + 1 - ws.length) ws = true := by
    exact Bool.and_eq_true_iff.mp hc
  have e := pre_only ws hws hp
  subst e
  have ho' : optimized 6 2 [r0, r1, r2, r3, r4] = true := ho
  rw [c0] at ho'
  exact Bool.false_ne_true ho'

theorem noSmall {t : W} (ht : t = goal ∨ t = ~~~goal) (k : Nat) (low : k ≤ 9) (run : build basicOps t k rows.toFinset) : False := by
  have d0 : differs 120 t := by rcases ht with rfl|rfl <;> unfold differs <;> decide
  obtain ⟨t1,k1,ht1,run1,_,h0⟩ := shrink 120 (by decide +kernel) ht d0 k map0 run
  have less0 := h0 clean0
  have d1 : differs 121 t1 := by rcases ht1 with rfl|rfl <;> unfold differs <;> decide
  obtain ⟨t2,k2,ht2,run2,_,h1⟩ := shrink 121 (by decide +kernel) ht1 d1 k1 map1 run1
  have less1 := h1 clean1
  have d2 : differs 122 t2 := by rcases ht2 with rfl|rfl <;> unfold differs <;> decide
  obtain ⟨t3,k3,ht3,run3,_,h2⟩ := shrink 122 (by decide +kernel) ht2 d2 k2 map2 run2
  have less2 := h2 clean2
  have lift {n m : Nat} (h : n ≤ m) (hr : build basicOps t3 n reduced3.toFinset) : build basicOps t3 m reduced3.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (smallReject.symm.trans (search_complete ht3 6 reduced3 (by decide) (lift (by omega) run3)))

def F (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem sample : ∀ k : Fin 246, F (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ rows, holds rows.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 246) :
      (gs.foldl step (rows.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 8) : Bool := bit k (rows.getD i.val 0)
    have same : List.ofFn x = rows.map (bit k) := by
      apply List.ext_getElem
      · simp [rows]
      · intro i hi hj
        have hlt : i < rows.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (rows.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg rows rows.toFinset init evaluate
  exact noSmall ht _ low run

end PEqualNP.Outside.L_meta_26751.Signed

namespace PEqualNP.Outside.L_meta_26751

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem bridge : ∀ x : Fin 8 → Bool, decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = ((x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)) := by
  decide +kernel

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [3, 7]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [9, 0]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [9, 5]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [8, 17]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem weval : ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 18⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_26751

theorem PEqualNP.Outside.L_meta_26751 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fits _ computes
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_26751.Signed.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_26751.Signed.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_26751.Signed.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_26751.Signed.bound gates o (fun g hg => fits g hg) (fun x => (computes x).trans (PEqualNP.Outside.L_meta_26751.bridge x))
    have hl : PEqualNP.Outside.L_meta_26751.wg.length = 11 := rfl
    exact ⟨PEqualNP.Outside.L_meta_26751.wg, 18, PEqualNP.Outside.L_meta_26751.wfits, by omega, PEqualNP.Outside.L_meta_26751.weval⟩
  · refine ⟨gates, o, fun g hg => ⟨?_, (fits g hg).2⟩, le_refl _, computes⟩
    rcases (fits g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
