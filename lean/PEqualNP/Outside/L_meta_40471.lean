import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40471

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

abbrev W := BitVec 128

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

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276809450 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 128,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
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
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x3c384429800488a0#64 ++ 0xbd93352d8106bcb0#64 : BitVec 128),
   (0x382c5e7834d8a960#64 ++ 0x726cdefa7ef9eb60#64 : BitVec 128),
   (0xca73840a0b4347fe#64 ++ 0x8a73cc4a8fcbc7ff#64 : BitVec 128),
   (0x45c9c2a0da2a9e17#64 ++ 0x4d8dc2b8fa3a9edf#64 : BitVec 128),
   (0x4307381667a1301b#64 ++ 0x63023c3777a1311f#64 : BitVec 128),
   (0x82c4a9c26990740d#64 ++ 0x94fc23c269d47c2f#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [6, 4]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [10, 1]⟩, ⟨.or, [11, 9]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [14, 12]⟩], 15⟩

section Fast

def full64 : ℕ := 0xFFFFFFFFFFFFFFFF
def sepF (x : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight x 64) x) full64
def cutsF (ws : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ v => Nat.lor (sepF w) v) ws
def goalF : ℕ := Nat.shiftLeft full64 64
def isGoalF (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w rest _ => List.isEmpty rest && (Nat.beq w goalF || Nat.beq w full64)) ws

def anyOneF (f : ℕ → List ℕ → Bool) (ws : List ℕ) : (List ℕ → List ℕ) → Bool :=
  List.rec (motive := fun _ => (List ℕ → List ℕ) → Bool) (fun _ => false)
    (fun b bs ih pre => f b (pre bs) || ih (fun t => pre (b :: t))) ws
def anyPairF (f : ℕ → ℕ → List ℕ → Bool) (ws : List ℕ) : (List ℕ → List ℕ) → Bool :=
  List.rec (motive := fun _ => (List ℕ → List ℕ) → Bool) (fun _ => false)
    (fun a rest ih pre => anyOneF (fun b bs => f a b (pre bs)) rest id || ih (fun t => pre (a :: t))) ws

def tryF (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) (base w : ℕ) : Bool :=
  (fun v => (Nat.beq v full64 && next extra (w :: r)) ||
    (!(Nat.beq extra 0) && ((Nat.beq (Nat.lor v (sepF a)) full64 && next (extra - 1) (w :: a :: r)) ||
      (Nat.beq (Nat.lor v (sepF b)) full64 && next (extra - 1) (w :: b :: r)))) ||
    (Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v (sepF a)) (sepF b)) full64 &&
      next (extra - 2) (w :: a :: b :: r)))
    (Nat.lor (sepF w) base)
def dispatchF (extra : ℕ) (next : ℕ → List ℕ → Bool) (a b : ℕ) (r : List ℕ) : Bool :=
  (fun base ab => tryF extra next a b r base ab || tryF extra next a b r base (Nat.lor a b) ||
    tryF extra next a b r base (Nat.xor a ab) || tryF extra next a b r base (Nat.xor b ab))
    (cutsF r) (Nat.land a b)
def optF (k : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → List ℕ → Bool) (fun _ ws => isGoalF ws)
    (fun _ ih extra ws => isGoalF ws || anyPairF (fun a b r => dispatchF extra ih a b r) ws id) k

def kidsW (extra a b : ℕ) (r : List ℕ) (base w : ℕ) : List (ℕ × List ℕ) :=
  (fun v => (bif Nat.beq v full64 then [(extra, w :: r)] else []) ++
    (bif Nat.beq extra 0 then [] else
      (bif Nat.beq (Nat.lor v (sepF a)) full64 then [(extra - 1, w :: a :: r)] else []) ++
      (bif Nat.beq (Nat.lor v (sepF b)) full64 then [(extra - 1, w :: b :: r)] else [])) ++
    (bif Nat.ble 2 extra && Nat.beq (Nat.lor (Nat.lor v (sepF a)) (sepF b)) full64
      then [(extra - 2, w :: a :: b :: r)] else []))
    (Nat.lor (sepF w) base)
def kidsP (extra a b : ℕ) (r : List ℕ) : List (ℕ × List ℕ) :=
  (fun base ab => kidsW extra a b r base ab ++ kidsW extra a b r base (Nat.lor a b) ++
    kidsW extra a b r base (Nat.xor a ab) ++ kidsW extra a b r base (Nat.xor b ab))
    (cutsF r) (Nat.land a b)
def kidsF (s : ℕ × List ℕ) : List (ℕ × List ℕ) :=
  (pairs s.2).flatMap fun p => kidsP s.1 p.1 p.2.1 p.2.2
def rootsF (n : ℕ) (inputs : List ℕ) : List (ℕ × List ℕ) :=
  (inputs.sublists.filter fun ws => decide (ws.length ≤ n + 1) && Nat.beq (cutsF ws) full64).map
    fun ws => (n + 1 - ws.length, ws)

theorem beq_toNat {n : ℕ} (a b : BitVec n) : Nat.beq a.toNat b.toNat = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, ← BitVec.toNat_inj]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem full_spec (v : BitVec 64) : Nat.beq v.toNat full64 = (v == -1) := by
  rw [show full64 = (-1 : BitVec 64).toNat by decide +kernel]
  exact beq_toNat _ _

theorem sepF_spec (w : W) : sepF w.toNat = (sep w).toNat := by
  unfold sep
  rw [BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  change ((w.toNat >>> 64) ^^^ w.toNat) &&& full64 = ((w.toNat >>> 64) ^^^ w.toNat) % 2 ^ 64
  rw [show full64 = 2 ^ 64 - 1 by decide +kernel, Nat.and_two_pow_sub_one_eq_mod]

theorem lor_sep (v : BitVec 64) (w : W) : Nat.lor v.toNat (sepF w.toNat) = (v ||| sep w).toNat := by
  rw [sepF_spec, BitVec.toNat_or]; rfl

theorem sep_lor (v : BitVec 64) (w : W) : Nat.lor (sepF w.toNat) v.toNat = (sep w ||| v).toNat := by
  rw [sepF_spec, BitVec.toNat_or]; rfl

theorem cutsF_spec (ws : List W) : cutsF (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons a rest ih =>
    change Nat.lor (sepF a.toNat) (cutsF (rest.map BitVec.toNat)) = (sep a ||| cuts rest).toNat
    rw [ih, sep_lor]

theorem isGoalF_spec (ws : List W) :
    isGoalF (ws.map BitVec.toNat) = (ws == [goal] || ws == [~~~goal]) := by
  match ws with
  | [] => rfl
  | [w] =>
    change (true && (Nat.beq w.toNat goalF || Nat.beq w.toNat full64)) =
      ((w == goal && true) || (w == ~~~goal && true))
    rw [show goalF = goal.toNat by decide +kernel, show full64 = (~~~goal).toNat by decide +kernel,
      beq_toNat, beq_toNat, Bool.true_and, Bool.and_true, Bool.and_true]
  | w :: u :: rest =>
    change (false && (Nat.beq w.toNat goalF || Nat.beq w.toNat full64)) =
      ((w == goal && false) || (w == ~~~goal && false))
    rw [Bool.false_and, Bool.and_false, Bool.and_false, Bool.or_false]

theorem anyOneF_spec (f : ℕ → List ℕ → Bool) (ws : List ℕ) (pre : List ℕ → List ℕ) :
    anyOneF f ws pre = (singles ws).any (fun p => f p.1 (pre p.2)) := by
  induction ws generalizing pre with
  | nil => rfl
  | cons b bs ih =>
    change (f b (pre bs) || anyOneF f bs (fun t => pre (b :: t))) = _
    rw [ih, singles, List.any_cons, List.any_map]
    rfl

theorem anyPairF_spec (f : ℕ → ℕ → List ℕ → Bool) (ws : List ℕ) (pre : List ℕ → List ℕ) :
    anyPairF f ws pre = (pairs ws).any (fun p => f p.1 p.2.1 (pre p.2.2)) := by
  induction ws generalizing pre with
  | nil => rfl
  | cons a rest ih =>
    change (anyOneF (fun b bs => f a b (pre bs)) rest id || anyPairF f rest (fun t => pre (a :: t))) = _
    rw [ih, anyOneF_spec, pairs, List.any_append, List.any_map, List.any_map]
    rfl

theorem singles_map {α β : Type} (g : α → β) (ws : List α) :
    singles (ws.map g) = (singles ws).map (fun p => (g p.1, p.2.map g)) := by
  induction ws with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, singles, ih, List.map_map]
    rfl

theorem pairs_map {α β : Type} (g : α → β) (ws : List α) :
    pairs (ws.map g) = (pairs ws).map (fun p => (g p.1, g p.2.1, p.2.2.map g)) := by
  induction ws with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, pairs, ih, singles_map, List.map_map, List.map_append]
    rfl

theorem andNot_eq (a b : W) : a &&& ~~~b = a ^^^ (a &&& b) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_xor]
  cases a[i] <;> cases b[i] <;> rfl

theorem andNot_eq' (a b : W) : b &&& ~~~a = b ^^^ (a &&& b) := by
  rw [andNot_eq, BitVec.and_comm]

theorem tryF_spec (extra : ℕ) (next : ℕ → List ℕ → Bool) (next' : ℕ → List W → Bool)
    (h : ∀ e l, next e (l.map BitVec.toNat) = next' e l) (a b w : W) (r : List W) :
    tryF extra next a.toNat b.toNat (r.map BitVec.toNat) (cuts r).toNat w.toNat =
      (((sep w ||| cuts r == -1) && next' extra (w :: r)) ||
      ((extra != 0) && (((sep w ||| cuts r ||| sep a == -1) && next' (extra - 1) (w :: a :: r)) ||
        ((sep w ||| cuts r ||| sep b == -1) && next' (extra - 1) (w :: b :: r)))) ||
      ((decide (extra ≥ 2)) && (sep w ||| cuts r ||| sep a ||| sep b == -1) &&
        next' (extra - 2) (w :: a :: b :: r))) := by
  have e0 : (!(Nat.beq extra 0)) = (extra != 0) := by cases extra <;> rfl
  have e2 : Nat.ble 2 extra = decide (extra ≥ 2) := by
    rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  unfold tryF
  simp only [sep_lor, lor_sep, full_spec, e0, e2, ← h, List.map_cons]

theorem dispatchF_spec (extra : ℕ) (next : ℕ → List ℕ → Bool) (next' : ℕ → List W → Bool)
    (h : ∀ e l, next e (l.map BitVec.toNat) = next' e l) (a b : W) (r : List W) :
    dispatchF extra next a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra next' a b r := by
  have h1 : Nat.land a.toNat b.toNat = (a &&& b).toNat := (BitVec.toNat_and a b).symm
  have h2 : Nat.lor a.toNat b.toNat = (a ||| b).toNat := (BitVec.toNat_or a b).symm
  have h3 : Nat.xor a.toNat (a &&& b).toNat = (a &&& ~~~b).toNat := by
    rw [andNot_eq, BitVec.toNat_xor]; rfl
  have h4 : Nat.xor b.toNat (a &&& b).toNat = (b &&& ~~~a).toNat := by
    rw [andNot_eq' a b, BitVec.toNat_xor]; rfl
  unfold dispatchF dispatch
  simp only [cutsF_spec, h1, h2, h3, h4, tryF_spec extra next next' h, ops, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_assoc]

theorem optF_spec (k extra : ℕ) (ws : List W) :
    optF k extra (ws.map BitVec.toNat) = optimized k extra ws := by
  induction k generalizing extra ws with
  | zero => exact isGoalF_spec ws
  | succ k ih =>
    change (isGoalF (ws.map BitVec.toNat) ||
      anyPairF (fun a b r => dispatchF extra (optF k) a b r) (ws.map BitVec.toNat) id) = _
    rw [isGoalF_spec, anyPairF_spec, pairs_map, List.any_map, optimized]
    congr 1
    apply congrArg
    funext p
    exact dispatchF_spec extra (optF k) (optimized k) ih p.1 p.2.1 p.2.2

theorem any_single (c : Bool) (s : ℕ × List ℕ) (p : ℕ × List ℕ → Bool) :
    (bif c then [s] else []).any p = (c && p s) := by
  cases c <;> simp

theorem any_unless (c : Bool) (l : List (ℕ × List ℕ)) (p : ℕ × List ℕ → Bool) :
    (bif c then [] else l).any p = (!c && l.any p) := by
  cases c <;> simp

theorem kidsW_any (next : ℕ → List ℕ → Bool) (extra a b : ℕ) (r : List ℕ) (base w : ℕ) :
    (kidsW extra a b r base w).any (fun s => next s.1 s.2) = tryF extra next a b r base w := by
  unfold kidsW tryF
  simp only [List.any_append, any_single, any_unless]

theorem optF_succ (k extra : ℕ) (ws : List ℕ) :
    optF (k + 1) extra ws = (isGoalF ws || (kidsF (extra, ws)).any (fun s => optF k s.1 s.2)) := by
  change (isGoalF ws || anyPairF (fun a b r => dispatchF extra (optF k) a b r) ws id) = _
  rw [anyPairF_spec]
  unfold kidsF
  rw [List.any_flatMap]
  congr 1
  apply congrArg
  funext p
  simp only [kidsP, List.any_append, kidsW_any]
  rfl

theorem peel (k : ℕ) (L : List (ℕ × List ℕ)) (hg : L.any (fun s => isGoalF s.2) = false)
    (h : (L.flatMap kidsF).any (fun s => optF k s.1 s.2) = false) :
    L.any (fun s => optF (k + 1) s.1 s.2) = false := by
  rw [List.any_eq_false] at hg ⊢
  rw [List.any_flatMap, List.any_eq_false] at h
  intro s hs
  rw [optF_succ, Bool.or_eq_true]
  rintro (c | c)
  · exact hg s hs c
  · exact h s hs c

theorem search_spec (n : ℕ) (inputs : List W) :
    search n inputs = (rootsF n (inputs.map BitVec.toNat)).any (fun s => optF n s.1 s.2) := by
  unfold search rootsF
  rw [List.sublists_map, List.filter_map, List.map_map, List.any_map, List.any_filter]
  apply congrArg
  funext ws
  simp only [Function.comp, cutsF_spec, full_spec, optF_spec, List.length_map]

theorem glue {α : Type} (l : List α) (p : α → Bool) (i c : ℕ)
    (h1 : ((l.drop i).take c).any p = false) (h2 : (l.drop (i + c)).any p = false) :
    (l.drop i).any p = false := by
  rw [← List.take_append_drop c (l.drop i), List.any_append, h1, List.drop_drop, h2]
  rfl

end Fast

def front : List (ℕ × List ℕ) :=
  ((rootsF 8 (rows.map BitVec.toNat)).flatMap kidsF).flatMap kidsF
def deep (s : ℕ × List ℕ) : Bool := optF 6 s.1 s.2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part0 : ((front.drop 0).take 123).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part1 : ((front.drop 123).take 181).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part2 : ((front.drop 304).take 179).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part3 : ((front.drop 483).take 159).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part4 : ((front.drop 642).take 169).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part5 : ((front.drop 811).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part6 : ((front.drop 1011).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part7 : ((front.drop 1211).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part8 : ((front.drop 1411).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part9 : ((front.drop 1611).take 144).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part10 : ((front.drop 1755).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part11 : ((front.drop 1955).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part12 : ((front.drop 2155).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part13 : ((front.drop 2355).take 200).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem part14 : (front.drop 2555).any deep = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem reject : search 8 rows = false := by
  rw [search_spec]
  refine peel 7 _ (by decide +kernel) ?_
  refine peel 6 _ (by decide +kernel) ?_
  show (front.drop 0).any deep = false
  refine glue front deep 0 123 part0 ?_
  refine glue front deep 123 181 part1 ?_
  refine glue front deep 304 179 part2 ?_
  refine glue front deep 483 159 part3 ?_
  refine glue front deep 642 169 part4 ?_
  refine glue front deep 811 200 part5 ?_
  refine glue front deep 1011 200 part6 ?_
  refine glue front deep 1211 200 part7 ?_
  refine glue front deep 1411 200 part8 ?_
  refine glue front deep 1611 144 part9 ?_
  refine glue front deep 1755 200 part10 ?_
  refine glue front deep 1955 200 part11 ?_
  refine glue front deep 2155 200 part12 ?_
  refine glue front deep 2355 200 part13 ?_
  exact part14

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 128, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_40471

theorem PEqualNP.Outside.L_meta_40471
    : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  exact PEqualNP.Outside.L_meta_40471.solve
