import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31865

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

abbrev W := BitVec 50
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 25 := ((x >>> 25) ^^^ x).setWidth 25
def cuts (ws : List W) : BitVec 25 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 25) ++ (0 : BitVec 25)
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

def differs (i : Fin 25) (w : W) : Prop :=
  w.getLsbD (25+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 25) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 25+i.val < 50 := by omega
  have hi' : i.val < 50 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 25) :
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
  change (cuts ws)[j] = (BitVec.allOnes 25)[j]
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
  · change reachable av (BitVec.allOnes 50 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 50)
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

private def bit (k : Fin 50) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 50) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 50) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 50 0)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [_, _] => true
  | .or, [_, _] => true
  | _, _ => false
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
    | exact .inl rfl
    | exact .inr (.inl rfl)
    | exact available_read hw _
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


private abbrev Basis (gs : List Gate) : Prop := ∀ g ∈ gs, legal g

private lemma wires_append (g1 g2 : List Gate) (x : List Bool) :
    Circuit.wires ⟨g1 ++ g2, 0⟩ x = Circuit.wires ⟨g2, 0⟩ (Circuit.wires ⟨g1, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

private lemma wires_append_singleton (pref : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨pref ++ [g], 0⟩ x =
    Circuit.wires ⟨pref, 0⟩ x ++ [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false)] := by
  rw [wires_append]
  rfl

private lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    simp only [Circuit.wires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

private lemma wires_cons_getD_lt (pref : List Gate) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + pref.length) :
    (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false = (Circuit.wires ⟨pref, 0⟩ x).getD w false := by
  rw [wires_append_singleton]
  have hlen : (Circuit.wires ⟨pref, 0⟩ x).length = x.length + pref.length := wires_length pref x
  have hlt : w < (Circuit.wires ⟨pref, 0⟩ x).length := by omega
  simp [List.getD, List.getElem?_append_left hlt]

private lemma wires_cons_getD_eq (pref : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD (x.length + pref.length) false =
    g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := by
  rw [wires_append_singleton]
  have hlen : (Circuit.wires ⟨pref, 0⟩ x).length = x.length + pref.length := wires_length pref x
  rw [← hlen]
  simp [List.getD]

private def Simple (D : List Bool → Prop) (p : ℕ) (f : List Bool → Bool) : Prop :=
  (∀ x, D x → f x = f (x.set p false)) ∨
  (∀ x, D x → f x = x.getD p false) ∨
  (∀ x, D x → f x = !(x.getD p false))

private lemma simple_const (D : List Bool → Prop) (p : ℕ) (b : Bool) :
    Simple D p (fun _ => b) := Or.inl (fun _ _ => rfl)

private lemma simple_not {D : List Bool → Prop} {p : ℕ} {f : List Bool → Bool}
    (hf : Simple D p f) : Simple D p (fun x => !(f x)) := by
  rcases hf with h1 | h2 | h3
  · exact Or.inl (fun x hx => by dsimp only; rw [h1 x hx])
  · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [h2 x hx]))
  · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [h3 x hx, Bool.not_not]))

private lemma wire_simple_all {D : List Bool → Prop} {p : ℕ} {pref : List Gate}
    (hlenD : ∀ x, D x → x.length = 8)
    (hpref : ∀ w < 8 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (w : ℕ) : Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false) := by
  by_cases hw : w < 8 + pref.length
  · exact hpref w hw
  · left
    intro x hx
    dsimp only
    have h1 : (Circuit.wires ⟨pref, 0⟩ x).length = 8 + pref.length := by
      rw [wires_length, hlenD x hx]
    have h2 : (Circuit.wires ⟨pref, 0⟩ (x.set p false)).length = 8 + pref.length := by
      rw [wires_length, List.length_set, hlenD x hx]
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma gate_non_simple {D : List Bool → Prop} {p : ℕ} {pref : List Gate} {g : Gate}
    (hlenD : ∀ x, D x → x.length = 8)
    (hD : ∀ x, D x → D (x.set p false))
    (hg : legal g)
    (hpref : ∀ w < 8 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (hnot : ¬ Simple D p (fun x => g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false))) :
    isBinary g = true ∧ ∃ g' : Gate,
      (legal g') ∧
      isBinary g' = false ∧
      ∀ x, D x → x.getD p false = false →
        g'.op.eval (g'.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) =
        g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  cases op with
  | not =>
    exfalso; apply hnot
    cases ins with
    | nil => exact simple_const D p true
    | cons a _ => exact simple_not (wire_simple_all hlenD hpref a)
  | mod m => simp at hop
  | maj => simp at hop
  | and =>
    match ins, hlen with
    | [], _ => exact False.elim (hnot (simple_const D p true))
    | [a], _ =>
      exfalso; apply hnot
      simpa [GateOp.eval] using wire_simple_all hlenD hpref a
    | [a, b], _ =>
      refine ⟨rfl, ?_⟩
      have ha := wire_simple_all hlenD hpref a
      have hb := wire_simple_all hlenD hpref b
      dsimp only [Simple] at ha hb
      rcases ha with ha1 | ha2 | ha3
      · rcases hb with hb1 | hb2 | hb3
        · exfalso; apply hnot; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha1 x hx, hb1 x hx]
        · refine ⟨⟨.or, []⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true]
          rw [hb2 x hx, hxp, Bool.and_false]
        · refine ⟨⟨.or, [a]⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [hb3 x hx, hxp, Bool.not_false, Bool.and_true]
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, []⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hxp, Bool.false_and]
        · exfalso; apply hnot; right; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hb2 x hx, Bool.and_self]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha2 x hx, hb3 x hx, ha2 _ hx', hb3 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, [b]⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          rw [ha3 x hx, hxp, Bool.not_false, Bool.true_and]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha3 x hx, hb2 x hx, ha3 _ hx', hb2 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
        · exfalso; apply hnot; right; right; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [ha3 x hx, hb3 x hx, Bool.and_self]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => exact False.elim (hnot (simple_const D p false))
    | [a], _ =>
      exfalso; apply hnot
      simpa [GateOp.eval] using wire_simple_all hlenD hpref a
    | [a, b], _ =>
      refine ⟨rfl, ?_⟩
      have ha := wire_simple_all hlenD hpref a
      have hb := wire_simple_all hlenD hpref b
      dsimp only [Simple] at ha hb
      rcases ha with ha1 | ha2 | ha3
      · rcases hb with hb1 | hb2 | hb3
        · exfalso; apply hnot; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha1 x hx, hb1 x hx]
        · refine ⟨⟨.or, [a]⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hb2 x hx, hxp, Bool.or_false]
        · refine ⟨⟨.and, []⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [hb3 x hx, hxp, Bool.not_false, Bool.or_true]
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.or, [b]⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hxp, Bool.false_or]
        · exfalso; apply hnot; right; left; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hb2 x hx, Bool.or_self]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha2 x hx, hb3 x hx, ha2 _ hx', hb3 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
      · rcases hb with hb1 | hb2 | hb3
        · refine ⟨⟨.and, []⟩, by simp [legal], rfl, fun x hx hxp => ?_⟩
          simp only [GateOp.eval, List.map, List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hxp, Bool.not_false, Bool.true_or]
        · exfalso; apply hnot; left; intro x hx
          have hx' := hD x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hb2 x hx, ha3 _ hx', hb2 _ hx']
          cases x.getD p false <;> cases (x.set p false).getD p false <;> rfl
        · exfalso; apply hnot; right; right; intro x hx
          dsimp only
          simp only [GateOp.eval, List.map, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          rw [ha3 x hx, hb3 x hx, Bool.or_self]
    | _ :: _ :: _ :: _, h => simp at h

private lemma elim_aux (D : List Bool → Prop) (p : ℕ)
    (hlenD : ∀ x, D x → x.length = 8)
    (hD : ∀ x, D x → D (x.set p false))
    (suff : List Gate) (pref : List Gate) (o : ℕ)
    (hb : Basis suff)
    (hpref : ∀ w < 8 + pref.length, Simple D p (fun x => (Circuit.wires ⟨pref, 0⟩ x).getD w false))
    (hnot : ¬ Simple D p (fun x => (Circuit.wires ⟨pref ++ suff, 0⟩ x).getD o false)) :
    ∃ suff' : List Gate, Basis suff' ∧ binaryCost suff' < binaryCost suff ∧
      ∀ x, D x → x.getD p false = false →
        Circuit.wires ⟨pref ++ suff', 0⟩ x = Circuit.wires ⟨pref ++ suff, 0⟩ x := by
  induction suff generalizing pref with
  | nil =>
    exfalso
    apply hnot
    simpa using wire_simple_all hlenD hpref o
  | cons g rest ih =>
    have hg : legal g :=
      hb g List.mem_cons_self
    have hrest : Basis rest := fun g' hg' => hb g' (List.mem_cons_of_mem _ hg')
    by_cases hgs : Simple D p (fun x => g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false))
    · have hpref' : ∀ w < 8 + (pref ++ [g]).length,
          Simple D p (fun x => (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false) := by
        intro w hw
        have hlen1 : (pref ++ [g]).length = pref.length + 1 := by simp
        by_cases hlt : w < 8 + pref.length
        · have heq : ∀ x, D x → (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD w false =
              (Circuit.wires ⟨pref, 0⟩ x).getD w false := fun x hx =>
            wires_cons_getD_lt pref g x w (by rw [hlenD x hx]; omega)
          have hwS := hpref w hlt
          dsimp only [Simple] at hwS
          rcases hwS with h1 | h2 | h3
          · exact Or.inl (fun x hx => by dsimp only; rw [heq x hx, heq _ (hD x hx), h1 x hx])
          · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [heq x hx, h2 x hx]))
          · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [heq x hx, h3 x hx]))
        · have hweq : w = 8 + pref.length := by omega
          subst hweq
          have heq : ∀ x, D x → (Circuit.wires ⟨pref ++ [g], 0⟩ x).getD (8 + pref.length) false =
              g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨pref, 0⟩ x).getD i false) := fun x hx => by
            have := wires_cons_getD_eq pref g x
            rwa [hlenD x hx] at this
          dsimp only [Simple] at hgs
          rcases hgs with h1 | h2 | h3
          · exact Or.inl (fun x hx => by dsimp only; rw [heq x hx, heq _ (hD x hx), h1 x hx])
          · exact Or.inr (Or.inl (fun x hx => by dsimp only; rw [heq x hx, h2 x hx]))
          · exact Or.inr (Or.inr (fun x hx => by dsimp only; rw [heq x hx, h3 x hx]))
      have hnot' : ¬ Simple D p (fun x => (Circuit.wires ⟨(pref ++ [g]) ++ rest, 0⟩ x).getD o false) := by
        simpa [List.append_assoc] using hnot
      obtain ⟨rest', hbr', hcr', hwr'⟩ := ih (pref ++ [g]) hrest hpref' hnot'
      refine ⟨g :: rest', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg
        · exact hbr' x hx'
      · unfold binaryCost at hcr' ⊢
        simp only [List.filter_cons]
        cases isBinary g <;> simp <;> omega
      · intro x hx hxp
        simpa [List.append_assoc] using hwr' x hx hxp
    · obtain ⟨hbin, g', hg', hbin', hgeval⟩ := gate_non_simple hlenD hD hg hpref hgs
      refine ⟨g' :: rest, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hg'
        · exact hrest x hx'
      · unfold binaryCost
        simp only [List.filter_cons, hbin, hbin']
        simp
      · intro x hx hxp
        have hstep : Circuit.wires ⟨pref ++ [g'], 0⟩ x = Circuit.wires ⟨pref ++ [g], 0⟩ x := by
          rw [wires_append_singleton, wires_append_singleton, hgeval x hx hxp]
        have h1 : pref ++ (g' :: rest) = (pref ++ [g']) ++ rest := by simp
        have h2 : pref ++ (g :: rest) = (pref ++ [g]) ++ rest := by simp
        calc Circuit.wires ⟨pref ++ (g' :: rest), 0⟩ x
            = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨pref ++ [g'], 0⟩ x) := by
                rw [h1]; exact wires_append (pref ++ [g']) rest x
          _ = Circuit.wires ⟨rest, 0⟩ (Circuit.wires ⟨pref ++ [g], 0⟩ x) := by rw [hstep]
          _ = Circuit.wires ⟨pref ++ (g :: rest), 0⟩ x := by
                rw [h2]; exact (wires_append (pref ++ [g]) rest x).symm

private lemma elim_step (D : List Bool → Prop) (p : ℕ)
    (hlenD : ∀ x, D x → x.length = 8)
    (hD : ∀ x, D x → D (x.set p false))
    (gs : List Gate) (o : ℕ) (hb : Basis gs)
    (hnot : ¬ Simple D p (fun x => Circuit.eval ⟨gs, o⟩ x)) :
    ∃ gs' : List Gate, Basis gs' ∧ binaryCost gs' < binaryCost gs ∧
      ∀ x, D x → x.getD p false = false →
        Circuit.eval ⟨gs', o⟩ x = Circuit.eval ⟨gs, o⟩ x := by
  have hpref : ∀ w < 8 + ([] : List Gate).length,
      Simple D p (fun x => (Circuit.wires ⟨[], 0⟩ x).getD w false) := by
    intro w _
    by_cases hwp : w = p
    · subst hwp
      exact Or.inr (Or.inl (fun _ _ => rfl))
    · left
      intro x _
      simp [Circuit.wires, List.getD, List.getElem?_set_ne (Ne.symm hwp)]
  have hnot' : ¬ Simple D p (fun x => (Circuit.wires ⟨[] ++ gs, 0⟩ x).getD o false) := hnot
  obtain ⟨gs', hb', hc', hw'⟩ := elim_aux D p hlenD hD gs [] o hb hpref hnot'
  refine ⟨gs', hb', hc', fun x hx hxp => ?_⟩
  change (Circuit.wires ⟨[] ++ gs', 0⟩ x).getD o false = (Circuit.wires ⟨[] ++ gs, 0⟩ x).getD o false
  rw [hw' x hx hxp]



def F (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def fL (l : List Bool) : Bool := F (fun i : Fin 8 => l.getD i.val false)

private lemma list_ofFn_getD (l : List Bool) (hl : l.length = 8) :
    List.ofFn (fun i : Fin 8 => l.getD i.val false) = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

def rowsR : List W := [0x1201042b77b61, 0x808185f95cca, 0x182a21ceb536, 0x20244195de29d]
def rowsAll : List W := [0x1201042b77b61, 0, 0, 0, 0, 0x808185f95cca, 0x182a21ceb536, 0x20244195de29d]

private def firstChoice (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W) : Bool :=
  let v := sep w ||| cuts r
  ((v == -1) && next extra (w :: r)) ||
  ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                     ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
  ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_1_0_child3 : optimized 5 1 [11622464, 316729187597153, 141293786848458, 26569234887990, 565441460036253] = false := by decide +kernel

private theorem first_0_1_0 : firstChoice 3 (optimized 5) 316729187597153 141293786848458 [26569234887990, 565441460036253] 11622464 = false := by
  have c0 : (((sep (11622464 : W) ||| cuts [26569234887990, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (11622464 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (11622464 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (11622464 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_1_0_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_1_1_child3 : optimized 5 1 [458022962823147, 316729187597153, 141293786848458, 26569234887990, 565441460036253] = false := by decide +kernel

private theorem first_0_1_1 : firstChoice 3 (optimized 5) 316729187597153 141293786848458 [26569234887990, 565441460036253] 458022962823147 = false := by
  have c0 : (((sep (458022962823147 : W) ||| cuts [26569234887990, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (458022962823147 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (458022962823147 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (458022962823147 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_1_1_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_1_2_child3 : optimized 5 1 [316729175974689, 316729187597153, 141293786848458, 26569234887990, 565441460036253] = false := by decide +kernel

private theorem first_0_1_2 : firstChoice 3 (optimized 5) 316729187597153 141293786848458 [26569234887990, 565441460036253] 316729175974689 = false := by
  have c0 : (((sep (316729175974689 : W) ||| cuts [26569234887990, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (316729175974689 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (316729175974689 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (316729175974689 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_1_2_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_1_3_child3 : optimized 5 1 [141293775225994, 316729187597153, 141293786848458, 26569234887990, 565441460036253] = false := by decide +kernel

private theorem first_0_1_3 : firstChoice 3 (optimized 5) 316729187597153 141293786848458 [26569234887990, 565441460036253] 141293775225994 = false := by
  have c0 : (((sep (141293775225994 : W) ||| cuts [26569234887990, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (141293775225994 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (141293775225994 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (141293775225994 : W) ||| cuts [26569234887990, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_1_3_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

private theorem pair_0_1 : dispatch 3 (optimized 5) 316729187597153 141293786848458 [26569234887990, 565441460036253] = false := by
  change (ops 316729187597153 141293786848458).any (firstChoice 3 (optimized 5) 316729187597153 141293786848458 [26569234887990, 565441460036253]) = false
  have step : ops 316729187597153 141293786848458 = [11622464, 458022962823147, 316729175974689, 141293775225994] := by decide
  rw [step]
  simp only [List.any_cons, List.any_nil, first_0_1_0, first_0_1_1, first_0_1_2, first_0_1_3, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_2_0_child3 : optimized 5 1 [8794400, 316729187597153, 26569234887990, 141293786848458, 565441460036253] = false := by decide +kernel

private theorem first_0_2_0 : firstChoice 3 (optimized 5) 316729187597153 26569234887990 [141293786848458, 565441460036253] 8794400 = false := by
  have c0 : (((sep (8794400 : W) ||| cuts [141293786848458, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (8794400 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (8794400 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (8794400 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_2_0_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_2_1_child3 : optimized 5 1 [343298413690743, 316729187597153, 26569234887990, 141293786848458, 565441460036253] = false := by decide +kernel

private theorem first_0_2_1 : firstChoice 3 (optimized 5) 316729187597153 26569234887990 [141293786848458, 565441460036253] 343298413690743 = false := by
  have c0 : (((sep (343298413690743 : W) ||| cuts [141293786848458, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (343298413690743 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (343298413690743 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (343298413690743 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_2_1_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_2_2_child3 : optimized 5 1 [316729178802753, 316729187597153, 26569234887990, 141293786848458, 565441460036253] = false := by decide +kernel

private theorem first_0_2_2 : firstChoice 3 (optimized 5) 316729187597153 26569234887990 [141293786848458, 565441460036253] 316729178802753 = false := by
  have c0 : (((sep (316729178802753 : W) ||| cuts [141293786848458, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (316729178802753 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (316729178802753 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (316729178802753 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_2_2_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_2_3_child3 : optimized 5 1 [26569226093590, 316729187597153, 26569234887990, 141293786848458, 565441460036253] = false := by decide +kernel

private theorem first_0_2_3 : firstChoice 3 (optimized 5) 316729187597153 26569234887990 [141293786848458, 565441460036253] 26569226093590 = false := by
  have c0 : (((sep (26569226093590 : W) ||| cuts [141293786848458, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (26569226093590 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (26569226093590 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (26569226093590 : W) ||| cuts [141293786848458, 565441460036253]) ||| sep (316729187597153 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_2_3_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

private theorem pair_0_2 : dispatch 3 (optimized 5) 316729187597153 26569234887990 [141293786848458, 565441460036253] = false := by
  change (ops 316729187597153 26569234887990).any (firstChoice 3 (optimized 5) 316729187597153 26569234887990 [141293786848458, 565441460036253]) = false
  have step : ops 316729187597153 26569234887990 = [8794400, 343298413690743, 316729178802753, 26569226093590] := by decide
  rw [step]
  simp only [List.any_cons, List.any_nil, first_0_2_0, first_0_2_1, first_0_2_2, first_0_2_3, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_3_0_child3 : optimized 5 1 [1401345, 316729187597153, 565441460036253, 141293786848458, 26569234887990] = false := by decide +kernel

private theorem first_0_3_0 : firstChoice 3 (optimized 5) 316729187597153 565441460036253 [141293786848458, 26569234887990] 1401345 = false := by
  have c0 : (((sep (1401345 : W) ||| cuts [141293786848458, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (1401345 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (1401345 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (1401345 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_3_0_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_3_1_child3 : optimized 5 1 [882170646232061, 316729187597153, 565441460036253, 141293786848458, 26569234887990] = false := by decide +kernel

private theorem first_0_3_1 : firstChoice 3 (optimized 5) 316729187597153 565441460036253 [141293786848458, 26569234887990] 882170646232061 = false := by
  have c0 : (((sep (882170646232061 : W) ||| cuts [141293786848458, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (882170646232061 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (882170646232061 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (882170646232061 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_3_1_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_3_2_child3 : optimized 5 1 [316729186195808, 316729187597153, 565441460036253, 141293786848458, 26569234887990] = false := by decide +kernel

private theorem first_0_3_2 : firstChoice 3 (optimized 5) 316729187597153 565441460036253 [141293786848458, 26569234887990] 316729186195808 = false := by
  have c0 : (((sep (316729186195808 : W) ||| cuts [141293786848458, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (316729186195808 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (316729186195808 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (316729186195808 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_3_2_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_0_3_3_child3 : optimized 5 1 [565441458634908, 316729187597153, 565441460036253, 141293786848458, 26569234887990] = false := by decide +kernel

private theorem first_0_3_3 : firstChoice 3 (optimized 5) 316729187597153 565441460036253 [141293786848458, 26569234887990] 565441458634908 = false := by
  have c0 : (((sep (565441458634908 : W) ||| cuts [141293786848458, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (565441458634908 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (565441458634908 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (565441458634908 : W) ||| cuts [141293786848458, 26569234887990]) ||| sep (316729187597153 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_0_3_3_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

private theorem pair_0_3 : dispatch 3 (optimized 5) 316729187597153 565441460036253 [141293786848458, 26569234887990] = false := by
  change (ops 316729187597153 565441460036253).any (firstChoice 3 (optimized 5) 316729187597153 565441460036253 [141293786848458, 26569234887990]) = false
  have step : ops 316729187597153 565441460036253 = [1401345, 882170646232061, 316729186195808, 565441458634908] := by decide
  rw [step]
  simp only [List.any_cons, List.any_nil, first_0_3_0, first_0_3_1, first_0_3_2, first_0_3_3, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_2_0_child3 : optimized 5 1 [29889538, 141293786848458, 26569234887990, 316729187597153, 565441460036253] = false := by decide +kernel

private theorem first_1_2_0 : firstChoice 3 (optimized 5) 141293786848458 26569234887990 [316729187597153, 565441460036253] 29889538 = false := by
  have c0 : (((sep (29889538 : W) ||| cuts [316729187597153, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (29889538 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (29889538 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (29889538 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_2_0_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_2_1_child3 : optimized 5 1 [167862991846910, 141293786848458, 26569234887990, 316729187597153, 565441460036253] = false := by decide +kernel

private theorem first_1_2_1 : firstChoice 3 (optimized 5) 141293786848458 26569234887990 [316729187597153, 565441460036253] 167862991846910 = false := by
  have c0 : (((sep (167862991846910 : W) ||| cuts [316729187597153, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (167862991846910 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (167862991846910 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (167862991846910 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_2_1_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_2_2_child3 : optimized 5 1 [141293756958920, 141293786848458, 26569234887990, 316729187597153, 565441460036253] = false := by decide +kernel

private theorem first_1_2_2 : firstChoice 3 (optimized 5) 141293786848458 26569234887990 [316729187597153, 565441460036253] 141293756958920 = false := by
  have c0 : (((sep (141293756958920 : W) ||| cuts [316729187597153, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (141293756958920 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (141293756958920 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (141293756958920 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_2_2_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_2_3_child3 : optimized 5 1 [26569204998452, 141293786848458, 26569234887990, 316729187597153, 565441460036253] = false := by decide +kernel

private theorem first_1_2_3 : firstChoice 3 (optimized 5) 141293786848458 26569234887990 [316729187597153, 565441460036253] 26569204998452 = false := by
  have c0 : (((sep (26569204998452 : W) ||| cuts [316729187597153, 565441460036253])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (26569204998452 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (26569204998452 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (26569204998452 : W) ||| cuts [316729187597153, 565441460036253]) ||| sep (141293786848458 : W) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_2_3_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

private theorem pair_1_2 : dispatch 3 (optimized 5) 141293786848458 26569234887990 [316729187597153, 565441460036253] = false := by
  change (ops 141293786848458 26569234887990).any (firstChoice 3 (optimized 5) 141293786848458 26569234887990 [316729187597153, 565441460036253]) = false
  have step : ops 141293786848458 26569234887990 = [29889538, 167862991846910, 141293756958920, 26569204998452] := by decide
  rw [step]
  simp only [List.any_cons, List.any_nil, first_1_2_0, first_1_2_1, first_1_2_2, first_1_2_3, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_3_0_child3 : optimized 5 1 [22626440, 141293786848458, 565441460036253, 316729187597153, 26569234887990] = false := by decide +kernel

private theorem first_1_3_0 : firstChoice 3 (optimized 5) 141293786848458 565441460036253 [316729187597153, 26569234887990] 22626440 = false := by
  have c0 : (((sep (22626440 : W) ||| cuts [316729187597153, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (22626440 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (22626440 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (22626440 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_3_0_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_3_1_child3 : optimized 5 1 [706735224258271, 141293786848458, 565441460036253, 316729187597153, 26569234887990] = false := by decide +kernel

private theorem first_1_3_1 : firstChoice 3 (optimized 5) 141293786848458 565441460036253 [316729187597153, 26569234887990] 706735224258271 = false := by
  have c0 : (((sep (706735224258271 : W) ||| cuts [316729187597153, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (706735224258271 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (706735224258271 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (706735224258271 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_3_1_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_3_2_child3 : optimized 5 1 [141293764222018, 141293786848458, 565441460036253, 316729187597153, 26569234887990] = false := by decide +kernel

private theorem first_1_3_2 : firstChoice 3 (optimized 5) 141293786848458 565441460036253 [316729187597153, 26569234887990] 141293764222018 = false := by
  have c0 : (((sep (141293764222018 : W) ||| cuts [316729187597153, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (141293764222018 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (141293764222018 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (141293764222018 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_3_2_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_1_3_3_child3 : optimized 5 1 [565441437409813, 141293786848458, 565441460036253, 316729187597153, 26569234887990] = false := by decide +kernel

private theorem first_1_3_3 : firstChoice 3 (optimized 5) 141293786848458 565441460036253 [316729187597153, 26569234887990] 565441437409813 = false := by
  have c0 : (((sep (565441437409813 : W) ||| cuts [316729187597153, 26569234887990])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (565441437409813 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (565441437409813 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (565441437409813 : W) ||| cuts [316729187597153, 26569234887990]) ||| sep (141293786848458 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_1_3_3_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

private theorem pair_1_3 : dispatch 3 (optimized 5) 141293786848458 565441460036253 [316729187597153, 26569234887990] = false := by
  change (ops 141293786848458 565441460036253).any (firstChoice 3 (optimized 5) 141293786848458 565441460036253 [316729187597153, 26569234887990]) = false
  have step : ops 141293786848458 565441460036253 = [22626440, 706735224258271, 141293764222018, 565441437409813] := by decide
  rw [step]
  simp only [List.any_cons, List.any_nil, first_1_3_0, first_1_3_1, first_1_3_2, first_1_3_3, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_2_3_0_child3 : optimized 5 1 [21798932, 26569234887990, 565441460036253, 316729187597153, 141293786848458] = false := by decide +kernel

private theorem first_2_3_0 : firstChoice 3 (optimized 5) 26569234887990 565441460036253 [316729187597153, 141293786848458] 21798932 = false := by
  have c0 : (((sep (21798932 : W) ||| cuts [316729187597153, 141293786848458])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (21798932 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (21798932 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (21798932 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_2_3_0_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_2_3_1_child3 : optimized 5 1 [592010673125311, 26569234887990, 565441460036253, 316729187597153, 141293786848458] = false := by decide +kernel

private theorem first_2_3_1 : firstChoice 3 (optimized 5) 26569234887990 565441460036253 [316729187597153, 141293786848458] 592010673125311 = false := by
  have c0 : (((sep (592010673125311 : W) ||| cuts [316729187597153, 141293786848458])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (592010673125311 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (592010673125311 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (592010673125311 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_2_3_1_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_2_3_2_child3 : optimized 5 1 [26569213089058, 26569234887990, 565441460036253, 316729187597153, 141293786848458] = false := by decide +kernel

private theorem first_2_3_2 : firstChoice 3 (optimized 5) 26569234887990 565441460036253 [316729187597153, 141293786848458] 26569213089058 = false := by
  have c0 : (((sep (26569213089058 : W) ||| cuts [316729187597153, 141293786848458])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (26569213089058 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (26569213089058 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (26569213089058 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_2_3_2_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem first_2_3_3_child3 : optimized 5 1 [565441438237321, 26569234887990, 565441460036253, 316729187597153, 141293786848458] = false := by decide +kernel

private theorem first_2_3_3 : firstChoice 3 (optimized 5) 26569234887990 565441460036253 [316729187597153, 141293786848458] 565441438237321 = false := by
  have c0 : (((sep (565441438237321 : W) ||| cuts [316729187597153, 141293786848458])) == (-1 : BitVec 25)) = false := by decide
  have c1 : (((sep (565441438237321 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W)) == (-1 : BitVec 25)) = false := by decide
  have c2 : (((sep (565441438237321 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = false := by decide
  have c3 : (((sep (565441438237321 : W) ||| cuts [316729187597153, 141293786848458]) ||| sep (26569234887990 : W) ||| sep (565441460036253 : W)) == (-1 : BitVec 25)) = true := by decide
  have remainOne : (3 : ℕ) - 1 = 2 := by decide
  have remainTwo : (3 : ℕ) - 2 = 1 := by decide
  have hasOne : ((3 : ℕ) != 0) = true := by decide
  have hasTwo : decide ((3 : ℕ) ≥ 2) = true := by decide
  simp only [firstChoice, remainOne, remainTwo, hasOne, hasTwo, c0, c1, c2, c3, first_2_3_3_child3, Bool.and_false, Bool.false_and, Bool.true_and, Bool.and_true, Bool.or_false, Bool.false_or]

private theorem pair_2_3 : dispatch 3 (optimized 5) 26569234887990 565441460036253 [316729187597153, 141293786848458] = false := by
  change (ops 26569234887990 565441460036253).any (firstChoice 3 (optimized 5) 26569234887990 565441460036253 [316729187597153, 141293786848458]) = false
  have step : ops 26569234887990 565441460036253 = [21798932, 592010673125311, 26569213089058, 565441438237321] := by decide
  rw [step]
  simp only [List.any_cons, List.any_nil, first_2_3_0, first_2_3_1, first_2_3_2, first_2_3_3, Bool.false_or]

private theorem allPairs : optimized 6 3 rowsR = false := by
  have hzero : (rowsR == [goal] || rowsR == [~~~goal]) = false := by decide
  have hp : pairs rowsR = [(316729187597153, 141293786848458, [26569234887990, 565441460036253]), (316729187597153, 26569234887990, [141293786848458, 565441460036253]), (316729187597153, 565441460036253, [141293786848458, 26569234887990]), (141293786848458, 26569234887990, [316729187597153, 565441460036253]), (141293786848458, 565441460036253, [316729187597153, 26569234887990]), (26569234887990, 565441460036253, [316729187597153, 141293786848458])] := by decide
  change ((rowsR == [goal] || rowsR == [~~~goal]) || (pairs rowsR).any (fun (a, b, r) => dispatch 3 (optimized 5) a b r)) = false
  rw [hzero, Bool.false_or, hp]
  simp only [List.any_cons, List.any_nil, pair_0_1, pair_0_2, pair_0_3, pair_1_2, pair_1_3, pair_2_3, Bool.false_or]

theorem reject : search 6 rowsR = false := by
  let starts := rowsR.sublists.filter (fun ws => decide (ws.length ≤ 6+1) && (cuts ws == -1))
  have hstarts : starts = [rowsR] := by decide
  have he : search 6 rowsR = starts.any (fun ws => optimized 6 (6+1-ws.length) ws) := by
    simp only [starts, List.any_filter, search, Bool.and_assoc]
  rw [he, hstarts]
  change (optimized 6 3 rowsR || false) = false
  simp only [allPairs, Bool.false_or]

theorem rowsR_nd : rowsR.Nodup := by decide

theorem sample : ∀ k : Fin 50, F (fun i : Fin 8 => bit k (rowsAll.getD i.val 0)) = bit k (~~~goal) := by
  decide +kernel

private abbrev D0 (l : List Bool) : Prop := l.length = 8
private abbrev D1 (l : List Bool) : Prop := l.length = 8 ∧ l.getD 1 false = false
private abbrev D2 (l : List Bool) : Prop := l.length = 8 ∧ l.getD 1 false = false ∧ l.getD 2 false = false
private abbrev D3 (l : List Bool) : Prop := l.length = 8 ∧ l.getD 1 false = false ∧ l.getD 2 false = false ∧ l.getD 3 false = false
private abbrev D4 (l : List Bool) : Prop := l.length = 8 ∧ l.getD 1 false = false ∧ l.getD 2 false = false ∧ l.getD 3 false = false ∧ l.getD 4 false = false

private lemma elim_chain (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    ∃ gsE : List Gate, (∀ g ∈ gsE, legal g) ∧ binaryCost gsE + 4 ≤ binaryCost gs ∧
      ∀ l, D4 l → Circuit.eval ⟨gsE, o⟩ l = fL l := by
  have he0 : ∀ l, D0 l → Circuit.eval ⟨gs, o⟩ l = fL l := by
    intro l hl
    have h1 := he (fun i : Fin 8 => l.getD i.val false)
    rwa [list_ofFn_getD l hl] at h1
  have hns0 : ¬ Simple D0 1 (fun l => Circuit.eval ⟨gs, o⟩ l) := by
    rintro (h1 | h2 | h3)
    · have ha := h1 [false, true, false, false, true, false, false, false] rfl
      dsimp only [List.set] at ha
      rw [he0 _ rfl, he0 _ rfl] at ha; exact Bool.noConfusion ha
    · have hb := h2 [false, true, false, false, false, false, false, false] rfl
      dsimp only at hb
      rw [he0 _ rfl] at hb; exact Bool.noConfusion hb
    · have hc := h3 [false, false, false, false, false, false, false, false] rfl
      dsimp only at hc
      rw [he0 _ rfl] at hc; exact Bool.noConfusion hc
  obtain ⟨gs1, hg1, hc1, he1'⟩ := elim_step D0 1 (fun _ h => h)
    (fun l hl => by show (l.set 1 false).length = 8; rw [List.length_set]; exact hl) gs o hg hns0
  have he1 : ∀ l, D1 l → Circuit.eval ⟨gs1, o⟩ l = fL l := fun l ⟨hl, h0⟩ => (he1' l hl h0).trans (he0 l hl)
  have hns1 : ¬ Simple D1 2 (fun l => Circuit.eval ⟨gs1, o⟩ l) := by
    rintro (h1 | h2 | h3)
    · have ha := h1 [false, false, true, false, false, true, false, false] ⟨rfl, rfl⟩
      dsimp only [List.set] at ha
      rw [he1 _ ⟨rfl, rfl⟩, he1 _ ⟨rfl, rfl⟩] at ha; exact Bool.noConfusion ha
    · have hb := h2 [false, false, true, false, false, false, false, false] ⟨rfl, rfl⟩
      dsimp only at hb
      rw [he1 _ ⟨rfl, rfl⟩] at hb; exact Bool.noConfusion hb
    · have hc := h3 [false, false, false, false, false, false, false, false] ⟨rfl, rfl⟩
      dsimp only at hc
      rw [he1 _ ⟨rfl, rfl⟩] at hc; exact Bool.noConfusion hc
  obtain ⟨gs2, hg2, hc2, he2'⟩ := elim_step D1 2 (fun _ h => h.1)
    (fun l ⟨hl, h0⟩ => ⟨by rw [List.length_set]; exact hl, by rw [List.getD, List.getElem?_set_ne (by decide)]; exact h0⟩) gs1 o hg1 hns1
  have he2 : ∀ l, D2 l → Circuit.eval ⟨gs2, o⟩ l = fL l := fun l ⟨hl, h0, h1⟩ => (he2' l ⟨hl, h0⟩ h1).trans (he1 l ⟨hl, h0⟩)
  have hns2 : ¬ Simple D2 3 (fun l => Circuit.eval ⟨gs2, o⟩ l) := by
    rintro (h1 | h2 | h3)
    · have ha := h1 [false, false, false, true, false, false, true, false] ⟨rfl, rfl, rfl⟩
      dsimp only [List.set] at ha
      rw [he2 _ ⟨rfl, rfl, rfl⟩, he2 _ ⟨rfl, rfl, rfl⟩] at ha; exact Bool.noConfusion ha
    · have hb := h2 [false, false, false, true, false, false, false, false] ⟨rfl, rfl, rfl⟩
      dsimp only at hb
      rw [he2 _ ⟨rfl, rfl, rfl⟩] at hb; exact Bool.noConfusion hb
    · have hc := h3 [false, false, false, false, false, false, false, false] ⟨rfl, rfl, rfl⟩
      dsimp only at hc
      rw [he2 _ ⟨rfl, rfl, rfl⟩] at hc; exact Bool.noConfusion hc
  obtain ⟨gs3, hg3, hc3, he3'⟩ := elim_step D2 3 (fun _ h => h.1)
    (fun l ⟨hl, h0, h1⟩ => ⟨by rw [List.length_set]; exact hl, by rw [List.getD, List.getElem?_set_ne (by decide)]; exact h0, by rw [List.getD, List.getElem?_set_ne (by decide)]; exact h1⟩) gs2 o hg2 hns2
  have he3 : ∀ l, D3 l → Circuit.eval ⟨gs3, o⟩ l = fL l := fun l ⟨hl, h0, h1, h2⟩ => (he3' l ⟨hl, h0, h1⟩ h2).trans (he2 l ⟨hl, h0, h1⟩)
  have hns3 : ¬ Simple D3 4 (fun l => Circuit.eval ⟨gs3, o⟩ l) := by
    rintro (h1 | h2 | h3)
    · have ha := h1 [true, false, false, false, true, false, false, false] ⟨rfl, rfl, rfl, rfl⟩
      dsimp only [List.set] at ha
      rw [he3 _ ⟨rfl, rfl, rfl, rfl⟩, he3 _ ⟨rfl, rfl, rfl, rfl⟩] at ha; exact Bool.noConfusion ha
    · have hb := h2 [false, false, false, false, true, false, false, false] ⟨rfl, rfl, rfl, rfl⟩
      dsimp only at hb
      rw [he3 _ ⟨rfl, rfl, rfl, rfl⟩] at hb; exact Bool.noConfusion hb
    · have hc := h3 [false, false, false, false, false, false, false, false] ⟨rfl, rfl, rfl, rfl⟩
      dsimp only at hc
      rw [he3 _ ⟨rfl, rfl, rfl, rfl⟩] at hc; exact Bool.noConfusion hc
  obtain ⟨gs4, hg4, hc4, he4'⟩ := elim_step D3 4 (fun _ h => h.1)
    (fun l ⟨hl, h0, h1, h2⟩ => ⟨by rw [List.length_set]; exact hl, by rw [List.getD, List.getElem?_set_ne (by decide)]; exact h0, by rw [List.getD, List.getElem?_set_ne (by decide)]; exact h1, by rw [List.getD, List.getElem?_set_ne (by decide)]; exact h2⟩) gs3 o hg3 hns3
  have he4 : ∀ l, D4 l → Circuit.eval ⟨gs4, o⟩ l = fL l := fun l ⟨hl, h0, h1, h2, h3⟩ => (he4' l ⟨hl, h0, h1, h2⟩ h3).trans (he3 l ⟨hl, h0, h1, h2⟩)
  exact ⟨gs4, hg4, by omega, he4⟩

set_option maxRecDepth 8000 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    10 < binaryCost gs := by
  obtain ⟨gsE, hgE, hcost, heE⟩ := elim_chain gs o hg he
  suffices hB : 6 < binaryCost gsE by omega
  by_contra! low
  have init : ∀ u ∈ rowsAll, holds rowsR.toFinset u := by
    intro u hu
    simp only [rowsAll, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (by simp [rowsR]), .inl rfl⟩)
    · exact .inl rfl
    · exact .inl rfl
    · exact .inl rfl
    · exact .inl rfl
    · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (by simp [rowsR]), .inl rfl⟩)
    · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (by simp [rowsR]), .inl rfl⟩)
    · exact .inr (.inr ⟨_, List.mem_toFinset.mpr (by simp [rowsR]), .inl rfl⟩)
  have evaluate (k : Fin 50) :
      (gsE.foldl step (rowsAll.map (bit k))).getD o false = bit k (~~~goal) := by
    have bit0 : bit k (0 : W) = false := by change (BitVec.ofNat 50 0)[k.val] = false; simp
    have hDE : D4 (rowsAll.map (bit k)) := by
      refine ⟨by simp [rowsAll], ?_, ?_, ?_, ?_⟩
      · simpa [rowsAll] using bit0
      · simpa [rowsAll] using bit0
      · simpa [rowsAll] using bit0
      · simpa [rowsAll] using bit0
    have hsame : fL (rowsAll.map (bit k)) = F (fun i : Fin 8 => bit k (rowsAll.getD i.val 0)) := by
      unfold fL
      congr 1
      funext i
      exact read_bit rowsAll i.val k
    change Circuit.eval ⟨gsE, o⟩ (rowsAll.map (bit k)) = bit k (~~~goal)
    rw [heE _ hDE, hsame]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gsE o hgE rowsAll rowsR.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a rowsR.toFinset) :
      build basicOps t c rowsR.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 6 rowsR rowsR_nd (lift low run)))

theorem bridge : ∀ x : Fin 8 → Bool,
    decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) = F x := by
  decide +kernel

def wg : List Gate :=
  [⟨.or, [4, 5]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [10, 7]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [16, 6]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [18, 17]⟩]

theorem wfits : ∀ g ∈ wg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem weval_F : ∀ x : Fin 8 → Bool, Circuit.eval ⟨wg, 19⟩ (List.ofFn x) = F x := by
  decide +kernel

end PEqualNP.Outside.L_meta_31865

theorem PEqualNP.Outside.L_meta_31865 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 5, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hlegal hnot1 heval
  by_cases hasNot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_31865.binaryCost gates < gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_31865.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_31865.isBinary, op]⟩
    have hb := PEqualNP.Outside.L_meta_31865.bound gates o hlegal
      (fun x => (heval x).trans (PEqualNP.Outside.L_meta_31865.bridge x))
    have hlen : PEqualNP.Outside.L_meta_31865.wg.length = 12 := rfl
    refine ⟨PEqualNP.Outside.L_meta_31865.wg, 19, PEqualNP.Outside.L_meta_31865.wfits, by omega, ?_⟩
    intro x
    exact (PEqualNP.Outside.L_meta_31865.weval_F x).trans (PEqualNP.Outside.L_meta_31865.bridge x).symm
  · refine ⟨gates, o, ?_, Nat.le_refl _, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hlegal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
