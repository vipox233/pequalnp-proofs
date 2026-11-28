import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37045.Signed

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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra fail
  have ha : ¬ differs i a := fun h => fail (.inl h)
  have hb : ¬ differs i b := fun h => fail (.inr h)
  apply hd
  unfold differs at ha hb
  have ha' : a.getLsbD (64 + i.val) = a.getLsbD i.val := Classical.byContradiction ha
  have hb' : b.getLsbD (64 + i.val) = b.getLsbD i.val := Classical.byContradiction hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha', hb']

set_option maxRecDepth 100000 in
theorem cuts_spec (ws : List W) (i : Fin 64) :
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
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  grind

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

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
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

set_option maxRecDepth 100000 in
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

theorem bound_from_search {n : Nat} (budget : Nat) (F : (Fin n → Bool) → Bool) (inputs : List W) (width : inputs.length = n)
    (nd : inputs.Nodup) (reject : search budget inputs = false)
    (sample : ∀ k : Fin 128, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    budget < binaryCost gs := by
  by_contra hnot
  have low : binaryCost gs ≤ budget := Nat.le_of_not_lt hnot
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin n) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht budget inputs nd (lift low run)))

def strictN {α : Type} (v : ℕ) (k : ℕ → α) : α :=
  match v with
  | 0 => k 0
  | n + 1 => k (n + 1)

theorem strictN_eq {α : Type} (v : ℕ) (k : ℕ → α) : strictN v k = k v := by
  cases v <;> rfl

def forceList {α : Type} : List W → (List W → α) → α
  | [], k => k []
  | x :: xs, k => strictN x.toNat fun xn => forceList xs fun ys => k (BitVec.ofNat 128 xn :: ys)

theorem forceList_eq {α : Type} (l : List W) : ∀ k : List W → α, forceList l k = k l := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih => intro k; simp [forceList, strictN_eq, ih]

def dispatchF (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  strictN (cuts r).toNat fun bn =>
  (ops a b).any fun w0 =>
    strictN w0.toNat fun wn =>
    strictN (sep (BitVec.ofNat 128 wn) ||| BitVec.ofNat 64 bn).toNat fun vn =>
    ((BitVec.ofNat 64 vn == -1) && next extra (BitVec.ofNat 128 wn :: r)) ||
    ((extra != 0) && (((BitVec.ofNat 64 vn ||| sep a == -1) && next (extra - 1) (BitVec.ofNat 128 wn :: a :: r)) ||
                       ((BitVec.ofNat 64 vn ||| sep b == -1) && next (extra - 1) (BitVec.ofNat 128 wn :: b :: r)))) ||
    ((extra ≥ 2) && (BitVec.ofNat 64 vn ||| sep a ||| sep b == -1) && next (extra - 2) (BitVec.ofNat 128 wn :: a :: b :: r))

theorem ofNat_toNat_wide (x : W) : BitVec.ofNat 128 x.toNat = x := by simp

theorem ofNat_toNat_half (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem dispatchF_eq (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) :
    dispatchF extra next a b r = dispatch extra next a b r := by
  simp only [dispatchF, dispatch, strictN_eq, ofNat_toNat_wide, ofNat_toNat_half]

def optimizedF : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => forceList ws fun vs => (vs == [goal] || vs == [~~~goal]) ||
    (pairs vs).any (fun (a, b, r) => dispatchF extra (optimizedF k) a b r)

theorem optimizedF_eq : ∀ (k extra : ℕ) (ws : List W), optimizedF k extra ws = optimized k extra ws := by
  intro k
  induction k with
  | zero => intro extra ws; rfl
  | succ k ih =>
    intro extra ws
    have hk : optimizedF k = optimized k := by funext e w; exact ih e w
    simp only [optimizedF, optimized, forceList_eq, hk]
    congr 1
    congr 1
    funext p
    exact dispatchF_eq extra (optimized k) p.1 p.2.1 p.2.2

def searchF (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimizedF n (n+1-ws.length) ws

theorem searchF_eq (n : ℕ) (inputs : List W) : searchF n inputs = search n inputs := by
  have h : optimizedF n = optimized n := by funext e w; exact optimizedF_eq n e w
  simp only [searchF, search, h]

end PEqualNP.Outside.L_meta_37045.Signed
namespace PEqualNP.Outside.L_meta_37045
namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isNegGate (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem negGate_iff (g : Gate) : isNegGate g = true ↔ g.op = .not := by
  cases g with | mk o l => cases o <;> simp [isNegGate]

theorem countNeg_le (gs : List Gate)
    (u : ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j) :
    gs.countP isNegGate ≤ 1 := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun i j hi hj => Fin.ext (by
      have h := u i.succ j.succ hi hj
      exact Nat.succ.inj (congrArg Fin.val h)))
    by_cases neg : g.op = .not
    · have clear : gs.countP isNegGate = 0 := by
        apply List.countP_eq_zero.mpr
        intro k hk
        obtain ⟨i, rfl⟩ := List.get_of_mem hk
        have ne : (gs.get i).op ≠ .not := by
          intro h; have absurd := u 0 i.succ neg h
          have := congrArg Fin.val absurd
          simp at this
        cases h : isNegGate (gs.get i)
        · decide
        · exact (ne ((negGate_iff _).mp h)).elim
      simp [List.countP_cons,(negGate_iff g).mpr neg,clear]
    · simpa [List.countP_cons,negGate_iff,neg] using tail

theorem gateMonoOn (g : Gate) (h : g.op = .and ∨ g.op = .or)
    (a b : ℕ → Bool) (le : ∀ i ∈ g.inputs, a i ≤ b i) :
    g.op.eval (g.inputs.map a) ≤ g.op.eval (g.inputs.map b) := by
  rcases h with e | e
  · rw [e]; simp only [GateOp.eval,List.all_map,Function.comp_def]
    apply Bool.le_iff_imp.mpr
    intro ha
    simp_all only [List.all_eq_true,decide_eq_true_eq]
    intro i hi
    exact Bool.le_iff_imp.mp (le i hi) (ha i hi)
  · rw [e]; simp only [GateOp.eval,List.any_map,Function.comp_def]
    apply Bool.le_iff_imp.mpr
    intro ha
    simp_all only [List.any_eq_true,decide_eq_true_eq]
    obtain ⟨i,hi,ha⟩ := ha
    exact ⟨i,hi,Bool.le_iff_imp.mp (le i hi) ha⟩

theorem wiresAnti (gs : List Gate) (p : ℕ) (legal : ∀ g ∈ gs, Ok g)
    (no : ∀ g ∈ gs, g.op ≠ GateOp.not → p ∉ g.inputs)
    (unique : gs.countP isNegGate ≤ 1) :
    ∀ (A B : List Bool), A.length = B.length → p < A.length →
      A.getD p false = true → B.getD p false = false →
      (∀ i ≠ p, A.getD i false ≤ B.getD i false) →
      ((∃ g ∈ gs, g.op = GateOp.not) → ∀ i ≠ p, A.getD i false = B.getD i false) →
      ∀ i ≠ p, (wiresFrom gs A).getD i false ≤ (wiresFrom gs B).getD i false := by
  induction gs with
  | nil => intro A B _ _ _ _ le _; exact le
  | cons g gs ih =>
    intro A B lens plen ap bp le eq
    let newBit (W : List Bool) := g.op.eval (g.inputs.map fun i => W.getD i false)
    have child (h : ∃ k ∈ gs, k.op = GateOp.not) : g.op ≠ GateOp.not := by
      obtain ⟨k,hk,e⟩ := h
      have pos : 0 < gs.countP isNegGate := List.countP_pos_iff.mpr ⟨k,hk,(negGate_iff k).mpr e⟩
      intro bad
      simp only [List.countP_cons,(negGate_iff g).mpr bad,if_true] at unique
      omega
    have bit : newBit A ≤ newBit B := by
      by_cases neg : g.op = GateOp.not
      · have he := eq ⟨g,List.mem_cons_self,neg⟩
        unfold newBit
        rw [neg]
        cases hs : g.inputs with
        | nil => simp [GateOp.eval]
        | cons i ins =>
          change (!A.getD i false) ≤ !B.getD i false
          by_cases hn : i = p
          · rw [hn,ap,bp]; decide
          · rw [he i hn]
      · have hg := (legal g List.mem_cons_self).1
        have ops : g.op = .and ∨ g.op = .or := by
          rcases hg with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (neg h).elim
        exact gateMonoOn g ops _ _ (fun i hi => le i (fun e => no g List.mem_cons_self neg (e ▸ hi)))
    have ut : gs.countP isNegGate ≤ 1 := by
      rw [List.countP_cons] at unique
      split at unique <;> omega
    apply ih (fun k hk => legal k (List.mem_cons_of_mem _ hk))
      (fun k hk => no k (List.mem_cons_of_mem _ hk)) ut
      (A ++ [newBit A]) (B ++ [newBit B]) (by simp [lens]) (by simp;omega)
      (by rw [List.getD_append _ _ _ _ plen];exact ap)
      (by rw [List.getD_append _ _ _ _ (lens ▸ plen)];exact bp)
    · intro i nei
      by_cases h : i = A.length
      · rw [h,getD_snoc_eq,lens,getD_snoc_eq];exact bit
      · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)];exact le i nei
    · intro ex i nei
      have he := eq (by obtain ⟨k,hk,hn⟩ := ex;exact ⟨k,List.mem_cons_of_mem _ hk,hn⟩)
      by_cases h : i = A.length
      · rw [h,getD_snoc_eq,lens,getD_snoc_eq]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        exact he j (fun e => no g List.mem_cons_self (child ex) (e ▸ hj))
      · rw [getD_snoc_ne _ _ _ _ h,getD_snoc_ne _ _ _ _ (by omega)];exact he i nei

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isBinaryGate (g : Gate) : Bool := !isNegGate g
abbrev binaryCount (gs : List Gate) := gs.countP isBinaryGate

theorem binary_of_ne {g : Gate} (ne : g.op ≠ .not) : isBinaryGate g = true := by
  cases h : isNegGate g
  · simp [isBinaryGate,h]
  · exact (ne ((negGate_iff _).mp h)).elim

theorem simp_binary_le (g : Gate) (m : ℕ) (ins : List Stat) :
    binaryCount (simplify g.op m ins).1.toList ≤ (if isBinaryGate g then 1 else 0) := by
  by_cases neg : g.op = .not
  · rw [show isBinaryGate g = false by simp [isBinaryGate,(negGate_iff g).mpr neg]]
    rw [neg]
    cases ins with
    | nil => simp [binaryCount,simplify,simpNot]
    | cons s t => cases s <;> simp [binaryCount,simplify,simpNot,isBinaryGate,isNegGate]
  · have flag := binary_of_ne neg
    rw [flag]
    exact le_trans List.countP_le_length (toList_length_le _)

theorem bin_step (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binaryCount (elimStep n acc g).2 ≤ binaryCount acc.2 + (if isBinaryGate g then 1 else 0) := by
  simp only [elimStep,binaryCount,List.countP_append]
  exact Nat.add_le_add_left (simp_binary_le _ _ _) _

theorem bin_all (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    binaryCount (elim n gs acc).2 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs generalizing acc with
  | nil => simp [elim,binaryCount]
  | cons g gs ih =>
    have a := ih (elimStep n acc g)
    have b := bin_step n acc g
    rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
    omega

theorem bin_save (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, g.op ≠ .not ∧ k ∈ g.inputs) →
    binaryCount (elim n gs acc).2 + 1 ≤ binaryCount acc.2 + binaryCount gs := by
  induction gs with
  | nil => intro acc _ _ _ h; simpa using h
  | cons g gs ih =>
    intro acc ok hk hc hex
    by_cases hit : g.op ≠ .not ∧ k ∈ g.inputs
    · obtain ⟨c,hc⟩ := hc
      have hg := ok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hg.1.1
        · simpa using hg.1.2
        · intro h; simpa using hg.2 h
        · exact ⟨c,List.mem_map.2 ⟨k,hit.2,hc⟩⟩
      have same : (elimStep n acc g).2 = acc.2 := by simp only [elimStep,hnone];simp
      have after := bin_all n gs (elimStep n acc g)
      rw [same] at after
      have flag := binary_of_ne hit.1
      rw [elim_cons];simp only [binaryCount,List.countP_cons,flag,if_true] at *
      omega
    · have rest : ∃ g ∈ gs, g.op ≠ .not ∧ k ∈ g.inputs := by
        obtain ⟨g',hmem,props⟩ := hex
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact (hit props).elim
        · exact ⟨_,hmem,props⟩
      have step := bin_step n acc g
      have after := ih (elimStep n acc g) (fun j hj => ok j (List.mem_cons_of_mem _ hj))
        (by simp [elimStep];omega)
        (by obtain ⟨c,hc⟩ := hc; refine ⟨c,?_⟩;simp only [elimStep];rw [getD_snoc_ne _ _ _ _ (by omega)];exact hc)
        rest
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem needsPositiveReader (n : ℕ) (C : Circuit) (legal : FanInTwo C)
    (unique : C.gates.countP isNegGate ≤ 1) (hout : C.output ≠ n)
    (y : Fin n → Bool)
    (up : C.eval (List.ofFn (Fin.snoc y true)) = true)
    (dn : C.eval (List.ofFn (Fin.snoc y false)) = false) :
    ∃ g ∈ C.gates, g.op ≠ .not ∧ n ∈ g.inputs := by
  by_contra no
  have bad : ∀ g ∈ C.gates, g.op ≠ .not → n ∉ g.inputs :=
    fun g hg a b => no ⟨g,hg,a,b⟩
  let W := List.ofFn y
  have len : W.length = n := by simp [W]
  have same (i : ℕ) (ne : i ≠ n) : (W ++ [true]).getD i false = (W ++ [false]).getD i false := by
    rw [getD_snoc_ne _ _ _ _ (by omega),getD_snoc_ne _ _ _ _ (by omega)]
  have h := wiresAnti C.gates n legal bad unique (W ++ [true]) (W ++ [false])
    (by simp) (by simp [len]) (getD_snoc_len _ _ _ _ len) (getD_snoc_len _ _ _ _ len)
    (fun i hi => le_of_eq (same i hi)) (fun _ => same) C.output hout
  rw [ofFn_snoc] at up dn
  change (wiresFrom C.gates (W ++ [true])).getD C.output false = true at up
  change (wiresFrom C.gates (W ++ [false])).getD C.output false = false at dn
  rw [up,dn] at h
  contradiction

theorem normBinary (gs : List Gate) : binaryCount (gs.map normGate) = binaryCount gs := by
  simp only [binaryCount,List.countP_map]
  have eq : isBinaryGate ∘ normGate = isBinaryGate := by
    funext g
    cases g with | mk op t => cases op <;> rfl
  rw [eq]

theorem saveBinaryLast (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (unique : C.gates.countP isNegGate ≤ 1)
    (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (inc : ∃ y : Fin n → Bool, f (Fin.snoc y true) = true ∧ f (Fin.snoc y false) = false)
    (nonconstant : ∃ y z : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc z false)) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y false)) ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates := by
  have hout : C.output ≠ n := by
    intro out
    have fixed (y : Fin n → Bool) : f (Fin.snoc y false) = false := by
      rw [← comp,ofFn_snoc]
      change (wiresFrom C.gates (List.ofFn y ++ [false])).getD C.output false = false
      rw [out,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨y,z,ne⟩ := nonconstant
    exact ne ((fixed _).trans (fixed _).symm)
  obtain ⟨y,yup,ydn⟩ := inc
  obtain ⟨g,mem,op,read⟩ := needsPositiveReader n C fit unique hout y
    ((comp _).trans yup) ((comp _).trans ydn)
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, NOk g := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact normGate_nok u (fit u hu)
  have same : normGate g = g := by
    cases g with | mk o t => cases o <;> simp_all [normGate]
  have read' : ∃ t ∈ gs, t.op ≠ .not ∧ n ∈ t.inputs :=
    ⟨g,same ▸ List.mem_map_of_mem mem,op,read⟩
  set acc := elim n gs (initStats n false,[]) with ha
  have val (z : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) = f (Fin.snoc z false) := by
    have h := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (hok k hk).1) (inv_init n false z)
    rw [((h.2 C.output).2 : statVal _ _ = _), ← ofFn_snoc,hgs,wiresFrom_norm,← comp]
    rfl
  cases status : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y,z,ne⟩ := nonconstant
    exfalso;apply ne;rw [← val y,← val z,status];rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),?_,?_⟩
    · intro z;have e := val z;rw [status] at e;exact e
    · have h := bin_save n n gs (initStats n false,[]) hok (by simp [initStats])
        ⟨false,getD_snoc_len _ _ _ _ (by simp)⟩ read'
      change binaryCount acc.2 + 1 ≤ binaryCount ([] : List Gate) + binaryCount gs at h
      have counts : binaryCount gs = binaryCount C.gates := normBinary _
      rw [counts] at h
      simpa only [binaryCount,List.countP_nil,Nat.zero_add] using h

theorem relabelBinary {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    binaryCount (relabel n m π C).gates = binaryCount C.gates := by
  simp only [binaryCount,relabel,List.countP_map]
  rfl

theorem binary_lt_length (gs : List Gate) (ex : ∃ g ∈ gs, g.op = .not) :
    binaryCount gs < gs.length := by
  obtain ⟨g,hg,neg⟩ := ex
  by_contra! h
  have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
  simp [isBinaryGate,(negGate_iff g).mpr neg] at eq

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem relabelFan {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (fit : FanInTwo C) :
    FanInTwo (relabel n m π C) := by
  intro g hg
  obtain ⟨h, mem, rfl⟩ := List.mem_map.mp hg
  exact ⟨(fit h mem).1, by simpa [relGate] using (fit h mem).2⟩

theorem relabelHasNot {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (ex : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ g ∈ (relabel n m π C).gates, g.op = GateOp.not := by
  obtain ⟨g, hg, hop⟩ := ex
  exact ⟨relGate n m π g, List.mem_map.mpr ⟨g,hg,rfl⟩, hop⟩

theorem relabelUniqueNot {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j) :
    let D := relabel n m π C
    ∀ i j : Fin D.gates.length, (D.gates.get i).op = GateOp.not →
      (D.gates.get j).op = GateOp.not → i = j := by
  dsimp only
  intro i j hi hj
  let a : Fin C.gates.length := ⟨i.val, by simpa [relabel] using i.isLt⟩
  let b : Fin C.gates.length := ⟨j.val, by simpa [relabel] using j.isLt⟩
  have pick (k : Fin (C.gates.map (relGate n m π)).length) :
      ((C.gates.map (relGate n m π)).get k).op =
      (C.gates.get ⟨k.val, by simpa using k.isLt⟩).op := by
    change ((C.gates.map (relGate n m π))[k.val]).op =
      (C.gates[k.val]'(by simpa using k.isLt)).op
    rw [List.getElem_map]
    rfl
  have ha : (C.gates.get a).op = GateOp.not := (pick i).symm.trans hi
  have hb : (C.gates.get b).op = GateOp.not := (pick j).symm.trans hj
  apply Fin.ext
  exact congrArg (fun k : Fin C.gates.length => k.val) (unique a b ha hb)

theorem relabelEval {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) := by
  exact (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output

theorem liftBinaryLower (π : Fin 8 → Fin 8) (graph : (Fin 8 → Bool) → Bool)
    (base : (Fin 7 → Bool) → Bool) (b : ℕ)
    (inc : ∃ y : Fin 7 → Bool, graph ((Fin.snoc y true) ∘ π) = true ∧ graph ((Fin.snoc y false) ∘ π) = false)
    (nc : ∃ y z : Fin 7 → Bool, graph ((Fin.snoc y false) ∘ π) ≠ graph ((Fin.snoc z false) ∘ π))
    (table : ∀ y, graph ((Fin.snoc y false) ∘ π) = base y)
    (baseLower : ∀ D : Circuit, FanInTwo D → (∀ x, D.eval (List.ofFn x) = base x) → b ≤ binaryCount D.gates)
    (C : Circuit) (fit : FanInTwo C)
    (unique : ∀ i j : Fin C.gates.length, (C.gates.get i).op = .not → (C.gates.get j).op = .not → i = j)
    (has : ∃ g ∈ C.gates, g.op = .not) (comp : ∀ x, C.eval (List.ofFn x) = graph x) :
    b + 2 ≤ C.gates.length := by
  let D := relabel 8 8 π C
  have cd (x : Fin 8 → Bool) : D.eval (List.ofFn x) = graph (x ∘ π) :=
    (relabelEval π C x).trans (comp _)
  have un := countNeg_le D.gates (relabelUniqueNot π C unique)
  obtain ⟨S,fitS,evS,saved⟩ := saveBinaryLast 7 (fun x => graph (x ∘ π)) D
    (relabelFan π C fit) un cd inc nc
  have l := baseLower S fitS (fun x => (evS x).trans (table x))
  have same : binaryCount D.gates = binaryCount C.gates := relabelBinary π C
  have lt := binary_lt_length _ has
  omega
end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem simplify_neg_sub (g : Gate) (m : ℕ) (ins : List Stat) :
    (simplify g.op m ins).1.toList.countP isNegGate ≤ (if isNegGate g then 1 else 0) := by
  cases g with
  | mk op inp =>
    cases op with
    | not => exact le_trans List.countP_le_length (toList_length_le _)
    | and =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simplify,simpAnd,isNegGate]
    | or =>
      rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
        simp [simplify,simpOr,isNegGate]
    | _ => simp [simplify,isNegGate]

theorem elim_neg_sub (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).2.countP isNegGate ≤ acc.2.countP isNegGate + gs.countP isNegGate := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    have step : (elimStep n acc g).2.countP isNegGate ≤ acc.2.countP isNegGate + (if isNegGate g then 1 else 0) := by
      simp only [elimStep,List.countP_append]
      exact Nat.add_le_add_left (simplify_neg_sub _ _ _) _
    have tail := ih (elimStep n acc g)
    rw [elim_cons,List.countP_cons]
    omega

theorem normNeg (gs : List Gate) : (gs.map normGate).countP isNegGate = gs.countP isNegGate := by
  rw [List.countP_map]
  have e : isNegGate ∘ normGate = isNegGate := by
    funext g;cases g with | mk op t => cases op <;> rfl
  rw [e]
end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem saveBinaryWithBudget (n : ℕ) (bit : Bool) (f : (Fin (n + 1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (unique : C.gates.countP isNegGate ≤ 1)
    (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (inc : ∃ y : Fin n → Bool, f (Fin.snoc y true) = true ∧ f (Fin.snoc y false) = false)
    (nonconstant : ∃ y z : Fin n → Bool, f (Fin.snoc y bit) ≠ f (Fin.snoc z bit)) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y bit)) ∧
      binaryCount D.gates + 1 ≤ binaryCount C.gates ∧ D.gates.countP isNegGate ≤ C.gates.countP isNegGate := by
  have hout : C.output ≠ n := by
    intro out
    have fixed (y : Fin n → Bool) : f (Fin.snoc y bit) = bit := by
      rw [← comp,ofFn_snoc]
      change (wiresFrom C.gates (List.ofFn y ++ [bit])).getD C.output false = bit
      rw [out,getD_wiresFrom _ _ _ (by simp)]
      exact getD_snoc_len _ _ _ _ (by simp)
    obtain ⟨y,z,ne⟩ := nonconstant
    exact ne ((fixed _).trans (fixed _).symm)
  obtain ⟨y,yup,ydn⟩ := inc
  obtain ⟨g,mem,op,read⟩ := needsPositiveReader n C fit unique hout y
    ((comp _).trans yup) ((comp _).trans ydn)
  set gs := C.gates.map normGate with hgs
  have hok : ∀ g ∈ gs, NOk g := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    exact normGate_nok u (fit u hu)
  have same : normGate g = g := by
    cases g with | mk o t => cases o <;> simp_all [normGate]
  have read' : ∃ t ∈ gs, t.op ≠ .not ∧ n ∈ t.inputs :=
    ⟨g,same ▸ List.mem_map_of_mem mem,op,read⟩
  set acc := elim n gs (initStats n bit,[]) with ha
  have val (z : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn z)) (acc.1.getD C.output (Sum.inl false)) = f (Fin.snoc z bit) := by
    have h := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (hok k hk).1) (inv_init n bit z)
    rw [((h.2 C.output).2 : statVal _ _ = _), ← ofFn_snoc,hgs,wiresFrom_norm,← comp]
    rfl
  cases status : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨y,z,ne⟩ := nonconstant
    exfalso;apply ne;rw [← val y,← val z,status];rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩,elim_ok n gs _ (by simp),?_,?_,?_⟩
    · intro z;have e := val z;rw [status] at e;exact e
    · have h := bin_save n n gs (initStats n bit,[]) hok (by simp [initStats])
        ⟨bit,getD_snoc_len _ _ _ _ (by simp)⟩ read'
      change binaryCount acc.2 + 1 ≤ binaryCount ([] : List Gate) + binaryCount gs at h
      have counts : binaryCount gs = binaryCount C.gates := normBinary _
      rw [counts] at h
      simpa only [binaryCount,List.countP_nil,Nat.zero_add] using h
    · have h := elim_neg_sub n gs (initStats n bit,[])
      change acc.2.countP isNegGate ≤ ([] : List Gate).countP isNegGate + gs.countP isNegGate at h
      have e : gs.countP isNegGate = C.gates.countP isNegGate := normNeg _
      rw [e] at h
      simpa only [List.countP_nil,Nat.zero_add] using h

end Transfer

namespace Transfer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev SA := List Stat × List Gate
abbrev signal (w : List Bool) (i : Nat) := w.getD i false
abbrev statusAt (s : SA) (i : Nat) := s.1.getD i (Sum.inl false)
def nextBit (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map (signal w))
abbrev pushBit (w : List Bool) (g : Gate) := w ++ [nextBit w g]
def diffInput (a b : List Bool) (g : Gate) :=
  ∃ i ∈ g.inputs, signal a i ≠ signal b i
def tracks (a b : List Bool) (s : SA) (p : Nat → Stat → Prop) :=
  ∀ i, signal a i ≠ signal b i → p i (statusAt s i)
abbrev constantStat (v : Stat) := ∃ c : Bool, v = Sum.inl c

theorem pushLast (w : List Bool) (g : Gate) (i : Nat) (h : i = w.length) :
    signal (pushBit w g) i = nextBit w g := h ▸ getD_snoc_eq _ _ _

theorem pushOld (w : List Bool) (g : Gate) (i : Nat) (h : i ≠ w.length) :
    signal (pushBit w g) i = signal w i := getD_snoc_ne _ _ _ _ h

theorem differentReader {a b : List Bool} {g : Gate}
    (h : nextBit a g ≠ nextBit b g) : diffInput a b g := by
  by_contra hno
  apply h
  unfold nextBit
  congr 1
  apply List.map_congr_left
  intro i hi
  by_contra ne
  exact hno ⟨i,hi,ne⟩

theorem chargedStep {n : Nat} {s : SA} {g : Gate} (ok : NOk g) (binary : g.op ≠ .not)
    {i : Nat} (read : i ∈ g.inputs) (val : constantStat (statusAt s i)) :
    binaryCount (elimStep n s g).2 + 1 ≤ binaryCount s.2 + (if isBinaryGate g then 1 else 0) := by
  obtain ⟨c,hc⟩ := val
  have size := elimStep_none n s g ok i read c hc
  have same : (elimStep n s g).2 = s.2 := by
    let tail := (simplify g.op (n + s.2.length) (g.inputs.map (statusAt s))).1.toList
    change (s.2 ++ tail).length = s.2.length at size
    rw [List.length_append] at size
    have nil : tail = [] := List.length_eq_zero_iff.mp (by omega)
    change s.2 ++ tail = s.2
    rw [nil,List.append_nil]
  rw [same,binary_of_ne binary]
  simp

theorem preserveBefore {n : Nat} {a b w : List Bool} {s : SA} {g : Gate}
    (la : a.length = s.1.length) (lb : b.length = s.1.length) (lw : w.length = s.1.length)
    (prev : tracks a b s (fun i v => v = Sum.inl (signal w i)))
    (easy : g.op = .not ∨ ¬diffInput a b g) :
    tracks (pushBit a g) (pushBit b g) (elimStep n s g)
      (fun i v => v = Sum.inl (signal (pushBit w g) i)) := by
  intro i disagree
  by_cases last : i = s.1.length
  · subst i
    rw [show signal (pushBit a g) s.1.length = nextBit a g by rw [← la]; exact getD_snoc_eq _ _ _,
        show signal (pushBit b g) s.1.length = nextBit b g by rw [← lb]; exact getD_snoc_eq _ _ _] at disagree
    have rd := differentReader disagree
    have neg := easy.resolve_right (fun e => e rd)
    rw [show signal (pushBit w g) s.1.length = nextBit w g by rw [← lw]; exact getD_snoc_eq _ _ _]
    change (s.1 ++ [_]).getD s.1.length _ = _
    rw [getD_snoc_eq]
    cases he : g.inputs with
    | nil => simp [nextBit,he,neg,GateOp.eval] at disagree
    | cons j rest =>
      have delta : signal a j ≠ signal b j := by
        simpa [nextBit,neg,he,GateOp.eval] using disagree
      have eq := prev j delta
      change s.1.getD j (Sum.inl false) = Sum.inl (signal w j) at eq
      simp only [simplify,neg,he,List.map_cons,eq,simpNot,nextBit,GateOp.eval,List.headD_cons]
  · have hda := getD_snoc_ne a (nextBit a g) false i (by omega)
    have hdb := getD_snoc_ne b (nextBit b g) false i (by omega)
    have hdw := getD_snoc_ne w (nextBit w g) false i (by omega)
    have hstat : statusAt (elimStep n s g) i = statusAt s i := getD_snoc_ne _ _ _ _ last
    rw [hstat,pushOld w g i (by omega)]
    exact prev i (by simpa only [signal,pushBit,hda,hdb] using disagree)

theorem trackStep {n : Nat} {a b : List Bool} {s : SA} {g : Gate}
    (la : a.length = s.1.length) (lb : b.length = s.1.length)
    (prev : tracks a b s (fun _ v => constantStat v))
    (new : nextBit a g ≠ nextBit b g → constantStat (statusAt (elimStep n s g) s.1.length)) :
    tracks (pushBit a g) (pushBit b g) (elimStep n s g) (fun _ v => constantStat v) := by
  intro i diff
  by_cases eq : i = s.1.length
  · subst i
    exact new (by simpa only [pushLast a g _ la.symm,pushLast b g _ lb.symm] using diff)
  · have prevDiff : signal a i ≠ signal b i := by
      simpa only [pushOld a g i (by omega),pushOld b g i (by omega)] using diff
    have same : statusAt (elimStep n s g) i = statusAt s i := getD_snoc_ne _ _ _ _ eq
    rw [same];exact prev i prevDiff

theorem staysConstant {n : Nat} {a b : List Bool} {s : SA} {g : Gate}
    (prev : tracks a b s (fun _ v => constantStat v))
    (easy : g.op = .not ∨ ¬diffInput a b g) (diff : nextBit a g ≠ nextBit b g) :
    constantStat (statusAt (elimStep n s g) s.1.length) := by
  have neg := easy.resolve_right (fun e => e (differentReader diff))
  unfold constantStat statusAt
  simp only [elimStep]
  rw [getD_snoc_eq]
  cases h : g.inputs with
  | nil => simp [nextBit,neg,h] at diff
  | cons j rest =>
    have delta : signal a j ≠ signal b j := by simpa [nextBit,neg,h,GateOp.eval] using diff
    obtain ⟨c,hc⟩ := prev j delta
    change s.1.getD j (Sum.inl false) = Sum.inl c at hc
    exact ⟨!c,by simp only [simplify,neg,List.map_cons,hc,simpNot]⟩

theorem afterFirst (n : Nat) (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, NOk g) :
    ∀ a b s, a.length = s.1.length → b.length = s.1.length →
      tracks a b s (fun _ v => constantStat v) →
      signal (wiresFrom gs a) o ≠ signal (wiresFrom gs b) o →
      ¬constantStat (statusAt (elim n gs s) o) →
      binaryCount (elim n gs s).2 + 1 ≤ binaryCount s.2 + binaryCount gs := by
  induction gs with
  | nil =>
    intro a b s _ _ prev diff non
    exact (non (prev o diff)).elim
  | cons g gs ih =>
    intro a b s la lb prev diff non
    have ok := legal g List.mem_cons_self
    by_cases hit : g.op ≠ .not ∧ diffInput a b g
    · obtain ⟨op,i,read,delta⟩ := hit
      have first := chargedStep (n := n) ok op read (prev i delta)
      have tail := bin_all n gs (elimStep n s g)
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega
    · have easy : g.op = .not ∨ ¬diffInput a b g := by tauto
      have still := trackStep la lb prev (staysConstant (n := n) prev easy)
      have tail := ih (fun k hk => legal k (List.mem_cons_of_mem _ hk)) (pushBit a g) (pushBit b g) (elimStep n s g)
        (by simp [pushBit,elimStep,la]) (by simp [pushBit,elimStep,lb]) still diff non
      have step := bin_step n s g
      rw [elim_cons];simp only [binaryCount,List.countP_cons] at *
      omega

theorem pickBranch (v : Bool → Bool) (force : Bool) (diff : v false ≠ v true) :
    ∃ b, v b = force := by
  by_cases e : v false = force
  · exact ⟨false,e⟩
  · refine ⟨true,?_⟩
    cases h0 : v false <;> cases h1 : v true <;> cases force <;> simp_all

theorem beforeFirst (n : Nat) (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, NOk g) :
    ∀ (w : Bool → List Bool) (s : Bool → SA),
      (∀ a b, (w a).length = (s b).1.length) →
      (∀ b, tracks (w false) (w true) (s b) (fun i v => v = Sum.inl (signal (w b) i))) →
      signal (wiresFrom gs (w false)) o ≠ signal (wiresFrom gs (w true)) o →
      (∀ b, ¬constantStat (statusAt (elim n gs (s b)) o)) →
      ∃ b, binaryCount (elim n gs (s b)).2 + 2 ≤ binaryCount (s b).2 + binaryCount gs := by
  induction gs with
  | nil =>
    intro w s _ prev diff non
    exact (non false ⟨_,prev false o diff⟩).elim
  | cons g gs ih =>
    intro w s width prev diff non
    have ok := legal g List.mem_cons_self
    have tailOk (k) (hk : k ∈ gs) := legal k (List.mem_cons_of_mem _ hk)
    let w' := fun b => pushBit (w b) g
    let s' := fun b => elimStep n (s b) g
    have width' (a b : Bool) : (w' a).length = (s' b).1.length := by simp [w',s',pushBit,elimStep,width a b]
    by_cases hit : g.op ≠ .not ∧ diffInput (w false) (w true) g
    · obtain ⟨op,i,read,delta⟩ := hit
      obtain ⟨b,force⟩ := pickBranch (fun b => signal (w b) i) (fixBit g) delta
      have hc := prev b i delta
      have first := chargedStep (n := n) ok op read ⟨_,hc⟩
      have status := elimStep_const n (s b) g ok i read (hc.trans (congrArg Sum.inl force))
      have still : tracks (w' false) (w' true) (s' b) (fun _ v => constantStat v) :=
        trackStep (width false b) (width true b) (fun j d => ⟨_,prev b j d⟩) (fun _ => status)
      have tail := afterFirst n gs o tailOk (w' false) (w' true) (s' b)
        (width' false b) (width' true b) still diff (non b)
      refine ⟨b,?_⟩
      change binaryCount (elim n gs (s' b)).2 + 2 ≤ _
      change binaryCount (s' b).2 + 1 ≤ _ at first
      simp only [binaryCount,List.countP_cons] at *
      omega
    · have easy : g.op = .not ∨ ¬diffInput (w false) (w true) g := by tauto
      have next (b) := preserveBefore (n := n) (width false b) (width true b) (width b b) (prev b) easy
      obtain ⟨b,tail⟩ := ih tailOk w' s' width' next diff non
      have step := bin_step n (s b) g
      change binaryCount (s' b).2 ≤ _ at step
      refine ⟨b,?_⟩
      change binaryCount (elim n gs (s' b)).2 + 2 ≤ _
      simp only [binaryCount,List.countP_cons] at *
      omega

theorem saveTwoBinary (n : Nat) (f : (Fin (n+1) → Bool) → Bool) (C : Circuit)
    (fit : FanInTwo C) (comp : ∀ x, C.eval (List.ofFn x) = f x)
    (depends : ∃ y : Fin n → Bool, f (Fin.snoc y false) ≠ f (Fin.snoc y true))
    (nonconstant : ∀ b, ∃ y z : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc z b)) :
    ∃ (b : Bool) (D : Circuit), FanInTwo D ∧ (∀ y, D.eval (List.ofFn y) = f (Fin.snoc y b)) ∧
      binaryCount D.gates + 2 ≤ binaryCount C.gates ∧ D.gates.countP isNegGate ≤ C.gates.countP isNegGate := by
  obtain ⟨y,dep⟩ := depends
  let gs := C.gates.map normGate
  let w := fun b => List.ofFn y ++ [b]
  let s : Bool → SA := fun b => (initStats n b,[])
  let acc := fun b => elim n gs (s b)
  have ok (g) (mem : g ∈ gs) : NOk g := by
    obtain ⟨old,hm,rfl⟩ := List.mem_map.mp mem
    exact normGate_nok old (fit old hm)
  have val (b : Bool) (z : Fin n → Bool) :
      statVal (wiresFrom (acc b).2 (List.ofFn z)) (statusAt (acc b) C.output) = f (Fin.snoc z b) := by
    have inv := inv_elim n _ (by simp : (List.ofFn z).length = n) gs _ _ (fun k hk => (ok k hk).1) (inv_init n b z)
    rw [((inv.2 C.output).2 : statVal _ _ = _), ←ofFn_snoc, show gs = C.gates.map normGate by rfl,wiresFrom_norm,←comp]
    rfl
  have non (b : Bool) : ¬constantStat (statusAt (acc b) C.output) := by
    rintro ⟨c,hc⟩
    obtain ⟨u,v,ne⟩ := nonconstant b
    apply ne;rw [←val b u,←val b v,hc];rfl
  have ev (b : Bool) : signal (wiresFrom gs (w b)) C.output = f (Fin.snoc y b) := by
    change (wiresFrom (C.gates.map normGate) (List.ofFn y ++ [b])).getD C.output false = _
    rw [wiresFrom_norm,←ofFn_snoc,←comp];rfl
  have start (b : Bool) : tracks (w false) (w true) (s b) (fun i v => v = Sum.inl (signal (w b) i)) := by
    intro i diff
    by_cases last : i = n
    · subst i
      change (initStats n b).getD n _ = Sum.inl ((List.ofFn y ++ [b]).getD n false)
      rw [initStats_last,getD_snoc_len _ _ _ _ (by simp)]
    · exfalso;apply diff
      change (List.ofFn y ++ [false]).getD i _ = (List.ofFn y ++ [true]).getD i _
      rw [getD_snoc_ne _ _ _ _ (by simpa using last),getD_snoc_ne _ _ _ _ (by simpa using last)]
  obtain ⟨b,paid⟩ := beforeFirst n gs C.output ok w s (by simp [s,w,initStats]) start
    (by simpa only [ev] using dep) non
  cases h : statusAt (acc b) C.output with
  | inl c => exact (non b ⟨c,h⟩).elim
  | inr j =>
    refine ⟨b,⟨(acc b).2,j⟩,elim_ok n gs _ (by simp [s]),?_,?_,?_⟩
    · intro z;have e := val b z;rw [h] at e;exact e
    · change binaryCount (acc b).2 + 2 ≤ binaryCount ([] : List Gate) + binaryCount (C.gates.map normGate) at paid
      simpa only [normBinary,binaryCount,List.countP_nil,Nat.zero_add] using paid
    · have h := elim_neg_sub n gs (s b)
      change (acc b).2.countP isNegGate ≤ ([] : List Gate).countP isNegGate + (C.gates.map normGate).countP isNegGate at h
      simpa only [normNeg,List.countP_nil,Nat.zero_add] using h

end Transfer

end PEqualNP.Outside.L_meta_37045

namespace PEqualNP.Outside.L_meta_37045
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4276808424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def witness : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [14, 15]⟩],16⟩

def rows0 : List Signed.W := [((9227875637627191632 : BitVec 64) ++ (18427169592577692022 : BitVec 64)),
   ((4614239980197512749 : BitVec 64) ++ (3413050067107759805 : BitVec 64)),
   ((1927615424504129664 : BitVec 64) ++ (11122622720119402112 : BitVec 64)),
   ((7540249851084015786 : BitVec 64) ++ (16764043637822466475 : BitVec 64)),
   ((1237228921848754695 : BitVec 64) ++ (94522706843826767 : BitVec 64))]
set_option maxRecDepth 32000 in
theorem reject0 : Signed.search 7 rows0 = false := by
  rw [← Signed.searchF_eq]
  decide +kernel
set_option maxRecDepth 32000 in
theorem lower0 (C : Circuit) (fit : FanInTwo C)
    (ev : ∀ x, C.eval (List.ofFn x) = F (Fin.snoc x false)) :
    7 < Signed.binaryCost C.gates :=
  Signed.bound_from_search 7 (fun x => F (Fin.snoc x false))
    rows0 rfl (by decide) reject0 (by decide +kernel) C.gates C.output fit ev

def rows1 : List Signed.W := [((4616189619164151896 : BitVec 64) ++ (18427131659246011486 : BitVec 64)),
   ((2534720450331013 : BitVec 64) ++ (3413072607208827309 : BitVec 64)),
   ((11150994058419171872 : BitVec 64) ++ (15734265582619587488 : BitVec 64)),
   ((2928584998225381922 : BitVec 64) ++ (7540693041582643811 : BitVec 64)),
   ((1237261357503558791 : BitVec 64) ++ (9317885947499591319 : BitVec 64))]
set_option maxRecDepth 32000 in
theorem reject1 : Signed.search 7 rows1 = false := by
  rw [← Signed.searchF_eq]
  decide +kernel
set_option maxRecDepth 32000 in
theorem lower1 (C : Circuit) (fit : FanInTwo C)
    (ev : ∀ x, C.eval (List.ofFn x) = F (Fin.snoc x true)) :
    7 < Signed.binaryCost C.gates :=
  Signed.bound_from_search 7 (fun x => F (Fin.snoc x true))
    rows1 rfl (by decide) reject1 (by decide +kernel) C.gates C.output fit ev

theorem counts (gs : List Gate) : Transfer.binaryCount gs = Signed.binaryCost gs := by
  rw [Transfer.binaryCount, Signed.binaryCost, List.countP_eq_length_filter]
  have e : Transfer.isBinaryGate = Signed.isBinary := by
    funext g
    cases g with | mk op ins => cases op <;> rfl
  rw [e]

theorem bound (C : Circuit) (legal : ∀ g ∈ C.gates, Signed.legal g)
    (eval : ∀ x, C.eval (List.ofFn x) = F x) : 9 < Signed.binaryCost C.gates := by
  have differs : ∃ y : Fin 5 → Bool, F (Fin.snoc y false) ≠ F (Fin.snoc y true) :=
    ⟨(fun k : Fin 5 => Nat.testBit 10 k.val), by decide +kernel⟩
  have nonconstant : ∀ b, ∃ y z : Fin 5 → Bool, F (Fin.snoc y b) ≠ F (Fin.snoc z b) := by
    intro b
    cases b
    · exact ⟨(fun k : Fin 5 => Nat.testBit 0 k.val), (fun k : Fin 5 => Nat.testBit 3 k.val), by decide +kernel⟩
    · exact ⟨(fun k : Fin 5 => Nat.testBit 0 k.val), (fun k : Fin 5 => Nat.testBit 3 k.val), by decide +kernel⟩
  obtain ⟨b,D,fit,ev,save,_⟩ := Transfer.saveTwoBinary 5 F C legal eval differs nonconstant
  rw [counts, counts] at save
  cases b with
  | false => have h := lower0 D fit ev; omega
  | true => have h := lower1 D fit ev; omega

end PEqualNP.Outside.L_meta_37045

open PEqualNP.Outside.L_meta_37045 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 32000 in
theorem PEqualNP.Outside.L_meta_37045 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4276808424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4276808424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  change HasCircuitSize 6 F s at hs
  obtain ⟨C, legal, size, computes⟩ := hs
  by_cases h : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := h
    have short : Signed.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := Signed.isBinary)).mpr
        ⟨g, mem, by simp [Signed.isBinary, op]⟩
    have lb := bound C legal computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, by decide +kernel⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, k⟩ := legal g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.imp_right (fun q => q.resolve_right (fun eq => h ⟨g, mem, eq⟩)),k⟩
