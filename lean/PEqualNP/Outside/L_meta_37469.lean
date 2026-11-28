import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37469

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

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

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
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

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
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
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
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

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
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

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
  Nat.testBit (4008241832 * 2 ^ 32 + 3974684832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x80030a0b2ce02e15#64 ++ 0xdf471e3ffde07e3f#64 : BitVec 128),
   (0x011864d8942d96cc#64 ++ 0x7fb8e7d89e7f9fcc#64 : BitVec 128),
   (0x02c0b160c302c16a#64 ++ 0xefc0f9e0e383e3ff#64 : BitVec 128),
   (0x08ed01bd03f403b0#64 ++ 0x7aff01ff03fc03f0#64 : BitVec 128),
   (0x14f7de0003db7800#64 ++ 0x7dfffe0003fffc00#64 : BitVec 128),
   (0x26fefff6f8000000#64 ++ 0x76fffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x011864d8942d96cc 0x7fb8e7d89e7f9fcc

def z1 : W := mkw 0x02c0b160c302c16a 0xefc0f9e0e383e3ff

def z2 : W := mkw 0x04f6de0000091000 0x7dfffe00027f9c00

def z3 : W := mkw 0x08ed01bd03f403b0 0x7aff01ff03fc03f0

def z4 : W := mkw 0x14f7de0003db7800 0x7dfffe0003fffc00

def z5 : W := mkw 0x26fefff6f8000000 0x76fffffffc000000

def z6 : W := mkw 0x80030a0b2ce02e15 0xdf471e3ffde07e3f

def z7 : W := mkw 0xa6fffffffce02e15 0x76fffffffc601c00

def z8 : W := mkw 0xa20b2bfffce02e15 0xdf471ffffde07e3f

def z9 : W := mkw 0x8001000904e02e15 0x8900000001e07e3f

def z10 : W := mkw 0x94f7de0907fb7e15 0xfdfffe0003fffe3f

def z11 : W := mkw 0x09fd65fd97fd97fc 0x7fffe7ff9fff9ffc

def z12 : W := mkw 0x88ef0bbf2ff42fb5 0xffff1ffffffc7fff

def z13 : W := mkw 0x26eebbf6f8000000 0x024719fffc000000

def z14 : W := mkw 0x811b6edbbcedbedd 0xffffffffffffffff

def z15 : W := mkw 0x00020a0228000000 0x56471e3ffc000000

def z16 : W := mkw 0x0aedb1fdc3f6c3fa 0xfffff9ffe3ffe3ff

def z17 : W := mkw 0x80020a0b2c202e15 0x87001e3ffc007e3f

def z18 : W := mkw 0x27fefff6f80d90c8 0x76fffffffe1f81c0

def z19 : W := mkw 0x26fefff6fb02c16a 0xffffffffff83e3ff

def z20 : W := mkw 0x80020a022c002c05 0xd7471e3ffc007c0f

def z21 : W := mkw 0x010820d8942486cc 0x020001d89c0003cc

def z22 : W := mkw 0x0010440000091000 0x7db8e600027f9c00

def z23 : W := mkw 0x080801bd002403b0 0x020001ff000003f0

def z24 : W := mkw 0x811864dbbc2d96dd 0xffb8e7fffe7f9fff

def z25 : W := mkw 0x0000000000000000 0x6a8001c0020003c0

def z26 : W := mkw 0x0000204080008048 0x6f80e1c0820383cc

def z27 : W := mkw 0x0000204080008048 0xefc0f9e0e383e3ff

def z28 : W := mkw 0x14374e0000d93800 0x103f0600007c1c00

def z29 : W := mkw 0x16f7ff60c3dbf96a 0x7dffffc003fffdc0

def z30 : W := mkw 0x220821f6f8000000 0x020001fffc000000

def z31 : W := mkw 0x8000000904200615 0x800000000000023f

def z32 : W := mkw 0x0000000000008048 0x09000000020383cc

def z33 : W := mkw 0x011864d8942d96cc 0x0700e7d89c039fcc

def z34 : W := mkw 0x82c1b169c7e2ef7f 0xefc0f9e0e3e3ffff

def z35 : W := mkw 0x15fffed897fffecc 0x7fffffd89fffffcc

def z36 : W := mkw 0x243e4e9638000000 0x103f061f1c000000

def z37 : W := mkw 0x82c3bb6befe2ef7f 0xffc7ffffffe3ffff

def z38 : W := mkw 0x1801000903ff7bb0 0x0900000003fffff0

def z39 : W := mkw 0x02c0b160c3024000 0x6fc0f9e0e383e000

def z40 : W := mkw 0x36fefff6fb1b5000 0x76fffffffe1f8000

def z41 : W := mkw 0x011b6ed894edbecc 0x7fffffd89fffffcc

def z42 : W := mkw 0x14f7de022bdb7800 0x7ffffe3ffffffc00

def z43 : W := mkw 0x0825000500d00010 0x0007000700000000

def z44 : W := mkw 0x26fefff6fb000120 0x7effffffff8003f0

def z45 : W := mkw 0x0200b040c002c04a 0x8500f800e003e00f

def z46 : W := mkw 0xa6ffffffffe2ef7f 0xffffffffffe3ffff

def z47 : W := mkw 0x04f6de0000000000 0x74fffe0000000000

def z48 : W := mkw 0x80134e0b2ce93e15 0xfffffe3ffffffe3f

def z49 : W := mkw 0x80030a0328c02811 0x8047182761806033

def z50 : W := mkw 0x1412de00000b7800 0x0500fe000003fc00

def z51 : W := mkw 0x0801000903f403b0 0x0800000003fc03f0

def z52 : W := mkw 0x08ec01b4031401a0 0x20b801c0021c01c0

def z53 : W := mkw 0x16f7ff60c3dbf96a 0xffffffe0e3ffffff

def z54 : W := mkw 0x010820d8942486cc 0x6f80e1d89e0383cc

def z55 : W := mkw 0x011864d8942d96cc 0xfff8fff8ffffffff

def z56 : W := mkw 0x010020409400844c 0x000000009c00000c

def z57 : W := mkw 0x15fcf4d8973fd6cc 0x7fb8e7d89e7f9fcc

def z58 : W := mkw 0x02c8b1f8c326c3ea 0xfff8f9f8e3ffe3ff

def z59 : W := mkw 0x94f7de0b2ffb7e15 0xfffffe3ffffffe3f

def z60 : W := mkw 0x14e79a0003d26800 0x0047180001806000

def z61 : W := mkw 0x26fefff6f8000000 0x20fff9e760000000

def z62 : W := mkw 0x00020a0228000000 0xdf471e3ffd80623f

def z63 : W := mkw 0x00020a0228000000 0x1007061f1c000000

def z64 : W := mkw 0x080901bd00e403b0 0x5a4701ff01e003f0

def z65 : W := mkw 0x00ed009803f40280 0x7aff01d803fc03c0

def z66 : W := mkw 0x0200b160c002c16a 0x8700f9e0e003e3ff

def z67 : W := mkw 0x80e70a0b2ff02e15 0xffff1e3ffffc7e3f

def z68 : W := mkw 0x0000000004000404 0x050006009c001c0c

def z69 : W := mkw 0x0010440000000000 0x74b8e60000000000

def z70 : W := mkw 0x0000000804200604 0x5f0006189c601e0c

def z71 : W := mkw 0x26fedfb678000000 0x107f1e3f7c000000

def z72 : W := mkw 0x95fffedbbffffedd 0xffffffffffffffff

def z73 : W := mkw 0x00134e0000c93800 0x7dfffe0003fffc00

def z74 : W := mkw 0x8000000b2c200615 0x8200003ffc00023f

def z75 : W := mkw 0x01184498142d1684 0x103806181c7c1c00

def z76 : W := mkw 0x02c0912043024122 0x8040182061806033

def z77 : W := mkw 0x1cffdfbd03ff7bb0 0x7fffffff03fffff0

def z78 : W := mkw 0x80020a022c002c05 0x85001e00fc007c0f

def z79 : W := mkw 0x26fefff6f8000000 0x30bfe7df1c000000

def z80 : W := mkw 0x01000008072fd7ee 0x8900000003ffffff

def z81 : W := mkw 0x1412de00000b7800 0x7db8fe00027ffc00

def z82 : W := mkw 0x08fd45bd03fd13b0 0x7fffe7ff03ff9ff0

def z83 : W := mkw 0x82c3bb63ebc2e97b 0xefc7f9e7e383e3ff

def z84 : W := mkw 0x080801b4000401a0 0x000001c0000001c0

def z85 : W := mkw 0x00030a0b28e00210 0x5e471e3ffde00230

def z86 : W := mkw 0x16f7ff60c3db7800 0x7fffffe0e3fffc00

def z87 : W := mkw 0x00e4000000000000 0x70ff000000000000

def z88 : W := mkw 0x02c0912043024122 0x0000000000000000

def z89 : W := mkw 0x0000204080008048 0x020001c0800003cc

def z90 : W := mkw 0x02002160c000816a 0xef80e1e0e20383ff

def z91 : W := mkw 0x800b0a9b2ce42e95 0xffff1ffffffc7fff

def z92 : W := mkw 0x81126e42bc09bc4d 0x8500fe00fc03fc0f

def z93 : W := mkw 0x8001000904e02e15 0x0000000000601c00

def z94 : W := mkw 0x94f7de032bdb7811 0xfdfffe2763fffc33

def z95 : W := mkw 0x26f6fe42f8000000 0x74fffe00fc000000

def z96 : W := mkw 0x80030a0b2ce02e15 0x8d001e00fde07e3f

def z97 : W := mkw 0x001864d090000000 0x76b8e7d89c000000

def z98 : W := mkw 0x220821f4d0000000 0x000001c000000000

def z99 : W := mkw 0x80030a022cc02c05 0xdd471e00fde07c0f

def z100 : W := mkw 0x011a6edabc2d96cc 0x7ffffffffe7f9fcc

def z101 : W := mkw 0x00ec01b400000000 0x72ff01ff00000000

def z102 : W := mkw 0x09fc65fc973d97ec 0x7fb8e7d89e7f9fcc

def z103 : W := mkw 0x88ed01bf2ff407b5 0xfaff01fffffc03ff

def z104 : W := mkw 0x14f5d40003db7800 0x29b8e00003fffc00

def z105 : W := mkw 0x011064409409944c 0x0500e6009c039c0c

def z106 : W := mkw 0xa43f4e9f3ce02e15 0xdf7f1e3ffde07e3f

def z107 : W := mkw 0x03d8f5f0d30fd1ea 0xeff8f9e0e39fe3ff

def z108 : W := mkw 0x02002160c000816a 0x000001c0000001c0

def z109 : W := mkw 0x000020488420864c 0x7f80e7d89e639fcc

def z110 : W := mkw 0x2612fe42f8000000 0x0400fe00fc000000

def z111 : W := mkw 0xa6fefff6fc002c05 0xf7fffffffc007c0f

def z112 : W := mkw 0x16f4f560c31bd16a 0xeff8f9e0e39fe3ff

def z113 : W := mkw 0x02002160c000816a 0x820001e0e00003ff

def z114 : W := mkw 0x24fede9638000000 0x74fffe1f1c000000

def z115 : W := mkw 0x26fffffff8e00210 0x7efffffffde00230

def z116 : W := mkw 0x011064409409944c 0x7db8e6009e7f9c0c

def z117 : W := mkw 0x2efffffffbf403b0 0x7efffffffffc03f0

def z118 : W := mkw 0x00c0012003000120 0x6ac001e0038003f0

def z119 : W := mkw 0x36fffff6fbdb7800 0x7ffffffffffffc00

def z120 : W := mkw 0x011864d8942486cc 0x76b8e7d89c0003cc

def z121 : W := mkw 0x02c3bb60c3c2e96a 0xffc7ffe0e3e3ffff

def z122 : W := mkw 0x01d865f8972d97ec 0x7ff8e7f89fff9ffc

def z123 : W := mkw 0x00c0012000000000 0x62c001e000000000

def z124 : W := mkw 0x80030a0b2ce02e15 0x5d471e1f1de07c00

def z125 : W := mkw 0x0001000900e00210 0x5a47003f01e00230

def z126 : W := mkw 0x02c2bb62e8000000 0x76c7fffffc000000

def z127 : W := mkw 0x8801000907f42fb5 0x8900000003fc7fff

def z128 : W := mkw 0x22c8b1f6fb02c16a 0xefc0f9ffff83e3ff

def z129 : W := mkw 0x14f7de0003db7800 0x107f1e0001fc7c00

def z130 : W := mkw 0xa6e79b2f6ce02e15 0xdf471e3ffde07e3f

def z131 : W := mkw 0x001a6ed2b8000000 0x76fffffffc000000

def z132 : W := mkw 0x02c0b160c3000120 0x6ec0f9e0e38003f0

def z133 : W := mkw 0x26fefff6f8000000 0x24b8ffc0fc000000

def z134 : W := mkw 0x0008009800240280 0x7ab801d8027c03c0

def z135 : W := mkw 0x0a0821fdc02483fa 0x820001ffe00003ff

def z136 : W := mkw 0x01d8f4d8972fd6cc 0x7ff8ffd89fffffcc

def z137 : W := mkw 0x00030a0228c02800 0x5f471e3ffde07c00

def z138 : W := mkw 0x1001000003db7800 0x0900000003fffc00

def z139 : W := mkw 0x811b4e9b3ced3e95 0xdf7f1e3ffdfc7e3f

def z140 : W := mkw 0x14029a0000026800 0x0000180000006000

def z141 : W := mkw 0x0000000000000000 0x0000000000000000

def z142 : W := mkw 0x093d64dd94fd96dc 0x7fbfe7df9e7f9fcc

def z143 : W := mkw 0x1efffffdc3fffbfa 0xffffffffe3ffffff

def z144 : W := mkw 0x0000900000024000 0x0500f8000003e000

def z145 : W := mkw 0x08ed01bd07f407b4 0x7fff07ff9ffc1ffc

def z146 : W := mkw 0x94f7de022fdb7c05 0xfdfffe00fffffc0f

def z147 : W := mkw 0x05fefed8942d96cc 0x7fffffd89e7f9fcc

def z148 : W := mkw 0xa612fe42fc002c05 0x8500fe00fc007c0f

def z149 : W := mkw 0x02c0b160c0000000 0x66c0f9e0e0000000

def z150 : W := mkw 0x14f4d400031b5000 0x20b8e000021f8000

def z151 : W := mkw 0x27fefffefc2d96cc 0x7ffffffffe7f9fcc

def z152 : W := mkw 0x10c1900003db7800 0x6dc0f80003fffc00

def z153 : W := mkw 0x1cf7df2503db7930 0x7dfffe2703fffc30

def z154 : W := mkw 0x1434440000191000 0x00380000001c0000

def z155 : W := mkw 0x00e5000003d00000 0x78ff000003fc0000

def z156 : W := mkw 0x8001000b2ce02e15 0x8b00003ffde07e3f

def z157 : W := mkw 0x80020a0a2c202e05 0xdf001e18fc607e0f

def z158 : W := mkw 0x02c0b160c302c16a 0x6f80e1c0820383cc

def z159 : W := mkw 0x82c2bb62ef02ed6f 0xefc0ffe0ff83ffff

def z160 : W := mkw 0x0aecb1f4c316c1ea 0xeff8f9e0e39fe3ff

def z161 : W := mkw 0x030821f8d42487ee 0x820001f8fc0003ff

def z162 : W := mkw 0x16e7bb60c3d2e96a 0xefc7f9e0e383e3ff

def z163 : W := mkw 0x08ec01b4031401a0 0x72ff01ff021c01c0

def z164 : W := mkw 0x0200b040c002c04a 0x0000e00000038000

def z165 : W := mkw 0x2612fe42f802c04a 0x8500fe00fc03e00f

def z166 : W := mkw 0x14f5d40003db5000 0x78ffe00003ff8000

def z167 : W := mkw 0x0000204080008048 0x2080e1c0020381c0

def z168 : W := mkw 0x80030a0328c02811 0xcf471827e180623f

def z169 : W := mkw 0x26fefff6f8091000 0x7ffffffffe7f9c00

def z170 : W := mkw 0x1001000000d93800 0x00000000007c1c00

def z171 : W := mkw 0x8001000904e02e15 0xcf401820e1e07e3f

def z172 : W := mkw 0x26d2ff62fb02c16a 0xefc0ffe0ff83e3ff

def z173 : W := mkw 0x03d8f5f8d72fd7ee 0xfff8fff8ffffffff

def z174 : W := mkw 0x00c001200302c16a 0xebc001e00383e3ff

def z175 : W := mkw 0x00c0900003024000 0x6dc0f8000383e000

def z176 : W := mkw 0x02c0b168c722c76e 0xffc0fff8ffe3ffff

def z177 : W := mkw 0x02c0b040c302c04a 0xedc0f800e383e00f

def z178 : W := mkw 0x1cef9bbd03f66bb0 0x7aff19ff03fc63f0

def z179 : W := mkw 0x0000000000000000 0xcf401820e180623f

def z180 : W := mkw 0x09fd65fd93fd93f8 0x7affe1ff03ff83f0

def z181 : W := mkw 0x02c0b160c0000000 0xefc0f9e0e180623f

def z182 : W := mkw 0x000000000302c16a 0x890000000383e3ff

def z183 : W := mkw 0x221865f6f8000000 0x76b8e7fffc000000

def z184 : W := mkw 0x0000000003000120 0x08000000038003f0

def z185 : W := mkw 0x082d01bd00f403b0 0x123f01ff007c03f0

def z186 : W := mkw 0x00020a0000000000 0x54471e0000000000

def z187 : W := mkw 0x08e5012503d00130 0x0047002701800030

def z188 : W := mkw 0x253e6edebc2d96cc 0x7fbfe7df9e7f9fcc

def z189 : W := mkw 0x14f7de0003db7800 0xfffffe20e3fffe3f

def z190 : W := mkw 0x08ec01b4031401a0 0x6af801e0039c03f0

def z191 : W := mkw 0x2efdf5fdd3f403b0 0x7affe1ff03fc03f0

def z192 : W := mkw 0x14f7de0003d26800 0x74fffe0001806000

def z193 : W := mkw 0x26e69b2668000000 0x0047182760000000

def z194 : W := mkw 0x36f7df266bdb7800 0x7dfffe2763fffc00

def z195 : W := mkw 0x14e79a0003d26800 0x5d471e0001e07c00

def z196 : W := mkw 0x00030a0000c02800 0x5d471e0001e07c00

def z197 : W := mkw 0x00ee0bb628000000 0x76ff1ffffc000000

def z198 : W := mkw 0x14f7df2003db7920 0x7fffffe003fffff0

def z199 : W := mkw 0x80030a0b2ce02e15 0x5a47063f1de01e30

def z200 : W := mkw 0x011864d8942d96cc 0x29b8e1c0027f9fcc

def z201 : W := mkw 0x80030a0b2ce02e15 0x95071e1ffc607c0f

def z202 : W := mkw 0x1cfcd5b4031f51a0 0x20b8e1c0021f81c0

def z203 : W := mkw 0x80030a0904e02e15 0xdd471e0001e07e3f

def z204 : W := mkw 0x08ed01bd03f6c3fa 0xfbff01ff03ffe3ff

def z205 : W := mkw 0x80030a0b2ce02e15 0x1007061f1c601c00

def z206 : W := mkw 0x2ee79b276bd00130 0x0047182761800030

def z207 : W := mkw 0x0000000804200604 0x020000189c00020c

def z208 : W := mkw 0x011864d0900d90c8 0x6fb8e1c0821f83cc

def z209 : W := mkw 0x80c39a0b2fe26e15 0xffc7fe3fffe3fe3f

def z210 : W := mkw 0xa6fffffffce02e15 0xfffffffffde07e3f

def z211 : W := mkw 0x0000000003024122 0x8000000001806033

def z212 : W := mkw 0x0aedb1fdc3f403b0 0x7efff9ffe3fc03f0

def z213 : W := mkw 0x8203ba4bece2ee5f 0xdf47fe3ffde3fe3f

def z214 : W := mkw 0x091865fd942d97fc 0x7fb8e7ff9e7f9ffc

def z215 : W := mkw 0x12c1b160c3dbf96a 0xefc0f9e0e3ffffff

def z216 : W := mkw 0x80030a0b2ce02e15 0x8247183ffd80623f

def z217 : W := mkw 0x14f6de00000b7800 0x75fffe000003fc00

def z218 : W := mkw 0x26e6bb66eb02c16a 0xefc7f9e7e383e3ff

def z219 : W := mkw 0x83dbfffbffefffff 0xffffffffffffffff

def z220 : W := mkw 0x09ed21fd97f487fc 0x7aff01ff9ffc03fc

def z221 : W := mkw 0x0901000907fd97fc 0x0900000003ff9ffc

def z222 : W := mkw 0x00020a0a2c200604 0x5f471e3ffc601e0c

def z223 : W := mkw 0x08ed01bd03f403b0 0xffff19ffe3fc63ff

def z224 : W := mkw 0x0000000000091000 0x09000000027f9c00

def z225 : W := mkw 0x011864d0900d90c8 0x20b8e1c0021f81c0

def z226 : W := mkw 0x8aefbbffeff6efff 0xffffffffffffffff

def z227 : W := mkw 0x04f6de0003024000 0x7dfffe000383e000

def z228 : W := mkw 0xa6fefffffc200615 0xf6fffffffc00023f

def z229 : W := mkw 0x08ed01bd03f403b0 0x024701ff018003f0

def z230 : W := mkw 0x36fffff6f8d93800 0x76fffffffc7c1c00

def z231 : W := mkw 0x0809009903f403b0 0x7ab801d803fc03f0

def z232 : W := mkw 0x8000000328000011 0x8000002760000033

def z233 : W := mkw 0x26fefff6f802c04a 0xf7fffffffc03e00f

def z234 : W := mkw 0x2efcf5f4d31401a0 0x20b8e1c0021c01c0

def z235 : W := mkw 0x90030a0b2ffb7e15 0xdf471e3ffffffe3f

def z236 : W := mkw 0x0000000804200604 0xdf401e38fde07e3f

def z237 : W := mkw 0x14270a0000d02800 0x0007000000000000

def z238 : W := mkw 0x26fefff6fb024122 0xf6fffffffd806033

def z239 : W := mkw 0x14f4d400031b5000 0x7db8e600027f9c00

def z240 : W := mkw 0x15f7fe4097dbfc4c 0x7dfffe009ffffc0c

def z241 : W := mkw 0x80020a022c002c05 0x000006001c001c00

def z242 : W := mkw 0x0010644080099048 0x7fb8e7c0827f9fcc

def z243 : W := mkw 0x36f7fe42fbdb7800 0x7dfffe00fffffc00

def z244 : W := mkw 0x8001000904e02e15 0xdb47003f01e07e3f

def z245 : W := mkw 0x082d009d00f40290 0x5a7f003f01fc0230

def z246 : W := mkw 0x08ed01bd03f403b0 0x107f003f01fc0030

def z247 : W := mkw 0x26029a0268000000 0x0000180060000000

def z248 : W := mkw 0x082d009d00f40290 0x103f001f007c0000

def z249 : W := mkw 0x14f7de0000d93800 0x74fffe00007c1c00

def z250 : W := mkw 0x15ffde9817ff7e84 0x7dfffe181ffffc00

def z251 : W := mkw 0x153f6ed894fdbecc 0x7fbfe7d89e7f9fcc

def z252 : W := mkw 0x1ce79b2503d26930 0x0047182701806030

def z253 : W := mkw 0x04f7de0000c02800 0x7dfffe0001e07c00

def z254 : W := mkw 0x01000008042d96cc 0x09000000027f9fcc

def z255 : W := mkw 0x81030a0b2cedbedd 0xdf471e3fffffffff

def z256 : W := mkw 0x94f7de0b2ffb7e15 0x7dfffe1f1ffffc00

def z257 : W := mkw 0x14ffdfb403db7800 0x7fffffff03fffc00

def z258 : W := mkw 0x04f7de0003d00000 0x7cfffe0003fc0000

def z259 : W := mkw 0x010820d8942d96cc 0x0b0001d89e7f9fcc

def z260 : W := mkw 0x08ed91bd03f643b0 0x7ffff9ff03ffe3f0

def z261 : W := mkw 0x82c0b16bef22c77f 0xefc0f9ffff83e3ff

def z262 : W := mkw 0x01000008042486cc 0x00000000000003cc

def z263 : W := mkw 0x001864d894200604 0x7fb8e7d89c601e0c

def z264 : W := mkw 0x00fc65f490000000 0x76ffe7ff9c000000

def z265 : W := mkw 0x882f0a9f2cf42e95 0xdf7f1e3ffdfc7e3f

def z266 : W := mkw 0x0000000000000000 0x890000000180623f

def z267 : W := mkw 0x26fcf5f4d0000000 0x66f8f9e0e0000000

def z268 : W := mkw 0x36e79b266bd26800 0x0047182761806000

def z269 : W := mkw 0x26fcf5f4d0000000 0x20b8e1c000000000

def z270 : W := mkw 0x0010440000091000 0x10380600007c1c00

def z271 : W := mkw 0x00020a0228000000 0x0047182760000000

def z272 : W := mkw 0x00c0012003000120 0x208001c0020001c0

def z273 : W := mkw 0x02ecb1f4c0000000 0x76fff9ffe0000000

def z274 : W := mkw 0x0800012500000130 0x0000002700000030

def z275 : W := mkw 0x80030a0b2ce02e15 0x9207063ffc601e3f

def z276 : W := mkw 0x02c0b160c302c16a 0x8540f820e183e03f

def z277 : W := mkw 0x02c0912043024122 0xcf401820e180623f

def z278 : W := mkw 0x0000000000000000 0x5247003f00000000

def z279 : W := mkw 0x0000000000000000 0x78b80000027c0000

def z280 : W := mkw 0x243e4e9638000000 0x567f1e3ffc000000

def z281 : W := mkw 0x0318f4d8d42fd6ce 0xffb8ffd8fe7fffcf

def z282 : W := mkw 0x0001000900e00210 0x0800000001e00230

def z283 : W := mkw 0x0000000000000000 0x8040182061806033

def z284 : W := mkw 0x82c3bb6bece02e15 0xffc7fffffde07e3f

def z285 : W := mkw 0x1612fe40c00bf84a 0x8500fe00e003fc0f

def z286 : W := mkw 0x2efffffffbf6c3fa 0xffffffffffffe3ff

def z287 : W := mkw 0x01184498142d1684 0x7ab807d81e7c1fc0

def z288 : W := mkw 0x243c449410000000 0x0038000000000000

def z289 : W := mkw 0x16d2ff60c30bf96a 0xefc0ffe0e383ffff

def z290 : W := mkw 0x27fcf5f4d00d90c8 0x20b8e1c0021f81c0

def z291 : W := mkw 0x01184498142d96cc 0x193806181e7f9fcc

def z292 : W := mkw 0x8000000004002c05 0x8100000000007c0f

def z293 : W := mkw 0x02002160c000816a 0xcf4019e0e18063ff

def z294 : W := mkw 0x22002042f8000000 0x00000000fc000000

def z295 : W := mkw 0xa43f4e9f3ce02e15 0x103f061f1c601c00

def z296 : W := mkw 0x36fcf5f4d31b5000 0x20b8e1c0021f8000

def z297 : W := mkw 0x80030a0328c02811 0xd6471e3ffd806033

def z298 : W := mkw 0x14374e0000d93800 0x7dbfe600027f9c00

def z299 : W := mkw 0x26fefff6f8000000 0xfffffffffd80623f

def z300 : W := mkw 0x02c0912043024122 0xedc0f8206383e033

def z301 : W := mkw 0x14124e0000093800 0x0000060000001c00

def z302 : W := mkw 0x011064489429964c 0x5f00e6189c639e0c

def z303 : W := mkw 0x02c0b160c302c16a 0xa280e1e0e20383ff

def z304 : W := mkw 0x001864d090000000 0x20b8e1c000000000

def z305 : W := mkw 0x810820dbbc2486dd 0x820001fffc0003ff

def z306 : W := mkw 0x8101000904edbedd 0x8900000003ffffff

def z307 : W := mkw 0x010820d8942486cc 0x7ab801d89e7c03cc

def z308 : W := mkw 0x14f7fe4083dbf848 0x7fffffc083ffffcc

def z309 : W := mkw 0x0aedb1fdc3f6c3fa 0x7affe1ff03ff83f0

def z310 : W := mkw 0x09fd45bd17fd17b4 0x7aff07ff1ffc1ff0

def z311 : W := mkw 0x0001000000c02800 0x0900000001e07c00

def z312 : W := mkw 0x231865fefc2d96cc 0x7fb8e7fffe7f9fcc

def z313 : W := mkw 0x03d8f5f0d30fd1ea 0x20b8e1c0021f81c0

def z314 : W := mkw 0x26fefff6f8008048 0x7ffffffffe0383cc

def z315 : W := mkw 0x090821fd942487fc 0x020001ff9c0003fc

def z316 : W := mkw 0x27fefffeff2fd7ee 0xffffffffffffffff

def z317 : W := mkw 0x1437de0000db7800 0x153ffe00007ffc00

def z318 : W := mkw 0x08c801bd032403b0 0x6ac001ff038003f0

def z319 : W := mkw 0x001864d890240280 0x7eb8e7d89e7c03c0

def z320 : W := mkw 0x093d449d14fd1694 0x103f061f1c7c1c00

def z321 : W := mkw 0x0801000900f40290 0x00000000007c0000

def z322 : W := mkw 0x14ffde9803ff7a80 0x7fffffd803ffffc0

def z323 : W := mkw 0x09fc65f4931d91e8 0x20b8e1c0021f81c0

def z324 : W := mkw 0x03d0f560d70bd56e 0xefc0ffe0ff83ffff

def z325 : W := mkw 0x082d009d03f403b0 0x183f001f03fc03f0

def z326 : W := mkw 0x1101000807fffecc 0x0900000003ffffcc

def z327 : W := mkw 0x00c0912003024120 0x6fc0f9e00383e3f0

def z328 : W := mkw 0x011864d09409944c 0x77b8e7d89c039c0c

def z329 : W := mkw 0x0200b040c002c04a 0xcf40f820e183e23f

def z330 : W := mkw 0x2efefff6fb1401a0 0x76fffffffe1c01c0

def z331 : W := mkw 0x84f7de0b2ce02e15 0xfffffe3ffde07e3f

def z332 : W := mkw 0x0aecb1f4c316c1ea 0x20b8e1c0021f81c0

def z333 : W := mkw 0x0000000003024000 0x090000000383e000

def z334 : W := mkw 0x8001000907e2ef7f 0x8900000003e3ffff

def z335 : W := mkw 0x08c1012903f403b0 0x6ac001e003fc03f0

def z336 : W := mkw 0x1cffdfb403df79a0 0x7dffffc003fffdc0

def z337 : W := mkw 0x00ec01bc00240280 0x7aff01ff027c03c0

def z338 : W := mkw 0x1011440003db7800 0x7db8e60003fffc00

def z339 : W := mkw 0x01fd64d897fd96cc 0x7fffe7d89fff9fcc

def z340 : W := mkw 0x0000000000000000 0x5d00060000601c00

def z341 : W := mkw 0x24fe4fb638000000 0x72ff07ff1c000000

def z342 : W := mkw 0x26fefff6fb024000 0x7fffffffff83e000

def z343 : W := mkw 0x01fc65fc942d96cc 0x7fffe7ff9e7f9fcc

def z344 : W := mkw 0x00f5440003d91000 0x7dffe60003ff9c00

def z345 : W := mkw 0x0110644090099048 0x0000e00000038000

def z346 : W := mkw 0x811a6edabc2dbecd 0xffb8ffd8fe7fffcf

def z347 : W := mkw 0x27fefffefc2486cc 0x76fffffffc0003cc

def z348 : W := mkw 0x0001000003d00000 0x0800000003fc0000

def z349 : W := mkw 0x16f7df2043db7922 0xfdfffe2063fffc33

def z350 : W := mkw 0x26f6df2668000000 0x74fffe2760000000

def z351 : W := mkw 0x14e4900003124000 0x0000000000000000

def z352 : W := mkw 0x00e5900003d24000 0x7dfff80003ffe000

def z353 : W := mkw 0x00c0012003000120 0x0040002001800030

def z354 : W := mkw 0x00c0900003024000 0x0040180001806000

def z355 : W := mkw 0x00030a0000c02800 0xdf471e20e1e07e3f

def z356 : W := mkw 0x88e70b272bd02931 0x8047182761806033

def z357 : W := mkw 0x0010440804291604 0x7fb8e6189e7f9e0c

def z358 : W := mkw 0x26fcf5f4d302c16a 0x20b8e1c0020381c0

def z359 : W := mkw 0x02c0b160c3024122 0xe6c0f9e0e1806033

def z360 : W := mkw 0x0ac1b169c3f6c3fa 0xefc0f9e0e3ffe3ff

def z361 : W := mkw 0x0000000000000000 0x6d80e00002038000

def z362 : W := mkw 0x000820d090000000 0x020001d89c000000

def z363 : W := mkw 0x02c0b160c302c16a 0x6dc0f9c00383e1c0

def z364 : W := mkw 0x2612fe42f8000000 0x5647fe3ffc000000

def z365 : W := mkw 0x26fefffef8240280 0x7efffffffe7c03c0

def z366 : W := mkw 0x082c009400140080 0x00380000001c0000

def z367 : W := mkw 0x010820d8942486cc 0x5f0007d89c601fcc

def z368 : W := mkw 0x011864d8942d96cc 0x30b8e7d81e7f9dc0

def z369 : W := mkw 0x04f4d40000000000 0x20b8e00000000000

def z370 : W := mkw 0x811b6edbbcedbedd 0x7fbfe7df9e7f9fcc

def z371 : W := mkw 0x04f6de0228000000 0x76fffe3ffc000000

def z372 : W := mkw 0x26fcf5f4d0000000 0x72ffe1ff00000000

def z373 : W := mkw 0x0001000900e00210 0x1007001f00600000

def z374 : W := mkw 0x01002048842d96cc 0x6f80e1c0827f9fcc

def z375 : W := mkw 0x80032a4bace0ae5d 0xffc7ffffffe3ffff

def z376 : W := mkw 0x801b6edbbce02e15 0xfffffffffde07e3f

def z377 : W := mkw 0x02c02160c300816a 0xeac001e0e38003ff

def z378 : W := mkw 0x011864d0900d90c8 0x76b8e7d89e1f81c0

def z379 : W := mkw 0x00c0900000000000 0x64c0f80000000000

def z380 : W := mkw 0x0008009800240280 0x10380018007c0000

def z381 : W := mkw 0x36fefff6f80b7800 0x77fffffffc03fc00

def z382 : W := mkw 0x1cfdd5bd03ff53b0 0x7affe1ff03ff83f0

def z383 : W := mkw 0x011064409409944c 0x6f80e7c09e039fcc

def z384 : W := mkw 0x0000000804200604 0x0900000000601e0c

def z385 : W := mkw 0x36fffff6fbdbf96a 0xffffffffffffffff

def z386 : W := mkw 0x261afff6f8000000 0x0600fffffc000000

def z387 : W := mkw 0x0018449010000000 0x103806181c000000

def z388 : W := mkw 0x00d0d400030b5000 0x7df8fe0003fffc00

def z389 : W := mkw 0x80030a0328c02811 0xdd471e2761e07c33

def z390 : W := mkw 0x0001000904e00614 0x5f47063f9de01e3c

def z391 : W := mkw 0x15fcf4d0931fd0c8 0x20b8e1c0021f81c0

def z392 : W := mkw 0x0000000000000000 0x4f0000008000020c

def z393 : W := mkw 0x011864d8972fd7ee 0xffb8e7d89fffffff

def z394 : W := mkw 0x00c39a0003c26800 0x7dc7fe0003e3fc00

def z395 : W := mkw 0x9001000907fb7e15 0x8900000003fffe3f

def z396 : W := mkw 0x0aed91bd43f643b2 0xfaff19ff63fc63f3

def z397 : W := mkw 0x02c0912043024122 0xeac019e0638063f3

def z398 : W := mkw 0x0010440000091000 0x20b8e000021f8000

def z399 : W := mkw 0x06f6ff60c0000000 0x76ffffe0e0000000

def z400 : W := mkw 0x082d009d00f40290 0x7abf01df027c03c0

def z401 : W := mkw 0x00ec01b400000000 0x20b801c000000000

def z402 : W := mkw 0x81136e4bbce9be5d 0xdf47fe3ffde3fe3f

def z403 : W := mkw 0x011864d8942d96cc 0x123807d89c7c1fcc

def z404 : W := mkw 0x01104408042d96cc 0x7db8e600027f9fcc

def z405 : W := mkw 0x08ec01bd033403b0 0x22b801ff021c03f0

def z406 : W := mkw 0x08ed01b503d401b0 0x20ff01e7039c01f0

def z407 : W := mkw 0x0000000000000000 0x46401820e0000000

def z408 : W := mkw 0x34ffde963bdb7800 0x7dfffe1f1ffffc00

def z409 : W := mkw 0x2efefffff82403b0 0x76fffffffc0003f0

def z410 : W := mkw 0x010820d0900480c8 0x000001c0000001c0

def z411 : W := mkw 0x15fffed093dff8c8 0x7dffffc003fffdc0

def z412 : W := mkw 0x00ec01b403000120 0x7aff01ff038003f0

def z413 : W := mkw 0x02c0b160c302c16a 0x2080e1c0020381c0

def z414 : W := mkw 0x02ecb1f4c302c16a 0xfffff9ffe383e3ff

def z415 : W := mkw 0x80030a0328c02811 0x0007000700000000

def z416 : W := mkw 0x02c091204302c16a 0x894018206383e3ff

def z417 : W := mkw 0x26fcf5f4d0000000 0x76b8e7d89c000000

def z418 : W := mkw 0x04364e0000000000 0x103f060000000000

def z419 : W := mkw 0x811b4e9b3ced3e95 0x103f061f1c7c1c00

def z420 : W := mkw 0x0200b040c302c16a 0x8d00f800e383e3ff

def z421 : W := mkw 0x17fffff8d7ffffee 0xfffffff8ffffffff

def z422 : W := mkw 0x0008009804240684 0x7fb807d89e7c1fcc

def z423 : W := mkw 0x00c090000302c16a 0xedc0f8000383e3ff

def z424 : W := mkw 0x1001000003d26800 0x0000000001806000

def z425 : W := mkw 0x08e5012d03f403b0 0x0847002703fc03f0

def z426 : W := mkw 0x882f0a9f2cf42e95 0x103f061f1c7c1c00

def z427 : W := mkw 0x002c009400000000 0x103f001f00000000

def z428 : W := mkw 0x810b2adbbce4aedd 0xdf471ffffde07fff

def z429 : W := mkw 0x1413de0000cb7800 0x5d47fe0001e3fc00

def z430 : W := mkw 0x02e5b160c3d2c16a 0xfffff9e0e3ffe3ff

def z431 : W := mkw 0x14f7de0003db7800 0x0547fe000183fc00

def z432 : W := mkw 0x0001000100c00010 0x0047002701800030

def z433 : W := mkw 0x0000000800240280 0x08000000027c03c0

def z434 : W := mkw 0xa6e79b2768c02811 0x8047182761806033

def z435 : W := mkw 0x80030a0b2ce02e15 0x8947182761e07e3f

def z436 : W := mkw 0x02c0b160c302c16a 0xa980e1c00383e3ff

def z437 : W := mkw 0x10000000000b7800 0x010000000003fc00

def z438 : W := mkw 0x000000000302c16a 0xcf401820e383e3ff

def z439 : W := mkw 0x000801b400000000 0x020001ff00000000

def z440 : W := mkw 0x0801000103d00130 0x0000000001800030

def z441 : W := mkw 0x16f7fe40c3dbf84a 0xfdfffe00e3fffc0f

def z442 : W := mkw 0x0010440000091000 0x0500e60000039c00

def z443 : W := mkw 0x0aed21fdc3f483fa 0xfaff01ffe3fc03ff

def z444 : W := mkw 0x0008009000040080 0x20b801c0021c01c0

def z445 : W := mkw 0x0009009900e40290 0x7aff01ff03fc03f0

def z446 : W := mkw 0x94374e0b2cf93e15 0xdf7f1e3ffdfc7e3f

def z447 : W := mkw 0x14e79a0003d26800 0x78ff180003fc6000

def z448 : W := mkw 0x26fefff6f800816a 0xf6fffffffc0003ff

def z449 : W := mkw 0x02d8f5f0d0000000 0x76f8fff8fc000000

def z450 : W := mkw 0x8000000b2c200615 0xcf40183ffd80623f

def z451 : W := mkw 0x011964d994ed96dc 0x7fffe7ff9fff9ffc

def z452 : W := mkw 0x02c0b160c302c16a 0x824019e0e18063ff

def z453 : W := mkw 0x811964d994edbedd 0xffb8e7d89fffffff

def z454 : W := mkw 0x0000204080000000 0x6680e1c080000000

def z455 : W := mkw 0x2ffffffffffd97fc 0x7fffffffffff9ffc

def z456 : W := mkw 0x09ed01bd07fd97fc 0x7bff01ff03ff9ffc

def z457 : W := mkw 0x2efffffff8f40290 0x76fffffffc7c0000

def z458 : W := mkw 0x0000204080008048 0x0500e0008003800c

def z459 : W := mkw 0x26e69b2668000000 0x56471e3ffc000000

def z460 : W := mkw 0x343f4e9638d93800 0x103f061f1c7c1c00

def z461 : W := mkw 0x26fffff6f8c02800 0x7ffffffffde07c00

def z462 : W := mkw 0x271afedafc2d96cc 0x7fb8ffd8fe7f9fcc

def z463 : W := mkw 0x08ef0bbf2bf403b0 0x7eff1ffffffc03f0

def z464 : W := mkw 0x26e69b266b024122 0x8047182761806033

def z465 : W := mkw 0x08ed01bd03f403b0 0x30bf01df027c01c0

def z466 : W := mkw 0x80030a0b2ce02e15 0x9907061f1de07e3f

def z467 : W := mkw 0x0808009d00240290 0x0000001f00000000

def z468 : W := mkw 0x0310f440d40bd44e 0x8500fe00fc03fc0f

def z469 : W := mkw 0x08e5012503d00130 0x78ff002703fc0030

def z470 : W := mkw 0x8000000b2c200615 0xdf00063ffc601e3f

def z471 : W := mkw 0x04fefed090000000 0x76ffffd89c000000

def z472 : W := mkw 0x08ec01bc033403a0 0x7ab801d8027c03c0

def z473 : W := mkw 0x8001000100c02811 0x8000000001806033

def z474 : W := mkw 0x001864d090008048 0x7fb8e7d89e0383cc

def z475 : W := mkw 0x08ed01b403d401a0 0x78ff01c003fc01c0

def z476 : W := mkw 0x02c0b160c302c16a 0xa0c0f9e06383e1f3

def z477 : W := mkw 0xa6fffff7f8c02811 0xf6fffffffd806033

def z478 : W := mkw 0xa7fffffffcedbedd 0xffffffffffffffff

def z479 : W := mkw 0x001864d090091000 0x7fb8e7d89e7f9c00

def z480 : W := mkw 0x220821f6f800816a 0x820001fffc0003ff

def z481 : W := mkw 0x08ef0bbd03f42bb0 0x7fff1fff03fc7ff0

def z482 : W := mkw 0x08ed01bd03f403b0 0x28b801c003fc03f0

def z483 : W := mkw 0x000020408302c16a 0xef80e1c08383e3ff

def z484 : W := mkw 0x22c8b1f6f8000000 0x66c0f9fffc000000

def z485 : W := mkw 0x0108009814240684 0x000000181c000000

def z486 : W := mkw 0x88030a0b2ff42fb5 0xdf471e3ffffc7fff

def z487 : W := mkw 0x89ff6fffbffdbffd 0xffffffffffffffff

def z488 : W := mkw 0x15f7de0807fffecc 0x7dfffe0003ffffcc

def z489 : W := mkw 0x0000000900200210 0x0200003f00000230

def z490 : W := mkw 0x10030a0003db7800 0x5d471e0003fffc00

def z491 : W := mkw 0x091964d997fd97fc 0x7fb8e7d89fff9ffc

def z492 : W := mkw 0x02c2bb62eb02c16a 0xffc7ffffff83e3ff

def z493 : W := mkw 0x03c8b1f8d726c7ee 0xefc0f9f8ff83e3ff

def z494 : W := mkw 0x00e4012400000000 0x0047002700000000

def z495 : W := mkw 0x96f7ff6beffbff7f 0xffffffffffffffff

def z496 : W := mkw 0x2008009638000000 0x0000001f1c000000

def z497 : W := mkw 0x22ec21f6f8000000 0x72ff01fffc000000

def z498 : W := mkw 0x88ed01bd07f42fb5 0xfbff01ff03fc7fff

def z499 : W := mkw 0x02c0912040000000 0x0040182060000000

def z500 : W := mkw 0x06f6ff60c302c16a 0xffffffe0e383e3ff

def z501 : W := mkw 0x0200b040c0000000 0x0400f800e0000000

def z502 : W := mkw 0x1c3f4e9d00fd3a90 0x103f061f007c1c00

def z503 : W := mkw 0x0ae5b165c3d2c17a 0xefc7f9e7e383e3ff

def z504 : W := mkw 0x00c1012903e00330 0x7ac701ff03e003f0

def z505 : W := mkw 0x1cff4fbd03fd3bb0 0x7aff07ff03fc1ff0

def z506 : W := mkw 0x14374e0003db7800 0x193f060003fffc00

def z507 : W := mkw 0x00e4000003100000 0x20b80000021c0000

def z508 : W := mkw 0x0000000804200604 0x100006181c601c00

def z509 : W := mkw 0x00030a0804e02e04 0x5f471e189de07e0c

def z510 : W := mkw 0x00c801b8032403a0 0x7af801f803fc03f0

def z511 : W := mkw 0x01184498142d1684 0x7db8e6181e7f9c00

def z512 : W := mkw 0x011864d0900d90c8 0x7db8e7c0027f9dc0

def z513 : W := mkw 0x220a2bf6f8000000 0x56471ffffc000000

def z514 : W := mkw 0x36fffff4d3db7800 0x7dffffc003fffc00

def z515 : W := mkw 0x010000000409944c 0x0100000000039c0c

def z516 : W := mkw 0x26fcf5f6f8000000 0x22b8e1fffc000000

def z517 : W := mkw 0x02d0f560c30bd16a 0xfff8ffe0e3ffffff

def z518 : W := mkw 0x0000000000000000 0x560006189c000000

def z519 : W := mkw 0x8202ba42ec02ec4f 0x8500fe00fc03fc0f

def z520 : W := mkw 0x80030a0b2ce02e15 0x90471e3f7de07c33

def z521 : W := mkw 0x02002160c302c16a 0x8b0001e0e383e3ff

def z522 : W := mkw 0x14f6de00031b5000 0x74fffe00021f8000

def z523 : W := mkw 0x00c0900003024000 0xefc0f820e383e23f

def z524 : W := mkw 0x01000008042d96cc 0x5f0006189e7f9fcc

def z525 : W := mkw 0x9413de0b2ceb7e15 0xdf47fe3ffde3fe3f

def z526 : W := mkw 0x14f6de00031b7800 0x25b8fe00021ffc00

def z527 : W := mkw 0x80020a0b2c200615 0xd6471e3ffc00023f

def z528 : W := mkw 0x24124e0238000000 0x000006001c000000

def z529 : W := mkw 0x08ed01b503d00130 0x72ff01ff01800030

def z530 : W := mkw 0x94e79a0b2ff26e15 0xdf471e3ffde07e3f

def z531 : W := mkw 0x1410d400000b5000 0x0000e00000038000

def z532 : W := mkw 0x27fefff6fc09944c 0x77fffffffc039c0c

def z533 : W := mkw 0x9cffdfbf2fff7fb5 0xffffffffffffffff

def z534 : W := mkw 0x82c39b2b6fe26f37 0xdf471e3ffde07e3f

def z535 : W := mkw 0x80030a0b28e02a11 0xda47183f61e06233

def z536 : W := mkw 0x230821fefc2486cc 0x020001fffc0003cc

def z537 : W := mkw 0x080901bd03f403b0 0x0a0001ff03fc03f0

def z538 : W := mkw 0x00020a0000002800 0x05001e0000007c00

def z539 : W := mkw 0xb6fffffffffb7e15 0xfffffffffffffe3f

def z540 : W := mkw 0x26fffff6fbd00000 0x7efffffffffc0000

def z541 : W := mkw 0x02c0b160c0008048 0x6fc0f9e0e20383cc

def z542 : W := mkw 0x08e5012d03f00330 0x5a47003f01e00230

def z543 : W := mkw 0x111964d897fffecc 0x7fb8e7d89fffffcc

def z544 : W := mkw 0x00030a0000c02800 0x0047180001806000

def z545 : W := mkw 0x26e6bb66e8000000 0x66c7f9e7e0000000

def z546 : W := mkw 0x80ef0bbf2ce02e15 0xffff1ffffde07e3f

def z547 : W := mkw 0x02c0b160c302c16a 0x6ac0e1e0038383f0

def z548 : W := mkw 0x0000012000000120 0x020001e0000003f0

def z549 : W := mkw 0x01000008042d1684 0x00000000007c1c00

def z550 : W := mkw 0x0000000000000000 0x85001800e000600f

def z551 : W := mkw 0x01000000000d90c8 0x00000000021f81c0

def z552 : W := mkw 0x2610f440d0000000 0x0000e00000000000

def z553 : W := mkw 0x02d8f5f0d302c16a 0xfff8fff8ff83e3ff

def z554 : W := mkw 0x26fefff6fb02c16a 0x76fffffffe0381c0

def z555 : W := mkw 0x24260a0628000000 0x0007000700000000

def z556 : W := mkw 0x14f74e0003d93800 0x78ff060003fc1c00

def z557 : W := mkw 0x00e5000003d00000 0x0047000001800000

def z558 : W := mkw 0x2200012668000000 0x0000002760000000

def z559 : W := mkw 0x0025000000d00000 0x103f0000007c0000

def z560 : W := mkw 0x0008009800240280 0x020001d8000003c0

def z561 : W := mkw 0x80020a0228002801 0x8000180060006003

def z562 : W := mkw 0x08000009002403b0 0x00000000000003f0

def z563 : W := mkw 0x2efffff7fbd00130 0x76fffffffd800030

def z564 : W := mkw 0x2712fe42fc09944c 0x0500fe00fc039c0c

def z565 : W := mkw 0x08ed01bd00f40290 0x72ff01ff007c0000

def z566 : W := mkw 0x03d8f5f8d72fd7ee 0x7fb8e7d89e7f9fcc

def z567 : W := mkw 0x0000000228000000 0x0200003ffc000000

def z568 : W := mkw 0x03c0b168c72fd7ee 0xefc0f9e0e3ffffff

def z569 : W := mkw 0x37fffffefffffecc 0x7fffffffffffffcc

def z570 : W := mkw 0x08e5012503d00130 0x6ac701e7038003f0

def z571 : W := mkw 0x08ec01bd002403b0 0x72ff01ff000003f0

def z572 : W := mkw 0x14f7de0003dbf96a 0xfdfffe0003ffffff

def z573 : W := mkw 0x261afed2f8000000 0x76b8ffd8fc000000

def z574 : W := mkw 0x2a0821fff82403b0 0x020001fffc0003f0

def z575 : W := mkw 0x00c0216083008168 0x6fc0e1e0838383fc

def z576 : W := mkw 0x8001000b2ce00615 0xda47003ffde0023f

def z577 : W := mkw 0x0cffdfbd03f403b0 0x7effffff03fc03f0

def z578 : W := mkw 0x27fcf5fcd42d96cc 0x7fb8e7d89e7f9fcc

def z579 : W := mkw 0x011864d8902d92c8 0x7ab8e1d8027f83c0

def z580 : W := mkw 0x0ac8b1fdc326c3fa 0xefc0f9ffe383e3ff

def z581 : W := mkw 0x02c1b169c3e2c37a 0xffc7f9ffe3e3e3ff

def z582 : W := mkw 0x26d2ff62f8000000 0x66c0ffe0fc000000

def z583 : W := mkw 0x00020a0228000000 0x04001e00fc000000

def z584 : W := mkw 0x0000000000000000 0x4d40180001806000

def z585 : W := mkw 0x031865f8d42d97ee 0xffb8e7f8fe7f9fff

def z586 : W := mkw 0x263efed6f8000000 0x143ffe1ffc000000

def z587 : W := mkw 0x00030a0000c02800 0x1007060000601c00

def z588 : W := mkw 0x00c0000003000000 0x68c0000003800000

def z589 : W := mkw 0x011864d8942d1684 0x76b8e7d89c7c1c00

def z590 : W := mkw 0x011864d8942d96cc 0x1538e6189c7f9c0c

def z591 : W := mkw 0x1413de0003db7800 0x0d00fe0003fffc00

def z592 : W := mkw 0x14f4d400031b5000 0x6df8f800039fe000

def z593 : W := mkw 0x10000000031b5000 0x00000000021f8000

def z594 : W := mkw 0x80030a0b2fe2ef7f 0xdf471e3fffe3ffff

def z595 : W := mkw 0x14f7de0903fb7a10 0x7ffffe3f03fffe30

def z596 : W := mkw 0x18ed01bd03ff7bb0 0x7bff01ff03fffff0

def z597 : W := mkw 0x00ed01bd00e00210 0x7aff01ff01e00230

def z598 : W := mkw 0x02002160c0000000 0x020001e0e0000000

def z599 : W := mkw 0x2cff4fbf3bf403b0 0x7aff07ff1ffc03f0

def z600 : W := mkw 0x800000022c000405 0x80000000fc00000f

def z601 : W := mkw 0x000000000000816a 0x80000000000003ff

def z602 : W := mkw 0x01184498142d1684 0x5f3806189c7c1e0c

def z603 : W := mkw 0x14e79a0003db7800 0x0947180003fffc00

def z604 : W := mkw 0x3efffffffbff7bb0 0x7ffffffffffffff0

def z605 : W := mkw 0x8000000b2c200615 0x0000001f1c000000

def z606 : W := mkw 0x08e4012403100120 0x0000000000000000

def z607 : W := mkw 0x0ae5912543d24132 0x8047182761806033

def z608 : W := mkw 0x26fcf5f4d302c16a 0xeff8f9e0e383e3ff

def z609 : W := mkw 0x151afed8942ffecc 0x7fb8ffd89e7fffcc

def z610 : W := mkw 0x263e6ff6f8000000 0x123f07fffc000000

def z611 : W := mkw 0x2c3f4e9f38f40290 0x103f061f1c7c0000

def z612 : W := mkw 0x80020a022c002c05 0xcf401e20fd807e3f

def z613 : W := mkw 0x01106448942d96cc 0x0d00e6009e7f9fcc

def z614 : W := mkw 0x94374e0b2cf93e15 0x103f061f1c7c1c00

def z615 : W := mkw 0x243e6ed6b8000000 0x76bfe7df9c000000

def z616 : W := mkw 0x8200216bec20877f 0x820001fffc0003ff

def z617 : W := mkw 0x16e79b2043d26922 0x8047182061806033

def z618 : W := mkw 0x14374e0000d93800 0x5d7f1e0001fc7c00

def z619 : W := mkw 0x01184490100d1080 0x00380000001c0000

def z620 : W := mkw 0x0001000000c00000 0x5847000001e00000

def z621 : W := mkw 0x80c30b2b2fe02f35 0xffc71fffffe07fff

def z622 : W := mkw 0x80030a0b2ce02e15 0x56471e3ffc601c00

def z623 : W := mkw 0x14fffed093db7800 0x7fffffd89ffffc00

def z624 : W := mkw 0x26fefffefc200604 0x7ffffffffc601e0c

def z625 : W := mkw 0xa613fe4bfce02e15 0xdf47fe3ffde07e3f

def z626 : W := mkw 0x0801000903f403b0 0x5a47003f03fc03f0

def z627 : W := mkw 0x14e79a0003d26800 0x6dc7f8000383e000

def z628 : W := mkw 0x011864d0940d94cc 0x25b8e7c09e1f9dcc

def z629 : W := mkw 0x8001000904e02e15 0xdf0006189de07e3f

def z630 : W := mkw 0x1cf7de0903ff7bb0 0x7dfffe0003fffff0

def z631 : W := mkw 0x00ed01b403d00000 0x7aff01ff03fc0000

def z632 : W := mkw 0x253e4e9e3c2d1684 0x103f061f1c7c1c00

def z633 : W := mkw 0x10e5000003db7800 0x79ff000003fffc00

def z634 : W := mkw 0x0801000903f6c3fa 0x8900000003ffe3ff

def z635 : W := mkw 0x01080098042d96cc 0x7bb801d8027f9fcc

def z636 : W := mkw 0x02c0b160c302c16a 0x66c0f9e0e20381c0

def z637 : W := mkw 0x00c0b0408302c048 0x6fc0f9c08383e3cc

def z638 : W := mkw 0x000000000302c16a 0x00000000020381c0

def z639 : W := mkw 0xaefffffffff42fb5 0xfffffffffffc7fff

def z640 : W := mkw 0x1dfffffd97fffffc 0x7fffffff9ffffffc

def z641 : W := mkw 0x00184498002d1280 0x7fb8e7d8027f9fc0

def z642 : W := mkw 0x2eef9bbf6bf403b0 0x7aff19ff63fc03f0

def z643 : W := mkw 0x88ef0bbf2bf42bb1 0xfaff19ff63fc63f3

def z644 : W := mkw 0x880801bf2c2407b5 0x820001fffc0003ff

def z645 : W := mkw 0x00c0012003000120 0xefc019e0e38063ff

def z646 : W := mkw 0x80030a0b2ce02e15 0x5f07061f9c601e0c

def z647 : W := mkw 0x02002040c000804a 0x80000000e000000f

def z648 : W := mkw 0xa20821fffc200615 0x820001fffc00023f

def z649 : W := mkw 0x02c0b160c302c16a 0xa580f9c0e203e1cf

def z650 : W := mkw 0x14f7de0003db7800 0x30bfe600027f9c00

def z651 : W := mkw 0x26fefff4d0000000 0x74ffffc000000000

def z652 : W := mkw 0x1512fe40940bfc4c 0x0500fe009c03fc0c

def z653 : W := mkw 0x000820d8802482c8 0x7fb8e1d8827f83cc

def z654 : W := mkw 0x16f4f560c31bd16a 0x20b8e1c0021f81c0

def z655 : W := mkw 0x1001000003dbf96a 0x8900000003ffffff

def z656 : W := mkw 0x26f6ff66f8000000 0x0447fe27fc000000

def z657 : W := mkw 0x36fffff6fbd26800 0x76fffffffd806000

def z658 : W := mkw 0x0200900040024002 0x8000180060006003

def z659 : W := mkw 0x08fd65fd93f403b0 0x7effe7ff9ffc03f0

def z660 : W := mkw 0x0110440014091404 0x000006001c001c00

def z661 : W := mkw 0x9412de022c0b7c05 0x8500fe00fc03fc0f

def z662 : W := mkw 0x14f7de0003db7800 0x20fff800039fe000

def z663 : W := mkw 0x02c0b160c002c04a 0xe7c0f9e0e003e00f

def z664 : W := mkw 0x1cffde9d03ff7a90 0x7dfffe1f03fffc00

def z665 : W := mkw 0x0412de0000000000 0x0400fe0000000000

def z666 : W := mkw 0x153f4e9814fd3e84 0x103f06181c7c1c00

def z667 : W := mkw 0x14d2de00030b7800 0x6dc0fe000383fc00

def z668 : W := mkw 0x04fedfb400000000 0x76ffffff00000000

def z669 : W := mkw 0x0010644090000000 0x0400e6009c000000

def z670 : W := mkw 0x00e5000903f00210 0x7aff003f03fc0230

def z671 : W := mkw 0x000000000002c04a 0x810000000003e00f

def z672 : W := mkw 0x0000000800200200 0x5a00001800600200

def z673 : W := mkw 0x0000000000000000 0x82000020e000023f

def z674 : W := mkw 0x26ee9bb668000000 0x72ff19ff60000000

def z675 : W := mkw 0x0200b040c002c04a 0xef80f9c0e203e3cf

def z676 : W := mkw 0x26e4912440000000 0x0000000000000000

def z677 : W := mkw 0x03d8f5f8d42d96cc 0x7ff8fff8fe7f9fcc

def z678 : W := mkw 0x04e69a0000000000 0x0047180000000000

def z679 : W := mkw 0x82032b6bece0af7f 0xdf471ffffde07fff

def z680 : W := mkw 0x88ef0bbf2ff42fb5 0x7aff07ff1ffc1ff0

def z681 : W := mkw 0x02c0b160c000816a 0xe6c0f9e0e00003ff

def z682 : W := mkw 0x011864d8942d96cc 0x22b8e1d89e1f83cc

def z683 : W := mkw 0x08ed21fd83f483f8 0x7fffe1ff83ff83fc

def z684 : W := mkw 0x3612fe42f80b7800 0x0500fe00fc03fc00

def z685 : W := mkw 0x0008009000000000 0x72b801d800000000

def z686 : W := mkw 0x02c0b160c0000000 0x2080e1c000000000

def z687 : W := mkw 0x2aed21fffbf403b0 0x7aff01fffffc03f0

def z688 : W := mkw 0x14f7de0807fb7e04 0x7ffffe189ffffe0c

def z689 : W := mkw 0x08ed009d03f40290 0x78ff001f03fc0000

def z690 : W := mkw 0x00030a0900e02a10 0x5f471e3f01e07e30

def z691 : W := mkw 0x80030a032cc02c15 0x85471e27fd807c3f

def z692 : W := mkw 0x08000000031401a0 0x00000000021c01c0

def z693 : W := mkw 0x94e79a032bd26811 0x8047182761806033

def z694 : W := mkw 0x080801bd002403b0 0x7ab801ff027c03f0

def z695 : W := mkw 0x00c0900003024000 0x2080e00002038000

def z696 : W := mkw 0x27fefffefc2d1684 0x76fffffffc7c1c00

def z697 : W := mkw 0x82c39b236bc26933 0x8047182761806033

def z698 : W := mkw 0x88e70b2f2ff02f35 0xdf471e3ffde07e3f

def z699 : W := mkw 0x0bfdf5fdd7ffd7fe 0xffffffffffffffff

def z700 : W := mkw 0x0001000900e00210 0xdf47183fe1e0623f

def z701 : W := mkw 0x0000000000000000 0x4a40002001800230

def z702 : W := mkw 0x00e70a0003d02800 0x7dff1e0003fc7c00

def z703 : W := mkw 0x08e5000903f403b0 0x78ff000003fc03f0

def z704 : W := mkw 0x0200012040000122 0x8000002060000033

def z705 : W := mkw 0x880b0bbf2ce42fb5 0xdf471ffffde07fff

def z706 : W := mkw 0x00e5012003d00120 0x7aff01e003fc03f0

def z707 : W := mkw 0x00134e0000c93800 0x7dbfe600027f9c00

def z708 : W := mkw 0x9ce79b272bd26931 0x8047182761806033

def z709 : W := mkw 0x0aed91bd43f643b2 0x7aff01ff03fc03f0

def z710 : W := mkw 0x011864d8942d96cc 0x7ab8e7d81e7f9fc0

def z711 : W := mkw 0x26fefff6f8091000 0x77fffffffc039c00

def z712 : W := mkw 0x26fefff6f8000000 0x76bfe7df9c000000

def z713 : W := mkw 0x14f7df2003db7920 0x7dffffc003fffdc0

def z714 : W := mkw 0x00c20b222b000120 0x7ec71fffff8003f0

def z715 : W := mkw 0x88ed01bd07f407b5 0xfaff01ff03fc03ff

def z716 : W := mkw 0x0bc1b169c7ffd7fe 0xefc0f9e0e3ffffff

def z717 : W := mkw 0x26eebbf6fb02c16a 0x824719fffd8063ff

def z718 : W := mkw 0x14f7de0003db7800 0x78ffe60003ff9c00

def z719 : W := mkw 0x14f7de0003db7800 0x74fffe00027f9c00

def z720 : W := mkw 0x36fefff6fb1b7800 0x77fffffffe1ffc00

def z721 : W := mkw 0x26f6df2668000000 0x76fffe3ffc000000

def z722 : W := mkw 0x0a2db0ddc0f6c2da 0x953ff81fe07fe00f

def z723 : W := mkw 0x16376f60c0d9b96a 0x923f07e0e07c1fff

def z724 : W := mkw 0x8001000904e02e15 0x8b000020e1e07e3f

def z725 : W := mkw 0x14f7de0003db7800 0x7ffffe0083fffe0c

def z726 : W := mkw 0x242e0a9638000000 0x0007001f1c000000

def z727 : W := mkw 0x14f7de0003db7800 0x7ffffe189ffffc00

def z728 : W := mkw 0x26e6bb66eb02c16a 0xffc7ffffff83e3ff

def z729 : W := mkw 0x24124e0238000000 0x56471e3ffc000000

def z730 : W := mkw 0x00ed009903f40290 0x7aff01ff03fc03f0

def z731 : W := mkw 0x010820d8942486cc 0x000001d81c0001c0

def z732 : W := mkw 0x80020a022c002c05 0xdf471e3ffd807e3f

def z733 : W := mkw 0x36f7de026bdb7800 0x7dfffe0063fffc00

def z734 : W := mkw 0x14f6de00031b7800 0x7db8fe00027ffc00

def z735 : W := mkw 0x00022a42a8000000 0x76c7fffffc000000

def z736 : W := mkw 0x88ee0bb62f142da5 0xa5b81fc0fe1c7dcf

def z737 : W := mkw 0x26fefff6fb024122 0xfeffffffff8063f3

def z738 : W := mkw 0x26fefed6f8000000 0x74fffe1ffc000000

def z739 : W := mkw 0x26fefff6f8000000 0x7ffffffffc00020c

def z740 : W := mkw 0x26fefff6f8000000 0x147ffe3ffc000000

def z741 : W := mkw 0x00126e42b8000000 0x5647fe3ffc000000

def z742 : W := mkw 0x1413de0000cb7800 0x7dfffe0003fffc00

def z743 : W := mkw 0x263efed6f8000000 0x76bfffdffc000000

def z744 : W := mkw 0x26fefff6fb02c16a 0x7ffffffffe0383cc

def z745 : W := mkw 0x0901000907ffd7fe 0x8900000003ffffff

def z746 : W := mkw 0x14374e0000d93800 0x153fe600007f9c00

def z747 : W := mkw 0x26fefff6f8000000 0x30ffffff7c000000

def z748 : W := mkw 0x8901000907fdbffd 0x8900000003ffffff

def z749 : W := mkw 0x8001000904e93e15 0x8900000003fffe3f

def z750 : W := mkw 0x1011440003db7800 0x29b8e00003fffc00

def z751 : W := mkw 0x090821fc942487ec 0x020001d89c0003cc

def z752 : W := mkw 0x243e6ed6b8000000 0x143fe61f9c000000

def z753 : W := mkw 0x011864d8942d96cc 0x2db8e7c09e7f9fcc

def z754 : W := mkw 0x8001000904e02e15 0x800000000180623f

def z755 : W := mkw 0xa6fdf5fdd4e02e15 0xa9b8e1c001e07e3f

def z756 : W := mkw 0x810820d9942486dd 0x820001d89c0003ff

def z757 : W := mkw 0x02fcf5f4d0000000 0x76fffffffc000000

def z758 : W := mkw 0x34f7de023bdb7800 0x7dfffe001ffffc00

def z759 : W := mkw 0x20ec01b638000000 0x72ff01ff1c000000

def z760 : W := mkw 0x243e6ed6b8000000 0x30bfe7df1c000000

def z761 : W := mkw 0x8001000904e02e15 0xcb40002001e07e3f

def z762 : W := mkw 0x9101000907fffedd 0x8900000003ffffff

def z763 : W := mkw 0x0200b160c302c16a 0x8f00f9e0e383e3ff

def z764 : W := mkw 0x800a0a9a2c242e85 0xffb81fd8fe7c7fcf

def z765 : W := mkw 0x80030a0b2ce02e15 0x95471e3ffde07c3f

def z766 : W := mkw 0x82c3bb6befe2ef7f 0x3087e7df1e639dc0

def z767 : W := mkw 0x26fefff6f8008048 0x76fffffffc0003cc

def z768 : W := mkw 0x0035440000d91000 0x7dbfe600027f9c00

def z769 : W := mkw 0x26fefff6f800816a 0xfffffffffd8063ff

def z770 : W := mkw 0x02c0b160c302c16a 0xffc0ffe0e3e3ffff

def z771 : W := mkw 0x000020408302c16a 0xefc0f9e0e383e3ff

def z772 : W := mkw 0x00f4440003191000 0x7db8e600027f9c00

def z773 : W := mkw 0x00fc45b410000000 0x72ff07ff1c000000

def z774 : W := mkw 0x08ed01bd03f403b0 0x127f01ff01fc03f0

def z775 : W := mkw 0x810b2adbbce4aedd 0x824719fffd8063ff

def z776 : W := mkw 0x003c64d490000000 0x76bfe7df9c000000

def z777 : W := mkw 0x24124e0238000000 0x1007061f1c000000

def z778 : W := mkw 0x0001000904e00614 0x0900000001e01e3c

def z779 : W := mkw 0x0ae4b164c312c16a 0xefc0f9e0e383e3ff

def z780 : W := mkw 0x02c0b160c302c16a 0xa2c0f9e0e383e3ff

def z781 : W := mkw 0x27e69b2e6c2d96cc 0x09471827627f9fcc

def z782 : W := mkw 0x08ed01bd00f40290 0x7aff01ff027c03c0

def z783 : W := mkw 0x09ed01bd17f407b4 0x7aff01ff1ffc03f0

def z784 : W := mkw 0x8001000904e02e15 0x8000000000601e3f

def z785 : W := mkw 0x8101000904e9be5d 0x8900000001e3fe3f

def z786 : W := mkw 0x15efbad897f6eecc 0x024719d89d8063cc

def z787 : W := mkw 0x03d8d5b8572f57a6 0x90781e387dfc7c33

def z788 : W := mkw 0x0801000907f407b4 0x0900000003fc1ffc

def z789 : W := mkw 0x14f7de022bdb7800 0xfffffe3ffffffe3f

def z790 : W := mkw 0x04364e0000091000 0x7dbfe600027f9c00

def z791 : W := mkw 0x001864d090000000 0x76ffe7ff9c000000

def z792 : W := mkw 0x26fefff6f8008048 0xffffffffff83e3ff

def z793 : W := mkw 0x00020a0228000000 0x5f471e3ffd806000

def z794 : W := mkw 0x320921f6fbdb7800 0x0b0001fffffffc00

def z795 : W := mkw 0x08ed01bd00f403b0 0x72ff01ff007c03f0

def z796 : W := mkw 0x00ec21f490000000 0x72ff01ff9c000000

def z797 : W := mkw 0x14d2de00030b7800 0x7df8fe0003fffc00

def z798 : W := mkw 0x00124e0228091000 0x7ffffe3ffe7f9c00

def z799 : W := mkw 0x08f5452503d91130 0x7dffe62703ff9c30

def z800 : W := mkw 0x00d0d40000091000 0x7df8fe00027f9c00

def z801 : W := mkw 0x0010440000091000 0x30b8e600027f9c00

def z802 : W := mkw 0x26fefff6f8000000 0x7ffffffffd806000

def z803 : W := mkw 0x343e4e9638191000 0x103f061f1c1c0000

def z804 : W := mkw 0x8011440904e93e15 0xfdb8e60003fffe3f

def z805 : W := mkw 0x88ed01bd07f42fb5 0xffff19ffe3fc7fff

def z806 : W := mkw 0x24fe6ff6b8000000 0x76ffe7ff9c000000

def z807 : W := mkw 0x00124e0000091000 0x7dfffe00027f9c00

def z808 : W := mkw 0x80030a0b2ce02e15 0x92471e3ffde07e3f

def z809 : W := mkw 0x200a0a9638000000 0x56471e3ffc000000

def z810 : W := mkw 0x26fefff6fb02c16a 0x7fffffffff83e1c0

def z811 : W := mkw 0x0008009800240280 0x7aff01ff027c03c0

def z812 : W := mkw 0x811b6ed3b8cdb8d9 0xa0fff9e7639fe1f3

def z813 : W := mkw 0x0001000904e00614 0xdf471e3ffde07e3f

def z814 : W := mkw 0x02c0b160c302c16a 0xfff8f9e0e3ffe3ff

def z815 : W := mkw 0x26fefff6fb024120 0x7fffffffff83e3f0

def z816 : W := mkw 0x08ed01bd03f403b0 0x7eff19ffe3fc03f0

def z817 : W := mkw 0x8801000907f407b5 0x8800000003fc03ff

def z818 : W := mkw 0x22ec21f6fb00816a 0xfaff01ffff8003ff

def z819 : W := mkw 0x0011440000c91000 0x7dffe60003ff9c00

def z820 : W := mkw 0x08ed01bd03f403b0 0x30ff01ff03fc01f0

def z821 : W := mkw 0x811964d994edbedd 0xa9b8e1c003ffffff

def z822 : W := mkw 0x00d0440003091000 0x7df8e60003ff9c00

def z823 : W := mkw 0x2c3e4e9638140080 0x103f061f1c1c0000

def z824 : W := mkw 0x26fefff6fb0bd16a 0xffffffffffffffff

def z825 : W := mkw 0x1011440000d93800 0x7db8e600027f9c00

def z826 : W := mkw 0x26fefff6f8024002 0xf6fffffffc006003

def z827 : W := mkw 0x263e4fb678000000 0x103f063f7c000000

def z828 : W := mkw 0x26eebbf6f8000000 0x56471ffffc000000

def z829 : W := mkw 0x0aed91bd43f643b2 0xfffff9ff63ffe3f3

def z830 : W := mkw 0x10e5900003db7800 0x7dfff80003fffc00

def z831 : W := mkw 0x09f5656597d9957c 0x0547e6279d839c3c

def z832 : W := mkw 0x0010440000091000 0x29b8e000027f9c00

def z833 : W := mkw 0x243e4e9638091000 0x103f061f1c7c1c00

def z834 : W := mkw 0x210820debc2486cc 0x020001df9c0003cc

def z835 : W := mkw 0x2e13fe4bfbf403b0 0x0c00fe00fffc03f0

def z836 : W := mkw 0x14f7de0003db7800 0x7fffffc003ffffc0

def z837 : W := mkw 0x243e4e9638000000 0x123f063ffc000000

def z838 : W := mkw 0x3612fe42f80bf84a 0x8500fe00fc03fc0f

def z839 : W := mkw 0x8001000904e02e15 0xcf00000081e07e3f

def z840 : W := mkw 0x26fedfb67b024122 0x907f1e3f7d806033

def z841 : W := mkw 0x27eebbfefc2486cc 0x024719fffc0003cc

def z842 : W := mkw 0x000a0bb628000000 0x56471ffffc000000

def z843 : W := mkw 0x26fefff6f8000000 0x0647fffffc000000

def z844 : W := mkw 0x26f6ff66f8000000 0x5647fe3ffc000000

def z845 : W := mkw 0x001a4e9238000000 0x103f061f1c000000

def z846 : W := mkw 0x010820d8942486cc 0x560007d89c0003cc

def z847 : W := mkw 0x0aed01bd43f403b2 0xfaff01ff63fc03f3

def z848 : W := mkw 0x1cf7df2403db7920 0x7dfffe0003fffc00

def z849 : W := mkw 0x36f7df266bdb7922 0xfdfffe2763fffc33

def z850 : W := mkw 0x14f5d40003db7800 0x79ffe00003fffc00

def z851 : W := mkw 0x80030a0b2ce02e15 0x87471e3ffd807e3f

def z852 : W := mkw 0x082d009d00f40290 0x123f01df007c03c0

def z853 : W := mkw 0x001a6ed2b8000000 0x76bfe7df9c000000

def z854 : W := mkw 0x221a6ff6f8000000 0x76fffffffc000000

def z855 : W := mkw 0x94f7de022bdb7801 0xfdfffe0063fffc03

def z856 : W := mkw 0x26fefff6f8000000 0x7efffffffe7c0000

def z857 : W := mkw 0x36fefff6f8093800 0x76fffffffc001c00

def z858 : W := mkw 0x200a0a9638000000 0x1007061f1c000000

def z859 : W := mkw 0x26fefff6fb02c16a 0xf7fffffffd83e03f

def z860 : W := mkw 0x27fefff6f8099048 0x76fffffffc038000

def z861 : W := mkw 0x27fefff6f80480c8 0x76fffffffc0001c0

def z862 : W := mkw 0x10d1d40003db7800 0x7df8fe0003fffc00

def z863 : W := mkw 0x0412de0228000000 0x5647fe3ffc000000

def z864 : W := mkw 0x00020a0a2c200604 0xdf471e3ffde07e3f

def z865 : W := mkw 0x26fefff6f8000000 0x74ffffdf1c000000

def z866 : W := mkw 0x011864d8942d96cc 0x76b8e7d89e7f9dc0

def z867 : W := mkw 0x88ed01bd07f42fb5 0x7aff01ff03fc1ff0

def z868 : W := mkw 0x36fefff6fb1b5000 0x7ffffffffe7f9c00

def z869 : W := mkw 0x8001000904e02e15 0x8940182061e07e3f

def z870 : W := mkw 0x00ec01b400000000 0x76ff07ff9c000000

def z871 : W := mkw 0x0101000904ed96dc 0x0900000003ff9ffc

def z872 : W := mkw 0x36fefff6fb124000 0x76fffffffc000000

def z873 : W := mkw 0x220a2bf6f8000000 0x024719fffc000000

def z874 : W := mkw 0x24fefed6b8000000 0x76ffffdf9c000000

def z875 : W := mkw 0x243e4e9638000000 0x527f063f1c000000

def z876 : W := mkw 0x94f5d40907fb7e15 0xa9b8e00003fffe3f

def z877 : W := mkw 0x010820dabc2486cc 0x020001fffc0003cc

def z878 : W := mkw 0x8101000904e4aedd 0x8900000001e07fff

def z879 : W := mkw 0x030821f8d42487ee 0x020001d89c0003cc

def z880 : W := mkw 0x02002160c000816a 0xefc0f9e0e383e3ff

def z881 : W := mkw 0x0aed91bd43f643b2 0xffff19ffe3fc63ff

def z882 : W := mkw 0x08ec01b4031401a0 0x30bf01df021c01c0

def z883 : W := mkw 0x26fefff6f802c16a 0xf7fffffffc03e3ff

def z884 : W := mkw 0x893f4e9f3cfd3e95 0x103f061f1c7c1c00

def z885 : W := mkw 0x08ee0bb62b1401a0 0x76ff1ffffe1c01c0

def z886 : W := mkw 0x27fefff6f80d1080 0x76fffffffc1c0000

def z887 : W := mkw 0x02eebbf6e8000000 0x76fffffffc000000

def z888 : W := mkw 0x263e6ff6f800816a 0x923f07fffc0003ff

def z889 : W := mkw 0x08ed01bd03f403b0 0x38bf01df03fc03f0

def z890 : W := mkw 0x09fd65fd97fd97fc 0x29b8e1c003ff9ffc

def z891 : W := mkw 0x26fefff6f8099048 0x7ffffffffe7f9fcc

def z892 : W := mkw 0x08ed01bd03f403b0 0x72ff01ff027c01c0

def z893 : W := mkw 0x3efefff6fb1f51a0 0x76fffffffe1f81c0

def z894 : W := mkw 0x27fefff6fb0fd1ea 0x76fffffffe1f81c0

def z895 : W := mkw 0x08ed01b503d401b0 0x6aff01e7039c03f0

def z896 : W := mkw 0x263ede9678000000 0x103f1e1f7c000000

def z897 : W := mkw 0x00d0d400030b5000 0x7db8e600027f9c00

def z898 : W := mkw 0x243e4e963b02c16a 0x993f061f1f83e3ff

def z899 : W := mkw 0x011864d0940d94cc 0x7db8e7c09e7f9dcc

def z900 : W := mkw 0x26eebbf6f8000000 0x66c7f9fffc000000

def z901 : W := mkw 0x94f7de032bdb7811 0xfffffe27e3fffe3f

def z902 : W := mkw 0x010820d8942486cc 0xcf4019f8fd8063ff

def z903 : W := mkw 0x14f7de022bdb7800 0x7dfffe00fffffc00

def z904 : W := mkw 0x14f5d40003db7800 0x6df8f80003fffc00

def z905 : W := mkw 0x14f4d400031b5000 0x30b8e600027f9c00

def z906 : W := mkw 0x14f6de00000b7800 0x7dfffe00027ffc00

def z907 : W := mkw 0x001864d090099048 0x7fb8e7d89e7f9fcc

def z908 : W := mkw 0x011864d8942d96cc 0xffb8ffd8fe7fffcf

def z909 : W := mkw 0x88ed01bd07f42fb5 0xffff07ff9ffc7fff

def z910 : W := mkw 0x26fefff6f8024000 0x77fffffffc03e000

def z911 : W := mkw 0x08ed01bd07f407b4 0x7aff01ff9ffc03fc

def z912 : W := mkw 0x26fefff6f8000000 0xf7fffffffc00600f

def z913 : W := mkw 0x00fe6ff6b8000000 0x76fffffffc000000

def z914 : W := mkw 0x00e60a0228000000 0x76ff1e3ffc000000

def z915 : W := mkw 0x010820d8942486cc 0x6a8001d89e0003cc

def z916 : W := mkw 0x00020a0228000000 0xd6471e3ffc00023f

def z917 : W := mkw 0x06f6ff62eb02c16a 0xffffffffff83e3ff

def z918 : W := mkw 0x02c0b160c302c16a 0xffc7f9ffe383e3ff

def z919 : W := mkw 0x09c1216987fd97fc 0x6fc0e1e083ff9ffc

def z920 : W := mkw 0x00ec01b400040080 0x72ff01ff021c01c0

def z921 : W := mkw 0x000a2ad2b8000000 0x56471ffffc000000

def z922 : W := mkw 0x04e69a0228000000 0x56471e3ffc000000

def z923 : W := mkw 0x8101000904ed3e95 0x00000000007c1c00

def z924 : W := mkw 0x263efed6f802c04a 0x953ffe1ffc03e00f

def z925 : W := mkw 0x011864d8942d96cc 0x7ff8ffd89fffffcc

def z926 : W := mkw 0x36f7df266bdb7800 0x7ffffe3ffffffc00

def z927 : W := mkw 0x26fedfb678000000 0x567f1e3ffc000000

def z928 : W := mkw 0x1cf7df2503db7930 0x7fffffe703fffff0

def z929 : W := mkw 0x010821fc942486cc 0x020001ff9c0003cc

def z930 : W := mkw 0x08ed01bd03f403b0 0x7abf01df027c03c0

def z931 : W := mkw 0x26fefff6fb000120 0xffffffffff8063ff

def z932 : W := mkw 0x26fefff6f800816a 0xfffffffffe0383ff

def z933 : W := mkw 0x243e4e9638000000 0x563f061f9c000000

def z934 : W := mkw 0x26fefff6f8000000 0x34bfffdffc000000

def z935 : W := mkw 0x002e0a9628000000 0x103f061f1c000000

def z936 : W := mkw 0x8101204984edbedd 0xefc0f9e0e3ffffff

def z937 : W := mkw 0x24fe4fb638000000 0x107f063f1c000000

def z938 : W := mkw 0x0aed91bd43f403b0 0x7aff19ff63fc03f0

def z939 : W := mkw 0x88030a0b2cf42e95 0xdf471e3ffdfc7e3f

def z940 : W := mkw 0x22022a42f8000000 0x56471e3ffc000000

def z941 : W := mkw 0x08e5012503d00130 0x7aff01e703fc03f0

def z942 : W := mkw 0x953f4e9b3cfd3e95 0x103f061f1c7c1c00

def z943 : W := mkw 0x02c0b160c302c16a 0xad80f9c0e383e3ff

def z944 : W := mkw 0xa30821fffc2486dd 0x820001fffc0003ff

def z945 : W := mkw 0x8801000907f42fb5 0x0800000003fc1ff0

def z946 : W := mkw 0x243e4fb638000000 0x123f07ff1c000000

def z947 : W := mkw 0x16f7df2043db7800 0x7dfffe2063fffc00

def z948 : W := mkw 0x02c29b226b024122 0xd6471e3ffd806033

def z949 : W := mkw 0x92c1b169c7fbff7f 0xefc0f9e0e3ffffff

def z950 : W := mkw 0x10104400031b5000 0x7db8e600027f9c00

def z951 : W := mkw 0x9001000907f26e15 0x8900000001e07e3f

def z952 : W := mkw 0x8001000904e02e15 0x8000000001e07c33

def z953 : W := mkw 0x80c1900907e26e15 0xedc0f80003e3fe3f

def z954 : W := mkw 0x9001000907fb7e15 0x0900000003fffc00

def z955 : W := mkw 0x26fefff6f802c04a 0xfffffffffd83e23f

def z956 : W := mkw 0x00c0216083008168 0xefc0f9e0e383e3ff

def z957 : W := mkw 0x14f5d40003db5000 0x7dffe60003ff9c00

def z958 : W := mkw 0x243e4e9638000000 0x107f1e3f7c000000

def z959 : W := mkw 0x27fefff6f80d90c8 0x7ffffffffe7f9dc0

def z960 : W := mkw 0x262e2bf6f8000000 0x020701fffc000000

def z961 : W := mkw 0x8001000904e02e15 0xdd00060001e07e3f

def z962 : W := mkw 0x14f7de0003db7800 0x7ffffe20e3fffc00

def z963 : W := mkw 0x26fefff6f8000000 0x7ffffffffe038000

def z964 : W := mkw 0x26fefff6fb000120 0x76fffffffd800030

def z965 : W := mkw 0x02d0d520430b5122 0xfdf8fe2063fffc33

def z966 : W := mkw 0x00020a0228000000 0x5f471e3ffc601c00

def z967 : W := mkw 0x08ed01bd03f403b0 0x7eff07ff9ffc03f0

def z968 : W := mkw 0x082d01bd00f403b0 0x7abf01ff027c03f0

def z969 : W := mkw 0x26fedfb678000000 0x103f061f1c000000

def z970 : W := mkw 0x230821fefc2487ee 0x820001fffc0003ff

def z971 : W := mkw 0x01126e42bc09944c 0x0500fe00fc039c0c

def z972 : W := mkw 0x8312fe42fc0bfc4f 0x8500fe00fc03fc0f

def z973 : W := mkw 0x26fefff6f8000000 0x7ffffffffc601c00

def z974 : W := mkw 0x011864d8942d96cc 0xffb8e7d89fffffff

def z975 : W := mkw 0x82c1b169c4e02e15 0xefc0f9e0e1e07e3f

def z976 : W := mkw 0x02dafff2f8000000 0x76fffffffc000000

def z977 : W := mkw 0xa712fe42fc09bc4d 0x8500fe00fc03fc0f

def z978 : W := mkw 0x030820d8d42486ce 0x820001d8fc0003cf

def z979 : W := mkw 0x04f6de022b024000 0xfffffe3fff83e23f

def z980 : W := mkw 0x230820dafc2486cc 0x020001d8fc0003cc

def z981 : W := mkw 0x08ed009d03f40290 0x7aff01df03fc03c0

def z982 : W := mkw 0x1cf7de0103db7930 0x7dfffe0003fffc30

def z983 : W := mkw 0x0010440000091000 0x1538e600007f9c00

def z984 : W := mkw 0x091864dd942d96dc 0x7fb8e7df9e7f9fcc

def z985 : W := mkw 0x02e4b160c302c16a 0xfffff9e0e383e3ff

def z986 : W := mkw 0x08ec01bc033403a0 0x7aff01ff027c03c0

def z987 : W := mkw 0x26fefff6f8008048 0x76fffffffe0381c0

def z988 : W := mkw 0x010821f8942487ec 0x020001f89c0003fc

def z989 : W := mkw 0x36fcf5f4d31bd16a 0x20b8e1c0021f81c0

def z990 : W := mkw 0x04fedfb628000000 0x76fffffffc000000

def z991 : W := mkw 0x010820d8942486cc 0x820001f8fc0003ff

def z992 : W := mkw 0x26fefff6fb02c04a 0xffffffffff83e00f

def z993 : W := mkw 0x011864d8942d96cc 0x7fffe7ff9e7f9fcc

def z994 : W := mkw 0x26fefff6f8000000 0x127f1ffffc000000

def z995 : W := mkw 0x9801000907ff7fb5 0x8900000003ffffff

def z996 : W := mkw 0x14f5d40003db7800 0x7db8e60003fffc00

def z997 : W := mkw 0x00ec01bc032403a0 0x7aff01ff03fc03f0

def z998 : W := mkw 0x26fefff6fb024000 0xffffffffff83e23f

def z999 : W := mkw 0x1410d400000b5000 0x7db8e600027f9c00

def z1000 : W := mkw 0x26fefff6f8040080 0x76fffffffe1c01c0

def z1001 : W := mkw 0x08ed01bd03f403b0 0x7fff07ff03fc1ff0

def z1002 : W := mkw 0x26fefff6f8091000 0x76fffffffe1f8000

def z1003 : W := mkw 0x0901000904fd96dc 0x09000000027f9fcc

def z1004 : W := mkw 0x010820d8942486cc 0x4f0001d89c0003cc

def z1005 : W := mkw 0x230821fcd42486cc 0x020001d89c0003cc

def z1006 : W := mkw 0x8001204984e0ae5d 0xef80e1c083e3ffff

def z1007 : W := mkw 0x24fede9638000000 0x76fffe3ffc000000

def z1008 : W := mkw 0x090820d9942487fc 0x020001d89c0003fc

def z1009 : W := mkw 0xa6fefff6f8002801 0xf6fffffffc006003

def z1010 : W := mkw 0x14f7de0003db7800 0x7ffffe3f03fffc00

def z1011 : W := mkw 0x08ec01b4031401a0 0x7aff01ff039c03f0

def z1012 : W := mkw 0x26fefff6f8091000 0x76fffffffc7c1c00

def z1013 : W := mkw 0x26fefff6fb02c16a 0xf7fffffffe03e1cf

def z1014 : W := mkw 0x08ed91bd03f643b0 0x7aff19ff03fc63f0

def z1015 : W := mkw 0x00020a022b02c16a 0xdf471e3fff83e3ff

def z1016 : W := mkw 0x94f7de032bdb7811 0x7dfffe0703fffc00

def z1017 : W := mkw 0x00ed01b403d00120 0x7aff01ff03fc03f0

def z1018 : W := mkw 0x2712fe42f8099048 0x0400fe00fc038000

def z1019 : W := mkw 0x082d009d00f40290 0x7aff01ff03fc03f0

def z1020 : W := mkw 0x08ed01bd03f643b2 0xfaff01ff03fc63f3

def z1021 : W := mkw 0x1c1adfbd002f7bb0 0x0700ffff0003fff0

def z1022 : W := mkw 0x9001000904f93e15 0x8900000001fc7e3f

def z1023 : W := mkw 0x243e4e9638000000 0x143f1e1ffc000000

def z1024 : W := mkw 0x9001000904eb7e15 0x8900000001e3fe3f

def z1025 : W := mkw 0x26e6bb66e8000000 0x76c7fffffc000000

def z1026 : W := mkw 0x14f7df2003db7920 0x7dfffe2003fffc30

def z1027 : W := mkw 0x08ed01bd03f403b0 0x22ff01ff039c03f0

def z1028 : W := mkw 0x80030a0b2ce02e15 0xffc7fe3fffe3fe3f

def z1029 : W := mkw 0x0010440000091000 0xfff8fe20e3fffe3f

def z1030 : W := mkw 0x001864d8902d1280 0x7fb8e7d89e7f9fc0

def z1031 : W := mkw 0x0000000228000000 0x5247003ffc000000

def z1032 : W := mkw 0x8001000904e02e15 0x8d001800e1e07e3f

def z1033 : W := mkw 0x26fedfb678000000 0x72ff1fff7c000000

def z1034 : W := mkw 0x811864d9942d96dd 0xffb8e7d89e7f9fff

def z1035 : W := mkw 0x00020a0228000000 0xd6471e3ffd806033

def z1036 : W := mkw 0x24fe4e9638000000 0x70ff061f1c000000

def z1037 : W := mkw 0x3ef7df276bdb7930 0x7dfffe2763fffc30

def z1038 : W := mkw 0x14374e0000d93800 0x30bfe600027f9c00

def z1039 : W := mkw 0x8801000907f02f35 0x8900000001e07e3f

def z1040 : W := mkw 0x26eebbf6f8000000 0x72ff19fffc000000

def z1041 : W := mkw 0x243e4e9638000000 0x72bf07df1c000000

def z1042 : W := mkw 0x80030a0b2ce02e15 0xffff1e3ffffc7e3f

def z1043 : W := mkw 0x24fede9638000000 0x30bfe61f1c000000

def z1044 : W := mkw 0x010a2adabc2486cc 0x56471ffffc0003cc

def z1045 : W := mkw 0x02c0b160c302c16a 0xffc0fff8ff83e3ff

def z1046 : W := mkw 0x9cf7df272bdb7931 0xfdfffe2763fffc33

def z1047 : W := mkw 0x8ae79b276bd26933 0x8047182761806033

def z1048 : W := mkw 0x26fefff6f8000000 0x22fff9fffc000000

def z1049 : W := mkw 0x082d01bd03f403b0 0x1a3f01ff03fc03f0

def z1050 : W := mkw 0x14f7de0003db7800 0x29fff80003fffc00

def z1051 : W := mkw 0x243e4e9638000000 0x547f1e1f1c000000

def z1052 : W := mkw 0x94f4d40b2f3b5615 0xa2b8e03ffe1f823f

def z1053 : W := mkw 0x8001000904e02e15 0xcd40180001e07e3f

def z1054 : W := mkw 0x83c1b169c7efffff 0xefc0f9e0e3ffffff

def z1055 : W := mkw 0x00e79a0003d26800 0x7dfffe0003fffc00

def z1056 : W := mkw 0x00184498042d1684 0x7fb8e7d89e7f9fcc

def z1057 : W := mkw 0x80030a0904e02e15 0x8d001e0001e07e3f

def z1058 : W := mkw 0x02022b62e8000000 0x56471ffffc000000

def z1059 : W := mkw 0x26fefff6f800816a 0x76fffffffc0001c0

def z1060 : W := mkw 0x80030a0b2ce02e15 0xffc71fffffe07fff

def z1061 : W := mkw 0x02fcf5f4d302c16a 0xffffffffff83e3ff

def z1062 : W := mkw 0x002e0a9628000000 0x567f1e3ffc000000

def z1063 : W := mkw 0x24fe4fb638000000 0x76ff1ffffc000000

def z1064 : W := mkw 0x26fefff6f8000120 0x76fffffffc0003f0

def z1065 : W := mkw 0x261afed2f8000000 0x76fffffffc000000

def z1066 : W := mkw 0x00ec01b628000000 0x72ff01fffc000000

def z1067 : W := mkw 0x16f7de0043db7802 0xfdfffe0063fffc03

def z1068 : W := mkw 0x02022b62e800816a 0xd6471ffffc0003ff

def z1069 : W := mkw 0x243e4e9638000000 0xdf7f1e3ffd80623f

def z1070 : W := mkw 0x00f4440000091000 0x7dffe600027f9c00

def z1071 : W := mkw 0x26fefff6fb024122 0xfffffffffd80623f

def z1072 : W := mkw 0x08ec01bd033403b0 0x72ff01ff021c03f0

def z1073 : W := mkw 0x0b0821fdd42487fe 0x820001fffc0003ff

def z1074 : W := mkw 0x14f7de0003db7800 0xfdfffe00e3fffc0f

def z1075 : W := mkw 0x080901bd00e403b0 0x7aff01ff03fc03f0

def z1076 : W := mkw 0x14f6de022b1b5000 0x76fffe3ffe1f8000

def z1077 : W := mkw 0x24fede9638000000 0x107f1e1f1c000000

def z1078 : W := mkw 0x343e4e9638093800 0x103f061f1c001c00

def z1079 : W := mkw 0x22ecb1f6fb02c16a 0xfffff9ffff83e3ff

def z1080 : W := mkw 0x0000000000000000 0x5647063f9c000000

def z1081 : W := mkw 0x08ed91bd03f643b0 0x7affe1ff03ff83f0

def z1082 : W := mkw 0x14f4d400031b5000 0x7df8fe0003fffc00

def z1083 : W := mkw 0x2712fe42fc0bd44e 0x8500fe00fc03fc0f

def z1084 : W := mkw 0x830821fbfc2487ff 0x820001fffc0003ff

def z1085 : W := mkw 0x80134e0328c93811 0xfdfffe2763fffc33

def z1086 : W := mkw 0x00c0912003024120 0xefc0f9e0e383e3ff

def z1087 : W := mkw 0x26fedfb678000000 0x74fffe3f7c000000

def z1088 : W := mkw 0x88ed01bd03f42bb1 0xfaff01ff03fc63f3

def z1089 : W := mkw 0x08ed91bd03f403b0 0x7efff9ff03fc03f0

def z1090 : W := mkw 0x8101000904edbedd 0x09000000027f9fcc

def z1091 : W := mkw 0x2ffefff6fb1d91e8 0x76fffffffe1f81c0

def z1092 : W := mkw 0x94f7de0103db7811 0xfdfffe0003fffc33

def z1093 : W := mkw 0x222c21f6f8000000 0x123f01fffc000000

def z1094 : W := mkw 0x26fefff6f802c04a 0xfffffffffe03e3cf

def z1095 : W := mkw 0x26fefff6fb02c16a 0xf6fffffffd8063ff

def z1096 : W := mkw 0x243e4e9638091000 0x7dbfe61f1e7f9c00

def z1097 : W := mkw 0x253e4e96380d1080 0x103f061f1c1c0000

def z1098 : W := mkw 0x00020a0228000000 0x5e471e3ffd800230

def z1099 : W := mkw 0x243e4e9638000000 0x74bfe61f1c000000

def z1100 : W := mkw 0x0bfcf5f4d31fd1ea 0x20b8e1c0021f81c0

def z1101 : W := mkw 0x26ee9bb668000000 0x76ff1ffffc000000

def z1102 : W := mkw 0x26ee9bb678000000 0x0047183f7c000000

def z1103 : W := mkw 0x02e4b164c302c16a 0xefc7f9e7e383e3ff

def z1104 : W := mkw 0x26fefff6fb000120 0x76fffffffe0001c0

def z1105 : W := mkw 0x24fe4fb638000000 0x30bf07df1c000000

def z1106 : W := mkw 0x26eebbf6fb02c16a 0xefc7f9ffff83e3ff

def z1107 : W := mkw 0x14f7de022bdb7800 0x7dfffe1f1ffffc00

def z1108 : W := mkw 0x0901000904fd1694 0x00000000007c1c00

def z1109 : W := mkw 0x26f6df2668091000 0x7dfffe27627f9c00

def z1110 : W := mkw 0x001064488429964c 0x7fb8e7d89e7f9fcc

def z1111 : W := mkw 0x24260a0628000000 0x56471e3ffc000000

def z1112 : W := mkw 0x00020a0228002800 0x57471e3ffc007c00

def z1113 : W := mkw 0x00020a0228000000 0x14071e1ffc000000

def z1114 : W := mkw 0x8001000904e0ae5d 0x8900000003e3ffff

def z1115 : W := mkw 0x02c0b160c0008048 0xefc0f9e0e383e3ff

def z1116 : W := mkw 0x26fefff6f8002800 0x77fffffffc007c00

def z1117 : W := mkw 0x14f7de0003db7800 0x7ffffe2003fffe30

def z1118 : W := mkw 0x36e79b266bd26922 0x8047182761806033

def z1119 : W := mkw 0x01c821f8972487ec 0x6ac001f89f8003fc

def z1120 : W := mkw 0x9001000904f93e15 0x00000000007c1c00

def z1121 : W := mkw 0x011864d8942d96cc 0x39b8e7d81e7f9fcc

def z1122 : W := mkw 0x08ed01bd03f643b0 0x7bff01ff03ffe3f0

def z1123 : W := mkw 0x220821f6f8000000 0x524701fffc000000

def z1124 : W := mkw 0x26fefff6fb024000 0x76fffffffd806000

def z1125 : W := mkw 0x09ed21fd97f487fc 0x024701ff9d8003fc

def z1126 : W := mkw 0x220a2bf6f8000000 0x120707fffc000000

def z1127 : W := mkw 0x26fefff6f802c04a 0x76fffffffc038000

def z1128 : W := mkw 0x8ac1b169c7f6efff 0xefc0f9e0e3ffffff

def z1129 : W := mkw 0x00020a0228000000 0x1207063ffc000000

def z1130 : W := mkw 0x0010440000091000 0x7fb8e600827f9e0c

def z1131 : W := mkw 0x1437de0000db7800 0x103fe600007f9c00

def z1132 : W := mkw 0x8101000904ed3e95 0x8900000001fc7e3f

def z1133 : W := mkw 0x80030a0b2ce02e15 0x8900180061e07e3f

def z1134 : W := mkw 0x9001000907fbff7f 0x8900000003ffffff

def z1135 : W := mkw 0x14f74e0003d93800 0x7dffe60003ff9c00

def z1136 : W := mkw 0x00020a0228000000 0x5607061f9c000000

def z1137 : W := mkw 0x011a6ed2b80d90c8 0x76fffffffe1f81c0

def z1138 : W := mkw 0x27fefff6f80d90c8 0x7ffffffffe1f83cc

def z1139 : W := mkw 0x26e69b2668000000 0x10471e3f7c000000

def z1140 : W := mkw 0x2b0821fffc2487fc 0x020001fffc0003fc

def z1141 : W := mkw 0x1ced91bd03f643b0 0x7aff01ff03fc03f0

def z1142 : W := mkw 0x04364e0228000000 0x103f061f1c000000

def z1143 : W := mkw 0x00ed01bc03f40280 0x7aff01ff03fc03c0

def z1144 : W := mkw 0x14f7de0000db7800 0x75fffe00007ffc00

def z1145 : W := mkw 0x26d2ff62fb02c16a 0xffc7ffffff83e3ff

def z1146 : W := mkw 0x24260a0628000000 0x1007061f1c000000

def z1147 : W := mkw 0x26fefff6f8000000 0x7efffffffd800230

def z1148 : W := mkw 0x08ed01b403d401a0 0x7aff01ff03fc01c0

def z1149 : W := mkw 0x14f7de0003db7800 0x157ffe0001fffc00

def z1150 : W := mkw 0x14f7de0003db7922 0xfdfffe0003fffc33

def z1151 : W := mkw 0x243ede9638000000 0x143ffe1f1c000000

def z1152 : W := mkw 0x011864d0900d90c8 0x7fb8e7d89e7f9dc0

def z1153 : W := mkw 0x8201b049c4e2ee5f 0x8d00f800e1e3fe3f

def z1154 : W := mkw 0x26fefff6fb02c16a 0x7effffffff8383f0

def z1155 : W := mkw 0x1ef7df2543db7932 0xfdfffe2763fffc33

def z1156 : W := mkw 0x26fefff6fb00816a 0xfeffffffff8003ff

def z1157 : W := mkw 0x253e6ed6b80d90c8 0x30bfe7df1e1f81c0

def z1158 : W := mkw 0x011864d8942d96cc 0x7ff8fff8fe7f9fcc

def z1159 : W := mkw 0x04fefed2b8000000 0x76fffffffc000000

def z1160 : W := mkw 0x02eebbf6eb02c16a 0xffffffffff83e3ff

def z1161 : W := mkw 0x80020a0228002801 0xd6471e3ffc006003

def z1162 : W := mkw 0x0901000907f487fc 0x0800000003fc03fc

def z1163 : W := mkw 0x08ed01bd07f407b4 0x7bff01ff03fc1ffc

def z1164 : W := mkw 0x36fefff6fb1bd16a 0xffffffffff9fe3ff

def z1165 : W := mkw 0x8001000904e02e15 0x0900000000601e0c

def z1166 : W := mkw 0x22ec21f6f8000000 0x024701fffc000000

def z1167 : W := mkw 0x0010440000091000 0x7df8fe0003fffc00

def z1168 : W := mkw 0x14124e0000093800 0x7db8e600027f9c00

def z1169 : W := mkw 0x8801000904e42fb5 0x8900000001e07fff

def z1170 : W := mkw 0x02c0b160c302c16a 0x8740f9e0e183e3ff

def z1171 : W := mkw 0x26fefff6fb000000 0x7effffffff800000

def z1172 : W := mkw 0x00020a0228000000 0x10471e3f7c000000

def z1173 : W := mkw 0x2efefff6fb16c1ea 0xffffffffff9fe3ff

def z1174 : W := mkw 0x00e60b2628000000 0x56471e3ffc000000

def z1175 : W := mkw 0x80c1012907e02f35 0xebc001e003e07fff

def z1176 : W := mkw 0x26fefff6fb024122 0xffffffffff83e033

def z1177 : W := mkw 0x1412de00000b7800 0x1538fe00007ffc00

def z1178 : W := mkw 0x04fefff490000000 0x76ffffff9c000000

def z1179 : W := mkw 0x00fc65f493008168 0x7fffe7ff9f8383fc

def z1180 : W := mkw 0x8001000904e0af7f 0x8900000001e07fff

def z1181 : W := mkw 0x02c0b160c302c16a 0xa9c0f9e06383e3ff

def z1182 : W := mkw 0x27fcf5f4d30fd1ea 0x20b8e1c0021f81c0

def z1183 : W := mkw 0x36fefff6fb1b5000 0x7fffffffff9fe000

def z1184 : W := mkw 0x24fedfb638000000 0x76ffffff1c000000

def z1185 : W := mkw 0x010820d8942486cc 0x000000189c00000c

def z1186 : W := mkw 0x8801000904f42e95 0x8900000001fc7e3f

def z1187 : W := mkw 0x082d01bd00f403b0 0x5a7f01ff01fc03f0

def z1188 : W := mkw 0x04f6de00030b5000 0x7dfffe0003fffc00

def z1189 : W := mkw 0x03c8b1f8d726c7ee 0x824019f8fd8063ff

def z1190 : W := mkw 0x011864d8942d96cc 0xffb8e7f8fe7f9fff

def z1191 : W := mkw 0x08ed01bd03f403b0 0x7fffe1ff03ff83f0

def z1192 : W := mkw 0x00020a0228000000 0x5247063f1c000000

def z1193 : W := mkw 0x96e79b236bd26933 0x8047182761806033

def z1194 : W := mkw 0x08ed01bd03f403b0 0x78ff01df03fc01c0

def z1195 : W := mkw 0x26fefff6fb02c16a 0x30bfe7df1e0381c0

def z1196 : W := mkw 0x08ed01bd03f42bb0 0x7bff01ff03fc7ff0

def z1197 : W := mkw 0x08ed01bd03f403b0 0xfaff19ff63fc63f3

def z1198 : W := mkw 0x0010440000091000 0x7fb8e6189e7f9c00

def z1199 : W := mkw 0x81126e42bc09bc4d 0x0500e6009c039c0c

def z1200 : W := mkw 0x22cabbf6fb02c16a 0xffc7ffffff83e3ff

def z1201 : W := mkw 0x26f6fe42f8000000 0x76fffe3ffc000000

def z1202 : W := mkw 0x14374e0003db7800 0x7dbfe60003fffc00

def z1203 : W := mkw 0x26fefff6fb100000 0x76fffffffe1c0000

def z1204 : W := mkw 0x003c449410000000 0x103f061f1c000000

def z1205 : W := mkw 0x001a6ed2b8008048 0xffffffffff83e3ff

def z1206 : W := mkw 0x00124e0000093800 0x7db8fe00027ffc00

def z1207 : W := mkw 0x26fefff6fb0b5000 0x7ffffffffffffc00

def z1208 : W := mkw 0x26fefff6fb008168 0x7fffffffff8383fc

def z1209 : W := mkw 0x82c1912947e26f37 0x8940182061e07e3f

def z1210 : W := mkw 0x22020b2668000000 0x56471e3ffc000000

def z1211 : W := mkw 0x1437de0000db7800 0x5d7ffe0001fffc00

def z1212 : W := mkw 0x82c1b169c7e2ef7f 0xa980e1c003e3ffff

def z1213 : W := mkw 0x14374e0000d93800 0x7dfffe0003fffc00

def z1214 : W := mkw 0x011864d8942d96cc 0x7ff8e7f89fff9ffc

def z1215 : W := mkw 0x8001000904e02e15 0x0900000001e07c00

def z1216 : W := mkw 0x00022a42a8008048 0x7fc7fffffe0383cc

def z1217 : W := mkw 0x8001000904e42e95 0x8900000003fc7fff

def z1218 : W := mkw 0x26fcf5f4d0000000 0x76ffe7ff9c000000

def z1219 : W := mkw 0x26fefff6f800804a 0xf6fffffffc00000f

def z1220 : W := mkw 0x08ed01bd03f403b0 0x7fff19ff03fc63f0

def z1221 : W := mkw 0x10f5440003db7800 0x7dffe60003fffc00

def z1222 : W := mkw 0x0412de0000091000 0x7db8fe00027f9c00

def z1223 : W := mkw 0x0011440000c93800 0x7db8e60003fffc00

def z1224 : W := mkw 0x08ed01bd03f403b0 0xfbff01ff03fc63ff

def z1225 : W := mkw 0x26fefff6f8000000 0xf6fffffffc00023f

def z1226 : W := mkw 0x14f7de0003db7800 0xfdfffe0003fffe3f

def z1227 : W := mkw 0x8001000907e02f35 0x8900000003e07fff

def z1228 : W := mkw 0x082d009d03f403b0 0x7abf01df03fc03f0

def z1229 : W := mkw 0x011864d8942d96cc 0x35b8e7d89e7f9dcc

def z1230 : W := mkw 0x26fefff6fb02c16a 0xf6fffffffe0383ff

def z1231 : W := mkw 0x08ed01bd03f403b0 0x7fff01ff83fc03fc

def z1232 : W := mkw 0x08ed01b503d401b0 0x72ff01ff039c01f0

def z1233 : W := mkw 0x08ed01bd07f407b4 0x7aff07ff1ffc1ff0

def z1234 : W := mkw 0x37fefff6fb1fd0c8 0x76fffffffe1f81c0

def z1235 : W := mkw 0x2efefff6f80401a0 0x76fffffffc0001c0

def z1236 : W := mkw 0x3712fe42fc0bfc4c 0x0500fe00fc03fc0c

def z1237 : W := mkw 0x011864d8942d96cc 0x32b8e7d89e7f9fcc

def z1238 : W := mkw 0x8001000904e00615 0x8800000001e0023f

def z1239 : W := mkw 0x8101000907efffff 0x8900000003ffffff

def z1240 : W := mkw 0x263e6ed6f8000000 0x103f061ffc000000

def z1241 : W := mkw 0x26fefff6fb024122 0x76fffffffc000000

def z1242 : W := mkw 0x00020a0228000000 0x0247183ffc000000

def z1243 : W := mkw 0x00124e0228000000 0x76fffe3ffc000000

def z1244 : W := mkw 0x80030a0b2ce42e95 0xdf471e3ffffc7fff

def z1245 : W := mkw 0x22ecb1f6f8000000 0x76fff9fffc000000

def z1246 : W := mkw 0x08ed01b503d401b0 0x20bf01c7021c01c0

def z1247 : W := mkw 0x22fc65f6f8000000 0x76ffe7fffc000000

def z1248 : W := mkw 0x02dafff2fb02c16a 0xffffffffff83e3ff

def z1249 : W := mkw 0x02c2bb62eb02c16a 0x76c7fffffe0381c0

def z1250 : W := mkw 0xb6f7df276bdb7811 0xfdfffe2763fffc33

def z1251 : W := mkw 0x00c0b0408302c048 0xefc0f9e0e383e3ff

def z1252 : W := mkw 0x011864d9942d96dc 0x7fb8e7ff9e7f9ffc

def z1253 : W := mkw 0x9413de0904eb7e15 0x8d00fe0001e3fe3f

def z1254 : W := mkw 0x88ed01bd07f42fb5 0xa9b801c003fc7fff

def z1255 : W := mkw 0x2612fe42f8000000 0x1407fe1ffc000000

def z1256 : W := mkw 0x16f7df2043db7922 0xfffffe20e3fffe3f

def z1257 : W := mkw 0x01184498142d1684 0x7fb8e7d81e7f9fc0

def z1258 : W := mkw 0x26fefff6fb024000 0x76fffffffe038000

def z1259 : W := mkw 0x10104400000b7800 0x7db8e600027ffc00

def z1260 : W := mkw 0x0901000907fd17b4 0x0800000003fc1ff0

def z1261 : W := mkw 0x14f4d400031b5000 0x29b8e000027f9c00

def z1262 : W := mkw 0x14f5d40003db7800 0x20b8e000027f9c00

def z1263 : W := mkw 0x010820d9942486dc 0x020001ff9c0003fc

def z1264 : W := mkw 0x00020a0228000000 0x54471e1f1c000000

def z1265 : W := mkw 0x2612fe42f802c04a 0xdf47fe3ffd83e23f

def z1266 : W := mkw 0x04f6de0228000000 0x74fffe1f1c000000

def z1267 : W := mkw 0x810820dabc2486cd 0x820001d8fc0003cf

def z1268 : W := mkw 0x26fefff6f8000000 0xf6fffffffd806033

def z1269 : W := mkw 0x00c901b903e403b0 0x7aff01ff03fc03f0

def z1270 : W := mkw 0x082d009d00f40290 0x30bf01df027c01c0

def z1271 : W := mkw 0x26fefff6f8000000 0x7efffffffe0003c0

def z1272 : W := mkw 0x16e4b160c312c16a 0xefc0f9e0e383e3ff

def z1273 : W := mkw 0x26fefff6fb02c16a 0xf6ffffffff83e1f3

def z1274 : W := mkw 0x26fefff6f8008048 0x77fffffffc03800c

def z1275 : W := mkw 0x3ee79b276bd26930 0x0047182761806030

def z1276 : W := mkw 0x2eed91bd43f403b0 0x7aff01ff03fc03f0

def z1277 : W := mkw 0x26fe6ff6f8000000 0x72ff07fffc000000

def z1278 : W := mkw 0x26fcf5f6f8000000 0x72ffe1fffc000000

def z1279 : W := mkw 0x14f7df2003db7800 0x7fffffe003fffc00

def z1280 : W := mkw 0x16f7df2043db7922 0x7dfffe0003fffc00

def z1281 : W := mkw 0x8801000904f42e95 0x00000000007c1c00

def z1282 : W := mkw 0x090820dd942486dc 0x020001df9c0003cc

def z1283 : W := mkw 0x14f7de0003db7920 0x7dfffe0003fffff0

def z1284 : W := mkw 0x14f7de022bdb7800 0x7dfffe2763fffc00

def z1285 : W := mkw 0x9c3f4e9f2cfd3e95 0x103f061f1c7c1c00

def z1286 : W := mkw 0x08ed91bd03f643b0 0xfffff9ffe3ffe3ff

def z1287 : W := mkw 0x08ec01b4031401a0 0x20ff01e7021c01c0

def z1288 : W := mkw 0x8001000904e02e15 0x8100000000607c0f

def z1289 : W := mkw 0x34f7de062bdb7800 0x7dfffe0703fffc00

def z1290 : W := mkw 0x25126e42bc09944c 0x0500e6009c039c0c

def z1291 : W := mkw 0x04f7de0000c93800 0x7dfffe0003fffc00

def z1292 : W := mkw 0x26d2ff62f8000000 0x76c7fffffc000000

def z1293 : W := mkw 0x08ed01bd03f403b0 0x28ff01e703fc03f0

def z1294 : W := mkw 0x8801000907f6efff 0x8900000003ffffff

def z1295 : W := mkw 0x00c29a0228000000 0x76c7fe3ffc000000

def z1296 : W := mkw 0x14f6de00031b5000 0x7dfffe00027f9c00

def z1297 : W := mkw 0x26e4b164c302c16a 0xefc0f9e0e383e3ff

def z1298 : W := mkw 0x90c1900907fb7e15 0xefc0f820e3fffe3f

def z1299 : W := mkw 0x08ed01bd03f403b0 0xfaff01ffe3fc03ff

def z1300 : W := mkw 0x00f74e0003d93800 0x7dfffe0003fffc00

def z1301 : W := mkw 0x14f7df2403db7800 0x7dfffe2703fffc00

def z1302 : W := mkw 0x002c009c00240280 0x7abf01df027c03c0

def z1303 : W := mkw 0x343ede96380b7800 0x153ffe1f1c03fc00

def z1304 : W := mkw 0x88c1012907f42fb5 0xefc019e0e3fc7fff

def z1305 : W := mkw 0x243e6ed6b8008048 0x7fbfe7df9e0383cc

def z1306 : W := mkw 0x0200b040c302c16a 0xef80f9c0e383e3ff

def z1307 : W := mkw 0x00c29a022b024000 0x7fc7fe3fff83e000

def z1308 : W := mkw 0x36fefff6f8191000 0x76fffffffc1c0000

def z1309 : W := mkw 0x0809009903f403b0 0x7aff01ff03fc03f0

def z1310 : W := mkw 0x263efed6f8000000 0x567ffe3ffc000000

def z1311 : W := mkw 0x36fefff6fb1bd16a 0x76fffffffe1f81c0

def z1312 : W := mkw 0x00ee0bb628000000 0x72ff07ff1c000000

def z1313 : W := mkw 0x00030a0228c02800 0xdf471e3ffde07e3f

def z1314 : W := mkw 0x22ee2bf6f8000000 0x76ff1ffffc000000

def z1315 : W := mkw 0xa53f4e9f3ced3e95 0x103f061f1c7c1c00

def z1316 : W := mkw 0x220a2bf6f800816a 0xdf471ffffd8063ff

def z1317 : W := mkw 0x1434440000191000 0x7db8e600027f9c00

def z1318 : W := mkw 0x16f7df2043db7922 0xffffffe063fffff3

def z1319 : W := mkw 0x36f7df2443db7800 0x7dfffe0003fffc00

def z1320 : W := mkw 0x2efefff6f8140080 0x76fffffffc1c0000

def z1321 : W := mkw 0x243e6ed6b8000000 0x123f07df9c000000

def z1322 : W := mkw 0x24fe4fb63b000120 0x7aff07ff1f8003f0

def z1323 : W := mkw 0x0009009900e40290 0x7abf01df027c03c0

def z1324 : W := mkw 0x04f7de0003d91000 0x7dfffe0003ff9c00

def z1325 : W := mkw 0x0200b040c002c04a 0xefc0f9e0e383e3ff

def z1326 : W := mkw 0x8001000904e2ee5f 0x8900000001e3fe3f

def z1327 : W := mkw 0x00d0452003091120 0x7ff8e7e003ff9ff0

def z1328 : W := mkw 0x0010d400000b5000 0x7db8fe00027ffc00

def z1329 : W := mkw 0x00020a0228000000 0xd7471e3ffc00600f

def z1330 : W := mkw 0x0202ba42e802c04a 0xd747fe3ffc03e00f

def z1331 : W := mkw 0x02e4b160c312c16a 0xeff8f9e0e39fe3ff

def z1332 : W := mkw 0x04f4d40000091000 0x7db8e600027f9c00

def z1333 : W := mkw 0x08ed01bd07f407b4 0xffff1ffffffc7fff

def z1334 : W := mkw 0x06f6ff62e8000000 0x76fffffffc000000

def z1335 : W := mkw 0x1413de0003db7800 0x7db8fe0003fffc00

def z1336 : W := mkw 0x80030a032cc02c15 0xd7471e3ffd807c3f

def z1337 : W := mkw 0x1412de02280b7800 0x5747fe3ffc03fc00

def z1338 : W := mkw 0x14f7de0000d93800 0x7dfffe00027f9c00

def z1339 : W := mkw 0x031864d8d42d96ce 0xffb8e7d8fe7f9fcf

def z1340 : W := mkw 0x00104400030b5000 0x7db8e60003fffc00

def z1341 : W := mkw 0x08ed01b503d401b0 0x78ff01e703fc01f0

def z1342 : W := mkw 0x00ed01bd00e40290 0x7aff01ff03fc03f0

def z1343 : W := mkw 0x2efefff6fb1401a0 0x7effffffff9c03f0

def z1344 : W := mkw 0x263efed6f8000000 0x103fe61f1c000000

def z1345 : W := mkw 0x1cf7de0503db7810 0x7dfffe0703fffc00

def z1346 : W := mkw 0x09fc65f4931d91e8 0x76ffe7ff9e1f81c0

def z1347 : W := mkw 0x22cabbf6f8000000 0x76c7fffffc000000

def z1348 : W := mkw 0x030821f8d42486cc 0x020001f8fc0003cc

def z1349 : W := mkw 0x14f7de0003db7800 0x35bffe00027ffc00

def z1350 : W := mkw 0x0202ba42e8000000 0x5647fe3ffc000000

def z1351 : W := mkw 0x14f7de0003db7800 0x39bfe60003fffc00

def z1352 : W := mkw 0x26fefff6fb02c048 0x7fffffffff83e3cc

def z1353 : W := mkw 0x82012169c4e0af7f 0x8b0001e0e1e07fff

def z1354 : W := mkw 0x0011440003d91000 0x7db8e60003ff9c00

def z1355 : W := mkw 0x36fefff6f80b5000 0x76fffffffc038000

def z1356 : W := mkw 0x08ed01bd03f403b0 0x32bf01ff027c03f0

def z1357 : W := mkw 0x36fefff6f80b7800 0x7ffffffffe7ffc00

def z1358 : W := mkw 0x000820d8842486cc 0x7fb8e7d89e7f9fcc

def z1359 : W := mkw 0x24fede963b024000 0x7dfffe1f1f83e000

def z1360 : W := mkw 0x36fefff6f8026800 0x76fffffffc006000

def z1361 : W := mkw 0x8001000907e26e15 0x8900000003e3fe3f

def z1362 : W := mkw 0x9612fe42ec0bfc4f 0x8500fe00fc03fc0f

def z1363 : W := mkw 0x26fefff6f8000000 0x32bfe7fffc000000

def z1364 : W := mkw 0x000a0a9228000000 0x76ff1ffffc000000

def z1365 : W := mkw 0x96f7df236bdb7933 0xfdfffe2763fffc33

def z1366 : W := mkw 0x36fefff6f80bf84a 0xf7fffffffc03fc0f

def z1367 : W := mkw 0x001a4e9238000000 0x567f1e3ffc000000

def z1368 : W := mkw 0x9512fe42bc0bfc4d 0x8500fe00fc03fc0f

def z1369 : W := mkw 0x263e6ff6f8000000 0x567f1ffffc000000

def z1370 : W := mkw 0x010820d8942487ee 0x820001d89c0003ff

def z1371 : W := mkw 0x26e69b2668000000 0x0247183ffc000000

def z1372 : W := mkw 0x26fefff6f8000122 0xf6fffffffc000033

def z1373 : W := mkw 0x14f7de0003db7800 0x30fffe0003fffc00

def z1374 : W := mkw 0x18ed01bd03f66bb0 0x7aff01ff03fc63f0

def z1375 : W := mkw 0x263efff6f8000000 0x163ffffffc000000

def z1376 : W := mkw 0x34fede963b1b5000 0x30bfe61f1e1f8000

def z1377 : W := mkw 0x010820d8942486cc 0x000001c0000003cc

def z1378 : W := mkw 0x00d3de0003cb7800 0x7dfffe0003fffc00

def z1379 : W := mkw 0x00020a0228000000 0x5f471e3ffc00020c

def z1380 : W := mkw 0x0010440000091000 0x7fb8e7c0027f9fc0

def z1381 : W := mkw 0x14f7de0003db7800 0x2db8fe0003fffc00

def z1382 : W := mkw 0x00c20b2228000000 0x76c71ffffc000000

def z1383 : W := mkw 0x26fefff6f8000000 0x72ffe7ff1c000000

def z1384 : W := mkw 0x36fefff6fb0bf96a 0xffffffffff83ffff

def z1385 : W := mkw 0x2cfe4fb63b1401a0 0x30bf07df1e1c01c0

def z1386 : W := mkw 0x26029a0268000000 0x56471e3ffc000000

def z1387 : W := mkw 0x14f7de0003db7800 0xfdfffe2063fffc33

def z1388 : W := mkw 0x810820dbbc2486dd 0x020001df9c0003cc

def z1389 : W := mkw 0x26e69b266b024122 0xdf471e3ffd80623f

def z1390 : W := mkw 0x8001000907f02e15 0x8900000003fc7e3f

def z1391 : W := mkw 0x261afff6f8000000 0x5647fffffc000000

def z1392 : W := mkw 0x94f7de032bdb7811 0xfffffe3ffffffc33

def z1393 : W := mkw 0x27fefff6fb0fd1ea 0xffffffffff9fe3ff

def z1394 : W := mkw 0x263e6ff6f8000000 0x103f07df1c000000

def z1395 : W := mkw 0x0111644994e9965c 0x5f47e63f9de39e3c

def z1396 : W := mkw 0x8001000904e02e15 0x0800000001e01e30

def z1397 : W := mkw 0x1437de0000db7800 0x7dbffe00027ffc00

def z1398 : W := mkw 0x8a0821ffec2487ff 0x820001fffc0003ff

def z1399 : W := mkw 0x2efefff6fb16c1ea 0x76fffffffe1f81c0

def z1400 : W := mkw 0x14f7df2003db7920 0xffffffe0e3ffffff

def z1401 : W := mkw 0x14f7de0103db7810 0x7dfffe2703fffc30

def z1402 : W := mkw 0x10134e0003db7800 0x7dfffe0003fffc00

def z1403 : W := mkw 0x36fefff6fb0b7800 0x7fffffffff83fc00

def z1404 : W := mkw 0x2efefff6fb100120 0x76fffffffc000000

def z1405 : W := mkw 0x1437de0003db7800 0x1d3ffe0003fffc00

def z1406 : W := mkw 0x263e6ff6f8000000 0x76bfe7fffc000000

def z1407 : W := mkw 0x14f7de0003db7800 0x7dbfe600027f9c00

def z1408 : W := mkw 0x011064409409944c 0x7fb8e7c09e7f9fcc

def z1409 : W := mkw 0x00f5d40003db5000 0x7dfffe0003fffc00

def z1410 : W := mkw 0x00ee0bb62b000120 0xffff1fffff8063ff

def z1411 : W := mkw 0x890821ffbc2487fd 0x820001fffc0003ff

def z1412 : W := mkw 0x02c29b2268000000 0x56471e3ffc000000

def z1413 : W := mkw 0x00e5012903f00330 0x7aff01ff03fc03f0

def z1414 : W := mkw 0x08ec01bd002403b0 0x7aff01ff027c03f0

def z1415 : W := mkw 0x202c009638000000 0x103f001f1c000000

def z1416 : W := mkw 0x0200b160c002c16a 0xcf40f9e0e183e3ff

def z1417 : W := mkw 0x082d01bd00f403b0 0x103f01df007c01c0

def z1418 : W := mkw 0x8001000907e26f37 0x8900000001e07e3f

def z1419 : W := mkw 0x1901000907fffffc 0x0900000003fffffc

def z1420 : W := mkw 0x011864d8942d96cc 0x7db8e7d81e7f9dc0

def z1421 : W := mkw 0x04364e0228000000 0x567f1e3ffc000000

def z1422 : W := mkw 0x243e6ed6b8000000 0x76fffffffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z7]),(0,[z0,z1,z3,z4,z5,z6,z8]),(0,[z0,z1,z3,z4,z9,z6,z10])],[(0,[z0,z1,z11,z4,z5,z6,z12]),(1,[z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z3,z4,z5,z6,z14]),(0,[z15,z0,z1,z3,z16,z4,z6]),(0,[z0,z1,z3,z4,z5,z17,z6])],[],[(0,[z0,z1,z3,z4,z5,z18,z6]),(0,[z15,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z20,z6])],[(1,[z21,z0,z1,z3,z5,z6]),(0,[z22,z0,z1,z23,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z24])],[(0,[z25,z0,z1,z3,z4,z5,z6]),(0,[z26,z15,z0,z1,z3,z4,z6]),(1,[z27,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z28,z4,z5,z6]),(0,[z0,z1,z3,z4,z29,z5,z6]),(0,[z0,z1,z3,z4,z30,z9,z6]),(0,[z0,z1,z3,z4,z31,z9,z6])],[(0,[z32,z0,z1,z3,z4,z5,z6]),(0,[z33,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z6,z34])],[(0,[z0,z1,z3,z4,z35,z36,z6]),(0,[z21,z0,z1,z3,z5,z6,z37]),(0,[z0,z1,z3,z4,z38,z5,z6]),(0,[z0,z39,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z40,z6])],[(0,[z21,z0,z1,z3,z36,z5,z6]),(0,[z0,z41,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z42,z5,z6])],[(0,[z0,z1,z43,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z44,z6]),(0,[z0,z45,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z46]),(0,[z0,z1,z47,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z48]),(0,[z0,z1,z3,z4,z36,z49,z6]),(0,[z0,z1,z3,z50,z4,z19,z6]),(0,[z0,z1,z51,z3,z4,z36,z6]),(0,[z0,z1,z52,z3,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z53,z6]),(0,[z54,z0,z1,z3,z4,z5,z6]),(0,[z0,z55,z1,z3,z4,z5,z6])],[(0,[z56,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z57,z5,z6])],[(0,[z0,z1,z58,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z5,z6,z59]),(0,[z0,z1,z3,z60,z4,z19,z6]),(0,[z0,z1,z3,z4,z61,z5,z6]),(0,[z62,z0,z1,z3,z4,z5,z6]),(1,[z63,z0,z1,z3,z4,z6]),(0,[z0,z1,z64,z3,z4,z5,z6])],[(0,[z65,z0,z1,z3,z4,z5,z6]),(0,[z0,z66,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z67])]],
   [[(0,[z68,z0,z1,z3,z4,z5,z6]),(0,[z69,z22,z0,z1,z3,z5,z6]),(0,[z70,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z51,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z71,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z72]),(0,[z73,z0,z1,z3,z5,z6,z14]),(0,[z0,z1,z52,z3,z4,z5,z12]),(0,[z0,z1,z3,z5,z74,z6,z59])],[(0,[z75,z0,z76,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z60,z4,z6]),(0,[z0,z1,z3,z4,z77,z19,z6]),(0,[z0,z1,z3,z4,z19,z78,z6])],[(0,[z22,z0,z1,z3,z16,z5,z6]),(1,[z0,z1,z3,z4,z79,z6])],[],[(0,[z80,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z82,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z83]),(0,[z0,z1,z84,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z86,z5,z6]),(0,[z87,z0,z1,z3,z4,z5,z6])],[(0,[z0,z88,z1,z3,z4,z5,z6]),(0,[z89,z21,z0,z1,z3,z5,z6])],[(0,[z0,z90,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z91]),(1,[z0,z1,z4,z5,z6,z92]),(0,[z0,z1,z3,z4,z5,z93,z6])],[(1,[z0,z1,z3,z5,z6,z94]),(0,[z0,z1,z3,z5,z49,z6,z94]),(0,[z0,z1,z3,z4,z95,z5,z6]),(0,[z0,z1,z3,z4,z5,z96,z6]),(0,[z0,z1,z3,z4,z5,z6,z59])],[(0,[z97,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z98,z5,z6])],[(0,[z0,z1,z3,z4,z5,z99,z6]),(0,[z15,z0,z100,z1,z3,z4,z6])],[(0,[z101,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z102,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z103]),(1,[z0,z1,z3,z104,z5,z6])],[(0,[z22,z105,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z50,z28,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z106])]],
   [[(0,[z0,z1,z107,z3,z4,z5,z6]),(0,[z15,z0,z45,z1,z3,z4,z6]),(0,[z0,z108,z1,z3,z4,z5,z6]),(0,[z109,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z52,z4,z110,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z111]),(0,[z0,z1,z3,z4,z112,z5,z6])],[(0,[z21,z0,z1,z52,z3,z5,z6]),(0,[z0,z113,z1,z3,z4,z114,z6]),(0,[z0,z1,z3,z4,z5,z115,z6])],[(0,[z116,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z117,z9,z6])],[(0,[z118,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z119,z9,z6]),(0,[z120,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z121,z3,z4,z5,z6])],[(0,[z0,z76,z1,z3,z4,z36,z6]),(0,[z22,z0,z1,z3,z60,z5,z6]),(0,[z21,z0,z1,z3,z5,z6,z12]),(0,[z0,z122,z1,z3,z4,z5,z6]),(0,[z123,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z124,z6]),(0,[z125,z0,z1,z3,z4,z36,z6]),(1,[z0,z1,z126,z3,z4,z6]),(1,[z0,z1,z3,z4,z6,z127]),(1,[z15,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z19,z6,z37]),(0,[z0,z1,z3,z4,z128,z5,z6])],[(0,[z0,z1,z3,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z130]),(0,[z131,z0,z1,z3,z4,z5,z6]),(0,[z0,z132,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z133,z5,z6])],[(0,[z125,z134,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z135,z4,z5,z6]),(0,[z0,z136,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z6,z59]),(0,[z0,z1,z3,z4,z79,z5,z6])],[(0,[z137,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z138,z4,z9,z6])],[(0,[z0,z1,z16,z4,z5,z6,z12])],[(0,[z0,z1,z3,z4,z5,z6,z139]),(0,[z0,z76,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z140,z4,z5,z6]),(0,[z105,z0,z1,z3,z4,z36,z6]),(0,[z141,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z142,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z143,z5,z6]),(0,[z144,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z145,z4,z5,z6])],[(0,[z0,z45,z1,z3,z4,z19,z6]),(0,[z101,z0,z1,z52,z4,z5,z6])],[(0,[z15,z0,z76,z1,z3,z4,z6]),(0,[z15,z22,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6,z146]),(0,[z0,z1,z147,z3,z4,z5,z6])]],
   [[(0,[z22,z0,z1,z3,z11,z5,z6]),(0,[z105,z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z110,z9,z6]),(0,[z0,z1,z3,z4,z5,z6,z148])],[(0,[z22,z0,z1,z3,z5,z74,z6]),(0,[z21,z0,z149,z1,z3,z5,z6]),(0,[z21,z0,z1,z3,z150,z5,z6]),(0,[z97,z0,z1,z3,z4,z151,z6]),(0,[z0,z1,z3,z152,z4,z5,z6])],[(1,[z0,z1,z3,z153,z5,z6]),(0,[z22,z0,z45,z1,z3,z5,z6]),(0,[z0,z1,z3,z154,z4,z5,z6]),(0,[z155,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z5,z156,z6])],[(0,[z22,z0,z1,z3,z5,z49,z6])],[(0,[z0,z1,z3,z4,z5,z157,z6]),(0,[z0,z158,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z159])],[(0,[z15,z0,z1,z23,z3,z4,z6]),(0,[z0,z1,z3,z160,z4,z5,z6])],[(0,[z134,z0,z1,z3,z4,z36,z6])],[(1,[z0,z1,z161,z3,z5,z6]),(0,[z0,z1,z3,z11,z4,z19,z6]),(0,[z0,z1,z3,z4,z162,z5,z6]),(0,[z0,z1,z3,z150,z4,z36,z6]),(0,[z0,z1,z163,z3,z4,z5,z6])],[(0,[z155,z0,z1,z3,z4,z9,z6])],[(0,[z118,z0,z45,z3,z4,z5,z6]),(0,[z0,z1,z23,z16,z4,z5,z6]),(0,[z0,z164,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z165,z5,z6]),(0,[z0,z1,z3,z166,z4,z5,z6])],[(0,[z167,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z168,z6]),(1,[z0,z1,z3,z4,z169,z6]),(0,[z0,z1,z3,z170,z4,z19,z6]),(1,[z0,z1,z3,z4,z171,z6])],[(0,[z134,z1,z3,z11,z4,z5,z6]),(0,[z0,z1,z3,z4,z172,z5,z6])],[(0,[z26,z1,z173,z3,z4,z5,z6]),(0,[z134,z0,z1,z3,z4,z9,z6])],[(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z53,z5,z6,z59]),(0,[z0,z149,z1,z3,z4,z5,z6]),(0,[z101,z0,z1,z3,z4,z110,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z150,z4,z9,z6])],[(0,[z175,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z176,z3,z4,z5,z6]),(0,[z0,z177,z1,z3,z4,z5,z6]),(1,[z101,z0,z1,z4,z117,z6])],[(0,[z0,z1,z173,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z178,z5,z6])]],
   [[(0,[z179,z75,z0,z3,z4,z5,z6]),(0,[z22,z0,z76,z1,z3,z5,z6]),(0,[z22,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z49,z6]),(0,[z0,z1,z3,z180,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z36,z6])],[(0,[z0,z1,z3,z4,z30,z36,z6]),(0,[z0,z181,z1,z3,z4,z5,z6])],[(0,[z15,z0,z1,z173,z3,z4,z6]),(0,[z182,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z151,z119,z6])],[(0,[z0,z1,z3,z4,z183,z5,z6]),(0,[z184,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z30,z5,z119,z6])],[(0,[z0,z1,z185,z3,z4,z5,z6]),(0,[z186,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z187,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z188,z5,z6]),(0,[z179,z0,z1,z3,z189,z5,z6]),(0,[z0,z1,z190,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z191,z6])],[(0,[z0,z1,z3,z4,z6,z127,z12])],[(0,[z21,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z192,z4,z5,z6]),(0,[z0,z1,z3,z4,z53,z9,z6]),(0,[z179,z0,z1,z3,z4,z5,z37])],[(0,[z0,z1,z3,z193,z5,z194,z6]),(0,[z0,z1,z3,z195,z4,z5,z6]),(0,[z0,z1,z3,z150,z53,z5,z6]),(0,[z196,z0,z1,z3,z4,z36,z6]),(0,[z197,z0,z1,z3,z4,z6,z12])],[(0,[z0,z1,z3,z4,z198,z5,z6]),(0,[z0,z1,z3,z4,z5,z199,z6]),(0,[z0,z1,z51,z3,z4,z30,z6])],[(0,[z0,z1,z3,z4,z36,z74,z6])],[(0,[z200,z0,z1,z3,z4,z5,z6])],[(0,[z70,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z201,z6]),(0,[z0,z1,z3,z4,z202,z5,z6]),(0,[z0,z1,z3,z4,z5,z203,z6])],[(0,[z0,z1,z3,z4,z193,z5,z6]),(0,[z0,z1,z3,z204,z4,z5,z6]),(0,[z0,z1,z3,z4,z9,z205,z6]),(0,[z0,z1,z3,z4,z5,z206,z6])],[(0,[z89,z0,z1,z3,z4,z5,z6]),(0,[z207,z0,z1,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z4,z9,z6])]],
   [[(0,[z15,z105,z0,z1,z3,z4,z6]),(0,[z208,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z163,z4,z9,z6])],[(0,[z0,z1,z3,z4,z5,z6,z209]),(0,[z0,z1,z3,z4,z9,z6,z210])],[(0,[z22,z1,z3,z4,z35,z5,z6])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z211,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z212,z4,z5,z6]),(0,[z15,z196,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6,z213]),(0,[z0,z1,z3,z214,z4,z5,z6]),(0,[z0,z1,z3,z215,z4,z5,z6]),(1,[z0,z1,z3,z4,z9,z6])],[(0,[z22,z0,z1,z173,z3,z5,z6]),(0,[z22,z0,z1,z3,z5,z216,z6]),(0,[z0,z1,z3,z217,z4,z5,z6])],[(0,[z0,z1,z187,z52,z4,z5,z6]),(0,[z21,z0,z1,z3,z5,z9,z6]),(0,[z0,z1,z3,z4,z218,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z219]),(0,[z0,z1,z3,z220,z4,z5,z6]),(0,[z0,z1,z3,z150,z5,z119,z6])],[(0,[z0,z1,z3,z221,z11,z4,z6]),(0,[z222,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z223,z4,z5,z6])],[(0,[z224,z22,z0,z1,z3,z5,z6]),(0,[z22,z0,z1,z3,z13,z5,z6]),(0,[z207,z21,z0,z1,z3,z5,z6]),(0,[z225,z1,z3,z4,z5,z49,z6])],[(0,[z0,z1,z3,z4,z5,z6,z226]),(0,[z182,z0,z3,z4,z36,z5,z6]),(0,[z0,z1,z23,z3,z77,z5,z6])],[(0,[z15,z0,z1,z3,z4,z151,z6]),(0,[z0,z1,z227,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z228])],[(0,[z22,z0,z1,z229,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z230,z6]),(0,[z0,z1,z23,z3,z4,z19,z6])],[(0,[z0,z1,z231,z3,z4,z5,z6]),(0,[z179,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z232,z6]),(1,[z21,z0,z1,z3,z9,z6]),(0,[z0,z1,z52,z3,z4,z36,z6])]],
   [[(0,[z0,z45,z1,z3,z4,z233,z6]),(0,[z0,z1,z3,z28,z4,z9,z6]),(0,[z0,z1,z3,z4,z5,z234,z6]),(0,[z0,z1,z3,z4,z5,z6,z235])],[(0,[z236,z0,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z11,z4,z6]),(0,[z0,z1,z3,z4,z30,z193,z6])],[(0,[z0,z1,z3,z237,z4,z5,z6]),(0,[z0,z76,z1,z3,z4,z238,z6]),(0,[z0,z1,z187,z3,z81,z5,z6]),(0,[z0,z1,z3,z4,z5,z216,z6]),(0,[z0,z1,z3,z239,z5,z49,z6]),(0,[z0,z1,z3,z138,z4,z30,z6]),(1,[z196,z0,z1,z3,z5,z59])],[(0,[z0,z1,z3,z4,z240,z5,z6]),(0,[z197,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z241,z6]),(0,[z0,z1,z47,z3,z4,z9,z6])],[(0,[z0,z1,z161,z173,z3,z5,z6]),(0,[z134,z0,z1,z187,z4,z5,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z138,z4,z36,z6]),(0,[z0,z1,z3,z4,z5,z243,z6]),(0,[z0,z1,z3,z4,z5,z244,z6]),(0,[z0,z1,z52,z3,z4,z9,z6])],[(0,[z134,z101,z0,z1,z4,z5,z6]),(0,[z0,z1,z245,z3,z4,z5,z6])],[(0,[z0,z1,z246,z3,z4,z5,z6]),(0,[z141,z0,z1,z3,z4,z19,z6])],[],[(0,[z0,z1,z3,z4,z247,z5,z6]),(0,[z21,z0,z1,z3,z35,z5,z6]),(0,[z179,z21,z0,z1,z3,z5,z6]),(1,[z0,z45,z248,z4,z5,z6]),(0,[z0,z1,z3,z249,z4,z5,z6]),(0,[z0,z1,z23,z3,z50,z5,z6])],[(0,[z0,z1,z3,z4,z250,z5,z6]),(0,[z0,z1,z3,z4,z251,z5,z6]),(0,[z0,z1,z3,z4,z252,z5,z6])],[(0,[z0,z1,z253,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z71,z6]),(0,[z254,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z16,z4,z19,z6]),(1,[z62,z0,z1,z3,z4,z6]),(0,[z0,z1,z51,z3,z4,z119,z6])],[(0,[z21,z75,z0,z1,z3,z5,z6]),(0,[z21,z1,z3,z60,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z255]),(0,[z0,z1,z248,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z256]),(0,[z0,z1,z3,z4,z257,z5,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z259,z0,z1,z3,z4,z5,z6])],[(0,[z175,z0,z1,z260,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z261])],[(0,[z262,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z186,z15,z0,z1,z3,z4,z6]),(0,[z263,z0,z1,z3,z4,z5,z6])],[(0,[z264,z0,z1,z3,z11,z4,z6]),(0,[z70,z1,z3,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z265]),(0,[z0,z1,z3,z4,z114,z5,z6]),(0,[z266,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z267,z5,z6]),(0,[z0,z1,z3,z4,z5,z268,z6]),(0,[z0,z1,z3,z4,z269,z5,z210])],[(0,[z26,z0,z1,z3,z4,z36,z6]),(0,[z270,z22,z0,z1,z3,z5,z6]),(0,[z271,z0,z1,z3,z4,z5,z6]),(0,[z272,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z273,z3,z4,z5,z6]),(0,[z101,z0,z1,z3,z4,z36,z6])],[(0,[z0,z1,z274,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z275,z6])],[(0,[z0,z276,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z9,z6])],[(1,[z73,z0,z1,z3,z5,z6])],[(0,[z21,z225,z0,z1,z3,z5,z6]),(0,[z0,z277,z1,z3,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z5,z6]),(0,[z278,z0,z1,z3,z4,z5,z6])],[(0,[z279,z22,z0,z1,z3,z5,z6]),(0,[z175,z0,z3,z4,z53,z5,z6]),(1,[z182,z0,z3,z4,z36,z6]),(1,[z0,z1,z3,z4,z280,z6])],[(0,[z26,z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z281,z3,z4,z5,z6]),(0,[z179,z0,z1,z3,z4,z79,z6]),(0,[z101,z0,z1,z3,z4,z9,z6])],[(0,[z15,z175,z0,z1,z3,z4,z6]),(0,[z282,z0,z1,z3,z4,z5,z6])],[(0,[z262,z21,z0,z1,z3,z5,z6])],[(0,[z283,z0,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z77,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z284])],[(0,[z0,z1,z3,z4,z285,z5,z6]),(0,[z15,z0,z1,z3,z4,z117,z6])],[(0,[z134,z105,z1,z3,z4,z5,z6]),(0,[z0,z1,z248,z52,z4,z5,z6])],[(0,[z22,z0,z1,z3,z5,z19,z6]),(0,[z0,z1,z3,z4,z5,z286,z6]),(0,[z287,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z288,z5,z6]),(0,[z0,z1,z3,z4,z289,z5,z6]),(0,[z0,z1,z47,z3,z5,z119,z6])],[(0,[z0,z1,z187,z3,z153,z5,z6]),(0,[z0,z1,z3,z4,z5,z290,z6]),(0,[z291,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z292,z6]),(0,[z0,z293,z1,z3,z4,z5,z6])]],
   [[(0,[z182,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z50,z4,z5,z6]),(0,[z0,z1,z3,z4,z294,z5,z6])],[(0,[z0,z1,z3,z4,z5,z74,z6]),(0,[z0,z1,z3,z4,z5,z6,z295])],[(0,[z254,z0,z1,z3,z4,z151,z6])],[(0,[z0,z1,z3,z60,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z77,z6]),(0,[z0,z1,z3,z4,z5,z296,z6])],[(0,[z15,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z138,z4,z119,z6]),(1,[z15,z0,z1,z3,z4,z9])],[(0,[z0,z1,z3,z4,z5,z297,z6]),(0,[z0,z1,z3,z4,z53,z36,z6]),(0,[z15,z0,z1,z3,z4,z6,z37]),(1,[z197,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z152,z4,z36,z6])],[(0,[z0,z76,z1,z3,z298,z5,z6]),(0,[z1,z3,z4,z193,z5,z151,z6]),(0,[z0,z1,z3,z4,z5,z299,z6])],[(0,[z0,z300,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z301,z4,z5,z6]),(0,[z0,z1,z3,z4,z77,z5,z6]),(0,[z302,z0,z1,z3,z4,z5,z6])],[(0,[z179,z15,z0,z1,z3,z4,z6]),(0,[z0,z303,z1,z3,z4,z5,z6])],[(0,[z21,z0,z0,z1,z3,z5,z6]),(0,[z304,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z305]),(0,[z0,z1,z3,z4,z5,z6,z306]),(0,[z307,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z308,z5,z6]),(1,[z0,z1,z3,z4,z71,z6]),(0,[z22,z175,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z19,z6]),(0,[z0,z1,z3,z309,z4,z5,z6])],[(0,[z0,z1,z3,z310,z4,z5,z6]),(0,[z97,z0,z1,z51,z3,z4,z6]),(0,[z0,z1,z3,z4,z19,z205,z6]),(0,[z311,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z312,z5,z6])],[(0,[z0,z1,z313,z3,z4,z5,z6]),(1,[z22,z0,z1,z3,z19,z6])],[(0,[z26,z0,z1,z3,z4,z314,z6]),(0,[z0,z1,z3,z315,z11,z5,z6])],[(0,[z0,z1,z3,z4,z19,z316,z6])]],
   [[(0,[z118,z0,z1,z3,z317,z5,z6]),(0,[z0,z1,z318,z3,z4,z5,z6]),(0,[z319,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z320,z4,z5,z6]),(0,[z21,z0,z1,z3,z269,z5,z6]),(0,[z97,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z321,z3,z4,z19,z6])],[(0,[z0,z1,z3,z4,z322,z5,z6]),(0,[z22,z0,z1,z3,z28,z5,z6]),(0,[z118,z0,z1,z3,z198,z5,z6]),(0,[z0,z149,z1,z3,z4,z36,z6]),(0,[z0,z1,z163,z3,z4,z9,z6])],[(0,[z0,z1,z3,z323,z4,z5,z6]),(1,[z0,z1,z223,z4,z5,z6])],[(0,[z0,z1,z324,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z5,z151,z6])],[(0,[z21,z0,z1,z187,z3,z5,z6]),(0,[z0,z1,z325,z3,z4,z5,z6])],[(0,[z26,z0,z76,z3,z4,z5,z6]),(0,[z0,z1,z3,z326,z4,z5,z6]),(1,[z0,z1,z3,z239,z5,z6]),(0,[z327,z0,z1,z3,z4,z5,z6])],[(0,[z328,z0,z1,z3,z4,z5,z6])],[(1,[z75,z76,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z9,z6,z14]),(0,[z0,z149,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z36,z19,z6]),(0,[z0,z329,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z330,z6])],[(0,[z254,z1,z3,z4,z193,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z331])],[(0,[z0,z1,z3,z332,z4,z5,z6]),(0,[z333,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z334,z6]),(0,[z15,z0,z1,z3,z4,z6,z6])],[(0,[z105,z0,z1,z187,z4,z5,z6]),(0,[z97,z21,z0,z1,z3,z5,z6]),(1,[z21,z0,z1,z3,z36,z6]),(1,[z225,z1,z3,z4,z5,z49]),(0,[z0,z1,z335,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z336,z5,z6])],[(1,[z337,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z338,z193,z5,z6]),(0,[z0,z1,z3,z28,z4,z36,z6]),(0,[z0,z339,z1,z3,z4,z5,z6]),(0,[z271,z15,z0,z1,z3,z4,z6])],[(0,[z340,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z47,z3,z4,z30,z6]),(0,[z15,z0,z1,z3,z104,z5,z6])],[(0,[z0,z1,z3,z4,z341,z5,z6]),(0,[z0,z1,z3,z4,z5,z342,z6]),(0,[z0,z343,z1,z3,z4,z5,z6])]],
   [[(0,[z344,z0,z1,z3,z11,z5,z6]),(0,[z21,z0,z1,z47,z3,z5,z6])],[(0,[z0,z1,z187,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z5,z151,z6]),(0,[z0,z1,z47,z3,z4,z36,z6]),(0,[z278,z15,z0,z1,z3,z4,z6])],[(0,[z345,z0,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z36,z5,z19,z6]),(0,[z15,z0,z1,z3,z4,z6,z12]),(0,[z0,z1,z3,z4,z5,z6,z346])],[(0,[z0,z1,z3,z4,z5,z347,z6]),(0,[z0,z45,z1,z3,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z5,z78])],[(0,[z21,z0,z1,z3,z30,z5,z6]),(0,[z348,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z138,z5,z6,z59])],[(0,[z75,z0,z173,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z349,z5,z6]),(0,[z0,z1,z3,z4,z350,z5,z6]),(1,[z21,z1,z3,z60,z5,z6]),(0,[z0,z1,z3,z351,z4,z5,z6]),(0,[z352,z0,z1,z3,z4,z5,z6]),(0,[z175,z0,z113,z3,z4,z5,z6]),(1,[z0,z3,z4,z36,z19,z6]),(0,[z0,z1,z3,z150,z4,z40,z6]),(0,[z0,z1,z3,z4,z292,z9,z6])],[(0,[z353,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z0,z113,z1,z3,z4,z19,z6]),(0,[z155,z0,z1,z4,z77,z5,z6]),(0,[z0,z1,z3,z4,z93,z9,z6])],[],[(0,[z354,z0,z1,z3,z4,z5,z6]),(0,[z134,z22,z0,z1,z3,z5,z6]),(0,[z0,z45,z1,z248,z4,z5,z6]),(0,[z355,z0,z1,z3,z4,z5,z6]),(1,[z125,z0,z1,z4,z5,z12]),(0,[z0,z1,z3,z4,z5,z6,z356]),(0,[z357,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z193,z9,z6]),(1,[z0,z1,z145,z4,z5,z6]),(0,[z0,z1,z3,z4,z358,z19,z6])],[(0,[z0,z1,z3,z4,z13,z5,z6]),(0,[z0,z359,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z194,z6]),(0,[z0,z1,z3,z360,z4,z5,z6]),(0,[z0,z1,z52,z3,z4,z330,z6])],[(0,[z361,z0,z1,z3,z4,z5,z6]),(0,[z362,z0,z1,z3,z4,z5,z6])],[],[(1,[z0,z1,z3,z4,z314,z6]),(0,[z0,z363,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z36,z151,z6])],[]],
   [[(0,[z225,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z170,z4,z5,z6]),(0,[z0,z1,z3,z4,z364,z5,z6])],[(0,[z0,z1,z3,z4,z5,z365,z6]),(0,[z21,z0,z1,z3,z5,z205,z6]),(0,[z0,z1,z366,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z9,z6,z59]),(0,[z367,z0,z1,z3,z4,z5,z6])],[(0,[z21,z0,z1,z3,z5,z119,z6]),(1,[z0,z1,z3,z4,z341,z6]),(0,[z101,z0,z1,z3,z4,z30,z6]),(0,[z0,z1,z47,z3,z138,z5,z6])],[(0,[z0,z1,z3,z221,z4,z5,z6]),(1,[z0,z1,z185,z4,z5,z6]),(0,[z368,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z369,z3,z4,z5,z6])],[(0,[z22,z0,z1,z3,z5,z117,z6]),(0,[z21,z0,z1,z3,z5,z6,z210]),(0,[z0,z1,z3,z4,z36,z188,z6]),(0,[z0,z1,z3,z4,z5,z6,z370]),(0,[z0,z1,z371,z3,z4,z5,z6])],[(0,[z0,z1,z173,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z372,z5,z6]),(0,[z15,z0,z1,z3,z4,z78,z6])],[(0,[z362,z21,z0,z1,z3,z5,z6]),(0,[z373,z0,z1,z3,z4,z5,z6]),(0,[z374,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z78,z6,z12])],[(0,[z0,z1,z3,z4,z5,z6,z375]),(0,[z0,z1,z3,z4,z5,z6,z376]),(0,[z0,z377,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z51,z3,z4,z6]),(0,[z378,z0,z1,z3,z4,z5,z6])],[(0,[z379,z0,z1,z3,z4,z5,z6])],[(0,[z380,z0,z1,z3,z4,z5,z6]),(0,[z179,z0,z1,z3,z4,z9,z6]),(1,[z0,z1,z3,z4,z381,z6]),(0,[z0,z1,z3,z4,z382,z5,z6])],[(0,[z383,z0,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z248,z3,z4,z6]),(0,[z15,z0,z1,z3,z50,z4,z6]),(0,[z0,z1,z4,z110,z5,z117,z6])],[(0,[z337,z0,z1,z4,z5,z151,z6]),(0,[z0,z113,z1,z3,z28,z5,z6])],[(0,[z384,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z385,z6]),(0,[z0,z1,z126,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z386,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z6])],[(0,[z387,z0,z1,z3,z4,z5,z6])],[(0,[z388,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z389,z6]),(0,[z0,z1,z3,z4,z5,z233,z6]),(0,[z0,z1,z3,z4,z93,z205,z6]),(0,[z15,z155,z0,z1,z3,z4,z6])],[(0,[z390,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z391,z5,z6])]],
   [[(0,[z392,z0,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z19,z6]),(0,[z0,z393,z1,z3,z4,z5,z6]),(0,[z179,z0,z1,z3,z4,z5,z205]),(0,[z394,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z47,z3,z4,z119,z6]),(0,[z0,z1,z3,z4,z5,z6,z395])],[(0,[z0,z1,z3,z396,z4,z5,z6]),(0,[z0,z397,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z117,z6])],[(0,[z398,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z248,z3,z4,z36,z6])],[(0,[z105,z0,z1,z11,z4,z5,z6]),(0,[z15,z0,z1,z3,z28,z4,z6])],[(0,[z118,z0,z3,z16,z4,z5,z6])],[(0,[z0,z1,z399,z3,z4,z5,z6])],[(0,[z0,z76,z1,z400,z4,z5,z6]),(1,[z134,z1,z11,z4,z5,z6])],[(0,[z401,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z402]),(0,[z0,z1,z248,z3,z4,z9,z6]),(0,[z403,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z126,z3,z4,z6,z37]),(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z405,z3,z4,z5,z6])],[(0,[z22,z0,z1,z51,z3,z5,z6]),(0,[z0,z1,z406,z3,z4,z5,z6])],[(0,[z407,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z408,z6]),(0,[z0,z1,z3,z4,z5,z409,z6])],[(0,[z410,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z411,z5,z6]),(0,[z175,z0,z1,z3,z4,z36,z6]),(0,[z412,z0,z1,z3,z4,z19,z6]),(0,[z179,z0,z413,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z5,z6,z59])],[(0,[z264,z0,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z248,z3,z5,z6]),(0,[z22,z0,z1,z3,z50,z5,z6]),(1,[z0,z1,z23,z50,z5,z6]),(0,[z0,z1,z414,z3,z4,z5,z6]),(0,[z266,z0,z1,z3,z4,z9,z6])],[],[(0,[z0,z1,z3,z4,z5,z415,z6]),(0,[z70,z21,z0,z1,z3,z5,z6]),(0,[z0,z416,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z417,z5,z6]),(0,[z0,z1,z418,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z117,z6])],[(0,[z225,z1,z173,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z238,z6]),(0,[z134,z0,z1,z11,z4,z5,z6]),(0,[z21,z0,z1,z3,z110,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z419]),(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z0,z420,z1,z3,z4,z5,z6])]],
   [[(0,[z22,z155,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z19,z119,z6])],[(0,[z0,z1,z3,z4,z421,z5,z6]),(0,[z0,z76,z1,z396,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z9,z6]),(0,[z422,z0,z1,z3,z4,z5,z6]),(0,[z423,z0,z1,z3,z4,z5,z6])],[(0,[z75,z76,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z424,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z6,z210]),(0,[z0,z1,z3,z4,z42,z5,z6])],[(0,[z0,z1,z425,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z288,z36,z6]),(0,[z0,z1,z23,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z426])],[(0,[z0,z413,z1,z3,z4,z19,z6]),(0,[z101,z0,z1,z3,z4,z119,z6]),(0,[z282,z0,z1,z3,z4,z9,z6])],[(0,[z21,z0,z1,z3,z4,z36,z6]),(1,[z0,z1,z3,z4,z269,z9])],[(0,[z410,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z19,z6,z14]),(0,[z427,z0,z1,z3,z4,z5,z6])],[(1,[z388,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z428]),(0,[z0,z1,z3,z4,z9,z49,z6]),(0,[z0,z1,z3,z4,z36,z6,z37]),(0,[z155,z0,z1,z23,z4,z5,z6]),(0,[z0,z1,z3,z429,z4,z5,z6])],[(0,[z0,z1,z23,z248,z4,z5,z6]),(0,[z0,z1,z430,z3,z4,z5,z6]),(0,[z0,z100,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z431,z4,z5,z6]),(0,[z432,z0,z1,z3,z4,z5,z6]),(0,[z125,z22,z0,z1,z3,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z9])],[(0,[z22,z0,z1,z3,z5,z6,z12])],[(0,[z0,z1,z3,z50,z4,z9,z6])],[(0,[z433,z0,z1,z3,z4,z5,z6]),(0,[z97,z254,z1,z3,z4,z5,z6]),(1,[z0,z1,z406,z4,z5,z6]),(0,[z0,z248,z3,z16,z4,z5,z6]),(0,[z0,z1,z3,z28,z5,z6,z59]),(0,[z0,z149,z3,z4,z5,z19,z6]),(0,[z15,z0,z1,z3,z4,z110,z6])],[(0,[z254,z0,z1,z51,z3,z4,z6]),(0,[z175,z0,z1,z3,z53,z5,z6]),(1,[z0,z1,z52,z4,z5,z78]),(0,[z0,z1,z3,z150,z5,z74,z6]),(0,[z0,z1,z3,z4,z5,z6,z434])],[(0,[z0,z1,z187,z3,z4,z36,z6]),(0,[z0,z1,z3,z60,z4,z9,z6]),(0,[z0,z1,z3,z4,z5,z435,z6]),(0,[z0,z1,z52,z3,z4,z5,z78]),(0,[z15,z0,z436,z1,z3,z4,z6])],[(0,[z97,z1,z3,z4,z5,z151,z6]),(1,[z118,z0,z16,z4,z5,z6]),(0,[z182,z0,z149,z3,z4,z5,z6]),(0,[z0,z1,z3,z437,z4,z5,z6]),(1,[z0,z1,z3,z4,z364,z6])]],
   [[(0,[z75,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z4,z110,z5,z6,z12])],[],[(1,[z22,z21,z1,z3,z5,z6]),(1,[z22,z1,z3,z35,z5,z6]),(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z5,z6])],[(0,[z131,z0,z1,z3,z4,z6,z14]),(0,[z0,z1,z3,z5,z119,z6,z59]),(0,[z438,z0,z1,z3,z4,z5,z6])],[(0,[z26,z22,z0,z1,z3,z5,z6]),(0,[z439,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z440,z3,z4,z5,z6]),(1,[z0,z1,z371,z3,z4,z6])],[(0,[z26,z0,z173,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z138,z5,z6]),(0,[z0,z1,z3,z4,z441,z5,z6])],[(0,[z21,z0,z1,z3,z53,z5,z6]),(0,[z15,z15,z0,z1,z3,z4,z6]),(0,[z311,z0,z1,z3,z4,z9,z6])],[(0,[z141,z21,z0,z1,z3,z5,z6])],[(0,[z442,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z81,z4,z5,z6]),(0,[z0,z1,z3,z443,z4,z5,z6])],[(0,[z444,z0,z1,z3,z4,z5,z6])],[(1,[z445,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z446])],[(0,[z0,z1,z3,z447,z4,z5,z6]),(0,[z22,z0,z1,z3,z5,z78,z6]),(0,[z254,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z448,z6])],[(0,[z0,z1,z449,z3,z4,z5,z6]),(0,[z0,z76,z1,z3,z349,z5,z6]),(0,[z21,z0,z1,z3,z220,z5,z6]),(0,[z0,z1,z3,z53,z77,z5,z6]),(0,[z0,z1,z3,z4,z5,z450,z6]),(0,[z0,z451,z1,z3,z4,z5,z6])],[]],
   [[(0,[z0,z1,z3,z11,z4,z5,z6]),(0,[z0,z452,z1,z3,z4,z5,z6]),(0,[z0,z1,z52,z3,z4,z364,z6])],[(0,[z118,z0,z1,z16,z4,z5,z6])],[(0,[z70,z225,z1,z3,z4,z5,z6]),(0,[z15,z118,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z453])],[],[(0,[z454,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z298,z5,z6]),(0,[z0,z1,z3,z4,z5,z455,z6]),(0,[z22,z21,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z456,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z457,z6]),(0,[z0,z1,z3,z4,z36,z6,z12])],[(0,[z458,z0,z1,z3,z4,z5,z6]),(0,[z179,z26,z0,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z459,z6]),(0,[z0,z1,z3,z4,z5,z460,z6]),(0,[z0,z1,z3,z4,z5,z461,z6]),(0,[z407,z15,z0,z1,z3,z4,z6])],[(0,[z179,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z5,z462,z6])],[],[(0,[z0,z1,z52,z11,z4,z5,z6]),(0,[z105,z0,z1,z16,z4,z5,z6]),(0,[z21,z0,z413,z1,z3,z5,z6]),(0,[z179,z0,z1,z223,z4,z5,z6]),(0,[z0,z1,z3,z463,z4,z5,z6])],[(0,[z0,z1,z3,z4,z35,z19,z6]),(1,[z0,z1,z3,z338,z5,z6]),(0,[z0,z1,z3,z4,z464,z19,z6]),(1,[z0,z1,z465,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z466,z6]),(0,[z0,z1,z3,z4,z5,z78,z6]),(0,[z63,z15,z0,z1,z3,z4,z6]),(1,[z15,z0,z1,z3,z42,z6])],[(1,[z0,z1,z396,z4,z5,z6]),(0,[z21,z0,z1,z3,z5,z6,z14]),(1,[z254,z1,z3,z4,z193,z6]),(1,[z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z467,z3,z4,z5,z6]),(0,[z15,z200,z0,z1,z3,z4,z6])],[(0,[z0,z1,z51,z3,z4,z19,z6])],[(0,[z21,z0,z113,z1,z3,z5,z6])],[(0,[z196,z22,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z317,z5,z6]),(1,[z0,z1,z3,z4,z114,z6]),(1,[z15,z0,z1,z3,z4,z210])],[(0,[z0,z1,z468,z3,z4,z5,z6]),(0,[z21,z0,z1,z469,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z470,z6]),(1,[z179,z0,z3,z4,z5,z37]),(1,[z0,z1,z3,z4,z40,z6])]],
   [[(0,[z22,z0,z1,z3,z5,z6,z37]),(0,[z0,z1,z471,z3,z4,z5,z6]),(0,[z0,z1,z472,z3,z4,z5,z6]),(1,[z0,z1,z3,z198,z5,z6]),(0,[z0,z1,z3,z4,z5,z408,z6])],[(0,[z22,z0,z452,z1,z3,z5,z6]),(0,[z22,z0,z1,z3,z36,z5,z6]),(0,[z182,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z1,z3,z4,z5,z473,z6]),(0,[z474,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z475,z3,z4,z5,z6])],[(0,[z0,z476,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z477])],[(1,[z22,z0,z1,z3,z5,z6])],[(0,[z75,z1,z3,z4,z5,z6,z14]),(0,[z134,z0,z1,z16,z4,z5,z6]),(0,[z22,z118,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z478]),(0,[z479,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z193,z119,z6]),(0,[z225,z0,z1,z3,z4,z36,z6])],[(1,[z0,z1,z3,z221,z4,z6]),(0,[z69,z0,z1,z3,z4,z5,z6]),(0,[z70,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z36,z78,z6])],[(0,[z0,z113,z1,z3,z4,z448,z6]),(0,[z15,z0,z1,z52,z3,z4,z6])],[],[],[(1,[z22,z0,z1,z3,z13,z6]),(0,[z21,z0,z1,z23,z3,z5,z6]),(0,[z225,z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z480,z19,z6]),(1,[z0,z413,z3,z4,z5,z205])],[(0,[z0,z1,z3,z481,z4,z5,z6]),(0,[z15,z0,z1,z482,z3,z4,z6])],[(0,[z483,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z484,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z37])],[(0,[z485,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z34])],[(0,[z0,z1,z3,z4,z5,z6,z486])]],
   [[(0,[z0,z1,z173,z3,z4,z9,z6]),(0,[z105,z0,z1,z4,z5,z78,z6])],[(0,[z0,z1,z3,z4,z5,z44,z6]),(0,[z0,z3,z28,z4,z53,z5,z6]),(1,[z0,z1,z3,z4,z93,z6]),(0,[z15,z0,z1,z3,z4,z36,z6])],[(0,[z0,z1,z3,z4,z5,z6,z487]),(0,[z378,z0,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z488,z5,z6])],[(0,[z21,z0,z1,z3,z5,z6,z59]),(0,[z489,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z490,z4,z5,z6])],[(0,[z118,z0,z1,z3,z4,z19,z6])],[(0,[z0,z76,z1,z3,z4,z19,z6]),(0,[z125,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z491,z4,z5,z6]),(0,[z0,z1,z492,z3,z4,z5,z6])],[(0,[z0,z1,z493,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z9,z6]),(0,[z384,z0,z1,z3,z4,z9,z6])],[(0,[z494,z0,z1,z3,z4,z5,z6]),(0,[z15,z0,z149,z1,z3,z4,z6]),(0,[z0,z1,z3,z50,z4,z36,z6]),(0,[z15,z0,z1,z3,z150,z4,z6])],[(0,[z485,z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z495])],[(0,[z22,z0,z1,z52,z3,z5,z6]),(0,[z21,z0,z1,z3,z16,z5,z6]),(0,[z0,z1,z3,z4,z496,z5,z6])],[(0,[z0,z1,z3,z60,z4,z36,z6]),(0,[z179,z0,z1,z465,z4,z5,z6]),(1,[z0,z1,z3,z4,z497,z6])],[(0,[z134,z0,z1,z4,z5,z78,z6]),(0,[z105,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z469,z3,z4,z5,z6]),(0,[z0,z113,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z150,z4,z5,z59]),(0,[z0,z1,z3,z4,z5,z6,z498])],[(0,[z101,z254,z0,z1,z3,z4,z6])],[],[(0,[z0,z499,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z6,z419]),(0,[z101,z0,z1,z4,z5,z117,z6]),(0,[z0,z1,z500,z3,z4,z5,z6])]],
   [[(0,[z141,z0,z1,z3,z4,z5,z6]),(0,[z0,z501,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z77,z36,z6]),(0,[z0,z1,z3,z4,z502,z5,z6])],[(0,[z0,z1,z3,z503,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z6,z46]),(0,[z0,z1,z3,z4,z269,z19,z6]),(0,[z504,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z298,z4,z5,z6]),(0,[z0,z1,z3,z4,z505,z5,z6]),(0,[z0,z1,z3,z506,z4,z5,z6]),(0,[z507,z0,z1,z3,z4,z5,z6]),(0,[z155,z0,z1,z3,z77,z5,z6])],[(0,[z508,z0,z1,z3,z4,z5,z6]),(0,[z509,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z418,z3,z4,z36,z6])],[(0,[z510,z0,z1,z3,z4,z5,z6]),(0,[z225,z0,z1,z3,z4,z5,z49]),(0,[z511,z0,z1,z3,z4,z5,z6]),(0,[z155,z0,z1,z3,z4,z19,z6]),(0,[z512,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z150,z4,z513,z6]),(0,[z0,z1,z3,z4,z5,z514,z6])],[(0,[z515,z0,z1,z3,z4,z5,z6]),(0,[z21,z105,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z77,z9,z6]),(0,[z0,z1,z3,z4,z516,z5,z6])],[(0,[z125,z105,z0,z1,z4,z5,z6]),(0,[z22,z0,z1,z517,z3,z5,z6]),(0,[z518,z0,z1,z3,z4,z5,z6])],[(0,[z134,z0,z1,z3,z4,z19,z6]),(0,[z0,z3,z4,z5,z6,z419,z14]),(0,[z0,z1,z3,z4,z5,z6,z519])],[(0,[z0,z1,z3,z4,z5,z520,z6]),(0,[z97,z0,z1,z3,z4,z36,z6]),(1,[z0,z149,z3,z4,z19,z6]),(0,[z0,z1,z3,z150,z4,z19,z6]),(0,[z0,z521,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z522,z4,z5,z6])],[(1,[z264,z0,z1,z3,z4,z6]),(0,[z22,z0,z149,z1,z3,z5,z6]),(0,[z22,z0,z1,z3,z150,z5,z6]),(0,[z0,z1,z3,z50,z53,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z12]),(0,[z523,z0,z1,z3,z4,z5,z6])],[(0,[z21,z0,z1,z3,z60,z5,z6]),(0,[z0,z1,z3,z4,z189,z5,z6]),(1,[z0,z1,z492,z3,z4,z6])],[(0,[z0,z1,z3,z4,z334,z6,z37]),(0,[z0,z1,z3,z4,z5,z6,z127]),(0,[z524,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z52,z16,z4,z5,z6])],[(0,[z0,z1,z3,z4,z36,z110,z6]),(0,[z0,z1,z3,z4,z5,z6,z525]),(0,[z196,z0,z1,z3,z4,z5,z59])],[(0,[z15,z21,z0,z1,z3,z4,z6]),(0,[z97,z0,z1,z3,z4,z9,z6]),(0,[z15,z0,z1,z3,z4,z205,z6]),(0,[z0,z1,z3,z526,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z527,z6])]],
   [[(0,[z0,z1,z3,z4,z528,z5,z6]),(0,[z175,z0,z1,z185,z4,z5,z6]),(0,[z155,z0,z1,z3,z50,z5,z6])],[(0,[z70,z15,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z19,z93,z6])],[(0,[z0,z1,z529,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z6,z59]),(0,[z15,z0,z1,z3,z4,z6,z210])],[(1,[z0,z1,z400,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z530]),(0,[z0,z1,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z531,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z532,z6]),(0,[z0,z1,z3,z4,z30,z19,z6]),(0,[z0,z1,z335,z3,z4,z36,z6])],[(0,[z22,z0,z1,z3,z5,z169,z6]),(0,[z0,z1,z3,z4,z5,z6,z533])],[(0,[z0,z1,z3,z4,z5,z6,z534]),(0,[z22,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z248,z4,z77,z5,z6])],[(0,[z0,z1,z3,z4,z5,z535,z6]),(0,[z0,z1,z3,z4,z536,z5,z6]),(0,[z0,z1,z537,z3,z4,z5,z6]),(1,[z0,z1,z3,z138,z30,z6])],[(0,[z21,z0,z1,z3,z5,z74,z6]),(0,[z15,z0,z1,z3,z4,z269,z6])],[(0,[z21,z0,z45,z1,z3,z5,z6]),(0,[z182,z0,z1,z3,z4,z5,z6]),(0,[z538,z0,z1,z3,z4,z5,z6])],[(0,[z21,z0,z1,z3,z5,z49,z6]),(0,[z125,z0,z1,z4,z5,z6,z12]),(0,[z0,z1,z3,z4,z5,z6,z539])],[(0,[z0,z45,z1,z3,z4,z36,z6]),(0,[z196,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z540,z6])],[(0,[z0,z541,z1,z3,z4,z5,z6]),(0,[z0,z1,z542,z3,z4,z5,z6]),(0,[z0,z1,z3,z543,z4,z5,z6])],[(0,[z544,z0,z1,z3,z4,z5,z6]),(0,[z254,z0,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z545,z5,z6]),(0,[z22,z0,z1,z3,z4,z13,z6]),(0,[z0,z1,z3,z4,z5,z6,z546])],[(0,[z0,z547,z1,z3,z4,z5,z6])]],
   [[(1,[z0,z1,z3,z5,z6,z305]),(0,[z548,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z50,z4,z381,z6])],[(0,[z1,z173,z3,z4,z5,z6,z14]),(0,[z22,z21,z0,z1,z3,z5,z6]),(0,[z1,z3,z4,z5,z49,z6,z14]),(0,[z0,z45,z1,z3,z4,z9,z6]),(0,[z412,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z169,z6]),(0,[z0,z1,z3,z4,z459,z5,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z549,z0,z1,z3,z4,z19,z6])],[(1,[z22,z0,z1,z3,z169,z6]),(0,[z15,z0,z1,z3,z463,z4,z6])],[(0,[z0,z1,z3,z11,z4,z36,z6]),(0,[z550,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z52,z4,z5,z78,z6])],[(0,[z0,z1,z161,z3,z4,z5,z6]),(0,[z551,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z552,z5,z6])],[(0,[z21,z0,z76,z1,z3,z5,z6]),(1,[z155,z0,z1,z77,z5,z6])],[(0,[z21,z0,z1,z3,z193,z5,z6]),(0,[z0,z1,z553,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z554,z6])],[(0,[z15,z0,z1,z3,z104,z4,z6])],[(0,[z0,z1,z3,z4,z30,z151,z6]),(0,[z0,z1,z321,z3,z4,z5,z6]),(0,[z0,z1,z3,z28,z77,z5,z6]),(0,[z0,z413,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z555,z5,z6]),(0,[z0,z1,z3,z11,z4,z9,z6]),(0,[z0,z1,z3,z556,z4,z5,z6]),(0,[z141,z15,z0,z1,z3,z4,z6])],[],[(0,[z0,z1,z173,z3,z4,z36,z6]),(1,[z344,z0,z1,z3,z5,z6]),(0,[z557,z0,z1,z3,z4,z5,z6]),(0,[z118,z0,z1,z248,z4,z5,z6])],[(0,[z0,z1,z3,z4,z558,z5,z6]),(0,[z374,z0,z1,z3,z4,z36,z6]),(0,[z0,z413,z1,z3,z4,z554,z6])],[(0,[z22,z0,z1,z3,z5,z9,z6]),(0,[z559,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z171,z6])]],
   [[(0,[z15,z134,z0,z1,z3,z4,z6]),(0,[z224,z0,z1,z3,z4,z5,z6])],[(0,[z560,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z561,z6]),(0,[z0,z1,z52,z3,z4,z19,z6]),(0,[z0,z1,z562,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z30,z6]),(0,[z0,z1,z3,z4,z74,z9,z6])],[(0,[z97,z101,z0,z1,z3,z4,z6]),(1,[z368,z1,z3,z4,z5,z6]),(0,[z518,z15,z0,z1,z3,z4,z6])],[(0,[z22,z0,z1,z3,z82,z5,z6]),(0,[z0,z1,z3,z4,z19,z286,z6]),(0,[z15,z0,z1,z3,z4,z5,z210])],[(0,[z15,z75,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z563,z6]),(0,[z0,z1,z3,z4,z5,z564,z6]),(0,[z0,z1,z565,z3,z4,z5,z6]),(0,[z0,z1,z566,z3,z4,z5,z6]),(0,[z567,z0,z1,z3,z4,z5,z6])],[(0,[z387,z0,z1,z3,z4,z36,z6])],[(0,[z0,z1,z3,z4,z19,z74,z6]),(1,[z0,z1,z47,z3,z119,z6]),(1,[z0,z1,z4,z5,z6,z498])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z138,z4,z19,z6])],[(0,[z0,z1,z3,z4,z19,z49,z6]),(0,[z118,z0,z1,z3,z4,z44,z6]),(0,[z0,z413,z3,z4,z5,z205,z6])],[(0,[z0,z1,z568,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z569,z6]),(0,[z21,z0,z1,z3,z5,z347,z6])],[(0,[z0,z1,z570,z3,z4,z5,z6]),(1,[z0,z1,z3,z349,z5,z6]),(0,[z70,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z571,z3,z4,z5,z6])],[(0,[z21,z0,z1,z173,z3,z5,z6]),(1,[z105,z1,z187,z4,z5,z6]),(0,[z560,z21,z0,z1,z3,z5,z6]),(0,[z0,z45,z1,z3,z4,z341,z6])],[(0,[z15,z225,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z572,z5,z6])],[(1,[z22,z0,z1,z3,z9,z6]),(0,[z0,z1,z2,z3,z5,z151,z6])],[(0,[z0,z1,z3,z4,z573,z5,z6]),(0,[z0,z1,z3,z4,z110,z19,z6]),(0,[z0,z1,z3,z4,z5,z574,z6])]],
   [[(0,[z575,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z194,z6]),(0,[z0,z1,z3,z4,z5,z576,z6]),(0,[z0,z1,z3,z577,z4,z5,z6])],[(0,[z70,z0,z1,z3,z4,z9,z6])],[(0,[z22,z0,z1,z3,z35,z5,z6]),(0,[z0,z1,z3,z4,z358,z5,z6]),(0,[z0,z1,z3,z4,z5,z578,z6])],[(1,[z131,z0,z1,z3,z4,z6]),(0,[z579,z0,z1,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z19,z6]),(0,[z75,z0,z3,z4,z5,z205,z6]),(0,[z0,z1,z3,z4,z5,z6,z94]),(0,[z101,z0,z1,z3,z4,z19,z6]),(0,[z182,z15,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z580,z4,z5,z6]),(0,[z0,z1,z581,z3,z4,z5,z6])],[(0,[z22,z75,z0,z1,z3,z5,z6]),(1,[z70,z1,z3,z4,z5,z14]),(0,[z0,z1,z3,z4,z582,z5,z6]),(0,[z583,z0,z1,z3,z4,z5,z6])],[(0,[z0,z45,z248,z3,z4,z5,z6]),(0,[z584,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z585,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z36,z6])],[(0,[z270,z0,z1,z3,z4,z5,z6]),(0,[z179,z22,z0,z1,z3,z5,z6])],[(0,[z0,z1,z4,z5,z564,z151,z6]),(0,[z0,z1,z3,z4,z36,z9,z6]),(0,[z0,z1,z3,z4,z5,z6,z10])],[(0,[z118,z0,z1,z3,z4,z586,z6]),(0,[z587,z0,z1,z3,z4,z5,z6])],[(0,[z588,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z23,z3,z4,z36,z6])],[],[(0,[z279,z0,z1,z3,z4,z5,z6]),(0,[z589,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z92,z14]),(0,[z590,z0,z1,z3,z4,z5,z6]),(0,[z427,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z3,z591,z4,z5,z6])],[(0,[z22,z225,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z35,z5,z6]),(0,[z225,z0,z1,z3,z4,z18,z6]),(0,[z0,z1,z3,z4,z496,z36,z6])]],
   [[(0,[z0,z1,z3,z4,z586,z5,z6]),(0,[z0,z1,z3,z592,z4,z5,z6]),(0,[z0,z1,z3,z593,z4,z5,z6])],[(0,[z0,z1,z23,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z5,z6,z594]),(0,[z0,z1,z51,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z595,z5,z6])],[(0,[z15,z0,z1,z3,z4,z193,z6]),(0,[z70,z0,z1,z145,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z119,z6])],[(0,[z179,z368,z1,z3,z4,z5,z6])],[(0,[z101,z105,z0,z1,z4,z5,z6]),(0,[z141,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z51,z3,z4,z117,z6])],[(0,[z0,z1,z3,z4,z596,z5,z6]),(1,[z15,z0,z1,z3,z104,z6]),(0,[z597,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z316,z6]),(0,[z22,z0,z1,z3,z4,z169,z6]),(0,[z0,z1,z3,z4,z53,z19,z6]),(0,[z0,z113,z1,z3,z4,z9,z6]),(0,[z0,z413,z1,z3,z4,z5,z37]),(0,[z0,z1,z3,z4,z9,z6,z6])],[(0,[z27,z0,z1,z3,z4,z5,z6]),(0,[z0,z113,z3,z28,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z6,z14])],[(0,[z21,z0,z1,z3,z11,z5,z6]),(0,[z254,z0,z1,z3,z4,z36,z6]),(0,[z70,z0,z1,z3,z4,z5,z49]),(0,[z0,z1,z3,z16,z4,z36,z6]),(0,[z0,z598,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z599,z6]),(0,[z0,z1,z3,z4,z5,z600,z6])],[(0,[z601,z0,z1,z3,z4,z5,z6]),(0,[z141,z0,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z153,z5,z6]),(0,[z602,z0,z1,z3,z4,z5,z6])],[(0,[z15,z101,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z603,z4,z5,z6]),(0,[z0,z1,z3,z138,z150,z5,z6])],[(1,[z0,z1,z3,z4,z299,z6]),(0,[z179,z0,z3,z4,z5,z6,z37]),(1,[z0,z1,z3,z4,z513,z6]),(0,[z567,z15,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z6,z306,z14]),(0,[z0,z1,z3,z16,z4,z9,z6])],[(0,[z0,z1,z3,z4,z480,z5,z6]),(0,[z0,z1,z3,z4,z36,z205,z6]),(0,[z0,z1,z3,z4,z5,z604,z6])],[(0,[z0,z1,z400,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z77,z5,z6]),(1,[z0,z1,z3,z4,z6,z306]),(0,[z0,z1,z3,z4,z5,z605,z6])],[(0,[z22,z0,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z465,z3,z4,z5,z6])],[(0,[z0,z149,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z36,z6,z210]),(0,[z0,z1,z3,z522,z4,z9,z6])],[(0,[z75,z225,z1,z3,z4,z5,z6]),(0,[z105,z1,z187,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z5,z19,z6]),(0,[z0,z1,z3,z4,z5,z171,z6]),(0,[z63,z0,z1,z3,z4,z205,z6])],[],[(0,[z0,z1,z606,z3,z4,z5,z6]),(0,[z21,z0,z300,z1,z3,z5,z6]),(0,[z0,z1,z16,z4,z77,z5,z6]),(0,[z0,z1,z3,z4,z36,z599,z6]),(0,[z15,z0,z1,z47,z3,z4,z6])],[(0,[z0,z1,z3,z607,z4,z5,z6]),(0,[z101,z0,z1,z4,z5,z6,z12]),(1,[z0,z1,z3,z42,z5,z6])],[(0,[z0,z1,z3,z4,z608,z5,z6]),(0,[z0,z1,z3,z4,z9,z6,z453])],[(0,[z22,z0,z1,z3,z269,z5,z6]),(0,[z0,z1,z517,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z269,z6])],[(0,[z97,z0,z1,z3,z4,z193,z6]),(0,[z118,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z609,z5,z6])],[(0,[z0,z76,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z610,z6]),(0,[z0,z1,z3,z4,z5,z611,z6])],[(0,[z0,z1,z187,z3,z4,z19,z6]),(0,[z27,z0,z3,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z612,z6])],[(0,[z22,z0,z1,z187,z3,z5,z6]),(1,[z21,z0,z1,z3,z19,z6]),(1,[z0,z1,z4,z5,z564,z6]),(0,[z225,z0,z1,z3,z4,z5,z14]),(0,[z182,z0,z1,z3,z4,z36,z6])],[(0,[z22,z101,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z28,z4,z19,z6])]],
   [[(0,[z76,z1,z173,z3,z4,z5,z6])],[(0,[z22,z0,z1,z3,z4,z9,z6]),(0,[z613,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z9,z78,z6]),(0,[z0,z1,z3,z4,z5,z6,z614]),(0,[z583,z15,z0,z1,z3,z4,z6])],[(0,[z0,z76,z1,z3,z4,z615,z6]),(0,[z0,z1,z3,z338,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z616]),(0,[z0,z1,z51,z3,z4,z110,z6]),(0,[z0,z436,z1,z3,z4,z5,z6]),(0,[z0,z1,z482,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z617,z5,z6]),(0,[z0,z1,z47,z3,z4,z19,z6]),(0,[z0,z1,z3,z618,z4,z5,z6])],[(0,[z0,z1,z3,z315,z4,z5,z6]),(0,[z340,z0,z1,z3,z4,z5,z6]),(0,[z182,z0,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z193,z19,z6]),(0,[z0,z1,z3,z150,z4,z5,z74])],[(0,[z619,z0,z1,z3,z4,z5,z6]),(0,[z118,z21,z0,z1,z3,z5,z6]),(0,[z73,z0,z1,z3,z4,z5,z6])],[(0,[z105,z0,z1,z248,z4,z5,z6]),(0,[z125,z21,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z4,z342,z6]),(0,[z62,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z269,z5,z6])],[(0,[z620,z0,z1,z3,z4,z5,z6])],[(0,[z75,z0,z1,z3,z4,z5,z6]),(0,[z22,z0,z1,z47,z3,z5,z6]),(0,[z21,z0,z1,z3,z28,z5,z6]),(0,[z254,z0,z1,z3,z4,z193,z6]),(0,[z0,z1,z3,z4,z5,z6,z621])],[(0,[z445,z0,z1,z3,z4,z5,z6]),(0,[z155,z0,z1,z3,z4,z5,z6])],[(1,[z22,z0,z1,z3,z36,z6]),(0,[z21,z0,z1,z3,z5,z151,z6]),(0,[z0,z3,z4,z5,z205,z6,z37])],[(0,[z0,z1,z3,z4,z5,z6,z92])],[(1,[z26,z173,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z53,z5,z6]),(0,[z22,z0,z1,z3,z30,z5,z6]),(0,[z0,z1,z3,z4,z5,z622,z6]),(0,[z0,z1,z3,z4,z6,z395,z59])],[(0,[z134,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z610,z5,z6])],[(0,[z21,z0,z1,z3,z350,z5,z6]),(0,[z0,z1,z3,z4,z623,z5,z6]),(0,[z0,z1,z3,z4,z5,z624,z6]),(0,[z0,z1,z3,z4,z5,z6,z625]),(0,[z0,z1,z3,z4,z5,z9,z6]),(0,[z0,z1,z626,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z627,z4,z5,z6]),(0,[z0,z1,z3,z4,z555,z36,z6]),(0,[z628,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z150,z5,z74])],[(0,[z15,z97,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z629,z6]),(0,[z179,z0,z1,z3,z4,z299,z6]),(0,[z0,z1,z3,z4,z630,z5,z6]),(0,[z631,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z632,z5,z6]),(0,[z0,z1,z3,z50,z4,z497,z6]),(0,[z0,z1,z3,z633,z4,z5,z6])],[(0,[z134,z0,z1,z248,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z19,z6]),(0,[z0,z1,z3,z4,z5,z334,z6])],[(0,[z0,z1,z634,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z9,z6,z37]),(0,[z635,z0,z1,z3,z4,z5,z6]),(0,[z0,z636,z1,z3,z4,z5,z6])],[(0,[z637,z0,z1,z3,z4,z5,z6]),(0,[z155,z21,z0,z1,z3,z5,z6]),(0,[z179,z0,z1,z3,z4,z19,z6]),(0,[z638,z0,z1,z3,z4,z5,z6]),(0,[z0,z413,z1,z3,z4,z9,z6]),(0,[z196,z0,z1,z3,z150,z5,z6]),(0,[z0,z1,z3,z4,z9,z6,z34])],[(0,[z344,z0,z1,z3,z4,z5,z6]),(0,[z70,z0,z1,z406,z4,z5,z6]),(0,[z0,z1,z3,z4,z36,z36,z6]),(0,[z0,z1,z3,z4,z5,z6,z639])],[(0,[z196,z0,z1,z3,z4,z5,z74])],[(0,[z0,z1,z3,z4,z640,z5,z6]),(0,[z0,z1,z3,z239,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z134,z21,z0,z1,z3,z5,z6])],[(0,[z22,z0,z1,z3,z5,z205,z6]),(1,[z175,z0,z3,z53,z5,z6]),(0,[z641,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z30,z5,z6]),(0,[z0,z1,z4,z5,z9,z6,z498])],[(0,[z22,z0,z1,z3,z5,z119,z6]),(0,[z0,z1,z3,z4,z5,z31,z6]),(0,[z15,z0,z1,z492,z3,z4,z6])],[(0,[z225,z0,z1,z3,z4,z459,z6])],[(0,[z22,z0,z1,z3,z5,z6,z210]),(0,[z0,z1,z3,z4,z5,z642,z6])],[(0,[z0,z1,z3,z4,z5,z6,z643]),(0,[z0,z1,z3,z4,z5,z6,z644])],[]],
   [[(0,[z645,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z646,z6]),(0,[z0,z1,z187,z4,z5,z6,z12]),(0,[z22,z0,z1,z3,z5,z6,z14]),(0,[z0,z647,z1,z3,z4,z5,z6]),(1,[z55,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z464,z5,z6])],[(0,[z22,z97,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z648]),(0,[z0,z1,z3,z4,z9,z6,z498])],[(0,[z0,z1,z248,z3,z4,z19,z6]),(0,[z0,z113,z1,z3,z4,z36,z6]),(0,[z0,z649,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z314,z6]),(0,[z361,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z650,z4,z5,z6]),(0,[z0,z1,z3,z4,z651,z5,z6])],[(0,[z0,z1,z3,z4,z652,z5,z6]),(0,[z653,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z233,z6]),(0,[z0,z1,z3,z4,z654,z5,z6])],[(0,[z0,z1,z3,z260,z4,z5,z6]),(0,[z0,z1,z3,z655,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z205,z6])],[(0,[z21,z0,z1,z3,z5,z389,z6]),(0,[z15,z0,z1,z3,z4,z49,z6]),(1,[z0,z1,z3,z4,z6,z395])],[(0,[z21,z0,z1,z493,z3,z5,z6]),(0,[z0,z1,z3,z4,z19,z151,z6])],[(0,[z0,z1,z3,z4,z656,z5,z6]),(0,[z0,z1,z3,z4,z5,z657,z6]),(0,[z474,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z650,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z210])],[(0,[z0,z658,z1,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z5,z117,z6]),(0,[z0,z1,z3,z659,z4,z5,z6])],[(0,[z196,z21,z0,z1,z3,z5,z6]),(0,[z15,z254,z0,z1,z3,z4,z6])],[(0,[z26,z75,z1,z3,z4,z5,z6]),(0,[z660,z0,z1,z3,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z19,z6])],[],[(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z15,z0,z1,z187,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z661])]],
   [[(0,[z0,z1,z3,z662,z4,z5,z6]),(0,[z0,z663,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z381,z6]),(0,[z0,z1,z3,z4,z9,z6,z12])],[],[(0,[z0,z1,z3,z4,z165,z19,z6])],[(0,[z0,z1,z3,z4,z664,z5,z6]),(0,[z0,z1,z665,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z36,z193,z6]),(0,[z0,z1,z3,z4,z36,z119,z6])],[(0,[z15,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z666,z5,z6]),(0,[z0,z1,z3,z667,z4,z5,z6]),(0,[z175,z0,z1,z3,z4,z610,z6]),(0,[z0,z113,z1,z3,z53,z5,z6])],[(0,[z21,z0,z1,z3,z4,z19,z6]),(1,[z0,z113,z3,z28,z5,z6])],[(0,[z22,z0,z1,z3,z110,z5,z6]),(0,[z0,z1,z3,z4,z528,z36,z6]),(0,[z0,z413,z1,z3,z4,z280,z6]),(0,[z0,z1,z3,z4,z513,z5,z6])],[(1,[z97,z1,z3,z4,z151,z6])],[(0,[z0,z1,z3,z4,z35,z9,z6])],[(0,[z0,z1,z3,z4,z36,z6,z14]),(0,[z0,z1,z51,z4,z110,z5,z6])],[(0,[z398,z22,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z138,z4,z5,z6]),(0,[z15,z0,z1,z3,z138,z4,z6]),(0,[z0,z1,z371,z3,z4,z6,z59])],[(0,[z22,z254,z0,z1,z3,z5,z6]),(0,[z22,z0,z1,z3,z4,z36,z6]),(0,[z0,z1,z668,z3,z4,z5,z6])],[(0,[z669,z0,z1,z3,z4,z5,z6]),(0,[z125,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z21,z0,z1,z51,z3,z5,z6])],[(0,[z21,z0,z1,z3,z5,z6,z428]),(0,[z175,z0,z1,z3,z4,z342,z6]),(0,[z670,z0,z1,z3,z4,z5,z6])],[(0,[z671,z0,z1,z3,z4,z5,z6]),(0,[z175,z0,z1,z3,z28,z5,z6])],[(0,[z672,z0,z1,z3,z4,z5,z6]),(0,[z21,z0,z1,z248,z3,z5,z6]),(0,[z21,z0,z1,z3,z50,z5,z6]),(0,[z179,z55,z1,z3,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z35,z6]),(0,[z56,z21,z0,z1,z3,z5,z6]),(0,[z673,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z50,z4,z77,z5,z6]),(0,[z0,z1,z163,z4,z5,z9,z6])],[(0,[z105,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z110,z5,z6]),(0,[z15,z0,z1,z3,z4,z6,z59])],[(0,[z125,z0,z1,z3,z4,z5,z12])],[(0,[z0,z1,z3,z4,z5,z238,z6]),(0,[z0,z1,z23,z50,z4,z5,z6])],[(0,[z0,z1,z3,z4,z674,z5,z6]),(0,[z0,z675,z1,z3,z4,z5,z6]),(1,[z15,z22,z0,z1,z3,z6]),(0,[z1,z3,z60,z4,z35,z5,z6]),(0,[z0,z1,z3,z4,z676,z5,z6]),(1,[z0,z1,z3,z4,z586,z6]),(0,[z0,z1,z248,z4,z5,z6,z12]),(1,[z0,z1,z51,z4,z110,z6])],[(0,[z337,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z117,z6])],[(0,[z26,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z677,z3,z4,z5,z6])],[],[(0,[z445,z0,z1,z4,z5,z6,z14]),(0,[z179,z0,z1,z3,z650,z5,z6]),(0,[z101,z0,z1,z51,z4,z5,z6])],[(0,[z388,z0,z1,z173,z3,z5,z6]),(0,[z101,z0,z1,z3,z4,z117,z6]),(0,[z0,z1,z3,z4,z473,z9,z6])],[(0,[z1,z187,z3,z11,z4,z5,z6])],[(0,[z22,z0,z1,z3,z138,z5,z6]),(0,[z0,z1,z678,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z15,z0,z413,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z680]),(0,[z125,z0,z1,z52,z4,z5,z6]),(0,[z0,z681,z1,z3,z4,z5,z6]),(0,[z682,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z683,z4,z5,z6])],[(1,[z0,z1,z3,z189,z5,z6]),(0,[z0,z1,z3,z4,z5,z684,z6])],[(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z413,z1,z3,z4,z36,z6]),(0,[z0,z1,z3,z150,z4,z5,z6])],[(0,[z0,z686,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z687,z6])],[(0,[z70,z0,z1,z3,z4,z5,z14]),(0,[z15,z0,z113,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z330,z6])],[(0,[z26,z21,z0,z1,z3,z5,z6]),(0,[z101,z21,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z4,z448,z6])],[(1,[z15,z21,z0,z1,z3,z6]),(0,[z118,z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z227,z3,z4,z19,z6])],[(0,[z0,z1,z3,z4,z151,z9,z6]),(0,[z0,z1,z3,z4,z688,z5,z6]),(0,[z0,z1,z3,z4,z5,z385,z6]),(0,[z0,z1,z689,z3,z4,z5,z6])],[(0,[z26,z0,z3,z4,z5,z205,z6]),(0,[z0,z1,z3,z4,z280,z5,z6]),(0,[z690,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z691,z6]),(0,[z0,z1,z3,z4,z36,z6,z106])],[(0,[z0,z1,z692,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z693])],[(0,[z105,z0,z1,z4,z110,z5,z6])],[(0,[z0,z1,z694,z3,z4,z5,z6]),(0,[z695,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z696,z6]),(1,[z0,z1,z3,z536,z5,z6]),(0,[z0,z1,z3,z4,z53,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z697]),(1,[z0,z1,z4,z9,z6,z498])],[(0,[z75,z0,z1,z3,z4,z36,z6])],[(0,[z0,z413,z1,z3,z4,z5,z205]),(0,[z0,z1,z3,z4,z497,z5,z6])]],
   [[(0,[z0,z1,z3,z5,z6,z305,z14])],[(0,[z0,z1,z3,z4,z5,z6,z698]),(0,[z22,z0,z413,z1,z3,z5,z6]),(1,[z0,z1,z260,z4,z5,z6]),(0,[z0,z1,z3,z138,z30,z5,z6])],[(0,[z0,z1,z3,z699,z4,z5,z6]),(0,[z0,z1,z3,z4,z269,z9,z6])],[(0,[z442,z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z9,z9,z6])],[(0,[z75,z0,z1,z3,z4,z9,z6]),(0,[z21,z0,z1,z3,z5,z78,z6]),(0,[z700,z0,z1,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z163,z4,z5,z6])],[(0,[z22,z0,z113,z1,z3,z5,z6]),(0,[z0,z1,z3,z536,z5,z151,z6]),(0,[z701,z0,z1,z3,z4,z5,z6]),(0,[z702,z0,z1,z3,z4,z5,z6])],[(0,[z134,z0,z1,z4,z110,z5,z6]),(0,[z225,z0,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z269,z5,z9])],[],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z28,z150,z5,z6]),(0,[z15,z0,z1,z3,z4,z74,z6])],[(0,[z125,z15,z0,z1,z3,z4,z6]),(0,[z0,z1,z703,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z42,z6])],[(0,[z0,z704,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z705]),(0,[z0,z1,z3,z4,z5,z119,z6])],[(0,[z549,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z104,z4,z5,z6])],[(1,[z0,z1,z3,z315,z5,z6]),(0,[z22,z0,z1,z3,z5,z6,z48]),(0,[z0,z1,z3,z317,z4,z5,z6]),(0,[z706,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z554,z6])],[(0,[z0,z1,z3,z4,z615,z5,z6]),(0,[z22,z0,z1,z3,z193,z5,z6])],[(1,[z0,z1,z3,z4,z615,z6]),(0,[z0,z1,z3,z4,z19,z6,z12]),(0,[z0,z636,z1,z3,z4,z9,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z21,z0,z1,z3,z93,z6]),(0,[z0,z1,z3,z4,z358,z9]),(0,[z707,z0,z1,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z708]),(0,[z319,z101,z0,z1,z4,z6])],[(0,[z0,z1,z709,z4,z5,z6]),(0,[z22,z1,z3,z142,z5,z6]),(0,[z710,z1,z3,z4,z5,z6])],[(0,[z236,z1,z3,z4,z5,z14])],[(0,[z0,z3,z4,z5,z6,z419]),(0,[z22,z0,z1,z3,z711,z6])],[(0,[z0,z1,z3,z4,z712,z6]),(0,[z22,z474,z1,z3,z19,z6]),(0,[z0,z1,z3,z713,z5,z6]),(0,[z714,z0,z1,z3,z4,z6]),(0,[z0,z1,z52,z4,z5,z78]),(0,[z0,z1,z4,z9,z6,z715])],[(0,[z0,z1,z3,z716,z4,z6]),(0,[z22,z0,z1,z3,z717,z6]),(0,[z21,z0,z1,z371,z3,z6]),(0,[z0,z1,z3,z718,z5,z6]),(0,[z0,z1,z3,z719,z5,z6]),(0,[z0,z1,z3,z4,z720,z6]),(0,[z63,z0,z436,z3,z4,z6])],[(0,[z0,z1,z3,z4,z721,z6]),(0,[z0,z722,z16,z4,z5,z6]),(0,[z0,z3,z723,z53,z5,z6]),(0,[z0,z1,z3,z4,z724,z6]),(0,[z0,z1,z3,z4,z364,z6])],[(0,[z0,z1,z3,z725,z5,z6]),(0,[z22,z21,z1,z3,z169,z6]),(0,[z22,z0,z1,z3,z726,z6]),(0,[z22,z1,z3,z35,z169,z6]),(0,[z0,z1,z3,z727,z5,z6]),(0,[z0,z1,z3,z4,z728,z6]),(0,[z0,z1,z3,z4,z729,z6]),(0,[z15,z0,z1,z3,z189,z6])],[(0,[z134,z264,z0,z1,z4,z6]),(0,[z730,z0,z1,z4,z5,z6]),(0,[z731,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z19,z6]),(0,[z0,z1,z3,z4,z19,z732])],[(0,[z0,z1,z3,z5,z733,z6]),(0,[z0,z1,z3,z734,z5,z6]),(0,[z22,z21,z1,z3,z5,z6]),(0,[z22,z1,z3,z464,z5,z6]),(0,[z0,z1,z229,z50,z5,z6]),(0,[z131,z21,z0,z1,z3,z6])],[(0,[z735,z0,z1,z3,z4,z6]),(0,[z15,z388,z0,z1,z3,z6]),(0,[z21,z0,z1,z3,z497,z6]),(0,[z0,z1,z536,z5,z564,z6])],[(0,[z26,z173,z3,z4,z19,z6]),(0,[z21,z75,z76,z3,z5,z6]),(0,[z0,z1,z23,z50,z9,z6]),(0,[z0,z1,z52,z4,z5,z736])],[(0,[z0,z1,z3,z4,z737,z6]),(0,[z21,z1,z3,z5,z268,z6]),(0,[z0,z1,z3,z42,z151,z6]),(0,[z0,z1,z3,z4,z738,z6])],[(0,[z0,z1,z3,z4,z739,z6]),(0,[z15,z0,z1,z185,z4,z6]),(0,[z0,z149,z3,z4,z19,z6]),(0,[z0,z3,z4,z36,z172,z6])],[(0,[z0,z1,z3,z4,z740,z6]),(0,[z75,z3,z4,z5,z6,z370]),(0,[z264,z0,z1,z3,z4,z6]),(0,[z741,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z150,z19,z74]),(0,[z179,z0,z126,z3,z4,z37])],[(0,[z0,z1,z492,z3,z4,z6]),(0,[z0,z1,z223,z4,z36,z6]),(0,[z278,z0,z1,z463,z4,z6])]],
   [[(0,[z0,z1,z3,z742,z5,z6]),(0,[z0,z3,z4,z36,z6,z419])],[(0,[z0,z1,z3,z4,z743,z6]),(0,[z270,z0,z452,z3,z5,z6]),(0,[z27,z22,z0,z3,z5,z6]),(0,[z21,z0,z1,z3,z364,z6]),(0,[z15,z0,z1,z145,z4,z6]),(0,[z0,z1,z3,z4,z744,z6])],[(0,[z0,z1,z3,z745,z4,z6]),(0,[z0,z1,z3,z746,z5,z6]),(0,[z101,z515,z0,z1,z4,z6]),(0,[z22,z0,z1,z3,z6,z127]),(0,[z0,z1,z3,z5,z74,z428]),(0,[z0,z1,z3,z239,z36,z6])],[(0,[z0,z1,z3,z4,z747,z6]),(0,[z445,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z748]),(0,[z22,z0,z1,z3,z749,z6]),(0,[z0,z1,z3,z750,z5,z6]),(0,[z15,z0,z413,z3,z4,z205]),(0,[z0,z1,z3,z751,z5,z6])],[(0,[z0,z492,z173,z3,z4,z6]),(0,[z75,z76,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z752,z6]),(0,[z0,z681,z3,z4,z19,z6]),(0,[z753,z1,z3,z4,z5,z6])],[(0,[z22,z0,z1,z3,z754,z6]),(0,[z0,z1,z4,z19,z6,z92]),(0,[z0,z1,z223,z4,z9,z6])],[(0,[z388,z0,z1,z3,z9,z6]),(0,[z134,z344,z1,z11,z5,z6]),(0,[z22,z0,z1,z3,z448,z6]),(0,[z337,z0,z1,z4,z30,z6]),(0,[z0,z1,z3,z19,z6,z94])],[(0,[z0,z568,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z755]),(0,[z0,z1,z3,z5,z6,z756])],[(0,[z0,z1,z757,z3,z4,z6]),(0,[z422,z22,z1,z3,z5,z6]),(0,[z175,z0,z517,z3,z5,z6]),(0,[z225,z1,z3,z4,z36,z49]),(0,[z0,z1,z3,z239,z9,z6]),(0,[z0,z1,z3,z5,z758,z6]),(0,[z175,z0,z3,z53,z19,z6]),(0,[z0,z1,z3,z4,z759,z6]),(0,[z0,z1,z371,z3,z119,z6])],[(0,[z337,z0,z1,z4,z36,z6]),(0,[z0,z1,z3,z4,z760,z6]),(0,[z0,z1,z3,z4,z761,z6]),(0,[z0,z1,z3,z513,z119,z6])],[(0,[z75,z76,z3,z4,z9,z6]),(0,[z22,z225,z1,z3,z5,z49]),(0,[z0,z1,z3,z4,z6,z762]),(0,[z0,z763,z3,z4,z5,z6]),(0,[z15,z0,z1,z23,z50,z6]),(0,[z15,z0,z1,z163,z4,z9])],[(0,[z0,z1,z3,z298,z5,z6]),(0,[z0,z1,z4,z5,z6,z764]),(0,[z0,z1,z406,z4,z9,z6]),(0,[z0,z3,z722,z4,z5,z6]),(0,[z0,z1,z3,z4,z288,z171]),(0,[z55,z1,z3,z4,z299,z6])],[(0,[z0,z1,z3,z4,z5,z765]),(0,[z0,z1,z3,z4,z459,z6]),(0,[z0,z413,z3,z4,z5,z766]),(0,[z0,z3,z4,z205,z6,z34])],[(0,[z0,z1,z3,z4,z767,z6]),(0,[z225,z1,z3,z239,z5,z49]),(0,[z0,z1,z3,z4,z9,z527])],[(0,[z225,z1,z3,z4,z9,z49]),(0,[z15,z0,z1,z3,z198,z6]),(0,[z118,z0,z16,z4,z9,z6]),(0,[z768,z0,z1,z3,z5,z6]),(0,[z101,z0,z1,z4,z599,z6]),(0,[z423,z0,z3,z4,z36,z6]),(0,[z368,z1,z3,z189,z5,z6]),(0,[z0,z1,z3,z4,z769,z6])],[(0,[z22,z0,z770,z3,z5,z6]),(0,[z771,z0,z3,z4,z5,z6]),(0,[z55,z1,z3,z4,z19,z6]),(0,[z772,z0,z1,z3,z5,z6])]],
   [[(0,[z773,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z338,z5,z6]),(0,[z15,z0,z3,z4,z6,z419])],[(0,[z0,z1,z774,z4,z5,z6]),(0,[z0,z1,z3,z298,z615,z6]),(0,[z22,z0,z1,z774,z5,z6]),(0,[z0,z1,z3,z5,z6,z775]),(0,[z22,z1,z3,z35,z9,z6]),(0,[z21,z1,z3,z60,z36,z6]),(0,[z73,z0,z1,z5,z6,z92]),(0,[z776,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z777,z6])],[(0,[z0,z1,z396,z4,z5,z6]),(0,[z778,z0,z1,z3,z4,z6]),(0,[z254,z1,z3,z4,z193,z6]),(0,[z0,z1,z3,z4,z18,z6])],[(0,[z0,z581,z3,z4,z19,z6])],[(0,[z0,z1,z3,z5,z6,z305]),(0,[z62,z0,z1,z3,z4,z78]),(0,[z125,z0,z1,z4,z36,z12]),(0,[z0,z1,z3,z650,z299,z6])],[(0,[z0,z3,z779,z4,z5,z6]),(0,[z0,z780,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z781,z6]),(0,[z0,z1,z145,z4,z36,z6]),(0,[z0,z1,z3,z4,z114,z6]),(0,[z0,z1,z3,z36,z758,z6])],[(0,[z0,z1,z782,z4,z5,z6]),(0,[z21,z0,z1,z783,z5,z6]),(0,[z21,z0,z3,z5,z6,z419]),(0,[z0,z1,z3,z4,z784,z6])],[(0,[z0,z1,z3,z4,z6,z785]),(0,[z21,z511,z1,z3,z5,z6]),(0,[z1,z3,z60,z786,z5,z6])],[(1,[z787,z3,z4,z5,z6]),(0,[z0,z1,z396,z4,z615,z6]),(0,[z22,z0,z1,z3,z169,z6]),(0,[z0,z1,z3,z338,z13,z6]),(0,[z21,z0,z1,z3,z767,z6]),(0,[z0,z1,z788,z145,z4,z6]),(0,[z0,z45,z248,z4,z36,z6]),(0,[z0,z1,z3,z650,z19,z6]),(0,[z0,z1,z3,z789,z19,z6]),(0,[z0,z1,z790,z3,z36,z6]),(0,[z15,z0,z1,z3,z4,z8])],[(0,[z15,z0,z1,z3,z6,z305]),(0,[z791,z0,z1,z3,z4,z6])],[(0,[z22,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z792,z6]),(0,[z445,z73,z0,z1,z5,z6]),(0,[z793,z0,z1,z3,z4,z6]),(0,[z62,z0,z1,z3,z4,z210]),(0,[z0,z1,z3,z5,z794,z6])],[(0,[z15,z75,z76,z3,z4,z6]),(0,[z0,z1,z795,z4,z5,z6]),(0,[z15,z0,z1,z223,z4,z6]),(0,[z155,z0,z1,z77,z5,z6])],[(0,[z175,z0,z3,z53,z342,z6]),(0,[z0,z293,z3,z28,z5,z6])],[(0,[z796,z0,z1,z3,z4,z6]),(0,[z645,z0,z16,z4,z5,z6]),(0,[z101,z0,z1,z463,z4,z6]),(0,[z282,z0,z1,z4,z6,z498])],[(0,[z0,z1,z3,z797,z5,z6]),(0,[z22,z0,z1,z3,z554,z6]),(0,[z798,z0,z1,z3,z4,z6]),(0,[z0,z3,z4,z36,z608,z6])],[(0,[z0,z1,z185,z4,z36,z6])]],
   [[(0,[z22,z0,z1,z3,z615,z6]),(0,[z21,z0,z1,z3,z114,z6]),(0,[z63,z0,z1,z3,z4,z106])],[(0,[z26,z161,z173,z3,z5,z6]),(0,[z0,z1,z3,z799,z5,z6]),(0,[z0,z1,z3,z36,z6,z305]),(0,[z800,z0,z1,z3,z5,z6]),(0,[z801,z368,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z802,z6]),(0,[z0,z1,z3,z150,z5,z450]),(0,[z0,z1,z3,z4,z803,z6])],[(0,[z22,z120,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z6,z804])],[(0,[z0,z3,z4,z36,z218,z6]),(0,[z73,z0,z1,z3,z36,z6]),(0,[z0,z1,z4,z171,z6,z805])],[(0,[z0,z3,z4,z5,z205,z139]),(0,[z0,z1,z3,z4,z806,z6]),(0,[z0,z1,z185,z4,z9,z6]),(0,[z0,z113,z3,z28,z19,z6]),(0,[z807,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z808]),(0,[z368,z1,z3,z4,z5,z6]),(0,[z22,z1,z281,z3,z5,z6]),(0,[z70,z3,z4,z5,z419,z14]),(0,[z27,z0,z3,z4,z792,z6]),(0,[z15,z175,z0,z3,z53,z6]),(0,[z0,z1,z3,z4,z809,z6]),(0,[z0,z1,z3,z4,z810,z6])],[(0,[z134,z451,z1,z4,z5,z6]),(0,[z89,z0,z493,z3,z5,z6]),(0,[z15,z811,z0,z1,z4,z6])],[(0,[z337,z0,z1,z4,z119,z6]),(1,[z1,z3,z4,z5,z812]),(0,[z0,z1,z465,z4,z9,z6])],[(0,[z27,z173,z3,z4,z5,z6]),(0,[z813,z0,z1,z3,z4,z5]),(0,[z0,z814,z3,z4,z5,z6])],[(0,[z0,z521,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z815,z6]),(0,[z0,z1,z47,z3,z119,z6]),(0,[z15,z0,z1,z816,z4,z6])],[(0,[z0,z1,z3,z4,z6,z817])],[(0,[z15,z0,z1,z3,z4,z629]),(0,[z0,z1,z3,z4,z818,z6]),(0,[z819,z0,z1,z3,z5,z6]),(1,[z0,z1,z3,z794,z6])],[(0,[z0,z1,z820,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z821]),(0,[z822,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z823,z6])],[(0,[z15,z0,z1,z313,z3,z4]),(0,[z22,z0,z1,z3,z824,z6]),(0,[z0,z1,z3,z150,z5,z216]),(0,[z0,z1,z3,z825,z19,z6]),(0,[z179,z0,z3,z4,z9,z37]),(0,[z15,z0,z1,z3,z42,z9])],[(0,[z0,z1,z3,z4,z826,z6]),(0,[z0,z1,z3,z4,z827,z6])]],
   [[(0,[z22,z0,z1,z3,z828,z6]),(0,[z0,z1,z829,z4,z5,z6]),(0,[z0,z1,z3,z830,z5,z6]),(0,[z0,z1,z3,z104,z42,z6])],[(0,[z15,z0,z1,z3,z4,z91]),(0,[z1,z3,z831,z4,z5,z6])],[(0,[z15,z832,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z833,z6]),(0,[z0,z1,z3,z834,z36,z6]),(0,[z179,z0,z3,z4,z334,z37]),(0,[z0,z1,z4,z5,z835,z6]),(0,[z15,z0,z1,z3,z4,z755])],[(0,[z0,z1,z3,z836,z5,z6]),(0,[z134,z22,z1,z11,z5,z6]),(0,[z0,z1,z4,z5,z78,z402]),(0,[z15,z798,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z837,z6]),(0,[z63,z0,z1,z3,z104,z6])],[(0,[z361,z0,z517,z3,z5,z6]),(0,[z22,z0,z1,z3,z79,z6]),(0,[z22,z1,z3,z5,z6,z697]),(0,[z0,z1,z321,z4,z165,z6]),(0,[z0,z1,z4,z19,z838,z6]),(0,[z101,z0,z1,z4,z687,z6])],[(0,[z0,z1,z3,z4,z839,z6]),(0,[z0,z1,z3,z4,z840,z6]),(0,[z0,z1,z3,z5,z841,z6]),(0,[z842,z0,z1,z3,z4,z6]),(0,[z101,z0,z1,z4,z330,z6]),(0,[z0,z1,z3,z104,z513,z6])],[(0,[z0,z1,z3,z4,z843,z6]),(0,[z0,z1,z3,z4,z844,z6]),(0,[z845,z0,z3,z4,z6,z419]),(0,[z0,z1,z3,z4,z358,z93]),(0,[z0,z1,z482,z3,z42,z6])],[(0,[z15,z0,z1,z3,z4,z106]),(0,[z0,z1,z4,z36,z6,z498]),(0,[z846,z0,z1,z3,z5,z6])],[(0,[z0,z1,z847,z4,z5,z6]),(0,[z134,z1,z11,z4,z9,z6]),(0,[z0,z1,z3,z848,z5,z6]),(0,[z0,z1,z722,z4,z5,z6]),(0,[z0,z1,z23,z50,z36,z6]),(0,[z0,z1,z3,z4,z755,z210])],[(0,[z22,z54,z1,z3,z5,z6]),(0,[z15,z0,z1,z3,z194,z6]),(0,[z0,z45,z248,z4,z341,z6])],[(0,[z225,z1,z3,z5,z49,z94]),(0,[z0,z1,z3,z138,z480,z6]),(0,[z0,z413,z3,z4,z9,z205])],[(0,[z0,z1,z3,z19,z849,z6]),(0,[z0,z1,z3,z189,z299,z6]),(0,[z0,z1,z3,z850,z5,z6])],[(0,[z0,z1,z3,z4,z5,z851]),(0,[z21,z0,z1,z852,z5,z6]),(0,[z853,z0,z1,z3,z4,z6])],[(0,[z479,z21,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z854,z6])],[(0,[z254,z21,z1,z3,z193,z6]),(0,[z97,z1,z2,z3,z151,z6]),(0,[z15,z0,z1,z3,z4,z130])],[(0,[z0,z1,z3,z5,z6,z855]),(0,[z22,z0,z1,z3,z856,z6]),(0,[z0,z1,z3,z189,z19,z6]),(1,[z0,z1,z3,z4,z755])]],
   [[(0,[z0,z1,z3,z4,z857,z6]),(0,[z0,z1,z3,z4,z858,z6]),(0,[z368,z1,z3,z4,z79,z6])],[(0,[z0,z1,z3,z4,z859,z6]),(0,[z134,z21,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z860,z6]),(0,[z0,z1,z3,z4,z861,z6]),(0,[z0,z1,z3,z36,z194,z6]),(0,[z0,z1,z3,z862,z36,z6]),(0,[z0,z1,z863,z3,z4,z6])],[(0,[z864,z0,z1,z3,z4,z5]),(0,[z75,z76,z3,z4,z238,z6]),(0,[z15,z0,z1,z3,z315,z6]),(0,[z21,z0,z1,z829,z5,z6]),(0,[z0,z1,z3,z4,z865,z6]),(0,[z866,z1,z3,z4,z5,z6]),(0,[z0,z1,z4,z9,z6,z867])],[(0,[z388,z0,z1,z3,z36,z6]),(0,[z0,z1,z3,z4,z868,z6])],[(0,[z0,z1,z3,z4,z869,z6]),(0,[z870,z0,z1,z145,z4,z6]),(0,[z871,z0,z1,z3,z4,z6])],[(0,[z21,z0,z1,z400,z5,z6]),(0,[z0,z1,z3,z4,z872,z6]),(0,[z0,z1,z3,z4,z873,z6])],[(0,[z0,z1,z3,z4,z874,z6]),(0,[z55,z1,z3,z650,z5,z6]),(0,[z0,z1,z3,z4,z875,z6]),(0,[z0,z1,z3,z4,z6,z876]),(0,[z15,z877,z0,z1,z3,z6]),(0,[z278,z0,z1,z3,z42,z6])],[(0,[z0,z397,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z878]),(0,[z0,z1,z52,z4,z5,z612]),(0,[z62,z0,z1,z3,z789,z6]),(0,[z0,z1,z879,z3,z5,z6]),(0,[z15,z0,z1,z3,z4,z203]),(0,[z0,z1,z163,z4,z292,z6])],[(1,[z1,z831,z4,z5,z6]),(0,[z0,z880,z3,z4,z5,z6]),(0,[z0,z1,z406,z4,z36,z6]),(0,[z0,z1,z881,z4,z5,z6]),(0,[z0,z1,z882,z4,z5,z6])],[(0,[z27,z15,z0,z3,z4,z6]),(0,[z0,z1,z52,z4,z36,z78]),(0,[z0,z1,z3,z4,z883,z6])],[(0,[z0,z1,z400,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z884]),(0,[z0,z1,z3,z885,z4,z6])],[(0,[z0,z1,z3,z4,z886,z6]),(0,[z0,z1,z3,z536,z19,z6]),(0,[z118,z0,z16,z4,z36,z6]),(0,[z0,z1,z887,z3,z4,z6])],[(0,[z21,z0,z1,z3,z861,z6]),(0,[z0,z1,z3,z4,z888,z6]),(0,[z0,z1,z889,z4,z5,z6]),(0,[z0,z1,z430,z77,z5,z6]),(0,[z15,z0,z1,z3,z4,z156]),(0,[z15,z0,z1,z3,z150,z74])],[(0,[z0,z1,z3,z890,z4,z6])],[(0,[z22,z21,z1,z3,z36,z6]),(0,[z22,z1,z3,z35,z36,z6]),(0,[z0,z1,z3,z4,z891,z6]),(0,[z0,z1,z892,z4,z5,z6]),(0,[z0,z1,z3,z4,z893,z6]),(0,[z0,z1,z3,z138,z30,z6])],[(0,[z0,z1,z3,z4,z894,z6]),(0,[z0,z1,z3,z169,z6,z48]),(0,[z1,z3,z4,z5,z49,z812]),(0,[z15,z118,z0,z16,z4,z6]),(0,[z0,z1,z4,z5,z736,z12]),(0,[z0,z1,z52,z4,z9,z78])]],
   [[(0,[z0,z1,z895,z4,z5,z6]),(0,[z0,z1,z400,z4,z615,z6]),(0,[z0,z1,z3,z4,z896,z6]),(0,[z0,z3,z4,z632,z19,z6]),(0,[z0,z39,z3,z4,z19,z6]),(0,[z125,z0,z1,z4,z5,z736]),(0,[z0,z1,z3,z719,z9,z6])],[],[(0,[z21,z0,z1,z3,z6,z878]),(0,[z27,z21,z0,z3,z5,z6]),(0,[z897,z0,z1,z3,z5,z6])],[(0,[z75,z55,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z221,z6]),(0,[z801,z0,z1,z3,z5,z6]),(0,[z22,z1,z3,z57,z5,z6]),(0,[z0,z1,z3,z4,z299,z6]),(0,[z0,z1,z163,z4,z19,z6]),(0,[z0,z1,z3,z4,z513,z6])],[(0,[z26,z22,z173,z3,z5,z6]),(0,[z22,z264,z0,z1,z3,z6]),(0,[z22,z21,z1,z3,z9,z6]),(0,[z0,z3,z4,z36,z898,z6]),(0,[z899,z1,z3,z4,z5,z6])],[(0,[z15,z0,z1,z161,z3,z6]),(0,[z0,z1,z3,z4,z900,z6]),(0,[z0,z1,z3,z5,z6,z901]),(0,[z22,z0,z1,z3,z280,z6]),(0,[z137,z0,z1,z3,z4,z9])],[(0,[z0,z1,z3,z4,z6,z306]),(0,[z445,z0,z4,z5,z6,z419]),(0,[z0,z1,z4,z6,z34,z498])],[(0,[z0,z1,z3,z4,z19,z6]),(0,[z22,z0,z1,z5,z564,z6]),(0,[z902,z0,z1,z3,z5,z6]),(0,[z27,z131,z0,z3,z4,z6])],[(0,[z445,z0,z1,z4,z36,z6]),(0,[z0,z1,z260,z4,z610,z6]),(0,[z0,z377,z3,z28,z5,z6]),(0,[z15,z0,z1,z3,z903,z6])],[(0,[z236,z15,z0,z1,z3,z4]),(0,[z0,z1,z3,z904,z5,z6])],[(0,[z0,z1,z3,z905,z5,z6]),(0,[z0,z1,z3,z906,z5,z6]),(0,[z907,z1,z3,z4,z19,z6])],[(0,[z22,z0,z1,z3,z171,z6]),(0,[z908,z1,z3,z4,z5,z6])],[(0,[z0,z1,z4,z5,z6,z909]),(0,[z0,z1,z3,z4,z794,z6]),(0,[z0,z1,z3,z42,z5,z6])],[(0,[z0,z675,z3,z4,z19,z6]),(0,[z97,z100,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z910,z6]),(0,[z0,z413,z3,z4,z280,z205])],[(0,[z21,z0,z1,z911,z5,z6]),(0,[z21,z0,z1,z3,z299,z6]),(0,[z21,z0,z1,z3,z513,z6]),(0,[z97,z337,z0,z1,z4,z6]),(0,[z445,z0,z1,z4,z9,z6]),(0,[z0,z1,z3,z4,z912,z6]),(0,[z0,z649,z3,z4,z19,z6]),(0,[z0,z1,z3,z150,z74,z9])],[(0,[z913,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z169,z6,z59]),(0,[z914,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z298,z36,z6]),(0,[z915,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z610,z6]),(0,[z0,z1,z23,z50,z381,z6])],[(0,[z21,z0,z1,z3,z6,z306]),(0,[z916,z0,z1,z3,z4,z6])],[(0,[z26,z21,z173,z3,z5,z6]),(0,[z21,z0,z1,z3,z19,z6]),(0,[z15,z0,z1,z3,z4,z612]),(0,[z0,z1,z917,z3,z4,z6]),(0,[z0,z1,z3,z4,z9,z755])],[(0,[z27,z0,z3,z5,z6,z305]),(0,[z0,z1,z260,z4,z342,z6]),(0,[z15,z0,z918,z3,z4,z6])],[(0,[z344,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z919,z4,z6]),(0,[z0,z1,z260,z28,z5,z6]),(0,[z101,z0,z1,z3,z42,z6])],[(0,[z15,z0,z1,z400,z4,z6]),(0,[z0,z1,z465,z4,z36,z6])],[(0,[z0,z1,z3,z298,z9,z6]),(0,[z920,z0,z1,z4,z18,z6])],[(0,[z75,z76,z3,z298,z5,z6]),(0,[z15,z0,z1,z3,z4,z435])],[(0,[z921,z0,z1,z3,z4,z6]),(0,[z0,z1,z922,z3,z4,z6]),(0,[z0,z476,z3,z4,z19,z6]),(0,[z0,z3,z4,z6,z923,z419]),(0,[z0,z132,z3,z4,z19,z6]),(0,[z174,z0,z3,z4,z36,z6])],[(0,[z22,z0,z1,z3,z71,z6]),(0,[z483,z0,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z924,z6]),(0,[z925,z1,z3,z4,z5,z6]),(0,[z62,z0,z1,z3,z4,z46]),(0,[z0,z1,z51,z4,z165,z6])],[(0,[z22,z474,z1,z3,z5,z6]),(0,[z22,z41,z1,z3,z5,z6]),(0,[z0,z1,z3,z317,z36,z6])],[(0,[z125,z0,z1,z4,z5,z91]),(0,[z21,z0,z1,z3,z610,z6]),(0,[z0,z1,z3,z338,z9,z6]),(0,[z0,z1,z3,z5,z926,z6]),(0,[z0,z1,z3,z4,z342,z6]),(0,[z179,z0,z3,z4,z36,z37])],[(0,[z0,z1,z3,z4,z927,z6]),(0,[z0,z1,z3,z928,z5,z6]),(0,[z0,z1,z4,z6,z306,z92]),(0,[z0,z1,z3,z198,z36,z6]),(0,[z929,z0,z1,z3,z5,z6])],[(0,[z0,z1,z396,z4,z9,z6]),(0,[z0,z1,z930,z4,z5,z6]),(0,[z55,z1,z3,z189,z5,z6]),(0,[z179,z0,z223,z4,z5,z37]),(0,[z0,z1,z4,z5,z6,z498])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z732]),(0,[z0,z1,z3,z4,z931,z6])],[(0,[z22,z0,z1,z3,z36,z6]),(0,[z0,z1,z4,z36,z564,z6])]],
   [[(0,[z0,z1,z3,z4,z932,z6]),(0,[z0,z1,z3,z317,z9,z6])],[(0,[z26,z173,z3,z4,z5,z6]),(1,[z0,z3,z4,z898,z6])],[(0,[z0,z1,z3,z349,z5,z6]),(0,[z0,z1,z3,z4,z933,z6]),(0,[z0,z1,z3,z198,z9,z6]),(0,[z0,z1,z3,z4,z934,z6]),(0,[z935,z0,z1,z3,z4,z6])],[(0,[z105,z1,z187,z4,z5,z6]),(0,[z0,z1,z3,z81,z19,z6]),(0,[z182,z22,z0,z3,z36,z6]),(0,[z22,z0,z1,z9,z6,z498]),(0,[z0,z300,z3,z53,z5,z6]),(0,[z0,z1,z3,z4,z6,z936])],[(0,[z0,z1,z3,z4,z937,z6]),(0,[z0,z1,z3,z150,z5,z74])],[(0,[z134,z1,z11,z4,z36,z6]),(0,[z22,z0,z1,z3,z9,z6]),(0,[z0,z1,z3,z13,z169,z6]),(0,[z355,z0,z1,z3,z5,z59])],[(0,[z0,z1,z938,z4,z5,z6]),(0,[z21,z0,z1,z3,z342,z6]),(0,[z175,z0,z260,z53,z5,z6]),(0,[z0,z1,z3,z4,z19,z939]),(0,[z155,z0,z1,z77,z9,z6]),(0,[z0,z1,z3,z4,z940,z6])],[(0,[z0,z1,z941,z4,z5,z6]),(0,[z0,z1,z3,z5,z194,z6]),(0,[z0,z3,z4,z5,z6,z942]),(0,[z0,z413,z3,z4,z36,z205]),(0,[z15,z0,z943,z3,z4,z6])],[(0,[z75,z787,z3,z4,z5,z6]),(0,[z0,z1,z3,z349,z615,z6]),(0,[z21,z116,z1,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z944]),(0,[z179,z0,z3,z4,z5,z766])],[(0,[z22,z0,z1,z3,z334,z6]),(0,[z0,z1,z3,z4,z6,z945]),(0,[z0,z1,z3,z4,z946,z6])],[(0,[z0,z1,z3,z947,z5,z6]),(0,[z131,z0,z1,z3,z4,z6])],[(0,[z0,z1,z948,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z949]),(0,[z0,z1,z3,z950,z5,z6])],[(0,[z21,z55,z1,z3,z5,z6]),(0,[z0,z1,z3,z104,z19,z6])],[(0,[z0,z1,z3,z4,z6,z951]),(0,[z70,z1,z3,z4,z5,z14])],[(0,[z0,z1,z3,z4,z952,z6]),(0,[z175,z0,z3,z53,z5,z6]),(0,[z0,z1,z3,z4,z6,z953]),(0,[z0,z420,z3,z4,z36,z6])],[(0,[z15,z344,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z6,z954]),(0,[z0,z1,z3,z4,z955,z6])]],
   [[(0,[z956,z0,z3,z4,z5,z6]),(0,[z559,z0,z1,z77,z5,z6]),(0,[z186,z0,z1,z3,z42,z6])],[(0,[z0,z1,z3,z957,z5,z6]),(0,[z21,z0,z1,z260,z5,z6]),(0,[z0,z1,z3,z4,z958,z6]),(0,[z368,z1,z3,z4,z9,z6])],[(0,[z22,z0,z1,z52,z5,z78]),(0,[z0,z1,z3,z4,z959,z6])],[(0,[z388,z0,z1,z3,z960,z6]),(0,[z22,z0,z1,z3,z961,z6]),(0,[z22,z337,z0,z1,z5,z6]),(1,[z798,z0,z1,z3,z6]),(0,[z0,z1,z3,z962,z5,z6]),(0,[z0,z1,z3,z4,z269,z755])],[(0,[z0,z1,z3,z4,z963,z6]),(0,[z0,z1,z3,z4,z964,z6])],[(0,[z0,z1,z965,z3,z5,z6]),(0,[z55,z1,z3,z4,z5,z6]),(0,[z966,z22,z0,z1,z3,z6]),(0,[z15,z0,z1,z967,z4,z6])],[(0,[z0,z1,z968,z4,z5,z6]),(0,[z134,z343,z1,z4,z5,z6]),(0,[z0,z1,z3,z4,z969,z6]),(0,[z0,z1,z3,z970,z19,z6]),(0,[z971,z0,z1,z4,z5,z6])],[(0,[z27,z445,z0,z4,z5,z6]),(0,[z73,z0,z3,z5,z6,z419])],[(0,[z0,z414,z3,z4,z36,z6])],[(0,[z0,z1,z4,z5,z6,z972]),(0,[z22,z0,z1,z163,z5,z6]),(0,[z15,z0,z1,z3,z4,z265])],[(0,[z22,z0,z1,z3,z973,z6]),(0,[z0,z3,z4,z9,z6,z419]),(0,[z0,z1,z3,z4,z233,z6]),(0,[z974,z1,z3,z4,z5,z6])],[(0,[z22,z0,z1,z3,z314,z6]),(0,[z22,z97,z1,z3,z151,z6]),(0,[z0,z1,z3,z4,z6,z975])],[(0,[z0,z1,z976,z3,z4,z6]),(0,[z22,z0,z780,z3,z5,z6]),(0,[z118,z21,z0,z16,z5,z6]),(0,[z0,z1,z4,z5,z6,z977]),(0,[z0,z1,z978,z3,z5,z6]),(0,[z0,z1,z3,z4,z234,z9]),(0,[z0,z1,z3,z4,z6,z395])],[(0,[z15,z0,z1,z3,z104,z6])],[(0,[z0,z1,z3,z650,z5,z6]),(0,[z864,z0,z1,z3,z4,z19]),(0,[z0,z1,z979,z3,z4,z6]),(0,[z0,z3,z4,z5,z766,z37])],[(0,[z105,z1,z187,z81,z5,z6]),(0,[z105,z1,z4,z5,z6,z346]),(0,[z0,z1,z371,z3,z42,z6])]],
   [[(0,[z0,z1,z3,z153,z19,z6]),(0,[z22,z0,z1,z465,z5,z6]),(0,[z1,z3,z786,z35,z5,z6]),(0,[z179,z0,z465,z4,z5,z37]),(0,[z0,z1,z3,z980,z5,z6]),(0,[z407,z0,z492,z3,z4,z6]),(0,[z384,z0,z1,z163,z4,z6])],[(0,[z0,z1,z981,z4,z5,z6]),(0,[z97,z1,z3,z536,z151,z6]),(0,[z225,z1,z3,z4,z5,z812]),(0,[z0,z1,z371,z3,z138,z6])],[(0,[z0,z1,z3,z982,z5,z6]),(0,[z398,z0,z1,z3,z5,z216]),(0,[z983,z0,z1,z3,z5,z6]),(0,[z641,z21,z1,z3,z5,z6]),(0,[z27,z0,z3,z4,z969,z6]),(0,[z1,z3,z984,z4,z5,z6]),(0,[z0,z1,z260,z4,z19,z6]),(0,[z0,z985,z3,z4,z5,z6])],[(0,[z0,z1,z3,z30,z347,z6]),(0,[z0,z1,z986,z4,z5,z6])],[(0,[z0,z1,z3,z4,z987,z6]),(0,[z21,z0,z1,z406,z5,z6]),(0,[z27,z73,z0,z3,z5,z6]),(0,[z0,z1,z52,z4,z330,z78])],[(0,[z0,z787,z3,z4,z5,z6]),(0,[z0,z1,z161,z3,z19,z6]),(0,[z63,z22,z0,z1,z3,z6]),(0,[z22,z1,z3,z5,z206,z6]),(0,[z21,z0,z1,z3,z233,z6]),(0,[z0,z149,z3,z4,z898,z6])],[(0,[z988,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z19,z989]),(0,[z0,z1,z990,z3,z4,z6]),(0,[z196,z0,z1,z371,z3,z59])],[(0,[z22,z0,z1,z3,z381,z6]),(0,[z21,z0,z1,z3,z6,z395]),(0,[z196,z0,z1,z3,z395,z59])],[(1,[z0,z3,z723,z5,z6]),(0,[z991,z55,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z992,z6])],[(0,[z15,z993,z1,z3,z4,z6])],[(0,[z22,z0,z1,z3,z994,z6]),(0,[z0,z1,z3,z4,z6,z995])],[(0,[z70,z22,z1,z3,z5,z14]),(0,[z0,z1,z23,z667,z5,z6]),(0,[z15,z0,z1,z3,z996,z6])],[(0,[z26,z15,z173,z3,z4,z6]),(0,[z997,z0,z1,z4,z19,z6]),(0,[z15,z55,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z998,z6])],[(0,[z344,z0,z1,z3,z221,z6]),(0,[z22,z0,z149,z3,z19,z6]),(0,[z97,z1,z3,z4,z151,z6]),(0,[z0,z1,z3,z999,z5,z6]),(0,[z866,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z4,z1000,z6]),(0,[z0,z1,z3,z315,z19,z6]),(0,[z344,z264,z0,z1,z3,z6]),(0,[z0,z1,z1001,z4,z5,z6]),(0,[z0,z1,z3,z4,z1002,z6]),(0,[z0,z1,z3,z1003,z4,z6]),(0,[z0,z1,z3,z9,z6,z756])],[(0,[z0,z1,z400,z4,z36,z6]),(0,[z22,z0,z1,z5,z6,z92]),(0,[z0,z1,z3,z239,z873,z6]),(0,[z55,z1,z3,z4,z79,z6]),(0,[z1004,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z1005,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z1006,z6]),(0,[z0,z1,z3,z4,z1007,z6]),(0,[z0,z1,z3,z1008,z5,z6])],[(0,[z15,z0,z1,z260,z4,z6])],[(0,[z0,z1,z3,z4,z6,z1009]),(0,[z0,z1,z3,z1010,z5,z6])],[(0,[z63,z21,z0,z1,z3,z6]),(0,[z97,z1,z3,z4,z188,z6]),(0,[z0,z1,z1011,z4,z93,z6])],[(0,[z134,z1,z831,z4,z5,z6]),(0,[z22,z0,z1,z3,z1012,z6]),(0,[z22,z1,z3,z786,z5,z6]),(0,[z0,z1,z3,z825,z5,z6])],[(0,[z0,z1,z400,z4,z9,z6]),(0,[z0,z1,z4,z5,z564,z6]),(0,[z0,z1,z3,z338,z30,z6]),(0,[z0,z1,z3,z4,z5,z812]),(0,[z27,z0,z3,z4,z6,z306]),(0,[z327,z0,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z1013,z6])],[(0,[z75,z76,z400,z4,z5,z6]),(0,[z27,z0,z3,z4,z19,z6])],[(0,[z0,z1,z1014,z4,z5,z6]),(0,[z97,z0,z1,z163,z4,z6]),(0,[z1015,z0,z1,z3,z4,z6]),(0,[z0,z1,z51,z4,z6,z498])],[(0,[z0,z1,z3,z5,z6,z1016]),(0,[z0,z1,z3,z338,z36,z6]),(0,[z1017,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z650,z79,z6]),(0,[z15,z0,z1,z3,z42,z210])],[(0,[z279,z0,z1,z82,z5,z6]),(0,[z70,z21,z1,z3,z5,z14]),(0,[z0,z1,z4,z1018,z18,z6])],[(0,[z0,z1,z396,z4,z36,z6]),(0,[z0,z1,z1019,z4,z5,z6]),(0,[z15,z0,z1,z3,z104,z9])],[(0,[z207,z0,z1,z3,z5,z428]),(0,[z0,z1,z2,z5,z564,z6]),(0,[z0,z1,z3,z4,z290,z9]),(0,[z0,z1,z3,z9,z6,z305])],[(0,[z21,z0,z1,z396,z5,z6]),(0,[z0,z1,z1020,z4,z5,z6]),(0,[z105,z1,z187,z153,z5,z6]),(0,[z15,z22,z0,z1,z3,z6]),(0,[z0,z1,z3,z459,z926,z6]),(0,[z0,z1,z50,z1021,z5,z6])],[(0,[z0,z45,z492,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1022]),(0,[z0,z1,z3,z4,z1023,z6])],[(0,[z337,z254,z0,z1,z4,z6]),(0,[z70,z131,z1,z3,z4,z14]),(0,[z0,z1,z3,z904,z36,z6]),(0,[z0,z1,z3,z4,z6,z1024])],[(0,[z0,z1,z2,z3,z169,z6]),(0,[z225,z1,z3,z4,z459,z49]),(0,[z0,z1,z51,z4,z835,z6]),(0,[z0,z1,z3,z4,z296,z9]),(0,[z15,z753,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z1025,z6]),(0,[z1,z3,z4,z781,z151,z6]),(0,[z0,z3,z4,z723,z5,z6])],[(0,[z75,z76,z396,z4,z5,z6]),(0,[z0,z1,z3,z1026,z5,z6]),(0,[z15,z0,z1,z3,z349,z6]),(0,[z224,z0,z1,z3,z13,z6]),(0,[z22,z0,z1,z1027,z5,z6]),(0,[z22,z1,z3,z251,z5,z6]),(0,[z0,z1,z47,z3,z42,z6])],[(0,[z0,z1,z3,z4,z5,z1028]),(0,[z1029,z0,z1,z3,z5,z6]),(0,[z1030,z1,z3,z4,z5,z6]),(0,[z1031,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z794,z119,z6])],[(0,[z22,z0,z1,z3,z269,z9]),(0,[z0,z1,z3,z4,z9,z297]),(0,[z0,z1,z3,z4,z1032,z6]),(0,[z155,z0,z1,z77,z36,z6]),(0,[z0,z1,z4,z5,z6,z805])],[(0,[z0,z1,z3,z4,z1033,z6]),(0,[z15,z0,z1,z406,z4,z6]),(0,[z1,z3,z4,z5,z6,z1034]),(0,[z0,z1,z3,z138,z42,z6])],[(0,[z1035,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z9,z255]),(0,[z225,z1,z3,z4,z18,z49]),(0,[z474,z1,z3,z4,z316,z6]),(0,[z0,z1,z335,z4,z110,z6]),(0,[z0,z1,z3,z4,z1036,z6]),(0,[z0,z1,z3,z5,z1037,z6])],[(0,[z22,z1,z3,z543,z5,z6]),(0,[z0,z1,z3,z152,z496,z6])],[(0,[z21,z0,z1,z3,z586,z6]),(0,[z0,z1,z3,z42,z9,z6])],[(0,[z1,z187,z831,z4,z5,z6]),(0,[z179,z22,z0,z3,z5,z37]),(0,[z0,z1,z3,z1038,z5,z6]),(0,[z118,z0,z16,z317,z5,z6])],[(0,[z344,z0,z1,z3,z36,z6]),(0,[z0,z1,z3,z4,z6,z1039]),(0,[z22,z0,z1,z3,z1040,z6]),(0,[z0,z248,z722,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1041,z6]),(0,[z0,z1,z3,z4,z5,z1042]),(0,[z390,z0,z1,z4,z5,z12]),(0,[z15,z21,z0,z1,z3,z6]),(0,[z22,z0,z1,z3,z330,z6]),(0,[z118,z0,z16,z198,z5,z6]),(0,[z125,z0,z1,z4,z127,z12]),(0,[z0,z1,z3,z4,z1043,z6])],[(0,[z0,z76,z492,z3,z4,z6]),(0,[z832,z0,z1,z3,z5,z6]),(0,[z0,z113,z493,z3,z5,z6]),(0,[z0,z1,z23,z220,z5,z6])],[(0,[z1044,z0,z1,z3,z5,z6]),(0,[z0,z1045,z3,z4,z5,z6]),(0,[z0,z1,z3,z750,z459,z6])],[(0,[z787,z173,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1046])],[(0,[z1,z3,z4,z5,z6,z1047]),(0,[z368,z1,z3,z4,z36,z6])],[(0,[z344,z0,z1,z3,z9,z6]),(0,[z0,z1,z3,z4,z1048,z6]),(0,[z0,z1,z1049,z4,z5,z6]),(0,[z0,z1,z47,z3,z794,z6])]],
   [[(0,[z0,z1,z3,z1050,z5,z6]),(0,[z27,z55,z3,z4,z5,z6]),(0,[z196,z0,z1,z3,z19,z59]),(0,[z0,z1,z4,z36,z6,z805]),(0,[z368,z1,z223,z4,z5,z6]),(0,[z0,z1,z3,z4,z1051,z6])],[(0,[z0,z1,z4,z9,z6,z498])],[(0,[z254,z0,z1,z163,z4,z6]),(0,[z0,z1,z23,z50,z497,z6])],[(0,[z0,z1,z4,z19,z6,z867]),(0,[z0,z1,z3,z30,z794,z6])],[(0,[z182,z21,z0,z3,z36,z6]),(0,[z21,z0,z1,z3,z448,z6])],[(0,[z0,z1,z831,z4,z5,z6]),(0,[z0,z1,z3,z5,z1052,z59])],[(0,[z0,z1,z3,z4,z1053,z6])],[(0,[z15,z0,z1,z3,z536,z6]),(0,[z0,z1,z3,z338,z119,z6]),(0,[z137,z0,z1,z3,z5,z59])],[(0,[z1,z831,z11,z4,z5,z6]),(0,[z0,z1,z3,z830,z36,z6])],[(0,[z442,z0,z1,z229,z5,z6]),(0,[z97,z21,z1,z3,z151,z6]),(0,[z0,z1,z2,z3,z9,z6]),(0,[z0,z1,z3,z4,z6,z1054]),(0,[z1055,z0,z1,z3,z5,z6]),(0,[z1056,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1057,z6])],[(0,[z0,z113,z3,z28,z448,z6]),(0,[z0,z1058,z1,z3,z4,z6]),(0,[z0,z1,z3,z903,z5,z6])],[(0,[z22,z0,z1,z51,z110,z6]),(0,[z0,z1,z3,z4,z1059,z6])],[(0,[z0,z1,z3,z4,z5,z1060]),(0,[z26,z173,z3,z4,z9,z6]),(0,[z15,z0,z1,z396,z4,z6]),(0,[z0,z1,z1061,z3,z4,z6]),(0,[z22,z105,z1,z187,z5,z6]),(0,[z1062,z0,z1,z3,z4,z6]),(0,[z0,z1,z882,z4,z171,z6]),(0,[z0,z1,z163,z4,z117,z6])],[(0,[z0,z1,z3,z349,z9,z6])],[(0,[z105,z1,z187,z4,z9,z6]),(0,[z0,z1,z3,z4,z1063,z6]),(0,[z15,z0,z1,z3,z650,z6])],[(0,[z22,z307,z1,z3,z5,z6]),(0,[z15,z0,z1,z3,z4,z376]),(0,[z0,z1,z3,z4,z1064,z6])]],
   [[(0,[z0,z1,z3,z4,z1065,z6]),(0,[z1066,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z1067,z5,z6]),(0,[z966,z0,z1,z3,z4,z6]),(0,[z0,z1068,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z3,z789,z5,z6])],[(0,[z70,z1,z3,z4,z36,z14]),(0,[z0,z492,z3,z4,z36,z6]),(0,[z15,z155,z0,z1,z77,z6]),(0,[z1070,z0,z1,z3,z5,z6])],[(0,[z22,z0,z1,z3,z341,z6]),(0,[z0,z1,z3,z4,z1071,z6]),(0,[z0,z1,z3,z723,z5,z6]),(0,[z0,z1,z1072,z4,z5,z6])],[(0,[z22,z0,z1,z126,z3,z6]),(0,[z0,z3,z4,z898,z19,z6])],[(0,[z0,z1,z3,z1073,z5,z6]),(0,[z22,z1,z147,z3,z5,z6]),(0,[z357,z21,z1,z3,z5,z6]),(0,[z0,z1,z3,z1074,z5,z6]),(0,[z0,z1,z492,z3,z42,z6])],[(0,[z0,z1,z1075,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z284]),(0,[z0,z3,z4,z5,z6,z766]),(0,[z0,z1,z3,z1076,z4,z6]),(0,[z0,z1,z163,z4,z6,z34])],[(0,[z1,z3,z4,z786,z5,z6]),(0,[z15,z0,z1,z4,z6,z498]),(0,[z384,z1,z3,z4,z6,z453])],[(0,[z21,z0,z1,z3,z5,z6]),(0,[z0,z1,z1027,z4,z5,z6]),(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z359,z3,z4,z19,z6]),(0,[z70,z1,z3,z4,z9,z14]),(0,[z179,z0,z492,z3,z4,z6]),(0,[z0,z1,z3,z4,z1078,z6])],[(0,[z22,z451,z1,z3,z5,z6]),(0,[z15,z0,z1,z2,z3,z6]),(0,[z131,z0,z1,z4,z6,z92]),(0,[z175,z0,z3,z53,z9,z6]),(0,[z0,z1,z3,z4,z1079,z6]),(0,[z378,z0,z1,z163,z4,z6])],[(0,[z1080,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z34]),(0,[z0,z1,z52,z4,z364,z78])],[(0,[z21,z0,z45,z248,z5,z6]),(0,[z21,z1,z3,z617,z5,z6]),(0,[z0,z1,z1081,z4,z5,z6]),(0,[z0,z500,z3,z4,z36,z6])],[(0,[z0,z1,z3,z1082,z5,z6]),(0,[z22,z0,z1,z185,z5,z6]),(0,[z0,z1,z5,z6,z305,z92]),(0,[z0,z1,z4,z19,z1083,z6])],[(0,[z22,z0,z1,z3,z40,z6]),(0,[z21,z0,z1,z5,z6,z498]),(0,[z0,z1,z3,z4,z44,z6]),(0,[z0,z66,z3,z4,z19,z6])],[(0,[z0,z1,z3,z5,z6,z1084]),(0,[z21,z0,z1,z3,z615,z6]),(0,[z0,z1,z3,z5,z6,z1085]),(0,[z22,z0,z3,z36,z19,z6]),(0,[z70,z445,z1,z4,z5,z14]),(0,[z0,z113,z3,z28,z5,z6]),(0,[z1086,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1087,z6])]],
   [[(0,[z21,z0,z1,z3,z13,z6]),(0,[z22,z0,z1,z145,z5,z6]),(0,[z0,z1,z4,z5,z6,z1088]),(0,[z0,z1,z3,z239,z868,z6]),(0,[z0,z1,z1089,z4,z5,z6]),(0,[z0,z1,z882,z4,z36,z6]),(0,[z55,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z6,z1090]),(0,[z567,z0,z1,z3,z104,z6])],[(0,[z0,z1,z3,z298,z238,z6]),(0,[z0,z1,z3,z221,z315,z6]),(0,[z0,z1,z3,z4,z1091,z6]),(0,[z15,z21,z1,z3,z60,z6]),(0,[z0,z1,z3,z5,z6,z1092]),(0,[z63,z0,z1,z3,z4,z6])],[(0,[z22,z0,z413,z3,z5,z205]),(0,[z0,z1,z3,z4,z1093,z6]),(0,[z63,z0,z1,z3,z4,z171]),(0,[z15,z0,z1045,z3,z4,z6])],[(0,[z105,z1,z4,z5,z462,z6]),(0,[z0,z1,z3,z4,z1094,z6]),(0,[z0,z1,z3,z4,z1095,z6]),(0,[z0,z1,z3,z4,z1096,z6]),(0,[z70,z15,z1,z3,z4,z14]),(0,[z0,z1,z3,z4,z1097,z6]),(0,[z1098,z0,z1,z3,z4,z6])],[(0,[z0,z1,z163,z4,z6,z498])],[(0,[z0,z1,z3,z4,z1099,z6]),(0,[z21,z0,z1,z3,z6,z34]),(0,[z0,z1,z23,z1021,z5,z6]),(0,[z974,z1,z3,z4,z9,z6])],[(0,[z0,z1,z3,z1100,z4,z5]),(0,[z0,z1,z3,z4,z1101,z6]),(0,[z0,z45,z722,z4,z5,z6]),(0,[z0,z1,z318,z50,z5,z6]),(0,[z0,z636,z3,z4,z93,z6])],[(0,[z0,z1,z3,z4,z1102,z6])],[(0,[z0,z1,z396,z4,z238,z6]),(0,[z0,z1103,z3,z4,z5,z6]),(0,[z21,z0,z1,z3,z44,z6]),(0,[z254,z1,z3,z4,z464,z6]),(0,[z0,z1,z3,z4,z1104,z6]),(0,[z0,z1,z3,z4,z1105,z6])],[(0,[z0,z1,z3,z4,z711,z6]),(0,[z22,z0,z1,z3,z1106,z6]),(0,[z21,z368,z1,z3,z5,z6]),(0,[z15,z0,z1,z3,z4,z654]),(0,[z0,z1,z3,z1107,z5,z6]),(0,[z0,z1,z3,z650,z9,z6]),(0,[z0,z1,z163,z4,z110,z6]),(0,[z196,z0,z1,z3,z5,z1052])],[(0,[z264,z105,z0,z1,z4,z6]),(0,[z0,z1,z3,z1108,z4,z6]),(0,[z0,z1,z3,z1109,z5,z6]),(0,[z21,z0,z1,z3,z1087,z6]),(1,[z1,z3,z4,z781,z6]),(0,[z70,z1,z145,z4,z5,z14]),(0,[z1110,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z1050,z6])],[(0,[z0,z1,z3,z4,z1111,z6]),(0,[z0,z1,z3,z13,z119,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z70,z73,z1,z3,z5,z14]),(0,[z0,z1,z3,z4,z9,z235])],[(0,[z22,z378,z1,z3,z5,z6]),(0,[z0,z176,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z5,z939]),(1,[z0,z1,z4,z835,z6]),(0,[z0,z1,z892,z4,z9,z6])],[(0,[z0,z1,z4,z5,z6,z92]),(0,[z0,z1,z3,z4,z726,z6]),(0,[z21,z0,z1,z492,z3,z6]),(0,[z374,z1,z3,z4,z193,z6]),(0,[z0,z1,z223,z4,z299,z6]),(0,[z1112,z0,z1,z3,z4,z6]),(0,[z583,z0,z1,z482,z4,z6])],[(0,[z0,z1,z3,z5,z6,z94]),(0,[z1113,z0,z1,z3,z4,z6]),(0,[z15,z971,z0,z1,z4,z6])],[(0,[z0,z1,z3,z4,z1114,z6]),(0,[z22,z0,z1,z3,z93,z6]),(0,[z0,z1115,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z586,z6]),(0,[z0,z1,z3,z4,z898,z6]),(0,[z0,z1,z3,z4,z1116,z6]),(0,[z0,z1,z51,z4,z110,z6])]],
   [[(0,[z22,z0,z1,z3,z238,z6]),(0,[z109,z22,z1,z3,z5,z6]),(0,[z0,z1,z3,z1117,z5,z6]),(0,[z0,z492,z3,z4,z205,z6]),(0,[z0,z1,z3,z4,z835,z6])],[(0,[z0,z1,z223,z4,z19,z6]),(0,[z427,z0,z1,z4,z599,z6])],[(0,[z21,z0,z1,z3,z79,z6]),(0,[z1,z3,z4,z19,z1118,z6]),(0,[z0,z1,z3,z104,z5,z6])],[(0,[z155,z0,z1,z82,z5,z6]),(0,[z0,z1119,z1,z3,z5,z6]),(0,[z97,z1,z4,z564,z151,z6]),(0,[z15,z0,z1,z3,z6,z94]),(0,[z0,z1,z3,z4,z6,z1120]),(0,[z374,z1,z3,z4,z555,z6])],[(0,[z62,z22,z0,z1,z3,z6]),(0,[z0,z1,z3,z239,z19,z6]),(0,[z1121,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z42,z36,z6]),(0,[z991,z0,z1,z3,z5,z6]),(0,[z15,z0,z1,z3,z1010,z6])],[(0,[z22,z682,z1,z3,z5,z6]),(0,[z0,z1,z1122,z4,z5,z6]),(0,[z0,z1,z4,z93,z6,z867]),(0,[z0,z1,z3,z4,z1123,z6]),(0,[z15,z0,z1,z3,z4,z331])],[(0,[z75,z76,z3,z4,z19,z6]),(0,[z222,z0,z1,z3,z4,z9])],[(0,[z0,z1,z3,z4,z1124,z6]),(0,[z0,z413,z3,z4,z93,z205])],[(0,[z0,z1,z3,z1125,z5,z6]),(0,[z0,z1,z3,z189,z5,z6]),(0,[z0,z1,z3,z4,z1126,z6]),(0,[z0,z1,z3,z4,z6,z127]),(0,[z0,z1,z3,z5,z74,z1052])],[(0,[z0,z1,z3,z4,z749,z6]),(0,[z22,z0,z1,z3,z497,z6]),(0,[z27,z0,z4,z5,z6,z92]),(0,[z0,z1,z3,z4,z1127,z6]),(0,[z0,z1,z3,z170,z480,z6]),(0,[z0,z1,z3,z4,z6,z1128])],[(0,[z22,z75,z76,z3,z5,z6]),(0,[z22,z0,z1,z223,z5,z6]),(0,[z101,z0,z1,z659,z4,z6]),(0,[z0,z1,z4,z36,z6,z92]),(0,[z225,z1,z3,z4,z19,z49]),(0,[z0,z45,z248,z4,z233,z6]),(0,[z0,z177,z248,z4,z5,z6]),(0,[z1129,z0,z1,z3,z4,z6]),(0,[z1130,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z1131,z5,z6]),(0,[z311,z0,z1,z3,z6,z10])],[(0,[z0,z1,z3,z4,z6,z1132]),(0,[z0,z1,z3,z4,z754,z6]),(0,[z337,z0,z1,z4,z19,z6]),(0,[z0,z1,z3,z36,z6,z94]),(0,[z15,z0,z45,z248,z4,z6]),(0,[z412,z0,z1,z4,z286,z6])],[(0,[z0,z1,z3,z970,z5,z6]),(0,[z134,z264,z1,z11,z4,z6]),(0,[z0,z1,z3,z4,z1133,z6]),(0,[z0,z1,z3,z4,z448,z6]),(0,[z0,z1,z3,z4,z6,z1134]),(0,[z0,z1,z3,z138,z513,z6])],[(0,[z0,z1,z3,z1135,z5,z6]),(0,[z1136,z0,z1,z3,z4,z6])],[],[(0,[z0,z1,z3,z996,z5,z6]),(0,[z0,z1137,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1138,z6]),(0,[z0,z1,z3,z4,z1139,z6])]],
   [[(0,[z0,z1,z3,z5,z1140,z6]),(0,[z22,z0,z1,z3,z364,z6]),(0,[z0,z3,z4,z19,z6,z295]),(0,[z179,z15,z0,z3,z4,z37])],[(0,[z22,z33,z1,z3,z5,z6]),(0,[z0,z1,z4,z1141,z5,z6]),(0,[z0,z1,z1142,z3,z4,z6])],[(0,[z101,z0,z1,z4,z365,z6]),(0,[z0,z1,z3,z150,z169,z6]),(0,[z62,z21,z0,z1,z3,z6]),(0,[z0,z3,z215,z4,z19,z6])],[(0,[z26,z173,z3,z4,z71,z6]),(0,[z1143,z0,z1,z4,z5,z6]),(0,[z410,z0,z1,z3,z5,z389]),(0,[z21,z0,z1,z3,z6,z127]),(0,[z21,z1,z3,z60,z19,z6]),(0,[z0,z1,z2,z3,z30,z6]),(0,[z0,z1,z3,z1144,z5,z6]),(0,[z182,z0,z3,z4,z6,z34]),(0,[z0,z1,z3,z4,z1145,z6]),(0,[z0,z100,z1,z3,z42,z6])],[(0,[z0,z1,z3,z536,z5,z6]),(0,[z0,z553,z3,z4,z36,z6])],[(0,[z264,z0,z1,z3,z315,z6]),(0,[z0,z1,z3,z4,z1146,z6]),(0,[z0,z1,z3,z4,z1147,z6]),(0,[z0,z1,z3,z138,z794,z6])],[(0,[z0,z1,z2,z3,z36,z6]),(0,[z125,z0,z1,z4,z19,z12]),(0,[z0,z1,z4,z110,z835,z6]),(0,[z0,z1,z1148,z4,z5,z6])],[(0,[z0,z1,z3,z1149,z5,z6]),(0,[z0,z1,z145,z4,z19,z6]),(0,[z445,z0,z1,z5,z6,z305])],[(0,[z26,z55,z3,z4,z5,z6]),(0,[z0,z1,z3,z1150,z5,z6]),(0,[z0,z1,z51,z456,z4,z6]),(0,[z0,z1,z260,z4,z5,z6]),(0,[z0,z1,z3,z4,z1151,z6]),(0,[z1152,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z9,z6,z1034])],[(0,[z26,z173,z3,z4,z36,z6]),(0,[z179,z21,z0,z3,z5,z37]),(0,[z254,z1,z3,z4,z6,z453]),(0,[z0,z1,z3,z4,z6,z1153]),(0,[z15,z368,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1154,z6])],[(0,[z0,z1,z3,z349,z36,z6]),(0,[z0,z1,z3,z1155,z5,z6]),(0,[z0,z45,z248,z4,z19,z6]),(0,[z0,z1,z3,z4,z1156,z6])],[(0,[z0,z1,z161,z3,z5,z6]),(0,[z105,z1,z187,z4,z36,z6]),(0,[z21,z225,z1,z3,z5,z49]),(0,[z0,z3,z4,z19,z6,z419]),(0,[z0,z1,z3,z4,z1157,z6]),(0,[z1158,z1,z3,z4,z5,z6])],[(0,[z15,z22,z0,z1,z3,z9]),(0,[z0,z1,z3,z150,z36,z74]),(0,[z0,z1,z163,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z736])],[(0,[z0,z1,z396,z298,z5,z6]),(0,[z352,z0,z1,z77,z5,z6])],[(0,[z0,z1,z3,z4,z169,z6]),(0,[z0,z1,z418,z3,z408,z6])],[(0,[z0,z1,z1159,z3,z4,z6]),(0,[z15,z0,z1,z4,z564,z6]),(0,[z0,z1,z1160,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1161,z6])],[(0,[z75,z76,z3,z349,z5,z6]),(0,[z21,z0,z1,z3,z221,z6]),(0,[z0,z1,z185,z4,z19,z6])],[(0,[z378,z1,z3,z4,z151,z6]),(0,[z254,z1,z3,z338,z193,z6]),(0,[z0,z1,z3,z189,z79,z6])],[(0,[z97,z343,z1,z3,z4,z6]),(0,[z70,z1,z4,z5,z92,z14]),(0,[z907,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z315,z5,z6]),(0,[z0,z1,z3,z1162,z4,z6]),(0,[z0,z1,z1163,z4,z5,z6]),(0,[z70,z27,z3,z4,z5,z14]),(0,[z0,z1,z3,z4,z1164,z6]),(0,[z0,z1,z3,z4,z554,z6]),(0,[z0,z436,z3,z4,z36,z6])],[(0,[z0,z1,z3,z4,z1165,z6]),(0,[z0,z1,z3,z4,z1166,z6]),(0,[z22,z0,z3,z5,z6,z419]),(0,[z21,z0,z1,z5,z564,z6]),(0,[z73,z0,z1,z3,z6,z306]),(0,[z0,z1,z1011,z4,z19,z6])],[(0,[z0,z1,z3,z4,z615,z6]),(0,[z0,z1,z4,z110,z532,z6]),(0,[z22,z0,z1,z3,z459,z6]),(0,[z73,z0,z1,z3,z19,z6]),(0,[z175,z0,z3,z53,z36,z6]),(0,[z0,z943,z3,z4,z5,z6])],[(0,[z134,z1,z142,z4,z5,z6]),(0,[z15,z0,z1,z3,z239,z6]),(0,[z1167,z55,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z13,z6]),(0,[z182,z0,z3,z4,z898,z6])],[(0,[z21,z0,z1,z3,z169,z6]),(0,[z0,z1,z3,z1168,z5,z6])],[(0,[z242,z21,z1,z3,z5,z6]),(0,[z15,z21,z0,z1,z3,z9]),(0,[z0,z1,z185,z4,z610,z6]),(0,[z63,z0,z492,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1169])],[(0,[z422,z1,z11,z4,z5,z6]),(0,[z22,z0,z1170,z3,z5,z6]),(0,[z197,z21,z0,z1,z3,z6]),(0,[z254,z1,z3,z491,z4,z6])],[(0,[z27,z0,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z18,z6])],[(0,[z70,z1,z406,z4,z5,z14]),(0,[z55,z1,z3,z4,z36,z6])],[(0,[z22,z367,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z1171,z6]),(0,[z518,z100,z1,z3,z4,z6])],[(0,[z1172,z0,z1,z3,z4,z6]),(0,[z22,z0,z1,z3,z114,z6]),(0,[z21,z0,z1,z3,z554,z6]),(0,[z1,z3,z4,z193,z781,z6]),(0,[z0,z1,z3,z4,z1173,z6]),(0,[z55,z1,z223,z4,z5,z6])]],
   [[(0,[z0,z1,z400,z4,z238,z6]),(0,[z1174,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1175])],[(1,[z0,z3,z4,z5,z766])],[(0,[z21,z0,z1,z3,z1176,z6])],[(0,[z0,z1,z3,z1177,z5,z6]),(0,[z0,z1,z1178,z3,z4,z6]),(0,[z398,z0,z1,z3,z169,z6]),(0,[z0,z1,z3,z5,z849,z6])],[(0,[z1179,z0,z1,z3,z4,z6]),(0,[z22,z628,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z824,z6]),(0,[z15,z0,z1,z3,z104,z210])],[(0,[z26,z173,z3,z4,z314,z6]),(0,[z22,z136,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z119,z6]),(0,[z0,z1,z185,z4,z342,z6])],[(0,[z196,z0,z1,z3,z5,z48]),(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z1,z3,z4,z1180,z6]),(0,[z0,z1,z3,z650,z36,z6]),(0,[z368,z1,z465,z4,z5,z6]),(0,[z0,z1,z4,z5,z78,z736]),(0,[z15,z0,z1181,z3,z4,z6])],[(0,[z22,z0,z1,z163,z9,z6]),(0,[z0,z1,z3,z4,z19,z1182])],[(0,[z0,z1,z223,z650,z5,z6]),(0,[z0,z1,z3,z4,z1183,z6])],[(0,[z0,z1,z3,z350,z119,z6]),(0,[z0,z1,z3,z4,z1184,z6])],[(0,[z101,z21,z0,z1,z117,z6]),(0,[z0,z1,z3,z4,z79,z6]),(0,[z0,z1,z23,z50,z19,z6])],[(0,[z15,z0,z1,z3,z4,z691]),(0,[z1185,z0,z1,z3,z5,z6]),(0,[z15,z225,z1,z3,z4,z49]),(0,[z0,z1,z3,z4,z6,z1186]),(0,[z0,z1,z1187,z4,z5,z6]),(0,[z0,z1,z1188,z3,z19,z6])],[(0,[z0,z1,z1189,z3,z5,z6]),(0,[z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z19,z6,z305]),(0,[z1190,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z1107,z6])],[(0,[z26,z787,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z6,z804]),(0,[z15,z0,z1,z3,z4,z244])],[(0,[z0,z1,z1191,z4,z5,z6]),(0,[z22,z118,z0,z16,z5,z6]),(0,[z1192,z0,z1,z3,z4,z6]),(0,[z1,z3,z4,z5,z6,z1193]),(0,[z0,z1,z1194,z4,z5,z6]),(0,[z0,z1,z3,z4,z1195,z6]),(0,[z0,z1,z1072,z4,z9,z6])],[(0,[z0,z3,z28,z723,z5,z6]),(0,[z0,z1,z47,z3,z408,z6]),(0,[z15,z0,z1,z3,z727,z6]),(0,[z378,z1,z3,z4,z473,z6])]],
   [[(0,[z22,z0,z1,z3,z5,z808]),(0,[z0,z1,z1196,z4,z5,z6])],[(0,[z0,z1,z1197,z4,z5,z6]),(0,[z0,z1,z3,z81,z1166,z6]),(0,[z0,z3,z4,z19,z460,z6]),(0,[z1198,z0,z1,z3,z5,z6]),(0,[z0,z1,z986,z4,z9,z6]),(0,[z0,z1,z163,z4,z6,z10])],[(0,[z22,z1,z3,z5,z6,z356]),(0,[z21,z0,z1,z941,z5,z6]),(0,[z21,z1,z3,z5,z6,z693]),(0,[z1,z3,z4,z5,z6,z812]),(0,[z0,z1,z4,z5,z6,z1199]),(0,[z0,z1,z3,z4,z1200,z6])],[(0,[z56,z0,z1,z469,z5,z6]),(0,[z0,z113,z3,z28,z36,z6]),(0,[z0,z1,z227,z3,z385,z6]),(0,[z0,z1,z3,z4,z1201,z6])],[(0,[z0,z1,z3,z1202,z5,z6]),(0,[z70,z1,z3,z4,z5,z812]),(0,[z993,z1,z3,z4,z5,z6]),(0,[z15,z846,z0,z1,z3,z6])],[(0,[z388,z0,z1,z3,z19,z6]),(0,[z0,z1,z3,z4,z856,z6]),(0,[z0,z1,z3,z4,z1203,z6])],[(0,[z1204,z0,z1,z3,z4,z6]),(0,[z0,z1,z967,z4,z5,z6]),(0,[z1205,z0,z1,z3,z4,z6])],[(0,[z22,z0,z1,z371,z3,z6]),(0,[z1206,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z1207,z6]),(0,[z0,z1,z3,z4,z1208,z6]),(0,[z21,z0,z1,z3,z1162,z6]),(0,[z175,z0,z185,z53,z5,z6]),(0,[z0,z1,z816,z4,z5,z6])],[(0,[z0,z1,z3,z4,z6,z1209]),(0,[z22,z1,z3,z5,z6,z453]),(0,[z0,z1,z3,z4,z1210,z6]),(0,[z0,z1,z3,z1211,z5,z6]),(0,[z0,z113,z3,z28,z9,z6]),(0,[z0,z1,z3,z4,z6,z1212])],[(0,[z0,z1,z3,z1213,z5,z6]),(0,[z0,z770,z3,z4,z5,z6]),(0,[z0,z1,z406,z4,z19,z6]),(0,[z0,z1,z16,z198,z5,z6]),(0,[z1214,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1215,z6]),(0,[z0,z1,z1021,z77,z5,z6])],[(0,[z15,z0,z1,z3,z4,z6]),(0,[z485,z0,z300,z3,z5,z6]),(0,[z870,z0,z1,z3,z4,z6]),(0,[z0,z1,z126,z3,z4,z6]),(0,[z0,z1,z52,z4,z19,z78]),(0,[z0,z1,z3,z4,z171,z37])],[(0,[z1216,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1217,z6]),(0,[z0,z1,z3,z4,z1218,z6]),(0,[z22,z0,z1,z3,z833,z6]),(0,[z15,z0,z1,z3,z4,z171])],[(0,[z118,z0,z16,z4,z19,z6]),(0,[z0,z1,z3,z4,z1219,z6]),(0,[z0,z1,z1220,z4,z5,z6])],[(0,[z0,z1,z3,z1221,z5,z6]),(0,[z412,z0,z1,z4,z117,z6]),(0,[z0,z1,z3,z1107,z36,z6]),(0,[z0,z1,z1222,z3,z5,z6]),(0,[z1223,z0,z1,z3,z5,z6])],[(0,[z15,z73,z0,z1,z3,z6]),(0,[z0,z181,z3,z4,z19,z6]),(0,[z0,z1,z1224,z4,z5,z6])]],
   [[(0,[z22,z21,z1,z3,z19,z6]),(0,[z22,z0,z1,z3,z843,z6]),(0,[z22,z1,z3,z35,z19,z6]),(0,[z62,z0,z1,z3,z4,z6])],[(0,[z0,z1,z3,z4,z6,z923]),(0,[z0,z1,z3,z4,z1225,z6])],[(0,[z0,z1,z4,z19,z6,z498]),(0,[z0,z1,z3,z1226,z5,z6])],[(0,[z125,z22,z0,z1,z5,z12]),(0,[z0,z1,z3,z4,z1227,z6]),(0,[z0,z918,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z1107,z6])],[(0,[z22,z0,z1,z400,z5,z6]),(0,[z0,z1,z1228,z4,z5,z6]),(0,[z0,z1,z482,z4,z110,z6])],[(0,[z0,z1,z400,z298,z5,z6]),(0,[z134,z1,z221,z11,z4,z6]),(0,[z15,z445,z0,z1,z4,z6]),(0,[z1229,z1,z3,z4,z5,z6]),(0,[z0,z113,z3,z723,z5,z6]),(0,[z0,z1,z3,z4,z1230,z6])],[(0,[z0,z1,z1231,z4,z5,z6]),(0,[z22,z0,z1,z3,z5,z851]),(0,[z337,z21,z0,z1,z5,z6]),(0,[z0,z1,z1232,z4,z5,z6]),(0,[z0,z1,z3,z522,z31,z6])],[(0,[z0,z1,z1233,z4,z5,z6]),(0,[z69,z0,z1,z3,z169,z6]),(0,[z22,z378,z1,z3,z9,z6]),(0,[z0,z1,z3,z4,z1234,z6]),(0,[z0,z1,z227,z3,z119,z6])],[(0,[z0,z1,z3,z349,z238,z6]),(0,[z0,z1,z3,z4,z1235,z6])],[(0,[z0,z1,z3,z153,z5,z6]),(0,[z302,z1,z187,z4,z5,z6]),(0,[z0,z1,z4,z5,z1236,z6]),(0,[z445,z0,z1,z4,z6,z306]),(0,[z1237,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1238,z6])],[(0,[z0,z1,z3,z4,z6,z1239]),(0,[z445,z0,z1,z4,z19,z6]),(0,[z0,z3,z4,z898,z5,z6]),(0,[z0,z3,z4,z19,z6,z34])],[(0,[z0,z1,z852,z4,z5,z6]),(0,[z0,z1,z3,z4,z280,z6])],[(0,[z0,z1,z3,z19,z194,z6]),(0,[z0,z1,z3,z4,z1240,z6])],[(0,[z0,z1,z3,z4,z1241,z6]),(0,[z1242,z22,z0,z1,z3,z6]),(0,[z1243,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z189,z36,z6]),(0,[z0,z1,z3,z104,z9,z6])],[(0,[z560,z0,z1,z220,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1244]),(0,[z131,z0,z3,z4,z6,z419]),(0,[z0,z1,z3,z4,z1245,z6]),(0,[z0,z1,z3,z4,z5,z989]),(0,[z0,z1,z223,z189,z5,z6])]],
   [[(0,[z0,z1,z1246,z4,z5,z6]),(0,[z0,z1,z3,z4,z1247,z6]),(0,[z0,z1,z1248,z3,z4,z6]),(0,[z15,z0,z1,z889,z4,z6])],[(0,[z125,z21,z0,z1,z5,z12]),(0,[z200,z1,z3,z4,z193,z6]),(0,[z0,z1,z3,z4,z171,z6]),(0,[z0,z1,z1249,z3,z4,z6]),(0,[z0,z1,z4,z110,z6,z127]),(0,[z0,z1,z492,z3,z104,z6])],[(0,[z0,z1,z3,z298,z19,z6]),(0,[z0,z1,z788,z3,z4,z6]),(0,[z877,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1250])],[(0,[z0,z1170,z3,z4,z5,z6]),(0,[z73,z131,z0,z1,z3,z6]),(0,[z0,z1,z465,z4,z299,z6]),(0,[z0,z1,z3,z189,z9,z6]),(0,[z15,z0,z1,z4,z9,z498])],[(0,[z1251,z0,z3,z4,z5,z6])],[(0,[z997,z0,z1,z4,z5,z6]),(0,[z101,z0,z1,z4,z117,z6])],[(0,[z21,z0,z1,z3,z280,z6]),(0,[z0,z1,z3,z42,z193,z6]),(0,[z1252,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z1253]),(0,[z15,z0,z1,z3,z4,z546]),(0,[z0,z1,z3,z4,z6,z1254])],[(0,[z15,z0,z1,z3,z4,z466]),(0,[z0,z1,z465,z4,z19,z6]),(0,[z0,z1,z3,z4,z9,z486])],[(0,[z131,z0,z1,z3,z6,z305]),(0,[z0,z3,z360,z4,z19,z6]),(0,[z0,z636,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z1255,z6]),(0,[z271,z0,z1,z3,z42,z6]),(0,[z15,z0,z1,z3,z4,z9])],[(0,[z0,z1,z3,z1256,z5,z6]),(0,[z1257,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1258,z6]),(0,[z179,z0,z3,z4,z299,z37])],[(0,[z0,z1,z3,z4,z1176,z6]),(0,[z0,z1,z3,z1259,z5,z6])],[(0,[z0,z1,z3,z1260,z4,z6])],[(0,[z21,z0,z1,z3,z171,z6]),(0,[z0,z1,z3,z317,z19,z6])],[(0,[z22,z0,z1,z3,z299,z6]),(0,[z22,z0,z1,z3,z513,z6]),(0,[z0,z1,z3,z1261,z5,z6]),(0,[z179,z0,z3,z4,z19,z37]),(0,[z0,z1,z4,z5,z6,z715])],[(0,[z0,z1,z3,z198,z19,z6])],[(0,[z0,z1,z3,z4,z71,z6]),(0,[z22,z0,z1,z3,z900,z6]),(0,[z0,z1,z3,z536,z9,z6]),(0,[z0,z1,z4,z5,z838,z6]),(0,[z0,z1,z3,z217,z119,z6])]],
   [[(0,[z22,z0,z1,z3,z6,z306]),(0,[z0,z1,z3,z591,z30,z6])],[(0,[z22,z0,z1,z3,z19,z6]),(0,[z845,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z1262,z19,z6]),(0,[z0,z1,z163,z4,z36,z6]),(0,[z1263,z0,z1,z3,z5,z6]),(0,[z0,z1,z1148,z4,z9,z6])],[],[(0,[z0,z1,z260,z4,z9,z6]),(0,[z0,z1,z3,z150,z5,z527]),(0,[z1152,z1,z3,z4,z9,z6])],[(0,[z920,z0,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z36,z6]),(0,[z337,z0,z1,z2,z5,z6]),(0,[z337,z0,z1,z536,z5,z6]),(0,[z1264,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1265,z6]),(0,[z0,z1,z1266,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z1267])],[(0,[z0,z1,z161,z3,z9,z6]),(0,[z0,z1,z3,z4,z1268,z6]),(0,[z0,z1181,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z96])],[(0,[z1269,z0,z1,z4,z5,z6]),(0,[z134,z1,z11,z4,z19,z6]),(0,[z0,z1,z3,z4,z781,z6]),(0,[z0,z1,z1270,z4,z5,z6]),(0,[z0,z1,z163,z4,z9,z6])],[(0,[z125,z197,z0,z1,z4,z12])],[(0,[z0,z1,z3,z4,z1271,z6]),(0,[z0,z413,z3,z4,z19,z205]),(0,[z0,z1,z4,z835,z117,z6])],[(0,[z21,z0,z1,z3,z71,z6]),(0,[z0,z1,z3,z239,z5,z6]),(1,[z1,z3,z786,z5,z6]),(0,[z22,z0,z1,z3,z610,z6]),(0,[z0,z3,z4,z1272,z5,z6]),(0,[z0,z1,z3,z4,z1273,z6]),(0,[z0,z3,z4,z5,z205,z766])],[(0,[z0,z1,z3,z4,z9,z6]),(0,[z0,z1,z3,z4,z1274,z6])],[(0,[z75,z76,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1275,z6]),(0,[z0,z1,z51,z4,z684,z6])],[(0,[z22,z254,z1,z3,z193,z6]),(0,[z0,z1,z4,z5,z1276,z6]),(0,[z0,z1,z3,z4,z1277,z6]),(0,[z62,z0,z1,z3,z4,z37]),(0,[z101,z0,z1,z4,z6,z498])],[(0,[z0,z1,z335,z4,z528,z6])],[(0,[z0,z1,z3,z315,z9,z6]),(0,[z0,z1,z260,z53,z5,z6]),(0,[z0,z1,z3,z4,z334,z6]),(0,[z0,z1,z4,z1021,z5,z6]),(0,[z0,z1,z3,z4,z1278,z6]),(0,[z271,z200,z1,z3,z4,z6])]],
   [[(0,[z21,z0,z1,z3,z36,z6]),(0,[z0,z1,z3,z1279,z5,z6])],[(0,[z0,z1,z3,z1280,z5,z6]),(0,[z337,z0,z1,z4,z5,z6]),(0,[z0,z1,z47,z3,z169,z6]),(0,[z0,z1,z3,z4,z6,z1281])],[(0,[z75,z76,z3,z4,z615,z6]),(0,[z0,z3,z4,z6,z306,z419])],[(0,[z0,z1,z3,z1282,z5,z6]),(0,[z1167,z0,z1,z3,z5,z6]),(0,[z0,z1,z163,z4,z31,z6])],[(0,[z0,z1,z396,z349,z5,z6]),(0,[z21,z0,z1,z9,z6,z498]),(0,[z0,z1,z3,z1283,z5,z6]),(0,[z0,z1,z4,z93,z6,z498])],[(0,[z105,z1,z607,z4,z5,z6]),(0,[z0,z1,z3,z30,z169,z6]),(0,[z22,z0,z1,z3,z342,z6]),(0,[z0,z1,z3,z1284,z5,z6]),(0,[z0,z3,z4,z5,z6,z1285]),(0,[z101,z0,z1,z4,z835,z6]),(0,[z0,z1,z1286,z4,z5,z6])],[(0,[z21,z0,z1,z3,z9,z6]),(0,[z0,z1,z1287,z4,z5,z6]),(0,[z0,z1,z3,z4,z1288,z6])],[(0,[z27,z0,z3,z4,z9,z6]),(0,[z0,z1,z3,z36,z1289,z6]),(0,[z0,z1,z4,z1290,z5,z6]),(0,[z179,z55,z3,z4,z5,z37]),(0,[z0,z1,z4,z9,z6,z1088])],[(0,[z22,z319,z1,z3,z5,z6]),(0,[z0,z1,z3,z9,z6,z1092])],[(0,[z21,z1,z3,z60,z5,z6]),(0,[z0,z1,z3,z4,z961,z6]),(0,[z15,z22,z1,z3,z35,z6]),(0,[z21,z512,z1,z3,z5,z6]),(0,[z0,z1,z1291,z3,z5,z6]),(0,[z0,z1,z3,z4,z1292,z6]),(0,[z196,z0,z1,z3,z5,z59])],[(0,[z22,z798,z0,z1,z3,z6]),(0,[z21,z0,z1,z3,z334,z6]),(0,[z0,z1,z1293,z4,z5,z6]),(0,[z0,z1,z4,z19,z564,z6]),(0,[z0,z1,z3,z4,z6,z1294]),(0,[z1295,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z150,z40,z74])],[(0,[z22,z55,z1,z3,z5,z6]),(0,[z362,z0,z1,z3,z347,z6]),(0,[z0,z1,z3,z1296,z5,z6]),(0,[z0,z3,z4,z1297,z5,z6])],[(0,[z0,z3,z4,z93,z6,z34]),(0,[z0,z1,z3,z4,z6,z1298]),(0,[z125,z0,z1,z4,z5,z12])],[(0,[z179,z0,z3,z4,z5,z375]),(0,[z0,z1,z145,z4,z5,z6]),(0,[z0,z1,z1299,z4,z5,z6]),(0,[z101,z0,z1,z4,z6,z127]),(0,[z15,z196,z0,z1,z3,z59])],[(0,[z0,z1,z3,z138,z13,z6]),(0,[z0,z1,z4,z564,z9,z6])],[(0,[z0,z1,z4,z269,z9,z498])]],
   [[(0,[z0,z1,z3,z4,z973,z6]),(0,[z22,z0,z1,z260,z5,z6]),(0,[z0,z45,z248,z4,z5,z6]),(0,[z118,z0,z16,z4,z44,z6]),(0,[z62,z0,z1,z3,z1262,z6]),(0,[z0,z1,z790,z3,z5,z6])],[(0,[z0,z1,z3,z4,z314,z6]),(0,[z1300,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z81,z36,z6])],[],[(0,[z22,z1,z3,z464,z19,z6]),(0,[z21,z0,z1,z52,z5,z78]),(0,[z404,z1,z3,z4,z193,z6])],[(0,[z0,z1,z3,z1301,z5,z6]),(0,[z0,z1,z4,z9,z6,z92]),(0,[z0,z1,z4,z36,z1290,z6]),(0,[z1302,z0,z1,z4,z5,z6])],[(0,[z22,z0,z814,z3,z5,z6]),(0,[z0,z1,z3,z9,z6,z94]),(0,[z0,z1,z3,z4,z1303,z6]),(0,[z0,z1,z3,z4,z6,z1304]),(0,[z55,z1,z465,z4,z5,z6])],[(0,[z15,z22,z0,z1,z3,z210]),(0,[z262,z0,z1,z3,z350,z6]),(0,[z0,z1,z469,z77,z5,z6]),(0,[z706,z0,z1,z77,z5,z6]),(0,[z0,z430,z3,z4,z19,z6])],[(0,[z0,z1,z3,z4,z1305,z6]),(0,[z0,z1,z3,z81,z9,z6]),(0,[z0,z1306,z3,z4,z5,z6]),(0,[z445,z22,z0,z1,z5,z6]),(0,[z1307,z0,z1,z3,z4,z6]),(0,[z62,z196,z0,z1,z3,z4]),(0,[z0,z1,z3,z104,z30,z6])],[(0,[z15,z807,z0,z1,z3,z6])],[(0,[z21,z1,z585,z3,z5,z6])],[(0,[z15,z134,z1,z11,z4,z6]),(0,[z21,z0,z1,z163,z5,z6]),(0,[z0,z1,z3,z4,z1308,z6]),(0,[z62,z0,z1,z3,z4,z12]),(0,[z0,z1,z3,z104,z36,z6]),(0,[z0,z1,z4,z6,z127,z498])],[(0,[z0,z1,z1011,z4,z5,z6]),(0,[z125,z15,z0,z1,z4,z12]),(0,[z0,z1,z1196,z4,z9,z6])],[(0,[z21,z0,z1,z3,z314,z6]),(0,[z73,z0,z1,z3,z5,z6]),(0,[z0,z1,z1309,z4,z5,z6]),(0,[z811,z0,z1,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1310,z6]),(0,[z0,z1,z3,z4,z269,z171]),(0,[z0,z1,z3,z4,z381,z6])],[(0,[z22,z0,z1,z3,z963,z6]),(0,[z0,z1,z3,z4,z1311,z6]),(0,[z182,z0,z3,z4,z36,z6]),(0,[z63,z0,z1,z3,z904,z6]),(0,[z0,z1,z465,z650,z5,z6]),(0,[z0,z1,z52,z4,z5,z96])],[(0,[z21,z1,z3,z5,z6,z24]),(0,[z1312,z0,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z3,z4,z994,z6]),(0,[z1313,z0,z1,z3,z4,z5]),(0,[z0,z1,z3,z4,z1314,z6])],[(0,[z0,z1,z400,z4,z19,z6]),(0,[z21,z0,z1,z3,z341,z6]),(0,[z21,z0,z1,z465,z5,z6]),(0,[z15,z0,z1,z1293,z4,z6]),(0,[z15,z1121,z1,z3,z4,z6])],[(0,[z118,z0,z16,z4,z586,z6])],[(0,[z22,z0,z1,z406,z5,z6]),(0,[z0,z1,z3,z6,z306,z305])],[(0,[z22,z0,z1,z3,z233,z6]),(0,[z15,z21,z0,z1,z3,z210]),(0,[z0,z3,z4,z5,z6,z1315]),(0,[z0,z1,z3,z194,z9,z6]),(0,[z15,z355,z0,z1,z3,z4]),(0,[z0,z1,z3,z4,z1316,z6]),(0,[z179,z0,z3,z650,z5,z37]),(0,[z0,z1,z3,z1317,z5,z6])],[(0,[z0,z1,z3,z1318,z5,z6]),(0,[z445,z21,z0,z1,z5,z6]),(0,[z0,z1,z3,z5,z1319,z6]),(0,[z0,z1,z3,z4,z1320,z6])],[(0,[z22,z0,z1,z3,z6,z395]),(0,[z0,z1,z3,z4,z1321,z6]),(0,[z0,z1,z3,z4,z1322,z6]),(0,[z1323,z0,z1,z4,z5,z6]),(0,[z0,z1,z3,z522,z119,z6])],[(0,[z0,z1,z1324,z3,z5,z6]),(0,[z0,z1325,z3,z4,z5,z6]),(0,[z22,z403,z1,z3,z5,z6]),(0,[z97,z1,z3,z4,z781,z6]),(0,[z0,z1,z3,z4,z1326,z6])],[(0,[z1327,z0,z1,z3,z5,z6]),(0,[z21,z0,z1,z3,z381,z6]),(0,[z1328,z0,z1,z3,z5,z6]),(0,[z1329,z0,z1,z3,z4,z6]),(0,[z0,z1330,z1,z3,z4,z6])],[(0,[z1313,z0,z1,z3,z4,z19]),(0,[z0,z1331,z3,z4,z5,z6]),(0,[z85,z0,z1,z3,z4,z9]),(0,[z1223,z0,z1,z3,z9,z6])],[(0,[z0,z1,z3,z4,z1012,z6]),(0,[z0,z1,z3,z338,z19,z6]),(0,[z15,z0,z1,z4,z6,z92]),(0,[z0,z1,z3,z834,z5,z6]),(0,[z0,z1,z3,z5,z6,z1052]),(0,[z15,z0,z1,z3,z850,z6]),(0,[z0,z1,z1224,z4,z9,z6])],[(0,[z62,z225,z0,z1,z3,z4]),(0,[z0,z1,z1332,z3,z5,z6])],[(0,[z0,z1,z396,z4,z19,z6]),(0,[z796,z21,z0,z1,z3,z6]),(0,[z15,z1044,z0,z1,z3,z6]),(0,[z0,z1,z3,z536,z36,z6]),(0,[z197,z0,z1,z3,z4,z6]),(0,[z266,z0,z3,z4,z6,z34])],[(0,[z0,z1,z3,z4,z5,z1182]),(0,[z22,z0,z1,z1001,z5,z6]),(0,[z0,z1,z3,z1226,z9,z6])],[(0,[z0,z1,z1333,z4,z5,z6]),(0,[z75,z277,z3,z4,z5,z6]),(0,[z0,z1,z3,z153,z36,z6]),(0,[z22,z131,z0,z1,z3,z6]),(0,[z21,z0,z149,z3,z19,z6]),(0,[z1,z3,z4,z5,z812,z14]),(0,[z0,z1,z1334,z3,z4,z6])],[(0,[z0,z1,z3,z1335,z5,z6]),(0,[z0,z1,z3,z4,z5,z766])]],
   [[(0,[z21,z0,z1,z5,z6,z92]),(0,[z0,z416,z3,z4,z36,z6]),(0,[z97,z337,z1,z4,z151,z6]),(0,[z0,z1,z260,z4,z36,z6]),(0,[z62,z0,z1,z3,z4,z9]),(0,[z0,z1,z23,z50,z5,z6])],[(0,[z0,z1,z1188,z3,z5,z6]),(0,[z21,z0,z1,z3,z1321,z6]),(0,[z179,z368,z3,z4,z5,z37]),(0,[z0,z1,z163,z4,z30,z6]),(0,[z0,z1,z1232,z4,z9,z6])],[(0,[z26,z388,z173,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z1336])],[(0,[z0,z1,z161,z3,z36,z6]),(0,[z0,z4,z5,z6,z92,z419]),(0,[z0,z1,z4,z5,z1018,z6]),(0,[z0,z1,z3,z1337,z4,z6]),(0,[z15,z0,z1,z52,z4,z78])],[(0,[z0,z1,z3,z1338,z5,z6]),(0,[z105,z1,z831,z4,z5,z6]),(0,[z0,z1,z3,z153,z9,z6]),(0,[z15,z337,z0,z1,z4,z6]),(0,[z1,z1339,z3,z4,z5,z6]),(0,[z1340,z0,z1,z3,z5,z6])],[(0,[z0,z1,z3,z4,z960,z6]),(0,[z0,z1,z783,z4,z5,z6]),(0,[z0,z1,z1341,z4,z5,z6]),(0,[z21,z1,z3,z786,z5,z6]),(0,[z1342,z0,z1,z4,z5,z6]),(0,[z0,z149,z492,z3,z4,z6]),(0,[z155,z0,z1,z77,z19,z6]),(0,[z438,z0,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z1343,z6]),(0,[z15,z0,z1,z3,z904,z6]),(0,[z0,z1,z163,z4,z269,z9])],[(0,[z549,z1,z3,z4,z464,z6])],[(0,[z0,z1,z3,z4,z1344,z6])],[(0,[z0,z1,z3,z1345,z5,z6]),(0,[z0,z1,z3,z1346,z4,z6]),(0,[z22,z0,z1,z3,z1002,z6]),(0,[z0,z1,z3,z4,z1347,z6]),(0,[z0,z1,z1348,z3,z5,z6]),(0,[z0,z1,z3,z1021,z5,z6])],[(0,[z0,z1,z3,z862,z5,z6]),(0,[z0,z1,z3,z1349,z5,z6]),(0,[z0,z1350,z1,z3,z4,z6]),(0,[z0,z1,z3,z1351,z5,z6]),(0,[z63,z0,z413,z3,z4,z205]),(0,[z0,z1,z3,z104,z119,z6])],[(0,[z0,z1,z223,z4,z5,z6])],[(0,[z388,z0,z1,z3,z5,z6]),(0,[z22,z0,z1,z396,z5,z6]),(0,[z344,z0,z1,z3,z19,z6]),(0,[z0,z1,z3,z4,z1352,z6]),(0,[z0,z1,z3,z4,z6,z1353]),(0,[z0,z1,z4,z5,z6,z867])],[(0,[z0,z1,z400,z349,z5,z6]),(0,[z0,z1,z3,z315,z36,z6]),(0,[z368,z1,z3,z4,z299,z6]),(0,[z1354,z0,z1,z3,z5,z6]),(0,[z0,z1,z163,z4,z330,z6])],[(0,[z0,z1,z3,z5,z1289,z6]),(0,[z22,z259,z1,z3,z5,z6])],[(0,[z21,z0,z1,z3,z238,z6]),(0,[z0,z1,z3,z4,z1355,z6]),(0,[z0,z1,z3,z150,z5,z1052])],[(0,[z0,z1,z3,z4,z1040,z6]),(0,[z0,z1,z1356,z4,z5,z6]),(0,[z15,z0,z113,z3,z28,z6])]],
   [[(0,[z0,z1,z406,z4,z5,z6]),(0,[z22,z0,z1,z1191,z5,z6]),(0,[z22,z197,z0,z1,z3,z6]),(0,[z368,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z330,z6])],[(0,[z479,z1,z3,z4,z151,z6]),(0,[z0,z1,z3,z317,z586,z6]),(0,[z0,z1,z3,z4,z9,z622]),(0,[z0,z1,z3,z152,z30,z6]),(0,[z15,z0,z1,z465,z4,z6]),(0,[z155,z0,z1,z1021,z5,z6])],[(0,[z0,z1,z3,z4,z1357,z6]),(0,[z21,z1,z3,z252,z5,z6]),(0,[z254,z1,z3,z4,z781,z6]),(0,[z0,z1,z1163,z4,z9,z6])],[(0,[z225,z1,z3,z4,z5,z49]),(0,[z118,z0,z16,z4,z5,z6]),(0,[z0,z1,z3,z198,z586,z6]),(0,[z1358,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1359,z6]),(0,[z0,z1,z3,z4,z171,z205]),(0,[z179,z0,z3,z4,z6,z34])],[(0,[z0,z1,z3,z4,z1360,z6]),(0,[z15,z0,z1,z3,z153,z6]),(0,[z340,z0,z1,z3,z5,z48]),(0,[z21,z0,z1,z3,z269,z9]),(0,[z27,z0,z3,z4,z36,z6]),(0,[z0,z1,z3,z4,z1361,z6]),(0,[z0,z1,z4,z5,z6,z1362])],[(0,[z0,z1,z3,z4,z1363,z6]),(0,[z0,z1,z465,z189,z5,z6])],[(0,[z15,z0,z1,z3,z81,z6]),(0,[z22,z0,z1,z3,z586,z6]),(0,[z22,z383,z1,z3,z5,z6]),(0,[z22,z101,z0,z1,z117,z6]),(0,[z798,z0,z1,z3,z5,z6]),(0,[z22,z1,z3,z35,z5,z6])],[(0,[z1364,z0,z1,z3,z4,z6]),(0,[z15,z0,z1,z3,z4,z625]),(0,[z0,z1,z3,z150,z513,z74]),(0,[z63,z0,z1,z3,z42,z6])],[(0,[z21,z0,z1,z223,z5,z6]),(0,[z118,z0,z722,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1365])],[(0,[z0,z1,z3,z349,z19,z6]),(0,[z0,z1,z371,z3,z4,z6])],[(0,[z105,z1,z187,z4,z19,z6]),(0,[z21,z0,z1,z1341,z5,z6]),(1,[z0,z722,z4,z5,z6]),(0,[z0,z1,z3,z4,z1366,z6]),(0,[z0,z1,z3,z4,z9,z594]),(0,[z0,z1,z3,z4,z5,z1052])],[(0,[z1367,z0,z1,z3,z4,z6]),(0,[z0,z1,z4,z5,z6,z1368]),(0,[z21,z0,z1,z3,z330,z6]),(0,[z0,z1,z3,z4,z1369,z6]),(0,[z1370,z0,z1,z3,z5,z6]),(0,[z179,z0,z3,z189,z5,z37]),(0,[z0,z1,z3,z4,z1371,z6])],[(0,[z0,z1,z3,z4,z1372,z6]),(0,[z22,z0,z1,z3,z5,z1028]),(0,[z0,z329,z248,z4,z5,z6]),(0,[z0,z3,z4,z36,z19,z6])],[(0,[z0,z1,z3,z1373,z5,z6]),(0,[z0,z276,z248,z4,z5,z6]),(0,[z523,z0,z3,z53,z5,z6]),(0,[z0,z1,z4,z5,z244,z12])],[(0,[z134,z1,z315,z11,z5,z6]),(0,[z22,z21,z1,z3,z13,z6]),(0,[z22,z1,z3,z35,z13,z6]),(0,[z21,z0,z1,z3,z721,z6]),(0,[z0,z1,z4,z1374,z5,z6])],[(0,[z0,z541,z3,z4,z19,z6])]],
   [[(0,[z264,z21,z0,z1,z3,z6]),(0,[z0,z1,z3,z4,z1375,z6]),(0,[z0,z1,z3,z4,z1376,z6])],[(0,[z225,z1,z3,z4,z5,z168]),(0,[z0,z1,z52,z4,z5,z157]),(0,[z1377,z0,z1,z3,z5,z6])],[(0,[z0,z492,z3,z16,z4,z6])],[(0,[z70,z1,z3,z5,z305,z14]),(0,[z0,z1,z163,z4,z119,z6])],[(0,[z0,z1,z4,z5,z1083,z6]),(0,[z1378,z0,z1,z3,z5,z6]),(0,[z22,z0,z1,z3,z5,z1042]),(0,[z70,z1,z3,z4,z19,z14]),(0,[z0,z1,z223,z4,z79,z6])],[(0,[z0,z1,z3,z5,z389,z59])],[(0,[z1379,z0,z1,z3,z4,z6]),(0,[z22,z1243,z0,z1,z3,z6]),(0,[z731,z368,z1,z3,z5,z6]),(0,[z0,z1,z4,z110,z330,z6]),(0,[z15,z0,z1,z3,z962,z6])],[(0,[z1380,z0,z1,z3,z5,z6]),(0,[z0,z1,z3,z1381,z5,z6])],[(0,[z15,z0,z1,z3,z338,z6]),(0,[z1382,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z1383,z6]),(0,[z0,z3,z4,z19,z611,z6]),(0,[z387,z1,z3,z4,z188,z6])],[(0,[z22,z0,z1,z3,z1048,z6]),(0,[z0,z1,z3,z4,z341,z6])],[(0,[z0,z1,z185,z4,z5,z6]),(0,[z0,z1,z3,z4,z1384,z6])],[(0,[z0,z1,z3,z4,z1385,z6]),(0,[z15,z1198,z0,z1,z3,z6])],[(0,[z0,z1,z3,z4,z1386,z6]),(0,[z21,z0,z1,z51,z110,z6]),(0,[z337,z0,z1,z4,z9,z6]),(0,[z254,z1,z3,z193,z194,z6])],[(0,[z21,z105,z1,z187,z5,z6]),(0,[z0,z1,z465,z4,z5,z6]),(1,[z0,z1,z3,z5,z1052])],[(0,[z76,z787,z3,z4,z5,z6]),(0,[z0,z1,z3,z1387,z5,z6]),(0,[z0,z1,z3,z81,z1357,z6]),(0,[z175,z0,z3,z53,z610,z6]),(0,[z196,z0,z1,z3,z36,z59]),(0,[z0,z1,z3,z5,z6,z1388]),(0,[z15,z0,z1,z3,z42,z6])],[(0,[z0,z3,z503,z4,z19,z6]),(0,[z0,z1,z3,z4,z1389,z6])]],
   [[(0,[z22,z1,z3,z9,z6,z453])],[(0,[z0,z1,z3,z4,z9,z20])],[(0,[z22,z1,z3,z609,z5,z6]),(0,[z0,z1,z3,z317,z5,z6]),(0,[z15,z0,z1,z3,z4,z210])],[(0,[z388,z0,z1,z3,z1207,z6]),(0,[z179,z0,z3,z4,z5,z37]),(0,[z0,z1,z3,z4,z1390,z6]),(0,[z0,z1,z3,z4,z1391,z6]),(0,[z0,z1,z3,z4,z40,z6])],[(0,[z21,z0,z1,z3,z459,z6]),(0,[z21,z1,z3,z60,z9,z6]),(0,[z21,z1,z3,z312,z5,z6]),(0,[z0,z1,z3,z198,z5,z6]),(0,[z196,z0,z1,z3,z9,z59])],[(0,[z264,z0,z1,z52,z4,z6]),(0,[z21,z0,z1,z126,z3,z6]),(0,[z0,z1,z3,z5,z6,z1392]),(0,[z0,z1,z3,z4,z1393,z6]),(0,[z0,z1,z3,z4,z1394,z6])],[(0,[z0,z1,z3,z1296,z9,z6])],[(0,[z0,z1,z3,z1262,z5,z6]),(0,[z125,z0,z1,z4,z9,z12])],[(0,[z27,z75,z3,z4,z5,z6]),(0,[z0,z1,z145,z4,z9,z6])],[(0,[z1395,z0,z1,z4,z5,z6]),(0,[z0,z1,z248,z198,z5,z6]),(0,[z1302,z0,z1,z4,z36,z6])],[(0,[z0,z1,z3,z221,z4,z6]),(0,[z22,z0,z45,z248,z5,z6]),(0,[z21,z0,z1,z3,z18,z6]),(0,[z70,z1,z3,z4,z306,z14]),(0,[z0,z1,z3,z4,z1396,z6]),(0,[z175,z0,z3,z723,z5,z6]),(0,[z1,z3,z4,z5,z1118,z6]),(0,[z15,z0,z1,z3,z1284,z6])],[(0,[z0,z1,z3,z1397,z5,z6]),(0,[z0,z45,z248,z4,z9,z6])],[(0,[z22,z0,z1,z5,z6,z498]),(0,[z1242,z0,z1,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z1398]),(0,[z0,z1,z3,z4,z1399,z6]),(0,[z0,z1,z3,z1400,z5,z6])],[(0,[z134,z1,z11,z4,z5,z6]),(0,[z21,z0,z1,z185,z5,z6]),(0,[z445,z131,z0,z1,z4,z6]),(0,[z15,z0,z1,z3,z317,z6]),(0,[z62,z0,z1,z3,z150,z4])],[(0,[z0,z1,z3,z1401,z5,z6]),(0,[z15,z1377,z0,z1,z3,z6]),(0,[z21,z0,z1,z3,z40,z6]),(0,[z0,z1,z3,z1402,z5,z6]),(0,[z0,z1,z3,z4,z1403,z6]),(0,[z0,z1,z3,z138,z6,z10])],[(0,[z0,z1,z3,z4,z1404,z6]),(0,[z22,z0,z1,z3,z13,z6]),(0,[z0,z1,z3,z4,z1106,z6]),(0,[z21,z0,z3,z36,z19,z6]),(0,[z474,z1,z3,z4,z151,z6]),(0,[z0,z1,z3,z1405,z5,z6]),(0,[z0,z413,z3,z4,z5,z205])]],
   [[(0,[z0,z1,z3,z4,z1406,z6]),(0,[z15,z0,z1,z3,z1351,z6])],[(0,[z15,z0,z1,z3,z298,z6]),(0,[z0,z1,z3,z1407,z5,z6]),(0,[z21,z404,z1,z3,z5,z6]),(0,[z21,z0,z1,z145,z5,z6]),(0,[z1408,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z128,z36,z6]),(0,[z0,z1,z51,z3,z42,z6]),(0,[z0,z1,z163,z4,z93,z6])],[(0,[z1409,z0,z1,z3,z5,z6]),(0,[z0,z3,z5,z6,z305,z419]),(0,[z0,z1,z3,z317,z44,z6]),(0,[z1410,z0,z1,z3,z4,z6]),(0,[z15,z1158,z1,z3,z4,z6])],[(0,[z0,z1,z3,z5,z6,z1411]),(0,[z21,z0,z413,z3,z5,z205]),(0,[z70,z62,z0,z1,z3,z4]),(0,[z0,z113,z3,z28,z114,z6]),(0,[z0,z413,z3,z4,z554,z205])],[(0,[z22,z0,z1,z3,z6,z34]),(0,[z21,z1,z3,z214,z5,z6]),(0,[z0,z1,z3,z198,z44,z6])],[(0,[z0,z1,z1412,z3,z4,z6]),(0,[z21,z0,z1,z163,z9,z6]),(0,[z0,z1,z3,z4,z93,z6]),(0,[z62,z0,z1,z3,z4,z205])],[(0,[z0,z1,z3,z4,z238,z6]),(0,[z700,z0,z1,z4,z5,z12]),(0,[z1413,z0,z1,z4,z5,z6]),(0,[z62,z0,z1,z3,z4,z93]),(0,[z0,z1,z3,z42,z19,z6]),(0,[z0,z1,z3,z4,z6,z755]),(0,[z0,z1,z1011,z4,z9,z6])],[(0,[z22,z0,z1,z3,z44,z6]),(0,[z0,z1,z3,z786,z5,z6]),(0,[z921,z21,z0,z1,z3,z6]),(0,[z0,z1,z1414,z4,z5,z6]),(0,[z73,z0,z1,z3,z9,z6]),(0,[z0,z1,z3,z4,z1415,z6]),(0,[z368,z1,z3,z650,z5,z6]),(0,[z0,z1,z465,z4,z79,z6]),(0,[z0,z1416,z3,z4,z5,z6]),(1,[z0,z1,z1021,z5,z6]),(1,[z0,z1,z4,z5,z736])],[(0,[z22,z368,z1,z3,z5,z6]),(0,[z0,z1,z1417,z4,z5,z6])],[(0,[z0,z452,z3,z28,z5,z6]),(0,[z327,z0,z3,z53,z5,z6])],[],[(0,[z1,z787,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1418,z6]),(0,[z264,z0,z1,z4,z6,z12]),(0,[z22,z287,z1,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z736]),(0,[z15,z0,z1,z3,z1381,z6])],[(0,[z15,z22,z21,z1,z3,z6]),(0,[z22,z0,z1,z492,z3,z6]),(0,[z0,z663,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z269,z9])],[(0,[z0,z1,z3,z4,z1419,z6]),(0,[z15,z105,z1,z187,z4,z6]),(0,[z22,z0,z1,z3,z1095,z6]),(0,[z22,z0,z1,z3,z1096,z6]),(0,[z22,z339,z1,z3,z5,z6]),(0,[z1420,z1,z3,z4,z5,z6]),(0,[z0,z1,z1421,z3,z4,z6]),(0,[z179,z0,z3,z4,z79,z37]),(0,[z15,z0,z1,z163,z4,z6])],[],[(0,[z0,z1,z3,z4,z1422,z6]),(0,[z22,z0,z1,z3,z1099,z6]),(0,[z0,z1,z911,z4,z5,z6]),(0,[z1017,z0,z1,z4,z19,z6]),(0,[z0,z1,z3,z4,z497,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 496).take 487) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 983).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1479).take 71) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1550)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [496, 487, 496, 71] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 131).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 131).take 130).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 261).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 404).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [131, 130, 143, 108] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37469

theorem PEqualNP.Outside.L_meta_37469 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241832 * 2 ^ 32 + 3974684832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241832 * 2 ^ 32 + 3974684832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37469.solve