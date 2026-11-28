import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38735

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
  Nat.testBit (4276808426 * 2 ^ 32 + 3941264064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x004000002a01515c#64 ++ 0x3fb009ce7e73f3fc#64 : BitVec 128),
   (0x6880729498a4c4c5#64 ++ 0xff70f6b599accccf#64 : BitVec 128),
   (0x95070529614b0b0a#64 ++ 0xfeff0739e1cf0f0f#64 : BitVec 128),
   (0x260bb83e01f00ea0#64 ++ 0x15fff83e01f00ff0#64 : BitVec 128),
   (0x380ddfc001fea000#64 ++ 0x33efffc001fff000#64 : BitVec 128),
   (0x000eefffd4000000#64 ++ 0x0feffffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [7, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x000eefffd4000000 0x0feffffffe000000

def z1 : W := mkw 0x004000002a01515c 0x3fb009ce7e73f3fc

def z2 : W := mkw 0x260bb83e01f00ea0 0x15fff83e01f00ff0

def z3 : W := mkw 0x380ddfc001fea000 0x33efffc001fff000

def z4 : W := mkw 0x6880729498a4c4c5 0xff70f6b599accccf

def z5 : W := mkw 0x95070529614b0b0a 0xfeff0739e1cf0f0f

def z6 : W := mkw 0x95070529614b0b0a 0xffff0ff9e1ffff0f

def z7 : W := mkw 0x000cefd490000000 0x0feffff598000000

def z8 : W := mkw 0x850eeffff4010b0a 0xcffffffffe000f0f

def z9 : W := mkw 0x000cefd694000000 0x03efffc61e000000

def z10 : W := mkw 0x0000000000000000 0xfe700631818c0c0f

def z11 : W := mkw 0xfd8777bdf9efcfcf 0xfffff7bdf9efcfcf

def z12 : W := mkw 0xbd0ffffff5ffab0a 0xffffffffffffff0f

def z13 : W := mkw 0x4880428090048001 0xc0000601800c0003

def z14 : W := mkw 0x68c010002aa5d5dd 0xf010000001ffffff

def z15 : W := mkw 0x0009880001500000 0x008f080000500000

def z16 : W := mkw 0x000a882a00000000 0x008f080a00000000

def z17 : W := mkw 0x264bb83e2bf15ffc 0x1dfff83e7ff00ffc

def z18 : W := mkw 0x9507253ff54b0b0a 0xfeff073fffcf0f0f

def z19 : W := mkw 0x0602203e00000ea0 0x0410003e00000ff0

def z20 : W := mkw 0x3801100001fea000 0x3000000001fff000

def z21 : W := mkw 0x0006052940000000 0xfeff0739e18c0c0f

def z22 : W := mkw 0x0000000000000000 0x0080080a00500330

def z23 : W := mkw 0x2001100001f00000 0x1000000001f00000

def z24 : W := mkw 0x0000000000000000 0x3fa009ce7e73f000

def z25 : W := mkw 0x260bb83e01f00ea0 0x004ff03001800c00

def z26 : W := mkw 0x000eefffd4000000 0x0c4ff63ffe000000

def z27 : W := mkw 0x0000000000000000 0x33a009c00073f000

def z28 : W := mkw 0x260bb83e01f00ea0 0x37fff9fe01f3fff0

def z29 : W := mkw 0x4080201490000481 0xc000003180000c03

def z30 : W := mkw 0x6e8bfabe91f48ea1 0xc04ff631818c0c03

def z31 : W := mkw 0x2208b81600b004a0 0x0100f806003000f0

def z32 : W := mkw 0x10050500014a0000 0xfeff073181cf0c0f

def z33 : W := mkw 0x788dffd499fee4c5 0xfffffff599fffccf

def z34 : W := mkw 0x8502002960010b0a 0xcc100039e0000f0f

def z35 : W := mkw 0x2800528000a48000 0xff70f6b181accc0f

def z36 : W := mkw 0x000e8d6b44000000 0x0eef0f7be6000000

def z37 : W := mkw 0x2009980001f00000 0x11eff80001f00000

def z38 : W := mkw 0x260bb83e01f00ea0 0x157ff03401a00cc0

def z39 : W := mkw 0x060b882a01500a20 0x008f080a00500330

def z40 : W := mkw 0x000ead7f44000000 0x05eff97e66000000

def z41 : W := mkw 0x004000000a005054 0x3f3008c61e30f0fc

def z42 : W := mkw 0x950f8d6b654b0b0a 0x008f094a66430300

def z43 : W := mkw 0x0000000000000000 0x15b0080e007003f0

def z44 : W := mkw 0x0642203e2a015ffc 0x0c10003e7e000ffc

def z45 : W := mkw 0x264bb83e2bf15ffc 0x3ffff9fe7ff3fffc

def z46 : W := mkw 0x0403002801400a00 0x14ff003801c00f00

def z47 : W := mkw 0x6880729498a4c4c5 0x0100f0841820c0c0

def z48 : W := mkw 0x950fefffd54a0a02 0xc04ff631818c0c03

def z49 : W := mkw 0x000eefffd4000000 0x3feffffffe73f000

def z50 : W := mkw 0x2800528000a48000 0x3360f68001acc000

def z51 : W := mkw 0x004aa83e2a01515c 0x3ffff9fe7e73f3fc

def z52 : W := mkw 0x2601100001f00ea0 0x1010000001f00ff0

def z53 : W := mkw 0x384ddfc02bfff15c 0x3fffffce7ffff3fc

def z54 : W := mkw 0x3e0ffffe01feaea0 0x37fffffe01fffff0

def z55 : W := mkw 0x004000002a01515c 0x2b0009c67e33f0fc

def z56 : W := mkw 0x91040501600b010a 0xea000701e00f000f

def z57 : W := mkw 0x2808dac000b4a000 0x0100f8c00030f000

def z58 : W := mkw 0xbd0fdfe961ffab0a 0xfffffff9e1ffff0f

def z59 : W := mkw 0x6880100000a48481 0xc0000000018c0c03

def z60 : W := mkw 0x260bb83e01f00ea0 0x05eff83e01800c00

def z61 : W := mkw 0x000eefffd4000000 0x0a4ff7f1fe000000

def z62 : W := mkw 0x000aa83e00000000 0x0feff9fe7e000000

def z63 : W := mkw 0x2009980001f00000 0x33eff9c001f3f000

def z64 : W := mkw 0x000eeffff4010108 0x3ffffffffe43030c

def z65 : W := mkw 0x004000002a01515c 0x3f3001c47e23f0cc

def z66 : W := mkw 0x004000000a005054 0x000000000030f0f0

def z67 : W := mkw 0x0002203e00000000 0x0400003e00000000

def z68 : W := mkw 0x68c07294baa5d5dd 0xfff0ffffffffffff

def z69 : W := mkw 0x954705296b4b5b5e 0xffff0fffffffffff

def z70 : W := mkw 0x0001000001400000 0x10ef000001c00000

def z71 : W := mkw 0x060eefffd4000ea0 0x0ffffffffe000ff0

def z72 : W := mkw 0x004000002a01515c 0x0c10000e7e0003fc

def z73 : W := mkw 0x6a88fa9698b4c4e5 0x0100f8861830c0f0

def z74 : W := mkw 0x6e8bfabe99f4cee5 0xfffffebf99fccfff

def z75 : W := mkw 0x000aa83e00000000 0x15fff83e007003f0

def z76 : W := mkw 0x2601100001f00ea0 0x15b0080e01f00ff0

def z77 : W := mkw 0x180447c0000ea000 0x220007c0000ff000

def z78 : W := mkw 0x260fffffd5f00ea0 0x1ffffffffff00ff0

def z79 : W := mkw 0x6e8bfabe91f48ea1 0xd5fffe3f81fc0ff3

def z80 : W := mkw 0xa70bb83f61f10faa 0xddfff83fe1f00fff

def z81 : W := mkw 0x3e0fffffd5feaea0 0x3ffffffffffffff0

def z82 : W := mkw 0x040ba83e01400a00 0x15fff83e01c00f00

def z83 : W := mkw 0x0000000000000000 0x32a0010000430000

def z84 : W := mkw 0x260bb83e01f00ea0 0x014ff83601b00cf0

def z85 : W := mkw 0x380ddfc1d5fea000 0x3befffc1fffff000

def z86 : W := mkw 0x380d9d4001fea000 0x308f094001fff000

def z87 : W := mkw 0x204030142aa155dc 0x3ff0f9fe7ff3fffc

def z88 : W := mkw 0xb70fbd3f61fb0faa 0xfefff739e1cf0f0f

def z89 : W := mkw 0x384ddfc023ffb118 0x33efffca67fff330

def z90 : W := mkw 0xfd8ffffdf9ffefcf 0xfffffffdf9ffffcf

def z91 : W := mkw 0x000aa83e00000000 0x05eff83e00000000

def z92 : W := mkw 0x0602002a00000a20 0x0000000a00000330

def z93 : W := mkw 0x380ddfc001fea000 0xfffffff181fffc0f

def z94 : W := mkw 0x0000000000000000 0x0fa009ce7e000000

def z95 : W := mkw 0x6880729498a4c4c5 0xfff0ffffffaccccf

def z96 : W := mkw 0x000e8d6b44000000 0x000f000000000000

def z97 : W := mkw 0x0407052941400a00 0x1eff0739e1c00f00

def z98 : W := mkw 0x9d0747e9614fab0a 0xfeff07f9e1cfff0f

def z99 : W := mkw 0xd587253df94b4fcf 0xfeff073df9cf0fcf

def z100 : W := mkw 0x2208b81600b004a0 0x1570f83601b00cf0

def z101 : W := mkw 0x000eefffd4000000 0x004ff63180000000

def z102 : W := mkw 0x060b882a01500a20 0x14ff083a01d00f30

def z103 : W := mkw 0x0000000000000000 0x10100000007003f0

def z104 : W := mkw 0x95030029614b0b0a 0xfc100039e1cf0f0f

def z105 : W := mkw 0x2609980001f00ea0 0x11fff80001f00ff0

def z106 : W := mkw 0x0002203fd4000000 0x0fa009fffe000000

def z107 : W := mkw 0x0008ead694000000 0x0fa0f9ce7e000000

def z108 : W := mkw 0x0000000000000000 0x1470003001800c00

def z109 : W := mkw 0x6e81729499f4cee5 0xff70f6b599fccfff

def z110 : W := mkw 0x280cdfc000a48000 0x33efffc001acc000

def z111 : W := mkw 0x380ddfc001fea000 0x004ff600018c0000

def z112 : W := mkw 0x6889fa9499f4c4c5 0xfffffeb599fccccf

def z113 : W := mkw 0x2000301400a00480 0x0100f004002000c0

def z114 : W := mkw 0x204998002bf1515c 0x3ffff9ce7ff3f3fc

def z115 : W := mkw 0x100d8d40015a2000 0x008f094000533000

def z116 : W := mkw 0x95010000214b0b0a 0xf010000001cf0f0f

def z117 : W := mkw 0x95070529414a0a02 0xc04f0631818c0c03

def z118 : W := mkw 0x954fefffff4b5b5e 0xffffffffffffffff

def z119 : W := mkw 0x000ccfc000000000 0x03efffc000000000

def z120 : W := mkw 0x380fffffd5fea000 0x3feffffffffff000

def z121 : W := mkw 0x100dcfc0014a0000 0x33efffc001cf0000

def z122 : W := mkw 0x0008ead694000000 0x0100f8c61e000000

def z123 : W := mkw 0x910eeffff40b010a 0xefeffffffe0f000f

def z124 : W := mkw 0x380ddfc001fea000 0x304ff60001fff000

def z125 : W := mkw 0x95070529614b0b0a 0xffff0f3fe1ff0fff

def z126 : W := mkw 0x0000000000000000 0x0080094000533000

def z127 : W := mkw 0x004000000a005054 0x010008c61e30f0f0

def z128 : W := mkw 0x2200100000b004a0 0x00000000003000f0

def z129 : W := mkw 0x0000629490000000 0xff70f6b5998c0c0f

def z130 : W := mkw 0x2248b8160ab054f4 0x0100f8c61e30f0f0

def z131 : W := mkw 0x004eeffffe01515c 0x2feffffffe03f00c

def z132 : W := mkw 0x6880729498a4c4c5 0xeb00f685982cc0cf

def z133 : W := mkw 0x95070529614b0b0a 0xf05f063181cf0f0f

def z134 : W := mkw 0x488000000804c045 0xe0000000000cc00f

def z135 : W := mkw 0x3805150001fea000 0x32ef070001fff000

def z136 : W := mkw 0x0008ead694000000 0x0f60fef79e000000

def z137 : W := mkw 0x380ddfc001fea000 0x37ffffce01fff3f0

def z138 : W := mkw 0x0006052940000000 0x0eef0739e0000000

def z139 : W := mkw 0x004000002a01515c 0x2e1001ce7e03f3fc

def z140 : W := mkw 0x000aa83fd4000000 0x0deff83ffe000000

def z141 : W := mkw 0x004447c1fe01515c 0x3fb00fcffe73f3fc

def z142 : W := mkw 0x000447c1d4000000 0x0a0007c1fe000000

def z143 : W := mkw 0x280cdfc000b4a000 0x03efffc00030f000

def z144 : W := mkw 0x004eeffffe01515c 0x0ffffffffe0003fc

def z145 : W := mkw 0x260bb83e21f10fa8 0x3ffff93e61f30ffc

def z146 : W := mkw 0xb70fbd3f41fa0ea2 0xd5fffe3f81fc0ff3

def z147 : W := mkw 0x14070528014a0a00 0x36ff073801cf0f00

def z148 : W := mkw 0x004000002a01515c 0x1db0080e7e7003fc

def z149 : W := mkw 0x004000000a005054 0x33a009c61e73f0f0

def z150 : W := mkw 0x264bb83e0bf05ef4 0x15fff8fe1ff0fff0

def z151 : W := mkw 0x2800100000b4a000 0x000000000030f000

def z152 : W := mkw 0x0403002801400a00 0xfeff063981cc0f0f

def z153 : W := mkw 0x6880729498a4c4c5 0xcd10f0b59820cccf

def z154 : W := mkw 0x3e0bb83e01feaea0 0x35fff83e01fffff0

def z155 : W := mkw 0x2000301400a00480 0x0040f03001800c00

def z156 : W := mkw 0x384110002bfff15c 0x3010000001fff3fc

def z157 : W := mkw 0x95070529614b0b0a 0xc0cf0739e1cf0f03

def z158 : W := mkw 0xdd8747a9f94fcb4f 0xfeff07b9f9cfcf0f

def z159 : W := mkw 0x0000000000000000 0x32600600018c0000

def z160 : W := mkw 0x264ffffffff15ffc 0x3ffffffffff3fffc

def z161 : W := mkw 0x000e8d6b44000000 0x008f094a66000000

def z162 : W := mkw 0x6880100008a4c4c5 0xf010000001accccf

def z163 : W := mkw 0x68c010002aa5d5dd 0xffb009ce7fffffff

def z164 : W := mkw 0x6880729490a48481 0xc040f631818c0c03

def z165 : W := mkw 0x2000301400a00480 0x1570f03401a00cc0

def z166 : W := mkw 0x668bb83e99f04ee5 0xddfff83f99f00fff

def z167 : W := mkw 0x260bb83e01f00ea0 0x018ff80e007003f0

def z168 : W := mkw 0x060aa83e00000ea0 0x05fff83e00000ff0

def z169 : W := mkw 0x8506052960010b0a 0xceff0739e0000f0f

def z170 : W := mkw 0x954705296b4b5b5e 0xfeff07f9ffcfff0f

def z171 : W := mkw 0x788dffd499fee4c5 0xff7ff6b599accccf

def z172 : W := mkw 0x380ddfc001fea000 0x32eff70001cf0000

def z173 : W := mkw 0x004000002a01515c 0x311008c61e73f3fc

def z174 : W := mkw 0xb70bb83e21fb0faa 0xf5fff83e01ff0fff

def z175 : W := mkw 0x0000000008004044 0x3f3000841820c0cc

def z176 : W := mkw 0x0000000020010108 0x3eb001086043030c

def z177 : W := mkw 0x004eeffffe01515c 0x3ffffffffe73f3fc

def z178 : W := mkw 0x68807294b8a5c5cd 0xfff0f7bdf9efcfcf

def z179 : W := mkw 0x68c072949aa4d4d5 0xff70fef79fbcfcff

def z180 : W := mkw 0x004000002a01515c 0x0c90094e7e5333fc

def z181 : W := mkw 0x0002203fd4000000 0x0c00003ffe000000

def z182 : W := mkw 0x0042203ffe01515c 0x0c10003ffe0003fc

def z183 : W := mkw 0x380fdfeb45fea000 0x33efffca67fff000

def z184 : W := mkw 0x0000000000000000 0x14b0000800400300

def z185 : W := mkw 0x104d8d40235b3118 0x008f094a66533330

def z186 : W := mkw 0x2248b8162ab155fc 0x3fb0f9ce7e73f3fc

def z187 : W := mkw 0x8502002960010b0a 0x0000000860000300

def z188 : W := mkw 0x10050500014a0000 0x32ef070001cf0000

def z189 : W := mkw 0x95070529614b0b0a 0x008f010860430300

def z190 : W := mkw 0x950fcfe9614b0b0a 0xfffffff9e1cf0f0f

def z191 : W := mkw 0x004000000a005054 0x0fa009ce7e30f0f0

def z192 : W := mkw 0x95470529634b1b1a 0xfeff0f7be7df3f3f

def z193 : W := mkw 0x68c07294baa5d5dd 0xff70f6b599ffffff

def z194 : W := mkw 0x0000629490000000 0x0f60f6b598000000

def z195 : W := mkw 0x0000000020010108 0x2a0001006003000c

def z196 : W := mkw 0x2009980001f00000 0x004ff00001800000

def z197 : W := mkw 0x2808dac000b4a000 0x0000f00000000000

def z198 : W := mkw 0x40802014980044c5 0xcc10003598000ccf

def z199 : W := mkw 0x810000016001010a 0xc8000001e000000f

def z200 : W := mkw 0x3809980001fea000 0x31eff80001fff000

def z201 : W := mkw 0x200bb83e01f00000 0x15eff83e01f00000

def z202 : W := mkw 0x78cdffd4bbfff5dd 0xffffffffffffffff

def z203 : W := mkw 0x0000000000000000 0xc0400631818c0c03

def z204 : W := mkw 0x3a0dffd601fea4a0 0x33efffc601fff0f0

def z205 : W := mkw 0x0004050140000000 0x0a000701e0000000

def z206 : W := mkw 0x950feffff54b0b0a 0xffffffffffcf0f0f

def z207 : W := mkw 0x0000629490000000 0x0fe0fffffe000000

def z208 : W := mkw 0x180eefffd40ea000 0x2feffffffe0ff000

def z209 : W := mkw 0x004000002a01515c 0xfff00fffffffffff

def z210 : W := mkw 0x000000002801414c 0x3fb0018c7863c3cc

def z211 : W := mkw 0xb70fbd3f61fb0faa 0x15fff93e61f30ff0

def z212 : W := mkw 0x380ffffe01fea000 0x37effffe01fff000

def z213 : W := mkw 0x488062949804c045 0xef60f6b5980cc00f

def z214 : W := mkw 0x95070529614b0b0a 0x0eef0739e0430300

def z215 : W := mkw 0x6ecbfabebbf5dffd 0xffffffffffffffff

def z216 : W := mkw 0x004000002a01515c 0x080000007e00000c

def z217 : W := mkw 0x0042203ffe01515c 0x3fb009fffe73f3fc

def z218 : W := mkw 0x488062949804c4c5 0xee1006b5980ccccf

def z219 : W := mkw 0x2609b81601f00ea0 0x1110f80601f00ff0

def z220 : W := mkw 0x380ddfc001fea000 0x00cfff4001df3000

def z221 : W := mkw 0xbd01100021ffab0a 0xf010000001ffff0f

def z222 : W := mkw 0x260bb83e01f00ea0 0x105ff03001f00ff0

def z223 : W := mkw 0x688effffdca4c4c5 0xffffffffffaccccf

def z224 : W := mkw 0x6880729498a4c4c5 0xc140f6b599acccc3

def z225 : W := mkw 0x2000301400a00480 0xff70f63581ac0ccf

def z226 : W := mkw 0x000ccfc000000000 0x33efffc00073f000

def z227 : W := mkw 0x00406294ba01515c 0x3ff0fffffe73f3fc

def z228 : W := mkw 0x100dcfc0015a2000 0x03efffc000533000

def z229 : W := mkw 0x0000000000000000 0x37b009ce0073f3f0

def z230 : W := mkw 0x380ddfc021ffa108 0x3fffffc861fff30c

def z231 : W := mkw 0x488042809804c045 0xea000681980cc00f

def z232 : W := mkw 0xb90ddfc161ffa10a 0xfbefffc1e1fff00f

def z233 : W := mkw 0x788fffffddfee4c5 0xfffffffffffffccf

def z234 : W := mkw 0x380fffffd5fea000 0x0fefffffff8c0000

def z235 : W := mkw 0x68c072949aa4d4d5 0x0100f8c61e30f0f0

def z236 : W := mkw 0x2208b81600b004a0 0x0000f00000000000

def z237 : W := mkw 0x95070529614b0b0a 0xcc5f0639e18c0f0f

def z238 : W := mkw 0x10040540000a2000 0x0000014000033000

def z239 : W := mkw 0x004000002a01515c 0x301000000073f3fc

def z240 : W := mkw 0x91060529600b010a 0xeeef0739e00f000f

def z241 : W := mkw 0x260bb83fd5f00ea0 0x1dfff83ffff00ff0

def z242 : W := mkw 0xbd07152961ffab0a 0xfeff0739e1ffff0f

def z243 : W := mkw 0xb707152961fb0faa 0xfeff0739e1ff0fff

def z244 : W := mkw 0x3801528001fea000 0x3360f68001fff000

def z245 : W := mkw 0x954705296b4b5b5e 0xfeff073fffcf0fff

def z246 : W := mkw 0x000467d5d4000000 0x0f60f7f5fe000000

def z247 : W := mkw 0x000eefffd4000000 0x1ffffffffe7003f0

def z248 : W := mkw 0x0000000020010108 0x3fb0090e607303fc

def z249 : W := mkw 0x180547c0014ea000 0x32ef07c001cff000

def z250 : W := mkw 0x0000000000000000 0x0a0001c07e000000

def z251 : W := mkw 0x0002002940000000 0x0c000039e0000000

def z252 : W := mkw 0x950747e9f54b0b0a 0xfeff07f9ffcf0f0f

def z253 : W := mkw 0x2000100000a00480 0x1010000001a00cc0

def z254 : W := mkw 0x2603303e01f00ea0 0x1410003e01f00ff0

def z255 : W := mkw 0x004447c1fe01515c 0x2a0007c1fe03f00c

def z256 : W := mkw 0x004000002a01515c 0x00100000000003fc

def z257 : W := mkw 0x688afabe98a4c4c5 0xfffffebf99accccf

def z258 : W := mkw 0x000eefffd4000000 0x05effe3f80000000

def z259 : W := mkw 0x2000100000a00000 0x1160f00001a00000

def z260 : W := mkw 0x6e8272be98a4cee5 0xff70f6bf99accfff

def z261 : W := mkw 0x260bb83e01f00ea0 0xfffffe3f81fc0fff

def z262 : W := mkw 0x950feffff54b0b0a 0xfefff739e1cf0f0f

def z263 : W := mkw 0x004000002a01515c 0x2a0001c07e03f00c

def z264 : W := mkw 0x180447c1d40ea000 0x2a0007c1fe0ff000

def z265 : W := mkw 0x2808fad694b4a000 0x0100f8c61e30f000

def z266 : W := mkw 0x380ddfc001fea000 0x224ff7c0018ff000

def z267 : W := mkw 0x000eefffd4000000 0x03effff180000000

def z268 : W := mkw 0x2403303c01e00e80 0x15fff03c01e00fc0

def z269 : W := mkw 0x8500000020010b0a 0xc010000000000f0f

def z270 : W := mkw 0x220ab83e00b004a0 0x05eff83e003000f0

def z271 : W := mkw 0x6880729498a4c4c5 0xcc50f635998c0ccf

def z272 : W := mkw 0x40800000080044c5 0xc010000000000ccf

def z273 : W := mkw 0x0000000020010108 0x0c1000086000030c

def z274 : W := mkw 0x004e8d6b66011118 0x008f094a66533330

def z275 : W := mkw 0x260fbd3f41f00ea0 0x1fffff3fe1f00ff0

def z276 : W := mkw 0x000aeabe90000000 0x0feffebf98000000

def z277 : W := mkw 0x970f8d2b615b0b2a 0x008f090a60530330

def z278 : W := mkw 0xb70fbd3f61fb0faa 0xffffff3fe1ff0fff

def z279 : W := mkw 0xbd0ddfc021ffab0a 0xf3ffffc001ffff0f

def z280 : W := mkw 0x004000000a005054 0x15b008ce1e70f3f0

def z281 : W := mkw 0x260bb83e01f00ea0 0x1ffff9fe7ff00ff0

def z282 : W := mkw 0x2603102801f00ea0 0x14ff003801f00ff0

def z283 : W := mkw 0x95070529614b0b0a 0xea4f0731e18f0c0f

def z284 : W := mkw 0x0040000022011118 0x0080094a66533330

def z285 : W := mkw 0x004000002a01515c 0x2a8009ca7e53f33c

def z286 : W := mkw 0x380dffd401fea480 0x37fffff401fffcc0

def z287 : W := mkw 0x0000201490000000 0x0c00003598000000

def z288 : W := mkw 0x0000201694000000 0x000000061e000000

def z289 : W := mkw 0x688effffd4a48481 0xc04ff631818c0c03

def z290 : W := mkw 0x160f8d6a015a2a20 0x008f094a00533330

def z291 : W := mkw 0x004000002a01515c 0x3eb001c87e43f30c

def z292 : W := mkw 0x004000002a01515c 0x018009ce7e73f3f0

def z293 : W := mkw 0x954100002b4b5b5e 0xf010000001ffffff

def z294 : W := mkw 0x384ddfc02bfff15c 0x3befffc07ffff00c

def z295 : W := mkw 0x0000000020010108 0x3fb009c86073f30c

def z296 : W := mkw 0x384ffffffffff15c 0x3ffffffffffff3fc

def z297 : W := mkw 0x4080000098004045 0xc80000019800000f

def z298 : W := mkw 0x0000000000000000 0x3e3000000000000c

def z299 : W := mkw 0x0000201400000480 0x0410003400000cc0

def z300 : W := mkw 0x2800729400a48480 0x3770f6b401acccc0

def z301 : W := mkw 0x2000729490a00480 0x1f70f6b599a00cc0

def z302 : W := mkw 0x2000301400a00480 0x15f0f83e01f00ff0

def z303 : W := mkw 0x380dffd491fea000 0x3feffff599fff000

def z304 : W := mkw 0x95010000214b0b0a 0x0000000000430300

def z305 : W := mkw 0x95070529414a0a02 0xfe7f0631818c0c0f

def z306 : W := mkw 0x40802014980044c5 0x00000004180000c0

def z307 : W := mkw 0x688cffd498a4c4c5 0xfffffff599accccf

def z308 : W := mkw 0x788ddfc009fee4c5 0xf3ffffc001fffccf

def z309 : W := mkw 0x000e8d6b44000000 0x0faf09ce7e000000

def z310 : W := mkw 0x6888fad498b4e4c5 0x0100f8c41830f0c0

def z311 : W := mkw 0x3e4ffffe2bfffffc 0x3ffffffe7ffffffc

def z312 : W := mkw 0x000aeafe94000000 0x05eff8fe1e000000

def z313 : W := mkw 0x990447c1600fa10a 0xea0007c1e00ff00f

def z314 : W := mkw 0x0000000000000000 0x1fb009ce7e7003f0

def z315 : W := mkw 0x004eeffff6011118 0x0feffffffe533330

def z316 : W := mkw 0xb50f9d2961fb0b0a 0xffffff39e1ff0f0f

def z317 : W := mkw 0x4682203e98004ee5 0xcc10003f98000fff

def z318 : W := mkw 0xfd8ffffffdefcfcf 0xffffffffffefcfcf

def z319 : W := mkw 0x6888fad69ca4c4c5 0xff70fef79faccccf

def z320 : W := mkw 0x000eefffd4000000 0x0f6ff6b598000000

def z321 : W := mkw 0x200fffffd5f00000 0x1feffffffff00000

def z322 : W := mkw 0x6888fad498b4e4c5 0xff70fef599bcfccf

def z323 : W := mkw 0x0800428000048000 0x22000680000cc000

def z324 : W := mkw 0x95070529414a0a02 0xceef0739e18c0c03

def z325 : W := mkw 0x384110002bfff15c 0x3fb009ce7ffff3fc

def z326 : W := mkw 0x0000000008004044 0x3fb009ce7e20c0cc

def z327 : W := mkw 0x8503002961410b0a 0xdcff0039e1c00f0f

def z328 : W := mkw 0x6a88fa9698b4c4e5 0xff70feb799bcccff

def z329 : W := mkw 0x360fbd7e01fa2ea0 0x15fff97e01f33ff0

def z330 : W := mkw 0x0000000008004044 0x301000000020c0cc

def z331 : W := mkw 0x0000000000000000 0xcc10003180000c0f

def z332 : W := mkw 0x95070529614b0b0a 0x32ef070861cf0300

def z333 : W := mkw 0x2800100000a48000 0x3000000001acc000

def z334 : W := mkw 0x004000000a005054 0x000000c01e00f000

def z335 : W := mkw 0x380cdfc000bea000 0x2300ffc0003ff000

def z336 : W := mkw 0x0000629498004044 0x3f70f6b59820c0cc

def z337 : W := mkw 0x0000000008004044 0x2a0000801800c00c

def z338 : W := mkw 0x10050500014a0000 0x33ef0fc001fff000

def z339 : W := mkw 0x91050501614b010a 0xfaef0701e1cf000f

def z340 : W := mkw 0x18000000000ea000 0x20000000000ff000

def z341 : W := mkw 0x91000000200b010a 0xe0000000000f000f

def z342 : W := mkw 0x6880100008a4c4c5 0x000000000020c0c0

def z343 : W := mkw 0x2808dac000b4a000 0x3360fec001bcf000

def z344 : W := mkw 0x6880729498a4c4c5 0xfff0fff599fffccf

def z345 : W := mkw 0x3e0ddfc001feaea0 0x33ffffc001fffff0

def z346 : W := mkw 0x6880729490a48481 0xcf60f6b5998c0c03

def z347 : W := mkw 0x6e8bb83e09f4cee5 0xf5fff83e01fccfff

def z348 : W := mkw 0x6880729498a4c4c5 0xea40f6b1998ccc0f

def z349 : W := mkw 0x68c07294baa5d5dd 0xff70f7f5ffaffccf

def z350 : W := mkw 0x488042809804c045 0xff300685982cc0cf

def z351 : W := mkw 0x004000002a01515c 0x0fb009ce7e0003fc

def z352 : W := mkw 0x10010000014a0000 0x3000000001cf0000

def z353 : W := mkw 0x950f8d6b654b0b0a 0xfeff0f7be7cf0f0f

def z354 : W := mkw 0x788ddfc099fee045 0xfbefffc199fff00f

def z355 : W := mkw 0x0000201400000000 0x0560f03400000000

def z356 : W := mkw 0x264110002bf15ffc 0x3010000001f3fffc

def z357 : W := mkw 0x40802014980044c5 0xff3000b59820cccf

def z358 : W := mkw 0x0040000022011118 0x0000000000533330

def z359 : W := mkw 0x02002016000004a0 0x00000006000000f0

def z360 : W := mkw 0xd9844781f80fc14f 0xea000781f80fc00f

def z361 : W := mkw 0x004000002a01515c 0x3090094a6673f3fc

def z362 : W := mkw 0x044300282b415b5c 0x3fff09fe7ff3fffc

def z363 : W := mkw 0x0006052940000000 0x008f010860000000

def z364 : W := mkw 0xbd0fdfe961ffab0a 0xfefff739e1cf0f0f

def z365 : W := mkw 0x95070529614b0b0a 0xcc9f0139e0430f0f

def z366 : W := mkw 0x970f8d2b615b0b2a 0xfeff0f3be1df0f3f

def z367 : W := mkw 0x0000000000000000 0xea000601800c000f

def z368 : W := mkw 0x6880100008a4c4c5 0xff30008419accccf

def z369 : W := mkw 0x380557c001fea000 0x320007c001fff000

def z370 : W := mkw 0x380ddfc001fea000 0x018ff9c00073f000

def z371 : W := mkw 0x260bb83e01f00ea0 0x14fff03801c00f00

def z372 : W := mkw 0x2208b81600b004a0 0x15b0f80e007003f0

def z373 : W := mkw 0x2800729490a48000 0x3f60f6b599acc000

def z374 : W := mkw 0x6e8bfabe99f4cee5 0xff7ff6b599accccf

def z375 : W := mkw 0x3e0ffffe01feaea0 0x15fffe3e01fc0ff0

def z376 : W := mkw 0x384ddfc00bfef054 0x33efffc61ffff0f0

def z377 : W := mkw 0x10050500014a0000 0x008f010000430000

def z378 : W := mkw 0x6880729498a4c4c5 0xf110f08419accccf

def z379 : W := mkw 0x100d8d40015a2000 0x33af09c00073f000

def z380 : W := mkw 0x000eefffd4000000 0xffffffffff8c0c0f

def z381 : W := mkw 0x220effffd4b004a0 0x0feffffffe3000f0

def z382 : W := mkw 0x488042809804c045 0x000000801800c000

def z383 : W := mkw 0x2e0bfafe01f4aea0 0x15fff8fe01f0fff0

def z384 : W := mkw 0x000ccfc000000000 0x004ff60000000000

def z385 : W := mkw 0x0006052940000000 0x004f063180000000

def z386 : W := mkw 0x8502203ff4010b0a 0xcc10003ffe000f0f

def z387 : W := mkw 0x6880729498a4c4c5 0xfff0febf99fccfff

def z388 : W := mkw 0x260bb83e09f04ee4 0x3ffff8be19f0cffc

def z389 : W := mkw 0x0000000008004044 0x3fb0088e1870c3fc

def z390 : W := mkw 0x6880301408a4c4c5 0xf570f03401accccf

def z391 : W := mkw 0x004000002a01515c 0x0d1008ce7e30f3fc

def z392 : W := mkw 0x6880729498a4c4c5 0x0f60f6b59820c0c0

def z393 : W := mkw 0x68c07294baa5d5dd 0xff70f6bfffaccfff

def z394 : W := mkw 0x260bb83e01f00ea0 0x00cff83a01d00f30

def z395 : W := mkw 0x68c07294baa5d5dd 0x3fb0f9ce7e73f3fc

def z396 : W := mkw 0x95050500214b0b0a 0xf2ff070001cf0f0f

def z397 : W := mkw 0x200ddfc001f00000 0x13efffc001f00000

def z398 : W := mkw 0x380457c000aea000 0x3360f7c001aff000

def z399 : W := mkw 0x000647e9d4000000 0x0eef07f9fe000000

def z400 : W := mkw 0x004000002a01515c 0x3ba009c07e73f00c

def z401 : W := mkw 0x0006253fd4000000 0x0eef073ffe000000

def z402 : W := mkw 0x95010000014a0a02 0xc0000000018c0c03

def z403 : W := mkw 0x0642203e2a015ffc 0x3fb009fe7e73fffc

def z404 : W := mkw 0x2848dac02ab5f15c 0x3fb0f9ce7e73f3fc

def z405 : W := mkw 0x0601000001500a20 0x0000000000500330

def z406 : W := mkw 0x000447c1d4000000 0x0fa00fcffe000000

def z407 : W := mkw 0x000ccfc1d4000000 0x0befffc1fe000000

def z408 : W := mkw 0x91040501600b010a 0xfe700731e18f0c0f

def z409 : W := mkw 0x000447c1d4000000 0x0000060180000000

def z410 : W := mkw 0x0048ead69e005054 0x0100f8c61e30f0f0

def z411 : W := mkw 0x6880301498a4c4c5 0xfc10003599accccf

def z412 : W := mkw 0x000eeffe00000000 0x07effffe00000000

def z413 : W := mkw 0x004000002a01515c 0x35b0080e0073f3fc

def z414 : W := mkw 0x2009980001f00000 0x15fff80e01f003f0

def z415 : W := mkw 0x2808dac000b4a000 0x33a0f9c00073f000

def z416 : W := mkw 0x95070529614b0b0a 0xffff0fffffcf0f0f

def z417 : W := mkw 0x488eefffdc04c045 0xefeffffffe0cc00f

def z418 : W := mkw 0x0000428090000000 0x0a00068198000000

def z419 : W := mkw 0x688677bdd8a4c4c5 0xfffff7bdf9accccf

def z420 : W := mkw 0x0000629490000000 0x0100f08418000000

def z421 : W := mkw 0x2800528000a48000 0x0040f600018c0000

def z422 : W := mkw 0x10010000015a2000 0x0000000000533000

def z423 : W := mkw 0x184447c02a0ff15c 0x2a0007c07e0ff00c

def z424 : W := mkw 0x064b882a2b515b7c 0x3fbf09ce7e73f3fc

def z425 : W := mkw 0x7881100009fee4c5 0xf010000001fffccf

def z426 : W := mkw 0x2602303e00a00ea0 0x1570f03e01a00ff0

def z427 : W := mkw 0x0000000008004044 0x0c100004180000cc

def z428 : W := mkw 0x380ddfc001fea000 0x336ff68001acc000

def z429 : W := mkw 0xbd0fdfe941feaa02 0xf3effff181fffc03

def z430 : W := mkw 0x0402002800000a00 0x0410003800000f00

def z431 : W := mkw 0x3e0fdfea01feaa20 0x33efffca01fff330

def z432 : W := mkw 0x8702203f60010faa 0xcc10003fe0000fff

def z433 : W := mkw 0x360fbd3e01fa0ea0 0x37ffff3e01ff0ff0

def z434 : W := mkw 0x950f8d69615b2b0a 0x008f094860533300

def z435 : W := mkw 0x0002002b44000000 0x0000000a66000000

def z436 : W := mkw 0x260bb83e01f00ea0 0x045ff03e01800ff0

def z437 : W := mkw 0x0000000000000000 0x010008c61e000000

def z438 : W := mkw 0xbd0fdfe961ffab0a 0x33efffc861fff300

def z439 : W := mkw 0x6880729498a4c4c5 0xf050f63181accccf

def z440 : W := mkw 0x0040000022011118 0x0fa009ce7e533330

def z441 : W := mkw 0x000262bfd4000000 0x0f60f6bffe000000

def z442 : W := mkw 0x004000002a01515c 0x33b009c00073f3fc

def z443 : W := mkw 0x0403002821410b08 0x3eff013861c30f0c

def z444 : W := mkw 0x2800528008a4c044 0x3f70f68419acc0cc

def z445 : W := mkw 0x8502002940000a02 0xc000003180000c03

def z446 : W := mkw 0x0000000008004044 0x3fb009c41873f0cc

def z447 : W := mkw 0x0048ead6be01515c 0x3fb0f9ce7e73f3fc

def z448 : W := mkw 0x260fffffd5f00ea0 0x15fffe3f81f00ff0

def z449 : W := mkw 0x0004050000000000 0x02ef070000000000

def z450 : W := mkw 0x260bfafe95f00ea0 0x15fff8fe1ff00ff0

def z451 : W := mkw 0x000042c094000000 0x000000c01e000000

def z452 : W := mkw 0x0602203e00000ea0 0x0000003000000c00

def z453 : W := mkw 0x000eefffd4000000 0x00cfff7be6000000

def z454 : W := mkw 0x6880729490a48481 0x0000f00000000000

def z455 : W := mkw 0x380ddfc001fea000 0x3fefffce7ffff000

def z456 : W := mkw 0x2800528000a48000 0x33e0ffc001fff000

def z457 : W := mkw 0xbf0fffff61ffafaa 0xffffffffe1ffffff

def z458 : W := mkw 0xbd0757a961ef8b0a 0xfffff7b9e1efcf0f

def z459 : W := mkw 0x104d8d402b5b715c 0x3fbf09ce7e73f3fc

def z460 : W := mkw 0x688effffdca4c4c5 0x0feffffffe20c0c0

def z461 : W := mkw 0x380ddfc001fea000 0x014ffec001bcf000

def z462 : W := mkw 0x180dcfc0015ea000 0x228f0fc0005ff000

def z463 : W := mkw 0x688477d5dca4c4c5 0xff70f7f5ffaccccf

def z464 : W := mkw 0x260b982a01f00ea0 0x109f080a01f00ff0

def z465 : W := mkw 0x380fdfe941fea000 0x3feffff9e1fff000

def z466 : W := mkw 0x3e0ffffe01feaea0 0x004ff630018c0c00

def z467 : W := mkw 0x380ddfc009fee044 0x3fffffc419fff0cc

def z468 : W := mkw 0x260b982a01f00a20 0x11eff80a01f00330

def z469 : W := mkw 0x0603203e01400ea0 0x14ff003e01c00ff0

def z470 : W := mkw 0x060b882a01500a20 0x000f000000000000

def z471 : W := mkw 0x2008980000b00000 0x0100f80000300000

def z472 : W := mkw 0x200effffd4a00480 0x1fffffffffa00cc0

def z473 : W := mkw 0x004000002a01515c 0x3c10000e7e73f3fc

def z474 : W := mkw 0x0602203fd4000ea0 0x0c10003ffe000ff0

def z475 : W := mkw 0x954705296b4b5b5e 0xfeff0739e1ffffff

def z476 : W := mkw 0x0000428000000000 0x0360f68000000000

def z477 : W := mkw 0x2e0bfabe01f48ea0 0x37fffebe01fccff0

def z478 : W := mkw 0x6880729490a48481 0xd570f63581ac0cc3

def z479 : W := mkw 0x000ccfc000000000 0x0fefffce7e000000

def z480 : W := mkw 0x380ddfc001fea000 0x03efffc0018c0000

def z481 : W := mkw 0x854200296a015b5e 0xcc10003ffe000fff

def z482 : W := mkw 0x004605296a01515c 0x3fff0ffffe73f3fc

def z483 : W := mkw 0x0000000008004044 0xff7006b599accccf

def z484 : W := mkw 0x6880729490a48481 0xfe70f631818c0c0f

def z485 : W := mkw 0x300d9d4001fa2000 0x11eff94001f33000

def z486 : W := mkw 0x0000000000000000 0x0ea0010860000000

def z487 : W := mkw 0x40806294980044c5 0xcf70f6b598000ccf

def z488 : W := mkw 0x95070529614b0b0a 0x3ebf01086043030c

def z489 : W := mkw 0x3c0fdfe801feaa00 0x37fffff801ffff00

def z490 : W := mkw 0x0008880000000000 0x01eff80000000000

def z491 : W := mkw 0x0000000020010108 0xfef00739e1cf0f0f

def z492 : W := mkw 0xff8fffbff9ffcfef 0xffffffbff9ffcfff

def z493 : W := mkw 0x0401000001400a00 0x1010000001c00f00

def z494 : W := mkw 0x10050500214b0108 0x3eff070861cf030c

def z495 : W := mkw 0x000667ffd4000000 0x0e0007fffe000000

def z496 : W := mkw 0x910447c1f40b010a 0xea0007c1fe0f000f

def z497 : W := mkw 0x0208880200100020 0x0000080200100030

def z498 : W := mkw 0x0040000022011118 0x3eb0094a6653333c

def z499 : W := mkw 0x004000002a01515c 0x3a1001c07e73f3fc

def z500 : W := mkw 0x100d8d40015a2000 0x000f000000000000

def z501 : W := mkw 0x0040000022011118 0x15b0094e667333f0

def z502 : W := mkw 0x060ba83e01500a20 0x05eff83e00500330

def z503 : W := mkw 0x080042c00004a000 0x000000c00000f000

def z504 : W := mkw 0x000cefd7d4000000 0x0b00ffc7fe000000

def z505 : W := mkw 0x6e8fffffddf4cee5 0xfffffffffffccfff

def z506 : W := mkw 0x2209b81601f004a0 0x11eff80601f000f0

def z507 : W := mkw 0x0000000000000000 0x0e60063180000000

def z508 : W := mkw 0x000ead7fd4000000 0x0c8f097ffe000000

def z509 : W := mkw 0x408eefffdc0044c5 0xcffffffffe000ccf

def z510 : W := mkw 0x7885779499eec4c5 0xfffff7b599efcccf

def z511 : W := mkw 0xc582203df8014fcf 0xcc10003df8000fcf

def z512 : W := mkw 0x180447c0000ea000 0x33a00fc0007ff000

def z513 : W := mkw 0x95070529694b4b4e 0xffff07bdf9efcfcf

def z514 : W := mkw 0x95070529414a0a02 0x000f000000000000

def z515 : W := mkw 0x7881729499fee4c5 0xff70f6b599fffccf

def z516 : W := mkw 0x6880729498a4c4c5 0x3f30f0841820c0cc

def z517 : W := mkw 0x3e01100001feaea0 0x3010000001fffff0

def z518 : W := mkw 0x000eefffdc004044 0x3ffffffffe20c0cc

def z519 : W := mkw 0x000667bdd0000000 0x0feff7bdf8000000

def z520 : W := mkw 0x200ab83e00a00480 0x15fff83e01a00cc0

def z521 : W := mkw 0x6888fad69ca4c4c5 0x0100f8c61e20c0c0

def z522 : W := mkw 0x004000002a01515c 0x2fa009ce7e03f00c

def z523 : W := mkw 0x95010000214b0b0a 0xfeb0010861cf0f0f

def z524 : W := mkw 0x688effffd4a48481 0xcfefffffff8c0c03

def z525 : W := mkw 0x950fefffd54a0a02 0xcfefffffff8c0c03

def z526 : W := mkw 0x380fffffd5fea000 0x33effff181fff000

def z527 : W := mkw 0x0040000002001010 0x0000084206103030

def z528 : W := mkw 0x0006052940000000 0x0fef0ffffe000000

def z529 : W := mkw 0x688effffdca4c4c5 0xff7ff6b599accccf

def z530 : W := mkw 0x6880528008a4c4c5 0xf370f68001accccf

def z531 : W := mkw 0x2809dac001f4a000 0x11eff8c001f0f000

def z532 : W := mkw 0x000447c000000000 0x020007c000000000

def z533 : W := mkw 0x6880729490a48481 0xf360f6b181accc03

def z534 : W := mkw 0x264bb83e2bf15ffc 0x35fff83e01f3fffc

def z535 : W := mkw 0x0000000020010108 0x301000000043030c

def z536 : W := mkw 0x0040000022011118 0x0000014066033000

def z537 : W := mkw 0x100fefffd54a0000 0x3fefffffffcf0000

def z538 : W := mkw 0x000aeaffd4000000 0x0d00f8fffe000000

def z539 : W := mkw 0x40802014980044c5 0xfe700635998c0ccf

def z540 : W := mkw 0x854200296a015b5e 0xffb009fffe73ffff

def z541 : W := mkw 0x0600000000000ea0 0x0010000000000ff0

def z542 : W := mkw 0x180ccfc0000ea000 0x23efffc0000ff000

def z543 : W := mkw 0x4082203fdc0044c5 0xcc10003ffe000ccf

def z544 : W := mkw 0x004000002a01515c 0x3f3000841873f3fc

def z545 : W := mkw 0x3e0ffffe01feaea0 0x33effff001fffc00

def z546 : W := mkw 0x95070529414a0a02 0xf2ef073181cf0c03

def z547 : W := mkw 0x7e8ffffe99feeee5 0xffffffff99ffffff

def z548 : W := mkw 0xfd8777bdd1ee8e83 0xc04ff631818c0c03

def z549 : W := mkw 0x000c8d4000000000 0x008f094000000000

def z550 : W := mkw 0x0602203e00000ea0 0x15b0083e00700ff0

def z551 : W := mkw 0x000eefffd4000000 0x018ff9ce7e000000

def z552 : W := mkw 0x68cefffffea5d5dd 0xffffffffffffffff

def z553 : W := mkw 0x6880528098a4c4c5 0xfa10068199accccf

def z554 : W := mkw 0x264110002bf15ffc 0x3fb009ce7ff3fffc

def z555 : W := mkw 0x91040501400a0002 0xc0000601800c0003

def z556 : W := mkw 0x788dffd491fea481 0xc04ff631818c0c03

def z557 : W := mkw 0x060f8d6b45500a20 0x008f094a66500330

def z558 : W := mkw 0x0403002801400a00 0x004f003001800c00

def z559 : W := mkw 0xb70ffffff5fb0faa 0xffffffffffff0fff

def z560 : W := mkw 0x0000000008004044 0x010000841820c0c0

def z561 : W := mkw 0x6880729498a4c4c5 0x3360f68419acc0c0

def z562 : W := mkw 0x8502002960010b0a 0xfeb00139e0430f0f

def z563 : W := mkw 0xb507353d61eb0f8a 0xfffff73de1ef0fcf

def z564 : W := mkw 0x0000000000000000 0x300000000073f000

def z565 : W := mkw 0x6880100008a4c4c5 0xfe70063181accccf

def z566 : W := mkw 0x0000000020010108 0x0080010860430300

def z567 : W := mkw 0x104505002b4b515c 0x3fff0fce7ffff3fc

def z568 : W := mkw 0x0040000022011118 0x0000000a66000330

def z569 : W := mkw 0x060b882a01500a20 0x15bf080e007003f0

def z570 : W := mkw 0x95070529614b0b0a 0xea8f0709e04f030f

def z571 : W := mkw 0x48c04280ba05d15d 0xffb00fcffe7ff3ff

def z572 : W := mkw 0x240b982801f00a00 0x15fff83801f00f00

def z573 : W := mkw 0x00000001d4000000 0x08000001fe000000

def z574 : W := mkw 0x100f8d6b455a2000 0x008f094a66533000

def z575 : W := mkw 0x688272bfdca4c4c5 0xff70f6bfffaccccf

def z576 : W := mkw 0x6880729498a4c4c5 0x1570f0b419a0ccc0

def z577 : W := mkw 0x40c02014ba0155dd 0xffb009fffe73ffff

def z578 : W := mkw 0x0040000022011118 0x33a009ca6673f330

def z579 : W := mkw 0x000aa83e00000000 0x004ff03000000000

def z580 : W := mkw 0x0000000000000000 0x11a0080000700000

def z581 : W := mkw 0x300d9d0001fa0000 0x33efff0001ff0000

def z582 : W := mkw 0x0008cac000000000 0x0100f8c000000000

def z583 : W := mkw 0x0008a81600000000 0x0100f80600000000

def z584 : W := mkw 0x950767bdf14b0b0a 0xfffff7bdf9cf0f0f

def z585 : W := mkw 0x004000002a01515c 0x3eb0010e7e4303fc

def z586 : W := mkw 0x2000301408a044c4 0x3f70f0b419a0cccc

def z587 : W := mkw 0xfdc777bdfbefdfdf 0xffffffffffffffff

def z588 : W := mkw 0x184447c02a0ff15c 0x3fb00fce7e7ff3fc

def z589 : W := mkw 0x260bb83e01f00ea0 0x11eff83001f00c00

def z590 : W := mkw 0x060fefffd5500a20 0x0feffffffe500330

def z591 : W := mkw 0xfd81100029efcfcf 0xf010000001efcfcf

def z592 : W := mkw 0x95030028214b0b0a 0xf4ff003801cf0f0f

def z593 : W := mkw 0x0000000000000000 0x01000806003000f0

def z594 : W := mkw 0x264bb83e23f11fb8 0x15fff97e67f33ff0

def z595 : W := mkw 0xf9847795f8afc5cf 0xff70f7b5f9afcccf

def z596 : W := mkw 0x284052802aa5d15c 0x3ff0ffce7ffff3fc

def z597 : W := mkw 0x380fffffd5fea000 0x004ff631818c0000

def z598 : W := mkw 0x0000000000000000 0x332000800020c000

def z599 : W := mkw 0x950feffff54b0b0a 0x0feffffffe430300

def z600 : W := mkw 0x0008884000102000 0x0000084000103000

def z601 : W := mkw 0x8502002960010b0a 0xfe700639e18c0f0f

def z602 : W := mkw 0x0002203fd4000000 0x0000003180000000

def z603 : W := mkw 0x0008ead694000000 0x0000f00000000000

def z604 : W := mkw 0x2848dac00ab4f054 0x0100f8c61e30f0f0

def z605 : W := mkw 0x91040501600b010a 0x0000010060030000

def z606 : W := mkw 0x100d8d40015a2000 0x32ef0f4001df3000

def z607 : W := mkw 0x004000002a01515c 0x200000000003f00c

def z608 : W := mkw 0x95070529614b0b0a 0xf09f010861cf0f0f

def z609 : W := mkw 0xb70fbd3f41fa0ea2 0xc04ff631818c0c03

def z610 : W := mkw 0x488042809804c045 0xfe7006b1998ccc0f

def z611 : W := mkw 0x004000002a01515c 0x3f30008e7e20c3fc

def z612 : W := mkw 0x260ab83e00b00ea0 0x0510f83e00300ff0

def z613 : W := mkw 0x10070529414a0000 0x3eef0739e1cf0000

def z614 : W := mkw 0x9707253f614b0faa 0xfeff073fe1cf0fff

def z615 : W := mkw 0x0403002801400a00 0x008f000800400300

def z616 : W := mkw 0x100fefffd55a2000 0x0feffffffe533000

def z617 : W := mkw 0x2009b81401f00480 0x15fff83401f00cc0

def z618 : W := mkw 0x260fffffd5f00ea0 0x004ff63181800c00

def z619 : W := mkw 0x0000000000000000 0xf0100000018c0c0f

def z620 : W := mkw 0x10050500014a0000 0x004f0600018c0000

def z621 : W := mkw 0x0008884204000000 0x0000084206000000

def z622 : W := mkw 0xfd87152969efcfcf 0xfeff0739e1efcfcf

def z623 : W := mkw 0x280effffd4a48000 0x3fefffffffacc000

def z624 : W := mkw 0x260ffffe01f00ea0 0x17fffffe01f00ff0

def z625 : W := mkw 0x064b882a23511b38 0x008f094a66533330

def z626 : W := mkw 0x788dffd491fea481 0xf3effff181fffc03

def z627 : W := mkw 0x950f8d69615b2b0a 0xfeff0f79e1df3f0f

def z628 : W := mkw 0xfd817294b9efcfcf 0xff70f6b599efcfcf

def z629 : W := mkw 0x004000000a005054 0x000000061e0000f0

def z630 : W := mkw 0x384ddfc02bfff15c 0x33ffffc001fff3fc

def z631 : W := mkw 0x0000000000000000 0x010008c00030f000

def z632 : W := mkw 0x000ecfebd4000000 0x0a8f0fcbfe000000

def z633 : W := mkw 0x2809da8001f48000 0x33effe8001fcc000

def z634 : W := mkw 0x6e8bfabe99f4cee5 0x15fff8be19f0cff0

def z635 : W := mkw 0x2601100001f00ea0 0x0000000001800c00

def z636 : W := mkw 0x0000000000000000 0x220001c00003f000

def z637 : W := mkw 0x0002002800000000 0x04ef003800000000

def z638 : W := mkw 0x180447c0000ea000 0x00000600000c0000

def z639 : W := mkw 0x95060529600b0b0a 0xee100739e00f0f0f

def z640 : W := mkw 0x788dffd499fee4c5 0x33efffc419fff0c0

def z641 : W := mkw 0x914405016a0b515e 0xea0007c1fe0ff00f

def z642 : W := mkw 0x280effffd4b4a000 0x0feffffffe30f000

def z643 : W := mkw 0x3801100001fea000 0x00000000018c0000

def z644 : W := mkw 0x0006052960010108 0x3eff0739e043030c

def z645 : W := mkw 0x0000000000000000 0x05a0080e00000000

def z646 : W := mkw 0x40c02014ba0155dd 0xcc10003ffe000fff

def z647 : W := mkw 0x0000000000000000 0x03a009c000000000

def z648 : W := mkw 0x260fbd7f45f00ea0 0x15fff97e67f00ff0

def z649 : W := mkw 0xb74fbd3f6bfb5ffe 0xffffffffffffffff

def z650 : W := mkw 0x000eefffd4000000 0x014ffef79e000000

def z651 : W := mkw 0x060ba83e01500ea0 0x049f083e00500ff0

def z652 : W := mkw 0x380dffd695fea000 0x33efffc61ffff000

def z653 : W := mkw 0x6080301498a044c5 0xdd70f03599a00ccf

def z654 : W := mkw 0x588447c0980ee045 0xea0007c1980ff00f

def z655 : W := mkw 0xbd0fdfe941feaa02 0xc04ff631818c0c03

def z656 : W := mkw 0x95070529414a0a02 0xd4ff063981cc0f03

def z657 : W := mkw 0x2a08fad600b4a4a0 0x0100f8c60030f0f0

def z658 : W := mkw 0x0000000000000000 0x0080094a66000000

def z659 : W := mkw 0x2601301401f00ea0 0x1570f03401f00ff0

def z660 : W := mkw 0x260fffffd5f00ea0 0x0fefffffff800c00

def z661 : W := mkw 0x48c04280ba05d15d 0xea0007c1fe0ff00f

def z662 : W := mkw 0x788477d498aee4c5 0xff70f7f599affccf

def z663 : W := mkw 0x914405016a0b515e 0xffb00fcffe7ff3ff

def z664 : W := mkw 0x950fad3f614b0b0a 0xffffff3fe1cf0f0f

def z665 : W := mkw 0x6e81100009f4cee5 0xf010000001fccfff

def z666 : W := mkw 0x0403002801400a00 0x15ff083e01f00ff0

def z667 : W := mkw 0x954705296b4b5b5e 0x3fbf09ce7e73f3fc

def z668 : W := mkw 0x0000629490000000 0x0040f63180000000

def z669 : W := mkw 0x0000000000000000 0x0410000e000003f0

def z670 : W := mkw 0x004eefffde005054 0x0feffffffe30f0f0

def z671 : W := mkw 0x260bfabe91f00ea0 0x1ffffebf99f00ff0

def z672 : W := mkw 0x3809dac001fea000 0x3100f8c001fff000

def z673 : W := mkw 0x004e8d6b6e01515c 0x3fbf09ce7e73f3fc

def z674 : W := mkw 0x0000000000000000 0x0000000000000000

def z675 : W := mkw 0x3801100001fea000 0x33a009c001fff000

def z676 : W := mkw 0x10040500000a0000 0x22000700000f0000

def z677 : W := mkw 0xb701100021fb0faa 0xf010000001ff0fff

def z678 : W := mkw 0x004ccfc02a01515c 0x3fffffce7e73f3fc

def z679 : W := mkw 0x0000000000000000 0x15300004002000c0

def z680 : W := mkw 0x91040501600b010a 0xfeb00709e04f030f

def z681 : W := mkw 0xfd8777bdd9eecec7 0xff7ff6b599accccf

def z682 : W := mkw 0x040fefffd5400a00 0x1fffffffffc00f00

def z683 : W := mkw 0xed8272bdf8a5cfcf 0xff70f6bdf9accfcf

def z684 : W := mkw 0x95470529634b1b1a 0x008f094a66533330

def z685 : W := mkw 0x3805578001ee8000 0x33eff78001efc000

def z686 : W := mkw 0x954100002b4b5b5e 0xffb009ce7fffffff

def z687 : W := mkw 0x000ecfeb44000000 0x03efffca66000000

def z688 : W := mkw 0x000ecfe940000000 0x0feffff9e0000000

def z689 : W := mkw 0x0000000000000000 0x0f20008418000000

def z690 : W := mkw 0x0000000020010108 0x3fb009ce7e43030c

def z691 : W := mkw 0xfd8777bdf1ef8f8b 0xfefff739e1cf0f0f

def z692 : W := mkw 0x000ead3f40000000 0x0fefff3fe0000000

def z693 : W := mkw 0x380ddfc001fea000 0x11effe0001fc0000

def z694 : W := mkw 0x0004054144000000 0x0000014066000000

def z695 : W := mkw 0x95010000214b0b0a 0xfe70063181cf0f0f

def z696 : W := mkw 0x004000002a01515c 0x3eb001086073f3fc

def z697 : W := mkw 0xbd4fdfe96bfffb5e 0xffffffffffffffff

def z698 : W := mkw 0x2800528000a48000 0x0100f0800020c000

def z699 : W := mkw 0x0000000000000000 0x0c00000e7e000000

def z700 : W := mkw 0x2208fad694b004a0 0x0100f8c61e3000f0

def z701 : W := mkw 0x488447c1dc04c045 0xea0007c1fe0cc00f

def z702 : W := mkw 0x6880528098a4c045 0xfb60f68199acc00f

def z703 : W := mkw 0x95050501614b0b0a 0xfa100701e1cf0f0f

def z704 : W := mkw 0x000eefffd4000000 0x0eeff739e0000000

def z705 : W := mkw 0x95070529614b0b0a 0x14ff013861c30f00

def z706 : W := mkw 0x6c8372bc99e4cec5 0xfffff6bd99eccfcf

def z707 : W := mkw 0x004447c1fe01515c 0x0a0007c1fe00000c

def z708 : W := mkw 0x78c110002bfff5dd 0xf010000001ffffff

def z709 : W := mkw 0xfdc110002befdfdf 0xf010000001ffffff

def z710 : W := mkw 0x3a0ddfc001fea4a0 0x33efffc001fff0f0

def z711 : W := mkw 0x3803303fd5fea000 0x3c00003ffffff000

def z712 : W := mkw 0x380ddfc205fea000 0x33efffc207fff000

def z713 : W := mkw 0x1e0667fe000eaea0 0x261007fe000ffff0

def z714 : W := mkw 0x954f8d6b674b1b1a 0x008f094a66533330

def z715 : W := mkw 0x2603303fd5f00ea0 0x1c10003ffff00ff0

def z716 : W := mkw 0xad0adae960b5ab0a 0xcd10f8f9e030ff0f

def z717 : W := mkw 0x000aeafe94000000 0x0feff9fe7e000000

def z718 : W := mkw 0x6880729498a4c4c5 0xf370f6b181accccf

def z719 : W := mkw 0x2800729400a48480 0xff70f6b581accccf

def z720 : W := mkw 0x260bb83e01f00ea0 0x37fffe3e01fc0ff0

def z721 : W := mkw 0x6880729490a48481 0xf050f631818c0c0f

def z722 : W := mkw 0x260bb83e01f00ea0 0x157ff03e01a00ff0

def z723 : W := mkw 0x950f8d69615b2b0a 0x008f010860430300

def z724 : W := mkw 0x000eefffd4000480 0x0ffffffffe000cc0

def z725 : W := mkw 0x000ead7fd4000000 0x0deff97ffe000000

def z726 : W := mkw 0x3e0557c001feaea0 0x321007c001fffff0

def z727 : W := mkw 0x9509ead6b54b0b0a 0xf110f8c61fcf0f0f

def z728 : W := mkw 0x380ddfc001fea000 0x31effe0001fff000

def z729 : W := mkw 0x380cdfc000bea000 0x23efffc0003ff000

def z730 : W := mkw 0x180667ffd40ea000 0x2e0007fffe0ff000

def z731 : W := mkw 0x260b982a01f00ea0 0x11fff80a01f00ff0

def z732 : W := mkw 0x000eefffd4000000 0x0d4ffefffe000000

def z733 : W := mkw 0x95070529614b0b0a 0xc05f0631818c0f0f

def z734 : W := mkw 0x688e9d6b4ca4c4c5 0xf09f094a67accccf

def z735 : W := mkw 0x004000002a01515c 0xffb009ce7fffffff

def z736 : W := mkw 0x2800528000a48000 0xfe70f631818c0c0f

def z737 : W := mkw 0x000ccfc000000000 0x0befffc07e000000

def z738 : W := mkw 0x180dcfc0014ea000 0x33efffc001cff000

def z739 : W := mkw 0x95070529614b0b0a 0xfeff0f3be1df0f3f

def z740 : W := mkw 0x0008880000000000 0x0feff9ce7e000000

def z741 : W := mkw 0x4e8bcaaa9954ca65 0xea8f0e8b985cc33f

def z742 : W := mkw 0x0042203e2a01515c 0x0c10003e7e0003fc

def z743 : W := mkw 0x6880729498a4c4c5 0xfff0f6bd99eccfcf

def z744 : W := mkw 0x260bb83e01f00ea0 0x11fff83001f00ff0

def z745 : W := mkw 0x260ab83e00a00ea0 0x15fff83e01a00ff0

def z746 : W := mkw 0x380ddfc001fea000 0x336ff7c001aff000

def z747 : W := mkw 0x260bb83e01f00ea0 0x15fff8fe01f0fff0

def z748 : W := mkw 0x95070529614b0b0a 0xc84f0631e18c0c0f

def z749 : W := mkw 0x060ba83e01400ea0 0x15fff83e01c00ff0

def z750 : W := mkw 0x384ddfc02bfff15c 0x0c5ff60e7f8c03fc

def z751 : W := mkw 0x380ddfc001fea000 0x238fffc0007ff000

def z752 : W := mkw 0x260bb83e01f00ea0 0x15fff8fe1ff00ff0

def z753 : W := mkw 0x200ab83e00a00480 0x15fff83e01f00ff0

def z754 : W := mkw 0x260bb83e01f00ea0 0x15fff97e67f00ff0

def z755 : W := mkw 0x3809980001fea000 0x304ff00001fff000

def z756 : W := mkw 0x95070529614b0b0a 0xfe7f0731e18f0c0f

def z757 : W := mkw 0xb30cbd1760bb05aa 0xeb00ff07e03f00ff

def z758 : W := mkw 0x46c2203eba015ffd 0xcc10003ffe000fff

def z759 : W := mkw 0x95070529614b0b0a 0xfc5f0639e1cf0f0f

def z760 : W := mkw 0x260bb83e01f00ea0 0xddfff83f81f00fff

def z761 : W := mkw 0x380ddfc001fea000 0x33efffc61ffff000

def z762 : W := mkw 0x95070529414a0a02 0xfeff063981cc0f0f

def z763 : W := mkw 0x10070529414a0000 0xfeff0739e1cf0c0f

def z764 : W := mkw 0x000eefffd4000000 0x0b4ffff7fe000000

def z765 : W := mkw 0x6880729498a4c4c5 0xff70f6b599fccfff

def z766 : W := mkw 0x95070529614b0b0a 0xfeff0739e1ff0fff

def z767 : W := mkw 0x2800528008a4c044 0xff70f6b599accccf

def z768 : W := mkw 0x6880729498a4c4c5 0xf150f6b599accccf

def z769 : W := mkw 0x970f8d2b615b0b2a 0x008f010860430300

def z770 : W := mkw 0x3a0ddfc201fea020 0x33efffc201fff030

def z771 : W := mkw 0x260b982a01f00a20 0x15fff80e01f003f0

def z772 : W := mkw 0x000eefffd4000000 0xcfefffffff8c0c03

def z773 : W := mkw 0x508dad54995a64c5 0xcc9f097598533ccf

def z774 : W := mkw 0x6880729498a4c4c5 0xfe70f6b1998ccc0f

def z775 : W := mkw 0x000aeabe90000000 0x0feffffffe000000

def z776 : W := mkw 0x380ddfc001fea000 0x33aff9c00073f000

def z777 : W := mkw 0x954705294b4a5a56 0xc14f0ef79fbcfcf3

def z778 : W := mkw 0x184447c02a0ff15c 0x220007c0000ff00c

def z779 : W := mkw 0x95070529614b0b0a 0xffff07b9e1efcf0f

def z780 : W := mkw 0x004eeffffe01515c 0x305ff6318073f3fc

def z781 : W := mkw 0x6880729498a4c4c5 0xeb40f6b599accccf

def z782 : W := mkw 0x000667bdd0000000 0x0feffffffe000000

def z783 : W := mkw 0x95070569614b2b0a 0xfeff0779e1cf3f0f

def z784 : W := mkw 0x95070529614b0b0a 0xffff0f39e1ff0f0f

def z785 : W := mkw 0x004000002a01515c 0xffb00fcffe7ff3ff

def z786 : W := mkw 0x3e0ddfc001feaa20 0x33efffc001fff330

def z787 : W := mkw 0x8742203f6a015ffe 0xcc10003ffe000fff

def z788 : W := mkw 0x260bb83e01f00ea0 0x37fff8be01f0cff0

def z789 : W := mkw 0x260bb83e91f00ea0 0x1dfff83f99f00ff0

def z790 : W := mkw 0x2809da8001f48000 0x33efffc001fff000

def z791 : W := mkw 0x220ab83e00b004a0 0x15fff83e007003f0

def z792 : W := mkw 0x260bb83e01f00ea0 0x1ffffe3f81f00ff0

def z793 : W := mkw 0x6880528008a4c4c5 0xff70f6b181accccf

def z794 : W := mkw 0x668bb83e91f00ea1 0xd5fff83f81f00ff3

def z795 : W := mkw 0x95070529614b0b0a 0xf0df0739e1cf0f0f

def z796 : W := mkw 0x6888fad498a4c4c5 0x0100f8c41820c0c0

def z797 : W := mkw 0x000ccfc000000000 0x23efffc00003f000

def z798 : W := mkw 0x95070529614b0b0a 0xfeff0739e1ffff0f

def z799 : W := mkw 0x380ddfc141fea000 0x3befffc1e1fff000

def z800 : W := mkw 0x6880729498a4c4c5 0xfe70f635998c0ccf

def z801 : W := mkw 0xd9c44781fa0fd15f 0xea0007c1fe0ff00f

def z802 : W := mkw 0x688072d498a4e4c5 0xff70f6f599acfccf

def z803 : W := mkw 0x004000002a01515c 0x33a009ce7e73f3f0

def z804 : W := mkw 0x0008880000000000 0x15fff80e007003f0

def z805 : W := mkw 0x000ccfc1d4000000 0x0fefffcffe000000

def z806 : W := mkw 0x380ddfc001fea000 0x23efffc0018ff000

def z807 : W := mkw 0x6a80729698a4c4e5 0xff70f6b799acccff

def z808 : W := mkw 0x260bb83f41f00ea0 0x1dfff83fe1f00ff0

def z809 : W := mkw 0x260bb83e01f00ea0 0x35fff83e01f3fff0

def z810 : W := mkw 0x6880729498a4c4c5 0xc840f631998c0c0f

def z811 : W := mkw 0x380ddfc001fea000 0x33efffca01fff330

def z812 : W := mkw 0x260bb83e01f00ea0 0x14fff03e01c00ff0

def z813 : W := mkw 0x95070529614b0b0a 0xffff0fffe1ffffff

def z814 : W := mkw 0x6880729498a4c4c5 0xfff0febf99accccf

def z815 : W := mkw 0x10050500214b0108 0xfeff0739e1cf0f0f

def z816 : W := mkw 0xa70bb83f41f00ea2 0xd5fff83f81f00ff3

def z817 : W := mkw 0x000eefffd4000000 0x0b8fffcffe000000

def z818 : W := mkw 0x260bb83e01f00ea0 0x10dff83a01f00ff0

def z819 : W := mkw 0x260bb83fd5f00ea0 0x15fff83f81f00ff0

def z820 : W := mkw 0x0407052941400a00 0xfeff0739e1cc0f0f

def z821 : W := mkw 0x3809da8001fea000 0x33effe8001fff000

def z822 : W := mkw 0x300d9d0001fa0000 0x33efffc001fff000

def z823 : W := mkw 0x180eefffd40ea000 0x3feffffffe7ff000

def z824 : W := mkw 0x58c447c0ba0ff15d 0xea0007c1fe0ff00f

def z825 : W := mkw 0x0006052940000000 0xfe7f0631818c0c0f

def z826 : W := mkw 0x3c0ddfc001feaa00 0x33ffffc001ffff00

def z827 : W := mkw 0x000eefffd4000000 0x3feffffffe430000

def z828 : W := mkw 0x260bb83e01f00ea0 0x05eff83e007003f0

def z829 : W := mkw 0x2009b81401f00480 0x15fff83e01f00ff0

def z830 : W := mkw 0x260bb83e01f00ea0 0x15bff80e007003f0

def z831 : W := mkw 0xfd8777bdf9efcfcf 0x018ff18c7863c3c0

def z832 : W := mkw 0x260bb83e01f00ea0 0x1dfff83e7ff00ff0

def z833 : W := mkw 0x260bb83e01f00ea0 0xd5fffe3f81fc0ff3

def z834 : W := mkw 0x380ddfc001fea000 0x37fffff001fffc00

def z835 : W := mkw 0x95070529614b0b0a 0xfeff0f7be7cf0f0f

def z836 : W := mkw 0x95470529634b1b1a 0xffff0fffffdf3f3f

def z837 : W := mkw 0x000eefffd4000000 0x0beffff1fe000000

def z838 : W := mkw 0x264bb83e2bf15ffc 0x2a4ff1f07f83fc0c

def z839 : W := mkw 0x6880729498a4c4c5 0xfff0fffffffccfff

def z840 : W := mkw 0x000aa83fd4000000 0x0feff9fffe000000

def z841 : W := mkw 0x6880729498a4c4c5 0xff70feb799bcccff

def z842 : W := mkw 0x004000002a01515c 0x15b009ce7e73f3f0

def z843 : W := mkw 0x97070529615b0b2a 0xfeff0739e1df0f3f

def z844 : W := mkw 0x6880729498a4c4c5 0xc050f631818c0ccf

def z845 : W := mkw 0x6a88fad698b4e4e5 0x0100f8c61830f0f0

def z846 : W := mkw 0x40c2203ffe0155dd 0xcc10003ffe000fff

def z847 : W := mkw 0x000eefffd4000000 0x0faff9ce7e000000

def z848 : W := mkw 0x68c8fad49ab4f4d5 0x0100f8c61e30f0f0

def z849 : W := mkw 0x6880729498a4c4c5 0xfe70f63181accccf

def z850 : W := mkw 0x260557c1d5f00ea0 0x1a1007c1fff00ff0

def z851 : W := mkw 0x000eefffd4000000 0x03efffce7e000000

def z852 : W := mkw 0x260bb83e01f00ea0 0x3ffff9fe7ff3fff0

def z853 : W := mkw 0x68c07294b2a59599 0xc0c0ff7be7df3f33

def z854 : W := mkw 0x91060529600b010a 0xfeff0739e18f0c0f

def z855 : W := mkw 0x260b982801f00ea0 0x15fff83801f00ff0

def z856 : W := mkw 0x380ddfc001fea000 0x37efffce01fff000

def z857 : W := mkw 0x000eeffe00000000 0x0feffffe7e000000

def z858 : W := mkw 0x68c072949aa4d4d5 0xff70f6f59facfccf

def z859 : W := mkw 0x260bb83fd5f00ea0 0x1ffff9fffff00ff0

def z860 : W := mkw 0x004ccfc02a01515c 0x33ffffc00073f3fc

def z861 : W := mkw 0x95070529615b2b0a 0xfeff0739e1df3f0f

def z862 : W := mkw 0x020eefffd40004a0 0x0feffffffe0000f0

def z863 : W := mkw 0x100eefffd40a0000 0x2feffffffe0f0000

def z864 : W := mkw 0x6a80729498b4c4e5 0xff70f6b599bcccff

def z865 : W := mkw 0x6880729498a4c4c5 0xee50f6b5998ccccf

def z866 : W := mkw 0x95070529614b0b0a 0xfeff07f9e1cfff0f

def z867 : W := mkw 0x380ddfc1d5fea000 0x3fefffcffffff000

def z868 : W := mkw 0x788ddfc001fea481 0xf3efffc001fffc03

def z869 : W := mkw 0x6880729490a48481 0xff70f6b5998c0c0f

def z870 : W := mkw 0x240b982801f00a00 0x15fff83e01f00ff0

def z871 : W := mkw 0x2209b81601f004a0 0x15fff80e01f003f0

def z872 : W := mkw 0x6880729498a4c4c5 0xff70fef79faccccf

def z873 : W := mkw 0x950f8d69614b0b0a 0x008f094860430300

def z874 : W := mkw 0x060eefffd4000a20 0x0feffffffe000330

def z875 : W := mkw 0x384110002bfff15c 0x3000000001fff00c

def z876 : W := mkw 0x3e0bb83e01feaea0 0x37fff9fe01fffff0

def z877 : W := mkw 0x380ddfc001fea000 0x22cfffc001dff000

def z878 : W := mkw 0x6888fa9498b4c4c5 0x0100f8841830c0c0

def z879 : W := mkw 0x95030028214b0b0a 0xfeff063981cf0f0f

def z880 : W := mkw 0x004000002a01515c 0x0fa009ce7e73f3f0

def z881 : W := mkw 0x000aa83e00000000 0x0deff83e7e000000

def z882 : W := mkw 0x260bb83e01f00ea0 0x04dff83e01d00ff0

def z883 : W := mkw 0x000aeaffd4000000 0x0deff8fffe000000

def z884 : W := mkw 0x6a88fad69cb4c4e5 0x0100f8c61e30c0f0

def z885 : W := mkw 0x6ac8fa969ab4d4f5 0x0100f8c61e30f0f0

def z886 : W := mkw 0x000eefffd4000000 0xefeffffffe0c000f

def z887 : W := mkw 0x380ddfc001fea480 0x33ffffc001fffcc0

def z888 : W := mkw 0x000ead3fd4000000 0x0fefff3ffe000000

def z889 : W := mkw 0x95070529614b0b0a 0xfa5f0731e1cf0f0f

def z890 : W := mkw 0x68c072949aa4d4d5 0xfff0ffffffbcfcff

def z891 : W := mkw 0xc5c2203dfa015fdf 0xcc10003ffe000fff

def z892 : W := mkw 0x004000002a01515c 0x2b8009ce7e73f3fc

def z893 : W := mkw 0x380557c001eea000 0x33eff7c001eff000

def z894 : W := mkw 0x488eefffd4048001 0xcfeffffffe0c0003

def z895 : W := mkw 0x020eefffd4100020 0x0feffffffe100030

def z896 : W := mkw 0x380ddfc091fea000 0x3befffc199fff000

def z897 : W := mkw 0x6888fad69cb4e4c5 0x0100f8c61e30f0c0

def z898 : W := mkw 0x380ddfc001fea000 0x01cfffc001fff000

def z899 : W := mkw 0x260bb83e01f00ea0 0x11eff80e01f003f0

def z900 : W := mkw 0x380ddfc001fea000 0x3befffc07ffff000

def z901 : W := mkw 0x040ba83e01400a00 0x15fff83e01f00ff0

def z902 : W := mkw 0x2609b81601f00ea0 0x11fff80601f00ff0

def z903 : W := mkw 0x2e0bb83e01f4aea0 0x15fff83e01f0fff0

def z904 : W := mkw 0x2403303c01e00e80 0x15fff83e01f00ff0

def z905 : W := mkw 0x95070529614b0b0a 0xfeff073fe1cf0fff

def z906 : W := mkw 0x060eefffd4000ea0 0x0feffffffe000c00

def z907 : W := mkw 0x000eefffd4000000 0x3feffffffe20c000

def z908 : W := mkw 0x6880729490a48481 0xff70f6b181accc0f

def z909 : W := mkw 0x954f8d69635b3b1a 0x008f094a66533330

def z910 : W := mkw 0x004000002a01515c 0x3ff009fe7ff3fffc

def z911 : W := mkw 0x360bb83e01fa0ea0 0x35fff83e01ff0ff0

def z912 : W := mkw 0x2000301400a00480 0xfe70f631818c0c0f

def z913 : W := mkw 0x000eefffd4000000 0x1fffffffff800c00

def z914 : W := mkw 0x260bb83e01f00ea0 0x115ff83601f00ff0

def z915 : W := mkw 0x0000201400000000 0xff70f635818c0c0f

def z916 : W := mkw 0x000eefffd4000000 0x0e4ff7fffe000000

def z917 : W := mkw 0x788ddfc091fea001 0xf3efffc181fff003

def z918 : W := mkw 0x2000301408a044c4 0xff70f6b599accccf

def z919 : W := mkw 0x994447c16a0ff15e 0xea0007c1fe0ff00f

def z920 : W := mkw 0x6080301498a044c5 0xff70f63599ac0ccf

def z921 : W := mkw 0xb70bb83e01fa0ea2 0xd5fff83e01fc0ff3

def z922 : W := mkw 0x95070529414a0a02 0xea4f0631818c0c0f

def z923 : W := mkw 0x004000002a01515c 0x0d9009ce7e73f3fc

def z924 : W := mkw 0x6880729490a48481 0xff70f63581ac0ccf

def z925 : W := mkw 0x260bb83e01f00ea0 0x055ff83e01b00ff0

def z926 : W := mkw 0x380ddfc001fea000 0x3fffffc001fff00c

def z927 : W := mkw 0x0001000001400000 0xfeff063181cc0c0f

def z928 : W := mkw 0x6880729498a4c4c5 0xfa50f6b199accccf

def z929 : W := mkw 0x380ddfc001fea000 0x11eff9c001f3f000

def z930 : W := mkw 0x000eefffd4000000 0x0deffe3ffe000000

def z931 : W := mkw 0x2809dac001f4a000 0x33eff9c001f3f000

def z932 : W := mkw 0x380ddfc001fea000 0x32eff7c001cff000

def z933 : W := mkw 0x000eefffd4000000 0x084ff631fe000000

def z934 : W := mkw 0x95070529614b0b0a 0xdcff0639e1cc0f0f

def z935 : W := mkw 0x000aa83fd4000000 0x0c4ff03ffe000000

def z936 : W := mkw 0x950f8d29615b0b0a 0x008f090860530300

def z937 : W := mkw 0x6880729498a4c4c5 0xfff0f7bdf9accccf

def z938 : W := mkw 0x8542203ffe015b5e 0xcc10003ffe000fff

def z939 : W := mkw 0x060667ffd4000ea0 0x0e1007fffe000ff0

def z940 : W := mkw 0x380ddfc001fea000 0xf3ffffc001fffc0f

def z941 : W := mkw 0x380ddfc001fea000 0x33efffc601fff0f0

def z942 : W := mkw 0x060ba83e01500a20 0x15fff83e007003f0

def z943 : W := mkw 0x004aa83e2a01515c 0x2feff9fe7e03f00c

def z944 : W := mkw 0x000cefd7d4000000 0x0befffc7fe000000

def z945 : W := mkw 0x380ddfc001fea000 0x336ff68001fff000

def z946 : W := mkw 0x3801100001fea000 0x3fa009ce7ffff000

def z947 : W := mkw 0x68c072949aa4d4d5 0xff70f6b599bcfcff

def z948 : W := mkw 0x970f8d6b655b0b2a 0x008f094a66530330

def z949 : W := mkw 0x95070529614b0b0a 0xffff073de1ef0fcf

def z950 : W := mkw 0x974f8d2b635b1b3a 0x008f094a66533330

def z951 : W := mkw 0x488062949804c045 0xff70f6b5998ccc0f

def z952 : W := mkw 0x910eefffd40a0002 0xcfeffffffe0c0003

def z953 : W := mkw 0x260bb83e01f00ea0 0x14fff03801f00ff0

def z954 : W := mkw 0x204110002bf1515c 0x3010000001f3f3fc

def z955 : W := mkw 0x380ddfc001fea000 0x37ffffc801fff300

def z956 : W := mkw 0x000ead3f40000000 0x0feffffffe000000

def z957 : W := mkw 0x260bb83e01f00ea0 0x17fff9fe01f00ff0

def z958 : W := mkw 0x6888fad69ca4c4c5 0x0100f0841820c0c0

def z959 : W := mkw 0x004000002a01515c 0x3ff00ffffe73f3fc

def z960 : W := mkw 0x3809dac001fea000 0x31eff8c001fff000

def z961 : W := mkw 0x260bb83e95f00ea0 0x15fff83e1ff00ff0

def z962 : W := mkw 0x95470529634b1b1a 0xffff0ffbe7ffff3f

def z963 : W := mkw 0x6880729498a4c4c5 0xcf70f6b5998c0ccf

def z964 : W := mkw 0x180dcfc0015ea000 0x23efffc0005ff000

def z965 : W := mkw 0x300d9d4001fa2000 0x33eff9c001f3f000

def z966 : W := mkw 0x95070529614b0b0a 0xfe7f063181cf0f0f

def z967 : W := mkw 0x380ddfc001fea000 0x204ff600018ff000

def z968 : W := mkw 0x180ccfc0000ea000 0x224ff7c0000ff000

def z969 : W := mkw 0x260ab83e00b00ea0 0x05fff83e00300ff0

def z970 : W := mkw 0x380ddfc1d5fea000 0x33efffc181fff000

def z971 : W := mkw 0x380d9d0001fea000 0x33efff0001fff000

def z972 : W := mkw 0x950f8d6b655b2b0a 0x008f094a66533300

def z973 : W := mkw 0x060ba83e01500ea0 0x05fff83e00500ff0

def z974 : W := mkw 0x95070529614b0b0a 0xffff0ff9e1cf0f0f

def z975 : W := mkw 0x380ddfc001fea000 0x314ffec001fff000

def z976 : W := mkw 0x380ddfc145fea000 0x33efffc067fff000

def z977 : W := mkw 0x060aa83e00000ea0 0x045ff03e00000ff0

def z978 : W := mkw 0x004000002a01515c 0x319009ce7e73f3fc

def z979 : W := mkw 0x260bb83f45f00ea0 0x15fff83e67f00ff0

def z980 : W := mkw 0x260bb83e01f00ea0 0x15fff97e01f33ff0

def z981 : W := mkw 0x95070529614b0b0a 0xfe7f0639e18c0f0f

def z982 : W := mkw 0x48c447c1fe05d15d 0xea0007c1fe0ff00f

def z983 : W := mkw 0x95070529614b0b0a 0xffff0fffffff0fff

def z984 : W := mkw 0x688072d49ca4c4c5 0xff70f6f59faccccf

def z985 : W := mkw 0x95070529614b0b0a 0xccdf0739e1cf0f0f

def z986 : W := mkw 0x3e0ddfc001feaea0 0x33efffc001fffc00

def z987 : W := mkw 0x6880729498a4c4c5 0xe040f631818ccc0f

def z988 : W := mkw 0x000eefffd4000000 0x0eeff7f9fe000000

def z989 : W := mkw 0x000667bfd4000000 0x0feff7bffe000000

def z990 : W := mkw 0x6880729498a4c4c5 0xfff0feb599fccccf

def z991 : W := mkw 0x180447c0000ea000 0x37b00fce007ff3f0

def z992 : W := mkw 0xb74110002bfb5ffe 0xf010000001ffffff

def z993 : W := mkw 0x14070528014a0a00 0xfeff073981cf0f0f

def z994 : W := mkw 0x380d9d4001fea000 0x31eff94001fff000

def z995 : W := mkw 0x95070529614b0b0a 0xfeff0f79e1df3f0f

def z996 : W := mkw 0x000eefffd4000000 0x01cffffffe000000

def z997 : W := mkw 0x91050501614b010a 0xfeff0731e1cf0c0f

def z998 : W := mkw 0x9507052b654b0b0a 0xfeff073be7cf0f0f

def z999 : W := mkw 0x0004050000000000 0xfeff0731818c0c0f

def z1000 : W := mkw 0x0403002821410b08 0xfeff0739e1cf0f0f

def z1001 : W := mkw 0x10050500014a0000 0xfe7f0631818c0c0f

def z1002 : W := mkw 0x380ddfc001fea000 0x3fefffc861fff000

def z1003 : W := mkw 0x000ecfeb44000000 0x0fefffce7e000000

def z1004 : W := mkw 0x6880729498a4c4c5 0xff70f7f5ffaccccf

def z1005 : W := mkw 0x688072969ca4c4c5 0xff70f6b79faccccf

def z1006 : W := mkw 0x6880729498b4e4c5 0xff70f6b599bcfccf

def z1007 : W := mkw 0x68c072949aa4d4d5 0xfff0fff79ffffcff

def z1008 : W := mkw 0x100dcfc0015a2000 0x33efffc00073f000

def z1009 : W := mkw 0x6880729498a4c4c5 0xfff0ffff99ffffff

def z1010 : W := mkw 0x004000002a01515c 0x3ff00fce7ffff3fc

def z1011 : W := mkw 0x95070529614b0b0a 0xf4ff063981cf0f0f

def z1012 : W := mkw 0x260bb83e01f00ea0 0x145ff03e01f00ff0

def z1013 : W := mkw 0x6880729498a4c4c5 0xfff0fffffffffccf

def z1014 : W := mkw 0x100eefffd40a2000 0x0feffffffe033000

def z1015 : W := mkw 0x6880729498a4c4c5 0xfc50f63599accccf

def z1016 : W := mkw 0x95070529614b0b0a 0xffff0fffffffff0f

def z1017 : W := mkw 0x95070529614b0b0a 0xfaef0731e1cf0c0f

def z1018 : W := mkw 0x000ecfe940000000 0x0feffffffe000000

def z1019 : W := mkw 0x000cefd5d4000000 0x0feffff5fe000000

def z1020 : W := mkw 0x2009980001f00000 0x31eff80001f3f000

def z1021 : W := mkw 0x380cdfc000aea000 0x33efffc001aff000

def z1022 : W := mkw 0x6880729490a48481 0xcc50f631818c0c0f

def z1023 : W := mkw 0x95070529614b0b0a 0xee5f0739e18f0f0f

def z1024 : W := mkw 0x260bb83e01f00ea0 0x37fff93e01f30ff0

def z1025 : W := mkw 0x260bb83e01f00ea0 0x3ffff83e01f00ffc

def z1026 : W := mkw 0x000eefffd4000000 0x05eff9fe7e000000

def z1027 : W := mkw 0x204998002bf1515c 0x1dfff80e7ff003fc

def z1028 : W := mkw 0x95070529414a0a02 0xfeff073181cf0c0f

def z1029 : W := mkw 0x850eefffd4000a02 0xcfeffffffe000c03

def z1030 : W := mkw 0x000eefffd4000000 0x3ffffffffe00000c

def z1031 : W := mkw 0x2000729490a00480 0xff70f6b599ac0ccf

def z1032 : W := mkw 0x950f8d6b654b0b0a 0x008f010860430300

def z1033 : W := mkw 0x95070529614b0b0a 0xfeff07f9ffcf0f0f

def z1034 : W := mkw 0x000eefffd4000000 0x0ffffffffe0003f0

def z1035 : W := mkw 0x95070529414a0a02 0xfeff0739e18c0c0f

def z1036 : W := mkw 0x970f8d6b615b2b2a 0x008f094a60533330

def z1037 : W := mkw 0x380ddfc001fea000 0x234fffc001bff000

def z1038 : W := mkw 0x000ead7f44000000 0x0feff9fe7e000000

def z1039 : W := mkw 0x000eefffd4000000 0x0feffffffe30f000

def z1040 : W := mkw 0x380ddfc001fea000 0x33efffca67fff000

def z1041 : W := mkw 0x2603303c01f00ea0 0x15fff03c01f00ff0

def z1042 : W := mkw 0x0000000000000000 0x3fb009ce7e73f3f0

def z1043 : W := mkw 0x2000100000a00000 0xff70f63181ac0c0f

def z1044 : W := mkw 0x6880528098a4c045 0xff70f6b199accc0f

def z1045 : W := mkw 0x0008880000000000 0x33eff9c00073f000

def z1046 : W := mkw 0x0403002801400a00 0xfe7f0631818c0c0f

def z1047 : W := mkw 0x95070529614b0b0a 0xffff0f3fe1cf0f0f

def z1048 : W := mkw 0x380ddfc001fea000 0x3feffff181fff000

def z1049 : W := mkw 0x95070529414a0a02 0xf05f0631818c0c0f

def z1050 : W := mkw 0x000eefffd4000000 0x1ffffffffe400300

def z1051 : W := mkw 0x6880729498a4c4c5 0xfff0f7b599efcccf

def z1052 : W := mkw 0x9707052b614b0b2a 0xfeff073be1cf0f3f

def z1053 : W := mkw 0x000447c1d4000000 0x1fb00fcffe7003f0

def z1054 : W := mkw 0x40806294980044c5 0xff70f6b5998c0ccf

def z1055 : W := mkw 0x260bb83e01f00ea0 0x157ff03401f00ff0

def z1056 : W := mkw 0x380ddfc001fea000 0x3fffffce7ffff3f0

def z1057 : W := mkw 0x95470529634b1b1a 0xfeff073be7cf0f3f

def z1058 : W := mkw 0x3805578001ee8000 0x33efffc001fff000

def z1059 : W := mkw 0x8503002961410b0a 0xfeff0639e1cc0f0f

def z1060 : W := mkw 0x380ddfc001fea000 0x32eff70001fff000

def z1061 : W := mkw 0x6880729498a4c4c5 0xff70f6b599fffccf

def z1062 : W := mkw 0x380ddfc001fea000 0xf3effff181fffc03

def z1063 : W := mkw 0x200bb83e01f00000 0x15fff83e01f003f0

def z1064 : W := mkw 0x360bb83e01fa2ea0 0x15fff83e01f33ff0

def z1065 : W := mkw 0x3e0fffffd5feaea0 0x004ff631818c0c00

def z1066 : W := mkw 0x000eefffd4000000 0x0feffffffe500330

def z1067 : W := mkw 0x000eefffd4000000 0x0feffffffe533000

def z1068 : W := mkw 0x004aa83e2a01515c 0x35fff83e0073f3fc

def z1069 : W := mkw 0x380ddfc095fea000 0x33efffc01ffff000

def z1070 : W := mkw 0xbd4110002bfffb5e 0xf010000001ffffff

def z1071 : W := mkw 0x2009980001f00000 0x11fff80001f003f0

def z1072 : W := mkw 0x000667fdd4000000 0x0feff7fdfe000000

def z1073 : W := mkw 0x0002203fd4000000 0x3fa009fffe73f000

def z1074 : W := mkw 0x000eefffd4000000 0x0acffffbfe000000

def z1075 : W := mkw 0x0042203ffe01515c 0x0c00003ffe00000c

def z1076 : W := mkw 0x6880729498a4c4c5 0xfff0fff599accccf

def z1077 : W := mkw 0x6888fa9698a4c4c5 0x0100f8861820c0c0

def z1078 : W := mkw 0x260bb87e05f00ea0 0x15fff87e07f00ff0

def z1079 : W := mkw 0x380ddfc001fea000 0x30cfff4001fff000

def z1080 : W := mkw 0x000eefffd4102000 0x0feffffffe103000

def z1081 : W := mkw 0x380ddfc001fea000 0x37ffffc401fff0c0

def z1082 : W := mkw 0x260bb83e01f00ea0 0x05fff83e01800ff0

def z1083 : W := mkw 0x6ec110002bf5dffd 0xf010000001ffffff

def z1084 : W := mkw 0x0602203e00000ea0 0x37b009fe0073fff0

def z1085 : W := mkw 0x0642203ffe015ffc 0x0c10003ffe000ffc

def z1086 : W := mkw 0x95470529634b1b1a 0xfeff0739e1df3f3f

def z1087 : W := mkw 0x3e03303e01feaea0 0x3410003e01fffff0

def z1088 : W := mkw 0x260bb83e01f00ea0 0x005ff03001800ff0

def z1089 : W := mkw 0x408eefffd4000481 0xcfeffffffe000c03

def z1090 : W := mkw 0x000ecfebd4000000 0x0befffcbfe000000

def z1091 : W := mkw 0x180ccfc0000ea000 0x33efffc0007ff000

def z1092 : W := mkw 0x0000428000000000 0xff70f6b1818c0c0f

def z1093 : W := mkw 0x6880729498a4c4c5 0xff70fef599bcfccf

def z1094 : W := mkw 0x040eefffd4000a00 0x0ffffffffe000f00

def z1095 : W := mkw 0x264110002bf15ffc 0x1010000001f00ffc

def z1096 : W := mkw 0x6880729490a48481 0xea40f631818c0c0f

def z1097 : W := mkw 0x180eefffd40ea000 0x0feffffffe0c0000

def z1098 : W := mkw 0x060aa83e00000ea0 0x15fff83e00700ff0

def z1099 : W := mkw 0x2603303e01e00ea0 0x15fff03e01e00ff0

def z1100 : W := mkw 0x95070529614b0b0a 0xfeff073fffcf0f0f

def z1101 : W := mkw 0x0002002800000000 0xfeff0639818c0c0f

def z1102 : W := mkw 0x2e0bb83e01f48ea0 0x35fff83e01fccff0

def z1103 : W := mkw 0x204998002bf1515c 0x3beff9c07ff3f00c

def z1104 : W := mkw 0x0006052960010108 0xfeff0739e1cf0f0f

def z1105 : W := mkw 0x6880729498a4c4c5 0xef60f6b5998ccc0f

def z1106 : W := mkw 0xb90ddfc141fea002 0xf3efffc181fff003

def z1107 : W := mkw 0x000eefffd4000000 0x0d8ff9fffe000000

def z1108 : W := mkw 0x95070529414a0a02 0xcc5f0631818c0c0f

def z1109 : W := mkw 0x060eefffd4000ea0 0x1ffffffffe700ff0

def z1110 : W := mkw 0x6880729498a4c4c5 0xdd70f63599ac0ccf

def z1111 : W := mkw 0x000eefffd4000000 0x0eeff73ffe000000

def z1112 : W := mkw 0x2601100001f00ea0 0x1fb009ce7ff00ff0

def z1113 : W := mkw 0x000eefffd4000000 0x3fefffffff8c0000

def z1114 : W := mkw 0x380557c1d5fea000 0x3a0007c1fffff000

def z1115 : W := mkw 0x000eefffd4000000 0x1ffffffffe2000c0

def z1116 : W := mkw 0x0000629498004044 0xff70f6b599accccf

def z1117 : W := mkw 0x000cefd694000000 0x0fefffce7e000000

def z1118 : W := mkw 0x8506052960010b0a 0xfeff0739e18c0f0f

def z1119 : W := mkw 0x0000629490000000 0xfe70f631818c0c0f

def z1120 : W := mkw 0x95070529614b0b0a 0xffff07bdf9cf0f0f

def z1121 : W := mkw 0x2800729490a48000 0xff70f6b599accc0f

def z1122 : W := mkw 0x380ddfc001fea000 0x318ff9c001fff000

def z1123 : W := mkw 0x95070529614b0b0a 0xf2ff073181cf0f0f

def z1124 : W := mkw 0x260bb83e01f00ea0 0x119ff80e01f00ff0

def z1125 : W := mkw 0x260bb83e01f00ea0 0x01cff83e01f00ff0

def z1126 : W := mkw 0x95470529634b1b1a 0xffff0f7fe7ff3fff

def z1127 : W := mkw 0x280cdfc000b4a000 0x33efffc00073f000

def z1128 : W := mkw 0x260bb87e01f02ea0 0x15fff87e01f03ff0

def z1129 : W := mkw 0x6e8bb83e01f48ea1 0xd5fff83e01fc0ff3

def z1130 : W := mkw 0x2609980001f00ea0 0x15fff80e01f00ff0

def z1131 : W := mkw 0x68c8fad69ea4d4d5 0x0100f8c61e30f0f0

def z1132 : W := mkw 0x3e0ddfc001feaea0 0x37ffffce01fffff0

def z1133 : W := mkw 0x2609980001f00ea0 0x105ff00001f00ff0

def z1134 : W := mkw 0x080eefffd4048000 0x2feffffffe0cc000

def z1135 : W := mkw 0x000cefd490000000 0x0feffffffe000000

def z1136 : W := mkw 0xbd0ddfc001feaa02 0xf3efffc001fffc03

def z1137 : W := mkw 0x95070529614b0b0a 0xeeef0739e18f0c0f

def z1138 : W := mkw 0x000eefffd4000000 0x0feffffffe3000f0

def z1139 : W := mkw 0x2609b81401f00ea0 0x15fff83401f00ff0

def z1140 : W := mkw 0x000eefffd4000000 0x0f6ff7f5fe000000

def z1141 : W := mkw 0x6888fad498b4e4c5 0x0100f0841820c0c0

def z1142 : W := mkw 0x000eefffd4000000 0x3ffffffffe73f3f0

def z1143 : W := mkw 0x914447c1fe0b515e 0xea0007c1fe0ff00f

def z1144 : W := mkw 0x95070529614b0b0a 0xeacf0739e1cf0f0f

def z1145 : W := mkw 0x3e4110002bfffffc 0x3010000001fffffc

def z1146 : W := mkw 0x950f8d2b614b0b0a 0x008f090a60430300

def z1147 : W := mkw 0x000aeabfd4000000 0x0feffebffe000000

def z1148 : W := mkw 0x260bb83e01f00ea0 0x1ffff8be19f00ff0

def z1149 : W := mkw 0x184447c1fe0ff15c 0x2a0007c1fe0ff00c

def z1150 : W := mkw 0x380ddfc001fea000 0x03efffc00073f000

def z1151 : W := mkw 0x260bb83e01f00ea0 0x1ffff93e61f00ff0

def z1152 : W := mkw 0x000ccfc1d4000000 0x0a4ff7c1fe000000

def z1153 : W := mkw 0x080eefffd404a000 0x0feffffffe00f000

def z1154 : W := mkw 0x95070529614b0b0a 0xe04f0631818f0c0f

def z1155 : W := mkw 0x000eefffd4000000 0xcffffffffe000c0f

def z1156 : W := mkw 0x000eefffd4000000 0x1feffffffe700000

def z1157 : W := mkw 0x6880729498a4c4c5 0xff70f7f599affccf

def z1158 : W := mkw 0x000eefffd4000000 0x0ccfff7ffe000000

def z1159 : W := mkw 0x6880729498a4c4c5 0xf570f63581accccf

def z1160 : W := mkw 0x000ecfe9d4000000 0x0feffff9fe000000

def z1161 : W := mkw 0x380ddfc001fea000 0xfbefffc181fff00f

def z1162 : W := mkw 0x380ddfc001fea000 0x33ffffc001fff3f0

def z1163 : W := mkw 0x000eefffd4000000 0x0f6ff6bffe000000

def z1164 : W := mkw 0x380ddfc001fea000 0x324ff7c001fff000

def z1165 : W := mkw 0x68c072949aa4d4d5 0xfff0feff9ffcffff

def z1166 : W := mkw 0x6880301408a4c4c5 0xff70f63581accccf

def z1167 : W := mkw 0x000eefffd4000000 0x2feffffffe03f000

def z1168 : W := mkw 0x3e0bb83e01feaea0 0x15fff83e01fc0ff0

def z1169 : W := mkw 0x100dcfc0014a0000 0x33efffc001fff000

def z1170 : W := mkw 0x6880729498a4c4c5 0xcd50f6b599accccf

def z1171 : W := mkw 0x260bb83e01f00ea0 0xf5fff83e01fc0fff

def z1172 : W := mkw 0x260bb83e01f00ea0 0x059ff83e00700ff0

def z1173 : W := mkw 0x95070569654b0b0a 0xfeff0779e7cf0f0f

def z1174 : W := mkw 0x004ccfc02a01515c 0x0fffffce7e0003fc

def z1175 : W := mkw 0x95470529634b1b1a 0xfeff0779e7cf3f0f

def z1176 : W := mkw 0x6a88fa9698b4c4e5 0x0100f0841820c0c0

def z1177 : W := mkw 0x004000002a01515c 0xffb009fffe73ffff

def z1178 : W := mkw 0x6880729498a4c4c5 0xfb60f6b199accc0f

def z1179 : W := mkw 0x000aa83e00000000 0x05fff83e000003f0

def z1180 : W := mkw 0x280cdfc000a48000 0x33efffc001fff000

def z1181 : W := mkw 0x3809980001fea000 0x33eff9c001fff000

def z1182 : W := mkw 0x004447c02a01515c 0x2a0007c07e03f00c

def z1183 : W := mkw 0x68c072949aa4d4d5 0xff70f6b79facccff

def z1184 : W := mkw 0x6880729498a4c4c5 0xff70f6bf99accfff

def z1185 : W := mkw 0x0642203e2a015ffc 0x0410003e00000ffc

def z1186 : W := mkw 0x6880729498a4c4c5 0xff70f6bfffaccccf

def z1187 : W := mkw 0x380ddfc001fea000 0x3fefffc419fff000

def z1188 : W := mkw 0x200ddfc001f00000 0x33efffc001f3f000

def z1189 : W := mkw 0x95070529614b0b0a 0xceff0739e18c0f0f

def z1190 : W := mkw 0x95050500214b0b0a 0xfeff073181cf0f0f

def z1191 : W := mkw 0x3805578001fea000 0x33eff78001fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z5]),(0,[z9,z0,z1,z2,z3,z4,z5]),(1,[z10,z0,z1,z2,z3,z11])],[(0,[z0,z1,z2,z3,z4,z5,z12]),(0,[z0,z1,z2,z3,z13,z4,z5]),(0,[z0,z1,z2,z3,z4,z14,z5]),(0,[z15,z0,z1,z2,z3,z4,z5])],[(0,[z16,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z17,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z18]),(0,[z0,z1,z19,z2,z20,z4,z5]),(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z22,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z23,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z24,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z25,z2,z3,z4,z5]),(1,[z26,z1,z2,z3,z4,z5]),(0,[z27,z0,z1,z28,z3,z4,z5]),(0,[z0,z1,z2,z3,z29,z4,z5]),(0,[z0,z1,z2,z3,z4,z30,z5]),(0,[z0,z1,z31,z2,z3,z4,z5]),(0,[z0,z1,z32,z2,z3,z4,z33]),(0,[z0,z1,z2,z3,z4,z34,z5]),(0,[z0,z1,z2,z35,z3,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z37,z2,z20,z4,z5]),(0,[z0,z1,z38,z2,z3,z4,z5]),(0,[z0,z1,z39,z2,z3,z4,z5]),(0,[z40,z0,z1,z2,z3,z4,z5]),(0,[z0,z41,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z5,z42]),(0,[z43,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z44,z2,z45,z4,z5]),(0,[z0,z1,z46,z2,z3,z47,z4])],[(0,[z0,z1,z2,z20,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z48]),(1,[z49,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z50,z4,z33,z5])]],
   [[(0,[z0,z1,z51,z2,z3,z4,z5]),(0,[z0,z1,z52,z2,z3,z4,z5]),(0,[z0,z1,z2,z53,z54,z4,z5]),(0,[z0,z55,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z56,z5]),(0,[z0,z1,z2,z57,z3,z4,z58]),(0,[z0,z1,z2,z4,z34,z5,z58])],[(0,[z0,z1,z2,z3,z59,z4,z5]),(0,[z0,z1,z60,z2,z3,z4,z5]),(0,[z43,z61,z1,z2,z3,z4,z5]),(0,[z62,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z63,z2,z45,z4,z5]),(0,[z0,z64,z1,z2,z3,z4,z5]),(0,[z0,z65,z1,z2,z3,z4,z5])],[(0,[z0,z66,z1,z2,z3,z4,z5]),(0,[z67,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z68,z5]),(0,[z0,z1,z2,z3,z4,z5,z69]),(0,[z0,z1,z2,z57,z3,z4,z5])],[(0,[z70,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z71,z2,z3,z4,z5])],[(0,[z0,z72,z1,z37,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z73,z74])],[(1,[z75,z0,z1,z3,z4,z5]),(0,[z0,z1,z76,z2,z3,z4,z5]),(0,[z0,z1,z77,z78,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z79,z5]),(0,[z0,z1,z2,z3,z4,z5,z80])],[(0,[z0,z1,z2,z3,z81,z4,z5]),(0,[z0,z1,z82,z2,z3,z4,z5]),(0,[z83,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z84,z2,z3,z4,z5])],[(1,[z0,z1,z2,z85,z4,z5]),(0,[z0,z1,z2,z86,z3,z4,z5]),(0,[z0,z1,z87,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z88]),(0,[z0,z1,z2,z3,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z90])],[(0,[z91,z0,z1,z19,z3,z4,z5]),(0,[z0,z1,z92,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z93,z4,z5])],[(0,[z94,z0,z1,z2,z3,z95,z5]),(0,[z96,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z97,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z98]),(0,[z0,z1,z2,z3,z4,z5,z99]),(0,[z0,z1,z100,z2,z3,z4,z5])],[(0,[z94,z101,z1,z2,z3,z4,z5]),(0,[z0,z1,z102,z2,z3,z4,z5])],[(0,[z103,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z104,z5]),(1,[z0,z1,z105,z3,z4,z5]),(0,[z106,z0,z1,z2,z3,z4,z5]),(0,[z107,z0,z1,z2,z3,z4,z5]),(0,[z108,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z74,z5])],[(0,[z0,z1,z2,z3,z4,z109,z5]),(0,[z0,z1,z2,z110,z3,z4,z5]),(0,[z27,z0,z1,z2,z111,z4,z5]),(0,[z0,z1,z2,z3,z4,z112,z5])],[(1,[z0,z1,z37,z54,z4,z5]),(0,[z0,z1,z113,z2,z3,z4,z5])],[(0,[z0,z1,z114,z2,z3,z4,z5]),(0,[z10,z0,z1,z115,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z116,z117])],[(0,[z0,z1,z2,z3,z4,z5,z118]),(0,[z119,z0,z1,z2,z120,z4,z5]),(0,[z0,z1,z121,z2,z3,z4,z5]),(0,[z122,z0,z1,z2,z3,z4,z116]),(0,[z0,z1,z2,z3,z4,z123,z5])],[(0,[z0,z1,z2,z124,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z125]),(0,[z126,z0,z1,z2,z3,z4,z5]),(0,[z0,z127,z2,z3,z4,z68,z5])],[(0,[z0,z1,z128,z2,z3,z4,z5]),(0,[z129,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z130,z2,z3,z4,z5]),(0,[z0,z1,z131,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z132,z4,z5]),(1,[z0,z1,z32,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z133,z5]),(0,[z0,z1,z2,z3,z134,z4,z5]),(0,[z0,z1,z2,z135,z3,z4,z5]),(0,[z0,z1,z2,z3,z68,z33,z5]),(0,[z0,z1,z19,z77,z3,z4,z5]),(0,[z0,z1,z32,z2,z3,z4,z5]),(0,[z136,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z137,z4,z5]),(0,[z0,z1,z115,z2,z4,z5,z58])],[(0,[z138,z0,z1,z2,z3,z4,z5]),(0,[z0,z139,z1,z2,z3,z4,z5]),(0,[z140,z1,z77,z2,z3,z4,z5])],[(0,[z0,z1,z141,z2,z3,z4,z5]),(0,[z142,z0,z1,z3,z54,z4,z5]),(0,[z0,z1,z2,z143,z3,z4,z5]),(0,[z0,z1,z144,z2,z3,z4,z5]),(0,[z0,z1,z2,z145,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z146]),(0,[z0,z1,z147,z2,z3,z4,z5]),(0,[z0,z148,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z37,z78,z3,z4,z5]),(0,[z0,z72,z1,z19,z2,z4,z5]),(0,[z0,z149,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z150,z3,z4,z5]),(1,[z0,z1,z2,z35,z3,z5])],[(1,[z0,z1,z2,z124,z4,z5]),(0,[z0,z1,z2,z151,z3,z4,z5]),(0,[z0,z1,z152,z2,z3,z4,z74]),(0,[z0,z1,z2,z3,z153,z4,z5])],[(0,[z0,z1,z2,z3,z4,z95,z5]),(0,[z142,z0,z1,z19,z3,z4,z5]),(0,[z0,z1,z20,z3,z154,z4,z5]),(0,[z0,z1,z155,z2,z3,z4,z5]),(1,[z1,z2,z3,z156,z4,z5]),(0,[z0,z1,z2,z3,z4,z157,z5]),(0,[z0,z1,z2,z3,z4,z5,z158]),(0,[z159,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z160,z3,z4,z5]),(0,[z0,z1,z2,z20,z111,z4,z5]),(1,[z21,z0,z1,z2,z3,z4]),(0,[z161,z0,z1,z2,z3,z162,z5]),(0,[z0,z1,z2,z3,z4,z163,z5]),(0,[z10,z0,z1,z2,z3,z164,z5]),(0,[z0,z1,z165,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z166,z4,z5]),(0,[z0,z1,z167,z2,z3,z4,z5])],[(0,[z0,z1,z2,z111,z120,z4,z5]),(0,[z0,z1,z168,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z169,z5]),(0,[z0,z1,z2,z3,z4,z5,z170]),(0,[z0,z1,z2,z3,z4,z171,z5]),(0,[z0,z1,z2,z172,z3,z4,z5])],[(0,[z0,z173,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z174]),(0,[z175,z0,z1,z2,z3,z68,z5]),(0,[z176,z0,z1,z2,z3,z4,z117])],[(0,[z94,z1,z177,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z178,z5]),(0,[z0,z1,z2,z3,z4,z179,z5]),(0,[z0,z180,z1,z2,z3,z4,z5])]],
   [[(0,[z181,z0,z1,z105,z3,z4,z5]),(0,[z122,z1,z2,z3,z4,z116,z5])],[(0,[z0,z1,z182,z177,z2,z4,z5]),(0,[z0,z1,z2,z3,z183,z4,z5]),(0,[z184,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z111,z3,z53,z4,z5]),(0,[z0,z1,z185,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z69,z58]),(0,[z0,z1,z186,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z187,z5]),(0,[z10,z0,z1,z188,z2,z3,z4]),(0,[z0,z1,z2,z3,z47,z189,z5])],[(0,[z0,z1,z2,z3,z4,z5,z190]),(0,[z0,z191,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z116,z69]),(1,[z0,z1,z2,z3,z4,z192]),(1,[z0,z1,z2,z3,z4,z73]),(0,[z0,z1,z115,z2,z57,z4,z5])],[(0,[z0,z1,z2,z3,z4,z193,z5]),(0,[z10,z194,z0,z1,z2,z3,z5]),(0,[z195,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z196,z2,z3,z4,z5]),(0,[z0,z1,z2,z197,z3,z4,z5])],[(0,[z0,z1,z2,z3,z198,z164,z5]),(0,[z0,z1,z2,z3,z4,z199,z5])],[(0,[z0,z1,z2,z3,z154,z4,z5])],[(1,[z0,z1,z2,z200,z4,z5]),(0,[z27,z119,z0,z1,z2,z4,z5]),(0,[z0,z1,z201,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z202,z5]),(0,[z203,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z204,z4,z5]),(0,[z0,z1,z2,z57,z3,z47,z4])],[(0,[z205,z0,z1,z2,z3,z4,z5]),(1,[z138,z1,z2,z3,z4,z206]),(0,[z207,z0,z1,z2,z3,z4,z5]),(0,[z1,z77,z208,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z25,z78,z3,z4,z5])],[(0,[z43,z0,z2,z45,z3,z4,z5]),(0,[z10,z0,z209,z2,z3,z4,z5]),(0,[z210,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z211])],[(0,[z0,z1,z2,z3,z212,z4,z5]),(0,[z0,z1,z2,z3,z213,z4,z5]),(0,[z0,z1,z2,z3,z4,z214,z5]),(0,[z0,z1,z2,z3,z4,z215,z5]),(0,[z0,z216,z1,z2,z3,z4,z5])],[(0,[z94,z0,z1,z2,z3,z4,z5]),(0,[z1,z52,z2,z78,z3,z4,z5]),(0,[z0,z1,z217,z2,z3,z4,z5]),(0,[z181,z0,z1,z77,z2,z4,z5]),(0,[z0,z1,z2,z3,z218,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z58])],[(0,[z119,z0,z72,z1,z2,z4,z5]),(0,[z0,z1,z219,z2,z3,z4,z5]),(0,[z0,z1,z2,z220,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z221])],[(0,[z94,z0,z1,z222,z3,z4,z5]),(0,[z101,z1,z2,z3,z120,z4,z5]),(0,[z194,z1,z2,z3,z4,z223,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z27,z49,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z224,z4,z5]),(0,[z0,z1,z77,z3,z54,z4,z5]),(1,[z0,z1,z225,z2,z3,z5])],[(0,[z0,z1,z19,z37,z3,z4,z5])],[(0,[z226,z0,z1,z177,z2,z4,z5]),(0,[z0,z1,z227,z2,z3,z4,z5]),(0,[z0,z1,z228,z2,z3,z4,z5]),(0,[z229,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z115,z2,z3,z189,z5])]],
   [[(0,[z101,z0,z177,z2,z3,z4,z5]),(0,[z142,z0,z1,z52,z3,z4,z5]),(0,[z0,z1,z2,z3,z230,z4,z5]),(0,[z176,z0,z1,z2,z3,z4,z69])],[(0,[z0,z72,z1,z2,z53,z4,z5])],[(0,[z0,z1,z39,z3,z231,z4,z5]),(1,[z0,z1,z167,z3,z4,z5])],[(0,[z0,z1,z105,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z232])],[(0,[z0,z1,z2,z3,z4,z233,z5]),(1,[z43,z0,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z234,z4,z5]),(0,[z0,z1,z2,z3,z4,z235,z5])],[(1,[z226,z0,z1,z2,z4,z5]),(0,[z0,z1,z236,z2,z3,z4,z5]),(0,[z0,z1,z19,z25,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z237]),(0,[z0,z1,z238,z2,z3,z4,z5])],[(1,[z101,z239,z2,z3,z4,z5]),(0,[z101,z239,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z240,z5]),(0,[z0,z1,z2,z241,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z242]),(0,[z0,z1,z2,z28,z3,z4,z5])],[(0,[z1,z2,z78,z20,z3,z4,z5]),(0,[z142,z1,z2,z20,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z243]),(0,[z0,z1,z2,z244,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z245]),(0,[z246,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z47,z189])]],
   [[(1,[z142,z1,z52,z3,z4,z5]),(0,[z142,z1,z52,z2,z3,z4,z5]),(0,[z0,z247,z1,z2,z3,z4,z5]),(0,[z248,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z249,z2,z3,z4,z5])],[(0,[z250,z0,z1,z2,z3,z4,z5]),(0,[z251,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z252]),(0,[z142,z119,z1,z2,z3,z4,z5]),(0,[z0,z1,z253,z2,z3,z4,z5]),(0,[z0,z1,z254,z2,z3,z4,z5]),(0,[z138,z0,z1,z2,z3,z47,z4]),(0,[z0,z25,z2,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z231,z164,z5]),(1,[z0,z1,z39,z3,z231,z5])],[(0,[z0,z1,z255,z177,z3,z4,z5]),(0,[z0,z256,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z257,z5]),(0,[z258,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z259,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z260,z5]),(1,[z0,z1,z261,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z262]),(0,[z142,z0,z263,z1,z3,z4,z5]),(0,[z0,z1,z264,z2,z3,z4,z5]),(0,[z0,z1,z2,z265,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z4,z5]),(1,[z0,z1,z2,z266,z4,z5]),(0,[z267,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z268,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z269,z5]),(0,[z0,z1,z270,z2,z3,z4,z5]),(1,[z0,z1,z63,z2,z4,z5]),(1,[z0,z1,z2,z3,z271,z5]),(0,[z0,z1,z209,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z272,z4,z5]),(0,[z273,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z50,z33,z5]),(0,[z0,z1,z2,z3,z93,z4,z5])],[(0,[z0,z1,z274,z2,z3,z4,z5]),(0,[z0,z1,z2,z275,z3,z4,z5]),(0,[z276,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z277,z278]),(0,[z0,z1,z2,z50,z3,z198,z5])]],
   [[(0,[z94,z0,z1,z2,z124,z4,z5]),(0,[z0,z1,z2,z3,z5,z42,z206]),(0,[z0,z1,z2,z3,z4,z5,z279]),(0,[z0,z280,z1,z2,z3,z4,z5])],[(0,[z94,z0,z1,z281,z3,z4,z5]),(0,[z0,z1,z2,z3,z85,z4,z5]),(0,[z0,z1,z282,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z283,z5])],[(0,[z43,z0,z1,z37,z3,z4,z5]),(0,[z0,z127,z284,z2,z3,z4,z5]),(0,[z0,z285,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z286,z4,z5])],[(0,[z287,z0,z1,z2,z3,z4,z5]),(0,[z288,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z289,z5]),(0,[z0,z1,z290,z2,z3,z4,z5]),(0,[z0,z291,z1,z2,z3,z4,z5]),(0,[z0,z292,z1,z2,z3,z4,z5])],[(0,[z1,z52,z2,z3,z120,z4,z5]),(0,[z21,z0,z1,z2,z3,z4,z223]),(0,[z0,z263,z1,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z293])],[(0,[z0,z1,z2,z3,z294,z4,z5]),(0,[z0,z284,z1,z2,z3,z4,z5]),(0,[z295,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z57,z4,z34,z5])],[(0,[z0,z1,z2,z3,z296,z4,z5]),(0,[z161,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z297,z4,z5]),(0,[z1,z19,z71,z2,z3,z4,z5]),(0,[z0,z1,z39,z2,z3,z189,z5]),(0,[z0,z1,z188,z2,z3,z4,z58])],[(0,[z298,z0,z1,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z117]),(0,[z299,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z5,z277]),(1,[z0,z1,z2,z93,z4,z5])]],
   [[(0,[z91,z0,z1,z3,z54,z4,z5]),(0,[z0,z127,z2,z3,z4,z117,z5]),(0,[z0,z1,z2,z300,z3,z4,z5]),(0,[z10,z0,z1,z31,z2,z3,z4]),(0,[z0,z1,z2,z50,z3,z4,z5]),(0,[z0,z1,z188,z2,z3,z4,z5])],[(0,[z101,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z301,z2,z3,z4,z5]),(0,[z181,z0,z1,z2,z120,z4,z5]),(0,[z43,z0,z1,z25,z3,z4,z5]),(0,[z0,z1,z302,z2,z3,z4,z5]),(1,[z0,z1,z165,z3,z74,z5])],[(0,[z0,z1,z2,z3,z303,z4,z5]),(0,[z0,z1,z2,z3,z4,z304,z5]),(0,[z10,z0,z1,z2,z3,z68,z5]),(1,[z0,z1,z2,z3,z4,z305]),(0,[z0,z1,z2,z3,z4,z305,z5]),(0,[z0,z1,z2,z3,z306,z4,z5])],[(0,[z181,z1,z52,z2,z3,z4,z5]),(0,[z0,z1,z52,z25,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z307,z5]),(0,[z0,z1,z2,z3,z4,z308,z5]),(0,[z309,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z19,z77,z4,z5]),(0,[z0,z1,z3,z4,z56,z5,z278]),(0,[z0,z1,z2,z3,z4,z310,z33])],[(1,[z161,z1,z2,z3,z162,z5]),(0,[z0,z1,z2,z3,z4,z116,z5]),(0,[z0,z1,z2,z3,z311,z4,z5]),(0,[z0,z1,z39,z2,z3,z231,z5]),(0,[z312,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z313])],[(1,[z94,z177,z2,z3,z4,z5]),(0,[z314,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z223,z68,z5]),(0,[z0,z284,z1,z2,z3,z68,z5]),(0,[z0,z1,z315,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z316]),(0,[z0,z1,z2,z3,z317,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z318]),(0,[z0,z1,z2,z3,z4,z319,z5]),(0,[z0,z1,z2,z3,z137,z4,z5]),(0,[z320,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z321,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z322,z5])]],
   [[(1,[z0,z1,z255,z3,z4,z5]),(0,[z0,z1,z323,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z324,z5]),(0,[z43,z91,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z325,z4,z5]),(0,[z326,z0,z1,z2,z3,z4,z5]),(0,[z43,z0,z1,z2,z137,z4,z5]),(0,[z0,z1,z2,z3,z4,z327,z5]),(0,[z0,z1,z3,z231,z4,z74,z5]),(0,[z0,z1,z2,z3,z4,z328,z5]),(0,[z0,z1,z2,z329,z3,z4,z5])],[(0,[z330,z0,z1,z2,z3,z4,z5]),(0,[z0,z263,z25,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z164,z33,z5]),(0,[z331,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z332,z5])],[(0,[z0,z1,z2,z333,z3,z4,z5]),(0,[z0,z334,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z335,z3,z4,z5])],[(0,[z336,z0,z1,z2,z3,z4,z5]),(0,[z43,z0,z1,z2,z3,z4,z283]),(0,[z0,z1,z46,z31,z3,z4,z5])],[(0,[z337,z0,z1,z2,z3,z4,z5]),(0,[z26,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z338,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z339,z5])],[(0,[z0,z1,z340,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z341,z5]),(0,[z0,z1,z2,z3,z342,z4,z5]),(0,[z10,z0,z1,z2,z50,z3,z5])],[(0,[z101,z1,z2,z78,z3,z4,z5]),(0,[z0,z1,z2,z343,z3,z4,z5])]],
   [[(1,[z122,z1,z2,z3,z4,z116]),(1,[z0,z1,z44,z2,z4,z5]),(1,[z0,z1,z2,z3,z344,z5]),(1,[z0,z72,z2,z111,z4,z5]),(0,[z175,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z47,z4,z117])],[(1,[z0,z1,z2,z345,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z69])],[(0,[z0,z1,z2,z3,z346,z4,z5]),(0,[z0,z1,z2,z120,z53,z4,z5]),(0,[z0,z1,z2,z3,z4,z347,z5]),(0,[z43,z0,z1,z2,z3,z348,z5]),(0,[z0,z1,z2,z3,z4,z349,z5]),(0,[z0,z1,z2,z3,z350,z4,z5]),(0,[z0,z1,z46,z3,z4,z5,z278])],[(0,[z119,z0,z1,z2,z3,z4,z5]),(0,[z0,z351,z1,z2,z3,z4,z5]),(0,[z0,z1,z352,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z353]),(1,[z0,z1,z2,z3,z4,z283]),(0,[z176,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z354,z5])],[],[(0,[z355,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z356,z3,z4,z5]),(0,[z0,z1,z2,z3,z357,z4,z5]),(0,[z0,z1,z115,z2,z3,z33,z5])],[(0,[z0,z358,z1,z2,z3,z4,z5]),(0,[z122,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z359,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z360])],[(0,[z0,z1,z37,z2,z120,z4,z5]),(0,[z0,z361,z1,z2,z3,z4,z5]),(0,[z0,z1,z362,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z182,z2,z4,z5]),(0,[z363,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z364]),(0,[z0,z1,z46,z2,z3,z4,z56]),(0,[z0,z1,z2,z3,z4,z365,z5])],[(0,[z0,z1,z182,z2,z3,z4,z5]),(0,[z91,z0,z1,z52,z3,z4,z5]),(1,[z0,z1,z2,z3,z348,z5]),(0,[z0,z1,z2,z3,z4,z5,z366]),(0,[z367,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z368,z4,z5]),(0,[z0,z1,z2,z369,z3,z4,z5]),(0,[z10,z0,z1,z2,z370,z4,z5])],[(0,[z119,z0,z1,z2,z54,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z237]),(0,[z0,z1,z371,z2,z3,z4,z5]),(0,[z0,z1,z372,z2,z3,z4,z5]),(0,[z0,z1,z31,z2,z3,z47,z4])],[(0,[z0,z1,z2,z373,z3,z4,z5]),(0,[z181,z0,z72,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z374,z5]),(0,[z0,z1,z2,z3,z375,z4,z5]),(0,[z0,z1,z2,z3,z376,z4,z5]),(1,[z0,z1,z152,z2,z3,z4]),(0,[z0,z1,z377,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z11])],[(0,[z0,z1,z2,z3,z378,z4,z5]),(0,[z0,z1,z379,z2,z3,z4,z5]),(0,[z0,z380,z1,z2,z3,z4,z5])],[(1,[z194,z1,z2,z3,z223,z5]),(0,[z0,z1,z208,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z73,z5]),(0,[z0,z1,z381,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z164,z189,z5]),(0,[z0,z1,z2,z3,z382,z4,z5]),(0,[z0,z1,z2,z383,z3,z4,z5])]],
   [[(0,[z0,z1,z222,z2,z3,z4,z5]),(0,[z384,z0,z1,z2,z3,z4,z5]),(0,[z385,z0,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z223,z5,z206]),(0,[z0,z1,z2,z3,z4,z386,z5])],[(0,[z75,z0,z1,z177,z3,z4,z5]),(0,[z119,z1,z2,z78,z3,z4,z5]),(0,[z27,z0,z72,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z387,z5]),(0,[z0,z1,z2,z388,z3,z4,z5]),(0,[z0,z1,z2,z3,z47,z4,z69]),(0,[z389,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z390,z4,z5]),(0,[z27,z0,z1,z2,z3,z271,z5]),(0,[z0,z1,z2,z3,z271,z4,z5]),(0,[z0,z127,z1,z2,z3,z4,z117]),(0,[z0,z391,z1,z2,z3,z4,z5])],[(0,[z119,z0,z1,z2,z20,z4,z5]),(0,[z0,z1,z2,z3,z164,z223,z5]),(0,[z0,z1,z2,z3,z392,z4,z5]),(0,[z0,z1,z2,z3,z4,z393,z5]),(0,[z0,z1,z394,z2,z3,z4,z5]),(0,[z0,z1,z188,z2,z3,z47,z4]),(0,[z0,z1,z2,z3,z4,z395,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z91,z0,z263,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z68,z74,z5])],[(0,[z0,z1,z2,z3,z4,z396,z5])],[(0,[z226,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z397,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z120,z4,z5]),(0,[z0,z72,z1,z2,z111,z4,z5]),(0,[z0,z1,z2,z398,z3,z4,z5]),(0,[z0,z1,z225,z2,z3,z5,z278]),(0,[z399,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z400,z1,z2,z3,z4,z5]),(0,[z401,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z402,z5]),(0,[z0,z1,z403,z2,z3,z4,z5]),(0,[z0,z1,z2,z404,z3,z4,z5])],[(0,[z0,z1,z405,z2,z3,z4,z5]),(0,[z406,z0,z1,z2,z3,z4,z5]),(0,[z407,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z408,z5])],[(0,[z409,z0,z1,z2,z3,z4,z5]),(1,[z176,z0,z2,z3,z4,z69])],[(0,[z142,z1,z177,z2,z3,z4,z5]),(0,[z0,z1,z410,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z411,z4,z5]),(0,[z412,z0,z1,z2,z3,z4,z5])],[(0,[z0,z413,z1,z2,z3,z4,z5]),(0,[z0,z1,z77,z2,z53,z4,z5]),(1,[z0,z1,z414,z3,z4,z5]),(0,[z0,z1,z2,z415,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z416]),(0,[z10,z0,z1,z165,z2,z3,z5]),(0,[z0,z1,z2,z3,z417,z4,z5]),(0,[z0,z1,z115,z2,z198,z4,z5])],[(0,[z418,z0,z1,z2,z3,z4,z5]),(0,[z194,z0,z1,z2,z3,z189,z5]),(0,[z0,z1,z2,z3,z4,z419,z5]),(0,[z0,z1,z39,z31,z3,z4,z5]),(1,[z0,z1,z115,z2,z198,z5]),(0,[z0,z1,z188,z2,z4,z5,z58])]],
   [[(0,[z0,z239,z1,z2,z3,z4,z5]),(0,[z420,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z42]),(0,[z43,z0,z1,z2,z266,z4,z5]),(0,[z0,z1,z2,z421,z3,z4,z5])],[(0,[z0,z1,z422,z2,z3,z4,z5]),(1,[z0,z1,z423,z3,z4,z5]),(0,[z0,z1,z424,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z425,z5]),(0,[z0,z1,z426,z2,z3,z4,z5]),(0,[z10,z0,z292,z2,z3,z4,z5])],[(0,[z27,z181,z0,z1,z2,z4,z5]),(1,[z0,z1,z3,z154,z4,z5]),(0,[z427,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z164,z4,z68,z5]),(0,[z0,z1,z2,z428,z3,z4,z5])],[(0,[z0,z1,z2,z3,z162,z164,z5]),(0,[z138,z1,z2,z3,z4,z5,z206]),(0,[z0,z1,z2,z3,z4,z5,z429]),(0,[z0,z1,z430,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z431,z4,z5]),(0,[z0,z1,z2,z3,z4,z432,z5]),(0,[z0,z1,z2,z433,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z434,z58])],[(0,[z94,z0,z239,z2,z3,z4,z5]),(0,[z435,z0,z1,z2,z3,z4,z5]),(0,[z194,z0,z1,z2,z3,z223,z5]),(0,[z62,z1,z2,z45,z3,z4,z5]),(1,[z0,z1,z436,z3,z4,z5]),(0,[z0,z1,z152,z2,z3,z4,z5])],[(0,[z437,z0,z1,z2,z3,z4,z5]),(0,[z0,z127,z1,z2,z3,z4,z69]),(1,[z1,z71,z2,z3,z4,z5]),(0,[z0,z1,z39,z3,z4,z5,z278]),(0,[z0,z1,z2,z3,z4,z5,z438])],[(1,[z0,z1,z2,z3,z439,z5]),(0,[z0,z440,z1,z2,z3,z4,z5]),(1,[z129,z0,z1,z2,z3,z5]),(0,[z441,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z177,z2,z3,z4,z5]),(0,[z0,z1,z45,z3,z54,z4,z5])]],
   [[(0,[z142,z0,z1,z2,z3,z4,z5])],[(0,[z0,z442,z1,z2,z3,z4,z5]),(0,[z0,z1,z443,z2,z3,z4,z5]),(0,[z0,z1,z2,z444,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z445,z5]),(0,[z446,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z188,z2,z4,z58])],[(0,[z142,z91,z1,z2,z3,z4,z5]),(0,[z119,z1,z2,z3,z120,z4,z5]),(0,[z0,z1,z447,z2,z3,z4,z5]),(0,[z122,z0,z1,z2,z3,z47,z4]),(0,[z0,z1,z19,z77,z2,z4,z5]),(0,[z0,z1,z31,z2,z3,z4,z56])],[(0,[z0,z1,z2,z281,z3,z4,z5]),(0,[z0,z1,z2,z448,z3,z4,z5]),(0,[z449,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z19,z45,z3,z4,z5]),(0,[z0,z1,z37,z3,z54,z4,z5])],[(0,[z0,z1,z2,z450,z3,z4,z5]),(0,[z0,z1,z2,z3,z348,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z5])],[(0,[z451,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z452,z2,z3,z4,z5]),(0,[z453,z0,z1,z2,z3,z4,z5]),(1,[z407,z1,z2,z3,z4,z5]),(0,[z140,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z189,z5])],[(0,[z27,z0,z1,z2,z3,z344,z5]),(0,[z0,z1,z2,z3,z454,z4,z5])],[(1,[z0,z1,z2,z455,z4,z5]),(0,[z0,z1,z2,z456,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z457]),(0,[z0,z1,z2,z3,z4,z5,z458]),(0,[z0,z1,z459,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z460,z5])]],
   [[],[(0,[z0,z1,z77,z52,z3,z4,z5]),(0,[z0,z1,z2,z461,z3,z4,z5]),(0,[z0,z1,z3,z4,z74,z5,z278])],[(0,[z0,z1,z462,z2,z3,z4,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z119,z239,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z463,z5]),(1,[z0,z1,z241,z3,z4,z5]),(0,[z0,z1,z464,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z465,z4,z5]),(0,[z0,z127,z1,z2,z3,z179,z5]),(0,[z0,z1,z77,z37,z2,z4,z5]),(0,[z0,z1,z2,z3,z466,z4,z5])],[(0,[z27,z0,z1,z2,z53,z4,z5]),(0,[z0,z1,z2,z3,z467,z4,z5]),(0,[z0,z1,z468,z2,z3,z4,z5]),(0,[z0,z1,z469,z2,z3,z4,z5])],[(0,[z181,z1,z2,z20,z3,z4,z5]),(0,[z0,z1,z470,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z5,z192]),(0,[z0,z1,z471,z2,z3,z4,z5]),(0,[z0,z1,z472,z2,z3,z4,z5])],[],[(0,[z0,z473,z1,z2,z3,z4,z5]),(0,[z161,z0,z1,z2,z3,z189,z5]),(0,[z0,z1,z2,z3,z4,z344,z5])]],
   [[(0,[z0,z1,z474,z2,z3,z4,z5]),(0,[z181,z119,z1,z2,z3,z4,z5]),(1,[z27,z0,z2,z53,z4,z5]),(0,[z176,z0,z127,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z475]),(0,[z476,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z477,z3,z4,z5]),(0,[z0,z1,z2,z50,z3,z189,z5])],[(1,[z0,z1,z2,z3,z4,z310])],[(0,[z0,z1,z2,z3,z345,z4,z5]),(0,[z0,z1,z2,z3,z478,z4,z5]),(0,[z0,z1,z25,z3,z54,z4,z5]),(1,[z479,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z480,z3,z4,z5]),(0,[z0,z1,z414,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z481,z5])],[(0,[z91,z1,z2,z3,z120,z4,z5]),(0,[z0,z1,z482,z2,z3,z4,z5]),(0,[z0,z72,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z198,z68,z5]),(0,[z483,z0,z1,z2,z3,z4,z5]),(0,[z0,z127,z1,z2,z3,z484,z5]),(0,[z0,z1,z2,z485,z3,z4,z5]),(0,[z0,z1,z2,z3,z47,z4,z5])],[(0,[z138,z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z423,z2,z3,z4,z5])],[(0,[z486,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z52,z2,z345,z4,z5]),(0,[z0,z1,z2,z3,z487,z4,z5]),(0,[z43,z0,z1,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z488,z5]),(0,[z0,z1,z2,z3,z489,z4,z5]),(0,[z0,z1,z2,z4,z33,z5,z58])]],
   [[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z490,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z53,z4,z5]),(0,[z491,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z492]),(0,[z0,z1,z2,z57,z3,z4,z34])],[(0,[z0,z1,z2,z78,z3,z4,z5]),(0,[z0,z1,z2,z200,z3,z4,z5]),(0,[z0,z1,z52,z45,z3,z4,z5]),(0,[z0,z1,z493,z2,z3,z4,z5]),(0,[z61,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z494,z2,z3,z4,z5]),(0,[z495,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z496,z5]),(0,[z0,z1,z497,z2,z3,z4,z5]),(0,[z0,z1,z46,z2,z3,z4,z278]),(0,[z0,z498,z1,z2,z3,z4,z5])],[(0,[z0,z499,z1,z2,z3,z4,z5]),(0,[z181,z0,z1,z2,z54,z4,z5]),(0,[z0,z1,z500,z2,z3,z4,z5]),(0,[z0,z501,z1,z2,z3,z4,z5])],[(0,[z94,z0,z1,z2,z3,z4,z416]),(0,[z0,z1,z37,z52,z3,z4,z5]),(0,[z0,z1,z502,z2,z3,z4,z5]),(0,[z0,z1,z503,z2,z3,z4,z5]),(0,[z504,z0,z1,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z57,z3,z4])],[],[(0,[z0,z1,z2,z3,z4,z505,z5]),(0,[z0,z1,z506,z2,z3,z4,z5])],[(0,[z94,z1,z2,z20,z3,z4,z5]),(0,[z1,z177,z2,z78,z3,z4,z5]),(0,[z181,z0,z1,z241,z3,z4,z5]),(0,[z507,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z94,z1,z52,z2,z3,z4,z5]),(0,[z0,z1,z19,z2,z120,z4,z5]),(0,[z194,z161,z1,z2,z3,z4,z5]),(0,[z122,z1,z2,z3,z4,z223,z5]),(0,[z508,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z509,z4,z5]),(0,[z0,z1,z2,z3,z4,z510,z5]),(1,[z0,z1,z2,z370,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z511])],[(0,[z10,z380,z1,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z189])],[(0,[z94,z119,z1,z2,z3,z4,z5]),(0,[z0,z1,z512,z2,z3,z4,z5]),(0,[z27,z0,z1,z37,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z513]),(0,[z0,z1,z2,z3,z4,z514,z5]),(0,[z0,z1,z2,z3,z231,z4,z5])],[(0,[z142,z101,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z515,z5]),(0,[z0,z1,z2,z261,z3,z4,z5])],[(0,[z0,z1,z436,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z516,z4,z5]),(0,[z0,z1,z2,z3,z517,z4,z5]),(0,[z10,z0,z1,z39,z2,z3,z5]),(1,[z0,z1,z46,z3,z4,z278])],[(0,[z0,z518,z1,z2,z3,z4,z5]),(0,[z0,z284,z1,z2,z3,z4,z192]),(1,[z0,z1,z2,z3,z179,z5]),(0,[z519,z0,z1,z2,z3,z4,z5])],[(0,[z43,z0,z1,z2,z3,z387,z5])],[(0,[z0,z1,z520,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z521,z5]),(1,[z0,z1,z2,z3,z4,z125]),(0,[z0,z1,z44,z2,z3,z4,z5]),(0,[z0,z72,z2,z111,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z310,z5]),(0,[z0,z1,z2,z370,z3,z4,z5])]],
   [[(0,[z0,z522,z1,z2,z3,z4,z5]),(0,[z0,z127,z1,z2,z3,z4,z5]),(0,[z0,z1,z165,z2,z3,z189,z5])],[(0,[z0,z1,z2,z3,z4,z523,z5]),(0,[z0,z1,z2,z3,z4,z524,z5]),(0,[z0,z1,z2,z3,z4,z5,z525])],[(0,[z0,z1,z2,z3,z526,z4,z5]),(0,[z27,z0,z1,z436,z3,z4,z5]),(0,[z0,z1,z2,z111,z3,z4,z5]),(0,[z479,z0,z1,z2,z3,z4,z5]),(0,[z0,z527,z1,z2,z3,z4,z5]),(0,[z528,z0,z1,z2,z3,z4,z5]),(1,[z0,z209,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z529,z5]),(0,[z239,z1,z2,z20,z3,z4,z5]),(0,[z0,z1,z2,z3,z530,z4,z5]),(0,[z161,z1,z2,z3,z4,z5,z206]),(0,[z43,z247,z1,z2,z3,z4,z5]),(0,[z0,z263,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z231,z68,z5]),(0,[z0,z1,z2,z3,z164,z74,z5]),(0,[z0,z1,z2,z531,z3,z4,z5])],[(0,[z239,z1,z52,z2,z3,z4,z5]),(0,[z532,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z533,z4,z5]),(0,[z10,z0,z1,z2,z3,z5,z11])],[(0,[z0,z1,z2,z534,z3,z4,z5]),(0,[z535,z0,z1,z2,z3,z4,z5])],[(0,[z0,z536,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z156,z53,z4,z5]),(0,[z0,z1,z537,z2,z3,z4,z5]),(0,[z538,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z539,z4,z5])],[(0,[z175,z0,z284,z2,z3,z4,z5]),(0,[z0,z284,z2,z3,z4,z5,z69]),(1,[z0,z1,z2,z3,z484,z5]),(0,[z0,z1,z165,z2,z3,z231,z5]),(0,[z0,z1,z2,z3,z4,z540,z5])]],
   [[(0,[z0,z1,z541,z2,z3,z4,z5])],[(0,[z91,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z542,z2,z4,z5]),(0,[z0,z1,z2,z3,z543,z4,z5]),(0,[z0,z544,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z545,z4,z5])],[(1,[z247,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z546,z5]),(0,[z0,z1,z2,z111,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z547,z5]),(0,[z0,z1,z2,z3,z4,z5,z548]),(0,[z0,z1,z2,z3,z47,z4,z189])],[(0,[z549,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z237,z5]),(0,[z0,z1,z550,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z33,z5]),(0,[z10,z551,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z552,z5]),(0,[z0,z1,z2,z3,z553,z4,z5]),(0,[z0,z1,z2,z554,z3,z4,z5]),(1,[z0,z1,z168,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z555,z5]),(0,[z0,z1,z39,z165,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z117,z278]),(0,[z0,z1,z2,z3,z4,z556,z5])],[(0,[z181,z101,z1,z2,z3,z4,z5]),(0,[z0,z1,z557,z2,z3,z4,z5]),(0,[z138,z122,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z266,z3,z4,z5]),(0,[z0,z1,z558,z2,z3,z4,z5]),(0,[z27,z0,z1,z19,z2,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z559]),(0,[z1,z2,z20,z3,z120,z4,z5]),(0,[z479,z1,z2,z3,z53,z4,z5]),(0,[z560,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z5,z434]),(0,[z0,z1,z2,z3,z561,z4,z5]),(1,[z0,z292,z2,z3,z4,z5])]],
   [[(0,[z1,z177,z2,z3,z120,z4,z5]),(0,[z0,z1,z2,z3,z4,z117,z206])],[(0,[z0,z1,z2,z3,z4,z562,z5]),(0,[z0,z1,z2,z3,z4,z5,z563]),(0,[z0,z1,z2,z57,z4,z33,z5])],[(0,[z564,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z565,z4,z5]),(0,[z566,z0,z1,z2,z3,z4,z5]),(1,[z0,z127,z2,z3,z4,z117]),(0,[z0,z1,z567,z2,z3,z4,z5]),(0,[z10,z0,z1,z261,z3,z4,z5])],[(0,[z27,z0,z1,z2,z3,z4,z6]),(0,[z0,z568,z1,z2,z3,z4,z5]),(0,[z0,z1,z569,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z570,z5]),(0,[z0,z1,z165,z3,z4,z74,z5]),(0,[z0,z1,z2,z3,z571,z4,z5]),(0,[z0,z1,z572,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z4,z11])],[(0,[z1,z2,z356,z45,z3,z4,z5]),(0,[z0,z1,z31,z2,z3,z4,z278])],[(0,[z0,z1,z2,z3,z439,z4,z5]),(0,[z573,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z574,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z575,z5])],[(0,[z0,z1,z225,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z576,z4,z5]),(0,[z0,z1,z2,z3,z577,z4,z5]),(0,[z0,z578,z1,z2,z3,z4,z5])],[(0,[z579,z0,z1,z2,z3,z4,z5]),(0,[z91,z1,z2,z78,z3,z4,z5]),(0,[z10,z122,z0,z1,z2,z3,z4]),(0,[z580,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z414,z3,z53,z4,z5]),(0,[z0,z1,z2,z3,z4,z34,z117]),(0,[z0,z1,z2,z581,z3,z4,z5]),(0,[z0,z1,z2,z50,z3,z33,z5])]],
   [[],[(0,[z0,z1,z2,z3,z455,z4,z5]),(0,[z582,z0,z1,z2,z3,z4,z5]),(0,[z194,z0,z1,z2,z3,z162,z5]),(0,[z10,z138,z0,z1,z2,z3,z4]),(0,[z0,z1,z423,z3,z53,z4,z5]),(0,[z0,z1,z2,z3,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z277])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z583,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z584]),(0,[z175,z0,z2,z3,z4,z68,z5]),(1,[z0,z1,z31,z3,z4,z56]),(0,[z0,z585,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z56,z117])],[(1,[z0,z1,z222,z3,z4,z5]),(0,[z0,z1,z586,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z587]),(0,[z0,z1,z588,z2,z3,z4,z5])],[(0,[z142,z0,z1,z2,z85,z4,z5]),(0,[z10,z161,z0,z1,z2,z3,z5]),(1,[z61,z1,z2,z3,z4,z5]),(0,[z0,z1,z589,z2,z3,z4,z5]),(0,[z176,z0,z2,z3,z4,z5,z69]),(0,[z0,z1,z590,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z591])],[(0,[z0,z1,z2,z3,z4,z592,z5]),(0,[z593,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z594,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z595]),(0,[z0,z1,z2,z596,z3,z4,z5])],[(0,[z0,z1,z2,z3,z597,z4,z5]),(0,[z129,z0,z1,z2,z3,z5,z206]),(0,[z598,z0,z1,z2,z3,z4,z5]),(1,[z175,z0,z2,z3,z68,z5]),(0,[z0,z1,z188,z2,z57,z4,z5])]],
   [[(0,[z0,z49,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z599])],[(0,[z0,z1,z542,z2,z3,z4,z5]),(0,[z138,z0,z1,z2,z3,z4,z116]),(0,[z600,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z601,z5])],[(0,[z181,z1,z177,z2,z3,z4,z5]),(0,[z602,z0,z1,z2,z3,z4,z5]),(0,[z603,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z604,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z605,z5]),(0,[z0,z1,z606,z2,z3,z4,z5])],[(0,[z0,z607,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z608,z5]),(0,[z0,z284,z2,z3,z164,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z609]),(0,[z0,z1,z2,z3,z610,z4,z5]),(0,[z0,z611,z1,z2,z3,z4,z5]),(0,[z0,z1,z612,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z133]),(0,[z0,z1,z613,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z614]),(0,[z0,z1,z615,z2,z3,z4,z5]),(0,[z0,z1,z616,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z47,z4,z11])],[(0,[z0,z1,z2,z3,z4,z223,z5]),(0,[z0,z284,z1,z2,z3,z4,z305]),(1,[z140,z1,z2,z3,z4,z5]),(0,[z0,z1,z39,z2,z3,z74,z5]),(0,[z0,z1,z617,z2,z3,z4,z5])],[(0,[z0,z1,z2,z618,z3,z4,z5]),(0,[z619,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z28,z3,z4,z5]),(0,[z0,z1,z620,z2,z3,z4,z5])],[(0,[z94,z0,z177,z2,z3,z4,z5]),(0,[z621,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z622]),(0,[z0,z1,z2,z623,z3,z4,z5]),(0,[z0,z1,z2,z3,z198,z4,z5])]],
   [[(0,[z0,z1,z2,z624,z3,z4,z5]),(0,[z122,z161,z1,z2,z3,z4,z5]),(0,[z43,z0,z263,z2,z3,z4,z5]),(0,[z0,z1,z625,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z626,z5])],[(0,[z0,z1,z2,z3,z4,z34,z69]),(0,[z407,z1,z19,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z627])],[(0,[z43,z142,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z628]),(0,[z0,z629,z1,z2,z3,z4,z5]),(0,[z0,z1,z31,z3,z4,z56,z5])],[(0,[z0,z1,z2,z3,z630,z4,z5]),(0,[z631,z0,z1,z2,z3,z4,z5])],[(0,[z75,z0,z1,z2,z3,z4,z5]),(0,[z632,z0,z1,z2,z3,z4,z5])],[(0,[z0,z263,z1,z77,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z56,z69]),(0,[z0,z1,z2,z633,z3,z4,z5]),(0,[z551,z0,z1,z2,z3,z4,z5])],[(0,[z181,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z634,z5])],[(0,[z0,z1,z635,z2,z3,z4,z5]),(0,[z161,z0,z1,z2,z3,z223,z5]),(1,[z1,z2,z356,z3,z4,z5]),(0,[z636,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z57,z4,z34])]],
   [[(1,[z0,z1,z281,z3,z4,z5]),(0,[z637,z0,z1,z2,z3,z4,z5]),(0,[z181,z91,z1,z2,z3,z4,z5]),(0,[z0,z1,z638,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z639,z5]),(0,[z0,z1,z2,z3,z4,z640,z5])],[(1,[z0,z1,z2,z3,z4,z521]),(0,[z0,z1,z2,z3,z4,z641,z5]),(0,[z0,z1,z77,z2,z3,z4,z5]),(0,[z0,z1,z2,z642,z3,z4,z5])],[(0,[z0,z1,z2,z643,z3,z4,z5]),(0,[z644,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z46,z2,z3,z4,z5])],[(0,[z645,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z164,z4,z5]),(0,[z0,z1,z2,z3,z646,z4,z5])],[(0,[z647,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z648,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z47,z5])],[(0,[z101,z0,z239,z2,z3,z4,z5]),(0,[z91,z0,z1,z78,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z206,z69]),(0,[z0,z1,z2,z3,z4,z5,z649]),(0,[z0,z284,z1,z2,z3,z164,z5]),(0,[z650,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z115,z2,z3,z198,z5])],[(0,[z0,z1,z2,z20,z53,z4,z5]),(0,[z122,z0,z1,z2,z3,z4,z206]),(0,[z0,z1,z31,z3,z4,z74,z5]),(0,[z0,z1,z651,z2,z3,z4,z5]),(0,[z0,z1,z188,z2,z3,z4,z34])],[(1,[z0,z263,z25,z3,z4,z5]),(1,[z380,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z652,z4,z5]),(1,[z1,z208,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z653,z4,z5]),(0,[z0,z1,z2,z3,z654,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z655])],[(0,[z0,z1,z2,z3,z4,z5,z416]),(0,[z91,z239,z1,z2,z3,z4,z5]),(1,[z181,z1,z2,z20,z4,z5]),(0,[z161,z1,z2,z3,z162,z4,z5]),(0,[z1,z2,z3,z4,z116,z5,z206]),(0,[z0,z1,z2,z3,z4,z656,z5]),(0,[z0,z1,z2,z657,z3,z4,z5])],[(0,[z658,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z659,z2,z3,z4,z5]),(0,[z0,z1,z2,z660,z3,z4,z5]),(0,[z0,z1,z2,z3,z661,z4,z5]),(0,[z0,z1,z2,z3,z4,z662,z5]),(0,[z0,z1,z2,z3,z4,z663,z5])],[(0,[z0,z1,z2,z3,z4,z5,z664]),(0,[z0,z1,z2,z3,z162,z4,z5]),(0,[z43,z0,z1,z2,z3,z4,z125]),(0,[z0,z1,z2,z3,z4,z69,z278]),(0,[z0,z1,z2,z3,z4,z665,z5])],[(1,[z0,z1,z2,z3,z95,z5]),(0,[z142,z0,z1,z2,z200,z4,z5]),(0,[z0,z1,z2,z3,z4,z387,z5]),(0,[z0,z1,z2,z3,z156,z4,z5]),(0,[z0,z2,z3,z4,z68,z5,z69]),(0,[z0,z1,z666,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z667])],[(0,[z668,z0,z1,z2,z3,z4,z5]),(0,[z669,z0,z1,z2,z3,z4,z5]),(0,[z43,z0,z1,z77,z3,z4,z5]),(0,[z0,z1,z670,z2,z3,z4,z5]),(0,[z0,z1,z2,z198,z4,z33,z5]),(0,[z0,z1,z2,z3,z189,z5,z11])],[(0,[z0,z1,z2,z3,z68,z189,z5]),(0,[z0,z1,z115,z2,z3,z4,z5])],[(0,[z94,z0,z1,z2,z3,z439,z5]),(0,[z0,z1,z542,z52,z2,z4,z5]),(0,[z181,z0,z1,z2,z20,z4,z5]),(0,[z0,z1,z2,z671,z3,z4,z5]),(0,[z0,z1,z2,z672,z3,z4,z5]),(1,[z62,z1,z2,z3,z4,z5]),(0,[z27,z26,z1,z2,z3,z4,z5])]],
   [[(0,[z239,z1,z177,z2,z3,z4,z5]),(0,[z1,z2,z3,z162,z4,z223,z5]),(0,[z0,z1,z673,z2,z3,z4,z5])],[(0,[z674,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z255,z2,z3,z4,z5]),(0,[z0,z1,z2,z675,z3,z4,z5]),(0,[z0,z1,z676,z2,z3,z4,z5])],[(0,[z94,z91,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z484,z4,z5]),(0,[z0,z1,z19,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z677])],[(0,[z194,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z115,z2,z50,z4,z5]),(0,[z0,z1,z2,z35,z3,z5,z58])],[(0,[z0,z1,z78,z45,z3,z4,z5]),(0,[z0,z1,z678,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z162,z68,z5]),(0,[z679,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z680,z5]),(0,[z0,z1,z2,z3,z4,z5,z681]),(0,[z0,z1,z37,z2,z3,z4,z5]),(0,[z0,z1,z165,z2,z3,z74,z5]),(0,[z0,z1,z682,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z683])],[(0,[z0,z1,z63,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z684]),(0,[z0,z1,z2,z3,z4,z5,z278]),(0,[z0,z1,z2,z685,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z686]),(0,[z687,z0,z1,z2,z3,z4,z5]),(0,[z688,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z434])],[(0,[z689,z0,z1,z2,z3,z4,z5]),(0,[z142,z0,z1,z78,z3,z4,z5]),(1,[z119,z1,z2,z120,z4,z5]),(0,[z690,z0,z1,z2,z3,z4,z5]),(0,[z0,z263,z1,z37,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z691]),(0,[z0,z2,z3,z4,z117,z5,z69]),(0,[z692,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z94,z0,z1,z2,z455,z4,z5]),(1,[z91,z1,z78,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z521,z223]),(0,[z0,z1,z2,z3,z4,z5,z206]),(0,[z0,z1,z2,z693,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z5]),(0,[z27,z0,z2,z3,z53,z4,z5]),(0,[z175,z0,z1,z2,z3,z164,z5]),(0,[z10,z0,z1,z46,z2,z3,z4])],[(1,[z551,z1,z2,z3,z4,z5])],[(0,[z94,z0,z1,z2,z3,z4,z133]),(0,[z694,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z168,z20,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z695,z5]),(0,[z0,z696,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z697]),(0,[z0,z1,z19,z2,z54,z4,z5])],[(0,[z119,z0,z1,z77,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z117,z58]),(0,[z0,z1,z2,z698,z3,z4,z5])],[(1,[z0,z284,z2,z3,z164,z5]),(0,[z0,z1,z37,z2,z54,z4,z5]),(0,[z10,z0,z1,z167,z3,z4,z5])],[(0,[z699,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z700,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z701,z4,z5]),(0,[z0,z1,z2,z3,z4,z117,z5])],[(0,[z0,z263,z1,z25,z3,z4,z5]),(0,[z0,z1,z77,z2,z111,z4,z5]),(0,[z0,z1,z2,z3,z702,z4,z5])],[(0,[z0,z1,z2,z3,z4,z703,z5]),(0,[z704,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z705,z5]),(0,[z0,z1,z2,z3,z4,z706,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z226,z0,z1,z255,z4,z5]),(0,[z0,z1,z105,z54,z4,z5]),(0,[z0,z1,z2,z3,z47,z319]),(0,[z0,z1,z37,z28,z4,z5]),(0,[z0,z1,z707,z3,z4,z5]),(0,[z0,z1,z19,z17,z4,z5])],[(0,[z75,z226,z0,z1,z4,z5]),(0,[z107,z1,z2,z3,z4,z116]),(0,[z0,z1,z2,z137,z4,z5]),(0,[z0,z1,z19,z512,z4,z5]),(0,[z1,z2,z3,z4,z708,z5]),(0,[z1,z2,z3,z4,z5,z709]),(0,[z1,z19,z208,z2,z4,z5])],[(0,[z0,z1,z2,z710,z4,z5]),(1,[z1,z2,z711,z4,z5]),(0,[z0,z1,z2,z712,z4,z5]),(0,[z1,z71,z45,z3,z4,z5]),(0,[z0,z1,z114,z54,z4,z5]),(0,[z0,z1,z713,z2,z4,z5]),(0,[z10,z0,z1,z2,z93,z11])],[(0,[z0,z1,z2,z3,z5,z714]),(0,[z1,z715,z2,z3,z4,z5]),(0,[z21,z380,z1,z2,z3,z4]),(0,[z0,z1,z188,z2,z4,z716])],[(0,[z61,z1,z2,z137,z4,z5]),(0,[z717,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z718,z5]),(0,[z0,z1,z2,z124,z439,z5]),(0,[z91,z607,z1,z3,z4,z5]),(0,[z690,z0,z2,z3,z4,z69]),(0,[z43,z0,z45,z3,z4,z125]),(0,[z0,z1,z2,z719,z3,z5]),(0,[z0,z1,z720,z3,z4,z5]),(0,[z0,z1,z261,z370,z4,z5])],[(0,[z1,z2,z356,z3,z4,z5]),(0,[z43,z0,z51,z3,z4,z5]),(0,[z0,z1,z2,z3,z721,z5]),(0,[z0,z1,z63,z54,z4,z5]),(0,[z0,z1,z722,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z723]),(0,[z724,z1,z2,z3,z4,z5]),(0,[z725,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z50,z310,z33]),(0,[z0,z209,z167,z3,z4,z5])],[(0,[z0,z1,z281,z3,z4,z5]),(0,[z0,z1,z3,z726,z4,z5]),(0,[z122,z1,z2,z3,z4,z727])]],
   [[(0,[z0,z1,z2,z728,z4,z5]),(0,[z142,z75,z1,z3,z4,z5]),(0,[z0,z1,z2,z729,z4,z5]),(0,[z27,z0,z678,z2,z4,z5]),(0,[z0,z1,z730,z2,z4,z5]),(0,[z0,z1,z731,z3,z4,z5]),(0,[z21,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z521]),(0,[z49,z1,z2,z111,z4,z5]),(0,[z732,z1,z2,z3,z4,z5]),(0,[z0,z1,z32,z2,z3,z164]),(0,[z0,z1,z2,z93,z4,z69]),(0,[z0,z1,z2,z415,z4,z34])],[(0,[z0,z1,z2,z3,z4,z733]),(0,[z0,z1,z105,z20,z4,z5]),(0,[z1,z2,z3,z4,z734,z5]),(0,[z0,z735,z2,z3,z4,z5]),(0,[z138,z1,z2,z3,z4,z727]),(0,[z1,z2,z3,z4,z5,z727]),(0,[z0,z1,z2,z736,z3,z5]),(0,[z0,z2,z3,z484,z68,z5]),(0,[z0,z1,z152,z3,z4,z278])],[(0,[z27,z0,z1,z105,z4,z5]),(0,[z737,z1,z2,z3,z4,z5]),(0,[z495,z0,z1,z54,z4,z5])],[(0,[z0,z1,z738,z2,z4,z5]),(0,[z1,z241,z20,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z739]),(0,[z740,z1,z2,z3,z4,z5]),(0,[z0,z1,z165,z3,z741,z5])],[(0,[z0,z1,z742,z2,z4,z5]),(0,[z0,z1,z2,z3,z743,z5]),(0,[z0,z1,z19,z63,z4,z5]),(0,[z0,z1,z188,z2,z434,z58])],[(0,[z0,z1,z744,z3,z4,z5]),(0,[z0,z1,z745,z3,z4,z5]),(0,[z0,z1,z2,z266,z4,z125]),(0,[z0,z1,z2,z746,z4,z5]),(0,[z0,z1,z747,z3,z4,z5]),(0,[z0,z148,z2,z111,z4,z5]),(0,[z0,z280,z2,z3,z4,z117]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z46,z225,z3,z278])],[(0,[z0,z1,z749,z3,z4,z5]),(0,[z0,z2,z3,z750,z4,z5]),(0,[z0,z1,z2,z751,z4,z5]),(0,[z0,z1,z2,z3,z4,z73])],[(0,[z1,z281,z20,z3,z4,z5]),(0,[z0,z1,z752,z3,z4,z5]),(0,[z0,z1,z753,z3,z4,z5]),(0,[z142,z1,z131,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z124,z4,z133]),(0,[z0,z1,z754,z3,z4,z5]),(0,[z0,z1,z2,z755,z4,z5]),(0,[z0,z1,z39,z225,z3,z5])],[(0,[z0,z1,z281,z3,z4,z133]),(0,[z21,z0,z1,z2,z3,z164]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z3,z4,z757,z278]),(0,[z0,z1,z32,z2,z57,z4])],[(0,[z0,z1,z2,z200,z4,z5]),(0,[z0,z1,z2,z758,z4,z5]),(0,[z0,z216,z1,z37,z4,z5]),(0,[z27,z0,z2,z53,z344,z5])],[(0,[z0,z1,z2,z3,z4,z759]),(0,[z1,z254,z2,z120,z4,z5]),(0,[z0,z1,z2,z266,z387,z5]),(0,[z0,z1,z760,z3,z4,z5]),(0,[z0,z292,z167,z3,z4,z5])],[(0,[z91,z1,z474,z3,z4,z5]),(0,[z0,z1,z19,z28,z4,z5])],[(0,[z384,z1,z2,z120,z4,z5])],[(0,[z0,z1,z2,z761,z4,z5]),(0,[z101,z1,z2,z85,z4,z5]),(0,[z0,z1,z2,z3,z4,z762]),(0,[z0,z1,z46,z3,z4,z757])],[(0,[z0,z1,z414,z120,z4,z5]),(0,[z0,z1,z763,z2,z3,z4]),(0,[z0,z72,z217,z2,z4,z5]),(0,[z181,z1,z105,z20,z4,z5]),(0,[z764,z1,z2,z3,z4,z5])]],
   [[(0,[z226,z1,z2,z120,z4,z5]),(0,[z0,z1,z2,z3,z765,z5]),(0,[z0,z1,z2,z3,z4,z766]),(0,[z142,z0,z1,z137,z4,z5]),(0,[z0,z1,z77,z105,z4,z5]),(0,[z247,z1,z2,z266,z4,z5]),(0,[z0,z1,z2,z767,z3,z5])],[(0,[z0,z1,z2,z3,z768,z5]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z225,z2,z3,z5]),(0,[z0,z1,z32,z2,z50,z3])],[(0,[z0,z191,z2,z3,z4,z117]),(0,[z0,z1,z32,z2,z3,z68])],[(0,[z0,z1,z37,z154,z4,z5]),(0,[z0,z1,z2,z770,z4,z5]),(0,[z0,z209,z2,z93,z4,z5])],[(0,[z0,z1,z771,z3,z4,z5]),(0,[z772,z1,z2,z3,z4,z5]),(0,[z0,z292,z261,z3,z4,z5])],[(0,[z142,z1,z254,z3,z4,z5]),(0,[z0,z1,z32,z2,z93,z4]),(0,[z0,z1,z115,z2,z773,z5])],[(0,[z0,z1,z2,z3,z439,z416]),(0,[z75,z239,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z774,z5]),(0,[z775,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z776,z4,z5]),(0,[z0,z2,z3,z4,z5,z777]),(0,[z0,z1,z167,z3,z4,z5])],[(0,[z94,z182,z177,z2,z4,z5]),(0,[z0,z1,z778,z3,z4,z5]),(0,[z91,z1,z78,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z779]),(0,[z10,z0,z292,z2,z3,z11])]],
   [[(0,[z780,z177,z2,z3,z4,z5]),(0,[z43,z0,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z781,z5]),(0,[z782,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z783])],[(0,[z0,z1,z45,z345,z4,z5]),(0,[z406,z1,z52,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z784]),(0,[z0,z1,z2,z3,z4,z237]),(0,[z0,z785,z2,z3,z4,z5])],[(0,[z579,z1,z78,z3,z4,z5]),(0,[z142,z1,z76,z3,z4,z5]),(0,[z0,z1,z2,z786,z4,z5]),(0,[z129,z380,z1,z2,z3,z5]),(0,[z0,z1,z2,z4,z787,z5]),(0,[z176,z0,z2,z3,z4,z777])],[(0,[z21,z0,z1,z2,z3,z68]),(0,[z0,z1,z788,z3,z4,z5]),(0,[z0,z1,z2,z35,z93,z5])],[(0,[z142,z1,z52,z3,z4,z5]),(0,[z0,z1,z789,z3,z4,z5]),(0,[z0,z1,z2,z790,z4,z5])],[(0,[z0,z1,z791,z3,z4,z5]),(0,[z0,z1,z792,z3,z4,z5])],[(0,[z0,z1,z2,z3,z793,z5]),(0,[z1,z2,z3,z734,z223,z5]),(0,[z62,z1,z44,z2,z4,z5]),(0,[z0,z1,z3,z794,z4,z5])],[(0,[z0,z1,z2,z455,z4,z416]),(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z2,z3,z4,z796]),(0,[z1,z2,z711,z3,z4,z5]),(0,[z797,z0,z1,z2,z4,z5]),(0,[z0,z1,z261,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z11])]],
   [[(0,[z0,z1,z2,z124,z95,z5]),(0,[z0,z1,z2,z3,z4,z798]),(0,[z140,z1,z78,z3,z4,z5]),(0,[z0,z1,z2,z799,z4,z5]),(0,[z194,z1,z2,z3,z734,z5]),(0,[z0,z1,z2,z3,z800,z5]),(0,[z0,z1,z3,z4,z5,z801]),(0,[z0,z498,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z802,z5]),(0,[z0,z803,z2,z3,z4,z5]),(0,[z10,z0,z209,z2,z3,z11]),(0,[z0,z292,z2,z93,z4,z5])],[(0,[z0,z780,z2,z3,z4,z5]),(0,[z804,z0,z1,z3,z4,z5]),(0,[z1,z2,z3,z4,z116,z727]),(0,[z805,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z271,z5])],[(0,[z94,z75,z1,z3,z4,z5]),(0,[z314,z177,z2,z3,z4,z5]),(0,[z1,z177,z2,z85,z4,z5]),(0,[z0,z1,z2,z806,z4,z5]),(0,[z0,z1,z2,z3,z807,z5])],[(0,[z1,z52,z2,z455,z4,z5]),(0,[z0,z1,z182,z255,z4,z5]),(0,[z61,z1,z2,z266,z4,z5]),(0,[z0,z1,z77,z137,z4,z5]),(0,[z62,z1,z19,z3,z4,z5]),(0,[z0,z292,z2,z3,z4,z305])],[(0,[z0,z1,z808,z3,z4,z5]),(0,[z27,z479,z2,z53,z4,z5])],[(0,[z119,z1,z2,z455,z4,z5]),(0,[z0,z1,z809,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z42]),(0,[z129,z0,z1,z2,z3,z117]),(0,[z0,z1,z28,z3,z4,z237]),(0,[z0,z1,z2,z3,z810,z5])],[(0,[z49,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z811,z4,z5]),(0,[z0,z1,z812,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z813])],[(0,[z0,z1,z2,z3,z814,z5]),(0,[z1,z52,z241,z3,z4,z5]),(0,[z0,z263,z588,z3,z4,z5]),(0,[z27,z0,z414,z53,z4,z5]),(0,[z0,z1,z815,z2,z3,z4]),(0,[z1,z19,z77,z208,z4,z5]),(0,[z10,z551,z1,z2,z3,z11])]],
   [[(0,[z21,z1,z2,z3,z4,z206]),(0,[z0,z1,z3,z4,z5,z816]),(0,[z817,z1,z2,z3,z4,z5])],[(0,[z0,z1,z818,z3,z4,z5]),(0,[z0,z1,z819,z3,z4,z5]),(0,[z0,z1,z820,z2,z3,z4]),(0,[z142,z247,z1,z3,z4,z5]),(0,[z119,z1,z241,z3,z4,z5]),(0,[z0,z1,z46,z3,z277,z278]),(0,[z0,z1,z2,z35,z57,z3])],[(0,[z0,z1,z2,z821,z4,z5]),(0,[z0,z1,z2,z3,z348,z125]),(0,[z479,z1,z414,z3,z4,z5]),(0,[z0,z1,z569,z3,z231,z5]),(1,[z0,z1,z3,z741,z5]),(0,[z0,z1,z2,z198,z773,z5])],[(0,[z0,z1,z2,z822,z4,z5]),(0,[z1,z823,z2,z3,z4,z5]),(0,[z27,z0,z423,z53,z4,z5]),(0,[z0,z1,z3,z824,z4,z5]),(0,[z0,z1,z2,z93,z4,z5])],[(0,[z825,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z826,z4,z5]),(0,[z10,z0,z1,z2,z3,z510])],[(0,[z43,z62,z1,z3,z4,z5]),(0,[z0,z1,z28,z3,z271,z5]),(0,[z827,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z305,z69]),(0,[z295,z0,z2,z3,z4,z69])],[(0,[z0,z1,z2,z85,z4,z5]),(0,[z0,z1,z77,z254,z4,z5]),(0,[z181,z0,z1,z154,z4,z5]),(0,[z0,z1,z828,z3,z4,z5]),(0,[z27,z0,z436,z53,z4,z5]),(0,[z479,z1,z423,z3,z4,z5]),(0,[z0,z1,z829,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z305]),(0,[z0,z1,z830,z3,z4,z5]),(0,[z0,z1,z2,z773,z33,z5]),(0,[z0,z1,z2,z3,z5,z831])],[(0,[z0,z1,z832,z3,z4,z5]),(0,[z247,z1,z45,z3,z4,z5]),(0,[z247,z1,z2,z3,z4,z283]),(0,[z0,z1,z833,z3,z4,z5]),(0,[z0,z1,z2,z834,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z835]),(0,[z0,z1,z2,z3,z4,z836]),(0,[z0,z1,z19,z77,z4,z5])],[(0,[z94,z255,z177,z3,z4,z5]),(0,[z0,z1,z19,z369,z4,z5]),(0,[z161,z1,z2,z3,z162,z5]),(0,[z207,z1,z2,z3,z223,z5]),(0,[z837,z1,z2,z3,z4,z5]),(0,[z0,z25,z838,z3,z4,z5]),(0,[z10,z0,z1,z497,z2,z3]),(0,[z0,z1,z39,z3,z741,z5]),(0,[z0,z1,z2,z3,z831,z11])],[(0,[z94,z177,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z839,z5]),(0,[z840,z1,z2,z3,z4,z5]),(0,[z10,z0,z1,z2,z685,z3])],[(0,[z0,z1,z2,z3,z841,z5]),(0,[z491,z0,z2,z3,z4,z69]),(0,[z380,z1,z167,z3,z4,z5])],[(0,[z94,z177,z222,z3,z4,z5]),(0,[z0,z1,z255,z3,z4,z5]),(0,[z1,z2,z20,z630,z4,z5]),(0,[z0,z1,z2,z93,z68,z5]),(0,[z0,z842,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z843]),(0,[z0,z1,z2,z3,z844,z5]),(0,[z247,z1,z2,z3,z348,z5]),(0,[z0,z1,z713,z37,z4,z5]),(0,[z0,z1,z2,z3,z4,z845])],[(0,[z0,z1,z2,z846,z4,z5]),(0,[z0,z1,z78,z200,z4,z5])],[(0,[z0,z1,z37,z81,z4,z5]),(0,[z129,z0,z1,z2,z3,z69]),(0,[z0,z1,z2,z3,z68,z305]),(0,[z0,z1,z167,z370,z4,z5])]],
   [[(0,[z181,z1,z2,z711,z4,z5]),(0,[z0,z284,z2,z3,z164,z192]),(0,[z847,z1,z2,z3,z4,z5]),(0,[z0,z1,z19,z713,z4,z5]),(0,[z0,z1,z188,z2,z35,z3])],[(0,[z0,z1,z2,z3,z4,z848])],[(0,[z0,z1,z2,z3,z849,z5]),(0,[z94,z1,z542,z2,z4,z5]),(0,[z1,z52,z850,z3,z4,z5]),(0,[z122,z1,z2,z3,z4,z695]),(0,[z407,z72,z1,z2,z4,z5]),(0,[z0,z1,z32,z2,z3,z4]),(0,[z851,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z716]),(0,[z0,z1,z2,z4,z34,z716])],[(0,[z314,z0,z45,z3,z4,z5]),(0,[z0,z1,z852,z3,z4,z5]),(1,[z0,z2,z3,z853,z5]),(0,[z140,z1,z19,z77,z4,z5])],[(0,[z479,z1,z2,z455,z4,z5]),(0,[z94,z177,z2,z3,z4,z133]),(0,[z0,z1,z474,z77,z4,z5]),(0,[z0,z1,z2,z3,z4,z854]),(0,[z0,z1,z44,z2,z4,z5]),(0,[z0,z72,z2,z111,z4,z5]),(0,[z380,z1,z261,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z831])],[(0,[z94,z226,z177,z2,z4,z5]),(0,[z94,z1,z168,z3,z4,z5]),(0,[z142,z1,z52,z200,z4,z5]),(0,[z0,z1,z855,z3,z4,z5]),(0,[z0,z1,z37,z137,z4,z5]),(0,[z0,z1,z31,z3,z4,z634]),(0,[z0,z1,z2,z3,z4,z831])],[(0,[z181,z226,z1,z2,z4,z5]),(0,[z0,z1,z200,z154,z4,z5]),(0,[z247,z1,z2,z3,z387,z5]),(0,[z0,z1,z2,z3,z4,z777])],[(0,[z0,z1,z2,z856,z4,z5]),(0,[z0,z1,z2,z3,z4,z283]),(0,[z857,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z858,z5]),(0,[z0,z1,z859,z3,z4,z5])]],
   [[(0,[z1,z860,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z861]),(0,[z194,z380,z1,z2,z3,z5]),(0,[z1,z862,z2,z3,z4,z5]),(0,[z1,z863,z2,z3,z4,z5]),(0,[z0,z1,z2,z35,z3,z5]),(0,[z10,z0,z1,z268,z2,z3])],[(0,[z0,z1,z2,z124,z4,z5]),(0,[z0,z1,z2,z3,z864,z5]),(0,[z0,z1,z2,z3,z865,z5]),(0,[z0,z1,z2,z3,z4,z866]),(0,[z0,z1,z2,z867,z4,z5]),(0,[z0,z1,z2,z3,z235,z189]),(0,[z0,z1,z2,z3,z47,z328])],[(0,[z1,z2,z3,z156,z4,z5]),(0,[z0,z1,z2,z4,z868,z5]),(0,[z0,z1,z2,z3,z869,z5]),(0,[z61,z1,z2,z3,z4,z283]),(0,[z0,z1,z870,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z458])],[(0,[z0,z1,z222,z124,z4,z5]),(0,[z129,z138,z1,z2,z3,z206]),(0,[z0,z1,z871,z3,z4,z5])],[(0,[z0,z1,z2,z3,z872,z5]),(0,[z101,z780,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z873]),(0,[z0,z1,z25,z137,z4,z5]),(0,[z1,z874,z2,z3,z4,z5])],[(0,[z0,z1,z63,z78,z4,z5]),(0,[z0,z1,z2,z3,z348,z5]),(0,[z1,z2,z3,z875,z4,z5]),(0,[z551,z1,z167,z3,z4,z5])],[(0,[z10,z0,z1,z2,z3,z419]),(0,[z62,z1,z63,z2,z4,z5])],[(0,[z0,z1,z3,z876,z4,z5]),(0,[z0,z1,z2,z877,z4,z5]),(0,[z0,z1,z2,z3,z853,z5]),(0,[z0,z1,z2,z3,z4,z878])]],
   [[(0,[z94,z177,z281,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z879]),(0,[z142,z1,z850,z3,z4,z5]),(0,[z61,z1,z2,z3,z348,z5]),(0,[z0,z1,z28,z3,z344,z5]),(0,[z479,z72,z1,z2,z4,z5]),(0,[z140,z1,z3,z54,z4,z5]),(0,[z380,z1,z2,z93,z4,z5])],[(0,[z0,z72,z1,z105,z4,z5]),(0,[z0,z880,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z727,z206]),(0,[z0,z1,z2,z3,z4,z192])],[(0,[z1,z264,z52,z3,z4,z5]),(0,[z194,z1,z2,z3,z223,z5]),(0,[z0,z1,z2,z3,z344,z6]),(0,[z881,z1,z2,z3,z4,z5])],[(0,[z0,z1,z882,z3,z4,z5]),(0,[z883,z1,z2,z3,z4,z5]),(0,[z10,z600,z0,z1,z2,z3])],[(0,[z91,z0,z1,z137,z4,z5]),(0,[z0,z1,z2,z3,z4,z884]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z140,z1,z19,z3,z4,z5]),(0,[z0,z1,z2,z3,z741,z5]),(0,[z886,z1,z2,z3,z4,z5])],[],[(0,[z138,z1,z2,z3,z4,z206]),(0,[z0,z1,z28,z53,z4,z5]),(0,[z551,z1,z261,z3,z4,z5])],[(0,[z0,z1,z2,z887,z4,z5]),(0,[z181,z1,z144,z2,z4,z5]),(0,[z0,z1,z111,z154,z4,z5]),(0,[z888,z1,z2,z3,z4,z5]),(0,[z0,z1,z115,z2,z93,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z889]),(0,[z0,z1,z2,z3,z734,z5]),(0,[z0,z440,z2,z3,z164,z5]),(0,[z0,z1,z2,z3,z890,z5]),(0,[z0,z1,z2,z4,z5,z891]),(0,[z0,z892,z2,z3,z4,z5])],[(0,[z239,z780,z2,z3,z4,z5]),(0,[z0,z1,z152,z2,z3,z164]),(0,[z0,z1,z2,z893,z4,z5]),(0,[z10,z519,z0,z1,z2,z3])],[(1,[z1,z850,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z706]),(0,[z10,z0,z1,z2,z370,z11]),(0,[z0,z1,z2,z3,z47,z831])],[(0,[z129,z161,z1,z2,z3,z5]),(0,[z1,z2,z3,z894,z4,z5]),(0,[z26,z1,z2,z3,z4,z237])],[(0,[z94,z177,z2,z3,z95,z5]),(0,[z142,z0,z1,z345,z4,z5]),(0,[z0,z2,z3,z4,z777,z69])],[(0,[z75,z247,z1,z3,z4,z5]),(0,[z27,z26,z2,z53,z4,z5]),(0,[z1,z895,z2,z3,z4,z5])],[(0,[z43,z61,z45,z3,z4,z5]),(0,[z49,z1,z2,z3,z4,z237]),(0,[z0,z1,z2,z3,z484,z117]),(1,[z0,z1,z2,z3,z831])],[(0,[z0,z1,z281,z124,z4,z5]),(0,[z0,z1,z2,z896,z4,z5]),(0,[z0,z1,z2,z3,z4,z897]),(0,[z0,z1,z2,z898,z4,z5]),(0,[z0,z578,z2,z3,z164,z5]),(0,[z176,z0,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z773,z5]),(0,[z0,z1,z899,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z900,z4,z5]),(0,[z0,z1,z901,z3,z4,z5])],[(0,[z0,z1,z902,z3,z4,z5]),(0,[z21,z161,z0,z1,z2,z3]),(0,[z0,z1,z165,z261,z3,z5])],[(0,[z0,z1,z2,z3,z4,z416]),(0,[z0,z1,z903,z3,z4,z5]),(0,[z0,z1,z904,z3,z4,z5]),(0,[z0,z1,z152,z165,z2,z3]),(0,[z551,z1,z2,z93,z4,z5])],[(0,[z142,z1,z542,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z26,z1,z2,z3,z271,z5]),(0,[z380,z1,z2,z3,z164,z5]),(0,[z0,z149,z2,z3,z4,z117])],[(0,[z0,z1,z222,z3,z4,z416]),(0,[z226,z0,z1,z2,z4,z5]),(0,[z181,z1,z2,z517,z4,z5]),(0,[z0,z1,z77,z294,z4,z5]),(0,[z0,z263,z838,z3,z4,z5]),(0,[z1,z906,z2,z3,z4,z5]),(0,[z907,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z908,z5]),(0,[z0,z1,z302,z3,z74,z5]),(0,[z0,z1,z2,z50,z773,z5]),(0,[z0,z1,z32,z2,z4,z58])],[(0,[z101,z239,z2,z3,z4,z5])],[(0,[z142,z1,z168,z3,z4,z5]),(0,[z49,z1,z2,z3,z271,z5]),(0,[z0,z1,z2,z3,z5,z909]),(0,[z10,z0,z2,z3,z68,z69]),(0,[z0,z910,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z47,z189])],[(0,[z0,z1,z2,z3,z4,z727]),(0,[z0,z2,z838,z3,z4,z5]),(0,[z0,z1,z2,z57,z4,z640])]],
   [[(0,[z0,z1,z911,z3,z4,z5]),(0,[z0,z1,z2,z3,z189,z353]),(0,[z0,z1,z912,z2,z3,z5]),(0,[z0,z284,z2,z3,z164,z305]),(0,[z913,z1,z2,z3,z4,z5])],[(0,[z0,z1,z914,z3,z4,z5]),(0,[z915,z0,z1,z2,z3,z5]),(0,[z1,z71,z2,z3,z4,z5]),(0,[z142,z1,z52,z85,z4,z5]),(0,[z916,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z917,z5]),(0,[z0,z1,z918,z2,z3,z5]),(0,[z0,z1,z414,z54,z4,z5]),(0,[z0,z1,z3,z4,z5,z919]),(0,[z0,z1,z39,z3,z231,z5]),(0,[z0,z1,z188,z2,z93,z4])],[(0,[z101,z413,z2,z3,z4,z5]),(0,[z0,z1,z19,z200,z4,z5]),(0,[z129,z0,z1,z2,z3,z5]),(0,[z62,z1,z3,z54,z4,z5]),(0,[z0,z1,z2,z3,z920,z5])],[(0,[z0,z1,z105,z120,z4,z5]),(0,[z0,z1,z2,z266,z4,z5]),(0,[z43,z0,z838,z3,z4,z5]),(0,[z0,z1,z152,z2,z3,z68]),(0,[z0,z127,z2,z3,z4,z305])],[(0,[z0,z1,z3,z4,z5,z921]),(0,[z0,z1,z63,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z922]),(0,[z0,z923,z2,z3,z4,z5])],[(0,[z1,z2,z20,z455,z4,z5]),(0,[z91,z247,z1,z3,z4,z5]),(0,[z181,z1,z208,z2,z4,z5]),(0,[z0,z1,z2,z50,z33,z5])],[(0,[z0,z1,z2,z3,z924,z5]),(0,[z0,z1,z925,z3,z4,z5]),(0,[z0,z1,z2,z926,z4,z5]),(0,[z927,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z189,z366]),(0,[z0,z1,z31,z3,z4,z757])],[(0,[z0,z1,z2,z3,z928,z5]),(0,[z0,z1,z77,z345,z4,z5]),(0,[z129,z1,z2,z3,z223,z5]),(0,[z0,z1,z2,z929,z4,z5])]],
   [[(0,[z129,z122,z0,z1,z2,z3]),(0,[z0,z263,z1,z63,z4,z5]),(0,[z930,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z484,z69])],[(0,[z407,z1,z2,z3,z4,z5]),(0,[z1,z414,z3,z156,z4,z5])],[(0,[z0,z1,z2,z455,z439,z5]),(0,[z119,z1,z2,z81,z4,z5]),(0,[z0,z1,z19,z154,z4,z5]),(0,[z309,z1,z2,z3,z162,z5]),(0,[z0,z1,z2,z931,z4,z5])],[(0,[z43,z0,z45,z137,z4,z5]),(0,[z0,z1,z2,z932,z4,z5]),(0,[z1,z423,z3,z156,z4,z5]),(0,[z933,z1,z2,z3,z4,z5]),(0,[z0,z1,z115,z2,z539,z5]),(0,[z0,z1,z2,z4,z5,z716])],[(0,[z0,z1,z2,z3,z4,z934]),(0,[z935,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z936]),(0,[z0,z209,z2,z370,z4,z5])],[(0,[z0,z1,z2,z3,z937,z5]),(0,[z0,z1,z2,z4,z938,z5]),(0,[z181,z1,z2,z675,z4,z5]),(0,[z0,z1,z939,z3,z4,z5]),(0,[z0,z1,z2,z711,z4,z5]),(0,[z0,z1,z2,z940,z4,z5]),(0,[z0,z1,z2,z941,z4,z5]),(0,[z140,z263,z1,z3,z4,z5]),(0,[z10,z0,z1,z2,z3,z548])],[(0,[z0,z1,z942,z3,z4,z5]),(0,[z0,z1,z943,z3,z4,z5]),(0,[z0,z1,z436,z3,z4,z6]),(0,[z0,z1,z379,z2,z198,z5]),(0,[z944,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z277])],[(0,[z0,z1,z2,z945,z4,z5]),(0,[z24,z177,z2,z3,z4,z5]),(0,[z43,z0,z1,z63,z4,z5])]],
   [[(0,[z0,z1,z281,z3,z4,z416]),(0,[z43,z356,z45,z3,z4,z5]),(0,[z0,z1,z165,z3,z74,z5])],[(0,[z1,z780,z2,z3,z4,z5]),(0,[z1,z2,z946,z3,z4,z5]),(0,[z0,z1,z2,z3,z947,z5]),(0,[z0,z1,z2,z3,z5,z948]),(0,[z0,z1,z2,z3,z4,z949]),(0,[z0,z1,z2,z3,z5,z950]),(0,[z407,z1,z2,z54,z4,z5])],[(0,[z0,z1,z2,z3,z951,z5]),(0,[z1,z2,z3,z4,z952,z5])],[(0,[z0,z1,z953,z3,z4,z5]),(0,[z0,z127,z2,z3,z4,z777]),(0,[z1,z954,z2,z3,z4,z5])],[(0,[z1,z52,z281,z3,z4,z5]),(0,[z27,z0,z2,z53,z4,z5]),(0,[z10,z0,z1,z2,z3,z563])],[(0,[z0,z1,z19,z264,z4,z5]),(0,[z0,z1,z2,z955,z4,z5]),(0,[z956,z1,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z777])],[(0,[z119,z1,z281,z3,z4,z5]),(0,[z0,z1,z957,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z958]),(0,[z1,z542,z2,z78,z4,z5]),(0,[z0,z959,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z387,z125]),(0,[z26,z1,z2,z3,z344,z5]),(0,[z0,z292,z2,z3,z164,z5]),(0,[z1,z208,z37,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z310])],[(0,[z479,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z960,z4,z5]),(0,[z0,z1,z961,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z962])]],
   [[(0,[z446,z0,z2,z3,z68,z5])],[(0,[z0,z1,z2,z3,z963,z5]),(0,[z0,z1,z964,z2,z4,z5]),(0,[z0,z1,z2,z965,z4,z5]),(0,[z49,z1,z2,z3,z344,z5])],[(0,[z0,z1,z2,z3,z4,z966]),(0,[z0,z1,z2,z967,z4,z5]),(0,[z407,z1,z2,z20,z4,z5])],[(0,[z0,z1,z968,z2,z4,z5]),(0,[z62,z1,z52,z3,z4,z5]),(0,[z0,z1,z969,z3,z4,z5]),(0,[z247,z1,z2,z3,z4,z125]),(0,[z27,z0,z1,z414,z4,z5])],[(0,[z0,z1,z2,z3,z95,z416]),(0,[z0,z1,z2,z970,z4,z5]),(0,[z0,z1,z2,z971,z4,z5]),(0,[z119,z0,z1,z28,z4,z5]),(0,[z0,z1,z2,z3,z5,z972]),(0,[z0,z1,z973,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z974]),(0,[z0,z1,z2,z975,z4,z5]),(0,[z0,z1,z2,z976,z4,z5]),(0,[z1,z168,z3,z120,z4,z5]),(0,[z10,z0,z1,z2,z3,z584]),(0,[z0,z1,z28,z3,z4,z6])],[(0,[z0,z1,z977,z3,z4,z5]),(0,[z0,z978,z2,z3,z4,z5]),(0,[z10,z0,z1,z39,z31,z3])],[(0,[z0,z1,z979,z3,z4,z5]),(0,[z122,z1,z2,z3,z4,z116]),(0,[z0,z1,z2,z3,z344,z5]),(0,[z479,z1,z2,z54,z4,z5]),(0,[z10,z0,z1,z2,z3,z587]),(0,[z0,z1,z3,z4,z56,z757])]],
   [[(0,[z0,z1,z2,z345,z4,z5]),(0,[z27,z0,z28,z53,z4,z5]),(0,[z0,z1,z980,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z981])],[(0,[z0,z1,z3,z982,z4,z5]),(0,[z490,z0,z1,z54,z4,z5]),(0,[z0,z1,z2,z3,z4,z983]),(0,[z0,z127,z2,z3,z179,z117]),(0,[z0,z1,z3,z231,z741,z5])],[(0,[z0,z1,z2,z3,z984,z5]),(0,[z0,z1,z2,z3,z4,z985]),(0,[z27,z0,z2,z53,z4,z6]),(0,[z0,z1,z152,z39,z2,z3])],[(0,[z0,z1,z2,z986,z4,z5]),(0,[z0,z1,z2,z3,z987,z5]),(0,[z988,z1,z2,z3,z4,z5]),(0,[z1,z44,z2,z356,z4,z5]),(0,[z0,z1,z666,z3,z4,z278]),(0,[z989,z1,z2,z3,z4,z5])],[(0,[z91,z1,z3,z81,z4,z5]),(0,[z43,z247,z45,z3,z4,z5])],[(0,[z0,z1,z2,z3,z990,z5]),(0,[z0,z1,z991,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z992]),(0,[z389,z0,z2,z3,z68,z5]),(0,[z0,z1,z993,z2,z3,z4])],[(0,[z0,z1,z2,z994,z4,z5]),(0,[z0,z1,z2,z3,z4,z995]),(0,[z996,z1,z2,z3,z4,z5]),(0,[z175,z0,z2,z3,z853,z5]),(0,[z380,z1,z2,z3,z4,z117]),(0,[z0,z1,z2,z3,z4,z997]),(1,[z0,z1,z2,z4,z716]),(0,[z0,z1,z2,z3,z189,z831])],[(0,[z0,z1,z182,z2,z4,z5]),(0,[z1,z850,z2,z3,z4,z5]),(0,[z1,z37,z78,z20,z4,z5]),(0,[z0,z1,z105,z345,z4,z5]),(0,[z119,z49,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z998]),(0,[z62,z263,z1,z3,z4,z5]),(0,[z483,z0,z2,z3,z68,z5]),(0,[z0,z1,z338,z2,z4,z58]),(0,[z0,z1,z39,z261,z3,z5])]],
   [[(0,[z999,z0,z1,z2,z3,z4]),(0,[z479,z1,z2,z20,z4,z5]),(0,[z0,z1,z1000,z2,z3,z4]),(0,[z0,z1,z1001,z2,z3,z4]),(0,[z0,z292,z2,z3,z484,z5]),(0,[z0,z1,z46,z3,z4,z278]),(0,[z0,z1,z225,z31,z2,z3])],[(0,[z0,z1,z2,z1002,z4,z5]),(0,[z226,z239,z1,z2,z4,z5]),(0,[z27,z2,z156,z53,z4,z5]),(0,[z0,z1,z77,z414,z4,z5]),(0,[z1003,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1004,z5]),(0,[z94,z177,z2,z124,z4,z5]),(0,[z94,z75,z177,z3,z4,z5]),(0,[z1,z51,z78,z3,z4,z5]),(0,[z142,z1,z71,z3,z4,z5]),(0,[z0,z1,z2,z3,z1005,z5]),(0,[z0,z1,z2,z3,z1006,z5]),(0,[z0,z2,z3,z164,z853,z5]),(0,[z0,z1,z2,z3,z1007,z5])],[(0,[z181,z75,z1,z3,z4,z5]),(0,[z0,z1,z1008,z2,z4,z5]),(0,[z24,z0,z2,z53,z4,z5]),(0,[z0,z1,z2,z3,z4,z125]),(0,[z0,z127,z2,z3,z484,z117]),(0,[z0,z1,z2,z3,z1009,z5]),(0,[z1,z71,z77,z3,z4,z5]),(0,[z0,z1,z152,z2,z3,z4]),(0,[z0,z1010,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1011]),(0,[z0,z1,z1012,z3,z4,z5]),(0,[z0,z400,z25,z3,z4,z5]),(0,[z0,z1,z713,z3,z4,z5])],[(0,[z0,z1,z2,z455,z95,z5]),(0,[z0,z1,z2,z3,z1013,z5])],[(0,[z101,z1,z2,z455,z4,z5]),(0,[z181,z1,z241,z20,z4,z5]),(0,[z61,z1,z2,z3,z4,z125]),(0,[z0,z209,z2,z3,z4,z5]),(0,[z1,z1014,z2,z3,z4,z5])],[(0,[z0,z1,z225,z261,z3,z5])]],
   [[(0,[z0,z1,z46,z261,z3,z4])],[(0,[z0,z1,z2,z3,z1015,z5]),(0,[z0,z1,z2,z3,z4,z1016]),(0,[z0,z1,z2,z3,z387,z5]),(0,[z27,z0,z2,z750,z4,z5])],[(0,[z101,z1,z241,z3,z4,z5]),(0,[z1,z2,z711,z120,z4,z5]),(0,[z194,z21,z0,z1,z2,z3]),(0,[z0,z1,z45,z137,z4,z5]),(0,[z0,z1,z2,z137,z4,z283]),(0,[z0,z1,z2,z3,z4,z1017]),(0,[z43,z0,z45,z266,z4,z5]),(0,[z27,z0,z114,z2,z4,z5])],[(0,[z1018,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z484,z5]),(0,[z229,z0,z1,z37,z4,z5]),(0,[z1019,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1020,z2,z4,z5]),(0,[z0,z1,z2,z1021,z4,z5]),(0,[z61,z1,z2,z3,z387,z5]),(0,[z0,z1,z2,z3,z271,z237]),(0,[z0,z1,z713,z54,z4,z5]),(0,[z0,z1,z2,z3,z1022,z5])],[(0,[z0,z1,z542,z2,z4,z5]),(0,[z49,z1,z37,z2,z4,z5])],[(0,[z247,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1023]),(0,[z0,z1,z1024,z3,z4,z5]),(1,[z0,z2,z750,z4,z5]),(0,[z0,z1,z1025,z3,z4,z5]),(0,[z0,z2,z3,z853,z68,z5]),(0,[z1026,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z50,z93,z5])],[(0,[z490,z1,z78,z3,z4,z5]),(0,[z0,z1,z1027,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z1028])]],
   [[(0,[z0,z1,z168,z3,z4,z5]),(0,[z0,z1,z2,z137,z348,z5]),(0,[z1,z2,z3,z4,z1029,z5]),(0,[z1030,z1,z2,z3,z4,z5]),(0,[z380,z1,z2,z3,z4,z69]),(0,[z1,z19,z71,z77,z4,z5])],[(0,[z1,z168,z71,z3,z4,z5]),(0,[z43,z62,z45,z3,z4,z5]),(0,[z229,z0,z45,z3,z4,z5])],[(0,[z0,z1,z1031,z2,z3,z5]),(0,[z26,z1,z436,z3,z4,z5])],[(0,[z0,z1,z2,z3,z5,z1032]),(0,[z0,z1,z2,z3,z5,z434]),(0,[z0,z1,z167,z93,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1033]),(0,[z495,z1,z52,z3,z4,z5]),(0,[z0,z1,z414,z3,z4,z5]),(0,[z1034,z1,z2,z3,z4,z5]),(0,[z0,z1,z32,z2,z50,z33])],[(0,[z0,z1,z2,z3,z4,z1035]),(0,[z0,z1,z53,z154,z4,z5]),(0,[z49,z1,z436,z3,z4,z5]),(0,[z27,z479,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z5,z1036]),(0,[z0,z1,z3,z741,z4,z5]),(0,[z10,z0,z1,z261,z3,z11])],[(0,[z0,z351,z2,z111,z4,z5]),(0,[z0,z1,z2,z1037,z4,z5]),(0,[z1038,z1,z2,z3,z4,z5]),(0,[z0,z284,z2,z3,z853,z5]),(0,[z0,z127,z2,z3,z4,z117]),(0,[z0,z1,z115,z2,z198,z5])],[(0,[z94,z678,z2,z3,z4,z5]),(0,[z1039,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z1040,z4,z5]),(0,[z0,z1,z1041,z3,z4,z5]),(0,[z0,z1,z423,z3,z4,z5])],[(0,[z0,z1,z3,z154,z4,z5]),(0,[z0,z292,z2,z3,z4,z117])],[(0,[z1,z177,z2,z455,z4,z5]),(0,[z1042,z0,z2,z3,z4,z5]),(0,[z1,z2,z20,z85,z4,z5]),(0,[z0,z1,z2,z750,z4,z5]),(0,[z0,z1,z46,z225,z2,z3])],[(0,[z94,z177,z2,z3,z4,z416]),(0,[z1,z52,z2,z85,z4,z5]),(0,[z142,z1,z3,z517,z4,z5]),(0,[z181,z1,z542,z2,z4,z5]),(0,[z0,z1,z436,z3,z4,z5]),(0,[z1,z208,z2,z53,z4,z5]),(0,[z0,z1,z372,z3,z4,z56]),(0,[z0,z1,z1043,z2,z3,z5]),(0,[z0,z1,z2,z3,z1044,z5])],[(0,[z181,z1,z2,z369,z4,z5]),(0,[z140,z1,z52,z3,z4,z5]),(0,[z0,z838,z45,z3,z4,z5]),(0,[z0,z292,z2,z3,z68,z5]),(0,[z0,z1,z261,z93,z4,z5])],[(0,[z0,z1,z2,z3,z439,z5]),(0,[z1045,z0,z1,z2,z4,z5]),(0,[z119,z1,z2,z85,z4,z5]),(0,[z1,z71,z37,z3,z4,z5]),(0,[z0,z1,z152,z31,z3,z4]),(0,[z0,z1,z115,z2,z5,z438])],[(0,[z1,z177,z241,z3,z4,z5]),(0,[z314,z91,z1,z3,z4,z5]),(0,[z181,z1,z168,z3,z4,z5]),(0,[z0,z1,z1046,z2,z3,z4]),(0,[z0,z1,z225,z3,z74,z5]),(0,[z0,z1,z31,z3,z4,z56])],[(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z1,z222,z3,z439,z5]),(0,[z1,z168,z78,z3,z4,z5]),(0,[z0,z1,z2,z1048,z4,z5]),(0,[z194,z21,z1,z2,z3,z223]),(0,[z0,z1,z2,z3,z4,z1049]),(0,[z1050,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1051,z5]),(0,[z10,z0,z1,z2,z3,z681]),(0,[z0,z1,z2,z35,z33,z5])]],
   [[(0,[z1,z2,z3,z162,z734,z5]),(0,[z0,z1,z2,z3,z4,z1052]),(0,[z0,z1,z188,z2,z4,z58])],[(0,[z49,z1,z19,z2,z4,z5])],[(0,[z1053,z0,z1,z3,z4,z5]),(0,[z24,z119,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z1054,z5]),(0,[z10,z0,z1,z2,z3,z691])],[(0,[z0,z1,z1055,z3,z4,z5]),(0,[z0,z1,z2,z1056,z4,z5]),(0,[z26,z1,z2,z3,z4,z6]),(0,[z0,z1,z165,z3,z73,z74]),(0,[z380,z209,z2,z3,z4,z5])],[(0,[z0,z1,z414,z137,z4,z5]),(0,[z0,z1,z196,z54,z4,z5]),(0,[z1,z71,z25,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1057]),(0,[z0,z1,z2,z1058,z4,z5]),(0,[z248,z0,z2,z3,z4,z69]),(0,[z0,z1,z2,z3,z4,z1059])],[(0,[z0,z1,z2,z1060,z4,z5]),(0,[z0,z1,z414,z20,z4,z5]),(0,[z0,z1,z32,z115,z2,z3])],[(0,[z0,z1,z2,z455,z4,z5]),(0,[z0,z1,z2,z3,z1061,z5]),(0,[z407,z1,z2,z85,z4,z5]),(0,[z0,z1,z2,z1062,z4,z5])],[(0,[z0,z1,z2,z3,z439,z133]),(0,[z0,z1,z2,z3,z344,z237])]],
   [[(0,[z0,z1,z222,z455,z4,z5]),(0,[z91,z1,z2,z455,z4,z5]),(0,[z1,z37,z52,z120,z4,z5]),(0,[z194,z1,z2,z3,z521,z223]),(0,[z0,z1,z3,z741,z74,z5])],[(0,[z0,z1,z1063,z3,z4,z5]),(0,[z140,z1,z2,z3,z4,z5]),(0,[z0,z1,z1064,z3,z4,z5]),(0,[z528,z1,z2,z3,z4,z206]),(0,[z43,z0,z45,z3,z4,z283]),(0,[z0,z1,z2,z3,z47,z322])],[(0,[z0,z1,z2,z124,z4,z416]),(0,[z0,z1,z241,z3,z4,z5]),(0,[z0,z2,z3,z1065,z4,z5]),(0,[z181,z1,z20,z154,z4,z5]),(0,[z0,z1,z28,z3,z4,z5])],[(0,[z94,z51,z2,z3,z4,z5]),(0,[z142,z226,z1,z2,z4,z5]),(0,[z1,z850,z78,z3,z4,z5]),(0,[z142,z1,z52,z345,z4,z5]),(0,[z1066,z1,z2,z3,z4,z5]),(0,[z1067,z1,z2,z3,z4,z5]),(0,[z0,z292,z2,z3,z4,z69]),(0,[z551,z1,z2,z370,z4,z5])],[(0,[z1,z1068,z2,z3,z4,z5]),(0,[z91,z1,z241,z3,z4,z5]),(0,[z0,z1,z2,z1069,z4,z5]),(0,[z129,z138,z0,z1,z2,z3]),(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z2,z111,z750,z4,z5])],[],[(0,[z91,z1,z19,z120,z4,z5])],[(0,[z181,z1,z168,z20,z4,z5]),(0,[z43,z0,z45,z3,z348,z5]),(0,[z1,z2,z3,z4,z5,z1070]),(0,[z0,z1,z261,z3,z164,z5]),(0,[z0,z1,z2,z773,z4,z5])]],
   [[(0,[z0,z1,z2,z455,z4,z133]),(0,[z0,z1,z1071,z3,z4,z5]),(0,[z1072,z1,z2,z3,z4,z5]),(0,[z380,z292,z2,z3,z4,z5])],[(0,[z1073,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z266,z4,z283]),(0,[z1074,z1,z2,z3,z4,z5]),(0,[z0,z1,z1075,z2,z4,z5]),(0,[z0,z1,z550,z77,z4,z5]),(0,[z0,z1,z2,z57,z4,z716])],[(0,[z0,z1,z2,z3,z1076,z5]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z0,z1,z52,z200,z4,z5]),(0,[z495,z1,z2,z20,z4,z5]),(0,[z0,z1,z1078,z3,z4,z5]),(0,[z0,z1,z2,z456,z33,z5])],[(0,[z0,z1,z281,z3,z439,z5]),(0,[z0,z1,z2,z1079,z4,z5]),(0,[z0,z263,z141,z3,z4,z5]),(0,[z43,z0,z44,z45,z4,z5]),(0,[z0,z1,z39,z3,z5,z211]),(0,[z1080,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z57,z4,z34])],[(0,[z1,z474,z2,z20,z4,z5]),(0,[z0,z1,z2,z1081,z4,z5]),(0,[z0,z292,z2,z370,z4,z5])],[(0,[z0,z1,z1082,z3,z4,z5]),(0,[z1,z678,z2,z120,z4,z5]),(0,[z140,z1,z241,z3,z4,z5]),(0,[z10,z0,z1,z115,z2,z57]),(0,[z551,z209,z2,z3,z4,z5])],[(0,[z91,z1,z281,z3,z4,z5]),(0,[z1,z2,z3,z4,z1083,z5]),(0,[z0,z1,z1084,z2,z4,z5]),(0,[z0,z1,z2,z3,z47,z684]),(1,[z0,z1,z713,z4,z5]),(0,[z407,z1,z77,z2,z4,z5])],[(0,[z0,z1,z1085,z2,z4,z5]),(0,[z101,z442,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1086]),(0,[z0,z1,z2,z1087,z4,z5]),(0,[z0,z1,z1088,z3,z4,z5]),(0,[z0,z1,z2,z266,z348,z5]),(0,[z1,z2,z3,z1089,z4,z5]),(0,[z1090,z1,z2,z3,z4,z5])]],
   [[(0,[z247,z1,z77,z3,z4,z5]),(0,[z43,z0,z45,z3,z387,z5]),(0,[z0,z1,z2,z35,z3,z117])],[(0,[z0,z1,z1091,z2,z4,z5]),(0,[z1092,z0,z1,z2,z3,z5]),(0,[z119,z1,z264,z2,z4,z5]),(1,[z0,z838,z3,z4,z5]),(0,[z0,z1,z63,z28,z4,z5]),(0,[z0,z1,z2,z3,z1093,z5]),(0,[z1,z1094,z2,z3,z4,z5])],[(0,[z161,z1,z2,z3,z734,z5]),(0,[z49,z1,z2,z53,z4,z5]),(0,[z0,z72,z1,z414,z4,z5]),(0,[z1,z2,z1095,z3,z4,z5]),(0,[z0,z1,z2,z3,z1096,z5])],[(0,[z380,z1,z2,z3,z4,z5]),(0,[z0,z263,z25,z3,z4,z5]),(0,[z1,z1097,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z164,z5])],[(0,[z0,z1,z281,z455,z4,z5]),(0,[z75,z1,z78,z3,z4,z5]),(0,[z226,z49,z1,z2,z4,z5]),(0,[z0,z1,z1098,z3,z4,z5]),(0,[z1,z208,z2,z3,z4,z5]),(0,[z0,z1,z37,z345,z4,z5]),(0,[z0,z72,z403,z2,z4,z5]),(0,[z0,z1,z1099,z3,z4,z5]),(0,[z0,z209,z261,z3,z4,z5])],[(0,[z239,z1,z542,z2,z4,z5]),(0,[z0,z1,z850,z3,z4,z5]),(0,[z181,z1,z2,z20,z4,z5]),(0,[z0,z1,z31,z3,z4,z408])],[(0,[z0,z1,z2,z3,z4,z1100]),(0,[z94,z780,z2,z3,z4,z5]),(0,[z1101,z0,z1,z2,z3,z4]),(0,[z91,z1,z71,z3,z4,z5]),(0,[z0,z263,z1,z200,z4,z5]),(0,[z0,z1,z1102,z3,z4,z5]),(0,[z0,z1,z1103,z3,z4,z5]),(0,[z0,z1,z2,z3,z164,z305]),(0,[z0,z1,z152,z261,z3,z4])],[(0,[z1104,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z1105,z5]),(0,[z91,z1,z850,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z1106]),(0,[z0,z1,z77,z713,z4,z5]),(0,[z1107,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z370,z4,z5]),(0,[z0,z1,z2,z3,z4,z1108])]],
   [[(0,[z0,z1,z2,z3,z95,z5]),(0,[z239,z1,z168,z3,z4,z5]),(0,[z0,z522,z25,z3,z4,z5]),(0,[z1,z1109,z2,z3,z4,z5])],[(0,[z1,z63,z2,z356,z4,z5]),(0,[z0,z1,z2,z3,z1110,z5]),(0,[z1111,z1,z2,z3,z4,z5])],[(0,[z0,z1,z222,z3,z95,z5]),(0,[z1,z1112,z2,z3,z4,z5]),(1,[z0,z1,z3,z4,z757]),(0,[z1113,z1,z2,z3,z4,z5]),(0,[z551,z292,z2,z3,z4,z5])],[(0,[z62,z1,z2,z3,z4,z5]),(0,[z75,z0,z1,z182,z4,z5]),(0,[z181,z1,z77,z52,z4,z5]),(0,[z0,z1,z25,z345,z4,z5]),(0,[z43,z0,z114,z3,z4,z5])],[(0,[z1,z2,z1114,z3,z4,z5]),(0,[z1115,z1,z2,z3,z4,z5]),(0,[z479,z1,z77,z2,z4,z5]),(0,[z380,z1,z2,z3,z68,z5]),(0,[z0,z1,z2,z3,z179,z5])],[(0,[z1116,z0,z1,z2,z3,z5]),(0,[z43,z0,z1,z200,z4,z5]),(0,[z0,z1,z838,z3,z4,z5]),(0,[z1117,z1,z2,z3,z4,z5])],[(0,[z119,z1,z208,z2,z4,z5]),(0,[z106,z1,z2,z20,z4,z5]),(0,[z0,z1,z2,z3,z4,z1118])],[(0,[z1119,z0,z1,z2,z3,z5]),(0,[z0,z1,z28,z111,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1120]),(0,[z0,z1,z2,z1121,z3,z5]),(0,[z181,z0,z1,z28,z4,z5]),(0,[z0,z1,z2,z1122,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1123]),(0,[z0,z1,z1124,z3,z4,z5]),(0,[z0,z1,z1125,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1126])],[(0,[z0,z1,z2,z3,z95,z133]),(0,[z0,z1,z2,z1127,z4,z5]),(0,[z239,z2,z3,z325,z4,z5]),(0,[z21,z122,z1,z2,z3,z4]),(0,[z0,z1,z2,z35,z3,z69])],[(0,[z91,z0,z1,z345,z4,z5]),(0,[z119,z1,z2,z120,z4,z5]),(0,[z0,z1,z436,z3,z4,z237]),(0,[z0,z1,z39,z3,z610,z5]),(0,[z0,z1,z1128,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1129,z5]),(0,[z0,z1,z1130,z3,z4,z5]),(0,[z0,z1,z225,z2,z3,z117])],[(0,[z94,z226,z1,z2,z4,z5]),(0,[z142,z1,z19,z20,z4,z5]),(0,[z551,z1,z2,z3,z4,z5]),(0,[z326,z0,z2,z3,z68,z5]),(0,[z0,z1,z37,z517,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1131]),(0,[z0,z1,z2,z1132,z4,z5]),(0,[z161,z1,z2,z3,z565,z5]),(0,[z0,z2,z750,z53,z4,z5]),(0,[z0,z1,z1133,z3,z4,z5]),(0,[z1,z1134,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z189,z627])],[(0,[z10,z621,z0,z1,z2,z3]),(0,[z1135,z1,z2,z3,z4,z5]),(0,[z10,z380,z1,z2,z3,z11])]],
   [[(0,[z0,z1,z2,z4,z5,z1136]),(0,[z0,z1,z2,z3,z4,z1137]),(0,[z1,z542,z208,z2,z4,z5]),(0,[z1138,z1,z2,z3,z4,z5]),(0,[z0,z72,z2,z750,z4,z5]),(0,[z0,z284,z2,z3,z164,z5]),(0,[z0,z1,z115,z2,z35,z5])],[(0,[z119,z1,z77,z78,z4,z5]),(0,[z0,z1,z1139,z3,z4,z5]),(0,[z1140,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1141]),(0,[z0,z501,z2,z3,z164,z5]),(0,[z1142,z1,z2,z3,z4,z5]),(0,[z0,z1,z188,z2,z35,z58])],[(0,[z0,z1,z200,z54,z4,z5]),(0,[z142,z1,z542,z52,z4,z5]),(0,[z119,z0,z1,z154,z4,z5]),(0,[z247,z1,z37,z3,z4,z5])],[(0,[z0,z1,z3,z4,z1143,z5]),(0,[z181,z49,z1,z2,z4,z5]),(0,[z0,z1,z436,z3,z271,z5])],[(0,[z407,z1,z2,z120,z4,z5]),(0,[z122,z380,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1144]),(0,[z1,z2,z3,z1145,z4,z5]),(0,[z27,z49,z2,z53,z4,z5]),(0,[z0,z1,z2,z57,z93,z4])],[(0,[z75,z1,z3,z120,z4,z5]),(0,[z1,z542,z2,z120,z4,z5]),(1,[z1,z2,z3,z734,z5]),(0,[z10,z122,z161,z1,z2,z3])],[(0,[z0,z1,z281,z3,z95,z5]),(0,[z490,z1,z2,z120,z4,z5]),(0,[z138,z380,z1,z2,z3,z4]),(0,[z0,z1,z2,z137,z4,z125]),(0,[z0,z1,z2,z3,z348,z283]),(0,[z0,z292,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z117,z777]),(0,[z0,z1,z152,z165,z3,z74])],[(0,[z101,z1,z281,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z1146]),(0,[z229,z0,z2,z53,z4,z5]),(0,[z1147,z1,z2,z3,z4,z5])]],
   [[(0,[z26,z1,z2,z3,z4,z5]),(0,[z0,z1,z1148,z3,z4,z5]),(0,[z0,z1,z1149,z3,z4,z5]),(0,[z0,z1,z2,z1150,z4,z5])],[(0,[z62,z1,z281,z3,z4,z5]),(0,[z0,z1,z1151,z3,z4,z5]),(0,[z1,z52,z534,z3,z4,z5]),(0,[z1,z2,z20,z711,z4,z5]),(0,[z247,z1,z25,z3,z4,z5]),(0,[z1152,z1,z2,z3,z4,z5]),(0,[z1,z208,z2,z111,z4,z5]),(0,[z1,z1153,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1154]),(0,[z161,z380,z1,z2,z3,z5]),(0,[z0,z1,z261,z3,z4,z117]),(0,[z1155,z1,z2,z3,z4,z5])],[(0,[z0,z1,z63,z52,z4,z5]),(0,[z1156,z1,z2,z3,z4,z5]),(0,[z43,z0,z63,z45,z4,z5]),(0,[z0,z1,z2,z3,z1157,z5]),(0,[z1158,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1159,z5]),(0,[z119,z256,z1,z2,z4,z5]),(0,[z181,z91,z1,z54,z4,z5]),(0,[z119,z1,z2,z711,z4,z5]),(0,[z0,z1,z2,z137,z387,z5]),(0,[z1160,z1,z2,z3,z4,z5]),(0,[z380,z1,z2,z370,z4,z5])],[(0,[z142,z119,z1,z54,z4,z5]),(0,[z0,z1,z261,z3,z68,z5]),(0,[z0,z1,z2,z1161,z4,z5])],[(0,[z0,z1,z2,z1162,z4,z5]),(0,[z43,z140,z1,z3,z4,z5]),(0,[z1163,z1,z2,z3,z4,z5]),(0,[z0,z1,z225,z2,z3,z69]),(1,[z0,z1,z2,z773,z5])],[(0,[z0,z1,z2,z1164,z4,z5]),(0,[z161,z1,z2,z3,z5,z599]),(0,[z0,z1,z2,z3,z387,z283]),(0,[z27,z0,z2,z53,z4,z237]),(0,[z0,z1,z2,z3,z1165,z5])]],
   [[(0,[z0,z1,z2,z3,z1166,z5]),(0,[z0,z1,z31,z261,z3,z4])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z75,z0,z1,z3,z4,z5]),(0,[z1,z78,z369,z3,z4,z5]),(0,[z247,z1,z2,z137,z4,z5]),(0,[z1167,z1,z2,z3,z4,z5])],[(0,[z0,z1,z3,z1168,z4,z5]),(0,[z0,z1,z1169,z2,z4,z5]),(0,[z479,z1,z2,z120,z4,z5]),(0,[z0,z1,z2,z3,z1170,z5]),(0,[z0,z284,z2,z3,z484,z5])],[(0,[z0,z1,z222,z3,z4,z5]),(0,[z0,z1,z1171,z3,z4,z5]),(0,[z0,z2,z3,z4,z853,z5]),(0,[z0,z1,z1172,z3,z4,z5])],[(0,[z61,z1,z2,z3,z4,z5]),(0,[z226,z1,z2,z78,z4,z5]),(0,[z0,z1,z2,z3,z4,z1173]),(0,[z0,z1,z1174,z2,z4,z5]),(1,[z1,z2,z3,z4,z727]),(0,[z0,z1,z2,z3,z4,z1175]),(0,[z0,z1,z2,z3,z4,z1176]),(0,[z26,z1,z28,z3,z4,z5]),(0,[z0,z1,z2,z3,z271,z6]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1177,z2,z3,z4,z5])],[(0,[z91,z1,z2,z85,z4,z5]),(0,[z138,z1,z2,z3,z42,z206]),(0,[z122,z1,z2,z3,z4,z460]),(0,[z0,z1,z2,z3,z1178,z5])],[(0,[z94,z177,z2,z3,z439,z5]),(0,[z175,z0,z2,z3,z68,z5]),(0,[z0,z1,z2,z93,z4,z117])],[(0,[z49,z1,z28,z3,z4,z5]),(0,[z27,z0,z2,z53,z271,z5]),(0,[z1179,z0,z1,z3,z4,z5]),(0,[z0,z41,z2,z3,z68,z5]),(0,[z0,z1,z3,z4,z5,z757])]],
   [[(0,[z0,z1,z2,z1180,z4,z5]),(0,[z0,z1,z105,z3,z4,z5]),(0,[z0,z1,z2,z57,z4,z601])],[(1,[z780,z2,z3,z4,z5]),(0,[z49,z1,z2,z3,z4,z6])],[(0,[z239,z2,z554,z3,z4,z5]),(0,[z0,z1,z37,z54,z4,z5])],[(0,[z0,z1,z2,z3,z4,z133]),(0,[z1,z177,z281,z3,z4,z5]),(0,[z0,z1,z2,z1181,z4,z5]),(0,[z407,z1,z19,z77,z4,z5]),(0,[z0,z1,z2,z4,z716,z58])],[(0,[z0,z1,z1182,z3,z4,z5]),(0,[z0,z1,z2,z3,z1183,z5]),(0,[z0,z1,z261,z3,z4,z69])],[(0,[z0,z1,z222,z3,z4,z133]),(0,[z0,z1,z2,z3,z1184,z5])],[(0,[z0,z1,z1185,z2,z4,z5]),(0,[z0,z1,z436,z3,z344,z5]),(0,[z27,z407,z1,z2,z4,z5]),(0,[z10,z0,z1,z167,z3,z11])],[(0,[z94,z177,z2,z455,z4,z5]),(0,[z0,z1,z2,z3,z1186,z5]),(0,[z0,z1,z2,z1187,z4,z5]),(0,[z0,z1,z1188,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z1189]),(0,[z62,z1,z78,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1190]),(0,[z0,z1,z2,z1191,z4,z5])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 524).take 536) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1060).take 86) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1146)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [524, 536, 86] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 97).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 195).take 61).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [97, 98, 61] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38735

theorem PEqualNP.Outside.L_meta_38735 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 3941264064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 3941264064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38735.solve