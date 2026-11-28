import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37023

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
  Nat.testBit (4276809448 * 2 ^ 32 + 4008373480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00200020c5041305#64 ++ 0xffd809e9cf4cf70f#64 : BitVec 128),
   (0x2240128212114052#64 ++ 0xffbc369633b349f3#64 : BitVec 128),
   (0x0901c51828c28c28#64 ++ 0xdb7bc7183cc38e3c#64 : BitVec 128),
   (0x4d82e81d40ec0f80#64 ++ 0xb6f7f81fc0fc0fc0#64 : BitVec 128),
   (0x8e037fc000fbe000#64 ++ 0x71f3ffe000fff000#64 : BitVec 128),
   (0xf007bfffbf000000#64 ++ 0x0ff7ffffff000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x00200020c5041305 0xffd809e9cf4cf70f

def z1 : W := mkw 0x0901c51828c28c28 0xdb7bc7183cc38e3c

def z2 : W := mkw 0x2240128212114052 0xffbc369633b349f3

def z3 : W := mkw 0x226012a2d7155357 0x248438e7c33c71c3

def z4 : W := mkw 0x4d82e81d40ec0f80 0xb6f7f81fc0fc0fc0

def z5 : W := mkw 0x8e037fc000fbe000 0x71f3ffe000fff000

def z6 : W := mkw 0xf007bfffbf000000 0x0ff7ffffff000000

def z7 : W := mkw 0x700492bfbf000000 0x0fb4369fff000000

def z8 : W := mkw 0x0c02680000e80000 0x30f3f80000fc0000

def z9 : W := mkw 0x44822805402c0380 0x24843807c03c01c0

def z10 : W := mkw 0x2240128212114052 0xae8c3096333049f3

def z11 : W := mkw 0x0200128000114000 0x4100068000034000

def z12 : W := mkw 0x6dc2e81f52ec0fd2 0xbefff81ff3fc0ff3

def z13 : W := mkw 0x0240000000114052 0xf008000000b349f3

def z14 : W := mkw 0x0d80400040ec0f80 0xb000000000fc0fc0

def z15 : W := mkw 0x0020000040041305 0xf0080000004cf70f

def z16 : W := mkw 0xf027bfffff041305 0xffffffffff4cf70f

def z17 : W := mkw 0x0801450000c28000 0x5173c70000c38000

def z18 : W := mkw 0xf247bfffbf114052 0xffffffffffb349f3

def z19 : W := mkw 0xf007bfffbf000000 0xbff7ffffffb009c0

def z20 : W := mkw 0x4da2e83dc5ec1f85 0xfffff9ffcffcffcf

def z21 : W := mkw 0x6fc2fa9f52fd4fd2 0xfffffe9ff3ff4ff3

def z22 : W := mkw 0x4003ad1d28000000 0x0ff7ff1ffc000000

def z23 : W := mkw 0x226012a2d7155357 0xfffc3fffffffffff

def z24 : W := mkw 0xae437fc212fbe052 0xfffffff633fff9f3

def z25 : W := mkw 0x2240128212114052 0x24843086033041c3

def z26 : W := mkw 0xd007ad7dad000000 0x0043c969cc000000

def z27 : W := mkw 0x4002a81d00000000 0x06f7f81fc0000000

def z28 : W := mkw 0xb905d7fabfc28c28 0xdb7bc7f83fc38e3c

def z29 : W := mkw 0xfd87ffffffee8fa8 0xffffffffffff8ffc

def z30 : W := mkw 0x8e437fc000fbe052 0xf1fbffe000fff9f3

def z31 : W := mkw 0x0200128000114000 0xfbb8369030b34830

def z32 : W := mkw 0x80033fc000000000 0x01f3ffe000000000

def z33 : W := mkw 0xf927ffffffc69f2d 0xffffffffffcfff3f

def z34 : W := mkw 0x6fe2fabfd7fd5fd7 0xffffffffffffffff

def z35 : W := mkw 0x4180801d40040f80 0x00000009c0000600

def z36 : W := mkw 0x8e037fc000fbe000 0xfbfbffe80cfff60c

def z37 : W := mkw 0xfd87ffdf7aec0f80 0xb6f7fe1ff0fc0fc0

def z38 : W := mkw 0x2241979a3a114052 0xfffff79e3fb349f3

def z39 : W := mkw 0x0001851828000000 0x0b73c7183c000000

def z40 : W := mkw 0xf0063ae797000000 0x048438e7c3000000

def z41 : W := mkw 0xf007bfdf3a000000 0x0fb7f69633000000

def z42 : W := mkw 0x00200020c5041305 0x8e080009cf00070f

def z43 : W := mkw 0x8c036d4000eaa000 0x0043c960004cb000

def z44 : W := mkw 0xf007bfdf3a000000 0x0027f61630000000

def z45 : W := mkw 0x0b40400000d3cc7a 0xf008000000f3cfff

def z46 : W := mkw 0x0100801828000c28 0x8a0800183c000e3c

def z47 : W := mkw 0xdd87ed7dedec0f80 0xb6f7f97fccfc0fc0

def z48 : W := mkw 0x2240128212114052 0x24a4369633b349f3

def z49 : W := mkw 0x00200020c5041305 0x248008e1c30c7103

def z50 : W := mkw 0x0901c51828c28c28 0x0023c61030830830

def z51 : W := mkw 0x8e037fc000fbe000 0x0023f60000b30000

def z52 : W := mkw 0x0901c51828c28c28 0xfffbc7983fc3cf3f

def z53 : W := mkw 0x0921c538edc69f2d 0xdb7bcf79fccfbe3c

def z54 : W := mkw 0x0000002085000000 0x0fd009e9cf000000

def z55 : W := mkw 0x0000000000000000 0xdb38061030830830

def z56 : W := mkw 0x0240000000114052 0x20000000003041c3

def z57 : W := mkw 0x8e027ac000f96000 0x30f3f8e000fc7000

def z58 : W := mkw 0x226012a2d7155357 0xffd80fe9ff4ff73f

def z59 : W := mkw 0x2b41d79a3ad3cc7a 0xdb7bc7983fc3ce3f

def z60 : W := mkw 0x2000128212000000 0x0fb4369633000000

def z61 : W := mkw 0x0e00400000fbe000 0x7000000000fff000

def z62 : W := mkw 0x7004803fbf000000 0x0e04001fff000000

def z63 : W := mkw 0x0020002085001005 0x490801e00f00f00f

def z64 : W := mkw 0x00200020c5041305 0x00400969cc4cb60c

def z65 : W := mkw 0x0001050028028028 0x490807003c03803c

def z66 : W := mkw 0xf007bfffbf028028 0x4fffffffff03803c

def z67 : W := mkw 0xb00597fabf000000 0x0b73c7f83f000000

def z68 : W := mkw 0x0f00400000fbec28 0xf008000000fffe3c

def z69 : W := mkw 0x0d80400040ec0f80 0x00000000004c0600

def z70 : W := mkw 0x4d82e81d40ec0f80 0x0043c809c04c0600

def z71 : W := mkw 0x86023ac000396000 0x208038e0003c7000

def z72 : W := mkw 0x2941c51a3ac28c7a 0xdf7fc71e3fc38fff

def z73 : W := mkw 0x8d03ed5828eaac28 0xdb7bcf783ccfbe3c

def z74 : W := mkw 0x0900c01828c00c28 0x9a7bc0183cc00e3c

def z75 : W := mkw 0x8e037fc000fbe000 0xf7f7fff600fff9c0

def z76 : W := mkw 0xde07fffdadfbe000 0x71f3ffe9ccfff000

def z77 : W := mkw 0x0000000000000000 0x06d00809c0000000

def z78 : W := mkw 0x0000000040040300 0xb6d00809c04c0700

def z79 : W := mkw 0x8f03ffd828fbec28 0xfbfbfff83cfffe3c

def z80 : W := mkw 0xcd83ed5d40eeaf80 0xb6f7f97fc0fcbfc0

def z81 : W := mkw 0x4d82e81d40ec0f80 0xb043c809c0fc0fc0

def z82 : W := mkw 0x0002280000000000 0x00f3f80000000000

def z83 : W := mkw 0xfe07ffffbffbe000 0x7ff7fffffffff000

def z84 : W := mkw 0xcd83ed5d40eeaf80 0x0043c969c04cb600

def z85 : W := mkw 0x0f80400040ffef80 0xf000000000ffffc0

def z86 : W := mkw 0x0000000000000000 0xdb5801080c40860c

def z87 : W := mkw 0xf007bfffbf000000 0xdfffffffff40860c

def z88 : W := mkw 0x0fc0400040fd4fd2 0xf008000000ff4ff3

def z89 : W := mkw 0x41a0803dc5041f85 0xffdc09ffcf4cffcf

def z90 : W := mkw 0x2240128212114052 0x6d8c3686333341f3

def z91 : W := mkw 0x0900c01800c00c00 0xdb7bc61830c30e30

def z92 : W := mkw 0xf207bfffbf114000 0x7ff7ffffffb34000

def z93 : W := mkw 0xcf83ffdd40ffef80 0xf7f7ffffc0ffffc0

def z94 : W := mkw 0x0180000040040f80 0x8000000000000fc0

def z95 : W := mkw 0x20600022d7041357 0xffdc09ffff4cffff

def z96 : W := mkw 0x0900c01800c00c00 0x9273c01800c00e00

def z97 : W := mkw 0x0402280000280000 0x20803800003c0000

def z98 : W := mkw 0xf107bfffbf000c28 0x8fffffffff000e3c

def z99 : W := mkw 0x8e037fc000fbe000 0x4143cfe0004ff000

def z100 : W := mkw 0x0901c51828c28c28 0x492bc7103c83883c

def z101 : W := mkw 0x0000000000000000 0xb6b4301600b009c0

def z102 : W := mkw 0x2b41d79a3ad3cc7a 0xfffff79e3ff3cfff

def z103 : W := mkw 0x0e20400040fff305 0xf008000000fff70f

def z104 : W := mkw 0x0e00400000fbe000 0x0000000000b30000

def z105 : W := mkw 0x0000000000000000 0x0024301600b008c0

def z106 : W := mkw 0x4d82e81d00e80c80 0x0027f01600b008c0

def z107 : W := mkw 0x0001851828000000 0xdb7bc7183c40860c

def z108 : W := mkw 0x0901c51828c28c28 0xfffff71e3cf38ffc

def z109 : W := mkw 0xd007ad5d28000000 0x0003c00000000000

def z110 : W := mkw 0x2240128212114052 0x0024361630b308f0

def z111 : W := mkw 0x80033fc000000000 0x71f3ffe0004cf000

def z112 : W := mkw 0x4d83ed1d68ee8fa8 0xffffff1ffcff8ffc

def z113 : W := mkw 0x0e00528000fbe000 0x71b0368000fff000

def z114 : W := mkw 0x82033fc00013e000 0x41f3ffe00003f000

def z115 : W := mkw 0x2200128212114000 0x7fb4369633b34000

def z116 : W := mkw 0x4d82e81d40ec0f80 0x8627f01fc0b00fc0

def z117 : W := mkw 0x4d82e81d40ec0f80 0xfffff91fccfc8fcc

def z118 : W := mkw 0xf247bfdf3a114052 0xffbff69633b349f3

def z119 : W := mkw 0x4002a81d00000000 0xb6f7f81fc0b009c0

def z120 : W := mkw 0xf027bfffbf001005 0x4fffffffff00f00f

def z121 : W := mkw 0x2240128212114052 0x4908068033034033

def z122 : W := mkw 0xb00517e2bf000000 0x090007e03f000000

def z123 : W := mkw 0x2240128212114052 0x00043006003000c0

def z124 : W := mkw 0x2240128212114052 0xfffc3ff633fff9f3

def z125 : W := mkw 0x0000000000000000 0x71d009e0004cf000

def z126 : W := mkw 0x8e237fe0c5fff305 0xfffbffe9cffff70f

def z127 : W := mkw 0xf4863ae7d72c0380 0x248438e7c33c01c0

def z128 : W := mkw 0x8f037fc000fbec28 0xf1fbffe000fffe3c

def z129 : W := mkw 0x00200020c5041305 0xcf0801e9cf00f70f

def z130 : W := mkw 0xf007bfffbf000000 0x04c7f9efcf000000

def z131 : W := mkw 0x2001979a3a000000 0x0ff7f79e3f000000

def z132 : W := mkw 0x00200020c5041305 0x8fd809e9cf00070f

def z133 : W := mkw 0x4d82e81d40ec0f80 0xf7f7f9ffc0fcffc0

def z134 : W := mkw 0x0020002085001005 0xdb5801e80f40f60f

def z135 : W := mkw 0x2040000212000052 0x8e0c0016330009f3

def z136 : W := mkw 0x0d02e81800e80c00 0xb2f3f81800fc0e00

def z137 : W := mkw 0x0600000000396000 0x20000000003c7000

def z138 : W := mkw 0xf0063ae797000000 0x0fb43ef7f3000000

def z139 : W := mkw 0xfe27fffffffff305 0xfffffffffffff70f

def z140 : W := mkw 0x7024803fff041305 0x8e0c001fff00070f

def z141 : W := mkw 0x0c00400000e80000 0x3000000000fc0000

def z142 : W := mkw 0x4d82680540ec0f80 0xb4843807c0fc0fc0

def z143 : W := mkw 0x8c036d4000eaa000 0x5173cf6000cfb000

def z144 : W := mkw 0x0000000000000000 0x86040016000009c0

def z145 : W := mkw 0x86033fc000396000 0x21f3ffe0003c7000

def z146 : W := mkw 0xb0073fe2bf000000 0x09f3ffe03f000000

def z147 : W := mkw 0x00200020c5041305 0xff9808e1c30c7103

def z148 : W := mkw 0x2240128212114052 0xf48c308603b349f3

def z149 : W := mkw 0xa24117c21213e052 0x490807e03303f033

def z150 : W := mkw 0x86033fc0003be000 0x61803fe0003ff000

def z151 : W := mkw 0x724492bfbf114052 0xffbc369fffb349f3

def z152 : W := mkw 0x0200128000114000 0x71b0368000b34000

def z153 : W := mkw 0x0901450000c28c28 0xd17bc70000c38e3c

def z154 : W := mkw 0x822117e08513f005 0x490807e00f03f00f

def z155 : W := mkw 0xf007bfffbf000000 0x0e27f61fff000000

def z156 : W := mkw 0x0001851828000000 0xdb7bc7183c830830

def z157 : W := mkw 0x0921c538edc69f2d 0xfffbcff9ffcfff3f

def z158 : W := mkw 0x8e037fc000fbe000 0xfbfbfff030fff830

def z159 : W := mkw 0x00200020c5041305 0xdf580109cf40870f

def z160 : W := mkw 0x4d83ed1d28ea8ca8 0xdb7ff71e3cf38efc

def z161 : W := mkw 0x0d03ed1828ea8c28 0xfbfbff183cff8e3c

def z162 : W := mkw 0x41a0803dc5041f85 0x8e0c001fcf000fcf

def z163 : W := mkw 0x0900400000c28c28 0xd008000000c38e3c

def z164 : W := mkw 0x4022a83dc5041305 0xfffff9ffcf4cf70f

def z165 : W := mkw 0xa2433fc212114052 0xfffffff633b349f3

def z166 : W := mkw 0x7005853fbf000000 0x0f77c71fff000000

def z167 : W := mkw 0x0900400000c28c28 0xdb38061030c38e3c

def z168 : W := mkw 0x0020000040041305 0xf1d809e0004cf70f

def z169 : W := mkw 0x0000128000000000 0x01b0368000000000

def z170 : W := mkw 0x8e037fc040ffe300 0xf7f3ffe9c0fff700

def z171 : W := mkw 0x0d80400040ee8fa8 0xf008000000ff8ffc

def z172 : W := mkw 0xae437fc212fbe052 0x71f7fff630fff8f0

def z173 : W := mkw 0xd006286585000000 0x00000861c0000000

def z174 : W := mkw 0x2240128212114052 0x0000060030030030

def z175 : W := mkw 0x8e027ac000fbe000 0x708038e000fff000

def z176 : W := mkw 0x2040000212000052 0xdf3c0616338309f3

def z177 : W := mkw 0x0901c51828c28c28 0x494bc7083c43863c

def z178 : W := mkw 0x6242ba9f12114052 0xfffffe9ff3b349f3

def z179 : W := mkw 0x61c0801f52040fd2 0x8e0c001ff3000ff3

def z180 : W := mkw 0xf047bfffbf000052 0x8fffffffff0009f3

def z181 : W := mkw 0x8c236d60c5eeb305 0xffdbc9e9cf4cf70f

def z182 : W := mkw 0x0000000000000000 0x0000000000000000

def z183 : W := mkw 0x7905c53fbfc28c28 0xdf7fc71fffc38e3c

def z184 : W := mkw 0x30040022bf000000 0x080000003f000000

def z185 : W := mkw 0x4180801d40040f80 0x8604001fc0000fc0

def z186 : W := mkw 0x820117c00013e000 0x410007e00003f000

def z187 : W := mkw 0x226012a2d7155357 0xffbc3ef7f3bf79f3

def z188 : W := mkw 0xf007bfdf3a000000 0x06f7fe1ff0000000

def z189 : W := mkw 0x0e40400000fbe052 0xf008000000fff9f3

def z190 : W := mkw 0xf007ad7fbf000000 0x0e47c97fff000000

def z191 : W := mkw 0x2240128212114052 0x8e2c361633b309f3

def z192 : W := mkw 0x0240000000114052 0xfb38061030b349f3

def z193 : W := mkw 0xae437fc212fbe052 0x79fbffe033fff033

def z194 : W := mkw 0x0020000000001005 0x400800000000f00f

def z195 : W := mkw 0x0901c51828c28c28 0xfbfbcff83ccffe3c

def z196 : W := mkw 0x4002a81d40040300 0xb6f7f81fc04c0700

def z197 : W := mkw 0x00200020c5041305 0x24c009e9cf4cf70f

def z198 : W := mkw 0x820012c000116000 0x000000e000007000

def z199 : W := mkw 0xf2463ae797114052 0x248438e7c33041c3

def z200 : W := mkw 0x0900c01800c00c00 0xdb7bc1180cc08e0c

def z201 : W := mkw 0x2b41d79a3ad3cc7a 0xdb7ff71e3cf38efc

def z202 : W := mkw 0x09204020c5c69f2d 0xffd809e9cfcfff3f

def z203 : W := mkw 0x0920400040c69f2d 0xf008000000cfff3f

def z204 : W := mkw 0x86023ac000396000 0x71d039e0007cf000

def z205 : W := mkw 0x0020000040041305 0xfb5801080c4cf70f

def z206 : W := mkw 0x0d82680040ec0f80 0xb0f3f80000fc0fc0

def z207 : W := mkw 0xf0063ac712000000 0x0004300600000000

def z208 : W := mkw 0x8f03ffd828fbec28 0x71f3fff030fff830

def z209 : W := mkw 0x0000000000000000 0xff98008003004103

def z210 : W := mkw 0x0020000040041305 0x00000000004cb60c

def z211 : W := mkw 0x08214520c5c69305 0xfffbcfe9cfcff70f

def z212 : W := mkw 0xf247bfffbf114052 0x4fffffffff034033

def z213 : W := mkw 0xae637fe2d7fff357 0xffffffffffffffff

def z214 : W := mkw 0x86023ac000396000 0x0000300000300000

def z215 : W := mkw 0xf007bfdf3a000000 0x01f7fff630000000

def z216 : W := mkw 0x4482a81d402c0380 0x26f7f81fc03c01c0

def z217 : W := mkw 0x4fc2e81d40fd4fd2 0xf6fff81fc0ff4ff3

def z218 : W := mkw 0xae437fc212fbe052 0xffbff69633b349f3

def z219 : W := mkw 0xaf43ffda3afbec7a 0xfffffffe3fffffff

def z220 : W := mkw 0x0901c51828c28c28 0x5173c7080cc3860c

def z221 : W := mkw 0x2240128212114052 0xf908068033b349f3

def z222 : W := mkw 0x0901c51828c28c28 0x0043c1080c40860c

def z223 : W := mkw 0xf006baffbf000000 0x0e8438ffff000000

def z224 : W := mkw 0x6002ba9f12000000 0x0ff7fe9ff3000000

def z225 : W := mkw 0xfd87ffffbfe80c80 0x0ff7ffffffb008c0

def z226 : W := mkw 0xf607bfffbf396000 0x2ff7ffffff3c7000

def z227 : W := mkw 0x4002a81d00000000 0x0043c809c0000000

def z228 : W := mkw 0x2000128212000000 0xdfbc369633830830

def z229 : W := mkw 0x0001050028028028 0x0000060030030030

def z230 : W := mkw 0x4903ed1d28c28c28 0xdfffff1ffcc38e3c

def z231 : W := mkw 0x4d83ed1d40ee8f80 0xf7f7ff1fc0ff8fc0

def z232 : W := mkw 0x2e427a8212f94052 0xfffffe9633ff49f3

def z233 : W := mkw 0x8402284000282000 0x00000860000c3000

def z234 : W := mkw 0x00200020c5041305 0xf0480969cc4cf70f

def z235 : W := mkw 0x2140801a3a000c7a 0x8e0c001e3f000fff

def z236 : W := mkw 0x0000801800000000 0x0273c01800000000

def z237 : W := mkw 0x8e037fc028fbe028 0x79fbffe03cfff03c

def z238 : W := mkw 0x2040000212000052 0x00040016300008f0

def z239 : W := mkw 0x8e037fc000fbe000 0x0063ff6000ffb000

def z240 : W := mkw 0x0000000000000000 0xb000000000b009c0

def z241 : W := mkw 0x00200020c5041305 0x71d009e9cc4cf60c

def z242 : W := mkw 0x8003bfd828000000 0x0bf3fff83c000000

def z243 : W := mkw 0x00200020c5041305 0xb6d00969cc4cb70c

def z244 : W := mkw 0x0020002085001005 0xff9801e00f00f10f

def z245 : W := mkw 0x0d80400040ec0f80 0xb6b4301600fc0fc0

def z246 : W := mkw 0x00200020c5041305 0xfffc39ffcffcffcf

def z247 : W := mkw 0x020000000013e000 0x400000000003f000

def z248 : W := mkw 0x8e237fe085fbf005 0x79fbffe00ffff00f

def z249 : W := mkw 0x4da2e83dc5ec1f85 0x0043c969cc4cb60c

def z250 : W := mkw 0x4180801d40040f80 0xb6d4081fc04c0fc0

def z251 : W := mkw 0xf007bfffbf000000 0xdfffffffff830830

def z252 : W := mkw 0xf247bfffbf114052 0x0ff7ffffffb308f0

def z253 : W := mkw 0x80033fc000000000 0x0023f60000000000

def z254 : W := mkw 0x4002a81d00000000 0x0027f01600000000

def z255 : W := mkw 0x8c037fc000eaa000 0x01f3ffe0004cb000

def z256 : W := mkw 0x0000000000000000 0x30b0300000b00000

def z257 : W := mkw 0x2240128212114052 0xdb38069033834833

def z258 : W := mkw 0x4002280500000000 0x04843807c0000000

def z259 : W := mkw 0xfb47ffffbfd3cc7a 0xfffffffffff3cfff

def z260 : W := mkw 0x4d82e81d40ec0f80 0xfffffe1ff0ff0ff0

def z261 : W := mkw 0x2901d79a3ac28c28 0xdffff79e3fc38e3c

def z262 : W := mkw 0x0000000000000000 0xd00800000040860c

def z263 : W := mkw 0x8e037fe085fbe000 0x7ff3ffe9cffff000

def z264 : W := mkw 0xf007bfffff040300 0xbff7ffffff4c0700

def z265 : W := mkw 0x0901450028c28c28 0xd90807003cc38e3c

def z266 : W := mkw 0x0000000000000000 0xffd809e0034cf103

def z267 : W := mkw 0x0000000000000000 0x7190008000004000

def z268 : W := mkw 0xf007bfffbf000000 0x0067ff7ffc000000

def z269 : W := mkw 0x0000000000000000 0x8a0800080c00060c

def z270 : W := mkw 0xfda7ffffffec1f85 0xfffffffffffcffcf

def z271 : W := mkw 0x0000000000000000 0x06b4301600000000

def z272 : W := mkw 0x4d82e81d40ec0f80 0x24c7f80fc07c07c0

def z273 : W := mkw 0x8e037fc000fbe000 0x4123f7e000b3f000

def z274 : W := mkw 0x01208038ed041f2d 0x8e080019ff000f3f

def z275 : W := mkw 0x0000000040040300 0x86000009c0000700

def z276 : W := mkw 0x44a22825c52c1385 0x248438e7c33c71c3

def z277 : W := mkw 0xf207bfffbf13e000 0x4ff7ffffff03f000

def z278 : W := mkw 0x0001851828000000 0x0023c61030000000

def z279 : W := mkw 0x0000000000000000 0x9250000800400600

def z280 : W := mkw 0xfd87ffffffec0f80 0xbff7fffffffc0fc0

def z281 : W := mkw 0x4c02e81d00e80000 0x36f7f81fc0fc0000

def z282 : W := mkw 0x0001851828000000 0x0043c1080c000000

def z283 : W := mkw 0x00200020c5041305 0xf90801e00f4cf70f

def z284 : W := mkw 0x4d82e81d40ec0f80 0x0067f81fc0fc0ec0

def z285 : W := mkw 0x0801450000c28000 0xdb7bc7080cc3860c

def z286 : W := mkw 0xd007ad7dad000000 0x0b73cf79fc000000

def z287 : W := mkw 0xce837fc540ffe380 0x75f7ffe7c0fff1c0

def z288 : W := mkw 0x2000000212000000 0x0e04001633000000

def z289 : W := mkw 0x80033fe085000000 0x0ff3ffe9cf000000

def z290 : W := mkw 0x7004803fbf000000 0x0fd409ffff000000

def z291 : W := mkw 0x8e036d4000fbe000 0x7043c96000fff000

def z292 : W := mkw 0xf907ffdf3ac28c28 0x0027f61630830830

def z293 : W := mkw 0x0e027a8000f94000 0x71f3fe8000ff4000

def z294 : W := mkw 0x0c02680000e80000 0xb6f7f81600fc09c0

def z295 : W := mkw 0x0020002085001005 0x000000e003007003

def z296 : W := mkw 0x0901c51828c28c28 0x8a2bc6183c830e3c

def z297 : W := mkw 0x822117e0c517f305 0xffd80fe9cf4ff70f

def z298 : W := mkw 0x0000000000000000 0x00400960004cb000

def z299 : W := mkw 0x0240000000114052 0xff98008003b349f3

def z300 : W := mkw 0x90050560ad000000 0x000001600c000000

def z301 : W := mkw 0x0901c51828c28c28 0xd04bc1080cc38e3c

def z302 : W := mkw 0x7004002797000000 0x04040007c3000000

def z303 : W := mkw 0xf907ffffbfc28c28 0x0ff7ffffff40860c

def z304 : W := mkw 0x820117c02813e028 0x490807e03c03f03c

def z305 : W := mkw 0x8c036d4000eaa000 0x71d3c9e0004cf000

def z306 : W := mkw 0x5004803dad000000 0x00000009cc000000

def z307 : W := mkw 0x0da0400040ec1f85 0xf008000000fcffcf

def z308 : W := mkw 0x0020002085001005 0x080800000f00000f

def z309 : W := mkw 0xc6823ac5403d6380 0x248438e7c03c71c0

def z310 : W := mkw 0x0000000000000000 0xffd801880f40c70f

def z311 : W := mkw 0x4902e81d00c00c00 0x96f7f81fc0c00e00

def z312 : W := mkw 0x0001851828028028 0x4b7bc7183c03803c

def z313 : W := mkw 0x00200020c5041305 0x494809e9cf4cf60f

def z314 : W := mkw 0x7024803fff041305 0xffdc09ffff4cf70f

def z315 : W := mkw 0x4d82e81d40ec0f80 0x24a7f817c0bc09c0

def z316 : W := mkw 0x00200020c5041305 0x04000001c3000103

def z317 : W := mkw 0xce03ffdd00fbe000 0x77f7ffffc0fff000

def z318 : W := mkw 0x8e237fe0c5fff305 0x75f3ffe1c3fff103

def z319 : W := mkw 0x8c036d4000eaa000 0x30f3f96000fcb000

def z320 : W := mkw 0x4da2e81d40ec1f85 0xf6fff81fc0fcffcf

def z321 : W := mkw 0xefc3ffdf52ffefd2 0xfffffffff3fffff3

def z322 : W := mkw 0x0020000040041305 0xff980080034cf70f

def z323 : W := mkw 0xf247bfffbf114052 0x2ff7ffffff3041c3

def z324 : W := mkw 0x0920c038c5c41f05 0xfffbc9f9cfccff0f

def z325 : W := mkw 0x00210520ad02902d 0x490807e03f03f03f

def z326 : W := mkw 0x4180801d68040fa8 0x8e0c001ffc000ffc

def z327 : W := mkw 0x0000000040040300 0xffd80889c34c4703

def z328 : W := mkw 0x00200020c5041305 0x00000009cc00060c

def z329 : W := mkw 0x0d81c51868ee8fa8 0xfb7bc7183cff8ffc

def z330 : W := mkw 0x00200020c5041305 0xdb580969cc4cb60c

def z331 : W := mkw 0xcf83ffdd00fbec80 0x0027f61600b308c0

def z332 : W := mkw 0x4d82e81d40ec0f80 0xfffff89fc3fc4fc3

def z333 : W := mkw 0x0900400000c28c28 0x000000000040860c

def z334 : W := mkw 0x7104803fbf000c28 0x8e0c001fff000e3c

def z335 : W := mkw 0x0000000000000000 0xd008000000830830

def z336 : W := mkw 0x0900400000c28c28 0x0000000000830830

def z337 : W := mkw 0xf027bfffff041305 0x8fffffffff00070f

def z338 : W := mkw 0xfe07ffdf3afbe000 0x0027f61630b30000

def z339 : W := mkw 0xf907ffffbfc28c28 0xdfffffffffc38e3c

def z340 : W := mkw 0x4d83ed1d28ea8ca8 0x0027f61630b308f0

def z341 : W := mkw 0x80032d4000000000 0x0043c96000000000

def z342 : W := mkw 0x0901c51828c28c28 0x0063c7183cc38e3c

def z343 : W := mkw 0x8e037fc000fbe000 0x01f3ffe000b30000

def z344 : W := mkw 0x4d82e81d40ec0f80 0xb6d3c809c04c0700

def z345 : W := mkw 0x4d82e81d00e80c80 0x06f7f81fc0b008c0

def z346 : W := mkw 0x202012a2d7041305 0xfffc3fffff4cf70f

def z347 : W := mkw 0xd907ed7dadc28c28 0xdb7bcf79fcc38e3c

def z348 : W := mkw 0x0901c51828c28c28 0x9273c1180cc08e0c

def z349 : W := mkw 0xb24517e2bf114052 0x490807e03f034033

def z350 : W := mkw 0x00018538ad000000 0x0ff3cff9ff000000

def z351 : W := mkw 0xf0263ae7d7041305 0xffdc39efcf4cf70f

def z352 : W := mkw 0x2240128212114052 0xff9c3086033041c3

def z353 : W := mkw 0x0901c51800c28c00 0xd373c71800c38e00

def z354 : W := mkw 0x0000000000000000 0xf008000000004103

def z355 : W := mkw 0xae037fc212fbe000 0x7ff7fff633fff000

def z356 : W := mkw 0x0000000000000000 0xdb18000000000000

def z357 : W := mkw 0x0e00400000fbe000 0x71d009e000fff000

def z358 : W := mkw 0x8e037fc000fbe000 0x20c3f9e0007cf000

def z359 : W := mkw 0xfc07ffffbfeaa000 0x0ff7ffffff4cb000

def z360 : W := mkw 0x0020002085001005 0x4fd809e9cf00f00f

def z361 : W := mkw 0xb00517e2bf000000 0x0fb437f63f000000

def z362 : W := mkw 0xcfa3fffdc5ffff85 0xffffffffcfffffcf

def z363 : W := mkw 0xb02517e2bf001005 0x490807e03f00f00f

def z364 : W := mkw 0x4d83ed1d68ee8fa8 0xb6f7fe1ff0ff0ff0

def z365 : W := mkw 0x0901c51868c68f28 0xfffbcf19fccf8f3c

def z366 : W := mkw 0x00200020c5041305 0xfff80ff9ffcfff3f

def z367 : W := mkw 0x4d82e81d40ee8fa8 0xf6fff81fc0ff8ffc

def z368 : W := mkw 0x02600020c5155357 0xffd809e9cfffffff

def z369 : W := mkw 0x2b41d79a3ad3cc7a 0xffbff69633b349f3

def z370 : W := mkw 0x0000000000000000 0xb690000000000100

def z371 : W := mkw 0x0901c51828c28c28 0x9273c61830c30e30

def z372 : W := mkw 0x4d83ed1d68ec0f80 0xbff7ff1ffcfc0fc0

def z373 : W := mkw 0xf007bfffbf000000 0x0927f7f63f000000

def z374 : W := mkw 0xf007bfffbf000000 0x04a7fef7f3000000

def z375 : W := mkw 0x0b41c51828d3cc7a 0xfb7bc7183cf3cfff

def z376 : W := mkw 0x0901c51828c28c28 0xdb5bc1080c40860c

def z377 : W := mkw 0x0801450000c28000 0x0043c10000408000

def z378 : W := mkw 0x0f01c51828fbec28 0xfb7bc7183cfffe3c

def z379 : W := mkw 0x4da2e83dc5ec1f85 0xbefff81fcffc0fcf

def z380 : W := mkw 0x2240128212114052 0x2fb43696333041c3

def z381 : W := mkw 0x0800400000c28000 0x5000000000c38000

def z382 : W := mkw 0xb00517e2bf028028 0x490807e03f03803c

def z383 : W := mkw 0x0000002085000000 0xffd809e9cf004103

def z384 : W := mkw 0x0900c01800c00c00 0x0023c01000800800

def z385 : W := mkw 0x8d03ed5828eaac28 0x0043c9680c4cb60c

def z386 : W := mkw 0x2240128212114052 0xfffc379e3ff3cfff

def z387 : W := mkw 0x2240128212114052 0xff98068033034133

def z388 : W := mkw 0x0001050000028000 0x4100070000038000

def z389 : W := mkw 0x0000000000000000 0x4908060030030030

def z390 : W := mkw 0xf267bfffff155357 0xffffffffffffffff

def z391 : W := mkw 0xf006baff97000000 0x06f7f8ffc3000000

def z392 : W := mkw 0xae437fc212fbe052 0x0027f61630b308f0

def z393 : W := mkw 0x4000801d00000000 0x0604001fc0000000

def z394 : W := mkw 0x800105400002a000 0x000001600000b000

def z395 : W := mkw 0x0100000000000c28 0x8008000000000e3c

def z396 : W := mkw 0xd027ad7ded041305 0xffdbc9e9cf4cf70f

def z397 : W := mkw 0x0200128000114000 0x0020360000b30000

def z398 : W := mkw 0x4482280500280080 0x00043006003000c0

def z399 : W := mkw 0x0000000040040300 0xb0000000004c0700

def z400 : W := mkw 0x0000000000000000 0x8a08001030000830

def z401 : W := mkw 0x4d83ed1d68ee8fa8 0xdb7bcf19fccf8e3c

def z402 : W := mkw 0x0801450028c28028 0x597bc7003cc3803c

def z403 : W := mkw 0x6fc2fa9f12f94cd2 0x0027f61630b308f0

def z404 : W := mkw 0x0b01d79828d3cc28 0xfbfbf7983cf3ce3c

def z405 : W := mkw 0x2240128212114052 0x79b8368033b34033

def z406 : W := mkw 0x0da04020c5ec1f85 0xffd809e9cffcffcf

def z407 : W := mkw 0x4d83ed1d68ee8fa8 0xb6f7f91fccfc8fcc

def z408 : W := mkw 0x00200020c5041305 0x0fd009e9cf4cb60c

def z409 : W := mkw 0x2040000212000052 0xbebc301633b009f3

def z410 : W := mkw 0xd007ad7dad000000 0x0fd3c9e9cf000000

def z411 : W := mkw 0x0c226820c5ec1305 0xfffbf9e9cffcf70f

def z412 : W := mkw 0x0000002085000000 0xdfd809e9cf40860c

def z413 : W := mkw 0xc003bfdd00000000 0x07f7ffffc0000000

def z414 : W := mkw 0xb00517e2bf000000 0x0fd00fe9ff000000

def z415 : W := mkw 0x0000000000028028 0x400800000003803c

def z416 : W := mkw 0xffc7fffffffd4fd2 0xffffffffffff4ff3

def z417 : W := mkw 0x7044803fbf000052 0x8e0c001fff0009f3

def z418 : W := mkw 0xfe077fe797fbe000 0x75f7ffe7c3fff000

def z419 : W := mkw 0x0c02680000e80000 0x0043c800004c0000

def z420 : W := mkw 0x0000000000000000 0xffbc361630b309f0

def z421 : W := mkw 0x0101851828028c28 0xcb0807183c038e3c

def z422 : W := mkw 0xf027bfffff041305 0x0ff7ffffff4cb60c

def z423 : W := mkw 0xf007bfffbf000000 0x0943cfe9ff000000

def z424 : W := mkw 0x8e037fc000fbe000 0x7023f60000fff000

def z425 : W := mkw 0xdd87ed7dedec0f80 0x0043c969cc4c0600

def z426 : W := mkw 0x7d86e83fffec0f80 0xbef7f81ffffc0fc0

def z427 : W := mkw 0x0020000040041305 0x20000000000c7103

def z428 : W := mkw 0x6fc2fa9f52fd4fd2 0xb6f7fe1ff0ff0ff0

def z429 : W := mkw 0x2040000212000052 0xff9c0096330049f3

def z430 : W := mkw 0x0d80400040ec0f80 0xb6d00809c0fc0fc0

def z431 : W := mkw 0x2240128212114052 0x75b4368603b341c3

def z432 : W := mkw 0x8c037fc000e80000 0x31f3ffe000fc0000

def z433 : W := mkw 0x6fc2fa9f52fd4fd2 0xb6f7f89fc3fc4fc3

def z434 : W := mkw 0x8e037fc000fbe000 0xfffbffe003fff103

def z435 : W := mkw 0x0020002085001005 0x000001600c00b00c

def z436 : W := mkw 0xcf83ffdd40ffef80 0xb6f7fe1fc0ff0fc0

def z437 : W := mkw 0x0100801828000c28 0x000000080c00060c

def z438 : W := mkw 0xfc07ffffbfe80000 0x3ff7fffffffc0000

def z439 : W := mkw 0x4981c51d68c68fa8 0xdf7fc71ffcc38ffc

def z440 : W := mkw 0x2000128212000000 0x0024361630000000

def z441 : W := mkw 0x0901c51828c28c28 0x0b73c7183c830830

def z442 : W := mkw 0x0000002085000000 0x00400969cc000000

def z443 : W := mkw 0xae437fc212fbe052 0x75f7ffe603fff1c3

def z444 : W := mkw 0x0000000000000000 0xfbd809e80c4cf60c

def z445 : W := mkw 0x01208038ed041f2d 0xffd809f9ff4cff3f

def z446 : W := mkw 0xd007bffdad000000 0x01f3ffe9cc000000

def z447 : W := mkw 0x00200020c5041305 0x00000861c00c3000

def z448 : W := mkw 0xcf83ffdd68ffefa8 0xfffffffffcfffffc

def z449 : W := mkw 0x0000000040040300 0xf7d009e9c04cf700

def z450 : W := mkw 0x0000000000000000 0xffb8069033834933

def z451 : W := mkw 0x0801450000c28000 0x0023c60000830000

def z452 : W := mkw 0x0921c51868c69f2d 0xfb7bc7183ccfff3f

def z453 : W := mkw 0x0001050000000000 0x0173c70000000000

def z454 : W := mkw 0xf027bfffff041305 0x2ff7ffffff0c7103

def z455 : W := mkw 0x0801450000c28000 0x71f3cfe000cff000

def z456 : W := mkw 0x2e40528212fbe052 0xffbc369633fff9f3

def z457 : W := mkw 0xf007bfdf3a000000 0x0b77f71e3c000000

def z458 : W := mkw 0x00200020c5041305 0xff980089cf00470f

def z459 : W := mkw 0x0000000040040300 0xffd80909cc4c870c

def z460 : W := mkw 0x4080000540040380 0x04040007c00001c0

def z461 : W := mkw 0x4da2e83dc5ec1f85 0xffdbc9e9cf4cf70f

def z462 : W := mkw 0x2fc0528252fd4fd2 0xffbc369633ff4ff3

def z463 : W := mkw 0x0900c01800c28c28 0xd27bc01800c38e3c

def z464 : W := mkw 0x4002a83d85000000 0x0ff7f9ffcf000000

def z465 : W := mkw 0x66c23a87523d43d2 0xffbc3e97f3bf49f3

def z466 : W := mkw 0x2240128212114052 0xdb3c361630b308f0

def z467 : W := mkw 0x0901c51828c28c28 0x5173c71030c38830

def z468 : W := mkw 0x0001050028000000 0x090007003c000000

def z469 : W := mkw 0x0200128000114000 0x71f03fe000fff000

def z470 : W := mkw 0xa6423ac212396052 0xffbc3ef633bf79f3

def z471 : W := mkw 0xb24517e2bf114052 0xffbc37f63fb349f3

def z472 : W := mkw 0x8f837fc040ffef80 0xf1f3ffe000ffffc0

def z473 : W := mkw 0xb02517e2ff041305 0xffd80fe9ff4cf70f

def z474 : W := mkw 0x8c036d4000eaa000 0x0003c00000000000

def z475 : W := mkw 0x00200020c5041305 0x6d8809e1cf0cf10f

def z476 : W := mkw 0xd007ad7dad000000 0x06f7f97fcc000000

def z477 : W := mkw 0xff87ffffffffef80 0xfff7ffffffffffc0

def z478 : W := mkw 0x8f23fff8edffff2d 0xfffbfff9ffffff3f

def z479 : W := mkw 0x0020002085001005 0x79d809e00f4cf00f

def z480 : W := mkw 0x8e237fe0c5fff305 0x71f3ffe9ccfff60c

def z481 : W := mkw 0x0901c538adc28c28 0xdffbcff9ffc38e3c

def z482 : W := mkw 0xff07ffffbffbec28 0xfffffffffffffe3c

def z483 : W := mkw 0x00200020c5041305 0x75d009e1c34cf103

def z484 : W := mkw 0x00200020c5041305 0x8e480969cf4cb70f

def z485 : W := mkw 0xf807ffffbfc28000 0x5ff7ffffffc38000

def z486 : W := mkw 0x4d82e81d40ec0f80 0x06f7f81fc04c0600

def z487 : W := mkw 0x0000000000000000 0x24843006003001c0

def z488 : W := mkw 0x8e037fc000fbe000 0x30f3fe0000ff0000

def z489 : W := mkw 0x2b41d79a3ad3cc7a 0x0027f61630b308f0

def z490 : W := mkw 0x00200020c5041305 0x2fd009e9cf0c7103

def z491 : W := mkw 0xa0033fc212000000 0x0ff7fff633000000

def z492 : W := mkw 0x2240128212114052 0xb6b4309603b049c3

def z493 : W := mkw 0x4d82e81d68ec0fa8 0xbefff81ffcfc0ffc

def z494 : W := mkw 0xf0073fe797000000 0x05f7ffe7c3000000

def z495 : W := mkw 0xfe07ffdf3afbe000 0x71f7fff630fff000

def z496 : W := mkw 0x0900400000c00c00 0x9000000000c00e00

def z497 : W := mkw 0x0c00400000eaa000 0x00000000004cb000

def z498 : W := mkw 0x0921c538edc69f2d 0x0043c969cc4cb60c

def z499 : W := mkw 0x4d82e81d40ec0f80 0xb027f01600fc0fc0

def z500 : W := mkw 0x0001050028028028 0x000001000c00800c

def z501 : W := mkw 0xfd86faffd7ec0f80 0xb6f7f8ffc3fc0fc0

def z502 : W := mkw 0x63c0929f52154fd2 0xffbc369ff3b34ff3

def z503 : W := mkw 0x0d80400000e80c80 0x0000000000b008c0

def z504 : W := mkw 0x7184803fff040f80 0x8e04001fff000fc0

def z505 : W := mkw 0x0c036d0000ea8000 0x71f3ff0000ff8000

def z506 : W := mkw 0x0c02680000e80000 0x0023f00000b00000

def z507 : W := mkw 0x0000000000000000 0x4908008003004003

def z508 : W := mkw 0x226012a2d7155357 0xffdc39efcf7cf7cf

def z509 : W := mkw 0x800117c000000000 0x010007e000000000

def z510 : W := mkw 0x226012a297115057 0x490807e03f03f03f

def z511 : W := mkw 0x4980c01d40c40f80 0x9677c01fc0c00fc0

def z512 : W := mkw 0x2000128212000000 0xbfb4369633b009c0

def z513 : W := mkw 0x0000000000000000 0x8e08000003000103

def z514 : W := mkw 0x0100801828000c28 0xdb5801183c408e3c

def z515 : W := mkw 0x0260000040155357 0xf008000000ffffff

def z516 : W := mkw 0xf6063ae797396000 0x248438e7c33c7000

def z517 : W := mkw 0x0000000000000000 0x2480008003004103

def z518 : W := mkw 0x0001050028028028 0xdb3807103c83883c

def z519 : W := mkw 0x4d82e81d40ec0f80 0x8647c81fc04c0fc0

def z520 : W := mkw 0x0000000000000000 0x0f90008003000000

def z521 : W := mkw 0x00210520ed06932d 0xffd80fe9ff4ff73f

def z522 : W := mkw 0x226012a297115057 0xffbc37f63fb3f9ff

def z523 : W := mkw 0xfd87ffdf3ae80c80 0x0027f61630b008c0

def z524 : W := mkw 0x0240000000114052 0xf6bc301600b349f3

def z525 : W := mkw 0x200012a297000000 0x0ff43fffff000000

def z526 : W := mkw 0xb00517c23a000000 0x0000060030000000

def z527 : W := mkw 0x20600022d7041357 0x8e0c001fff000fff

def z528 : W := mkw 0x0c02680040ec0300 0xb6f3f809c0fc0700

def z529 : W := mkw 0x8e037fc000fbe000 0x20a3fee000bf7000

def z530 : W := mkw 0xd907ed7dadc28c28 0x0043c969cc40860c

def z531 : W := mkw 0xb20517e2bf13e000 0x490007e03f03f000

def z532 : W := mkw 0x8f03ffd828fbec28 0x0023f61030b30830

def z533 : W := mkw 0x0801450000c28000 0xdb7bc71030c38830

def z534 : W := mkw 0xfe47ffffbffbe052 0xfffffffffffff9f3

def z535 : W := mkw 0x4182a81d40040f80 0x86f7f81fc0000fc0

def z536 : W := mkw 0x0c02680000e80000 0x71f3f9e000fcf000

def z537 : W := mkw 0x4d82e81d00e80c80 0x9277f01e00f00ec0

def z538 : W := mkw 0x2040000212000052 0x0808000033000033

def z539 : W := mkw 0x2240000212114052 0xfe0c001633b349f3

def z540 : W := mkw 0x86023ac000396000 0x71b03ee000bf7000

def z541 : W := mkw 0x0200000000114000 0x7000000000b34000

def z542 : W := mkw 0x2040128212000052 0x8fbc3696330009f3

def z543 : W := mkw 0x0901c51828c28c28 0x0003c00000000000

def z544 : W := mkw 0xf487bfffff2c0380 0x2ff7ffffff3c01c0

def z545 : W := mkw 0x0000002085000000 0x048008e1c3000000

def z546 : W := mkw 0x4180801d00000c80 0x00040016000008c0

def z547 : W := mkw 0xfd87ffffffec0f80 0x0ff7ffffff4c0600

def z548 : W := mkw 0x2260128252155357 0xffbc369633ffffff

def z549 : W := mkw 0x0000000000000000 0xffbc309603b049c3

def z550 : W := mkw 0x4d80c01d40ec0f80 0xb604001fc0fc0fc0

def z551 : W := mkw 0xf247bfdf3a114052 0x0027f61630b308f0

def z552 : W := mkw 0x00000020c5040300 0xbfd009e9cf4c0700

def z553 : W := mkw 0xcd83ffdd40ec0f80 0xb7f7ffffc0fc0fc0

def z554 : W := mkw 0xb00412e297000000 0x000000e003000000

def z555 : W := mkw 0x4180801d40040f80 0xb6b4301fc0b00fc0

def z556 : W := mkw 0x0901c51828c28c28 0x0b73c7183c40860c

def z557 : W := mkw 0x7006a83fbf000000 0x0ef7f81fff000000

def z558 : W := mkw 0x226012a2d7155357 0xffbc369fffb34fff

def z559 : W := mkw 0x2040000212000052 0x04040006030001c3

def z560 : W := mkw 0x88037fc000c28000 0x51f3ffe000c38000

def z561 : W := mkw 0xf907ffdf3ac28c28 0xdb7ff71e3cc38e3c

def z562 : W := mkw 0x820117c00013e000 0x71d00fe0004ff000

def z563 : W := mkw 0x0100801800000c00 0x8200001800000e00

def z564 : W := mkw 0xf007bfffbf000000 0x7ff7ffffff4cf000

def z565 : W := mkw 0x4582a81d402c0f80 0xa684381fc03c0fc0

def z566 : W := mkw 0x820117c00013e000 0x0000060000030000

def z567 : W := mkw 0x0000002085000000 0x0e000009cf000000

def z568 : W := mkw 0x00218538ed041305 0xfffbcff9ff4cf70f

def z569 : W := mkw 0x0000000000000000 0x208008e0000c7000

def z570 : W := mkw 0x0921c538adc29c2d 0xdb7bc7f83fc3fe3f

def z571 : W := mkw 0xdc07ed7dadeaa000 0x0043c969cc4cb000

def z572 : W := mkw 0x4c82680540ec0380 0x34f7f807c0fc01c0

def z573 : W := mkw 0x0801c51828c28000 0x5b73c7183cc38000

def z574 : W := mkw 0xd027ad7ded041305 0x0043c969cc4cb60c

def z575 : W := mkw 0x0900c01840c40f00 0xb6f3c819c0cc0f00

def z576 : W := mkw 0x0000000000000000 0x004001080c40860c

def z577 : W := mkw 0x2240128212114052 0x4fbc369633034033

def z578 : W := mkw 0x7004801f3a000000 0x0004001630000000

def z579 : W := mkw 0x8f03ffd800fbec00 0xf3f3fff800fffe00

def z580 : W := mkw 0x0040000000000052 0x80080000000009f3

def z581 : W := mkw 0xf007bfffbf000000 0xffffffffff004103

def z582 : W := mkw 0x0000000028000028 0x080800003c00003c

def z583 : W := mkw 0x0101851828000c28 0x8b7bc7183c000e3c

def z584 : W := mkw 0x0000000040040300 0x24800801c00c0100

def z585 : W := mkw 0x8903ffd828c28c28 0xdbfbfff83cc38e3c

def z586 : W := mkw 0x0000000000000000 0x70000000004cf000

def z587 : W := mkw 0x4da2e83dc5ec1f85 0xb6f7f97fccfcbfcc

def z588 : W := mkw 0x0000000000000000 0x30d00800004c0000

def z589 : W := mkw 0x2000128212000000 0x0484308603000000

def z590 : W := mkw 0x0000000040040300 0x00400809c04c0600

def z591 : W := mkw 0x0100801828000c28 0xdb3806183c830e3c

def z592 : W := mkw 0x2240128212114052 0x492c369633b348f3

def z593 : W := mkw 0x82033fc000114000 0x71f3ffe000b34000

def z594 : W := mkw 0x0000000000000000 0xdb7807183cc38e3c

def z595 : W := mkw 0x4f82e81d40ffef80 0xf6f7f81fc0ffffc0

def z596 : W := mkw 0x8f03ffd828fbec28 0xdb7bf7183cf38e3c

def z597 : W := mkw 0x6fc3ff9f7affcffa 0xffffff9fffffcfff

def z598 : W := mkw 0x0901c51828c28c28 0xdb3bc61030830830

def z599 : W := mkw 0xf00597ffbf000000 0x0f0407ffff000000

def z600 : W := mkw 0x04800000402c0380 0x20000000003c01c0

def z601 : W := mkw 0x86223ae0c53d7305 0xffd839e9cf7cf70f

def z602 : W := mkw 0x6fc2fa9f12f94cd2 0xffbff69633b349f3

def z603 : W := mkw 0x2b40528212d3cc7a 0xffbc369633f3cfff

def z604 : W := mkw 0xf907ffffbfc00c00 0x9ff7ffffffc00e00

def z605 : W := mkw 0x6d82fa9f52ec0f80 0xbff7fe9ff3fc0fc0

def z606 : W := mkw 0x2240128212114052 0x0000008003004003

def z607 : W := mkw 0x0000000040040300 0xb6f4381fc0fc0fc0

def z608 : W := mkw 0x0800400000c00000 0x1073c00000c00000

def z609 : W := mkw 0xcf82fadd40fd6f80 0xb6f7f8ffc0fc7fc0

def z610 : W := mkw 0x0901c51828c28c28 0x8a4bc1183c408e3c

def z611 : W := mkw 0x0240128000114052 0xf1b8368000b349f3

def z612 : W := mkw 0x0900c01828c28c28 0xda0800183cc38e3c

def z613 : W := mkw 0x8f03ffd828fbec28 0x71f3ffe80cfff60c

def z614 : W := mkw 0xbe077fe2bffbe000 0x79f3ffe03ffff000

def z615 : W := mkw 0x4da2e83dc5ec1f85 0xb6f7f8ffc3fc7fc3

def z616 : W := mkw 0x2000128212000000 0x0900068033000000

def z617 : W := mkw 0x0000000000000000 0x01d009e000000000

def z618 : W := mkw 0x80233fe0c5041305 0xfffbffe9cf4cf70f

def z619 : W := mkw 0x2240128212114052 0x0fb4369633b308f0

def z620 : W := mkw 0x2b40d29a12d14c52 0xfffff69e33f34ff3

def z621 : W := mkw 0xf0073fe7bf000000 0x0d843fe7ff000000

def z622 : W := mkw 0x0000000000000000 0x490801000c00800c

def z623 : W := mkw 0x0901c51828c28c28 0xd02bc61030c38e3c

def z624 : W := mkw 0x8e0157c000fbe000 0x710007e000fff000

def z625 : W := mkw 0x8c236d60c5eeb305 0x0043c969cc4cb60c

def z626 : W := mkw 0xa6423ac212396052 0x248438e6033c71c3

def z627 : W := mkw 0x8e03ffd828fbe000 0x7bf3fff83cfff000

def z628 : W := mkw 0x0000000000000000 0x5150010000408000

def z629 : W := mkw 0x8a0157c000d3e000 0x5173c7e000c3f000

def z630 : W := mkw 0x0240000000114052 0x4008000000034033

def z631 : W := mkw 0xf907ffffbfc28c28 0x0ff7ffffff830830

def z632 : W := mkw 0x224117823a13c07a 0x490807803f03c03f

def z633 : W := mkw 0x00200020c5041305 0xf48808e1c34cf70f

def z634 : W := mkw 0x2240128212114052 0xcf0c0696330349f3

def z635 : W := mkw 0x44a22825c52c1385 0xffdc39efcf7cf7cf

def z636 : W := mkw 0x0000801828000000 0x0a0000183c000000

def z637 : W := mkw 0x8e037fc000fbe000 0x5173f70000f38000

def z638 : W := mkw 0x0200128000114000 0xffb8368003b34103

def z639 : W := mkw 0xcf83ffdd00fbec80 0x71f7fff600fff8c0

def z640 : W := mkw 0x0100801828000c28 0x0000001030000830

def z641 : W := mkw 0x0240000000114052 0x0000000000b308f0

def z642 : W := mkw 0x0020000040041305 0x800800000000070f

def z643 : W := mkw 0x0921c538edc69f2d 0xffdbc9e9cf4cf70f

def z644 : W := mkw 0x0020000040041305 0xf6d80809c04cf70f

def z645 : W := mkw 0x2240128212114052 0xf02c361630b349f3

def z646 : W := mkw 0x0900c01800c00c00 0xb6f7f01e00f00fc0

def z647 : W := mkw 0x80023ac000000000 0x008038e000000000

def z648 : W := mkw 0x820117c00013e000 0x71b037e000b3f000

def z649 : W := mkw 0x4d82e83dc5ec0f80 0xbff7f9ffcffc0fc0

def z650 : W := mkw 0x8b01d7d828d3ec28 0xdb7bc7f83cc3fe3c

def z651 : W := mkw 0x0901c51828c00c00 0x9b73c7183cc00e00

def z652 : W := mkw 0x0000000000000000 0x9230001000800800

def z653 : W := mkw 0x0e01450000fbe000 0x7173c70000fff000

def z654 : W := mkw 0xf2463ae797114052 0xffbc3ef7f3b349f3

def z655 : W := mkw 0x2a41578212d3c052 0xfffff79633f3c9f3

def z656 : W := mkw 0xfe07ffffbffbe000 0x0ff7ffffffb30000

def z657 : W := mkw 0x224012a297114052 0xfffc3fffffb349f3

def z658 : W := mkw 0x66c23a87523d43d2 0x24843887c33c41c3

def z659 : W := mkw 0x2340929a3a114c7a 0xffbc369e3fb34fff

def z660 : W := mkw 0x44822805402c0380 0x00000801c00c0000

def z661 : W := mkw 0x2000128212000000 0xffbc369633004103

def z662 : W := mkw 0x4d82e81d00e80c80 0x0003c00000000000

def z663 : W := mkw 0x4f82fa9d40fd4f80 0xf7f7fe9fc0ff4fc0

def z664 : W := mkw 0x44822805402c0380 0xb6b43817c0bc09c0

def z665 : W := mkw 0x0200128000114000 0x2080308000304000

def z666 : W := mkw 0x0e204020c5fff305 0xffd809e9cffff70f

def z667 : W := mkw 0xf187bfffff040f80 0x8ff7ffffff000fc0

def z668 : W := mkw 0x0921c538edc69f2d 0xdf7bc719ffc38f3f

def z669 : W := mkw 0x0a01578000d3c000 0x71f3f78000f3c000

def z670 : W := mkw 0x4da3ed3dedee9fad 0xffffffffffffffff

def z671 : W := mkw 0x0000000000000000 0x0020061030830830

def z672 : W := mkw 0x2240128252154352 0xfffc3e9ff3ff4ff3

def z673 : W := mkw 0x0000000000000000 0x410001e00000f000

def z674 : W := mkw 0x4d82e81d00e80c80 0xb6b7f01600b009c0

def z675 : W := mkw 0xcf83ffdd40ffef80 0x71f3ffe9c0fff600

def z676 : W := mkw 0x4d83ed1d68ee8fa8 0x0043c909cc4c860c

def z677 : W := mkw 0x2240128212114052 0xb6b4361630b309f0

def z678 : W := mkw 0x0e02680000fbe000 0x70f3f80000fff000

def z679 : W := mkw 0x0d80c01840ec0f80 0xb273c01800fc0fc0

def z680 : W := mkw 0x0200128000114000 0xf7b4369600b349c0

def z681 : W := mkw 0x0000002085000000 0x090001e00f000000

def z682 : W := mkw 0x0900c01800c00c00 0x0043c00800400600

def z683 : W := mkw 0x022012a0c5155305 0xfff83fe9cffff70f

def z684 : W := mkw 0x0000002085000000 0x7fd009e9cf4cf000

def z685 : W := mkw 0x0900400000c28c28 0xdb5801080cc38e3c

def z686 : W := mkw 0xf0263ae7d7041305 0x248438e7c30c7103

def z687 : W := mkw 0x0000000000000000 0x0b30061030000000

def z688 : W := mkw 0x0000000000000000 0x0b5001080c000000

def z689 : W := mkw 0x8e237fc040fff305 0xf1fbffe000fff70f

def z690 : W := mkw 0x4d82e81d40ec0f80 0x9273c819c0cc0e00

def z691 : W := mkw 0x2b61d7baffd7df7f 0xffffffffffffffff

def z692 : W := mkw 0xa24117c21213e052 0xffbc37f633b3f9f3

def z693 : W := mkw 0x00200020c5041305 0xae8808e9cf0c770f

def z694 : W := mkw 0x86223ae0c53d7305 0x248038e1c33c7103

def z695 : W := mkw 0x224117823a13c07a 0xffbc37963fb3c9ff

def z696 : W := mkw 0x0000000000000000 0x5130060000830000

def z697 : W := mkw 0x4d82e81d00e80c80 0x30f7f81600fc08c0

def z698 : W := mkw 0x00200020c5041305 0xb6d008e9c34c7703

def z699 : W := mkw 0x0001050028028028 0xdb5807083c43863c

def z700 : W := mkw 0x8e037fc000fbe000 0x71b3f68000b34000

def z701 : W := mkw 0x4d82e81d40ec0f80 0x30f3f809c0fc0600

def z702 : W := mkw 0x44822805402c0380 0xb6d4380fc07c07c0

def z703 : W := mkw 0xf0063ae797000000 0x0fd439efcf000000

def z704 : W := mkw 0x2240128212114052 0x71b4369630b348f0

def z705 : W := mkw 0x00200020c5041305 0xfe080009cf4cf70f

def z706 : W := mkw 0x00200020c5041305 0xbed80809cf4c070f

def z707 : W := mkw 0x0000000000000000 0xffbc369633b349f3

def z708 : W := mkw 0x4002a81d00000000 0x04c7f80fc0000000

def z709 : W := mkw 0x4d82e81d40ec0f80 0x34f7f80fc0fc07c0

def z710 : W := mkw 0x8e037fc000fbe000 0x21f3ffe0007cf000

def z711 : W := mkw 0x4002280500000000 0x24843807c03001c0

def z712 : W := mkw 0xf007bfffbf02a000 0x0ff7ffffff00b000

def z713 : W := mkw 0x8e037fc000fbe000 0xfbfbffe000fff000

def z714 : W := mkw 0x4d82e81d40ec0f80 0xb067f81fc0fc0fc0

def z715 : W := mkw 0x8f437fc000fbec7a 0xf1fbffe000ffffff

def z716 : W := mkw 0x8e036d4000fbe000 0x7173cf6000fff000

def z717 : W := mkw 0x4002a81d00000000 0x26f7f81fc03001c0

def z718 : W := mkw 0x4902e81d00c00c00 0xb6f7f81fc0f00fc0

def z719 : W := mkw 0xbd8557e2ffec0f80 0xb90007e03ffc0fc0

def z720 : W := mkw 0x4002a83d85000000 0x0fd3c9e9cf000000

def z721 : W := mkw 0x4002a81d00000000 0x0ff7f91fcc000000

def z722 : W := mkw 0x0c036d0000ea8000 0x71f3ffe000fff000

def z723 : W := mkw 0xf247bfffbf114052 0xdfffffffffb308f0

def z724 : W := mkw 0xf247bfffbf114052 0x0067ff7ffcb308f0

def z725 : W := mkw 0x0c02680000e80000 0x0043c960004cb000

def z726 : W := mkw 0x4002a83d85000000 0xfffff9ffcfb049c3

def z727 : W := mkw 0x4c82680540ec0380 0xb6f7f817c0fc09c0

def z728 : W := mkw 0x8702bad828396c28 0xaa8838f83c3c7e3c

def z729 : W := mkw 0x80033fe085000000 0x05f3ffe1c3000000

def z730 : W := mkw 0xf647bfffbf396052 0x2ff7ffffff3c71c3

def z731 : W := mkw 0x4022a83dc5041305 0xfffff9ffcffcffcf

def z732 : W := mkw 0xae437fc212fbe052 0x71f7ffe600fff0c0

def z733 : W := mkw 0x4d82e81d40ec0f80 0xb6f7f8ffc0fc7fc0

def z734 : W := mkw 0x4002a81d00000000 0x06d3c809c0000000

def z735 : W := mkw 0x80033fc000000000 0x07f3ffe9c0000000

def z736 : W := mkw 0x8e037fc000fbe000 0xfffffff603fff9c3

def z737 : W := mkw 0xb26517e2bf115057 0x490807e03f03f03f

def z738 : W := mkw 0x8e037fc000fbe000 0xf1f3ffe000fff9c0

def z739 : W := mkw 0xae437fc212fbe052 0xfffbffe033fff133

def z740 : W := mkw 0x0001851828028028 0xdb7bc7183c43863c

def z741 : W := mkw 0xf9067ae797c28c28 0xd48c38e7c3c38e3c

def z742 : W := mkw 0xac436d4212eaa052 0x8e4fc976334cb9f3

def z743 : W := mkw 0x63e092bfd7155fd7 0xffbc369fffb34fff

def z744 : W := mkw 0xa0033fe297000000 0x0ff7ffffff000000

def z745 : W := mkw 0x8e436d4000fbe052 0xf04bc96000fff9f3

def z746 : W := mkw 0xf607bfffbf3be000 0x6ff7ffffff3ff000

def z747 : W := mkw 0x0c02680000e80000 0x30f3f8e000fc7000

def z748 : W := mkw 0xf207bfffbf114000 0x0ff7ffffffb30000

def z749 : W := mkw 0x8e437fc000fbe052 0xfbfbfff030fff9f3

def z750 : W := mkw 0x0901c51828c28c28 0x597bc7083cc3863c

def z751 : W := mkw 0x0921c538edc69f2d 0x24a3cef1f38f7933

def z752 : W := mkw 0xd007ad5d28000000 0x06f7f81fc0000000

def z753 : W := mkw 0x0900400040c68f28 0xf008000000cf8f3c

def z754 : W := mkw 0x8e237fe0c5fff305 0x8e2bf609cfb3070f

def z755 : W := mkw 0xf247bfffbf114052 0xdfffffffff834833

def z756 : W := mkw 0xf007bfdf3a000000 0x0ff7ff1ffc000000

def z757 : W := mkw 0x8c036d4000eaa000 0x0173cf60004cb000

def z758 : W := mkw 0xd007ad7dad000000 0x0003c009cc000000

def z759 : W := mkw 0x8c036d4000eaa000 0x3043c96000fcb000

def z760 : W := mkw 0x8c036d4000eaa000 0x5153c960004cb000

def z761 : W := mkw 0x4d82e81d40ec0f80 0x26f7f81fc07c07c0

def z762 : W := mkw 0xd007ad7dad000000 0x0943cf69fc000000

def z763 : W := mkw 0x8e037fc000fbe000 0x71f3ffe80cfff60c

def z764 : W := mkw 0x0e027a8000f94000 0x71f3ffe000fff000

def z765 : W := mkw 0x8e037fc000fbe028 0x71fbffe000fff03c

def z766 : W := mkw 0xc003ad5d00000000 0x06f7f97fc0000000

def z767 : W := mkw 0x41a0803ded041fad 0x8e0c001fff000fff

def z768 : W := mkw 0xf047bfffbf000052 0xdfffffffff8309f3

def z769 : W := mkw 0x0101851828000c28 0xdb7bc7183c830e3c

def z770 : W := mkw 0x0901c51828c28c28 0xfb7bc7183cc3cf3f

def z771 : W := mkw 0x0c02680000e80000 0x71d3c9e0004cf000

def z772 : W := mkw 0xb24517e2bf13c07a 0x490807e03f03c03f

def z773 : W := mkw 0x0e00400040ffe300 0xf000000000fff700

def z774 : W := mkw 0xf007bfffbf000000 0x9ff7ffffff800800

def z775 : W := mkw 0x00200020c5041305 0xffdc39efcf7cf7cf

def z776 : W := mkw 0x8c02684000e82000 0x0043c860004c3000

def z777 : W := mkw 0x4003ad1d00000000 0x07f7ff1fc0000000

def z778 : W := mkw 0xf007bfffbf000000 0x7ff7ffffff004000

def z779 : W := mkw 0x0c80400040ec0380 0x3000000000fc01c0

def z780 : W := mkw 0x4980c01d40c40f80 0xb6f7f01fc0f00fc0

def z781 : W := mkw 0x4da2e81d40ec1f85 0xb6f7f81fc0fcbfcc

def z782 : W := mkw 0x00200020c5041305 0xf4c809e9cf4cf70f

def z783 : W := mkw 0x4d82e81d00e80c80 0x04a7f817c0b008c0

def z784 : W := mkw 0x0d80400040ec0f80 0xf008000000ff0ff0

def z785 : W := mkw 0x8e037fc000fbe000 0x5173cfe000cff000

def z786 : W := mkw 0x0d80c01840ec0f80 0xb200001800fc0fc0

def z787 : W := mkw 0xd007ad7dad000000 0xdb5bc969cc40860c

def z788 : W := mkw 0x7006a81f3a000000 0x06f7f81ff0000000

def z789 : W := mkw 0xf027bfdf7a041305 0xf02ff616304cf70f

def z790 : W := mkw 0xf247bfffbf114052 0x8fffffffffb309f3

def z791 : W := mkw 0xd007ad7dad028028 0x0043c969cc00800c

def z792 : W := mkw 0x8e037fc000fbe000 0x30f3ff6000ffb000

def z793 : W := mkw 0x6242ba9f12114052 0x26f7f89fc33041c3

def z794 : W := mkw 0x4c82680540ec0380 0x24c7f807c07c01c0

def z795 : W := mkw 0x0d01c51828eaac28 0xdb7bc7183ccfbe3c

def z796 : W := mkw 0x8c036d4028eaa028 0x0043c9600c4cb00c

def z797 : W := mkw 0x4d82e81d40ec0f80 0xbff7f89fc3fc0fc0

def z798 : W := mkw 0x0fe0400040fd5fd7 0xf008000000ffffff

def z799 : W := mkw 0x0901c51828c28c28 0xfb7bc7183cf38ffc

def z800 : W := mkw 0x0901c51828c28c28 0x4b7bc7183c43863c

def z801 : W := mkw 0x4d82e81d40eeaf80 0xb6f7f81fc0fcbfc0

def z802 : W := mkw 0x2a41578212d3c052 0xfffffff633fff9f3

def z803 : W := mkw 0x86033fc000396000 0x71f3ffe000bf7000

def z804 : W := mkw 0x6242babf97114052 0xffffffffffb349f3

def z805 : W := mkw 0xd007ad7dad000000 0xb6f7f97fccb009c0

def z806 : W := mkw 0x2240128212114052 0xf92c369633b349f3

def z807 : W := mkw 0xf607bfffbf396000 0x7ff7ffffffbf7000

def z808 : W := mkw 0x00200020c5041305 0x004009e9cf4cf60f

def z809 : W := mkw 0x702492bfff041305 0xffbc369fff00470f

def z810 : W := mkw 0xf107bfffbf000c28 0xdfffffffff830e3c

def z811 : W := mkw 0x4d82e81d68ec0fa8 0xfffffe1ffcff0ffc

def z812 : W := mkw 0xd007ad7dad000000 0x0003c861c0000000

def z813 : W := mkw 0x0d80400040ec0f80 0x3000000000fc0600

def z814 : W := mkw 0xb24517e2bf13e052 0x490807e03f03f033

def z815 : W := mkw 0x0002282085000000 0x0ff3f9e9cf000000

def z816 : W := mkw 0x00018538ad000000 0x0f73c719ff000000

def z817 : W := mkw 0x0d80400040ee8fa8 0xffbc361630ff8ffc

def z818 : W := mkw 0x0c02680040ec0300 0xb6f7f81fc0fc0fc0

def z819 : W := mkw 0xf006baffbf000000 0x0ef7f8ffff000000

def z820 : W := mkw 0x0901450028c28c28 0xd97bc7003cc38e3c

def z821 : W := mkw 0x200197babf000000 0x0ff7ffffff000000

def z822 : W := mkw 0xf007bfffbf000000 0x0ef7fe1fff000000

def z823 : W := mkw 0x4002a83d85000000 0x0ef7f81fcf000000

def z824 : W := mkw 0x8e437fc000fbe052 0x71f3ffe000fff1c3

def z825 : W := mkw 0x8e037fc000fbe000 0xfffffff630fff9f0

def z826 : W := mkw 0x8e437fc000fbe052 0xf7fffff600fff9f3

def z827 : W := mkw 0xd027ad7dad001005 0x494bc9e9cf00f00f

def z828 : W := mkw 0x4003ad1d28000000 0x06f7f91fcc000000

def z829 : W := mkw 0xf107bfffbf000c00 0x8ff7ffffff000e00

def z830 : W := mkw 0x4d82e81d40ee8f80 0xf6f7f81fc0ff8fc0

def z831 : W := mkw 0xf247bfffbf13e052 0x4fffffffff03f033

def z832 : W := mkw 0x4d82e81d40ec0f80 0xf7f7f91fc0fc8fc0

def z833 : W := mkw 0x4482a81d402c0380 0xb6f7f81fc0bc09c0

def z834 : W := mkw 0xf007bfffbf000000 0x0ff7ffffff40860c

def z835 : W := mkw 0x0d80400040ec0f80 0xb024301600fc0fc0

def z836 : W := mkw 0x8e036d4000fbe000 0x70f3f96000fff000

def z837 : W := mkw 0x86023ac000396000 0x20f3f8e0003c7000

def z838 : W := mkw 0xf247bfffbf114052 0x6fffffffff3341f3

def z839 : W := mkw 0x4da2e83d85e81c85 0x492ff1f60fb0f8cf

def z840 : W := mkw 0x0da0400040ec1f85 0x00000000004cb60c

def z841 : W := mkw 0xb0073fe2bf000000 0x0ff3ffe9ff000000

def z842 : W := mkw 0xf207bfffbf114000 0x2ff7ffffff304000

def z843 : W := mkw 0xf007bfffbf000028 0x0fffffffff00003c

def z844 : W := mkw 0x0e20400040fff305 0x7000000000fff103

def z845 : W := mkw 0xf007bfffbf000000 0x0b73cff9ff000000

def z846 : W := mkw 0x2240128212114052 0xfffc369e33f34ff3

def z847 : W := mkw 0x00200020c5041305 0xdb5809e9cf4cf60f

def z848 : W := mkw 0x4d82e81d40ee8fa8 0xb6f7f81fc0fc8fcc

def z849 : W := mkw 0x0801450000c28000 0xfffbcff033cff933

def z850 : W := mkw 0x8a0157c000d3e000 0x71f3cfe000cff000

def z851 : W := mkw 0x8e037fc000fbe000 0x71d3f9e0007cf000

def z852 : W := mkw 0xf007bfffbf000000 0x0e67ff7fff000000

def z853 : W := mkw 0x0901c51828c28c28 0xd92bc7103cc38e3c

def z854 : W := mkw 0xf007bfffbf000000 0xffffffffff4cf60c

def z855 : W := mkw 0x8e037fc000fbe000 0x7143cfe000fff000

def z856 : W := mkw 0xf007bfffbf000000 0x2ff7ffffff3001c0

def z857 : W := mkw 0x7004803fbf000000 0x0e77c01fff000000

def z858 : W := mkw 0x0002280000000000 0x71f3f9e0004cf000

def z859 : W := mkw 0x8e037fc000fbe000 0x30f3fee000ff7000

def z860 : W := mkw 0x0b60400040d7df7f 0xf008000000ffffff

def z861 : W := mkw 0xf047bfffbf000052 0xffffffffff0049f3

def z862 : W := mkw 0x0901c51828c28c28 0x496bc7183cc38e3c

def z863 : W := mkw 0x4d82e81d00e80c80 0xb6f7f81fc0b009c0

def z864 : W := mkw 0x4da2e81d40ec1f85 0xfffff89fc3fcffcf

def z865 : W := mkw 0xf187bfffbf000c80 0x0ff7ffffff0008c0

def z866 : W := mkw 0x00018538ad000000 0x0b73cf79fc000000

def z867 : W := mkw 0x8e027ac000f96000 0x20c3f8e0007c7000

def z868 : W := mkw 0x8e037fc000fbe000 0x0043f960007cb000

def z869 : W := mkw 0x8c036d4000eaa000 0x00f3f960004cb000

def z870 : W := mkw 0x4003ad1d28000000 0x06f7fe1ff0000000

def z871 : W := mkw 0x8c036d4000eaa000 0xffdbc9e0034cf103

def z872 : W := mkw 0xb24517e2bf114052 0x090007e03f004003

def z873 : W := mkw 0x7006a83fbf000000 0x0e27f01fff000000

def z874 : W := mkw 0x2240128212114052 0xfe2c361633b349f3

def z875 : W := mkw 0x0901c51828c28c28 0xdffbcf19fcc38e3c

def z876 : W := mkw 0xf007bfffbf000000 0x0fb7fef7f3000000

def z877 : W := mkw 0xf007bfffbf000000 0x2ff7ffffff004103

def z878 : W := mkw 0x2240128212114052 0x8fbc369633b309f3

def z879 : W := mkw 0x8c036d4000eaa000 0x0043c9680c4cb60c

def z880 : W := mkw 0x4002a81d40040300 0xb6f7f81fc0fc0fc0

def z881 : W := mkw 0x0901c51828c28c28 0xdb5bc7083c43863c

def z882 : W := mkw 0xae437fc212fbe052 0xf1fffff630fff9f3

def z883 : W := mkw 0xf007bfffbf000000 0x0f77f71fff000000

def z884 : W := mkw 0x0fc0400040ffcffa 0xf008000000ffcfff

def z885 : W := mkw 0x2240128212114052 0xfffc3ff633b349f3

def z886 : W := mkw 0x4102a81d00000c00 0x86f7f81fc0000e00

def z887 : W := mkw 0xd607bffdad396000 0x20c3f9e9cc3c7000

def z888 : W := mkw 0xf247bfffbf114052 0x2ff7ffffffb349f3

def z889 : W := mkw 0x4002a81d00000000 0x04a7f817c0000000

def z890 : W := mkw 0x226012a2d7155357 0x00643f7ffcffbefc

def z891 : W := mkw 0xf647bfffbf396052 0xffffffffffbf79f3

def z892 : W := mkw 0x2240128212114052 0x2fb4369633b349f3

def z893 : W := mkw 0xae437fc212fbe052 0x24a7fef633bf79f3

def z894 : W := mkw 0x8e037fc000fbe000 0x7123f7e000fff000

def z895 : W := mkw 0x0920400040c69f2d 0x00000000004cb60c

def z896 : W := mkw 0x8c036d4000eaa000 0x30d3c960004cb000

def z897 : W := mkw 0x0fa0400040ffff85 0xf008000000ffffcf

def z898 : W := mkw 0x84033fc000282000 0x01f3ffe0000c3000

def z899 : W := mkw 0x2040000212000052 0xffbc361633b309f3

def z900 : W := mkw 0x00200020c5041305 0xffd809e9cfcfff3f

def z901 : W := mkw 0xc38197dd4017ef80 0xc70407ffc003ffc0

def z902 : W := mkw 0x8e037fc000fbe000 0x75f7ffe600fff1c0

def z903 : W := mkw 0xaf437fc212fbec7a 0xfffffff633ffffff

def z904 : W := mkw 0xd007ad7dad000000 0x0ff7ff7ffc000000

def z905 : W := mkw 0x4d82e81d40ec0f80 0xb6b7f01fc0b00fc0

def z906 : W := mkw 0xf007bfffbf000000 0x05f7ffefcf000000

def z907 : W := mkw 0x0f80528040ffef80 0xf7b4369600ffffc0

def z908 : W := mkw 0xf0073fe797000000 0x0ff7ffefcf000000

def z909 : W := mkw 0x4182a81d00000c80 0x06f7f81fc00008c0

def z910 : W := mkw 0x0801450000c28000 0x5173cf6000cfb000

def z911 : W := mkw 0x0901c51828c28c28 0x8a6bc7183cc38e3c

def z912 : W := mkw 0xf006baff97000000 0x04c7f8efc3000000

def z913 : W := mkw 0xf107bfffbf000c28 0x0ff7ffffff00060c

def z914 : W := mkw 0xf007bfffbf000000 0x0b77ff7ffc000000

def z915 : W := mkw 0xae437fc212fbe052 0xf7f7fff603fff9c3

def z916 : W := mkw 0xa6433fc212396052 0x2ff7fff6333c71c3

def z917 : W := mkw 0xf0073fe797000000 0x0ff7fff7f3000000

def z918 : W := mkw 0xae037fc212fbe000 0xfff7fff633fff9c0

def z919 : W := mkw 0x00200020c5041305 0xffd809f9ff4cff3f

def z920 : W := mkw 0xf247bfffbf114052 0xafffffffff3049f3

def z921 : W := mkw 0x0d80400040ec0f80 0xfb5801080cfc8fcc

def z922 : W := mkw 0x8c036d4000eaa000 0x71f3ff6000ffb000

def z923 : W := mkw 0x0d80400040ee8fa8 0x00000000004c860c

def z924 : W := mkw 0x4242a81d00114052 0xf6fff81fc0b349f3

def z925 : W := mkw 0x8e027ac000fbe000 0x70f3f8e000fff000

def z926 : W := mkw 0x80032d4000000000 0x71d3c9e0004cf000

def z927 : W := mkw 0xf007bfffbf000000 0xffffffffffb049c3

def z928 : W := mkw 0x4d82e81d40ee8fa8 0xb6f7f81fc0ff0ff0

def z929 : W := mkw 0xf247bfdf3a114052 0xfffffe9ff3b349f3

def z930 : W := mkw 0x8f037fc000fbec00 0xf1f3ffe000fffe00

def z931 : W := mkw 0xae437fc23afbe07a 0xfffffff63ffff9ff

def z932 : W := mkw 0xf007bfffbf000000 0x0ff7ffffff4cb000

def z933 : W := mkw 0x0d80400040ee8fa8 0xb000000000ff0ff0

def z934 : W := mkw 0x8f827ac040fd6f80 0xb08038e000fc7fc0

def z935 : W := mkw 0x4d82e81d40ec0f80 0xbff7f91fccfc0fc0

def z936 : W := mkw 0x8e036d4000fbe000 0x2043c960007cf000

def z937 : W := mkw 0x41a0803dc5041f85 0x8e080009cf00070f

def z938 : W := mkw 0xc203bfdd0013e000 0x47f7ffffc003f000

def z939 : W := mkw 0x01208038ed041f2d 0x8a080019fc000e3c

def z940 : W := mkw 0xd007bffdad000000 0x0ff3ffe9cf000000

def z941 : W := mkw 0x0d80400040ec0f80 0x8000000000b00fc0

def z942 : W := mkw 0xd007ad7dad000000 0x0943c9e9cf000000

def z943 : W := mkw 0x00200020c5041305 0xcf4809e9cf4cf70f

def z944 : W := mkw 0x8f037fc028fbec28 0xf9fbffe03cfffe3c

def z945 : W := mkw 0xe243bfdf12114052 0xfffffffff3b349f3

def z946 : W := mkw 0x5006a83dad000000 0x06f7f81fcc000000

def z947 : W := mkw 0x8e037fc000fbe000 0xf1fbffe000fff103

def z948 : W := mkw 0x80033fe085000000 0x01f3ffe9cc000000

def z949 : W := mkw 0x4002a81d00000000 0x06f7f81fc0b008c0

def z950 : W := mkw 0x0c02680000e80000 0xfffff9f603fcf9c3

def z951 : W := mkw 0x00200020c5041305 0xffd80fe9ff4ff73f

def z952 : W := mkw 0x41a0803dc5041f85 0x8604001fc3000fc3

def z953 : W := mkw 0xf00597ffbf000000 0x0f77c7ffff000000

def z954 : W := mkw 0xd007bffdad000000 0x07f7ffffcc000000

def z955 : W := mkw 0x0980400040c40f80 0x9000000000c00fc0

def z956 : W := mkw 0xd007ad7dad000000 0x00f3f969cc000000

def z957 : W := mkw 0x6002ba9f12000000 0x06f7f89fc3000000

def z958 : W := mkw 0x4182a81d40040f80 0xb6f7f81fc0b00fc0

def z959 : W := mkw 0x0801450000c28000 0x0043c960004cb000

def z960 : W := mkw 0xcd82e85d40ec2f80 0xb6f7f87fc0fc3fc0

def z961 : W := mkw 0xf007ad7fbf000000 0x0447c96fcf000000

def z962 : W := mkw 0x8f037fc000fbec28 0xfbfbfff030fffe3c

def z963 : W := mkw 0x0101851828028c28 0xcb7bc7183c038e3c

def z964 : W := mkw 0x7006a83fbf000000 0x0ff7f9ffff000000

def z965 : W := mkw 0x4d82e81d40ec0f80 0xfffff9ffc3fcffc3

def z966 : W := mkw 0xd007ad7dad000000 0x0ff3cff9ff000000

def z967 : W := mkw 0xf007bfdf3a000000 0x04a7fe17f0000000

def z968 : W := mkw 0x0900c01828c00c28 0xdb7bc6183cc30e3c

def z969 : W := mkw 0x2240128212114052 0x75b4369633b349f3

def z970 : W := mkw 0x2160803aff041f7f 0x8e0c001fff000fff

def z971 : W := mkw 0x4002a81d00000000 0xb6f7f81fc0000100

def z972 : W := mkw 0x4002a81d00000000 0x07f7f9ffc0000000

def z973 : W := mkw 0x0001851828000000 0x0ff3cf19fc000000

def z974 : W := mkw 0x7e04c03fbffbe000 0x7e04001ffffff000

def z975 : W := mkw 0xf007bfffbf028028 0xdfffffffff43863c

def z976 : W := mkw 0x4002a81d00000000 0x0627f01fc0000000

def z977 : W := mkw 0x86033fc000396000 0x20a3fee0003c7000

def z978 : W := mkw 0x8e037fc000fbe000 0x0023fe6000bf3000

def z979 : W := mkw 0x80032d6085000000 0x0fd3c9e9cf000000

def z980 : W := mkw 0x00200020c5041305 0x490801e00f4cf60f

def z981 : W := mkw 0x00200020c5041305 0x79d809e9cf4cf60f

def z982 : W := mkw 0x2b41d79a3ad3cc7a 0x24c7f18e0f70c7cf

def z983 : W := mkw 0x0901c51828c28c28 0xdb7bc7f83cc3fe3c

def z984 : W := mkw 0x00200020c5041305 0xfffc3fffffffffff

def z985 : W := mkw 0xf007bfffbf000000 0x0027f61ffc000000

def z986 : W := mkw 0xf207bfffbf114000 0xfff7ffffffb349c0

def z987 : W := mkw 0x44832d05682e83a8 0x6d8c3f07fc3f81fc

def z988 : W := mkw 0xf007bfdf3a000000 0x0ff7fe9ff3000000

def z989 : W := mkw 0xf007bfffbf000000 0x0fd3cfe9ff000000

def z990 : W := mkw 0x4c02e81d00e80000 0xb6f7f81fc0fc09c0

def z991 : W := mkw 0x8c037fc000eaa000 0x51f3ffe000cfb000

def z992 : W := mkw 0x2fc0528252fd4fd2 0xf908068033ff4ff3

def z993 : W := mkw 0x4da2e81d40ec1f85 0xb6f7f81fc0fc7fc3

def z994 : W := mkw 0xd007ad7dad000000 0x0173cf69cc000000

def z995 : W := mkw 0x8e037fc000fbe000 0xf1fbffe000fff60c

def z996 : W := mkw 0xf006badf12000000 0x06f7f81fc0000000

def z997 : W := mkw 0x0901c51828c28c28 0xda2bc6183cc38e3c

def z998 : W := mkw 0x4003ad1d28000000 0x0043c909cc000000

def z999 : W := mkw 0xf007bfffbf000000 0xdfffffffffc38e3c

def z1000 : W := mkw 0xae437fc212fbe052 0x24c7f9e6037cf1c3

def z1001 : W := mkw 0x4d82e81d40ec0f80 0xb6b7f817c0bc09c0

def z1002 : W := mkw 0x00200020c5041305 0xfffc39ffcf4cf70f

def z1003 : W := mkw 0x2240128212114052 0xb6b4369633b349f3

def z1004 : W := mkw 0x4003ad3dad000000 0x0ff7ffffff000000

def z1005 : W := mkw 0x61e0803fd7041fd7 0x8e0c001fff000fff

def z1006 : W := mkw 0xf007ad7fbf000000 0x0fd7c9ffff000000

def z1007 : W := mkw 0x8e037fc000fbe000 0x0043c9e0004cf000

def z1008 : W := mkw 0xd006a87d85000000 0x0043c869c0000000

def z1009 : W := mkw 0x4003ad1d28000000 0x0b73cf19fc000000

def z1010 : W := mkw 0xd007ad7dad000000 0x0647c97fcc000000

def z1011 : W := mkw 0x0801450028c28028 0xdb7bc7083cc3863c

def z1012 : W := mkw 0xd0073fe585000000 0x01f3ffe1c0000000

def z1013 : W := mkw 0xc003bfdd28000000 0x0ff7fffffc000000

def z1014 : W := mkw 0x4d82e81d00e80c80 0x0627f01fc0b008c0

def z1015 : W := mkw 0x0c02680000e80000 0x30f3f96000fcb000

def z1016 : W := mkw 0xf207bfffbf114000 0xffffffffffb34830

def z1017 : W := mkw 0x2b60528252d7df7f 0xffbc369633ffffff

def z1018 : W := mkw 0x00018538ad000000 0x0fd3c9e9cf000000

def z1019 : W := mkw 0xd207bffdad13e000 0x4143cfe9cc03f000

def z1020 : W := mkw 0x4d82e81d40ec0f80 0xb6f7f91fccfc8fcc

def z1021 : W := mkw 0x8e037fc000fbe000 0x71f3fff030fff830

def z1022 : W := mkw 0xa0033fc212000000 0xfffffff6334cf103

def z1023 : W := mkw 0x0fc0400040fd4fd2 0xb000000000fc4fc3

def z1024 : W := mkw 0xae437fc212fbe052 0x7ff7fff633fff1c3

def z1025 : W := mkw 0x4020803dc5041305 0x8e0c001fcf00070f

def z1026 : W := mkw 0xae437fc212fbe052 0xfffffffe3fffffff

def z1027 : W := mkw 0xae437fc212fbe052 0xf7f7fff630fff9f0

def z1028 : W := mkw 0x4d82e81d40ec0f80 0xa6c7f81fc07c0fc0

def z1029 : W := mkw 0xf007bfffbf000000 0xffffffffffb309f0

def z1030 : W := mkw 0x0901c51828c28c28 0xdf7bc7183fc38f3f

def z1031 : W := mkw 0x44822805402c0380 0x24f7f807c03c01c0

def z1032 : W := mkw 0x8e037fc000fbe000 0x4163ffe000fff000

def z1033 : W := mkw 0x0901c51828c28c28 0xfffff79e3ff3cfff

def z1034 : W := mkw 0x2fc0528252fd4fd2 0xb484308603fc4fc3

def z1035 : W := mkw 0x4da2e81d40ec1f85 0xf7fff9ffc0fcffcf

def z1036 : W := mkw 0x0da0400040ec1f85 0xb000000000fcbfcc

def z1037 : W := mkw 0x8e037fc000f96000 0x31f3ffe000fc7000

def z1038 : W := mkw 0x4d82e81d68ec0fa8 0xb6f7f81ff0fc0ff0

def z1039 : W := mkw 0x0901450028c28c28 0x490807003c43863c

def z1040 : W := mkw 0x80032d6085000000 0x0043c969cc000000

def z1041 : W := mkw 0x4d82e81d68ec0f80 0xbef7f81ffcfc0fc0

def z1042 : W := mkw 0xd007ad7dad000000 0x0b53c969cc000000

def z1043 : W := mkw 0xae427ac212f96052 0xfffffef633ff79f3

def z1044 : W := mkw 0x6fc2fa9f52fd4fd2 0x494bce89f34f4633

def z1045 : W := mkw 0x0000801800000000 0x06f3c819c0000000

def z1046 : W := mkw 0x0820400040c69305 0xf008000000cff70f

def z1047 : W := mkw 0x4d82680540ec0f80 0xb4f7f807c0fc0fc0

def z1048 : W := mkw 0xf007bfffbf000000 0xffffffffff834933

def z1049 : W := mkw 0xf207bfffbf13e028 0x4fffffffff03f03c

def z1050 : W := mkw 0x6242ba9f12114052 0x4ffffe9ff3034033

def z1051 : W := mkw 0x4482a81d00280080 0x06f7f81fc03000c0

def z1052 : W := mkw 0x00218538ad02902d 0x4ffbcff9ff03f03f

def z1053 : W := mkw 0xae437fc212fbe052 0xffffffe603fff1c3

def z1054 : W := mkw 0x0e20400040fff305 0x7000000000fff60c

def z1055 : W := mkw 0x8e037fc028fbe000 0x79f3ffe03cfff000

def z1056 : W := mkw 0x4002a81d00000000 0x36f7f81fc0b00000

def z1057 : W := mkw 0x0901c51828c28c28 0x0043c7083c43863c

def z1058 : W := mkw 0xd107ad7dad000c28 0x0043c969cc00060c

def z1059 : W := mkw 0x0901c51828c28c28 0x5173c7183cc38e3c

def z1060 : W := mkw 0xd0072d6585000000 0x0043c961c0000000

def z1061 : W := mkw 0x5005853dad000000 0x0043c109cc000000

def z1062 : W := mkw 0x8c036d4000eaa000 0x71f3cfe000cff000

def z1063 : W := mkw 0x8e037fc000fbe000 0x21f3ffe000bf7000

def z1064 : W := mkw 0x0da0400040ec1f85 0xffbc309603fcffcf

def z1065 : W := mkw 0x8e437fc000fbe052 0x71f3ffe000fff8f0

def z1066 : W := mkw 0x2240128212114052 0x0424361633b309f3

def z1067 : W := mkw 0x5024803ded041305 0x8e080009cf00070f

def z1068 : W := mkw 0x8f837fc000fbec80 0x71f3ffe000fff8c0

def z1069 : W := mkw 0x4d82e81d40ec0f80 0x2487f807c03c01c0

def z1070 : W := mkw 0x4d82e81d00e80c80 0x96f7f81fc0f00ec0

def z1071 : W := mkw 0x4d82e81d40ec0f80 0xbefff81fc3fc0fc3

def z1072 : W := mkw 0x8e037fc000fbe000 0x70a3fee000fff000

def z1073 : W := mkw 0x00200020c5041305 0xfff809f9cfccff0f

def z1074 : W := mkw 0xf007bfffbf000000 0x8fffffffff00060c

def z1075 : W := mkw 0x8c036d4000eaa000 0x0063cf6000cfb000

def z1076 : W := mkw 0xf2663ae7d7155357 0x248438e7c33c71c3

def z1077 : W := mkw 0x0901c51828c28c28 0x8b7bc7183c830e3c

def z1078 : W := mkw 0x00200020c5041305 0x6dc809e9cf4cf70f

def z1079 : W := mkw 0x82033fc00013e000 0x71f3ffe0004ff000

def z1080 : W := mkw 0x80033fc000000000 0x21f3ffe0000c7000

def z1081 : W := mkw 0x4003ad1d28000000 0xffffff1ffcb309f0

def z1082 : W := mkw 0x4d82e81d40ec0f80 0xb6f7fe1ff0ff0ff0

def z1083 : W := mkw 0xf247bfdf3a114052 0xb6f7fe1ff0b309f0

def z1084 : W := mkw 0x6003bf9f3a000000 0x0ff7ff9fff000000

def z1085 : W := mkw 0x8c036d4000eaa000 0x5043c96000cfb000

def z1086 : W := mkw 0x0901c51828c28c28 0xdffff71e3cc38e3c

def z1087 : W := mkw 0x5005853dad000000 0x0b73c719fc000000

def z1088 : W := mkw 0xf027bfffbf001005 0x7fffffffff4cf00f

def z1089 : W := mkw 0xf007bfdf3a000000 0x0627f61ff0000000

def z1090 : W := mkw 0xd007ad7dad000000 0x0063cf79fc000000

def z1091 : W := mkw 0x8e037fc000fbe000 0xf7f3ffe000fff100

def z1092 : W := mkw 0xf247bfffbf114052 0x7ff7ffffffb348f0

def z1093 : W := mkw 0x8e037fc000fbe000 0xfffbffe80ffff70f

def z1094 : W := mkw 0x86033fc000396000 0x20c3f9e0003c7000

def z1095 : W := mkw 0x00200020c5041305 0xf94809e9cf4cf70f

def z1096 : W := mkw 0x7005853fbf000000 0x0ff7cfffff000000

def z1097 : W := mkw 0x66e23aa7d73d53d7 0x248438e7c33c71c3

def z1098 : W := mkw 0x4d82e81d40ec0f80 0xb6f7f89fc3fc4fc3

def z1099 : W := mkw 0xf007bfff97000000 0x07f7ffffc3000000

def z1100 : W := mkw 0xf407bfffbf282000 0x0ff7ffffff0c3000

def z1101 : W := mkw 0xd007ad7dad000000 0x0ff7f9ffcf000000

def z1102 : W := mkw 0x4202ba9d00114000 0x77f7fe9fc0b34000

def z1103 : W := mkw 0x0f80528040fd4f80 0xf1b0368000ff4fc0

def z1104 : W := mkw 0x0901c51828c28c28 0xfffbcff83fcfff3f

def z1105 : W := mkw 0x4482a81d402c0380 0x24c7f80fc03c01c0

def z1106 : W := mkw 0x8c037fc000eaa000 0x0143cfe0004cb000

def z1107 : W := mkw 0xf247bfffbf114052 0xfffffffffff3cfff

def z1108 : W := mkw 0x2240128212114052 0xffbc3ef633bf79f3

def z1109 : W := mkw 0x00200020c5041305 0xfff80fe9cfcff70f

def z1110 : W := mkw 0x0920400040c69f2d 0xd008000000c38f3f

def z1111 : W := mkw 0x0fc0400040ffefd2 0xf008000000fffff3

def z1112 : W := mkw 0x8e037fc000fbe000 0x71b3fee000bf7000

def z1113 : W := mkw 0x8e027ac000f96000 0x71f3f9e000fcf000

def z1114 : W := mkw 0x4d82e81d00e80c80 0x36f7f81fc0fc08c0

def z1115 : W := mkw 0xf007bfffbf000000 0x0427f617f3000000

def z1116 : W := mkw 0x0f80400040ffefa8 0xf008000000fffffc

def z1117 : W := mkw 0x0da0400040ee9fad 0xf008000000ffffff

def z1118 : W := mkw 0xf007bfffbf000000 0x4fffffffff004003

def z1119 : W := mkw 0xf007bfffbf000000 0x0043cf69fc000000

def z1120 : W := mkw 0x0da0400040ec1f85 0xb008000000fc0fcf

def z1121 : W := mkw 0x80233fc040041305 0xf1fbffe0004cf70f

def z1122 : W := mkw 0x0000000000000000 0xb6d00809c0000100

def z1123 : W := mkw 0x4002a81d00000000 0x77f7f9ffc04cf000

def z1124 : W := mkw 0x0d82680040ec0f80 0xb080380000fc0fc0

def z1125 : W := mkw 0x8d036d4000eaac28 0xd04bc96000cfbe3c

def z1126 : W := mkw 0xf0073fe797000000 0x04c7f9e7c3000000

def z1127 : W := mkw 0x0901c51828c28c28 0x9273c7183cc38e3c

def z1128 : W := mkw 0xc003bfdd00000000 0x06f7fe1fc0000000

def z1129 : W := mkw 0x4d82e81d40ec0f80 0xb4c7f80fc0fc0fc0

def z1130 : W := mkw 0x4003ad1d28028028 0x4fffff1ffc03803c

def z1131 : W := mkw 0x4d82e81d40ec0f80 0x0427f017c0b009c0

def z1132 : W := mkw 0xf007bfffbf000000 0x0fd7f9efcf000000

def z1133 : W := mkw 0x0901c51828c28c28 0xfb7bc7183ccffe3c

def z1134 : W := mkw 0x0021851868041305 0xfb7bc7183c4cf70f

def z1135 : W := mkw 0x0901c51828c28c28 0xfffbc7183cc38f3c

def z1136 : W := mkw 0xd027ad7dad001005 0x0043c969cc00b00c

def z1137 : W := mkw 0x0c00400040ec0300 0xb000000000fc0700

def z1138 : W := mkw 0x00200020c5041305 0xfff80ff9ff4cf70f

def z1139 : W := mkw 0xae437fc212fbe052 0x79fffff633fff8f3

def z1140 : W := mkw 0x4d82e81d40ec0f80 0xf6f7f81fc0fcffc0

def z1141 : W := mkw 0x4d82e81d40ec0f80 0xbff7fe1ff0fc0fc0

def z1142 : W := mkw 0x4d82e81d40ee8fa8 0xfffffe1ff0ff8ffc

def z1143 : W := mkw 0x4002a81d00000000 0xdffffe1ff0830830

def z1144 : W := mkw 0x0d80400040ee8fa8 0xb000000000fc8fcc

def z1145 : W := mkw 0xf247bfffbf13c07a 0xffffffffffb3c9ff

def z1146 : W := mkw 0x4d82e81d40ec0f80 0x86f7f81fc0b00fc0

def z1147 : W := mkw 0xf007bfffbf000000 0x4fffffffff00800c

def z1148 : W := mkw 0x2240128212114052 0xfffc3e9ff3b349f3

def z1149 : W := mkw 0x00200020c5041305 0x2fd009e9cf4cf70f

def z1150 : W := mkw 0x84032d4000282000 0x0043c960000c3000

def z1151 : W := mkw 0xf0073fe797000000 0x04a7fee7c3000000

def z1152 : W := mkw 0xd007ad7dad000000 0x0e43c969cf000000

def z1153 : W := mkw 0x4c82680540ec0380 0x24a7f807c0bc01c0

def z1154 : W := mkw 0x4d82e81d40ec0f80 0xf7f7fe1fc0ff0fc0

def z1155 : W := mkw 0x4d82e81d00e80c80 0x0067f81fc0b008c0

def z1156 : W := mkw 0xf007bfffbf000000 0x04e7ffffff000000

def z1157 : W := mkw 0x8c036d4000eaa000 0x4143c9e0004cf000

def z1158 : W := mkw 0x4da2e81d40ec1f85 0xb6fff81fc0fc0fcf

def z1159 : W := mkw 0xae037fc212fbe000 0xfffffff633fff103

def z1160 : W := mkw 0xf007bfffbf000000 0x0027fe77f0000000

def z1161 : W := mkw 0x0901c51828c28c28 0xcb4bc7183c438e3c

def z1162 : W := mkw 0x0d80400040eeaf80 0x00000000004cb600

def z1163 : W := mkw 0x0d01c51828ea8c28 0xfb7bc7183cff8e3c

def z1164 : W := mkw 0x7005853fbf000000 0x0e27c61fff000000

def z1165 : W := mkw 0x8e037fc000fbe000 0x79fbffe030fff030

def z1166 : W := mkw 0xe003bfdf12000000 0x0ff7fffff3000000

def z1167 : W := mkw 0x8e437fc000fbe052 0x71fbffe000fff033

def z1168 : W := mkw 0x8e037fc000fbe000 0x77f7fff600fff000

def z1169 : W := mkw 0x0d80400040ec0f80 0xf008000000fc8fcc

def z1170 : W := mkw 0x8c036d4000eaa000 0x20c3f960007cb000

def z1171 : W := mkw 0x8e037fc000fbe000 0x77f3ffe9c0fff000

def z1172 : W := mkw 0x0901c51828c28c28 0xdb7bcf783ccfbe3c

def z1173 : W := mkw 0x0d80400040ec0f80 0xb0d0080000fc0fc0

def z1174 : W := mkw 0xf007bfffbf000000 0x8fffffffff000830

def z1175 : W := mkw 0x0901c51828c28c28 0xd94bc7083cc38e3c

def z1176 : W := mkw 0xf2473fe797114052 0x75f7ffe7c3b341c3

def z1177 : W := mkw 0xd006a87d85000000 0x06f7f87fc0000000

def z1178 : W := mkw 0x82033fc000114000 0x71f3ffe000fff000

def z1179 : W := mkw 0xd247ad7dad114052 0xf04bc969ccb349f3

def z1180 : W := mkw 0x4d82e81d40ec0f80 0x26f7f81fc0bc09c0

def z1181 : W := mkw 0x0901c51828c28c28 0xdb7bc7983fc3ce3f

def z1182 : W := mkw 0x0901c51828c28c28 0xdb3bc6183c830e3c

def z1183 : W := mkw 0x700597bfbf000000 0x0ff7f79fff000000

def z1184 : W := mkw 0xfe077fc712fbe000 0x71f7ffe600fff000

def z1185 : W := mkw 0x8e037fc000fbe000 0x20e3ffe000fff000

def z1186 : W := mkw 0x88037fc000c28000 0x71f3ffe000cff000

def z1187 : W := mkw 0xb24517e2bf114052 0x090007e03f030030

def z1188 : W := mkw 0x8e037fc000fbe000 0x79fbffe00cfff00c

def z1189 : W := mkw 0x8e037fc000fbe000 0x70c3f9e000fff000

def z1190 : W := mkw 0x7046a83fbf000052 0xbefff81fffb009f3

def z1191 : W := mkw 0x8e037fc000fbe000 0x7ff3ffe003fff000

def z1192 : W := mkw 0x4002a81d00000000 0x96f7f81fc0400600

def z1193 : W := mkw 0x8e037fc000fbe000 0x79fbffe003fff003

def z1194 : W := mkw 0x8e037fc000fbe000 0x2083f8e0003c7000

def z1195 : W := mkw 0x4d82e81d40ec0f80 0x0027f01fc0b00ec0

def z1196 : W := mkw 0x226117a2bf13d07f 0x490807e03f03f03f

def z1197 : W := mkw 0x6242ba9f12114052 0x06f7fe1ff0b308f0

def z1198 : W := mkw 0x8e037fc000fbe000 0xf1fbffe000fff830

def z1199 : W := mkw 0x00018538ad000000 0xfffbcff9ff834933

def z1200 : W := mkw 0xf247bfffbf114052 0x494bcfe9ff034033

def z1201 : W := mkw 0x0d80400040ec0f80 0xb690000000fc0fc0

def z1202 : W := mkw 0xf007bfffbf000000 0x3ff7ffffff4c0000

def z1203 : W := mkw 0xd007bffdad000000 0x0063ff69cc000000

def z1204 : W := mkw 0xf007bfffbf000000 0x09f3ffe9ff000000

def z1205 : W := mkw 0x0d80400040ec0f80 0x80000000004c0fc0

def z1206 : W := mkw 0x2e427a8212f94052 0xfffffff633fff9f3

def z1207 : W := mkw 0x71a4803fff041f85 0x8e0c001fff000fcf

def z1208 : W := mkw 0x0002280000000000 0x06f3f809c0000000

def z1209 : W := mkw 0xf007bfffbf000000 0x4fffffffff030030

def z1210 : W := mkw 0x2fc0528252ffefd2 0xffbc369633fffff3

def z1211 : W := mkw 0xd007ad7dad000000 0x0043c969cc4cb000

def z1212 : W := mkw 0x00200020c5041305 0xffdc09ffcf4cffcf

def z1213 : W := mkw 0xf007bfffbf000000 0x01f7fffffc000000

def z1214 : W := mkw 0x2240128212114052 0xbebc361633b309f3

def z1215 : W := mkw 0x4d82e81d40ec0f80 0x34f7f817c0fc09c0

def z1216 : W := mkw 0xf027bfffbf001005 0xdfffffffff40f60f

def z1217 : W := mkw 0x8c037fc000eaa000 0x00c3f9e0004cb000

def z1218 : W := mkw 0x4002a81d00000000 0x36f7f81fc04c0000

def z1219 : W := mkw 0x4d82e81d40ec0f80 0xb6d7f80fc07c07c0

def z1220 : W := mkw 0xae427ac212f96052 0xb6f7f8f603fc79c3

def z1221 : W := mkw 0x8e037fc000fbe000 0xf3f3ffe800fff600

def z1222 : W := mkw 0x8c02684000e82000 0x30f3f86000fc3000

def z1223 : W := mkw 0x2240128212114052 0xdf3c361633b309f3

def z1224 : W := mkw 0xf047bfffbf000052 0x0ff7ffffff0008f0

def z1225 : W := mkw 0x8c036d4000eaa000 0x0003c860000c3000

def z1226 : W := mkw 0x8e0157c000fbe000 0x410007e0004ff000

def z1227 : W := mkw 0x7045853fbf000052 0xdf7fc71fff8309f3

def z1228 : W := mkw 0xd007bffdad000000 0x0bf3fff9fc000000

def z1229 : W := mkw 0x8f8157c040ffef80 0xf10007e000ffffc0

def z1230 : W := mkw 0x8003bff8ad000000 0x0ff3fff9ff000000

def z1231 : W := mkw 0xce03ffdd00fbe000 0xf7f7ffffc0fff9c0

def z1232 : W := mkw 0x0002280000000000 0x30f3f80000b00000

def z1233 : W := mkw 0xf107bfffbf000c28 0xdfffffffff408e3c

def z1234 : W := mkw 0xd007ad7dad02a000 0x0043c969cc00b000

def z1235 : W := mkw 0x0901c51828c28c28 0xfbfbc7983cc3ce3c

def z1236 : W := mkw 0x7005853fbf000000 0x0e47c11fff000000

def z1237 : W := mkw 0xf007bfdf3a000000 0x0067fe1ff0000000

def z1238 : W := mkw 0xf247bfffbf114052 0xcfffffffff0349f3

def z1239 : W := mkw 0x4002a81d00000000 0x0067f81fc0000000

def z1240 : W := mkw 0x0e02680000fbe000 0x71f3f9e000fff000

def z1241 : W := mkw 0xc002badd00000000 0x06f7f8ffc0000000

def z1242 : W := mkw 0x8901c55828c2ac28 0xdb7bc7783cc3be3c

def z1243 : W := mkw 0xae437fc212fbe052 0x7ff7fff633fff8f0

def z1244 : W := mkw 0xf247bfffbf114052 0xffffffffff3041c3

def z1245 : W := mkw 0x6243bf9f3a114052 0xffffff9fffb349f3

def z1246 : W := mkw 0xf007ad7fbf000000 0x0047c97ffc000000

def z1247 : W := mkw 0x0d81c51828ea8ca8 0xdb7bc7183cf38efc

def z1248 : W := mkw 0x0a01578000d3c000 0x71f3ffe000fff000

def z1249 : W := mkw 0x4d82e81d40ec0f80 0x9677f01fc0f00fc0

def z1250 : W := mkw 0xa6433fc212396052 0xfffffff633bf79f3

def z1251 : W := mkw 0xd007ad7dad000000 0x71d3c9e9cc4cf000

def z1252 : W := mkw 0xf247bfffbf114052 0x24a7fef7f3b349f3

def z1253 : W := mkw 0xf007bfffbf000000 0x8ff7ffffff0009c0

def z1254 : W := mkw 0xf007bfffbf000000 0x2ff7ffffff0c7000

def z1255 : W := mkw 0x0da04020c5ec1f85 0xf90801e00ffcffcf

def z1256 : W := mkw 0x4d80c01d40ec0f80 0xb004001600fc0fc0

def z1257 : W := mkw 0x5024803ded041305 0x00000009cc00060c

def z1258 : W := mkw 0x4d82e81d68ec0fa8 0xb6f7f81fccfc0fcc

def z1259 : W := mkw 0x7006a83f97000000 0x06f7f81fc3000000

def z1260 : W := mkw 0x2240128212114052 0xfffc3e9633ff49f3

def z1261 : W := mkw 0x0d80400040ec0f80 0xf000000000fcffc0

def z1262 : W := mkw 0x4d82e81d40ec0f80 0xbefff81ff0fc0ff0

def z1263 : W := mkw 0x8e037fc000fbe000 0x61a3ffe000bff000

def z1264 : W := mkw 0x0801450000c28000 0xdb7bc7183cc38e3c

def z1265 : W := mkw 0xf247bfffbf114052 0x4fffffffffb348f3

def z1266 : W := mkw 0xf247bfffbf114052 0x8e2ff61fffb309f3

def z1267 : W := mkw 0x4d82e81d40ec0f80 0x0027f817c0bc08c0

def z1268 : W := mkw 0x236092baff155f7f 0xffbc369fffb34fff

def z1269 : W := mkw 0xd007ad7dad000000 0xffdbc9e9cf004103

def z1270 : W := mkw 0xf027bfffbf02902d 0x4fffffffff03f03f

def z1271 : W := mkw 0x8c036d4000eaa000 0x20c3c9e0004cf000

def z1272 : W := mkw 0x0901c51828c28c28 0xdbfbcff83cc38e3c

def z1273 : W := mkw 0xf027bfffbf001005 0xffffffffff00f10f

def z1274 : W := mkw 0x0e60400040fff357 0xf008000000ffffff

def z1275 : W := mkw 0x4c82680540ec0380 0xb6f7f80fc0fc07c0

def z1276 : W := mkw 0x4981c51d28c28ca8 0xdb7fc71e3cc38efc

def z1277 : W := mkw 0x4001851d28000000 0x0f77c71ffc000000

def z1278 : W := mkw 0x41a0803dc5041f85 0x00000009cc00060c

def z1279 : W := mkw 0x0801450000c28000 0x71d3c9e0004cf000

def z1280 : W := mkw 0x0901c51828c28c28 0xfbfbf7183cf38e3c

def z1281 : W := mkw 0x4d82e81d40ec0f80 0xf6fff81fc0ff0ff0

def z1282 : W := mkw 0x0c20400040ec1305 0xf008000000fcf70f

def z1283 : W := mkw 0x8f037fc000fbec28 0xfbfbffe80cfffe3c

def z1284 : W := mkw 0xf007bfffbf000000 0x0043c9e9cf000000

def z1285 : W := mkw 0xd107ad7dad000c28 0x8a4bc979fc000e3c

def z1286 : W := mkw 0xf007bfffbf000000 0x0ff7ffffffb008c0

def z1287 : W := mkw 0xa2433fe297114052 0xffffffffffb349f3

def z1288 : W := mkw 0x00200020c5041305 0xaec809e9cf4cf70f

def z1289 : W := mkw 0xf247bfffbf13c07a 0x4fffffffff03c03f

def z1290 : W := mkw 0xae437fc212fbe052 0xfbfbfff033fff833

def z1291 : W := mkw 0x4402a81d00280000 0x26f7f81fc03c0000

def z1292 : W := mkw 0x0d81450068ee8fa8 0xf90807003cff8ffc

def z1293 : W := mkw 0x7124803fff041f2d 0x8e0c001fff000f3f

def z1294 : W := mkw 0x0920400040c69f2d 0xd008000000cfbe3c

def z1295 : W := mkw 0xf027bfffbf001005 0x0fffffffff00000f

def z1296 : W := mkw 0xf207bfffbf114000 0x4ff7ffffff034000

def z1297 : W := mkw 0x2fe0528252fd5fd7 0xffbc369633ffffff

def z1298 : W := mkw 0xf007bfffbf000000 0x4ff7ffffff00f000

def z1299 : W := mkw 0x8e037fc000fbe000 0x30f3f9e000fcf000

def z1300 : W := mkw 0xae037fc212fbe000 0x75f7ffe603fff000

def z1301 : W := mkw 0x0901c51828c28c28 0xdf7fc71e3cc38ffc

def z1302 : W := mkw 0xf007bfffbf028028 0x0ff7ffffff00800c

def z1303 : W := mkw 0x0001052085000000 0x0ff3cfe9cf000000

def z1304 : W := mkw 0x2e60528252fff357 0xffbc369633ffffff

def z1305 : W := mkw 0x4d82e81d40ec0f80 0xfffff81fc0fc0fc0

def z1306 : W := mkw 0xf007bfffbf000000 0x9ff7ffffff400600

def z1307 : W := mkw 0x4002280500000000 0x04f7f807c0000000

def z1308 : W := mkw 0x0901c51828c28c28 0x0023c6183c830e3c

def z1309 : W := mkw 0xae437fc212fbe052 0x75f7fff633fff9f3

def z1310 : W := mkw 0x8c036d4000eaa000 0xdb7bcf7030cfb830

def z1311 : W := mkw 0x0d80400040ee8fa8 0xd008000000cf8e3c

def z1312 : W := mkw 0xf007bfffbf000000 0x0487f8e7c3000000

def z1313 : W := mkw 0x724597bfbf114052 0xfffff79fffb349f3

def z1314 : W := mkw 0x4000801d00000000 0x8604001fc00009c0

def z1315 : W := mkw 0xae437fc212fbe052 0xf9fbffe033fff9f3

def z1316 : W := mkw 0xae437fc212fbe052 0x7ffffff633fff033

def z1317 : W := mkw 0x4002a81d00000000 0x0ff7f89fc3000000

def z1318 : W := mkw 0x0d80400040eeaf80 0xb000000000fcbfc0

def z1319 : W := mkw 0xae437fc212fbe052 0x71f3ffe030fff030

def z1320 : W := mkw 0xf246baff97114052 0xfffffefff3b349f3

def z1321 : W := mkw 0xf247bfffbf114052 0xffbff69fffb349f3

def z1322 : W := mkw 0xf006baff97000000 0x0ff7f9ffcf000000

def z1323 : W := mkw 0x0d80400040ec0f80 0xb0b0300000fc0fc0

def z1324 : W := mkw 0x86033fc0003be000 0x61f3ffe0003ff000

def z1325 : W := mkw 0xf007bfffbf000000 0x0ec7f9ffff000000

def z1326 : W := mkw 0x0920400040c41f05 0xf008000000ccff0f

def z1327 : W := mkw 0x0d80400040ec0f80 0xf008000000fc4fc3

def z1328 : W := mkw 0x4d82e81d40ec0f80 0xf7f7f89fc0fc4fc0

def z1329 : W := mkw 0x82233fe08513f005 0x4ffbffe9cf03f00f

def z1330 : W := mkw 0xd007ad7dad000000 0x0067f97fcc000000

def z1331 : W := mkw 0x4901c51d28c28c28 0xdf7fc71ffcc38e3c

def z1332 : W := mkw 0xd007ad7dad000000 0x04c7f96fcc000000

def z1333 : W := mkw 0x8e037fc000fbe000 0x41f3ffe0004ff000

def z1334 : W := mkw 0x0800400000c00000 0x71f3c9e000ccf000

def z1335 : W := mkw 0x0d80400040ec0f80 0xb484300600fc0fc0

def z1336 : W := mkw 0x8c036d4000eaa000 0x1073c96000ccb000

def z1337 : W := mkw 0xae437fc212fbe052 0xffbffef633bf79f3

def z1338 : W := mkw 0x4d82e81d40ec0f80 0x06f7f81fc0fc0ec0

def z1339 : W := mkw 0x0900c01800c00c00 0xdb7bc7183cc38e3c

def z1340 : W := mkw 0x4002a81d00000000 0x00f3f809c0000000

def z1341 : W := mkw 0xd007ad7dad000000 0x0043c969cc40860c

def z1342 : W := mkw 0xf007bfffbf000000 0xffffffffff4cf103

def z1343 : W := mkw 0x0d80400040ec0f80 0x2000000000bc09c0

def z1344 : W := mkw 0x4d82e81d40ec0f80 0xa6a7f81fc0bc0fc0

def z1345 : W := mkw 0xf047bfffbf000052 0xbfffffffffb009f3

def z1346 : W := mkw 0xf007bfffbf000000 0x0047f96fcc000000

def z1347 : W := mkw 0x0e20528040fff305 0xffb8368003fff70f

def z1348 : W := mkw 0x8e037fc028fbe028 0xfbfbffe83cfff63c

def z1349 : W := mkw 0x0f80400040fd6f80 0xb000000000fc7fc0

def z1350 : W := mkw 0x8f037fc000fbec28 0x71f3ffe000fff60c

def z1351 : W := mkw 0xce837fc500fbe080 0x71f7ffe600fff0c0

def z1352 : W := mkw 0x0da0400040ec1f85 0xb000000000fc7fc3

def z1353 : W := mkw 0xf247bfffbf114052 0xffffffffff034133

def z1354 : W := mkw 0x00200020c5041305 0xffd809e9cffcffcf

def z1355 : W := mkw 0x00200020c5041305 0x4fd809e9cf4cf60f

def z1356 : W := mkw 0x8e037fc000fbe000 0x7063ff6000fff000

def z1357 : W := mkw 0x41a0803dc5041f85 0xffbc309fcfb04fcf

def z1358 : W := mkw 0x82033fe085114000 0xfffbffe9cfb34103

def z1359 : W := mkw 0xae437fc212fbe052 0x71f3ffe003fff003

def z1360 : W := mkw 0xc602badd00396000 0x26f7f8ffc03c7000

def z1361 : W := mkw 0xae037fc212fbe000 0xfffffff633fff830

def z1362 : W := mkw 0xae037fc212fbe000 0x79f3ffe033fff000

def z1363 : W := mkw 0xf007bfffbf000000 0x5ff7ffffff408000

def z1364 : W := mkw 0x00208038ed041305 0x8e080019ff00070f

def z1365 : W := mkw 0xf007bfffbf000000 0x0f47cfffff000000

def z1366 : W := mkw 0x80033fc000000000 0x01f3ffe0004cb000

def z1367 : W := mkw 0x8e037fc000fbe000 0x71d3cfe0004ff000

def z1368 : W := mkw 0xae437fc23afbe07a 0x79fbffe03ffff03f

def z1369 : W := mkw 0xf347bfffbf114c7a 0xffffffffffb34fff

def z1370 : W := mkw 0xf007ad7fbf000000 0x0843c969ff000000

def z1371 : W := mkw 0x41a0803dc5041f85 0x8604001fcc000fcc

def z1372 : W := mkw 0x8e437fc000fbe052 0xfffbffe003fff9f3

def z1373 : W := mkw 0x5006a83dad000000 0x0043c809cc000000

def z1374 : W := mkw 0x4002a83d85000000 0x06f7f8ffc3000000

def z1375 : W := mkw 0xf007bfffbf028028 0x0ff7ffffff030030

def z1376 : W := mkw 0x4002a81d00000000 0x0273c819c0000000

def z1377 : W := mkw 0xf007bfffbf000000 0xbff7ffffff000100

def z1378 : W := mkw 0xf007bfffbf000000 0x06f7ff7ffc000000

def z1379 : W := mkw 0xf007bfffbf000000 0x0fb7f69fff000000

def z1380 : W := mkw 0x8c037fc000eaa000 0x71f3ffe0004cf000

def z1381 : W := mkw 0x7007ad3fbf000000 0x0ff7ff1fff000000

def z1382 : W := mkw 0x4d82680540ec0f80 0xb004300600fc0fc0

def z1383 : W := mkw 0x0901c51828c28c28 0xcb2bc7183c838e3c

def z1384 : W := mkw 0xf207bfffbf116000 0x0ff7ffffff007000

def z1385 : W := mkw 0x4582a81d402c0f80 0xa6f7f81fc03c0fc0

def z1386 : W := mkw 0x8e037fc000fbe000 0x7bf3ffe80cfff000

def z1387 : W := mkw 0x4d82e81d40ec0f80 0xf6fff81fc0fc8fcc

def z1388 : W := mkw 0x0d80400040ec0f80 0xff98008003fc4fc3

def z1389 : W := mkw 0x8e037fc000fbe000 0x0043cf60004fb000

def z1390 : W := mkw 0x4d82e81d40ec0f80 0xfffff9ffccfcffcc

def z1391 : W := mkw 0x4002ba9d00000000 0x07f7fe9fc0000000

def z1392 : W := mkw 0xf207bfffbf13e000 0x7ff7ffffff4ff000

def z1393 : W := mkw 0x4482a81d402c0380 0x24a7f817c03c01c0

def z1394 : W := mkw 0xf247bfffbf114052 0x7fffffffffb34033

def z1395 : W := mkw 0x726492bfff155357 0xffbc369fffb34fff

def z1396 : W := mkw 0x0000801800000000 0x9273c01800800800

def z1397 : W := mkw 0x0901c51828c28c28 0xfbfbcf183ccf8e3c

def z1398 : W := mkw 0xf0073fe7bf000000 0x0df7ffe7ff000000

def z1399 : W := mkw 0x7024803fff041305 0x0e04001fff000103

def z1400 : W := mkw 0x8c037fc000eaa000 0x0063ff60004cb000

def z1401 : W := mkw 0xf007bfffbf000000 0x0ff7ffffff830830

def z1402 : W := mkw 0x6002a81f12000000 0x0ef7f81ff3000000

def z1403 : W := mkw 0xc203bfdd00114000 0xf7f7ffffc0b349c0

def z1404 : W := mkw 0xd007ad7dad000000 0x04c3c9e9cf000000

def z1405 : W := mkw 0x4d82e81d40ec0f80 0xb6f7f97fc0fcbfc0

def z1406 : W := mkw 0x4022a83d85001005 0x4ffff9ffcf00f00f

def z1407 : W := mkw 0x2240128212114052 0xffbc37963fb3c9ff

def z1408 : W := mkw 0x4d82e81d40ec0f80 0x30f7f81fc0fc0ec0

def z1409 : W := mkw 0x4d82e81d40ec0f80 0xb4a7f817c0fc0fc0

def z1410 : W := mkw 0x0d80400040ec0f80 0xf1d009e000fcffc0

def z1411 : W := mkw 0xf007bfffbf000000 0x0f27f7ffff000000

def z1412 : W := mkw 0xf007bfffbf000000 0x3ff7ffffffb00000

def z1413 : W := mkw 0xd007ad7dad000000 0x0a43c979fc000000

def z1414 : W := mkw 0xfe067ae797fbe000 0x748438e7c3fff000

def z1415 : W := mkw 0xd007ad7dad000000 0x01d3c9e9cc000000

def z1416 : W := mkw 0x2d80528252ec0f80 0xbfb4369633fc0fc0

def z1417 : W := mkw 0xf207bfffbf114000 0xffffffffffb34103

def z1418 : W := mkw 0x0dc0400040ec0fd2 0xb008000000fc0ff3

def z1419 : W := mkw 0x8e036d4000fbe000 0x4043c960004ff000

def z1420 : W := mkw 0x224197babf114052 0xffffffffffb349f3

def z1421 : W := mkw 0xf007bfffbf000000 0x0da7fff7ff000000

def z1422 : W := mkw 0xf267bfffbf115057 0xffffffffffb3f9ff

def z1423 : W := mkw 0x4c82e81d40ec0380 0x36f7f81fc0fc01c0

def z1424 : W := mkw 0x0d80400040ec0fa8 0xb008000000fc0ffc

def z1425 : W := mkw 0x2240128212114052 0xfffc379e3fb349f3

def z1426 : W := mkw 0xae437fc212fbe052 0x0067ff7630ffb8f0

def z1427 : W := mkw 0x0d80400040ec0f80 0x9000000000cc0e00

def z1428 : W := mkw 0x7024803fff041305 0x0e04001fff00060c

def z1429 : W := mkw 0x4002a81d00000000 0x0027f01600b008c0

def z1430 : W := mkw 0x0c20400040eeb305 0xf0080000004cf70f

def z1431 : W := mkw 0x4002a81d00000000 0x86f7f81fc00009c0

def z1432 : W := mkw 0x8e037fc000fbe000 0x71f7fff600fff8c0

def z1433 : W := mkw 0xb00597fabf000000 0x0ff3cff9ff000000

def z1434 : W := mkw 0x0d80400040ec0f80 0xb0000000004c0700

def z1435 : W := mkw 0xf247bfffbf114052 0xbff7ffffffb049c3

def z1436 : W := mkw 0xd007ad7dad028028 0x494bcf69fc03803c

def z1437 : W := mkw 0x7064803fff041357 0x8e0c001fff000fff

def z1438 : W := mkw 0x8e037fc000fbe000 0xfffbfff033fff933

def z1439 : W := mkw 0x80032d4000000000 0x0043c960004cb000

def z1440 : W := mkw 0x01208038ed041f2d 0x00000009cc00060c

def z1441 : W := mkw 0x4d82e81d40ec0f80 0xf6fff81fc0fc4fc3

def z1442 : W := mkw 0x4002a81d00000000 0x0ff7fe1ff0000000

def z1443 : W := mkw 0x0d80400040ec0f80 0x20000000007c07c0

def z1444 : W := mkw 0x2240128212114052 0xffbc37f633b3f9f3

def z1445 : W := mkw 0x8c036d4000eaa000 0x7043c960004cf000

def z1446 : W := mkw 0xf007bfffbf028028 0xdfffffffff83883c

def z1447 : W := mkw 0xc003bfdd00000000 0x01f3ffe9c0000000

def z1448 : W := mkw 0x8e0157c000fbe000 0x7173c7e000fff000

def z1449 : W := mkw 0x0901c51828c28c28 0xdb7ff71e3cf38efc

def z1450 : W := mkw 0x2dc0400252ec0fd2 0xbe0c001633fc0ff3

def z1451 : W := mkw 0x7006babfbf000000 0x0ff7fe9fff000000

def z1452 : W := mkw 0x8c036d4000eaa000 0xdb5bc9680c4cb60c

def z1453 : W := mkw 0x4d82e81d40ec0f80 0x0047f80fc07c06c0

def z1454 : W := mkw 0x0e80400040ffe380 0x7000000000fff1c0

def z1455 : W := mkw 0x0001851828000000 0xdb7bc7183cc38e3c

def z1456 : W := mkw 0xf047ad7fbf000052 0x8e4fc97fff0009f3

def z1457 : W := mkw 0xf007bfffbf000000 0x0ea7feffff000000

def z1458 : W := mkw 0x4d82e81d40ec0f80 0xb7f7f9ffc0fc0fc0

def z1459 : W := mkw 0x01208038ed041f2d 0xffb80699ff834f3f

def z1460 : W := mkw 0xf607bfffbf396000 0x7ff7ffffff7cf000

def z1461 : W := mkw 0x4d82e81d40ec0fa8 0xb6fff81fc0fc0ffc

def z1462 : W := mkw 0x4d82e81d40ec0f80 0xbefff81fccfc0fcc

def z1463 : W := mkw 0x8e037fc000fbe000 0x01f3ffe000ffb000

def z1464 : W := mkw 0x4d82e81d40ec0f80 0xb627f01fc0fc0fc0

def z1465 : W := mkw 0x0901c51828c28c28 0x0b73c7183cc38e3c

def z1466 : W := mkw 0xa6623ae2d73d7357 0x248438e7c33c71c3

def z1467 : W := mkw 0x6002ba9f12000000 0x06f7fe1ff0000000

def z1468 : W := mkw 0xf247bfffbf114052 0x7ff7ffffffb341c3

def z1469 : W := mkw 0x4da2e81d40ee9fad 0xf6fff81fc0ffffff

def z1470 : W := mkw 0x09214520edc69f2d 0xf90807e03fcfff3f

def z1471 : W := mkw 0xd007ad5d28000000 0x0043c809c0000000

def z1472 : W := mkw 0x0901c51828c28c28 0xd06bc7183cc38e3c

def z1473 : W := mkw 0xae437fc212fbe052 0xf5ffffe603fff9f3

def z1474 : W := mkw 0xf147bfffbf000c7a 0x8fffffffff000fff

def z1475 : W := mkw 0xf2473fe797114052 0xfffffff7f3b349f3

def z1476 : W := mkw 0x4da2e81d40ec1f85 0xfffff91fccfcffcf

def z1477 : W := mkw 0x4002a83d85000000 0x06f7f97fcc000000

def z1478 : W := mkw 0xf007bfffbf000000 0xffffffffff40c70f

def z1479 : W := mkw 0xf006baff97000000 0x0ff7fefff3000000

def z1480 : W := mkw 0x0f80400040ffef80 0x7000000000fff600

def z1481 : W := mkw 0x00200020c5041305 0x75d009e9cf4cf70f

def z1482 : W := mkw 0xf007ad7fbf000000 0x0ef7f97fff000000

def z1483 : W := mkw 0x7904c03fbfc28c28 0xde0c001fffc38e3c

def z1484 : W := mkw 0xf107bfffbf028c28 0xcfffffffff038e3c

def z1485 : W := mkw 0x8c037fc000e80000 0x71f3ffe000fcf000

def z1486 : W := mkw 0xf047bfffbf000052 0x0fffffffff000033

def z1487 : W := mkw 0x8c037fc000eaa000 0x31f3ffe000fcb000

def z1488 : W := mkw 0x0d80400040ee8f80 0xf000000000ff8fc0

def z1489 : W := mkw 0x8e037fc000fbe000 0x75f3ffe003fff103

def z1490 : W := mkw 0x4482a81d402c0380 0xb6f7f81fc07c07c0

def z1491 : W := mkw 0x0900402085c28c28 0xdfd809e9cfc38e3c

def z1492 : W := mkw 0x2240128212114052 0xfffc3ffe3fffffff

def z1493 : W := mkw 0xf007bfdf3a000000 0x07f7fffff0000000

def z1494 : W := mkw 0xf247bfffbf114052 0xfffffffffffff9f3

def z1495 : W := mkw 0xce037fc500fbe000 0x75f7ffe7c0fff000

def z1496 : W := mkw 0x0001050000000000 0x71f3cfe0004cf000

def z1497 : W := mkw 0x4d82e81d40ec0f80 0x9277f81fc0fc0ec0

def z1498 : W := mkw 0xf247bfffbf114052 0xbff7ffffffb309f0

def z1499 : W := mkw 0x0900c01840c40f00 0xb6f7f81fc0fc0fc0

def z1500 : W := mkw 0x2fc0528252ffcffa 0xffbc369633ffcfff

def z1501 : W := mkw 0x0d80400040ec0f80 0xb250000800fc0fc0

def z1502 : W := mkw 0x86033fc000396000 0x71f3ffe0007cf000

def z1503 : W := mkw 0x8e027ac000f96000 0x20a3f8e000bc7000

def z1504 : W := mkw 0xf007ad7fbf000000 0x0f77cf7fff000000

def z1505 : W := mkw 0xf247bfffbf13e052 0xffffffffffb3f9f3

def z1506 : W := mkw 0x4d82e81d40ec0f80 0x24e7f81fc0fc0fc0

def z1507 : W := mkw 0x7006a83fbf000000 0x0e47c81fff000000

def z1508 : W := mkw 0x8e036d4000fbe000 0x71d3c9e000fff000

def z1509 : W := mkw 0xf007bfffbf000000 0x06f7f9ffcf000000

def z1510 : W := mkw 0x4002a81d00000000 0x96f7f81fc0800800

def z1511 : W := mkw 0xf007bfffbf000000 0x05f7fff7f3000000

def z1512 : W := mkw 0x4002a81d00000000 0xfffff89fc3004103

def z1513 : W := mkw 0xf007bfffbf000000 0x8fffffffff000103

def z1514 : W := mkw 0xf007ad7fbf000000 0x0e07c01fff000000

def z1515 : W := mkw 0x01208038ed041f2d 0x8e080009cf00070f

def z1516 : W := mkw 0x0000803885000000 0x0ff3c9f9cf000000

def z1517 : W := mkw 0xf247bfffbf114052 0x24c7f9efcf3041c3

def z1518 : W := mkw 0xac037fc212eaa000 0x0ff7fff6334cb000

def z1519 : W := mkw 0xf207bfffbf114000 0x7ff7fffffffff000

def z1520 : W := mkw 0x8c036d4000eaa000 0x71f3f9e000fcf000

def z1521 : W := mkw 0x0f80400040fd4f80 0xf000000000ff4fc0

def z1522 : W := mkw 0x00018538ad000000 0x0043c969cc000000

def z1523 : W := mkw 0x4903ed1d28c28c28 0xffffff1ffcf38ffc

def z1524 : W := mkw 0xc003bffd85000000 0x0ff7ffffcf000000

def z1525 : W := mkw 0x8e036d4000fbe000 0x0043c96000ffb000

def z1526 : W := mkw 0x8e037fc028fbe028 0x71f3ffe00cfff00c

def z1527 : W := mkw 0xf407bfffbf280000 0x2ff7ffffff3c0000

def z1528 : W := mkw 0x2240128212114052 0xaeac369633b349f3

def z1529 : W := mkw 0x8e037fc000fbe000 0x7bf3fff030fff000

def z1530 : W := mkw 0x0d80400040ec0f80 0x0000000000fc0ec0

def z1531 : W := mkw 0x4d82e81d40ee8fa8 0xfffff91fccff8ffc

def z1532 : W := mkw 0x8c036d4000eaa000 0x0063f96000fcb000

def z1533 : W := mkw 0x0d80c01868ec0fa8 0xba0800183cfc0ffc

def z1534 : W := mkw 0x4d82e81d40ec0f80 0xffffff1ffcff8ffc

def z1535 : W := mkw 0x2240128212114052 0xcf2c369633b349f3

def z1536 : W := mkw 0x8c036d4000eaa000 0x01d3c9e0004cb000

def z1537 : W := mkw 0xd007ad7dad000000 0xdb7bcf79fc830830

def z1538 : W := mkw 0x8e2157e0c5fff305 0xf90807e00ffff70f

def z1539 : W := mkw 0xf007bfffbf000000 0xdfffffffff000000

def z1540 : W := mkw 0xae437fc212fbe052 0x7dffffe633fff1f3

def z1541 : W := mkw 0xf247bfffbf114052 0x0ff7ffffff3000c0

def z1542 : W := mkw 0x4d82e81d40ec0f80 0xfffff99fcffccfcf

def z1543 : W := mkw 0xf207bfffbf13e000 0x0ff7ffffff030000

def z1544 : W := mkw 0xd407ad7dad282000 0x0043c969cc0c3000

def z1545 : W := mkw 0x6042a81f12000052 0x8efff81ff30009f3

def z1546 : W := mkw 0xf267bfffbf115057 0x4fffffffff03f03f

def z1547 : W := mkw 0x8c036d4000eaa000 0xb6f7f97600fcb9c0

def z1548 : W := mkw 0xf027bfffbf001005 0x0ff7ffffff007003

def z1549 : W := mkw 0x8e037fc000fbe000 0x61c3ffe0007ff000

def z1550 : W := mkw 0xf207bfffbf13e000 0x7ff7ffffffb3f000

def z1551 : W := mkw 0xf007bfffbf000000 0x06f7fefff3000000

def z1552 : W := mkw 0x0100801828000c28 0xfbd809f83c4cfe3c

def z1553 : W := mkw 0x0da0400040ec1f85 0xf0080000004cf70f

def z1554 : W := mkw 0x4da3ed3dedee9fad 0x0043c969cc4cb60c

def z1555 : W := mkw 0x0901c51828c28c28 0xdffbc7983fc38e3c

def z1556 : W := mkw 0xf027bfffbf001005 0x0ff7ffffff00b00c

def z1557 : W := mkw 0x8e037fc000fbe000 0xf3f3fff000fff800

def z1558 : W := mkw 0xf247bfffbf114052 0x0ff7ffffff004003

def z1559 : W := mkw 0xf227bfffbf13f005 0x4fffffffff03f00f

def z1560 : W := mkw 0x0900400040c40f00 0xb000000000cc0f00

def z1561 : W := mkw 0xa26117e29713f057 0x490807e03f03f03f

def z1562 : W := mkw 0x0f80400040ffef80 0xb000000000ff0fc0

def z1563 : W := mkw 0xf0063ae797000000 0x04f7f8e7c3000000

def z1564 : W := mkw 0x0f20400040ffff2d 0xf008000000ffff3f

def z1565 : W := mkw 0x8e037fc028fbe028 0xfbfbfff03cfff83c

def z1566 : W := mkw 0x2240128212114052 0xfffc379633f3c9f3

def z1567 : W := mkw 0xf107bfffbf000c28 0x0ff7ffffff000830

def z1568 : W := mkw 0x0e01450000fbe000 0x71f3cfe000fff000

def z1569 : W := mkw 0xf047bfffbf000052 0x0ff7ffffff0001c3

def z1570 : W := mkw 0x7246babfbf114052 0xfffffe9fffb349f3

def z1571 : W := mkw 0xd007ad7dad000000 0x0273c979cc000000

def z1572 : W := mkw 0x2240128212114052 0xffbc369e3fb34fff

def z1573 : W := mkw 0xbe077fc23afbe000 0x71f3ffe030fff000

def z1574 : W := mkw 0x2240128212114052 0xf4ac369633b349f3

def z1575 : W := mkw 0xd007ad7dad000000 0x06d3c969cc000000

def z1576 : W := mkw 0x8c036d4000eaa000 0x4143cf60004fb000

def z1577 : W := mkw 0x4000801d00000000 0x0677c01fc0000000

def z1578 : W := mkw 0x4002a81d00000000 0x0647c81fc0000000

def z1579 : W := mkw 0xc003ad5d00000000 0x0043c969c0000000

def z1580 : W := mkw 0xf007bfffbf028000 0x4ff7ffffff038000

def z1581 : W := mkw 0x8c036d4028eaa028 0x494bcf603c4fb03c

def z1582 : W := mkw 0xd007bffdad000000 0x00c3f9e9cc000000

def z1583 : W := mkw 0x0fc0400040fd4fd2 0xb000000000ff0ff0

def z1584 : W := mkw 0x2fc0528252fd4fd2 0xb024361630ff0ff0

def z1585 : W := mkw 0x4d82e81d40ec0f80 0xfffffe9ff3ff4ff3

def z1586 : W := mkw 0xf006baff97000000 0x04a7f8f7c3000000

def z1587 : W := mkw 0x8d036d4000eaac28 0x0043c960004cb60c

def z1588 : W := mkw 0x6002babf97000000 0x0ff7ffffff000000

def z1589 : W := mkw 0xc0033fc500000000 0x05f7ffe7c0000000

def z1590 : W := mkw 0x4002a83d85000000 0x0043c969cc000000

def z1591 : W := mkw 0x8e037fc028fbe028 0x71f3ffe030fff030

def z1592 : W := mkw 0x0920400040c69f2d 0xf0080000004cf70f

def z1593 : W := mkw 0x00200020c5041305 0xfff839e9cffcf70f

def z1594 : W := mkw 0x2240128212114052 0x6dac369633b349f3

def z1595 : W := mkw 0xd207bffdad114000 0x71f3ffe9ccb34000

def z1596 : W := mkw 0x4d82e81d68ee8fa8 0xfefff81ffcff8ffc

def z1597 : W := mkw 0x4d82e81d68ec0fa8 0xfffff91ffcfc8ffc

def z1598 : W := mkw 0x8e027ac000f96000 0x71f3fee000ff7000

def z1599 : W := mkw 0xa24012c212116052 0xffbc36f633b379f3

def z1600 : W := mkw 0x4002a81d28000000 0x0ef7f81ffc000000

def z1601 : W := mkw 0x8e037fc000fbe000 0x5173ff6000ffb000

def z1602 : W := mkw 0xae437fc212fbe052 0xfbfffff630fff8f0

def z1603 : W := mkw 0x4002a81d00000000 0xdffff91fcc40860c

def z1604 : W := mkw 0xf246baff97114052 0xb6f7f8ffc3b049c3

def z1605 : W := mkw 0x01208038c5041f05 0x8e080019cf000f0f

def z1606 : W := mkw 0x4d82e81d40ec0f80 0x8667f81fc0fc0fc0

def z1607 : W := mkw 0x08214520c5c69305 0xdf7bc709cfc3870f

def z1608 : W := mkw 0x0c20400040eeb305 0x00000000004cb60c

def z1609 : W := mkw 0xf607bfffbf396000 0x0ff7ffffff300000

def z1610 : W := mkw 0xd007bffdad000000 0x0143cfe9cc000000

def z1611 : W := mkw 0x0920400040c69f2d 0xffb8069033cfff3f

def z1612 : W := mkw 0xf007bfffbf000000 0x0967ffffff000000

def z1613 : W := mkw 0x2240128212114052 0xffbc369633fff9f3

def z1614 : W := mkw 0x0e00402085fbe000 0x7fd009e9cffff000

def z1615 : W := mkw 0x2240128212114052 0xffbc369633f3cfff

def z1616 : W := mkw 0x0d80400040ec0f80 0xb230001000fc0fc0

def z1617 : W := mkw 0xf007bfffbf000000 0x0dc7ffefff000000

def z1618 : W := mkw 0xae037fc212fbe000 0x71f7fff630fff000

def z1619 : W := mkw 0xf247bfffbf114052 0x0ff7ffffff030030

def z1620 : W := mkw 0x0901c51828c28c28 0x9a7bc6183cc30e3c

def z1621 : W := mkw 0x8e037fc000fbe000 0xfbfbfff83cfffe3c

def z1622 : W := mkw 0xf007bfffbf000000 0x5ff7ffffff830000

def z1623 : W := mkw 0x0d80400040ec0f80 0xfb38061030ff0ff0

def z1624 : W := mkw 0xf247bfffbf114052 0xffbffef7f3b349f3

def z1625 : W := mkw 0xa2433fc212114052 0xfffffff633fff9f3

def z1626 : W := mkw 0x0980400040c68fa8 0xd008000000c38ffc

def z1627 : W := mkw 0x00200020c5041305 0xb6d009e9cf4cf70f

def z1628 : W := mkw 0x0d80400040ec0f80 0xb604001600fc0fc0

def z1629 : W := mkw 0x8f037fc000fbec28 0x71f3ffe000fff830

def z1630 : W := mkw 0xf487bfffbf280080 0x0ff7ffffff3000c0

def z1631 : W := mkw 0xae437fc212fbe052 0x494bcfe0334ff033

def z1632 : W := mkw 0x4102a81d28000c28 0x8efff81ffc000e3c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z4,z7,z5,z6])],[(0,[z0,z1,z8,z2,z9,z5,z6]),(0,[z0,z1,z10,z2,z4,z5,z6]),(0,[z0,z11,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z12,z5,z6]),(0,[z0,z13,z1,z14,z2,z4,z5])],[(0,[z15,z0,z1,z2,z4,z5,z16]),(0,[z0,z17,z1,z2,z4,z5,z18]),(1,[z0,z1,z2,z4,z5,z19])],[(0,[z0,z1,z2,z20,z21,z5,z6]),(0,[z0,z1,z2,z22,z4,z5,z6])],[(1,[z0,z1,z23,z4,z24,z6]),(0,[z0,z1,z25,z2,z4,z5,z26]),(0,[z0,z1,z25,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z5,z28,z6])],[(0,[z0,z1,z2,z4,z5,z6,z29]),(0,[z0,z13,z1,z2,z4,z30,z6])],[(0,[z0,z31,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z18])],[(0,[z0,z1,z2,z4,z5,z6,z33]),(0,[z0,z1,z2,z4,z34,z5,z6]),(0,[z0,z1,z2,z35,z4,z24,z6])],[(0,[z0,z1,z2,z4,z5,z36,z6]),(0,[z0,z1,z2,z4,z5,z6,z37]),(0,[z0,z1,z2,z38,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z40])],[(0,[z0,z1,z2,z4,z5,z41,z6]),(0,[z42,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z44,z18]),(0,[z0,z1,z45,z2,z4,z5,z6]),(0,[z0,z46,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z26,z47])],[(1,[z0,z1,z48,z4,z5,z6]),(0,[z49,z50,z1,z2,z4,z5,z6]),(0,[z0,z50,z1,z14,z2,z4,z5]),(0,[z0,z1,z14,z2,z4,z51,z5])],[(0,[z0,z1,z52,z2,z4,z5,z6]),(0,[z0,z1,z53,z2,z4,z5,z6]),(0,[z54,z39,z0,z1,z2,z4,z5]),(0,[z55,z0,z1,z2,z4,z24,z6]),(0,[z0,z56,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z57,z5,z6]),(0,[z0,z1,z2,z58,z4,z5,z6]),(0,[z0,z1,z2,z59,z4,z5,z6]),(1,[z0,z1,z60,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z18,z18]),(0,[z0,z1,z61,z2,z4,z62,z6])],[(0,[z63,z64,z1,z2,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z66]),(0,[z0,z1,z2,z4,z5,z67,z6]),(0,[z0,z1,z68,z2,z4,z5,z6]),(0,[z0,z1,z69,z2,z70,z4,z5]),(0,[z0,z1,z14,z2,z70,z4,z5])],[(0,[z0,z1,z2,z4,z71,z24,z6]),(0,[z0,z1,z2,z72,z4,z5,z6]),(0,[z0,z1,z2,z4,z73,z5,z6])],[(1,[z0,z13,z1,z4,z5,z26]),(0,[z0,z74,z1,z2,z4,z5,z6])]],
   [[(0,[z54,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z75,z6]),(0,[z0,z1,z61,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z26,z76]),(0,[z77,z0,z1,z2,z27,z4,z5])],[(0,[z78,z63,z1,z2,z4,z5,z6]),(1,[z0,z17,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z5,z80,z6]),(0,[z0,z1,z2,z81,z4,z5,z6]),(0,[z82,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z24,z6,z83]),(0,[z0,z1,z2,z4,z5,z84,z6]),(1,[z0,z1,z85,z2,z4,z5])],[(0,[z86,z0,z1,z2,z4,z5,z87]),(0,[z64,z0,z1,z23,z4,z5,z6]),(0,[z0,z1,z88,z2,z4,z21,z5]),(0,[z0,z1,z2,z89,z4,z5,z6])],[(0,[z0,z1,z90,z2,z4,z5,z6]),(0,[z0,z91,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z92]),(0,[z0,z1,z2,z4,z43,z93,z6]),(0,[z0,z94,z1,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z5,z16]),(0,[z0,z1,z2,z9,z4,z24,z6]),(0,[z0,z1,z2,z4,z24,z40,z6]),(0,[z0,z1,z95,z2,z4,z5,z6])],[(0,[z0,z96,z1,z2,z4,z43,z6]),(0,[z0,z97,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z6]),(1,[z0,z1,z2,z4,z5,z98]),(0,[z0,z1,z2,z4,z99,z5,z6])],[(0,[z0,z100,z1,z2,z4,z5,z6]),(0,[z101,z0,z1,z2,z4,z24,z6]),(0,[z0,z1,z14,z60,z2,z4,z5]),(0,[z0,z1,z2,z27,z4,z62,z5])],[(1,[z0,z1,z2,z4,z24,z26])],[(0,[z0,z50,z2,z102,z4,z5,z6]),(1,[z0,z1,z103,z2,z4,z5]),(0,[z0,z1,z104,z2,z4,z5,z6])],[(0,[z105,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z106,z4,z5]),(0,[z107,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z106,z5,z93,z6]),(0,[z15,z0,z1,z2,z4,z43,z6]),(1,[z0,z108,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z109,z6]),(0,[z0,z1,z110,z2,z4,z24,z6]),(1,[z0,z1,z2,z4,z111,z6]),(0,[z0,z96,z1,z2,z112,z5,z6]),(0,[z0,z1,z113,z2,z4,z5,z26]),(0,[z0,z1,z2,z4,z114,z5,z6]),(0,[z0,z1,z115,z2,z4,z5,z6])],[(0,[z0,z1,z2,z23,z4,z5,z26]),(0,[z0,z1,z2,z23,z27,z4,z5]),(0,[z0,z1,z2,z116,z4,z5,z6])],[(0,[z86,z0,z1,z2,z117,z5,z6]),(0,[z0,z46,z50,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z118])]],
   [[(1,[z0,z1,z2,z119,z5,z18])],[(1,[z0,z1,z2,z4,z5,z120]),(0,[z0,z1,z121,z2,z5,z122,z6])],[(0,[z0,z1,z123,z2,z4,z5,z6]),(1,[z0,z1,z124,z4,z5,z6]),(0,[z125,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z14,z2,z4,z5,z126]),(0,[z0,z1,z2,z27,z4,z5,z16]),(0,[z0,z1,z2,z4,z24,z24,z6]),(0,[z0,z1,z2,z4,z5,z6,z127])],[(1,[z0,z1,z2,z4,z128,z6]),(0,[z129,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z5,z83])],[(0,[z54,z15,z1,z2,z4,z5,z6]),(0,[z55,z0,z1,z2,z4,z5,z130]),(0,[z0,z1,z131,z2,z4,z5,z6]),(0,[z132,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z4,z5,z16,z18]),(0,[z134,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z135,z4,z43,z5,z6])],[(0,[z0,z1,z136,z2,z4,z5,z6]),(0,[z0,z137,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z18])],[(0,[z64,z0,z1,z2,z27,z4,z5]),(0,[z42,z1,z2,z4,z51,z5,z6]),(0,[z0,z1,z2,z4,z5,z138,z6])],[(0,[z0,z1,z2,z4,z5,z6,z139]),(0,[z0,z1,z2,z4,z140,z6,z16]),(0,[z0,z1,z141,z14,z2,z4,z5])],[(0,[z0,z1,z2,z142,z4,z5,z6]),(0,[z101,z0,z1,z2,z27,z5,z6]),(0,[z0,z1,z2,z2,z4,z43,z6])],[(1,[z0,z1,z2,z4,z143,z6]),(0,[z144,z0,z1,z2,z4,z5,z6])],[(0,[z39,z0,z1,z2,z4,z5,z26]),(0,[z39,z0,z1,z2,z27,z4,z5]),(1,[z0,z1,z2,z4,z145,z6]),(0,[z0,z1,z2,z4,z5,z146,z6])],[(0,[z147,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z148,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z149,z24,z6]),(0,[z0,z1,z61,z2,z4,z5,z6])],[(0,[z0,z50,z2,z4,z5,z79,z6]),(0,[z0,z1,z2,z4,z150,z5,z6]),(0,[z0,z1,z2,z4,z151,z5,z6])],[(0,[z0,z152,z1,z2,z4,z5,z26]),(0,[z0,z153,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z154,z5,z6]),(0,[z42,z0,z1,z14,z2,z4,z5]),(0,[z0,z46,z1,z14,z2,z4,z5]),(0,[z0,z1,z60,z2,z4,z5,z26]),(0,[z0,z1,z60,z2,z27,z4,z5]),(0,[z0,z1,z2,z27,z4,z4,z5])]],
   [[(0,[z64,z1,z110,z2,z4,z5,z6]),(0,[z0,z1,z2,z70,z4,z24,z6])],[(0,[z0,z1,z2,z4,z5,z155,z6]),(0,[z0,z1,z2,z4,z32,z71,z6]),(0,[z156,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z8,z2,z4,z5,z26]),(0,[z0,z1,z8,z2,z27,z4,z5])],[(0,[z0,z1,z157,z2,z27,z4,z5]),(1,[z0,z1,z2,z4,z158,z6]),(0,[z159,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z20,z5,z18]),(0,[z0,z1,z2,z4,z160,z5,z6]),(0,[z0,z1,z161,z2,z4,z5,z6])],[(0,[z0,z1,z25,z23,z4,z5,z6]),(0,[z0,z1,z2,z162,z4,z5,z6]),(0,[z0,z163,z1,z2,z4,z5,z18]),(1,[z0,z1,z2,z4,z32,z83])],[(0,[z0,z46,z2,z4,z71,z5,z6]),(1,[z0,z1,z2,z4,z43,z18]),(0,[z0,z1,z2,z164,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z165,z6])],[(1,[z0,z1,z2,z4,z166,z5]),(0,[z0,z167,z1,z2,z4,z5,z26]),(0,[z168,z0,z1,z2,z4,z5,z6])],[(0,[z101,z0,z1,z2,z21,z5,z6]),(0,[z169,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z170,z6]),(1,[z0,z1,z171,z2,z4,z5])],[(1,[z0,z1,z2,z4,z172,z6])],[(0,[z0,z1,z2,z4,z5,z6,z16]),(0,[z0,z1,z2,z4,z5,z173,z6])],[(0,[z0,z1,z174,z2,z4,z5,z6]),(0,[z0,z1,z2,z106,z4,z5,z18]),(0,[z0,z96,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z112,z43,z6]),(0,[z0,z1,z2,z4,z175,z5,z6]),(0,[z0,z1,z2,z27,z4,z43,z6])],[(0,[z86,z0,z1,z2,z4,z36,z6]),(0,[z0,z1,z176,z2,z4,z5,z6]),(1,[z0,z177,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z178,z5,z6])],[(0,[z0,z1,z2,z4,z5,z40,z44]),(0,[z0,z1,z2,z4,z179,z5,z6]),(1,[z0,z1,z2,z4,z5,z180]),(0,[z0,z1,z2,z4,z181,z5,z6]),(0,[z182,z0,z1,z2,z4,z5,z26]),(0,[z182,z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z183,z5,z6])],[(0,[z0,z1,z2,z4,z71,z51,z6]),(0,[z0,z1,z2,z184,z4,z5,z6]),(1,[z0,z1,z2,z185,z186,z6])],[(0,[z0,z1,z48,z2,z4,z5,z6]),(0,[z0,z1,z2,z187,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z188]),(0,[z0,z1,z189,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z43,z43,z6])],[(0,[z15,z0,z1,z14,z2,z4,z5])],[(0,[z0,z1,z2,z27,z112,z5,z6]),(0,[z0,z1,z2,z4,z5,z190,z6])],[(1,[z0,z1,z191,z4,z5,z6]),(0,[z0,z192,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z193,z6])],[(0,[z194,z0,z1,z2,z4,z5,z6])],[],[(0,[z0,z1,z195,z2,z4,z5,z6]),(0,[z0,z1,z2,z196,z4,z5,z6]),(1,[z197,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z71,z5])],[(0,[z0,z1,z2,z4,z198,z5,z6]),(0,[z0,z1,z2,z4,z24,z122,z6]),(0,[z0,z1,z2,z4,z5,z6,z199])],[(0,[z0,z200,z1,z2,z4,z5,z6]),(1,[z0,z1,z88,z2,z4,z5])],[(0,[z0,z1,z2,z201,z4,z5,z6]),(0,[z0,z1,z202,z2,z4,z5,z6])],[(0,[z0,z1,z203,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z204,z5,z6]),(0,[z205,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z206,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z207,z6]),(0,[z0,z1,z2,z4,z5,z208,z6]),(0,[z78,z0,z1,z2,z4,z5,z18])],[(0,[z209,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z26,z16]),(0,[z55,z0,z1,z2,z4,z5,z26]),(0,[z55,z0,z1,z2,z27,z4,z5]),(0,[z210,z0,z1,z2,z4,z5,z18])],[(1,[z125,z1,z2,z4,z126,z6]),(0,[z0,z211,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z212]),(0,[z0,z1,z2,z4,z24,z213,z6]),(2,[z0,z1,z2,z119,z5])],[(0,[z0,z1,z2,z4,z214,z5,z6]),(0,[z0,z1,z2,z4,z5,z215,z6]),(0,[z0,z1,z2,z4,z71,z5,z26]),(1,[z0,z1,z2,z216,z5,z6]),(0,[z0,z1,z2,z4,z217,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z218,z6]),(0,[z0,z1,z2,z4,z5,z219,z6]),(0,[z0,z1,z2,z9,z70,z5,z6]),(0,[z0,z1,z121,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z212]),(0,[z0,z220,z1,z2,z4,z5,z6]),(0,[z0,z1,z221,z2,z4,z5,z6])],[(0,[z0,z222,z1,z2,z4,z5,z18]),(0,[z0,z1,z135,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z223,z6])],[(0,[z0,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z224,z5,z6])],[(0,[z78,z0,z1,z2,z106,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z225]),(0,[z0,z1,z2,z4,z5,z6,z226]),(0,[z0,z1,z2,z227,z4,z5,z6])],[(0,[z49,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z43,z73,z6])],[(0,[z65,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z9,z4,z5,z26]),(0,[z0,z1,z228,z2,z4,z5,z6])],[(0,[z229,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z230,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z231,z5,z6]),(0,[z0,z1,z2,z4,z21,z5,z6]),(0,[z0,z1,z2,z232,z4,z5,z6])],[(0,[z0,z1,z2,z112,z20,z5,z6]),(0,[z0,z1,z2,z4,z71,z126,z6]),(0,[z101,z0,z1,z2,z4,z5,z26])],[(0,[z0,z1,z2,z102,z4,z24,z6]),(0,[z0,z1,z2,z4,z233,z5,z6]),(0,[z234,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z69,z2,z4,z5])],[(0,[z0,z1,z235,z2,z4,z5,z6]),(0,[z236,z0,z1,z2,z27,z4,z5])],[(0,[z0,z222,z1,z102,z4,z5,z6]),(1,[z0,z1,z2,z4,z237,z6]),(0,[z0,z1,z2,z119,z4,z5,z6])],[(0,[z0,z1,z110,z2,z4,z5,z26]),(0,[z0,z1,z110,z2,z27,z4,z5]),(1,[z0,z1,z2,z27,z9,z5]),(0,[z0,z163,z1,z2,z4,z128,z6])],[(0,[z0,z1,z238,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z239,z6]),(0,[z240,z0,z1,z2,z4,z5,z6]),(0,[z241,z0,z1,z2,z4,z5,z6])],[(0,[z0,z13,z1,z2,z4,z24,z6])],[(0,[z0,z17,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z242,z5,z6])],[(0,[z55,z0,z222,z2,z4,z5,z6]),(0,[z243,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z111,z5,z6]),(0,[z244,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z245,z2,z4,z5])],[(0,[z0,z246,z1,z2,z4,z5,z6]),(0,[z0,z247,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z248,z6]),(0,[z0,z163,z1,z2,z4,z145,z6]),(0,[z0,z1,z2,z4,z32,z5,z6])],[(0,[z0,z1,z14,z110,z2,z4,z5]),(0,[z0,z1,z2,z4,z249,z5,z6]),(0,[z0,z1,z2,z250,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z251])],[(0,[z0,z1,z2,z4,z5,z6,z252]),(0,[z0,z1,z2,z4,z253,z5,z6]),(0,[z0,z1,z2,z254,z27,z4,z5])],[(0,[z210,z0,z1,z2,z4,z5,z6]),(0,[z42,z0,z1,z2,z4,z32,z6]),(0,[z0,z1,z2,z4,z5,z44,z6]),(0,[z0,z96,z1,z2,z9,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z26]),(1,[z0,z1,z2,z4,z255,z6])],[(0,[z0,z50,z1,z2,z4,z24,z6]),(1,[z246,z1,z2,z4,z5,z6]),(0,[z256,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z185,z4,z5])],[(0,[z0,z1,z2,z4,z5,z79,z26]),(0,[z39,z0,z1,z2,z4,z5,z83])],[(0,[z0,z1,z257,z2,z4,z5,z6]),(0,[z0,z1,z2,z258,z4,z5,z6])],[],[(0,[z0,z1,z2,z9,z20,z5,z6]),(0,[z54,z0,z1,z61,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z259])],[(0,[z54,z0,z1,z2,z4,z24,z6]),(0,[z39,z15,z0,z1,z2,z4,z5]),(0,[z55,z0,z1,z2,z260,z5,z6]),(0,[z0,z1,z2,z261,z4,z5,z6])]],
   [[(0,[z262,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z263,z6]),(0,[z0,z17,z1,z2,z4,z71,z6])],[(0,[z209,z0,z1,z2,z4,z239,z6]),(0,[z0,z1,z2,z4,z5,z6,z264]),(0,[z0,z1,z2,z27,z4,z21,z5]),(0,[z0,z1,z2,z70,z4,z5,z26]),(1,[z0,z1,z2,z4,z5,z190]),(0,[z0,z152,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z43,z6,z83]),(0,[z0,z265,z1,z2,z4,z5,z6])],[(0,[z0,z222,z1,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z6,z18])],[(0,[z0,z1,z14,z2,z102,z4,z5]),(0,[z39,z0,z163,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z43,z40,z6]),(0,[z266,z0,z1,z2,z4,z24,z6])],[(0,[z0,z94,z1,z14,z2,z4,z5])],[(0,[z267,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z268,z6]),(0,[z0,z1,z2,z185,z186,z5,z6])],[(0,[z269,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z270]),(0,[z271,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z272,z5,z6])],[(0,[z0,z1,z2,z4,z273,z5,z6]),(0,[z0,z1,z135,z2,z4,z5,z180])],[(0,[z0,z274,z1,z157,z2,z4,z6])],[(0,[z275,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z276,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z277])],[(0,[z86,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z203,z157,z2,z4,z5]),(0,[z278,z0,z1,z2,z4,z5,z6])],[(0,[z279,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z23,z102,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z26,z280]),(0,[z0,z1,z2,z281,z4,z5,z6])],[(1,[z0,z1,z2,z119,z5,z6]),(0,[z0,z1,z245,z2,z4,z5,z6])]],
   [[(0,[z282,z0,z1,z2,z4,z5,z6]),(1,[z0,z163,z2,z4,z5,z40]),(0,[z0,z1,z2,z4,z7,z43,z6]),(0,[z283,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z284,z4,z5,z6]),(0,[z125,z0,z1,z2,z4,z24,z6]),(0,[z0,z285,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z286]),(0,[z0,z1,z2,z4,z5,z287,z6]),(0,[z0,z1,z2,z4,z43,z24,z6]),(0,[z0,z1,z288,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z289,z5,z126]),(0,[z0,z1,z2,z4,z290,z5,z6]),(0,[z0,z1,z2,z4,z43,z79,z6]),(1,[z0,z1,z2,z4,z291,z6]),(0,[z0,z1,z69,z2,z4,z5,z18]),(0,[z0,z1,z14,z2,z4,z5,z18]),(1,[z0,z1,z14,z2,z5,z122])],[(0,[z0,z1,z2,z4,z5,z6,z292]),(0,[z0,z1,z293,z2,z4,z5,z6])],[(0,[z0,z1,z294,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z6])],[(0,[z295,z0,z1,z2,z4,z5,z6]),(0,[z125,z0,z296,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z297,z5,z6])],[(0,[z298,z0,z1,z2,z4,z5,z6])],[(0,[z0,z299,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z300,z6]),(0,[z0,z301,z1,z2,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z62,z5])],[(0,[z0,z1,z2,z70,z20,z5,z6]),(0,[z0,z1,z2,z4,z302,z5,z6]),(0,[z0,z1,z121,z2,z4,z5,z212])],[(0,[z0,z1,z2,z4,z5,z6,z303]),(0,[z0,z1,z2,z4,z304,z5,z6]),(0,[z0,z163,z1,z2,z216,z5,z6])],[],[(1,[z0,z1,z2,z4,z305,z6]),(0,[z0,z1,z121,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z306,z5,z6])],[(0,[z0,z1,z135,z2,z4,z43,z6])],[(0,[z86,z0,z1,z48,z4,z5,z6]),(0,[z0,z1,z23,z4,z5,z24,z6]),(0,[z0,z1,z307,z2,z4,z20,z5]),(0,[z42,z0,z1,z2,z4,z24,z6]),(1,[z0,z96,z2,z112,z5,z6]),(0,[z0,z46,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z122,z26])],[(0,[z50,z1,z157,z2,z4,z5,z6]),(0,[z308,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z309,z6])]],
   [[(0,[z0,z1,z14,z2,z23,z4,z5]),(0,[z0,z1,z2,z4,z51,z5,z18]),(0,[z310,z0,z1,z2,z4,z5,z6]),(0,[z0,z46,z1,z2,z4,z79,z6]),(0,[z0,z1,z2,z311,z4,z5,z6]),(0,[z156,z0,z1,z2,z4,z5,z6])],[(0,[z54,z0,z1,z2,z4,z5,z44]),(0,[z312,z0,z1,z2,z4,z5,z6])],[(1,[z86,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z20,z5,z6]),(1,[z313,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z314,z5,z6])],[(0,[z86,z0,z1,z2,z315,z5,z6]),(0,[z316,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z71,z6]),(0,[z0,z163,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z21,z43,z6]),(1,[z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z317,z6])],[(0,[z0,z1,z2,z4,z5,z318,z6]),(1,[z0,z1,z2,z4,z5,z226]),(0,[z0,z1,z2,z4,z319,z5,z6])],[(0,[z0,z1,z2,z4,z140,z5,z6]),(0,[z0,z1,z2,z4,z320,z5,z6]),(0,[z101,z0,z1,z2,z70,z5,z6]),(0,[z0,z1,z2,z4,z5,z321,z6]),(0,[z0,z1,z2,z4,z233,z43,z6]),(0,[z0,z1,z2,z27,z4,z5,z280])],[(0,[z322,z0,z1,z2,z4,z5,z26])],[(1,[z0,z1,z203,z2,z4,z5]),(0,[z0,z1,z25,z2,z4,z5,z323]),(0,[z0,z96,z1,z2,z4,z5,z26])],[(0,[z0,z1,z307,z2,z4,z5,z6]),(1,[z0,z1,z2,z27,z4,z24])],[(0,[z0,z1,z2,z106,z4,z5,z6]),(0,[z0,z1,z324,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z4,z24,z6])],[(0,[z0,z325,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z126,z79,z6]),(0,[z0,z1,z2,z102,z4,z5,z26]),(0,[z0,z1,z2,z102,z27,z4,z5]),(0,[z0,z1,z2,z326,z4,z5,z6]),(0,[z327,z0,z1,z2,z4,z5,z6]),(0,[z328,z0,z1,z2,z4,z24,z6])],[(0,[z0,z1,z2,z4,z260,z5,z6]),(0,[z101,z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z5,z93,z18]),(0,[z0,z1,z2,z119,z5,z6,z18])],[(1,[z0,z1,z2,z22,z4,z5]),(0,[z0,z1,z14,z329,z2,z4,z5])],[(0,[z330,z0,z1,z2,z4,z5,z6]),(0,[z0,z17,z1,z2,z4,z43,z6]),(0,[z0,z1,z14,z2,z4,z5,z24]),(0,[z0,z1,z2,z4,z5,z331,z6])],[(0,[z0,z1,z2,z4,z332,z5,z6]),(0,[z125,z0,z1,z2,z4,z32,z6]),(0,[z15,z0,z1,z61,z2,z4,z5]),(0,[z0,z333,z1,z2,z4,z5,z18])]],
   [[(0,[z15,z0,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z334,z5,z6])],[(0,[z0,z1,z2,z4,z24,z26,z6])],[(0,[z335,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z43,z6]),(0,[z0,z13,z1,z2,z4,z5,z26]),(0,[z0,z13,z1,z2,z27,z4,z5])],[(0,[z0,z336,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z337]),(1,[z0,z1,z2,z4,z57,z6]),(0,[z0,z1,z2,z4,z5,z6,z338])],[(0,[z0,z1,z25,z2,z4,z5,z18])],[(1,[z39,z0,z2,z4,z5,z339]),(0,[z0,z1,z2,z4,z43,z122,z6])],[(0,[z0,z1,z2,z20,z5,z93,z6]),(0,[z0,z1,z2,z4,z340,z5,z6]),(0,[z0,z1,z2,z4,z341,z5,z6])],[(1,[z0,z1,z2,z4,z5,z251]),(0,[z65,z0,z96,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z252])],[(1,[z0,z342,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z343,z5,z6]),(0,[z0,z1,z2,z112,z186,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z79])],[(0,[z0,z50,z1,z2,z4,z5,z26]),(0,[z0,z50,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z344,z4,z5,z6]),(0,[z78,z0,z1,z2,z4,z5,z6]),(0,[z15,z0,z1,z2,z345,z5,z6]),(0,[z0,z1,z108,z2,z4,z5,z6]),(1,[z0,z152,z1,z4,z24,z6]),(0,[z0,z1,z61,z2,z4,z43,z6]),(0,[z0,z1,z346,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z347,z6]),(0,[z0,z1,z14,z2,z4,z5,z93])],[(0,[z209,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z5,z6]),(0,[z0,z163,z1,z2,z4,z62,z5]),(0,[z0,z1,z2,z4,z5,z199,z18])],[(0,[z0,z348,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z24,z6]),(0,[z0,z1,z2,z185,z4,z5,z18])],[(0,[z0,z1,z2,z106,z5,z122,z6]),(0,[z0,z1,z2,z4,z5,z349,z18]),(0,[z0,z1,z2,z4,z5,z6,z280])],[(0,[z0,z96,z2,z4,z112,z5,z6]),(1,[z0,z1,z2,z119,z4,z5])]],
   [[(1,[z350,z0,z1,z2,z4,z5]),(0,[z54,z0,z1,z2,z4,z5,z26]),(0,[z54,z0,z1,z2,z27,z4,z5]),(0,[z0,z222,z1,z2,z4,z5,z6])],[(0,[z125,z0,z1,z2,z4,z51,z6]),(0,[z0,z1,z2,z4,z43,z51,z6]),(0,[z0,z1,z2,z4,z5,z6,z351])],[(0,[z0,z1,z352,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z5,z93,z6]),(0,[z0,z353,z1,z2,z4,z5,z6])],[(0,[z354,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z135,z110,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z286,z6]),(1,[z0,z1,z2,z4,z355,z6])],[(0,[z49,z0,z1,z2,z4,z5,z6]),(0,[z356,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z126,z26]),(0,[z0,z1,z357,z2,z4,z5,z6])],[(0,[z0,z1,z2,z185,z106,z5,z6]),(0,[z0,z1,z2,z4,z358,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z6,z359])],[(0,[z0,z1,z2,z4,z5,z128,z6])],[(0,[z0,z222,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z43,z5]),(0,[z0,z1,z2,z185,z4,z186,z6]),(0,[z360,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z361,z6])],[(0,[z0,z1,z2,z4,z5,z362,z6]),(0,[z0,z1,z2,z4,z5,z363,z6]),(1,[z0,z1,z2,z4,z24,z18]),(1,[z0,z1,z14,z2,z4,z5])],[(0,[z15,z0,z1,z2,z320,z5,z6]),(0,[z65,z0,z1,z2,z4,z237,z6])],[(0,[z49,z0,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z364,z5,z6]),(0,[z0,z1,z365,z2,z4,z5,z6]),(0,[z0,z366,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z367,z5,z6]),(0,[z0,z368,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z369,z4,z5,z6]),(0,[z370,z0,z1,z2,z4,z5,z6]),(0,[z0,z371,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z277])],[(0,[z0,z1,z2,z4,z117,z5,z6]),(0,[z0,z1,z2,z4,z372,z5,z6]),(1,[z0,z1,z2,z4,z30,z6])],[(0,[z0,z1,z2,z23,z4,z5,z18]),(1,[z78,z1,z2,z20,z5,z6]),(0,[z42,z0,z1,z2,z4,z51,z6])],[(0,[z0,z1,z2,z4,z5,z373,z6]),(0,[z0,z1,z2,z4,z112,z24,z6]),(0,[z0,z1,z2,z9,z186,z5,z6]),(0,[z0,z1,z2,z27,z4,z24,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z374]),(1,[z0,z1,z2,z27,z106,z5]),(1,[z366,z1,z2,z4,z5,z6]),(0,[z101,z0,z1,z2,z4,z75,z6])],[(0,[z0,z50,z222,z2,z4,z5,z6]),(0,[z101,z0,z1,z2,z4,z99,z6]),(0,[z0,z1,z2,z4,z62,z43,z6]),(0,[z0,z1,z375,z2,z4,z5,z6]),(0,[z240,z0,z1,z14,z2,z4,z5])],[(0,[z0,z376,z1,z2,z4,z5,z6]),(0,[z125,z0,z1,z2,z4,z5,z26]),(0,[z125,z0,z1,z2,z27,z4,z5]),(0,[z15,z0,z1,z2,z4,z5,z44]),(1,[z0,z1,z2,z4,z358,z6]),(0,[z0,z377,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z339]),(0,[z0,z1,z2,z4,z43,z5,z26]),(0,[z0,z1,z2,z4,z5,z18,z259])],[(0,[z0,z17,z1,z14,z2,z4,z5]),(0,[z298,z0,z1,z2,z4,z43,z6])],[(0,[z0,z274,z1,z2,z4,z5,z6]),(0,[z0,z1,z378,z2,z4,z5,z6]),(1,[z0,z1,z61,z2,z4,z62])],[(0,[z1,z2,z23,z4,z20,z5,z6]),(0,[z0,z1,z2,z4,z379,z5,z6]),(0,[z0,z1,z2,z4,z5,z158,z6]),(0,[z0,z46,z17,z2,z4,z5,z6]),(0,[z0,z1,z380,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z224,z21,z5])],[(0,[z54,z0,z1,z2,z4,z32,z5]),(0,[z0,z1,z2,z4,z5,z26,z40]),(1,[z0,z1,z135,z4,z43,z6])],[(0,[z64,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z110,z102,z4,z5,z6]),(0,[z0,z381,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z382,z6]),(0,[z0,z1,z2,z4,z24,z219,z6]),(0,[z383,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z186,z5,z18])],[(0,[z0,z384,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z385,z5,z6])],[(0,[z0,z1,z2,z4,z5,z26,z44])],[(0,[z0,z1,z2,z4,z5,z349,z6]),(0,[z0,z1,z2,z5,z349,z6,z18])],[(0,[z0,z1,z2,z386,z4,z5,z6]),(0,[z0,z1,z387,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z112,z5]),(0,[z388,z0,z1,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z18])],[(0,[z0,z1,z2,z4,z5,z172,z6]),(0,[z125,z0,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z43,z126,z6])],[(0,[z389,z0,z1,z2,z4,z5,z6]),(0,[z0,z222,z25,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z390]),(0,[z0,z1,z2,z4,z20,z43,z6]),(0,[z0,z1,z103,z2,z4,z5,z126]),(1,[z0,z1,z2,z4,z5,z391])],[(0,[z42,z0,z1,z2,z4,z5,z26]),(0,[z42,z0,z1,z2,z27,z4,z5]),(0,[z0,z46,z1,z2,z4,z5,z26]),(0,[z0,z46,z1,z2,z27,z4,z5]),(0,[z0,z163,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z392,z24,z6]),(0,[z0,z1,z2,z393,z27,z4,z5])]],
   [[(0,[z63,z0,z1,z2,z106,z5,z6]),(0,[z0,z1,z2,z4,z394,z5,z6])],[(0,[z0,z1,z2,z27,z9,z5,z6]),(0,[z0,z1,z2,z4,z43,z6,z18]),(0,[z0,z1,z8,z2,z4,z5,z18]),(0,[z0,z1,z2,z186,z5,z93,z6])],[(0,[z0,z1,z157,z2,z4,z5,z18]),(0,[z0,z395,z1,z2,z4,z5,z6])],[(1,[z0,z1,z2,z4,z5,z268]),(0,[z313,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z26,z396]),(0,[z0,z1,z2,z4,z5,z26,z347]),(0,[z0,z1,z2,z4,z32,z6,z83])],[(0,[z0,z397,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z21,z24,z6])],[(0,[z0,z1,z2,z106,z4,z43,z6])],[(0,[z0,z1,z14,z2,z4,z20,z5]),(0,[z0,z1,z2,z185,z4,z71,z6])],[(0,[z0,z1,z2,z398,z4,z5,z6]),(0,[z0,z1,z110,z4,z5,z24,z6]),(0,[z399,z0,z1,z2,z4,z5,z6])],[(0,[z42,z0,z1,z2,z4,z126,z6]),(0,[z400,z0,z1,z2,z4,z5,z6])],[(1,[z0,z296,z2,z4,z5,z6]),(0,[z125,z0,z1,z2,z4,z5,z155]),(0,[z39,z0,z2,z4,z5,z6,z339]),(0,[z0,z1,z2,z4,z5,z6,z339]),(0,[z0,z1,z2,z4,z401,z5,z6]),(0,[z0,z402,z1,z2,z4,z5,z6])],[(0,[z86,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z27,z20,z5]),(0,[z197,z0,z1,z2,z4,z5,z6]),(0,[z0,z96,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z403,z5,z6]),(0,[z0,z1,z404,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z109,z26]),(0,[z0,z1,z8,z2,z4,z186,z6]),(0,[z0,z1,z405,z2,z4,z5,z6]),(0,[z0,z1,z406,z2,z4,z5,z6])],[(1,[z0,z1,z2,z284,z5,z6]),(0,[z0,z1,z110,z25,z4,z5,z6]),(0,[z125,z0,z1,z8,z2,z4,z6]),(0,[z0,z1,z2,z4,z126,z24,z6]),(0,[z0,z1,z2,z4,z407,z5,z6]),(0,[z408,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z409,z2,z4,z5,z6])],[],[(1,[z0,z1,z2,z4,z5,z410]),(0,[z0,z2,z102,z4,z112,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z40]),(1,[z0,z1,z14,z2,z27,z5])],[]],
   [[(0,[z65,z0,z2,z9,z4,z5,z6])],[(0,[z15,z0,z1,z2,z4,z5,z26]),(0,[z15,z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z27,z4,z5,z44]),(0,[z0,z1,z411,z2,z4,z5,z6])],[(0,[z86,z0,z157,z2,z4,z5,z6]),(0,[z0,z1,z69,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z5,z6])],[(0,[z412,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z186,z5,z6]),(1,[z0,z1,z2,z4,z5,z413])],[(0,[z209,z0,z1,z2,z4,z5,z268]),(0,[z63,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z414,z6]),(0,[z0,z17,z2,z4,z5,z79,z6]),(0,[z0,z1,z2,z4,z32,z79,z6])],[(0,[z415,z0,z1,z2,z4,z5,z6])],[(0,[z78,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z6,z416]),(0,[z0,z1,z2,z4,z417,z5,z18])],[(0,[z209,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z216,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z418]),(0,[z0,z1,z419,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z26,z26])],[(0,[z42,z0,z1,z8,z2,z4,z6]),(0,[z420,z0,z1,z2,z4,z5,z6]),(0,[z0,z152,z1,z2,z4,z5,z92]),(0,[z0,z421,z1,z2,z4,z5,z6])],[(1,[z0,z274,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z422]),(0,[z78,z1,z2,z4,z20,z5,z6]),(0,[z0,z1,z2,z5,z122,z6,z280])],[(0,[z0,z1,z2,z4,z5,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z16]),(0,[z0,z152,z1,z4,z5,z24,z6])],[(0,[z0,z222,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z423,z6]),(0,[z0,z1,z121,z2,z21,z5,z6]),(1,[z0,z1,z4,z43,z24,z6]),(0,[z0,z1,z61,z2,z4,z24,z6])],[(0,[z1,z2,z4,z51,z5,z126,z6]),(0,[z0,z1,z2,z4,z424,z5,z6]),(0,[z55,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z26,z339])],[(1,[z0,z222,z25,z4,z5,z6]),(0,[z0,z1,z2,z2,z4,z5,z26]),(0,[z0,z1,z2,z4,z5,z425,z6]),(0,[z0,z1,z2,z4,z426,z5,z6])],[(0,[z350,z0,z1,z2,z4,z5,z6]),(0,[z427,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z428,z5,z6]),(0,[z0,z1,z429,z2,z4,z5,z6]),(0,[z0,z1,z430,z2,z4,z5,z6]),(0,[z0,z1,z431,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z5,z18])]],
   [[(0,[z49,z0,z1,z2,z4,z43,z6]),(0,[z63,z0,z1,z2,z4,z5,z120]),(0,[z0,z1,z2,z4,z5,z237,z6])],[(0,[z65,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z432,z5,z6])],[(0,[z0,z1,z2,z4,z433,z5,z6]),(0,[z0,z1,z2,z4,z166,z5,z6])],[],[(1,[z0,z1,z2,z4,z434,z6]),(0,[z435,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z436,z6]),(0,[z0,z1,z2,z4,z24,z6,z16]),(0,[z0,z437,z1,z2,z4,z5,z6]),(0,[z0,z163,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z438]),(0,[z0,z1,z2,z439,z4,z5,z6])],[(0,[z0,z1,z440,z2,z4,z5,z6])],[(0,[z0,z1,z2,z9,z4,z5,z18]),(0,[z0,z1,z14,z2,z5,z122,z6])],[(0,[z0,z441,z1,z2,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z32,z5])],[(0,[z65,z0,z1,z2,z112,z5,z6])],[(0,[z55,z0,z1,z102,z4,z5,z6]),(0,[z0,z1,z60,z4,z5,z6,z18])],[(0,[z442,z0,z1,z2,z4,z5,z26])],[(1,[z0,z1,z2,z4,z443,z6]),(0,[z0,z1,z2,z4,z5,z93,z6]),(0,[z0,z1,z14,z2,z4,z62,z5])],[(1,[z54,z1,z2,z4,z5,z16]),(0,[z444,z0,z1,z2,z4,z5,z6]),(0,[z0,z445,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z40,z18])],[(1,[z0,z1,z2,z4,z5,z446])],[(0,[z209,z0,z342,z2,z4,z5,z6]),(0,[z0,z1,z110,z2,z4,z5,z18]),(0,[z0,z1,z14,z2,z106,z4,z5]),(0,[z0,z1,z2,z272,z4,z5,z6]),(0,[z0,z333,z1,z2,z4,z5,z6])],[(0,[z447,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z189,z2,z4,z24,z6])]],
   [[(0,[z0,z1,z2,z4,z112,z5,z26]),(0,[z0,z1,z2,z4,z5,z448,z6]),(0,[z0,z1,z2,z4,z43,z181,z6]),(0,[z0,z1,z2,z4,z43,z26,z6]),(0,[z0,z1,z2,z27,z4,z5,z26]),(0,[z449,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z27,z4,z5])],[(0,[z450,z0,z1,z2,z4,z5,z6]),(0,[z0,z451,z1,z2,z4,z5,z6]),(0,[z0,z1,z452,z2,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z57,z6]),(0,[z0,z1,z2,z27,z9,z4,z5]),(0,[z453,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z454]),(0,[z0,z1,z2,z4,z5,z18,z280])],[(0,[z101,z0,z1,z2,z4,z5,z19]),(0,[z0,z1,z2,z4,z5,z355,z6])],[(1,[z0,z455,z1,z2,z4,z6]),(0,[z0,z1,z25,z2,z4,z5,z6])],[(0,[z49,z0,z50,z2,z4,z5,z6])],[],[(0,[z0,z163,z2,z4,z5,z40,z6]),(0,[z0,z1,z2,z456,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z457,z6]),(0,[z458,z0,z1,z2,z4,z5,z6])],[(0,[z459,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z460,z4,z5,z6]),(0,[z0,z1,z2,z4,z461,z5,z6]),(0,[z0,z1,z14,z2,z4,z186,z5]),(0,[z0,z1,z2,z462,z4,z5,z6]),(0,[z0,z463,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z464,z4,z20,z5]),(0,[z0,z1,z2,z4,z465,z5,z6]),(0,[z0,z1,z61,z2,z4,z32,z6])],[(0,[z0,z1,z466,z2,z4,z5,z6]),(0,[z0,z467,z1,z2,z4,z5,z6]),(0,[z468,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z79,z18]),(0,[z0,z1,z61,z2,z4,z5,z40]),(0,[z0,z1,z2,z27,z164,z4,z5])],[(0,[z0,z469,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z305,z5,z6]),(0,[z78,z0,z1,z14,z2,z4,z5]),(1,[z0,z1,z307,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z470,z6]),(0,[z0,z1,z2,z4,z394,z43,z6]),(0,[z0,z1,z2,z185,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z471,z6])],[(0,[z209,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z24,z321,z6])],[(0,[z209,z0,z1,z110,z4,z5,z6]),(0,[z55,z0,z1,z25,z4,z5,z6])],[(0,[z77,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z472,z6]),(0,[z0,z1,z2,z4,z5,z473,z6])]],
   [[(0,[z0,z1,z2,z4,z474,z5,z6]),(1,[z42,z1,z2,z4,z51,z6]),(0,[z101,z0,z1,z2,z4,z5,z423]),(0,[z0,z1,z121,z2,z4,z24,z6]),(0,[z0,z1,z85,z2,z4,z5,z93])],[(0,[z0,z222,z1,z14,z2,z4,z5]),(0,[z0,z152,z1,z2,z4,z5,z18]),(0,[z0,z1,z135,z2,z4,z24,z6])],[(1,[z209,z1,z23,z4,z5,z6]),(0,[z475,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z27,z112,z5]),(0,[z0,z1,z2,z4,z5,z476,z6]),(0,[z0,z1,z60,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z6,z477]),(0,[z82,z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z14,z2,z4,z4,z5])],[],[(0,[z0,z1,z2,z4,z5,z478,z6]),(0,[z479,z0,z1,z2,z4,z5,z6])],[(0,[z49,z0,z1,z14,z2,z4,z5])],[(0,[z65,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z21,z5,z26]),(0,[z0,z1,z2,z27,z4,z32,z5])],[(0,[z0,z1,z2,z315,z4,z5,z6]),(0,[z86,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z480,z6]),(0,[z0,z1,z481,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z482])],[(0,[z0,z342,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z20,z5,z6]),(0,[z483,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z24,z6]),(0,[z360,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z14,z2,z4,z5,z472])],[(0,[z0,z1,z25,z2,z4,z143,z6]),(0,[z0,z1,z171,z2,z4,z112,z5]),(0,[z484,z0,z1,z2,z4,z5,z6])],[],[(0,[z42,z0,z17,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z6,z485]),(0,[z0,z1,z2,z486,z4,z5,z6])],[(0,[z487,z0,z1,z2,z4,z5,z6]),(0,[z101,z0,z108,z2,z4,z5,z6]),(0,[z0,z1,z113,z2,z4,z5,z6]),(0,[z0,z1,z2,z185,z4,z93,z6])],[(0,[z0,z1,z2,z23,z4,z5,z6])],[(0,[z0,z1,z2,z4,z488,z5,z6]),(0,[z0,z1,z2,z489,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z43,z6])],[(0,[z490,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z491,z24,z6]),(0,[z0,z1,z14,z2,z4,z5,z122])]],
   [[(0,[z0,z1,z2,z106,z112,z5,z6]),(0,[z125,z0,z195,z2,z4,z5,z6]),(0,[z0,z1,z492,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z493,z5,z6]),(0,[z0,z1,z2,z4,z5,z494,z6]),(0,[z182,z0,z1,z2,z4,z5,z18])],[(0,[z350,z0,z1,z157,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z6,z495]),(0,[z0,z496,z1,z2,z4,z5,z6]),(0,[z0,z1,z121,z2,z27,z5,z6]),(0,[z0,z1,z497,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z76,z6])],[(0,[z0,z17,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z18,z390])],[(0,[z0,z1,z498,z2,z4,z5,z6]),(1,[z0,z1,z2,z345,z5,z6]),(0,[z0,z1,z2,z4,z24,z44,z6])],[(0,[z0,z1,z2,z499,z4,z5,z6]),(0,[z500,z0,z1,z2,z4,z5,z6]),(0,[z0,z17,z1,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z5,z6,z501]),(0,[z0,z1,z419,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z32,z5,z26]),(0,[z0,z1,z2,z4,z502,z5,z6])],[(0,[z0,z1,z503,z2,z4,z5,z6]),(0,[z65,z0,z2,z102,z4,z5,z6])],[(0,[z64,z0,z1,z2,z4,z5,z6]),(0,[z55,z0,z1,z2,z4,z158,z6]),(0,[z0,z1,z2,z4,z32,z24,z6]),(0,[z0,z1,z2,z4,z341,z43,z6]),(0,[z383,z0,z1,z2,z4,z5,z6])],[],[(0,[z0,z1,z2,z27,z4,z51,z5]),(0,[z0,z1,z2,z4,z5,z26,z83])],[(1,[z49,z50,z2,z4,z5,z6]),(0,[z209,z0,z1,z2,z4,z24,z6]),(0,[z0,z1,z14,z2,z4,z71,z5]),(0,[z0,z1,z2,z4,z32,z5,z339]),(0,[z0,z1,z2,z4,z504,z5,z6])],[(0,[z0,z1,z1,z2,z4,z5,z6]),(0,[z0,z1,z505,z2,z4,z5,z6]),(0,[z39,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z70,z4,z5]),(0,[z0,z1,z2,z4,z43,z80,z6])],[(0,[z0,z1,z506,z2,z4,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z391])],[(0,[z86,z0,z50,z2,z4,z5,z6]),(0,[z507,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z44,z339]),(0,[z0,z1,z2,z508,z4,z5,z6]),(0,[z0,z1,z2,z4,z291,z5,z6]),(0,[z0,z1,z2,z4,z509,z5,z6])],[(0,[z0,z1,z2,z510,z4,z5,z6]),(0,[z0,z1,z25,z2,z4,z5,z286]),(0,[z0,z2,z4,z71,z5,z79,z6]),(0,[z0,z1,z2,z511,z4,z5,z6]),(0,[z0,z177,z1,z2,z4,z5,z6]),(0,[z0,z152,z1,z2,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z5,z26]),(0,[z0,z1,z61,z2,z27,z4,z5])],[(1,[z0,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z5,z18,z339]),(0,[z0,z1,z60,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z122,z18]),(0,[z0,z1,z512,z2,z4,z5,z6])],[(0,[z513,z0,z1,z2,z4,z5,z6]),(0,[z0,z514,z1,z2,z4,z5,z6])]],
   [[(0,[z209,z0,z1,z2,z284,z5,z6]),(0,[z0,z515,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z130]),(1,[z55,z0,z102,z4,z5,z6]),(0,[z0,z1,z171,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z47,z6]),(0,[z0,z1,z8,z2,z4,z5,z6])],[(0,[z0,z1,z157,z2,z4,z5,z6])],[(0,[z0,z455,z1,z157,z2,z4,z6]),(1,[z0,z1,z2,z320,z5,z6]),(0,[z0,z1,z2,z345,z4,z5,z6]),(0,[z0,z1,z61,z2,z4,z5,z339])],[(0,[z209,z1,z2,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z516])],[(0,[z517,z0,z1,z2,z4,z5,z6]),(0,[z518,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z519,z4,z5,z6]),(0,[z0,z1,z2,z27,z5,z6,z280])],[(0,[z520,z0,z1,z2,z4,z5,z6]),(0,[z0,z521,z1,z2,z4,z5,z6]),(0,[z0,z167,z1,z2,z4,z5,z6]),(0,[z312,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z62,z6,z83])],[(1,[z0,z1,z386,z4,z5,z6]),(0,[z0,z1,z2,z522,z4,z5,z6]),(0,[z0,z1,z2,z106,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z523]),(0,[z0,z524,z1,z2,z4,z5,z6])],[(0,[z0,z157,z2,z4,z5,z79,z6]),(0,[z0,z1,z525,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z526,z6]),(1,[z0,z1,z2,z4,z289,z5])],[(0,[z0,z1,z527,z2,z4,z5,z6]),(0,[z0,z1,z528,z2,z4,z5,z6])],[(0,[z0,z455,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z20,z5,z122,z6]),(0,[z0,z1,z135,z2,z4,z5,z446]),(0,[z399,z0,z1,z14,z2,z4,z5])],[(1,[z0,z1,z2,z4,z529,z6]),(1,[z0,z52,z2,z4,z5,z6])],[(0,[z0,z1,z2,z102,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z530,z6]),(0,[z0,z1,z2,z4,z5,z18,z416]),(0,[z0,z1,z2,z4,z5,z173,z26]),(0,[z0,z1,z2,z4,z5,z413,z93]),(0,[z0,z1,z2,z4,z5,z531,z6])],[(0,[z182,z0,z1,z2,z4,z5,z6]),(0,[z86,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z532,z6]),(0,[z101,z0,z1,z2,z4,z5,z18]),(0,[z0,z533,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z534]),(0,[z0,z1,z2,z4,z255,z5,z6]),(0,[z0,z1,z2,z535,z4,z5,z6])],[(0,[z0,z1,z110,z2,z4,z172,z6]),(0,[z0,z1,z536,z2,z4,z20,z6]),(0,[z0,z1,z8,z2,z4,z71,z6])],[(0,[z0,z1,z2,z537,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z126]),(0,[z0,z1,z538,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z25,z2,z4,z43,z6]),(0,[z0,z1,z2,z27,z4,z5,z83]),(0,[z0,z1,z539,z2,z4,z5,z6])],[(0,[z0,z1,z2,z9,z106,z5,z6]),(0,[z0,z1,z2,z4,z540,z5,z6]),(0,[z0,z541,z1,z2,z4,z5,z6]),(0,[z0,z377,z1,z2,z4,z43,z6]),(0,[z0,z1,z4,z5,z26,z6,z18]),(0,[z0,z1,z542,z2,z4,z5,z6])],[(0,[z0,z543,z1,z2,z4,z5,z6]),(0,[z0,z13,z1,z2,z4,z5,z18])],[(0,[z86,z0,z1,z2,z4,z5,z374]),(0,[z0,z1,z2,z4,z5,z6,z544]),(0,[z39,z0,z1,z2,z4,z62,z5]),(0,[z0,z1,z69,z14,z2,z4,z5]),(0,[z0,z1,z14,z14,z2,z4,z5])],[(0,[z545,z0,z1,z2,z4,z5,z6]),(0,[z458,z0,z1,z2,z4,z43,z6])],[(0,[z63,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z546,z4,z5,z6]),(0,[z0,z1,z2,z4,z32,z5,z40]),(0,[z0,z1,z294,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z62,z24,z6])],[(0,[z0,z1,z2,z4,z133,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z547]),(0,[z0,z1,z2,z4,z417,z5,z6])],[(0,[z0,z1,z2,z4,z5,z16,z339]),(0,[z0,z1,z2,z548,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z79,z6]),(0,[z0,z1,z85,z2,z4,z5,z6])],[(0,[z209,z0,z1,z2,z4,z434,z6]),(0,[z549,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z5,z16]),(0,[z0,z1,z2,z35,z4,z5,z6]),(0,[z0,z1,z2,z185,z4,z43,z6]),(0,[z0,z1,z2,z550,z4,z5,z6])],[],[(1,[z0,z1,z2,z5,z349,z18]),(0,[z0,z1,z2,z4,z5,z6,z551])],[(0,[z0,z50,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z130,z6]),(0,[z0,z1,z121,z2,z70,z5,z6]),(0,[z552,z0,z1,z2,z4,z5,z6])],[(0,[z55,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z306,z24,z6]),(0,[z0,z1,z2,z4,z5,z24,z18]),(0,[z0,z1,z2,z4,z474,z43,z6]),(0,[z0,z1,z2,z27,z230,z4,z5])],[(0,[z0,z1,z14,z2,z185,z4,z5]),(0,[z0,z1,z2,z4,z5,z553,z6])],[(0,[z0,z1,z2,z4,z71,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z87]),(0,[z0,z1,z191,z2,z4,z5,z6]),(0,[z101,z0,z1,z121,z4,z5,z6])]],
   [[(0,[z54,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z30,z6])],[(0,[z125,z0,z17,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z554,z6]),(0,[z0,z1,z121,z2,z4,z5,z26]),(0,[z0,z1,z121,z2,z27,z4,z5]),(0,[z0,z1,z2,z555,z4,z5,z6]),(0,[z0,z1,z221,z2,z27,z4,z5])],[(0,[z0,z1,z2,z4,z20,z24,z6]),(0,[z0,z1,z135,z2,z4,z5,z26]),(0,[z0,z1,z135,z2,z27,z4,z5]),(0,[z0,z556,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z557,z5])],[(0,[z1,z110,z2,z23,z4,z5,z6]),(0,[z0,z1,z2,z558,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z6,z16]),(0,[z0,z1,z559,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z560,z5,z6]),(0,[z0,z163,z1,z2,z4,z24,z6])],[(0,[z0,z1,z2,z4,z5,z126,z18]),(0,[z0,z1,z2,z4,z5,z6,z561]),(0,[z0,z1,z2,z112,z5,z122,z6]),(1,[z0,z1,z121,z2,z27,z5]),(0,[z0,z1,z2,z70,z4,z5,z18]),(1,[z0,z1,z2,z462,z4,z5])],[(1,[z0,z1,z2,z464,z4,z5]),(0,[z0,z1,z2,z4,z562,z5,z6]),(0,[z0,z1,z2,z9,z4,z5,z6]),(0,[z0,z1,z2,z227,z4,z5,z26]),(0,[z0,z1,z2,z227,z27,z4,z5])],[(0,[z0,z563,z1,z2,z4,z5,z6]),(0,[z0,z163,z1,z2,z4,z5,z339])],[(0,[z125,z0,z1,z2,z4,z5,z564]),(1,[z0,z1,z2,z367,z5,z6])],[(0,[z0,z1,z2,z464,z4,z5,z6]),(0,[z0,z1,z2,z565,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z83])],[(1,[z0,z1,z2,z117,z5,z6]),(0,[z0,z1,z2,z23,z4,z43,z6]),(0,[z0,z1,z2,z4,z566,z5,z6]),(0,[z567,z0,z1,z2,z4,z5,z6]),(1,[z0,z1,z14,z2,z4,z43]),(0,[z0,z1,z60,z2,z4,z291,z6]),(1,[z0,z1,z2,z4,z5,z26]),(1,[z0,z1,z2,z27,z4,z5])],[(0,[z0,z1,z2,z106,z4,z24,z6]),(0,[z0,z568,z1,z2,z4,z5,z6])],[(0,[z86,z49,z1,z2,z4,z5,z6]),(0,[z1,z2,z106,z4,z20,z5,z6]),(0,[z236,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z40,z6])],[],[(0,[z569,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z110,z2,z4,z5,z6]),(0,[z0,z1,z570,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z571,z6])],[(0,[z0,z46,z1,z2,z572,z5,z6]),(0,[z0,z46,z1,z2,z4,z5,z494]),(0,[z0,z573,z1,z2,z4,z5,z6])],[(0,[z0,z152,z1,z135,z4,z5,z6])]],
   [[],[(0,[z0,z1,z2,z4,z5,z574,z6])],[(0,[z0,z575,z1,z2,z4,z5,z6]),(0,[z64,z0,z1,z2,z4,z43,z6]),(0,[z125,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z186,z43,z6])],[(0,[z576,z0,z1,z2,z4,z5,z6]),(0,[z63,z0,z1,z2,z4,z43,z6]),(0,[z0,z17,z1,z2,z4,z5,z26]),(0,[z0,z17,z1,z2,z27,z4,z5]),(0,[z0,z1,z4,z43,z5,z24,z6])],[(0,[z125,z1,z2,z4,z5,z126,z6]),(0,[z0,z1,z14,z577,z2,z4,z5])],[(0,[z64,z1,z2,z4,z20,z5,z6]),(0,[z0,z1,z2,z4,z578,z5,z6]),(0,[z0,z1,z2,z4,z5,z579,z6])],[(0,[z39,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z121,z2,z4,z319,z6]),(0,[z0,z580,z1,z2,z4,z5,z6])],[(0,[z0,z157,z2,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z581]),(1,[z63,z1,z2,z106,z5,z6]),(0,[z0,z1,z2,z254,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z44])],[(0,[z0,z1,z2,z4,z5,z6,z323]),(0,[z0,z1,z2,z4,z24,z6,z280])],[(0,[z582,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z9,z5,z122,z6]),(0,[z0,z583,z1,z2,z4,z5,z6])],[(0,[z584,z0,z1,z2,z4,z5,z6]),(0,[z209,z0,z1,z2,z4,z5,z26]),(0,[z1,z2,z4,z5,z44,z6,z16]),(0,[z0,z1,z2,z4,z5,z79,z6]),(0,[z101,z246,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z178,z5]),(0,[z0,z1,z2,z4,z585,z5,z6])],[(0,[z78,z0,z1,z2,z4,z24,z6]),(0,[z586,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z551,z18]),(0,[z0,z1,z8,z2,z185,z5,z6])],[(0,[z0,z1,z2,z4,z587,z5,z6]),(0,[z588,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z24,z6]),(1,[z15,z1,z2,z4,z5,z44]),(0,[z55,z0,z1,z2,z272,z5,z6]),(0,[z101,z0,z1,z2,z5,z122,z6]),(0,[z0,z1,z8,z2,z4,z43,z6])],[(0,[z0,z1,z157,z2,z4,z43,z6]),(0,[z0,z1,z589,z2,z4,z5,z6]),(0,[z0,z1,z2,z258,z27,z4,z5]),(0,[z0,z1,z61,z2,z4,z5,z83])],[(0,[z590,z0,z1,z2,z4,z5,z6]),(0,[z63,z1,z2,z106,z4,z5,z6]),(0,[z0,z1,z2,z4,z51,z79,z6]),(1,[z65,z0,z2,z9,z5,z6]),(1,[z0,z1,z2,z4,z319,z6]),(0,[z0,z591,z1,z2,z4,z5,z6])],[(0,[z42,z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z6,z66]),(0,[z0,z46,z1,z2,z4,z5,z18]),(1,[z101,z0,z1,z21,z5,z6]),(1,[z0,z1,z2,z4,z224,z5])]],
   [[(0,[z0,z222,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z70,z4,z5,z6])],[],[(0,[z0,z1,z592,z2,z4,z5,z6]),(0,[z0,z163,z1,z2,z4,z5,z40]),(0,[z0,z1,z2,z4,z593,z5,z18]),(0,[z0,z1,z2,z4,z5,z413,z6])],[(0,[z594,z0,z1,z2,z4,z5,z6]),(0,[z0,z25,z2,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z595,z5,z6])],[(0,[z49,z0,z1,z2,z4,z24,z6]),(1,[z0,z195,z2,z4,z5,z6])],[(0,[z42,z0,z46,z1,z2,z4,z6]),(0,[z65,z0,z1,z2,z4,z24,z6]),(0,[z0,z46,z1,z2,z493,z5,z6])],[(1,[z0,z1,z2,z4,z36,z6])],[],[(0,[z0,z1,z2,z4,z5,z374,z6]),(0,[z0,z1,z2,z4,z5,z596,z6]),(0,[z0,z1,z2,z4,z597,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z24]),(0,[z271,z0,z1,z2,z27,z4,z5])],[(0,[z0,z598,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z599,z6]),(0,[z0,z1,z14,z2,z4,z5,z280])],[(1,[z0,z1,z110,z4,z24,z6])],[(1,[z0,z1,z2,z4,z140,z6]),(1,[z0,z1,z2,z260,z5,z6]),(0,[z0,z96,z1,z2,z4,z5,z18]),(0,[z0,z600,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z601,z5,z6]),(0,[z0,z1,z2,z4,z166,z71,z5])],[(0,[z0,z1,z2,z4,z602,z5,z6]),(0,[z55,z197,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z75,z6])],[(0,[z49,z1,z2,z23,z4,z5,z6]),(1,[z0,z1,z2,z332,z5,z6]),(0,[z0,z1,z2,z603,z4,z5,z6]),(1,[z0,z1,z2,z4,z99,z6])],[(0,[z0,z2,z4,z5,z40,z6,z339]),(0,[z101,z0,z177,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z497,z2,z4,z5,z6]),(0,[z0,z1,z245,z2,z4,z5,z26])],[(0,[z0,z1,z135,z23,z4,z5,z6]),(0,[z15,z0,z1,z2,z4,z5,z18]),(0,[z282,z0,z1,z2,z4,z5,z26]),(0,[z283,z0,z1,z2,z27,z4,z5])],[(0,[z0,z1,z2,z4,z43,z44,z6]),(0,[z0,z1,z2,z4,z5,z6,z604]),(0,[z0,z1,z2,z4,z605,z5,z6]),(0,[z0,z496,z1,z14,z2,z4,z5])],[(0,[z0,z1,z606,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z93,z6])],[(0,[z0,z1,z14,z25,z2,z4,z5])],[(0,[z0,z222,z2,z4,z112,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z93])],[(0,[z0,z1,z2,z4,z289,z5,z6]),(0,[z0,z1,z2,z4,z62,z5,z26]),(0,[z0,z1,z503,z14,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z434,z6]),(0,[z64,z0,z1,z14,z2,z4,z5]),(0,[z65,z0,z1,z2,z9,z5,z6]),(0,[z0,z1,z14,z406,z2,z4,z5])],[(0,[z64,z0,z1,z110,z4,z5,z6]),(0,[z55,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z26,z18])],[(0,[z125,z42,z1,z2,z4,z5,z6]),(0,[z0,z152,z1,z2,z4,z5,z190]),(0,[z0,z1,z2,z185,z4,z24,z6]),(0,[z0,z1,z60,z2,z4,z355,z6]),(0,[z0,z1,z2,z4,z5,z300,z26])],[(0,[z607,z0,z1,z2,z4,z5,z6]),(0,[z0,z608,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z71,z43,z6]),(0,[z0,z1,z2,z4,z5,z609,z6]),(0,[z0,z610,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z186,z5,z277])],[(0,[z125,z0,z1,z124,z4,z5,z6]),(0,[z0,z1,z2,z185,z4,z79,z6]),(0,[z0,z1,z2,z4,z71,z5,z226]),(0,[z39,z0,z1,z14,z2,z4,z5])],[],[(0,[z0,z1,z14,z2,z4,z5,z79]),(0,[z0,z1,z2,z555,z4,z43,z6]),(0,[z0,z1,z2,z4,z306,z5,z26]),(0,[z0,z1,z2,z4,z5,z122,z6]),(0,[z0,z611,z1,z2,z4,z5,z6])],[(0,[z209,z0,z52,z2,z4,z5,z6]),(0,[z125,z0,z1,z2,z133,z5,z6]),(0,[z0,z1,z103,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z443,z6]),(0,[z0,z1,z2,z2,z4,z5,z18])],[(0,[z0,z612,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z87]),(0,[z0,z1,z2,z4,z5,z613,z6]),(0,[z0,z1,z2,z4,z5,z614,z6])],[(0,[z0,z1,z2,z4,z615,z5,z6]),(0,[z0,z1,z110,z2,z4,z305,z6]),(0,[z0,z1,z2,z9,z4,z43,z6]),(0,[z0,z1,z616,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z18,z534]),(0,[z0,z1,z8,z14,z2,z4,z5])],[(0,[z0,z1,z157,z14,z2,z4,z5]),(0,[z209,z64,z1,z2,z4,z5,z6]),(0,[z125,z0,z1,z2,z116,z5,z6]),(0,[z617,z0,z1,z2,z4,z5,z6]),(0,[z0,z163,z1,z2,z367,z5,z6]),(0,[z101,z313,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z20,z5,z26]),(1,[z0,z1,z2,z162,z4,z6])],[(0,[z0,z1,z2,z4,z24,z6,z339]),(0,[z0,z163,z1,z2,z4,z5,z26]),(0,[z0,z163,z1,z2,z27,z4,z5])],[(0,[z0,z1,z2,z106,z70,z5,z6]),(1,[z0,z1,z2,z4,z43,z26]),(0,[z0,z1,z2,z4,z618,z5,z6])],[(0,[z0,z1,z619,z2,z4,z5,z6]),(0,[z0,z1,z2,z620,z4,z5,z6]),(0,[z322,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z621,z6]),(0,[z0,z1,z14,z2,z4,z21,z5])],[],[(0,[z209,z0,z1,z23,z4,z5,z6]),(0,[z0,z1,z110,z2,z4,z43,z6]),(0,[z0,z1,z121,z2,z4,z5,z476])],[(0,[z622,z0,z1,z2,z4,z5,z6]),(0,[z0,z623,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z102,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z43,z5]),(0,[z0,z1,z2,z27,z4,z624,z5])],[(0,[z86,z0,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z106,z4,z5,z26]),(0,[z0,z1,z2,z4,z625,z5,z6]),(0,[z101,z0,z1,z2,z4,z5,z6]),(0,[z0,z13,z1,z4,z5,z26,z6])],[(0,[z55,z0,z1,z2,z4,z5,z251]),(0,[z0,z1,z2,z4,z5,z626,z6]),(0,[z0,z1,z2,z4,z5,z6,z359]),(0,[z0,z1,z2,z4,z62,z32,z5])],[(0,[z182,z0,z1,z14,z2,z4,z5])],[],[(0,[z0,z1,z2,z4,z5,z627,z6])]],
   [[(0,[z628,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z5,z6]),(0,[z0,z1,z2,z4,z112,z5,z18]),(0,[z0,z1,z2,z27,z4,z5,z18])],[(0,[z125,z0,z1,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z629,z5,z6]),(0,[z0,z1,z88,z2,z4,z5,z6]),(0,[z0,z630,z1,z2,z4,z5,z6]),(1,[z0,z1,z2,z4,z5,z476]),(0,[z0,z13,z1,z2,z4,z5,z6]),(0,[z0,z1,z14,z61,z2,z4,z5])],[(0,[z0,z1,z2,z4,z5,z6,z631]),(0,[z0,z1,z14,z2,z4,z24,z6])],[(0,[z0,z1,z2,z4,z186,z24,z6]),(0,[z0,z1,z2,z4,z557,z186,z5])],[(0,[z63,z0,z1,z2,z4,z24,z6])],[(0,[z0,z1,z2,z632,z4,z5,z6]),(1,[z0,z1,z2,z572,z5,z6]),(1,[z0,z1,z2,z4,z5,z494]),(0,[z633,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z5,z339]),(0,[z0,z1,z2,z4,z43,z5,z18]),(0,[z0,z1,z634,z2,z4,z5,z6])],[(0,[z64,z49,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z635,z4,z5,z6])],[(0,[z0,z2,z9,z4,z112,z5,z6]),(0,[z0,z1,z14,z2,z4,z114,z5]),(0,[z0,z1,z2,z4,z32,z5,z83])],[(1,[z0,z1,z2,z4,z5,z581]),(0,[z0,z1,z2,z27,z106,z5,z6]),(0,[z636,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z121,z2,z4,z193,z6]),(0,[z0,z1,z2,z4,z341,z5,z26])],[(0,[z0,z1,z2,z4,z637,z5,z6]),(1,[z0,z1,z2,z4,z5,z323]),(1,[z0,z1,z2,z5,z349,z6])],[(0,[z0,z50,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z44,z83]),(1,[z0,z1,z2,z227,z4,z5]),(0,[z0,z591,z1,z2,z4,z43,z6])],[(0,[z125,z0,z46,z1,z2,z4,z6]),(0,[z0,z638,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z24,z6])],[(0,[z78,z0,z1,z2,z4,z5,z26]),(0,[z78,z0,z1,z2,z27,z4,z5]),(0,[z0,z152,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z18,z83])],[(0,[z209,z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z162,z4,z20,z6]),(0,[z0,z1,z2,z4,z5,z6,z564]),(0,[z0,z1,z2,z4,z51,z5,z26]),(0,[z55,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z60,z2,z4,z43,z6])],[(0,[z0,z1,z157,z2,z4,z24,z6]),(0,[z63,z1,z2,z23,z4,z5,z6]),(0,[z0,z1,z110,z2,z4,z5,z252]),(0,[z0,z1,z2,z4,z5,z639,z6]),(0,[z42,z0,z1,z2,z4,z62,z6])],[(0,[z0,z640,z1,z2,z4,z5,z6]),(0,[z54,z0,z1,z2,z4,z5,z6])]],
   [[(1,[z0,z1,z2,z4,z5,z66]),(1,[z0,z1,z2,z4,z193,z6])],[(0,[z0,z641,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z20,z5]),(0,[z642,z0,z1,z2,z4,z5,z6]),(0,[z0,z222,z1,z2,z4,z5,z26]),(0,[z0,z222,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z624,z5,z6])],[(0,[z0,z13,z1,z2,z4,z255,z6])],[(1,[z0,z1,z2,z4,z5,z188]),(0,[z0,z1,z2,z4,z5,z126,z6]),(0,[z0,z1,z643,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z27,z5,z6]),(0,[z644,z0,z1,z2,z4,z5,z6])],[(1,[z0,z1,z536,z2,z4,z6]),(0,[z0,z1,z645,z2,z4,z5,z6]),(0,[z55,z366,z1,z2,z4,z5,z6]),(0,[z0,z437,z1,z2,z4,z24,z6]),(0,[z266,z0,z1,z2,z4,z5,z6]),(0,[z0,z13,z1,z60,z4,z5,z6])],[(0,[z49,z0,z1,z2,z4,z5,z26]),(0,[z49,z0,z1,z2,z27,z4,z5]),(0,[z0,z646,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z93,z6]),(0,[z0,z265,z1,z2,z27,z4,z5])],[(0,[z55,z0,z1,z2,z4,z358,z6]),(0,[z0,z1,z8,z2,z112,z5,z6]),(0,[z65,z0,z1,z2,z4,z5,z26]),(0,[z65,z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z647,z5,z6])],[(0,[z0,z1,z2,z124,z4,z5,z6]),(1,[z0,z46,z2,z4,z71,z6]),(0,[z0,z1,z2,z4,z648,z5,z6])],[(0,[z0,z1,z2,z4,z649,z5,z6]),(0,[z0,z1,z2,z4,z626,z24,z6]),(0,[z0,z1,z2,z4,z5,z6,z18]),(0,[z0,z1,z2,z4,z650,z5,z6]),(0,[z0,z651,z1,z2,z4,z5,z6])],[(0,[z86,z0,z1,z386,z4,z5,z6]),(0,[z86,z1,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z572,z4,z5,z6])],[],[(0,[z652,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z145,z5,z6]),(0,[z0,z1,z653,z2,z4,z5,z6]),(0,[z0,z1,z70,z4,z21,z5,z6]),(0,[z182,z0,z1,z2,z4,z43,z6])],[(0,[z55,z0,z2,z102,z4,z5,z6]),(1,[z0,z1,z2,z493,z5,z6]),(0,[z0,z1,z2,z4,z5,z392,z6]),(0,[z0,z1,z2,z4,z5,z446,z6]),(0,[z0,z1,z497,z2,z4,z43,z6])],[(0,[z86,z0,z1,z2,z4,z529,z6]),(0,[z42,z0,z1,z2,z185,z4,z6])],[],[(0,[z0,z1,z2,z4,z5,z6,z654]),(0,[z0,z1,z2,z4,z557,z5,z6])]],
   [[(1,[z0,z1,z2,z27,z5,z280])],[(0,[z64,z1,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z188,z6]),(0,[z125,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z40,z16]),(0,[z0,z1,z2,z655,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z5,z40]),(0,[z0,z1,z2,z4,z43,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z656]),(0,[z0,z1,z2,z4,z79,z24,z6]),(0,[z0,z1,z2,z4,z5,z6,z19]),(0,[z0,z1,z2,z227,z70,z4,z5])],[(0,[z0,z1,z2,z657,z4,z5,z6]),(0,[z101,z0,z1,z4,z21,z5,z6]),(1,[z0,z1,z2,z4,z178,z5])],[(0,[z78,z0,z1,z2,z20,z5,z6]),(0,[z0,z1,z14,z2,z4,z5,z44]),(0,[z0,z1,z25,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z658,z5,z6])],[(0,[z0,z1,z536,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z16,z83])],[(0,[z0,z1,z2,z659,z4,z5,z6])],[(0,[z0,z1,z2,z660,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z6,z280]),(0,[z0,z1,z141,z2,z4,z5,z6])],[(0,[z0,z1,z661,z2,z4,z5,z6])],[(0,[z0,z296,z1,z2,z4,z5,z6])],[(0,[z54,z0,z163,z1,z2,z4,z5]),(0,[z0,z1,z2,z185,z4,z5,z26])],[(0,[z0,z1,z2,z4,z5,z410,z6]),(0,[z0,z1,z2,z27,z4,z5,z317])],[(0,[z0,z1,z2,z662,z4,z5,z6]),(0,[z65,z0,z222,z2,z4,z5,z6])],[(1,[z0,z1,z2,z315,z5,z6]),(1,[z0,z1,z2,z4,z5,z423])],[(0,[z42,z0,z1,z2,z4,z5,z6]),(0,[z0,z46,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z393,z4,z5,z6])],[(0,[z0,z1,z2,z4,z663,z5,z6]),(1,[z0,z1,z8,z2,z93,z6])]],
   [[(0,[z0,z1,z2,z664,z4,z5,z6]),(0,[z0,z665,z1,z2,z4,z5,z6]),(0,[z0,z46,z1,z2,z4,z5,z98]),(0,[z0,z1,z666,z2,z4,z5,z6])],[(0,[z0,z152,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z593,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z667])],[(0,[z209,z0,z1,z2,z332,z5,z6]),(0,[z0,z1,z668,z2,z4,z5,z6]),(0,[z0,z1,z669,z2,z4,z5,z6])],[(0,[z0,z1,z121,z70,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6,z92])],[(0,[z0,z1,z2,z4,z670,z5,z6]),(0,[z671,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z672,z4,z5,z6]),(0,[z673,z0,z1,z2,z4,z5,z6]),(0,[z0,z163,z1,z2,z4,z5,z83])],[(0,[z0,z46,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z674,z4,z5,z6])],[(0,[z0,z1,z2,z102,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z6,z98]),(0,[z0,z1,z2,z4,z5,z675,z6])],[(0,[z0,z1,z2,z4,z5,z213,z6]),(0,[z0,z1,z2,z4,z676,z5,z6]),(0,[z101,z0,z1,z2,z4,z43,z6])],[(0,[z0,z1,z677,z2,z4,z5,z6]),(1,[z101,z0,z1,z2,z27,z5]),(0,[z0,z1,z678,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z6,z16])],[(0,[z0,z96,z1,z2,z4,z5,z6]),(0,[z0,z1,z679,z2,z4,z5,z6]),(0,[z0,z680,z1,z2,z4,z5,z6])],[(0,[z328,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z391,z6])],[(0,[z86,z0,z1,z2,z4,z5,z26]),(0,[z86,z0,z1,z2,z27,z4,z5]),(0,[z681,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z112,z21,z5,z6]),(0,[z0,z46,z1,z2,z4,z71,z6]),(0,[z0,z600,z1,z14,z2,z4,z5])],[(0,[z0,z1,z2,z23,z4,z24,z6]),(0,[z0,z682,z1,z2,z4,z5,z6]),(0,[z0,z13,z1,z2,z4,z43,z6])],[(0,[z0,z683,z1,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z462,z4,z5]),(0,[z684,z0,z1,z2,z4,z5,z6])],[]],
   [[(0,[z0,z1,z2,z4,z5,z6,z120]),(0,[z15,z0,z1,z2,z4,z5,z6]),(0,[z0,z685,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z686]),(0,[z0,z1,z2,z4,z5,z491,z6])],[(0,[z0,z1,z2,z185,z20,z5,z6])],[(1,[z64,z1,z110,z4,z5,z6]),(0,[z0,z1,z110,z2,z4,z5,z410]),(0,[z0,z1,z14,z2,z4,z5,z26]),(0,[z0,z1,z2,z27,z4,z186,z5]),(0,[z0,z1,z14,z2,z27,z4,z5])],[(0,[z64,z0,z1,z2,z4,z5,z26]),(0,[z0,z1,z14,z2,z9,z4,z5]),(0,[z0,z1,z2,z4,z186,z5,z26])],[(0,[z63,z0,z1,z2,z4,z5,z26]),(0,[z63,z0,z1,z2,z27,z4,z5])],[(0,[z0,z50,z1,z2,z4,z43,z6]),(0,[z64,z0,z1,z2,z4,z24,z6]),(1,[z0,z1,z2,z116,z5,z6]),(0,[z687,z0,z1,z2,z4,z5,z6])],[(0,[z1,z157,z2,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z26,z6]),(0,[z0,z1,z329,z2,z4,z5,z6])],[(0,[z0,z1,z2,z27,z4,z112,z5])],[],[(0,[z688,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z25,z2,z4,z443,z6]),(0,[z39,z0,z1,z2,z4,z24,z6])],[(0,[z54,z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z689,z6]),(0,[z0,z1,z2,z690,z4,z5,z6])],[(0,[z0,z1,z2,z691,z4,z5,z6])],[(0,[z0,z1,z2,z2,z4,z5,z6]),(0,[z0,z1,z2,z22,z4,z112,z5]),(0,[z39,z0,z1,z2,z4,z5,z339]),(0,[z0,z152,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z692,z6]),(0,[z0,z1,z577,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z529,z5,z6]),(1,[z0,z1,z2,z4,z5,z564]),(0,[z0,z1,z60,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z149,z6])],[(0,[z0,z1,z157,z2,z4,z5,z26]),(0,[z125,z0,z1,z191,z4,z5,z6]),(0,[z693,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z70,z4,z43,z6])]],
   [[(0,[z0,z1,z2,z4,z694,z5,z6]),(0,[z0,z1,z8,z2,z4,z24,z6])],[(0,[z0,z1,z2,z695,z4,z5,z6]),(0,[z0,z1,z2,z9,z21,z5,z6]),(0,[z0,z1,z121,z2,z4,z5,z18])],[(0,[z696,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z4,z79,z6]),(0,[z0,z1,z135,z2,z4,z5,z18])],[(0,[z125,z0,z1,z2,z185,z4,z6]),(0,[z0,z1,z2,z4,z43,z6,z339]),(1,[z0,z1,z4,z5,z26,z18])],[(0,[z0,z1,z14,z135,z2,z4,z5])],[(0,[z0,z1,z2,z697,z4,z5,z6]),(0,[z698,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z396,z6])],[(0,[z699,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z111,z6,z16]),(0,[z15,z1,z2,z4,z5,z44,z6]),(0,[z0,z1,z2,z70,z112,z5,z6])],[(0,[z0,z1,z2,z4,z700,z5,z6]),(0,[z0,z1,z2,z4,z143,z5,z6]),(0,[z0,z1,z2,z4,z24,z6,z534])],[(0,[z0,z1,z2,z701,z4,z5,z6])],[(0,[z442,z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z21,z5,z18]),(1,[z0,z1,z14,z2,z4,z24]),(1,[z0,z1,z2,z27,z4,z43]),(1,[z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z27,z4,z5,z122]),(0,[z0,z1,z14,z2,z4,z32,z5])],[(0,[z0,z1,z2,z702,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z703,z6])],[(0,[z0,z1,z704,z2,z4,z5,z6]),(0,[z15,z0,z163,z1,z2,z4,z5])],[(0,[z209,z0,z1,z2,z4,z5,z581]),(0,[z101,z0,z1,z14,z2,z4,z5]),(0,[z0,z1,z14,z121,z2,z4,z5]),(0,[z0,z533,z1,z2,z4,z24,z6]),(0,[z182,z0,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z6,z180]),(0,[z0,z1,z2,z4,z5,z93,z26])],[(0,[z63,z0,z1,z2,z20,z5,z6]),(0,[z125,z0,z1,z2,z4,z43,z6]),(0,[z705,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z119,z4,z5,z18]),(0,[z706,z0,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z112,z5,z6]),(0,[z0,z1,z2,z27,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z707,z0,z1,z4,z5,z6]),(0,[z0,z1,z2,z4,z140,z18]),(0,[z0,z1,z2,z708,z272,z5]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z0,z1,z2,z4,z710,z6]),(0,[z0,z1,z431,z4,z24,z6]),(0,[z0,z1,z2,z27,z142,z5]),(0,[z0,z1,z2,z711,z119,z5]),(0,[z322,z1,z2,z4,z5,z109]),(0,[z0,z1,z2,z4,z32,z76])],[(0,[z0,z296,z2,z4,z5,z6]),(0,[z0,z1,z2,z27,z674,z5]),(0,[z0,z108,z2,z4,z5,z26]),(0,[z0,z108,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z5,z712])],[(0,[z0,z52,z2,z4,z5,z18]),(0,[z64,z1,z677,z4,z5,z6]),(0,[z0,z1,z2,z27,z20,z5]),(0,[z0,z1,z8,z2,z27,z93])],[(0,[z0,z1,z2,z4,z713,z6]),(0,[z0,z1,z2,z714,z5,z6]),(0,[z0,z1,z2,z20,z178,z5]),(0,[z0,z1,z536,z14,z2,z4]),(0,[z0,z463,z2,z112,z5,z6])],[(0,[z0,z1,z2,z4,z305,z252]),(0,[z0,z1,z2,z4,z715,z6]),(0,[z0,z1,z2,z4,z716,z6]),(0,[z0,z1,z25,z2,z717,z5])],[(0,[z366,z1,z14,z2,z4,z5]),(0,[z0,z1,z2,z718,z5,z6]),(0,[z0,z1,z2,z5,z719,z280])],[(0,[z15,z0,z1,z2,z216,z5]),(0,[z0,z1,z2,z720,z4,z5]),(0,[z0,z1,z406,z2,z27,z5])],[(0,[z0,z1,z2,z721,z117,z5]),(0,[z0,z1,z722,z2,z4,z6]),(0,[z0,z1,z124,z4,z5,z26]),(0,[z0,z1,z2,z4,z111,z339])],[(0,[z0,z1,z2,z4,z5,z723]),(0,[z0,z1,z2,z4,z5,z724]),(0,[z0,z1,z725,z2,z4,z6]),(0,[z0,z1,z2,z726,z4,z5]),(0,[z449,z1,z2,z20,z5,z6]),(0,[z0,z1,z2,z4,z24,z120]),(0,[z0,z1,z2,z727,z5,z6]),(1,[z0,z2,z4,z728,z6]),(0,[z0,z1,z2,z4,z128,z26])],[(0,[z0,z1,z2,z4,z729,z5]),(0,[z0,z342,z2,z4,z5,z268]),(0,[z39,z0,z2,z4,z43,z339]),(0,[z0,z1,z2,z4,z5,z730]),(0,[z0,z1,z2,z119,z731,z5])],[(0,[z1,z157,z23,z4,z24,z6]),(0,[z0,z1,z2,z4,z732,z6]),(0,[z0,z1,z2,z733,z5,z6]),(0,[z63,z1,z2,z674,z5,z6]),(0,[z0,z1,z2,z734,z4,z5]),(0,[z0,z1,z2,z4,z735,z5]),(0,[z0,z1,z2,z4,z736,z6]),(0,[z0,z1,z2,z133,z5,z26]),(0,[z0,z1,z2,z4,z165,z83])],[(0,[z101,z0,z1,z21,z5,z423])],[(0,[z0,z1,z2,z5,z737,z6]),(0,[z0,z1,z2,z4,z43,z252]),(0,[z0,z1,z2,z4,z728,z6]),(0,[z0,z1,z2,z4,z738,z6])],[(0,[z0,z342,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z739,z6]),(0,[z125,z1,z2,z4,z289,z126]),(0,[z0,z1,z2,z4,z99,z19]),(0,[z740,z0,z14,z2,z4,z5])],[(0,[z0,z1,z2,z116,z5,z26]),(0,[z366,z1,z2,z4,z358,z6]),(0,[z0,z1,z2,z112,z57,z6]),(0,[z0,z1,z2,z119,z5,z79]),(0,[z0,z2,z4,z5,z6,z741]),(0,[z246,z1,z2,z4,z24,z6]),(0,[z0,z152,z1,z4,z742,z6]),(0,[z0,z13,z1,z2,z119,z5]),(0,[z0,z1,z14,z2,z5,z531])],[(0,[z0,z1,z2,z4,z743,z6]),(0,[z0,z1,z2,z4,z744,z24]),(0,[z0,z1,z2,z4,z745,z6])]],
   [[(0,[z549,z0,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z5,z746]),(0,[z0,z1,z2,z4,z145,z26]),(0,[z0,z1,z2,z4,z5,z719])],[(0,[z0,z1,z124,z4,z126,z6]),(0,[z0,z1,z2,z227,z4,z24])],[(0,[z0,z1,z2,z315,z36,z6]),(0,[z0,z1,z747,z2,z4,z6]),(0,[z0,z342,z2,z284,z5,z6]),(0,[z54,z0,z1,z2,z216,z5]),(0,[z0,z1,z2,z216,z5,z40])],[(0,[z0,z1,z2,z4,z5,z748]),(0,[z0,z1,z657,z4,z5,z26]),(0,[z412,z1,z2,z4,z5,z16]),(0,[z383,z1,z2,z4,z5,z16]),(0,[z0,z1,z2,z4,z749,z6]),(0,[z0,z750,z2,z4,z5,z6])],[(0,[z49,z751,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z752]),(0,[z0,z753,z1,z2,z4,z5]),(0,[z1,z2,z4,z754,z126,z6]),(0,[z0,z1,z2,z4,z5,z130]),(0,[z55,z0,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z755])],[(0,[z0,z1,z2,z4,z5,z756]),(0,[z0,z1,z307,z2,z27,z5]),(0,[z0,z222,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z757,z6]),(0,[z0,z1,z2,z4,z145,z339]),(0,[z101,z0,z1,z2,z178,z5])],[(0,[z0,z1,z124,z4,z5,z758])],[(0,[z0,z1,z14,z2,z4,z759])],[(0,[z0,z1,z2,z4,z760,z6]),(0,[z42,z1,z2,z4,z392,z6]),(0,[z0,z1,z2,z761,z5,z6]),(0,[z0,z1,z2,z4,z5,z762]),(0,[z0,z1,z2,z119,z21,z5]),(0,[z0,z1,z2,z27,z5,z127])],[(0,[z0,z1,z2,z4,z763,z6]),(0,[z0,z1,z764,z2,z4,z6]),(0,[z0,z514,z2,z4,z71,z6]),(0,[z0,z1,z2,z572,z5,z494]),(0,[z0,z1,z2,z4,z75,z423])],[(0,[z0,z1,z386,z4,z5,z6]),(0,[z86,z157,z14,z2,z4,z5]),(0,[z0,z1,z14,z2,z4,z140]),(0,[z0,z1,z2,z4,z765,z6]),(0,[z0,z1,z2,z4,z99,z423]),(0,[z0,z1,z2,z4,z5,z766]),(0,[z0,z1,z2,z119,z5,z390])],[(0,[z0,z1,z2,z4,z434,z6]),(0,[z0,z1,z2,z4,z289,z5]),(0,[z0,z1,z380,z4,z5,z18]),(0,[z101,z0,z177,z21,z5,z6]),(0,[z0,z1,z4,z24,z84,z6]),(0,[z0,z1,z2,z119,z43,z5])],[(0,[z0,z1,z2,z767,z4,z6]),(0,[z0,z1,z2,z272,z24,z6]),(0,[z0,z46,z2,z27,z4,z71]),(0,[z0,z1,z2,z4,z5,z768]),(0,[z0,z769,z2,z4,z5,z18])],[(0,[z0,z770,z2,z4,z5,z6]),(0,[z0,z1,z771,z2,z4,z6]),(0,[z0,z1,z2,z5,z772,z18])],[(0,[z0,z1,z2,z4,z529,z6]),(0,[z0,z1,z773,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z774]),(0,[z0,z222,z1,z2,z119,z5]),(0,[z775,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z776,z6]),(0,[z0,z1,z2,z777,z4,z5])],[(1,[z157,z386,z4,z5,z6]),(0,[z147,z50,z2,z4,z5,z6]),(0,[z590,z1,z2,z20,z5,z6]),(0,[z0,z1,z124,z4,z5,z155]),(0,[z0,z1,z2,z367,z5,z18]),(0,[z246,z1,z2,z27,z5,z6]),(0,[z0,z1,z2,z4,z43,z277]),(0,[z0,z1,z542,z4,z5,z18])]],
   [[(1,[z366,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z193,z476]),(0,[z0,z265,z2,z258,z4,z5])],[(0,[z0,z157,z386,z4,z5,z6]),(0,[z0,z1,z2,z117,z5,z18]),(0,[z86,z157,z2,z4,z5,z374]),(0,[z594,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z778]),(0,[z78,z1,z2,z20,z43,z6]),(0,[z0,z1,z2,z22,z4,z43]),(0,[z0,z1,z779,z2,z4,z5]),(0,[z0,z1,z4,z5,z425,z18]),(0,[z82,z0,z1,z2,z4,z317])],[(0,[z0,z1,z110,z27,z4,z24]),(0,[z0,z1,z2,z133,z5,z155]),(0,[z125,z1,z2,z4,z754,z6]),(0,[z0,z1,z645,z4,z5,z26]),(0,[z0,z366,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z443,z6]),(0,[z0,z1,z2,z780,z5,z6]),(1,[z101,z0,z1,z178,z5])],[(0,[z0,z1,z2,z4,z43,z374]),(0,[z0,z1,z2,z781,z5,z6]),(0,[z54,z1,z2,z4,z5,z16]),(0,[z0,z1,z2,z4,z111,z40]),(0,[z366,z1,z2,z4,z43,z6]),(0,[z782,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z783,z5,z6]),(0,[z0,z177,z2,z4,z24,z6]),(0,[z0,z1,z2,z119,z24,z6]),(0,[z0,z1,z2,z185,z186,z26])],[(0,[z64,z1,z14,z110,z4,z5]),(0,[z0,z1,z784,z2,z260,z5]),(0,[z0,z1,z2,z4,z785,z6]),(0,[z0,z1,z786,z2,z4,z5]),(0,[z101,z0,z108,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z446]),(0,[z0,z1,z2,z4,z24,z180]),(0,[z0,z1,z2,z119,z417,z5]),(0,[z0,z1,z14,z2,z4,z255]),(0,[z0,z1,z2,z5,z122,z719])],[(0,[z0,z1,z2,z4,z5,z787]),(0,[z1,z52,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z788,z5]),(0,[z1,z2,z4,z5,z789,z16]),(0,[z0,z1,z2,z4,z24,z286])],[(0,[z0,z1,z14,z2,z4,z172]),(0,[z0,z1,z191,z4,z5,z790]),(0,[z0,z1,z2,z119,z5,z339]),(0,[z0,z108,z2,z4,z99,z6]),(1,[z0,z1,z4,z742,z6])],[(0,[z0,z1,z48,z4,z5,z87]),(0,[z0,z1,z2,z4,z5,z791]),(0,[z156,z0,z1,z2,z119,z5])],[(0,[z0,z1,z2,z4,z792,z6]),(0,[z0,z1,z2,z4,z793,z5]),(0,[z0,z1,z2,z794,z5,z6])],[(0,[z0,z195,z2,z116,z5,z6]),(0,[z0,z1,z14,z2,z535,z5])],[(0,[z0,z1,z191,z4,z24,z6]),(0,[z0,z1,z2,z4,z178,z24]),(0,[z0,z795,z2,z4,z5,z18])],[(0,[z0,z1,z2,z185,z562,z6]),(0,[z0,z1,z2,z4,z796,z6]),(0,[z0,z46,z2,z572,z71,z6]),(0,[z0,z46,z2,z4,z71,z494]),(0,[z0,z1,z4,z5,z530,z18])],[(0,[z0,z1,z2,z315,z5,z87]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z0,z1,z798,z2,z4,z5]),(0,[z0,z1,z2,z27,z260,z5]),(0,[z0,z1,z2,z717,z4,z5]),(0,[z0,z799,z14,z2,z4,z5]),(0,[z0,z800,z14,z2,z4,z5])],[(0,[z0,z1,z23,z4,z24,z26]),(0,[z197,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z801,z43,z6])],[(0,[z0,z1,z2,z802,z4,z6]),(0,[z64,z0,z1,z2,z119,z5])],[(0,[z63,z1,z2,z106,z5,z18]),(0,[z125,z1,z2,z27,z4,z126]),(0,[z0,z1,z176,z4,z43,z6]),(0,[z0,z1,z2,z4,z803,z18])]],
   [[(0,[z0,z1,z2,z4,z804,z5]),(0,[z125,z0,z1,z2,z4,z289]),(0,[z42,z445,z1,z2,z4,z6]),(1,[z0,z1,z2,z717,z5]),(0,[z0,z2,z4,z71,z728,z6]),(0,[z0,z1,z2,z4,z5,z805]),(0,[z0,z1,z2,z27,z5,z47])],[(0,[z0,z1,z806,z4,z5,z6]),(0,[z0,z195,z2,z4,z5,z564]),(0,[z0,z1,z2,z4,z158,z130]),(0,[z55,z0,z102,z4,z158,z6]),(0,[z0,z1,z2,z4,z5,z807]),(0,[z808,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z391])],[(0,[z0,z342,z14,z2,z4,z5]),(0,[z125,z211,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z809,z6]),(0,[z420,z0,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z810]),(0,[z0,z1,z2,z811,z5,z6]),(0,[z0,z1,z409,z4,z43,z6])],[(0,[z0,z1,z386,z4,z5,z812]),(0,[z0,z1,z48,z117,z5,z6]),(0,[z0,z1,z307,z2,z4,z5]),(0,[z125,z1,z2,z4,z126,z26]),(0,[z125,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z119,z4,z43]),(0,[z0,z1,z2,z119,z5,z416])],[(0,[z0,z1,z2,z272,z5,z130]),(0,[z55,z0,z102,z272,z5,z6]),(0,[z0,z1,z2,z216,z5,z26]),(0,[z0,z1,z813,z2,z4,z5]),(0,[z0,z1,z2,z5,z814,z18]),(0,[z815,z0,z1,z2,z4,z5])],[(0,[z0,z1,z14,z2,z117,z5]),(0,[z816,z0,z1,z2,z4,z5]),(0,[z0,z1,z817,z2,z4,z5]),(0,[z0,z1,z2,z4,z24,z212]),(0,[z0,z1,z121,z27,z70,z5])],[(0,[z86,z157,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z43,z268]),(0,[z1,z110,z23,z4,z24,z6]),(0,[z65,z0,z2,z9,z5,z18]),(0,[z313,z1,z2,z4,z24,z6]),(0,[z101,z0,z1,z27,z178,z5]),(0,[z0,z1,z2,z4,z319,z18]),(0,[z0,z1,z497,z2,z119,z5]),(0,[z0,z1,z2,z4,z557,z5]),(0,[z236,z0,z2,z230,z4,z5])],[(0,[z0,z1,z818,z2,z5,z6]),(0,[z0,z1,z548,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z819]),(0,[z101,z0,z1,z21,z5,z18]),(0,[z0,z820,z2,z4,z5,z6])],[(0,[z0,z1,z821,z2,z4,z5]),(0,[z209,z1,z14,z23,z4,z5]),(0,[z0,z1,z2,z4,z5,z822]),(0,[z0,z1,z2,z227,z106,z5]),(0,[z0,z1,z2,z112,z5,z391]),(0,[z0,z1,z121,z2,z27,z5]),(0,[z0,z1,z2,z462,z4,z5]),(0,[z0,z1,z69,z2,z119,z5])],[(0,[z209,z1,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z305,z410]),(0,[z0,z1,z2,z823,z4,z5]),(0,[z0,z1,z2,z4,z824,z6]),(0,[z0,z1,z2,z4,z825,z6]),(0,[z0,z1,z8,z2,z287,z6]),(0,[z0,z2,z4,z728,z79,z6]),(0,[z0,z1,z2,z216,z5,z339]),(0,[z0,z1,z2,z4,z826,z6])],[(0,[z0,z1,z2,z4,z5,z827]),(0,[z0,z1,z2,z828,z4,z5]),(0,[z0,z1,z2,z4,z5,z829]),(0,[z0,z1,z2,z830,z5,z6]),(0,[z0,z1,z2,z4,z5,z831])],[(0,[z0,z1,z2,z832,z5,z6]),(0,[z0,z1,z2,z284,z5,z268]),(0,[z0,z1,z2,z4,z5,z790]),(0,[z0,z1,z2,z833,z5,z18]),(0,[z0,z1,z14,z2,z185,z186])],[(0,[z0,z1,z2,z4,z5,z834]),(0,[z0,z195,z2,z4,z5,z18]),(0,[z0,z1,z4,z151,z24,z6]),(0,[z0,z1,z462,z4,z5,z18])],[(0,[z0,z1,z2,z4,z5,z26]),(0,[z0,z1,z2,z27,z4,z5]),(0,[z0,z1,z835,z2,z4,z5]),(0,[z0,z296,z2,z4,z43,z6]),(0,[z0,z1,z14,z2,z311,z5]),(0,[z0,z1,z2,z4,z836,z6]),(0,[z0,z1,z14,z2,z4,z43]),(0,[z0,z1,z2,z4,z43,z712]),(0,[z0,z1,z2,z4,z837,z6])],[(0,[z0,z1,z2,z4,z36,z18]),(0,[z0,z222,z25,z4,z5,z286]),(0,[z0,z1,z2,z4,z5,z838]),(0,[z240,z0,z1,z2,z119,z5])],[(0,[z0,z1,z2,z284,z43,z6]),(1,[z1,z2,z839,z5,z6]),(0,[z0,z1,z840,z2,z4,z5]),(0,[z0,z1,z2,z106,z224,z5]),(0,[z0,z1,z2,z4,z5,z841]),(0,[z0,z1,z2,z27,z5,z29]),(0,[z0,z1,z2,z27,z4,z128]),(0,[z101,z0,z1,z2,z27,z24])]],
   [[(0,[z0,z1,z191,z4,z5,z155]),(0,[z0,z1,z2,z4,z5,z842]),(0,[z0,z1,z2,z4,z5,z843]),(0,[z0,z163,z329,z2,z4,z5]),(0,[z0,z1,z2,z27,z5,z349])],[(0,[z0,z1,z844,z2,z4,z5]),(0,[z209,z1,z23,z4,z239,z6]),(0,[z0,z1,z2,z4,z43,z410]),(0,[z0,z1,z2,z839,z5,z6]),(0,[z0,z1,z2,z4,z5,z845]),(0,[z0,z1,z2,z4,z57,z391]),(0,[z101,z313,z1,z2,z27,z5]),(0,[z0,z1,z60,z5,z349,z18]),(0,[z0,z1,z14,z2,z5,z719])],[(0,[z0,z1,z846,z4,z5,z6]),(0,[z0,z1,z110,z4,z24,z18]),(0,[z0,z1,z2,z4,z237,z26]),(0,[z0,z46,z2,z493,z71,z6]),(0,[z0,z1,z2,z119,z5,z40]),(0,[z0,z1,z245,z2,z227,z5])],[(0,[z0,z1,z2,z260,z5,z18]),(0,[z847,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z848,z5,z18])],[(0,[z0,z849,z1,z2,z4,z6]),(0,[z0,z1,z2,z27,z133,z5]),(0,[z125,z0,z1,z2,z572,z6]),(0,[z0,z1,z14,z2,z4,z57])],[(0,[z671,z0,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z239,z26]),(0,[z0,z1,z2,z4,z111,z26]),(0,[z0,z1,z2,z119,z5,z44]),(0,[z197,z1,z2,z4,z5,z130]),(0,[z0,z1,z2,z4,z75,z18])],[(0,[z0,z1,z2,z4,z850,z6]),(0,[z0,z1,z2,z4,z851,z6]),(0,[z0,z1,z2,z332,z5,z18]),(0,[z0,z1,z2,z4,z5,z852]),(0,[z0,z853,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z854]),(0,[z0,z1,z2,z4,z99,z18]),(0,[z0,z1,z2,z27,z5,z212]),(0,[z0,z1,z2,z4,z43,z413]),(0,[z0,z1,z2,z27,z4,z855])],[(0,[z0,z1,z2,z227,z112,z5]),(0,[z0,z1,z2,z27,z5,z80]),(0,[z0,z1,z8,z2,z309,z6])],[(0,[z1,z2,z4,z5,z6,z789]),(0,[z0,z1,z2,z4,z5,z856]),(0,[z0,z1,z2,z4,z857,z5]),(0,[z858,z0,z1,z2,z27,z4])],[(0,[z0,z1,z2,z4,z859,z6]),(0,[z0,z1,z860,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z861]),(0,[z0,z1,z2,z367,z128,z6]),(0,[z246,z1,z2,z70,z5,z6]),(0,[z0,z1,z2,z35,z149,z6])],[(0,[z0,z862,z2,z4,z5,z6]),(0,[z0,z1,z2,z863,z5,z6]),(0,[z0,z1,z2,z345,z5,z6]),(0,[z0,z1,z2,z27,z5,z225]),(0,[z0,z1,z124,z27,z4,z5]),(0,[z0,z1,z2,z27,z407,z5]),(0,[z39,z0,z2,z4,z24,z339]),(0,[z0,z1,z2,z864,z5,z26])],[(0,[z549,z1,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z865]),(0,[z125,z1,z2,z4,z126,z155]),(0,[z0,z1,z2,z4,z803,z6]),(0,[z0,z1,z2,z4,z443,z286])],[(0,[z866,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z758]),(0,[z0,z1,z2,z4,z24,z251]),(0,[z0,z1,z2,z4,z867,z6]),(0,[z0,z1,z4,z181,z24,z6])],[(0,[z0,z1,z2,z4,z24,z252]),(0,[z0,z1,z4,z5,z571,z18])],[(0,[z0,z1,z2,z4,z868,z6]),(0,[z0,z1,z187,z4,z24,z6]),(0,[z0,z342,z2,z4,z24,z6]),(0,[z125,z0,z1,z2,z4,z494]),(0,[z0,z1,z2,z4,z255,z26]),(0,[z0,z1,z2,z4,z869,z6])],[(0,[z0,z1,z2,z870,z4,z5]),(0,[z0,z1,z2,z4,z871,z6]),(0,[z518,z0,z2,z9,z5,z6]),(0,[z246,z1,z2,z4,z5,z26]),(0,[z246,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z75,z19]),(0,[z0,z1,z4,z43,z742,z6])]],
   [[(0,[z49,z50,z2,z4,z5,z6]),(0,[z0,z1,z48,z4,z36,z6]),(0,[z0,z1,z2,z5,z872,z323]),(0,[z0,z1,z2,z4,z145,z83]),(0,[z0,z163,z1,z2,z119,z5])],[(0,[z0,z1,z4,z5,z574,z18]),(0,[z0,z222,z25,z4,z43,z6]),(0,[z0,z1,z2,z367,z145,z6]),(0,[z0,z1,z14,z2,z4,z319])],[(0,[z0,z1,z2,z4,z873,z5]),(0,[z0,z1,z874,z4,z5,z6]),(0,[z0,z1,z2,z4,z143,z26]),(0,[z65,z0,z2,z9,z5,z6]),(0,[z0,z1,z2,z4,z319,z6])],[(0,[z0,z875,z2,z4,z5,z6]),(0,[z459,z1,z2,z20,z5,z6]),(0,[z0,z1,z2,z227,z20,z5]),(0,[z0,z1,z14,z2,z4,z158])],[(0,[z86,z157,z386,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z876]),(0,[z0,z455,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z5,z877]),(0,[z244,z1,z2,z106,z5,z6]),(0,[z0,z1,z878,z4,z5,z6])],[(0,[z0,z1,z2,z4,z879,z6]),(0,[z0,z1,z2,z880,z5,z6]),(0,[z0,z881,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z882,z6]),(0,[z0,z1,z4,z43,z692,z6])],[(0,[z0,z1,z386,z4,z43,z6]),(0,[z0,z1,z2,z27,z315,z5]),(0,[z0,z1,z2,z4,z5,z883]),(0,[z15,z1,z406,z2,z4,z5]),(0,[z0,z1,z884,z2,z4,z5])],[(0,[z63,z1,z2,z106,z5,z120]),(0,[z0,z1,z885,z4,z5,z6]),(0,[z366,z2,z102,z4,z5,z6]),(0,[z65,z0,z2,z9,z237,z6]),(0,[z0,z1,z2,z886,z4,z5]),(0,[z0,z1,z2,z4,z5,z887]),(0,[z0,z1,z2,z4,z32,z226]),(0,[z39,z0,z2,z230,z4,z5])],[(0,[z0,z1,z48,z4,z5,z888]),(0,[z86,z157,z2,z4,z529,z6]),(0,[z39,z0,z1,z2,z345,z5]),(0,[z0,z1,z503,z2,z345,z5]),(0,[z0,z46,z1,z2,z119,z5]),(0,[z0,z1,z2,z4,z24,z190])],[(0,[z0,z1,z14,z48,z4,z5]),(0,[z0,z1,z2,z889,z4,z5]),(0,[z1,z890,z23,z4,z5,z6]),(0,[z0,z1,z2,z320,z5,z6]),(0,[z0,z163,z1,z2,z345,z5]),(0,[z0,z1,z2,z4,z5,z891]),(0,[z0,z1,z38,z4,z5,z26])],[(0,[z0,z1,z892,z4,z5,z6]),(0,[z0,z1,z2,z4,z893,z6]),(0,[z0,z1,z430,z2,z27,z5]),(0,[z0,z1,z2,z4,z158,z26]),(0,[z0,z1,z2,z27,z4,z894])],[(0,[z0,z1,z14,z2,z4,z305]),(0,[z0,z1,z2,z162,z4,z18])],[(0,[z0,z1,z895,z2,z4,z5]),(0,[z0,z1,z2,z4,z896,z6]),(0,[z0,z1,z897,z2,z4,z5]),(0,[z0,z1,z2,z4,z898,z6]),(0,[z0,z1,z899,z4,z5,z6]),(0,[z0,z1,z141,z2,z4,z472])],[(0,[z0,z1,z2,z272,z5,z26])],[(0,[z0,z1,z110,z4,z24,z6]),(0,[z0,z1,z8,z2,z133,z6]),(0,[z900,z1,z2,z4,z5,z6]),(0,[z0,z1,z8,z2,z901,z6])],[(0,[z0,z1,z203,z2,z4,z43]),(0,[z0,z1,z2,z27,z20,z43]),(0,[z0,z1,z2,z4,z140,z6]),(0,[z54,z1,z2,z4,z43,z16]),(0,[z0,z1,z2,z260,z5,z6]),(0,[z0,z1,z2,z4,z902,z6]),(0,[z0,z1,z2,z4,z903,z6]),(0,[z0,z1,z2,z27,z4,z75])]],
   [[(0,[z479,z1,z2,z106,z5,z6]),(0,[z0,z1,z2,z4,z5,z904]),(0,[z0,z1,z2,z4,z24,z277]),(0,[z0,z1,z2,z4,z43,z446])],[(0,[z0,z52,z2,z4,z5,z6]),(0,[z0,z1,z2,z905,z5,z6]),(0,[z0,z1,z2,z4,z172,z26]),(0,[z0,z1,z2,z4,z5,z906]),(0,[z0,z1,z907,z2,z4,z5])],[(0,[z0,z222,z352,z4,z5,z6]),(0,[z0,z1,z2,z332,z5,z6]),(0,[z0,z1,z2,z27,z4,z239]),(0,[z0,z296,z14,z2,z4,z5]),(0,[z0,z1,z14,z2,z27,z43])],[(0,[z0,z1,z2,z4,z5,z908]),(0,[z0,z1,z2,z909,z4,z5])],[(0,[z0,z1,z2,z4,z24,z374]),(0,[z0,z910,z1,z2,z4,z6]),(0,[z366,z1,z2,z4,z24,z6]),(0,[z55,z0,z102,z4,z5,z251]),(0,[z0,z177,z2,z4,z5,z26]),(0,[z0,z177,z2,z27,z4,z5]),(0,[z0,z1,z2,z794,z43,z6]),(0,[z383,z1,z2,z4,z5,z390]),(0,[z0,z1,z2,z119,z5,z26])],[(0,[z0,z911,z2,z4,z5,z6]),(0,[z0,z195,z124,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z912]),(0,[z0,z1,z2,z27,z4,z30]),(0,[z858,z0,z1,z2,z4,z6])],[(0,[z0,z1,z2,z27,z284,z5]),(0,[z55,z197,z102,z4,z5,z6]),(0,[z0,z2,z102,z27,z112,z5]),(0,[z0,z1,z2,z4,z24,z913])],[(0,[z751,z157,z2,z4,z5,z6]),(0,[z0,z1,z157,z2,z119,z5]),(0,[z0,z1,z2,z4,z5,z914]),(0,[z0,z1,z2,z4,z915,z6]),(0,[z0,z163,z2,z4,z24,z40]),(0,[z0,z1,z2,z4,z916,z6]),(0,[z0,z1,z2,z4,z24,z917]),(0,[z0,z1,z2,z4,z918,z6])],[(0,[z64,z1,z110,z4,z5,z18]),(0,[z0,z195,z2,z133,z5,z6]),(0,[z919,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z920]),(0,[z0,z108,z2,z4,z75,z6]),(0,[z0,z1,z2,z4,z291,z26])],[(0,[z0,z1,z921,z2,z4,z5]),(0,[z0,z52,z2,z4,z239,z6]),(0,[z0,z1,z2,z4,z922,z6]),(0,[z0,z1,z923,z2,z4,z5]),(0,[z39,z0,z2,z4,z5,z741]),(0,[z0,z1,z2,z119,z593,z5]),(0,[z0,z1,z2,z924,z4,z5]),(0,[z0,z1,z2,z5,z901,z6])],[(0,[z517,z1,z23,z4,z5,z6]),(0,[z0,z1,z2,z332,z239,z6]),(0,[z0,z1,z14,z2,z4,z443]),(0,[z0,z1,z2,z4,z925,z6]),(0,[z0,z163,z2,z4,z5,z741]),(0,[z0,z1,z14,z2,z24,z122]),(0,[z0,z1,z135,z4,z742,z6]),(0,[z0,z1,z2,z4,z926,z26])],[(0,[z0,z50,z386,z4,z5,z6]),(0,[z1,z751,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z927]),(0,[z63,z0,z1,z2,z119,z5]),(0,[z0,z1,z191,z27,z4,z5]),(0,[z0,z1,z191,z4,z5,z26]),(0,[z0,z2,z4,z5,z741,z339])],[(0,[z0,z1,z2,z928,z5,z6]),(0,[z0,z1,z2,z4,z5,z929]),(0,[z0,z1,z2,z4,z930,z6]),(0,[z0,z1,z2,z4,z931,z6]),(0,[z0,z1,z2,z27,z4,z99]),(0,[z0,z1,z88,z2,z4,z24]),(0,[z0,z1,z2,z4,z43,z932])],[(0,[z0,z1,z933,z2,z4,z5]),(0,[z0,z342,z2,z4,z434,z6]),(0,[z0,z1,z124,z4,z474,z6]),(0,[z0,z1,z2,z345,z5,z16]),(0,[z0,z1,z2,z572,z5,z18]),(0,[z0,z1,z2,z4,z5,z934]),(0,[z0,z1,z70,z4,z178,z5])],[(0,[z0,z1,z2,z935,z5,z6]),(0,[z197,z1,z2,z4,z5,z26]),(0,[z197,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z936,z6]),(0,[z0,z1,z603,z4,z5,z18]),(0,[z0,z1,z2,z937,z4,z6]),(0,[z0,z1,z2,z811,z43,z6]),(0,[z0,z1,z2,z4,z341,z76]),(0,[z0,z1,z2,z4,z5,z938])],[(0,[z0,z1,z2,z27,z276,z5])]],
   [[(0,[z0,z939,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z940]),(0,[z0,z1,z941,z2,z116,z5])],[(0,[z0,z1,z2,z4,z305,z26]),(0,[z0,z1,z2,z4,z5,z942]),(0,[z0,z2,z620,z112,z5,z6]),(0,[z943,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z5,z349,z18]),(0,[z0,z1,z2,z4,z944,z6])],[(0,[z0,z1,z2,z889,z315,z5]),(0,[z0,z1,z4,z871,z24,z6]),(0,[z0,z1,z2,z4,z24,z391]),(0,[z0,z1,z2,z4,z5,z945])],[(0,[z0,z1,z704,z4,z24,z6]),(0,[z0,z1,z661,z4,z5,z18]),(0,[z0,z1,z2,z493,z5,z494]),(0,[z0,z1,z2,z4,z946,z5])],[(0,[z0,z1,z2,z4,z947,z6]),(0,[z0,z1,z2,z4,z948,z5]),(0,[z0,z1,z110,z2,z949,z5]),(0,[z0,z1,z950,z2,z4,z6]),(0,[z951,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z216,z5,z83]),(0,[z246,z1,z2,z4,z99,z6])],[(0,[z0,z1,z2,z952,z4,z6]),(0,[z209,z1,z23,z4,z43,z6]),(0,[z55,z0,z1,z2,z119,z5]),(0,[z65,z0,z2,z664,z5,z6]),(0,[z0,z1,z606,z2,z27,z5]),(0,[z0,z96,z2,z112,z24,z6]),(0,[z0,z1,z2,z4,z5,z953]),(0,[z0,z108,z2,z4,z5,z423]),(0,[z0,z1,z2,z4,z5,z954])],[(0,[z0,z1,z955,z2,z4,z5])],[(0,[z86,z157,z2,z4,z5,z26]),(0,[z350,z0,z1,z2,z4,z43]),(0,[z0,z1,z2,z4,z24,z268]),(0,[z313,z1,z2,z4,z5,z26]),(0,[z313,z1,z2,z27,z4,z5]),(0,[z0,z1,z294,z2,z93,z6]),(0,[z0,z1,z2,z4,z5,z956]),(0,[z0,z1,z2,z27,z4,z837])],[(0,[z0,z1,z2,z27,z4,z529]),(0,[z0,z1,z784,z2,z4,z5]),(0,[z0,z1,z2,z4,z957,z5]),(0,[z0,z1,z2,z4,z193,z18]),(0,[z0,z1,z2,z958,z5,z18])],[(0,[z0,z959,z1,z2,z4,z6]),(0,[z0,z1,z619,z4,z24,z6]),(0,[z0,z1,z2,z27,z272,z5]),(0,[z0,z1,z2,z112,z557,z5]),(0,[z0,z1,z2,z27,z372,z5]),(0,[z0,z1,z2,z4,z43,z26]),(0,[z0,z1,z85,z2,z4,z24]),(0,[z0,z1,z294,z2,z27,z5])],[(0,[z0,z1,z2,z5,z960,z6]),(0,[z0,z1,z2,z4,z5,z961]),(0,[z101,z0,z1,z178,z5,z6]),(0,[z0,z1,z2,z119,z32,z5]),(0,[z0,z1,z2,z4,z962,z26]),(0,[z0,z963,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z964,z5]),(0,[z0,z195,z2,z4,z62,z6]),(0,[z0,z1,z2,z4,z742,z6]),(0,[z0,z1,z2,z965,z5,z6]),(0,[z0,z1,z405,z4,z24,z6]),(0,[z0,z769,z2,z4,z5,z6])],[(0,[z0,z1,z2,z464,z4,z5]),(0,[z0,z1,z536,z2,z4,z18]),(0,[z366,z1,z2,z4,z5,z130]),(0,[z0,z1,z2,z260,z158,z6]),(0,[z0,z1,z2,z5,z772,z6]),(0,[z0,z1,z2,z4,z24,z226])],[(0,[z0,z1,z2,z4,z5,z966]),(0,[z0,z1,z110,z4,z434,z6]),(0,[z0,z1,z2,z4,z5,z967]),(0,[z0,z968,z2,z4,z5,z6]),(0,[z0,z1,z4,z151,z5,z26])],[(0,[z0,z1,z969,z4,z5,z6]),(0,[z0,z1,z970,z2,z4,z6]),(0,[z0,z1,z14,z110,z4,z24]),(0,[z42,z1,z2,z89,z4,z6]),(0,[z0,z1,z2,z4,z358,z130]),(0,[z55,z0,z102,z4,z358,z6]),(0,[z0,z1,z2,z367,z5,z6])],[(0,[z0,z46,z2,z4,z71,z18]),(0,[z0,z1,z69,z2,z4,z24]),(0,[z0,z1,z577,z4,z5,z18])]],
   [[(0,[z0,z1,z2,z117,z5,z6]),(0,[z0,z1,z2,z284,z24,z6]),(0,[z0,z1,z2,z971,z4,z5]),(0,[z0,z1,z2,z972,z4,z5])],[(0,[z973,z0,z1,z2,z4,z5]),(0,[z0,z1,z103,z2,z4,z24]),(0,[z0,z1,z2,z227,z5,z47]),(0,[z0,z1,z2,z4,z974,z6])],[(0,[z0,z1,z386,z4,z5,z374]),(0,[z0,z1,z2,z4,z24,z410]),(0,[z0,z1,z2,z4,z5,z975]),(0,[z0,z1,z2,z976,z4,z5]),(1,[z1,z2,z4,z5,z789]),(0,[z0,z1,z2,z4,z977,z6]),(0,[z0,z91,z2,z112,z5,z6]),(0,[z0,z1,z2,z27,z9,z24])],[(0,[z0,z1,z2,z106,z5,z188]),(0,[z0,z1,z2,z4,z978,z6]),(0,[z0,z437,z2,z4,z626,z6]),(0,[z0,z1,z2,z27,z43,z80]),(0,[z0,z1,z2,z4,z979,z5]),(0,[z980,z0,z1,z2,z119,z5])],[(0,[z0,z1,z110,z4,z443,z6]),(0,[z0,z1,z2,z4,z5,z789]),(0,[z0,z1,z2,z9,z5,z391]),(0,[z0,z1,z2,z493,z5,z18]),(0,[z101,z0,z177,z2,z27,z5]),(0,[z981,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z111,z83]),(0,[z0,z25,z982,z4,z5,z6]),(0,[z0,z1,z2,z27,z493,z5]),(0,[z0,z1,z4,z5,z165,z26])],[(0,[z0,z1,z2,z4,z529,z374]),(0,[z1,z2,z27,z106,z20,z5]),(0,[z0,z1,z536,z2,z185,z6]),(0,[z0,z983,z2,z4,z5,z6]),(0,[z0,z195,z191,z4,z5,z6]),(0,[z0,z1,z2,z345,z43,z6]),(0,[z984,z1,z2,z4,z5,z6]),(0,[z0,z591,z2,z4,z71,z6]),(0,[z0,z1,z2,z4,z24,z985]),(1,[z0,z1,z2,z119,z24]),(0,[z0,z1,z2,z4,z5,z986]),(0,[z0,z1,z2,z4,z62,z974])],[(0,[z0,z1,z2,z27,z106,z43]),(0,[z0,z1,z2,z972,z133,z5]),(0,[z0,z96,z2,z987,z5,z6]),(0,[z0,z1,z2,z4,z24,z413])],[(0,[z0,z1,z2,z4,z5,z988]),(0,[z0,z1,z2,z4,z5,z989]),(0,[z1,z2,z106,z839,z5,z6]),(0,[z0,z177,z2,z4,z75,z6]),(0,[z0,z1,z245,z2,z4,z24]),(0,[z0,z1,z2,z990,z24,z6])],[(0,[z0,z1,z2,z4,z991,z6]),(0,[z0,z177,z2,z4,z99,z6]),(0,[z0,z1,z2,z992,z4,z5]),(0,[z0,z795,z2,z4,z5,z6])],[(0,[z0,z1,z2,z993,z5,z6]),(0,[z0,z195,z2,z185,z4,z6]),(0,[z0,z1,z2,z4,z32,z263]),(0,[z0,z1,z2,z4,z5,z994]),(0,[z0,z1,z4,z742,z24,z6])],[(0,[z0,z1,z2,z4,z995,z6]),(0,[z0,z1,z2,z4,z5,z996]),(0,[z209,z342,z23,z4,z5,z6]),(0,[z1,z2,z839,z20,z5,z6]),(0,[z0,z1,z14,z2,z162,z4]),(0,[z0,z997,z2,z4,z5,z6]),(0,[z0,z1,z2,z998,z4,z5]),(0,[z0,z1,z2,z572,z5,z98]),(0,[z0,z1,z2,z4,z319,z212])],[(0,[z49,z50,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z5,z581]),(0,[z0,z1,z2,z4,z5,z999]),(0,[z0,z1,z2,z119,z51,z5]),(0,[z0,z1,z2,z4,z1000,z6]),(0,[z0,z1,z2,z119,z119,z5]),(0,[z0,z1,z4,z178,z5,z26])],[(0,[z0,z1,z2,z1001,z5,z6]),(0,[z0,z1,z2,z4,z289,z79]),(0,[z0,z265,z2,z27,z9,z5]),(0,[z101,z0,z108,z2,z27,z5]),(0,[z0,z1,z2,z5,z349,z6]),(0,[z1002,z1,z2,z27,z4,z5])],[(0,[z0,z1,z1003,z4,z5,z6]),(0,[z0,z1,z2,z1004,z4,z5]),(0,[z0,z1,z2,z4,z1005,z6]),(0,[z0,z1,z2,z4,z5,z1006]),(0,[z63,z1,z2,z106,z5,z6]),(0,[z0,z17,z195,z2,z4,z6]),(0,[z0,z1,z2,z4,z1007,z6]),(0,[z0,z1,z2,z4,z5,z1008]),(0,[z0,z1,z2,z1009,z4,z5]),(0,[z0,z1,z2,z4,z5,z1010])],[(0,[z0,z342,z2,z4,z5,z26]),(0,[z0,z342,z2,z27,z4,z5]),(0,[z0,z1011,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1012]),(0,[z0,z1,z2,z4,z5,z1013]),(0,[z0,z1,z2,z1014,z5,z6])]],
   [[(0,[z0,z1,z48,z4,z5,z18]),(0,[z444,z157,z2,z4,z5,z6]),(0,[z350,z0,z274,z1,z2,z4]),(0,[z0,z1,z1015,z2,z4,z6]),(0,[z458,z1,z2,z4,z51,z6]),(0,[z197,z1,z2,z260,z5,z6]),(0,[z0,z222,z492,z4,z5,z6]),(1,[z0,z2,z987,z5,z6]),(0,[z0,z1,z2,z4,z5,z1016]),(0,[z0,z1,z61,z2,z4,z306])],[(0,[z0,z1,z2,z1017,z4,z5]),(0,[z125,z195,z2,z4,z126,z6]),(0,[z0,z1,z14,z124,z4,z5]),(0,[z0,z1,z2,z4,z43,z155]),(0,[z1018,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1019])],[(0,[z0,z1,z2,z1020,z5,z6]),(0,[z0,z1,z2,z4,z1021,z6]),(0,[z63,z1,z23,z4,z24,z6]),(0,[z0,z1,z2,z27,z4,z111]),(0,[z39,z0,z1,z2,z119,z5]),(0,[z0,z1,z135,z4,z43,z446]),(0,[z0,z1,z456,z4,z43,z6]),(0,[z0,z1,z221,z4,z5,z26])],[(0,[z0,z1,z2,z106,z178,z5]),(0,[z15,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z43,z130]),(0,[z55,z0,z102,z4,z43,z6]),(0,[z0,z1,z2,z5,z814,z6])],[(0,[z0,z1,z2,z4,z239,z581]),(0,[z0,z1,z536,z2,z112,z6]),(0,[z0,z1,z14,z2,z116,z5]),(0,[z0,z1,z2,z4,z1022,z6]),(0,[z0,z1,z1023,z2,z4,z5]),(0,[z0,z1,z2,z987,z5,z6]),(0,[z0,z1,z2,z4,z1024,z6]),(0,[z0,z1,z2,z4,z62,z145]),(0,[z0,z1,z2,z1025,z4,z6])],[(0,[z0,z1,z2,z315,z5,z18]),(0,[z266,z1,z23,z4,z24,z6]),(0,[z78,z0,z1,z2,z119,z5]),(0,[z0,z1,z14,z191,z4,z5]),(0,[z0,z1,z2,z320,z43,z6])],[(0,[z0,z1,z2,z4,z1026,z6]),(0,[z0,z1,z2,z4,z434,z268]),(0,[z0,z1,z2,z4,z1027,z6]),(0,[z0,z1,z2,z27,z112,z43]),(0,[z0,z17,z2,z4,z79,z18]),(0,[z101,z0,z1,z21,z5,z6]),(0,[z0,z1,z2,z4,z224,z5]),(0,[z0,z1,z2,z119,z5,z551]),(0,[z0,z1,z14,z2,z119,z5])],[(0,[z0,z1,z14,z2,z4,z434]),(0,[z0,z1,z2,z4,z5,z188]),(0,[z0,z1,z8,z2,z93,z18])],[(0,[z0,z1,z2,z1028,z5,z6]),(0,[z0,z1,z2,z4,z5,z1029]),(0,[z0,z1,z2,z119,z9,z5]),(0,[z0,z600,z1,z2,z216,z5]),(0,[z0,z1,z2,z4,z355,z26])],[(0,[z0,z1,z2,z4,z43,z766]),(0,[z0,z1,z2,z27,z4,z291])],[(0,[z49,z1,z386,z4,z5,z6]),(0,[z0,z1030,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z44,z789]),(0,[z0,z1,z2,z833,z5,z6]),(0,[z0,z1,z2,z27,z5,z149]),(0,[z0,z1,z2,z1031,z5,z6])],[(0,[z0,z195,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1032,z6]),(0,[z209,z1,z890,z4,z5,z6]),(0,[z0,z46,z2,z4,z71,z6]),(0,[z0,z591,z2,z4,z233,z6]),(0,[z0,z1,z14,z2,z4,z930])],[(0,[z0,z1033,z2,z4,z5,z6]),(0,[z0,z1,z124,z4,z5,z564]),(0,[z0,z1,z2,z1034,z4,z5]),(0,[z0,z1,z2,z1035,z5,z6])],[(0,[z0,z1,z2,z4,z36,z6]),(0,[z0,z52,z2,z4,z43,z6]),(0,[z0,z1,z14,z2,z332,z5]),(0,[z0,z1,z1036,z2,z4,z5]),(0,[z0,z1,z2,z9,z57,z6]),(0,[z0,z1,z2,z4,z1037,z6]),(0,[z0,z46,z2,z4,z71,z98]),(0,[z0,z1,z2,z4,z166,z24]),(0,[z0,z1,z2,z905,z43,z6]),(0,[z0,z1,z4,z43,z165,z6]),(0,[z0,z1,z2,z27,z1025,z4])],[(0,[z0,z1,z2,z1038,z5,z6]),(0,[z0,z1039,z1,z2,z119,z5]),(0,[z0,z1,z245,z2,z5,z300])],[(0,[z0,z1,z2,z284,z434,z6]),(0,[z0,z1,z2,z133,z5,z564]),(0,[z0,z1,z2,z4,z1040,z5]),(0,[z0,z1,z14,z2,z345,z5]),(0,[z0,z1,z2,z632,z27,z5]),(0,[z0,z1,z171,z2,z4,z24]),(0,[z0,z1,z2,z1041,z5,z6])]],
   [[(0,[z0,z1,z48,z4,z5,z1042]),(0,[z0,z163,z452,z2,z4,z5]),(0,[z0,z1,z2,z4,z32,z571])],[(0,[z450,z1,z23,z4,z5,z6]),(0,[z283,z1,z2,z106,z5,z6]),(0,[z0,z108,z2,z4,z5,z18]),(0,[z0,z1,z2,z780,z43,z6])],[(0,[z0,z1,z2,z848,z5,z6]),(0,[z0,z1,z2,z4,z143,z323]),(0,[z0,z1,z2,z4,z1043,z6]),(0,[z0,z1,z2,z493,z5,z98]),(0,[z0,z1,z4,z1044,z5,z6]),(0,[z0,z1,z2,z4,z30,z26])],[(0,[z1045,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z116,z5,z564]),(0,[z0,z1,z2,z119,z5,z126]),(0,[z0,z1046,z1,z2,z4,z5]),(0,[z0,z1,z2,z1047,z5,z6])],[(0,[z0,z157,z2,z4,z36,z6]),(0,[z0,z1,z2,z4,z5,z1048]),(0,[z0,z1,z2,z4,z5,z1049]),(0,[z0,z1,z2,z4,z75,z6]),(0,[z0,z1,z2,z27,z1050,z5]),(0,[z0,z1,z2,z119,z5,z83]),(0,[z0,z1,z2,z186,z901,z6]),(0,[z0,z1,z2,z27,z5,z280])],[(0,[z0,z1,z2,z4,z5,z888]),(0,[z0,z1,z2,z1051,z5,z6]),(0,[z0,z1052,z1,z2,z4,z5]),(0,[z78,z1,z2,z20,z24,z6]),(0,[z366,z1,z2,z4,z5,z26]),(0,[z366,z1,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z99,z6])],[(0,[z0,z1,z2,z4,z1053,z6]),(0,[z0,z1,z1054,z2,z4,z5]),(0,[z0,z1,z2,z4,z1055,z6]),(0,[z0,z163,z2,z367,z5,z40]),(0,[z0,z1,z2,z1056,z4,z5])],[(0,[z0,z1,z48,z315,z5,z6]),(0,[z0,z1057,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z358,z26]),(1,[z0,z982,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1058])],[(0,[z0,z1059,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1060]),(0,[z0,z1,z2,z4,z1061,z5])],[(0,[z0,z1,z2,z4,z1062,z6]),(0,[z0,z1,z2,z4,z289,z71]),(0,[z54,z1,z2,z4,z5,z396]),(0,[z0,z1,z2,z4,z855,z6])],[(0,[z0,z1,z2,z133,z5,z18])],[(0,[z0,z1,z2,z4,z1063,z6]),(0,[z0,z274,z1,z203,z2,z4]),(0,[z1,z2,z890,z4,z5,z6]),(0,[z0,z1,z1064,z2,z4,z5]),(0,[z0,z1,z982,z4,z5,z6]),(0,[z0,z108,z2,z4,z5,z19]),(0,[z0,z1,z135,z4,z43,z26]),(0,[z0,z1,z539,z4,z43,z6])],[(0,[z0,z1,z2,z4,z1065,z6]),(0,[z0,z1,z1066,z4,z5,z6]),(0,[z0,z1,z2,z4,z1067,z26]),(0,[z0,z1,z14,z2,z4,z1068])],[(0,[z0,z1,z2,z1069,z5,z6]),(0,[z0,z1,z23,z27,z4,z24]),(0,[z63,z1,z14,z2,z106,z5])],[(0,[z0,z1,z2,z1070,z5,z6]),(0,[z0,z1,z2,z1071,z5,z6]),(0,[z0,z1,z2,z116,z5,z18]),(1,[z0,z1,z2,z5,z719])],[(0,[z0,z1,z2,z4,z1072,z6]),(0,[z1073,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z260,z5,z251])]],
   [[(0,[z0,z1,z2,z4,z5,z1074]),(0,[z0,z1,z2,z27,z5,z270])],[(0,[z49,z50,z14,z2,z4,z5]),(0,[z0,z1,z2,z4,z1075,z6]),(0,[z0,z1,z110,z4,z871,z6])],[(0,[z0,z2,z4,z5,z6,z1076]),(0,[z0,z1,z2,z4,z62,z564]),(0,[z0,z1077,z2,z4,z5,z6]),(0,[z1078,z1,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z1079])],[(0,[z0,z1,z2,z4,z1080,z6]),(0,[z0,z1,z2,z1081,z4,z5]),(0,[z0,z1,z257,z2,z27,z5]),(0,[z101,z0,z1,z462,z4,z5]),(0,[z156,z0,z2,z4,z5,z259]),(0,[z0,z1,z8,z2,z93,z6])],[(0,[z0,z1,z2,z1082,z5,z6]),(0,[z0,z342,z2,z332,z5,z6]),(0,[z209,z1,z23,z4,z5,z268]),(0,[z0,z1,z2,z4,z5,z1083]),(0,[z0,z1,z2,z4,z1084,z5]),(0,[z0,z1,z2,z4,z1085,z6]),(0,[z0,z1086,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1087,z24]),(0,[z0,z1,z2,z4,z5,z1088]),(0,[z0,z1,z2,z4,z5,z1089])],[(0,[z0,z1,z2,z4,z5,z1090]),(0,[z0,z1,z2,z4,z1091,z6]),(0,[z125,z1,z411,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1092]),(0,[z0,z1,z2,z4,z1093,z6]),(0,[z0,z1,z14,z4,z43,z24]),(0,[z0,z1,z2,z4,z1094,z6]),(0,[z1095,z1,z2,z27,z4,z5])],[(0,[z0,z1,z2,z4,z1096,z5]),(0,[z0,z2,z4,z1097,z5,z6]),(0,[z15,z1,z2,z4,z5,z789]),(0,[z0,z96,z2,z112,z5,z26]),(0,[z246,z1,z2,z4,z75,z6])],[(0,[z0,z1,z2,z4,z5,z87]),(0,[z0,z1,z2,z1098,z5,z6]),(0,[z0,z1,z2,z4,z5,z1099]),(0,[z0,z769,z2,z4,z43,z6])],[(0,[z0,z1,z4,z43,z218,z6]),(0,[z0,z1,z2,z4,z5,z1100]),(0,[z0,z222,z25,z4,z443,z6]),(0,[z0,z1,z8,z2,z448,z6])],[(0,[z0,z1,z2,z4,z5,z1101]),(0,[z0,z1,z2,z1102,z4,z5]),(0,[z0,z1,z1103,z2,z4,z5]),(0,[z0,z1104,z2,z4,z24,z6]),(0,[z0,z968,z2,z4,z43,z6])],[(0,[z86,z157,z2,z117,z5,z6]),(0,[z86,z157,z2,z27,z4,z5]),(0,[z0,z1,z2,z162,z4,z6]),(0,[z0,z1,z2,z27,z4,z140]),(0,[z0,z1,z2,z367,z43,z6]),(0,[z0,z1,z542,z4,z43,z6]),(0,[z0,z1,z2,z1105,z5,z6]),(0,[z0,z1,z2,z4,z1106,z6]),(0,[z0,z1,z2,z4,z974,z5])],[(0,[z0,z1,z386,z4,z5,z1107]),(0,[z0,z1,z1108,z4,z5,z6]),(0,[z0,z1,z2,z4,z289,z43]),(0,[z366,z222,z2,z4,z5,z6]),(0,[z1109,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z117,z43,z6]),(0,[z0,z1,z1110,z2,z4,z5]),(0,[z0,z1,z1111,z2,z4,z5])],[(0,[z209,z1,z23,z284,z5,z6]),(0,[z0,z1,z121,z2,z1050,z5]),(0,[z0,z1,z2,z185,z149,z6])],[(0,[z0,z1,z2,z4,z1112,z6]),(0,[z0,z1,z2,z4,z1113,z6]),(0,[z0,z1,z536,z2,z27,z4]),(0,[z0,z1,z2,z1114,z5,z6]),(0,[z0,z1,z2,z4,z5,z1115])],[(0,[z0,z1,z1116,z2,z4,z5]),(0,[z0,z2,z9,z987,z5,z6])]],
   [[(0,[z0,z1,z1117,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1118]),(0,[z0,z1,z2,z4,z5,z1119]),(0,[z0,z1,z1120,z2,z4,z5]),(0,[z0,z1,z2,z4,z1121,z5]),(0,[z1122,z0,z1,z2,z119,z5])],[(0,[z310,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z284,z5,z26]),(0,[z0,z296,z2,z4,z24,z6]),(0,[z0,z1,z2,z1123,z4,z5]),(0,[z0,z1,z148,z4,z5,z26])],[(0,[z0,z52,z14,z2,z4,z5]),(0,[z0,z1,z1124,z2,z4,z5]),(0,[z0,z1,z2,z4,z1125,z6]),(0,[z0,z1,z2,z4,z5,z1126]),(0,[z0,z1,z2,z27,z555,z5])],[(0,[z0,z52,z110,z4,z5,z6]),(0,[z0,z1127,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1128]),(0,[z0,z1,z2,z1129,z5,z6]),(0,[z0,z1,z2,z1130,z4,z5]),(0,[z0,z1,z2,z1131,z5,z6]),(0,[z0,z1,z2,z185,z186,z18])],[(0,[z0,z1,z2,z4,z5,z1132]),(0,[z0,z1,z672,z4,z5,z18]),(0,[z0,z1133,z2,z4,z5,z6]),(0,[z0,z46,z668,z2,z4,z6]),(0,[z0,z1134,z1,z2,z4,z5]),(0,[z458,z1,z2,z4,z474,z6]),(0,[z0,z1,z2,z27,z4,z255]),(0,[z0,z1,z2,z27,z4,z944])],[(0,[z0,z1135,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1136]),(0,[z0,z1,z1137,z2,z4,z5]),(0,[z1138,z1,z2,z4,z5,z6]),(0,[z0,z795,z2,z4,z43,z6])],[(0,[z0,z1,z2,z27,z4,z172]),(0,[z0,z1,z2,z4,z1139,z6]),(0,[z0,z1,z2,z1140,z5,z6]),(0,[z0,z1,z2,z1141,z5,z6]),(0,[z0,z1,z2,z5,z349,z212]),(0,[z0,z1,z2,z1142,z5,z26])],[(0,[z64,z1,z110,z4,z5,z6]),(0,[z366,z1,z2,z260,z5,z6]),(0,[z0,z1,z2,z1143,z4,z5]),(0,[z0,z1,z1144,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1145]),(0,[z0,z17,z2,z4,z73,z6])],[(0,[z0,z1,z2,z1146,z5,z6]),(0,[z65,z0,z2,z9,z5,z391]),(0,[z0,z1,z2,z4,z5,z476]),(0,[z0,z1,z2,z727,z24,z6])],[(0,[z0,z1,z2,z4,z5,z1147]),(0,[z0,z1,z1148,z4,z5,z6]),(0,[z0,z1,z2,z260,z358,z6]),(0,[z1149,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z326,z186,z6]),(0,[z0,z1,z2,z4,z24,z730]),(0,[z0,z1,z14,z2,z486,z5])],[(0,[z63,z1,z2,z106,z43,z6]),(0,[z42,z0,z1,z2,z4,z289]),(0,[z0,z1,z2,z4,z1150,z6])],[(0,[z0,z1,z2,z4,z5,z1151]),(0,[z0,z1,z61,z2,z4,z689]),(0,[z0,z177,z2,z4,z5,z19])],[(1,[z1,z890,z4,z5,z6]),(0,[z1,z2,z23,z27,z20,z5]),(0,[z0,z1,z2,z4,z5,z1152]),(0,[z0,z1,z2,z572,z5,z6]),(0,[z0,z2,z27,z9,z112,z5]),(0,[z0,z1,z2,z4,z57,z26]),(0,[z0,z1,z2,z4,z5,z494]),(0,[z0,z1,z2,z27,z149,z24]),(0,[z0,z1,z2,z119,z5,z534])],[(0,[z0,z1,z23,z4,z24,z18]),(0,[z0,z1,z2,z4,z193,z212])],[(0,[z0,z1,z890,z4,z5,z6]),(0,[z0,z1,z2,z1153,z5,z6]),(0,[z0,z1,z2,z1154,z5,z6]),(0,[z0,z1,z2,z1155,z5,z6])],[(0,[z0,z1,z2,z4,z5,z1156]),(0,[z0,z274,z1,z2,z4,z26]),(0,[z0,z1,z2,z4,z1157,z6]),(0,[z0,z1,z2,z1158,z5,z6]),(0,[z0,z1,z2,z4,z1159,z6]),(0,[z15,z1,z2,z4,z43,z44]),(0,[z0,z1,z2,z4,z5,z1160]),(0,[z0,z612,z2,z4,z5,z40]),(0,[z0,z1161,z2,z4,z5,z6]),(0,[z0,z1,z1162,z2,z4,z5]),(0,[z0,z1163,z2,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z4,z1164,z5]),(0,[z0,z1,z2,z4,z5,z323]),(0,[z420,z0,z1,z21,z5,z6]),(0,[z0,z31,z1,z4,z24,z6])],[(0,[z0,z1,z2,z4,z1165,z6]),(0,[z65,z0,z2,z9,z43,z6]),(0,[z0,z108,z2,z5,z122,z6]),(0,[z0,z1,z2,z227,z4,z5]),(0,[z0,z1,z2,z4,z5,z1166]),(0,[z0,z1,z2,z4,z1167,z6]),(0,[z0,z1,z4,z43,z24,z26]),(0,[z0,z1,z497,z2,z4,z7]),(0,[z0,z1,z2,z27,z4,z1168])],[(0,[z0,z1,z1169,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z564]),(0,[z101,z0,z1,z21,z43,z6])],[(0,[z0,z1,z2,z27,z398,z5]),(0,[z0,z1,z307,z2,z4,z43]),(0,[z0,z1,z2,z4,z43,z188]),(0,[z0,z1,z124,z133,z5,z6]),(0,[z0,z1,z2,z4,z1170,z6]),(0,[z0,z152,z1,z4,z24,z26]),(0,[z0,z1,z2,z119,z4,z24]),(0,[z0,z524,z1,z4,z5,z26]),(0,[z0,z1,z2,z27,z4,z1171]),(0,[z0,z1,z2,z393,z4,z624])],[(0,[z0,z1172,z2,z4,z5,z6]),(0,[z0,z1,z1173,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1174]),(0,[z0,z1,z2,z4,z24,z130]),(0,[z55,z0,z102,z4,z24,z6]),(0,[z0,z1175,z2,z4,z5,z6])],[(0,[z0,z1,z2,z27,z117,z5]),(0,[z0,z1,z2,z1051,z4,z5]),(0,[z0,z222,z25,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1176])],[(0,[z0,z1,z2,z27,z649,z5]),(0,[z15,z0,z1,z2,z4,z111]),(0,[z0,z1,z2,z4,z5,z1177]),(0,[z0,z153,z2,z4,z79,z6]),(0,[z0,z1,z2,z4,z557,z43]),(0,[z0,z1,z2,z4,z1178,z18])],[(0,[z86,z157,z2,z4,z36,z6]),(0,[z0,z195,z2,z4,z43,z6]),(0,[z0,z296,z2,z4,z5,z155]),(0,[z0,z1,z124,z116,z5,z6]),(0,[z0,z1,z2,z4,z5,z66]),(0,[z0,z1,z4,z385,z24,z6]),(0,[z0,z1,z2,z4,z193,z6]),(0,[z0,z1,z189,z2,z4,z62]),(0,[z0,z1,z2,z958,z5,z6]),(0,[z0,z13,z1,z4,z5,z1179]),(0,[z283,z1,z2,z254,z4,z5]),(0,[z0,z94,z1,z2,z4,z114])],[(0,[z0,z1,z2,z1180,z5,z6]),(0,[z0,z1181,z2,z4,z5,z6]),(0,[z0,z1182,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1183,z5]),(0,[z65,z0,z2,z987,z5,z6]),(0,[z0,z421,z2,z4,z71,z6]),(0,[z0,z177,z2,z4,z5,z423]),(0,[z0,z1,z121,z2,z27,z43]),(0,[z0,z1,z2,z462,z4,z43])],[(0,[z330,z1,z110,z4,z5,z6]),(0,[z0,z1,z2,z464,z4,z43]),(0,[z0,z1,z2,z112,z224,z5]),(0,[z0,z533,z2,z4,z219,z6])],[(0,[z0,z1,z386,z4,z24,z6]),(0,[z0,z1,z2,z4,z111,z564]),(0,[z0,z1,z2,z572,z71,z6]),(0,[z0,z1,z2,z4,z71,z494])],[(0,[z0,z1,z536,z2,z4,z6]),(0,[z0,z1,z14,z2,z4,z358]),(0,[z0,z1,z2,z27,z185,z186]),(0,[z0,z963,z14,z2,z4,z5])],[(0,[z0,z1,z2,z4,z6,z1184]),(0,[z0,z52,z2,z4,z5,z268]),(0,[z0,z1,z171,z2,z367,z5]),(0,[z0,z1,z2,z4,z237,z66]),(0,[z0,z1,z14,z2,z4,z145])],[(0,[z0,z1,z2,z332,z5,z268]),(0,[z0,z1,z2,z27,z4,z43]),(0,[z0,z1,z14,z2,z4,z24])],[(0,[z0,z342,z2,z4,z5,z581]),(0,[z1,z23,z4,z392,z24,z6]),(0,[z0,z1,z307,z2,z162,z4]),(0,[z0,z1,z2,z260,z43,z6]),(0,[z313,z1,z2,z4,z75,z6]),(0,[z101,z0,z1,z2,z27,z75])],[(0,[z0,z1,z2,z4,z1185,z6]),(0,[z0,z583,z2,z4,z5,z339]),(0,[z313,z1,z2,z4,z99,z6])]],
   [[(0,[z0,z1,z2,z4,z1186,z6]),(0,[z0,z1,z2,z5,z1187,z6]),(0,[z0,z1,z2,z20,z5,z413]),(0,[z39,z0,z2,z4,z183,z5]),(0,[z0,z1,z2,z4,z979,z43])],[(0,[z0,z1,z2,z4,z1188,z6]),(0,[z0,z1,z2,z332,z43,z6]),(0,[z65,z0,z2,z9,z57,z6]),(0,[z0,z1,z2,z27,z5,z719])],[(0,[z0,z1,z536,z2,z133,z6]),(0,[z54,z0,z1,z2,z4,z111]),(0,[z0,z1,z2,z4,z1189,z6]),(0,[z0,z1,z2,z4,z1190,z5]),(0,[z0,z1,z2,z27,z426,z5])],[(0,[z0,z1,z2,z4,z1191,z6]),(0,[z54,z1,z2,z4,z24,z16]),(0,[z0,z1,z2,z493,z5,z6])],[(0,[z0,z1,z2,z1192,z4,z5]),(0,[z0,z1,z110,z4,z24,z410]),(0,[z15,z1,z2,z4,z5,z551]),(0,[z0,z1,z2,z27,z4,z57]),(0,[z0,z1,z2,z4,z24,z446])],[(0,[z0,z52,z2,z284,z5,z6]),(0,[z0,z1,z2,z4,z1193,z6]),(0,[z0,z1,z2,z4,z1194,z6]),(0,[z0,z1,z2,z4,z111,z18]),(0,[z0,z1,z2,z1195,z5,z6])],[(0,[z78,z1,z2,z20,z5,z26]),(0,[z0,z1,z124,z4,z62,z6])],[(0,[z0,z1,z2,z1196,z5,z6]),(0,[z0,z1,z2,z4,z1197,z5]),(0,[z0,z1,z2,z4,z1198,z6]),(0,[z0,z1,z2,z4,z62,z175]),(0,[z0,z1,z2,z4,z5,z19])],[(0,[z0,z1,z2,z117,z5,z374]),(0,[z64,z1,z2,z27,z20,z5]),(0,[z0,z46,z195,z2,z4,z6]),(0,[z42,z1,z14,z2,z4,z51]),(0,[z0,z1,z2,z24,z349,z18])],[(0,[z0,z455,z1,z2,z4,z26]),(0,[z1199,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z185,z379,z6])],[(0,[z0,z1,z124,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z1200]),(0,[z0,z1,z2,z4,z178,z5]),(0,[z0,z683,z1,z4,z24,z6]),(0,[z0,z1,z497,z2,z4,z62]),(0,[z399,z1,z406,z2,z4,z5])],[(0,[z0,z1,z14,z2,z4,z36]),(0,[z50,z751,z2,z4,z5,z6]),(0,[z0,z1,z1201,z2,z4,z5]),(0,[z64,z1,z110,z4,z172,z6]),(0,[z0,z1,z2,z4,z5,z1202]),(0,[z0,z1,z2,z4,z5,z1203]),(0,[z0,z1,z2,z4,z128,z18]),(0,[z0,z1,z2,z4,z32,z418]),(0,[z0,z1,z2,z4,z5,z1204]),(0,[z101,z0,z1,z2,z27,z99]),(0,[z0,z1,z1205,z2,z4,z5])],[(0,[z0,z1,z121,z2,z27,z319])],[(0,[z0,z1,z2,z4,z5,z1042]),(0,[z0,z1,z2,z1206,z4,z6]),(0,[z0,z1,z2,z4,z1207,z6]),(0,[z0,z1,z2,z4,z1079,z6]),(0,[z1208,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1209]),(0,[z101,z0,z1,z14,z21,z5]),(0,[z0,z1,z2,z1210,z4,z5])],[(0,[z0,z50,z2,z4,z36,z6]),(0,[z0,z1,z466,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1211]),(0,[z0,z1,z2,z27,z635,z5]),(0,[z1212,z1,z2,z4,z5,z6]),(0,[z0,z1,z121,z70,z24,z6])],[(0,[z0,z1,z48,z4,z5,z6]),(0,[z246,z1,z2,z4,z5,z18])]],
   [[(0,[z0,z1,z2,z4,z5,z1213]),(0,[z0,z1,z2,z27,z697,z5]),(0,[z0,z1,z60,z4,z5,z18])],[(0,[z86,z157,z2,z4,z5,z87]),(0,[z0,z1,z1214,z4,z5,z6]),(0,[z0,z1,z2,z27,z4,z319])],[(0,[z0,z1,z2,z1215,z5,z6]),(0,[z0,z1,z110,z4,z24,z252]),(0,[z78,z1,z14,z2,z20,z5]),(0,[z0,z1,z2,z4,z143,z18])],[(0,[z0,z1,z2,z4,z43,z87]),(0,[z0,z1,z2,z4,z1171,z6]),(0,[z168,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z27,z4,z158]),(0,[z0,z1,z2,z4,z5,z1216]),(0,[z0,z1,z2,z4,z145,z18]),(0,[z0,z1,z2,z4,z1217,z6]),(0,[z0,z1,z8,z2,z413,z93])],[(0,[z0,z1,z2,z315,z5,z6]),(0,[z0,z1,z2,z1218,z4,z5]),(0,[z420,z0,z1,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z423]),(0,[z0,z1,z2,z4,z43,z1100]),(0,[z210,z1,z2,z4,z5,z551]),(0,[z0,z1,z61,z2,z119,z5])],[(0,[z0,z1,z2,z1219,z5,z6]),(0,[z42,z1,z2,z4,z51,z26]),(0,[z0,z17,z2,z4,z79,z6]),(0,[z0,z1,z512,z2,z27,z5])],[(0,[z327,z1,z2,z20,z5,z6]),(0,[z0,z1,z2,z4,z1220,z6])],[(0,[z0,z192,z1,z4,z5,z26]),(0,[z0,z1,z818,z2,z24,z6])],[(0,[z1,z157,z386,z4,z5,z6]),(0,[z0,z1,z2,z4,z1221,z6]),(0,[z0,z1,z191,z116,z5,z6]),(0,[z0,z1,z2,z4,z1222,z6]),(0,[z0,z163,z2,z4,z5,z199]),(0,[z0,z1,z2,z4,z5,z92]),(0,[z0,z1,z14,z2,z4,z355])],[(0,[z0,z1,z1223,z4,z5,z6]),(0,[z209,z1,z23,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1224]),(0,[z246,z1,z2,z4,z5,z19])],[(0,[z0,z1,z2,z4,z1225,z6]),(0,[z0,z1,z2,z27,z332,z5]),(0,[z0,z1,z2,z4,z158,z18]),(0,[z0,z96,z1,z2,z119,z5]),(0,[z0,z1,z2,z4,z24,z831]),(0,[z0,z1,z2,z119,z1226,z5])],[(0,[z64,z1,z110,z4,z305,z6]),(0,[z0,z1,z2,z27,z4,z305]),(0,[z0,z1,z2,z5,z122,z19]),(0,[z0,z1,z113,z2,z4,z62])],[(0,[z0,z1,z386,z4,z529,z6]),(0,[z0,z195,z14,z2,z4,z5]),(0,[z312,z0,z2,z4,z5,z339])],[(0,[z0,z52,z2,z4,z434,z6]),(0,[z0,z1,z61,z2,z345,z5]),(0,[z0,z1,z2,z272,z5,z18]),(0,[z0,z1,z2,z4,z24,z26]),(0,[z0,z1,z60,z4,z178,z5])],[(0,[z0,z1,z2,z4,z1227,z5]),(0,[z0,z1,z2,z216,z128,z6]),(0,[z0,z1,z14,z2,z4,z193]),(0,[z0,z1,z2,z4,z43,z1126])],[(0,[z0,z1,z203,z2,z4,z24]),(0,[z125,z1,z2,z133,z126,z6]),(0,[z42,z1,z2,z4,z754,z6]),(0,[z0,z1,z2,z4,z5,z1228]),(0,[z0,z1,z14,z2,z4,z143]),(0,[z0,z1,z2,z5,z872,z6]),(0,[z101,z0,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z5,z1229])]],
   [[(0,[z0,z1,z2,z4,z1230,z5]),(0,[z0,z1,z191,z4,z5,z564]),(0,[z0,z108,z2,z4,z5,z6]),(0,[z0,z1,z2,z119,z5,z1231])],[(0,[z0,z1,z2,z4,z172,z18]),(0,[z1232,z0,z1,z2,z119,z5])],[(0,[z0,z296,z2,z4,z5,z26]),(0,[z0,z296,z2,z27,z4,z5]),(0,[z0,z1,z2,z4,z5,z1233]),(0,[z487,z0,z1,z2,z27,z5]),(0,[z0,z1,z14,z2,z5,z382]),(0,[z0,z1,z14,z2,z27,z24]),(0,[z0,z1,z2,z4,z5,z1234])],[(0,[z0,z1235,z2,z4,z5,z6]),(0,[z64,z1,z110,z4,z43,z6]),(0,[z125,z1,z2,z116,z126,z6]),(0,[z0,z1,z14,z2,z196,z5]),(0,[z0,z1,z2,z4,z1236,z5]),(0,[z0,z17,z2,z4,z728,z6]),(0,[z101,z0,z1,z224,z21,z5]),(0,[z0,z1,z2,z4,z5,z1237]),(0,[z0,z152,z1,z14,z4,z24]),(0,[z0,z1,z2,z4,z5,z1238])],[(0,[z86,z203,z157,z2,z4,z5]),(0,[z0,z1,z2,z1239,z4,z5]),(0,[z0,z1,z592,z4,z24,z6]),(0,[z0,z1,z1240,z2,z4,z6]),(0,[z0,z1,z2,z22,z4,z24]),(0,[z0,z177,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z43,z476]),(0,[z0,z1,z2,z119,z5,z18])],[(0,[z0,z1,z2,z4,z36,z374]),(0,[z54,z1,z2,z4,z5,z789]),(0,[z0,z1,z2,z4,z5,z1241])],[(0,[z0,z1,z124,z4,z5,z6]),(0,[z0,z1,z2,z216,z145,z6]),(0,[z246,z1,z2,z4,z5,z423]),(0,[z0,z2,z4,z1242,z5,z6]),(0,[z0,z2,z4,z5,z18,z1076])],[(0,[z0,z1,z2,z4,z1243,z6]),(0,[z0,z1,z2,z4,z128,z6])],[(0,[z0,z455,z1,z203,z2,z4]),(0,[z0,z1,z2,z4,z5,z1244]),(0,[z0,z1,z23,z4,z434,z6]),(0,[z0,z1,z2,z27,z340,z5]),(0,[z0,z1,z2,z4,z1245,z5]),(0,[z0,z1,z2,z9,z557,z5]),(0,[z0,z402,z2,z4,z79,z6]),(0,[z0,z1,z2,z572,z43,z6]),(0,[z0,z1,z2,z4,z43,z494])],[(0,[z0,z1,z2,z133,z5,z6]),(0,[z0,z1,z2,z4,z5,z1246]),(0,[z54,z1,z2,z4,z618,z5]),(0,[z0,z1,z2,z4,z114,z83])],[(0,[z0,z1,z2,z345,z24,z6]),(0,[z0,z1,z2,z27,z4,z443]),(0,[z0,z1,z2,z24,z814,z6]),(0,[z0,z14,z1247,z2,z4,z5])],[(0,[z0,z1,z1248,z2,z4,z6]),(0,[z0,z1,z2,z1249,z5,z6]),(0,[z0,z1,z2,z4,z43,z581]),(0,[z0,z1,z191,z4,z5,z18]),(0,[z125,z1,z2,z4,z126,z564]),(0,[z0,z96,z171,z2,z112,z5]),(0,[z0,z1,z2,z4,z1250,z6])],[(0,[z0,z1,z2,z4,z5,z1251]),(0,[z54,z1,z2,z164,z4,z5]),(0,[z0,z1,z14,z2,z320,z5]),(0,[z0,z1,z2,z4,z43,z323]),(0,[z0,z1,z2,z555,z394,z6])],[(0,[z0,z1,z2,z4,z5,z1252]),(0,[z0,z1,z2,z116,z5,z6]),(0,[z0,z222,z2,z27,z112,z5]),(0,[z0,z1,z2,z4,z5,z1253]),(0,[z0,z1,z121,z2,z227,z5]),(0,[z298,z1,z2,z4,z181,z6])],[(0,[z0,z1,z2,z4,z5,z1254]),(0,[z49,z50,z2,z4,z5,z26]),(0,[z52,z2,z23,z4,z5,z6]),(0,[z0,z1,z1255,z2,z20,z5]),(0,[z0,z1,z2,z1256,z4,z5]),(0,[z197,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z119,z5,z19])],[(0,[z0,z1,z23,z4,z443,z6]),(0,[z0,z1,z2,z4,z1257,z6]),(0,[z0,z1,z2,z1258,z5,z6]),(0,[z0,z1,z2,z4,z145,z6]),(0,[z0,z1,z2,z4,z1259,z5]),(0,[z0,z1,z135,z27,z4,z43])]],
   [[(0,[z49,z50,z2,z4,z24,z6]),(0,[z0,z1,z1260,z4,z5,z6]),(0,[z0,z1,z1261,z2,z4,z5]),(0,[z42,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z1262,z5,z6]),(0,[z0,z1,z115,z4,z24,z6]),(0,[z0,z1172,z2,z4,z43,z6])],[(0,[z0,z1,z2,z4,z1263,z6]),(0,[z0,z1,z157,z2,z1051,z5]),(0,[z0,z1264,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1265]),(0,[z0,z1,z2,z4,z5,z1266]),(0,[z0,z1,z2,z1267,z5,z6]),(0,[z0,z1,z2,z119,z178,z5]),(0,[z282,z0,z2,z4,z5,z347])],[(0,[z0,z1,z2,z1268,z4,z6]),(0,[z0,z1,z2,z4,z5,z1269]),(0,[z0,z2,z102,z260,z5,z6]),(0,[z65,z0,z2,z9,z24,z6]),(0,[z246,z108,z2,z4,z5,z6]),(0,[z0,z1,z497,z2,z4,z417])],[(0,[z86,z350,z157,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1270]),(0,[z0,z1,z2,z4,z1271,z6]),(0,[z0,z1272,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z43,z66]),(0,[z0,z1,z2,z958,z43,z6])],[(0,[z64,z1,z466,z4,z5,z6]),(0,[z0,z1,z536,z2,z464,z4]),(0,[z0,z1,z2,z4,z5,z1273]),(0,[z0,z1182,z2,z4,z43,z6])],[(0,[z209,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z4,z24,z155]),(0,[z55,z0,z102,z4,z5,z26]),(0,[z0,z1,z1274,z2,z4,z24])],[(0,[z0,z1,z2,z1275,z5,z6]),(0,[z0,z2,z1276,z4,z5,z6]),(0,[z125,z1,z2,z4,z126,z18]),(0,[z0,z222,z25,z27,z4,z5]),(0,[z0,z222,z25,z4,z5,z26]),(0,[z0,z265,z2,z9,z5,z6]),(0,[z0,z1,z2,z1044,z5,z6]),(0,[z0,z1,z2,z1277,z4,z5])],[(0,[z350,z0,z1,z2,z4,z24]),(0,[z0,z1,z2,z1278,z4,z6]),(0,[z0,z1,z1261,z2,z133,z5]),(0,[z0,z1279,z1,z2,z4,z6]),(0,[z0,z1,z2,z216,z5,z18]),(0,[z0,z1280,z2,z4,z5,z6]),(0,[z0,z1,z60,z119,z5,z18]),(0,[z0,z1,z2,z27,z4,z869])],[(0,[z209,z1,z23,z4,z434,z6]),(0,[z64,z1,z110,z4,z5,z252]),(0,[z0,z1,z2,z1281,z5,z6]),(0,[z0,z1,z69,z462,z4,z5]),(0,[z0,z1,z1282,z2,z4,z5])],[(0,[z0,z1,z2,z320,z24,z6]),(0,[z0,z1,z2,z4,z1283,z6]),(0,[z0,z1,z2,z4,z5,z1284])],[(0,[z0,z1,z25,z2,z119,z5]),(0,[z0,z1,z2,z4,z32,z482]),(0,[z0,z1,z2,z4,z5,z1285]),(0,[z0,z1,z14,z2,z367,z5]),(0,[z0,z1,z2,z27,z5,z501]),(0,[z0,z1,z4,z5,z26,z18])],[(0,[z0,z1,z386,z27,z4,z5]),(0,[z0,z1,z386,z117,z5,z6]),(0,[z0,z1,z386,z4,z5,z26]),(0,[z209,z52,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1286]),(0,[z0,z1,z4,z305,z24,z6]),(0,[z0,z1,z2,z4,z5,z1287]),(0,[z1288,z1,z2,z4,z5,z6]),(0,[z0,z46,z2,z4,z71,z226])],[(0,[z450,z0,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z434,z26]),(0,[z0,z1,z2,z4,z5,z1289]),(0,[z0,z1,z2,z4,z1290,z6]),(0,[z0,z1,z2,z1291,z4,z5]),(0,[z0,z1,z329,z2,z27,z5])],[(0,[z0,z1,z1292,z2,z112,z5]),(1,[z0,z2,z4,z5,z741]),(0,[z0,z1,z14,z2,z217,z5])],[(0,[z0,z1,z2,z4,z1293,z6]),(0,[z0,z1,z1294,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1295]),(0,[z0,z1,z2,z4,z5,z1296]),(0,[z240,z0,z1,z462,z4,z5])],[(0,[z0,z1,z2,z4,z529,z26]),(0,[z0,z1,z203,z2,z1051,z5]),(0,[z0,z1,z4,z474,z24,z6]),(0,[z0,z1,z2,z1297,z4,z5]),(0,[z0,z1,z2,z260,z24,z6]),(0,[z0,z1,z2,z493,z43,z6]),(0,[z0,z1,z2,z119,z5,z24]),(0,[z0,z377,z2,z4,z73,z6])]],
   [[(0,[z0,z1,z2,z4,z5,z18]),(0,[z0,z1,z536,z307,z2,z4])],[(0,[z0,z52,z2,z4,z24,z6]),(0,[z42,z0,z1,z2,z572,z6]),(0,[z0,z1,z2,z4,z5,z741]),(0,[z0,z1,z4,z5,z26,z654]),(0,[z313,z1,z2,z4,z5,z19]),(0,[z0,z1,z2,z185,z557,z186])],[(0,[z0,z1,z2,z332,z24,z6]),(0,[z0,z1,z14,z2,z216,z5]),(0,[z0,z1,z2,z185,z186,z6])],[(0,[z0,z1,z2,z27,z670,z5]),(0,[z0,z1,z2,z4,z5,z1298]),(0,[z0,z1,z2,z4,z443,z26]),(0,[z0,z1,z2,z4,z57,z66]),(0,[z0,z1,z14,z2,z572,z5]),(0,[z0,z1,z2,z4,z43,z19]),(0,[z0,z1,z2,z27,z43,z280])],[(0,[z684,z0,z1,z2,z4,z32])],[(0,[z0,z1,z2,z4,z1299,z6]),(0,[z0,z1,z2,z4,z1300,z6]),(0,[z0,z1,z2,z4,z237,z18]),(0,[z0,z1301,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z624])],[(0,[z0,z1,z2,z4,z5,z1302]),(0,[z0,z1,z14,z2,z4,z237]),(0,[z0,z1,z221,z227,z4,z5]),(0,[z0,z1,z2,z456,z4,z62])],[(0,[z0,z1,z1169,z2,z117,z5]),(0,[z0,z1,z2,z464,z162,z4]),(0,[z0,z1,z2,z27,z106,z24]),(0,[z1303,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z185,z304,z6]),(0,[z240,z0,z1,z2,z27,z5]),(0,[z0,z680,z1,z4,z24,z6])],[(0,[z0,z1,z2,z4,z239,z18]),(0,[z0,z1,z2,z27,z499,z5]),(0,[z0,z333,z1,z2,z119,z5])],[(0,[z86,z157,z48,z4,z5,z6]),(0,[z0,z1,z2,z1304,z4,z5]),(0,[z0,z1,z171,z2,z5,z122]),(0,[z65,z0,z14,z2,z9,z5])],[(0,[z0,z1,z2,z1305,z5,z6]),(0,[z0,z1,z2,z4,z5,z1306]),(0,[z0,z1,z2,z1307,z572,z5]),(0,[z0,z1308,z2,z4,z5,z6])],[(0,[z0,z1,z48,z4,z1309,z6]),(0,[z0,z1,z48,z4,z43,z6]),(0,[z0,z200,z2,z112,z5,z6]),(0,[z0,z1,z2,z27,z162,z4]),(0,[z0,z1,z2,z22,z106,z5]),(0,[z42,z0,z1,z2,z4,z494]),(0,[z0,z1,z2,z4,z1310,z6]),(0,[z0,z1,z1311,z2,z4,z5]),(0,[z0,z1,z2,z5,z719,z6])],[(0,[z1,z2,z23,z332,z5,z6]),(0,[z0,z1,z23,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1312]),(0,[z0,z1,z536,z2,z27,z20]),(0,[z0,z1,z2,z345,z5,z44]),(0,[z0,z1,z2,z4,z1313,z5]),(0,[z0,z1,z88,z2,z4,z5]),(0,[z0,z1,z2,z119,z5,z93]),(0,[z0,z1,z2,z1314,z119,z5]),(0,[z0,z1,z2,z27,z4,z1315]),(0,[z0,z1,z2,z27,z5,z523]),(0,[z0,z1,z2,z4,z1316,z6]),(0,[z0,z1,z61,z2,z4,z974])],[(0,[z0,z1,z2,z1317,z4,z5]),(0,[z0,z1,z2,z1239,z284,z5]),(0,[z0,z96,z2,z22,z112,z5]),(0,[z0,z1,z2,z112,z178,z5]),(0,[z0,z211,z2,z4,z79,z6]),(0,[z0,z1,z1318,z2,z4,z5]),(0,[z0,z1,z539,z4,z5,z26])],[(0,[z86,z157,z2,z315,z5,z6]),(0,[z0,z1,z2,z4,z1319,z6]),(0,[z0,z1,z2,z4,z5,z1320]),(0,[z313,z1,z2,z4,z5,z423]),(0,[z0,z1,z2,z227,z4,z43]),(0,[z0,z152,z1,z2,z119,z5])],[(0,[z0,z1,z2,z510,z27,z5]),(0,[z0,z1,z2,z4,z5,z1321]),(0,[z55,z0,z102,z4,z5,z130]),(0,[z0,z1,z121,z70,z5,z26]),(0,[z0,z1,z2,z4,z593,z534])]],
   [[(0,[z0,z1,z2,z315,z43,z6]),(0,[z0,z1,z2,z4,z5,z1322]),(0,[z0,z1,z68,z2,z4,z62]),(0,[z0,z1,z2,z4,z43,z423]),(0,[z0,z1,z1323,z2,z4,z5]),(0,[z0,z1,z14,z2,z4,z1324]),(0,[z0,z1163,z14,z2,z4,z5])],[(0,[z0,z1,z2,z4,z255,z18]),(0,[z0,z13,z1,z462,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1325]),(0,[z0,z1,z1326,z2,z4,z5]),(0,[z0,z1,z806,z27,z4,z5])],[(0,[z0,z1,z1327,z2,z4,z5]),(0,[z0,z1,z2,z1328,z5,z6]),(0,[z125,z1,z103,z2,z4,z126]),(0,[z0,z1,z2,z4,z1329,z5]),(0,[z0,z1,z2,z216,z5,z6]),(0,[z0,z1,z4,z502,z24,z6]),(0,[z0,z1,z634,z4,z43,z6])],[(0,[z0,z397,z1,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1330]),(0,[z0,z1,z2,z27,z116,z5]),(0,[z0,z1,z2,z4,z43,z92])],[(0,[z0,z1,z2,z4,z1178,z6]),(1,[z1,z2,z4,z754,z6]),(0,[z0,z1,z2,z4,z1183,z43])],[(0,[z0,z646,z2,z112,z5,z6]),(0,[z0,z1,z2,z27,z112,z24]),(0,[z0,z1,z10,z4,z43,z6]),(0,[z0,z1,z2,z27,z119,z5]),(0,[z0,z1,z2,z4,z224,z43]),(0,[z0,z1,z4,z5,z742,z6]),(0,[z0,z13,z1,z4,z5,z26]),(0,[z0,z2,z27,z1331,z4,z5]),(0,[z0,z1,z2,z4,z32,z516])],[(0,[z0,z1,z2,z27,z4,z434]),(0,[z0,z1,z2,z4,z5,z744]),(0,[z0,z1,z536,z2,z93,z6]),(0,[z0,z1,z191,z133,z5,z6]),(0,[z0,z1,z2,z4,z754,z6]),(0,[z42,z1,z2,z4,z314,z6]),(0,[z0,z1,z2,z4,z143,z286])],[(0,[z350,z0,z455,z1,z2,z4]),(0,[z0,z1,z124,z185,z4,z6]),(0,[z0,z1,z2,z4,z5,z1332]),(0,[z0,z600,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z1333,z6]),(0,[z0,z1,z2,z4,z355,z18]),(0,[z0,z820,z2,z27,z4,z5])],[(0,[z0,z274,z1,z14,z2,z4]),(0,[z105,z0,z1,z2,z27,z5]),(0,[z0,z1334,z1,z2,z4,z6]),(0,[z420,z0,z1,z2,z27,z5]),(0,[z0,z1,z2,z27,z5,z544]),(0,[z0,z1,z85,z2,z4,z5])],[(0,[z209,z1,z23,z27,z4,z5]),(0,[z209,z1,z23,z4,z5,z26]),(0,[z125,z1,z2,z4,z618,z6]),(0,[z0,z1,z1335,z2,z4,z5]),(0,[z0,z1,z2,z4,z1336,z6]),(0,[z313,z108,z2,z4,z5,z6]),(0,[z0,z630,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z901,z6])],[(0,[z0,z1,z2,z4,z1337,z6]),(0,[z0,z1,z2,z965,z24,z6]),(1,[z0,z1,z2,z4,z974])],[(0,[z0,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z1338,z5,z6]),(0,[z0,z1339,z2,z4,z5,z6]),(0,[z0,z46,z2,z4,z166,z71]),(0,[z0,z108,z2,z4,z43,z6]),(0,[z0,z1,z2,z1340,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1341]),(0,[z0,z1,z2,z119,z106,z5]),(0,[z101,z0,z1,z27,z21,z5]),(0,[z0,z1,z121,z2,z224,z5]),(0,[z0,z1,z2,z4,z5,z1342])],[(0,[z0,z1,z1343,z2,z4,z5]),(0,[z0,z1,z2,z1344,z5,z6]),(0,[z0,z1,z2,z4,z5,z98]),(0,[z0,z1,z2,z367,z24,z6]),(0,[z0,z1,z2,z119,z185,z5]),(0,[z0,z1,z2,z4,z5,z1345])],[(0,[z0,z1,z2,z4,z5,z1346]),(0,[z0,z1,z2,z27,z345,z5]),(0,[z125,z1,z124,z4,z126,z6]),(0,[z0,z1,z1347,z2,z4,z5]),(0,[z0,z1,z69,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z117,z24,z6]),(0,[z0,z1,z2,z4,z1348,z6]),(0,[z0,z1,z1349,z2,z4,z5]),(0,[z0,z1,z2,z4,z32,z534]),(0,[z0,z1,z2,z4,z1350,z18])],[(0,[z0,z1,z2,z4,z1351,z6]),(0,[z0,z1,z1352,z2,z4,z5]),(0,[z0,z1,z2,z332,z434,z6]),(0,[z0,z1,z2,z4,z5,z1353]),(0,[z0,z1,z103,z2,z4,z5]),(0,[z0,z1,z2,z4,z237,z6]),(0,[z1354,z1,z2,z4,z5,z6]),(0,[z1355,z1,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z1356,z6]),(0,[z0,z1,z2,z27,z20,z24]),(0,[z0,z1,z2,z1357,z4,z6]),(0,[z0,z1,z2,z4,z1358,z5]),(0,[z0,z1,z2,z4,z1359,z6]),(0,[z0,z1,z2,z27,z9,z5]),(0,[z0,z1,z8,z2,z609,z6]),(0,[z0,z1,z2,z4,z5,z1360]),(0,[z0,z1,z2,z4,z1361,z6]),(0,[z0,z1,z2,z4,z1362,z6]),(0,[z0,z1,z2,z27,z605,z5]),(0,[z0,z1,z69,z2,z5,z349])],[(0,[z0,z1,z2,z4,z5,z1363]),(0,[z0,z1364,z1,z2,z4,z6]),(0,[z360,z1,z503,z2,z4,z5])],[(0,[z0,z1,z2,z4,z239,z6]),(0,[z0,z1,z2,z4,z111,z6])],[(0,[z0,z1,z2,z27,z587,z5]),(0,[z78,z1,z307,z2,z20,z5]),(0,[z0,z1,z522,z4,z24,z6]),(0,[z0,z1,z2,z133,z43,z6]),(0,[z0,z1,z2,z4,z5,z1365])],[(0,[z0,z1,z2,z4,z1366,z6]),(0,[z0,z1,z2,z4,z1367,z6]),(0,[z0,z1,z2,z22,z20,z5]),(0,[z54,z1,z2,z4,z140,z16]),(1,[z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z5,z122,z212]),(0,[z0,z1,z27,z4,z43,z24])],[(0,[z64,z52,z2,z4,z5,z6]),(0,[z197,z1,z2,z4,z158,z6]),(0,[z0,z1,z2,z4,z358,z18]),(0,[z0,z1,z2,z4,z1368,z6]),(0,[z0,z1,z2,z4,z5,z1369]),(0,[z0,z1,z2,z24,z349,z6]),(0,[z0,z1,z135,z2,z119,z5]),(0,[z0,z1,z2,z43,z349,z18]),(0,[z0,z13,z1,z4,z255,z26]),(0,[z0,z1,z2,z4,z5,z1370]),(0,[z0,z853,z2,z27,z4,z5])],[(0,[z0,z1,z2,z1371,z4,z6]),(0,[z0,z1,z2,z4,z5,z120]),(0,[z0,z1,z2,z4,z1372,z6]),(0,[z0,z1,z245,z2,z4,z5]),(0,[z0,z1,z2,z4,z1373,z5])],[(0,[z0,z1,z2,z116,z43,z6]),(0,[z0,z1,z2,z27,z664,z5]),(0,[z0,z96,z14,z2,z112,z5]),(0,[z0,z17,z14,z2,z4,z79]),(0,[z0,z1,z245,z2,z70,z5]),(0,[z0,z1,z2,z864,z5,z6])],[(0,[z0,z1,z2,z1374,z4,z5]),(0,[z0,z1,z2,z4,z5,z1375]),(0,[z0,z1,z2,z1376,z4,z5]),(0,[z0,z1,z2,z4,z593,z83])],[(0,[z0,z1,z2,z4,z5,z1377]),(0,[z0,z1,z2,z4,z5,z1378]),(0,[z0,z1,z2,z4,z5,z1379]),(0,[z0,z1,z2,z4,z1380,z6]),(0,[z0,z1,z8,z124,z4,z6]),(0,[z0,z1,z2,z345,z5,z26]),(0,[z0,z1,z2,z4,z1381,z5]),(0,[z65,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z572,z79,z6]),(0,[z0,z1,z135,z4,z43,z18]),(0,[z0,z1,z60,z4,z355,z18]),(0,[z0,z1,z2,z4,z291,z18]),(0,[z0,z1,z14,z2,z595,z5])],[(0,[z0,z1,z2,z1382,z4,z5]),(1,[z52,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z581]),(0,[z0,z1,z110,z4,z178,z5]),(0,[z0,z1383,z2,z4,z5,z6]),(0,[z0,z1,z2,z119,z112,z5]),(0,[z0,z1,z2,z4,z5,z1384])],[(0,[z64,z1,z110,z4,z5,z410]),(0,[z63,z1,z2,z27,z106,z5]),(0,[z0,z1,z2,z1385,z5,z6]),(0,[z0,z1,z2,z4,z255,z6])],[(0,[z0,z1,z2,z4,z1386,z6]),(0,[z0,z1,z2,z1387,z5,z6]),(0,[z0,z52,z23,z4,z5,z6]),(0,[z0,z1,z1388,z2,z4,z5]),(0,[z246,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1389,z6]),(0,[z63,z1,z2,z106,z24,z6]),(0,[z0,z1,z2,z1390,z5,z6]),(0,[z0,z1,z2,z1391,z4,z5]),(0,[z0,z167,z2,z4,z5,z173])],[(0,[z78,z1,z2,z27,z20,z5]),(0,[z0,z1,z2,z4,z5,z1392]),(0,[z0,z1,z2,z1393,z5,z6]),(0,[z55,z366,z102,z4,z5,z6]),(0,[z0,z1,z121,z2,z119,z5]),(0,[z0,z1,z2,z4,z5,z1394]),(0,[z0,z1,z14,z2,z4,z1316])]],
   [[(0,[z0,z1,z2,z4,z1395,z6]),(0,[z101,z0,z1,z221,z27,z5]),(0,[z1396,z0,z1,z2,z119,z5])],[(0,[z49,z50,z2,z27,z4,z5]),(0,[z0,z1397,z2,z4,z5,z6]),(0,[z644,z1,z2,z20,z5,z6]),(0,[z0,z1,z2,z4,z43,z564]),(0,[z366,z1,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z143,z6]),(0,[z0,z1,z2,z4,z5,z1398]),(1,[z246,z1,z2,z27,z5]),(0,[z0,z1,z227,z4,z178,z5])],[(0,[z0,z1,z386,z4,z5,z87]),(0,[z0,z2,z4,z5,z40,z741])],[(0,[z0,z455,z1,z14,z2,z4]),(0,[z0,z1,z2,z4,z1399,z6]),(0,[z0,z1,z2,z284,z5,z581]),(0,[z15,z1,z2,z4,z24,z44]),(0,[z0,z1,z2,z4,z1400,z6]),(0,[z65,z0,z2,z9,z5,z26]),(0,[z0,z246,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z319,z26]),(0,[z0,z152,z1,z27,z4,z24])],[(0,[z0,z1,z2,z4,z5,z1401]),(0,[z0,z1,z2,z4,z305,z18]),(0,[z101,z0,z1,z21,z5,z26]),(0,[z0,z1,z2,z4,z1402,z5]),(0,[z0,z1,z2,z4,z5,z1403]),(0,[z0,z875,z2,z27,z4,z5])],[(0,[z0,z1,z2,z4,z5,z812]),(0,[z0,z1,z2,z4,z5,z1404]),(0,[z0,z1,z2,z1405,z5,z6]),(0,[z159,z1,z2,z4,z51,z6]),(0,[z0,z1,z679,z2,z27,z5]),(0,[z0,z1,z2,z27,z81,z5]),(0,[z0,z1,z245,z2,z5,z122])],[(0,[z0,z1,z2,z4,z529,z87]),(0,[z0,z46,z455,z2,z4,z6]),(0,[z0,z1,z2,z1406,z4,z5]),(0,[z0,z1,z548,z4,z24,z6]),(0,[z0,z96,z2,z112,z5,z18]),(0,[z101,z0,z1,z21,z24,z6]),(0,[z0,z1,z14,z135,z4,z43])],[(0,[z0,z1,z48,z4,z5,z374]),(0,[z0,z1,z1407,z4,z5,z6]),(0,[z0,z1,z1343,z2,z315,z5]),(0,[z0,z1,z2,z1408,z5,z6]),(0,[z0,z1,z2,z4,z24,z188])],[(0,[z0,z1,z2,z1409,z5,z6]),(0,[z0,z50,z1,z2,z119,z5]),(0,[z0,z1,z2,z119,z20,z5]),(0,[z0,z1,z1410,z2,z4,z5]),(0,[z55,z0,z102,z27,z4,z5]),(0,[z0,z1,z2,z2,z119,z5])],[(0,[z0,z1,z2,z4,z5,z1411]),(0,[z0,z1,z2,z4,z158,z6]),(0,[z0,z1,z2,z4,z5,z1412])],[(0,[z86,z157,z2,z4,z5,z18]),(0,[z0,z1,z2,z320,z5,z26]),(0,[z313,z1,z2,z4,z5,z18])],[(0,[z0,z195,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z289,z24]),(0,[z0,z1,z2,z4,z5,z1413]),(0,[z0,z1,z2,z4,z32,z83])],[(0,[z0,z1,z2,z315,z5,z374]),(0,[z0,z1,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z5,z1414]),(0,[z101,z0,z1,z2,z27,z43]),(0,[z0,z1,z2,z4,z43,z18]),(0,[z0,z1,z4,z5,z471,z26])],[(0,[z134,z1,z2,z106,z5,z6]),(0,[z0,z1,z2,z4,z166,z5]),(0,[z0,z46,z2,z4,z728,z6])],[(0,[z0,z1,z2,z27,z364,z5]),(0,[z15,z1,z2,z345,z5,z44]),(0,[z0,z1,z60,z4,z291,z18])],[(0,[z209,z1,z23,z332,z5,z6]),(0,[z0,z1,z110,z4,z24,z26]),(0,[z0,z1,z307,z2,z320,z5]),(0,[z0,z1,z171,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z4,z172,z6]),(0,[z283,z1,z2,z27,z106,z5]),(0,[z125,z1,z191,z4,z126,z6]),(0,[z0,z1,z2,z4,z140,z26]),(0,[z0,z1,z2,z260,z5,z26])],[(0,[z1,z23,z4,z20,z24,z6]),(0,[z0,z1,z191,z4,z5,z1415]),(0,[z0,z1,z2,z345,z32,z5]),(0,[z0,z108,z14,z2,z4,z5])],[(0,[z0,z1,z2,z117,z529,z6]),(0,[z0,z52,z2,z4,z5,z26]),(0,[z0,z52,z2,z27,z4,z5]),(0,[z0,z1,z558,z4,z24,z6]),(0,[z156,z0,z2,z4,z5,z339]),(0,[z246,z1,z2,z5,z122,z6]),(0,[z0,z1,z2,z27,z555,z43]),(0,[z0,z1,z2,z1416,z4,z5])],[(0,[z0,z1,z2,z332,z5,z26]),(0,[z0,z1,z2,z949,z5,z6]),(0,[z241,z1,z110,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1417]),(0,[z0,z177,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z99,z26]),(0,[z0,z1,z2,z119,z5,z6]),(0,[z0,z1,z1418,z2,z4,z5]),(0,[z0,z1,z2,z4,z1419,z6])],[(0,[z0,z1,z2,z1420,z4,z5]),(0,[z63,z1,z2,z839,z5,z6]),(0,[z699,z0,z2,z9,z5,z6]),(0,[z15,z1,z666,z2,z4,z5]),(0,[z0,z1,z1292,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z180]),(0,[z0,z1,z2,z27,z24,z280])],[(0,[z0,z1,z2,z4,z5,z1421]),(0,[z0,z1,z2,z4,z5,z1422]),(0,[z0,z1,z2,z4,z5,z286]),(0,[z0,z1,z2,z1423,z5,z6]),(0,[z101,z0,z1,z4,z178,z5]),(0,[z271,z0,z1,z4,z178,z5])],[(0,[z366,z1,z25,z4,z5,z6]),(0,[z0,z222,z25,z4,z5,z323]),(0,[z0,z1,z1424,z2,z4,z5]),(0,[z0,z265,z2,z4,z5,z40]),(0,[z0,z1,z4,z24,z571,z6])],[(0,[z1,z2,z4,z839,z5,z6])],[(0,[z0,z1,z1425,z4,z5,z6]),(0,[z0,z1,z2,z4,z1426,z6]),(0,[z0,z1,z2,z9,z224,z5]),(0,[z0,z167,z2,z4,z5,z40])],[(0,[z0,z285,z2,z4,z79,z6]),(0,[z0,z1,z1427,z2,z4,z5]),(0,[z0,z1,z2,z4,z926,z6])],[(0,[z0,z1,z2,z27,z615,z5]),(0,[z0,z1,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z1428,z6]),(0,[z0,z1,z2,z1429,z119,z5])],[(0,[z0,z1,z2,z4,z434,z581]),(0,[z0,z1,z1424,z2,z493,z5]),(0,[z0,z1,z1430,z2,z4,z5]),(0,[z0,z1,z60,z2,z119,z5])],[(0,[z0,z1,z2,z27,z702,z5]),(0,[z0,z1,z2,z4,z57,z18]),(0,[z0,z2,z27,z9,z230,z5])],[(0,[z197,z1,z2,z4,z5,z6]),(0,[z15,z1,z2,z320,z5,z44]),(0,[z0,z1,z2,z1431,z4,z5]),(0,[z0,z1,z245,z2,z27,z5])],[(0,[z483,z50,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1432,z6]),(0,[z0,z1,z1255,z2,z27,z5]),(0,[z0,z2,z982,z4,z5,z6]),(0,[z0,z1,z4,z5,z1179,z18]),(0,[z0,z1,z14,z2,z4,z738])],[(0,[z0,z1,z2,z4,z5,z1433]),(0,[z0,z274,z1,z2,z4,z18]),(0,[z0,z1,z1434,z2,z4,z5]),(0,[z0,z299,z1,z4,z5,z26]),(0,[z0,z1,z2,z4,z5,z1435]),(0,[z0,z1,z60,z4,z43,z18])]],
   [[(0,[z0,z1,z2,z4,z5,z1436]),(0,[z0,z1,z2,z4,z1437,z18])],[(0,[z0,z1,z2,z4,z1438,z6]),(0,[z0,z195,z2,z4,z5,z155]),(0,[z0,z1,z2,z4,z1439,z6]),(0,[z0,z2,z987,z4,z5,z6])],[(0,[z0,z1440,z1,z2,z4,z6]),(0,[z0,z342,z2,z4,z5,z18]),(0,[z0,z1,z2,z1441,z5,z6]),(0,[z0,z163,z2,z4,z128,z40]),(0,[z0,z13,z1,z4,z43,z26]),(0,[z0,z1,z2,z27,z5,z553])],[(0,[z0,z1,z307,z2,z4,z24]),(0,[z0,z1,z387,z2,z27,z5]),(0,[z0,z1,z14,z2,z5,z363]),(0,[z0,z1,z2,z1442,z260,z5]),(0,[z0,z1,z1443,z2,z4,z5]),(0,[z0,z1,z2,z4,z443,z323]),(0,[z0,z152,z1,z4,z24,z18]),(0,[z0,z1,z61,z2,z4,z151])],[(0,[z0,z1,z386,z4,z1026,z6]),(0,[z0,z1,z2,z5,z1187,z252]),(0,[z0,z1,z4,z43,z470,z6]),(0,[z0,z1,z2,z4,z1087,z5])],[(0,[z0,z1,z1444,z4,z5,z6]),(0,[z125,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z185,z133,z6]),(0,[z54,z568,z1,z2,z4,z5]),(0,[z246,z177,z2,z4,z5,z6]),(0,[z101,z246,z1,z21,z5,z6]),(0,[z0,z1,z2,z4,z5,z212]),(0,[z0,z1,z2,z185,z901,z6])],[(0,[z157,z23,z102,z4,z5,z6]),(0,[z313,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1415]),(0,[z0,z1,z2,z4,z1445,z6]),(0,[z0,z685,z2,z4,z5,z40]),(0,[z0,z222,z2,z260,z5,z6]),(0,[z0,z1,z2,z4,z5,z1446]),(0,[z0,z1,z2,z4,z5,z1447]),(0,[z0,z1,z2,z4,z557,z24]),(0,[z0,z1,z2,z27,z4,z1448])],[(0,[z0,z1,z2,z4,z24,z87]),(0,[z0,z451,z2,z4,z79,z6]),(0,[z0,z1449,z2,z4,z5,z6]),(0,[z0,z1,z2,z1450,z4,z5])],[(0,[z0,z1,z2,z4,z1309,z6]),(0,[z0,z1,z2,z4,z1451,z5]),(0,[z0,z1,z121,z2,z27,z24]),(0,[z0,z1,z2,z462,z4,z24])],[(0,[z0,z1,z2,z4,z1452,z6]),(0,[z0,z1,z2,z1453,z5,z6]),(0,[z0,z195,z2,z4,z32,z6]),(0,[z0,z1,z2,z976,z116,z5]),(0,[z0,z1,z941,z2,z4,z5]),(0,[z0,z1,z2,z272,z158,z6]),(0,[z55,z0,z14,z102,z4,z5]),(0,[z0,z1,z2,z4,z962,z6]),(0,[z0,z1,z14,z2,z281,z5]),(0,[z0,z1,z2,z4,z974,z32])],[(0,[z15,z0,z1,z2,z119,z5]),(0,[z322,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z260,z5,z130]),(0,[z55,z0,z102,z260,z5,z6]),(0,[z0,z1,z1454,z2,z4,z5]),(0,[z0,z1,z2,z4,z43,z98]),(0,[z0,z163,z2,z4,z145,z40]),(0,[z1455,z0,z2,z4,z5,z18])],[(0,[z0,z1,z386,z4,z36,z6]),(0,[z86,z0,z1,z2,z119,z5]),(0,[z0,z1,z503,z2,z27,z5]),(0,[z0,z1,z2,z27,z4,z358])],[(0,[z0,z46,z14,z2,z4,z71]),(0,[z0,z1,z2,z27,z4,z145])],[(0,[z0,z17,z1,z124,z4,z6]),(0,[z15,z0,z1,z2,z4,z145]),(0,[z0,z1,z2,z4,z5,z1456]),(0,[z0,z1,z2,z27,z4,z24])],[(0,[z0,z1,z2,z4,z5,z1457])],[(0,[z0,z1247,z2,z4,z5,z6]),(0,[z0,z1,z2,z1458,z5,z6]),(0,[z0,z1,z2,z367,z5,z26])]],
   [[(0,[z0,z1459,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1460]),(0,[z0,z1,z2,z1461,z5,z6]),(0,[z101,z0,z1,z88,z21,z5])],[(0,[z157,z2,z386,z4,z5,z6]),(0,[z0,z1,z2,z117,z5,z26]),(0,[z0,z1,z2,z1462,z5,z6]),(0,[z0,z1,z2,z4,z1463,z6]),(0,[z0,z1,z2,z464,z9,z5]),(0,[z0,z1,z2,z1464,z5,z6]),(0,[z0,z1,z4,z5,z26,z118]),(0,[z0,z46,z2,z4,z626,z6])],[],[(0,[z0,z1465,z2,z4,z5,z6]),(0,[z0,z2,z4,z5,z1466,z6]),(0,[z0,z1,z2,z119,z43,z18])],[(0,[z0,z1,z2,z4,z43,z120]),(0,[z0,z1,z171,z2,z27,z5]),(0,[z0,z1,z419,z2,z80,z6]),(0,[z0,z1,z8,z85,z2,z93])],[(0,[z0,z1,z124,z4,z43,z6]),(0,[z0,z2,z4,z1242,z43,z6]),(0,[z0,z1,z2,z4,z30,z18])],[(0,[z0,z1,z2,z4,z1467,z5]),(0,[z78,z1,z2,z20,z5,z18]),(0,[z54,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z58,z27,z5]),(0,[z0,z1,z2,z4,z341,z83]),(0,[z0,z1,z2,z185,z186,z277])],[(0,[z0,z52,z2,z332,z5,z6]),(0,[z64,z1,z110,z4,z24,z6]),(0,[z0,z1,z2,z27,z160,z5])],[(0,[z42,z1,z2,z27,z4,z51]),(0,[z366,z1,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z1468]),(0,[z0,z1,z2,z4,z24,z476])],[(0,[z0,z1,z2,z1469,z5,z6]),(0,[z0,z1,z1470,z2,z4,z5]),(0,[z209,z1,z23,z4,z5,z581]),(0,[z0,z1,z2,z4,z5,z1471]),(0,[z0,z1,z1292,z2,z27,z5])],[(0,[z0,z1472,z2,z4,z5,z6]),(0,[z39,z0,z2,z4,z5,z339]),(0,[z0,z1,z2,z4,z1473,z6]),(0,[z246,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z178,z43]),(0,[z0,z1,z4,z5,z1179,z6]),(0,[z210,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z119,z186,z5]),(0,[z0,z1,z8,z14,z2,z93])],[(0,[z0,z1,z2,z27,z4,z36]),(0,[z64,z1,z2,z332,z5,z6]),(0,[z0,z195,z2,z4,z51,z6]),(0,[z0,z1,z2,z4,z5,z1474]),(0,[z0,z1,z2,z4,z5,z1475]),(0,[z0,z1,z2,z1476,z5,z6])],[(0,[z0,z1,z2,z1477,z4,z5]),(0,[z0,z1,z1255,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z251]),(0,[z0,z1,z14,z2,z260,z5]),(0,[z0,z1,z2,z4,z5,z1478]),(0,[z0,z1,z2,z572,z24,z6]),(0,[z0,z1,z2,z4,z24,z494]),(0,[z1002,z1,z2,z4,z5,z6])],[(0,[z197,z1,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z5,z1479]),(0,[z0,z1,z1480,z2,z4,z5])],[(0,[z0,z342,z2,z4,z5,z6]),(0,[z78,z1,z2,z839,z5,z6]),(0,[z78,z1,z2,z464,z20,z5]),(0,[z1481,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z79,z494]),(0,[z0,z1,z1044,z21,z5,z6]),(0,[z0,z152,z1,z4,z24,z92]),(0,[z0,z1,z2,z5,z349,z26])],[(0,[z63,z1,z2,z106,z5,z26]),(0,[z0,z296,z2,z116,z5,z6]),(0,[z125,z1,z14,z2,z4,z126]),(0,[z360,z1,z2,z4,z5,z16]),(0,[z0,z1,z655,z4,z43,z6]),(0,[z0,z1,z2,z4,z145,z226]),(0,[z0,z1,z2,z216,z62,z5]),(0,[z0,z1,z2,z4,z5,z1482]),(0,[z0,z1,z61,z2,z4,z7])]],
   [[(0,[z1,z2,z4,z51,z754,z6]),(0,[z0,z1,z2,z4,z24,z323]),(0,[z0,z1,z2,z717,z5,z323]),(0,[z0,z1,z2,z4,z1483,z5])],[(0,[z0,z1,z2,z4,z1448,z6]),(0,[z101,z0,z1,z1044,z5,z6]),(0,[z0,z1,z121,z2,z178,z5]),(0,[z0,z1,z4,z24,z26,z18]),(0,[z0,z1,z2,z4,z24,z1166]),(0,[z0,z1,z2,z1405,z43,z6]),(0,[z0,z1,z512,z4,z5,z18])],[(1,[z751,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z564]),(0,[z0,z982,z102,z4,z5,z6]),(0,[z0,z1,z2,z801,z5,z18]),(0,[z0,z1,z2,z4,z5,z1484])],[(0,[z0,z1,z2,z949,z4,z5]),(0,[z0,z1,z2,z4,z1485,z6]),(0,[z0,z1,z2,z227,z9,z5]),(0,[z0,z1,z2,z119,z4,z5]),(0,[z0,z1,z2,z4,z5,z1486]),(0,[z0,z1,z2,z43,z960,z6])],[(0,[z0,z751,z2,z4,z5,z6]),(0,[z444,z1,z2,z4,z126,z6]),(0,[z0,z1,z2,z4,z1487,z6]),(0,[z0,z1,z2,z119,z70,z5])],[(0,[z0,z1,z386,z4,z1225,z6]),(0,[z42,z1,z2,z4,z51,z18])],[(0,[z0,z342,z2,z4,z239,z6]),(0,[z0,z1,z1488,z2,z4,z5]),(0,[z0,z1,z85,z2,z4,z43]),(0,[z0,z1,z2,z119,z5,z349])],[(0,[z0,z1,z2,z4,z1489,z6]),(0,[z0,z1,z2,z1490,z5,z6]),(0,[z0,z296,z2,z4,z5,z564]),(0,[z283,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z24,z66]),(0,[z0,z1,z2,z4,z355,z6])],[(0,[z0,z1,z2,z272,z43,z6]),(0,[z0,z1,z2,z4,z5,z190]),(0,[z0,z1,z2,z27,z4,z355])],[(0,[z0,z1,z2,z27,z162,z20]),(0,[z0,z1,z677,z4,z24,z6]),(0,[z0,z1491,z1,z2,z4,z5]),(0,[z0,z682,z2,z112,z5,z6]),(0,[z0,z1,z1492,z4,z5,z6]),(0,[z0,z1,z121,z2,z27,z193])],[(0,[z328,z1,z2,z4,z392,z6])],[(0,[z0,z1,z2,z4,z894,z6]),(0,[z0,z1,z2,z4,z5,z1493]),(0,[z0,z1,z124,z4,z5,z1494]),(0,[z0,z1,z2,z4,z1495,z6]),(0,[z1496,z0,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z491,z534]),(0,[z0,z13,z1,z4,z30,z26])],[(0,[z0,z1,z2,z1497,z5,z6]),(0,[z0,z1,z2,z4,z5,z1498]),(0,[z0,z195,z2,z4,z5,z26]),(0,[z0,z195,z2,z27,z4,z5]),(0,[z0,z421,z2,z9,z5,z6]),(0,[z0,z46,z2,z4,z71,z26]),(0,[z0,z1,z2,z4,z62,z226]),(0,[z0,z108,z2,z21,z5,z6])],[(0,[z0,z1,z14,z2,z4,z5]),(0,[z0,z1499,z1,z2,z5,z6]),(0,[z0,z1,z619,z4,z5,z18]),(0,[z313,z177,z2,z4,z5,z6])],[(0,[z0,z1,z2,z117,z36,z6]),(0,[z0,z1,z2,z4,z36,z26]),(0,[z0,z1,z191,z4,z305,z6]),(0,[z1,z2,z27,z164,z106,z5]),(0,[z0,z1,z2,z1500,z4,z5]),(0,[z0,z163,z2,z216,z5,z40]),(0,[z0,z1,z2,z27,z4,z193])],[(0,[z0,z1,z2,z4,z1350,z6]),(0,[z0,z1,z2,z27,z4,z143]),(0,[z0,z1,z14,z2,z4,z128]),(0,[z0,z177,z2,z4,z43,z6]),(0,[z0,z1,z2,z119,z43,z6]),(0,[z0,z1,z2,z4,z32,z359]),(0,[z0,z1,z2,z27,z550,z5])]],
   [[(0,[z0,z1,z1501,z2,z4,z5]),(0,[z0,z1,z2,z4,z1502,z6]),(0,[z0,z1,z2,z4,z1503,z6]),(0,[z0,z1,z2,z4,z43,z180]),(0,[z0,z1,z14,z2,z5,z349]),(0,[z0,z1,z2,z119,z5,z122]),(0,[z0,z1,z113,z2,z4,z306])],[(0,[z0,z1,z2,z4,z43,z286]),(0,[z0,z1,z2,z4,z30,z6])],[(0,[z0,z1,z135,z4,z305,z6]),(0,[z0,z296,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z1504]),(0,[z0,z611,z1,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1505]),(0,[z1354,z1,z14,z2,z4,z5]),(0,[z1355,z1,z14,z2,z4,z5])],[(0,[z0,z1,z2,z1506,z5,z6]),(0,[z0,z1,z2,z493,z24,z6]),(0,[z0,z1,z2,z4,z1507,z5]),(1,[z0,z1,z2,z119,z43])],[(0,[z0,z1,z2,z4,z5,z374]),(0,[z86,z274,z157,z2,z4,z6]),(0,[z366,z1,z2,z4,z5,z6]),(0,[z0,z1,z203,z2,z1469,z5]),(0,[z0,z1,z2,z284,z5,z18]),(0,[z0,z1,z2,z4,z1508,z6]),(0,[z0,z1,z14,z2,z133,z5]),(0,[z0,z1,z2,z4,z5,z1509]),(0,[z0,z1,z2,z1510,z4,z5]),(0,[z0,z1,z2,z1307,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1511]),(0,[z0,z1,z2,z4,z75,z26]),(0,[z0,z1,z2,z1195,z24,z6])],[(0,[z0,z1,z2,z1512,z4,z5]),(0,[z63,z1,z2,z106,z5,z188]),(0,[z0,z195,z2,z4,z126,z6]),(0,[z0,z1,z191,z4,z43,z6]),(0,[z0,z1,z2,z4,z358,z6]),(0,[z0,z1,z2,z4,z5,z913]),(0,[z0,z17,z2,z27,z4,z79]),(0,[z0,z1,z2,z43,z349,z6]),(0,[z0,z1,z2,z718,z5,z18])],[(0,[z576,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1513]),(0,[z310,z1,z23,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1514]),(0,[z549,z0,z1,z21,z5,z6]),(0,[z0,z646,z1,z2,z27,z5]),(0,[z0,z1515,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z917]),(0,[z1516,z0,z1,z2,z4,z5]),(0,[z0,z1,z779,z2,z572,z5]),(0,[z0,z163,z2,z4,z5,z40]),(0,[z0,z1,z2,z4,z24,z19]),(0,[z0,z1,z2,z4,z1315,z6])],[(0,[z0,z1,z2,z4,z5,z1517]),(0,[z0,z1,z2,z4,z1518,z6])],[(0,[z0,z1,z2,z4,z5,z1519]),(0,[z0,z1,z2,z4,z1520,z6]),(0,[z125,z1,z2,z4,z181,z6]),(0,[z197,z1,z2,z4,z43,z6]),(0,[z0,z1,z2,z4,z158,z251]),(0,[z0,z1,z1521,z2,z4,z5])],[(0,[z1522,z0,z1,z2,z4,z5]),(0,[z0,z1,z4,z625,z24,z6]),(0,[z0,z1,z2,z119,z71,z5]),(0,[z0,z1,z61,z2,z4,z334]),(0,[z0,z1,z135,z4,z43,z6]),(0,[z0,z1,z2,z4,z291,z6]),(0,[z0,z1,z2,z119,z1523,z5]),(0,[z0,z1,z14,z2,z5,z122])],[(0,[z0,z1,z14,z23,z4,z24]),(0,[z0,z1,z2,z4,z5,z1524]),(0,[z642,z0,z1,z2,z4,z32]),(0,[z0,z1,z2,z4,z1067,z6])],[(0,[z49,z1,z23,z4,z24,z6]),(0,[z740,z0,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z1525,z6]),(0,[z0,z1,z2,z27,z320,z5]),(0,[z0,z1,z2,z272,z5,z251]),(0,[z0,z1,z2,z4,z1526,z6]),(0,[z0,z1,z2,z4,z5,z1527]),(0,[z0,z1,z2,z990,z5,z18])],[(0,[z0,z1,z1528,z4,z5,z6]),(1,[z0,z1,z2,z1051,z5])],[(0,[z0,z1,z2,z4,z1529,z6]),(0,[z0,z1,z2,z4,z1324,z6])],[(0,[z0,z1,z48,z4,z24,z6]),(0,[z0,z1,z2,z20,z224,z5]),(0,[z0,z1,z1443,z2,z272,z5]),(0,[z246,z1,z14,z2,z4,z5])]],
   [[(0,[z0,z1,z1530,z2,z4,z5]),(0,[z0,z1,z2,z20,z5,z188]),(0,[z0,z1,z2,z4,z32,z564]),(0,[z266,z1,z2,z4,z126,z6]),(0,[z39,z0,z481,z2,z4,z5]),(0,[z0,z1,z2,z1531,z5,z6]),(0,[z0,z1,z60,z4,z24,z18])],[(0,[z0,z274,z1,z2,z27,z4]),(0,[z0,z52,z2,z4,z5,z581]),(0,[z0,z1,z2,z4,z172,z252]),(0,[z0,z1,z2,z4,z1532,z6]),(0,[z0,z222,z14,z25,z4,z5]),(0,[z0,z1,z2,z4,z43,z212])],[(0,[z0,z1,z2,z721,z4,z5]),(0,[z0,z1,z2,z4,z5,z391]),(0,[z0,z1,z2,z216,z43,z6])],[(0,[z0,z1,z2,z4,z305,z6]),(0,[z0,z1,z2,z106,z5,z413]),(0,[z0,z1,z1533,z2,z4,z5]),(0,[z39,z0,z2,z4,z5,z347]),(0,[z0,z1,z2,z4,z946,z24])],[(0,[z0,z1,z2,z315,z24,z6]),(0,[z0,z1,z2,z949,z5,z252]),(0,[z0,z2,z987,z112,z5,z6]),(0,[z1095,z1,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z24,z423]),(0,[z0,z1,z4,z43,z24,z18]),(0,[z0,z1,z8,z2,z93,z26])],[(0,[z0,z1,z2,z1534,z5,z6]),(0,[z0,z1,z1535,z4,z5,z6]),(0,[z0,z1,z2,z4,z1536,z6]),(0,[z0,z1,z2,z4,z5,z1537]),(0,[z0,z96,z2,z112,z5,z6]),(0,[z0,z1086,z2,z27,z4,z5])],[(0,[z0,z1,z14,z2,z315,z5]),(0,[z0,z195,z8,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z1538]),(0,[z0,z222,z25,z4,z5,z18]),(0,[z0,z1,z2,z4,z491,z83]),(0,[z0,z1,z2,z4,z1094,z26])],[(0,[z0,z1,z2,z4,z5,z1539]),(0,[z0,z1,z2,z4,z5,z268]),(0,[z0,z1,z2,z4,z1540,z6]),(0,[z0,z1,z2,z4,z237,z391])],[(0,[z0,z1,z2,z117,z5,z87]),(0,[z0,z1,z2,z4,z5,z1541]),(0,[z684,z1,z2,z4,z5,z16]),(0,[z0,z1,z2,z1542,z5,z6]),(0,[z0,z1,z2,z27,z5,z19]),(0,[z0,z1,z2,z4,z24,z92])],[(0,[z86,z157,z2,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1543]),(0,[z0,z1,z2,z4,z5,z1544]),(0,[z0,z1,z294,z2,z27,z24]),(0,[z0,z1,z2,z4,z1545,z5]),(0,[z383,z0,z1,z2,z119,z5])],[(0,[z0,z1,z2,z4,z5,z1546]),(0,[z0,z1,z110,z2,z119,z5]),(0,[z0,z2,z4,z728,z5,z6]),(0,[z0,z1,z2,z27,z367,z5]),(0,[z0,z1,z2,z4,z1547,z6]),(0,[z0,z1,z2,z119,z5,z259])],[(0,[z0,z1,z2,z4,z43,z6]),(0,[z0,z1,z386,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z1548]),(0,[z0,z1,z2,z162,z4,z26]),(0,[z101,z0,z1,z21,z75,z6]),(0,[z0,z1,z119,z5,z26,z18]),(0,[z0,z1,z2,z1105,z5,z26])],[(0,[z0,z1,z2,z4,z434,z18]),(0,[z0,z1,z2,z464,z4,z24]),(0,[z0,z1,z2,z9,z178,z5]),(0,[z0,z1,z2,z4,z5,z226]),(0,[z101,z0,z1,z21,z99,z6])],[(1,[z0,z1,z2,z949,z5]),(0,[z107,z0,z2,z4,z5,z339]),(0,[z197,z1,z2,z4,z5,z251]),(0,[z0,z1,z2,z4,z1549,z6]),(1,[z0,z108,z2,z27,z5]),(0,[z0,z1,z2,z4,z5,z1550])],[(0,[z0,z1,z2,z4,z5,z1551]),(0,[z86,z455,z157,z2,z4,z6])],[(0,[z0,z1,z2,z4,z529,z18]),(0,[z0,z1,z203,z2,z4,z5]),(0,[z0,z1,z2,z4,z239,z268]),(0,[z0,z1,z429,z4,z43,z6]),(0,[z0,z1,z14,z2,z4,z75]),(0,[z0,z1,z189,z2,z4,z306]),(0,[z0,z1,z2,z119,z62,z5]),(0,[z0,z1,z2,z4,z759,z6])]],
   [[(0,[z0,z1,z2,z284,z5,z6]),(0,[z0,z1552,z1,z2,z4,z6]),(0,[z0,z108,z2,z4,z24,z6])],[(0,[z366,z1,z2,z4,z158,z6]),(0,[z0,z1,z108,z2,z27,z5]),(0,[z101,z0,z1,z2,z224,z5])],[(0,[z0,z1,z2,z4,z5,z410]),(0,[z0,z1,z14,z2,z4,z239]),(0,[z0,z222,z982,z4,z5,z6]),(0,[z0,z1,z2,z27,z216,z5]),(0,[z0,z1,z1553,z2,z4,z5]),(0,[z442,z1,z2,z4,z5,z396]),(0,[z0,z1,z14,z2,z27,z5]),(0,[z0,z1,z2,z4,z974,z83])],[(0,[z0,z1,z4,z1554,z5,z6]),(0,[z0,z1555,z2,z4,z5,z6]),(0,[z0,z376,z25,z4,z5,z6]),(0,[z0,z1,z2,z4,z443,z18]),(0,[z0,z1,z2,z27,z572,z5]),(0,[z0,z1,z14,z2,z4,z1333])],[(0,[z0,z1,z2,z4,z5,z1556]),(0,[z0,z638,z1,z4,z24,z6]),(0,[z366,z1,z2,z272,z5,z6]),(0,[z0,z1,z2,z4,z1557,z6]),(0,[z0,z1,z2,z708,z4,z5]),(0,[z0,z1,z2,z4,z5,z1558]),(0,[z0,z1,z2,z22,z4,z5]),(0,[z0,z177,z14,z2,z4,z5]),(0,[z0,z1,z2,z119,z24,z18]),(0,[z0,z1,z2,z781,z5,z18])],[(0,[z594,z0,z102,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1559]),(0,[z0,z1,z14,z2,z4,z30]),(0,[z0,z1,z2,z1142,z5,z6]),(0,[z77,z1,z2,z164,z4,z5])],[(0,[z0,z1560,z1,z2,z4,z5]),(0,[z0,z1,z14,z2,z284,z5]),(0,[z0,z1,z124,z4,z24,z6]),(0,[z0,z1,z2,z5,z1561,z6]),(0,[z0,z1,z1562,z2,z4,z5]),(0,[z0,z1,z2,z272,z358,z6]),(0,[z0,z1,z2,z102,z119,z5]),(0,[z0,z1,z2,z27,z4,z237]),(0,[z0,z1,z462,z70,z4,z5]),(0,[z0,z1,z2,z4,z5,z985]),(0,[z312,z0,z600,z2,z4,z5])],[(0,[z86,z751,z2,z4,z5,z6]),(0,[z0,z1,z2,z1442,z4,z5]),(0,[z0,z1,z2,z4,z5,z1563]),(0,[z0,z1,z2,z4,z5,z413])],[(0,[z49,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z284,z239,z6]),(0,[z64,z1,z110,z27,z4,z5]),(0,[z64,z1,z110,z4,z5,z26]),(0,[z0,z1,z2,z4,z43,z251]),(0,[z0,z74,z2,z112,z5,z6]),(0,[z0,z1,z2,z990,z5,z6]),(0,[z0,z1,z1430,z2,z4,z43])],[(0,[z0,z1,z1564,z2,z4,z5]),(0,[z0,z1,z2,z133,z24,z6]),(0,[z0,z1,z2,z119,z5,z16]),(0,[z65,z0,z2,z27,z9,z5]),(0,[z0,z1,z2,z4,z1565,z6]),(0,[z0,z1,z2,z1561,z24,z6]),(0,[z0,z1,z8,z2,z80,z6])],[(0,[z0,z1,z1566,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1567]),(0,[z0,z1,z2,z4,z1068,z6]),(0,[z0,z1,z2,z4,z43,z1379]),(0,[z0,z1,z2,z4,z341,z359]),(0,[z0,z1,z2,z227,z119,z5]),(0,[z0,z2,z1331,z4,z5,z6]),(0,[z0,z1,z1148,z27,z4,z5])],[(0,[z0,z1,z48,z4,z760,z6]),(0,[z0,z455,z1,z2,z27,z4]),(0,[z0,z296,z124,z4,z5,z6]),(0,[z0,z1,z2,z4,z57,z6]),(0,[z0,z799,z2,z4,z5,z6]),(0,[z0,z800,z2,z4,z5,z6])],[(0,[z0,z455,z1,z2,z4,z18]),(0,[z0,z1,z1568,z2,z4,z6]),(0,[z78,z1,z2,z162,z20,z6]),(0,[z54,z0,z1,z2,z4,z145]),(0,[z0,z1,z2,z4,z5,z1569]),(0,[z0,z1,z14,z2,z4,z99]),(0,[z0,z1,z88,z2,z4,z43]),(1,[z0,z1,z4,z5,z1179]),(0,[z0,z1,z8,z2,z119,z5]),(0,[z0,z1,z2,z4,z1570,z5])],[(0,[z0,z1,z2,z116,z24,z6]),(0,[z0,z1,z2,z4,z5,z1571]),(0,[z0,z1,z2,z572,z5,z26]),(0,[z0,z1,z245,z2,z21,z5]),(0,[z0,z1,z2,z59,z27,z5]),(0,[z0,z1,z1318,z2,z4,z43])],[(0,[z0,z274,z1,z2,z4,z6]),(0,[z0,z1,z2,z27,z537,z5]),(0,[z0,z469,z1,z4,z24,z6]),(0,[z0,z296,z2,z133,z5,z6]),(0,[z197,z1,z14,z2,z4,z5])],[(0,[z0,z1,z1572,z4,z5,z6]),(0,[z0,z1,z2,z4,z1437,z6]),(0,[z1,z2,z4,z5,z754,z6]),(0,[z0,z1,z2,z1258,z24,z6]),(0,[z0,z1,z294,z2,z321,z6]),(0,[z0,z1,z2,z1155,z5,z26])]],
   [[(0,[z0,z1,z2,z4,z5,z252]),(0,[z0,z1,z2,z4,z1573,z6]),(0,[z0,z1,z4,z43,z24,z6]),(0,[z0,z333,z2,z4,z5,z199]),(0,[z0,z1,z61,z2,z4,z417])],[(0,[z0,z1,z48,z4,z529,z6]),(0,[z0,z1,z1574,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z1575]),(0,[z0,z1,z2,z4,z5,z1494]),(0,[z0,z108,z2,z27,z5,z6]),(0,[z0,z1264,z2,z4,z24,z6])],[(0,[z0,z1,z386,z315,z5,z6]),(0,[z0,z1,z657,z4,z24,z6]),(0,[z0,z1,z2,z4,z1576,z6]),(0,[z0,z1,z2,z1577,z4,z5]),(0,[z0,z152,z1,z4,z24,z6]),(0,[z0,z1,z2,z1578,z4,z5]),(0,[z0,z1,z135,z4,z43,z180]),(0,[z0,z1,z2,z4,z5,z1579])],[(0,[z607,z0,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z5,z1580]),(0,[z101,z0,z1,z2,z119,z5]),(0,[z0,z1,z2,z4,z1050,z5])],[(0,[z101,z0,z1,z2,z227,z5]),(0,[z0,z1,z2,z4,z1168,z6]),(0,[z0,z1,z2,z4,z43,z190]),(0,[z266,z1,z2,z4,z213,z6])],[(0,[z0,z1,z2,z4,z36,z87]),(0,[z266,z1,z23,z4,z5,z6]),(0,[z0,z1,z1274,z2,z4,z5]),(0,[z0,z1,z174,z2,z27,z5]),(0,[z0,z1,z659,z4,z24,z6]),(0,[z0,z1,z2,z4,z1451,z43]),(0,[z0,z1175,z2,z27,z4,z5])],[(0,[z0,z1,z2,z315,z529,z6]),(0,[z1,z2,z672,z20,z5,z6]),(0,[z55,z0,z982,z4,z5,z6]),(0,[z0,z1,z2,z4,z224,z24]),(0,[z0,z1,z2,z119,z5,z199])],[(0,[z350,z0,z1,z2,z4,z5]),(0,[z0,z1,z23,z4,z178,z5]),(0,[z0,z46,z1,z124,z4,z6]),(0,[z197,z1,z2,z4,z358,z6]),(0,[z0,z1,z2,z4,z1581,z6]),(0,[z0,z1,z2,z4,z5,z1582]),(0,[z313,z1,z14,z2,z4,z5])],[(0,[z0,z1,z14,z2,z4,z529]),(0,[z1,z110,z890,z4,z5,z6]),(0,[z101,z313,z1,z21,z5,z6]),(0,[z0,z1,z2,z4,z193,z26]),(0,[z0,z1,z4,z5,z26,z1179]),(1,[z0,z1,z2,z901,z6])],[(0,[z0,z1,z1530,z2,z284,z5]),(0,[z1455,z0,z2,z4,z5,z6]),(0,[z0,z1,z1583,z2,z4,z5]),(0,[z0,z1,z2,z1584,z4,z5]),(0,[z0,z1,z14,z2,z272,z5])],[(0,[z0,z1,z2,z1585,z5,z6]),(0,[z209,z1,z23,z4,z5,z18])],[(0,[z0,z1,z2,z4,z5,z1586]),(0,[z0,z1,z2,z4,z1587,z6])],[(0,[z0,z1,z2,z4,z1588,z5]),(0,[z0,z1,z536,z2,z4,z26]),(0,[z0,z1,z2,z4,z5,z1589])],[(0,[z0,z1,z2,z4,z5,z1107]),(0,[z0,z1,z2,z1590,z4,z5])],[(0,[z101,z246,z1,z2,z27,z5]),(0,[z0,z1,z2,z4,z319,z476]),(0,[z0,z1,z2,z4,z5,z1179])],[(0,[z0,z1,z2,z4,z1591,z6]),(0,[z0,z1,z1592,z2,z4,z5]),(0,[z1593,z1,z2,z4,z5,z6]),(0,[z0,z1,z69,z2,z4,z43])]],
   [[(0,[z0,z1,z1594,z4,z5,z6]),(0,[z0,z1,z536,z2,z9,z6]),(0,[z205,z1,z2,z4,z5,z44]),(0,[z0,z1,z2,z4,z5,z1595]),(0,[z0,z1,z2,z4,z24,z18])],[(0,[z0,z1,z103,z2,z4,z43]),(0,[z0,z1,z645,z4,z24,z6]),(0,[z0,z1,z2,z1596,z5,z6])],[(0,[z0,z1,z2,z1597,z5,z6]),(0,[z15,z1,z202,z2,z4,z5]),(0,[z0,z1,z2,z4,z1598,z6]),(0,[z0,z1,z4,z5,z1599,z6]),(0,[z0,z1,z2,z27,z9,z43]),(0,[z0,z1,z2,z901,z93,z6])],[(0,[z0,z1,z2,z23,z119,z5]),(0,[z0,z1,z672,z4,z24,z6]),(0,[z0,z1,z2,z116,z5,z155]),(0,[z0,z1,z2,z1600,z4,z5]),(0,[z0,z163,z2,z4,z43,z40]),(0,[z0,z1,z232,z4,z43,z6]),(0,[z0,z611,z1,z4,z5,z26]),(0,[z0,z1,z2,z4,z5,z277]),(0,[z0,z1,z577,z2,z27,z5])],[(0,[z0,z1,z2,z4,z1601,z6]),(0,[z0,z1,z2,z4,z1602,z6]),(0,[z0,z1,z124,z4,z32,z6]),(0,[z0,z1,z2,z493,z5,z26]),(0,[z0,z163,z2,z4,z5,z516])],[(0,[z0,z1,z14,z386,z4,z5]),(0,[z0,z1,z2,z1603,z4,z5]),(0,[z78,z1,z2,z20,z5,z6]),(0,[z0,z1,z592,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z1604]),(0,[z0,z1,z14,z2,z493,z5]),(0,[z0,z1,z2,z27,z4,z1495])],[(0,[z0,z1,z2,z4,z172,z410]),(0,[z0,z1605,z1,z2,z4,z6]),(0,[z0,z1,z4,z676,z24,z6]),(0,[z0,z1,z14,z2,z43,z122]),(0,[z0,z1,z2,z4,z32,z317])],[(0,[z0,z1,z2,z27,z106,z5]),(0,[z0,z222,z25,z4,z143,z6])],[(0,[z0,z455,z1,z2,z4,z6]),(0,[z0,z1,z2,z1606,z5,z6]),(0,[z0,z1607,z1,z2,z4,z6]),(0,[z0,z1,z1608,z2,z4,z5]),(0,[z54,z1,z2,z4,z111,z16]),(0,[z0,z1,z2,z1600,z493,z5]),(0,[z0,z1,z245,z2,z4,z43])],[(0,[z0,z96,z2,z27,z112,z5]),(0,[z0,z1,z5,z349,z26,z18]),(0,[z0,z1,z69,z577,z4,z5])],[(0,[z0,z1,z2,z4,z5,z1609]),(0,[z0,z1,z2,z1317,z332,z5]),(0,[z246,z1,z2,z21,z5,z6]),(0,[z0,z1308,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1610])],[(0,[z0,z1,z1611,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z1612]),(0,[z0,z1,z1613,z4,z5,z6]),(0,[z0,z1,z2,z345,z5,z18]),(0,[z0,z152,z1,z4,z24,z190]),(0,[z0,z1,z2,z863,z5,z18]),(0,[z0,z1,z61,z2,z4,z62])],[(0,[z0,z296,z191,z4,z5,z6]),(0,[z0,z1,z2,z4,z62,z337]),(0,[z0,z1,z1614,z2,z4,z5])],[(0,[z0,z455,z195,z2,z4,z6]),(0,[z0,z1,z2,z4,z5,z932]),(0,[z78,z1,z536,z2,z20,z6]),(0,[z0,z1,z2,z4,z62,z111]),(0,[z65,z0,z2,z9,z5,z66])],[(0,[z0,z1,z1615,z4,z5,z6]),(0,[z0,z1,z1616,z2,z4,z5]),(0,[z0,z1,z2,z4,z145,z40])],[(0,[z0,z1,z2,z4,z5,z1617])]],
   [[(0,[z0,z1,z48,z27,z4,z5]),(0,[z0,z1,z48,z4,z5,z26]),(0,[z0,z1,z1327,z2,z332,z5]),(0,[z0,z1,z2,z4,z1618,z6]),(0,[z0,z1,z357,z2,z4,z62]),(0,[z0,z1,z4,z43,z26,z18]),(0,[z0,z1,z2,z5,z737,z18])],[(0,[z49,z50,z2,z4,z5,z18]),(0,[z0,z1,z2,z4,z5,z1619]),(0,[z0,z1620,z2,z4,z5,z6]),(0,[z0,z96,z2,z112,z43,z6]),(0,[z0,z1,z2,z27,z231,z5]),(0,[z0,z1,z2,z801,z5,z6]),(0,[z0,z1,z60,z4,z5,z1179]),(0,[z0,z1,z115,z4,z5,z18])],[(0,[z0,z1,z2,z464,z112,z5]),(0,[z0,z1,z14,z2,z4,z111]),(0,[z0,z2,z4,z1466,z24,z6]),(0,[z0,z496,z329,z2,z4,z5])],[(0,[z0,z1,z2,z4,z1621,z6]),(0,[z0,z533,z2,z4,z79,z6]),(0,[z0,z1,z2,z216,z24,z6]),(0,[z0,z1,z206,z2,z27,z5])],[(0,[z42,z1,z2,z4,z51,z6]),(0,[z366,z1,z2,z4,z5,z251]),(0,[z0,z1,z2,z4,z5,z1622]),(0,[z0,z1,z1623,z2,z4,z5])],[(0,[z0,z1,z2,z315,z5,z26]),(0,[z0,z1,z2,z4,z5,z1624]),(0,[z86,z157,z2,z4,z43,z6]),(0,[z0,z1,z2,z332,z5,z581]),(0,[z0,z1,z2,z4,z1625,z6]),(0,[z0,z1,z228,z4,z5,z18]),(0,[z313,z1,z2,z4,z43,z6]),(0,[z0,z1,z1626,z2,z4,z5])],[(0,[z0,z1,z124,z4,z51,z6]),(0,[z0,z1,z2,z4,z358,z251]),(0,[z0,z1,z2,z27,z112,z5]),(0,[z0,z17,z2,z4,z79,z26]),(0,[z0,z13,z1,z4,z24,z26]),(0,[z0,z1,z2,z4,z5,z810]),(0,[z0,z1,z2,z555,z186,z6]),(0,[z0,z1,z2,z880,z5,z18])],[(0,[z607,z1,z2,z20,z5,z6]),(0,[z64,z1,z890,z4,z5,z6]),(0,[z125,z296,z2,z4,z126,z6]),(0,[z1627,z1,z2,z4,z5,z6]),(0,[z0,z1,z456,z4,z5,z18])],[(0,[z55,z0,z102,z4,z5,z18]),(0,[z0,z1,z2,z4,z43,z226]),(0,[z0,z1,z1628,z2,z4,z5]),(0,[z0,z1,z61,z2,z4,z472])],[(0,[z0,z1104,z2,z4,z5,z6]),(0,[z0,z1,z14,z2,z4,z291])],[(0,[z0,z1,z2,z320,z5,z18]),(0,[z101,z0,z1,z121,z27,z5]),(0,[z0,z1,z2,z119,z5,z280])],[(0,[z0,z1,z2,z4,z1629,z6]),(0,[z0,z1,z2,z27,z379,z5]),(0,[z0,z108,z2,z70,z5,z6]),(0,[z182,z0,z1,z2,z119,z5])],[(0,[z0,z1,z2,z4,z24,z6]),(0,[z0,z1,z2,z4,z5,z1630]),(0,[z0,z46,z2,z4,z204,z6]),(0,[z0,z1,z2,z717,z5,z6]),(0,[z0,z1,z1111,z2,z4,z24])],[(0,[z0,z1,z307,z2,z5,z122]),(0,[z0,z1,z2,z4,z166,z43]),(0,[z0,z1,z2,z4,z1631,z6]),(0,[z0,z1,z2,z4,z24,z1342])],[(0,[z49,z598,z2,z4,z5,z6]),(0,[z0,z17,z1,z2,z119,z5]),(0,[z0,z1,z2,z4,z24,z98]),(0,[z0,z1,z2,z1632,z4,z5]),(0,[z0,z612,z2,z4,z71,z6]),(0,[z101,z0,z1,z21,z5,z19])],[(0,[z0,z1,z2,z27,z5,z37]),(0,[z0,z1,z171,z2,z4,z43]),(0,[z0,z1,z2,z27,z565,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 471) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 471).take 474) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 945).take 469) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1414).take 236) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1650)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [471, 474, 469, 236] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 65).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 65).take 75).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 140).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 222).take 79).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 301).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 373).take 81).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 454).take 58).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [65, 75, 82, 79, 72, 81, 58] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

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

end PEqualNP.Outside.L_meta_37023

theorem PEqualNP.Outside.L_meta_37023 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4008373480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4008373480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37023.solve