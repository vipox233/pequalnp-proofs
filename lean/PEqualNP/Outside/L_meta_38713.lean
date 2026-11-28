import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38713

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
  Nat.testBit (4276808424 * 2 ^ 32 + 3941264104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0xb020000822801045#64 ++ 0xffdc0279e79cf3cf#64 : BitVec 128),
   (0x42401ca289294512#64 ++ 0x7fbc3da699eb4d33#64 : BitVec 128),
   (0x0901c14514528a28#64 ++ 0x9f7fc1c71e738e3c#64 : BitVec 128),
   (0x0d82ee07c07c0f80#64 ++ 0x16f3fe07e07c0fc0#64 : BitVec 128),
   (0x0e0377f0007fe000#64 ++ 0x0df3fff8007ff000#64 : BitVec 128),
   (0x100bbbffff800000#64 ++ 0x03fbffffff800000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [8, 3]⟩, ⟨.and, [9, 4]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0002aa07c0000000 0x16f3fe07e01c03c0

def z1 : W := mkw 0x0901c14514528a28 0x9f7fc1c71e738e3c

def z2 : W := mkw 0x0e0377f0007fe000 0x0df3fff8007ff000

def z3 : W := mkw 0x100bbbffff800000 0x17fbffffff9c03c0

def z4 : W := mkw 0x42401ca289294512 0x7fbc3da699eb4d33

def z5 : W := mkw 0xb020000822801045 0xffdc0279e79cf3cf

def z6 : W := mkw 0x0d82ee07d47c0fa8 0x96fffe07fe7c0ffc

def z7 : W := mkw 0x110bbbffff800a28 0x93ffffffff800e3c

def z8 : W := mkw 0x04800400002c0580 0x00000000000c01c0

def z9 : W := mkw 0x0482ae07c02c0580 0x02f3fe07e00c01c0

def z10 : W := mkw 0x0e004400007fe000 0x0c000000007ff000

def z11 : W := mkw 0x0d82ee07c07c0f80 0x16f3fe07e07c0fc0

def z12 : W := mkw 0x100bbbffff800000 0x03fbffffff800000

def z13 : W := mkw 0x42401ca289294512 0xffbc3de69febcd3f

def z14 : W := mkw 0x000bbbf7dd000000 0x0023fd8618000000

def z15 : W := mkw 0xb020000822801045 0xfc840238e19cf3cf

def z16 : W := mkw 0x42401ca289294512 0x7b2c3da699e34d33

def z17 : W := mkw 0x0f8377f0007fef80 0x0df3fff8007ffc00

def z18 : W := mkw 0x0d82e20540540a80 0x0043c201601402c0

def z19 : W := mkw 0x424010a009014012 0x690c01a019834033

def z20 : W := mkw 0x000333f000000000 0x01f3fff800000000

def z21 : W := mkw 0x0c036750007ea000 0x04f3fe58007cb000

def z22 : W := mkw 0x1e08cc0fffffe000 0x0e080007fffff000

def z23 : W := mkw 0x0d82ee07c07e8fa8 0x96f3fe07e07c8fcc

def z24 : W := mkw 0x01808807c0000f80 0x12000007e0000fc0

def z25 : W := mkw 0x0901c14514528a28 0x9fffc3ff1e7ffe3c

def z26 : W := mkw 0x0002aa07c0000000 0x02f3fe07e0000000

def z27 : W := mkw 0x0d82ee07c07c0f80 0x00a3fe06e06c0dc0

def z28 : W := mkw 0x00033bf289000000 0x01f3fffe18000000

def z29 : W := mkw 0x0900c00500500a00 0x1673c00700700e00

def z30 : W := mkw 0x0d83ef47d47e8fa8 0x9fffffc7fe7f8ffc

def z31 : W := mkw 0x0002aa07c0000000 0x03fbfe47e6000000

def z32 : W := mkw 0x0002aa07c0000000 0x00f3fe0600000000

def z33 : W := mkw 0x404018a289000512 0x7fbc3da699e30d33

def z34 : W := mkw 0xbe2bfffffffff045 0xfffffffffffff3cf

def z35 : W := mkw 0xb028880fff801045 0x62080007ff8001c3

def z36 : W := mkw 0xa020000000001045 0xfed40201e01cf3cf

def z37 : W := mkw 0xb020000822801045 0x804002596614b2cc

def z38 : W := mkw 0x0e0377f0007fe000 0x00c3fe78001cf000

def z39 : W := mkw 0x020333f00003e000 0x09f3fff80003f000

def z40 : W := mkw 0x0000000000000000 0x16d00201e01c03c0

def z41 : W := mkw 0xbda2ee0fe2fc1fc5 0xe92ffc7e07e0fc0f

def z42 : W := mkw 0x0182aa07c0000f80 0x16f3fe07e01c0fc0

def z43 : W := mkw 0x0e004400007fe000 0x0000000000630000

def z44 : W := mkw 0x0901c14514528a28 0x8d73c1c71e738e3c

def z45 : W := mkw 0x0d82ea07c0540a80 0x02f3fe07e01402c0

def z46 : W := mkw 0x100ba35d76800000 0x0043c25966000000

def z47 : W := mkw 0x424014a009294512 0x690c01a019e34c33

def z48 : W := mkw 0xb02911f83f801045 0xe90c01f81f80f00f

def z49 : W := mkw 0xb02bbbffff801045 0xffffffffff9cf3cf

def z50 : W := mkw 0x0002220000000000 0x0df3fe78001cf000

def z51 : W := mkw 0x0e0155f0007fe000 0x0000018000630000

def z52 : W := mkw 0x0901c14514528a28 0x9f3fc1c61e638c3c

def z53 : W := mkw 0x0182aa07c0000f80 0x12f3fe07e0000fc0

def z54 : W := mkw 0x1008880fff800000 0x02080007ff800000

def z55 : W := mkw 0x0901c14514528a28 0x892fc1c61e638c3c

def z56 : W := mkw 0xb1a0880fe2801fc5 0x92000007e6000fcc

def z57 : W := mkw 0x100bbbffff800000 0x9fffffffff9cf20c

def z58 : W := mkw 0x0d82ee07c07c0f80 0x1fffff87f87f0ff0

def z59 : W := mkw 0x4b41dde79d7bcf3a 0xfffffde79ffbcf3f

def z60 : W := mkw 0xb921c14d36d29a6d 0xffffc3ffffffffff

def z61 : W := mkw 0xf2601caaaba95557 0xfffc3fffffffffff

def z62 : W := mkw 0x000333f000000000 0x01f3fff8000c7000

def z63 : W := mkw 0x0d80cc07c07c0f80 0x16000007e07c0fc0

def z64 : W := mkw 0x0d804400007c0f80 0x1dd00278007cffc0

def z65 : W := mkw 0x0e0377f0007fe000 0x0023fd8000630000

def z66 : W := mkw 0xb020000822801045 0xf20c0001e78003cf

def z67 : W := mkw 0xb02bbbffff801045 0xf3ffffffff8003cf

def z68 : W := mkw 0xb020000822801045 0xf2cc0279e79cf3cf

def z69 : W := mkw 0x0203bbf7c003e000 0x0bf3ffffe003f000

def z70 : W := mkw 0x40400c0289280512 0x76bc3c0699e80d33

def z71 : W := mkw 0x4fc2fea7c97d4f92 0x7fffffa7f9ff4ff3

def z72 : W := mkw 0xb020000822801045 0xff9c00788788f10f

def z73 : W := mkw 0x0d83ef57c07eaf80 0x16f3fe5fe07cbfc0

def z74 : W := mkw 0x0901c14514528a28 0x0023c18618630c30

def z75 : W := mkw 0xb020000822801045 0x60800238e18c71c3

def z76 : W := mkw 0x42401ca289294512 0x7ffc3fa699ff4d33

def z77 : W := mkw 0xb02333f822801045 0xfffffff9e79cf3cf

def z78 : W := mkw 0x0001814514000000 0x9f7fc1c71e738e3c

def z79 : W := mkw 0x0001814514000000 0x037bc1c71e000000

def z80 : W := mkw 0x0901d9e79d528a28 0x9ffffde79ff38e3c

def z81 : W := mkw 0x0d82ea07c0540a80 0x16f3fe07e01c03c0

def z82 : W := mkw 0x0000000000000000 0x1f3c018618630c30

def z83 : W := mkw 0x040333f000042000 0x01f3fff800043000

def z84 : W := mkw 0x42401ca289294512 0x7ffc3ffe99fffd33

def z85 : W := mkw 0x0002aa07c0000000 0x02f3fe07e01402c0

def z86 : W := mkw 0xb02bbbffff801045 0x83fbffffff94b2cc

def z87 : W := mkw 0x0c026600007c0000 0x04f3fe38007c7000

def z88 : W := mkw 0x40433bf289000512 0x73fffffe99800d33

def z89 : W := mkw 0x0002aa07c0000000 0x12f3fe07e00003c0

def z90 : W := mkw 0x0d804400007c0fa8 0x94040000007c0ffc

def z91 : W := mkw 0x0d83ef47d47e8fa8 0x16f3ff87f87f0ff0

def z92 : W := mkw 0x42401ca289294512 0x7ffc3ffff9fffff3

def z93 : W := mkw 0xb1a0880fe2801fc5 0xffdc027fe79cffcf

def z94 : W := mkw 0xb02bbbffff801045 0xebffffffff8cf1cf

def z95 : W := mkw 0x0000000000000000 0x0020018618630c30

def z96 : W := mkw 0x04822e02c02c0580 0x00803e00e00c01c0

def z97 : W := mkw 0x04832f42d42e85a8 0x898c3fc0fe0f81fc

def z98 : W := mkw 0x0002aa07d4000000 0x02fbfe07fe000000

def z99 : W := mkw 0x0e03f7f5147fe000 0x0ffbffff1e7ff000

def z100 : W := mkw 0x0d804400007c0f80 0x14000000007c0fc0

def z101 : W := mkw 0xbda2ee0fe2fc1fc5 0xfffffe7fe7fcffcf

def z102 : W := mkw 0x0e0377f0007fe000 0x1ff3fff8807ff100

def z103 : W := mkw 0x04822e02c02c0580 0x00f3fe00e00c01c0

def z104 : W := mkw 0x0002aa07c0000000 0x0273fc0700000000

def z105 : W := mkw 0x0003bbf7c0000000 0x02f3ff87e0000000

def z106 : W := mkw 0x0d82e605407c0a80 0x04f3fe01607c02c0

def z107 : W := mkw 0x0d826600007c0f80 0x16f3fe01e07c0fc0

def z108 : W := mkw 0x0f03f7f5147fea28 0x9fffffff1e7ffe3c

def z109 : W := mkw 0x0e0377f0147fe028 0x9ffffffe1e7ffc3c

def z110 : W := mkw 0x0901c14514528a28 0x837bc1c71e738e3c

def z111 : W := mkw 0x4040080289000512 0x720c000699800d33

def z112 : W := mkw 0x0000000000000000 0x0000000000000000

def z113 : W := mkw 0x0002aa07c0000000 0x06f3fe07e01c0000

def z114 : W := mkw 0x4e437ff2897fe512 0x7ffffffe99fffd33

def z115 : W := mkw 0xb02bbbffff801045 0x03fbffffff8430c0

def z116 : W := mkw 0x100bbbffff800000 0x032bfdffff800000

def z117 : W := mkw 0x0c0363500056a000 0x0043c2580014b000

def z118 : W := mkw 0x0e0377f0007fe000 0x7ffffff881fff103

def z119 : W := mkw 0x424018a289014012 0x6bbc3da699834033

def z120 : W := mkw 0x524bbfffffa94512 0x7fffffffffeb4d33

def z121 : W := mkw 0x0900c00500500a00 0x9f7fc1c71e738e3c

def z122 : W := mkw 0x000333f000000000 0x0df3fff8001cf000

def z123 : W := mkw 0x0901c14514528a28 0xffffc1e79ffbcf3f

def z124 : W := mkw 0x0d82ee07c07c0f80 0x04f3fe01e07c03c0

def z125 : W := mkw 0x0002aa07c0000000 0x0023fc0600000000

def z126 : W := mkw 0x0d804400007c0f80 0x16d00201e07c0fc0

def z127 : W := mkw 0x0c02ee07c07c0000 0x16f3fe07e07c03c0

def z128 : W := mkw 0x020014a000294000 0x0df03ff8007ff000

def z129 : W := mkw 0x020333f00003e000 0x0df3fff8001ff000

def z130 : W := mkw 0xb028880fff801045 0xf20c0007ff8003cf

def z131 : W := mkw 0xbda3e34d76d69aed 0x8043c2596614b2cc

def z132 : W := mkw 0x0900400000528a28 0x9c04000000738e3c

def z133 : W := mkw 0x0c004400007c0000 0x04d00200007c0000

def z134 : W := mkw 0x0d82ee07c07c0f80 0x0023fc0600600c00

def z135 : W := mkw 0xb022aa0fe2801045 0xfffffe7fe79cf3cf

def z136 : W := mkw 0x000333f000000000 0x0023fd8000000000

def z137 : W := mkw 0x0f83fff7c07fef80 0x1ff3ffffe07fffc0

def z138 : W := mkw 0x100bb3fd76800000 0x01f3fff966000000

def z139 : W := mkw 0xb02bbbffff801045 0xffdffe79e79cf3cf

def z140 : W := mkw 0x0e8377f0007fe580 0x0df3fff8007ff1c0

def z141 : W := mkw 0x0e0377f0007fe000 0x1ff3fff9e07ff3c0

def z142 : W := mkw 0x100bbbffff800000 0x012bfdfe1f800000

def z143 : W := mkw 0x404bbbf7dd000512 0x722ffd8699800d33

def z144 : W := mkw 0xa020000000001045 0xfc040000001cf3cf

def z145 : W := mkw 0x0e004400007fe000 0x00000000006f7000

def z146 : W := mkw 0x0f804400007fef80 0x1c000000007fffc0

def z147 : W := mkw 0x0f82ee07c07fef80 0x1ef3fe07e07fffc0

def z148 : W := mkw 0x0f82fea7c07d4f80 0x1ff3ffa7e07f4fc0

def z149 : W := mkw 0xb22333f82283f045 0xfffffff9e79ff3cf

def z150 : W := mkw 0x0702b6b5142d6a28 0x928c3e3f1e0c7e3c

def z151 : W := mkw 0x0002220000000000 0x00f3fe0000000000

def z152 : W := mkw 0x000bbbf7dd000000 0x03f3fffff8000000

def z153 : W := mkw 0x0901c14514528a28 0x9fffc3c7fe7f8ffc

def z154 : W := mkw 0x0e0377f0007fe000 0x0923fdf80063f000

def z155 : W := mkw 0xee604400007ff557 0xfc040000007fffff

def z156 : W := mkw 0x0d804c02807c0f80 0x16000006807c0fc0

def z157 : W := mkw 0x4e4377f0097fe512 0x7dfffff819fffd33

def z158 : W := mkw 0x100bbbffff828028 0x9fffffffff93823c

def z159 : W := mkw 0x0000000000000000 0x0dd00278001cf000

def z160 : W := mkw 0x0182aa07c0000f80 0x1223fc07e0000fc0

def z161 : W := mkw 0x0402221000042000 0x0000021800043000

def z162 : W := mkw 0x0f8155f0007fef80 0x1d0001f8007fffc0

def z163 : W := mkw 0x020111f00003e000 0x090001f80003f000

def z164 : W := mkw 0x00000c0280280500 0x7fbc3da699eb4d33

def z165 : W := mkw 0xb1abbbffff801fc5 0xffffffffff9cffcf

def z166 : W := mkw 0x0000000000000000 0x090000780000f000

def z167 : W := mkw 0x42401ca289294512 0x692c3da619e34c33

def z168 : W := mkw 0x0003b3f500000000 0x03f3ffff00000000

def z169 : W := mkw 0x100bbbffff800000 0x0ffbffffff9cf000

def z170 : W := mkw 0xb821414822d29045 0xffffc3f9e7fff3cf

def z171 : W := mkw 0x0c004400007c0000 0x04000000007c0000

def z172 : W := mkw 0x0e837ff2c07fe580 0x0df3fff8e07ff1c0

def z173 : W := mkw 0x4b41dde79d7bcf3a 0xe0c3fc618798c30f

def z174 : W := mkw 0x0901c14514528a28 0x9c67c1c71e738e3c

def z175 : W := mkw 0x0d80cc07c07c0f80 0x12000007e0600fc0

def z176 : W := mkw 0x0003ab47d4000000 0x02f3fe47e6000000

def z177 : W := mkw 0x0d82ee07c07c0f80 0x1623fc07e07c0fc0

def z178 : W := mkw 0x4b404400007bcf3a 0xfc040000007bcf3f

def z179 : W := mkw 0x4f4377f0007fef3a 0xfdf7fff8007fff3f

def z180 : W := mkw 0xb020000822801045 0xe90c00780780f00f

def z181 : W := mkw 0xbe2377f822fff045 0xedfffff807fff00f

def z182 : W := mkw 0x0d804400007c0f80 0x04000000007c0c00

def z183 : W := mkw 0x1002aa0fe2800000 0x03fbfe7fe7800000

def z184 : W := mkw 0x4e4377f01d7fe03a 0xedfffff81ffff03f

def z185 : W := mkw 0x038199f7c003ef80 0x1b0001ffe003ffc0

def z186 : W := mkw 0x0c026600007c0000 0x04f3fe00007c0000

def z187 : W := mkw 0x100333f822800000 0x03fbfff9e7800000

def z188 : W := mkw 0x0e0377f0007fe000 0x1ffffffe187ffc30

def z189 : W := mkw 0xb020000822801045 0xe0c00279e79cf3cf

def z190 : W := mkw 0x0182aa07c0000a80 0x02f3fe07e00002c0

def z191 : W := mkw 0x0e0276b0007fe000 0x0cf3fe38007ff000

def z192 : W := mkw 0x0d82ee07c07c0f80 0x16b3fe06e06c0dc0

def z193 : W := mkw 0x0101814514000a28 0x937fc1c71e000e3c

def z194 : W := mkw 0x0e0377f0007fe000 0x0063ffd80077b000

def z195 : W := mkw 0x000018a289000000 0x03b83da699800000

def z196 : W := mkw 0x0e0377f0147fe028 0x8dfffff81e7ff03c

def z197 : W := mkw 0x0f0377f0007fea28 0x8df3fff8007ff20c

def z198 : W := mkw 0x100a3abaeb800000 0x00803e38e1800000

def z199 : W := mkw 0x0901c14514528a28 0x8043c0410610820c

def z200 : W := mkw 0xb020000822801045 0xfffc03ffffffffff

def z201 : W := mkw 0x0a0373f00053e000 0x0df3fff80073f000

def z202 : W := mkw 0x4e404400007fe512 0x7c040000007ffd33

def z203 : W := mkw 0x4e4377f0007fe512 0x7df7fff8007ffd33

def z204 : W := mkw 0x0d82ee07c07c0f80 0x76f3fe27e1fc4fc3

def z205 : W := mkw 0x0d82ee07c07c0f80 0x9ffffe47e67c8fcc

def z206 : W := mkw 0x0c026600007c0000 0x16f3fe01e07c03c0

def z207 : W := mkw 0x0800400000528000 0x0c00000000738000

def z208 : W := mkw 0x0f01c545147fea28 0x9f7fc1c71e7ffe3c

def z209 : W := mkw 0x0d804400007c0f80 0x0000000000600c00

def z210 : W := mkw 0x0f8377f0007fef80 0x1df3fff8007fffc0

def z211 : W := mkw 0x0d82ea07c0540f80 0x12f3fe07e0140fc0

def z212 : W := mkw 0x0d82ee07c07c0f80 0x1463fe07607c0fc0

def z213 : W := mkw 0x0101814514028a28 0x9b0c01c71e038e3c

def z214 : W := mkw 0xb020000822801045 0xffdc027fff9cffff

def z215 : W := mkw 0x0f82ee07c07d6f80 0x16f3fe07e07c7fc0

def z216 : W := mkw 0x0901c14514528a28 0x8063c1c71e738e3c

def z217 : W := mkw 0x1d8aee0ffffc0f80 0x16fbfe07fffc0fc0

def z218 : W := mkw 0xbe2377f822fff045 0xfffffff9e7fff3cf

def z219 : W := mkw 0x0482aa07c0040080 0x02f3fe07e00400c0

def z220 : W := mkw 0x0e0155f0007fe000 0x0d0001f8007ff000

def z221 : W := mkw 0x100911f83f800000 0x010801f81f800000

def z222 : W := mkw 0xb02bbbffff801045 0xebffffffff80f00f

def z223 : W := mkw 0x0001894794000000 0x03fbfdc79e000000

def z224 : W := mkw 0x060337f0002d6000 0x01f3fff8000c7000

def z225 : W := mkw 0x100ababfeb800000 0x00a3fe3ee1800000

def z226 : W := mkw 0x0003b3f514000000 0x9fffffff1e1cf20c

def z227 : W := mkw 0x0d82ee07c07c0f80 0x76fffe07e1fc0fc3

def z228 : W := mkw 0xf06bbbffff801557 0xf3ffffffff800fff

def z229 : W := mkw 0x0f0377f0007fea28 0x9df7fff8007ffe3c

def z230 : W := mkw 0xb921c14d36d29a6d 0x60a3c3bef9ef7df3

def z231 : W := mkw 0x0000000000000000 0x7fbc01a699eb4d33

def z232 : W := mkw 0x0d81c545147e8fa8 0x9f7fc1c71e7f8ffc

def z233 : W := mkw 0x100bab5ff6800000 0x02f3fe5fe6000000

def z234 : W := mkw 0x110bbbffff800a28 0x03fbffffff800c30

def z235 : W := mkw 0x0e0377f0007fe000 0x9ffffff9067ff20c

def z236 : W := mkw 0x42401ca289294512 0x60a03da699eb4d33

def z237 : W := mkw 0x0901c14514528a28 0x926fc1c71e738e3c

def z238 : W := mkw 0x504bbbffff800512 0x7fffffffffe30d33

def z239 : W := mkw 0x0c0373f00056a000 0x0df3fff80077b000

def z240 : W := mkw 0x0e0377f0007fe000 0x0d23fdf8007ff000

def z241 : W := mkw 0x1d8955f83ffc0f80 0x150801f81ffc0fc0

def z242 : W := mkw 0x0f82ee07c07fef80 0x16f3fe07e07f0fc0

def z243 : W := mkw 0x0e0377f0147fe000 0x0dfbfff81e7ff000

def z244 : W := mkw 0x524bbbffff814012 0x63fbffffff804003

def z245 : W := mkw 0x0c804400007c0580 0x04000000007c01c0

def z246 : W := mkw 0x0c826e02c07c0580 0x04f3fe00e07c01c0

def z247 : W := mkw 0x0001814514000000 0x9f7fc1c71e10820c

def z248 : W := mkw 0x190bfbffffd28a28 0x9ffffffffff38e3c

def z249 : W := mkw 0x000333f000000000 0x03fbfffe18000000

def z250 : W := mkw 0x100199efbf800000 0x03fbffffff800000

def z251 : W := mkw 0x0002aa07c0000000 0x02b3fc0680000000

def z252 : W := mkw 0x0001014014028028 0x890c01c01e03803c

def z253 : W := mkw 0x4fc2f2a549554a92 0x694fc3a1799742f3

def z254 : W := mkw 0x0c026600007c0000 0x0df3fe78007cf000

def z255 : W := mkw 0x1d8bfffffffe8fa8 0x9fffffffffff8ffc

def z256 : W := mkw 0x000333f014028028 0x89fffff81e03803c

def z257 : W := mkw 0x0e0377f0007fe000 0x00a3ffb8006f7000

def z258 : W := mkw 0x0182aa07c0000f80 0x0023fc0600000c00

def z259 : W := mkw 0x0d82ee07c07e8fa8 0x9ef7fe07e07f8ffc

def z260 : W := mkw 0x000101500002a000 0x000000580000b000

def z261 : W := mkw 0x0b004400007bca28 0x9c040000007bce3c

def z262 : W := mkw 0x0d804400007e8fa8 0x9c040000007f8ffc

def z263 : W := mkw 0x0d82ee07c07c0f80 0x00c3fe01e01c03c0

def z264 : W := mkw 0x100bbbffff800000 0x00c3fe79e7800000

def z265 : W := mkw 0x0e0b77f01d7fe000 0x0df3fff8187ff000

def z266 : W := mkw 0x000333f000000000 0x00f3ff8000000000

def z267 : W := mkw 0x0d82ee07c07c0f80 0x17f3fe7fe07c0fc0

def z268 : W := mkw 0xf2601caaaba95557 0x80603fdf7e77befc

def z269 : W := mkw 0xfb60440822fbdf7f 0xffdc0279e7ffffff

def z270 : W := mkw 0x100bab5ff6800000 0x03fbfe7fe7800000

def z271 : W := mkw 0x0f8377f0007fef80 0x1ff3fff9e07fffc0

def z272 : W := mkw 0xb020000822801045 0xf6dc0201e79c03cf

def z273 : W := mkw 0x0d804400007e8fa8 0x9fdc0241e67f8ffc

def z274 : W := mkw 0x0582ae07c02c0f80 0x12803e07e00c0fc0

def z275 : W := mkw 0x0000000000000000 0x9f5c00410610820c

def z276 : W := mkw 0x0002220000000000 0x04f3fe00001c0000

def z277 : W := mkw 0x100bbbffff800000 0x002bfd861f800000

def z278 : W := mkw 0x4fc2ee07c07d4f92 0x7ef7fe07e07f4ff3

def z279 : W := mkw 0x0901c14514528a28 0x8023c1c61e638c3c

def z280 : W := mkw 0x0d82ee07d47c0fa8 0x9fffff87fe7f0ffc

def z281 : W := mkw 0x4dc04400007c0f92 0x74040000007c0ff3

def z282 : W := mkw 0x01808807c0000f80 0x16d00207e01c0fc0

def z283 : W := mkw 0x0002baa7c9000000 0x0023fd8618000000

def z284 : W := mkw 0x4e4377f0007fe512 0x6df3fff8007ff103

def z285 : W := mkw 0x4e4155f0097fe512 0x7d0c01f819fffd33

def z286 : W := mkw 0x100bbbffff800000 0x17fbffffff880100

def z287 : W := mkw 0x0d82ee07c07c0f80 0x0063fe0760740ec0

def z288 : W := mkw 0x100bbbffff800000 0x0063ffdf7e000000

def z289 : W := mkw 0x100bbbffff828028 0x8bffffffff83803c

def z290 : W := mkw 0x148bbfffffac0580 0x03fbffffff8c01c0

def z291 : W := mkw 0xb020000822801045 0x60000000e18001c3

def z292 : W := mkw 0x0c0373f00056a000 0x01f3fff80014b000

def z293 : W := mkw 0x0f804400007fea80 0x0c000000007ff2c0

def z294 : W := mkw 0xb020880fe2801045 0xf20c0007e78003cf

def z295 : W := mkw 0x4fc2ee07c07fef92 0x7ef7fe07e07ffff3

def z296 : W := mkw 0x0d804400007c0f80 0x14d00200007c0fc0

def z297 : W := mkw 0x000232b000000000 0x00803e38000c7000

def z298 : W := mkw 0x060236b0002d6000 0x00803e38000c7000

def z299 : W := mkw 0xb020000822801045 0xebdc0279e780f00f

def z300 : W := mkw 0x000333f000000000 0x0123fdf800000000

def z301 : W := mkw 0x000abab7c9000000 0x02f3fe07e0000000

def z302 : W := mkw 0x0901c14514528a28 0x9d2fc1c61e738e3c

def z303 : W := mkw 0x0e004400007fe500 0x1c000000007ffd00

def z304 : W := mkw 0x0000000000000000 0x7f9c002081884103

def z305 : W := mkw 0xb020000822801045 0xffdc0279e7ffffff

def z306 : W := mkw 0x0e004400007fe000 0x0cd00200007ff000

def z307 : W := mkw 0x42401ca289294512 0x7ffc3fa7f9ff4ff3

def z308 : W := mkw 0x000b33f01d000000 0x01f3fff818000000

def z309 : W := mkw 0x100bbbffff800000 0x73ffffffff800103

def z310 : W := mkw 0x000018a289000000 0x7fbc3da699884103

def z311 : W := mkw 0x190a7abaebd28a28 0x9c843e38e1f38e3c

def z312 : W := mkw 0x0900c00500500a00 0x16f3c207e07c0fc0

def z313 : W := mkw 0x0e03fff7c07fe000 0x0ff3ffffe07ff000

def z314 : W := mkw 0x424111f00903e012 0x690c01f81983f033

def z315 : W := mkw 0x100bbbffff800000 0x01abfffeff800000

def z316 : W := mkw 0x42401ca289294512 0x7ffc3fa7f9eb4d33

def z317 : W := mkw 0x0002220000000000 0x16f3fe01e01c03c0

def z318 : W := mkw 0x00000c0280280500 0x16b03c0680680d00

def z319 : W := mkw 0x0d82e605407c0f80 0x14f3fe01607c0fc0

def z320 : W := mkw 0x0e004400007fe000 0x0dd00278007ff000

def z321 : W := mkw 0x0f82ee07c07fef80 0x1ff3fe7fe07fffc0

def z322 : W := mkw 0xb020000822801045 0xf6d00279e79cf3cf

def z323 : W := mkw 0x1e0b77f83fffe000 0x0dfbfff81ffff000

def z324 : W := mkw 0x0c0363500056a000 0x0dd3c278001cf000

def z325 : W := mkw 0x0d82ee07c07c0f80 0x16f3ff87f87f0ff0

def z326 : W := mkw 0x0f804400007fef80 0x0000000000630c00

def z327 : W := mkw 0x0f804400007d4f80 0x1c000000007f4fc0

def z328 : W := mkw 0x000bbbf7dd000000 0x03bbfda699800000

def z329 : W := mkw 0x0002baa7c9000000 0x03fbffa7f9800000

def z330 : W := mkw 0x0002bab7c0000000 0x02f3fe3fe0000000

def z331 : W := mkw 0xb02bbbffff82906d 0xebffffffff83f03f

def z332 : W := mkw 0x0103b3f514000a28 0x93ffffff1e000e3c

def z333 : W := mkw 0x42401ca289294512 0x60803c2081884103

def z334 : W := mkw 0xbe20440822fff045 0xffdc0279e7fff3cf

def z335 : W := mkw 0x020014a000294000 0x0db03da0006b4000

def z336 : W := mkw 0x1e0bf7fd76ffe000 0x0df3fff9667ff000

def z337 : W := mkw 0x0e004400007fe000 0x7c040000007ff103

def z338 : W := mkw 0x42401ca289294512 0x00203d8618630c30

def z339 : W := mkw 0x100ababfeb800000 0x02f3fe3fe1800000

def z340 : W := mkw 0x00023aa289000000 0x03fbffa699800000

def z341 : W := mkw 0x1d8be35d76d40a80 0x0043c259661402c0

def z342 : W := mkw 0x0003ab47d4000000 0x9fffffc7fe1c83cc

def z343 : W := mkw 0x0d804400007c0f80 0x00000000006c0dc0

def z344 : W := mkw 0x1e0955f83fffe000 0x0d0801f81ffff000

def z345 : W := mkw 0x504bbbffff800512 0x7fffffffff884d33

def z346 : W := mkw 0x0c0377f0007c0000 0x05f3fff8007c0000

def z347 : W := mkw 0x0e014540007fe000 0x0d0001c0007ff000

def z348 : W := mkw 0xb020000822801045 0xedd00279e79cf3cf

def z349 : W := mkw 0x100abaafff800000 0x03fbffa7ff800000

def z350 : W := mkw 0x0901c14514528a28 0x922fc1871e630e3c

def z351 : W := mkw 0x0d82ee07c07c0f80 0x1223fc07e0600fc0

def z352 : W := mkw 0xb02bbbffff801045 0xe3fbffffff9cf3cf

def z353 : W := mkw 0x5fcbfffffffd4f92 0x7fffffffffff4ff3

def z354 : W := mkw 0x0d82ee07c07c0f80 0x1ef7fe07e07f0ff0

def z355 : W := mkw 0xb02a3abaeb801045 0x60803e38e18c71c3

def z356 : W := mkw 0x000bbbf7dd000000 0x037bfdc71e000000

def z357 : W := mkw 0x0d82ee07c07c0f80 0x1ff3fe7fe07cffc0

def z358 : W := mkw 0x0d03e3551456aa28 0x8043c2590614b20c

def z359 : W := mkw 0x0e0373f00057e000 0x0943c3f80017f000

def z360 : W := mkw 0x000bbbf7dd000000 0x0df3fffe181cf000

def z361 : W := mkw 0x0d83fff7c07c0f80 0x17f3ffffe07c0fc0

def z362 : W := mkw 0x0e0377f0097fe000 0x0dfbfff819fff000

def z363 : W := mkw 0x0d82ee07c07c0f80 0x7ffffe27e1fc4fc3

def z364 : W := mkw 0x0e0377f0007fe000 0x0ffbfffe187ff000

def z365 : W := mkw 0xb02bbbffff801045 0x63fbffffff8c71c3

def z366 : W := mkw 0x000bbbf7dd000000 0x0063ffde18000000

def z367 : W := mkw 0xb22111f82283f045 0xe90c01f80783f00f

def z368 : W := mkw 0x0d82ee07c07c0f80 0x96f3fe47e67c8fcc

def z369 : W := mkw 0x0e0377f0007fe000 0x7ffffffe99fffd33

def z370 : W := mkw 0xf2601caaaba95557 0xffbc3da7ffeb4fff

def z371 : W := mkw 0xb02333f822801045 0x81f3fff96614b2cc

def z372 : W := mkw 0x0900400000528a28 0x0000000000630c30

def z373 : W := mkw 0x120bbbffff816000 0x03fbffffff807000

def z374 : W := mkw 0xf260040822a95557 0xffdc0279e7ffffff

def z375 : W := mkw 0x0d804400007e8fa8 0x14000000007f0ff0

def z376 : W := mkw 0x42433ff289294512 0x7ffffffe99eb4d33

def z377 : W := mkw 0x0003bbf7c0000000 0x01f3fffe00000000

def z378 : W := mkw 0x0e004400007fe000 0x04000000007f0000

def z379 : W := mkw 0x0e0377f0007fe000 0x09c3fff8001ff000

def z380 : W := mkw 0xbc22660822fc1045 0xfffffe79e7fcf3cf

def z381 : W := mkw 0x0002aa07c9000000 0x02fbfe07f9800000

def z382 : W := mkw 0x4dc2ee07c97c0f92 0x76fffe07f9fc0ff3

def z383 : W := mkw 0x4fc04400007d4f92 0x14000000007f0ff0

def z384 : W := mkw 0x4fc04400007d4f92 0x7c040000007f4ff3

def z385 : W := mkw 0x4fc377f0007fef92 0x7df7fff8007ffff3

def z386 : W := mkw 0x4240040000294512 0x0000000000630c30

def z387 : W := mkw 0xb02ba35d76801045 0x8043c2596614b2cc

def z388 : W := mkw 0x100bbbffff800000 0x63fbffffff884103

def z389 : W := mkw 0xb92be35d76d29a6d 0x8043c2596614b2cc

def z390 : W := mkw 0x0e014540007fe000 0x0d73c1c0007ff000

def z391 : W := mkw 0x42401ca289294512 0x7fbc3da699ff4ff3

def z392 : W := mkw 0x1d8bfffffffc0f80 0x17fbfffffffc0fc0

def z393 : W := mkw 0x0901c14514528a28 0xffffc3e7ffffcfff

def z394 : W := mkw 0x0002baa7c9000000 0x7fffffa7f99c43c3

def z395 : W := mkw 0x424018a289014512 0x7b0c01a699834d33

def z396 : W := mkw 0x0002a20540000000 0x0043c20160000000

def z397 : W := mkw 0x424014a009294512 0x7d0c01a019eb4d33

def z398 : W := mkw 0xb020000822801045 0xfd0c0078079cf3cf

def z399 : W := mkw 0xb02ababfeb801045 0x76f3fe3fe19c73c3

def z400 : W := mkw 0x0e8377f0407fe080 0x0df3fff8607ff0c0

def z401 : W := mkw 0x06823eb2c02d6580 0x00803e38e00c71c0

def z402 : W := mkw 0x46401ca2892d6512 0x7fbc3da699ef7d33

def z403 : W := mkw 0x0e0377f0007fe000 0x7df7fff8007ff103

def z404 : W := mkw 0x00000c0280280500 0x1fbc3d86986b0d30

def z405 : W := mkw 0x100b3bfaeb800000 0x01f3fff8e1800000

def z406 : W := mkw 0x0d82ee07c07c0f80 0x17fbfe47e67c0fc0

def z407 : W := mkw 0x0e0377f0007fe000 0xfffffff987fff30f

def z408 : W := mkw 0x000bbbf7dd000000 0x012bfda619800000

def z409 : W := mkw 0x0000000000000000 0x7fdc0278819cf103

def z410 : W := mkw 0x0983eb47d4528fa8 0x9fffffc7fe738ffc

def z411 : W := mkw 0x0101814514000a28 0x9f7fc1c71e630e3c

def z412 : W := mkw 0x00033bf289000000 0x03fbfffe99800000

def z413 : W := mkw 0x42401ca289294512 0xfffc3de79ffbcf3f

def z414 : W := mkw 0xb22111f82283f045 0x690001f80183f003

def z415 : W := mkw 0x0901c14514528a28 0x9fffc1e79ff38e3c

def z416 : W := mkw 0x0e0155f0007fe000 0x090001f80063f000

def z417 : W := mkw 0xa020000000001045 0xff5c0041061cf3cf

def z418 : W := mkw 0x000bbbf7dd000000 0x00a3fda699800000

def z419 : W := mkw 0x00000c0280280500 0x16f03e07e07c0fc0

def z420 : W := mkw 0x0c0373f00056a000 0x0df3fff8001cf000

def z421 : W := mkw 0x0d82ee07c07c0f80 0x96fffe07e67c0fcc

def z422 : W := mkw 0x0100800514000a28 0x920c00071e000e3c

def z423 : W := mkw 0xb1abbbffff801fc5 0xf3ffffffff800fcf

def z424 : W := mkw 0x0d826600007c0f80 0x14f3fe00007c0fc0

def z425 : W := mkw 0x0e0377f0007fe000 0x0dfffff8187ff030

def z426 : W := mkw 0x42400c0289294512 0x7e0c000699eb4d33

def z427 : W := mkw 0x51cbbbffff800f92 0x73ffffffff800ff3

def z428 : W := mkw 0x100bbbffff800000 0x6bffffffff804003

def z429 : W := mkw 0x00033bf289000000 0x7ffffffe999cf103

def z430 : W := mkw 0x0801414000528000 0x9f7fc1c71e738e3c

def z431 : W := mkw 0x0901c14514528a28 0x896fc1c71e738e3c

def z432 : W := mkw 0x000232b000000000 0x00f3fe3800000000

def z433 : W := mkw 0x4240040000294512 0x7c040000006b4d33

def z434 : W := mkw 0xb02bbbffff801045 0xe0c3fe79e79cf3cf

def z435 : W := mkw 0x100bbbffff800000 0x022bfd87ff800000

def z436 : W := mkw 0x0d804400007eaf80 0x14000000007cbfc0

def z437 : W := mkw 0x000333f000000000 0x09f3fff80000f000

def z438 : W := mkw 0xf26bbbffff815057 0xebffffffff83f03f

def z439 : W := mkw 0x0d804400007c0f80 0x1f3c0186187f0ff0

def z440 : W := mkw 0x4fc3fff7c97fef92 0x7ffffffff9fffff3

def z441 : W := mkw 0x4dc2ee07c97c0f92 0x7ffffe27f9fc4ff3

def z442 : W := mkw 0x00008807c0000000 0x12000007e00003c0

def z443 : W := mkw 0xbe2377f822fff045 0xf22ffd81e7e303cf

def z444 : W := mkw 0x000bbbf7dd000000 0x0063fdc71e000000

def z445 : W := mkw 0x0c0363500056a000 0x00f3fe580014b000

def z446 : W := mkw 0x0d82ee07c07c0f80 0x0083fe00e00c01c0

def z447 : W := mkw 0x0f0377f0007fea28 0x0df3fff8007ffc30

def z448 : W := mkw 0x100aaa0fff800000 0x03fbfe7fff800000

def z449 : W := mkw 0x100bab4fff800000 0x03fbffc7ff800000

def z450 : W := mkw 0xb1a0880fe2801fc5 0xf20c0007e7800fcf

def z451 : W := mkw 0xf26bbfffffa95557 0xffffffffffffffff

def z452 : W := mkw 0x1188880fff800f80 0x12080007ff800fc0

def z453 : W := mkw 0x0d83fff7c07c0f80 0x1ff3ffffe07cffc0

def z454 : W := mkw 0x0e026600007fe000 0x0df3fe78007ff000

def z455 : W := mkw 0x42401ca289294512 0x7ffc3da799fb4f33

def z456 : W := mkw 0x000111f000000000 0x090001f80000f000

def z457 : W := mkw 0xbda0440822fc1fc5 0x94400259667cbfcc

def z458 : W := mkw 0x0182ae07c0280f80 0x16f3fe07e0680fc0

def z459 : W := mkw 0x1000000822800000 0x03d80279e7800000

def z460 : W := mkw 0x000bab57d4000000 0x02f3fe07e0000000

def z461 : W := mkw 0x0c026600007c0000 0x04f3fe00e07c01c0

def z462 : W := mkw 0xbe2155f822fff045 0xffdc03f9e7fff3cf

def z463 : W := mkw 0x4242bea7c9294512 0x7fffffa7f9eb4d33

def z464 : W := mkw 0x0e0276b0007d6000 0x04f3fe38007c7000

def z465 : W := mkw 0x0d82ee07c07c0f80 0x14a3fe06e07c0fc0

def z466 : W := mkw 0x1002220822800000 0x03fbfe79e7800000

def z467 : W := mkw 0xb0233bfaab801045 0xffffffffff9cf3cf

def z468 : W := mkw 0x0f0377f0147fea28 0x9dfffff81e7ffe3c

def z469 : W := mkw 0x0d82ee07c07c0f80 0x02f3fe07e0600c00

def z470 : W := mkw 0x424018a289014012 0x7fbc3da699e34c33

def z471 : W := mkw 0x0901c14514528a28 0x9fffc3ff1e738e3c

def z472 : W := mkw 0x000bbbf7dd000000 0x00a3ffbe18000000

def z473 : W := mkw 0x0002aa07c0000000 0x16f3fe07e0100200

def z474 : W := mkw 0x100999efff800000 0x03fbfde7ff800000

def z475 : W := mkw 0x0001814514000000 0x1f7fc1c71e630c30

def z476 : W := mkw 0x018bbbf7dd000f80 0x1223fd87f8000fc0

def z477 : W := mkw 0x020333f00003e000 0x0923fdf80003f000

def z478 : W := mkw 0x0e0276b0007d6000 0x0df3fe78007cf000

def z479 : W := mkw 0x120bbbffff83e000 0x0bfbffffff83f000

def z480 : W := mkw 0x100bbbffff82a000 0x03fbffffff80b000

def z481 : W := mkw 0x4e4377f0097fe012 0x6dfffff819fff033

def z482 : W := mkw 0x424bbbf7dd014012 0x0023fd8618030030

def z483 : W := mkw 0x0e004400007fe000 0x1c000000007ff3c0

def z484 : W := mkw 0x00022a02c0000000 0x00f3fe00e0000000

def z485 : W := mkw 0x000333f000028000 0x09f3fff800038000

def z486 : W := mkw 0x0801414000528000 0x0d73c1c000738000

def z487 : W := mkw 0x100bbbffff800000 0x0023ff9e78000000

def z488 : W := mkw 0x060337f0002d6000 0x00a3ffb8000c7000

def z489 : W := mkw 0x4b404400007bcf3a 0x9c04000000738e3c

def z490 : W := mkw 0x4e4377f0007fe012 0x6df7fff8007ff033

def z491 : W := mkw 0xb120800d36801a6d 0xf20c0007ff800fff

def z492 : W := mkw 0x524bbbffff814012 0x03fbffffff830030

def z493 : W := mkw 0x42400c0289294512 0x720c000699e30d33

def z494 : W := mkw 0x0f83fff7d47fefa8 0x9ffffffffe7ffffc

def z495 : W := mkw 0xb02911f83f82906d 0xe90c01f81f83f03f

def z496 : W := mkw 0x0901414014528a28 0x9d0c01c01e738e3c

def z497 : W := mkw 0x100bbbffff800500 0x13fbffffff800d00

def z498 : W := mkw 0x1002aa0fe2800000 0x02f3fe5fe6000000

def z499 : W := mkw 0x100b33f862800000 0x01f3fff860000000

def z500 : W := mkw 0x000333f000000000 0x0df3fff800108000

def z501 : W := mkw 0x0f804400007fef80 0x1fd00279e07fffc0

def z502 : W := mkw 0x504bbbffff800512 0x73ffffffff800d33

def z503 : W := mkw 0x0e0377f0007fe000 0x0ca3ffb8007ff000

def z504 : W := mkw 0x0f03f7f5007fea00 0x1ff3ffff007ffe00

def z505 : W := mkw 0x46c01ca2892d4592 0x7fbc3da699ef4df3

def z506 : W := mkw 0xb22111f82283f045 0x890001f80603f00c

def z507 : W := mkw 0xb02bbbffff801045 0x9fffffffff94b2cc

def z508 : W := mkw 0x41c08807c9000f92 0x720c0007f9800ff3

def z509 : W := mkw 0x000bbbf7dd000000 0x012bfdc61e000000

def z510 : W := mkw 0x0801414000528000 0x0df3c3f8007ff000

def z511 : W := mkw 0x0003bbf7c0000000 0x1ff3ffffe01cf3c0

def z512 : W := mkw 0xefe04400007d5fd7 0xfc040000007fffff

def z513 : W := mkw 0xb020000822801045 0xed0c0078079cf00f

def z514 : W := mkw 0x100aaa0fff800000 0x02fbfe07ff800000

def z515 : W := mkw 0x0f83fff7c07fef80 0x16f3ff87e07f0fc0

def z516 : W := mkw 0x0901c14514528a28 0x8d7fc1c61e738c3c

def z517 : W := mkw 0x0003ab47d4000000 0x03fbffc7fe000000

def z518 : W := mkw 0x000111e000000000 0x01f3fde000000000

def z519 : W := mkw 0x020014a000294000 0x7fbc3da081eb4103

def z520 : W := mkw 0x0e0377f0007fe000 0x01f3fff8001cf000

def z521 : W := mkw 0x0000000000000000 0x14000000001c03c0

def z522 : W := mkw 0xbda0440822fc1fc5 0xffdc0279e7fcffcf

def z523 : W := mkw 0x1e0bffffffffe000 0x0ffbfffffffff000

def z524 : W := mkw 0x0002ae07c0280500 0x16f3fe07e07c0fc0

def z525 : W := mkw 0x100bbbffff800000 0x83fbffffff90820c

def z526 : W := mkw 0x000333f00002a000 0x01f3fff80000b000

def z527 : W := mkw 0x0f004400007fea28 0x9c04000000738e3c

def z528 : W := mkw 0xa02bbbf7dd001045 0xfc27fd86181cf3cf

def z529 : W := mkw 0x0482ae07c02c0580 0x16f3fe07e01c03c0

def z530 : W := mkw 0x100b33f83f800000 0x01fbfff81f800000

def z531 : W := mkw 0x0e0377f0007fe000 0x1df3fff8007ff3c0

def z532 : W := mkw 0x0e037ff2897fe000 0x0ffbfffe99fff000

def z533 : W := mkw 0x4b40440000794f12 0x7c040000007b4f33

def z534 : W := mkw 0xb022aa0fe2801045 0xf2fffe07e78003cf

def z535 : W := mkw 0xb02bbbffff801045 0x60a3ffbef98c71c3

def z536 : W := mkw 0x100bbbffff828028 0x9fffffffffe38c3c

def z537 : W := mkw 0x0d82ee07c07c0a80 0x06f3fe07e07c02c0

def z538 : W := mkw 0xb022baafeb801045 0xffffffffff9cf3cf

def z539 : W := mkw 0x0e004400007fe000 0x00000000001cf000

def z540 : W := mkw 0x0e004400007fe000 0x9c040000007ff20c

def z541 : W := mkw 0x0901c14514528a28 0xff7fc1c71e7bcf3f

def z542 : W := mkw 0x01808807d4000fa8 0x920c0007fe000ffc

def z543 : W := mkw 0x0901c14514528a28 0x9f7fc3c77e778efc

def z544 : W := mkw 0x0d82ee17c07c2f80 0x16f3fe1fe07c3fc0

def z545 : W := mkw 0xb02bbbffff801045 0xefffffffff9cf00f

def z546 : W := mkw 0x0e0377f0007fe000 0x0ffbfff881fff000

def z547 : W := mkw 0x000333f000000000 0x0063ffd800000000

def z548 : W := mkw 0x060236b0002d6000 0x0dd03e78001cf000

def z549 : W := mkw 0x1003bbffe2800000 0x03fbffffe7800000

def z550 : W := mkw 0x4fc2fea7c97d4f92 0x16f3ff87f87f0ff0

def z551 : W := mkw 0x0003235000000000 0x0043c2580014b000

def z552 : W := mkw 0x000bbbf7dd000000 0x00a3ff86f8000000

def z553 : W := mkw 0x1f8bffffffffef80 0x1ffbffffffffffc0

def z554 : W := mkw 0x46c23ea2c92d4592 0x7fbc3fa6f9ef4df3

def z555 : W := mkw 0x42401ca289294512 0x73bc3da699e30d33

def z556 : W := mkw 0x0002aa07c0000000 0x0223fc07e0000000

def z557 : W := mkw 0x0900400000500a00 0x1400000000700e00

def z558 : W := mkw 0x0000000000000000 0x9fdc0279061cf20c

def z559 : W := mkw 0x0d804400007c0f80 0x00000000001c03c0

def z560 : W := mkw 0x020232b000016000 0x00803e3800007000

def z561 : W := mkw 0x404bbbf7dd000512 0x0023fd8618000c30

def z562 : W := mkw 0x42401ca289294512 0x722c3d8699e30d33

def z563 : W := mkw 0x0901c14514528a28 0x9f3fc1871e630e3c

def z564 : W := mkw 0x080373f000528000 0x0df3fff8007ff000

def z565 : W := mkw 0x0e004400007fe000 0x1f3c0186187ffc30

def z566 : W := mkw 0x0b03f3f51453ea28 0x9fffffff1e73fe3c

def z567 : W := mkw 0x0e0377f0007fe000 0x0df3fff8e07ff1c0

def z568 : W := mkw 0x020333f000016000 0x01f3fff800007000

def z569 : W := mkw 0x100bb3fd76800000 0x03fbffff7e000000

def z570 : W := mkw 0xb12bbbffff801a6d 0xffffffffff9cffff

def z571 : W := mkw 0x0001014000000000 0x0173c1c000000000

def z572 : W := mkw 0x0903f3f514528a28 0x9fffffff1e738e3c

def z573 : W := mkw 0x42401ca289294512 0x72ac3da699eb4d33

def z574 : W := mkw 0x0b01d1f51453ea28 0x9f7fc1ff1e73fe3c

def z575 : W := mkw 0x000bbbf7dd000000 0x01f3fffe18000000

def z576 : W := mkw 0x0e0377f0007fe000 0x1ff3fff9007ff200

def z577 : W := mkw 0x0900c00514500a28 0x967fc0071e700e3c

def z578 : W := mkw 0x0000000000000000 0x1fd00279e01cf3c0

def z579 : W := mkw 0x0002a20540000000 0x00f3fe0160000000

def z580 : W := mkw 0xb921c14d36d29a6d 0xff7fc1c7fff38fff

def z581 : W := mkw 0xb02911f83f801045 0xe10c01f81f80000f

def z582 : W := mkw 0x0c826e02c07c0580 0x16f3fe01e07c03c0

def z583 : W := mkw 0x0f004400007fea28 0x9c040000007ffe3c

def z584 : W := mkw 0x0f82ee07c07fefa8 0x9ef7fe07e07ffffc

def z585 : W := mkw 0x000b3bf2c9000000 0x01f3fff800000000

def z586 : W := mkw 0x0900c00514500a28 0x960c00071e700e3c

def z587 : W := mkw 0x0e0377f0007fe000 0x0ffbfff9067ff000

def z588 : W := mkw 0xb020000822801045 0xf60c0001e79c03cf

def z589 : W := mkw 0x000018a289000000 0x00203d8618000000

def z590 : W := mkw 0x424bbff7dd294512 0x7fbffda699eb4d33

def z591 : W := mkw 0x118bbbffff800f80 0x13fbffffff800fc0

def z592 : W := mkw 0x0d82ee07c07c0f80 0x12f3fe07e0600fc0

def z593 : W := mkw 0x0c0373f00056a000 0x00c3fe780014b000

def z594 : W := mkw 0x0d80cc07c07c0f80 0x16d00207e07c0fc0

def z595 : W := mkw 0x0f804400007fefa8 0x9c040000007ffffc

def z596 : W := mkw 0x46423eb2892d6512 0x60803e38818c7103

def z597 : W := mkw 0x4f404400007fef3a 0xfc040000007fff3f

def z598 : W := mkw 0x514bbbffff800f3a 0xf3ffffffff800f3f

def z599 : W := mkw 0x000333f000000000 0x0173fdc000000000

def z600 : W := mkw 0x424333f009014012 0x69fffff819834033

def z601 : W := mkw 0x100bbbffff800000 0x03fbffffff94b000

def z602 : W := mkw 0x0d814540147e8fa8 0x9d0c01c01e7f8ffc

def z603 : W := mkw 0x1000000822800000 0x9fdc0279e790820c

def z604 : W := mkw 0x100bbbffff800000 0x03fbffffff9402c0

def z605 : W := mkw 0x43c09ca7c9294f92 0x7fbc3da7f9eb4ff3

def z606 : W := mkw 0x0d82ee07c07e8fa8 0x9ffffe47e67f8ffc

def z607 : W := mkw 0x0f83f7f5407fea80 0x0df3fff9607ff2c0

def z608 : W := mkw 0x0003ab57c0000000 0x02f3fe5fe0000000

def z609 : W := mkw 0x090bfbf7dd528a28 0x0023fd8618630c30

def z610 : W := mkw 0xb02ba35d76801045 0xffdfc279e79cf3cf

def z611 : W := mkw 0xb02b33f83f801045 0xedfffff81f9cf00f

def z612 : W := mkw 0xb02b3bfaeb801045 0xfffffff9e79cf3cf

def z613 : W := mkw 0x4e437ff2897fe512 0x0df3fffe187ffc30

def z614 : W := mkw 0x42401ca289294512 0x7fbc3da699fffd33

def z615 : W := mkw 0xb22bbbffff83f045 0xebffffffff83f00f

def z616 : W := mkw 0x0e0377f0007fe000 0x0dd3fe78001cf000

def z617 : W := mkw 0x0901c14514528a28 0x9fffc1c79e7b8f3c

def z618 : W := mkw 0x0e004400007fe000 0x0d000078007ff000

def z619 : W := mkw 0x42401ca289294512 0x7fbc3fa6f9ef4df3

def z620 : W := mkw 0x0e0377f0007fe000 0x0023fdd80063b000

def z621 : W := mkw 0x0e0377f0007fe000 0x0ff3fff9e07ff000

def z622 : W := mkw 0x0902ea07c0500a00 0x16f3fe07e07c0fc0

def z623 : W := mkw 0xb02bbbffff801045 0xffffffffff88f10f

def z624 : W := mkw 0x100aaa0fff800000 0x022bfc07ff800000

def z625 : W := mkw 0xa02333f000001045 0xfdf7fff8001cf3cf

def z626 : W := mkw 0x100bbbffff800000 0x9fffffffff90820c

def z627 : W := mkw 0x118bbbffff800f80 0x03fbffffff800c00

def z628 : W := mkw 0x0e0377f0007fe000 0x0db3ffb8006f7000

def z629 : W := mkw 0xb020000822801045 0xff5c0041e79083cf

def z630 : W := mkw 0x42401ca289294512 0x602c3d8619e30c33

def z631 : W := mkw 0x4fc2ee07c07d4f92 0x7ffffe27e1ff4ff3

def z632 : W := mkw 0xbc20440822fc1045 0xffdc0279e7fcf3cf

def z633 : W := mkw 0xbc22660822fc1045 0xf6fffe01e7fc03cf

def z634 : W := mkw 0x0f0377f0007fea00 0x1df3fff8007ffe00

def z635 : W := mkw 0x100bbbffff800000 0x03fbffffff8c7000

def z636 : W := mkw 0x100bb3fd3f800000 0x03fbffff1f800000

def z637 : W := mkw 0xbc22660822fc1045 0xedfffe7807fcf00f

def z638 : W := mkw 0x060337f0002d6000 0x0df3fff8001cf000

def z639 : W := mkw 0x0d82e605407c0a80 0x16f3fe07607c0ec0

def z640 : W := mkw 0xae204400007ff045 0x6c000000007ff1c3

def z641 : W := mkw 0x0f8377f0007fea80 0x0df3fff8007ff2c0

def z642 : W := mkw 0x100bbbffff800000 0x00a3ffbef9800000

def z643 : W := mkw 0x0d82ee07d47c0fa8 0x96f3fe07e67c0fcc

def z644 : W := mkw 0x0d804400007c0f80 0x1c000000007cffc0

def z645 : W := mkw 0xbe20440822fff045 0xfe0c0001e7fff3cf

def z646 : W := mkw 0xb02ababfeb801045 0xfffffe7fe79cf3cf

def z647 : W := mkw 0x020111f01403e028 0x890c01f81e03f03c

def z648 : W := mkw 0xb92bfbffffd29a6d 0xffffffffffffffff

def z649 : W := mkw 0x0e0377f0007fe000 0x9df7fff8007ff20c

def z650 : W := mkw 0x0000000000000000 0x9f7c01c71e738e3c

def z651 : W := mkw 0x1d8bef5ff6fc0f80 0x16f3fe5fe67c0fc0

def z652 : W := mkw 0xb02bbbffff801045 0xe92ffdfe1f80f00f

def z653 : W := mkw 0x000911f01d000000 0x0000018018000000

def z654 : W := mkw 0x0f004400007fea28 0x0c000000007ffc30

def z655 : W := mkw 0x0002aa07c0000000 0x1fffff87f8630c30

def z656 : W := mkw 0x0e0377f0007fe000 0x9fffffff1e7ffe3c

def z657 : W := mkw 0x0e0377f0007fe000 0x0043fe580014b000

def z658 : W := mkw 0x000bbbf7dd000000 0x7fbffda699884103

def z659 : W := mkw 0x0e0377f0007fe000 0x8dfffff8067ff00c

def z660 : W := mkw 0xb028880fff801045 0x82080007ff8002cc

def z661 : W := mkw 0xae204400007ff045 0xfc040000007ff3cf

def z662 : W := mkw 0x42401ca289294512 0x7e2c3d8699eb4d33

def z663 : W := mkw 0xb02911f83f801045 0x810801f81f80b00c

def z664 : W := mkw 0x0e004400007fe000 0x1c040000007ffc30

def z665 : W := mkw 0xf068880fff801557 0xf20c0007ff800fff

def z666 : W := mkw 0x000a3ab2c9000000 0x00003c0000000000

def z667 : W := mkw 0x0900400000528a28 0x9f5c004106738e3c

def z668 : W := mkw 0x100bbbffff800000 0x13ffffffff800c30

def z669 : W := mkw 0x0183bbf7c0000f80 0x13f3ffffe0000fc0

def z670 : W := mkw 0x0d82e20540540a80 0x16d3c201e01c03c0

def z671 : W := mkw 0x0000000000000000 0x9fdc0241e61c83cc

def z672 : W := mkw 0x42401ca289294512 0xffbc3da79feb4f3f

def z673 : W := mkw 0x4b405ca2897bcf3a 0xffbc3da699fbcf3f

def z674 : W := mkw 0xbdabfffffffc1fc5 0xfffffffffffcffcf

def z675 : W := mkw 0x100333f822800000 0x01f3fff966000000

def z676 : W := mkw 0x0e0377f0007fe000 0x0023ff9800673000

def z677 : W := mkw 0x0c02ee07c07c0000 0x06f3fe07e07c0000

def z678 : W := mkw 0x0900c00500500a00 0x1f7fc18718730e30

def z679 : W := mkw 0x0102aa07d4000a28 0x92fffe07fe000e3c

def z680 : W := mkw 0x0003a34514000000 0x03fbffc71e000000

def z681 : W := mkw 0xbe2155f822fff045 0xfd0c01f807fff3cf

def z682 : W := mkw 0x0d01c1451456aa28 0x9f7fc1c71e77be3c

def z683 : W := mkw 0x100bbbffff828028 0x03fbffffff830030

def z684 : W := mkw 0x00033bf2c0000000 0x01f3fff8e0000000

def z685 : W := mkw 0x0982ea07c0500f80 0x16f3fe07e0700fc0

def z686 : W := mkw 0xb023ab4ff6801045 0xffffffffff9cf3cf

def z687 : W := mkw 0x42401ca289294512 0x7f3c3d8699e30d33

def z688 : W := mkw 0xb0200c0aa2a81545 0xfffc3e7fe7fcffcf

def z689 : W := mkw 0x1002baafeb800000 0x03fbffffff800000

def z690 : W := mkw 0x0901c14514528a28 0x8023c1871e630e3c

def z691 : W := mkw 0x0003b3f514000000 0x03fbffff1e000000

def z692 : W := mkw 0x100bbbffff800000 0x7fffffffff884103

def z693 : W := mkw 0x000bbbf7dd000000 0x1f3ffd8618630c30

def z694 : W := mkw 0x000333f000000000 0x01b3fda000000000

def z695 : W := mkw 0x0000000000000000 0x0c000000001cf000

def z696 : W := mkw 0x0003235000000000 0x00f3fe5800000000

def z697 : W := mkw 0x0082aa07c0000580 0x02f3fe07e00001c0

def z698 : W := mkw 0x0c004400007c0500 0x14000000007c0d00

def z699 : W := mkw 0x0002aa07c0000000 0x02f3fe07e00c01c0

def z700 : W := mkw 0xbda2ee0fe2fc1fc5 0xf6fffe07e7fc0fcf

def z701 : W := mkw 0x0901414000528a28 0x9d77c1c000738e3c

def z702 : W := mkw 0x424014a009294012 0x6dbc3da019eb4033

def z703 : W := mkw 0x060337f0002d6000 0x0df3fff8006f7000

def z704 : W := mkw 0x0180000000000f80 0x1000000000000fc0

def z705 : W := mkw 0x0d80400000540a80 0x00000000001402c0

def z706 : W := mkw 0x4fc2ee07c97d4f92 0x7efffe07f9ff4ff3

def z707 : W := mkw 0xb02bbbffff801045 0xfbffffffff80f3cf

def z708 : W := mkw 0x43c2bea7c9294f92 0x7fffffa7f9eb4ff3

def z709 : W := mkw 0x000bbbf7dd028028 0x892ffdc61e03803c

def z710 : W := mkw 0x0e0377f0007fe000 0x0d73fdf80073f000

def z711 : W := mkw 0x0a0151f00053e000 0x0d73c1f80073f000

def z712 : W := mkw 0x0d82ee07d47e8fa8 0x9efffe07fe7f8ffc

def z713 : W := mkw 0x0d82ea07c0540a80 0x0063fe07601402c0

def z714 : W := mkw 0x46c23ea2c92d4592 0x60803e20e18c41c3

def z715 : W := mkw 0x0d82e605407c0a80 0x16f3fe01e07c03c0

def z716 : W := mkw 0x0c004400007c0000 0x0000000000600000

def z717 : W := mkw 0x424bbff7dd294512 0x0023fd8618630c30

def z718 : W := mkw 0x0d82ee07c07c0fa8 0x96f7fe07e07c0ffc

def z719 : W := mkw 0x04822e02c02c0580 0x16b03e06e06c0dc0

def z720 : W := mkw 0x0d804400007c0f80 0x14400201607c0fc0

def z721 : W := mkw 0x1000000822800000 0x0fd80279e79cf000

def z722 : W := mkw 0x4c436b528956a512 0x724fc25e9994bd33

def z723 : W := mkw 0x0002aa07c0000000 0x03fbfe27e1800000

def z724 : W := mkw 0x090bfbf7dd528a28 0x9f7ffdc71e738e3c

def z725 : W := mkw 0x0002aa07c0000000 0x16f3fe07e0600c00

def z726 : W := mkw 0x0003bbf7c0000000 0x0023fd8600000000

def z727 : W := mkw 0x0100800500000a00 0x1273c00700000e00

def z728 : W := mkw 0xb02bb3fd76801045 0xfffffff9e79cf3cf

def z729 : W := mkw 0x0e03fff7c07fe000 0x1ff3ffffe07ff3c0

def z730 : W := mkw 0xb02bbbffff82906d 0xffffffffff9ff3ff

def z731 : W := mkw 0x4040080289000512 0x7f3c018699e30d33

def z732 : W := mkw 0x000bbbf7dd000000 0x00f3ff8618000000

def z733 : W := mkw 0x4dc04c02897c0f92 0x760c000699fc0ff3

def z734 : W := mkw 0x4fc04400007fcfba 0xfc040000007fcfff

def z735 : W := mkw 0x100bbbfff6800000 0x03f3ffffe6000000

def z736 : W := mkw 0x524bbbffff814012 0x6bffffffff834033

def z737 : W := mkw 0x0e0377f0007fe000 0x6dfffff801fff003

def z738 : W := mkw 0x0f82ee07c07d4f80 0x1ef3fe07e07f4fc0

def z739 : W := mkw 0x0100800514000a28 0x9f3c01871e630e3c

def z740 : W := mkw 0x0901c14514528a28 0x9f7fc1ff1e73fe3c

def z741 : W := mkw 0xada04400007c1fc5 0xfc040000007cffcf

def z742 : W := mkw 0x0901c14514528a28 0x8b7fc1c71e638c3c

def z743 : W := mkw 0x100ba35d76800000 0x00f3fe5966000000

def z744 : W := mkw 0x0e0377f0007d6000 0x05f3fff8007c7000

def z745 : W := mkw 0x0d82ee07c07c0f80 0x1ff3ff87e07f0fc0

def z746 : W := mkw 0x1e0377f822ffe000 0x0ffbfff9e7fff000

def z747 : W := mkw 0x108bbbffff800580 0x03fbffffff8001c0

def z748 : W := mkw 0xfe60440822fff557 0xffdc0279e7ffffff

def z749 : W := mkw 0x4240040000294512 0x7f3c0186186b4d33

def z750 : W := mkw 0x0180800540000a80 0x00000001600002c0

def z751 : W := mkw 0x0e0377f0007fe000 0x01f3fff800630000

def z752 : W := mkw 0x000333f000000000 0x01f3fff80014b000

def z753 : W := mkw 0xb02bbbffff801045 0x63fbffffff807003

def z754 : W := mkw 0x42401ca289294512 0x63b83da699eb4d33

def z755 : W := mkw 0x000bbbf7dd000000 0x0123fdfe18000000

def z756 : W := mkw 0xae204400007ff045 0xec040000007ff00f

def z757 : W := mkw 0x42401ca289294512 0x7ffc3ffe99eb4d33

def z758 : W := mkw 0x0903eb47d4528a28 0x9fffffc7fe738e3c

def z759 : W := mkw 0x0002aa07c0000000 0x0063fe0760000000

def z760 : W := mkw 0x4a404400007bc512 0x7c040000007bcd33

def z761 : W := mkw 0x0d82ee07c07c0f80 0x1673fe0760740ec0

def z762 : W := mkw 0xf26010a82b815057 0xe90c01f81f83f03f

def z763 : W := mkw 0xb020000822801045 0xfffc03ffff9cf3cf

def z764 : W := mkw 0x0e026600007fe000 0x0cf3fe00007ff000

def z765 : W := mkw 0x0f0155f0147fea28 0x9d0c01f81e7ffe3c

def z766 : W := mkw 0x100bab5ff6800000 0x00c3fe59e6000000

def z767 : W := mkw 0x0d804400007c0f80 0x16300006007c0fc0

def z768 : W := mkw 0xb02bbbffff801045 0xf3ffffffff8c73cf

def z769 : W := mkw 0xafa04400007fffc5 0xfc040000007fffcf

def z770 : W := mkw 0xb020000822801045 0xf3dc0279e78003cf

def z771 : W := mkw 0xb02bbbffff801045 0xf3ffffffff94b3cf

def z772 : W := mkw 0x0e0377f0007fe000 0x1ff3fffe007ffc00

def z773 : W := mkw 0xb02bbbffff801045 0xffffffffffffffff

def z774 : W := mkw 0x000bbbf7dd000000 0x0003fc0000000000

def z775 : W := mkw 0x4e405ca2897fe512 0x7fbc3da699fffd33

def z776 : W := mkw 0x0d82ee07c07c0f80 0x0023fe0660640cc0

def z777 : W := mkw 0x0d804400007c0f80 0x9f5c0041067c8fcc

def z778 : W := mkw 0xb02333f822801045 0x61f3fff8e18c71c3

def z779 : W := mkw 0x000098a789000000 0x03fbfda799800000

def z780 : W := mkw 0x0003b3f540000000 0x01f3fff960000000

def z781 : W := mkw 0x0901c14514528a28 0x9673c1c71e738e3c

def z782 : W := mkw 0x020014a000294000 0x00203d8000630000

def z783 : W := mkw 0x0900c00514528a28 0x9e0c00071e738e3c

def z784 : W := mkw 0x4042aa07c9000512 0x72fffe07f9800d33

def z785 : W := mkw 0x100bbbffff800000 0x02f3ffbff9800000

def z786 : W := mkw 0x1d8bfbffffd40a80 0x03fbffffff9402c0

def z787 : W := mkw 0x504bbbffff800512 0x03fbffffff800c30

def z788 : W := mkw 0x4e404400007fe512 0x0c000000007ffc30

def z789 : W := mkw 0xb020000822801045 0x7f9c0238e18c71c3

def z790 : W := mkw 0x0482ae07c02c0580 0x16f3fe07e06c0dc0

def z791 : W := mkw 0x100b33f83f800000 0x012bfdf81f800000

def z792 : W := mkw 0xb02bab5ff6801045 0xfffffe7fe79cf3cf

def z793 : W := mkw 0x0482220040040080 0x00000200600400c0

def z794 : W := mkw 0x000333f000000000 0x03fbfff906000000

def z795 : W := mkw 0xada2ee07c07c1fc5 0xfef7fe07e07cffcf

def z796 : W := mkw 0xf26a3ebaeba95557 0x60803e38e18c71c3

def z797 : W := mkw 0xb920c00d22d01a45 0xffffc27fe7fcffcf

def z798 : W := mkw 0x120bbbffff83e028 0x8bffffffff83f03c

def z799 : W := mkw 0xb128880fff801a6d 0xf20c0007ff800fff

def z800 : W := mkw 0x0a004400007bc000 0x0c000000007bc000

def z801 : W := mkw 0x000bbbf7dd000000 0x0023fd8618630c30

def z802 : W := mkw 0x020000000003e000 0x080000000003f000

def z803 : W := mkw 0xb22333f82283f045 0xebfffff9e783f00f

def z804 : W := mkw 0x0200040000294000 0x0c000000006b4000

def z805 : W := mkw 0x0003bbf79d000000 0x03fbffff9f800000

def z806 : W := mkw 0x0002aa07c0000000 0x03fbff87f8000000

def z807 : W := mkw 0xb1a8880fff801fc5 0xf20c0007ff800fcf

def z808 : W := mkw 0xb02bbbffff801045 0x8063ffdf7e14b2cc

def z809 : W := mkw 0x0d82e605407c0a80 0x00c3fe01601c02c0

def z810 : W := mkw 0x0001814514028028 0x8b7fc1c71e03803c

def z811 : W := mkw 0x0c026600007c0000 0x0023fc0000600000

def z812 : W := mkw 0x100bab5ff6800000 0x03fbffdffe000000

def z813 : W := mkw 0x0901c14514528a28 0x9f7fc1c71e7f8ffc

def z814 : W := mkw 0xb020000822801045 0xfffc03f9e7fff3cf

def z815 : W := mkw 0x42419de79d294512 0x7ffffde79feb4d33

def z816 : W := mkw 0xf6e23eaaebad55d7 0x60803e38e18c71c3

def z817 : W := mkw 0x100bbbffff800000 0x0023fdde1e000000

def z818 : W := mkw 0x0d804400007c0f80 0x9c040000007c8fcc

def z819 : W := mkw 0x100bbbffff800000 0x0023fd877e000000

def z820 : W := mkw 0xb020000822801045 0xff5c00790790f20f

def z821 : W := mkw 0xf26bbbffff815057 0xffffffffff9ff3ff

def z822 : W := mkw 0x0e0377f0147fe028 0x0df3fff8187ff030

def z823 : W := mkw 0x100bbbffff800000 0x0023fd86f9800000

def z824 : W := mkw 0x100b3bfaeb800000 0x00c3fe78e1800000

def z825 : W := mkw 0x100bbbffff800000 0x8bffffffff80800c

def z826 : W := mkw 0x0d80cc07d47e8fa8 0x9e0c0007fe7f8ffc

def z827 : W := mkw 0x524bbbffff83c03a 0xebffffffff83c03f

def z828 : W := mkw 0x0002220000000000 0x02f3fe01e0000000

def z829 : W := mkw 0x000abab7c9000000 0x0023fc0600000000

def z830 : W := mkw 0x0d82e605407c0f80 0x1443c201607c0fc0

def z831 : W := mkw 0x0c004400007c0000 0x0dd00278007cf000

def z832 : W := mkw 0x524ba75d76a94512 0x7c47c259666b4d33

def z833 : W := mkw 0x0d83e3554056aa80 0x0043c2596014b2c0

def z834 : W := mkw 0xb020000822801045 0xe00c00000780000f

def z835 : W := mkw 0x0003ab47d4000000 0x037bfdc71e000000

def z836 : W := mkw 0x0e004400007fe000 0x0d500040007ff000

def z837 : W := mkw 0x000bbbf7dd000000 0x02b3fd8698000000

def z838 : W := mkw 0x000333f000000000 0x17f3fff9e01c03c0

def z839 : W := mkw 0x000018a289000000 0x1fbc3da699e30c30

def z840 : W := mkw 0x0f8377f0007fefa8 0x9df7fff8007ffffc

def z841 : W := mkw 0x110bbbffff800a28 0x9fffffffffe30e3c

def z842 : W := mkw 0x0d82ee07c07c0f80 0x0023fc06e0600dc0

def z843 : W := mkw 0x0901c14514528a28 0x9f7fc1c7fe738ffc

def z844 : W := mkw 0x0102aa07c0000a00 0x12f3fe07e0000e00

def z845 : W := mkw 0x100bbbffff800000 0x03bbffbef9800000

def z846 : W := mkw 0x000333f000000000 0x00a3ffb800000000

def z847 : W := mkw 0x42401ca289294512 0x6bbc3da699e34c33

def z848 : W := mkw 0xf060080aab801557 0xf20c0007ff800fff

def z849 : W := mkw 0x42401ca289294512 0x7fbc3da7f9eb4ff3

def z850 : W := mkw 0xb02333f822801045 0xe9fffff80780f00f

def z851 : W := mkw 0x0d8aee07dd7c0f80 0x16f3fe07f87c0fc0

def z852 : W := mkw 0x0e004400007fe028 0x8c040000007ff03c

def z853 : W := mkw 0x0d804400007c0f80 0x7f9c002081fc4fc3

def z854 : W := mkw 0x0d82ee07c07c0f80 0x02f3fe07e06c0dc0

def z855 : W := mkw 0xb020000822801045 0x9f5c02596614b2cc

def z856 : W := mkw 0x4fc2ee07c07d4f92 0x7fffff87f87f4ff3

def z857 : W := mkw 0x00022a02c0000000 0x00803e00e0000000

def z858 : W := mkw 0xb1a2aa0fe2801fc5 0xfffffe7fe79cffcf

def z859 : W := mkw 0x42401ca289294512 0x60203da619e34c33

def z860 : W := mkw 0x0d82fea7c97c0f80 0x17fbffa7f9fc0fc0

def z861 : W := mkw 0x0900c00500500a00 0x9f7fc04706708e0c

def z862 : W := mkw 0x060236b0002d6000 0x00f3fe38000c7000

def z863 : W := mkw 0x000bb3f554000000 0x0023fd8000000000

def z864 : W := mkw 0x42401ca289294512 0xfffc3fe7ffffcfff

def z865 : W := mkw 0x0000040000280500 0x1400000000680d00

def z866 : W := mkw 0x100b3bfaeb800000 0x03fbfffef9800000

def z867 : W := mkw 0x000111f000000000 0x010001f800000000

def z868 : W := mkw 0x0003ab47d4000000 0x02f3ff87f8000000

def z869 : W := mkw 0x160a3ebaebad6000 0x00803e38e18c7000

def z870 : W := mkw 0x0e0373f00057e000 0x09f3fff80017f000

def z871 : W := mkw 0x0c0040000056a000 0x000000000014b000

def z872 : W := mkw 0x404018a289000512 0x73bc3da699800d33

def z873 : W := mkw 0x4fc05ca2897d4f92 0x7fbc3da699ff4ff3

def z874 : W := mkw 0x0d82ee07c07c0f80 0x7ffffe7fe1fcffc3

def z875 : W := mkw 0x0d83ef47c07e8f80 0x1ff3ffc7e07f8fc0

def z876 : W := mkw 0xac204400007c1045 0xfc040000007cf3cf

def z877 : W := mkw 0x0d82ee07d47c0f80 0x16fbfe07fe7c0fc0

def z878 : W := mkw 0x0d82ee07c07e8fa8 0x16f3fe07e07f0ff0

def z879 : W := mkw 0x0003235000000000 0x0043c25800000000

def z880 : W := mkw 0x0f804400007fef80 0x14000000007f0fc0

def z881 : W := mkw 0xb020000822801045 0x6000003801807003

def z882 : W := mkw 0x0d82ee07d47c0fa8 0x9ffffe47fe7c8ffc

def z883 : W := mkw 0x020bbbf7dd03e000 0x0923fdfe1803f000

def z884 : W := mkw 0x4e4377f0097fe012 0x7ffffffe19fffc33

def z885 : W := mkw 0x0e0377f0007fe000 0x09a3fff8006ff000

def z886 : W := mkw 0x0d804400007c0f80 0x7c040000007c4fc3

def z887 : W := mkw 0x0c026600007c0000 0x04f3fe58007cb000

def z888 : W := mkw 0x0a0155f0007be000 0x0df3fdf8007bf000

def z889 : W := mkw 0x00022a0280000000 0x02f3fe0680000000

def z890 : W := mkw 0x00033bf289000000 0x03bbfda699800000

def z891 : W := mkw 0x100999ffbf800000 0x03fbfdff9f800000

def z892 : W := mkw 0x020337f000294000 0x0df3fff8007ff000

def z893 : W := mkw 0x42401ca289294512 0x7f3c3da619e34c33

def z894 : W := mkw 0x100bbbffff800000 0x1fffffffffe30c30

def z895 : W := mkw 0xf160880fbf801f7f 0xf20c0007ff800fff

def z896 : W := mkw 0x0d804400007c0f80 0x14800200e07c0fc0

def z897 : W := mkw 0x100bbbffff800000 0xffffffffff98c30f

def z898 : W := mkw 0x0582ae07c02c0f80 0x12f3fe07e00c0fc0

def z899 : W := mkw 0x0e026610007fe000 0x0c000218007ff000

def z900 : W := mkw 0xb020000822801045 0x8dd00279661cf2cc

def z901 : W := mkw 0xb02bbbffff801045 0xf22ffd87ff8003cf

def z902 : W := mkw 0x0e0276a0007d4000 0x0df3fff8007ff000

def z903 : W := mkw 0x0801414000528000 0x9f7fc1c10673820c

def z904 : W := mkw 0xbda0440822fe9fed 0xffdc0279e7ffffff

def z905 : W := mkw 0xf1e0880feb801fd7 0xf20c0007ff800fff

def z906 : W := mkw 0x0e0377f0007fe000 0x0df3fff9607ff2c0

def z907 : W := mkw 0x000333f000000000 0x0df3fff800084000

def z908 : W := mkw 0xb1a0880ff6801fed 0xf20c0007ff800fff

def z909 : W := mkw 0x000b3bf2c9000000 0x0023fd8000000000

def z910 : W := mkw 0x020333f00003e000 0x0023fd8000030000

def z911 : W := mkw 0x100bb3fd7f800000 0x01fbfff97f800000

def z912 : W := mkw 0x000323500002a000 0x0043c2580000b000

def z913 : W := mkw 0x0e0276b0007d6000 0x0df3ffb8007f7000

def z914 : W := mkw 0xf26911f83f815057 0xe90c01f81f83f03f

def z915 : W := mkw 0x0d804400007c0f80 0x0000000000740ec0

def z916 : W := mkw 0x0d804400007c0f80 0x1c040000007f0ff0

def z917 : W := mkw 0x4fc04400007d4f92 0x74000000007c4fc3

def z918 : W := mkw 0x0f83fff7c07fef80 0x0df3fffe007ffc00

def z919 : W := mkw 0x0e004400007fe000 0x000000000077b000

def z920 : W := mkw 0x5e4bffffffffe512 0x7ffffffffffffd33

def z921 : W := mkw 0xb020000822801045 0xfc440259661cf3cf

def z922 : W := mkw 0x0d82ee07c07c0f80 0x0043fe01601402c0

def z923 : W := mkw 0x4dc2ee07c07c0f92 0x76f7fe07e07c0ff3

def z924 : W := mkw 0x4b41c545147bcf3a 0xff7fc1c71e7bcf3f

def z925 : W := mkw 0x0d83ef47d47e8fa8 0x96f3fe47e67c8fcc

def z926 : W := mkw 0x0d82e20540540a80 0x1673c20760740ec0

def z927 : W := mkw 0x0d82ee07c07eaf80 0x16f3fe07e07cbfc0

def z928 : W := mkw 0x000199e79d000000 0x037bfdc71e000000

def z929 : W := mkw 0xb020000822801045 0xe9cc0279e79cf3cf

def z930 : W := mkw 0x4fc2ee07c07fcfba 0xfef7fe07e07fcfff

def z931 : W := mkw 0x0d004400007c0a00 0x14000000007c0e00

def z932 : W := mkw 0x0d82ee07c07c0f80 0x12a3fe07e06c0fc0

def z933 : W := mkw 0x0c0377f0007c0000 0x0df3fff8007cf000

def z934 : W := mkw 0x100a3abaeb800000 0x00f3fe38e1800000

def z935 : W := mkw 0x4fc3ffe7dd7fcfba 0xffffffe7ffffcfff

def z936 : W := mkw 0x000bab57d4000000 0x0023fc0600000000

def z937 : W := mkw 0x0d82e20540540a80 0x00f3fe01601402c0

def z938 : W := mkw 0x42433ff289294512 0x7ffffffe99fffd33

def z939 : W := mkw 0x0d82ee07c07c0f80 0x16fffe07f87c0ff0

def z940 : W := mkw 0x120911f83f83e000 0x090801f81f83f000

def z941 : W := mkw 0x0e0377f0147fe028 0x9ffffff91e7ff23c

def z942 : W := mkw 0x0d804400007c0f80 0x1400000000680d00

def z943 : W := mkw 0x0f82feb7c07d6f80 0x16f3fe3fe07c7fc0

def z944 : W := mkw 0x100bbbffff800000 0x037bfdff1f800000

def z945 : W := mkw 0x0e004400007fe000 0x9f5c0041067ff20c

def z946 : W := mkw 0x0f804400007fef80 0x0c000000007ffc00

def z947 : W := mkw 0x000aaa07dd000000 0x02f3fe07f8000000

def z948 : W := mkw 0x100bbbffff800000 0x00e3ffffff800000

def z949 : W := mkw 0xb02bbbffff801045 0x7fffffffff8c71c3

def z950 : W := mkw 0x0002baa7c0000000 0x03f3ffa7e0000000

def z951 : W := mkw 0xb02911f83f801045 0xffdc03f9ff9cf3cf

def z952 : W := mkw 0x0e004400007fe000 0x0c00000000738000

def z953 : W := mkw 0x0d804400007e8f80 0x1c000000007f8fc0

def z954 : W := mkw 0x4b404400007bcf3a 0x7c040000006b4d33

def z955 : W := mkw 0x0900c00514500a28 0x9f7fc1871e730e3c

def z956 : W := mkw 0x4e404c02897fe512 0x7e0c000699fffd33

def z957 : W := mkw 0x100bbbffff800000 0x03dbfe79e7800000

def z958 : W := mkw 0x0002a20500000000 0x02f3fe0700000000

def z959 : W := mkw 0xb02aaa0fff801045 0xf6fffe07ff9c03cf

def z960 : W := mkw 0xb02bbbffff801045 0x83fbffffff8002cc

def z961 : W := mkw 0x0e004400007d6000 0x04000000007c7000

def z962 : W := mkw 0x0c036750007ea000 0x0063fe580074b000

def z963 : W := mkw 0x0901c14514528a28 0x802fc1861e630c3c

def z964 : W := mkw 0xb22014a822a95045 0xfffc3ff9e7fff3cf

def z965 : W := mkw 0x000018a289000000 0x7fbc3da699eb4d33

def z966 : W := mkw 0x0900c00500500a00 0x0023c00600600c00

def z967 : W := mkw 0x000bbbf7dd000000 0x0173fdc618000000

def z968 : W := mkw 0xffe0440822fd5fd7 0xffdc0279e7ffffff

def z969 : W := mkw 0x4fc2ee07c07d4f92 0x16f3fe07e07f0ff0

def z970 : W := mkw 0x100b3bfaff800000 0x01fbfff8ff800000

def z971 : W := mkw 0x0f03f7f5147fea28 0x0df3fffe187ffc30

def z972 : W := mkw 0xbda0cc0fe2fc1fc5 0xfe0c0007e7fcffcf

def z973 : W := mkw 0xb020000822801045 0x80000001660002cc

def z974 : W := mkw 0x0d82ea07c0540f80 0x1243c207e0140fc0

def z975 : W := mkw 0x0901c14514528a28 0x9fffc3c71e7f8e3c

def z976 : W := mkw 0x0e0377f0007fe000 0x01f3fff80077b000

def z977 : W := mkw 0x0d82ee07c07c0f80 0x9ffffe7fe67cffcc

def z978 : W := mkw 0x0d82ea07c0540a80 0x16f3fe07e0740ec0

def z979 : W := mkw 0x0c036750007ea000 0x0df3ffd8007fb000

def z980 : W := mkw 0x100ababfff800000 0x02fbfe3fff800000

def z981 : W := mkw 0x000bbbf7dd000000 0x033bfd8618000000

def z982 : W := mkw 0x0e036750007fe000 0x0cf3fe58007ff000

def z983 : W := mkw 0xb02bbbffff801045 0xffffffffff90f20f

def z984 : W := mkw 0x100bbbffff800000 0x02fbff87ff800000

def z985 : W := mkw 0x0e0276b0007d6000 0x00c3fe38001c7000

def z986 : W := mkw 0x424bbbf7dd014012 0x692ffda619834033

def z987 : W := mkw 0x100bbbffff800000 0x02f3fe7fe7800000

def z988 : W := mkw 0x0d82ee07c07c0f80 0x12c3fe07e01c0fc0

def z989 : W := mkw 0x42411df2892be512 0x7fbc3dfe99ebfd33

def z990 : W := mkw 0x0e0377f0007fe000 0x04f3ffd8007fb000

def z991 : W := mkw 0xada04400007c1fc5 0x94000000007cbfcc

def z992 : W := mkw 0x0e0054b0007fe000 0x0c000038007ff000

def z993 : W := mkw 0x0f00c405147fea28 0x9e0c00071e7ffe3c

def z994 : W := mkw 0x0e0377f0007fe000 0x0c23fd80007ff000

def z995 : W := mkw 0x148bbbffff840080 0x03fbffffff8400c0

def z996 : W := mkw 0x0901c1551452aa28 0x9f7fc1df1e73be3c

def z997 : W := mkw 0x524bbbffff814512 0x7bffffffff834d33

def z998 : W := mkw 0x10033bfaab800000 0x03fbffffff800000

def z999 : W := mkw 0xb020000822801045 0xfffc027fe7fcffcf

def z1000 : W := mkw 0xada04400007c1fc5 0x74000000007c7fc3

def z1001 : W := mkw 0xb020000822801045 0xfe0c0001e79cf3cf

def z1002 : W := mkw 0x000333f000000000 0x03fbfff881800000

def z1003 : W := mkw 0x0f004400007fea28 0x9fdc0279067ffe3c

def z1004 : W := mkw 0x100bbbffff800000 0x17fbffffffe00c00

def z1005 : W := mkw 0x0801414000528000 0x0023c18000630000

def z1006 : W := mkw 0x0002aa07c0000000 0x00a3fe06e0000000

def z1007 : W := mkw 0x0e0377f0147fe028 0x8df3fff8067ff00c

def z1008 : W := mkw 0x4fc2fea7c97d4f92 0x76f3fe27e1fc4fc3

def z1009 : W := mkw 0x0f03f7f5147fea28 0x8df3fff9067ff20c

def z1010 : W := mkw 0x0d8bfff7dd7c0f80 0x16f3ff87f87c0fc0

def z1011 : W := mkw 0x060337f0002fe000 0x09803ff8000ff000

def z1012 : W := mkw 0x0e0377f0007fe000 0x0c63ffd8007ff000

def z1013 : W := mkw 0x0801414014528028 0x8d0c01c01e73803c

def z1014 : W := mkw 0x0d804400007c0f80 0x16500001007c0fc0

def z1015 : W := mkw 0xae2377f0007ff045 0xfdf7fff8007ff3cf

def z1016 : W := mkw 0x42401ca289294512 0x76bc3d8699eb0d33

def z1017 : W := mkw 0x0c004400007ea000 0x04000000007cb000

def z1018 : W := mkw 0xb020000822801045 0xff9c0021e78843cf

def z1019 : W := mkw 0x100bbbffff800000 0x1fffffffff800000

def z1020 : W := mkw 0x0000800500000000 0x0273c00700000000

def z1021 : W := mkw 0x000232a000000000 0x01f3ffa000000000

def z1022 : W := mkw 0x100b3bfaeb800000 0x03fbfff9e7800000

def z1023 : W := mkw 0x100bbbffff800000 0x01fbfffe1f800000

def z1024 : W := mkw 0x0901c14514528a28 0x9fffc3c7fe738e3c

def z1025 : W := mkw 0x000bbbf7dd000000 0x022bfd8699800000

def z1026 : W := mkw 0x4e404400007fe512 0x7fdc027881fffd33

def z1027 : W := mkw 0x0d82ee07c07c0f80 0x04f3fe06e07c0dc0

def z1028 : W := mkw 0x0d03e3551456aa28 0x9f7fc3df1e77be3c

def z1029 : W := mkw 0x0e004400007fe000 0x7f9c002081fff103

def z1030 : W := mkw 0x06000400002d6000 0x00000000000c7000

def z1031 : W := mkw 0xb022aa0fe2801045 0xebfffe7fe780f00f

def z1032 : W := mkw 0xb02333f822801045 0xf3fffff9e78003cf

def z1033 : W := mkw 0x0d82ee07c07c0f80 0x04f3fe07607c0ec0

def z1034 : W := mkw 0x00033bf280000000 0x03f3fffe80000000

def z1035 : W := mkw 0x0000000000000000 0x12d00201e00003c0

def z1036 : W := mkw 0x100bbbffff800000 0x0ffbffffff908000

def z1037 : W := mkw 0x0f0377f0007fea28 0x9ffffffe187ffe3c

def z1038 : W := mkw 0x0e004400007fe000 0x1ed00201e07ff3c0

def z1039 : W := mkw 0x0c026610007c2000 0x04f3fe18007c3000

def z1040 : W := mkw 0x4e4377f0097fe012 0x0df3fff8187ff030

def z1041 : W := mkw 0xb02199efbf801045 0xffffffffff9cf3cf

def z1042 : W := mkw 0x000bbbf7dd000000 0x01b3fda618000000

def z1043 : W := mkw 0x0000000000000000 0x02d00201e0000000

def z1044 : W := mkw 0x100aaa0feb800000 0x02f3fe07e1800000

def z1045 : W := mkw 0x0f804400007d6f80 0x14000000007c7fc0

def z1046 : W := mkw 0xb22911f83f83f045 0xe90c01f81f83f00f

def z1047 : W := mkw 0x010bbbf7dd000a28 0x922ffd871e000e3c

def z1048 : W := mkw 0x100bbbffff800000 0x7fffffffffeb4d33

def z1049 : W := mkw 0x100bab5fff800000 0x02fbfe5fff800000

def z1050 : W := mkw 0x100aaa0ff6800000 0x02f3fe07e6000000

def z1051 : W := mkw 0x42400c0280294512 0x7eb43c06806b4d33

def z1052 : W := mkw 0x00022a02c0000000 0x00803e00e00c01c0

def z1053 : W := mkw 0x4dc2ee07c97c0f92 0x7fffff87f9ff0ff3

def z1054 : W := mkw 0x0901414014528a28 0x890c01c01e638c3c

def z1055 : W := mkw 0x000333f000000000 0x00c3fe7800000000

def z1056 : W := mkw 0x0d826e02c07c0f80 0x14803e00e07c0fc0

def z1057 : W := mkw 0x1c0be35d76d6a000 0x0043c2596614b000

def z1058 : W := mkw 0xb02bbbffff801045 0x77fbffffff9c73c3

def z1059 : W := mkw 0x0d004400007e8a28 0x9c040000007f8e3c

def z1060 : W := mkw 0x0000000000000000 0x01d0027800000000

def z1061 : W := mkw 0xb028880fff801045 0xffdc027fff9cf3cf

def z1062 : W := mkw 0x0000000000000000 0x004002580014b000

def z1063 : W := mkw 0x100bbbffff800000 0x0ffbffffff884000

def z1064 : W := mkw 0x0980c807c0500f80 0x1673c007e0700fc0

def z1065 : W := mkw 0x4fc04400007d4f92 0x7c040000006b4d33

def z1066 : W := mkw 0x100bbbffff800000 0x0ffbffffffe30000

def z1067 : W := mkw 0x0d82ee07c07c0f80 0x1ef3fe07e07cffc0

def z1068 : W := mkw 0x1f0bffffffffea28 0x9ffffffffffffe3c

def z1069 : W := mkw 0x000ba35554000000 0x0003c00000000000

def z1070 : W := mkw 0x4240040000294512 0x7f9c002081eb4d33

def z1071 : W := mkw 0xae204400007ff045 0x8c000000007ff2cc

def z1072 : W := mkw 0x46423eb2892d6512 0x7fbc3fbe99ef7d33

def z1073 : W := mkw 0x0d82ee07c07c0f80 0x16d3fe01e01c03c0

def z1074 : W := mkw 0x4b4155e01d7bcf3a 0xfd0c01e01ffbcf3f

def z1075 : W := mkw 0x0d804c02c07c0f80 0x14000000e07c0fc0

def z1076 : W := mkw 0x160bbfffffad6000 0x03fbffffff8c7000

def z1077 : W := mkw 0x118bbbffff800f80 0x17fbffffff9c0fc0

def z1078 : W := mkw 0x0002aa07c0000000 0x0ff3fe7fe01cf000

def z1079 : W := mkw 0x118bbbffff800fa8 0x93ffffffff800ffc

def z1080 : W := mkw 0x0203b3f51403e028 0x8bffffff1e03f03c

def z1081 : W := mkw 0xf2601caaaba95557 0xffbc3dfe9febfd3f

def z1082 : W := mkw 0x0000000000000000 0xffdc00618798c30f

def z1083 : W := mkw 0x0e0054a0007fe000 0x0db03da0007ff000

def z1084 : W := mkw 0x000199e79d000000 0x03fbfde79f800000

def z1085 : W := mkw 0xb02111f822801045 0xe90c01f80780f00f

def z1086 : W := mkw 0x000333f000000000 0x03f3fff9e0000000

def z1087 : W := mkw 0x100bbbffff800000 0x02abffbfff800000

def z1088 : W := mkw 0x0d82ee07d47c0fa8 0x16f3fe07f87c0ff0

def z1089 : W := mkw 0xb023bbffe2801045 0xffffffffe79cf3cf

def z1090 : W := mkw 0xb02bbbffff801045 0x97fbffffff9cb3cc

def z1091 : W := mkw 0x000333f014000000 0x01fbfff81e000000

def z1092 : W := mkw 0x504bbbffff800512 0x63fbffffff800103

def z1093 : W := mkw 0xf26111e83f83d07f 0xe90c01f81f83f03f

def z1094 : W := mkw 0x4e404400007fe512 0x6c000000007ff103

def z1095 : W := mkw 0x0c004400007c0000 0x0c000000007cf000

def z1096 : W := mkw 0x42401ca289294512 0x7fbc3dfe99ebfd33

def z1097 : W := mkw 0x0c026600007c0000 0x04f3fe01607c02c0

def z1098 : W := mkw 0x0e0377f0007fe028 0x8df7fff8007ff03c

def z1099 : W := mkw 0x0000000000000000 0x12000001e00003c0

def z1100 : W := mkw 0x0001814514028028 0x9f7fc1c71e638c3c

def z1101 : W := mkw 0x020337f0002be000 0x0df3fff8006bf000

def z1102 : W := mkw 0x100bbbffff800000 0x03bbfdfe9f800000

def z1103 : W := mkw 0x4b40cc079d7bcf3a 0xfe0c00079ffbcf3f

def z1104 : W := mkw 0x100bbbffff800000 0x03bbfda7ff800000

def z1105 : W := mkw 0x100ababfeb800000 0x03fbfe7fe7800000

def z1106 : W := mkw 0xbf20440822fffa6d 0xffdc0279e7ffffff

def z1107 : W := mkw 0x0d82ea07c0540a80 0x00c3fe01e01402c0

def z1108 : W := mkw 0x100bbbffff800000 0x1ffbffffff9cf3c0

def z1109 : W := mkw 0x0000000000000000 0x00400201601402c0

def z1110 : W := mkw 0x000333f000000000 0x0df3fff800630000

def z1111 : W := mkw 0x000bbbf7dd000000 0x022bfd871e000000

def z1112 : W := mkw 0xbd23e35d36d6ba6d 0x8043c2596614b2cc

def z1113 : W := mkw 0xbe20440822fff045 0x6c800238e1fff1c3

def z1114 : W := mkw 0xbda0440822fc1fc5 0xf60c0001e7fc0fcf

def z1115 : W := mkw 0x0c82ee07c07c0580 0x06f3fe07e07c01c0

def z1116 : W := mkw 0x000199e79d000000 0xfffffde79f98c30f

def z1117 : W := mkw 0x0d82ee07c07c0f80 0x1423fc06007c0fc0

def z1118 : W := mkw 0x4040080289000512 0x7f9c002699884d33

def z1119 : W := mkw 0x0f004400007fea28 0x8c000000007ff20c

def z1120 : W := mkw 0x0e0377f0007fe000 0x6df3fff881fff103

def z1121 : W := mkw 0xa020000000001045 0xfdd40278001cf3cf

def z1122 : W := mkw 0x0c826600407c0080 0x04f3fe00607c00c0

def z1123 : W := mkw 0x0d82e605407c0a80 0x0063fe01607402c0

def z1124 : W := mkw 0x0981c14554528aa8 0x9f7fc1c77e738efc

def z1125 : W := mkw 0xbda0440822fc1fc5 0xfd0c007807fcffcf

def z1126 : W := mkw 0x0d81c14514568aa8 0x9f7fc1c71e778efc

def z1127 : W := mkw 0x100bbbffff800000 0x93ffffffff80020c

def z1128 : W := mkw 0xf26111f82b83f057 0xe90c01f81f83f03f

def z1129 : W := mkw 0x0e004400007fe000 0x0d900020007ff000

def z1130 : W := mkw 0xb22111f83683f06d 0xe90c01f81f83f03f

def z1131 : W := mkw 0x0c0363500056a000 0x0d73c3d80077b000

def z1132 : W := mkw 0x0d804400007c0a80 0x04000000007c02c0

def z1133 : W := mkw 0x4fc0cc07c97d4f92 0x7e0c0007f9ff4ff3

def z1134 : W := mkw 0x020111f00003e000 0x0dd003f8001ff000

def z1135 : W := mkw 0x000333f000000000 0x05f3fff8001c0000

def z1136 : W := mkw 0x0003ab47c0000000 0x03f3ffc7e0000000

def z1137 : W := mkw 0x00008807c0000000 0x02000007e0000000

def z1138 : W := mkw 0xb020000822801045 0x83d80279e794b2cc

def z1139 : W := mkw 0x0002a20540000000 0x0043c201601402c0

def z1140 : W := mkw 0x100bbbffff800000 0x9ffffffffff38e3c

def z1141 : W := mkw 0x42401ca289294512 0x7ca43da699eb4d33

def z1142 : W := mkw 0x4e404400007fe512 0x7c040000006b4d33

def z1143 : W := mkw 0x0903eb47d4528a28 0x9fffffc7fe7f8ffc

def z1144 : W := mkw 0x0901c14514528a28 0x9f5fc0410610820c

def z1145 : W := mkw 0x00000c0280280500 0x00203c0600600c00

def z1146 : W := mkw 0x0d804400007c0f80 0x16900000807c0fc0

def z1147 : W := mkw 0x0901c14514528a28 0x9fffc1e71e7bce3c

def z1148 : W := mkw 0x000bb3f554000000 0x01f3fff800000000

def z1149 : W := mkw 0x0e0377f0007fe000 0x04f3ffb8007f7000

def z1150 : W := mkw 0x0901c14514528a28 0x9e2fc1871e738e3c

def z1151 : W := mkw 0x524911f83f814012 0x690c01f81f834033

def z1152 : W := mkw 0x0e0054a0007fe000 0x0d0001a0007ff000

def z1153 : W := mkw 0x0002ae07c0280500 0x16f3fe07e0680d00

def z1154 : W := mkw 0x080373f000528000 0x0df3fff800738000

def z1155 : W := mkw 0x0001814514000000 0x0023c18618000000

def z1156 : W := mkw 0x424014a009294012 0x6d0c01a019eb4033

def z1157 : W := mkw 0x0e0377f0007fe000 0x0d73ffd80077b000

def z1158 : W := mkw 0x120bbbffff814000 0x0bfbffffff834000

def z1159 : W := mkw 0x0d82ee07c07c0f80 0x16f3fe5fe07cbfc0

def z1160 : W := mkw 0x4e437ff2897fe512 0x6df3fff881fff103

def z1161 : W := mkw 0x41c2baa7c9000f92 0x73ffffa7f9800ff3

def z1162 : W := mkw 0x100b33f82b800000 0x01f3fff801800000

def z1163 : W := mkw 0x100b33f836800000 0x01f3fff806000000

def z1164 : W := mkw 0x0901c14514528a28 0xff7fc1e71ff3ce3f

def z1165 : W := mkw 0x000333f000000000 0x1ffffffe18630c30

def z1166 : W := mkw 0x0901c14514528a28 0x9f7fc1c71e7ffe3c

def z1167 : W := mkw 0x0002aa07c0000000 0x00c3fe01e0000000

def z1168 : W := mkw 0x020337f000294000 0x0df3fff8006b4000

def z1169 : W := mkw 0x0d80cc07c07c0f80 0x14000006007c0fc0

def z1170 : W := mkw 0x0001014014028028 0x9f5c01c11e13823c

def z1171 : W := mkw 0xb02bbbffff801045 0x6ffbffffff9cf1c3

def z1172 : W := mkw 0x0900440000780f00 0x1400000000780f00

def z1173 : W := mkw 0x0901c14514528a28 0xffffc3ff9fffff3f

def z1174 : W := mkw 0x000bbbf7dd028028 0x0023fd8618030030

def z1175 : W := mkw 0xb023b3fd36801045 0xffffffffff9cf3cf

def z1176 : W := mkw 0x0f0377f0007fea28 0x9ffffff9067ffe3c

def z1177 : W := mkw 0x0e0377f0007fe000 0x09f3fff80063f000

def z1178 : W := mkw 0x0000000000000000 0x6080002081884103

def z1179 : W := mkw 0xb02a3abaeb801045 0xffdc3e79e79cf3cf

def z1180 : W := mkw 0xa020000000001045 0xf0040000000003cf

def z1181 : W := mkw 0x42401ca289294512 0x76b03da699eb4d33

def z1182 : W := mkw 0x0d82ee07c07c0f80 0x16f3fe3fe07c7fc0

def z1183 : W := mkw 0x0d82ee07c07c0f80 0x1ff3fe47e07c8fc0

def z1184 : W := mkw 0xbda0440822fc1fc5 0x74800238e1fc7fc3

def z1185 : W := mkw 0x42c01ca2c9294592 0x7fbc3da6f9eb4df3

def z1186 : W := mkw 0x0c036750007ea000 0x00c3fe58001cb000

def z1187 : W := mkw 0x4e4377f0097fe012 0x7ffffff899fff133

def z1188 : W := mkw 0x0d804400007c0f80 0x1000000000600fc0

def z1189 : W := mkw 0x0000880780000000 0x02f3fc0780000000

def z1190 : W := mkw 0x0d82ee07c07c0f80 0x9ef7fe07e07c8fcc

def z1191 : W := mkw 0xa020000000001045 0xff9c0020819cf3cf

def z1192 : W := mkw 0x0003234000000000 0x01f3ffc000000000

def z1193 : W := mkw 0xb022aa0fe2801045 0x62f3fe3fe18c71c3

def z1194 : W := mkw 0xa020000000001045 0xe80400000000f00f

def z1195 : W := mkw 0x0801414014528028 0x8d7fc1c01e73803c

def z1196 : W := mkw 0x0d82ee07c07c0f80 0x17fbff87f87c0fc0

def z1197 : W := mkw 0x1d80440822fc0f80 0x17d80279e7fc0fc0

def z1198 : W := mkw 0x0002aa07c0000000 0x7ffffe27e1884103

def z1199 : W := mkw 0x0d804400007e8fa8 0x94000000007c8fcc

def z1200 : W := mkw 0xb02911f83f801045 0x610801f81f807003

def z1201 : W := mkw 0x000bbbf7dd000000 0x02f3ff87f8000000

def z1202 : W := mkw 0x100bbbffff800000 0x0043fe5966000000

def z1203 : W := mkw 0x0d80cc07c07c0f80 0x0000000600600c00

def z1204 : W := mkw 0x42433bf28903e012 0x6bfffffe9983f033

def z1205 : W := mkw 0x0d82ee07c07c0f80 0x1ff3fe27e07c4fc0

def z1206 : W := mkw 0x100bb3fd76800000 0x0063ffd966000000

def z1207 : W := mkw 0x504bbbffff800012 0x63ffffffff800033

def z1208 : W := mkw 0x42401ca289294512 0x7d2c3da619eb4d33

def z1209 : W := mkw 0x4e404400007fe012 0x6c040000007ff033

def z1210 : W := mkw 0x4e4377f0097fe012 0x6df3fff801fff003

def z1211 : W := mkw 0xb02bbbffff801045 0xebffffffff94f2cf

def z1212 : W := mkw 0xb022220822801045 0xfffffe79e79cf3cf

def z1213 : W := mkw 0x0d82ee07c07c0f80 0x1ffffe07e07c0fc0

def z1214 : W := mkw 0x0100800514000a28 0x9f5c00471e108e3c

def z1215 : W := mkw 0x0002220000000000 0x01f3fe7800000000

def z1216 : W := mkw 0x000333f000000000 0x7ffffff881884103

def z1217 : W := mkw 0x0901c14514528a28 0xff7fc1c79ff38f3f

def z1218 : W := mkw 0x0d80c405147c0fa8 0x960c00071e7c0ffc

def z1219 : W := mkw 0x0002aa07c0000000 0x03f3fe7fe0000000

def z1220 : W := mkw 0x0d804400007e8fa8 0x0000000000630c30

def z1221 : W := mkw 0x4fc04400007fef92 0x7c040000007ffff3

def z1222 : W := mkw 0x100bbbffff828000 0x0bfbffffff838000

def z1223 : W := mkw 0x0e004400007fe000 0x0c400258007ff000

def z1224 : W := mkw 0x100bbbffff800000 0x9fffffffff9c83cc

def z1225 : W := mkw 0x4fc054a0097d4f92 0x7d0c01a019ff4ff3

def z1226 : W := mkw 0x110bbbffff800a00 0x13fbffffff800e00

def z1227 : W := mkw 0x0003bbe7dd000000 0x03fbffe7ff800000

def z1228 : W := mkw 0x1e0b7ffaebffe000 0x0df3fff8e1fff000

def z1229 : W := mkw 0x424199e79d03c03a 0xebfffde79f83c03f

def z1230 : W := mkw 0xada04400007c1fc5 0xf4040000007c0fcf

def z1231 : W := mkw 0x090058a289528a28 0x9fbc3da699f38e3c

def z1232 : W := mkw 0x0003ab47d4000000 0x0023fd8618000000

def z1233 : W := mkw 0x0980cc07c0780f80 0x16f3fc07e0780fc0

def z1234 : W := mkw 0x0e037ff2807fe500 0x1ff3fffe807ffd00

def z1235 : W := mkw 0x01808c07c0280f80 0x16b03c07e0680fc0

def z1236 : W := mkw 0xbe20440822fff045 0xed0c007807fff00f

def z1237 : W := mkw 0xb020000822801045 0xe3d80279e79cf3cf

def z1238 : W := mkw 0x0c004400007c0000 0x14000000007c03c0

def z1239 : W := mkw 0x100bbbffff800000 0x037bffdf7e000000

def z1240 : W := mkw 0x0003ab47d4028028 0x8bffffc7fe03803c

def z1241 : W := mkw 0x0e004400007fe000 0x0d300180007ff000

def z1242 : W := mkw 0x4e4054a0097fe012 0x6d0c01a019fff033

def z1243 : W := mkw 0x0d826e02c07c0f80 0x14f3fe00e07c0fc0

def z1244 : W := mkw 0x1002aa0fe2800000 0x02f3fe3fe1800000

def z1245 : W := mkw 0x0e0377f0007fe000 0x1ffffff8007ff000

def z1246 : W := mkw 0x42401ca289294512 0x7f9c3c2081884103

def z1247 : W := mkw 0x42401ca289294512 0x6dbc3da619eb4c33

def z1248 : W := mkw 0x1000000822800000 0x7fdc0279e7884103

def z1249 : W := mkw 0x000333f009000000 0x01fbfff819800000

def z1250 : W := mkw 0x0c026e02807c0500 0x16f3fe07e07c0fc0

def z1251 : W := mkw 0x414199e79d000f3a 0xf3fffde79f800f3f

def z1252 : W := mkw 0x000bbbf7dd000000 0x0063ff8778000000

def z1253 : W := mkw 0x0002baa7c9000000 0x03bbfda699800000

def z1254 : W := mkw 0x0e0bfff7dd7fe000 0x0df3fffe187ff000

def z1255 : W := mkw 0x0d83e34554568aa8 0x9f7fc3c77e778efc

def z1256 : W := mkw 0x020115f0002be000 0x0db03df8006bf000

def z1257 : W := mkw 0x4b404400007bcf3a 0x0000000000630c30

def z1258 : W := mkw 0x0f80cc07c07fef80 0x1e000007e07fffc0

def z1259 : W := mkw 0x0003b3f514000000 0x0023fd8618000000

def z1260 : W := mkw 0x40400c0289280512 0x760c000699e80d33

def z1261 : W := mkw 0x000bbbf7dd000000 0x16f3ff87f81c03c0

def z1262 : W := mkw 0x42401ca289294512 0x6db03da699eb4d33

def z1263 : W := mkw 0x0002aa07c0000500 0x12f3fe07e0000d00

def z1264 : W := mkw 0x0e0377f0007fe000 0x9ffffff9e67ff3cc

def z1265 : W := mkw 0x42401ca289294512 0x7fbc3fbe99ef7d33

def z1266 : W := mkw 0x4e4377f0007fe512 0x7ffffff881fffd33

def z1267 : W := mkw 0xb02bbbffff801045 0xe3ffffffff80000f

def z1268 : W := mkw 0x0c826e02c07c0580 0x16f3fe06e07c0dc0

def z1269 : W := mkw 0xb02bab5ff6801045 0x96f3fe5fe61cb3cc

def z1270 : W := mkw 0x0d82ee07c07c0f80 0x1263fe07e0740fc0

def z1271 : W := mkw 0x020010a000014000 0x09b03da000034000

def z1272 : W := mkw 0x0901c14514528a28 0x9f7fc3df1e77be3c

def z1273 : W := mkw 0xb020000822801045 0xeddc0278079cf00f

def z1274 : W := mkw 0x0000000000000000 0x09d002780000f000

def z1275 : W := mkw 0x0d82ee07c07c0f80 0x02f3fe07e01c03c0

def z1276 : W := mkw 0xb22111f82283f045 0xffdc03f9e79ff3cf

def z1277 : W := mkw 0x0d8bfff7dd7c0f80 0x0023fd8618600c00

def z1278 : W := mkw 0x0e0377f0007fe000 0x0df3fffe187ffc30

def z1279 : W := mkw 0x1d82ee0fe2fc0f80 0x17fbfe7fe7fc0fc0

def z1280 : W := mkw 0xb02018aaab801045 0xfffc3fffff9cf3cf

def z1281 : W := mkw 0x000119e289000000 0x03fbfde699800000

def z1282 : W := mkw 0x0e004400007d4000 0x0c000000007f4000

def z1283 : W := mkw 0x1003ab4ff6800000 0x03fbffffff800000

def z1284 : W := mkw 0x00033bf289000000 0x01f3fff881800000

def z1285 : W := mkw 0x100bb3fd76800000 0x00c3fe7966000000

def z1286 : W := mkw 0xb12bbbffff801a6d 0xf3ffffffff800fff

def z1287 : W := mkw 0x0901c14514528a28 0x967fc1871e730e3c

def z1288 : W := mkw 0xb021814d36801045 0xffffc3ffff9cf3cf

def z1289 : W := mkw 0x524bbbffff83e012 0x6bffffffff83f033

def z1290 : W := mkw 0x00088807dd000000 0x0000000618000000

def z1291 : W := mkw 0x00033bf289000000 0x0023fd8618000000

def z1292 : W := mkw 0x4242baa7c9014012 0x6bffffa7f9834033

def z1293 : W := mkw 0x000bbbf7dd000000 0x03fbfffe99800000

def z1294 : W := mkw 0x100bbbffff828028 0x83fbffffff80800c

def z1295 : W := mkw 0x0d80c405007c0f80 0x1673c007007c0fc0

def z1296 : W := mkw 0xb02bbbffff801045 0x63fbffffff8001c3

def z1297 : W := mkw 0x0002baa7c9000000 0x02f3ff87f8000000

def z1298 : W := mkw 0x0e014540147fe028 0x8d0c01c01e7ff03c

def z1299 : W := mkw 0xeb604400007bdf7f 0xfc040000007fffff

def z1300 : W := mkw 0x42401ca289294512 0xffbc3da699fbcf3f

def z1301 : W := mkw 0x0182aa07c0000f80 0x02f3fe07e0000c00

def z1302 : W := mkw 0x100aaa1fe2800000 0x02f3fe1fe0000000

def z1303 : W := mkw 0x0d82ee07c07c0f80 0x14c3fe01e07c0fc0

def z1304 : W := mkw 0xbe20440822fff045 0x8c400259667ff2cc

def z1305 : W := mkw 0x000199e79d000000 0x0023fd8618000000

def z1306 : W := mkw 0x100999ffff800000 0x030801ffff800000

def z1307 : W := mkw 0x0e0377f0007fe000 0x8df3fff9067ff20c

def z1308 : W := mkw 0x000aaa07dd000000 0x0023fc0618000000

def z1309 : W := mkw 0x1d88cc0ffffc0f80 0x16080007fffc0fc0

def z1310 : W := mkw 0x0901c14514528a28 0x937fc1c71e630e3c

def z1311 : W := mkw 0xb020000822801045 0x96d00259e61cb3cc

def z1312 : W := mkw 0x100bbbffff800000 0x17fbffffff900200

def z1313 : W := mkw 0x0d82ee07c07e8f80 0x1ef3fe07e07f8fc0

def z1314 : W := mkw 0x0900400000528a28 0x9f3c018618738e3c

def z1315 : W := mkw 0xb020000822801045 0x6dd00278e19cf1c3

def z1316 : W := mkw 0x1d8afebfebfc0f80 0x16f3fe3fe1fc0fc0

def z1317 : W := mkw 0x0e0377f0007fe000 0x0db3fdf8006bf000

def z1318 : W := mkw 0x100bbbffff800000 0x13fbffffff8003c0

def z1319 : W := mkw 0x100b33f83f800000 0x03fbfff9ff800000

def z1320 : W := mkw 0x09004400007a8f28 0x9c040000007b8f3c

def z1321 : W := mkw 0x0e0377f0007fe000 0x7ffffff9e1fff3c3

def z1322 : W := mkw 0x1108880fff800a28 0x920c0007ff800e3c

def z1323 : W := mkw 0xb02bb3fd76801045 0x8df3fff9661cf2cc

def z1324 : W := mkw 0x020111f00003e000 0x1fd003f9e01ff3c0

def z1325 : W := mkw 0x0901c14514528a28 0x9fffc3fffe7ffffc

def z1326 : W := mkw 0x0e0155f0007fe000 0x0c000180007ff000

def z1327 : W := mkw 0x000010a000000000 0x0db03da000084000

def z1328 : W := mkw 0x120bbbffff83e000 0x0ffbffffff9ff000

def z1329 : W := mkw 0xb02bbbffff801045 0x83fbffffff80b00c

def z1330 : W := mkw 0x4e4377f0007fe512 0x7ffffffe187ffd33

def z1331 : W := mkw 0x110bbbffff800a28 0x9fffffffff908e3c

def z1332 : W := mkw 0x0d82ee07c07e8fa8 0x9fffff87f87f8ffc

def z1333 : W := mkw 0x424014a009294012 0x7fbc3da619eb4c33

def z1334 : W := mkw 0x000bbbf7dd000000 0x0223fd87f8000000

def z1335 : W := mkw 0x0c0373f00056a000 0x0063ffd80014b000

def z1336 : W := mkw 0x0182a20540000a80 0x0043c201600002c0

def z1337 : W := mkw 0x000191e514000000 0x03fbfde71e000000

def z1338 : W := mkw 0x0003b3f514000000 0x01f3fff906000000

def z1339 : W := mkw 0x0002aa07c0000000 0x9ffffe47e610820c

def z1340 : W := mkw 0x0c826e02c07c0580 0x00a3fe00e06c01c0

def z1341 : W := mkw 0x0000080280000000 0x16b03c0680080100

def z1342 : W := mkw 0x0e0377f0007fe000 0x00e3fff8007ff000

def z1343 : W := mkw 0x0000000000000000 0x7fdc0221e19c43c3

def z1344 : W := mkw 0x100bbbffff800000 0x02f3ffdffe000000

def z1345 : W := mkw 0x42401ca289294512 0x7ffc3de79feb4d33

def z1346 : W := mkw 0x0e0276b0007d6000 0x00a3fe38006c7000

def z1347 : W := mkw 0x0d82ee07c07c0f80 0x02f3fe07e0740ec0

def z1348 : W := mkw 0x000bbbf7dd000000 0x03fbfde79f800000

def z1349 : W := mkw 0x0d02e605007c0a00 0x16f3fe07e07c0fc0

def z1350 : W := mkw 0x0000080280000500 0x12b03c0680000d00

def z1351 : W := mkw 0x00800802c0000580 0x00000000e00001c0

def z1352 : W := mkw 0x4fc2ee07c07d4f92 0x76f3fe07e07c4fc3

def z1353 : W := mkw 0x0e0377f0007fe000 0x1df7fff8007ffc30

def z1354 : W := mkw 0x01808807c0000f80 0x1fd0027fe01cffc0

def z1355 : W := mkw 0x0801414014528028 0x9f7fc1c61e738c3c

def z1356 : W := mkw 0x4dc2ee07c97c0f92 0x16f3fe07f87c0ff0

def z1357 : W := mkw 0x0d83ef47d47c0f80 0x17fbffc7fe7c0fc0

def z1358 : W := mkw 0xb020000822801045 0xfcc40279e79cf3cf

def z1359 : W := mkw 0x04822e02c02c0580 0x16d03e01e01c03c0

def z1360 : W := mkw 0x0001014014028028 0x9f3c01c61e638c3c

def z1361 : W := mkw 0x0d82ee07c07c0f80 0x1673fc07e0700fc0

def z1362 : W := mkw 0x0000080280000000 0x02b03c0680000000

def z1363 : W := mkw 0x1c0bfbffffd6a000 0x03fbffffff94b000

def z1364 : W := mkw 0x4f43fff79d7fef3a 0xffffffff9fffff3f

def z1365 : W := mkw 0x424014a000294512 0x7db43da0006b4d33

def z1366 : W := mkw 0x0e0155f0007fe000 0x0dd003f8007ff000

def z1367 : W := mkw 0xb920400822d29a6d 0xffdc0279e7ffffff

def z1368 : W := mkw 0x1000000822800000 0x17d80279e79c03c0

def z1369 : W := mkw 0x4fc04400007d4f92 0x0000000000630c30

def z1370 : W := mkw 0x000bbbf7dd000000 0x03fbffa7f9800000

def z1371 : W := mkw 0x0e004400007fe000 0x080000000063f000

def z1372 : W := mkw 0x060236b0002d6000 0x0db03fb8006f7000

def z1373 : W := mkw 0x000333f000000000 0x9ffffff90610820c

def z1374 : W := mkw 0x0d82ee07c07c0f80 0x0023fc0760600ec0

def z1375 : W := mkw 0x4e4377f0007fe512 0x0df3fff8007ffc30

def z1376 : W := mkw 0xada04400007e9fed 0xfc040000007fffff

def z1377 : W := mkw 0x020333f00003e000 0x01f3fff800030000

def z1378 : W := mkw 0x0901c14514528a28 0x1f3fc18618630c30

def z1379 : W := mkw 0x42401ca289294512 0x60203d8699e30d33

def z1380 : W := mkw 0xb028880fff801045 0xe20c0007ff80000f

def z1381 : W := mkw 0x000bbbf7dd000000 0x03fbffff1e000000

def z1382 : W := mkw 0x020014a000294000 0x7fbc3da699eb4d33

def z1383 : W := mkw 0x4fc04400007d4f92 0x7fdc0221e1ff4ff3

def z1384 : W := mkw 0x100bbbffff800000 0x01f3ffff7e000000

def z1385 : W := mkw 0x0d82ee07c07c0f80 0x17fbfe27e1fc0fc0

def z1386 : W := mkw 0x100bbbffff800000 0x0bfbffffff80f000

def z1387 : W := mkw 0x0801414000528000 0x1f7fc1c618738c30

def z1388 : W := mkw 0x100bbbffff800000 0x01f3fffef9800000

def z1389 : W := mkw 0x0e0276b0007fe000 0x0c803e38007ff000

def z1390 : W := mkw 0x0003b3f514000000 0x037bfdc71e000000

def z1391 : W := mkw 0x100bab5ff6800000 0x0063fe5f66000000

def z1392 : W := mkw 0x000010a000000000 0x01b03da000000000

def z1393 : W := mkw 0x0d82ee07c07c0f80 0x7fffffa7f9ff4ff3

def z1394 : W := mkw 0x0c826e02c07c0580 0x00c3fe00e01c01c0

def z1395 : W := mkw 0x000b33f01d000000 0x0023fd8018000000

def z1396 : W := mkw 0x0e0377f0007fe000 0x0cc3fe78007ff000

def z1397 : W := mkw 0x100333f822800000 0x01f3fff8e1800000

def z1398 : W := mkw 0x100ababfeb800000 0x00c3fe39e1800000

def z1399 : W := mkw 0x0981c947d4528fa8 0x9f7fc1c7fe738ffc

def z1400 : W := mkw 0x0e004400007fe000 0x0c000000006b4000

def z1401 : W := mkw 0x020bbbf7dd03e000 0x0023fd8618030000

def z1402 : W := mkw 0x0c004400007c0000 0x16d00201e07c03c0

def z1403 : W := mkw 0x0d82ee07c97c0f80 0x16fbfe07f9fc0fc0

def z1404 : W := mkw 0x42433ff2892be512 0x7ffffffe99ebfd33

def z1405 : W := mkw 0x00822a02c0000580 0x00803e00e00001c0

def z1406 : W := mkw 0x42401ca289294512 0x69ac3da699eb4d33

def z1407 : W := mkw 0x118bbbffff800a80 0x03fbffffff8002c0

def z1408 : W := mkw 0x42401ca289294512 0x7ffc3de699fbcd33

def z1409 : W := mkw 0x0c004400007e8000 0x0c000000007f8000

def z1410 : W := mkw 0x4242bea7c9294512 0x7fffffa7f9ff4ff3

def z1411 : W := mkw 0x0d83e34554568aa8 0x8043c241661482cc

def z1412 : W := mkw 0x0000000000000000 0x00800200e00c01c0

def z1413 : W := mkw 0xb22bbbffff83f045 0xffffffffff9ff3cf

def z1414 : W := mkw 0x0c036750007ea000 0x0df3fe78007cf000

def z1415 : W := mkw 0x0a0155e0007bc000 0x0df3fff8007ff000

def z1416 : W := mkw 0x000199e79d000000 0x03bbfda699800000

def z1417 : W := mkw 0x060337f0002fe000 0x09f3fff8000ff000

def z1418 : W := mkw 0x0d82ee07c07c0f80 0xfffffe67e7fccfcf

def z1419 : W := mkw 0x0000000000000000 0x00800238000c7000

def z1420 : W := mkw 0x0e0377f0007fe000 0x01f3fff8006f7000

def z1421 : W := mkw 0x0d804400007c0f80 0x16000001e07c0fc0

def z1422 : W := mkw 0x0d804400007c0f80 0x1400000000700e00

def z1423 : W := mkw 0x4dc2ee07dd7c0fba 0xf6fffe07fffc0fff

def z1424 : W := mkw 0x1002aa0fe2800000 0x02fbfe07e7800000

def z1425 : W := mkw 0x42401cb289296512 0x7fbc3dbe99eb7d33

def z1426 : W := mkw 0x4e404400007d4512 0x7c040000007f4d33

def z1427 : W := mkw 0x0e0377f0007fe500 0x1df3fff8007ffd00

def z1428 : W := mkw 0x0000800500000000 0x1673c00700100200

def z1429 : W := mkw 0x100911f83f828028 0x890c01f81f83803c

def z1430 : W := mkw 0x140bbbffff842000 0x03fbffffff843000

def z1431 : W := mkw 0x100ababfeb800000 0x03fbffbff9800000

def z1432 : W := mkw 0x0900c00500528a28 0x9e77c00700738e3c

def z1433 : W := mkw 0x100b3bfabf800000 0x03fbfffe9f800000

def z1434 : W := mkw 0x40400c0289280512 0x7fbc3d8699eb0d33

def z1435 : W := mkw 0x100bbbffeb800000 0x03f3ffffe1800000

def z1436 : W := mkw 0xb02b33f83f801045 0xfffffff9ff9cf3cf

def z1437 : W := mkw 0x424010a009014012 0x7f9c01a0998b4133

def z1438 : W := mkw 0x0e0377f0007fe000 0x0083fe38000c7000

def z1439 : W := mkw 0x100bbbffff800000 0x01cbfff9ff800000

def z1440 : W := mkw 0x000bbbf7dd000000 0x03fbffc7fe000000

def z1441 : W := mkw 0x4e404400007fe512 0x0000000000630c30

def z1442 : W := mkw 0x100bbbffff800000 0x03fbffffffe30c30

def z1443 : W := mkw 0x0000000000000000 0x804000410610820c

def z1444 : W := mkw 0x0183ab47d4000fa8 0x93ffffc7fe000ffc

def z1445 : W := mkw 0x0f004400007fea28 0x0000000000630c30

def z1446 : W := mkw 0x1003b3fd36800000 0x03fbffffff800000

def z1447 : W := mkw 0x0003bbf7d4000000 0x03fbfffffe000000

def z1448 : W := mkw 0x0c0377f0007ea000 0x05f3fff8007cb000

def z1449 : W := mkw 0x0003bbf7c0000000 0x03f3ffffe0000000

def z1450 : W := mkw 0xb022aa0fe2801045 0x82f3fe5fe614b2cc

def z1451 : W := mkw 0x42401ca289294512 0xfffc3fff9fffff3f

def z1452 : W := mkw 0x1e00440822ffe000 0x0fd80279e7fff000

def z1453 : W := mkw 0x100bbbffff800000 0x7fffffffff9cf103

def z1454 : W := mkw 0x100bbbffff800000 0x0bffffffff830030

def z1455 : W := mkw 0x0002baa7c9000000 0x02f3fe27e1800000

def z1456 : W := mkw 0x100bbbffff800000 0x7fffffffff9c43c3

def z1457 : W := mkw 0x0903f3f514528a28 0x9fffffff1e7ffe3c

def z1458 : W := mkw 0x020333f000014000 0x09f3fff800034000

def z1459 : W := mkw 0x148a3ebaebac0580 0x00803e38e18c01c0

def z1460 : W := mkw 0x0d82ee07c07c0f80 0x7ef7fe07e07c4fc3

def z1461 : W := mkw 0x000bbbf7dd000000 0x0273fd8718000000

def z1462 : W := mkw 0x0482ae07c02c0580 0x00a3fe06e00c01c0

def z1463 : W := mkw 0xb020000822801045 0xffdc03f9ff9ff3ff

def z1464 : W := mkw 0xaf204400007ffa6d 0xfc040000007fffff

def z1465 : W := mkw 0x000bbbf7dd000000 0x9f7ffdc71e10820c

def z1466 : W := mkw 0x0e0bfff7dd7fe000 0x0023fd8618630000

def z1467 : W := mkw 0x010bbbf7dd000a28 0x0023fd8618000c30

def z1468 : W := mkw 0x0003bbf7c9000000 0x03fbfffff9800000

def z1469 : W := mkw 0x0d82ee07c07c0f80 0x9fffffc7fe7f8ffc

def z1470 : W := mkw 0x000232b000000000 0x00803e3800000000

def z1471 : W := mkw 0x0900cc0780780f00 0x16f3fe07e07c0fc0

def z1472 : W := mkw 0x00000c0280280500 0x7fbc3c2681e84d03

def z1473 : W := mkw 0x100bb3fd76800000 0x03fbfff9e7800000

def z1474 : W := mkw 0x100bbbffff800000 0x0023fdbe19800000

def z1475 : W := mkw 0x524bbbffff814012 0x7fffffffff8b4133

def z1476 : W := mkw 0x100bbbffff800000 0x026bffdfff800000

def z1477 : W := mkw 0x0d826600407c0f80 0x14000200607c0fc0

def z1478 : W := mkw 0x4b404400007bcf3a 0xffdc006187fbcf3f

def z1479 : W := mkw 0x0482ae07c02c0580 0x00c3fe01e00c01c0

def z1480 : W := mkw 0x0001014000000000 0x0d73c1c000108000

def z1481 : W := mkw 0x0900c00514528a28 0x920c00071e630e3c

def z1482 : W := mkw 0x0f004400007fea00 0x1c000000007ffe00

def z1483 : W := mkw 0x100bbbffff800000 0x037bfdc7ff800000

def z1484 : W := mkw 0x100bbbffff800000 0x0083fe38e1800000

def z1485 : W := mkw 0x424010a009014012 0x7f3c01a619e34c33

def z1486 : W := mkw 0xb020000822801045 0x76d00239e19c73c3

def z1487 : W := mkw 0xb020000822801045 0x63d80279e78c71c3

def z1488 : W := mkw 0x0e0377f0007fe000 0x04f3fe78007cf000

def z1489 : W := mkw 0xb02101483682906d 0xe90c01f81f83f03f

def z1490 : W := mkw 0xb921c14d36d29a6d 0xff7fc1ff1ff3fe3f

def z1491 : W := mkw 0xb02bbbffff801045 0xffffffffff9083cf

def z1492 : W := mkw 0x0e004400007fe000 0x0c800238007ff000

def z1493 : W := mkw 0xb02bbbffff801045 0xffffffffff8843cf

def z1494 : W := mkw 0x0d80c405407c0f80 0x14000001607c0fc0

def z1495 : W := mkw 0x0e036750007fe000 0x0c43c258007ff000

def z1496 : W := mkw 0x0002aa07c0000000 0x16f3fe07e0080100

def z1497 : W := mkw 0x0d804c02807c0f80 0x16b03c06807c0fc0

def z1498 : W := mkw 0x5048880fff800512 0x720c0007ff800d33

def z1499 : W := mkw 0xb1a0880fe2801fc5 0x72000007e1800fc3

def z1500 : W := mkw 0x0e0377f0007fe000 0x0963fff80077f000

def z1501 : W := mkw 0xb02bbbffff801045 0x8ffbffffff9cf2cc

def z1502 : W := mkw 0x0e0377f0007fe000 0x0023fdb800637000

def z1503 : W := mkw 0x0d82ee07c07c0f80 0x00e3fe07e07c0fc0

def z1504 : W := mkw 0x0901c14514528a28 0x9b2fc1c71e638e3c

def z1505 : W := mkw 0xb02b3bfaeb801045 0x6df3fff8e19cf1c3

def z1506 : W := mkw 0xb1a2aa0fe2801fc5 0xf3fffe7fe7800fcf

def z1507 : W := mkw 0xf06bbbffff801557 0xffffffffff9cffff

def z1508 : W := mkw 0x110bbbffff800a28 0x83fbffffff80020c

def z1509 : W := mkw 0x100bbbffff800000 0x016bffff7f800000

def z1510 : W := mkw 0xf6623ebaabad7557 0x60803e38e18c71c3

def z1511 : W := mkw 0x020010b000016000 0x0000003800007000

def z1512 : W := mkw 0x0d80c405007c0f80 0x16000007007c0fc0

def z1513 : W := mkw 0x524bbbffff814012 0x7fffffffffe34c33

def z1514 : W := mkw 0x110bbbffff828a28 0x9bffffffff838e3c

def z1515 : W := mkw 0x0002220000000000 0x0023fc0000000000

def z1516 : W := mkw 0x0d82ee07c07c0f80 0x16b3fc07e0680fc0

def z1517 : W := mkw 0x0c036740007e8000 0x0df3fff8007ff000

def z1518 : W := mkw 0x100bbbffff800000 0x07fbffffff9c0000

def z1519 : W := mkw 0x0e014550007fe000 0x0c000058007ff000

def z1520 : W := mkw 0x100bbbffff800028 0x83ffffffff80003c

def z1521 : W := mkw 0x100bbbffff800000 0x03fbffffff8c01c0

def z1522 : W := mkw 0x4dc2ee07c97c0f92 0x76f3fe07e1fc0fc3

def z1523 : W := mkw 0x0003b3f514000000 0x01f3fffe18000000

def z1524 : W := mkw 0x0001014000028000 0x0973c1c000038000

def z1525 : W := mkw 0x018bbbf7dd000f80 0x0023fd8618000c00

def z1526 : W := mkw 0x0902ea07c0500a00 0x16f3fe07e0700e00

def z1527 : W := mkw 0xb02aaa0fff801045 0xfffffe7fff9cf3cf

def z1528 : W := mkw 0x100bbbffff800000 0x01f3fff9e7800000

def z1529 : W := mkw 0xb020000822801045 0x800000580600b00c

def z1530 : W := mkw 0x42401ca289294512 0x1f3c3d8618630c30

def z1531 : W := mkw 0x060337f0002d6000 0x00c3fe78000c7000

def z1532 : W := mkw 0xbda0cc0fe2fc1fc5 0xffdc027fe7fcffcf

def z1533 : W := mkw 0x4241854514294512 0x7f7fc1c71e6b4d33

def z1534 : W := mkw 0x120bbbffff83e000 0x03fbffffff830000

def z1535 : W := mkw 0xb02bbbffff801045 0xf7ffffffff9c03cf

def z1536 : W := mkw 0xbfa0440822ffffc5 0xffdc0279e7ffffcf

def z1537 : W := mkw 0x100333f822800000 0x01fbfff807800000

def z1538 : W := mkw 0x020014a000294000 0x1fbc3da6186b4c30

def z1539 : W := mkw 0x0e804400007fe580 0x0c000000007ff1c0

def z1540 : W := mkw 0x100b3bfaeb800000 0x00a3ffb8e1800000

def z1541 : W := mkw 0xa022aa07c0001045 0xfef7fe07e01cf3cf

def z1542 : W := mkw 0x0d804400007e8fa8 0x9c04000000738e3c

def z1543 : W := mkw 0x100bbbffff800000 0x02cbfe7fff800000

def z1544 : W := mkw 0x0182aa07c0000f80 0x00c3fe01e00003c0

def z1545 : W := mkw 0x0002aa07c0000000 0x16f3fe07e00c01c0

def z1546 : W := mkw 0x0f81ddf7c07fef80 0x1f0001ffe07fffc0

def z1547 : W := mkw 0x04818545142e85a8 0x8b7fc1c71e0f81fc

def z1548 : W := mkw 0x0002aa07c0000000 0x16f3fe07e00803c0

def z1549 : W := mkw 0x0182aa07c0000f80 0x02f3fe07e0000dc0

def z1550 : W := mkw 0x000333f000000000 0x0df3fff80008f000

def z1551 : W := mkw 0x0002aa07c0000000 0x9ef7fe07e01c83cc

def z1552 : W := mkw 0x020333f000016000 0x09f3fff800037000

def z1553 : W := mkw 0xbda0cc0fe2fc1fc5 0xf60c0007e7fc0fcf

def z1554 : W := mkw 0xb22111f82283f045 0xe00c01800783000f

def z1555 : W := mkw 0x424ba75554294512 0x7f9fc02081eb4d33

def z1556 : W := mkw 0x000333f000028000 0x09f3fff80003f000

def z1557 : W := mkw 0xb02111f822801045 0xe10c01f80780000f

def z1558 : W := mkw 0x0002aa07c0000000 0x02f3fe07e00001c0

def z1559 : W := mkw 0x0f0377f0147fea28 0x8dfffff81e7ffc3c

def z1560 : W := mkw 0x1f8955f83fffef80 0x1d0801f81fffffc0

def z1561 : W := mkw 0x020333f00003e000 0x7ffffff8818bf103

def z1562 : W := mkw 0x000333f014028028 0x8dfffff81e1ff03c

def z1563 : W := mkw 0x0e08cc07dd7fe000 0x0dd0027e187ff000

def z1564 : W := mkw 0x0182aa07c0000f80 0x93fffe47e6000fcc

def z1565 : W := mkw 0x0182aa07c0000f80 0x16f3fe07e0080fc0

def z1566 : W := mkw 0x0002220000000000 0x00f3fe38000c7000

def z1567 : W := mkw 0xbe20440822fff045 0xf20c0001e7e303cf

def z1568 : W := mkw 0x100333f822800000 0x022bfd81e7800000

def z1569 : W := mkw 0x000333f000028000 0x0df3fff8001ff000

def z1570 : W := mkw 0x0002aa07c0000000 0x06f3fe07e01c01c0

def z1571 : W := mkw 0x000323500002a000 0x00f3fe580000b000

def z1572 : W := mkw 0xb92a7abaebd29a6d 0x60803e38e1ef7df3

def z1573 : W := mkw 0x0002aa07c0000000 0x1fffff87f87f0ff0

def z1574 : W := mkw 0x020333f00003e000 0x09f3fff8000ff000

def z1575 : W := mkw 0x1f88cc0fffffef80 0x1e080007ffffffc0

def z1576 : W := mkw 0x060236b0002d6000 0x04f3fe38001c7000

def z1577 : W := mkw 0x0e0155f0007fe000 0x1d0001f8007ff3c0

def z1578 : W := mkw 0x0182aa07d4000fa8 0x92fffe07fe000ffc

def z1579 : W := mkw 0x000333f000000000 0x0df3fff8007ff000

def z1580 : W := mkw 0x0002aa07c0000000 0x12f3fe07e00c03c0

def z1581 : W := mkw 0x0482220040040080 0x00f3fe00600400c0

def z1582 : W := mkw 0x000333f000000000 0x09f3fff8000cf000

def z1583 : W := mkw 0x0182aa07c0000f80 0x0063fe0760000ec0

def z1584 : W := mkw 0xbe20440822fff045 0xf3dc0279e7e303cf

def z1585 : W := mkw 0x0182aa07c0000f80 0x02f3fe07e0000ec0

def z1586 : W := mkw 0x0002aa07c0000000 0x16f3fe07e07c0fc0

def z1587 : W := mkw 0x000333f000000000 0x01f3fff8001cf000

def z1588 : W := mkw 0x020333f00003e000 0x01f3fff80003b000

def z1589 : W := mkw 0x000333f000000000 0x01f3fff800043000

def z1590 : W := mkw 0x0182aa07c0000f80 0x12a3fe07e0000fc0

def z1591 : W := mkw 0x0082aa07c0000580 0x0023fc06e00001c0

def z1592 : W := mkw 0x00022a0280000000 0x16f3fe07e01c03c0

def z1593 : W := mkw 0x020333f000016000 0x0023fdb800007000

def z1594 : W := mkw 0x0002aa07c0000000 0x02f3fe07e01c03c0

def z1595 : W := mkw 0x0c0363500056a000 0x04f3fe58001cb000

def z1596 : W := mkw 0x0003235000000000 0x04f3fe58001cb000

def z1597 : W := mkw 0x0d80cc07c07c0f80 0x1e000007e07cffc0

def z1598 : W := mkw 0xb022aa0fe2801045 0xe92ffc7e0780f00f

def z1599 : W := mkw 0x0002220000000000 0x09f3fe780000f000

def z1600 : W := mkw 0x0082aa07c0000580 0x02f3fe07e00c01c0

def z1601 : W := mkw 0x0002aa07c0000500 0x12f3fe07e0000fc0

def z1602 : W := mkw 0x040333f000042000 0x0df3fff8001cf000

def z1603 : W := mkw 0x0d80cc07c07c0f80 0x1fd0027fe07cffc0

def z1604 : W := mkw 0x5e48cc0fffffe512 0x7e0c0007fffffd33

def z1605 : W := mkw 0xb02333f822801045 0xfe2ffd81e79cf3cf

def z1606 : W := mkw 0x020333f01403e028 0x89fffff81e03f03c

def z1607 : W := mkw 0x0383bbf7c003ef80 0x1bf3ffffe003ffc0

def z1608 : W := mkw 0x0182aa07c0000f80 0x1ef3fe07e01cffc0

def z1609 : W := mkw 0x0182aa07c0000a80 0x02f3fe07e01402c0

def z1610 : W := mkw 0x020333f00003e000 0x0063ffd80003b000

def z1611 : W := mkw 0x4042aa07c9000512 0x76fffe07f99c0ff3

def z1612 : W := mkw 0xa022aa07c0001045 0xeaf7fe07e000f00f

def z1613 : W := mkw 0x0002aa07c0000500 0x16f3fe07e01c0fc0

def z1614 : W := mkw 0x0f80cc07c07fef80 0x1fd0027fe07fffc0

def z1615 : W := mkw 0x4fc2ee07c97fef92 0x7efffe07f9fffff3

def z1616 : W := mkw 0x0182aa07c0000f80 0x16f3fe07e0100fc0

def z1617 : W := mkw 0xb022220822801045 0xf2fffe01e78003cf

def z1618 : W := mkw 0x0e01ddf7c07fe000 0x0f0001ffe07ff000

def z1619 : W := mkw 0x020333f00003e000 0x01f3fff800037000

def z1620 : W := mkw 0xb022aa0fe2801045 0xfd2ffc7e079cf3cf

def z1621 : W := mkw 0x01808807c0000f80 0x12f3fc07e0000fc0

def z1622 : W := mkw 0x0182aa07c0000f80 0x13f3fe7fe0000fc0

def z1623 : W := mkw 0x4e4377f0097fe512 0x6dfffff819fffc33

def z1624 : W := mkw 0x0182aa07c0000f80 0x12b3fc07e0000fc0

def z1625 : W := mkw 0x040333f00006a000 0x01f3fff80004b000

def z1626 : W := mkw 0x020333f00003e000 0x09a3fff80003f000

def z1627 : W := mkw 0x000232b000000000 0x04f3fe38001c7000

def z1628 : W := mkw 0x020333f00003e000 0x01f3fff80000f000

def z1629 : W := mkw 0x0002aa07c0000000 0x02f3fe07e00400c0

def z1630 : W := mkw 0x000333f00002a000 0x01f3fff80014b000

def z1631 : W := mkw 0x43c199f7c903ef92 0x7b0c01fff983fff3

def z1632 : W := mkw 0x0002aa07c0000000 0x02f3fe07e00002c0

def z1633 : W := mkw 0x0182aa07c0000f80 0x1273fc07e0000fc0

def z1634 : W := mkw 0xb02333f822801045 0xf22ffd81e78003cf

def z1635 : W := mkw 0x020333f00003e000 0x0963fff80003f000

def z1636 : W := mkw 0x020232b000016000 0x00f3fe3800007000

def z1637 : W := mkw 0x020333f000014000 0x09f3fff80003f000

def z1638 : W := mkw 0x0002aa07c0000000 0x00c3fe01e01c03c0

def z1639 : W := mkw 0x04822e02c02c0580 0x04f3fe00e01c01c0

def z1640 : W := mkw 0x0f8155f0007fef80 0x1fd003f9e07fffc0

def z1641 : W := mkw 0x41c2aa07c9000f92 0x72fffe07f9800ff3

def z1642 : W := mkw 0x020333f00003e000 0x6bfffff88183f003

def z1643 : W := mkw 0x0002aa07c0000000 0x00a3fe06e00c01c0

def z1644 : W := mkw 0x0000880780000000 0x16f3fe07e01c03c0

def z1645 : W := mkw 0x0002aa07c0000000 0x06f3fe07e01c02c0

def z1646 : W := mkw 0x4c436b528956a512 0x7fdfc27e999cfd33

def z1647 : W := mkw 0x0002aa07c0000000 0x7ffffe27e19c43c3

def z1648 : W := mkw 0x020333f000014000 0x0df3fff8001ff000

def z1649 : W := mkw 0x000333f000000000 0x7ffffff8819cf103

def z1650 : W := mkw 0x0901c14514528a28 0x9fffc3c7fe738ffc

def z1651 : W := mkw 0x0182aa07c0000f80 0x00a3fe06e0000dc0

def z1652 : W := mkw 0x0182a20540000a80 0x00f3fe01600002c0

def z1653 : W := mkw 0x0002220000000000 0x12f3fe01e00003c0

def z1654 : W := mkw 0x0002aa07d4000000 0x96fffe07fe1c03cc

def z1655 : W := mkw 0x0002aa07c0000000 0x1fffff87f81c03c0

def z1656 : W := mkw 0x000333f000000000 0x0df3fff8000c7000

def z1657 : W := mkw 0x000333f014000000 0x8dfffff81e1cf00c

def z1658 : W := mkw 0x0582aa07c0040f80 0x12f3fe07e0040fc0

def z1659 : W := mkw 0x424333f00903e012 0x69fffff81983f033

def z1660 : W := mkw 0xbda0440822fc1fc5 0xe90c007807e0fc0f

def z1661 : W := mkw 0x0182aa07c0000f80 0x13ffff87f8000ff0

def z1662 : W := mkw 0x0002220000000000 0x00f3fe00e00c01c0

def z1663 : W := mkw 0x0182aa07c0000f80 0x12f3fe07e0140fc0

def z1664 : W := mkw 0x020333f00003e000 0x0973fdf80003f000

def z1665 : W := mkw 0x4b404400007bcf3a 0xe00000000018c30f

def z1666 : W := mkw 0x0182aa07c0000fa8 0x92f7fe07e0000ffc

def z1667 : W := mkw 0x000333f000000000 0x00a3ffb8000c7000

def z1668 : W := mkw 0xb022220822801045 0xe9fffe780780f00f

def z1669 : W := mkw 0x0382aa07c003ef80 0x1af3fe07e003ffc0

def z1670 : W := mkw 0x0002aa07c0000000 0x16f3fe07e01003c0

def z1671 : W := mkw 0x0482aa07c0040080 0x02f3fe07e01402c0

def z1672 : W := mkw 0x42401ca289294512 0x7ffc3ffe99ebfd33

def z1673 : W := mkw 0x000333f000000000 0x0df3fff80010f000

def z1674 : W := mkw 0x0482aa07c0040080 0x16f3fe07e01c03c0

def z1675 : W := mkw 0x020333f00003e000 0x8bfffff90603f00c

def z1676 : W := mkw 0x424333f00003e012 0x69f7fff80003f033

def z1677 : W := mkw 0x424333f009014012 0x6dfffff8199ff033

def z1678 : W := mkw 0x0002aa07c0000000 0x1223fc07e00003c0

def z1679 : W := mkw 0x0f8377f0147fefa8 0x9dfffff81e7ffffc

def z1680 : W := mkw 0x020333f000016000 0x09f3fff80000f000

def z1681 : W := mkw 0x42401ca289294512 0x762c3d8699eb0d33

def z1682 : W := mkw 0x000333f000000000 0x0923fdf80000f000

def z1683 : W := mkw 0x0d81ddf7c07c0f80 0x170001ffe07c0fc0

def z1684 : W := mkw 0x020333f00003e000 0x0df3fff80063f000

def z1685 : W := mkw 0x000333f00002a000 0x09f3fff80000f000

def z1686 : W := mkw 0x0182aa07c0000a80 0x12f3fe07e0000ec0

def z1687 : W := mkw 0x0582aa07c0040a80 0x02f3fe07e00402c0

def z1688 : W := mkw 0x020333f00003e000 0x1ffffffe1863fc30

def z1689 : W := mkw 0x0002aa07c0000000 0x16d3fe01e01c03c0

def z1690 : W := mkw 0xb1a0880fe2801fc5 0xe00c000607800c0f

def z1691 : W := mkw 0x020333f000016000 0x0df3fff8001cf000

def z1692 : W := mkw 0x4fc377f0097fef92 0x7dfffff819fffff3

def z1693 : W := mkw 0x000333f000000000 0x7df7fff8001cf103

def z1694 : W := mkw 0x42432f5289294512 0x7e4fc25e99eb4d33

def z1695 : W := mkw 0xbda955f83ffc1fc5 0xe90c01f81fe0fc0f

def z1696 : W := mkw 0x000333f00002a000 0x0df3fff8001cf000

def z1697 : W := mkw 0x0901c14514528a28 0x8d2fc1c61e738c3c

def z1698 : W := mkw 0x020333f00003e000 0x09f3fff80017f000

def z1699 : W := mkw 0x020333f00003e000 0x0bfffffe1803f030

def z1700 : W := mkw 0x0002a20540000000 0x16f3fe01e01c03c0

def z1701 : W := mkw 0x0002aa07c0000000 0x0063fe07601402c0

def z1702 : W := mkw 0xb022220822801045 0xf6fffe01e79c03cf

def z1703 : W := mkw 0x0002aa07c0000000 0x12f3fe07e01403c0

def z1704 : W := mkw 0x0c026600007c0000 0x1223fc01e06003c0

def z1705 : W := mkw 0x000333f000000000 0x09f3fff80014f000

def z1706 : W := mkw 0x00822a02c0000580 0x00f3fe00e00001c0

def z1707 : W := mkw 0x020333f00003e028 0x89f7fff80003f03c

def z1708 : W := mkw 0xf26ba75d76a95557 0x8043c2596677befc

def z1709 : W := mkw 0x0003234000000000 0x0df3fff8001cf000

def z1710 : W := mkw 0x000232a000000000 0x0df3fff8001cf000

def z1711 : W := mkw 0x42401ca289294512 0x7ffc3fa7f9eb4ff3

def z1712 : W := mkw 0x0082aa07c0000580 0x12f3fe07e00003c0

def z1713 : W := mkw 0x4fc2ee07c97d4f92 0x76fffe07f9ff0ff3

def z1714 : W := mkw 0x020333f00003e000 0x00a3ffb800037000

def z1715 : W := mkw 0xa02333f000001045 0xf1f7fff8000003cf

def z1716 : W := mkw 0xbe2955f83ffff045 0xe90c01f81fe3f00f

def z1717 : W := mkw 0x020333f00003e000 0x0df3fff8000bf000

def z1718 : W := mkw 0x0182aa07c0000f80 0x1fffff87f8630ff0

def z1719 : W := mkw 0x040333f000042000 0x0023ff9800043000

def z1720 : W := mkw 0x138bbbffff83ef80 0x1bfbffffff83ffc0

def z1721 : W := mkw 0x0082aa07c0000580 0x16f3fe07e01c03c0

def z1722 : W := mkw 0x0c026600007c0000 0x0923fc780060f000

def z1723 : W := mkw 0x00022a02c0000000 0x16f3fe01e01c03c0

def z1724 : W := mkw 0x0182aa07c0000a80 0x0023fc07600002c0

def z1725 : W := mkw 0x060333f000056000 0x01f3fff800047000

def z1726 : W := mkw 0x0d82e20540540a80 0x04f3fe01601c02c0

def z1727 : W := mkw 0x0002aa07c0000000 0x9ffffe47e61c83cc

def z1728 : W := mkw 0x0102aa07c0000a00 0x12f3fe07e0000fc0

def z1729 : W := mkw 0x09036b42d4528a28 0x9d8c3fc0fe738e3c

def z1730 : W := mkw 0x5fc955f83ffd4f92 0x7d0c01f81fff4ff3

def z1731 : W := mkw 0x020333f00003e000 0x1ff3fff9e01ff3c0

def z1732 : W := mkw 0x0102aa07d4000a28 0x96fffe07fe1c0ffc

def z1733 : W := mkw 0x0182aa07c0000f80 0x16f3fe07e0600fc0

def z1734 : W := mkw 0x0002aa07c0000000 0x1ef3fe07e01cf3c0

def z1735 : W := mkw 0x000333f000000000 0x1ffffffe187ffc30

def z1736 : W := mkw 0x0182aa07c0000f80 0x9ffffe47e6108fcc

def z1737 : W := mkw 0x0e0155f0007fe000 0x1fd003f9e07ff3c0

def z1738 : W := mkw 0x0182aa07c0000f80 0x1ff3fe7fe01cffc0

def z1739 : W := mkw 0x038199f7c003ef80 0x1fd003ffe01fffc0

def z1740 : W := mkw 0x000333f000000000 0x1ff3fff9e01cf3c0

def z1741 : W := mkw 0x0102aa07c0000a00 0x16f3fe07e01c0fc0

def z1742 : W := mkw 0x020111f00003e000 0x09f3fdf80003f000

def z1743 : W := mkw 0x020333f00003e000 0x0df3fff80013f000

def z1744 : W := mkw 0x020333f00003e000 0x09b3fdf80003f000

def z1745 : W := mkw 0xbda8cc0ffffc1fc5 0xf20c0007ffe00fcf

def z1746 : W := mkw 0x0182aa07c0000f80 0x02f3fe07e00003c0

def z1747 : W := mkw 0x0901c14514528a28 0x962fc1871e730e3c

def z1748 : W := mkw 0x41c2aa07c0000f92 0x72f7fe07e0000ff3

def z1749 : W := mkw 0x1f08cc0fffffea28 0x9e0c0007fffffe3c

def z1750 : W := mkw 0x0182aa07c0000f80 0x12c3fe07e0000fc0

def z1751 : W := mkw 0x0002220000000000 0x00f3fe580014b000

def z1752 : W := mkw 0x100a22083f800000 0x00fbfe001f800000

def z1753 : W := mkw 0x0002aa07c0000000 0x16f3fe07e01402c0

def z1754 : W := mkw 0x040333f000042000 0x01f3fff8000c7000

def z1755 : W := mkw 0x020333f00003e000 0x00c3fe780000f000

def z1756 : W := mkw 0x4c4058a28956a512 0x73bc3da69994bd33

def z1757 : W := mkw 0x04832f42d42e85a8 0x9fdc3fc1fe1f83fc

def z1758 : W := mkw 0x000333f000000000 0x9ffffff9061cf20c

def z1759 : W := mkw 0xbe2155f822fff045 0xe90c01f807e3f00f

def z1760 : W := mkw 0xb022220822801045 0xedfffe78079cf00f

def z1761 : W := mkw 0x0182aa07c0000f80 0x7ffffe27e1884fc3

def z1762 : W := mkw 0x0002a20540000000 0x04f3fe01601c02c0

def z1763 : W := mkw 0x038333f00003ef80 0x19f3fff80003ffc0

def z1764 : W := mkw 0x0902f2b514528a28 0x9e8c3e3f1e738e3c

def z1765 : W := mkw 0x000333f00002a000 0x09f3fff80003b000

def z1766 : W := mkw 0x1d8955f83ffe8fa8 0x9d0c01f81fff8ffc

def z1767 : W := mkw 0x0182aa07c0000f80 0x12f3fe07e00c0fc0

def z1768 : W := mkw 0x0002aa07c0000000 0x1ff3fe7fe01cf3c0

def z1769 : W := mkw 0xbda0440822fc1fc5 0xebdc0279e7e0fc0f

def z1770 : W := mkw 0x0d8955f01d7c0f80 0x16d00381f87c0fc0

def z1771 : W := mkw 0x060333f00007e000 0x09f3fff80007f000

def z1772 : W := mkw 0x038199f7d403efa8 0x9b0c01fffe03fffc

def z1773 : W := mkw 0x0182aa07c0000f80 0x73fffe27e1800fc3

def z1774 : W := mkw 0x4b41dde79d7bcf3a 0xffdffc618798c30f

def z1775 : W := mkw 0x000333f000000000 0x0063ffd80014b000

def z1776 : W := mkw 0xb921c14d36d29a6d 0x7fbfc3bef9ef7df3

def z1777 : W := mkw 0xbda0cc0fe2fc1fc5 0xf20c0007e7e00fcf

def z1778 : W := mkw 0x090a7ab2c9528a28 0x9f5c3c4106738e3c

def z1779 : W := mkw 0x0c026600007c0000 0x1ff3fe79e07cf3c0

def z1780 : W := mkw 0x0482aa07c0040080 0x02f3fe07e00c01c0

def z1781 : W := mkw 0x0002220000000000 0x00f3fe01601402c0

def z1782 : W := mkw 0x020333f00003e000 0x9ffffff90613f20c

def z1783 : W := mkw 0xada04400007c1fc5 0xe80400000060fc0f

def z1784 : W := mkw 0x000333f000000000 0x00c3fe78001cf000

def z1785 : W := mkw 0xbe2955f83ffff045 0xed0c01f81ffff00f

def z1786 : W := mkw 0x000333f000000000 0x0dd3fe78001cf000

def z1787 : W := mkw 0x000333f000000000 0x01f3fff80000b000

def z1788 : W := mkw 0x000333f000002000 0x01f3fff800003000

def z1789 : W := mkw 0x0082aa07c0000580 0x12f3fe07e0000dc0

def z1790 : W := mkw 0x0002a20500000000 0x16f3fe07e01c03c0

def z1791 : W := mkw 0xf2601caaaba95557 0x9f7c3fdf7e77befc

def z1792 : W := mkw 0x000333f00002a000 0x0023fdd80000b000

def z1793 : W := mkw 0x0482aa07c0040580 0x02f3fe07e00401c0

def z1794 : W := mkw 0xb020880fe2801045 0xe20c0007e780000f

def z1795 : W := mkw 0x0f82ee07d47fefa8 0x9efffe07fe7ffffc

def z1796 : W := mkw 0x0482aa07c0040080 0x0023fe06600400c0

def z1797 : W := mkw 0x0402221000042000 0x00f3fe1800043000

def z1798 : W := mkw 0x000333f000000000 0x05f3fff8001cb000

def z1799 : W := mkw 0x1002aa0fe2800000 0x012bfc7e07800000

def z1800 : W := mkw 0x07018545142d6a28 0x937fc1c71e0c7e3c

def z1801 : W := mkw 0x020333f00003e000 0x1df3fff8001ff3c0

def z1802 : W := mkw 0x000333f000000000 0x1ffffffe181cf000

def z1803 : W := mkw 0x000111e000000000 0x0df3fff8001cf000

def z1804 : W := mkw 0x000333f000000000 0x9df7fff8001cf20c

def z1805 : W := mkw 0x42401ca289294512 0x6d2c3da619eb4c33

def z1806 : W := mkw 0x0901c14514528a28 0x9fffc3ff1e73fe3c

def z1807 : W := mkw 0x000333f000000000 0x1df3fff8001cf3c0

def z1808 : W := mkw 0x000333f000000000 0x01f3fff800007000

def z1809 : W := mkw 0x4242b6a549294512 0x7d4fc3a179eb4d33

def z1810 : W := mkw 0xbda8cc0ffffc1fc5 0xf60c0007fffc0fcf

def z1811 : W := mkw 0x000aaa07dd000000 0x16f3fe07f81c03c0

def z1812 : W := mkw 0x000b33f01d000000 0x0df3fff8181cf000

def z1813 : W := mkw 0x0082aa07c0000080 0x02f3fe07e00000c0

def z1814 : W := mkw 0x000333f000000000 0x05f3fff8001c7000

def z1815 : W := mkw 0x000199e79d000000 0x00c3fc6187800000

def z1816 : W := mkw 0x0182aa07c0000f80 0x1263fe07e0000fc0

def z1817 : W := mkw 0x0182aa07c0000a80 0x12f3fe07e00003c0

def z1818 : W := mkw 0xbc22660822fc1045 0xe4fffe0007fc000f

def z1819 : W := mkw 0x020333f000016000 0x01f3fff8000c7000

def z1820 : W := mkw 0x0002aa07c0000000 0x7ef7fe07e01c43c3

def z1821 : W := mkw 0x4fc058a289554a92 0x6bbc3da6999742f3

def z1822 : W := mkw 0xbe2155f822fff045 0xed0c01f807fff00f

def z1823 : W := mkw 0xbe28cc0ffffff045 0xf20c0007ffe303cf

def z1824 : W := mkw 0x000333f000000000 0x0df3fff80014b000

def z1825 : W := mkw 0x0002aa07c9000000 0x76fffe07f99c03c3

def z1826 : W := mkw 0x020333f00003e000 0x0bf3fff9e003f000

def z1827 : W := mkw 0x000333f009000000 0x6dfffff8199cf003

def z1828 : W := mkw 0x0182aa07c0000a80 0x16f3fe07e01c03c0

def z1829 : W := mkw 0xae204400007ff045 0xf0040000006303cf

def z1830 : W := mkw 0x000232b000000000 0x0df3fe78001cf000

def z1831 : W := mkw 0x040333f000042000 0x01f3fff80014b000

def z1832 : W := mkw 0x0003235000000000 0x0df3fe78001cf000

def z1833 : W := mkw 0x0d82ee07d47e8fa8 0x96fffe07fe7f0ffc

def z1834 : W := mkw 0x020333f00003e000 0x09c3fff80003f000

def z1835 : W := mkw 0x0702b6b5142d6a28 0x9fdc3e7f1e1cfe3c

def z1836 : W := mkw 0x00022a02c0000000 0x04f3fe00e01c01c0

def z1837 : W := mkw 0x4fc2f2a549554a92 0x7fdfc3a1f99f43f3

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5])],[(0,[z1,z6,z2,z7,z4,z5]),(0,[z8,z9,z1,z2,z4,z5]),(0,[z9,z1,z10,z2,z4,z5])],[(0,[z1,z11,z2,z12,z13,z5]),(0,[z14,z1,z11,z2,z4,z15]),(0,[z1,z11,z2,z12,z16,z5]),(0,[z1,z11,z17,z12,z4,z5]),(0,[z14,z1,z18,z2,z19,z5]),(0,[z20,z1,z21,z11,z4,z5]),(0,[z20,z1,z11,z10,z4,z5])],[(0,[z1,z11,z2,z12,z4,z5]),(0,[z1,z11,z2,z22,z4,z5])],[(0,[z1,z23,z2,z12,z4,z5]),(0,[z24,z25,z11,z12,z4,z5])],[(0,[z14,z1,z11,z2,z4,z5]),(0,[z26,z1,z27,z2,z4,z5]),(0,[z28,z1,z11,z2,z4,z5])],[(0,[z20,z29,z30,z2,z4,z5]),(0,[z31,z1,z11,z2,z4,z5]),(0,[z32,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z12,z33,z5])],[(0,[z0,z1,z2,z4,z5,z34])],[(0,[z1,z11,z12,z4,z5,z35]),(0,[z14,z1,z11,z2,z4,z36]),(0,[z0,z1,z2,z4,z37,z5])],[(0,[z1,z11,z10,z38,z4,z5]),(0,[z39,z8,z1,z11,z4,z5]),(0,[z40,z1,z2,z12,z4,z41]),(0,[z42,z1,z43,z2,z4,z5]),(0,[z44,z11,z2,z12,z4,z5]),(0,[z1,z45,z2,z46,z4,z5]),(0,[z0,z1,z2,z47,z4,z5]),(0,[z1,z2,z4,z5,z48,z49])],[(0,[z1,z27,z2,z12,z4,z5]),(0,[z50,z1,z11,z12,z4,z5])],[(0,[z1,z11,z51,z2,z4,z5]),(0,[z52,z11,z2,z12,z4,z5]),(0,[z53,z1,z2,z54,z4,z5])],[(0,[z14,z55,z11,z2,z4,z5]),(0,[z1,z11,z12,z4,z5,z56])],[(0,[z1,z11,z2,z57,z4,z5]),(0,[z26,z1,z58,z2,z4,z5]),(0,[z11,z2,z12,z59,z60,z61]),(0,[z62,z1,z11,z12,z4,z5]),(0,[z39,z1,z63,z11,z4,z5]),(0,[z1,z64,z11,z2,z4,z5]),(0,[z1,z11,z65,z4,z66,z67])],[(0,[z1,z11,z2,z12,z4,z68]),(0,[z69,z1,z11,z2,z4,z5]),(0,[z1,z2,z12,z70,z71,z5]),(0,[z26,z1,z2,z4,z72,z5]),(0,[z26,z1,z73,z2,z4,z5])],[(0,[z14,z74,z11,z2,z4,z75]),(0,[z1,z11,z2,z12,z76,z5]),(0,[z1,z11,z4,z66,z5,z77]),(0,[z78,z11,z2,z12,z4,z5]),(0,[z14,z1,z11,z2,z4,z49])],[(0,[z79,z80,z11,z2,z4,z5]),(0,[z25,z11,z65,z12,z4,z5]),(0,[z1,z81,z2,z12,z4,z5])],[(0,[z82,z11,z38,z12,z59,z5]),(0,[z83,z1,z11,z4,z59,z5])],[(0,[z25,z11,z2,z12,z84,z5]),(0,[z85,z1,z2,z4,z5,z86])],[(0,[z1,z87,z11,z12,z4,z5]),(0,[z1,z11,z2,z88,z4,z5]),(0,[z89,z1,z2,z12,z4,z5])],[],[(0,[z1,z90,z11,z2,z4,z5]),(0,[z26,z1,z91,z2,z4,z5]),(0,[z1,z11,z2,z12,z92,z5]),(0,[z1,z11,z12,z4,z66,z93])],[],[(0,[z1,z11,z2,z4,z5,z94]),(0,[z95,z11,z2,z12,z59,z5])],[(0,[z96,z97,z2,z12,z4,z5]),(0,[z98,z1,z6,z2,z4,z5]),(0,[z20,z1,z11,z99,z4,z5]),(0,[z40,z1,z100,z2,z4,z101]),(0,[z1,z11,z102,z12,z4,z5]),(0,[z14,z1,z21,z11,z4,z5]),(1,[z1,z2,z12,z4,z41]),(0,[z20,z103,z1,z2,z4,z5])],[(0,[z104,z1,z11,z2,z4,z5]),(0,[z1,z11,z54,z4,z5,z67]),(0,[z105,z1,z11,z2,z4,z5])],[(0,[z1,z106,z10,z2,z4,z5]),(0,[z1,z107,z2,z12,z4,z5])],[(0,[z20,z74,z11,z108,z4,z5]),(0,[z1,z11,z109,z12,z4,z5]),(0,[z110,z11,z2,z12,z4,z5])],[(0,[z14,z29,z30,z2,z4,z5]),(0,[z53,z1,z2,z111,z4,z5]),(0,[z112,z53,z1,z2,z4,z5]),(0,[z113,z1,z11,z2,z4,z5])],[(0,[z53,z1,z2,z4,z114,z5])],[(0,[z1,z11,z2,z4,z5,z115]),(0,[z1,z11,z2,z116,z4,z5]),(0,[z1,z117,z11,z4,z5,z77]),(0,[z1,z11,z118,z12,z5,z61])]],
   [[(0,[z1,z11,z108,z4,z5,z77]),(0,[z1,z11,z2,z119,z120,z5]),(0,[z121,z11,z2,z12,z4,z5]),(0,[z122,z1,z11,z4,z5,z5]),(0,[z123,z11,z2,z12,z5,z61])],[(0,[z1,z124,z2,z12,z4,z5])],[(0,[z125,z1,z126,z2,z4,z5]),(0,[z1,z127,z2,z12,z4,z5]),(0,[z128,z1,z11,z12,z114,z5]),(0,[z129,z1,z11,z4,z5,z49]),(0,[z14,z1,z11,z4,z130,z49])],[(0,[z1,z11,z2,z12,z5,z131]),(0,[z132,z1,z45,z2,z4,z5]),(0,[z1,z133,z11,z2,z4,z5]),(0,[z1,z134,z11,z2,z4,z135])],[(0,[z122,z1,z11,z4,z59,z5]),(0,[z136,z1,z11,z137,z4,z5]),(0,[z1,z11,z138,z4,z114,z5])],[(0,[z1,z11,z2,z4,z5,z139]),(0,[z0,z74,z1,z2,z4,z5]),(0,[z1,z100,z11,z140,z4,z5]),(0,[z1,z11,z141,z142,z4,z5]),(0,[z1,z11,z2,z143,z4,z5]),(0,[z0,z1,z2,z4,z144,z5])],[(0,[z0,z1,z43,z2,z4,z5])],[(0,[z1,z11,z145,z2,z4,z5]),(0,[z1,z2,z146,z147,z4,z5]),(0,[z26,z1,z2,z148,z4,z5]),(0,[z39,z1,z11,z4,z5,z149])],[(1,[z150,z11,z12,z4,z5]),(0,[z151,z20,z1,z137,z4,z5]),(0,[z152,z1,z11,z2,z4,z5])],[(0,[z153,z11,z2,z142,z4,z5]),(0,[z20,z1,z11,z154,z4,z5]),(0,[z1,z11,z2,z4,z5,z155])],[(0,[z82,z26,z11,z2,z59,z5]),(0,[z1,z156,z11,z2,z4,z5])],[(0,[z1,z11,z12,z4,z157,z5]),(0,[z1,z11,z2,z158,z4,z5])],[(0,[z159,z151,z1,z11,z4,z5]),(0,[z0,z1,z2,z4,z5,z5]),(0,[z14,z160,z1,z2,z4,z5])],[(0,[z20,z161,z1,z11,z4,z5]),(0,[z1,z11,z2,z162,z4,z5]),(0,[z163,z153,z2,z12,z4,z5])],[(0,[z164,z1,z11,z2,z12,z5]),(0,[z1,z11,z2,z4,z5,z165]),(0,[z166,z20,z1,z11,z4,z5]),(0,[z1,z11,z154,z12,z167,z5])],[(0,[z168,z1,z11,z2,z4,z5]),(0,[z122,z1,z11,z169,z4,z5])],[(0,[z11,z108,z12,z4,z5,z170]),(0,[z26,z1,z6,z2,z4,z5]),(0,[z0,z1,z2,z4,z59,z5]),(0,[z1,z171,z2,z147,z4,z5])],[(0,[z136,z1,z11,z108,z4,z5])],[(0,[z20,z1,z11,z172,z4,z5]),(0,[z82,z11,z2,z12,z173,z5]),(0,[z174,z11,z2,z12,z4,z5]),(0,[z122,z1,z175,z11,z4,z5])],[(0,[z176,z1,z11,z2,z4,z5]),(0,[z20,z1,z177,z2,z4,z5]),(0,[z1,z177,z2,z12,z4,z5])],[(0,[z1,z11,z4,z178,z179,z5]),(0,[z125,z1,z2,z4,z180,z5]),(0,[z26,z1,z2,z4,z5,z181]),(0,[z1,z182,z11,z2,z4,z5]),(0,[z40,z1,z2,z183,z4,z101])],[(0,[z1,z11,z12,z4,z184,z5]),(0,[z185,z1,z186,z12,z4,z5]),(0,[z163,z1,z11,z187,z4,z5]),(0,[z40,z26,z1,z2,z4,z180])],[(0,[z1,z11,z188,z12,z4,z189]),(0,[z123,z100,z11,z2,z4,z5]),(0,[z190,z1,z2,z12,z4,z5])],[(0,[z1,z11,z191,z12,z4,z5]),(0,[z1,z192,z2,z12,z4,z5]),(0,[z193,z53,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z49])],[(0,[z1,z100,z11,z194,z4,z5]),(0,[z195,z1,z11,z2,z120,z5])],[(0,[z1,z11,z196,z4,z5,z49]),(0,[z1,z11,z197,z12,z4,z5]),(0,[z122,z1,z11,z198,z4,z5]),(0,[z199,z11,z2,z12,z4,z200]),(0,[z1,z201,z100,z11,z4,z5]),(0,[z1,z11,z4,z202,z203,z5])],[(0,[z1,z204,z2,z12,z4,z5]),(0,[z20,z1,z205,z2,z4,z5]),(0,[z1,z206,z2,z12,z4,z5]),(0,[z207,z11,z2,z208,z4,z5])],[(0,[z0,z1,z209,z2,z4,z5]),(0,[z14,z1,z11,z210,z4,z5]),(0,[z1,z211,z2,z12,z4,z5]),(0,[z1,z212,z2,z12,z4,z5]),(0,[z1,z4,z5,z130,z48,z49])],[(0,[z213,z96,z2,z12,z4,z5]),(0,[z1,z11,z2,z12,z4,z214]),(0,[z1,z2,z215,z12,z4,z5]),(0,[z26,z216,z11,z2,z4,z5]),(0,[z26,z1,z2,z217,z4,z5]),(0,[z53,z1,z2,z4,z5,z218])],[(0,[z219,z1,z2,z4,z59,z5]),(0,[z40,z1,z220,z2,z4,z5]),(0,[z1,z2,z221,z4,z5,z222])],[(0,[z223,z1,z11,z2,z4,z5])],[(0,[z97,z1,z2,z12,z4,z5]),(0,[z20,z1,z11,z196,z4,z5]),(0,[z224,z1,z11,z4,z5,z49]),(0,[z1,z171,z186,z137,z4,z5]),(0,[z1,z11,z2,z225,z4,z5]),(0,[z122,z1,z11,z43,z4,z5])]],
   [[(0,[z29,z100,z30,z2,z4,z5]),(0,[z226,z1,z11,z2,z4,z5]),(0,[z14,z1,z11,z154,z4,z5]),(0,[z1,z11,z2,z3,z167,z5]),(0,[z1,z227,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z228])],[(0,[z26,z1,z11,z229,z4,z5]),(1,[z11,z2,z12,z4,z230]),(0,[z24,z1,z220,z2,z4,z5])],[(0,[z231,z1,z11,z2,z12,z61]),(0,[z26,z1,z232,z2,z4,z5]),(0,[z1,z21,z11,z233,z4,z5])],[(0,[z1,z11,z2,z234,z4,z5]),(0,[z1,z11,z235,z12,z236,z5])],[(0,[z40,z26,z153,z2,z4,z5]),(0,[z237,z11,z2,z12,z4,z5]),(0,[z1,z206,z2,z187,z4,z5])],[(0,[z1,z11,z38,z12,z4,z5]),(0,[z1,z11,z2,z4,z238,z5]),(0,[z74,z11,z2,z12,z4,z230])],[(0,[z39,z1,z11,z2,z4,z5])],[(0,[z1,z11,z38,z12,z4,z200])],[(0,[z1,z239,z11,z12,z4,z5]),(0,[z74,z11,z10,z2,z4,z75]),(0,[z1,z11,z240,z12,z4,z5]),(0,[z1,z2,z12,z241,z4,z5]),(0,[z1,z2,z12,z4,z5,z48]),(0,[z1,z2,z242,z4,z5,z49])],[(0,[z1,z11,z243,z12,z4,z5]),(0,[z53,z1,z2,z208,z4,z5])],[(0,[z1,z11,z2,z4,z244,z5]),(0,[z1,z245,z246,z2,z4,z5]),(0,[z247,z11,z2,z248,z4,z5]),(0,[z249,z1,z11,z188,z4,z5]),(0,[z1,z11,z2,z250,z4,z5]),(0,[z251,z1,z11,z2,z4,z5])],[(0,[z252,z96,z196,z12,z4,z5]),(0,[z216,z11,z2,z12,z4,z5])],[(0,[z1,z11,z154,z3,z4,z5])],[(0,[z26,z1,z2,z141,z4,z5]),(0,[z1,z2,z12,z19,z253,z5]),(0,[z1,z254,z11,z183,z4,z5])],[],[(0,[z26,z1,z2,z255,z4,z5]),(0,[z256,z1,z11,z2,z4,z5]),(0,[z1,z11,z257,z12,z4,z5]),(0,[z258,z53,z1,z2,z4,z5])],[(0,[z26,z1,z259,z2,z4,z5]),(0,[z260,z20,z1,z11,z4,z5]),(0,[z1,z261,z11,z2,z4,z5])],[(0,[z1,z262,z259,z2,z4,z5]),(0,[z1,z263,z2,z264,z4,z5]),(0,[z14,z1,z205,z2,z4,z5]),(0,[z1,z11,z265,z12,z4,z5]),(0,[z266,z1,z11,z2,z4,z5]),(0,[z20,z1,z267,z2,z4,z5]),(1,[z1,z11,z2,z12,z268])],[(0,[z1,z11,z2,z4,z5,z269]),(0,[z1,z11,z2,z270,z4,z5]),(0,[z14,z1,z11,z271,z4,z5])],[(0,[z1,z171,z11,z2,z4,z5]),(0,[z20,z1,z11,z4,z272,z5]),(1,[z26,z153,z2,z4,z5]),(0,[z1,z254,z11,z4,z5,z49])],[(0,[z1,z273,z11,z2,z4,z5]),(0,[z26,z274,z1,z2,z4,z5]),(0,[z275,z14,z11,z2,z4,z60]),(0,[z276,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z277,z4,z5]),(0,[z1,z2,z12,z4,z278,z5]),(0,[z279,z11,z2,z12,z4,z5]),(0,[z1,z280,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z281,z5])],[(0,[z282,z163,z1,z12,z4,z5]),(0,[z283,z1,z11,z2,z4,z5])],[(0,[z14,z1,z11,z196,z4,z5]),(0,[z1,z11,z12,z4,z284,z5]),(0,[z151,z26,z1,z137,z4,z5]),(0,[z1,z11,z2,z4,z285,z5]),(0,[z1,z11,z2,z286,z4,z5]),(0,[z1,z18,z2,z233,z19,z5]),(0,[z1,z287,z2,z288,z4,z5])],[(0,[z82,z100,z11,z2,z59,z5]),(0,[z1,z206,z141,z12,z4,z5])],[(0,[z252,z96,z2,z289,z4,z5]),(0,[z26,z1,z2,z290,z4,z5]),(0,[z20,z1,z11,z4,z291,z5]),(0,[z26,z1,z292,z11,z4,z5]),(0,[z258,z1,z11,z2,z4,z5]),(0,[z0,z122,z1,z2,z4,z5])],[(0,[z1,z11,z2,z293,z4,z5])],[(0,[z20,z163,z1,z137,z4,z5]),(1,[z163,z1,z63,z4,z5]),(0,[z26,z1,z11,z4,z5,z294]),(0,[z39,z1,z11,z10,z4,z5]),(0,[z1,z2,z12,z4,z295,z5]),(0,[z1,z296,z11,z2,z4,z5]),(0,[z297,z122,z1,z11,z4,z5])],[(0,[z53,z298,z1,z2,z4,z5]),(0,[z26,z1,z141,z12,z4,z5])],[(0,[z1,z11,z2,z4,z299,z49]),(0,[z300,z1,z11,z2,z4,z5]),(0,[z190,z1,z2,z4,z114,z5])],[(0,[z1,z11,z2,z264,z4,z189]),(0,[z301,z1,z11,z2,z4,z5]),(0,[z302,z11,z2,z12,z4,z5]),(0,[z1,z11,z303,z2,z4,z5]),(0,[z304,z1,z11,z10,z2,z61])],[(0,[z1,z11,z2,z12,z4,z305]),(0,[z1,z11,z306,z2,z4,z5]),(0,[z40,z1,z2,z12,z307,z101]),(0,[z159,z1,z63,z11,z4,z5])],[(0,[z308,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z309,z4,z5]),(0,[z310,z0,z1,z2,z4,z5])]],
   [[(0,[z79,z11,z2,z311,z4,z5]),(0,[z26,z312,z1,z2,z4,z5]),(0,[z151,z1,z11,z313,z4,z5]),(0,[z20,z1,z11,z4,z314,z5]),(0,[z310,z122,z1,z11,z4,z5]),(0,[z85,z1,z2,z12,z4,z5])],[(0,[z1,z27,z235,z12,z4,z5])],[(0,[z1,z11,z2,z315,z4,z5]),(0,[z26,z1,z30,z2,z4,z5]),(0,[z26,z1,z11,z2,z316,z5]),(0,[z317,z1,z2,z12,z4,z5])],[(0,[z318,z1,z100,z2,z71,z5]),(0,[z1,z319,z2,z12,z4,z5]),(0,[z1,z320,z2,z321,z4,z5])],[(0,[z1,z11,z2,z12,z4,z322]),(0,[z11,z235,z12,z4,z5,z60]),(0,[z20,z1,z11,z323,z4,z5]),(0,[z1,z324,z11,z12,z111,z5])],[(0,[z252,z97,z2,z12,z4,z5]),(0,[z1,z325,z2,z12,z4,z5]),(0,[z1,z11,z2,z326,z4,z5]),(0,[z20,z163,z1,z4,z71,z5]),(0,[z1,z254,z12,z4,z71,z5]),(0,[z53,z1,z10,z54,z4,z5]),(0,[z1,z11,z2,z327,z4,z5]),(0,[z328,z1,z11,z2,z4,z5])],[(0,[z329,z96,z1,z2,z4,z5]),(0,[z330,z1,z11,z2,z4,z5]),(0,[z20,z1,z11,z2,z4,z189]),(0,[z1,z11,z2,z4,z5,z331]),(0,[z304,z0,z1,z2,z4,z5]),(0,[z160,z1,z2,z12,z4,z5])],[(0,[z332,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z12,z333,z200]),(0,[z39,z1,z11,z333,z4,z5]),(0,[z25,z100,z11,z2,z4,z5]),(0,[z1,z100,z2,z147,z4,z5]),(0,[z159,z1,z11,z2,z4,z334]),(0,[z0,z335,z1,z2,z4,z5]),(0,[z304,z122,z1,z11,z4,z5])],[(0,[z20,z1,z11,z336,z4,z5]),(0,[z1,z11,z337,z118,z4,z5])],[(0,[z26,z1,z2,z338,z71,z5])],[(0,[z96,z1,z2,z339,z4,z5]),(0,[z340,z1,z11,z2,z4,z5])],[(0,[z26,z1,z2,z341,z4,z5]),(0,[z53,z1,z2,z338,z4,z5]),(0,[z216,z11,z194,z12,z4,z5])],[],[(0,[z342,z1,z11,z2,z4,z5]),(0,[z1,z343,z11,z2,z4,z5]),(0,[z1,z11,z2,z344,z4,z5]),(0,[z1,z11,z2,z4,z345,z5])],[(0,[z26,z1,z11,z2,z167,z5]),(0,[z1,z346,z11,z10,z4,z5])],[(0,[z1,z263,z2,z12,z4,z5]),(0,[z1,z11,z347,z2,z4,z5]),(0,[z1,z11,z2,z12,z4,z348]),(0,[z185,z1,z137,z12,z4,z5]),(0,[z1,z11,z2,z349,z4,z5]),(0,[z1,z11,z54,z22,z4,z5])],[(0,[z82,z11,z10,z2,z59,z5]),(0,[z350,z11,z2,z4,z5,z49])],[(0,[z40,z1,z2,z12,z4,z101]),(0,[z122,z1,z11,z4,z5,z101]),(0,[z1,z351,z2,z169,z4,z5])],[(0,[z1,z11,z2,z4,z5,z352]),(0,[z26,z1,z2,z4,z353,z5])],[(0,[z1,z354,z2,z12,z4,z5]),(0,[z1,z206,z12,z4,z114,z5]),(0,[z0,z1,z2,z4,z5,z355])],[(0,[z1,z259,z2,z12,z4,z5]),(0,[z356,z1,z11,z2,z4,z5]),(0,[z1,z2,z162,z137,z4,z5]),(0,[z125,z1,z11,z2,z4,z5]),(0,[z53,z1,z2,z4,z180,z5]),(0,[z20,z1,z357,z2,z4,z5]),(0,[z350,z11,z2,z169,z4,z5])],[(0,[z20,z1,z358,z11,z4,z5]),(0,[z20,z1,z11,z359,z4,z5]),(0,[z360,z1,z11,z2,z4,z5])],[(0,[z53,z1,z2,z221,z4,z5]),(0,[z1,z11,z2,z4,z5,z77])],[(0,[z26,z1,z361,z2,z4,z5]),(0,[z1,z100,z11,z2,z307,z5]),(0,[z1,z11,z362,z12,z4,z5]),(0,[z122,z1,z11,z4,z5,z48]),(0,[z1,z363,z118,z12,z4,z5])],[(0,[z1,z11,z364,z12,z4,z5]),(0,[z74,z11,z2,z4,z75,z365]),(0,[z366,z1,z11,z2,z4,z5]),(0,[z123,z363,z2,z12,z4,z5])],[(0,[z1,z100,z2,z4,z5,z367]),(0,[z1,z254,z18,z12,z4,z5]),(0,[z1,z11,z10,z2,z338,z37])],[(0,[z1,z368,z2,z12,z4,z5]),(0,[z1,z11,z369,z12,z4,z5]),(0,[z20,z1,z11,z4,z5,z370])],[(0,[z26,z9,z1,z2,z4,z5]),(0,[z1,z11,z2,z12,z4,z189])],[(0,[z1,z11,z2,z4,z5,z371]),(0,[z372,z11,z2,z4,z5,z355])],[(0,[z1,z11,z2,z373,z4,z5]),(0,[z1,z11,z2,z4,z49,z374])],[(0,[z26,z1,z11,z188,z4,z5]),(0,[z1,z375,z11,z2,z4,z5]),(0,[z26,z24,z1,z4,z66,z5])],[(0,[z20,z1,z117,z11,z376,z5])]],
   [[(0,[z377,z1,z11,z2,z4,z5]),(0,[z1,z11,z378,z2,z4,z5])],[(0,[z1,z11,z379,z12,z4,z5])],[(0,[z1,z137,z12,z4,z5,z380]),(0,[z40,z122,z1,z11,z4,z5]),(0,[z381,z1,z2,z4,z382,z5])],[(0,[z1,z6,z2,z4,z5,z49]),(0,[z1,z11,z154,z4,z5,z49]),(0,[z1,z11,z2,z4,z383,z5])],[(0,[z1,z11,z4,z384,z385,z5]),(0,[z1,z11,z2,z386,z5,z387])],[(0,[z1,z11,z2,z388,z4,z5]),(0,[z1,z11,z2,z5,z49,z389])],[(0,[z26,z1,z246,z2,z4,z5]),(0,[z20,z1,z11,z390,z4,z5])],[(0,[z1,z11,z118,z288,z4,z5])],[(0,[z1,z11,z2,z12,z391,z5]),(0,[z123,z11,z2,z288,z4,z5])],[(0,[z40,z26,z1,z2,z307,z5]),(0,[z26,z1,z2,z4,z382,z5]),(0,[z1,z2,z241,z392,z4,z5])],[(0,[z129,z1,z100,z11,z4,z5]),(0,[z393,z11,z2,z12,z4,z5]),(0,[z20,z1,z11,z4,z203,z5])],[(0,[z394,z1,z11,z2,z4,z5]),(0,[z14,z1,z357,z2,z4,z5])],[(0,[z1,z100,z11,z2,z4,z200]),(0,[z1,z117,z11,z12,z395,z5]),(0,[z396,z1,z11,z2,z397,z5]),(0,[z14,z1,z11,z2,z4,z398])],[(0,[z1,z11,z2,z4,z5,z399]),(0,[z1,z11,z400,z12,z4,z5]),(0,[z1,z11,z10,z2,z236,z5]),(0,[z20,z401,z1,z11,z4,z5]),(0,[z26,z24,z1,z313,z4,z5]),(0,[z24,z1,z11,z220,z4,z5]),(0,[z0,z1,z134,z2,z4,z5]),(0,[z159,z53,z1,z2,z4,z5])],[(0,[z40,z1,z141,z12,z4,z101]),(0,[z1,z11,z10,z2,z402,z5]),(0,[z1,z11,z320,z54,z4,z5]),(0,[z1,z11,z43,z65,z4,z66]),(0,[z1,z11,z403,z12,z4,z5]),(0,[z247,z0,z1,z2,z4,z5])],[(0,[z404,z1,z2,z12,z71,z5]),(0,[z20,z163,z96,z1,z4,z5]),(0,[z1,z6,z2,z405,z4,z5]),(0,[z1,z406,z2,z12,z4,z5]),(0,[z1,z11,z407,z12,z4,z5]),(0,[z408,z1,z11,z2,z4,z5]),(0,[z409,z1,z11,z2,z12,z61]),(0,[z247,z122,z1,z11,z4,z5])],[(0,[z53,z1,z410,z2,z4,z5]),(0,[z411,z11,z10,z2,z4,z5]),(0,[z14,z1,z11,z2,z4,z144])],[(0,[z412,z298,z1,z11,z4,z5]),(0,[z20,z1,z11,z2,z413,z5]),(0,[z1,z63,z11,z137,z4,z5]),(1,[z122,z1,z11,z4,z5]),(0,[z53,z1,z2,z147,z4,z5]),(0,[z1,z292,z11,z46,z4,z5])],[(0,[z1,z2,z12,z4,z5,z414]),(0,[z55,z11,z2,z12,z307,z5]),(0,[z20,z1,z206,z2,z4,z5]),(0,[z415,z11,z2,z12,z4,z5]),(0,[z1,z11,z416,z2,z4,z5])],[(0,[z14,z1,z11,z2,z4,z417])],[(0,[z20,z11,z108,z4,z5,z60]),(0,[z418,z1,z11,z2,z4,z5]),(0,[z122,z1,z11,z137,z4,z5]),(0,[z419,z26,z1,z2,z4,z5])],[(1,[z20,z1,z357,z4,z5]),(0,[z14,z1,z2,z4,z5,z48]),(0,[z1,z363,z2,z4,z5,z49]),(0,[z1,z420,z11,z4,z5,z49])],[(0,[z1,z421,z2,z12,z4,z5]),(0,[z422,z53,z1,z2,z4,z5]),(0,[z151,z1,z11,z137,z4,z5]),(0,[z26,z1,z11,z65,z4,z66]),(0,[z1,z2,z183,z4,z180,z5]),(0,[z1,z11,z2,z4,z5,z423])],[(0,[z1,z424,z137,z12,z4,z5]),(0,[z300,z1,z11,z154,z4,z5])],[(0,[z1,z11,z425,z12,z4,z5]),(1,[z26,z1,z2,z307,z5]),(0,[z53,z1,z10,z2,z4,z5]),(0,[z1,z11,z2,z46,z426,z5])],[(0,[z151,z1,z30,z2,z4,z5]),(0,[z1,z11,z2,z4,z427,z5])],[(0,[z26,z1,z11,z235,z4,z5])],[(0,[z1,z11,z2,z4,z5,z222]),(0,[z1,z11,z2,z428,z4,z5]),(0,[z429,z1,z11,z2,z4,z5]),(0,[z430,z11,z2,z12,z4,z5])],[(0,[z40,z26,z1,z2,z4,z5]),(0,[z304,z39,z1,z11,z4,z5]),(0,[z431,z11,z2,z12,z4,z5])],[(0,[z432,z1,z11,z2,z4,z5]),(0,[z9,z1,z2,z433,z4,z5]),(0,[z1,z11,z2,z4,z5,z434])],[(0,[z1,z63,z11,z108,z4,z5]),(0,[z0,z199,z1,z2,z4,z5]),(0,[z26,z1,z153,z2,z4,z5]),(0,[z1,z11,z2,z435,z84,z5]),(0,[z1,z2,z4,z5,z49,z367])],[(0,[z26,z0,z1,z2,z4,z5]),(0,[z122,z1,z11,z4,z71,z5]),(0,[z1,z436,z11,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z137,z4,z5]),(0,[z26,z122,z1,z11,z4,z5]),(0,[z437,z1,z11,z4,z5,z222]),(0,[z159,z20,z1,z11,z4,z5]),(0,[z1,z11,z2,z4,z5,z438])],[(0,[z1,z439,z11,z2,z4,z5]),(0,[z26,z1,z2,z4,z440,z5]),(0,[z1,z134,z2,z4,z180,z49]),(0,[z1,z10,z2,z215,z4,z5]),(0,[z1,z2,z12,z4,z441,z5]),(0,[z14,z1,z11,z4,z203,z5]),(0,[z442,z0,z1,z2,z4,z5])],[(0,[z122,z74,z1,z11,z4,z5]),(0,[z1,z2,z147,z12,z4,z5]),(0,[z26,z1,z100,z210,z4,z5]),(0,[z335,z1,z11,z10,z114,z5]),(0,[z1,z11,z54,z12,z84,z5]),(0,[z1,z11,z12,z4,z443,z218])],[(0,[z1,z11,z10,z2,z4,z5]),(0,[z444,z1,z11,z2,z4,z5]),(0,[z26,z1,z445,z11,z4,z5]),(0,[z1,z446,z2,z12,z4,z5])],[(0,[z1,z11,z447,z12,z4,z5]),(0,[z1,z11,z2,z448,z4,z5]),(1,[z1,z11,z22,z4,z5]),(0,[z304,z14,z1,z11,z2,z61])],[(0,[z55,z11,z2,z12,z4,z5]),(0,[z1,z11,z2,z449,z4,z5]),(0,[z1,z11,z12,z4,z5,z450]),(0,[z0,z1,z2,z4,z5,z451])],[(0,[z1,z11,z2,z12,z413,z5]),(0,[z1,z11,z10,z452,z4,z5]),(0,[z122,z1,z11,z453,z4,z5]),(0,[z14,z1,z11,z454,z4,z5])],[(0,[z1,z11,z2,z12,z455,z5]),(0,[z1,z30,z220,z2,z4,z5]),(0,[z20,z1,z134,z2,z4,z180]),(0,[z1,z11,z10,z2,z33,z5]),(0,[z456,z122,z1,z11,z4,z5])],[(0,[z20,z224,z1,z11,z4,z5]),(0,[z14,z1,z11,z2,z413,z5]),(0,[z26,z1,z11,z194,z4,z5]),(0,[z14,z1,z107,z2,z4,z5])],[(0,[z1,z11,z2,z4,z5,z457]),(0,[z14,z1,z206,z2,z4,z5])],[(0,[z298,z1,z11,z405,z4,z5]),(0,[z458,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z459,z4,z5]),(0,[z460,z1,z11,z2,z4,z5])],[(0,[z1,z27,z10,z2,z4,z5]),(0,[z1,z461,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z462]),(0,[z26,z1,z18,z2,z463,z5]),(0,[z153,z100,z11,z2,z4,z5]),(0,[z20,z1,z11,z169,z4,z5]),(0,[z53,z53,z1,z2,z4,z5])],[],[(0,[z0,z1,z2,z108,z4,z5]),(0,[z39,z1,z18,z11,z4,z5]),(0,[z20,z1,z117,z11,z114,z5])],[(0,[z26,z1,z11,z464,z4,z5]),(0,[z1,z465,z2,z12,z4,z5]),(0,[z1,z27,z2,z12,z413,z5]),(0,[z1,z11,z2,z466,z4,z5]),(0,[z151,z1,z361,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z467])],[(0,[z26,z1,z11,z468,z4,z5]),(0,[z40,z1,z11,z2,z4,z135]),(0,[z1,z100,z469,z2,z4,z5]),(0,[z1,z21,z18,z12,z19,z5]),(0,[z20,z1,z11,z73,z4,z5])],[(0,[z26,z1,z2,z4,z307,z5]),(0,[z1,z100,z11,z2,z470,z5]),(0,[z471,z11,z2,z12,z4,z5])],[(0,[z29,z262,z30,z2,z4,z5]),(0,[z1,z263,z38,z12,z4,z5])],[(0,[z472,z1,z11,z2,z4,z5]),(0,[z473,z1,z11,z2,z4,z5]),(0,[z1,z21,z11,z12,z4,z5])],[(0,[z1,z11,z2,z474,z4,z5]),(0,[z475,z11,z2,z248,z4,z5]),(0,[z476,z1,z11,z2,z4,z5])],[(0,[z53,z1,z11,z2,z4,z5]),(0,[z477,z1,z11,z2,z4,z5])],[(0,[z26,z153,z2,z12,z4,z5])],[(0,[z1,z11,z478,z12,z4,z5]),(0,[z39,z1,z11,z46,z4,z5]),(0,[z122,z1,z11,z19,z4,z5]),(1,[z159,z1,z11,z4,z77])],[],[(0,[z20,z1,z11,z479,z4,z5]),(0,[z1,z11,z2,z480,z4,z5]),(0,[z20,z1,z11,z4,z481,z5]),(0,[z1,z11,z2,z4,z482,z5]),(0,[z1,z11,z483,z141,z4,z5]),(0,[z122,z1,z209,z11,z4,z5])],[(0,[z484,z1,z11,z2,z4,z5])],[(0,[z485,z1,z11,z2,z4,z5]),(0,[z486,z11,z108,z4,z5,z49]),(0,[z1,z11,z2,z487,z4,z5]),(0,[z53,z1,z2,z4,z75,z5])],[(0,[z1,z11,z220,z65,z4,z5]),(0,[z1,z254,z100,z11,z4,z5]),(0,[z1,z2,z221,z4,z384,z5]),(0,[z318,z1,z2,z12,z71,z5]),(0,[z1,z357,z2,z169,z4,z5])],[(0,[z1,z100,z11,z257,z4,z5])],[(0,[z1,z11,z38,z12,z4,z189]),(0,[z122,z1,z11,z4,z5,z60]),(0,[z26,z282,z1,z2,z4,z5]),(0,[z488,z1,z11,z12,z4,z5]),(0,[z1,z11,z2,z4,z489,z5])],[(0,[z1,z11,z12,z4,z490,z5]),(0,[z39,z1,z11,z11,z4,z5])],[(0,[z14,z224,z1,z11,z4,z5]),(0,[z20,z1,z58,z2,z4,z5]),(0,[z20,z1,z11,z4,z5,z491]),(0,[z1,z11,z2,z4,z492,z5]),(0,[z40,z20,z1,z2,z4,z101]),(0,[z136,z1,z11,z2,z4,z5])]],
   [[(0,[z1,z58,z2,z4,z5,z49]),(0,[z1,z11,z2,z413,z5,z49]),(0,[z163,z1,z63,z11,z4,z5]),(0,[z122,z1,z11,z493,z4,z5])],[(0,[z26,z1,z2,z494,z4,z5]),(0,[z1,z134,z2,z12,z4,z72]),(0,[z1,z11,z320,z2,z4,z5])],[(0,[z132,z11,z229,z198,z4,z5]),(0,[z55,z11,z141,z12,z4,z5])],[(0,[z1,z2,z4,z5,z495,z49])],[(0,[z26,z96,z496,z2,z4,z5]),(0,[z82,z58,z2,z12,z59,z5]),(0,[z1,z11,z2,z497,z4,z5]),(0,[z24,z163,z1,z10,z4,z5]),(0,[z1,z11,z2,z498,z4,z5])],[(0,[z1,z11,z2,z499,z4,z5])],[(0,[z53,z1,z2,z392,z4,z5]),(0,[z1,z100,z11,z4,z5,z130])],[(1,[z185,z1,z12,z4,z5])],[(0,[z500,z1,z11,z2,z4,z5]),(0,[z26,z1,z11,z4,z157,z5])],[(0,[z1,z11,z2,z501,z4,z5]),(0,[z1,z106,z2,z4,z502,z5])],[],[(0,[z1,z11,z503,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z135]),(0,[z1,z117,z100,z11,z111,z5])],[(0,[z20,z1,z11,z504,z4,z5]),(0,[z1,z100,z11,z2,z505,z5]),(0,[z1,z2,z12,z4,z5,z506])],[(0,[z1,z11,z2,z4,z5,z507]),(0,[z26,z1,z2,z508,z4,z5])],[(0,[z509,z1,z11,z2,z4,z5]),(0,[z510,z11,z108,z12,z4,z5]),(0,[z82,z0,z1,z2,z4,z5]),(0,[z511,z1,z11,z2,z4,z5])],[(0,[z82,z122,z1,z11,z4,z5]),(0,[z1,z11,z2,z4,z5,z512]),(0,[z14,z1,z11,z4,z481,z5]),(0,[z153,z11,z2,z12,z167,z5]),(0,[z20,z25,z11,z12,z4,z5]),(0,[z53,z1,z2,z4,z513,z5]),(0,[z1,z206,z117,z12,z4,z5]),(0,[z0,z0,z1,z2,z4,z5]),(0,[z304,z1,z11,z2,z49,z61])],[(0,[z62,z1,z11,z4,z75,z5]),(0,[z24,z163,z1,z514,z4,z5]),(0,[z26,z1,z2,z515,z4,z5]),(0,[z89,z1,z11,z2,z4,z5]),(0,[z0,z122,z1,z11,z4,z5])],[(0,[z516,z11,z2,z12,z4,z5]),(0,[z39,z1,z11,z4,z37,z5])],[(0,[z517,z29,z30,z2,z4,z5]),(0,[z518,z1,z11,z2,z4,z5]),(0,[z1,z11,z65,z2,z4,z334])],[(0,[z20,z163,z1,z30,z4,z5]),(0,[z50,z1,z11,z4,z5,z135]),(0,[z519,z1,z11,z12,z114,z5])],[(0,[z1,z11,z520,z12,z4,z5]),(0,[z1,z186,z2,z12,z307,z5]),(0,[z521,z1,z11,z2,z4,z522]),(0,[z122,z1,z11,z523,z4,z5]),(0,[z524,z1,z2,z12,z4,z5])],[(0,[z1,z11,z2,z525,z4,z5]),(0,[z1,z205,z2,z4,z5,z49]),(0,[z1,z11,z210,z12,z4,z5]),(0,[z26,z1,z45,z2,z4,z5]),(0,[z526,z1,z11,z4,z384,z5]),(0,[z317,z1,z2,z4,z5,z77]),(0,[z1,z11,z2,z527,z4,z5]),(0,[z1,z11,z2,z459,z4,z528]),(0,[z122,z122,z1,z11,z4,z5])],[(0,[z529,z1,z2,z12,z4,z5]),(0,[z1,z11,z530,z4,z66,z5]),(0,[z1,z11,z531,z12,z4,z5]),(0,[z20,z1,z11,z532,z4,z5])],[(0,[z1,z11,z2,z4,z533,z5]),(0,[z53,z486,z1,z2,z4,z5]),(0,[z40,z26,z1,z154,z4,z5]),(0,[z1,z11,z2,z4,z5,z534])],[(0,[z1,z11,z2,z4,z5,z535]),(0,[z1,z11,z2,z536,z4,z5]),(0,[z159,z20,z1,z11,z4,z66]),(0,[z1,z537,z2,z12,z4,z5]),(0,[z42,z1,z2,z12,z4,z5])],[],[(0,[z1,z11,z2,z4,z5,z538]),(0,[z1,z206,z10,z2,z4,z5])],[(0,[z1,z11,z2,z4,z5,z365]),(0,[z1,z11,z539,z38,z4,z5]),(0,[z1,z11,z540,z235,z4,z5]),(0,[z153,z11,z154,z12,z4,z5]),(0,[z159,z20,z1,z351,z4,z5]),(0,[z1,z211,z10,z2,z4,z5])],[(0,[z1,z11,z2,z12,z5,z389]),(0,[z1,z11,z2,z288,z4,z5])],[(0,[z103,z1,z2,z12,z4,z5]),(0,[z541,z11,z2,z12,z4,z5])],[(0,[z26,z542,z1,z2,z4,z5]),(0,[z252,z96,z2,z4,z5,z49]),(0,[z151,z1,z11,z220,z4,z5]),(0,[z543,z11,z2,z12,z4,z5]),(0,[z1,z11,z10,z154,z4,z5])],[(0,[z122,z1,z11,z248,z4,z5])]],
   [[(0,[z1,z544,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z545]),(0,[z1,z11,z546,z12,z4,z5]),(0,[z547,z1,z11,z194,z4,z5])],[],[(0,[z422,z548,z11,z12,z4,z5]),(0,[z275,z39,z1,z11,z4,z5]),(0,[z1,z11,z2,z549,z4,z5])],[(0,[z275,z11,z2,z12,z4,z230]),(0,[z14,z350,z11,z2,z4,z5])],[(0,[z26,z1,z2,z4,z550,z5]),(0,[z122,z335,z1,z11,z4,z5]),(0,[z25,z11,z2,z169,z4,z5]),(0,[z551,z122,z1,z11,z4,z5])],[(0,[z552,z1,z11,z2,z4,z5]),(0,[z1,z287,z118,z12,z4,z5])],[(0,[z26,z1,z2,z553,z4,z5]),(0,[z20,z1,z137,z221,z4,z5]),(0,[z123,z287,z2,z12,z4,z5])],[(0,[z26,z1,z2,z4,z554,z5]),(0,[z9,z1,z2,z4,z5,z49]),(0,[z1,z2,z137,z4,z5,z135]),(0,[z1,z11,z2,z12,z555,z5]),(0,[z1,z2,z12,z382,z5,z61])],[(0,[z40,z153,z2,z12,z4,z101]),(0,[z122,z1,z11,z12,z4,z5]),(0,[z556,z1,z351,z2,z4,z5])],[(0,[z26,z1,z18,z2,z4,z5]),(0,[z26,z1,z2,z4,z5,z367])],[(0,[z252,z39,z1,z11,z4,z5]),(0,[z1,z445,z11,z12,z4,z5]),(0,[z39,z557,z1,z11,z4,z5])],[(0,[z558,z11,z2,z12,z4,z60]),(0,[z1,z559,z263,z2,z4,z5]),(0,[z560,z39,z1,z11,z4,z5]),(0,[z216,z11,z10,z2,z4,z5]),(0,[z1,z11,z2,z561,z4,z5])],[(0,[z97,z30,z2,z12,z4,z5]),(0,[z1,z186,z10,z137,z4,z5]),(0,[z1,z100,z11,z2,z562,z5]),(0,[z159,z20,z350,z11,z4,z5]),(0,[z20,z1,z324,z11,z4,z5]),(0,[z563,z11,z2,z12,z4,z5]),(0,[z1,z363,z194,z12,z4,z5])],[(0,[z564,z1,z11,z12,z4,z5]),(0,[z1,z11,z565,z2,z4,z5]),(0,[z40,z26,z1,z2,z4,z101]),(0,[z39,z1,z566,z11,z4,z5]),(0,[z153,z11,z2,z3,z4,z5]),(0,[z20,z1,z11,z141,z4,z5]),(0,[z20,z216,z11,z2,z4,z5]),(0,[z1,z11,z65,z12,z84,z5])],[(0,[z1,z11,z567,z12,z4,z5]),(0,[z224,z132,z11,z198,z4,z5]),(0,[z26,z1,z2,z162,z4,z5]),(0,[z53,z1,z2,z4,z5,z61])],[],[(0,[z568,z1,z11,z12,z4,z5]),(0,[z1,z11,z2,z569,z4,z5]),(0,[z1,z11,z2,z4,z5,z570]),(0,[z571,z572,z11,z2,z4,z5])],[(0,[z1,z11,z2,z12,z573,z5]),(0,[z20,z1,z574,z11,z4,z5]),(0,[z575,z1,z11,z2,z4,z5])],[(0,[z1,z11,z576,z12,z4,z5]),(0,[z20,z1,z11,z229,z4,z5]),(0,[z1,z11,z257,z12,z413,z5]),(0,[z190,z1,z11,z2,z4,z5]),(0,[z1,z2,z12,z338,z382,z5]),(0,[z1,z11,z65,z12,z4,z66])],[(0,[z577,z30,z2,z12,z4,z5]),(0,[z1,z186,z63,z2,z4,z5])],[(0,[z1,z11,z10,z196,z4,z5]),(0,[z1,z2,z221,z3,z4,z5]),(0,[z1,z11,z2,z459,z4,z77])],[(0,[z578,z1,z2,z12,z4,z101]),(0,[z579,z1,z11,z2,z4,z5]),(0,[z20,z1,z11,z4,z5,z580]),(0,[z20,z1,z11,z4,z202,z5]),(0,[z1,z2,z12,z4,z5,z581])],[(0,[z1,z582,z2,z12,z4,z5]),(0,[z53,z1,z65,z2,z4,z5]),(0,[z1,z2,z46,z433,z278,z5])],[(0,[z1,z2,z583,z584,z4,z5]),(0,[z585,z1,z11,z2,z4,z5]),(0,[z39,z586,z1,z11,z4,z5])],[(0,[z1,z11,z587,z12,z4,z5]),(0,[z39,z1,z11,z4,z59,z5]),(0,[z39,z1,z11,z4,z588,z5])],[(0,[z1,z58,z2,z12,z4,z200]),(0,[z589,z1,z11,z2,z590,z5])],[(0,[z26,z1,z2,z591,z4,z5]),(0,[z1,z592,z2,z12,z4,z5])],[(0,[z125,z1,z11,z2,z4,z398])],[(0,[z1,z593,z11,z12,z4,z5]),(0,[z26,z1,z11,z2,z4,z200]),(0,[z74,z11,z2,z12,z413,z5]),(1,[z24,z1,z220,z4,z5]),(0,[z1,z594,z11,z2,z4,z5]),(0,[z14,z1,z11,z118,z4,z5]),(0,[z1,z11,z194,z288,z4,z5])],[(0,[z1,z11,z2,z595,z4,z5]),(0,[z20,z1,z11,z4,z596,z5])],[(0,[z1,z11,z2,z4,z597,z5]),(0,[z1,z11,z2,z4,z598,z5]),(0,[z599,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z600,z5]),(0,[z1,z11,z233,z4,z481,z5]),(0,[z1,z11,z2,z601,z4,z5])],[(0,[z1,z602,z30,z2,z4,z5]),(0,[z1,z11,z2,z603,z4,z49]),(0,[z1,z11,z2,z604,z4,z5])]],
   [[(0,[z26,z1,z2,z4,z605,z5]),(0,[z1,z606,z2,z12,z4,z5])],[(0,[z20,z1,z259,z2,z4,z5]),(0,[z219,z1,z2,z12,z4,z5]),(0,[z1,z106,z2,z4,z5,z49])],[(0,[z1,z100,z11,z2,z4,z189]),(0,[z1,z186,z607,z12,z4,z5]),(0,[z608,z1,z11,z2,z4,z5])],[(0,[z1,z609,z11,z2,z4,z49]),(0,[z14,z1,z11,z2,z4,z610])],[(0,[z82,z11,z2,z178,z59,z5]),(0,[z1,z186,z141,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z611]),(0,[z14,z1,z11,z141,z4,z5]),(0,[z14,z216,z11,z2,z4,z5])],[(0,[z1,z11,z2,z4,z5,z612]),(0,[z20,z1,z11,z4,z613,z5]),(0,[z1,z11,z2,z12,z614,z5]),(0,[z1,z2,z4,z5,z367,z615])],[(0,[z20,z1,z11,z583,z4,z5]),(0,[z1,z11,z616,z12,z4,z5]),(0,[z20,z163,z1,z361,z4,z5]),(0,[z159,z1,z100,z11,z4,z218]),(0,[z617,z11,z2,z12,z4,z5]),(0,[z1,z11,z618,z2,z4,z5])],[(0,[z1,z11,z2,z7,z4,z5])],[(0,[z1,z11,z2,z311,z4,z5]),(0,[z0,z1,z2,z54,z4,z5])],[(0,[z1,z11,z2,z12,z619,z5]),(0,[z14,z1,z11,z229,z4,z5]),(0,[z318,z20,z1,z2,z71,z5]),(0,[z1,z11,z620,z12,z4,z5]),(0,[z20,z1,z292,z11,z4,z5])],[(0,[z1,z11,z621,z12,z4,z5]),(1,[z526,z1,z11,z4,z5]),(0,[z122,z1,z134,z11,z4,z5]),(0,[z1,z622,z2,z4,z5,z49])],[(0,[z1,z63,z11,z4,z114,z5])],[(0,[z1,z11,z2,z4,z5,z623]),(0,[z1,z11,z2,z624,z4,z5]),(0,[z1,z11,z2,z4,z625,z5])],[(0,[z122,z1,z11,z30,z4,z5]),(0,[z39,z1,z11,z198,z4,z5]),(0,[z40,z1,z2,z514,z4,z5])],[(0,[z1,z11,z235,z626,z4,z5]),(0,[z1,z11,z2,z627,z4,z5]),(0,[z26,z1,z2,z452,z4,z5]),(0,[z122,z1,z11,z4,z114,z5])],[(0,[z1,z246,z100,z2,z4,z5]),(0,[z1,z263,z10,z2,z4,z5]),(0,[z20,z1,z11,z4,z5,z67])],[(0,[z1,z11,z628,z12,z4,z5]),(0,[z151,z1,z11,z4,z114,z5]),(0,[z20,z1,z11,z137,z4,z5]),(0,[z39,z1,z11,z479,z4,z5]),(0,[z1,z45,z2,z12,z4,z5]),(0,[z40,z14,z1,z2,z4,z101]),(0,[z1,z254,z357,z12,z4,z5]),(1,[z20,z25,z11,z4,z5])],[(0,[z1,z246,z108,z12,z4,z5]),(0,[z20,z1,z11,z4,z629,z5]),(0,[z1,z11,z2,z4,z200,z49]),(0,[z1,z11,z2,z12,z630,z5]),(0,[z26,z1,z11,z621,z4,z5]),(0,[z1,z11,z2,z167,z5,z49]),(0,[z40,z1,z10,z2,z4,z101])],[(0,[z24,z1,z11,z320,z4,z5]),(0,[z1,z2,z12,z4,z631,z5])],[(0,[z1,z11,z2,z4,z178,z5])],[(0,[z1,z259,z10,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z632]),(0,[z1,z11,z12,z4,z5,z633]),(0,[z1,z126,z11,z2,z4,z5])],[(0,[z1,z11,z634,z12,z4,z5]),(0,[z568,z1,z11,z30,z4,z5])],[(0,[z1,z11,z2,z635,z4,z5]),(0,[z26,z24,z163,z1,z4,z5])],[(0,[z1,z11,z2,z636,z4,z5]),(0,[z14,z39,z1,z11,z4,z5]),(0,[z123,z11,z118,z12,z4,z5])],[(0,[z14,z1,z259,z2,z4,z5]),(0,[z1,z2,z12,z4,z5,z637]),(0,[z14,z335,z1,z11,z114,z5]),(0,[z1,z43,z2,z4,z5,z48])],[(0,[z26,z486,z11,z108,z4,z5]),(0,[z0,z1,z2,z111,z4,z5]),(0,[z638,z1,z11,z4,z5,z49])],[(0,[z1,z639,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z640,z5]),(0,[z1,z11,z2,z146,z4,z5]),(0,[z20,z163,z1,z63,z4,z5])],[(0,[z1,z11,z10,z2,z4,z189]),(0,[z122,z199,z1,z11,z4,z5]),(0,[z11,z2,z12,z4,z75,z230]),(0,[z1,z11,z641,z12,z4,z5])],[(0,[z1,z205,z2,z642,z4,z5]),(0,[z53,z1,z2,z4,z66,z5]),(0,[z85,z1,z11,z2,z4,z5])],[(0,[z20,z1,z11,z108,z4,z5]),(0,[z1,z643,z2,z12,z4,z5]),(0,[z83,z1,z11,z2,z4,z5]),(0,[z1,z644,z11,z2,z4,z5])],[(0,[z26,z74,z30,z2,z4,z5]),(0,[z275,z11,z2,z642,z4,z60]),(0,[z317,z1,z11,z2,z4,z5])],[(0,[z20,z298,z572,z11,z4,z5]),(0,[z24,z1,z357,z12,z4,z5]),(0,[z1,z18,z2,z514,z4,z5]),(0,[z1,z2,z12,z4,z180,z41]),(0,[z1,z11,z2,z4,z5,z645])]],
   [[(0,[z1,z11,z2,z4,z5,z646]),(0,[z24,z647,z1,z12,z4,z5]),(0,[z9,z1,z229,z12,z4,z5]),(0,[z151,z1,z18,z2,z4,z5]),(0,[z14,z1,z292,z11,z4,z5]),(0,[z247,z11,z2,z4,z5,z648])],[(0,[z1,z11,z649,z12,z4,z5])],[(0,[z650,z11,z2,z12,z4,z60]),(0,[z26,z1,z2,z651,z4,z5]),(0,[z1,z11,z2,z4,z5,z652]),(0,[z653,z1,z126,z2,z4,z5]),(0,[z160,z1,z11,z2,z4,z5])],[(0,[z40,z26,z1,z2,z4,z398])],[(0,[z1,z11,z2,z654,z4,z5]),(0,[z160,z1,z320,z2,z4,z5])],[(0,[z655,z1,z11,z2,z4,z5]),(0,[z1,z18,z12,z19,z481,z5]),(0,[z1,z11,z656,z12,z4,z5])],[(0,[z1,z11,z657,z12,z4,z5]),(0,[z74,z11,z2,z4,z75,z49]),(0,[z129,z1,z11,z2,z4,z5]),(0,[z39,z1,z100,z221,z4,z5]),(0,[z122,z1,z11,z4,z120,z5]),(0,[z658,z1,z11,z2,z4,z5])],[(0,[z1,z11,z659,z12,z4,z5]),(0,[z1,z11,z12,z4,z5,z660])],[(0,[z1,z11,z2,z626,z236,z5]),(0,[z1,z11,z2,z12,z316,z5]),(0,[z1,z2,z4,z661,z5,z367])],[(0,[z20,z1,z11,z2,z662,z5]),(0,[z1,z2,z12,z4,z5,z663])],[(0,[z1,z11,z664,z188,z4,z5]),(0,[z1,z351,z2,z12,z4,z5]),(0,[z20,z163,z1,z4,z180,z5]),(0,[z1,z254,z12,z4,z180,z5])],[(0,[z1,z209,z11,z2,z4,z5]),(0,[z1,z11,z12,z4,z5,z665]),(0,[z666,z667,z11,z2,z4,z5])],[(0,[z1,z11,z2,z668,z4,z5]),(0,[z26,z1,z11,z257,z4,z5]),(0,[z122,z1,z11,z4,z5,z218])],[(0,[z125,z1,z134,z2,z4,z180]),(0,[z335,z1,z11,z202,z114,z5]),(0,[z14,z25,z11,z2,z4,z5])],[(0,[z669,z1,z11,z2,z4,z5]),(0,[z26,z1,z670,z2,z4,z5]),(0,[z1,z11,z337,z2,z4,z5])],[(0,[z671,z11,z2,z12,z4,z60]),(0,[z1,z11,z2,z12,z672,z5]),(0,[z1,z11,z2,z433,z673,z5]),(0,[z122,z1,z11,z459,z4,z49]),(0,[z122,z1,z11,z4,z5,z674]),(0,[z1,z11,z2,z675,z4,z5])],[(0,[z1,z11,z676,z12,z4,z5])],[(0,[z1,z677,z100,z2,z4,z5])],[(0,[z678,z30,z2,z12,z4,z5]),(0,[z679,z1,z11,z2,z4,z5]),(0,[z680,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z681]),(0,[z682,z11,z2,z12,z4,z5])],[(0,[z1,z11,z2,z683,z4,z5]),(0,[z684,z1,z11,z2,z4,z5]),(0,[z1,z685,z2,z12,z4,z5])],[(0,[z1,z11,z2,z4,z5,z686]),(0,[z1,z11,z2,z12,z687,z5]),(0,[z1,z2,z12,z71,z5,z688]),(0,[z1,z11,z2,z689,z4,z5]),(0,[z53,z1,z2,z433,z4,z5]),(0,[z690,z11,z2,z12,z4,z5])],[(0,[z1,z10,z147,z54,z4,z5])],[(0,[z691,z1,z117,z11,z4,z5]),(0,[z216,z11,z2,z692,z4,z5])],[(0,[z693,z1,z11,z2,z4,z5]),(0,[z318,z26,z1,z2,z71,z5]),(0,[z159,z1,z11,z12,z562,z218])],[(0,[z1,z58,z188,z12,z4,z5]),(0,[z112,z39,z1,z11,z4,z5]),(0,[z694,z1,z11,z2,z4,z5]),(0,[z695,z1,z11,z2,z4,z334])],[(0,[z195,z224,z1,z11,z4,z5]),(0,[z231,z11,z2,z12,z59,z5]),(0,[z696,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z142,z167,z5])],[(0,[z697,z1,z2,z583,z4,z5]),(0,[z24,z163,z1,z530,z4,z5]),(0,[z1,z287,z2,z12,z4,z5])],[(0,[z11,z2,z311,z248,z4,z5]),(0,[z1,z698,z11,z2,z4,z5])],[(0,[z699,z1,z2,z12,z4,z5]),(0,[z20,z163,z1,z18,z4,z5])],[(0,[z159,z1,z11,z435,z4,z218])],[(0,[z20,z1,z11,z4,z5,z700]),(0,[z1,z11,z2,z12,z662,z5]),(0,[z304,z53,z1,z2,z4,z5])],[(0,[z1,z11,z108,z405,z4,z5]),(0,[z1,z11,z10,z4,z203,z5])]],
   [[(0,[z701,z11,z108,z12,z4,z5]),(0,[z14,z1,z11,z2,z4,z77])],[(0,[z1,z11,z12,z702,z114,z5])],[(0,[z703,z1,z11,z12,z4,z5]),(0,[z1,z11,z146,z54,z4,z5]),(0,[z26,z704,z1,z2,z4,z5]),(0,[z26,z1,z11,z4,z5,z450]),(0,[z39,z1,z705,z11,z4,z5])],[(0,[z1,z11,z137,z187,z4,z5]),(0,[z1,z100,z11,z2,z84,z5]),(0,[z1,z2,z12,z4,z706,z5])],[(0,[z1,z245,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z707]),(0,[z53,z1,z2,z4,z708,z5])],[(0,[z39,z1,z11,z4,z5,z101]),(0,[z55,z11,z10,z2,z4,z5]),(0,[z1,z11,z154,z142,z4,z5]),(0,[z0,z1,z2,z386,z4,z5]),(0,[z304,z123,z11,z2,z12,z61])],[(0,[z709,z1,z11,z2,z4,z5]),(0,[z1,z11,z710,z12,z4,z5]),(0,[z1,z11,z10,z2,z413,z5]),(0,[z1,z100,z11,z210,z4,z5])],[(0,[z20,z1,z711,z11,z4,z5]),(0,[z20,z1,z712,z2,z4,z5]),(0,[z1,z11,z2,z12,z4,z443])],[(0,[z1,z713,z2,z12,z4,z5]),(0,[z1,z11,z118,z12,z338,z5])],[(0,[z26,z1,z2,z4,z714,z5]),(0,[z26,z1,z117,z11,z111,z5]),(0,[z1,z715,z2,z12,z4,z5]),(0,[z159,z1,z11,z4,z661,z218]),(0,[z123,z11,z2,z12,z338,z5])],[(0,[z1,z716,z11,z2,z4,z5]),(0,[z458,z1,z10,z2,z4,z5]),(0,[z1,z10,z2,z4,z5,z367]),(0,[z1,z11,z2,z4,z717,z49])],[],[(0,[z1,z718,z2,z12,z4,z5]),(0,[z26,z719,z1,z2,z4,z5]),(0,[z1,z670,z2,z12,z19,z5]),(0,[z1,z720,z11,z2,z4,z5])],[(0,[z696,z1,z21,z11,z4,z5])],[(0,[z1,z11,z2,z721,z4,z49]),(0,[z1,z45,z2,z4,z120,z5])],[(0,[z26,z1,z2,z172,z4,z5]),(0,[z1,z2,z584,z12,z4,z5])],[(0,[z20,z1,z11,z523,z4,z5]),(0,[z1,z11,z12,z111,z722,z5]),(0,[z723,z1,z363,z2,z4,z5])],[(0,[z697,z1,z2,z108,z4,z5]),(0,[z79,z724,z11,z2,z4,z5]),(0,[z53,z132,z1,z2,z4,z5]),(0,[z725,z1,z11,z2,z4,z5]),(0,[z1,z186,z126,z2,z4,z5]),(0,[z726,z1,z11,z2,z4,z5]),(0,[z20,z122,z1,z11,z4,z5]),(0,[z1,z11,z2,z4,z502,z5]),(0,[z727,z53,z1,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z728])],[(0,[z1,z100,z27,z2,z4,z5]),(0,[z1,z11,z2,z236,z5,z49]),(0,[z0,z1,z2,z729,z4,z5])],[(0,[z79,z0,z1,z2,z4,z5])],[(0,[z1,z11,z2,z4,z5,z730]),(0,[z1,z117,z11,z12,z731,z5]),(0,[z732,z1,z11,z2,z4,z5]),(0,[z1,z134,z11,z2,z4,z522]),(0,[z1,z11,z2,z4,z733,z5])],[(0,[z1,z11,z2,z4,z734,z5]),(0,[z96,z1,z2,z4,z5,z135]),(0,[z1,z11,z2,z735,z4,z5]),(0,[z1,z11,z2,z4,z736,z5]),(0,[z1,z11,z737,z12,z4,z5]),(0,[z1,z2,z738,z12,z4,z5]),(0,[z1,z2,z4,z382,z502,z5])],[(0,[z739,z298,z11,z12,z4,z5]),(0,[z1,z292,z12,z4,z278,z5])],[(0,[z0,z298,z1,z2,z4,z5]),(0,[z740,z11,z2,z12,z4,z5]),(0,[z40,z1,z2,z4,z741,z101]),(0,[z1,z2,z4,z202,z295,z5])],[(1,[z83,z1,z11,z4,z5]),(0,[z20,z1,z11,z220,z4,z5]),(0,[z742,z100,z11,z2,z4,z5])],[(0,[z1,z11,z2,z743,z4,z5]),(0,[z20,z1,z11,z194,z4,z5]),(0,[z195,z1,z11,z2,z590,z5])],[(0,[z1,z11,z744,z12,z4,z5]),(0,[z1,z745,z2,z12,z4,z5]),(1,[z11,z2,z311,z4,z5]),(0,[z318,z14,z1,z2,z71,z5]),(0,[z20,z1,z11,z746,z4,z5]),(0,[z1,z287,z194,z12,z4,z5])],[(0,[z1,z11,z2,z747,z4,z5]),(0,[z39,z132,z1,z11,z4,z5]),(0,[z1,z100,z58,z2,z4,z5]),(0,[z318,z1,z10,z2,z71,z5]),(0,[z122,z1,z11,z4,z5,z77]),(0,[z1,z11,z2,z4,z5,z748]),(0,[z122,z1,z11,z338,z4,z5])],[(0,[z1,z11,z2,z46,z749,z5]),(0,[z0,z1,z2,z333,z4,z5]),(0,[z26,z750,z1,z2,z4,z5]),(0,[z26,z1,z11,z2,z562,z5]),(0,[z1,z11,z10,z751,z4,z5]),(1,[z752,z1,z11,z4,z5])],[(0,[z1,z186,z12,z4,z440,z5])],[(0,[z29,z30,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z753]),(0,[z193,z11,z2,z248,z4,z5]),(0,[z1,z11,z2,z12,z754,z5])],[(0,[z755,z1,z11,z2,z4,z5]),(0,[z14,z1,z2,z4,z631,z5])]],
   [[(0,[z350,z11,z2,z12,z84,z5]),(0,[z1,z292,z11,z4,z5,z49])],[(0,[z20,z1,z11,z494,z4,z5]),(0,[z1,z209,z11,z210,z4,z5]),(0,[z1,z126,z11,z271,z4,z5])],[(0,[z1,z205,z235,z12,z4,z5]),(0,[z1,z11,z2,z4,z756,z5]),(0,[z20,z1,z11,z2,z757,z5])],[(0,[z79,z758,z11,z2,z4,z5])],[(0,[z275,z11,z235,z12,z4,z60]),(0,[z1,z2,z12,z4,z5,z367]),(0,[z40,z26,z55,z2,z4,z5]),(0,[z318,z0,z1,z2,z4,z5]),(0,[z122,z1,z11,z4,z180,z5]),(0,[z20,z1,z11,z22,z4,z5])],[(0,[z318,z122,z1,z11,z4,z5]),(0,[z759,z1,z287,z2,z4,z5])],[(0,[z1,z11,z2,z4,z760,z5]),(0,[z1,z761,z2,z12,z4,z5]),(0,[z1,z2,z4,z180,z5,z135]),(0,[z26,z1,z2,z4,z5,z762])],[(0,[z1,z246,z2,z12,z4,z5]),(0,[z1,z11,z2,z12,z4,z763]),(0,[z159,z1,z11,z4,z49,z218]),(0,[z0,z1,z2,z338,z4,z5])],[(0,[z39,z1,z11,z137,z4,z5]),(0,[z1,z764,z137,z12,z4,z5])],[(0,[z1,z11,z2,z765,z4,z5]),(0,[z98,z1,z11,z2,z4,z5]),(0,[z24,z163,z1,z4,z5,z49]),(0,[z1,z11,z2,z169,z562,z5])],[(0,[z1,z11,z2,z766,z4,z5]),(0,[z298,z1,z63,z11,z4,z5]),(0,[z1,z767,z11,z2,z4,z5]),(0,[z26,z1,z11,z2,z236,z5]),(0,[z578,z20,z1,z11,z4,z5])],[(0,[z1,z11,z464,z339,z4,z5]),(0,[z1,z11,z2,z4,z5,z768]),(0,[z185,z1,z11,z12,z4,z5]),(0,[z1,z11,z2,z4,z769,z5]),(0,[z1,z254,z11,z10,z4,z5]),(0,[z1,z11,z2,z4,z770,z49]),(0,[z1,z11,z2,z4,z5,z771]),(0,[z1,z11,z118,z12,z4,z5])],[(0,[z1,z11,z772,z12,z4,z5]),(0,[z1,z11,z2,z4,z200,z773]),(0,[z123,z11,z2,z12,z4,z5]),(0,[z53,z74,z1,z2,z4,z5]),(0,[z304,z1,z11,z2,z692,z61])],[(0,[z774,z1,z11,z2,z4,z200]),(0,[z1,z11,z10,z4,z481,z5]),(0,[z53,z1,z43,z2,z4,z5]),(0,[z1,z11,z2,z433,z775,z5])],[(0,[z1,z776,z2,z12,z4,z5]),(0,[z1,z777,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z778])],[(0,[z779,z1,z11,z2,z4,z5]),(0,[z1,z58,z2,z12,z4,z189]),(0,[z1,z18,z2,z12,z397,z5]),(0,[z780,z1,z11,z2,z4,z5]),(0,[z781,z11,z2,z12,z4,z5]),(0,[z782,z1,z11,z12,z114,z5]),(0,[z1,z11,z2,z433,z5,z387])],[(0,[z783,z11,z2,z198,z4,z5]),(0,[z1,z206,z137,z12,z4,z5]),(0,[z1,z11,z2,z784,z4,z5]),(0,[z1,z134,z2,z12,z4,z180]),(0,[z1,z254,z11,z4,z741,z5]),(0,[z0,z1,z2,z4,z180,z5])],[(0,[z1,z11,z2,z785,z4,z5]),(0,[z26,z153,z11,z2,z4,z5]),(0,[z26,z1,z2,z786,z4,z5]),(0,[z695,z20,z1,z11,z4,z5]),(0,[z1,z206,z12,z4,z66,z5])],[(0,[z517,z1,z2,z4,z71,z5]),(0,[z24,z1,z2,z4,z5,z135]),(0,[z0,z1,z2,z221,z4,z5]),(0,[z1,z11,z2,z4,z787,z5]),(0,[z1,z705,z45,z2,z4,z5]),(0,[z1,z11,z2,z4,z788,z5])],[(0,[z1,z11,z2,z4,z189,z49]),(0,[z74,z11,z2,z12,z4,z789]),(0,[z39,z1,z11,z4,z71,z5]),(0,[z1,z117,z11,z187,z4,z5])],[(0,[z558,z20,z1,z11,z4,z5]),(0,[z1,z11,z108,z187,z4,z5]),(0,[z132,z11,z2,z4,z5,z355]),(0,[z1,z11,z539,z2,z4,z5]),(0,[z1,z357,z2,z12,z4,z5])],[(0,[z39,z1,z11,z108,z4,z5]),(0,[z790,z1,z2,z12,z4,z5])],[(0,[z39,z74,z1,z11,z4,z5]),(0,[z1,z11,z483,z2,z4,z5]),(0,[z1,z11,z2,z791,z4,z5])],[(0,[z122,z163,z1,z11,z4,z5]),(0,[z1,z11,z2,z12,z757,z5]),(0,[z1,z147,z54,z12,z4,z5]),(0,[z0,z1,z2,z4,z5,z130])],[(0,[z1,z11,z43,z2,z4,z5]),(0,[z42,z1,z10,z2,z4,z5]),(0,[z1,z117,z12,z111,z382,z5])],[(0,[z151,z163,z1,z11,z4,z5]),(0,[z1,z2,z514,z4,z71,z5])],[(0,[z24,z163,z1,z479,z4,z5]),(0,[z1,z11,z2,z4,z5,z792])],[(0,[z26,z793,z1,z2,z4,z5]),(0,[z794,z1,z11,z235,z4,z5]),(0,[z1,z117,z11,z10,z111,z5])],[(0,[z1,z205,z2,z12,z236,z5]),(0,[z1,z100,z2,z4,z795,z5]),(0,[z11,z2,z4,z5,z49,z796])],[(0,[z30,z2,z12,z4,z5,z797]),(0,[z1,z11,z2,z798,z4,z5]),(0,[z1,z100,z6,z2,z4,z5]),(0,[z1,z11,z4,z5,z49,z799])],[(0,[z1,z800,z11,z2,z4,z5]),(0,[z275,z11,z2,z12,z236,z60]),(0,[z53,z1,z2,z4,z5,z49])],[(0,[z801,z1,z11,z2,z4,z5]),(0,[z20,z802,z1,z11,z4,z5])]],
   [[(0,[z1,z11,z2,z4,z5,z803]),(0,[z53,z804,z1,z2,z4,z5])],[(0,[z805,z1,z11,z2,z4,z5]),(0,[z806,z1,z11,z2,z4,z5]),(0,[z1,z11,z12,z4,z5,z807])],[(0,[z163,z1,z11,z530,z4,z5]),(0,[z1,z11,z2,z4,z5,z808])],[(0,[z1,z11,z2,z183,z4,z5]),(0,[z153,z2,z221,z12,z4,z5]),(0,[z53,z1,z2,z19,z4,z5])],[],[(0,[z412,z335,z1,z11,z114,z5])],[(0,[z1,z809,z2,z12,z4,z5]),(0,[z20,z1,z45,z2,z4,z5])],[(0,[z810,z11,z2,z248,z4,z5]),(0,[z1,z811,z137,z12,z4,z5]),(0,[z1,z11,z10,z2,z555,z5])],[(0,[z1,z11,z2,z812,z4,z5]),(0,[z26,z55,z11,z2,z4,z5]),(0,[z813,z100,z11,z2,z4,z5]),(0,[z20,z1,z2,z147,z4,z5]),(0,[z1,z11,z17,z4,z5,z49])],[(0,[z1,z11,z2,z4,z5,z49]),(0,[z1,z11,z2,z12,z4,z814]),(0,[z195,z1,z11,z2,z815,z5]),(0,[z79,z39,z1,z11,z4,z5]),(0,[z11,z2,z12,z4,z5,z816]),(0,[z1,z11,z12,z481,z5,z61])],[(0,[z20,z1,z11,z4,z114,z5]),(0,[z20,z471,z11,z2,z4,z5]),(0,[z0,z1,z12,z4,z5,z130])],[(0,[z26,z74,z11,z2,z4,z75]),(0,[z1,z11,z4,z5,z130,z67])],[(0,[z252,z53,z1,z2,z4,z5]),(0,[z39,z1,z209,z11,z4,z5]),(1,[z129,z1,z11,z4,z5]),(0,[z1,z11,z2,z817,z4,z5]),(0,[z1,z351,z2,z12,z562,z5]),(0,[z123,z11,z194,z12,z4,z5])],[(0,[z82,z11,z2,z12,z59,z5]),(0,[z1,z818,z11,z2,z4,z5]),(0,[z26,z1,z2,z3,z4,z5]),(0,[z1,z11,z2,z819,z4,z5]),(0,[z1,z2,z4,z382,z5,z49])],[(0,[z1,z11,z464,z12,z4,z5]),(0,[z1,z134,z2,z12,z4,z820]),(0,[z1,z2,z183,z4,z71,z5]),(0,[z1,z11,z2,z4,z5,z821]),(0,[z159,z1,z11,z12,z84,z218])],[(0,[z1,z11,z822,z12,z4,z5]),(0,[z1,z11,z2,z823,z4,z5]),(0,[z82,z11,z2,z12,z59,z200]),(0,[z1,z186,z11,z12,z84,z5]),(0,[z1,z11,z2,z824,z4,z5]),(0,[z1,z11,z187,z4,z66,z5]),(1,[z85,z1,z2,z4,z5])],[(0,[z1,z11,z2,z825,z4,z5]),(0,[z802,z39,z1,z11,z4,z5])],[(0,[z1,z826,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z827,z5]),(0,[z1,z27,z2,z4,z5,z49]),(0,[z39,z1,z11,z4,z5,z60]),(0,[z195,z39,z1,z11,z4,z5])],[(0,[z828,z1,z206,z2,z4,z5])],[(0,[z0,z14,z1,z2,z4,z5])],[(0,[z829,z1,z11,z2,z4,z5]),(0,[z26,z1,z830,z2,z4,z5]),(0,[z1,z831,z11,z2,z4,z5]),(0,[z42,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z46,z832,z5])],[(0,[z1,z11,z2,z405,z4,z5]),(0,[z422,z298,z11,z405,z4,z5]),(0,[z40,z1,z2,z12,z4,z380]),(0,[z14,z1,z11,z2,z4,z135]),(0,[z1,z2,z12,z253,z71,z5])],[(0,[z78,z11,z2,z4,z5,z49])],[(0,[z1,z602,z11,z2,z4,z5]),(0,[z1,z186,z833,z12,z4,z5]),(0,[z20,z1,z11,z4,z834,z5]),(0,[z835,z1,z11,z2,z4,z5]),(0,[z1,z81,z2,z4,z5,z49]),(0,[z1,z11,z2,z12,z338,z268])],[(0,[z26,z29,z30,z2,z4,z5]),(0,[z697,z1,z2,z12,z4,z5]),(0,[z1,z11,z836,z2,z4,z5]),(0,[z837,z1,z11,z2,z4,z5]),(0,[z20,z1,z11,z2,z307,z5]),(0,[z838,z1,z11,z2,z4,z5])],[(0,[z125,z1,z30,z2,z4,z5]),(0,[z422,z150,z11,z12,z4,z5]),(0,[z839,z1,z11,z2,z120,z5]),(0,[z304,z1,z11,z194,z12,z61])],[(0,[z1,z262,z11,z840,z4,z5]),(0,[z20,z1,z2,z4,z5,z367]),(0,[z1,z592,z10,z2,z4,z5]),(0,[z1,z11,z2,z841,z4,z5])],[(0,[z1,z842,z2,z12,z4,z5]),(0,[z843,z11,z2,z12,z4,z5])],[(1,[z697,z1,z2,z4,z5])],[(0,[z25,z11,z2,z12,z4,z5]),(0,[z844,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z12,z268,z61])],[(0,[z1,z11,z2,z845,z4,z5]),(0,[z846,z1,z11,z257,z4,z5]),(0,[z1,z11,z2,z12,z847,z5]),(0,[z20,z1,z11,z4,z5,z848]),(0,[z0,z14,z1,z2,z4,z49])],[(0,[z1,z2,z137,z183,z4,z5]),(0,[z14,z1,z2,z147,z4,z5])]],
   [[(0,[z275,z11,z2,z4,z49,z60]),(0,[z578,z1,z186,z12,z4,z5]),(0,[z1,z11,z2,z12,z849,z5]),(0,[z1,z100,z2,z241,z4,z5]),(0,[z1,z100,z2,z4,z5,z48]),(0,[z1,z11,z2,z4,z5,z850]),(0,[z1,z851,z2,z12,z4,z5])],[(0,[z1,z11,z852,z196,z4,z5]),(0,[z412,z1,z11,z108,z4,z5]),(0,[z1,z853,z11,z2,z4,z5]),(0,[z1,z2,z4,z5,z663,z86])],[(0,[z40,z1,z2,z12,z167,z101])],[(0,[z1,z854,z2,z12,z4,z5]),(0,[z1,z644,z357,z2,z4,z5])],[(0,[z1,z11,z2,z12,z338,z855])],[(0,[z1,z11,z10,z2,z614,z5])],[(0,[z1,z2,z12,z4,z856,z5]),(0,[z82,z53,z1,z2,z4,z5]),(0,[z199,z100,z11,z2,z333,z5]),(0,[z24,z163,z1,z100,z4,z5]),(0,[z857,z496,z11,z2,z4,z5])],[(0,[z1,z11,z10,z229,z4,z5])],[(0,[z39,z1,z11,z523,z4,z5]),(0,[z53,z1,z2,z4,z5,z858]),(0,[z1,z127,z2,z4,z5,z49])],[(0,[z1,z11,z2,z12,z859,z5]),(0,[z26,z1,z860,z2,z4,z5]),(0,[z1,z209,z11,z2,z4,z522])],[(0,[z861,z30,z2,z12,z4,z5]),(0,[z122,z1,z11,z4,z75,z5]),(0,[z1,z11,z2,z12,z4,z41])],[(0,[z862,z1,z11,z12,z4,z5]),(0,[z1,z100,z11,z634,z4,z5]),(0,[z863,z1,z11,z2,z4,z5]),(0,[z0,z1,z2,z46,z4,z5])],[(0,[z1,z11,z2,z12,z864,z5]),(0,[z1,z11,z137,z4,z5,z77]),(0,[z865,z39,z1,z11,z4,z5]),(0,[z1,z100,z2,z4,z278,z5]),(0,[z159,z20,z1,z11,z4,z218])],[(0,[z1,z11,z2,z866,z4,z5]),(0,[z20,z1,z11,z2,z4,z200]),(0,[z1,z11,z12,z4,z481,z5]),(0,[z1,z11,z2,z12,z307,z5]),(0,[z867,z1,z63,z2,z4,z5]),(0,[z411,z11,z2,z12,z4,z5])],[(0,[z868,z1,z11,z2,z4,z5]),(0,[z40,z1,z154,z12,z4,z101]),(1,[z20,z1,z11,z84,z5]),(0,[z20,z1,z11,z869,z4,z5]),(0,[z53,z335,z1,z2,z4,z5])],[(0,[z14,z1,z11,z2,z307,z5]),(0,[z159,z136,z1,z11,z4,z5])],[(0,[z1,z100,z11,z870,z4,z5]),(0,[z1,z871,z11,z2,z872,z5])],[(0,[z422,z39,z1,z11,z4,z5]),(1,[z11,z2,z12,z173,z5]),(0,[z1,z186,z100,z137,z4,z5]),(0,[z39,z1,z11,z4,z873,z5]),(0,[z1,z874,z2,z12,z4,z5]),(0,[z14,z1,z2,z4,z5,z367])],[(0,[z26,z1,z875,z2,z4,z5]),(0,[z26,z422,z298,z11,z4,z5]),(0,[z1,z11,z2,z4,z876,z5]),(0,[z1,z100,z106,z2,z4,z5]),(0,[z1,z292,z11,z46,z433,z5])],[(0,[z39,z1,z11,z248,z4,z5]),(0,[z26,z1,z11,z2,z84,z5]),(0,[z1,z11,z2,z4,z5,z858])],[(0,[z1,z877,z2,z12,z4,z5]),(0,[z1,z878,z2,z12,z4,z5]),(0,[z350,z100,z11,z2,z4,z5]),(0,[z879,z1,z11,z2,z426,z5]),(0,[z1,z11,z2,z880,z4,z5]),(0,[z1,z11,z4,z5,z660,z86])],[(0,[z667,z11,z2,z198,z4,z5]),(0,[z122,z1,z11,z4,z5,z648])],[(0,[z26,z1,z2,z4,z881,z5]),(0,[z26,z1,z11,z210,z4,z5]),(0,[z159,z1,z11,z10,z4,z218]),(0,[z1,z882,z2,z12,z4,z5])],[(0,[z24,z1,z220,z12,z4,z5]),(0,[z883,z1,z11,z2,z4,z5]),(0,[z1,z363,z2,z692,z4,z5]),(0,[z304,z1,z363,z2,z12,z61])],[(0,[z26,z96,z1,z2,z4,z5]),(0,[z1,z11,z12,z4,z884,z5])],[(0,[z1,z2,z187,z4,z5,z367])],[(0,[z1,z11,z885,z12,z4,z5]),(0,[z1,z11,z2,z642,z236,z5]),(0,[z1,z886,z363,z2,z4,z5]),(0,[z1,z11,z2,z12,z4,z268])],[(0,[z542,z163,z1,z12,z4,z5]),(0,[z26,z1,z833,z2,z4,z5]),(0,[z1,z100,z11,z2,z167,z5]),(0,[z1,z871,z292,z11,z4,z5]),(0,[z1,z209,z2,z4,z5,z48]),(0,[z1,z887,z11,z12,z4,z5])],[(0,[z1,z888,z11,z12,z4,z5]),(0,[z39,z1,z11,z12,z4,z5]),(0,[z0,z1,z2,z4,z5,z135]),(0,[z889,z1,z11,z2,z4,z5]),(0,[z890,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z891,z4,z5]),(0,[z219,z1,z11,z2,z4,z5]),(0,[z1,z11,z54,z4,z202,z5])],[(0,[z1,z186,z146,z137,z4,z5]),(0,[z892,z1,z11,z12,z4,z5])],[(0,[z1,z11,z2,z12,z893,z5]),(0,[z1,z11,z2,z894,z4,z5]),(0,[z1,z11,z12,z4,z5,z895]),(0,[z199,z11,z10,z2,z333,z5]),(0,[z1,z896,z11,z2,z4,z5])]],
   [[(0,[z422,z298,z11,z12,z4,z5]),(0,[z1,z11,z2,z897,z4,z5]),(0,[z275,z20,z11,z2,z4,z60]),(0,[z40,z1,z2,z3,z4,z101]),(0,[z1,z11,z2,z169,z84,z5]),(0,[z1,z206,z2,z4,z5,z49])],[(0,[z898,z1,z2,z12,z4,z5]),(0,[z1,z11,z899,z2,z4,z5]),(0,[z1,z11,z540,z2,z4,z5]),(0,[z1,z134,z2,z12,z4,z41]),(0,[z1,z11,z2,z12,z338,z900]),(0,[z1,z11,z2,z4,z5,z901])],[(0,[z1,z11,z229,z12,z4,z5]),(0,[z1,z11,z2,z12,z4,z200]),(0,[z0,z1,z2,z392,z4,z5]),(0,[z1,z117,z106,z12,z111,z5])],[(0,[z39,z1,z232,z11,z4,z5]),(0,[z1,z11,z902,z12,z4,z5]),(0,[z1,z11,z183,z4,z5,z450]),(0,[z20,z1,z11,z357,z4,z5])],[(0,[z14,z1,z11,z2,z4,z200]),(0,[z1,z134,z2,z12,z307,z5]),(0,[z1,z11,z2,z338,z37,z86])],[(0,[z903,z11,z108,z12,z4,z5]),(1,[z1,z11,z2,z832,z5])],[(0,[z40,z1,z12,z4,z450,z101])],[(0,[z1,z11,z2,z4,z5,z904]),(0,[z1,z100,z351,z2,z4,z5]),(0,[z1,z11,z12,z4,z5,z905]),(0,[z1,z11,z906,z12,z4,z5]),(0,[z907,z1,z11,z2,z4,z5])],[(0,[z1,z11,z12,z4,z5,z908]),(0,[z909,z1,z11,z2,z4,z5]),(0,[z910,z39,z1,z11,z4,z5]),(0,[z1,z292,z100,z11,z4,z5])],[(0,[z1,z11,z2,z911,z4,z5]),(0,[z912,z39,z1,z11,z4,z5]),(0,[z122,z1,z11,z10,z4,z5])],[(0,[z1,z11,z913,z12,z4,z5]),(0,[z96,z496,z2,z12,z4,z5]),(0,[z1,z11,z141,z12,z307,z5]),(0,[z1,z11,z2,z187,z4,z5]),(0,[z1,z351,z10,z2,z4,z5]),(0,[z1,z2,z4,z5,z49,z914]),(0,[z1,z915,z287,z2,z4,z5])],[(0,[z1,z916,z58,z2,z4,z5]),(0,[z1,z100,z11,z188,z4,z5]),(0,[z1,z11,z38,z4,z5,z49]),(0,[z1,z11,z2,z4,z917,z5]),(0,[z1,z357,z12,z4,z5,z218])],[],[(0,[z40,z26,z1,z2,z167,z5])],[(0,[z20,z1,z11,z918,z4,z5]),(0,[z0,z122,z1,z12,z4,z5]),(0,[z1,z11,z919,z194,z4,z5])],[],[(0,[z1,z11,z2,z642,z4,z5]),(0,[z39,z1,z11,z54,z4,z5]),(0,[z20,z1,z11,z4,z920,z5]),(0,[z0,z1,z117,z2,z4,z5])],[(0,[z1,z254,z137,z12,z4,z5]),(0,[z159,z1,z11,z2,z4,z77]),(0,[z14,z1,z11,z2,z4,z921]),(0,[z216,z11,z2,z4,z5,z49])],[(0,[z1,z922,z2,z12,z4,z5]),(0,[z53,z1,z220,z2,z4,z5]),(0,[z20,z1,z11,z114,z5,z61]),(0,[z1,z2,z12,z4,z923,z5]),(0,[z682,z11,z10,z2,z4,z5]),(0,[z1,z10,z2,z242,z4,z5])],[(0,[z0,z486,z1,z2,z4,z5]),(0,[z132,z11,z2,z4,z924,z5]),(0,[z521,z26,z1,z2,z4,z5]),(0,[z1,z685,z10,z2,z4,z5]),(0,[z1,z11,z2,z84,z5,z49])],[(0,[z122,z298,z1,z11,z4,z5]),(0,[z26,z1,z925,z2,z4,z5]),(0,[z26,z1,z926,z2,z4,z5]),(0,[z557,z232,z11,z2,z4,z5]),(0,[z53,z1,z134,z2,z4,z5])],[(0,[z9,z224,z1,z12,z4,z5]),(0,[z1,z11,z257,z4,z5,z49]),(0,[z1,z11,z2,z307,z5,z49]),(0,[z1,z927,z2,z12,z4,z5]),(0,[z1,z292,z11,z4,z120,z5])],[(0,[z151,z298,z1,z11,z4,z5]),(0,[z1,z559,z11,z2,z4,z5]),(0,[z1,z100,z2,z4,z382,z5]),(0,[z55,z11,z2,z12,z167,z5]),(0,[z42,z1,z65,z2,z4,z5]),(0,[z125,z0,z1,z2,z4,z5]),(0,[z928,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z12,z4,z929])],[(0,[z1,z30,z2,z4,z5,z135]),(0,[z26,z96,z758,z2,z4,z5]),(0,[z1,z27,z2,z642,z4,z5])],[(0,[z53,z1,z30,z2,z4,z5]),(0,[z1,z818,z205,z2,z4,z5])],[(0,[z159,z26,z1,z11,z4,z218]),(0,[z1,z287,z10,z2,z4,z5])],[(0,[z1,z2,z4,z178,z930,z5]),(0,[z159,z20,z1,z11,z4,z77]),(0,[z1,z11,z2,z46,z433,z5])],[(0,[z1,z931,z11,z2,z4,z5]),(0,[z1,z11,z271,z12,z4,z5])],[(0,[z1,z932,z2,z12,z4,z5]),(0,[z213,z298,z11,z12,z4,z5]),(0,[z20,z1,z11,z257,z4,z5]),(0,[z1,z11,z220,z2,z4,z5]),(0,[z1,z11,z141,z12,z4,z5]),(0,[z1,z933,z11,z12,z4,z5]),(0,[z136,z1,z117,z11,z4,z5]),(0,[z20,z1,z11,z320,z4,z5])],[(0,[z1,z205,z257,z12,z4,z5]),(0,[z39,z1,z134,z11,z4,z5]),(0,[z122,z1,z11,z4,z5,z61])],[]],
   [[(0,[z1,z11,z2,z934,z4,z5]),(0,[z20,z128,z1,z11,z4,z5]),(0,[z1,z357,z54,z12,z4,z5]),(0,[z1,z11,z194,z12,z4,z5])],[(0,[z153,z11,z2,z12,z4,z5]),(0,[z26,z1,z2,z4,z935,z5]),(0,[z39,z1,z11,z30,z4,z5]),(0,[z39,z1,z11,z111,z4,z5]),(0,[z936,z1,z11,z2,z4,z5]),(0,[z20,z1,z10,z147,z4,z5])],[(0,[z1,z100,z263,z2,z4,z5]),(0,[z39,z1,z11,z4,z114,z5]),(0,[z55,z11,z154,z12,z4,z5]),(0,[z20,z1,z937,z2,z4,z5]),(0,[z122,z1,z11,z4,z938,z5])],[(0,[z1,z939,z2,z12,z4,z5]),(0,[z1,z11,z188,z264,z4,z5]),(0,[z1,z100,z11,z65,z4,z66]),(0,[z1,z100,z2,z940,z4,z5])],[(0,[z1,z11,z10,z188,z4,z5]),(0,[z1,z11,z2,z4,z5,z773]),(0,[z26,z24,z1,z2,z4,z5])],[(0,[z53,z199,z1,z2,z4,z5]),(0,[z1,z11,z941,z12,z4,z5])],[(0,[z1,z11,z2,z12,z470,z5]),(0,[z163,z1,z2,z12,z307,z5])],[(0,[z1,z100,z11,z235,z4,z5]),(0,[z20,z1,z11,z4,z5,z130]),(0,[z409,z1,z11,z12,z4,z218])],[(0,[z0,z96,z1,z2,z4,z5]),(1,[z1,z11,z12,z4,z443])],[(0,[z132,z1,z292,z11,z4,z5]),(0,[z1,z942,z11,z2,z4,z5]),(0,[z1,z11,z65,z4,z66,z49])],[(0,[z20,z1,z357,z12,z4,z5])],[(0,[z1,z186,z943,z12,z4,z5]),(0,[z329,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z944,z4,z5])],[],[(0,[z275,z26,z11,z2,z4,z60]),(0,[z1,z11,z945,z2,z4,z5]),(0,[z1,z2,z12,z4,z41,z101]),(0,[z1,z2,z147,z4,z5,z334])],[(0,[z151,z96,z1,z2,z4,z5]),(0,[z39,z199,z1,z11,z4,z5]),(0,[z1,z11,z2,z946,z4,z5])],[],[(0,[z422,z298,z100,z11,z4,z5]),(0,[z53,z1,z2,z459,z4,z5]),(0,[z947,z1,z11,z2,z4,z5]),(0,[z14,z1,z2,z4,z48,z49])],[(0,[z1,z11,z2,z948,z4,z5]),(0,[z1,z11,z2,z4,z5,z949]),(0,[z950,z1,z11,z2,z4,z5]),(0,[z0,z1,z65,z2,z4,z5])],[(0,[z1,z2,z12,z4,z180,z951]),(0,[z40,z1,z254,z12,z4,z101]),(0,[z20,z1,z11,z4,z5,z450]),(0,[z53,z1,z2,z4,z120,z5])],[(0,[z691,z486,z11,z108,z4,z5]),(0,[z14,z1,z11,z257,z4,z5]),(0,[z1,z11,z952,z2,z4,z5]),(0,[z55,z11,z2,z3,z4,z5]),(0,[z1,z134,z141,z12,z4,z5]),(0,[z25,z11,z12,z4,z5,z218])],[(0,[z1,z953,z11,z2,z4,z5]),(0,[z1,z263,z2,z4,z5,z49]),(0,[z1,z11,z2,z4,z954,z5]),(0,[z955,z11,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z144,z522]),(0,[z20,z1,z11,z4,z956,z5]),(0,[z1,z117,z11,z138,z111,z5])],[(0,[z1,z11,z2,z957,z4,z5])],[(0,[z1,z11,z2,z46,z397,z5])],[(0,[z958,z1,z11,z2,z4,z5]),(0,[z699,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z959]),(0,[z1,z100,z11,z531,z4,z5]),(0,[z159,z0,z1,z2,z4,z5])],[(0,[z82,z263,z2,z12,z59,z5]),(0,[z159,z122,z1,z11,z4,z5]),(0,[z1,z11,z2,z4,z5,z960])],[(0,[z1,z11,z961,z2,z4,z5]),(0,[z1,z259,z2,z4,z5,z49]),(0,[z1,z209,z11,z2,z4,z299]),(0,[z39,z1,z11,z4,z120,z5]),(0,[z1,z962,z11,z12,z4,z5]),(0,[z136,z1,z11,z2,z4,z77]),(0,[z20,z1,z117,z11,z111,z5])],[(0,[z1,z100,z11,z464,z4,z5]),(0,[z150,z486,z11,z12,z4,z5]),(0,[z963,z11,z2,z12,z4,z5]),(0,[z1,z11,z4,z481,z736,z5])],[(0,[z1,z11,z2,z4,z5,z522])],[(0,[z20,z1,z11,z147,z4,z5]),(0,[z159,z20,z1,z357,z4,z5]),(0,[z1,z11,z12,z114,z5,z964]),(0,[z159,z14,z1,z11,z4,z218])],[(0,[z29,z30,z10,z2,z4,z5]),(0,[z699,z1,z2,z4,z75,z5]),(0,[z195,z1,z11,z2,z463,z5]),(0,[z1,z117,z63,z11,z4,z5]),(0,[z965,z1,z11,z2,z5,z49]),(0,[z14,z1,z11,z4,z5,z130])],[(0,[z335,z39,z1,z11,z4,z5])]],
   [[(0,[z966,z30,z2,z12,z4,z5]),(0,[z39,z1,z11,z4,z5,z218])],[(0,[z252,z14,z96,z2,z4,z5]),(0,[z967,z1,z11,z2,z4,z5]),(0,[z1,z11,z188,z12,z4,z5]),(0,[z1,z11,z38,z894,z4,z5]),(1,[z1,z2,z241,z4,z5]),(0,[z1,z11,z2,z4,z5,z968]),(0,[z1,z2,z12,z4,z969,z5])],[(0,[z1,z11,z2,z12,z505,z5]),(0,[z484,z1,z246,z2,z4,z5]),(0,[z0,z1,z2,z198,z4,z5]),(0,[z163,z1,z12,z4,z5,z181])],[(0,[z1,z11,z2,z970,z4,z5]),(0,[z20,z1,z11,z971,z4,z5]),(0,[z1,z11,z2,z4,z5,z972]),(0,[z20,z1,z11,z4,z973,z5])],[(0,[z125,z1,z11,z2,z4,z135]),(0,[z26,z1,z974,z2,z4,z5]),(0,[z1,z2,z233,z4,z71,z5]),(0,[z1,z21,z11,z4,z736,z5]),(0,[z335,z1,z11,z12,z114,z5])],[(0,[z82,z11,z2,z12,z59,z189]),(0,[z163,z1,z63,z2,z4,z5]),(0,[z1,z18,z2,z233,z4,z5])],[(0,[z975,z11,z2,z12,z4,z5]),(0,[z1,z11,z976,z12,z4,z5])],[(0,[z1,z977,z2,z12,z4,z5]),(0,[z1,z246,z10,z2,z4,z5]),(0,[z1,z978,z2,z12,z4,z5]),(0,[z1,z11,z2,z459,z4,z49]),(1,[z1,z11,z2,z4,z528])],[(0,[z1,z11,z468,z12,z4,z5])],[(0,[z1,z979,z11,z12,z4,z5]),(0,[z25,z11,z54,z12,z4,z5])],[(0,[z224,z1,z11,z198,z4,z5]),(0,[z163,z39,z1,z11,z4,z5]),(0,[z39,z1,z11,z4,z299,z5]),(0,[z723,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z980,z4,z5]),(0,[z981,z1,z11,z2,z4,z189]),(0,[z1,z11,z982,z12,z4,z5])],[(0,[z1,z11,z2,z4,z5,z983]),(0,[z1,z11,z2,z984,z4,z5]),(0,[z1,z18,z220,z2,z4,z5]),(0,[z1,z11,z985,z12,z4,z5]),(0,[z1,z11,z2,z4,z986,z5]),(0,[z123,z11,z10,z2,z4,z5]),(0,[z122,z1,z11,z4,z66,z5])],[(0,[z96,z1,z2,z183,z4,z5]),(0,[z20,z1,z11,z2,z562,z5]),(0,[z1,z11,z2,z4,z144,z528])],[(0,[z432,z1,z11,z464,z4,z5]),(0,[z1,z11,z2,z987,z4,z5]),(0,[z1,z988,z2,z12,z4,z5]),(0,[z151,z1,z11,z4,z66,z5]),(0,[z26,z1,z137,z54,z4,z5]),(0,[z1,z11,z10,z194,z4,z5])],[(0,[z96,z1,z254,z12,z4,z5]),(0,[z224,z1,z259,z12,z4,z5]),(0,[z20,z1,z11,z4,z989,z5]),(0,[z1,z915,z11,z2,z4,z5]),(0,[z1,z11,z990,z12,z4,z5])],[(0,[z26,z1,z2,z241,z4,z5]),(0,[z26,z1,z2,z4,z5,z48]),(0,[z1,z134,z10,z2,z4,z180]),(0,[z304,z20,z1,z11,z2,z61]),(0,[z122,z14,z1,z11,z4,z5]),(0,[z14,z1,z851,z2,z4,z5]),(0,[z1,z11,z2,z4,z991,z5])],[(0,[z1,z11,z992,z2,z4,z5]),(0,[z219,z1,z2,z4,z178,z5]),(0,[z26,z123,z11,z2,z4,z5]),(0,[z14,z1,z117,z11,z111,z5])],[(0,[z159,z1,z351,z12,z4,z218])],[(0,[z1,z11,z2,z993,z4,z5]),(0,[z1,z100,z363,z2,z4,z5]),(0,[z20,z1,z11,z994,z4,z5])],[(0,[z1,z11,z10,z464,z4,z5]),(0,[z1,z11,z2,z995,z4,z5]),(0,[z699,z1,z2,z4,z5,z365]),(0,[z0,z24,z1,z2,z4,z5]),(0,[z1,z357,z10,z2,z4,z5]),(0,[z0,z1,z4,z5,z130,z49])],[(0,[z996,z11,z2,z12,z4,z5]),(0,[z20,z1,z11,z607,z4,z5])],[(0,[z1,z11,z235,z12,z4,z5]),(0,[z1,z11,z145,z257,z4,z5]),(0,[z1,z11,z2,z4,z997,z5]),(0,[z163,z1,z141,z12,z4,z5]),(0,[z159,z1,z11,z187,z4,z5])],[(0,[z1,z11,z4,z5,z294,z135]),(0,[z20,z1,z11,z4,z775,z5]),(0,[z1,z11,z2,z998,z4,z5])],[(0,[z1,z11,z2,z12,z4,z999]),(0,[z96,z1,z464,z12,z4,z5]),(0,[z1,z11,z2,z4,z1000,z5]),(0,[z14,z1,z11,z2,z4,z1001]),(0,[z136,z1,z11,z65,z4,z66]),(0,[z1002,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z1003,z4,z5]),(0,[z199,z11,z2,z12,z173,z5]),(0,[z1,z11,z10,z22,z4,z5])],[(0,[z122,z1,z4,z5,z48,z49])],[(0,[z1,z11,z2,z1004,z4,z5]),(0,[z1005,z11,z108,z12,z4,z5]),(0,[z275,z100,z11,z2,z4,z60]),(0,[z151,z24,z1,z2,z4,z5]),(0,[z122,z14,z1,z11,z4,z49])],[(0,[z1006,z1,z27,z2,z4,z5]),(0,[z1,z11,z257,z642,z4,z5]),(0,[z26,z1,z2,z4,z278,z5]),(0,[z20,z1,z11,z4,z84,z5])],[(0,[z1,z186,z137,z12,z4,z5])],[(0,[z1,z11,z1007,z12,z4,z5]),(0,[z298,z1,z246,z12,z4,z5]),(0,[z26,z1,z2,z4,z1008,z5]),(0,[z1,z2,z221,z591,z4,z5])],[(0,[z20,z1,z11,z1009,z4,z5]),(0,[z26,z1,z1010,z2,z4,z5]),(0,[z1,z210,z221,z12,z4,z5])]],
   [[(0,[z20,z1011,z1,z11,z4,z5]),(0,[z125,z1,z18,z2,z4,z5]),(0,[z39,z1,z11,z119,z4,z5]),(0,[z153,z2,z12,z4,z5,z101]),(0,[z1,z11,z1012,z12,z4,z5])],[(0,[z1,z11,z4,z956,z114,z5]),(0,[z53,z1013,z1,z2,z4,z5])],[(0,[z97,z11,z2,z12,z4,z5]),(0,[z1,z1014,z11,z2,z4,z5]),(0,[z26,z1,z106,z2,z4,z5]),(0,[z1,z100,z45,z2,z4,z5]),(0,[z20,z153,z11,z2,z4,z5]),(0,[z1,z43,z2,z147,z4,z5]),(0,[z1,z11,z10,z4,z1015,z5]),(0,[z1,z11,z2,z12,z562,z5]),(0,[z136,z122,z1,z11,z4,z5])],[(0,[z1,z11,z2,z12,z1016,z5]),(0,[z1,z175,z11,z2,z4,z5])],[(0,[z14,z1,z11,z2,z562,z5]),(0,[z122,z1,z11,z433,z4,z5]),(0,[z752,z1,z11,z4,z37,z5])],[(0,[z1,z100,z11,z2,z847,z5]),(0,[z1,z1017,z11,z2,z4,z5]),(0,[z1,z712,z2,z12,z4,z5]),(0,[z1,z287,z2,z692,z4,z5])],[(0,[z965,z1,z11,z2,z12,z5]),(0,[z199,z11,z2,z333,z5,z49]),(0,[z26,z1,z18,z2,z397,z5]),(0,[z20,z1,z11,z4,z1018,z5])],[],[(0,[z1,z11,z2,z435,z4,z5]),(0,[z1,z2,z147,z4,z5,z49])],[(0,[z1,z11,z2,z1019,z4,z5]),(0,[z1020,z758,z11,z2,z4,z5]),(0,[z26,z1,z100,z2,z4,z5]),(0,[z1021,z1,z11,z2,z4,z5])],[(0,[z24,z1,z2,z183,z4,z5]),(0,[z1,z11,z447,z4,z5,z49]),(0,[z477,z1,z11,z12,z4,z5])],[(0,[z79,z53,z1,z2,z4,z5]),(0,[z1,z263,z2,z894,z4,z5]),(0,[z55,z11,z2,z4,z5,z49])],[(0,[z298,z1,z11,z530,z4,z5]),(0,[z1,z11,z664,z2,z4,z5]),(0,[z40,z26,z1,z2,z4,z135]),(0,[z304,z1,z287,z2,z12,z61])],[(0,[z26,z1,z2,z137,z4,z5]),(0,[z1,z11,z10,z54,z4,z5])],[(0,[z1,z11,z2,z1022,z4,z5]),(0,[z1,z263,z2,z12,z4,z200]),(1,[z42,z1,z2,z4,z5])],[(0,[z1,z11,z2,z1023,z4,z5]),(0,[z26,z1024,z11,z2,z4,z5]),(0,[z39,z1,z11,z338,z4,z5]),(0,[z1,z11,z4,z481,z5,z49]),(0,[z412,z1,z11,z2,z4,z5]),(0,[z1025,z1,z11,z2,z4,z5])],[(0,[z20,z1,z134,z137,z4,z5]),(0,[z1,z11,z2,z4,z1026,z5])],[(0,[z1,z1027,z2,z12,z4,z5]),(0,[z20,z1,z1028,z11,z4,z5]),(0,[z1,z11,z1029,z2,z4,z5])],[],[(0,[z1,z11,z65,z12,z4,z629]),(0,[z1,z259,z229,z12,z4,z5]),(0,[z195,z53,z1,z2,z4,z5])],[(0,[z568,z1,z262,z11,z4,z5]),(0,[z1,z100,z11,z38,z4,z5]),(0,[z1,z126,z134,z2,z4,z5]),(0,[z1,z11,z2,z4,z661,z5])],[(0,[z1030,z224,z1,z11,z4,z5]),(0,[z1,z2,z4,z180,z5,z1031]),(0,[z1,z11,z4,z66,z5,z1032]),(0,[z1,z1033,z2,z12,z4,z5])],[(0,[z1,z209,z11,z17,z4,z5]),(0,[z1034,z1,z11,z2,z4,z5]),(0,[z1035,z53,z1,z2,z4,z5])],[(0,[z1,z11,z2,z1036,z4,z5]),(0,[z0,z1,z186,z2,z4,z5]),(0,[z26,z1,z351,z2,z4,z5]),(0,[z1,z11,z1037,z12,z4,z5])],[(0,[z1,z27,z2,z12,z236,z5]),(0,[z26,z1,z2,z4,z71,z5]),(0,[z39,z1,z11,z4,z180,z5]),(0,[z1,z21,z11,z4,z5,z49]),(0,[z1,z11,z1038,z2,z4,z5])],[(0,[z1,z1039,z11,z12,z4,z5]),(0,[z1,z1017,z21,z11,z4,z5]),(0,[z1,z11,z12,z4,z1040,z5]),(0,[z14,z153,z11,z2,z4,z5]),(0,[z159,z350,z11,z12,z4,z218])],[(0,[z26,z224,z1,z11,z4,z5]),(0,[z14,z1,z11,z2,z4,z189]),(0,[z1,z11,z2,z4,z5,z1041]),(0,[z39,z1,z11,z221,z4,z5]),(0,[z0,z1,z2,z4,z5,z101]),(0,[z20,z1,z25,z11,z4,z5])],[(0,[z1042,z1,z11,z2,z4,z5])],[(0,[z20,z74,z11,z2,z4,z75]),(0,[z1043,z1,z11,z2,z4,z135]),(0,[z318,z53,z1,z2,z4,z5]),(0,[z1,z11,z65,z2,z4,z77])],[(0,[z496,z11,z2,z198,z4,z5]),(0,[z25,z11,z10,z2,z4,z5])],[(0,[z401,z1,z186,z12,z4,z5]),(0,[z1,z2,z514,z4,z180,z5]),(0,[z40,z0,z1,z2,z4,z5]),(0,[z304,z26,z1,z11,z2,z61])],[(0,[z1,z11,z2,z1044,z4,z5]),(0,[z20,z1,z11,z4,z5,z1032]),(0,[z122,z1,z11,z4,z5,z34])]],
   [[(0,[z1,z11,z2,z1045,z4,z5]),(0,[z1,z2,z12,z4,z5,z1046]),(0,[z0,z1,z2,z4,z5,z48])],[(0,[z1047,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z1048,z4,z5]),(0,[z1,z11,z2,z1049,z4,z5])],[(0,[z1,z100,z11,z641,z4,z5]),(0,[z1,z11,z2,z872,z120,z5]),(0,[z1,z11,z2,z1050,z4,z5])],[(0,[z1,z11,z12,z4,z5,z799]),(0,[z1,z2,z12,z1051,z71,z5]),(0,[z1052,z0,z1,z2,z4,z5])],[],[(0,[z1,z2,z12,z4,z1053,z5]),(0,[z122,z1,z2,z4,z5,z48])],[(0,[z132,z11,z2,z208,z4,z5]),(0,[z0,z1054,z1,z2,z4,z5])],[(0,[z1,z205,z2,z626,z4,z5])],[(0,[z1055,z1,z11,z38,z4,z5])],[(0,[z26,z1,z1056,z2,z4,z5]),(0,[z275,z11,z2,z626,z4,z60]),(0,[z526,z1,z11,z2,z4,z5])],[(0,[z26,z1,z11,z4,z481,z5]),(0,[z1,z21,z12,z4,z71,z5]),(0,[z575,z1,z11,z65,z4,z66])],[(0,[z1,z201,z11,z12,z4,z5]),(0,[z1,z11,z2,z142,z4,z5]),(0,[z437,z1,z11,z12,z4,z5]),(0,[z20,z1,z11,z1057,z4,z5]),(0,[z1,z11,z2,z4,z528,z5])],[(0,[z1,z11,z2,z4,z5,z1058]),(0,[z132,z232,z11,z2,z4,z5]),(0,[z1,z63,z134,z2,z4,z5])],[(0,[z0,z132,z1,z2,z4,z5]),(0,[z1,z1059,z11,z2,z4,z5]),(1,[z0,z1,z2,z4,z5]),(0,[z865,z1,z11,z2,z873,z5]),(0,[z1,z11,z10,z2,z307,z5]),(0,[z1060,z1,z11,z2,z4,z77]),(0,[z1,z11,z12,z4,z66,z1061]),(0,[z122,z1,z117,z11,z4,z5])],[(0,[z11,z2,z12,z4,z173,z5]),(0,[z1062,z20,z1,z11,z4,z5])],[(0,[z151,z1,z117,z11,z4,z5]),(0,[z1,z2,z146,z221,z4,z5]),(0,[z1,z11,z2,z1063,z4,z5])],[(0,[z20,z298,z1,z11,z4,z5]),(0,[z122,z486,z1,z11,z4,z5]),(0,[z26,z1,z1064,z2,z4,z5]),(0,[z122,z1,z11,z65,z4,z5])],[(0,[z1,z11,z2,z4,z1065,z5]),(0,[z1,z11,z2,z4,z956,z5])],[(0,[z806,z1,z58,z2,z4,z5]),(0,[z26,z1,z263,z2,z4,z5])],[(0,[z1,z11,z2,z1066,z4,z5]),(0,[z1,z1067,z2,z12,z4,z5])],[(0,[z20,z1,z11,z1068,z4,z5]),(0,[z697,z1,z11,z2,z4,z5]),(0,[z24,z1,z12,z4,z5,z700]),(0,[z1,z2,z4,z384,z278,z5]),(0,[z350,z351,z2,z12,z4,z5])],[(0,[z40,z125,z1,z2,z4,z5]),(0,[z1069,z1,z11,z2,z1070,z5]),(0,[z1,z11,z2,z4,z1071,z5])],[(0,[z1,z2,z12,z4,z5,z495]),(0,[z1,z11,z2,z4,z528,z49]),(0,[z1,z11,z118,z692,z4,z5])],[(0,[z123,z11,z2,z692,z4,z5])],[(0,[z20,z1,z11,z4,z1072,z5]),(0,[z1,z1073,z2,z12,z4,z5]),(0,[z122,z1,z12,z4,z5,z48])],[(0,[z1,z11,z2,z4,z1074,z5]),(0,[z0,z1,z100,z2,z4,z5]),(0,[z1,z11,z12,z22,z4,z5])],[(0,[z1,z11,z4,z114,z5,z77]),(0,[z524,z1,z2,z4,z5,z49])],[(0,[z691,z1,z11,z2,z4,z5]),(0,[z26,z1,z2,z4,z5,z1031]),(0,[z1,z11,z210,z4,z5,z49]),(0,[z136,z1,z11,z4,z114,z5])],[(0,[z0,z29,z1,z2,z4,z5]),(0,[z1,z1075,z11,z2,z4,z5]),(0,[z24,z163,z1,z591,z4,z5]),(0,[z529,z1,z2,z4,z5,z49]),(0,[z122,z1,z11,z4,z144,z5])],[(0,[z20,z1,z11,z1076,z4,z5]),(0,[z1,z11,z2,z1077,z4,z5])],[(0,[z26,z1,z18,z2,z71,z5]),(0,[z1078,z1,z11,z2,z4,z5]),(0,[z26,z350,z11,z2,z4,z5]),(0,[z1,z21,z18,z12,z4,z5]),(0,[z42,z1,z2,z4,z5,z49])],[(0,[z1,z11,z2,z1079,z4,z5]),(0,[z1080,z1,z11,z2,z4,z5]),(0,[z159,z1,z11,z169,z4,z218])]],
   [[(0,[z53,z1,z18,z2,z4,z5])],[(0,[z794,z1,z11,z2,z4,z5]),(0,[z26,z1,z2,z4,z5,z1081]),(0,[z898,z1,z10,z2,z4,z5])],[(0,[z1,z11,z10,z2,z4,z200])],[(0,[z20,z422,z298,z11,z4,z5]),(0,[z1082,z1,z11,z2,z12,z61]),(0,[z163,z1,z126,z2,z4,z5]),(0,[z20,z1,z11,z1083,z4,z5])],[(0,[z151,z1,z2,z137,z4,z5]),(0,[z308,z1,z11,z4,z5,z450]),(0,[z20,z1,z11,z2,z84,z5])],[(0,[z122,z96,z1,z11,z4,z5]),(0,[z1084,z1,z11,z2,z4,z5]),(1,[z317,z1,z2,z4,z5])],[(0,[z517,z1,z18,z2,z4,z5]),(0,[z1,z2,z4,z5,z1085,z77])],[(0,[z96,z1,z220,z2,z4,z5]),(0,[z20,z1,z11,z210,z4,z5]),(0,[z1086,z1,z11,z141,z4,z5])],[(0,[z0,z1,z2,z4,z71,z5]),(0,[z53,z1,z2,z4,z775,z5])],[(0,[z1,z11,z2,z1087,z4,z5])],[(0,[z1,z1088,z2,z12,z4,z5]),(0,[z1,z11,z38,z264,z4,z5]),(0,[z1,z11,z2,z4,z5,z1089]),(0,[z1,z11,z2,z4,z5,z1090]),(0,[z304,z1,z11,z2,z12,z268])],[(0,[z1091,z1,z11,z196,z4,z5]),(0,[z1,z11,z2,z4,z1092,z5]),(0,[z1,z246,z2,z7,z4,z5]),(0,[z1,z2,z12,z4,z5,z1093]),(0,[z1,z11,z2,z4,z1094,z5]),(0,[z1,z1095,z254,z11,z4,z5]),(0,[z1,z206,z2,z4,z661,z5])],[(0,[z74,z11,z235,z12,z4,z5]),(0,[z1,z11,z2,z12,z1096,z5]),(0,[z129,z1,z209,z11,z4,z5]),(0,[z1,z2,z4,z5,z581,z67]),(0,[z1,z1097,z2,z12,z4,z5])],[(0,[z1,z11,z1098,z12,z4,z5]),(0,[z1,z263,z188,z12,z4,z5]),(0,[z1099,z26,z1,z2,z4,z5]),(0,[z317,z20,z1,z2,z4,z5])],[(0,[z26,z1,z2,z12,z307,z5]),(0,[z1,z11,z2,z4,z5,z149]),(0,[z1100,z100,z11,z2,z4,z5]),(0,[z1101,z1,z11,z12,z4,z5]),(0,[z122,z1,z11,z4,z5,z49])],[(0,[z26,z1,z2,z4,z820,z5]),(0,[z151,z1,z2,z4,z71,z5])],[(1,[z219,z1,z2,z4,z5]),(0,[z1,z11,z2,z1102,z4,z5]),(0,[z1,z2,z459,z4,z48,z49])],[(0,[z1,z11,z2,z4,z1103,z5]),(0,[z53,z1,z2,z591,z4,z5]),(0,[z1,z10,z2,z4,z5,z48]),(0,[z1,z11,z2,z1104,z4,z5]),(0,[z304,z1,z11,z2,z12,z61])],[(0,[z1,z11,z2,z1105,z4,z5]),(0,[z74,z100,z11,z2,z4,z75])],[(0,[z1,z11,z2,z4,z5,z1106]),(0,[z1,z1107,z2,z12,z4,z5]),(0,[z11,z2,z12,z59,z5,z200]),(0,[z20,z1,z27,z2,z4,z5]),(0,[z1,z11,z2,z642,z413,z5]),(0,[z910,z1,z11,z2,z4,z5]),(0,[z564,z1,z11,z4,z5,z49])],[(0,[z40,z39,z1,z11,z4,z5]),(0,[z1,z886,z11,z2,z4,z5])],[(0,[z1,z11,z2,z1108,z4,z5]),(1,[z40,z1,z2,z4,z135]),(0,[z1109,z26,z1,z2,z4,z5]),(0,[z1,z927,z10,z2,z4,z5])],[(0,[z26,z1,z2,z4,z873,z5])],[(0,[z517,z1,z11,z2,z4,z5]),(0,[z1110,z1,z11,z2,z4,z5]),(0,[z26,z1,z11,z118,z4,z5])],[(0,[z1111,z1,z11,z2,z4,z5]),(0,[z24,z39,z1,z11,z4,z5]),(0,[z159,z20,z25,z11,z4,z5]),(0,[z1,z292,z11,z10,z4,z5])],[(0,[z1,z11,z2,z12,z5,z1112]),(0,[z1,z11,z2,z4,z5,z1113]),(0,[z1,z11,z2,z4,z5,z1114]),(0,[z1,z11,z2,z12,z84,z5])],[(0,[z1,z1115,z2,z12,z4,z5]),(0,[z14,z422,z298,z11,z4,z5]),(0,[z1116,z1,z11,z2,z4,z5])],[(0,[z20,z1,z11,z146,z4,z5]),(0,[z26,z1,z1117,z2,z4,z5]),(0,[z14,z1,z134,z2,z4,z180]),(0,[z1,z117,z11,z12,z1118,z5]),(0,[z14,z1,z11,z2,z84,z5]),(0,[z1,z11,z320,z4,z5,z218])],[(0,[z1,z11,z2,z1119,z4,z5]),(0,[z1,z11,z1120,z12,z4,z5]),(0,[z1,z11,z257,z12,z236,z5]),(0,[z1,z11,z2,z591,z4,z5])],[(0,[z298,z783,z11,z12,z4,z5]),(0,[z1,z10,z2,z4,z278,z5]),(0,[z14,z1,z11,z2,z4,z1121])],[(0,[z1,z1122,z2,z12,z4,z5]),(0,[z39,z1,z11,z4,z75,z5]),(0,[z53,z1,z2,z872,z4,z5]),(0,[z1,z117,z11,z12,z722,z5]),(0,[z1,z11,z12,z4,z66,z443]),(0,[z328,z1,z11,z2,z338,z37])],[(0,[z26,z1,z11,z141,z4,z5]),(0,[z0,z1,z2,z19,z4,z5]),(0,[z159,z1,z11,z4,z5,z77]),(0,[z53,z207,z1,z2,z4,z5])]],
   [[(0,[z14,z1,z11,z2,z4,z951]),(0,[z1,z1123,z2,z12,z4,z5])],[(0,[z20,z1,z11,z943,z4,z5]),(0,[z153,z11,z10,z2,z4,z5])],[(0,[z53,z1,z2,z2,z4,z5])],[(1,[z39,z1,z11,z4,z5]),(0,[z1124,z11,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z1125]),(0,[z26,z1,z363,z2,z4,z5]),(0,[z1126,z11,z2,z12,z4,z5]),(0,[z1,z18,z2,z12,z19,z5]),(0,[z159,z25,z11,z12,z4,z218])],[(0,[z1,z11,z2,z1127,z4,z5]),(0,[z1,z11,z12,z4,z385,z5])],[(0,[z1,z11,z4,z203,z5,z49])],[(0,[z0,z1,z2,z4,z5,z60]),(0,[z1,z2,z12,z4,z5,z1128]),(0,[z1,z11,z1129,z2,z4,z5])],[(0,[z1,z2,z12,z4,z5,z1130]),(0,[z20,z1,z1131,z11,z4,z5]),(0,[z1,z1132,z106,z2,z4,z5])],[(0,[z1,z100,z287,z2,z4,z5]),(0,[z1,z11,z2,z4,z1133,z5]),(0,[z20,z1,z11,z4,z66,z5])],[(0,[z26,z8,z1,z2,z4,z5]),(0,[z20,z1134,z1,z11,z4,z5]),(1,[z0,z1,z4,z5,z130])],[(0,[z14,z1,z27,z2,z4,z5]),(0,[z39,z1,z11,z392,z4,z5]),(0,[z1,z11,z2,z435,z562,z5])],[(0,[z1135,z1,z11,z2,z4,z5])],[(1,[z20,z1,z147,z4,z5]),(0,[z1,z45,z12,z4,z203,z5])],[(0,[z26,z1,z63,z2,z4,z5]),(0,[z1,z11,z2,z12,z37,z268])],[(0,[z1,z11,z464,z289,z4,z5]),(0,[z1136,z1,z11,z2,z4,z5]),(0,[z1137,z26,z1,z137,z4,z5]),(0,[z742,z11,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z1138,z49])],[(0,[z1,z100,z2,z221,z4,z5]),(0,[z1,z100,z11,z4,z5,z450])],[(0,[z1,z30,z2,z183,z4,z5]),(0,[z1,z11,z196,z339,z4,z5]),(0,[z82,z14,z11,z2,z59,z5]),(0,[z1,z11,z137,z530,z4,z5]),(0,[z1,z2,z12,z4,z5,z914]),(0,[z1139,z0,z1,z2,z4,z5])],[(0,[z163,z185,z1,z12,z4,z5]),(0,[z122,z24,z1,z11,z4,z5]),(0,[z1,z117,z106,z12,z4,z5]),(0,[z1,z11,z2,z1140,z4,z5])],[(0,[z1,z11,z2,z12,z1141,z5]),(0,[z1,z11,z10,z257,z4,z5]),(0,[z26,z39,z1,z11,z4,z5]),(0,[z437,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z1142,z5])],[(0,[z14,z1,z58,z2,z4,z5]),(0,[z83,z1,z11,z12,z4,z5]),(0,[z26,z335,z1,z11,z114,z5]),(0,[z1,z106,z2,z138,z4,z5]),(0,[z1,z11,z2,z4,z5,z615]),(0,[z0,z1,z1143,z2,z4,z5])],[(0,[z1144,z11,z2,z12,z333,z5]),(0,[z1145,z1,z2,z12,z71,z5])],[(0,[z31,z1,z205,z2,z4,z5]),(0,[z50,z1,z11,z2,z4,z5]),(0,[z1,z1146,z11,z2,z4,z5])],[(0,[z1147,z11,z2,z12,z4,z5]),(0,[z1,z45,z2,z4,z5,z49])],[(0,[z20,z1,z11,z313,z4,z5]),(0,[z1148,z1,z11,z2,z4,z5])],[(0,[z1,z11,z1149,z12,z4,z5]),(0,[z62,z1,z11,z2,z4,z5]),(0,[z20,z1,z11,z764,z4,z5])],[(0,[z20,z1150,z11,z2,z4,z5])],[(0,[z1,z27,z257,z12,z4,z5]),(0,[z1,z11,z2,z12,z832,z5])],[(0,[z1,z30,z464,z12,z4,z5]),(0,[z163,z1,z12,z508,z4,z5]),(0,[z1,z100,z2,z4,z1151,z5]),(0,[z1,z11,z1152,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z1032])],[(0,[z298,z150,z11,z12,z4,z5]),(0,[z129,z1,z11,z12,z4,z5]),(0,[z1,z11,z10,z4,z5,z130])],[(0,[z275,z205,z2,z12,z4,z60]),(0,[z1153,z1,z100,z2,z4,z5]),(0,[z0,z1,z2,z523,z4,z5])],[(0,[z20,z1,z6,z2,z4,z5]),(0,[z1154,z1,z11,z10,z4,z5]),(0,[z350,z357,z2,z12,z4,z5])],[(0,[z1,z11,z2,z4,z189,z352]),(0,[z1101,z1,z100,z11,z4,z5]),(0,[z1155,z724,z11,z2,z4,z5])]],
   [[(0,[z1,z21,z100,z11,z4,z5]),(0,[z53,z1,z2,z1156,z4,z5])],[(0,[z422,z298,z11,z10,z4,z5]),(0,[z1,z11,z1157,z12,z4,z5])],[(0,[z1,z11,z2,z1158,z4,z5])],[(0,[z53,z1,z2,z333,z4,z5]),(0,[z1,z100,z11,z2,z338,z37]),(0,[z1,z1095,z11,z2,z4,z5])],[(0,[z1,z263,z2,z12,z4,z189]),(0,[z26,z1,z11,z38,z4,z5]),(0,[z20,z1,z11,z721,z4,z5])],[(0,[z1,z1159,z2,z12,z4,z5])],[(0,[z20,z1,z11,z4,z1160,z5]),(0,[z1,z11,z2,z4,z741,z5]),(0,[z1,z11,z919,z2,z4,z5])],[(0,[z1,z11,z2,z1161,z4,z5]),(0,[z20,z1,z117,z11,z426,z5]),(0,[z1,z10,z2,z4,z382,z5])],[(0,[z39,z298,z1,z11,z4,z5]),(0,[z0,z1,z2,z248,z4,z5]),(0,[z26,z25,z11,z2,z4,z5]),(0,[z318,z1,z2,z71,z5,z49]),(0,[z1,z11,z10,z4,z5,z450]),(0,[z1,z11,z4,z5,z49,z665])],[(0,[z1,z11,z2,z1162,z4,z5]),(0,[z1,z2,z138,z4,z382,z5])],[(0,[z1,z30,z2,z339,z4,z5]),(0,[z20,z647,z1,z11,z4,z5]),(0,[z122,z1,z11,z4,z5,z355])],[(0,[z828,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z692,z4,z5])],[(0,[z1,z11,z2,z1163,z4,z5]),(0,[z1164,z11,z2,z12,z4,z5])],[(0,[z1165,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z514,z4,z5]),(0,[z1166,z11,z2,z12,z4,z5])],[(0,[z136,z1,z11,z320,z4,z5]),(0,[z1,z12,z4,z203,z278,z5])],[(0,[z11,z2,z198,z311,z4,z5]),(0,[z704,z39,z1,z11,z4,z5]),(0,[z310,z1,z11,z2,z5,z451])],[(0,[z224,z1,z11,z248,z4,z5]),(0,[z1,z351,z2,z4,z5,z49]),(0,[z159,z1,z206,z12,z4,z5]),(0,[z1,z11,z2,z12,z5,z268])],[(0,[z1167,z1,z263,z2,z4,z5]),(0,[z0,z1,z2,z12,z4,z5]),(0,[z1168,z1,z11,z10,z4,z5])],[(0,[z9,z1,z2,z198,z4,z5]),(0,[z39,z1,z11,z4,z5,z61])],[(0,[z1,z11,z196,z12,z4,z5]),(0,[z422,z298,z6,z12,z4,z5]),(0,[z1,z58,z2,z894,z4,z5]),(0,[z159,z20,z1,z11,z4,z1001]),(1,[z477,z1,z11,z4,z5])],[(0,[z122,z1,z186,z11,z4,z5]),(0,[z26,z1,z2,z4,z834,z5])],[(0,[z14,z1,z6,z2,z4,z5]),(0,[z1,z1169,z11,z2,z4,z5])],[(0,[z1170,z96,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z1171]),(0,[z1172,z1,z11,z2,z4,z5]),(0,[z1173,z11,z2,z12,z4,z5]),(0,[z310,z1,z11,z2,z120,z5])],[(0,[z1174,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z1175]),(0,[z11,z2,z12,z333,z173,z5]),(0,[z1,z100,z11,z2,z236,z5]),(0,[z0,z163,z1,z2,z4,z5]),(0,[z1,z11,z1176,z12,z4,z5])],[(0,[z1,z11,z1177,z12,z4,z5])],[(0,[z224,z1,z11,z12,z4,z5]),(0,[z1178,z1,z11,z2,z12,z61]),(0,[z1,z11,z235,z12,z413,z5]),(0,[z40,z1,z2,z142,z4,z101])],[(0,[z14,z1,z11,z2,z4,z1179]),(0,[z20,z1,z11,z4,z1180,z5])],[(0,[z1,z11,z2,z12,z1181,z5]),(0,[z1,z1182,z2,z12,z4,z5])],[(0,[z1,z1183,z2,z12,z4,z5]),(0,[z1,z11,z2,z12,z59,z200]),(0,[z1,z11,z2,z4,z5,z1184]),(0,[z24,z1134,z1,z12,z4,z5]),(0,[z40,z55,z2,z12,z4,z101]),(0,[z1,z43,z2,z242,z4,z5])],[(0,[z1,z11,z2,z12,z1185,z5]),(0,[z1,z1186,z11,z12,z4,z5])],[(0,[z813,z11,z2,z12,z4,z5]),(0,[z129,z1,z134,z11,z4,z5]),(0,[z1,z11,z12,z4,z1187,z5]),(0,[z1,z1188,z351,z2,z4,z5])],[(0,[z39,z1,z11,z210,z4,z5]),(0,[z159,z20,z1,z11,z562,z5])]],
   [[(0,[z1,z11,z2,z289,z4,z5]),(0,[z1,z117,z11,z530,z4,z5]),(0,[z40,z1,z2,z4,z49,z101]),(0,[z1,z287,z2,z4,z5,z49])],[(0,[z1,z11,z108,z530,z4,z5]),(0,[z82,z39,z1,z11,z4,z5]),(0,[z1189,z1,z11,z2,z4,z5]),(0,[z1,z2,z12,z4,z382,z5]),(0,[z1,z2,z12,z4,z253,z5]),(0,[z20,z1,z11,z4,z770,z5]),(0,[z20,z1,z2,z4,z5,z48])],[(0,[z356,z74,z11,z2,z4,z75]),(0,[z20,z123,z11,z2,z4,z5]),(0,[z193,z1030,z11,z2,z4,z5]),(0,[z1,z11,z10,z2,z562,z5]),(0,[z1,z2,z242,z12,z4,z5]),(0,[z752,z1,z11,z4,z5,z86])],[(0,[z1,z1190,z2,z12,z4,z5])],[(0,[z422,z298,z11,z7,z4,z5]),(1,[z62,z1,z11,z4,z5]),(0,[z151,z1,z63,z2,z4,z5]),(0,[z136,z163,z1,z11,z4,z5]),(0,[z1,z117,z11,z138,z4,z5]),(0,[z25,z351,z2,z12,z4,z5]),(0,[z14,z1,z11,z2,z4,z1191])],[(0,[z1192,z1,z11,z2,z4,z5]),(0,[z153,z186,z2,z12,z4,z5])],[(0,[z1,z90,z6,z2,z4,z5]),(0,[z1,z10,z2,z738,z4,z5])],[(0,[z1,z11,z2,z4,z5,z1193]),(0,[z437,z1,z11,z4,z180,z5])],[(0,[z1,z11,z65,z12,z4,z272]),(0,[z26,z1,z2,z4,z1194,z5])],[(0,[z1195,z11,z108,z12,z4,z5]),(0,[z1,z2,z137,z514,z4,z5]),(0,[z151,z39,z1,z11,z4,z5]),(0,[z20,z1,z117,z11,z4,z5])],[(0,[z1,z1196,z2,z12,z4,z5]),(0,[z122,z132,z1,z11,z4,z5]),(0,[z1,z11,z2,z1197,z4,z5]),(0,[z1,z100,z18,z2,z19,z5]),(0,[z695,z122,z1,z11,z4,z5])],[(0,[z1198,z1,z11,z2,z4,z5]),(0,[z1,z11,z194,z692,z4,z5])],[(0,[z1,z171,z11,z210,z4,z5])],[(0,[z1,z100,z11,z2,z4,z5]),(0,[z1,z254,z11,z12,z4,z5]),(0,[z50,z26,z1,z11,z4,z5]),(0,[z20,z1,z2,z4,z278,z5])],[(0,[z1,z1199,z11,z2,z4,z5]),(0,[z1,z2,z4,z5,z1200,z365]),(0,[z53,z1,z171,z2,z4,z5]),(0,[z1201,z1,z11,z2,z4,z5]),(0,[z1,z11,z210,z4,z5,z522])],[(0,[z1,z11,z2,z1202,z4,z5]),(0,[z26,z1,z2,z4,z299,z5])],[(0,[z1,z11,z2,z4,z49,z522]),(0,[z1,z1203,z11,z2,z4,z5])],[(0,[z0,z422,z1,z2,z4,z5]),(0,[z205,z2,z12,z4,z5,z60]),(0,[z1,z2,z12,z307,z5,z101])],[(0,[z1,z11,z2,z4,z1204,z5]),(0,[z136,z1,z11,z2,z4,z1001]),(0,[z1,z1205,z2,z12,z4,z5]),(0,[z1,z11,z2,z1206,z4,z5])],[(0,[z1,z2,z12,z4,z930,z5]),(0,[z1,z11,z2,z4,z1207,z5]),(0,[z26,z1,z11,z2,z1208,z5]),(0,[z1,z11,z2,z4,z1209,z5]),(0,[z20,z1,z106,z2,z4,z5])],[(0,[z1,z11,z12,z4,z1210,z5]),(0,[z1,z11,z187,z4,z114,z5])],[(0,[z0,z1,z30,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z1211]),(0,[z14,z1,z11,z2,z4,z1061]),(0,[z1,z11,z2,z12,z722,z5]),(0,[z1,z11,z12,z4,z5,z443])],[(0,[z1,z11,z2,z4,z384,z5]),(0,[z122,z1,z100,z11,z4,z5]),(0,[z1,z11,z4,z5,z450,z423])],[(0,[z1,z11,z2,z4,z5,z1212]),(0,[z0,z1,z2,z4,z114,z5])],[(0,[z1,z1213,z2,z12,z4,z5]),(0,[z39,z1,z171,z11,z4,z5])],[(0,[z122,z29,z1,z11,z4,z5]),(0,[z1214,z298,z11,z12,z4,z5]),(0,[z26,z1,z424,z2,z4,z5]),(0,[z1215,z1,z254,z11,z4,z5]),(0,[z1216,z1,z11,z2,z4,z5]),(0,[z1217,z11,z2,z12,z4,z5]),(0,[z14,z123,z11,z2,z4,z5])],[(0,[z1,z1218,z11,z2,z4,z5]),(0,[z1,z11,z65,z12,z4,z1018]),(0,[z1219,z1,z11,z2,z4,z5]),(0,[z1,z123,z11,z2,z12,z61])],[(1,[z122,z1,z4,z5,z48])],[(0,[z1,z1220,z11,z2,z4,z5]),(0,[z199,z11,z2,z12,z333,z5]),(0,[z1,z11,z2,z4,z1221,z5]),(0,[z20,z1,z11,z2,z167,z5]),(0,[z1,z11,z12,z4,z5,z130]),(0,[z1,z11,z2,z12,z4,z528]),(0,[z122,z1,z11,z4,z5,z451])],[(0,[z1,z11,z2,z1222,z4,z5]),(0,[z578,z26,z1,z2,z4,z5]),(0,[z1,z117,z11,z12,z111,z5]),(0,[z1,z117,z11,z111,z502,z5])],[(0,[z11,z2,z12,z173,z59,z5]),(0,[z14,z1,z606,z2,z4,z5]),(0,[z14,z1,z11,z2,z4,z528]),(0,[z1,z11,z1223,z2,z4,z5])],[(0,[z1,z11,z2,z1224,z4,z5])]],
   [[(0,[z1,z2,z4,z1225,z71,z5]),(0,[z39,z1,z11,z4,z66,z5])],[(0,[z1,z11,z2,z1226,z4,z5]),(0,[z26,z96,z30,z2,z4,z5]),(0,[z1227,z1,z11,z2,z4,z5]),(0,[z1055,z1,z11,z2,z4,z5]),(0,[z163,z1,z11,z4,z5,z77]),(0,[z122,z1,z11,z459,z4,z5])],[(0,[z20,z1,z11,z1228,z4,z5]),(0,[z1,z11,z2,z4,z1229,z5])],[(0,[z1,z11,z2,z4,z1230,z5])],[(0,[z29,z30,z2,z4,z5,z49]),(0,[z122,z1,z11,z108,z4,z5]),(0,[z20,z1030,z1,z11,z4,z5]),(0,[z1231,z1,z11,z2,z4,z5]),(0,[z26,z1,z65,z137,z4,z5]),(0,[z14,z1,z2,z4,z278,z5])],[(0,[z1232,z1,z11,z2,z4,z5])],[(0,[z151,z1,z11,z108,z4,z5])],[(0,[z1,z1233,z2,z12,z4,z5]),(0,[z1,z11,z12,z84,z5,z218])],[(0,[z20,z1,z351,z2,z4,z5]),(0,[z1,z45,z2,z46,z433,z5])],[(0,[z20,z9,z1,z2,z4,z5]),(0,[z1,z11,z12,z4,z179,z5]),(0,[z20,z1,z11,z1234,z4,z5])],[(0,[z350,z11,z2,z12,z4,z5]),(0,[z224,z1,z100,z11,z4,z5]),(0,[z26,z1235,z1,z2,z4,z5]),(0,[z1,z11,z154,z12,z307,z5]),(0,[z1,z11,z2,z4,z5,z1236]),(0,[z14,z1,z106,z2,z4,z5]),(0,[z0,z372,z1,z2,z4,z5])],[(0,[z26,z1,z126,z2,z4,z5])],[(0,[z150,z11,z108,z12,z4,z5]),(0,[z1,z11,z2,z12,z4,z1237]),(0,[z20,z1,z11,z188,z4,z5]),(0,[z1,z100,z11,z1177,z4,z5]),(0,[z1,z1238,z11,z2,z4,z5]),(0,[z1,z363,z2,z12,z338,z5])],[(0,[z1,z246,z2,z4,z5,z49]),(0,[z1,z11,z2,z1239,z4,z5]),(0,[z55,z11,z2,z142,z4,z5])],[],[(0,[z1240,z1,z11,z2,z4,z5]),(0,[z125,z96,z1,z2,z4,z5]),(0,[z1,z11,z1241,z2,z4,z5]),(0,[z275,z0,z1,z2,z4,z5]),(0,[z1,z11,z2,z4,z1242,z5]),(0,[z0,z1,z2,z4,z120,z5])],[(0,[z1,z1243,z2,z12,z4,z5]),(0,[z275,z122,z1,z11,z4,z5])],[(0,[z1,z11,z2,z1244,z4,z5]),(0,[z1,z11,z2,z12,z167,z5]),(0,[z1,z11,z118,z4,z5,z49])],[(0,[z1,z11,z1245,z12,z4,z5]),(0,[z199,z11,z2,z12,z1246,z5]),(0,[z1,z343,z27,z2,z4,z5]),(0,[z1,z11,z2,z12,z1247,z5]),(0,[z1,z11,z2,z4,z1225,z5]),(0,[z1,z11,z2,z433,z873,z5]),(0,[z53,z1,z2,z46,z4,z5]),(0,[z335,z1,z11,z12,z722,z5]),(0,[z1,z11,z2,z1248,z4,z49]),(0,[z123,z11,z2,z4,z5,z49])],[(0,[z14,z1,z11,z2,z167,z5]),(0,[z1,z1067,z10,z2,z4,z5])],[(0,[z20,z1,z246,z2,z4,z5]),(0,[z1249,z1,z11,z4,z481,z5]),(0,[z1,z1250,z2,z12,z4,z5]),(0,[z1,z11,z2,z562,z5,z49])],[(0,[z1,z11,z2,z1251,z4,z5]),(0,[z0,z1,z2,z4,z5,z218]),(0,[z89,z1,z2,z4,z66,z5])],[(0,[z25,z186,z11,z12,z4,z5])],[(0,[z252,z0,z1,z2,z4,z5]),(0,[z20,z1,z2,z4,z382,z5])],[(0,[z252,z122,z1,z11,z4,z5]),(0,[z26,z1,z287,z2,z4,z5]),(0,[z39,z1,z11,z433,z4,z5]),(0,[z1,z141,z221,z12,z4,z5]),(0,[z1252,z1,z11,z2,z4,z5]),(0,[z1253,z1,z11,z2,z4,z5]),(0,[z0,z1,z2,z459,z4,z49]),(0,[z0,z1,z2,z4,z5,z674]),(0,[z136,z1,z11,z1254,z4,z5])],[(0,[z1,z246,z2,z405,z4,z5]),(0,[z26,z1,z1255,z2,z4,z5]),(0,[z20,z1256,z1,z11,z4,z5])],[(0,[z132,z11,z2,z311,z4,z5]),(0,[z1,z11,z2,z4,z1257,z5]),(0,[z1,z357,z2,z4,z5,z49])],[(0,[z1,z11,z2,z626,z4,z5]),(0,[z1,z11,z1258,z137,z4,z5]),(0,[z100,z1126,z11,z2,z4,z5])],[(0,[z1259,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z3,z307,z5])],[(0,[z1,z6,z2,z12,z4,z5]),(0,[z1082,z11,z2,z12,z4,z60]),(0,[z1,z11,z154,z12,z4,z5]),(0,[z26,z1,z2,z4,z180,z5]),(0,[z1,z11,z2,z832,z120,z5])],[(0,[z39,z1,z11,z1260,z4,z5]),(0,[z1261,z1,z11,z2,z4,z5]),(0,[z1,z11,z4,z5,z49,z807])],[(0,[z1,z11,z2,z12,z1262,z5]),(0,[z24,z185,z1,z12,z4,z5]),(0,[z0,z20,z1,z2,z4,z5]),(0,[z1263,z1,z11,z2,z4,z5]),(0,[z14,z1,z351,z2,z4,z5])]],
   [[(0,[z1,z262,z2,z221,z4,z5]),(0,[z671,z1,z2,z12,z4,z101]),(0,[z252,z96,z100,z2,z4,z5]),(0,[z14,z9,z1,z2,z4,z5]),(0,[z1,z11,z2,z12,z413,z60])],[(0,[z1,z11,z1264,z12,z4,z5]),(0,[z53,z1,z2,z4,z5,z334])],[(0,[z1,z11,z2,z12,z1265,z5]),(0,[z1,z220,z2,z137,z4,z5])],[(0,[z26,z30,z2,z4,z5,z60]),(0,[z132,z11,z2,z198,z4,z5]),(0,[z20,z1,z263,z2,z4,z5]),(0,[z14,z1,z11,z188,z4,z5]),(0,[z1,z27,z2,z626,z4,z5]),(0,[z804,z1,z11,z2,z775,z5]),(0,[z1,z11,z2,z46,z1070,z5])],[(0,[z20,z1,z11,z65,z4,z66]),(0,[z14,z1,z11,z4,z1266,z5])],[(0,[z1,z11,z2,z4,z5,z1267]),(0,[z26,z1,z254,z11,z4,z5]),(0,[z1,z11,z2,z4,z144,z334])],[(0,[z1,z1268,z2,z12,z4,z5]),(0,[z26,z24,z1,z137,z4,z5]),(0,[z1,z11,z43,z2,z4,z334]),(0,[z304,z1,z11,z2,z288,z61])],[(0,[z1,z11,z2,z4,z5,z1269])],[(0,[z20,z1,z11,z235,z4,z5]),(0,[z1,z100,z11,z154,z4,z5]),(0,[z1,z1270,z2,z12,z4,z5])],[(0,[z74,z11,z196,z12,z4,z5]),(0,[z422,z298,z246,z12,z4,z5]),(0,[z9,z1,z100,z2,z4,z5]),(0,[z249,z1,z11,z2,z4,z5])],[(0,[z1271,z39,z1,z11,z4,z5]),(0,[z1272,z11,z2,z12,z4,z5]),(0,[z14,z1,z713,z2,z4,z5])],[(0,[z20,z298,z11,z108,z4,z5]),(0,[z14,z1,z246,z2,z4,z5]),(0,[z26,z1,z2,z4,z1273,z5]),(0,[z1274,z39,z1,z11,z4,z5])],[(0,[z1,z1275,z2,z12,z4,z5]),(0,[z318,z1,z2,z12,z253,z5]),(0,[z1,z11,z2,z4,z5,z334])],[(0,[z1,z11,z852,z2,z4,z5]),(0,[z1,z186,z11,z220,z4,z5]),(0,[z1,z220,z2,z4,z71,z5]),(0,[z53,z1,z2,z4,z37,z5])],[(1,[z11,z2,z12,z59,z200]),(0,[z1,z11,z141,z12,z167,z5]),(0,[z14,z1,z2,z4,z382,z5]),(0,[z25,z357,z2,z12,z4,z5])],[(0,[z24,z1,z11,z12,z84,z5]),(0,[z1,z2,z12,z4,z180,z1276]),(0,[z1,z11,z1277,z2,z4,z49]),(0,[z1,z11,z2,z3,z4,z5]),(0,[z1,z363,z2,z12,z4,z5]),(0,[z20,z350,z11,z2,z4,z5]),(0,[z1,z420,z11,z12,z4,z5]),(0,[z1002,z1,z11,z118,z4,z5]),(0,[z752,z1,z11,z12,z4,z5])],[(0,[z1,z186,z494,z12,z4,z5]),(0,[z329,z1,z30,z2,z4,z5]),(0,[z26,z39,z1,z100,z4,z5]),(0,[z26,z1,z2,z71,z5,z61]),(0,[z1,z18,z2,z19,z736,z5])],[(0,[z867,z20,z1,z137,z4,z5]),(0,[z1215,z1,z11,z2,z4,z5])],[(0,[z1,z11,z1278,z12,z4,z5]),(0,[z163,z1,z206,z12,z4,z5]),(0,[z26,z1,z2,z1279,z4,z5]),(0,[z1,z11,z870,z12,z4,z5]),(0,[z53,z1,z2,z4,z770,z5]),(0,[z14,z1,z11,z2,z4,z1280])],[(0,[z1281,z1,z11,z2,z4,z5]),(0,[z26,z24,z1,z108,z4,z5]),(0,[z26,z1,z11,z2,z338,z37]),(0,[z1,z11,z1282,z2,z4,z5])],[(0,[z1,z11,z2,z1283,z4,z5]),(0,[z1,z11,z464,z4,z5,z49]),(0,[z1284,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z1285,z4,z5]),(0,[z1,z11,z2,z4,z5,z1286]),(0,[z216,z100,z11,z2,z4,z5]),(0,[z1,z117,z11,z111,z5,z49])],[(0,[z1287,z11,z2,z12,z4,z5]),(0,[z1137,z1,z11,z220,z4,z5]),(0,[z40,z53,z1,z2,z4,z5]),(0,[z159,z20,z1,z11,z84,z5]),(0,[z195,z1,z11,z2,z832,z5])],[(0,[z26,z199,z11,z2,z333,z5]),(0,[z1,z11,z2,z530,z4,z5]),(0,[z53,z1,z117,z2,z4,z5])],[(0,[z486,z11,z583,z108,z4,z5]),(0,[z14,z1,z11,z2,z4,z1288]),(0,[z1,z11,z2,z4,z1289,z5]),(0,[z159,z1,z11,z12,z4,z218]),(0,[z1290,z1,z11,z320,z4,z5])],[(0,[z1,z100,z205,z2,z4,z5]),(0,[z26,z1,z2,z4,z5,z222]),(0,[z1,z126,z2,z221,z4,z5]),(0,[z1,z11,z10,z2,z84,z5]),(0,[z1291,z1,z11,z2,z4,z5])],[(0,[z14,z1,z263,z2,z4,z5]),(0,[z24,z53,z1,z2,z4,z5]),(0,[z26,z1,z2,z147,z4,z5])],[(0,[z125,z24,z1,z2,z4,z5]),(0,[z1,z11,z2,z4,z1292,z5]),(0,[z1,z11,z2,z138,z4,z5]),(0,[z1293,z1,z11,z2,z4,z5]),(0,[z14,z1,z11,z65,z4,z66])],[(0,[z20,z1,z11,z464,z4,z5]),(0,[z1,z11,z2,z1294,z4,z5]),(0,[z1,z58,z2,z264,z4,z5]),(0,[z1,z11,z10,z210,z4,z5]),(0,[z1,z2,z4,z5,z48,z222])],[(0,[z26,z1,z1295,z2,z4,z5]),(0,[z477,z1,z126,z11,z4,z5])],[(0,[z1,z100,z11,z196,z4,z5]),(0,[z1,z11,z2,z4,z5,z1296]),(0,[z1297,z1,z11,z2,z4,z5])],[(0,[z1,z11,z1298,z2,z4,z5]),(0,[z14,z1,z11,z235,z4,z5]),(0,[z20,z1,z871,z11,z4,z5]),(0,[z1,z11,z2,z4,z832,z5])]],
   [[(0,[z1,z11,z2,z4,z5,z1299])],[(0,[z136,z298,z1,z11,z4,z5]),(0,[z1,z11,z2,z12,z1300,z5]),(0,[z39,z1,z117,z11,z4,z5]),(0,[z1301,z1,z11,z2,z4,z5])],[(0,[z298,z1,z11,z187,z4,z5]),(0,[z1,z11,z2,z1302,z4,z5]),(0,[z159,z1,z11,z187,z4,z218])],[(0,[z1,z1303,z2,z12,z4,z5]),(0,[z1,z18,z10,z2,z19,z5]),(0,[z1,z11,z2,z4,z5,z1304]),(0,[z25,z11,z2,z4,z5,z49])],[(0,[z39,z486,z1,z11,z4,z5]),(0,[z1305,z1,z11,z2,z4,z5]),(1,[z26,z1,z210,z4,z5]),(0,[z39,z1,z11,z65,z4,z5]),(0,[z1,z267,z2,z12,z4,z5]),(0,[z1,z209,z11,z4,z5,z130])],[(1,[z53,z1,z2,z4,z5]),(0,[z1,z137,z1306,z12,z4,z5]),(0,[z1086,z1,z11,z2,z4,z5])],[(0,[z252,z96,z464,z12,z4,z5]),(0,[z1024,z11,z2,z12,z4,z5]),(0,[z1,z11,z22,z523,z4,z5]),(0,[z14,z1,z11,z265,z4,z5])],[(0,[z1,z11,z1307,z12,z4,z5])],[(0,[z82,z11,z2,z59,z5,z49]),(0,[z1308,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z1309,z4,z5]),(0,[z20,z1,z11,z118,z4,z5])],[(0,[z62,z1,z11,z4,z5,z365]),(0,[z26,z1,z186,z137,z4,z5]),(0,[z53,z1,z2,z4,z144,z5]),(0,[z1310,z11,z2,z12,z4,z5]),(0,[z1,z2,z4,z969,z5,z49])],[(0,[z26,z1,z11,z2,z307,z5]),(0,[z318,z1,z2,z384,z71,z5]),(0,[z1,z11,z2,z12,z338,z1311]),(0,[z123,z11,z2,z12,z4,z61])],[(0,[z1,z11,z2,z1312,z4,z5]),(0,[z671,z26,z1,z2,z4,z5]),(0,[z1,z1313,z2,z12,z4,z5]),(0,[z1314,z11,z2,z198,z4,z5]),(0,[z40,z1,z2,z4,z5,z135])],[(0,[z74,z11,z2,z12,z4,z1315]),(0,[z26,z1,z2,z1316,z4,z5]),(0,[z1,z11,z454,z12,z4,z5]),(0,[z1,z11,z1317,z12,z4,z5]),(0,[z1,z11,z141,z3,z4,z5]),(1,[z123,z11,z2,z12,z61])],[(0,[z14,z1,z11,z194,z4,z5])],[(0,[z1,z11,z2,z1318,z4,z5]),(0,[z1,z11,z2,z1319,z4,z5]),(0,[z1320,z1,z11,z2,z4,z5]),(0,[z20,z1,z147,z12,z4,z5])],[(0,[z53,z96,z1,z2,z4,z5]),(0,[z20,z548,z1,z11,z4,z5]),(0,[z1,z11,z1321,z12,z4,z5]),(0,[z1,z292,z45,z12,z4,z5])],[(0,[z39,z1,z11,z4,z144,z5])],[(0,[z1,z11,z10,z1322,z4,z5]),(0,[z1,z705,z11,z2,z119,z5]),(0,[z1,z63,z2,z221,z4,z5])],[(0,[z97,z29,z2,z12,z4,z5]),(0,[z26,z1,z2,z607,z4,z5]),(0,[z53,z1030,z1,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z1323])],[(0,[z14,z1,z11,z464,z4,z5])],[(0,[z486,z11,z108,z12,z4,z5]),(0,[z53,z1,z2,z4,z59,z5]),(0,[z151,z1,z2,z4,z180,z5]),(0,[z26,z53,z1,z2,z4,z5]),(0,[z1,z2,z221,z241,z4,z5]),(0,[z20,z1,z363,z2,z4,z5])],[(0,[z252,z96,z2,z339,z4,z5]),(0,[z20,z298,z783,z11,z4,z5]),(0,[z1324,z1,z2,z12,z4,z5]),(0,[z1325,z11,z2,z12,z4,z5])],[(0,[z381,z1,z11,z2,z4,z5])],[(0,[z96,z1,z2,z514,z4,z5]),(0,[z1,z11,z1326,z2,z4,z5]),(0,[z1327,z122,z1,z11,z4,z5])],[(0,[z1,z11,z2,z1328,z4,z5])],[(0,[z39,z96,z1,z11,z4,z5]),(0,[z185,z1,z2,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z1329])],[(0,[z1,z58,z2,z12,z4,z5]),(0,[z1,z11,z12,z4,z1330,z5]),(0,[z26,z1,z18,z2,z19,z5]),(0,[z1,z878,z2,z4,z5,z49])],[(0,[z1,z11,z2,z1331,z4,z5]),(0,[z1,z1332,z2,z12,z4,z5])],[(0,[z312,z30,z2,z12,z4,z5]),(0,[z26,z1,z262,z2,z4,z5]),(0,[z11,z196,z12,z4,z5,z60]),(0,[z1,z11,z2,z12,z1333,z5]),(0,[z1334,z1,z11,z2,z4,z5]),(0,[z1,z11,z12,z4,z203,z5])],[(0,[z26,z1,z11,z2,z4,z5]),(0,[z1,z916,z11,z2,z4,z5]),(0,[z1,z18,z2,z4,z5,z135]),(0,[z14,z1,z1335,z11,z4,z5])],[(0,[z1,z262,z11,z2,z4,z5]),(1,[z50,z1,z11,z4,z5]),(0,[z1336,z53,z1,z2,z4,z5])],[(0,[z1,z11,z840,z12,z4,z5]),(0,[z122,z1,z11,z54,z4,z5]),(0,[z1337,z1,z11,z2,z4,z5])]],
   [[(0,[z1338,z1,z11,z2,z4,z5]),(0,[z0,z1,z416,z2,z4,z5])],[(0,[z1339,z1,z11,z2,z4,z5]),(0,[z1,z1340,z2,z12,z4,z5]),(0,[z1341,z0,z1,z2,z4,z5])],[(0,[z150,z11,z2,z12,z4,z5]),(0,[z1,z11,z1342,z12,z4,z5]),(0,[z39,z1,z11,z4,z5,z49])],[(0,[z20,z39,z1,z11,z4,z5]),(0,[z1343,z1,z11,z2,z12,z61])],[(0,[z1,z18,z2,z19,z5,z49]),(0,[z1,z11,z2,z1344,z4,z5]),(0,[z20,z335,z1,z11,z114,z5]),(1,[z89,z1,z2,z4,z5]),(0,[z892,z1,z11,z4,z5,z49])],[(0,[z1,z11,z2,z12,z1345,z5]),(0,[z1,z11,z1346,z12,z4,z5]),(1,[z437,z1,z11,z4,z5]),(0,[z1,z1347,z2,z12,z4,z5]),(0,[z112,z0,z1,z2,z4,z5]),(0,[z1,z1335,z11,z12,z4,z5])],[(0,[z422,z298,z11,z4,z5,z49]),(0,[z1348,z1,z11,z2,z4,z5]),(0,[z1,z134,z2,z12,z4,z1273]),(0,[z112,z122,z1,z11,z4,z5])],[(0,[z1,z1349,z2,z12,z4,z5]),(0,[z1,z11,z257,z626,z4,z5]),(0,[z39,z1,z11,z19,z4,z5]),(0,[z159,z1,z11,z12,z4,z77]),(0,[z1350,z53,z1,z2,z4,z5])],[(0,[z26,z1351,z1,z2,z4,z5]),(0,[z1,z11,z229,z4,z5,z49]),(0,[z1,z2,z321,z12,z4,z5])],[(0,[z1,z2,z12,z4,z1352,z5]),(0,[z1,z11,z1353,z12,z4,z5]),(0,[z53,z1,z2,z198,z4,z5]),(0,[z82,z11,z2,z894,z59,z5])],[(0,[z1,z11,z2,z169,z4,z5])],[(0,[z14,z1,z363,z2,z4,z5])],[(0,[z1354,z1,z11,z12,z4,z5]),(0,[z350,z11,z2,z12,z562,z5])],[(0,[z1355,z11,z2,z12,z4,z5]),(0,[z1166,z11,z10,z2,z4,z5]),(0,[z1,z2,z12,z4,z1356,z5])],[(0,[z26,z1,z602,z2,z4,z5]),(0,[z122,z422,z1,z11,z4,z5]),(0,[z1,z2,z12,z4,z5,z1200]),(0,[z26,z24,z1,z220,z4,z5])],[(0,[z1,z205,z2,z12,z4,z5]),(0,[z26,z1,z1357,z2,z4,z5]),(0,[z1,z11,z2,z12,z4,z1358]),(0,[z79,z1,z292,z11,z4,z5]),(0,[z26,z862,z1,z11,z4,z5]),(0,[z26,z1,z2,z392,z4,z5]),(0,[z1,z351,z2,z435,z4,z5])],[(0,[z252,z1359,z2,z12,z4,z5]),(0,[z1360,z96,z2,z12,z4,z5]),(0,[z1,z1361,z2,z12,z4,z5]),(0,[z1362,z1,z11,z2,z463,z5]),(0,[z1,z21,z11,z10,z4,z5]),(0,[z122,z1,z11,z111,z4,z5]),(0,[z159,z1,z11,z12,z4,z443])],[(0,[z275,z11,z2,z12,z4,z60]),(0,[z26,z1,z21,z11,z4,z5]),(0,[z20,z1,z11,z1363,z4,z5]),(0,[z704,z53,z1,z2,z4,z5]),(0,[z0,z1,z10,z2,z4,z5])],[(0,[z20,z1,z11,z4,z1364,z5]),(0,[z79,z11,z2,z248,z4,z5]),(1,[z11,z2,z12,z413,z60]),(0,[z1,z100,z11,z2,z391,z5]),(0,[z350,z11,z2,z435,z4,z5])],[(0,[z74,z6,z2,z12,z4,z5]),(0,[z9,z132,z2,z198,z4,z5]),(0,[z26,z1,z210,z12,z4,z5]),(0,[z1,z100,z357,z2,z4,z5])],[(0,[z24,z1,z2,z514,z4,z5]),(0,[z1,z11,z12,z1365,z114,z5]),(0,[z0,z122,z1,z4,z5,z49])],[(0,[z20,z1,z11,z38,z4,z5]),(0,[z1,z18,z2,z12,z395,z5]),(0,[z1,z11,z1366,z2,z4,z5]),(1,[z160,z1,z2,z4,z5])],[(0,[z1,z11,z2,z4,z49,z1367]),(0,[z1,z11,z2,z1368,z4,z49]),(0,[z1,z11,z2,z4,z1369,z5]),(0,[z125,z1,z1010,z2,z4,z5]),(0,[z752,z1,z11,z2,z4,z5])],[(0,[z1,z11,z2,z479,z4,z5]),(0,[z318,z39,z1,z11,z4,z5]),(0,[z216,z363,z2,z12,z4,z5])],[(0,[z252,z96,z2,z12,z4,z5]),(0,[z9,z1,z2,z248,z4,z5]),(0,[z1370,z1,z11,z2,z4,z5]),(0,[z1,z11,z1371,z2,z4,z5])],[(0,[z20,z1372,z1,z11,z4,z5]),(0,[z275,z27,z2,z12,z4,z60]),(0,[z1373,z1,z11,z2,z4,z5]),(0,[z26,z1,z11,z240,z4,z5]),(0,[z136,z1,z11,z4,z66,z5]),(0,[z20,z25,z11,z2,z4,z5])],[(0,[z14,z1,z45,z2,z4,z5]),(0,[z122,z1,z11,z4,z5,z387])],[(1,[z568,z1,z11,z4,z5]),(0,[z1,z11,z4,z5,z35,z365])],[(0,[z0,z1,z18,z2,z4,z5]),(0,[z1,z1374,z2,z12,z4,z5])],[(0,[z79,z572,z11,z2,z4,z5]),(0,[z1,z11,z12,z4,z1375,z5])],[],[(0,[z1,z11,z2,z4,z1376,z5]),(0,[z1377,z1,z11,z2,z4,z5]),(0,[z14,z1,z11,z1176,z4,z5])]],
   [[(0,[z1378,z11,z2,z12,z4,z75]),(0,[z151,z1,z186,z137,z4,z5]),(0,[z1219,z1,z357,z2,z4,z5])],[(0,[z9,z1,z2,z12,z4,z5]),(0,[z1,z11,z2,z12,z1379,z5]),(0,[z1,z100,z210,z221,z4,z5]),(0,[z335,z1,z11,z114,z5,z49])],[],[(0,[z159,z1,z11,z530,z4,z5]),(0,[z1,z11,z141,z4,z5,z49]),(0,[z1,z11,z4,z5,z1380,z222]),(0,[z1,z933,z11,z4,z5,z49])],[(0,[z1381,z1,z11,z2,z4,z5]),(0,[z26,z401,z1,z2,z4,z5]),(0,[z125,z1,z2,z137,z4,z5])],[(0,[z1382,z1,z11,z2,z12,z5])],[(0,[z1,z186,z172,z12,z4,z5]),(0,[z1,z11,z583,z229,z4,z5]),(0,[z1,z11,z2,z4,z1383,z5]),(0,[z0,z1,z2,z4,z5,z387]),(0,[z1,z11,z4,z5,z130,z49]),(0,[z1,z11,z194,z4,z5,z49])],[(0,[z20,z1,z11,z1258,z4,z5]),(0,[z759,z1,z11,z2,z4,z5]),(0,[z1,z11,z220,z54,z4,z5]),(0,[z153,z11,z2,z4,z5,z49]),(0,[z122,z372,z1,z11,z4,z5]),(0,[z216,z11,z2,z288,z4,z5])],[(0,[z11,z2,z12,z4,z230,z60]),(0,[z1,z11,z2,z1384,z4,z5]),(0,[z1,z1385,z2,z12,z4,z5]),(0,[z304,z1,z11,z118,z12,z61])],[(0,[z1,z11,z2,z1386,z4,z5]),(0,[z1,z100,z11,z4,z203,z5])],[(0,[z1387,z11,z108,z12,z4,z5]),(0,[z1,z11,z2,z1388,z4,z5]),(0,[z20,z1,z11,z1389,z4,z5]),(0,[z14,z488,z1,z11,z4,z5])],[(0,[z1,z11,z961,z464,z4,z5]),(0,[z1343,z1,z2,z12,z4,z101]),(0,[z151,z53,z1,z2,z4,z5]),(0,[z1390,z1,z11,z2,z4,z5])],[(0,[z14,z1,z11,z38,z4,z5]),(0,[z1,z2,z12,z4,z5,z1085])],[(0,[z252,z20,z96,z2,z4,z5]),(0,[z26,z1359,z1,z2,z4,z5]),(0,[z0,z1,z11,z2,z4,z5]),(0,[z53,z1,z871,z2,z4,z5]),(0,[z1,z11,z12,z4,z722,z5])],[(1,[z151,z1,z137,z4,z5]),(0,[z1,z11,z2,z1391,z4,z5]),(0,[z1392,z1,z11,z2,z376,z5])],[(0,[z1,z63,z11,z2,z4,z5]),(0,[z125,z1,z2,z4,z71,z5]),(0,[z55,z100,z11,z2,z4,z5]),(0,[z409,z20,z1,z11,z4,z5])],[(0,[z1,z100,z11,z2,z413,z5]),(0,[z1,z186,z12,z4,z834,z5]),(0,[z304,z216,z11,z2,z12,z61])],[(0,[z1,z1393,z2,z12,z4,z5]),(0,[z1,z11,z43,z4,z5,z130])],[(0,[z122,z1,z11,z2,z4,z5]),(0,[z1,z1394,z2,z12,z4,z5])],[(0,[z0,z1,z2,z4,z75,z5]),(0,[z1395,z1,z11,z2,z4,z5]),(0,[z1,z2,z4,z71,z5,z135]),(0,[z276,z0,z1,z2,z4,z5])],[(0,[z20,z1,z11,z993,z4,z5]),(0,[z1,z11,z1396,z12,z4,z5]),(0,[z132,z259,z2,z198,z4,z5]),(0,[z82,z1084,z11,z2,z59,z5]),(0,[z1,z11,z2,z1397,z4,z5]),(0,[z151,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z1398,z4,z5]),(0,[z276,z122,z1,z11,z4,z5])],[(0,[z26,z1,z1399,z2,z4,z5]),(0,[z547,z1,z11,z2,z4,z5]),(0,[z1,z11,z1400,z2,z4,z5]),(0,[z521,z0,z1,z2,z4,z5]),(0,[z85,z1,z2,z4,z37,z5])],[(0,[z1401,z1,z11,z2,z4,z5]),(0,[z526,z1,z11,z4,z71,z5]),(0,[z1,z1402,z11,z2,z4,z5]),(0,[z1,z1403,z2,z12,z4,z5]),(1,[z1,z11,z12,z722,z5])],[(0,[z159,z26,z24,z1,z4,z5]),(0,[z39,z1,z11,z4,z1404,z5]),(0,[z1405,z53,z1,z2,z4,z5])],[(0,[z1,z11,z2,z12,z1406,z5]),(0,[z1,z11,z2,z1407,z4,z5]),(0,[z26,z1,z11,z154,z4,z5])],[(0,[z11,z2,z12,z413,z5,z60]),(0,[z26,z1,z11,z4,z5,z130]),(0,[z20,z1,z11,z940,z4,z5])],[(0,[z568,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z12,z1408,z5]),(0,[z195,z9,z1,z2,z4,z5])],[(0,[z1,z1409,z11,z2,z4,z5]),(0,[z1,z106,z2,z12,z4,z5]),(0,[z163,z1,z63,z12,z4,z5]),(0,[z1,z10,z2,z147,z4,z5])],[(0,[z1,z58,z38,z12,z4,z5]),(0,[z122,z1,z11,z386,z4,z5])],[(0,[z0,z1,z2,z4,z1410,z5])],[(0,[z1,z11,z2,z894,z4,z200]),(0,[z53,z1,z186,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z648])],[]],
   [[(0,[z26,z1,z1411,z2,z4,z5]),(0,[z26,z24,z1,z4,z114,z5]),(0,[z1,z363,z2,z12,z5,z61])],[(0,[z1412,z26,z1,z2,z4,z5]),(0,[z159,z1,z11,z12,z4,z380]),(0,[z1,z11,z2,z4,z5,z1413]),(0,[z1,z1414,z11,z12,z4,z5]),(0,[z53,z1,z2,z4,z5,z101])],[],[(0,[z486,z100,z11,z108,z4,z5]),(0,[z1,z12,z4,z5,z130,z48])],[(0,[z1,z622,z2,z12,z4,z5]),(0,[z1,z1415,z11,z12,z4,z5]),(0,[z1416,z1,z11,z2,z4,z5]),(0,[z20,z1,z11,z4,z440,z5]),(0,[z20,z24,z163,z1,z4,z5]),(0,[z26,z1,z2,z210,z4,z5])],[(0,[z1417,z1,z11,z12,z4,z5])],[(0,[z1,z1418,z2,z12,z4,z5]),(0,[z26,z1,z2,z1368,z4,z5]),(0,[z1,z100,z134,z2,z4,z180])],[(0,[z20,z486,z11,z108,z4,z5]),(0,[z1419,z20,z1,z11,z4,z5]),(0,[z1,z11,z1420,z12,z4,z5]),(0,[z1,z11,z188,z4,z5,z49]),(0,[z1201,z1,z134,z2,z4,z180]),(0,[z159,z1,z12,z4,z367,z218]),(0,[z1,z1421,z11,z2,z4,z5])],[(0,[z39,z1,z186,z11,z4,z5])],[(0,[z26,z1,z205,z2,z4,z5]),(0,[z1,z11,z459,z4,z130,z49])],[(0,[z1,z117,z11,z12,z426,z5]),(0,[z53,z802,z1,z2,z4,z5]),(0,[z350,z11,z10,z2,z4,z5]),(0,[z14,z477,z1,z11,z4,z5])],[(0,[z298,z1,z11,z4,z5,z77]),(0,[z82,z11,z188,z12,z59,z5]),(0,[z1,z1422,z11,z2,z4,z5]),(0,[z153,z11,z2,z12,z307,z5])],[(0,[z1,z2,z12,z4,z1423,z5]),(0,[z1,z11,z2,z459,z4,z135]),(0,[z1,z11,z2,z1424,z4,z5])],[],[(0,[z1,z11,z2,z12,z1425,z5]),(0,[z26,z1,z11,z196,z4,z5]),(0,[z26,z24,z298,z1,z4,z5]),(0,[z1,z11,z2,z4,z1426,z5]),(0,[z1,z100,z11,z1427,z4,z5]),(0,[z1428,z0,z1,z2,z4,z5])],[(0,[z1,z100,z2,z1429,z4,z5])],[(0,[z1,z11,z2,z1430,z4,z5]),(0,[z1,z1238,z206,z2,z4,z5]),(1,[z0,z122,z1,z4,z5])],[(0,[z150,z1,z11,z12,z4,z5]),(0,[z11,z2,z12,z4,z5,z230]),(0,[z1,z11,z10,z2,z167,z5])],[(0,[z1,z11,z2,z1431,z4,z5]),(0,[z1,z186,z11,z320,z4,z5]),(0,[z1,z11,z2,z241,z4,z5]),(0,[z1,z2,z221,z12,z307,z5])],[(0,[z1432,z30,z2,z12,z4,z5]),(0,[z638,z1,z11,z12,z4,z5]),(0,[z122,z1,z11,z333,z4,z5]),(0,[z1,z11,z2,z233,z4,z5]),(0,[z1,z11,z1371,z154,z4,z5]),(0,[z1,z357,z2,z12,z562,z5])],[(0,[z1,z11,z2,z1433,z4,z5]),(0,[z1,z11,z2,z4,z202,z5])],[(0,[z1,z11,z2,z12,z1434,z5]),(0,[z1,z11,z2,z1435,z4,z5]),(0,[z1,z11,z2,z4,z5,z1436]),(0,[z1,z18,z2,z12,z1437,z5]),(0,[z1,z141,z12,z4,z5,z101]),(0,[z1,z11,z1438,z12,z4,z5])],[(0,[z1343,z26,z1,z2,z4,z5]),(0,[z14,z1,z2,z321,z4,z5])],[(0,[z1,z11,z2,z1439,z4,z5]),(0,[z1440,z1,z11,z2,z4,z5]),(0,[z79,z122,z1,z11,z4,z5]),(0,[z1006,z1,z11,z2,z4,z5]),(0,[z1,z11,z220,z4,z5,z218]),(0,[z26,z1,z2,z4,z384,z5]),(0,[z1,z100,z11,z4,z481,z5]),(0,[z1,z11,z2,z4,z1441,z5]),(0,[z1,z11,z2,z338,z37,z49])],[(0,[z26,z1,z2,z146,z4,z5])],[(0,[z1,z11,z2,z1442,z4,z5]),(0,[z1443,z11,z2,z12,z4,z60]),(0,[z1,z11,z2,z12,z1208,z5]),(0,[z1,z357,z2,z435,z4,z5])],[(0,[z1444,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z1445,z4,z5]),(0,[z224,z1,z11,z10,z4,z5]),(0,[z318,z329,z1,z2,z71,z5])],[(0,[z252,z26,z96,z2,z4,z5]),(0,[z14,z24,z163,z1,z4,z5]),(0,[z39,z39,z1,z11,z4,z5])],[(0,[z486,z11,z10,z108,z4,z5]),(0,[z1167,z1,z11,z2,z4,z5]),(0,[z1,z11,z235,z4,z5,z49])],[(0,[z1,z6,z10,z2,z4,z5]),(0,[z275,z11,z257,z12,z4,z60]),(0,[z40,z1,z11,z2,z4,z522]),(0,[z1,z11,z43,z2,z4,z770]),(0,[z947,z1,z2,z4,z5,z367])],[(0,[z14,z486,z11,z108,z4,z5]),(0,[z26,z1,z2,z943,z4,z5]),(0,[z1,z11,z2,z626,z413,z5]),(0,[z159,z1,z357,z12,z4,z218]),(0,[z195,z0,z1,z2,z4,z5])],[(0,[z1,z11,z2,z1446,z4,z5]),(0,[z1,z186,z357,z12,z4,z5]),(0,[z1,z11,z320,z65,z4,z5]),(0,[z195,z122,z1,z11,z4,z5])]],
   [[(0,[z1447,z1,z11,z2,z4,z5]),(0,[z40,z20,z163,z1,z4,z5]),(0,[z53,z1,z100,z2,z4,z5]),(0,[z1,z351,z2,z12,z84,z5])],[(0,[z1,z209,z134,z2,z4,z180]),(0,[z695,z53,z1,z2,z4,z5])],[(0,[z1,z11,z2,z12,z173,z5]),(0,[z1,z1448,z11,z12,z4,z5]),(0,[z1,z1132,z11,z2,z4,z5]),(0,[z20,z1,z2,z4,z5,z1085])],[(0,[z53,z29,z1,z2,z4,z5]),(0,[z83,z1,z11,z4,z178,z5]),(0,[z1449,z1,z186,z137,z4,z5]),(0,[z1,z186,z137,z4,z5,z49])],[(0,[z53,z1,z2,z137,z4,z5]),(0,[z1,z11,z2,z4,z5,z1450]),(0,[z1100,z11,z2,z12,z4,z5])],[(0,[z1,z11,z2,z583,z4,z5]),(0,[z1,z11,z2,z12,z1451,z5]),(0,[z74,z205,z2,z12,z4,z5]),(0,[z1,z11,z2,z1452,z4,z5])],[(0,[z1,z11,z4,z1209,z481,z5]),(0,[z1,z11,z2,z1453,z4,z5])],[(0,[z1,z11,z2,z1454,z4,z5]),(0,[z1455,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z1456,z4,z5]),(0,[z0,z1,z2,z4,z5,z61]),(0,[z122,z1,z1457,z11,z4,z5])],[(0,[z74,z11,z2,z12,z4,z75]),(0,[z1458,z1,z11,z2,z4,z5]),(0,[z123,z11,z2,z12,z4,z37])],[(0,[z26,z1,z2,z1459,z4,z5]),(0,[z122,z1,z11,z221,z4,z5]),(0,[z20,z1,z287,z2,z4,z5]),(0,[z0,z1,z11,z4,z5,z130])],[(0,[z39,z1,z100,z11,z4,z5]),(0,[z1,z1460,z2,z12,z4,z5])],[(0,[z1461,z1,z11,z2,z4,z5]),(0,[z11,z2,z12,z4,z59,z200]),(0,[z556,z1,z11,z2,z4,z5]),(0,[z521,z39,z1,z11,z4,z5]),(0,[z14,z1462,z1,z2,z4,z5])],[],[(0,[z39,z29,z1,z11,z4,z5]),(0,[z1,z11,z2,z12,z4,z1463]),(0,[z1,z11,z2,z4,z1464,z5]),(0,[z304,z1,z100,z11,z2,z61])],[(0,[z774,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z67]),(0,[z122,z1,z11,z4,z5,z130])],[(0,[z846,z1,z11,z2,z4,z5]),(0,[z1465,z1,z11,z2,z4,z5]),(0,[z53,z1,z2,z4,z71,z5]),(0,[z1,z11,z2,z1466,z4,z49]),(0,[z1,z363,z10,z2,z4,z5])],[(0,[z1467,z1,z11,z2,z4,z5]),(0,[z20,z163,z1,z11,z4,z5]),(0,[z1468,z1,z11,z2,z4,z5])],[(0,[z53,z1,z2,z108,z4,z5]),(0,[z1,z1469,z2,z12,z4,z5])],[(0,[z82,z11,z2,z264,z59,z5]),(0,[z1470,z783,z11,z2,z4,z5])],[(0,[z1,z11,z196,z289,z4,z5]),(0,[z1471,z1,z2,z12,z4,z5]),(0,[z26,z1,z2,z4,z1225,z5]),(0,[z1,z134,z2,z4,z180,z222]),(0,[z1,z937,z2,z12,z4,z5])],[(0,[z1,z106,z12,z4,z114,z5])],[(0,[z11,z2,z12,z311,z4,z5]),(0,[z26,z1,z11,z2,z4,z189]),(0,[z39,z1,z11,z4,z5,z522]),(0,[z39,z1,z11,z459,z4,z5]),(0,[z1472,z1,z2,z12,z71,z5]),(0,[z153,z134,z2,z12,z4,z5])],[(0,[z1417,z1,z100,z11,z4,z5]),(0,[z20,z1,z254,z11,z4,z5]),(0,[z1,z11,z54,z169,z4,z5]),(0,[z1,z11,z2,z1473,z4,z5]),(0,[z1,z11,z2,z4,z5,z86])],[(0,[z1449,z1,z11,z2,z4,z5])],[],[(0,[z1,z11,z2,z1474,z4,z5]),(0,[z24,z1,z12,z4,z314,z5]),(0,[z810,z8,z11,z2,z4,z5]),(0,[z1,z11,z10,z65,z4,z66])],[(0,[z1,z30,z2,z514,z4,z5]),(0,[z1,z11,z2,z4,z1475,z5]),(0,[z1,z11,z2,z1476,z4,z5])],[(1,[z97,z2,z12,z4,z5]),(0,[z1,z1477,z11,z2,z4,z5]),(0,[z153,z11,z141,z12,z4,z5]),(0,[z20,z1,z11,z338,z114,z5]),(0,[z1,z11,z65,z12,z4,z443]),(0,[z1462,z1,z2,z12,z4,z5])],[(0,[z298,z1,z206,z12,z4,z5]),(0,[z20,z1,z2,z4,z706,z5]),(0,[z25,z11,z2,z12,z562,z5]),(0,[z159,z1,z206,z12,z4,z218])],[(0,[z1,z11,z188,z894,z4,z5]),(0,[z1,z11,z10,z235,z4,z5]),(0,[z1,z11,z12,z4,z5,z294]),(0,[z1,z11,z1427,z12,z4,z5]),(0,[z1,z2,z4,z5,z49,z1046])],[(0,[z810,z39,z1,z11,z4,z5])],[(0,[z1,z11,z993,z108,z4,z5]),(0,[z526,z1,z11,z12,z4,z5]),(0,[z89,z1,z2,z4,z5,z67])]],
   [[(0,[z1,z11,z188,z12,z4,z200]),(0,[z1,z11,z2,z4,z1478,z5]),(0,[z1479,z1,z2,z12,z4,z5]),(0,[z14,z1,z287,z2,z4,z5])],[(0,[z26,z1,z705,z2,z4,z5]),(0,[z1,z2,z4,z278,z5,z49]),(0,[z1480,z122,z1,z11,z4,z5]),(0,[z122,z1481,z1,z11,z4,z5])],[(0,[z1,z11,z2,z1482,z4,z5]),(0,[z1,z11,z2,z1483,z4,z5]),(0,[z650,z11,z2,z12,z59,z5]),(0,[z25,z11,z2,z435,z4,z5])],[(0,[z1,z11,z140,z12,z4,z5]),(0,[z1,z11,z2,z1258,z4,z5]),(0,[z1,z11,z54,z479,z4,z5]),(0,[z26,z1,z357,z2,z4,z5]),(0,[z1,z11,z2,z1484,z4,z5])],[(0,[z1,z18,z2,z12,z1485,z5]),(0,[z1,z1188,z11,z2,z4,z5]),(0,[z1,z100,z11,z118,z4,z5]),(0,[z20,z1,z11,z2,z338,z37]),(0,[z1150,z11,z2,z12,z4,z5])],[(0,[z216,z287,z2,z12,z4,z5])],[(0,[z74,z11,z2,z12,z4,z1486]),(0,[z1,z11,z2,z4,z1487,z49]),(0,[z1,z63,z11,z4,z66,z5])],[(0,[z1,z11,z1488,z12,z4,z5]),(0,[z275,z53,z1,z2,z4,z5]),(0,[z26,z24,z1,z117,z4,z5]),(0,[z14,z1,z11,z4,z5,z450]),(0,[z190,z1,z2,z4,z202,z5])],[(0,[z20,z199,z11,z2,z333,z5])],[(0,[z26,z1,z2,z4,z5,z1489]),(0,[z20,z1,z11,z553,z4,z5]),(0,[z1,z11,z2,z12,z253,z5]),(0,[z1,z11,z4,z741,z5,z450]),(0,[z1310,z11,z10,z2,z4,z5])],[(0,[z26,z1,z2,z4,z5,z1490])],[(0,[z1,z1313,z10,z2,z4,z5])],[(0,[z1,z11,z2,z4,z5,z1491]),(0,[z79,z1,z45,z2,z4,z5]),(0,[z1,z11,z1492,z2,z4,z5]),(0,[z1,z100,z11,z141,z4,z5]),(0,[z1,z11,z2,z4,z5,z1493])],[(0,[z53,z1,z2,z4,z5,z60]),(0,[z14,z1,z254,z11,z4,z5])],[],[(0,[z1,z1494,z11,z2,z4,z5])],[(0,[z419,z1,z2,z12,z71,z5]),(0,[z20,z1,z11,z1495,z4,z5])],[(0,[z1,z100,z11,z229,z4,z5]),(0,[z1496,z1,z11,z2,z4,z5])],[(0,[z1,z220,z2,z4,z180,z5]),(0,[z26,z1,z1497,z2,z4,z5]),(0,[z1,z11,z10,z4,z1498,z5])],[(0,[z1,z11,z12,z4,z5,z1499])],[(0,[z1,z11,z1500,z12,z4,z5]),(0,[z1,z11,z2,z4,z5,z1501])],[(0,[z1,z11,z1502,z12,z4,z5]),(0,[z0,z1,z2,z4,z66,z5])],[(0,[z981,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z433,z832,z5])],[(0,[z1091,z1,z11,z2,z4,z5]),(0,[z6,z2,z12,z4,z5,z60]),(0,[z1,z1503,z2,z12,z4,z5]),(0,[z1504,z11,z2,z12,z4,z5])],[(0,[z1,z11,z2,z4,z5,z1505]),(0,[z20,z1,z11,z2,z236,z5]),(0,[z1,z11,z530,z4,z114,z5]),(0,[z1,z100,z11,z17,z4,z5]),(0,[z1,z11,z2,z4,z5,z1506]),(0,[z1,z11,z2,z4,z5,z1507])],[(0,[z26,z1,z11,z4,z203,z5]),(0,[z122,z1,z18,z11,z4,z5]),(0,[z1,z11,z2,z12,z338,z37])],[(0,[z1,z58,z10,z2,z4,z5]),(0,[z20,z1,z186,z137,z4,z5]),(0,[z1,z292,z11,z12,z4,z5]),(0,[z20,z1,z11,z12,z84,z5]),(0,[z1,z11,z12,z722,z114,z5]),(0,[z579,z1,z106,z2,z4,z5])],[(0,[z1,z2,z12,z4,z5,z41]),(0,[z14,z1,z11,z2,z338,z37])],[],[(0,[z1,z11,z2,z4,z5,z1031]),(0,[z1,z11,z10,z118,z4,z5])],[(0,[z1,z11,z2,z1508,z4,z5]),(0,[z40,z26,z1,z141,z4,z5]),(0,[z1,z11,z2,z1509,z4,z5]),(0,[z1,z11,z12,z338,z481,z5]),(0,[z1,z11,z46,z433,z203,z5])],[(0,[z14,z199,z11,z2,z333,z5]),(0,[z1,z11,z4,z5,z49,z450]),(0,[z11,z2,z12,z4,z5,z1510]),(0,[z1,z2,z4,z281,z382,z5])]],
   [[(0,[z1,z11,z2,z339,z4,z5]),(0,[z20,z1511,z1,z11,z4,z5]),(0,[z1,z1512,z11,z2,z4,z5]),(0,[z1,z100,z259,z2,z4,z5]),(0,[z26,z1,z11,z2,z413,z5]),(0,[z1,z11,z2,z4,z49,z334])],[(0,[z1,z11,z2,z4,z1513,z5]),(0,[z1,z11,z2,z1514,z4,z5]),(0,[z26,z1,z206,z2,z4,z5]),(0,[z1,z126,z2,z4,z5,z101])],[(0,[z1515,z1,z11,z2,z4,z5]),(0,[z578,z1,z11,z12,z4,z218]),(0,[z1,z206,z100,z2,z4,z5]),(0,[z1,z1516,z2,z12,z4,z5]),(0,[z122,z1,z11,z46,z4,z5]),(0,[z1,z11,z12,z4,z1266,z5])],[(0,[z1,z11,z235,z642,z4,z5]),(0,[z24,z163,z1,z12,z4,z5]),(0,[z40,z1,z2,z183,z4,z5])],[(0,[z1,z1517,z11,z12,z4,z5]),(0,[z1,z206,z108,z12,z4,z5]),(0,[z1,z11,z2,z1518,z4,z5]),(0,[z20,z1,z11,z1254,z4,z5]),(0,[z53,z1,z2,z523,z4,z5])],[(0,[z1,z11,z2,z264,z4,z5]),(0,[z1,z11,z1519,z2,z4,z5]),(0,[z1,z11,z10,z141,z4,z5]),(0,[z40,z1,z254,z12,z4,z5]),(0,[z20,z53,z1,z2,z4,z5])],[(0,[z1,z11,z2,z1520,z4,z5]),(0,[z1,z11,z4,z1375,z5,z49])],[(0,[z1,z11,z2,z1521,z4,z5]),(0,[z1,z11,z2,z264,z4,z200]),(0,[z1249,z1,z11,z2,z4,z5])],[(0,[z1,z2,z12,z4,z1522,z5]),(0,[z1523,z1,z11,z2,z4,z5]),(0,[z26,z302,z11,z2,z4,z5]),(0,[z1524,z39,z1,z11,z4,z5]),(0,[z1,z357,z65,z12,z4,z5]),(0,[z1,z363,z2,z288,z4,z5])],[(0,[z1525,z1,z11,z2,z4,z5]),(0,[z24,z1,z254,z12,z4,z5])],[(0,[z1,z1526,z100,z2,z4,z5]),(0,[z1,z11,z2,z4,z5,z1527]),(0,[z1,z357,z2,z12,z84,z5])],[(0,[z1,z11,z2,z1528,z4,z5]),(0,[z1,z186,z73,z12,z4,z5]),(0,[z159,z39,z1,z11,z4,z5]),(0,[z20,z1,z18,z2,z19,z5])],[(0,[z1,z11,z583,z54,z4,z5]),(0,[z558,z1,z11,z12,z4,z218]),(0,[z26,z1,z2,z4,z1529,z5])],[(0,[z1,z11,z2,z12,z236,z5]),(1,[z699,z1,z2,z4,z5]),(1,[z26,z1,z141,z4,z5]),(0,[z0,z1,z2,z433,z4,z5])],[(0,[z20,z1,z11,z2,z4,z5]),(0,[z1,z11,z2,z12,z402,z5]),(0,[z151,z1,z137,z12,z4,z5]),(0,[z1,z11,z146,z210,z4,z5])],[(0,[z53,z1,z2,z248,z4,z5]),(0,[z1,z205,z10,z2,z4,z5]),(0,[z11,z2,z12,z4,z413,z60]),(0,[z14,z1,z11,z2,z236,z5]),(0,[z1,z11,z2,z12,z4,z230]),(0,[z1,z11,z2,z12,z1530,z37]),(0,[z1531,z1,z11,z12,z4,z5])],[(0,[z1,z11,z12,z4,z5,z1380]),(0,[z1,z11,z2,z4,z5,z1532])],[(0,[z1,z11,z2,z4,z1533,z5]),(0,[z275,z11,z10,z2,z4,z60]),(0,[z14,z1,z186,z137,z4,z5]),(0,[z26,z20,z1,z137,z4,z5]),(0,[z20,z1,z137,z4,z5,z101]),(0,[z1,z11,z2,z1534,z4,z5])],[(0,[z1,z254,z30,z12,z4,z5]),(0,[z1,z205,z2,z12,z413,z5]),(0,[z335,z1,z100,z11,z114,z5]),(0,[z195,z1,z11,z2,z376,z5])],[(0,[z1,z11,z2,z4,z5,z1535]),(0,[z40,z1,z2,z12,z4,z135]),(0,[z1,z45,z10,z2,z4,z5])],[(0,[z1,z11,z2,z894,z4,z189]),(0,[z275,z11,z2,z12,z413,z60]),(0,[z20,z510,z1,z11,z4,z5]),(0,[z1,z11,z2,z4,z5,z1536])],[(0,[z224,z1,z11,z433,z4,z5]),(0,[z1,z11,z2,z12,z413,z75]),(1,[z1,z2,z12,z253,z5]),(0,[z1,z18,z2,z183,z4,z5]),(0,[z1,z11,z2,z142,z307,z5])],[(0,[z26,z1,z134,z2,z4,z180]),(0,[z20,z55,z11,z2,z4,z5]),(0,[z1,z11,z2,z1537,z4,z5]),(0,[z216,z11,z118,z12,z4,z5])],[(0,[z691,z1,z11,z4,z114,z5]),(0,[z1538,z1,z11,z12,z114,z5])],[(0,[z252,z96,z10,z2,z4,z5]),(0,[z53,z1,z2,z12,z4,z5]),(0,[z20,z1,z11,z833,z4,z5]),(0,[z1,z18,z2,z12,z253,z5]),(0,[z20,z1,z11,z208,z4,z5])],[(0,[z1,z11,z2,z1539,z4,z5]),(0,[z122,z1,z11,z392,z4,z5]),(0,[z1,z63,z2,z4,z5,z101]),(0,[z20,z53,z1,z10,z4,z5])],[(0,[z40,z151,z1,z2,z4,z5]),(1,[z190,z1,z2,z4,z5])],[(0,[z26,z1,z137,z4,z5,z218]),(0,[z1,z11,z2,z1540,z4,z5])],[(0,[z82,z20,z11,z2,z59,z5]),(0,[z1,z11,z2,z4,z1541,z5]),(0,[z1,z1542,z11,z2,z4,z5]),(0,[z14,z53,z1,z2,z4,z5])],[(0,[z1,z11,z2,z1543,z4,z5]),(0,[z122,z1,z11,z4,z37,z5])],[(0,[z53,z163,z1,z2,z4,z5])],[(0,[z11,z2,z12,z4,z5,z796])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z39,z55,z11,z4,z5]),(0,[z39,z1,z11,z391,z5]),(0,[z20,z25,z351,z4,z5])],[(0,[z1544,z1,z2,z4,z5]),(0,[z1545,z1,z2,z4,z5]),(0,[z20,z1,z1546,z4,z5]),(0,[z578,z1,z11,z4,z77]),(0,[z53,z1,z2,z555,z5]),(0,[z1327,z1,z11,z938,z5])],[(0,[z224,z1,z45,z4,z5]),(0,[z526,z1,z11,z4,z5]),(0,[z1,z63,z1546,z4,z5]),(0,[z1,z12,z481,z253,z5]),(0,[z20,z1,z11,z722,z5]),(0,[z0,z1,z4,z1375,z5])],[(0,[z39,z74,z11,z4,z75]),(0,[z838,z163,z1,z4,z5]),(0,[z1547,z11,z2,z4,z5]),(0,[z125,z1,z2,z4,z41]),(0,[z1548,z1,z2,z4,z5])],[(0,[z9,z1,z2,z470,z5]),(0,[z11,z188,z12,z59,z200]),(0,[z0,z1,z2,z4,z200]),(0,[z1549,z1,z235,z4,z5]),(0,[z1550,z1,z11,z4,z5]),(0,[z1,z287,z2,z12,z268])],[(0,[z1551,z1,z2,z4,z5]),(0,[z122,z1,z263,z4,z5]),(0,[z1,z11,z435,z4,z443])],[(0,[z11,z2,z12,z59,z200]),(0,[z1552,z1,z11,z4,z5]),(0,[z53,z199,z2,z333,z5]),(0,[z1,z220,z508,z4,z5]),(0,[z125,z1,z2,z307,z5]),(0,[z1271,z1,z11,z1404,z5]),(0,[z1,z11,z4,z5,z1553]),(0,[z1,z12,z4,z1554,z443]),(0,[z1,z11,z2,z1555,z5])],[(0,[z317,z298,z1,z4,z5]),(0,[z53,z1,z2,z236,z5])]],
   [[(0,[z26,z153,z2,z4,z5]),(0,[z1556,z1,z11,z4,z5]),(0,[z20,z1,z4,z5,z1557]),(0,[z53,z1,z2,z402,z5]),(0,[z25,z11,z12,z4,z443])],[(0,[z1558,z1,z2,z4,z5]),(0,[z185,z1,z171,z4,z5]),(0,[z1035,z1,z2,z4,z858]),(0,[z122,z1,z4,z382,z5]),(0,[z0,z1,z1559,z4,z5])],[(0,[z14,z11,z2,z413,z60]),(0,[z1,z2,z1560,z4,z5]),(0,[z1561,z1,z11,z4,z5]),(0,[z965,z122,z1,z11,z5])],[(0,[z1562,z1,z11,z4,z5]),(0,[z39,z9,z1,z4,z5]),(0,[z151,z1,z833,z4,z5]),(0,[z26,z185,z1,z4,z5]),(0,[z1,z154,z12,z4,z41]),(0,[z53,z1,z2,z167,z5]),(0,[z159,z1,z357,z4,z77]),(0,[z1,z11,z1563,z4,z5])],[(0,[z1564,z1,z2,z4,z5]),(0,[z53,z1,z257,z4,z5]),(0,[z62,z1,z4,z5,z1200]),(0,[z1,z141,z4,z5,z135]),(0,[z1,z11,z10,z722,z5]),(0,[z1565,z1,z194,z4,z5])],[(0,[z83,z1,z11,z4,z5]),(0,[z1566,z1,z11,z4,z5]),(0,[z39,z1,z134,z4,z180]),(0,[z1,z11,z320,z4,z77]),(0,[z1,z117,z11,z956,z5]),(0,[z1,z11,z65,z4,z1567])],[(0,[z568,z29,z30,z4,z5]),(0,[z150,z100,z11,z4,z5]),(0,[z122,z55,z11,z4,z5])],[(0,[z159,z1,z11,z4,z1212]),(0,[z0,z1,z4,z481,z5]),(0,[z1,z11,z1568,z4,z443]),(0,[z1480,z1457,z11,z4,z5])]],
   [[(0,[z568,z1,z11,z4,z5]),(0,[z568,z1,z259,z4,z5]),(0,[z0,z74,z2,z4,z75]),(0,[z26,z1,z1321,z4,z5]),(0,[z39,z25,z11,z4,z5])],[(0,[z1569,z1,z11,z4,z5]),(0,[z11,z229,z311,z4,z5]),(0,[z122,z74,z11,z4,z75]),(0,[z1,z2,z12,z4,z41]),(0,[z752,z1,z11,z4,z5]),(0,[z1,z11,z4,z661,z443]),(0,[z1,z11,z4,z67,z443])],[(0,[z1570,z1,z2,z4,z5]),(0,[z1571,z1,z11,z4,z5]),(0,[z40,z1,z2,z4,z858]),(0,[z437,z1,z134,z4,z180])],[(0,[z185,z1,z479,z4,z5]),(0,[z24,z1,z416,z4,z5]),(0,[z39,z123,z11,z4,z5]),(0,[z11,z2,z4,z5,z1572])],[(0,[z1573,z1,z2,z4,z5]),(0,[z100,z11,z2,z413,z60]),(0,[z1574,z1,z11,z4,z5]),(0,[z53,z1,z118,z4,z5])],[(0,[z50,z96,z1,z4,z5]),(0,[z263,z2,z12,z173,z5]),(0,[z1,z11,z1575,z4,z5]),(0,[z26,z55,z2,z307,z5]),(0,[z412,z1,z11,z722,z5]),(0,[z0,z1576,z1,z4,z5])],[(0,[z50,z1,z30,z4,z5]),(0,[z422,z53,z298,z4,z5]),(0,[z185,z1,z530,z4,z5]),(0,[z24,z1,z1546,z4,z5]),(0,[z1,z1577,z141,z4,z5]),(0,[z26,z1,z11,z2,z268]),(0,[z129,z1,z134,z4,z180]),(0,[z53,z1,z4,z5,z130])],[(0,[z1578,z1,z2,z4,z5]),(0,[z1579,z1,z11,z4,z5]),(0,[z11,z2,z642,z413,z60]),(0,[z40,z1,z2,z307,z135]),(0,[z122,z1,z11,z4,z334])]],
   [[(0,[z1580,z1,z2,z4,z5]),(0,[z20,z11,z2,z173,z5]),(0,[z1581,z1,z2,z4,z5]),(0,[z26,z24,z25,z4,z5]),(0,[z26,z1,z641,z4,z5])],[(0,[z1582,z1,z11,z4,z5]),(0,[z697,z486,z108,z4,z5]),(0,[z122,z9,z1,z4,z5]),(0,[z26,z1,z906,z4,z5]),(0,[z1,z2,z384,z253,z5]),(0,[z318,z526,z1,z71,z5]),(0,[z55,z2,z12,z4,z41])],[(0,[z1052,z1054,z2,z4,z5])],[(0,[z53,z1,z188,z4,z5]),(0,[z25,z11,z530,z4,z5]),(0,[z39,z1,z11,z470,z5]),(0,[z122,z1,z134,z4,z180]),(0,[z1583,z1,z2,z4,z5]),(0,[z123,z11,z118,z12,z61])],[(0,[z53,z1,z141,z4,z5]),(0,[z20,z1,z2,z4,z41]),(0,[z1,z11,z2,z4,z1584])],[(0,[z53,z1,z2,z4,z5]),(0,[z20,z1,z544,z4,z5]),(0,[z82,z11,z2,z1229,z5]),(0,[z356,z11,z2,z4,z230]),(0,[z123,z100,z11,z2,z61]),(0,[z1,z2,z3,z4,z41]),(0,[z0,z25,z2,z4,z5]),(0,[z123,z11,z2,z12,z268]),(0,[z1585,z1,z118,z4,z5])],[(0,[z153,z2,z183,z4,z5]),(0,[z122,z25,z11,z4,z5]),(0,[z53,z1,z292,z4,z5]),(0,[z0,z1,z2,z4,z528]),(0,[z0,z1,z2,z5,z389])],[(0,[z26,z393,z2,z4,z5]),(0,[z122,z1,z11,z4,z528]),(0,[z122,z1,z11,z5,z389]),(0,[z42,z1,z4,z5,z130])]],
   [[(0,[z150,z11,z12,z4,z5]),(0,[z1586,z1,z2,z4,z5]),(0,[z11,z2,z178,z173,z5]),(0,[z82,z122,z11,z59,z5]),(0,[z39,z1,z937,z4,z5]),(0,[z0,z123,z2,z4,z5])],[(0,[z53,z1,z229,z4,z5]),(0,[z1587,z1,z11,z4,z189]),(0,[z1,z126,z2,z4,z135]),(0,[z53,z1,z2,z33,z5]),(0,[z276,z1,z729,z4,z5]),(0,[z122,z123,z11,z4,z5]),(0,[z1588,z1,z363,z4,z5]),(0,[z1,z11,z2,z288,z268])],[(0,[z20,z25,z357,z4,z5]),(0,[z1101,z1,z45,z4,z5])],[(0,[z20,z97,z2,z4,z5]),(0,[z151,z1,z137,z4,z5]),(0,[z1,z12,z4,z450,z41])],[(0,[z150,z11,z7,z4,z5]),(0,[z1589,z1,z11,z4,z5]),(0,[z1590,z1,z2,z4,z5]),(0,[z39,z742,z11,z4,z5]),(0,[z1,z254,z126,z4,z5]),(0,[z159,z1,z11,z84,z77]),(0,[z159,z0,z1,z4,z218])],[(0,[z219,z1,z2,z4,z5]),(0,[z1591,z1,z2,z4,z5]),(0,[z810,z11,z2,z470,z5]),(0,[z39,z1,z11,z307,z5])],[(0,[z150,z246,z12,z4,z5]),(0,[z42,z1,z2,z4,z5]),(0,[z1,z11,z530,z84,z5]),(0,[z26,z1,z2,z253,z5]),(0,[z1592,z1,z2,z4,z5]),(0,[z0,z1,z4,z5,z807])],[(0,[z1593,z1,z11,z4,z5]),(0,[z11,z2,z59,z200,z49]),(0,[z0,z39,z1,z4,z5]),(0,[z20,z25,z11,z562,z5]),(0,[z1,z11,z169,z4,z443]),(0,[z123,z363,z2,z12,z61])]],
   [[(0,[z151,z1,z607,z4,z5]),(0,[z26,z1,z2,z391,z5])],[(0,[z1594,z1,z2,z4,z5]),(0,[z0,z1,z1595,z4,z5])],[(0,[z9,z232,z2,z4,z5]),(0,[z224,z11,z311,z4,z5]),(0,[z151,z401,z1,z4,z5]),(0,[z40,z1,z2,z4,z135]),(0,[z0,z564,z1,z4,z5]),(0,[z122,z1,z11,z555,z5]),(0,[z752,z1,z11,z338,z37])],[(0,[z1596,z1,z11,z4,z5]),(0,[z1134,z1,z63,z4,z5]),(0,[z1,z1597,z357,z4,z5])],[(0,[z276,z1,z137,z4,z5]),(0,[z1,z134,z2,z4,z1598]),(0,[z190,z335,z1,z114,z5])],[(0,[z26,z1124,z2,z4,z5]),(0,[z1599,z1,z11,z4,z5]),(0,[z122,z42,z1,z4,z5]),(0,[z1600,z1,z2,z4,z5]),(0,[z122,z529,z1,z4,z5]),(0,[z1601,z1,z2,z4,z5])],[(0,[z11,z38,z12,z173,z5]),(0,[z0,z199,z2,z333,z5]),(0,[z14,z185,z1,z4,z5]),(0,[z1,z45,z2,z873,z5]),(0,[z40,z122,z1,z4,z101])],[(0,[z1602,z1,z11,z4,z5]),(0,[z0,z1,z2,z236,z5]),(0,[z26,z1,z1546,z4,z5]),(0,[z39,z1126,z11,z4,z5]),(0,[z1,z1603,z11,z4,z5])]],
   [[(0,[z26,z1,z11,z722,z5]),(0,[z1,z11,z4,z1604,z5])],[(0,[z11,z2,z626,z4,z230]),(0,[z1,z11,z2,z4,z1605]),(0,[z20,z1,z11,z4,z443]),(0,[z53,z1,z117,z111,z5]),(0,[z0,z742,z2,z4,z5])],[(0,[z1606,z1,z11,z4,z5]),(0,[z1607,z1,z186,z4,z5]),(0,[z442,z1,z416,z4,z5])],[(0,[z0,z1,z2,z167,z5]),(0,[z122,z1,z11,z307,z5]),(0,[z1,z2,z4,z222,z41]),(0,[z1608,z1,z2,z4,z5]),(0,[z53,z1,z65,z4,z66])],[(0,[z0,z1,z257,z4,z5]),(0,[z1,z206,z220,z4,z5]),(0,[z122,z1,z242,z4,z5]),(0,[z1609,z1,z2,z4,z5])],[(0,[z153,z220,z2,z4,z5]),(0,[z1610,z1,z11,z4,z5]),(0,[z1,z11,z10,z2,z268]),(0,[z1,z2,z1611,z4,z5]),(0,[z89,z1,z4,z5,z130])],[(0,[z39,z29,z30,z4,z5]),(0,[z40,z1,z2,z4,z1212]),(0,[z50,z1,z11,z4,z5]),(0,[z1,z357,z530,z4,z5]),(0,[z1343,z1,z2,z4,z135]),(0,[z1,z2,z4,z1612,z5]),(0,[z1613,z1,z2,z4,z5])],[(0,[z53,z1,z235,z4,z5]),(0,[z1,z11,z1614,z4,z5]),(0,[z25,z11,z4,z5,z77]),(0,[z1,z11,z43,z4,z443])]],
   [[(0,[z39,z1,z11,z4,z5]),(0,[z39,z1,z259,z4,z5]),(0,[z185,z1,z591,z4,z5]),(0,[z24,z1,z4,z5,z959]),(0,[z20,z1,z321,z4,z5]),(0,[z20,z1,z4,z1615,z5])],[(0,[z97,z2,z4,z5,z49]),(0,[z558,z20,z11,z4,z60]),(0,[z1616,z1,z257,z4,z5]),(0,[z1,z11,z4,z5,z1617]),(0,[z1,z186,z1546,z4,z5]),(0,[z1,z11,z1618,z4,z5]),(0,[z26,z153,z2,z167,z5]),(0,[z159,z317,z1,z4,z77]),(0,[z53,z1,z240,z4,z5])],[(0,[z39,z1,z11,z4,z200]),(0,[z1215,z1,z357,z4,z5]),(0,[z1201,z1,z2,z4,z41]),(0,[z78,z0,z2,z4,z5])],[(0,[z20,z25,z11,z84,z5]),(0,[z122,z1,z127,z4,z5])],[(0,[z275,z122,z11,z4,z60]),(0,[z89,z1,z2,z4,z5]),(0,[z1449,z185,z1,z4,z5]),(0,[z40,z1,z2,z4,z1031]),(0,[z53,z1,z2,z562,z5]),(0,[z42,z1,z65,z4,z66])],[(0,[z1619,z1,z205,z4,z5]),(0,[z1,z2,z1546,z4,z5]),(0,[z437,z1,z11,z4,z5]),(0,[z1,z11,z2,z4,z1620]),(0,[z39,z1,z106,z4,z5])],[(0,[z97,z464,z12,z4,z5]),(0,[z1621,z1,z2,z4,z5]),(0,[z1622,z1,z2,z4,z5]),(0,[z1139,z1,z2,z47,z5]),(0,[z0,z1,z4,z1623,z5]),(0,[z0,z1,z4,z5,z130]),(0,[z276,z1,z453,z4,z5]),(0,[z1624,z1,z2,z4,z5])],[(0,[z1625,z1,z11,z4,z5]),(0,[z1626,z1,z11,z4,z5]),(0,[z317,z39,z1,z4,z5]),(0,[z123,z11,z2,z49,z61])]],
   [[(0,[z26,z1,z2,z849,z5]),(0,[z317,z1,z117,z4,z5]),(0,[z136,z1,z11,z4,z443])],[(0,[z1627,z1,z11,z4,z5]),(0,[z27,z2,z12,z4,z230]),(0,[z129,z1,z11,z4,z5]),(0,[z20,z1,z147,z4,z5])],[(0,[z1628,z1,z11,z4,z5]),(0,[z11,z2,z626,z413,z60]),(0,[z39,z813,z11,z4,z5])],[(0,[z20,z1,z1182,z4,z5]),(0,[z82,z1116,z11,z2,z5]),(0,[z1629,z1,z2,z4,z5]),(0,[z151,z1,z141,z4,z5]),(0,[z20,z1,z11,z92,z5]),(0,[z1,z220,z141,z4,z5])],[(0,[z122,z29,z30,z4,z5]),(0,[z1215,z1,z137,z4,z5]),(0,[z26,z543,z2,z4,z5]),(0,[z1630,z1,z11,z4,z5]),(0,[z1,z11,z2,z692,z268])],[(0,[z0,z1,z2,z4,z5]),(0,[z151,z1,z172,z4,z5]),(0,[z11,z2,z4,z49,z230]),(0,[z185,z1,z4,z5,z49]),(0,[z1,z12,z4,z1631,z5]),(0,[z153,z2,z12,z4,z41]),(0,[z53,z1,z194,z4,z5]),(0,[z1632,z1,z2,z4,z5]),(0,[z1377,z1,z357,z4,z5])],[(0,[z122,z1,z11,z4,z5]),(0,[z122,z1,z259,z4,z5]),(0,[z26,z11,z2,z173,z5]),(0,[z1633,z1,z2,z4,z5]),(0,[z25,z11,z12,z84,z218]),(0,[z0,z1,z292,z4,z5])],[(0,[z1,z11,z4,z5,z1634]),(0,[z136,z1,z321,z4,z5]),(0,[z1635,z1,z11,z4,z5])]],
   [[(0,[z1636,z1,z30,z4,z5]),(0,[z11,z38,z12,z59,z200]),(0,[z122,z1,z11,z4,z200]),(0,[z153,z2,z514,z4,z5]),(0,[z1,z11,z203,z832,z5]),(0,[z122,z1,z11,z614,z5]),(0,[z1637,z1,z11,z4,z5])],[(0,[z11,z2,z12,z1451,z60]),(0,[z0,z1,z229,z4,z5]),(0,[z1638,z1,z2,z4,z5]),(0,[z11,z10,z2,z173,z5]),(0,[z40,z50,z1,z4,z5]),(0,[z20,z1,z4,z295,z5]),(0,[z122,z1,z4,z969,z5]),(0,[z1,z11,z2,z12,z268])],[(0,[z11,z2,z12,z413,z60]),(0,[z1616,z1,z2,z4,z5]),(0,[z20,z1,z357,z4,z5]),(0,[z26,z153,z141,z4,z5]),(0,[z26,z1,z2,z4,z41]),(0,[z0,z1,z4,z5,z450])],[(0,[z53,z1,z464,z4,z5]),(0,[z1,z137,z466,z4,z5]),(0,[z20,z740,z11,z4,z5]),(0,[z1,z63,z357,z4,z5]),(0,[z122,z1,z106,z4,z5]),(0,[z122,z1639,z1,z4,z5])],[(0,[z26,z1,z2,z864,z5]),(0,[z647,z1,z63,z4,z5]),(0,[z11,z235,z12,z4,z230]),(0,[z1,z2,z1640,z4,z5]),(0,[z1,z2,z1641,z4,z5]),(0,[z1642,z1,z11,z4,z5]),(0,[z123,z11,z194,z12,z61])],[(0,[z26,z1,z400,z4,z5]),(0,[z1084,z11,z2,z173,z5]),(0,[z1643,z1,z2,z4,z5]),(0,[z160,z1,z2,z4,z5]),(0,[z26,z1,z2,z307,z5])],[(0,[z1644,z1,z2,z4,z5]),(0,[z699,z1,z4,z5,z35]),(0,[z409,z20,z1,z11,z61]),(0,[z1645,z1,z2,z4,z5])],[(0,[z1,z11,z12,z1646,z5]),(0,[z1,z12,z4,z367,z443]),(0,[z0,z813,z2,z4,z5])]],
   [[(0,[z11,z2,z12,z864,z60]),(0,[z26,z1354,z1,z4,z5]),(0,[z0,z1,z17,z4,z5])],[(0,[z697,z1,z2,z4,z5]),(0,[z26,z97,z2,z4,z5]),(0,[z151,z25,z11,z4,z5]),(0,[z20,z163,z1,z307,z5]),(0,[z1647,z1,z2,z4,z5]),(0,[z39,z1,z11,z338,z37]),(0,[z1648,z1,z11,z4,z5]),(0,[z1649,z1,z11,z4,z5]),(0,[z53,z1650,z2,z4,z5])],[(0,[z11,z2,z311,z4,z5]),(0,[z53,z1,z2,z4,z189]),(0,[z1651,z1,z2,z4,z5]),(0,[z27,z2,z12,z413,z60]),(0,[z275,z53,z2,z4,z60]),(0,[z163,z1,z63,z4,z5]),(0,[z1325,z186,z12,z4,z5]),(0,[z1652,z1,z2,z4,z5]),(0,[z89,z1,z65,z4,z66])],[(0,[z97,z10,z2,z4,z5]),(0,[z24,z1,z4,z285,z5]),(0,[z53,z1,z210,z4,z5]),(0,[z20,z1,z1067,z4,z5]),(0,[z411,z53,z2,z4,z5]),(0,[z14,z1,z11,z722,z5]),(0,[z1,z106,z12,z722,z5]),(0,[z122,z1,z622,z4,z5])],[(0,[z1653,z1,z2,z4,z5])],[(0,[z697,z1,z229,z4,z5]),(0,[z1,z45,z2,z832,z5])],[(0,[z20,z1,z11,z1096,z5]),(0,[z1,z11,z12,z84,z443])],[(0,[z298,z11,z993,z4,z5]),(0,[z26,z1126,z2,z4,z5]),(0,[z0,z1,z2,z4,z299]),(0,[z1,z11,z4,z1634,z77]),(0,[z53,z335,z1,z114,z5]),(0,[z0,z1,z933,z4,z5])]],
   [[(0,[z39,z1,z206,z4,z5]),(0,[z526,z1,z4,z278,z5]),(0,[z53,z1,z154,z4,z5]),(0,[z1,z254,z63,z4,z5])],[(0,[z1654,z1,z2,z4,z5]),(0,[z1655,z1,z2,z4,z5]),(0,[z1656,z1,z11,z4,z5]),(0,[z578,z26,z1,z4,z218]),(0,[z1,z2,z142,z4,z41]),(0,[z25,z63,z11,z4,z5]),(0,[z1,z11,z84,z5,z77]),(0,[z136,z1,z357,z4,z5]),(0,[z304,z53,z1,z2,z61]),(0,[z0,z1,z117,z111,z5])],[(0,[z1657,z1,z11,z4,z5]),(0,[z39,z1,z246,z4,z5]),(0,[z1658,z1,z2,z4,z5]),(0,[z1,z11,z4,z1659,z5]),(0,[z39,z1,z45,z4,z5])],[(0,[z97,z100,z2,z4,z5]),(0,[z82,z219,z2,z59,z5]),(0,[z867,z1,z1258,z4,z5]),(0,[z40,z1,z2,z167,z135]),(0,[z125,z1,z141,z4,z5]),(0,[z0,z1,z65,z4,z66])],[(0,[z1,z100,z11,z722,z5]),(0,[z53,z1,z445,z4,z5])],[(0,[z26,z1,z2,z1185,z5]),(0,[z11,z235,z12,z413,z60]),(0,[z317,z1,z2,z4,z5]),(0,[z185,z1,z10,z4,z5]),(0,[z1,z134,z2,z4,z1660])],[(0,[z1661,z1,z2,z4,z5]),(0,[z1594,z1,z2,z4,z189]),(0,[z1662,z1,z2,z4,z5]),(0,[z53,z1310,z2,z4,z5]),(0,[z14,z123,z11,z2,z61])],[(0,[z0,z1,z235,z4,z5]),(0,[z511,z1,z186,z4,z5]),(0,[z26,z1,z11,z4,z443]),(0,[z1663,z1,z2,z4,z5]),(0,[z122,z1,z11,z338,z37])]],
   [[(0,[z1,z2,z4,z49,z41])],[(0,[z224,z1,z685,z4,z5]),(0,[z1664,z1,z11,z4,z5]),(0,[z42,z1,z154,z4,z5]),(0,[z20,z1,z1159,z4,z5])],[(0,[z0,z1,z4,z5,z294]),(0,[z0,z2,z4,z5,z796])],[(0,[z20,z1,z11,z84,z5]),(0,[z20,z1272,z11,z4,z5])],[(0,[z11,z2,z1665,z173,z5]),(0,[z39,z199,z11,z333,z5]),(0,[z1,z63,z11,z84,z5]),(0,[z0,z1,z2,z562,z5]),(0,[z0,z1,z1177,z4,z5])],[(0,[z9,z1,z292,z4,z5]),(0,[z11,z2,z894,z173,z5]),(0,[z39,z1,z11,z236,z5]),(0,[z20,z11,z2,z4,z230]),(0,[z122,z1,z592,z4,z5])],[(0,[z24,z1,z765,z4,z5]),(0,[z1666,z1,z2,z4,z5]),(0,[z26,z1325,z2,z4,z5]),(0,[z153,z2,z4,z5,z135]),(0,[z125,z1,z271,z4,z5]),(0,[z39,z103,z1,z4,z5]),(0,[z1,z147,z22,z4,z5]),(0,[z1,z357,z12,z4,z443]),(0,[z122,z1,z206,z4,z5])],[(0,[z20,z1,z584,z4,z5]),(0,[z20,z1,z215,z4,z5]),(0,[z1667,z1,z11,z4,z5])]],
   [[(0,[z1636,z1,z11,z4,z5]),(0,[z122,z1,z246,z4,z5]),(0,[z1,z2,z4,z5,z1668]),(0,[z1669,z1,z2,z4,z5]),(0,[z122,z1,z45,z4,z5])],[(0,[z1670,z1,z2,z4,z5]),(0,[z1671,z1,z2,z4,z5]),(0,[z151,z185,z1,z4,z5]),(0,[z39,z1,z11,z1672,z5]),(0,[z39,z1,z11,z167,z5]),(0,[z53,z350,z2,z4,z5])],[(0,[z1673,z1,z11,z4,z5]),(0,[z1674,z1,z2,z4,z5]),(0,[z1675,z1,z11,z4,z5]),(0,[z26,z55,z141,z4,z5])],[(0,[z163,z1,z4,z1133,z5]),(0,[z1,z11,z4,z1676,z5])],[(0,[z40,z1,z141,z4,z135]),(0,[z1,z2,z4,z1598,z135]),(0,[z1,z11,z4,z1677,z5]),(0,[z1678,z1,z2,z4,z5])],[(0,[z26,z1,z1679,z4,z5]),(0,[z1680,z1,z11,z4,z5]),(0,[z699,z74,z2,z4,z75]),(0,[z24,z1,z162,z4,z5]),(0,[z1,z220,z4,z5,z181]),(0,[z39,z1,z11,z1681,z5]),(0,[z1682,z1,z11,z4,z5]),(0,[z1,z1683,z2,z4,z5]),(0,[z53,z216,z2,z4,z5])],[(0,[z97,z262,z2,z4,z5]),(0,[z53,z1,z196,z4,z5]),(0,[z219,z1,z4,z179,z5]),(0,[z1,z11,z12,z722,z5])],[(0,[z1684,z1,z263,z4,z5]),(0,[z39,z1,z27,z4,z5]),(0,[z1,z292,z11,z775,z5]),(0,[z411,z292,z11,z4,z5])]],
   [[(0,[z0,z1,z531,z4,z5]),(0,[z1685,z1,z11,z4,z5])],[(0,[z1686,z1,z2,z4,z5]),(0,[z163,z1,z175,z4,z5])],[(0,[z1687,z1,z2,z4,z5]),(0,[z263,z2,z12,z59,z200]),(0,[z1688,z1,z11,z4,z5]),(0,[z122,z199,z11,z333,z5]),(0,[z0,z129,z1,z4,z5]),(0,[z136,z1,z11,z84,z5])],[(0,[z20,z150,z11,z4,z5]),(0,[z100,z11,z2,z173,z5]),(0,[z122,z1,z11,z236,z5]),(0,[z39,z1,z351,z4,z5])],[(0,[z14,z97,z2,z4,z5]),(0,[z1,z137,z4,z5,z1212]),(0,[z578,z20,z1,z4,z101])],[(0,[z1689,z1,z2,z4,z5]),(0,[z20,z11,z2,z59,z200]),(0,[z1,z12,z4,z1690,z41]),(0,[z159,z1,z4,z1085,z77]),(0,[z1,z126,z454,z4,z5])],[(0,[z1691,z1,z11,z4,z5]),(0,[z224,z11,z208,z4,z5]),(0,[z26,z1,z4,z1692,z5]),(0,[z1693,z1,z11,z4,z5]),(0,[z122,z1,z878,z4,z5]),(0,[z456,z1,z175,z4,z5])],[(0,[z122,z1,z11,z167,z5]),(0,[z1,z11,z2,z1694,z5]),(0,[z1,z11,z65,z4,z1634]),(0,[z1,z2,z4,z5,z1695])]],
   [[(0,[z20,z1,z11,z1425,z5]),(0,[z393,z11,z2,z12,z61])],[(0,[z82,z53,z2,z59,z5]),(0,[z1,z186,z12,z92,z5]),(0,[z1696,z1,z11,z4,z5]),(0,[z53,z1,z21,z4,z5]),(0,[z53,z1697,z2,z4,z5])],[(0,[z39,z1,z11,z505,z5]),(0,[z1698,z1,z11,z4,z5]),(0,[z524,z122,z1,z4,z5])],[(0,[z1699,z1,z11,z4,z5]),(1,[z1,z1546,z4,z5])],[(0,[z50,z1,z175,z4,z5]),(0,[z1700,z1,z2,z4,z5]),(0,[z1701,z1,z2,z4,z5]),(0,[z14,z1,z11,z2,z268])],[(0,[z163,z1,z826,z4,z5]),(0,[z11,z2,z178,z59,z200]),(0,[z122,z1,z27,z4,z5]),(0,[z53,z1,z2,z413,z5]),(0,[z26,z24,z1,z84,z5]),(0,[z1,z2,z233,z253,z5]),(0,[z1,z11,z722,z5,z49])],[(0,[z1,z11,z4,z5,z1702]),(0,[z1,z2,z307,z5,z135]),(0,[z1,z11,z10,z4,z443]),(0,[z1703,z1,z2,z4,z5]),(0,[z1,z1704,z12,z4,z443])],[(0,[z317,z1,z137,z4,z5]),(0,[z50,z1,z18,z4,z5]),(0,[z1,z18,z2,z1225,z5]),(0,[z1705,z1,z11,z4,z5]),(0,[z0,z335,z1,z114,z5]),(0,[z0,z1,z118,z4,z5]),(0,[z752,z1,z4,z5,z663])]],
   [[(0,[z0,z1,z154,z4,z5])],[(0,[z1706,z1,z2,z4,z5]),(0,[z1707,z1,z11,z4,z5]),(0,[z1078,z24,z1,z4,z5]),(0,[z20,z1173,z11,z4,z5]),(0,[z122,z1,z351,z4,z5]),(0,[z1350,z1,z2,z708,z5]),(0,[z1,z11,z2,z5,z1708])],[(0,[z1709,z1,z11,z4,z5]),(0,[z11,z2,z59,z200,z773]),(0,[z11,z2,z4,z365,z230]),(0,[z185,z1,z100,z4,z5]),(0,[z1710,z1,z11,z4,z5]),(0,[z53,z153,z2,z4,z5]),(0,[z53,z1,z2,z1711,z5])],[(0,[z163,z1,z4,z5,z850]),(0,[z1301,z1,z141,z4,z5]),(0,[z1,z63,z4,z5,z700]),(0,[z1,z11,z118,z12,z268])],[(0,[z252,z39,z96,z4,z5]),(0,[z53,z1,z38,z4,z5]),(0,[z1712,z1,z2,z4,z5]),(0,[z1,z206,z12,z4,z443])],[(0,[z205,z2,z12,z4,z230]),(0,[z11,z257,z12,z4,z230]),(0,[z1,z100,z11,z2,z268]),(0,[z0,z1,z447,z4,z5]),(0,[z122,z1,z4,z1713,z5])],[(0,[z0,z1,z188,z4,z5]),(0,[z1714,z1,z11,z4,z5]),(0,[z20,z996,z11,z4,z5]),(0,[z26,z153,z154,z4,z5]),(0,[z159,z25,z11,z4,z77]),(0,[z1173,z11,z2,z12,z61]),(0,[z1,z11,z138,z722,z5]),(0,[z0,z638,z1,z4,z5])],[(0,[z62,z74,z11,z4,z75]),(0,[z20,z1324,z1,z4,z5]),(0,[z85,z1,z2,z4,z5]),(0,[z0,z1,z141,z4,z5]),(0,[z26,z1,z4,z385,z5]),(0,[z1,z11,z4,z1715,z5]),(0,[z1,z2,z4,z5,z1716]),(0,[z1717,z1,z287,z4,z5])]],
   [[(0,[z39,z216,z11,z4,z5]),(0,[z1,z210,z241,z4,z5]),(0,[z1405,z1013,z2,z4,z5]),(0,[z1,z11,z722,z202,z5]),(0,[z1,z11,z722,z502,z5]),(0,[z0,z122,z1,z4,z5])],[(0,[z1718,z1,z2,z4,z5]),(0,[z329,z1,z2,z253,z5])],[(0,[z82,z11,z2,z1251,z5]),(0,[z1719,z1,z11,z4,z5])],[(0,[z11,z2,z264,z173,z5]),(0,[z83,z219,z1,z4,z5]),(0,[z53,z682,z2,z4,z5]),(0,[z965,z247,z11,z2,z5])],[(0,[z185,z1,z1720,z4,z5]),(0,[z14,z1,z2,z253,z5])],[(0,[z1721,z1,z2,z4,z5]),(0,[z151,z1,z1546,z4,z5]),(0,[z1,z220,z1546,z4,z5]),(0,[z1,z10,z2,z253,z5]),(0,[z1,z1722,z12,z4,z41])],[(0,[z1723,z1,z2,z4,z5]),(0,[z26,z843,z2,z4,z5]),(0,[z190,z1,z4,z203,z5]),(0,[z1724,z1,z2,z4,z5])],[(0,[z20,z1,z11,z1451,z5]),(0,[z317,z163,z1,z4,z5]),(0,[z26,z1,z141,z307,z5]),(0,[z39,z1,z363,z4,z5]),(0,[z50,z53,z1,z4,z5])]],
   [[(0,[z97,z2,z339,z4,z5]),(0,[z1100,z11,z2,z119,z5]),(0,[z1725,z1,z11,z4,z5]),(0,[z1336,z1,z2,z1156,z5]),(0,[z122,z1,z1726,z4,z5])],[(0,[z1727,z1,z2,z4,z5]),(0,[z1,z2,z183,z4,z41]),(0,[z0,z350,z2,z4,z5])],[(0,[z1728,z1,z2,z4,z5]),(0,[z1729,z11,z2,z4,z5])],[(0,[z26,z11,z2,z4,z230]),(0,[z50,z1,z357,z4,z5]),(0,[z1,z2,z4,z1730,z5]),(0,[z1,z254,z12,z4,z41]),(0,[z53,z1,z2,z84,z5]),(0,[z53,z1,z22,z4,z5])],[(0,[z151,z1,z943,z4,z5]),(0,[z1731,z1,z11,z4,z5]),(0,[z1,z2,z183,z307,z5]),(0,[z1341,z1,z2,z1410,z5])],[(0,[z1732,z1,z2,z4,z5]),(0,[z1733,z1,z2,z4,z5]),(0,[z39,z1,z357,z4,z5]),(0,[z1,z100,z2,z253,z5]),(0,[z1,z357,z4,z5,z77]),(0,[z1734,z1,z2,z4,z5]),(0,[z0,z216,z2,z4,z5]),(0,[z78,z122,z11,z4,z5])],[(0,[z0,z1,z196,z4,z5]),(0,[z1735,z1,z11,z4,z5]),(0,[z205,z2,z12,z413,z60]),(0,[z11,z257,z12,z413,z60]),(0,[z1736,z1,z2,z4,z5]),(0,[z1515,z1,z137,z4,z5]),(0,[z1,z1737,z2,z4,z5]),(0,[z318,z39,z1,z71,z5]),(0,[z1,z254,z12,z307,z5]),(0,[z122,z216,z11,z4,z5])],[(0,[z151,z1,z4,z440,z5]),(0,[z39,z1,z177,z4,z5]),(0,[z1738,z1,z2,z4,z5])]],
   [[(0,[z1739,z1,z12,z4,z5]),(0,[z304,z39,z1,z11,z61])],[(0,[z11,z2,z12,z413,z230]),(0,[z1740,z1,z11,z4,z5]),(0,[z153,z2,z12,z307,z101])],[(0,[z39,z1,z205,z4,z5]),(0,[z39,z1,z11,z562,z5]),(0,[z122,z1,z147,z4,z5])],[(0,[z1741,z1,z2,z4,z5]),(0,[z1,z209,z2,z4,z41])],[(0,[z1742,z1,z11,z4,z5]),(0,[z1743,z1,z27,z4,z5]),(0,[z1,z1546,z137,z4,z5]),(0,[z20,z1166,z11,z4,z5]),(0,[z1,z11,z22,z4,z5]),(0,[z123,z287,z2,z12,z61]),(0,[z1744,z1,z11,z4,z5])],[(0,[z1,z63,z220,z4,z5]),(0,[z50,z1,z137,z4,z5]),(0,[z1274,z1,z11,z4,z149]),(0,[z1,z11,z4,z5,z1745]),(0,[z122,z1,z363,z4,z5])],[(0,[z1746,z1,z2,z4,z5]),(0,[z275,z0,z2,z4,z60]),(0,[z39,z1747,z11,z4,z5]),(0,[z39,z1,z4,z5,z367]),(0,[z1,z2,z253,z736,z5]),(0,[z20,z682,z11,z4,z5]),(0,[z20,z1,z351,z84,z5]),(0,[z1,z2,z1748,z4,z5]),(0,[z122,z1,z4,z5,z495])],[(0,[z53,z224,z1,z4,z5]),(0,[z317,z1,z141,z4,z5])]],
   [[(0,[z26,z1,z567,z4,z5]),(0,[z1,z11,z1749,z4,z5]),(0,[z1750,z1,z2,z4,z5]),(0,[z1751,z1,z11,z4,z5]),(0,[z317,z122,z1,z4,z5])],[(0,[z26,z150,z11,z4,z5]),(0,[z1,z137,z1752,z4,z5]),(0,[z0,z1,z21,z4,z5]),(0,[z1565,z1,z2,z4,z5])],[(0,[z26,z1,z2,z505,z5]),(0,[z53,z486,z108,z4,z5]),(0,[z9,z1,z201,z4,z5]),(0,[z26,z1,z141,z4,z5]),(0,[z20,z163,z153,z4,z5]),(0,[z53,z55,z2,z4,z5]),(0,[z20,z1,z927,z4,z5])],[(0,[z26,z11,z2,z59,z200]),(0,[z1753,z1,z2,z4,z5]),(0,[z122,z1,z357,z4,z5])],[],[(0,[z20,z1,z977,z4,z5]),(0,[z53,z74,z2,z4,z75]),(0,[z0,z1,z4,z5,z799]),(0,[z304,z0,z1,z2,z61]),(0,[z1754,z1,z11,z4,z5])],[(0,[z97,z196,z12,z4,z5]),(0,[z150,z11,z4,z5,z49]),(0,[z11,z10,z2,z59,z200]),(0,[z82,z83,z11,z59,z5]),(0,[z163,z1,z1258,z4,z5]),(0,[z159,z1,z11,z4,z149])],[(0,[z11,z188,z12,z173,z5]),(0,[z1755,z1,z11,z4,z5]),(0,[z1599,z1,z4,z180,z5]),(0,[z1,z11,z2,z1756,z5]),(0,[z411,z11,z2,z872,z5]),(0,[z1,z11,z187,z4,z443]),(0,[z1,z11,z2,z49,z268])]],
   [[(0,[z122,z1,z205,z4,z5]),(0,[z1743,z1,z11,z4,z5]),(0,[z50,z1,z4,z71,z5]),(0,[z40,z1,z154,z4,z135]),(0,[z122,z1,z11,z562,z5])],[(0,[z26,z1,z2,z619,z5]),(0,[z11,z2,z12,z173,z5]),(0,[z1587,z1,z11,z4,z5]),(0,[z151,z153,z2,z4,z5])],[(0,[z517,z97,z2,z4,z5]),(0,[z1084,z11,z2,z59,z200]),(0,[z151,z1,z4,z834,z5])],[(0,[z1757,z2,z12,z4,z5]),(0,[z1758,z1,z11,z4,z5]),(0,[z11,z2,z12,z173,z200]),(0,[z477,z1,z11,z4,z5]),(0,[z40,z1,z4,z294,z135]),(0,[z25,z206,z12,z4,z5]),(0,[z1,z2,z4,z5,z1759])],[(0,[z0,z1,z38,z4,z5]),(0,[z14,z11,z2,z173,z5]),(0,[z699,z62,z1,z4,z5]),(0,[z185,z1,z514,z4,z5]),(0,[z20,z1,z357,z562,z5]),(0,[z122,z1,z4,z5,z367]),(0,[z122,z1,z1067,z4,z5]),(0,[z1,z11,z2,z86,z268])],[(0,[z1,z2,z4,z5,z1760]),(0,[z26,z813,z2,z4,z5]),(0,[z1761,z1,z2,z4,z5])],[(0,[z39,z1,z11,z84,z5]),(0,[z159,z1,z11,z4,z77]),(0,[z122,z1,z11,z4,z770]),(0,[z1762,z1,z2,z4,z5])],[(0,[z1,z2,z278,z832,z5])]],
   [[(0,[z1706,z1,z108,z4,z5]),(0,[z1684,z1,z11,z4,z5]),(0,[z39,z1,z11,z4,z189]),(0,[z20,z1325,z11,z4,z5]),(0,[z50,z1,z4,z180,z5]),(0,[z14,z1,z2,z4,z41]),(0,[z0,z1,z194,z4,z5])],[(0,[z9,z2,z311,z4,z5]),(0,[z1,z10,z2,z4,z41])],[(0,[z150,z11,z405,z4,z5]),(0,[z1,z11,z1546,z4,z5]),(0,[z1763,z1,z11,z4,z5])],[(0,[z97,z2,z12,z4,z5]),(0,[z97,z2,z289,z4,z5])],[(0,[z671,z26,z2,z4,z60]),(0,[z1,z2,z4,z741,z41]),(0,[z1764,z11,z2,z4,z5]),(0,[z122,z1,z4,z5,z1085]),(0,[z1,z11,z194,z12,z268])],[(0,[z1765,z1,z11,z4,z5])],[(0,[z96,z602,z2,z4,z5]),(0,[z1,z2,z1766,z4,z5]),(0,[z0,z1,z464,z4,z5]),(0,[z1767,z1,z2,z4,z5]),(0,[z1768,z1,z2,z4,z5]),(0,[z26,z1,z2,z92,z5]),(0,[z1,z2,z241,z4,z5]),(0,[z1,z11,z2,z4,z1769]),(0,[z1,z206,z12,z84,z5]),(0,[z575,z1,z11,z4,z443]),(0,[z965,z0,z1,z2,z5]),(0,[z0,z892,z1,z4,z5]),(0,[z1,z1770,z2,z4,z5])],[(0,[z151,z1,z494,z4,z5]),(0,[z774,z11,z2,z59,z200]),(0,[z910,z1,z11,z4,z588])]],
   [[(0,[z1771,z1,z11,z4,z5]),(0,[z20,z1,z874,z4,z5]),(0,[z1,z107,z320,z4,z5])],[(0,[z1772,z1,z12,z4,z5]),(0,[z671,z1,z2,z4,z135]),(0,[z20,z11,z2,z413,z60]),(0,[z1,z100,z2,z4,z41]),(0,[z409,z1,z11,z4,z77]),(0,[z53,z1,z4,z203,z5]),(0,[z1,z206,z320,z4,z5]),(0,[z123,z11,z2,z288,z61])],[(0,[z828,z1,z141,z4,z5])],[(0,[z1,z21,z12,z253,z5]),(0,[z1,z2,z12,z307,z41]),(0,[z1773,z1,z2,z4,z5]),(0,[z0,z1,z2,z84,z5]),(0,[z122,z1,z81,z4,z5])],[(0,[z62,z1,z11,z4,z5]),(0,[z53,z39,z1,z4,z5]),(0,[z122,z1,z11,z84,z5]),(0,[z1,z11,z2,z4,z528])],[(0,[z0,z1,z2,z4,z189]),(0,[z1,z11,z2,z832,z5])],[(0,[z150,z11,z10,z4,z5]),(0,[z122,z1,z11,z4,z189]),(0,[z1,z2,z514,z307,z5]),(0,[z0,z1,z210,z4,z5]),(0,[z350,z11,z12,z4,z443])],[(0,[z11,z2,z12,z1774,z5]),(0,[z82,z39,z11,z59,z5]),(0,[z185,z1,z12,z4,z5]),(0,[z129,z1,z351,z4,z5]),(0,[z1775,z1,z11,z4,z5])]],
   [[(0,[z100,z11,z2,z4,z230]),(0,[z185,z1,z1752,z4,z5]),(0,[z39,z1,z287,z4,z5]),(0,[z20,z1,z357,z84,z5])],[(0,[z11,z2,z12,z4,z1776]),(0,[z125,z153,z2,z4,z5]),(0,[z1100,z39,z11,z4,z5]),(0,[z1,z11,z4,z5,z1777])],[(0,[z150,z11,z583,z4,z5]),(0,[z11,z2,z894,z59,z200]),(0,[z151,z1,z73,z4,z5])],[(0,[z259,z2,z311,z4,z5]),(0,[z11,z2,z642,z4,z230]),(0,[z40,z1,z2,z4,z1598]),(0,[z0,z1,z2,z4,z522])],[(0,[z14,z150,z11,z4,z5]),(0,[z1,z141,z183,z4,z5])],[(0,[z20,z25,z11,z4,z5]),(0,[z11,z2,z173,z5,z49]),(0,[z82,z0,z2,z59,z5]),(0,[z39,z1,z4,z5,z48]),(0,[z39,z1,z241,z4,z5]),(0,[z14,z1,z11,z4,z443]),(0,[z1778,z11,z2,z4,z5])],[(0,[z14,z11,z2,z59,z200]),(0,[z1,z1779,z12,z4,z5]),(0,[z1,z2,z4,z528,z48])],[(0,[z0,z224,z1,z4,z5]),(0,[z1571,z1,z4,z71,z5]),(0,[z39,z350,z11,z4,z5]),(0,[z53,z1,z2,z307,z5]),(0,[z1780,z1,z2,z4,z5])]],
   [[(0,[z1781,z1,z2,z4,z5])],[],[(0,[z0,z486,z108,z4,z5]),(0,[z1782,z1,z11,z4,z5]),(0,[z0,z55,z2,z4,z5]),(0,[z1,z2,z4,z1783,z41]),(0,[z437,z1,z4,z5,z48]),(0,[z20,z123,z11,z2,z61]),(0,[z0,z1,z2,z391,z5]),(0,[z122,z1310,z11,z4,z5]),(0,[z1588,z1,z11,z4,z5])],[(0,[z1784,z1,z11,z4,z5]),(0,[z1,z2,z4,z5,z1598]),(0,[z26,z1,z154,z307,z5]),(0,[z122,z1,z4,z5,z1046]),(0,[z85,z1,z4,z5,z660])],[(0,[z39,z1,z6,z4,z5]),(0,[z53,z1166,z2,z4,z5]),(0,[z1,z2,z4,z5,z1785])],[(0,[z282,z1,z220,z4,z5]),(0,[z40,z39,z1,z4,z101]),(0,[z159,z1,z11,z562,z77]),(0,[z123,z11,z10,z2,z61]),(0,[z297,z1481,z11,z4,z5]),(0,[z85,z752,z1,z4,z5])],[(0,[z26,z1,z531,z4,z5]),(0,[z1,z100,z11,z4,z443]),(0,[z25,z11,z187,z4,z5]),(0,[z129,z1,z4,z5,z48]),(0,[z122,z1,z287,z4,z5])],[(0,[z317,z1,z108,z4,z5]),(0,[z1786,z1,z11,z4,z5]),(0,[z39,z1,z147,z4,z5]),(0,[z1787,z1,z11,z4,z5])]],
   [[(0,[z1788,z1,z11,z4,z5]),(0,[z558,z1,z11,z4,z77]),(0,[z150,z6,z12,z4,z5]),(0,[z100,z11,z2,z59,z200]),(0,[z1789,z1,z2,z4,z5]),(0,[z53,z1,z254,z4,z5]),(0,[z0,z1,z4,z5,z665])],[(0,[z1790,z1,z2,z4,z5]),(0,[z39,z1,z58,z4,z5]),(0,[z1,z11,z2,z12,z1791]),(0,[z39,z1,z4,z278,z5]),(0,[z1792,z1,z11,z4,z5]),(0,[z1793,z1,z2,z4,z5]),(0,[z1100,z45,z2,z4,z5])],[(0,[z40,z153,z2,z4,z135]),(0,[z39,z1,z18,z19,z5]),(0,[z1,z2,z253,z5,z49])],[(0,[z26,z1,z141,z167,z5]),(0,[z39,z1,z11,z847,z5]),(0,[z159,z1,z11,z4,z1032]),(0,[z53,z862,z1,z4,z5]),(0,[z122,z1,z4,z5,z48])],[(0,[z24,z1,z4,z5,z534]),(0,[z26,z1,z4,z5,z1794]),(0,[z136,z25,z11,z4,z5])],[(0,[z20,z1,z1795,z4,z5]),(0,[z1796,z1,z2,z4,z5]),(0,[z122,z350,z11,z4,z5]),(0,[z0,z1,z420,z4,z5])],[(0,[z1579,z1,z11,z4,z200]),(0,[z1797,z1,z11,z4,z5]),(0,[z151,z1,z357,z4,z5]),(0,[z185,z1,z146,z4,z5])],[]],
   [[(0,[z0,z422,z298,z4,z5]),(0,[z20,z1,z11,z402,z5]),(0,[z24,z1,z1366,z4,z5]),(0,[z1798,z1,z11,z4,z5]),(0,[z258,z1,z2,z4,z513]),(0,[z159,z53,z1,z4,z218]),(0,[z1,z292,z11,z832,z5]),(0,[z122,z1,z4,z5,z914])],[(0,[z11,z10,z2,z4,z230]),(0,[z26,z1,z210,z4,z5]),(0,[z40,z50,z1,z4,z135]),(0,[z1,z2,z1799,z4,z41]),(0,[z20,z350,z357,z4,z5]),(0,[z1800,z11,z2,z4,z5]),(0,[z1,z11,z187,z84,z5])],[(0,[z122,z1,z6,z4,z5]),(0,[z1801,z1,z11,z4,z5]),(0,[z1,z351,z12,z4,z443]),(0,[z122,z11,z4,z5,z796])],[(0,[z1628,z1,z58,z4,z5]),(0,[z1802,z1,z11,z4,z5]),(0,[z1803,z1,z11,z4,z5]),(0,[z1619,z1,z11,z4,z5]),(0,[z39,z1,z11,z413,z5]),(0,[z275,z39,z11,z4,z60]),(0,[z50,z0,z1,z4,z5])],[(0,[z1804,z1,z11,z4,z5]),(0,[z53,z1,z2,z4,z200]),(0,[z1524,z566,z11,z4,z5]),(0,[z53,z1,z2,z614,z5]),(0,[z123,z11,z2,z692,z61])],[(0,[z20,z185,z1,z4,z5]),(0,[z828,z1,z137,z4,z5]),(0,[z153,z254,z12,z4,z5]),(0,[z727,z410,z2,z4,z5])],[(0,[z578,z1,z2,z4,z135]),(0,[z53,z1,z2,z1805,z5])],[(0,[z122,z1,z58,z4,z5]),(0,[z1746,z1,z188,z4,z5]),(0,[z1586,z1,z2,z4,z200]),(0,[z50,z24,z1,z4,z5]),(0,[z39,z1806,z11,z4,z5]),(0,[z1807,z1,z11,z4,z5]),(0,[z53,z1,z4,z5,z450]),(0,[z122,z1,z4,z278,z5])]],
   [[(0,[z1808,z1,z11,z4,z5]),(0,[z58,z2,z12,z173,z5]),(0,[z39,z153,z11,z4,z5]),(0,[z122,z1,z18,z19,z5]),(0,[z1,z12,z722,z382,z5]),(0,[z1,z11,z12,z4,z443]),(0,[z0,z1,z2,z847,z5])],[(0,[z123,z11,z2,z12,z61]),(0,[z0,z1,z4,z203,z5])],[(0,[z83,z1,z4,z930,z5]),(0,[z1,z11,z2,z1809,z5]),(0,[z1,z11,z4,z5,z1810]),(0,[z122,z53,z1,z4,z5]),(0,[z1811,z1,z2,z4,z5])],[(0,[z1812,z1,z11,z4,z5]),(0,[z1585,z1,z2,z4,z5])],[(0,[z224,z1,z11,z33,z5]),(0,[z20,z1,z4,z5,z581])],[(0,[z699,z1,z2,z4,z5]),(0,[z252,z122,z96,z4,z5])],[(0,[z317,z1,z416,z4,z5]),(0,[z159,z1,z11,z4,z1634]),(0,[z458,z1,z292,z4,z5])],[(0,[z26,z11,z2,z413,z60]),(0,[z163,z1,z4,z5,z611]),(0,[z53,z1,z4,z481,z5])]],
   [[(0,[z1813,z1,z2,z4,z5]),(0,[z11,z2,z264,z59,z200]),(0,[z0,z1,z2,z413,z5]),(0,[z1,z63,z4,z314,z5]),(0,[z20,z1,z11,z2,z268]),(0,[z551,z1,z11,z493,z5])],[(0,[z1814,z1,z11,z4,z5]),(0,[z1815,z11,z2,z173,z5]),(0,[z122,z1,z11,z413,z5]),(0,[z578,z151,z1,z4,z5]),(0,[z1,z186,z501,z4,z5]),(0,[z159,z1,z351,z4,z77]),(0,[z1,z357,z187,z4,z5]),(0,[z1816,z1,z2,z4,z5]),(0,[z1817,z1,z2,z4,z5])],[(0,[z1549,z1,z2,z4,z5]),(0,[z11,z10,z2,z413,z60]),(0,[z11,z2,z413,z49,z60]),(0,[z1,z12,z4,z5,z1818]),(0,[z1343,z26,z1,z2,z61]),(0,[z193,z11,z2,z33,z5])],[(0,[z1,z141,z12,z4,z41])],[(0,[z20,z1,z11,z1265,z5]),(0,[z1819,z1,z11,z4,z5]),(0,[z1,z11,z4,z49,z443]),(0,[z1820,z1,z2,z4,z5]),(0,[z1,z11,z4,z528,z130]),(0,[z328,z1,z11,z2,z268])],[(0,[z0,z153,z2,z4,z5]),(0,[z912,z1,z11,z1260,z5]),(0,[z1,z11,z2,z1821,z5]),(0,[z1,z2,z12,z253,z5])],[(0,[z542,z1,z220,z4,z5]),(0,[z151,z1,z2,z307,z5]),(0,[z1,z141,z514,z4,z5]),(0,[z1,z220,z2,z307,z5]),(0,[z122,z153,z11,z4,z5]),(0,[z1652,z1,z4,z114,z5]),(0,[z1653,z1,z4,z66,z5])],[(0,[z151,z1,z11,z84,z5]),(0,[z0,z1,z2,z307,z5]),(0,[z20,z1,z11,z614,z5])]],
   [[(0,[z1,z1546,z12,z4,z5]),(0,[z1,z2,z4,z5,z1822]),(0,[z26,z1,z271,z4,z5]),(0,[z1,z11,z4,z5,z1823])],[(0,[z1824,z1,z11,z4,z5]),(0,[z1825,z1,z2,z4,z5])],[(0,[z190,z1,z2,z4,z5]),(0,[z40,z55,z2,z4,z135]),(0,[z1826,z1,z11,z4,z5]),(0,[z1827,z1,z11,z4,z5]),(0,[z20,z350,z11,z84,z5]),(0,[z1828,z1,z2,z4,z5])],[(0,[z1137,z1,z162,z4,z5]),(0,[z163,z1,z594,z4,z5]),(0,[z26,z1,z4,z5,z1380]),(0,[z1,z11,z4,z1829,z443])],[(0,[z691,z150,z11,z4,z5]),(0,[z24,z1,z220,z4,z5]),(0,[z560,z586,z11,z4,z5])],[(0,[z26,z153,z2,z307,z5]),(0,[z53,z25,z2,z4,z5]),(0,[z122,z1166,z11,z4,z5])],[(0,[z11,z2,z12,z4,z230]),(0,[z578,z1,z12,z4,z380])],[(0,[z39,z1,z263,z4,z5]),(0,[z318,z122,z1,z71,z5]),(0,[z317,z1,z4,z66,z5])]],
   [[(0,[z26,z123,z11,z2,z61]),(0,[z20,z1,z2,z253,z5]),(0,[z0,z1,z254,z4,z5]),(0,[z53,z123,z2,z4,z5])],[(0,[z14,z11,z2,z4,z230]),(0,[z317,z1,z4,z114,z5]),(0,[z304,z122,z1,z11,z61])],[(0,[z1830,z1,z11,z4,z5]),(0,[z58,z2,z12,z59,z200]),(0,[z1831,z1,z11,z4,z5]),(0,[z1832,z1,z11,z4,z5]),(0,[z159,z350,z11,z4,z77]),(0,[z122,z1,z1833,z4,z5]),(0,[z310,z78,z11,z2,z5])],[(0,[z26,z1,z140,z4,z5]),(0,[z39,z1,z4,z382,z5])],[(0,[z1733,z1,z38,z4,z5]),(0,[z163,z1,z1546,z4,z5])],[(0,[z26,z1,z1264,z4,z5])],[(0,[z1834,z1,z11,z4,z5]),(0,[z159,z317,z1,z4,z5]),(0,[z1428,z1143,z2,z4,z5])],[(0,[z26,z1,z840,z4,z5]),(0,[z1835,z11,z12,z4,z5]),(0,[z1836,z1,z2,z4,z5]),(0,[z1717,z1,z11,z4,z5]),(0,[z1,z2,z12,z1837,z5]),(0,[z1,z2,z12,z167,z41]),(0,[z1,z11,z12,z562,z443])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 32 1024 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 1 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 1 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa1 : chunkB SA 2 ((parents.drop 9).take 9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa2 : chunkB SA 2 ((parents.drop 18).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa3 : chunkB SA 2 ((parents.drop 25).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa4 : chunkB SA 2 ((parents.drop 33).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa5 : chunkB SA 2 ((parents.drop 40).take 8) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa6 : chunkB SA 2 ((parents.drop 48).take 9) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa7 : chunkB SA 2 ((parents.drop 57).take 7) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa8 : chunkB SA 2 ((parents.drop 64).take 2) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 66)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [9, 9, 7, 8, 7, 8, 9, 7, 2] = true :=
  windowsG_cons pa0 (windowsG_cons pa1 (windowsG_cons pa2 (windowsG_cons pa3 (windowsG_cons pa4 (windowsG_cons pa5 (windowsG_cons pa6 (windowsG_cons pa7 (windowsG_cons pa8 (windowsG_nil paend)))))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 632) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 632).take 636) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1268).take 635) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1903).take 636) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb4 : chunkB SB 1 ((bkA.flatten.flatten.drop 2539).take 632) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb5 : chunkB SB 1 ((bkA.flatten.flatten.drop 3171).take 299) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 3470)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [632, 636, 635, 636, 632, 299] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_cons pb4 (windowsG_cons pb5 (windowsG_nil pbend))))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 4 ((bkB.flatten.drop 0).take 115).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 4 ((bkB.flatten.drop 115).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 4 ((bkB.flatten.drop 241).take 15).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 4 bkB.flatten 0 [115, 126, 15] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 1) (J := 4) (d := 2) (g1 := 32) (nb1 := 1024) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38713

theorem PEqualNP.Outside.L_meta_38713 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808424 * 2 ^ 32 + 3941264104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808424 * 2 ^ 32 + 3941264104) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38713.solve