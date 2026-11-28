import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36753

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
  Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x9400000002001025#64 ++ 0xfffe44e71e88f1ff#64 : BitVec 128),
   (0x485c194a68334692#64 ++ 0x4fffbb5ae9774e93#64 : BitVec 128),
   (0x6208c294b1858b18#64 ++ 0x737bc39cf1878f1c#64 : BitVec 128),
   (0x0090ec1f01d80dc0#64 ++ 0x82d7fc1f01f80fe0#64 : BitVec 128),
   (0x00e0f7e001eee000#64 ++ 0x01ceffe001fff000#64 : BitVec 128),
   (0x0300ffffdc000000#64 ++ 0x003efffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0000f7e000000000 0x000effe000000000

def z1 : W := mkw 0x0090ec1f01d80dc0 0x82d7fc1f01f80fe0

def z2 : W := mkw 0x00e0f7e001eee000 0x01ceffe001fff000

def z3 : W := mkw 0x03e0ffffddeee000 0x01fefffffffff000

def z4 : W := mkw 0x485c194a68334692 0x4fffbb5ae9774e93

def z5 : W := mkw 0x6208c294b1858b18 0x737bc39cf1878f1c

def z6 : W := mkw 0x9400000002001025 0xfffe44e71e88f1ff

def z7 : W := mkw 0x0080e41501c80940 0x8000440500880160

def z8 : W := mkw 0x0300ffffdc000000 0x003efffffe000000

def z9 : W := mkw 0x484c114068234212 0x4d280340e8074013

def z10 : W := mkw 0x0000000000000000 0x003e44e71e000000

def z11 : W := mkw 0x6208c294b1858b18 0x737fc7ffff878f1c

def z12 : W := mkw 0x2200c29491848908 0x300040841080810c

def z13 : W := mkw 0x6208c294b1858b18 0x00018318e1070e00

def z14 : W := mkw 0x0010080a00100480 0x02d7b81a01700e80

def z15 : W := mkw 0x0010081f00100dc0 0x8211001f00000fe0

def z16 : W := mkw 0x6008000020058218 0x710000000007801c

def z17 : W := mkw 0x00e0e40001eee000 0x01c6fc0001fff000

def z18 : W := mkw 0x9400000002001025 0xfe3000071e0001ff

def z19 : W := mkw 0x485c194a68334692 0x0001bb18e1770e00

def z20 : W := mkw 0x0200c29490000000 0x003ac39cf0000000

def z21 : W := mkw 0x4b5cfffffc334692 0x4fffffffff774e93

def z22 : W := mkw 0x00902c0b005804c0 0x80843c03007800e0

def z23 : W := mkw 0x62080280b0058218 0x71280380f007801c

def z24 : W := mkw 0x62e8f7f4b1efeb18 0x73fffffcf1ffff1c

def z25 : W := mkw 0x0090080a01d80dc0 0x82d7b81a01f80fe0

def z26 : W := mkw 0x0b54ffffdc324482 0x0cbefffffe704083

def z27 : W := mkw 0x0000000000000000 0x737a40841080811c

def z28 : W := mkw 0xf608c294b3859b3d 0xffffc7ffff8fffff

def z29 : W := mkw 0x62080014b1858b18 0x7371001cf1878f1c

def z30 : W := mkw 0x0000000000000000 0x01ce44e00088f000

def z31 : W := mkw 0x94e0f7e003eef025 0xfffeffe71ffff1ff

def z32 : W := mkw 0x00902c0b005804c0 0x82d7bc1b01780ee0

def z33 : W := mkw 0x0000000000000000 0x4ffe004208004093

def z34 : W := mkw 0x0300ffffdc000000 0x0000ffbdf6000000

def z35 : W := mkw 0x484c114068234212 0x4ffe0342e8074093

def z36 : W := mkw 0x0300081fdc000000 0x0030001ffe000000

def z37 : W := mkw 0x0090ec1f01d80dc0 0xcffffc5f09f84ff3

def z38 : W := mkw 0x48dcfd5f69fb4fd2 0xcfffff5fe9ff4ff3

def z39 : W := mkw 0x481c080a68110692 0x4f7b831ae9070e93

def z40 : W := mkw 0x00e0114001eee000 0x01cebb4001fff000

def z41 : W := mkw 0x6a5cdbdef9b7cf9a 0x737bfb9cf1f78f1c

def z42 : W := mkw 0x6298ee9fb1dd8fd8 0xf3ffff9ff1ff8ffc

def z43 : W := mkw 0x48fcf7e021ffe692 0x4fcfffe001fffe93

def z44 : W := mkw 0x6308fffffd858b18 0x737fffffff878f1c

def z45 : W := mkw 0x970013e0de001025 0x7d2803e0fe00f01f

def z46 : W := mkw 0x0000194a48000000 0x003efffffe000000

def z47 : W := mkw 0x0090ec1f01d80dc0 0x0001b81801700e00

def z48 : W := mkw 0x48ecf7e069efe212 0x4deeffe0e9fff013

def z49 : W := mkw 0x006013e00026e000 0x010803e00007f000

def z50 : W := mkw 0x0090000001d80dc0 0x82c1000001f80fe0

def z51 : W := mkw 0x0000194a48000000 0x003ebb5ae8000000

def z52 : W := mkw 0x0300ffffdc000000 0x0000bb18e0000000

def z53 : W := mkw 0x9700ffffde001025 0xfffefffffe88f1ff

def z54 : W := mkw 0x0000194a48000000 0x4ffebb5ae8004093

def z55 : W := mkw 0x0310ffffdc100dc0 0x823ffffffe000fe0

def z56 : W := mkw 0x62080280b0058218 0x737b8398f1078e1c

def z57 : W := mkw 0x0200c29490000000 0x003ec7fffe000000

def z58 : W := mkw 0x030013e0dc000000 0x002803e0fe000000

def z59 : W := mkw 0x03e0f7e0ddeee000 0x01eeffe0fffff000

def z60 : W := mkw 0x0000000000000000 0x000404630e000000

def z61 : W := mkw 0x6a5cdbdef9b7cf9a 0x7ffffbdef9f7cf9f

def z62 : W := mkw 0xf708ffffff859b3d 0xffffffffff8fffff

def z63 : W := mkw 0x01003d6b4c000000 0x00043c630e000000

def z64 : W := mkw 0x0000000000000000 0xf3fe4487108881fc

def z65 : W := mkw 0x62080014b0010b18 0x7231001cf0000f1c

def z66 : W := mkw 0x0854194a48324482 0x0dcebb4209774083

def z67 : W := mkw 0x00e0f7e001eee000 0x01c0bb0001fff000

def z68 : W := mkw 0x0000f7e000000000 0x01ceffe00088f000

def z69 : W := mkw 0xfe5cdbdefbb7dfbf 0xffffffffffffffff

def z70 : W := mkw 0x6208c294b1858b18 0x7fffc3def987cf9f

def z71 : W := mkw 0x00f0ffff01feedc0 0x83dfffff01ffffe0

def z72 : W := mkw 0x481c080a68110692 0x4e31001ae8000e93

def z73 : W := mkw 0x0854194a48324482 0x0c84384208704083

def z74 : W := mkw 0x6008000021858b18 0x7341000001878f1c

def z75 : W := mkw 0x9400000002001025 0xffc000000088f1ff

def z76 : W := mkw 0x0390ffffddd80dc0 0x82fffffffff80fe0

def z77 : W := mkw 0x9400000002001025 0x0c0000600e007003

def z78 : W := mkw 0x6208c294b0010b18 0x723bc39cf0000f1c

def z79 : W := mkw 0x485c194a68334692 0x4ffffffae9fffe93

def z80 : W := mkw 0xdc5c194a6a3356b7 0xffffbb5ae9ffffff

def z81 : W := mkw 0x00e0f7e001eee000 0x0000bb0001770000

def z82 : W := mkw 0x03003d7fdc000000 0x00343c7ffe000000

def z83 : W := mkw 0x0300ffffdc000000 0x0030bb1ffe000000

def z84 : W := mkw 0xdc1c080a6a1116b7 0xfe31001ffe000fff

def z85 : W := mkw 0xdc5c194a6a3356b7 0xffffffffffffffff

def z86 : W := mkw 0x00e0f7e001eee000 0x000effe001770000

def z87 : W := mkw 0x2300ffffdd848908 0x303efffffe80810c

def z88 : W := mkw 0x0000000000000000 0x82d64407008801e0

def z89 : W := mkw 0x0000000000000000 0x82fe44e71e8801e0

def z90 : W := mkw 0x0000ec1f00000000 0x0016fc1f00000000

def z91 : W := mkw 0x9700081fde001025 0xfe30001ffe0001ff

def z92 : W := mkw 0xdc4c11406a235237 0x7d2803e0fe07f01f

def z93 : W := mkw 0x94a0e6a003ccb025 0xfffe44e71e88f1ff

def z94 : W := mkw 0x00e0f7e001eee000 0x4ffeffe209fff093

def z95 : W := mkw 0x6308d3f4fd858b18 0x737bc3fcff878f1c

def z96 : W := mkw 0x485c194a68334692 0x0c85bb5ae9774e83

def z97 : W := mkw 0x6208c294b1858b18 0x73ffc7fcf18fff1c

def z98 : W := mkw 0x9400000002001025 0xf37a44a51688b17c

def z99 : W := mkw 0x485cfd5f68334692 0x4fffff5fe9774e93

def z100 : W := mkw 0x9400000002001025 0x7d2800e01e00f01f

def z101 : W := mkw 0x0300f7e0dc000000 0x002effe0fe000000

def z102 : W := mkw 0x9490ec1f03d81de5 0xfffffcff1ff8ffff

def z103 : W := mkw 0x0300d3f4dc000000 0x003ac3fcfe000000

def z104 : W := mkw 0x0040114000224000 0x01cebb4001774000

def z105 : W := mkw 0x48fcffea69ffe692 0x4ffffffae9fffe93

def z106 : W := mkw 0x4b5c1beafc334692 0x4fffbbfaff774e93

def z107 : W := mkw 0x4b4cfffffc234212 0x4d3efffffe074013

def z108 : W := mkw 0x0390ffffddd80dc0 0x0001bb18e1700e00

def z109 : W := mkw 0x6288e695b1cd8b58 0xf37bc79df18f8f7c

def z110 : W := mkw 0x0000c01401800900 0x0253c01c01800f00

def z111 : W := mkw 0x485c194a68334692 0xcfffff5fe9ff4ff3

def z112 : W := mkw 0x0300081fdc000000 0x00000018e0000000

def z113 : W := mkw 0x6208c294b1858b18 0x7341408411878f1c

def z114 : W := mkw 0x6008000021858b18 0x737b8318e1878f1c

def z115 : W := mkw 0xf608c294b3859b3d 0xf37bc7bdf78fbf7c

def z116 : W := mkw 0x6208c294b1858b18 0x71298398f1078e1c

def z117 : W := mkw 0x03e0ffffdc6a6000 0x00befffffe787000

def z118 : W := mkw 0x0290ee9f91d80dc0 0x82ffff9ff1f80fe0

def z119 : W := mkw 0x0010000000100480 0x02c1000001700e80

def z120 : W := mkw 0x40e8f7e021efe210 0x43fffff8e1fffe10

def z121 : W := mkw 0x0080e40001c80000 0x00c6fc0001f80000

def z122 : W := mkw 0x00e0000001eee000 0x01c0000001fff000

def z123 : W := mkw 0x00f0f7e001feedc0 0x83cfffe001ffffe0

def z124 : W := mkw 0x0000c01401800900 0x0000400400800100

def z125 : W := mkw 0x0300ffffdc000000 0x003ebb5ae8000000

def z126 : W := mkw 0x030002a094000000 0x000000a016000000

def z127 : W := mkw 0x485c194a68334692 0x4d29bb58e9774e13

def z128 : W := mkw 0x00e0f7e001eee000 0x01feffe71ffff000

def z129 : W := mkw 0x485c194a68334692 0x4fffffffff774e93

def z130 : W := mkw 0x03001bffdc000000 0x003803fffe000000

def z131 : W := mkw 0x0080e41401c80900 0x02d7fc1c01f80f00

def z132 : W := mkw 0x0200028090000000 0x00280380f0000000

def z133 : W := mkw 0x03e0ffffddeee000 0x003effffff770000

def z134 : W := mkw 0x94e03560026a7025 0xfffe7ce71ef8f1ff

def z135 : W := mkw 0x00a0e6a001cca000 0x000044a00088b000

def z136 : W := mkw 0x00b0eebf01dcadc0 0x82d7fcbf01f8bfe0

def z137 : W := mkw 0x0010c81f01900dc0 0x8253c01f01800fe0

def z138 : W := mkw 0x0380ffffddc80000 0x00fefffffff80000

def z139 : W := mkw 0x0300ffffdc000000 0x0028bbf8fe000000

def z140 : W := mkw 0x9410080a021014a5 0xfffffcff1ff8ffff

def z141 : W := mkw 0x0844114048224002 0x0c00004008004003

def z142 : W := mkw 0x62e8f7e0b1efe218 0x71eeffe0f1fff01c

def z143 : W := mkw 0x94a0e6a003ccb025 0xb00044a51688b16c

def z144 : W := mkw 0x0300e6b594000000 0x000044a516000000

def z145 : W := mkw 0x0090ec1f01d80dc0 0x82fffcff1ff80fe0

def z146 : W := mkw 0x00e0f7e0006a6000 0x008effe000787000

def z147 : W := mkw 0x030013e0dc000000 0x003e47e7fe000000

def z148 : W := mkw 0x00a0e6a001cca000 0x0000000000000000

def z149 : W := mkw 0x0040194a48224000 0x01febb5ae9774000

def z150 : W := mkw 0x9400000002001025 0xb1ce44e51688f16c

def z151 : W := mkw 0x9700081fde001025 0xfffe44fffe88f1ff

def z152 : W := mkw 0x0060d3e001a6e000 0x014ac3e00187f000

def z153 : W := mkw 0x0000000000000000 0x4e30000208000093

def z154 : W := mkw 0x0300eebf94000000 0x0016fcbf16000000

def z155 : W := mkw 0x0300eebfdc000000 0x003044bffe000000

def z156 : W := mkw 0x0010000000100dc0 0x8201000000000fe0

def z157 : W := mkw 0x4008000020010210 0x737bc39cf1878f1c

def z158 : W := mkw 0x9400000002001025 0x8c8404630e0870e3

def z159 : W := mkw 0x62080000b0010218 0x70200000f000001c

def z160 : W := mkw 0x03a0e6b595cca000 0x000044a51688b000

def z161 : W := mkw 0x6008c28021858b18 0x734bc38001878f1c

def z162 : W := mkw 0x00e0e6a001eee000 0x01c044a001fff000

def z163 : W := mkw 0x9700ffffde001025 0xb03efffffe88b16c

def z164 : W := mkw 0x9400000002001025 0x8c0000030e0000e3

def z165 : W := mkw 0x4308fffffc010210 0x437fffffff070e10

def z166 : W := mkw 0x00e013e001eee000 0x01c803e001fff000

def z167 : W := mkw 0x0300195fdc000000 0x003ebb5ffe000000

def z168 : W := mkw 0x9400000002001025 0xb00044a51688b16c

def z169 : W := mkw 0x00e0f7e001eee000 0x010847e0008ff000

def z170 : W := mkw 0x0000000000000000 0x712800801000801c

def z171 : W := mkw 0x00e037e0006ee000 0x018c3fe0007ff000

def z172 : W := mkw 0x6008000020010b18 0x7201000000000f1c

def z173 : W := mkw 0x0390ec1fddd80dc0 0x82f7fc1ffff80fe0

def z174 : W := mkw 0x00e03560006a6000 0x00843c6000787000

def z175 : W := mkw 0x4008000020010210 0x437b8318e1070e10

def z176 : W := mkw 0x62080014b0010b18 0x737b409cf0808f1c

def z177 : W := mkw 0x62080014b0010b18 0x737b831cf1070f1c

def z178 : W := mkw 0x9400000002001025 0xffc404630e88f1ff

def z179 : W := mkw 0x9400000002001025 0xbc8444e71e88f1ef

def z180 : W := mkw 0x0000080a00000000 0x0016b81a00000000

def z181 : W := mkw 0x48dcfd5f69fb4fd2 0x4fffbb5ae9774e93

def z182 : W := mkw 0x0000c28001848000 0x0000830001070000

def z183 : W := mkw 0x946013e00226f025 0xfffe47e71e8ff1ff

def z184 : W := mkw 0x0000000000000000 0x00c6440000880000

def z185 : W := mkw 0x0000000000000000 0x0000000000000000

def z186 : W := mkw 0x0000000000000000 0x002800e01e000000

def z187 : W := mkw 0x0010194a48100480 0x02ffbb5ae9700e80

def z188 : W := mkw 0x00f03d6b007a64c0 0x80843c63007870e0

def z189 : W := mkw 0x48dcfd5f69fb4fd2 0x0001bb18e1770e00

def z190 : W := mkw 0x00a0e6a001cca000 0x00c6fca001f8b000

def z191 : W := mkw 0x0200c29490000000 0x00008318e0000000

def z192 : W := mkw 0x0000000000000000 0x0253801801000e00

def z193 : W := mkw 0xf698ee9fb3dd9ffd 0xffffffffffffffff

def z194 : W := mkw 0x62e8f7f4b1efeb18 0x0001bb18e1770e00

def z195 : W := mkw 0x0090ec1f01d80dc0 0x83dffcff01f8ffe0

def z196 : W := mkw 0x00902c0b01d80dc0 0x82c53c0301f80fe0

def z197 : W := mkw 0x00a0f7e001cca000 0x000effe00088b000

def z198 : W := mkw 0x4bdcfffffdfb4fd2 0xcfffffffffff4ff3

def z199 : W := mkw 0x01903d6b4c5804c0 0x80843c630e7800e0

def z200 : W := mkw 0x0000e41500000000 0x0000440500000000

def z201 : W := mkw 0x02e0f7f491eee000 0x01fefffcf1fff000

def z202 : W := mkw 0x0090ec1f01d80dc0 0x8001fc1d01f80f60

def z203 : W := mkw 0xf408000023859b3d 0xffc10000018fffff

def z204 : W := mkw 0x0000000000000000 0x82c00000008801e0

def z205 : W := mkw 0x0000080a48000000 0x0030001ae8000000

def z206 : W := mkw 0x485c194a68334692 0x4fc5384209774e93

def z207 : W := mkw 0x0360ffffdc26e000 0x013efffffe07f000

def z208 : W := mkw 0x0310ffffdc100480 0x02ffffffff700e80

def z209 : W := mkw 0x0000c28001848000 0x014ac38001878000

def z210 : W := mkw 0x484c114068234212 0x4deebb40e9774013

def z211 : W := mkw 0x0080e40001c80000 0x01cefce001f8f000

def z212 : W := mkw 0x9c54194a4a3254a7 0x8c843c630e7870e3

def z213 : W := mkw 0x0080e40001c80000 0x0000440000880000

def z214 : W := mkw 0x0300ec1fdc000000 0x0036fc1ffe000000

def z215 : W := mkw 0x485c114020334692 0x4fcfbb4001774e93

def z216 : W := mkw 0x0340ffffdc224000 0x01feffffff774000

def z217 : W := mkw 0x0090ee9f01dc8dc0 0x83dfff9f01ff8fe0

def z218 : W := mkw 0x0000000000000000 0x0084046000087000

def z219 : W := mkw 0xdc5c0000223356b7 0xffc1000001ffffff

def z220 : W := mkw 0x6308e6b5b5858b18 0x737bc7bdf7878f1c

def z221 : W := mkw 0x0010080a00100480 0x4fffb85a09704e93

def z222 : W := mkw 0x485c000020334692 0x4fc1000001774e93

def z223 : W := mkw 0x0090000001d80dc0 0x82d7440701f80fe0

def z224 : W := mkw 0x9700ffffde001025 0x7d3efffffe00f01f

def z225 : W := mkw 0x00e03560006a6000 0x01cebf60017f7000

def z226 : W := mkw 0x6b5cfffffdb7cf9a 0x7ffffffffff7cf9f

def z227 : W := mkw 0x2300e6b595848908 0x300044a51680810c

def z228 : W := mkw 0x010011604c000000 0x000000600e000000

def z229 : W := mkw 0x0090e40001d80dc0 0x82c7fc0001f80fe0

def z230 : W := mkw 0x6a5cc294b1b7cf9a 0x7ffbc39cf1f7cf9f

def z231 : W := mkw 0x0000000000000000 0x80840403000800e0

def z232 : W := mkw 0x01e03d6b4c6a6000 0x00843c630e787000

def z233 : W := mkw 0x2290ee9f91dc8dc8 0xb2d7fc9f11f88fec

def z234 : W := mkw 0x00a0e6b501cca940 0x800044a50088b160

def z235 : W := mkw 0x0080000001c80000 0x00c0000001f80000

def z236 : W := mkw 0x48fc194a69ffe692 0x4fffbb5ae9fffe93

def z237 : W := mkw 0x6208c294b1858b18 0x437b8318e1070e10

def z238 : W := mkw 0x03001beadc000000 0x003ebbfafe000000

def z239 : W := mkw 0x6308fffffd858b18 0x0001bb18e1070e00

def z240 : W := mkw 0x6008000021858b18 0x737b408411878f1c

def z241 : W := mkw 0x9400000002001025 0xfeb404671e0871ff

def z242 : W := mkw 0x485c194a68334692 0x4fc1bb18e1774e93

def z243 : W := mkw 0x485c194a68334692 0x7ffffbdef9f7cf9f

def z244 : W := mkw 0x0300001594000000 0x0000000516000000

def z245 : W := mkw 0x9400000002001025 0xffce44e00088f1ff

def z246 : W := mkw 0x9700e6b596001025 0xfffe44e71e88f1ff

def z247 : W := mkw 0x9400000002001025 0xffd644070088f1ff

def z248 : W := mkw 0x0380ffffddc80940 0x803efffffe880160

def z249 : W := mkw 0x036013e0dc26e000 0x012803e0fe07f000

def z250 : W := mkw 0x0010080a00100480 0x82d7fc1f01f80fe0

def z251 : W := mkw 0xdc5c0000223356b7 0xffff44e71fffffff

def z252 : W := mkw 0x0010081f00100dc0 0x82d7b81f01700fe0

def z253 : W := mkw 0x685c000021b7cf9a 0x7fc1000001f7cf9f

def z254 : W := mkw 0x00902c0b005804c0 0x82d67c0700f801e0

def z255 : W := mkw 0x62080294b0058b18 0x7339039cf0078f1c

def z256 : W := mkw 0x03000000dc000000 0x00200000fe000000

def z257 : W := mkw 0x030013e0dc000000 0x00000300e0000000

def z258 : W := mkw 0x0000000000000000 0x723000041000011c

def z259 : W := mkw 0x0090ec1f01d80dc0 0x8211b81f01700fe0

def z260 : W := mkw 0x485c194a68334692 0x4e31bb1ae9770e93

def z261 : W := mkw 0x48dc194a69fb4fd2 0xcfffbb5ae9ff4ff3

def z262 : W := mkw 0x481c081f68110fd2 0xce31001fe8000ff3

def z263 : W := mkw 0x9400ec1f02001025 0xfffefcff1e88f1ff

def z264 : W := mkw 0x0300ffffdd848000 0x017effffff878000

def z265 : W := mkw 0x481c080a68110692 0x4ef7b81ae9700e93

def z266 : W := mkw 0x0000fd5f48000000 0x003eff5fe8000000

def z267 : W := mkw 0x00e0356001eee000 0x01c43c6001fff000

def z268 : W := mkw 0x0000001400000900 0x0211001c00000f00

def z269 : W := mkw 0x03a0ffffddcca000 0x003efffffe88b000

def z270 : W := mkw 0x08f43d6a487a6482 0x0c843c6208787083

def z271 : W := mkw 0x0200001490000000 0x0030001cf0000000

def z272 : W := mkw 0x0100080b4c000000 0x000000030e000000

def z273 : W := mkw 0x0010ec1f00100480 0x02d7fc1f01700e80

def z274 : W := mkw 0x03e0f7f595eee000 0x01ceffe517fff000

def z275 : W := mkw 0x0000000000000000 0x83de44e70088f1e0

def z276 : W := mkw 0x6208c294b1858b18 0x71284384f087811c

def z277 : W := mkw 0x0000000000000000 0x8000440500880160

def z278 : W := mkw 0x0000f7e000000000 0x003effe71e000000

def z279 : W := mkw 0x01003d6b4c000000 0x003ebf7bee000000

def z280 : W := mkw 0x0090ec1f01d80dc0 0xf3fffc9f11f88ffc

def z281 : W := mkw 0x9400000002001025 0xfffe00420888f1ff

def z282 : W := mkw 0x4b5cfffffc334692 0x4fffbb5ae9774e93

def z283 : W := mkw 0x0000000000000000 0x0c84004208004083

def z284 : W := mkw 0x6288e694b1cd8b18 0x73ffff9cf1ff8f1c

def z285 : W := mkw 0x6208c294b1858b18 0xf3ffc79ff18f8ffc

def z286 : W := mkw 0x006013e00026e000 0x01ce47e0008ff000

def z287 : W := mkw 0xf6080014b2011b3d 0xfe31001ffe000fff

def z288 : W := mkw 0x0000c01400000000 0x0012c01c00000000

def z289 : W := mkw 0x485c000020334692 0x0001000001770e00

def z290 : W := mkw 0x0300ffffdc000000 0x00047ce71e000000

def z291 : W := mkw 0x00e0f7e001eee000 0x01cebb4001774000

def z292 : W := mkw 0x626813e0b027e218 0x712803e0f007f01c

def z293 : W := mkw 0x9400000002001025 0x8c800000000870e3

def z294 : W := mkw 0x6208c294b1858b18 0x3001c39cf1878f0c

def z295 : W := mkw 0x48fc000021ffe692 0x4fc1000001fffe93

def z296 : W := mkw 0x6098000021dd8fd8 0xf3c1000001ff8ffc

def z297 : W := mkw 0x0080ec1f01c80000 0x00d6fc1f01f80000

def z298 : W := mkw 0x0000194a48000000 0x0000bb18e0000000

def z299 : W := mkw 0x00e0000001eee000 0x01ce44e001fff000

def z300 : W := mkw 0x485c080a20334692 0x4fd7b81a01774e93

def z301 : W := mkw 0x0040114000224000 0x0000bb0001770000

def z302 : W := mkw 0x0200f7f490000000 0x003efffcf0000000

def z303 : W := mkw 0x0300ffffdc000000 0x4ffefffffe004093

def z304 : W := mkw 0x487c1bea6837e692 0x4fffbbfae977fe93

def z305 : W := mkw 0x0040114000224000 0x0108034000074000

def z306 : W := mkw 0x4b5cfffffc334692 0x0001bb18e1770e00

def z307 : W := mkw 0x0300081fdc000000 0x003e44fffe000000

def z308 : W := mkw 0x9480e40003c81025 0xfffefce71ff8f1ff

def z309 : W := mkw 0x4008000020010210 0x00018318e1070e00

def z310 : W := mkw 0x0040000000224000 0x01c0000001774000

def z311 : W := mkw 0x0090ec1f01d80dc0 0x8211441f00880fe0

def z312 : W := mkw 0x0090000001d80dc0 0x0001000001700e00

def z313 : W := mkw 0x0000ec1f01800900 0x0257fc1f01800f00

def z314 : W := mkw 0xf608c294b3859b3d 0x7f7bc3fcff87ff1f

def z315 : W := mkw 0x0010c81e01900d80 0x02d7f81e01f00f80

def z316 : W := mkw 0xb600c2949384992d 0xfffe44e71e88f1ff

def z317 : W := mkw 0x484c114068234212 0x00000300e0070000

def z318 : W := mkw 0x4bfcfffffdffe692 0x4ffffffffffffe93

def z319 : W := mkw 0x48dc000021fb4fd2 0xcfc1000001ff4ff3

def z320 : W := mkw 0x0090ec1f01d80dc0 0x00c7fc1801f80e00

def z321 : W := mkw 0xf408000023859b3d 0xffff44e71f8fffff

def z322 : W := mkw 0x0390ffffddd80dc0 0x82d7ff1fe1f80fe0

def z323 : W := mkw 0x00e0f7e001eee000 0x0084bf60017f7000

def z324 : W := mkw 0x0200dbded8000000 0x003efbdef8000000

def z325 : W := mkw 0x00e0f7e001eee000 0x83deffe701fff1e0

def z326 : W := mkw 0x006000000026e000 0x010000000007f000

def z327 : W := mkw 0x9400c01403801925 0xffffc4ff1f88ffff

def z328 : W := mkw 0x95003d6b4e001025 0x8c843c630e0870e3

def z329 : W := mkw 0x0300e6b594000000 0x003e44e71e000000

def z330 : W := mkw 0x94902c0b025814e5 0x8c843c630e7870e3

def z331 : W := mkw 0x00e03560006a6000 0x0000380000700000

def z332 : W := mkw 0x62080280b0058218 0x00000300e0070000

def z333 : W := mkw 0x0300ffffdc000000 0x82fefffffe8801e0

def z334 : W := mkw 0x6a1cca9ef9958f9a 0x7f7bc39ef9878f9f

def z335 : W := mkw 0xf6080014b2011b3d 0xffff44fffe88ffff

def z336 : W := mkw 0x0000356000000000 0x00043c6000000000

def z337 : W := mkw 0x00e0ffff01eee000 0x01deffff01fff000

def z338 : W := mkw 0x0300f7f5dc000000 0x002847e5fe000000

def z339 : W := mkw 0x9400000002001025 0xb00000000088b16c

def z340 : W := mkw 0x00f0000001feedc0 0x83c1000001ffffe0

def z341 : W := mkw 0x0090081f01d80dc0 0x82d1001f01f80fe0

def z342 : W := mkw 0x0300ca9fdc000000 0x003ac39ffe000000

def z343 : W := mkw 0x0090ec1f01d80dc0 0x82c1b81801f80fe0

def z344 : W := mkw 0x00902c0b005804c0 0x0000380000700000

def z345 : W := mkw 0xb600c2949384992d 0xb00044a51688b16c

def z346 : W := mkw 0x0390ffffdc5804c0 0x80befffffe7800e0

def z347 : W := mkw 0x0000ec1f00000000 0x003efcff1e000000

def z348 : W := mkw 0x485c194a68334692 0x4f39035ae8074e93

def z349 : W := mkw 0x0080e41501c80940 0x80c6fc0501f80160

def z350 : W := mkw 0x9400c28003849025 0xfffec7e71f8ff1ff

def z351 : W := mkw 0x0000000000000000 0x300040841080810c

def z352 : W := mkw 0x62e8c294b1efeb18 0x73fbc39cf1ffff1c

def z353 : W := mkw 0x0080e41501c80940 0x82d64407008801e0

def z354 : W := mkw 0x03f0ffffddfeedc0 0x83ffffffffffffe0

def z355 : W := mkw 0x0000000000000000 0x437a000000000010

def z356 : W := mkw 0xf6080280b205923d 0xfffe47e7fe8ff1ff

def z357 : W := mkw 0x9400000002001025 0x7d0000000000f01f

def z358 : W := mkw 0x0300e6b594000000 0x003ac7bdf6000000

def z359 : W := mkw 0x4008000020010210 0x41280300e0070010

def z360 : W := mkw 0x03003febdc000000 0x002c3fe3fe000000

def z361 : W := mkw 0x2200c29491848908 0x314ac3841187810c

def z362 : W := mkw 0x9700ffffde001025 0xfe3efffffe0001ff

def z363 : W := mkw 0x9600c29492001025 0xfffec7fffe88f1ff

def z364 : W := mkw 0x0000000000000000 0x010800e00000f000

def z365 : W := mkw 0x0090ec1f01d80dc0 0x8085bc1b01780ee0

def z366 : W := mkw 0xd408000022011235 0xffffc7ffff8fffff

def z367 : W := mkw 0x0000000000000000 0x01fe44e71e88f000

def z368 : W := mkw 0x0310081fdc100dc0 0x8231001ffe000fe0

def z369 : W := mkw 0x08d43d4b487a44c2 0x8c843c43087840e3

def z370 : W := mkw 0xdc1c080a6a1116b7 0xffff44fffe88ffff

def z371 : W := mkw 0x94e0f7e003eef025 0xb1ceffe517fff16c

def z372 : W := mkw 0x0300f7f594000000 0x000effe516000000

def z373 : W := mkw 0x6308ca9ffd858b18 0x737bc39fff878f1c

def z374 : W := mkw 0x0010081f00100dc0 0x82d7441f00880fe0

def z375 : W := mkw 0x9c54194a4a3254a7 0xfffe7ce71ef8f1ff

def z376 : W := mkw 0x0300ffffdc000000 0x01fefffffe88f000

def z377 : W := mkw 0x4048114020234210 0x43ffbb58e1774e10

def z378 : W := mkw 0x9400000002001025 0x8dce44e30e88f0e3

def z379 : W := mkw 0x6adcffdff9ffcfda 0xffffffdff9ffcfff

def z380 : W := mkw 0x97e0ffffdfeef025 0xfffefffffffff1ff

def z381 : W := mkw 0x9400000002001025 0xb03e44e71e88b16c

def z382 : W := mkw 0x4008c28021858210 0x437bc398e1878e10

def z383 : W := mkw 0x00e0f7f501eee940 0x81ceffe501fff160

def z384 : W := mkw 0x0300ffffdd800900 0x027fffffff800f00

def z385 : W := mkw 0x9700e6b596001025 0xb00044a51688b16c

def z386 : W := mkw 0x485c194a68334692 0x437bbb18e1770e10

def z387 : W := mkw 0x0090ec0a01d80480 0x02d7fc1a01f80e80

def z388 : W := mkw 0x62a8e6b4b1cdab18 0x737bc7bcf18fbf1c

def z389 : W := mkw 0x9790ffffdfd81de5 0xfffffffffff8ffff

def z390 : W := mkw 0x0390ffffddd80dc0 0x003fffffff700e00

def z391 : W := mkw 0x485cdbca69b7c692 0x4ffffbdae9f7ce93

def z392 : W := mkw 0x485c194a68334692 0x003fbb5ae9770e00

def z393 : W := mkw 0x0100ffeb4c000000 0x000effe30e000000

def z394 : W := mkw 0x6afcfffef9ffef9a 0x7ffffffef9ffff9f

def z395 : W := mkw 0x48fcffff69ffefd2 0xcfffffffe9fffff3

def z396 : W := mkw 0x94e0f7e003eef025 0x8dceffe30ffff0e3

def z397 : W := mkw 0x006013e00026e000 0x01cebbe00177f000

def z398 : W := mkw 0x9490ec1f03d81de5 0xb2d7fcbf17f8bfec

def z399 : W := mkw 0x0380e6b595c80940 0x800044a516880160

def z400 : W := mkw 0x9400000002001025 0xfef644071e8801ff

def z401 : W := mkw 0x000013e000000000 0x000803e000000000

def z402 : W := mkw 0x00e0f7e001eee000 0x0108bbe00177f000

def z403 : W := mkw 0x0300ffffdc000000 0x737efffffe80811c

def z404 : W := mkw 0x6308fffffd858b18 0x003fffffff070e00

def z405 : W := mkw 0x00e0f7e001eee000 0x014afb8001f78000

def z406 : W := mkw 0x0080e68001cc8000 0x01ceff8001ff8000

def z407 : W := mkw 0x0854000000324482 0x0c80000000704083

def z408 : W := mkw 0x00f0ffeb01fee4c0 0x81ceffe301fff0e0

def z409 : W := mkw 0x6a5cdbdef9b7cf9a 0x4fffbb5ae9774e93

def z410 : W := mkw 0x485c194a68334692 0x01cfbb58e1774e00

def z411 : W := mkw 0x0200c29490000000 0x737ac39cf080811c

def z412 : W := mkw 0x62e8f7f4b1efeb18 0x01cffff8e1fffe00

def z413 : W := mkw 0x4b4c13e0fc234212 0x4d2803e0fe074013

def z414 : W := mkw 0x0080e41501c80940 0x0000000000000000

def z415 : W := mkw 0x0000000000000000 0x014a408000808000

def z416 : W := mkw 0x0080e40001c80000 0x82d6fc0701f801e0

def z417 : W := mkw 0x0300e6b594000000 0x0000000000000000

def z418 : W := mkw 0x0010080a00100480 0x0001b81801700e00

def z419 : W := mkw 0x0000081f00000000 0x0010001f00000000

def z420 : W := mkw 0x22a0e6b491cca908 0x300044a41088b10c

def z421 : W := mkw 0x9400000002001025 0xff3800e71e00f1ff

def z422 : W := mkw 0x0000000000000000 0x014a830001070000

def z423 : W := mkw 0x0040114000224000 0x0084384000704000

def z424 : W := mkw 0x630813e0fc058218 0x712803e0fe07801c

def z425 : W := mkw 0x00e0f56001ea6000 0x00c6fc6001f87000

def z426 : W := mkw 0x0000e40000000000 0x0006fc0000000000

def z427 : W := mkw 0x484c000020234212 0x4d00000000074013

def z428 : W := mkw 0xdcdcfd5f6bfb5ff7 0xffffffffffffffff

def z429 : W := mkw 0x9400000002001025 0xcffe04630e0870f3

def z430 : W := mkw 0x63e8fffffdefeb18 0x73ffffffffffff1c

def z431 : W := mkw 0x9400000002001025 0x8cbe44e71e0870e3

def z432 : W := mkw 0x6298ee9fb1dd8fd8 0x737bfb9cf1f78f1c

def z433 : W := mkw 0x0010081f00100dc0 0x0001001800000e00

def z434 : W := mkw 0x00e0f7f401eee900 0x03dffffc01ffff00

def z435 : W := mkw 0x48fc3d6a687b6692 0x4fffbf7ae97f7e93

def z436 : W := mkw 0x6218ca9eb1958f98 0x73fffb9ef1f78f9c

def z437 : W := mkw 0x01e0ffeb4deee000 0x01ceffe30ffff000

def z438 : W := mkw 0x00e0f7e001eee000 0x00847ce000f8f000

def z439 : W := mkw 0x6a5cdbdef9b7cf9a 0x0001bb18e1770e00

def z440 : W := mkw 0x00e0f7e001eee000 0x00c6ff0001ff0000

def z441 : W := mkw 0x0080f7e001c80000 0x00ceffe001f80000

def z442 : W := mkw 0x00d0fd5f01fa4dc0 0x83dfff5f01ff4fe0

def z443 : W := mkw 0x0000ec1f00000000 0x82d6fc1f008801e0

def z444 : W := mkw 0x0000000000000000 0x00c6b80001700000

def z445 : W := mkw 0x0050194a00324480 0x03dfbb5a01774e80

def z446 : W := mkw 0x62080280b1858b18 0x73690380f1878f1c

def z447 : W := mkw 0x489cec1f69d90fd2 0xcef7fc1fe9f80ff3

def z448 : W := mkw 0x0000000000000000 0x01ce004000004000

def z449 : W := mkw 0x9440114002225025 0xfffeffe71ffff1ff

def z450 : W := mkw 0x0000c01401800900 0x737bc09c11808f1c

def z451 : W := mkw 0x95003d6b4e001025 0xfffe7ce71e88f1ff

def z452 : W := mkw 0x0060116000226000 0x0000006000007000

def z453 : W := mkw 0x485cd95e69b34f92 0x4ffffb5ee9f74f93

def z454 : W := mkw 0x0000001500000940 0x8000000500000160

def z455 : W := mkw 0x00e0ffea49eee000 0x01fefffae9fff000

def z456 : W := mkw 0x495c3d6b6c334692 0x4fffbf7bef774e93

def z457 : W := mkw 0x0000f7e000000000 0x0000bb0000000000

def z458 : W := mkw 0x486c13e06827e212 0x4d2803e0e807f013

def z459 : W := mkw 0x9400000002001025 0x8000042106083060

def z460 : W := mkw 0x0080000001c80940 0x8000000000880160

def z461 : W := mkw 0x484c114068234212 0x4f7b8358e9074e13

def z462 : W := mkw 0x0090ec0b01d804c0 0x80c6fc0301f800e0

def z463 : W := mkw 0x4208c294b0010210 0x437bc39cf1070e10

def z464 : W := mkw 0x4008000020010210 0x4341000001070e10

def z465 : W := mkw 0x0080e40001c80000 0x0000b80001700000

def z466 : W := mkw 0x9410081f02101de5 0xffff44ff1e88ffff

def z467 : W := mkw 0x9400000002001025 0xb2d644a71688b1ec

def z468 : W := mkw 0x946013e00226f025 0x7d2803e01e07f01f

def z469 : W := mkw 0x60e8f7e021efeb18 0x73cfffe001ffff1c

def z470 : W := mkw 0x0000000000000000 0x0252400400800100

def z471 : W := mkw 0x48fcffea69ffe692 0x01cffff8e1fffe00

def z472 : W := mkw 0x00a0242000482000 0x0000042000083000

def z473 : W := mkw 0x0854194a48324482 0x0cbebb5ae8704083

def z474 : W := mkw 0x0040f7e000224000 0x01ceffe001774000

def z475 : W := mkw 0x0390eebf95d80dc0 0x82d7fcbf17f80fe0

def z476 : W := mkw 0x6a4cd3d4f9a7cb1a 0x7f7bc3dcf987cf1f

def z477 : W := mkw 0x6208c294b1858b18 0x014bc398e1878e00

def z478 : W := mkw 0x6a1c081ef8110f9a 0x7e31001ef8000f9f

def z479 : W := mkw 0x9400000002001025 0x7c2000001e00001f

def z480 : W := mkw 0x9400000002001025 0x7f7a40e41e80f11f

def z481 : W := mkw 0x94e0f7e003eef025 0x7deeffe01ffff01f

def z482 : W := mkw 0x0010ec1f00100dc0 0x8217fc1f00000fe0

def z483 : W := mkw 0x0090fd5f49d80dc0 0x82ffff5fe9f80fe0

def z484 : W := mkw 0x0300ffffdc000000 0x003afb9cf0000000

def z485 : W := mkw 0x0010080a00100480 0x0211001a00000e80

def z486 : W := mkw 0x9400000002001025 0x7d3e44e71e00f01f

def z487 : W := mkw 0x00902c1f00580dc0 0x82953c1f00780fe0

def z488 : W := mkw 0x0814080a48100482 0x0c00000208000083

def z489 : W := mkw 0x0090ec1f01d80dc0 0x0253f81c01f00f00

def z490 : W := mkw 0x4b5c195ffc334692 0x4fffbb5fff774e93

def z491 : W := mkw 0x0000c01401800900 0x82d7c41f01880fe0

def z492 : W := mkw 0x0060f7e00026e000 0x010effe00007f000

def z493 : W := mkw 0x9400000002001025 0xfdac04e31e08f0ff

def z494 : W := mkw 0x0000000000000000 0x003000071e000000

def z495 : W := mkw 0x0000000000000000 0x0016440700000000

def z496 : W := mkw 0x685c194a69b7cf9a 0x7fffbb5ae9f7cf9f

def z497 : W := mkw 0x0000ec1f00000000 0x0000b81800000000

def z498 : W := mkw 0x03e0ffffddeee000 0x0000bb18e1770000

def z499 : W := mkw 0x0000028000048000 0x0108038000078000

def z500 : W := mkw 0x48dcfd4a69fb4692 0x4fffff5ae9ff4e93

def z501 : W := mkw 0x0200c29491800900 0x027bc39cf1800f00

def z502 : W := mkw 0x4008c01421810b10 0x437bc31ce1870f10

def z503 : W := mkw 0x6a5c1bcaf837c69a 0x7fffbbdaf977ce9f

def z504 : W := mkw 0xf6e8f7f4b3effb3d 0xffffffffffffffff

def z505 : W := mkw 0x4a5cdbdef8334692 0x4ffffbdef9774e93

def z506 : W := mkw 0x0090ec1f01d80dc0 0x0017fc1f01700e00

def z507 : W := mkw 0x6208c294b1858b18 0x73418318e1878f1c

def z508 : W := mkw 0x0000000000000000 0x82100007000001e0

def z509 : W := mkw 0x970013e0de001025 0xfffe47e7fe88f1ff

def z510 : W := mkw 0x9410081f02101de5 0xfe31001f1e000fff

def z511 : W := mkw 0x0000000000000000 0x4ffe44e20888f093

def z512 : W := mkw 0x94e0000003eef025 0xffc0000001fff1ff

def z513 : W := mkw 0x0000114000000000 0x000ebb4000000000

def z514 : W := mkw 0x08d4fd5f49fa4dc2 0x8ed7fc5f09f84fe3

def z515 : W := mkw 0x0080240100480040 0x8000040100080060

def z516 : W := mkw 0x48dcfd5f69fb4fd2 0x82d7ff1fe1ff0fe0

def z517 : W := mkw 0x00900000005804c0 0x80800000007800e0

def z518 : W := mkw 0x4b1cfffffc110692 0x4e3ffffffe000e93

def z519 : W := mkw 0x6308081ffc010b18 0x7231001ffe000f1c

def z520 : W := mkw 0x6008c01421858b18 0x7353c01c01878f1c

def z521 : W := mkw 0x0000000000000000 0x02d6000200000080

def z522 : W := mkw 0x9400000002001025 0x7ffe00e21e00f09f

def z523 : W := mkw 0x0100242104000000 0x0000042106000000

def z524 : W := mkw 0x0000000001848000 0x0140000001878000

def z525 : W := mkw 0x0300ffffdc000000 0x0004bf7bee000000

def z526 : W := mkw 0x00e0f7e001eee000 0x0000ffa001ffb000

def z527 : W := mkw 0x0000e6a000000000 0x000044a000000000

def z528 : W := mkw 0x9400194a4a001025 0xfffefffffe88f1ff

def z529 : W := mkw 0x94902c0b025814e5 0xfffe7ce71ef8f1ff

def z530 : W := mkw 0x0090ffff01d80dc0 0x82dfffff01f80fe0

def z531 : W := mkw 0x6308fffffc010b18 0x723ffffffe000f1c

def z532 : W := mkw 0x00a0e6a001cca000 0x01ce44e00088f000

def z533 : W := mkw 0x9490ec1f03d81de5 0xfef7fc1f1ff80fff

def z534 : W := mkw 0xdc4c11406a235237 0xfffe47e7fe8ff1ff

def z535 : W := mkw 0x9400000002001025 0xff7a40871e8081ff

def z536 : W := mkw 0x0000c28001848000 0x01cec7e0018ff000

def z537 : W := mkw 0x9400000002001025 0xfd2844e51e88f17f

def z538 : W := mkw 0x00c0f54001ea4000 0x01ceff4001ff4000

def z539 : W := mkw 0x0090ec1f01d80dc0 0x02d7b81a01700e80

def z540 : W := mkw 0x9490000003d81de5 0xffc1000001f8ffff

def z541 : W := mkw 0x94e0000003eef025 0xfffe44e71ffff1ff

def z542 : W := mkw 0x0000000000000000 0x003e004208000000

def z543 : W := mkw 0x6008000021858b18 0x0001000001070e00

def z544 : W := mkw 0x485cffea68334692 0x4ffffffae9774e93

def z545 : W := mkw 0x0200c29491848000 0x017ac39cf1878000

def z546 : W := mkw 0x00a0e6a001cca000 0x014ac7a0018fb000

def z547 : W := mkw 0x6298ec1fb1d90fd8 0xf2f7fc1ff1f80ffc

def z548 : W := mkw 0x22e0f7f491eee908 0x31ceffe411fff10c

def z549 : W := mkw 0x9400000002001025 0xffc044a51688f1ff

def z550 : W := mkw 0x4008194a68010210 0x437fbb5ae9070e10

def z551 : W := mkw 0x0200c29490000000 0x0000408410000000

def z552 : W := mkw 0x0040114000224000 0x01ceffe001fff000

def z553 : W := mkw 0x00f0fd7f01fa6dc0 0x82d7fc7f01f87fe0

def z554 : W := mkw 0x0000114048000000 0x00280340e8000000

def z555 : W := mkw 0x0000c01401800900 0x0001801801000e00

def z556 : W := mkw 0x0854194a48324482 0x4ffe384208704093

def z557 : W := mkw 0x2200028090048008 0x300000801000800c

def z558 : W := mkw 0x00f0ffea01fee480 0x03dffffa01fffe80

def z559 : W := mkw 0x9400000002001025 0x300000a01600b00c

def z560 : W := mkw 0x0000000000000000 0x4ffe44e71e004093

def z561 : W := mkw 0x2280e69591cc8948 0xb00044851088816c

def z562 : W := mkw 0x481c080a68110692 0x4fff005ae8004e93

def z563 : W := mkw 0x62e8f7f4b1efeb18 0x737bfb9cf1f78f1c

def z564 : W := mkw 0x002002a00004a000 0x000000a00000b000

def z565 : W := mkw 0xdc5c194a6a3356b7 0x7fffbbfaff77fe9f

def z566 : W := mkw 0x485c195f68334fd2 0xcfffbb5fe9774ff3

def z567 : W := mkw 0x6208c294b1858b18 0x7231831cf1070f1c

def z568 : W := mkw 0x485c194a68334692 0x4eb5385ae8704e93

def z569 : W := mkw 0x00e0f7e001eee000 0x73feffe411fff11c

def z570 : W := mkw 0x9490000003d81de5 0xffff44e71ff8ffff

def z571 : W := mkw 0x0000000000000000 0x003a408410000000

def z572 : W := mkw 0x9400000002001025 0xfe000000000001ff

def z573 : W := mkw 0x6208c294b1858b18 0x003bc39cf1070e00

def z574 : W := mkw 0x0010080b001004c0 0x80000003000000e0

def z575 : W := mkw 0x9400000002001025 0xffe800e01e88f1ff

def z576 : W := mkw 0x62080014b0010b18 0x00010018e0000e00

def z577 : W := mkw 0x08f4ffea49fee482 0x0dceffe209fff083

def z578 : W := mkw 0x0000ffea48000000 0x003efffae8000000

def z579 : W := mkw 0x0000000000000000 0x737e44e71e80811c

def z580 : W := mkw 0x6218ca9fb1958fd8 0xf37bc39ff1878ffc

def z581 : W := mkw 0x00e0000001eee000 0x0000000001770000

def z582 : W := mkw 0xdc5c194a6a3356b7 0xffffbb5fff774fff

def z583 : W := mkw 0x485c000020334692 0x4ffb8318e1774e93

def z584 : W := mkw 0x480c000068010212 0x4c200000e8000013

def z585 : W := mkw 0x6248d3d4b1a7cb18 0x73fffbdcf1f7cf1c

def z586 : W := mkw 0x0200ee9f90000000 0x003eff9ff0000000

def z587 : W := mkw 0x6308fffffc058218 0x713efffffe07801c

def z588 : W := mkw 0x62080280b0058218 0x737a4384f087811c

def z589 : W := mkw 0x6208c014b1810b18 0x7273c01cf1800f1c

def z590 : W := mkw 0x481c000020110692 0x4e01000000000e93

def z591 : W := mkw 0x0854194a48324482 0x0ed7b85a09704e83

def z592 : W := mkw 0x0000000000000000 0x000e44e000000000

def z593 : W := mkw 0xf6080280b205923d 0x7d2803e0fe07f01f

def z594 : W := mkw 0x9700ffffde001025 0x8cbefffffe0870e3

def z595 : W := mkw 0x4b1c081ffc110692 0x4e31001ffe000e93

def z596 : W := mkw 0x6308fffffd858b18 0x737bfb9cf1878f1c

def z597 : W := mkw 0x4098ec1f21d90fd0 0xc3ffff1fe1ff0ff0

def z598 : W := mkw 0x006013e00026e000 0x0000030000070000

def z599 : W := mkw 0x2000000001848908 0x300000000080810c

def z600 : W := mkw 0x0000000000000000 0x01c000000088f000

def z601 : W := mkw 0x94e03560026a7025 0x8c843c630e7870e3

def z602 : W := mkw 0x0090ec1f01d80dc0 0x80847c0700f801e0

def z603 : W := mkw 0x485c114068334692 0x4fe90340e9774e93

def z604 : W := mkw 0x484c194a68234212 0x4d3ebb5ae8074013

def z605 : W := mkw 0x9400f7e002001025 0xfffeffe71e88f1ff

def z606 : W := mkw 0x00f0ffff01feedc0 0x01cffff801fffe00

def z607 : W := mkw 0x00e00000006a6000 0x0080000000787000

def z608 : W := mkw 0x9400000002001025 0xfe3e44e71e0001ff

def z609 : W := mkw 0x9400000002001025 0xfffe00471e0041ff

def z610 : W := mkw 0x01003d6b4c000000 0x003e7ce71e000000

def z611 : W := mkw 0x0090e41501d80dc0 0x82c1440501f80fe0

def z612 : W := mkw 0x48dc3d4b687b46d2 0xcfffbf5be97f4ef3

def z613 : W := mkw 0x6208f7f4b1858b18 0x737ffffcf1878f1c

def z614 : W := mkw 0xdcfcffea6bfff6b7 0xffffffffffffffff

def z615 : W := mkw 0x6298ee9fb1dd8fd8 0x82d7ff1fe1ff0fe0

def z616 : W := mkw 0x60e8000021efeb18 0x73c1000001ffff1c

def z617 : W := mkw 0x48dcec1f21fb4fd2 0xcfd7fc1f01ff4ff3

def z618 : W := mkw 0x9400000002001025 0xfffa40841088f1ff

def z619 : W := mkw 0x0300ffffdc000000 0x000efff8e0000000

def z620 : W := mkw 0x485c194a68334692 0x02d7bb1ae1770e80

def z621 : W := mkw 0x4b5cfffffc334692 0x003fffffff770e00

def z622 : W := mkw 0x62f8ffffb1ffefd8 0xf3fffffff1fffffc

def z623 : W := mkw 0x00f0ffff01feedc0 0x82d7ff1f01ff0fe0

def z624 : W := mkw 0x0190fd7f4dd80dc0 0x82d7fc7f0ff80fe0

def z625 : W := mkw 0xf608c294b3859b3d 0xfffbc39cf18fffff

def z626 : W := mkw 0x0080240000480000 0x00843c0000780000

def z627 : W := mkw 0x48fcffea69ffe692 0x4fffbb5ae9774e93

def z628 : W := mkw 0x0000c28001848000 0x737ac3841187811c

def z629 : W := mkw 0x9400000002001025 0x7dee44e01e88f01f

def z630 : W := mkw 0x6a4c13c0f827c21a 0x7d2803c0f807c01f

def z631 : W := mkw 0x485c080a68334692 0x4ff1001ae9774e93

def z632 : W := mkw 0x6208dbdef9858b18 0x737ffbdef9878f1c

def z633 : W := mkw 0x9490ec1f03d81de5 0xffd7fc1f01f8ffff

def z634 : W := mkw 0x0000c29401848900 0x035bc39c01878f00

def z635 : W := mkw 0x00a0000001cca000 0x000000000088b000

def z636 : W := mkw 0x6398fffffddd8fd8 0xf3ffffffffff8ffc

def z637 : W := mkw 0x48fcffea69ffe692 0x0001bb18e1770e00

def z638 : W := mkw 0x0080ec1f01c80940 0x8016fc1f00880160

def z639 : W := mkw 0x0100fd7f4c000000 0x0016fc7f0e000000

def z640 : W := mkw 0x9480e41503c81965 0xfffe44e71e88f1ff

def z641 : W := mkw 0x00e03560006a6000 0x01ce7ce000f8f000

def z642 : W := mkw 0x9490ec1f03d81de5 0x8ed7fc7f0ff87fe3

def z643 : W := mkw 0x00f0ffff01feedc0 0x0001bb1801770e00

def z644 : W := mkw 0x4018080a20110690 0x43ffbb1ae1770e90

def z645 : W := mkw 0x0080e41501c80940 0x8253c41d01880f60

def z646 : W := mkw 0x0090c01401d80dc0 0x82d3c01c01f80fe0

def z647 : W := mkw 0x481c194a68110692 0x4e3fbb5ae8000e93

def z648 : W := mkw 0x6298c294b1dd8fd8 0xf3fbc39cf1ff8ffc

def z649 : W := mkw 0x09543d6b4c324482 0x0c843c630e704083

def z650 : W := mkw 0x0000000000000000 0xcffe4447088841f3

def z651 : W := mkw 0x2200c29491848908 0x303ac39cf080810c

def z652 : W := mkw 0x00e0c28001eee000 0x01cac38001fff000

def z653 : W := mkw 0x0000000000000000 0x73fe44e41088f11c

def z654 : W := mkw 0x9400000002001025 0x8ed644670e8871e3

def z655 : W := mkw 0x0300ffffdc000000 0x0016ff1fe0000000

def z656 : W := mkw 0x2200001490000908 0x300000041000010c

def z657 : W := mkw 0x0040114000224000 0x4ffebb4209774093

def z658 : W := mkw 0x9480e41503c81965 0xb00044a51688b16c

def z659 : W := mkw 0x6098ec1f21dd8fd8 0xf3d7fc1f01ff8ffc

def z660 : W := mkw 0x0000f7e001848000 0x014effe001878000

def z661 : W := mkw 0x01003d6b4c000000 0x0000380000000000

def z662 : W := mkw 0x00002c0b00000000 0x00043c0300000000

def z663 : W := mkw 0xdc5c194a6a3356b7 0xcfffbf7bef7f7ef3

def z664 : W := mkw 0x0010080a00100480 0x0084380200700080

def z665 : W := mkw 0x6208c294b1858b18 0x7231409cf0808f1c

def z666 : W := mkw 0x0040d3c001a6c000 0x01cefbc001f7c000

def z667 : W := mkw 0x6208c294b0058218 0x713ac39cf007801c

def z668 : W := mkw 0xf608c294b3859b3d 0xff7bc39fff878fff

def z669 : W := mkw 0x94e0f7e003eef025 0xffceffe001fff1ff

def z670 : W := mkw 0x03e0ffffddeee000 0x01cefff8e1fff000

def z671 : W := mkw 0x4008000020010210 0x42310018e0000e10

def z672 : W := mkw 0x2200c29491848908 0x3253c09c11808f0c

def z673 : W := mkw 0x6208c294b1858b18 0x0253c31ce1870f00

def z674 : W := mkw 0x0000000000000000 0x000044a516000000

def z675 : W := mkw 0x6298ee9fb1dd8fd8 0x0001bb18e1770e00

def z676 : W := mkw 0x0000c28000000000 0x000ac38000000000

def z677 : W := mkw 0x0000000000000000 0x4fc0000000004093

def z678 : W := mkw 0x0090ec1f005804c0 0x8096fc1f007800e0

def z679 : W := mkw 0x0000000000000000 0x003a8318e0000000

def z680 : W := mkw 0x94f0ffff03fefde5 0xffffffff1fffffff

def z681 : W := mkw 0x0000000000000000 0x7ffe40c61880c19f

def z682 : W := mkw 0x2200c29491848908 0x0000000000000000

def z683 : W := mkw 0x9400000002001025 0xfff000071e88f1ff

def z684 : W := mkw 0x9400000002001025 0xfe3044a71e88b1ff

def z685 : W := mkw 0xdf5cfffffe3356b7 0xffffffffffffffff

def z686 : W := mkw 0x0854194a48324482 0x0000380000700000

def z687 : W := mkw 0x9400000002001025 0xb00000051600016c

def z688 : W := mkw 0x0000000001800900 0x0241000001800f00

def z689 : W := mkw 0x6208c280b1858218 0x716ac380f187801c

def z690 : W := mkw 0x00f0ec1f01feedc0 0x83d7fc1f01ffffe0

def z691 : W := mkw 0x0000000000000000 0x4d28004008004013

def z692 : W := mkw 0x6218081fb0110fd8 0xf231001ff0000ffc

def z693 : W := mkw 0x481c080a68110692 0x00010018e0000e00

def z694 : W := mkw 0x0000000000000000 0x734000000080811c

def z695 : W := mkw 0x0000194a48000000 0x0004384208000000

def z696 : W := mkw 0x0000c00001800000 0x0042c00001800000

def z697 : W := mkw 0x6208ee9fb1858b18 0x737fff9ff1878f1c

def z698 : W := mkw 0x485c000020334692 0x4fff004209774e93

def z699 : W := mkw 0x0000ffff00000000 0x001effff00000000

def z700 : W := mkw 0x485c194a68334692 0x4dac3b42e8774093

def z701 : W := mkw 0x0000c28001848000 0x0000408000808000

def z702 : W := mkw 0x6a5c195ef8334f9a 0x7fffbb5ef9774f9f

def z703 : W := mkw 0x6268d3f4b1a7eb18 0x737bc3fcf187ff1c

def z704 : W := mkw 0x0000000000000000 0x000044a00088b000

def z705 : W := mkw 0x2200c29491848908 0x737a40841080811c

def z706 : W := mkw 0x4008000020010210 0x4fff835ae9074e93

def z707 : W := mkw 0x0360ffffdc226000 0x003efffffe007000

def z708 : W := mkw 0x039013e0ddd80dc0 0x82e903e0fff80fe0

def z709 : W := mkw 0x0310081fdc1004c0 0x8030001ffe0000e0

def z710 : W := mkw 0x01003d6b4c000000 0x00343c7bee000000

def z711 : W := mkw 0x00e0f7e001eee000 0x73ceffe001fff11c

def z712 : W := mkw 0x48bceeaa69dda692 0x4e3144bae888be93

def z713 : W := mkw 0x0090ec1f01d80dc0 0x8001b81d01700f60

def z714 : W := mkw 0x485c194a68334692 0x0c01bb1ae9770e83

def z715 : W := mkw 0x9cd43d4b4a7a54e7 0x8c843c630e7870e3

def z716 : W := mkw 0x03f0ffffddfee4c0 0x81fefffffffff0e0

def z717 : W := mkw 0x006011400026e000 0x01cebb400177f000

def z718 : W := mkw 0x00e0f7e001eee000 0x01c6ff0001fff000

def z719 : W := mkw 0x03e0ffffddeee000 0x013efffffe8ff000

def z720 : W := mkw 0x6288e695b1cd8b58 0x737bc39cf1878f1c

def z721 : W := mkw 0x0090240001d80dc0 0x82c53c0001f80fe0

def z722 : W := mkw 0x0300081fdc000000 0x00200018fe000000

def z723 : W := mkw 0x0300ca9fdc000000 0x003ec7fffe000000

def z724 : W := mkw 0x00e0f7e001eee000 0x008effe0017f7000

def z725 : W := mkw 0x22e0f7f591eee948 0xb1ceffe511fff16c

def z726 : W := mkw 0x0090ec1f01d80dc0 0xf3d7fc1f01f88ffc

def z727 : W := mkw 0x0390ffffddd80dc0 0x027ffffffff00f00

def z728 : W := mkw 0x22b0eebf91dcadc8 0xb2d7fcbf11f8bfec

def z729 : W := mkw 0x0090ec1f01d80dc0 0xfffffcdf19f8cfff

def z730 : W := mkw 0x0090e40001d80dc0 0x82d7fc0701f80fe0

def z731 : W := mkw 0x03002c3fdc000000 0x0030043ffe000000

def z732 : W := mkw 0x0300ffffdc000000 0x0020bb18fe000000

def z733 : W := mkw 0xf4e8000023effb3d 0xffc1000001ffffff

def z734 : W := mkw 0x00e0f7e001eee000 0x014afbe001f7f000

def z735 : W := mkw 0x2a54dbded9b6cd8a 0x3c8478c618f0c18f

def z736 : W := mkw 0x9400000002001025 0xfe100007000001ff

def z737 : W := mkw 0x485c194a68334692 0x4ffffbdae9f7ce93

def z738 : W := mkw 0x61083d6b6d858b18 0x73453c630f878f1c

def z739 : W := mkw 0x0300ffffdd800000 0x007effffff800000

def z740 : W := mkw 0x01e0f7e04deee000 0x01ceffe00ffff000

def z741 : W := mkw 0x030013e0dc000000 0x00000360ee000000

def z742 : W := mkw 0x00e03560006ee000 0x01843c60007ff000

def z743 : W := mkw 0x03001140dc000000 0x00280340fe000000

def z744 : W := mkw 0x03001160dc000000 0x00200060fe000000

def z745 : W := mkw 0x03e0ffffddeee900 0x03ffffffffffff00

def z746 : W := mkw 0x0300ffffdc000000 0x003afbfcfe000000

def z747 : W := mkw 0x0090ec1f01d80dc0 0x83fffcff1ff8ffe0

def z748 : W := mkw 0x0390ffffddd80dc0 0x803ffffffff80f60

def z749 : W := mkw 0x0290ee9f91d80dc0 0x82fffffffff80fe0

def z750 : W := mkw 0x0310ffffdc100480 0x023ffffffe000e80

def z751 : W := mkw 0x485c194a68334692 0x4f7bbb58e9774e13

def z752 : W := mkw 0x0090ec0a01d80dc0 0x82d7fc1a01f80fe0

def z753 : W := mkw 0x0310ffffdd900d80 0x02fffffffff00f80

def z754 : W := mkw 0x03a0e6b595cca000 0x017ac7bdf78fb000

def z755 : W := mkw 0x0390eebfddd80dc0 0x82f7fcbffff80fe0

def z756 : W := mkw 0x0390ee9fddd80dc0 0x82ffff9ffff80fe0

def z757 : W := mkw 0x2390ffffdddc8dc8 0xb2fffffffff88fec

def z758 : W := mkw 0x0310081fdc100dc0 0x0031001ffe000e00

def z759 : W := mkw 0x485c194a68334692 0x7ffffffef9ffff9f

def z760 : W := mkw 0x0390eebf95d80dc0 0x82ffffbff7f80fe0

def z761 : W := mkw 0x00701bff0036edc0 0x831903ff0007ffe0

def z762 : W := mkw 0x6208c294b1858b18 0xf3fbc39cf18f8ffc

def z763 : W := mkw 0x0090ec1f01d80dc0 0x8097fc1f01780ee0

def z764 : W := mkw 0x03f0ffffddfeedc0 0x01fffffffffffe00

def z765 : W := mkw 0x0300ffffdc048000 0x013efffffe078000

def z766 : W := mkw 0x0340195fdc224000 0x01febb5fff774000

def z767 : W := mkw 0x03001beadc000000 0x003803fafe000000

def z768 : W := mkw 0x6288e694b1cd8b18 0x737bc79cf18f8f1c

def z769 : W := mkw 0x03000014dc000000 0x0030001cfe000000

def z770 : W := mkw 0x4bdcfd5ffdfb4fd2 0xcfffff5fffff4ff3

def z771 : W := mkw 0x0200001490000000 0x003e44fffe000000

def z772 : W := mkw 0x0200c29490000000 0x003ac39ffe000000

def z773 : W := mkw 0x2290ee9f91dc8dc8 0xb2ffff9ff1f88fec

def z774 : W := mkw 0x0390ffffddd80dc0 0x02ffffffff700e80

def z775 : W := mkw 0x03e0f7f4ddeee000 0x01fefffcfffff000

def z776 : W := mkw 0x485c194a68334692 0x4ff1bb1ae9774e93

def z777 : W := mkw 0x03001bffdc000000 0x002803f8fe000000

def z778 : W := mkw 0x0300081fdc000000 0x003a409ffe000000

def z779 : W := mkw 0x6208c294b1858b18 0x73fffb9cf1f78f1c

def z780 : W := mkw 0x9410080a021014a5 0x7fffb8fa1f70fe9f

def z781 : W := mkw 0xdc4c11406a235237 0x7d280340e807f01f

def z782 : W := mkw 0x0000000000000000 0x01ee44e01e88f000

def z783 : W := mkw 0x9490ec1f03d81de5 0x7d29b8f81f70fe1f

def z784 : W := mkw 0x0090ec1f49d80dc0 0x82f7fc1fe9f80fe0

def z785 : W := mkw 0x0090ec1f01d80dc0 0x82f7fc1f1ff80fe0

def z786 : W := mkw 0x0090ec1f01d80dc0 0x82c1fc1d01f80fe0

def z787 : W := mkw 0x0090ec1f01d80dc0 0x82c5bc1b01f80fe0

def z788 : W := mkw 0x485c194a68334692 0xcfffffffffff4ff3

def z789 : W := mkw 0x00e0f54001eee000 0x01ceff4001fff000

def z790 : W := mkw 0x485c194a68334692 0x4fc5bb5ae9774e93

def z791 : W := mkw 0x00e0f7e001eee000 0x43feffe001fff010

def z792 : W := mkw 0x0300d3f4dc000000 0x002843e4fe000000

def z793 : W := mkw 0x030013e0dc000000 0x4d2803e0fe004013

def z794 : W := mkw 0x0300eebfdc000000 0x003e44fffe000000

def z795 : W := mkw 0x00e03560006a6000 0x01ceffe001fff000

def z796 : W := mkw 0x62e83574b06b6b18 0x72b53c7cf0787f1c

def z797 : W := mkw 0xf408000023859b3d 0xff41000001878fff

def z798 : W := mkw 0xdcfcf7e023fff6b7 0xffcfffe001ffffff

def z799 : W := mkw 0x03e0ffffddeee000 0x013effffff77f000

def z800 : W := mkw 0x0310ffffdc100480 0x4fffffffff704e93

def z801 : W := mkw 0x0090e41501d80dc0 0x82c7fc0501f80fe0

def z802 : W := mkw 0x00e0f7e001eee000 0x83ceffe001fff1e0

def z803 : W := mkw 0x6208c294b1858b18 0x73fbc39cf18fff1c

def z804 : W := mkw 0x0010081f00100dc0 0x82d7fc1f01f80fe0

def z805 : W := mkw 0x0090ec1f01d80dc0 0xcef7fc1f09f80ff3

def z806 : W := mkw 0x03d0ffffddfa4dc0 0x83ffffffffff4fe0

def z807 : W := mkw 0x6208c294b1858b18 0x73ffc7ffff8fff1c

def z808 : W := mkw 0x2300ca9fdd848908 0x3030409ffe80810c

def z809 : W := mkw 0x94e0f7e003eef025 0xfe30bb071f7701ff

def z810 : W := mkw 0x00e0f7e001eee000 0x01ceffe30ffff000

def z811 : W := mkw 0x00e0f56001eee000 0x01c6fc6001fff000

def z812 : W := mkw 0x030013e0dc000000 0x4ffe03e2fe004093

def z813 : W := mkw 0x0894ec1f49d80dc2 0x8ed7fc1f09f80fe3

def z814 : W := mkw 0x0310ffffdc100dc0 0x82fffffffe880fe0

def z815 : W := mkw 0x0300ffffdc000000 0x003efffffe88b000

def z816 : W := mkw 0x00e01140006a6000 0x01cebb40017f7000

def z817 : W := mkw 0x03f0ffffddfeedc0 0x003fffffff770e00

def z818 : W := mkw 0x01903d6b4c5804c0 0x82ffbf7bef780ee0

def z819 : W := mkw 0xdc5c1140223356b7 0xffcfffe001ffffff

def z820 : W := mkw 0x030013e0dc000000 0x002ebbe0fe000000

def z821 : W := mkw 0x0090ec1f01d80dc0 0x82c7fc1801f80fe0

def z822 : W := mkw 0x6208c294b1858b18 0x314bc39cf1878f0c

def z823 : W := mkw 0xdc1c080a6a1116b7 0xfe31001ae8000fff

def z824 : W := mkw 0x485c194a68334692 0x4defbb58e9774e13

def z825 : W := mkw 0x487c196a68336692 0x4fffbb7ae9777e93

def z826 : W := mkw 0x00e0f7e001eee000 0x01c8bbe001fff000

def z827 : W := mkw 0x62080294b0058b18 0x737b439cf0878f1c

def z828 : W := mkw 0x0300ffffdc000000 0x803efffffe880160

def z829 : W := mkw 0x62982e8bb05d86d8 0xf1ac3f83f07f80fc

def z830 : W := mkw 0x485c194a68334692 0x4fffbb5fff774e93

def z831 : W := mkw 0x03e0ffffddeee000 0x4ffefffffffff093

def z832 : W := mkw 0x48ccf55569eb4b52 0xcd284745e88f4173

def z833 : W := mkw 0x00e0f7e001eee000 0x01c0ffa001fff000

def z834 : W := mkw 0x03e0f7e095eee000 0x01ceffe017fff000

def z835 : W := mkw 0x0010ec1f00100dc0 0x82d7fc1f01700fe0

def z836 : W := mkw 0x6008000021858b18 0x737bc39cf1878f1c

def z837 : W := mkw 0x0040d3c001a6c000 0x01ceffe001fff000

def z838 : W := mkw 0x6208c294b1858b18 0x7353c31ce1878f1c

def z839 : W := mkw 0x0300f7e0dc000000 0x0028bbe0fe000000

def z840 : W := mkw 0x00902c0b01d80dc0 0x82c1380001f80fe0

def z841 : W := mkw 0x00e0356001eee000 0x00843c60017f7000

def z842 : W := mkw 0x0090ee9f01dc8dc0 0xf3ffff9f11ff8ffc

def z843 : W := mkw 0x0380ffffdc480040 0x803efffffe080060

def z844 : W := mkw 0x0380ffffddc80940 0x80fefffffff80160

def z845 : W := mkw 0x0340ffffdc224000 0x01fefffffffff000

def z846 : W := mkw 0x0100080b4c000000 0x0030001bee000000

def z847 : W := mkw 0x030013e0dc000000 0x712803e0fe00801c

def z848 : W := mkw 0x485c194a68334692 0xcfffbb5fe9774ff3

def z849 : W := mkw 0x03e0f7e0ddeee000 0x01ceffe0e1fff000

def z850 : W := mkw 0x0200028090000000 0x002803e0fe000000

def z851 : W := mkw 0x0060d3e001a6e000 0x01cefbe001f7f000

def z852 : W := mkw 0x0390ffffdc580dc0 0x82bffffffe780fe0

def z853 : W := mkw 0x03e0f7f595eee000 0x01fefffdf7fff000

def z854 : W := mkw 0x030013e0dc000000 0x003a43e4fe000000

def z855 : W := mkw 0xdc4c000022235237 0x7d0000000007f01f

def z856 : W := mkw 0x485c194a68334692 0x4d01bb18e1774e13

def z857 : W := mkw 0x0300081fdc000000 0x003800fffe000000

def z858 : W := mkw 0x0340ffffdda6c000 0x01fefffffff7c000

def z859 : W := mkw 0x01e0ffeb4deee000 0x01fefffbeffff000

def z860 : W := mkw 0x62080294b0058b18 0x737b839cf1078f1c

def z861 : W := mkw 0x03e0f7f595eee940 0x81ceffe517fff160

def z862 : W := mkw 0x00e0f7e0006a6000 0x01ceffe0017f7000

def z863 : W := mkw 0x00e0f7f401eee000 0x01defffc01fff000

def z864 : W := mkw 0x0300080adc000000 0x0030001afe000000

def z865 : W := mkw 0x03001bffdc000000 0x003ebbfffe000000

def z866 : W := mkw 0x0090000001d80dc0 0x82c7b80001f80fe0

def z867 : W := mkw 0x6388e6b5b5cd8b58 0xf37bc7bdf78f8f7c

def z868 : W := mkw 0x03e0ffeaddeee000 0x01fefffafffff000

def z869 : W := mkw 0x0300ffffdc000000 0x0030ffbffe000000

def z870 : W := mkw 0x0300ffffdc000000 0x83fefffffe88f1e0

def z871 : W := mkw 0x2300ffffdd848908 0x327fffffff808f0c

def z872 : W := mkw 0x0390ec1fddd80dc0 0x0001b818e1700e00

def z873 : W := mkw 0x6008000020058218 0x737b8318e1078e1c

def z874 : W := mkw 0x0090eebf01d80dc0 0x82d7fcbf01f80fe0

def z875 : W := mkw 0x6208c294b1858b18 0x737bc7bdf7878f1c

def z876 : W := mkw 0x0000080a48000000 0x0030001ffe000000

def z877 : W := mkw 0x6208c294b1858b18 0x737fc3def9878f1c

def z878 : W := mkw 0x22e0f7f491eee908 0x73feffe411fff11c

def z879 : W := mkw 0x03101bffdc100dc0 0x823903fffe000fe0

def z880 : W := mkw 0x0320ffffdc04a000 0x003efffffe00b000

def z881 : W := mkw 0x0200c29490000000 0x003ac3fcfe000000

def z882 : W := mkw 0x62080014b0010b18 0x7339031cf0070f1c

def z883 : W := mkw 0x03001bffdc000000 0x0030031ffe000000

def z884 : W := mkw 0x0300ffffdc000000 0x000efffdf6000000

def z885 : W := mkw 0x0300ffffdc000000 0x0038bbfffe000000

def z886 : W := mkw 0x030002a094000000 0x002803a0f6000000

def z887 : W := mkw 0x00902c0b00580dc0 0x82853c0300780fe0

def z888 : W := mkw 0x6208c294b1858b18 0x7fffc7ffff87cf9f

def z889 : W := mkw 0x00e0f7e001eee000 0x01feffe411fff000

def z890 : W := mkw 0x03003febdc000000 0x00283be0fe000000

def z891 : W := mkw 0x03e0ffffddeee940 0x81fefffffffff160

def z892 : W := mkw 0x0300d3f4dc000000 0x002883f8fe000000

def z893 : W := mkw 0x03b0eebf95dcadc0 0x82d7fcbf17f8bfe0

def z894 : W := mkw 0x03e0081fddeee000 0x01f0001ffffff000

def z895 : W := mkw 0x0010080a48100480 0x02f7b81ae9700e80

def z896 : W := mkw 0x6208c294b1858b18 0x73ffc39ef1878f9c

def z897 : W := mkw 0x0300f7e0dc000000 0x002847e0fe000000

def z898 : W := mkw 0x63a8e6b5b5cdab18 0x737bc7bdf78fbf1c

def z899 : W := mkw 0x00b0eebf01dcadc0 0x82d7fc1f01f80fe0

def z900 : W := mkw 0x01e0f7e105eee000 0x01ceffe107fff000

def z901 : W := mkw 0x03f0ffffddfa6dc0 0x82fffffffff87fe0

def z902 : W := mkw 0x0200dbded8000000 0x003efffffe000000

def z903 : W := mkw 0x0300ffffdc000000 0x823efffffe0001e0

def z904 : W := mkw 0x4bfcffeafdffe692 0x4ffffffafffffe93

def z905 : W := mkw 0xf408c01423859b3d 0xffd7c41f018fffff

def z906 : W := mkw 0x03e0f7f5ddeee000 0x01eeffe5fffff000

def z907 : W := mkw 0x4018080a20110690 0x4fffbb5ae9774e93

def z908 : W := mkw 0x0300081fdc000000 0x01fe44fffe88f000

def z909 : W := mkw 0x485c194a68334692 0x4fffbf7bef774e93

def z910 : W := mkw 0x0300c2b494000000 0x003ac3bcf6000000

def z911 : W := mkw 0x0000194a48000000 0x003ebbfafe000000

def z912 : W := mkw 0x0300081fdc000940 0x8030001ffe000160

def z913 : W := mkw 0x00e0f7e001eee000 0x0084ffe001fff000

def z914 : W := mkw 0x00e0f7f501eee940 0x83dffffd01ffff60

def z915 : W := mkw 0x485c194a68334692 0x4fffbbfaff774e93

def z916 : W := mkw 0x485c194a68334692 0xcfffbf5be97f4ef3

def z917 : W := mkw 0x2290ec1f91d80dc8 0xb2d7fc1f11f80fec

def z918 : W := mkw 0x6208c294b1858b18 0x737b831cf1070f1c

def z919 : W := mkw 0xdc1c0000221116b7 0xffc100000088ffff

def z920 : W := mkw 0x010011604c000000 0x00280360ee000000

def z921 : W := mkw 0x6208c294b1858b18 0x7339439cf0878f1c

def z922 : W := mkw 0x0b44ffffdc224002 0x0c3efffffe004003

def z923 : W := mkw 0x00e03560006a6000 0x018c3f60007f7000

def z924 : W := mkw 0x0100196a4c000000 0x003ebb7aee000000

def z925 : W := mkw 0x485c194a68334692 0x4e01bb18e1770e93

def z926 : W := mkw 0x0300ffffdc000000 0x0000bb1bee000000

def z927 : W := mkw 0x03003d7fdc000000 0x00043c7bee000000

def z928 : W := mkw 0x03e0ffffdc6a6000 0x01feffffff7f7000

def z929 : W := mkw 0x03001beadc000000 0x0028bbf8fe000000

def z930 : W := mkw 0x0390ffffddd80dc0 0x8231bb1fff700fe0

def z931 : W := mkw 0x485c194a68334692 0x4ffffbdef9774e93

def z932 : W := mkw 0x9700ffffde001025 0xffc0bb18e088f1ff

def z933 : W := mkw 0x6308e6b5b5858b18 0x737fc7ffff878f1c

def z934 : W := mkw 0x0090ec1f01d80dc0 0x8201b81801700fe0

def z935 : W := mkw 0x484c114068234212 0x4fffbb58e9774e13

def z936 : W := mkw 0x6008c28021858b18 0x737bc398e1878f1c

def z937 : W := mkw 0x0b54195fdc324482 0x0cb4385ffe704083

def z938 : W := mkw 0x22e0f7f491eee908 0x01ceffe001fff000

def z939 : W := mkw 0x0310081fdc100dc0 0x82ff44fffe880fe0

def z940 : W := mkw 0x485c194a68334692 0x0cbfbb5ae9774e83

def z941 : W := mkw 0x485c194a68334692 0x0dcfbb5ae9774e83

def z942 : W := mkw 0x0090ec1f01d80dc0 0x82c57c0701f80fe0

def z943 : W := mkw 0xdc5c0000223356b7 0xcfc10000017f7ef3

def z944 : W := mkw 0x00e037e0006ee000 0x01cebfe0017ff000

def z945 : W := mkw 0x0300ca9fdd848000 0x017ac39fff878000

def z946 : W := mkw 0x0090ec1f01d80dc0 0xcffffcff1ff84ff3

def z947 : W := mkw 0x00e0f7e001eee000 0x03dffff801fffe00

def z948 : W := mkw 0x03e0ffffddeee000 0x0084bf7bef7f7000

def z949 : W := mkw 0x00e0f7e001eee000 0x01fefff8e1fff000

def z950 : W := mkw 0x0300081fdc000000 0x0036b81ffe000000

def z951 : W := mkw 0x9c54194a4a3254a7 0x8c8438430e7040e3

def z952 : W := mkw 0x00902c0b01d80dc0 0x82d77c0701f80fe0

def z953 : W := mkw 0x00e0114001eee000 0x01c0bb0001fff000

def z954 : W := mkw 0x0300d3f4dd800900 0x027bc3fcff800f00

def z955 : W := mkw 0x0310ffffdc100dc0 0x82ffffffff700fe0

def z956 : W := mkw 0x0380ffffddc80940 0x82fefffffe8801e0

def z957 : W := mkw 0x6208c294b1858b18 0x7339839cf1078f1c

def z958 : W := mkw 0x0300ffffdc000900 0x023ffffffe000f00

def z959 : W := mkw 0x484c114020234212 0x4d08034000074013

def z960 : W := mkw 0x0300ffffdc000000 0x4ffefffffe88f093

def z961 : W := mkw 0xdc5c194a6a3356b7 0xb001ffbdf7ffbf6c

def z962 : W := mkw 0x03902c1fdc5804c0 0x80b43c1ffe7800e0

def z963 : W := mkw 0x00902c0b01d80dc0 0x82d7bc1b01f80fe0

def z964 : W := mkw 0x6208c294b1858b18 0x303bc39cf1878f0c

def z965 : W := mkw 0x0390ffffddd80dc0 0x80befffffef801e0

def z966 : W := mkw 0x030013e0dc000000 0x003a83f8fe000000

def z967 : W := mkw 0x0390ffffdddc8dc0 0x83ffffffffff8fe0

def z968 : W := mkw 0x0854194a48324482 0x7ffe78c618f0c19f

def z969 : W := mkw 0x03e0ffffddeee000 0x003effffffffb000

def z970 : W := mkw 0x0090ec1f01d80dc0 0x8253f81f01f00fe0

def z971 : W := mkw 0x0300195fdc000000 0x0034385ffe000000

def z972 : W := mkw 0x0300ffffdc000000 0x00befffffe087000

def z973 : W := mkw 0x00902c0b005804c0 0x82d7fc1f01f80fe0

def z974 : W := mkw 0xdc5c0000223356b7 0xffc1000001774fff

def z975 : W := mkw 0x0300e6b594000000 0x0000c7bdf6000000

def z976 : W := mkw 0x03000000dc000000 0x002800e0fe000000

def z977 : W := mkw 0x00e0000001eee000 0x01c6b80001fff000

def z978 : W := mkw 0x0300ffffdc000000 0xcffefffffe8841f3

def z979 : W := mkw 0xdc1c080a6a1116b7 0x7e31001afe000e9f

def z980 : W := mkw 0x00e03560006a6000 0x01c43c60017f7000

def z981 : W := mkw 0x03003fffdc000000 0x003c3ffffe000000

def z982 : W := mkw 0x03a0eebfddcca000 0x003044bffe88b000

def z983 : W := mkw 0x0290ee9f91d80dc0 0x82d7ff1fe1f80fe0

def z984 : W := mkw 0x6208c294b1858b18 0xf37bc79df18f8f7c

def z985 : W := mkw 0x01003d6b4c000000 0x0004bf7bee000000

def z986 : W := mkw 0x0300ec1fdc000000 0x0030b81ffe000000

def z987 : W := mkw 0x0390ffffddd80dc0 0xf3fffffffff88ffc

def z988 : W := mkw 0x0390ec1fddd80dc0 0x82d7fc1fe1f80fe0

def z989 : W := mkw 0x0300ffffdc000000 0x003ebf7bee000000

def z990 : W := mkw 0x00a0e6a001cca000 0x01ceffa001ffb000

def z991 : W := mkw 0x030013e0dc000000 0x003803e7fe000000

def z992 : W := mkw 0x6208c294b1858b18 0xffffc7dff98fcfff

def z993 : W := mkw 0x00e0356001eee000 0x01ce7ce001fff000

def z994 : W := mkw 0x0360ffffdda6e000 0x017effffff87f000

def z995 : W := mkw 0x4b5ce6b5b4334692 0x4fc144a517774e93

def z996 : W := mkw 0x9400000002001025 0xfffec7e71f8ff1ff

def z997 : W := mkw 0x00e0f7e001eee000 0x73feffe71ffff11c

def z998 : W := mkw 0x0300081fdc000000 0x003044bffe000000

def z999 : W := mkw 0x0300081fdc000000 0x7230001ffe00011c

def z1000 : W := mkw 0x0300ffffdc000000 0x013efffffe00f000

def z1001 : W := mkw 0x030013f5dc000000 0x002803e5fe000000

def z1002 : W := mkw 0x03e0ffffddeee000 0x73fefffffffff11c

def z1003 : W := mkw 0x0300ffffdc000000 0x4e3efffffe000093

def z1004 : W := mkw 0x030013e0dc000000 0x00200300fe000000

def z1005 : W := mkw 0x63e8f7f4fdefeb18 0x73fffffcffffff1c

def z1006 : W := mkw 0x0010080b001004c0 0x82d7b81b01700ee0

def z1007 : W := mkw 0x6208c294b1858b18 0x3001831cf1070f0c

def z1008 : W := mkw 0x006013e00026e000 0x0108bbe00177f000

def z1009 : W := mkw 0xf608c294b3859b3d 0x8c85877bef0f7ee3

def z1010 : W := mkw 0x0040114000224000 0x01cebf60017f7000

def z1011 : W := mkw 0x6208c294b1858b18 0x7371831cf1878f1c

def z1012 : W := mkw 0x0090ec1f01d80dc0 0x8211fc1f01f80fe0

def z1013 : W := mkw 0x0390ffffddd80dc0 0x823fffffff700fe0

def z1014 : W := mkw 0x485c194a68334692 0x0ed7bb5ae9774e83

def z1015 : W := mkw 0x485c194a68334692 0x4fffbf7ae97f7e93

def z1016 : W := mkw 0x00e0f7e001eee000 0x0dceffe209fff083

def z1017 : W := mkw 0x00e0f7f401eee900 0x83dfffff01ffffe0

def z1018 : W := mkw 0x00e0e6a001eee000 0x01c6fca001fff000

def z1019 : W := mkw 0x0010c81e01900d80 0x82d7fc1f01f80fe0

def z1020 : W := mkw 0x00e0f7e001eee000 0x81ceffe501fff160

def z1021 : W := mkw 0x0060116000226000 0x01cebb6001777000

def z1022 : W := mkw 0x00e0f7e001eee000 0x01cebb4001fff000

def z1023 : W := mkw 0x02e0f7e091eee000 0x01eeffe0f1fff000

def z1024 : W := mkw 0x03e0f7f5ddeee000 0x012847e5fe8ff000

def z1025 : W := mkw 0x0300ffffdc000000 0x0000bb78ee000000

def z1026 : W := mkw 0x0090e41401d80dc0 0x82d7fc1c01f80fe0

def z1027 : W := mkw 0x0300ffffdc000000 0xf3fefffffe8881fc

def z1028 : W := mkw 0x0090ec1f01dc8dc0 0x83d7fc1f01ff8fe0

def z1029 : W := mkw 0x0090ec1f01d80dc0 0x82d7bc1b01780ee0

def z1030 : W := mkw 0x00e0f7e001eee000 0x018c7fe000fff000

def z1031 : W := mkw 0x03e0ffffddeee000 0x01eefff8fffff000

def z1032 : W := mkw 0x0090ec1f005804c0 0x82d7fc1f01780ee0

def z1033 : W := mkw 0x0040f7e000224000 0x01ceffe001fff000

def z1034 : W := mkw 0x0090ec1f01d80dc0 0x8217fc1f01700fe0

def z1035 : W := mkw 0x6288c294b1cd8b18 0x73fbc39cf1ff8f1c

def z1036 : W := mkw 0x03101beadc100480 0x02ffbbfaff700e80

def z1037 : W := mkw 0x0390eebf95d80dc0 0x82fffcff1ff80fe0

def z1038 : W := mkw 0xdc4c11406a235237 0x4d280360ee077013

def z1039 : W := mkw 0x03e03d7fdc6a6000 0x00b43c7ffe787000

def z1040 : W := mkw 0x0300081fdc000000 0x0000001bee000000

def z1041 : W := mkw 0x006013e00026e000 0x018c3be00077f000

def z1042 : W := mkw 0x03e0ffffdc6a6000 0x01fefffffef8f000

def z1043 : W := mkw 0x0310ffffdc1004c0 0x803efffffe0000e0

def z1044 : W := mkw 0x03e0ffffdc6ee000 0x01befffffe7ff000

def z1045 : W := mkw 0x0300ffffdd800900 0x003efffffe800100

def z1046 : W := mkw 0x03002c1fdc000000 0x00343c1ffe000000

def z1047 : W := mkw 0x485c114020334692 0x4fffbb58e1774e93

def z1048 : W := mkw 0x0300ffffdd848900 0x037fffffff878f00

def z1049 : W := mkw 0x0300ffffdc000000 0x0000bbb8f6000000

def z1050 : W := mkw 0x0300fd5fdc000000 0x003eff5ffe000000

def z1051 : W := mkw 0x0300fd7fdc000000 0x0036fc7ffe000000

def z1052 : W := mkw 0x00e0f7e001eee000 0x01eeffe01ffff000

def z1053 : W := mkw 0x6008000020010b18 0x737b8318e1070f1c

def z1054 : W := mkw 0x03b0ffffdddcadc0 0x82fffffffff8bfe0

def z1055 : W := mkw 0x2380ffffddcc8948 0xb03efffffe88816c

def z1056 : W := mkw 0x0300ffffdd848000 0x01feffffff8ff000

def z1057 : W := mkw 0x03601beadc26e000 0x01febbfaff77f000

def z1058 : W := mkw 0x00e0f7e001eee000 0xf3feffe711fff1fc

def z1059 : W := mkw 0x03000000dc000000 0x00300007fe000000

def z1060 : W := mkw 0x0090ec1f01d80dc0 0x82dffcff01f80fe0

def z1061 : W := mkw 0x62080000b0010218 0x737b8318f1070e1c

def z1062 : W := mkw 0x0300c294dc000000 0x003ac39cfe000000

def z1063 : W := mkw 0x03e0f7e0ddeee000 0x01feffe7fffff000

def z1064 : W := mkw 0x03001bebdc000000 0x002803e3fe000000

def z1065 : W := mkw 0x484c114068234212 0xcffe4747e88f41f3

def z1066 : W := mkw 0x0380ffffddc80940 0x003efffffe000000

def z1067 : W := mkw 0x6288e694b1cd8b18 0x737bfb9cf1f78f1c

def z1068 : W := mkw 0x00e0f7e049eee000 0x01eeffe0e9fff000

def z1069 : W := mkw 0x03000015dc000000 0x00200005fe000000

def z1070 : W := mkw 0x00e0f7e001eee000 0x0108ffe001fff000

def z1071 : W := mkw 0x030013e0dc000000 0x002e47e0fe000000

def z1072 : W := mkw 0x00e0d3c001eee000 0x01cefbc001fff000

def z1073 : W := mkw 0x0010080a00100480 0x82d7b81a01f80fe0

def z1074 : W := mkw 0x6008000021858b18 0x73418318e1878f1c

def z1075 : W := mkw 0x485c080a20334692 0x4fffbb1ae1774e93

def z1076 : W := mkw 0x030037e0dc000000 0x002c3fe0fe000000

def z1077 : W := mkw 0x0310ffffdc100480 0x82fffffffff80fe0

def z1078 : W := mkw 0x6208c295b1858b58 0xf37bc39df1878f7c

def z1079 : W := mkw 0x03e0f7e0ddeee000 0x0000bb00e1770000

def z1080 : W := mkw 0x6008c01421858b18 0x737bc31ce1878f1c

def z1081 : W := mkw 0x6398ee9ffddd8fd8 0xf3ffff9fffff8ffc

def z1082 : W := mkw 0x4008c01421810b10 0x737bc39cf1878f1c

def z1083 : W := mkw 0x0300ffffdc000000 0x4d3efffffe004013

def z1084 : W := mkw 0xf408c28023859b3d 0xffcfc7e0018fffff

def z1085 : W := mkw 0x0090ec1f01d80dc0 0xcffffcff09f8fff3

def z1086 : W := mkw 0x0090ec1f01d80dc0 0x8001b81b01700ee0

def z1087 : W := mkw 0x03e0ffffdc6a6000 0x003efffffe700000

def z1088 : W := mkw 0x22e0f7f491eee908 0x31fefffcf1fff10c

def z1089 : W := mkw 0x0300081fdc000000 0x0000001df6000000

def z1090 : W := mkw 0x0310ffffdc100dc0 0x003ffffffe000e00

def z1091 : W := mkw 0x6208c294b1858b18 0xf3ffc7ffff8f8ffc

def z1092 : W := mkw 0x03000abfdc000000 0x003000bffe000000

def z1093 : W := mkw 0x03000a9fdc000000 0x0038039ffe000000

def z1094 : W := mkw 0x23e0ffffddeee908 0x31fefffffffff10c

def z1095 : W := mkw 0x00902c0b005804c0 0x8085bc1b01780ee0

def z1096 : W := mkw 0x0300081fdc000000 0x737a409ffe80811c

def z1097 : W := mkw 0x0300dbffdc000000 0x003ac3fffe000000

def z1098 : W := mkw 0x0090ec1f01d80dc0 0x80c7fc1d01f80f60

def z1099 : W := mkw 0x6208c294b1858b18 0x716bc398f1878e1c

def z1100 : W := mkw 0x6208c294b1858b18 0x737fc79ff1878f1c

def z1101 : W := mkw 0x9c54194a4a3254a7 0x8c843842087870e3

def z1102 : W := mkw 0x62080280b0058218 0x71298398f1078e1c

def z1103 : W := mkw 0x0bd4ffffddfa4dc2 0x8efffffffff84fe3

def z1104 : W := mkw 0xf40800002205923d 0x7d0000000007f01f

def z1105 : W := mkw 0x00b0ec3f01d82dc0 0x82d7fc3f01f83fe0

def z1106 : W := mkw 0x0300f7f4dc000000 0x003efffcfe000000

def z1107 : W := mkw 0x0000ffea48000000 0x003efffffe000000

def z1108 : W := mkw 0x6208c294b1858b18 0x3253c39cf1878f0c

def z1109 : W := mkw 0x485c194a68334692 0x7fffbbdaf977ce9f

def z1110 : W := mkw 0x6008028020058218 0x710803800007801c

def z1111 : W := mkw 0x0b54ffffdc324482 0x003efffffe700000

def z1112 : W := mkw 0x6208c280b1858218 0x737bc398f1878e1c

def z1113 : W := mkw 0x6228c2b4b185ab18 0x737bc3bcf187bf1c

def z1114 : W := mkw 0x0090ec1f01d80dc0 0x83dffc5f01f84fe0

def z1115 : W := mkw 0x6208c294b1858b18 0x737b8318e1878f1c

def z1116 : W := mkw 0xd408000022011235 0xffc10000018fffff

def z1117 : W := mkw 0x6208c294b1858b18 0x737bc7bcf18fbf1c

def z1118 : W := mkw 0xf4e8f7e023effb3d 0xffcfffe001ffffff

def z1119 : W := mkw 0x6208c294b0058b18 0x733bc39cf0078f1c

def z1120 : W := mkw 0x0200c29491800900 0x82ffc7ffff880fe0

def z1121 : W := mkw 0x0390ffffdc5804c0 0x82ffffffff780ee0

def z1122 : W := mkw 0x00e0f7e001eee000 0x0100bb000177f000

def z1123 : W := mkw 0x00e0f7e001eee000 0x01ceffe517fff000

def z1124 : W := mkw 0x6208c294b1858b18 0x7fffc7fef98fff9f

def z1125 : W := mkw 0x0390ec1fddd80dc0 0x82fffcfffff80fe0

def z1126 : W := mkw 0x485c194a68334692 0x4fcfbb58e1774e93

def z1127 : W := mkw 0x0300ffffdd848000 0x003efffffe808000

def z1128 : W := mkw 0x0380ffffddc80940 0x827fffffff880f60

def z1129 : W := mkw 0x485c194a68334692 0x4ffffb5ee9f74f93

def z1130 : W := mkw 0x6208c294b1858b18 0x737fc7fcf1878f1c

def z1131 : W := mkw 0xdcdc000023fb5ff7 0xffc1000001ffffff

def z1132 : W := mkw 0x0300081fdc000000 0x82f6441ffe8801e0

def z1133 : W := mkw 0x4048114020234210 0x4fffbb5ae9774e93

def z1134 : W := mkw 0x00e0f7f401eee900 0x01cffff801fffe00

def z1135 : W := mkw 0x0200c01491800900 0x0273c01cf1800f00

def z1136 : W := mkw 0x030013e0dc000000 0x000003a0f6000000

def z1137 : W := mkw 0x0300ffffdd800900 0x82ffffffff880fe0

def z1138 : W := mkw 0x00902c1f00580dc0 0x8211381f00700fe0

def z1139 : W := mkw 0x0300080bdc000000 0x00200003fe000000

def z1140 : W := mkw 0x0380f7f5ddc80940 0x802847e5fe880160

def z1141 : W := mkw 0x2300d3f4dd848908 0x302843e4fe80810c

def z1142 : W := mkw 0x0300ffffdc000000 0x003ebb5ffe000000

def z1143 : W := mkw 0x030013e0dc000000 0x737a43e4fe80811c

def z1144 : W := mkw 0x6308c295b5858b18 0x737bc39df7878f1c

def z1145 : W := mkw 0x0090ec1f01d80dc0 0xf3fffcff1ff88ffc

def z1146 : W := mkw 0x62080294b0058b18 0x7231031cf0070f1c

def z1147 : W := mkw 0x0090ec0a01d80480 0x82d7fc1f01f80fe0

def z1148 : W := mkw 0x0090ec1f01d80dc0 0x82d7fc7f01f87fe0

def z1149 : W := mkw 0x03e0ffffddeee000 0x0000ffbdf7ffb000

def z1150 : W := mkw 0x0100ffeb4c000000 0x003efffbee000000

def z1151 : W := mkw 0x0390ffffddd80dc0 0x80bfffffff780ee0

def z1152 : W := mkw 0x02e0f7f491eee000 0x01fefffffffff000

def z1153 : W := mkw 0x6308c2b4b5858b18 0x737bc3bcf7878f1c

def z1154 : W := mkw 0x0300c81fdc000000 0x0032c01ffe000000

def z1155 : W := mkw 0x0300ffeadc000000 0x003efffafe000000

def z1156 : W := mkw 0x0200c29491848000 0x01fec7ffff8ff000

def z1157 : W := mkw 0x00e0114001eee000 0x01c4384001fff000

def z1158 : W := mkw 0x0300eebf94000000 0x003effbff6000000

def z1159 : W := mkw 0x0090c81e01d80dc0 0x82d7f81e01f80fe0

def z1160 : W := mkw 0x0390eebf95d80dc0 0x82d7fc1f01f80fe0

def z1161 : W := mkw 0x03003d6bdc000000 0x00243c63fe000000

def z1162 : W := mkw 0x0000000000000000 0x82f644071e8801e0

def z1163 : W := mkw 0x03e0ffffddeee000 0x0030bb1fff770000

def z1164 : W := mkw 0x0300eebfdc000000 0x003ac7bffe000000

def z1165 : W := mkw 0x6208c294b1858b18 0x30018318e1878f0c

def z1166 : W := mkw 0x0300ffffdc000000 0x002efff8fe000000

def z1167 : W := mkw 0x00e0e40001eee000 0x01c0b80001fff000

def z1168 : W := mkw 0x00e0f7e001eee000 0x7ffeffe619fff19f

def z1169 : W := mkw 0x00b0eebf01dcadc0 0x83dffcff01f8ffe0

def z1170 : W := mkw 0x485c194a68334692 0x4fffff5ae9ff4e93

def z1171 : W := mkw 0x6208e6b4b1858b18 0x737bc7bcf1878f1c

def z1172 : W := mkw 0x0300ffffdc000000 0x003affbdf6000000

def z1173 : W := mkw 0x22e0f7f491eee908 0x33dffffc11ffff0c

def z1174 : W := mkw 0x00902c1f01d80dc0 0x82d53c1f01f80fe0

def z1175 : W := mkw 0x00e0f7e001eee000 0x71eeffe011fff01c

def z1176 : W := mkw 0x030002a0dc000000 0x002000a0fe000000

def z1177 : W := mkw 0x03000280dc000000 0x00280380fe000000

def z1178 : W := mkw 0x0090ee9f01dc8dc0 0x82d7ff1f01ff0fe0

def z1179 : W := mkw 0x6208e695b1858b18 0x737bc79df1878f1c

def z1180 : W := mkw 0x0090ec1f01d80dc0 0x82957c1f00f80fe0

def z1181 : W := mkw 0x0090ec1f01d80dc0 0x8001b81801f80f60

def z1182 : W := mkw 0x0300d3e0dc000000 0x002ac3e0fe000000

def z1183 : W := mkw 0x03e0ffffddeee000 0x01cefffbeffff000

def z1184 : W := mkw 0x0300001594000000 0x0030001df6000000

def z1185 : W := mkw 0x006013e00026e000 0x01ceffe001fff000

def z1186 : W := mkw 0x485c194a68334692 0x0c01bb58e9774e03

def z1187 : W := mkw 0x6288e695b1cd8b58 0xf3ffff9df1ff8f7c

def z1188 : W := mkw 0x00e0f7e001eee000 0x83feffe71ffff1e0

def z1189 : W := mkw 0x0300ffffdc000000 0x002c7fe7fe000000

def z1190 : W := mkw 0x0090081f01d80dc0 0x82d7b81f01f80fe0

def z1191 : W := mkw 0x0090ec1f01d80dc0 0x82fffc9f11f80fe0

def z1192 : W := mkw 0x0090ec1f01d80dc0 0x82d1b81f01f80fe0

def z1193 : W := mkw 0x6208c294b1858b18 0x734bc398e1878f1c

def z1194 : W := mkw 0x00e0f7e001eee000 0x01c47ce001fff000

def z1195 : W := mkw 0x0010080a00100dc0 0x82d7b81a01700fe0

def z1196 : W := mkw 0x0390ec1f95d80dc0 0x82d7fc1f17f80fe0

def z1197 : W := mkw 0x00e0f7e001eee000 0x4fceffe001fff093

def z1198 : W := mkw 0x485c194a68334692 0x4fffbb5ae9fffe93

def z1199 : W := mkw 0x0390ffffddd80dc0 0x823ffffffe880fe0

def z1200 : W := mkw 0xf408000022011b3d 0xffc100000088ffff

def z1201 : W := mkw 0x0090ec1f01d80dc0 0x82ffff1fe1f80fe0

def z1202 : W := mkw 0x02e0f7f491eee000 0x01ceffe411fff000

def z1203 : W := mkw 0x9600c29492001025 0xfffac39cf088f1ff

def z1204 : W := mkw 0x9400000002001025 0xffffc4ff1f88ffff

def z1205 : W := mkw 0x00902c0b01d80dc0 0x80853c0301780ee0

def z1206 : W := mkw 0x0300ffffdc000940 0x803efffffe000160

def z1207 : W := mkw 0x495c196a6c334692 0x4fffbb7aef774e93

def z1208 : W := mkw 0x030013e0dc000000 0x01ee47e0fe88f000

def z1209 : W := mkw 0x0b54ffffdc324482 0x4ffefffffe704093

def z1210 : W := mkw 0x0060f7e00026e000 0x01ceffe00177f000

def z1211 : W := mkw 0x485c194a68334692 0x4d3fbb5ae9774e13

def z1212 : W := mkw 0x4008000020010210 0x737b8398f1078e1c

def z1213 : W := mkw 0x0300f7f5dc000000 0x003e47e7fe000000

def z1214 : W := mkw 0xd408000022011235 0xcfff877bef0f7ef3

def z1215 : W := mkw 0x0090ec1f01d80dc0 0x8ed7fc5f09f84fe3

def z1216 : W := mkw 0x01902c0b4c5804c0 0x80843c030e7800e0

def z1217 : W := mkw 0x036013e0dc26e000 0x002803e0fe070000

def z1218 : W := mkw 0x0090ec1f01d80dc0 0x82d7b81f01700fe0

def z1219 : W := mkw 0x0300ec1fdc000000 0x003efcfffe000000

def z1220 : W := mkw 0x0300ffffdd848000 0x003effffff070000

def z1221 : W := mkw 0x00e0f56001ea6000 0x01ceff6001ff7000

def z1222 : W := mkw 0x0390ffffddd80dc0 0xcffffffffff84ff3

def z1223 : W := mkw 0x0300ffffdc000000 0x73fefffffe88f11c

def z1224 : W := mkw 0x0300ffffdc000000 0x437efffffe000010

def z1225 : W := mkw 0x0300eebfdc000000 0x000044bdf6000000

def z1226 : W := mkw 0x0300ffffdd800900 0x003fffffff000e00

def z1227 : W := mkw 0x0390ec1fddd80dc0 0x0031b81fff700e00

def z1228 : W := mkw 0x0080e41401c80900 0x82d7fc1f01f80fe0

def z1229 : W := mkw 0x00e0f7e001eee000 0x0000bb0001ffb000

def z1230 : W := mkw 0x62a8e6b4b1cdab18 0x73ffc7fcf18fff1c

def z1231 : W := mkw 0x03003febdc000000 0x003e7fe7fe000000

def z1232 : W := mkw 0x03e0f7f595eee000 0x01ceffe001fff000

def z1233 : W := mkw 0x0300d3f4dc000000 0x003ec7fffe000000

def z1234 : W := mkw 0x0300081fdc000000 0x003e005ffe000000

def z1235 : W := mkw 0x0080e68001cc8000 0x01ceffe001fff000

def z1236 : W := mkw 0x02e0f7f491eee000 0x01cefff8e1fff000

def z1237 : W := mkw 0x0300ffffdc000000 0x0036ff1ffe000000

def z1238 : W := mkw 0x0000114048000000 0x002803e0fe000000

def z1239 : W := mkw 0x03e013e0ddeee000 0x01e803e0fffff000

def z1240 : W := mkw 0x0190ec1f4dd80dc0 0x82d7fc1f0ff80fe0

def z1241 : W := mkw 0x00e0f7f501eee940 0x83deffe701fff1e0

def z1242 : W := mkw 0x0090ec1f01d80dc0 0x80c7fc1b01f80ee0

def z1243 : W := mkw 0x0090ec1f01d80dc0 0x8295bc1f01780fe0

def z1244 : W := mkw 0x0300ffffdc000000 0x713efffffe00801c

def z1245 : W := mkw 0x0200ee9f90000000 0x003efffffe000000

def z1246 : W := mkw 0x0300d3e0dd848000 0x016ac3e0ff878000

def z1247 : W := mkw 0x0090ec1f01d80dc0 0x8017fc1f01f80f60

def z1248 : W := mkw 0x0300ffffdc000000 0x723efffffe00011c

def z1249 : W := mkw 0x485c194a68334692 0x7fffbb5ae9f7cf9f

def z1250 : W := mkw 0x0080e41501c80940 0x82d7fc1d01f80f60

def z1251 : W := mkw 0x00e0f7e001eee000 0x0080bb00017f7000

def z1252 : W := mkw 0x0200c29490000000 0x003ac7bdf6000000

def z1253 : W := mkw 0x03a0e6a095cca000 0x000044a01688b000

def z1254 : W := mkw 0x03e0ffebddeee000 0x01eeffe3fffff000

def z1255 : W := mkw 0x03e0ffffddeee000 0x00feffffffff0000

def z1256 : W := mkw 0x6308e6b5b5858b18 0x734144a517878f1c

def z1257 : W := mkw 0x0300ffffdc000000 0x002cbffbfe000000

def z1258 : W := mkw 0x0380ffffdc480000 0x00befffffe780000

def z1259 : W := mkw 0x00e0f7e001eee000 0x03deffe201fff080

def z1260 : W := mkw 0x00e0f7f401eee900 0x73fffffc11ffff1c

def z1261 : W := mkw 0x0390ffffddd80dc0 0x83fffffffff8ffe0

def z1262 : W := mkw 0x2300ffffdd848908 0x003efffffe000000

def z1263 : W := mkw 0x4008c28021858210 0x737bc39cf1878f1c

def z1264 : W := mkw 0x6288e695b1cd8b58 0xf3ffc79ff18f8ffc

def z1265 : W := mkw 0x03001bffdc000000 0x003e47fffe000000

def z1266 : W := mkw 0x2290ee9f91dc8dc8 0xf3fffc9f11f88ffc

def z1267 : W := mkw 0x0090ec1f01d80dc0 0x83dfff1f01ff0fe0

def z1268 : W := mkw 0x0300ffffdc000000 0x0cbefffffe004083

def z1269 : W := mkw 0x030013e0dc000000 0x003e03e2fe000000

def z1270 : W := mkw 0x0300081fdc000000 0x0036441ffe000000

def z1271 : W := mkw 0x03a0ffffddcca940 0x803efffffe88b160

def z1272 : W := mkw 0x485c194b683346d2 0xcfffbb5be9774ef3

def z1273 : W := mkw 0x495c194b6c334692 0x4fffbb5bef774e93

def z1274 : W := mkw 0x495c3d6b6c334692 0x4fc53c630f774e93

def z1275 : W := mkw 0x03e0ffffddeee000 0x017efffffff78000

def z1276 : W := mkw 0xdcdcec1f23fb5ff7 0xffd7fc1f01ffffff

def z1277 : W := mkw 0x0300ffffdc000000 0x003847fffe000000

def z1278 : W := mkw 0x00902c1f00580dc0 0x82d77c1f00f80fe0

def z1279 : W := mkw 0x0300ffffdc000000 0x0034bf7ffe000000

def z1280 : W := mkw 0x23e0f7f595eee908 0x31ceffe517fff10c

def z1281 : W := mkw 0xfe4c13c0fa27d23f 0x7d2803e0fe07f01f

def z1282 : W := mkw 0x0300ffffdc000000 0x000efffbee000000

def z1283 : W := mkw 0x00e037e0006ee000 0x00843f60007f7000

def z1284 : W := mkw 0x03601bffdc26e000 0x013803fffe07f000

def z1285 : W := mkw 0x6208c294b1858b18 0xf37bc39ff1878ffc

def z1286 : W := mkw 0x0380e6b595c80940 0x827bc7bdf7880f60

def z1287 : W := mkw 0x0040114000224000 0x01cebb4001fff000

def z1288 : W := mkw 0x030013e0dc000000 0x82fe47e7fe8801e0

def z1289 : W := mkw 0x20e0f7e001eee908 0x31ceffe001fff10c

def z1290 : W := mkw 0x6208c294b1858b18 0x713bc39cf1078e1c

def z1291 : W := mkw 0x03003febdc000000 0x003ebffbfe000000

def z1292 : W := mkw 0x485c000020334692 0x4fff44e71f774e93

def z1293 : W := mkw 0x0190ec3f05d80dc0 0x82d7fc3f07f80fe0

def z1294 : W := mkw 0x0300f7e0dc000000 0x003effe7fe000000

def z1295 : W := mkw 0x2300081fdc000908 0x3030001ffe00010c

def z1296 : W := mkw 0x0390fd5fddd80dc0 0x82ffff5ffff80fe0

def z1297 : W := mkw 0x0390fd7fddd80dc0 0x82f7fc7ffff80fe0

def z1298 : W := mkw 0x0090ec1f01d80dc0 0x82fffc5f09f80fe0

def z1299 : W := mkw 0x6208c294b0058218 0x737bc39cf1078e1c

def z1300 : W := mkw 0x6208c294b1858b18 0x737bc3fcff878f1c

def z1301 : W := mkw 0x9440114002225025 0xfffebb471f7741ff

def z1302 : W := mkw 0x03e0f7f595eee000 0x01feffe71ffff000

def z1303 : W := mkw 0x0300f7f5dc000000 0x002effe5fe000000

def z1304 : W := mkw 0x0000114048000000 0x003e47e7fe000000

def z1305 : W := mkw 0x0200028090000000 0x003e47e7fe000000

def z1306 : W := mkw 0x4208c294b0010210 0x737bc39cf1878f1c

def z1307 : W := mkw 0x0000fd5f48000000 0x003efffffe000000

def z1308 : W := mkw 0x62a8e6b4b1cdab18 0x73ffffbcf1ffbf1c

def z1309 : W := mkw 0x0300f7f5dc000000 0x002803e0fe000000

def z1310 : W := mkw 0x0300dbdfdc000000 0x003efbdffe000000

def z1311 : W := mkw 0x00e0114001eee000 0x01ceffe001fff000

def z1312 : W := mkw 0x0090ec0b01d80dc0 0x82c7fc0301f80fe0

def z1313 : W := mkw 0x00e0f7e001eee000 0x01cebf60017f7000

def z1314 : W := mkw 0x030013e0dc000000 0x002c07e3fe000000

def z1315 : W := mkw 0x481c080a68110692 0x4fffbb1ae9770e93

def z1316 : W := mkw 0x00e0240001eee000 0x01c43c0001fff000

def z1317 : W := mkw 0x00c0f54001ea4000 0x01ceffe001fff000

def z1318 : W := mkw 0x03a0f7e0ddcca000 0x002847e0fe88b000

def z1319 : W := mkw 0x0300081fdc000000 0x4ffe005ffe004093

def z1320 : W := mkw 0x0b54ffffdc324482 0x0dfeffffff774083

def z1321 : W := mkw 0x00b0eebf01dcadc0 0x83dfffbf01ffbfe0

def z1322 : W := mkw 0x0bf4ffffdc7a6482 0x0cbefffffe787083

def z1323 : W := mkw 0x03c0ffffddea4000 0x01feffffffff4000

def z1324 : W := mkw 0x00e0f7f501eee940 0x01ceffe001fff000

def z1325 : W := mkw 0xf408000023859b3d 0x7f4100000187ff1f

def z1326 : W := mkw 0x485c194a68334692 0x4fe9bb58e9774e93

def z1327 : W := mkw 0x0390ffffddd80dc0 0x8085bf7bef780ee0

def z1328 : W := mkw 0x0300ffffdc000000 0x00fefffffe880000

def z1329 : W := mkw 0x6208c294b1858b18 0x70218318f1070e1c

def z1330 : W := mkw 0x6208c294b1858b18 0x737bc3fcf187ff1c

def z1331 : W := mkw 0x0310195fdc100dc0 0x82ffbb5fff700fe0

def z1332 : W := mkw 0x00e0e68001eee000 0x01ceff8001fff000

def z1333 : W := mkw 0x0300ec1fdc000000 0x0030441ffe000000

def z1334 : W := mkw 0x01e03d6b4c6a6000 0x01febf7bef7f7000

def z1335 : W := mkw 0x485c194a68334692 0x4ffbbb18e1774e93

def z1336 : W := mkw 0x0300ffffdc000000 0x0016ffbff6000000

def z1337 : W := mkw 0x0090080a01d80dc0 0x82d7fc1f01f80fe0

def z1338 : W := mkw 0x0000194a48000000 0x003ebb5ffe000000

def z1339 : W := mkw 0x6008000021858b18 0x737f44e71f878f1c

def z1340 : W := mkw 0x0310ca9fdd900dc0 0x827bc39fff800fe0

def z1341 : W := mkw 0x6008001420010b18 0x7211001c00000f1c

def z1342 : W := mkw 0xdc5c0000223356b7 0x7fc100000177fe9f

def z1343 : W := mkw 0x0090ee9f01dc8dc0 0x82d7fc9f01f88fe0

def z1344 : W := mkw 0x03a0ffffdc482000 0x003efffffe083000

def z1345 : W := mkw 0x00e0f7e001eee000 0x01cafb8001fff000

def z1346 : W := mkw 0x4008000020010210 0x737b8318e1878f1c

def z1347 : W := mkw 0x0300ffffdc000000 0x0000bf39e6000000

def z1348 : W := mkw 0x0090ec1f01d80dc0 0xb2d7fc9f11f88fec

def z1349 : W := mkw 0x6208c294b1858b18 0x71018318e1078e1c

def z1350 : W := mkw 0xf408000023859b3d 0xf3410000018fbf7c

def z1351 : W := mkw 0xb6a0e6b493ccb92d 0xb00044a51688b16c

def z1352 : W := mkw 0x03001beadc000000 0x003efffffe000000

def z1353 : W := mkw 0x0300ffffdc000000 0x017efffffe808000

def z1354 : W := mkw 0x4008000020010210 0x737b831cf1070f1c

def z1355 : W := mkw 0x0300e6b594000000 0x002847a5f6000000

def z1356 : W := mkw 0xdf1c081ffe1116b7 0xfe31001ffe000fff

def z1357 : W := mkw 0x00e037e001eee000 0x01cc3fe001fff000

def z1358 : W := mkw 0x0040194a48224000 0x01fefffffffff000

def z1359 : W := mkw 0x0380e41595c80940 0x8000440516880160

def z1360 : W := mkw 0x0390ffffddd80dc0 0x82f7ff1ffff80fe0

def z1361 : W := mkw 0x0380f7e0ddc80000 0x00eeffe0fff80000

def z1362 : W := mkw 0x485c194a68334692 0x4ffffffffffffe93

def z1363 : W := mkw 0x485c194a68334692 0x4e3fbb5ae9770e93

def z1364 : W := mkw 0x0300ffebdc000000 0x002effe3fe000000

def z1365 : W := mkw 0x01003d6b4c000000 0x002c3f63ee000000

def z1366 : W := mkw 0x00e0f7e001eee000 0x01cebbe00177f000

def z1367 : W := mkw 0x485c194a68334692 0x7fffbb5ef9774f9f

def z1368 : W := mkw 0x9400000002001025 0xffc444e71e88f1ff

def z1369 : W := mkw 0x0010c81f01900dc0 0x82d7f81f01f00fe0

def z1370 : W := mkw 0x0310ffffdd900dc0 0x827fffffff800fe0

def z1371 : W := mkw 0x0290ee9f91d80dc0 0xf3ffff9ff1f88ffc

def z1372 : W := mkw 0x0300ca9fdc000000 0x0030831ffe000000

def z1373 : W := mkw 0x0300081fdc000000 0x0034047ffe000000

def z1374 : W := mkw 0x230013e0dc048008 0x302803e0fe00800c

def z1375 : W := mkw 0x485c194a68334692 0xcfffffffe9fffff3

def z1376 : W := mkw 0x00902c0b005804c0 0x82c53c0301780ee0

def z1377 : W := mkw 0x6208c294b1858b18 0x737bc39fff878f1c

def z1378 : W := mkw 0x03e0ffffddeee000 0x01feffffff774000

def z1379 : W := mkw 0x0300eebfdc000000 0x0036fcbffe000000

def z1380 : W := mkw 0x0300ee9fdc000000 0x003eff9ffe000000

def z1381 : W := mkw 0x0090080a01d80dc0 0x82c1b81801f80fe0

def z1382 : W := mkw 0x0300ffffdc000000 0x0028fffdfe000000

def z1383 : W := mkw 0x0100fd7f4c000000 0x003eff7fee000000

def z1384 : W := mkw 0x00e0356001eee000 0x01cebf6001fff000

def z1385 : W := mkw 0x0300ffffdc000000 0x303efffffe80810c

def z1386 : W := mkw 0x0300195fdc000000 0x0030bb1ffe000000

def z1387 : W := mkw 0x03000000dc000000 0x003e44e7fe000000

def z1388 : W := mkw 0xb680e69593cc996d 0xb00044a51688b16c

def z1389 : W := mkw 0x00e0e40001eee000 0x01cefce001fff000

def z1390 : W := mkw 0x00e037e0006ee000 0x01ce7fe000fff000

def z1391 : W := mkw 0x62080014b0010b18 0x737bc39cf1878f1c

def z1392 : W := mkw 0x0300ffffdc000000 0x02fefffffe000080

def z1393 : W := mkw 0x62080280b0058218 0x737bc39cf1878f1c

def z1394 : W := mkw 0x030013e0dc048000 0x012803e0fe078000

def z1395 : W := mkw 0x03e0ffffddeee000 0x0128bbf8ff77f000

def z1396 : W := mkw 0x034013e0dc224000 0x012803e0fe074000

def z1397 : W := mkw 0x00e0356001eee000 0x01c0380001fff000

def z1398 : W := mkw 0x03e03febdc6ee000 0x01ac3fe3fe7ff000

def z1399 : W := mkw 0x0b14081fdc100482 0x0c30001ffe000083

def z1400 : W := mkw 0x481c080a68110692 0x4fff44fae888fe93

def z1401 : W := mkw 0x0300ca9fdc000000 0x0030409ffe000000

def z1402 : W := mkw 0x0350ffffdc324480 0x03ffffffff774e80

def z1403 : W := mkw 0x0bf4ffffddfee482 0x0dfefffffffff083

def z1404 : W := mkw 0x0200001490000000 0x0030001ffe000000

def z1405 : W := mkw 0x03e0ffffddea6000 0x00fefffffff87000

def z1406 : W := mkw 0x0390ffffdc5804c0 0x82fefffffef801e0

def z1407 : W := mkw 0x00e0f7e001eee000 0x01deffe701fff000

def z1408 : W := mkw 0x0300f7f5dc000000 0x003ac7fdfe000000

def z1409 : W := mkw 0x62a8e6b5b1cdab58 0xf37bc7bdf18fbf7c

def z1410 : W := mkw 0x00e0f7e001eee000 0xcffeffe709fff1f3

def z1411 : W := mkw 0xf498000023dd9ffd 0xffc1000001ffffff

def z1412 : W := mkw 0x03003febdc000000 0x00043f63ee000000

def z1413 : W := mkw 0x485c194a68334692 0x4fd7bb1ae1774e93

def z1414 : W := mkw 0x0300eebfdc000000 0x0030001ffe000000

def z1415 : W := mkw 0x0290ee9f91dc8dc0 0x83ffff9ff1ff8fe0

def z1416 : W := mkw 0x0290ec1f91d80dc0 0x82f7fc1ff1f80fe0

def z1417 : W := mkw 0x0090ec1f01d80dc0 0x8253fc1d01f80f60

def z1418 : W := mkw 0x0040114000224000 0x01cebbe00177f000

def z1419 : W := mkw 0xdc6c13e06a27f237 0x7d2803e0fe07f01f

def z1420 : W := mkw 0x0010ec1f00100480 0x82d7fc1f01f80fe0

def z1421 : W := mkw 0x0300ffffdc000000 0x0016ff7fee000000

def z1422 : W := mkw 0x0090ec0b01d804c0 0x82d7fc1b01f80ee0

def z1423 : W := mkw 0x0090ec1f01d80dc0 0xf2f7fc1f11f80ffc

def z1424 : W := mkw 0x6208c294b1858b18 0x72018318e1070f1c

def z1425 : W := mkw 0x0390ffffddd80480 0x02fffffffff80e80

def z1426 : W := mkw 0x03003d7fdc000000 0x0030381ffe000000

def z1427 : W := mkw 0xdc4c000022235237 0xffc00000008ff1ff

def z1428 : W := mkw 0x0300ffffdd848000 0x737effffff87811c

def z1429 : W := mkw 0x9400194a4a001025 0xfffebb5ae888f1ff

def z1430 : W := mkw 0x0300ffffdc000000 0x00feffffff700000

def z1431 : W := mkw 0x6208c014b1810b18 0x737bc31cf1870f1c

def z1432 : W := mkw 0x6288e694b1cd8b18 0x73fffffcf1ffff1c

def z1433 : W := mkw 0x0090ec1f01d80dc0 0x82d3f81c01f80fe0

def z1434 : W := mkw 0xf66813e0b227f23d 0x7d2803e0fe07f01f

def z1435 : W := mkw 0x0380ffffddcc8000 0x01feffffffff8000

def z1436 : W := mkw 0x0300ffffdd800900 0x737fffffff808f1c

def z1437 : W := mkw 0x485c194a68334692 0xcfffbb5ae9ff4ff3

def z1438 : W := mkw 0x034013e0dc224000 0x01eebbe0ff774000

def z1439 : W := mkw 0x6208c294b1858b18 0x7f7bc3dcf987cf1f

def z1440 : W := mkw 0xdc1c0000221116b7 0xfe01000000000fff

def z1441 : W := mkw 0x0090ec1f01d80dc0 0x83dffc9f01f88fe0

def z1442 : W := mkw 0x485c194a68334692 0x4ef7bb1ae9770e93

def z1443 : W := mkw 0x9400000002001025 0xfdac44e71e88f1ff

def z1444 : W := mkw 0x2290ee9f91dc8dc8 0x82d7fc1f01f80fe0

def z1445 : W := mkw 0x030013e0dc000000 0x002847e5fe000000

def z1446 : W := mkw 0x02e0f7f491eee900 0x03fffffcf1ffff00

def z1447 : W := mkw 0x6208c294b1858b18 0x7341c39cf1878f1c

def z1448 : W := mkw 0x00e037e0006ee000 0x01083be00077f000

def z1449 : W := mkw 0xf498ec1f23dd9ffd 0xffd7fc1f01ffffff

def z1450 : W := mkw 0x00e0f7e001eee940 0x81ceffe001fff160

def z1451 : W := mkw 0x03903d7fdc580dc0 0x82b53c7ffe780fe0

def z1452 : W := mkw 0xdc5c080a223356b7 0xffd7fc1f01ffffff

def z1453 : W := mkw 0x6208c294b1858b18 0x7129c39cf1878f1c

def z1454 : W := mkw 0x0300ffffdc000000 0x017effffff070000

def z1455 : W := mkw 0x62080294b0058b18 0x71290398f0078e1c

def z1456 : W := mkw 0x0380ec1fddc80000 0x00f6fc1ffff80000

def z1457 : W := mkw 0x0390ffffddd80dc0 0x8001ffbdf7f80f60

def z1458 : W := mkw 0x08e4f7e049eee002 0x0dceffe009fff003

def z1459 : W := mkw 0x00e0f7e001eee000 0x03deffe401fff100

def z1460 : W := mkw 0x62080280b0058218 0x73390398f0078e1c

def z1461 : W := mkw 0x0300c81fdd800900 0x0273c01fff800f00

def z1462 : W := mkw 0x0300ffffdc000000 0x01fefffffe004000

def z1463 : W := mkw 0x00902c1f00580dc0 0x82d7bc1f01780fe0

def z1464 : W := mkw 0x0390eebfddd80dc0 0x823144bffe880fe0

def z1465 : W := mkw 0x0090ec1f00580dc0 0x8297fc1f00780fe0

def z1466 : W := mkw 0x032013e0dc04a000 0x002803e0fe00b000

def z1467 : W := mkw 0x9790ec1fdfd81de5 0xfffffcfffff8ffff

def z1468 : W := mkw 0x036013e0dc226000 0x002803e0fe007000

def z1469 : W := mkw 0x485c194a68334692 0x4f7bbb1ae9770e93

def z1470 : W := mkw 0xdcfc000023fff6b7 0xffc1000001ffffff

def z1471 : W := mkw 0x02e0f7f491eee000 0x73fefffcf1fff11c

def z1472 : W := mkw 0x0300ffffdc000000 0x027efffffe800100

def z1473 : W := mkw 0x0010081f00100dc0 0x8211b81f01700fe0

def z1474 : W := mkw 0x0310081fdc100480 0x0231001ffe000e80

def z1475 : W := mkw 0x0300ffffdc000000 0x0000bb1df6000000

def z1476 : W := mkw 0x2300ffffdd848908 0x737efffffe80811c

def z1477 : W := mkw 0x03f0ffffddfee480 0x03fffffffffffe80

def z1478 : W := mkw 0xdc4c11406a235237 0x7d280340fe07401f

def z1479 : W := mkw 0x6208c294b1858b18 0x737b8398f1078e1c

def z1480 : W := mkw 0xfe1c081efa111fbf 0xfe31001ffe000fff

def z1481 : W := mkw 0x0360ffffdc26e000 0x01feffffff77f000

def z1482 : W := mkw 0x0090ee9f01dc8dc0 0x83dfffff01ffffe0

def z1483 : W := mkw 0x00902c1f00580dc0 0x80853c1b00780ee0

def z1484 : W := mkw 0x00e0f7e001eee000 0x4ffeffe71ffff093

def z1485 : W := mkw 0x0300ffffdc000000 0x7ffefffffe80c19f

def z1486 : W := mkw 0x0090080a01d80dc0 0x82c5380201f80fe0

def z1487 : W := mkw 0x0200c28091848000 0x016ac380f1878000

def z1488 : W := mkw 0x6208c294b1858b18 0x723bc39cf1070f1c

def z1489 : W := mkw 0x0090ec1f01d80dc0 0x82d7fcbf01f8bfe0

def z1490 : W := mkw 0x0b541beadc324482 0x0cac3be2fe704083

def z1491 : W := mkw 0x00e0f7f401eee900 0x01ceffe401fff100

def z1492 : W := mkw 0x03e0ffffddeee000 0x83fefffffffff1e0

def z1493 : W := mkw 0x0300c29594000000 0x003ac39df6000000

def z1494 : W := mkw 0x0390ffffdc5804c0 0x003efffffe700000

def z1495 : W := mkw 0x485c194a68334692 0x4fffff5fe9774e93

def z1496 : W := mkw 0x0090ec1f01d80dc0 0x82d7fcbf17f80fe0

def z1497 : W := mkw 0x0090fd5f49d80dc0 0x82fffffffff80fe0

def z1498 : W := mkw 0x0100194b4c000000 0x003ebb5bee000000

def z1499 : W := mkw 0x0b4413e0dc224002 0x0c2803e0fe004003

def z1500 : W := mkw 0x0360ffffdc26e000 0x01fefffffe8ff000

def z1501 : W := mkw 0x0300ffffdc000000 0x00347cfffe000000

def z1502 : W := mkw 0x030037e1dc000000 0x002807e1fe000000

def z1503 : W := mkw 0x0300194adc000000 0x003ebb5afe000000

def z1504 : W := mkw 0x00e0f7e001eee000 0x4deeffe009fff013

def z1505 : W := mkw 0x0b54ffffdc324482 0x0effffffff704e83

def z1506 : W := mkw 0x6288e694b1cd8b18 0xf3ffff9ff1ff8ffc

def z1507 : W := mkw 0x0090ec1f01d80dc0 0x82d7fc7f0ff80fe0

def z1508 : W := mkw 0x00e0f7e001eee000 0x0000bf20017f3000

def z1509 : W := mkw 0x0300081fdc000000 0x003a831ffe000000

def z1510 : W := mkw 0x0310ffffdc100480 0x00befffffe700080

def z1511 : W := mkw 0x0290ee9f91d80dc0 0x82d7fc9f11f80fe0

def z1512 : W := mkw 0x0300e6b594000000 0x003ec7fffe000000

def z1513 : W := mkw 0x0190fd7f4dd80dc0 0x82ffff7feff80fe0

def z1514 : W := mkw 0x03a0ffffddcca000 0x00fefffffff8b000

def z1515 : W := mkw 0x0300f7f594000000 0x003efffdf6000000

def z1516 : W := mkw 0x9400000002001025 0xfffefce71ff8f1ff

def z1517 : W := mkw 0x6208c294b1858b18 0x73ffc79cf18f8f1c

def z1518 : W := mkw 0x0040114048224000 0x01eebb40e9774000

def z1519 : W := mkw 0x0090ec1f01d80dc0 0x8001bc1901780e60

def z1520 : W := mkw 0x0310081fdc100480 0x02f7b81fff700e80

def z1521 : W := mkw 0x62080014b0010b18 0x7231831cf1070f1c

def z1522 : W := mkw 0x0300dbfedc000000 0x003efbfefe000000

def z1523 : W := mkw 0x0360ffffdc26e000 0x003efffffe070000

def z1524 : W := mkw 0x0000000000000000 0x003ec7fffe000000

def z1525 : W := mkw 0x2300ffffdc000908 0x303efffffe00010c

def z1526 : W := mkw 0x03003d7fdc000000 0x003ebf7ffe000000

def z1527 : W := mkw 0x01e035604c6a6000 0x00843c600e787000

def z1528 : W := mkw 0x0090ec1f01d80dc0 0xcfd7fc1f01f84ff3

def z1529 : W := mkw 0x03a0ffffddcca000 0x017effffff8fb000

def z1530 : W := mkw 0x0380ffffddc80000 0x82fefffffff801e0

def z1531 : W := mkw 0x485c194a68334692 0x7ffffffffff7cf9f

def z1532 : W := mkw 0x0010080a00100480 0x82d7bc1b01780ee0

def z1533 : W := mkw 0x6208e694b1858b18 0x737fff9cf1878f1c

def z1534 : W := mkw 0x6208c294b1858b18 0x30018398f1078e0c

def z1535 : W := mkw 0x03a0ffffddcca000 0x01fefffffe88f000

def z1536 : W := mkw 0x0300f7f5dc000000 0x000047a5f6000000

def z1537 : W := mkw 0x0090ec1f01d80dc0 0x82d7b81a01f80fe0

def z1538 : W := mkw 0x00e0f7e001eee000 0x010effe00177f000

def z1539 : W := mkw 0x0090ec1f01d80dc0 0x8085fc1f01f80fe0

def z1540 : W := mkw 0x9400000002001025 0xfeb444e71e88f1ff

def z1541 : W := mkw 0x030013f4dc000000 0x003803fcfe000000

def z1542 : W := mkw 0x0090080a005804c0 0x82d7b81a01780ee0

def z1543 : W := mkw 0x00e0f7e001eee000 0x0000bba00177b000

def z1544 : W := mkw 0x6208c294b0010b18 0x737bc39cf1070f1c

def z1545 : W := mkw 0x485c194a68334692 0x0c81bb18e1774e83

def z1546 : W := mkw 0x0000194a48000000 0x003ebf7bee000000

def z1547 : W := mkw 0x0390ffffddd80dc0 0x82d7ff7feff80fe0

def z1548 : W := mkw 0x00e0f7e001eee000 0x01c4bf6001fff000

def z1549 : W := mkw 0x0300ffffdc000000 0x0004fffffe000000

def z1550 : W := mkw 0x0360d3f4dda6e000 0x017ac3fcff87f000

def z1551 : W := mkw 0x00902c0b005804c0 0x82953c1b00780ee0

def z1552 : W := mkw 0x0380ffffddc80900 0x02fffffffff80f00

def z1553 : W := mkw 0x036013e0dc26e000 0x01fe47e7fe8ff000

def z1554 : W := mkw 0x6208c294b1858b18 0x7ffbc39cf187cf9f

def z1555 : W := mkw 0x03e0ffffddeee000 0x01cefffdf7fff000

def z1556 : W := mkw 0x62080280b1858b18 0x737b8398f1878f1c

def z1557 : W := mkw 0x0090ee9f01d80dc0 0x82dfff9f01f80fe0

def z1558 : W := mkw 0x03a0ffffddcca000 0x003efffffe000000

def z1559 : W := mkw 0x00e0f7e001eee000 0x01feffe209fff000

def z1560 : W := mkw 0x0390081fddd80dc0 0x82f1001ffff80fe0

def z1561 : W := mkw 0x0300ffffdc000000 0x003ebbfafe000000

def z1562 : W := mkw 0x0340ffffdc224000 0x003effffff770000

def z1563 : W := mkw 0x0390ffffddd80dc0 0x82d7ffbff7f80fe0

def z1564 : W := mkw 0x0300e6b5dc000000 0x002044a5fe000000

def z1565 : W := mkw 0x97e0f7e0dfeef025 0xfffeffe7fffff1ff

def z1566 : W := mkw 0x0300081fdc000000 0x8230001ffe0001e0

def z1567 : W := mkw 0x2300ffffdc048008 0x303efffffe00800c

def z1568 : W := mkw 0x03903febdc5804c0 0x80ac3fe3fe7800e0

def z1569 : W := mkw 0x00e013e001eee000 0x01cebbe001fff000

def z1570 : W := mkw 0x0340ffffdc224000 0x00befffffe704000

def z1571 : W := mkw 0x0380ffffddc80000 0x01fefffffff8f000

def z1572 : W := mkw 0x0010080a00100480 0x82d7b81f01700fe0

def z1573 : W := mkw 0x0300195fdc000000 0x003efffffe000000

def z1574 : W := mkw 0x0090e40001d80dc0 0x82c1b80001f80fe0

def z1575 : W := mkw 0x2390eebf95dc8dc8 0xb2d7fcbf17f88fec

def z1576 : W := mkw 0x00e0f7e001eee000 0x0000bb6001777000

def z1577 : W := mkw 0x6308e6b5b5858b18 0x737bc39cf1878f1c

def z1578 : W := mkw 0x9400000002001025 0xff3844e71e88f1ff

def z1579 : W := mkw 0x485c194a68334692 0x4c21bb18e9770e13

def z1580 : W := mkw 0x00e0f7e001eee000 0x018cbfe0017ff000

def z1581 : W := mkw 0x00e0f7e001eee000 0x00c6ffa001ffb000

def z1582 : W := mkw 0x2300ffffdd848908 0x317effffff87810c

def z1583 : W := mkw 0xf40800002205923d 0xffc00000008ff1ff

def z1584 : W := mkw 0x9400000002001025 0x7d0800e00000f01f

def z1585 : W := mkw 0x00e0f7e001eee000 0x014affa001ffb000

def z1586 : W := mkw 0x62a8e6b4b1cdab18 0x737bc39cf1878f1c

def z1587 : W := mkw 0x0340ffffdc224000 0x013efffffe074000

def z1588 : W := mkw 0x481c080a20110692 0x4e11001a00000e93

def z1589 : W := mkw 0x6208c294b1858b18 0x7f7bc39ef9878f9f

def z1590 : W := mkw 0x23a0ffffddcca908 0x303efffffe88b10c

def z1591 : W := mkw 0x03f0ffffdc7a64c0 0x80befffffe7870e0

def z1592 : W := mkw 0x0390ffffddd80dc0 0x0029bbf8ff700e00

def z1593 : W := mkw 0x0300081fdc000900 0x0231001ffe000f00

def z1594 : W := mkw 0xfc5c000023b7dfbf 0xffc1000001ffffff

def z1595 : W := mkw 0x00e0f7e101eee040 0x81ceffe101fff060

def z1596 : W := mkw 0x485c194a68334692 0x4eb5bb5ae9774e93

def z1597 : W := mkw 0x0010081f00100dc0 0x8295381f00700fe0

def z1598 : W := mkw 0x2290ee9f91dc8dc8 0xb3dfff9f11ff8fec

def z1599 : W := mkw 0x03001beadc000000 0x002c3be2fe000000

def z1600 : W := mkw 0x00b0ec1f01dcadc0 0x82d7fc1f01f8bfe0

def z1601 : W := mkw 0x0380ffffddc80000 0x003effffff700000

def z1602 : W := mkw 0xdc1c080a6a1116b7 0xce31001bee000ef3

def z1603 : W := mkw 0x0300195fdc000000 0x0038035ffe000000

def z1604 : W := mkw 0x0300197fdc000000 0x0030007ffe000000

def z1605 : W := mkw 0x2090ec1f01dc8dc8 0xb2d7fc1f01f88fec

def z1606 : W := mkw 0xdf4c13e0fe235237 0x7d2803e0fe07f01f

def z1607 : W := mkw 0x00e0f7e0006ee000 0x018effe0007ff000

def z1608 : W := mkw 0x0090ec1f01d80dc0 0x83d7fc1f01f8ffe0

def z1609 : W := mkw 0x0b14ffffdc100482 0x0c3efffffe000083

def z1610 : W := mkw 0x00e03560006a6000 0x0084bf60017f7000

def z1611 : W := mkw 0x6288c294b1cd8b58 0xf37bc39cf18f8f7c

def z1612 : W := mkw 0x03e037e0dc6a6000 0x00ac3fe0fe787000

def z1613 : W := mkw 0x0300ffffdc000000 0x027fffffff000e00

def z1614 : W := mkw 0x0090ec1f01d80dc0 0xf3fffcff11f8fffc

def z1615 : W := mkw 0x0200f7f490000000 0x003efffffe000000

def z1616 : W := mkw 0x0090ec1f01d80dc0 0xc3fffc1f01f80ff0

def z1617 : W := mkw 0x0390ffffddd804c0 0x80fefffffff800e0

def z1618 : W := mkw 0x0380ffffddc80000 0x003efffffe880000

def z1619 : W := mkw 0x6208c294b1858b18 0x7273c31cf1870f1c

def z1620 : W := mkw 0x0310ffffdc100480 0x003fffffff700e00

def z1621 : W := mkw 0x03003d7fdc000000 0x003e7cfffe000000

def z1622 : W := mkw 0x0300ffffdc000000 0x003afb9ffe000000

def z1623 : W := mkw 0x6208c294b1858b18 0x73ffc3dcf187cf1c

def z1624 : W := mkw 0x62080294b1858b18 0x7379039cf1878f1c

def z1625 : W := mkw 0x485c194a68334692 0x4f39bb5ae9774e93

def z1626 : W := mkw 0x0bd4ffffdc7a44c2 0x8cbefffffe7840e3

def z1627 : W := mkw 0x0090ec1f01d80dc0 0x8081b81801780ee0

def z1628 : W := mkw 0x00e0f7e001eee000 0x31ceffe411fff10c

def z1629 : W := mkw 0x6208c294b1858b18 0x73698398f1878f1c

def z1630 : W := mkw 0x9400000002001025 0xfffec7fffe88f1ff

def z1631 : W := mkw 0x9c54194a4a3254a7 0x0c8438620e707083

def z1632 : W := mkw 0x0300081fdc000000 0x4e30001ffe000093

def z1633 : W := mkw 0x6208c294b1858b18 0xf3ffc7fff18ffffc

def z1634 : W := mkw 0x00e0f7e001eee000 0x00c6ff6001ff7000

def z1635 : W := mkw 0x22e0f7e091eee008 0x31ceffe011fff00c

def z1636 : W := mkw 0x485c194a68334692 0xffffffdff9ffcfff

def z1637 : W := mkw 0x485c194a68334692 0x4ffffffae9774e93

def z1638 : W := mkw 0x9cf43d6a4a7a74a7 0x8c843c630e7870e3

def z1639 : W := mkw 0x00e0f7f501eee000 0x01ceffe501fff000

def z1640 : W := mkw 0x03e0ffffddeee000 0x00beffffff7f7000

def z1641 : W := mkw 0x0010194a48100480 0x82fffffffff80fe0

def z1642 : W := mkw 0x03f0ffffddfeedc0 0x82ffffffffff0fe0

def z1643 : W := mkw 0x62080014b1858b18 0x737b831cf1878f1c

def z1644 : W := mkw 0xdc1c081f6a111ff7 0xfe31001ffe000fff

def z1645 : W := mkw 0x62a8c294b1cdab18 0x737bc39cf18fbf1c

def z1646 : W := mkw 0x6208c294b1858b18 0x7231c39cf1878f1c

def z1647 : W := mkw 0x030013e0dc000000 0x012803e0fe00f000

def z1648 : W := mkw 0x00e0f7e001eee900 0x03cfffe001ffff00

def z1649 : W := mkw 0x00e0ffea49eee000 0x01fefffffffff000

def z1650 : W := mkw 0x0390ffffddd80dc0 0x00fffffffff80e00

def z1651 : W := mkw 0x00e0f7e001eee000 0x000effe001ffb000

def z1652 : W := mkw 0xf408000022011b3d 0xfe01000000000fff

def z1653 : W := mkw 0x9d543d6b4e3254a7 0x8c843c630e7870e3

def z1654 : W := mkw 0x03e0ffffddeee000 0x00befffffef8f000

def z1655 : W := mkw 0xf618081fb2111ffd 0xfe31001ffe000fff

def z1656 : W := mkw 0x01003d6b4c000000 0x003efffffe000000

def z1657 : W := mkw 0x0380ec1fddc80940 0x8030441ffe880160

def z1658 : W := mkw 0x0300ffffdc000000 0x80befffffe0800e0

def z1659 : W := mkw 0x0000080a48000000 0x003e44fffe000000

def z1660 : W := mkw 0x485c194a68334692 0x4fffbbfae977fe93

def z1661 : W := mkw 0x0300e6b594000000 0x003044bdf6000000

def z1662 : W := mkw 0x03e0f7e0ddeee000 0x0028bbe0ff770000

def z1663 : W := mkw 0x0340ffffdc224000 0x4ffeffffff774093

def z1664 : W := mkw 0x485c194a68334692 0x4dadbb5ae9774e93

def z1665 : W := mkw 0x00e0f7e001eee000 0x81ceffe301fff0e0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(1,[z7,z2,z8,z9,z5,z6]),(0,[z10,z1,z2,z8,z4,z11,z6]),(0,[z1,z2,z8,z12,z4,z13,z6])],[(0,[z14,z15,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z16,z5,z6]),(0,[z1,z17,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z6]),(0,[z1,z2,z3,z19,z4,z5,z6]),(0,[z1,z2,z20,z4,z21,z5,z6])],[(1,[z22,z2,z8,z4,z23,z6]),(1,[z1,z3,z4,z5,z24,z6]),(1,[z25,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z26,z4,z5,z6]),(1,[z27,z1,z2,z8,z4,z28])],[(0,[z1,z2,z8,z4,z29,z5,z6]),(1,[z30,z1,z8,z4,z5,z31]),(1,[z32,z2,z8,z4,z5,z6]),(0,[z33,z1,z2,z34,z4,z5,z6])],[(0,[z1,z2,z8,z35,z4,z5,z6]),(0,[z1,z2,z36,z36,z4,z5,z6]),(0,[z33,z37,z2,z8,z4,z5,z6])],[(0,[z2,z8,z9,z4,z38,z5,z6]),(0,[z1,z2,z8,z39,z4,z5,z6]),(0,[z1,z40,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z41,z6])],[(0,[z15,z2,z8,z4,z5,z42,z6]),(0,[z1,z2,z8,z9,z19,z5,z6]),(0,[z1,z2,z8,z4,z43,z5,z6]),(0,[z1,z2,z8,z4,z5,z44,z6]),(0,[z1,z2,z8,z4,z5,z6,z45]),(0,[z46,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z5,z6]),(0,[z22,z2,z8,z4,z23,z5,z6]),(0,[z47,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z48,z5,z6])],[(0,[z49,z50,z2,z8,z4,z5,z6]),(0,[z51,z1,z2,z8,z21,z5,z6]),(0,[z1,z2,z52,z8,z4,z5,z53]),(0,[z54,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z55,z4,z5,z6]),(0,[z1,z2,z8,z4,z56,z5,z6]),(0,[z1,z2,z57,z8,z4,z5,z6])],[(1,[z1,z58,z59,z4,z5,z6]),(0,[z60,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z61,z6])],[(0,[z1,z2,z52,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z62]),(0,[z1,z2,z63,z52,z4,z5,z6])],[(0,[z64,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z65,z5,z6]),(0,[z1,z2,z8,z66,z4,z5,z6]),(1,[z1,z67,z8,z4,z5,z6]),(0,[z68,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z69]),(0,[z1,z2,z8,z4,z5,z70,z6])],[]],
   [[(0,[z1,z2,z36,z58,z4,z5,z6])],[(0,[z1,z71,z8,z72,z4,z5,z6]),(0,[z1,z2,z36,z4,z38,z5,z6]),(0,[z1,z2,z8,z73,z4,z42,z6]),(0,[z1,z2,z4,z74,z5,z44,z6]),(1,[z1,z2,z52,z4,z5,z75])],[(0,[z1,z2,z76,z72,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z77,z6]),(0,[z1,z2,z8,z4,z78,z5,z6])],[],[(0,[z30,z1,z2,z8,z79,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z80])],[(0,[z1,z81,z2,z3,z4,z5,z6]),(1,[z1,z2,z82,z4,z5,z6]),(1,[z1,z2,z83,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z84,z85])],[(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z1,z86,z2,z8,z4,z5,z6]),(0,[z1,z2,z12,z87,z4,z5,z6])],[(0,[z88,z1,z2,z76,z4,z5,z6]),(0,[z2,z8,z76,z9,z4,z5,z6]),(0,[z89,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z6,z53])],[(0,[z90,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z91]),(0,[z1,z2,z8,z4,z5,z6,z92])],[(0,[z1,z2,z8,z4,z5,z6,z93]),(0,[z33,z1,z94,z8,z4,z5,z6])],[(0,[z1,z2,z76,z73,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z95,z6]),(0,[z1,z2,z36,z4,z5,z18,z6]),(0,[z1,z2,z36,z19,z4,z5,z6]),(0,[z1,z2,z8,z4,z79,z5,z6]),(0,[z1,z2,z8,z96,z4,z5,z6])],[(0,[z30,z1,z2,z8,z4,z97,z6]),(0,[z1,z2,z8,z4,z5,z98,z6])],[(0,[z1,z2,z8,z4,z99,z5,z6]),(0,[z1,z2,z76,z4,z5,z100,z6]),(0,[z1,z2,z36,z4,z5,z6,z85]),(0,[z51,z1,z2,z4,z5,z44,z6])],[(0,[z15,z1,z2,z101,z4,z5,z6]),(0,[z15,z2,z8,z4,z5,z6,z102]),(1,[z1,z2,z103,z4,z5,z6]),(1,[z104,z1,z8,z105,z5,z6])],[(0,[z1,z2,z8,z4,z106,z5,z6]),(0,[z1,z2,z8,z4,z107,z5,z6]),(0,[z1,z8,z4,z105,z5,z6,z31])],[(0,[z1,z2,z108,z76,z4,z5,z6]),(0,[z7,z1,z2,z8,z4,z109,z6]),(0,[z110,z1,z2,z8,z4,z42,z6]),(1,[z1,z2,z8,z111,z5,z6]),(0,[z1,z2,z112,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z113,z5,z6]),(0,[z1,z2,z8,z4,z114,z5,z6]),(0,[z1,z2,z4,z5,z44,z6,z53]),(0,[z1,z2,z8,z4,z5,z6,z115])]],
   [[(0,[z104,z1,z2,z76,z4,z5,z6]),(1,[z1,z2,z8,z4,z116,z6]),(1,[z1,z2,z117,z4,z5,z6]),(1,[z2,z118,z8,z4,z5,z6])],[(0,[z119,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z19,z38,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z6]),(0,[z1,z2,z8,z120,z4,z5,z6])],[(0,[z121,z1,z122,z8,z4,z5,z6]),(0,[z1,z2,z123,z8,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z75,z6]),(0,[z51,z1,z2,z8,z4,z5,z6])],[(0,[z1,z1,z2,z76,z4,z5,z6]),(0,[z124,z1,z2,z8,z4,z5,z6]),(0,[z7,z1,z2,z8,z9,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z1,z2,z125,z8,z4,z5,z6])],[(0,[z1,z2,z126,z58,z4,z5,z6]),(0,[z88,z1,z2,z8,z127,z5,z6]),(0,[z1,z2,z128,z8,z4,z5,z6]),(0,[z10,z1,z2,z8,z129,z5,z6])],[(1,[z1,z2,z130,z4,z5,z6]),(0,[z1,z2,z8,z108,z4,z5,z6]),(1,[z50,z2,z58,z4,z5,z6]),(0,[z131,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z132,z8,z4,z5,z6]),(1,[z104,z1,z3,z4,z5,z6]),(0,[z1,z81,z2,z133,z4,z5,z6])],[(0,[z14,z1,z2,z8,z4,z5,z6])],[],[(0,[z104,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z8,z72,z19,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z134])],[(0,[z135,z136,z2,z8,z4,z5,z6]),(0,[z137,z1,z2,z8,z4,z5,z6]),(0,[z10,z1,z128,z8,z4,z5,z6])],[(0,[z1,z58,z8,z59,z4,z5,z6])],[(1,[z1,z2,z138,z4,z5,z6]),(1,[z1,z2,z139,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z140]),(0,[z1,z2,z8,z141,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z42,z6]),(0,[z1,z2,z8,z4,z5,z142,z6]),(0,[z1,z122,z36,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z143]),(0,[z1,z2,z144,z8,z4,z114,z6]),(0,[z10,z145,z2,z8,z4,z5,z6])],[(0,[z1,z146,z2,z8,z4,z5,z6])]],
   [[(0,[z47,z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z63,z36,z4,z5,z6]),(0,[z1,z148,z2,z8,z4,z5,z6])],[(0,[z15,z1,z2,z8,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z150,z6])],[(0,[z1,z2,z8,z4,z5,z6,z151]),(0,[z1,z2,z8,z73,z19,z5,z6])],[(0,[z152,z1,z2,z8,z4,z5,z6]),(0,[z153,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z12,z4,z6,z28])],[(0,[z1,z2,z154,z8,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z155,z4,z5,z6])],[(0,[z1,z2,z8,z4,z74,z5,z6])],[(0,[z1,z8,z4,z5,z18,z6,z31])],[(0,[z156,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z24,z6]),(0,[z1,z2,z8,z157,z4,z6,z85])],[(0,[z49,z1,z2,z8,z4,z5,z6]),(0,[z10,z51,z1,z2,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z158,z6])],[(0,[z1,z81,z71,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z159,z5,z6]),(0,[z1,z2,z8,z160,z4,z5,z6]),(0,[z1,z2,z8,z4,z161,z5,z6]),(0,[z1,z162,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z163]),(0,[z1,z2,z8,z4,z13,z5,z28])],[(0,[z1,z2,z63,z58,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z75,z6]),(0,[z1,z2,z8,z4,z5,z164,z6])],[(0,[z14,z50,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z165,z4,z5,z6])],[],[(0,[z1,z166,z2,z8,z4,z5,z6]),(0,[z1,z2,z167,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z168,z6])],[(0,[z1,z169,z2,z8,z4,z5,z6]),(0,[z170,z1,z2,z8,z4,z5,z6])]],
   [[(1,[z1,z171,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z172,z5,z6]),(1,[z2,z36,z173,z4,z5,z6])],[(0,[z1,z2,z58,z58,z4,z5,z6]),(0,[z14,z2,z8,z4,z5,z42,z6]),(0,[z1,z122,z174,z8,z4,z5,z6]),(0,[z1,z2,z8,z175,z4,z65,z6]),(0,[z1,z2,z8,z4,z176,z5,z6]),(0,[z1,z2,z52,z4,z5,z75,z6])],[(0,[z1,z2,z58,z4,z38,z5,z6]),(0,[z1,z2,z36,z175,z4,z5,z6]),(0,[z1,z2,z63,z4,z5,z6,z53])],[(0,[z1,z2,z8,z4,z177,z5,z6]),(0,[z1,z2,z8,z4,z5,z178,z6])],[(0,[z1,z2,z36,z4,z5,z6,z102]),(0,[z1,z122,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z179,z6]),(0,[z1,z2,z8,z5,z168,z6,z85])],[(0,[z180,z1,z2,z8,z4,z5,z6]),(1,[z110,z2,z8,z4,z42,z6]),(0,[z1,z2,z8,z4,z181,z5,z6]),(0,[z182,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z183]),(0,[z1,z122,z2,z3,z4,z5,z6])],[(1,[z1,z8,z4,z5,z6,z84])],[(0,[z184,z1,z2,z8,z4,z5,z6]),(0,[z185,z1,z2,z76,z4,z5,z6]),(0,[z186,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z58,z4,z5,z6,z53])],[(0,[z187,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z144,z4,z5,z6])],[(1,[z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z36,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z24,z6,z28])],[(0,[z1,z2,z58,z4,z5,z18,z6]),(0,[z1,z2,z58,z19,z4,z5,z6])],[(0,[z1,z2,z188,z8,z4,z5,z6]),(0,[z1,z2,z76,z76,z4,z5,z6]),(0,[z1,z2,z8,z175,z4,z23,z6]),(0,[z10,z1,z2,z20,z4,z5,z6])],[(1,[z2,z58,z76,z4,z5,z6]),(0,[z1,z2,z58,z4,z5,z6,z85])],[(0,[z1,z2,z8,z4,z189,z5,z6]),(0,[z1,z190,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z9,z5,z6,z85]),(0,[z1,z2,z8,z4,z158,z6,z28])],[(0,[z1,z122,z2,z58,z4,z5,z6]),(0,[z1,z2,z191,z8,z4,z5,z6]),(0,[z27,z1,z2,z8,z4,z13,z6])]],
   [[],[(0,[z1,z2,z8,z8,z4,z5,z6]),(0,[z192,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z193])],[(0,[z1,z2,z8,z4,z5,z194,z6]),(0,[z1,z195,z2,z8,z4,z5,z6]),(0,[z196,z2,z20,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z111,z5,z6]),(0,[z1,z197,z2,z8,z4,z5,z6]),(0,[z1,z2,z94,z8,z4,z5,z6])],[(0,[z1,z2,z76,z4,z198,z5,z6]),(0,[z104,z1,z122,z8,z4,z5,z6]),(0,[z1,z122,z8,z4,z5,z6,z31]),(0,[z1,z2,z20,z36,z4,z5,z6])],[(1,[z1,z2,z58,z4,z5,z6]),(0,[z47,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z199,z8,z4,z5,z6])],[(0,[z200,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z58,z52,z4,z5,z6]),(1,[z1,z201,z8,z4,z5,z6]),(0,[z33,z202,z2,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z203,z28])],[(0,[z204,z1,z2,z8,z4,z5,z6]),(0,[z205,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z206,z4,z5,z6])],[(0,[z15,z2,z8,z9,z4,z5,z6]),(0,[z49,z1,z2,z207,z4,z5,z6]),(1,[z1,z2,z208,z4,z5,z6])],[(0,[z1,z135,z2,z58,z4,z5,z6])],[(0,[z209,z1,z174,z8,z4,z5,z6]),(0,[z1,z81,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z210,z4,z5,z6]),(0,[z211,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z212])],[(0,[z213,z1,z2,z8,z4,z5,z6]),(0,[z104,z49,z1,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z6]),(1,[z1,z2,z8,z175,z61,z6])],[(0,[z49,z1,z2,z214,z4,z5,z6]),(0,[z90,z1,z2,z8,z4,z5,z6]),(0,[z209,z1,z2,z36,z4,z5,z6])],[(0,[z50,z2,z58,z8,z4,z5,z6]),(0,[z1,z135,z8,z4,z5,z6,z31])],[(0,[z1,z2,z58,z4,z5,z42,z6]),(0,[z1,z2,z20,z58,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z215,z4,z5,z6]),(1,[z1,z2,z216,z4,z5,z6]),(0,[z1,z217,z2,z8,z4,z5,z6]),(0,[z218,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z219])],[(0,[z1,z2,z8,z4,z5,z220,z6]),(0,[z1,z2,z144,z52,z4,z5,z6])],[(0,[z221,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z72,z4,z5,z24,z6]),(0,[z1,z2,z222,z4,z5,z75,z6]),(0,[z223,z1,z2,z8,z4,z5,z6])],[],[(0,[z89,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z224]),(0,[z1,z2,z3,z4,z5,z168,z6]),(0,[z1,z2,z8,z72,z4,z5,z6]),(1,[z1,z225,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z226,z6]),(0,[z1,z2,z8,z227,z4,z5,z6])],[(0,[z1,z2,z228,z8,z4,z5,z6]),(0,[z2,z8,z9,z4,z5,z42,z6]),(0,[z229,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z230,z6])],[(0,[z1,z2,z76,z4,z105,z5,z6]),(0,[z231,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z4,z21,z5,z6,z53])],[(0,[z121,z2,z8,z76,z4,z5,z6]),(0,[z209,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z232,z8,z4,z5,z6])],[(1,[z1,z2,z8,z157,z4,z6])],[(0,[z49,z1,z81,z8,z4,z5,z6]),(0,[z1,z2,z8,z233,z4,z5,z6])],[(0,[z1,z234,z2,z8,z4,z5,z6]),(0,[z104,z1,z2,z8,z72,z5,z6]),(0,[z209,z1,z2,z82,z4,z5,z6]),(0,[z1,z2,z8,z73,z4,z44,z6])],[(0,[z1,z2,z58,z4,z5,z75,z6]),(0,[z1,z2,z8,z73,z4,z5,z6])],[(0,[z235,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z236,z5,z6]),(0,[z1,z2,z8,z4,z237,z5,z6])],[(1,[z2,z76,z4,z5,z6,z102]),(0,[z7,z1,z2,z238,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z100,z6]),(0,[z1,z2,z8,z4,z5,z239,z6]),(0,[z1,z2,z8,z4,z240,z5,z6])],[(0,[z1,z2,z8,z4,z5,z241,z6]),(0,[z10,z1,z67,z8,z4,z5,z6]),(1,[z1,z2,z8,z242,z5,z6]),(1,[z1,z2,z8,z243,z5,z6])]],
   [[(0,[z1,z2,z8,z207,z4,z5,z6]),(0,[z51,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z222,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z8,z73,z4,z61,z6])],[(0,[z90,z50,z2,z8,z4,z5,z6]),(0,[z1,z2,z244,z36,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z245,z6]),(0,[z1,z2,z8,z4,z5,z6,z246])],[(0,[z1,z2,z8,z4,z5,z247,z6])],[(0,[z1,z2,z58,z175,z4,z5,z6]),(0,[z7,z1,z2,z248,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(1,[z1,z2,z249,z4,z5,z6])],[(0,[z1,z2,z58,z4,z5,z6,z102]),(0,[z1,z2,z3,z4,z5,z61,z6]),(0,[z1,z2,z63,z3,z4,z5,z6]),(0,[z250,z2,z8,z4,z5,z6,z85])],[(0,[z1,z2,z8,z4,z105,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z251])],[(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z252,z135,z2,z8,z4,z5,z6])],[(0,[z1,z2,z76,z4,z23,z5,z6]),(0,[z30,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z253,z6]),(0,[z254,z1,z2,z8,z4,z5,z6])],[(0,[z121,z1,z2,z8,z4,z255,z6]),(1,[z1,z2,z256,z4,z5,z6]),(0,[z1,z174,z2,z58,z4,z5,z6]),(0,[z1,z2,z257,z8,z4,z5,z6])],[(0,[z110,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z160,z3,z4,z5,z6]),(0,[z258,z1,z2,z8,z4,z5,z6]),(1,[z259,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z260,z5,z6])],[(1,[z1,z2,z59,z4,z5,z6]),(0,[z1,z2,z58,z3,z4,z5,z6])],[(0,[z1,z2,z8,z4,z261,z5,z6]),(0,[z1,z2,z8,z262,z4,z5,z6]),(1,[z33,z1,z2,z8,z5,z85])],[(0,[z1,z2,z8,z4,z5,z6,z263]),(0,[z1,z2,z8,z264,z4,z5,z6])],[(0,[z15,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z265,z4,z5,z6]),(0,[z266,z1,z2,z8,z4,z5,z6]),(0,[z1,z174,z8,z4,z5,z6,z31]),(0,[z1,z267,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z73,z4,z74,z6])],[(0,[z1,z2,z36,z9,z4,z5,z6]),(0,[z1,z2,z82,z8,z4,z5,z6]),(0,[z1,z2,z52,z8,z4,z5,z75])]],
   [[(0,[z268,z1,z2,z8,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z31]),(0,[z1,z2,z8,z269,z4,z5,z6])],[(0,[z1,z2,z8,z270,z4,z5,z6]),(0,[z1,z81,z8,z4,z5,z18,z6]),(0,[z1,z2,z8,z21,z5,z6,z85])],[(0,[z1,z2,z271,z36,z4,z5,z6]),(0,[z27,z1,z2,z8,z4,z6,z28]),(0,[z1,z2,z8,z4,z5,z6,z203])],[(0,[z30,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z272,z36,z4,z5,z6]),(0,[z1,z81,z2,z8,z4,z5,z18]),(0,[z273,z1,z2,z8,z4,z5,z6]),(1,[z1,z8,z274,z4,z5,z6])],[(0,[z15,z121,z2,z8,z4,z5,z6]),(0,[z275,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z276,z5,z6]),(0,[z277,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z24,z6,z31]),(0,[z278,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z279,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z212,z85]),(0,[z27,z280,z2,z8,z4,z5,z6])],[(0,[z1,z2,z71,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z281,z6]),(0,[z1,z2,z8,z4,z282,z5,z6]),(0,[z283,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z284,z6]),(0,[z49,z1,z2,z76,z4,z5,z6]),(0,[z88,z1,z2,z8,z4,z285,z6]),(0,[z286,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z144,z3,z4,z5,z6]),(0,[z30,z1,z2,z83,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z287])],[(0,[z288,z1,z2,z8,z4,z5,z6]),(0,[z1,z174,z2,z117,z4,z5,z6]),(0,[z1,z2,z8,z289,z4,z5,z6]),(0,[z1,z2,z290,z8,z4,z5,z6]),(0,[z1,z291,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z5,z158])],[(0,[z15,z1,z8,z3,z4,z5,z6]),(0,[z0,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z44,z6]),(0,[z1,z2,z8,z4,z5,z292,z6]),(0,[z30,z1,z8,z4,z5,z6,z31]),(0,[z1,z2,z8,z4,z5,z293,z6]),(0,[z1,z2,z8,z4,z294,z5,z6])],[(0,[z2,z36,z8,z173,z4,z5,z6]),(0,[z1,z135,z2,z8,z105,z5,z6]),(0,[z1,z2,z8,z4,z295,z5,z6])],[(0,[z1,z2,z8,z4,z296,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z72,z4,z5,z6]),(0,[z298,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z20,z4,z5,z75,z6]),(0,[z1,z299,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z300,z4,z5,z6]),(0,[z22,z1,z2,z36,z4,z5,z6]),(0,[z301,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z302,z8,z4,z5,z6])],[(0,[z1,z2,z8,z303,z4,z5,z6])],[(0,[z1,z2,z8,z4,z304,z5,z6]),(0,[z1,z2,z36,z4,z5,z61,z6]),(0,[z1,z145,z2,z8,z4,z5,z6])],[(0,[z305,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z306,z5,z6]),(0,[z1,z2,z52,z4,z5,z44,z6])],[(0,[z7,z1,z2,z8,z4,z56,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z65,z5,z6]),(0,[z1,z81,z2,z307,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z6,z308]),(0,[z1,z2,z71,z58,z4,z5,z6]),(0,[z22,z2,z71,z8,z4,z5,z6]),(0,[z1,z2,z8,z309,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z219,z85])],[(0,[z310,z1,z2,z8,z4,z5,z6]),(0,[z1,z135,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z11,z6]),(0,[z202,z1,z2,z8,z4,z5,z6])],[(0,[z15,z22,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z311,z1,z2,z8,z4,z5,z6])],[(0,[z312,z1,z2,z8,z4,z5,z6]),(0,[z110,z2,z8,z4,z5,z42,z6]),(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z313,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z100,z6]),(0,[z1,z2,z8,z4,z5,z6,z314]),(0,[z315,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z316])],[(0,[z1,z2,z52,z8,z4,z5,z6])],[(1,[z49,z2,z76,z4,z5,z6]),(0,[z187,z1,z2,z76,z4,z5,z6]),(0,[z22,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z317,z4,z5,z6]),(0,[z1,z2,z144,z4,z5,z6,z53])],[(0,[z88,z1,z2,z8,z4,z5,z100]),(0,[z1,z2,z8,z4,z318,z5,z6]),(0,[z1,z144,z8,z274,z4,z5,z6])],[(0,[z14,z7,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z319,z5,z6]),(0,[z320,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z20,z144,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z321]),(0,[z1,z2,z8,z322,z4,z5,z6]),(1,[z1,z323,z8,z4,z5,z6])],[(0,[z1,z2,z20,z3,z4,z5,z6]),(0,[z104,z1,z8,z4,z5,z24,z6])],[(0,[z1,z2,z324,z8,z4,z5,z6])],[(1,[z2,z76,z4,z5,z42,z6]),(1,[z1,z325,z8,z4,z5,z6])],[(0,[z1,z2,z8,z73,z4,z24,z6])],[(0,[z326,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z327]),(0,[z1,z2,z8,z4,z5,z6,z328]),(0,[z1,z2,z8,z19,z5,z61,z6]),(0,[z1,z2,z329,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z255,z5,z6]),(0,[z1,z2,z8,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z330]),(0,[z1,z331,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z332,z5,z6]),(1,[z1,z2,z333,z4,z5,z6]),(0,[z47,z2,z8,z4,z5,z100,z6])]],
   [[(0,[z1,z8,z72,z4,z105,z5,z6]),(0,[z1,z2,z8,z4,z5,z334,z6]),(0,[z1,z2,z8,z4,z5,z6,z335])],[(0,[z22,z1,z2,z103,z4,z5,z6]),(0,[z336,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z6]),(1,[z1,z2,z133,z4,z5,z6])],[(0,[z1,z2,z337,z8,z4,z5,z6]),(0,[z14,z1,z2,z338,z4,z5,z6]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z72,z4,z5,z6]),(0,[z1,z2,z155,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z339,z6]),(0,[z1,z2,z8,z4,z5,z6,z84])],[(0,[z1,z2,z340,z8,z4,z5,z6]),(0,[z341,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z63,z4,z74,z6]),(0,[z1,z2,z8,z4,z243,z5,z6])],[(0,[z1,z2,z342,z8,z4,z5,z6]),(0,[z1,z37,z2,z8,z4,z5,z6])],[(0,[z1,z71,z8,z4,z5,z6,z31]),(0,[z32,z2,z8,z12,z4,z5,z6]),(0,[z1,z2,z8,z157,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z6,z31]),(0,[z1,z2,z8,z4,z198,z5,z6])],[(1,[z343,z2,z8,z4,z5,z6]),(0,[z343,z1,z2,z8,z4,z5,z6])],[(0,[z50,z1,z2,z36,z4,z5,z6]),(0,[z30,z259,z2,z8,z4,z5,z6]),(0,[z30,z1,z2,z8,z260,z5,z6])],[(1,[z2,z76,z9,z4,z5,z6]),(0,[z344,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z172,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z345])],[(0,[z50,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z58,z59,z4,z5,z6]),(1,[z1,z2,z346,z4,z5,z6]),(0,[z347,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z144,z222,z5,z6])],[(0,[z1,z2,z8,z348,z4,z5,z6]),(0,[z1,z2,z8,z87,z4,z5,z6])],[(0,[z349,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z350]),(0,[z351,z1,z2,z8,z4,z5,z6]),(0,[z27,z1,z2,z8,z4,z5,z28])],[(0,[z1,z2,z8,z4,z5,z352,z6]),(0,[z353,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z76,z354,z4,z5,z6]),(0,[z33,z1,z2,z36,z4,z5,z6]),(0,[z355,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z356]),(1,[z88,z2,z8,z4,z5,z102]),(0,[z1,z2,z222,z4,z5,z44,z6])]],
   [[(0,[z1,z2,z76,z4,z5,z357,z6]),(0,[z1,z2,z58,z9,z4,z5,z6]),(0,[z14,z1,z2,z8,z38,z5,z6]),(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z358,z73,z4,z5,z6])],[(0,[z1,z81,z8,z3,z4,z5,z6]),(0,[z1,z174,z2,z36,z4,z5,z6]),(0,[z250,z1,z2,z8,z4,z5,z6])],[(0,[z15,z1,z122,z8,z4,z5,z6]),(0,[z1,z2,z8,z359,z4,z5,z6]),(0,[z110,z1,z2,z360,z4,z5,z6]),(0,[z33,z1,z2,z8,z4,z5,z85])],[(0,[z50,z1,z2,z58,z4,z5,z6]),(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z6,z151]),(0,[z1,z2,z8,z361,z4,z5,z6]),(0,[z25,z2,z144,z8,z4,z5,z6])],[(0,[z1,z2,z71,z256,z4,z5,z6]),(0,[z1,z2,z8,z72,z5,z6,z85]),(0,[z1,z2,z8,z4,z5,z6,z362]),(0,[z1,z2,z8,z4,z5,z6,z363])],[(0,[z364,z1,z2,z8,z4,z5,z6])],[(0,[z10,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z105,z5,z6,z85])],[(0,[z1,z2,z36,z4,z74,z5,z6]),(0,[z365,z1,z2,z8,z4,z5,z6])],[(0,[z14,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z366]),(0,[z1,z2,z8,z73,z12,z4,z6])],[(0,[z33,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z58,z4,z5,z44,z6]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z149,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z24,z6])],[(0,[z15,z49,z1,z8,z4,z5,z6])],[(0,[z1,z2,z8,z368,z4,z5,z6]),(0,[z1,z2,z8,z369,z4,z5,z6]),(0,[z1,z2,z36,z4,z161,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z370]),(0,[z1,z2,z8,z5,z61,z6,z85]),(0,[z1,z2,z8,z73,z5,z6,z85]),(0,[z1,z2,z8,z4,z5,z6,z371])],[(0,[z1,z2,z8,z354,z4,z5,z6]),(0,[z1,z2,z58,z144,z4,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z318,z5,z6]),(0,[z1,z2,z372,z8,z4,z5,z6]),(0,[z10,z1,z2,z4,z5,z6,z53])],[(0,[z1,z2,z58,z4,z5,z61,z6])],[(0,[z1,z2,z76,z12,z4,z5,z6]),(0,[z1,z2,z76,z4,z5,z158,z6]),(0,[z1,z2,z8,z4,z5,z357,z6]),(0,[z14,z2,z8,z4,z5,z100,z6]),(0,[z1,z2,z36,z4,z5,z168,z6]),(0,[z1,z2,z8,z4,z5,z373,z6]),(1,[z209,z1,z8,z4,z24,z6])]],
   [[(0,[z156,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z58,z4,z65,z5,z6]),(0,[z1,z2,z8,z4,z5,z109,z6]),(1,[z1,z81,z3,z4,z5,z6])],[(0,[z374,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z375])],[(0,[z1,z2,z8,z173,z4,z5,z6]),(1,[z1,z2,z376,z4,z5,z6]),(0,[z1,z2,z8,z222,z4,z5,z6]),(0,[z1,z2,z34,z8,z4,z5,z6])],[(0,[z1,z2,z8,z377,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z378,z6])],[(0,[z1,z2,z8,z4,z5,z379,z6]),(1,[z1,z2,z8,z4,z177,z6]),(0,[z1,z2,z4,z21,z74,z5,z6])],[(0,[z1,z2,z8,z4,z42,z24,z6]),(0,[z1,z2,z8,z175,z5,z61,z6])],[(0,[z1,z2,z8,z4,z5,z6,z380]),(0,[z1,z2,z8,z4,z5,z381,z6])],[(0,[z1,z2,z8,z382,z4,z5,z6]),(1,[z1,z174,z8,z4,z65,z6])],[(1,[z1,z383,z8,z4,z5,z6]),(0,[z1,z2,z8,z384,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z385]),(1,[z1,z2,z26,z4,z5,z6])],[(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z23,z5,z6]),(0,[z1,z2,z8,z175,z4,z158,z6]),(0,[z1,z2,z8,z386,z4,z5,z6])],[(1,[z1,z122,z36,z4,z5,z6]),(0,[z1,z2,z8,z222,z19,z5,z6]),(0,[z10,z1,z2,z52,z4,z5,z6])],[(0,[z1,z2,z58,z4,z5,z95,z6]),(0,[z14,z22,z2,z8,z4,z5,z6]),(0,[z387,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z388,z6]),(0,[z1,z2,z63,z8,z4,z74,z6]),(0,[z1,z2,z4,z5,z75,z6,z53])],[(0,[z1,z2,z76,z4,z5,z6,z389]),(0,[z47,z1,z2,z390,z4,z5,z6]),(0,[z1,z2,z8,z4,z391,z5,z6]),(0,[z1,z2,z8,z392,z4,z5,z6])],[(0,[z1,z122,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z12,z4,z5,z6]),(1,[z1,z2,z8,z73,z12,z6])],[(0,[z47,z2,z8,z76,z4,z5,z6]),(0,[z1,z2,z393,z8,z4,z5,z6]),(0,[z1,z2,z8,z19,z5,z168,z6])]],
   [[(0,[z1,z2,z58,z4,z106,z5,z6]),(0,[z22,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z394,z6]),(0,[z10,z1,z2,z8,z242,z5,z6])],[],[(0,[z1,z2,z8,z4,z395,z5,z6]),(0,[z88,z1,z2,z8,z111,z5,z6]),(0,[z1,z2,z36,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z396])],[(1,[z397,z1,z8,z4,z5,z6]),(0,[z88,z1,z2,z8,z4,z116,z6]),(0,[z1,z2,z8,z390,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z398])],[(1,[z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z399,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z400,z6]),(0,[z0,z1,z2,z76,z4,z5,z6]),(0,[z401,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z42,z6]),(0,[z1,z402,z2,z8,z4,z5,z6]),(0,[z47,z1,z2,z8,z4,z5,z100]),(0,[z27,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z403,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z404,z6]),(0,[z1,z405,z2,z8,z4,z5,z6])],[(0,[z1,z2,z399,z76,z4,z5,z6]),(1,[z14,z2,z8,z38,z5,z6]),(0,[z406,z1,z2,z8,z4,z5,z6])],[(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z104,z1,z8,z4,z105,z5,z6]),(0,[z1,z2,z8,z407,z4,z5,z6]),(0,[z1,z2,z20,z4,z5,z44,z6])],[(0,[z1,z174,z71,z8,z4,z5,z6]),(0,[z1,z2,z358,z8,z4,z5,z6])],[(0,[z121,z2,z71,z8,z4,z5,z6]),(0,[z1,z2,z76,z4,z5,z6,z28]),(0,[z1,z2,z408,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z409,z6])],[(0,[z2,z58,z8,z76,z4,z5,z6]),(0,[z1,z2,z8,z410,z4,z5,z6]),(0,[z1,z2,z411,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z70,z6]),(0,[z1,z2,z8,z4,z5,z412,z6])],[(0,[z1,z2,z8,z4,z413,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z389]),(0,[z1,z2,z8,z4,z65,z23,z6])],[(0,[z7,z1,z2,z36,z4,z5,z6]),(0,[z30,z104,z1,z8,z4,z5,z6])],[(1,[z14,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z4,z13,z5,z6]),(0,[z414,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z97,z6]),(0,[z1,z2,z8,z274,z4,z5,z6]),(0,[z1,z2,z20,z8,z4,z5,z6])],[(0,[z121,z1,z2,z58,z4,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z105,z5,z6])]],
   [[(0,[z1,z2,z76,z4,z21,z5,z6]),(0,[z1,z2,z256,z58,z4,z5,z6]),(0,[z27,z1,z2,z58,z4,z5,z6]),(0,[z88,z1,z2,z139,z4,z5,z6]),(0,[z415,z1,z2,z8,z4,z5,z6]),(0,[z416,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z36,z215,z4,z5,z6]),(0,[z205,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z417,z8,z4,z5,z6])],[(0,[z1,z2,z52,z76,z4,z5,z6]),(0,[z418,z1,z2,z8,z4,z5,z6]),(0,[z419,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z63,z4,z74,z5,z6])],[(0,[z1,z2,z8,z420,z4,z5,z6])],[(0,[z2,z8,z9,z4,z5,z100,z6])],[(0,[z1,z2,z8,z4,z5,z421,z6]),(0,[z1,z2,z199,z76,z4,z5,z6]),(0,[z14,z1,z2,z8,z9,z5,z6]),(0,[z1,z2,z57,z4,z5,z6,z28])],[],[(0,[z1,z2,z126,z8,z4,z5,z6]),(0,[z422,z1,z2,z8,z4,z5,z6]),(0,[z423,z1,z2,z8,z4,z5,z6])],[(0,[z49,z1,z8,z72,z4,z5,z6]),(0,[z7,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z58,z4,z74,z5,z6]),(0,[z1,z2,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z424,z6])],[(0,[z1,z425,z2,z8,z4,z5,z6])],[(0,[z326,z1,z2,z76,z4,z5,z6]),(0,[z1,z81,z2,z76,z4,z5,z6]),(0,[z1,z2,z58,z4,z5,z24,z6]),(0,[z1,z2,z2,z3,z4,z5,z6])],[(0,[z22,z1,z2,z346,z4,z5,z6])],[(0,[z426,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z76,z427,z4,z5,z6]),(2,[z2,z173,z4,z5,z6]),(0,[z1,z2,z8,z73,z4,z65,z6])],[(0,[z90,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z428]),(0,[z1,z8,z3,z72,z4,z5,z6]),(0,[z1,z2,z36,z73,z4,z5,z6]),(0,[z10,z1,z2,z8,z4,z5,z53]),(0,[z1,z2,z8,z4,z13,z5,z6])],[(0,[z10,z1,z2,z36,z4,z5,z6]),(0,[z27,z1,z2,z8,z73,z4,z6]),(0,[z1,z2,z8,z4,z5,z429,z6])],[(0,[z14,z2,z8,z76,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z100,z6]),(0,[z1,z2,z8,z4,z5,z430,z6]),(0,[z1,z2,z8,z4,z5,z431,z6])]],
   [[(0,[z1,z2,z214,z8,z4,z5,z6]),(0,[z1,z2,z58,z4,z5,z168,z6]),(0,[z1,z2,z3,z4,z23,z5,z6]),(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z30,z1,z2,z376,z4,z5,z6]),(0,[z1,z2,z20,z8,z4,z74,z6])],[(0,[z1,z2,z8,z4,z5,z432,z6]),(0,[z1,z2,z8,z4,z13,z61,z6])],[(0,[z433,z1,z2,z8,z4,z5,z6])],[(0,[z121,z1,z2,z130,z4,z5,z6]),(0,[z110,z1,z434,z8,z4,z5,z6]),(0,[z1,z2,z144,z4,z74,z5,z6])],[(1,[z1,z17,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z435,z5,z6]),(0,[z1,z2,z201,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z436,z6]),(0,[z1,z2,z437,z8,z4,z5,z6])],[(0,[z1,z2,z325,z8,z4,z5,z6]),(0,[z1,z438,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z439,z6])],[(0,[z1,z2,z8,z73,z4,z23,z6]),(0,[z1,z440,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z4,z105,z5,z6]),(1,[z1,z2,z8,z4,z294,z6]),(0,[z1,z323,z2,z8,z4,z5,z6])],[(1,[z1,z2,z214,z4,z5,z6]),(1,[z1,z402,z8,z4,z5,z6]),(1,[z136,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z31])],[(0,[z27,z1,z2,z8,z4,z5,z158])],[(0,[z121,z1,z2,z138,z4,z5,z6]),(0,[z441,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z23,z24,z6]),(0,[z27,z1,z2,z8,z243,z5,z6])],[(0,[z1,z2,z244,z8,z4,z5,z6]),(0,[z1,z442,z2,z8,z4,z5,z6])],[(1,[z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z63,z8,z4,z44,z6]),(0,[z443,z1,z2,z8,z4,z5,z6]),(0,[z1,z280,z2,z8,z4,z5,z6])],[(0,[z444,z1,z2,z8,z4,z5,z6]),(0,[z22,z1,z2,z8,z4,z42,z6]),(0,[z1,z2,z36,z4,z5,z373,z6]),(0,[z1,z2,z63,z8,z4,z5,z6])],[(0,[z445,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z446,z5,z6]),(0,[z367,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z447,z5,z6]),(0,[z1,z2,z8,z4,z65,z13,z6])],[(0,[z49,z1,z8,z4,z5,z24,z6])]],
   [[(0,[z49,z2,z8,z76,z4,z5,z6]),(0,[z448,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z449])],[(0,[z22,z2,z8,z4,z5,z6,z102]),(0,[z1,z2,z8,z127,z4,z5,z6]),(0,[z450,z1,z2,z8,z4,z5,z6])],[(0,[z397,z7,z1,z8,z4,z5,z6]),(0,[z30,z1,z2,z8,z4,z5,z6]),(1,[z1,z267,z8,z4,z5,z6])],[(1,[z1,z2,z101,z4,z5,z6]),(0,[z1,z2,z58,z8,z4,z5,z6]),(0,[z104,z1,z174,z8,z4,z5,z6]),(1,[z1,z2,z269,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z451])],[(0,[z452,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z24,z6]),(0,[z51,z1,z2,z4,z21,z5,z6]),(1,[z1,z40,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z453,z5,z6]),(0,[z1,z2,z73,z26,z4,z5,z6])],[(0,[z454,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z455,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z456,z5,z6])],[(1,[z121,z71,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z285,z6]),(0,[z457,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z458,z5,z6]),(0,[z1,z2,z8,z19,z105,z5,z6]),(1,[z1,z2,z57,z4,z5,z6])],[(0,[z50,z2,z8,z4,z5,z42,z6]),(0,[z88,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z4,z5,z6]),(0,[z2,z8,z4,z5,z42,z6,z102])],[(0,[z22,z47,z2,z8,z4,z5,z6]),(0,[z0,z1,z122,z8,z4,z5,z6]),(1,[z1,z2,z342,z4,z5,z6]),(1,[z1,z2,z307,z4,z5,z6])],[(0,[z110,z1,z2,z76,z4,z5,z6])],[(0,[z1,z135,z2,z8,z4,z177,z6]),(0,[z1,z2,z8,z12,z175,z4,z6]),(0,[z1,z2,z8,z4,z5,z459,z6])],[(0,[z460,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z360,z4,z5,z6]),(0,[z1,z2,z271,z8,z4,z5,z6]),(1,[z365,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z461,z4,z5,z6])],[(0,[z1,z2,z144,z8,z4,z5,z6])],[(0,[z1,z2,z71,z8,z4,z5,z6]),(0,[z462,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z303,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z463,z4,z5,z6]),(0,[z1,z2,z8,z464,z4,z5,z6])],[(0,[z465,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z466]),(0,[z104,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z467,z6]),(0,[z1,z2,z8,z4,z5,z158,z6])],[(0,[z297,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z468]),(0,[z1,z225,z8,z12,z4,z5,z6]),(0,[z1,z2,z8,z19,z4,z5,z85])],[],[(1,[z47,z2,z76,z4,z5,z6]),(0,[z1,z1,z2,z58,z4,z5,z6]),(0,[z22,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z430,z6])],[(0,[z1,z2,z58,z72,z4,z5,z6]),(0,[z1,z2,z8,z4,z469,z5,z6])],[(0,[z121,z1,z2,z36,z4,z5,z6])],[(0,[z1,z2,z256,z36,z4,z5,z6])],[(0,[z121,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z8,z248,z4,z5,z6])],[(0,[z1,z122,z2,z76,z4,z5,z6]),(0,[z470,z1,z2,z8,z4,z5,z6]),(0,[z1,z135,z2,z8,z4,z5,z6])],[(0,[z104,z1,z2,z216,z4,z5,z6]),(0,[z1,z2,z8,z4,z471,z5,z6])],[(0,[z1,z472,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z473,z4,z5,z6])],[(0,[z50,z2,z8,z4,z5,z6,z102]),(0,[z1,z2,z58,z73,z4,z5,z6]),(0,[z110,z22,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z31]),(0,[z229,z2,z36,z8,z4,z5,z6]),(0,[z474,z1,z2,z8,z4,z5,z6]),(1,[z2,z8,z475,z4,z5,z6])],[(0,[z1,z2,z36,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z476,z6]),(0,[z1,z2,z139,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z58,z4,z5,z100,z6]),(0,[z1,z81,z8,z4,z5,z24,z6]),(0,[z1,z2,z8,z4,z477,z5,z6]),(0,[z1,z2,z20,z8,z4,z44,z6]),(0,[z1,z2,z8,z4,z5,z478,z6])],[(0,[z1,z2,z101,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z479,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z480,z6]),(0,[z1,z2,z8,z4,z5,z6,z481]),(0,[z482,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z383,z8,z4,z5,z6]),(0,[z1,z483,z2,z8,z4,z5,z6]),(0,[z1,z2,z118,z8,z4,z5,z6]),(0,[z27,z1,z323,z8,z4,z5,z6])],[(0,[z90,z2,z8,z76,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z92,z85]),(0,[z1,z2,z484,z8,z4,z5,z6])],[(0,[z15,z1,z2,z55,z4,z5,z6])],[(0,[z485,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z486,z6]),(0,[z50,z47,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z354,z4,z5,z6]),(1,[z487,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z74,z13,z6]),(1,[z1,z2,z4,z5,z6,z219])],[(0,[z1,z2,z8,z488,z4,z5,z6]),(1,[z1,z2,z8,z4,z6,z212])],[(0,[z1,z2,z58,z4,z105,z5,z6]),(0,[z489,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z490,z5,z6]),(0,[z491,z1,z2,z8,z4,z5,z6])],[(0,[z492,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z338,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z493,z6]),(0,[z494,z1,z2,z36,z4,z5,z6]),(0,[z209,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z144,z8,z222,z5,z6])],[(0,[z495,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z222,z4,z5,z6]),(0,[z30,z1,z2,z8,z4,z5,z18]),(0,[z1,z2,z8,z4,z5,z6,z28])],[(0,[z1,z2,z8,z4,z5,z496,z6])],[(0,[z497,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z220,z6])],[(0,[z1,z2,z8,z498,z4,z5,z6]),(1,[z1,z81,z8,z4,z5,z18])],[(1,[z1,z2,z8,z127,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z380]),(0,[z1,z2,z8,z4,z13,z44,z6])]],
   [[(0,[z499,z1,z2,z8,z4,z5,z6])],[(0,[z1,z81,z2,z8,z4,z5,z31])],[(0,[z50,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z21,z5,z6])],[(0,[z252,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z500,z5,z6]),(0,[z1,z2,z501,z8,z4,z5,z6]),(0,[z1,z2,z8,z502,z4,z5,z6]),(0,[z110,z1,z2,z384,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z503,z6]),(0,[z1,z2,z8,z4,z5,z6,z504]),(0,[z1,z2,z8,z4,z505,z5,z6])],[],[(1,[z1,z2,z207,z4,z5,z6]),(2,[z1,z59,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z6,z31])],[(0,[z1,z2,z3,z12,z4,z5,z6])],[(0,[z1,z2,z144,z8,z21,z5,z6]),(0,[z1,z20,z201,z8,z4,z5,z6]),(0,[z506,z1,z2,z8,z4,z5,z6]),(0,[z33,z1,z2,z8,z4,z5,z6])],[(0,[z185,z1,z2,z58,z4,z5,z6]),(1,[z1,z2,z8,z4,z507,z6])],[(0,[z508,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z509]),(0,[z1,z2,z8,z4,z5,z6,z510]),(0,[z511,z1,z2,z8,z4,z5,z6])],[(0,[z397,z1,z2,z8,z4,z5,z6]),(0,[z1,z174,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z512])],[(0,[z22,z2,z8,z9,z4,z5,z6])],[(0,[z1,z2,z58,z300,z4,z5,z6]),(0,[z513,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z514,z4,z5,z6])],[(0,[z121,z1,z71,z8,z4,z5,z6]),(0,[z1,z2,z76,z4,z38,z5,z6]),(0,[z1,z2,z8,z427,z4,z5,z6]),(0,[z515,z1,z2,z8,z4,z5,z6]),(0,[z33,z1,z2,z8,z4,z70,z6]),(0,[z1,z2,z8,z4,z516,z5,z6])],[(0,[z517,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z518,z5,z6]),(0,[z1,z2,z8,z4,z5,z519,z6]),(1,[z1,z2,z358,z4,z5,z6])]],
   [[(0,[z47,z2,z71,z8,z4,z5,z6]),(0,[z1,z17,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z520,z5,z6]),(0,[z88,z1,z2,z36,z4,z5,z6])],[(0,[z521,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z522,z6]),(0,[z104,z1,z2,z8,z105,z5,z6]),(0,[z1,z2,z523,z8,z4,z5,z6]),(0,[z33,z1,z2,z8,z19,z5,z6])],[(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z122,z81,z8,z4,z5,z6])],[(0,[z524,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z173,z4,z5,z6]),(0,[z1,z2,z36,z222,z4,z5,z6]),(1,[z1,z2,z264,z4,z5,z6]),(1,[z1,z2,z525,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z6,z53]),(0,[z88,z14,z2,z8,z4,z5,z6]),(0,[z1,z2,z279,z12,z4,z5,z6]),(1,[z1,z526,z8,z4,z5,z6])],[(0,[z1,z2,z8,z55,z4,z5,z6]),(0,[z1,z526,z2,z8,z4,z5,z6])],[(0,[z47,z1,z2,z58,z4,z5,z6]),(0,[z527,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z528])],[(0,[z1,z2,z76,z4,z5,z18,z6]),(0,[z1,z2,z76,z19,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z529]),(0,[z1,z530,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z531,z6]),(0,[z259,z1,z2,z8,z4,z5,z6])],[(0,[z110,z1,z2,z8,z4,z23,z6]),(0,[z1,z2,z83,z8,z4,z5,z6]),(0,[z1,z532,z2,z8,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z203])],[(0,[z1,z2,z76,z4,z5,z6,z85]),(0,[z104,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z533])],[(0,[z1,z2,z63,z76,z4,z5,z6]),(0,[z1,z135,z2,z269,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z534]),(0,[z1,z2,z36,z4,z23,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z535,z6]),(0,[z196,z1,z2,z8,z4,z5,z6]),(0,[z10,z343,z2,z8,z4,z5,z6])],[(0,[z1,z135,z81,z8,z4,z5,z6]),(0,[z536,z1,z2,z8,z4,z5,z6])],[(1,[z1,z434,z8,z4,z5,z6]),(0,[z33,z1,z2,z8,z4,z5,z168])],[(1,[z1,z2,z338,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z537,z6]),(0,[z1,z538,z2,z8,z4,z5,z6]),(0,[z88,z1,z325,z8,z4,z5,z6]),(0,[z539,z1,z2,z8,z4,z5,z6])],[(1,[z15,z49,z8,z4,z5,z6]),(1,[z229,z2,z36,z4,z5,z6]),(0,[z1,z2,z36,z12,z4,z5,z6]),(1,[z195,z2,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z58,z76,z4,z5,z6]),(0,[z1,z2,z272,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z540]),(0,[z1,z2,z8,z4,z5,z6,z541]),(0,[z542,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z284,z6]),(0,[z88,z1,z2,z333,z4,z5,z6])],[(0,[z7,z2,z8,z4,z5,z6,z102]),(0,[z1,z2,z8,z4,z543,z5,z6])],[(0,[z401,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z544,z5,z6]),(0,[z1,z2,z545,z3,z4,z5,z6]),(0,[z1,z546,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z96,z5,z6])],[(0,[z1,z2,z8,z4,z5,z547,z6]),(0,[z1,z2,z8,z222,z5,z6,z85]),(0,[z1,z8,z12,z548,z4,z5,z6])],[(0,[z1,z2,z3,z4,z13,z5,z6]),(0,[z209,z1,z2,z264,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z549,z6]),(0,[z1,z2,z8,z550,z4,z5,z6])],[(0,[z1,z2,z360,z8,z4,z5,z6]),(0,[z1,z2,z551,z8,z4,z5,z6]),(1,[z552,z1,z8,z4,z5,z6])],[(0,[z1,z2,z3,z4,z21,z5,z6]),(1,[z2,z8,z4,z5,z6,z92]),(1,[z1,z2,z403,z4,z5,z6])],[(0,[z50,z2,z8,z9,z4,z5,z6]),(0,[z1,z2,z553,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z74,z6,z28])],[(0,[z554,z1,z2,z58,z4,z5,z6]),(1,[z1,z8,z59,z4,z5,z6]),(0,[z555,z1,z2,z8,z4,z5,z6]),(0,[z209,z1,z2,z8,z4,z24,z6]),(0,[z1,z2,z8,z117,z4,z5,z6]),(0,[z1,z2,z8,z556,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z42,z6]),(0,[z1,z2,z144,z76,z4,z5,z6]),(0,[z1,z2,z8,z557,z4,z5,z6]),(0,[z7,z1,z383,z8,z4,z5,z6]),(0,[z7,z47,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z116,z5,z6]),(0,[z33,z1,z2,z8,z4,z294,z6])],[],[(0,[z1,z2,z8,z38,z5,z6,z85]),(0,[z10,z1,z2,z4,z74,z5,z6]),(1,[z1,z2,z8,z4,z11,z6])],[(0,[z1,z2,z558,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z559,z6]),(1,[z1,z2,z8,z4,z13,z158])],[(0,[z560,z1,z2,z8,z4,z5,z6]),(0,[z27,z1,z2,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z561,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z24,z6])],[(0,[z51,z1,z2,z58,z4,z5,z6])],[(0,[z2,z71,z8,z4,z5,z42,z6]),(0,[z1,z2,z8,z562,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z563,z6]),(0,[z10,z1,z2,z8,z4,z5,z75])],[(0,[z564,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z565])],[(0,[z1,z2,z8,z4,z566,z5,z6]),(1,[z1,z2,z76,z4,z5,z6])],[(0,[z1,z2,z132,z58,z4,z5,z6]),(1,[z1,z2,z8,z4,z567,z6])],[(0,[z1,z2,z8,z175,z4,z42,z6]),(0,[z1,z2,z8,z568,z4,z5,z6]),(1,[z1,z569,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z570]),(0,[z1,z2,z58,z4,z5,z247,z6]),(0,[z7,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z4,z490,z5,z6]),(0,[z1,z2,z144,z8,z4,z220,z6]),(0,[z571,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z44,z6,z28]),(1,[z2,z8,z233,z4,z5,z6])],[(0,[z1,z135,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z4,z5,z75,z6]),(0,[z1,z2,z8,z4,z5,z572,z6]),(0,[z1,z2,z8,z4,z573,z5,z6])],[(0,[z574,z1,z2,z8,z4,z5,z6]),(0,[z49,z1,z174,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z575,z6]),(0,[z1,z2,z8,z4,z576,z5,z6])],[],[(0,[z1,z174,z2,z8,z4,z24,z6]),(0,[z32,z1,z2,z8,z4,z5,z6])],[(0,[z419,z1,z2,z8,z4,z5,z6]),(0,[z49,z1,z2,z36,z4,z5,z6]),(0,[z88,z1,z2,z8,z4,z5,z102]),(0,[z1,z174,z81,z8,z4,z5,z6]),(0,[z1,z2,z8,z577,z4,z5,z6])],[],[(0,[z1,z2,z20,z76,z4,z5,z6]),(0,[z1,z2,z36,z4,z13,z5,z6]),(0,[z578,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z63,z222,z4,z5,z6])],[(0,[z15,z1,z2,z58,z4,z5,z6]),(0,[z1,z2,z76,z175,z4,z5,z6]),(0,[z2,z20,z118,z8,z4,z5,z6]),(1,[z1,z8,z548,z4,z5,z6])]],
   [[(0,[z104,z1,z71,z8,z4,z5,z6]),(0,[z1,z174,z2,z342,z4,z5,z6]),(0,[z579,z1,z2,z8,z4,z5,z6])],[(0,[z49,z2,z71,z8,z4,z5,z6]),(0,[z1,z2,z76,z4,z5,z6,z102]),(0,[z185,z1,z2,z36,z4,z5,z6]),(1,[z1,z2,z87,z4,z5,z6])],[(0,[z1,z2,z2,z8,z4,z5,z6]),(0,[z121,z50,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z580,z6]),(0,[z1,z581,z2,z8,z4,z5,z6])],[(1,[z1,z17,z8,z4,z5,z6]),(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z582]),(0,[z1,z2,z8,z583,z4,z5,z6]),(0,[z33,z1,z2,z303,z4,z5,z6])],[(1,[z121,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z584,z4,z5,z6]),(0,[z1,z2,z58,z222,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z585,z6]),(0,[z1,z2,z8,z4,z65,z6,z28])],[(0,[z1,z2,z586,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z587,z6]),(0,[z1,z2,z8,z73,z4,z158,z6])],[(0,[z30,z1,z81,z8,z4,z5,z6]),(0,[z1,z2,z52,z4,z21,z5,z6])],[(0,[z49,z1,z2,z58,z4,z5,z6]),(0,[z209,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z588,z5,z6])],[(0,[z2,z71,z8,z4,z5,z6,z102]),(0,[z1,z2,z8,z4,z589,z5,z6]),(0,[z10,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z590,z4,z5,z6]),(1,[z1,z2,z155,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z158,z6])],[(0,[z1,z2,z8,z591,z4,z5,z6]),(0,[z88,z47,z2,z8,z4,z5,z6])],[(0,[z49,z1,z8,z4,z5,z6,z31]),(0,[z1,z2,z58,z4,z23,z5,z6]),(0,[z592,z1,z2,z8,z4,z5,z6]),(0,[z209,z487,z2,z8,z4,z5,z6]),(0,[z25,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z593])],[(1,[z15,z1,z3,z4,z5,z6]),(1,[z90,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z594])],[(0,[z47,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z595,z5,z6]),(0,[z1,z2,z8,z4,z5,z596,z6]),(0,[z1,z2,z8,z597,z4,z5,z6])],[(0,[z598,z1,z2,z8,z4,z5,z6]),(0,[z50,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z599,z4,z5,z6]),(0,[z1,z2,z525,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z58,z12,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z368,z4,z5,z6]),(0,[z1,z2,z501,z76,z4,z5,z6]),(0,[z1,z8,z3,z4,z5,z6,z31]),(0,[z600,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z601]),(1,[z1,z2,z8,z129,z5,z6]),(0,[z602,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z603,z4,z5,z6])],[(1,[z1,z2,z354,z4,z5,z6])],[(0,[z1,z2,z8,z604,z4,z5,z6])],[(0,[z33,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z605]),(1,[z1,z2,z279,z4,z5,z6])],[(0,[z186,z1,z2,z58,z4,z5,z6]),(0,[z2,z8,z4,z5,z100,z6,z102]),(1,[z10,z1,z2,z4,z5,z53])],[(1,[z1,z128,z8,z4,z5,z6])],[(0,[z1,z174,z2,z76,z4,z5,z6]),(0,[z1,z36,z8,z3,z4,z5,z6]),(1,[z1,z2,z173,z4,z5,z6])],[],[(0,[z441,z1,z2,z76,z4,z5,z6]),(1,[z145,z2,z8,z4,z5,z6])],[(0,[z1,z2,z606,z8,z4,z5,z6]),(0,[z1,z607,z2,z8,z4,z5,z6]),(1,[z1,z135,z8,z72,z5,z6])],[(1,[z1,z2,z8,z4,z109,z6]),(0,[z1,z2,z8,z4,z5,z608,z6]),(0,[z1,z2,z8,z4,z5,z609,z6]),(0,[z1,z2,z610,z8,z4,z5,z6])],[(0,[z611,z1,z2,z8,z4,z5,z6])],[(0,[z7,z2,z8,z9,z4,z5,z6]),(1,[z1,z2,z384,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z572,z6])],[]],
   [[(0,[z1,z2,z8,z4,z38,z5,z6])],[],[(0,[z30,z1,z2,z76,z4,z5,z6]),(0,[z1,z174,z8,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z158,z6])],[(0,[z1,z17,z58,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z612,z5,z6]),(0,[z1,z2,z8,z4,z5,z613,z6]),(0,[z1,z2,z8,z4,z5,z6,z614]),(0,[z30,z1,z2,z8,z4,z567,z6])],[(0,[z1,z2,z3,z4,z5,z6,z28]),(0,[z1,z122,z8,z4,z5,z24,z6]),(0,[z46,z1,z2,z4,z5,z6,z85]),(0,[z1,z2,z8,z4,z5,z615,z6])],[(1,[z47,z2,z8,z4,z5,z100]),(0,[z1,z2,z112,z36,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z53])],[(0,[z27,z365,z2,z8,z4,z5,z6])],[(0,[z2,z8,z4,z38,z5,z6,z102]),(0,[z1,z2,z8,z4,z616,z5,z6]),(0,[z1,z2,z307,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z617,z5,z6]),(0,[z1,z2,z8,z4,z5,z618,z6])],[(1,[z1,z2,z390,z4,z5,z6]),(0,[z51,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z18,z6]),(0,[z1,z2,z8,z19,z4,z5,z6])],[(0,[z1,z2,z8,z216,z4,z5,z6]),(1,[z196,z2,z8,z4,z5,z6]),(0,[z10,z1,z2,z8,z4,z507,z6])],[(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z85])],[(0,[z27,z1,z2,z8,z175,z4,z6])],[],[(0,[z14,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z619,z8,z4,z5,z6])],[(0,[z1,z2,z71,z76,z4,z5,z6]),(0,[z1,z2,z3,z590,z4,z5,z6]),(0,[z2,z144,z8,z475,z4,z5,z6])]],
   [[(0,[z49,z121,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z620,z4,z5,z6]),(1,[z217,z2,z8,z4,z5,z6]),(1,[z1,z2,z34,z4,z5,z6]),(0,[z1,z2,z8,z4,z621,z5,z6])],[(0,[z121,z1,z2,z8,z4,z5,z6]),(0,[z1,z81,z8,z4,z105,z5,z6])],[(0,[z1,z2,z256,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z622,z6]),(0,[z1,z2,z623,z8,z4,z5,z6]),(0,[z1,z40,z144,z8,z4,z5,z6])],[(0,[z14,z2,z71,z8,z4,z5,z6]),(0,[z1,z2,z249,z3,z4,z5,z6])],[],[(0,[z22,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z624,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z625])],[(0,[z15,z49,z2,z8,z4,z5,z6])],[(0,[z626,z1,z2,z8,z4,z5,z6]),(0,[z15,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z627,z5,z6]),(0,[z1,z2,z8,z4,z61,z6,z28])],[(0,[z1,z2,z434,z8,z4,z5,z6]),(0,[z33,z1,z526,z8,z4,z5,z6])],[(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z14,z1,z2,z58,z4,z5,z6]),(0,[z628,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z138,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z629,z6]),(0,[z1,z2,z58,z4,z5,z6,z31]),(0,[z47,z1,z2,z8,z4,z5,z102]),(0,[z209,z1,z2,z8,z4,z65,z6]),(1,[z1,z2,z8,z4,z97,z6]),(0,[z1,z2,z8,z4,z5,z630,z6])],[(0,[z88,z1,z402,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z255,z6]),(0,[z1,z2,z76,z9,z4,z5,z6]),(0,[z27,z1,z2,z76,z4,z5,z6]),(0,[z14,z1,z2,z208,z4,z5,z6]),(1,[z1,z36,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z5,z6,z28])],[(0,[z1,z2,z8,z4,z5,z42,z6]),(0,[z1,z2,z8,z631,z4,z5,z6]),(0,[z1,z2,z8,z73,z175,z5,z6])],[(0,[z1,z2,z8,z4,z5,z632,z6]),(0,[z1,z2,z8,z4,z5,z6,z633]),(0,[z1,z2,z8,z19,z4,z5,z168]),(0,[z27,z1,z569,z8,z4,z5,z6])],[(0,[z634,z1,z2,z8,z4,z5,z6]),(0,[z1,z635,z2,z8,z4,z5,z6]),(0,[z104,z1,z135,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z76,z4,z5,z636,z6]),(0,[z1,z2,z76,z4,z16,z5,z6]),(0,[z1,z2,z498,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z637,z5,z6])],[(0,[z49,z1,z2,z3,z4,z5,z6]),(0,[z638,z1,z2,z8,z4,z5,z6])],[],[(0,[z2,z71,z8,z9,z4,z5,z6]),(0,[z1,z2,z8,z4,z65,z42,z6]),(0,[z1,z2,z36,z4,z21,z5,z6]),(0,[z1,z135,z2,z8,z72,z5,z6]),(0,[z209,z217,z2,z8,z4,z5,z6])],[(0,[z1,z2,z639,z8,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z44,z6]),(0,[z1,z2,z8,z4,z129,z5,z6]),(1,[z1,z94,z8,z4,z5,z6])],[(0,[z1,z2,z3,z4,z38,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z640]),(0,[z88,z2,z8,z4,z5,z6,z102]),(0,[z1,z67,z2,z8,z4,z5,z6]),(0,[z1,z641,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z642])],[(0,[z1,z2,z257,z58,z4,z5,z6]),(0,[z1,z225,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z42,z6,z28])],[(1,[z46,z1,z2,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z61,z6]),(0,[z1,z2,z103,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z23,z13,z6]),(0,[z1,z2,z8,z4,z5,z75,z6])],[(0,[z1,z174,z2,z8,z4,z65,z6])],[(0,[z1,z2,z643,z8,z4,z5,z6]),(0,[z1,z2,z76,z4,z65,z5,z6]),(0,[z1,z2,z8,z644,z4,z5,z6])],[(0,[z645,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z71,z354,z4,z5,z6]),(0,[z646,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z636,z6]),(1,[z1,z174,z3,z4,z5,z6]),(0,[z1,z2,z8,z647,z4,z5,z6]),(1,[z2,z8,z173,z4,z5,z6]),(1,[z51,z1,z2,z21,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z5,z648,z6]),(0,[z1,z122,z8,z72,z4,z5,z6]),(0,[z30,z195,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z649,z4,z5,z6]),(0,[z1,z2,z8,z175,z4,z44,z6])],[(0,[z47,z2,z8,z4,z38,z5,z6]),(0,[z650,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z85]),(0,[z1,z2,z8,z175,z4,z5,z6]),(0,[z1,z2,z569,z8,z4,z5,z6])],[(0,[z1,z2,z144,z222,z4,z5,z6]),(0,[z1,z2,z8,z651,z4,z5,z6]),(0,[z1,z652,z2,z8,z4,z5,z6])],[(0,[z1,z2,z58,z4,z5,z158,z6]),(0,[z1,z2,z8,z4,z5,z6,z102]),(0,[z1,z8,z72,z4,z5,z18,z6]),(0,[z1,z2,z8,z19,z21,z5,z6])],[(0,[z1,z171,z2,z8,z4,z5,z6]),(0,[z653,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z4,z74,z5,z75,z6])],[(1,[z22,z2,z76,z4,z5,z6]),(0,[z10,z1,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z654,z6]),(0,[z1,z2,z8,z175,z4,z61,z6])],[(0,[z2,z8,z76,z4,z5,z42,z6]),(0,[z0,z1,z2,z58,z4,z5,z6])],[(0,[z1,z2,z655,z8,z4,z5,z6]),(0,[z1,z2,z8,z260,z4,z5,z6])],[(0,[z1,z2,z8,z656,z4,z5,z6]),(0,[z657,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z3,z4,z5,z6])],[(0,[z88,z1,z2,z8,z4,z5,z6]),(0,[z1,z135,z8,z72,z4,z5,z6]),(0,[z1,z2,z8,z548,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z658]),(0,[z33,z1,z2,z8,z5,z6,z85])],[],[(0,[z1,z2,z8,z4,z659,z5,z6])],[(0,[z15,z1,z71,z8,z4,z5,z6]),(0,[z27,z1,z2,z525,z4,z5,z6])],[(0,[z1,z2,z368,z76,z4,z5,z6]),(0,[z51,z1,z2,z4,z5,z75,z6])]],
   [[(0,[z1,z81,z2,z36,z4,z5,z6]),(0,[z660,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z661,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z507,z5,z6])],[(0,[z662,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z63,z20,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z663])],[(0,[z664,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z12,z5,z61,z6])],[(0,[z90,z1,z2,z36,z4,z5,z6]),(1,[z1,z2,z8,z4,z285,z6]),(0,[z104,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z665,z5,z6]),(0,[z1,z2,z8,z175,z4,z74,z6]),(0,[z666,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z667,z5,z6]),(0,[z1,z2,z8,z242,z4,z5,z6])],[(0,[z1,z2,z8,z208,z4,z5,z6]),(0,[z1,z2,z8,z4,z567,z5,z6]),(0,[z552,z1,z2,z8,z4,z5,z6])],[(0,[z50,z22,z2,z8,z4,z5,z6])],[(0,[z1,z1,z2,z8,z4,z5,z6]),(0,[z1,z174,z8,z4,z65,z5,z6]),(0,[z1,z2,z8,z4,z5,z6,z668]),(0,[z1,z2,z8,z4,z5,z6,z669])],[],[(0,[z554,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z333,z4,z5,z6]),(1,[z229,z2,z8,z4,z5,z6]),(0,[z30,z1,z2,z8,z4,z5,z31])],[(0,[z1,z2,z222,z4,z21,z5,z6])],[(0,[z1,z81,z2,z58,z4,z5,z6]),(1,[z1,z2,z238,z4,z5,z6]),(1,[z1,z2,z8,z4,z388,z6]),(0,[z1,z2,z8,z133,z4,z5,z6]),(0,[z1,z2,z8,z670,z4,z5,z6])],[(0,[z121,z1,z2,z8,z4,z284,z6]),(0,[z22,z2,z8,z76,z4,z5,z6]),(0,[z2,z8,z76,z4,z5,z6,z102]),(0,[z1,z2,z545,z8,z4,z5,z6]),(0,[z229,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z671,z4,z5,z6])],[(0,[z1,z2,z58,z4,z5,z6,z28]),(0,[z1,z2,z8,z672,z4,z5,z6]),(0,[z1,z2,z8,z4,z673,z5,z6]),(0,[z487,z1,z2,z8,z4,z5,z6]),(0,[z51,z1,z2,z144,z4,z5,z6])],[(0,[z90,z1,z2,z58,z4,z5,z6]),(0,[z47,z2,z8,z4,z5,z42,z6]),(0,[z1,z2,z8,z475,z4,z5,z6])],[(0,[z1,z135,z2,z8,z4,z388,z6]),(0,[z674,z1,z2,z8,z4,z5,z6]),(0,[z27,z1,z2,z8,z96,z5,z6])]],
   [[(1,[z1,z2,z248,z4,z5,z6]),(0,[z1,z2,z232,z3,z4,z5,z6]),(0,[z51,z1,z2,z63,z4,z5,z6])],[(0,[z14,z2,z8,z4,z38,z5,z6]),(0,[z1,z2,z8,z4,z5,z675,z6]),(1,[z252,z2,z8,z4,z5,z6])],[(0,[z15,z47,z2,z8,z4,z5,z6]),(0,[z1,z2,z58,z4,z13,z5,z6]),(0,[z676,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z36,z52,z4,z5,z6]),(0,[z677,z1,z2,z8,z4,z5,z6])],[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z2,z8,z4,z23,z5,z42,z6]),(0,[z22,z1,z2,z8,z4,z23,z6]),(0,[z27,z1,z2,z403,z4,z5,z6])],[(0,[z1,z2,z76,z4,z74,z5,z6]),(0,[z1,z2,z58,z4,z21,z5,z6]),(0,[z1,z2,z8,z346,z4,z5,z6]),(0,[z678,z1,z2,z8,z4,z5,z6]),(1,[z37,z2,z8,z4,z5,z6])],[(0,[z1,z71,z8,z4,z5,z24,z6])],[(0,[z1,z2,z76,z4,z5,z24,z6]),(0,[z110,z1,z171,z8,z4,z5,z6]),(1,[z1,z2,z8,z79,z5,z6])],[(0,[z1,z2,z228,z58,z4,z5,z6]),(0,[z1,z2,z238,z8,z4,z5,z6]),(0,[z1,z2,z3,z175,z4,z5,z6]),(0,[z679,z1,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6,z680]),(1,[z1,z2,z167,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z102]),(0,[z10,z1,z2,z222,z4,z5,z6]),(0,[z681,z1,z2,z8,z4,z5,z6])],[(0,[z1,z174,z8,z72,z4,z5,z6]),(0,[z1,z267,z20,z8,z4,z5,z6]),(1,[z1,z2,z20,z4,z44,z6]),(0,[z1,z2,z8,z682,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z683,z6]),(0,[z1,z2,z8,z4,z5,z684,z6]),(0,[z1,z2,z8,z4,z5,z6,z685]),(0,[z1,z2,z8,z686,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z168,z6]),(0,[z1,z2,z58,z4,z5,z6,z509]),(1,[z1,z3,z72,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z687,z6]),(0,[z1,z135,z2,z167,z4,z5,z6])],[(0,[z1,z2,z8,z4,z23,z6,z28])],[(0,[z121,z1,z2,z76,z4,z5,z6]),(0,[z688,z1,z2,z8,z4,z5,z6])],[(0,[z7,z1,z2,z8,z38,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z130,z8,z4,z5,z6]),(0,[z110,z1,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z245,z6]),(0,[z209,z1,z8,z4,z5,z24,z6])],[(0,[z1,z2,z8,z4,z689,z5,z6]),(0,[z88,z2,z8,z9,z4,z5,z6]),(0,[z1,z2,z8,z249,z4,z5,z6]),(0,[z1,z2,z690,z8,z4,z5,z6]),(0,[z1,z2,z8,z175,z4,z24,z6])],[(0,[z1,z2,z58,z4,z520,z5,z6]),(0,[z691,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z692,z6]),(0,[z1,z2,z147,z8,z4,z5,z6]),(1,[z202,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z693,z4,z5,z6]),(0,[z694,z1,z2,z8,z4,z5,z6])],[(0,[z30,z1,z8,z72,z4,z5,z6]),(0,[z695,z1,z2,z8,z4,z5,z6]),(1,[z1,z2,z8,z4,z114,z6])],[(0,[z696,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z697,z6])],[(1,[z121,z1,z3,z4,z5,z6]),(0,[z1,z2,z8,z698,z4,z5,z6])],[(0,[z7,z1,z2,z76,z4,z5,z6]),(0,[z494,z1,z2,z8,z4,z5,z6])],[(0,[z121,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z8,z59,z4,z5,z6])],[(0,[z699,z1,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z700,z4,z5,z6]),(1,[z280,z2,z8,z4,z5,z6])],[(0,[z104,z1,z8,z4,z5,z18,z6])],[(0,[z185,z1,z2,z8,z4,z5,z6]),(0,[z110,z1,z2,z58,z4,z5,z6]),(0,[z1,z136,z2,z8,z4,z5,z6]),(0,[z701,z1,z2,z8,z4,z5,z6])],[(1,[z1,z2,z8,z4,z56,z6]),(0,[z1,z2,z8,z4,z5,z702,z6]),(0,[z1,z2,z8,z376,z4,z5,z6]),(0,[z51,z1,z2,z8,z222,z5,z6])],[(0,[z1,z2,z8,z4,z5,z703,z6]),(0,[z704,z1,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z65,z5,z24,z6]),(0,[z2,z8,z12,z233,z4,z5,z6])],[(0,[z1,z2,z8,z9,z4,z5,z6]),(0,[z0,z1,z2,z36,z4,z5,z6]),(1,[z250,z2,z8,z4,z5,z6]),(0,[z552,z1,z8,z4,z5,z6,z85])],[(0,[z1,z2,z3,z4,z5,z6,z53]),(0,[z1,z2,z8,z73,z12,z5,z6]),(0,[z1,z2,z8,z705,z4,z5,z6]),(0,[z1,z2,z8,z706,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z707,z4,z5,z6]),(0,[z2,z8,z708,z4,z5,z6]),(0,[z2,z76,z4,z5,z6,z140]),(0,[z2,z76,z141,z4,z5,z6]),(0,[z14,z2,z8,z612,z5,z6]),(0,[z1,z2,z709,z4,z5,z6]),(0,[z1,z2,z710,z4,z5,z6]),(0,[z1,z2,z206,z4,z44,z6]),(0,[z1,z711,z8,z4,z5,z6])],[(0,[z1,z76,z548,z4,z5,z6]),(0,[z2,z173,z4,z38,z5,z6]),(0,[z1,z2,z8,z712,z5,z6]),(0,[z713,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z714,z5,z6]),(0,[z30,z1,z8,z4,z97,z31]),(0,[z1,z128,z52,z4,z5,z6]),(0,[z1,z2,z8,z4,z70,z6])],[(0,[z121,z3,z354,z4,z5,z6]),(0,[z1,z71,z368,z4,z5,z6]),(0,[z2,z8,z475,z4,z5,z6]),(0,[z22,z2,z8,z4,z276,z6]),(0,[z1,z2,z8,z4,z6,z715]),(0,[z1,z2,z716,z4,z5,z6]),(0,[z1,z2,z8,z111,z285,z6])],[(0,[z1,z3,z4,z5,z6,z466]),(0,[z717,z1,z76,z4,z5,z6]),(0,[z50,z2,z338,z4,z5,z6]),(0,[z1,z718,z58,z4,z5,z6]),(0,[z1,z2,z719,z4,z5,z6]),(0,[z1,z2,z8,z4,z720,z6]),(0,[z721,z2,z342,z4,z5,z6]),(0,[z1,z20,z201,z4,z44,z6]),(0,[z1,z2,z8,z309,z61,z6])],[(0,[z17,z58,z76,z4,z5,z6]),(0,[z1,z325,z722,z4,z5,z6]),(0,[z1,z81,z8,z4,z5,z609]),(0,[z1,z8,z420,z72,z5,z6]),(0,[z1,z2,z723,z4,z5,z6]),(0,[z1,z376,z4,z5,z6,z31]),(0,[z1,z724,z8,z4,z5,z6]),(0,[z145,z2,z52,z4,z5,z6])],[(0,[z14,z2,z76,z4,z5,z6]),(0,[z217,z2,z58,z4,z5,z6]),(0,[z1,z8,z725,z4,z5,z6]),(0,[z149,z1,z2,z21,z5,z6]),(0,[z726,z2,z8,z4,z5,z6]),(0,[z10,z1,z2,z242,z5,z53]),(0,[z1,z2,z727,z4,z5,z6])],[(0,[z1,z2,z36,z4,z255,z6]),(0,[z15,z249,z3,z4,z5,z6]),(0,[z2,z8,z728,z4,z5,z6]),(0,[z1,z128,z8,z242,z5,z6]),(0,[z729,z2,z8,z4,z5,z6])],[(0,[z50,z2,z8,z4,z284,z6]),(0,[z2,z2,z173,z4,z5,z6]),(0,[z2,z173,z4,z5,z6,z53]),(0,[z730,z2,z8,z4,z5,z6]),(0,[z25,z2,z8,z4,z114,z6]),(0,[z1,z2,z731,z4,z5,z6])],[(0,[z1,z2,z732,z4,z5,z6]),(0,[z1,z3,z4,z469,z5,z6]),(0,[z1,z2,z4,z5,z6,z733]),(0,[z27,z280,z2,z8,z4,z28])],[(0,[z1,z734,z8,z4,z5,z6]),(0,[z401,z2,z173,z4,z5,z6]),(0,[z145,z2,z8,z242,z5,z6])],[(0,[z1,z59,z300,z4,z5,z6]),(0,[z196,z2,z103,z4,z5,z6]),(0,[z2,z173,z4,z5,z18,z6]),(0,[z2,z173,z19,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z219]),(0,[z1,z2,z8,z735,z5,z6]),(0,[z1,z2,z8,z19,z70,z6])],[(0,[z1,z59,z4,z5,z736,z6]),(0,[z205,z2,z173,z4,z5,z6]),(0,[z1,z2,z8,z19,z5,z150]),(0,[z1,z2,z8,z737,z5,z6]),(0,[z1,z2,z83,z79,z5,z6]),(0,[z1,z2,z8,z73,z227,z6]),(0,[z1,z2,z8,z4,z6,z212]),(0,[z27,z1,z2,z57,z4,z28])],[(0,[z1,z323,z76,z4,z5,z6]),(0,[z2,z173,z4,z5,z6,z85]),(0,[z1,z2,z8,z4,z738,z6])],[(0,[z1,z2,z739,z4,z5,z6]),(0,[z1,z740,z58,z4,z5,z6]),(0,[z7,z2,z8,z9,z56,z6]),(0,[z1,z545,z3,z4,z24,z6]),(0,[z1,z2,z160,z590,z5,z6]),(0,[z280,z2,z741,z4,z5,z6])],[(0,[z187,z2,z76,z9,z5,z6]),(0,[z1,z742,z8,z4,z5,z6]),(0,[z1,z2,z743,z4,z5,z6]),(0,[z1,z2,z744,z4,z5,z6]),(0,[z1,z434,z745,z4,z5,z6]),(0,[z1,z2,z746,z4,z5,z6]),(0,[z747,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z735,z61,z6]),(0,[z202,z2,z748,z4,z5,z6]),(0,[z2,z749,z4,z5,z6,z28])],[(0,[z229,z2,z130,z4,z5,z6]),(0,[z190,z71,z8,z4,z5,z6]),(0,[z1,z2,z750,z4,z5,z6]),(0,[z1,z325,z76,z4,z5,z6]),(0,[z1,z2,z58,z4,z97,z6]),(0,[z1,z2,z8,z751,z5,z6]),(0,[z1,z3,z4,z13,z24,z6]),(0,[z137,z1,z3,z4,z5,z6]),(0,[z752,z2,z8,z4,z5,z6]),(0,[z136,z2,z8,z4,z177,z6]),(0,[z1,z2,z753,z4,z5,z6])]],
   [[(0,[z15,z2,z8,z4,z284,z6]),(0,[z1,z17,z36,z4,z5,z6]),(0,[z1,z2,z139,z4,z285,z6]),(0,[z267,z118,z8,z4,z5,z6]),(0,[z552,z8,z4,z5,z6,z92]),(0,[z280,z2,z8,z4,z13,z6])],[(0,[z1,z2,z58,z4,z255,z6]),(0,[z121,z1,z354,z4,z5,z6]),(0,[z15,z8,z249,z4,z5,z6]),(0,[z1,z3,z4,z5,z563,z6]),(0,[z1,z2,z754,z4,z5,z6]),(0,[z2,z8,z755,z4,z5,z6]),(0,[z2,z8,z756,z4,z5,z6])],[(0,[z1,z2,z757,z4,z5,z6]),(0,[z1,z17,z3,z4,z5,z6]),(0,[z1,z2,z758,z4,z5,z6]),(0,[z1,z3,z4,z5,z478,z6]),(0,[z209,z1,z264,z4,z24,z6]),(0,[z1,z2,z8,z759,z5,z6]),(0,[z1,z2,z83,z4,z97,z6]),(0,[z2,z358,z760,z4,z5,z6])],[(0,[z15,z761,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z762,z6]),(0,[z1,z2,z232,z4,z172,z6]),(0,[z763,z2,z8,z4,z5,z6]),(0,[z552,z1,z8,z157,z4,z6])],[(0,[z71,z8,z4,z5,z284,z6]),(0,[z1,z132,z59,z4,z5,z6]),(0,[z2,z8,z38,z5,z6,z140]),(0,[z1,z2,z764,z4,z5,z6])],[(0,[z1,z2,z765,z4,z5,z6]),(0,[z1,z2,z766,z4,z5,z6]),(0,[z1,z2,z767,z4,z5,z6]),(0,[z628,z1,z8,z4,z24,z6])],[(0,[z1,z71,z8,z4,z284,z6]),(0,[z638,z2,z76,z4,z5,z6]),(0,[z192,z2,z8,z4,z42,z6])],[(0,[z1,z2,z8,z4,z768,z6]),(0,[z286,z2,z76,z4,z5,z6]),(0,[z1,z2,z769,z4,z5,z6]),(0,[z2,z173,z4,z770,z5,z6]),(0,[z1,z2,z244,z215,z5,z6]),(0,[z1,z2,z771,z4,z5,z6]),(0,[z1,z2,z772,z4,z5,z6]),(0,[z2,z8,z773,z4,z5,z6])],[(0,[z2,z76,z4,z5,z6,z183]),(0,[z1,z249,z59,z4,z5,z6]),(0,[z1,z2,z774,z4,z5,z6])],[(0,[z47,z2,z8,z4,z5,z629]),(0,[z1,z58,z274,z4,z5,z6]),(0,[z1,z2,z775,z4,z5,z6]),(0,[z1,z2,z8,z776,z5,z6]),(0,[z1,z3,z488,z4,z5,z6]),(0,[z1,z2,z777,z4,z5,z6]),(0,[z1,z2,z778,z4,z5,z6])],[(0,[z1,z2,z207,z4,z5,z6]),(0,[z1,z2,z8,z4,z779,z6]),(0,[z1,z94,z58,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z780]),(0,[z1,z2,z269,z4,z177,z6]),(0,[z1,z81,z376,z4,z5,z6]),(0,[z10,z1,z2,z4,z5,z528]),(0,[z2,z8,z4,z5,z6,z781])],[(0,[z343,z2,z76,z4,z5,z6]),(0,[z782,z1,z59,z4,z5,z6]),(0,[z47,z2,z8,z4,z5,z783]),(0,[z784,z2,z8,z4,z5,z6]),(0,[z785,z2,z8,z4,z5,z6]),(0,[z1,z267,z342,z4,z5,z6]),(0,[z1,z438,z8,z4,z65,z6]),(0,[z786,z2,z8,z4,z5,z6]),(0,[z787,z2,z8,z4,z5,z6]),(0,[z1,z2,z4,z738,z44,z6])],[(1,[z17,z76,z4,z5,z6]),(0,[z1,z2,z8,z788,z5,z6]),(0,[z1,z789,z8,z4,z5,z6]),(0,[z195,z2,z8,z260,z5,z6]),(0,[z1,z2,z8,z790,z5,z6]),(0,[z1,z2,z4,z738,z5,z6]),(0,[z1,z791,z8,z4,z5,z6]),(0,[z1,z2,z792,z4,z5,z6]),(0,[z1,z2,z793,z4,z5,z6])],[(0,[z1,z2,z794,z4,z5,z6]),(0,[z1,z2,z8,z4,z507,z6]),(0,[z1,z795,z8,z4,z5,z6])],[(0,[z611,z2,z58,z4,z5,z6]),(0,[z2,z173,z4,z5,z42,z6]),(0,[z1,z2,z36,z129,z5,z6]),(0,[z1,z174,z8,z4,z796,z6]),(0,[z1,z2,z4,z5,z6,z797]),(0,[z1,z2,z4,z5,z75,z321]),(0,[z1,z2,z8,z4,z294,z6]),(0,[z1,z2,z4,z5,z6,z798])],[(0,[z1,z2,z214,z4,z5,z6]),(0,[z136,z2,z8,z4,z5,z6]),(0,[z1,z402,z799,z4,z5,z6]),(0,[z1,z2,z800,z4,z5,z6]),(0,[z801,z2,z36,z4,z5,z6]),(0,[z1,z8,z568,z4,z24,z6])]],
   [[(0,[z2,z76,z9,z5,z6,z85]),(0,[z1,z802,z8,z4,z5,z6]),(0,[z1,z112,z3,z4,z5,z6]),(0,[z1,z2,z3,z129,z5,z6]),(0,[z1,z2,z8,z4,z803,z6]),(0,[z804,z2,z8,z4,z5,z6]),(0,[z805,z2,z8,z4,z5,z6])],[(0,[z1,z3,z4,z5,z580,z6]),(0,[z1,z2,z806,z4,z5,z6]),(0,[z1,z2,z3,z4,z807,z6]),(0,[z1,z2,z808,z4,z5,z6]),(0,[z1,z8,z4,z5,z809,z31]),(0,[z1,z810,z8,z4,z5,z6])],[(0,[z14,z2,z368,z4,z5,z6])],[(0,[z1,z2,z147,z4,z5,z6]),(0,[z2,z76,z4,z5,z6,z193]),(0,[z88,z2,z76,z4,z5,z102]),(0,[z1,z123,z3,z4,z5,z6]),(0,[z1,z811,z58,z4,z5,z6]),(0,[z1,z2,z812,z4,z5,z6]),(0,[z1,z122,z59,z4,z5,z6]),(0,[z1,z3,z4,z5,z585,z6]),(0,[z1,z405,z3,z4,z5,z6]),(0,[z2,z8,z813,z4,z5,z6]),(0,[z209,z1,z8,z4,z796,z6])],[(0,[z14,z2,z354,z4,z5,z6]),(0,[z15,z169,z8,z4,z5,z6]),(0,[z137,z49,z8,z4,z5,z6]),(0,[z186,z1,z2,z4,z5,z509]),(0,[z1,z128,z36,z4,z5,z6]),(0,[z1,z2,z814,z4,z5,z6])],[(0,[z1,z2,z815,z4,z5,z6]),(0,[z1,z816,z8,z4,z5,z6])],[(0,[z1,z2,z817,z4,z5,z6]),(0,[z1,z2,z818,z4,z5,z6]),(0,[z678,z2,z76,z4,z5,z6]),(0,[z1,z434,z360,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z504]),(0,[z1,z128,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z819]),(0,[z1,z2,z820,z4,z5,z6])],[(0,[z1,z2,z264,z4,z5,z6]),(0,[z821,z2,z36,z4,z5,z6]),(0,[z145,z2,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z822,z6]),(0,[z1,z8,z4,z5,z6,z823]),(0,[z1,z2,z8,z61,z6,z366])],[(0,[z1,z2,z8,z824,z5,z6]),(0,[z1,z2,z8,z825,z5,z6]),(0,[z1,z826,z8,z4,z5,z6]),(0,[z2,z118,z4,z21,z5,z6]),(0,[z1,z225,z87,z4,z5,z6])],[(0,[z1,z402,z76,z4,z5,z6]),(0,[z14,z2,z173,z4,z5,z6]),(0,[z1,z2,z36,z4,z109,z6]),(0,[z1,z267,z8,z4,z5,z6]),(0,[z145,z2,z3,z4,z5,z6])],[(0,[z444,z1,z3,z4,z5,z6]),(0,[z1,z2,z238,z4,z56,z6]),(0,[z1,z135,z3,z72,z5,z6]),(0,[z1,z2,z269,z4,z5,z6])],[(0,[z1,z2,z8,z4,z827,z6]),(0,[z49,z1,z59,z4,z5,z6]),(0,[z33,z1,z2,z76,z5,z85]),(0,[z1,z2,z3,z4,z109,z6]),(0,[z1,z2,z828,z4,z5,z6]),(0,[z1,z2,z8,z4,z829,z6]),(0,[z2,z173,z4,z5,z75,z6]),(0,[z1,z2,z227,z222,z5,z6])],[(0,[z1,z2,z36,z830,z5,z6]),(0,[z1,z2,z4,z5,z6,z203]),(0,[z145,z2,z257,z4,z5,z6])],[(0,[z250,z2,z8,z111,z5,z6]),(0,[z1,z2,z36,z4,z285,z6]),(0,[z1,z2,z831,z4,z5,z6]),(0,[z1,z2,z52,z4,z5,z245])],[(1,[z1,z59,z4,z5,z6]),(0,[z2,z8,z4,z832,z5,z6]),(0,[z1,z833,z8,z4,z5,z6]),(0,[z1,z323,z525,z4,z5,z6])],[(0,[z1,z76,z59,z4,z5,z6]),(0,[z1,z8,z834,z4,z5,z6])]],
   [[(0,[z835,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z836,z6]),(0,[z837,z1,z8,z4,z5,z6])],[(0,[z761,z1,z8,z4,z5,z6]),(0,[z1,z434,z8,z4,z5,z6]),(0,[z49,z81,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z838,z6]),(0,[z88,z2,z8,z127,z5,z102]),(0,[z1,z2,z839,z4,z5,z6]),(0,[z840,z2,z8,z4,z5,z6])],[(0,[z1,z2,z338,z4,z5,z6]),(1,[z2,z8,z832,z5,z6]),(0,[z2,z173,z175,z4,z5,z6]),(0,[z136,z2,z743,z4,z5,z6]),(0,[z1,z841,z8,z4,z5,z6]),(0,[z46,z1,z2,z157,z4,z6])],[(0,[z209,z1,z76,z4,z24,z6]),(0,[z365,z2,z8,z4,z5,z6]),(0,[z229,z2,z36,z4,z5,z6]),(0,[z842,z2,z8,z4,z5,z6]),(0,[z46,z250,z2,z4,z5,z6])],[(0,[z1,z130,z3,z4,z5,z6]),(0,[z1,z59,z4,z5,z247,z6]),(0,[z1,z2,z843,z4,z5,z6]),(0,[z2,z173,z4,z5,z6,z102]),(0,[z47,z2,z3,z4,z5,z100]),(0,[z1,z2,z844,z4,z5,z6]),(0,[z259,z2,z8,z4,z97,z6]),(0,[z552,z1,z845,z4,z5,z6])],[(0,[z1,z40,z76,z4,z5,z6]),(0,[z1,z2,z36,z4,z388,z6]),(0,[z1,z2,z846,z4,z5,z6]),(0,[z1,z2,z847,z4,z5,z6])],[(0,[z1,z2,z8,z4,z284,z6]),(0,[z1,z2,z8,z848,z5,z6]),(0,[z15,z3,z4,z5,z42,z6]),(0,[z1,z58,z849,z4,z5,z6]),(0,[z1,z2,z850,z4,z5,z6]),(0,[z851,z1,z8,z4,z5,z6]),(0,[z1,z2,z852,z4,z5,z6]),(0,[z1,z2,z303,z4,z5,z6]),(0,[z1,z2,z144,z698,z5,z6]),(0,[z1,z358,z853,z4,z5,z6]),(0,[z1,z2,z854,z4,z5,z6])],[(0,[z2,z256,z173,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z855]),(0,[z1,z2,z8,z856,z5,z6]),(0,[z1,z402,z8,z127,z5,z6]),(0,[z1,z2,z857,z4,z5,z6]),(0,[z156,z2,z249,z4,z5,z6]),(0,[z196,z2,z36,z4,z5,z6]),(0,[z1,z2,z376,z4,z567,z6]),(0,[z1,z20,z274,z4,z5,z6]),(0,[z1,z2,z858,z4,z5,z6]),(0,[z1,z2,z859,z4,z5,z6])],[(0,[z1,z2,z8,z4,z860,z6]),(0,[z121,z71,z76,z4,z5,z6]),(0,[z499,z1,z8,z4,z24,z6]),(0,[z1,z2,z76,z4,z177,z6]),(0,[z1,z76,z861,z4,z5,z6]),(0,[z1,z2,z58,z4,z285,z6]),(0,[z1,z59,z4,z105,z5,z6]),(0,[z1,z862,z8,z4,z5,z6])],[(0,[z1,z863,z8,z4,z5,z6]),(0,[z1,z2,z864,z4,z5,z6]),(0,[z196,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z74,z220,z6])],[(0,[z1,z2,z865,z4,z5,z6]),(1,[z1,z3,z4,z284,z6]),(0,[z2,z8,z9,z5,z6,z565]),(0,[z2,z173,z3,z4,z5,z6]),(0,[z866,z2,z155,z4,z5,z6])],[(1,[z49,z368,z4,z5,z6]),(0,[z1,z174,z76,z4,z65,z6]),(0,[z1,z2,z8,z4,z867,z6]),(0,[z1,z2,z868,z4,z5,z6]),(0,[z1,z2,z869,z4,z5,z6])],[(0,[z1,z2,z870,z4,z5,z6]),(0,[z47,z2,z76,z4,z5,z6]),(0,[z2,z76,z233,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z92]),(0,[z1,z2,z871,z4,z5,z6]),(0,[z2,z872,z173,z4,z5,z6]),(0,[z1,z2,z303,z4,z70,z6])],[(0,[z626,z71,z8,z4,z5,z6]),(0,[z50,z2,z173,z4,z5,z6]),(0,[z602,z2,z8,z4,z23,z6]),(0,[z1,z2,z722,z4,z5,z6])],[(0,[z1,z8,z59,z4,z5,z6]),(0,[z1,z2,z8,z4,z873,z6]),(0,[z229,z2,z58,z4,z5,z6]),(0,[z1,z2,z799,z4,z5,z6]),(0,[z37,z2,z36,z4,z5,z6])],[(0,[z110,z1,z59,z4,z5,z6]),(0,[z874,z2,z8,z4,z5,z6]),(0,[z27,z1,z2,z3,z4,z28]),(0,[z1,z2,z8,z4,z875,z6]),(0,[z1,z2,z303,z19,z5,z6]),(0,[z1,z323,z8,z96,z5,z6])]],
   [[(0,[z1,z2,z58,z4,z388,z6]),(0,[z37,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z79,z5,z6]),(0,[z876,z1,z2,z4,z5,z6]),(0,[z536,z1,z8,z4,z24,z6]),(0,[z1,z2,z8,z4,z877,z6]),(0,[z1,z144,z274,z222,z5,z6]),(0,[z1,z2,z26,z5,z6,z85]),(0,[z1,z8,z878,z4,z5,z6])],[(0,[z465,z2,z76,z4,z5,z6]),(0,[z1,z2,z879,z4,z5,z6]),(0,[z1,z2,z880,z4,z5,z6]),(0,[z1,z17,z59,z4,z5,z6]),(0,[z88,z2,z8,z4,z5,z140]),(0,[z1,z2,z881,z4,z5,z6]),(0,[z1,z40,z8,z4,z220,z6])],[(0,[z104,z1,z354,z4,z5,z6]),(0,[z1,z2,z76,z73,z12,z6]),(0,[z1,z3,z4,z5,z613,z6]),(0,[z1,z2,z3,z79,z5,z6]),(0,[z1,z2,z8,z4,z13,z158])],[(0,[z1,z2,z8,z4,z882,z6]),(0,[z196,z201,z8,z4,z5,z6]),(0,[z280,z2,z8,z4,z6,z28]),(0,[z1,z323,z403,z4,z5,z6])],[(0,[z646,z2,z58,z4,z5,z6]),(0,[z1,z2,z883,z4,z5,z6]),(0,[z1,z2,z884,z4,z5,z6])],[(0,[z1,z2,z885,z4,z5,z6]),(0,[z1,z2,z886,z4,z5,z6]),(0,[z887,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z888,z6]),(0,[z1,z889,z8,z4,z5,z6])],[(0,[z15,z2,z173,z4,z5,z6]),(0,[z252,z2,z58,z4,z5,z6]),(0,[z2,z52,z475,z4,z5,z6]),(0,[z1,z2,z890,z4,z5,z6])],[(0,[z397,z1,z76,z4,z5,z6]),(0,[z1,z8,z861,z4,z5,z6]),(0,[z2,z208,z4,z5,z42,z6]),(0,[z1,z383,z891,z4,z5,z6]),(0,[z1,z2,z36,z4,z97,z6]),(0,[z1,z2,z63,z4,z161,z6]),(0,[z1,z81,z307,z4,z5,z18]),(0,[z1,z2,z892,z4,z5,z6])],[(0,[z1,z2,z76,z4,z5,z6]),(0,[z341,z2,z58,z4,z5,z6]),(0,[z2,z8,z893,z4,z5,z6]),(0,[z33,z2,z173,z4,z5,z6])],[(0,[z37,z2,z58,z4,z5,z6]),(0,[z1,z2,z3,z4,z97,z6]),(0,[z1,z36,z894,z4,z5,z6]),(0,[z895,z2,z173,z4,z5,z6]),(0,[z1,z2,z8,z4,z567,z6])],[(0,[z14,z2,z76,z38,z5,z6]),(0,[z1,z2,z8,z4,z896,z6]),(0,[z252,z2,z897,z4,z5,z6]),(0,[z1,z569,z8,z4,z5,z6]),(0,[z1,z67,z8,z242,z5,z6])],[(0,[z1,z2,z3,z4,z255,z6]),(0,[z1,z2,z58,z79,z5,z6]),(0,[z1,z2,z8,z4,z898,z6]),(0,[z511,z1,z2,z8,z5,z85])],[(0,[z15,z3,z4,z5,z6,z102]),(0,[z899,z2,z8,z4,z5,z6]),(0,[z1,z900,z8,z4,z5,z6])],[(0,[z487,z2,z8,z4,z5,z6]),(0,[z1,z2,z901,z4,z5,z6]),(0,[z416,z2,z76,z4,z5,z6]),(0,[z1,z2,z902,z4,z5,z6])],[(0,[z1,z2,z903,z4,z5,z6]),(0,[z1,z2,z76,z4,z70,z6]),(0,[z1,z59,z4,z904,z5,z6]),(0,[z450,z2,z8,z4,z42,z6]),(0,[z136,z2,z269,z4,z5,z6])],[(0,[z2,z76,z4,z5,z6,z263]),(0,[z1,z2,z4,z5,z6,z905]),(0,[z1,z338,z906,z4,z5,z6]),(0,[z1,z2,z8,z907,z5,z6]),(0,[z1,z2,z8,z111,z116,z6]),(0,[z1,z81,z908,z4,z5,z6]),(0,[z1,z2,z8,z909,z5,z6])]],
   [[(0,[z2,z76,z265,z4,z5,z6]),(0,[z1,z2,z910,z4,z5,z6]),(0,[z911,z1,z2,z4,z5,z6]),(0,[z136,z81,z8,z4,z5,z6])],[(0,[z275,z2,z8,z4,z5,z102]),(0,[z10,z1,z2,z4,z5,z509]),(0,[z1,z2,z912,z4,z5,z6]),(0,[z1,z913,z8,z4,z5,z6]),(0,[z1,z914,z8,z4,z5,z6])],[(0,[z22,z2,z8,z4,z689,z6]),(0,[z15,z286,z8,z4,z5,z6]),(0,[z1,z2,z58,z915,z5,z6]),(0,[z110,z171,z8,z4,z42,z6]),(0,[z1,z2,z8,z916,z5,z6]),(0,[z2,z8,z111,z5,z6,z102]),(0,[z367,z1,z8,z4,z5,z31]),(0,[z1,z94,z36,z4,z5,z6]),(0,[z2,z8,z917,z4,z5,z6]),(0,[z1,z2,z8,z4,z918,z6]),(0,[z1,z2,z4,z5,z6,z919]),(0,[z1,z8,z73,z548,z4,z6]),(0,[z2,z920,z233,z4,z5,z6])],[(0,[z1,z2,z8,z4,z921,z6]),(0,[z121,z76,z3,z4,z5,z6]),(0,[z401,z1,z59,z4,z5,z6]),(0,[z1,z2,z891,z4,z5,z6]),(0,[z1,z2,z922,z4,z5,z6]),(0,[z1,z923,z8,z4,z5,z6]),(0,[z1,z2,z924,z4,z5,z6]),(0,[z1,z2,z3,z925,z5,z6]),(0,[z1,z8,z548,z4,z5,z6]),(0,[z1,z2,z926,z4,z5,z6]),(0,[z1,z2,z927,z4,z5,z6]),(0,[z1,z225,z928,z4,z5,z6]),(0,[z1,z2,z929,z4,z5,z6])],[(0,[z2,z55,z4,z5,z6,z102]),(0,[z2,z475,z76,z4,z5,z6]),(0,[z1,z2,z930,z4,z5,z6]),(0,[z1,z3,z562,z4,z5,z6]),(0,[z1,z94,z3,z4,z5,z6]),(0,[z1,z8,z4,z24,z6,z350]),(0,[z1,z2,z8,z4,z220,z6]),(0,[z1,z2,z8,z931,z5,z6]),(0,[z10,z1,z2,z4,z5,z932])],[(0,[z1,z81,z8,z4,z5,z18]),(0,[z1,z2,z87,z4,z5,z6]),(0,[z250,z8,z4,z5,z6,z84])],[(0,[z1,z2,z8,z127,z5,z6]),(0,[z1,z2,z36,z4,z56,z6]),(0,[z1,z2,z8,z4,z933,z6])],[(0,[z1,z354,z4,z5,z6,z31]),(0,[z462,z2,z76,z4,z5,z6]),(0,[z934,z2,z8,z4,z5,z6]),(0,[z343,z2,z8,z4,z11,z6]),(0,[z1,z2,z8,z73,z6,z663]),(0,[z1,z8,z4,z6,z212,z84])],[(0,[z2,z76,z4,z5,z284,z6]),(0,[z1,z2,z8,z935,z5,z6]),(0,[z2,z333,z4,z5,z6,z102]),(0,[z1,z2,z36,z4,z936,z6]),(0,[z1,z2,z937,z4,z5,z6]),(0,[z250,z2,z36,z4,z5,z6]),(0,[z1,z117,z72,z4,z5,z6]),(0,[z1,z8,z938,z4,z5,z6])],[(0,[z47,z2,z368,z4,z5,z6]),(0,[z1,z2,z939,z4,z5,z6]),(0,[z1,z2,z58,z4,z114,z6]),(0,[z1,z2,z303,z4,z294,z6])],[(0,[z2,z76,z4,z5,z292,z6]),(0,[z250,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z940,z5,z6])],[(0,[z47,z2,z354,z4,z5,z6]),(0,[z1,z742,z76,z4,z5,z6]),(0,[z7,z2,z36,z9,z5,z6]),(0,[z1,z81,z269,z4,z5,z6]),(0,[z1,z2,z8,z941,z5,z6]),(0,[z942,z2,z8,z4,z5,z6]),(0,[z2,z8,z475,z4,z220,z6]),(0,[z46,z1,z4,z5,z6,z84]),(0,[z1,z2,z4,z5,z6,z943])],[(0,[z1,z944,z8,z4,z5,z6]),(0,[z2,z8,z4,z5,z829,z6]),(0,[z1,z2,z139,z111,z5,z6]),(0,[z1,z3,z631,z4,z5,z6]),(0,[z1,z2,z945,z4,z5,z6]),(0,[z946,z2,z8,z4,z5,z6])],[(0,[z2,z76,z300,z4,z5,z6]),(0,[z1,z947,z8,z4,z5,z6]),(0,[z1,z2,z139,z4,z116,z6]),(0,[z1,z2,z155,z4,z5,z6]),(0,[z1,z2,z948,z4,z5,z6]),(0,[z1,z949,z8,z4,z5,z6]),(0,[z1,z2,z4,z11,z6,z53]),(0,[z681,z1,z2,z8,z5,z85]),(0,[z27,z1,z2,z8,z243,z28])],[(0,[z1,z337,z36,z4,z5,z6]),(0,[z280,z2,z58,z4,z5,z6]),(0,[z1,z2,z950,z4,z5,z6]),(0,[z406,z1,z8,z4,z24,z6]),(0,[z30,z1,z36,z4,z5,z31]),(0,[z32,z2,z36,z4,z5,z6]),(0,[z104,z2,z755,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z951]),(0,[z1,z201,z4,z21,z5,z6]),(0,[z952,z2,z8,z4,z5,z6]),(0,[z1,z953,z8,z4,z5,z6])],[(0,[z22,z2,z954,z4,z5,z6]),(0,[z1,z908,z3,z4,z5,z6]),(0,[z1,z2,z955,z4,z5,z6]),(0,[z1,z135,z8,z72,z177,z6]),(0,[z51,z2,z475,z4,z5,z6]),(0,[z1,z2,z956,z4,z5,z6])]],
   [[(0,[z1,z2,z8,z4,z957,z6]),(0,[z1,z2,z958,z4,z5,z6]),(0,[z33,z1,z2,z58,z5,z85]),(0,[z47,z2,z173,z4,z5,z6]),(0,[z32,z2,z3,z4,z5,z6]),(0,[z2,z173,z959,z4,z5,z6]),(0,[z1,z2,z960,z4,z5,z6]),(0,[z1,z2,z358,z73,z12,z6]),(0,[z1,z2,z8,z5,z6,z961])],[(0,[z71,z8,z4,z5,z6,z308]),(0,[z49,z76,z4,z5,z6,z31]),(0,[z1,z2,z58,z4,z56,z6]),(0,[z1,z2,z962,z4,z5,z6]),(0,[z2,z173,z4,z5,z245,z6]),(0,[z963,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z964,z6]),(0,[z1,z2,z965,z4,z5,z6]),(0,[z1,z2,z966,z4,z5,z6])],[(0,[z2,z76,z4,z5,z6,z308]),(0,[z2,z690,z76,z4,z5,z6]),(0,[z1,z2,z967,z4,z5,z6]),(0,[z229,z2,z256,z4,z5,z6]),(0,[z1,z2,z112,z4,z5,z245]),(0,[z1,z2,z8,z968,z4,z6]),(0,[z1,z526,z969,z4,z5,z6]),(0,[z33,z1,z526,z8,z5,z85])],[(0,[z1,z234,z8,z72,z5,z6]),(0,[z2,z147,z76,z4,z5,z6]),(0,[z250,z2,z58,z4,z5,z6]),(0,[z970,z2,z8,z4,z5,z6]),(0,[z1,z2,z971,z4,z5,z6]),(0,[z1,z2,z279,z73,z12,z6])],[(0,[z49,z2,z55,z4,z5,z6]),(0,[z1,z383,z8,z4,z109,z6]),(0,[z47,z2,z8,z4,z109,z6]),(0,[z336,z1,z3,z4,z5,z6]),(0,[z1,z133,z4,z5,z24,z6]),(0,[z2,z342,z756,z4,z5,z6]),(0,[z1,z2,z972,z4,z5,z6]),(0,[z195,z2,z376,z4,z5,z6]),(0,[z973,z2,z8,z4,z5,z6]),(0,[z840,z2,z57,z4,z5,z6])],[(0,[z1,z2,z368,z4,z5,z6]),(0,[z344,z2,z76,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z974]),(0,[z1,z2,z358,z4,z44,z6]),(0,[z1,z2,z975,z4,z5,z6])],[(0,[z211,z71,z8,z4,z5,z6]),(0,[z1,z207,z4,z5,z6,z31]),(0,[z7,z2,z58,z9,z5,z6]),(0,[z1,z257,z59,z4,z5,z6]),(0,[z1,z2,z976,z4,z5,z6]),(0,[z1,z977,z8,z4,z5,z6]),(0,[z1,z2,z978,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z979]),(0,[z1,z2,z358,z4,z5,z6]),(0,[z1,z980,z8,z4,z5,z6])],[(0,[z1,z2,z981,z4,z5,z6]),(0,[z1,z2,z354,z4,z5,z6]),(0,[z104,z1,z982,z4,z5,z6]),(0,[z1,z546,z8,z4,z24,z6]),(0,[z2,z983,z8,z4,z5,z6])],[(0,[z1,z122,z101,z4,z5,z6]),(0,[z2,z76,z317,z4,z5,z6]),(0,[z22,z2,z58,z4,z23,z6]),(0,[z25,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z984,z6]),(0,[z1,z2,z8,z175,z503,z6]),(0,[z1,z67,z36,z4,z5,z6]),(0,[z1,z2,z985,z4,z5,z6])],[(0,[z121,z71,z8,z4,z284,z6]),(0,[z1,z2,z76,z788,z5,z6]),(0,[z506,z2,z76,z4,z5,z6]),(0,[z30,z1,z58,z4,z5,z31]),(0,[z32,z2,z58,z4,z5,z6]),(0,[z1,z2,z986,z4,z5,z6]),(0,[z205,z1,z3,z4,z5,z6]),(0,[z104,z1,z8,z4,z97,z6]),(0,[z1,z2,z279,z4,z5,z6]),(0,[z1,z2,z4,z74,z11,z6]),(0,[z280,z2,z987,z4,z5,z6])],[(0,[z1,z2,z76,z4,z507,z6]),(0,[z1,z2,z63,z4,z520,z6]),(0,[z1,z2,z8,z4,z5,z783]),(0,[z1,z67,z3,z4,z5,z6]),(0,[z2,z36,z988,z4,z5,z6]),(0,[z511,z1,z8,z4,z5,z31]),(0,[z1,z2,z525,z4,z5,z6]),(0,[z10,z1,z2,z4,z5,z53])],[(0,[z1,z2,z76,z4,z294,z6]),(0,[z50,z17,z8,z4,z5,z6]),(0,[z1,z174,z8,z4,z78,z6]),(0,[z1,z526,z8,z4,z5,z6]),(0,[z1,z2,z989,z4,z5,z6])],[(0,[z1,z2,z173,z4,z5,z6]),(0,[z136,z2,z76,z4,z5,z6]),(0,[z2,z8,z832,z38,z5,z6]),(0,[z30,z1,z83,z4,z5,z31]),(0,[z280,z2,z8,z73,z4,z6])],[(0,[z1,z990,z8,z4,z5,z6]),(0,[z349,z1,z3,z4,z5,z6]),(1,[z217,z8,z4,z24,z6]),(0,[z1,z2,z991,z4,z5,z6])],[(0,[z2,z103,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z992,z6]),(0,[z1,z122,z342,z4,z5,z6]),(0,[z1,z122,z307,z4,z5,z6]),(0,[z1,z993,z8,z4,z5,z6])],[(0,[z2,z173,z9,z4,z5,z6]),(0,[z1,z2,z994,z4,z5,z6]),(0,[z1,z135,z8,z72,z5,z6]),(0,[z1,z2,z222,z995,z5,z6])]],
   [[(0,[z2,z76,z4,z5,z6,z330]),(0,[z14,z2,z8,z4,z109,z6]),(0,[z1,z3,z4,z595,z5,z6]),(0,[z1,z2,z8,z4,z5,z996]),(0,[z259,z2,z8,z79,z5,z6]),(0,[z1,z997,z8,z4,z5,z6]),(0,[z1,z2,z998,z4,z5,z6]),(0,[z1,z2,z999,z4,z5,z6])],[(0,[z1,z2,z1000,z4,z5,z6]),(0,[z254,z2,z76,z4,z5,z6]),(0,[z1,z2,z1001,z4,z5,z6]),(0,[z1,z526,z8,z4,z70,z6])],[(0,[z1,z2,z384,z4,z5,z6]),(0,[z554,z1,z59,z4,z5,z6]),(0,[z2,z8,z4,z109,z6,z102]),(0,[z1,z2,z3,z4,z285,z6]),(0,[z1,z2,z1002,z4,z5,z6]),(0,[z1,z2,z1003,z4,z5,z6])],[(0,[z17,z2,z76,z4,z5,z6]),(0,[z14,z1,z59,z4,z5,z6]),(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z67,z58,z4,z5,z6]),(0,[z22,z2,z103,z4,z23,z6]),(0,[z1,z3,z4,z5,z6,z601])],[(0,[z406,z71,z8,z4,z5,z6]),(0,[z1,z59,z4,z5,z1005,z6]),(0,[z14,z2,z8,z4,z285,z6]),(0,[z1006,z2,z8,z4,z5,z6]),(0,[z1,z2,z57,z4,z11,z6])],[(0,[z1,z383,z248,z4,z5,z6]),(0,[z1,z2,z8,z4,z1007,z6]),(0,[z1008,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z1009]),(0,[z1010,z1,z8,z4,z5,z6])],[(0,[z15,z49,z8,z4,z5,z6]),(0,[z195,z2,z8,z4,z5,z6]),(0,[z1,z267,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z1011,z6]),(0,[z1012,z2,z8,z4,z5,z6]),(0,[z259,z2,z1013,z4,z5,z6]),(0,[z1,z2,z8,z73,z157,z6])],[(0,[z1,z368,z354,z4,z5,z6]),(0,[z497,z2,z76,z4,z5,z6]),(0,[z1,z59,z4,z5,z6,z31]),(0,[z14,z2,z338,z38,z5,z6]),(0,[z14,z2,z8,z832,z5,z6]),(0,[z1,z2,z8,z1014,z5,z6]),(0,[z1,z3,z4,z5,z6,z605]),(0,[z104,z1,z36,z105,z5,z6]),(0,[z1,z2,z8,z1015,z5,z6]),(0,[z1,z2,z8,z260,z97,z6]),(0,[z1,z8,z4,z97,z6,z31]),(0,[z250,z2,z8,z157,z4,z6])],[(0,[z229,z2,z3,z4,z5,z6]),(0,[z2,z173,z4,z5,z44,z6]),(0,[z2,z475,z222,z4,z5,z6]),(0,[z1,z2,z358,z4,z74,z6]),(0,[z1,z1016,z8,z4,z5,z6]),(0,[z32,z225,z8,z4,z5,z6]),(0,[z280,z2,z8,z243,z5,z6]),(0,[z1,z1017,z8,z4,z5,z6])],[(0,[z1,z1018,z8,z4,z5,z6]),(0,[z47,z2,z8,z4,z5,z100]),(0,[z1,z2,z36,z111,z5,z6]),(0,[z487,z2,z264,z4,z5,z6]),(0,[z10,z1,z201,z4,z5,z6]),(0,[z1,z2,z403,z175,z4,z6]),(0,[z1019,z2,z8,z4,z5,z6])],[(0,[z47,z2,z8,z4,z5,z486]),(0,[z1,z1020,z8,z4,z5,z6]),(0,[z1,z2,z36,z4,z116,z6]),(0,[z1,z2,z3,z4,z388,z6]),(0,[z2,z118,z36,z4,z5,z6]),(0,[z1,z2,z8,z73,z243,z6]),(0,[z46,z2,z4,z5,z6,z92]),(1,[z2,z749,z4,z5,z6])],[(0,[z1021,z1,z8,z4,z5,z6]),(0,[z1,z81,z3,z4,z5,z31]),(0,[z343,z2,z8,z129,z5,z6]),(0,[z1,z2,z8,z96,z5,z6])],[(0,[z71,z8,z348,z4,z5,z6]),(0,[z1,z2,z272,z4,z161,z6]),(0,[z1,z1022,z8,z4,z5,z6])],[(0,[z1,z2,z390,z4,z5,z6]),(0,[z1,z1023,z58,z4,z5,z6]),(0,[z1,z2,z1024,z4,z5,z6]),(0,[z1,z2,z1025,z4,z5,z6]),(0,[z2,z173,z4,z5,z61,z6])],[(0,[z1,z434,z76,z4,z5,z6]),(0,[z1,z325,z8,z4,z285,z6]),(0,[z252,z2,z36,z4,z5,z6]),(0,[z1026,z2,z36,z4,z5,z6]),(0,[z552,z1,z8,z4,z5,z6])],[(0,[z14,z2,z76,z9,z5,z6]),(0,[z1,z59,z354,z4,z5,z6]),(0,[z1,z2,z1027,z4,z5,z6]),(0,[z278,z1,z3,z4,z5,z6]),(0,[z1028,z2,z8,z4,z5,z6]),(0,[z2,z173,z4,z65,z5,z6]),(0,[z1,z2,z403,z4,z5,z6]),(0,[z1029,z2,z8,z4,z5,z6])]],
   [[(0,[z465,z1,z3,z4,z5,z6]),(0,[z365,z2,z76,z4,z5,z6]),(0,[z1,z1030,z8,z4,z5,z6]),(0,[z252,z2,z3,z4,z5,z6])],[(0,[z2,z55,z4,z5,z42,z6]),(0,[z2,z954,z76,z4,z5,z6]),(0,[z14,z2,z248,z4,z5,z6]),(0,[z343,z128,z8,z4,z5,z6]),(0,[z27,z1,z2,z8,z4,z1009])],[(0,[z104,z1,z58,z105,z5,z6]),(0,[z1,z425,z8,z4,z65,z6]),(0,[z1,z2,z333,z4,z285,z6]),(0,[z1,z2,z1031,z4,z5,z6]),(0,[z1032,z2,z8,z4,z5,z6]),(0,[z1033,z1,z8,z4,z5,z6]),(0,[z365,z569,z8,z4,z5,z6])],[(0,[z443,z2,z76,z4,z5,z6]),(0,[z2,z36,z475,z4,z5,z6]),(0,[z657,z1,z8,z105,z5,z6])],[(0,[z217,z2,z8,z4,z5,z6]),(0,[z1,z2,z58,z111,z5,z6]),(0,[z1,z59,z222,z4,z5,z6]),(0,[z1,z249,z72,z4,z5,z6]),(0,[z1034,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z11,z6])],[(0,[z1,z2,z58,z4,z116,z6]),(0,[z2,z118,z58,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1035,z6]),(0,[z1,z2,z1036,z4,z5,z6]),(0,[z1,z279,z548,z4,z5,z6]),(0,[z1,z2,z303,z5,z6,z85]),(0,[z1,z2,z8,z243,z13,z6])],[(0,[z15,z3,z9,z4,z5,z6]),(0,[z50,z1,z59,z4,z5,z6]),(0,[z1,z8,z274,z4,z114,z6]),(0,[z1,z569,z8,z175,z4,z6]),(0,[z1,z2,z73,z87,z4,z6]),(0,[z2,z8,z1037,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z1038])],[(0,[z1,z2,z76,z4,z867,z6]),(0,[z1,z2,z108,z4,z5,z357]),(0,[z1,z2,z1039,z4,z5,z6]),(0,[z1,z2,z1040,z4,z5,z6]),(0,[z487,z2,z852,z4,z5,z6]),(0,[z2,z8,z233,z175,z4,z6]),(0,[z1041,z1,z8,z4,z5,z6])],[(0,[z15,z1,z249,z4,z5,z6]),(1,[z2,z760,z4,z5,z6]),(0,[z1,z2,z1042,z4,z5,z6])],[(0,[z121,z690,z8,z4,z5,z6]),(0,[z1,z2,z1043,z4,z5,z6]),(0,[z1,z2,z920,z4,z5,z6]),(0,[z7,z2,z8,z35,z5,z6]),(0,[z1,z171,z1044,z4,z5,z6])],[(0,[z1,z2,z1045,z4,z5,z6]),(0,[z1,z2,z1046,z4,z5,z6]),(0,[z1,z2,z36,z1047,z5,z6]),(0,[z46,z552,z1,z4,z5,z6])],[(0,[z1,z2,z1048,z4,z5,z6]),(0,[z131,z2,z76,z4,z5,z6]),(0,[z187,z1,z2,z198,z5,z6]),(0,[z89,z2,z8,z4,z5,z102]),(0,[z89,z1,z2,z4,z5,z53]),(0,[z1,z59,z4,z23,z5,z6]),(0,[z1,z740,z8,z4,z5,z6]),(0,[z1,z2,z1049,z4,z5,z6]),(0,[z1,z2,z982,z4,z5,z6]),(0,[z416,z1,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z284,z6]),(0,[z1,z2,z1050,z4,z5,z6]),(0,[z1,z2,z1051,z4,z5,z6]),(0,[z441,z1,z3,z4,z5,z6]),(0,[z1,z1052,z58,z4,z5,z6]),(0,[z1,z2,z3,z4,z1053,z6]),(0,[z104,z1,z216,z105,z5,z6]),(0,[z1,z40,z155,z4,z5,z6]),(1,[z1,z8,z712,z5,z6]),(0,[z552,z1,z4,z5,z6,z219])],[(0,[z1,z81,z207,z4,z5,z6]),(0,[z1,z2,z1054,z4,z5,z6]),(0,[z2,z8,z233,z4,z5,z6]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z30,z1,z8,z260,z5,z31]),(0,[z679,z1,z2,z4,z44,z6]),(0,[z1,z526,z8,z4,z294,z6]),(0,[z552,z1,z8,z4,z6,z212])],[(0,[z2,z55,z9,z4,z5,z6]),(0,[z202,z2,z36,z4,z5,z6])]],
   [[(0,[z15,z1,z59,z4,z5,z6]),(0,[z1,z59,z12,z4,z5,z6]),(0,[z1,z8,z548,z175,z4,z6]),(0,[z1,z2,z1056,z4,z5,z6])],[(0,[z22,z2,z76,z4,z42,z6]),(0,[z1,z2,z1057,z4,z5,z6]),(0,[z1,z1058,z8,z4,z5,z6]),(0,[z1,z2,z1059,z4,z5,z6]),(0,[z1060,z2,z8,z4,z5,z6]),(0,[z202,z2,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z114,z6])],[(0,[z33,z1,z59,z4,z5,z6]),(0,[z1,z2,z87,z175,z4,z6])],[(0,[z1,z2,z8,z4,z1061,z6]),(0,[z1,z2,z1062,z4,z5,z6]),(0,[z2,z333,z9,z4,z5,z6]),(0,[z1,z2,z1063,z4,z5,z6]),(0,[z1,z2,z3,z4,z114,z6]),(0,[z1,z2,z1064,z4,z5,z6]),(0,[z1,z128,z4,z74,z5,z6])],[(0,[z761,z121,z8,z4,z5,z6]),(0,[z121,z2,z879,z4,z5,z6]),(0,[z2,z8,z1065,z4,z5,z6]),(0,[z1,z2,z1066,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1067,z6]),(0,[z15,z49,z207,z4,z5,z6]),(0,[z49,z441,z76,z4,z5,z6]),(0,[z1,z1068,z8,z4,z5,z6]),(0,[z1,z2,z1069,z4,z5,z6]),(0,[z1,z1070,z8,z4,z5,z6]),(0,[z1,z545,z8,z4,z24,z6]),(0,[z259,z2,z1071,z4,z5,z6]),(0,[z1,z1072,z8,z4,z5,z6]),(0,[z1073,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1074,z6])],[(0,[z71,z8,z4,z42,z24,z6]),(0,[z1,z2,z76,z4,z567,z6]),(0,[z320,z2,z76,z4,z5,z6]),(0,[z1,z228,z59,z4,z5,z6]),(0,[z1,z2,z58,z1075,z5,z6]),(0,[z747,z2,z8,z4,z5,z6]),(0,[z280,z2,z36,z4,z5,z6]),(0,[z1,z2,z1076,z4,z5,z6]),(0,[z40,z8,z475,z4,z5,z6]),(0,[z25,z8,z274,z4,z5,z6]),(0,[z145,z2,z4,z74,z5,z6]),(0,[z250,z2,z1077,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1078,z6]),(0,[z2,z76,z4,z42,z24,z6]),(0,[z1,z569,z76,z4,z5,z6]),(0,[z1,z1079,z59,z4,z5,z6]),(0,[z1,z2,z58,z4,z1080,z6]),(0,[z1,z982,z3,z4,z5,z6]),(0,[z217,z2,z744,z4,z5,z6])],[(0,[z280,z2,z3,z4,z5,z6]),(0,[z1,z2,z8,z925,z5,z6]),(0,[z2,z173,z4,z5,z1081,z6]),(0,[z30,z195,z8,z4,z5,z31])],[(0,[z1,z2,z8,z1082,z4,z6]),(0,[z1,z232,z3,z4,z24,z6]),(0,[z185,z2,z173,z4,z5,z6])],[(0,[z1,z17,z8,z4,z5,z6]),(0,[z121,z71,z354,z4,z5,z6]),(0,[z275,z1,z8,z4,z5,z31]),(0,[z15,z49,z214,z4,z5,z6]),(0,[z487,z2,z76,z4,z5,z6]),(0,[z1,z2,z399,z222,z5,z6]),(0,[z202,z2,z58,z4,z5,z6]),(0,[z1,z171,z36,z4,z5,z6]),(0,[z104,z1,z8,z4,z388,z6]),(0,[z1,z2,z4,z44,z6,z363])],[(0,[z121,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z4,z6,z212]),(0,[z1,z2,z3,z4,z56,z6]),(0,[z1,z2,z1083,z4,z5,z6]),(0,[z1,z249,z4,z5,z24,z6]),(0,[z660,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1084]),(0,[z1085,z2,z8,z4,z5,z6]),(0,[z1086,z2,z8,z4,z5,z6]),(0,[z1,z2,z1087,z4,z5,z6]),(0,[z1,z8,z1088,z4,z5,z6]),(0,[z10,z1,z128,z4,z5,z53]),(0,[z1,z94,z1089,z4,z5,z6])],[(0,[z1,z2,z1090,z4,z5,z6]),(0,[z2,z249,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z1091,z6]),(0,[z1,z2,z1092,z4,z5,z6]),(0,[z1,z171,z3,z4,z5,z6]),(0,[z645,z2,z8,z4,z42,z6]),(0,[z1,z2,z1093,z4,z5,z6]),(0,[z1,z548,z1094,z4,z5,z6]),(0,[z1095,z2,z8,z4,z5,z6])],[(0,[z1,z2,z1096,z4,z5,z6]),(0,[z46,z1,z2,z4,z5,z6])],[(0,[z1,z2,z1097,z4,z5,z6]),(0,[z1,z269,z72,z4,z5,z6]),(0,[z1,z135,z269,z72,z5,z6]),(0,[z1098,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1099,z6]),(0,[z1,z2,z8,z4,z1100,z6]),(0,[z110,z2,z36,z4,z42,z6]),(0,[z579,z1,z2,z4,z5,z53]),(0,[z1,z2,z8,z4,z6,z1101]),(0,[z1,z2,z8,z4,z1102,z6]),(0,[z1,z2,z8,z4,z5,z1009])]],
   [[(0,[z1,z2,z1103,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1104]),(0,[z7,z2,z3,z9,z5,z6]),(0,[z22,z2,z36,z4,z23,z6]),(0,[z1,z3,z175,z4,z24,z6]),(0,[z25,z2,z36,z4,z5,z6]),(0,[z1105,z2,z8,z4,z5,z6])],[(0,[z1,z2,z1106,z4,z5,z6]),(0,[z1,z2,z76,z4,z220,z6]),(0,[z110,z2,z3,z4,z42,z6]),(0,[z1,z3,z4,z5,z692,z6]),(0,[z47,z2,z147,z4,z5,z100]),(0,[z1107,z1,z2,z4,z5,z6])],[(0,[z1,z81,z76,z4,z5,z18]),(0,[z1,z811,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1108,z6]),(0,[z22,z2,z3,z4,z23,z6]),(0,[z1,z2,z8,z1109,z5,z6]),(0,[z25,z2,z3,z4,z5,z6]),(0,[z2,z173,z4,z1110,z5,z6]),(0,[z1,z36,z670,z4,z5,z6]),(0,[z1,z2,z4,z5,z932,z53]),(0,[z1,z2,z1111,z4,z5,z6]),(0,[z365,z2,z525,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1112,z6]),(0,[z1,z2,z8,z4,z1113,z6]),(0,[z1,z2,z76,z127,z5,z6]),(0,[z650,z2,z8,z4,z5,z102]),(0,[z88,z2,z8,z4,z5,z783]),(0,[z30,z1,z3,z4,z5,z31]),(0,[z1,z155,z3,z4,z5,z6]),(0,[z2,z173,z4,z5,z6,z151]),(0,[z1114,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1115,z6]),(0,[z1,z2,z8,z175,z496,z6]),(0,[z1,z2,z4,z5,z6,z1116])],[(0,[z15,z1,z3,z4,z5,z6]),(0,[z2,z130,z76,z4,z5,z6]),(0,[z90,z2,z76,z4,z5,z6]),(0,[z1,z103,z775,z4,z5,z6]),(0,[z1,z8,z105,z5,z6,z449]),(0,[z1,z2,z8,z4,z1117,z6]),(0,[z1,z2,z4,z5,z6,z1118])],[(0,[z1,z2,z8,z4,z1119,z6]),(0,[z15,z49,z101,z4,z5,z6]),(0,[z2,z76,z4,z5,z6,z398]),(0,[z1,z2,z1120,z4,z5,z6]),(0,[z1,z171,z58,z4,z5,z6]),(0,[z1,z2,z741,z4,z5,z6]),(1,[z1,z775,z4,z5,z6]),(0,[z88,z2,z173,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z92]),(0,[z1,z342,z3,z4,z5,z6]),(0,[z2,z155,z755,z4,z5,z6]),(0,[z104,z1,z8,z79,z5,z6]),(0,[z2,z228,z118,z4,z5,z6]),(0,[z32,z2,z1121,z4,z5,z6])],[(0,[z2,z154,z76,z4,z5,z6]),(0,[z1,z1122,z8,z4,z5,z6]),(0,[z681,z1,z2,z8,z4,z28]),(0,[z1,z526,z303,z4,z5,z6])],[(0,[z2,z354,z4,z5,z42,z6]),(0,[z2,z76,z4,z13,z42,z6]),(0,[z2,z173,z4,z74,z5,z6]),(0,[z1,z2,z157,z4,z6,z219])],[(0,[z1,z2,z8,z129,z5,z6])],[(0,[z530,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z4,z807,z6]),(0,[z2,z173,z4,z5,z24,z6]),(0,[z801,z2,z8,z4,z5,z6]),(0,[z1,z1123,z8,z4,z5,z6])],[(0,[z110,z2,z58,z4,z42,z6]),(0,[z47,z1,z59,z4,z5,z6]),(0,[z1,z2,z8,z4,z1124,z6]),(0,[z1,z8,z79,z5,z6,z31]),(1,[z2,z1125,z4,z5,z6]),(0,[z1,z2,z63,z4,z113,z6]),(1,[z1,z2,z8,z735,z6]),(0,[z2,z8,z73,z233,z4,z6]),(0,[z33,z1,z2,z8,z212,z85])],[(0,[z47,z2,z8,z4,z285,z6]),(0,[z2,z173,z4,z161,z5,z6]),(0,[z1,z2,z36,z1126,z5,z6]),(0,[z1,z2,z1127,z4,z5,z6]),(0,[z1,z2,z8,z4,z796,z6]),(0,[z1,z2,z1128,z4,z5,z6])],[(0,[z14,z2,z55,z4,z5,z6]),(0,[z1,z2,z8,z1129,z5,z6]),(0,[z1,z2,z8,z4,z1130,z6])],[(0,[z2,z76,z4,z413,z5,z6]),(0,[z1,z2,z8,z73,z561,z6]),(0,[z1,z86,z3,z4,z5,z6]),(0,[z1,z2,z52,z4,z5,z932]),(0,[z1,z2,z748,z4,z5,z6])],[(0,[z2,z199,z76,z4,z42,z6]),(0,[z1,z128,z8,z4,z5,z6]),(0,[z1,z2,z473,z21,z5,z6]),(0,[z1,z2,z144,z222,z114,z6])],[(0,[z166,z2,z76,z4,z5,z6]),(0,[z1,z59,z4,z13,z5,z6]),(0,[z1,z2,z4,z5,z6,z1131]),(0,[z1,z2,z1132,z4,z5,z6]),(0,[z2,z173,z4,z5,z168,z6]),(0,[z1,z2,z8,z1133,z5,z6])]],
   [[(0,[z169,z2,z76,z4,z5,z6]),(0,[z1,z8,z72,z712,z5,z6]),(0,[z217,z2,z264,z4,z5,z6]),(0,[z2,z118,z4,z5,z75,z6])],[(0,[z145,z2,z8,z4,z5,z6]),(0,[z1,z59,z4,z21,z5,z6]),(0,[z1,z1134,z8,z4,z5,z6]),(0,[z1,z274,z4,z5,z6,z53]),(0,[z365,z2,z854,z4,z5,z6])],[(0,[z2,z58,z708,z4,z5,z6]),(0,[z397,z1,z8,z4,z109,z6]),(0,[z136,z2,z1054,z4,z5,z6])],[(0,[z574,z1,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z109,z6]),(0,[z1,z383,z238,z4,z5,z6]),(0,[z2,z1135,z173,z4,z5,z6]),(0,[z365,z2,z8,z96,z5,z6])],[(0,[z2,z58,z475,z4,z5,z6]),(0,[z1,z2,z1136,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z783]),(0,[z2,z3,z233,z4,z5,z6]),(0,[z68,z1,z3,z4,z5,z6]),(0,[z229,z122,z36,z4,z5,z6]),(0,[z2,z112,z173,z4,z5,z6]),(0,[z217,z2,z8,z4,z24,z6])],[(0,[z1,z2,z4,z995,z5,z6]),(0,[z1,z2,z1137,z4,z5,z6]),(0,[z1138,z2,z8,z4,z5,z6])],[(0,[z1,z1,z59,z4,z5,z6]),(0,[z1,z2,z8,z830,z5,z6]),(0,[z51,z1,z274,z4,z5,z6]),(0,[z1,z2,z8,z12,z735,z6])],[(0,[z1,z122,z8,z4,z284,z6]),(0,[z554,z1,z2,z106,z5,z6]),(0,[z1,z2,z1139,z4,z5,z6]),(0,[z1,z2,z8,z4,z285,z6]),(0,[z1,z174,z216,z4,z5,z6]),(0,[z27,z1,z2,z8,z4,z366]),(0,[z2,z4,z5,z6,z855,z92]),(0,[z365,z2,z403,z4,z5,z6])],[(0,[z121,z2,z368,z4,z5,z6]),(0,[z14,z2,z1140,z4,z5,z6]),(0,[z1,z526,z76,z4,z5,z6]),(0,[z47,z2,z248,z4,z5,z6]),(0,[z33,z1,z2,z3,z5,z85]),(0,[z1,z146,z3,z4,z5,z6]),(0,[z1,z299,z36,z4,z5,z6]),(0,[z1,z2,z376,z79,z5,z6]),(0,[z1,z2,z8,z4,z5,z809])],[(0,[z49,z8,z368,z4,z5,z6]),(0,[z1,z2,z1141,z4,z5,z6]),(0,[z1,z2,z1142,z4,z5,z6]),(0,[z1,z2,z8,z73,z420,z6]),(0,[z46,z1,z2,z222,z5,z6]),(0,[z1,z2,z129,z5,z6,z53]),(0,[z1,z569,z525,z4,z5,z6]),(0,[z1,z2,z8,z243,z6,z28])],[(0,[z761,z71,z8,z4,z5,z6]),(0,[z121,z2,z354,z4,z5,z6]),(0,[z2,z76,z4,z5,z424,z6]),(0,[z1,z2,z1143,z4,z5,z6]),(0,[z474,z1,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z1144,z6])],[(0,[z121,z123,z8,z4,z5,z6]),(0,[z2,z249,z354,z4,z5,z6]),(0,[z1,z201,z58,z4,z5,z6]),(0,[z1145,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1146,z6]),(0,[z104,z1,z3,z105,z5,z6]),(0,[z1,z3,z548,z4,z5,z6]),(0,[z1,z2,z167,z4,z177,z6]),(1,[z1,z2,z4,z5,z932])],[(0,[z2,z354,z4,z5,z6,z102]),(0,[z2,z36,z4,z5,z6,z92]),(0,[z1147,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z18,z370]),(0,[z1148,z2,z8,z4,z5,z6]),(0,[z25,z2,z144,z222,z5,z6])],[(0,[z15,z47,z3,z4,z5,z6]),(0,[z397,z1,z238,z4,z5,z6]),(0,[z1,z2,z3,z111,z5,z6]),(0,[z1,z2,z1149,z4,z5,z6]),(0,[z1,z372,z3,z4,z5,z6]),(0,[z2,z118,z144,z4,z5,z6]),(0,[z33,z1,z2,z5,z219,z85])],[(0,[z121,z2,z173,z4,z5,z6]),(0,[z190,z2,z76,z4,z5,z6]),(0,[z1,z36,z59,z4,z5,z6]),(0,[z1,z2,z3,z4,z116,z6]),(0,[z2,z118,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z388,z6]),(0,[z1,z2,z1150,z4,z5,z6]),(0,[z1,z2,z376,z4,z97,z6]),(0,[z51,z1,z2,z995,z5,z6]),(0,[z1,z2,z358,z4,z220,z6]),(0,[z1,z2,z8,z735,z175,z6])]],
   [[(0,[z2,z76,z348,z4,z5,z6]),(0,[z14,z2,z8,z111,z5,z6]),(0,[z1,z2,z1151,z4,z5,z6]),(0,[z1,z1152,z4,z5,z6,z28])],[(0,[z196,z2,z8,z4,z5,z6]),(0,[z1,z2,z58,z4,z1153,z6]),(0,[z1,z2,z58,z175,z61,z6]),(0,[z2,z279,z233,z4,z5,z6])],[(0,[z1,z2,z1154,z4,z5,z6]),(0,[z1,z2,z498,z4,z5,z75]),(0,[z1,z2,z329,z222,z5,z6]),(0,[z1,z2,z8,z70,z6,z85])],[(0,[z121,z71,z8,z4,z255,z6]),(0,[z1,z2,z1155,z4,z5,z6]),(0,[z15,z49,z76,z4,z5,z6]),(0,[z2,z76,z4,z5,z432,z6]),(0,[z195,z2,z76,z4,z5,z6]),(0,[z397,z1,z248,z4,z5,z6]),(0,[z1,z2,z1156,z4,z5,z6]),(0,[z122,z36,z173,z4,z5,z6]),(0,[z1,z2,z8,z735,z4,z6]),(0,[z1,z1157,z8,z4,z5,z6]),(0,[z1,z2,z928,z4,z5,z6]),(0,[z1,z2,z8,z157,z243,z6])],[(0,[z15,z121,z3,z4,z5,z6]),(0,[z1,z2,z248,z4,z5,z6]),(0,[z1,z2,z126,z300,z5,z6]),(0,[z1,z2,z1158,z4,z5,z6]),(0,[z195,z2,z8,z4,z567,z6]),(0,[z1159,z2,z8,z4,z5,z6]),(0,[z2,z8,z1160,z4,z5,z6])],[(0,[z1,z2,z1161,z4,z5,z6]),(0,[z1,z52,z59,z4,z5,z6]),(0,[z1,z718,z8,z4,z5,z6]),(0,[z1162,z2,z173,z4,z5,z6]),(0,[z1,z2,z222,z4,z220,z6]),(0,[z343,z67,z8,z4,z5,z6])],[(0,[z1,z2,z76,z4,z284,z6]),(0,[z313,z2,z76,z4,z5,z6]),(0,[z1,z2,z1163,z4,z5,z6]),(0,[z1,z2,z1164,z4,z5,z6]),(0,[z1,z2,z8,z4,z1165,z6])],[(0,[z1,z2,z1166,z4,z5,z6]),(0,[z2,z76,z4,z5,z436,z6]),(0,[z1,z2,z76,z856,z5,z6]),(0,[z1,z1167,z8,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z91]),(0,[z1,z2,z271,z4,z373,z6]),(0,[z1,z2,z34,z4,z5,z6]),(0,[z46,z1,z2,z21,z5,z6]),(0,[z1,z1168,z8,z4,z5,z6]),(0,[z1169,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z1170,z5,z6]),(1,[z15,z249,z4,z5,z6]),(0,[z90,z2,z173,z4,z5,z6]),(0,[z1,z2,z76,z96,z5,z6]),(0,[z483,z2,z58,z4,z5,z6]),(0,[z37,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1171,z6]),(0,[z1,z2,z1172,z4,z5,z6])],[(0,[z1,z225,z58,z4,z5,z6]),(0,[z1,z8,z1173,z4,z5,z6]),(0,[z1174,z2,z8,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z669]),(0,[z1,z2,z36,z243,z5,z6]),(0,[z1,z2,z36,z242,z5,z6])],[(0,[z221,z2,z8,z38,z5,z6]),(0,[z1,z1175,z8,z4,z5,z6]),(0,[z1,z325,z8,z111,z5,z6]),(0,[z1,z2,z8,z79,z5,z6]),(0,[z1,z2,z8,z129,z507,z6]),(0,[z1,z569,z8,z96,z5,z6])],[(0,[z552,z1,z76,z4,z5,z6]),(0,[z1,z2,z1176,z4,z5,z6]),(0,[z1,z2,z1177,z4,z5,z6]),(0,[z1,z325,z8,z4,z116,z6]),(0,[z1,z174,z249,z4,z5,z6]),(0,[z131,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z242,z5,z6]),(0,[z1178,z2,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z1179,z6]),(0,[z1,z2,z167,z4,z5,z6]),(0,[z1180,z2,z8,z4,z5,z6]),(0,[z1181,z2,z8,z4,z5,z6])],[(0,[z650,z1,z2,z8,z5,z85]),(0,[z1,z2,z1182,z4,z5,z6]),(0,[z1,z2,z34,z4,z70,z6]),(0,[z1,z2,z1183,z4,z5,z6])],[(0,[z1,z2,z76,z4,z873,z6]),(0,[z1,z2,z58,z157,z4,z6]),(0,[z1,z2,z333,z111,z5,z6]),(0,[z0,z1,z894,z4,z5,z6]),(0,[z1,z2,z1184,z4,z5,z6]),(0,[z136,z8,z72,z4,z5,z6]),(0,[z1,z2,z20,z4,z44,z6]),(0,[z37,z2,z8,z4,z70,z6]),(0,[z1,z569,z403,z4,z5,z6])],[(0,[z1185,z1,z8,z4,z5,z6]),(0,[z22,z2,z8,z4,z829,z6]),(0,[z1,z2,z333,z4,z116,z6]),(1,[z229,z3,z4,z5,z6]),(0,[z1,z302,z3,z4,z5,z6]),(0,[z10,z1,z2,z4,z507,z53])]],
   [[(0,[z374,z49,z8,z4,z5,z6]),(0,[z2,z76,z4,z447,z5,z6]),(0,[z657,z1,z3,z4,z5,z6]),(0,[z1,z3,z120,z4,z5,z6]),(0,[z209,z2,z173,z4,z5,z6]),(0,[z1,z128,z8,z4,z507,z6])],[(0,[z217,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z4,z11,z6]),(0,[z2,z173,z215,z4,z5,z6]),(0,[z1,z2,z8,z4,z97,z6]),(0,[z37,z2,z8,z19,z5,z6])],[(0,[z221,z2,z76,z4,z5,z6]),(0,[z1,z174,z59,z4,z5,z6]),(0,[z1,z2,z8,z1186,z5,z6]),(0,[z423,z1,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z1053,z6]),(0,[z1,z2,z8,z4,z1187,z6]),(0,[z2,z20,z475,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z431])],[(0,[z1,z2,z8,z4,z255,z6]),(0,[z2,z71,z249,z4,z5,z6]),(0,[z2,z1140,z76,z4,z5,z6]),(0,[z1,z1188,z8,z4,z5,z6]),(0,[z1,z59,z4,z5,z158,z6]),(0,[z1,z2,z1189,z4,z5,z6]),(0,[z1,z36,z3,z4,z5,z6]),(0,[z1190,z2,z8,z4,z5,z6]),(0,[z1191,z2,z8,z4,z5,z6]),(0,[z145,z2,z8,z4,z507,z6]),(0,[z225,z8,z233,z4,z5,z6])],[(0,[z1,z2,z58,z243,z5,z6]),(0,[z1,z2,z58,z242,z5,z6]),(0,[z1,z383,z8,z4,z56,z6]),(0,[z259,z2,z36,z4,z5,z6]),(0,[z1,z2,z36,z260,z5,z6]),(0,[z1,z36,z548,z4,z5,z6]),(0,[z301,z1,z8,z105,z5,z6])],[(0,[z2,z368,z4,z5,z6,z102]),(0,[z315,z2,z76,z4,z5,z6]),(0,[z22,z434,z8,z4,z5,z6]),(0,[z88,z2,z8,z4,z285,z102]),(0,[z1192,z2,z8,z4,z5,z6]),(0,[z2,z173,z72,z4,z5,z6]),(0,[z1,z2,z36,z4,z1193,z6])],[(0,[z273,z2,z76,z4,z5,z6]),(0,[z30,z1,z376,z4,z5,z31]),(0,[z1,z1194,z8,z4,z5,z6])],[(0,[z1195,z2,z3,z4,z5,z6]),(0,[z2,z8,z1196,z4,z5,z6]),(0,[z1,z1197,z8,z4,z5,z6]),(0,[z1,z569,z1040,z4,z5,z6])],[(0,[z462,z2,z8,z4,z23,z6]),(0,[z1,z325,z139,z4,z5,z6]),(0,[z1,z2,z8,z1198,z5,z6]),(0,[z1,z2,z1199,z4,z5,z6]),(0,[z1,z81,z8,z4,z5,z535]),(0,[z1,z2,z4,z5,z6,z1200]),(0,[z1201,z2,z8,z4,z5,z6]),(0,[z1,z1202,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1203])],[(0,[z89,z2,z76,z4,z5,z102]),(0,[z2,z76,z4,z458,z5,z6]),(0,[z1,z76,z4,z5,z6,z84]),(0,[z1,z2,z8,z4,z5,z1204]),(0,[z7,z383,z8,z9,z5,z6]),(0,[z1,z3,z4,z5,z6,z134]),(0,[z1205,z2,z8,z4,z5,z6]),(0,[z2,z8,z157,z4,z6,z92])],[(0,[z1,z2,z906,z4,z5,z6]),(0,[z2,z8,z9,z4,z109,z6])],[(0,[z1,z81,z354,z4,z5,z6]),(0,[z1,z2,z1206,z4,z5,z6]),(0,[z539,z2,z76,z4,z5,z6]),(0,[z1,z402,z8,z4,z285,z6]),(0,[z2,z144,z475,z222,z5,z6]),(0,[z1,z2,z8,z157,z61,z6])],[(0,[z1,z2,z58,z1207,z5,z6]),(0,[z7,z2,z173,z4,z5,z6]),(0,[z1,z94,z8,z4,z5,z6])],[(0,[z1,z2,z1208,z4,z5,z6]),(0,[z1,z3,z4,z5,z142,z6]),(0,[z2,z173,z73,z4,z5,z6]),(0,[z51,z1,z2,z490,z5,z6]),(0,[z1,z2,z1209,z4,z5,z6])],[(0,[z2,z8,z9,z4,z285,z6]),(0,[z1,z2,z8,z4,z13,z654]),(0,[z88,z2,z8,z111,z5,z102]),(0,[z301,z1,z3,z4,z5,z6]),(0,[z1,z122,z155,z4,z5,z6])],[(0,[z2,z76,z461,z4,z5,z6]),(0,[z1210,z1,z8,z4,z5,z6]),(0,[z1,z2,z8,z1211,z5,z6]),(0,[z259,z2,z58,z4,z5,z6]),(0,[z1,z2,z58,z260,z5,z6]),(0,[z397,z1,z8,z4,z56,z6]),(0,[z2,z173,z4,z5,z100,z6]),(0,[z1,z2,z8,z1212,z4,z6]),(0,[z104,z1,z117,z4,z5,z6]),(0,[z1,z8,z4,z5,z18,z809]),(1,[z1,z2,z8,z4,z1009])]],
   [[(0,[z1,z977,z338,z4,z5,z6]),(0,[z1,z2,z20,z4,z738,z6])],[(0,[z1,z58,z834,z4,z5,z6]),(0,[z1,z2,z20,z4,z95,z6]),(0,[z1,z2,z1213,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z151]),(0,[z1,z2,z8,z4,z6,z1214]),(0,[z1215,z2,z8,z4,z5,z6])],[(0,[z250,z2,z8,z4,z5,z6]),(0,[z2,z1216,z173,z4,z5,z6]),(0,[z1,z2,z8,z4,z936,z6]),(0,[z259,z2,z83,z4,z5,z6]),(0,[z1,z2,z83,z260,z5,z6]),(0,[z1,z2,z1217,z4,z5,z6]),(0,[z32,z2,z8,z73,z12,z6]),(0,[z1,z94,z8,z4,z70,z6])],[(0,[z47,z2,z55,z4,z5,z6]),(0,[z185,z1,z59,z4,z5,z6]),(0,[z136,z2,z8,z4,z388,z6]),(0,[z1218,z2,z8,z4,z5,z6]),(0,[z10,z2,z118,z4,z5,z6])],[(0,[z1,z274,z3,z4,z5,z6]),(0,[z280,z323,z8,z4,z5,z6])],[(0,[z1,z2,z1219,z4,z5,z6]),(0,[z2,z76,z4,z5,z6,z468]),(0,[z7,z2,z8,z9,z5,z6]),(0,[z1,z3,z693,z4,z5,z6]),(0,[z1,z2,z1220,z4,z5,z6]),(0,[z1,z94,z8,z19,z5,z6])],[(0,[z2,z8,z173,z4,z5,z6]),(0,[z1,z122,z368,z4,z5,z6]),(0,[z1,z174,z3,z4,z5,z6]),(0,[z51,z1,z2,z21,z5,z6]),(0,[z1,z201,z4,z5,z75,z6])],[(0,[z1,z17,z76,z4,z5,z6]),(0,[z1,z1221,z8,z4,z5,z6]),(0,[z1,z3,z4,z5,z24,z6])],[(0,[z1,z2,z1222,z4,z5,z6]),(0,[z32,z2,z8,z4,z5,z6]),(0,[z1,z2,z1223,z4,z5,z6]),(0,[z30,z1,z8,z4,z5,z31]),(0,[z1,z2,z1224,z4,z5,z6])],[(0,[z1,z2,z76,z4,z1091,z6]),(0,[z1,z2,z894,z4,z5,z6]),(0,[z1,z2,z1225,z4,z5,z6]),(0,[z1,z81,z8,z4,z5,z809])],[(0,[z2,z257,z76,z4,z5,z6]),(0,[z1,z63,z59,z4,z5,z6]),(0,[z1,z2,z1226,z4,z5,z6]),(0,[z195,z81,z8,z4,z5,z6]),(0,[z1,z2,z34,z4,z294,z6]),(0,[z1,z2,z525,z96,z5,z6])],[(0,[z1,z434,z384,z4,z5,z6]),(0,[z1,z2,z1227,z4,z5,z6]),(0,[z217,z2,z967,z4,z5,z6]),(0,[z1228,z2,z8,z4,z5,z6]),(0,[z37,z2,z8,z4,z294,z6])],[(0,[z22,z2,z76,z4,z5,z6]),(0,[z88,z2,z139,z4,z5,z102]),(0,[z1,z117,z4,z5,z6,z31]),(0,[z1,z1229,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1230,z6])],[(0,[z626,z2,z76,z4,z5,z6]),(0,[z1,z59,z4,z5,z6,z28]),(0,[z1,z2,z1231,z4,z5,z6]),(0,[z51,z1,z128,z4,z5,z6]),(0,[z1,z8,z1232,z4,z5,z6])],[(0,[z2,z58,z4,z5,z6,z92]),(0,[z1,z2,z1233,z4,z5,z6]),(0,[z1,z2,z269,z4,z388,z6]),(0,[z195,z2,z1004,z4,z5,z6]),(0,[z1,z2,z1234,z4,z5,z6])],[(0,[z1,z2,z55,z4,z5,z6]),(0,[z88,z1,z59,z4,z5,z6]),(0,[z1,z1167,z147,z4,z5,z6]),(0,[z81,z2,z173,z4,z5,z6]),(0,[z1,z2,z1071,z4,z5,z6]),(0,[z196,z267,z8,z4,z5,z6])]],
   [[(0,[z1,z58,z59,z4,z5,z6]),(0,[z1235,z1,z8,z4,z5,z6]),(0,[z104,z2,z173,z4,z5,z6]),(0,[z136,z2,z167,z4,z5,z6]),(0,[z1,z1236,z8,z4,z5,z6]),(0,[z46,z1,z2,z4,z6,z212])],[(0,[z2,z76,z4,z5,z476,z6]),(0,[z250,z2,z4,z5,z6,z219]),(0,[z2,z749,z8,z4,z5,z6])],[(0,[z433,z1,z3,z4,z5,z6]),(0,[z1,z2,z1237,z4,z5,z6]),(0,[z1238,z1,z2,z4,z5,z6]),(0,[z254,z2,z8,z4,z23,z6]),(0,[z1,z67,z8,z4,z5,z6]),(0,[z33,z1,z2,z303,z5,z85]),(0,[z27,z1,z2,z525,z4,z28])],[(0,[z1,z1122,z76,z4,z5,z6]),(0,[z1,z201,z36,z4,z5,z6]),(0,[z10,z1,z2,z4,z11,z53])],[(0,[z1,z2,z1239,z4,z5,z6]),(0,[z2,z1240,z36,z4,z5,z6]),(0,[z1,z437,z36,z4,z5,z6]),(0,[z821,z2,z8,z4,z5,z6]),(0,[z10,z145,z2,z4,z5,z53]),(0,[z1,z1241,z8,z4,z5,z6])],[(0,[z1,z2,z76,z129,z5,z6]),(0,[z1,z325,z36,z4,z5,z6]),(0,[z1,z201,z3,z4,z5,z6]),(0,[z1242,z2,z8,z4,z5,z6]),(0,[z1,z2,z222,z4,z11,z6]),(0,[z33,z202,z2,z8,z5,z85])],[(0,[z1,z2,z52,z4,z5,z247]),(0,[z367,z1,z2,z4,z5,z380]),(0,[z1243,z2,z8,z4,z5,z6])],[(0,[z1,z2,z1244,z4,z5,z6]),(0,[z47,z2,z8,z111,z5,z6]),(0,[z1,z174,z117,z4,z65,z6]),(0,[z8,z475,z274,z4,z5,z6])],[(0,[z444,z71,z8,z4,z5,z6]),(0,[z2,z354,z9,z4,z5,z6]),(0,[z387,z2,z76,z4,z5,z6]),(0,[z1,z2,z1245,z4,z5,z6]),(0,[z1,z8,z775,z4,z5,z6]),(0,[z1,z3,z39,z4,z5,z6]),(0,[z104,z1,z8,z236,z5,z6]),(0,[z252,z2,z8,z4,z177,z6]),(0,[z1,z174,z133,z4,z5,z6]),(0,[z365,z2,z1151,z4,z5,z6])],[(0,[z1,z2,z1246,z4,z5,z6]),(0,[z1,z894,z3,z4,z5,z6]),(0,[z1,z3,z4,z24,z6,z28]),(0,[z1,z3,z4,z43,z5,z6]),(0,[z1,z2,z36,z175,z61,z6]),(0,[z1247,z2,z8,z4,z5,z6]),(0,[z2,z63,z118,z4,z5,z6]),(0,[z8,z4,z5,z6,z84,z92])],[(0,[z1,z2,z897,z4,z5,z6]),(0,[z1,z2,z1248,z4,z5,z6]),(0,[z1,z2,z8,z1249,z5,z6])],[(0,[z1,z128,z76,z4,z5,z6]),(0,[z1,z3,z4,z48,z5,z6]),(0,[z64,z2,z8,z4,z5,z102]),(0,[z1,z2,z3,z175,z61,z6]),(0,[z1250,z2,z8,z4,z5,z6]),(0,[z174,z2,z756,z4,z5,z6]),(0,[z1,z1251,z8,z4,z5,z6]),(0,[z33,z1,z2,z34,z5,z85]),(0,[z1,z2,z1252,z4,z5,z6])],[(0,[z1,z1253,z59,z4,z5,z6]),(0,[z1,z59,z4,z5,z6,z509]),(0,[z1,z2,z1254,z4,z5,z6]),(0,[z1,z267,z20,z4,z44,z6])],[(0,[z2,z8,z76,z4,z284,z6]),(0,[z2,z501,z8,z4,z42,z6]),(0,[z1,z323,z58,z4,z5,z6]),(0,[z1,z2,z8,z832,z5,z6]),(0,[z1,z2,z1255,z4,z5,z6]),(0,[z1,z2,z4,z5,z1256,z6]),(0,[z51,z1,z2,z456,z5,z6]),(0,[z2,z118,z4,z5,z44,z6]),(0,[z33,z2,z8,z5,z92,z85]),(0,[z27,z1,z323,z8,z4,z28])],[(1,[z2,z708,z4,z5,z6]),(0,[z145,z2,z76,z4,z5,z6]),(0,[z1,z2,z1257,z4,z5,z6]),(0,[z374,z1,z3,z4,z5,z6]),(0,[z1,z197,z3,z4,z5,z6])],[(0,[z1,z2,z1258,z4,z5,z6]),(0,[z1,z135,z76,z72,z5,z6]),(0,[z1,z434,z8,z4,z23,z6]),(0,[z1,z94,z8,z4,z294,z6]),(0,[z1,z2,z403,z96,z5,z6])]],
   [[(0,[z229,z2,z8,z4,z5,z6]),(0,[z1,z2,z76,z4,z109,z6]),(0,[z1,z325,z58,z4,z5,z6]),(0,[z1,z1259,z8,z4,z5,z6]),(0,[z1,z190,z3,z4,z5,z6]),(0,[z22,z2,z346,z4,z23,z6]),(0,[z1,z1260,z8,z4,z5,z6])],[(0,[z1,z2,z1261,z4,z5,z6]),(0,[z2,z8,z4,z5,z100,z783]),(0,[z1,z225,z36,z4,z5,z6]),(0,[z104,z1,z8,z105,z5,z6]),(0,[z135,z136,z8,z72,z5,z6]),(0,[z1,z2,z1262,z4,z5,z6])],[(0,[z49,z1,z8,z4,z284,z6]),(0,[z121,z1,z249,z4,z5,z6]),(0,[z1,z2,z238,z4,z5,z6]),(0,[z2,z368,z4,z5,z42,z6]),(0,[z1,z59,z4,z520,z5,z6]),(0,[z1,z2,z8,z1263,z4,z6]),(0,[z1,z81,z8,z4,z97,z6]),(0,[z1,z2,z8,z4,z1264,z6])],[(0,[z1,z2,z1265,z4,z5,z6]),(0,[z1,z2,z8,z111,z5,z6]),(0,[z1,z225,z3,z4,z5,z6]),(0,[z37,z2,z303,z4,z5,z6])],[(0,[z50,z58,z59,z4,z5,z6]),(0,[z1,z2,z8,z4,z116,z6]),(0,[z217,z2,z8,z4,z65,z6]),(0,[z259,z2,z8,z260,z5,z6]),(0,[z2,z8,z1266,z4,z5,z6]),(0,[z1,z569,z1002,z4,z5,z6])],[(0,[z1,z58,z548,z4,z5,z6]),(0,[z1,z455,z36,z4,z5,z6]),(0,[z1267,z2,z8,z4,z5,z6]),(0,[z27,z1,z2,z4,z203,z28])],[(0,[z1,z2,z36,z157,z4,z6]),(0,[z10,z1,z2,z4,z5,z151]),(0,[z1,z2,z4,z5,z75,z932]),(0,[z1,z2,z1268,z4,z5,z6]),(0,[z202,z2,z1269,z4,z5,z6])],[(0,[z2,z624,z58,z4,z5,z6])],[(0,[z252,z2,z8,z4,z5,z6]),(0,[z1,z402,z1270,z4,z5,z6]),(0,[z1,z2,z3,z157,z4,z6]),(0,[z1026,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z378]),(0,[z1,z40,z8,z4,z114,z6])],[(0,[z121,z1,z59,z4,z5,z6]),(0,[z234,z2,z8,z9,z5,z6]),(0,[z22,z2,z368,z4,z5,z6]),(0,[z47,z2,z76,z4,z5,z100]),(0,[z666,z1,z3,z4,z5,z6]),(0,[z32,z2,z792,z4,z5,z6])],[(0,[z1,z2,z1271,z4,z5,z6]),(0,[z1,z3,z210,z4,z5,z6]),(0,[z1,z2,z8,z1272,z5,z6]),(0,[z50,z2,z58,z4,z5,z6]),(0,[z1,z2,z36,z1273,z5,z6]),(0,[z1,z2,z4,z1274,z5,z6]),(0,[z1,z2,z1275,z4,z5,z6])],[(0,[z22,z2,z354,z4,z5,z6])],[(0,[z2,z76,z4,z5,z6,z509]),(0,[z343,z2,z58,z4,z5,z6]),(0,[z1,z135,z8,z562,z5,z6]),(0,[z30,z259,z8,z4,z5,z31]),(0,[z1,z2,z4,z5,z6,z1276])],[],[(0,[z1,z2,z1277,z4,z5,z6]),(0,[z1,z2,z199,z4,z16,z6]),(0,[z196,z2,z76,z4,z5,z6]),(0,[z1,z20,z59,z4,z5,z6]),(0,[z2,z390,z4,z5,z42,z6]),(0,[z1,z2,z3,z243,z5,z6]),(0,[z1,z94,z831,z4,z5,z6])],[(0,[z2,z173,z76,z4,z5,z6]),(0,[z1,z59,z4,z38,z5,z6]),(0,[z1,z3,z215,z4,z5,z6]),(0,[z2,z36,z233,z4,z5,z6]),(1,[z2,z755,z4,z5,z6]),(0,[z209,z487,z8,z4,z24,z6]),(0,[z1278,z2,z8,z4,z5,z6]),(1,[z2,z756,z4,z5,z6])]],
   [[(0,[z1,z166,z36,z4,z5,z6]),(0,[z2,z368,z9,z4,z5,z6]),(0,[z22,z2,z173,z4,z5,z6]),(0,[z1,z498,z3,z4,z5,z31]),(0,[z1,z2,z1279,z4,z5,z6])],[(0,[z2,z879,z76,z4,z5,z6]),(0,[z485,z1,z3,z4,z5,z6]),(0,[z1,z2,z139,z4,z5,z6]),(0,[z30,z1,z8,z4,z5,z809]),(0,[z1,z8,z1280,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z1281])],[(0,[z90,z1,z59,z4,z5,z6]),(0,[z1,z2,z8,z127,z285,z6]),(0,[z1,z2,z1282,z4,z5,z6]),(0,[z579,z1,z2,z8,z4,z28]),(0,[z1238,z2,z4,z5,z6,z92]),(0,[z27,z1,z569,z8,z4,z28])],[(0,[z1,z3,z72,z4,z5,z6]),(0,[z1,z438,z3,z4,z5,z6]),(0,[z1,z2,z1013,z4,z5,z6]),(0,[z1,z2,z853,z4,z5,z6])],[(0,[z88,z2,z58,z4,z5,z102]),(0,[z1,z2,z8,z915,z5,z6]),(0,[z1,z2,z8,z19,z5,z467]),(0,[z1,z67,z8,z4,z507,z6])],[(0,[z37,z2,z76,z4,z5,z6]),(0,[z1,z76,z274,z4,z5,z6]),(0,[z50,z2,z103,z4,z5,z6]),(0,[z47,z2,z8,z4,z5,z480]),(0,[z1,z1283,z8,z4,z5,z6]),(0,[z1,z2,z8,z1047,z5,z6]),(0,[z1,z8,z72,z5,z6,z582]),(0,[z51,z1,z2,z4,z220,z6])],[(0,[z121,z1,z1284,z4,z5,z6]),(0,[z1,z2,z8,z4,z1285,z6]),(0,[z1,z174,z8,z4,z589,z6]),(0,[z49,z311,z8,z4,z5,z6]),(0,[z211,z2,z76,z4,z5,z6]),(0,[z1,z2,z1286,z4,z5,z6]),(0,[z1,z2,z8,z4,z1080,z6]),(0,[z22,z2,z384,z4,z5,z6]),(0,[z1,z174,z3,z4,z24,z6]),(0,[z1,z2,z232,z4,z74,z6]),(0,[z552,z1,z8,z72,z5,z6]),(0,[z1287,z1,z8,z4,z5,z6])],[(0,[z2,z1288,z76,z4,z5,z6]),(0,[z1,z2,z76,z79,z5,z6]),(0,[z1,z126,z59,z4,z5,z6]),(0,[z560,z1,z2,z4,z5,z53]),(0,[z1,z8,z1289,z4,z5,z6]),(0,[z25,z40,z8,z4,z5,z6]),(0,[z10,z1,z2,z129,z5,z53]),(0,[z1,z94,z303,z4,z5,z6]),(0,[z1,z323,z8,z243,z5,z6])],[(0,[z104,z1,z8,z304,z5,z6]),(0,[z187,z1,z2,z21,z5,z6]),(0,[z1,z2,z8,z4,z1290,z6]),(0,[z1,z2,z1291,z4,z5,z6]),(0,[z1,z249,z4,z5,z6,z31]),(0,[z1,z8,z160,z72,z5,z6]),(0,[z1,z2,z8,z79,z567,z6])],[(0,[z121,z2,z76,z4,z284,z6]),(0,[z2,z76,z4,z5,z6,z529]),(0,[z1,z2,z132,z4,z95,z6]),(0,[z202,z2,z8,z4,z5,z6]),(0,[z1,z171,z360,z4,z5,z6]),(0,[z259,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z260,z5,z6]),(0,[z209,z1,z36,z4,z24,z6]),(0,[z1,z2,z1292,z4,z5,z6]),(0,[z2,z1293,z8,z4,z5,z6]),(0,[z1,z2,z222,z129,z5,z6]),(0,[z1,z2,z290,z4,z74,z6])],[(0,[z2,z228,z76,z4,z5,z6]),(0,[z1,z59,z4,z5,z6,z85]),(0,[z209,z1,z59,z4,z5,z6]),(0,[z397,z7,z8,z9,z5,z6]),(0,[z280,z2,z8,z175,z4,z6]),(0,[z250,z552,z8,z4,z5,z6])],[(0,[z1,z2,z1294,z4,z5,z6]),(0,[z2,z76,z4,z5,z6,z533]),(0,[z418,z2,z8,z38,z5,z6]),(0,[z1,z2,z8,z4,z114,z6]),(0,[z1,z2,z1295,z4,z5,z6])],[(0,[z121,z122,z76,z4,z5,z6]),(0,[z1,z3,z72,z19,z5,z6]),(0,[z1195,z2,z8,z4,z5,z6]),(0,[z2,z20,z118,z4,z44,z6])],[(0,[z121,z1,z3,z4,z5,z6]),(0,[z761,z2,z8,z4,z5,z6]),(0,[z2,z76,z4,z5,z6,z534]),(0,[z1,z2,z1094,z4,z5,z6]),(0,[z1,z2,z1296,z4,z5,z6]),(0,[z1,z2,z1297,z4,z5,z6]),(0,[z1298,z2,z8,z4,z5,z6]),(1,[z1,z2,z995,z5,z6])],[(0,[z50,z2,z130,z4,z5,z6]),(0,[z1,z2,z76,z4,z97,z6]),(0,[z1,z2,z8,z4,z1299,z6]),(0,[z1,z2,z58,z4,z1300,z6]),(0,[z1,z2,z257,z4,z5,z247]),(0,[z110,z2,z360,z4,z42,z6]),(0,[z2,z8,z4,z23,z829,z6]),(0,[z1,z2,z36,z4,z177,z6]),(0,[z1,z8,z4,z5,z6,z1301]),(0,[z1,z8,z1302,z4,z5,z6])],[(0,[z1,z2,z1303,z4,z5,z6]),(0,[z2,z248,z4,z5,z6,z102]),(0,[z1304,z1,z2,z4,z5,z6]),(1,[z1,z1063,z4,z5,z6]),(0,[z487,z2,z1182,z4,z5,z6]),(0,[z1,z128,z222,z4,z5,z6]),(0,[z202,z2,z8,z4,z70,z6])]],
   [[(0,[z1,z2,z76,z4,z255,z6]),(0,[z1,z1188,z76,z4,z5,z6]),(0,[z2,z8,z4,z829,z42,z6]),(0,[z280,z2,z8,z4,z5,z6]),(0,[z1,z2,z1305,z4,z5,z6]),(0,[z1,z2,z8,z1306,z4,z6])],[(0,[z1307,z1,z2,z4,z5,z6]),(0,[z1,z2,z8,z4,z1308,z6]),(0,[z22,z2,z390,z4,z5,z6]),(0,[z1,z174,z36,z4,z65,z6]),(0,[z1,z2,z8,z4,z13,z429]),(0,[z250,z2,z1309,z4,z5,z6])],[(0,[z1,z101,z3,z4,z5,z6]),(0,[z2,z708,z76,z4,z5,z6]),(0,[z1,z383,z36,z4,z5,z6]),(0,[z88,z2,z8,z4,z116,z102]),(0,[z1,z641,z3,z4,z5,z6]),(0,[z1,z2,z1310,z4,z5,z6]),(0,[z2,z8,z475,z4,z114,z6]),(0,[z145,z2,z222,z4,z5,z6])],[(0,[z418,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z56,z6]),(1,[z1,z906,z4,z5,z6])],[(0,[z1,z171,z8,z4,z5,z6]),(0,[z406,z2,z76,z4,z5,z6]),(0,[z209,z1,z58,z4,z24,z6]),(0,[z1,z383,z3,z4,z5,z6]),(0,[z2,z8,z9,z832,z5,z6]),(0,[z1,z1311,z8,z4,z5,z6])],[],[(0,[z7,z1,z59,z4,z5,z6]),(0,[z1312,z2,z36,z4,z5,z6]),(0,[z343,z2,z8,z242,z5,z6]),(0,[z1,z1313,z8,z4,z5,z6]),(0,[z1,z2,z1314,z4,z5,z6])],[(0,[z1,z2,z8,z1315,z5,z6]),(0,[z2,z76,z4,z5,z547,z6]),(0,[z1,z1316,z103,z4,z5,z6]),(0,[z1,z402,z8,z111,z5,z6]),(0,[z1,z2,z1270,z4,z5,z6]),(0,[z209,z1,z82,z4,z24,z6]),(0,[z1,z67,z307,z4,z5,z6])],[(0,[z14,z15,z3,z4,z5,z6]),(0,[z1,z1317,z8,z4,z5,z6]),(0,[z1,z402,z8,z4,z116,z6]),(0,[z1,z2,z36,z73,z12,z6]),(0,[z182,z1,z8,z4,z24,z6]),(0,[z1,z2,z20,z4,z220,z6]),(0,[z1,z2,z8,z175,z243,z6])],[(0,[z1,z94,z76,z4,z5,z6]),(0,[z1,z2,z1318,z4,z5,z6]),(0,[z1,z2,z58,z4,z177,z6]),(0,[z110,z2,z8,z4,z42,z6]),(0,[z1,z2,z1319,z4,z5,z6]),(0,[z1,z2,z1320,z4,z5,z6]),(0,[z1321,z2,z8,z4,z5,z6])],[(0,[z25,z2,z8,z4,z5,z6]),(0,[z2,z8,z9,z111,z5,z6]),(0,[z22,z2,z8,z4,z23,z6]),(0,[z2,z173,z4,z105,z5,z6]),(0,[z2,z52,z173,z4,z5,z6]),(0,[z1,z8,z4,z388,z6,z31]),(0,[z1,z2,z4,z5,z6,z932]),(0,[z27,z1,z2,z8,z4,z28])],[(0,[z1,z3,z262,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z84])],[(0,[z14,z2,z8,z261,z5,z6]),(0,[z1,z174,z58,z4,z65,z6]),(0,[z1,z2,z1322,z4,z5,z6]),(0,[z1,z94,z8,z5,z6,z85])],[(0,[z1,z383,z58,z4,z5,z6]),(0,[z1,z2,z1323,z4,z5,z6]),(0,[z397,z1,z36,z4,z5,z6]),(0,[z1,z1324,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1325])],[(0,[z1,z1157,z358,z4,z5,z6])],[(0,[z1,z2,z8,z1326,z5,z6]),(0,[z250,z2,z76,z4,z5,z6]),(0,[z1,z2,z1327,z4,z5,z6])]],
   [[(0,[z1,z2,z1328,z4,z5,z6]),(0,[z1,z2,z8,z4,z1329,z6]),(0,[z1,z2,z8,z4,z1330,z6]),(0,[z49,z174,z76,z4,z5,z6]),(0,[z1,z2,z1331,z4,z5,z6]),(0,[z492,z1,z3,z4,z5,z6]),(0,[z1,z434,z1139,z4,z5,z6]),(0,[z2,z173,z4,z5,z373,z6]),(0,[z1,z2,z8,z175,z702,z6])],[(0,[z49,z1,z368,z4,z5,z6]),(0,[z1,z1332,z58,z4,z5,z6]),(0,[z397,z1,z1333,z4,z5,z6]),(0,[z1,z2,z1334,z4,z5,z6]),(0,[z1,z2,z8,z129,z11,z6])],[(0,[z1,z2,z1333,z4,z5,z6]),(0,[z1,z269,z4,z5,z6,z31]),(0,[z1,z2,z8,z1335,z5,z6]),(0,[z1,z2,z8,z556,z12,z6])],[(0,[z1,z2,z58,z73,z12,z6]),(0,[z1,z2,z1336,z4,z5,z6]),(0,[z104,z1,z249,z4,z5,z6]),(0,[z2,z173,z173,z4,z5,z6]),(0,[z2,z173,z222,z4,z5,z6]),(0,[z30,z1,z8,z4,z5,z449]),(0,[z1,z81,z8,z4,z388,z6]),(0,[z1,z201,z4,z5,z44,z6])],[(0,[z49,z121,z76,z4,z5,z6]),(0,[z452,z2,z76,z4,z5,z6]),(0,[z1337,z2,z8,z4,z5,z6])],[(0,[z1,z3,z4,z5,z284,z6]),(0,[z32,z2,z76,z4,z5,z6]),(0,[z1,z402,z139,z4,z5,z6]),(0,[z1,z323,z36,z4,z5,z6]),(0,[z1,z2,z8,z1126,z5,z6]),(0,[z1338,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z1339,z5,z6]),(0,[z250,z2,z8,z4,z6,z212])],[(0,[z1,z2,z1340,z4,z5,z6]),(0,[z1,z216,z4,z5,z24,z6]),(0,[z2,z307,z1125,z4,z5,z6]),(0,[z1,z2,z4,z6,z212,z219])],[(0,[z1,z59,z4,z1341,z5,z6]),(0,[z223,z2,z58,z4,z5,z6]),(0,[z383,z8,z4,z5,z6,z102]),(0,[z1,z2,z4,z5,z6,z1342]),(0,[z1,z323,z3,z4,z5,z6]),(0,[z252,z2,z269,z4,z5,z6]),(0,[z1343,z2,z8,z4,z5,z6]),(0,[z1,z2,z1344,z4,z5,z6]),(1,[z1,z8,z4,z796,z6]),(0,[z1,z201,z144,z4,z5,z6]),(0,[z1,z1345,z8,z4,z5,z6]),(0,[z1,z128,z8,z4,z11,z6]),(0,[z1,z2,z8,z1346,z4,z6]),(0,[z1,z2,z1347,z4,z5,z6]),(0,[z1,z526,z34,z4,z5,z6])],[(0,[z2,z76,z175,z4,z42,z6]),(0,[z397,z1,z58,z4,z5,z6]),(0,[z1,z217,z8,z4,z24,z6]),(0,[z1,z2,z52,z4,z5,z75]),(0,[z37,z526,z8,z4,z5,z6])],[(0,[z1,z2,z58,z4,z5,z6]),(0,[z1348,z2,z8,z4,z5,z6]),(0,[z33,z250,z2,z8,z5,z85])],[(0,[z1,z2,z8,z4,z1349,z6]),(0,[z104,z1,z59,z4,z5,z6]),(0,[z1,z325,z3,z4,z5,z6]),(0,[z145,z2,z8,z4,z11,z6]),(0,[z1,z2,z4,z5,z6,z1350]),(0,[z1,z569,z8,z4,z13,z6])],[(0,[z349,z71,z8,z4,z5,z6]),(0,[z14,z2,z58,z38,z5,z6]),(0,[z2,z173,z4,z23,z5,z6]),(0,[z1,z2,z8,z5,z6,z1351])],[(0,[z121,z340,z8,z4,z5,z6]),(0,[z14,z325,z8,z4,z5,z6]),(0,[z1,z2,z82,z4,z5,z6]),(0,[z1,z2,z83,z4,z5,z6]),(0,[z202,z2,z8,z4,z294,z6])],[(0,[z121,z71,z130,z4,z5,z6]),(0,[z1,z2,z1352,z4,z5,z6]),(0,[z0,z2,z173,z4,z5,z6]),(0,[z1,z2,z545,z4,z44,z6]),(0,[z1,z2,z1353,z4,z5,z6]),(0,[z1,z2,z8,z1354,z4,z6]),(0,[z1,z2,z191,z4,z44,z6])],[(0,[z1,z2,z1140,z4,z5,z6]),(0,[z1,z144,z59,z4,z5,z6]),(0,[z1,z2,z1355,z4,z5,z6]),(0,[z47,z2,z390,z4,z5,z100]),(0,[z1,z81,z8,z79,z5,z6]),(0,[z1,z8,z4,z5,z6,z1356])],[(0,[z1,z71,z59,z4,z5,z6]),(0,[z1,z1357,z8,z4,z5,z6]),(0,[z1,z67,z76,z4,z5,z6]),(0,[z1,z2,z58,z4,z70,z6]),(0,[z1,z1023,z8,z4,z5,z6]),(0,[z1358,z1,z2,z4,z5,z6]),(0,[z2,z1359,z173,z4,z5,z6]),(0,[z1,z2,z1360,z4,z5,z6])]],
   [[(0,[z1,z2,z1361,z4,z5,z6]),(0,[z1,z2,z501,z4,z636,z6]),(0,[z1,z368,z3,z4,z5,z6]),(0,[z1,z59,z175,z4,z5,z6]),(0,[z2,z58,z233,z4,z5,z6]),(0,[z1,z2,z8,z4,z1153,z6]),(0,[z14,z2,z333,z4,z5,z6]),(0,[z1,z2,z3,z1362,z5,z6]),(0,[z1,z2,z8,z1363,z5,z6]),(0,[z32,z8,z548,z4,z5,z6])],[(0,[z1,z2,z1364,z4,z5,z6]),(0,[z1,z2,z1365,z4,z5,z6]),(0,[z1,z8,z4,z5,z796,z6])],[(0,[z121,z2,z55,z4,z5,z6]),(0,[z598,z2,z76,z4,z5,z6]),(0,[z1,z1366,z8,z4,z5,z6])],[(0,[z1,z2,z399,z427,z5,z6]),(0,[z51,z2,z173,z4,z5,z6]),(0,[z104,z195,z8,z4,z5,z6]),(0,[z1,z2,z8,z1367,z5,z6]),(0,[z1,z2,z8,z4,z5,z1368]),(0,[z1,z8,z548,z4,z13,z6]),(0,[z1,z4,z5,z6,z84,z219])],[(0,[z121,z71,z138,z4,z5,z6]),(0,[z1,z2,z103,z4,z5,z6]),(0,[z1,z2,z987,z4,z5,z6]),(0,[z1,z3,z4,z5,z194,z6]),(0,[z1,z2,z216,z4,z5,z6]),(0,[z1,z2,z8,z4,z1144,z6]),(0,[z343,z2,z36,z4,z5,z6]),(0,[z1369,z2,z8,z4,z5,z6]),(0,[z1,z2,z1370,z4,z5,z6]),(1,[z1,z8,z4,z5,z809]),(0,[z554,z2,z475,z4,z5,z6])],[(0,[z195,z2,z8,z79,z5,z6]),(0,[z51,z1,z2,z4,z11,z6]),(0,[z2,z1371,z8,z4,z5,z6]),(0,[z8,z233,z548,z4,z5,z6]),(0,[z1,z2,z749,z4,z5,z6]),(0,[z1,z2,z1372,z4,z5,z6]),(0,[z1,z2,z1373,z4,z5,z6])],[(0,[z343,z2,z3,z4,z5,z6]),(0,[z1,z2,z144,z215,z5,z6]),(0,[z51,z145,z2,z4,z5,z6]),(0,[z2,z8,z73,z12,z233,z6]),(0,[z1,z2,z1374,z4,z5,z6])],[(0,[z121,z76,z354,z4,z5,z6]),(0,[z1,z2,z76,z4,z285,z6]),(0,[z2,z118,z8,z4,z5,z6]),(0,[z1,z2,z117,z4,z5,z6]),(0,[z1,z8,z4,z65,z796,z6])],[(0,[z1,z2,z8,z1375,z5,z6]),(0,[z1,z59,z3,z4,z5,z6]),(0,[z1376,z2,z8,z4,z5,z6]),(0,[z33,z1,z2,z8,z157,z85])],[(0,[z1,z2,z36,z4,z1377,z6]),(0,[z1,z2,z1378,z4,z5,z6])],[(0,[z1,z2,z1379,z4,z5,z6]),(0,[z1,z2,z1380,z4,z5,z6]),(0,[z2,z501,z76,z4,z42,z6]),(0,[z1,z325,z333,z4,z5,z6]),(0,[z1,z81,z8,z4,z5,z608]),(0,[z494,z1,z2,z4,z5,z151]),(0,[z217,z8,z4,z5,z24,z6]),(0,[z46,z1,z2,z129,z5,z6]),(0,[z1381,z2,z8,z4,z5,z6])],[(1,[z71,z8,z4,z284,z6]),(0,[z15,z1,z207,z4,z5,z6]),(0,[z14,z2,z346,z4,z5,z6]),(0,[z1,z3,z73,z4,z24,z6])],[(0,[z1,z2,z1382,z4,z5,z6]),(0,[z1,z2,z1383,z4,z5,z6]),(0,[z88,z2,z36,z4,z5,z102]),(0,[z195,z2,z8,z4,z97,z6]),(0,[z259,z2,z376,z4,z5,z6]),(0,[z1,z2,z376,z260,z5,z6]),(0,[z2,z475,z4,z5,z6,z53]),(0,[z1,z8,z73,z12,z548,z6])],[(0,[z1,z2,z130,z4,z5,z6]),(0,[z15,z152,z8,z4,z5,z6]),(0,[z229,z2,z76,z4,z5,z6]),(0,[z552,z1,z8,z79,z5,z6]),(0,[z33,z1,z8,z5,z84,z85]),(0,[z27,z1,z2,z8,z96,z28])],[(1,[z434,z8,z4,z42,z6]),(0,[z2,z8,z4,z42,z6,z327]),(0,[z88,z2,z3,z4,z5,z102]),(0,[z104,z1,z3,z4,z5,z6]),(0,[z785,z2,z36,z4,z5,z6]),(0,[z1,z1384,z8,z4,z5,z6])],[(0,[z1,z2,z76,z4,z388,z6]),(0,[z1,z1052,z8,z4,z5,z6]),(0,[z1,z2,z1385,z4,z5,z6]),(0,[z1,z2,z1386,z4,z5,z6])]],
   [[(0,[z1,z2,z1387,z4,z5,z6]),(0,[z2,z76,z597,z4,z5,z6]),(0,[z1,z2,z8,z5,z6,z1388])],[(0,[z1,z101,z59,z4,z5,z6]),(0,[z1,z1389,z58,z4,z5,z6]),(0,[z1,z1390,z8,z4,z5,z6]),(0,[z1,z272,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z1391,z6]),(0,[z1,z274,z4,z74,z5,z6])],[(0,[z17,z8,z76,z4,z5,z6]),(0,[z1,z402,z36,z4,z5,z6]),(0,[z1,z2,z411,z4,z44,z6])],[(0,[z1,z2,z1392,z4,z5,z6]),(0,[z1,z2,z8,z4,z1393,z6]),(0,[z1,z331,z3,z4,z5,z6]),(0,[z1,z2,z1394,z4,z5,z6]),(0,[z1,z2,z8,z242,z5,z6]),(0,[z1,z2,z8,z243,z5,z6])],[(0,[z1,z2,z138,z4,z5,z6]),(0,[z15,z22,z3,z4,z5,z6]),(0,[z2,z76,z603,z4,z5,z6]),(0,[z1,z402,z3,z4,z5,z6]),(0,[z1,z2,z1395,z4,z5,z6]),(0,[z311,z1,z3,z4,z5,z6]),(0,[z1,z2,z760,z4,z5,z6]),(0,[z202,z2,z303,z4,z5,z6])],[(0,[z252,z2,z76,z4,z5,z6]),(0,[z1,z2,z1396,z4,z5,z6]),(0,[z1,z1397,z57,z4,z5,z6])],[(1,[z121,z354,z4,z5,z6]),(0,[z482,z2,z76,z4,z5,z6]),(0,[z1,z2,z1398,z4,z5,z6]),(0,[z1,z147,z1063,z4,z5,z6]),(0,[z1,z2,z1399,z4,z5,z6]),(0,[z32,z2,z279,z4,z5,z6])],[(0,[z229,z8,z3,z4,z5,z6]),(0,[z1,z8,z1400,z4,z5,z6]),(0,[z1,z225,z1401,z4,z5,z6])],[(0,[z121,z1,z3,z4,z284,z6]),(0,[z1,z2,z1402,z4,z5,z6]),(0,[z1,z59,z4,z5,z6,z53]),(0,[z1,z2,z8,z1075,z5,z6]),(0,[z2,z8,z4,z5,z783,z102]),(0,[z0,z1,z3,z4,z5,z6]),(0,[z149,z1,z3,z72,z5,z6]),(0,[z1,z2,z1403,z4,z5,z6]),(0,[z2,z36,z1196,z4,z5,z6]),(0,[z1,z2,z1404,z4,z5,z6]),(0,[z1,z2,z20,z4,z11,z6])],[(0,[z1,z2,z1405,z4,z5,z6]),(0,[z1,z2,z129,z74,z5,z6]),(0,[z1,z2,z1406,z4,z5,z6])],[(0,[z1,z1407,z8,z4,z5,z6]),(0,[z347,z2,z76,z4,z5,z6]),(0,[z22,z1,z59,z4,z5,z6]),(0,[z1,z789,z58,z4,z5,z6]),(0,[z1,z2,z1408,z4,z5,z6]),(0,[z2,z248,z9,z4,z5,z6]),(0,[z653,z1,z8,z4,z5,z31]),(0,[z1,z2,z8,z4,z5,z932])],[(0,[z1,z2,z8,z4,z1409,z6]),(0,[z1,z59,z19,z4,z5,z6]),(0,[z1,z59,z4,z5,z18,z6]),(0,[z1,z2,z8,z1207,z5,z6]),(0,[z1,z1410,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1411]),(0,[z1,z2,z610,z4,z74,z6]),(0,[z1,z128,z8,z129,z5,z6]),(0,[z37,z2,z8,z5,z6,z85])],[(0,[z1,z1284,z3,z4,z5,z6]),(0,[z1,z2,z58,z4,z294,z6]),(0,[z1,z2,z1412,z4,z5,z6])],[(0,[z1,z2,z256,z4,z5,z6]),(0,[z1,z402,z58,z4,z5,z6]),(0,[z136,z2,z58,z4,z5,z6]),(0,[z1,z2,z58,z1413,z5,z6]),(0,[z1,z538,z3,z4,z5,z6]),(0,[z1,z174,z8,z4,z176,z6])],[(0,[z259,z2,z8,z4,z5,z6]),(0,[z209,z1,z3,z4,z24,z6]),(0,[z1,z40,z36,z4,z5,z6]),(0,[z1,z2,z8,z260,z5,z6]),(0,[z145,z2,z8,z129,z5,z6]),(0,[z1,z526,z1234,z4,z5,z6]),(0,[z1,z2,z1414,z4,z5,z6])],[(0,[z110,z434,z8,z4,z42,z6]),(0,[z1,z2,z8,z127,z116,z6]),(0,[z2,z1415,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z1193,z6])]],
   [[(0,[z1,z945,z3,z4,z5,z6]),(0,[z1,z40,z3,z4,z5,z6])],[(0,[z121,z71,z36,z4,z5,z6]),(0,[z2,z214,z76,z4,z5,z6]),(0,[z25,z2,z338,z4,z5,z6]),(0,[z1,z2,z1044,z4,z5,z6]),(0,[z555,z2,z8,z4,z42,z6])],[(0,[z136,z8,z4,z5,z6,z31])],[(0,[z121,z71,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z177,z6]),(0,[z1,z3,z72,z5,z6,z85]),(0,[z122,z2,z173,z4,z5,z6])],[(0,[z2,z1416,z36,z4,z5,z6]),(0,[z145,z128,z8,z4,z5,z6])],[(0,[z1,z2,z63,z4,z240,z6]),(0,[z1417,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z5,z961,z85]),(0,[z1,z1397,z8,z4,z5,z6])],[(0,[z202,z2,z76,z4,z5,z6]),(0,[z2,z76,z4,z5,z615,z6]),(0,[z1418,z1,z8,z4,z5,z6]),(0,[z1,z174,z3,z4,z65,z6]),(0,[z2,z8,z4,z5,z6,z1419]),(0,[z1420,z2,z8,z4,z5,z6]),(0,[z33,z37,z2,z8,z5,z85])],[(0,[z1,z267,z58,z4,z5,z6]),(0,[z1,z2,z1421,z4,z5,z6]),(0,[z2,z36,z173,z4,z5,z6]),(0,[z1,z8,z274,z4,z5,z6]),(0,[z1422,z2,z8,z4,z5,z6]),(0,[z1423,z2,z8,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z809])],[(0,[z1,z2,z76,z4,z114,z6]),(0,[z1,z2,z3,z4,z1424,z6]),(0,[z1,z2,z1425,z4,z5,z6]),(0,[z195,z8,z72,z4,z5,z6]),(0,[z2,z8,z4,z6,z212,z92]),(0,[z1,z2,z8,z4,z1009,z28]),(0,[z1,z2,z1426,z4,z5,z6])],[(0,[z1,z40,z58,z4,z5,z6]),(0,[z14,z383,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1427]),(0,[z2,z173,z4,z5,z6,z31]),(0,[z27,z1,z2,z36,z4,z28]),(0,[z1,z2,z1428,z4,z5,z6]),(0,[z51,z1,z2,z129,z5,z6]),(0,[z1,z2,z4,z5,z6,z1429])],[(0,[z15,z49,z55,z4,z5,z6]),(0,[z662,z2,z76,z4,z5,z6]),(0,[z250,z2,z8,z38,z5,z6]),(0,[z149,z1,z2,z318,z5,z6]),(0,[z1,z122,z894,z4,z5,z6])],[(0,[z1,z2,z1430,z4,z5,z6]),(0,[z1,z2,z8,z4,z1431,z6]),(0,[z152,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z1432,z6]),(0,[z1,z3,z4,z5,z6,z370]),(0,[z1,z2,z651,z4,z44,z6]),(0,[z1433,z2,z8,z4,z5,z6])],[(0,[z121,z71,z58,z4,z5,z6]),(0,[z1,z2,z1284,z4,z5,z6]),(0,[z50,z2,z249,z4,z5,z6]),(0,[z1,z2,z139,z127,z5,z6]),(0,[z252,z2,z955,z4,z5,z6]),(0,[z1,z8,z361,z4,z24,z6]),(0,[z2,z8,z4,z5,z6,z1434])],[(0,[z104,z49,z76,z4,z5,z6]),(0,[z280,z2,z76,z4,z5,z6]),(0,[z7,z2,z8,z832,z5,z6]),(0,[z1,z2,z3,z73,z12,z6]),(0,[z1,z569,z8,z4,z6,z28])],[(0,[z2,z58,z322,z4,z5,z6]),(0,[z1,z2,z1435,z4,z5,z6]),(0,[z64,z1,z2,z8,z4,z28]),(0,[z1,z2,z1436,z4,z5,z6]),(0,[z1,z3,z4,z5,z373,z6]),(1,[z1,z2,z4,z738,z6]),(0,[z1,z2,z845,z4,z5,z6])],[(0,[z626,z1,z3,z4,z5,z6]),(0,[z1,z2,z8,z1437,z5,z6]),(0,[z1,z59,z4,z5,z42,z6]),(0,[z1,z2,z1438,z4,z5,z6]),(0,[z1,z2,z58,z4,z838,z6]),(0,[z1,z2,z8,z4,z1439,z6]),(0,[z280,z569,z8,z4,z5,z6]),(0,[z1,z2,z403,z4,z13,z6])]],
   [[(0,[z1,z2,z76,z4,z56,z6]),(0,[z1,z2,z4,z5,z6,z1440]),(0,[z1,z376,z72,z4,z5,z6])],[(0,[z1,z2,z36,z4,z5,z6]),(0,[z1,z171,z76,z4,z5,z6]),(0,[z365,z2,z58,z4,z5,z6]),(0,[z2,z434,z8,z4,z42,z6]),(0,[z2,z173,z354,z4,z5,z6]),(0,[z229,z2,z173,z4,z5,z6]),(0,[z1441,z2,z8,z4,z5,z6])],[(0,[z2,z8,z399,z9,z5,z6]),(0,[z383,z8,z9,z4,z5,z6]),(0,[z397,z1,z3,z4,z5,z6]),(0,[z1,z8,z1063,z4,z5,z6]),(0,[z1,z3,z377,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z121,z2,z76,z4,z255,z6]),(0,[z1,z2,z8,z1442,z5,z6]),(0,[z717,z1,z8,z4,z5,z6]),(0,[z14,z2,z36,z38,z5,z6]),(0,[z47,z325,z8,z4,z5,z6])],[(0,[z2,z58,z76,z4,z5,z6]),(0,[z2,z399,z76,z9,z5,z6]),(0,[z1,z2,z8,z4,z5,z1443]),(0,[z47,z2,z8,z4,z5,z522]),(0,[z1,z3,z4,z42,z24,z6]),(0,[z2,z8,z1444,z4,z5,z6]),(0,[z1,z2,z1445,z4,z5,z6])],[(0,[z15,z2,z249,z4,z5,z6]),(0,[z7,z2,z76,z9,z5,z6]),(0,[z1,z1446,z8,z4,z5,z6]),(0,[z14,z2,z3,z38,z5,z6]),(1,[z1,z894,z4,z5,z6]),(0,[z1,z2,z1125,z4,z5,z6]),(0,[z1,z2,z8,z4,z1447,z6]),(0,[z1,z1448,z8,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1449])],[(0,[z110,z2,z76,z4,z42,z6]),(0,[z1,z1450,z8,z4,z5,z6]),(0,[z1,z8,z906,z4,z5,z6]),(0,[z1,z8,z712,z105,z5,z6]),(0,[z1,z135,z8,z72,z388,z6]),(0,[z1,z8,z548,z4,z6,z28])],[(0,[z22,z2,z76,z4,z23,z6]),(0,[z1,z2,z1451,z4,z5,z6]),(0,[z25,z2,z76,z4,z5,z6]),(0,[z1,z59,z59,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1452]),(0,[z1,z2,z8,z4,z1453,z6]),(0,[z47,z2,z333,z4,z5,z6]),(0,[z1,z291,z3,z4,z5,z6]),(0,[z1,z2,z36,z4,z70,z6]),(0,[z1,z2,z1454,z4,z5,z6]),(0,[z1,z2,z8,z4,z1455,z6])],[(0,[z1,z2,z1456,z4,z5,z6]),(0,[z30,z1,z76,z4,z5,z31]),(0,[z1,z81,z117,z4,z5,z6]),(0,[z1,z2,z222,z5,z6,z80])],[(0,[z664,z2,z76,z4,z5,z6]),(0,[z1,z2,z1457,z4,z5,z6]),(0,[z1,z2,z3,z4,z70,z6]),(0,[z30,z1,z8,z4,z567,z31]),(0,[z2,z57,z749,z4,z5,z6])],[(0,[z1,z425,z3,z4,z5,z6]),(0,[z1,z4,z5,z6,z1440,z84])],[(0,[z268,z2,z8,z4,z42,z6]),(0,[z1,z8,z1458,z4,z5,z6]),(0,[z1,z1459,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1460,z6]),(0,[z10,z343,z2,z4,z5,z53]),(0,[z1,z67,z8,z4,z11,z6])],[(0,[z2,z76,z4,z5,z630,z6]),(0,[z1,z59,z4,z5,z75,z6]),(0,[z1,z2,z248,z4,z109,z6]),(0,[z1,z2,z1461,z4,z5,z6]),(0,[z10,z2,z173,z4,z5,z6]),(0,[z1,z2,z1462,z4,z5,z6]),(0,[z252,z135,z8,z72,z5,z6]),(0,[z1463,z2,z8,z4,z5,z6]),(0,[z1,z264,z4,z5,z24,z6]),(0,[z195,z2,z1261,z4,z5,z6]),(0,[z1,z2,z995,z21,z5,z6]),(0,[z1,z2,z649,z4,z74,z6]),(0,[z1,z2,z20,z129,z5,z6])],[(0,[z1,z2,z1464,z4,z5,z6]),(0,[z1,z59,z9,z4,z5,z6]),(0,[z1,z201,z8,z4,z5,z6]),(0,[z730,z2,z36,z4,z5,z6]),(0,[z1,z2,z4,z74,z6,z625]),(0,[z27,z365,z2,z8,z4,z28])],[(0,[z326,z1,z368,z4,z5,z6]),(0,[z1,z135,z59,z4,z5,z6]),(0,[z2,z1240,z8,z4,z5,z6]),(0,[z205,z1,z274,z4,z5,z6]),(0,[z2,z8,z233,z4,z13,z6])],[(0,[z1,z325,z8,z4,z5,z6]),(0,[z2,z76,z4,z5,z42,z6]),(0,[z1,z2,z208,z4,z5,z6]),(0,[z2,z475,z3,z4,z5,z6]),(0,[z1465,z2,z8,z4,z5,z6]),(0,[z104,z1,z8,z435,z5,z6]),(0,[z1,z2,z1466,z4,z5,z6])]],
   [[(0,[z2,z76,z4,z5,z6,z633]),(0,[z1,z8,z72,z4,z97,z6]),(0,[z2,z233,z757,z4,z5,z6])],[(0,[z441,z1,z354,z4,z5,z6]),(0,[z14,z2,z208,z38,z5,z6]),(0,[z1,z3,z4,z5,z6,z396]),(0,[z229,z122,z8,z4,z5,z6]),(0,[z2,z173,z4,z5,z6,z1467]),(0,[z1,z2,z36,z4,z6,z212]),(0,[z104,z1,z376,z4,z5,z6]),(0,[z1,z2,z1468,z4,z5,z6]),(0,[z1,z2,z8,z1469,z5,z6]),(0,[z1,z2,z4,z220,z6,z53]),(0,[z37,z2,z1136,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z308]),(0,[z2,z346,z4,z5,z6,z102]),(0,[z47,z2,z346,z4,z5,z6]),(0,[z2,z173,z12,z4,z5,z6]),(0,[z2,z173,z4,z5,z158,z6]),(0,[z1,z2,z4,z5,z6,z1470]),(0,[z1,z128,z20,z4,z5,z6]),(0,[z1,z1471,z8,z4,z5,z6])],[(0,[z1,z2,z333,z4,z5,z6]),(0,[z1,z2,z1472,z4,z5,z6]),(0,[z1,z135,z167,z72,z5,z6]),(0,[z25,z2,z8,z4,z220,z6]),(0,[z1,z2,z8,z175,z61,z6]),(0,[z1473,z2,z8,z4,z5,z6])],[(0,[z1,z8,z849,z4,z5,z6]),(0,[z653,z1,z2,z8,z4,z28]),(0,[z560,z1,z2,z8,z5,z85])],[(0,[z2,z214,z173,z4,z5,z6]),(0,[z2,z76,z4,z65,z42,z6]),(0,[z1,z59,z4,z5,z6,z102]),(0,[z1,z2,z1474,z4,z5,z6]),(0,[z1,z2,z133,z4,z5,z6]),(0,[z1,z2,z8,z1362,z5,z6]),(0,[z752,z2,z36,z4,z5,z6]),(0,[z1,z2,z1475,z4,z5,z6]),(0,[z145,z2,z20,z4,z5,z6]),(0,[z1,z2,z52,z4,z5,z618]),(0,[z1,z225,z8,z73,z12,z6]),(0,[z32,z2,z87,z4,z5,z6]),(0,[z1,z2,z1476,z4,z5,z6])],[(0,[z27,z2,z173,z4,z5,z6]),(0,[z1,z2,z20,z4,z373,z6])],[(0,[z0,z1,z59,z4,z5,z6]),(0,[z1,z2,z1477,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z1478])],[(0,[z1,z2,z130,z4,z284,z6]),(0,[z2,z76,z4,z5,z6,z642]),(0,[z1,z2,z501,z4,z44,z6]),(0,[z1,z2,z8,z4,z1479,z6]),(0,[z10,z1,z2,z4,z5,z363]),(0,[z1,z8,z4,z5,z6,z1480]),(0,[z1,z2,z87,z4,z13,z6])],[(0,[z397,z1,z1481,z4,z5,z6]),(0,[z1,z2,z36,z127,z5,z6]),(0,[z1,z3,z4,z5,z412,z6]),(0,[z202,z526,z8,z4,z5,z6]),(0,[z1482,z2,z8,z4,z5,z6])],[(0,[z49,z368,z76,z4,z5,z6]),(0,[z2,z76,z4,z42,z6,z28]),(0,[z1,z2,z1481,z4,z5,z6]),(0,[z1,z2,z83,z4,z567,z6]),(0,[z1483,z2,z8,z4,z5,z6]),(0,[z1,z1484,z8,z4,z5,z6]),(0,[z1,z2,z1485,z4,z5,z6]),(0,[z1486,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z961])],[(0,[z1,z1487,z59,z4,z5,z6]),(0,[z1,z2,z8,z4,z1488,z6]),(0,[z1,z225,z8,z4,z5,z6]),(0,[z1489,z2,z8,z4,z5,z6]),(0,[z2,z8,z760,z4,z5,z6])],[(0,[z1,z2,z1490,z4,z5,z6]),(0,[z1,z2,z58,z4,z6,z212]),(0,[z1,z1491,z8,z4,z5,z6])],[(0,[z1,z174,z207,z4,z5,z6]),(0,[z51,z1,z59,z4,z5,z6]),(0,[z1,z325,z1492,z4,z5,z6]),(0,[z1,z2,z1493,z4,z5,z6])],[(0,[z2,z76,z644,z4,z5,z6]),(0,[z1,z2,z1494,z4,z5,z6]),(0,[z487,z2,z82,z4,z5,z6]),(0,[z1,z2,z144,z222,z5,z6]),(0,[z2,z760,z73,z4,z5,z6])],[(0,[z1,z2,z138,z4,z284,z6]),(0,[z1,z2,z8,z1495,z5,z6]),(0,[z1496,z2,z8,z4,z5,z6]),(0,[z1,z1497,z2,z4,z5,z6]),(0,[z280,z2,z525,z4,z5,z6]),(0,[z1,z2,z8,z4,z13,z1009])]],
   [[(0,[z121,z71,z256,z4,z5,z6]),(0,[z1,z2,z1498,z4,z5,z6]),(0,[z1,z2,z8,z157,z4,z6])],[(0,[z465,z71,z8,z4,z5,z6]),(0,[z104,z1,z76,z105,z5,z6]),(0,[z784,z2,z36,z4,z5,z6]),(0,[z1,z2,z1499,z4,z5,z6]),(0,[z33,z552,z1,z8,z5,z85])],[(0,[z1,z2,z58,z4,z220,z6]),(0,[z1,z2,z1500,z4,z5,z6]),(0,[z1,z3,z4,z5,z334,z6]),(0,[z2,z63,z173,z4,z5,z6]),(0,[z1,z2,z1501,z4,z5,z6]),(0,[z1,z2,z1502,z4,z5,z6])],[(0,[z22,z2,z55,z4,z5,z6]),(0,[z1,z2,z76,z111,z5,z6]),(0,[z1,z81,z58,z4,z5,z18]),(0,[z1,z2,z36,z4,z507,z6]),(0,[z54,z1,z2,z21,z5,z6])],[(0,[z634,z1,z8,z4,z24,z6]),(0,[z1,z2,z1503,z4,z5,z6]),(0,[z2,z118,z76,z4,z5,z6]),(0,[z1,z2,z76,z4,z116,z6]),(0,[z1,z2,z58,z127,z5,z6]),(0,[z1,z1504,z8,z4,z5,z6]),(0,[z1,z2,z1505,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z84]),(0,[z419,z2,z173,z4,z5,z6]),(0,[z1,z2,z36,z4,z294,z6]),(0,[z1,z2,z8,z1273,z5,z6]),(0,[z1,z2,z8,z4,z1506,z6]),(0,[z196,z2,z20,z4,z44,z6]),(0,[z37,z2,z34,z4,z5,z6])],[(0,[z2,z76,z4,z5,z6,z102]),(0,[z136,z2,z36,z4,z5,z6])],[(0,[z297,z2,z76,z4,z5,z6]),(0,[z341,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z294,z6]),(0,[z1507,z2,z8,z4,z5,z6]),(0,[z1,z1508,z8,z4,z5,z6])],[(0,[z1,z354,z4,z5,z24,z6]),(0,[z136,z2,z3,z4,z5,z6]),(0,[z1,z8,z4,z712,z5,z6]),(0,[z1,z2,z756,z4,z5,z6]),(0,[z1,z2,z1509,z4,z5,z6])],[(0,[z15,z1,z354,z4,z5,z6]),(0,[z2,z58,z173,z4,z5,z6]),(0,[z1,z2,z1510,z4,z5,z6]),(0,[z211,z1,z3,z4,z5,z6]),(0,[z2,z1511,z8,z4,z5,z6])],[(0,[z121,z8,z354,z4,z5,z6]),(0,[z305,z2,z76,z4,z5,z6]),(0,[z186,z1,z59,z4,z5,z6]),(0,[z325,z8,z4,z5,z6,z102]),(0,[z1,z307,z3,z4,z5,z6]),(0,[z104,z1,z8,z712,z5,z6]),(0,[z1,z2,z1512,z4,z5,z6]),(0,[z1,z2,z1513,z4,z5,z6])],[(0,[z50,z2,z708,z4,z5,z6]),(0,[z1,z2,z1514,z4,z5,z6]),(0,[z2,z173,z4,z490,z5,z6]),(0,[z1,z174,z264,z4,z5,z6])],[(0,[z1,z2,z249,z4,z5,z6]),(0,[z2,z338,z76,z4,z5,z6]),(0,[z1,z171,z384,z4,z5,z6]),(0,[z1,z160,z3,z72,z5,z6]),(0,[z1,z2,z1515,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z1516]),(0,[z1,z2,z8,z4,z1517,z6]),(0,[z457,z1,z3,z4,z5,z6]),(0,[z2,z173,z4,z5,z6,z28]),(0,[z209,z217,z8,z4,z24,z6])],[(0,[z1,z3,z348,z4,z5,z6]),(0,[z416,z71,z8,z4,z5,z6]),(0,[z1518,z1,z59,z4,z5,z6]),(0,[z1,z2,z8,z4,z1300,z6]),(0,[z7,z2,z8,z9,z109,z6]),(0,[z88,z325,z8,z4,z5,z102]),(0,[z1,z63,z201,z4,z5,z6]),(0,[z1519,z2,z8,z4,z5,z6]),(0,[z1,z2,z1152,z4,z5,z6])],[(0,[z1,z2,z58,z4,z507,z6])],[(0,[z47,z2,z1288,z4,z5,z6]),(0,[z2,z76,z4,z659,z5,z6]),(0,[z1,z2,z1520,z4,z5,z6]),(0,[z250,z2,z8,z9,z5,z6]),(1,[z2,z8,z4,z5,z783]),(0,[z1,z267,z36,z4,z5,z6]),(0,[z1,z67,z8,z129,z5,z6]),(1,[z1,z853,z4,z5,z6]),(0,[z1,z2,z8,z4,z1521,z6])]],
   [[(0,[z1,z2,z199,z4,z74,z6]),(0,[z1,z2,z76,z242,z5,z6]),(0,[z47,z383,z8,z4,z5,z6]),(0,[z1,z2,z8,z79,z97,z6]),(0,[z280,z2,z8,z96,z5,z6])],[(1,[z2,z173,z4,z5,z6]),(0,[z131,z2,z8,z4,z42,z6]),(0,[z88,z2,z333,z4,z5,z102]),(0,[z1,z267,z3,z4,z5,z6]),(0,[z2,z173,z4,z13,z5,z6])],[(0,[z1,z2,z59,z4,z5,z6]),(0,[z1,z2,z1522,z4,z5,z6]),(0,[z2,z4,z5,z6,z92,z219]),(0,[z1,z2,z403,z4,z6,z28])],[(1,[z2,z8,z4,z829,z6]),(0,[z2,z173,z4,z21,z5,z6]),(0,[z2,z144,z173,z4,z5,z6]),(0,[z209,z1,z8,z4,z24,z6]),(0,[z33,z1,z2,z8,z5,z85]),(0,[z1,z1152,z8,z4,z5,z6])],[(0,[z1,z2,z1523,z4,z5,z6]),(0,[z1524,z1,z2,z4,z5,z6]),(0,[z1,z2,z8,z4,z158,z375]),(0,[z280,z2,z403,z4,z5,z6])],[(0,[z205,z1,z2,z490,z5,z6]),(0,[z1,z2,z1525,z4,z5,z6]),(0,[z1,z2,z1526,z4,z5,z6])],[(0,[z1,z1527,z59,z4,z5,z6]),(0,[z2,z8,z672,z4,z42,z6]),(0,[z406,z1,z3,z4,z5,z6]),(0,[z104,z1,z155,z105,z5,z6]),(0,[z1528,z2,z8,z4,z5,z6]),(0,[z1,z2,z1529,z4,z5,z6])],[(0,[z1,z434,z36,z4,z5,z6]),(0,[z1,z402,z333,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z31]),(0,[z1,z2,z1530,z4,z5,z6]),(0,[z1,z2,z52,z4,z220,z6]),(0,[z1,z2,z8,z1531,z5,z6])],[(0,[z444,z2,z76,z4,z5,z6]),(0,[z145,z67,z8,z4,z5,z6]),(0,[z1,z94,z34,z4,z5,z6]),(0,[z1,z2,z8,z4,z158,z1009])],[(0,[z426,z2,z76,z4,z5,z6]),(0,[z1,z526,z58,z4,z5,z6]),(0,[z1,z434,z3,z4,z5,z6]),(0,[z1,z3,z4,z23,z24,z6]),(0,[z365,z2,z36,z4,z5,z6]),(0,[z104,z136,z8,z4,z5,z6]),(0,[z37,z94,z8,z4,z5,z6]),(0,[z33,z1,z2,z8,z70,z85]),(0,[z33,z46,z1,z2,z5,z85]),(0,[z1532,z2,z8,z4,z5,z6])],[],[(0,[z1,z2,z8,z4,z1533,z6]),(0,[z1,z2,z1288,z4,z5,z6]),(0,[z14,z1,z906,z4,z5,z6]),(0,[z1,z2,z8,z4,z1534,z6]),(0,[z365,z2,z3,z4,z5,z6]),(0,[z1,z174,z8,z4,z65,z6]),(0,[z1,z52,z274,z4,z5,z6]),(0,[z1,z2,z1535,z4,z5,z6])],[(0,[z1,z2,z36,z4,z284,z6]),(0,[z1,z383,z8,z4,z5,z6]),(0,[z1,z36,z4,z5,z6,z84]),(0,[z2,z8,z1125,z4,z5,z6])],[(0,[z2,z76,z4,z617,z5,z6]),(0,[z1,z2,z1536,z4,z5,z6]),(0,[z1,z2,z26,z4,z5,z6])],[(0,[z49,z761,z8,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z371]),(0,[z1537,z2,z8,z4,z5,z6])],[(0,[z1,z1538,z8,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z449]),(0,[z1539,z2,z8,z4,z5,z6]),(0,[z1,z2,z1077,z4,z5,z6])]],
   [[(0,[z1,z1332,z8,z4,z5,z6]),(0,[z491,z2,z8,z4,z42,z6]),(0,[z135,z2,z173,z4,z5,z6]),(0,[z1312,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1540]),(0,[z1,z2,z1541,z4,z5,z6])],[(0,[z2,z71,z8,z4,z284,z6]),(1,[z761,z8,z4,z5,z6]),(0,[z30,z2,z173,z4,z5,z6]),(0,[z1,z8,z72,z4,z388,z6]),(0,[z1542,z2,z8,z4,z5,z6]),(0,[z2,z8,z233,z4,z6,z28])],[(0,[z121,z1,z3,z4,z255,z6]),(0,[z634,z2,z8,z4,z42,z6]),(0,[z1,z81,z8,z4,z5,z400]),(0,[z27,z1,z2,z76,z4,z28]),(0,[z1,z434,z58,z4,z5,z6]),(0,[z1,z1543,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z1544,z6]),(0,[z1,z2,z8,z1545,z5,z6])],[(0,[z2,z76,z4,z5,z675,z6]),(0,[z1,z2,z228,z4,z520,z6]),(0,[z1546,z1,z2,z4,z5,z6])],[(0,[z15,z49,z58,z4,z5,z6]),(0,[z195,z2,z58,z4,z5,z6]),(0,[z1,z846,z548,z4,z5,z6]),(0,[z1,z2,z1547,z4,z5,z6])],[(0,[z1,z59,z4,z74,z5,z6])],[(0,[z2,z893,z3,z4,z5,z6]),(0,[z2,z20,z173,z4,z5,z6]),(0,[z1,z1548,z8,z4,z5,z6]),(0,[z1,z2,z26,z19,z5,z6])],[(0,[z397,z1,z8,z4,z5,z6]),(0,[z1,z2,z58,z4,z284,z6]),(0,[z1,z1018,z58,z4,z5,z6]),(0,[z88,z402,z8,z4,z5,z102]),(0,[z195,z2,z83,z4,z5,z6]),(0,[z1,z2,z1549,z4,z5,z6])],[(0,[z1,z2,z1550,z4,z5,z6]),(0,[z1,z2,z36,z4,z13,z158]),(0,[z1,z2,z144,z995,z5,z6]),(0,[z1,z2,z8,z242,z507,z6]),(0,[z1,z2,z1121,z4,z5,z6]),(0,[z33,z1,z2,z8,z5,z961])],[(0,[z1,z2,z58,z96,z5,z6]),(0,[z1551,z2,z8,z4,z5,z6]),(0,[z1,z2,z1552,z4,z5,z6]),(0,[z1,z2,z4,z5,z75,z251])],[(0,[z1,z2,z108,z4,z5,z75]),(0,[z1,z2,z238,z4,z109,z6]),(0,[z1,z2,z1553,z4,z5,z6]),(0,[z1,z2,z1089,z4,z5,z6])],[(0,[z1,z2,z954,z4,z5,z6]),(0,[z1,z2,z87,z4,z6,z28]),(0,[z876,z1,z4,z5,z6,z84])],[(0,[z602,z2,z76,z4,z5,z6]),(0,[z552,z1,z58,z4,z5,z6]),(0,[z2,z8,z4,z5,z100,z534]),(0,[z1,z8,z72,z79,z5,z6]),(0,[z1,z2,z8,z4,z1554,z6]),(0,[z1,z2,z1555,z4,z5,z6])],[(0,[z49,z2,z76,z4,z5,z6]),(0,[z1,z2,z8,z4,z1556,z6]),(0,[z1,z59,z4,z5,z168,z6]),(0,[z1,z2,z144,z300,z5,z6]),(0,[z2,z346,z9,z4,z5,z6]),(0,[z1557,z2,z8,z4,z5,z6]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z1,z2,z160,z222,z5,z6]),(0,[z1,z2,z1558,z4,z5,z6]),(0,[z1,z1559,z8,z4,z5,z6])],[(0,[z1,z2,z1560,z4,z5,z6]),(0,[z1,z40,z144,z222,z5,z6])],[(0,[z1,z2,z36,z4,z567,z6]),(0,[z1,z323,z8,z4,z5,z6])]],
   [[(0,[z1,z2,z1561,z4,z5,z6]),(0,[z494,z2,z173,z4,z5,z6]),(0,[z1,z569,z36,z4,z5,z6]),(0,[z1,z8,z274,z4,z220,z6])],[(0,[z554,z2,z76,z4,z5,z6]),(0,[z489,z2,z76,z4,z5,z6]),(0,[z1,z2,z3,z4,z567,z6])],[(0,[z1,z1446,z76,z4,z5,z6]),(0,[z1,z2,z58,z4,z11,z6]),(0,[z434,z8,z4,z5,z42,z6]),(0,[z2,z8,z700,z4,z42,z6]),(0,[z1,z569,z3,z4,z5,z6]),(0,[z1,z162,z36,z4,z5,z6]),(0,[z104,z1,z269,z4,z5,z6]),(0,[z1,z2,z525,z243,z5,z6])],[(0,[z1,z354,z72,z4,z5,z6]),(0,[z1,z440,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z898,z6]),(0,[z487,z2,z36,z4,z5,z6]),(0,[z1,z2,z1562,z4,z5,z6]),(0,[z2,z233,z87,z4,z5,z6]),(0,[z1,z2,z1563,z4,z5,z6])],[(0,[z121,z1,z207,z4,z5,z6]),(0,[z326,z121,z76,z4,z5,z6]),(0,[z1,z2,z1564,z4,z5,z6]),(0,[z1,z59,z4,z5,z6,z1565]),(0,[z1,z2,z1566,z4,z5,z6]),(0,[z1,z652,z36,z4,z5,z6])],[(0,[z1,z2,z1567,z4,z5,z6]),(0,[z487,z2,z3,z4,z5,z6]),(0,[z217,z2,z82,z4,z5,z6])],[(0,[z1,z2,z1568,z4,z5,z6]),(0,[z10,z1,z59,z4,z5,z6]),(0,[z1,z2,z1492,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z212]),(0,[z367,z1,z2,z4,z5,z53]),(0,[z33,z1,z2,z8,z294,z85])],[(0,[z1,z1569,z8,z4,z5,z6]),(0,[z2,z76,z4,z5,z697,z6]),(0,[z353,z2,z8,z9,z5,z6]),(0,[z1,z2,z52,z4,z5,z281]),(0,[z1,z2,z1401,z4,z5,z6])],[(0,[z1,z8,z894,z4,z5,z6]),(0,[z1,z2,z1570,z4,z5,z6]),(0,[z1,z8,z157,z4,z6,z84])],[(0,[z156,z121,z3,z4,z5,z6]),(0,[z1,z2,z708,z4,z5,z6]),(0,[z1,z59,z4,z5,z44,z6]),(0,[z1,z2,z63,z4,z738,z6])],[(0,[z1,z2,z76,z4,z1349,z6]),(0,[z1,z201,z76,z4,z5,z6]),(0,[z22,z2,z8,z4,z667,z6]),(0,[z1,z2,z58,z4,z567,z6]),(0,[z1,z2,z1571,z4,z5,z6]),(0,[z367,z1,z3,z4,z5,z31]),(0,[z1,z2,z36,z4,z220,z6]),(0,[z1572,z2,z8,z4,z5,z6]),(0,[z1,z2,z63,z4,z74,z6]),(0,[z27,z1,z2,z403,z4,z28])],[(0,[z1,z569,z58,z4,z5,z6]),(0,[z1,z2,z1573,z4,z5,z6]),(0,[z1,z2,z403,z73,z4,z6])],[(0,[z1,z81,z249,z4,z5,z6]),(0,[z1,z2,z3,z4,z220,z6]),(0,[z252,z2,z8,z4,z388,z6]),(0,[z1574,z2,z307,z4,z5,z6]),(0,[z1,z2,z144,z206,z5,z6]),(0,[z2,z8,z1575,z4,z5,z6])],[(0,[z49,z76,z72,z4,z5,z6]),(0,[z1,z1576,z8,z4,z5,z6]),(0,[z1,z81,z3,z4,z5,z18]),(0,[z1,z2,z8,z4,z1577,z6])],[(0,[z1,z122,z130,z4,z5,z6]),(0,[z1,z2,z8,z4,z5,z1578]),(0,[z1,z2,z8,z1579,z5,z6]),(0,[z343,z2,z8,z4,z5,z6]),(0,[z1,z59,z4,z5,z61,z6]),(0,[z487,z2,z58,z4,z5,z6]),(0,[z1,z1580,z8,z4,z5,z6]),(0,[z1,z2,z3,z127,z5,z6]),(0,[z721,z2,z8,z4,z5,z6]),(0,[z365,z2,z8,z243,z5,z6])],[(0,[z121,z50,z3,z4,z5,z6]),(0,[z2,z76,z4,z5,z703,z6]),(0,[z229,z1,z3,z4,z5,z6]),(0,[z1,z174,z945,z4,z5,z6]),(0,[z934,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z76,z9,z4,z5,z6]),(0,[z1,z2,z76,z175,z61,z6]),(0,[z27,z1,z59,z4,z5,z6]),(0,[z1,z59,z4,z65,z5,z6]),(0,[z1,z1389,z8,z4,z5,z6]),(0,[z174,z2,z173,z4,z5,z6])],[(0,[z14,z2,z8,z566,z5,z6]),(0,[z1,z2,z346,z4,z5,z6]),(0,[z1,z1581,z8,z4,z5,z6]),(0,[z22,z1,z775,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z481]),(0,[z1,z2,z1582,z4,z5,z6]),(0,[z33,z1,z94,z8,z5,z85])],[(0,[z1,z256,z59,z4,z5,z6]),(0,[z1,z207,z72,z4,z5,z6]),(0,[z89,z1,z2,z4,z5,z389]),(0,[z51,z1,z2,z106,z5,z6]),(0,[z1,z2,z4,z5,z6,z1583]),(0,[z2,z173,z4,z5,z1584,z6]),(0,[z1,z1585,z8,z4,z5,z6]),(0,[z1,z2,z8,z73,z705,z6])],[(0,[z180,z2,z76,z4,z5,z6]),(0,[z1,z81,z59,z4,z5,z6]),(0,[z1,z1068,z58,z4,z5,z6]),(0,[z2,z244,z173,z4,z5,z6]),(0,[z1,z2,z8,z4,z1377,z6]),(0,[z1,z2,z167,z4,z388,z6]),(0,[z1,z2,z8,z4,z1586,z6])],[(0,[z1,z2,z1587,z4,z5,z6]),(0,[z2,z368,z173,z4,z5,z6]),(0,[z1,z59,z1588,z4,z5,z6]),(0,[z325,z8,z9,z4,z5,z6]),(0,[z1,z2,z8,z4,z1589,z6]),(0,[z1,z2,z1590,z4,z5,z6]),(0,[z1,z548,z87,z4,z5,z6])],[],[(0,[z1,z2,z1591,z4,z5,z6]),(0,[z1,z2,z1592,z4,z5,z6]),(0,[z1,z434,z8,z4,z42,z6]),(0,[z1,z2,z1593,z4,z5,z6]),(0,[z88,z2,z8,z4,z5,z102]),(0,[z1,z2,z21,z5,z6,z528]),(0,[z1,z2,z4,z5,z6,z1594])],[(0,[z2,z76,z35,z4,z5,z6]),(0,[z1,z2,z52,z4,z11,z6]),(0,[z1,z2,z403,z243,z5,z6])],[(0,[z1,z17,z58,z4,z5,z6]),(0,[z1,z225,z76,z4,z5,z6]),(0,[z1,z1595,z8,z4,z5,z6]),(0,[z1,z2,z745,z4,z5,z6]),(0,[z229,z36,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z507,z6]),(0,[z866,z2,z8,z4,z5,z6]),(0,[z1,z2,z8,z1596,z5,z6])],[(0,[z2,z76,z9,z19,z5,z6]),(0,[z2,z76,z4,z5,z6,z45]),(0,[z252,z2,z167,z4,z5,z6]),(0,[z1597,z2,z8,z4,z5,z6]),(0,[z1,z569,z8,z73,z4,z6])],[(0,[z1,z174,z354,z4,z5,z6]),(0,[z49,z2,z368,z4,z5,z6]),(0,[z1,z325,z8,z127,z5,z6]),(0,[z1,z2,z755,z4,z5,z6]),(0,[z2,z8,z1598,z4,z5,z6]),(0,[z1574,z2,z8,z4,z5,z6]),(0,[z1,z2,z1599,z4,z5,z6]),(0,[z1,z2,z73,z12,z87,z6])],[(0,[z1,z2,z908,z4,z5,z6]),(0,[z1600,z2,z8,z4,z5,z6])],[(0,[z1,z402,z8,z4,z5,z6]),(0,[z1,z2,z1601,z4,z5,z6]),(0,[z49,z2,z354,z4,z5,z6]),(0,[z131,z71,z8,z4,z5,z6]),(0,[z1,z59,z4,z5,z95,z6]),(0,[z1,z2,z8,z1413,z5,z6]),(0,[z1,z2,z8,z242,z11,z6]),(0,[z1,z8,z4,z5,z6,z1602])],[(0,[z1,z2,z76,z157,z4,z6]),(0,[z1,z58,z4,z5,z6,z84]),(0,[z1,z135,z8,z712,z5,z6]),(0,[z1,z274,z222,z4,z5,z6]),(0,[z1,z323,z778,z4,z5,z6])],[(0,[z47,z2,z76,z4,z5,z102]),(0,[z419,z1,z59,z4,z5,z6]),(0,[z1,z1316,z8,z4,z5,z6]),(0,[z22,z2,z8,z4,z588,z6]),(0,[z1,z2,z333,z127,z5,z6]),(0,[z47,z1,z1063,z4,z5,z6])],[(0,[z1,z2,z1603,z4,z5,z6]),(0,[z1,z2,z1604,z4,z5,z6]),(0,[z1,z81,z133,z4,z5,z18]),(0,[z2,z8,z1605,z4,z5,z6]),(0,[z2,z8,z4,z5,z6,z1606])]],
   [[(0,[z1,z1607,z8,z4,z5,z6]),(0,[z1,z59,z4,z106,z5,z6]),(0,[z22,z2,z208,z4,z5,z6]),(0,[z1,z2,z498,z4,z5,z572]),(0,[z1608,z2,z8,z4,z5,z6]),(0,[z1,z2,z1609,z4,z5,z6]),(0,[z1,z174,z342,z4,z65,z6]),(0,[z1,z2,z73,z26,z12,z6])],[(0,[z49,z2,z173,z4,z5,z6]),(0,[z1,z526,z36,z4,z5,z6]),(0,[z552,z1,z1414,z4,z5,z6]),(0,[z1,z1610,z8,z4,z5,z6])],[(0,[z1,z2,z130,z4,z255,z6]),(0,[z90,z2,z708,z4,z5,z6]),(0,[z1,z2,z8,z4,z1611,z6]),(0,[z1,z2,z1612,z4,z5,z6]),(0,[z1,z2,z1613,z4,z5,z6]),(0,[z1,z2,z545,z4,z430,z6]),(0,[z33,z1,z2,z36,z5,z85]),(0,[z1614,z2,z8,z4,z5,z6]),(0,[z1,z2,z1615,z4,z5,z6]),(0,[z1616,z2,z8,z4,z5,z6])],[(0,[z2,z76,z73,z4,z42,z6]),(0,[z1,z2,z76,z243,z5,z6]),(0,[z1,z59,z72,z4,z5,z6]),(0,[z110,z2,z384,z4,z42,z6]),(0,[z1,z526,z3,z4,z5,z6]),(0,[z1,z2,z1617,z4,z5,z6])],[(0,[z1,z2,z1618,z4,z5,z6]),(0,[z1,z2,z8,z4,z1619,z6]),(0,[z49,z76,z4,z5,z24,z6]),(0,[z1,z2,z1620,z4,z5,z6]),(0,[z2,z384,z4,z5,z42,z6]),(0,[z2,z271,z173,z4,z5,z6]),(0,[z1,z2,z1621,z4,z5,z6]),(0,[z1,z2,z1622,z4,z5,z6]),(0,[z298,z1,z2,z21,z5,z6])],[(0,[z401,z2,z76,z4,z5,z6]),(0,[z2,z108,z76,z4,z5,z102]),(0,[z2,z272,z173,z4,z5,z6]),(0,[z1,z135,z36,z72,z5,z6]),(0,[z1,z2,z8,z4,z1623,z6]),(0,[z202,z2,z34,z4,z5,z6]),(0,[z1,z569,z8,z243,z5,z6])],[(0,[z1,z2,z8,z4,z1624,z6]),(0,[z1,z2,z8,z1625,z5,z6]),(0,[z2,z586,z76,z4,z5,z6]),(0,[z1,z2,z58,z129,z5,z6]),(0,[z1,z2,z1626,z4,z5,z6]),(0,[z104,z1,z3,z72,z5,z6]),(0,[z1,z8,z4,z796,z24,z6]),(0,[z1627,z2,z8,z4,z5,z6]),(0,[z1,z1628,z8,z4,z5,z6]),(1,[z1,z1152,z4,z5,z6])],[(0,[z1,z2,z101,z4,z5,z6]),(0,[z2,z71,z173,z4,z5,z6]),(0,[z1,z2,z8,z4,z1629,z6]),(0,[z27,z1,z2,z58,z4,z28]),(0,[z2,z8,z4,z285,z6,z102]),(0,[z1,z81,z3,z4,z5,z6]),(0,[z2,z1415,z8,z4,z5,z6]),(0,[z1,z641,z8,z4,z65,z6]),(0,[z1,z2,z8,z4,z5,z1630]),(0,[z1,z2,z144,z222,z220,z6])],[(0,[z426,z1,z3,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z1631]),(0,[z1,z40,z8,z4,z5,z6]),(0,[z1,z36,z274,z4,z5,z6]),(0,[z422,z1,z8,z4,z24,z6]),(0,[z1,z2,z1269,z4,z5,z6]),(0,[z1,z2,z1632,z4,z5,z6])],[(0,[z1,z2,z138,z4,z255,z6]),(0,[z1,z207,z4,z5,z24,z6]),(0,[z1,z3,z4,z5,z6,z510]),(0,[z1,z2,z376,z4,z5,z6]),(0,[z2,z8,z988,z4,z5,z6]),(0,[z1,z853,z73,z4,z5,z6])],[(0,[z2,z76,z4,z5,z6,z92]),(0,[z1,z383,z864,z4,z5,z6]),(0,[z1,z2,z57,z4,z44,z6])],[(0,[z121,z71,z8,z4,z5,z6]),(0,[z349,z2,z76,z4,z5,z6]),(0,[z1,z59,z73,z4,z5,z6]),(0,[z1,z171,z1154,z4,z5,z6]),(0,[z1,z2,z8,z4,z177,z6]),(0,[z1,z2,z57,z4,z5,z6])],[(0,[z1,z17,z130,z4,z5,z6]),(0,[z1,z2,z8,z4,z1633,z6]),(0,[z15,z49,z36,z4,z5,z6]),(0,[z2,z76,z4,z5,z95,z6]),(0,[z50,z17,z58,z4,z5,z6]),(0,[z1,z128,z58,z4,z5,z6]),(0,[z1,z2,z248,z4,z56,z6]),(0,[z7,z2,z238,z9,z5,z6]),(0,[z1,z1634,z8,z4,z5,z6]),(0,[z513,z1,z3,z4,z5,z6]),(0,[z195,z2,z36,z4,z5,z6]),(0,[z552,z1,z8,z105,z5,z6]),(0,[z2,z475,z4,z74,z5,z6])],[(0,[z1,z59,z4,z5,z100,z6]),(0,[z1,z8,z1635,z4,z5,z6]),(0,[z1,z2,z8,z1636,z5,z6]),(0,[z1,z2,z342,z4,z5,z6]),(0,[z1,z2,z8,z1637,z5,z6]),(0,[z1,z2,z307,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z1638])],[(0,[z15,z49,z3,z4,z5,z6]),(0,[z1,z1639,z8,z4,z5,z6]),(0,[z259,z2,z76,z4,z5,z6]),(0,[z1,z2,z76,z260,z5,z6]),(0,[z195,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z519,z6]),(0,[z2,z1416,z8,z4,z5,z6]),(0,[z10,z1,z67,z4,z5,z53]),(0,[z1,z2,z1640,z4,z5,z6])],[(0,[z1641,z1,z2,z4,z5,z6]),(0,[z145,z2,z58,z4,z5,z6]),(0,[z47,z2,z36,z4,z5,z100]),(0,[z259,z2,z8,z4,z567,z6]),(0,[z1,z2,z8,z260,z567,z6])]],
   [[(0,[z50,z2,z214,z4,z5,z6]),(0,[z1,z2,z360,z4,z5,z6]),(0,[z1,z135,z58,z72,z5,z6]),(0,[z1,z2,z8,z4,z1424,z6]),(0,[z1,z272,z201,z4,z5,z6]),(0,[z343,z2,z8,z4,z507,z6])],[(0,[z1,z2,z3,z4,z284,z6]),(0,[z1,z2,z1642,z4,z5,z6]),(0,[z1,z2,z58,z4,z109,z6]),(0,[z7,z2,z248,z9,z5,z6]),(0,[z1,z2,z8,z4,z1643,z6]),(0,[z1,z2,z36,z96,z5,z6]),(0,[z1,z2,z4,z74,z738,z6])],[(0,[z419,z1,z3,z4,z5,z6]),(0,[z1,z8,z4,z5,z6,z1644]),(0,[z1,z122,z36,z4,z5,z6]),(0,[z1,z2,z8,z4,z1645,z6]),(0,[z1,z2,z8,z4,z1646,z6]),(0,[z1,z2,z1647,z4,z5,z6]),(0,[z1,z8,z853,z4,z5,z6]),(0,[z1,z2,z969,z4,z5,z6])],[(0,[z1,z1648,z8,z4,z5,z6]),(0,[z1,z2,z3,z96,z5,z6]),(0,[z1,z128,z112,z4,z5,z6]),(0,[z1,z128,z4,z5,z6,z53]),(0,[z1,z2,z1649,z4,z5,z6]),(0,[z1,z57,z1152,z4,z5,z6])],[(0,[z15,z297,z3,z4,z5,z6]),(0,[z50,z2,z147,z4,z5,z6]),(0,[z552,z1,z36,z4,z5,z6])],[(0,[z104,z1,z207,z4,z5,z6]),(0,[z110,z2,z173,z4,z5,z6]),(0,[z1,z2,z1650,z4,z5,z6]),(0,[z1,z1651,z8,z4,z5,z6]),(0,[z118,z201,z8,z4,z5,z6]),(0,[z1,z2,z8,z73,z12,z6]),(0,[z1486,z2,z358,z4,z5,z6]),(0,[z1,z323,z1640,z4,z5,z6])],[(0,[z343,z2,z147,z4,z5,z6]),(0,[z552,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1652]),(0,[z145,z2,z4,z5,z6,z53])],[(0,[z110,z2,z8,z4,z829,z6]),(0,[z217,z174,z8,z4,z5,z6]),(0,[z1,z2,z8,z4,z6,z1653]),(0,[z1,z2,z1654,z4,z5,z6]),(0,[z1,z2,z1309,z4,z5,z6]),(0,[z365,z323,z8,z4,z5,z6])],[(0,[z1,z8,z4,z5,z6,z1655]),(0,[z297,z2,z354,z4,z5,z6]),(0,[z81,z2,z1125,z4,z5,z6]),(0,[z37,z2,z1222,z4,z5,z6])],[(0,[z1,z383,z76,z4,z5,z6]),(0,[z36,z173,z3,z4,z5,z6]),(0,[z1,z2,z8,z73,z735,z6]),(0,[z1,z225,z279,z4,z5,z6]),(0,[z1,z2,z1656,z4,z5,z6])],[(0,[z47,z2,z58,z4,z5,z100]),(0,[z1,z59,z4,z5,z24,z6]),(0,[z217,z2,z36,z4,z5,z6]),(0,[z1,z2,z36,z4,z11,z6]),(0,[z30,z1,z8,z79,z5,z31]),(0,[z1,z2,z8,z706,z61,z6]),(0,[z202,z94,z8,z4,z5,z6])],[(0,[z1,z2,z8,z4,z5,z6]),(1,[z2,z76,z4,z284,z6]),(0,[z30,z1,z59,z4,z5,z6]),(0,[z1,z2,z1657,z4,z5,z6]),(0,[z1,z2,z1658,z4,z5,z6]),(0,[z1,z2,z52,z129,z5,z6])],[(0,[z1,z17,z256,z4,z5,z6]),(0,[z217,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z6]),(0,[z1659,z1,z2,z4,z5,z6]),(0,[z195,z8,z4,z5,z6,z31])],[(0,[z1,z2,z8,z1660,z5,z6]),(0,[z14,z2,z8,z38,z5,z6]),(0,[z1,z2,z3,z4,z13,z158]),(0,[z1,z2,z1661,z4,z5,z6]),(0,[z1,z2,z57,z4,z74,z6])],[(0,[z58,z76,z59,z4,z5,z6]),(0,[z1,z2,z1662,z4,z5,z6]),(0,[z2,z8,z561,z9,z5,z6]),(0,[z1,z174,z8,z4,z665,z6]),(0,[z1,z2,z1663,z4,z5,z6]),(0,[z1,z2,z8,z995,z5,z6])],[(0,[z196,z2,z58,z4,z5,z6]),(0,[z1,z2,z8,z1664,z5,z6]),(0,[z1,z1665,z8,z4,z5,z6]),(0,[z1,z532,z8,z72,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 465) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 925).take 457) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1382).take 197) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1579)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 465, 457, 197] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 57).take 59).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 116).take 54).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 170).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 227).take 62).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 289).take 61).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 350).take 60).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc7 : chunkOK 5 ((bkB.flatten.drop 410).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc8 : chunkOK 5 ((bkB.flatten.drop 474).take 38).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [57, 59, 54, 57, 62, 61, 60, 64, 38] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_cons pc7 (windowsF_cons pc8 (windowsF_nil pcend)))))))))

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

end PEqualNP.Outside.L_meta_36753

theorem PEqualNP.Outside.L_meta_36753 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4008372904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36753.solve