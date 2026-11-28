import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37217

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4008505064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x440100040084c045#64 ++ 0xfffe814d27adc4cf#64 : BitVec 128),
   (0x804200104a001112#64 ++ 0xfffdc2b2da527b33#64 : BitVec 128),
   (0x18301cc314630c28#64 ++ 0x2dabbcc31c638c3c#64 : BitVec 128),
   (0x12a42f03a0780e80#64 ++ 0x1b67ff03e07c0fc0#64 : BitVec 128),
   (0x233837ec007fe000#64 ++ 0x071fbffc007ff000#64 : BitVec 128),
   (0x03c03bfbff000000#64 ++ 0x00ffbfffff800000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [6, 11]⟩, ⟨.and, [10, 7]⟩, ⟨.and, [13, 8]⟩, ⟨.or, [12, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x02802b03a0000000 0x0067bf03e0000000

def z1 : W := mkw 0x12a42f03a0780e80 0x1b67ff03e07c0fc0

def z2 : W := mkw 0x18301cc314630c28 0x2dabbcc31c638c3c

def z3 : W := mkw 0x1bf03ffbff630c28 0x2dffbfffffe38c3c

def z4 : W := mkw 0x233837ec007fe000 0x071fbffc007ff000

def z5 : W := mkw 0x440100040084c045 0xfffe814d27adc4cf

def z6 : W := mkw 0x804200104a001112 0xfffdc2b2da527b33

def z7 : W := mkw 0x03c03bfbff000000 0x00ffbfffff800000

def z8 : W := mkw 0x12a42f03a0780e80 0x00017e02c0500b00

def z9 : W := mkw 0x13e43ffbff780e80 0x1bfffffffffc0fc0

def z10 : W := mkw 0x9bf23ffbff631d3a 0xfffffffffff3ff3f

def z11 : W := mkw 0x4c1110c41487c06d 0xfffe81cd3fafc4ff

def z12 : W := mkw 0x651910ec0087e045 0xfffe81fd27aff4cf

def z13 : W := mkw 0x000000040004c000 0x07fe814d27adc000

def z14 : W := mkw 0x814210f85f001112 0xfffdc2fedfd27b33

def z15 : W := mkw 0x834233f84a001112 0xfffffffeda527b33

def z16 : W := mkw 0x98721cd35e631d3a 0xfffffef3de73ff3f

def z17 : W := mkw 0xc44300144a84d157 0xffffc3ffffffffff

def z18 : W := mkw 0x6709232c009ce045 0xd254033c239c70c3

def z19 : W := mkw 0x2308232c001ce000 0x0214033c001c7000

def z20 : W := mkw 0x804200104a001112 0xfde9c082da420b33

def z21 : W := mkw 0x0000000000000000 0x071d82b000527000

def z22 : W := mkw 0x673937ec00ffe045 0xffffbffd27fff4cf

def z23 : W := mkw 0x0000000000000000 0x000102b000523000

def z24 : W := mkw 0x10840803a0000e80 0x18604003e0000fc0

def z25 : W := mkw 0x804200104a001112 0xf8e04002da000b33

def z26 : W := mkw 0x014010f85f000000 0x009800fc1f800000

def z27 : W := mkw 0x1024040000780e80 0x1b004000007c0fc0

def z28 : W := mkw 0x03c03bfbff000000 0x1bffbfffffac04c0

def z29 : W := mkw 0x0000000000000000 0x2da9808218420830

def z30 : W := mkw 0x233837e8007b2000 0x00013eb000523000

def z31 : W := mkw 0x03c03bfbff000000 0x07ffbfffffd27000

def z32 : W := mkw 0x987204104a631d3a 0xfffdc2b2da73ff3f

def z33 : W := mkw 0x56a52f07a0fccec5 0xffffff4fe7fdcfcf

def z34 : W := mkw 0x0220270000780000 0x071fbfb0007e7000

def z35 : W := mkw 0x0000000000000000 0x2daa80410421840c

def z36 : W := mkw 0x03c03bfbff000000 0x2dffbfffffa1840c

def z37 : W := mkw 0x033037e800630000 0x051fbffc00638000

def z38 : W := mkw 0x0220270000780000 0x0307bf00007c0000

def z39 : W := mkw 0x46852304a09cc2c5 0xfffec34de7bdc7cf

def z40 : W := mkw 0x804200104a001112 0xe49942b2da527b33

def z41 : W := mkw 0x0000000000000000 0xe498000002004003

def z42 : W := mkw 0x233837ec007fe000 0x00033ffc007fb000

def z43 : W := mkw 0x80c20813ff001112 0xf8e04003ff800b33

def z44 : W := mkw 0x83c23bfbff001112 0xffffffffffd27b33

def z45 : W := mkw 0x32bc2f07a07fee80 0x1f67ff03e07fffc0

def z46 : W := mkw 0x440100040084c045 0xff1e814c002dc4cf

def z47 : W := mkw 0x0000000000000000 0x00fe814d27800000

def z48 : W := mkw 0x47c13bffff84c045 0xffffbfffffadc4cf

def z49 : W := mkw 0x003014c000630000 0x050bbcc000638000

def z50 : W := mkw 0x804200104a001112 0xd2544230c2107303

def z51 : W := mkw 0xc44300144a84d157 0xfffec14fffadcfff

def z52 : W := mkw 0x02842300a0180280 0x12444300e01c03c0

def z53 : W := mkw 0x03803bebb5000000 0x00003c0000000000

def z54 : W := mkw 0x03803bebb5000000 0x00023d4d25800000

def z55 : W := mkw 0x0000000000000000 0x18600001200004c0

def z56 : W := mkw 0xdc731cd75ee7dd7f 0xffffffffffffffff

def z57 : W := mkw 0x18301cc314630c28 0xffffbcc31e63cc3f

def z58 : W := mkw 0x92e62f13ea781f92 0xffffffb3fa7e7ff3

def z59 : W := mkw 0x440100040084c045 0xff000000002dc4cf

def z60 : W := mkw 0x3b383feb147b2c28 0x2dabbef31c73bc3c

def z61 : W := mkw 0x1830040000630c28 0x2d00000000638c3c

def z62 : W := mkw 0x081010c014030028 0x2daa80c11c23843c

def z63 : W := mkw 0x0000000000000000 0x1b65c202c0500b00

def z64 : W := mkw 0x440100040084c045 0xe49a014d27adc4cf

def z65 : W := mkw 0x03c02338eb000000 0x0054033ce3800000

def z66 : W := mkw 0x20380404007fe000 0x07000000007ff000

def z67 : W := mkw 0x0000000000000000 0x1b668101202c04c0

def z68 : W := mkw 0x014018fb5f000000 0x00bbbcff1f800000

def z69 : W := mkw 0x5c31040400e7cc6d 0xff000000006fccff

def z70 : W := mkw 0x673937ec00ffe045 0x00023d4d25ad84cc

def z71 : W := mkw 0x47c1233ceb84c045 0xfffe837de7adc4cf

def z72 : W := mkw 0x211810ec0007e000 0x041800fc0003f000

def z73 : W := mkw 0x000000040004c000 0x07000000002dc000

def z74 : W := mkw 0x12a42f03a0780e80 0x1bffff4fe7fc0fc0

def z75 : W := mkw 0x03c02b3beb000000 0x0077bf3fe3800000

def z76 : W := mkw 0x10200c0300600c00 0x2dabbc8318620c30

def z77 : W := mkw 0x0000000000000000 0x0002014d25800000

def z78 : W := mkw 0x8002000000001112 0xe400000000027033

def z79 : W := mkw 0x1024040000780e80 0x1b66c101207c0fc0

def z80 : W := mkw 0x3b383feb147b2c28 0x00013eb218523830

def z81 : W := mkw 0x00800803a0000000 0x00600003e0000000

def z82 : W := mkw 0x233837ec007fe000 0x07ffbffd27fff000

def z83 : W := mkw 0x233837ec007fe000 0x02163f7c003df000

def z84 : W := mkw 0x77bd3fefa0ffeec5 0xffffffffe7ffffcf

def z85 : W := mkw 0x4401000000800045 0xfffc8001278044cf

def z86 : W := mkw 0x000010c000000000 0x000bbcc000000000

def z87 : W := mkw 0x1830040000630c28 0x000000000021840c

def z88 : W := mkw 0x5c311cc714e7cc6d 0xffffbdcf3fefccff

def z89 : W := mkw 0xc7c33bffff84d157 0xffffffffffffffff

def z90 : W := mkw 0x081010c014030028 0x2da980c21c43883c

def z91 : W := mkw 0x440100040084c045 0x0002014d25ad84cc

def z92 : W := mkw 0x231833ec0007e000 0x041fbffc0003f000

def z93 : W := mkw 0x0000000000000000 0xfffc800002004003

def z94 : W := mkw 0x10840803a0000e80 0x00004002c0000b00

def z95 : W := mkw 0x03c03bfbff000000 0x1bffffffffd00b00

def z96 : W := mkw 0x1bc03bfbff000c28 0x28ffbfffff800c3c

def z97 : W := mkw 0x000000040004c000 0x071e814c002dc000

def z98 : W := mkw 0x4401000000800045 0xf8e00001278004cf

def z99 : W := mkw 0x03c03bfbff000000 0x00013eb2d8000000

def z100 : W := mkw 0x03c03bfbff000000 0x00563f7de7800000

def z101 : W := mkw 0x02a42700a0780280 0x1347ff00e07c03c0

def z102 : W := mkw 0x10c40813ff000e80 0x18e04003ff800fc0

def z103 : W := mkw 0x1800080314000c28 0x28a000031c000c3c

def z104 : W := mkw 0x33ac2f2fa07cee80 0x1b77ff3fe07c7fc0

def z105 : W := mkw 0x23f83fffff7fe000 0x07ffbffffffff000

def z106 : W := mkw 0xa37a37fc4a7ff112 0xfffffffeda7ffb33

def z107 : W := mkw 0x00c00813ff000000 0x00e00003ff800000

def z108 : W := mkw 0x030033ec0004c000 0x071fbffc002dc000

def z109 : W := mkw 0x1bf03ffbff630c28 0x2dabbef3dc638c3c

def z110 : W := mkw 0x92a62f03a0781f92 0xff67ff03e07e7ff3

def z111 : W := mkw 0x23d83bffff07e000 0x04ffbfffff83f000

def z112 : W := mkw 0x000018c314000000 0x00abbcc31c000000

def z113 : W := mkw 0x804200104a001112 0xdb75c232c2507b03

def z114 : W := mkw 0x03803beba0000000 0x007fbfffe0000000

def z115 : W := mkw 0x12a42f03a0780e80 0x0307ff02c07c0b00

def z116 : W := mkw 0x030033e800000000 0x001fbffc00000000

def z117 : W := mkw 0x33bc3fefa07fee80 0x1f7fffffe07fffc0

def z118 : W := mkw 0x1bb03febb5630c28 0x2dabbdcf3de38c3c

def z119 : W := mkw 0x03c43bfbff180280 0x12ffffffff9c03c0

def z120 : W := mkw 0x18301cc314630c28 0x00023c410421840c

def z121 : W := mkw 0x2308232800182000 0x0000023000103000

def z122 : W := mkw 0x20380404007fe000 0x00000000002d8000

def z123 : W := mkw 0x4401000000800045 0x00000001258004cc

def z124 : W := mkw 0x12a42f03a0780e80 0x18627d03e02c0fc0

def z125 : W := mkw 0x0000000000000000 0x0066810120000000

def z126 : W := mkw 0x181018c314030c28 0x2ca800c31c038c3c

def z127 : W := mkw 0x440100040084c045 0xd75e814c23adc0c3

def z128 : W := mkw 0x12842b03a0180e80 0x1a644303e01c0fc0

def z129 : W := mkw 0x804200104a001112 0x000142b2d8523b30

def z130 : W := mkw 0x0000000000000000 0x001e814c00000000

def z131 : W := mkw 0x10240c0300780e80 0x1b23fc03007c0fc0

def z132 : W := mkw 0x47c13bffff84c045 0xe4ffbfffff81c00f

def z133 : W := mkw 0x2108002c0004e000 0x0010003c00007000

def z134 : W := mkw 0x440100040084c045 0xffffc34fe7fdcfcf

def z135 : W := mkw 0x0000000000000000 0x2d00000000420830

def z136 : W := mkw 0x440100040084c045 0xe498004c0781c00f

def z137 : W := mkw 0x67f93fffffffe045 0xffffbffffffff4cf

def z138 : W := mkw 0x004000104a000000 0x00fd82b2da000000

def z139 : W := mkw 0x233837ec007fe000 0x00023d4c002d8000

def z140 : W := mkw 0x673937ec00ffe045 0x071fbffd25fff4cc

def z141 : W := mkw 0x440100040084c045 0xd254010c238c40c3

def z142 : W := mkw 0x00c00010eb000000 0x00400000e3800000

def z143 : W := mkw 0x010010e815000000 0x0000004c05800000

def z144 : W := mkw 0x12a42f03a0780e80 0x00023d01202c04c0

def z145 : W := mkw 0x03803bebb5000000 0x00abbdcf3d800000

def z146 : W := mkw 0x92e62f13ea781f92 0x00017eb2d8523b30

def z147 : W := mkw 0x0000000000000000 0x00658202c0000000

def z148 : W := mkw 0x13e42f3beb780e80 0x1b77ff3fe3fc0fc0

def z149 : W := mkw 0x03f03ffbff630000 0x05ffbfffffe38000

def z150 : W := mkw 0x18301cc314630c28 0x00013c8218420830

def z151 : W := mkw 0x46812b07a084c045 0xffffbf4fe7adc4cf

def z152 : W := mkw 0x081010c014030028 0x248800c01c03803c

def z153 : W := mkw 0x4401000000800045 0xe08000000780000f

def z154 : W := mkw 0x10200c0300600c00 0x0923bc0300600c00

def z155 : W := mkw 0x0000000000000000 0x12440100200c00c0

def z156 : W := mkw 0x233837e8007b2000 0x0307bfb0007e3000

def z157 : W := mkw 0x12a42f03a0780e80 0x1b65fe02c0500b00

def z158 : W := mkw 0x014000384b000000 0x0010003c03800000

def z159 : W := mkw 0x804200104a001112 0xd0404000c2000303

def z160 : W := mkw 0x233837e8007b2000 0x001fbffc00523000

def z161 : W := mkw 0x804200104a001112 0x071dc2b2d8527b30

def z162 : W := mkw 0x230833ec001ce000 0x021fbffc001c7000

def z163 : W := mkw 0x5425040400fccec5 0xff004000007dcfcf

def z164 : W := mkw 0x03c033f8eb000000 0x005fbffce3800000

def z165 : W := mkw 0x0000000000000000 0xfffd82b002527003

def z166 : W := mkw 0x1ab43fc3b47b0ea8 0x3fefffc3fc7f8ffc

def z167 : W := mkw 0x18301cc314630c28 0x3fefbdc33c6f8cfc

def z168 : W := mkw 0x804200104a001112 0xe49800b01a027033

def z169 : W := mkw 0x12a42f03a0780e80 0x00037f03e07c0fc0

def z170 : W := mkw 0x004000104a000000 0x00e00002da000000

def z171 : W := mkw 0x39381cef1467ec28 0x2dbbbcff1c63fc3c

def z172 : W := mkw 0x443114c400e7c045 0xffffbdcd27efc4cf

def z173 : W := mkw 0x00840000a0000280 0x10404000e00003c0

def z174 : W := mkw 0x454110fc5f84c045 0xfffe81fd3fadc4cf

def z175 : W := mkw 0x233837ec007fe000 0x07013eb0007ff000

def z176 : W := mkw 0x000018c314000000 0x00ffbdcf3f800000

def z177 : W := mkw 0x98721cd35e631d3a 0xfdebfcc3de638f3f

def z178 : W := mkw 0x03c03bfbff000000 0xffffbfffff804003

def z179 : W := mkw 0x814210f85f001112 0xe49800fc1f827033

def z180 : W := mkw 0x54850803a0800ec5 0xf8e04003e7800fcf

def z181 : W := mkw 0x03c03bfbff000000 0x00553fbefb800000

def z182 : W := mkw 0x440100040084c045 0xf6dc014c278dc0cf

def z183 : W := mkw 0xa15a10fc4a07f112 0xe49800fc1a03f033

def z184 : W := mkw 0x47c13bfbff800045 0xf8ffbfffff8004cf

def z185 : W := mkw 0x23b83fefb57fe000 0x071fbffd25fff000

def z186 : W := mkw 0x804200104a001112 0x000000b018023030

def z187 : W := mkw 0x440100040084c045 0xf8e2014d27ad84cf

def z188 : W := mkw 0x1024040000780e80 0x00000000002c04c0

def z189 : W := mkw 0x440100040084c045 0xffaa8041042dc4cf

def z190 : W := mkw 0x804200104a001112 0xfcf840b2da027b33

def z191 : W := mkw 0xa34a233c4a1cf112 0xfffdc3beda5e7b33

def z192 : W := mkw 0x13e43ffbff780e80 0x00ffffffffd00b00

def z193 : W := mkw 0x82c62310ea181392 0xd2544330e21c73c3

def z194 : W := mkw 0x440100040084c045 0xc010000c03804003

def z195 : W := mkw 0x238c232ca01ce280 0x1254433ce01c73c0

def z196 : W := mkw 0x3b383fef147fec28 0x2fbfbfff1c7ffc3c

def z197 : W := mkw 0x3bbc3fefb47feea8 0x3ffffffffc7ffffc

def z198 : W := mkw 0x213814ec0067e000 0x051bbcfc0063f000

def z199 : W := mkw 0x83c23bfbff001112 0xd2ffffffff907303

def z200 : W := mkw 0x02842300a0180280 0x1b66c301e03c07c0

def z201 : W := mkw 0x034033f84a000000 0x00ffbffeda000000

def z202 : W := mkw 0x000000040004c000 0x0418004c0001c000

def z203 : W := mkw 0x23c8233ceb1ce000 0x0254033ce39c7000

def z204 : W := mkw 0x8002000000001112 0xf800400000000b33

def z205 : W := mkw 0x885210d05e03113a 0xe49800f01e03f03f

def z206 : W := mkw 0x440100040084c045 0x2daa814d25ad84cc

def z207 : W := mkw 0x030033e800000000 0x071fbffc00527000

def z208 : W := mkw 0x233837ec007fe000 0x1f7ffffec07ffb00

def z209 : W := mkw 0xc44300144a84d157 0xfffe81fd3faff4ff

def z210 : W := mkw 0x1bf03ffbff630c28 0x00ffbfffffc20830

def z211 : W := mkw 0x00301cc314630000 0x05abbcc31c638000

def z212 : W := mkw 0x8002000000001112 0xff00400000527b33

def z213 : W := mkw 0x02842b03a0180280 0x1267ff03e01c03c0

def z214 : W := mkw 0x0020040000600000 0x0103bc0000600000

def z215 : W := mkw 0x0000000000000000 0x18604002c0000b00

def z216 : W := mkw 0x18340400007b0ea8 0x3f004000007f8ffc

def z217 : W := mkw 0x23bc37eca07fe280 0x175ffffce07ff3c0

def z218 : W := mkw 0x5c31040400e7cc6d 0xfffe814d27efccff

def z219 : W := mkw 0x0000000000000000 0x00fc800002000000

def z220 : W := mkw 0x000018c314000000 0x00013c8218000000

def z221 : W := mkw 0x18301cc314630c28 0x3feffec3dc738f3c

def z222 : W := mkw 0x030033e800000000 0x00023d4c00000000

def z223 : W := mkw 0x0000000000000000 0x050a804000218000

def z224 : W := mkw 0x83c23bfbff001112 0xf8ffffffff800b33

def z225 : W := mkw 0x804200104a001112 0xfffcc230c2107303

def z226 : W := mkw 0x18301cc314630c28 0x2d013c8218638c3c

def z227 : W := mkw 0x18301cc314630c28 0x00abbcc31c420830

def z228 : W := mkw 0xc44300144a84d157 0xfffdc2b2da7fffff

def z229 : W := mkw 0x2308232c001ce000 0x071e837c003df000

def z230 : W := mkw 0x02c02b13ea000000 0x00ffbfb3fa000000

def z231 : W := mkw 0x004000104a000000 0x2dfd82b2da420830

def z232 : W := mkw 0x92e62f13ea781f92 0xfffdfeb2da527b33

def z233 : W := mkw 0x6439040400ffe045 0xff000000007ff4cf

def z234 : W := mkw 0xa37a37f84a7b3112 0xfffdfeb2da527b33

def z235 : W := mkw 0x18301cc314630c28 0x2fbfbef31c73fc3c

def z236 : W := mkw 0x00c00813ff000000 0x00000002d8000000

def z237 : W := mkw 0xe77b37fc4afff157 0xffffffffffffffff

def z238 : W := mkw 0x0000000000000000 0x2fbd82b218527830

def z239 : W := mkw 0x440118c71484c045 0xffffbdcf3fadc4cf

def z240 : W := mkw 0x804200144a04d112 0xffffc3feda7ffb33

def z241 : W := mkw 0x12a42f03a0780e80 0x1f7fffb3e07e7fc0

def z242 : W := mkw 0x10200c0300600c00 0x00023c0100200400

def z243 : W := mkw 0x12a42f03a0780e80 0x12467f01e03c07c0

def z244 : W := mkw 0x0000000000000000 0x0000000000000000

def z245 : W := mkw 0x00c00813ff000000 0x00fe814fff800000

def z246 : W := mkw 0x02802b03a0000000 0x00ffbf4fe7800000

def z247 : W := mkw 0x0220270000780000 0x00023d00002c0000

def z248 : W := mkw 0x23f83fffff7fe000 0x00ffbfffffad8000

def z249 : W := mkw 0x13e43ffbff780e80 0x1b67ffb3f87c0fc0

def z250 : W := mkw 0x291810ec1407e028 0x249800fc1c03f03c

def z251 : W := mkw 0x233837ec007fe000 0x02153fbc005e7000

def z252 : W := mkw 0x03c03bfbff000000 0x00e23d4fff800000

def z253 : W := mkw 0x18301cc314630c28 0x28a23c431c218c3c

def z254 : W := mkw 0x804200104a001112 0xff0142b2d8527b33

def z255 : W := mkw 0x003014c000630000 0x00013c8000420000

def z256 : W := mkw 0x02802b03a0000000 0x00023d0120000000

def z257 : W := mkw 0x203814c4007fe000 0x070bbcc0007ff000

def z258 : W := mkw 0x8002000000001112 0xff65c202c0527b33

def z259 : W := mkw 0x440100040084c045 0xe40000000001c00f

def z260 : W := mkw 0x804200104a001112 0xffffc3ffffd27b33

def z261 : W := mkw 0x10840803a0000e80 0x1b66c103e02c0fc0

def z262 : W := mkw 0x003014c000630000 0x071fbef00073f000

def z263 : W := mkw 0x12a02f03a0600c00 0x0967bf03e0600c00

def z264 : W := mkw 0x5c311cc314e30c6d 0xfdebbcc33fe38cff

def z265 : W := mkw 0x8002000000001112 0xff1dc2b000527b33

def z266 : W := mkw 0x18301cc314630c28 0x00abbcc31c21840c

def z267 : W := mkw 0x33bc3feba07b2e80 0x1b67ffb3e07e3fc0

def z268 : W := mkw 0x180018c314000c28 0x28abbcc31c000c3c

def z269 : W := mkw 0x233837e8007b2000 0x050bbef00073b000

def z270 : W := mkw 0x18341cc3147b0ea8 0x3fabfcc31c7f8ffc

def z271 : W := mkw 0x4401000000800045 0xfbe6810127ac04cf

def z272 : W := mkw 0x233837e8007b2000 0x00003c0000000000

def z273 : W := mkw 0x0000000000000000 0x00014202c0500b00

def z274 : W := mkw 0x9026040000781f92 0xff004000007e7ff3

def z275 : W := mkw 0x83c23bfbff001112 0x00ffffffffd23b30

def z276 : W := mkw 0x034033f85f000000 0x009fbffc1f800000

def z277 : W := mkw 0x03803bebb5000000 0x001fbffd25800000

def z278 : W := mkw 0x47c13bffff84c045 0x00ffbfffffad84cc

def z279 : W := mkw 0x0000000000000000 0x00020101202c04c0

def z280 : W := mkw 0x440100040084c045 0xfffc8000022dc4cf

def z281 : W := mkw 0x5c0108071484cc6d 0xfffe814f3fadccff

def z282 : W := mkw 0x0000000000000000 0xf8e0000002000003

def z283 : W := mkw 0x12a42f03a0780e80 0x1b017e02c07c0fc0

def z284 : W := mkw 0x56a52f03a0f80ec5 0xfbe7ff03e7fc0fcf

def z285 : W := mkw 0x00800803b5000000 0x0000000125800000

def z286 : W := mkw 0x2308232c001ce000 0x0000010c000c0000

def z287 : W := mkw 0x804200104a001112 0xfffcc002da004b33

def z288 : W := mkw 0x1024040000780e80 0x1b65c202c07c0fc0

def z289 : W := mkw 0x0000000000000000 0x2dab80c31c638c3c

def z290 : W := mkw 0x23b83fefa07fe000 0x077fbfffe07ff000

def z291 : W := mkw 0x440100040084c045 0xe4fe814d2781c00f

def z292 : W := mkw 0x010010e800000000 0x001800fc00000000

def z293 : W := mkw 0x0200230000000000 0x0007bf0000000000

def z294 : W := mkw 0x03c03bfbff000000 0x0067bfb3f8000000

def z295 : W := mkw 0x22382704007fe000 0x0707bf00007ff000

def z296 : W := mkw 0x03c03bfbff000000 0x001fbffed8000000

def z297 : W := mkw 0x20380400007b2000 0x0000000000523000

def z298 : W := mkw 0x081018c314030028 0x24abbcc31c03803c

def z299 : W := mkw 0x1004000000000e80 0x1800400000000fc0

def z300 : W := mkw 0x5425040400fccec5 0xfffec14d27fdcfcf

def z301 : W := mkw 0x3bf83fffff7fec28 0x2fffbffffffffc3c

def z302 : W := mkw 0x440100040084c045 0xdb76810d23ac44c3

def z303 : W := mkw 0x38380404007fec28 0x2f000000007ffc3c

def z304 : W := mkw 0x98721cd35e631d3a 0x2dabfef3dc73bf3c

def z305 : W := mkw 0x000018c314000000 0x2dabbcc31c420830

def z306 : W := mkw 0x1ab43fc3b47b0ea8 0x00017e82d8520b30

def z307 : W := mkw 0x0220270000780000 0x1b67bf01207c04c0

def z308 : W := mkw 0x03c03bfbff000000 0x00033ffffd800000

def z309 : W := mkw 0x00c018d3ff000000 0x00ebbcc3ff800000

def z310 : W := mkw 0x233837ec007fe000 0x2fbfbffd047ff40c

def z311 : W := mkw 0x0000000000000000 0xfffdc202c2504b03

def z312 : W := mkw 0x440100040084c045 0x00fe814d27ad84cc

def z313 : W := mkw 0x0220270000780000 0x00013e0000500000

def z314 : W := mkw 0x4401000000800045 0xf8fe814d278004cf

def z315 : W := mkw 0x0000000000000000 0xfffe8101222c44c3

def z316 : W := mkw 0x023037c0007b0000 0x070fbfc0007f8000

def z317 : W := mkw 0x1224270000780e80 0x1b07ff00007c0fc0

def z318 : W := mkw 0x23f837fceb7fe000 0x075fbffce3fff000

def z319 : W := mkw 0x47813befb584c045 0xfffebd4d27adc4cf

def z320 : W := mkw 0x804200104a001112 0xd75dc2b0c2527303

def z321 : W := mkw 0x9832040000631d3a 0xff0040000073ff3f

def z322 : W := mkw 0x83c22338eb001112 0xd254433ce3907303

def z323 : W := mkw 0x804200104a001112 0xff544230c2527b33

def z324 : W := mkw 0x004000104a000000 0x000102b2d8000000

def z325 : W := mkw 0x0000000000000000 0x071c800000004000

def z326 : W := mkw 0x92e62f13ea781f92 0xfbe7ff03fa7c0ff3

def z327 : W := mkw 0x804200104a001112 0xf8fdc2b2da000b33

def z328 : W := mkw 0x804200104a001112 0xffffc3b3fa7e7ff3

def z329 : W := mkw 0x804200104a001112 0x1b65c2b2d8523b30

def z330 : W := mkw 0x6709232c009ce045 0xfffe837d27bdf4cf

def z331 : W := mkw 0x804200104a001112 0xe4fd82b2da027033

def z332 : W := mkw 0x804218d35e001112 0xfffffef3de527b33

def z333 : W := mkw 0x0000000000000000 0x2da8800000000000

def z334 : W := mkw 0x13c43bfbff000e80 0x18ffffffff800fc0

def z335 : W := mkw 0x23f83ffbff7b2000 0x00ffbfffffd23000

def z336 : W := mkw 0x33bc3fefa07fee80 0x071ffffec07ffb00

def z337 : W := mkw 0x83c23bfbff001112 0xe4ffbfffff827033

def z338 : W := mkw 0x1800080314000c28 0x0000000218000830

def z339 : W := mkw 0xc44300144a84d157 0xd254433ce39c73c3

def z340 : W := mkw 0x081010c014030028 0x000000400401800c

def z341 : W := mkw 0x18301cc314630c28 0x248a3cc11c23843c

def z342 : W := mkw 0x333c37ec007fee80 0x1f1ffffc007fffc0

def z343 : W := mkw 0x12e42f13ff780e80 0x1be7ff03fffc0fc0

def z344 : W := mkw 0x440100040084c045 0xfaf4010d278c44cf

def z345 : W := mkw 0x13e43ffbff780e80 0x00ffbfffffac04c0

def z346 : W := mkw 0x18301cc314630c28 0x00033cc31c638c3c

def z347 : W := mkw 0x213814ec007fe000 0x071800fc007ff000

def z348 : W := mkw 0x5c311cc714e7cc6d 0x00023d4d25ad84cc

def z349 : W := mkw 0x440100040084c045 0x00000000002d84cc

def z350 : W := mkw 0x10200c0300600c00 0x00013c0200400800

def z351 : W := mkw 0x1800080314000c28 0x2daa80431c218c3c

def z352 : W := mkw 0x18b41cc3b4630ea8 0x3debfcc3fc638ffc

def z353 : W := mkw 0x003014c000630000 0x2dabbcc10463840c

def z354 : W := mkw 0x7f393fef14ffec6d 0xffffbfff3ffffcff

def z355 : W := mkw 0x03803bebb5000000 0x00febd4d27800000

def z356 : W := mkw 0x233837ec007fe000 0x071ebd4c002dc000

def z357 : W := mkw 0x10301cc300630c00 0x0d2bbcc300638c00

def z358 : W := mkw 0x440100040084c045 0xff668101202dc4cf

def z359 : W := mkw 0x1a303fc3147b0c28 0x2fafbfc31c7f8c3c

def z360 : W := mkw 0x804200104a001112 0xe08000001a000033

def z361 : W := mkw 0x233837ec007fe000 0x041a3dfc002ff000

def z362 : W := mkw 0x4c1110c41487c06d 0xe49800cc1f83c03f

def z363 : W := mkw 0x651910ec0087e045 0xe49800fc0783f00f

def z364 : W := mkw 0x5c311cc714e7cc6d 0x2dabbdcf3def8cfc

def z365 : W := mkw 0x10840803a0000e80 0x1b65c203e0500fc0

def z366 : W := mkw 0x02802b03a0000000 0x00013e02c0000000

def z367 : W := mkw 0xd6e72f17eafcdfd7 0xffffffffffffffff

def z368 : W := mkw 0x030033e800000000 0x00ffbffd27800000

def z369 : W := mkw 0x13e43ffbff780e80 0x00017eb2d8500b00

def z370 : W := mkw 0x804200104a001112 0xffe04002da527b33

def z371 : W := mkw 0x23b83fefb57fe000 0x00023d4d25ad8000

def z372 : W := mkw 0x2b3837ec147fe028 0x279fbffc1c7ff03c

def z373 : W := mkw 0x0000000000000000 0x001d82b000000000

def z374 : W := mkw 0xc40300040084d157 0xff004000007fffff

def z375 : W := mkw 0x12a42f03a0780e80 0x18617e03e0500fc0

def z376 : W := mkw 0x0000000000000000 0xd254000002004003

def z377 : W := mkw 0x03c03bfbff000000 0x00fdbeb2da000000

def z378 : W := mkw 0x804200104a001112 0xff9840b01a527b33

def z379 : W := mkw 0x82c62310ea181392 0xfffdc3b2fa5e7bf3

def z380 : W := mkw 0x12a42f03a0780e80 0x0067bf03e02c04c0

def z381 : W := mkw 0x54210c0700e4cc45 0xffffbd4f27edcccf

def z382 : W := mkw 0x0000000000000000 0x248800400401800c

def z383 : W := mkw 0x000000040004c000 0x2fbe814d042dc40c

def z384 : W := mkw 0x12a42f03a0780e80 0x0923bd03206c0cc0

def z385 : W := mkw 0x4401000000800045 0xf8000000000004cf

def z386 : W := mkw 0x02842300a0180280 0x00000100200c00c0

def z387 : W := mkw 0x004000104a000000 0x009800b01a000000

def z388 : W := mkw 0x0000000000000000 0x00e0000127800000

def z389 : W := mkw 0x0000000000000000 0x0098004c07800000

def z390 : W := mkw 0x01c018fbff000000 0x00f800ffff800000

def z391 : W := mkw 0x004000104a000000 0x00ff83ffff800000

def z392 : W := mkw 0x0000000000000000 0x0921800200400800

def z393 : W := mkw 0x10200c0300600c00 0x1b67bd03206c0cc0

def z394 : W := mkw 0x8002000000001112 0xd200400000107303

def z395 : W := mkw 0x003014c40067c000 0x071fbdcc006fc000

def z396 : W := mkw 0x23f83fffff7fe000 0x071fbffed87ff000

def z397 : W := mkw 0x12b43fc3a07b0e80 0x1f6fffc3e07f8fc0

def z398 : W := mkw 0x03c03bffff04c000 0x07ffbfffffadc000

def z399 : W := mkw 0x83c23bfbff001112 0x00017eb2d8523b30

def z400 : W := mkw 0x0000000000000000 0x28a0000218000830

def z401 : W := mkw 0x3b383fef147fec28 0x2dabbdcf1c6f8c3c

def z402 : W := mkw 0x18301cc314630c28 0x2d023c4104638c3c

def z403 : W := mkw 0x2328272c007ce000 0x0317bf3c007c7000

def z404 : W := mkw 0x03803bebb5000000 0x0067bf4fe5800000

def z405 : W := mkw 0x8002000000001112 0xffa9c08218527b33

def z406 : W := mkw 0x2338272c007fe000 0x0714033c007ff000

def z407 : W := mkw 0x0000000000000000 0x12444200c0100300

def z408 : W := mkw 0x804200104a001112 0xffffc2f3de73ff3f

def z409 : W := mkw 0x03e03ffbff780000 0x03ffbffffffc0000

def z410 : W := mkw 0x44c10817ff84c045 0xfffe814fffadc4cf

def z411 : W := mkw 0x18301cc314630c28 0x2daabc410421840c

def z412 : W := mkw 0x83c22338eb001112 0xfffdc3befbd27b33

def z413 : W := mkw 0x12a42f03a0780e80 0x3fefff83f87e0ff0

def z414 : W := mkw 0x440100040084c045 0xffff81cf3fefccff

def z415 : W := mkw 0x804200104a001112 0xf8e142b2da523b33

def z416 : W := mkw 0x0bd03bfbff030028 0x24ffbfffff83803c

def z417 : W := mkw 0x1aa42f03b4780ea8 0x3be7ff03fc7c0ffc

def z418 : W := mkw 0x673937ec00ffe045 0xff1fbffc007ff4cf

def z419 : W := mkw 0x90620c134a601d12 0xfffffeb3da727f33

def z420 : W := mkw 0x18301cc314630c28 0x24893cc21c43883c

def z421 : W := mkw 0xc44300144a84d157 0xfffdc2fedfd3fb3f

def z422 : W := mkw 0x440100040084c045 0xffff83fd27fff4cf

def z423 : W := mkw 0x56a52f07a0fccec5 0xff67ff03e07dcfcf

def z424 : W := mkw 0x804200104a001112 0xe79d82b01a527033

def z425 : W := mkw 0x014010f85f000000 0x00fe81fd3f800000

def z426 : W := mkw 0x0004000000180280 0x12004000001c03c0

def z427 : W := mkw 0x5eb53fc7b4ffceed 0xffffffcfffffcfff

def z428 : W := mkw 0x10200c0300600c00 0x2dabbc4304618c0c

def z429 : W := mkw 0x18301cc314630c28 0x050bbcc218638830

def z430 : W := mkw 0xc44300144a84d157 0xfffdc3befbde7bf3

def z431 : W := mkw 0x18c00813ff000c28 0x28e00003ff800c3c

def z432 : W := mkw 0xa33a37ec007ff112 0xff1ffffc007ffb33

def z433 : W := mkw 0x000000040004c000 0x1f7e814d202dc4c0

def z434 : W := mkw 0x4621270400fcc045 0xffffbf4d27fdc4cf

def z435 : W := mkw 0x4401000000800045 0xd0400000238000c3

def z436 : W := mkw 0x1ab42f03a07b0ea8 0x3f67ff03e07f8ffc

def z437 : W := mkw 0x03c03bfbff000000 0x009a3dfd3f800000

def z438 : W := mkw 0x014010f85f000000 0x00fd82fedf800000

def z439 : W := mkw 0x211810e800032000 0x000000b000023000

def z440 : W := mkw 0x18301cc314630c28 0x00003c0000000000

def z441 : W := mkw 0x12a42f03a0780e80 0xffffff03e27c4fc3

def z442 : W := mkw 0xa37a37f84a7b3112 0x00017eb2d8523b30

def z443 : W := mkw 0x3b3837ec007fec28 0x2f1fbffc007ffc3c

def z444 : W := mkw 0x030033e800000000 0x00013eb000000000

def z445 : W := mkw 0x804200104a001112 0x00004002d8000b30

def z446 : W := mkw 0x0000000000000000 0xfffe814d27804003

def z447 : W := mkw 0x03802328a1000000 0x0000010c21800000

def z448 : W := mkw 0x014010f85f000000 0x000000b018000000

def z449 : W := mkw 0x233837e8007b2000 0x071dbeb000527000

def z450 : W := mkw 0x673937ec00ffe045 0xe79fbffc07fff00f

def z451 : W := mkw 0x90c60813ea001f92 0xf8e04003fa000ff3

def z452 : W := mkw 0x02202704007cc000 0x071fbf4c007dc000

def z453 : W := mkw 0x804200104a001112 0xfffc80b01a027033

def z454 : W := mkw 0x18301cc314630c28 0x2dffbdcf3fe38c3c

def z455 : W := mkw 0x02802300a0000000 0x00440300e0000000

def z456 : W := mkw 0x440100040084c045 0xff98004c07adc4cf

def z457 : W := mkw 0x004000104a000000 0xfffd82b2da004003

def z458 : W := mkw 0x440100040084c045 0xedba804d07a1c40f

def z459 : W := mkw 0x1bf03ffbff630c28 0x00013eb2d8420830

def z460 : W := mkw 0x440100040084c045 0xd256014d27adc4cf

def z461 : W := mkw 0x02a02f03a0780000 0x0367bf03e07c0000

def z462 : W := mkw 0x454110fc5f84c045 0xe49800fc1f81c00f

def z463 : W := mkw 0x1800080314000c28 0x000000010400040c

def z464 : W := mkw 0x3b383fef147fec28 0x071fbffd047ff40c

def z465 : W := mkw 0x0220270000780000 0x1b67ff02c07c0b00

def z466 : W := mkw 0x1020040000600c00 0x0900000000600c00

def z467 : W := mkw 0x0300232800000000 0x0014033c00000000

def z468 : W := mkw 0x440100040084c045 0xff02014d25adc4cf

def z469 : W := mkw 0x0000000000000000 0x2dfe814d27a1840c

def z470 : W := mkw 0x12a42f03a0780e80 0x00003c0000000000

def z471 : W := mkw 0x233837ec007fe000 0x001fbffc002d8000

def z472 : W := mkw 0x10a40c03a0600e80 0x1963fc03e0600fc0

def z473 : W := mkw 0x18301cc314630c28 0x0923bc8318620c30

def z474 : W := mkw 0x0000000000000000 0xff00000000004003

def z475 : W := mkw 0x02c02b13ff000000 0x00e7bf03ff800000

def z476 : W := mkw 0x18300c0300630c28 0x2d23bc0300638c3c

def z477 : W := mkw 0x92e62f13ea781f92 0x1b67ffb3f87e3ff0

def z478 : W := mkw 0xa37a37fc4a7ff112 0xd75ffffcc27ff303

def z479 : W := mkw 0x33fc3fffff7fee80 0x1fffffffffffffc0

def z480 : W := mkw 0x303c0404007fee80 0x1f004000007fffc0

def z481 : W := mkw 0x0000000000000000 0x00aa804104000000

def z482 : W := mkw 0x13a43feba0780e80 0x1b7fffffe07c0fc0

def z483 : W := mkw 0x03c02338eb000000 0x00000230c0000000

def z484 : W := mkw 0x000018c314000000 0x00023c4104000000

def z485 : W := mkw 0x211810ec0007e000 0x071d82fc0053f000

def z486 : W := mkw 0x003014c000630000 0x00023c4000218000

def z487 : W := mkw 0x804200104a001112 0xfbe5c202da500b33

def z488 : W := mkw 0x233837ec007fe000 0x04193efc0053f000

def z489 : W := mkw 0x0000080314000000 0x00a000031c000000

def z490 : W := mkw 0x56a52f07a0fccec5 0x00023d4d25ad84cc

def z491 : W := mkw 0x0000000000000000 0x1b67c303e07c0fc0

def z492 : W := mkw 0x233837ec007fe000 0x2fbfbffe187ff830

def z493 : W := mkw 0xbb7a3fff5e7ffd3a 0xffffffffde7fff3f

def z494 : W := mkw 0x13a43febb5780e80 0x00023d4d25ac04c0

def z495 : W := mkw 0x03c03bfbff000000 0x2dffbfffffc20830

def z496 : W := mkw 0x5c311cc714e7cc6d 0xffabbcc31c6fccff

def z497 : W := mkw 0x18301cc314630c28 0x050bbcc10463840c

def z498 : W := mkw 0x12a42f03a0780e80 0x1b66bd01202c04c0

def z499 : W := mkw 0x0000000000000000 0x2d0000000021840c

def z500 : W := mkw 0x12a42f03a0780e80 0x0067ff03e0500b00

def z501 : W := mkw 0x000000040004c000 0x071f83fc007ff000

def z502 : W := mkw 0x02803bc3b4000000 0x00efbfc3fc000000

def z503 : W := mkw 0x5c311cc714e7cc6d 0xedbbbccf1fe3cc3f

def z504 : W := mkw 0x0000000000000000 0x0509808000420000

def z505 : W := mkw 0x0020040000780000 0x03000000007c0000

def z506 : W := mkw 0x0000000000000000 0x2488008018020030

def z507 : W := mkw 0x03003beb14000000 0x00bfbfff1c000000

def z508 : W := mkw 0x5c01080314800c6d 0xf8e000033f800cff

def z509 : W := mkw 0x201800040007e000 0x040000000003f000

def z510 : W := mkw 0x233837ec007fe000 0xffffbffc027ff003

def z511 : W := mkw 0x23383fef147fe000 0x07bfbfff1c7ff000

def z512 : W := mkw 0x10a40c03a0780e80 0x1b604003e07c0fc0

def z513 : W := mkw 0x33bc3feba07b2e80 0x00017eb2c0523b00

def z514 : W := mkw 0x1ab43fc3b47b0ea8 0x1b67ff43e47d8fcc

def z515 : W := mkw 0x03c03bfbff000000 0x00e13eb3ff800000

def z516 : W := mkw 0x03c03bfbff000000 0x00993efedf800000

def z517 : W := mkw 0x233837ec007fe000 0x0307bf4c007d8000

def z518 : W := mkw 0x083014c014630028 0x258bbcc01c63803c

def z519 : W := mkw 0x984208135e001d3a 0xf8e04003de000f3f

def z520 : W := mkw 0x004000105f000000 0x008000001f800000

def z521 : W := mkw 0x5ff13fffffe7cc6d 0xffffbfffffefccff

def z522 : W := mkw 0x12a42f03a0780e80 0x3fefff43e47d8fcc

def z523 : W := mkw 0x032037e800780000 0x031fbffc007c0000

def z524 : W := mkw 0x807214d04a631112 0xfffffef2da73fb33

def z525 : W := mkw 0x47c13bffff84c045 0xd2ffbfffff8c40c3

def z526 : W := mkw 0x00c00813ff000000 0x00fd82b3ff800000

def z527 : W := mkw 0x03c02338eb000000 0x00fe837de7800000

def z528 : W := mkw 0xa3fa3fffff7ff112 0xfffffffffffffb33

def z529 : W := mkw 0x237837fc4a7fe000 0x07ffbffeda7ff000

def z530 : W := mkw 0x237837fc5f7fe000 0x079fbffc1ffff000

def z531 : W := mkw 0x03c02b3bff000000 0x00f4033fff800000

def z532 : W := mkw 0x18301cc314630c28 0x28a13c831c420c3c

def z533 : W := mkw 0x6439040400ffe045 0xfffe814d27fff4cf

def z534 : W := mkw 0x12a42f03a0780e80 0x1b027d01207c0fc0

def z535 : W := mkw 0x0000000000000000 0x041800b000027000

def z536 : W := mkw 0x02802b03a0000000 0x1b67ff03e0500b00

def z537 : W := mkw 0x000000040004c000 0x0002014c002d8000

def z538 : W := mkw 0x0000000000000000 0x0305820000500000

def z539 : W := mkw 0x46852304a09cc2c5 0xd254430ce39c43c3

def z540 : W := mkw 0x92e62f13ea781f92 0xdb77ff33e27c7fc3

def z541 : W := mkw 0x20080004001ce000 0x02000000001c7000

def z542 : W := mkw 0x233837ec007fe000 0x1f7fbffd207ff4c0

def z543 : W := mkw 0x1ab43fc3b47b0ea8 0x1b67ff83f87e0ff0

def z544 : W := mkw 0x0000000000000000 0x0001008218420830

def z545 : W := mkw 0x98721cd35e631d3a 0xedbbbcf31e63fc3f

def z546 : W := mkw 0xc44300104a801157 0xf8e04003ff800fff

def z547 : W := mkw 0x0810000000030028 0x240000000003803c

def z548 : W := mkw 0x12a42f03a0780e80 0x12457f02e05c0bc0

def z549 : W := mkw 0x12a42f07a07cce80 0x1f7fff4fe07dcfc0

def z550 : W := mkw 0xa37a37fc4a7ff112 0x071ffffed87ffb30

def z551 : W := mkw 0x02802b03a0000000 0x1b67bf03e02c04c0

def z552 : W := mkw 0x440100040084c045 0x071e814d25adc4cc

def z553 : W := mkw 0x47c1233ceb84c045 0xd254033ce38c40c3

def z554 : W := mkw 0x215810fc5f07e000 0x049800fc1f83f000

def z555 : W := mkw 0x673937ec00ffe045 0xd75fbffc23fff0c3

def z556 : W := mkw 0x1830040000630c28 0x2daa804104638c3c

def z557 : W := mkw 0x33383fef007fec00 0x0f3fbfff007ffc00

def z558 : W := mkw 0x0200230000180000 0x02040300001c0000

def z559 : W := mkw 0x02842300a0180280 0x1b65c302e05c0bc0

def z560 : W := mkw 0x10201cc314600c00 0x09abbcc31c600c00

def z561 : W := mkw 0x004000104a000000 0x1bfdc2b2da500b00

def z562 : W := mkw 0x804200104a001112 0xd2fdc2b2da107303

def z563 : W := mkw 0x8002000000001112 0x0000400000523b30

def z564 : W := mkw 0x0000000000000000 0x3fee8141242d84cc

def z565 : W := mkw 0x20380404007fe000 0x071d82b0007ff000

def z566 : W := mkw 0x804200104a001112 0xfaf44232da107b33

def z567 : W := mkw 0x804200104a001112 0xd25542b2da527b33

def z568 : W := mkw 0x0000000000000000 0x1b64800000000000

def z569 : W := mkw 0x183014c000630c28 0x2d0bbcc000638c3c

def z570 : W := mkw 0x02842300a0180280 0x00004200c0100300

def z571 : W := mkw 0x18301cc314630c28 0x0923bc4304618c0c

def z572 : W := mkw 0x5c311cc714e7cc6d 0xfffebd4d27adc4cf

def z573 : W := mkw 0xc44300144a84d157 0xe49800fc1f83f03f

def z574 : W := mkw 0x004000104a000000 0x00540230c2000000

def z575 : W := mkw 0x0000000000000000 0x0922800100200400

def z576 : W := mkw 0x0000000000000000 0x0214023000107000

def z577 : W := mkw 0x0000000000000000 0x1b00400000500b00

def z578 : W := mkw 0x440100040084c045 0xff54010c23adc4cf

def z579 : W := mkw 0x57e53ffffffccec5 0xfffffffffffdcfcf

def z580 : W := mkw 0x98721cd35e631d3a 0x00017eb2d8523b30

def z581 : W := mkw 0x1830040000630c28 0x0000000000420830

def z582 : W := mkw 0x440100040084c045 0xffe0000127adc4cf

def z583 : W := mkw 0x03c033f8ff000000 0x00dc03fcff800000

def z584 : W := mkw 0x18701cd35e630c28 0x2dffbef3de638c3c

def z585 : W := mkw 0x56a52f07a0fccec5 0x1b67ff4fe5fd8fcc

def z586 : W := mkw 0xa37a37fc4a7ff112 0xe79fbffc1a7ff033

def z587 : W := mkw 0x3b383fef147fec28 0x00023d4d042d840c

def z588 : W := mkw 0x18301cc314630c28 0x2da9bc8218420830

def z589 : W := mkw 0x231833ec001fe000 0x061c03fc001ff000

def z590 : W := mkw 0x0000000000000000 0x1b000000002c04c0

def z591 : W := mkw 0x03c03bfbff000000 0x00abbef3dc000000

def z592 : W := mkw 0x33bc3fefa07fee80 0x1b67ff4fe07d8fc0

def z593 : W := mkw 0x804200104a001112 0xedb980b21a427833

def z594 : W := mkw 0x44c10813ff800045 0xf8e00003ff8004cf

def z595 : W := mkw 0x1000080300000c00 0x0820000300000c00

def z596 : W := mkw 0x440100040084c045 0xfffc810c238c40c3

def z597 : W := mkw 0x18300c0314630c28 0x2da000031c638c3c

def z598 : W := mkw 0x80c20813ff001112 0xfffdc2b3ffd27b33

def z599 : W := mkw 0x3b383fef147fec28 0x071fbffe187ff830

def z600 : W := mkw 0x18301cc71467cc28 0x2fbfbdcf1c6fcc3c

def z601 : W := mkw 0x0000000000000000 0x00a9808218000000

def z602 : W := mkw 0x000018c314000000 0x2dabbcc31c21840c

def z603 : W := mkw 0x1bf43ffbff7b0ea8 0x3fffffffffff8ffc

def z604 : W := mkw 0x93e63ffbff781f92 0xfffffffffffe7ff3

def z605 : W := mkw 0xa07a04144a7ff112 0xfffdc2b2da7ffb33

def z606 : W := mkw 0x440100040084c045 0xfffc804c0781c00f

def z607 : W := mkw 0x12202f0300780c00 0x0b27bf03007c0c00

def z608 : W := mkw 0x000010c014000000 0x008800c01c000000

def z609 : W := mkw 0x440100040084c045 0xd2000000000c40c3

def z610 : W := mkw 0x081010c014030028 0x0000008018020030

def z611 : W := mkw 0xb3fe3fffea7fff92 0xfffffffffa7ffff3

def z612 : W := mkw 0x10840803a0000e80 0x00000001200004c0

def z613 : W := mkw 0x1800000000000c28 0x2800000000000c3c

def z614 : W := mkw 0x1b303feb14630c28 0x2dbfbfff1c638c3c

def z615 : W := mkw 0x0000000000000000 0x000200410421840c

def z616 : W := mkw 0x1800080314000c28 0x2da980831c420c3c

def z617 : W := mkw 0x20380404007fe000 0x071e814c007ff000

def z618 : W := mkw 0x000000040004c000 0x0214010c000c4000

def z619 : W := mkw 0x470133ec0084c045 0xffffbffd27adc4cf

def z620 : W := mkw 0x23f83ffbff7b2000 0x00013eb2d8523000

def z621 : W := mkw 0x18200c0314600c28 0x29a3bc031c600c3c

def z622 : W := mkw 0x440100040084c045 0x0000010c218c00c0

def z623 : W := mkw 0x12a43fc3b4780e80 0x1befffc3fc7c0fc0

def z624 : W := mkw 0x18840803b4000ea8 0x38e04003fc000ffc

def z625 : W := mkw 0x12a42f03a0780e80 0x0307bf01207c04c0

def z626 : W := mkw 0x23c83bffff1ce000 0x02ffbfffff9c7000

def z627 : W := mkw 0x9af63fd3fe7b1fba 0xfffffff3fe7fffff

def z628 : W := mkw 0x440100040084c045 0x0000004c0581800c

def z629 : W := mkw 0x233837ec007fe000 0x050bbdcc006f8000

def z630 : W := mkw 0x4401000000800045 0xfdea804127a184cf

def z631 : W := mkw 0x804200104a001112 0x00004230c0103300

def z632 : W := mkw 0x440100040084c045 0xd2fe814d278c40c3

def z633 : W := mkw 0x984208135e001d3a 0xfffdc2b3de527f3f

def z634 : W := mkw 0x12a42700a0780e80 0x1b444300e07c0fc0

def z635 : W := mkw 0x98721cd35e631d3a 0xfffdfeb2da527b33

def z636 : W := mkw 0x1ab03fc3b4630c28 0x2defbfc3fc638c3c

def z637 : W := mkw 0x804200104a001112 0x2da9c2b2d8523b30

def z638 : W := mkw 0x33bc3fefa07fee80 0x071fbffd207ff4c0

def z639 : W := mkw 0x0000000000000000 0x1bfe814d27ac04c0

def z640 : W := mkw 0x000000040004c000 0xfffe814c022dc003

def z641 : W := mkw 0x440100040084c045 0xe79e814c07adc00f

def z642 : W := mkw 0x211810ec0007e000 0x071e81fc002ff000

def z643 : W := mkw 0x1ab43fc3b47b0ea8 0x2dabfec3dc738f3c

def z644 : W := mkw 0x0000000000000000 0xfffd80821a424833

def z645 : W := mkw 0x095010f85f030028 0x249800fc1f83803c

def z646 : W := mkw 0x1024040000780e80 0x0000400000500b00

def z647 : W := mkw 0xc40300040084d157 0xfffec14d27ffffff

def z648 : W := mkw 0xa15a10fc4a07f112 0xfffdc2feda53fb33

def z649 : W := mkw 0x03c02338eb000000 0x00fd83befb800000

def z650 : W := mkw 0x83c23bfbff001112 0xfffdfeb2da527b33

def z651 : W := mkw 0x673937ec00ffe045 0xfffebd4d27adc4cf

def z652 : W := mkw 0x804200104a001112 0x00fdc2b2da523b30

def z653 : W := mkw 0x56a52f07a0fccec5 0xdb77ff0fe3fc4fc3

def z654 : W := mkw 0x12842b03a0000e80 0x1867ff03e0000fc0

def z655 : W := mkw 0x13e03ffbff600c00 0x09ffbfffffe00c00

def z656 : W := mkw 0x804200104a001112 0xc010003002007003

def z657 : W := mkw 0x0800000014000028 0x208000001c00003c

def z658 : W := mkw 0x885210d05e03113a 0xfffdc2f2de53fb3f

def z659 : W := mkw 0x03c42338eb180280 0x1254433ce39c03c0

def z660 : W := mkw 0xc44300104a801157 0xfffdc2b3ffd27fff

def z661 : W := mkw 0x98321cc314631d3a 0xffabfcc31c73ff3f

def z662 : W := mkw 0x18f01cd3ff630c28 0x2debbcc3ffe38c3c

def z663 : W := mkw 0x0000000000000000 0x3fedc282d8520b30

def z664 : W := mkw 0x1ab43fc3b47b0ea8 0x00023d41242d84cc

def z665 : W := mkw 0x003014c000630000 0x2dabbcc218638830

def z666 : W := mkw 0xa34a233c4a1cf112 0xd254433cc21c7303

def z667 : W := mkw 0x2308232c001ce000 0x071d83bc005e7000

def z668 : W := mkw 0xc44300144a84d157 0xfffec37de7bdf7cf

def z669 : W := mkw 0x004000104a000000 0x07fd82b2da527000

def z670 : W := mkw 0x1ab43fc3b47b0ea8 0x2dabbdc33c6f8cfc

def z671 : W := mkw 0x12a42f03a0780e80 0x0923fe03c0700f00

def z672 : W := mkw 0x82c22b13ea001112 0xffffffb3fa527b33

def z673 : W := mkw 0x444100144a84c045 0xffff83ffffadc4cf

def z674 : W := mkw 0x826227104a781112 0xffffffb2da7e7b33

def z675 : W := mkw 0x211810ec0007e000 0x0000004c00018000

def z676 : W := mkw 0x56a52f07a0fccec5 0xfffebd4d27adc4cf

def z677 : W := mkw 0x10200c0300600c00 0x1b67fe03c0700f00

def z678 : W := mkw 0x90c60813ea001f92 0xfffdc2b3fa527ff3

def z679 : W := mkw 0x0000000000000000 0x0054010c23800000

def z680 : W := mkw 0x004018d35e000000 0x00ffbef3de000000

def z681 : W := mkw 0x906604104a781f92 0xfffdc2b2da7e7ff3

def z682 : W := mkw 0x1bb03febb5630c28 0x00023d4d25a1840c

def z683 : W := mkw 0x440100040084c045 0xfcf8004d2781c4cf

def z684 : W := mkw 0x54850807a084cec5 0xfffec14fe7adcfcf

def z685 : W := mkw 0x0000000000000000 0x0700000000527000

def z686 : W := mkw 0x8002000000001112 0xfffcc00002527b33

def z687 : W := mkw 0x233837ec007fe000 0x07023d4c007ff000

def z688 : W := mkw 0x1830040000630c28 0x2da9808218638c3c

def z689 : W := mkw 0x183014c014630c28 0x2d8800c01c638c3c

def z690 : W := mkw 0x38381cc7147fec28 0x2fabbcc31c7ffc3c

def z691 : W := mkw 0x0000000000000000 0x28a000010400040c

def z692 : W := mkw 0x0000080300000000 0x0023bc0300000000

def z693 : W := mkw 0x33bc3fefa07fee80 0x00023d4d202d84c0

def z694 : W := mkw 0x13a43febb5780e80 0x1b67ff4fe5fc0fc0

def z695 : W := mkw 0x0000000000000000 0x03068100002c0000

def z696 : W := mkw 0x47813befb584c045 0x00023d4d25ad84cc

def z697 : W := mkw 0x12e42f13ea780e80 0x1bffffb3fa7c0fc0

def z698 : W := mkw 0x0000000000000000 0x1f7dc2b2c0527b00

def z699 : W := mkw 0x804200104a001112 0xf6dc42b0da127333

def z700 : W := mkw 0x1bf03ffbff630c28 0x00ffbfffffa1840c

def z701 : W := mkw 0x0030040000630000 0x0500000000638000

def z702 : W := mkw 0x440100040084c045 0x1b66814d25ad84cc

def z703 : W := mkw 0x001010c000030000 0x040800c000038000

def z704 : W := mkw 0xa03a0404007ff112 0xff004000007ffb33

def z705 : W := mkw 0x19701cfb5f630c28 0x2dbbbcff1fe38c3c

def z706 : W := mkw 0x0000000000000000 0xfffe80410621c40f

def z707 : W := mkw 0x319c18efa007ee80 0x1c7840ffe003ffc0

def z708 : W := mkw 0x12a42f03a0780e80 0x1963fd03e06c0fc0

def z709 : W := mkw 0x233837ec007fe000 0x04013eb00053f000

def z710 : W := mkw 0x2328272c007ce000 0x02153f3c005c7000

def z711 : W := mkw 0xc44300144a84d157 0x000343fffdffbffc

def z712 : W := mkw 0x653914ec00e7e045 0xedbbbcfd07e3f40f

def z713 : W := mkw 0x83c23bfbff001112 0xd2ffffffffd27b33

def z714 : W := mkw 0x18301cc3147b0c28 0x2fabbcc31c7f8c3c

def z715 : W := mkw 0x18301cc314630c28 0x2dbfbef31c638c3c

def z716 : W := mkw 0x0bd03bfbff030028 0x00ffbfffff820030

def z717 : W := mkw 0x03c03bfbff000000 0x00823d4d3f800000

def z718 : W := mkw 0x18301cc314630c28 0x2defbdc33c638c3c

def z719 : W := mkw 0x20f80c17ff7fe000 0x07e00003fffff000

def z720 : W := mkw 0x440100040084c045 0xfcfa014d27adc4cf

def z721 : W := mkw 0x0220270000780000 0x071dbeb000527000

def z722 : W := mkw 0x443114c400e7c045 0xffffbffd27fff4cf

def z723 : W := mkw 0x804200104a001112 0xdb75c2b2da527b33

def z724 : W := mkw 0x18301cc314630c28 0x2dbbbcf31c63fc3c

def z725 : W := mkw 0x030033e800000000 0x021fbffc00107000

def z726 : W := mkw 0x03c03bfbff000000 0x00f53fbfff800000

def z727 : W := mkw 0x03c03bfbff000000 0x07ffbfffff804000

def z728 : W := mkw 0x0bd03bfbff030028 0x00ffbfffff81800c

def z729 : W := mkw 0x98c20813ff001d3a 0xf8e04003ff800f3f

def z730 : W := mkw 0x12a42f03a0780e80 0x1b65fe02c07c0fc0

def z731 : W := mkw 0x233837e8007b2000 0x07013eb000527000

def z732 : W := mkw 0x67bd37eca0ffe2c5 0xfffffffde7fff7cf

def z733 : W := mkw 0x233837e8007b2000 0x00033ffc00523000

def z734 : W := mkw 0x03803bebb5000000 0x00aabd4d25800000

def z735 : W := mkw 0x673937e800fb2045 0xf8e13eb127d234cf

def z736 : W := mkw 0x18341cc3147b0ea8 0x2dabfcc31c738f3c

def z737 : W := mkw 0x213814ec0067e000 0x071fbdfc006ff000

def z738 : W := mkw 0x233837ec007fe000 0xd75fbffc027ff003

def z739 : W := mkw 0x3b3837ec147fec28 0x2f9fbffc1c7ffc3c

def z740 : W := mkw 0x203814c4007fe000 0x071fbef0007ff000

def z741 : W := mkw 0x183014c014630c28 0x2d8bbcc01c638c3c

def z742 : W := mkw 0x18301cc314630c28 0x24abbcc31c23843c

def z743 : W := mkw 0x180018c314000c28 0x2dabbcc31c218c3c

def z744 : W := mkw 0x13c43bfbff000e80 0x00ffffffff800b00

def z745 : W := mkw 0x18301cc314630c28 0x24013c821843883c

def z746 : W := mkw 0x233837ec007fe000 0x0707bfb0007ff000

def z747 : W := mkw 0x338c2b2fa01cee80 0x1a74433fe01c7fc0

def z748 : W := mkw 0x030033e800000000 0x009fbffc07800000

def z749 : W := mkw 0x6439040400ffe045 0xe7000000007ff00f

def z750 : W := mkw 0x18301cc314630c28 0x00013c8218638c3c

def z751 : W := mkw 0x233837ec007fe000 0xffffbffe1a7ff833

def z752 : W := mkw 0x0a9433c0b41b02a8 0x36cc43c0fc1f83fc

def z753 : W := mkw 0xa37a37fc4a7ff112 0xf8e27d4eda2d8b33

def z754 : W := mkw 0x804200104a001112 0xfffdc2b2da73ff3f

def z755 : W := mkw 0x03843bebb5180280 0x00023d4d258c00c0

def z756 : W := mkw 0x440100040084c045 0xff56014d27adc4cf

def z757 : W := mkw 0x673937ec00ffe045 0xff1fbffd25fff4cf

def z758 : W := mkw 0x12a42f03a0780e80 0x1b77ff33e07c7fc0

def z759 : W := mkw 0x673937ec00ffe045 0x071fbffc21fff0c0

def z760 : W := mkw 0x03c033f8eb000000 0x00563f7ce3800000

def z761 : W := mkw 0xe43b040400fff157 0xff004000007fffff

def z762 : W := mkw 0x03803bebb5000000 0x001a3dfd25800000

def z763 : W := mkw 0x773d37ec00ffeec5 0xff1ffffc007fffcf

def z764 : W := mkw 0x034033f85f000000 0x009a3dfc1f800000

def z765 : W := mkw 0x5425040400fccec5 0x1b004000007d8fcc

def z766 : W := mkw 0x13a42f2ba1780e80 0x1b67ff0fe1fc0fc0

def z767 : W := mkw 0x4431040400e7c045 0xff000000006fc4cf

def z768 : W := mkw 0x807214d04a631112 0xfdebfcc2da638b33

def z769 : W := mkw 0x83823bebb5001112 0xff027d4d25d27b33

def z770 : W := mkw 0x12a42f03a0780e80 0x1f6fff43e07d8fc0

def z771 : W := mkw 0x47c13bffff84c045 0xff013eb2d82dc4cf

def z772 : W := mkw 0x93c63bfbff001f92 0xf8ffffffff800ff3

def z773 : W := mkw 0x984208135e001d3a 0x00004002d8000b30

def z774 : W := mkw 0x116414f85f780e80 0x1b9840fc1ffc0fc0

def z775 : W := mkw 0x230833ec001ce000 0x071fbffc005e7000

def z776 : W := mkw 0xc7c3233ceb84d157 0xd254433ce39c73c3

def z777 : W := mkw 0x03802b2ba1000000 0x00023d0d21800000

def z778 : W := mkw 0x03803bebb5000000 0x00003d0c21800000

def z779 : W := mkw 0x1bf02738eb630c28 0x2d54033ce3e38c3c

def z780 : W := mkw 0x83c63bfbff181392 0xffffffffffde7bf3

def z781 : W := mkw 0x0bc03bfbff000028 0x20ffbfffff80003c

def z782 : W := mkw 0x92e62f13ea781f92 0xe49a3db13a2e74f3

def z783 : W := mkw 0x10a40c03a0600e80 0x1b67fd03e06c0fc0

def z784 : W := mkw 0x02842300a0180280 0x1247ff00e01c03c0

def z785 : W := mkw 0x233837e8007b2000 0x071fbef00073f000

def z786 : W := mkw 0x18301cc314630c28 0x2d893cc21c638c3c

def z787 : W := mkw 0x98721cd35e631d3a 0xd2567e71c631f70f

def z788 : W := mkw 0x18301cc314630c28 0x2fafbdc31c6f8c3c

def z789 : W := mkw 0x18301cc314630c28 0x00013cc21c43883c

def z790 : W := mkw 0x32bc2f03a07b2e80 0x1b67ff03e07e3fc0

def z791 : W := mkw 0x440118c71484c045 0xffabbcc31c2dc4cf

def z792 : W := mkw 0x1ab42f03a07b0ea8 0x1b67ff03e07d8fcc

def z793 : W := mkw 0x333c37ec007fee80 0x1f7ffffd207fffc0

def z794 : W := mkw 0x18301cc314630c28 0x29a3bc431c618c3c

def z795 : W := mkw 0x673937ec00ffe045 0xe49a3dfd27aff4cf

def z796 : W := mkw 0x83c63bfbff181392 0xd2ffffffff9c73c3

def z797 : W := mkw 0x2328272c007ce000 0x02163f3c003c7000

def z798 : W := mkw 0x03803bebb5000000 0x00003c4c05800000

def z799 : W := mkw 0x034033f85f000000 0x00ffbffd3f800000

def z800 : W := mkw 0x02a42f03a0780280 0x1367ff03e07c03c0

def z801 : W := mkw 0x18301cc314630c28 0x2ca93cc31c438c3c

def z802 : W := mkw 0x010018eb15000000 0x00023c4d05800000

def z803 : W := mkw 0x02802b03a0000000 0x00febd4d27800000

def z804 : W := mkw 0x23d83bfbff032000 0x00ffbfffff823000

def z805 : W := mkw 0x673937ec00ffe045 0xffffbfff3ffffcff

def z806 : W := mkw 0x233837ec007fe000 0x041fbffc0053f000

def z807 : W := mkw 0x12a42f03a0780e80 0xffffff4fe7fc4fc3

def z808 : W := mkw 0x233837ec007fe000 0x0f3fbffd007ff400

def z809 : W := mkw 0x004018d35e000000 0x00ffbfffff800000

def z810 : W := mkw 0xcc5310d45e87d17f 0xe49800fc1f83f03f

def z811 : W := mkw 0x2b3837e8147b2028 0x24893ef01c53b03c

def z812 : W := mkw 0x391818ef1407ec28 0x2cb800ff1c03fc3c

def z813 : W := mkw 0x7c39040400ffec6d 0xff000000007ffcff

def z814 : W := mkw 0x233837ec147fe000 0x079fbffc1c7ff000

def z815 : W := mkw 0x030033e800000000 0xffffbffd27d27003

def z816 : W := mkw 0x038033e8a1000000 0x001fbffc21800000

def z817 : W := mkw 0x83c23bfbff001112 0xfdffffffffc20b33

def z818 : W := mkw 0x034033f84a000000 0x00ffbfffff800000

def z819 : W := mkw 0x33ac2f2ba0782e80 0x1b67ff33e07c3fc0

def z820 : W := mkw 0x12a42f03a0780e80 0x1b457f02e07c0fc0

def z821 : W := mkw 0x83c23bfbff001112 0xe7ffbfffffd27033

def z822 : W := mkw 0x032037e800780000 0x071fbffc007e7000

def z823 : W := mkw 0x233837ec007fe000 0xfffffffec27ffb03

def z824 : W := mkw 0x18b41cc3b4630ea8 0x3feffdc3fc6f8ffc

def z825 : W := mkw 0x671933ec0087e045 0xffffbffd27aff4cf

def z826 : W := mkw 0x3b3837e8007b2c28 0x2d013eb00073bc3c

def z827 : W := mkw 0x18301cc314630c28 0xffffbdcf3fe3cc3f

def z828 : W := mkw 0x03c03bfbff000000 0x00e7bf4fff800000

def z829 : W := mkw 0x673937ec00ffe045 0xffffffffe7ffffcf

def z830 : W := mkw 0x213814ec007fe000 0x071bbcfc007ff000

def z831 : W := mkw 0x12a42f03a0780e80 0x1be7ff03e7fc0fc0

def z832 : W := mkw 0x233837e8007b2000 0x071fbffc00527000

def z833 : W := mkw 0x18341cc314630ea8 0x3dabfcc31c638ffc

def z834 : W := mkw 0x12a42f03a0780e80 0x1b67ff4fe5fc0fc0

def z835 : W := mkw 0x673937ec00ffe045 0xffffbffc027ff4cf

def z836 : W := mkw 0x83c23bfbff001112 0xd0ffffffff800303

def z837 : W := mkw 0x333c37ec007fee80 0x1f7ffffec07fffc0

def z838 : W := mkw 0x2b3837ec147fe028 0x071fbffc047ff00c

def z839 : W := mkw 0x440100040084c045 0xf6de014d27adc4cf

def z840 : W := mkw 0x02a42700a0780280 0x12457f00e05c03c0

def z841 : W := mkw 0x804200104a001112 0xffffc2f3de527b33

def z842 : W := mkw 0x233837ec007fe000 0x071fbffd25fff000

def z843 : W := mkw 0x233837ec007fe000 0x071dbeb0007ff000

def z844 : W := mkw 0x03c03bfbff000000 0x09ffbfffffa00400

def z845 : W := mkw 0x12a42f03a0780e80 0x1b67ff43e47d8fcc

def z846 : W := mkw 0x8bd23bfbff03113a 0xffffffffffd3fb3f

def z847 : W := mkw 0x233837ec007fe000 0x051bbefc0073f000

def z848 : W := mkw 0x014018fb5f000000 0x00ffbdff3f800000

def z849 : W := mkw 0x03c03bfbff000000 0x03ffbfffffd00000

def z850 : W := mkw 0x2b3837ec147fe028 0x2fbfbffe1c7ff83c

def z851 : W := mkw 0x984208135e001d3a 0xf8e04002da000b33

def z852 : W := mkw 0x83c23bfbff001112 0xffffbfffff827033

def z853 : W := mkw 0x213814ec0067e000 0x071fbefc0073f000

def z854 : W := mkw 0x83c22b3beb001112 0xffffffbffbd27b33

def z855 : W := mkw 0x03c03bfbff000000 0x00573fffff800000

def z856 : W := mkw 0x83c23bfbff001112 0xe4997efedfd27b33

def z857 : W := mkw 0x081018c314030028 0x248a3cc11c03803c

def z858 : W := mkw 0x081010c014030028 0x248bbcc01c03803c

def z859 : W := mkw 0x231833ec0007e000 0x04193efc0003f000

def z860 : W := mkw 0x0bd03bfbff030028 0x2dffbfffffa3843c

def z861 : W := mkw 0x83c23bfbff001112 0xf6ffffffff927333

def z862 : W := mkw 0x034033f84b000000 0x001fbffc03800000

def z863 : W := mkw 0x56a52f07a0fccec5 0xe4997e4ec7d1cb0f

def z864 : W := mkw 0x03c03bfbff000000 0x28ffbfffff800830

def z865 : W := mkw 0x80c20813ff001112 0x00e04003ff800b30

def z866 : W := mkw 0x183014c000630c28 0x2dabbcc218638c3c

def z867 : W := mkw 0x03c03bfbff000000 0x09ffbfffffc00800

def z868 : W := mkw 0x804200104a001112 0xedb9c2b2da527b33

def z869 : W := mkw 0x18301cc314630c28 0x2dabfec3dc738f3c

def z870 : W := mkw 0x23c83bfbff182000 0x00ffbfffff903000

def z871 : W := mkw 0x18301cc314630c28 0x2dabbdcf3de38c3c

def z872 : W := mkw 0x826227104a781112 0xfbe7ff02da7c0b33

def z873 : W := mkw 0x003014c40067c000 0x071fbffc007ff000

def z874 : W := mkw 0x673937ec00ffe045 0xff9fbffc07fff4cf

def z875 : W := mkw 0x034033f85f000000 0x00ffbffedf800000

def z876 : W := mkw 0x233837e8007b2000 0x00013eb218523830

def z877 : W := mkw 0x12a42f03a0780e80 0xffffff43e67dcfcf

def z878 : W := mkw 0x18b01cc3b5630c28 0x2dabbcc33de38c3c

def z879 : W := mkw 0x03c03bfbff000000 0x28ffbfffff80040c

def z880 : W := mkw 0x233837ec007fe000 0x070bbef0007ff000

def z881 : W := mkw 0x03803bebb5000000 0x2daabd4d25a1840c

def z882 : W := mkw 0x67bd37eca0ffe2c5 0xd75ffffce3fff3c3

def z883 : W := mkw 0x90c60813ea001f92 0xfffec103fa2c4ff3

def z884 : W := mkw 0x03802b2ba1000000 0x0067bf0fe1800000

def z885 : W := mkw 0x18301cc314630c28 0x0923bcc31c638c3c

def z886 : W := mkw 0x83c23bfbff001112 0xffffffffff907303

def z887 : W := mkw 0xd427040400fcdfd7 0xff004000007fffff

def z888 : W := mkw 0x0bd03bfbff030028 0x2dffbfffffc3883c

def z889 : W := mkw 0x00c018d3ff000000 0x00ffbdcfff800000

def z890 : W := mkw 0x12a42f03a0780e80 0x1b67ffb3e07e3fc0

def z891 : W := mkw 0x12a42f03a0780e80 0x1b66fd03e02c0fc0

def z892 : W := mkw 0x02802b03a0000000 0x0067bf4fe5800000

def z893 : W := mkw 0x233837ec007fe000 0x00023dfc002fb000

def z894 : W := mkw 0x03803bebb5000000 0x001ebd4d25800000

def z895 : W := mkw 0x233837e8007b2000 0xfffdbeb002527003

def z896 : W := mkw 0x804200104a001112 0xff65c2b2d8527b33

def z897 : W := mkw 0x673937ec00ffe045 0xe7ffbffd27fff00f

def z898 : W := mkw 0x2b3837ec147fe028 0x071fbffc187ff030

def z899 : W := mkw 0x13c43bfbff000e80 0x1bffffffffac0fc0

def z900 : W := mkw 0x231833ec0007e000 0x071fbffc002ff000

def z901 : W := mkw 0x12a42f03a0780e80 0x1267ff03e03c07c0

def z902 : W := mkw 0x18b41cc3b4630ea8 0x3feffec3fc738ffc

def z903 : W := mkw 0x18300c0314630c28 0x2da3bc031c638c3c

def z904 : W := mkw 0x03c03bfbff000000 0xffffbfffffac44c3

def z905 : W := mkw 0x233837e8007b2000 0x05013eb00073b000

def z906 : W := mkw 0x12a42f03a0780e80 0x1f67ff03e07e7fc0

def z907 : W := mkw 0x83c233f8eb001112 0xd75ffffce3d27303

def z908 : W := mkw 0x03c03bfbff000000 0x00f63f7fff800000

def z909 : W := mkw 0x12a42f03a0780e80 0x0307ff03e07c0fc0

def z910 : W := mkw 0x18301cc314630c28 0xfdebbcc31e638c3f

def z911 : W := mkw 0x18301cc314630c28 0x2d8a3cc11c638c3c

def z912 : W := mkw 0x233837ec007fe000 0x00013eb0007fb000

def z913 : W := mkw 0x440100040084c045 0xffff814f27edcccf

def z914 : W := mkw 0x12a42f03a0780e80 0x1b037f03e07c0fc0

def z915 : W := mkw 0x673937ec00ffe045 0x071fbffc007ff4cc

def z916 : W := mkw 0x233837e8007b2000 0x1b65feb2c0523b00

def z917 : W := mkw 0x18301cc314630c28 0xffabbcc31c63cc3f

def z918 : W := mkw 0x5425040400fccec5 0xdb004000007c4fc3

def z919 : W := mkw 0x10840803a0000e80 0x1f7dc2b3e0527fc0

def z920 : W := mkw 0x03803bebb5000000 0x0066bd4d25800000

def z921 : W := mkw 0x6729272c00fce045 0xffffbf7d27fdf4cf

def z922 : W := mkw 0x9bc23bfbff001d3a 0xffffffffffd27f3f

def z923 : W := mkw 0x804200104a001112 0xc01142b2da527b33

def z924 : W := mkw 0x333837ec007fec00 0x0f1fbffc007ffc00

def z925 : W := mkw 0x03803bebb5000000 0x008a3dcd3d800000

def z926 : W := mkw 0x83c23bfbff001112 0xdbffffffffd07b03

def z927 : W := mkw 0x03c03bfbff000000 0x03ffbfffffac0000

def z928 : W := mkw 0x18301cc314630c28 0x2dabbdc33c6f8cfc

def z929 : W := mkw 0x984208135e001d3a 0x28a04003dc000f3c

def z930 : W := mkw 0x12a42f03a0780e80 0x00027f01e03c07c0

def z931 : W := mkw 0x440100040084c045 0xfffe81cd3fafc4ff

def z932 : W := mkw 0x804200104a001112 0xffa9c2b2d8527b33

def z933 : W := mkw 0x0b903bebb5030028 0x248a3dcd3d83803c

def z934 : W := mkw 0x18301cc314630c28 0x3fabfcc31c738f3c

def z935 : W := mkw 0x1224270000780e80 0x1b67ff02c07c0fc0

def z936 : W := mkw 0x1bc03bfbff000c28 0x2dffbfffffa18c3c

def z937 : W := mkw 0x233837e8007b2000 0x00017eb2c0523b00

def z938 : W := mkw 0x12a42f03a0780e80 0xdb77ff03e27c4fc3

def z939 : W := mkw 0x233837ec007fe000 0x279fbffc047ff00c

def z940 : W := mkw 0x12b42f03a07b0e80 0x1f67ff03e07f8fc0

def z941 : W := mkw 0x03c03bfbff000000 0x1fffffffffd27b00

def z942 : W := mkw 0x804218d35e001112 0xffffffffffd27b33

def z943 : W := mkw 0x333c37e8007b2e80 0x00017eb000523b00

def z944 : W := mkw 0x5c31040400e7cc6d 0x00000000002d84cc

def z945 : W := mkw 0x6f3937ec14ffe06d 0xe79fbffc1ffff03f

def z946 : W := mkw 0x233837ec007fe000 0x07bfbffe187ff000

def z947 : W := mkw 0x030033e800000000 0x041fbffc00027000

def z948 : W := mkw 0x3b3837ec007fec28 0x071fbffc007ff40c

def z949 : W := mkw 0x12a42f03b5780e80 0x1b67ff03e5fc0fc0

def z950 : W := mkw 0x12a42f03a0780e80 0x1a657f03e05c0fc0

def z951 : W := mkw 0x3b082b2f141cec28 0x2ab4033f1c1c7c3c

def z952 : W := mkw 0x1aa42f03b4780ea8 0x3fefff83fc7e0ffc

def z953 : W := mkw 0x233837ec007fe000 0x00123d7c002df000

def z954 : W := mkw 0x38381cc3147b2c28 0x2dabbcc31c73bc3c

def z955 : W := mkw 0x90c60813ff001f92 0xf8e04003ff800ff3

def z956 : W := mkw 0x5425040400fccec5 0xfffdc202c27dcfcf

def z957 : W := mkw 0x03803bebb5000000 0x0023bd4f25800000

def z958 : W := mkw 0x12a42f03a0780e80 0x1f7fff03e07c4fc0

def z959 : W := mkw 0x233837ec007fe000 0x1f1ffffc007ffb00

def z960 : W := mkw 0x1b803bebb5000c28 0x00023d4d2580040c

def z961 : W := mkw 0x5c31040400e7cc6d 0xff000000002dc4cf

def z962 : W := mkw 0x440100040084c045 0xffe2014d27adc4cf

def z963 : W := mkw 0x18301cc314630c28 0x3fffbdcf3fef8cfc

def z964 : W := mkw 0x233837e8007b2000 0x00033ef00073b000

def z965 : W := mkw 0x233837ec007fe000 0x07ffbffc027ff000

def z966 : W := mkw 0x014018fb5f000000 0x009a3cfd1f800000

def z967 : W := mkw 0x12a42f03a0780e80 0x12477f03e07c0fc0

def z968 : W := mkw 0x83c23bfbff001112 0xf8ffffffffd23b33

def z969 : W := mkw 0x233837e8007b2000 0x0509beb000523000

def z970 : W := mkw 0x440100040084c045 0xdb76814d27adc4cf

def z971 : W := mkw 0xdc7304144ae7dd7f 0xfffdc2b2da7fffff

def z972 : W := mkw 0x014018fb5f000000 0x00993cfe1f800000

def z973 : W := mkw 0x18301cc314630c28 0x050bbcc31c638c3c

def z974 : W := mkw 0x804200104a001112 0xfffdc2b2da7e7ff3

def z975 : W := mkw 0x804200104a001112 0xd20142b2d8527b33

def z976 : W := mkw 0x083014c014630028 0x2dabbcc21c63883c

def z977 : W := mkw 0x804200104a001112 0xfaf542b2da527b33

def z978 : W := mkw 0x02802b03a0000000 0x0077bf0fe3800000

def z979 : W := mkw 0x12a42f03a0780e80 0x1b7fff4fe07c0fc0

def z980 : W := mkw 0x18341cc3147b0ea8 0x3feffec3dc7f8ffc

def z981 : W := mkw 0x233837e8007b2000 0x04093ef00053b000

def z982 : W := mkw 0x0200230000000000 0x071fbfb000527000

def z983 : W := mkw 0x233837ec007fe000 0x07163f7c007ff000

def z984 : W := mkw 0x233837e8007b2000 0x051fbffc0073b000

def z985 : W := mkw 0x233837ec007fe000 0x279fbffc187ff030

def z986 : W := mkw 0x034033f85f000000 0x00993efc1f800000

def z987 : W := mkw 0x804200104a001112 0xffffc3fffffe7ff3

def z988 : W := mkw 0x233837ec007fe000 0xffffbffd27fff003

def z989 : W := mkw 0x18301cc314630c28 0x2fafbec31c738c3c

def z990 : W := mkw 0x440100040084c045 0xffff83ff3ffffcff

def z991 : W := mkw 0x03c033f8eb000000 0x00553fbce3800000

def z992 : W := mkw 0x1bc03bfbff000c28 0x00ffbfffff80040c

def z993 : W := mkw 0x12a42f03a0780e80 0x00027d03e02c0fc0

def z994 : W := mkw 0x18301cc314630c28 0x2fabbcc31c73fc3c

def z995 : W := mkw 0x03803bebb5000000 0x007fbfffe5800000

def z996 : W := mkw 0x12a42f03a0780e80 0x1b65ff02e05c0bc0

def z997 : W := mkw 0x673937ec00ffe045 0xe71fbffc007ff00f

def z998 : W := mkw 0x03803bebb5000000 0x071fbffd25d27000

def z999 : W := mkw 0x213814e800632000 0x00013cb000423000

def z1000 : W := mkw 0x233837ec007fe000 0x071dbefc0053f000

def z1001 : W := mkw 0x5c31040400e7cc6d 0xfffd80821a6fccff

def z1002 : W := mkw 0x3b3837ec007fec28 0x2fbfbffe187ffc3c

def z1003 : W := mkw 0x2b3837ec007fe028 0x271fbffc007ff03c

def z1004 : W := mkw 0x1aa42f03b4780ea8 0x3fefff43fc7d8ffc

def z1005 : W := mkw 0x80c20813ea001112 0xf8e04003fa000b33

def z1006 : W := mkw 0x03803bebb5000000 0x00bfbfff3d800000

def z1007 : W := mkw 0x233837e8007b2000 0x070fbff0007fb000

def z1008 : W := mkw 0x440100040084c045 0xe082014d27ad84cf

def z1009 : W := mkw 0x6439040400ffe045 0xd7000000007ff0c3

def z1010 : W := mkw 0x12a42f03a0780e80 0x1347ff02e07c0bc0

def z1011 : W := mkw 0x233837ec007fe000 0x0f3fbffe007ff800

def z1012 : W := mkw 0x804200104a001112 0xfffdc2f2de53fb3f

def z1013 : W := mkw 0x1bd03bfbff030c28 0x2cffbfffff838c3c

def z1014 : W := mkw 0x743d040400ffeec5 0xff004000007fffcf

def z1015 : W := mkw 0x83c23bfbff001112 0x1bffffffffd23b30

def z1016 : W := mkw 0xe47b04144afff157 0xfffdc2b2da7fffff

def z1017 : W := mkw 0x12842b03a0000e80 0x1b67ff03e02c0fc0

def z1018 : W := mkw 0x83c23bfbff001112 0xfcffffffff827b33

def z1019 : W := mkw 0x90c60813ea001f92 0x00004002d8000b30

def z1020 : W := mkw 0x12a42f03a0780e80 0x3be7ff03e47c0fcc

def z1021 : W := mkw 0x03c03bfbff000000 0x00013fbef9800000

def z1022 : W := mkw 0x233837ec007fe000 0x07153fbc007ff000

def z1023 : W := mkw 0x231833ec0007e000 0x041a3dfc0003f000

def z1024 : W := mkw 0x804200104a001112 0xfffdc3befbd27b33

def z1025 : W := mkw 0x13c03bfbff000c00 0x08ffbfffff800c00

def z1026 : W := mkw 0x23bc37eca07fe280 0x071fbffc207ff0c0

def z1027 : W := mkw 0x231833e800032000 0x001fbffc00023000

def z1028 : W := mkw 0x18341cc3147b0ea8 0x2dabbcc31c6f8cfc

def z1029 : W := mkw 0x804200104a001112 0xfffdc3b2fa5e7bf3

def z1030 : W := mkw 0x440100040084c045 0xfffec14fe7adcfcf

def z1031 : W := mkw 0x038033e8a1000000 0x00023d4c21800000

def z1032 : W := mkw 0x233837ec007fe000 0x071fbffd207ff4c0

def z1033 : W := mkw 0x03c02b3beb000000 0x00ffbfbffb800000

def z1034 : W := mkw 0x03c03bfbff000000 0x00fdbfbefb800000

def z1035 : W := mkw 0x030033ec0004c000 0x071fbffc007ff000

def z1036 : W := mkw 0x003014c000630000 0x00013eb000523000

def z1037 : W := mkw 0x233837ec007fe000 0x3fffbffd247ff4cc

def z1038 : W := mkw 0x02c02b13ea000000 0x00ffbfffff800000

def z1039 : W := mkw 0xdc4308175e84dd7f 0xfffec14fffadcfff

def z1040 : W := mkw 0x83c23bfbff001112 0xfbffffffffd00b33

def z1041 : W := mkw 0x8bd23bfbff03113a 0xe4ffbfffff83f03f

def z1042 : W := mkw 0x440100040084c045 0xd2fe814d27adc4cf

def z1043 : W := mkw 0x5421040400e4cc45 0xff000000006dcccf

def z1044 : W := mkw 0x83c23bfbff001112 0x00ffffffff800b30

def z1045 : W := mkw 0x18301cc314630c28 0xfffffec3de73cf3f

def z1046 : W := mkw 0x12a42f03a0780e80 0x3be7ff03f87c0ff0

def z1047 : W := mkw 0x233837ec007fe000 0x2f1fbffc007ff830

def z1048 : W := mkw 0x804200104a001112 0xfffdc2b3fa527ff3

def z1049 : W := mkw 0x03c03bfbff000000 0x00023dfd3d800000

def z1050 : W := mkw 0x030033e800000000 0x001fbffc00523000

def z1051 : W := mkw 0x1bc43bfbff000ea8 0x38ffffffff800ffc

def z1052 : W := mkw 0x18b01cc3b4630c28 0x2debbcc3fc638c3c

def z1053 : W := mkw 0x233837ec007fe000 0x1f7fbffc007ff000

def z1054 : W := mkw 0x4621270400fcc045 0xffffbffd27fff4cf

def z1055 : W := mkw 0x804200104a001112 0xd75dc2b2da527b33

def z1056 : W := mkw 0x083014c014630028 0x2dabbcc11c63843c

def z1057 : W := mkw 0x6f3937ec14ffe06d 0xffffbffd3ffff4ff

def z1058 : W := mkw 0x18300c0300630c28 0x2dabbc8318638c3c

def z1059 : W := mkw 0x231833ec001fe000 0x061fbffc001ff000

def z1060 : W := mkw 0x03c03bfbff000000 0xffffffffffd04b03

def z1061 : W := mkw 0x003014c000630000 0x071dbeb000527000

def z1062 : W := mkw 0x804200104a001112 0xff1dc2b2d8527b33

def z1063 : W := mkw 0x233837ec007fe000 0x050bbffc007fb000

def z1064 : W := mkw 0x03c03bfbff000000 0xf8ffbfffff800003

def z1065 : W := mkw 0x13a42f2ba0780e80 0x1b77ff3fe07c0fc0

def z1066 : W := mkw 0x5425040400fccec5 0x00000000002d84cc

def z1067 : W := mkw 0x83c23bfbff001112 0xfffffffffff3ff3f

def z1068 : W := mkw 0x03c03bfbff000000 0x00febdfd3f800000

def z1069 : W := mkw 0x834233f84a001112 0xffffffffffd27b33

def z1070 : W := mkw 0x03c03bfbff000000 0x00ffbfffffac04c0

def z1071 : W := mkw 0x440100040084c045 0xd042014d27ad84cf

def z1072 : W := mkw 0x230833ec001ce000 0x071fbffc003df000

def z1073 : W := mkw 0x12a42f03a0780e80 0x3fefff03e07c0fc0

def z1074 : W := mkw 0x03803bebb5000000 0x1b66bd4d25ac04c0

def z1075 : W := mkw 0x03c43bfbff000280 0x10ffffffff8003c0

def z1076 : W := mkw 0x03c03bfbff000000 0x1bffbfffff800000

def z1077 : W := mkw 0x233837e8007b2000 0x00003cb000023000

def z1078 : W := mkw 0x1aa42f03b4780ea8 0x1b67ff03f87c0ff0

def z1079 : W := mkw 0x03c03bfbff000000 0x00ffbfffffd23000

def z1080 : W := mkw 0x000018c314000000 0x00abbdcf3d800000

def z1081 : W := mkw 0x18301cc314630c28 0x3ffffef3dc73ff3c

def z1082 : W := mkw 0xd4c70813ea801fd7 0xf8e04003ff800fff

def z1083 : W := mkw 0x233837ec007fe000 0x041b3ffc007ff000

def z1084 : W := mkw 0x081018c314030028 0x24893cc21c03803c

def z1085 : W := mkw 0x90c60813ea001f92 0xf8e04002da000b33

def z1086 : W := mkw 0x233837e8007b2000 0x0007bfb000523000

def z1087 : W := mkw 0x18200c0314600c28 0x2dabbc431c618c3c

def z1088 : W := mkw 0x5425040400fccec5 0xff000000002dc4cf

def z1089 : W := mkw 0x18301cc314630c28 0x28a33cc31c638c3c

def z1090 : W := mkw 0x083014c014630028 0x24893cc01c43803c

def z1091 : W := mkw 0x4421040400fcc045 0xff000000007dc4cf

def z1092 : W := mkw 0x233837ec007fe000 0x02173ffc007ff000

def z1093 : W := mkw 0x83c23bfbff001112 0xffffffffff804b33

def z1094 : W := mkw 0x18301cc314630c28 0x28abbcc31c218c3c

def z1095 : W := mkw 0x83c23bfbff001112 0xf8e27d4fff800b33

def z1096 : W := mkw 0x83c233f8eb001112 0xfffffffefbd27b33

def z1097 : W := mkw 0x83c23bfbff001112 0xedffbfffffc27833

def z1098 : W := mkw 0x18301cc314630c28 0x258bbcc21c63883c

def z1099 : W := mkw 0x18301cc314630c28 0x2da13c831c638c3c

def z1100 : W := mkw 0x18301cc314630c28 0x2da23c431c638c3c

def z1101 : W := mkw 0x233837ec007fe000 0x071ebf7c003df000

def z1102 : W := mkw 0x03843bebb5180280 0x12467f4de59c03c0

def z1103 : W := mkw 0x18301cc314630c28 0xffffbdc33e6fccff

def z1104 : W := mkw 0x18301cc314630c28 0x2daabc431c218c3c

def z1105 : W := mkw 0x12a42f03a0780e80 0x3f67ff03e07e0ff0

def z1106 : W := mkw 0x233837ec157fe000 0x071fbffc05fff000

def z1107 : W := mkw 0x02842b03a0180280 0x12467f01e01c03c0

def z1108 : W := mkw 0x233837ec007fe000 0x061d3ffc005ff000

def z1109 : W := mkw 0x081018c314030028 0x2dabbcc31c23843c

def z1110 : W := mkw 0x83c23bfbff001112 0xe4ffffffffd27b33

def z1111 : W := mkw 0x03c03bfbff000000 0x00abbffffd800000

def z1112 : W := mkw 0x83c23bfbff001112 0xc0ffbfffff807003

def z1113 : W := mkw 0x673937ec00ffe045 0xff7fbffd207ff4cf

def z1114 : W := mkw 0x02842b03a0180280 0x12457f02e01c03c0

def z1115 : W := mkw 0x03403bfb5f000000 0x00bfbfff1f800000

def z1116 : W := mkw 0x83c23bfbff001112 0xe0ffbfffff800033

def z1117 : W := mkw 0x5c31040400e7cc6d 0x2d000000006f8cfc

def z1118 : W := mkw 0x03c03bfbff000000 0x00bbbdff3f800000

def z1119 : W := mkw 0x80c20813ff001112 0xfffec14fff804b33

def z1120 : W := mkw 0x10200c0300600c00 0x2dabbcc31c638c3c

def z1121 : W := mkw 0x03c03bfbff000000 0x00ebbdcfff800000

def z1122 : W := mkw 0x233837e8007b2000 0x0103beb000723000

def z1123 : W := mkw 0x03803bebb5000000 0x00033dcf3d800000

def z1124 : W := mkw 0x5c311cc714e7cc6d 0xd2553d8e3bce48f3

def z1125 : W := mkw 0x18301cc314630c28 0x00023c431c218c3c

def z1126 : W := mkw 0x440100040084c045 0xfffe814d27fff4cf

def z1127 : W := mkw 0x03c03bfbff000000 0x24ffbfffff820030

def z1128 : W := mkw 0x03803bebb5000000 0x00efbfcffd800000

def z1129 : W := mkw 0x2b3837e8147b2028 0x00013eb018523030

def z1130 : W := mkw 0x440100040084c045 0xfffe81fd27aff4cf

def z1131 : W := mkw 0x03803bebb5000000 0x00033ffd25800000

def z1132 : W := mkw 0x13e42738eb780e80 0x1b54433ce3fc0fc0

def z1133 : W := mkw 0x19301ceb14630c28 0x2dbbbcff1c638c3c

def z1134 : W := mkw 0x12a42f03a0780e80 0x1267ff03e05c0bc0

def z1135 : W := mkw 0x233837ec007fe000 0x0317bf7c007df000

def z1136 : W := mkw 0x440100040084c045 0xfaf6014d27adc4cf

def z1137 : W := mkw 0x233837ec007fe000 0x07193efc007ff000

def z1138 : W := mkw 0x03803bebb5000000 0x00ffbdcf3f800000

def z1139 : W := mkw 0x18341cc3147b0ea8 0x3feffdc33c7f8ffc

def z1140 : W := mkw 0x03c03bfbff000000 0x02ffbfffff907000

def z1141 : W := mkw 0x1aa42f03b4780ea8 0x1b67ff03e47c0fcc

def z1142 : W := mkw 0x39381ceb14632c28 0x2dabbcf31c63bc3c

def z1143 : W := mkw 0x03c43bfbff180280 0x00ffbfffff8c00c0

def z1144 : W := mkw 0x12a42f03a0780e80 0x1347ff01e07c07c0

def z1145 : W := mkw 0x230833ec001ce000 0x02163f7c001c7000

def z1146 : W := mkw 0x23bc37e8a07b2280 0x12457fb0e05e33c0

def z1147 : W := mkw 0x03c02338eb000000 0x0057bf3ce3800000

def z1148 : W := mkw 0x233837e8007b2000 0x2da9beb218523830

def z1149 : W := mkw 0x03803bebb5000000 0x00623d4fe5800000

def z1150 : W := mkw 0x03c03bfbff000000 0x005fbffefb800000

def z1151 : W := mkw 0x233837ec007fe000 0xff1fbffc007ff003

def z1152 : W := mkw 0x83c23bfbff001112 0x07ffffffffd27b30

def z1153 : W := mkw 0x233837e8007b2000 0x04193eb000527000

def z1154 : W := mkw 0x03803bebb5000000 0x00a23d4f3d800000

def z1155 : W := mkw 0x03803bebb5000000 0x1b67ff4fe5d00b00

def z1156 : W := mkw 0x6439040400ffe045 0x00000000002d84cc

def z1157 : W := mkw 0x0220270000780000 0xffffbfb1227e74c3

def z1158 : W := mkw 0x233837ec007fe000 0x00013efc0053b000

def z1159 : W := mkw 0x3b3837ec007fec28 0x2fbfbffd047ffc3c

def z1160 : W := mkw 0x1ab42f03a07b0ea8 0x3fefff83f87f8ffc

def z1161 : W := mkw 0x03c43bfbff180280 0x00ffffffff900300

def z1162 : W := mkw 0x12a42f03a0780e80 0x10427d01e02c07c0

def z1163 : W := mkw 0xe55b10fc4a87f157 0xe49800fc1f83f03f

def z1164 : W := mkw 0x12a42f03a0780e80 0xfbe7ff03e27c0fc3

def z1165 : W := mkw 0x233837ec007fe000 0x061e3ffc003ff000

def z1166 : W := mkw 0x03c03bfbff000000 0xd2ffbfffff804003

def z1167 : W := mkw 0x033037e800630000 0x071fbffc0073f000

def z1168 : W := mkw 0x1b803bebb5000c28 0x28a23d4f3d800c3c

def z1169 : W := mkw 0x233837ec007fe000 0x071a3dfc007ff000

def z1170 : W := mkw 0x3b3c37ec007feea8 0x3f1ffffc007ffffc

def z1171 : W := mkw 0x804200104a001112 0xe40142b2d8527b33

def z1172 : W := mkw 0x12a42f03a0780e80 0x12017e02c05c0bc0

def z1173 : W := mkw 0x18301cc314630c28 0x248b3cc31c638c3c

def z1174 : W := mkw 0x014018fb5f000000 0x00ffbeffdf800000

def z1175 : W := mkw 0x83c23bfbff001112 0xd2567f7de7907303

def z1176 : W := mkw 0x233837e8007b2000 0x071fbfb0007e7000

def z1177 : W := mkw 0x6439040400ffe045 0x07000000007ff4cc

def z1178 : W := mkw 0x01c018fbff000000 0x00fbbcffff800000

def z1179 : W := mkw 0x233837e8007b2000 0x00003e3000103000

def z1180 : W := mkw 0x233837ec007fe000 0xe79fbffc027ff003

def z1181 : W := mkw 0x0220270000780000 0x0307bfb0007e3000

def z1182 : W := mkw 0x233837ec007fe000 0x079fbffc07fff000

def z1183 : W := mkw 0x230833ec0004e000 0x001fbffc00007000

def z1184 : W := mkw 0xc6c72314ea9cd3d7 0xd254433ce39c73c3

def z1185 : W := mkw 0xe74b233c4a9cf157 0xd254433ce39c73c3

def z1186 : W := mkw 0x03c03bfbff000000 0x00983cfc1f800000

def z1187 : W := mkw 0x233837ec007fe000 0x0307bffc007fb000

def z1188 : W := mkw 0x804200104a001112 0xfffdc2b3de527f3f

def z1189 : W := mkw 0x80c20813ff001112 0xd0e04003ff800303

def z1190 : W := mkw 0x18b41cc3b4630ea8 0x2dabfcc3dc638f3c

def z1191 : W := mkw 0x440100040084c045 0xfffec14d27fdcfcf

def z1192 : W := mkw 0x6439040400ffe045 0xfffd82b0027ff4cf

def z1193 : W := mkw 0x003014c000630000 0x051bbcf00063f000

def z1194 : W := mkw 0x333c37ec007fee80 0x071fbffc007ff4c0

def z1195 : W := mkw 0x23b837eca17fe000 0x071fbffc21fff000

def z1196 : W := mkw 0x12a42f03a0780e80 0x1b23fe03c07c0fc0

def z1197 : W := mkw 0x83c23bfbff001112 0x00037ffffdd23b30

def z1198 : W := mkw 0x9bc23bfbff001d3a 0xf8ffffffff800f3f

def z1199 : W := mkw 0x2338272c007fe000 0x0717bf3c007ff000

def z1200 : W := mkw 0x181018c314030c28 0x2cabbcc31c038c3c

def z1201 : W := mkw 0x1ab42f03a07b0ea8 0x3fefff43e47f8ffc

def z1202 : W := mkw 0x83c23bfbff001112 0x00ffbfffff823030

def z1203 : W := mkw 0x233837ec007fe000 0x021fbffc003df000

def z1204 : W := mkw 0x03d03bfbff030000 0x04ffbfffff838000

def z1205 : W := mkw 0x231833ec0007e000 0x071fbffc0053f000

def z1206 : W := mkw 0x030033e800000000 0x00013eb000523000

def z1207 : W := mkw 0x13843bebb5000e80 0x18627d4fe5800fc0

def z1208 : W := mkw 0x804200104a001112 0xfffdc2fedfd27b33

def z1209 : W := mkw 0x03803bebb5000000 0x00ffbffd27800000

def z1210 : W := mkw 0x83c23bfbff001112 0x2dffffffffd23b30

def z1211 : W := mkw 0x233837ec007fe000 0x00113ebc00527000

def z1212 : W := mkw 0x83c23bfbff001112 0xfffffffffffe7ff3

def z1213 : W := mkw 0x5c31040400e7cc6d 0xed0000000063cc3f

def z1214 : W := mkw 0x03803bebb5000000 0x00023d4d25a1840c

def z1215 : W := mkw 0x12a42f03a0780e80 0x3fffff4fe7fd8fcc

def z1216 : W := mkw 0x18301cc314630c28 0x24abbcc31c43883c

def z1217 : W := mkw 0x02803bc3b4000000 0x00ffbfcfff800000

def z1218 : W := mkw 0x03c03bfbff000000 0x18ffbfffff8004c0

def z1219 : W := mkw 0x10200c0300600c00 0x1b67ff03e07c0fc0

def z1220 : W := mkw 0x18301cc314630c28 0x2d0bbcc218638c3c

def z1221 : W := mkw 0x18301cc314630c28 0x00abbcc31c638c3c

def z1222 : W := mkw 0x83c23bfbff001112 0x00ffffffff903300

def z1223 : W := mkw 0x1bc03bfbff000c28 0x2dffbfffffc20c3c

def z1224 : W := mkw 0x233837ec007fe000 0x07bfbffd047ff000

def z1225 : W := mkw 0x03c03bfbff000000 0x00ffffffffd00b00

def z1226 : W := mkw 0x03c03bfbff000000 0x05ffbfffffa18000

def z1227 : W := mkw 0x03803beba0000000 0x00ffbfffe7800000

def z1228 : W := mkw 0x03c03bfbff000000 0x0077bfbffb800000

def z1229 : W := mkw 0x83c23bfbff001112 0xfaffffffff907b33

def z1230 : W := mkw 0x440100040084c045 0xfdea814d27ad84cf

def z1231 : W := mkw 0x03c03bfbff000000 0x001fbffffd800000

def z1232 : W := mkw 0x470133ec0084c045 0xffffbffd27fff4cf

def z1233 : W := mkw 0x233c37ec007fe280 0x171ffffc007ff3c0

def z1234 : W := mkw 0x233837ec007fe000 0x02013eb0005e7000

def z1235 : W := mkw 0x02802b03a0000000 0x1b67ff03e07c0fc0

def z1236 : W := mkw 0x233837ec007fe000 0x0317bfbc007e7000

def z1237 : W := mkw 0x1aa42f03a0780ea8 0x3b67ff03e07c0ffc

def z1238 : W := mkw 0x673937ec00ffe045 0xefbfbffd07fff40f

def z1239 : W := mkw 0x230833e800182000 0x001fbffc00103000

def z1240 : W := mkw 0x03c03bfbff000000 0x05ffbfffffc20000

def z1241 : W := mkw 0x231833e800032000 0x00013eb000023000

def z1242 : W := mkw 0x18301cc314630c28 0x3fefffc3fc7f8ffc

def z1243 : W := mkw 0x670933ec009ce045 0xffffbffd27bdf4cf

def z1244 : W := mkw 0x197014f85f630c28 0x2d9800fc1fe38c3c

def z1245 : W := mkw 0x03c03bfbff000000 0x24ffbfffff81800c

def z1246 : W := mkw 0x13c43bfbff000e80 0x1bffffffffd00fc0

def z1247 : W := mkw 0x773d37ec00ffeec5 0xfffffffd27ffffcf

def z1248 : W := mkw 0xc4c30813ff801157 0xf8e04003ff800fff

def z1249 : W := mkw 0x233837ec007fe000 0x071dbfbc005e7000

def z1250 : W := mkw 0x440100040084c045 0xfffe837d27bdf4cf

def z1251 : W := mkw 0x03c03bfbff000000 0x0067bffffd800000

def z1252 : W := mkw 0x233837e8007b2000 0x0305beb000523000

def z1253 : W := mkw 0x233837ec007fe000 0x00023f7c003db000

def z1254 : W := mkw 0x03c02b3bff000000 0x00f7bf3fff800000

def z1255 : W := mkw 0x673937ec00ffe045 0xd2563f7d27bdf4cf

def z1256 : W := mkw 0x440100040084c045 0xffff834fe7adc4cf

def z1257 : W := mkw 0x233837e8007b2000 0x00ffbffd27d23000

def z1258 : W := mkw 0x233837ec007fe000 0x175fbffc207ff0c0

def z1259 : W := mkw 0xd4c70817ea84dfd7 0xfffec14fffadcfff

def z1260 : W := mkw 0xdc33040400e7dd7f 0xff004000007fffff

def z1261 : W := mkw 0x10a40c03a0780e80 0x1b63fc03e07c0fc0

def z1262 : W := mkw 0x18301cc314630c28 0x2dabbef31c73bc3c

def z1263 : W := mkw 0x10240c0300780e80 0x1b67fe03c07c0fc0

def z1264 : W := mkw 0x03c03bfbff000000 0x2fffbfffffd27830

def z1265 : W := mkw 0x12a42f03a0780e80 0xff67ff03e07c4fc3

def z1266 : W := mkw 0x030033e800000000 0x001fbffd25800000

def z1267 : W := mkw 0x440100040084c045 0xc012014d27adc4cf

def z1268 : W := mkw 0x673937ec00ffe045 0xd75fbffd27fff4cf

def z1269 : W := mkw 0x804200104a001112 0xf6dd42b2da527b33

def z1270 : W := mkw 0x233837e8007b2000 0x02153eb000527000

def z1271 : W := mkw 0x03c033f8eb000000 0x00ffbffefb800000

def z1272 : W := mkw 0x13c43bfbff180e80 0x1affffffff9c0fc0

def z1273 : W := mkw 0x233837ec007fe000 0xffffbffd227ff4c3

def z1274 : W := mkw 0x233837ec007fe000 0x1fffbffd27fff4c0

def z1275 : W := mkw 0x804200104a001112 0xffe142b2da527b33

def z1276 : W := mkw 0x03c03bfbff000000 0x12ffbfffff8c00c0

def z1277 : W := mkw 0x673937ec00ffe045 0xe4993efc07d3f00f

def z1278 : W := mkw 0x2328272c007ce000 0x071fbf7c007df000

def z1279 : W := mkw 0x03c03bfbff000000 0xffffbfffffa1c40f

def z1280 : W := mkw 0x02842b03a0180280 0x1b67ff03e03c07c0

def z1281 : W := mkw 0x12a42f03b4780e80 0x1be7ff03fc7c0fc0

def z1282 : W := mkw 0x03803bebb5000000 0x00e23d4d27800000

def z1283 : W := mkw 0x03803bebb5000000 0xfffebd4d27804003

def z1284 : W := mkw 0x03c03bfbff000000 0x00fa3dffff800000

def z1285 : W := mkw 0x804208135e001112 0xf8e04003de000b33

def z1286 : W := mkw 0x673937ec00ffe045 0x07ffbffd27fff4cc

def z1287 : W := mkw 0x03c03bfbff000000 0xffffbfffffc24833

def z1288 : W := mkw 0x230833e800182000 0x00013eb000103000

def z1289 : W := mkw 0xc54310fc5f84d157 0xe49800fc1f83f03f

def z1290 : W := mkw 0x6729272c00fce045 0xdb77bf3d23fc74c3

def z1291 : W := mkw 0x030033e800000000 0x005fbffc23800000

def z1292 : W := mkw 0x673937ec00ffe045 0xffbfbffd047ff4cf

def z1293 : W := mkw 0x673937ec00ffe045 0xffffbffc07fff00f

def z1294 : W := mkw 0x02842b03a0180280 0x1b67ff03e05c0bc0

def z1295 : W := mkw 0x233837ec007fe000 0x071fbffd047ff40c

def z1296 : W := mkw 0x003014c000630000 0xffffbef10673f40f

def z1297 : W := mkw 0x22382704007fe000 0x071fbfb0007ff000

def z1298 : W := mkw 0x23b837eca07fe000 0x075fbffce07ff000

def z1299 : W := mkw 0x233837e8007b2000 0x000bbef000523000

def z1300 : W := mkw 0x18301cc314630c28 0x258bbcc11c63843c

def z1301 : W := mkw 0x12a42f03a0780e80 0x00017e02c07c0fc0

def z1302 : W := mkw 0x02a42700a0780280 0x12467f00e03c03c0

def z1303 : W := mkw 0x804200104a001112 0xffffc3feda527b33

def z1304 : W := mkw 0x1830040000630c28 0x2dfe814d27e38c3c

def z1305 : W := mkw 0x233837ec007fe000 0x2fbfbfff1c7ffc3c

def z1306 : W := mkw 0x80c20813ff001112 0xf8e04002da000b33

def z1307 : W := mkw 0x18301cc314630c28 0x3debfcc3dc638f3c

def z1308 : W := mkw 0x440100040084c045 0xfffe814f3fadccff

def z1309 : W := mkw 0x440100040084c045 0xfffe814d27efccff

def z1310 : W := mkw 0x03c03bfbff000000 0x00023d4ffd800000

def z1311 : W := mkw 0x232837ec007ce000 0x031fbffc007c7000

def z1312 : W := mkw 0x1024040000780e80 0x1bfec14d27fc0fc0

def z1313 : W := mkw 0x233837e8007b2000 0x00153fbc00523000

def z1314 : W := mkw 0x030033e800000000 0x071dbeb000527000

def z1315 : W := mkw 0x233837e8007b2000 0x00033fb0007e3000

def z1316 : W := mkw 0x081018c314030028 0x2dabbcc31c43883c

def z1317 : W := mkw 0x19301ceb15630c28 0x2dabbccf1de38c3c

def z1318 : W := mkw 0x804200104a001112 0xffffc2f2da73fb33

def z1319 : W := mkw 0x03c03bfbff000000 0x00113ebedb800000

def z1320 : W := mkw 0x03803bebb5000000 0x0007bf4d25800000

def z1321 : W := mkw 0x12a42f03a0780e80 0x1b07ff02c07c0fc0

def z1322 : W := mkw 0x233837ec007fe000 0x2fbfbffc007ff000

def z1323 : W := mkw 0x02c02b13ff000000 0x00ffbf4fff800000

def z1324 : W := mkw 0x233837e8007b2000 0x1b67bfb1207e34c0

def z1325 : W := mkw 0x12a42f03a0780e80 0x18637f03e07c0fc0

def z1326 : W := mkw 0x18301cc314630c28 0x2da9bc8218638c3c

def z1327 : W := mkw 0x814218fb5f001112 0xfffffeffdfd27b33

def z1328 : W := mkw 0x233837e8007b2000 0x02053fb0005e3000

def z1329 : W := mkw 0x1ab42f03b47b0ea8 0x3fe7ff03fc7f8ffc

def z1330 : W := mkw 0x80c20813ff001112 0xe0e00003ff800033

def z1331 : W := mkw 0x18301cc314630c28 0x2dffbcc31e638c3c

def z1332 : W := mkw 0x030033e800000000 0x00023d4d25800000

def z1333 : W := mkw 0x03c03bfbff000000 0x005fbffde7800000

def z1334 : W := mkw 0x03003beb14000000 0x00ffbfff3f800000

def z1335 : W := mkw 0x80c20813ff001112 0x00004002d8000b30

def z1336 : W := mkw 0x18301cc314630c28 0x2dbbbccf1fe38c3c

def z1337 : W := mkw 0x18301cc314630c28 0x2caa3cc31c238c3c

def z1338 : W := mkw 0x03c03bfbff000000 0x00013efedd800000

def z1339 : W := mkw 0x18301cc314630c28 0x2fbfbcc31c63cc3c

def z1340 : W := mkw 0x18301cc314630c28 0x2defbec3dc638c3c

def z1341 : W := mkw 0x03803bebb5000000 0x2dabbdcf3dc20830

def z1342 : W := mkw 0x03c03bfbff180000 0x02ffbfffff9c0000

def z1343 : W := mkw 0x834233f85f001112 0xe79fbffc1fd27033

def z1344 : W := mkw 0x0020040000600000 0x071fbeb000727000

def z1345 : W := mkw 0x1bc03bfbff000c28 0x00ffbfffff800830

def z1346 : W := mkw 0x03c03bfbeb000000 0x007fbfffe3800000

def z1347 : W := mkw 0x834233f85f001112 0xfffffffedfd27b33

def z1348 : W := mkw 0x12a42f03a0780e80 0x00017f02e05c0bc0

def z1349 : W := mkw 0x12a42f03a0780e80 0x3f67ff03e07d8fcc

def z1350 : W := mkw 0x03c033f8ff000000 0x00dfbffcff800000

def z1351 : W := mkw 0x030033e815000000 0x001fbffc05800000

def z1352 : W := mkw 0x03c03bfbff000000 0x1bfffffffffc0fc0

def z1353 : W := mkw 0x3b3837ec007fec28 0x071fbffc007ff830

def z1354 : W := mkw 0x03803bebb5000000 0x009a3d4d27800000

def z1355 : W := mkw 0x12a42f03a0780e80 0x1a667f03e03c0fc0

def z1356 : W := mkw 0x023037c0007b0000 0x071fbff0007ff000

def z1357 : W := mkw 0x000018c314000000 0xffffbdcf3fc24833

def z1358 : W := mkw 0x673937ec00ffe045 0x071fbffc05fff00c

def z1359 : W := mkw 0x03c03bfbff000000 0x00023f7de5800000

def z1360 : W := mkw 0x233837ec007fe000 0x2fffbffd27fff40c

def z1361 : W := mkw 0x03c03bfbff000000 0x00fdbefedf800000

def z1362 : W := mkw 0x233837e8007b2000 0x03013eb0007e3000

def z1363 : W := mkw 0x12a42f03a0780e80 0x1b77ff0fe3fc0fc0

def z1364 : W := mkw 0x2328272c007ce000 0x071fbfbc007e7000

def z1365 : W := mkw 0x18301cc314630c28 0x20823c411c21843c

def z1366 : W := mkw 0x18301cc314630c28 0x2daabcc11c23843c

def z1367 : W := mkw 0x03c03bfbff000000 0x00123d7d27800000

def z1368 : W := mkw 0x440100040084c045 0xffffc3cfffffcfff

def z1369 : W := mkw 0x03c03bfbff000000 0x00febd4fff800000

def z1370 : W := mkw 0x23bc37eca07fe280 0x071ffffcc07ff300

def z1371 : W := mkw 0x000018c314000000 0x00bbbccf1f800000

def z1372 : W := mkw 0x12a42f03a0780e80 0x0923ff03e07c0fc0

def z1373 : W := mkw 0x03c03bfbff000000 0xffffbfffffd27003

def z1374 : W := mkw 0x03c03bfbff000000 0x00febf7de7800000

def z1375 : W := mkw 0x440100040084c045 0xffff81cf3fadc4cf

def z1376 : W := mkw 0x03c03bfbff000000 0x3fffbfffffad84cc

def z1377 : W := mkw 0x03803bebb5000000 0x00163f7d25800000

def z1378 : W := mkw 0x673937ec00ffe045 0xfffebdfd27aff4cf

def z1379 : W := mkw 0x440100040084c045 0xffff81cd27efc4cf

def z1380 : W := mkw 0x03803bebb5000000 0x00463f4de5800000

def z1381 : W := mkw 0x003014c000630000 0x2dabbcc31c638c3c

def z1382 : W := mkw 0x12a42f03a0780e80 0x3fefffc3fc7f8ffc

def z1383 : W := mkw 0x93c63bfbff001f92 0xffffffffffd27ff3

def z1384 : W := mkw 0x0b903bebb5030028 0x00023d4d2581800c

def z1385 : W := mkw 0x03c02b3beb000000 0x00ffbf7fe7800000

def z1386 : W := mkw 0x233837ec007fe000 0x041fbffc002ff000

def z1387 : W := mkw 0x18301cc314630c28 0x2debbcc33fe38c3c

def z1388 : W := mkw 0x233837ec007fe000 0x00013fbc005e3000

def z1389 : W := mkw 0x12a42f03a0780e80 0x12447f00e01c03c0

def z1390 : W := mkw 0x440100040084c045 0xffff834d27fdc4cf

def z1391 : W := mkw 0x83c23bfbff001112 0xfffdffbefbd27b33

def z1392 : W := mkw 0x673937ec00ffe045 0xfffebf7d27bdf4cf

def z1393 : W := mkw 0x440100040084c045 0xffff83fd27adc4cf

def z1394 : W := mkw 0x984208135e001d3a 0xfffec043de21cf3f

def z1395 : W := mkw 0x230833ec001ce000 0x02153fbc001c7000

def z1396 : W := mkw 0x03c03bfbff000000 0x12ffffffff900300

def z1397 : W := mkw 0x010018eb15000000 0x00abbccf1d800000

def z1398 : W := mkw 0x03c03bfbff000000 0x00bbbeffdf800000

def z1399 : W := mkw 0x03c03bfbff000000 0x2dffbfffff800000

def z1400 : W := mkw 0x440100040084c045 0xedba814d27adc4cf

def z1401 : W := mkw 0x233837ec007fe000 0x021fbffc005e7000

def z1402 : W := mkw 0x18301cc314630c28 0x24883cc01c03803c

def z1403 : W := mkw 0x12a42f03a0780e80 0x1867ff03e02c0fc0

def z1404 : W := mkw 0xc4c30817ff84d157 0xfffec14fffadcfff

def z1405 : W := mkw 0x000018c314000000 0x2dabbcc31c638c3c

def z1406 : W := mkw 0x904208134a001d12 0xf8e04003da000f33

def z1407 : W := mkw 0x03c43bfbff180280 0x1bffffffffbc07c0

def z1408 : W := mkw 0x12a42f03a0780e80 0x1b66ff01e03c07c0

def z1409 : W := mkw 0x12a42f03a0780e80 0x1befff43e47c0fc0

def z1410 : W := mkw 0x03c02b3beb000000 0x00563f3de3800000

def z1411 : W := mkw 0x673937ec00ffe045 0x2fbfbffd25fff4cc

def z1412 : W := mkw 0x03c03bfbff000000 0x00543f3ce3800000

def z1413 : W := mkw 0x673937ec00ffe045 0xd7ffbffd27fff0c3

def z1414 : W := mkw 0x03c03bfbff000000 0x18ffffffff800b00

def z1415 : W := mkw 0x233837ec007fe000 0x1f1fbffc007ff4c0

def z1416 : W := mkw 0x7f3937ec00ffec6d 0xffffbffd27fffcff

def z1417 : W := mkw 0x671933ec0087e045 0xe4ffbffd2783f00f

def z1418 : W := mkw 0x03c02b3beb000000 0x00553f3ee3800000

def z1419 : W := mkw 0x0220270000780000 0x0317bf30007c7000

def z1420 : W := mkw 0x233837ec007fe000 0x02143f3c001c7000

def z1421 : W := mkw 0x804200104a001112 0xff9942b2da527b33

def z1422 : W := mkw 0x670933ec009ce045 0xd2ffbffd279c70c3

def z1423 : W := mkw 0x1800080314000c28 0x2fbd82b31c527c3c

def z1424 : W := mkw 0x12a42f03a0780e80 0x3fffffb3f87e7ff0

def z1425 : W := mkw 0x03c43bfbff180280 0x1bffffffffdc0bc0

def z1426 : W := mkw 0x0220270000780000 0x1b67ff03e07c0fc0

def z1427 : W := mkw 0x03803bebb5000000 0x00033f4fe5800000

def z1428 : W := mkw 0x03c03bfbff000000 0x00ffbfffffa1840c

def z1429 : W := mkw 0x233837ec007fe000 0x001fbffc007fb000

def z1430 : W := mkw 0x673937ec00ffe045 0xff013eb0007ff4cf

def z1431 : W := mkw 0x83c23bfbff001112 0xd7ffffffffd27303

def z1432 : W := mkw 0x83c23bfbff001112 0xd2557fbefbd27b33

def z1433 : W := mkw 0x12a42f03a0780e80 0x0067ff03e07c0fc0

def z1434 : W := mkw 0x03c03bfbff000000 0x00ffbfffffc20830

def z1435 : W := mkw 0x18b41cc3b4630ea8 0x2dabbcc33c638cfc

def z1436 : W := mkw 0x02202704007cc000 0x071fbffc007ff000

def z1437 : W := mkw 0x12a42f03a0780e80 0x1b627d03e07c0fc0

def z1438 : W := mkw 0x18301cc314630c28 0x00023cc11c23843c

def z1439 : W := mkw 0x673937ec00ffe045 0xdf7fbffd23fff4c3

def z1440 : W := mkw 0x233837e8007b2000 0x031fbffc007e3000

def z1441 : W := mkw 0x03803bebb5000000 0x00ffbf4fe7800000

def z1442 : W := mkw 0x673937ec00ffe045 0xe79fbffd27fff4cf

def z1443 : W := mkw 0x33bc37eca07fee80 0x1f5ffffce07fffc0

def z1444 : W := mkw 0x000018c314000000 0x00023d4d25800000

def z1445 : W := mkw 0x673937ec00ffe045 0xc71fbffc03fff003

def z1446 : W := mkw 0x673937ec00ffe045 0xffffbffc23fff0c3

def z1447 : W := mkw 0x233837ec007fe000 0x071ffffec07ffb00

def z1448 : W := mkw 0x90c60813ea001f92 0x18604003f8000ff0

def z1449 : W := mkw 0x03c03bfbff000000 0x00f93effff800000

def z1450 : W := mkw 0x46812b07a084c045 0xff67bf03e02dc4cf

def z1451 : W := mkw 0x12a42f03a0780e80 0x1b7fffb3e07c0fc0

def z1452 : W := mkw 0x233837ec007fe000 0x075fbffc23fff000

def z1453 : W := mkw 0x804200104a001112 0xffffc3b2da7e7b33

def z1454 : W := mkw 0x03c03bfbff000000 0x009fbffd3f800000

def z1455 : W := mkw 0x000018c314000000 0x00febd4d27800000

def z1456 : W := mkw 0x08301cc314630028 0x25abbcc31c63803c

def z1457 : W := mkw 0x673937ec00ffe045 0x1f7fbffd25fff4cc

def z1458 : W := mkw 0x03c033f8eb000000 0x00ffbffde7800000

def z1459 : W := mkw 0x653914ec00e7e045 0xffffbdfd27eff4cf

def z1460 : W := mkw 0x23bc37eca07fe280 0x1f7ffffde07ff7c0

def z1461 : W := mkw 0x18301cc314630c28 0xffffbef31e73fc3f

def z1462 : W := mkw 0x0000080300000000 0x00ffbd4f27800000

def z1463 : W := mkw 0x003014c000630000 0x050bbef00073b000

def z1464 : W := mkw 0x03c03bfbff000000 0x009fbffedf800000

def z1465 : W := mkw 0x0200230000000000 0x00ffbf4d27800000

def z1466 : W := mkw 0x12a42f03a0780e80 0x1b467f01e07c0fc0

def z1467 : W := mkw 0x12a42700a0780e80 0x1b47ff00e07c0fc0

def z1468 : W := mkw 0x440100040084c045 0xf8fe814d27ad84cf

def z1469 : W := mkw 0x804200104a001112 0xffffc2b3da727f33

def z1470 : W := mkw 0x673937ec00ffe045 0x00033ffd25ffb4cc

def z1471 : W := mkw 0x804200104a001112 0xd2fdc2b2da527b33

def z1472 : W := mkw 0x083014c014630028 0x248a3cc01c23803c

def z1473 : W := mkw 0x03c03bfbff000000 0x00423d4de7800000

def z1474 : W := mkw 0x000010c000000000 0x071fbef000527000

def z1475 : W := mkw 0x12a42f03a0780e80 0xffffffb3e27e7fc3

def z1476 : W := mkw 0x233837ec007fe000 0x175ffffcc07ff300

def z1477 : W := mkw 0x2328272800782000 0x00013e3000503000

def z1478 : W := mkw 0x03c03bfbff000000 0x04ffbfffff827000

def z1479 : W := mkw 0x82c22b13ea001112 0xffffffffffd27b33

def z1480 : W := mkw 0x03c03bfbff000000 0xe4ffbfffff804003

def z1481 : W := mkw 0x02a42700a0780280 0x1b67ff02e07c0bc0

def z1482 : W := mkw 0x804200104a001112 0xff5542b2da527b33

def z1483 : W := mkw 0x02a42700a0780280 0x1b67ff01e07c07c0

def z1484 : W := mkw 0x233837e8007b2000 0x001dbeb000523000

def z1485 : W := mkw 0x83c23bfbff001112 0xe49a3dfd3f827033

def z1486 : W := mkw 0x5c35040400ffceed 0xff004000007fcfff

def z1487 : W := mkw 0x440100040084c045 0xe79e814d27adc4cf

def z1488 : W := mkw 0x030033e815000000 0x00023d4c05800000

def z1489 : W := mkw 0x233837ec007fe000 0x3ffffffed87ffb30

def z1490 : W := mkw 0x98c60813fe001fba 0xf8e04003fe000fff

def z1491 : W := mkw 0x673937ec00ffe045 0xd2553fbc23de70c3

def z1492 : W := mkw 0x90c60813ea001f92 0xd8604003e2000fc3

def z1493 : W := mkw 0x233837ec007fe000 0x051bbdfc006ff000

def z1494 : W := mkw 0x03803bebb5000000 0x00563d4d27800000

def z1495 : W := mkw 0x233837ec007fe000 0x077fbffd207ff000

def z1496 : W := mkw 0x213814e800632000 0x050bbcf00063b000

def z1497 : W := mkw 0x233837ec007fe000 0x071fbffe187ff830

def z1498 : W := mkw 0x673937ec00ffe045 0xf7dfbffc27fff0cf

def z1499 : W := mkw 0x13c43bfbff000e80 0x00ffbfffff8004c0

def z1500 : W := mkw 0x673937ec00ffe045 0xd71fbffc007ff0c3

def z1501 : W := mkw 0x440100040084c045 0xfffec34de7bdc7cf

def z1502 : W := mkw 0x233837e8007b2000 0x2dabbef10473b40c

def z1503 : W := mkw 0x7f3937ec00ffec6d 0xff1fbffc007ffcff

def z1504 : W := mkw 0x2328272800782000 0x0307bf30007c3000

def z1505 : W := mkw 0x233837ec007fe000 0x2f1fbffc007ff40c

def z1506 : W := mkw 0x18301cc314630c28 0x3debbcc33c638cfc

def z1507 : W := mkw 0x18301cc314630c28 0x3fefbcc31c638c3c

def z1508 : W := mkw 0x1ab42f03a07b0ea8 0x1b67ff03e07e0ff0

def z1509 : W := mkw 0x18b41cc3b47b0ea8 0x3febfcc3fc7f8ffc

def z1510 : W := mkw 0x233837ec007fe000 0xffffbffd067ff40f

def z1511 : W := mkw 0x030033e800000000 0x00febd4d27800000

def z1512 : W := mkw 0x12a42f03a0780e80 0x1befff83f87c0fc0

def z1513 : W := mkw 0x03c03bfbff000000 0x3fffffffffd20b30

def z1514 : W := mkw 0x233837ec0067e000 0x051fbffc0063f000

def z1515 : W := mkw 0x333c37e8007b2e80 0x1b017eb0007e3fc0

def z1516 : W := mkw 0x03c03bfbff000000 0x00de3ffdff800000

def z1517 : W := mkw 0x233837e8007b2000 0x00193efc00523000

def z1518 : W := mkw 0x804200104a001112 0xffffc3fffff3ff3f

def z1519 : W := mkw 0x2b3837ec147fe028 0x2fbfbffd1c7ff43c

def z1520 : W := mkw 0x014010f85f000000 0x009bbcfc1f800000

def z1521 : W := mkw 0x804200104a001112 0xffffc3b3fa527b33

def z1522 : W := mkw 0x814218fb5f001112 0xedbbbcff1fc27833

def z1523 : W := mkw 0x03c03bfbff000000 0x00dd3ffeff800000

def z1524 : W := mkw 0x804200104a001112 0xfcf942b2da527b33

def z1525 : W := mkw 0x233837ec007fe000 0x077fbffec07ff000

def z1526 : W := mkw 0x673937ec00ffe045 0xff5fbffc23fff4cf

def z1527 : W := mkw 0x804200104a001112 0xfffdc2b3ffd27b33

def z1528 : W := mkw 0x804200104a001112 0xffffc3f3fe7fffff

def z1529 : W := mkw 0x23bc37eca07fe280 0x1f7ffffee07ffbc0

def z1530 : W := mkw 0x12a42f03a0780e80 0x1b617e03e07c0fc0

def z1531 : W := mkw 0x02802b03a0000000 0x00023d4d25800000

def z1532 : W := mkw 0x213814ec0067e000 0x041a3cfc0023f000

def z1533 : W := mkw 0x440100040084c045 0xe4fe814d27adc4cf

def z1534 : W := mkw 0x6439040400ffe045 0xff000000002dc4cf

def z1535 : W := mkw 0x233837ec007fe000 0x1f7fffffe07fffc0

def z1536 : W := mkw 0x233837ec007fe000 0x07033ffc007ff000

def z1537 : W := mkw 0x02802b03a0000000 0xffffff4fe7d04b03

def z1538 : W := mkw 0x03c03bfbff000000 0x2dffbfffffe38c3c

def z1539 : W := mkw 0x211810ec0007e000 0x041bbcfc0003f000

def z1540 : W := mkw 0x12a42f03a0780e80 0x1b67ff83f87e0ff0

def z1541 : W := mkw 0x804200104a001112 0xe79dc2b2da527b33

def z1542 : W := mkw 0x440100040084c045 0xd75e814d27adc4cf

def z1543 : W := mkw 0x440100040084c045 0xffffc3ffe7ffffcf

def z1544 : W := mkw 0x000010c000000000 0x00ffbdcd27800000

def z1545 : W := mkw 0x440100040084c045 0xff9a014d27adc4cf

def z1546 : W := mkw 0x804200104a001112 0xe4fdc2b2da527b33

def z1547 : W := mkw 0x2308232c001ce000 0x0217bf3c001c7000

def z1548 : W := mkw 0x233837ec007fe000 0x04183cfc0003f000

def z1549 : W := mkw 0x83c23bfbff001112 0xfffdfefedfd27b33

def z1550 : W := mkw 0x03c03bfbff000000 0x0077bf7fe7800000

def z1551 : W := mkw 0x333c37ec007fee80 0x071ffffc007ffb00

def z1552 : W := mkw 0x18301cc314630c28 0x2dbfbdcf1c638c3c

def z1553 : W := mkw 0x03803bebb5000000 0x00023d4d25ac04c0

def z1554 : W := mkw 0x18301cc314630c28 0x3fabbcc31c6f8cfc

def z1555 : W := mkw 0x440100040084c045 0xfbe6814d27ad84cf

def z1556 : W := mkw 0x03c03bfbff000000 0x009b3fffff800000

def z1557 : W := mkw 0x12a42f03a0780e80 0xffffff83fa7e4ff3

def z1558 : W := mkw 0x12a42f03a0780e80 0x1f6fff83e07e0fc0

def z1559 : W := mkw 0x13843bebb5000e80 0x00023d4d258004c0

def z1560 : W := mkw 0xd46704144afcdfd7 0xfffdc2b2da7fffff

def z1561 : W := mkw 0x18301cc314630c28 0x2d033cc31c638c3c

def z1562 : W := mkw 0x3b3837e8007b2c28 0x00013eb000523830

def z1563 : W := mkw 0x83c22b3beb001112 0xdb77ff3fe3d07b03

def z1564 : W := mkw 0x18301cc314630c28 0xedbbbcc31e63cc3f

def z1565 : W := mkw 0x03803bebb5000000 0x000bbdcd25800000

def z1566 : W := mkw 0x233837ec007fe000 0x071ebdfc002ff000

def z1567 : W := mkw 0x18301cc314630c28 0x2d23bc8318638c3c

def z1568 : W := mkw 0x18301cc314630c28 0x2da9bcc21c43883c

def z1569 : W := mkw 0x0220270000780000 0x00013eb000523000

def z1570 : W := mkw 0x12a42f03a0780e80 0x1bffff03e27c0fc0

def z1571 : W := mkw 0x984208135e001d3a 0xe8a000031e000c3f

def z1572 : W := mkw 0x12842b03a0180e80 0x1a67ff03e01c0fc0

def z1573 : W := mkw 0x23bc37e8a07b2280 0x00017eb0c0523300

def z1574 : W := mkw 0x213814ec0067e000 0x04193cfc0043f000

def z1575 : W := mkw 0x03c03bfbff000000 0x00e33fffff800000

def z1576 : W := mkw 0xdc4308135e801d7f 0xf8e04003ff800fff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z10]),(0,[z7,z1,z2,z4,z5,z11,z6]),(0,[z7,z1,z2,z4,z5,z12,z6])],[(0,[z13,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z14])],[(0,[z7,z1,z2,z4,z5,z6,z15]),(0,[z7,z1,z2,z4,z5,z16,z17]),(0,[z7,z1,z2,z4,z5,z18,z6])],[(0,[z7,z1,z2,z19,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z20,z6]),(0,[z21,z7,z1,z2,z5,z22,z6]),(0,[z23,z7,z1,z2,z4,z5,z6])],[(0,[z7,z24,z1,z2,z5,z25,z6])],[(1,[z26,z27,z2,z4,z5,z6]),(1,[z28,z1,z2,z4,z5,z6]),(0,[z29,z7,z1,z2,z30,z5,z6]),(0,[z7,z31,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z32]),(0,[z7,z1,z2,z4,z33,z6,z17]),(0,[z34,z7,z1,z2,z4,z5,z6]),(0,[z35,z36,z1,z2,z4,z5,z6])],[(0,[z37,z7,z1,z2,z4,z5,z6]),(0,[z38,z7,z1,z2,z30,z5,z6])],[(0,[z7,z1,z2,z4,z5,z39,z6]),(1,[z7,z1,z2,z4,z5,z40]),(0,[z41,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z42,z5,z6])],[(1,[z1,z2,z5,z6,z43,z44])],[],[(0,[z7,z1,z2,z4,z45,z5,z6])],[(0,[z7,z1,z2,z4,z46,z5,z6]),(1,[z47,z1,z2,z4,z48,z6]),(0,[z49,z7,z1,z2,z5,z25,z6]),(0,[z7,z1,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z5,z6,z51])],[(0,[z52,z1,z2,z4,z5,z6,z44])],[(0,[z53,z54,z1,z2,z4,z5,z6]),(0,[z55,z7,z1,z2,z4,z5,z6]),(0,[z21,z49,z7,z1,z2,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z56]),(1,[z7,z1,z57,z4,z5,z6])]],
   [[(0,[z7,z2,z4,z5,z33,z6,z58])],[(0,[z1,z2,z4,z59,z5,z6,z44]),(0,[z7,z1,z2,z30,z60,z5,z6])],[(0,[z7,z1,z61,z2,z4,z5,z6]),(0,[z54,z1,z2,z19,z4,z5,z6]),(0,[z7,z62,z1,z2,z4,z5,z6])],[(0,[z63,z1,z2,z4,z5,z6,z44]),(1,[z7,z1,z2,z4,z64,z6])],[(0,[z65,z1,z2,z66,z4,z5,z6])],[(0,[z67,z1,z2,z4,z5,z6,z44]),(1,[z68,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z69,z6]),(0,[z7,z1,z2,z4,z22,z6,z17])],[],[(0,[z7,z1,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z70,z22,z6])],[(0,[z7,z1,z2,z4,z5,z71,z6]),(1,[z7,z24,z2,z72,z5,z6])],[(0,[z73,z7,z1,z2,z4,z5,z6]),(0,[z47,z7,z74,z2,z4,z5,z6]),(0,[z75,z7,z1,z2,z4,z5,z6]),(0,[z7,z76,z1,z2,z4,z5,z6])],[(0,[z77,z54,z1,z2,z4,z5,z6])],[(0,[z47,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z78,z6]),(0,[z7,z79,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z50,z6]),(0,[z7,z1,z2,z4,z80,z5,z6])],[(0,[z81,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z66,z5,z22,z6]),(0,[z47,z7,z1,z2,z82,z5,z6]),(1,[z7,z1,z2,z83,z5,z6]),(0,[z7,z1,z2,z5,z22,z84,z6]),(0,[z7,z1,z2,z4,z85,z5,z6])],[(0,[z7,z1,z2,z5,z33,z22,z6])],[],[(0,[z86,z7,z1,z2,z4,z5,z6]),(0,[z1,z87,z2,z4,z5,z6,z44]),(0,[z1,z2,z4,z5,z6,z43,z44]),(0,[z7,z1,z2,z30,z5,z88,z6])]],
   [[(0,[z54,z1,z61,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z89]),(0,[z7,z90,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z5,z17])],[(0,[z7,z1,z2,z92,z4,z5,z6])],[(0,[z93,z54,z1,z2,z4,z5,z6]),(0,[z21,z7,z1,z2,z4,z5,z6])],[(0,[z7,z94,z1,z2,z4,z5,z6]),(0,[z63,z95,z1,z2,z4,z5,z6]),(1,[z1,z2,z96,z4,z5,z6]),(0,[z97,z7,z1,z2,z4,z98,z6])],[(0,[z99,z7,z1,z2,z4,z59,z6]),(0,[z29,z100,z1,z2,z4,z5,z6])],[(0,[z54,z1,z9,z2,z4,z5,z6]),(0,[z29,z1,z2,z4,z5,z6,z44]),(0,[z1,z2,z30,z4,z5,z6,z44]),(1,[z101,z7,z2,z4,z5,z6])],[],[(0,[z7,z102,z1,z2,z4,z5,z6]),(0,[z21,z7,z1,z103,z2,z5,z6]),(0,[z7,z1,z2,z4,z104,z5,z6])],[(0,[z1,z2,z66,z4,z105,z5,z6]),(0,[z7,z1,z2,z72,z5,z6,z106]),(0,[z7,z1,z2,z30,z5,z33,z6]),(0,[z7,z1,z2,z30,z5,z6,z16])],[(0,[z54,z27,z1,z2,z4,z5,z6]),(0,[z107,z1,z2,z66,z4,z5,z6])],[(0,[z47,z1,z2,z4,z5,z48,z6]),(0,[z108,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z109,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z110]),(0,[z7,z1,z2,z4,z111,z5,z6]),(0,[z7,z1,z103,z19,z4,z5,z6])],[(0,[z26,z52,z7,z2,z4,z5,z6]),(0,[z112,z54,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z30,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z113,z6]),(0,[z7,z1,z2,z4,z5,z6,z17])],[(0,[z114,z7,z1,z2,z4,z5,z6]),(0,[z7,z115,z1,z2,z4,z5,z6])],[(0,[z112,z1,z9,z2,z4,z5,z6]),(0,[z116,z7,z1,z2,z117,z5,z6]),(0,[z7,z1,z2,z118,z4,z5,z6]),(0,[z7,z119,z1,z2,z4,z5,z6]),(0,[z7,z1,z120,z2,z4,z5,z50]),(0,[z7,z1,z2,z121,z30,z5,z6])],[(0,[z0,z7,z27,z2,z4,z5,z6]),(0,[z99,z1,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z122,z4,z5,z6]),(0,[z7,z1,z2,z4,z123,z5,z6]),(0,[z21,z7,z124,z2,z4,z5,z6])]],
   [[(0,[z125,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z126,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z127,z5,z6])],[(0,[z7,z128,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z129,z16]),(1,[z7,z1,z2,z30,z5,z6])],[(0,[z130,z7,z1,z2,z4,z5,z6])],[],[(0,[z7,z131,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z132,z6])],[],[(0,[z27,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z133,z4,z5,z6]),(0,[z63,z7,z1,z2,z4,z134,z6])],[(0,[z135,z7,z1,z2,z4,z5,z6]),(0,[z7,z8,z1,z2,z4,z136,z6]),(0,[z93,z7,z1,z2,z4,z91,z6])],[(0,[z7,z1,z2,z4,z5,z137,z6]),(0,[z138,z7,z1,z2,z4,z5,z44]),(0,[z7,z1,z2,z72,z139,z5,z6]),(0,[z7,z1,z2,z91,z5,z140,z6])],[(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z30,z141,z5,z6])],[(0,[z26,z1,z61,z2,z4,z5,z6]),(0,[z142,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z66,z4,z5,z6]),(0,[z143,z54,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z6,z17]),(0,[z7,z144,z1,z2,z4,z5,z58]),(0,[z145,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z146])],[(0,[z147,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z9,z2,z5,z22,z6])],[(0,[z7,z1,z148,z2,z4,z5,z6]),(0,[z7,z149,z1,z2,z4,z5,z6]),(0,[z7,z1,z150,z2,z4,z88,z6])],[(0,[z7,z1,z2,z4,z5,z151,z6]),(0,[z65,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z58,z17])],[(0,[z65,z7,z152,z1,z4,z5,z6]),(0,[z116,z1,z2,z4,z105,z5,z6]),(0,[z7,z1,z2,z4,z153,z5,z6]),(1,[z7,z1,z103,z19,z5,z6]),(0,[z7,z1,z2,z5,z22,z129,z6]),(0,[z7,z124,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z27,z1,z2,z5,z22,z6]),(0,[z154,z1,z2,z4,z5,z6,z44]),(0,[z155,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z156,z5,z6]),(0,[z7,z144,z1,z2,z5,z22,z6]),(0,[z97,z7,z1,z2,z30,z5,z6]),(0,[z7,z157,z1,z2,z4,z5,z6])],[(0,[z158,z7,z1,z2,z4,z5,z6]),(0,[z116,z65,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z159,z6])],[(0,[z1,z9,z2,z4,z5,z48,z6]),(0,[z116,z7,z1,z2,z66,z5,z6]),(0,[z7,z1,z2,z160,z59,z5,z6]),(0,[z7,z1,z2,z5,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z161,z6])],[(0,[z1,z2,z4,z141,z5,z6,z44]),(0,[z38,z7,z24,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z5,z22,z6])],[(0,[z7,z1,z2,z162,z4,z5,z6]),(0,[z7,z1,z2,z72,z30,z5,z6]),(0,[z1,z2,z4,z5,z163,z33,z6])],[(0,[z164,z1,z103,z2,z4,z5,z6]),(0,[z165,z7,z1,z2,z5,z22,z6])],[(0,[z7,z1,z120,z166,z4,z5,z6]),(0,[z7,z24,z1,z2,z30,z5,z6]),(0,[z67,z7,z1,z167,z4,z5,z6]),(0,[z7,z144,z2,z4,z5,z168,z6]),(1,[z7,z169,z2,z4,z5,z6])],[(0,[z170,z7,z1,z2,z4,z5,z6]),(0,[z107,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z171,z5,z6]),(0,[z7,z1,z2,z4,z5,z172,z6]),(0,[z35,z7,z1,z2,z30,z5,z6])],[(0,[z54,z1,z2,z66,z4,z5,z6]),(0,[z173,z7,z1,z2,z4,z5,z6]),(0,[z7,z94,z1,z2,z5,z22,z6])],[(0,[z1,z2,z19,z4,z5,z6,z44])],[(0,[z0,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z174,z6]),(0,[z47,z7,z1,z2,z175,z5,z6]),(0,[z38,z7,z2,z166,z4,z5,z6])],[(0,[z164,z7,z1,z2,z4,z5,z6]),(0,[z176,z1,z2,z4,z5,z88,z6])],[(0,[z7,z1,z2,z4,z5,z6,z177]),(0,[z93,z178,z1,z2,z4,z5,z6])],[(0,[z116,z7,z1,z2,z72,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z179]),(0,[z7,z1,z2,z4,z5,z180,z6]),(0,[z176,z7,z1,z2,z4,z5,z6])],[(0,[z49,z7,z1,z2,z30,z5,z6]),(0,[z181,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z182,z5,z6]),(1,[z100,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z183])]],
   [[(1,[z1,z2,z4,z5,z6,z44]),(1,[z1,z2,z4,z5,z163,z6]),(0,[z7,z1,z2,z4,z5,z184,z6])],[(0,[z7,z1,z2,z4,z185,z5,z6]),(0,[z7,z1,z2,z4,z5,z186,z6]),(0,[z7,z1,z2,z4,z187,z5,z6])],[(0,[z116,z7,z1,z2,z19,z5,z6]),(0,[z188,z1,z2,z4,z5,z6,z44])],[(0,[z7,z1,z2,z4,z189,z5,z6]),(0,[z7,z1,z2,z4,z5,z190,z6]),(0,[z7,z1,z2,z4,z5,z6,z191])],[(0,[z7,z1,z192,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z193])],[(0,[z65,z7,z1,z166,z4,z5,z6]),(0,[z7,z1,z2,z4,z194,z5,z6]),(0,[z7,z1,z2,z4,z195,z5,z6]),(0,[z7,z1,z2,z30,z196,z5,z6])],[(0,[z26,z7,z2,z166,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z44,z89]),(0,[z7,z1,z2,z4,z197,z5,z6]),(0,[z52,z7,z1,z2,z198,z5,z6]),(0,[z29,z7,z1,z2,z4,z5,z16]),(1,[z1,z2,z4,z5,z6,z199]),(0,[z7,z1,z2,z30,z5,z129,z6])],[(0,[z200,z7,z1,z2,z4,z5,z6]),(0,[z201,z7,z1,z2,z4,z5,z6])],[(0,[z202,z7,z1,z2,z4,z5,z6])],[(0,[z47,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z4,z141,z5,z88,z6])],[(0,[z7,z1,z2,z4,z203,z5,z6]),(0,[z7,z1,z2,z4,z5,z204,z6]),(0,[z7,z1,z2,z4,z5,z6,z205]),(0,[z7,z1,z2,z4,z206,z5,z6]),(0,[z7,z1,z2,z5,z18,z22,z6])],[(0,[z7,z1,z2,z3,z5,z22,z6]),(0,[z207,z7,z1,z2,z5,z6,z44]),(0,[z7,z1,z2,z4,z208,z5,z6]),(1,[z7,z1,z2,z22,z6,z17])],[(0,[z7,z1,z2,z156,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z209]),(0,[z7,z1,z2,z210,z4,z5,z6])],[(0,[z7,z27,z1,z2,z4,z5,z6]),(0,[z7,z144,z1,z2,z4,z5,z6])],[(1,[z7,z1,z2,z160,z5,z6]),(0,[z97,z1,z2,z4,z5,z6,z44]),(0,[z1,z2,z122,z4,z5,z6,z44]),(0,[z54,z1,z2,z4,z185,z5,z6])]],
   [[(0,[z211,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z22,z212,z6]),(1,[z95,z1,z2,z4,z5,z6]),(1,[z35,z7,z1,z4,z88,z6])],[(1,[z213,z7,z2,z4,z5,z6]),(0,[z214,z7,z1,z2,z4,z5,z6]),(0,[z215,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z4,z5,z6])],[(0,[z7,z1,z2,z216,z4,z5,z6]),(0,[z7,z1,z2,z4,z217,z5,z6]),(0,[z38,z52,z7,z2,z4,z5,z6]),(0,[z52,z7,z144,z2,z4,z5,z6]),(0,[z35,z7,z1,z150,z4,z5,z6])],[(0,[z21,z107,z7,z1,z2,z5,z6]),(0,[z1,z2,z4,z5,z6,z44,z17]),(0,[z165,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z139,z5,z25,z6])],[(0,[z7,z1,z2,z4,z5,z218,z6]),(0,[z219,z7,z1,z2,z4,z5,z6]),(0,[z138,z7,z1,z2,z5,z22,z6])],[(0,[z220,z7,z1,z2,z4,z5,z6]),(1,[z138,z1,z2,z4,z5,z44]),(0,[z1,z2,z4,z117,z5,z6,z44]),(1,[z7,z1,z221,z4,z5,z6])],[(0,[z222,z7,z1,z2,z4,z5,z6]),(0,[z35,z1,z2,z4,z5,z6,z44]),(0,[z54,z54,z1,z2,z4,z5,z6]),(0,[z67,z7,z1,z2,z4,z33,z6]),(0,[z63,z7,z1,z2,z208,z5,z6]),(0,[z223,z7,z1,z2,z4,z5,z6])],[(0,[z38,z7,z2,z4,z117,z5,z6]),(0,[z63,z7,z144,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z224])],[(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z225,z6])],[(0,[z1,z61,z2,z4,z5,z6,z44]),(1,[z7,z1,z226,z4,z5,z6]),(0,[z7,z1,z227,z2,z4,z5,z6]),(0,[z7,z1,z120,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z50,z17]),(1,[z21,z7,z1,z2,z5,z106])],[(0,[z7,z1,z2,z4,z5,z6,z228]),(0,[z24,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z229,z4,z5,z6])],[(0,[z230,z7,z1,z2,z4,z5,z6]),(1,[z49,z7,z1,z196,z5,z6])],[(0,[z231,z7,z1,z2,z4,z5,z6]),(0,[z54,z144,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z232]),(1,[z1,z2,z5,z233,z22,z6]),(0,[z7,z1,z2,z30,z5,z6,z234]),(0,[z7,z1,z2,z235,z4,z5,z6])],[(0,[z49,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z19,z5,z6,z106]),(0,[z236,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z5,z22,z6,z237])],[(0,[z65,z1,z2,z4,z5,z48,z6])],[(0,[z238,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z22,z6,z106])]],
   [[(0,[z7,z1,z2,z4,z5,z239,z6]),(0,[z7,z1,z2,z5,z48,z22,z6]),(0,[z7,z2,z4,z136,z5,z33,z6])],[(0,[z7,z1,z2,z4,z5,z6,z240]),(0,[z7,z1,z241,z2,z4,z5,z6])],[(0,[z107,z7,z1,z2,z105,z5,z6]),(0,[z107,z7,z1,z2,z66,z5,z6]),(0,[z7,z242,z1,z2,z4,z5,z6]),(0,[z7,z152,z1,z2,z30,z5,z6]),(0,[z29,z7,z243,z2,z4,z5,z6]),(0,[z244,z7,z1,z2,z5,z22,z6])],[(0,[z52,z119,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z134,z6]),(0,[z245,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z166,z5,z22,z6]),(0,[z246,z1,z2,z4,z5,z33,z6])],[(0,[z247,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z248,z5,z6])],[(0,[z7,z1,z249,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z250,z5,z6]),(1,[z7,z1,z2,z251,z5,z6])],[(0,[z54,z1,z120,z2,z4,z5,z6]),(0,[z21,z252,z1,z2,z4,z5,z6]),(0,[z7,z1,z253,z2,z4,z5,z6])],[(0,[z47,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z254]),(0,[z7,z1,z2,z30,z5,z212,z6]),(0,[z7,z1,z2,z196,z5,z22,z6]),(0,[z255,z7,z1,z2,z30,z5,z6])],[(0,[z256,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z98,z5,z6])],[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z257,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z40,z6])],[(0,[z7,z1,z2,z4,z5,z258,z6]),(0,[z112,z7,z1,z3,z4,z5,z6]),(0,[z7,z8,z2,z166,z4,z5,z6]),(0,[z93,z7,z1,z2,z4,z5,z129])],[(0,[z112,z7,z152,z1,z4,z5,z6])],[(0,[z7,z1,z2,z4,z259,z5,z6]),(0,[z47,z7,z1,z2,z4,z5,z260]),(0,[z7,z1,z2,z19,z139,z5,z6]),(0,[z7,z261,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z25,z6,z106]),(0,[z7,z1,z2,z42,z4,z5,z6])],[(0,[z144,z1,z2,z4,z5,z6,z44]),(0,[z262,z7,z1,z2,z5,z6,z16])],[(0,[z7,z263,z1,z2,z4,z5,z6]),(1,[z52,z7,z152,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z233,z6]),(0,[z7,z1,z2,z4,z5,z264,z6])]],
   [[(0,[z26,z54,z1,z2,z4,z5,z6])],[(1,[z7,z1,z167,z4,z5,z6]),(0,[z1,z2,z4,z5,z233,z22,z6])],[(0,[z7,z1,z2,z4,z5,z265,z6]),(0,[z138,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z266,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z267,z5,z6]),(1,[z7,z1,z2,z4,z187,z6]),(0,[z7,z178,z1,z2,z4,z5,z6])],[(0,[z116,z7,z1,z2,z5,z22,z6])],[(0,[z7,z1,z268,z2,z4,z5,z6]),(0,[z7,z1,z2,z269,z4,z5,z6])],[],[(0,[z26,z27,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z98,z5,z6])],[(1,[z7,z1,z270,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z52,z7,z2,z4,z5,z33,z6]),(0,[z7,z1,z2,z4,z271,z5,z6]),(0,[z7,z1,z2,z272,z30,z5,z6])],[(0,[z273,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z274]),(0,[z23,z7,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z275])],[(1,[z276,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z136,z6]),(1,[z277,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z278,z6])],[(0,[z236,z7,z1,z2,z4,z5,z6]),(0,[z279,z7,z1,z2,z4,z5,z6]),(0,[z21,z7,z1,z2,z5,z6,z106])],[(0,[z54,z1,z2,z4,z280,z5,z6]),(0,[z35,z7,z1,z2,z251,z5,z6])],[(0,[z7,z152,z1,z150,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z281,z6]),(0,[z7,z1,z2,z5,z22,z25,z6]),(1,[z31,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z105,z5,z6]),(0,[z7,z1,z120,z2,z5,z22,z6]),(0,[z282,z7,z1,z2,z4,z5,z6])],[(0,[z47,z7,z283,z2,z4,z5,z6]),(0,[z67,z7,z2,z4,z5,z33,z6]),(0,[z101,z7,z103,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z284,z6])]],
   [[(0,[z244,z7,z1,z2,z4,z5,z6]),(0,[z54,z65,z1,z2,z4,z5,z6]),(0,[z285,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z286,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z287,z6])],[(0,[z112,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z2,z162,z5,z6]),(0,[z7,z288,z1,z2,z4,z5,z6]),(0,[z34,z7,z1,z2,z5,z6,z58]),(0,[z289,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z290,z5,z6]),(0,[z7,z1,z2,z4,z291,z5,z6]),(0,[z99,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z166,z4,z5,z6])],[(0,[z112,z7,z1,z166,z4,z5,z6]),(0,[z21,z7,z1,z253,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z48,z6]),(0,[z7,z1,z120,z4,z5,z88,z6])],[(1,[z54,z1,z2,z4,z5,z44]),(1,[z7,z241,z2,z4,z5,z6])],[(0,[z116,z7,z1,z2,z196,z5,z6])],[(0,[z7,z1,z61,z2,z30,z5,z6]),(0,[z1,z150,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z5,z22,z168,z6]),(0,[z7,z1,z19,z4,z196,z5,z6]),(0,[z7,z1,z2,z30,z139,z5,z6])],[(0,[z292,z7,z1,z2,z4,z5,z6])],[(0,[z293,z7,z1,z2,z4,z5,z6]),(0,[z112,z65,z1,z2,z4,z5,z6]),(0,[z7,z2,z166,z4,z5,z33,z6]),(1,[z7,z1,z2,z198,z5,z6]),(1,[z7,z1,z2,z30,z98,z6])],[(0,[z294,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z6,z44]),(0,[z21,z7,z1,z2,z139,z5,z6])],[(0,[z7,z1,z2,z295,z4,z5,z6]),(0,[z207,z1,z2,z4,z5,z6,z44]),(0,[z296,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z297,z4,z5,z6]),(0,[z52,z54,z1,z2,z4,z5,z6]),(1,[z7,z243,z2,z4,z5,z6])],[(0,[z7,z298,z27,z1,z4,z5,z6]),(0,[z65,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z166,z4,z5,z88,z6]),(0,[z75,z152,z1,z2,z4,z5,z6])],[(0,[z7,z299,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z300,z6]),(0,[z7,z1,z2,z4,z301,z5,z6]),(0,[z1,z2,z4,z98,z5,z6,z44]),(0,[z54,z288,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z302,z5,z6]),(0,[z7,z1,z2,z4,z303,z5,z6]),(0,[z7,z1,z2,z269,z141,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z304])]],
   [[(0,[z305,z7,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z166,z4,z5,z6]),(0,[z7,z1,z2,z306,z4,z5,z6])],[(0,[z116,z7,z1,z2,z4,z5,z6]),(0,[z107,z7,z1,z2,z117,z5,z6]),(0,[z1,z2,z4,z136,z5,z6,z44]),(0,[z307,z7,z1,z2,z5,z22,z6])],[(0,[z54,z1,z2,z4,z5,z48,z6]),(0,[z63,z54,z1,z2,z4,z5,z6]),(0,[z21,z38,z7,z1,z2,z5,z6]),(0,[z93,z308,z1,z2,z4,z5,z6])],[(1,[z7,z1,z2,z208,z5,z6]),(0,[z309,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z310,z5,z6]),(0,[z7,z1,z150,z2,z4,z141,z6])],[(0,[z77,z7,z1,z2,z4,z5,z6]),(0,[z67,z54,z1,z2,z4,z5,z6])],[(0,[z26,z1,z2,z66,z4,z5,z6]),(0,[z311,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z5,z25,z6])],[(0,[z54,z7,z1,z2,z4,z5,z44]),(0,[z7,z1,z2,z4,z312,z5,z6]),(0,[z313,z7,z1,z2,z30,z5,z6])],[(0,[z7,z1,z2,z4,z314,z5,z6]),(0,[z7,z1,z166,z4,z5,z6,z16]),(0,[z7,z1,z2,z30,z136,z5,z6]),(0,[z315,z7,z1,z2,z4,z5,z6]),(0,[z21,z7,z1,z2,z30,z5,z6]),(0,[z252,z7,z1,z2,z4,z5,z6])],[(0,[z316,z7,z1,z2,z4,z5,z6])],[(0,[z7,z317,z1,z2,z4,z5,z6]),(0,[z7,z8,z1,z2,z4,z33,z6])],[(0,[z7,z1,z2,z4,z318,z5,z6]),(0,[z68,z7,z1,z2,z4,z5,z6]),(0,[z52,z7,z1,z2,z217,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z319,z6]),(0,[z49,z7,z1,z103,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z320,z6]),(0,[z7,z1,z2,z4,z5,z6,z321])],[(0,[z7,z1,z2,z4,z5,z6,z322]),(0,[z7,z1,z103,z2,z117,z5,z6]),(0,[z7,z8,z144,z2,z4,z5,z6])],[(0,[z7,z1,z2,z5,z22,z6,z44])],[(0,[z7,z1,z2,z4,z5,z323,z6]),(0,[z324,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z129,z6,z44]),(0,[z35,z7,z1,z2,z4,z88,z6]),(0,[z325,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z326])],[(0,[z7,z1,z2,z4,z5,z327,z6]),(0,[z7,z1,z2,z30,z5,z168,z6])]],
   [[(0,[z7,z1,z2,z59,z5,z22,z6]),(0,[z246,z7,z1,z2,z4,z5,z6])],[(0,[z67,z7,z1,z2,z4,z5,z328]),(0,[z7,z1,z2,z4,z5,z329,z6]),(0,[z7,z1,z2,z4,z5,z330,z6])],[(0,[z7,z1,z2,z4,z5,z331,z6]),(0,[z7,z27,z8,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z332]),(0,[z333,z7,z1,z2,z4,z5,z6])],[],[(0,[z1,z2,z4,z105,z5,z6,z44]),(0,[z29,z54,z1,z2,z4,z5,z6]),(0,[z7,z152,z2,z166,z4,z5,z6])],[(1,[z119,z1,z2,z4,z5,z6]),(0,[z7,z1,z334,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z335,z5,z6])],[(0,[z38,z54,z1,z2,z4,z5,z6]),(0,[z7,z152,z1,z19,z4,z5,z6])],[(0,[z262,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z336,z5,z6])],[(0,[z54,z1,z2,z4,z5,z319,z6]),(0,[z7,z24,z144,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z337]),(0,[z7,z169,z1,z2,z4,z5,z6])],[],[(0,[z7,z1,z2,z4,z5,z134,z6]),(0,[z7,z1,z338,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z6,z339])],[(0,[z65,z7,z1,z2,z4,z5,z6]),(0,[z7,z340,z1,z2,z4,z5,z6]),(0,[z63,z7,z1,z341,z4,z5,z6]),(0,[z7,z1,z2,z196,z5,z6,z106])],[(0,[z54,z1,z2,z4,z117,z5,z6])],[(0,[z7,z27,z1,z2,z342,z5,z6]),(0,[z7,z1,z343,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z344,z5,z6])],[(0,[z7,z1,z345,z2,z4,z5,z6]),(0,[z307,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z346,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z347,z4,z5,z6]),(0,[z107,z7,z1,z2,z72,z5,z6]),(0,[z7,z1,z2,z4,z5,z348,z6])],[(1,[z54,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z280,z5,z6])],[(0,[z7,z1,z3,z4,z5,z88,z6]),(0,[z1,z61,z2,z4,z59,z5,z6])],[(0,[z7,z1,z2,z4,z105,z5,z6]),(0,[z1,z2,z4,z349,z5,z6,z44]),(0,[z7,z350,z1,z2,z4,z5,z6]),(0,[z7,z1,z351,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z91,z129])],[(0,[z7,z1,z2,z352,z4,z5,z6]),(0,[z353,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z5,z22,z354,z6]),(0,[z355,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z356,z4,z5,z6])],[(0,[z107,z7,z1,z2,z19,z5,z6]),(0,[z7,z1,z2,z30,z5,z6,z44]),(0,[z7,z154,z1,z166,z4,z5,z6]),(0,[z7,z357,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z358,z5,z6]),(0,[z7,z1,z2,z4,z82,z5,z6]),(0,[z21,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z359,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z360,z6]),(0,[z63,z7,z1,z2,z361,z5,z6]),(0,[z7,z1,z2,z4,z5,z362,z6]),(0,[z7,z1,z2,z4,z5,z363,z6]),(0,[z7,z1,z2,z4,z5,z364,z6])],[(0,[z213,z7,z1,z2,z4,z5,z6]),(0,[z7,z365,z1,z2,z4,z5,z6])],[(0,[z366,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z367])],[(0,[z368,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z30,z4,z98,z6])],[(0,[z7,z1,z369,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z370,z6]),(0,[z7,z1,z2,z4,z371,z5,z6]),(0,[z1,z2,z166,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z372,z5,z6]),(0,[z7,z1,z2,z30,z5,z6,z106])],[(0,[z373,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z103,z2,z72,z5,z6]),(0,[z7,z1,z120,z4,z196,z5,z6]),(0,[z97,z7,z1,z2,z4,z22,z6]),(0,[z7,z1,z2,z4,z5,z6,z374])],[(0,[z7,z1,z2,z19,z30,z5,z6]),(0,[z7,z375,z1,z2,z4,z5,z6])],[(0,[z7,z1,z103,z4,z5,z6,z16]),(0,[z376,z7,z1,z2,z4,z5,z6])],[(0,[z377,z7,z1,z2,z4,z5,z6])],[]],
   [[(0,[z7,z1,z103,z2,z19,z5,z6])],[(0,[z7,z1,z2,z4,z5,z378,z6]),(0,[z107,z7,z1,z2,z4,z5,z6]),(0,[z93,z7,z1,z2,z5,z22,z6])],[(0,[z54,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z60,z5,z6])],[(0,[z7,z1,z150,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z379]),(0,[z7,z1,z2,z5,z22,z6,z58])],[(0,[z7,z1,z2,z4,z349,z5,z6]),(0,[z7,z380,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z381,z6]),(0,[z382,z7,z1,z2,z4,z5,z6]),(0,[z383,z7,z1,z2,z4,z5,z6]),(0,[z7,z384,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z385,z5,z6]),(0,[z386,z7,z1,z2,z4,z5,z6]),(1,[z97,z7,z1,z2,z22,z6])],[(0,[z387,z7,z1,z2,z4,z5,z6]),(0,[z388,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z103,z120,z4,z5,z6]),(0,[z93,z7,z1,z346,z4,z5,z6])],[],[(0,[z389,z7,z1,z2,z4,z5,z6])],[(0,[z390,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z338,z2,z4,z5,z6]),(0,[z391,z7,z1,z2,z4,z5,z6])],[(0,[z21,z116,z7,z1,z2,z5,z6]),(0,[z392,z7,z1,z2,z4,z5,z6]),(1,[z246,z1,z2,z4,z5,z6]),(0,[z7,z393,z1,z2,z4,z5,z6])],[(0,[z112,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z394,z6]),(0,[z395,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z59,z5,z48,z6]),(0,[z7,z1,z2,z4,z396,z5,z6]),(0,[z53,z7,z1,z2,z4,z5,z6]),(0,[z99,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z397,z2,z4,z5,z6]),(0,[z7,z398,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z399,z44]),(0,[z400,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z129,z50]),(0,[z7,z1,z2,z4,z401,z5,z6])],[],[(0,[z7,z1,z9,z2,z30,z5,z6]),(1,[z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z402,z2,z4,z5,z6]),(0,[z7,z152,z1,z2,z403,z5,z6]),(0,[z404,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z88,z6])],[(0,[z7,z1,z2,z4,z5,z405,z6]),(1,[z7,z1,z2,z403,z5,z6])],[(0,[z7,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z406,z4,z5,z6]),(0,[z407,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z408]),(0,[z353,z7,z1,z2,z4,z5,z6])],[(0,[z7,z27,z1,z2,z30,z5,z6])],[(0,[z7,z409,z1,z2,z4,z5,z6])],[(0,[z116,z7,z1,z2,z5,z25,z6]),(0,[z7,z1,z2,z4,z5,z410,z6]),(0,[z7,z1,z411,z2,z4,z5,z6])],[(0,[z7,z1,z2,z156,z136,z5,z6]),(0,[z7,z1,z2,z30,z30,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z412]),(0,[z368,z7,z1,z2,z4,z5,z6])],[(0,[z7,z154,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z33,z6]),(1,[z7,z413,z2,z4,z5,z6]),(0,[z29,z7,z1,z2,z4,z414,z6]),(0,[z7,z1,z2,z4,z5,z6,z16]),(0,[z7,z1,z2,z4,z5,z415,z6]),(1,[z355,z1,z2,z4,z5,z6])],[(0,[z54,z1,z103,z2,z4,z5,z6]),(0,[z7,z416,z1,z2,z4,z5,z6]),(1,[z7,z2,z417,z4,z5,z6])],[(0,[z7,z1,z2,z59,z5,z418,z6]),(0,[z7,z1,z150,z166,z4,z5,z6]),(0,[z7,z1,z2,z30,z5,z6,z58])],[(0,[z7,z1,z2,z4,z5,z6,z419]),(1,[z7,z1,z2,z217,z5,z6]),(0,[z38,z7,z1,z2,z72,z5,z6]),(0,[z7,z1,z420,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z328]),(0,[z7,z1,z2,z4,z5,z6,z421]),(0,[z7,z144,z1,z2,z4,z5,z168]),(1,[z7,z1,z2,z4,z422,z6])],[(0,[z0,z7,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z5,z423,z6]),(0,[z1,z2,z4,z5,z88,z6,z44]),(0,[z52,z7,z152,z1,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z424,z6]),(0,[z425,z7,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z88,z6]),(0,[z97,z54,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z6,z224])],[(0,[z426,z7,z1,z2,z4,z5,z6]),(0,[z93,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z26,z0,z1,z2,z4,z5,z6]),(0,[z47,z116,z1,z2,z4,z5,z6]),(0,[z54,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z212,z6,z44]),(0,[z7,z1,z150,z2,z5,z22,z6]),(0,[z7,z1,z2,z30,z5,z5,z6])],[(1,[z63,z7,z2,z4,z5,z58]),(0,[z7,z1,z2,z5,z22,z50,z6])],[(0,[z7,z1,z2,z4,z117,z5,z6])],[(0,[z7,z1,z2,z4,z91,z88,z6])],[(0,[z7,z1,z2,z4,z98,z6,z17])],[(0,[z7,z1,z61,z150,z4,z5,z6]),(0,[z35,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z427,z6]),(0,[z7,z428,z1,z2,z4,z5,z6]),(0,[z7,z1,z429,z2,z4,z5,z6])],[(0,[z107,z7,z1,z2,z5,z22,z6]),(0,[z54,z154,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z430])],[(0,[z0,z7,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z431,z4,z5,z6]),(0,[z7,z1,z61,z2,z162,z5,z6]),(0,[z54,z1,z2,z4,z5,z33,z6]),(0,[z54,z1,z2,z4,z5,z6,z16]),(0,[z7,z1,z2,z4,z5,z6,z432]),(0,[z433,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z434,z6]),(0,[z7,z1,z2,z4,z435,z5,z6]),(0,[z101,z7,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z5,z408])],[(0,[z112,z7,z1,z2,z4,z5,z6]),(0,[z7,z61,z2,z436,z4,z5,z6]),(0,[z63,z437,z1,z2,z4,z5,z6]),(1,[z7,z1,z341,z4,z5,z6]),(0,[z438,z7,z1,z2,z4,z5,z6])],[(0,[z99,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z439,z4,z5,z6]),(0,[z355,z1,z2,z4,z5,z129,z6])],[(0,[z1,z2,z4,z5,z168,z6,z44]),(0,[z7,z1,z440,z2,z4,z5,z6]),(0,[z93,z7,z441,z2,z4,z5,z6])],[(0,[z49,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z33,z6]),(0,[z7,z1,z2,z4,z5,z6,z442])],[(0,[z7,z2,z72,z4,z117,z5,z6])],[(0,[z7,z1,z2,z4,z443,z5,z6])],[(0,[z26,z1,z2,z4,z5,z48,z6]),(0,[z444,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z251,z4,z5,z6]),(0,[z7,z1,z150,z4,z5,z6,z16]),(0,[z7,z1,z2,z5,z22,z445,z6])]],
   [[(0,[z7,z152,z154,z1,z4,z5,z6])],[(0,[z7,z1,z103,z2,z5,z22,z6]),(0,[z29,z7,z413,z2,z4,z5,z6])],[(0,[z7,z1,z2,z66,z30,z5,z6]),(0,[z7,z261,z1,z2,z30,z5,z6])],[(0,[z446,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z361,z5,z6]),(0,[z29,z7,z1,z2,z4,z5,z50]),(0,[z7,z1,z2,z30,z91,z5,z6]),(0,[z21,z31,z1,z2,z4,z5,z6])],[(0,[z447,z54,z1,z2,z4,z5,z6]),(0,[z52,z7,z1,z166,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z22,z6])],[(0,[z448,z7,z1,z2,z4,z5,z6])],[(1,[z1,z2,z4,z5,z233,z6]),(0,[z7,z1,z2,z449,z4,z5,z6])],[(0,[z143,z7,z1,z2,z4,z5,z6]),(0,[z65,z7,z1,z61,z4,z5,z6])],[(0,[z54,z1,z2,z4,z141,z5,z6]),(0,[z7,z1,z2,z4,z5,z450,z6]),(0,[z63,z7,z1,z2,z4,z5,z58]),(0,[z7,z1,z2,z5,z6,z451,z58]),(0,[z7,z1,z150,z120,z4,z5,z6]),(0,[z7,z1,z413,z2,z4,z5,z6]),(0,[z93,z7,z1,z2,z4,z5,z17])],[(0,[z107,z7,z1,z2,z196,z5,z6]),(0,[z452,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z453,z6]),(0,[z7,z1,z2,z417,z4,z5,z6]),(0,[z368,z1,z2,z4,z5,z22,z6]),(1,[z178,z1,z2,z4,z5,z6])],[(0,[z47,z7,z1,z454,z4,z5,z6])],[(0,[z455,z7,z1,z2,z4,z5,z6]),(1,[z107,z1,z2,z66,z5,z6]),(0,[z21,z7,z241,z2,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z70,z6]),(1,[z93,z7,z1,z2,z4,z17])],[(0,[z7,z1,z2,z4,z456,z5,z6]),(0,[z457,z7,z1,z2,z4,z5,z6]),(0,[z7,z154,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z458,z5,z6]),(0,[z7,z1,z4,z5,z88,z6,z16])],[(0,[z7,z1,z2,z459,z4,z5,z6]),(0,[z213,z7,z61,z2,z4,z5,z6]),(0,[z63,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z150,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z460,z6]),(0,[z308,z7,z1,z2,z4,z5,z6])],[(0,[z461,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z462,z6]),(0,[z38,z7,z1,z2,z117,z5,z6]),(0,[z67,z7,z1,z2,z5,z22,z6]),(1,[z1,z2,z4,z5,z6,z275])],[(0,[z7,z1,z2,z4,z5,z129,z44]),(1,[z7,z1,z2,z372,z5,z6]),(0,[z7,z1,z463,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z464,z5,z6]),(0,[z465,z7,z1,z2,z4,z5,z6])],[(0,[z7,z466,z1,z2,z4,z5,z6]),(0,[z467,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z468,z5,z6]),(0,[z54,z1,z2,z4,z5,z22,z6]),(1,[z404,z1,z2,z4,z5,z6]),(0,[z7,z243,z1,z2,z4,z5,z6])],[],[(0,[z26,z7,z27,z2,z4,z5,z6]),(1,[z7,z1,z2,z92,z5,z6]),(0,[z1,z2,z4,z5,z25,z6,z44]),(0,[z7,z1,z103,z2,z196,z5,z6]),(0,[z35,z7,z1,z2,z4,z141,z6]),(1,[z7,z1,z2,z4,z414,z6])],[(0,[z244,z7,z1,z2,z30,z5,z6])],[(0,[z469,z7,z1,z2,z4,z5,z6]),(0,[z7,z470,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z471,z4,z5,z6]),(0,[z7,z1,z2,z4,z196,z5,z6]),(0,[z7,z1,z2,z4,z91,z22,z6])],[(0,[z7,z472,z1,z2,z4,z5,z6])],[],[(0,[z7,z1,z473,z2,z4,z5,z6])],[(0,[z474,z7,z1,z2,z4,z5,z6])],[(0,[z54,z1,z150,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z22,z137,z6])],[(0,[z475,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z476,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z59,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z477])],[(0,[z7,z1,z103,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z6,z44,z16]),(0,[z7,z1,z2,z4,z5,z6,z478]),(1,[z7,z1,z235,z4,z5,z6])],[],[(0,[z0,z1,z2,z4,z59,z5,z6]),(0,[z7,z1,z2,z4,z4,z5,z6]),(1,[z75,z1,z2,z4,z5,z6]),(0,[z38,z7,z1,z2,z5,z22,z6]),(0,[z145,z1,z2,z4,z5,z50,z6])],[(0,[z7,z1,z2,z4,z479,z5,z6]),(0,[z7,z1,z2,z4,z480,z5,z6])],[(0,[z481,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z482,z2,z4,z5,z6]),(1,[z7,z1,z2,z269,z5,z6])],[(0,[z483,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z72,z4,z5,z6,z44]),(0,[z484,z54,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z196,z5,z6]),(0,[z7,z1,z2,z485,z4,z5,z6]),(0,[z486,z7,z1,z2,z4,z5,z6]),(1,[z164,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z141,z5,z22,z6])],[(0,[z116,z7,z1,z2,z30,z5,z6]),(0,[z138,z7,z1,z2,z4,z5,z212]),(0,[z138,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z487,z6]),(0,[z7,z1,z2,z488,z4,z5,z6]),(0,[z7,z144,z1,z2,z30,z5,z6]),(0,[z29,z7,z1,z2,z4,z460,z6])],[(0,[z489,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z91,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z490,z6]),(0,[z7,z36,z1,z2,z4,z5,z6]),(0,[z93,z7,z1,z2,z4,z6,z17]),(0,[z491,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z492,z5,z6]),(1,[z7,z1,z120,z4,z5,z50])],[(0,[z7,z1,z74,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z43]),(0,[z7,z1,z2,z4,z5,z6,z493])],[(0,[z7,z1,z494,z2,z4,z5,z6])],[],[(0,[z63,z7,z1,z2,z4,z5,z6]),(0,[z7,z495,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z496,z6]),(1,[z7,z1,z2,z310,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z234]),(0,[z7,z1,z497,z2,z4,z5,z6]),(0,[z7,z498,z1,z2,z4,z5,z6])],[(0,[z499,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z66,z4,z5,z6,z44]),(0,[z7,z500,z1,z2,z4,z5,z6]),(0,[z67,z7,z1,z2,z4,z5,z6])],[(0,[z0,z7,z2,z166,z4,z5,z6]),(0,[z26,z7,z1,z2,z5,z22,z6]),(0,[z501,z7,z1,z2,z4,z5,z6])]],
   [[(0,[z47,z99,z1,z2,z4,z5,z6])],[(0,[z65,z99,z1,z2,z4,z5,z6]),(0,[z502,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z503,z6]),(0,[z7,z1,z120,z2,z30,z5,z6])],[],[],[(1,[z1,z2,z5,z22,z6,z44]),(0,[z244,z1,z2,z4,z5,z6,z44]),(0,[z38,z7,z1,z2,z19,z5,z6]),(0,[z504,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z422,z6])],[(0,[z38,z7,z1,z2,z196,z5,z6])],[(1,[z437,z1,z2,z4,z5,z6]),(0,[z437,z7,z1,z2,z4,z5,z6])],[(0,[z505,z7,z1,z2,z4,z5,z6]),(0,[z506,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z129,z58])],[(0,[z7,z1,z2,z4,z5,z84,z6]),(0,[z507,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z508,z6])],[(0,[z7,z1,z2,z509,z4,z5,z6]),(0,[z93,z7,z1,z2,z510,z5,z6])],[(0,[z7,z27,z1,z270,z4,z5,z6]),(0,[z7,z2,z4,z117,z5,z6,z58]),(1,[z67,z7,z2,z4,z33,z6])],[(0,[z7,z1,z2,z4,z511,z5,z6]),(1,[z7,z1,z2,z175,z5,z6]),(0,[z1,z2,z4,z5,z33,z6,z44]),(0,[z245,z7,z1,z2,z30,z5,z6]),(0,[z21,z7,z1,z2,z4,z187,z6])],[(1,[z1,z334,z2,z4,z5,z6])],[(0,[z7,z512,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z513,z5,z6]),(0,[z7,z1,z2,z4,z141,z5,z6])],[],[(0,[z7,z1,z2,z4,z5,z418,z6]),(0,[z7,z1,z2,z514,z4,z5,z6])]],
   [[(0,[z47,z7,z1,z2,z30,z5,z6]),(1,[z54,z1,z2,z4,z5,z212]),(0,[z38,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z136,z5,z22,z6]),(0,[z515,z7,z1,z2,z4,z5,z6])],[(0,[z65,z7,z1,z2,z30,z5,z6]),(1,[z7,z1,z2,z30,z22,z6])],[(0,[z27,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z3,z30,z5,z6]),(0,[z516,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z517,z4,z5,z6])],[(0,[z35,z7,z1,z2,z310,z5,z6])],[(0,[z112,z7,z1,z61,z4,z5,z6]),(0,[z1,z2,z66,z4,z59,z5,z6]),(0,[z305,z1,z2,z4,z5,z6,z44]),(0,[z7,z518,z1,z2,z4,z5,z6]),(0,[z67,z7,z1,z420,z4,z5,z6]),(0,[z7,z1,z2,z136,z5,z450,z6]),(0,[z7,z1,z2,z4,z5,z6,z519])],[(0,[z520,z7,z1,z2,z4,z5,z6]),(0,[z116,z1,z2,z4,z5,z6,z44]),(1,[z207,z7,z1,z2,z5,z6]),(1,[z7,z154,z166,z4,z5,z6])],[(0,[z7,z9,z2,z4,z5,z33,z6])],[(0,[z0,z52,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z521,z6]),(0,[z7,z1,z2,z454,z4,z5,z6]),(0,[z7,z1,z2,z117,z5,z22,z6]),(1,[z7,z522,z2,z4,z5,z6])],[(0,[z523,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z50,z6,z44]),(0,[z7,z1,z351,z2,z30,z5,z6])],[(0,[z107,z116,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z22,z6,z44]),(0,[z7,z1,z2,z4,z5,z6,z408])],[(0,[z138,z7,z1,z2,z30,z5,z6])],[(1,[z99,z1,z2,z4,z59,z6]),(0,[z7,z1,z2,z4,z5,z212,z129]),(0,[z52,z7,z2,z4,z5,z6,z58]),(0,[z7,z1,z2,z4,z5,z6,z524])],[(1,[z1,z2,z30,z5,z6,z44]),(0,[z52,z7,z1,z2,z5,z22,z6]),(0,[z49,z7,z152,z1,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z525,z6]),(0,[z7,z1,z2,z30,z5,z50,z6]),(0,[z93,z7,z1,z2,z42,z5,z6])],[(0,[z26,z7,z1,z2,z4,z5,z6]),(1,[z7,z74,z2,z4,z5,z6]),(0,[z152,z416,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z44,z17]),(0,[z7,z24,z1,z2,z117,z5,z6])],[(1,[z7,z1,z2,z5,z450,z6]),(0,[z1,z2,z4,z5,z50,z6,z199]),(0,[z526,z7,z1,z2,z4,z5,z6])]],
   [[(1,[z7,z1,z2,z82,z5,z6]),(0,[z63,z7,z2,z4,z5,z6,z58]),(0,[z527,z7,z1,z2,z4,z5,z6])],[(0,[z47,z112,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z528]),(0,[z7,z1,z2,z4,z529,z5,z6])],[(0,[z7,z152,z1,z2,z372,z5,z6]),(0,[z93,z7,z1,z57,z4,z5,z6])],[(0,[z7,z1,z2,z4,z530,z5,z6]),(0,[z7,z1,z2,z105,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z6,z328]),(0,[z7,z8,z1,z2,z5,z22,z6]),(0,[z531,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z150,z4,z141,z5,z6]),(0,[z7,z1,z2,z5,z22,z6,z17])],[(0,[z7,z1,z2,z198,z4,z5,z6]),(0,[z7,z1,z532,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z533,z6]),(0,[z7,z534,z1,z2,z4,z5,z6]),(0,[z21,z54,z1,z2,z4,z5,z6])],[(0,[z49,z7,z1,z2,z117,z5,z6]),(0,[z24,z1,z334,z2,z4,z5,z6]),(0,[z276,z7,z1,z2,z4,z5,z6])],[(0,[z535,z7,z1,z2,z4,z5,z6])],[(0,[z107,z7,z1,z2,z5,z25,z6]),(0,[z536,z7,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z69,z88,z6]),(0,[z7,z1,z2,z4,z91,z141,z6])],[(0,[z7,z1,z2,z166,z30,z5,z6]),(0,[z537,z7,z1,z2,z4,z5,z6])],[(0,[z47,z7,z1,z2,z4,z48,z6]),(0,[z538,z7,z1,z2,z4,z5,z6]),(0,[z7,z518,z24,z1,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z539,z6]),(0,[z7,z1,z2,z4,z5,z6,z540]),(0,[z7,z1,z2,z4,z5,z129,z6])],[(0,[z7,z1,z2,z541,z4,z5,z6]),(0,[z7,z2,z166,z4,z5,z6,z58]),(0,[z21,z7,z24,z1,z2,z5,z6]),(0,[z7,z1,z2,z4,z542,z5,z6]),(0,[z7,z1,z2,z4,z5,z414,z6])],[(0,[z1,z61,z2,z3,z4,z5,z6]),(0,[z285,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z460,z5,z6])],[(0,[z52,z7,z2,z72,z4,z5,z6]),(1,[z7,z1,z2,z91,z22,z6])],[(0,[z1,z2,z3,z66,z4,z5,z6]),(0,[z47,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z543,z4,z5,z6]),(0,[z544,z7,z1,z2,z4,z5,z6]),(1,[z308,z1,z2,z4,z5,z6])]],
   [[(0,[z65,z1,z2,z4,z5,z6,z44]),(0,[z7,z24,z1,z2,z5,z22,z6])],[(0,[z7,z1,z2,z4,z5,z6,z545]),(0,[z7,z1,z2,z4,z5,z6,z546])],[(0,[z67,z7,z1,z2,z488,z5,z6]),(1,[z262,z7,z1,z2,z5,z6])],[(0,[z7,z547,z1,z2,z4,z5,z6]),(0,[z49,z7,z1,z166,z4,z5,z6]),(0,[z7,z1,z103,z2,z5,z25,z6]),(0,[z7,z548,z1,z2,z4,z5,z6]),(0,[z29,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z549,z2,z4,z5,z6])],[(1,[z54,z1,z2,z30,z5,z6]),(0,[z1,z2,z4,z5,z168,z6,z337])],[(0,[z7,z1,z2,z4,z5,z254,z6]),(0,[z1,z120,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z297,z30,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z550])],[(0,[z551,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z121,z4,z5,z6]),(0,[z7,z1,z522,z2,z4,z5,z6])],[(0,[z7,z188,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z552,z5,z6])],[(0,[z7,z144,z2,z166,z4,z5,z6]),(0,[z67,z7,z1,z2,z542,z5,z6]),(0,[z1,z103,z2,z96,z4,z5,z6]),(0,[z7,z1,z4,z5,z50,z6,z16])],[(1,[z7,z1,z2,z4,z5,z6]),(1,[z207,z1,z2,z5,z6,z44]),(0,[z54,z1,z2,z4,z5,z129,z6]),(0,[z52,z7,z154,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z553,z6]),(0,[z52,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z554,z4,z5,z6]),(0,[z7,z1,z2,z141,z5,z555,z6]),(0,[z7,z1,z2,z30,z5,z6,z17])],[(0,[z7,z1,z2,z4,z510,z5,z6])],[(0,[z7,z1,z556,z2,z4,z5,z6]),(0,[z7,z24,z1,z2,z72,z5,z6]),(0,[z404,z1,z2,z4,z5,z168,z6])],[(1,[z7,z1,z2,z4,z5,z260]),(0,[z277,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z129,z6])],[(0,[z7,z1,z2,z4,z557,z5,z6]),(0,[z7,z2,z166,z72,z4,z5,z6]),(0,[z558,z7,z1,z2,z4,z5,z6]),(1,[z34,z7,z1,z2,z5,z6]),(1,[z7,z1,z2,z492,z5,z6]),(0,[z7,z1,z2,z139,z4,z5,z25])]],
   [[(0,[z7,z1,z2,z4,z5,z168,z6])],[(1,[z416,z1,z2,z4,z5,z6]),(0,[z67,z516,z1,z2,z4,z5,z6]),(0,[z7,z8,z1,z2,z4,z5,z6]),(0,[z559,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z4,z22,z6])],[(0,[z7,z560,z1,z2,z4,z5,z6]),(0,[z561,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z562,z6]),(0,[z7,z1,z2,z4,z5,z563,z6]),(0,[z564,z7,z1,z2,z4,z5,z6]),(0,[z7,z24,z1,z2,z19,z5,z6]),(0,[z29,z7,z1,z4,z5,z6,z16])],[(0,[z7,z24,z1,z2,z196,z5,z6])],[(0,[z54,z1,z2,z4,z5,z25,z6]),(0,[z93,z7,z1,z2,z30,z5,z6])],[(0,[z7,z1,z2,z565,z4,z5,z6]),(0,[z49,z7,z1,z2,z72,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z451]),(0,[z7,z1,z2,z4,z5,z566,z6]),(0,[z7,z1,z2,z4,z5,z567,z6]),(0,[z7,z1,z2,z4,z141,z6,z17]),(1,[z7,z1,z2,z139,z5,z25])],[(0,[z568,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z335,z5,z6]),(0,[z7,z1,z2,z4,z5,z140,z6])],[(0,[z1,z9,z2,z4,z5,z6,z44]),(0,[z7,z1,z569,z2,z4,z5,z6]),(0,[z570,z7,z1,z2,z4,z5,z6])],[(0,[z47,z7,z1,z226,z4,z5,z6]),(1,[z7,z1,z352,z4,z5,z6]),(0,[z7,z1,z571,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z572,z6])],[],[(0,[z49,z7,z1,z2,z19,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z573]),(0,[z7,z1,z2,z4,z129,z6,z17])],[(0,[z574,z7,z1,z2,z4,z5,z6]),(0,[z29,z7,z1,z120,z4,z5,z6])],[(0,[z7,z27,z2,z4,z5,z33,z6]),(0,[z7,z1,z2,z4,z5,z212,z6]),(1,[z181,z1,z2,z4,z5,z6]),(1,[z29,z7,z1,z4,z5,z16])],[(0,[z1,z2,z4,z5,z6,z322,z44])],[(0,[z112,z7,z1,z2,z30,z5,z6]),(0,[z54,z1,z2,z4,z5,z168,z6]),(0,[z575,z7,z1,z2,z4,z5,z6]),(0,[z7,z24,z1,z2,z4,z5,z6]),(0,[z576,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z120,z4,z5,z50,z6])],[(0,[z99,z7,z1,z2,z30,z5,z6]),(0,[z54,z8,z1,z2,z4,z5,z6]),(0,[z7,z28,z1,z2,z4,z5,z6]),(1,[z7,z1,z420,z4,z5,z6]),(0,[z7,z1,z2,z439,z30,z5,z6])]],
   [[(0,[z577,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z578,z5,z6]),(1,[z7,z283,z2,z4,z5,z6]),(0,[z68,z52,z1,z2,z4,z5,z6])],[(0,[z29,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z98,z5,z22,z6])],[(0,[z7,z1,z2,z4,z5,z579,z6]),(0,[z7,z1,z2,z4,z342,z5,z6]),(1,[z116,z1,z2,z105,z5,z6]),(1,[z38,z7,z2,z117,z5,z6]),(0,[z67,z7,z8,z2,z4,z5,z6]),(0,[z7,z1,z120,z2,z4,z5,z16]),(0,[z7,z1,z2,z4,z5,z6,z580])],[(0,[z7,z1,z581,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z582,z5,z6]),(0,[z7,z1,z2,z5,z6,z43,z44]),(0,[z54,z1,z2,z565,z4,z5,z6])],[(0,[z7,z103,z2,z417,z4,z5,z6]),(0,[z444,z7,z1,z2,z30,z5,z6])],[(0,[z7,z1,z2,z160,z4,z5,z6]),(0,[z583,z7,z1,z2,z4,z5,z6]),(0,[z7,z144,z2,z4,z117,z5,z6])],[(1,[z7,z1,z2,z5,z418,z6]),(0,[z7,z1,z2,z4,z267,z5,z6])],[(0,[z47,z7,z1,z2,z4,z5,z254]),(0,[z7,z1,z2,z584,z4,z5,z6]),(0,[z29,z7,z1,z2,z492,z5,z6]),(0,[z7,z1,z2,z4,z5,z585,z6])],[(0,[z7,z1,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z443,z5,z6]),(0,[z1,z2,z4,z5,z6,z44,z528]),(0,[z7,z1,z2,z4,z5,z6,z586])],[(0,[z1,z2,z139,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z6,z237]),(0,[z93,z7,z169,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z212,z6]),(0,[z7,z1,z2,z4,z587,z5,z6]),(0,[z7,z1,z588,z2,z4,z5,z6])],[(1,[z7,z2,z436,z4,z5,z6]),(1,[z7,z1,z2,z5,z6,z519]),(0,[z7,z1,z2,z4,z5,z6,z106])],[(0,[z112,z26,z1,z2,z4,z5,z6]),(0,[z54,z24,z1,z2,z4,z5,z6]),(0,[z7,z152,z1,z2,z5,z22,z6])],[(0,[z7,z1,z2,z589,z4,z5,z6]),(0,[z7,z24,z1,z352,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z555,z6])],[(0,[z590,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z48,z6,z44]),(0,[z7,z1,z2,z4,z5,z69,z6]),(0,[z591,z7,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z592,z5,z6])],[(0,[z7,z1,z2,z4,z5,z593,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z594,z6])],[(0,[z7,z595,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z596,z5,z6])],[(0,[z7,z152,z1,z4,z5,z88,z6]),(0,[z35,z181,z1,z2,z4,z5,z6])],[(0,[z7,z1,z597,z2,z4,z5,z6]),(0,[z93,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z6,z399]),(0,[z7,z1,z2,z83,z4,z5,z6]),(1,[z7,z1,z346,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z5,z129])],[(0,[z54,z1,z2,z4,z5,z6,z44]),(0,[z54,z7,z1,z2,z4,z5,z212]),(0,[z7,z8,z2,z4,z136,z5,z6])],[(0,[z1,z103,z2,z4,z5,z6,z44]),(0,[z7,z8,z2,z4,z5,z6,z58])],[(0,[z7,z1,z2,z4,z5,z6,z598]),(0,[z1,z2,z4,z196,z5,z6,z44]),(0,[z52,z7,z152,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z599,z5,z6]),(0,[z7,z1,z2,z600,z4,z5,z6]),(0,[z21,z7,z1,z235,z4,z5,z6])],[(0,[z601,z7,z1,z2,z4,z5,z6]),(1,[z65,z1,z61,z4,z5,z6]),(0,[z602,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z139,z4,z5,z106])],[(1,[z1,z2,z4,z5,z129,z44])],[(0,[z7,z1,z2,z603,z4,z5,z6]),(0,[z107,z7,z1,z2,z30,z5,z6]),(0,[z222,z54,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z6,z106]),(0,[z7,z1,z2,z403,z4,z5,z6])],[],[(0,[z0,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z604]),(0,[z27,z1,z2,z4,z59,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z605]),(0,[z7,z152,z1,z4,z5,z6,z16]),(0,[z7,z1,z2,z4,z606,z5,z6]),(0,[z7,z607,z1,z2,z4,z5,z6])],[(0,[z608,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z609,z5,z6]),(0,[z7,z1,z87,z2,z4,z5,z6]),(0,[z7,z1,z2,z96,z4,z5,z6])],[(0,[z0,z1,z9,z2,z4,z5,z6]),(0,[z112,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z226,z2,z4,z5,z6]),(0,[z7,z610,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z611]),(0,[z7,z612,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z488,z5,z6]),(1,[z176,z1,z2,z4,z5,z6]),(0,[z97,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z5,z363,z22,z6])],[(0,[z7,z1,z613,z2,z4,z5,z6]),(0,[z116,z1,z2,z4,z59,z5,z6]),(0,[z99,z1,z2,z4,z5,z6,z44]),(1,[z7,z1,z150,z4,z141,z6]),(0,[z7,z1,z2,z57,z4,z5,z6])],[]],
   [[(0,[z7,z1,z2,z614,z4,z5,z6]),(0,[z35,z7,z522,z2,z4,z5,z6]),(1,[z7,z548,z2,z4,z5,z6]),(0,[z615,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z616,z2,z4,z5,z6])],[(0,[z7,z1,z2,z617,z4,z5,z6]),(0,[z7,z1,z2,z72,z5,z22,z6])],[(0,[z7,z24,z2,z4,z5,z6,z58]),(0,[z618,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z619,z6]),(1,[z7,z1,z2,z542,z5,z6])],[(0,[z7,z1,z2,z4,z620,z5,z6]),(0,[z7,z152,z1,z120,z4,z5,z6]),(0,[z7,z1,z621,z2,z4,z5,z6]),(0,[z7,z1,z103,z2,z30,z5,z6]),(0,[z35,z7,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z622,z5,z6])],[(0,[z7,z1,z623,z2,z4,z5,z6]),(1,[z368,z1,z2,z5,z22,z6]),(0,[z21,z7,z1,z2,z4,z422,z6])],[(0,[z7,z1,z2,z624,z4,z5,z6])],[(0,[z446,z1,z2,z4,z5,z6,z44]),(0,[z7,z625,z1,z2,z4,z5,z6])],[(0,[z47,z1,z61,z2,z4,z5,z6]),(0,[z54,z99,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z626,z5,z6]),(0,[z7,z1,z2,z449,z91,z5,z6])],[(0,[z65,z1,z61,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z627]),(0,[z7,z1,z2,z4,z5,z25,z6])],[(0,[z7,z1,z2,z436,z4,z5,z6]),(0,[z7,z152,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z4,z5,z88,z6])],[(0,[z7,z1,z2,z4,z136,z5,z6]),(0,[z49,z7,z1,z2,z5,z22,z6])],[(0,[z7,z1,z2,z139,z117,z5,z6]),(1,[z516,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z58])],[],[(0,[z7,z1,z2,z4,z628,z5,z6]),(1,[z36,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z629,z4,z5,z6])],[(0,[z484,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z630,z5,z6])]],
   [[(0,[z7,z154,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z5,z631,z6])],[(0,[z7,z1,z2,z4,z632,z5,z6]),(0,[z7,z1,z2,z221,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z633]),(0,[z1,z2,z4,z5,z129,z6,z275])],[(0,[z7,z634,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z25,z6,z224])],[(0,[z112,z1,z2,z4,z59,z5,z6]),(1,[z7,z1,z2,z5,z6,z43]),(0,[z7,z1,z2,z4,z5,z6,z635]),(1,[z495,z1,z2,z4,z5,z6])],[(1,[z7,z518,z1,z4,z5,z6])],[(0,[z7,z24,z2,z72,z4,z5,z6]),(0,[z21,z7,z1,z2,z4,z5,z25])],[(0,[z7,z1,z2,z636,z4,z5,z6]),(0,[z7,z1,z4,z196,z5,z6,z16]),(0,[z35,z7,z548,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z637,z6])],[],[(0,[z107,z1,z2,z4,z5,z6,z44]),(0,[z54,z152,z1,z2,z4,z5,z6]),(0,[z54,z7,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z638,z5,z6]),(0,[z7,z1,z2,z30,z98,z5,z6]),(1,[z7,z441,z2,z4,z5,z6])],[(0,[z639,z7,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z48,z6]),(0,[z54,z1,z2,z4,z136,z5,z6]),(0,[z7,z1,z2,z4,z88,z6,z17]),(1,[z7,z124,z2,z4,z5,z6]),(0,[z640,z7,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z6,z58]),(0,[z7,z1,z2,z4,z641,z5,z6]),(0,[z63,z7,z1,z2,z4,z5,z168])],[(0,[z7,z1,z2,z642,z4,z5,z6]),(0,[z97,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z361,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z44,z44]),(0,[z7,z1,z2,z643,z4,z5,z6]),(1,[z7,z1,z2,z5,z140,z6])],[(0,[z1,z2,z4,z5,z6,z179,z44]),(0,[z52,z7,z8,z2,z4,z5,z6]),(0,[z49,z7,z1,z2,z196,z5,z6]),(0,[z644,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z139,z5,z22,z6]),(1,[z252,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z30,z105,z5,z6]),(0,[z7,z1,z2,z72,z4,z5,z6]),(0,[z7,z144,z2,z4,z5,z33,z6])]],
   [[(0,[z1,z9,z61,z2,z4,z5,z6]),(0,[z7,z645,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z272,z4,z5,z6])],[(0,[z7,z646,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z647]),(0,[z7,z1,z2,z4,z5,z6,z648]),(0,[z7,z1,z2,z4,z64,z5,z6]),(0,[z7,z1,z2,z4,z98,z91,z6])],[(0,[z26,z99,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z44,z106]),(0,[z7,z1,z166,z19,z4,z5,z6]),(0,[z35,z7,z1,z2,z4,z5,z6])],[(0,[z7,z298,z1,z2,z4,z5,z6]),(0,[z244,z54,z1,z2,z4,z5,z6]),(0,[z649,z7,z1,z2,z4,z5,z6]),(1,[z368,z1,z2,z4,z5,z6])],[(1,[z112,z1,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z650]),(0,[z7,z1,z2,z4,z5,z651,z6]),(0,[z7,z1,z2,z4,z91,z5,z6])],[(0,[z0,z65,z1,z2,z4,z5,z6]),(0,[z26,z116,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z4,z5,z567])],[(0,[z7,z27,z1,z2,z92,z5,z6]),(0,[z7,z1,z2,z4,z5,z652,z6]),(0,[z7,z1,z2,z4,z5,z653,z6]),(0,[z7,z1,z2,z91,z5,z22,z6])],[(0,[z38,z7,z1,z2,z5,z25,z6])],[],[(1,[z7,z1,z2,z342,z5,z6]),(0,[z7,z654,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z655,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z163,z6]),(0,[z49,z7,z1,z2,z4,z5,z6])],[],[(0,[z7,z283,z1,z2,z4,z5,z6]),(0,[z67,z28,z1,z2,z4,z5,z6]),(0,[z29,z495,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z656,z6]),(0,[z7,z1,z2,z4,z5,z168,z17])],[(0,[z54,z1,z2,z72,z4,z5,z6]),(0,[z7,z657,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z658]),(0,[z7,z1,z2,z167,z4,z5,z6]),(0,[z7,z1,z2,z5,z22,z6,z16])],[(0,[z7,z659,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z117,z5,z6,z106]),(0,[z67,z7,z1,z2,z4,z5,z40]),(0,[z7,z1,z2,z4,z5,z6,z660])],[(0,[z7,z1,z2,z4,z5,z6,z661]),(0,[z7,z1,z2,z5,z88,z22,z6]),(0,[z7,z1,z2,z30,z5,z287,z6])]],
   [[(0,[z47,z1,z2,z66,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z6]),(0,[z7,z2,z4,z5,z168,z6,z58]),(0,[z7,z1,z2,z4,z5,z6,z199])],[(0,[z447,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z139,z196,z5,z6])],[(0,[z26,z7,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z662,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z44,z604]),(0,[z54,z1,z2,z4,z91,z5,z6])],[(0,[z27,z1,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z5,z48,z6]),(0,[z663,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z664,z4,z5,z6]),(0,[z665,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z270,z4,z5,z6]),(0,[z116,z54,z1,z2,z4,z5,z6]),(1,[z7,z1,z2,z5,z555,z6]),(1,[z7,z1,z2,z449,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z260]),(1,[z1,z2,z4,z5,z44,z17]),(0,[z7,z1,z2,z4,z5,z6,z666])],[(0,[z116,z1,z9,z2,z4,z5,z6]),(0,[z63,z7,z1,z2,z4,z64,z6]),(0,[z7,z1,z150,z2,z30,z5,z6]),(0,[z7,z1,z2,z667,z4,z5,z6])],[(0,[z7,z1,z441,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z212,z17]),(0,[z7,z1,z2,z4,z5,z6,z668]),(0,[z7,z1,z2,z4,z5,z445,z6])],[(0,[z669,z7,z1,z2,z4,z5,z6]),(0,[z7,z95,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z670,z4,z5,z6]),(0,[z7,z671,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z672]),(1,[z7,z1,z253,z4,z5,z6])],[(0,[z35,z7,z1,z2,z4,z5,z567]),(0,[z100,z7,z1,z2,z4,z5,z6])],[(0,[z26,z7,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z139,z4,z5,z6])],[(0,[z99,z7,z1,z2,z4,z48,z6]),(0,[z7,z1,z2,z4,z5,z673,z6]),(0,[z7,z1,z2,z4,z5,z6,z674]),(0,[z21,z7,z1,z2,z4,z5,z106])],[(1,[z0,z9,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z6,z6]),(0,[z313,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z59,z5,z6]),(0,[z7,z1,z2,z675,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z676,z6]),(0,[z7,z677,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z354,z6])],[],[(0,[z7,z1,z2,z4,z5,z6,z678])],[(0,[z1,z2,z4,z5,z6,z44,z58]),(0,[z7,z1,z2,z4,z136,z6,z17]),(0,[z7,z1,z2,z5,z6,z519,z16])],[(0,[z679,z7,z1,z2,z4,z5,z6]),(0,[z38,z1,z2,z4,z5,z6,z44]),(0,[z680,z7,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z6,z681]),(0,[z7,z1,z2,z682,z4,z5,z6]),(0,[z47,z7,z1,z2,z4,z59,z6]),(0,[z7,z1,z2,z4,z683,z5,z6]),(0,[z7,z1,z2,z4,z5,z684,z6]),(0,[z63,z7,z1,z221,z4,z5,z6]),(0,[z7,z1,z2,z5,z233,z22,z6])],[(0,[z7,z1,z2,z19,z5,z22,z6])],[(0,[z685,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z686,z6]),(0,[z7,z1,z2,z687,z4,z5,z6])],[(0,[z1,z9,z2,z66,z4,z5,z6]),(0,[z7,z1,z688,z2,z4,z5,z6]),(0,[z49,z7,z1,z4,z196,z5,z6]),(0,[z7,z1,z2,z5,z22,z22,z6])],[(0,[z152,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z341,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z129,z168])],[(0,[z54,z1,z2,z139,z4,z5,z6])],[],[(0,[z7,z1,z689,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z690,z5,z6]),(0,[z691,z7,z1,z2,z4,z5,z6])],[(0,[z692,z7,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z59,z5,z6])],[(0,[z7,z1,z61,z2,z443,z5,z6]),(0,[z47,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z117,z5,z6]),(0,[z7,z1,z2,z4,z693,z5,z6])],[(0,[z256,z54,z1,z2,z4,z5,z6]),(0,[z7,z1,z694,z2,z4,z5,z6]),(0,[z52,z7,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z337])]],
   [[],[(0,[z26,z1,z2,z4,z5,z6,z44]),(0,[z29,z7,z1,z2,z83,z5,z6])],[(0,[z7,z154,z2,z166,z4,z5,z6]),(0,[z695,z7,z1,z2,z4,z5,z6]),(0,[z276,z24,z1,z2,z4,z5,z6]),(0,[z277,z1,z2,z4,z5,z25,z6])],[(0,[z7,z1,z2,z4,z5,z696,z6]),(0,[z7,z1,z697,z2,z4,z5,z6]),(0,[z698,z7,z1,z2,z4,z5,z6]),(0,[z255,z7,z1,z2,z4,z5,z6])],[(0,[z47,z27,z1,z2,z4,z5,z6]),(0,[z7,z1,z61,z2,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z5,z6]),(0,[z1,z2,z4,z5,z6,z44,z10]),(0,[z7,z1,z2,z4,z5,z699,z6]),(0,[z67,z7,z1,z2,z4,z136,z6]),(0,[z63,z7,z1,z2,z30,z5,z6])],[(0,[z65,z27,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z700,z4,z5,z6])],[(0,[z54,z1,z688,z2,z4,z5,z6]),(0,[z67,z7,z1,z2,z30,z5,z6]),(0,[z7,z8,z1,z2,z30,z5,z6]),(1,[z7,z1,z2,z510,z5,z6])],[(0,[z701,z7,z1,z2,z4,z5,z6]),(0,[z99,z1,z2,z4,z59,z5,z6]),(0,[z7,z1,z2,z4,z702,z5,z6])],[(1,[z7,z298,z1,z4,z5,z6]),(0,[z138,z54,z1,z2,z4,z5,z6]),(0,[z207,z7,z1,z2,z4,z5,z6]),(0,[z703,z7,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z118,z4,z5,z6]),(1,[z145,z1,z2,z4,z5,z6])],[(0,[z7,z1,z61,z4,z5,z88,z6])],[(1,[z7,z1,z454,z4,z5,z6])],[(0,[z536,z1,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z6,z704])],[(0,[z54,z1,z694,z2,z4,z5,z6])],[(0,[z7,z1,z2,z175,z4,z5,z6])],[(0,[z7,z1,z2,z705,z4,z5,z6]),(0,[z116,z7,z1,z2,z105,z5,z6]),(1,[z7,z1,z2,z5,z6,z451]),(0,[z706,z7,z1,z2,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z47,z1,z2,z4,z619,z6]),(0,[z47,z1,z2,z4,z48,z254]),(0,[z143,z288,z2,z4,z5,z6]),(0,[z7,z2,z72,z707,z5,z6]),(0,[z7,z708,z2,z4,z5,z6]),(0,[z21,z7,z1,z253,z5,z106])],[(0,[z246,z1,z2,z4,z5,z6]),(0,[z7,z413,z4,z5,z6,z16])],[(0,[z7,z1,z2,z709,z5,z6]),(0,[z615,z7,z1,z4,z88,z6]),(0,[z7,z1,z2,z4,z206,z129])],[(0,[z1,z2,z431,z66,z5,z6]),(0,[z7,z74,z2,z175,z5,z6]),(0,[z214,z7,z166,z4,z5,z6]),(0,[z7,z1,z2,z710,z5,z6]),(0,[z7,z1,z2,z4,z91,z711])],[(0,[z1,z2,z4,z5,z48,z260]),(0,[z7,z1,z2,z5,z712,z6]),(0,[z307,z7,z2,z117,z5,z6]),(0,[z7,z1,z2,z488,z5,z328]),(0,[z7,z1,z235,z4,z5,z6]),(0,[z1,z2,z4,z5,z567,z713])],[(0,[z7,z1,z714,z4,z5,z6]),(0,[z7,z1,z715,z4,z5,z6]),(0,[z1,z2,z66,z5,z418,z6]),(0,[z716,z1,z2,z4,z5,z6]),(0,[z717,z1,z2,z4,z5,z6]),(0,[z24,z334,z2,z72,z5,z6]),(0,[z7,z1,z167,z4,z5,z40]),(0,[z7,z548,z2,z310,z5,z6]),(0,[z29,z7,z1,z4,z460,z16])],[(0,[z75,z1,z2,z4,z5,z6]),(0,[z7,z1,z718,z4,z5,z6]),(0,[z9,z2,z4,z5,z151,z6]),(0,[z654,z9,z2,z4,z5,z6])],[(0,[z116,z1,z2,z719,z5,z6]),(0,[z7,z2,z72,z217,z5,z6]),(0,[z7,z1,z2,z4,z720,z6]),(0,[z721,z7,z1,z2,z5,z6]),(0,[z7,z1,z2,z5,z722,z6])],[(0,[z7,z1,z2,z4,z5,z723]),(0,[z7,z1,z2,z684,z22,z6]),(0,[z7,z1,z724,z4,z5,z6]),(0,[z725,z1,z2,z5,z6,z199])],[(0,[z26,z27,z270,z4,z5,z6]),(0,[z726,z1,z2,z4,z5,z6]),(0,[z727,z1,z2,z4,z5,z6])],[(0,[z116,z1,z2,z5,z6,z224]),(0,[z728,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z542,z5,z328]),(0,[z7,z413,z120,z4,z5,z6])],[(0,[z7,z1,z2,z5,z6,z729]),(0,[z54,z730,z2,z4,z5,z6]),(0,[z7,z1,z2,z731,z5,z6]),(0,[z7,z1,z2,z5,z732,z6]),(0,[z7,z1,z2,z139,z5,z487]),(0,[z36,z1,z2,z4,z5,z408]),(0,[z29,z7,z1,z4,z414,z16]),(0,[z7,z1,z2,z449,z22,z6])],[(0,[z54,z1,z2,z733,z5,z6]),(0,[z7,z393,z166,z4,z5,z6]),(0,[z7,z1,z2,z707,z5,z6]),(0,[z95,z1,z2,z30,z5,z6]),(0,[z734,z1,z2,z4,z5,z6]),(0,[z35,z7,z1,z30,z88,z6]),(0,[z7,z1,z120,z4,z5,z50]),(1,[z7,z1,z2,z735,z6]),(0,[z236,z1,z2,z5,z233,z6])],[(0,[z7,z1,z736,z4,z5,z6]),(0,[z213,z7,z2,z30,z5,z6]),(0,[z54,z1,z2,z5,z6,z43]),(0,[z93,z1,z2,z4,z44,z17]),(0,[z7,z1,z2,z737,z5,z6]),(0,[z7,z1,z150,z4,z302,z6]),(0,[z38,z7,z2,z195,z5,z6]),(0,[z7,z352,z72,z4,z5,z6]),(0,[z7,z1,z2,z738,z5,z6]),(0,[z7,z1,z2,z5,z70,z25])],[(0,[z7,z1,z2,z739,z5,z6]),(0,[z213,z9,z2,z4,z5,z6]),(0,[z54,z1,z2,z740,z5,z6]),(0,[z54,z518,z1,z4,z5,z6])],[(0,[z7,z1,z741,z4,z5,z6]),(0,[z207,z1,z9,z2,z5,z6]),(0,[z7,z1,z742,z4,z5,z6]),(0,[z1,z61,z454,z4,z5,z6]),(0,[z7,z1,z743,z4,z5,z6]),(0,[z441,z2,z4,z5,z6,z44]),(0,[z1,z2,z4,z5,z319,z44]),(0,[z1,z744,z2,z4,z5,z6]),(0,[z67,z7,z2,z488,z33,z6])]],
   [[(0,[z1,z2,z175,z5,z6,z44]),(0,[z355,z1,z2,z4,z5,z6]),(0,[z7,z413,z2,z4,z5,z6]),(0,[z7,z1,z2,z22,z6,z442])],[(0,[z7,z1,z745,z4,z5,z6]),(0,[z7,z1,z2,z746,z5,z6]),(0,[z116,z1,z2,z111,z5,z6]),(0,[z107,z7,z1,z2,z422,z6]),(0,[z138,z1,z2,z30,z5,z44]),(0,[z1,z2,z361,z5,z6,z44]),(0,[z7,z2,z417,z4,z5,z6]),(0,[z7,z1,z2,z747,z5,z6]),(0,[z748,z1,z2,z4,z5,z6]),(0,[z7,z1,z221,z30,z5,z6]),(0,[z7,z1,z2,z310,z5,z6]),(0,[z7,z124,z235,z4,z5,z6])],[(0,[z54,z441,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z749,z6]),(0,[z644,z7,z1,z2,z4,z17]),(0,[z178,z1,z2,z5,z22,z6])],[(0,[z1,z2,z4,z5,z327,z44]),(0,[z7,z74,z2,z5,z22,z6]),(0,[z7,z1,z750,z4,z5,z6]),(0,[z54,z124,z2,z4,z5,z6]),(0,[z516,z1,z2,z4,z5,z328]),(0,[z7,z1,z2,z751,z5,z6])],[(0,[z7,z752,z1,z4,z5,z6]),(0,[z7,z1,z196,z5,z6,z524]),(0,[z7,z1,z2,z139,z5,z753])],[(0,[z298,z1,z4,z59,z5,z6]),(0,[z7,z1,z226,z30,z5,z6]),(0,[z1,z2,z4,z5,z329,z44]),(0,[z207,z1,z2,z5,z44,z17]),(0,[z7,z1,z2,z30,z330,z6])],[(0,[z1,z2,z4,z5,z331,z44]),(0,[z7,z1,z2,z4,z5,z754]),(0,[z54,z1,z2,z5,z6,z451]),(0,[z35,z36,z1,z4,z88,z6]),(0,[z7,z413,z2,z492,z5,z6])],[(0,[z1,z454,z66,z4,z5,z6]),(0,[z54,z1,z2,z5,z140,z6]),(0,[z755,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z756,z6]),(0,[z7,z1,z2,z5,z757,z6]),(0,[z207,z1,z2,z5,z6,z528]),(0,[z52,z152,z416,z4,z5,z6]),(0,[z7,z758,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z759,z6]),(0,[z760,z1,z2,z4,z5,z6])],[(0,[z213,z119,z2,z4,z5,z6]),(0,[z1,z2,z30,z22,z6,z44]),(0,[z38,z7,z2,z217,z5,z6]),(0,[z7,z1,z2,z30,z434,z6]),(0,[z1,z2,z4,z5,z6,z761])],[(0,[z437,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z683,z6])],[(0,[z762,z1,z2,z4,z5,z6]),(0,[z1,z2,z5,z163,z763,z6]),(0,[z404,z1,z2,z5,z22,z6]),(0,[z764,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z765,z6])],[(0,[z7,z766,z2,z4,z5,z6]),(0,[z559,z7,z152,z4,z5,z6]),(0,[z1,z2,z4,z5,z767,z6]),(0,[z7,z1,z2,z5,z6,z768]),(0,[z21,z31,z1,z2,z5,z106])],[(0,[z446,z1,z2,z4,z6,z89]),(0,[z54,z1,z2,z4,z5,z769]),(0,[z276,z24,z2,z72,z5,z6]),(0,[z7,z770,z2,z4,z5,z6])],[(1,[z1,z2,z4,z771,z6]),(0,[z47,z1,z2,z48,z22,z6]),(0,[z67,z7,z2,z4,z33,z6]),(0,[z1,z2,z4,z5,z6,z772]),(0,[z7,z1,z2,z460,z22,z6]),(0,[z7,z1,z2,z5,z6,z773])],[(0,[z27,z774,z2,z4,z5,z6]),(0,[z1,z2,z775,z5,z6,z44]),(0,[z1,z4,z5,z6,z44,z776]),(0,[z777,z1,z2,z4,z5,z6]),(0,[z778,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z567]),(0,[z7,z1,z2,z30,z134,z6])]],
   [[(0,[z7,z124,z2,z4,z422,z6])],[(1,[z1,z779,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z780]),(0,[z1,z2,z5,z450,z6,z44]),(0,[z1,z2,z4,z349,z6,z399]),(0,[z7,z1,z2,z30,z344,z6])],[(0,[z7,z1,z2,z620,z22,z6]),(0,[z413,z2,z4,z5,z6,z44]),(0,[z7,z677,z166,z4,z5,z6]),(0,[z781,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z134,z22,z6]),(0,[z7,z1,z2,z5,z25,z753]),(0,[z7,z1,z2,z4,z129,z711])],[(0,[z54,z1,z2,z342,z5,z6]),(0,[z7,z2,z4,z5,z782,z58]),(0,[z7,z783,z2,z4,z5,z6])],[(0,[z784,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z175,z5,z260]),(0,[z7,z1,z2,z30,z5,z254]),(0,[z256,z694,z2,z4,z5,z6]),(0,[z97,z54,z1,z2,z22,z6]),(0,[z7,z8,z2,z4,z5,z328]),(0,[z181,z1,z2,z310,z5,z6]),(0,[z7,z1,z2,z785,z5,z6])],[(0,[z7,z1,z786,z4,z5,z6]),(0,[z734,z1,z2,z4,z5,z567]),(0,[z29,z7,z1,z4,z5,z787]),(0,[z7,z1,z411,z4,z5,z50]),(0,[z252,z1,z2,z4,z422,z6])],[(0,[z774,z1,z2,z4,z5,z6]),(0,[z7,z1,z788,z4,z5,z6]),(0,[z7,z1,z789,z4,z5,z6])],[(0,[z7,z2,z4,z790,z5,z6]),(0,[z7,z441,z2,z4,z91,z6])],[(0,[z1,z2,z4,z5,z791,z6]),(0,[z7,z2,z792,z4,z5,z6]),(0,[z1,z2,z4,z5,z44,z605]),(0,[z7,z1,z2,z793,z5,z6]),(1,[z1,z2,z4,z5,z769]),(0,[z7,z1,z794,z4,z5,z6]),(0,[z7,z1,z2,z4,z134,z168]),(0,[z7,z1,z2,z5,z795,z6]),(0,[z1,z2,z4,z5,z6,z796]),(0,[z7,z1,z2,z797,z5,z6]),(0,[z7,z1,z2,z552,z22,z6])],[(0,[z207,z7,z1,z2,z5,z6]),(0,[z68,z1,z2,z198,z5,z6]),(0,[z798,z1,z2,z4,z5,z328]),(0,[z7,z1,z2,z139,z5,z20]),(0,[z799,z1,z2,z5,z22,z6])],[(0,[z800,z7,z2,z4,z5,z6]),(0,[z669,z1,z2,z4,z5,z44]),(0,[z7,z1,z801,z4,z5,z6]),(0,[z7,z1,z2,z361,z5,z6]),(0,[z21,z7,z518,z1,z5,z6]),(0,[z21,z7,z124,z2,z5,z106])],[(0,[z802,z1,z2,z4,z5,z6]),(0,[z564,z7,z2,z4,z33,z6]),(0,[z52,z7,z152,z30,z5,z6]),(0,[z75,z1,z2,z5,z22,z6]),(0,[z803,z1,z2,z4,z5,z6]),(0,[z7,z1,z4,z88,z6,z408]),(0,[z1,z2,z30,z804,z5,z6])],[(0,[z7,z1,z2,z410,z22,z6]),(0,[z35,z181,z1,z4,z88,z6])],[(0,[z112,z1,z705,z4,z5,z6]),(0,[z1,z2,z4,z5,z233,z6]),(0,[z7,z1,z167,z30,z5,z6])],[(0,[z1,z2,z310,z5,z6,z44]),(0,[z54,z1,z2,z5,z555,z6]),(0,[z164,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z414,z805,z6]),(0,[z7,z1,z2,z30,z187,z6])],[(0,[z1,z334,z352,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z806,z5,z6]),(0,[z178,z1,z2,z4,z5,z6]),(0,[z807,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z808,z5,z6]),(0,[z119,z8,z2,z4,z5,z6]),(0,[z809,z1,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z810])],[(0,[z7,z74,z2,z4,z5,z6]),(0,[z1,z2,z372,z5,z6,z44]),(0,[z7,z1,z2,z811,z5,z6]),(0,[z7,z1,z2,z812,z5,z6]),(0,[z238,z7,z1,z2,z5,z106]),(0,[z1,z2,z5,z22,z813,z6])],[(0,[z7,z1,z2,z814,z5,z6]),(0,[z815,z7,z1,z2,z5,z6]),(0,[z816,z1,z2,z5,z6,z519])],[(0,[z1,z2,z92,z5,z6,z44]),(0,[z1,z2,z4,z414,z6,z44]),(0,[z7,z1,z2,z5,z450,z6]),(0,[z665,z7,z1,z196,z5,z6]),(0,[z1,z2,z4,z5,z6,z817]),(0,[z818,z1,z2,z5,z22,z6]),(0,[z7,z2,z30,z819,z5,z6])],[(0,[z7,z1,z270,z30,z5,z6]),(0,[z7,z820,z2,z4,z5,z6]),(0,[z7,z1,z2,z82,z5,z6]),(0,[z54,z1,z253,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z821]),(0,[z67,z7,z420,z4,z33,z6]),(0,[z7,z243,z2,z83,z5,z6])],[(0,[z822,z7,z1,z2,z5,z6]),(0,[z67,z516,z2,z4,z33,z6]),(0,[z7,z1,z2,z823,z5,z6]),(0,[z7,z1,z2,z4,z460,z6]),(0,[z7,z1,z824,z4,z5,z6])],[(0,[z7,z1,z2,z5,z825,z6]),(0,[z7,z74,z2,z4,z5,z260]),(0,[z276,z1,z2,z30,z5,z6]),(0,[z277,z1,z2,z30,z5,z6])],[(0,[z1,z2,z719,z4,z5,z6]),(0,[z116,z1,z2,z185,z5,z6]),(0,[z1,z2,z4,z5,z6,z275]),(0,[z7,z752,z154,z4,z5,z6]),(0,[z52,z119,z152,z4,z5,z6])],[(0,[z1,z2,z4,z59,z300,z6]),(0,[z7,z1,z2,z826,z5,z6]),(0,[z1,z827,z4,z5,z6,z44]),(0,[z7,z1,z2,z372,z5,z6]),(0,[z7,z1,z2,z641,z22,z6]),(0,[z828,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z134,z829,z6]),(0,[z1,z2,z30,z5,z69,z6])],[(0,[z7,z1,z2,z830,z5,z6]),(0,[z404,z1,z2,z4,z5,z6]),(0,[z7,z831,z2,z4,z5,z6]),(0,[z7,z1,z2,z82,z5,z260]),(0,[z7,z1,z2,z832,z5,z6]),(0,[z7,z1,z120,z4,z5,z113]),(0,[z31,z1,z2,z30,z5,z6])],[(0,[z7,z1,z833,z4,z5,z6]),(0,[z1,z2,z542,z5,z6,z44]),(0,[z54,z834,z2,z4,z5,z6]),(0,[z54,z1,z2,z5,z835,z6]),(0,[z1,z2,z4,z5,z6,z836]),(0,[z262,z7,z1,z103,z5,z6])],[(0,[z53,z1,z2,z4,z5,z44]),(0,[z7,z1,z2,z492,z460,z6])],[(0,[z7,z1,z2,z837,z5,z6]),(0,[z178,z441,z2,z4,z5,z6])],[(0,[z1,z103,z19,z5,z6,z44])],[(0,[z7,z1,z2,z838,z5,z6]),(0,[z7,z1,z352,z5,z22,z6]),(0,[z181,z522,z2,z4,z5,z6])],[(0,[z65,z1,z688,z4,z5,z6]),(0,[z49,z1,z196,z5,z6,z44]),(0,[z7,z1,z2,z4,z839,z6]),(0,[z840,z7,z2,z30,z5,z6])]],
   [[(0,[z561,z1,z2,z4,z5,z44]),(0,[z7,z1,z2,z4,z5,z841]),(0,[z65,z1,z779,z4,z5,z6]),(0,[z63,z54,z2,z4,z5,z58]),(0,[z416,z1,z2,z372,z5,z6]),(0,[z95,z1,z221,z4,z5,z6]),(0,[z7,z1,z4,z5,z50,z787])],[(0,[z7,z8,z2,z4,z291,z6]),(0,[z116,z1,z2,z203,z5,z6]),(0,[z54,z1,z2,z30,z5,z44]),(0,[z164,z1,z2,z196,z5,z6]),(0,[z7,z1,z2,z22,z6,z234]),(0,[z7,z1,z2,z272,z22,z6]),(0,[z255,z7,z1,z60,z5,z6]),(0,[z7,z1,z253,z4,z422,z6])],[(0,[z54,z1,z2,z4,z5,z258]),(0,[z7,z1,z2,z842,z5,z6]),(0,[z54,z1,z2,z843,z5,z6]),(0,[z844,z1,z2,z4,z5,z6]),(0,[z7,z845,z2,z4,z5,z6]),(0,[z495,z1,z2,z4,z414,z6])],[(0,[z1,z2,z4,z5,z6,z846]),(0,[z7,z1,z2,z847,z5,z6]),(0,[z848,z1,z2,z4,z5,z6]),(0,[z849,z1,z2,z4,z5,z6])],[(0,[z0,z2,z603,z4,z5,z6]),(0,[z7,z1,z597,z19,z5,z6]),(0,[z7,z1,z2,z850,z5,z6]),(0,[z7,z1,z2,z5,z6,z851])],[(0,[z1,z2,z4,z141,z44,z17]),(0,[z1,z334,z2,z5,z22,z6]),(0,[z7,z1,z420,z5,z22,z6]),(0,[z1,z2,z4,z5,z6,z852])],[(0,[z176,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z88,z44,z17]),(0,[z67,z54,z2,z4,z33,z6]),(0,[z7,z621,z166,z4,z5,z6]),(0,[z7,z1,z2,z853,z5,z6]),(0,[z1,z2,z4,z5,z6,z854]),(0,[z7,z1,z2,z91,z450,z6]),(0,[z7,z1,z4,z5,z6,z787])],[(0,[z7,z1,z2,z30,z582,z6]),(0,[z176,z152,z1,z4,z5,z6]),(0,[z799,z1,z2,z4,z5,z6]),(0,[z855,z1,z2,z4,z5,z6]),(0,[z368,z1,z2,z5,z233,z6])],[(0,[z368,z1,z2,z105,z5,z6]),(0,[z368,z1,z2,z66,z5,z6]),(0,[z1,z2,z4,z5,z6,z856]),(0,[z7,z857,z1,z4,z5,z6])],[(0,[z7,z858,z1,z4,z5,z6]),(0,[z7,z1,z2,z859,z5,z6]),(0,[z285,z1,z2,z565,z5,z6]),(0,[z54,z1,z2,z5,z22,z212]),(0,[z101,z7,z2,z217,z5,z6]),(0,[z7,z243,z2,z30,z5,z6]),(0,[z7,z1,z2,z139,z422,z6]),(0,[z178,z1,z2,z4,z5,z17]),(0,[z7,z1,z2,z57,z4,z17])],[(0,[z1,z2,z5,z6,z44,z519]),(0,[z207,z54,z1,z2,z5,z44]),(0,[z1,z2,z4,z129,z44,z17]),(0,[z7,z428,z166,z4,z5,z6]),(0,[z860,z1,z2,z4,z5,z6]),(0,[z307,z7,z2,z5,z84,z6])],[(0,[z1,z494,z2,z4,z5,z44]),(0,[z26,z7,z270,z4,z5,z6]),(0,[z26,z1,z2,z162,z5,z6]),(0,[z7,z2,z436,z443,z5,z6]),(0,[z7,z283,z2,z82,z5,z6]),(0,[z1,z2,z4,z5,z6,z861]),(0,[z862,z1,z2,z4,z5,z6]),(0,[z28,z2,z4,z5,z33,z6]),(0,[z7,z1,z2,z4,z863,z6]),(0,[z311,z7,z1,z2,z4,z17]),(0,[z7,z1,z2,z269,z5,z6]),(0,[z864,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z5,z408]),(0,[z7,z1,z2,z4,z735,z6]),(0,[z245,z1,z2,z297,z5,z6]),(0,[z7,z1,z2,z5,z6,z865])],[(0,[z164,z1,z2,z4,z5,z6]),(0,[z54,z1,z866,z4,z5,z6]),(0,[z867,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z868]),(0,[z7,z1,z869,z4,z5,z6]),(0,[z1,z2,z30,z870,z5,z6])],[(0,[z7,z1,z871,z4,z5,z6]),(0,[z1,z2,z4,z5,z415,z44]),(0,[z7,z1,z2,z5,z6,z872]),(0,[z873,z7,z1,z2,z5,z6])],[(0,[z7,z1,z2,z5,z874,z6]),(0,[z7,z154,z166,z5,z22,z6]),(0,[z875,z1,z2,z4,z5,z6]),(0,[z95,z1,z2,z4,z134,z6]),(0,[z7,z1,z2,z876,z5,z6]),(0,[z7,z877,z2,z4,z5,z6])],[(0,[z107,z1,z2,z480,z5,z6])]],
   [[(0,[z7,z1,z878,z4,z5,z6]),(0,[z54,z1,z2,z510,z5,z6]),(0,[z879,z1,z2,z4,z5,z6]),(0,[z7,z522,z2,z5,z22,z6])],[(0,[z7,z1,z2,z880,z5,z6]),(0,[z7,z2,z436,z5,z22,z6]),(0,[z207,z54,z1,z2,z5,z6]),(0,[z881,z1,z2,z4,z5,z6]),(0,[z38,z7,z2,z197,z5,z6]),(0,[z7,z1,z2,z5,z882,z6]),(0,[z7,z1,z2,z5,z6,z883]),(0,[z35,z7,z1,z251,z88,z6]),(0,[z818,z1,z2,z4,z5,z6])],[(0,[z54,z298,z1,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z260]),(0,[z1,z2,z5,z749,z450,z6]),(0,[z7,z1,z4,z5,z787,z16]),(0,[z884,z1,z2,z4,z5,z6])],[(0,[z7,z166,z589,z4,z5,z6]),(0,[z7,z1,z885,z4,z5,z6]),(0,[z7,z1,z221,z4,z134,z6]),(0,[z7,z1,z103,z5,z18,z6]),(0,[z1,z2,z4,z5,z6,z886]),(0,[z816,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z6,z887]),(0,[z888,z1,z2,z4,z5,z6]),(0,[z21,z164,z1,z2,z5,z6]),(0,[z7,z1,z2,z91,z22,z129]),(0,[z889,z1,z2,z30,z5,z6]),(0,[z7,z890,z2,z30,z5,z6]),(0,[z7,z891,z2,z30,z5,z6]),(0,[z892,z1,z2,z4,z5,z6])],[(0,[z54,z1,z454,z4,z5,z6]),(0,[z7,z1,z2,z4,z312,z129]),(0,[z38,z7,z2,z707,z5,z6]),(0,[z7,z1,z2,z893,z5,z6]),(0,[z894,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z895,z22,z6])],[(0,[z1,z2,z162,z5,z6,z44]),(0,[z815,z1,z2,z5,z6,z44]),(0,[z36,z1,z2,z310,z5,z6]),(0,[z7,z522,z4,z5,z88,z6])],[(0,[z0,z694,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z896]),(0,[z26,z288,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z897,z6]),(0,[z54,z1,z2,z156,z5,z6]),(0,[z7,z752,z166,z4,z5,z6]),(0,[z7,z1,z2,z898,z5,z6]),(0,[z49,z7,z417,z4,z5,z6]),(0,[z1,z899,z2,z30,z5,z6])],[(0,[z7,z1,z2,z900,z5,z6]),(0,[z7,z901,z2,z4,z5,z6]),(0,[z67,z7,z2,z542,z33,z6]),(0,[z7,z1,z902,z4,z5,z6])],[(0,[z7,z1,z903,z4,z5,z6]),(0,[z822,z1,z2,z5,z6,z44]),(0,[z52,z7,z90,z4,z5,z6]),(0,[z252,z1,z235,z4,z5,z6])],[(0,[z26,z634,z2,z4,z5,z6]),(0,[z7,z2,z624,z72,z5,z6]),(0,[z495,z413,z2,z4,z5,z6]),(0,[z31,z241,z2,z4,z5,z6]),(0,[z178,z1,z346,z4,z5,z6])],[(0,[z27,z1,z454,z4,z5,z6]),(0,[z1,z2,z4,z771,z48,z6]),(0,[z1,z2,z5,z22,z6,z44]),(0,[z1,z2,z4,z5,z44,z660]),(0,[z93,z54,z1,z2,z4,z17]),(0,[z904,z1,z2,z4,z5,z6]),(0,[z7,z417,z4,z5,z6,z16]),(0,[z1,z2,z4,z5,z199,z17])],[(0,[z112,z1,z118,z4,z5,z6]),(0,[z47,z213,z2,z4,z5,z6]),(0,[z7,z1,z2,z905,z5,z6]),(0,[z7,z906,z2,z4,z5,z6]),(0,[z7,z1,z226,z4,z5,z254]),(0,[z1,z2,z4,z5,z6,z907]),(0,[z7,z1,z352,z4,z5,z6]),(0,[z908,z1,z2,z4,z5,z6]),(0,[z7,z909,z2,z4,z5,z6])],[(0,[z53,z1,z2,z4,z280,z6]),(0,[z583,z7,z166,z4,z5,z6]),(0,[z49,z7,z241,z2,z5,z6]),(0,[z7,z1,z910,z4,z5,z6])],[(0,[z7,z1,z911,z4,z5,z6]),(0,[z26,z207,z1,z2,z5,z6]),(0,[z47,z1,z2,z4,z771,z6]),(0,[z1,z2,z912,z5,z6,z44]),(0,[z7,z1,z2,z4,z913,z6]),(0,[z176,z1,z166,z4,z5,z6])],[(0,[z7,z914,z2,z4,z5,z6]),(0,[z1,z2,z5,z915,z6,z44]),(0,[z1,z2,z4,z5,z6,z713]),(0,[z93,z7,z1,z2,z22,z17])]],
   [[(0,[z7,z350,z166,z4,z5,z6]),(0,[z7,z1,z2,z916,z5,z6]),(0,[z29,z7,z1,z4,z5,z16]),(0,[z29,z262,z7,z1,z5,z16]),(0,[z7,z1,z2,z70,z22,z17])],[(0,[z7,z1,z917,z4,z5,z6]),(0,[z119,z1,z2,z30,z5,z6])],[(0,[z7,z1,z2,z175,z5,z6]),(0,[z207,z1,z2,z5,z6,z604]),(0,[z7,z1,z2,z22,z44,z17]),(0,[z1,z2,z4,z5,z918,z6]),(0,[z1,z2,z5,z22,z6,z199])],[(0,[z1,z334,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z40]),(0,[z54,z1,z2,z42,z5,z6]),(0,[z7,z1,z420,z4,z5,z6]),(0,[z7,z919,z1,z2,z5,z6]),(0,[z920,z1,z2,z4,z5,z6]),(0,[z63,z7,z2,z4,z5,z782])],[(0,[z7,z1,z2,z5,z921,z6]),(0,[z7,z2,z4,z134,z6,z58]),(0,[z97,z7,z1,z2,z735,z6])],[(0,[z116,z1,z2,z5,z233,z6]),(0,[z1,z2,z4,z5,z6,z922]),(0,[z169,z2,z4,z5,z6,z44]),(0,[z7,z1,z2,z4,z5,z923]),(0,[z1,z2,z139,z5,z25,z224]),(0,[z7,z1,z2,z510,z91,z6])],[(0,[z7,z1,z2,z924,z5,z6]),(0,[z116,z1,z2,z105,z5,z6]),(0,[z925,z1,z2,z4,z5,z6]),(0,[z7,z548,z2,z5,z22,z6]),(0,[z29,z7,z1,z492,z5,z16]),(0,[z21,z7,z1,z2,z187,z106])],[(1,[z774,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z212]),(0,[z38,z7,z166,z19,z5,z6]),(0,[z1,z2,z4,z5,z6,z926]),(0,[z100,z243,z2,z4,z5,z6])],[(0,[z1,z341,z4,z5,z6,z44]),(0,[z927,z1,z2,z4,z5,z6]),(0,[z7,z518,z1,z117,z5,z6]),(0,[z7,z1,z928,z4,z5,z6]),(0,[z63,z437,z2,z4,z5,z58]),(0,[z7,z1,z2,z30,z22,z6]),(0,[z308,z1,z2,z5,z22,z6])],[(0,[z7,z283,z2,z4,z5,z260]),(0,[z54,z1,z57,z4,z5,z6])],[(0,[z7,z221,z4,z5,z6,z58]),(0,[z7,z1,z2,z5,z6,z929])],[(0,[z7,z930,z2,z4,z5,z6]),(0,[z7,z441,z2,z4,z5,z129])],[(0,[z7,z1,z2,z443,z5,z6]),(0,[z1,z2,z162,z59,z5,z6]),(0,[z7,z154,z166,z4,z5,z6]),(0,[z238,z7,z1,z4,z5,z16])],[(0,[z213,z7,z2,z162,z5,z6]),(0,[z1,z57,z4,z5,z6,z44]),(0,[z54,z1,z2,z4,z64,z6]),(0,[z7,z1,z2,z4,z931,z6]),(0,[z28,z1,z2,z4,z5,z328]),(0,[z7,z1,z2,z310,z5,z567]),(0,[z7,z1,z235,z5,z6,z106]),(0,[z308,z1,z346,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z932]),(0,[z933,z1,z2,z4,z5,z6]),(0,[z7,z522,z2,z4,z5,z6])],[(0,[z7,z2,z436,z4,z5,z6]),(0,[z7,z1,z934,z4,z5,z6]),(0,[z7,z935,z2,z4,z5,z6]),(0,[z1,z2,z156,z5,z6,z44]),(0,[z1,z2,z936,z30,z5,z6]),(0,[z7,z1,z2,z30,z91,z129])]],
   [[(0,[z7,z1,z2,z937,z5,z6]),(0,[z7,z938,z2,z4,z5,z6])],[(0,[z213,z2,z3,z4,z5,z6]),(0,[z1,z454,z4,z5,z48,z6]),(0,[z355,z1,z2,z4,z5,z212]),(0,[z7,z1,z2,z939,z5,z6]),(0,[z7,z1,z2,z272,z422,z6])],[(0,[z7,z1,z2,z5,z22,z6]),(0,[z7,z940,z2,z4,z5,z6]),(0,[z99,z1,z2,z4,z59,z6]),(0,[z54,z24,z2,z72,z5,z6]),(0,[z68,z52,z152,z4,z5,z6]),(0,[z941,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z942])],[(0,[z7,z1,z2,z943,z5,z6]),(0,[z1,z2,z30,z5,z6,z44]),(0,[z1,z2,z30,z5,z163,z6])],[(0,[z298,z1,z9,z4,z5,z6]),(0,[z1,z2,z5,z418,z6,z44]),(0,[z1,z2,z4,z5,z944,z6]),(0,[z7,z1,z2,z208,z64,z6]),(0,[z7,z1,z2,z5,z945,z6])],[(0,[z7,z1,z2,z702,z22,z6])],[(0,[z7,z1,z2,z946,z5,z6]),(0,[z54,z1,z2,z83,z5,z6]),(0,[z34,z7,z241,z2,z5,z6]),(0,[z947,z7,z1,z2,z5,z6])],[(0,[z7,z1,z2,z5,z22,z260]),(0,[z1,z2,z948,z5,z6,z44]),(0,[z368,z1,z2,z117,z5,z6])],[(0,[z7,z949,z2,z4,z5,z6]),(0,[z305,z1,z4,z5,z6,z10])],[(0,[z7,z283,z2,z175,z5,z6]),(0,[z491,z7,z2,z4,z33,z6]),(0,[z7,z950,z2,z4,z5,z6]),(0,[z7,z1,z2,z951,z5,z6]),(0,[z7,z2,z952,z4,z5,z6])],[(0,[z7,z1,z2,z953,z5,z6]),(0,[z416,z1,z2,z5,z22,z6]),(0,[z1,z2,z30,z5,z6,z199]),(0,[z7,z1,z30,z954,z5,z6]),(0,[z178,z1,z2,z510,z5,z6])],[(0,[z1,z2,z5,z6,z44,z955])],[(0,[z1,z2,z4,z5,z956,z6]),(0,[z54,z1,z221,z4,z5,z6]),(0,[z68,z1,z2,z217,z5,z6])],[(0,[z957,z1,z2,z4,z5,z6]),(0,[z7,z8,z2,z136,z22,z6]),(0,[z7,z958,z2,z4,z5,z6]),(0,[z501,z7,z1,z2,z22,z6]),(0,[z7,z1,z235,z139,z5,z6])],[(0,[z7,z1,z2,z959,z5,z6]),(0,[z7,z152,z128,z4,z5,z6]),(0,[z95,z1,z2,z208,z5,z6]),(0,[z1,z2,z960,z4,z5,z6]),(0,[z1,z2,z4,z5,z961,z6]),(0,[z7,z441,z2,z5,z22,z6]),(0,[z7,z1,z57,z4,z91,z6])],[(0,[z7,z1,z2,z4,z962,z6]),(0,[z49,z7,z1,z171,z5,z6]),(0,[z63,z7,z2,z4,z64,z58]),(0,[z495,z1,z2,z4,z460,z6]),(0,[z165,z368,z1,z2,z5,z6]),(0,[z7,z124,z2,z5,z22,z6])]],
   [[(0,[z7,z74,z454,z4,z5,z6]),(0,[z7,z2,z217,z5,z6,z58]),(0,[z416,z1,z4,z5,z88,z6]),(0,[z7,z1,z150,z269,z141,z6]),(0,[z7,z413,z2,z83,z5,z6])],[(0,[z7,z1,z963,z4,z5,z6]),(0,[z7,z1,z2,z488,z5,z6]),(0,[z1,z2,z5,z22,z6,z337]),(0,[z7,z1,z2,z964,z5,z6]),(0,[z313,z7,z2,z267,z5,z6])],[(0,[z692,z7,z166,z4,z5,z6]),(0,[z0,z1,z454,z4,z5,z6]),(0,[z7,z270,z4,z5,z33,z6]),(0,[z7,z1,z2,z965,z5,z6]),(0,[z7,z1,z2,z64,z22,z6]),(0,[z966,z1,z2,z4,z5,z6])],[(0,[z7,z1,z454,z82,z5,z6]),(0,[z7,z518,z1,z372,z5,z6]),(0,[z7,z1,z221,z208,z5,z6]),(0,[z7,z967,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z968])],[(0,[z138,z207,z1,z2,z5,z44]),(0,[z7,z548,z2,z4,z5,z6]),(0,[z7,z144,z221,z4,z5,z6]),(0,[z7,z1,z2,z969,z460,z6])],[(0,[z116,z1,z2,z301,z5,z6]),(0,[z181,z1,z2,z5,z22,z6]),(0,[z29,z7,z1,z5,z22,z16]),(0,[z7,z1,z2,z91,z22,z6])],[(0,[z308,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z970,z6]),(0,[z246,z1,z2,z30,z5,z6]),(0,[z1,z2,z4,z5,z6,z971]),(0,[z972,z1,z2,z4,z5,z6]),(0,[z7,z1,z973,z4,z5,z6])],[(0,[z7,z298,z1,z92,z5,z6]),(0,[z7,z1,z2,z4,z5,z974]),(0,[z7,z1,z2,z4,z5,z975]),(0,[z391,z1,z2,z4,z5,z44]),(0,[z7,z518,z1,z72,z5,z6]),(0,[z7,z976,z1,z4,z5,z6]),(0,[z7,z1,z341,z4,z64,z6]),(0,[z7,z1,z2,z4,z5,z977]),(0,[z7,z522,z2,z4,z5,z567]),(0,[z978,z1,z2,z4,z5,z6])],[(0,[z7,z979,z2,z4,z5,z6]),(0,[z116,z7,z1,z2,z422,z6]),(0,[z7,z1,z2,z5,z829,z6])],[(0,[z0,z774,z2,z4,z5,z6]),(0,[z7,z283,z2,z5,z22,z6]),(0,[z7,z1,z980,z4,z5,z6]),(0,[z7,z1,z2,z981,z5,z6]),(0,[z262,z7,z1,z2,z5,z6]),(0,[z7,z1,z235,z30,z5,z6])],[(0,[z982,z7,z1,z2,z5,z6]),(0,[z7,z1,z2,z983,z5,z6]),(0,[z7,z1,z2,z984,z5,z6]),(0,[z53,z1,z2,z4,z5,z260]),(0,[z7,z1,z2,z985,z5,z6]),(0,[z465,z7,z2,z117,z5,z6]),(0,[z29,z100,z1,z4,z5,z16]),(0,[z986,z1,z2,z4,z5,z6]),(0,[z31,z1,z2,z4,z187,z6])],[(0,[z54,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z5,z22,z567])],[(0,[z7,z1,z2,z4,z5,z987]),(0,[z1,z2,z92,z59,z5,z6]),(0,[z7,z1,z2,z988,z5,z6]),(0,[z447,z1,z688,z4,z5,z6]),(0,[z222,z1,z2,z185,z5,z6]),(0,[z7,z1,z989,z4,z5,z6]),(0,[z7,z518,z1,z19,z5,z6]),(0,[z7,z1,z103,z235,z5,z6]),(0,[z7,z1,z2,z5,z6,z753])],[(0,[z7,z1,z2,z4,z990,z6]),(0,[z7,z1,z2,z895,z91,z6]),(0,[z991,z1,z2,z30,z5,z6]),(0,[z178,z1,z2,z42,z5,z6])],[(0,[z27,z2,z4,z5,z6,z179]),(0,[z7,z1,z2,z30,z314,z6]),(0,[z368,z1,z2,z82,z5,z6]),(0,[z63,z7,z221,z4,z5,z58]),(0,[z1,z2,z992,z4,z5,z6]),(0,[z368,z1,z2,z5,z363,z6]),(0,[z7,z993,z2,z5,z22,z6])],[(0,[z7,z1,z2,z948,z5,z6]),(0,[z7,z1,z994,z4,z5,z6]),(0,[z1,z2,z42,z5,z6,z44]),(0,[z49,z7,z1,z197,z5,z6]),(0,[z1,z2,z5,z69,z22,z6])]],
   [[(0,[z7,z1,z2,z4,z5,z6]),(0,[z246,z9,z2,z4,z5,z6]),(0,[z116,z1,z2,z318,z5,z6]),(0,[z207,z1,z2,z5,z6,z44]),(0,[z164,z1,z2,z5,z25,z6]),(0,[z7,z1,z2,z251,z5,z408]),(0,[z7,z1,z120,z492,z5,z6])],[(0,[z446,z1,z2,z4,z48,z6]),(0,[z995,z1,z2,z4,z5,z6]),(0,[z7,z996,z2,z4,z5,z6])],[(0,[z7,z1,z2,z5,z997,z6]),(0,[z998,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z999,z5,z6]),(1,[z7,z2,z4,z33,z328]),(0,[z7,z1,z2,z1000,z5,z6]),(0,[z7,z241,z2,z4,z187,z6]),(0,[z308,z441,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z562,z44]),(0,[z38,z7,z1,z2,z422,z6]),(0,[z178,z1,z57,z4,z5,z6])],[(0,[z1,z2,z4,z33,z44,z17]),(0,[z1,z2,z4,z5,z1001,z6])],[(0,[z26,z27,z2,z92,z5,z6]),(0,[z154,z166,z4,z5,z6,z44]),(0,[z7,z1,z2,z1002,z5,z6]),(0,[z7,z413,z2,z30,z5,z6]),(0,[z355,z1,z2,z30,z5,z6]),(0,[z93,z308,z1,z2,z4,z17])],[(0,[z7,z1,z2,z1003,z5,z6]),(0,[z1,z2,z269,z5,z6,z44]),(0,[z34,z7,z1,z2,z5,z6]),(0,[z368,z1,z2,z72,z5,z6]),(0,[z7,z1,z2,z4,z136,z328]),(0,[z7,z1,z2,z492,z5,z6]),(0,[z7,z2,z417,z30,z5,z6]),(0,[z7,z2,z1004,z30,z5,z6])],[(0,[z7,z1,z2,z5,z6,z1005]),(0,[z7,z1,z2,z5,z6,z43]),(0,[z1,z2,z5,z555,z6,z44]),(0,[z7,z2,z707,z117,z5,z6]),(0,[z7,z1,z420,z488,z5,z6]),(0,[z1006,z1,z2,z4,z5,z6]),(0,[z181,z548,z2,z4,z5,z6])],[(0,[z416,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z740,z5,z6]),(0,[z7,z1,z2,z1007,z5,z6]),(0,[z7,z1,z2,z30,z5,z328]),(0,[z7,z1,z2,z30,z422,z6])],[(0,[z54,z1,z103,z19,z5,z6]),(0,[z262,z7,z1,z166,z5,z6]),(0,[z7,z1,z2,z4,z1008,z6]),(0,[z7,z1,z2,z422,z22,z6])],[(0,[z65,z1,z61,z443,z5,z6]),(0,[z7,z1,z2,z5,z25,z598]),(0,[z1,z2,z5,z1009,z555,z6])],[(0,[z47,z1,z2,z4,z151,z6]),(0,[z7,z1010,z2,z4,z5,z6]),(0,[z368,z1,z2,z19,z5,z6]),(0,[z7,z1,z588,z4,z141,z6]),(0,[z93,z7,z1,z2,z30,z17])],[(0,[z7,z1,z2,z1011,z5,z6]),(0,[z7,z1,z2,z4,z5,z1012]),(0,[z1,z2,z1013,z4,z5,z6]),(0,[z1,z2,z4,z5,z1014,z6]),(0,[z7,z441,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1015]),(0,[z7,z1,z103,z5,z6,z177]),(0,[z145,z1,z120,z4,z5,z50]),(0,[z1,z2,z5,z22,z6,z1016]),(0,[z7,z1,z346,z5,z22,z6]),(0,[z7,z1,z2,z139,z5,z25])],[(0,[z7,z1017,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z771,z6]),(0,[z7,z124,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1018]),(0,[z7,z1,z420,z542,z5,z6]),(0,[z63,z7,z2,z30,z5,z58]),(0,[z7,z1,z2,z5,z6,z1019]),(0,[z7,z548,z2,z4,z5,z567])],[(0,[z7,z1020,z2,z4,z5,z6]),(0,[z7,z1,z150,z141,z22,z6])],[(0,[z1021,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z779,z4,z5,z6]),(0,[z65,z1,z61,z5,z22,z6]),(0,[z54,z169,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1022,z5,z6]),(0,[z65,z416,z1,z4,z5,z6]),(0,[z7,z512,z2,z72,z5,z6]),(0,[z7,z1,z2,z1023,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1024]),(0,[z213,z65,z2,z4,z5,z6]),(0,[z1,z2,z4,z22,z44,z17]),(0,[z1,z1025,z2,z4,z5,z6]),(0,[z7,z1,z2,z1026,z5,z6])],[(0,[z181,z1,z2,z4,z5,z6]),(0,[z67,z7,z2,z33,z22,z6]),(0,[z67,z7,z2,z30,z33,z6]),(0,[z7,z1,z4,z951,z5,z6])],[(0,[z0,z9,z2,z5,z22,z6]),(0,[z52,z7,z2,z403,z5,z6]),(0,[z7,z24,z2,z250,z5,z6]),(0,[z1,z2,z1027,z5,z163,z6])],[(0,[z54,z1,z2,z4,z5,z332]),(0,[z1,z1028,z4,z5,z6,z44]),(0,[z7,z1,z341,z30,z5,z6]),(0,[z7,z1,z2,z83,z460,z6])],[(0,[z207,z1,z2,z59,z5,z6]),(0,[z52,z152,z4,z5,z6,z44]),(0,[z798,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1029]),(0,[z7,z1,z103,z195,z5,z6]),(0,[z7,z1,z2,z4,z1030,z6]),(0,[z516,z1,z420,z4,z5,z6]),(0,[z176,z1,z2,z5,z22,z6])],[(0,[z7,z283,z2,z4,z5,z6]),(0,[z425,z27,z2,z4,z5,z6]),(0,[z7,z1,z2,z139,z5,z287]),(0,[z7,z1,z2,z30,z85,z6])],[(0,[z65,z7,z436,z4,z5,z6]),(0,[z1031,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1032,z5,z6])],[(0,[z54,z1,z2,z4,z5,z405]),(0,[z116,z74,z2,z4,z5,z6]),(0,[z1033,z1,z2,z4,z5,z6]),(0,[z38,z7,z2,z117,z5,z6]),(0,[z7,z1,z2,z4,z5,z567]),(0,[z7,z1,z150,z4,z5,z408]),(0,[z1034,z1,z2,z4,z5,z6])],[(0,[z1,z9,z2,z162,z5,z6]),(0,[z1035,z7,z1,z2,z5,z6]),(0,[z1036,z7,z1,z2,z5,z6])],[(0,[z527,z1,z61,z4,z5,z6]),(0,[z7,z1,z2,z1037,z5,z6]),(0,[z1038,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z83,z414,z6]),(0,[z7,z1,z2,z5,z6,z1039])],[(0,[z116,z1,z2,z82,z5,z6]),(0,[z54,z241,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1040]),(0,[z1,z2,z4,z5,z6,z1041]),(0,[z7,z993,z2,z4,z5,z6])],[(0,[z26,z298,z27,z4,z5,z6]),(0,[z7,z1,z2,z4,z1042,z6]),(0,[z7,z1,z2,z5,z418,z6]),(0,[z262,z1,z2,z5,z6,z44]),(0,[z1,z2,z4,z5,z1043,z6]),(0,[z1,z2,z5,z22,z6,z1044])],[(0,[z49,z7,z1,z250,z5,z6]),(0,[z376,z7,z1,z2,z4,z17])],[(0,[z7,z1,z1045,z4,z5,z6]),(0,[z7,z1046,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z1047,z5,z6]),(0,[z7,z1,z827,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1048]),(0,[z311,z7,z2,z4,z5,z58]),(0,[z1049,z1,z2,z4,z5,z6]),(0,[z1050,z7,z1,z2,z5,z6])],[(0,[z107,z7,z241,z2,z5,z6]),(0,[z7,z1,z454,z175,z5,z6]),(0,[z262,z54,z1,z2,z5,z6]),(0,[z1,z2,z1051,z4,z5,z6])],[(0,[z7,z1,z1052,z4,z5,z6]),(0,[z7,z1,z2,z1053,z5,z6]),(0,[z7,z1,z2,z5,z1054,z6]),(0,[z7,z1,z2,z5,z6,z519]),(0,[z7,z1,z2,z4,z5,z1055]),(0,[z7,z1056,z1,z5,z22,z6])],[(0,[z1,z2,z4,z136,z44,z17]),(0,[z1,z253,z4,z5,z6,z44]),(0,[z7,z1,z2,z5,z1057,z6]),(0,[z7,z1,z103,z667,z5,z6]),(0,[z36,z522,z2,z4,z5,z6]),(0,[z100,z413,z2,z4,z5,z6])],[(0,[z7,z1,z1058,z4,z5,z6]),(0,[z7,z1,z2,z1059,z5,z6]),(0,[z7,z1,z2,z30,z630,z6]),(0,[z165,z7,z1,z2,z4,z17])],[(0,[z774,z9,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z44,z681]),(0,[z101,z7,z2,z72,z5,z6]),(0,[z516,z1,z2,z5,z22,z6]),(0,[z1060,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z25,z633]),(0,[z1061,z7,z1,z2,z5,z6]),(0,[z178,z1,z2,z30,z5,z6])],[(0,[z1,z2,z779,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1062]),(0,[z7,z74,z2,z30,z5,z6]),(0,[z97,z1,z2,z22,z6,z44]),(0,[z54,z1,z2,z22,z6,z17])],[(0,[z7,z2,z4,z5,z863,z6]),(0,[z49,z7,z1,z235,z5,z6]),(0,[z36,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z1063,z5,z6]),(0,[z1064,z1,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z370]),(0,[z353,z7,z1,z196,z5,z6]),(0,[z7,z1,z2,z449,z5,z6])],[(0,[z7,z1,z2,z30,z533,z6]),(0,[z54,z1,z2,z160,z5,z6])],[(0,[z7,z1065,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1066,z6]),(0,[z34,z1,z2,z5,z6,z44]),(0,[z1,z2,z4,z5,z6,z1067]),(0,[z241,z2,z4,z5,z6,z44]),(0,[z1068,z1,z2,z4,z5,z6]),(0,[z7,z2,z208,z5,z6,z58]),(0,[z35,z7,z522,z4,z88,z6]),(0,[z7,z1,z346,z4,z5,z6]),(0,[z7,z1,z2,z30,z460,z6]),(0,[z1,z2,z4,z5,z6,z1069]),(0,[z7,z1,z824,z30,z5,z6])],[(0,[z220,z1,z3,z4,z5,z6]),(0,[z1,z87,z4,z5,z6,z322]),(0,[z7,z1,z2,z30,z271,z6]),(0,[z1070,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1071,z6]),(0,[z7,z1,z2,z4,z5,z711])],[(0,[z7,z1,z2,z1072,z5,z6]),(0,[z181,z1,z2,z4,z5,z567]),(0,[z7,z1073,z2,z4,z5,z6]),(0,[z495,z1,z2,z5,z22,z6])],[(0,[z1,z352,z4,z5,z6,z44]),(0,[z1074,z1,z2,z4,z5,z6]),(0,[z7,z752,z2,z4,z5,z6]),(0,[z7,z518,z1,z5,z22,z6]),(1,[z7,z2,z4,z134,z58]),(0,[z36,z1,z4,z5,z88,z6]),(0,[z35,z7,z1,z4,z88,z408]),(0,[z368,z1,z2,z5,z84,z6]),(0,[z1,z2,z5,z6,z865,z275])],[(0,[z65,z1,z61,z4,z5,z6]),(0,[z1,z2,z5,z6,z44,z451]),(0,[z243,z2,z4,z5,z6,z44]),(0,[z34,z54,z1,z2,z5,z6]),(0,[z67,z7,z2,z4,z33,z40]),(0,[z404,z1,z2,z30,z5,z6]),(0,[z7,z1,z253,z4,z5,z6])],[(0,[z65,z298,z1,z4,z5,z6]),(0,[z1,z2,z4,z5,z129,z44]),(0,[z68,z152,z1,z4,z5,z6]),(0,[z1075,z1,z2,z4,z5,z6]),(0,[z1076,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z1077,z5,z6]),(0,[z7,z1,z2,z30,z414,z6]),(0,[z7,z2,z1078,z5,z22,z6]),(0,[z1079,z1,z2,z30,z5,z6]),(0,[z1080,z1,z2,z4,z5,z6])],[(0,[z7,z1,z454,z5,z22,z6]),(0,[z7,z1,z1081,z4,z5,z6]),(0,[z7,z1,z2,z5,z6,z1082])],[(0,[z0,z9,z2,z4,z5,z6]),(0,[z7,z1,z2,z1083,z5,z6]),(0,[z368,z1,z2,z30,z22,z6])],[(0,[z54,z1,z226,z4,z5,z6]),(0,[z47,z1,z2,z175,z48,z6]),(0,[z7,z1084,z1,z4,z5,z6]),(0,[z663,z7,z2,z4,z5,z58]),(0,[z7,z1,z2,z5,z6,z1085]),(0,[z262,z7,z1,z235,z5,z6])],[(0,[z7,z1,z2,z1086,z5,z6]),(0,[z176,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z619,z6]),(0,[z7,z834,z2,z4,z5,z6]),(0,[z7,z1,z1087,z4,z5,z6]),(0,[z516,z1,z2,z488,z5,z6]),(0,[z437,z1,z2,z4,z64,z6]),(0,[z1,z2,z4,z5,z1088,z6]),(0,[z7,z1,z1089,z4,z5,z6]),(0,[z7,z1090,z1,z4,z5,z6])],[(0,[z1,z2,z4,z5,z1091,z6]),(0,[z7,z1,z150,z4,z141,z6])],[(0,[z116,z1,z2,z479,z5,z6]),(0,[z7,z1,z2,z1092,z5,z6]),(0,[z1,z2,z4,z5,z129,z199]),(0,[z1,z2,z4,z5,z6,z1093]),(0,[z7,z441,z346,z4,z5,z6]),(0,[z7,z1,z2,z91,z140,z129])],[(0,[z7,z1,z1094,z4,z5,z6]),(0,[z207,z1,z2,z5,z6,z10]),(0,[z1,z2,z4,z5,z6,z1095]),(0,[z1,z2,z4,z5,z6,z1096]),(0,[z252,z1,z2,z5,z22,z6])],[(0,[z7,z150,z436,z4,z5,z6]),(0,[z107,z7,z1,z235,z5,z6]),(0,[z644,z7,z1,z4,z5,z16])],[(0,[z1,z2,z4,z5,z254,z44]),(0,[z119,z1,z2,z198,z5,z6]),(0,[z1,z2,z4,z5,z6,z1097]),(0,[z7,z1,z1098,z4,z5,z6]),(0,[z36,z548,z2,z4,z5,z6])],[(0,[z7,z1,z1099,z4,z5,z6]),(0,[z7,z1,z1100,z4,z5,z6]),(0,[z116,z1,z2,z4,z5,z260]),(0,[z7,z1,z2,z542,z5,z6]),(0,[z7,z1,z2,z1101,z5,z6])],[(0,[z1102,z1,z2,z4,z5,z6]),(0,[z29,z54,z1,z4,z5,z16]),(0,[z7,z1,z1103,z4,z5,z6])],[(0,[z26,z27,z2,z5,z22,z6]),(0,[z2,z792,z4,z5,z6,z44]),(0,[z7,z24,z2,z707,z5,z6]),(0,[z28,z1,z2,z5,z22,z6]),(0,[z368,z1,z2,z5,z22,z6])],[(0,[z0,z119,z2,z4,z5,z6]),(0,[z47,z1,z2,z4,z239,z6]),(0,[z112,z1,z3,z5,z22,z6]),(0,[z54,z1,z2,z4,z134,z6]),(0,[z7,z157,z2,z4,z136,z6]),(0,[z7,z1,z1104,z4,z5,z6]),(0,[z7,z1,z2,z5,z753,z106])],[(0,[z26,z1,z2,z92,z5,z6]),(0,[z7,z1105,z2,z4,z5,z6]),(0,[z7,z1,z2,z46,z22,z6]),(0,[z54,z1,z2,z1106,z5,z6]),(0,[z1107,z7,z2,z4,z5,z6]),(0,[z7,z1,z2,z1108,z5,z6]),(0,[z75,z1,z2,z30,z5,z6])],[(0,[z7,z1109,z1,z4,z5,z6]),(0,[z7,z2,z166,z403,z5,z6]),(0,[z7,z1,z2,z5,z22,z40]),(0,[z1,z2,z4,z5,z6,z1110]),(0,[z486,z7,z1,z196,z5,z6]),(0,[z1111,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z187,z22,z6]),(0,[z7,z1,z2,z272,z5,z287])]],
   [[(0,[z54,z1,z2,z251,z5,z6]),(0,[z1,z2,z4,z5,z6,z1112]),(0,[z7,z152,z752,z4,z5,z6]),(0,[z7,z518,z1,z196,z5,z6]),(0,[z7,z1056,z1,z4,z5,z6]),(0,[z7,z1,z2,z30,z735,z6]),(0,[z21,z7,z1,z2,z422,z106]),(0,[z308,z1,z2,z510,z5,z6])],[(0,[z7,z1,z2,z5,z1113,z6]),(0,[z38,z54,z2,z117,z5,z6]),(0,[z164,z1,z2,z30,z5,z6])],[(0,[z54,z1,z2,z4,z5,z254]),(0,[z1114,z7,z2,z4,z5,z6]),(0,[z1115,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1116]),(0,[z1,z2,z4,z5,z1117,z6])],[(0,[z516,z1,z2,z4,z5,z6]),(0,[z112,z26,z166,z4,z5,z6]),(0,[z26,z79,z2,z4,z5,z6]),(0,[z437,z1,z221,z4,z5,z6])],[(0,[z1,z2,z342,z5,z6,z44]),(0,[z1,z167,z4,z5,z6,z44]),(0,[z1118,z1,z2,z4,z5,z6]),(0,[z95,z1,z341,z4,z5,z6]),(0,[z7,z1,z2,z208,z134,z6]),(0,[z7,z1,z2,z361,z64,z6])],[(0,[z36,z1,z2,z4,z5,z6]),(0,[z47,z74,z2,z4,z48,z6]),(0,[z1,z2,z5,z6,z1119,z44]),(0,[z7,z1120,z1,z4,z5,z6]),(0,[z7,z144,z2,z4,z134,z6])],[(0,[z7,z1,z866,z4,z5,z6]),(0,[z1,z150,z4,z141,z6,z44]),(0,[z68,z1,z166,z4,z5,z6]),(0,[z52,z7,z152,z198,z5,z6]),(0,[z1121,z1,z2,z4,z5,z6]),(0,[z29,z495,z1,z4,z5,z16])],[(0,[z1,z2,z4,z5,z44,z32]),(0,[z7,z1,z2,z1122,z5,z6]),(0,[z1123,z1,z2,z4,z5,z6]),(0,[z7,z1,z743,z30,z5,z6])],[(0,[z47,z1,z2,z82,z48,z6]),(0,[z7,z730,z2,z4,z5,z6]),(0,[z100,z1,z2,z4,z460,z6])],[(0,[z1,z2,z4,z5,z567,z44]),(0,[z7,z1,z2,z733,z5,z6]),(0,[z101,z7,z2,z117,z5,z6]),(0,[z35,z7,z1,z4,z1124,z6]),(0,[z7,z1,z2,z206,z22,z6]),(0,[z7,z1,z1125,z5,z22,z6])],[(0,[z495,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z412]),(0,[z1,z2,z5,z43,z44,z17]),(0,[z1,z750,z4,z5,z6,z44]),(0,[z7,z1,z2,z510,z5,z6]),(0,[z7,z1,z2,z4,z6,z711])],[(0,[z7,z1,z2,z4,z1126,z6]),(0,[z54,z1,z167,z4,z5,z6]),(0,[z7,z518,z1,z4,z5,z6]),(0,[z52,z7,z152,z403,z5,z6]),(0,[z1127,z1,z2,z4,z5,z6]),(0,[z28,z1,z2,z488,z5,z6])],[(0,[z355,z1,z2,z4,z5,z254]),(0,[z54,z1,z2,z4,z187,z6]),(0,[z1128,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1129,z5,z6]),(0,[z7,z1,z2,z4,z1130,z6]),(0,[z1,z2,z30,z5,z6,z337]),(0,[z7,z1,z2,z80,z22,z6]),(0,[z1131,z1,z2,z4,z5,z6])],[(0,[z99,z1,z2,z4,z280,z6])],[(0,[z7,z2,z4,z33,z58,z17]),(0,[z95,z1,z2,z361,z5,z6]),(0,[z7,z2,z1078,z4,z5,z6]),(0,[z100,z1,z2,z4,z414,z6])],[(0,[z1,z1132,z2,z4,z5,z6]),(0,[z7,z1,z1133,z4,z5,z6]),(0,[z7,z1,z454,z4,z5,z6]),(0,[z63,z7,z2,z4,z134,z58]),(0,[z368,z1,z2,z196,z5,z6]),(0,[z164,z1,z103,z19,z5,z6]),(0,[z7,z1,z2,z969,z5,z6]),(0,[z368,z1,z2,z91,z22,z6])]],
   [[(0,[z47,z298,z1,z4,z5,z6]),(0,[z7,z1134,z2,z4,z5,z6]),(0,[z1,z2,z4,z460,z6,z44]),(0,[z7,z1,z2,z1135,z5,z6]),(0,[z7,z1,z2,z22,z168,z17]),(0,[z7,z1,z2,z4,z1136,z6]),(0,[z495,z1,z2,z492,z5,z6]),(0,[z706,z7,z1,z2,z4,z17]),(0,[z7,z1,z2,z735,z22,z6]),(0,[z165,z7,z1,z2,z22,z17]),(0,[z21,z368,z1,z2,z5,z6]),(0,[z21,z7,z1,z2,z5,z753])],[(0,[z7,z1,z2,z1137,z5,z6]),(0,[z21,z101,z7,z2,z5,z6]),(0,[z1138,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z91,z22,z17])],[(0,[z54,z1,z270,z4,z5,z6]),(0,[z469,z7,z1,z4,z88,z6]),(0,[z7,z1,z1139,z4,z5,z6]),(0,[z1,z120,z4,z5,z50,z44]),(0,[z437,z1,z2,z30,z5,z6]),(0,[z1140,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z5,z6,z955]),(0,[z7,z1,z2,z5,z6,z451]),(0,[z7,z1,z221,z361,z5,z6]),(0,[z7,z2,z1141,z4,z5,z6]),(0,[z7,z1,z253,z5,z22,z6]),(0,[z7,z1,z30,z1142,z5,z6]),(0,[z308,z1,z2,z42,z5,z6])],[(0,[z7,z1,z454,z4,z5,z260]),(0,[z1,z2,z4,z134,z6,z44]),(0,[z1143,z1,z2,z4,z5,z6]),(0,[z67,z7,z2,z4,z863,z6]),(0,[z7,z1144,z2,z4,z5,z6]),(0,[z7,z1,z150,z141,z555,z6]),(0,[z7,z1,z2,z5,z140,z6]),(0,[z23,z7,z1,z2,z5,z234])],[(0,[z252,z1,z2,z4,z5,z6]),(0,[z116,z1,z2,z554,z5,z6]),(0,[z54,z1,z2,z1145,z5,z6]),(0,[z7,z1,z2,z1146,z5,z6]),(0,[z1147,z1,z2,z4,z5,z6]),(0,[z7,z2,z117,z5,z6,z674]),(0,[z1,z2,z4,z5,z129,z337]),(0,[z7,z1,z2,z1148,z5,z6]),(0,[z31,z1,z235,z4,z5,z6])],[(0,[z7,z774,z2,z4,z5,z6]),(0,[z52,z7,z152,z217,z5,z6]),(0,[z7,z1,z2,z5,z25,z678]),(0,[z1149,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z281,z22,z6])],[(0,[z1,z2,z66,z719,z5,z6]),(0,[z7,z1,z341,z4,z134,z6]),(0,[z1150,z1,z2,z4,z5,z6]),(1,[z7,z1,z57,z4,z17])],[(0,[z0,z148,z2,z4,z5,z6]),(0,[z7,z1,z2,z1151,z5,z6]),(0,[z38,z7,z352,z4,z5,z6]),(0,[z1,z334,z2,z30,z5,z6]),(0,[z7,z1,z167,z4,z5,z328]),(0,[z1,z2,z4,z5,z6,z1152])],[(0,[z99,z74,z2,z4,z5,z6]),(0,[z457,z1,z2,z4,z5,z44]),(0,[z1,z120,z4,z5,z50,z199]),(0,[z308,z1,z57,z4,z5,z6])],[(0,[z26,z27,z2,z4,z5,z6]),(0,[z28,z1,z2,z4,z5,z6]),(0,[z368,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z769]),(0,[z7,z1,z2,z1153,z5,z6]),(0,[z165,z7,z1,z2,z5,z237])],[(0,[z27,z2,z4,z5,z423,z6]),(0,[z112,z1,z3,z4,z5,z6]),(0,[z54,z1,z2,z162,z5,z6]),(0,[z101,z7,z2,z5,z22,z6]),(0,[z7,z783,z2,z30,z5,z6])],[(0,[z54,z1,z2,z30,z5,z212]),(0,[z7,z1,z2,z22,z212,z17]),(0,[z1,z2,z4,z804,z5,z6]),(0,[z1154,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z22,z6,z668]),(0,[z165,z7,z1,z2,z5,z106])],[(0,[z1155,z1,z2,z4,z5,z6]),(0,[z1,z2,z5,z1156,z22,z6]),(0,[z7,z1,z2,z4,z5,z40]),(0,[z7,z1,z2,z42,z5,z6]),(0,[z7,z241,z235,z4,z5,z6])],[(0,[z1,z2,z4,z59,z533,z6]),(0,[z1,z2,z5,z6,z43,z44]),(0,[z1157,z7,z1,z2,z5,z6]),(0,[z36,z1,z2,z4,z5,z567])],[(0,[z7,z1,z126,z19,z5,z6]),(0,[z7,z365,z2,z72,z5,z6]),(0,[z7,z1,z2,z1158,z5,z6]),(0,[z21,z7,z1,z2,z5,z234])]],
   [[(0,[z7,z1,z2,z342,z5,z6]),(0,[z0,z65,z166,z4,z5,z6]),(0,[z38,z7,z241,z2,z5,z6])],[(0,[z7,z1,z2,z1159,z5,z6]),(0,[z54,z2,z1160,z4,z5,z6]),(0,[z7,z154,z166,z30,z5,z6]),(0,[z1161,z1,z2,z4,z5,z6]),(0,[z7,z1162,z2,z4,z5,z6]),(0,[z7,z1,z2,z127,z22,z6])],[(0,[z645,z27,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z1163]),(0,[z7,z1164,z2,z4,z5,z6]),(0,[z252,z124,z2,z4,z5,z6])],[(0,[z298,z1,z3,z4,z5,z6]),(0,[z54,z1,z2,z198,z5,z6]),(0,[z54,z1,z2,z30,z98,z6]),(0,[z7,z1,z2,z1165,z5,z6]),(0,[z67,z7,z167,z4,z33,z6]),(0,[z7,z522,z2,z30,z5,z6])],[(0,[z518,z1,z334,z4,z5,z6]),(0,[z7,z24,z2,z5,z363,z6]),(0,[z7,z2,z4,z819,z5,z6]),(0,[z1166,z1,z2,z4,z5,z6]),(0,[z31,z1,z2,z4,z422,z6])],[(0,[z1167,z7,z1,z2,z5,z6]),(0,[z1,z2,z1168,z4,z5,z6]),(0,[z7,z1,z616,z19,z5,z6]),(0,[z7,z1,z2,z4,z88,z408])],[(0,[z7,z1,z2,z1169,z5,z6]),(0,[z7,z283,z454,z4,z5,z6]),(0,[z47,z1,z2,z4,z48,z260]),(0,[z7,z1,z2,z1170,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1171]),(0,[z7,z1172,z2,z4,z5,z6]),(0,[z99,z1,z2,z30,z59,z6]),(0,[z1,z2,z4,z5,z44,z228]),(0,[z54,z243,z2,z4,z5,z6]),(0,[z7,z1,z1173,z4,z5,z6]),(0,[z7,z1,z1125,z4,z5,z6])],[(0,[z1,z2,z30,z98,z6,z44]),(0,[z207,z31,z1,z2,z5,z6]),(0,[z54,z1,z2,z403,z5,z6]),(0,[z1174,z1,z2,z4,z5,z6]),(0,[z7,z1,z492,z5,z6,z16]),(0,[z7,z441,z2,z4,z5,z17])],[(0,[z67,z2,z4,z33,z6,z44]),(0,[z1,z2,z4,z5,z6,z1175]),(0,[z54,z1,z2,z4,z5,z408]),(0,[z315,z7,z2,z4,z33,z6]),(0,[z7,z1,z2,z1176,z5,z6]),(0,[z1,z2,z5,z22,z6,z224]),(0,[z1,z2,z4,z5,z1177,z6])],[(0,[z536,z2,z4,z5,z6,z604]),(0,[z119,z2,z4,z5,z33,z6]),(0,[z1178,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z782]),(0,[z7,z1,z2,z1179,z414,z6])],[(0,[z1,z346,z4,z5,z6,z44]),(0,[z1,z2,z988,z5,z6,z44]),(0,[z7,z1,z2,z1180,z5,z6]),(0,[z7,z1,z2,z5,z555,z6]),(0,[z1181,z7,z1,z2,z5,z6])],[(0,[z7,z1,z2,z1182,z5,z6]),(0,[z1,z2,z4,z5,z44,z17]),(0,[z7,z1,z2,z1183,z5,z6]),(0,[z7,z241,z2,z4,z422,z6])],[(0,[z7,z131,z166,z4,z5,z6]),(0,[z7,z74,z2,z4,z5,z254]),(0,[z54,z1,z2,z208,z5,z6]),(0,[z7,z1,z4,z5,z6,z1184]),(0,[z7,z1,z2,z4,z702,z129]),(0,[z101,z7,z2,z19,z5,z6]),(0,[z7,z1,z4,z5,z6,z1185]),(0,[z1186,z1,z2,z4,z5,z6])],[(0,[z101,z2,z4,z5,z6,z44]),(0,[z77,z1,z2,z4,z319,z6]),(0,[z7,z1,z2,z1187,z5,z6]),(0,[z63,z34,z7,z2,z5,z58]),(0,[z101,z7,z2,z196,z5,z6]),(0,[z7,z1,z2,z4,z5,z1188])],[(0,[z7,z1,z2,z775,z5,z6]),(0,[z7,z1,z2,z5,z6,z1189]),(0,[z7,z1,z1190,z5,z22,z6])]],
   [[(0,[z7,z1,z2,z4,z1191,z6]),(0,[z7,z1,z2,z82,z5,z254]),(0,[z1,z2,z217,z5,z6,z44]),(0,[z246,z52,z2,z4,z5,z6]),(0,[z28,z1,z420,z4,z5,z6]),(0,[z7,z8,z2,z4,z606,z6]),(0,[z7,z1,z2,z83,z5,z6])],[(0,[z7,z298,z1,z5,z22,z6]),(0,[z1,z2,z5,z129,z43,z44]),(0,[z1,z2,z5,z1192,z22,z6]),(0,[z1193,z7,z1,z2,z5,z6])],[(0,[z7,z1,z2,z1194,z5,z6]),(0,[z74,z2,z4,z5,z6,z44]),(0,[z54,z1,z2,z1195,z5,z6]),(0,[z49,z7,z1,z372,z5,z6]),(0,[z145,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z895,z5,z6])],[(0,[z7,z1196,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1197]),(0,[z54,z1,z2,z217,z5,z6]),(0,[z7,z1,z420,z4,z5,z40]),(0,[z920,z1,z2,z4,z5,z40]),(0,[z947,z1,z2,z5,z6,z337]),(0,[z1,z2,z4,z5,z6,z1198])],[(0,[z7,z1,z2,z1199,z5,z6]),(0,[z7,z1,z1200,z4,z5,z6]),(0,[z7,z2,z1201,z4,z5,z6]),(0,[z7,z1,z346,z510,z5,z6])],[(0,[z366,z9,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1202]),(0,[z7,z144,z2,z208,z5,z6]),(0,[z7,z1,z951,z196,z5,z6]),(0,[z7,z1,z57,z4,z5,z129])],[(0,[z7,z1,z2,z1203,z5,z6]),(0,[z1204,z1,z2,z4,z5,z6]),(0,[z273,z7,z2,z4,z5,z58]),(0,[z7,z1,z2,z450,z6,z17])],[(0,[z7,z1,z2,z1205,z5,z6]),(0,[z1206,z7,z1,z2,z5,z6]),(0,[z7,z1,z2,z5,z835,z6]),(0,[z97,z368,z1,z2,z22,z6])],[(0,[z47,z1,z2,z4,z319,z6]),(0,[z1,z1207,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z33,z328]),(0,[z35,z7,z1,z310,z88,z6])],[(0,[z7,z1,z2,z4,z5,z1208]),(0,[z99,z1,z2,z4,z358,z6]),(0,[z101,z7,z2,z4,z5,z6]),(0,[z7,z548,z2,z30,z5,z6]),(0,[z93,z7,z1,z2,z42,z17])],[(0,[z112,z74,z2,z4,z5,z6]),(0,[z2,z436,z4,z5,z6,z44]),(0,[z99,z1,z2,z4,z5,z260]),(0,[z7,z24,z1,z2,z422,z6]),(0,[z49,z7,z1,z60,z5,z6])],[(0,[z1,z2,z510,z5,z6,z44]),(0,[z246,z2,z166,z4,z5,z6]),(0,[z7,z144,z2,z217,z5,z6]),(0,[z7,z24,z352,z72,z5,z6]),(0,[z1209,z1,z2,z5,z22,z6]),(0,[z308,z1,z2,z30,z5,z6])],[(0,[z1,z2,z4,z5,z6,z1210])],[(0,[z1,z2,z3,z162,z5,z6]),(0,[z7,z1,z2,z1211,z5,z6]),(0,[z516,z1,z2,z542,z5,z6]),(0,[z21,z7,z1,z2,z5,z524]),(0,[z1,z2,z4,z870,z5,z6]),(0,[z1,z2,z4,z5,z408,z1067]),(0,[z178,z169,z2,z4,z5,z6])],[(0,[z7,z522,z150,z4,z5,z6]),(0,[z7,z1,z2,z91,z555,z6]),(0,[z7,z124,z253,z4,z5,z6])],[(0,[z176,z1,z61,z4,z5,z6]),(0,[z116,z1,z2,z5,z6,z43]),(0,[z7,z1,z2,z843,z5,z6]),(0,[z548,z2,z4,z5,z6,z44]),(0,[z1,z2,z4,z5,z328,z1212]),(0,[z1,z2,z4,z5,z1213,z6]),(0,[z63,z7,z2,z208,z5,z58]),(0,[z1214,z1,z2,z4,z5,z6]),(0,[z986,z1,z2,z30,z5,z6])]],
   [[(0,[z7,z1215,z2,z4,z5,z6]),(1,[z1,z2,z719,z5,z6]),(0,[z75,z2,z166,z4,z5,z6])],[(0,[z7,z1,z1216,z4,z5,z6]),(0,[z38,z2,z117,z5,z6,z44]),(0,[z1,z2,z251,z5,z6,z44]),(0,[z1035,z1,z2,z5,z6,z44]),(0,[z1217,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1124,z6]),(0,[z7,z1,z2,z4,z414,z16]),(0,[z1,z2,z30,z5,z6,z224])],[(0,[z1218,z1,z2,z4,z5,z6]),(0,[z7,z1219,z2,z4,z5,z6])],[(0,[z7,z1,z1220,z4,z5,z6]),(0,[z176,z1,z454,z4,z5,z6]),(0,[z7,z1,z1221,z4,z5,z6]),(0,[z7,z807,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1222]),(0,[z29,z7,z1,z83,z5,z16]),(0,[z252,z1,z253,z4,z5,z6]),(0,[z1,z2,z1223,z4,z5,z6])],[(0,[z207,z1,z2,z5,z6,z179]),(0,[z101,z2,z96,z4,z5,z6])],[(0,[z7,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z1224,z5,z6]),(0,[z65,z1,z2,z162,z5,z6]),(0,[z7,z1,z4,z5,z6,z776]),(0,[z99,z1,z2,z59,z22,z6]),(0,[z1225,z1,z2,z4,z5,z6]),(0,[z1226,z1,z2,z4,z5,z6]),(0,[z1227,z1,z2,z5,z22,z6])],[(0,[z1228,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1229]),(0,[z7,z1,z2,z4,z1230,z6])],[(0,[z7,z1,z270,z92,z5,z6]),(0,[z7,z1,z341,z208,z5,z6]),(1,[z7,z1,z951,z5,z6]),(0,[z7,z1,z2,z22,z16,z17]),(0,[z1,z2,z91,z233,z22,z6]),(0,[z7,z441,z2,z4,z6,z17]),(0,[z7,z1,z346,z42,z5,z6])],[(0,[z1,z2,z4,z5,z328,z44]),(0,[z1,z2,z449,z5,z6,z44]),(0,[z7,z1,z2,z22,z6,z647]),(0,[z7,z1,z2,z4,z141,z408]),(0,[z7,z1,z57,z5,z22,z6]),(0,[z1231,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z5,z1232,z6])],[(0,[z7,z1,z2,z1233,z5,z6]),(0,[z7,z1,z2,z30,z5,z260]),(0,[z1,z2,z4,z5,z637,z44]),(0,[z276,z1,z2,z72,z5,z6])],[(0,[z7,z1,z2,z1234,z5,z6]),(0,[z1235,z7,z2,z4,z5,z6]),(0,[z1,z2,z5,z22,z6,z275])],[(0,[z551,z9,z2,z4,z5,z6]),(0,[z119,z1,z2,z217,z5,z6]),(0,[z7,z1,z2,z1236,z5,z6]),(0,[z7,z1,z2,z5,z763,z6])],[(0,[z7,z2,z1237,z4,z5,z6]),(0,[z54,z1,z2,z4,z91,z129]),(0,[z7,z1,z2,z5,z1238,z6]),(0,[z34,z52,z7,z2,z5,z6]),(0,[z416,z1,z2,z30,z5,z6]),(0,[z7,z1,z1190,z4,z5,z6]),(0,[z491,z7,z2,z4,z5,z58]),(0,[z7,z1,z2,z5,z735,z6]),(0,[z7,z1,z235,z4,z187,z6])],[(0,[z68,z1,z2,z5,z22,z6]),(0,[z1,z2,z1239,z5,z69,z6]),(0,[z544,z7,z1,z4,z5,z16])],[(0,[z7,z298,z1,z4,z5,z6]),(0,[z7,z1,z226,z175,z5,z6]),(0,[z7,z518,z1,z5,z25,z6]),(0,[z7,z24,z2,z5,z6,z326]),(0,[z1240,z1,z2,z4,z5,z6])]],
   [[(0,[z7,z1,z2,z1241,z5,z6]),(0,[z145,z1,z2,z4,z5,z6]),(0,[z21,z1,z2,z5,z44,z106]),(0,[z7,z1,z150,z4,z596,z6]),(0,[z7,z1,z2,z422,z6,z106]),(0,[z308,z169,z2,z4,z5,z6])],[(0,[z7,z1,z2,z488,z5,z40]),(0,[z41,z7,z1,z2,z4,z17]),(0,[z7,z1,z2,z22,z6,z51]),(0,[z7,z1,z1242,z4,z5,z6])],[(0,[z7,z1,z2,z5,z1243,z6]),(0,[z383,z7,z1,z2,z22,z6]),(0,[z1,z103,z96,z19,z5,z6]),(0,[z7,z1017,z2,z30,z5,z6])],[(0,[z1,z2,z1244,z4,z5,z6]),(0,[z1245,z1,z2,z4,z5,z6]),(0,[z1,z1246,z2,z4,z5,z6])],[(0,[z7,z1,z2,z5,z1247,z6]),(0,[z1,z779,z3,z4,z5,z6]),(0,[z1,z2,z5,z6,z44,z1248]),(0,[z7,z1,z2,z312,z22,z6]),(0,[z7,z1,z2,z156,z5,z6]),(0,[z7,z1,z352,z30,z5,z6]),(0,[z7,z518,z24,z72,z5,z6]),(0,[z28,z1,z2,z542,z5,z6]),(0,[z437,z1,z2,z4,z134,z6]),(0,[z7,z1,z2,z1249,z5,z6])],[(0,[z116,z1,z2,z5,z418,z6]),(0,[z99,z1,z2,z160,z59,z6]),(0,[z7,z1,z2,z4,z1250,z6]),(0,[z7,z1,z120,z4,z5,z787])],[(0,[z1251,z1,z2,z4,z5,z6]),(0,[z95,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z1252,z5,z6]),(0,[z7,z243,z2,z4,z460,z6])],[(0,[z7,z1,z2,z542,z5,z40]),(0,[z7,z1,z2,z1253,z5,z6]),(0,[z355,z1,z2,z4,z91,z129])],[(0,[z52,z7,z689,z4,z5,z6]),(0,[z116,z7,z241,z2,z5,z6]),(0,[z1,z420,z4,z5,z6,z44]),(0,[z181,z1,z2,z30,z5,z6]),(0,[z7,z1,z4,z88,z16,z17]),(0,[z29,z7,z1,z30,z5,z16]),(0,[z7,z1,z2,z30,z651,z6])],[(0,[z65,z61,z436,z4,z5,z6]),(0,[z1,z2,z4,z399,z44,z17]),(0,[z1254,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z1255,z6]),(0,[z1209,z1,z2,z4,z5,z6]),(0,[z7,z441,z2,z510,z5,z6])],[(0,[z7,z1,z2,z4,z1256,z6]),(0,[z7,z1,z2,z1257,z5,z6]),(0,[z1,z2,z4,z5,z652,z44]),(0,[z7,z1,z2,z1258,z5,z6]),(0,[z7,z1,z2,z5,z6,z1259]),(0,[z1,z2,z4,z5,z6,z1260])],[(0,[z112,z1,z2,z4,z5,z260]),(0,[z7,z1261,z2,z4,z5,z6]),(0,[z138,z1,z2,z5,z22,z44]),(0,[z1,z2,z4,z5,z6,z1212]),(0,[z7,z1,z420,z30,z5,z6]),(0,[z7,z1,z221,z5,z22,z6]),(0,[z7,z1,z2,z4,z5,z787]),(0,[z7,z1,z1262,z4,z5,z6])],[(0,[z7,z283,z2,z30,z5,z6]),(0,[z1,z2,z4,z59,z6,z399]),(0,[z446,z207,z1,z2,z5,z6]),(0,[z54,z1263,z2,z4,z5,z6]),(0,[z1264,z1,z2,z4,z5,z6]),(0,[z1,z2,z96,z5,z22,z6]),(0,[z7,z243,z2,z4,z414,z6])],[(0,[z1,z9,z2,z92,z5,z6]),(0,[z1,z221,z4,z5,z6,z44]),(0,[z1,z2,z22,z6,z44,z17]),(0,[z63,z95,z2,z4,z5,z58]),(0,[z21,z7,z241,z2,z5,z106])],[(0,[z26,z213,z2,z4,z5,z6]),(0,[z7,z1,z2,z175,z5,z254]),(0,[z698,z7,z1,z2,z5,z106]),(0,[z368,z1,z2,z5,z25,z6])],[(0,[z7,z1265,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z805,z6]),(0,[z1266,z1,z2,z4,z5,z6])]],
   [[(0,[z602,z1,z3,z4,z5,z6]),(0,[z213,z65,z61,z4,z5,z6]),(0,[z7,z1,z2,z4,z1267,z6]),(0,[z516,z1,z2,z4,z5,z40]),(0,[z67,z246,z2,z4,z33,z6]),(0,[z7,z1,z2,z460,z1268,z6])],[(0,[z1,z61,z4,z5,z6,z322]),(0,[z7,z74,z226,z4,z5,z6]),(0,[z101,z54,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1269]),(0,[z7,z2,z4,z5,z33,z328]),(0,[z7,z1,z2,z1270,z5,z6])],[(0,[z7,z1,z624,z19,z5,z6]),(0,[z1271,z1,z2,z4,z5,z6])],[(0,[z102,z1,z2,z66,z5,z6]),(0,[z1,z2,z443,z5,z6,z44]),(0,[z1227,z1,z2,z4,z5,z6]),(0,[z34,z7,z24,z2,z5,z6]),(0,[z1,z1272,z2,z4,z5,z6]),(0,[z1,z2,z30,z5,z6,z275])],[(0,[z1,z2,z4,z5,z6,z44]),(0,[z47,z1,z2,z4,z48,z6]),(0,[z7,z1,z226,z82,z5,z6]),(0,[z7,z1,z2,z361,z134,z6]),(1,[z7,z441,z2,z4,z17])],[(0,[z305,z1,z3,z4,z5,z6]),(0,[z7,z1,z2,z1273,z5,z6])],[(0,[z7,z1,z2,z1274,z5,z6]),(0,[z47,z1,z2,z162,z5,z6]),(0,[z7,z1,z2,z4,z5,z1275]),(0,[z63,z2,z4,z5,z44,z58]),(0,[z564,z7,z1,z4,z88,z6]),(0,[z7,z1,z57,z4,z5,z6])],[(0,[z7,z2,z436,z30,z5,z6]),(0,[z54,z1,z235,z4,z5,z6]),(0,[z21,z276,z1,z2,z5,z6])],[(0,[z1,z2,z488,z5,z6,z44]),(0,[z1276,z1,z2,z4,z5,z6]),(0,[z416,z1,z150,z4,z5,z6]),(0,[z7,z1,z2,z5,z1277,z6]),(0,[z315,z7,z1,z2,z4,z17]),(0,[z7,z522,z2,z251,z5,z6])],[(0,[z116,z1,z2,z530,z5,z6]),(0,[z1107,z54,z2,z4,z5,z6]),(0,[z7,z1,z2,z1278,z5,z6]),(0,[z1279,z1,z2,z4,z5,z6])],[(0,[z1280,z7,z2,z4,z5,z6]),(0,[z276,z1,z352,z4,z5,z6]),(0,[z7,z1,z2,z4,z64,z6])],[(0,[z7,z1281,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z199]),(0,[z7,z1,z4,z954,z5,z6]),(0,[z1282,z1,z2,z4,z5,z6])],[(0,[z68,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z69,z6]),(0,[z1283,z1,z2,z4,z5,z129]),(0,[z7,z441,z2,z42,z5,z6])],[(0,[z29,z1,z4,z5,z44,z16]),(0,[z1284,z1,z2,z4,z5,z6]),(0,[z38,z7,z2,z267,z5,z6])],[(0,[z7,z1,z2,z5,z6,z1285]),(0,[z7,z1,z2,z5,z22,z254]),(0,[z7,z1,z2,z5,z1286,z6]),(0,[z276,z1,z2,z117,z5,z6]),(0,[z28,z8,z2,z4,z5,z6]),(0,[z1287,z1,z2,z4,z5,z6]),(0,[z353,z7,z1,z5,z354,z6])],[(0,[z324,z1,z2,z4,z5,z44]),(0,[z7,z24,z2,z72,z5,z6]),(0,[z7,z1,z346,z30,z5,z6])]],
   [[(0,[z52,z7,z752,z4,z5,z6]),(0,[z7,z1,z2,z22,z6,z17]),(0,[z1,z2,z5,z22,z6,z761]),(0,[z21,z252,z1,z2,z5,z106])],[(0,[z7,z1,z2,z1288,z5,z6]),(0,[z1,z2,z4,z5,z673,z44]),(0,[z522,z2,z4,z5,z6,z44]),(0,[z2,z4,z5,z6,z44,z1289]),(0,[z1,z2,z4,z5,z212,z769]),(0,[z7,z1,z2,z5,z1290,z6]),(0,[z1291,z1,z2,z4,z5,z6])],[(0,[z484,z1,z118,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z782]),(0,[z7,z441,z57,z4,z5,z6])],[(0,[z7,z1,z2,z5,z1292,z6]),(0,[z65,z1,z61,z30,z5,z6]),(0,[z207,z65,z1,z2,z5,z6]),(0,[z54,z413,z2,z4,z5,z6]),(0,[z7,z152,z1,z198,z5,z6]),(0,[z7,z1,z2,z5,z1293,z6]),(0,[z49,z7,z1,z951,z5,z6])],[(0,[z95,z1,z2,z4,z5,z6]),(0,[z1294,z7,z2,z4,z5,z6]),(0,[z1,z2,z4,z64,z6,z44]),(0,[z54,z2,z417,z4,z5,z6]),(0,[z7,z1,z19,z372,z5,z6]),(0,[z7,z1,z2,z1295,z5,z6]),(0,[z1296,z7,z1,z2,z5,z6]),(0,[z7,z1,z351,z121,z5,z6])],[(0,[z54,z1,z2,z1297,z5,z6])],[(0,[z7,z1,z2,z1298,z5,z6]),(0,[z54,z1,z2,z4,z5,z328]),(0,[z54,z1,z2,z4,z422,z6])],[(0,[z7,z1,z2,z1299,z5,z6]),(0,[z7,z1,z1300,z4,z5,z6]),(0,[z7,z1,z167,z5,z22,z6]),(0,[z7,z1,z2,z310,z5,z408])],[(0,[z1301,z2,z4,z5,z6,z44]),(0,[z1302,z7,z2,z4,z5,z6])],[(0,[z1,z2,z682,z4,z5,z44]),(0,[z7,z1,z2,z4,z5,z1303]),(0,[z7,z1,z2,z5,z6,z1248]),(0,[z138,z1,z2,z4,z5,z44]),(0,[z1,z2,z832,z5,z6,z44]),(0,[z7,z1,z221,z4,z5,z6]),(0,[z262,z7,z152,z1,z5,z6]),(0,[z176,z1,z2,z30,z5,z6]),(0,[z7,z1090,z1,z30,z5,z6])],[(0,[z26,z27,z2,z342,z5,z6]),(0,[z1,z2,z96,z4,z5,z6]),(0,[z1,z1304,z2,z4,z5,z6]),(0,[z38,z7,z1,z235,z5,z6]),(0,[z7,z1,z2,z4,z91,z329]),(0,[z7,z1,z150,z30,z141,z6]),(0,[z495,z1,z2,z83,z5,z6]),(0,[z7,z1,z2,z1305,z5,z6])],[(0,[z74,z61,z2,z4,z5,z6]),(0,[z47,z283,z2,z4,z48,z6]),(0,[z7,z1,z2,z5,z6,z1306]),(0,[z446,z1,z2,z4,z44,z17])],[(0,[z1,z2,z4,z5,z1009,z6])],[(0,[z7,z1,z1307,z4,z5,z6]),(0,[z1,z2,z4,z5,z813,z6]),(0,[z7,z1,z2,z4,z1308,z6]),(0,[z21,z7,z1,z2,z5,z106])],[(0,[z7,z1,z2,z4,z1309,z6]),(0,[z52,z7,z152,z372,z5,z6]),(0,[z7,z1,z2,z1027,z5,z6]),(0,[z7,z1,z4,z1124,z88,z6])],[(0,[z54,z766,z2,z4,z5,z6]),(0,[z279,z7,z2,z4,z33,z6]),(0,[z49,z7,z1,z196,z5,z6]),(0,[z7,z1,z2,z1179,z5,z6]),(0,[z7,z169,z2,z5,z22,z6]),(0,[z1310,z1,z2,z5,z22,z6]),(0,[z7,z1,z57,z4,z5,z17])]],
   [[(0,[z99,z1,z2,z59,z418,z6]),(0,[z276,z1,z2,z5,z22,z6]),(0,[z289,z7,z1,z4,z5,z16]),(0,[z1,z2,z5,z233,z22,z6]),(0,[z277,z1,z2,z5,z22,z6])],[(0,[z7,z1,z2,z1311,z5,z6]),(0,[z1,z2,z30,z233,z22,z6])],[(0,[z7,z1,z226,z4,z5,z260]),(0,[z7,z1,z2,z22,z58,z17]),(0,[z7,z1,z1104,z30,z5,z6])],[(0,[z7,z1,z569,z196,z5,z6]),(0,[z1235,z2,z4,z5,z6,z44]),(0,[z54,z1,z341,z4,z5,z6]),(1,[z7,z2,z707,z5,z6]),(0,[z31,z1,z2,z5,z22,z6])],[(0,[z1312,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1313,z5,z6]),(0,[z437,z1,z2,z208,z5,z6])],[(0,[z1314,z7,z1,z2,z5,z6]),(0,[z99,z1,z2,z4,z771,z6]),(0,[z778,z1,z2,z4,z5,z408]),(0,[z7,z1,z2,z510,z6,z17])],[(0,[z35,z1,z4,z88,z6,z44]),(0,[z7,z1,z167,z488,z5,z6]),(0,[z7,z1,z2,z1315,z5,z6]),(0,[z7,z1,z4,z141,z1124,z6])],[(0,[z7,z1316,z1,z4,z5,z6]),(0,[z116,z1,z454,z4,z5,z6]),(0,[z1,z2,z4,z5,z696,z44]),(0,[z663,z7,z1,z4,z5,z16]),(0,[z433,z7,z1,z2,z22,z6])],[(0,[z54,z1,z2,z4,z5,z686]),(0,[z54,z1,z1317,z4,z5,z6]),(0,[z516,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z5,z1318]),(0,[z100,z1,z2,z5,z22,z6])],[(0,[z1319,z1,z2,z4,z5,z6]),(0,[z1320,z1,z2,z4,z5,z6]),(0,[z7,z1,z338,z5,z18,z6])],[(0,[z7,z1321,z2,z4,z5,z6]),(0,[z1,z2,z1205,z5,z6,z44]),(0,[z7,z1,z166,z198,z5,z6]),(0,[z7,z1,z2,z251,z5,z6]),(0,[z36,z1,z2,z30,z5,z6]),(0,[z35,z7,z548,z4,z88,z6]),(0,[z93,z7,z169,z2,z4,z17])],[(0,[z0,z7,z270,z4,z5,z6]),(0,[z1,z2,z4,z422,z6,z44]),(0,[z7,z1,z2,z5,z6,z1119]),(0,[z698,z7,z2,z4,z5,z58]),(0,[z262,z7,z1,z196,z5,z6]),(0,[z7,z1,z103,z951,z5,z6]),(0,[z7,z241,z2,z5,z22,z6])],[(0,[z116,z1,z2,z335,z5,z6]),(0,[z7,z1,z2,z4,z5,z254]),(0,[z1167,z1,z2,z5,z6,z44]),(1,[z7,z1,z2,z5,z753])],[(0,[z107,z31,z1,z2,z5,z6]),(0,[z54,z1,z2,z361,z5,z6]),(0,[z7,z242,z166,z4,z5,z6]),(0,[z7,z1,z2,z1322,z5,z6])],[(0,[z112,z645,z1,z4,z5,z6]),(0,[z1323,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1324,z5,z6]),(0,[z7,z1325,z2,z4,z5,z6])],[(0,[z54,z1,z1326,z4,z5,z6]),(0,[z495,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z4,z711,z17])]],
   [[(0,[z247,z7,z2,z117,z5,z6]),(0,[z7,z518,z1,z30,z5,z6]),(1,[z7,z1,z2,z4,z711])],[(0,[z1,z2,z4,z5,z6,z1327]),(0,[z7,z261,z2,z72,z5,z6])],[(0,[z7,z1,z2,z1328,z5,z6]),(0,[z276,z1,z2,z19,z5,z6])],[(0,[z7,z2,z1329,z4,z5,z6]),(0,[z7,z2,z4,z707,z5,z6]),(0,[z276,z1,z2,z196,z5,z6]),(0,[z1,z2,z5,z6,z1330,z337]),(0,[z7,z243,z2,z5,z22,z6]),(0,[z1,z2,z233,z22,z6,z17]),(0,[z7,z1,z2,z449,z98,z6])],[(0,[z213,z7,z2,z443,z5,z6]),(0,[z54,z74,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z12,z6]),(0,[z7,z441,z2,z30,z5,z6])],[(0,[z7,z1,z1331,z4,z5,z6]),(0,[z7,z1,z167,z4,z5,z6]),(0,[z63,z7,z341,z4,z5,z58]),(0,[z368,z1,z2,z5,z354,z6]),(0,[z7,z124,z2,z30,z5,z6])],[(0,[z1,z2,z198,z5,z6,z44]),(0,[z1283,z1,z2,z4,z5,z44]),(0,[z1332,z1,z2,z5,z22,z6]),(0,[z7,z1,z103,z19,z5,z6]),(0,[z7,z2,z30,z790,z5,z6])],[(0,[z54,z1,z2,z82,z5,z6]),(0,[z1333,z1,z2,z4,z5,z6]),(0,[z1334,z1,z2,z5,z22,z6])],[(0,[z7,z1,z2,z5,z6,z1335]),(0,[z54,z1,z2,z4,z460,z6]),(0,[z7,z1,z2,z30,z172,z6])],[(0,[z7,z1,z1336,z4,z5,z6]),(0,[z7,z1,z1337,z4,z5,z6]),(0,[z1338,z1,z2,z4,z5,z6]),(0,[z7,z1,z1339,z4,z5,z6])],[(0,[z7,z1,z1340,z4,z5,z6]),(0,[z27,z74,z2,z4,z5,z6]),(0,[z213,z7,z2,z5,z22,z6]),(0,[z1341,z1,z2,z4,z5,z6]),(0,[z1342,z1,z2,z4,z5,z6]),(0,[z252,z1,z2,z30,z5,z6]),(0,[z1,z2,z5,z1177,z140,z6])],[(0,[z107,z1,z2,z565,z5,z6]),(0,[z1,z2,z4,z5,z6,z1343]),(0,[z54,z1,z2,z372,z5,z6]),(0,[z1344,z7,z1,z2,z5,z6])],[(0,[z7,z1,z270,z4,z5,z6]),(0,[z1,z2,z4,z5,z771,z6]),(0,[z7,z1,z2,z912,z5,z6]),(0,[z1,z2,z30,z5,z233,z6]),(0,[z1,z2,z1345,z5,z22,z6])],[(0,[z1283,z1,z2,z4,z5,z6]),(0,[z1346,z1,z2,z4,z5,z6]),(0,[z7,z169,z2,z4,z5,z6]),(0,[z181,z1,z2,z251,z5,z6]),(0,[z1310,z1,z2,z4,z5,z6])],[(0,[z276,z1,z2,z4,z5,z6]),(0,[z54,z1,z2,z92,z5,z6]),(0,[z277,z1,z2,z4,z5,z6]),(0,[z1206,z1,z2,z5,z6,z44]),(0,[z54,z1,z2,z4,z414,z6]),(0,[z1,z2,z4,z5,z6,z1347]),(0,[z7,z1348,z2,z4,z5,z6]),(0,[z7,z1,z57,z4,z6,z17])],[(0,[z7,z1349,z2,z4,z5,z6]),(0,[z54,z1,z2,z837,z5,z6]),(0,[z7,z1,z2,z1145,z5,z6]),(0,[z1350,z1,z2,z4,z5,z6]),(0,[z63,z7,z2,z361,z5,z58]),(0,[z1351,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1239,z5,z6]),(0,[z368,z1,z2,z30,z5,z6]),(0,[z1352,z1,z2,z4,z5,z6])]],
   [[(0,[z112,z1,z3,z30,z5,z6]),(0,[z7,z1,z2,z1353,z5,z6]),(0,[z1354,z1,z2,z4,z5,z6]),(0,[z7,z1355,z2,z4,z5,z6])],[(0,[z31,z1,z2,z4,z5,z6]),(0,[z446,z7,z1,z2,z4,z17]),(0,[z1356,z7,z1,z2,z5,z6]),(0,[z1,z2,z5,z163,z22,z6]),(0,[z7,z1,z2,z22,z6,z209]),(0,[z7,z1,z2,z30,z5,z567]),(0,[z7,z1,z2,z414,z22,z6])],[(0,[z54,z1,z2,z4,z5,z265]),(0,[z7,z1,z226,z5,z22,z6]),(0,[z1357,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z1358,z6]),(0,[z1359,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1360,z5,z6]),(0,[z74,z2,z66,z4,z5,z6]),(0,[z7,z283,z2,z4,z5,z254]),(0,[z207,z1,z2,z5,z6,z322]),(0,[z1361,z1,z2,z4,z5,z6])],[(0,[z7,z128,z2,z72,z5,z6])],[(0,[z7,z1,z2,z1362,z5,z6]),(0,[z7,z1,z2,z162,z5,z6]),(0,[z7,z1363,z2,z4,z5,z6]),(0,[z54,z1,z2,z842,z5,z6]),(0,[z7,z1,z2,z1364,z5,z6]),(0,[z7,z1,z1365,z4,z5,z6])],[(0,[z100,z1,z2,z4,z5,z6]),(0,[z7,z1,z1366,z4,z5,z6]),(0,[z7,z1,z2,z4,z134,z58]),(0,[z7,z417,z19,z4,z5,z6])],[(0,[z1,z2,z4,z5,z163,z6]),(0,[z283,z2,z4,z5,z6,z44]),(0,[z1367,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1368,z6]),(0,[z7,z1,z341,z361,z5,z6]),(0,[z840,z7,z2,z4,z5,z6]),(0,[z1369,z1,z2,z4,z5,z6])],[(0,[z7,z413,z2,z4,z414,z6])],[(0,[z26,z774,z2,z4,z5,z6]),(0,[z112,z1,z779,z4,z5,z6]),(0,[z469,z1,z2,z4,z48,z6]),(0,[z7,z1,z2,z5,z915,z6]),(0,[z1,z2,z4,z5,z44,z421]),(0,[z7,z1,z2,z1370,z5,z6]),(0,[z7,z241,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z40,z1110])],[(0,[z1371,z1,z2,z4,z5,z6]),(0,[z1,z2,z5,z6,z451,z772]),(0,[z7,z1372,z2,z4,z5,z6]),(0,[z1373,z1,z2,z5,z22,z6]),(0,[z277,z1,z2,z139,z5,z25])],[(0,[z138,z1,z2,z5,z43,z44]),(0,[z54,z857,z1,z4,z5,z6])],[(0,[z1294,z2,z4,z5,z6,z44]),(0,[z1374,z1,z2,z4,z5,z6]),(0,[z100,z1,z2,z492,z5,z6])],[(0,[z7,z1,z2,z4,z1375,z6]),(0,[z213,z2,z4,z5,z6,z44]),(0,[z1,z2,z208,z5,z6,z44]),(0,[z1376,z1,z2,z4,z5,z6]),(0,[z1377,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z22,z50,z17])],[(0,[z7,z1,z2,z673,z22,z6]),(0,[z54,z1,z2,z269,z5,z6]),(0,[z75,z1,z2,z403,z5,z6]),(0,[z7,z1,z372,z5,z6,z16]),(0,[z7,z1,z2,z5,z1378,z6]),(0,[z7,z1,z2,z4,z1379,z6]),(0,[z7,z241,z103,z2,z5,z6])],[(0,[z7,z298,z1,z342,z5,z6]),(0,[z7,z317,z2,z117,z5,z6]),(0,[z1380,z1,z2,z4,z5,z6]),(0,[z1381,z7,z1,z5,z22,z6]),(0,[z7,z1382,z2,z4,z5,z6])]],
   [[(0,[z518,z1,z4,z5,z6,z44]),(0,[z1,z2,z4,z5,z6,z1383]),(0,[z54,z1,z871,z4,z5,z6]),(0,[z1384,z1,z2,z4,z5,z6]),(0,[z1385,z1,z2,z4,z5,z6]),(0,[z7,z1,z4,z414,z6,z16]),(0,[z7,z1,z57,z510,z5,z6])],[(0,[z7,z1,z2,z1386,z5,z6]),(0,[z54,z1,z2,z4,z5,z323]),(0,[z7,z1,z1387,z4,z5,z6]),(0,[z1,z2,z4,z98,z44,z17]),(0,[z7,z243,z2,z4,z5,z6]),(0,[z7,z1,z2,z1388,z5,z6])],[(0,[z1,z61,z2,z4,z5,z260]),(0,[z116,z7,z1,z235,z5,z6]),(0,[z54,z1,z120,z4,z5,z50]),(0,[z7,z120,z417,z4,z5,z6]),(0,[z7,z1389,z2,z4,z5,z6])],[(0,[z47,z1,z454,z4,z48,z6]),(0,[z7,z2,z4,z863,z33,z6]),(0,[z1266,z1,z2,z5,z140,z6])],[(0,[z1332,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1390,z6]),(0,[z1,z2,z4,z5,z6,z1391]),(0,[z7,z1,z2,z5,z1392,z6])],[(0,[z7,z1,z2,z4,z1393,z6]),(0,[z1334,z1,z2,z4,z5,z6]),(0,[z7,z1,z19,z951,z5,z6]),(0,[z7,z1,z2,z5,z6,z1394]),(0,[z7,z1,z2,z22,z6,z240])],[(0,[z7,z1,z2,z160,z5,z6]),(0,[z7,z1,z2,z1395,z5,z6]),(0,[z1,z2,z4,z5,z6,z1044]),(0,[z7,z1,z253,z30,z5,z6])],[(0,[z1,z2,z4,z5,z408,z44]),(0,[z54,z1,z2,z310,z5,z6]),(0,[z35,z7,z1,z4,z88,z6]),(0,[z7,z243,z2,z492,z5,z6]),(0,[z7,z1,z235,z4,z422,z6]),(0,[z21,z7,z1,z235,z5,z106])],[(0,[z213,z7,z2,z4,z5,z6]),(0,[z26,z512,z2,z4,z5,z6]),(0,[z1396,z1,z2,z4,z5,z6]),(0,[z52,z7,z152,z5,z22,z6]),(0,[z1397,z1,z2,z4,z5,z6]),(0,[z101,z164,z2,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z598]),(0,[z107,z207,z1,z2,z5,z6]),(0,[z1398,z1,z2,z4,z5,z6]),(0,[z52,z75,z152,z4,z5,z6]),(0,[z7,z1,z351,z19,z5,z6]),(0,[z1399,z1,z2,z4,z5,z6]),(0,[z93,z7,z1,z57,z4,z17])],[(0,[z54,z1,z2,z4,z5,z672]),(0,[z0,z9,z2,z30,z5,z6]),(0,[z207,z1,z2,z105,z5,z6]),(0,[z28,z1,z2,z4,z5,z40]),(0,[z1,z2,z1345,z4,z5,z6])],[(0,[z1,z2,z5,z233,z418,z6]),(0,[z7,z1,z2,z4,z1400,z6])],[(0,[z7,z1,z2,z1401,z5,z6]),(0,[z1,z2,z66,z82,z5,z6]),(0,[z47,z207,z1,z2,z5,z6]),(0,[z1,z2,z5,z6,z43,z224]),(0,[z49,z7,z166,z72,z5,z6]),(0,[z889,z1,z2,z4,z5,z6]),(0,[z7,z1,z1087,z30,z5,z6]),(0,[z7,z890,z2,z4,z5,z6]),(0,[z7,z1,z1402,z4,z5,z6])],[(0,[z7,z1403,z2,z4,z5,z6]),(0,[z1,z2,z5,z6,z44,z1404]),(0,[z1405,z1,z4,z5,z6,z44])],[(0,[z639,z1,z2,z4,z48,z6]),(0,[z116,z1,z2,z626,z5,z6]),(0,[z7,z1,z2,z5,z6,z1406]),(0,[z101,z7,z2,z30,z5,z6]),(0,[z1407,z1,z2,z4,z5,z6]),(0,[z7,z1408,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z637])],[(0,[z7,z1409,z2,z4,z5,z6]),(0,[z7,z1,z2,z719,z5,z6]),(0,[z1,z235,z4,z5,z6,z44]),(0,[z1410,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z1411,z6]),(0,[z1412,z1,z2,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z92,z5,z6]),(0,[z7,z1,z226,z4,z5,z6]),(0,[z107,z1,z2,z719,z5,z6]),(0,[z2,z417,z4,z5,z6,z44]),(0,[z52,z7,z62,z4,z5,z6]),(0,[z101,z7,z2,z5,z25,z6])],[(0,[z7,z1,z270,z5,z22,z6]),(0,[z7,z1,z2,z5,z1413,z6]),(0,[z1,z2,z4,z187,z6,z44]),(0,[z1414,z1,z2,z4,z5,z6]),(0,[z7,z167,z4,z5,z33,z6]),(0,[z7,z548,z2,z251,z5,z6])],[(0,[z7,z1,z2,z1415,z5,z6]),(0,[z7,z1,z2,z5,z1416,z6]),(0,[z34,z7,z2,z166,z5,z6]),(0,[z1,z2,z4,z91,z129,z275])],[(0,[z7,z1,z2,z5,z1417,z6]),(0,[z231,z1,z2,z4,z5,z44]),(0,[z107,z1,z2,z5,z6,z224]),(0,[z1418,z1,z2,z4,z5,z6]),(1,[z7,z1,z4,z88,z408]),(0,[z7,z1,z57,z42,z5,z6])],[(0,[z1419,z7,z1,z2,z5,z6]),(0,[z7,z1,z2,z1420,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1421]),(0,[z99,z1,z2,z4,z189,z6]),(0,[z1,z2,z719,z105,z5,z6]),(0,[z54,z1,z2,z175,z5,z6]),(0,[z52,z75,z2,z4,z5,z6])],[],[(0,[z112,z416,z1,z4,z5,z6]),(0,[z7,z2,z436,z162,z5,z6]),(0,[z7,z1,z2,z5,z1422,z6]),(0,[z99,z1,z454,z4,z5,z6]),(0,[z1,z2,z160,z5,z6,z44]),(0,[z7,z144,z352,z4,z5,z6]),(0,[z7,z1,z2,z5,z6,z1330]),(0,[z7,z169,z346,z4,z5,z6])],[(0,[z65,z1,z2,z92,z5,z6]),(0,[z245,z1,z2,z66,z5,z6]),(0,[z7,z1,z1423,z2,z5,z6]),(0,[z7,z1424,z2,z4,z5,z6]),(0,[z1425,z1,z2,z4,z5,z6]),(0,[z1426,z7,z2,z5,z22,z6]),(0,[z1373,z1,z2,z4,z5,z6])],[(0,[z1427,z1,z2,z4,z5,z6]),(0,[z1428,z1,z2,z4,z5,z6])],[(0,[z65,z1,z216,z4,z5,z6]),(0,[z1,z2,z4,z59,z771,z6]),(0,[z7,z1,z2,z1429,z5,z6]),(0,[z7,z166,z4,z5,z381,z6]),(0,[z7,z1,z2,z4,z134,z6]),(0,[z725,z7,z1,z2,z5,z6]),(0,[z368,z1,z2,z22,z6,z17])],[(0,[z7,z1,z2,z1106,z5,z6]),(0,[z13,z7,z1,z2,z22,z6]),(0,[z1,z2,z1194,z5,z6,z44]),(0,[z207,z1,z2,z349,z5,z6]),(0,[z54,z1,z2,z30,z22,z6]),(0,[z1,z2,z4,z5,z337,z17]),(0,[z640,z7,z1,z2,z22,z6])],[(0,[z7,z1,z2,z5,z1430,z6]),(0,[z1,z2,z4,z5,z6,z1431]),(0,[z93,z7,z1,z346,z4,z17])],[(0,[z1,z2,z4,z5,z6,z337]),(0,[z1,z2,z4,z5,z6,z1432]),(0,[z1381,z7,z1,z4,z5,z6])],[(0,[z7,z1433,z2,z4,z5,z6]),(0,[z54,z1,z2,z5,z22,z44]),(0,[z1434,z1,z2,z4,z5,z6])],[(0,[z298,z416,z1,z4,z5,z6]),(0,[z1,z2,z4,z5,z260,z44]),(0,[z54,z154,z166,z4,z5,z6]),(0,[z21,z7,z1,z2,z5,z674]),(0,[z7,z1,z1435,z4,z5,z6]),(0,[z7,z1,z167,z542,z5,z6]),(0,[z1436,z7,z1,z2,z5,z6]),(0,[z7,z2,z4,z5,z134,z58]),(0,[z36,z1,z2,z251,z5,z6])]],
   [[(0,[z7,z1437,z2,z4,z5,z6]),(0,[z7,z1,z1438,z4,z5,z6]),(0,[z35,z7,z1,z4,z88,z567]),(0,[z368,z1,z2,z5,z445,z6])],[(0,[z54,z522,z2,z4,z5,z6]),(0,[z67,z7,z2,z4,z33,z328])],[(0,[z246,z74,z2,z4,z5,z6]),(0,[z1,z2,z82,z5,z6,z44]),(0,[z1,z2,z4,z5,z240,z44]),(0,[z54,z935,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z1439,z6]),(0,[z7,z1,z2,z98,z735,z6])],[(0,[z7,z1,z2,z1440,z5,z6]),(0,[z65,z1,z61,z162,z5,z6]),(0,[z1,z2,z5,z6,z44,z729]),(0,[z1,z2,z5,z22,z129,z44]),(0,[z1441,z1,z2,z4,z5,z6])],[(0,[z7,z298,z1,z30,z5,z6]),(0,[z7,z522,z2,z4,z5,z408]),(0,[z1131,z1,z2,z30,z5,z6])],[(0,[z54,z1,z2,z5,z22,z6]),(0,[z1,z2,z83,z5,z6,z44]),(0,[z7,z24,z2,z485,z5,z6]),(0,[z7,z1,z2,z5,z1442,z6]),(0,[z145,z1,z2,z30,z5,z6])],[(0,[z65,z1,z689,z4,z5,z6]),(0,[z7,z1,z2,z1443,z5,z6]),(0,[z1,z454,z4,z5,z6,z44]),(0,[z1,z2,z4,z5,z161,z44]),(0,[z1444,z1,z2,z4,z5,z6]),(0,[z52,z7,z152,z4,z5,z6]),(0,[z7,z1,z2,z5,z1445,z6]),(0,[z2,z417,z96,z4,z5,z6]),(0,[z7,z1,z2,z5,z1446,z6])],[(0,[z7,z283,z226,z4,z5,z6]),(0,[z7,z1,z454,z30,z5,z6]),(0,[z1,z2,z936,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z129])],[(0,[z516,z1,z167,z4,z5,z6]),(0,[z7,z1,z2,z1447,z5,z6]),(0,[z7,z1,z2,z5,z22,z408])],[(0,[z54,z1,z2,z5,z450,z6]),(0,[z63,z7,z2,z5,z451,z58]),(0,[z289,z7,z1,z4,z88,z6]),(0,[z7,z1,z2,z4,z187,z6])],[(0,[z1,z2,z66,z4,z5,z260]),(0,[z144,z2,z4,z5,z168,z44]),(0,[z7,z24,z241,z2,z5,z6]),(0,[z437,z1,z341,z4,z5,z6]),(0,[z7,z1,z441,z2,z4,z17])],[(0,[z1,z2,z403,z5,z6,z44]),(0,[z1,z2,z492,z5,z6,z44]),(0,[z54,z1,z2,z5,z43,z44]),(0,[z54,z949,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z6,z1448])],[(0,[z1449,z1,z2,z4,z5,z6]),(0,[z706,z7,z1,z4,z88,z6]),(0,[z1291,z1,z2,z5,z555,z6])],[(0,[z1,z2,z4,z5,z1450,z6]),(0,[z7,z1451,z2,z4,z5,z6]),(0,[z7,z94,z2,z5,z363,z6])],[(0,[z75,z1,z2,z372,z5,z6]),(0,[z7,z1,z4,z5,z88,z408])],[(0,[z7,z1,z2,z1452,z5,z6]),(0,[z35,z54,z1,z4,z88,z6]),(1,[z7,z1,z4,z1124,z6]),(1,[z7,z1,z4,z414,z16])]],
   [[(0,[z213,z54,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z1453]),(0,[z1454,z1,z2,z4,z5,z6]),(0,[z1455,z1,z2,z4,z5,z6]),(0,[z7,z1,z1262,z30,z5,z6])],[(0,[z7,z1456,z1,z4,z5,z6]),(0,[z7,z1,z2,z5,z1457,z6]),(0,[z7,z1,z150,z4,z1124,z6])],[(0,[z54,z1,z2,z4,z5,z14]),(0,[z26,z27,z2,z30,z5,z6]),(0,[z26,z298,z1,z4,z5,z6]),(0,[z7,z1,z2,z5,z6,z1404]),(0,[z7,z166,z4,z5,z6,z419]),(0,[z7,z472,z166,z4,z5,z6]),(0,[z28,z1,z2,z30,z5,z6]),(0,[z7,z1,z2,z5,z22,z328]),(0,[z1458,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z91,z161])],[(0,[z7,z1,z2,z5,z1459,z6]),(0,[z7,z1,z2,z1460,z5,z6]),(0,[z7,z1,z1461,z5,z22,z6]),(0,[z444,z1,z2,z335,z5,z6])],[(0,[z1,z268,z3,z4,z5,z6]),(0,[z1462,z1,z2,z4,z5,z6]),(0,[z748,z1,z2,z5,z450,z6]),(0,[z437,z1,z2,z361,z5,z6])],[(0,[z7,z2,z4,z5,z6,z1289]),(0,[z7,z1301,z2,z4,z5,z6]),(0,[z7,z1,z2,z30,z5,z40]),(0,[z7,z1,z2,z64,z1442,z6]),(0,[z7,z413,z2,z4,z460,z6])],[(0,[z7,z1,z2,z251,z5,z567]),(0,[z1426,z7,z2,z4,z5,z6]),(0,[z7,z124,z2,z4,z187,z6]),(0,[z1463,z7,z1,z2,z5,z6])],[(0,[z54,z1,z2,z4,z5,z650]),(0,[z54,z548,z2,z4,z5,z6]),(0,[z1464,z1,z2,z4,z5,z6]),(0,[z63,z7,z2,z5,z22,z58]),(0,[z7,z169,z2,z510,z5,z6])],[(0,[z112,z1,z454,z4,z5,z6]),(0,[z54,z1,z2,z91,z22,z6]),(0,[z21,z54,z1,z2,z5,z106]),(0,[z1465,z1,z2,z4,z5,z6]),(0,[z36,z1,z150,z4,z5,z6]),(0,[z1,z2,z5,z6,z1189,z199]),(0,[z1,z2,z4,z5,z6,z1016])],[(0,[z536,z9,z2,z4,z5,z6]),(0,[z47,z1,z2,z92,z5,z6]),(0,[z7,z1466,z2,z4,z5,z6]),(0,[z47,z1,z2,z30,z48,z6]),(0,[z276,z518,z1,z4,z5,z6]),(0,[z7,z8,z167,z4,z5,z6])],[(0,[z7,z1467,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z1468,z6]),(0,[z49,z54,z1,z196,z5,z6]),(0,[z7,z1,z2,z4,z5,z1469]),(0,[z7,z548,z2,z4,z5,z408]),(0,[z7,z1,z2,z5,z1470,z6])],[(0,[z7,z1,z2,z4,z5,z1471]),(0,[z1316,z1,z4,z5,z6,z44]),(0,[z1,z2,z30,z5,z129,z44]),(0,[z7,z1,z2,z513,z22,z6]),(0,[z7,z1,z57,z30,z5,z6]),(0,[z252,z1,z2,z4,z187,z6]),(0,[z7,z1472,z1,z4,z5,z6])],[(0,[z54,z1,z2,z4,z5,z44]),(0,[z54,z1,z980,z4,z5,z6]),(0,[z1473,z1,z2,z4,z5,z6])],[(0,[z26,z119,z2,z4,z5,z6]),(0,[z1,z3,z4,z5,z239,z6]),(0,[z1474,z7,z1,z2,z5,z6]),(0,[z49,z7,z1,z2,z422,z6]),(0,[z7,z1,z2,z4,z414,z50]),(0,[z368,z1,z2,z5,z137,z6]),(0,[z7,z1475,z2,z5,z22,z6])],[(0,[z65,z1,z556,z4,z5,z6]),(0,[z7,z2,z1160,z4,z5,z6]),(0,[z119,z1,z2,z5,z22,z6]),(0,[z7,z1,z2,z1476,z5,z6]),(0,[z7,z1,z2,z1477,z5,z6]),(0,[z1478,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1479]),(0,[z1480,z1,z2,z4,z5,z6]),(0,[z1481,z7,z2,z4,z5,z6])],[(0,[z207,z1,z2,z3,z5,z6]),(0,[z1,z2,z4,z5,z769,z44]),(0,[z28,z1,z167,z4,z5,z6]),(0,[z67,z2,z4,z163,z33,z6]),(0,[z7,z1,z341,z5,z22,z6]),(0,[z7,z1,z2,z30,z64,z6]),(0,[z7,z1,z2,z555,z6,z17]),(0,[z93,z7,z1,z2,z4,z711])]],
   [[(0,[z7,z476,z166,z4,z5,z6]),(0,[z7,z8,z270,z4,z5,z6]),(0,[z7,z1,z2,z198,z5,z6]),(0,[z7,z1,z2,z30,z98,z6])],[(0,[z7,z1,z2,z4,z5,z1482]),(0,[z68,z1,z2,z30,z5,z6]),(0,[z7,z24,z1,z235,z5,z6]),(0,[z1483,z7,z2,z5,z22,z6]),(0,[z31,z124,z2,z4,z5,z6]),(0,[z93,z7,z1,z2,z510,z17])],[(0,[z7,z1,z2,z1484,z5,z6]),(0,[z1,z2,z4,z5,z6,z1485]),(0,[z1351,z1,z2,z5,z6,z451]),(0,[z35,z1,z4,z69,z88,z6]),(0,[z1,z2,z30,z5,z6,z1093])],[(0,[z54,z1,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z1486,z6]),(0,[z7,z1,z2,z4,z1487,z6]),(0,[z1,z2,z5,z22,z1014,z6])],[(0,[z1488,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z1489,z5,z6]),(0,[z7,z1,z2,z5,z6,z1490]),(0,[z7,z1,z2,z5,z1491,z6]),(0,[z93,z178,z1,z2,z4,z17])],[(0,[z1,z270,z4,z5,z6,z44]),(0,[z21,z7,z1,z2,z5,z15]),(0,[z7,z1,z2,z403,z5,z6]),(0,[z991,z1,z2,z4,z5,z6])],[(0,[z1,z2,z4,z5,z44,z430]),(0,[z355,z1,z2,z4,z5,z44]),(0,[z54,z1,z878,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z408]),(0,[z7,z1,z2,z5,z6,z1492])],[(0,[z112,z1,z603,z4,z5,z6]),(0,[z659,z1,z61,z4,z5,z6]),(0,[z24,z2,z72,z5,z6,z44]),(0,[z1,z2,z139,z5,z25,z44]),(0,[z7,z1,z2,z1493,z5,z6]),(0,[z35,z7,z1,z88,z22,z6]),(0,[z1494,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z1268,z6])],[(0,[z7,z1,z2,z1495,z5,z6]),(0,[z246,z27,z2,z4,z5,z6]),(0,[z54,z1,z2,z4,z5,z260]),(0,[z54,z1,z2,z1002,z5,z6]),(0,[z7,z1,z2,z1496,z5,z6])],[(0,[z54,z1,z2,z492,z5,z6]),(0,[z7,z1,z2,z1497,z5,z6]),(1,[z7,z1,z4,z5,z787])],[(0,[z7,z1,z2,z208,z5,z6]),(0,[z7,z1,z2,z1077,z134,z6]),(0,[z7,z1,z4,z5,z1124,z6]),(0,[z7,z1,z4,z5,z414,z16]),(0,[z7,z169,z2,z42,z5,z6])],[(0,[z107,z1,z2,z303,z5,z6]),(0,[z7,z1,z2,z5,z1498,z6]),(0,[z200,z7,z152,z4,z5,z6]),(0,[z1,z1499,z2,z4,z5,z6]),(0,[z495,z243,z2,z4,z5,z6]),(0,[z368,z1,z2,z5,z18,z6])],[(0,[z7,z1,z270,z342,z5,z6]),(0,[z7,z152,z634,z4,z5,z6]),(0,[z7,z1,z2,z5,z1500,z6]),(0,[z7,z436,z4,z5,z88,z6]),(0,[z7,z1,z2,z4,z1501,z6]),(0,[z7,z1,z2,z1502,z5,z6])],[(0,[z74,z2,z4,z5,z48,z6]),(0,[z416,z1,z2,z403,z5,z6]),(0,[z164,z2,z417,z4,z5,z6]),(0,[z7,z1,z2,z5,z1503,z6]),(0,[z7,z1,z2,z1504,z5,z6])],[(0,[z27,z1,z2,z4,z5,z260]),(0,[z1,z2,z5,z140,z6,z44]),(0,[z52,z54,z152,z4,z5,z6]),(0,[z7,z2,z1004,z4,z5,z6]),(0,[z252,z241,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1297,z5,z6]),(0,[z7,z1,z2,z1195,z5,z6]),(0,[z7,z1,z2,z1505,z5,z6]),(0,[z54,z1,z2,z139,z5,z25]),(0,[z7,z1,z1506,z4,z5,z6]),(0,[z1,z2,z96,z30,z5,z6]),(0,[z7,z891,z2,z4,z5,z6]),(0,[z7,z1,z2,z449,z91,z129])]],
   [[(0,[z7,z1,z1028,z4,z5,z6]),(0,[z1,z61,z779,z4,z5,z6]),(0,[z1,z2,z4,z5,z1192,z6]),(0,[z7,z1,z2,z217,z5,z6]),(0,[z7,z1,z2,z4,z5,z328]),(0,[z7,z1,z1507,z4,z5,z6]),(0,[z7,z1,z2,z1252,z64,z6]),(0,[z7,z1,z2,z4,z422,z6]),(0,[z7,z169,z57,z4,z5,z6])],[(0,[z7,z2,z1508,z4,z5,z6]),(0,[z7,z1,z1509,z4,z5,z6]),(0,[z7,z1,z2,z1510,z5,z6]),(0,[z7,z1,z1461,z4,z5,z6]),(0,[z7,z1,z2,z449,z187,z6]),(0,[z1511,z1,z2,z4,z5,z6])],[(0,[z7,z1512,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z224]),(0,[z54,z1,z352,z4,z5,z6]),(0,[z1513,z1,z2,z4,z5,z6]),(0,[z29,z7,z1,z5,z519,z16]),(0,[z1,z899,z2,z4,z5,z6])],[(0,[z7,z1,z2,z468,z22,z6])],[(0,[z0,z74,z2,z4,z5,z6]),(0,[z7,z1,z2,z1514,z5,z6]),(0,[z116,z31,z1,z2,z5,z6]),(0,[z815,z1,z2,z5,z22,z6]),(0,[z54,z1,z2,z1023,z5,z6]),(0,[z35,z176,z1,z4,z88,z6])],[(0,[z7,z1,z2,z1515,z5,z6]),(0,[z7,z74,z2,z82,z5,z6]),(0,[z63,z7,z2,z4,z5,z58]),(0,[z7,z1,z103,z2,z422,z6])],[(0,[z213,z2,z4,z59,z5,z6]),(0,[z1516,z1,z2,z4,z5,z6]),(0,[z7,z2,z5,z22,z6,z1163]),(0,[z93,z7,z441,z2,z4,z17])],[(0,[z7,z1,z2,z1517,z5,z6]),(0,[z1458,z1,z2,z5,z22,z6]),(0,[z7,z1,z253,z4,z187,z6]),(0,[z1050,z1,z2,z5,z6,z275])],[(0,[z7,z1,z2,z4,z5,z1518]),(0,[z1,z2,z4,z5,z6,z769]),(0,[z1,z2,z4,z5,z1156,z6]),(0,[z207,z1,z2,z5,z129,z44]),(0,[z7,z1,z2,z1519,z5,z6]),(0,[z1520,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1521]),(0,[z1,z226,z4,z5,z6,z44]),(0,[z1405,z7,z1,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1522]),(0,[z54,z1,z420,z4,z5,z6]),(0,[z164,z1,z2,z117,z5,z6]),(0,[z181,z1,z2,z4,z5,z408])],[(0,[z54,z283,z2,z4,z5,z6]),(0,[z188,z2,z4,z5,z6,z179]),(0,[z1523,z1,z2,z4,z5,z6]),(0,[z52,z7,z126,z4,z5,z6])],[(0,[z7,z1,z2,z4,z5,z1524]),(0,[z7,z1475,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1525,z5,z6]),(0,[z119,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z5,z1526,z6]),(0,[z7,z1,z2,z4,z5,z1527]),(0,[z7,z1,z2,z4,z5,z1528]),(0,[z7,z1,z120,z4,z5,z320]),(0,[z7,z1,z2,z1529,z5,z6])],[(0,[z7,z1530,z2,z4,z5,z6]),(0,[z7,z1,z341,z4,z5,z6])],[(0,[z1,z2,z4,z5,z40,z44]),(0,[z1531,z1,z2,z4,z5,z6]),(0,[z38,z7,z2,z104,z5,z6]),(0,[z7,z1,z2,z4,z5,z753])],[(0,[z1,z2,z91,z22,z6,z44]),(0,[z101,z7,z103,z19,z5,z6]),(0,[z1483,z7,z2,z4,z5,z6])]],
   [[(0,[z54,z1,z2,z5,z418,z6]),(0,[z1,z2,z5,z22,z44,z17]),(0,[z7,z1,z2,z1532,z5,z6])],[(0,[z112,z7,z436,z4,z5,z6]),(0,[z67,z28,z2,z4,z33,z6]),(0,[z1,z2,z5,z22,z6,z1069]),(0,[z7,z1,z5,z22,z6,z1185])],[(0,[z7,z1,z1317,z4,z5,z6]),(0,[z7,z1,z2,z4,z1533,z6]),(0,[z54,z1,z2,z443,z5,z6]),(0,[z31,z1,z253,z4,z5,z6]),(0,[z7,z241,z2,z5,z6,z106]),(0,[z1,z2,z4,z5,z1534,z6]),(0,[z7,z1,z2,z1535,z5,z6])],[(0,[z7,z1,z2,z1536,z5,z6]),(0,[z1537,z1,z2,z4,z5,z6]),(1,[z1,z2,z22,z44,z17]),(0,[z246,z1,z2,z5,z22,z6]),(0,[z1323,z1,z2,z30,z5,z6]),(0,[z1538,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1539,z5,z6]),(0,[z1,z2,z122,z5,z6,z43]),(0,[z7,z1540,z2,z4,z5,z6])],[(0,[z54,z2,z436,z4,z5,z6]),(0,[z54,z1,z2,z5,z6,z519]),(0,[z7,z1,z2,z4,z5,z1541]),(0,[z7,z1,z2,z4,z1542,z6])],[(0,[z7,z1,z2,z4,z1543,z6]),(0,[z7,z1,z420,z4,z5,z328]),(0,[z1544,z1,z2,z4,z5,z6]),(0,[z100,z1,z2,z83,z5,z6]),(0,[z7,z1,z235,z5,z22,z6])],[(0,[z0,z659,z2,z4,z5,z6]),(0,[z54,z1,z1058,z4,z5,z6]),(0,[z7,z1,z4,z1142,z5,z6]),(0,[z7,z1,z2,z5,z70,z445])],[(0,[z7,z1,z2,z4,z1545,z6]),(0,[z54,z1,z2,z4,z5,z378]),(0,[z7,z1,z2,z4,z5,z1546]),(0,[z7,z1,z150,z4,z632,z6])],[(0,[z7,z1,z2,z1547,z5,z6]),(0,[z7,z1,z1326,z4,z5,z6]),(0,[z7,z103,z417,z19,z5,z6]),(0,[z7,z1,z2,z1548,z5,z6])],[(0,[z1,z2,z5,z69,z1503,z6]),(0,[z7,z241,z253,z4,z5,z6])],[(0,[z1,z2,z4,z371,z5,z44]),(0,[z124,z2,z4,z5,z6,z44]),(0,[z54,z1,z2,z449,z5,z6]),(1,[z7,z752,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z1549])],[(0,[z639,z7,z2,z4,z33,z6]),(0,[z7,z76,z166,z4,z5,z6]),(0,[z34,z7,z2,z117,z5,z6])],[(0,[z138,z1,z2,z4,z5,z769]),(0,[z54,z1,z346,z4,z5,z6]),(0,[z1550,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z1551,z5,z6]),(0,[z7,z1,z1552,z4,z5,z6]),(0,[z107,z1,z2,z5,z233,z6]),(0,[z7,z1,z454,z4,z5,z254]),(0,[z1553,z1,z2,z4,z5,z6]),(0,[z95,z1,z2,z4,z64,z6]),(0,[z97,z1,z2,z233,z22,z6])],[(0,[z7,z1,z1554,z4,z5,z6]),(0,[z107,z1,z2,z66,z5,z6]),(0,[z1,z2,z66,z5,z6,z43]),(0,[z7,z1,z120,z372,z5,z6]),(0,[z7,z1,z2,z4,z1555,z6]),(0,[z7,z522,z2,z310,z5,z6])]],
   [[(0,[z65,z1,z597,z4,z5,z6]),(0,[z207,z1,z2,z5,z6,z43]),(0,[z1556,z1,z2,z4,z5,z6]),(0,[z7,z1557,z2,z4,z5,z6]),(0,[z29,z7,z243,z4,z5,z16]),(0,[z93,z7,z1,z2,z4,z17])],[(0,[z47,z1,z226,z4,z48,z6]),(0,[z7,z1558,z2,z4,z5,z6]),(0,[z537,z7,z1,z2,z22,z6]),(0,[z1,z744,z2,z5,z22,z6])],[(0,[z815,z1,z2,z4,z5,z6]),(0,[z7,z413,z2,z5,z22,z6]),(0,[z7,z1,z120,z4,z414,z6]),(0,[z355,z1,z2,z5,z22,z6]),(0,[z7,z169,z2,z30,z5,z6]),(0,[z7,z241,z2,z139,z5,z6])],[(0,[z1,z1559,z2,z4,z5,z6]),(0,[z7,z2,z4,z33,z6,z328]),(0,[z1,z2,z4,z5,z6,z1560]),(0,[z7,z1,z221,z4,z64,z6]),(0,[z7,z2,z417,z5,z22,z6]),(0,[z7,z1,z120,z4,z5,z225])],[(0,[z7,z1,z1561,z4,z5,z6])],[(0,[z0,z1,z2,z4,z5,z260]),(0,[z1,z61,z4,z5,z496,z6]),(0,[z7,z1,z2,z1562,z5,z6]),(0,[z1,z2,z4,z5,z6,z1563]),(0,[z1,z2,z5,z6,z1335,z44]),(0,[z276,z1,z2,z5,z25,z6]),(0,[z7,z261,z2,z439,z5,z6])],[(0,[z54,z1,z2,z4,z5,z15]),(0,[z7,z1,z1564,z4,z5,z6]),(0,[z29,z7,z413,z4,z5,z16])],[(1,[z815,z1,z2,z5,z6]),(0,[z54,z1,z2,z488,z5,z6]),(0,[z1565,z1,z2,z4,z5,z6])],[(0,[z7,z1,z2,z92,z5,z6]),(0,[z1,z2,z30,z5,z44,z17]),(0,[z54,z1,z150,z4,z141,z6]),(0,[z164,z1,z2,z72,z5,z6]),(0,[z7,z1,z2,z1566,z5,z6]),(0,[z7,z1,z2,z4,z414,z6]),(0,[z1079,z1,z2,z4,z5,z6])],[(0,[z7,z1263,z2,z4,z5,z6])],[(0,[z7,z352,z4,z5,z6,z58])],[(0,[z7,z1,z1567,z4,z5,z6]),(0,[z1,z2,z5,z1232,z6,z44]),(0,[z100,z1,z2,z30,z5,z6])],[(0,[z7,z1,z1568,z4,z5,z6]),(0,[z437,z1,z2,z5,z22,z6]),(0,[z1569,z7,z1,z2,z5,z6]),(0,[z97,z7,z1,z2,z22,z6]),(0,[z1369,z1,z2,z30,z5,z6])],[(0,[z26,z2,z216,z4,z5,z6]),(0,[z1,z2,z4,z59,z218,z6]),(0,[z7,z1570,z2,z4,z5,z6]),(0,[z54,z1,z2,z542,z5,z6]),(0,[z7,z1,z2,z5,z6,z1571]),(0,[z164,z1,z2,z19,z5,z6]),(0,[z1,z2,z5,z6,z519,z1198])],[(0,[z7,z1572,z2,z4,z5,z6]),(0,[z7,z1,z2,z1573,z5,z6]),(0,[z7,z1,z2,z1574,z5,z6]),(0,[z7,z1,z2,z492,z414,z6]),(0,[z1575,z1,z2,z4,z5,z6]),(0,[z7,z241,z2,z30,z5,z6])],[(0,[z298,z1,z4,z5,z6,z44]),(0,[z7,z1,z2,z5,z6,z1576]),(0,[z178,z1,z2,z4,z5,z129])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 477) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 477).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 962).take 480) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1442).take 102) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1544)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [477, 485, 480, 102] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 91).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 189).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 277).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 380).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 471).take 41).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [91, 98, 88, 103, 91, 41] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_nil pcend))))))

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

end PEqualNP.Outside.L_meta_37217

theorem PEqualNP.Outside.L_meta_37217 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4008505064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008505064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37217.solve