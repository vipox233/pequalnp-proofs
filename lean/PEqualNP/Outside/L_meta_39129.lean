import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39129

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0000000000000000#64 ++ 0xffff414511d11c7f#64 : BitVec 128),
   (0x50088018668669aa#64 ++ 0x57fec2baeeaeebaa#64 : BitVec 128),
   (0x65c51cc30b30b2cc#64 ++ 0x66d5fcc30f30f3cc#64 : BitVec 128),
   (0x80962f03b03b0370#64 ++ 0x85b3ff03f03f03f0#64 : BitVec 128),
   (0x011837ec003ddc00#64 ++ 0x038ffffc003ffc00#64 : BitVec 128),
   (0x01e03bf7ddc00000#64 ++ 0x007fffffffc00000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [13, 10]⟩, ⟨.or, [0, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0000000000000000 0x05b2400000000020

def z1 : W := mkw 0x0000000000000000 0xffff414511d11c7f

def z2 : W := mkw 0x011837ec003ddc00 0x038ffffc003ffc00

def z3 : W := mkw 0x01e03bf7ddc00000 0x007fffffffc00000

def z4 : W := mkw 0x50088018668669aa 0x57fec2baeeaeebaa

def z5 : W := mkw 0x65c51cc30b30b2cc 0x66d5fcc30f30f3cc

def z6 : W := mkw 0x80962f03b03b0370 0x85b3ff03f03f03f0

def z7 : W := mkw 0x0000000000000000 0x7a4c004401c01c0f

def z8 : W := mkw 0x011837ec003ddc00 0x0183ffb8003fe000

def z9 : W := mkw 0x50008010668221aa 0x547ec2baee8003aa

def z10 : W := mkw 0x01e03bf7ddc00000 0xffffffffffd11c7f

def z11 : W := mkw 0x65c51cc30b30b2cc 0x0000bc820e20e380

def z12 : W := mkw 0x75cd9cdb6fb6fbee 0x66d5fefbef3ef3cc

def z13 : W := mkw 0x011837ec003ddc00 0x7bcffffc01fffc0f

def z14 : W := mkw 0x81f63ff7fdfb0370 0x007fffffffee0380

def z15 : W := mkw 0x80962f0390390250 0x8183ff01103f0050

def z16 : W := mkw 0xe5d73fc3bb3bb3fc 0xe7f7ffc3ff3ff3fc

def z17 : W := mkw 0x51e8bbffffc669aa 0x57fefebaeeaeebaa

def z18 : W := mkw 0x50088018668669aa 0x000082baee2ee380

def z19 : W := mkw 0x65c51cc30b30b2cc 0xfffffdc71ff1ffff

def z20 : W := mkw 0x011837ec003ddc00 0xfffffffd11fffc7f

def z21 : W := mkw 0x00202334d4c00000 0x992a033cf0c10c33

def z22 : W := mkw 0x65e53ff7dff0b2cc 0x66fffffffff0f3cc

def z23 : W := mkw 0x80160400203b0370 0x85800000003f03f0

def z24 : W := mkw 0x011837ec003ddc00 0x0000beb8002ee000

def z25 : W := mkw 0x50088008220669aa 0x57800000002eebaa

def z26 : W := mkw 0x0000000000000000 0x1808000400c00c03

def z27 : W := mkw 0x75cd9cdb6fb6fbee 0x77fffefbefbefbee

def z28 : W := mkw 0x80962f03b03b0370 0x0000be02e02e0380

def z29 : W := mkw 0x00180408003ddc00 0x038ec2b8003ffc00

def z30 : W := mkw 0x80b62f37f4fb0370 0x85bbff3ff0ff03f0

def z31 : W := mkw 0x80322334f4cb0130 0x812a033cf0cf0030

def z32 : W := mkw 0x500880184684688a 0x524c00b80e80e80a

def z33 : W := mkw 0x1008801864864922 0x112a0238e08e0822

def z34 : W := mkw 0x01f83bffddcd4c00 0x017fffffffcf0c00

def z35 : W := mkw 0x00840c0300300240 0x0491fc03003003c0

def z36 : W := mkw 0x010033e400000000 0x000ffffc00000000

def z37 : W := mkw 0x00180408003ddc00 0x038f4144003ffc00

def z38 : W := mkw 0x01e03bf7ddc00000 0x0000bebaee000000

def z39 : W := mkw 0x00180408003ddc00 0x03800000003ffc00

def z40 : W := mkw 0x5018a71866bf69aa 0x57ffffbaeebfebaa

def z41 : W := mkw 0x80962f03b03b0370 0xffffff47f1ff1fff

def z42 : W := mkw 0x00e00813ddc00000 0x00000002ee000000

def z43 : W := mkw 0x010014c000309000 0x0000bc800020e000

def z44 : W := mkw 0x0000000020020120 0x05b2c202e02e03a0

def z45 : W := mkw 0x50088018668669aa 0x77ffc2fbefbefbee

def z46 : W := mkw 0x80922b03b00b0130 0x8133ff03f00f0030

def z47 : W := mkw 0x01e03be799400000 0x0033ff47f1400000

def z48 : W := mkw 0x640504000230b2cc 0x668000000030f3cc

def z49 : W := mkw 0x25c51cc309309244 0x2491fc43013013c4

def z50 : W := mkw 0x50088018668669aa 0xffffc3ffffffffff

def z51 : W := mkw 0x0000000000000000 0xa801014511511455

def z52 : W := mkw 0x011837ec003ddc00 0x038efeb8002ee800

def z53 : W := mkw 0x654110c00b00b08c 0x66d540c10f10f04c

def z54 : W := mkw 0x0018272c003ddc00 0x038a033c003ffc00

def z55 : W := mkw 0x011837ec003ddc00 0x57fffffc00bffc2a

def z56 : W := mkw 0xd09eaf1bf6bf6bfa 0xd7ffffbbfebfebfa

def z57 : W := mkw 0x80122300b00b0130 0x992a0304f0cf0c33

def z58 : W := mkw 0x0000000000000000 0xfef5404111d0107f

def z59 : W := mkw 0x0010270000390000 0x0183ff00003f0000

def z60 : W := mkw 0x819e3fefb03fdf70 0x87bffffff03ffff0

def z61 : W := mkw 0x50008010668221aa 0x54700002ee8003aa

def z62 : W := mkw 0x006000104dc00000 0x004000000fc00000

def z63 : W := mkw 0x80122700b03b0130 0x81a3ff00f03f0030

def z64 : W := mkw 0x0000000000000000 0x57fe40000080082a

def z65 : W := mkw 0x00802b0390000000 0x007fff47f1c00000

def z66 : W := mkw 0x50088018668669aa 0x57f00002eeaeebaa

def z67 : W := mkw 0x65cd1cef0b34fecc 0x66ddfcff0f30ffcc

def z68 : W := mkw 0x010810ec0004dc00 0x020c00fc0000fc00

def z69 : W := mkw 0x80860803b0020370 0x84300003f00003f0

def z70 : W := mkw 0x80122300b00b0130 0x81220300f00f0030

def z71 : W := mkw 0x51f8bffffffffdaa 0x57ffffffffffffaa

def z72 : W := mkw 0x01f83fffddfddc00 0xfffffffffffffc7f

def z73 : W := mkw 0x01f83fffddfddc00 0x038ffffeee3ffc00

def z74 : W := mkw 0x654110c00b00b08c 0x7a4c00c40fc0fc0f

def z75 : W := mkw 0x654114c00b30b08c 0x62c5fcc00f30f00c

def z76 : W := mkw 0xd01e8408223f6bfa 0xd7800000003febfa

def z77 : W := mkw 0x010814ec0034dc00 0x028dfcfc0030fc00

def z78 : W := mkw 0x0000000000000000 0x992a010410c10c33

def z79 : W := mkw 0x80962f0390390250 0x80013d0110110050

def z80 : W := mkw 0x011837ec003ddc00 0x03fffffd11fffc00

def z81 : W := mkw 0x011837ec003ddc00 0x67dffffd013ffc4c

def z82 : W := mkw 0x80962f03b03b0370 0x9dbbff07f0ff0ff3

def z83 : W := mkw 0x0000000000000000 0x85b3410110110070

def z84 : W := mkw 0x01c018c309000000 0x0055fcc30f000000

def z85 : W := mkw 0x00202334d4c00000 0x007ec3befec00000

def z86 : W := mkw 0x0000000000000000 0xff80000000111c7f

def z87 : W := mkw 0x65c51cc30b30b2cc 0xffd5fcc30f31ffff

def z88 : W := mkw 0x01e03bf7ddc00000 0x002abfbefec00000

def z89 : W := mkw 0x0000001044800000 0x002a0238e0800000

def z90 : W := mkw 0x011037e400399400 0x00013d4400111400

def z91 : W := mkw 0x4000000002002088 0x468000000020e388

def z92 : W := mkw 0x654110c00b00b08c 0x624400c00f00f00c

def z93 : W := mkw 0x819e3fefb03fdf70 0x038ffffee03fff80

def z94 : W := mkw 0x0000000000000000 0x7bcf414401d11c0f

def z95 : W := mkw 0x41e03bf7dfc02088 0x46ffffffffe0e388

def z96 : W := mkw 0x0000000000000000 0x007f414511c00000

def z97 : W := mkw 0x500880080204688a 0x520000000000e80a

def z98 : W := mkw 0x01c018c309000000 0xfffffdc71fd11c7f

def z99 : W := mkw 0x65dd3fef0b3dfecc 0x67dfffff0f3fffcc

def z100 : W := mkw 0x25c51cc309309244 0x20013c4101101044

def z101 : W := mkw 0x819e3fefb03fdf70 0x0000bebae02ee380

def z102 : W := mkw 0x80962f03b03b0370 0x0033ff03f02e0380

def z103 : W := mkw 0x0000001044800000 0x007fc3ffffc00000

def z104 : W := mkw 0x0000000000000000 0x57ff414400911c2a

def z105 : W := mkw 0x64e50813dfc022cc 0x64700003ffc003cc

def z106 : W := mkw 0x00180408003ddc00 0x00000000002ee000

def z107 : W := mkw 0x640504000230b2cc 0x66d4c0820e30f3cc

def z108 : W := mkw 0x80860803b0020370 0x85b34103f01103f0

def z109 : W := mkw 0x01e03bf7ddc00000 0x0055fefbef000000

def z110 : W := mkw 0x819e3fefb03fdf70 0x85b3ffbbf03fe3f0

def z111 : W := mkw 0x0000000000000000 0x66d540410110104c

def z112 : W := mkw 0x75ddbfff6fbfffee 0x77ffffffefbfffee

def z113 : W := mkw 0x80962b03b00b0370 0x85320303f00f03f0

def z114 : W := mkw 0x65dd3fef0b3dfecc 0x0000beba0e2ee380

def z115 : W := mkw 0x011837ec003ddc00 0x010b3f7c001f1c00

def z116 : W := mkw 0x819e3fef903dde50 0x838ffffd103ffc50

def z117 : W := mkw 0x0000000000000000 0x0001014400111400

def z118 : W := mkw 0x010810ec0004dc00 0x038f41fc0011fc00

def z119 : W := mkw 0x0008000800044800 0x010a0238000e0800

def z120 : W := mkw 0x016010f44dc00000 0x004c00fc0fc00000

def z121 : W := mkw 0x00202334d4c00000 0x00000238e0000000

def z122 : W := mkw 0x0000000020020120 0x57fec202e0ae0baa

def z123 : W := mkw 0x80160400203b0370 0x85b2c202e03f03f0

def z124 : W := mkw 0x80962f03b03b0370 0xadb3ff47f17f17f5

def z125 : W := mkw 0x0008000800044800 0x038ec2b8002ee800

def z126 : W := mkw 0x01e03bf7ddc00000 0x03ffffffffd11c00

def z127 : W := mkw 0x80860803b0020370 0xffff4147f1d11fff

def z128 : W := mkw 0x80162700b03b0370 0x85a20300f03f03f0

def z129 : W := mkw 0x00202334d4c00000 0x002a033cf0c00000

def z130 : W := mkw 0x0000000000000000 0xeed541451151145d

def z131 : W := mkw 0x50088018668669aa 0x038ec2baee2eeb80

def z132 : W := mkw 0x0000000000000000 0xfc70000111c0007f

def z133 : W := mkw 0x65c51cc30b30b2cc 0xfef5fcc31ff0f3ff

def z134 : W := mkw 0x4000000002002088 0x46d4c0820e20e388

def z135 : W := mkw 0x0010270000390000 0x0000be00002e0000

def z136 : W := mkw 0x50008010668221aa 0x55f2c202eeae03aa

def z137 : W := mkw 0x50088018668669aa 0x57aa0238e0aeebaa

def z138 : W := mkw 0x64c50c030b30b2cc 0x66d000030f30f3cc

def z139 : W := mkw 0x508c8c1b66b66bea 0x57fffebbeebeebea

def z140 : W := mkw 0x5118b7fc66bffdaa 0x038ffffeee3fff80

def z141 : W := mkw 0x010014c000309000 0xfffffdc511f1fc7f

def z142 : W := mkw 0xe5df3fefbb3ffffc 0xe7ffffffff3ffffc

def z143 : W := mkw 0x50088018668669aa 0x567c00baee80ebaa

def z144 : W := mkw 0x016033f44dc00000 0x004ffffc0fc00000

def z145 : W := mkw 0x011837ec003ddc00 0x9baffffc10fffc33

def z146 : W := mkw 0x50088018668669aa 0x7ffec2feefeeffaf

def z147 : W := mkw 0x01e03ff7ddf09000 0x02fffffffff0f000

def z148 : W := mkw 0x50008000220221aa 0x54000000000003aa

def z149 : W := mkw 0x644100000b00208c 0x604000000f00000c

def z150 : W := mkw 0x0018232c000d4c00 0x010a033c000f0c00

def z151 : W := mkw 0x011037e400399400 0x0285fdc40031f400

def z152 : W := mkw 0x0000000000000000 0x46d4400000000008

def z153 : W := mkw 0x80962f03b03b0370 0x8122bf02f02f03b0

def z154 : W := mkw 0x01f83fffddfddc00 0x03fffffffffffc00

def z155 : W := mkw 0xa5d73fc3b93b9374 0xa5b3ff43f13f13f4

def z156 : W := mkw 0x5028a33cf6c669aa 0x57fec3befeeeebaa

def z157 : W := mkw 0x74c588136f8223ee 0x74700003ef8003ee

def z158 : W := mkw 0x65c51cc30b30b2cc 0x0285fcc20e30f380

def z159 : W := mkw 0x754990d86f86f9ae 0x77fec2faefaefbae

def z160 : W := mkw 0x011837ec003ddc00 0x010abfbc002fec00

def z161 : W := mkw 0x500880184684688a 0x7a4c00fc0fc0fc0f

def z162 : W := mkw 0x80962f03b03b0370 0x84313d03f01103f0

def z163 : W := mkw 0x0000000000000000 0x0032c202e0000000

def z164 : W := mkw 0x50008010668221aa 0x00000002ee000380

def z165 : W := mkw 0x64c50c030b3022cc 0x64d1fc030f3003cc

def z166 : W := mkw 0x0000000000000000 0xffb3410110111c7f

def z167 : W := mkw 0x01e03bf7ddc00000 0x66ffffffffd0104c

def z168 : W := mkw 0x4008000802046888 0x47dec2ba0e2eeb88

def z169 : W := mkw 0x00180408003ddc00 0xffff414511fffc7f

def z170 : W := mkw 0x0010230000090000 0x01020300000f0000

def z171 : W := mkw 0xd09eaf1bf6bf6bfa 0xffffffffffffffff

def z172 : W := mkw 0x0000000000000000 0x7a7f414511c01c0f

def z173 : W := mkw 0x01c018d34d800000 0x007ffefbef800000

def z174 : W := mkw 0x011837ec003ddc00 0x000ffffc002ee000

def z175 : W := mkw 0x64c508030b0022cc 0x645000030f0003cc

def z176 : W := mkw 0x010014c000309000 0x0285fcc00030f000

def z177 : W := mkw 0x40840c03023022c8 0x46d5fc830e30e3c8

def z178 : W := mkw 0x4000000002002088 0x57fec0820ea0ebaa

def z179 : W := mkw 0x00e00813ddc00000 0x00700003ffc00000

def z180 : W := mkw 0x80862b03b0020370 0x8433ff03f00003f0

def z181 : W := mkw 0x654110c00b00b08c 0x000000800e00e000

def z182 : W := mkw 0x50088008220669aa 0x57d4c0820e2eebaa

def z183 : W := mkw 0x0000000000000000 0x038f414400111c00

def z184 : W := mkw 0x010010c000000000 0x0005fcc000000000

def z185 : W := mkw 0xd0868813f68223fa 0xd4700003fe8003fa

def z186 : W := mkw 0x010033e400000000 0x007ffffd11c00000

def z187 : W := mkw 0x00802b0390000000 0x0033ff03f0000000

def z188 : W := mkw 0x80962f03b03b0370 0x8001bf03f03f03d0

def z189 : W := mkw 0x010014c000309000 0x66d5fcc10130f04c

def z190 : W := mkw 0x0008000800044800 0x000082b8002ee000

def z191 : W := mkw 0x0000000000000000 0x0000000000000000

def z192 : W := mkw 0x01e03bf7ddc00000 0x007efebaee800000

def z193 : W := mkw 0x010033e400000000 0x0000beb800000000

def z194 : W := mkw 0x50008010668221aa 0xfc700003ffc003ff

def z195 : W := mkw 0x64c508030b0022cc 0x66d4c0830f20e3cc

def z196 : W := mkw 0x01e03be799400000 0x00013d4511400000

def z197 : W := mkw 0x640504000230b2cc 0x000000000020e380

def z198 : W := mkw 0x010033e400000000 0x00013d4400000000

def z199 : W := mkw 0x80962f03b03b0370 0x81233f01f01f0070

def z200 : W := mkw 0x50088008220669aa 0xff800000003fffff

def z201 : W := mkw 0x5118b7fc66bffdaa 0xffffffffffffffff

def z202 : W := mkw 0x0000001044800000 0xffffc3ffffd11c7f

def z203 : W := mkw 0x25c51cc309309244 0xffff7d4511d11c7f

def z204 : W := mkw 0xc0962f03b23b23f8 0xc7f7ff83fe3fe3f8

def z205 : W := mkw 0x50088008220669aa 0x00000000002ee380

def z206 : W := mkw 0x50088018668669aa 0x57ffc3feeebfffaa

def z207 : W := mkw 0x819e3fefb03fdf70 0xfffffffff1ffffff

def z208 : W := mkw 0x500880184684688a 0x000000b80e00e000

def z209 : W := mkw 0x4000000002002088 0x445000020e000388

def z210 : W := mkw 0x010810ec0004dc00 0x000000b80000e000

def z211 : W := mkw 0x5018a33c668f6daa 0x57fec3beeeafefaa

def z212 : W := mkw 0x0000000000000000 0xffcc004401d11c7f

def z213 : W := mkw 0x01c018c309000000 0x66d5fcc30f10104c

def z214 : W := mkw 0x010014c000309000 0x038ffdc40031fc00

def z215 : W := mkw 0x0000000020020120 0x05800000002e03a0

def z216 : W := mkw 0x65c51cc30b30b2cc 0x46d4fc820e20e388

def z217 : W := mkw 0x51e8bbffffc669aa 0x57ffffffffeeebaa

def z218 : W := mkw 0x65e53ff7dff0b2cc 0x007fffffffe0e380

def z219 : W := mkw 0x50e8881bffc669aa 0x57fec2bbffeeebaa

def z220 : W := mkw 0x1018a33c648f4d22 0x112a033ce08f0c22

def z221 : W := mkw 0x5118b7fc66bffdaa 0x57fffffeeebfffaa

def z222 : W := mkw 0x01e03bf7ddc00000 0x000ffffeee000000

def z223 : W := mkw 0x80962f13f4bb0370 0x85ffffbbfebf03f0

def z224 : W := mkw 0x811e37ec203fdf70 0x878ffffc003ffff0

def z225 : W := mkw 0x809e2f0bb03f4b70 0x87bfffbbf03febf0

def z226 : W := mkw 0x011037e400399400 0x0183ff44003f1400

def z227 : W := mkw 0x51e8bbffdfc4688a 0x527fffffffc0e80a

def z228 : W := mkw 0x1008801864864922 0x57fe4238e08e082a

def z229 : W := mkw 0x0000001044800000 0x004c00b80e800000

def z230 : W := mkw 0x01e03bf7ddc00000 0xa87fffffffd11455

def z231 : W := mkw 0x640504000230b2cc 0xff8000000031ffff

def z232 : W := mkw 0x25c51cc309309244 0xa8013d4511511455

def z233 : W := mkw 0x0018232c000d4c00 0x038f437c001f1c00

def z234 : W := mkw 0x01f83fffddfddc00 0x0000bebaee2ee000

def z235 : W := mkw 0x41c018c30b002088 0x46d5fcc30f20e388

def z236 : W := mkw 0x80160400203b0370 0x85b34101103f03f0

def z237 : W := mkw 0x80962f03b03b0370 0x05b2fe02e02e03a0

def z238 : W := mkw 0x80962f03b03b0370 0xe7f7ff43f13f13fc

def z239 : W := mkw 0x50088008220669aa 0x578ec2b8002eebaa

def z240 : W := mkw 0x51e8bbffffc669aa 0xffffffffffffffff

def z241 : W := mkw 0x0000000000000000 0x000ec2b800000000

def z242 : W := mkw 0x1028a33cf4c64922 0x112a033cf0ce0822

def z243 : W := mkw 0x75cd9ccb2b36fbee 0x77d5fcc30f3efbee

def z244 : W := mkw 0x0004040000300240 0x04800000003003c0

def z245 : W := mkw 0x81f63ff7fdfb0370 0x85ffffffffff03f0

def z246 : W := mkw 0x0000000000000000 0x8122010010010030

def z247 : W := mkw 0x50088018668669aa 0x557a023aee8e0baa

def z248 : W := mkw 0x80122300b00b0130 0x00000200e00e0000

def z249 : W := mkw 0x25c51cc309309244 0x00003c0000000000

def z250 : W := mkw 0x0008001844844800 0x03fec2baeeaee800

def z251 : W := mkw 0x654910ec0b04fc8c 0x624c00fc0f00fc0c

def z252 : W := mkw 0x01e03be799400000 0x007f7d4511c00000

def z253 : W := mkw 0x011837ec003ddc00 0xff8ffffc003ffc7f

def z254 : W := mkw 0x011837ec003ddc00 0x0285fef8003ef000

def z255 : W := mkw 0x51e0bbf7ffc221aa 0x547fffffffc003aa

def z256 : W := mkw 0x1008801864864922 0x13aec2b8e0aee822

def z257 : W := mkw 0x0080080300000000 0x0011fc0300000000

def z258 : W := mkw 0x65c51cc30b30b2cc 0x6244bcc20f20f38c

def z259 : W := mkw 0x50188408223ffdaa 0x57800000003fffaa

def z260 : W := mkw 0x65d53fc30b39b2cc 0x67d7ffc30f3ff3cc

def z261 : W := mkw 0x0000000000000000 0x85ff414511d10070

def z262 : W := mkw 0x00202334d4c00000 0x007f437df1c00000

def z263 : W := mkw 0x012033f4d4c00000 0x002ffffcf0c00000

def z264 : W := mkw 0x0008000800044800 0xffffc3fd11fffc7f

def z265 : W := mkw 0x0000000000000000 0xfd7a010511c10c7f

def z266 : W := mkw 0x65cd1ccb0b34facc 0x67dffefb0f3efbcc

def z267 : W := mkw 0x80962f03b03b0370 0xfdf3ff03f1ff03ff

def z268 : W := mkw 0x65e53ff7dff0b2cc 0xfffffffffff1ffff

def z269 : W := mkw 0x00840c0300300240 0x0000bc0200200380

def z270 : W := mkw 0x01803be790000000 0x003ffffff0000000

def z271 : W := mkw 0x50e08813ffc221aa 0x54700003ffc003aa

def z272 : W := mkw 0x0010270000390000 0x85b3ff01103f0070

def z273 : W := mkw 0x0000001044800000 0x007ec2baee800000

def z274 : W := mkw 0x01e03bf7ddc00000 0x0070bebbffc00000

def z275 : W := mkw 0x01c018c309000000 0x0000bc820e000000

def z276 : W := mkw 0x0000000000000000 0x997f414511c10c33

def z277 : W := mkw 0x80860803b0020370 0x00000002e0000380

def z278 : W := mkw 0x75cd9cdb6fb6fbee 0xffffffffffffffff

def z279 : W := mkw 0x01c01cc309309000 0x02d5fcc30f30f000

def z280 : W := mkw 0x1008801864864922 0x00000238e00e0000

def z281 : W := mkw 0x01e03bf7ddc00000 0x7a7fffffffc01c0f

def z282 : W := mkw 0x516890fc6fc669aa 0x57fec2feefeeebaa

def z283 : W := mkw 0x00840c0300300240 0x00013c0100100040

def z284 : W := mkw 0x75cd9cdb6fb6fbee 0x0000bebaee2ee380

def z285 : W := mkw 0x011837ec003ddc00 0x0001bffc003ff400

def z286 : W := mkw 0x01e03be799400000 0xa8013d4511511455

def z287 : W := mkw 0x0000000000000000 0xfe7c004511c01c7f

def z288 : W := mkw 0x65c51cc30b30b2cc 0xeed5fdc71f71f7dd

def z289 : W := mkw 0x1000801064820122 0x10200000e0800022

def z290 : W := mkw 0x654514c00b30b2cc 0x66c400c00f30f3cc

def z291 : W := mkw 0x80962f03b03b0370 0xd7ffff03f0bf0bfa

def z292 : W := mkw 0x75cd9cdb6fb6fbee 0x57fefebaeeaeebaa

def z293 : W := mkw 0x5118b7fc66bffdaa 0x0000bebaee2ee380

def z294 : W := mkw 0x80f62f13fdfb0370 0x85f3ff03ffff03f0

def z295 : W := mkw 0x010010e400009400 0x0000004400001400

def z296 : W := mkw 0x011837ec003ddc00 0x87bffffd103ffc70

def z297 : W := mkw 0x740d84082236fbee 0x77800000003efbee

def z298 : W := mkw 0x80962f03b03b0370 0x85ffff47f1ff03f0

def z299 : W := mkw 0x24c5080309000244 0x2000000101000044

def z300 : W := mkw 0x81f63ff7fdfb0370 0xffffffffffff1fff

def z301 : W := mkw 0x81963fe790399650 0x80013d4510111450

def z302 : W := mkw 0x00e02b13ddc00000 0x0073ff03ffc00000

def z303 : W := mkw 0x50088018668669aa 0x547082baeeaee3aa

def z304 : W := mkw 0x81f63fe799790250 0x80013d4511510050

def z305 : W := mkw 0x01841cc300309240 0x0695fcc30030f3c0

def z306 : W := mkw 0x00802b03b0020120 0x05b3ff03f02e03a0

def z307 : W := mkw 0x0000000000000000 0x0054c0820e000000

def z308 : W := mkw 0x801e0408203fdf70 0x87800000003ffff0

def z309 : W := mkw 0x80120000200b0130 0x81000000000f0030

def z310 : W := mkw 0x65dd3fef0b3dfecc 0xffffffff1fffffff

def z311 : W := mkw 0xe5d73fc3bb3bb3fc 0x66d5fec3ef3ef3cc

def z312 : W := mkw 0x010010e400000000 0x000c00fc00000000

def z313 : W := mkw 0x00802b13d4800000 0x007fffbbfe800000

def z314 : W := mkw 0x65c51cc30b30b2cc 0x6450bc830f20e3cc

def z315 : W := mkw 0x010810ec0004dc00 0x7a4c00fc01c0fc0f

def z316 : W := mkw 0xd09eaf1bf6bf6bfa 0x57fefebaeeaeebaa

def z317 : W := mkw 0x75cd9cdb4fb4face 0x76ddfcfb0fb0fbce

def z318 : W := mkw 0x5018841866bffdaa 0x57fec2baeebfffaa

def z319 : W := mkw 0x74cd881b6f866bee 0x77fec2bbefaeebee

def z320 : W := mkw 0x80962f03b03b0370 0x8580be02e03f03f0

def z321 : W := mkw 0x01e03be799400000 0x00003c0000000000

def z322 : W := mkw 0x0000001044800000 0x000082baee000000

def z323 : W := mkw 0x0000000000000000 0x0490c00200200380

def z324 : W := mkw 0x64c508030b0022cc 0x66d540430f1013cc

def z325 : W := mkw 0xe5d73fc3bb3bb3fc 0x0000be82ee2ee380

def z326 : W := mkw 0x0000000000000000 0x0491400100100040

def z327 : W := mkw 0x0000000000000000 0x03ff414511d11c00

def z328 : W := mkw 0x011037e400399400 0x038f7d4400111c00

def z329 : W := mkw 0x50088008220669aa 0x57fe400000aeebaa

def z330 : W := mkw 0xe5d73fc3bb3bb3fc 0x85b3ff83fe3fe3f0

def z331 : W := mkw 0x0010270000390000 0x038fff44003f1c00

def z332 : W := mkw 0x500080104680208a 0x504000000e80000a

def z333 : W := mkw 0x01e03be799400000 0x0055fdc71f400000

def z334 : W := mkw 0x64c508030b0022cc 0x000000020e000380

def z335 : W := mkw 0x80962f03b03b0370 0x8430be03f02e03f0

def z336 : W := mkw 0xd09eaf1bf6bf6bfa 0x85b3ffbbfe3fe3f0

def z337 : W := mkw 0xd096af13f6bb23fa 0xd5f3ff03febf03fa

def z338 : W := mkw 0x010037e400309000 0x028ffffc0030f000

def z339 : W := mkw 0x80960c03b03b0370 0x85b00003f03f03f0

def z340 : W := mkw 0x50008010668221aa 0xffff4147ffd11fff

def z341 : W := mkw 0xd09eaf0bb23f6bfa 0xd7b3ff03f03febfa

def z342 : W := mkw 0x0000000000000000 0x624400400100100c

def z343 : W := mkw 0x65c118c30b00b08c 0x6255fcc30f00f00c

def z344 : W := mkw 0x011037e400399400 0x00003c0000000000

def z345 : W := mkw 0x01e03bf7ddc00000 0x0001bfffff400000

def z346 : W := mkw 0x0000000000000000 0x57ff414511c0082a

def z347 : W := mkw 0x1008801864864922 0x117ec2baee8e0822

def z348 : W := mkw 0x64c508030b0022cc 0xfc7000031fc003ff

def z349 : W := mkw 0x81963fc3b03b9370 0x87b7ffc3f03ff3f0

def z350 : W := mkw 0x011814c8003ddc00 0x0385fcc0003ffc00

def z351 : W := mkw 0x0000000000000000 0xab8f414511511c55

def z352 : W := mkw 0x80860803b0020370 0x85b2c203f02e03f0

def z353 : W := mkw 0x909eaf1bf4bf4b72 0x95bbff3bf0bf0bf2

def z354 : W := mkw 0x0000000000000000 0x87bf414510111c70

def z355 : W := mkw 0x016033f4ddc00000 0x006e03fcffc00000

def z356 : W := mkw 0x010014c000309000 0x00013c4000101000

def z357 : W := mkw 0x80860803b0020370 0xfc700003f1c003ff

def z358 : W := mkw 0x410014c00230b088 0x46d5fcc20e30f388

def z359 : W := mkw 0x011037e400390000 0x018ffffc003f0000

def z360 : W := mkw 0x01c018c309000000 0x007ffdc71fc00000

def z361 : W := mkw 0x80160400203b0370 0xff800000003f1fff

def z362 : W := mkw 0x0000000000000000 0xfff0000111d11c7f

def z363 : W := mkw 0x010833ec00044800 0x038ffffc002ee800

def z364 : W := mkw 0x80962f0390390250 0xffff7d4511d11c7f

def z365 : W := mkw 0x0000000000000000 0x038e400000000800

def z366 : W := mkw 0x81f63ff7fdfb0370 0x0000bebaee2e0380

def z367 : W := mkw 0x0000000000000000 0xd7ff41011091087a

def z368 : W := mkw 0x65e53ff7dff0b2cc 0x0000bebaee20e380

def z369 : W := mkw 0x0018232c000d4c00 0x992a033c10cf0c33

def z370 : W := mkw 0x640504000230b2cc 0x66d540410130f3cc

def z371 : W := mkw 0x00180408003ddc00 0xff800000003ffc7f

def z372 : W := mkw 0x65c51cc30b30b2cc 0x66fffdc71ff0f3cc

def z373 : W := mkw 0x81f63ff7fdfb0370 0x85b3ffbbfe3f03f0

def z374 : W := mkw 0x00840c0300300240 0x66d5fc43013013cc

def z375 : W := mkw 0x80160400203b0370 0xffff414511ff1fff

def z376 : W := mkw 0x500880184684688a 0xffff41fd1fd1fc7f

def z377 : W := mkw 0x011837ec003ddc00 0x020cbefc002efc00

def z378 : W := mkw 0x016010f44dc00000 0x007ec2feefc00000

def z379 : W := mkw 0x0000000000000000 0x77ff40410190186e

def z380 : W := mkw 0x50088018668669aa 0xfffec2bbffeeebff

def z381 : W := mkw 0x01e83bffddc44800 0x03ffffffffeee800

def z382 : W := mkw 0x0000000020020120 0x85b3c303f03f03f0

def z383 : W := mkw 0x00e00813ddc00000 0x007ec2bbffc00000

def z384 : W := mkw 0x0008000800044800 0x038fc3fc003ffc00

def z385 : W := mkw 0x901aa318f48f4932 0x912a0338f08f0832

def z386 : W := mkw 0x8006000020020370 0x84000000000003f0

def z387 : W := mkw 0xe4c70803bb0223fc 0xe4700003ff0003fc

def z388 : W := mkw 0x80962f0390390250 0x8033ff03f0110050

def z389 : W := mkw 0x5118b7fc46bdfc8a 0x53cffffc0ebffc0a

def z390 : W := mkw 0x011837ec003ddc00 0xab8ffffd117ffc55

def z391 : W := mkw 0x809e2f0bb03fdf70 0x87b3ff03f03ffff0

def z392 : W := mkw 0x50088018668669aa 0x57cc00b80eaeebaa

def z393 : W := mkw 0x0038233cd4cd4c00 0x012a033cf0cf0c00

def z394 : W := mkw 0x516890fc4fc4688a 0x524c00fc0fc0e80a

def z395 : W := mkw 0x011833ec000ddc00 0x030e03fc000ffc00

def z396 : W := mkw 0x811a37ecb03fdd30 0x83affffcf03ffc30

def z397 : W := mkw 0x01f03ff7ddf90000 0x01ffffffffff0000

def z398 : W := mkw 0x500880184684688a 0x53cec2b80eaee80a

def z399 : W := mkw 0x25c51cc309309244 0x66d57c410110104c

def z400 : W := mkw 0x0018272c003d4c00 0x018bff3c003f0c00

def z401 : W := mkw 0x65c51cc30b30b2cc 0x2001bcc30f30f3c4

def z402 : W := mkw 0x01e03bf7ddc00000 0x997fffffffc10c33

def z403 : W := mkw 0x81fe3ffffdffdf70 0x87fffffffffffff0

def z404 : W := mkw 0x640504000230b2cc 0xffff414511f1ffff

def z405 : W := mkw 0x0000000000000000 0xdffe410410c10c3b

def z406 : W := mkw 0x00802b0390000000 0x0000be02e0000000

def z407 : W := mkw 0x65c51cc30b30b2cc 0x67dffdc70f31ffcc

def z408 : W := mkw 0x65c51cc30b30b2cc 0x77fffcc30fb0fbee

def z409 : W := mkw 0x0000000000000000 0x8800010410410411

def z410 : W := mkw 0x01e03bf7ddc00000 0x85ffffffffd10070

def z411 : W := mkw 0x411837ec023dfc88 0x47dffffe0e3fff88

def z412 : W := mkw 0x01e03bf7fdc20120 0x05ffffffffee03a0

def z413 : W := mkw 0x1008800820064922 0x11000000000e0822

def z414 : W := mkw 0x80962f0390390250 0x00003c0000000000

def z415 : W := mkw 0x11e8bbfffdc64922 0x117fffffffce0822

def z416 : W := mkw 0x0000000000000000 0x67df414501111c4c

def z417 : W := mkw 0x64c508030b0022cc 0xffff41471fd11fff

def z418 : W := mkw 0x00842f0390300240 0x04b3ff03f03003c0

def z419 : W := mkw 0x01f83fffddfddc00 0x007fffffffeee000

def z420 : W := mkw 0x0000000000000000 0x7ffe404401c01c2f

def z421 : W := mkw 0x1008801864864922 0xffff437df1df1c7f

def z422 : W := mkw 0x0000000020020120 0xffffc347f1ff1fff

def z423 : W := mkw 0x0000040000309000 0x028000000030f000

def z424 : W := mkw 0xd08e881bf6866bfa 0xd7fec2bbfeaeebfa

def z425 : W := mkw 0x010814c80034d800 0x038ffef8003ef800

def z426 : W := mkw 0x0000000000000000 0x2800004401401405

def z427 : W := mkw 0x65c51cc30b30b2cc 0x6680bc820e30f3cc

def z428 : W := mkw 0x801a232cb00f4d30 0x812a033cf00f0c30

def z429 : W := mkw 0x00102700203b0120 0x05b3ff02e03f03a0

def z430 : W := mkw 0x016010f44dc00000 0x000000b80e000000

def z431 : W := mkw 0x0000001044800000 0x57fec2baee80082a

def z432 : W := mkw 0x51e8bbffffc669aa 0x007fffffffeee380

def z433 : W := mkw 0x0000000000000000 0x002a010410c00000

def z434 : W := mkw 0x80160400203b0370 0x00000000002e0380

def z435 : W := mkw 0x010810ec0004dc00 0x038ec2fc002efc00

def z436 : W := mkw 0x50088018668669aa 0xdffec3befeefefbb

def z437 : W := mkw 0x0000000000000000 0xfffe400000911c7f

def z438 : W := mkw 0x50088018668669aa 0x112a82baeeaeeba2

def z439 : W := mkw 0x0010040000390000 0x01800000003f0000

def z440 : W := mkw 0x0020232490400000 0x0000010410400000

def z441 : W := mkw 0x00e00813ddc00000 0xfc700003ffc0007f

def z442 : W := mkw 0x5118b7fc66bffdaa 0x57fefebaeeaeebaa

def z443 : W := mkw 0x0000000000000000 0x0001014511400000

def z444 : W := mkw 0x0000000000000000 0xa800000000111455

def z445 : W := mkw 0xd19ebffff6bffffa 0xd7fffffffebffffa

def z446 : W := mkw 0xd1febfffffff6bfa 0xd7ffffffffffebfa

def z447 : W := mkw 0x0000000000000000 0xffd5404101111c7f

def z448 : W := mkw 0x50088018668669aa 0x007ec2baeeaee380

def z449 : W := mkw 0x0008002c00044c00 0x0008003c00000c00

def z450 : W := mkw 0x011837ec003ddc00 0x03813d44003ffc00

def z451 : W := mkw 0x80962f0390390250 0xa8013d4511511455

def z452 : W := mkw 0x0008000800044800 0x03800000002ee800

def z453 : W := mkw 0x0000230000000000 0x0003ff0000000000

def z454 : W := mkw 0x01e03bf7ddc00000 0x57ffffffffc0082a

def z455 : W := mkw 0x0000000000000000 0xfc0000000000007f

def z456 : W := mkw 0x01e03bf7ddc00000 0x004cbefeefc00000

def z457 : W := mkw 0x51e8bbffffc669aa 0x0000bebaee2ee380

def z458 : W := mkw 0x01e03bf7ddc00000 0x002b3f7df1c00000

def z459 : W := mkw 0x0000000000000000 0x8001010110110050

def z460 : W := mkw 0x1118b7fc64bfdd22 0x13affffce0bffc22

def z461 : W := mkw 0x0000000000000000 0x9820000010c00033

def z462 : W := mkw 0x81963fe7b03b0370 0x85bffffff03f03f0

def z463 : W := mkw 0x016010f44dc00000 0x007f41fd1fc00000

def z464 : W := mkw 0x50088018668669aa 0xd7ffc3bbfebfebfa

def z465 : W := mkw 0x016810fc4dc4dc00 0x024c00fc0fc0fc00

def z466 : W := mkw 0x25dd3fef093dde44 0x238ffffd013ffc44

def z467 : W := mkw 0x65dd3fef0b3dfecc 0x038ffffe0e3fff80

def z468 : W := mkw 0x8012230090090010 0x8000010010010010

def z469 : W := mkw 0x65fd3fffdffdfecc 0x67ffffffffffffcc

def z470 : W := mkw 0x014010c009000000 0x004400c00f000000

def z471 : W := mkw 0x0000000000000000 0x2001004101101044

def z472 : W := mkw 0x65c53fe70b30b2cc 0x66dfffff0f30f3cc

def z473 : W := mkw 0xe4170400223bb3fc 0xe7800000003ff3fc

def z474 : W := mkw 0x01e03bf7ddc00000 0xfc7fffffffc0007f

def z475 : W := mkw 0x0020003444c00000 0x0008003c00c00000

def z476 : W := mkw 0x0018232c000d4c00 0x00000238000e0000

def z477 : W := mkw 0x011037e400399400 0xffff7d4511d11c7f

def z478 : W := mkw 0x80860c03b0320370 0x84b1fc03f03003f0

def z479 : W := mkw 0x00e02b37ddc00000 0x007a033fffc00000

def z480 : W := mkw 0x50008010668221aa 0x57fe4002ee800baa

def z481 : W := mkw 0x01e03bf7ddc00000 0x0033ffbbfe000000

def z482 : W := mkw 0x50088018668669aa 0x05b2c2baee2ee3a0

def z483 : W := mkw 0x016010e409400000 0x0000004401400000

def z484 : W := mkw 0x80162700203b0370 0x8583ff00003f03f0

def z485 : W := mkw 0x0000000020020120 0x04300002e00003a0

def z486 : W := mkw 0x81e63bf7fdc20370 0x847fffffffc003f0

def z487 : W := mkw 0x010033f444800000 0x007ffffeee800000

def z488 : W := mkw 0x50088018668669aa 0x46d4c2baee2ee388

def z489 : W := mkw 0x25d53fe709399644 0x20013d4501111444

def z490 : W := mkw 0xe5d73fc3bb3bb3fc 0xffffffc7ffffffff

def z491 : W := mkw 0x80962f0390390250 0x85b37d0110110070

def z492 : W := mkw 0x0000000020020120 0x00008202e02e0380

def z493 : W := mkw 0x00902f0390390000 0x01b3ff03f03f0000

def z494 : W := mkw 0x75c59cd36fb2b3ee 0x76f5fcc3efb0f3ee

def z495 : W := mkw 0x00802b0390000000 0x00013d0110000000

def z496 : W := mkw 0x5088ab1bf68669aa 0x57ffffbbfeaeebaa

def z497 : W := mkw 0x2405040000309244 0x2000000000101044

def z498 : W := mkw 0x0000000020020120 0x01220200e00e0020

def z499 : W := mkw 0x25e53ff7ddf09244 0x207fffffffd01044

def z500 : W := mkw 0x010033e400000000 0x038ffffc00111c00

def z501 : W := mkw 0x0000000000000000 0x668000000010104c

def z502 : W := mkw 0x500880184684688a 0x56dcc0ba0ea0eb8a

def z503 : W := mkw 0x4000000002002088 0x000080820e20e380

def z504 : W := mkw 0x656110f44fc0b08c 0x624c00fc0fc0f00c

def z505 : W := mkw 0x81f63ff7ddf90250 0x807fffffffd10050

def z506 : W := mkw 0x00942f0300390240 0x0593ff03003f03c0

def z507 : W := mkw 0x809e2f2fb03f4f70 0x85bbff3ff03f0ff0

def z508 : W := mkw 0x80962f03b03b0370 0x0491fe03e03e03c0

def z509 : W := mkw 0xe4972f03b23bb3fc 0xe7b3ff03f03ff3fc

def z510 : W := mkw 0x0000000000000000 0x0285404000101000

def z511 : W := mkw 0xd01e841866bf6bfa 0xd7fec2baeebfebfa

def z512 : W := mkw 0x0000000000000000 0xfc71014511d1147f

def z513 : W := mkw 0x81963fe7b03b9770 0x85b3ff47f03f17f0

def z514 : W := mkw 0x81f63fe7b97b0370 0x85b3ff47f17f03f0

def z515 : W := mkw 0x651d37ec023dfecc 0x678ffffc003fffcc

def z516 : W := mkw 0x01e43ff7ddf00240 0x04fffffffff003c0

def z517 : W := mkw 0x0000000000000000 0x000f414400000000

def z518 : W := mkw 0xe5f73ff7fffbb3fc 0xe7fffffffffff3fc

def z519 : W := mkw 0x40000000220221a8 0x47f6c282ee2ee3a8

def z520 : W := mkw 0x0000000000000000 0x7840000001c0000f

def z521 : W := mkw 0x655937ec0b3dfc8c 0x63cffffc0f3ffc0c

def z522 : W := mkw 0x0000000000000000 0x547000000080002a

def z523 : W := mkw 0x011814ec003ddc00 0x038c00fc003ffc00

def z524 : W := mkw 0x00802b0390000000 0x85b3ff03f0110070

def z525 : W := mkw 0x740d841866b6fbee 0x77fec2baeebefbee

def z526 : W := mkw 0x0000000000000000 0x9dbb410510d10c73

def z527 : W := mkw 0x0000000000000000 0x0284c0800020e000

def z528 : W := mkw 0x50088018668669aa 0x524c82baeeaeeb8a

def z529 : W := mkw 0x010033e400000000 0xfffffffd11d11c7f

def z530 : W := mkw 0x00a02b37d4c00000 0x003bff3ff0c00000

def z531 : W := mkw 0x1008801864864922 0x15bac23ae0ae0ba2

def z532 : W := mkw 0x01e83bffddc4dc00 0x027fffffffc0fc00

def z533 : W := mkw 0x0000000000000000 0x0033410110000000

def z534 : W := mkw 0x4000000002002088 0xffffc1c71ff1ffff

def z535 : W := mkw 0x0080080390000000 0x00300003f0000000

def z536 : W := mkw 0x0000000000000000 0xfb6e014411c11c3f

def z537 : W := mkw 0x65c51cc32b32b3ec 0x67f7fec3ef3ef3ec

def z538 : W := mkw 0x65e53bf7dfc022cc 0x647fffffffc003cc

def z539 : W := mkw 0x65dd1ccb0b3dfecc 0x67d5fcc30f3fffcc

def z540 : W := mkw 0x65c51cc30b30b2cc 0x64513c430f1013cc

def z541 : W := mkw 0x01c41cc309300240 0x04d5fcc30f3003c0

def z542 : W := mkw 0x0084080300000240 0x04100003000003c0

def z543 : W := mkw 0x8016040000390250 0x8000000000110050

def z544 : W := mkw 0x011037e400399400 0xa8013d4511511455

def z545 : W := mkw 0x25e53fe799709244 0x20013d4511501044

def z546 : W := mkw 0x016010f44dc00000 0x7a4c00fc0fc01c0f

def z547 : W := mkw 0x65e53ff7dff0b2cc 0x66d5fefbef30f3cc

def z548 : W := mkw 0x65e51cf74ff0b2cc 0x66ddfcff0ff0f3cc

def z549 : W := mkw 0x00e0080399400000 0x0000000111400000

def z550 : W := mkw 0x0018232c000d4c00 0xffff437d11df1c7f

def z551 : W := mkw 0x754990d84f84f88e 0x724c00f80f80f80e

def z552 : W := mkw 0x65dd3fef0b3dfecc 0x66d5fefb0f3ef3cc

def z553 : W := mkw 0x00840c0320320360 0x05b3fe03e03e03e0

def z554 : W := mkw 0x65c518c30b00b2cc 0x665400c30f00f3cc

def z555 : W := mkw 0x01c018c309000000 0x00013c4101000000

def z556 : W := mkw 0x65c51cc30b30b2cc 0x7eddfcc70ff0ffcf

def z557 : W := mkw 0x00200010d4c00000 0x00200000f0c00000

def z558 : W := mkw 0x0008000800044800 0x57fec2b800aee82a

def z559 : W := mkw 0x010010c000009000 0x020400c00000f000

def z560 : W := mkw 0x0010232400090400 0x0000010400010400

def z561 : W := mkw 0x0000000000000000 0x0183410000110000

def z562 : W := mkw 0x4000000002002088 0x66d5c0c30f30f3cc

def z563 : W := mkw 0x65c51cc30b30b2cc 0x0055fcc30f20e380

def z564 : W := mkw 0x80122300b00b0130 0x85b34301f01f0070

def z565 : W := mkw 0x65c518c30b0022cc 0x6455fcc30f0003cc

def z566 : W := mkw 0x01e018d3ddc00000 0x0075fcc3ffc00000

def z567 : W := mkw 0x80e60813fdc20370 0x84700003ffc003f0

def z568 : W := mkw 0x01e03be799400000 0xffff7d4511d11c7f

def z569 : W := mkw 0x0000000000000000 0x7a00000000001c0f

def z570 : W := mkw 0x65c51cd34fb0b2cc 0x66fffefbefb0f3cc

def z571 : W := mkw 0x80962f03b03b0370 0x0183ff02e03f0380

def z572 : W := mkw 0x1008801864864922 0x992a033cf0cf0c33

def z573 : W := mkw 0x0000000000000000 0x7edd404501d01c4f

def z574 : W := mkw 0x50088018668669aa 0x57ffc3ffffeeebaa

def z575 : W := mkw 0x00802b0390000000 0xffffff47f1d11c7f

def z576 : W := mkw 0x011037e400399400 0x000ffffc00111400

def z577 : W := mkw 0x01d83fef093ddc00 0x03dfffff0f3ffc00

def z578 : W := mkw 0x011037c000399000 0x0387ffc0003ff000

def z579 : W := mkw 0x0008000820064920 0x07bec2bae02eeba0

def z580 : W := mkw 0x81d63fc3b93b0370 0x85f7ffc3ff3f03f0

def z581 : W := mkw 0x640100000200b08c 0x620000000000f00c

def z582 : W := mkw 0x0000232400000000 0x000a033c00000000

def z583 : W := mkw 0x010833ec0004dc00 0x020ffffc0000fc00

def z584 : W := mkw 0x5108b3fc668669aa 0x57fffffeeeaeebaa

def z585 : W := mkw 0x0010270000390000 0x00013d0000110000

def z586 : W := mkw 0x00840c0300300240 0x85b3fd03103103f0

def z587 : W := mkw 0x65c51cc30b30b2cc 0x0491fc830e30e3c0

def z588 : W := mkw 0x64850c030230b2cc 0x6691fc030030f3cc

def z589 : W := mkw 0x019c3fef003dde40 0x079fffff003fffc0

def z590 : W := mkw 0x01e03bf7ddc00000 0x004d3dfd1fc00000

def z591 : W := mkw 0x0000000000000000 0xe7f741411111107c

def z592 : W := mkw 0x80960c03203b0370 0x8591fc03003f03f0

def z593 : W := mkw 0x00e00813ddc00000 0x007f4147ffc00000

def z594 : W := mkw 0x010810ec0004dc00 0xffff41fd11d1fc7f

def z595 : W := mkw 0x500880184684688a 0x57fe40b80e80e82a

def z596 : W := mkw 0x01f03ff7ddf99400 0x007fffffffd11400

def z597 : W := mkw 0x25c51cc309309244 0x2055fcc30f101044

def z598 : W := mkw 0x011833ec000d4c00 0x010ffffc000f0c00

def z599 : W := mkw 0x80962f03b03b0370 0x85813d01103f03f0

def z600 : W := mkw 0x81f23bf7fdcb0130 0x817fffffffcf0030

def z601 : W := mkw 0x50088018668669aa 0x578082baee2eebaa

def z602 : W := mkw 0x80962f03b03b0370 0xffb3ff03f03f1fff

def z603 : W := mkw 0x0000000000000000 0x8580000000110070

def z604 : W := mkw 0x0000000000000000 0x004c004401c00000

def z605 : W := mkw 0x25c51cc309309244 0x2285fcc10130f044

def z606 : W := mkw 0x654110c00b00b08c 0x66d4c0c20f20f38c

def z607 : W := mkw 0x00182708003ddc00 0x0383ff00003ffc00

def z608 : W := mkw 0x01e018f74dc00000 0x005dfcff0fc00000

def z609 : W := mkw 0x65e13bf7dfc0b08c 0x627fffffffc0f00c

def z610 : W := mkw 0xe5c71cc3bb32b3fc 0xe6f5fcc3ff30f3fc

def z611 : W := mkw 0x65e53fe79b70b2cc 0x66d5fdc71f70f3cc

def z612 : W := mkw 0x0000000000000000 0x9900000000010c33

def z613 : W := mkw 0x4000000002002088 0x424400800e00e008

def z614 : W := mkw 0x0000040000300000 0x0081fc0000300000

def z615 : W := mkw 0x65c51cc30b30b2cc 0x62453cc10f10f04c

def z616 : W := mkw 0x01e03bf7ddc00000 0x00713d47ffc00000

def z617 : W := mkw 0x0000000000000000 0xb92b014511d11c77

def z618 : W := mkw 0x51c898db6f8669aa 0x57fffefbefaeebaa

def z619 : W := mkw 0x80962f03b03b0370 0x87bfff47f03f1ff0

def z620 : W := mkw 0xe5d71cc32b3bb3fc 0xe7d5fcc30f3ff3fc

def z621 : W := mkw 0x254110c009009004 0x2000004001001004

def z622 : W := mkw 0xa5d73fc399399254 0xa0013d4111111054

def z623 : W := mkw 0x0000000000000000 0x0070000111c00000

def z624 : W := mkw 0x1008801844844802 0x1008003800800802

def z625 : W := mkw 0x80122300b00b0130 0xffff4345f1df1c7f

def z626 : W := mkw 0x50088018668669aa 0x536e02b8ee8ee82a

def z627 : W := mkw 0x0000000000000000 0x112a000000800822

def z628 : W := mkw 0x65c51cc30b30b2cc 0xe7f7fdc31f31f3fc

def z629 : W := mkw 0x0010040000399400 0x0000000000111400

def z630 : W := mkw 0x0000000000000000 0xfffe400111c0087f

def z631 : W := mkw 0x01983fef903ddc00 0x03bffffff03ffc00

def z632 : W := mkw 0x0000000000000000 0xa800000111400055

def z633 : W := mkw 0x0000000000000000 0xffaa010410d11c7f

def z634 : W := mkw 0x017837fc4dfddc00 0x03cffffc0ffffc00

def z635 : W := mkw 0x011837ec203fdd20 0x07bffffee03fffa0

def z636 : W := mkw 0x65c53fc39b30b2cc 0x66f7ffc3ff30f3cc

def z637 : W := mkw 0x0000000000000000 0x8430000110000070

def z638 : W := mkw 0x510894d866b6f9aa 0x57fffefaeebefbaa

def z639 : W := mkw 0x01f03fe799799400 0x00013d4511511400

def z640 : W := mkw 0x000800080004dc00 0x020000000000fc00

def z641 : W := mkw 0x0000000000000000 0x9baf414410d11c33

def z642 : W := mkw 0x0018232c000d4c00 0x038ec3bc002fec00

def z643 : W := mkw 0x50088008220669aa 0x57b2c202e02eebaa

def z644 : W := mkw 0x0000000000000000 0xff81014511511c7f

def z645 : W := mkw 0x0000000000000000 0x0380000000111c00

def z646 : W := mkw 0x011837ec003ddc00 0x0380beb8003ffc00

def z647 : W := mkw 0x510890fc6686fdaa 0x57fec2feeeaeffaa

def z648 : W := mkw 0x0000000000000000 0x010a010400010c00

def z649 : W := mkw 0x00180008000d4c00 0x01000000000f0c00

def z650 : W := mkw 0x00840c0300300240 0xfffffd4711f11fff

def z651 : W := mkw 0x0000000000000000 0x578000000000082a

def z652 : W := mkw 0x8086080390000250 0x8000000110000050

def z653 : W := mkw 0x50088018668669aa 0xfffec2baeebfffff

def z654 : W := mkw 0x0000000000000000 0xfa4d014511d11c5f

def z655 : W := mkw 0xd01aa318f68f69ba 0xd7fec3bafeafebba

def z656 : W := mkw 0x0000000000000000 0x020c004400001c00

def z657 : W := mkw 0x50088008220669aa 0xffff414511ffffff

def z658 : W := mkw 0xd09eaf1bf6bf6bfa 0x0000bebaee2ee380

def z659 : W := mkw 0x80020000b0020130 0x80200000f0000030

def z660 : W := mkw 0x0000000000000000 0xa87f414511d11455

def z661 : W := mkw 0x650514c00230b2cc 0x6685fcc00030f3cc

def z662 : W := mkw 0x65d53fe70b39b6cc 0x66d5fdc70f31f7cc

def z663 : W := mkw 0x00e00813ddc00000 0xffff4147ffd11c7f

def z664 : W := mkw 0x0000000000000000 0x524c00000080080a

def z665 : W := mkw 0x0000001064820120 0x05fec2baeeae03a0

def z666 : W := mkw 0x0000000000000000 0xfc7f414511c0007f

def z667 : W := mkw 0x00182708003d4800 0x038fffb8003fe800

def z668 : W := mkw 0x0000000000000000 0x007e400000800000

def z669 : W := mkw 0x641d0408023dfecc 0x67800000003fffcc

def z670 : W := mkw 0x65c51cc30b30b2cc 0x66813c410130f3cc

def z671 : W := mkw 0x0000000000000000 0x645000010100004c

def z672 : W := mkw 0xe5d73fc39b39b2dc 0xe6d5fdc31f31f3dc

def z673 : W := mkw 0x5118b7ec223ffdaa 0x578ffffc003fffaa

def z674 : W := mkw 0x0000000000000000 0x0055404101000000

def z675 : W := mkw 0x01f83fef997ddc00 0x038ffffd117ffc00

def z676 : W := mkw 0x510890fc4684fc8a 0x524c00fc0e80fc0a

def z677 : W := mkw 0x011837fc44bddc00 0x03fffffeeebffc00

def z678 : W := mkw 0xe4d72f03bb3b23fc 0xe5f3ff03ff3f03fc

def z679 : W := mkw 0x75edbffffff6fbee 0x77fffffffffefbee

def z680 : W := mkw 0x00202334d4c00000 0xffff437df1d11c7f

def z681 : W := mkw 0x80122300b00b0130 0x85b2c302f02f03b0

def z682 : W := mkw 0x64050000020022cc 0x64000000000003cc

def z683 : W := mkw 0x013837fcd4fddc00 0x03affffcf0fffc00

def z684 : W := mkw 0x654110c00b00b08c 0xffff41c51fd1fc7f

def z685 : W := mkw 0x0000000000000000 0xff8f414400111c7f

def z686 : W := mkw 0x0000000000000000 0x0182c200002e0000

def z687 : W := mkw 0x65e51cd3dff0b2cc 0x66f5fcc3fff0f3cc

def z688 : W := mkw 0x01c03be709000000 0x005fffff0f000000

def z689 : W := mkw 0x4000001046802088 0x46fec2baeea0e388

def z690 : W := mkw 0x0010270000390000 0xffffff4511ff1c7f

def z691 : W := mkw 0x500880184684688a 0x527ec2baee80e80a

def z692 : W := mkw 0x016010f44dc00000 0xffff41fd1fd11c7f

def z693 : W := mkw 0x80962f0390390250 0x8491fd03103103d0

def z694 : W := mkw 0x01e03be799400000 0x000ffffd11400000

def z695 : W := mkw 0x50008010668221aa 0x56f4c082eea0e3aa

def z696 : W := mkw 0x0000000000000000 0x66ff414511d0104c

def z697 : W := mkw 0x0000000000000000 0xadb3414511511475

def z698 : W := mkw 0x011837ec003ddc00 0x020d3dfc0011fc00

def z699 : W := mkw 0x00c0080309000000 0x005000030f000000

def z700 : W := mkw 0x0008000800044800 0x020c00b80000e800

def z701 : W := mkw 0x0000230090000000 0x00220300f0000000

def z702 : W := mkw 0xf5dfbfdbffbffbfe 0xf7fffffbffbffbfe

def z703 : W := mkw 0x0000000000000000 0xfdf3410111d1007f

def z704 : W := mkw 0x01c03bc399000000 0x0077ffc3ff000000

def z705 : W := mkw 0x0000001044800000 0x00700002ee800000

def z706 : W := mkw 0x01e018f7ddc00000 0x007c00ffffc00000

def z707 : W := mkw 0x010033f444800000 0x007fffffffc00000

def z708 : W := mkw 0x754990d84f84f88e 0x000000b80e00e000

def z709 : W := mkw 0x50088018668669aa 0x7fffc3feefffffaf

def z710 : W := mkw 0x65c51ce70b30b6cc 0x66d5fcc70f30f7cc

def z711 : W := mkw 0x510890d84684f88a 0x524c00f80e80f80a

def z712 : W := mkw 0x011837ec003ddc00 0x000ffffc003ff400

def z713 : W := mkw 0x011837ec003ddc00 0x018bffbc003fec00

def z714 : W := mkw 0x65c51cc30b30b2cc 0x46d5fcc30f20e388

def z715 : W := mkw 0x50188408223ffdaa 0xffff414511ffffff

def z716 : W := mkw 0xe55333c0bb0bb1bc 0xe36603c0ff0ff03c

def z717 : W := mkw 0x50e08813ffc221aa 0xfc700003ffc003ff

def z718 : W := mkw 0x01e03bf7ddc00000 0x007b3f7fffc00000

def z719 : W := mkw 0x01e03bf7ddc00000 0x0033ffffff400000

def z720 : W := mkw 0x40840c03023022c8 0xd7fffd831eb1ebfa

def z721 : W := mkw 0x00182708003d4800 0x0183ffb8003fe000

def z722 : W := mkw 0x80962f03b03b0370 0x8400be02e02e03f0

def z723 : W := mkw 0x00802b13d4800000 0xd7ffffbbfe91087a

def z724 : W := mkw 0x65c51cc30b30b2cc 0xe7d5fcc30f31f3fc

def z725 : W := mkw 0x901aa318f48f4932 0x112a0238e08e0822

def z726 : W := mkw 0x65c51cc30b30b2cc 0x0280bc820e30f380

def z727 : W := mkw 0x64252734d6f0b2cc 0x66aa033cf0f0f3cc

def z728 : W := mkw 0x01e03bf7ddc00000 0x005dfeffefc00000

def z729 : W := mkw 0x80962f03b03b0370 0x007fff47f1ee0380

def z730 : W := mkw 0x50e08813ffc221aa 0x54700002ee8003aa

def z731 : W := mkw 0x80962f03b03b0370 0x8491ff03f03f03d0

def z732 : W := mkw 0x011837ec003ddc00 0xfbeffffc11fffc3f

def z733 : W := mkw 0x50188408223ffdaa 0x57800000002eebaa

def z734 : W := mkw 0x80962f03b03b0370 0x85ffff03f0bf03f0

def z735 : W := mkw 0x00e02b13ddc00000 0x007fffbbffc00000

def z736 : W := mkw 0x80b62f27b07b0370 0x85b3ff07f07f03f0

def z737 : W := mkw 0x80962f03b03b0370 0x0480be02e03e03c0

def z738 : W := mkw 0xd01e8408223f6bfa 0xff800000003fffff

def z739 : W := mkw 0x50088018668669aa 0xdffec2bafeeeebbb

def z740 : W := mkw 0x50088018668669aa 0x57cc82baeeaeebaa

def z741 : W := mkw 0x65c51cc30b30b2cc 0x66d5fdc71f70f3cc

def z742 : W := mkw 0x516890fc4fc4688a 0x004c00fc0fc0e000

def z743 : W := mkw 0x74c588136f8223ee 0x54700002ee8003aa

def z744 : W := mkw 0x50088018668669aa 0x468082baee2ee388

def z745 : W := mkw 0x00102700203b0120 0x85b3ff03f03f03f0

def z746 : W := mkw 0x015837ec093ddc00 0x03cffffc0f3ffc00

def z747 : W := mkw 0x40840c03023022c8 0x0000bc820e20e380

def z748 : W := mkw 0x00840c0320320360 0x05b2fe02e02e03a0

def z749 : W := mkw 0x0000000000000000 0xfd7b014511d11c7f

def z750 : W := mkw 0x50088018668669aa 0xfffec3bfffefefff

def z751 : W := mkw 0x80962f03b03b0370 0x8583ff02e03f03f0

def z752 : W := mkw 0x011837ec003ddc00 0xfc70beb911eee07f

def z753 : W := mkw 0x65c51cc30b30b2cc 0x7ed5fcc30ff0f3cf

def z754 : W := mkw 0x80962f03b03b0370 0x0003ff02e02e0380

def z755 : W := mkw 0x0000230020020120 0x05b3ff02e02e03a0

def z756 : W := mkw 0x818e18efb006df70 0x863c00fff000fff0

def z757 : W := mkw 0xd0868813f68223fa 0x00000002ee000380

def z758 : W := mkw 0x1008a33c64864922 0x112a033ce08e0822

def z759 : W := mkw 0x80962f03b03b0370 0xd7ffff47f1ff0bfa

def z760 : W := mkw 0x01e03bf7ddc00000 0x0054febaee000000

def z761 : W := mkw 0x011837ec003ddc00 0x030f3ffc001ffc00

def z762 : W := mkw 0x010814c80034d800 0x038efeb8002ee800

def z763 : W := mkw 0x510890fc4684fc8a 0x7a4c00fc0fc0fc0f

def z764 : W := mkw 0x65c51cc30b30b2cc 0x6691fc830e30f3cc

def z765 : W := mkw 0x740d84082236fbee 0x57800000002eebaa

def z766 : W := mkw 0x74c588136f8223ee 0xfc700003ffc003ff

def z767 : W := mkw 0x01c018d34d800000 0x0055fefbef000000

def z768 : W := mkw 0x00102700203b0120 0x57ffff46e0bf1faa

def z769 : W := mkw 0x01e03bf7ddc00000 0xff80bebaee111c7f

def z770 : W := mkw 0x00802b03b0020120 0x85b3ff03f03f03f0

def z771 : W := mkw 0x0008001864864920 0x07fec2baeeaeeba0

def z772 : W := mkw 0x50088018668669aa 0x0054c2baee2ee380

def z773 : W := mkw 0x74c588136f8223ee 0x77ff4043ef901bee

def z774 : W := mkw 0x50088018668669aa 0xffffc2fbfffefbff

def z775 : W := mkw 0x35cd9cdb6db6db66 0x312b3e79e19e1866

def z776 : W := mkw 0x50088018668669aa 0x46fec2baeeaee388

def z777 : W := mkw 0x011837ec003ddc00 0x018ffffc003fe000

def z778 : W := mkw 0x01e03bf7ddc00000 0x7bffffffffd11c0f

def z779 : W := mkw 0x01e03bf7ddc00000 0x003bffbffec00000

def z780 : W := mkw 0x01e018f7ddc00000 0x007dfcffffc00000

def z781 : W := mkw 0x50088018668669aa 0x043082baee2ee3a0

def z782 : W := mkw 0x65c51cc30b30b2cc 0xfeddfdc71ff1ffdf

def z783 : W := mkw 0x010833ec00044800 0x57fffffd11eee82a

def z784 : W := mkw 0x01e03bf7ddc00000 0x207fffffffd01044

def z785 : W := mkw 0x011837ec003ddc00 0x0180beb8003fe000

def z786 : W := mkw 0x011837ec003ddc00 0x85b3ffb9103fe070

def z787 : W := mkw 0x80962f03b03b0370 0x9dffff47f1ff0ff3

def z788 : W := mkw 0x80962f03b03b0370 0xe7b3ff03f03f13fc

def z789 : W := mkw 0x80962f03b03b0370 0x0081fe02e03e0380

def z790 : W := mkw 0x01e03bf7ddc00000 0x0001befbef000000

def z791 : W := mkw 0x00840c0320320360 0xffffff47f1ff1fff

def z792 : W := mkw 0x011837ec003ddc00 0x0381bffc003ffc00

def z793 : W := mkw 0x01e03bf7ddc00000 0x027fffffffc01c00

def z794 : W := mkw 0x00f80c1bddfddc00 0x03f00003fffffc00

def z795 : W := mkw 0x50188408223ffdaa 0xff800000003fffff

def z796 : W := mkw 0x011837ec003ddc00 0x2b8ffffc017ffc05

def z797 : W := mkw 0x65c51cc30b30b2cc 0x67d7fec30f3ef3cc

def z798 : W := mkw 0x1028a33cf4c64922 0xffff437df1df1c7f

def z799 : W := mkw 0x01e03bf7ddc00000 0x0075fefbffc00000

def z800 : W := mkw 0xe4e70813ffc223fc 0xe4700003ffc003fc

def z801 : W := mkw 0x65c51cc30b30b2cc 0xffd5fdc71f71ffff

def z802 : W := mkw 0x011837ec903ddc00 0x03affffcf03ffc00

def z803 : W := mkw 0x251d37ec003dde44 0x238ffffc003ffc44

def z804 : W := mkw 0x50088018668669aa 0xfffec2bbffffffff

def z805 : W := mkw 0x65c51cc30b30b2cc 0xeefffdc71ff1f7dd

def z806 : W := mkw 0x5110b7f466bbb5aa 0x54713d46ee9117aa

def z807 : W := mkw 0x50088018668669aa 0x56f4c2baeeaee3aa

def z808 : W := mkw 0x010814c80034d800 0x038ffffc003ffc00

def z809 : W := mkw 0x01e03bf7ddc00000 0x7a4cbefeefc01c0f

def z810 : W := mkw 0x01e03bf7ddc00000 0x527fffffffc0080a

def z811 : W := mkw 0x50088018668669aa 0x57fec3befeeeebaa

def z812 : W := mkw 0x011837ec003ddc00 0x0001bef8003ef000

def z813 : W := mkw 0x817614f46dfb0370 0x85cc00fc0fff03f0

def z814 : W := mkw 0x01e03bf7ddc00000 0x0071bfffffc00000

def z815 : W := mkw 0x510890fc4684fc8a 0x524c00b80e80e80a

def z816 : W := mkw 0x01e03bf7ddc00000 0x05ffffffffc00020

def z817 : W := mkw 0x01803bf7d4800000 0x007ffffffe800000

def z818 : W := mkw 0x80962f03b03b0370 0x85f7ff83fe3f03f0

def z819 : W := mkw 0x010833ec00044800 0x038ffffc003ffc00

def z820 : W := mkw 0x65c51cc30b30b2cc 0x46d5fc830e30e3c8

def z821 : W := mkw 0xd01e8408223f6bfa 0x85800000003fe3f0

def z822 : W := mkw 0x410014c00230b088 0x66d5fcc30f30f3cc

def z823 : W := mkw 0x01c03be799000000 0x007fffffff000000

def z824 : W := mkw 0x80962f03b03b0370 0xadb3ff03f03f17f5

def z825 : W := mkw 0x010814c80034d800 0xfffffffd11fffc7f

def z826 : W := mkw 0x65c51cc30b30b2cc 0x0480bc820e30e3c0

def z827 : W := mkw 0x65c51cc30b30b2cc 0xeff7fdc71f71f7fd

def z828 : W := mkw 0x65c51cc30b30b2cc 0x66c4bcc20f30f3cc

def z829 : W := mkw 0x50088018668669aa 0xff8082baee3fffff

def z830 : W := mkw 0x01e03bf7ddc00000 0x000efebaee000000

def z831 : W := mkw 0x50088018668669aa 0xd7ffc3ffffffebfa

def z832 : W := mkw 0x011837ec003ddc00 0x87fffffd11fffc70

def z833 : W := mkw 0x011837ec003ddc00 0x010ffffc002fec00

def z834 : W := mkw 0x01e03bf7ddc00000 0x007fffffffd11400

def z835 : W := mkw 0x25e53bf7ddc00244 0x207fffffffc00044

def z836 : W := mkw 0x011837ec003ddc00 0xffdffffd013ffc7f

def z837 : W := mkw 0x80962f03b03b0370 0x8431bf03f03f03f0

def z838 : W := mkw 0x80962f03b03b0370 0xffb3ff47f17f1fff

def z839 : W := mkw 0x010833ec00044800 0x0000beb8002ee000

def z840 : W := mkw 0x65c51cc30b30b2cc 0x6ed5fcc70f70f7cd

def z841 : W := mkw 0x50088018668669aa 0xdfffc3fefeffffbb

def z842 : W := mkw 0x011837ec003ddc00 0x03affffc10fffc00

def z843 : W := mkw 0x011837ec003ddc00 0x678ffffc003ffc4c

def z844 : W := mkw 0x01e03bf7ddc00000 0x000abfbeee000000

def z845 : W := mkw 0x50088018668669aa 0x57f082baeeaeebaa

def z846 : W := mkw 0x50088018668669aa 0x77ffc3fffffefbee

def z847 : W := mkw 0x40840c03023022c8 0x0491fc830e30e3c0

def z848 : W := mkw 0x01e03bf7ddc00000 0x02ffffffffd01000

def z849 : W := mkw 0x80962f03b03b0370 0x0490fe02e02e0380

def z850 : W := mkw 0x740d84082236fbee 0x77ff404101befbee

def z851 : W := mkw 0x51e8bbefbb4669aa 0x57813d45116eebaa

def z852 : W := mkw 0x011837ec003ddc00 0x7b8ffffc003ffc0f

def z853 : W := mkw 0x01c018d34d800000 0x0000bebaee000000

def z854 : W := mkw 0x01e03bf7ddc00000 0x007effbefec00000

def z855 : W := mkw 0x80962f03b03b0370 0xbdbbff47f1ff1ff7

def z856 : W := mkw 0x010010d044800000 0x007ffefaee800000

def z857 : W := mkw 0x510890fc4684688a 0x524c00fc0e80e80a

def z858 : W := mkw 0x754990d84f84f88e 0xffff41fd1fd1fc7f

def z859 : W := mkw 0x00840c0320320360 0x85b3ff03f03f03f0

def z860 : W := mkw 0x510890fc4684fc8a 0x020c00fc0e00fc00

def z861 : W := mkw 0x64dd2b2f0b0d6ecc 0x655a033f0f0f0fcc

def z862 : W := mkw 0x50088018668669aa 0xa80183ffff7ff7d5

def z863 : W := mkw 0x80962f03b03b0370 0x8000bf02f02f0390

def z864 : W := mkw 0x65c51cc30b30b2cc 0xfed5fcc30f30f3ff

def z865 : W := mkw 0x65e51cc39b70b2cc 0x66d5fcc31f70f3cc

def z866 : W := mkw 0x01e03bf7ddc00000 0x0044befaef000000

def z867 : W := mkw 0x1018a33c648f4d22 0x992a033cf0cf0c33

def z868 : W := mkw 0x50088018668669aa 0x77fec2bbefaeebee

def z869 : W := mkw 0x40840c03023022c8 0x46d4fc820e20e388

def z870 : W := mkw 0x00182708003d4800 0xd7ffffb910bfe87a

def z871 : W := mkw 0x74c588136f8223ee 0x64500003ef0003cc

def z872 : W := mkw 0x50088018668669aa 0xffffc3bbffffebff

def z873 : W := mkw 0x011833ec000d4c00 0x038ffffc002fec00

def z874 : W := mkw 0x011837ec003ddc00 0xe7fffffd113ffc7c

def z875 : W := mkw 0x50088018668669aa 0x53cec2baeeaeeb8a

def z876 : W := mkw 0x901aa318f48f4932 0x992a033cf0cf0c33

def z877 : W := mkw 0x00840c0320320360 0x0000be02e02e0380

def z878 : W := mkw 0x901aa318f48f4932 0x81220338f00f0030

def z879 : W := mkw 0x80962f03b03b0370 0x0001bf03f02e0380

def z880 : W := mkw 0x50088018668669aa 0x7ffec2baeeaeffaf

def z881 : W := mkw 0x50088018668669aa 0x110082baee2eeba2

def z882 : W := mkw 0x74c588136f8223ee 0x00000002ee000380

def z883 : W := mkw 0x80962f03b03b0370 0x66d5fe43e13e13cc

def z884 : W := mkw 0x80962f03b03b0370 0xffbbff07f0ff1fff

def z885 : W := mkw 0x41c018c30b002088 0x46d4fc820e20e388

def z886 : W := mkw 0x00182708003d4800 0x038ffffc003ffc00

def z887 : W := mkw 0x65c51cc30b30b2cc 0x66c53cc10f30f3cc

def z888 : W := mkw 0x0000000000000000 0xffcd014511d11c7f

def z889 : W := mkw 0x65c118c30b00b08c 0x66d5fcc30f20f38c

def z890 : W := mkw 0x01e03bf7ddc00000 0x002bbfffffc00000

def z891 : W := mkw 0x65c51cc30b30b2cc 0xe6d5fdc31f31f3dc

def z892 : W := mkw 0x011837ec003ddc00 0xd7fffffd10bffc7a

def z893 : W := mkw 0x011837ec003ddc00 0x13affffc00bffc22

def z894 : W := mkw 0x01e03bf7ddc00000 0xfd7fffffffc10c7f

def z895 : W := mkw 0x01c018d34d800000 0x007efebaee800000

def z896 : W := mkw 0x00802b13d4800000 0x0033ffbbfe000000

def z897 : W := mkw 0x0000000000000000 0xffab014511d11c7f

def z898 : W := mkw 0x410014c00230b088 0x0000bc820e20e380

def z899 : W := mkw 0x01e03bf7ddc00000 0xffffffffffc0087f

def z900 : W := mkw 0xd09eaf1bd6bd6ada 0xd24d3db91e91e85a

def z901 : W := mkw 0x011837ec003ddc00 0x238ffffd013ffc44

def z902 : W := mkw 0x012033f4d4c00000 0x007ffffefec00000

def z903 : W := mkw 0x65c51cc30b30b2cc 0xfc70bc831fe0e3ff

def z904 : W := mkw 0x010033f444800000 0x000ffffeee000000

def z905 : W := mkw 0x50088018668669aa 0xffffc2fbefbfffff

def z906 : W := mkw 0x50088018668669aa 0xfffec3feffefffbf

def z907 : W := mkw 0x011837ec003ddc00 0x578ffffc003ffc2a

def z908 : W := mkw 0x50088018668669aa 0x57ffc3feeeaeebaa

def z909 : W := mkw 0x65e51ce70b70b2cc 0x66d5fcc70f70f3cc

def z910 : W := mkw 0x65c51cc30b30b2cc 0x64d1fc830f30e3cc

def z911 : W := mkw 0x0000000000000000 0xfe7d014511d11c7f

def z912 : W := mkw 0x80962f03b03b0370 0xafbfff47f17f1ff5

def z913 : W := mkw 0x011837ec003ddc00 0x038ffffd117ffc00

def z914 : W := mkw 0x65c51cc30b30b2cc 0x992abd861ee1efb3

def z915 : W := mkw 0x01e03bf7ddc00000 0x0022bfbafe000000

def z916 : W := mkw 0x50088018668669aa 0x117ec2baeeaeeba2

def z917 : W := mkw 0xf4c78813ff8223fe 0xf4700003ff8003fe

def z918 : W := mkw 0x011837ec003ddc00 0x03dffffe0e3ffc00

def z919 : W := mkw 0x0000000000000000 0xfb6f014511d11c7f

def z920 : W := mkw 0x516890fc4fc4688a 0xffff41fd1fd1fc7f

def z921 : W := mkw 0x50088018668669aa 0x0032c2baee2ee380

def z922 : W := mkw 0x50088018668669aa 0x567c82baeeaeebaa

def z923 : W := mkw 0x4000040002302088 0x46d5fc820e30e388

def z924 : W := mkw 0x80962f03b03b0370 0x8000be02e03f03d0

def z925 : W := mkw 0x01e03bf7ddc00000 0x004cbebaee800000

def z926 : W := mkw 0x011837ec003ddc00 0x0280beb8003ef000

def z927 : W := mkw 0x01e03bf7ddc00000 0xadffffffffd11475

def z928 : W := mkw 0xd0868813f68223fa 0x84300003fe0003f0

def z929 : W := mkw 0x011837ec003ddc00 0x07bffffc003ffc20

def z930 : W := mkw 0x4008001846846888 0x47fec2baeeaeeb88

def z931 : W := mkw 0x80962f03b03b0370 0x05b3ff03f02e03a0

def z932 : W := mkw 0x0008040800344800 0x038ffeb8003ee800

def z933 : W := mkw 0x654114c00b30b08c 0x66d5fcc20f30f38c

def z934 : W := mkw 0x516890fc4fc4688a 0x7a4c00fc0fc0fc0f

def z935 : W := mkw 0x50e08813ffc221aa 0x00700003ffc00380

def z936 : W := mkw 0x65c51cc30b30b2cc 0x66f7fec3ef30f3cc

def z937 : W := mkw 0x50088018668669aa 0x57fec3beeeafefaa

def z938 : W := mkw 0x41841cc30230b2c8 0x46d5fcc30e30f3c8

def z939 : W := mkw 0x01e03bf7ddc00000 0xfdffffffffd1007f

def z940 : W := mkw 0x01c018d34d800000 0xffffffffffd11c7f

def z941 : W := mkw 0x80962f03b03b0370 0xadb3ff03f17f03f5

def z942 : W := mkw 0xd01e8408223f6bfa 0x57800000002eebaa

def z943 : W := mkw 0x01f03bf7ddc90400 0x007fffffffc10400

def z944 : W := mkw 0x01e018f74dc00000 0x007ffeffefc00000

def z945 : W := mkw 0x01e03bf7ddc00000 0x0005fefaee000000

def z946 : W := mkw 0x65c51cc30b30b2cc 0x4680bc820e20e388

def z947 : W := mkw 0x65c51cc30b30b2cc 0x038ffdc60e31ff80

def z948 : W := mkw 0x016033f44dc00000 0x007ffffeefc00000

def z949 : W := mkw 0x00802b03b0020120 0x05b2fe02e02e03a0

def z950 : W := mkw 0xd0868813f68223fa 0x54700002ee8003aa

def z951 : W := mkw 0x65c51cc30b30b2cc 0xefdffdc71f71ffdd

def z952 : W := mkw 0x01e03bf7ddc00000 0xdfffffffffc10c3b

def z953 : W := mkw 0x740d84082236fbee 0x00000000002ee380

def z954 : W := mkw 0x011837ec003ddc00 0x079ffffd003ffc40

def z955 : W := mkw 0x65c518c30b00b2cc 0x6655fcc30f00f3cc

def z956 : W := mkw 0x50088018668669aa 0xd7fec2baeebfebfa

def z957 : W := mkw 0x01e03bf7ddc00000 0x847fffffffc00070

def z958 : W := mkw 0x011837ec003ddc00 0x038effbc002fec00

def z959 : W := mkw 0x017837ec097ddc00 0x038ffffc017ffc00

def z960 : W := mkw 0x901aa318f48f4932 0xffff437df1df1c7f

def z961 : W := mkw 0x80962f03b03b0370 0x0430be02e02e03a0

def z962 : W := mkw 0x65c51cc30b30b2cc 0x0005fcc20e20e380

def z963 : W := mkw 0x410010c002002088 0x46d5fcc20e20e388

def z964 : W := mkw 0x011837ec003ddc00 0x66d5fef9013ef04c

def z965 : W := mkw 0x50088018668669aa 0x15bac2baeeaeeba2

def z966 : W := mkw 0x40080008220669a8 0x47fec2baee2eeba8

def z967 : W := mkw 0x01e03bf7ddc00000 0xd7ffffffffd1087a

def z968 : W := mkw 0x50088018668669aa 0x100882baeeaeeb82

def z969 : W := mkw 0x011837ec003ddc00 0x038b3f7c003ffc00

def z970 : W := mkw 0x01e03bf7ddc00000 0x547fffffffc0002a

def z971 : W := mkw 0x65c51cc30b30b2cc 0x2491fcc30f30f3c4

def z972 : W := mkw 0x011837ec003ddc00 0x000efeb8002ee000

def z973 : W := mkw 0x011837ec003ddc00 0x7ffffffc01fffc2f

def z974 : W := mkw 0x650514c00230b2cc 0x66d5fcc20e30f3cc

def z975 : W := mkw 0x50088018668669aa 0x77ffc3ffefbfffee

def z976 : W := mkw 0x01e03bf7ddc00000 0x0003ffbaee000000

def z977 : W := mkw 0x00802b13d4800000 0x007efebaee800000

def z978 : W := mkw 0x011814c8003ddc00 0x038ffef8003ffc00

def z979 : W := mkw 0x010833ec00044800 0x038efeb8002ee800

def z980 : W := mkw 0x81e63bf7ddc00250 0x807fffffffc00050

def z981 : W := mkw 0x0000000000000000 0xffffc1c71fd11c7f

def z982 : W := mkw 0x00a02b37d4c00000 0x007fffbffec00000

def z983 : W := mkw 0x011837ec003ddc00 0x020ffffc002efc00

def z984 : W := mkw 0x1028a33cf4c64922 0x002a033cf0ce0000

def z985 : W := mkw 0x50c088136f8221aa 0x54700003ef8003aa

def z986 : W := mkw 0x80962f03b03b0370 0x05b3ff02e03f03a0

def z987 : W := mkw 0x011837ec003ddc00 0x0200beb8002efc00

def z988 : W := mkw 0x80962f03b03b0370 0xd7b3ff03f03f0bfa

def z989 : W := mkw 0x011837ec003ddc00 0x03bffffd103ffc00

def z990 : W := mkw 0x40000010668221a8 0x47fec2baeeaee3a8

def z991 : W := mkw 0x011837ec003ddc00 0x7fdffffd01fffc4f

def z992 : W := mkw 0x80962f03b03b0370 0x05b3fe03e03e03e0

def z993 : W := mkw 0x50088018668669aa 0x13aec2baeeaeeba2

def z994 : W := mkw 0x01e03bf7ddc00000 0x007ffffeee800000

def z995 : W := mkw 0x00102700203b0120 0x0000be02e02e0380

def z996 : W := mkw 0x65c51cc30b30b2cc 0x4244bc820e20e388

def z997 : W := mkw 0x50088018668669aa 0x57d4c2baee2eebaa

def z998 : W := mkw 0x011814ec003ddc00 0x038dfcfc003ffc00

def z999 : W := mkw 0x80962f03b03b0370 0x95bbff03f0bf0bf2

def z1000 : W := mkw 0x00102700203b0120 0x05b2fe02e02e03a0

def z1001 : W := mkw 0x00842f03b0320360 0x05b3ff03f03e03e0

def z1002 : W := mkw 0x80962f03b03b0370 0x8123bf03f03f03f0

def z1003 : W := mkw 0x65c51cc30b30b2cc 0x66d0bc830f30f3cc

def z1004 : W := mkw 0x011837ec003ddc00 0x03bffffee03ffc00

def z1005 : W := mkw 0x1028a33cf4c64922 0x992a033cf0cf0c33

def z1006 : W := mkw 0x80962f03b03b0370 0x0182fe02e02e0380

def z1007 : W := mkw 0x81f23bf7ddc90010 0x807fffffffc10010

def z1008 : W := mkw 0x656910fc4fc4fc8c 0x624c00fc0fc0fc0c

def z1009 : W := mkw 0x64c50c030b3022cc 0x66d5fc830f30e3cc

def z1010 : W := mkw 0x01c03bd3dd800000 0x007ffffbff800000

def z1011 : W := mkw 0x50188408223ffdaa 0x03800000003fff80

def z1012 : W := mkw 0x410014c00230b088 0x46d4fc820e20e388

def z1013 : W := mkw 0x00802b03b0020120 0x57ffff47f1ee0baa

def z1014 : W := mkw 0x50088018668669aa 0x520082baee2eeb8a

def z1015 : W := mkw 0x65c51cc30b30b2cc 0x7fdffdc70ff1ffcf

def z1016 : W := mkw 0x65c51cc30b30b2cc 0x2055fcc30f30f3c4

def z1017 : W := mkw 0x50088018668669aa 0x77fec2faefaefbae

def z1018 : W := mkw 0x011837ec003ddc00 0x67fffffd11fffc4c

def z1019 : W := mkw 0x50088018668669aa 0x058082baee2ee3a0

def z1020 : W := mkw 0x01e03bf7ddc00000 0x005fffffef000000

def z1021 : W := mkw 0x011837ec003ddc00 0x7bfffffd11fffc0f

def z1022 : W := mkw 0x0080081344800000 0x007ffebbee800000

def z1023 : W := mkw 0x65c51cc30b30b2cc 0x0284fc820e20e380

def z1024 : W := mkw 0x50088018668669aa 0xfffec2feefffffff

def z1025 : W := mkw 0x011837ec003ddc00 0xbbaffffd11fffc77

def z1026 : W := mkw 0x01e03bf7ddc00000 0x0032febaee000000

def z1027 : W := mkw 0x80962f03b03b0370 0x87ffff47f1ff1ff0

def z1028 : W := mkw 0x01e03bf7ddc00000 0x77ffffffffd0186e

def z1029 : W := mkw 0x01e03bf7ddc00000 0xfe7fffffffc01c7f

def z1030 : W := mkw 0x1028a33cf4c64922 0x112a0238e08e0822

def z1031 : W := mkw 0x80962f03b03b0370 0x85bfff47f03f03f0

def z1032 : W := mkw 0x65c51cc30b30b2cc 0x66d5fdc70f31f7cc

def z1033 : W := mkw 0x65c51cc30b30b2cc 0xe7fffdc71f31fffc

def z1034 : W := mkw 0x41c41cc30b3022c8 0x46d5fcc30f30e3c8

def z1035 : W := mkw 0x64850c030230b2cc 0x66d5fc830e30f3cc

def z1036 : W := mkw 0x80962f03b03b0370 0x0011fe03e02e0380

def z1037 : W := mkw 0x011837ec003ddc00 0x0204bef8002ef000

def z1038 : W := mkw 0x011837ec003ddc00 0xff8ffffd117ffc7f

def z1039 : W := mkw 0x011837ec003ddc00 0x0380beb8002ee800

def z1040 : W := mkw 0x80962f03b03b0370 0x7a4cbe46e1ee1f8f

def z1041 : W := mkw 0x00802b13d4800000 0xffffffffffd11c7f

def z1042 : W := mkw 0x011837ec003ddc00 0x020dbffc003ffc00

def z1043 : W := mkw 0x80962f03b03b0370 0x85bfffbbf03f03f0

def z1044 : W := mkw 0x65c51cc39b30b2cc 0x66f5fcc3ff30f3cc

def z1045 : W := mkw 0x65c51cc30b30b2cc 0x0204bcc20e20f380

def z1046 : W := mkw 0x65c51cc30b30b2cc 0xfffffcc30fb1ffff

def z1047 : W := mkw 0x50088018668669aa 0x05fec2baeeaee3a0

def z1048 : W := mkw 0x1018a33c648f4d22 0x112a0238e08e0822

def z1049 : W := mkw 0x754990d84f84f88e 0x524c00b80e80e80a

def z1050 : W := mkw 0x80962f03b03b0370 0x8532bf03f02f03f0

def z1051 : W := mkw 0x65c51cc30b30b2cc 0x66dffdc70f30f3cc

def z1052 : W := mkw 0x65c51cc30b30b2cc 0x66ddfcc70f30ffcc

def z1053 : W := mkw 0x741d8408223fffee 0x77800000003fffee

def z1054 : W := mkw 0x80962f03b03b0370 0x85f3ff03f1ff03f0

def z1055 : W := mkw 0x01e03bf7ddc00000 0x987fffffffc00033

def z1056 : W := mkw 0x41c018c30b002088 0x66d5fcc30f30f3cc

def z1057 : W := mkw 0x80962f03b03b0370 0x85a33f01f03f03f0

def z1058 : W := mkw 0x0000000000000000 0xfff1014511d11c7f

def z1059 : W := mkw 0x01c018d34d800000 0x77fffefbef90186e

def z1060 : W := mkw 0x41c018c30b002088 0x0055fcc30f20e380

def z1061 : W := mkw 0x1018a33c648f4d22 0x00000238e00e0000

def z1062 : W := mkw 0x011837ec003ddc00 0x0285fffc003ff400

def z1063 : W := mkw 0x00802b03b0020120 0x0000be02e02e0380

def z1064 : W := mkw 0x011837ec003ddc00 0xafbffffd117ffc75

def z1065 : W := mkw 0x50188408223f69aa 0x57800000003febaa

def z1066 : W := mkw 0x01e03bf7ddc00000 0xfc7fffffffd1147f

def z1067 : W := mkw 0x011837ec003ddc00 0x0003ffb8002ee000

def z1068 : W := mkw 0x011837ec003ddc00 0x57fffffd11fffc2a

def z1069 : W := mkw 0x50188408223ffdaa 0x00000000002ee380

def z1070 : W := mkw 0x50088018668669aa 0x56dcc2baeeaeeb8a

def z1071 : W := mkw 0x50088018668669aa 0x445082baee2ee388

def z1072 : W := mkw 0x50088018668669aa 0x07bec2baee2eeba0

def z1073 : W := mkw 0x010033f444800000 0xffffffffffd11c7f

def z1074 : W := mkw 0x01e03bf7ddc00000 0xfeffffffffd0107f

def z1075 : W := mkw 0x516890fc4fc4688a 0x524c00b80e80e80a

def z1076 : W := mkw 0x65c51cc30b30b2cc 0x6040bc820f20e38c

def z1077 : W := mkw 0x41c018c30b002088 0xfffffdc71ff1ffff

def z1078 : W := mkw 0x011837ec003ddc00 0x0081feb8003ee000

def z1079 : W := mkw 0x80962f03b03b9770 0x85b3ff03f03f17f0

def z1080 : W := mkw 0x80f62f03b97b0370 0x85b3ff03f17f03f0

def z1081 : W := mkw 0x01e03bf7ddc00000 0x647fffffffc0004c

def z1082 : W := mkw 0xd01e8408223f6bfa 0xffff414511ffffff

def z1083 : W := mkw 0x65c51cc30b30b2cc 0x66f5fcc31ff0f3cc

def z1084 : W := mkw 0x011837ec003ddc00 0x0000bfbc002fe400

def z1085 : W := mkw 0x01e03bf7ddc00000 0x0077fffbff000000

def z1086 : W := mkw 0x80962f03b03b0370 0x85b0be03f03f03f0

def z1087 : W := mkw 0x010810c800044800 0x038ffef8002ee800

def z1088 : W := mkw 0x65c51cc30b30b2cc 0xfefffdc71ff0f3ff

def z1089 : W := mkw 0x65c51cc30b30b2cc 0xfefdfcc71ff0ffff

def z1090 : W := mkw 0x011837ec003ddc00 0xff80beb8003ffc7f

def z1091 : W := mkw 0x01e03bf7ddc00000 0x038ffffeee111c00

def z1092 : W := mkw 0x901aa318f48f4932 0xd7ff4339f09f087a

def z1093 : W := mkw 0x80962f03b03b0370 0x87b7ff43f03f13f0

def z1094 : W := mkw 0x50088018668669aa 0x038fc3feee3fff80

def z1095 : W := mkw 0x011837ec003ddc00 0x0383ffb8003ffc00

def z1096 : W := mkw 0x80962f03b03b0370 0xf7ffff43f1bf1bfe

def z1097 : W := mkw 0x50088018668669aa 0x424482baee2ee388

def z1098 : W := mkw 0x011837ec003ddc00 0x992abfbc10efec33

def z1099 : W := mkw 0x80962f03b03b0370 0x0122be02e02e03a0

def z1100 : W := mkw 0x01e43bf7ddc00240 0x047fffffffc003c0

def z1101 : W := mkw 0x65c51cc30b30b2cc 0x67d5fcc30f31ffcc

def z1102 : W := mkw 0x01e03bf7ddc00000 0x01ffffffffd10000

def z1103 : W := mkw 0x65c51cc30b30b2cc 0x67d7fdc30f31f3cc

def z1104 : W := mkw 0x01e03bf7ddc00000 0x0001bfbbfe000000

def z1105 : W := mkw 0x010833ec00044800 0x000ffffc002ee000

def z1106 : W := mkw 0x01e03bf7ddc00000 0x0070bebaee800000

def z1107 : W := mkw 0x0018272c003d4c00 0x038fffbc003fec00

def z1108 : W := mkw 0x65c51cc30b30b2cc 0xffdffdc70f31ffff

def z1109 : W := mkw 0x901aa33cf48f4d32 0x912a033cf08f0c32

def z1110 : W := mkw 0x50e08813ffc221aa 0xffff4147ffd11fff

def z1111 : W := mkw 0x80962f03b03b0370 0x01b3ff03f03f0380

def z1112 : W := mkw 0x74c588136f8223ee 0xffff4147ffd11fff

def z1113 : W := mkw 0x80962f03b03b0370 0xfff7ff43f13f1fff

def z1114 : W := mkw 0x65c51cc30b30b2cc 0x0011fc830e20e380

def z1115 : W := mkw 0x00182708003d4800 0x038efeb8002ee800

def z1116 : W := mkw 0x50088018668669aa 0xffffc3bbfebfffff

def z1117 : W := mkw 0x65c51cc30b30b2cc 0x67dffcc30f30fbcc

def z1118 : W := mkw 0x50088018668669aa 0xffffc3ffffeeebff

def z1119 : W := mkw 0x011837ec003ddc00 0x0000beb8003ff400

def z1120 : W := mkw 0x50088018668669aa 0x992a83befeefefb3

def z1121 : W := mkw 0x01e03bf7ddc00000 0x0040bebaefc00000

def z1122 : W := mkw 0x65c51cc30b30b2cc 0x6255fcc30f20f38c

def z1123 : W := mkw 0x011833ec000ddc00 0x030ffffc000ffc00

def z1124 : W := mkw 0x65c51cc30b30b2cc 0x66d4fcc20f20f38c

def z1125 : W := mkw 0x011837ec003ddc00 0xab8ffffc003ffc55

def z1126 : W := mkw 0x65c51cc30b30b2cc 0x2000bcc20f20f384

def z1127 : W := mkw 0x00840c0320320360 0x0491fe03e03e03c0

def z1128 : W := mkw 0x50088018668669aa 0x540082baee2ee3aa

def z1129 : W := mkw 0x011837ec003ddc00 0x038efefc002efc00

def z1130 : W := mkw 0x01e03bf7ddc00000 0x46ffffffffc00008

def z1131 : W := mkw 0x65c51cc30b30b2cc 0xfff5fcc31ff1ffff

def z1132 : W := mkw 0x01e03bf7ddc00000 0x0050bebbef000000

def z1133 : W := mkw 0x65c51cc30b30b2cc 0xfff7fdc31ff1f3ff

def z1134 : W := mkw 0x01e03bf7ddc00000 0x007fffbbfe800000

def z1135 : W := mkw 0x80d62f03b93b0370 0x85f3ff03ff3f03f0

def z1136 : W := mkw 0x50088018668669aa 0x0182c2baee2ee380

def z1137 : W := mkw 0x80962f03b03b0370 0xfc70be03f1ee03ff

def z1138 : W := mkw 0x011837ec003ddc00 0x8b8ffffc107ffc11

def z1139 : W := mkw 0x1028a33cf4c64922 0x00000238e00e0000

def z1140 : W := mkw 0x50088018668669aa 0x007082baeeaee380

def z1141 : W := mkw 0x010837ec0034d800 0x038ffffc003ef800

def z1142 : W := mkw 0x80962f03b03b0370 0xffffff03f0bf1fff

def z1143 : W := mkw 0x65c51cc30b30b2cc 0xfffffcc31ff0fbff

def z1144 : W := mkw 0x011037e400399000 0x038ffffc003ff000

def z1145 : W := mkw 0x410014c00230b088 0x0285fcc20e30f380

def z1146 : W := mkw 0x0000000000000000 0xffffc3fd11d11c7f

def z1147 : W := mkw 0x011837ec003ddc00 0x0387fff8003ff000

def z1148 : W := mkw 0x80962f03b03b0370 0x992abf06f0ef0fb3

def z1149 : W := mkw 0x00902f03b03b0120 0x05b3ff03f03f03a0

def z1150 : W := mkw 0x80962f03b03b0370 0xa5b3ff43f13f13f4

def z1151 : W := mkw 0x00102700203b0120 0x0183ff02e03f0380

def z1152 : W := mkw 0x011837ec003ddc00 0x0001bffc002ee000

def z1153 : W := mkw 0x65c51cc30b30b2cc 0x62c5fcc20f30f38c

def z1154 : W := mkw 0x510890fc4684fc8a 0x57ff41fc0e91fc2a

def z1155 : W := mkw 0x50088018668669aa 0x547ec2baeeaee3aa

def z1156 : W := mkw 0x01e03bf7ddc00000 0xabffffffffd11c55

def z1157 : W := mkw 0x01e03bf7ddc00000 0x287fffffffc01405

def z1158 : W := mkw 0x01e03bf7ddc00000 0xe7ffffffffd1107c

def z1159 : W := mkw 0x016033f4ddc00000 0x006ffffcffc00000

def z1160 : W := mkw 0x65c51cc30b30b2cc 0x0044bcc20f20e380

def z1161 : W := mkw 0x740d84082236fbee 0xff800000003fffff

def z1162 : W := mkw 0x80962f03b03b0370 0x9fbfff47f0ff1ff3

def z1163 : W := mkw 0x011837c8003dd800 0x038ffff8003ff800

def z1164 : W := mkw 0x01e03bf7ddc00000 0x002abebaee800000

def z1165 : W := mkw 0x00182708003d4800 0xfffffffd11fffc7f

def z1166 : W := mkw 0x011837ec003ddc00 0x0102bfb8002fe000

def z1167 : W := mkw 0x0000231044800000 0x007fffbaee800000

def z1168 : W := mkw 0x1018a33c648f4d22 0x010a033ce00f0c00

def z1169 : W := mkw 0x65c51cc30b30b2cc 0xe6f5fcc31f30f3fc

def z1170 : W := mkw 0x80962f03b03b0370 0x85bbff07f03f0ff0

def z1171 : W := mkw 0x01e03bf7ddc00000 0x787fffffffc0000f

def z1172 : W := mkw 0x65c51cc30b30b2cc 0x0001bcc20e30f380

def z1173 : W := mkw 0x516890fc4fc4fc8a 0x524c00fc0fc0fc0a

def z1174 : W := mkw 0x740d84082236fbee 0xffff414511ffffff

def z1175 : W := mkw 0x516890fc4fc4688a 0x000000b80e00e000

def z1176 : W := mkw 0x80960c03b03b0370 0x85b1fc03f03f03f0

def z1177 : W := mkw 0x011837ec003ddc00 0x9b8ffffc003ffc33

def z1178 : W := mkw 0xe5c71cc39b30b2dc 0xe6d5fcc31f30f3dc

def z1179 : W := mkw 0x65c51cc30b30b2cc 0x66dffefb0f30f3cc

def z1180 : W := mkw 0x011837ec003ddc00 0x0005fef8002ee000

def z1181 : W := mkw 0x80962f03b03b0370 0x8433ff03f02e03f0

def z1182 : W := mkw 0xe5d71cc30b39b2dc 0xe6d5fcc30f31f3dc

def z1183 : W := mkw 0x754990d84f84f88e 0x7a4c00fc0fc0fc0f

def z1184 : W := mkw 0x510890fc4684fc8a 0xffff41fd1fd1fc7f

def z1185 : W := mkw 0x50088018668669aa 0x557a82baeeaeebaa

def z1186 : W := mkw 0x80962f03b03b0370 0x9db3ff03f0ff03f3

def z1187 : W := mkw 0x80962f03b03b0370 0x04b3ff03f03e03c0

def z1188 : W := mkw 0x901aa318f48f4932 0x00000238e00e0000

def z1189 : W := mkw 0x50088018668669aa 0x000ec2baee2ee380

def z1190 : W := mkw 0x01e03bf7ddc09400 0x007fffffffc01400

def z1191 : W := mkw 0x01e03bf7ddc00000 0x0000bfbefe400000

def z1192 : W := mkw 0x65c51cc30b30b2cc 0x6455fcc30f20e3cc

def z1193 : W := mkw 0x65d51cc30b39b2cc 0x67d5fcc30f3ff3cc

def z1194 : W := mkw 0xd01e8408223f6bfa 0xd7ff410110bfebfa

def z1195 : W := mkw 0x01e03bf7ddc00000 0x0011febbee000000

def z1196 : W := mkw 0x01e03bf7ddc00000 0x000cbefeee000000

def z1197 : W := mkw 0x903aa33cf4cf4932 0x912a033cf0cf0832

def z1198 : W := mkw 0x41c01cc30b30b088 0x46d5fcc30f30f388

def z1199 : W := mkw 0x0000000000000000 0xffffc34511ff1c7f

def z1200 : W := mkw 0x0000000000000000 0xffffc14711f11fff

def z1201 : W := mkw 0x50088018668669aa 0xd7fec3bafeafebba

def z1202 : W := mkw 0x011837ec003ddc00 0xa801bffd117ff455

def z1203 : W := mkw 0x011c37ec003dde40 0x078ffffc003fffc0

def z1204 : W := mkw 0x65c51cc30b30b2cc 0x66d4fc820e30f3cc

def z1205 : W := mkw 0x011837ec003ddc00 0x0385fef8003ffc00

def z1206 : W := mkw 0x754990d84f84f88e 0x624400f80f00f00c

def z1207 : W := mkw 0x65c51cc30b30b2cc 0x2000bc820e30f3c4

def z1208 : W := mkw 0x80962f03b03b0370 0x84b1fe03f03e03f0

def z1209 : W := mkw 0x65c51cc30b30b2cc 0xff80bc820e31ffff

def z1210 : W := mkw 0x80962f03b03b0370 0x85b3ff47f03f17f0

def z1211 : W := mkw 0x011837ec003ddc00 0x038d3dfc003ffc00

def z1212 : W := mkw 0x01e03bf7ddc00000 0xfb7fffffffc11c3f

def z1213 : W := mkw 0x65c51cc30b30b2cc 0x7ed5fcc30f30ffcf

def z1214 : W := mkw 0x50088018668669aa 0x536e82baeeaeebaa

def z1215 : W := mkw 0x500c840822366bea 0x57800000003eebea

def z1216 : W := mkw 0x50088018668669aa 0xfffec2baeeaeebff

def z1217 : W := mkw 0x410014c00230b088 0x57fffdc60eb1ffaa

def z1218 : W := mkw 0x01e03bf7ddc00000 0x807fffffffd10050

def z1219 : W := mkw 0x011837ec003ddc00 0x838ffffd103ffc50

def z1220 : W := mkw 0x011837ec003ddc00 0x0100beb8002fec00

def z1221 : W := mkw 0x80962f03b03b0370 0x87b3ff03f03f1ff0

def z1222 : W := mkw 0x00840c0320320360 0x77fffe43e1be1bee

def z1223 : W := mkw 0x740d84082236fbee 0x66800000003ef3cc

def z1224 : W := mkw 0x65c51cc30b30b2cc 0x0001bcc30f20e380

def z1225 : W := mkw 0x50088018668669aa 0xfffec3befeffffff

def z1226 : W := mkw 0xe41f0408223ffffc 0xe7800000003ffffc

def z1227 : W := mkw 0x50088018668669aa 0x010a82baee2eeb80

def z1228 : W := mkw 0x01e03bf7ddc00000 0xeeffffffffd1145d

def z1229 : W := mkw 0x65c51cc30b30b2cc 0x76f5fcc30fb0f3ee

def z1230 : W := mkw 0x80962f03b03b0370 0xc7f7ff03f03f03f8

def z1231 : W := mkw 0x50088018668669aa 0x66d5c2fbef3ef3cc

def z1232 : W := mkw 0x00182708003d4800 0x0000beb8002ee000

def z1233 : W := mkw 0x4080080302002088 0x46d5fc830e20e388

def z1234 : W := mkw 0x65c51cc30b30b2cc 0x66d13c430f30f3cc

def z1235 : W := mkw 0x50088018668669aa 0xf7ffc3fbffbffbfe

def z1236 : W := mkw 0x80962f03b03b0370 0xfdffff47f1ff03ff

def z1237 : W := mkw 0x01c03bf74d800000 0x007fffffef800000

def z1238 : W := mkw 0x011837ec003ddc00 0x7a4cbefc01eefc0f

def z1239 : W := mkw 0x50088018668669aa 0xdfffc3ffffefefbb

def z1240 : W := mkw 0x010814c80034d800 0x77fffef901bef86e

def z1241 : W := mkw 0x80962f03b03b0370 0x8581bf03f03f03f0

def z1242 : W := mkw 0x80962f03b03b0370 0xffffff03f1ff0bff

def z1243 : W := mkw 0x011837ec003ddc00 0x0000befc002ef400

def z1244 : W := mkw 0x50808813f68221aa 0x54700003fe8003aa

def z1245 : W := mkw 0x010814c80034d800 0x0285fef8003ef000

def z1246 : W := mkw 0x00942f03203b0360 0x05b3ff03e03f03e0

def z1247 : W := mkw 0x011837ec003ddc00 0xfbcffffd11fffc5f

def z1248 : W := mkw 0x50088018668669aa 0x57aa82baeeaeebaa

def z1249 : W := mkw 0x00802b13d4800000 0x007fffffffc00000

def z1250 : W := mkw 0x50088018668669aa 0x7fffc3ffffeeffaf

def z1251 : W := mkw 0x65c518c30b0022cc 0x66d5fcc30f20e3cc

def z1252 : W := mkw 0x80962f03b03b0370 0x85b13d03f03f03f0

def z1253 : W := mkw 0x65c51cc30b30b2cc 0x66d4fc830f20e3cc

def z1254 : W := mkw 0x01c41cc309309240 0x06d5fcc30f30f3c0

def z1255 : W := mkw 0x50088018668669aa 0xfc7082bbffeee3ff

def z1256 : W := mkw 0x1028a33cf4c64922 0x57ff437df1ce082a

def z1257 : W := mkw 0x011837ec003ddc00 0x020cbeb8002ee800

def z1258 : W := mkw 0x65c51cc30b30b2cc 0x2000bc830f20e3c4

def z1259 : W := mkw 0x010833ec00044800 0xfffffffd11fffc7f

def z1260 : W := mkw 0x80862b03b0020370 0x85b3ff03f02e03f0

def z1261 : W := mkw 0x50088018668669aa 0x57fec2bbffeeebaa

def z1262 : W := mkw 0x1008a318f4864922 0x112a0338f08e0822

def z1263 : W := mkw 0x80962f03b03b0370 0xe7ffff47f13f1ffc

def z1264 : W := mkw 0x65c51cc30b30b2cc 0xa801bdc71f71f7d5

def z1265 : W := mkw 0x25f53fe799799644 0x20013d4511511444

def z1266 : W := mkw 0x011837ec003ddc00 0xfffffffc00bffc7f

def z1267 : W := mkw 0x00182708003ddc00 0x038fffb8003ffc00

def z1268 : W := mkw 0x010814c80034d800 0x0000beb8002ee000

def z1269 : W := mkw 0x65c51cc30b30b2cc 0x6681bcc30f30f3cc

def z1270 : W := mkw 0x40840c03023022c8 0x66d5fcc30f30f3cc

def z1271 : W := mkw 0x80962f03b03b0370 0xff80be02e03f1fff

def z1272 : W := mkw 0x65c51cc30b30b2cc 0x0410bc830e20e3c0

def z1273 : W := mkw 0x011837ec003ddc00 0x079ffffe003fff80

def z1274 : W := mkw 0x011837ec003ddc00 0xabfffffd11fffc55

def z1275 : W := mkw 0x011837ec003ddc00 0x0284feb8002ee000

def z1276 : W := mkw 0x01e03bf7ddc00000 0xfc70bebbffc0007f

def z1277 : W := mkw 0x65c51cc30b30b2cc 0x7ffffcc70ff0ffef

def z1278 : W := mkw 0x65c51cc30b30b2cc 0x6654bcc30f20f3cc

def z1279 : W := mkw 0x011837ec003ddc00 0xdffffffc10fffc3b

def z1280 : W := mkw 0x80962f03b03b0370 0xfff7ff43f1ff13ff

def z1281 : W := mkw 0x80962b03b00b0370 0x8533ff03f00f03f0

def z1282 : W := mkw 0x013837ec907ddc00 0x038ffffc107ffc00

def z1283 : W := mkw 0x01e03bf7ddc00000 0xfa7fffffffd11c5f

def z1284 : W := mkw 0x80922b03b00b0130 0x85b3ff03f02f03b0

def z1285 : W := mkw 0x011837ec003ddc00 0xefdffffd117ffc5d

def z1286 : W := mkw 0x40840c03023022c8 0xfffffdc71ff1ffff

def z1287 : W := mkw 0x80962f03b03b0370 0xe5f3ff03f13f03fc

def z1288 : W := mkw 0x80962f03b03b0370 0x0001bf02e03f0380

def z1289 : W := mkw 0x80962f03b03b0370 0x85a2bf02f03f03f0

def z1290 : W := mkw 0x65c51cc30b30b2cc 0x85b3fd831e31e3f0

def z1291 : W := mkw 0x80962f03b03b0370 0x0022bf02f02e0380

def z1292 : W := mkw 0x50088018668669aa 0x57ffc2bbeebeebea

def z1293 : W := mkw 0x80962f03b03b0370 0x0001be03e03e03c0

def z1294 : W := mkw 0x65c51cc30b30b2cc 0x67fffdc71ff1ffcc

def z1295 : W := mkw 0xd0868813f68223fa 0xfc700003ffc003ff

def z1296 : W := mkw 0x011837ec003ddc00 0x1b8ffffc00fffc03

def z1297 : W := mkw 0x010033f444800000 0x57fffffeee911c2a

def z1298 : W := mkw 0x80962f03b03b0370 0xdfffff07f0ff0ffb

def z1299 : W := mkw 0x50088018668669aa 0xffffc3feeebfffff

def z1300 : W := mkw 0x65c51cc30b30b2cc 0x0001bc830e30e3c0

def z1301 : W := mkw 0xd01e8408223f6bfa 0x00000000002ee380

def z1302 : W := mkw 0x74e58813ffc223ee 0x74700003ffc003ee

def z1303 : W := mkw 0x50088018668669aa 0x0490c2baee2ee380

def z1304 : W := mkw 0x80962f03b03b0370 0x85333f03f01f03f0

def z1305 : W := mkw 0x010814ec0034dc00 0x038ffefc003efc00

def z1306 : W := mkw 0x65c51cc30b30b2cc 0x0050bc830f20e380

def z1307 : W := mkw 0x65c51cc30b30b2cc 0x6200bc820e20f38c

def z1308 : W := mkw 0xa4d72f03b93b0374 0xa5b3ff03f13f03f4

def z1309 : W := mkw 0x80962f03b03b0370 0x85b3ff47f17f03f0

def z1310 : W := mkw 0x65c51cc30b30b2cc 0x6245bcc30f30f3cc

def z1311 : W := mkw 0x01e03bf7ddc00000 0x0073ffbbffc00000

def z1312 : W := mkw 0x01e03bf7ddc00000 0x006ebffeffc00000

def z1313 : W := mkw 0x80962f03b03b0370 0x8020be02f02e03b0

def z1314 : W := mkw 0x80162700203b0370 0x85b3ff02e03f03f0

def z1315 : W := mkw 0x65c51cc30b30b2cc 0xf7fffdc31fb1fbfe

def z1316 : W := mkw 0x654514c00b30b2cc 0x66c5fcc00f30f3cc

def z1317 : W := mkw 0x01e03bf7ddc00000 0x0001bffeee000000

def z1318 : W := mkw 0x01e03bf7ddc09000 0x027fffffffc0f000

def z1319 : W := mkw 0x01e03bf7ddc00000 0x007ffefbef800000

def z1320 : W := mkw 0x65c51ce70b30b2cc 0x66ddfcff0f30f3cc

def z1321 : W := mkw 0x00802b03b0020120 0x0033ff03f02e0380

def z1322 : W := mkw 0x011837ec003ddc00 0x57fefeb800aee82a

def z1323 : W := mkw 0x754990d84f84f88e 0x77ff40f90f90f86e

def z1324 : W := mkw 0x50088018668669aa 0x77fec2baeebefbee

def z1325 : W := mkw 0x80962f03b03b9370 0x87b3ff03f03ff3f0

def z1326 : W := mkw 0x50088018668669aa 0x57fec2feeeaeffaa

def z1327 : W := mkw 0x0000000000000000 0xffffc347f1d11c7f

def z1328 : W := mkw 0x011837ec003ddc00 0x9bfffffd11fffc33

def z1329 : W := mkw 0x50088018668669aa 0x47dec2baee2eeb88

def z1330 : W := mkw 0x65c51cc30b30b2cc 0x76ddfcc30fb0fbce

def z1331 : W := mkw 0x50088018668669aa 0x0284c2baee2ee380

def z1332 : W := mkw 0x50088018668669aa 0x5ffec2beeeeeefab

def z1333 : W := mkw 0x80962f03b03b0370 0x81a3ff02f03f03b0

def z1334 : W := mkw 0x65d51cc30b39b6cc 0x66d5fcc30f31f7cc

def z1335 : W := mkw 0x80122700b03b0130 0x85b3ff02f03f03b0

def z1336 : W := mkw 0x011837ec003ddc00 0x010bbffc003ffc00

def z1337 : W := mkw 0x80962f03b03b0370 0x0580be02e02e03a0

def z1338 : W := mkw 0x65c51cc30b30b2cc 0x2285fcc30f30f3c4

def z1339 : W := mkw 0x50088018668669aa 0x57ffc2fbefaeebaa

def z1340 : W := mkw 0x50088018668669aa 0xdffec2baeeafefbb

def z1341 : W := mkw 0x80962f03b03b0370 0x85bbff07f0ff03f0

def z1342 : W := mkw 0x80962f03b03b0370 0x8033ff03f03f03d0

def z1343 : W := mkw 0x65c51cc30b30b2cc 0x77d5fcc30f30fbee

def z1344 : W := mkw 0x80962f03b03b0370 0x8000be03f02e03d0

def z1345 : W := mkw 0x80962f03b03b0370 0x0410be03e02e03c0

def z1346 : W := mkw 0x65c51cc30b30b2cc 0x66fffcc30fb0f3cc

def z1347 : W := mkw 0x01e03bf7ddc00000 0x0055ffffff400000

def z1348 : W := mkw 0x50088018668669aa 0x57ffc3ffffffffaa

def z1349 : W := mkw 0x011837ec003ddc00 0x0183fffc003ff400

def z1350 : W := mkw 0x65c51cc30b30b2cc 0x0695fcc30e30f3c0

def z1351 : W := mkw 0x80962f03b03b0370 0x57fefe02e0ae0baa

def z1352 : W := mkw 0x01c018d34d800000 0x007fffffffc00000

def z1353 : W := mkw 0x010033f444800000 0x007efebaee800000

def z1354 : W := mkw 0x64c50c030b30b2cc 0x66d1fc030f30f3cc

def z1355 : W := mkw 0x01e03bf7ddc00000 0x004ffffeefc00000

def z1356 : W := mkw 0x80962f03b03b0370 0x8db3ff07f07f07f1

def z1357 : W := mkw 0x01e03bf7ddc00000 0x117fffffffc00822

def z1358 : W := mkw 0x50088018668669aa 0x7fffc2ffeffeffef

def z1359 : W := mkw 0x65c51cc30b30b2cc 0x67f7fcc30f30f3ec

def z1360 : W := mkw 0x50088018668669aa 0x038082baee2eeb80

def z1361 : W := mkw 0x01e03bf7ddc00000 0x66d5fefbef10104c

def z1362 : W := mkw 0x80962f03b03b0370 0x038fff46e03f1f80

def z1363 : W := mkw 0x011837ec003ddc00 0x038fffb8003fe800

def z1364 : W := mkw 0x1018a33c648f4d22 0x57ff437ce09f1c2a

def z1365 : W := mkw 0x80962f03b03b0370 0xfdfbff07f1ff0fff

def z1366 : W := mkw 0x80962f03b03b0370 0x8183ff03f03f03d0

def z1367 : W := mkw 0x01e03bf7ddc00000 0x7fffffffffc01c2f

def z1368 : W := mkw 0x0008230800044800 0x038fffb8002ee800

def z1369 : W := mkw 0x80962f03b03b0370 0x0593ff03e03f03c0

def z1370 : W := mkw 0x01e03bf7ddc00000 0x006f3ffdffc00000

def z1371 : W := mkw 0x50188408223ffdaa 0x57ff414400bfffaa

def z1372 : W := mkw 0x01e03bf7ddc00000 0x04ffffffffd00040

def z1373 : W := mkw 0xd0868813f68223fa 0xffff4147ffd11fff

def z1374 : W := mkw 0x500884082236f9aa 0x57800000003efbaa

def z1375 : W := mkw 0x50088018668669aa 0x578ec2baee2eebaa

def z1376 : W := mkw 0x01e03bf7ddc00000 0xa801bfffff511455

def z1377 : W := mkw 0x41c018c30b002088 0x0000bc820e20e380

def z1378 : W := mkw 0x01e03bf7ddc00000 0x0000befeef400000

def z1379 : W := mkw 0x01e03bf7ddc00000 0x002ffffefec00000

def z1380 : W := mkw 0x01e03bf7ddc00000 0x627fffffffc0100c

def z1381 : W := mkw 0x65c51cc30b30b2cc 0x7a4cbcc60fe0ff8f

def z1382 : W := mkw 0x50088018668669aa 0x7a4c82feefeeff8f

def z1383 : W := mkw 0x010833ec0004dc00 0x038ffffc002efc00

def z1384 : W := mkw 0x80962f03b03b0370 0x85b2ff02f02f03b0

def z1385 : W := mkw 0x00102700203b0120 0xffffff47f1ff1fff

def z1386 : W := mkw 0x80962f03b03b0370 0x8591fe03e03f03f0

def z1387 : W := mkw 0x65c51cc30b30b2cc 0x6400bc820e20e3cc

def z1388 : W := mkw 0x80962f27b03b0370 0x85bbff3ff03f03f0

def z1389 : W := mkw 0x65c51cc30b30b2cc 0x02d5fcc30f30f380

def z1390 : W := mkw 0x011837ec003ddc00 0x028ffffc003ef000

def z1391 : W := mkw 0x80962f03b03b0370 0x85b2fe03f02e03f0

def z1392 : W := mkw 0x01e03bf7ddc00000 0x003ffffffe000000

def z1393 : W := mkw 0x50088018668669aa 0x03fec2baeeaeeb80

def z1394 : W := mkw 0x65c51cc30b30b2cc 0x66553cc30f10f3cc

def z1395 : W := mkw 0x80962f03b03b0370 0x87b7ff83f03fe3f0

def z1396 : W := mkw 0x80962f03b03b0370 0xffbfff47f03f1fff

def z1397 : W := mkw 0x65c51cc30b30b2cc 0x6451bcc30f30f3cc

def z1398 : W := mkw 0x50088018668669aa 0x004c82baeeaee380

def z1399 : W := mkw 0xa4972f03b03b9374 0xa5b3ff03f03f13f4

def z1400 : W := mkw 0x011837ec003ddc00 0x77fffffd01bffc6e

def z1401 : W := mkw 0x1018a318648f4922 0x112a0338e08f0822

def z1402 : W := mkw 0x80962f03b03b0370 0xfdf3ff47f1ff17ff

def z1403 : W := mkw 0x011837ec003ddc00 0x000abfbc002ee000

def z1404 : W := mkw 0x01e03bf7ddc00000 0x000fffffff400000

def z1405 : W := mkw 0x65c51cc30b30b2cc 0x7efffdc71ff0ffcf

def z1406 : W := mkw 0x65c51cc30b30b2cc 0x57fefc820ea0ebaa

def z1407 : W := mkw 0x01e03bf7ddc00000 0x007efefeefc00000

def z1408 : W := mkw 0xa5d73fe799399654 0xa0013d4511111454

def z1409 : W := mkw 0x410014c00230b088 0xfffffdc71ff1ffff

def z1410 : W := mkw 0x50e08813ffc221aa 0x00000002ee000380

def z1411 : W := mkw 0x754990fc4f84fc8e 0x724c00fc0f80fc0e

def z1412 : W := mkw 0xf41f8408223ffbfe 0xf7800000003ffbfe

def z1413 : W := mkw 0x01e03bf7ddc00000 0x87ffffffffd11c70

def z1414 : W := mkw 0x80962f03b03b0370 0xfff3ff03f1ff1fff

def z1415 : W := mkw 0x50088018668669aa 0x85b3c3bbfe3fe3f0

def z1416 : W := mkw 0x00942f0390390240 0x05b3ff03f03f03c0

def z1417 : W := mkw 0x50088018668669aa 0x57ffc2faeebefbaa

def z1418 : W := mkw 0x510890fc4684fc8a 0x000000b80e00e000

def z1419 : W := mkw 0x50088018668669aa 0x020c82baee2eeb80

def z1420 : W := mkw 0x80962f03b03b0370 0xfdb3ff03f03f03ff

def z1421 : W := mkw 0x01e03bf7ddc00000 0x187fffffffc00c03

def z1422 : W := mkw 0x01e03bf7ddc00000 0x57ffffffffd11c2a

def z1423 : W := mkw 0x65c51cc30b30b2cc 0xe7fffdc71ff1f3fc

def z1424 : W := mkw 0x01e03bf7ddc00000 0x0008bebeeec00000

def z1425 : W := mkw 0x011837ec003ddc00 0x038abfbc003ffc00

def z1426 : W := mkw 0x01e03bf7ddc00000 0x57fefebaee80082a

def z1427 : W := mkw 0x01f03bf7ddc90000 0x017fffffffcf0000

def z1428 : W := mkw 0x80962f03b03b0370 0x85b2fe02e03f03f0

def z1429 : W := mkw 0xd01e8408223ffffa 0xd7800000003ffffa

def z1430 : W := mkw 0x65c51cc30b30b2cc 0x4450bc820e20e388

def z1431 : W := mkw 0x011837ec003ddc00 0x007ffffd11eee000

def z1432 : W := mkw 0x80962f03b03b0370 0x0032fe02e02e0380

def z1433 : W := mkw 0x80962f03b03b0370 0xe7ffff47f1ff13fc

def z1434 : W := mkw 0x011837ec003ddc00 0x03cffffc01fffc00

def z1435 : W := mkw 0x011837ec003ddc00 0xffaffffc10fffc7f

def z1436 : W := mkw 0x65c51cc30b30b2cc 0x66ddfcc70ff0f3cc

def z1437 : W := mkw 0x25e13bf7ddc09004 0x207fffffffc01004

def z1438 : W := mkw 0x01e03bf7ddc00000 0x7effffffffd01c4f

def z1439 : W := mkw 0x50088018668669aa 0x55f2c2baeeaee3aa

def z1440 : W := mkw 0x65c51cc30b30b2cc 0xeed5fcc30f31f7dd

def z1441 : W := mkw 0x011837ec003ddc00 0x028dfefc003efc00

def z1442 : W := mkw 0x65c51cc30b30b2cc 0x77fffdc70fb1ffee

def z1443 : W := mkw 0x50088018668669aa 0x57fec2baeebfffaa

def z1444 : W := mkw 0x50088018668669aa 0x504082baeeaee38a

def z1445 : W := mkw 0x50088018668669aa 0x012282baee2ee3a0

def z1446 : W := mkw 0x50088018668669aa 0x57fec2feefeeebaa

def z1447 : W := mkw 0x01e03bf7ddc00000 0x992abfbefec10c33

def z1448 : W := mkw 0x00802b03b0020120 0xffffff47f1ff1fff

def z1449 : W := mkw 0x50088018668669aa 0xd7fec2bbfeaeebfa

def z1450 : W := mkw 0x80962f03b03b0370 0xeff7ff47f17f17fd

def z1451 : W := mkw 0x01e03bf7ddc00000 0xb97fffffffd11c77

def z1452 : W := mkw 0x011837ec003ddc00 0x038efeb8003ffc00

def z1453 : W := mkw 0x011837ec003d4800 0x038ffffc003fe800

def z1454 : W := mkw 0x00802b13d4800000 0x0000bebaee000000

def z1455 : W := mkw 0x0080080320020120 0x05b3fe03e02e03a0

def z1456 : W := mkw 0x011837ec003ddc00 0x0008bebc002eec00

def z1457 : W := mkw 0x80962f03b03b0370 0xadffff47f1ff17f5

def z1458 : W := mkw 0x65c51cc30b30b2cc 0x0490fc820e20e380

def z1459 : W := mkw 0x65c51cc30b30b2cc 0x04d5fcc30f30e3c0

def z1460 : W := mkw 0x65c51cc30b30b2cc 0x6685fcc20e30f3cc

def z1461 : W := mkw 0x50088018668669aa 0x57b2c2baee2eebaa

def z1462 : W := mkw 0x65c51cc30b30b2cc 0x007ffdc71fe0e380

def z1463 : W := mkw 0x811e37ec003dde50 0x838ffffc003ffc50

def z1464 : W := mkw 0x011837ec003ddc00 0x63cffffc013ffc0c

def z1465 : W := mkw 0x80962f03b03b0370 0x9db3ff03f03f0ff3

def z1466 : W := mkw 0x00e02b37ddc00000 0x007bff3fffc00000

def z1467 : W := mkw 0x80962f03b03b0370 0x0102bf02e02f0380

def z1468 : W := mkw 0x50088018668669aa 0x7ffec2baefeeebaf

def z1469 : W := mkw 0x011837ec003ddc00 0x53cffffc00bffc0a

def z1470 : W := mkw 0x011837ec003ddc00 0x0001bfb8003fe000

def z1471 : W := mkw 0x01e03bf7ddc00000 0x004dbfffffc00000

def z1472 : W := mkw 0x50088018668669aa 0x007fc3ffffeee380

def z1473 : W := mkw 0x01e03bf7ddc00000 0x007d3dffffc00000

def z1474 : W := mkw 0x010033f444800000 0x0000bebaee000000

def z1475 : W := mkw 0x01e03bf7ddc00000 0x0020bebafec00000

def z1476 : W := mkw 0x01e03bf7ddc00000 0x817fffffffc10030

def z1477 : W := mkw 0x80962f27b03b0770 0x85b3ff07f03f07f0

def z1478 : W := mkw 0x80962f03b03b0370 0x8100be02e02f03b0

def z1479 : W := mkw 0x811a37ec903ddc10 0x838ffffc103ffc10

def z1480 : W := mkw 0x255937ec093ddc04 0x238ffffc013ffc04

def z1481 : W := mkw 0x011837ec003ddc00 0x038ffffc002ee800

def z1482 : W := mkw 0x0000000000000000 0xffffc1c511f1fc7f

def z1483 : W := mkw 0x65c51cc30b30b2cc 0xffddfcc70ff1ffff

def z1484 : W := mkw 0x01e03bf7ddc00000 0x02ffffffffe0e000

def z1485 : W := mkw 0x65c51cc30b30b2cc 0x66f7fdc31f30f3cc

def z1486 : W := mkw 0x1038a33cf4cf4d22 0x112a033cf0cf0c22

def z1487 : W := mkw 0xd0868813f68223fa 0xd7ff4103fe910bfa

def z1488 : W := mkw 0x65c51cc30b30b2cc 0x0081fc820e30e380

def z1489 : W := mkw 0x41c018c30b002088 0x57fffdc71fe0ebaa

def z1490 : W := mkw 0x80962f03b03b0370 0xa801bf47f17f17d5

def z1491 : W := mkw 0x50088018668669aa 0x57ffc3baeebfebaa

def z1492 : W := mkw 0x50088018668669aa 0x527ec2baeeaeeb8a

def z1493 : W := mkw 0x01e03bf7ddc00000 0x0030bebbfe000000

def z1494 : W := mkw 0xd0e68813ffc223fa 0xd4700003ffc003fa

def z1495 : W := mkw 0x80962f03b03b0370 0xd7ffff47f0bf1ffa

def z1496 : W := mkw 0x011837ec003ddc00 0x03fffffc00bffc00

def z1497 : W := mkw 0x0018272c003ddc00 0x038bff3c003ffc00

def z1498 : W := mkw 0x80962f03b03b0370 0x87bfff03f03f0bf0

def z1499 : W := mkw 0x01e03bf7ddc00000 0x04ffffffffe00380

def z1500 : W := mkw 0x80962f03b03b0370 0x0180be02e03f0380

def z1501 : W := mkw 0x01e03bf7ddc00000 0x01ffffffffee0000

def z1502 : W := mkw 0xa5f73fe799799254 0xa0013d4511511054

def z1503 : W := mkw 0x756990fc4fc4f88e 0x724c00fc0fc0f80e

def z1504 : W := mkw 0x803a233cf4cf4d30 0x812a033cf0cf0c30

def z1505 : W := mkw 0x65c51cc30b30b2cc 0x0054fc820e20e380

def z1506 : W := mkw 0x01e03bf7ddc00000 0x9bffffffffd11c33

def z1507 : W := mkw 0x01e03bf7ddc00000 0xa87fffffffc00055

def z1508 : W := mkw 0x516890fc4fc4688a 0x57ff41fd1fc0e82a

def z1509 : W := mkw 0x01e03bf7ddc00000 0x017fffffffc10c00

def z1510 : W := mkw 0x011837ec003ddc00 0x000cbefc002ee000

def z1511 : W := mkw 0x01e03bf7ddc00000 0x0000bebbff400000

def z1512 : W := mkw 0x01e03bf7ddc00000 0x85b3ffbbfe110070

def z1513 : W := mkw 0x011837ec003ddc00 0x47dffffc003ffc08

def z1514 : W := mkw 0x65c51cc30b30b2cc 0x46d5fcc20e30f388

def z1515 : W := mkw 0x01e03bf7ddc00000 0x03ffffffffc00800

def z1516 : W := mkw 0x50088018668669aa 0xfffec2ffffeeffff

def z1517 : W := mkw 0x011837ec003ddc00 0x878ffffc003ffc70

def z1518 : W := mkw 0x50088018668669aa 0x002a82baeeaee380

def z1519 : W := mkw 0x65c51cc30b30b2cc 0xfef5fdc71ff1f7ff

def z1520 : W := mkw 0x0000040020320120 0x05b3fe02e03e03a0

def z1521 : W := mkw 0x80962f03b03b0370 0xd5f3ff03f0bf03fa

def z1522 : W := mkw 0x81f63fe799799650 0x80013d4511511450

def z1523 : W := mkw 0x011837ec003ddc00 0x9fbffffd10fffc73

def z1524 : W := mkw 0x50e08813ffc221aa 0x57ff4147ffc00baa

def z1525 : W := mkw 0x011837ec003ddc00 0x038ffef8003ef800

def z1526 : W := mkw 0x01e03bf7ddc00000 0x67ffffffffd11c4c

def z1527 : W := mkw 0x01e018d3ddc00000 0x007ffefbffc00000

def z1528 : W := mkw 0x01e03bf7ddc00000 0x007cbeffffc00000

def z1529 : W := mkw 0x011837ec003ddc00 0x030ebffc002ffc00

def z1530 : W := mkw 0x50088018668669aa 0x57ffc3bbfeaeebaa

def z1531 : W := mkw 0x514890d84f84688a 0x524c00f80f80e80a

def z1532 : W := mkw 0x80162700b03b0370 0x85a3ff00f03f03f0

def z1533 : W := mkw 0x80962f03b03b0370 0x0030be03f02e0380

def z1534 : W := mkw 0x50088018668669aa 0xd7ffc3fffebffffa

def z1535 : W := mkw 0x50848813668223ea 0x54700003ee8003ea

def z1536 : W := mkw 0x65c51cc30b30b2cc 0xeed5fcc31f70f3dd

def z1537 : W := mkw 0x011837ec003ddc00 0x038cbefc003ffc00

def z1538 : W := mkw 0x65c51cc30b30b2cc 0x77fffdc71ff0fbee

def z1539 : W := mkw 0x50088018668669aa 0x102082baeeaee3a2

def z1540 : W := mkw 0x01e03bf7ddc00000 0x007efebbffc00000

def z1541 : W := mkw 0x65c51cc30b30b2cc 0xfff7fdc31f31ffff

def z1542 : W := mkw 0x011837ec003ddc00 0x010abeb8002ee800

def z1543 : W := mkw 0x50088018668669aa 0xdfffc3bffeffeffb

def z1544 : W := mkw 0x50088018668669aa 0x47f6c2baee2ee3a8

def z1545 : W := mkw 0x80962f03b03b0370 0x8133ff03f02f03b0

def z1546 : W := mkw 0x011837ec003ddc00 0x83affffc103ffc30

def z1547 : W := mkw 0x80860c03b0320370 0x85b3fe03f03e03f0

def z1548 : W := mkw 0x011837ec003ddc00 0xffcffffc01fffc7f

def z1549 : W := mkw 0x80962f03b03b0370 0x85f7ff43f13f03f0

def z1550 : W := mkw 0x01e03bf7ddc00000 0x9dffffffffd10c73

def z1551 : W := mkw 0x80960c03203b0370 0x85b3fe03e03f03f0

def z1552 : W := mkw 0x01e03bf7ddc00000 0x007abfbfffc00000

def z1553 : W := mkw 0x01e03bf7ddc00000 0x887fffffffc10411

def z1554 : W := mkw 0x011837ec003ddc00 0x03dffffd013ffc00

def z1555 : W := mkw 0x011837ec003ddc00 0xffbffffd103ffc7f

def z1556 : W := mkw 0x1018a33c648f4d22 0xffff437df1df1c7f

def z1557 : W := mkw 0x011837ec003ddc00 0x0182feb8002ee000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6])],[(0,[z1,z2,z10,z4,z11,z5,z6]),(0,[z1,z2,z3,z4,z5,z12,z6]),(0,[z7,z1,z13,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z14]),(0,[z1,z2,z3,z4,z5,z15,z6])],[(0,[z1,z2,z10,z4,z5,z6,z16]),(0,[z1,z2,z3,z4,z17,z5,z6]),(0,[z1,z2,z3,z18,z5,z19,z6])],[(0,[z1,z1,z20,z3,z4,z5,z6]),(0,[z1,z21,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z22,z6]),(0,[z1,z2,z3,z4,z19,z23,z6])],[(0,[z1,z24,z3,z25,z4,z5,z6]),(0,[z26,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z28]),(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z30]),(0,[z1,z2,z3,z4,z5,z31,z6])],[(0,[z1,z20,z3,z32,z4,z5,z6]),(0,[z1,z2,z3,z33,z4,z19,z6])],[(0,[z1,z2,z3,z34,z4,z5,z6]),(1,[z1,z35,z2,z3,z4,z16])],[(0,[z1,z36,z20,z3,z4,z5,z6]),(0,[z1,z37,z2,z38,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z40,z5,z6])],[(1,[z1,z20,z3,z4,z5,z41]),(0,[z1,z42,z2,z3,z4,z5,z6]),(0,[z1,z43,z24,z3,z4,z5,z6]),(0,[z1,z44,z24,z3,z4,z5,z6]),(1,[z1,z2,z3,z45,z5,z6]),(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z1,z2,z47,z3,z4,z5,z6])],[(0,[z1,z2,z25,z4,z48,z5,z6]),(0,[z1,z2,z3,z49,z4,z5,z6])],[(0,[z1,z2,z20,z3,z50,z5,z6]),(0,[z51,z1,z52,z3,z4,z5,z6]),(1,[z1,z8,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z53,z5,z28]),(0,[z1,z54,z2,z3,z4,z5,z6])],[(0,[z1,z2,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z6,z56]),(1,[z1,z13,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z19,z41]),(0,[z1,z2,z3,z4,z5,z57,z6]),(0,[z58,z1,z2,z3,z4,z5,z6]),(1,[z1,z59,z3,z4,z5,z60])],[(0,[z1,z2,z3,z4,z5,z22,z41]),(0,[z1,z2,z3,z61,z4,z5,z28]),(0,[z1,z62,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z63,z6])],[(0,[z64,z1,z20,z3,z4,z5,z6]),(0,[z1,z65,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z28,z56]),(0,[z1,z2,z3,z66,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z67,z6]),(1,[z1,z68,z3,z4,z5,z69])],[(0,[z1,z24,z3,z4,z5,z70,z6]),(0,[z1,z2,z3,z4,z71,z5,z6])]],
   [[],[(0,[z1,z20,z3,z72,z4,z5,z6]),(0,[z1,z24,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z73,z4,z5,z6]),(0,[z1,z2,z3,z4,z74,z19,z6]),(0,[z1,z2,z3,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z75,z5,z6]),(0,[z1,z2,z4,z5,z6,z76,z56]),(0,[z1,z77,z2,z3,z4,z5,z6])],[(0,[z78,z1,z2,z3,z4,z11,z6])],[(0,[z1,z2,z38,z4,z5,z6,z16]),(0,[z1,z2,z3,z32,z50,z5,z6]),(0,[z2,z3,z4,z5,z28,z6,z41]),(0,[z1,z2,z3,z32,z4,z5,z79])],[(0,[z1,z2,z80,z3,z4,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z82]),(0,[z7,z83,z2,z3,z4,z5,z6]),(1,[z1,z2,z84,z4,z22,z6])],[(0,[z1,z85,z2,z3,z4,z5,z6])],[(0,[z86,z1,z2,z3,z4,z87,z6]),(0,[z1,z2,z38,z18,z4,z5,z6]),(0,[z1,z2,z88,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z6])],[(0,[z1,z90,z2,z38,z4,z5,z6]),(0,[z1,z39,z36,z3,z4,z5,z6]),(0,[z1,z2,z3,z91,z4,z5,z6])],[(0,[z1,z2,z3,z4,z92,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z93]),(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z95,z4,z5,z6])],[(0,[z96,z86,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z97,z4,z5,z6]),(0,[z1,z2,z98,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z99,z6]),(0,[z1,z2,z3,z4,z50,z11,z6]),(0,[z1,z2,z3,z100,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z101])],[(0,[z86,z1,z2,z3,z4,z5,z102]),(0,[z1,z103,z2,z3,z4,z5,z6]),(0,[z104,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z105,z5,z6])],[(0,[z1,z106,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6])],[(0,[z1,z24,z3,z4,z5,z108,z6]),(0,[z1,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z109,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z99,z6])],[(0,[z1,z2,z3,z4,z5,z6,z110]),(0,[z1,z2,z3,z50,z5,z19,z6]),(0,[z111,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z112,z6]),(0,[z1,z2,z3,z4,z5,z113,z6]),(0,[z1,z2,z3,z4,z5,z114,z6]),(0,[z1,z115,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z116])],[(0,[z117,z1,z2,z3,z4,z5,z6]),(0,[z1,z20,z3,z33,z4,z5,z6]),(0,[z1,z59,z20,z3,z4,z5,z6]),(0,[z1,z118,z2,z3,z4,z5,z28]),(0,[z1,z119,z2,z3,z4,z5,z6]),(0,[z1,z2,z120,z3,z32,z4,z5])]],
   [[(0,[z1,z121,z2,z3,z4,z5,z6]),(0,[z1,z122,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z123,z6])],[(0,[z1,z36,z2,z3,z50,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z124]),(1,[z1,z2,z120,z4,z5,z23])],[(0,[z1,z20,z3,z4,z5,z79,z6]),(1,[z1,z2,z3,z50,z5,z41]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z1,z125,z2,z3,z61,z5,z6]),(0,[z1,z59,z68,z3,z4,z5,z6])],[(1,[z1,z2,z126,z4,z5,z6]),(0,[z1,z2,z3,z4,z45,z5,z6]),(0,[z1,z2,z3,z4,z5,z127,z6]),(0,[z1,z2,z3,z4,z5,z128,z6])],[(0,[z1,z20,z84,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z87,z6]),(1,[z1,z129,z2,z4,z48,z6])],[(0,[z1,z20,z3,z18,z4,z5,z6]),(0,[z1,z2,z20,z10,z4,z5,z6]),(0,[z1,z2,z20,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z11,z79,z6]),(0,[z130,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z131,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z133,z6]),(0,[z1,z2,z84,z3,z134,z4,z6])],[(0,[z1,z2,z10,z4,z5,z19,z6]),(0,[z1,z135,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z136,z4,z5,z6]),(0,[z1,z2,z3,z137,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z22,z6]),(0,[z64,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z120,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z138,z5,z6]),(0,[z1,z2,z3,z4,z139,z5,z6]),(0,[z1,z2,z3,z4,z92,z70,z6])],[(1,[z1,z2,z3,z4,z5,z102]),(0,[z1,z2,z3,z4,z140,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z41,z41]),(0,[z1,z2,z3,z4,z5,z6,z142]),(0,[z1,z2,z3,z143,z4,z5,z6]),(0,[z1,z2,z144,z3,z4,z5,z6])],[(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z1,z2,z145,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z146,z5,z6]),(0,[z1,z2,z3,z147,z4,z5,z6])],[(0,[z1,z2,z3,z134,z4,z5,z28])],[(0,[z132,z1,z2,z3,z131,z5,z6]),(0,[z1,z24,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z33,z50,z5,z6]),(0,[z1,z2,z3,z148,z4,z5,z6]),(0,[z1,z2,z3,z4,z149,z5,z6])],[(0,[z1,z2,z3,z32,z4,z19,z6]),(0,[z78,z1,z145,z3,z4,z5,z6]),(0,[z1,z150,z2,z3,z4,z5,z6])],[(0,[z1,z151,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z10,z4,z5,z6,z56]),(0,[z152,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z6]),(0,[z1,z2,z3,z154,z4,z11,z6]),(0,[z1,z2,z3,z134,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z155])],[(0,[z132,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z18,z92,z5,z6]),(0,[z1,z2,z3,z4,z156,z5,z6])],[(0,[z1,z2,z38,z3,z4,z11,z6]),(0,[z1,z2,z84,z3,z50,z5,z6])],[(0,[z1,z90,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z18,z50,z5,z6]),(0,[z1,z125,z2,z3,z4,z5,z41]),(0,[z1,z125,z90,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z157,z27,z6]),(0,[z1,z44,z2,z3,z4,z5,z56])],[],[(1,[z1,z2,z3,z146,z5,z6])],[(0,[z1,z2,z3,z4,z158,z5,z6]),(0,[z1,z2,z3,z4,z5,z159,z6])],[(0,[z111,z1,z160,z3,z4,z5,z6])],[(0,[z1,z1,z2,z10,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z19,z6]),(0,[z1,z2,z3,z161,z50,z5,z6]),(0,[z1,z1,z2,z3,z4,z19,z6])],[(0,[z1,z59,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z48,z5,z28]),(0,[z1,z2,z3,z4,z5,z162,z6]),(0,[z163,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z164,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z69,z6]),(0,[z1,z2,z3,z4,z165,z5,z6]),(0,[z166,z1,z2,z3,z4,z5,z6])],[(0,[z1,z24,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z11,z5,z6]),(0,[z1,z2,z3,z4,z92,z5,z41])],[(0,[z51,z1,z2,z10,z4,z5,z6]),(1,[z1,z2,z167,z4,z5,z6]),(0,[z1,z36,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z168,z4,z5,z6])],[(1,[z1,z2,z10,z4,z5,z41]),(0,[z1,z2,z3,z4,z50,z5,z41]),(1,[z1,z2,z3,z4,z19,z41]),(0,[z1,z169,z2,z3,z4,z5,z6]),(0,[z1,z170,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z48,z5,z6])],[(0,[z1,z2,z3,z4,z5,z41,z171]),(0,[z172,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z28,z28])]],
   [[(0,[z1,z35,z2,z3,z4,z11,z6]),(0,[z1,z2,z173,z4,z5,z27,z6])],[(0,[z1,z90,z20,z3,z4,z5,z6]),(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z175,z11,z6]),(0,[z1,z176,z2,z3,z4,z175,z6]),(0,[z1,z2,z3,z177,z4,z5,z6])],[(0,[z1,z2,z3,z178,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z180,z6])],[(0,[z64,z1,z2,z10,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z19,z6]),(1,[z1,z2,z3,z4,z5,z82]),(0,[z1,z2,z3,z4,z5,z28,z6]),(0,[z1,z2,z3,z4,z181,z5,z41]),(0,[z1,z2,z3,z182,z4,z5,z6])],[(0,[z183,z1,z2,z126,z4,z5,z6]),(0,[z1,z24,z3,z32,z4,z5,z6]),(0,[z1,z125,z2,z3,z18,z5,z6]),(0,[z111,z78,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z69,z41]),(0,[z1,z184,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z185,z56])],[(0,[z1,z186,z20,z3,z4,z5,z6]),(0,[z1,z187,z2,z38,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z188]),(0,[z1,z2,z3,z33,z100,z5,z6])],[(0,[z1,z189,z2,z3,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z6])],[(0,[z1,z190,z24,z3,z4,z5,z6]),(0,[z191,z1,z2,z10,z4,z5,z6]),(0,[z51,z1,z2,z192,z4,z5,z6])],[(0,[z86,z1,z2,z3,z4,z11,z6]),(0,[z1,z193,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z194,z50,z5,z6]),(0,[z111,z1,z2,z3,z45,z5,z6]),(1,[z2,z3,z4,z5,z28,z41])],[(0,[z1,z2,z3,z4,z195,z5,z6])],[(0,[z51,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z196,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z197,z5,z6]),(0,[z1,z198,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z199,z6])],[(1,[z1,z2,z3,z4,z133,z6]),(0,[z1,z2,z3,z200,z50,z5,z6]),(0,[z1,z2,z120,z3,z4,z5,z41])],[(0,[z1,z20,z3,z4,z201,z5,z6]),(0,[z7,z1,z2,z3,z4,z11,z6]),(0,[z1,z202,z2,z3,z4,z5,z6]),(1,[z1,z2,z173,z4,z5,z6]),(0,[z1,z2,z3,z203,z4,z5,z6])],[(0,[z1,z2,z84,z10,z4,z5,z6]),(0,[z1,z2,z84,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z6,z204])],[(1,[z1,z2,z10,z18,z5,z6]),(1,[z1,z2,z3,z18,z19,z6]),(0,[z1,z2,z3,z18,z4,z19,z6]),(0,[z1,z2,z3,z4,z19,z70,z6]),(0,[z1,z2,z84,z3,z4,z22,z6])],[(0,[z1,z2,z3,z205,z18,z5,z6])]],
   [[(1,[z1,z2,z3,z206,z5,z6]),(1,[z1,z20,z38,z4,z5,z6]),(0,[z1,z20,z3,z4,z5,z6,z207]),(0,[z1,z2,z3,z208,z4,z5,z6]),(0,[z1,z2,z3,z209,z4,z5,z6])],[(0,[z1,z187,z2,z3,z18,z5,z6]),(0,[z1,z176,z2,z3,z4,z11,z6]),(0,[z1,z210,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z211,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z131,z5,z6]),(0,[z1,z2,z213,z10,z4,z5,z6]),(0,[z1,z214,z2,z3,z4,z19,z6]),(1,[z1,z2,z3,z4,z11,z28]),(0,[z1,z215,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z216,z6]),(0,[z1,z2,z3,z18,z217,z5,z6]),(0,[z1,z2,z3,z4,z11,z218,z6]),(0,[z1,z2,z3,z154,z4,z5,z41]),(0,[z1,z2,z3,z4,z219,z5,z6]),(0,[z1,z2,z3,z220,z4,z221,z6])],[(0,[z1,z59,z2,z10,z4,z5,z6]),(0,[z1,z59,z2,z3,z4,z19,z6])],[(0,[z191,z1,z20,z3,z4,z5,z6]),(0,[z132,z1,z2,z222,z4,z5,z6]),(0,[z1,z24,z2,z3,z50,z5,z6]),(0,[z1,z2,z38,z4,z11,z5,z6]),(0,[z1,z68,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z6,z223]),(0,[z1,z2,z3,z4,z5,z6,z224])],[(0,[z1,z2,z3,z50,z5,z69,z6]),(1,[z1,z2,z3,z4,z11,z6])],[(0,[z1,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z225]),(1,[z1,z2,z196,z25,z5,z6]),(0,[z1,z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z227,z5,z6])],[(0,[z1,z68,z2,z3,z4,z5,z69])],[(0,[z1,z24,z3,z4,z5,z99,z6]),(0,[z1,z2,z10,z205,z4,z5,z6]),(0,[z1,z2,z3,z228,z4,z11,z6]),(0,[z1,z229,z2,z3,z4,z5,z6])],[(0,[z1,z68,z2,z38,z4,z5,z6]),(1,[z1,z2,z230,z4,z5,z6]),(0,[z1,z2,z3,z4,z231,z19,z6]),(0,[z1,z2,z3,z232,z4,z19,z6]),(0,[z1,z233,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z234,z4,z5,z6]),(0,[z1,z2,z3,z235,z4,z217,z6])],[(0,[z1,z36,z24,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z236,z6]),(0,[z1,z90,z2,z3,z50,z5,z6]),(1,[z1,z2,z3,z4,z5,z237]),(1,[z1,z2,z3,z4,z5,z238])],[(1,[z1,z20,z3,z18,z5,z6]),(1,[z1,z24,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z19,z28,z6]),(0,[z83,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z239,z4,z5,z6])],[(0,[z1,z2,z10,z4,z240,z5,z6]),(0,[z1,z2,z3,z4,z217,z5,z41]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z242,z4,z5,z6])],[(0,[z1,z24,z3,z33,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z1,z244,z2,z3,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z69,z6]),(0,[z1,z2,z4,z5,z23,z6,z245])]],
   [[(0,[z96,z1,z2,z3,z4,z11,z6]),(0,[z246,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z247,z4,z5,z6])],[(0,[z1,z24,z3,z4,z5,z79,z6]),(0,[z1,z24,z3,z4,z5,z6,z16]),(0,[z1,z2,z3,z4,z19,z248,z6]),(0,[z1,z2,z3,z249,z4,z11,z6]),(0,[z1,z250,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z251,z5,z6])],[(0,[z64,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z22,z6]),(0,[z1,z125,z176,z3,z4,z5,z6])],[(0,[z1,z24,z84,z3,z4,z5,z6]),(0,[z1,z2,z252,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z6,z41])],[(0,[z1,z20,z3,z4,z11,z5,z6]),(0,[z1,z20,z196,z3,z4,z5,z6]),(0,[z1,z24,z3,z18,z4,z5,z6]),(0,[z86,z1,z253,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z50,z5,z6]),(0,[z1,z254,z2,z3,z4,z5,z6]),(0,[z1,z44,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z255,z5,z6]),(0,[z1,z2,z3,z256,z4,z5,z6]),(0,[z1,z257,z2,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z6,z16]),(0,[z83,z1,z2,z3,z4,z258,z6]),(0,[z1,z2,z4,z259,z221,z5,z6]),(0,[z1,z2,z3,z4,z5,z260,z6]),(0,[z261,z1,z2,z3,z4,z5,z6])],[(0,[z191,z1,z24,z3,z4,z5,z6]),(0,[z1,z68,z2,z3,z18,z5,z6])],[(0,[z1,z262,z2,z3,z4,z11,z6]),(0,[z1,z2,z263,z3,z4,z5,z6])],[(0,[z1,z43,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z153]),(0,[z1,z2,z3,z4,z11,z6,z16]),(0,[z1,z264,z2,z3,z4,z5,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z187,z2,z4,z5,z6,z245]),(0,[z1,z44,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z25,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z266,z6])],[(0,[z1,z2,z3,z4,z5,z6,z267]),(1,[z2,z38,z10,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z268,z6]),(0,[z1,z2,z3,z10,z4,z11,z6]),(1,[z1,z2,z38,z50,z5,z6]),(0,[z1,z2,z3,z50,z5,z6,z56]),(0,[z1,z269,z2,z3,z4,z11,z6]),(0,[z1,z2,z270,z3,z4,z5,z6]),(0,[z1,z3,z4,z271,z217,z5,z6])],[(0,[z1,z2,z3,z4,z206,z5,z6]),(0,[z1,z272,z2,z3,z4,z5,z6]),(0,[z1,z273,z2,z3,z4,z5,z28]),(1,[z1,z150,z3,z4,z175,z6])],[(1,[z1,z2,z274,z4,z5,z6]),(0,[z1,z129,z2,z84,z4,z5,z6])],[(1,[z1,z24,z3,z18,z5,z6]),(0,[z1,z2,z275,z3,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z5,z41]),(0,[z1,z150,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z25,z4,z5,z6]),(0,[z276,z1,z2,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z277,z6]),(0,[z1,z2,z10,z154,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z278,z6])],[(0,[z191,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z279,z3,z4,z5,z6]),(0,[z1,z3,z61,z4,z5,z69,z6]),(0,[z1,z3,z4,z5,z69,z6,z60]),(0,[z1,z273,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z24,z2,z3,z4,z19,z6]),(0,[z1,z2,z38,z4,z5,z69,z6]),(0,[z1,z2,z3,z4,z221,z11,z6]),(0,[z1,z36,z2,z25,z4,z5,z6])],[(0,[z183,z1,z2,z3,z206,z5,z6])],[(0,[z1,z2,z196,z3,z50,z5,z6]),(0,[z1,z2,z3,z280,z4,z5,z6]),(0,[z7,z1,z2,z281,z4,z5,z6])],[(0,[z1,z59,z24,z3,z4,z5,z6]),(0,[z1,z129,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z282,z5,z6]),(0,[z1,z283,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z70,z28]),(0,[z1,z273,z2,z3,z25,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z284,z6])],[(1,[z1,z285,z3,z4,z5,z6]),(0,[z1,z90,z2,z3,z4,z19,z6])],[(0,[z183,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z286,z10,z4,z5,z6]),(0,[z287,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z10,z4,z217,z5,z6]),(0,[z51,z1,z2,z3,z4,z288,z6]),(1,[z78,z2,z3,z4,z11,z6]),(0,[z78,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z289,z4,z5,z6]),(0,[z1,z2,z3,z4,z290,z5,z6]),(0,[z1,z2,z3,z32,z4,z5,z56]),(0,[z1,z2,z3,z4,z5,z70,z6])],[(0,[z64,z1,z2,z3,z4,z5,z291]),(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z2,z3,z4,z293,z5,z6]),(1,[z1,z2,z3,z134,z27,z6])],[(0,[z1,z2,z274,z3,z4,z5,z6]),(1,[z1,z2,z222,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z294]),(0,[z1,z295,z2,z3,z4,z5,z6]),(0,[z1,z35,z2,z3,z32,z4,z5])],[(0,[z1,z125,z2,z38,z4,z5,z6]),(0,[z1,z2,z296,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z297,z6])],[(0,[z1,z106,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z298]),(0,[z1,z2,z38,z4,z5,z22,z6]),(0,[z111,z1,z2,z167,z4,z5,z6]),(1,[z1,z2,z281,z4,z5,z6]),(0,[z1,z2,z3,z299,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z6,z300]),(0,[z78,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z301]),(0,[z1,z302,z2,z3,z4,z5,z6])],[(0,[z183,z1,z2,z3,z303,z5,z6]),(0,[z1,z39,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z304])],[(0,[z51,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z305,z3,z4,z5,z6]),(0,[z1,z306,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z100,z4,z5,z41])],[(0,[z307,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z76])],[(0,[z1,z2,z3,z4,z5,z308,z6]),(0,[z1,z2,z3,z4,z5,z309,z6])],[(0,[z1,z20,z3,z4,z5,z310,z6]),(0,[z1,z2,z3,z4,z5,z6,z311])],[(0,[z1,z2,z38,z4,z5,z6,z56]),(0,[z1,z312,z2,z3,z4,z5,z6])],[(1,[z1,z2,z38,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z237,z6]),(0,[z1,z2,z3,z61,z4,z11,z6]),(0,[z1,z2,z3,z235,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z108,z6]),(0,[z1,z313,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z92,z5,z70])],[(0,[z1,z2,z3,z4,z314,z5,z6]),(0,[z1,z315,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z28,z316]),(0,[z1,z2,z3,z4,z5,z248,z28]),(0,[z1,z2,z3,z134,z4,z27,z6])],[(0,[z1,z2,z3,z4,z5,z317,z6])],[(0,[z78,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z18,z221,z5,z6]),(0,[z1,z2,z3,z4,z318,z5,z6]),(0,[z1,z2,z3,z4,z5,z319,z6])],[(0,[z1,z20,z3,z4,z5,z19,z6]),(0,[z1,z2,z3,z18,z5,z6,z245]),(0,[z191,z1,z2,z3,z4,z19,z6])],[(0,[z1,z20,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z4,z5,z320,z6]),(0,[z1,z2,z321,z38,z4,z5,z6]),(0,[z1,z322,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z248,z6])],[],[(0,[z183,z1,z2,z274,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z19,z6]),(0,[z1,z2,z196,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z6,z41]),(0,[z1,z2,z3,z4,z5,z28,z245]),(0,[z323,z1,z2,z3,z4,z5,z6])],[(0,[z1,z24,z3,z4,z324,z5,z6]),(0,[z1,z2,z3,z4,z11,z22,z6]),(0,[z1,z2,z3,z4,z5,z28,z60]),(0,[z1,z2,z3,z4,z259,z5,z6]),(1,[z1,z2,z3,z235,z4,z6])],[(0,[z1,z24,z24,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z297,z27,z6]),(0,[z1,z2,z3,z5,z79,z6,z56])]],
   [[(0,[z1,z2,z3,z50,z92,z5,z6]),(0,[z1,z2,z3,z4,z74,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z325])],[(0,[z1,z2,z3,z100,z18,z5,z6]),(0,[z326,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z28,z14]),(0,[z327,z1,z2,z3,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z92,z6])],[(0,[z1,z2,z3,z50,z50,z5,z6]),(0,[z1,z328,z2,z3,z18,z5,z6]),(0,[z1,z150,z2,z3,z4,z175,z6]),(0,[z1,z2,z196,z3,z217,z5,z6])],[(0,[z1,z2,z120,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z221,z5,z41]),(0,[z1,z2,z3,z4,z146,z5,z6])],[(0,[z1,z2,z3,z329,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z330]),(0,[z1,z331,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z332,z4,z5,z6]),(0,[z1,z2,z333,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z334,z5,z6]),(0,[z1,z90,z24,z3,z4,z5,z6]),(1,[z1,z55,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z207])],[(0,[z111,z1,z2,z3,z4,z11,z6]),(0,[z1,z129,z2,z3,z4,z5,z41])],[(0,[z1,z2,z3,z4,z5,z335,z6]),(0,[z132,z1,z2,z3,z4,z5,z41]),(0,[z1,z125,z2,z10,z4,z5,z6]),(1,[z64,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z50,z240,z5,z6]),(0,[z1,z2,z3,z18,z5,z6,z336]),(0,[z1,z39,z2,z154,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z337]),(0,[z1,z338,z2,z3,z4,z5,z6])],[(0,[z132,z1,z2,z3,z4,z158,z6]),(0,[z1,z2,z38,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z19,z99,z6]),(0,[z1,z2,z3,z4,z5,z339,z6])],[(0,[z1,z2,z10,z4,z92,z5,z6]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z341])],[(0,[z183,z1,z2,z3,z4,z5,z41]),(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z343,z5,z6])],[(0,[z1,z344,z24,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z50,z5,z6]),(0,[z1,z2,z10,z100,z4,z5,z6]),(0,[z64,z1,z2,z345,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z238]),(0,[z346,z1,z2,z3,z4,z5,z6])],[(0,[z1,z273,z2,z196,z4,z5,z6])],[(0,[z1,z2,z3,z18,z175,z5,z6]),(0,[z111,z2,z3,z4,z5,z19,z6]),(0,[z1,z2,z3,z347,z4,z5,z6])],[(0,[z51,z1,z24,z3,z4,z5,z6]),(1,[z1,z80,z3,z4,z5,z6]),(1,[z1,z81,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z19,z6]),(0,[z1,z2,z3,z4,z5,z6,z349]),(0,[z1,z350,z2,z3,z4,z5,z6])],[(0,[z1,z2,z120,z3,z18,z5,z6]),(0,[z351,z1,z2,z3,z4,z5,z6]),(0,[z1,z44,z68,z2,z3,z4,z5])]],
   [[(1,[z1,z2,z3,z303,z5,z6]),(0,[z1,z2,z20,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z19,z79,z6]),(0,[z1,z129,z2,z3,z33,z4,z6]),(0,[z1,z2,z3,z4,z70,z6,z16])],[(0,[z1,z2,z3,z4,z5,z6,z171]),(0,[z1,z2,z3,z4,z5,z352,z6]),(0,[z1,z2,z3,z4,z5,z6,z353])],[(0,[z1,z2,z3,z200,z4,z5,z6]),(1,[z1,z2,z3,z4,z258,z6]),(0,[z354,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z355,z3,z4,z5,z6])],[(0,[z1,z24,z3,z4,z11,z5,z6]),(0,[z1,z24,z196,z3,z4,z5,z6]),(0,[z1,z356,z2,z3,z4,z5,z6])],[(0,[z1,z2,z20,z3,z4,z5,z6]),(1,[z1,z24,z38,z4,z5,z6]),(0,[z1,z187,z2,z10,z4,z5,z6]),(0,[z1,z344,z2,z3,z50,z5,z6]),(0,[z1,z187,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z134,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z357,z6]),(1,[z1,z2,z3,z358,z4,z6]),(0,[z1,z359,z2,z3,z4,z5,z6])],[(0,[z1,z125,z20,z3,z4,z5,z6]),(0,[z1,z2,z360,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z361,z6]),(0,[z362,z1,z2,z3,z4,z5,z6])],[(0,[z1,z285,z2,z3,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z5,z41])],[(0,[z1,z190,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z154,z18,z5,z6]),(0,[z1,z2,z3,z4,z175,z5,z41]),(1,[z1,z363,z3,z4,z5,z6])],[(0,[z132,z1,z2,z3,z18,z5,z6]),(0,[z96,z1,z80,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z153])],[(0,[z1,z2,z38,z3,z18,z5,z6]),(0,[z1,z2,z3,z32,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z364,z6])],[(0,[z365,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z16]),(0,[z1,z179,z3,z154,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z366]),(0,[z367,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z368,z6])],[(0,[z1,z369,z20,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z50,z5,z6]),(0,[z1,z2,z3,z4,z370,z5,z6])],[(0,[z1,z371,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z372,z6]),(0,[z1,z363,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z32,z4,z5,z6])],[(0,[z1,z2,z10,z4,z221,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z6,z373]),(0,[z1,z374,z2,z3,z4,z5,z41])],[(1,[z1,z20,z10,z4,z5,z6]),(1,[z1,z20,z3,z4,z19,z6]),(0,[z1,z2,z10,z4,z5,z6,z245]),(0,[z1,z129,z2,z3,z4,z48,z6]),(0,[z1,z2,z3,z4,z5,z375,z6]),(0,[z1,z2,z3,z376,z4,z5,z6])]],
   [[(0,[z1,z377,z2,z3,z4,z5,z6]),(0,[z1,z35,z2,z3,z33,z4,z6]),(0,[z1,z2,z378,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z48,z11,z6]),(0,[z1,z90,z2,z3,z221,z5,z6])],[(0,[z1,z187,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z217,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z41])],[(0,[z1,z1,z2,z3,z4,z5,z28])],[(0,[z379,z1,z2,z3,z4,z5,z6])],[(0,[z132,z1,z2,z3,z380,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z298]),(1,[z1,z253,z3,z4,z5,z6]),(0,[z1,z39,z2,z38,z4,z5,z6]),(1,[z1,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z218,z6]),(0,[z1,z2,z3,z381,z4,z5,z6]),(0,[z1,z44,z2,z3,z4,z92,z5])],[(0,[z1,z2,z3,z126,z4,z5,z6]),(0,[z1,z382,z2,z3,z50,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z5,z267]),(0,[z1,z35,z2,z3,z18,z5,z6]),(0,[z1,z176,z2,z3,z4,z5,z41]),(0,[z1,z36,z2,z3,z4,z5,z28]),(0,[z1,z383,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z242,z4,z6]),(0,[z1,z44,z2,z3,z32,z5,z6])],[],[(0,[z1,z2,z3,z72,z4,z5,z6]),(0,[z1,z68,z2,z10,z4,z5,z6]),(0,[z1,z384,z2,z3,z50,z5,z6])],[(0,[z1,z2,z3,z18,z5,z23,z6]),(0,[z1,z179,z2,z3,z4,z11,z6]),(1,[z1,z273,z2,z217,z5,z6]),(0,[z1,z44,z35,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z6,z385,z56])],[(0,[z1,z36,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z92,z5,z16])],[(1,[z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z386,z6]),(0,[z1,z2,z3,z4,z5,z6,z387])],[(1,[z1,z2,z3,z4,z158,z6]),(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z1,z2,z3,z4,z389,z5,z6])],[(0,[z64,z1,z2,z3,z4,z5,z28]),(1,[z1,z390,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z197,z11,z6]),(0,[z1,z2,z3,z4,z5,z99,z28]),(0,[z1,z2,z3,z4,z5,z6,z391]),(0,[z1,z2,z3,z392,z4,z5,z6])],[(0,[z86,z1,z2,z3,z18,z5,z6]),(0,[z1,z125,z2,z3,z50,z5,z6])]],
   [[(0,[z1,z393,z2,z3,z4,z5,z6])],[(0,[z1,z176,z2,z3,z33,z4,z6]),(0,[z1,z2,z196,z25,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z69,z6]),(0,[z1,z2,z10,z4,z175,z5,z6]),(0,[z1,z2,z38,z154,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z83,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z99,z6]),(0,[z1,z2,z3,z4,z394,z5,z6]),(0,[z1,z395,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z396])],[(0,[z1,z187,z24,z3,z4,z5,z6]),(0,[z2,z38,z3,z10,z4,z5,z6]),(0,[z7,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z33,z4,z5,z28]),(0,[z1,z2,z3,z397,z4,z5,z6]),(0,[z1,z2,z3,z398,z4,z5,z6]),(1,[z1,z2,z3,z4,z394,z5])],[(0,[z1,z2,z3,z399,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z41]),(0,[z1,z2,z84,z25,z4,z5,z6]),(0,[z1,z400,z2,z3,z4,z5,z6])],[(0,[z64,z1,z2,z3,z4,z401,z6]),(0,[z78,z1,z2,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z69,z6]),(0,[z1,z2,z3,z4,z5,z6,z403]),(0,[z1,z2,z3,z4,z404,z5,z6]),(0,[z405,z1,z2,z3,z4,z5,z6])],[(0,[z1,z193,z24,z3,z4,z5,z6]),(0,[z96,z1,z2,z3,z4,z5,z41]),(0,[z1,z406,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z28])],[(0,[z1,z68,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z33,z4,z5,z6])],[(0,[z1,z2,z84,z3,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z407,z6]),(0,[z1,z24,z3,z4,z5,z19,z6]),(1,[z1,z2,z10,z50,z5,z6]),(0,[z64,z1,z2,z3,z4,z408,z6]),(1,[z1,z2,z3,z50,z19,z6]),(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z4,z5,z28]),(1,[z1,z2,z410,z4,z5,z6]),(0,[z1,z2,z3,z411,z4,z5,z6]),(0,[z1,z2,z3,z412,z4,z5,z6])],[(0,[z1,z24,z3,z4,z5,z22,z6]),(0,[z1,z2,z3,z413,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z6]),(1,[z1,z44,z2,z3,z5,z56]),(0,[z1,z2,z3,z4,z5,z6,z16])],[(0,[z96,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z414,z6]),(0,[z1,z2,z3,z415,z4,z5,z6])],[(0,[z1,z2,z38,z4,z217,z5,z6]),(0,[z1,z187,z2,z3,z50,z5,z6]),(0,[z1,z2,z84,z3,z4,z5,z6])],[(1,[z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z18,z4,z5,z6]),(0,[z416,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z417,z5,z6])],[(0,[z1,z2,z3,z18,z5,z6,z60]),(0,[z1,z418,z2,z3,z4,z5,z6])],[(0,[z1,z24,z3,z419,z4,z5,z6]),(0,[z1,z2,z3,z167,z4,z5,z6]),(0,[z83,z1,z2,z410,z4,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z28]),(0,[z420,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z10,z4,z5,z41])],[(0,[z1,z20,z3,z154,z4,z5,z6]),(0,[z1,z39,z2,z10,z4,z5,z6]),(0,[z1,z2,z213,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z12,z6]),(0,[z1,z214,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z421,z4,z5,z6]),(0,[z1,z422,z2,z3,z4,z5,z6])],[(0,[z1,z24,z3,z4,z5,z6,z56]),(0,[z1,z2,z3,z161,z4,z5,z6]),(0,[z1,z423,z2,z3,z4,z5,z6]),(0,[z1,z3,z61,z4,z175,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z424]),(1,[z1,z425,z3,z4,z5,z6])],[(0,[z426,z1,z2,z3,z4,z5,z6]),(0,[z83,z1,z2,z3,z18,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z427,z6])],[(0,[z1,z2,z3,z4,z5,z428,z6])],[(0,[z1,z20,z3,z4,z5,z6,z56]),(0,[z1,z2,z3,z4,z5,z6,z124]),(1,[z1,z187,z2,z4,z5,z245])],[(1,[z1,z20,z3,z50,z5,z6]),(0,[z96,z1,z2,z3,z18,z5,z6]),(0,[z1,z429,z2,z3,z4,z221,z5])],[(0,[z1,z2,z3,z18,z5,z27,z6]),(0,[z1,z2,z430,z3,z4,z5,z41]),(0,[z1,z363,z3,z4,z217,z5,z6])],[(0,[z1,z431,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z1,z2,z3,z232,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z6,z56]),(0,[z1,z176,z3,z61,z4,z5,z6])],[(1,[z1,z2,z3,z380,z5,z6]),(0,[z433,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z434,z6]),(0,[z1,z125,z2,z3,z4,z19,z6])],[(0,[z1,z20,z3,z4,z217,z5,z6]),(0,[z86,z2,z38,z3,z4,z5,z6]),(0,[z1,z2,z3,z33,z4,z27,z6])],[(1,[z1,z2,z3,z4,z5,z267]),(0,[z78,z1,z2,z10,z4,z5,z6]),(0,[z1,z43,z2,z3,z4,z11,z6]),(0,[z1,z44,z2,z3,z4,z11,z6]),(0,[z1,z36,z3,z154,z4,z5,z6]),(0,[z1,z273,z2,z84,z4,z5,z6])],[(0,[z1,z435,z2,z3,z4,z5,z6])],[(0,[z96,z1,z2,z3,z4,z427,z6]),(0,[z1,z129,z2,z38,z4,z5,z6]),(0,[z111,z1,z81,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z436,z5,z6]),(0,[z437,z1,z2,z3,z4,z5,z6])],[(0,[z1,z39,z20,z3,z4,z5,z6]),(0,[z132,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z23,z6]),(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z439,z2,z3,z4,z5,z6]),(0,[z1,z440,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z38,z38,z4,z5,z6])],[(0,[z1,z441,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z10,z18,z5,z6]),(0,[z1,z68,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z25,z4,z11,z6]),(0,[z1,z2,z275,z3,z4,z11,z6])],[(0,[z183,z1,z2,z38,z4,z5,z6]),(0,[z1,z24,z3,z4,z442,z5,z6]),(0,[z443,z1,z2,z3,z4,z5,z6]),(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z194,z4,z5,z6]),(0,[z1,z2,z3,z4,z92,z19,z6]),(0,[z1,z2,z3,z4,z5,z27,z41]),(0,[z1,z2,z3,z4,z5,z6,z445])],[(0,[z1,z2,z3,z4,z19,z6,z16]),(0,[z1,z273,z2,z3,z4,z11,z6]),(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z446])],[(1,[z1,z2,z10,z4,z19,z6]),(0,[z1,z2,z3,z4,z50,z19,z6])],[(0,[z1,z37,z2,z3,z4,z5,z6]),(0,[z1,z150,z2,z3,z4,z11,z6])],[(0,[z1,z2,z3,z4,z5,z57,z41]),(0,[z1,z150,z3,z4,z175,z5,z6]),(0,[z447,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z120,z4,z5,z23,z6])],[(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z86,z1,z2,z3,z448,z5,z6]),(0,[z1,z449,z2,z3,z4,z5,z6]),(0,[z1,z450,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z310,z6]),(1,[z1,z24,z3,z50,z5,z6]),(0,[z96,z1,z2,z3,z4,z372,z6]),(0,[z96,z2,z3,z10,z4,z5,z6]),(0,[z1,z2,z3,z50,z221,z5,z6]),(0,[z1,z2,z3,z4,z5,z451,z6]),(0,[z1,z452,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z50,z5,z6,z245])],[(0,[z78,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z6,z60]),(0,[z1,z129,z2,z3,z18,z5,z6]),(0,[z1,z453,z2,z3,z4,z5,z6])],[(0,[z1,z24,z2,z3,z4,z5,z28]),(0,[z1,z2,z10,z10,z4,z5,z6]),(1,[z1,z2,z454,z4,z5,z6]),(0,[z1,z2,z3,z61,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z28,z93])],[(0,[z455,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z456,z4,z5,z6]),(0,[z1,z44,z59,z2,z3,z4,z5])],[(0,[z1,z2,z3,z230,z4,z5,z6]),(0,[z1,z2,z3,z4,z457,z5,z6]),(0,[z1,z2,z458,z3,z4,z5,z6])],[(0,[z183,z1,z2,z3,z18,z5,z6]),(1,[z1,z2,z3,z4,z5,z298]),(0,[z1,z35,z2,z38,z4,z5,z6]),(1,[z1,z52,z3,z4,z5,z6]),(0,[z1,z176,z2,z3,z4,z99,z6])],[(0,[z1,z24,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z100,z4,z5,z6])]],
   [[(0,[z1,z2,z173,z3,z4,z5,z6])],[(0,[z459,z1,z2,z3,z4,z5,z6]),(0,[z1,z90,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z460,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z5,z70])],[(0,[z1,z2,z120,z10,z4,z5,z6]),(0,[z1,z2,z120,z3,z4,z19,z6]),(0,[z83,z1,z2,z456,z4,z5,z6])],[(0,[z461,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z6,z60]),(0,[z1,z2,z3,z4,z5,z6,z462])],[(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z2,z3,z50,z5,z27,z6]),(0,[z1,z2,z463,z3,z4,z5,z28])],[(0,[z1,z2,z3,z4,z380,z5,z6]),(1,[z1,z2,z3,z464,z5,z6]),(0,[z1,z2,z465,z3,z4,z5,z6]),(0,[z1,z90,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z466,z4,z5,z6])],[(0,[z86,z1,z2,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z324,z5,z6]),(1,[z1,z429,z2,z3,z4,z5]),(0,[z1,z2,z3,z134,z4,z70,z6])],[(0,[z1,z2,z3,z4,z5,z6,z207]),(0,[z1,z24,z3,z4,z92,z5,z6]),(0,[z1,z2,z3,z4,z11,z467,z6]),(1,[z83,z2,z3,z4,z5,z41]),(0,[z1,z2,z463,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z468,z6])],[(0,[z1,z186,z2,z3,z4,z5,z6]),(0,[z1,z125,z24,z3,z4,z5,z6]),(0,[z1,z39,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z18,z140,z5,z6]),(0,[z1,z2,z3,z4,z5,z469,z6]),(0,[z1,z2,z470,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z407,z6]),(0,[z7,z1,z2,z38,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z154,z4,z19,z6]),(0,[z1,z122,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z32,z4,z92,z5])],[(0,[z1,z344,z2,z3,z4,z5,z6]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z83,z1,z2,z3,z464,z5,z6])],[(0,[z1,z20,z3,z4,z92,z5,z6]),(0,[z1,z2,z38,z10,z4,z5,z6]),(0,[z1,z2,z3,z50,z175,z5,z6]),(0,[z1,z2,z3,z61,z18,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z41]),(0,[z1,z68,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z472,z6]),(0,[z1,z2,z3,z4,z5,z6,z473])],[(0,[z132,z1,z2,z474,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z27,z6]),(0,[z1,z475,z2,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z50,z5,z6]),(0,[z1,z20,z3,z100,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z476,z2,z3,z4,z19,z6])],[(0,[z1,z176,z2,z38,z4,z5,z6]),(0,[z1,z477,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z478,z6])]],
   [[(1,[z1,z2,z38,z4,z5,z28]),(0,[z1,z479,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z100,z134,z4,z6])],[(0,[z1,z24,z3,z480,z4,z5,z6]),(0,[z1,z24,z3,z4,z5,z69,z6]),(0,[z1,z2,z3,z4,z19,z310,z6]),(0,[z1,z3,z61,z4,z221,z5,z6])],[(0,[z1,z2,z38,z4,z221,z5,z6]),(0,[z1,z2,z481,z3,z4,z5,z6])],[(1,[z1,z24,z10,z4,z5,z6]),(1,[z1,z24,z3,z4,z19,z6]),(0,[z1,z2,z38,z4,z5,z6,z245])],[(1,[z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z6,z60]),(0,[z78,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z217,z19,z6]),(0,[z7,z1,z2,z3,z482,z5,z6]),(0,[z1,z2,z483,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z124]),(1,[z1,z296,z3,z4,z5,z6]),(0,[z191,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z484,z6]),(0,[z1,z3,z4,z175,z5,z99,z6])],[(0,[z1,z2,z10,z61,z4,z5,z6]),(0,[z1,z485,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z486]),(0,[z1,z425,z2,z3,z4,z5,z6])],[(0,[z1,z487,z2,z4,z221,z5,z6]),(0,[z1,z2,z3,z33,z134,z5,z6])],[(0,[z1,z24,z120,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z19,z6]),(0,[z78,z1,z2,z3,z488,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z28]),(0,[z1,z150,z2,z3,z4,z5,z41]),(0,[z1,z2,z196,z3,z4,z5,z28])],[(0,[z191,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z22,z6]),(1,[z1,z2,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z334,z11,z6]),(0,[z1,z2,z3,z489,z4,z5,z6])],[(0,[z83,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z134,z4,z5,z41])],[(0,[z1,z176,z2,z3,z18,z5,z6]),(0,[z83,z1,z296,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z490]),(0,[z1,z187,z2,z3,z4,z5,z23])],[(0,[z1,z20,z120,z3,z4,z5,z6]),(0,[z1,z2,z3,z100,z50,z5,z6]),(1,[z1,z2,z3,z18,z5,z28]),(0,[z1,z2,z3,z4,z5,z491,z6]),(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z1,z492,z2,z3,z4,z5,z28]),(0,[z1,z493,z2,z3,z4,z5,z6]),(0,[z1,z2,z196,z3,z4,z5,z6])],[(0,[z1,z382,z2,z3,z4,z5,z6]),(0,[z111,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z18,z48,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(0,[z1,z495,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z496,z5,z6])],[(0,[z1,z2,z38,z4,z5,z27,z6]),(1,[z1,z2,z3,z482,z5,z6]),(0,[z1,z2,z3,z497,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z297,z6])],[(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z499,z4,z5,z6])]],
   [[(0,[z1,z24,z3,z154,z4,z5,z6]),(0,[z1,z500,z2,z10,z4,z5,z6]),(0,[z501,z1,z2,z3,z4,z5,z6]),(0,[z1,z384,z2,z3,z4,z5,z6]),(0,[z1,z492,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z464,z5,z6]),(0,[z1,z2,z3,z502,z4,z5,z6])],[(0,[z1,z2,z196,z3,z25,z5,z6])],[(0,[z1,z20,z3,z4,z5,z6,z245]),(0,[z1,z2,z3,z4,z5,z236,z6]),(0,[z1,z2,z321,z3,z50,z5,z6]),(0,[z1,z2,z3,z503,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z277,z28]),(0,[z1,z150,z2,z3,z33,z4,z6]),(0,[z1,z2,z3,z4,z504,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z505])],[(0,[z1,z2,z3,z18,z5,z28,z6]),(0,[z1,z2,z3,z4,z5,z28,z311]),(0,[z1,z506,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z507])],[(0,[z51,z2,z3,z18,z4,z5,z6]),(0,[z1,z39,z2,z3,z4,z19,z6]),(0,[z78,z1,z2,z3,z4,z5,z508]),(0,[z1,z2,z3,z4,z5,z6,z509])],[(0,[z510,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z1,z125,z2,z3,z221,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z511])],[(0,[z1,z20,z38,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z277,z6]),(0,[z7,z1,z2,z10,z4,z5,z6]),(0,[z1,z2,z38,z4,z175,z5,z6]),(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z129,z2,z3,z134,z4,z6])],[(0,[z1,z210,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z48,z5,z41]),(1,[z1,z39,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z513])],[(0,[z1,z2,z20,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z514]),(0,[z1,z2,z3,z4,z515,z5,z6])],[(1,[z132,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z23,z6]),(0,[z1,z273,z187,z2,z4,z5,z6])],[(0,[z1,z24,z3,z4,z217,z5,z6]),(0,[z1,z2,z120,z3,z50,z5,z6]),(0,[z1,z2,z3,z18,z5,z6,z41]),(1,[z1,z2,z3,z220,z4,z6]),(0,[z1,z2,z3,z516,z4,z5,z6])],[(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z407,z6]),(0,[z1,z68,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z134,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z56]),(0,[z1,z187,z2,z25,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z518])],[(0,[z1,z2,z3,z4,z271,z5,z6]),(0,[z1,z2,z3,z33,z100,z4,z6])],[(0,[z1,z476,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z6]),(0,[z83,z1,z377,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z28,z41]),(0,[z1,z2,z3,z519,z4,z5,z6])],[(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z345,z3,z4,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z60])],[(0,[z78,z1,z2,z3,z4,z19,z6])]],
   [[(0,[z86,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z430,z38,z4,z5,z6]),(0,[z1,z179,z2,z3,z4,z5,z41]),(0,[z1,z125,z179,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z521,z5,z6])],[(0,[z522,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z372,z6]),(0,[z1,z2,z3,z32,z4,z11,z6]),(0,[z1,z523,z2,z3,z4,z5,z6])],[(1,[z1,z2,z474,z4,z5,z6]),(0,[z1,z524,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z154,z50,z5,z6]),(1,[z1,z2,z88,z4,z5,z6])],[(0,[z132,z1,z2,z3,z50,z5,z6])],[(0,[z7,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z38,z3,z50,z5,z6]),(0,[z1,z2,z360,z3,z4,z5,z6]),(1,[z1,z2,z3,z177,z4,z6])],[(0,[z1,z20,z3,z4,z175,z5,z6]),(0,[z1,z2,z10,z134,z4,z5,z6]),(0,[z1,z2,z3,z164,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z525,z6])],[(0,[z1,z193,z2,z3,z4,z5,z6]),(0,[z83,z1,z2,z10,z4,z5,z6]),(0,[z1,z35,z2,z3,z134,z4,z6]),(0,[z1,z35,z2,z3,z4,z5,z16]),(0,[z526,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z291]),(0,[z1,z2,z3,z100,z4,z19,z6]),(0,[z527,z1,z2,z3,z4,z5,z6])],[(0,[z1,z35,z2,z3,z4,z6,z16])],[(0,[z78,z1,z254,z3,z4,z5,z6])],[(0,[z96,z1,z2,z10,z4,z5,z6]),(0,[z1,z42,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z1,z2,z3,z208,z4,z5,z41]),(0,[z1,z529,z2,z3,z4,z5,z6]),(0,[z1,z530,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z531,z4,z5,z6])],[(1,[z1,z2,z192,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z288,z6]),(0,[z1,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z532,z4,z5,z6])],[(0,[z533,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z216,z6])],[],[(1,[z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z19,z28]),(0,[z1,z2,z3,z534,z4,z5,z6])],[(0,[z1,z36,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z22,z28]),(0,[z1,z535,z2,z3,z4,z5,z6]),(0,[z1,z44,z2,z120,z3,z4,z5]),(0,[z536,z1,z2,z3,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z11,z41])],[(0,[z1,z179,z2,z3,z18,z5,z6]),(0,[z1,z2,z456,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z537,z6])],[(1,[z96,z2,z10,z4,z5,z6]),(0,[z1,z2,z10,z4,z48,z5,z6]),(0,[z1,z2,z3,z4,z401,z5,z6]),(0,[z1,z35,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z19,z6])],[(0,[z1,z39,z24,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z23,z6]),(0,[z51,z1,z2,z230,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z538,z6]),(0,[z1,z2,z3,z4,z5,z22,z6])],[(0,[z83,z1,z20,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z237]),(0,[z1,z65,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z539,z6])],[(0,[z1,z2,z3,z4,z540,z5,z6]),(0,[z1,z2,z541,z3,z4,z5,z6])],[(0,[z1,z2,z38,z134,z4,z5,z6]),(0,[z64,z1,z2,z3,z4,z11,z6]),(0,[z1,z542,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z448,z4,z5,z6]),(0,[z1,z150,z176,z3,z4,z5,z6]),(0,[z1,z176,z2,z3,z134,z4,z6]),(0,[z1,z2,z3,z4,z5,z543,z6]),(0,[z1,z2,z3,z32,z5,z79,z6])],[(0,[z96,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z419,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z28,z6]),(1,[z1,z2,z3,z448,z5,z6]),(0,[z1,z125,z59,z3,z4,z5,z6])],[(0,[z1,z2,z286,z3,z4,z5,z6])],[(0,[z86,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z221,z19,z6]),(0,[z1,z273,z2,z4,z217,z5,z6])],[(0,[z1,z544,z20,z3,z4,z5,z6]),(0,[z1,z315,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z208,z18,z5,z6]),(0,[z1,z2,z3,z33,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z56])],[(0,[z1,z2,z3,z545,z4,z5,z6]),(1,[z1,z313,z2,z4,z5,z6])],[(0,[z1,z24,z3,z4,z50,z5,z6]),(0,[z1,z24,z3,z100,z4,z5,z6]),(0,[z1,z2,z546,z10,z4,z5,z6]),(0,[z1,z129,z2,z10,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z547,z6]),(0,[z1,z129,z2,z3,z4,z19,z6]),(0,[z78,z1,z2,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z548,z6])],[(0,[z132,z1,z2,z10,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z19,z6]),(0,[z78,z1,z24,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z50,z5,z6]),(0,[z1,z549,z2,z3,z4,z5,z6]),(0,[z1,z550,z2,z3,z4,z5,z6])],[(0,[z1,z2,z10,z4,z197,z5,z6]),(0,[z1,z2,z38,z3,z4,z19,z6]),(0,[z1,z150,z2,z3,z4,z99,z6]),(0,[z1,z44,z187,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z19,z69,z6]),(0,[z1,z2,z84,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z551,z27])],[(0,[z183,z1,z2,z10,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z19,z6]),(0,[z1,z24,z3,z4,z5,z552,z6]),(0,[z1,z2,z3,z18,z4,z11,z6])],[(0,[z1,z20,z3,z4,z5,z23,z6]),(0,[z1,z2,z3,z4,z427,z5,z6]),(0,[z1,z121,z2,z38,z4,z5,z6]),(0,[z1,z44,z2,z3,z4,z5,z41]),(0,[z1,z179,z3,z61,z4,z5,z6]),(1,[z1,z553,z2,z3,z4,z5])],[],[(0,[z111,z1,z2,z38,z4,z5,z6]),(1,[z1,z2,z3,z50,z5,z28]),(0,[z1,z2,z3,z4,z19,z6,z490]),(0,[z1,z2,z3,z4,z554,z5,z6]),(0,[z1,z2,z555,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z556,z6]),(0,[z1,z557,z2,z3,z4,z5,z6])],[(0,[z1,z558,z20,z3,z4,z5,z6])],[(0,[z1,z59,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z258,z5,z6]),(0,[z1,z2,z3,z25,z4,z5,z41]),(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z1,z176,z3,z4,z5,z99,z6])],[(1,[z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z18,z5,z70,z6]),(0,[z1,z39,z2,z25,z4,z5,z6]),(0,[z1,z560,z2,z3,z4,z5,z6])],[(0,[z561,z1,z2,z3,z4,z5,z6]),(0,[z1,z273,z2,z3,z4,z5,z41])],[],[(0,[z1,z129,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z442,z5,z6]),(0,[z1,z2,z38,z4,z17,z5,z6])],[(0,[z132,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z275,z38,z4,z5,z6]),(1,[z1,z2,z3,z488,z5,z6]),(0,[z1,z313,z2,z4,z5,z6,z56])],[(0,[z1,z35,z2,z10,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z551,z6])],[(0,[z1,z20,z3,z10,z4,z5,z6]),(0,[z1,z273,z2,z38,z4,z5,z6]),(0,[z83,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z252,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z175,z19,z6])],[(0,[z183,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z562,z50,z5,z6]),(0,[z1,z2,z25,z4,z217,z5,z6])]],
   [[(0,[z1,z24,z3,z4,z221,z5,z6]),(0,[z1,z150,z2,z38,z4,z5,z6])],[(0,[z1,z24,z3,z4,z5,z6,z245])],[(0,[z96,z1,z2,z3,z50,z5,z6]),(0,[z2,z3,z4,z11,z5,z19,z6]),(0,[z1,z2,z3,z4,z5,z70,z41])],[(0,[z1,z2,z3,z249,z50,z5,z6]),(0,[z1,z44,z2,z3,z18,z5,z6])],[(0,[z1,z42,z20,z3,z4,z5,z6]),(0,[z1,z20,z3,z4,z221,z5,z6]),(0,[z1,z2,z3,z4,z19,z6,z56])],[(0,[z1,z24,z38,z3,z4,z5,z6]),(0,[z86,z1,z2,z10,z4,z5,z6]),(0,[z86,z1,z2,z3,z4,z19,z6]),(0,[z1,z125,z2,z3,z4,z5,z28])],[(0,[z1,z20,z3,z4,z5,z6,z60]),(0,[z86,z1,z2,z3,z4,z563,z6]),(0,[z64,z1,z285,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z564,z6]),(0,[z1,z2,z3,z4,z565,z5,z6])],[(0,[z183,z132,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z79,z6]),(0,[z1,z2,z566,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z567])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z18,z5,z6]),(0,[z1,z2,z3,z4,z19,z278,z6]),(1,[z1,z2,z3,z4,z5,z508]),(0,[z1,z2,z3,z4,z11,z6,z245]),(0,[z1,z2,z568,z3,z4,z5,z6])],[(0,[z7,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z11,z6,z60]),(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z1,z2,z120,z3,z4,z5,z23])],[(0,[z1,z2,z38,z73,z4,z5,z6]),(0,[z1,z2,z38,z61,z4,z5,z6]),(0,[z1,z273,z2,z3,z18,z5,z6]),(1,[z1,z377,z3,z4,z5,z6]),(0,[z1,z39,z179,z3,z4,z5,z6]),(0,[z1,z2,z3,z358,z4,z5,z6]),(1,[z1,z2,z3,z33,z100,z6])],[(0,[z1,z35,z20,z3,z4,z5,z6]),(0,[z569,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z570,z6])],[(0,[z1,z129,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z50,z5,z6]),(0,[z2,z3,z18,z4,z50,z5,z6]),(1,[z1,z2,z3,z4,z288,z6]),(0,[z1,z150,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z410,z4,z5,z6])],[(0,[z132,z1,z24,z3,z4,z5,z6])],[(0,[z1,z176,z2,z10,z4,z5,z6]),(1,[z2,z3,z18,z50,z5,z6]),(0,[z1,z52,z2,z3,z4,z5,z6]),(0,[z1,z176,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z33,z4,z5,z41])],[(0,[z1,z2,z3,z4,z5,z571,z6]),(1,[z1,z2,z10,z4,z5,z28]),(1,[z1,z2,z3,z4,z19,z28]),(0,[z1,z2,z4,z48,z5,z22,z6])]],
   [[(0,[z183,z1,z24,z3,z4,z5,z6]),(0,[z1,z20,z3,z4,z5,z27,z6]),(0,[z1,z369,z2,z3,z4,z5,z6]),(0,[z1,z441,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z572,z50,z5,z6]),(0,[z573,z1,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z10,z25,z4,z5,z6]),(0,[z111,z1,z2,z88,z4,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z28])],[(0,[z1,z24,z2,z3,z4,z11,z6]),(1,[z1,z2,z3,z574,z5,z6]),(1,[z1,z2,z10,z4,z5,z6]),(1,[z1,z2,z3,z438,z5,z6]),(1,[z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z11,z27,z6])],[(0,[z1,z24,z3,z4,z175,z5,z6]),(0,[z1,z2,z3,z205,z4,z5,z6]),(1,[z1,z2,z3,z4,z563,z6]),(0,[z1,z2,z3,z50,z5,z70,z6]),(0,[z1,z328,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z28,z6])],[(1,[z1,z2,z3,z4,z5,z188]),(0,[z1,z129,z2,z3,z50,z5,z6]),(1,[z1,z2,z3,z436,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6])],[(1,[z24,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z69,z28]),(1,[z1,z306,z2,z3,z4,z5]),(0,[z1,z576,z2,z3,z4,z5,z6]),(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z6])],[(0,[z1,z578,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z240,z5,z6]),(0,[z1,z179,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z300])],[(0,[z183,z1,z2,z3,z50,z5,z6]),(0,[z1,z20,z3,z61,z4,z5,z6]),(0,[z83,z1,z2,z3,z4,z19,z6]),(0,[z1,z90,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z181,z5,z6]),(0,[z1,z579,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z580]),(0,[z1,z2,z3,z4,z581,z5,z6])],[(0,[z1,z2,z3,z480,z4,z5,z6]),(1,[z1,z36,z154,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z69,z6])],[(0,[z1,z2,z3,z4,z5,z102,z6]),(0,[z1,z273,z36,z2,z4,z5,z6]),(0,[z1,z125,z3,z4,z5,z69,z6])],[(0,[z1,z176,z20,z3,z4,z5,z6]),(0,[z1,z35,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z48,z5,z6]),(0,[z7,z1,z2,z3,z4,z556,z6])],[(1,[z1,z20,z3,z4,z5,z28]),(0,[z96,z1,z2,z3,z574,z5,z6]),(0,[z96,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z10,z4,z5,z70,z6]),(1,[z1,z254,z3,z4,z5,z6]),(0,[z1,z582,z2,z3,z4,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z245])],[(0,[z111,z1,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z490]),(0,[z1,z331,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z100,z5,z27,z6])],[(0,[z86,z1,z174,z3,z4,z5,z6]),(0,[z1,z583,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z584,z5,z6])],[(0,[z1,z2,z3,z4,z5,z188,z6]),(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z157,z6])],[(0,[z1,z2,z3,z50,z5,z28,z6]),(0,[z51,z1,z2,z3,z4,z11,z6])],[(0,[z1,z2,z38,z25,z4,z5,z6])],[(0,[z86,z1,z24,z3,z4,z5,z6]),(0,[z1,z586,z2,z3,z4,z19,z6]),(0,[z1,z36,z3,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z185])],[(0,[z1,z2,z3,z4,z5,z268,z6]),(0,[z64,z1,z55,z3,z4,z5,z6])],[(0,[z1,z322,z2,z3,z18,z5,z6]),(1,[z1,z2,z3,z4,z556,z6]),(0,[z1,z2,z3,z4,z587,z5,z6]),(0,[z1,z2,z3,z4,z588,z5,z6]),(0,[z1,z2,z589,z3,z4,z5,z6])],[(0,[z1,z210,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z10,z4,z19,z6]),(0,[z1,z2,z3,z61,z50,z5,z6]),(0,[z1,z68,z2,z3,z4,z5,z28])],[(0,[z7,z1,z24,z3,z4,z5,z6]),(1,[z1,z2,z38,z4,z11,z6])],[(0,[z1,z2,z3,z50,z5,z6,z41]),(0,[z1,z2,z3,z154,z4,z5,z6]),(0,[z1,z59,z3,z4,z5,z6,z60]),(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z591,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z592,z6])],[(1,[z1,z2,z3,z4,z314,z6]),(0,[z1,z593,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z563,z5,z6]),(0,[z83,z2,z3,z4,z5,z6,z41]),(0,[z1,z68,z2,z3,z4,z5,z6]),(0,[z1,z594,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z595,z4,z5,z28]),(0,[z1,z2,z3,z596,z4,z5,z6]),(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z1,z598,z2,z3,z4,z5,z6])],[(0,[z1,z476,z2,z3,z4,z5,z6]),(0,[z1,z176,z24,z3,z4,z5,z6]),(1,[z1,z174,z3,z4,z5,z6]),(0,[z191,z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z599,z6]),(1,[z1,z2,z3,z4,z5,z551])],[(0,[z1,z2,z20,z3,z4,z5,z41]),(1,[z1,z24,z3,z4,z5,z28]),(0,[z1,z2,z38,z4,z5,z70,z6]),(0,[z1,z2,z3,z454,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z357,z41])],[(0,[z1,z2,z3,z4,z5,z361,z41]),(0,[z1,z2,z3,z4,z5,z451,z41]),(0,[z1,z2,z3,z4,z217,z5,z28]),(0,[z1,z2,z3,z4,z5,z6,z600])]],
   [[(1,[z111,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z436,z5,z6]),(0,[z1,z2,z3,z4,z11,z11,z6]),(0,[z1,z2,z196,z3,z4,z11,z6]),(0,[z1,z2,z3,z595,z4,z5,z6])],[(0,[z1,z24,z3,z4,z5,z23,z6]),(0,[z96,z1,z2,z3,z601,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z602]),(0,[z1,z2,z13,z3,z4,z5,z6]),(0,[z1,z59,z2,z3,z32,z4,z5]),(0,[z1,z129,z2,z3,z4,z22,z6])],[(1,[z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z6,z41]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z278,z6])],[(0,[z1,z2,z3,z4,z217,z5,z6])],[(0,[z1,z21,z2,z10,z4,z5,z6]),(1,[z1,z2,z3,z18,z11,z6]),(0,[z1,z129,z2,z4,z48,z5,z6])],[(0,[z1,z179,z36,z2,z4,z5,z6]),(1,[z1,z90,z3,z61,z5,z6])],[(0,[z604,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z48,z5,z6]),(0,[z1,z176,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z503,z4,z11,z6]),(0,[z1,z2,z3,z605,z4,z5,z6]),(0,[z1,z2,z3,z4,z606,z5,z6])],[(0,[z1,z2,z3,z32,z4,z5,z41]),(0,[z1,z607,z2,z3,z4,z5,z6]),(0,[z1,z2,z608,z3,z4,z5,z6])],[(0,[z1,z20,z3,z134,z4,z5,z6]),(0,[z83,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z300]),(0,[z111,z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z11,z23,z6]),(0,[z1,z150,z2,z3,z134,z4,z6]),(0,[z1,z2,z3,z4,z5,z609,z6])],[(0,[z1,z2,z3,z4,z5,z6,z610]),(0,[z1,z2,z3,z4,z5,z611,z6])],[(0,[z612,z1,z2,z3,z4,z5,z6]),(0,[z1,z44,z2,z38,z4,z5,z6]),(0,[z1,z2,z84,z4,z5,z22,z6]),(0,[z1,z2,z3,z613,z4,z5,z6])],[(0,[z1,z2,z3,z4,z216,z5,z6])],[(0,[z96,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z28,z6]),(0,[z7,z1,z2,z3,z4,z587,z6]),(0,[z1,z59,z3,z61,z4,z5,z6]),(0,[z1,z614,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z615,z5,z6])],[(0,[z1,z24,z3,z10,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z6,z171]),(0,[z1,z68,z3,z4,z5,z69,z6])],[(0,[z1,z2,z3,z4,z19,z268,z6]),(0,[z1,z2,z3,z33,z4,z70,z6])],[(0,[z1,z39,z2,z3,z4,z5,z28])]],
   [[(0,[z1,z2,z3,z4,z19,z6,z245]),(0,[z1,z2,z616,z3,z4,z5,z6]),(0,[z617,z1,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z41]),(0,[z1,z273,z39,z2,z4,z5,z6])],[(0,[z1,z20,z3,z164,z4,z5,z6]),(0,[z1,z189,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z99,z6]),(0,[z1,z2,z3,z61,z4,z19,z6]),(0,[z1,z2,z3,z4,z618,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z619]),(0,[z1,z2,z38,z4,z5,z6,z41]),(0,[z1,z39,z2,z3,z4,z5,z6])],[],[(0,[z1,z20,z3,z4,z48,z5,z6]),(0,[z1,z24,z3,z4,z5,z6,z60]),(0,[z1,z36,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z6,z620]),(0,[z1,z2,z3,z621,z4,z5,z6])],[(0,[z1,z2,z3,z134,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z622])],[(0,[z24,z2,z20,z3,z4,z5,z6]),(0,[z623,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z390,z3,z4,z5,z6]),(0,[z1,z8,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z624,z4,z5,z6]),(1,[z1,z2,z3,z32,z5,z79])],[(0,[z1,z2,z3,z32,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z414,z28]),(0,[z1,z2,z3,z4,z5,z625,z6])],[(1,[z1,z2,z3,z4,z5,z291])],[(0,[z1,z2,z3,z18,z5,z6,z16]),(0,[z78,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z41,z245]),(0,[z1,z2,z3,z626,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z28,z6]),(0,[z1,z431,z2,z3,z4,z5,z6]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z60])],[(0,[z183,z1,z2,z3,z4,z314,z6]),(0,[z64,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z414,z6]),(0,[z1,z2,z3,z402,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z99,z41])],[(0,[z1,z2,z3,z4,z5,z467,z6]),(0,[z1,z2,z3,z4,z5,z28,z16])],[(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z628,z6])],[(0,[z1,z24,z3,z4,z5,z27,z6])]],
   [[(0,[z1,z2,z3,z280,z18,z5,z6]),(0,[z1,z160,z2,z3,z4,z5,z6]),(0,[z1,z406,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z92,z5,z28])],[(0,[z96,z1,z2,z3,z4,z5,z320]),(0,[z1,z524,z2,z3,z4,z5,z6]),(0,[z1,z121,z2,z3,z4,z19,z6]),(1,[z1,z2,z3,z528,z5,z6]),(0,[z1,z629,z2,z3,z4,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z10,z32,z4,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z602]),(0,[z1,z2,z3,z4,z50,z5,z28]),(0,[z1,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z100,z4,z5,z28])],[(0,[z111,z1,z2,z10,z4,z5,z6]),(0,[z111,z1,z2,z3,z438,z5,z6]),(0,[z111,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z631,z3,z4,z5,z6])],[(0,[z1,z406,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z79,z41]),(0,[z1,z2,z3,z4,z92,z5,z6])],[(0,[z632,z1,z2,z3,z4,z5,z6]),(1,[z1,z487,z2,z4,z5,z6]),(0,[z633,z1,z2,z3,z4,z5,z6])],[(0,[z1,z44,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6]),(0,[z1,z36,z2,z3,z18,z5,z6]),(0,[z1,z2,z84,z3,z4,z5,z41]),(1,[z1,z3,z4,z271,z5,z6]),(0,[z1,z2,z634,z3,z4,z5,z6]),(0,[z1,z2,z3,z100,z4,z5,z6]),(0,[z1,z2,z635,z3,z4,z5,z6]),(0,[z1,z44,z2,z3,z5,z6,z56])],[(1,[z1,z2,z3,z18,z5,z41]),(0,[z1,z2,z3,z18,z4,z5,z41]),(0,[z83,z1,z2,z3,z528,z5,z6]),(0,[z1,z2,z3,z4,z5,z636,z6])],[(0,[z637,z1,z2,z3,z4,z5,z6]),(0,[z1,z24,z3,z61,z4,z5,z6]),(0,[z1,z2,z3,z4,z638,z5,z6])],[(0,[z1,z2,z3,z18,z432,z5,z6]),(0,[z1,z2,z3,z639,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z552,z6]),(0,[z1,z640,z2,z3,z4,z5,z6]),(0,[z641,z1,z2,z3,z4,z5,z6])],[(0,[z1,z642,z2,z3,z4,z5,z6])],[(0,[z1,z544,z2,z3,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6]),(0,[z1,z179,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z643,z4,z5,z6])],[(0,[z1,z273,z2,z10,z4,z5,z6]),(0,[z1,z322,z2,z38,z4,z5,z6]),(0,[z64,z1,z2,z3,z18,z5,z6]),(0,[z1,z59,z2,z3,z4,z5,z41]),(0,[z644,z1,z2,z3,z4,z5,z6])],[(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z96,z1,z646,z3,z4,z5,z6]),(0,[z1,z2,z10,z72,z4,z5,z6]),(0,[z1,z90,z3,z61,z4,z5,z6])],[(0,[z1,z150,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z399,z18,z5,z6]),(0,[z1,z150,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z647,z5,z6])]],
   [[(1,[z1,z2,z3,z4,z5,z602]),(0,[z1,z262,z2,z3,z4,z5,z6]),(0,[z1,z2,z120,z3,z4,z5,z28]),(0,[z1,z59,z2,z3,z4,z5,z69]),(0,[z1,z2,z84,z3,z33,z4,z6])],[(0,[z64,z2,z3,z4,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z134,z4,z19,z6])],[(0,[z64,z51,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z33,z18,z5,z6]),(0,[z1,z273,z2,z3,z217,z5,z6])],[(0,[z1,z2,z38,z32,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6])],[(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z44,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z120,z3,z4,z5,z6])],[(0,[z1,z2,z3,z474,z4,z5,z6]),(0,[z1,z24,z3,z4,z5,z6,z110])],[(0,[z1,z2,z3,z50,z5,z79,z6]),(0,[z1,z425,z3,z4,z5,z27,z6])],[(0,[z1,z272,z20,z3,z4,z5,z6]),(0,[z1,z558,z2,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z99,z6]),(0,[z1,z2,z84,z3,z18,z5,z6]),(0,[z1,z649,z2,z3,z4,z5,z6]),(0,[z1,z650,z2,z3,z4,z5,z6])],[(0,[z651,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z408,z6]),(0,[z1,z2,z3,z18,z18,z5,z6]),(1,[z2,z3,z4,z11,z19,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z2,z3,z154,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z652,z6])],[(0,[z1,z2,z222,z3,z4,z5,z6]),(0,[z132,z1,z2,z3,z4,z5,z28]),(0,[z86,z1,z2,z3,z653,z5,z6]),(0,[z1,z2,z3,z4,z221,z5,z6])],[(1,[z1,z2,z3,z601,z5,z6]),(0,[z1,z2,z38,z3,z4,z5,z28]),(0,[z1,z125,z3,z4,z221,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z245])],[(0,[z1,z273,z20,z3,z4,z5,z6]),(1,[z1,z2,z345,z4,z5,z6]),(0,[z1,z2,z120,z3,z4,z5,z245])],[(0,[z1,z2,z10,z33,z4,z5,z6]),(1,[z1,z2,z3,z50,z11,z6]),(0,[z1,z129,z2,z3,z4,z5,z6])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z150,z20,z3,z4,z5,z6]),(0,[z1,z187,z2,z120,z4,z5,z6])],[(0,[z1,z2,z38,z3,z4,z5,z6]),(0,[z1,z59,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z48,z19,z6]),(0,[z1,z90,z2,z3,z61,z5,z6])],[(0,[z1,z2,z10,z4,z5,z79,z6]),(0,[z1,z36,z2,z154,z4,z5,z6]),(0,[z1,z2,z84,z3,z4,z48,z6])]],
   [[(0,[z183,z1,z2,z3,z4,z5,z6]),(0,[z654,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z655])],[(0,[z1,z2,z3,z4,z574,z5,z6])],[(1,[z1,z2,z3,z4,z5,z619]),(0,[z111,z1,z24,z3,z4,z5,z6]),(0,[z1,z2,z10,z18,z4,z5,z6])],[(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z1,z646,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z178,z4,z19,z6]),(0,[z1,z487,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z657,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z658])],[(1,[z1,z2,z3,z4,z5,z335]),(0,[z1,z103,z2,z3,z50,z5,z6]),(1,[z1,z2,z109,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z659,z6])],[(0,[z1,z20,z3,z25,z4,z5,z6]),(0,[z660,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z20,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z508,z6]),(0,[z1,z2,z3,z4,z661,z5,z6]),(0,[z1,z2,z3,z358,z4,z221,z6]),(0,[z1,z68,z2,z3,z4,z5,z60]),(0,[z1,z2,z3,z4,z5,z6,z385])],[(0,[z1,z24,z3,z134,z4,z5,z6]),(0,[z1,z179,z2,z10,z4,z5,z6]),(1,[z1,z2,z3,z653,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z336]),(0,[z1,z179,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z662,z6])],[(0,[z1,z2,z38,z4,z5,z99,z6]),(0,[z1,z35,z2,z3,z4,z5,z28])],[(0,[z1,z24,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z175,z5,z28]),(0,[z1,z663,z2,z3,z4,z5,z6])],[],[(0,[z1,z135,z24,z3,z4,z5,z6]),(0,[z64,z1,z2,z454,z4,z5,z6]),(0,[z664,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z53,z5,z6]),(0,[z1,z665,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z177,z4,z6,z56])],[(0,[z1,z273,z24,z3,z4,z5,z6]),(0,[z1,z35,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z92,z70])],[(0,[z1,z2,z38,z33,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z175,z5,z6])],[(0,[z1,z150,z24,z3,z4,z5,z6]),(0,[z1,z44,z2,z3,z50,z5,z6]),(0,[z1,z125,z3,z4,z175,z5,z6]),(0,[z1,z44,z2,z3,z4,z5,z79])],[(1,[z1,z2,z3,z4,z628,z6]),(0,[z1,z90,z2,z3,z4,z5,z41]),(0,[z666,z1,z2,z3,z4,z5,z6]),(1,[z1,z667,z3,z4,z5,z6])]],
   [[(0,[z1,z20,z3,z4,z5,z70,z6]),(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z38,z4,z5,z79,z6]),(0,[z1,z2,z3,z4,z669,z5,z6])],[(0,[z1,z187,z2,z3,z32,z4,z5])],[(0,[z1,z2,z20,z3,z18,z5,z6]),(0,[z1,z500,z2,z3,z4,z5,z6]),(0,[z1,z39,z179,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z670,z5,z6])],[(0,[z671,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z25,z50,z5,z6]),(0,[z1,z2,z3,z4,z11,z70,z6]),(0,[z1,z2,z3,z4,z5,z6,z672])],[(0,[z1,z24,z3,z4,z48,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z6,z60]),(0,[z1,z2,z3,z4,z11,z292,z6]),(0,[z1,z374,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z28]),(0,[z1,z667,z2,z3,z4,z5,z6])],[(0,[z1,z179,z20,z3,z4,z5,z6]),(0,[z1,z273,z2,z3,z50,z5,z6]),(0,[z1,z190,z2,z3,z18,z5,z6]),(0,[z83,z1,z2,z3,z4,z628,z6])],[(1,[z183,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z601,z4,z5,z6]),(0,[z1,z2,z3,z4,z673,z5,z6])],[(0,[z1,z2,z3,z4,z5,z133,z6]),(0,[z132,z1,z2,z3,z4,z5,z571]),(1,[z1,z2,z10,z4,z11,z6]),(0,[z1,z150,z2,z3,z50,z5,z6])],[(0,[z674,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z41]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z675,z4,z5,z6]),(0,[z1,z553,z2,z3,z4,z5,z27])],[(0,[z1,z1,z2,z38,z4,z5,z6]),(1,[z1,z2,z3,z4,z587,z6]),(0,[z1,z176,z2,z3,z4,z5,z28])],[(0,[z1,z24,z3,z4,z5,z28,z6]),(0,[z1,z24,z2,z3,z18,z5,z6]),(1,[z1,z2,z3,z4,z5,z320]),(0,[z1,z187,z2,z3,z4,z11,z6])],[(0,[z1,z593,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z676,z5])],[(0,[z1,z2,z3,z18,z11,z5,z6]),(0,[z1,z2,z3,z18,z5,z491,z6]),(0,[z1,z2,z677,z3,z4,z5,z6]),(0,[z1,z306,z2,z3,z4,z217,z5]),(0,[z1,z2,z3,z4,z394,z217,z5])],[(0,[z51,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z38,z329,z4,z5,z6]),(0,[z1,z36,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z181,z11,z6]),(0,[z1,z125,z36,z3,z4,z5,z6]),(0,[z1,z176,z2,z3,z4,z5,z6])],[(1,[z1,z2,z38,z4,z5,z41]),(0,[z1,z2,z3,z4,z19,z27,z6]),(1,[z1,z2,z3,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z6,z678])]],
   [[(0,[z1,z2,z3,z50,z201,z5,z6]),(0,[z1,z90,z2,z3,z18,z5,z6]),(0,[z1,z118,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z679,z6])],[(0,[z1,z24,z3,z4,z5,z6,z41]),(0,[z1,z2,z3,z4,z11,z28,z6]),(1,[z7,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z434,z28]),(0,[z1,z680,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z681,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z653,z5,z6]),(0,[z1,z2,z3,z4,z682,z5,z6])],[(0,[z183,z1,z2,z3,z4,z5,z619]),(0,[z191,z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z482,z4,z5,z6]),(0,[z1,z2,z683,z3,z4,z5,z6])],[(0,[z64,z1,z2,z38,z4,z5,z6]),(0,[z83,z1,z2,z3,z4,z5,z28]),(0,[z1,z273,z2,z4,z5,z23,z6]),(0,[z1,z2,z3,z4,z684,z5,z6])],[(0,[z183,z1,z2,z3,z4,z5,z335]),(1,[z1,z20,z3,z4,z11,z6]),(0,[z1,z20,z3,z4,z5,z6,z41]),(0,[z1,z2,z3,z4,z5,z434,z6]),(1,[z1,z2,z3,z4,z401,z6]),(0,[z1,z2,z3,z228,z4,z5,z6]),(0,[z1,z553,z2,z3,z4,z5,z6])],[(0,[z1,z179,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z5,z41]),(0,[z1,z233,z2,z3,z4,z5,z6]),(0,[z1,z2,z196,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z23,z28]),(0,[z685,z1,z2,z3,z4,z5,z6]),(0,[z1,z68,z2,z3,z32,z4,z5])],[(1,[z1,z646,z3,z4,z5,z6]),(0,[z686,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z220,z4,z5,z6])],[(0,[z96,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z253,z3,z4,z5,z6]),(0,[z191,z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z6,z41]),(0,[z83,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6])],[(1,[z1,z2,z3,z4,z408,z6]),(0,[z1,z2,z3,z562,z4,z5,z6]),(0,[z51,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z238]),(0,[z1,z44,z2,z3,z4,z19,z6])],[(0,[z1,z2,z688,z3,z4,z5,z6]),(0,[z1,z2,z3,z689,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z23,z6])],[(0,[z1,z2,z196,z38,z4,z5,z6]),(0,[z1,z2,z3,z488,z4,z5,z6])],[(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z1,z690,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z691,z4,z5,z6])],[(0,[z1,z20,z3,z4,z334,z5,z6]),(0,[z1,z2,z3,z249,z4,z5,z6]),(0,[z1,z2,z692,z3,z4,z5,z6])],[(0,[z1,z2,z84,z38,z4,z5,z6]),(0,[z1,z2,z3,z25,z4,z19,z6]),(1,[z1,z2,z4,z5,z6,z76])],[(1,[z1,z2,z38,z18,z5,z6]),(0,[z1,z68,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z11,z6,z330]),(0,[z1,z2,z3,z242,z4,z217,z6])]],
   [[(0,[z183,z2,z20,z3,z4,z5,z6]),(0,[z1,z273,z2,z3,z4,z19,z6]),(0,[z7,z1,z2,z481,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z693,z6])],[(0,[z1,z2,z3,z50,z5,z99,z6]),(0,[z1,z2,z390,z3,z4,z5,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z1,z2,z3,z695,z4,z5,z6])],[(0,[z1,z2,z3,z10,z4,z5,z28]),(0,[z1,z269,z2,z3,z4,z5,z28]),(1,[z1,z125,z3,z221,z5,z6]),(0,[z1,z2,z3,z4,z676,z221,z5])],[(0,[z1,z2,z3,z4,z5,z87,z6]),(0,[z1,z2,z3,z280,z4,z19,z6]),(0,[z1,z586,z2,z3,z4,z5,z6]),(0,[z78,z2,z3,z4,z11,z5,z6]),(0,[z696,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z547,z6]),(0,[z191,z1,z2,z3,z18,z5,z6]),(0,[z1,z273,z2,z4,z48,z5,z6])],[(0,[z132,z24,z2,z3,z4,z5,z6]),(0,[z1,z59,z2,z38,z4,z5,z6]),(0,[z1,z2,z38,z4,z370,z5,z6]),(0,[z697,z1,z2,z3,z4,z5,z6])],[(1,[z1,z24,z3,z4,z11,z6]),(0,[z1,z2,z3,z10,z4,z5,z6]),(0,[z1,z269,z2,z3,z4,z5,z6]),(0,[z1,z698,z2,z3,z4,z5,z6])],[(0,[z1,z2,z38,z4,z5,z6,z373]),(0,[z1,z2,z196,z3,z18,z5,z6]),(1,[z1,z160,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z217,z11,z6]),(0,[z1,z699,z2,z3,z4,z5,z6]),(0,[z1,z700,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z385])],[(0,[z1,z2,z3,z4,z221,z5,z28]),(0,[z1,z701,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z134,z5,z27,z6])],[(0,[z1,z371,z20,z3,z4,z5,z6]),(0,[z1,z36,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z6,z16]),(0,[z1,z2,z25,z4,z5,z23,z6])],[(0,[z1,z2,z3,z572,z4,z5,z6]),(1,[z1,z2,z481,z4,z5,z6]),(0,[z1,z667,z3,z4,z5,z6,z56])],[(0,[z1,z492,z2,z3,z18,z5,z6]),(0,[z1,z129,z2,z3,z4,z5,z28]),(1,[z1,z2,z4,z259,z5,z6]),(1,[z1,z3,z4,z5,z157,z6]),(0,[z1,z2,z3,z4,z5,z6,z702])],[(0,[z1,z20,z20,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z571]),(1,[z1,z176,z3,z4,z99,z6])],[(0,[z1,z106,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z503,z18,z5,z6]),(0,[z1,z187,z2,z3,z4,z5,z41]),(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z704,z3,z4,z5,z6])],[(0,[z1,z2,z430,z3,z4,z5,z6]),(0,[z1,z705,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z676,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z60]),(1,[z1,z3,z4,z5,z6,z185])],[(0,[z183,z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z546,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z82]),(0,[z1,z2,z706,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z20,z3,z340,z4,z5,z6]),(0,[z696,z2,z10,z4,z5,z6]),(0,[z78,z2,z3,z4,z11,z82]),(0,[z1,z2,z456,z4,z628,z6]),(0,[z1,z44,z2,z3,z177,z56])],[(0,[z1,z2,z3,z4,z372,z28]),(0,[z1,z121,z2,z4,z370,z6]),(0,[z1,z707,z2,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z708]),(0,[z1,z187,z2,z4,z5,z14])],[(0,[z20,z10,z4,z50,z5,z6]),(0,[z1,z2,z474,z4,z5,z28])],[(0,[z1,z187,z24,z4,z5,z245]),(0,[z1,z2,z3,z4,z11,z153])],[(0,[z111,z24,z3,z4,z19,z6]),(0,[z1,z2,z3,z709,z5,z6])],[(0,[z1,z189,z3,z4,z310,z6]),(0,[z1,z44,z2,z38,z5,z56]),(0,[z1,z2,z345,z50,z5,z6]),(0,[z650,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z710,z6])],[(0,[z2,z3,z18,z50,z19,z6]),(0,[z1,z2,z3,z4,z711,z5])],[(0,[z1,z2,z274,z4,z11,z6]),(0,[z1,z712,z3,z4,z5,z6])],[(0,[z1,z24,z3,z18,z11,z6]),(0,[z1,z81,z3,z4,z5,z153]),(0,[z1,z713,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z714,z6]),(0,[z1,z160,z3,z18,z5,z6]),(0,[z1,z2,z4,z715,z5,z6])],[(0,[z1,z174,z3,z50,z5,z6]),(0,[z1,z487,z2,z4,z19,z6]),(0,[z1,z254,z3,z4,z5,z508]),(0,[z1,z2,z3,z358,z4,z676]),(0,[z1,z2,z173,z134,z27,z6]),(0,[z1,z2,z3,z4,z92,z716])],[(0,[z1,z2,z3,z574,z19,z6]),(0,[z1,z3,z4,z717,z5,z6]),(0,[z1,z2,z3,z438,z19,z6]),(0,[z1,z3,z4,z271,z19,z6]),(0,[z1,z8,z3,z4,z5,z41]),(0,[z1,z2,z718,z4,z5,z6])],[(0,[z1,z2,z10,z18,z5,z41]),(0,[z83,z2,z3,z4,z628,z41])],[(0,[z1,z253,z3,z4,z11,z6]),(0,[z1,z2,z719,z4,z5,z6]),(0,[z1,z2,z3,z720,z4,z6]),(0,[z1,z145,z3,z4,z11,z6])],[(0,[z1,z2,z38,z45,z5,z6]),(0,[z1,z2,z454,z4,z5,z28]),(0,[z1,z2,z50,z259,z5,z6]),(0,[z2,z3,z421,z18,z5,z6]),(0,[z1,z721,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z722])],[(0,[z1,z24,z3,z50,z5,z6]),(0,[z1,z723,z2,z4,z5,z6]),(0,[z64,z285,z3,z50,z5,z6])],[],[(0,[z7,z20,z3,z4,z5,z28]),(0,[z1,z125,z3,z201,z5,z6]),(0,[z1,z2,z3,z131,z158,z6]),(0,[z1,z13,z38,z4,z5,z6]),(0,[z1,z3,z50,z5,z6,z185]),(0,[z1,z52,z3,z4,z5,z28]),(0,[z51,z2,z3,z4,z19,z41]),(0,[z1,z2,z3,z134,z292,z6])],[(0,[z1,z2,z109,z488,z5,z6])],[(0,[z1,z2,z456,z4,z5,z6]),(0,[z1,z2,z3,z4,z724,z6]),(0,[z1,z390,z3,z4,z216,z6]),(0,[z1,z2,z3,z4,z28,z725])],[(0,[z1,z20,z3,z528,z5,z6]),(0,[z1,z68,z38,z4,z5,z69]),(0,[z1,z586,z2,z3,z4,z490]),(0,[z1,z2,z173,z33,z4,z6]),(0,[z1,z44,z2,z3,z139,z5])],[(0,[z183,z20,z3,z4,z407,z6]),(0,[z1,z2,z196,z25,z5,z41]),(0,[z1,z2,z3,z4,z726,z6])],[(0,[z1,z2,z3,z50,z92,z70]),(0,[z1,z390,z3,z4,z11,z6])],[(0,[z685,z20,z3,z4,z5,z6]),(1,[z1,z2,z4,z727,z6])],[(0,[z1,z2,z230,z4,z5,z41]),(0,[z1,z328,z3,z61,z5,z6]),(0,[z1,z2,z728,z4,z5,z6]),(0,[z1,z2,z3,z464,z5,z28])],[(0,[z1,z2,z3,z4,z5,z729]),(0,[z1,z38,z4,z730,z5,z6])],[(0,[z1,z2,z3,z18,z133,z6]),(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z429,z2,z3,z18,z5]),(0,[z1,z732,z3,z4,z5,z6])],[(0,[z1,z2,z3,z380,z5,z571]),(0,[z1,z24,z4,z733,z5,z6]),(0,[z1,z24,z3,z32,z5,z79]),(0,[z96,z646,z10,z4,z5,z6])],[(0,[z24,z3,z18,z50,z5,z6]),(0,[z1,z2,z3,z448,z5,z6]),(0,[z1,z2,z3,z4,z5,z734]),(0,[z1,z735,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z407,z28]),(0,[z1,z24,z3,z4,z5,z291]),(0,[z86,z2,z3,z50,z19,z6]),(0,[z1,z13,z3,z18,z5,z6]),(0,[z420,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z736])],[(0,[z1,z2,z3,z4,z5,z737])],[(0,[z183,z20,z38,z4,z5,z6]),(0,[z51,z20,z3,z4,z5,z41]),(0,[z1,z24,z3,z4,z5,z508]),(0,[z1,z2,z10,z601,z5,z6]),(0,[z83,z2,z3,z4,z5,z41]),(0,[z1,z2,z4,z5,z41,z738]),(0,[z1,z125,z3,z358,z4,z6])]],
   [[(0,[z1,z2,z474,z4,z5,z571]),(0,[z1,z2,z3,z739,z5,z6]),(0,[z1,z2,z3,z740,z5,z6]),(0,[z1,z68,z3,z18,z5,z69]),(0,[z573,z2,z3,z4,z19,z6]),(0,[z1,z313,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z741,z6])],[(0,[z1,z382,z2,z3,z5,z56]),(0,[z1,z2,z3,z18,z742,z5]),(0,[z1,z3,z4,z5,z743,z6])],[(0,[z1,z20,z3,z4,z5,z602]),(0,[z1,z2,z3,z50,z587,z6]),(0,[z1,z2,z3,z744,z5,z6])],[(0,[z1,z2,z126,z4,z5,z41]),(0,[z1,z2,z38,z4,z676,z5])],[(0,[z1,z174,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z551]),(0,[z1,z129,z2,z4,z48,z41])],[(0,[z1,z24,z3,z4,z19,z28]),(0,[z1,z174,z3,z4,z563,z6]),(0,[z1,z745,z2,z3,z50,z5]),(0,[z1,z2,z3,z4,z92,z248]),(0,[z1,z746,z3,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z619]),(0,[z591,z2,z3,z4,z5,z41]),(0,[z1,z44,z2,z3,z5,z316])],[(0,[z1,z2,z3,z747,z4,z6]),(0,[z1,z296,z3,z4,z5,z28])],[(0,[z1,z2,z10,z4,z5,z335]),(0,[z1,z2,z109,z4,z19,z6]),(0,[z1,z748,z2,z3,z4,z5])],[(0,[z749,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z750,z5,z6])],[(0,[z86,z20,z3,z50,z5,z6]),(0,[z1,z24,z3,z4,z563,z6]),(0,[z2,z10,z4,z50,z19,z6]),(0,[z1,z38,z4,z5,z6,z185]),(0,[z7,z2,z3,z50,z5,z28]),(0,[z1,z2,z109,z436,z5,z6]),(0,[z697,z2,z3,z4,z5,z41])],[(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z24,z3,z4,z5,z188]),(0,[z1,z2,z3,z653,z19,z6])],[(0,[z1,z59,z3,z4,z5,z207]),(0,[z24,z752,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z18,z5,z297,z6])],[(0,[z1,z55,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z754])],[(0,[z1,z646,z3,z50,z5,z6]),(0,[z1,z2,z10,z4,z92,z70]),(0,[z1,z2,z3,z482,z5,z28]),(0,[z1,z755,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z756])],[(0,[z1,z429,z2,z38,z4,z5]),(0,[z64,z2,z3,z50,z11,z6]),(0,[z1,z2,z3,z572,z249,z6]),(0,[z1,z487,z2,z50,z5,z6])],[(0,[z1,z3,z4,z5,z6,z757]),(0,[z1,z2,z3,z4,z53,z70]),(0,[z1,z2,z3,z758,z4,z6]),(0,[z1,z2,z3,z4,z5,z759])],[(0,[z1,z2,z10,z4,z628,z6]),(0,[z2,z10,z4,z457,z5,z6]),(0,[z1,z667,z10,z4,z5,z6]),(0,[z1,z285,z3,z4,z5,z41]),(0,[z1,z492,z2,z3,z5,z56])],[],[(0,[z1,z2,z3,z18,z87,z6]),(0,[z1,z748,z2,z3,z4,z11]),(0,[z1,z202,z2,z217,z5,z6]),(0,[z1,z2,z760,z4,z5,z6]),(0,[z1,z761,z3,z4,z5,z6]),(0,[z1,z44,z2,z3,z5,z658])],[(0,[z20,z3,z4,z11,z19,z6]),(0,[z1,z762,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z763,z5]),(0,[z1,z2,z222,z4,z5,z41]),(0,[z1,z2,z3,z235,z4,z394])],[(0,[z1,z80,z3,z4,z11,z6]),(0,[z2,z38,z10,z18,z5,z6])],[(0,[z1,z20,z3,z653,z5,z6]),(0,[z1,z377,z3,z4,z5,z28]),(0,[z1,z39,z179,z4,z5,z28]),(0,[z690,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z32,z647,z5])],[(0,[z1,z125,z38,z221,z5,z6]),(0,[z264,z2,z3,z4,z19,z6]),(0,[z405,z2,z3,z4,z11,z6])],[(0,[z132,z24,z3,z4,z5,z28]),(0,[z437,z2,z38,z4,z5,z6])],[(0,[z1,z2,z3,z50,z5,z602]),(0,[z1,z145,z3,z4,z5,z82])],[(0,[z1,z24,z3,z601,z5,z6]),(0,[z1,z2,z10,z4,z587,z6]),(0,[z1,z2,z463,z4,z5,z23]),(0,[z1,z2,z84,z413,z4,z6])],[(0,[z1,z24,z345,z4,z5,z6]),(0,[z1,z2,z3,z574,z5,z320]),(0,[z1,z2,z3,z4,z19,z320])]],
   [[(0,[z1,z2,z3,z4,z764,z6]),(0,[z1,z2,z4,z11,z765,z6])],[(0,[z1,z3,z4,z5,z766,z6])],[(0,[z1,z2,z767,z18,z5,z6]),(0,[z1,z768,z2,z3,z4,z5]),(0,[z1,z2,z463,z4,z5,z434])],[(0,[z2,z769,z10,z4,z5,z6]),(0,[z1,z770,z2,z10,z4,z5]),(0,[z1,z2,z38,z4,z19,z41]),(0,[z696,z2,z3,z4,z19,z6]),(0,[z1,z771,z2,z3,z5,z6])],[(0,[z1,z2,z3,z772,z5,z6])],[(0,[z1,z328,z3,z164,z5,z6]),(0,[z1,z2,z3,z436,z5,z28])],[(0,[z1,z273,z20,z217,z5,z6]),(0,[z1,z3,z4,z5,z773,z6]),(0,[z7,z2,z10,z4,z5,z28]),(0,[z2,z3,z4,z19,z114,z6]),(0,[z1,z2,z3,z774,z5,z6])],[(0,[z1,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z177,z18,z6]),(0,[z1,z2,z3,z177,z4,z28])],[],[(0,[z1,z2,z88,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z756]),(0,[z1,z2,z3,z100,z775,z6])],[(0,[z1,z186,z72,z4,z5,z6])],[(0,[z1,z431,z2,z240,z5,z6]),(0,[z1,z2,z3,z776,z5,z6]),(0,[z1,z777,z3,z4,z5,z6])],[(0,[z1,z646,z10,z4,z5,z6])],[(0,[z1,z2,z778,z4,z5,z6])],[(0,[z1,z20,z3,z4,z676,z5]),(0,[z1,z2,z192,z4,z5,z28]),(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z3,z61,z5,z319,z6]),(0,[z1,z2,z780,z4,z5,z6]),(0,[z1,z2,z3,z781,z5,z6])],[(0,[z1,z2,z3,z18,z19,z41]),(0,[z1,z2,z3,z4,z782,z6])],[(0,[z1,z783,z3,z4,z5,z6]),(0,[z1,z24,z3,z4,z92,z70]),(0,[z1,z36,z419,z4,z5,z6]),(0,[z1,z2,z784,z4,z5,z6]),(0,[z1,z785,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z28]),(0,[z1,z20,z38,z4,z5,z41])],[(0,[z1,z2,z3,z50,z763,z5]),(0,[z1,z35,z2,z3,z4,z537])],[(0,[z1,z24,z3,z4,z628,z6]),(0,[z1,z193,z154,z4,z5,z6]),(0,[z1,z8,z38,z4,z5,z6]),(0,[z1,z55,z3,z4,z5,z41]),(0,[z1,z122,z2,z3,z5,z56])],[(0,[z1,z786,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z787])],[(0,[z96,z2,z10,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z788]),(0,[z1,z2,z3,z18,z5,z82]),(0,[z1,z2,z3,z4,z5,z789]),(0,[z1,z187,z2,z4,z5,z223])],[(0,[z1,z2,z38,z206,z5,z6]),(0,[z1,z272,z3,z4,z5,z60]),(0,[z1,z2,z222,z380,z5,z6]),(0,[z536,z2,z3,z50,z5,z6])],[(0,[z1,z2,z3,z4,z11,z41]),(0,[z1,z210,z3,z4,z5,z357])],[(0,[z1,z2,z222,z4,z5,z267])],[(0,[z1,z2,z3,z4,z563,z602])],[(0,[z132,z24,z3,z4,z5,z571]),(0,[z2,z3,z534,z4,z5,z41]),(0,[z1,z2,z790,z4,z5,z6])],[(0,[z1,z24,z10,z4,z11,z6]),(0,[z529,z2,z38,z4,z5,z6]),(0,[z2,z3,z50,z5,z28,z41]),(0,[z1,z791,z2,z3,z4,z5])],[(0,[z1,z20,z3,z4,z408,z6]),(0,[z1,z80,z3,z4,z5,z41]),(0,[z1,z792,z3,z4,z5,z6]),(0,[z1,z160,z10,z4,z5,z6]),(0,[z1,z81,z3,z4,z5,z41])],[(0,[z1,z2,z793,z4,z5,z6]),(0,[z1,z24,z3,z4,z587,z6]),(0,[z276,z2,z10,z4,z5,z6]),(0,[z1,z8,z3,z482,z5,z6])],[(0,[z1,z2,z3,z448,z87,z6]),(0,[z1,z2,z84,z50,z22,z6]),(0,[z1,z160,z88,z4,z5,z6])],[(0,[z1,z2,z481,z4,z19,z6]),(0,[z1,z313,z2,z4,z5,z28]),(0,[z1,z179,z794,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z795,z5,z6]),(0,[z1,z796,z3,z4,z5,z6]),(0,[z111,z2,z3,z4,z19,z28]),(0,[z1,z2,z4,z259,z19,z6]),(0,[z1,z2,z3,z4,z258,z41]),(0,[z1,z2,z3,z4,z797,z6]),(0,[z1,z2,z4,z727,z22,z6])],[(0,[z1,z2,z38,z4,z5,z237]),(0,[z1,z2,z38,z4,z5,z238]),(0,[z422,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z798,z4,z6]),(0,[z1,z3,z4,z6,z385,z185])],[(0,[z1,z2,z126,z4,z407,z6]),(0,[z1,z2,z799,z4,z5,z6]),(0,[z1,z187,z20,z4,z5,z245]),(0,[z1,z2,z3,z358,z4,z41]),(0,[z1,z3,z4,z5,z6,z800])],[(0,[z183,z20,z3,z50,z5,z6]),(0,[z1,z285,z454,z4,z5,z6]),(0,[z1,z2,z3,z4,z801,z6]),(0,[z1,z802,z3,z4,z5,z6]),(0,[z1,z425,z173,z4,z5,z6])],[(0,[z1,z524,z2,z4,z5,z245]),(0,[z1,z2,z3,z18,z11,z28]),(0,[z1,z3,z803,z4,z5,z6])],[(0,[z7,z24,z3,z4,z5,z28]),(0,[z1,z553,z2,z3,z18,z5]),(0,[z1,z2,z3,z804,z5,z6])],[(0,[z1,z24,z3,z4,z5,z6])],[(0,[z2,z3,z4,z684,z11,z6]),(0,[z1,z2,z3,z4,z805,z6])],[(0,[z1,z24,z3,z528,z5,z6]),(0,[z1,z135,z3,z4,z5,z60]),(0,[z1,z2,z3,z50,z676,z5]),(0,[z1,z90,z3,z806,z5,z6])],[(0,[z1,z2,z3,z807,z5,z6]),(0,[z1,z808,z3,z4,z19,z6])],[(0,[z1,z2,z3,z4,z19,z619]),(0,[z1,z20,z3,z4,z6,z385]),(0,[z1,z2,z809,z4,z5,z6]),(0,[z1,z2,z810,z4,z5,z6])],[(0,[z1,z2,z3,z811,z5,z6]),(0,[z1,z2,z3,z50,z5,z28]),(0,[z1,z812,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z19,z335]),(0,[z1,z2,z230,z18,z5,z6]),(0,[z1,z150,z3,z4,z175,z41]),(0,[z1,z374,z2,z3,z4,z16])],[(0,[z1,z20,z481,z4,z5,z6]),(0,[z1,z2,z10,z45,z5,z6]),(0,[z1,z2,z3,z18,z5,z237]),(0,[z1,z2,z3,z18,z5,z238]),(0,[z1,z425,z3,z4,z11,z6]),(0,[z1,z2,z4,z5,z23,z813])],[(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z20,z4,z259,z5,z6]),(0,[z1,z24,z3,z4,z815,z5]),(0,[z1,z2,z38,z4,z5,z153]),(0,[z1,z2,z816,z4,z5,z6]),(0,[z1,z2,z817,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z818])],[(0,[z422,z20,z3,z4,z5,z6]),(0,[z1,z20,z3,z4,z5,z571]),(0,[z1,z2,z474,z4,z133,z6]),(0,[z1,z819,z10,z4,z5,z6]),(0,[z1,z2,z88,z45,z5,z6])],[(0,[z1,z13,z10,z4,z5,z6]),(0,[z1,z2,z3,z653,z563,z6]),(0,[z1,z2,z3,z4,z820,z6]),(0,[z1,z2,z4,z11,z6,z76]),(0,[z1,z2,z84,z4,z368,z6])],[(0,[z1,z2,z4,z5,z6,z821]),(0,[z1,z35,z2,z3,z4,z330]),(0,[z2,z3,z4,z5,z127,z28]),(0,[z1,z35,z2,z3,z519,z4])],[(0,[z1,z24,z4,z5,z6,z76]),(0,[z1,z174,z3,z4,z5,z602]),(0,[z1,z2,z3,z822,z50,z6]),(0,[z1,z2,z481,z4,z556,z6])],[(0,[z1,z68,z10,z4,z5,z69]),(0,[z1,z2,z3,z488,z5,z6]),(0,[z1,z2,z823,z4,z5,z6])],[(0,[z477,z2,z3,z50,z5,z6])],[(0,[z1,z2,z3,z380,z11,z6]),(1,[z2,z10,z50,z19,z6]),(0,[z2,z38,z4,z5,z28,z41]),(0,[z630,z2,z3,z50,z5,z6])],[(0,[z1,z2,z474,z131,z5,z6]),(0,[z24,z3,z4,z11,z19,z6]),(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z406,z2,z4,z5,z245]),(0,[z1,z2,z3,z50,z408,z6])],[(0,[z1,z2,z3,z4,z11,z267]),(0,[z1,z24,z3,z4,z5,z602]),(0,[z1,z667,z3,z4,z19,z6]),(0,[z1,z825,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z826,z6])],[(0,[z78,z2,z3,z4,z11,z41]),(0,[z1,z306,z3,z4,z271,z5])],[(0,[z1,z2,z474,z4,z11,z6]),(0,[z1,z770,z2,z3,z50,z5]),(0,[z1,z2,z3,z18,z5,z153]),(0,[z1,z2,z84,z4,z218,z6])],[(0,[z1,z2,z3,z4,z827,z6])],[(0,[z1,z285,z38,z4,z5,z6]),(0,[z1,z2,z4,z5,z297,z41]),(0,[z1,z179,z4,z255,z5,z6])],[(0,[z1,z553,z2,z38,z4,z5]),(0,[z1,z492,z2,z3,z5,z336]),(0,[z650,z2,z3,z4,z11,z6]),(0,[z1,z553,z2,z3,z134,z27])],[(0,[z1,z2,z274,z18,z5,z6])],[(0,[z1,z2,z3,z4,z288,z28])]],
   [[(0,[z437,z2,z3,z50,z5,z6])],[(0,[z1,z2,z3,z4,z828,z6]),(0,[z1,z306,z2,z25,z4,z5]),(0,[z1,z2,z3,z33,z100,z6])],[(0,[z1,z2,z3,z4,z314,z619]),(0,[z1,z55,z454,z4,z5,z6])],[(1,[z20,z10,z50,z5,z6]),(0,[z1,z2,z3,z829,z5,z6]),(0,[z1,z2,z10,z4,z676,z5]),(0,[z1,z2,z830,z4,z5,z6]),(0,[z1,z2,z3,z831,z5,z6])],[(0,[z1,z2,z3,z4,z314,z335]),(0,[z1,z253,z3,z18,z5,z6]),(0,[z1,z2,z321,z25,z5,z6]),(0,[z1,z2,z3,z4,z408,z291]),(0,[z1,z2,z3,z50,z6,z385])],[(0,[z2,z3,z18,z50,z5,z6]),(0,[z1,z832,z3,z4,z5,z6])],[(0,[z1,z2,z454,z4,z11,z6]),(0,[z1,z52,z3,z4,z216,z6])],[(0,[z1,z2,z3,z4,z563,z28]),(0,[z1,z2,z3,z4,z92,z317])],[(0,[z1,z135,z3,z4,z5,z110]),(0,[z1,z285,z3,z18,z5,z6]),(0,[z1,z2,z192,z4,z5,z237])],[(0,[z24,z20,z3,z4,z5,z28]),(0,[z1,z2,z3,z50,z5,z571]),(0,[z1,z2,z10,z4,z87,z6]),(0,[z1,z174,z3,z653,z5,z6]),(0,[z2,z568,z38,z4,z5,z6]),(0,[z1,z176,z3,z50,z99,z6]),(0,[z1,z52,z3,z4,z11,z6]),(0,[z1,z487,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z574,z5,z6]),(0,[z1,z833,z3,z4,z5,z6]),(0,[z1,z2,z3,z438,z5,z6]),(0,[z1,z3,z4,z271,z5,z6])],[],[(0,[z1,z2,z834,z4,z5,z6]),(0,[z1,z24,z3,z45,z5,z6]),(0,[z1,z2,z835,z4,z5,z6]),(0,[z1,z836,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z837]),(0,[z1,z390,z3,z18,z5,z6]),(0,[z1,z36,z154,z4,z5,z28]),(0,[z1,z125,z3,z584,z5,z6]),(0,[z1,z2,z3,z4,z5,z838])],[(0,[z20,z3,z4,z50,z19,z6]),(0,[z1,z839,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z102]),(0,[z1,z2,z50,z5,z297,z6]),(0,[z1,z2,z3,z4,z840,z6]),(0,[z1,z2,z3,z841,z5,z6])],[(0,[z1,z842,z3,z4,z5,z6]),(0,[z1,z843,z3,z4,z5,z6]),(0,[z1,z2,z3,z235,z4,z41]),(0,[z1,z2,z844,z4,z5,z6])],[(0,[z1,z254,z3,z4,z5,z28]),(0,[z1,z2,z3,z464,z11,z6])],[(0,[z1,z2,z3,z845,z5,z6]),(0,[z1,z2,z196,z205,z5,z6]),(0,[z1,z808,z3,z50,z5,z6]),(0,[z1,z2,z402,z4,z5,z82]),(0,[z1,z2,z3,z846,z5,z6])],[(0,[z1,z2,z3,z847,z4,z6]),(0,[z1,z425,z4,z5,z297,z6])],[(0,[z1,z2,z848,z4,z5,z6]),(0,[z1,z39,z42,z4,z5,z6]),(0,[z1,z306,z24,z3,z4,z5]),(0,[z1,z2,z3,z4,z408,z188]),(0,[z1,z2,z3,z4,z5,z849])],[(0,[z1,z20,z120,z4,z5,z23]),(0,[z261,z2,z10,z4,z5,z6]),(0,[z1,z2,z4,z5,z850,z6]),(0,[z1,z2,z3,z851,z5,z6])],[(0,[z1,z20,z3,z50,z5,z41]),(0,[z132,z24,z222,z4,z5,z6])],[(0,[z1,z20,z126,z4,z5,z6]),(0,[z2,z752,z3,z4,z5,z6]),(0,[z1,z2,z3,z601,z5,z320]),(0,[z1,z852,z3,z4,z5,z6]),(0,[z575,z2,z38,z4,z5,z6])],[(0,[z1,z2,z38,z18,z19,z6]),(0,[z1,z2,z853,z4,z5,z6]),(0,[z1,z8,z3,z50,z5,z6]),(0,[z1,z2,z854,z4,z5,z6])],[(0,[z1,z24,z84,z4,z22,z6])],[(0,[z1,z59,z3,z50,z5,z60]),(0,[z1,z2,z3,z464,z258,z6]),(0,[z2,z3,z4,z5,z41,z366]),(0,[z1,z2,z3,z4,z5,z855])],[(0,[z1,z2,z10,z146,z5,z6]),(0,[z1,z856,z2,z4,z5,z6]),(0,[z1,z68,z3,z4,z389,z5])],[(0,[z1,z55,z38,z4,z5,z6]),(0,[z1,z2,z345,z4,z5,z28]),(0,[z1,z2,z3,z4,z857,z5])],[(0,[z1,z20,z3,z4,z5,z102]),(0,[z1,z2,z3,z4,z5,z858])],[(0,[z183,z752,z3,z4,z5,z6]),(0,[z64,z2,z38,z50,z5,z6]),(0,[z1,z859,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z216,z124]),(0,[z1,z2,z3,z18,z860,z5]),(0,[z2,z3,z4,z19,z284,z6]),(0,[z1,z2,z3,z4,z556,z6])],[],[(0,[z1,z2,z38,z4,z11,z6]),(0,[z529,z2,z3,z50,z5,z6]),(0,[z1,z160,z3,z438,z5,z6]),(1,[z1,z3,z4,z861,z6]),(0,[z1,z680,z2,z4,z48,z6])]],
   [[(0,[z1,z174,z3,z4,z5,z28]),(0,[z2,z3,z4,z862,z5,z6]),(0,[z1,z2,z3,z4,z11,z124]),(0,[z1,z296,z3,z4,z11,z6]),(0,[z1,z429,z2,z4,z259,z5]),(0,[z1,z2,z3,z4,z5,z863])],[(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z167,z4,z19,z6]),(0,[z1,z2,z167,z438,z5,z6]),(0,[z1,z2,z3,z4,z865,z6])],[(0,[z1,z2,z3,z4,z314,z6]),(0,[z1,z24,z3,z4,z676,z5]),(0,[z1,z2,z10,z4,z19,z41])],[(0,[z1,z363,z3,z242,z4,z6]),(0,[z1,z2,z866,z4,z5,z6])],[(0,[z1,z20,z3,z867,z4,z6]),(0,[z1,z80,z38,z4,z5,z6]),(0,[z1,z81,z38,z4,z5,z6]),(0,[z2,z3,z421,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z551])],[(0,[z1,z24,z3,z4,z5,z28]),(0,[z703,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z238])],[(0,[z20,z38,z10,z4,z5,z6]),(0,[z1,z2,z345,z4,z408,z6]),(0,[z644,z2,z3,z4,z19,z6])],[(0,[z1,z2,z3,z868,z5,z6]),(0,[z1,z55,z3,z18,z5,z6]),(0,[z1,z2,z3,z869,z4,z6])],[(0,[z1,z870,z3,z4,z5,z6]),(0,[z1,z2,z109,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z82]),(0,[z1,z2,z38,z4,z258,z6]),(0,[z1,z3,z18,z5,z871,z6])],[(0,[z1,z2,z454,z4,z5,z41]),(0,[z64,z2,z3,z862,z5,z6]),(0,[z1,z2,z3,z482,z11,z6]),(0,[z1,z296,z3,z4,z258,z6]),(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z2,z84,z689,z4,z6])],[(0,[z1,z2,z38,z358,z4,z6])],[],[(0,[z1,z253,z3,z448,z5,z6]),(0,[z1,z2,z321,z329,z5,z6]),(0,[z1,z873,z3,z4,z5,z6])],[(0,[z1,z492,z2,z3,z5,z316]),(0,[z1,z874,z3,z4,z5,z6])],[(0,[z477,z24,z3,z4,z5,z6]),(0,[z1,z2,z120,z50,z5,z23])],[(0,[z1,z20,z167,z4,z5,z6]),(0,[z1,z2,z3,z875,z5,z6]),(0,[z630,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z876]),(0,[z1,z877,z2,z3,z4,z5])],[(0,[z1,z2,z126,z50,z5,z6]),(0,[z1,z80,z3,z18,z5,z6]),(0,[z1,z81,z3,z18,z5,z6]),(0,[z1,z35,z2,z3,z4,z325])],[(0,[z1,z129,z2,z50,z48,z6]),(0,[z1,z2,z3,z4,z6,z878]),(0,[z1,z2,z173,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z879])],[(0,[z1,z553,z24,z3,z4,z5]),(0,[z1,z8,z10,z4,z5,z6]),(0,[z1,z2,z3,z880,z5,z6]),(0,[z1,z377,z3,z4,z11,z6]),(0,[z1,z39,z179,z4,z11,z6]),(0,[z1,z2,z4,z5,z41,z76]),(0,[z1,z2,z3,z881,z5,z6])],[(0,[z1,z3,z4,z5,z882,z6]),(0,[z1,z13,z3,z4,z19,z6]),(0,[z1,z2,z3,z464,z5,z41])],[(0,[z132,z24,z3,z4,z11,z6]),(0,[z1,z150,z38,z4,z175,z6]),(0,[z1,z44,z3,z5,z185,z56])],[(0,[z1,z2,z10,z206,z5,z6]),(0,[z1,z2,z3,z4,z5,z883])],[(0,[z1,z68,z3,z4,z19,z69]),(0,[z1,z2,z3,z4,z5,z884])],[(0,[z1,z2,z3,z131,z19,z6]),(0,[z1,z2,z10,z4,z11,z28])],[(0,[z51,z2,z10,z4,z19,z6]),(0,[z1,z2,z38,z885,z4,z6]),(0,[z1,z886,z3,z4,z5,z6]),(0,[z1,z2,z230,z4,z288,z6]),(0,[z1,z2,z252,z205,z5,z6]),(0,[z2,z3,z4,z19,z6,z325]),(0,[z1,z2,z3,z4,z887,z6])],[(0,[z1,z2,z3,z4,z288,z237]),(0,[z1,z2,z3,z4,z587,z28]),(0,[z888,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z889,z6])],[],[(0,[z1,z2,z890,z4,z5,z6]),(0,[z1,z2,z3,z4,z891,z6]),(0,[z1,z892,z3,z4,z5,z6])],[(0,[z1,z2,z3,z653,z5,z602]),(0,[z1,z2,z3,z595,z5,z79])],[(0,[z1,z893,z3,z4,z5,z6]),(0,[z1,z2,z3,z436,z11,z6]),(0,[z1,z2,z894,z4,z5,z6])],[(0,[z1,z20,z3,z4,z133,z6]),(0,[z1,z2,z3,z4,z158,z41]),(0,[z1,z2,z3,z4,z5,z320]),(0,[z111,z2,z167,z4,z19,z6]),(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z2,z3,z4,z70,z353])],[(0,[z1,z20,z173,z4,z5,z6])]],
   [[(0,[z2,z10,z50,z5,z6,z41]),(0,[z1,z2,z10,z4,z5,z237]),(0,[z1,z2,z10,z4,z5,z238]),(0,[z1,z285,z3,z50,z5,z6]),(0,[z1,z896,z2,z4,z5,z6]),(0,[z1,z145,z402,z4,z5,z6])],[(0,[z1,z20,z3,z18,z19,z6]),(0,[z1,z24,z3,z4,z19,z41]),(0,[z78,z2,z38,z4,z11,z6]),(0,[z1,z2,z196,z851,z5,z6])],[(0,[z1,z2,z38,z4,z5,z41]),(0,[z1,z2,z88,z4,z5,z238])],[(0,[z1,z24,z3,z4,z5,z571]),(0,[z1,z646,z3,z4,z5,z320]),(0,[z1,z2,z3,z4,z401,z291]),(0,[z897,z2,z3,z4,z5,z6])],[(0,[z1,z558,z3,z201,z5,z6]),(0,[z1,z2,z222,z50,z5,z6]),(0,[z1,z2,z3,z898,z4,z6]),(0,[z1,z2,z3,z528,z5,z28]),(0,[z1,z794,z2,z4,z5,z6]),(0,[z1,z2,z899,z4,z5,z6]),(0,[z1,z2,z3,z5,z79,z900])],[(0,[z1,z20,z3,z131,z5,z6]),(0,[z1,z487,z2,z4,z676,z5])],[(0,[z1,z20,z3,z4,z216,z6]),(0,[z1,z2,z192,z4,z11,z6]),(0,[z1,z901,z3,z4,z5,z6]),(0,[z1,z13,z3,z4,z556,z6]),(1,[z1,z2,z3,z4,z716])],[(0,[z1,z646,z3,z4,z5,z28]),(0,[z1,z2,z902,z4,z5,z6])],[(0,[z1,z2,z3,z4,z903,z6]),(0,[z660,z2,z3,z18,z5,z6]),(0,[z1,z487,z2,z4,z5,z28])],[(0,[z1,z20,z3,z4,z11,z6]),(0,[z1,z2,z38,z4,z394,z5]),(0,[z1,z3,z4,z271,z5,z28]),(0,[z1,z550,z3,z4,z175,z6])],[(0,[z1,z904,z2,z18,z5,z6]),(0,[z1,z2,z3,z905,z5,z6])],[(0,[z1,z2,z3,z906,z5,z6])],[],[(0,[z96,z2,z10,z4,z11,z6]),(0,[z1,z2,z10,z4,z5,z153]),(0,[z1,z129,z2,z4,z197,z6]),(0,[z1,z374,z2,z3,z4,z490])],[(0,[z1,z2,z3,z18,z5,z41])],[(0,[z2,z38,z10,z4,z19,z6]),(0,[z1,z907,z3,z4,z5,z6]),(0,[z1,z2,z38,z50,z19,z6]),(0,[z1,z2,z88,z4,z5,z153])],[(0,[z1,z2,z3,z908,z5,z6]),(0,[z1,z2,z3,z4,z909,z6])],[(0,[z1,z2,z3,z4,z910,z6]),(0,[z1,z44,z2,z3,z5,z171]),(0,[z1,z39,z4,z673,z5,z6]),(0,[z911,z2,z3,z4,z5,z6]),(0,[z1,z59,z3,z332,z4,z5])],[(0,[z1,z24,z10,z18,z5,z6]),(0,[z96,z80,z10,z4,z5,z6])],[],[(0,[z1,z2,z3,z358,z50,z6]),(0,[z1,z2,z3,z488,z5,z82])],[(0,[z1,z39,z179,z4,z5,z41]),(0,[z1,z2,z481,z4,z587,z6])],[(0,[z1,z106,z441,z4,z5,z6]),(0,[z2,z692,z3,z4,z5,z41])],[(0,[z132,z24,z3,z4,z5,z41]),(0,[z1,z313,z2,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z912])],[(0,[z1,z913,z3,z4,z5,z6]),(0,[z111,z2,z3,z4,z914,z6]),(0,[z379,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z134,z551,z27]),(0,[z1,z2,z3,z33,z775,z6])],[(0,[z1,z90,z3,z164,z5,z6]),(0,[z529,z24,z3,z4,z5,z6]),(0,[z1,z2,z915,z4,z5,z6])],[(0,[z1,z2,z38,z4,z427,z6]),(0,[z1,z2,z3,z916,z5,z6]),(0,[z1,z3,z4,z5,z6,z917])],[(0,[z1,z24,z196,z25,z5,z6]),(0,[z1,z285,z10,z4,z5,z6]),(0,[z1,z918,z3,z4,z5,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z385])],[(0,[z1,z2,z3,z380,z158,z6]),(0,[z1,z2,z3,z4,z920,z5])],[(0,[z1,z20,z38,z50,z5,z6]),(0,[z1,z2,z3,z146,z19,z6]),(0,[z7,z2,z481,z4,z5,z28]),(0,[z1,z2,z3,z921,z5,z6]),(0,[z1,z425,z3,z33,z4,z6])],[(0,[z1,z24,z230,z4,z5,z6]),(0,[z1,z2,z481,z4,z5,z6])],[(0,[z1,z2,z3,z303,z407,z6]),(0,[z1,z2,z3,z922,z5,z6]),(0,[z1,z24,z3,z4,z5,z237]),(0,[z1,z24,z3,z4,z5,z238]),(0,[z2,z3,z4,z11,z19,z6]),(0,[z78,z2,z3,z436,z11,z6]),(0,[z2,z98,z3,z4,z11,z6]),(0,[z83,z2,z3,z4,z258,z41]),(0,[z1,z2,z4,z259,z5,z6]),(0,[z1,z2,z3,z32,z282,z5])]],
   [[(0,[z1,z2,z38,z380,z5,z6]),(0,[z1,z2,z3,z50,z216,z6]),(0,[z1,z176,z3,z4,z99,z6]),(0,[z1,z2,z3,z923,z4,z6]),(0,[z1,z2,z3,z4,z5,z924])],[(0,[z1,z2,z474,z4,z158,z6]),(0,[z1,z2,z281,z4,z19,z6])],[(0,[z1,z2,z38,z4,z5,z267]),(0,[z1,z3,z4,z5,z6,z185])],[(0,[z1,z2,z3,z50,z11,z6]),(0,[z1,z2,z568,z25,z5,z6])],[(0,[z1,z425,z3,z18,z5,z6]),(1,[z1,z2,z3,z5,z900]),(0,[z1,z44,z313,z2,z5,z56]),(0,[z1,z2,z925,z4,z5,z6])],[(0,[z24,z38,z10,z4,z5,z6]),(0,[z1,z2,z345,z4,z401,z6]),(0,[z1,z926,z3,z4,z5,z6])],[(0,[z1,z2,z3,z18,z427,z6]),(0,[z1,z2,z927,z4,z5,z6])],[(0,[z1,z2,z3,z242,z50,z6])],[(0,[z1,z24,z120,z4,z5,z23]),(0,[z1,z81,z3,z50,z5,z6]),(0,[z1,z808,z3,z4,z5,z6]),(0,[z1,z2,z3,z45,z5,z28])],[(0,[z1,z2,z3,z4,z5,z619]),(0,[z1,z24,z3,z50,z5,z41]),(0,[z1,z3,z18,z5,z6,z928])],[(0,[z1,z24,z126,z4,z5,z6]),(0,[z1,z2,z3,z653,z5,z28]),(0,[z1,z929,z3,z4,z5,z6]),(0,[z1,z2,z3,z930,z5,z6]),(0,[z1,z35,z2,z3,z4,z16])],[(0,[z1,z2,z3,z4,z5,z335]),(0,[z78,z20,z3,z4,z11,z6]),(0,[z1,z174,z3,z4,z5,z102]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z193,z73,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z82]),(0,[z1,z932,z3,z4,z5,z6])],[(0,[z1,z2,z3,z50,z258,z6]),(0,[z536,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z933,z6])],[(0,[z550,z24,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z934,z5]),(0,[z1,z3,z4,z935,z5,z6]),(0,[z1,z2,z456,z4,z5,z41]),(0,[z7,z8,z3,z4,z5,z28])],[(0,[z1,z20,z4,z5,z297,z6]),(0,[z1,z2,z3,z18,z5,z267]),(0,[z1,z2,z3,z4,z936,z6])],[(0,[z1,z2,z3,z937,z5,z6]),(0,[z1,z20,z281,z4,z5,z6]),(0,[z654,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z32,z11,z79])],[(0,[z1,z2,z3,z18,z372,z6]),(0,[z96,z2,z10,z4,z5,z41]),(0,[z1,z2,z3,z146,z556,z6])],[(0,[z1,z2,z474,z18,z5,z6]),(0,[z1,z187,z2,z4,z5,z373]),(0,[z1,z2,z3,z4,z11,z291])],[(0,[z1,z306,z20,z3,z4,z5]),(0,[z1,z39,z663,z4,z5,z6])],[(0,[z1,z20,z3,z4,z394,z5]),(0,[z1,z121,z2,z4,z48,z6]),(0,[z1,z2,z3,z4,z11,z508]),(0,[z1,z2,z3,z938,z4,z6]),(0,[z1,z3,z4,z175,z861,z6]),(0,[z1,z2,z939,z4,z5,z6])],[(0,[z1,z2,z281,z4,z556,z6]),(0,[z1,z2,z84,z4,z22,z28])],[(0,[z1,z43,z3,z4,z99,z6])],[(0,[z1,z500,z154,z4,z5,z6]),(0,[z1,z2,z3,z448,z5,z41]),(0,[z1,z667,z3,z4,z5,z6]),(0,[z1,z2,z940,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z941]),(0,[z132,z24,z3,z4,z5,z267]),(0,[z2,z3,z4,z5,z364,z28]),(0,[z1,z2,z4,z5,z6,z942])],[(0,[z1,z2,z3,z206,z19,z6]),(0,[z1,z150,z3,z50,z175,z6]),(0,[z1,z2,z3,z32,z5,z491]),(0,[z1,z3,z4,z19,z157,z6]),(0,[z1,z2,z3,z4,z5,z813])],[(0,[z183,z20,z3,z4,z5,z28]),(0,[z1,z2,z943,z4,z5,z6]),(0,[z1,z2,z944,z4,z5,z6])],[(0,[z1,z55,z10,z4,z5,z6]),(0,[z1,z313,z2,z4,z5,z41]),(0,[z1,z2,z945,z4,z5,z6])],[(0,[z1,z2,z38,z464,z5,z6]),(0,[z1,z3,z4,z19,z6,z185]),(0,[z1,z2,z3,z4,z946,z6])],[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z190,z3,z442,z5,z6]),(0,[z64,z2,z10,z50,z5,z6]),(1,[z1,z794,z4,z5,z6]),(0,[z1,z2,z948,z4,z5,z6])],[(0,[z654,z20,z3,z4,z5,z6]),(0,[z1,z949,z2,z3,z4,z5]),(0,[z1,z2,z454,z18,z5,z6]),(0,[z1,z3,z4,z5,z6,z950]),(0,[z1,z2,z3,z4,z951,z6])],[(0,[z1,z24,z222,z4,z5,z6])],[]],
   [[(0,[z1,z2,z3,z4,z11,z188]),(0,[z379,z2,z3,z50,z5,z6]),(0,[z1,z52,z3,z18,z5,z6]),(0,[z2,z3,z657,z18,z5,z6]),(0,[z1,z2,z3,z228,z100,z6]),(0,[z1,z2,z952,z4,z5,z6])],[(0,[z24,z20,z3,z4,z11,z6]),(0,[z1,z20,z3,z235,z4,z6]),(0,[z1,z2,z4,z5,z953,z6]),(0,[z1,z954,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z955,z6])],[(0,[z1,z2,z3,z956,z5,z6])],[(0,[z1,z2,z957,z4,z5,z6]),(0,[z1,z80,z10,z4,z5,z6]),(0,[z1,z81,z10,z4,z5,z6])],[(0,[z1,z958,z3,z4,z5,z6])],[(0,[z1,z2,z3,z303,z19,z6]),(0,[z78,z2,z3,z50,z11,z6]),(0,[z1,z81,z88,z4,z5,z6]),(0,[z1,z36,z154,z4,z11,z6]),(0,[z1,z959,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z960])],[(0,[z20,z3,z10,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z961]),(0,[z1,z306,z2,z3,z235,z4])],[(0,[z1,z2,z10,z4,z258,z6]),(0,[z1,z13,z481,z4,z5,z6]),(0,[z1,z273,z2,z235,z4,z6])],[(0,[z1,z254,z3,z4,z11,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z24,z38,z4,z19,z6]),(0,[z1,z2,z10,z358,z4,z6]),(0,[z1,z2,z281,z50,z5,z6]),(0,[z1,z2,z109,z4,z5,z82]),(0,[z1,z2,z3,z4,z962,z6])],[(0,[z1,z2,z3,z963,z4,z6])],[],[(0,[z1,z2,z3,z18,z407,z6]),(0,[z1,z2,z3,z4,z401,z6]),(0,[z1,z2,z3,z4,z408,z28]),(0,[z1,z363,z3,z4,z19,z6])],[(0,[z1,z964,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z102]),(0,[z1,z2,z3,z50,z394,z5]),(0,[z1,z2,z3,z965,z5,z6])],[(0,[z1,z2,z3,z966,z5,z6]),(0,[z1,z2,z967,z4,z5,z6])],[(0,[z1,z2,z3,z968,z5,z6])],[(0,[z1,z2,z3,z206,z314,z6]),(0,[z1,z2,z3,z438,z5,z153]),(0,[z1,z2,z3,z4,z19,z153]),(0,[z1,z969,z3,z4,z5,z6]),(0,[z1,z425,z3,z134,z4,z6])],[(0,[z1,z553,z20,z3,z4,z5]),(0,[z1,z2,z970,z4,z5,z6]),(0,[z1,z2,z3,z4,z372,z298])],[(0,[z1,z2,z3,z4,z6,z876])],[(0,[z1,z20,z3,z303,z5,z6]),(0,[z1,z2,z345,z4,z11,z6]),(0,[z1,z2,z3,z4,z971,z6]),(0,[z1,z296,z410,z4,z5,z6]),(0,[z1,z972,z3,z4,z5,z6]),(0,[z1,z973,z3,z4,z5,z6])],[(0,[z1,z2,z274,z4,z19,z6]),(0,[z1,z20,z10,z4,z19,z6]),(0,[z641,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z974,z6])],[(0,[z1,z24,z3,z18,z19,z6]),(0,[z1,z487,z24,z4,z5,z6]),(0,[z78,z2,z3,z4,z11,z508]),(0,[z1,z125,z3,z221,z5,z28]),(0,[z1,z2,z3,z975,z5,z6]),(0,[z1,z2,z976,z4,z5,z6])],[(0,[z1,z2,z38,z18,z5,z6]),(0,[z1,z2,z120,z4,z5,z361]),(0,[z1,z977,z2,z4,z5,z6])],[(0,[z1,z2,z3,z18,z5,z124]),(0,[z1,z296,z3,z18,z5,z6])],[(0,[z1,z174,z3,z4,z11,z6])],[],[(0,[z1,z253,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z288,z41]),(0,[z1,z145,z3,z4,z19,z6]),(0,[z1,z978,z3,z4,z5,z6])],[(0,[z660,z2,z10,z4,z5,z6]),(0,[z1,z2,z4,z259,z676,z5])],[(0,[z1,z2,z10,z242,z4,z6]),(0,[z1,z306,z2,z10,z4,z5]),(0,[z1,z979,z38,z4,z5,z6]),(0,[z1,z145,z3,z436,z5,z6]),(0,[z1,z2,z4,z5,z6,z980]),(0,[z981,z2,z3,z4,z5,z6]),(0,[z1,z982,z2,z4,z5,z6])],[(0,[z1,z24,z3,z4,z11,z6]),(0,[z1,z2,z3,z303,z314,z6]),(0,[z1,z745,z2,z3,z4,z5]),(0,[z1,z476,z3,z4,z175,z6])],[(0,[z1,z160,z3,z4,z5,z6]),(0,[z2,z692,z38,z4,z5,z6]),(0,[z1,z3,z4,z5,z157,z28])],[(0,[z132,z24,z38,z4,z5,z6]),(0,[z1,z983,z3,z4,z5,z6]),(0,[z1,z273,z2,z217,z19,z6]),(0,[z1,z176,z3,z4,z99,z28]),(0,[z422,z2,z3,z4,z5,z28])]],
   [[(0,[z1,z2,z167,z4,z5,z6]),(0,[z1,z2,z196,z200,z5,z6]),(0,[z1,z2,z3,z984,z4,z6]),(0,[z1,z44,z667,z3,z5,z56])],[(0,[z1,z2,z10,z4,z5,z41]),(0,[z1,z2,z3,z503,z27,z6])],[(0,[z1,z3,z4,z985,z5,z6])],[(0,[z20,z3,z50,z5,z6,z41]),(0,[z1,z390,z3,z4,z19,z6]),(0,[z1,z2,z88,z4,z5,z41])],[(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z987,z3,z4,z5,z6])],[(0,[z1,z377,z410,z4,z5,z6])],[(0,[z1,z24,z3,z4,z258,z6]),(0,[z1,z2,z456,z464,z5,z6])],[(0,[z1,z2,z3,z4,z5,z988])],[(0,[z1,z24,z3,z358,z4,z6]),(0,[z1,z2,z10,z4,z394,z5])],[(0,[z1,z989,z3,z4,z5,z6]),(0,[z1,z377,z3,z18,z5,z6]),(0,[z1,z39,z179,z18,z5,z6]),(0,[z1,z35,z2,z3,z18,z16])],[(0,[z78,z254,z3,z4,z11,z6]),(0,[z1,z2,z3,z990,z5,z6]),(0,[z1,z991,z3,z4,z5,z6])],[(0,[z132,z24,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z992]),(0,[z1,z254,z3,z4,z5,z41])],[(0,[z1,z2,z274,z4,z314,z6]),(0,[z1,z2,z3,z993,z5,z6])],[(0,[z1,z2,z994,z4,z5,z6]),(0,[z1,z3,z50,z5,z766,z6]),(0,[z1,z8,z3,z4,z5,z28])],[(0,[z1,z2,z10,z50,z19,z6]),(0,[z1,z2,z410,z4,z19,z6]),(0,[z1,z2,z3,z228,z249,z6])],[(0,[z1,z2,z3,z4,z133,z6]),(0,[z2,z3,z10,z50,z19,z6]),(0,[z1,z995,z2,z3,z4,z5])],[(0,[z1,z20,z3,z4,z158,z6]),(0,[z1,z2,z173,z4,z5,z6]),(0,[z1,z2,z3,z4,z996,z6])],[(0,[z1,z2,z3,z997,z5,z6]),(0,[z512,z2,z3,z4,z5,z41])],[(0,[z1,z13,z3,z4,z5,z6]),(0,[z86,z2,z38,z4,z5,z41]),(0,[z83,z2,z3,z464,z5,z41]),(0,[z1,z998,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z999]),(0,[z1,z35,z2,z3,z624,z4])],[(0,[z1,z363,z3,z50,z5,z6])],[(0,[z1,z1000,z24,z3,z4,z5]),(0,[z1,z160,z167,z4,z5,z6]),(0,[z1,z306,z2,z3,z4,z19]),(0,[z1,z121,z2,z4,z231,z6]),(0,[z1,z2,z3,z595,z5,z414]),(0,[z1,z68,z3,z4,z5,z69]),(0,[z1,z1001,z2,z3,z4,z5])],[(0,[z1,z2,z3,z131,z5,z6]),(0,[z2,z20,z3,z50,z5,z41]),(0,[z1,z296,z456,z4,z5,z6])],[(0,[z1,z425,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z216,z6]),(0,[z1,z2,z196,z25,z5,z28])],[(0,[z96,z2,z769,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1002])],[(0,[z1,z2,z10,z4,z427,z6]),(0,[z7,z2,z3,z4,z11,z28])],[(0,[z1,z2,z3,z4,z1003,z6]),(0,[z1,z2,z230,z4,z5,z28])],[(0,[z327,z20,z3,z4,z5,z6]),(0,[z1,z187,z2,z4,z19,z245]),(0,[z1,z269,z2,z3,z4,z311]),(0,[z1,z1004,z3,z4,z5,z6]),(0,[z1,z273,z306,z2,z4,z5])],[(0,[z1,z20,z10,z50,z5,z6]),(0,[z1,z20,z410,z4,z5,z6]),(0,[z1,z2,z275,z4,z547,z6]),(0,[z1,z2,z3,z528,z11,z6])],[(0,[z1,z2,z10,z1005,z4,z6]),(0,[z663,z2,z38,z4,z5,z6]),(0,[z1,z2,z192,z18,z5,z6])],[(0,[z183,z20,z126,z4,z5,z6]),(0,[z1,z2,z38,z448,z5,z6]),(0,[z1,z65,z2,z4,z5,z300]),(0,[z1,z2,z3,z4,z5,z1006]),(0,[z1,z2,z4,z5,z6,z1007])],[(0,[z1,z2,z10,z380,z5,z6]),(0,[z78,z24,z3,z4,z11,z6]),(0,[z1,z646,z3,z4,z11,z6]),(0,[z64,z2,z3,z50,z19,z6]),(0,[z1,z2,z3,z4,z1008,z5]),(0,[z1,z2,z3,z4,z1009,z6])]],
   [[(0,[z1,z24,z3,z4,z5,z41]),(0,[z1,z20,z3,z18,z5,z6]),(0,[z1,z369,z3,z4,z334,z6]),(0,[z1,z487,z2,z4,z11,z6]),(0,[z1,z2,z1010,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z267]),(0,[z83,z2,z38,z4,z5,z41]),(0,[z1,z35,z2,z38,z4,z16]),(0,[z1,z103,z2,z217,z5,z6]),(0,[z1,z3,z4,z271,z11,z6])],[(0,[z1,z24,z4,z5,z297,z6]),(0,[z1,z2,z4,z1011,z5,z6]),(0,[z83,z296,z3,z4,z5,z41])],[(0,[z1,z707,z20,z4,z5,z6]),(0,[z1,z2,z3,z1012,z4,z6]),(0,[z1,z476,z3,z4,z348,z6]),(0,[z1,z306,z363,z3,z4,z5])],[(0,[z132,z2,z10,z50,z5,z6]),(0,[z96,z2,z10,z18,z5,z6])],[(0,[z1,z544,z3,z61,z5,z6]),(0,[z1,z382,z2,z3,z5,z171]),(0,[z2,z3,z4,z19,z28,z41]),(0,[z1,z2,z3,z528,z258,z6]),(0,[z1,z1013,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z716])],[(0,[z1,z2,z126,z4,z5,z28]),(0,[z1,z80,z3,z574,z5,z6]),(0,[z1,z2,z167,z45,z5,z6]),(0,[z1,z2,z3,z1014,z5,z6])],[(0,[z1,z24,z3,z4,z394,z5]),(0,[z1,z129,z2,z4,z48,z28]),(0,[z1,z2,z3,z4,z1015,z6])],[(0,[z1,z2,z3,z4,z1016,z6]),(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z377,z456,z4,z5,z6])],[(0,[z1,z8,z481,z4,z5,z6])],[(0,[z1,z2,z3,z50,z158,z6]),(0,[z2,z98,z38,z4,z5,z6])],[(0,[z1,z2,z3,z4,z87,z6]),(0,[z1,z2,z3,z4,z11,z602]),(0,[z1,z35,z2,z3,z4,z490]),(0,[z1,z487,z2,z358,z4,z6]),(0,[z1,z1018,z3,z4,z5,z6])],[(0,[z1,z2,z50,z795,z5,z6]),(0,[z1,z594,z3,z4,z5,z69]),(0,[z1,z2,z3,z1019,z5,z6])],[(0,[z1,z2,z3,z488,z5,z41]),(0,[z1,z59,z3,z4,z5,z93])],[(0,[z2,z38,z10,z4,z5,z6]),(0,[z1,z313,z2,z18,z5,z6])],[(0,[z1,z2,z1020,z4,z5,z6]),(0,[z1,z59,z3,z4,z5,z101]),(0,[z1,z2,z120,z4,z5,z813])],[(0,[z1,z272,z3,z4,z5,z207]),(0,[z1,z2,z120,z4,z5,z236])],[],[(0,[z1,z2,z213,z4,z22,z6]),(0,[z1,z1021,z3,z4,z5,z6])],[(0,[z1,z68,z3,z4,z5,z108]),(0,[z1,z2,z3,z4,z19,z298]),(0,[z1,z52,z10,z4,z5,z6]),(0,[z1,z306,z2,z3,z50,z5])],[(0,[z1,z949,z2,z38,z4,z5]),(0,[z1,z2,z3,z177,z50,z6]),(0,[z1,z553,z2,z3,z4,z19]),(0,[z83,z377,z3,z4,z5,z41]),(0,[z1,z44,z2,z3,z40,z5]),(0,[z1,z273,z363,z4,z5,z6]),(0,[z1,z1022,z2,z4,z5,z6])],[(0,[z1,z24,z3,z235,z4,z6]),(0,[z1,z250,z36,z4,z5,z6]),(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z1024,z5,z6])],[(0,[z1,z285,z3,z4,z5,z28]),(0,[z1,z2,z410,z50,z5,z6]),(0,[z1,z1025,z3,z4,z5,z6]),(0,[z1,z2,z1026,z4,z5,z6])],[(0,[z1,z2,z3,z206,z5,z619]),(0,[z1,z2,z767,z4,z5,z6]),(0,[z1,z2,z281,z4,z587,z6])],[(0,[z416,z2,z3,z4,z19,z6])],[(0,[z1,z2,z3,z206,z5,z335]),(0,[z1,z2,z3,z4,z5,z1027]),(0,[z1,z2,z1028,z4,z5,z6])],[(0,[z1,z2,z222,z4,z5,z28]),(0,[z1,z2,z10,z464,z5,z6]),(0,[z1,z2,z3,z862,z5,z6]),(0,[z1,z2,z1029,z4,z5,z6]),(0,[z1,z3,z242,z4,z271,z6])],[(0,[z104,z20,z3,z4,z5,z6]),(0,[z1,z2,z38,z1030,z4,z6]),(0,[z1,z2,z3,z33,z100,z41])],[(0,[z1,z2,z3,z146,z5,z6])],[],[(0,[z1,z315,z3,z4,z5,z69]),(0,[z1,z2,z38,z4,z5,z508])],[(0,[z1,z2,z10,z4,z407,z6]),(0,[z1,z20,z456,z4,z5,z6]),(0,[z2,z3,z18,z50,z5,z41]),(0,[z7,z2,z281,z4,z5,z28])]],
   [[(0,[z1,z24,z3,z4,z5,z267]),(0,[z1,z2,z281,z4,z5,z6]),(0,[z1,z2,z430,z4,z5,z23]),(0,[z1,z2,z3,z45,z11,z6])],[(0,[z1,z20,z3,z4,z5,z298]),(0,[z1,z285,z3,z4,z408,z6]),(0,[z1,z667,z3,z32,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z2,z3,z653,z11,z6]),(0,[z1,z2,z38,z4,z288,z6])],[(0,[z1,z187,z2,z50,z5,z245]),(0,[z1,z487,z2,z4,z5,z41])],[(0,[z1,z2,z3,z4,z1032,z6]),(0,[z1,z2,z3,z303,z5,z619]),(0,[z1,z2,z3,z574,z5,z41]),(0,[z1,z2,z3,z438,z5,z41]),(0,[z536,z2,z3,z4,z11,z6]),(0,[z1,z3,z4,z271,z5,z41]),(0,[z1,z477,z3,z61,z5,z6]),(0,[z1,z2,z3,z4,z1033,z6]),(0,[z1,z2,z4,z5,z23,z341])],[(0,[z2,z10,z50,z5,z19,z6]),(0,[z1,z2,z38,z4,z19,z28]),(0,[z1,z2,z3,z280,z232,z6]),(0,[z1,z2,z3,z1034,z4,z6]),(0,[z1,z2,z3,z4,z1035,z6])],[(0,[z1,z2,z3,z303,z5,z335]),(0,[z1,z2,z3,z4,z5,z1036])],[(0,[z663,z20,z3,z4,z5,z6]),(0,[z1,z1037,z3,z4,z5,z6])],[(0,[z1,z20,z3,z448,z5,z6]),(0,[z1,z24,z10,z4,z19,z6]),(0,[z1,z2,z3,z18,z5,z291]),(0,[z1,z1038,z3,z4,z5,z6]),(0,[z1,z1039,z3,z4,z5,z6])],[(0,[z1,z2,z3,z822,z4,z6]),(0,[z1,z2,z769,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z124]),(0,[z1,z296,z10,z4,z5,z6]),(0,[z1,z2,z38,z4,z563,z6]),(0,[z1,z406,z2,z4,z5,z373]),(0,[z346,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z18,z5,z508]),(0,[z1,z2,z3,z4,z5,z82])],[(0,[z83,z20,z3,z4,z5,z41]),(0,[z2,z3,z4,z5,z28,z1040]),(0,[z1,z273,z2,z496,z5,z6]),(0,[z1,z3,z4,z271,z394,z5]),(0,[z1,z1041,z2,z4,z5,z6])],[(0,[z24,z20,z38,z4,z5,z6])],[],[(0,[z1,z2,z50,z5,z6,z738]),(0,[z1,z2,z3,z18,z288,z6]),(0,[z1,z2,z402,z4,z19,z6])],[(0,[z1,z24,z454,z4,z5,z6]),(0,[z1,z262,z2,z4,z197,z6])],[(0,[z1,z1042,z3,z4,z5,z6]),(0,[z1,z2,z402,z436,z5,z6]),(0,[z1,z2,z3,z4,z5,z1043]),(1,[z1,z2,z851,z5,z6])],[(0,[z183,z20,z3,z4,z11,z6]),(0,[z1,z770,z2,z3,z4,z5]),(0,[z1,z2,z3,z18,z19,z28]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z1,z125,z3,z358,z221,z6])],[(0,[z1,z553,z2,z3,z50,z5]),(0,[z1,z36,z234,z4,z5,z6]),(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z3,z177,z4,z6,z185])],[(0,[z1,z2,z274,z4,z5,z619]),(0,[z1,z20,z38,z4,z5,z28]),(0,[z1,z2,z10,z482,z5,z6]),(0,[z1,z254,z38,z4,z5,z6])],[(0,[z1,z2,z3,z1047,z5,z6])],[(0,[z1,z2,z274,z4,z5,z335]),(0,[z1,z24,z3,z1048,z4,z6]),(0,[z104,z2,z3,z50,z5,z6]),(0,[z1,z2,z895,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z1049]),(1,[z1,z2,z3,z775,z6])],[(0,[z1,z2,z3,z4,z5,z1050]),(0,[z1,z2,z3,z18,z563,z6]),(0,[z86,z2,z3,z50,z5,z41]),(0,[z1,z2,z3,z4,z216,z28]),(0,[z1,z122,z2,z3,z5,z171])],[(0,[z1,z2,z3,z206,z5,z6]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z1,z2,z3,z4,z1052,z6]),(0,[z1,z2,z3,z18,z5,z188]),(0,[z1,z2,z3,z4,z556,z41])],[(0,[z24,z20,z3,z18,z5,z6]),(0,[z1,z2,z222,z4,z5,z571]),(0,[z1,z2,z4,z19,z297,z6]),(0,[z1,z2,z4,z5,z1053,z6])],[(0,[z1,z2,z3,z4,z5,z1054]),(0,[z1,z2,z1055,z4,z5,z6]),(0,[z1,z24,z3,z464,z5,z6]),(0,[z1,z2,z3,z1056,z4,z6]),(0,[z1,z2,z456,z50,z5,z6]),(0,[z1,z2,z3,z4,z11,z28])],[(0,[z1,z80,z3,z4,z5,z320]),(0,[z1,z3,z18,z935,z5,z6]),(0,[z1,z425,z3,z4,z19,z6])],[(0,[z1,z2,z3,z50,z5,z298])],[(0,[z1,z2,z3,z4,z314,z41]),(0,[z1,z20,z402,z4,z5,z6]),(0,[z1,z2,z3,z574,z427,z6]),(0,[z1,z36,z154,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z1057])],[(0,[z1058,z2,z3,z4,z5,z6])],[(0,[z132,z24,z10,z4,z5,z6]),(0,[z1,z81,z3,z4,z5,z28])],[(0,[z1,z254,z3,z18,z5,z6])]],
   [[(0,[z1,z2,z1059,z4,z5,z6]),(0,[z1,z55,z3,z4,z408,z6]),(0,[z130,z2,z3,z18,z5,z6]),(0,[z1,z68,z3,z4,z5,z756])],[],[(0,[z1,z2,z3,z380,z19,z6]),(0,[z1,z2,z3,z1060,z18,z6]),(0,[z1,z2,z3,z1061,z4,z6]),(0,[z1,z2,z109,z4,z5,z41]),(0,[z1,z2,z3,z4,z258,z28]),(0,[z1,z3,z235,z4,z271,z6])],[(0,[z1,z1062,z3,z4,z5,z6]),(0,[z1,z1063,z2,z3,z4,z5]),(0,[z1,z363,z25,z4,z5,z6]),(0,[z1,z1064,z3,z4,z5,z6])],[(0,[z1,z2,z3,z303,z5,z6]),(0,[z1,z24,z3,z4,z158,z6]),(0,[z1,z476,z3,z4,z324,z6]),(0,[z2,z10,z4,z50,z5,z41])],[(0,[z346,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z653,z5,z41]),(0,[z83,z2,z3,z50,z5,z41]),(0,[z1,z13,z3,z146,z5,z6]),(0,[z1,z2,z4,z1065,z5,z6])],[(0,[z1,z2,z3,z574,z372,z6])],[(0,[z1,z2,z474,z4,z19,z6]),(0,[z132,z2,z3,z50,z19,z6])],[(0,[z1,z24,z38,z4,z5,z6])],[(0,[z1,z2,z10,z177,z4,z6]),(0,[z1,z13,z281,z4,z5,z6]),(0,[z1,z2,z1066,z4,z5,z6])],[(0,[z1,z36,z381,z4,z5,z6]),(0,[z1,z1067,z3,z4,z5,z6])],[(0,[z1,z1068,z3,z4,z5,z6])],[(0,[z1,z429,z2,z3,z220,z4])],[(0,[z1,z20,z3,z220,z4,z6]),(0,[z1,z2,z38,z50,z5,z28]),(0,[z1,z125,z3,z221,z11,z6])],[(0,[z1,z2,z4,z1069,z5,z6]),(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1,z150,z3,z4,z175,z28]),(0,[z1,z2,z3,z1071,z5,z6]),(0,[z1,z2,z4,z5,z813,z245])],[(0,[z1,z174,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z153])],[(0,[z1,z2,z3,z1072,z5,z6]),(0,[z1,z1073,z2,z4,z5,z6]),(0,[z1,z2,z1074,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1075,z5]),(0,[z1,z2,z3,z4,z1076,z6])],[(0,[z1,z886,z3,z4,z5,z41]),(0,[z1,z2,z3,z1077,z4,z6])],[(0,[z1,z2,z274,z4,z5,z6]),(0,[z2,z3,z4,z417,z11,z6]),(0,[z1,z1078,z3,z4,z5,z6])],[(0,[z1,z24,z3,z18,z5,z6]),(0,[z1,z20,z3,z4,z372,z6]),(0,[z1,z129,z24,z4,z48,z6]),(0,[z1,z2,z213,z4,z268,z6]),(0,[z264,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z425,z3,z4,z5,z551])],[(0,[z1,z20,z88,z4,z5,z6]),(0,[z1,z2,z38,z488,z5,z6]),(0,[z1,z2,z3,z4,z5,z1080])],[(0,[z1,z2,z1081,z4,z5,z6]),(0,[z1,z2,z402,z50,z5,z6]),(0,[z1,z52,z3,z4,z19,z6]),(0,[z58,z2,z3,z4,z19,z6]),(0,[z1,z125,z3,z293,z5,z6]),(0,[z1,z2,z4,z5,z6,z1082])],[(0,[z1,z2,z3,z4,z1083,z6]),(0,[z1,z2,z3,z4,z11,z571])],[(0,[z1,z214,z3,z4,z99,z6]),(0,[z1,z1084,z3,z4,z5,z6])],[(0,[z1,z253,z3,z4,z5,z6]),(0,[z1,z145,z3,z4,z5,z6]),(0,[z1,z2,z167,z4,z5,z238]),(0,[z1,z2,z1085,z4,z5,z6])],[(0,[z1,z2,z410,z4,z628,z6])],[(0,[z1,z2,z3,z4,z5,z1086]),(0,[z78,z2,z3,z4,z11,z28])],[(0,[z1,z189,z3,z4,z99,z6]),(0,[z1,z1087,z3,z4,z5,z6])],[(0,[z1,z2,z10,z448,z5,z6]),(0,[z1,z2,z3,z4,z1088,z6]),(0,[z1,z2,z3,z4,z1089,z6])],[(0,[z1,z1090,z3,z4,z5,z6]),(0,[z1,z2,z3,z448,z563,z6]),(0,[z1,z2,z4,z5,z297,z28]),(0,[z1,z3,z4,z861,z99,z6])],[(0,[z1,z2,z1091,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z1092]),(0,[z1,z2,z3,z134,z638,z6])]],
   [[(0,[z83,z2,z10,z4,z5,z41]),(0,[z1,z285,z3,z4,z401,z6]),(0,[z1,z2,z3,z134,z27,z6])],[(0,[z2,z10,z234,z4,z5,z6])],[(0,[z1,z390,z3,z4,z5,z6]),(0,[z1,z2,z18,z5,z6,z76])],[(0,[z1,z2,z3,z4,z5,z1093]),(0,[z1,z20,z3,z4,z11,z41])],[(0,[z1,z2,z3,z1094,z5,z6]),(0,[z1,z90,z3,z194,z5,z6]),(0,[z1,z160,z3,z4,z5,z153])],[(0,[z1,z8,z3,z4,z11,z6])],[(0,[z1,z2,z167,z4,z5,z153]),(0,[z1,z2,z402,z4,z5,z508])],[(0,[z1,z2,z38,z528,z5,z6]),(0,[z1,z2,z3,z4,z408,z41]),(0,[z1,z59,z3,z4,z11,z60])],[(0,[z1,z2,z3,z18,z587,z6])],[(0,[z1,z2,z3,z4,z53,z248])],[(0,[z1,z2,z3,z601,z5,z298]),(0,[z685,z2,z38,z4,z5,z6]),(0,[z1,z262,z2,z4,z48,z6])],[],[(0,[z1,z20,z4,z795,z5,z6]),(0,[z1,z2,z38,z574,z5,z6]),(0,[z1,z1095,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1096])],[(0,[z1,z2,z10,z50,z5,z6]),(0,[z1,z2,z410,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z124]),(0,[z1,z296,z3,z4,z19,z6]),(0,[z654,z2,z3,z4,z5,z28]),(0,[z1,z487,z61,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z900]),(0,[z1,z2,z3,z1097,z5,z6])],[(0,[z1,z1098,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z28,z385])],[(0,[z1,z2,z3,z4,z934,z5]),(0,[z1,z2,z88,z50,z5,z6]),(0,[z1,z2,z230,z4,z216,z6]),(0,[z1,z2,z196,z25,z11,z6]),(0,[z1,z2,z410,z528,z5,z6]),(1,[z1,z3,z806,z5,z6])],[(0,[z1,z2,z3,z4,z427,z320]),(0,[z7,z2,z3,z50,z19,z6]),(0,[z1,z2,z3,z4,z216,z237])],[(0,[z1,z2,z3,z235,z18,z6]),(0,[z1,z2,z3,z235,z4,z28]),(0,[z1,z553,z2,z4,z5,z297]),(0,[z1,z2,z3,z4,z5,z1099])],[(0,[z1,z2,z230,z4,z11,z6]),(0,[z1,z2,z3,z4,z860,z5]),(0,[z2,z3,z4,z5,z41,z658]),(0,[z1,z2,z1100,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1101,z6]),(0,[z1,z2,z1102,z4,z5,z6]),(0,[z1,z2,z3,z4,z1103,z6]),(0,[z1,z24,z456,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z238]),(0,[z1,z2,z1104,z4,z5,z6])],[(0,[z351,z20,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z28,z185])],[(0,[z96,z24,z10,z4,z5,z6]),(0,[z1,z646,z3,z18,z5,z6]),(0,[z1,z2,z38,z4,z5,z602]),(0,[z1,z2,z3,z482,z19,z6])],[(0,[z1,z20,z3,z50,z5,z28]),(0,[z1,z174,z3,z448,z5,z6]),(0,[z2,z3,z50,z293,z5,z6]),(0,[z1,z1105,z3,z18,z5,z6]),(0,[z1,z487,z2,z18,z5,z6]),(0,[z1,z2,z1106,z4,z5,z6])],[(0,[z1,z344,z3,z61,z5,z6]),(0,[z1,z2,z481,z4,z5,z41]),(0,[z1,z1107,z3,z4,z5,z6])],[(0,[z617,z20,z3,z4,z5,z6]),(0,[z2,z3,z4,z11,z19,z41]),(0,[z1,z2,z4,z259,z5,z41]),(0,[z1,z2,z3,z4,z1108,z6])],[(0,[z1,z176,z3,z4,z99,z41]),(0,[z1,z2,z3,z4,z6,z1109]),(0,[z1,z187,z2,z4,z5,z245])],[(0,[z183,z20,z3,z303,z5,z6]),(0,[z1,z3,z4,z1110,z5,z6])],[(0,[z1,z24,z3,z448,z5,z6]),(0,[z1,z2,z120,z4,z11,z23]),(0,[z1,z2,z3,z33,z203,z6])],[(0,[z1,z2,z3,z4,z5,z1111]),(0,[z1,z2,z10,z4,z5,z508]),(0,[z1,z2,z3,z50,z11,z41]),(0,[z1,z118,z3,z4,z5,z69]),(0,[z1,z306,z2,z3,z242,z4])],[(0,[z1,z2,z126,z4,z11,z6]),(0,[z7,z20,z3,z50,z5,z6]),(0,[z64,z2,z3,z50,z5,z6]),(0,[z51,z2,z3,z18,z5,z41]),(0,[z1,z214,z3,z4,z310,z6])],[(0,[z1,z20,z3,z488,z5,z6]),(0,[z83,z24,z3,z4,z5,z41]),(0,[z1,z55,z3,z4,z401,z6]),(0,[z1,z377,z3,z4,z19,z6])]],
   [[(0,[z2,z3,z4,z19,z625,z6]),(0,[z1,z3,z4,z5,z1112,z6])],[(0,[z1,z2,z10,z4,z288,z6]),(0,[z64,z2,z3,z50,z401,z6]),(0,[z2,z3,z203,z50,z5,z6]),(0,[z1,z2,z3,z572,z100,z6]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z2,z3,z4,z716,z16])],[(0,[z1,z2,z3,z18,z5,z602]),(0,[z1,z2,z3,z4,z1114,z6])],[],[(0,[z1,z2,z38,z4,z314,z6]),(0,[z20,z3,z4,z5,z6,z101]),(0,[z1,z2,z10,z4,z19,z28]),(0,[z1,z1115,z3,z4,z5,z6])],[(0,[z1,z80,z3,z4,z5,z6]),(0,[z1,z2,z3,z1116,z5,z6])],[(0,[z1,z2,z3,z4,z1117,z6]),(0,[z1,z273,z2,z240,z5,z6]),(0,[z1,z2,z38,z4,z5,z551]),(0,[z1,z2,z3,z562,z27,z6])],[(0,[z1,z2,z222,z4,z133,z6]),(0,[z287,z2,z3,z50,z5,z6]),(0,[z1,z2,z120,z4,z227,z5])],[(0,[z20,z3,z50,z5,z19,z6]),(0,[z1,z2,z3,z1118,z5,z6])],[(0,[z1,z2,z10,z4,z563,z6]),(0,[z1,z2,z3,z482,z556,z6]),(0,[z1,z1119,z3,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z188]),(0,[z1,z2,z3,z1120,z5,z6]),(0,[z1,z2,z3,z436,z19,z6]),(0,[z1,z363,z3,z4,z5,z28]),(0,[z1,z2,z4,z5,z28,z942]),(0,[z1,z2,z1121,z4,z5,z6])],[(0,[z24,z20,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z1122,z6]),(0,[z2,z3,z50,z11,z19,z6]),(0,[z1,z8,z281,z4,z5,z6])],[],[(0,[z20,z3,z4,z5,z127,z6]),(0,[z1,z20,z3,z33,z100,z6]),(0,[z1,z2,z38,z653,z5,z6]),(0,[z1,z1123,z3,z4,z5,z6])],[(0,[z1,z2,z222,z131,z5,z6]),(1,[z2,z10,z50,z5,z41]),(0,[z1,z285,z3,z4,z11,z6])],[(0,[z78,z2,z10,z50,z5,z6]),(0,[z1,z2,z18,z1011,z5,z6])],[(0,[z1,z2,z3,z4,z1124,z6]),(0,[z1,z667,z3,z4,z5,z41]),(0,[z1,z3,z4,z5,z28,z950])],[],[(0,[z1,z20,z10,z4,z5,z28]),(0,[z1,z2,z222,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z298]),(0,[z1,z254,z10,z4,z5,z6]),(0,[z1,z2,z456,z528,z5,z6]),(0,[z1,z2,z3,z32,z5,z364])],[(0,[z1,z1125,z3,z4,z5,z6]),(0,[z1,z2,z192,z4,z19,z6]),(0,[z1,z2,z3,z4,z1126,z6])],[(0,[z1,z1127,z2,z3,z4,z5]),(0,[z1,z2,z3,z1128,z5,z6]),(1,[z1,z2,z4,z5,z813])],[(0,[z1,z3,z61,z219,z5,z6]),(0,[z1,z125,z259,z221,z5,z6])],[(0,[z1,z20,z3,z4,z19,z6]),(0,[z1,z20,z3,z574,z5,z6]),(0,[z1,z20,z3,z438,z5,z6]),(0,[z1,z2,z454,z4,z408,z6])],[(0,[z1,z646,z3,z4,z5,z298]),(0,[z1,z1129,z3,z4,z5,z6]),(0,[z367,z2,z3,z4,z5,z41])],[(0,[z1,z20,z3,z436,z5,z6]),(0,[z512,z2,z10,z4,z5,z6]),(0,[z1,z3,z4,z5,z871,z6])],[(0,[z1,z2,z1130,z4,z5,z6]),(0,[z1,z2,z3,z4,z1131,z6]),(0,[z1,z2,z1132,z4,z5,z6]),(0,[z1,z2,z3,z4,z1133,z6])],[(0,[z96,z2,z10,z574,z5,z6]),(0,[z1,z2,z1134,z4,z5,z6]),(0,[z1,z129,z2,z4,z404,z6])],[(0,[z1,z253,z3,z4,z87,z6]),(0,[z526,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z3,z1136,z5,z6])],[(0,[z1,z81,z167,z4,z5,z6]),(0,[z202,z2,z3,z4,z19,z6])],[(0,[z2,z20,z10,z50,z5,z6]),(0,[z1,z2,z3,z601,z372,z6]),(0,[z1,z273,z2,z217,z5,z28])],[(0,[z83,z2,z3,z528,z5,z41]),(0,[z1,z2,z3,z242,z4,z6])],[(0,[z1,z904,z2,z4,z5,z6])]],
   [[(0,[z20,z3,z4,z293,z5,z6]),(0,[z1,z2,z3,z4,z158,z28]),(0,[z1,z24,z3,z4,z288,z6]),(0,[z1,z2,z38,z4,z5,z320])],[(0,[z141,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z32,z5,z451])],[(0,[z1,z2,z546,z4,z5,z23]),(0,[z1,z125,z3,z806,z5,z6])],[(0,[z1,z2,z3,z4,z5,z41]),(0,[z1,z2,z84,z18,z22,z6])],[(0,[z1,z2,z38,z4,z5,z28]),(0,[z1,z176,z3,z168,z4,z6])],[(0,[z752,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1137]),(0,[z2,z38,z4,z11,z19,z6]),(0,[z1,z1138,z3,z4,z5,z6]),(0,[z111,z2,z3,z438,z19,z6])],[(0,[z1,z2,z546,z4,z5,z434]),(0,[z1,z2,z3,z4,z401,z41]),(0,[z1,z2,z3,z1139,z4,z6]),(0,[z1,z273,z2,z851,z5,z6])],[(0,[z1,z24,z10,z4,z5,z6]),(0,[z20,z3,z4,z50,z5,z41]),(0,[z1,z2,z3,z1140,z5,z6])],[(0,[z183,z20,z3,z18,z5,z6]),(0,[z1,z1141,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z556,z6]),(0,[z1,z24,z88,z4,z5,z6]),(0,[z1,z2,z3,z488,z5,z508]),(0,[z1,z36,z677,z4,z5,z6])],[(0,[z202,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z448,z5,z602]),(0,[z1,z90,z3,z61,z19,z6]),(0,[z1,z2,z3,z4,z5,z1142])],[(0,[z1,z20,z38,z4,z11,z6]),(0,[z1,z273,z2,z242,z217,z6])],[(0,[z1,z2,z10,z50,z5,z28]),(0,[z1,z2,z410,z4,z5,z28]),(0,[z1,z2,z3,z4,z1143,z6]),(0,[z1,z579,z59,z3,z4,z5]),(0,[z1,z1144,z3,z4,z5,z6]),(0,[z1,z4,z5,z297,z157,z6])],[(0,[z1,z2,z402,z4,z5,z6]),(0,[z1,z2,z3,z18,z676,z5]),(0,[z1,z2,z3,z4,z676,z19])],[(0,[z1,z20,z3,z4,z314,z6]),(0,[z1,z90,z3,z480,z5,z6]),(0,[z1,z896,z2,z18,z5,z6]),(0,[z1,z2,z3,z1145,z4,z6]),(0,[z1146,z2,z3,z4,z5,z6])],[(0,[z1,z2,z38,z4,z408,z6]),(0,[z1,z1147,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z551]),(0,[z1,z2,z38,z18,z5,z41]),(0,[z1,z2,z3,z18,z5,z28]),(0,[z1,z2,z3,z50,z19,z6]),(0,[z1,z2,z3,z4,z5,z1148])],[],[(0,[z1,z3,z18,z5,z157,z6]),(0,[z1,z2,z3,z134,z139,z6])],[(0,[z111,z20,z3,z4,z19,z6]),(0,[z1,z129,z20,z4,z48,z6]),(0,[z1,z500,z72,z4,z5,z6])],[(0,[z1,z20,z109,z4,z5,z6]),(0,[z2,z3,z534,z4,z11,z6]),(0,[z1,z1149,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1150])],[(0,[z1,z1151,z2,z3,z18,z5]),(0,[z1,z81,z3,z4,z11,z6])],[(0,[z1,z24,z3,z4,z11,z41]),(0,[z1,z44,z24,z3,z5,z56]),(0,[z512,z24,z3,z4,z5,z6]),(0,[z1,z1152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z900])],[(0,[z1,z2,z3,z4,z1153,z6]),(0,[z86,z24,z38,z4,z5,z6]),(0,[z1,z176,z3,z289,z4,z6])],[(0,[z1,z425,z3,z4,z5,z6])],[(0,[z1,z2,z167,z4,z5,z41]),(0,[z1,z2,z3,z4,z1154,z5])],[(0,[z1,z2,z3,z4,z427,z6]),(0,[z1,z2,z3,z18,z408,z6]),(0,[z1,z2,z3,z33,z232,z6])],[(0,[z1,z2,z3,z1155,z5,z6]),(0,[z1,z2,z84,z4,z547,z6]),(0,[z1,z2,z3,z32,z19,z79]),(0,[z1,z2,z1156,z4,z5,z6])],[(0,[z1,z2,z38,z4,z6,z385]),(0,[z1,z2,z275,z4,z218,z6])],[(0,[z1,z2,z3,z4,z158,z571]),(0,[z1,z2,z3,z4,z19,z291]),(0,[z1,z254,z3,z488,z5,z6]),(0,[z1,z2,z3,z220,z4,z6])],[(0,[z1,z2,z1157,z4,z5,z6]),(0,[z644,z2,z3,z4,z5,z41]),(0,[z1,z2,z1158,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z19,z508])],[(0,[z1,z2,z3,z380,z5,z6]),(0,[z1,z2,z274,z206,z5,z6]),(0,[z1,z2,z3,z4,z407,z619]),(0,[z287,z24,z3,z4,z5,z6]),(0,[z1,z2,z50,z5,z6,z76])],[(0,[z1,z2,z38,z4,z5,z571]),(0,[z1,z176,z38,z4,z99,z6])],[(0,[z1,z2,z3,z4,z407,z335]),(0,[z1,z2,z3,z50,z556,z6]),(0,[z1,z2,z3,z33,z211,z6]),(0,[z1,z2,z1159,z4,z5,z6]),(0,[z1,z2,z3,z4,z1160,z6])],[(0,[z20,z3,z234,z4,z5,z6]),(0,[z1,z2,z4,z5,z1161,z6]),(0,[z1,z2,z3,z4,z5,z1162]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z1163,z3,z4,z5,z6]),(0,[z1,z2,z1164,z4,z5,z6]),(0,[z1,z1165,z3,z4,z5,z6]),(0,[z1,z1166,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z372,z6]),(0,[z1,z2,z38,z50,z11,z6])],[(0,[z1,z2,z474,z4,z5,z6]),(0,[z1,z2,z10,z528,z5,z6]),(0,[z51,z2,z38,z18,z5,z6])],[(0,[z1,z1167,z2,z4,z5,z6])],[(0,[z1,z2,z3,z50,z314,z6]),(0,[z1,z2,z3,z1168,z4,z6])],[(0,[z1,z2,z3,z4,z133,z41]),(0,[z1,z2,z3,z4,z1169,z6]),(0,[z1,z2,z3,z18,z6,z385]),(0,[z2,z3,z4,z5,z41,z101]),(0,[z1,z794,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z320]),(0,[z1,z20,z3,z32,z5,z79]),(0,[z1,z646,z3,z4,z372,z6]),(0,[z1,z2,z3,z50,z5,z551]),(0,[z1,z2,z173,z4,z5,z41]),(0,[z1,z2,z481,z482,z5,z6])],[(0,[z1,z24,z3,z50,z5,z28]),(0,[z1,z3,z806,z221,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1170]),(0,[z1,z20,z3,z4,z5,z291]),(0,[z1,z2,z1171,z4,z5,z6]),(0,[z1,z2,z481,z18,z5,z6]),(0,[z1,z13,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z1172,z6]),(0,[z1,z2,z3,z4,z70,z716])],[(0,[z1,z2,z3,z4,z19,z188]),(0,[z1,z384,z3,z221,z5,z6]),(0,[z1,z2,z3,z134,z284,z6])],[(0,[z1,z2,z274,z303,z5,z6]),(0,[z24,z20,z3,z4,z19,z6]),(0,[z1,z2,z3,z18,z5,z571]),(0,[z96,z2,z10,z4,z5,z320]),(0,[z1,z2,z109,z50,z5,z6]),(0,[z1,z176,z3,z18,z99,z6]),(0,[z422,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z1173,z5]),(0,[z1,z2,z4,z5,z1174,z6])],[(0,[z1,z2,z456,z4,z5,z28]),(0,[z1,z35,z2,z3,z4,z716])],[(0,[z1,z2,z3,z131,z5,z41]),(0,[z2,z3,z4,z50,z19,z41]),(0,[z1,z59,z3,z4,z5,z756])],[(0,[z51,z2,z10,z4,z5,z41]),(1,[z2,z3,z50,z19,z41]),(0,[z1,z2,z3,z4,z216,z41])],[(0,[z1,z193,z419,z4,z5,z6]),(0,[z1,z59,z38,z4,z5,z60]),(0,[z1,z36,z154,z4,z19,z6]),(0,[z1,z2,z3,z4,z1175,z5]),(0,[z1,z2,z3,z4,z5,z1176])],[(0,[z1,z24,z3,z488,z5,z6]),(0,[z1,z1177,z3,z4,z5,z6]),(0,[z1,z1127,z2,z3,z18,z5]),(0,[z1,z2,z3,z4,z6,z1178])],[(0,[z1,z2,z3,z4,z1179,z6])],[(0,[z1,z52,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z5,z602]),(0,[z1,z2,z454,z4,z401,z6]),(0,[z1,z1180,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1181])],[(0,[z1,z10,z4,z5,z157,z6]),(0,[z1,z3,z4,z19,z766,z6])],[(0,[z1,z2,z3,z1048,z4,z6]),(0,[z1,z2,z3,z448,z5,z28]),(0,[z1,z2,z3,z4,z6,z1182])],[(0,[z1,z3,z4,z5,z6,z928]),(0,[z1,z2,z3,z4,z19,z1183]),(0,[z1,z296,z3,z4,z628,z6]),(0,[z1,z2,z3,z4,z1184,z5])],[(0,[z1,z20,z3,z18,z5,z41]),(0,[z1,z390,z230,z4,z5,z6])],[(0,[z141,z24,z3,z4,z5,z6]),(0,[z1,z390,z3,z4,z5,z237]),(0,[z83,z2,z3,z4,z5,z1040])],[(0,[z1,z2,z3,z464,z5,z6]),(0,[z1,z8,z3,z18,z5,z6]),(0,[z1,z2,z4,z851,z5,z6])],[(0,[z1,z273,z2,z17,z5,z6])],[(0,[z1,z886,z3,z50,z5,z6]),(0,[z1,z59,z3,z18,z5,z60]),(0,[z1,z2,z109,z4,z5,z508])],[(0,[z1,z2,z3,z601,z19,z6])]],
   [[(0,[z1,z2,z345,z4,z19,z6])],[(0,[z1,z2,z3,z4,z407,z6]),(0,[z1,z24,z3,z33,z100,z6]),(0,[z1,z2,z3,z4,z181,z564])],[(0,[z1,z44,z2,z3,z11,z56]),(0,[z1,z2,z3,z376,z5,z79])],[],[(0,[z1,z2,z3,z1185,z5,z6]),(0,[z1,z2,z3,z4,z5,z1186]),(0,[z1,z429,z24,z3,z4,z5]),(0,[z1,z2,z3,z50,z5,z320]),(0,[z1,z2,z3,z208,z5,z491])],[(0,[z1,z174,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z87,z41])],[(0,[z1,z2,z3,z4,z5,z1187])],[(0,[z1,z2,z3,z380,z133,z6]),(0,[z1,z2,z3,z4,z6,z1188])],[(0,[z2,z38,z10,z4,z5,z41]),(0,[z1,z2,z38,z50,z5,z41])],[(0,[z1,z2,z3,z4,z133,z267]),(0,[z1,z2,z3,z1189,z5,z6])],[(0,[z1,z24,z3,z574,z5,z6]),(0,[z1,z24,z3,z438,z5,z6]),(0,[z1,z273,z24,z217,z5,z6]),(0,[z1,z2,z3,z4,z92,z564]),(0,[z1,z2,z120,z4,z5,z375]),(0,[z1,z35,z2,z3,z4,z204])],[(0,[z2,z3,z50,z457,z5,z6]),(0,[z1,z429,z2,z3,z4,z11]),(0,[z1,z377,z3,z4,z628,z6]),(0,[z1,z2,z1190,z4,z5,z6])],[(0,[z1,z296,z3,z4,z5,z6]),(0,[z1,z2,z10,z653,z5,z6]),(0,[z1,z2,z3,z4,z5,z124]),(0,[z1,z2,z402,z4,z5,z28])],[(0,[z1,z20,z3,z601,z5,z6]),(0,[z1,z2,z3,z1145,z18,z6]),(0,[z1,z68,z3,z4,z5,z127]),(0,[z1,z2,z1191,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1192,z6]),(0,[z1,z20,z345,z4,z5,z6]),(0,[z1,z2,z38,z4,z401,z6])],[(0,[z1,z20,z3,z50,z11,z6]),(0,[z169,z24,z3,z4,z5,z6]),(0,[z1,z2,z38,z4,z5,z102]),(0,[z1,z68,z3,z4,z5,z357]),(0,[z1,z2,z3,z4,z1193,z6]),(0,[z1,z2,z84,z95,z4,z6])],[(0,[z51,z20,z3,z18,z5,z6]),(0,[z1,z2,z3,z131,z5,z267]),(0,[z1,z2,z4,z5,z6,z1194]),(0,[z261,z2,z3,z4,z5,z41]),(0,[z1,z2,z1195,z4,z5,z6])],[(0,[z1,z2,z1196,z4,z5,z6])],[(0,[z1,z524,z2,z4,z5,z300]),(0,[z2,z3,z4,z5,z1040,z6]),(0,[z1,z2,z3,z4,z6,z1197])],[(0,[z1,z2,z120,z18,z5,z23]),(0,[z1,z254,z109,z4,z5,z6]),(0,[z1,z2,z3,z1198,z4,z6]),(0,[z1199,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z806,z5,z6])],[(0,[z1200,z2,z3,z4,z5,z6])],[(0,[z1,z2,z126,z18,z5,z6]),(0,[z1,z20,z3,z4,z5,z619]),(0,[z1,z2,z3,z482,z5,z6]),(0,[z1,z2,z3,z1201,z5,z6]),(0,[z1,z553,z2,z173,z4,z5]),(0,[z1,z313,z2,z4,z6,z385])],[(0,[z1,z1202,z3,z4,z5,z6]),(0,[z1,z129,z2,z18,z48,z6]),(0,[z1,z2,z3,z178,z27,z6]),(0,[z1,z2,z3,z146,z5,z41]),(0,[z1,z1203,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z335]),(0,[z1,z2,z3,z4,z1204,z6]),(0,[z1,z1205,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1206])],[(0,[z1,z2,z275,z4,z22,z6]),(0,[z1,z667,z3,z177,z4,z6])],[(0,[z1,z2,z222,z4,z158,z6]),(0,[z1,z37,z179,z4,z5,z6]),(0,[z1,z273,z306,z2,z217,z5])],[(0,[z1,z44,z2,z3,z5,z336]),(0,[z1,z2,z281,z4,z5,z41]),(0,[z1,z273,z2,z394,z217,z5]),(0,[z1,z2,z3,z4,z1207,z6])],[(0,[z1,z2,z3,z4,z5,z1208]),(0,[z183,z20,z10,z4,z5,z6]),(0,[z264,z2,z10,z4,z5,z6]),(0,[z1,z21,z2,z4,z48,z6]),(0,[z1,z2,z3,z18,z5,z102]),(0,[z1,z2,z3,z33,z399,z6])],[(0,[z1,z176,z3,z4,z114,z6])],[(0,[z1,z24,z3,z4,z556,z6]),(0,[z1,z2,z3,z4,z1209,z6]),(0,[z1,z979,z3,z4,z5,z6]),(0,[z1,z2,z3,z220,z18,z6]),(0,[z1,z2,z3,z220,z4,z28])],[(0,[z1,z2,z3,z4,z5,z1210]),(0,[z1,z377,z3,z4,z5,z6]),(0,[z1,z39,z179,z4,z5,z6])],[(0,[z1,z20,z3,z4,z92,z70]),(0,[z1,z2,z10,z4,z5,z320]),(0,[z1,z2,z4,z5,z6,z738]),(0,[z2,z3,z18,z5,z28,z41]),(0,[z1,z1211,z3,z4,z5,z6]),(0,[z1,z2,z1212,z4,z5,z6])]],
   [[],[(0,[z1,z2,z3,z4,z1213,z6]),(0,[z1,z2,z3,z50,z5,z1183])],[(0,[z1,z24,z3,z4,z314,z6]),(0,[z1,z20,z3,z4,z628,z6]),(0,[z1,z363,z3,z4,z11,z6]),(0,[z1,z529,z154,z4,z5,z6])],[(0,[z1,z2,z10,z4,z5,z28]),(0,[z1,z2,z3,z1214,z5,z6]),(0,[z1,z3,z4,z5,z69,z756])],[(0,[z1,z24,z3,z4,z5,z551]),(0,[z1,z2,z481,z50,z5,z6]),(0,[z1,z2,z3,z4,z74,z70])],[(0,[z1,z2,z88,z4,z5,z28]),(1,[z2,z3,z4,z914,z6])],[(0,[z7,z2,z3,z4,z19,z28]),(0,[z1,z2,z3,z32,z5,z900]),(0,[z1,z2,z4,z1215,z5,z6])],[(0,[z1,z2,z3,z1216,z5,z6]),(0,[z1,z322,z2,z217,z5,z6]),(0,[z1,z2,z3,z1168,z18,z6]),(0,[z1,z2,z3,z1217,z4,z6]),(0,[z1,z3,z61,z806,z5,z6])],[(0,[z1,z24,z109,z4,z5,z6]),(0,[z1,z2,z1218,z4,z5,z6])],[(0,[z1,z2,z222,z18,z5,z6]),(0,[z1,z2,z3,z436,z5,z6]),(0,[z1,z2,z3,z528,z19,z6]),(0,[z1,z2,z25,z851,z5,z6])],[(0,[z1,z20,z10,z4,z11,z6]),(0,[z1,z150,z3,z460,z4,z6]),(0,[z1,z306,z2,z3,z4,z5])],[(0,[z1,z24,z3,z653,z5,z6]),(0,[z1,z1219,z3,z4,z5,z6]),(0,[z1,z2,z3,z177,z4,z6])],[(0,[z1,z20,z3,z4,z587,z6]),(0,[z1,z646,z3,z4,z19,z6]),(0,[z1,z646,z3,z574,z5,z6]),(0,[z1,z1220,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1221]),(0,[z1,z1222,z2,z3,z4,z5])],[(0,[z1,z2,z10,z4,z408,z6]),(0,[z1,z2,z167,z18,z5,z6])],[(0,[z1,z2,z3,z50,z5,z619]),(0,[z1,z2,z18,z5,z1223,z6]),(0,[z1,z2,z3,z4,z1224,z6])],[(0,[z1,z2,z3,z1225,z5,z6])],[(0,[z1,z2,z3,z206,z5,z41]),(0,[z1,z2,z3,z50,z5,z335]),(0,[z1,z2,z38,z4,z133,z6]),(0,[z1,z3,z50,z5,z157,z6]),(0,[z1,z2,z4,z5,z6,z1226]),(0,[z1,z2,z3,z1227,z5,z6]),(0,[z1,z2,z1228,z4,z5,z6]),(0,[z1,z2,z4,z6,z385,z76])],[(0,[z1,z2,z192,z4,z5,z6]),(1,[z1,z3,z4,z5,z756])],[(0,[z1,z2,z3,z4,z1229,z6]),(0,[z1,z2,z3,z4,z5,z1230])],[],[(0,[z1,z20,z3,z4,z5,z6]),(0,[z1,z273,z2,z217,z11,z6])],[(0,[z1,z44,z20,z3,z5,z56]),(0,[z1,z2,z345,z4,z5,z291]),(0,[z1,z2,z3,z1231,z5,z6])],[(0,[z1,z125,z10,z221,z5,z6]),(0,[z1,z306,z2,z3,z4,z11]),(0,[z1,z690,z3,z4,z5,z60])],[(0,[z1,z20,z3,z4,z401,z6]),(0,[z1,z2,z38,z131,z5,z6]),(0,[z1,z1232,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z602]),(0,[z1,z233,z3,z4,z334,z6]),(0,[z1,z2,z3,z1233,z4,z6])],[(0,[z96,z2,z10,z4,z5,z6]),(0,[z1,z2,z38,z4,z216,z6]),(0,[z1,z129,z2,z4,z370,z6]),(0,[z7,z2,z3,z4,z556,z28])],[(0,[z264,z24,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1234,z6]),(0,[z1,z2,z3,z775,z27,z6]),(0,[z1,z2,z3,z1235,z5,z6])],[(0,[z1,z2,z10,z4,z6,z385]),(0,[z1,z2,z3,z50,z628,z6]),(0,[z1,z667,z3,z50,z5,z6]),(0,[z1,z160,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z1236])],[(0,[z287,z2,z3,z4,z5,z28])],[(0,[z1,z2,z3,z303,z5,z41]),(0,[z1,z24,z3,z4,z5,z320]),(0,[z1,z2,z173,z18,z5,z6]),(0,[z1,z13,z3,z482,z5,z6]),(0,[z1,z429,z3,z61,z4,z5])],[]],
   [[(0,[z1,z35,z2,z3,z4,z311]),(0,[z1,z2,z1237,z4,z5,z6])],[(0,[z1,z20,z4,z5,z6,z76]),(0,[z1,z2,z10,z4,z5,z571]),(0,[z1,z176,z10,z4,z99,z6]),(0,[z422,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z867,z50,z6]),(0,[z1,z2,z3,z242,z4,z394])],[(0,[z1,z20,z38,z18,z5,z6]),(0,[z1,z24,z38,z4,z5,z41])],[(0,[z1,z2,z3,z448,z5,z102]),(0,[z367,z2,z3,z50,z5,z6])],[(0,[z1,z2,z10,z50,z11,z6]),(0,[z2,z10,z4,z5,z28,z41]),(0,[z111,z2,z3,z4,z19,z6]),(0,[z1,z2,z410,z4,z11,z6]),(0,[z594,z2,z3,z4,z5,z41]),(0,[z1,z313,z4,z5,z6,z185])],[(0,[z1,z369,z3,z4,z175,z6]),(0,[z1,z2,z345,z4,z5,z188]),(0,[z1,z2,z3,z18,z216,z6]),(0,[z1,z363,z3,z4,z5,z41]),(0,[z1,z575,z2,z4,z5,z245])],[(0,[z132,z24,z3,z4,z133,z6]),(0,[z1,z431,z2,z217,z5,z6]),(0,[z1,z2,z3,z421,z100,z6])],[(0,[z1,z1238,z3,z4,z5,z6])],[(0,[z1,z2,z3,z18,z11,z6]),(0,[z1,z2,z3,z1239,z5,z6])],[(0,[z1,z1240,z3,z4,z5,z6]),(0,[z1,z313,z24,z4,z5,z6]),(0,[z212,z2,z38,z4,z5,z6]),(0,[z1,z2,z321,z200,z5,z6]),(0,[z1,z90,z3,z61,z5,z6]),(0,[z1,z553,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1241])],[(0,[z1,z38,z4,z5,z157,z6]),(0,[z2,z3,z534,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z1242]),(0,[z1,z1243,z3,z4,z5,z6])],[(0,[z1,z363,z3,z4,z394,z5]),(0,[z1,z3,z4,z1244,z5,z6])],[(0,[z1,z2,z274,z4,z5,z41]),(0,[z1,z20,z10,z4,z5,z41]),(0,[z1,z150,z3,z4,z334,z6]),(0,[z132,z24,z3,z131,z5,z6]),(0,[z1,z24,z3,z4,z408,z6]),(0,[z1,z2,z38,z4,z87,z6]),(0,[z1,z2,z3,z45,z19,z6]),(0,[z1,z2,z410,z4,z258,z6]),(0,[z1,z125,z429,z3,z221,z5])],[(0,[z1,z24,z3,z18,z5,z41])],[(0,[z1,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z488,z5,z28])],[(0,[z1,z429,z487,z2,z4,z5])],[(0,[z644,z20,z3,z4,z5,z6]),(0,[z1,z59,z10,z4,z5,z60]),(0,[z64,z55,z3,z50,z5,z6]),(0,[z1,z2,z3,z18,z258,z6]),(0,[z1,z187,z2,z4,z11,z245]),(0,[z1,z125,z487,z221,z5,z6])],[(0,[z1,z2,z3,z50,z401,z6]),(0,[z78,z145,z3,z4,z11,z6]),(0,[z1,z2,z851,z217,z5,z6])],[(0,[z1,z253,z3,z4,z5,z41]),(0,[z1,z2,z3,z50,z5,z102]),(0,[z1,z1245,z3,z4,z5,z6]),(0,[z1,z145,z3,z4,z5,z41])],[(0,[z1,z1246,z2,z3,z4,z5]),(0,[z1,z1247,z3,z4,z5,z6])],[(0,[z2,z10,z534,z4,z5,z6])],[(0,[z1,z2,z3,z1248,z5,z6]),(0,[z1,z1249,z2,z4,z5,z6]),(0,[z1,z553,z2,z3,z4,z11]),(0,[z1,z2,z3,z1250,z5,z6])],[(0,[z20,z3,z4,z417,z5,z6])],[(0,[z1,z2,z3,z50,z6,z876]),(0,[z1,z273,z2,z217,z5,z41]),(0,[z1,z2,z3,z4,z1251,z6])],[(0,[z111,z160,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z1252])],[(0,[z1,z2,z3,z4,z1253,z6]),(0,[z1,z2,z3,z134,z27,z41]),(0,[z1,z2,z1254,z3,z4,z6]),(0,[z1,z363,z3,z235,z4,z6])],[(0,[z1,z20,z3,z45,z5,z6]),(0,[z1,z24,z3,z4,z6,z385]),(0,[z1,z2,z4,z733,z5,z6]),(0,[z633,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z32,z5,z79])],[(0,[z1,z2,z3,z1255,z5,z6]),(0,[z1,z2,z3,z1030,z4,z6]),(0,[z1,z390,z3,z4,z5,z41]),(0,[z1,z2,z3,z1256,z4,z6]),(0,[z1,z1257,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z291]),(0,[z1,z150,z3,z18,z175,z6]),(0,[z1,z3,z4,z11,z157,z6]),(0,[z1,z2,z3,z33,z100,z28]),(0,[z1,z2,z3,z4,z1258,z6]),(0,[z1,z1259,z3,z4,z5,z6])],[(0,[z183,z20,z3,z4,z19,z6]),(0,[z1,z24,z481,z4,z5,z6]),(0,[z1,z2,z38,z146,z5,z6]),(0,[z1,z2,z3,z4,z861,z6])],[(0,[z1,z24,z4,z259,z5,z6]),(0,[z1,z2,z3,z4,z5,z508]),(0,[z2,z3,z4,z5,z41,z325]),(0,[z1,z2,z3,z4,z5,z1260])]],
   [[(0,[z1,z2,z3,z1261,z5,z6]),(0,[z1,z44,z2,z10,z5,z56]),(0,[z1,z2,z192,z4,z216,z6]),(0,[z1,z3,z4,z11,z6,z185]),(0,[z1,z2,z3,z220,z4,z676])],[(0,[z2,z3,z18,z50,z5,z28])],[(0,[z1,z135,z3,z4,z5,z93]),(0,[z1,z2,z3,z1262,z4,z6])],[(0,[z51,z20,z10,z4,z5,z6]),(1,[z20,z3,z50,z19,z6]),(0,[z1,z429,z20,z3,z4,z5]),(0,[z1,z24,z3,z50,z11,z6]),(0,[z1,z2,z3,z4,z288,z6])],[(0,[z1,z160,z3,z50,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1263])],[(0,[z1,z2,z3,z574,z5,z28]),(0,[z1,z2,z3,z4,z1264,z6]),(0,[z1,z2,z167,z50,z5,z6]),(0,[z1,z2,z3,z438,z5,z28]),(0,[z1,z2,z3,z4,z19,z28]),(0,[z1,z2,z3,z1265,z5,z6]),(0,[z1,z1266,z3,z4,z5,z6])],[(0,[z1,z20,z84,z4,z22,z6]),(0,[z1,z2,z10,z50,z5,z41]),(0,[z1,z2,z456,z4,z11,z6]),(0,[z1,z2,z410,z4,z5,z41]),(0,[z172,z2,z3,z4,z5,z28]),(0,[z1,z1267,z3,z4,z5,z6]),(0,[z1,z3,z134,z157,z27,z6])],[(0,[z1,z1268,z3,z4,z5,z6]),(0,[z2,z3,z10,z50,z5,z41])],[(0,[z1,z24,z3,z4,z5,z619]),(0,[z1,z2,z3,z4,z11,z298]),(0,[z1,z306,z2,z3,z18,z5])],[(0,[z1,z2,z3,z4,z1269,z6]),(0,[z1,z2,z3,z1270,z4,z6]),(0,[z78,z2,z3,z18,z11,z6]),(0,[z111,z2,z3,z45,z19,z6]),(0,[z1,z2,z173,z134,z4,z6])],[(0,[z1,z24,z3,z4,z5,z335]),(0,[z1,z2,z3,z4,z563,z6])],[(0,[z1,z2,z3,z4,z5,z1271]),(0,[z1,z2,z38,z4,z5,z82]),(0,[z1,z2,z3,z4,z5,z188]),(0,[z1,z2,z281,z482,z5,z6])],[(0,[z24,z20,z3,z4,z5,z6]),(0,[z1,z2,z10,z4,z401,z6]),(0,[z1,z52,z230,z4,z5,z6]),(0,[z1,z3,z4,z861,z5,z6])],[(0,[z1,z80,z3,z4,z5,z298]),(0,[z1,z2,z10,z4,z5,z102]),(0,[z1,z52,z3,z4,z5,z237]),(0,[z1,z2,z281,z18,z5,z6]),(0,[z1,z2,z3,z847,z18,z6]),(0,[z1,z2,z3,z4,z1272,z6]),(0,[z1,z1273,z3,z4,z5,z6])],[(0,[z1,z2,z3,z206,z407,z6]),(0,[z1,z2,z3,z4,z563,z102]),(0,[z1,z2,z3,z4,z401,z188]),(0,[z1,z1274,z3,z4,z5,z6]),(0,[z1,z1275,z3,z4,z5,z6])],[(0,[z1,z2,z1276,z4,z5,z6]),(0,[z1,z2,z3,z448,z11,z6]),(0,[z2,z3,z4,z19,z368,z6]),(0,[z1,z2,z456,z4,z258,z6]),(0,[z1,z425,z3,z134,z27,z6])],[(0,[z1,z36,z154,z4,z5,z6])],[(0,[z1,z2,z3,z18,z394,z5]),(0,[z1,z2,z3,z4,z394,z19])],[(0,[z83,z2,z3,z4,z11,z41])],[(0,[z1,z254,z3,z4,z5,z6]),(0,[z1,z2,z38,z235,z4,z6])],[(0,[z354,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z133,z6]),(0,[z1,z2,z3,z4,z1277,z6])],[(0,[z183,z20,z3,z4,z314,z6]),(0,[z1,z2,z173,z50,z5,z6])],[(0,[z1,z2,z3,z4,z1278,z6]),(0,[z1,z20,z3,z4,z87,z6]),(0,[z1,z819,z3,z50,z5,z6]),(0,[z1,z3,z61,z5,z6,z424]),(0,[z1,z2,z98,z4,z22,z6])],[(0,[z64,z2,z3,z50,z5,z41]),(0,[z1,z13,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z1279,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z556,z28])],[(0,[z1,z125,z3,z221,z19,z6])],[(0,[z1,z707,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z158,z267]),(0,[z1,z2,z38,z4,z11,z28]),(0,[z1,z68,z3,z50,z5,z69]),(0,[z573,z2,z3,z4,z5,z28]),(0,[z1,z2,z4,z727,z5,z6])],[(0,[z654,z2,z3,z18,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1280])],[(0,[z1,z2,z3,z4,z314,z28]),(0,[z1,z2,z3,z601,z5,z6])],[(0,[z1,z2,z345,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1281]),(0,[z1,z1282,z3,z4,z5,z6]),(0,[z1,z2,z1283,z4,z5,z6])]],
   [[],[(0,[z1,z306,z2,z38,z4,z5]),(0,[z1,z2,z3,z4,z5,z1284]),(0,[z1,z129,z2,z415,z4,z6]),(0,[z1,z1285,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z765,z6])],[(0,[z1,z646,z3,z601,z5,z6]),(0,[z1,z2,z3,z869,z4,z28]),(0,[z1,z150,z3,z4,z861,z6]),(0,[z1,z2,z3,z1286,z4,z6])],[(0,[z1,z174,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z571]),(0,[z1,z2,z230,z4,z5,z124]),(0,[z1,z2,z402,z4,z11,z6]),(0,[z1,z2,z109,z4,z5,z28])],[(0,[z1,z2,z3,z4,z5,z1287])],[(0,[z1,z2,z38,z303,z5,z6])],[(0,[z1,z2,z3,z4,z181,z70]),(0,[z1,z2,z3,z4,z5,z1288])],[(0,[z1,z20,z3,z146,z5,z6]),(0,[z1,z2,z3,z4,z5,z1289]),(0,[z1,z90,z3,z61,z5,z28])],[],[(0,[z1,z2,z3,z4,z1290,z6]),(0,[z1,z2,z3,z436,z5,z82])],[(0,[z1,z2,z274,z4,z407,z6]),(0,[z1,z125,z3,z442,z5,z6]),(0,[z447,z2,z3,z4,z19,z6]),(0,[z1,z762,z3,z4,z11,z6]),(0,[z1,z3,z358,z61,z4,z6])],[(0,[z1,z24,z3,z4,z401,z6]),(0,[z1,z2,z3,z4,z5,z1291])],[(0,[z1,z24,z3,z4,z5,z102]),(0,[z1,z429,z2,z10,z4,z5]),(0,[z1,z363,z38,z4,z5,z6]),(0,[z212,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z1292,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1293])],[(0,[z1,z2,z3,z4,z1294,z6])],[(0,[z1,z20,z3,z4,z19,z41]),(0,[z1,z2,z10,z4,z133,z6]),(0,[z1,z344,z3,z194,z5,z6]),(0,[z1,z3,z4,z5,z41,z1295]),(0,[z1,z2,z3,z4,z92,z70])],[(0,[z1,z2,z3,z50,z87,z6]),(0,[z1,z1296,z3,z4,z5,z6])],[(0,[z1,z8,z3,z4,z19,z6])],[(0,[z1,z2,z10,z18,z19,z6]),(0,[z1,z2,z38,z4,z1075,z5]),(0,[z1,z2,z3,z4,z628,z6])],[(0,[z2,z38,z10,z50,z5,z6]),(0,[z1,z1297,z2,z4,z5,z6]),(0,[z1,z59,z3,z4,z19,z60]),(0,[z1,z2,z3,z4,z5,z1298])],[(0,[z1,z20,z3,z822,z4,z6]),(0,[z2,z3,z4,z914,z19,z6]),(0,[z1,z2,z3,z528,z628,z6]),(0,[z1,z2,z3,z1299,z5,z6]),(0,[z1,z125,z487,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z82]),(0,[z1,z24,z38,z18,z5,z6]),(0,[z1,z2,z3,z4,z1300,z6])],[(0,[z1,z2,z10,z131,z5,z6]),(0,[z1,z80,z3,z4,z427,z6]),(0,[z265,z2,z3,z50,z5,z6])],[(0,[z1,z2,z10,z4,z216,z6]),(0,[z1,z2,z4,z5,z6,z1301]),(0,[z1,z2,z3,z242,z4,z41])],[(0,[z1,z363,z3,z18,z5,z6])],[(0,[z1,z3,z4,z5,z1302,z6]),(0,[z1,z2,z3,z1303,z5,z6])],[(0,[z1,z2,z10,z4,z11,z6]),(0,[z1,z253,z38,z4,z5,z6]),(0,[z1,z145,z38,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z385]),(0,[z1,z2,z3,z4,z5,z1304]),(0,[z1,z1305,z3,z4,z5,z6])],[(0,[z1,z2,z196,z25,z19,z6]),(0,[z7,z2,z3,z4,z587,z28]),(0,[z1,z2,z3,z4,z1306,z6]),(0,[z1,z2,z134,z297,z27,z6])],[(0,[z94,z20,z3,z4,z5,z6]),(0,[z1,z2,z88,z4,z11,z6]),(0,[z1,z2,z3,z4,z587,z6]),(0,[z1,z406,z2,z4,z5,z14]),(0,[z1,z2,z3,z4,z1307,z6]),(0,[z1,z3,z4,z5,z157,z551])],[(0,[z1,z2,z3,z235,z50,z6]),(0,[z1,z2,z3,z4,z5,z1308])],[(0,[z1,z2,z3,z4,z5,z1309]),(0,[z1,z2,z3,z4,z1310,z6]),(0,[z1,z2,z230,z4,z19,z6]),(0,[z1,z667,z4,z5,z6,z76])]],
   [[(0,[z1,z2,z1311,z4,z5,z6]),(0,[z1,z24,z167,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z237]),(0,[z1,z2,z3,z438,z5,z238]),(0,[z1,z2,z3,z4,z19,z238]),(0,[z1,z2,z410,z464,z5,z6])],[(0,[z1,z20,z10,z18,z5,z6]),(0,[z1,z24,z10,z4,z5,z41]),(0,[z1,z80,z3,z4,z372,z6]),(0,[z1,z2,z1312,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1313])],[(0,[z1,z2,z38,z134,z27,z6]),(0,[z1,z3,z4,z5,z41,z185]),(0,[z1,z2,z3,z4,z5,z1314]),(0,[z1,z2,z3,z4,z1315,z6])],[(0,[z1,z20,z3,z206,z5,z6]),(0,[z1,z2,z38,z4,z158,z6]),(0,[z1,z2,z3,z4,z1316,z6]),(0,[z1,z2,z1317,z4,z5,z6]),(0,[z1,z2,z1318,z4,z5,z6])],[(0,[z1,z2,z3,z4,z427,z298]),(0,[z1,z390,z38,z4,z5,z6]),(0,[z1,z2,z1319,z4,z5,z6])],[(0,[z1,z20,z3,z4,z11,z28]),(0,[z1,z2,z3,z1056,z50,z6]),(0,[z1,z2,z3,z1005,z50,z6]),(0,[z1,z390,z3,z4,z5,z124]),(0,[z7,z2,z3,z4,z5,z28]),(0,[z1,z8,z3,z4,z556,z6]),(0,[z1,z125,z3,z638,z5,z6])],[(0,[z51,z20,z3,z4,z19,z6]),(0,[z1,z2,z286,z205,z5,z6]),(0,[z1,z322,z2,z17,z5,z6]),(0,[z1,z429,z2,z3,z4,z19]),(0,[z78,z2,z402,z4,z11,z6]),(0,[z1,z2,z3,z4,z1320,z6])],[(0,[z20,z3,z4,z5,z28,z41]),(0,[z2,z10,z657,z4,z5,z6]),(0,[z64,z2,z454,z50,z5,z6]),(0,[z1,z145,z3,z18,z5,z6]),(0,[z1,z1321,z2,z3,z4,z5]),(0,[z1,z2,z402,z4,z5,z41]),(0,[z1,z2,z3,z775,z134,z6])],[(0,[z1,z1322,z3,z4,z5,z6]),(0,[z1,z313,z20,z4,z5,z6]),(0,[z1,z2,z3,z528,z5,z6]),(0,[z1,z331,z3,z4,z5,z60])],[(0,[z1,z2,z120,z4,z19,z23])],[(0,[z1,z20,z196,z25,z5,z6]),(0,[z1,z2,z3,z50,z19,z41]),(0,[z2,z3,z4,z11,z28,z41]),(0,[z1,z2,z3,z4,z5,z1323]),(0,[z1,z176,z3,z4,z266,z6])],[(0,[z1,z646,z3,z4,z5,z6]),(0,[z1,z2,z126,z4,z19,z6])],[(0,[z1,z1105,z3,z4,z5,z6])],[(0,[z1,z20,z230,z4,z5,z6]),(0,[z1,z2,z3,z1324,z5,z6]),(0,[z2,z3,z4,z684,z5,z41]),(0,[z1,z2,z3,z4,z5,z1325]),(0,[z1,z129,z2,z4,z727,z6])],[(0,[z1,z20,z3,z4,z5,z237]),(0,[z1,z20,z3,z4,z5,z238]),(0,[z1,z371,z179,z4,z5,z6]),(0,[z1,z2,z3,z4,z815,z5]),(0,[z1,z2,z3,z161,z5,z79]),(0,[z550,z2,z3,z4,z19,z6]),(0,[z591,z2,z3,z4,z19,z6]),(0,[z1,z313,z2,z32,z4,z5])],[(0,[z1,z2,z3,z1326,z5,z6]),(0,[z1,z24,z3,z4,z133,z6]),(0,[z1,z2,z3,z18,z158,z6]),(0,[z2,z3,z203,z4,z11,z6]),(0,[z1327,z2,z3,z4,z5,z6]),(0,[z1,z1328,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1329,z5,z6]),(0,[z1,z24,z173,z4,z5,z6]),(0,[z1,z150,z10,z4,z175,z6]),(0,[z1,z2,z3,z50,z5,z82])],[(0,[z1,z37,z42,z4,z5,z6])],[(0,[z1,z2,z358,z4,z259,z6]),(0,[z1,z2,z4,z5,z6,z76])],[(0,[z1,z425,z3,z4,z5,z41])],[],[(0,[z1,z2,z3,z4,z427,z41]),(0,[z1,z2,z3,z4,z1330,z6])],[(0,[z1,z24,z3,z131,z5,z6])],[(0,[z1,z24,z3,z4,z216,z6]),(0,[z1,z2,z3,z4,z5,z602]),(0,[z1,z2,z3,z177,z32,z4])],[(0,[z20,z3,z534,z4,z5,z6]),(0,[z132,z24,z3,z4,z158,z6]),(0,[z1,z2,z3,z220,z4,z41]),(0,[z1,z125,z429,z3,z4,z5])],[(0,[z1,z2,z3,z1331,z5,z6])],[(0,[z362,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z1332,z5,z6]),(0,[z1,z2,z481,z4,z5,z28]),(0,[z1,z3,z4,z175,z494,z6]),(0,[z1,z273,z363,z217,z5,z6])],[(0,[z1,z20,z3,z4,z5,z153]),(0,[z1,z2,z3,z380,z5,z41]),(0,[z1,z285,z3,z4,z19,z6]),(0,[z1,z2,z410,z18,z5,z6]),(0,[z2,z3,z4,z11,z19,z28]),(0,[z1,z2,z4,z259,z5,z28])],[],[(0,[z183,z20,z3,z4,z5,z619]),(0,[z1,z2,z3,z601,z5,z28]),(0,[z78,z2,z10,z4,z11,z6]),(0,[z111,z2,z3,z4,z19,z238])],[],[(0,[z1,z20,z274,z4,z5,z6]),(0,[z183,z20,z3,z4,z5,z335]),(0,[z1,z2,z222,z4,z19,z6]),(0,[z1,z2,z3,z4,z5,z1333]),(0,[z1,z2,z3,z4,z372,z41]),(0,[z1,z2,z3,z50,z11,z28]),(0,[z1,z2,z3,z4,z1334,z6]),(0,[z1,z2,z3,z4,z5,z1335])]],
   [[(0,[z1,z2,z474,z4,z5,z41]),(0,[z132,z2,z3,z50,z5,z41]),(0,[z1,z1336,z3,z4,z5,z6]),(0,[z1,z721,z3,z4,z5,z6])],[(0,[z617,z2,z3,z4,z11,z6])],[(0,[z1,z2,z3,z33,z6,z655])],[(0,[z1,z2,z126,z4,z314,z6]),(0,[z1,z24,z3,z1012,z4,z6]),(0,[z1,z2,z3,z4,z5,z1337])],[(0,[z1,z2,z3,z4,z1338,z6]),(0,[z1,z429,z2,z3,z50,z5]),(0,[z1,z141,z3,z4,z99,z6])],[(0,[z1,z2,z3,z1339,z5,z6])],[(0,[z1,z174,z3,z4,z87,z6]),(0,[z1,z13,z3,z4,z587,z6])],[(0,[z1,z2,z3,z1340,z5,z6]),(0,[z1,z2,z230,z50,z5,z6]),(0,[z1,z2,z3,z488,z11,z6])],[(0,[z1,z2,z3,z4,z5,z1341]),(0,[z1,z2,z3,z4,z5,z1342]),(0,[z1,z2,z3,z50,z5,z237]),(0,[z1,z187,z2,z18,z5,z245])],[(0,[z1,z2,z3,z4,z1343,z6])],[(0,[z111,z2,z3,z4,z19,z153]),(0,[z1,z2,z3,z4,z5,z1344])],[(0,[z1,z24,z3,z4,z87,z6]),(0,[z1,z390,z192,z4,z5,z6]),(0,[z1,z2,z4,z19,z6,z76]),(0,[z1,z187,z2,z97,z4,z5])],[(0,[z1,z20,z3,z134,z27,z6]),(0,[z1,z2,z3,z4,z763,z5]),(0,[z1,z1000,z2,z3,z4,z5]),(0,[z1,z2,z3,z45,z5,z6]),(0,[z1,z2,z3,z4,z5,z1345])],[(0,[z1,z20,z222,z4,z5,z6]),(0,[z1,z2,z3,z4,z1346,z6]),(0,[z1,z2,z1347,z4,z5,z6]),(0,[z1,z187,z2,z4,z5,z366])],[(0,[z1,z24,z38,z50,z5,z6]),(0,[z1,z2,z3,z653,z5,z6]),(0,[z1,z819,z3,z4,z5,z6]),(0,[z7,z13,z3,z4,z5,z28]),(0,[z1,z2,z3,z1348,z5,z6])],[(0,[z654,z2,z10,z4,z5,z6]),(0,[z1,z52,z3,z4,z5,z41]),(0,[z141,z2,z3,z4,z11,z6]),(0,[z1,z667,z313,z4,z5,z6])],[(0,[z1,z2,z50,z5,z1161,z6]),(0,[z1,z429,z2,z3,z358,z4])],[(0,[z265,z24,z3,z4,z5,z6])],[(0,[z1,z2,z3,z653,z5,z102]),(0,[z1,z2,z3,z33,z249,z6]),(0,[z1,z2,z3,z4,z628,z28]),(0,[z1,z667,z3,z4,z5,z28])],[(0,[z1,z2,z10,z235,z4,z6]),(0,[z1,z1349,z3,z4,z5,z6])],[(0,[z1,z2,z38,z4,z5,z298]),(0,[z1,z2,z3,z32,z5,z414]),(0,[z1,z273,z2,z432,z5,z6]),(0,[z1,z2,z3,z4,z742,z5])],[(0,[z1,z2,z3,z4,z1350,z6]),(0,[z1,z2,z3,z50,z5,z153]),(0,[z1,z254,z3,z4,z5,z82])],[(0,[z1,z2,z3,z4,z5,z1351]),(0,[z1,z2,z1352,z4,z19,z6])],[],[(0,[z1,z20,z38,z4,z19,z6]),(0,[z1,z1353,z2,z4,z5,z6]),(0,[z1,z553,z2,z10,z4,z5]),(0,[z1,z2,z84,z4,z22,z6])],[(0,[z1,z2,z274,z50,z5,z6]),(0,[z2,z3,z18,z50,z11,z6])],[(0,[z1,z344,z3,z480,z5,z6]),(0,[z1,z2,z10,z1056,z4,z6]),(0,[z1,z55,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z1354,z6])],[(0,[z1,z2,z3,z4,z407,z41]),(0,[z1,z2,z3,z380,z5,z267])],[(0,[z1,z24,z3,z146,z5,z6])],[(0,[z183,z20,z3,z4,z5,z6]),(0,[z1,z2,z1355,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1356]),(0,[z1,z2,z4,z11,z297,z6]),(0,[z2,z3,z4,z5,z375,z28])],[(0,[z1,z2,z474,z380,z5,z6]),(0,[z1,z2,z3,z574,z11,z6]),(0,[z1,z2,z456,z18,z5,z6]),(0,[z1,z2,z3,z438,z11,z6]),(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z377,z3,z4,z258,z6])],[(0,[z1,z253,z3,z50,z5,z6]),(0,[z1,z2,z1357,z4,z5,z6]),(0,[z1,z145,z3,z50,z5,z6])]],
   [[(0,[z1,z2,z474,z4,z5,z267]),(0,[z1,z24,z281,z4,z5,z6]),(0,[z1,z2,z3,z18,z5,z298]),(0,[z1,z10,z4,z717,z5,z6]),(0,[z1,z2,z38,z242,z4,z6]),(0,[z1,z2,z3,z1358,z5,z6])],[(0,[z1,z2,z3,z4,z1359,z6]),(0,[z2,z3,z50,z5,z6,z658]),(0,[z1,z160,z3,z45,z5,z6]),(0,[z1,z2,z3,z1360,z5,z6])],[(0,[z1,z2,z1361,z4,z5,z6]),(0,[z1,z2,z3,z4,z676,z5])],[(0,[z1,z2,z3,z4,z5,z1362]),(0,[z1,z80,z3,z4,z19,z6]),(0,[z1,z81,z3,z4,z19,z6]),(0,[z1,z81,z3,z438,z5,z6]),(0,[z1,z2,z3,z134,z618,z6]),(0,[z1,z2,z4,z48,z727,z6])],[(0,[z1,z1363,z3,z4,z5,z6]),(0,[z617,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z92,z625])],[(0,[z1,z2,z3,z4,z5,z28]),(0,[z1,z2,z10,z303,z5,z6]),(0,[z1,z384,z3,z201,z5,z6]),(0,[z1,z2,z3,z1364,z4,z6])],[(0,[z24,z3,z4,z5,z28,z41]),(0,[z1,z1321,z2,z3,z18,z5]),(0,[z1,z296,z3,z4,z5,z41]),(0,[z83,z2,z410,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z1365]),(0,[z1,z553,z425,z3,z4,z5])],[(0,[z1,z2,z25,z318,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1366]),(0,[z1,z2,z3,z4,z401,z28]),(0,[z1,z390,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z181,z57]),(0,[z1,z2,z1367,z4,z5,z6])],[(0,[z78,z2,z3,z488,z11,z6]),(0,[z1,z1368,z3,z4,z5,z6])],[(0,[z64,z20,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z1369]),(0,[z1,z24,z3,z4,z5,z82]),(0,[z83,z2,z3,z18,z5,z41]),(0,[z1,z59,z635,z3,z4,z5])],[(0,[z1,z667,z3,z4,z6,z385])],[(0,[z1,z363,z10,z4,z5,z6]),(0,[z2,z3,z4,z5,z1040,z41]),(0,[z1,z2,z196,z657,z5,z6]),(0,[z1,z187,z2,z412,z4,z5])],[(0,[z1,z2,z3,z208,z5,z451]),(0,[z1,z794,z154,z4,z5,z6])],[(0,[z1,z2,z1370,z4,z5,z6]),(0,[z1,z2,z173,z4,z5,z551])],[(0,[z1,z145,z3,z4,z5,z508]),(0,[z1,z2,z3,z4,z676,z11]),(0,[z1,z2,z3,z482,z5,z41]),(0,[z1,z125,z3,z676,z221,z5])],[(0,[z1,z2,z3,z4,z408,z6]),(0,[z2,z568,z3,z50,z5,z6]),(0,[z1,z2,z3,z146,z587,z6])],[(0,[z1,z2,z4,z1371,z5,z6]),(0,[z1,z285,z3,z4,z5,z291]),(0,[z1,z2,z1372,z4,z5,z6]),(0,[z1,z2,z3,z4,z92,z57]),(0,[z1,z3,z4,z5,z6,z1373])],[(0,[z1,z2,z38,z18,z5,z28]),(0,[z680,z2,z38,z4,z5,z6]),(0,[z1,z977,z2,z4,z5,z28])],[(0,[z1,z3,z4,z730,z5,z6]),(0,[z1,z3,z4,z5,z6,z1295])],[(0,[z362,z24,z3,z4,z5,z6]),(0,[z1,z2,z4,z1374,z5,z6]),(0,[z1,z44,z2,z3,z5,z900])],[(0,[z1,z20,z3,z4,z258,z6]),(0,[z1,z2,z3,z50,z934,z5])],[(0,[z1,z2,z3,z1375,z5,z6])],[(0,[z1,z24,z3,z206,z5,z6]),(0,[z1,z20,z3,z358,z4,z6]),(0,[z1,z2,z1376,z4,z5,z6]),(0,[z1,z2,z3,z1377,z4,z6]),(0,[z1,z2,z1378,z4,z5,z6])],[(0,[z1,z2,z1379,z4,z5,z6]),(0,[z1,z2,z1380,z4,z5,z6]),(0,[z1,z2,z3,z4,z11,z551]),(0,[z1,z377,z3,z4,z5,z41]),(0,[z7,z2,z3,z146,z5,z28])],[(0,[z1,z24,z3,z4,z11,z28]),(0,[z1,z2,z3,z4,z87,z602]),(0,[z1,z125,z3,z221,z5,z6])],[(0,[z1,z145,z10,z4,z5,z6]),(0,[z1,z253,z10,z4,z5,z6]),(0,[z1,z2,z3,z134,z278,z6]),(0,[z1,z2,z3,z503,z12,z6]),(0,[z1,z160,z3,z4,z5,z28]),(0,[z1,z2,z3,z4,z1381,z6])],[(0,[z1,z253,z3,z4,z563,z6]),(0,[z1,z425,z38,z4,z5,z6]),(0,[z1,z2,z3,z1382,z5,z6]),(0,[z1,z2,z402,z18,z5,z6])],[(0,[z1,z390,z3,z4,z288,z6]),(0,[z1,z2,z3,z984,z18,z6]),(0,[z1,z2,z167,z4,z5,z28]),(0,[z1,z2,z109,z4,z11,z6]),(0,[z1,z1383,z3,z4,z5,z6])],[(0,[z575,z2,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z1384])],[(0,[z1,z2,z1352,z50,z5,z6]),(0,[z1,z1385,z2,z3,z4,z5]),(0,[z1,z2,z3,z775,z4,z6]),(0,[z1,z2,z3,z5,z900,z56])],[(0,[z1,z2,z3,z4,z5,z1386])]],
   [[(0,[z1,z2,z38,z220,z4,z6]),(0,[z1,z285,z3,z4,z5,z188]),(0,[z111,z81,z3,z4,z19,z6]),(0,[z78,z2,z3,z4,z914,z6]),(0,[z1,z90,z3,z61,z11,z6]),(0,[z1,z2,z3,z4,z1387,z6]),(0,[z1,z2,z84,z4,z570,z6])],[(0,[z1,z2,z10,z134,z27,z6]),(0,[z1,z2,z3,z4,z19,z41])],[(0,[z1,z2,z10,z4,z158,z6]),(0,[z96,z2,z10,z4,z5,z298]),(0,[z1,z55,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z1388]),(0,[z1,z3,z4,z5,z157,z6])],[(0,[z1,z2,z3,z4,z5,z571]),(0,[z416,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1389,z6]),(0,[z1,z390,z10,z4,z5,z6]),(0,[z1,z1390,z3,z4,z5,z6]),(0,[z1,z2,z3,z436,z5,z41])],[(0,[z1,z24,z3,z303,z5,z6]),(0,[z1,z2,z3,z4,z5,z1391])],[(0,[z1,z2,z3,z177,z4,z41])],[(0,[z1,z103,z2,z240,z5,z6]),(1,[z2,z3,z4,z5,z1040])],[(0,[z1,z2,z1392,z4,z5,z6]),(0,[z1,z2,z38,z4,z372,z6]),(0,[z2,z3,z769,z4,z5,z6])],[(0,[z1,z8,z3,z4,z587,z6])],[(0,[z1,z2,z3,z1393,z5,z6]),(0,[z1,z36,z73,z4,z5,z6]),(0,[z83,z2,z456,z4,z5,z41]),(0,[z1,z2,z3,z4,z1394,z6])],[(0,[z1,z2,z126,z4,z5,z619]),(0,[z1,z20,z3,z242,z4,z6]),(0,[z594,z24,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z133,z28]),(0,[z1,z80,z3,z50,z5,z6])],[(0,[z1,z2,z126,z4,z5,z335]),(0,[z1,z2,z192,z4,z5,z41]),(0,[z1,z2,z173,z4,z5,z28]),(0,[z1,z2,z3,z4,z5,z1395])],[(0,[z327,z2,z10,z4,z5,z6]),(0,[z405,z2,z3,z50,z5,z6])],[(0,[z1,z2,z430,z4,z5,z361]),(0,[z1,z13,z3,z4,z5,z28])],[(0,[z1,z20,z3,z4,z5,z41]),(0,[z1,z24,z3,z4,z5,z153]),(0,[z1,z44,z2,z3,z19,z56])],[(0,[z1,z2,z3,z653,z87,z6]),(0,[z1,z55,z3,z4,z5,z291]),(0,[z1,z2,z3,z4,z5,z1396])],[(0,[z1,z2,z3,z4,z1397,z6]),(0,[z1,z8,z3,z4,z5,z6]),(0,[z1,z487,z20,z4,z5,z6])],[(0,[z1,z2,z3,z131,z5,z28]),(0,[z1,z2,z3,z4,z11,z320]),(0,[z1,z2,z10,z18,z5,z6]),(0,[z64,z2,z3,z50,z5,z291])],[(0,[z1,z24,z274,z4,z5,z6]),(0,[z1,z35,z24,z3,z4,z16]),(0,[z1,z285,z345,z4,z5,z6]),(0,[z1,z59,z3,z4,z5,z60]),(0,[z1,z2,z3,z1398,z5,z6])],[(0,[z1,z2,z88,z18,z5,z6])],[(0,[z202,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z1399])],[(0,[z1,z2,z38,z4,z11,z41]),(0,[z1,z1400,z3,z4,z5,z6])],[(0,[z1,z52,z38,z4,z5,z6]),(0,[z1,z2,z3,z1401,z4,z6])],[(0,[z132,z24,z3,z380,z5,z6]),(0,[z1,z52,z3,z4,z5,z124]),(0,[z1,z2,z3,z4,z5,z1402]),(0,[z1,z1403,z3,z4,z5,z6])],[],[(0,[z1,z2,z1404,z4,z5,z6]),(0,[z1,z2,z84,z4,z268,z6]),(0,[z1,z3,z50,z717,z5,z6])],[(0,[z1,z39,z441,z4,z5,z6]),(0,[z1,z2,z196,z25,z5,z6]),(0,[z1,z2,z4,z48,z243,z6]),(0,[z1,z2,z3,z4,z727,z6])],[(1,[z752,z3,z4,z5,z6]),(0,[z1,z20,z3,z50,z19,z6]),(0,[z1,z20,z3,z18,z5,z28])],[(0,[z132,z24,z474,z4,z5,z6]),(0,[z1,z2,z3,z4,z1405,z6]),(0,[z1,z2,z4,z5,z297,z551])],[(0,[z1,z2,z230,z4,z5,z6]),(0,[z1,z2,z3,z4,z1406,z6]),(0,[z1,z2,z1407,z4,z5,z6]),(0,[z111,z2,z3,z4,z19,z41]),(0,[z78,z2,z109,z4,z11,z6]),(0,[z1,z2,z3,z5,z6,z1408])],[(0,[z1,z2,z3,z4,z5,z237]),(0,[z1,z55,z3,z4,z5,z188]),(0,[z1,z2,z3,z4,z5,z238]),(0,[z1,z296,z3,z464,z5,z6]),(0,[z1,z2,z3,z1409,z4,z6])]],
   [[(0,[z1,z3,z4,z1410,z5,z6]),(0,[z1,z24,z3,z134,z27,z6]),(0,[z1,z2,z3,z562,z278,z6]),(0,[z1,z2,z3,z4,z6,z725]),(0,[z1,z2,z3,z4,z5,z1411])],[(0,[z1,z2,z3,z4,z19,z267]),(0,[z64,z2,z3,z50,z5,z188]),(0,[z1,z2,z18,z5,z6,z821]),(0,[z1,z2,z4,z5,z6,z1412])],[(0,[z1,z2,z3,z18,z11,z41]),(0,[z512,z2,z3,z18,z5,z6]),(0,[z1,z39,z794,z4,z5,z6])],[(0,[z1,z2,z38,z4,z407,z6]),(0,[z86,z2,z38,z18,z5,z6]),(0,[z1,z90,z3,z61,z5,z41]),(0,[z212,z2,z3,z4,z5,z28])],[(0,[z1,z176,z3,z4,z861,z6]),(0,[z1,z2,z1413,z4,z5,z6])],[(0,[z1,z36,z148,z4,z5,z6])],[(0,[z1,z125,z3,z140,z5,z6]),(0,[z1,z145,z3,z488,z5,z6])],[(0,[z1,z20,z3,z4,z427,z6]),(0,[z1,z2,z3,z4,z87,z28]),(0,[z1,z2,z3,z161,z5,z414]),(0,[z1,z2,z3,z4,z5,z1414]),(0,[z1,z2,z3,z4,z6,z716])],[(0,[z1,z2,z3,z1415,z5,z6]),(0,[z2,z3,z4,z404,z11,z6]),(0,[z1,z1416,z2,z3,z4,z5]),(0,[z1,z2,z120,z4,z5,z23])],[(0,[z1,z176,z3,z4,z310,z6]),(0,[z1,z2,z3,z4,z133,z571]),(0,[z1,z2,z3,z50,z5,z41])],[(0,[z1,z2,z126,z4,z5,z6]),(0,[z2,z38,z10,z4,z5,z28]),(0,[z2,z3,z50,z5,z19,z41]),(0,[z1,z2,z3,z220,z50,z6]),(0,[z1,z2,z3,z32,z5,z159])],[(0,[z96,z2,z10,z4,z427,z6]),(0,[z1,z273,z2,z457,z5,z6]),(0,[z1,z129,z2,z4,z48,z6])],[(0,[z1,z2,z120,z4,z5,z434]),(0,[z1,z269,z2,z3,z4,z330]),(0,[z1,z44,z2,z3,z385,z56])],[(0,[z1,z20,z3,z380,z5,z6]),(0,[z1,z186,z154,z4,z5,z6]),(0,[z1,z24,z10,z50,z5,z6]),(0,[z1,z24,z410,z4,z5,z6])],[(0,[z1,z2,z3,z1417,z5,z6]),(0,[z1,z2,z38,z4,z5,z124]),(0,[z1,z296,z38,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z267]),(0,[z1,z68,z3,z4,z5,z277]),(0,[z1,z106,z593,z4,z5,z6]),(0,[z1,z2,z3,z4,z1418,z5]),(0,[z1,z2,z3,z1419,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1420]),(0,[z1,z2,z3,z131,z5,z571]),(0,[z1,z2,z454,z4,z19,z6]),(0,[z1,z1249,z2,z4,z5,z41])],[(0,[z1,z2,z1421,z4,z5,z6]),(0,[z1,z377,z3,z464,z5,z6])],[(0,[z1,z20,z474,z4,z5,z6]),(0,[z1,z55,z345,z4,z5,z6]),(0,[z1,z2,z481,z4,z11,z6]),(0,[z1,z2,z1422,z4,z5,z6]),(0,[z1,z2,z3,z4,z1423,z6])],[(0,[z1,z59,z3,z4,z5,z110]),(0,[z1,z2,z10,z4,z5,z298]),(0,[z2,z3,z4,z11,z914,z6]),(0,[z1,z2,z4,z259,z11,z6])],[(0,[z64,z2,z345,z50,z5,z6]),(0,[z1,z160,z3,z4,z5,z238]),(0,[z1,z90,z3,z340,z5,z6])],[(0,[z1,z2,z3,z601,z11,z6]),(0,[z96,z2,z10,z4,z372,z6])],[],[(0,[z1,z2,z38,z482,z5,z6])],[(0,[z1,z2,z3,z867,z4,z6]),(0,[z51,z2,z3,z18,z11,z6]),(0,[z1,z2,z3,z146,z5,z28]),(0,[z1,z2,z1424,z4,z5,z6])],[(0,[z1,z2,z360,z4,z22,z6]),(0,[z1,z264,z3,z221,z5,z6])],[(0,[z1,z285,z3,z4,z5,z6]),(0,[z1,z80,z3,z601,z5,z6]),(0,[z1,z1425,z3,z4,z5,z6]),(0,[z1,z3,z18,z271,z5,z6]),(0,[z1,z2,z3,z464,z19,z6]),(0,[z1,z173,z4,z5,z157,z6])],[(0,[z1,z2,z1426,z4,z5,z6]),(0,[z1,z2,z1427,z4,z5,z6])],[(0,[z1,z2,z281,z4,z5,z28])],[(0,[z1,z2,z3,z4,z11,z619]),(0,[z1,z210,z3,z4,z5,z69]),(0,[z1,z2,z3,z4,z5,z1428]),(0,[z1,z2,z4,z5,z6,z1429])],[(0,[z1,z2,z222,z4,z5,z6]),(0,[z1,z20,z454,z4,z5,z6]),(0,[z64,z24,z3,z50,z5,z6]),(0,[z1,z52,z192,z4,z5,z6])],[(0,[z1,z2,z3,z4,z11,z335]),(0,[z1,z425,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z1430,z6])]],
   [[(0,[z1,z1431,z3,z4,z5,z6]),(0,[z1,z377,z38,z4,z5,z6]),(0,[z1,z2,z38,z33,z100,z6])],[(0,[z1,z2,z3,z50,z427,z6]),(0,[z1,z2,z3,z4,z5,z1432]),(0,[z1,z2,z3,z4,z5,z1433])],[(0,[z1,z1434,z3,z4,z5,z6]),(0,[z1,z2,z252,z25,z5,z6]),(0,[z1,z1435,z3,z4,z5,z6]),(0,[z1,z2,z177,z4,z6,z76])],[(0,[z1,z2,z196,z329,z5,z6])],[(0,[z1,z2,z3,z1270,z4,z41])],[(0,[z1,z2,z3,z4,z1436,z6]),(0,[z1,z2,z3,z4,z563,z41]),(0,[z1,z2,z3,z18,z5,z1206]),(0,[z1,z2,z3,z45,z5,z238])],[(0,[z1,z371,z42,z4,z5,z6]),(0,[z1,z2,z1437,z4,z5,z6])],[(0,[z24,z20,z3,z4,z5,z41]),(0,[z1,z253,z3,z4,z5,z602]),(0,[z1,z125,z3,z40,z5,z6])],[(0,[z1,z20,z3,z464,z5,z6]),(0,[z1,z2,z430,z4,z5,z236]),(0,[z1,z2,z1438,z4,z5,z6])],[(0,[z1,z2,z3,z50,z5,z267]),(0,[z1,z2,z38,z4,z19,z6]),(0,[z1,z2,z38,z438,z5,z6])],[(0,[z1,z667,z3,z4,z11,z6]),(0,[z1,z273,z271,z217,z5,z6])],[(0,[z183,z20,z3,z206,z5,z6]),(0,[z1,z2,z3,z1439,z5,z6]),(0,[z1,z2,z3,z50,z372,z6]),(0,[z1,z2,z3,z4,z1440,z6]),(0,[z1,z2,z38,z436,z5,z6]),(0,[z78,z2,z3,z50,z5,z41]),(0,[z1,z1441,z3,z4,z5,z6]),(0,[z1,z36,z154,z4,z5,z41]),(0,[z1,z2,z3,z4,z1442,z6])],[(0,[z1,z2,z474,z50,z5,z6])],[(0,[z1,z2,z3,z1443,z5,z6]),(0,[z1,z20,z3,z4,z407,z6]),(0,[z1,z2,z38,z177,z4,z6]),(0,[z94,z2,z3,z4,z5,z28]),(0,[z1,z2,z3,z1444,z5,z6])],[],[(0,[z650,z2,z3,z50,z5,z6]),(0,[z2,z3,z4,z5,z28,z41]),(0,[z1,z2,z3,z1445,z5,z6])],[(0,[z1,z2,z3,z1446,z5,z6]),(0,[z1,z2,z1447,z4,z5,z6]),(0,[z1,z65,z2,z4,z5,z245])],[(0,[z1,z39,z593,z4,z5,z6]),(0,[z1,z2,z10,z18,z5,z28]),(0,[z1,z650,z2,z3,z4,z16])],[(0,[z1,z24,z3,z4,z5,z298]),(0,[z1,z2,z3,z45,z5,z153]),(0,[z1,z1448,z2,z3,z4,z5])],[(0,[z1,z2,z3,z206,z5,z28]),(0,[z666,z2,z10,z4,z5,z6])],[(0,[z1,z2,z3,z1449,z5,z6]),(0,[z1,z2,z481,z146,z5,z6])],[(0,[z1,z2,z3,z18,z19,z6]),(0,[z1,z2,z1352,z4,z5,z6]),(0,[z1,z2,z192,z4,z5,z124]),(0,[z526,z2,z3,z4,z11,z6])],[(0,[z1,z2,z3,z4,z5,z1450])],[(0,[z1,z20,z38,z4,z5,z6]),(0,[z1,z2,z1451,z4,z5,z6]),(0,[z1,z553,z3,z4,z5,z157])],[(0,[z1,z20,z3,z4,z5,z124]),(0,[z1,z315,z3,z4,z5,z277]),(0,[z1,z1452,z3,z4,z5,z6]),(0,[z1,z2,z3,z601,z5,z41]),(0,[z1,z2,z454,z50,z5,z6]),(0,[z1,z254,z402,z4,z5,z6]),(0,[z1,z1453,z3,z4,z5,z6]),(0,[z1,z44,z313,z2,z4,z5])],[(0,[z1,z55,z3,z4,z5,z6]),(0,[z1,z2,z345,z4,z5,z41])],[(0,[z2,z10,z18,z50,z5,z6]),(0,[z1,z150,z3,z4,z417,z6])],[(0,[z1,z210,z3,z4,z5,z108]),(0,[z1,z52,z3,z50,z5,z6]),(0,[z1,z145,z109,z4,z5,z6])],[(0,[z1,z2,z38,z4,z556,z6]),(0,[z1,z1454,z2,z4,z5,z6]),(0,[z1,z39,z179,z4,z19,z6]),(0,[z1,z2,z692,z4,z5,z23])],[(0,[z1,z2,z3,z4,z11,z6]),(0,[z202,z2,z38,z4,z5,z6]),(0,[z1,z3,z4,z11,z743,z6]),(0,[z1,z233,z3,z4,z175,z6])],[(0,[z132,z24,z3,z4,z19,z6]),(0,[z1,z24,z3,z242,z4,z6]),(0,[z1,z253,z3,z653,z5,z6]),(0,[z1,z174,z3,z4,z5,z41]),(0,[z1,z1455,z2,z3,z4,z5])],[(0,[z1,z2,z10,z220,z4,z6]),(0,[z1,z10,z4,z271,z5,z6]),(0,[z1,z2,z4,z5,z1223,z6])]],
   [[(0,[z1,z2,z3,z303,z5,z28]),(0,[z1,z1456,z3,z4,z5,z6])],[(0,[z1,z20,z3,z482,z5,z6]),(0,[z1,z2,z3,z4,z11,z102])],[(0,[z1,z81,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1457])],[],[(0,[z1,z24,z38,z4,z5,z28]),(0,[z1,z1353,z24,z4,z5,z6]),(0,[z1,z8,z3,z146,z5,z6]),(0,[z1,z2,z3,z4,z1458,z6])],[(0,[z20,z3,z4,z5,z114,z6]),(0,[z1,z169,z179,z4,z5,z6])],[(0,[z1,z2,z10,z4,z372,z6]),(0,[z1,z2,z3,z4,z1459,z6]),(0,[z111,z2,z38,z4,z19,z6]),(0,[z1,z2,z454,z4,z5,z291]),(0,[z1,z2,z3,z1060,z4,z6]),(0,[z1,z2,z3,z4,z258,z6])],[(0,[z183,z20,z274,z4,z5,z6]),(0,[z1,z2,z3,z50,z407,z6]),(0,[z1,z2,z3,z4,z1460,z6]),(0,[z1,z2,z3,z1461,z5,z6]),(0,[z1,z2,z3,z4,z1462,z6]),(0,[z420,z2,z3,z50,z5,z6])],[(0,[z1,z187,z2,z4,z5,z300]),(0,[z1,z2,z3,z18,z556,z6]),(0,[z1,z859,z2,z3,z4,z19]),(0,[z1,z2,z3,z358,z4,z6]),(0,[z1,z3,z4,z5,z6,z1463])],[(0,[z202,z2,z3,z18,z5,z6]),(0,[z633,z2,z3,z4,z11,z6])],[(0,[z1,z2,z38,z18,z11,z6]),(0,[z1,z1464,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1465]),(0,[z1,z90,z38,z61,z5,z6]),(0,[z1,z273,z2,z584,z5,z6]),(0,[z1,z1466,z2,z4,z5,z6])],[(0,[z132,z752,z3,z4,z5,z6]),(0,[z1,z59,z3,z4,z5,z225])],[(0,[z1,z2,z3,z18,z314,z6]),(0,[z1,z24,z402,z4,z5,z6]),(0,[z1,z129,z2,z4,z231,z6]),(0,[z1,z2,z3,z4,z628,z41])],[(0,[z1,z36,z72,z4,z5,z6]),(0,[z1,z2,z3,z806,z5,z6])],[(0,[z1,z2,z274,z4,z5,z28]),(0,[z1,z52,z3,z4,z288,z6]),(0,[z1,z2,z3,z18,z5,z551])],[(0,[z1,z24,z3,z50,z19,z6]),(0,[z1,z24,z3,z18,z5,z28]),(0,[z1,z2,z3,z601,z427,z6]),(0,[z1,z2,z3,z4,z5,z1467])],[(0,[z1,z2,z38,z50,z5,z6])],[(0,[z1,z35,z20,z3,z4,z16]),(0,[z666,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z102]),(0,[z1,z296,z3,z50,z5,z6]),(0,[z1,z2,z3,z50,z5,z124]),(0,[z111,z2,z3,z18,z19,z6]),(0,[z1,z160,z3,z4,z11,z6]),(0,[z1,z2,z3,z503,z292,z6]),(0,[z1,z150,z3,z4,z175,z6])],[(0,[z1,z2,z109,z18,z5,z6]),(0,[z2,z3,z340,z18,z5,z6]),(0,[z276,z2,z3,z4,z11,z6]),(0,[z1,z2,z25,z5,z6,z511])],[(0,[z1,z2,z167,z4,z11,z6]),(0,[z1,z2,z456,z4,z19,z6]),(0,[z1,z665,z187,z2,z4,z5])],[(0,[z1,z2,z10,z4,z11,z41]),(0,[z1,z253,z3,z4,z5,z28]),(0,[z1,z2,z454,z4,z5,z188]),(0,[z1,z145,z3,z4,z5,z28])],[(0,[z1,z2,z3,z1468,z5,z6]),(0,[z1,z2,z3,z574,z5,z298]),(0,[z1,z2,z3,z885,z4,z6])],[(0,[z1,z20,z3,z177,z4,z6]),(0,[z96,z2,z10,z4,z19,z6]),(0,[z1,z2,z3,z4,z587,z41])],[(0,[z1,z1469,z3,z4,z5,z6]),(0,[z2,z3,z376,z4,z5,z41]),(0,[z1,z1470,z3,z4,z5,z6])],[(0,[z1,z2,z3,z134,z12,z6])],[(0,[z1,z2,z402,z488,z5,z6])],[(0,[z1,z24,z3,z4,z427,z6]),(0,[z1,z2,z1471,z4,z5,z6]),(0,[z1,z2,z360,z4,z268,z6])],[(0,[z1,z2,z3,z18,z6,z878]),(0,[z1,z2,z3,z134,z27,z28]),(0,[z1,z2,z3,z534,z27,z6])],[(0,[z1,z2,z3,z1472,z5,z6]),(0,[z1,z2,z3,z448,z19,z6]),(0,[z1,z2,z38,z32,z5,z79]),(0,[z1,z322,z2,z432,z5,z6])],[(0,[z1,z20,z192,z4,z5,z6]),(0,[z1,z24,z3,z220,z4,z6]),(0,[z1,z390,z3,z4,z5,z28])],[(0,[z1,z2,z3,z131,z133,z6]),(0,[z1,z2,z38,z4,z5,z291]),(0,[z78,z2,z3,z4,z11,z6]),(0,[z7,z2,z3,z4,z5,z1040]),(0,[z1,z2,z1473,z4,z5,z6])]],
   [[(0,[z83,z2,z3,z4,z19,z41])],[(0,[z1,z24,z3,z380,z5,z6]),(0,[z1,z1474,z2,z4,z5,z6]),(0,[z2,z3,z50,z19,z6,z41]),(0,[z1,z1245,z3,z18,z5,z6]),(0,[z1,z313,z2,z4,z19,z6])],[(0,[z1,z2,z3,z528,z5,z41]),(0,[z1,z2,z220,z4,z259,z6]),(0,[z1,z2,z1475,z4,z5,z6]),(0,[z1,z2,z4,z5,z297,z6]),(0,[z1,z187,z2,z4,z5,z813])],[(0,[z2,z3,z4,z5,z625,z28]),(0,[z1,z2,z25,z5,z525,z6])],[(0,[z1,z377,z3,z50,z5,z6]),(0,[z1,z39,z179,z50,z5,z6]),(0,[z690,z2,z3,z50,z5,z6]),(0,[z1,z2,z173,z4,z11,z6])],[(0,[z96,z20,z10,z4,z5,z6]),(0,[z1,z24,z3,z4,z372,z6]),(0,[z1,z646,z3,z4,z5,z41]),(0,[z264,z2,z3,z18,z5,z6]),(0,[z1,z2,z1476,z4,z5,z6]),(0,[z1,z2,z4,z5,z28,z76]),(0,[z1,z2,z3,z4,z5,z1477]),(0,[z1,z2,z3,z4,z5,z1478]),(0,[z1,z3,z4,z5,z6,z1479]),(0,[z1,z3,z1480,z4,z5,z6]),(0,[z1,z313,z2,z177,z4,z6])],[(0,[z1,z24,z474,z4,z5,z6]),(0,[z132,z24,z3,z50,z5,z6]),(0,[z1,z1481,z3,z4,z5,z6]),(0,[z1,z859,z2,z3,z50,z5]),(0,[z1,z2,z3,z4,z288,z124]),(0,[z1,z13,z3,z4,z11,z6])],[(0,[z1,z2,z3,z208,z5,z79]),(0,[z1482,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z394,z5]),(0,[z1,z2,z3,z4,z1483,z6])],[(0,[z1,z81,z3,z45,z5,z6]),(0,[z1,z2,z1484,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1485,z6]),(0,[z1,z2,z3,z18,z5,z320]),(0,[z1,z68,z3,z4,z11,z69]),(0,[z1,z2,z3,z1486,z4,z6])],[(0,[z1,z2,z3,z131,z11,z6])],[(0,[z1,z3,z4,z5,z6,z1487]),(0,[z617,z2,z10,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1488,z6])],[(0,[z1,z190,z3,z221,z5,z6]),(0,[z1,z2,z3,z1489,z4,z6]),(0,[z1,z273,z2,z618,z5,z6])],[(0,[z1,z2,z38,z4,z5,z188]),(0,[z1,z44,z2,z3,z5,z56])],[(0,[z2,z10,z4,z5,z368,z6]),(0,[z1,z2,z3,z4,z5,z1490]),(0,[z2,z3,z18,z11,z19,z6]),(0,[z1,z2,z18,z259,z5,z6])],[(0,[z7,z2,z10,z50,z5,z6]),(0,[z1,z2,z3,z178,z278,z6])],[(0,[z1,z2,z3,z1491,z5,z6]),(0,[z1,z2,z10,z488,z5,z6]),(0,[z1,z2,z3,z1492,z5,z6]),(0,[z1,z2,z1493,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1494])],[(0,[z1,z3,z18,z5,z6,z185]),(0,[z1,z2,z3,z4,z5,z1495])],[(0,[z1,z1496,z3,z4,z5,z6]),(0,[z1,z2,z286,z25,z5,z6]),(0,[z2,z3,z50,z5,z284,z6]),(0,[z1,z586,z2,z3,z4,z16]),(0,[z575,z2,z3,z4,z5,z28]),(0,[z1,z1497,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1498]),(0,[z1,z20,z3,z18,z11,z6]),(0,[z2,z3,z862,z50,z5,z6]),(0,[z680,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z394,z11]),(0,[z1,z2,z1499,z4,z5,z6]),(0,[z1,z44,z667,z3,z4,z5]),(0,[z1,z2,z3,z4,z684,z70])],[(0,[z1,z544,z3,z164,z5,z6]),(0,[z58,z24,z3,z4,z5,z6]),(0,[z1,z160,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z5,z1500]),(0,[z1,z2,z1501,z4,z5,z6]),(0,[z1,z2,z3,z235,z4,z6])],[(0,[z1,z2,z3,z5,z6,z1502])],[(0,[z1,z2,z230,z4,z5,z237])],[(0,[z1,z2,z126,z206,z5,z6]),(0,[z1,z55,z3,z4,z5,z28]),(0,[z1,z2,z192,z50,z5,z6]),(0,[z1,z150,z3,z4,z348,z6]),(0,[z1,z2,z3,z4,z5,z1503]),(0,[z1,z4,z5,z6,z76,z185])],[(0,[z1,z3,z50,z271,z5,z6]),(0,[z1,z2,z3,z4,z1504,z6]),(0,[z1,z2,z3,z4,z1505,z6])],[(0,[z64,z2,z3,z50,z5,z28]),(0,[z1,z2,z3,z4,z74,z248]),(0,[z1,z2,z1506,z4,z5,z6])],[(0,[z1,z20,z3,z50,z5,z6]),(0,[z1,z2,z1507,z4,z5,z6]),(0,[z1,z176,z3,z4,z467,z6])],[(0,[z1,z35,z2,z10,z4,z16]),(0,[z1,z2,z3,z1005,z4,z6])],[(0,[z1,z646,z3,z4,z427,z6]),(0,[z1,z21,z2,z4,z197,z6]),(0,[z1,z2,z3,z4,z1508,z5])],[],[(0,[z96,z2,z10,z50,z5,z6]),(0,[z1,z377,z10,z4,z5,z6]),(0,[z1,z2,z10,z33,z100,z6]),(0,[z1,z2,z3,z436,z5,z508])]],
   [[(0,[z1,z2,z3,z4,z5,z267]),(0,[z1,z2,z1509,z4,z5,z6]),(0,[z1,z2,z38,z601,z5,z6]),(0,[z1,z1115,z3,z4,z5,z28]),(0,[z1,z794,z36,z4,z5,z6])],[(0,[z1,z24,z3,z4,z407,z6]),(0,[z1,z80,z3,z4,z5,z28]),(0,[z1,z487,z2,z220,z4,z6]),(0,[z1,z553,z2,z3,z33,z4])],[(0,[z2,z38,z10,z4,z11,z6]),(0,[z1,z331,z3,z4,z5,z207]),(0,[z1,z273,z2,z235,z217,z6])],[(0,[z1,z1510,z3,z4,z5,z6])],[(0,[z1,z2,z1511,z4,z5,z6])],[(0,[z1,z2,z126,z303,z5,z6]),(0,[z1,z745,z20,z3,z4,z5]),(0,[z1,z2,z1512,z4,z5,z6]),(0,[z1,z1513,z3,z4,z5,z6]),(0,[z64,z2,z3,z50,z408,z6]),(0,[z265,z2,z3,z4,z11,z6]),(0,[z1,z269,z2,z3,z4,z16]),(0,[z1,z2,z3,z33,z156,z6])],[(0,[z1,z2,z3,z4,z1514,z6]),(0,[z1,z174,z38,z4,z5,z6]),(0,[z1,z2,z3,z45,z5,z41]),(0,[z1,z2,z3,z464,z628,z6])],[(0,[z1,z2,z1515,z4,z5,z6]),(0,[z1,z2,z3,z358,z18,z6]),(0,[z1,z2,z3,z358,z4,z28]),(0,[z1,z2,z3,z1516,z5,z6])],[(0,[z1,z2,z38,z4,z5,z619]),(0,[z1,z176,z3,z4,z552,z6]),(0,[z1,z2,z10,z574,z5,z6]),(0,[z1,z2,z10,z4,z19,z6]),(0,[z1,z2,z10,z438,z5,z6])],[(0,[z2,z10,z4,z404,z5,z6]),(0,[z172,z2,z10,z4,z5,z6]),(0,[z1,z1517,z3,z4,z5,z6]),(0,[z1,z313,z2,z50,z5,z6])],[(0,[z1,z2,z38,z4,z5,z335]),(0,[z1,z2,z10,z436,z5,z6]),(0,[z111,z2,z3,z50,z19,z6]),(0,[z1,z2,z88,z4,z19,z6]),(0,[z1,z2,z88,z438,z5,z6]),(0,[z1,z3,z4,z5,z756,z60])],[(0,[z1,z20,z3,z4,z5,z508])],[(0,[z1,z558,z3,z221,z5,z6]),(0,[z1,z24,z3,z4,z5,z124]),(0,[z1,z2,z192,z4,z288,z6]),(0,[z1,z2,z3,z1518,z5,z6])],[(0,[z169,z2,z10,z4,z5,z6]),(0,[z1,z2,z345,z18,z5,z6]),(0,[z1,z2,z3,z4,z1519,z6])],[(0,[z2,z38,z18,z50,z5,z6]),(0,[z1,z363,z3,z4,z5,z6])],[(0,[z1,z20,z3,z4,z288,z6]),(0,[z1,z2,z454,z4,z5,z6])],[(0,[z1,z2,z3,z146,z11,z6]),(0,[z1,z43,z3,z4,z467,z6]),(0,[z1,z1520,z2,z3,z4,z5])],[(0,[z2,z98,z3,z50,z5,z6])],[(0,[z1,z20,z3,z4,z19,z28]),(0,[z1,z2,z3,z4,z5,z1521]),(0,[z1,z2,z38,z4,z92,z70]),(0,[z1,z254,z3,z4,z19,z6]),(0,[z1,z2,z84,z4,z22,z41]),(0,[z166,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z5,z6,z1522])],[(0,[z1,z38,z4,z271,z5,z6]),(0,[z130,z2,z3,z4,z19,z6])],[(0,[z1,z2,z3,z18,z5,z619]),(0,[z2,z10,z4,z11,z19,z6]),(0,[z1,z254,z3,z436,z5,z6]),(0,[z1,z2,z281,z4,z11,z6]),(0,[z1,z1523,z3,z4,z5,z6])],[(0,[z1,z24,z3,z482,z5,z6]),(0,[z1,z2,z38,z4,z628,z6]),(0,[z1,z667,z38,z4,z5,z6]),(0,[z1,z44,z2,z3,z496,z5])],[(0,[z1,z2,z3,z18,z5,z335]),(0,[z1,z20,z10,z4,z5,z6]),(0,[z1,z3,z4,z1524,z5,z6]),(0,[z1,z2,z3,z1270,z50,z6])],[(0,[z183,z20,z3,z4,z5,z41]),(0,[z1,z20,z3,z4,z563,z6]),(0,[z1,z10,z4,z5,z6,z185]),(0,[z1,z1525,z3,z4,z5,z6]),(0,[z1,z118,z3,z4,z5,z277]),(0,[z1,z2,z1526,z4,z5,z6])],[(0,[z1,z20,z3,z4,z5,z188]),(0,[z512,z2,z3,z4,z19,z6])],[(0,[z1,z106,z179,z4,z5,z6]),(0,[z86,z2,z38,z4,z19,z6]),(0,[z1,z2,z1527,z4,z5,z6])],[(0,[z1,z190,z3,z140,z5,z6]),(0,[z1,z2,z3,z242,z18,z6]),(0,[z1,z2,z4,z19,z1161,z6]),(0,[z1,z2,z3,z242,z4,z28])],[(0,[z1,z2,z10,z4,z556,z6]),(0,[z1,z429,z2,z3,z4,z5])],[(0,[z1,z2,z1528,z4,z5,z6]),(1,[z20,z3,z50,z5,z41]),(0,[z1,z1249,z2,z50,z5,z6]),(0,[z1,z1529,z3,z4,z5,z6])],[(0,[z20,z3,z18,z50,z5,z6]),(0,[z78,z20,z3,z50,z5,z6]),(0,[z2,z20,z3,z50,z19,z6]),(0,[z1,z43,z3,z4,z552,z6])],[(0,[z690,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z18,z92,z70]),(0,[z1,z2,z3,z4,z11,z82])],[(0,[z1,z2,z38,z4,z587,z6]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z703,z2,z3,z4,z5,z41])]],
   [[(0,[z1,z2,z10,z4,z314,z6]),(0,[z1,z2,z3,z1530,z5,z6]),(0,[z1,z253,z3,z4,z5,z102]),(0,[z354,z2,z3,z4,z5,z41]),(0,[z1,z2,z3,z4,z1531,z5]),(0,[z1,z422,z2,z3,z5,z56])],[(0,[z1,z2,z3,z18,z628,z6]),(0,[z1,z667,z3,z18,z5,z6]),(0,[z1,z2,z3,z4,z5,z1532]),(0,[z1,z273,z2,z217,z5,z6])],[(0,[z1,z2,z10,z4,z5,z551]),(0,[z1,z2,z3,z4,z5,z1533]),(0,[z1,z2,z3,z1534,z5,z6]),(0,[z1,z3,z4,z1535,z5,z6])],[(0,[z1,z24,z10,z4,z5,z28]),(0,[z1,z2,z3,z50,z5,z291]),(0,[z1,z176,z3,z411,z4,z6])],[(0,[z1,z2,z3,z4,z158,z6])],[(0,[z1,z2,z3,z4,z1536,z6]),(0,[z1,z1537,z3,z4,z5,z6]),(0,[z111,z2,z10,z4,z19,z6]),(0,[z1,z2,z3,z50,z5,z508]),(0,[z1,z2,z3,z4,z1538,z6])],[],[(0,[z1,z24,z3,z4,z19,z6]),(0,[z7,z2,z38,z4,z5,z28]),(0,[z2,z3,z50,z5,z364,z6]),(0,[z111,z2,z88,z4,z19,z6]),(0,[z1,z125,z3,z220,z221,z6])],[(0,[z1,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z280,z399,z6])],[(0,[z1,z24,z3,z436,z5,z6]),(0,[z1,z2,z10,z18,z11,z6]),(0,[z1,z2,z3,z50,z288,z6]),(0,[z1,z2,z3,z4,z11,z1049]),(0,[z1,z2,z3,z482,z587,z6])],[(0,[z1,z90,z10,z61,z5,z6]),(0,[z1,z2,z3,z1539,z5,z6])],[(0,[z1,z2,z3,z206,z11,z6]),(0,[z1,z2,z1540,z4,z5,z6]),(0,[z1,z24,z3,z177,z4,z6]),(0,[z1,z2,z3,z280,z100,z6]),(0,[z1,z296,z3,z528,z5,z6]),(0,[z1,z2,z84,z4,z727,z6]),(0,[z1,z2,z3,z4,z1541,z6])],[(0,[z641,z20,z3,z4,z5,z6]),(0,[z1,z2,z3,z50,z19,z28]),(0,[z2,z3,z376,z18,z5,z6]),(0,[z1,z1542,z3,z4,z5,z6])],[(0,[z1,z646,z38,z4,z5,z6]),(0,[z1,z44,z2,z3,z177,z4]),(0,[z1,z2,z3,z1543,z5,z6])],[(0,[z96,z2,z10,z601,z5,z6]),(0,[z1,z2,z3,z1544,z5,z6])],[(0,[z1,z44,z2,z5,z76,z56])],[(0,[z1,z2,z3,z4,z5,z1545])],[(0,[z2,z10,z4,z5,z6,z366]),(0,[z1,z2,z3,z50,z563,z6]),(0,[z1,z1546,z3,z4,z5,z6]),(0,[z7,z2,z3,z482,z5,z28]),(0,[z1,z2,z3,z4,z5,z1547])],[(0,[z1,z24,z192,z4,z5,z6]),(0,[z1,z2,z3,z50,z5,z188]),(0,[z1,z1548,z3,z4,z5,z6])],[(0,[z24,z20,z3,z50,z5,z6]),(0,[z1,z2,z3,z4,z5,z1549]),(0,[z1,z35,z2,z3,z50,z16]),(0,[z1,z125,z3,z221,z5,z41]),(0,[z1,z2,z4,z5,z6,z813])],[(0,[z1,z2,z3,z18,z5,z6]),(0,[z633,z2,z38,z4,z5,z6]),(0,[z1,z2,z3,z488,z19,z6])],[(0,[z1,z752,z3,z4,z5,z6]),(0,[z1,z425,z3,z4,z5,z28]),(0,[z1,z2,z235,z25,z4,z6]),(0,[z1,z2,z1550,z4,z5,z6])],[(0,[z2,z10,z4,z5,z375,z6]),(0,[z1,z2,z3,z4,z11,z237]),(0,[z1,z2,z281,z146,z5,z6]),(0,[z1,z2,z3,z4,z5,z1551])],[(0,[z1,z2,z1552,z4,z5,z6]),(0,[z1,z2,z3,z4,z427,z28]),(0,[z1,z2,z3,z18,z401,z6]),(0,[z1,z36,z154,z50,z5,z6]),(0,[z1,z2,z1553,z4,z5,z6])],[(0,[z1,z2,z3,z303,z11,z6]),(0,[z2,z3,z4,z5,z914,z6])],[(0,[z1,z150,z3,z4,z324,z6])],[(0,[z1,z254,z3,z50,z5,z6]),(0,[z1,z1151,z2,z3,z4,z5])],[(0,[z1,z81,z3,z4,z5,z238])],[(0,[z1,z24,z38,z4,z11,z6]),(0,[z1,z1554,z3,z4,z5,z6]),(0,[z1,z2,z10,z32,z5,z79]),(0,[z1,z3,z4,z5,z157,z41]),(0,[z1,z1555,z3,z4,z5,z6])],[(0,[z132,z24,z3,z4,z5,z6]),(0,[z1,z2,z3,z380,z5,z28]),(0,[z1,z2,z3,z4,z372,z320]),(0,[z1,z160,z38,z4,z5,z6]),(0,[z1,z377,z3,z528,z5,z6]),(0,[z1,z2,z3,z1556,z4,z6])],[(0,[z1,z2,z10,z4,z5,z291])],[(0,[z1,z3,z50,z5,z6,z1295]),(0,[z1,z3,z4,z5,z69,z337]),(0,[z1,z553,z2,z3,z134,z4]),(0,[z1,z1557,z3,z4,z5,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 16 512 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 32 1024 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 453) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 453).take 451) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 904).take 455) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1359).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb4 : chunkB SB 1 ((bkA.flatten.flatten.drop 1819).take 103) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1922)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [453, 451, 455, 460, 103] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_cons pb4 (windowsG_nil pbend)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 159).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 159).take 156).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 315).take 155).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 470).take 156).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 626).take 158).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc5 : chunkOK 5 ((bkB.flatten.drop 784).take 149).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc6 : chunkOK 5 ((bkB.flatten.drop 933).take 91).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 1024)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [159, 156, 155, 156, 158, 149, 91] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_cons pc5 (windowsF_cons pc6 (windowsF_nil pcend)))))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 16) (nb1 := 512) (g2 := 32) (nb2 := 1024) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_39129

theorem PEqualNP.Outside.L_meta_39129 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39129.solve