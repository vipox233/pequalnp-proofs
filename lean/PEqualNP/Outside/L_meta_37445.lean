import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37445

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
  Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0048310b8c2e31bc#64 ++ 0x2bd8733f9cfe73fc#64 : BitVec 128),
   (0x400b9458a1628455#64 ++ 0xffef9cd8e3638c7f#64 : BitVec 128),
   (0x82300aa056815a8a#64 ++ 0xfef01fe0ff83ff8f#64 : BitVec 128),
   (0x04b5c0f503d40f60#64 ++ 0x0fffe0ff03fc0ff0#64 : BitVec 128),
   (0x093eff0003fbe000#64 ++ 0x0f3fff0003fff000#64 : BitVec 128),
   (0x11bf7ffef8000000#64 ++ 0x0dbffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [13, 1]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0048310b8c2e31bc 0x2bd8733f9cfe73fc

def z1 : W := mkw 0x0485c05501540560 0x010fe01f007c0070

def z2 : W := mkw 0x093eff0003fbe000 0x0f3fff0003fff000

def z3 : W := mkw 0x11bf7ffef8000000 0x0dbffffffc000000

def z4 : W := mkw 0x15bffffffbd40f60 0x0ffffffffffc0ff0

def z5 : W := mkw 0x400b9458a1628455 0xffef9cd8e3638c7f

def z6 : W := mkw 0x82300aa056815a8a 0xfef01fe0ff83ff8f

def z7 : W := mkw 0x0001805001400440 0x0fef80d803600c70

def z8 : W := mkw 0x04b5c0f503d40f60 0x0fffe0ff03fc0ff0

def z9 : W := mkw 0x400a1408a0228015 0xf0001c00e003800f

def z10 : W := mkw 0x0000000002814000 0x020000000383f000

def z11 : W := mkw 0x820000a054001a8a 0xfee01ce0ff038f8f

def z12 : W := mkw 0x0000000000000000 0xfee01cc0e3038c0f

def z13 : W := mkw 0xc23b9ef8f7e3dedf 0xffff9ff8ffe3ffff

def z14 : W := mkw 0x820000a054001a8a 0xfad013e0fc827f8f

def z15 : W := mkw 0x404b9459a56eb5fd 0xffef9cd8e3ffffff

def z16 : W := mkw 0x090ef500017aa000 0x0b1ff30000fe7000

def z17 : W := mkw 0x82300aa052814a02 0xd4200cc063018c03

def z18 : W := mkw 0x013e7f0a88000000 0x0dbfff3f9c000000

def z19 : W := mkw 0x0840800107fff1bc 0x2240000003fff3fc

def z20 : W := mkw 0x0936ce0003fbe000 0x06278c0003fff000

def z21 : W := mkw 0x400b9458a1408441 0xddaf9cd8e3018c03

def z22 : W := mkw 0x00b540f400000000 0x0dbfe0ff00000000

def z23 : W := mkw 0x0400800103d40f60 0x0240000003fc0ff0

def z24 : W := mkw 0x00300aa052814000 0x0eb01fe0ff83f000

def z25 : W := mkw 0x09346b0002996000 0x00106300009c7000

def z26 : W := mkw 0x108b14fef8000000 0x0daf9cfffc000000

def z27 : W := mkw 0x0048310b8c2e31bc 0x2348601f00fe73fc

def z28 : W := mkw 0x930a3f0afc01508a 0xf0001f00fc03f00f

def z29 : W := mkw 0x400b9458a1628455 0x010f801800600070

def z30 : W := mkw 0xc20a1e08f423d09f 0xf0001f00fc03f00f

def z31 : W := mkw 0x11b74efef8000000 0x04a78cfffc000000

def z32 : W := mkw 0x093eff0a8bfbe000 0x0fbfff3f9ffff000

def z33 : W := mkw 0x4041005bac0415fd 0xf0c000fffc000fff

def z34 : W := mkw 0x08000000002be000 0x000000000003f000

def z35 : W := mkw 0x093eff0103ffe120 0x0fffff3f03fff3f0

def z36 : W := mkw 0x0048100b8c2611bc 0x2bc8103f9c6203fc

def z37 : W := mkw 0x00bd71fe88000000 0x0dbff3ff9c000000

def z38 : W := mkw 0x090abf0003fbe000 0x02001f0003fff000

def z39 : W := mkw 0x40bfd4fca1628455 0xfffffcffe3638c7f

def z40 : W := mkw 0x86308aa157d55fea 0xfef01fe0ffffffff

def z41 : W := mkw 0x04b440a502940b20 0x00106027009c0380

def z42 : W := mkw 0x00300a0002814000 0x0e301f000383f000

def z43 : W := mkw 0x8b3effa057fbfa8a 0xffffffe0ffffff8f

def z44 : W := mkw 0x8b0a3f00542bf08a 0xf0001f00fc03f00f

def z45 : W := mkw 0x090ef500017aa000 0x010fe000007c0000

def z46 : W := mkw 0x820000a054001a8a 0xf0c000e0fc000f8f

def z47 : W := mkw 0x0048310b8c0c31a8 0x0998733f9c9c7380

def z48 : W := mkw 0x108100fef8000000 0x008000fffc000000

def z49 : W := mkw 0x4000800001628455 0xf240000003638c7f

def z50 : W := mkw 0x19bffffef97aa000 0x0dbffffffc7c0000

def z51 : W := mkw 0x11b46ba658000000 0x001063271c000000

def z52 : W := mkw 0x82300aa056815a8a 0x2ad013209c82738c

def z53 : W := mkw 0x0800800003fbe000 0x0200000003fff000

def z54 : W := mkw 0x00481009842e31bc 0x2bc8101880fe73fc

def z55 : W := mkw 0x10c100fffc0411bc 0x20c000fffc0003fc

def z56 : W := mkw 0x404bb55bad6eb5fd 0xffffffffffffffff

def z57 : W := mkw 0x44b7c4f523d48f61 0xdfffecff63fd8ff3

def z58 : W := mkw 0x868100f554041fea 0xf0c000fffc000fff

def z59 : W := mkw 0x0dbff5f503feaf60 0x0fffe0ff03fc0ff0

def z60 : W := mkw 0x0000000000000000 0x0bc8001800600070

def z61 : W := mkw 0x003cf10003fa2000 0x0f3ff30003fe7000

def z62 : W := mkw 0x0008100880220014 0x2bc810188062007c

def z63 : W := mkw 0x404bb55ba96ea575 0x010fe01f007c0070

def z64 : W := mkw 0x093fff5003fbe440 0x0fffffd803fffc70

def z65 : W := mkw 0x833e7fa056815a8a 0xffffffe0ff83ff8f

def z66 : W := mkw 0x11b56bfef8000000 0x009063fffc000000

def z67 : W := mkw 0x4048b10b8d6eb5fd 0xfbd8733f9fffffff

def z68 : W := mkw 0x04b5c0f503d40f60 0xfffffcffe3ff8fff

def z69 : W := mkw 0x0000000000000000 0x0998603f00000000

def z70 : W := mkw 0x0000000100040120 0x0bd8603f00fc03f0

def z71 : W := mkw 0x04fdf1ff8ffe3ffc 0x2ffff3ff9ffe7ffc

def z72 : W := mkw 0x19bffffefbfbe000 0x0fbffffffffff000

def z73 : W := mkw 0x00300aa050000000 0x0cb01fe0fc000000

def z74 : W := mkw 0x093effa053fbe000 0x0fbfffe0fffff000

def z75 : W := mkw 0x11bf7ffef8220014 0x2ffffffffc62007c

def z76 : W := mkw 0x048100f500040f60 0x00c000ff00000ff0

def z77 : W := mkw 0x00000001040411a8 0x2bd8733f9cfe73fc

def z78 : W := mkw 0x86b5caf557d55fea 0xffffffffffffffff

def z79 : W := mkw 0x190a3f0af82be000 0x00001f00fc03f000

def z80 : W := mkw 0x82700aa156af7bbe 0xfef01fe0ffffffff

def z81 : W := mkw 0x0034ca0003d14000 0x0f3fff0003fff000

def z82 : W := mkw 0x14b5c0fffbd40f60 0x0fffe0fffffc0ff0

def z83 : W := mkw 0x00083100002a2000 0x0b18730000fe7000

def z84 : W := mkw 0x0936ce0003d1c000 0x0e379f000383f000

def z85 : W := mkw 0x003000a002800a00 0x0010002000800380

def z86 : W := mkw 0x51bffffef9628455 0xffffffffff638c7f

def z87 : W := mkw 0x048100f500040f60 0x0bd860ff00fc0ff0

def z88 : W := mkw 0x82300aa056815a8a 0xd4300fe07f81ff83

def z89 : W := mkw 0x04b5c0f503d40f60 0x052fe0df037c0c70

def z90 : W := mkw 0x0008310a88220014 0x2bd8733f9c62007c

def z91 : W := mkw 0x118f755ea8000000 0x010fe01f00000000

def z92 : W := mkw 0x0040000b8c0411bc 0x20c0003f9c0003fc

def z93 : W := mkw 0x0004c00001500000 0x010fe000007c0000

def z94 : W := mkw 0x0dbffff503ffef60 0x0fffffff03fffff0

def z95 : W := mkw 0x8a00800007fbfa8a 0xf240000003ffff8f

def z96 : W := mkw 0x0485c05501540560 0x0bdfe03f00fc03f0

def z97 : W := mkw 0x10b540fef8000000 0x0dbfe0fffc000000

def z98 : W := mkw 0x0db5ebf503dd6f60 0x0fffe3ff03fc7ff0

def z99 : W := mkw 0x11bf7ffef82a2000 0x0fbffffffcfe7000

def z100 : W := mkw 0x00b440a400000000 0x0010602700000000

def z101 : W := mkw 0x04f5c0f507fe3ffc 0x2fffe0ff03fe7ffc

def z102 : W := mkw 0x4008900881628455 0xfbc8101883638c7f

def z103 : W := mkw 0x110a3f0af8000000 0x00001f00fc000000

def z104 : W := mkw 0x8b346ba056997a8a 0xfef07fe0ff9fff8f

def z105 : W := mkw 0x11b74ef470000000 0x04278cc060000000

def z106 : W := mkw 0x0048310b882e2134 0x0108601f007c0070

def z107 : W := mkw 0x9bbffffefffbfa8a 0xffffffffffffff8f

def z108 : W := mkw 0x40010058a0000455 0xf0c000d8e0000c7f

def z109 : W := mkw 0x51bf7ffef8000455 0xfdfffffffc000c7f

def z110 : W := mkw 0x04b5c0f503d40f60 0x011fe03f00fc03f0

def z111 : W := mkw 0x51fffffffd6eb5fd 0xffffffffffffffff

def z112 : W := mkw 0x0934eb0003d96000 0x0f3fe30003fc7000

def z113 : W := mkw 0x0485c0f501540f60 0x01cfe0ff007c0ff0

def z114 : W := mkw 0x403b9e58a3e3c455 0xffff9fd8e3e3fc7f

def z115 : W := mkw 0x518ff55ea9628455 0x010fe01f00600070

def z116 : W := mkw 0x013e7f0000000000 0x0d3fff0000000000

def z117 : W := mkw 0x093ede0003f3c000 0x0f2f9c0003638000

def z118 : W := mkw 0x113e7f0af8000000 0x0d3fff00fc000000

def z119 : W := mkw 0x11be7fa658000000 0x0d3fff271c000000

def z120 : W := mkw 0x493fff5023fbe441 0xdf3fffc063fffc03

def z121 : W := mkw 0x0440800107fe3ffc 0x2240000003fe7ffc

def z122 : W := mkw 0x003000a002800a00 0x0ef000e003800f80

def z123 : W := mkw 0x000a940001628000 0x010f800000600000

def z124 : W := mkw 0x86b5c0f557d41fea 0xffffe0fffffc0fff

def z125 : W := mkw 0x0040000b88040134 0x0000001f00000070

def z126 : W := mkw 0x0048310a8c2a309c 0x200013009c02700c

def z127 : W := mkw 0x04b5c0f403d00e40 0x042780c003000c00

def z128 : W := mkw 0x86b5caf553d54f62 0xdfffecff63fd8ff3

def z129 : W := mkw 0x8b3effa053fbea02 0xdf3fffc063fffc03

def z130 : W := mkw 0x51bf7ffef8228015 0xfdbffffffc03800f

def z131 : W := mkw 0x440b9459a3f68f75 0xffef9cd8e3ff8fff

def z132 : W := mkw 0x048100f400000e40 0x000000c000000c00

def z133 : W := mkw 0x0000000000000000 0xf0001c00e003800f

def z134 : W := mkw 0x04b540f500040f60 0x0dffe0ff00000ff0

def z135 : W := mkw 0x08308a0003fbe000 0x0e301f0003fff000

def z136 : W := mkw 0x82300aa056815a8a 0xf4201fc0ff03fc0f

def z137 : W := mkw 0x4003845021408441 0xdfef8cd863618c73

def z138 : W := mkw 0x00400001042e31bc 0x2240000000fe73fc

def z139 : W := mkw 0x0034c00003d00000 0x0f3fe00003fc0000

def z140 : W := mkw 0x090a3f00002be000 0x00001f000003f000

def z141 : W := mkw 0xc2338ef073c1ce43 0xd4278cc063018c03

def z142 : W := mkw 0x108100f470000000 0x000000c060000000

def z143 : W := mkw 0x0000000004001088 0x2ad013209c82738c

def z144 : W := mkw 0x148100fff8040f60 0x00c000fffc000ff0

def z145 : W := mkw 0x000a940001628000 0x0f2f9c0003638000

def z146 : W := mkw 0x00783babdc2e31bc 0x2ff87ffffcfe73fc

def z147 : W := mkw 0x0008310a88000000 0x0998733f9c000000

def z148 : W := mkw 0x000b1458a0000000 0x0daf9cd8e0000000

def z149 : W := mkw 0x003ed40003f28000 0x0f3ffc0003ff8000

def z150 : W := mkw 0x00b54af450000000 0x0dbffffffc000000

def z151 : W := mkw 0x1184610608000000 0x0000600700000000

def z152 : W := mkw 0x0936ce0003d1c000 0x0f3fec0003fd8000

def z153 : W := mkw 0x004021020c083088 0x000003001c007000

def z154 : W := mkw 0x097eff0b8ffff1bc 0x2fffff3f9ffff3fc

def z155 : W := mkw 0x013e7f00002a2000 0x0f3fff0000fe7000

def z156 : W := mkw 0x11b76ff678000000 0x0437efe77c000000

def z157 : W := mkw 0x490ff558a17aa455 0xffeffcd8e37f8c7f

def z158 : W := mkw 0x8200000006815a8a 0x0000000000807380

def z159 : W := mkw 0x04b540f502940f60 0x00d060ff009c0ff0

def z160 : W := mkw 0x0800000002996000 0x00000000009c7000

def z161 : W := mkw 0x11bf7ffef8000000 0xffffffffff038c0f

def z162 : W := mkw 0x0001805101440560 0x0fffe0ff03fc0ff0

def z163 : W := mkw 0x097eff030ffff1a8 0x0f3fff271ffff380

def z164 : W := mkw 0x86b44aa556955baa 0x001063271c9c7380

def z165 : W := mkw 0x493fff58a3fbe455 0xffffffd8e3fffc7f

def z166 : W := mkw 0xc200800007e3dedf 0xf240000003e3ffff

def z167 : W := mkw 0x400b9458a56294dd 0xffff9ff8ffe3ffff

def z168 : W := mkw 0x400a9408a1628015 0xff2f9c00e363800f

def z169 : W := mkw 0x44bfd4fda3f68f75 0xfffffcffe3ff8fff

def z170 : W := mkw 0x4937ce5023d1c441 0xd4278cc063018c03

def z171 : W := mkw 0x090ef500017aa000 0x0f2ffc00037f8000

def z172 : W := mkw 0x404bb55ba96ea575 0xffeffcdfe37f8c7f

def z173 : W := mkw 0x4003845021408441 0xfee79cc0e3038c0f

def z174 : W := mkw 0x080a940003fbe000 0x0f2f9c0003fff000

def z175 : W := mkw 0x093e7f0002996000 0x0d3fff00009c7000

def z176 : W := mkw 0x0035c05003d00440 0x0fffe0d803fc0c70

def z177 : W := mkw 0x04bdf1f503fe2f60 0x0ffff3ff03fe7ff0

def z178 : W := mkw 0x04b5c0f403d00e40 0x0dbfe0ff03000c00

def z179 : W := mkw 0x04b5c0f503d40f60 0x0437e0e7039c0f80

def z180 : W := mkw 0x4dbffffda3ffef75 0xffffffffe3ffffff

def z181 : W := mkw 0x11be7faef8000000 0x00107f27fc000000

def z182 : W := mkw 0x8600800107d55fea 0xf240000003ffffff

def z183 : W := mkw 0x0040000b8c0411bc 0x2ad0133f9c8273fc

def z184 : W := mkw 0xd3bffffeffe3dedf 0xffffffffffe3ffff

def z185 : W := mkw 0x00300aa050000000 0x001003201c000000

def z186 : W := mkw 0x0936ce0003d1c000 0x04278c0003018000

def z187 : W := mkw 0x93bf7ffefe815a8a 0xffffffffff83ff8f

def z188 : W := mkw 0x19bfff5eabfbe000 0x0f3fff1f03fff000

def z189 : W := mkw 0x8200000006815a8a 0xf24000000383ff8f

def z190 : W := mkw 0x0034c0a003d00a00 0x0fffe0e003fc0f80

def z191 : W := mkw 0x40091058a0220455 0xfbc810d8e0620c7f

def z192 : W := mkw 0x82000a005401508a 0xfee01fc0ff03fc0f

def z193 : W := mkw 0x400b1458a0000455 0xfdef9cd8e0000c7f

def z194 : W := mkw 0x82300aa056815a8a 0x0cb01fe0fc807380

def z195 : W := mkw 0x0936ef0003d9e000 0x0437ef00039df000

def z196 : W := mkw 0x55bffffffbf68f75 0xffffffffffff8fff

def z197 : W := mkw 0x10c931fffc2e31bc 0x2bd873fffcfe73fc

def z198 : W := mkw 0x093eff0003fbe000 0xffffffc0e3fffc0f

def z199 : W := mkw 0x118f7f5ef8000000 0x010fff1ffc000000

def z200 : W := mkw 0x82300aa054001a8a 0xfcf01fe0fc000f8f

def z201 : W := mkw 0x82300a0006815a8a 0xfe701f000383ff8f

def z202 : W := mkw 0x09bffff403fbe000 0x0fbfffff03fff000

def z203 : W := mkw 0x000b9458a1400440 0x0fef9cd8e3600c70

def z204 : W := mkw 0x11020e0070000000 0x00000c0060000000

def z205 : W := mkw 0x11ff7ffffc2e31bc 0x2ffffffffcfe73fc

def z206 : W := mkw 0x004021030c0c31a8 0x001063271c9c7380

def z207 : W := mkw 0x4003845021408441 0xd4278cc063018c03

def z208 : W := mkw 0x400b9458a1628455 0xd52f8cd863618c73

def z209 : W := mkw 0x11bf7ffefa814000 0x0fbfffffff83f000

def z210 : W := mkw 0x0000000000000000 0xd4200cc063018c03

def z211 : W := mkw 0x82300aa056815a8a 0x001003201c807380

def z212 : W := mkw 0x0034c00003d00000 0x0427800003000000

def z213 : W := mkw 0x0db7cef503d5cf60 0x0fffecff03fd8ff0

def z214 : W := mkw 0x090eff00017be000 0x010fff00007ff000

def z215 : W := mkw 0x113a3faaf8000000 0x0cb01fe0fc000000

def z216 : W := mkw 0x0906c40001508000 0x0007800000000000

def z217 : W := mkw 0x000b355aa8000000 0x0dbffffffc000000

def z218 : W := mkw 0x110a350aa8000000 0x0000000000000000

def z219 : W := mkw 0x40010058a0000455 0xfee01cd8e3038c7f

def z220 : W := mkw 0x0001805001400440 0x010f801800600070

def z221 : W := mkw 0x8200000002814a02 0xd000000003018c03

def z222 : W := mkw 0x003000a002800a00 0xfef01ce0e3838f8f

def z223 : W := mkw 0x448fd45da1768575 0xffeffcdfe37f8c7f

def z224 : W := mkw 0x400a1408a0228015 0xfbc81c18e063807f

def z225 : W := mkw 0x118f755ea8000000 0x099ff33f9c000000

def z226 : W := mkw 0x403fd458a3f28455 0xfffffcd8e3ff8c7f

def z227 : W := mkw 0x93bf7ffefc01508a 0xfdbffffffc03f00f

def z228 : W := mkw 0x824831abdc2e3bbe 0xfbd873fffcfe7fff

def z229 : W := mkw 0x00400001040c31a8 0x00000000009c7380

def z230 : W := mkw 0x11bf7ffef8000000 0x011fe33f1c000000

def z231 : W := mkw 0x0000000000000000 0x0000000000000000

def z232 : W := mkw 0x82300aa156855baa 0xfff87fffffffffff

def z233 : W := mkw 0x0db46ba5029d6b20 0x00106327009c7380

def z234 : W := mkw 0x92b10afefe815a8a 0xfef01fffff83ff8f

def z235 : W := mkw 0x0009905881620454 0x2fef90d883620c7c

def z236 : W := mkw 0x820000000401508a 0xf00000000003f00f

def z237 : W := mkw 0x0001805001400440 0xffef9cd8e3638c7f

def z238 : W := mkw 0x400b9458a1628455 0x0daf9cd8e0600070

def z239 : W := mkw 0x400b9458a1628455 0xf4279cc0e3038c0f

def z240 : W := mkw 0x82300aa056815a8a 0xf0101f20fc83f38f

def z241 : W := mkw 0x40408001056eb5fd 0xf240000003ffffff

def z242 : W := mkw 0x193eff0afbfbe000 0x0f3fff00fffff000

def z243 : W := mkw 0x820000a056815a8a 0xf2c000e0ff83ff8f

def z244 : W := mkw 0x0934eb0003fbe000 0x0210630003fff000

def z245 : W := mkw 0x09346b0002996000 0x0e307f00039ff000

def z246 : W := mkw 0x11b74ef470000000 0x0cb79fe0fc000000

def z247 : W := mkw 0x0d8ff555017ea560 0x010fe01f007c0070

def z248 : W := mkw 0x823a9ea057e3da8a 0xffff9fe0ffe3ff8f

def z249 : W := mkw 0x10b10afef8000000 0x0cb01ffffc000000

def z250 : W := mkw 0x0034c00103d40120 0x0fffe03f03fc03f0

def z251 : W := mkw 0x04f5c0ff8fd41ffc 0x2fffe0ff9ffc0ffc

def z252 : W := mkw 0x1187445420000000 0x0007800000000000

def z253 : W := mkw 0x1081005ea8000000 0x0000001f00000000

def z254 : W := mkw 0x094a3f0a8c2bf09c 0x20001f009c03f00c

def z255 : W := mkw 0x15bf7ffff8040f60 0x0dfffffffc000ff0

def z256 : W := mkw 0x00300a0002814000 0xfef01fc0e383fc0f

def z257 : W := mkw 0x04bfd4fda3d40f60 0x0ffffcffe3fc0ff0

def z258 : W := mkw 0x0048310b8c2e31bc 0xfff87fffffffffff

def z259 : W := mkw 0x82783babdeaf7bbe 0xfff87fffffffffff

def z260 : W := mkw 0x010a3f0000000000 0x00001f0000000000

def z261 : W := mkw 0x000a940001628000 0xffef9cc0e3638c0f

def z262 : W := mkw 0x0000000000220014 0x224000000062007c

def z263 : W := mkw 0x097eff0b8bffe134 0x0f3fff1f03fff070

def z264 : W := mkw 0x0000800001400000 0x0f2f800003600000

def z265 : W := mkw 0x40000008a0000015 0xf0000000e000000f

def z266 : W := mkw 0x04b5caf553d40f60 0x0ffffffffffc0ff0

def z267 : W := mkw 0x400bb558a16aa455 0xffffffd8e3fffc7f

def z268 : W := mkw 0x0000210000082000 0x00106300009c7000

def z269 : W := mkw 0x0000000004001088 0xfef01fe0ff83ff8f

def z270 : W := mkw 0x114a3f0bfc2e31bc 0x2bd87f3ffcfe73fc

def z271 : W := mkw 0x08008000017aa000 0x00000000007c0000

def z272 : W := mkw 0x11bffffef9628000 0x0fbfffffff638000

def z273 : W := mkw 0x00b540f500040120 0x0fffe0ff00fc03f0

def z274 : W := mkw 0x93bf7ffefa814a02 0xddbfffffff018c03

def z275 : W := mkw 0x82783babdeaf7bbe 0x2bd8733f9cfe73fc

def z276 : W := mkw 0x82300aa05401508a 0xfcb01fe0fc03f00f

def z277 : W := mkw 0x0c00800103ffef60 0x0240000003fffff0

def z278 : W := mkw 0x8a308aa057fbfa8a 0xfef01fe0ffffff8f

def z279 : W := mkw 0x928100fefc001a8a 0xf0c000fffc000f8f

def z280 : W := mkw 0x11ff7ffffc0411bc 0x2dfffffffc0003fc

def z281 : W := mkw 0x090abf00016be000 0x0f2f9f000363f000

def z282 : W := mkw 0x097c7b0b8ebf71bc 0x2bd8733f9cfe73fc

def z283 : W := mkw 0x090ef50003fbe000 0x030fe00003fff000

def z284 : W := mkw 0x093eff0003fbe000 0x011fe30000fc7000

def z285 : W := mkw 0xc2338ef077c1decb 0xfef79fe0ff83ff8f

def z286 : W := mkw 0x093eff0007fbf088 0x2fffff209ffff38c

def z287 : W := mkw 0x15b5ebf75bd40f60 0x0fffe3ff1ffc0ff0

def z288 : W := mkw 0x11cf755fa82e2134 0x010fe01f007c0070

def z289 : W := mkw 0xc27bbffbffefffff 0xffffffffffffffff

def z290 : W := mkw 0x11bf7ffef8000000 0x052fecdf60000000

def z291 : W := mkw 0x823000a006815a8a 0xfef000e00383ff8f

def z292 : W := mkw 0x04b100f502840f60 0x0ef000ff03800ff0

def z293 : W := mkw 0x404b945bad6695fd 0xffef9cffff638fff

def z294 : W := mkw 0x86b5caf453d14e42 0xd4278cc063018c03

def z295 : W := mkw 0xcb3ffff8f7fbfedf 0xfffffff8ffffffff

def z296 : W := mkw 0x40010058a0000455 0x0000001800000070

def z297 : W := mkw 0x493eff0003fbe455 0xff7fff0003fffc7f

def z298 : W := mkw 0x82000a005401508a 0xfad01f20fc83f38f

def z299 : W := mkw 0x480b9458a3fbe455 0xffef9cd8e3fffc7f

def z300 : W := mkw 0x82000a005401508a 0xf0001f00fc03f00f

def z301 : W := mkw 0x108000a658000000 0x000000271c000000

def z302 : W := mkw 0x013f7f58a0000000 0x0dbfffd8e0000000

def z303 : W := mkw 0x004831030c2e31a8 0x0b1873271cfe7380

def z304 : W := mkw 0x403b9ef8f1628455 0xffff9ff8ff638c7f

def z305 : W := mkw 0x400b1458a0228455 0xf0c01cd8e0038c7f

def z306 : W := mkw 0x004021030c0c31a8 0x0bd8633f1cfc73f0

def z307 : W := mkw 0x048180f501440f60 0x0fef80ff03600ff0

def z308 : W := mkw 0x0008100880220014 0x0108001800600070

def z309 : W := mkw 0x093c7b0002bb6000 0x0b18730000fe7000

def z310 : W := mkw 0x004b355bac2e31bc 0x2ffffffffcfe73fc

def z311 : W := mkw 0x003180f003c00e40 0x0fff80f803e00ff0

def z312 : W := mkw 0x003a9e0003e3c000 0x0f3f9f0003e3f000

def z313 : W := mkw 0x400b9459a1668575 0xfffffcffe3ff8fff

def z314 : W := mkw 0x82702ba35e8d7baa 0xfef07fe7ff9fff8f

def z315 : W := mkw 0x00400001042e31bc 0x2bd8603f00fe73fc

def z316 : W := mkw 0x11b56bf658000000 0x0dbfe3ff1c000000

def z317 : W := mkw 0x823b1ef8f6815a8a 0xffff9ff8ff83ff8f

def z318 : W := mkw 0x0000000004001088 0x200013009c02700c

def z319 : W := mkw 0x09344a0002914000 0x0000000000000000

def z320 : W := mkw 0x04bdf1ff8bd40f60 0x0ffff3ff9ffc0ff0

def z321 : W := mkw 0x15bf7ffffa940b20 0x0dbffffffc9c0380

def z322 : W := mkw 0xc20b9458a7e3dedf 0xffef9cd8e3e3ffff

def z323 : W := mkw 0x400bb55aa9628455 0xffffffffff638c7f

def z324 : W := mkw 0x4003845021628455 0xf6678cc063638c7f

def z325 : W := mkw 0x4400800103f68f75 0xf240000003ff8fff

def z326 : W := mkw 0x048180f503d40f60 0x02c000ff03fc0ff0

def z327 : W := mkw 0x404a350aac2ab09d 0xf0001f00fc03f00f

def z328 : W := mkw 0x82318af057c15eca 0xffff9ff8ffe3ffff

def z329 : W := mkw 0x8b3eff0057fbf08a 0xff3fff00fffff00f

def z330 : W := mkw 0x19bf7ffefa996000 0x0dbffffffc9c7000

def z331 : W := mkw 0x00083100002a2000 0x0000130000027000

def z332 : W := mkw 0x933a3faafe815a8a 0xfef01fe0ff83ff8f

def z333 : W := mkw 0xc23a1ea8f6a3da9f 0xfef01fe0ff83ff8f

def z334 : W := mkw 0x093ef50003faa000 0x0f3fe00003fc0000

def z335 : W := mkw 0x19bf7ffef82be000 0x0dbffffffc03f000

def z336 : W := mkw 0x0048310b8c2e31bc 0x2108731f9c7e707c

def z337 : W := mkw 0x198ff55ea97aa000 0x010fe01f007c0000

def z338 : W := mkw 0x093eff0883fbe014 0x2fffff1883fff07c

def z339 : W := mkw 0x8b3a3fa056abfa8a 0xfef01fe0ff83ff8f

def z340 : W := mkw 0xc2308aa057e3dedf 0xfef01fe0ffe3ffff

def z341 : W := mkw 0x11bc7baed8000000 0x0998733f9c000000

def z342 : W := mkw 0x8b36cea053d1ca02 0xd4278cc063018c03

def z343 : W := mkw 0x0000800003d00000 0x0200000003fc0000

def z344 : W := mkw 0x4000000000228015 0xf00000000003800f

def z345 : W := mkw 0x0834c00003fbe000 0x0f3fe00003fff000

def z346 : W := mkw 0x114a3f0afc2a309c 0x20001f00fc02700c

def z347 : W := mkw 0x15b7cef473d00e40 0x04278cc063000c00

def z348 : W := mkw 0x11f46ba75c0c31a8 0x001063271c9c7380

def z349 : W := mkw 0x59bffffefbfbe455 0xfffffffffffffc7f

def z350 : W := mkw 0x11b46ba658000000 0x0cb07fe7fc000000

def z351 : W := mkw 0x003000a002800a00 0x042000c003000c00

def z352 : W := mkw 0x0808b10003fbe000 0x0b18730003fff000

def z353 : W := mkw 0x00083100002a2000 0x01086000007c0000

def z354 : W := mkw 0x0085405400000000 0x010fe01f00000000

def z355 : W := mkw 0x400b9458a1628455 0xf10f9c18e063807f

def z356 : W := mkw 0x04b5c0f503d40f60 0x04e780ff03000ff0

def z357 : W := mkw 0x048000a500040b20 0x0000002700000380

def z358 : W := mkw 0x118f75fef8000000 0x018fe0fffc000000

def z359 : W := mkw 0x11bf7ffefc001088 0x2ffffffffc82738c

def z360 : W := mkw 0x04b5c05503d40560 0x0f3fe01f03fc0070

def z361 : W := mkw 0x01364e0000000000 0x04278c0000000000

def z362 : W := mkw 0x0800800003d1c000 0x0000000003018000

def z363 : W := mkw 0x82000a0056815a8a 0xf2401f00ff83ff8f

def z364 : W := mkw 0x400b9458a1628455 0x0fef80d803600c70

def z365 : W := mkw 0x04bfd4f503f68f60 0x0ffffcff03ff8ff0

def z366 : W := mkw 0x0904610000182000 0x00006000001c0000

def z367 : W := mkw 0x44fff5ffaffebffd 0xffffffffffffffff

def z368 : W := mkw 0x82300aa056815a8a 0x0e301f201f83f380

def z369 : W := mkw 0xc20b94f8f5629edf 0xffef9cf8ff638fff

def z370 : W := mkw 0x40038458a1408455 0xf4e78cd8e3018c7f

def z371 : W := mkw 0x82381aa8d6a35a9e 0xfff81ff8ffe3ffff

def z372 : W := mkw 0x0008310b88040120 0x0bd8733f9cfc03f0

def z373 : W := mkw 0x0dbfff5503ffe560 0x0f3fff1f03fff070

def z374 : W := mkw 0x8200000004001a8a 0xf040000000000f8f

def z375 : W := mkw 0x00b540f400000000 0x042780c000000000

def z376 : W := mkw 0x0008310a882a2000 0x0b98733f9cfe7000

def z377 : W := mkw 0x00b5c0f403d00000 0x0fbfe0ff03fc0000

def z378 : W := mkw 0x04b440a502940b20 0x0ef060e7039c0f80

def z379 : W := mkw 0x11bf5efcf0000000 0x0daf9cd8e0000000

def z380 : W := mkw 0x0008310000000000 0x0918730000000000

def z381 : W := mkw 0x04fdf1ff8bfe2f74 0x0fffe0ff03fc0ff0

def z382 : W := mkw 0x0008100980260134 0x2bd8703f80fe03fc

def z383 : W := mkw 0x82300aa056815a8a 0xf4e00ce0ff018f8f

def z384 : W := mkw 0x0000000000000000 0x2ac010008002000c

def z385 : W := mkw 0x01bf7ff400000000 0x0dbfffff00000000

def z386 : W := mkw 0x00300a0000000000 0x0c301f0000000000

def z387 : W := mkw 0x82300aa056815a8a 0xf0d003e0fc807f8f

def z388 : W := mkw 0x8b3eff0007fbfa8a 0xff7fff0003ffff8f

def z389 : W := mkw 0x0448b10b8ffe3ffc 0x2bd8733f9ffe7ffc

def z390 : W := mkw 0x404a350bac2eb1bd 0xfbd87f3ffcfff3ff

def z391 : W := mkw 0x04cdf15f897e2574 0x010fe01f007c0070

def z392 : W := mkw 0x000a140000228000 0x00001c0000038000

def z393 : W := mkw 0x0434c00103d40f60 0x0f7fe00003fc0ff0

def z394 : W := mkw 0x003000a006801a88 0x2ef013e09f827f8c

def z395 : W := mkw 0x0048310b882e2134 0x2bc8701f807e007c

def z396 : W := mkw 0x86b5caf457d15eca 0xfef79fe0ff83ff8f

def z397 : W := mkw 0xc2310af8f6815edf 0xfef01ff8ff83ffff

def z398 : W := mkw 0x00083100042a3088 0x2bd873209cfe738c

def z399 : W := mkw 0x400b945021628441 0xdf2f9cc063638c03

def z400 : W := mkw 0x0008310a88000000 0x0108601f00000000

def z401 : W := mkw 0x44b5c0fda3d40f75 0xffffe0ffe3fc0fff

def z402 : W := mkw 0x4000800001408441 0xd000000003018c03

def z403 : W := mkw 0x00000a0050000000 0x00001f00fc000000

def z404 : W := mkw 0x518ff55ea9628455 0xffeffcdfe3638c7f

def z405 : W := mkw 0x00383baad8000000 0x0db87ffffc000000

def z406 : W := mkw 0x0001005000000440 0x00c000d800000c70

def z407 : W := mkw 0x158ff55fa9540560 0x010fe01f007c0070

def z408 : W := mkw 0x01346b0000000000 0x0010630000000000

def z409 : W := mkw 0x000a940881628014 0x2fef9c188363807c

def z410 : W := mkw 0x093effa003fbea00 0x0fffffe003ffff80

def z411 : W := mkw 0x82483b0bdc2f71be 0xfbd87f3ffcfff3ff

def z412 : W := mkw 0x00010058a0000000 0x008000d8e0000000

def z413 : W := mkw 0x004000030c0411a8 0x000000271c000380

def z414 : W := mkw 0x51bffffef9408441 0xddbfffffff018c03

def z415 : W := mkw 0x000b1458a0000000 0x010f801800000000

def z416 : W := mkw 0x0040000a8c00109c 0x200000009c00000c

def z417 : W := mkw 0x0008100880000000 0x0988101880000000

def z418 : W := mkw 0x51bfdefcf1628455 0xffef9cd8e3638c7f

def z419 : W := mkw 0x003000a000000000 0x0cb000e000000000

def z420 : W := mkw 0x000000a000000a00 0x00c000e000000f80

def z421 : W := mkw 0x003b1ef8f0000000 0x0dbf9ff8fc000000

def z422 : W := mkw 0x094a3f0b8c2ff1bc 0x2bd87f3f9cfff3fc

def z423 : W := mkw 0x493eff08a3fbe015 0xff3fff00e3fff00f

def z424 : W := mkw 0x0048310a882a2014 0x0000000000000000

def z425 : W := mkw 0x490a3f08a02be015 0xf0001f00e003f00f

def z426 : W := mkw 0x04b4c0a503d40f60 0x0250602703fc0ff0

def z427 : W := mkw 0xc20100f8f4001edf 0xf0c000f8fc000fff

def z428 : W := mkw 0x0048310b8c2e31bc 0x224013009cfe73fc

def z429 : W := mkw 0x093eff00017aa000 0x0d3fff00007c0000

def z430 : W := mkw 0x82783baadeab7a9e 0xfef01fe0ff83ff8f

def z431 : W := mkw 0xc23b9ef8f3e3ce57 0xffef9cd8e3638c7f

def z432 : W := mkw 0x0048310b8c2e31bc 0x201073279c9e738c

def z433 : W := mkw 0x404bb55bad6eb5fd 0x2bdff33f9cfe73fc

def z434 : W := mkw 0x0000210208000000 0x001063271c000000

def z435 : W := mkw 0x0034400000000000 0x0d3fe00000000000

def z436 : W := mkw 0x0000000000000000 0x0ee000c003000c00

def z437 : W := mkw 0x400a940001628455 0xff6f9c0003638c7f

def z438 : W := mkw 0x510a3f0af8228015 0xf0001f00fc03800f

def z439 : W := mkw 0x093eff0003fbe000 0x04279f000303f000

def z440 : W := mkw 0x823000a056801a8a 0xfef000e0ff800f8f

def z441 : W := mkw 0x000000a050000000 0x008000e0fc000000

def z442 : W := mkw 0x0040210b8c0c31bc 0x20d0633f9c9c73fc

def z443 : W := mkw 0x11bf7ff470000000 0x0d3fffc060000000

def z444 : W := mkw 0x11bffffef9400440 0x0fffffffff600c70

def z445 : W := mkw 0x000ab500016aa000 0x0f3fff0003fff000

def z446 : W := mkw 0x04b540f502940b20 0x0dbfe0ff009c0380

def z447 : W := mkw 0x097eff0a8ffbf09c 0x2f3fff009ffff00c

def z448 : W := mkw 0x820000a050000a02 0xd00000c060000c03

def z449 : W := mkw 0x493fff58a3fbe455 0x0f3fff1803fff070

def z450 : W := mkw 0x09746b030e9d71a8 0x001063271c9c7380

def z451 : W := mkw 0x0000000000000000 0x089013209c000000

def z452 : W := mkw 0x09002b0000096000 0x0000030000007000

def z453 : W := mkw 0x44bfd4fca3f28e55 0xffef9cd8e3638c7f

def z454 : W := mkw 0x19bffffefbd1c000 0x0dbfffffff018000

def z455 : W := mkw 0x4800800003fbe455 0xf240000003fffc7f

def z456 : W := mkw 0x0485c05401500440 0x0007800000000000

def z457 : W := mkw 0x8b36cea057d1da8a 0xfef79fe0ff83ff8f

def z458 : W := mkw 0x19bffff473fbe000 0x0f3fffc063fff000

def z459 : W := mkw 0x400a9408a1628455 0xf2401c00e3638c7f

def z460 : W := mkw 0x04b5caf503d54f60 0x0fffffff03fffff0

def z461 : W := mkw 0x8b7effabdffffbbe 0xffffffffffffffff

def z462 : W := mkw 0x0401805103d40f60 0x0fef80d803fc0ff0

def z463 : W := mkw 0x400b9458a1628455 0xf34f801803638c7f

def z464 : W := mkw 0x15bffffefbd00e40 0x0dbfffffff000c00

def z465 : W := mkw 0x82300aa052814a02 0x0000000000000000

def z466 : W := mkw 0x007831ab8eae3bbc 0x2ff873ff9ffe7ffc

def z467 : W := mkw 0x0048310b882e2134 0x0998733f9c7c0070

def z468 : W := mkw 0x11bf7ffff8040120 0x0ffffffffcfc03f0

def z469 : W := mkw 0x44b5c0f503f68f75 0xffffe0ff03ff8fff

def z470 : W := mkw 0x82300aa052814a02 0xde301fc06383fc03

def z471 : W := mkw 0x0048310a8c2a309c 0x2b1873009cfe700c

def z472 : W := mkw 0x00300aa052800a00 0x0ef01fe0ff800f80

def z473 : W := mkw 0x0400800101540560 0x00000000007c0070

def z474 : W := mkw 0x0000000a88000000 0x0080003f9c000000

def z475 : W := mkw 0x93b74ef476815a8a 0xfef79fe0ff83ff8f

def z476 : W := mkw 0x11b74ef470000000 0x0dbfecff60000000

def z477 : W := mkw 0x000b1458a0220014 0x2fef9cd8e062007c

def z478 : W := mkw 0x400b9458a1628455 0x2bcf90188062007c

def z479 : W := mkw 0x00300aa050000000 0xfef01fe0ff038c0f

def z480 : W := mkw 0x093eff0003fbe000 0x052fec00037d8000

def z481 : W := mkw 0x094ef50b8d7eb1bc 0x2bdff33f9cfe73fc

def z482 : W := mkw 0x0001005000000000 0x0daf80d800000000

def z483 : W := mkw 0x86b44aa556955baa 0xfef07fe7ff9fff8f

def z484 : W := mkw 0x11bf75fea8000000 0x0dbfe0ff00000000

def z485 : W := mkw 0x11bf7ffefa800a00 0x0fffffffff800f80

def z486 : W := mkw 0x0000000000000000 0x0e201c0003038000

def z487 : W := mkw 0x013e7f0002814000 0x0f3fff000383f000

def z488 : W := mkw 0x4000800001628455 0xfee01cc0e3638c7f

def z489 : W := mkw 0x04b5c0f403d00e40 0x0f3fe0c003fc0c00

def z490 : W := mkw 0x0048310b8c2e31bc 0x20c0133f9c0273fc

def z491 : W := mkw 0x11bffffefbd00000 0x0fbffffffffc0000

def z492 : W := mkw 0x00000a0000014000 0x00001f000003f000

def z493 : W := mkw 0x0000000100040120 0x0240000000fc03f0

def z494 : W := mkw 0x0000000100040120 0x00106027009c0380

def z495 : W := mkw 0x4002040020008001 0xd0000c0060018003

def z496 : W := mkw 0x00000000002a2000 0x0200000000fe7000

def z497 : W := mkw 0x0000000004001088 0x20c000209c00038c

def z498 : W := mkw 0x00383b0002ab6000 0x0f387f0003fff000

def z499 : W := mkw 0x82300aa052814a02 0xdef00ce063818f83

def z500 : W := mkw 0x19b7cef473d1c000 0x04278cc063018000

def z501 : W := mkw 0x820000a054001a8a 0x000000201c000380

def z502 : W := mkw 0x0034400002900000 0x00106000009c0000

def z503 : W := mkw 0x0400000102940b20 0x00000000009c0380

def z504 : W := mkw 0x448100fda0040f75 0xf0c000ffe0000fff

def z505 : W := mkw 0x0848b10b8ffff1bc 0x2bd8733f9ffff3fc

def z506 : W := mkw 0x4000000000000455 0xf040000000000c7f

def z507 : W := mkw 0x093eff0003d1c000 0x0d3fff0003018000

def z508 : W := mkw 0x110b3f5af8000000 0x0daf9fd8fc000000

def z509 : W := mkw 0x40018058a1628455 0xf2c000d8e3638c7f

def z510 : W := mkw 0xc20b9e58f563d4df 0xffef9fd8ff63fc7f

def z511 : W := mkw 0x0048310b8c2e31bc 0x21c8603f9c7c03fc

def z512 : W := mkw 0x448b94fda1668f75 0xffef9cffe3638fff

def z513 : W := mkw 0x0000800001628000 0x0200000003638000

def z514 : W := mkw 0x93bf7ffefc001a8a 0xfdfffffffc000f8f

def z515 : W := mkw 0x000810088422109c 0x2bd813389ce273fc

def z516 : W := mkw 0x00bf54fca0000000 0x0dbffcffe0000000

def z517 : W := mkw 0x11bf7f5ea8000000 0x0d3fff1f00000000

def z518 : W := mkw 0x04bdd0fd83f60f74 0x2ffff0ff83fe0ffc

def z519 : W := mkw 0x010e750000000000 0x010fe00000000000

def z520 : W := mkw 0x000a1408a0000000 0x00001c00e0000000

def z521 : W := mkw 0x04cdf15f8d7e35fc 0x2bdff33f9cfe73fc

def z522 : W := mkw 0x0cb5c0f503ffef60 0x0fffe0ff03fffff0

def z523 : W := mkw 0x93b74ef472814a02 0xd4278cc063018c03

def z524 : W := mkw 0x0048310b8c2e31bc 0x0118633f1cfc73f0

def z525 : W := mkw 0x00300aa050000000 0x04200cc060000000

def z526 : W := mkw 0x0048310a8c2a309c 0x2bc813189c62707c

def z527 : W := mkw 0x0048310b8c0411bc 0x29d8733f9c0003fc

def z528 : W := mkw 0x0048310a8c2a309c 0x2998733f9c02700c

def z529 : W := mkw 0x0485c05501540560 0x0fefe0df037c0c70

def z530 : W := mkw 0x0000000000000000 0x0b18600000fc0000

def z531 : W := mkw 0x1dbffffffbffef60 0x0ffffffffffffff0

def z532 : W := mkw 0x1000000af8000000 0x00000000fc000000

def z533 : W := mkw 0x51b7cef471408441 0xd4278cc063018c03

def z534 : W := mkw 0x19beffa65bfbe000 0x0f3fff271ffff000

def z535 : W := mkw 0x82383baade815a8a 0xfff87fffff83ff8f

def z536 : W := mkw 0x0d3eff0103ffef60 0x0f7fff0003fffff0

def z537 : W := mkw 0x4000800001628455 0x0000000000600070

def z538 : W := mkw 0x0001805001400440 0x042780c003000c00

def z539 : W := mkw 0x8200000006815a8a 0xfad013209f83ff8f

def z540 : W := mkw 0x004ab50b8d6eb1bc 0x2fffff3f9ffff3fc

def z541 : W := mkw 0x19fffffffffff1bc 0x2ffffffffffff3fc

def z542 : W := mkw 0x118b3ffef8000000 0x00801ffffc000000

def z543 : W := mkw 0x0db7cef403d1ce40 0x04278cc003018c00

def z544 : W := mkw 0x86fdfbffdfff7ffe 0xffffffffffffffff

def z545 : W := mkw 0x00300aa002814a00 0x0ef01fe00383ff80

def z546 : W := mkw 0x11b44aa450000000 0x0000000000000000

def z547 : W := mkw 0x820000005400108a 0xf0000000fc00000f

def z548 : W := mkw 0x0000000100040120 0x0108601f007c0070

def z549 : W := mkw 0x15fffffffffe3ffc 0x2ffffffffffe7ffc

def z550 : W := mkw 0x04b5c0f507d41fe8 0x2ffff3ff9ffe7ffc

def z551 : W := mkw 0x007cf10b8ffe31bc 0x2ffff33f9ffe73fc

def z552 : W := mkw 0x00b5c0f401400440 0x0fffe0ff03600c70

def z553 : W := mkw 0x82300aa056815a8a 0xf6600cc06383ff8f

def z554 : W := mkw 0x00300aa054001088 0x2ef01fe0fc82738c

def z555 : W := mkw 0x44b7c4f423d08e41 0xd4278cc063018c03

def z556 : W := mkw 0x04b5c0f501540560 0x0dbfe0ff007c0070

def z557 : W := mkw 0x0008100880220014 0xffe81cd8e3638c7f

def z558 : W := mkw 0x93b46ba65e815a8a 0x001063271c807380

def z559 : W := mkw 0x04f5e1f70fdc3fe8 0x0fffe3ff1ffc7ff0

def z560 : W := mkw 0x824000abdc041bbe 0xf0c000fffc000fff

def z561 : W := mkw 0x510bbf5af9628455 0xffef9fd8ff638c7f

def z562 : W := mkw 0x490ff558a17aa455 0x010fe018007c0070

def z563 : W := mkw 0x013eff0003d00000 0x0f3fff0003fc0000

def z564 : W := mkw 0x0484400500140120 0x00006007001c0000

def z565 : W := mkw 0x86b5c0f507d55fea 0xffffe0ff03ffffff

def z566 : W := mkw 0x090a3f00002be000 0x0b187f0000fff000

def z567 : W := mkw 0x108931fef8000000 0x099873fffc000000

def z568 : W := mkw 0x00400001002e2134 0x00000000007c0070

def z569 : W := mkw 0x40018058a1400455 0xffef80d8e3600c7f

def z570 : W := mkw 0x0000000000000000 0xf0c000c0e0000c0f

def z571 : W := mkw 0x0008100000220000 0x0b08100000620000

def z572 : W := mkw 0x82300a005681508a 0xfe301f00ff83f00f

def z573 : W := mkw 0x0485c05503d40f60 0x034fe01f03fc0ff0

def z574 : W := mkw 0x09020e000001c000 0x00000c0000018000

def z575 : W := mkw 0x86b5caf557d55fea 0x0fffe3ff1ffc7ff0

def z576 : W := mkw 0x0dffffff8ffffffc 0x2fffffff9ffffffc

def z577 : W := mkw 0x82383ba056ab7a8a 0xfff87fe0ffffff8f

def z578 : W := mkw 0x8200000006815a8a 0xfee01cc0e383ff8f

def z579 : W := mkw 0x11cf755fac2e31bc 0x2bdff33f9cfe73fc

def z580 : W := mkw 0x0003045020000000 0x04278cc060000000

def z581 : W := mkw 0x00b540f402800a00 0x0fffe0ff03800f80

def z582 : W := mkw 0x00300a0002814000 0x04200c0003018000

def z583 : W := mkw 0x0000000000000000 0x0ca01cc0e0000000

def z584 : W := mkw 0x0008310a8c001088 0x2bd8733f9c82738c

def z585 : W := mkw 0x8b3effa057fbfa8a 0x0f3fff201ffff380

def z586 : W := mkw 0x11ff7ffefc2a309c 0x2dbffffffc02700c

def z587 : W := mkw 0x15b46ba75a940b20 0x001063271c9c0380

def z588 : W := mkw 0x000a140000000000 0x0d2f9c0000000000

def z589 : W := mkw 0x82000a005401508a 0x000003001c007000

def z590 : W := mkw 0x097eff0107fff1bc 0x2f7fff0003fff3fc

def z591 : W := mkw 0x19b46ba65a996000 0x001063271c9c7000

def z592 : W := mkw 0x00083101002e2120 0x0bd8733f00fe73f0

def z593 : W := mkw 0x004021030c2e31bc 0x225063271cfe73fc

def z594 : W := mkw 0x04f461a70e9c3ba8 0x001063271c9c7380

def z595 : W := mkw 0x00083108802a2014 0x2bd8731880fe707c

def z596 : W := mkw 0x04c100ff8c041ffc 0x20c000ff9c000ffc

def z597 : W := mkw 0x497fff5baffff5fd 0xffffffffffffffff

def z598 : W := mkw 0x400a1408a0228015 0xfee01cc0e3038c0f

def z599 : W := mkw 0x118f755ea8000000 0x0daffcdfe0000000

def z600 : W := mkw 0x8248310b8eaf7bbe 0xfbd8733f9fffffff

def z601 : W := mkw 0x97bfffffffd55fea 0xffffffffffffffff

def z602 : W := mkw 0xc6bfdefdf7f7dfff 0xffffffffffffffff

def z603 : W := mkw 0x0048310a8c2a309c 0x2ad013209c82738c

def z604 : W := mkw 0x82000a0050014002 0xd0000c0060018003

def z605 : W := mkw 0x0030000002800000 0x0e30000003800000

def z606 : W := mkw 0x093fff58a3fbe000 0x0fbfffd8e3fff000

def z607 : W := mkw 0x00400001042e31bc 0x2ad013209cfe73fc

def z608 : W := mkw 0x4001005020000441 0xd00000c060000c03

def z609 : W := mkw 0x0000000002800a00 0x0240000003800f80

def z610 : W := mkw 0x00300a0002814000 0x0010030000807000

def z611 : W := mkw 0x8240000106af7bbe 0xf240000003ffffff

def z612 : W := mkw 0x8fbffff557ffffea 0xffffffffffffffff

def z613 : W := mkw 0x017e7f0b8c2e31bc 0x2fffff3f9cfe73fc

def z614 : W := mkw 0x00783b0b8eaf71bc 0x2ff87f3f9ffff3fc

def z615 : W := mkw 0x04b5c0f503d40f60 0x066780c003fc0ff0

def z616 : W := mkw 0x04b5c0f403d00e40 0x0fef80d803600c70

def z617 : W := mkw 0x003000a102840b20 0x0ff860ff03fc0ff0

def z618 : W := mkw 0x448fd45da1768575 0x010fe01f007c0070

def z619 : W := mkw 0x094ef50b897ea134 0x010fe01f007c0070

def z620 : W := mkw 0x0000000004001088 0x001003201c807380

def z621 : W := mkw 0x0dbeffa503ffeb20 0x0f3fff2703fff380

def z622 : W := mkw 0x093a3f0002abe000 0x0e301f000383f000

def z623 : W := mkw 0x0000000000000000 0xf240000003038c0f

def z624 : W := mkw 0x110a3f0af8000000 0x09987f3ffc000000

def z625 : W := mkw 0x00fd71ff8c2e31bc 0x2ffff3ff9cfe73fc

def z626 : W := mkw 0x508100fef8000455 0xf0c000fffc000c7f

def z627 : W := mkw 0x00300a0006815088 0x2ef01f209f83f38c

def z628 : W := mkw 0x93ff7ffffeaf7bbe 0xffffffffffffffff

def z629 : W := mkw 0x82300aa056815a8a 0x0ef003e01f807f80

def z630 : W := mkw 0x013e7fa050000000 0x0dbfffe0fc000000

def z631 : W := mkw 0x0dbffff403fbee40 0x0f3fffc003fffc00

def z632 : W := mkw 0x04b440a502940b20 0x0bd8603f00fc03f0

def z633 : W := mkw 0x508b94fef9628455 0xffef9cffff638c7f

def z634 : W := mkw 0x400b9458a1628455 0xf1cf80d8e0600c7f

def z635 : W := mkw 0x51bffffef9628455 0x0dbffffffc600070

def z636 : W := mkw 0x0040000b8c2e31bc 0x22c0003f9cfe73fc

def z637 : W := mkw 0x0000800001400440 0x0240000003600c70

def z638 : W := mkw 0x4001805001628455 0xffef80d803638c7f

def z639 : W := mkw 0x04fc71af8ebe3bbc 0x2bd8733f9cfe73fc

def z640 : W := mkw 0x00400001040411bc 0x20400000000003fc

def z641 : W := mkw 0x15bffffff9540560 0x0dbffffffc7c0070

def z642 : W := mkw 0x00400000042a309c 0x200000000002700c

def z643 : W := mkw 0x82702ba35e8d7baa 0x001063271c9c7380

def z644 : W := mkw 0x04c931ff8c2e3ffc 0x2bd873ff9cfe7ffc

def z645 : W := mkw 0x8b346ba056997a8a 0x001063201c9c7380

def z646 : W := mkw 0x15bff5ffabd40f60 0x0fffe0ff03fc0ff0

def z647 : W := mkw 0x04b4c0a503d40b20 0x0f3fe02703fc0380

def z648 : W := mkw 0x44bfd4fda3f68f75 0x0fffe0ff03fc0ff0

def z649 : W := mkw 0x0481005500040560 0x0000001f00000070

def z650 : W := mkw 0x400a1408a0228015 0x0000000000000000

def z651 : W := mkw 0x00402103080c2120 0x00006007001c0000

def z652 : W := mkw 0x000b1458a0000000 0xffef9cd8e3038c0f

def z653 : W := mkw 0x0000000000000000 0x0a10130000827000

def z654 : W := mkw 0x82483b0adc2b709e 0xf0001f00fc03f00f

def z655 : W := mkw 0x013eff0001628000 0x0f3fff0003638000

def z656 : W := mkw 0x82000aa054015a8a 0xf0c01fe0fc03ff8f

def z657 : W := mkw 0x403b94f8a3e28e55 0xffff9cf8e3e38fff

def z658 : W := mkw 0x413fff58a1628455 0xffffffd8e3638c7f

def z659 : W := mkw 0x04b440a402900a00 0x0000000000000000

def z660 : W := mkw 0x15b7cef573d40f60 0x0fffecff63fc0ff0

def z661 : W := mkw 0x008100f400000000 0x008000ff00000000

def z662 : W := mkw 0x82300aa056815a8a 0xf25003201f83ff8f

def z663 : W := mkw 0x82b54af456815a8a 0xffffffffff83ff8f

def z664 : W := mkw 0x400b1458a0228015 0xfdaf9cd8e003800f

def z665 : W := mkw 0x05bffff503d40f60 0x0fffffff03fc0ff0

def z666 : W := mkw 0x400b9458a1628455 0x0f2f9c1803638070

def z667 : W := mkw 0x0000000000000000 0x0ad0002000800380

def z668 : W := mkw 0x11ff7ffffc0c31a8 0x0dbffffffc9c7380

def z669 : W := mkw 0x0049b15b8d6e35fc 0x2ffff3ff9ffe7ffc

def z670 : W := mkw 0x0002840001408000 0x04278c0003018000

def z671 : W := mkw 0x0048310b882e2134 0x0b18731f00fe7070

def z672 : W := mkw 0x0040000b8c0411bc 0x2bd8603f9cfc03fc

def z673 : W := mkw 0x82300aa052814a02 0xfee01cc0e3038c0f

def z674 : W := mkw 0x04b5c0f403d00e40 0x0ef780e003800f80

def z675 : W := mkw 0x93b46ba65e815a8a 0xfef07fe7ff83ff8f

def z676 : W := mkw 0x93bf7ffefe815a8a 0x0dbffffffc807380

def z677 : W := mkw 0x0400800103d40f60 0x0bd8603f03fc0ff0

def z678 : W := mkw 0x0400000100040f60 0x0040000000000ff0

def z679 : W := mkw 0x11002b0258000000 0x000003001c000000

def z680 : W := mkw 0x493fde58a3f3c455 0xffef9cd8e3638c7f

def z681 : W := mkw 0x0048310b882e2134 0x0bd8603f00fc03f0

def z682 : W := mkw 0x11bf7ffef8000000 0x04279fc0fc000000

def z683 : W := mkw 0x0008310a88000000 0x000013009c000000

def z684 : W := mkw 0x8234caa057d15a8a 0xffffffe0ffffff8f

def z685 : W := mkw 0x4049315bac2e35fd 0xfbd873fffcfe7fff

def z686 : W := mkw 0x82700aabde855bbe 0xfef01fffff83ffff

def z687 : W := mkw 0x11ff7ffff82e2134 0x0dbffffffc7c0070

def z688 : W := mkw 0x0008100880220014 0x200010008002000c

def z689 : W := mkw 0x000b945001628440 0x0fef9cd803638c70

def z690 : W := mkw 0x004021030c0c31a8 0x2ad073279c9e738c

def z691 : W := mkw 0x000b9458a1628000 0x0faf9cd8e3638000

def z692 : W := mkw 0x00483101042e31bc 0x2b58730000fe73fc

def z693 : W := mkw 0x043080a103d40f60 0x0ef000e003fc0ff0

def z694 : W := mkw 0x0000000100040120 0x00c0003f000003f0

def z695 : W := mkw 0x404bb55aad6ab4dd 0xffef9fd8ff63fc7f

def z696 : W := mkw 0x0000000880000014 0x20c000188000007c

def z697 : W := mkw 0x4003845021408441 0x0007800000000000

def z698 : W := mkw 0x86b10af556855fea 0xfef01fffff83ffff

def z699 : W := mkw 0x0000000004001088 0x224000000082738c

def z700 : W := mkw 0x11fc7bafdc2e31bc 0x2bd8733f9cfe73fc

def z701 : W := mkw 0x490bbf58a16be455 0xffef9fd8e363fc7f

def z702 : W := mkw 0x093e7f00002be000 0x0d3fff000003f000

def z703 : W := mkw 0x093e7f0002bbe000 0x00107f00009ff000

def z704 : W := mkw 0x0400800003d00e40 0x0000000003000c00

def z705 : W := mkw 0x090a3500002aa000 0x0000000000000000

def z706 : W := mkw 0x82300aa052814a02 0xdcb01fe0ff018c03

def z707 : W := mkw 0x400b9458a1628455 0xf6679cc0e3638c7f

def z708 : W := mkw 0x4840800107fff5fd 0xf240000003ffffff

def z709 : W := mkw 0x04c100f504041ffc 0x20c000ff00000ffc

def z710 : W := mkw 0xc24a3f0afc2bf09f 0xf0001f00fc03f00f

def z711 : W := mkw 0x11bf7ffef8000000 0x0fffffffff000c00

def z712 : W := mkw 0x44be54ada2b68b35 0xf0107c27e09f838f

def z713 : W := mkw 0xc23b9ef8f7e3dedf 0x011f83381ce073f0

def z714 : W := mkw 0x000a940881628014 0xffef9cd8e3638c7f

def z715 : W := mkw 0x0976ce0b8fd5d1bc 0x24e78c3f9f0183fc

def z716 : W := mkw 0x04b5c0f503d40f60 0x0ffff3ff9ffc0ff0

def z717 : W := mkw 0x004021030c2e31bc 0x2bd8633f1cfe73fc

def z718 : W := mkw 0x188180fefbfbe000 0x028000fffffff000

def z719 : W := mkw 0x090eff00017be000 0x0b1fff0000fff000

def z720 : W := mkw 0x048100f504041fe8 0x20c000ff9c000ffc

def z721 : W := mkw 0x093eff0003fbe000 0x0fffffc003fffc00

def z722 : W := mkw 0x04408001057e35fc 0x2240000000fe73fc

def z723 : W := mkw 0x593eff0afbfbe015 0xff3fff00fffff00f

def z724 : W := mkw 0x11b74efef8000000 0x0cb79ffffc000000

def z725 : W := mkw 0x093eff0a8bfbe000 0x0f3fff1f03fff000

def z726 : W := mkw 0x4043a5532d4cb5e9 0xd437efe77f9dff83

def z727 : W := mkw 0x0040800107fe31bc 0x2240000003fe73fc

def z728 : W := mkw 0x04b5c05503d40f60 0x0f7fe01f03fc0ff0

def z729 : W := mkw 0x04b5c0f503d40f60 0xffffe0ff03ff8fff

def z730 : W := mkw 0x093ef50003faa000 0x0f3ff30003fe7000

def z731 : W := mkw 0x193eff0afbfbe000 0x0fbfff3ffffff000

def z732 : W := mkw 0x490bb558a16aa455 0xffef9cd8e3638c7f

def z733 : W := mkw 0x090ef50003fbe000 0x0f2ffc0003fff000

def z734 : W := mkw 0x013eff0003fa2000 0x0f3fff0003fe7000

def z735 : W := mkw 0x8fb7cef453d1ce42 0xd4278cc063018c03

def z736 : W := mkw 0x093eff0003fbe000 0x052fff00037ff000

def z737 : W := mkw 0x0934eb0003fbe000 0x0f3fe30003fff000

def z738 : W := mkw 0x493eff0003fbe455 0x0f3fff0003fff070

def z739 : W := mkw 0x093e7f0002996000 0x011fe300009c7000

def z740 : W := mkw 0x820000a054001a8a 0xfef01fe0ff83ff8f

def z741 : W := mkw 0x82344aa056815a8a 0xffffffe0ff83ff8f

def z742 : W := mkw 0x11bf7f5ef8000000 0x0d3fff1ffc000000

def z743 : W := mkw 0x150abf0bfbd40f60 0x02401f00fffc0ff0

def z744 : W := mkw 0x193effaafbfbe000 0x0fbfffe0fffff000

def z745 : W := mkw 0x04b5c0f503d40f60 0x035fe03f03fc0ff0

def z746 : W := mkw 0x108b14fef8000000 0x018f80fffc000000

def z747 : W := mkw 0x04b5c0f503d40f60 0xdfffecff63fd8ff3

def z748 : W := mkw 0x0041005bac0411bc 0x20c000fffc0003fc

def z749 : W := mkw 0x093eff0003fbe000 0xdf3fffc063fffc03

def z750 : W := mkw 0x008d715e88000000 0x099ff33f9c000000

def z751 : W := mkw 0x51b4eba659628455 0xf25063271f638c7f

def z752 : W := mkw 0x090ef500017aa000 0x030fe00000fe7000

def z753 : W := mkw 0x0048310b8c2e31bc 0xfbd87f3ffcfff3ff

def z754 : W := mkw 0x080ab50003fbe000 0x0f3fff0003fff000

def z755 : W := mkw 0x090ef50003fbe000 0x0b1ff30003fff000

def z756 : W := mkw 0x04b10af502854f60 0x0ef01fff0383fff0

def z757 : W := mkw 0x003c7100002a2000 0x0f3ff30000fe7000

def z758 : W := mkw 0x0008310b8c0411a8 0x2bd8733f9cfe73fc

def z759 : W := mkw 0x400a940001628455 0xffef9cc0e3638c7f

def z760 : W := mkw 0x118b3ffef8000000 0x0daf9ffffc000000

def z761 : W := mkw 0x11be7fa658000000 0x0dbfffe7fc000000

def z762 : W := mkw 0x4041005bac0415fd 0x20c0003f9c0003fc

def z763 : W := mkw 0x0dbeffa403fbea00 0x0f3fff0003fff000

def z764 : W := mkw 0x93bf7ffef8000a02 0xddbffffffc000c03

def z765 : W := mkw 0x11bf7ffefaab6000 0x0fbffffffffff000

def z766 : W := mkw 0x090eff0003fbe000 0x030fff0003fff000

def z767 : W := mkw 0x8b0ef5a0557aba8a 0xf1cfe0e0fc7c0f8f

def z768 : W := mkw 0x0001005100040120 0x0fffe0ff00fc03f0

def z769 : W := mkw 0x11f74ef5742e31bc 0x26678cc060fe73fc

def z770 : W := mkw 0x4440800107febffd 0xf240000003ffffff

def z771 : W := mkw 0x00bd7bfed8000000 0x0dbffffffc000000

def z772 : W := mkw 0x0d3eff0003fbee40 0x0f3fff0003fffc00

def z773 : W := mkw 0x93f46ba75e8d7baa 0x001063271c9c7380

def z774 : W := mkw 0x0936ef0003d9e000 0x0e37ff00039ff000

def z775 : W := mkw 0x118f755ea8000000 0x0dbffffffc000000

def z776 : W := mkw 0x0040210b8c2e31bc 0x22d0633f9cfe73fc

def z777 : W := mkw 0x04fdf1fe8ffa3edc 0x242793c09f027c0c

def z778 : W := mkw 0x19beffaedbfbe000 0x0fbfff3f9ffff000

def z779 : W := mkw 0x11b56bf658000000 0x0437e3e71c000000

def z780 : W := mkw 0x004021030c0c31a8 0x2bd8733f9cfe73fc

def z781 : W := mkw 0x8685ca55555555ea 0xf10fff1ffc7ff07f

def z782 : W := mkw 0x11bf7ffefa814000 0x0dbffffffc807000

def z783 : W := mkw 0x0936ce0003fbe000 0x0f3fec0003fff000

def z784 : W := mkw 0x108b35fef8000000 0x0dbffffffc000000

def z785 : W := mkw 0x11bf7ffef8000000 0x019fe3fffc000000

def z786 : W := mkw 0x19bf7ffefa996000 0x0fbfffffff9ff000

def z787 : W := mkw 0x00000001040411a8 0x0bd8633f1cfc73f0

def z788 : W := mkw 0x19b4eba65bfbe000 0x021063271ffff000

def z789 : W := mkw 0x8fb46ba5569d7baa 0x001063271c9c7380

def z790 : W := mkw 0x093eff0003fbe000 0x011fff0000fff000

def z791 : W := mkw 0x014a3f0a8c2a309c 0x20001f009c02700c

def z792 : W := mkw 0x493eff0883fbe455 0xffffff1883fffc7f

def z793 : W := mkw 0x09346b0002996000 0x0d3fe300009c7000

def z794 : W := mkw 0x0934eb0003d96000 0x011fe30000fc7000

def z795 : W := mkw 0x093eff0003fbe000 0x0d3fff0000fc7000

def z796 : W := mkw 0x44c100ffac041ffd 0xf0c000fffc000fff

def z797 : W := mkw 0x93bf7ffefa814a02 0xdfffffffff818f83

def z798 : W := mkw 0x11b66fa658000000 0x0437ef271c000000

def z799 : W := mkw 0x11bf7ffef8000000 0x0ffffffffc800380

def z800 : W := mkw 0x8b3eff0053fbe002 0xdf3fff0063fff003

def z801 : W := mkw 0x11b74ef470000000 0x0dbffffffc000000

def z802 : W := mkw 0x8b3effa053fbea02 0x0f3fff0003fff000

def z803 : W := mkw 0x004a350b8c2eb1bc 0x2bd87f3f9cfff3fc

def z804 : W := mkw 0x0009905881620454 0xffef9cd8e3638c7f

def z805 : W := mkw 0x400b9458a1408455 0xfdef9cd8e3018c7f

def z806 : W := mkw 0x1db7cef473d1ce40 0x04278cc063018c00

def z807 : W := mkw 0x11bf7ffef8000000 0x0fbffffffcfc0000

def z808 : W := mkw 0x090abf00016be000 0x0f3fff0003fff000

def z809 : W := mkw 0x093eff0003fbe000 0x0b1ff30000fe7000

def z810 : W := mkw 0x400bb55aa96aa455 0xfffffffffffffc7f

def z811 : W := mkw 0x400b9458a1628455 0xf76f8cd863638c7f

def z812 : W := mkw 0x938f755eae815a8a 0xf34fe01f0383ff8f

def z813 : W := mkw 0x19beffa65bfbe000 0x0fbfffe7fffff000

def z814 : W := mkw 0x004831030c2e31a8 0x0bd8733f1cfe73f0

def z815 : W := mkw 0x04b5c0f503d40f60 0x0dbfe0ff00fc03f0

def z816 : W := mkw 0x400b9458a1628455 0xf52f9cd8e3638c7f

def z817 : W := mkw 0x003cfb0003fb6000 0x0f3fff0003fff000

def z818 : W := mkw 0x093e7f0002996000 0x0f3fff00039ff000

def z819 : W := mkw 0x013eff00016aa000 0x0f3fff0003fff000

def z820 : W := mkw 0x93bf7ffef8014002 0xddbffffffc018003

def z821 : W := mkw 0x15b5caf553d40f60 0x0fffe0ff03fc0ff0

def z822 : W := mkw 0x82783babdaaf6b36 0xd5286cdf637d8c73

def z823 : W := mkw 0x51bf7ffef8000455 0x0dbffffffc000070

def z824 : W := mkw 0x493eff0023fbe001 0xdf3fff0063fff003

def z825 : W := mkw 0x51cff55fa96ea575 0x010fe01f007c0070

def z826 : W := mkw 0x0048310b8c2e31bc 0x21d8633f9cfc73fc

def z827 : W := mkw 0x93b44aa456815a8a 0xfef01fe0ff83ff8f

def z828 : W := mkw 0x004a350aac2a309c 0x20001f00fc02700c

def z829 : W := mkw 0x0485c05501540560 0x01cfe03f007c03f0

def z830 : W := mkw 0x97b7cef473d14e42 0xd4278cc063018c03

def z831 : W := mkw 0x000b9458a1400440 0xffef9cd8e3638c7f

def z832 : W := mkw 0x8e00800107ffffea 0xf240000003ffffff

def z833 : W := mkw 0x01bf7ff450000000 0x0dbffffffc000000

def z834 : W := mkw 0x04b5caf553d54f60 0x0ffffffffffffff0

def z835 : W := mkw 0x19bf7ffefa914000 0x0dbffffffc000000

def z836 : W := mkw 0x093eff0003fbe000 0x072fec0003fff000

def z837 : W := mkw 0x0048310b8c2e31bc 0x2358633f1cfe73fc

def z838 : W := mkw 0x11bf7ffef8000000 0x0437ffe7fc000000

def z839 : W := mkw 0x0936ce0003d1c000 0x0f3fff0003fff000

def z840 : W := mkw 0x094a350b8c2eb1bc 0x2bd8733f9cfe73fc

def z841 : W := mkw 0x8640800107ff7ffe 0xf240000003ffffff

def z842 : W := mkw 0x400b9458a1628455 0xffff9fd8e3e3fc7f

def z843 : W := mkw 0x093effa003fbe000 0x0fbfffe003fff000

def z844 : W := mkw 0x493eff0003fbe015 0xff3fff0003fff00f

def z845 : W := mkw 0x04b5c0f503d40f60 0x0bdfe03f00fc03f0

def z846 : W := mkw 0x404a350aac2ab09d 0x200013009c02700c

def z847 : W := mkw 0x11bf7ffef8220014 0x2dbffffffc02000c

def z848 : W := mkw 0x86b5c0f553d40f62 0xdfffe0ff63fc0ff3

def z849 : W := mkw 0x0401805103d40f60 0x0fffe0ff03fc0ff0

def z850 : W := mkw 0x82344aa056915a8a 0xfef07fe0ff9fff8f

def z851 : W := mkw 0x00c100ff8c0411bc 0x20c000ff9c0003fc

def z852 : W := mkw 0x11bf7ffef8000000 0x0fbfffffff038000

def z853 : W := mkw 0x0934eb0003d96000 0x0f3fff0003fff000

def z854 : W := mkw 0x10b540f658000000 0x0dbfe0ff1c000000

def z855 : W := mkw 0x0034c0a103d40b20 0x0fffe0ff03fc0ff0

def z856 : W := mkw 0x508b945ea9628455 0xffef9cdfe3638c7f

def z857 : W := mkw 0x4003845021628455 0xffef8cd863638c7f

def z858 : W := mkw 0x404bb55aa96aa455 0xffef9cd8e3638c7f

def z859 : W := mkw 0x003180f103c40f60 0x0fffe0ff03fc0ff0

def z860 : W := mkw 0x003b3ffaf8000000 0x0dbffffffc000000

def z861 : W := mkw 0x0d8b3ff5002fef60 0x00c01fff0003fff0

def z862 : W := mkw 0x093eff0003fbe000 0x2fffff0083fff00c

def z863 : W := mkw 0x493eff08a3fbe455 0xff7fff00e3fffc7f

def z864 : W := mkw 0x514a3f0afc2ab09d 0xf0001f00fc03f00f

def z865 : W := mkw 0x59bf7ffef82be015 0xfdbffffffc03f00f

def z866 : W := mkw 0x080a940003fbe000 0x030f800003fff000

def z867 : W := mkw 0x093eff0003fbe000 0x0fffff1803fff070

def z868 : W := mkw 0x01bf7ffe88000000 0x0dbfffff9c000000

def z869 : W := mkw 0x0834c00003fbe000 0x0627800003fff000

def z870 : W := mkw 0x000b145aa8000000 0x0daf9cfffc000000

def z871 : W := mkw 0x11bf75fef8000000 0x0dbfe0fffc000000

def z872 : W := mkw 0x0001805101440560 0x0bdfe03f00fc03f0

def z873 : W := mkw 0x11bf7ffef8000000 0x099ff33f9c000000

def z874 : W := mkw 0x118f7ffef8000000 0x018ffffffc000000

def z875 : W := mkw 0x400b9458a1628455 0xf5ef8cd8e3618c7f

def z876 : W := mkw 0x82300aa056815a8a 0xf4e01fe0ff03ff8f

def z877 : W := mkw 0x0936ef0003d9e000 0x0f3fef0003fdf000

def z878 : W := mkw 0x04b5caf503d54f60 0xffffffffe3ffffff

def z879 : W := mkw 0x400bb558a16aa455 0xffeffcd8e37f8c7f

def z880 : W := mkw 0x003ede0003f3c000 0x0f3fff0003fff000

def z881 : W := mkw 0x40038458a1408455 0xfee79cd8e3038c7f

def z882 : W := mkw 0x093eff0003fbe000 0xff3fff00e3fff00f

def z883 : W := mkw 0x0040210b8c0c31bc 0x2bd8633f9cfc73fc

def z884 : W := mkw 0x86b5caf453d14e42 0x042780c003000c00

def z885 : W := mkw 0x8b3effa053fbea02 0xdfbfffe0fffffc03

def z886 : W := mkw 0x4048310bac2e31bd 0xfbd8733ffcfe73ff

def z887 : W := mkw 0x00bf5efcf0000000 0x0dbffffffc000000

def z888 : W := mkw 0x11bf7ffef8000000 0x2ffffffffc02000c

def z889 : W := mkw 0x0485c0f501540f60 0x010fe03f007c03f0

def z890 : W := mkw 0x0485c0f501540f60 0x0fefe0ff037c0ff0

def z891 : W := mkw 0x11bf5efef8000000 0x0daf9cfffc000000

def z892 : W := mkw 0x003abf0003ebe000 0x0f3fff0003fff000

def z893 : W := mkw 0xc24100fbfc041fff 0xf0c000fffc000fff

def z894 : W := mkw 0x40408001056eb5fd 0x2240000000fe73fc

def z895 : W := mkw 0x82300aa056815a8a 0xfff87fffff83ff8f

def z896 : W := mkw 0x10c100fffc0411a8 0x008000fffc000380

def z897 : W := mkw 0x003c710a88000000 0x0dbff33f9c000000

def z898 : W := mkw 0x093eff0a8bfbe014 0x2fffff3f9ffff07c

def z899 : W := mkw 0x11b46ba658000000 0x0d3fe3271c000000

def z900 : W := mkw 0x0048310b8c2e31bc 0x2ff873ff9ffe7ffc

def z901 : W := mkw 0x093e7f0002bb6000 0x0f3fff0000fe7000

def z902 : W := mkw 0x04b5caf553d40f60 0xffffffffffff8fff

def z903 : W := mkw 0x0040000b8c0411bc 0x2bd8733f9cfe73fc

def z904 : W := mkw 0x968100fffc041fea 0xf0c000fffc000fff

def z905 : W := mkw 0x0800800003fbe000 0x0f2f800003fff000

def z906 : W := mkw 0x093eff0003fbe000 0x0fbfffc0e3fff000

def z907 : W := mkw 0xc600800107f7dfff 0xf240000003ffffff

def z908 : W := mkw 0x00bf75fea8000000 0x0dbffffffc000000

def z909 : W := mkw 0x493eff08a3fbe015 0xffffff18e3fff07f

def z910 : W := mkw 0x93bf7ffefa814a02 0xdfbfffffff83fc03

def z911 : W := mkw 0x11bf7ffefa800000 0x0fbfffffff800000

def z912 : W := mkw 0x193eff0aabfbe000 0x0f3fff0003fff000

def z913 : W := mkw 0x11bf7ffefa800a00 0x0dbfffffff000c00

def z914 : W := mkw 0x494a3f0aac2bf09d 0xf0001f00fc03f00f

def z915 : W := mkw 0x11bf7ffefa900000 0x0dbffffffc9c0000

def z916 : W := mkw 0x10bf54fef8000000 0x0dbffcfffc000000

def z917 : W := mkw 0x0048310b8c2e31bc 0x0bd8633f1cfc73f0

def z918 : W := mkw 0x118744fef8000000 0x008780fffc000000

def z919 : W := mkw 0x013eff0003d14000 0x0f3fff0003fff000

def z920 : W := mkw 0x0936ef0003fbe000 0x0637ef0003fff000

def z921 : W := mkw 0x51bf7ffef8000015 0xfdbffffffc00000f

def z922 : W := mkw 0x11b76ff678000000 0x0dbfefff7c000000

def z923 : W := mkw 0x4003845021408441 0xffef9cd8e3638c7f

def z924 : W := mkw 0x0485c0f501540f60 0x0bdfe0ff00fc0ff0

def z925 : W := mkw 0x010e750a88000000 0x099ff33f9c000000

def z926 : W := mkw 0x8b344aa056915a8a 0xfef01fe0ff83ff8f

def z927 : W := mkw 0x0440800107dc3fe8 0x0240000003fc7ff0

def z928 : W := mkw 0x11bf7ffef8220014 0xffffffffff638c7f

def z929 : W := mkw 0x11bf7ffef8000000 0x0dbfe3ff1c000000

def z930 : W := mkw 0x82300aa056815a8a 0xfff81ff8ffe3ffff

def z931 : W := mkw 0x118f755ef8000000 0x010fe01ffc000000

def z932 : W := mkw 0x4001805001628455 0xffef9cd8e3638c7f

def z933 : W := mkw 0x49356b58a2996455 0xf0d063d8e09c7c7f

def z934 : W := mkw 0x51bf7ffef8000441 0xddbffffffc000c03

def z935 : W := mkw 0x093eff0003fbe000 0x0fbfff209ffff000

def z936 : W := mkw 0x093eff0003fbe014 0x2f7fff0003fff07c

def z937 : W := mkw 0x0400800107d41fe8 0x2240000003fe7ffc

def z938 : W := mkw 0x51bf7ffef8000455 0xffffffffff038c7f

def z939 : W := mkw 0x093e7f0002bbe000 0x0d3fff00009ff000

def z940 : W := mkw 0x013e7f0002ab6000 0x0f3fff0003fff000

def z941 : W := mkw 0x110b3f5af8000000 0x0dbffffffc000000

def z942 : W := mkw 0x013e7faad8000000 0x0dbffffffc000000

def z943 : W := mkw 0x11bf7ffef8000a00 0x0dfffffffc000f80

def z944 : W := mkw 0x44b5c0f523d40f61 0xdfffe0ff63fc0ff3

def z945 : W := mkw 0x04308aa153d40f60 0x0ef01fe0fffc0ff0

def z946 : W := mkw 0x093eff0003fbe000 0x0fffff2003fff380

def z947 : W := mkw 0x10bd71fef8000000 0x0dbff3fffc000000

def z948 : W := mkw 0x013f7f5aa8000000 0x0dbffffffc000000

def z949 : W := mkw 0x97b46ba75e955baa 0x001063271c9c7380

def z950 : W := mkw 0x118f75fef8000000 0x0daffcfffc000000

def z951 : W := mkw 0x400b9458a1628455 0xffff9cf8e3e38fff

def z952 : W := mkw 0x093ede0003fbe000 0x0f2f9c0003fff000

def z953 : W := mkw 0x093e7f00002be000 0x0f3fff0000fff000

def z954 : W := mkw 0x40038458a1628455 0xf6e78cd8e3638c7f

def z955 : W := mkw 0x0048310b8c0c31a8 0x0bd8733f9cfc73f0

def z956 : W := mkw 0x093eff0003fbe000 0x0fbfff3f03fff000

def z957 : W := mkw 0x14c100fffc041ffc 0x20c000fffc000ffc

def z958 : W := mkw 0x19bf7ffef82be000 0x0fbffffffcfff000

def z959 : W := mkw 0x40408001056695fd 0xf240000003638fff

def z960 : W := mkw 0x093eff0883fbe000 0x0fbfff1883fff000

def z961 : W := mkw 0x09366f0002996000 0x0437ef00009c7000

def z962 : W := mkw 0x11be7faef8000000 0x0d3fff27fc000000

def z963 : W := mkw 0x19beff060bfbe000 0x0f3fff0703fff000

def z964 : W := mkw 0x193eff0073fbe000 0x0f3fff0063fff000

def z965 : W := mkw 0x40093158a02a2455 0xfbd873d8e0fe7c7f

def z966 : W := mkw 0x093eff08a3fbe000 0x0f3fff00e3fff000

def z967 : W := mkw 0x0048310b8c2e31bc 0xfbd873fffcfe7fff

def z968 : W := mkw 0x000b355aa8000000 0x099ff33f9c000000

def z969 : W := mkw 0x0034ca0003d14000 0x0f3fe30003fc7000

def z970 : W := mkw 0x11bf7ffef8000000 0x04a79ffffc000000

def z971 : W := mkw 0x0485c05503d40f60 0x0bdfe03f03fc0ff0

def z972 : W := mkw 0x083a9e0003fbe000 0x0f3f9f0003fff000

def z973 : W := mkw 0x11b74efef8000000 0x0dbfecfffc000000

def z974 : W := mkw 0x00b5c0f503d40120 0x0fffe0ff03fc03f0

def z975 : W := mkw 0x04b5c0f503d40f60 0x2ffff0ff83fe0ffc

def z976 : W := mkw 0x04c100f70c041fe8 0x00c000ff1c000ff0

def z977 : W := mkw 0x093effa053fbea00 0x0fffffe0ffffff80

def z978 : W := mkw 0x51bf7ffef8228015 0xfffffffffc63807f

def z979 : W := mkw 0x093effa003fbea00 0x0f3fffc003fffc00

def z980 : W := mkw 0x0048310b8c2e31bc 0x2118733f9cfe73fc

def z981 : W := mkw 0x51bf7ffef8228015 0x0dbffffffc000000

def z982 : W := mkw 0x04b5c0f503d40f60 0x05efe0ff037c0ff0

def z983 : W := mkw 0x11bf7ffefa814000 0x0dbfffffff018000

def z984 : W := mkw 0x04b5caf553d40f60 0x0fffecff63fc0ff0

def z985 : W := mkw 0x11bf7ffefa800a00 0xffffffffff838f8f

def z986 : W := mkw 0x118f7f5ef8000000 0x010fe31f1c000000

def z987 : W := mkw 0x0048310b8c2e31bc 0xfbd8733f9fffffff

def z988 : W := mkw 0x00300a0006815088 0xfef01fe0ff83ff8f

def z989 : W := mkw 0x82300aa056815a8a 0xf6601fc0ff83ff8f

def z990 : W := mkw 0x19beffa453fbe000 0x0f3fff0003fff000

def z991 : W := mkw 0x04b5caf503d40f60 0x0fffffff03fc0ff0

def z992 : W := mkw 0x51bf7ffef8228455 0xfdfffffffc038c7f

def z993 : W := mkw 0x19bf7ffef82aa000 0x0dbffffffc000000

def z994 : W := mkw 0x19beffaefbfbe000 0x0f3fff27fffff000

def z995 : W := mkw 0x82300aa056815a8a 0xfff87fe0ffffff8f

def z996 : W := mkw 0x86b5caf553d54f62 0xfffffcffe3ff8fff

def z997 : W := mkw 0x11bf7ffef8000014 0x2dfffffffc00007c

def z998 : W := mkw 0x8b3eff0003fbea02 0xdf3fff0003fffc03

def z999 : W := mkw 0x00b54af450000000 0x0dbfe3ff1c000000

def z1000 : W := mkw 0x118f7f5ef8000000 0x099fff3ffc000000

def z1001 : W := mkw 0x11bf7ffefa814a00 0x0fffffffff83ff80

def z1002 : W := mkw 0x0936ce0003d9e000 0x04278c00039df000

def z1003 : W := mkw 0x8b4a3f0adc2bf09e 0xf0001f00fc03f00f

def z1004 : W := mkw 0x013e7f0208000000 0x0d3fff271c000000

def z1005 : W := mkw 0x11b56bfef8000000 0x0dbfe3fffc000000

def z1006 : W := mkw 0x8b746ba35e9d7baa 0x001063271c9c7380

def z1007 : W := mkw 0x04b5c0f503d40f60 0x01dfe0ff00fc0ff0

def z1008 : W := mkw 0x10c1005fac0411bc 0x20c0003f9c0003fc

def z1009 : W := mkw 0x82000a005401508a 0xfef01fe0ff83ff8f

def z1010 : W := mkw 0x0035c05103d40560 0x0fffe0ff03fc0ff0

def z1011 : W := mkw 0xc6b7cef473d1ce43 0xd4278cc063018c03

def z1012 : W := mkw 0x108304fef8000000 0x04a78cfffc000000

def z1013 : W := mkw 0x04c1005f8c0415fc 0x20c0003f9c0003fc

def z1014 : W := mkw 0x114a350aac2a309c 0x200013009c02700c

def z1015 : W := mkw 0x093eff0883fbe014 0x2f3fff0083fff00c

def z1016 : W := mkw 0x0485c05501540560 0x034fe01f00fc03f0

def z1017 : W := mkw 0x093eff0883fbe014 0x0f3fff1803fff070

def z1018 : W := mkw 0x00300aa054001088 0xfef01fe0ff83ff8f

def z1019 : W := mkw 0x40410059a40415fd 0xf0c000d8e0000fff

def z1020 : W := mkw 0x00b561f608000000 0x0dbfe3ff1c000000

def z1021 : W := mkw 0x04b5c0f503d40f60 0x076fe0df03fc0ff0

def z1022 : W := mkw 0x0936ce0003fbe000 0x0e379f0003fff000

def z1023 : W := mkw 0x19bf7ffefabb6000 0x0fbffffffcfe7000

def z1024 : W := mkw 0x8b3effa053fbea02 0xffffffc0e3fffc0f

def z1025 : W := mkw 0x094a350a8c2ab09c 0x200013009c02700c

def z1026 : W := mkw 0x8600800107d55fea 0x0240000003fc7ff0

def z1027 : W := mkw 0x004a350a8c2ab09c 0x20001f009c03f00c

def z1028 : W := mkw 0x400b9458a16aa455 0xffef9cd8e3fffc7f

def z1029 : W := mkw 0x400b945021628455 0xff6f9cc063638c7f

def z1030 : W := mkw 0x00b5c0f501440560 0x0fffe0ff03fc0ff0

def z1031 : W := mkw 0x0008310b882e2120 0x0bd8733f9cfe73f0

def z1032 : W := mkw 0x00408001056e35fc 0x2240000003fe7ffc

def z1033 : W := mkw 0x11b56bf658000000 0x011fe33f1c000000

def z1034 : W := mkw 0x0808b10a8bfbe000 0x0b98733f9ffff000

def z1035 : W := mkw 0x04b540f502940b20 0x0fffe0ff00fc03f0

def z1036 : W := mkw 0x003000a006801a88 0xfef01fe0ff83ff8f

def z1037 : W := mkw 0x11bf7ff658000000 0x0dbfffff1c000000

def z1038 : W := mkw 0x493eff08a3fbe015 0xffffffc0e3fffc0f

def z1039 : W := mkw 0x11b76ffef8000000 0x04b7effffc000000

def z1040 : W := mkw 0x004a940b8d6691bc 0x2fef9c3f9f6383fc

def z1041 : W := mkw 0x0434c00103d40f60 0x0fffe03f03fc0ff0

def z1042 : W := mkw 0x0048310b8c2e31bc 0x0998733f9cfc73f0

def z1043 : W := mkw 0x11bf7ffef8000000 0x05afecfffc000000

def z1044 : W := mkw 0x10b54afef8000000 0x0dbffffffc000000

def z1045 : W := mkw 0x0008b100016a2000 0x0f3ff30003fe7000

def z1046 : W := mkw 0x04b5c0f501540f60 0x0dffe0ff007c0ff0

def z1047 : W := mkw 0x400b9458a1628455 0xfffffcd8e3ff8c7f

def z1048 : W := mkw 0x82b540f406815a8a 0xffffe0ff0383ff8f

def z1049 : W := mkw 0x0048310b8c2e31bc 0x0b18733f1cfe73f0

def z1050 : W := mkw 0x11bf7ffef8220014 0x0dbffffffc600070

def z1051 : W := mkw 0x19bf7ffefaabe000 0x0fbfffffff83f000

def z1052 : W := mkw 0x108931fef82a2000 0x0b9873fffcfe7000

def z1053 : W := mkw 0x494ff55ba97ea575 0x010fe01f007c0070

def z1054 : W := mkw 0x93bf7ffefa814a02 0x0dbffffffc000000

def z1055 : W := mkw 0x11b76ff678000000 0x0017e3271c000000

def z1056 : W := mkw 0x19bf7ffefabbe000 0x0dbffffffc9ff000

def z1057 : W := mkw 0x0802840003fbe000 0x06278c0003fff000

def z1058 : W := mkw 0x0906c40003fbe000 0x0207800003fff000

def z1059 : W := mkw 0x004a350bac2e31bc 0x2bd87f3ffcfe73fc

def z1060 : W := mkw 0x86f46ba75e9d7baa 0x001063271c9c7380

def z1061 : W := mkw 0x0085405500040120 0x0bdfe03f00fc03f0

def z1062 : W := mkw 0x118f7f5ef8000000 0x0dafffdffc000000

def z1063 : W := mkw 0x00b540f502840b20 0x0fffe0ff03fc0ff0

def z1064 : W := mkw 0x000cf100017a2000 0x0b1ff30000fe7000

def z1065 : W := mkw 0x11be7fa658000000 0x011fe3271c000000

def z1066 : W := mkw 0x097eff0a8bfbe014 0x0f3fff0003fff000

def z1067 : W := mkw 0x093eff0003fbea00 0x0f7fff0003ffff80

def z1068 : W := mkw 0x51bf7ffef8228015 0xffffffffff038c0f

def z1069 : W := mkw 0x093eff0003fbe000 0x06279f0003fff000

def z1070 : W := mkw 0x000a9400016aa000 0x0f2f9c0003fff000

def z1071 : W := mkw 0x093eff0883fbe014 0xffffffd8e3fffc7f

def z1072 : W := mkw 0x00083101042e31a8 0x2bd8733f9cfe73fc

def z1073 : W := mkw 0x093eff0003fbe440 0x0f7fff0003fffc70

def z1074 : W := mkw 0x108540fef8000000 0x018fe0fffc000000

def z1075 : W := mkw 0x118f75fef8000000 0x099ff3fffc000000

def z1076 : W := mkw 0x11bf7ffef8000000 0xddbfffffff018c03

def z1077 : W := mkw 0x0485c05501540f60 0x014fe01f007c0ff0

def z1078 : W := mkw 0x11b74ef678000000 0x04278ce77c000000

def z1079 : W := mkw 0x0034c00003d14000 0x0f3fe00003fff000

def z1080 : W := mkw 0x11bf7ffef8220000 0x0fbffffffc620000

def z1081 : W := mkw 0x0db5caf503d54f60 0x0fffe0ff03fc0ff0

def z1082 : W := mkw 0x934a3f0afc2b709e 0xf0001f00fc03f00f

def z1083 : W := mkw 0x404a350bac2eb1bd 0x2bd8733f9cfe73fc

def z1084 : W := mkw 0x11bf7ffef82a2000 0x0dbffffffc027000

def z1085 : W := mkw 0x017e7f01042e31bc 0x2f7fff0000fe73fc

def z1086 : W := mkw 0x11bf7ffef8000000 0x011fff3ffc000000

def z1087 : W := mkw 0x000b1458a0220014 0xffef9cd8e3638c7f

def z1088 : W := mkw 0x82000aa056815a8a 0xf2c01fe0ff83ff8f

def z1089 : W := mkw 0x0034400100040120 0x0fffe03f00fc03f0

def z1090 : W := mkw 0x19b56bfefa996000 0x009063fffc9c7000

def z1091 : W := mkw 0x04b5c0f503d40f60 0x0f3fe03f03fc03f0

def z1092 : W := mkw 0x40038458a1408455 0xffef8cd8e3618c7f

def z1093 : W := mkw 0x0804c00003fbe000 0x030fe00003fff000

def z1094 : W := mkw 0x003ef50003faa000 0x0f3fff0003fff000

def z1095 : W := mkw 0x04b5c0f503d40f60 0x0ffff3ff03fe7ff0

def z1096 : W := mkw 0x004021030c0c31a8 0x0118633f1cfc73f0

def z1097 : W := mkw 0x194a3f0afc2bf09c 0x20001f00fc03f00c

def z1098 : W := mkw 0x11bf7f5ea8000000 0x0dbfff3f9c000000

def z1099 : W := mkw 0x50c100fffc0415fd 0xf0c000fffc000fff

def z1100 : W := mkw 0x0cb5c0f503d5cf60 0x0fffe0ff03fd8ff0

def z1101 : W := mkw 0x86b5caf553d54f62 0x0fffe0ff03fc0ff0

def z1102 : W := mkw 0x083cf10003fbe000 0x0f3ff30003fff000

def z1103 : W := mkw 0x86b5caf553d54f62 0xdfffffff63fffff3

def z1104 : W := mkw 0x04b5c0f503d40f60 0x0ffffcff03ff8ff0

def z1105 : W := mkw 0x0009315a88000000 0x0dbff3ff9c000000

def z1106 : W := mkw 0x090abf0003fbe000 0x0f2f9f0003fff000

def z1107 : W := mkw 0x15bf7ffefa900a00 0x0dbffffffc000000

def z1108 : W := mkw 0x093eff020bfbe000 0x0f3fff271ffff000

def z1109 : W := mkw 0x11bf7ffefa800a00 0x0dbffffffc800380

def z1110 : W := mkw 0x013e7f0000082000 0x0d3fff00009c7000

def z1111 : W := mkw 0x108100fef8000000 0x0daf80fffc000000

def z1112 : W := mkw 0x11bf7ffef8000000 0xfdfffffffc000c0f

def z1113 : W := mkw 0x44cff55fa97ea575 0x010fe01f007c0070

def z1114 : W := mkw 0x86b44aa456915a8a 0xfef01fe0ff83ff8f

def z1115 : W := mkw 0x11b56bf658000000 0x0dbffffffc000000

def z1116 : W := mkw 0x8b3effa053fbea02 0xdfffffe063ffff83

def z1117 : W := mkw 0x11bf7ffef8228000 0x0dbffffffc038000

def z1118 : W := mkw 0x04b5c0f553d40f60 0x0fffe0fffffc0ff0

def z1119 : W := mkw 0x04b5c0f503d40f60 0x0ffffcffe3fc0ff0

def z1120 : W := mkw 0x11bd7bfed8000000 0x0dbff3ff9c000000

def z1121 : W := mkw 0x8a40800107fffbbe 0xf240000003ffffff

def z1122 : W := mkw 0x193eff025bfbe000 0x0f3fff001ffff000

def z1123 : W := mkw 0x118f755ea8000000 0x018fe03f9c000000

def z1124 : W := mkw 0xc240800107efffff 0xf240000003ffffff

def z1125 : W := mkw 0x404a350bac2eb1bd 0xfff87fffffffffff

def z1126 : W := mkw 0x19bf7ffef8096000 0x0dbffffffc007000

def z1127 : W := mkw 0x004a350b8c2e31bc 0x2fffff3f9cfe73fc

def z1128 : W := mkw 0x493eff0003fbe455 0xffffffc0e3fffc7f

def z1129 : W := mkw 0x04b5c0f501540560 0x0fffe0ff00fc03f0

def z1130 : W := mkw 0x04b5caf553d40f60 0x0fffe3ff1ffc0ff0

def z1131 : W := mkw 0x82000a0056815a8a 0xfee01fc0ff83ff8f

def z1132 : W := mkw 0x00b540f450000000 0x0dbfe0fffc000000

def z1133 : W := mkw 0x010e7500002a2000 0x0b1ff30000fe7000

def z1134 : W := mkw 0x11be7faed8000000 0x0dbfff3f9c000000

def z1135 : W := mkw 0x0840800107fff1a8 0x0200000003fff380

def z1136 : W := mkw 0x000b945001628440 0xffef9cd8e3638c7f

def z1137 : W := mkw 0x083ed40003fbe000 0x0f3ffc0003fff000

def z1138 : W := mkw 0x0834c00003d96000 0x0f3fe00003fc7000

def z1139 : W := mkw 0x868100f504041fea 0xf0c000ff00000fff

def z1140 : W := mkw 0x093eff0003fbe000 0x0437ff00039ff000

def z1141 : W := mkw 0x82300aa056815a8a 0xf4301fe0ff83ff8f

def z1142 : W := mkw 0x0934eb0003d96000 0x0437e300039c7000

def z1143 : W := mkw 0x400b9458a1628455 0xffff9ff8ff638c7f

def z1144 : W := mkw 0x11bf7ffef8000000 0x053fefff7c000000

def z1145 : W := mkw 0x00b540f400000000 0x0dbff3ff9c000000

def z1146 : W := mkw 0x400b1458a0000455 0xffef9cd8e3038c7f

def z1147 : W := mkw 0x11ff7ffef82a2014 0x0dbffffffc000000

def z1148 : W := mkw 0x86b5caf553d54f62 0xdffffffffffd8ff3

def z1149 : W := mkw 0x11b76ff678000000 0x0cb7ffe7fc000000

def z1150 : W := mkw 0x000ab500016aa000 0x0b1ff30000fe7000

def z1151 : W := mkw 0x400b9458a1628455 0xfffffcffe3638c7f

def z1152 : W := mkw 0x82b44aa456815a8a 0xfef07fe7ff83ff8f

def z1153 : W := mkw 0x093effa053fbe000 0xffffffe0fffffc0f

def z1154 : W := mkw 0x093eff0053fbe000 0x0f3fff00fffff000

def z1155 : W := mkw 0x11bf7ffef8000000 0x052fffdffc000000

def z1156 : W := mkw 0x090ef500017be000 0x010fe000007ff000

def z1157 : W := mkw 0x09beffa403fbe000 0x0f3fff2703fff000

def z1158 : W := mkw 0x508180fef9628455 0xf2c000ffff638c7f

def z1159 : W := mkw 0x04b5c0f503d40f60 0xffffe0ffe3fc0fff

def z1160 : W := mkw 0x19bf7ffef801c000 0x0dbffffffc018000

def z1161 : W := mkw 0x00b540fe88000000 0x0dbfe0ff9c000000

def z1162 : W := mkw 0x017e7f0b8c0411bc 0x2dffff3f9c0003fc

def z1163 : W := mkw 0x04b4c0a503d40b20 0x0fffe03f03fc03f0

def z1164 : W := mkw 0x090ef500017aa000 0x011fe30000fc7000

def z1165 : W := mkw 0x048180f501440f60 0x0fffe0ff03fc0ff0

def z1166 : W := mkw 0x15bf7ffef8000e40 0x0dbffffffc000c00

def z1167 : W := mkw 0x10b540fef8000000 0x04a780fffc000000

def z1168 : W := mkw 0x11bf75fea8000000 0x0dbff3ff9c000000

def z1169 : W := mkw 0x04b5c05503d40560 0x0fffe03f03fc03f0

def z1170 : W := mkw 0x093effaadbfbe000 0x0fbffffffffff000

def z1171 : W := mkw 0x093effa003fbea00 0x0f3fff2003fff380

def z1172 : W := mkw 0x4003845021628455 0xfee79cc0e3638c7f

def z1173 : W := mkw 0x14b5c0f573d40f60 0x0fffe0ff63fc0ff0

def z1174 : W := mkw 0x93bf7ffefa814a02 0xffffffffff038c0f

def z1175 : W := mkw 0x4048310b8c2eb1bd 0xfbd8733f9cfff3ff

def z1176 : W := mkw 0x090eff00017be000 0x010fe300007c7000

def z1177 : W := mkw 0x11bf7ffefa814000 0xffffffffff83fc0f

def z1178 : W := mkw 0x0034e10003d82000 0x0f3fe30003fc7000

def z1179 : W := mkw 0x11bf7ffef82a2014 0x2ffffffffcfe707c

def z1180 : W := mkw 0x400b945aa9628455 0xffef9cffff638c7f

def z1181 : W := mkw 0x11bf7ffef8000000 0x0fbffffffc827000

def z1182 : W := mkw 0x0440800107d41ffc 0x2240000003fc0ffc

def z1183 : W := mkw 0x4008b10a89628455 0xfbd8733f9f638c7f

def z1184 : W := mkw 0x400b9458a1628455 0xf4e79cd8e3038c7f

def z1185 : W := mkw 0x92c100fffc041bbe 0xf0c000fffc000fff

def z1186 : W := mkw 0x0c40800107fffffc 0x2240000003fffffc

def z1187 : W := mkw 0x00081009842611bc 0x2bd8733f9cfe73fc

def z1188 : W := mkw 0x493eff08a3fbe015 0x0f3fff0003fff000

def z1189 : W := mkw 0x51bf7ffef8008001 0xddbffffffc018003

def z1190 : W := mkw 0x0834ca0003fbe000 0x0f3fff0003fff000

def z1191 : W := mkw 0x000a350a88000000 0x0dbfff3f9c000000

def z1192 : W := mkw 0x400bb558a16aa455 0xffef9fd8e363fc7f

def z1193 : W := mkw 0x11bf7ffef8082000 0x0dbffffffc9c7000

def z1194 : W := mkw 0x0034c00003d00000 0x0f3ff30003fe7000

def z1195 : W := mkw 0x8234c0a057d01a8a 0xffffe0e0fffc0f8f

def z1196 : W := mkw 0x48018058a3fbe455 0xf2c000d8e3fffc7f

def z1197 : W := mkw 0x004b1459a42e31bc 0x2fef9cd8e0fe73fc

def z1198 : W := mkw 0x093effa053fbe000 0x0f3fffc063fff000

def z1199 : W := mkw 0xc68100fdf4041fff 0xf0c000fffc000fff

def z1200 : W := mkw 0x000a3500002a2000 0x0f3fff0000fe7000

def z1201 : W := mkw 0x093eff0003d96000 0x0f3fff0003fc7000

def z1202 : W := mkw 0x480b9458a17aa455 0xffef9cd8e37f8c7f

def z1203 : W := mkw 0x0048310b8c2e31bc 0x2ff87ffffcfe73fc

def z1204 : W := mkw 0x090ef500017aa000 0x010ff300007e7000

def z1205 : W := mkw 0x00400001042e31bc 0x2bd8733f9cfe73fc

def z1206 : W := mkw 0x510bb55aa9628455 0xffef9cd8e3638c7f

def z1207 : W := mkw 0x4003845021408455 0xf4678cc063018c7f

def z1208 : W := mkw 0x00408001056eb1bc 0x2240000003fff3fc

def z1209 : W := mkw 0x04b5c0f503d54f60 0x0fffe0ff03fffff0

def z1210 : W := mkw 0x118f755ea8000000 0x011fe33f1c000000

def z1211 : W := mkw 0x86c100ffdc041ffe 0xf0c000fffc000fff

def z1212 : W := mkw 0x400bb558a1628455 0xffffffd8e3638c7f

def z1213 : W := mkw 0x090ef500017aa000 0x0f3fff0003fff000

def z1214 : W := mkw 0x40018058a1400455 0xffef9cd8e3638c7f

def z1215 : W := mkw 0x114a350bac2e31bc 0x2bd8733f9cfe73fc

def z1216 : W := mkw 0x11bf7ffef8000000 0x0d3fff3f1c000000

def z1217 : W := mkw 0x08408001057eb1bc 0x2240000000fe73fc

def z1218 : W := mkw 0x090ef50003fbe000 0x010fe00000fc7000

def z1219 : W := mkw 0x093ef50003fbe000 0x0f3fe00003fff000

def z1220 : W := mkw 0x093cfb0003fb6000 0x0f3ff30003fe7000

def z1221 : W := mkw 0x093effa003fbea00 0xffffffe0e3ffff8f

def z1222 : W := mkw 0x0485c05503d40f60 0x010fe01f00fc03f0

def z1223 : W := mkw 0x0485c05503d40f60 0x0fefe0df03fc0ff0

def z1224 : W := mkw 0x118f755ea8000000 0x010ff31f9c000000

def z1225 : W := mkw 0x04b540f500040f60 0x0fffe0ff00fc0ff0

def z1226 : W := mkw 0x82000aa054015a8a 0xfee01fe0ff03ff8f

def z1227 : W := mkw 0x11bf7ffef8000000 0xfdbffffffc03800f

def z1228 : W := mkw 0x0048310b8c2e31bc 0x2ff87f3f9ffff3fc

def z1229 : W := mkw 0x093effa053fbe000 0x0f3fff201ffff000

def z1230 : W := mkw 0x11bf7ffef8000000 0x0ffffffffc600070

def z1231 : W := mkw 0x51bf7ffef8220455 0xfffffffffc620c7f

def z1232 : W := mkw 0x44b5c0f503d48f61 0xdfffe0ff03fd8ff3

def z1233 : W := mkw 0x0000800101440120 0x0fffe03f03fc03f0

def z1234 : W := mkw 0x11bf7ffef82a2000 0x0dbffffffc7c0000

def z1235 : W := mkw 0x093eff0003fbe000 0x053fef0003fdf000

def z1236 : W := mkw 0x0041005b8c0415fc 0x20c000ff9c000ffc

def z1237 : W := mkw 0x090eff00017be000 0x0f2fff00037ff000

def z1238 : W := mkw 0x093eff0003d9e000 0x0d3fff00039df000

def z1239 : W := mkw 0x0485c0f503d40f60 0x03cfe0ff03fc0ff0

def z1240 : W := mkw 0x86b5c0f503d54f62 0xdfffe0ff03fd8ff3

def z1241 : W := mkw 0x113e7f0af8000000 0x0dbfff3ffc000000

def z1242 : W := mkw 0x04b5caf503d54f60 0x0fffe3ff03fc7ff0

def z1243 : W := mkw 0x8200000006815a8a 0xfef01fe0ff83ff8f

def z1244 : W := mkw 0x8600800107d41fea 0xf240000003fc0fff

def z1245 : W := mkw 0x868100f554041fea 0x00c000ff1c000ff0

def z1246 : W := mkw 0x11bf7ff678000000 0x0d3fffe77c000000

def z1247 : W := mkw 0x493eff0003fbe441 0xdf3fff0003fffc03

def z1248 : W := mkw 0x0485c05501540560 0x0fffe0ff03fc0ff0

def z1249 : W := mkw 0x0485c05501540560 0x011fe03f00fc03f0

def z1250 : W := mkw 0x093eff0003fbe000 0x031fe30003fff000

def z1251 : W := mkw 0x04b5caf503d54f60 0x0fffecff03fd8ff0

def z1252 : W := mkw 0x0936ef0003d9e000 0x0017e300009c7000

def z1253 : W := mkw 0x093eff0003fbe000 0x0f3fe30003fc7000

def z1254 : W := mkw 0x118f75fef8000000 0x010fe03f1c000000

def z1255 : W := mkw 0x093eff0a8bfbe000 0x0f3fff009ffff000

def z1256 : W := mkw 0x400bb55aa9628455 0xffef9fd8ff638c7f

def z1257 : W := mkw 0x0034c00003fa2000 0x0f3fe00003fe7000

def z1258 : W := mkw 0x04b5c0f503d40f60 0x053fe0ff03fc0ff0

def z1259 : W := mkw 0x19bf7ffef8182000 0x0dbffffffc1c0000

def z1260 : W := mkw 0x093eff0003fbe000 0xff7fff0003fffc0f

def z1261 : W := mkw 0x11bf7ffef8014000 0x0dbffffffc03f000

def z1262 : W := mkw 0x093eff00017be000 0x0d3fff00007ff000

def z1263 : W := mkw 0x0004c00101540120 0x0bdfe03f00fc03f0

def z1264 : W := mkw 0x093eff00017aa000 0x0f3fff0000fe7000

def z1265 : W := mkw 0x11bf7ffef8000440 0x0dfffffffc000c70

def z1266 : W := mkw 0x400bb55aa9628455 0xffeffcdfe3638c7f

def z1267 : W := mkw 0x10bb1efef8000000 0x0dbf9ffffc000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z8,z2,z3,z9,z6]),(0,[z10,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z11,z6]),(1,[z12,z0,z8,z2,z3,z13]),(0,[z12,z0,z8,z2,z3,z6,z13])],[(0,[z0,z8,z2,z3,z5,z14,z6]),(0,[z0,z8,z2,z3,z5,z15,z6]),(0,[z0,z8,z16,z3,z5,z17,z6])],[(0,[z0,z18,z8,z2,z3,z5,z6]),(1,[z0,z8,z19,z2,z5,z6]),(0,[z0,z8,z20,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z21,z5,z6]),(0,[z0,z22,z23,z2,z3,z5,z6]),(0,[z24,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z25,z2,z26,z5,z6]),(0,[z27,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z28]),(0,[z12,z0,z8,z2,z3,z29,z6]),(0,[z0,z8,z2,z3,z5,z6,z30])],[(0,[z0,z8,z2,z31,z3,z5,z6]),(1,[z0,z8,z32,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z33,z6]),(0,[z0,z8,z34,z2,z3,z5,z6])],[(0,[z0,z8,z2,z35,z3,z5,z6]),(0,[z36,z0,z8,z2,z3,z5,z6])],[(0,[z0,z37,z8,z2,z3,z5,z6]),(0,[z0,z8,z38,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z39,z6]),(0,[z0,z8,z2,z3,z5,z6,z40]),(0,[z12,z0,z41,z8,z2,z3,z6]),(1,[z42,z0,z8,z3,z5,z43]),(0,[z0,z8,z2,z3,z5,z6,z44]),(0,[z0,z8,z45,z2,z3,z5,z46]),(0,[z47,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z48,z49,z5,z6]),(0,[z0,z8,z2,z3,z50,z5,z6]),(1,[z0,z8,z2,z51,z49,z6]),(0,[z0,z8,z2,z3,z29,z5,z13])],[(0,[z0,z8,z2,z3,z5,z52,z6]),(0,[z0,z8,z53,z2,z51,z5,z6]),(0,[z0,z8,z2,z51,z3,z5,z6]),(0,[z54,z0,z8,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z2,z55,z3,z5,z6]),(0,[z0,z8,z2,z3,z49,z56,z6]),(0,[z0,z8,z2,z3,z5,z57,z6]),(1,[z0,z8,z3,z5,z6,z58]),(0,[z0,z8,z2,z59,z3,z5,z6])],[(0,[z60,z0,z8,z2,z3,z5,z6]),(0,[z61,z0,z8,z2,z3,z5,z6]),(0,[z62,z8,z2,z3,z5,z56,z6]),(0,[z0,z8,z2,z3,z5,z63,z56]),(0,[z0,z8,z2,z64,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z65]),(0,[z0,z8,z2,z66,z3,z5,z6]),(0,[z42,z0,z8,z45,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z67,z6]),(0,[z0,z8,z68,z2,z3,z5,z6])],[(0,[z69,z0,z8,z2,z3,z5,z6]),(0,[z70,z8,z71,z2,z3,z5,z6]),(0,[z0,z8,z45,z3,z72,z5,z6]),(0,[z73,z0,z8,z74,z3,z5,z6])],[(1,[z0,z8,z2,z75,z5,z6]),(0,[z0,z76,z8,z3,z72,z5,z6]),(0,[z0,z22,z8,z2,z3,z5,z6]),(0,[z77,z8,z2,z3,z5,z6,z78]),(0,[z0,z8,z2,z3,z79,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z80]),(0,[z81,z0,z8,z3,z5,z6,z78]),(0,[z0,z8,z2,z3,z82,z5,z6])],[(0,[z83,z0,z76,z8,z3,z5,z6]),(0,[z0,z8,z84,z2,z3,z5,z6]),(0,[z85,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z86,z6])],[(0,[z0,z87,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z88,z6]),(0,[z0,z89,z8,z2,z3,z5,z6]),(0,[z90,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z91,z5,z86,z6])],[(0,[z83,z0,z8,z2,z3,z5,z6]),(0,[z92,z0,z8,z45,z3,z5,z6]),(0,[z93,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z94,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z95])]],
   [[(1,[z0,z96,z2,z3,z5,z6]),(0,[z0,z8,z2,z97,z3,z5,z6]),(1,[z0,z22,z2,z4,z5,z6]),(0,[z0,z8,z2,z98,z3,z5,z6])],[(0,[z83,z92,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z99,z5,z6]),(0,[z0,z100,z8,z2,z3,z5,z6])],[(0,[z0,z8,z101,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z102,z5,z6]),(1,[z0,z8,z2,z3,z5,z63]),(0,[z0,z2,z94,z3,z5,z6,z78]),(0,[z0,z8,z2,z103,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z104])],[(1,[z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z105,z3,z5,z6]),(0,[z106,z0,z8,z2,z3,z5,z17]),(0,[z0,z76,z2,z3,z5,z6,z78]),(0,[z0,z1,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z107]),(0,[z0,z8,z53,z48,z3,z5,z6]),(0,[z0,z8,z2,z108,z5,z109,z6]),(1,[z0,z110,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z111,z6]),(1,[z0,z8,z112,z3,z5,z6]),(0,[z0,z8,z25,z3,z108,z5,z6]),(0,[z42,z0,z113,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z114,z6]),(0,[z0,z8,z2,z3,z5,z115,z6])],[(0,[z92,z0,z116,z8,z3,z5,z6]),(0,[z0,z8,z117,z2,z3,z5,z6]),(0,[z0,z8,z2,z118,z3,z5,z6]),(0,[z0,z8,z2,z119,z108,z5,z6])],[(0,[z0,z8,z2,z3,z5,z120,z6])],[(0,[z0,z121,z8,z71,z2,z5,z6]),(0,[z106,z0,z8,z2,z3,z29,z5]),(0,[z122,z0,z1,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z108,z5,z6]),(0,[z123,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z124])]],
   [[(0,[z125,z0,z8,z2,z3,z5,z6])],[(0,[z126,z0,z127,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z128]),(1,[z0,z8,z3,z5,z6,z129]),(1,[z0,z8,z2,z5,z130,z6])],[(0,[z0,z8,z2,z3,z5,z6,z6]),(0,[z0,z8,z2,z3,z5,z131,z6]),(0,[z0,z8,z2,z51,z3,z86,z6])],[(0,[z0,z132,z8,z2,z3,z5,z6]),(0,[z133,z0,z8,z2,z3,z5,z6]),(0,[z0,z134,z8,z2,z3,z5,z6]),(0,[z0,z8,z135,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z136,z6]),(0,[z127,z8,z71,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z137,z5,z6]),(0,[z138,z0,z8,z2,z91,z5,z6]),(0,[z42,z139,z0,z8,z3,z5,z6]),(0,[z0,z8,z140,z2,z97,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z141])],[(0,[z0,z8,z2,z142,z3,z5,z6]),(0,[z143,z0,z8,z2,z3,z5,z17]),(0,[z0,z8,z2,z3,z144,z5,z6]),(0,[z145,z0,z8,z25,z3,z5,z6]),(0,[z0,z146,z8,z2,z3,z5,z6])],[(0,[z147,z148,z0,z8,z2,z5,z6]),(0,[z149,z0,z8,z2,z3,z5,z6]),(1,[z0,z150,z8,z2,z5,z6]),(0,[z0,z8,z2,z151,z3,z5,z6])],[]],
   [[(0,[z0,z8,z152,z2,z3,z5,z6]),(0,[z153,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z154,z3,z72,z5,z6]),(0,[z0,z155,z8,z2,z3,z5,z6])],[(0,[z62,z0,z8,z2,z156,z5,z6]),(0,[z143,z0,z8,z2,z3,z29,z5]),(0,[z0,z8,z2,z3,z5,z157,z6]),(0,[z0,z8,z2,z3,z5,z158,z6])],[(0,[z0,z8,z2,z48,z105,z5,z6]),(0,[z0,z1,z41,z2,z3,z5,z6]),(0,[z0,z159,z8,z2,z3,z5,z6])],[(0,[z0,z8,z19,z2,z3,z5,z6]),(0,[z0,z8,z160,z2,z3,z5,z6]),(0,[z12,z0,z8,z2,z161,z5,z6])],[(0,[z162,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z163,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z164]),(0,[z145,z0,z8,z3,z5,z165,z6]),(1,[z0,z8,z74,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z166])],[(0,[z0,z8,z2,z3,z5,z167,z6]),(0,[z0,z8,z2,z3,z168,z5,z6]),(0,[z0,z8,z2,z3,z5,z169,z6]),(0,[z0,z8,z2,z3,z72,z5,z6]),(0,[z0,z8,z2,z3,z5,z170,z6]),(0,[z0,z8,z171,z2,z3,z5,z6])],[(0,[z70,z7,z0,z2,z3,z5,z6]),(0,[z147,z138,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z172,z6]),(0,[z0,z8,z2,z3,z173,z5,z6]),(0,[z0,z8,z174,z2,z3,z5,z6]),(1,[z0,z8,z175,z3,z5,z6])],[(0,[z148,z0,z8,z2,z48,z5,z6]),(0,[z176,z0,z8,z2,z3,z5,z6]),(0,[z0,z113,z8,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z177,z2,z3,z5,z6]),(0,[z0,z178,z8,z2,z3,z5,z6]),(0,[z0,z179,z8,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z17,z6,z128]),(0,[z0,z8,z2,z3,z5,z180,z6]),(0,[z0,z8,z2,z181,z3,z5,z6]),(1,[z0,z8,z2,z5,z6,z182]),(0,[z183,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z184]),(0,[z185,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z186,z3,z72,z5,z6]),(0,[z139,z0,z8,z94,z3,z5,z6]),(0,[z139,z0,z8,z3,z5,z46,z6]),(0,[z0,z8,z2,z3,z5,z6,z187])],[(0,[z0,z8,z3,z5,z6,z58,z78]),(0,[z0,z8,z2,z3,z188,z5,z6])],[(0,[z0,z23,z2,z103,z3,z5,z6]),(0,[z0,z23,z8,z2,z5,z189,z6]),(0,[z0,z8,z53,z2,z5,z86,z6]),(0,[z190,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z191,z5,z6]),(0,[z7,z0,z2,z3,z5,z169,z6]),(0,[z0,z2,z3,z9,z5,z169,z6]),(0,[z0,z8,z2,z3,z5,z192,z6]),(0,[z0,z8,z2,z3,z193,z5,z6]),(0,[z0,z8,z2,z3,z5,z194,z6])],[(1,[z0,z8,z195,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z196,z6])],[(1,[z162,z0,z2,z3,z5,z6]),(1,[z0,z76,z140,z3,z5,z6]),(0,[z0,z8,z2,z197,z3,z5,z6]),(1,[z0,z8,z198,z3,z5,z6])],[(1,[z0,z8,z2,z199,z5,z6]),(0,[z0,z8,z2,z3,z5,z200,z6]),(0,[z0,z8,z2,z3,z5,z201,z6])]],
   [[(0,[z0,z8,z2,z202,z3,z5,z6])],[(0,[z0,z8,z16,z2,z3,z5,z6]),(0,[z203,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z204,z3,z5,z6]),(0,[z83,z0,z8,z3,z5,z6,z43]),(1,[z92,z8,z186,z3,z5,z6]),(0,[z147,z0,z8,z2,z205,z5,z6]),(1,[z206,z8,z2,z3,z207,z6]),(0,[z0,z8,z2,z3,z208,z5,z6]),(1,[z0,z8,z2,z209,z5,z6])],[(0,[z0,z8,z2,z51,z205,z5,z6]),(0,[z210,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z72,z49,z5,z6]),(0,[z0,z8,z25,z3,z5,z6,z43]),(0,[z12,z0,z8,z2,z3,z5,z211])],[(0,[z212,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z213,z3,z5,z6]),(0,[z0,z155,z8,z3,z205,z5,z6]),(0,[z122,z0,z8,z214,z3,z5,z6]),(0,[z0,z8,z2,z215,z3,z5,z6]),(0,[z0,z8,z2,z3,z161,z5,z6])],[(0,[z139,z126,z0,z2,z3,z5,z6]),(0,[z0,z8,z216,z2,z3,z5,z6]),(1,[z217,z0,z8,z2,z5,z6]),(0,[z0,z8,z2,z218,z3,z5,z6]),(0,[z0,z8,z2,z3,z219,z5,z6])],[(0,[z220,z0,z8,z2,z3,z5,z6])],[(0,[z61,z0,z8,z71,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z221,z6]),(0,[z0,z8,z45,z94,z3,z5,z6]),(0,[z222,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z223,z6]),(0,[z0,z8,z45,z3,z5,z46,z6])]],
   [[(0,[z0,z8,z2,z3,z224,z5,z6]),(1,[z0,z8,z2,z225,z5,z6]),(0,[z0,z8,z2,z3,z5,z226,z6]),(0,[z0,z76,z8,z94,z3,z5,z6]),(0,[z0,z76,z8,z3,z5,z46,z6]),(0,[z0,z8,z2,z3,z5,z6,z227]),(0,[z0,z8,z2,z3,z5,z6,z228])],[(0,[z229,z0,z8,z2,z3,z5,z6]),(0,[z12,z0,z8,z2,z230,z5,z6])],[(0,[z231,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z232]),(0,[z138,z0,z8,z2,z49,z5,z6]),(0,[z0,z96,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z233,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z234])],[(0,[z235,z0,z8,z2,z3,z5,z6]),(1,[z106,z8,z2,z3,z5,z17]),(0,[z0,z8,z2,z3,z5,z236,z6]),(0,[z237,z0,z8,z2,z3,z6,z78]),(0,[z0,z8,z2,z3,z5,z165,z6]),(0,[z0,z8,z2,z3,z238,z5,z6])],[(0,[z0,z8,z2,z3,z239,z5,z6]),(0,[z0,z8,z2,z3,z56,z165,z6]),(0,[z0,z8,z2,z3,z5,z240,z6])],[(0,[z0,z8,z2,z3,z5,z241,z6]),(1,[z0,z8,z3,z242,z5,z6]),(0,[z0,z8,z2,z3,z5,z243,z6]),(0,[z0,z8,z244,z2,z3,z5,z6]),(0,[z0,z8,z245,z2,z3,z5,z6]),(1,[z0,z8,z2,z3,z29,z211])],[(0,[z0,z8,z2,z246,z3,z5,z6]),(0,[z0,z8,z2,z247,z3,z5,z6]),(0,[z0,z23,z8,z2,z4,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z248]),(0,[z0,z8,z2,z249,z3,z5,z6]),(0,[z0,z8,z2,z91,z3,z5,z189])],[(1,[z250,z0,z2,z3,z5,z6]),(0,[z0,z8,z251,z2,z3,z5,z6]),(0,[z0,z8,z2,z252,z3,z5,z6]),(0,[z0,z8,z2,z253,z3,z5,z6]),(0,[z42,z0,z8,z2,z3,z5,z46])]],
   [[(0,[z0,z8,z2,z254,z3,z5,z6]),(0,[z106,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z255,z5,z6]),(0,[z0,z116,z8,z2,z48,z5,z6]),(0,[z256,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z257,z2,z3,z5,z6]),(1,[z258,z8,z2,z3,z5,z6])],[(0,[z106,z0,z8,z2,z3,z5,z259]),(0,[z0,z260,z8,z2,z3,z5,z6]),(0,[z261,z0,z8,z2,z3,z5,z6])],[(0,[z262,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z263,z3,z5,z6]),(0,[z264,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z265,z5,z6]),(0,[z73,z0,z266,z2,z3,z5,z6]),(0,[z0,z8,z2,z91,z3,z5,z187])],[(0,[z0,z8,z2,z3,z5,z267,z6]),(0,[z268,z0,z8,z2,z3,z5,z6]),(0,[z269,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z270,z3,z5,z6]),(0,[z0,z8,z53,z2,z72,z5,z6]),(0,[z0,z8,z271,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z272,z5,z6])],[(1,[z0,z273,z2,z3,z5,z6]),(1,[z0,z8,z2,z5,z6,z274])],[(0,[z0,z8,z2,z3,z5,z6,z275])],[(0,[z138,z0,z22,z8,z2,z5,z6]),(1,[z0,z8,z3,z5,z33,z6]),(0,[z0,z8,z2,z3,z5,z276,z6])],[(0,[z138,z8,z2,z105,z3,z5,z6]),(0,[z0,z8,z2,z277,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z278]),(0,[z0,z8,z2,z3,z5,z6,z279])]],
   [[(0,[z70,z0,z2,z103,z3,z5,z6]),(0,[z0,z8,z2,z3,z280,z5,z6]),(1,[z138,z8,z2,z105,z5,z6]),(0,[z0,z8,z281,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z78]),(0,[z0,z8,z2,z282,z3,z5,z6]),(1,[z0,z8,z2,z26,z5,z6]),(0,[z0,z8,z283,z2,z3,z5,z6]),(0,[z12,z0,z8,z284,z3,z5,z6])],[(0,[z0,z2,z254,z154,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z285]),(0,[z0,z8,z2,z286,z3,z5,z6]),(0,[z0,z8,z2,z3,z287,z5,z6])],[(0,[z0,z8,z2,z3,z288,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z289]),(0,[z0,z8,z2,z3,z108,z207,z6]),(0,[z143,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z290,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z291,z6]),(0,[z81,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z48,z3,z72,z5,z6]),(0,[z0,z292,z8,z2,z3,z5,z6]),(0,[z148,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z293,z6]),(1,[z0,z8,z55,z3,z5,z6]),(1,[z8,z2,z3,z5,z6,z294]),(0,[z0,z8,z2,z3,z5,z6,z295]),(0,[z0,z8,z2,z3,z296,z5,z6]),(0,[z0,z8,z2,z3,z5,z297,z6])],[(0,[z0,z8,z2,z3,z5,z298,z6]),(0,[z83,z0,z8,z48,z3,z5,z6]),(0,[z0,z8,z195,z2,z3,z5,z6]),(0,[z0,z8,z140,z45,z3,z5,z6]),(0,[z0,z8,z2,z4,z5,z6,z187])],[(0,[z0,z8,z2,z3,z5,z299,z6]),(0,[z0,z8,z25,z48,z3,z5,z6])],[(0,[z139,z0,z8,z25,z3,z5,z6]),(0,[z0,z23,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z300,z6]),(0,[z0,z8,z2,z301,z3,z5,z6]),(0,[z0,z302,z8,z2,z3,z5,z6]),(0,[z303,z0,z8,z2,z3,z5,z6]),(0,[z42,z0,z8,z2,z3,z5,z43]),(0,[z73,z0,z8,z2,z91,z5,z6]),(0,[z0,z8,z2,z3,z5,z304,z6])],[(0,[z0,z8,z2,z3,z305,z5,z6]),(1,[z306,z8,z2,z3,z5,z6]),(0,[z0,z307,z8,z2,z3,z5,z6])]],
   [[(0,[z0,z0,z8,z2,z3,z5,z6]),(0,[z0,z41,z8,z2,z3,z9,z6]),(0,[z0,z150,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z48,z3,z5,z6])],[(0,[z147,z0,z8,z20,z3,z5,z6]),(0,[z308,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z309,z2,z3,z5,z6]),(0,[z8,z2,z3,z5,z17,z6,z259]),(0,[z145,z0,z8,z53,z3,z5,z6]),(0,[z0,z8,z25,z2,z3,z165,z6]),(0,[z0,z310,z8,z2,z3,z5,z6])],[(0,[z145,z92,z0,z8,z3,z5,z6]),(1,[z62,z8,z2,z3,z56,z6]),(0,[z8,z2,z3,z207,z5,z56,z6]),(0,[z0,z23,z1,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z46,z6]),(0,[z0,z8,z2,z3,z5,z189,z6]),(0,[z311,z0,z8,z2,z3,z5,z6]),(0,[z312,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z313,z6]),(0,[z126,z0,z71,z2,z3,z5,z6]),(0,[z0,z8,z3,z5,z33,z56,z6]),(0,[z0,z8,z103,z3,z242,z5,z6]),(0,[z0,z8,z2,z199,z3,z5,z6]),(0,[z0,z8,z2,z91,z5,z189,z6]),(0,[z0,z8,z2,z3,z5,z6,z13])],[(0,[z126,z127,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z314]),(0,[z315,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z316,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z317])],[(0,[z318,z0,z8,z2,z3,z5,z6]),(0,[z92,z0,z8,z186,z3,z5,z6]),(0,[z0,z8,z319,z2,z3,z5,z6]),(0,[z0,z8,z320,z2,z3,z5,z6]),(0,[z139,z0,z8,z3,z5,z165,z6]),(0,[z0,z8,z2,z3,z321,z5,z6]),(0,[z0,z8,z3,z49,z5,z297,z6]),(0,[z0,z8,z2,z3,z5,z6,z322])],[(0,[z83,z0,z8,z3,z108,z5,z6]),(0,[z147,z0,z8,z2,z3,z323,z6]),(0,[z0,z8,z2,z3,z324,z5,z6]),(0,[z0,z8,z2,z3,z5,z325,z6]),(0,[z122,z0,z8,z2,z3,z5,z6]),(0,[z0,z326,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z109,z6])],[(0,[z147,z8,z2,z3,z205,z5,z6]),(1,[z0,z2,z3,z5,z327,z6]),(0,[z0,z8,z2,z3,z5,z6,z328]),(0,[z0,z8,z2,z3,z5,z6,z329]),(0,[z0,z8,z2,z3,z330,z5,z6])]],
   [[(0,[z83,z0,z8,z2,z3,z267,z6]),(0,[z143,z8,z2,z3,z5,z6,z259]),(1,[z0,z23,z2,z103,z5,z6])],[(1,[z0,z121,z8,z2,z5,z6]),(0,[z331,z0,z8,z2,z3,z5,z6]),(0,[z0,z22,z8,z2,z103,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z332]),(0,[z0,z8,z2,z316,z9,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z333]),(0,[z0,z8,z334,z2,z3,z5,z6])],[(1,[z81,z0,z8,z3,z5,z6]),(0,[z0,z8,z3,z108,z5,z165,z6]),(1,[z0,z8,z174,z3,z5,z6]),(0,[z0,z8,z2,z3,z211,z6,z13])],[(0,[z147,z0,z8,z2,z91,z5,z6]),(0,[z0,z273,z8,z2,z3,z5,z6]),(1,[z0,z8,z2,z335,z5,z6]),(0,[z336,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z337,z5,z6]),(0,[z0,z8,z3,z5,z165,z6,z43])],[(1,[z0,z8,z2,z3,z267,z6]),(0,[z62,z0,z8,z338,z3,z5,z6]),(0,[z143,z106,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z339]),(0,[z0,z8,z45,z25,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z340]),(1,[z0,z266,z2,z3,z5,z6])],[(0,[z0,z8,z2,z341,z3,z5,z6]),(0,[z0,z76,z8,z25,z3,z5,z6]),(1,[z0,z116,z8,z72,z5,z6]),(0,[z0,z8,z3,z72,z5,z6,z43]),(0,[z0,z8,z2,z3,z5,z6,z342]),(0,[z148,z0,z8,z2,z3,z86,z6]),(0,[z0,z8,z174,z51,z3,z5,z6])],[(0,[z0,z8,z2,z3,z207,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z259]),(0,[z343,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z344,z5,z6]),(0,[z0,z8,z345,z2,z3,z5,z6])],[(1,[z0,z2,z346,z3,z5,z6]),(0,[z62,z0,z8,z2,z3,z56,z6]),(0,[z206,z0,z8,z2,z3,z56,z6]),(0,[z0,z8,z2,z3,z347,z5,z6]),(0,[z0,z8,z2,z230,z3,z5,z6])]],
   [[(0,[z0,z8,z2,z3,z348,z5,z6]),(0,[z139,z0,z8,z140,z3,z5,z6]),(0,[z0,z22,z8,z2,z5,z86,z6]),(0,[z237,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z349,z6]),(0,[z0,z8,z175,z2,z3,z5,z6]),(0,[z0,z8,z2,z350,z3,z5,z6])],[(0,[z351,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z352,z2,z3,z5,z6])],[(0,[z353,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z156,z3,z5,z6]),(0,[z0,z96,z2,z3,z5,z17,z6]),(0,[z0,z354,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z355,z5,z6])],[(0,[z0,z356,z8,z2,z3,z5,z6]),(0,[z0,z357,z8,z2,z3,z5,z6]),(0,[z0,z116,z8,z2,z3,z5,z6]),(0,[z0,z8,z45,z3,z5,z165,z6]),(1,[z0,z8,z2,z358,z5,z6])],[(0,[z83,z145,z0,z8,z3,z5,z6]),(0,[z0,z8,z2,z3,z359,z5,z6]),(0,[z0,z76,z8,z3,z5,z165,z6]),(0,[z0,z360,z8,z2,z3,z5,z6]),(0,[z12,z0,z8,z2,z3,z5,z6])],[(0,[z0,z361,z8,z2,z3,z5,z6]),(0,[z0,z8,z362,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z363,z6]),(0,[z0,z8,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z3,z364,z5,z6]),(0,[z0,z8,z365,z2,z3,z5,z6]),(0,[z0,z8,z366,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z367,z6]),(0,[z92,z0,z8,z154,z3,z5,z6]),(0,[z0,z8,z2,z91,z4,z5,z6]),(0,[z0,z8,z2,z3,z5,z368,z6]),(0,[z0,z8,z2,z3,z5,z6,z369])],[(0,[z83,z0,z8,z2,z3,z370,z6]),(0,[z0,z8,z2,z338,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z371]),(0,[z372,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z373,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z374,z6])]],
   [[(0,[z70,z0,z140,z2,z3,z5,z6]),(0,[z0,z375,z8,z2,z3,z5,z6]),(0,[z83,z0,z8,z2,z99,z5,z6]),(0,[z0,z23,z2,z3,z5,z6,z78]),(0,[z376,z0,z8,z2,z3,z5,z6]),(0,[z0,z377,z8,z2,z3,z5,z6]),(0,[z0,z378,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z379,z3,z5,z6])],[(0,[z380,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z381,z2,z3,z5,z6]),(0,[z382,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z53,z45,z3,z5,z6]),(0,[z73,z0,z8,z2,z5,z6,z187])],[(0,[z70,z0,z8,z2,z3,z5,z6]),(1,[z0,z8,z2,z3,z370,z6]),(0,[z0,z8,z2,z3,z5,z383,z6]),(0,[z384,z0,z8,z2,z3,z5,z6]),(0,[z0,z385,z8,z2,z3,z5,z6])],[(1,[z0,z8,z2,z99,z5,z6]),(0,[z0,z8,z2,z5,z6,z182,z78]),(0,[z386,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z387,z6]),(0,[z0,z8,z2,z3,z5,z6,z388])],[(0,[z70,z0,z2,z3,z9,z5,z6]),(0,[z0,z8,z2,z3,z75,z5,z6]),(0,[z0,z389,z8,z2,z3,z5,z6]),(0,[z8,z2,z3,z9,z5,z390,z6]),(0,[z0,z150,z8,z2,z5,z6,z78])],[(0,[z0,z8,z391,z2,z3,z5,z6]),(0,[z392,z0,z8,z2,z3,z5,z6]),(0,[z0,z23,z8,z2,z48,z5,z6]),(0,[z12,z7,z0,z8,z2,z3,z6]),(0,[z0,z8,z2,z3,z49,z5,z6])],[(0,[z70,z0,z1,z2,z3,z5,z6]),(1,[z0,z8,z2,z156,z5,z6]),(0,[z0,z76,z8,z140,z3,z5,z6]),(0,[z0,z8,z214,z2,z3,z5,z6])]],
   [[(0,[z122,z0,z2,z3,z5,z6,z78]),(0,[z0,z393,z8,z2,z3,z5,z6])],[(0,[z394,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z207,z86,z6]),(0,[z145,z0,z8,z2,z3,z108,z6]),(0,[z395,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z396]),(0,[z122,z0,z8,z2,z199,z5,z6]),(1,[z0,z8,z25,z3,z108,z6]),(0,[z0,z8,z2,z3,z5,z6,z397]),(0,[z398,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z399,z5,z6]),(0,[z138,z0,z23,z8,z2,z5,z6]),(0,[z42,z0,z76,z8,z3,z5,z6]),(1,[z0,z8,z2,z91,z5,z189])],[(0,[z0,z8,z2,z5,z17,z6,z274])],[(0,[z0,z8,z2,z3,z3,z5,z6]),(0,[z400,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z140,z2,z3,z5,z6]),(0,[z0,z116,z8,z3,z72,z5,z6]),(0,[z0,z8,z2,z3,z5,z401,z6]),(0,[z42,z0,z8,z2,z3,z5,z6])],[(0,[z126,z0,z2,z103,z3,z5,z6]),(0,[z0,z8,z2,z3,z402,z5,z6]),(0,[z403,z0,z8,z2,z3,z5,z6]),(0,[z145,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z91,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z404,z6])],[(0,[z147,z0,z8,z2,z5,z6,z187]),(0,[z405,z0,z8,z2,z3,z5,z6]),(0,[z406,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z407,z5,z6]),(0,[z0,z408,z8,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z8,z2,z3,z5,z6]),(0,[z70,z0,z22,z2,z3,z5,z6]),(0,[z409,z0,z8,z2,z3,z5,z6]),(0,[z138,z0,z8,z53,z2,z5,z6]),(0,[z0,z22,z8,z2,z72,z5,z6]),(0,[z0,z8,z2,z410,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z411]),(0,[z412,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z51,z5,z6,z187])],[(0,[z0,z8,z154,z3,z5,z165,z6]),(0,[z413,z0,z8,z2,z3,z5,z6]),(0,[z92,z0,z76,z8,z3,z5,z6]),(0,[z0,z8,z2,z205,z5,z86,z6]),(0,[z0,z8,z2,z3,z5,z414,z6]),(0,[z415,z0,z8,z2,z3,z5,z6])],[(0,[z416,z0,z8,z2,z3,z5,z6]),(0,[z83,z8,z2,z154,z3,z5,z6]),(0,[z417,z0,z8,z2,z3,z5,z6]),(0,[z138,z0,z116,z8,z2,z5,z6]),(0,[z0,z8,z2,z3,z5,z418,z6]),(0,[z419,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z9,z5,z6])],[(0,[z92,z0,z8,z2,z3,z5,z6]),(0,[z420,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z130,z6]),(0,[z421,z0,z8,z2,z3,z5,z6])],[(0,[z83,z0,z8,z2,z31,z5,z6]),(0,[z0,z8,z2,z48,z205,z5,z6]),(0,[z0,z8,z2,z422,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z78]),(0,[z0,z8,z3,z9,z5,z423,z6])],[(0,[z0,z258,z8,z2,z3,z5,z6])],[(0,[z424,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z53,z154,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z425,z6]),(0,[z0,z426,z8,z2,z3,z5,z6])],[(0,[z12,z106,z0,z8,z2,z3,z5]),(0,[z0,z22,z8,z2,z51,z5,z6]),(0,[z7,z0,z8,z2,z3,z5,z6]),(0,[z12,z0,z8,z198,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z427])]],
   [[(1,[z0,z8,z2,z31,z5,z6]),(0,[z8,z186,z2,z154,z3,z5,z6]),(0,[z0,z8,z2,z105,z72,z5,z6]),(0,[z428,z0,z8,z2,z3,z5,z6]),(0,[z7,z0,z8,z2,z3,z211,z6]),(1,[z0,z8,z2,z3,z6,z164]),(0,[z0,z8,z429,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z430]),(0,[z0,z8,z2,z3,z5,z6,z431]),(0,[z139,z0,z2,z94,z3,z5,z6]),(0,[z432,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z3,z72,z108,z5,z6]),(1,[z148,z0,z8,z2,z86,z6]),(0,[z0,z8,z2,z3,z5,z433,z6])],[(0,[z0,z8,z186,z3,z5,z165,z6]),(0,[z139,z0,z8,z53,z3,z5,z6]),(0,[z42,z0,z8,z2,z358,z5,z6])],[(0,[z139,z92,z0,z8,z3,z5,z6]),(0,[z434,z0,z8,z2,z3,z5,z6]),(0,[z435,z0,z8,z2,z3,z5,z6]),(0,[z436,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z437,z5,z6]),(0,[z0,z8,z2,z3,z5,z438,z6])],[(0,[z0,z8,z439,z2,z3,z5,z6]),(0,[z138,z0,z8,z2,z3,z5,z6]),(0,[z0,z273,z2,z3,z205,z5,z6]),(0,[z106,z8,z2,z3,z5,z56,z6]),(0,[z0,z8,z2,z3,z5,z440,z6]),(0,[z441,z0,z8,z2,z3,z5,z6]),(0,[z442,z0,z8,z2,z3,z5,z6])],[(0,[z70,z0,z2,z3,z5,z6,z78]),(0,[z0,z8,z2,z443,z3,z5,z6]),(1,[z269,z0,z8,z2,z3,z5]),(0,[z0,z8,z2,z3,z444,z5,z6])],[(0,[z445,z0,z8,z3,z5,z56,z6]),(0,[z148,z0,z8,z2,z3,z49,z6]),(0,[z0,z8,z2,z51,z3,z49,z6]),(0,[z0,z446,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z447,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z448,z6]),(0,[z0,z8,z2,z358,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z449,z6])]],
   [[(0,[z0,z8,z2,z450,z3,z5,z6]),(0,[z451,z0,z8,z2,z3,z5,z6]),(0,[z269,z0,z8,z2,z3,z5,z56]),(0,[z0,z8,z452,z2,z3,z5,z6]),(1,[z8,z2,z3,z5,z390,z6]),(0,[z0,z8,z2,z3,z5,z6,z294])],[(0,[z0,z8,z2,z3,z5,z453,z6]),(0,[z0,z8,z2,z3,z454,z5,z6]),(0,[z0,z8,z2,z3,z5,z455,z6])],[(0,[z0,z456,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z457]),(0,[z147,z0,z8,z2,z3,z324,z6]),(0,[z0,z8,z2,z3,z458,z5,z6]),(0,[z0,z8,z2,z3,z459,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z182]),(1,[z0,z460,z2,z3,z5,z6])],[(0,[z143,z70,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z461]),(0,[z122,z0,z8,z2,z3,z5,z78]),(0,[z0,z462,z8,z2,z3,z5,z6])],[(0,[z0,z41,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z463,z5,z6])],[(0,[z0,z8,z2,z3,z464,z5,z6]),(1,[z83,z8,z154,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z323,z6]),(0,[z8,z2,z105,z3,z205,z5,z6]),(0,[z0,z8,z2,z3,z5,z465,z6]),(0,[z0,z41,z8,z2,z3,z211,z6]),(0,[z0,z8,z112,z3,z9,z5,z6])],[(0,[z143,z0,z8,z2,z3,z5,z259]),(0,[z7,z0,z41,z2,z3,z5,z6]),(0,[z0,z41,z2,z3,z9,z5,z6]),(0,[z0,z466,z8,z2,z3,z5,z6]),(1,[z0,z8,z3,z5,z297,z6]),(0,[z467,z0,z8,z2,z3,z5,z6])],[(0,[z0,z37,z8,z71,z2,z5,z6]),(0,[z139,z0,z76,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z2,z3,z468,z5,z6]),(0,[z106,z8,z2,z3,z5,z17,z6])],[(0,[z0,z8,z2,z205,z72,z5,z6]),(0,[z0,z76,z8,z53,z3,z5,z6]),(0,[z0,z2,z3,z5,z169,z6,z78]),(0,[z0,z8,z2,z3,z5,z469,z6]),(0,[z12,z258,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z470,z6]),(0,[z471,z0,z8,z2,z3,z5,z6]),(0,[z472,z0,z8,z2,z3,z5,z6]),(0,[z0,z473,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z78])],[(0,[z474,z0,z8,z2,z3,z5,z6]),(0,[z217,z0,z8,z2,z3,z5,z6]),(1,[z143,z8,z2,z3,z5,z259]),(0,[z0,z8,z53,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z475]),(0,[z0,z8,z2,z3,z5,z56,z6]),(0,[z0,z8,z94,z3,z5,z6,z43]),(0,[z306,z0,z8,z2,z3,z5,z6]),(0,[z42,z0,z8,z2,z209,z5,z6]),(0,[z0,z8,z2,z3,z209,z5,z6]),(1,[z73,z0,z8,z2,z5,z187])],[(0,[z0,z8,z2,z476,z3,z5,z6]),(0,[z477,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z5,z241,z56,z6]),(0,[z0,z8,z2,z3,z478,z5,z6]),(0,[z479,z0,z8,z2,z3,z5,z6])],[],[(0,[z0,z8,z480,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z423,z6]),(0,[z0,z8,z2,z481,z3,z5,z6])]],
   [[(0,[z0,z8,z140,z3,z5,z6,z43]),(0,[z482,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z483]),(0,[z0,z8,z2,z484,z3,z5,z6]),(0,[z42,z0,z8,z3,z5,z6,z43])],[(0,[z0,z8,z55,z3,z205,z5,z6]),(0,[z138,z0,z8,z2,z105,z5,z6]),(1,[z0,z8,z2,z485,z5,z6]),(0,[z486,z0,z8,z2,z3,z5,z6]),(0,[z0,z487,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z488,z5,z6])],[(0,[z70,z206,z8,z2,z3,z5,z6]),(0,[z0,z489,z8,z2,z3,z5,z6]),(0,[z8,z2,z3,z5,z56,z6,z259]),(1,[z445,z0,z8,z3,z5,z6]),(0,[z490,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z491,z5,z6]),(0,[z492,z0,z8,z2,z3,z5,z6])],[(0,[z493,z0,z8,z2,z3,z5,z6])],[(0,[z494,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z495,z5,z6]),(0,[z496,z0,z8,z2,z3,z5,z6]),(0,[z62,z0,z8,z195,z3,z5,z6]),(0,[z0,z23,z8,z2,z103,z5,z6]),(1,[z0,z8,z2,z119,z5,z6]),(0,[z0,z110,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z29,z5,z211])],[(0,[z497,z0,z8,z2,z3,z5,z6]),(0,[z498,z0,z8,z2,z3,z5,z6]),(0,[z12,z0,z8,z2,z3,z5,z13])],[(0,[z0,z8,z2,z3,z5,z499,z6]),(0,[z92,z0,z8,z3,z5,z6,z43]),(0,[z0,z8,z2,z3,z500,z5,z6]),(0,[z0,z8,z2,z3,z5,z501,z6])],[(0,[z502,z0,z8,z2,z3,z5,z6]),(0,[z0,z503,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z504,z6]),(0,[z0,z8,z505,z2,z3,z5,z6])]],
   [[(1,[z126,z127,z2,z3,z5,z6]),(0,[z148,z138,z0,z8,z2,z5,z6]),(0,[z0,z8,z2,z3,z5,z17,z6]),(1,[z139,z0,z94,z3,z5,z6]),(0,[z0,z8,z345,z103,z3,z5,z6]),(0,[z0,z8,z2,z3,z506,z5,z6])],[(1,[z0,z8,z20,z3,z5,z6]),(0,[z0,z8,z2,z3,z49,z207,z6]),(0,[z0,z8,z2,z225,z3,z5,z6]),(0,[z0,z8,z2,z3,z6,z164,z78])],[(0,[z0,z8,z2,z3,z370,z5,z6]),(0,[z0,z8,z507,z2,z3,z5,z6]),(0,[z0,z8,z2,z508,z3,z5,z6]),(0,[z0,z8,z2,z3,z509,z5,z6])],[(1,[z61,z0,z8,z3,z5,z6]),(0,[z83,z0,z8,z45,z3,z5,z6]),(1,[z0,z41,z2,z3,z9,z6]),(0,[z0,z8,z2,z3,z5,z6,z510]),(0,[z0,z8,z48,z3,z5,z165,z6]),(0,[z511,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z284,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z512,z6]),(0,[z513,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z514]),(1,[z0,z68,z2,z3,z5,z6]),(0,[z515,z0,z8,z2,z3,z5,z6])],[(0,[z0,z22,z8,z2,z5,z189,z6]),(0,[z0,z516,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z48,z91,z5,z6])],[(1,[z0,z8,z2,z3,z323,z6]),(0,[z0,z8,z2,z3,z5,z6,z274]),(0,[z0,z41,z2,z3,z5,z6,z78])],[(0,[z0,z8,z2,z517,z3,z5,z6]),(0,[z12,z0,z110,z2,z3,z5,z6])]],
   [[(0,[z250,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z518,z2,z3,z5,z6]),(0,[z0,z519,z8,z2,z3,z5,z6])],[(0,[z83,z0,z116,z8,z3,z5,z6]),(0,[z12,z143,z0,z8,z2,z3,z5]),(0,[z520,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z521,z2,z3,z5,z6])],[(0,[z0,z8,z19,z2,z154,z5,z6]),(1,[z0,z8,z338,z3,z5,z6]),(0,[z0,z1,z2,z94,z3,z5,z6]),(0,[z0,z8,z2,z103,z91,z5,z6]),(0,[z7,z0,z8,z2,z3,z169,z6]),(0,[z0,z8,z2,z522,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z523]),(1,[z524,z8,z2,z3,z5,z6])],[(0,[z525,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z105,z5,z86,z6]),(0,[z526,z0,z8,z2,z3,z5,z6]),(0,[z527,z0,z8,z2,z3,z5,z6])],[(0,[z528,z0,z8,z2,z3,z5,z6]),(0,[z0,z529,z8,z2,z3,z5,z6])],[(0,[z530,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z531,z5,z6]),(0,[z0,z8,z2,z532,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z533,z6])],[(1,[z0,z8,z345,z3,z5,z6]),(0,[z0,z8,z2,z3,z534,z5,z6])],[(0,[z70,z8,z2,z3,z5,z56,z6]),(0,[z0,z8,z2,z3,z5,z6,z535]),(0,[z0,z8,z2,z536,z3,z5,z6]),(0,[z0,z8,z25,z2,z330,z5,z6]),(0,[z0,z8,z2,z3,z537,z5,z6])]],
   [[(0,[z538,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z53,z186,z3,z5,z6]),(1,[z147,z8,z2,z205,z5,z6]),(0,[z138,z0,z8,z2,z205,z5,z6])],[(0,[z0,z8,z2,z3,z5,z539,z6]),(0,[z62,z206,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z108,z56,z6]),(0,[z0,z540,z8,z2,z3,z5,z6])],[(1,[z0,z37,z8,z2,z5,z6]),(0,[z147,z0,z23,z8,z2,z5,z6]),(0,[z217,z0,z8,z2,z5,z56,z6]),(0,[z0,z140,z2,z94,z3,z5,z6]),(1,[z0,z113,z2,z3,z5,z6])],[(0,[z0,z8,z53,z2,z48,z5,z6])],[(1,[z0,z2,z3,z5,z6,z128]),(1,[z0,z8,z45,z3,z5,z46])],[(0,[z0,z8,z2,z3,z541,z5,z6]),(0,[z206,z0,z8,z2,z3,z207,z6]),(0,[z0,z8,z2,z542,z3,z5,z6]),(0,[z0,z8,z2,z543,z3,z5,z6]),(0,[z0,z8,z2,z49,z5,z86,z6])],[(0,[z0,z8,z2,z3,z5,z6,z544]),(0,[z83,z139,z0,z8,z3,z5,z6]),(0,[z545,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z119,z3,z5,z6])],[(1,[z0,z18,z8,z2,z5,z6]),(0,[z148,z0,z8,z2,z72,z5,z6])]],
   [[(0,[z92,z0,z8,z48,z3,z5,z6]),(0,[z0,z8,z2,z546,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z547,z6]),(0,[z0,z22,z8,z2,z4,z5,z6]),(0,[z0,z116,z8,z2,z5,z86,z6]),(0,[z0,z8,z2,z3,z5,z211,z6])],[(0,[z548,z0,z8,z2,z3,z5,z6]),(0,[z70,z139,z0,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z549,z5,z6])],[(0,[z0,z8,z550,z2,z3,z5,z6]),(0,[z0,z551,z8,z2,z3,z5,z6]),(0,[z0,z76,z1,z2,z3,z5,z6]),(1,[z0,z8,z2,z97,z5,z6]),(0,[z0,z552,z8,z2,z3,z5,z6])],[(0,[z70,z126,z8,z2,z3,z5,z6]),(0,[z70,z8,z2,z3,z5,z17,z6]),(0,[z0,z8,z2,z154,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z553,z6]),(0,[z554,z0,z8,z2,z3,z5,z6]),(0,[z73,z0,z22,z8,z2,z5,z6]),(1,[z0,z8,z410,z3,z5,z6])],[(0,[z147,z0,z8,z2,z49,z5,z6]),(0,[z0,z8,z2,z3,z5,z327,z6]),(0,[z0,z8,z2,z3,z5,z555,z6]),(0,[z0,z1,z8,z2,z3,z5,z300]),(0,[z0,z8,z2,z26,z3,z5,z6]),(0,[z0,z556,z8,z2,z3,z5,z6])],[(0,[z62,z0,z8,z2,z75,z5,z6]),(0,[z0,z8,z140,z2,z335,z5,z6]),(0,[z0,z8,z2,z3,z335,z5,z6]),(0,[z0,z8,z2,z51,z49,z5,z6])],[(0,[z557,z0,z8,z2,z3,z5,z6]),(0,[z306,z8,z2,z3,z9,z5,z6]),(0,[z148,z0,z8,z2,z51,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z558])],[(0,[z0,z8,z559,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z560]),(0,[z0,z8,z2,z3,z5,z561,z6]),(1,[z122,z0,z2,z3,z5,z78]),(0,[z0,z8,z2,z3,z5,z562,z6])]],
   [[(0,[z0,z8,z2,z32,z3,z5,z6]),(0,[z0,z563,z8,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z169,z6]),(0,[z0,z564,z8,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z300]),(0,[z0,z8,z2,z3,z5,z6,z565])],[(0,[z127,z8,z2,z3,z5,z56,z6]),(0,[z0,z8,z566,z2,z3,z5,z6]),(0,[z0,z8,z2,z48,z5,z6,z187]),(0,[z0,z8,z266,z2,z3,z5,z6]),(0,[z73,z0,z8,z2,z3,z5,z189])],[(0,[z143,z127,z8,z2,z3,z5,z6]),(0,[z92,z0,z8,z3,z108,z5,z6]),(0,[z0,z8,z2,z567,z3,z5,z6]),(0,[z568,z0,z8,z2,z3,z5,z6]),(0,[z445,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z569,z5,z6]),(0,[z0,z23,z8,z2,z51,z5,z6]),(0,[z570,z0,z8,z2,z3,z5,z6])],[(0,[z571,z0,z8,z2,z3,z5,z6]),(0,[z147,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z3,z5,z17,z6,z129]),(0,[z0,z8,z2,z3,z5,z572,z6]),(0,[z73,z0,z573,z2,z3,z5,z6])],[(0,[z0,z8,z2,z346,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z63,z6])],[(0,[z0,z8,z574,z2,z3,z5,z6]),(0,[z62,z0,z8,z2,z3,z5,z6]),(0,[z206,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z390,z6]),(0,[z0,z8,z2,z3,z5,z6,z58]),(0,[z73,z0,z8,z2,z3,z5,z187]),(0,[z0,z8,z2,z3,z5,z6,z575])],[(0,[z0,z8,z2,z576,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z577]),(0,[z0,z8,z2,z103,z5,z6,z187]),(0,[z0,z8,z2,z3,z5,z578,z6]),(0,[z0,z8,z2,z3,z579,z5,z6])],[(0,[z580,z0,z8,z2,z3,z5,z6]),(0,[z0,z116,z8,z25,z3,z5,z6]),(0,[z0,z581,z8,z2,z3,z5,z6])]],
   [[(0,[z0,z127,z8,z2,z3,z5,z6]),(0,[z582,z0,z8,z2,z3,z5,z6]),(0,[z147,z0,z22,z8,z2,z5,z6]),(0,[z0,z8,z25,z2,z3,z108,z6]),(0,[z583,z0,z8,z2,z3,z5,z6]),(0,[z73,z0,z8,z283,z3,z5,z6]),(0,[z584,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z5,z189,z6,z187]),(0,[z0,z8,z2,z3,z5,z6,z585])],[(0,[z0,z8,z2,z3,z586,z5,z6]),(0,[z0,z8,z2,z3,z587,z5,z6]),(0,[z77,z0,z8,z2,z3,z5,z6]),(0,[z588,z0,z8,z2,z3,z5,z6])],[(0,[z7,z126,z0,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z589,z6])],[(1,[z70,z71,z2,z3,z5,z6]),(0,[z0,z8,z2,z590,z3,z5,z6]),(0,[z0,z8,z2,z3,z56,z86,z6]),(0,[z145,z0,z8,z3,z72,z5,z6]),(0,[z0,z8,z2,z3,z591,z5,z6]),(1,[z0,z8,z53,z48,z5,z6])],[(0,[z0,z18,z8,z2,z154,z5,z6]),(0,[z0,z8,z2,z225,z5,z17,z6])],[(0,[z127,z8,z2,z3,z5,z17,z6]),(0,[z592,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z25,z2,z3,z5,z6]),(0,[z593,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z29,z5,z6])],[(0,[z0,z8,z594,z2,z3,z5,z6]),(0,[z0,z116,z8,z3,z5,z165,z6]),(0,[z595,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z29,z211,z6])],[(0,[z0,z8,z596,z71,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z597,z6]),(0,[z0,z8,z2,z3,z598,z5,z6]),(0,[z0,z573,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z599,z3,z5,z6])]],
   [[(0,[z0,z121,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z2,z3,z5,z6]),(0,[z0,z116,z8,z2,z72,z5,z6]),(0,[z0,z8,z3,z5,z46,z6,z43]),(0,[z0,z8,z2,z3,z5,z6,z600])],[(0,[z0,z8,z2,z3,z5,z6,z601]),(0,[z0,z8,z2,z3,z5,z6,z602]),(0,[z603,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z45,z2,z3,z5,z43])],[(0,[z0,z8,z2,z3,z5,z604,z6]),(0,[z605,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z606,z3,z5,z6]),(0,[z607,z0,z8,z2,z3,z5,z6]),(1,[z0,z8,z2,z161,z5,z6])],[(0,[z0,z8,z2,z3,z608,z5,z6]),(0,[z206,z8,z2,z3,z207,z5,z6]),(0,[z206,z8,z2,z3,z5,z6,z259]),(0,[z609,z0,z8,z2,z3,z5,z6]),(0,[z610,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z186,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z611]),(0,[z0,z8,z2,z3,z5,z6,z612]),(0,[z8,z2,z3,z5,z6,z294,z78]),(0,[z0,z613,z8,z2,z3,z5,z6]),(0,[z0,z614,z8,z2,z3,z5,z6])],[(0,[z0,z615,z8,z2,z3,z5,z6]),(0,[z0,z616,z8,z2,z3,z5,z6]),(0,[z617,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z618,z6])],[(0,[z0,z8,z2,z619,z3,z5,z6]),(0,[z620,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z129]),(0,[z0,z8,z2,z621,z3,z5,z6]),(0,[z0,z8,z622,z2,z3,z5,z6]),(0,[z623,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z624,z3,z5,z6]),(0,[z206,z106,z8,z2,z3,z5,z6]),(0,[z0,z625,z8,z2,z3,z5,z6]),(1,[z237,z0,z8,z2,z3,z6]),(0,[z0,z116,z8,z2,z51,z5,z6]),(0,[z0,z8,z2,z3,z5,z626,z6])]],
   [[(0,[z627,z0,z8,z2,z3,z5,z6]),(0,[z147,z0,z8,z2,z105,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z628]),(1,[z77,z8,z2,z3,z5,z6])],[(0,[z126,z0,z140,z2,z3,z5,z6]),(0,[z0,z8,z2,z51,z105,z5,z6]),(0,[z0,z8,z2,z3,z5,z629,z6]),(0,[z0,z630,z8,z2,z3,z5,z6])],[(1,[z0,z8,z2,z3,z324,z6]),(1,[z0,z8,z3,z5,z423,z6]),(0,[z0,z8,z53,z3,z108,z5,z6])],[(0,[z0,z8,z2,z631,z3,z5,z6]),(1,[z0,z2,z254,z3,z5,z6]),(1,[z0,z155,z8,z3,z5,z6]),(1,[z0,z8,z2,z5,z241,z6])],[(0,[z126,z0,z8,z2,z3,z5,z6]),(1,[z0,z8,z596,z3,z5,z6]),(0,[z0,z632,z8,z2,z3,z5,z6]),(0,[z122,z0,z8,z2,z485,z5,z6]),(0,[z0,z8,z2,z3,z5,z633,z6]),(0,[z0,z8,z2,z3,z634,z5,z6]),(0,[z524,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z635,z6])],[(0,[z636,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z51,z3,z534,z5,z6]),(1,[z0,z573,z2,z3,z5,z6])],[(0,[z126,z0,z2,z3,z9,z5,z6]),(0,[z637,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z638,z5,z6]),(0,[z0,z8,z639,z2,z3,z5,z6])],[(0,[z640,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z641,z5,z6])]],
   [[(0,[z642,z0,z8,z2,z3,z5,z6]),(0,[z126,z0,z1,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z643]),(0,[z0,z8,z644,z2,z3,z5,z6]),(0,[z0,z2,z103,z3,z4,z5,z6])],[(0,[z0,z8,z2,z3,z5,z6,z645]),(0,[z0,z8,z2,z74,z3,z5,z6]),(0,[z0,z8,z2,z3,z646,z5,z6])],[(0,[z70,z0,z71,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z207,z165,z6]),(0,[z0,z647,z8,z2,z3,z5,z6]),(0,[z148,z0,z8,z2,z5,z86,z6]),(1,[z0,z8,z283,z3,z5,z6])],[(0,[z0,z2,z3,z5,z327,z56,z6]),(0,[z0,z8,z112,z2,z3,z5,z6]),(0,[z0,z8,z2,z91,z72,z5,z6])],[(0,[z0,z8,z596,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z205,z5,z6]),(0,[z0,z8,z2,z3,z5,z648,z6])],[(0,[z0,z649,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z650,z5,z6])],[(0,[z651,z0,z8,z2,z3,z5,z6]),(0,[z0,z23,z8,z2,z5,z86,z6]),(0,[z652,z0,z8,z2,z3,z5,z6])],[(0,[z653,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z654]),(0,[z0,z655,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z5,z86,z6,z187])]],
   [[(0,[z0,z8,z2,z3,z5,z656,z6]),(0,[z0,z22,z8,z2,z48,z5,z6]),(0,[z73,z0,z23,z8,z2,z5,z6]),(0,[z0,z8,z2,z3,z5,z657,z6]),(0,[z0,z8,z2,z3,z5,z658,z6]),(1,[z0,z8,z2,z230,z5,z6])],[(0,[z126,z0,z22,z2,z3,z5,z6]),(0,[z0,z659,z8,z2,z3,z5,z6]),(0,[z83,z0,z8,z186,z3,z5,z6]),(0,[z0,z8,z2,z3,z660,z5,z6]),(0,[z0,z661,z8,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z300,z6]),(0,[z0,z8,z2,z3,z5,z662,z6])],[(0,[z0,z8,z25,z186,z3,z5,z6]),(0,[z139,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z663]),(0,[z0,z8,z2,z3,z664,z5,z6]),(0,[z0,z8,z665,z2,z3,z5,z6]),(0,[z0,z8,z2,z91,z51,z5,z6])],[(0,[z70,z0,z127,z2,z3,z5,z6]),(0,[z250,z0,z2,z154,z3,z5,z6]),(0,[z0,z8,z2,z3,z666,z5,z6]),(0,[z0,z8,z2,z198,z3,z5,z6])],[(0,[z667,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z668,z5,z6]),(0,[z0,z669,z8,z2,z3,z5,z6]),(1,[z145,z0,z8,z3,z165,z6]),(0,[z42,z0,z460,z2,z3,z5,z6])],[(0,[z670,z0,z8,z2,z3,z5,z6]),(0,[z671,z0,z8,z2,z3,z5,z6])],[(0,[z672,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z72,z5,z6,z187])],[(0,[z0,z8,z71,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z673,z6]),(0,[z0,z674,z8,z2,z3,z5,z6]),(1,[z0,z8,z16,z3,z5,z6]),(0,[z0,z8,z460,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z675]),(0,[z0,z8,z2,z3,z5,z6,z676])]],
   [[],[(0,[z0,z677,z8,z2,z3,z5,z6]),(0,[z0,z678,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z679,z3,z5,z6]),(1,[z0,z8,z214,z3,z5,z6]),(1,[z0,z8,z3,z534,z5,z6])],[(0,[z0,z8,z2,z3,z5,z680,z6]),(0,[z681,z0,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z682,z3,z5,z6]),(0,[z683,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z43])],[(0,[z0,z8,z2,z3,z5,z6,z684]),(0,[z0,z8,z2,z3,z5,z685,z6]),(1,[z0,z8,z2,z5,z109,z6])],[(0,[z0,z8,z2,z3,z5,z6,z686]),(0,[z138,z0,z8,z2,z5,z6,z187]),(0,[z0,z8,z2,z3,z687,z5,z6]),(1,[z0,z8,z2,z330,z5,z6]),(0,[z12,z0,z68,z2,z3,z5,z6])],[(0,[z688,z0,z8,z2,z3,z5,z6]),(0,[z126,z0,z2,z3,z5,z6,z78]),(0,[z147,z0,z8,z32,z3,z5,z6]),(0,[z689,z0,z8,z2,z3,z5,z6]),(0,[z0,z76,z140,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z300,z6,z78]),(0,[z690,z0,z8,z2,z3,z5,z6])],[(1,[z0,z8,z2,z316,z5,z6]),(0,[z691,z0,z8,z2,z3,z5,z6]),(0,[z692,z0,z8,z2,z3,z5,z6]),(0,[z0,z693,z8,z2,z3,z5,z6]),(1,[z0,z8,z284,z3,z5,z6])]],
   [[(0,[z694,z0,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z695,z6]),(0,[z62,z0,z8,z2,z3,z207,z6]),(0,[z0,z22,z2,z3,z4,z5,z6]),(0,[z0,z8,z45,z2,z3,z5,z6])],[(0,[z696,z0,z8,z2,z3,z5,z6]),(0,[z0,z2,z346,z3,z205,z5,z6]),(0,[z0,z8,z2,z3,z697,z5,z6]),(0,[z0,z76,z8,z2,z3,z5,z6]),(1,[z7,z0,z2,z3,z169,z6]),(0,[z0,z8,z53,z3,z5,z6,z43]),(0,[z73,z0,z8,z2,z3,z5,z6])],[(0,[z206,z127,z8,z2,z3,z5,z6]),(0,[z83,z0,z8,z154,z3,z5,z6]),(0,[z147,z0,z8,z53,z2,z5,z6]),(0,[z0,z8,z2,z3,z5,z5,z6]),(0,[z0,z8,z2,z3,z242,z5,z6]),(0,[z0,z41,z8,z2,z3,z169,z6]),(0,[z145,z0,z8,z2,z3,z165,z6])],[(0,[z0,z8,z25,z154,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z698]),(0,[z0,z8,z2,z3,z485,z5,z6]),(0,[z0,z116,z8,z53,z3,z5,z6]),(0,[z12,z524,z8,z2,z3,z5,z6])],[(0,[z147,z0,z116,z8,z2,z5,z6]),(0,[z699,z0,z8,z2,z3,z5,z6]),(0,[z139,z0,z8,z3,z72,z5,z6]),(0,[z0,z8,z2,z3,z700,z5,z6])],[(0,[z162,z0,z2,z3,z5,z56,z6]),(0,[z0,z8,z2,z3,z5,z701,z6]),(0,[z0,z8,z702,z2,z3,z5,z6]),(0,[z0,z8,z703,z2,z3,z5,z6])],[(0,[z0,z704,z8,z2,z3,z5,z6]),(0,[z0,z8,z705,z2,z3,z5,z6]),(0,[z0,z23,z8,z2,z72,z5,z6]),(0,[z0,z8,z2,z9,z5,z130,z6]),(0,[z122,z0,z8,z410,z3,z5,z6]),(0,[z0,z8,z175,z3,z49,z5,z6])],[(0,[z92,z8,z186,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z706,z6]),(0,[z122,z0,z8,z2,z3,z5,z300])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z8,z2,z3,z707,z6]),(0,[z0,z8,z2,z5,z708,z6]),(0,[z0,z8,z709,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z710]),(0,[z139,z0,z8,z209,z5,z6]),(0,[z0,z8,z2,z711,z5,z6]),(1,[z0,z2,z3,z712,z6]),(0,[z0,z8,z2,z3,z211,z713])],[(0,[z714,z0,z8,z2,z3,z6]),(0,[z92,z8,z715,z3,z5,z6]),(0,[z0,z8,z2,z3,z324,z6]),(0,[z0,z8,z2,z5,z241,z63])],[(0,[z0,z155,z8,z3,z5,z6]),(0,[z0,z8,z2,z5,z241,z6]),(0,[z54,z8,z2,z105,z5,z6]),(0,[z445,z0,z8,z3,z165,z6]),(0,[z269,z0,z8,z3,z5,z33])],[(0,[z106,z8,z2,z5,z17,z274])],[(0,[z670,z0,z8,z3,z165,z6]),(0,[z0,z716,z2,z3,z5,z6]),(0,[z0,z573,z2,z3,z5,z6]),(0,[z717,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z193,z86,z6]),(0,[z0,z8,z48,z718,z5,z6]),(0,[z0,z8,z25,z3,z219,z6])],[(0,[z0,z8,z719,z3,z5,z6]),(0,[z0,z720,z8,z3,z5,z6]),(0,[z0,z8,z721,z3,z5,z6]),(0,[z0,z722,z8,z2,z5,z6]),(0,[z0,z8,z3,z5,z723,z6])],[(0,[z81,z126,z0,z3,z5,z6]),(0,[z0,z8,z2,z724,z5,z6]),(0,[z0,z8,z725,z3,z5,z6]),(0,[z0,z8,z25,z3,z305,z6]),(0,[z306,z41,z2,z3,z9,z6])],[(0,[z0,z8,z154,z330,z5,z6]),(0,[z0,z8,z2,z3,z726,z6]),(0,[z727,z0,z8,z2,z5,z6]),(0,[z0,z728,z2,z3,z5,z6]),(0,[z0,z729,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z730,z3,z5,z6]),(0,[z0,z8,z3,z731,z5,z6]),(0,[z162,z62,z2,z3,z56,z6]),(0,[z0,z8,z2,z3,z29,z172]),(0,[z0,z8,z53,z542,z5,z6]),(0,[z0,z8,z2,z3,z732,z6]),(0,[z0,z8,z74,z3,z5,z6]),(0,[z0,z8,z2,z91,z5,z201]),(0,[z0,z8,z733,z3,z5,z6]),(0,[z258,z8,z284,z3,z5,z6])],[(0,[z0,z734,z8,z3,z5,z6]),(0,[z0,z8,z195,z75,z5,z6]),(0,[z8,z2,z3,z5,z6,z735]),(0,[z8,z2,z5,z6,z182,z294]),(0,[z0,z8,z5,z6,z182,z58]),(0,[z0,z8,z283,z3,z5,z6]),(0,[z12,z0,z8,z284,z3,z13])],[(0,[z0,z8,z736,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z276]),(0,[z0,z8,z737,z3,z5,z6]),(0,[z77,z150,z8,z2,z5,z6]),(0,[z8,z3,z5,z6,z58,z294]),(0,[z150,z8,z2,z5,z6,z294]),(0,[z42,z0,z113,z3,z5,z43]),(0,[z0,z8,z3,z5,z738,z6])],[(0,[z250,z92,z0,z3,z5,z6]),(0,[z0,z8,z739,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z740]),(0,[z0,z8,z2,z3,z5,z741]),(0,[z0,z8,z2,z742,z5,z6]),(1,[z0,z2,z743,z5,z6]),(0,[z0,z8,z3,z744,z5,z6]),(0,[z0,z745,z2,z3,z5,z6]),(0,[z0,z8,z2,z746,z5,z6])],[(0,[z83,z8,z154,z99,z5,z6]),(0,[z0,z747,z2,z3,z5,z6]),(0,[z0,z8,z5,z6,z129,z274]),(0,[z0,z8,z25,z3,z509,z6]),(0,[z0,z116,z8,z534,z5,z6]),(0,[z748,z0,z8,z3,z5,z6])],[(0,[z0,z8,z749,z3,z5,z6]),(0,[z0,z750,z8,z2,z5,z6]),(0,[z0,z8,z2,z5,z751,z6])],[(0,[z147,z8,z55,z205,z5,z6]),(0,[z0,z8,z752,z3,z5,z6]),(0,[z0,z23,z8,z242,z5,z6]),(0,[z753,z8,z2,z3,z5,z6]),(0,[z0,z110,z2,z230,z5,z6])]],
   [[(0,[z127,z2,z3,z5,z6,z128]),(0,[z0,z8,z754,z3,z5,z6]),(0,[z0,z8,z755,z3,z5,z6]),(0,[z62,z8,z338,z3,z56,z6]),(0,[z0,z756,z8,z3,z5,z6]),(0,[z757,z0,z8,z3,z5,z6]),(0,[z758,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z759,z6])],[(0,[z0,z8,z99,z5,z6,z43]),(0,[z0,z8,z195,z3,z5,z6]),(0,[z0,z8,z2,z760,z5,z6]),(0,[z0,z8,z2,z761,z5,z6]),(0,[z0,z8,z3,z5,z762,z6])],[(0,[z126,z2,z270,z3,z5,z6]),(0,[z0,z8,z763,z3,z5,z6]),(0,[z250,z0,z19,z2,z5,z6]),(0,[z0,z8,z2,z5,z6,z764]),(0,[z0,z8,z2,z765,z5,z6]),(0,[z122,z0,z150,z2,z5,z78]),(0,[z0,z8,z198,z3,z5,z6])],[(0,[z0,z8,z48,z99,z5,z6]),(0,[z0,z8,z766,z3,z5,z6]),(0,[z0,z8,z2,z199,z5,z6]),(0,[z145,z0,z8,z3,z165,z6]),(0,[z0,z8,z3,z5,z767,z43]),(0,[z768,z0,z2,z3,z5,z6])],[(0,[z527,z8,z186,z3,z5,z6]),(1,[z8,z2,z769,z5,z6]),(0,[z0,z94,z3,z5,z6,z684]),(0,[z0,z8,z38,z48,z5,z6]),(0,[z0,z41,z2,z3,z6,z575]),(0,[z77,z8,z2,z5,z6,z182])],[(0,[z70,z596,z71,z3,z5,z6]),(0,[z0,z8,z2,z5,z770,z6]),(0,[z0,z771,z8,z2,z5,z6]),(0,[z0,z8,z772,z3,z5,z6]),(0,[z0,z8,z2,z3,z6,z773]),(0,[z0,z8,z774,z3,z5,z6]),(0,[z0,z8,z2,z775,z5,z6]),(0,[z8,z2,z3,z207,z726,z6]),(0,[z776,z8,z2,z3,z5,z6]),(0,[z0,z573,z74,z3,z5,z6]),(0,[z12,z0,z8,z2,z161,z13])],[(0,[z8,z777,z2,z3,z5,z6]),(0,[z92,z8,z186,z3,z5,z6]),(0,[z0,z8,z45,z335,z5,z6]),(0,[z0,z8,z5,z423,z130,z6]),(0,[z237,z0,z8,z3,z6,z58]),(0,[z0,z8,z2,z209,z5,z6]),(0,[z0,z8,z119,z534,z5,z6])],[(0,[z0,z8,z45,z3,z267,z6]),(0,[z0,z8,z3,z778,z5,z6]),(0,[z0,z8,z3,z5,z46,z698]),(0,[z77,z237,z8,z2,z3,z6])]],
   [[(0,[z0,z8,z2,z779,z5,z6]),(0,[z409,z0,z8,z3,z165,z6]),(0,[z0,z8,z20,z3,z323,z6]),(0,[z780,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z781]),(0,[z0,z8,z3,z534,z5,z6]),(0,[z0,z8,z2,z782,z5,z6])],[(0,[z0,z8,z3,z207,z297,z6]),(0,[z0,z96,z2,z225,z5,z6])],[(0,[z0,z8,z783,z3,z5,z6]),(0,[z83,z0,z18,z8,z5,z6]),(0,[z0,z8,z2,z784,z5,z6]),(0,[z0,z76,z3,z79,z5,z6]),(0,[z0,z76,z8,z330,z5,z6]),(0,[z0,z23,z345,z103,z5,z6]),(0,[z0,z8,z2,z785,z5,z6]),(0,[z0,z8,z2,z786,z5,z6]),(0,[z787,z8,z2,z3,z5,z6])],[(0,[z122,z0,z2,z5,z182,z78]),(0,[z0,z8,z2,z788,z5,z6])],[(0,[z70,z2,z3,z5,z6,z128]),(0,[z0,z8,z2,z225,z5,z6]),(0,[z138,z389,z8,z2,z5,z6]),(0,[z106,z96,z2,z3,z5,z17]),(0,[z0,z8,z2,z3,z6,z789]),(0,[z0,z8,z790,z3,z5,z6]),(0,[z122,z0,z3,z5,z58,z78]),(0,[z0,z1,z2,z3,z5,z781]),(0,[z0,z791,z2,z3,z5,z6]),(0,[z0,z8,z53,z718,z5,z6])],[(0,[z70,z0,z2,z97,z5,z6]),(0,[z0,z116,z8,z3,z267,z6]),(0,[z0,z8,z3,z5,z792,z6]),(0,[z162,z0,z2,z5,z241,z6]),(0,[z0,z8,z793,z3,z5,z6]),(0,[z0,z8,z794,z3,z5,z6]),(0,[z0,z8,z795,z3,z5,z6])],[(0,[z0,z8,z3,z5,z796,z6]),(0,[z0,z8,z2,z5,z6,z797]),(0,[z0,z8,z2,z798,z5,z6]),(0,[z0,z8,z2,z316,z5,z6]),(0,[z0,z116,z8,z718,z5,z6]),(0,[z0,z110,z284,z3,z5,z6])],[(0,[z0,z22,z2,z468,z5,z6]),(0,[z0,z8,z2,z799,z5,z6]),(0,[z0,z8,z3,z5,z6,z800]),(0,[z0,z8,z2,z801,z5,z6]),(0,[z0,z8,z3,z5,z6,z802]),(0,[z803,z8,z2,z3,z5,z6]),(0,[z122,z81,z0,z3,z5,z78]),(0,[z524,z68,z2,z3,z5,z6])]],
   [[(0,[z804,z0,z8,z2,z3,z6]),(0,[z126,z0,z345,z3,z5,z6]),(0,[z0,z8,z2,z3,z805,z6]),(0,[z0,z3,z5,z6,z128,z129]),(0,[z8,z2,z3,z806,z5,z6]),(0,[z0,z8,z702,z72,z5,z6]),(0,[z7,z0,z2,z3,z169,z6])],[(0,[z83,z8,z154,z31,z5,z6]),(0,[z0,z8,z352,z48,z5,z6]),(0,[z0,z8,z3,z242,z5,z6]),(0,[z0,z310,z8,z2,z86,z6])],[(0,[z0,z8,z2,z807,z5,z6]),(0,[z0,z8,z808,z3,z5,z6]),(0,[z147,z8,z20,z205,z5,z6]),(0,[z0,z8,z2,z91,z323,z6]),(0,[z0,z8,z2,z75,z207,z6]),(0,[z0,z8,z809,z3,z5,z6]),(0,[z0,z8,z91,z242,z5,z6]),(0,[z0,z150,z266,z2,z5,z6]),(0,[z0,z8,z2,z3,z810,z6]),(0,[z0,z8,z25,z119,z108,z6])],[(0,[z250,z0,z2,z3,z5,z6]),(0,[z70,z625,z2,z3,z5,z6]),(0,[z127,z777,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z811,z6]),(0,[z147,z2,z346,z205,z5,z6]),(0,[z0,z8,z2,z51,z102,z6]),(0,[z0,z2,z3,z5,z781,z78]),(0,[z0,z8,z2,z91,z5,z812]),(0,[z0,z8,z3,z813,z5,z6])],[(0,[z81,z0,z94,z3,z5,z6])],[(0,[z36,z8,z186,z3,z5,z6]),(0,[z303,z8,z2,z3,z207,z6]),(0,[z0,z96,z2,z5,z6,z274]),(0,[z814,z8,z2,z3,z5,z6]),(0,[z0,z8,z410,z485,z5,z6]),(0,[z0,z815,z2,z3,z5,z6]),(1,[z0,z8,z2,z3,z713])],[(0,[z0,z76,z3,z5,z6,z124]),(0,[z258,z8,z2,z161,z5,z6])],[(0,[z0,z8,z2,z3,z816,z6]),(0,[z817,z0,z8,z3,z5,z6]),(0,[z147,z8,z2,z205,z323,z6]),(0,[z0,z8,z25,z119,z5,z6]),(0,[z0,z8,z818,z3,z5,z6]),(0,[z12,z0,z8,z2,z3,z13])]],
   [[(0,[z0,z273,z2,z3,z5,z6]),(0,[z0,z2,z103,z586,z5,z6]),(0,[z0,z819,z8,z3,z5,z6])],[(0,[z0,z8,z225,z5,z6,z129]),(0,[z139,z0,z8,z335,z5,z6]),(0,[z122,z0,z2,z485,z5,z78]),(0,[z77,z8,z2,z3,z6,z164]),(0,[z0,z8,z3,z718,z5,z6])],[(0,[z139,z0,z8,z3,z267,z6]),(0,[z0,z8,z32,z3,z5,z6]),(0,[z0,z116,z8,z591,z5,z6]),(0,[z0,z8,z175,z48,z5,z6])],[(0,[z92,z8,z644,z3,z5,z6]),(0,[z472,z0,z2,z3,z5,z78])],[(0,[z83,z551,z8,z3,z5,z6]),(0,[z106,z258,z8,z2,z3,z5]),(0,[z0,z23,z2,z743,z5,z6]),(0,[z0,z8,z2,z26,z5,z6]),(0,[z42,z0,z8,z3,z5,z43])],[(0,[z0,z8,z2,z5,z6,z820]),(0,[z0,z116,z8,z99,z5,z6]),(0,[z0,z2,z3,z821,z5,z6]),(0,[z0,z8,z338,z156,z5,z6]),(1,[z8,z2,z3,z5,z822]),(0,[z0,z8,z2,z5,z823,z6])],[(0,[z0,z8,z3,z5,z824,z6]),(0,[z0,z8,z2,z3,z5,z825]),(0,[z62,z8,z2,z75,z56,z6]),(0,[z0,z8,z3,z437,z165,z6]),(0,[z826,z8,z2,z3,z5,z6])],[(0,[z70,z777,z2,z3,z5,z6]),(0,[z8,z2,z3,z5,z6,z294]),(0,[z0,z8,z2,z3,z5,z827]),(0,[z0,z8,z3,z5,z6,z58]),(0,[z0,z828,z2,z3,z5,z6]),(0,[z148,z0,z8,z534,z5,z6])]],
   [[(0,[z0,z829,z2,z3,z5,z6]),(0,[z106,z2,z3,z5,z17,z128]),(0,[z8,z2,z3,z5,z6,z830]),(0,[z831,z0,z8,z2,z3,z6]),(0,[z73,z0,z8,z74,z5,z187])],[(0,[z0,z8,z2,z5,z6,z832]),(0,[z0,z8,z174,z51,z49,z6])],[(0,[z0,z833,z8,z2,z5,z6]),(0,[z0,z2,z3,z743,z5,z6]),(0,[z0,z834,z2,z3,z5,z6]),(0,[z12,z0,z68,z2,z3,z13])],[(0,[z306,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z835,z5,z6]),(0,[z0,z8,z836,z3,z5,z6]),(0,[z93,z0,z94,z3,z5,z6]),(0,[z237,z81,z0,z8,z3,z6]),(0,[z42,z0,z460,z3,z5,z43]),(0,[z837,z8,z2,z3,z5,z6])],[(0,[z0,z8,z2,z838,z5,z6]),(0,[z0,z8,z839,z3,z5,z6]),(0,[z0,z8,z3,z267,z6,z43]),(0,[z8,z2,z840,z3,z5,z6]),(0,[z306,z8,z112,z3,z5,z6])],[(0,[z269,z70,z8,z2,z3,z5]),(0,[z70,z81,z0,z3,z5,z6]),(0,[z0,z8,z2,z5,z6,z841]),(0,[z0,z8,z2,z3,z842,z6]),(0,[z83,z254,z154,z3,z5,z6]),(0,[z0,z8,z843,z3,z5,z6]),(0,[z0,z8,z2,z743,z5,z6]),(0,[z0,z8,z3,z5,z844,z6])],[(0,[z0,z18,z8,z32,z5,z6]),(0,[z445,z0,z8,z3,z108,z6]),(0,[z0,z845,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z846,z6])],[(0,[z0,z8,z2,z847,z5,z6]),(0,[z0,z2,z3,z5,z6,z848]),(0,[z0,z849,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z850]),(0,[z0,z851,z8,z3,z5,z6]),(0,[z237,z0,z8,z2,z6,z182])]],
   [[(0,[z0,z8,z2,z769,z5,z6]),(0,[z0,z630,z8,z72,z5,z6]),(0,[z0,z8,z2,z852,z5,z6]),(0,[z0,z8,z25,z330,z108,z6])],[(0,[z0,z8,z2,z3,z5,z63]),(0,[z306,z8,z2,z5,z130,z6]),(0,[z0,z8,z853,z3,z5,z6]),(0,[z0,z150,z8,z5,z6,z58]),(0,[z0,z8,z2,z854,z5,z6]),(0,[z42,z0,z8,z358,z5,z43])],[(0,[z0,z8,z2,z3,z5,z6]),(0,[z0,z121,z8,z596,z5,z6]),(0,[z0,z2,z3,z9,z695,z6]),(0,[z139,z0,z8,z99,z5,z6]),(0,[z855,z0,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z327,z63]),(0,[z0,z110,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z856,z6])],[(0,[z0,z2,z3,z5,z327,z6]),(0,[z0,z8,z2,z3,z857,z6]),(0,[z0,z8,z2,z3,z858,z6]),(0,[z0,z55,z346,z3,z5,z6]),(0,[z859,z0,z2,z3,z5,z6]),(0,[z860,z0,z8,z2,z5,z6])],[(0,[z147,z310,z8,z2,z5,z6]),(0,[z0,z2,z5,z241,z327,z6])],[(0,[z139,z0,z861,z3,z5,z6]),(0,[z0,z150,z2,z4,z5,z6])],[(0,[z0,z8,z862,z3,z5,z6]),(0,[z106,z8,z16,z3,z5,z17]),(0,[z0,z8,z3,z5,z863,z6]),(0,[z8,z2,z3,z6,z164,z294]),(0,[z0,z8,z174,z3,z5,z6]),(0,[z12,z0,z110,z2,z3,z13])],[(0,[z0,z2,z3,z5,z864,z6]),(0,[z0,z76,z460,z3,z5,z6]),(0,[z0,z8,z2,z5,z865,z6]),(0,[z258,z8,z198,z3,z5,z6]),(0,[z0,z8,z866,z3,z5,z6])]],
   [[(0,[z0,z8,z867,z3,z5,z6]),(0,[z0,z868,z8,z2,z5,z6]),(0,[z0,z8,z869,z3,z5,z6]),(0,[z870,z0,z8,z2,z5,z6]),(0,[z90,z8,z2,z3,z56,z6]),(0,[z545,z0,z8,z3,z5,z43]),(0,[z0,z8,z2,z871,z5,z6]),(0,[z0,z266,z2,z3,z5,z6]),(0,[z73,z0,z8,z2,z5,z812]),(0,[z872,z0,z2,z3,z5,z6])],[(0,[z0,z8,z2,z873,z5,z6]),(0,[z0,z8,z2,z874,z5,z6]),(0,[z0,z116,z8,z72,z5,z6])],[(0,[z0,z8,z53,z567,z5,z6]),(0,[z0,z22,z2,z743,z5,z6])],[(0,[z0,z8,z2,z3,z875,z6]),(0,[z545,z0,z2,z3,z5,z78]),(0,[z41,z2,z3,z9,z390,z6])],[(0,[z0,z8,z2,z3,z5,z876]),(0,[z61,z0,z121,z8,z5,z6]),(0,[z0,z8,z877,z3,z5,z6]),(0,[z0,z8,z45,z3,z5,z383]),(0,[z0,z878,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z879,z6]),(0,[z0,z150,z8,z2,z5,z6]),(0,[z372,z0,z22,z2,z5,z6]),(0,[z880,z0,z8,z3,z5,z6]),(0,[z0,z460,z45,z3,z5,z6])],[(0,[z0,z8,z2,z3,z881,z6]),(0,[z445,z0,z8,z5,z241,z6])],[(0,[z83,z250,z154,z3,z5,z6]),(0,[z269,z445,z0,z8,z3,z5]),(0,[z0,z8,z16,z5,z6,z274]),(0,[z0,z2,z861,z3,z5,z6]),(0,[z0,z8,z882,z3,z5,z6]),(0,[z0,z8,z2,z358,z5,z6]),(0,[z0,z68,z2,z161,z5,z6])]],
   [[(0,[z0,z18,z8,z5,z165,z6]),(0,[z0,z273,z2,z48,z5,z6]),(0,[z883,z8,z2,z3,z5,z6]),(0,[z8,z2,z3,z5,z6,z884])],[(0,[z0,z8,z3,z5,z6,z885]),(0,[z8,z2,z3,z5,z886,z6]),(0,[z0,z887,z8,z2,z5,z6]),(0,[z652,z0,z8,z2,z86,z6])],[(0,[z0,z8,z48,z280,z5,z6]),(0,[z0,z8,z2,z888,z5,z6]),(0,[z0,z8,z119,z72,z5,z6])],[(0,[z126,z2,z422,z3,z5,z6]),(0,[z217,z0,z8,z5,z33,z6]),(0,[z0,z1,z2,z3,z5,z192]),(0,[z122,z0,z410,z3,z5,z78]),(0,[z0,z889,z2,z3,z5,z6]),(0,[z0,z890,z2,z3,z5,z6]),(0,[z42,z0,z8,z209,z5,z43])],[(0,[z0,z8,z2,z891,z5,z6]),(0,[z892,z0,z8,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z893]),(0,[z122,z0,z2,z3,z5,z781]),(0,[z237,z0,z68,z2,z3,z6]),(0,[z0,z8,z2,z5,z894,z6])],[(0,[z83,z8,z481,z3,z5,z6]),(0,[z0,z8,z2,z5,z706,z187]),(0,[z0,z8,z175,z3,z5,z6])],[(0,[z0,z8,z2,z3,z5,z895]),(0,[z7,z0,z2,z3,z313,z6]),(0,[z0,z8,z896,z3,z5,z6]),(0,[z897,z0,z8,z2,z5,z6]),(0,[z0,z8,z898,z3,z5,z6])],[(0,[z61,z126,z0,z3,z5,z6]),(0,[z0,z8,z2,z899,z5,z6]),(0,[z0,z8,z2,z5,z6,z182]),(0,[z900,z8,z2,z3,z5,z6]),(0,[z7,z0,z68,z2,z3,z6])]],
   [[(0,[z0,z8,z901,z3,z5,z6]),(0,[z62,z8,z195,z3,z56,z6]),(1,[z0,z8,z3,z5,z767]),(0,[z0,z902,z2,z3,z5,z6])],[(0,[z62,z445,z8,z3,z56,z6]),(0,[z0,z8,z2,z3,z5,z822]),(0,[z903,z8,z2,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z904]),(0,[z0,z8,z905,z3,z5,z6]),(0,[z0,z8,z906,z3,z5,z6]),(0,[z0,z266,z74,z3,z5,z6])],[(0,[z0,z8,z2,z5,z6,z907]),(0,[z0,z266,z283,z3,z5,z6])],[(0,[z0,z908,z8,z2,z5,z6]),(0,[z0,z8,z3,z5,z909,z6]),(0,[z376,z8,z154,z3,z5,z6]),(0,[z0,z8,z45,z3,z5,z440])],[(0,[z70,z0,z345,z3,z5,z6]),(0,[z0,z8,z2,z5,z6,z910]),(0,[z162,z0,z2,z3,z5,z63]),(0,[z0,z8,z2,z911,z5,z6]),(0,[z0,z8,z3,z912,z5,z6])],[(0,[z162,z0,z2,z3,z5,z6]),(0,[z0,z8,z2,z913,z5,z6]),(0,[z0,z2,z3,z5,z914,z6]),(0,[z0,z76,z140,z3,z5,z6]),(0,[z0,z8,z2,z915,z5,z6]),(0,[z0,z8,z2,z916,z5,z6]),(0,[z917,z8,z2,z3,z5,z6]),(0,[z73,z0,z266,z2,z5,z187]),(0,[z0,z110,z198,z3,z5,z6])],[(0,[z0,z8,z32,z205,z5,z6]),(0,[z143,z258,z8,z2,z3,z5]),(0,[z0,z8,z2,z918,z5,z6]),(0,[z0,z919,z8,z3,z5,z6]),(0,[z0,z8,z25,z3,z108,z6]),(0,[z0,z8,z534,z5,z6,z187]),(0,[z73,z0,z573,z2,z5,z187])],[(0,[z126,z2,z3,z5,z6,z294]),(0,[z0,z8,z920,z3,z5,z6]),(0,[z0,z155,z8,z5,z86,z6]),(0,[z0,z76,z8,z209,z5,z6]),(0,[z0,z8,z2,z91,z5,z189])]],
   [[(0,[z0,z8,z2,z5,z921,z6]),(1,[z0,z8,z2,z751,z6])],[(0,[z0,z8,z2,z922,z5,z6]),(0,[z0,z8,z2,z3,z923,z6]),(0,[z206,z8,z2,z3,z207,z6]),(0,[z0,z8,z48,z330,z5,z6]),(0,[z0,z8,z330,z108,z5,z6])],[(0,[z0,z924,z2,z3,z5,z6]),(0,[z306,z8,z2,z316,z5,z6]),(0,[z0,z925,z8,z2,z5,z6]),(1,[z0,z8,z2,z5,z812])],[(0,[z0,z155,z8,z99,z5,z6]),(0,[z0,z8,z2,z3,z5,z926]),(0,[z147,z8,z2,z205,z324,z6]),(0,[z217,z0,z8,z2,z5,z63]),(0,[z0,z927,z8,z2,z5,z6]),(0,[z0,z8,z2,z928,z5,z6]),(0,[z0,z8,z2,z929,z5,z6]),(0,[z0,z8,z214,z485,z5,z6]),(0,[z0,z8,z53,z119,z5,z6])],[(0,[z0,z8,z2,z3,z5,z930]),(0,[z92,z0,z8,z119,z5,z6]),(0,[z217,z0,z8,z2,z5,z6]),(0,[z147,z155,z8,z205,z5,z6]),(0,[z0,z8,z2,z931,z5,z6]),(0,[z479,z0,z8,z2,z5,z187])],[(0,[z0,z8,z186,z3,z267,z6]),(0,[z0,z8,z2,z3,z932,z6]),(0,[z0,z8,z3,z5,z933,z6]),(0,[z0,z68,z2,z230,z5,z6])],[(0,[z0,z8,z2,z5,z934,z6]),(0,[z0,z8,z935,z3,z5,z6]),(0,[z0,z8,z936,z3,z5,z6]),(0,[z0,z937,z8,z2,z5,z6]),(0,[z8,z2,z3,z5,z6,z822]),(0,[z0,z8,z2,z5,z938,z6]),(0,[z0,z8,z2,z51,z488,z6])],[(0,[z0,z1,z2,z3,z5,z572]),(0,[z0,z8,z939,z3,z5,z6]),(0,[z0,z8,z53,z249,z5,z6]),(0,[z0,z8,z3,z5,z46,z767])]],
   [[(0,[z92,z8,z3,z5,z685,z6]),(0,[z0,z940,z8,z3,z5,z6]),(0,[z122,z2,z3,z5,z294,z78])],[(0,[z0,z8,z2,z941,z5,z6]),(0,[z0,z942,z8,z2,z5,z6]),(0,[z269,z217,z0,z8,z2,z5]),(0,[z2,z3,z5,z6,z294,z128])],[(0,[z777,z71,z2,z3,z5,z6]),(0,[z106,z8,z2,z3,z5,z17]),(0,[z139,z0,z522,z3,z5,z6]),(0,[z0,z8,z2,z3,z6,z713])],[(0,[z0,z8,z2,z943,z5,z6]),(0,[z0,z23,z2,z215,z5,z6]),(0,[z524,z8,z2,z230,z5,z6])],[(0,[z0,z2,z3,z5,z944,z6]),(0,[z0,z8,z2,z3,z6,z164]),(0,[z0,z8,z2,z3,z29,z211])],[(0,[z0,z945,z8,z2,z5,z6]),(0,[z148,z0,z8,z2,z86,z6])],[(0,[z0,z8,z946,z3,z5,z6]),(0,[z0,z8,z2,z947,z5,z6]),(0,[z0,z948,z8,z2,z5,z6]),(0,[z81,z0,z150,z8,z5,z6])],[(0,[z258,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z6,z949]),(0,[z0,z8,z2,z950,z5,z6]),(0,[z258,z110,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z2,z3,z951,z6]),(0,[z0,z8,z952,z3,z5,z6]),(0,[z217,z0,z2,z5,z327,z6]),(0,[z595,z8,z2,z3,z56,z6]),(0,[z0,z2,z3,z5,z712,z6]),(0,[z0,z8,z244,z48,z5,z6]),(0,[z0,z8,z2,z5,z189,z812])],[(0,[z126,z0,z2,z316,z5,z6]),(0,[z0,z8,z953,z3,z5,z6]),(0,[z0,z8,z2,z3,z954,z6]),(0,[z955,z8,z2,z3,z5,z6])],[(0,[z0,z8,z956,z3,z5,z6]),(0,[z0,z8,z3,z957,z5,z6]),(0,[z0,z8,z2,z958,z5,z6]),(0,[z0,z8,z45,z99,z5,z6]),(0,[z0,z8,z2,z5,z959,z6]),(0,[z0,z8,z960,z3,z5,z6]),(0,[z0,z8,z961,z3,z5,z6]),(0,[z0,z8,z2,z6,z182,z164]),(0,[z0,z613,z8,z72,z5,z6]),(0,[z0,z8,z3,z5,z6,z767])],[(0,[z0,z8,z2,z5,z6,z274]),(0,[z0,z8,z338,z3,z56,z6]),(0,[z0,z8,z2,z962,z5,z6]),(0,[z237,z0,z41,z2,z3,z6]),(0,[z0,z8,z3,z963,z5,z6])],[(0,[z0,z8,z3,z5,z33,z63]),(0,[z0,z68,z284,z3,z5,z6])],[(0,[z0,z8,z3,z964,z5,z6]),(0,[z0,z8,z186,z99,z5,z6]),(0,[z0,z8,z3,z965,z5,z6]),(0,[z0,z8,z3,z5,z33,z6]),(0,[z692,z8,z2,z105,z5,z6]),(0,[z0,z8,z195,z156,z5,z6]),(0,[z62,z2,z3,z327,z56,z6])],[(0,[z70,z61,z0,z3,z5,z6]),(0,[z0,z8,z154,z3,z267,z6]),(0,[z8,z2,z3,z5,z726,z6]),(0,[z0,z8,z5,z241,z33,z6]),(0,[z0,z460,z2,z3,z5,z6]),(0,[z0,z8,z966,z3,z5,z6]),(0,[z967,z8,z2,z3,z5,z6]),(0,[z968,z0,z8,z2,z5,z6]),(0,[z969,z0,z8,z3,z5,z6])],[(0,[z0,z8,z2,z970,z5,z6]),(0,[z138,z8,z2,z105,z5,z6]),(0,[z0,z155,z8,z72,z5,z6]),(0,[z0,z971,z2,z3,z5,z6]),(0,[z217,z0,z8,z2,z86,z6]),(0,[z0,z150,z8,z2,z6,z164])]],
   [[(0,[z0,z8,z972,z3,z5,z6])],[(0,[z83,z8,z154,z3,z5,z6]),(0,[z269,z106,z8,z2,z3,z5]),(0,[z77,z81,z8,z3,z5,z6]),(0,[z145,z0,z8,z330,z5,z6])],[(0,[z0,z8,z2,z973,z5,z6]),(0,[z0,z974,z2,z3,z5,z6]),(0,[z0,z8,z55,z3,z5,z6]),(0,[z0,z975,z2,z3,z5,z6]),(0,[z0,z8,z976,z3,z5,z6]),(0,[z0,z8,z977,z3,z5,z6]),(0,[z0,z693,z2,z103,z5,z6]),(0,[z524,z8,z284,z3,z5,z6])],[(0,[z0,z8,z2,z5,z978,z6]),(0,[z0,z8,z979,z3,z5,z6]),(0,[z0,z361,z8,z72,z5,z6]),(0,[z0,z8,z105,z534,z5,z6]),(0,[z0,z8,z3,z56,z297,z6]),(0,[z980,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z5,z981,z6]),(0,[z0,z8,z2,z5,z6,z812])],[],[],[(0,[z206,z8,z2,z3,z239,z6]),(0,[z0,z982,z2,z3,z5,z6]),(0,[z0,z8,z2,z983,z5,z6]),(0,[z0,z155,z8,z51,z5,z6]),(0,[z0,z984,z2,z3,z5,z6]),(0,[z0,z8,z2,z985,z5,z6]),(0,[z0,z8,z2,z3,z211,z483]),(0,[z0,z8,z2,z3,z933,z6])],[(0,[z0,z76,z622,z3,z5,z6]),(0,[z472,z0,z8,z2,z5,z187]),(0,[z0,z8,z2,z986,z5,z6]),(0,[z77,z122,z2,z3,z5,z78]),(0,[z148,z0,z8,z2,z633,z6])]],
   [[(0,[z250,z0,z3,z72,z5,z6]),(0,[z8,z2,z3,z5,z822,z259]),(0,[z106,z8,z2,z3,z5,z433]),(0,[z0,z326,z8,z72,z5,z6]),(0,[z588,z0,z8,z72,z5,z6]),(0,[z0,z8,z330,z5,z6,z43]),(0,[z0,z8,z51,z49,z297,z6]),(0,[z73,z0,z8,z2,z5,z187])],[(0,[z139,z0,z35,z3,z5,z6]),(0,[z0,z23,z8,z2,z323,z6]),(0,[z62,z8,z2,z3,z56,z6]),(0,[z987,z8,z2,z3,z5,z6])],[(0,[z988,z0,z8,z2,z3,z5]),(0,[z162,z445,z0,z3,z5,z6]),(0,[z106,z8,z2,z3,z5,z673]),(0,[z0,z8,z53,z66,z5,z6])],[(0,[z0,z8,z72,z5,z6,z65])],[(0,[z0,z8,z2,z3,z5,z989]),(0,[z0,z8,z3,z990,z5,z6]),(0,[z73,z0,z8,z2,z5,z663]),(0,[z0,z8,z2,z5,z189,z40]),(0,[z0,z23,z2,z5,z6,z565]),(0,[z237,z0,z150,z8,z2,z6]),(0,[z0,z991,z2,z3,z5,z6])],[(0,[z147,z0,z155,z8,z5,z6]),(0,[z445,z0,z8,z3,z5,z63]),(0,[z0,z8,z2,z5,z992,z6]),(0,[z0,z8,z2,z993,z5,z6]),(0,[z0,z8,z2,z485,z5,z6]),(0,[z0,z8,z3,z994,z5,z6])],[(0,[z0,z8,z2,z3,z5,z995]),(0,[z0,z8,z154,z99,z5,z6]),(0,[z445,z0,z8,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z996])],[(0,[z8,z2,z715,z3,z5,z6]),(0,[z0,z8,z2,z997,z5,z6]),(0,[z0,z8,z32,z91,z5,z6]),(0,[z0,z8,z3,z5,z6,z998]),(0,[z0,z8,z309,z3,z108,z6]),(0,[z0,z8,z2,z207,z109,z6]),(0,[z0,z23,z2,z103,z5,z6]),(0,[z8,z112,z3,z5,z390,z6])]],
   [[(0,[z0,z121,z8,z2,z5,z6]),(0,[z0,z76,z8,z335,z5,z6])],[(0,[z0,z76,z8,z3,z267,z6]),(0,[z0,z23,z8,z32,z5,z6]),(0,[z81,z0,z8,z3,z5,z6]),(0,[z0,z1,z2,z485,z5,z6]),(0,[z122,z0,z214,z3,z5,z78]),(0,[z0,z999,z8,z2,z5,z6])],[(0,[z0,z8,z2,z1000,z5,z6]),(0,[z0,z8,z2,z335,z5,z6]),(0,[z0,z8,z2,z1001,z5,z6]),(0,[z0,z8,z1002,z3,z5,z6]),(0,[z0,z8,z2,z49,z751,z6])],[(0,[z0,z8,z2,z3,z267,z6]),(0,[z0,z2,z3,z5,z6,z1003]),(0,[z8,z186,z715,z3,z5,z6]),(0,[z0,z8,z2,z49,z323,z6]),(0,[z269,z258,z8,z2,z3,z5]),(0,[z0,z1004,z8,z2,z5,z6]),(0,[z0,z8,z2,z1005,z5,z6])],[(0,[z0,z8,z2,z3,z6,z1006]),(0,[z147,z8,z32,z205,z5,z6]),(0,[z0,z8,z205,z534,z5,z6]),(0,[z139,z0,z94,z3,z5,z6]),(0,[z0,z8,z2,z718,z5,z6])],[(0,[z70,z551,z2,z3,z5,z6]),(0,[z139,z0,z98,z3,z5,z6]),(0,[z0,z1007,z2,z3,z5,z6]),(0,[z0,z8,z1008,z3,z5,z6])],[(0,[z0,z2,z346,z3,z5,z6]),(0,[z126,z0,z112,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z1009]),(0,[z1010,z0,z2,z3,z5,z6]),(0,[z0,z8,z53,z32,z5,z6]),(0,[z0,z8,z338,z75,z5,z6]),(0,[z8,z2,z3,z5,z6,z1011])],[(1,[z777,z2,z3,z5,z6]),(0,[z70,z669,z2,z3,z5,z6]),(0,[z250,z0,z25,z3,z5,z6]),(0,[z147,z613,z8,z2,z5,z6]),(0,[z0,z8,z2,z1012,z5,z6]),(0,[z106,z8,z2,z225,z5,z17]),(0,[z0,z8,z1013,z3,z5,z6]),(0,[z0,z2,z1014,z3,z5,z6])]],
   [[(0,[z0,z8,z1015,z3,z5,z6]),(0,[z162,z0,z3,z5,z33,z6]),(0,[z0,z68,z2,z3,z5,z6]),(0,[z81,z0,z460,z3,z5,z6])],[(0,[z0,z1016,z2,z3,z5,z6]),(0,[z0,z8,z2,z75,z56,z6]),(0,[z0,z2,z3,z712,z169,z6]),(0,[z0,z8,z2,z3,z751,z6])],[(0,[z0,z1,z2,z3,z5,z136]),(0,[z0,z8,z2,z3,z323,z6]),(0,[z0,z8,z1017,z3,z5,z6])],[(0,[z70,z2,z3,z5,z6,z294]),(0,[z1018,z0,z8,z2,z3,z5]),(0,[z0,z8,z3,z5,z1019,z6]),(0,[z269,z0,z2,z3,z5,z327]),(0,[z0,z1020,z8,z2,z5,z6]),(0,[z0,z8,z48,z5,z455,z6]),(0,[z0,z8,z25,z26,z108,z6])],[(0,[z83,z613,z8,z3,z5,z6]),(0,[z0,z1021,z2,z3,z5,z6]),(0,[z0,z8,z1022,z3,z5,z6]),(0,[z0,z8,z2,z1023,z5,z6]),(0,[z0,z8,z45,z3,z5,z200])],[(0,[z147,z0,z8,z175,z5,z6]),(0,[z0,z8,z3,z5,z6,z1024]),(0,[z0,z76,z3,z5,z425,z6]),(0,[z0,z460,z2,z209,z5,z6]),(0,[z0,z2,z1025,z3,z5,z6]),(0,[z0,z8,z2,z5,z6,z1026])],[(0,[z83,z8,z715,z3,z5,z6]),(0,[z269,z62,z8,z2,z3,z56]),(0,[z269,z162,z0,z2,z3,z5]),(0,[z0,z8,z2,z341,z49,z6]),(0,[z8,z2,z316,z5,z390,z6]),(0,[z0,z1027,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z1028,z6]),(0,[z0,z8,z2,z3,z1029,z6]),(0,[z0,z8,z20,z3,z324,z6]),(0,[z0,z22,z8,z2,z323,z6]),(0,[z0,z1030,z2,z3,z5,z6]),(0,[z138,z8,z2,z5,z6,z523]),(0,[z1031,z8,z2,z3,z5,z6]),(0,[z1032,z0,z8,z2,z5,z6]),(0,[z0,z8,z2,z1033,z5,z6])]],
   [[(0,[z0,z8,z1034,z2,z5,z6]),(0,[z0,z1035,z2,z3,z5,z6]),(0,[z0,z41,z3,z9,z423,z6]),(0,[z524,z8,z2,z161,z5,z6])],[(0,[z0,z76,z8,z99,z5,z6]),(0,[z0,z487,z8,z72,z5,z6]),(0,[z0,z540,z8,z3,z165,z6]),(0,[z0,z8,z2,z91,z5,z578])],[(0,[z1036,z0,z8,z2,z3,z5]),(0,[z0,z8,z2,z3,z370,z6]),(0,[z0,z8,z3,z5,z470,z43]),(0,[z0,z8,z2,z1037,z5,z6]),(0,[z0,z8,z3,z5,z1038,z6])],[(0,[z0,z37,z8,z596,z5,z6]),(0,[z0,z8,z2,z99,z5,z6])],[(0,[z126,z2,z3,z5,z390,z6]),(0,[z147,z8,z2,z205,z5,z6]),(0,[z376,z8,z2,z205,z5,z6]),(0,[z0,z76,z861,z3,z5,z6])],[(0,[z0,z2,z3,z5,z499,z78]),(0,[z0,z8,z2,z1039,z5,z6]),(0,[z0,z1040,z8,z3,z5,z6]),(0,[z0,z1041,z2,z3,z5,z6]),(0,[z8,z2,z769,z205,z5,z6]),(0,[z106,z8,z3,z5,z17,z129]),(0,[z1042,z8,z2,z3,z5,z6])],[(0,[z143,z8,z2,z3,z5,z232]),(0,[z70,z121,z71,z2,z5,z6]),(0,[z0,z8,z2,z156,z5,z6]),(0,[z0,z113,z2,z3,z5,z6]),(0,[z81,z0,z8,z5,z6,z182])],[(0,[z0,z22,z8,z32,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z128]),(0,[z0,z8,z2,z1043,z5,z6]),(0,[z83,z18,z8,z154,z5,z6]),(0,[z0,z23,z101,z2,z5,z6]),(0,[z217,z0,z8,z2,z49,z6]),(0,[z0,z8,z2,z1044,z5,z6]),(0,[z0,z8,z209,z5,z6,z43])],[(0,[z1045,z0,z8,z3,z5,z6]),(0,[z0,z1046,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z1047,z6]),(0,[z92,z8,z197,z3,z5,z6]),(0,[z445,z217,z0,z8,z5,z6]),(0,[z0,z8,z2,z5,z6,z1048]),(0,[z1049,z8,z2,z3,z5,z6]),(0,[z0,z8,z284,z161,z5,z6])],[(0,[z0,z18,z8,z2,z5,z6]),(0,[z0,z8,z32,z5,z6,z187]),(0,[z138,z8,z2,z769,z5,z6]),(0,[z0,z22,z2,z82,z5,z6]),(0,[z0,z8,z534,z49,z5,z6])],[(0,[z83,z540,z8,z3,z5,z6]),(0,[z0,z273,z2,z51,z5,z6]),(0,[z0,z8,z2,z1050,z5,z6]),(0,[z0,z8,z2,z1051,z5,z6]),(0,[z0,z8,z25,z108,z109,z6])],[(0,[z70,z0,z2,z316,z5,z6]),(0,[z0,z8,z1052,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z1053]),(0,[z0,z155,z346,z3,z5,z6]),(0,[z0,z8,z2,z5,z6,z1054]),(0,[z0,z8,z2,z1055,z5,z6]),(0,[z0,z76,z140,z335,z5,z6]),(0,[z0,z8,z2,z1056,z5,z6]),(0,[z0,z8,z316,z5,z423,z6]),(0,[z0,z8,z2,z3,z29,z713])],[(0,[z0,z8,z1057,z3,z5,z6]),(0,[z0,z8,z1058,z3,z5,z6]),(0,[z0,z8,z2,z97,z5,z6]),(0,[z0,z23,z8,z74,z5,z6]),(0,[z1059,z8,z2,z3,z5,z6])],[(0,[z8,z2,z3,z5,z17,z396]),(0,[z0,z8,z2,z105,z323,z6]),(0,[z0,z150,z23,z2,z5,z6])]],
   [[(0,[z0,z8,z2,z3,z6,z1060]),(0,[z8,z2,z3,z769,z5,z6]),(1,[z8,z2,z3,z726,z6]),(0,[z8,z2,z3,z726,z56,z6]),(0,[z222,z0,z2,z3,z5,z78]),(0,[z0,z8,z74,z91,z5,z6]),(0,[z0,z1061,z2,z3,z5,z6])],[(0,[z8,z2,z3,z5,z17,z822]),(0,[z7,z0,z2,z3,z712,z6])],[(0,[z0,z8,z2,z1062,z5,z6]),(0,[z81,z8,z3,z5,z6,z294]),(0,[z24,z0,z8,z3,z5,z43]),(0,[z0,z8,z175,z5,z86,z6])],[(0,[z0,z273,z55,z3,z5,z6]),(0,[z477,z0,z8,z2,z86,z6]),(0,[z0,z1063,z2,z3,z5,z6]),(0,[z122,z0,z2,z3,z5,z78]),(0,[z0,z1,z410,z3,z5,z6]),(0,[z1064,z0,z8,z3,z5,z6]),(0,[z0,z8,z119,z5,z165,z6]),(0,[z0,z8,z2,z1065,z5,z6]),(0,[z0,z68,z198,z3,z5,z6])],[(0,[z0,z8,z1066,z3,z5,z6]),(0,[z8,z715,z154,z3,z5,z6]),(0,[z0,z8,z1067,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z300]),(0,[z0,z8,z2,z5,z1068,z6]),(0,[z261,z0,z8,z3,z165,z6])],[(0,[z0,z8,z1069,z3,z5,z6]),(0,[z1070,z0,z8,z3,z5,z6]),(0,[z0,z8,z1071,z3,z5,z6]),(0,[z1072,z8,z2,z3,z5,z6]),(0,[z0,z8,z1073,z3,z5,z6]),(0,[z0,z8,z2,z1074,z5,z6])],[(0,[z0,z8,z2,z1075,z5,z6]),(0,[z62,z8,z2,z241,z56,z6]),(0,[z557,z8,z2,z3,z56,z6]),(0,[z0,z8,z2,z1076,z5,z6]),(0,[z106,z8,z2,z3,z5,z822]),(0,[z0,z1077,z2,z3,z5,z6]),(1,[z0,z8,z3,z933,z6])],[(0,[z0,z8,z2,z31,z5,z6]),(0,[z62,z8,z3,z33,z56,z6]),(0,[z592,z139,z0,z3,z5,z6])]],
   [[(0,[z206,z8,z2,z3,z173,z6]),(0,[z0,z41,z2,z3,z598,z6]),(0,[z0,z8,z2,z1078,z5,z6])],[(0,[z147,z8,z2,z769,z5,z6]),(0,[z1079,z0,z8,z3,z5,z6]),(0,[z524,z8,z198,z3,z5,z6])],[(0,[z0,z8,z2,z1080,z5,z6]),(0,[z250,z0,z18,z2,z5,z6]),(0,[z0,z2,z1081,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1082]),(0,[z8,z2,z3,z5,z1083,z6])],[(0,[z0,z8,z2,z1084,z5,z6]),(0,[z0,z1085,z8,z2,z5,z6]),(0,[z62,z8,z2,z3,z63,z56]),(0,[z0,z8,z2,z1086,z5,z6]),(0,[z81,z0,z8,z3,z6,z164]),(0,[z0,z8,z2,z751,z86,z6])],[(0,[z70,z37,z71,z2,z5,z6]),(0,[z70,z521,z2,z3,z5,z6]),(0,[z217,z0,z8,z2,z323,z6]),(0,[z1087,z0,z8,z2,z3,z6]),(0,[z62,z8,z2,z3,z726,z6]),(0,[z269,z0,z8,z2,z3,z5]),(0,[z0,z8,z2,z3,z5,z1088]),(0,[z1089,z0,z2,z3,z5,z6]),(0,[z0,z8,z3,z1090,z5,z6]),(0,[z0,z1091,z2,z3,z5,z6])],[(0,[z0,z8,z2,z3,z1092,z6])],[(0,[z0,z41,z2,z316,z9,z6]),(0,[z0,z8,z3,z6,z58,z164]),(0,[z0,z8,z1093,z3,z5,z6])],[(0,[z1094,z0,z8,z3,z5,z6]),(0,[z8,z2,z3,z5,z390,z6]),(0,[z0,z1095,z2,z3,z5,z6]),(0,[z147,z0,z273,z2,z5,z6]),(0,[z1096,z8,z2,z3,z5,z6]),(0,[z0,z8,z53,z48,z5,z6]),(0,[z0,z8,z2,z5,z812,z187])]],
   [[(0,[z0,z2,z3,z1097,z5,z6]),(0,[z0,z8,z2,z1098,z5,z6]),(0,[z0,z8,z3,z5,z1099,z6]),(0,[z0,z8,z45,z330,z5,z6]),(0,[z12,z524,z8,z2,z3,z13]),(0,[z0,z8,z284,z230,z5,z6])],[(0,[z126,z0,z150,z2,z5,z6]),(0,[z0,z2,z1100,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1101])],[(0,[z61,z0,z37,z8,z5,z6]),(0,[z0,z8,z1102,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z1103]),(0,[z138,z0,z155,z8,z5,z6]),(0,[z0,z1104,z2,z3,z5,z6]),(0,[z0,z8,z3,z933,z165,z6])],[(0,[z127,z2,z3,z5,z327,z6]),(0,[z12,z0,z8,z2,z230,z13]),(0,[z12,z0,z8,z2,z3,z713])],[(0,[z126,z0,z37,z2,z5,z6]),(0,[z0,z22,z8,z74,z5,z6]),(0,[z0,z8,z45,z3,z5,z767])],[(0,[z1105,z0,z8,z2,z5,z6]),(0,[z0,z8,z3,z5,z297,z6]),(0,[z0,z113,z2,z209,z5,z6]),(0,[z258,z68,z2,z3,z5,z6])],[(0,[z0,z292,z140,z3,z5,z6]),(0,[z0,z8,z1106,z3,z5,z6]),(0,[z0,z116,z8,z330,z5,z6]),(0,[z0,z8,z2,z161,z5,z6])],[(0,[z0,z8,z2,z1107,z5,z6]),(0,[z0,z8,z1108,z3,z5,z6]),(0,[z0,z8,z2,z1109,z5,z6])]],
   [[(0,[z70,z61,z71,z3,z5,z6]),(0,[z162,z217,z0,z2,z5,z6]),(0,[z0,z1110,z8,z3,z5,z6]),(0,[z0,z8,z2,z1111,z5,z6]),(0,[z0,z8,z2,z1112,z5,z6])],[(0,[z0,z8,z2,z3,z5,z1113]),(0,[z595,z8,z154,z3,z5,z6]),(0,[z147,z8,z2,z579,z5,z6]),(0,[z0,z2,z485,z5,z6,z78]),(0,[z0,z519,z8,z72,z5,z6])],[(0,[z70,z0,z112,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z1114]),(0,[z83,z8,z154,z3,z267,z6]),(0,[z143,z8,z2,z3,z5,z259]),(0,[z8,z2,z5,z390,z130,z6]),(0,[z0,z8,z2,z1115,z5,z6]),(0,[z0,z2,z3,z5,z6,z781]),(0,[z0,z8,z175,z72,z5,z6])],[(0,[z0,z8,z3,z5,z6,z1116]),(0,[z250,z0,z53,z3,z5,z6]),(0,[z0,z18,z8,z53,z5,z6]),(0,[z2,z3,z5,z327,z390,z6]),(0,[z0,z8,z2,z1117,z5,z6]),(0,[z0,z8,z410,z199,z5,z6]),(0,[z0,z1118,z2,z3,z5,z6]),(0,[z0,z1119,z2,z3,z5,z6])],[(0,[z0,z8,z2,z1120,z5,z6]),(0,[z8,z2,z3,z224,z56,z6]),(0,[z139,z0,z177,z3,z5,z6]),(0,[z0,z8,z2,z5,z6,z1121]),(0,[z0,z8,z3,z1122,z5,z6]),(0,[z0,z8,z74,z5,z6,z187])],[(0,[z70,z550,z2,z3,z5,z6]),(0,[z0,z8,z2,z1123,z5,z6]),(0,[z0,z8,z32,z3,z323,z6]),(0,[z0,z8,z2,z5,z6,z1124]),(0,[z0,z8,z2,z91,z5,z291]),(0,[z8,z2,z3,z5,z1125,z6]),(0,[z256,z0,z8,z3,z5,z43]),(0,[z0,z8,z3,z108,z933,z6])],[(0,[z0,z8,z53,z590,z5,z6]),(0,[z0,z8,z3,z5,z423,z6]),(0,[z0,z8,z2,z1126,z5,z6]),(0,[z0,z354,z2,z4,z5,z6]),(0,[z1127,z8,z2,z3,z5,z6]),(0,[z0,z460,z2,z358,z5,z6]),(0,[z0,z8,z3,z5,z1128,z6])],[(0,[z70,z2,z3,z5,z327,z6]),(0,[z0,z2,z254,z3,z5,z6]),(0,[z0,z1129,z2,z3,z5,z6]),(0,[z122,z0,z2,z199,z5,z78]),(0,[z0,z116,z8,z5,z349,z6]),(0,[z0,z1130,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z596,z3,z5,z6]),(0,[z0,z8,z48,z3,z267,z6]),(0,[z0,z273,z2,z5,z86,z6]),(0,[z0,z8,z2,z3,z5,z1131]),(0,[z0,z1132,z8,z2,z5,z6])],[(0,[z0,z8,z53,z2,z323,z6]),(0,[z0,z8,z338,z3,z207,z6]),(0,[z0,z8,z2,z51,z459,z6]),(0,[z0,z8,z175,z51,z5,z6]),(0,[z0,z1133,z8,z3,z5,z6])],[(0,[z70,z559,z2,z3,z5,z6]),(0,[z0,z8,z2,z1134,z5,z6]),(0,[z138,z0,z8,z175,z5,z6]),(0,[z0,z8,z1135,z2,z5,z6]),(0,[z1136,z0,z8,z2,z3,z6]),(0,[z0,z8,z2,z664,z86,z6]),(0,[z0,z8,z1137,z3,z5,z6])],[(0,[z0,z116,z8,z2,z323,z6]),(0,[z139,z0,z8,z330,z5,z6]),(0,[z0,z23,z8,z534,z5,z6]),(0,[z0,z23,z266,z2,z5,z6]),(0,[z237,z122,z0,z2,z3,z78]),(0,[z0,z8,z2,z119,z5,z6]),(0,[z0,z8,z1138,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z1139])],[(0,[z0,z8,z1140,z3,z5,z6]),(0,[z0,z2,z225,z5,z6,z128])],[(0,[z0,z8,z2,z3,z5,z1141]),(0,[z0,z8,z1142,z3,z5,z6]),(0,[z0,z8,z2,z3,z1143,z6]),(0,[z147,z273,z2,z205,z5,z6]),(0,[z147,z625,z8,z2,z5,z6]),(0,[z0,z8,z2,z1144,z5,z6])],[(0,[z237,z126,z0,z2,z3,z6]),(0,[z0,z1145,z8,z2,z5,z6]),(1,[z0,z861,z3,z5,z6]),(0,[z0,z8,z2,z3,z1146,z6])],[(0,[z126,z127,z2,z3,z5,z6]),(0,[z0,z8,z2,z1147,z5,z6]),(0,[z445,z0,z8,z3,z267,z6]),(0,[z0,z2,z3,z5,z6,z1148]),(0,[z0,z23,z2,z79,z5,z6])]],
   [[(0,[z70,z2,z3,z5,z390,z6]),(0,[z0,z8,z20,z3,z5,z6]),(0,[z0,z8,z2,z1149,z5,z6]),(0,[z0,z8,z53,z534,z5,z6]),(0,[z73,z0,z8,z283,z5,z187]),(0,[z1150,z0,z8,z3,z5,z6])],[(0,[z0,z8,z2,z3,z1151,z6]),(0,[z83,z8,z154,z3,z370,z6]),(0,[z92,z8,z3,z5,z6,z342]),(0,[z0,z8,z2,z3,z5,z1152]),(0,[z376,z0,z116,z8,z5,z6]),(0,[z0,z8,z1153,z3,z5,z6]),(0,[z0,z8,z2,z3,z713,z13])],[(0,[z61,z0,z8,z3,z5,z6]),(0,[z0,z8,z3,z108,z267,z6]),(0,[z0,z8,z1154,z3,z5,z6]),(0,[z0,z41,z2,z3,z9,z6])],[(0,[z0,z8,z2,z1155,z5,z6]),(0,[z0,z116,z8,z32,z5,z6]),(0,[z0,z8,z1156,z3,z5,z6]),(0,[z0,z41,z112,z3,z9,z6]),(0,[z145,z0,z8,z3,z933,z6])],[(0,[z269,z0,z8,z2,z5,z241]),(0,[z0,z8,z1157,z3,z5,z6]),(0,[z0,z8,z2,z591,z49,z6]),(0,[z0,z8,z2,z230,z5,z6])],[(0,[z0,z8,z2,z5,z1158,z6]),(0,[z0,z1159,z2,z3,z5,z6])],[(0,[z0,z8,z2,z1160,z5,z6]),(0,[z0,z1161,z8,z2,z5,z6]),(0,[z445,z0,z3,z5,z327,z6]),(0,[z0,z8,z2,z3,z5,z812])],[(0,[z0,z1162,z8,z3,z5,z6]),(0,[z0,z1163,z2,z3,z5,z6]),(0,[z0,z8,z1164,z3,z5,z6]),(0,[z0,z2,z4,z5,z6,z663]),(0,[z0,z2,z103,z743,z5,z6]),(0,[z0,z41,z2,z9,z130,z6])]],
   [[(0,[z92,z0,z18,z8,z5,z6]),(0,[z143,z8,z2,z3,z5,z822]),(0,[z0,z96,z16,z3,z5,z6]),(0,[z0,z8,z3,z168,z165,z6])],[(0,[z250,z0,z3,z5,z165,z6]),(0,[z0,z8,z338,z3,z5,z6]),(0,[z0,z1165,z2,z3,z5,z6]),(0,[z524,z8,z2,z3,z5,z6]),(0,[z0,z2,z5,z6,z128,z274]),(0,[z0,z8,z72,z509,z5,z6]),(0,[z524,z110,z2,z3,z5,z6]),(0,[z0,z8,z198,z161,z5,z6])],[(0,[z0,z8,z2,z1166,z5,z6]),(0,[z0,z8,z3,z108,z293,z6]),(0,[z90,z8,z2,z205,z5,z6]),(0,[z580,z0,z8,z2,z86,z6]),(0,[z62,z217,z8,z2,z56,z6])],[(0,[z0,z8,z2,z1167,z5,z6]),(0,[z0,z8,z16,z3,z5,z6]),(0,[z0,z573,z283,z3,z5,z6])],[(0,[z0,z8,z2,z1168,z5,z6]),(0,[z0,z1169,z2,z3,z5,z6]),(0,[z0,z273,z155,z3,z5,z6]),(0,[z0,z8,z1170,z3,z5,z6]),(0,[z0,z861,z94,z3,z5,z6]),(0,[z0,z8,z1171,z3,z5,z6]),(0,[z0,z460,z3,z5,z6,z43])],[(0,[z0,z8,z2,z3,z1172,z6]),(0,[z62,z8,z2,z156,z56,z6]),(0,[z0,z8,z345,z3,z5,z6]),(0,[z0,z8,z214,z3,z5,z6])],[(0,[z0,z8,z91,z534,z5,z6])],[(0,[z0,z2,z3,z1173,z5,z6]),(0,[z0,z8,z2,z5,z6,z1174]),(0,[z8,z2,z3,z5,z1175,z6]),(0,[z0,z8,z1176,z3,z5,z6]),(0,[z0,z8,z2,z1177,z5,z6])]],
   [[(0,[z145,z0,z8,z3,z267,z6]),(0,[z0,z273,z2,z72,z5,z6]),(0,[z1178,z0,z8,z3,z5,z6]),(0,[z0,z22,z2,z287,z5,z6]),(0,[z0,z8,z2,z5,z109,z6]),(0,[z0,z8,z2,z1179,z5,z6]),(0,[z0,z266,z2,z91,z5,z6])],[(0,[z0,z37,z8,z2,z5,z6]),(0,[z0,z8,z2,z3,z1180,z6]),(0,[z0,z8,z2,z56,z109,z6]),(0,[z0,z22,z8,z534,z5,z6]),(0,[z0,z22,z266,z2,z5,z6]),(0,[z0,z8,z2,z330,z5,z6])],[(0,[z642,z0,z22,z2,z5,z6]),(0,[z0,z8,z2,z1181,z5,z6]),(0,[z237,z0,z2,z3,z169,z6]),(0,[z0,z8,z2,z51,z509,z6]),(0,[z0,z8,z25,z3,z933,z6])],[(0,[z70,z237,z0,z2,z3,z6]),(1,[z8,z715,z3,z5,z6]),(0,[z0,z1182,z8,z2,z5,z6]),(0,[z0,z8,z2,z1183,z5,z6]),(0,[z190,z0,z94,z3,z5,z6]),(0,[z0,z8,z284,z3,z5,z6]),(0,[z0,z8,z45,z3,z5,z46])],[(0,[z0,z8,z2,z3,z1184,z6]),(0,[z0,z8,z2,z99,z267,z6]),(0,[z0,z22,z320,z2,z5,z6]),(0,[z0,z8,z3,z5,z6,z1185]),(0,[z0,z8,z112,z316,z5,z6])],[(0,[z0,z8,z2,z3,z5,z767])],[(0,[z0,z8,z2,z1186,z5,z6]),(0,[z0,z8,z335,z5,z6,z43]),(0,[z1187,z8,z2,z3,z5,z6]),(0,[z0,z8,z3,z5,z1188,z6])],[(0,[z0,z8,z2,z5,z1189,z6]),(0,[z0,z155,z8,z48,z5,z6]),(0,[z0,z8,z1190,z3,z5,z6]),(0,[z1191,z0,z8,z2,z5,z6])]],
   [[(0,[z0,z8,z2,z3,z1192,z6]),(0,[z0,z8,z2,z1193,z5,z6]),(0,[z0,z8,z32,z49,z5,z6]),(0,[z0,z8,z135,z48,z5,z6])],[(0,[z1194,z0,z8,z3,z5,z6]),(0,[z122,z0,z2,z3,z164,z78]),(0,[z0,z8,z45,z3,z5,z11])],[(0,[z0,z8,z410,z3,z5,z6]),(0,[z0,z22,z8,z242,z5,z6]),(0,[z145,z0,z8,z3,z299,z6])],[(0,[z83,z8,z19,z154,z5,z6]),(0,[z0,z8,z3,z5,z6,z1195]),(0,[z0,z8,z3,z5,z1196,z6])],[(0,[z138,z0,z273,z2,z5,z6]),(0,[z0,z1197,z8,z2,z5,z6]),(0,[z0,z8,z1198,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z1199]),(0,[z1200,z0,z8,z3,z5,z6]),(0,[z148,z0,z8,z2,z751,z6])],[(0,[z70,z0,z150,z2,z5,z6]),(0,[z148,z0,z8,z2,z323,z6]),(0,[z0,z8,z2,z91,z5,z553]),(0,[z0,z8,z1201,z3,z5,z6]),(0,[z0,z8,z2,z3,z1202,z6]),(0,[z1203,z8,z2,z3,z5,z6])],[(0,[z0,z8,z1204,z3,z5,z6]),(0,[z0,z8,z19,z2,z5,z6]),(0,[z1205,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z1206,z6]),(0,[z0,z8,z2,z3,z712,z6]),(0,[z0,z41,z68,z2,z3,z6]),(0,[z0,z113,z2,z358,z5,z6]),(0,[z0,z8,z51,z534,z49,z6])],[(0,[z269,z8,z2,z3,z5,z259]),(0,[z0,z2,z743,z4,z5,z6]),(0,[z0,z8,z2,z3,z1207,z6]),(0,[z1208,z0,z8,z2,z5,z6]),(0,[z0,z8,z198,z230,z5,z6])]],
   [[(0,[z70,z0,z37,z2,z5,z6]),(0,[z145,z0,z8,z99,z5,z6]),(0,[z139,z0,z460,z3,z5,z6]),(0,[z12,z0,z8,z2,z3,z328]),(0,[z0,z2,z3,z9,z712,z6])],[(0,[z126,z0,z2,z97,z5,z6]),(0,[z83,z0,z8,z119,z5,z6]),(0,[z0,z19,z2,z254,z5,z6]),(0,[z0,z1209,z2,z3,z5,z6])],[(0,[z0,z18,z2,z254,z5,z6]),(0,[z0,z8,z2,z1210,z5,z6]),(0,[z42,z0,z8,z3,z5,z684]),(0,[z0,z8,z2,z51,z49,z6])],[(0,[z0,z8,z3,z5,z6,z1211]),(0,[z0,z8,z2,z3,z1212,z6]),(0,[z0,z8,z2,z99,z370,z6]),(0,[z0,z8,z1213,z3,z5,z6]),(0,[z0,z8,z2,z3,z1214,z6]),(0,[z8,z2,z1215,z3,z5,z6])],[(0,[z47,z8,z2,z3,z207,z6]),(0,[z0,z8,z118,z72,z5,z6]),(0,[z0,z140,z861,z3,z5,z6]),(0,[z0,z8,z718,z72,z5,z6]),(0,[z0,z8,z175,z330,z5,z6]),(0,[z0,z8,z2,z1216,z5,z6]),(0,[z0,z8,z1217,z2,z5,z6]),(0,[z0,z8,z1218,z3,z5,z6])],[(0,[z148,z0,z8,z32,z5,z6]),(0,[z0,z8,z1219,z3,z5,z6]),(0,[z0,z8,z3,z591,z108,z6]),(0,[z0,z8,z45,z209,z5,z6])],[(0,[z0,z777,z2,z3,z5,z6]),(0,[z0,z8,z1220,z3,z5,z6]),(0,[z0,z140,z447,z3,z5,z6]),(0,[z269,z127,z8,z2,z3,z5]),(0,[z138,z8,z505,z2,z5,z6]),(0,[z138,z8,z2,z5,z67,z6]),(0,[z0,z2,z3,z5,z300,z781])],[(0,[z0,z18,z8,z72,z5,z6]),(0,[z0,z76,z251,z3,z5,z6]),(0,[z0,z8,z2,z75,z5,z6]),(0,[z0,z8,z861,z3,z5,z6]),(0,[z0,z8,z1221,z3,z5,z6]),(0,[z0,z410,z3,z5,z6,z78]),(1,[z0,z2,z3,z5,z781]),(0,[z0,z1222,z2,z3,z5,z6]),(0,[z0,z1223,z2,z3,z5,z6])]],
   [[(0,[z0,z8,z2,z1224,z5,z6]),(0,[z0,z8,z2,z31,z267,z6]),(0,[z0,z1225,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z1226]),(0,[z0,z8,z2,z1227,z5,z6]),(0,[z1228,z8,z2,z3,z5,z6])],[(0,[z0,z8,z32,z3,z324,z6]),(0,[z435,z0,z8,z72,z5,z6]),(0,[z0,z8,z214,z199,z5,z6]),(0,[z24,z0,z8,z2,z5,z187]),(0,[z0,z8,z53,z5,z626,z6]),(0,[z0,z8,z1229,z3,z5,z6])],[(0,[z70,z71,z2,z3,z5,z6]),(0,[z0,z8,z2,z1230,z5,z6]),(0,[z0,z8,z99,z108,z5,z6]),(0,[z0,z8,z2,z5,z1231,z6]),(0,[z0,z8,z2,z323,z6,z187]),(0,[z0,z2,z3,z5,z1232,z6]),(0,[z1233,z0,z2,z3,z5,z6])],[(0,[z0,z8,z2,z1234,z5,z6]),(0,[z0,z8,z1235,z3,z5,z6]),(0,[z206,z8,z2,z3,z726,z6]),(0,[z1236,z0,z8,z3,z5,z6]),(0,[z0,z8,z1237,z3,z5,z6]),(0,[z12,z0,z8,z198,z3,z13])],[(0,[z0,z96,z2,z3,z5,z6]),(0,[z0,z8,z1238,z3,z5,z6]),(0,[z0,z22,z2,z4,z5,z6]),(0,[z77,z8,z3,z5,z6,z58]),(0,[z0,z1239,z2,z3,z5,z6]),(0,[z0,z266,z2,z5,z6,z187])],[(0,[z0,z2,z3,z5,z6,z1240]),(0,[z0,z41,z2,z3,z712,z6]),(0,[z8,z3,z5,z390,z423,z6])],[(0,[z0,z8,z2,z1241,z5,z6]),(0,[z0,z8,z186,z330,z5,z6]),(0,[z0,z1242,z2,z3,z5,z6]),(0,[z42,z0,z8,z3,z5,z767])],[(0,[z0,z8,z2,z49,z15,z6]),(0,[z0,z8,z2,z3,z5,z1243]),(0,[z81,z0,z76,z3,z5,z6]),(1,[z0,z8,z718,z5,z6]),(0,[z0,z8,z2,z5,z6,z1244]),(0,[z0,z8,z3,z5,z6,z1245])]],
   [[(0,[z0,z8,z2,z1246,z5,z6]),(0,[z0,z8,z3,z5,z1247,z6]),(0,[z0,z1248,z2,z3,z5,z6]),(0,[z0,z1249,z2,z3,z5,z6]),(0,[z0,z8,z16,z225,z5,z6]),(0,[z0,z8,z112,z3,z5,z6]),(0,[z0,z23,z103,z242,z5,z6]),(0,[z0,z8,z242,z5,z6,z187]),(0,[z0,z8,z1250,z3,z5,z6])],[(0,[z139,z416,z0,z3,z5,z6]),(0,[z0,z1251,z2,z3,z5,z6]),(0,[z0,z8,z2,z205,z323,z6]),(0,[z12,z0,z8,z2,z3,z167]),(0,[z0,z8,z1252,z3,z5,z6]),(0,[z0,z16,z3,z5,z6,z128]),(0,[z0,z8,z1253,z3,z5,z6]),(0,[z0,z8,z2,z1254,z5,z6]),(0,[z258,z8,z2,z230,z5,z6]),(0,[z0,z110,z2,z161,z5,z6])],[(0,[z0,z8,z1255,z3,z5,z6]),(0,[z0,z3,z5,z33,z327,z6]),(0,[z0,z96,z3,z5,z6,z129]),(0,[z306,z8,z3,z5,z423,z6])],[(0,[z0,z8,z2,z3,z1256,z6]),(0,[z126,z777,z2,z3,z5,z6]),(0,[z0,z18,z8,z25,z5,z6]),(0,[z1257,z0,z8,z3,z5,z6]),(0,[z8,z2,z105,z769,z5,z6]),(0,[z0,z1258,z2,z3,z5,z6]),(0,[z0,z8,z2,z1259,z5,z6]),(0,[z0,z8,z1260,z3,z5,z6])],[(0,[z0,z8,z32,z105,z5,z6]),(0,[z0,z76,z140,z97,z5,z6]),(0,[z0,z8,z2,z1261,z5,z6]),(0,[z0,z8,z1262,z3,z5,z6]),(0,[z0,z23,z2,z5,z438,z6]),(0,[z1263,z0,z2,z3,z5,z6])],[(0,[z83,z250,z0,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z129]),(0,[z0,z8,z1264,z3,z5,z6]),(0,[z0,z8,z2,z1265,z5,z6]),(0,[z0,z581,z2,z4,z5,z6]),(0,[z0,z8,z2,z5,z130,z6]),(0,[z0,z8,z175,z51,z49,z6]),(0,[z0,z8,z2,z51,z751,z6])],[(0,[z640,z0,z116,z8,z5,z6]),(0,[z0,z8,z25,z3,z191,z6]),(0,[z237,z0,z8,z2,z3,z6]),(0,[z0,z8,z112,z5,z130,z6]),(0,[z12,z258,z8,z2,z3,z13])],[(0,[z77,z8,z2,z3,z5,z6]),(0,[z0,z8,z2,z31,z370,z6]),(0,[z0,z8,z715,z3,z5,z6]),(0,[z0,z8,z2,z3,z1266,z6]),(0,[z237,z8,z2,z3,z6,z294]),(0,[z0,z8,z2,z1267,z5,z6]),(0,[z0,z8,z2,z3,z5,z713])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 535).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1057).take 137) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1194)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [535, 522, 137] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 106).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 106).take 98).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 204).take 52).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [106, 98, 52] = true :=
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

end PEqualNP.Outside.L_meta_37445

theorem PEqualNP.Outside.L_meta_37445 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4007717600 * 2 ^ 32 + 3940608192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37445.solve