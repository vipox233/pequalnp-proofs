import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38433

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
  Nat.testBit (4008372906 * 2 ^ 32 + 3972057216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x800215092a7c621b#64 ++ 0xef463f1ffefc623f#64 : BitVec 128),
   (0x8418cc649805aced#64 ++ 0xffb9cce4990fffff#64 : BitVec 128),
   (0x10c170b8e1b05746#64 ++ 0xb7c1f0f8e1f07fc7#64 : BitVec 128),
   (0x09ee00df01da83b0#64 ++ 0x7dfe00ff01ff83f8#64 : BitVec 128),
   (0x22f7bf0001ef7800#64 ++ 0x3effff0001fffc00#64 : BitVec 128),
   (0x03fdeaf6d4000000#64 ++ 0x3bfffffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [7, 6]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0802000901da83b0 0x4400000001ff83f8

def z1 : W := mkw 0x09ee00df01da83b0 0x7dfe00ff01ff83f8

def z2 : W := mkw 0x10c170b8e1b05746 0xb7c1f0f8e1f07fc7

def z3 : W := mkw 0x22f7bf0001ef7800 0x3effff0001fffc00

def z4 : W := mkw 0x800215092a7c621b 0xc400000000fc623f

def z5 : W := mkw 0x800215092a7c621b 0xef463f1ffefc623f

def z6 : W := mkw 0x8418cc649805aced 0xffb9cce4990fffff

def z7 : W := mkw 0x0000000000000000 0x2b463f1ffe000000

def z8 : W := mkw 0x10c170b8e1b05746 0x9481c0e001f07fc7

def z9 : W := mkw 0x00108c0000052800 0x3eb9cc00010ffc00

def z10 : W := mkw 0x03fdeaf6d4000000 0x3bfffffffe000000

def z11 : W := mkw 0x840004000805aced 0xef000c04990fffff

def z12 : W := mkw 0x0000100820304202 0x8400000000f06207

def z13 : W := mkw 0x0000009800100300 0x010000f8000003c0

def z14 : W := mkw 0x8d0840ff981087fd 0xc10000ff980003ff

def z15 : W := mkw 0x090a00df005883b0 0x6d4600ff00fc03f8

def z16 : W := mkw 0x1000100821b05746 0x8400000001f07fc7

def z17 : W := mkw 0x13fdfafef5b05746 0xbffffffffff07fc7

def z18 : W := mkw 0x810a55fffe7c621b 0xef463ffffefc623f

def z19 : W := mkw 0x8418cc649805aced 0x92b9cce09903fdc7

def z20 : W := mkw 0x01ec00d600000000 0x3bfe3ffffe000000

def z21 : W := mkw 0x89ee15df2bfee3bb 0xfffe3fffffffe3ff

def z22 : W := mkw 0x9418dc6cb9b5ffef 0xffb9cce499ffffff

def z23 : W := mkw 0x87fffffffe7deeff 0xffffffffffffffff

def z24 : W := mkw 0x0002000000480000 0x2c46000000fc0000

def z25 : W := mkw 0x80c335092bfc721b 0xffc7ff1ffffc7e3f

def z26 : W := mkw 0x880215092bfee3bb 0xef463f1fffffe3ff

def z27 : W := mkw 0x0000402080000000 0x3381c0e080000000

def z28 : W := mkw 0x800000010a000019 0x400000071e000038

def z29 : W := mkw 0x100040b0c0000544 0x000000e0000001c0

def z30 : W := mkw 0x0002110922784212 0x0046331b66f00000

def z31 : W := mkw 0x0418c86490018ce4 0x10b9c0e001039dc0

def z32 : W := mkw 0x0bffeaffd5da83b0 0x7fffffffffff83f8

def z33 : W := mkw 0x0802000901da0310 0x0000000000f00000

def z34 : W := mkw 0x800015092a34621b 0xc3003f1ffe00623f

def z35 : W := mkw 0x03fdeaf6d4000000 0x11b9c0fffe000000

def z36 : W := mkw 0x0000402080000444 0x1081c0e001001dc0

def z37 : W := mkw 0x2000150000257800 0x0000000000007c00

def z38 : W := mkw 0x090a00df01da83b0 0x450000ff01ff83f8

def z39 : W := mkw 0x23fffff6d5ef7800 0x3ffffffffffffc00

def z40 : W := mkw 0x00080044000080a0 0x7db800e4010f83f8

def z41 : W := mkw 0x8dfeccff99dfaffd 0xffffccff99ffffff

def z42 : W := mkw 0x8018cc6498042009 0xffb9cce4980c623f

def z43 : W := mkw 0x19ef70ffe1fad7f6 0xfffff0ffe1ffffff

def z44 : W := mkw 0x190840ffe01087f6 0xc10000ffe00003ff

def z45 : W := mkw 0x0219ea64d4000000 0x3bb9ffe4fe000000

def z46 : W := mkw 0x84188c441805a8a9 0x48380c04180f8038

def z47 : W := mkw 0x94d9fcfcf9b5ffef 0xfff9fcfcf9ffffff

def z48 : W := mkw 0xa00215092bff7a1b 0xc400000001fffe3f

def z49 : W := mkw 0x840844649804a4ed 0xef000ce4980c63ff

def z50 : W := mkw 0x0b3e8a47144a80b0 0x483e0f071e0f8038

def z51 : W := mkw 0x033c8a4614000000 0x083e0f071e000000

def z52 : W := mkw 0x0000000000000000 0x0000000000000000

def z53 : W := mkw 0x10005028a1b05746 0xb781c0e081f07fc7

def z54 : W := mkw 0x00c0009001800100 0x108000e0010001c0

def z55 : W := mkw 0x03fdeaf6d4000000 0x10fff3fb66000000

def z56 : W := mkw 0xa2f7bf092bff7a1b 0xfeffff0001fffe3f

def z57 : W := mkw 0x0002110922784212 0x0000000000f00000

def z58 : W := mkw 0x09ec00de019283a0 0x35f800f801f383c0

def z59 : W := mkw 0x09ee00df01da83b0 0x487e001f00ff8038

def z60 : W := mkw 0x010840f6d4000000 0x2b463ffffe000000

def z61 : W := mkw 0x0211aa0000000000 0x0201ff0000000000

def z62 : W := mkw 0x84084064980084ed 0xc10000e4980003ff

def z63 : W := mkw 0x99ef75ffebfef7ff 0xffffffffffffffff

def z64 : W := mkw 0x100040b8e0100746 0x810000f8e00003c7

def z65 : W := mkw 0xa2f7bf092bff7a1b 0xffffff1ffffffe3f

def z66 : W := mkw 0x8dfe8cdf19dfabb9 0x7dfe0cff19ff83f8

def z67 : W := mkw 0x09e6009b01da0310 0x6d46001f00fc0238

def z68 : W := mkw 0x0211ea20d4000000 0x0201ff00fe000000

def z69 : W := mkw 0x22f68f0001cf2800 0x3cfe0f0001ff8000

def z70 : W := mkw 0x0000402080000444 0xb781c0e081007fc7

def z71 : W := mkw 0x800205010a4c2019 0x48060f071e0c0038

def z72 : W := mkw 0x841a9d4d3a7deabb 0xef7e3f1ffeffe23f

def z73 : W := mkw 0x10c160b8e1901746 0x9181c0f8e1001fc7

def z74 : W := mkw 0x8000040008042009 0xef000c04980c623f

def z75 : W := mkw 0x90c175b8ebb4774f 0xb7c1fff8fff07fc7

def z76 : W := mkw 0x8418cc649805aced 0xc9380ce4980f83ff

def z77 : W := mkw 0x00c160b0c0000000 0x33c1f0f8e0000000

def z78 : W := mkw 0x00c170b8e0304202 0xb7c1f0f8e0f06207

def z79 : W := mkw 0x10c970fce1b0d7e6 0xfff9f0fce1ffffff

def z80 : W := mkw 0x03e5229244000000 0x0046331b66000000

def z81 : W := mkw 0x20129d0001ef7800 0x3eb9cc0001fffc00

def z82 : W := mkw 0x04084064900084e4 0x000000e0000001c0

def z83 : W := mkw 0x10c040b8e1900746 0xb5c000f8e1f003c7

def z84 : W := mkw 0x00108c0000052800 0x0201cc0000007c00

def z85 : W := mkw 0x14d9e8f4d1819de4 0x10b9c0e001039dc0

def z86 : W := mkw 0x00129d00006d6800 0x3effff0001fffc00

def z87 : W := mkw 0x841add6dba7deeff 0xffffffffffffffff

def z88 : W := mkw 0x03fffbfff6784212 0x3bfffffffef00000

def z89 : W := mkw 0x02f5aa0000000000 0x3affff0000000000

def z90 : W := mkw 0x2002150001ef7800 0x0400000001fffc00

def z91 : W := mkw 0x0418c86490018ce4 0x3bb9cce499039dc0

def z92 : W := mkw 0x0900009b00100310 0x0000001b00000000

def z93 : W := mkw 0x00c1300001a05000 0x36c1f00001f07c00

def z94 : W := mkw 0x090800df001083b0 0x410000ff000003f8

def z95 : W := mkw 0x09e6009b01da0310 0x0046001b00f00000

def z96 : W := mkw 0x8410cc2098052c4d 0x8201cc0098007c07

def z97 : W := mkw 0x10c170b8e1b05746 0xbfc7fffffff07fc7

def z98 : W := mkw 0x2802150901fffbb0 0x4400000001fffff8

def z99 : W := mkw 0x84084064980084ed 0xfdb800e4990f83ff

def z100 : W := mkw 0x09c800df019083b0 0x75c000ff01f003f8

def z101 : W := mkw 0x10c160b0c1801544 0x1081c0e001001dc0

def z102 : W := mkw 0x13fdeaf6d5801544 0x3bffffffff001dc0

def z103 : W := mkw 0x0000000000000444 0x8400000001007fc7

def z104 : W := mkw 0x09ee00df01da83b0 0x54b800e001ff83f8

def z105 : W := mkw 0x87fdeef6dc05aced 0xffffffffff0fffff

def z106 : W := mkw 0x8000040008042009 0xef463f1ffe0c623f

def z107 : W := mkw 0x0be7229b45da0310 0x0046331b66f00000

def z108 : W := mkw 0x0000040000052800 0x04000000010ffc00

def z109 : W := mkw 0x0018c86490000000 0x3bb9cce498000000

def z110 : W := mkw 0x0002000100480010 0x48060007000c0038

def z111 : W := mkw 0x0000000000000000 0x6d000004000c0238

def z112 : W := mkw 0x10017020e0205446 0xb781f0e0e1007fc7

def z113 : W := mkw 0x09ec00d6018281a0 0x7db800e4010f83f8

def z114 : W := mkw 0x10c1309861b05302 0x0040301860f00000

def z115 : W := mkw 0x0000100020204002 0x82003000e0006007

def z116 : W := mkw 0x22260300004a0000 0x0006030000000000

def z117 : W := mkw 0x00ee004401ca80a0 0x7dfe00e401ff83f8

def z118 : W := mkw 0x8418cc649805a8a9 0x7bb9cce4980f8038

def z119 : W := mkw 0x01ec00d6000080a0 0x7dfe00ff010f83f8

def z120 : W := mkw 0x00c160b0c0000000 0x3bc7fffffe000000

def z121 : W := mkw 0x00c3350001ec7000 0x3ec7ff0001fc7c00

def z122 : W := mkw 0x033dea66d4000000 0x0a3fff07fe000000

def z123 : W := mkw 0x2211bf0000257800 0x0201ff0000007c00

def z124 : W := mkw 0x22f7bf0821ff7a02 0xbfffff18e1fffe07

def z125 : W := mkw 0x89ee00df2bda83bb 0xfdfe00ffffff83ff

def z126 : W := mkw 0x0010c82090000000 0x0201cc0098000000

def z127 : W := mkw 0x22e7370001ef7800 0x0446330001fffc00

def z128 : W := mkw 0x22f5aa0001831800 0x3affff0001039c00

def z129 : W := mkw 0x94c174b8e9b5ffef 0xf7c1f0f8e1ffffff

def z130 : W := mkw 0x32e7339861fa5302 0x0046331860f00000

def z131 : W := mkw 0x86fdee649805aced 0xffffffe4990fffff

def z132 : W := mkw 0xb2f7ffb9ebff7f5f 0xffffffffffffffff

def z133 : W := mkw 0x07fdeaf6d4018ce4 0x3bffffffff039dc0

def z134 : W := mkw 0x0000000000000000 0x2946001f00000000

def z135 : W := mkw 0x080a004d01da83b0 0x7db800e401ff83f8

def z136 : W := mkw 0x23f7bf9245ef7800 0x3effff1b67fffc00

def z137 : W := mkw 0x8410cc2098052c4d 0xef01cc04980c7e3f

def z138 : W := mkw 0x02fdea6490000000 0x3bffffe498000000

def z139 : W := mkw 0x87fdeaf6dc0084ed 0xfbfffffffe0003ff

def z140 : W := mkw 0x22f5aa0001831800 0x10b9c00001039c00

def z141 : W := mkw 0x22f7bf0001ef7800 0x14b9c00001fffc00

def z142 : W := mkw 0x90c375b9ebfc775f 0xf7c1f0f8e1fc7fff

def z143 : W := mkw 0x892e154f2a7ee2bb 0xef7e3f1ffeffe23f

def z144 : W := mkw 0x8dfeddffbbffefff 0xffffffffffffffff

def z145 : W := mkw 0x32f7ffb8e1ff7f46 0xbffffff8e1ffffc7

def z146 : W := mkw 0x09ee11df23fac3b2 0x7dfe33ff67ff83f8

def z147 : W := mkw 0x00c160b0c0000444 0xb7c1f0f8e1007fc7

def z148 : W := mkw 0x9411fc20f8257c4f 0x8201fc00f8007c07

def z149 : W := mkw 0x800004092a14221b 0xef000c1ffe0c623f

def z150 : W := mkw 0x00016020c0000000 0x0201f000e0000000

def z151 : W := mkw 0x10c0109821b05746 0xb5c000f801f07fc7

def z152 : W := mkw 0x8418cc649805aced 0xd4b9c0e0010fffff

def z153 : W := mkw 0x1211fa20f4205446 0x8201ff00fe007c07

def z154 : W := mkw 0x22108f0000052800 0x00000f0000000000

def z155 : W := mkw 0x0002000900580210 0x6d46001f00fc0238

def z156 : W := mkw 0x800015002a24600b 0x82003f00fe006007

def z157 : W := mkw 0x19ed70fee1b2d7e6 0xb7f9f0f8e1f3ffc7

def z158 : W := mkw 0x0418c86490018ce4 0x7db9c0e4010f9ff8

def z159 : W := mkw 0x3211ff20e0257c46 0x8201ff00e0007c07

def z160 : W := mkw 0x80021500086c6009 0xef463f0498fc623f

def z161 : W := mkw 0x22f5bf0001a77800 0x12b9ff000103fc00

def z162 : W := mkw 0x22368f00004f2800 0x083e0f00000f8000

def z163 : W := mkw 0x09ee10df21fac3b2 0xfffe30ffe1ffe3ff

def z164 : W := mkw 0xa6ffff6dbbfffeff 0xffffffffffffffff

def z165 : W := mkw 0x8213ff29fe7c621b 0xef47ff1ffefc623f

def z166 : W := mkw 0x13fdfafef5b05746 0xb7f9f0f8e1f07fc7

def z167 : W := mkw 0x83e7379b6e7c621b 0xef463f1ffefc623f

def z168 : W := mkw 0x00c0009801900300 0x0040001800f00000

def z169 : W := mkw 0x10c160b0c1801544 0xb781c0e081007fc7

def z170 : W := mkw 0x01ec00d600000000 0x39fe00ff00000000

def z171 : W := mkw 0x22f7aa0001cb1800 0x3cffc00001ff9c00

def z172 : W := mkw 0x23fffbf6d5ea5000 0x3bfffffffef00000

def z173 : W := mkw 0x09ee00df01da83b0 0x7ffe3fffffff83f8

def z174 : W := mkw 0x033c8a4614000000 0x0038000000000000

def z175 : W := mkw 0x840004000805aced 0xc4000000010fffff

def z176 : W := mkw 0x033ccaf6d4000000 0x093e0ffffe000000

def z177 : W := mkw 0x90c375b9ebfc775f 0xffc7fffffffc7fff

def z178 : W := mkw 0x10c1309861b05302 0x35c030f861f003c0

def z179 : W := mkw 0x9418ccfcf815afef 0xffb9ccfcf90fffff

def z180 : W := mkw 0x873c8e461c05a8a9 0x483e0f071e0f8038

def z181 : W := mkw 0x850840f6dc0084ed 0xc10000fffe0003ff

def z182 : W := mkw 0x9dfffcfff9ffffff 0xfffffcfff9ffffff

def z183 : W := mkw 0x10c160b8e0100746 0xb3c1f0f8e00003c7

def z184 : W := mkw 0x0002000900580210 0x4400000000fc0238

def z185 : W := mkw 0xa6f7bf0009effced 0xfeffff0001ffffff

def z186 : W := mkw 0x00e7300001ea5000 0x3efff00001fffc00

def z187 : W := mkw 0x100040b8e0100746 0xb781c0f8e1007fc7

def z188 : W := mkw 0x800215092a7c621b 0xef000c0498fc623f

def z189 : W := mkw 0x00c0009801900300 0x35c000f801f003c0

def z190 : W := mkw 0x092e0047004a80b0 0x483e0007000f8038

def z191 : W := mkw 0x94d1fcb8f9b57f4f 0xb7c1fcf8f9f07fc7

def z192 : W := mkw 0x090800df001083b0 0x7db800ff010f83f8

def z193 : W := mkw 0x841a8d451a4da8b9 0x483e0f071e0f8038

def z194 : W := mkw 0xa6ffff6499effced 0xffffffe499ffffff

def z195 : W := mkw 0x32f7ffb0c1ef7d44 0x3effffe001fffdc0

def z196 : W := mkw 0x0002110922784212 0xa746331be6f06207

def z197 : W := mkw 0x19e7309b61fa5312 0x0046301b60f00000

def z198 : W := mkw 0x22e7330001ea5000 0x3cfe330001ff8000

def z199 : W := mkw 0x800044208804244d 0xff81cce4990c7fff

def z200 : W := mkw 0x08000000018281a0 0x00000000010381c0

def z201 : W := mkw 0x0100009244000000 0x0000001b66000000

def z202 : W := mkw 0x0002110922784212 0x6d46331f66fc0238

def z203 : W := mkw 0xa611ff2098257c4d 0x8201ff0098007c07

def z204 : W := mkw 0x81ee15df2a7c621b 0xfffe3ffffefc623f

def z205 : W := mkw 0x801add6dba7c621b 0xfffffffffefc623f

def z206 : W := mkw 0x800000092a10021b 0xeb463f1ffe00023f

def z207 : W := mkw 0x900255b9ea7c675f 0xef463ffffefc63ff

def z208 : W := mkw 0xa2f7bf010bef7819 0x7effff071ffffc38

def z209 : W := mkw 0x800000092a10021b 0xc100001ffe00023f

def z210 : W := mkw 0x840a556dba7ce6ff 0xef463ffffefc63ff

def z211 : W := mkw 0x2bffbfdf01fffbb0 0x7fffffff01fffff8

def z212 : W := mkw 0x0bffeaffd5da83b0 0x7dffc0ff01ff83f8

def z213 : W := mkw 0x03ed22d644000000 0x39fe33ff66000000

def z214 : W := mkw 0x00021508207c6202 0xaf463f18e0fc6207

def z215 : W := mkw 0x00c0009000000000 0x31c000f800000000

def z216 : W := mkw 0x2bffffffd5fffbb0 0x7ffffffffffffff8

def z217 : W := mkw 0x00021500006c6000 0x0400000000fc6000

def z218 : W := mkw 0x03f5eab2d4000000 0x0247ff1bfe000000

def z219 : W := mkw 0x83fdeef6dc042009 0xfffffffffe0c623f

def z220 : W := mkw 0x8418cc649805aced 0xffffffffff0fffff

def z221 : W := mkw 0x2bffbfd601eff9a0 0x3effffe001fffdc0

def z222 : W := mkw 0x8410dd20ba256c4f 0x8201ff00fe007c07

def z223 : W := mkw 0x800015002a24600b 0xab463f1ffe006007

def z224 : W := mkw 0x09e6009b01da83b0 0x4446001b01ff83f8

def z225 : W := mkw 0x01c960f6d4000000 0x33c1f0fffe000000

def z226 : W := mkw 0x03fdeaf6d4000000 0x10b9c0e000000000

def z227 : W := mkw 0x0bef22df45da83b0 0x7dfe33ff67ff83f8

def z228 : W := mkw 0xa402150009effced 0xc400000001ffffff

def z229 : W := mkw 0x80c375b9ea7c621b 0xffc7fffffefc623f

def z230 : W := mkw 0x1000000820100746 0x80000000000003c7

def z231 : W := mkw 0x0001300000205000 0x0201f00000007c00

def z232 : W := mkw 0x00e6009801da0300 0x3dfe00f801ff83c0

def z233 : W := mkw 0xb6fffffcf9ffffef 0xfffffffcf9ffffff

def z234 : W := mkw 0x03fdaad654000000 0x087e3f1f7e000000

def z235 : W := mkw 0x03fffff6d46c6000 0x3ffffffffefc6000

def z236 : W := mkw 0x0000150000246000 0x02003f0000006000

def z237 : W := mkw 0x2211aa0000011800 0x0001c00000001c00

def z238 : W := mkw 0x00e4000001820000 0x10b8000001038000

def z239 : W := mkw 0x83fdeafffe10021b 0xfbfffffffe00023f

def z240 : W := mkw 0x2000000001831800 0x0000000001039c00

def z241 : W := mkw 0x800205010a4c2019 0x40000000000c0038

def z242 : W := mkw 0x10017020e0205446 0x8201f000e0007c07

def z243 : W := mkw 0x10e770b8e1fa5746 0xbffff0f8e1ffffc7

def z244 : W := mkw 0x00021500006c6000 0x2e463f0000fc6000

def z245 : W := mkw 0x0211ea20d4000000 0x2b47ff1ffe000000

def z246 : W := mkw 0x880215092bfee3bb 0xc400000001ffe3ff

def z247 : W := mkw 0x900215092bfc775f 0xc400000001fc7fff

def z248 : W := mkw 0x0802000901da83b0 0x6d46001f01ff83f8

def z249 : W := mkw 0x09ee40ff81da87f4 0xffffc0ff81ffffff

def z250 : W := mkw 0x00e6000001ca0000 0x3cfe000001ff8000

def z251 : W := mkw 0x0000100820304202 0xa7403018e0f06207

def z252 : W := mkw 0x800215092a7c621b 0xc446331b66fc623f

def z253 : W := mkw 0x94dbfdfdfbfdffff 0xffffffffffffffff

def z254 : W := mkw 0x83fffffffe7c621b 0xfffffffffefc623f

def z255 : W := mkw 0x01ec40f6d4000000 0x39fe00fffe000000

def z256 : W := mkw 0x2213bf00006d7800 0x2e47ff0000fc7c00

def z257 : W := mkw 0xa2f7bf002bef780b 0xbeffff00fffffc07

def z258 : W := mkw 0x033cca6694000000 0x3bbfcfe79e000000

def z259 : W := mkw 0x000a004d005882b0 0x7dfe00ff01ff83f8

def z260 : W := mkw 0x890800df2a1083bb 0xc10000fffe0003ff

def z261 : W := mkw 0x02f7aa0001ca0000 0x3effff0001ff8000

def z262 : W := mkw 0x0000000801900300 0x0400000001f003c0

def z263 : W := mkw 0x13e5329a65b05302 0x0046331b66f00000

def z264 : W := mkw 0x0000000000000000 0x2b000c0498000000

def z265 : W := mkw 0x2002150001ef7800 0x2e463f0001fffc00

def z266 : W := mkw 0x09ec00d6018281a0 0x10b800e0010381c0

def z267 : W := mkw 0x00e6000001ca0000 0x0046000000f00000

def z268 : W := mkw 0x2201330000205000 0x0000330000000000

def z269 : W := mkw 0x8c02040909dfaffd 0xc400000001ffffff

def z270 : W := mkw 0x092e0047004a80b0 0x7dbe00e7010f83f8

def z271 : W := mkw 0x01e4009200000000 0x0046001b00000000

def z272 : W := mkw 0x0000100001a05000 0x0400000001f07c00

def z273 : W := mkw 0x13fdfafef5b05302 0x3bfffffffef00000

def z274 : W := mkw 0x800015082a34620b 0xa7403f18fef06207

def z275 : W := mkw 0x8418cc6498052c4d 0xbbb9cce498007c07

def z276 : W := mkw 0x09ef60ffc1da83b0 0x7ffff0ffe1ff83f8

def z277 : W := mkw 0x8412dd29ba7d6e5f 0xef47ff1ffefc7e3f

def z278 : W := mkw 0x10c1309861b05302 0xa7403018e0f06207

def z279 : W := mkw 0x1bfffafff5fad7f6 0xffffffffffffffff

def z280 : W := mkw 0x0000000000000000 0x02003f00fe000000

def z281 : W := mkw 0x80c215992bfc631b 0xffc63ffffffc63ff

def z282 : W := mkw 0x0000000000000000 0x2a463f0000000000

def z283 : W := mkw 0x0000000000000000 0x23403018e0000000

def z284 : W := mkw 0x03fdeaf6d40080a0 0x7fffffffff0f83f8

def z285 : W := mkw 0x00f68c0001cf2800 0x3effcc0001fffc00

def z286 : W := mkw 0x87fdeef6dc052c4d 0xbbfffffffe007c07

def z287 : W := mkw 0x0000402080000444 0x810000e0800003c7

def z288 : W := mkw 0x22e7330001ea5000 0x0046330000f00000

def z289 : W := mkw 0x84188c441805aced 0xcc380c04190fffff

def z290 : W := mkw 0x80e615092bfe621b 0xfffe3f1fffffe23f

def z291 : W := mkw 0x940840fcf81087ef 0xc10000fcf80003ff

def z292 : W := mkw 0x03fdeaf6d4000000 0x39ffc0ff00000000

def z293 : W := mkw 0x22368f00004f2800 0x3ebfcf00010ffc00

def z294 : W := mkw 0x0211ea20d4000000 0x0001c00000000000

def z295 : W := mkw 0x13e572bae5b05746 0xb7c7f3fbe7f07fc7

def z296 : W := mkw 0x84d9fc6499a5fced 0xfff9fce499ffffff

def z297 : W := mkw 0x08e6000901da83b0 0x7cfe000001ff83f8

def z298 : W := mkw 0x03ffeaffd4580210 0x7ffffffffefc0238

def z299 : W := mkw 0x00c160b8c1900300 0x37c1f0f8e1f003c0

def z300 : W := mkw 0x0010cc2080052c44 0xbfb9cce0810fffc7

def z301 : W := mkw 0xa6ffbf4419eff8a9 0x7effff0419fffc38

def z302 : W := mkw 0x00c170b0c1a05000 0x37c1f0f8e1f07c00

def z303 : W := mkw 0xa7fffff6ddeffced 0xffffffffffffffff

def z304 : W := mkw 0x2be7339b01fa5310 0x0046331b00f00000

def z305 : W := mkw 0x22f7bb0001eb5800 0x10fff30001f39c00

def z306 : W := mkw 0x010800d600000000 0x010000ff00000000

def z307 : W := mkw 0x00c1209040000000 0x0040301860000000

def z308 : W := mkw 0x8410cc2098052c4d 0xb781cce099007fc7

def z309 : W := mkw 0x010840f6d4000000 0x010000fffe000000

def z310 : W := mkw 0x840040209800044d 0x8000000098000007

def z311 : W := mkw 0x22f5ba0001a35800 0x36f9f00001f3fc00

def z312 : W := mkw 0x0000000000000000 0x358000e0010003c0

def z313 : W := mkw 0x84188c441805a8a9 0x7eb9cc04190ffc38

def z314 : W := mkw 0xa2f7bf0009ef7809 0xffffff0499fffe3f

def z315 : W := mkw 0x800205010a4c2019 0x6b463f1ffe0c0038

def z316 : W := mkw 0x10017028e0305646 0xa741f018e0f07e07

def z317 : W := mkw 0x09ef30df01fad3b0 0x7ffff0ff01fffff8

def z318 : W := mkw 0x0000100820304202 0xaf463f1ffef06207

def z319 : W := mkw 0x29ee15df01fffbb0 0x7dfe00ff01fffff8

def z320 : W := mkw 0x09ec00d6018281a0 0x39fe00ff010381c0

def z321 : W := mkw 0x07fdeaf6d4018ce4 0x10b9c0e001039dc0

def z322 : W := mkw 0x8418cc6dba15aeff 0xffb9ccffff0fffff

def z323 : W := mkw 0x2211ff20d4257800 0x0201ff00fe007c00

def z324 : W := mkw 0x0000000000000000 0x0046331b66000000

def z325 : W := mkw 0x0018c86490000000 0x10b9c0e000000000

def z326 : W := mkw 0x89ee15df2bfee3bb 0xfdfe00ff01ffe3ff

def z327 : W := mkw 0x800a154d2a7ce2bb 0xfffe3fffffffe3ff

def z328 : W := mkw 0x03ed62f6d4000000 0x014633fffe000000

def z329 : W := mkw 0x10c170b8e1b05746 0x10c1f0f861f01dc0

def z330 : W := mkw 0x84108c000805aced 0xfeb9cc00010fffff

def z331 : W := mkw 0x8fffeeffdddfaffd 0xffffffffffffffff

def z332 : W := mkw 0x00084064800084e4 0xffb9c0e4810fffff

def z333 : W := mkw 0x092c0046000280a0 0x0038000000038000

def z334 : W := mkw 0x8d18ccff9815affd 0xffb9ccff990fffff

def z335 : W := mkw 0x02348a0000000000 0x083e0f0000000000

def z336 : W := mkw 0x09ee00d601ca81a0 0x3cfe00e001ff81c0

def z337 : W := mkw 0x8000040008042009 0x82000c0098006007

def z338 : W := mkw 0x00000000000080a0 0x44000000010f83f8

def z339 : W := mkw 0x833e8f471e4c2019 0x483e0f071e0c0038

def z340 : W := mkw 0x090840ffd41083b0 0x410000fffe0003f8

def z341 : W := mkw 0x840804440805aced 0xfdb800e4010fffff

def z342 : W := mkw 0x833e9f4f3e7c621b 0xef7e3f1ffefc623f

def z343 : W := mkw 0x00c1300821b05202 0xb7c1f018e1f07e07

def z344 : W := mkw 0x18c370b9e1fad7f6 0xf7c1f0f8e1ffffff

def z345 : W := mkw 0x0000000000000000 0x08060f071e000000

def z346 : W := mkw 0xa63e8f44184fa8a9 0x483e0f04180f8038

def z347 : W := mkw 0x22f7bf9801ff7b00 0x3ffffff801ffffc0

def z348 : W := mkw 0x03fdaa4614000000 0x3affff071e000000

def z349 : W := mkw 0x03e5229244000000 0x0000000000000000

def z350 : W := mkw 0x09080047000080b0 0x4000000700000038

def z351 : W := mkw 0x32f7bf9861ff7b02 0x3effff1861fffc00

def z352 : W := mkw 0x11ed70fee1b05746 0xbffff0ffe1f07fc7

def z353 : W := mkw 0x00c1309801b05300 0x37c1f0f801f07fc0

def z354 : W := mkw 0x033c8a4614000000 0x2b7e3f1ffe000000

def z355 : W := mkw 0x02f5eab0c0000000 0x3bfffff8e0000000

def z356 : W := mkw 0x10c1309861b05302 0x36c1f01861f07c00

def z357 : W := mkw 0xa63ecf64984faced 0xffbfcfe4990fffff

def z358 : W := mkw 0x26fdea6491839ce4 0x10b9c0e001039dc0

def z359 : W := mkw 0x1000100821b05746 0xa7403018e1f07fc7

def z360 : W := mkw 0x8418dd64ba25ecef 0xffb9ffe4ff0fffff

def z361 : W := mkw 0x092e004f005a82b0 0x6d7e001f00ff8238

def z362 : W := mkw 0x0000040000042000 0x2e000c00000c6000

def z363 : W := mkw 0x22f7bf0923ff7a12 0x3effff1b67fffc00

def z364 : W := mkw 0x00c1200000000000 0x32c1f00000000000

def z365 : W := mkw 0x10c160b0c1801544 0x33c1f0f8e1001dc0

def z366 : W := mkw 0xafffffff99fffffd 0xffffffff99ffffff

def z367 : W := mkw 0x80020409085c2219 0xef460c1f98fc623f

def z368 : W := mkw 0x89e6159b2bfe631b 0xef463f1ffefc623f

def z369 : W := mkw 0x800215092a7c621b 0xc500001ffefc623f

def z370 : W := mkw 0x8418cc649805aced 0xc301cce498007fff

def z371 : W := mkw 0x0000000800100200 0x2540001800f00200

def z372 : W := mkw 0x0002000900580210 0x0046001b00f00000

def z373 : W := mkw 0x80129d092a7d6a1b 0xffffff1ffffffe3f

def z374 : W := mkw 0x840215092a7deeff 0xef463f1fffffffff

def z375 : W := mkw 0x841acd659a4dacfd 0xffbfcfe79f0fffff

def z376 : W := mkw 0x02f7bf00006c6000 0x3effff0000fc6000

def z377 : W := mkw 0x1802100921fad7f6 0xc400000001ffffff

def z378 : W := mkw 0x0bfdeaffd41083b0 0x7bfffffffe0003f8

def z379 : W := mkw 0x10c170b0c1a05544 0x36c1f0e001f07dc0

def z380 : W := mkw 0x09ee00df01da83b0 0x414600ff00f003f8

def z381 : W := mkw 0x840004000805a8a9 0x40000000000f8038

def z382 : W := mkw 0x2237bf00006f7800 0x0a3fff00000ffc00

def z383 : W := mkw 0x00e6150001ee6000 0x3efe3f0001ffe000

def z384 : W := mkw 0x800205010a4c2019 0xef060f079e0c623f

def z385 : W := mkw 0x01ec00d600000000 0x10b800e000000000

def z386 : W := mkw 0x84d9ecf4d805aced 0xfff9fcfcf90fffff

def z387 : W := mkw 0x03fc8ad614000000 0x39fe0fff1e000000

def z388 : W := mkw 0x800215010a6c6019 0x6e463f071efc6038

def z389 : W := mkw 0x02108a0014000000 0x00000f001e000000

def z390 : W := mkw 0x84084064980084ed 0xf781c0e499007fff

def z391 : W := mkw 0x800215012a6c601b 0xca063f07fe0c603f

def z392 : W := mkw 0x00e4000000000000 0x38fe000000000000

def z393 : W := mkw 0x00c040b881900744 0xb7c1c0f881f07fc7

def z394 : W := mkw 0x03fdeaf6d4000000 0x33f9f0f8e0000000

def z395 : W := mkw 0x8408406dba1086ff 0xc10000fffe0003ff

def z396 : W := mkw 0x00c0000001800000 0x34c0000001f00000

def z397 : W := mkw 0x10c170b8e1b05746 0x8241f018e0f07c07

def z398 : W := mkw 0x22f7ff20d5ef7800 0x3effff00fffffc00

def z399 : W := mkw 0x09fec8ff91da83b0 0x7fffccff99ff83f8

def z400 : W := mkw 0x8418c86498018ced 0xd1b9c0e499039fff

def z401 : W := mkw 0x89ee04df09dea3b9 0xfffe0cff99ffe3ff

def z402 : W := mkw 0x0201220044000000 0x0000330066000000

def z403 : W := mkw 0x22f7bf0001ef7800 0x3fffff1ffffffc00

def z404 : W := mkw 0x10c375b8e1fc7746 0xbfc7fff8e1fc7fc7

def z405 : W := mkw 0x892e05470a4ea0b9 0x483e0f071e0f8038

def z406 : W := mkw 0x22ffbf4401eff8a0 0x7fffffe401fffff8

def z407 : W := mkw 0x09ee15df01fee3b0 0x7ffe3fff01ffe3f8

def z408 : W := mkw 0x840215092a7deeff 0xc400000001ffffff

def z409 : W := mkw 0x09fe8cdf01dfabb0 0x7fffccff01fffff8

def z410 : W := mkw 0x2213bf0001ef7800 0x0601ff0001fffc00

def z411 : W := mkw 0x09e6009b01da0310 0x3cfe001b01ff8000

def z412 : W := mkw 0x100050b8e1b05746 0x850000f8e1f07fc7

def z413 : W := mkw 0x02f5aa0000000000 0x10b9c00000000000

def z414 : W := mkw 0x10c170b8e1b05746 0x814030f8e0f003c7

def z415 : W := mkw 0x800211092a78421b 0xc146331ffef0023f

def z416 : W := mkw 0x22f7bb0001ea5000 0x3affff0000f00000

def z417 : W := mkw 0x00108c0000052800 0x08380c00000f8000

def z418 : W := mkw 0x0002000900580210 0x6f463f1ffefc0238

def z419 : W := mkw 0x0000000900100210 0x4100001f00000238

def z420 : W := mkw 0x0008004400000000 0x39b800e400000000

def z421 : W := mkw 0x0bffaadf01da83b0 0x7fffffff01ff83f8

def z422 : W := mkw 0x03fdeaf6d4000444 0xbfffffffff007fc7

def z423 : W := mkw 0x23fdeaf6d5831800 0x3bffffffff039c00

def z424 : W := mkw 0x800215092a7c621b 0xc6003f00fefc623f

def z425 : W := mkw 0x20c3350001ef7800 0x36c1f00001fffc00

def z426 : W := mkw 0x010840f6d4000000 0x000000e000000000

def z427 : W := mkw 0x8518ccf6dc05aced 0xffb9ccffff0fffff

def z428 : W := mkw 0x00c1702081a05444 0xb7c1f0e081f07fc7

def z429 : W := mkw 0x0018c86490000000 0x3bfffffffe000000

def z430 : W := mkw 0x90c174b8e9b4774f 0xffc1fcfcf9fc7fff

def z431 : W := mkw 0x00005028a0304646 0xb7c1f0f8e1f07fc7

def z432 : W := mkw 0x00004020d4000000 0x00000000fe000000

def z433 : W := mkw 0x0000402080000444 0x8201c00080007c07

def z434 : W := mkw 0x092e00df005a83b0 0x493e00ff000f83f8

def z435 : W := mkw 0x22e5220001821000 0x0000000000000000

def z436 : W := mkw 0x01ee00d601ca0000 0x3dfe00ff01ff8000

def z437 : W := mkw 0x0dfcc8f691838de4 0x10b9c0e001039dc0

def z438 : W := mkw 0x0000100000204000 0x2640300000f06000

def z439 : W := mkw 0x00c2009901d80310 0x7dc600ff01fc03f8

def z440 : W := mkw 0x00c0109821b04302 0xb7c030f8e1f063c7

def z441 : W := mkw 0x10c160b8c1901744 0x35c1c0f801f01fc0

def z442 : W := mkw 0x09ee00d7004a80b0 0x79fe00ff000f8038

def z443 : W := mkw 0x00021500006c6000 0x2f463f1ffefc6000

def z444 : W := mkw 0x10d1fcb8e1b57f46 0xbff9fcf8e1ffffc7

def z445 : W := mkw 0x8000040008042009 0xc4000000000c623f

def z446 : W := mkw 0x800000002a00000b 0x80000000fe000007

def z447 : W := mkw 0xa6f7ff2099ef7c4d 0xbeffff0099fffc07

def z448 : W := mkw 0x90c335996bfc731b 0xef463f1ffefc623f

def z449 : W := mkw 0xa2368f010a4f2819 0x483e0f071e0f8038

def z450 : W := mkw 0x11c970fef5b05746 0xb7c1f0fffff07fc7

def z451 : W := mkw 0x8211ff20fe24600b 0x8201ff00fe006007

def z452 : W := mkw 0x810840fffe10021b 0xc10000fffe00023f

def z453 : W := mkw 0x00080044000080a0 0x48380004000f8038

def z454 : W := mkw 0xa213bf092a7d7a1b 0xef47ff1ffefc7e3f

def z455 : W := mkw 0x02e5220000000000 0x0046330000000000

def z456 : W := mkw 0x14d9f8fcf1b1dfe6 0xb7f9f0f8e1f3ffc7

def z457 : W := mkw 0x19ef60ffc1da97f4 0x7dffc0ff01ff9ff8

def z458 : W := mkw 0x08c2009901da83b0 0x75c000f801ff83f8

def z459 : W := mkw 0x841add6dba7deeff 0xffb9cce499ffffff

def z460 : W := mkw 0x03fdeaf6d4000000 0x18bfcfe71e000000

def z461 : W := mkw 0x22e7370001ee7000 0x2e463f0000fc6000

def z462 : W := mkw 0xa3ffffffffff7a1b 0xfffffffffffffe3f

def z463 : W := mkw 0x10004020e0000446 0x80000000e0000007

def z464 : W := mkw 0x22f7af00004f2800 0x3affff00000f8000

def z465 : W := mkw 0x30c375b8e1ff7f46 0xb7c1f0f8e1ffffc7

def z466 : W := mkw 0x8dfcccf69987aded 0xffb9cce4990fffff

def z467 : W := mkw 0x0000000922100212 0x0000001b66000000

def z468 : W := mkw 0x012c004600000000 0x083e000700000000

def z469 : W := mkw 0x10c170b0e0205446 0xb3c1f0f8e0007c07

def z470 : W := mkw 0x02f5ae0000052800 0x3effff00010ffc00

def z471 : W := mkw 0x0000000000000000 0x3681c00001007c00

def z472 : W := mkw 0x22f7af0001cf3800 0x18bfcf00010f9c00

def z473 : W := mkw 0x800014082834620b 0xef403c1cf8fc623f

def z474 : W := mkw 0x84188c441805a8a9 0x7db80ce4190f83f8

def z475 : W := mkw 0x12d1fab8f5b05746 0xb7c1fff8fff07fc7

def z476 : W := mkw 0x23fdeaf6d5831800 0x10b9c0e001039c00

def z477 : W := mkw 0x09ec00df001083b0 0x79fe00ff000003f8

def z478 : W := mkw 0x8418cc649805aced 0x58b9cce4190f9df8

def z479 : W := mkw 0x0002100920784212 0xef46301fe0fc623f

def z480 : W := mkw 0x00c160b0c0000000 0x1081c0e000000000

def z481 : W := mkw 0xa41add6499effced 0xffb9cce499ffffff

def z482 : W := mkw 0x22f7ffb0c1ef7800 0x3ffffff8e1fffc00

def z483 : W := mkw 0x82f7bf092a7c621b 0xffffff1ffefc623f

def z484 : W := mkw 0x100170b8e0305746 0x8301f0f8e0007fc7

def z485 : W := mkw 0x2bf7bf9b01ff7b10 0x3effff1b01fffc00

def z486 : W := mkw 0x0018884410000000 0x08380c0418000000

def z487 : W := mkw 0x800000092a10021b 0xc00000000000023f

def z488 : W := mkw 0x0000000000000000 0x0100001ffe000000

def z489 : W := mkw 0x800200092a58021b 0xed46001ffefc023f

def z490 : W := mkw 0x8d3e8c47184fa8b9 0x483e0c07180f8038

def z491 : W := mkw 0x22e7330923fa5212 0x0046331b66f00000

def z492 : W := mkw 0x8410cc209805aced 0xc601cc00990fffff

def z493 : W := mkw 0x09ee40ffd5da83b0 0x7dfe00ffffff83f8

def z494 : W := mkw 0x0bfdeaf6d58281a0 0x3bffffffff0381c0

def z495 : W := mkw 0x13fdeafef4100746 0xbbfffffffe0003c7

def z496 : W := mkw 0x90017520ea24744f 0x8201ff00fe007c07

def z497 : W := mkw 0x09ec00df019283b0 0x51b800ff010383f8

def z498 : W := mkw 0x800015002a24600b 0x8000000000006007

def z499 : W := mkw 0x100050b8e0304746 0xa74030f8e0f063c7

def z500 : W := mkw 0x09e6119b23fa4312 0x0046331b66f00000

def z501 : W := mkw 0x800215092a7c621b 0xe7403018e0fc623f

def z502 : W := mkw 0x8d3ecc67984facfd 0xffbfcce7990fffff

def z503 : W := mkw 0x8400040008052c4d 0x8000000000007c07

def z504 : W := mkw 0x1000100020205446 0x8000000000007c07

def z505 : W := mkw 0x22ffff6491ef7800 0x3fffffe499fffc00

def z506 : W := mkw 0x00d1bc0001a57800 0x3ef9fc0001fffc00

def z507 : W := mkw 0x8418c864980084ed 0xfbb9cce4980003ff

def z508 : W := mkw 0x32e773b8e1fa5746 0xb7c7f3f8e1f07fc7

def z509 : W := mkw 0x840844649805aced 0xc50000e4990fffff

def z510 : W := mkw 0x0002110922784212 0x2b463f1ffef00000

def z511 : W := mkw 0x87fdeef6dc05a8a9 0x7bfffffffe0f8038

def z512 : W := mkw 0x23e7339245ea5000 0x0046331b66f00000

def z513 : W := mkw 0x90c170b9ebb0575f 0xf7c1f0fffff07fff

def z514 : W := mkw 0x8619ee64dc05aced 0xffb9ffe4ff0fffff

def z515 : W := mkw 0x3bffffffe1fffff6 0xffffffffe1ffffff

def z516 : W := mkw 0x09ee00d701ca81b0 0x58be00e7010f81f8

def z517 : W := mkw 0x0008406490000000 0x010000e498000000

def z518 : W := mkw 0x800005000a042009 0x00000f001e000000

def z519 : W := mkw 0x1001300060205002 0x0000300060000000

def z520 : W := mkw 0x32f5fab8e1b35f46 0xb7f9f0f8e1f3ffc7

def z521 : W := mkw 0x0010880000010800 0x10b9c00001039c00

def z522 : W := mkw 0x22f5bf0000257800 0x3affff0000007c00

def z523 : W := mkw 0x80025529aa7c665f 0xffc7fffffffc7fff

def z524 : W := mkw 0x9400140829b5ffef 0xc400000001ffffff

def z525 : W := mkw 0x01ee00df00580210 0x7dfe00ff00fc0238

def z526 : W := mkw 0x22e7330001ea5000 0x36c7f30001f07c00

def z527 : W := mkw 0x0018c86490000444 0xbfb9cce499007fc7

def z528 : W := mkw 0xabffbfdf2bfffbbb 0xffffffffffffffff

def z529 : W := mkw 0x03f5aa9244000000 0x3affff1b66000000

def z530 : W := mkw 0x0018cc6490052800 0x3fb9cce4990ffc00

def z531 : W := mkw 0x19ed60f6c18295e4 0x10b9c0e001039dc0

def z532 : W := mkw 0x10d9f8fcf1b05746 0xbff9fcfcf9f07fc7

def z533 : W := mkw 0x13fdfaf6f4205446 0xbbfffffffe007c07

def z534 : W := mkw 0x13fdeaf6d5801544 0x10b9c0e001001dc0

def z535 : W := mkw 0x2bffbf4701eff8b0 0x7effff0701fffc38

def z536 : W := mkw 0x22f7bf0001ef7800 0x0247ff0000f07c00

def z537 : W := mkw 0x23ffbf4615ef7800 0x3effff071ffffc00

def z538 : W := mkw 0x0324020204000000 0x0006030306000000

def z539 : W := mkw 0x12f5fab8e1b05746 0xbffffff8e1f07fc7

def z540 : W := mkw 0x94d9ecf4d985bded 0xffb9cce4990fffff

def z541 : W := mkw 0x00c800dc019083a0 0x7df800fc01ff83f8

def z542 : W := mkw 0xa2e737092bfe721b 0xef463f1ffefc623f

def z543 : W := mkw 0x800215002a6c600b 0xae463f00fefc6007

def z544 : W := mkw 0x0002010102480010 0x0006030306000000

def z545 : W := mkw 0x32f7bf0821ff7f46 0xbeffff0001ffffc7

def z546 : W := mkw 0x800205090a5c2219 0x6d460f1f1efc0238

def z547 : W := mkw 0xa619ff649825fced 0xffb9ffe4990fffff

def z548 : W := mkw 0x10c1209041801100 0x0000000000000000

def z549 : W := mkw 0x09ee00df01da0310 0x39fe00ff00f00000

def z550 : W := mkw 0x0000100820304202 0x0040301860f00000

def z551 : W := mkw 0x04188844100188a0 0x0038000000038000

def z552 : W := mkw 0x00021509007c6210 0x6f463f1f00fc6238

def z553 : W := mkw 0x800205092a5c221b 0xc9060f1ffe0c023f

def z554 : W := mkw 0x19e770bbe1fa5756 0xb7c7f0fbe1f07fc7

def z555 : W := mkw 0x2bfe8fdf01dfabb0 0x7dfe0fff01ff83f8

def z556 : W := mkw 0x800215092a7c621b 0x48463f1f7efc0038

def z557 : W := mkw 0x00e6000901da0210 0x7dfe001f01ff8238

def z558 : W := mkw 0x9419fc64f825fcef 0xffb9fce4f90fffff

def z559 : W := mkw 0x8410cc2098052c4d 0xbeb9cc00990ffc07

def z560 : W := mkw 0x110840fef4100746 0x810000fffe0003c7

def z561 : W := mkw 0x87fdeef6dc05aced 0xffb9cce4990fffff

def z562 : W := mkw 0x03fdeaf6d4000000 0x12b9ffe0fe000000

def z563 : W := mkw 0x83fdfff6fe24600b 0xbbfffffffe006007

def z564 : W := mkw 0x00020500004c2000 0x08060f00000c0000

def z565 : W := mkw 0x8000000008000009 0xc10000049800023f

def z566 : W := mkw 0x2211bf0000257800 0x3eb9ff00010ffc00

def z567 : W := mkw 0x03e562b2c4000000 0x33c7f3fbe6000000

def z568 : W := mkw 0x85fcccf69805aced 0xffffccff990fffff

def z569 : W := mkw 0x1000009860100302 0x0000001860000000

def z570 : W := mkw 0x0dfec8ff91db8ff4 0x7dffc0ff01ff9ff8

def z571 : W := mkw 0x23fffff6d5ef7800 0x3effffe001fffc00

def z572 : W := mkw 0x02f5aa0000000000 0x3bffff1ffe000000

def z573 : W := mkw 0x2bef33df01fad3b0 0x7dfe33ff01ff83f8

def z574 : W := mkw 0x09e4009201820100 0x0000000000000000

def z575 : W := mkw 0x0bfdeaf6d58281a0 0x10b9c0e0010381c0

def z576 : W := mkw 0x02f5ba0001a05000 0x3effff0001f07c00

def z577 : W := mkw 0x94c970fcf9b0d7ef 0xf7c1f0fcf9f07fff

def z578 : W := mkw 0x97fdfefefdb5ffef 0xffffffffffffffff

def z579 : W := mkw 0x02d1eab0d4000000 0x33c1fff8fe000000

def z580 : W := mkw 0x890a15df2a7ce3bb 0xef463ffffefc63ff

def z581 : W := mkw 0x03e7339b66784212 0x0046331b66f00000

def z582 : W := mkw 0x10016020c0001444 0x0001c00000001c00

def z583 : W := mkw 0x93fffffffffc775f 0xfffffffffffc7fff

def z584 : W := mkw 0x03fdfafef4304202 0xbffffffffef06207

def z585 : W := mkw 0x19ef30df61fad3b2 0x7dfe30ff61ff83f8

def z586 : W := mkw 0x1000100821b05302 0x0000000000f00000

def z587 : W := mkw 0x32f5eab0c1831d44 0x10b9c0e001039dc0

def z588 : W := mkw 0x0118c8f6d4000000 0x3bb9ccfffe000000

def z589 : W := mkw 0x03fdfaf6d5a05000 0x3ffffffffff07c00

def z590 : W := mkw 0x00021509227c6212 0x2e463f1b66fc6000

def z591 : W := mkw 0x8418dc6cb835eeef 0xfff9fcfcf9ffffff

def z592 : W := mkw 0x00080044000080a0 0x10b800e0010381c0

def z593 : W := mkw 0x092e004f01da83b0 0x4c3e000701ff83f8

def z594 : W := mkw 0x0410c82090010c44 0x0001c00000001c00

def z595 : W := mkw 0x8bfffffffffee3bb 0xffffffffffffe3ff

def z596 : W := mkw 0x00260000004a0000 0x083e0000000f8000

def z597 : W := mkw 0x03fdaad600000000 0x3bffffff00000000

def z598 : W := mkw 0x3002150821ff7f46 0x8400000001ffffc7

def z599 : W := mkw 0x0002000001ca0000 0x0400000001ff8000

def z600 : W := mkw 0xa00215092bff7a1b 0xef463f1ffffffe3f

def z601 : W := mkw 0x2bfdaad6018399a0 0x10b9c0e001039dc0

def z602 : W := mkw 0x841acc6d985daefd 0xffffccff99ffffff

def z603 : W := mkw 0x09ee004701ca80b0 0x7cfe000701ff8038

def z604 : W := mkw 0x03e5229244000000 0x2b463f1ffe000000

def z605 : W := mkw 0x23ffbfd601ef7800 0x3fffffff01fffc00

def z606 : W := mkw 0x84108c0018052809 0x00000c0018000000

def z607 : W := mkw 0x19c970ffe1b0d7f6 0xf7c1f0ffe1f07fff

def z608 : W := mkw 0x800215092a7c621b 0xcc060f071efc623f

def z609 : W := mkw 0x84188c441805a8a9 0xef380c04980fe23f

def z610 : W := mkw 0x8418cc649805aced 0xca39cc04980ffc3f

def z611 : W := mkw 0x0000000000000000 0xa700000080006207

def z612 : W := mkw 0x0bfe8adf15da83b0 0x7dfe0fff1fff83f8

def z613 : W := mkw 0x26ffff6491effce4 0x3effffe001fffdc0

def z614 : W := mkw 0x1000000001801544 0x0000000001001dc0

def z615 : W := mkw 0x0002110000684000 0x0046330000f00000

def z616 : W := mkw 0xa6fdee649987bced 0xffb9cce4990fffff

def z617 : W := mkw 0x01fcc8f690000000 0x3bffccff98000000

def z618 : W := mkw 0x2bffaadf01db9bb0 0x7dffc0ff01ff9ff8

def z619 : W := mkw 0x03fdeef6d4052800 0x3fffffffff0ffc00

def z620 : W := mkw 0x83ffeff7de4c2019 0x7bfffffffe0c0038

def z621 : W := mkw 0x22f7bf0901ff7a10 0x7fffff1f01fffe38

def z622 : W := mkw 0x800015002a24600b 0xef003f04fe0c623f

def z623 : W := mkw 0x03ffeaf6d5ca0000 0x3fffffffffff8000

def z624 : W := mkw 0x0319eaf6d4000000 0x0301fffffe000000

def z625 : W := mkw 0x00c1300001a05000 0x0040300000f00000

def z626 : W := mkw 0x8dee40ff99da87fd 0xfdfe00ff99ff83ff

def z627 : W := mkw 0x08020001004a80b0 0x40000000000f8038

def z628 : W := mkw 0x841add64986deced 0xffffffe499ffffff

def z629 : W := mkw 0x09ee00df01da83b0 0x10fe00fb01f381c0

def z630 : W := mkw 0x01ed60f6c0000000 0x3bfff0ffe0000000

def z631 : W := mkw 0x09e6009b01da0310 0x35c600fb01f003c0

def z632 : W := mkw 0x0400000000018ce4 0x0000000001039dc0

def z633 : W := mkw 0x800215092a7c621b 0x82463f1bfef06007

def z634 : W := mkw 0x2002110001ea5000 0x0000000000f00000

def z635 : W := mkw 0x2b3e8f47004fa8b0 0x483e0f07000f8038

def z636 : W := mkw 0x233e8f46144f2800 0x083e0f071e0f8000

def z637 : W := mkw 0x00080044000080a0 0x410000e4000003f8

def z638 : W := mkw 0x8c1acc6d99dfaffd 0xffb9cce499ffffff

def z639 : W := mkw 0x00d9e8f4d0000000 0x3bf9fcfcf8000000

def z640 : W := mkw 0x10c1300821b05746 0xb6c1f00001f07fc7

def z641 : W := mkw 0x03fdeafed5900300 0x3ffffffffff003c0

def z642 : W := mkw 0x00c1200001801000 0x1081c00001001c00

def z643 : W := mkw 0x22f7ff2081ef7c44 0xbfffffe081ffffc7

def z644 : W := mkw 0x08000009001083b0 0x40000000000003f8

def z645 : W := mkw 0x8611ee20dc052c4d 0x8201ff00fe007c07

def z646 : W := mkw 0x32f7ff20e1ef7c46 0xbeffff00e1fffc07

def z647 : W := mkw 0x22348a0000030800 0x0038000000038000

def z648 : W := mkw 0x10c370b9e1f85756 0xffc7f0ffe1fc7fff

def z649 : W := mkw 0x19ee40ffe1da87f6 0xfdfe00ffe1ff83ff

def z650 : W := mkw 0x00188c440005a8a0 0x7fb9cce4010ffff8

def z651 : W := mkw 0x0bffeaffd5da0310 0x3bfffffffef00000

def z652 : W := mkw 0x33fffffef5ff7f46 0xbfffffffffffffc7

def z653 : W := mkw 0x09260003004a0010 0x0006000300000000

def z654 : W := mkw 0x800010092a30421b 0xe740301ffef0623f

def z655 : W := mkw 0x10c3319963f85312 0x0046331b66f00000

def z656 : W := mkw 0x0108004614000000 0x000000071e000000

def z657 : W := mkw 0x10c1309861b05746 0x8440301861f07fc7

def z658 : W := mkw 0x8dee04df09dfaffd 0xfdfe00ff01ffffff

def z659 : W := mkw 0x800215092a7c621b 0xed46001f00fc623f

def z660 : W := mkw 0x23ffeff6d44f2800 0x3bfffffffe0f8000

def z661 : W := mkw 0x000040b0c0000000 0x010000f8e0000000

def z662 : W := mkw 0x873cce669c05aced 0xffbfcfe79f0fffff

def z663 : W := mkw 0xa2369f092a7f6a1b 0xef7e3f1ffeffe23f

def z664 : W := mkw 0x800804440804a0a9 0xffb80ce4990fe3ff

def z665 : W := mkw 0x22369f00006f6800 0x2e7e3f0000ffe000

def z666 : W := mkw 0x22369f0001ef7800 0x0c3e0f0001fffc00

def z667 : W := mkw 0x90037529ea7c765f 0xef47ff1ffefc7e3f

def z668 : W := mkw 0x84080044180080a9 0x4000000418000038

def z669 : W := mkw 0x0018c864900080a0 0x7fb9cce4990f83f8

def z670 : W := mkw 0x89ee05df0bdea3b9 0x7dfe0fff1fff83f8

def z671 : W := mkw 0x8000040008042009 0x48000c04180c0038

def z672 : W := mkw 0x22f7bf0001ef7800 0x087e3f0000ff8000

def z673 : W := mkw 0x10c371b9e3f85756 0xb7c7f3fbe7f07fc7

def z674 : W := mkw 0x20020500004f2800 0x00000000000f8000

def z675 : W := mkw 0xa211bf002a25780b 0x8201ff00fe007c07

def z676 : W := mkw 0x840044208805aced 0xf781c0e0810fffff

def z677 : W := mkw 0x20e6150001ef7800 0x3cfe000001fffc00

def z678 : W := mkw 0x84000000080084ed 0xc0000000000003ff

def z679 : W := mkw 0x090800d6000081a0 0x000000e0000001c0

def z680 : W := mkw 0x23fdfff6d4257800 0x3bfffffffe007c00

def z681 : W := mkw 0x22d1bf0001a57800 0x36c1ff0001f07c00

def z682 : W := mkw 0x10c170b0e1a05546 0x9281f0e0e1007dc7

def z683 : W := mkw 0x0010880000000000 0x3ab9cc0000000000

def z684 : W := mkw 0x03fdeaf6d4000000 0x3bb9cce498000000

def z685 : W := mkw 0x19ee10df21fad7f6 0xfdfe00ff01ffffff

def z686 : W := mkw 0x10c17020e1a05446 0xb6c1f000e1f07c07

def z687 : W := mkw 0x10c170b8e1b05302 0x33c1f0f8e0f00000

def z688 : W := mkw 0x32d1ffb8e1b57f46 0xb7c1fff8e1f07fc7

def z689 : W := mkw 0x0000110022204002 0x0000330066000000

def z690 : W := mkw 0x0418cc649005ace4 0x3eb9cce0010ffdc0

def z691 : W := mkw 0x900040b9ea10075f 0xc10000fffe0003ff

def z692 : W := mkw 0x22f5ae0001873800 0x3eb9cc00010ffc00

def z693 : W := mkw 0x0000000000000000 0x3cb80000010f8000

def z694 : W := mkw 0x0418c86490018ce4 0xb7b9c0e08103ffc7

def z695 : W := mkw 0x03fdeaf6d4000000 0x3affffe000000000

def z696 : W := mkw 0x10017028e1b05746 0x8601f000e1f07fc7

def z697 : W := mkw 0x900215092bfc775f 0xef463f1ffffc7fff

def z698 : W := mkw 0x2af7bf0901fffbb0 0x7effff0001fffff8

def z699 : W := mkw 0x0bffeaf7d44a80b0 0x7bfffffffe0f8038

def z700 : W := mkw 0x02f5ea20d4000000 0x3affff00fe000000

def z701 : W := mkw 0x0000000820100202 0x81000018e0000207

def z702 : W := mkw 0x01ec00de01900300 0x3dfe00ff01f003c0

def z703 : W := mkw 0x84fecc6499cfaced 0xffffcce499ffffff

def z704 : W := mkw 0x800215092a7c621b 0xee463f0000fc623f

def z705 : W := mkw 0x84d8ccfc9995afed 0xfff9ccfc99ffffff

def z706 : W := mkw 0x80108c0008052809 0xffb9cc04990ffe3f

def z707 : W := mkw 0x0ffdeaf6d5838de4 0x10b9c0e001039dc0

def z708 : W := mkw 0x10c050b8a1b05746 0xb7c1c0f881f07fc7

def z709 : W := mkw 0x843e8c44184fa8a9 0x483e0c04180f8038

def z710 : W := mkw 0x03fdaad600000000 0x3bfffffffe000000

def z711 : W := mkw 0x90c365b1cbcc355d 0x5887cfe71f0c1df8

def z712 : W := mkw 0x02f7ba0001ea5000 0x3effff0001fffc00

def z713 : W := mkw 0xa00215092a7d7a1b 0xef463f1ffefc7e3f

def z714 : W := mkw 0x22f5ba0001a35800 0x14b9c00001f3fc00

def z715 : W := mkw 0x800215092a7c621b 0xfffe3f1fffffe23f

def z716 : W := mkw 0x2b19bfdf0035fbb0 0x4301ffff00007ff8

def z717 : W := mkw 0x00ca00dd01d883b0 0x7dfe00ff01ff83f8

def z718 : W := mkw 0x0018884410000000 0x2b7e3f1ffe000000

def z719 : W := mkw 0x22f7bf0001ef7800 0x1cbfcf0001fffc00

def z720 : W := mkw 0x10c170b8e1b05746 0xb7c1fff8fff07fc7

def z721 : W := mkw 0x8418cc649805aced 0xfff9fcfcf90fffff

def z722 : W := mkw 0x950840fefc1087ef 0xc10000fffe0003ff

def z723 : W := mkw 0x10c170b8e1b05746 0x94c1f0f861f07fc7

def z724 : W := mkw 0xa2f7bf010bef7819 0x7effff0001fffc38

def z725 : W := mkw 0x00e7350001ee7000 0x3effff0001fffc00

def z726 : W := mkw 0x00f7bc0001ef7800 0x3efffc0001fffc00

def z727 : W := mkw 0x00c1200000000000 0x3bc7ff1ffe000000

def z728 : W := mkw 0x00e4000000000000 0x3bfe3f1ffe000000

def z729 : W := mkw 0x8410dc20b8256c4f 0x8201fc00f8007c07

def z730 : W := mkw 0x090a00df01da83b0 0x7db800ff01ff83f8

def z731 : W := mkw 0x09ee00d601ca81a0 0x7dfe00e401ff83f8

def z732 : W := mkw 0x210a55f6d5ef7800 0x050000fffffffc00

def z733 : W := mkw 0x10c170b8e1b05746 0xbfc7f0ffe1f07fc7

def z734 : W := mkw 0x87e526924c05aced 0xc446331b670fffff

def z735 : W := mkw 0x09ee004701ca80b0 0x7dfe00e701ff83f8

def z736 : W := mkw 0x02f5be0001a57800 0x3effff0001fffc00

def z737 : W := mkw 0x22f7bf0001ef7800 0x3fffff18e1fffc00

def z738 : W := mkw 0x22f7bf0001ef7800 0x3effff1b67fffc00

def z739 : W := mkw 0x8418cc649805aced 0xd6b9cce0990fffff

def z740 : W := mkw 0x0000000000000000 0xaf463f1ffe006207

def z741 : W := mkw 0x27fdeaf6d5839ce4 0x10b9c0e001039dc0

def z742 : W := mkw 0x03fdeaf6d40084e4 0xffffffffff0fffff

def z743 : W := mkw 0x880215092bfe631b 0xc400000000fc623f

def z744 : W := mkw 0x800215092bfe621b 0xc400000001ffe23f

def z745 : W := mkw 0x0a13ea29d5da83b0 0x4601ff00ffff83f8

def z746 : W := mkw 0x0bee02df05da83b0 0x7dfe03ff07ff83f8

def z747 : W := mkw 0x83fffffffe7c621b 0xd4b9c0e000fc623f

def z748 : W := mkw 0x10c170b8e1b05746 0xb6c1f0e001f07fc7

def z749 : W := mkw 0x033cca6694000000 0x3bfffffffe000000

def z750 : W := mkw 0x22f7bf0001ef7800 0x3fffff1f01fffc00

def z751 : W := mkw 0x8418cc649805aced 0xf7b9c0e0810fffff

def z752 : W := mkw 0x09ee00df01da83b0 0x7ffe3fff01ff83f8

def z753 : W := mkw 0x22f7bf0001ef7800 0x3fffffe001ffffc0

def z754 : W := mkw 0x22f7bf0001ef7800 0x36f9f00001fffc00

def z755 : W := mkw 0x32f7bf0061ef7802 0x3effff0061fffc00

def z756 : W := mkw 0x900215092bfc731b 0xc400000000fc623f

def z757 : W := mkw 0x0118c8f6d4000000 0x3bfffffffe000000

def z758 : W := mkw 0x01ec00de019083a0 0x7dfe00ff01ff83f8

def z759 : W := mkw 0x09ee00df01da83b0 0x55b800ff01ff83f8

def z760 : W := mkw 0x8418cc649805aced 0xffffffe4990fffff

def z761 : W := mkw 0x94d9bcdc79b5fbab 0x48783c1c78ff8038

def z762 : W := mkw 0x10e570b8e1b05746 0xbffff0f8e1f07fc7

def z763 : W := mkw 0x22f7bf0001ef7800 0x3effff00fffffc00

def z764 : W := mkw 0x841a8d451a4da8b9 0x48380c04180f8038

def z765 : W := mkw 0x22f7bf0001ef7800 0x3cffc00001fffc00

def z766 : W := mkw 0x09ee00df01da83b0 0x5cbe00e701ff83f8

def z767 : W := mkw 0x00c050b8a1b04746 0xb7c1f0f8e1f07fc7

def z768 : W := mkw 0x100840fce01087e6 0xc10000fce00003ff

def z769 : W := mkw 0x23fdeaf6d4030800 0x3bfffffffe038000

def z770 : W := mkw 0x13fdeaf6d5801100 0x3bfffffffe000000

def z771 : W := mkw 0x09ee00df01da83b0 0x7dfe0fff1fff83f8

def z772 : W := mkw 0x22f5aa0001831800 0x34f9c00001f39c00

def z773 : W := mkw 0x8df6ccbb99df2f5d 0x8247cc1b98f07c07

def z774 : W := mkw 0x3236cfb8e05f2f46 0x893e0ff8e00f83c7

def z775 : W := mkw 0x22f7aa0001cb1800 0x3effff0001ff9c00

def z776 : W := mkw 0x8418cc649805aced 0xfeb9cce0010fffff

def z777 : W := mkw 0x22f7bf0001ef7800 0x3eb9cc0001fffc00

def z778 : W := mkw 0x03fc8ad614000000 0x3bfe3ffffe000000

def z779 : W := mkw 0x00e6000001ca0000 0x3effc00001fffc00

def z780 : W := mkw 0x20129d0001ef7800 0x14b9c00001fffc00

def z781 : W := mkw 0x02f5ea20d4000000 0x3bffff1ffe000000

def z782 : W := mkw 0x89ec15d62ba6e1ab 0x92b83fe0ff03e1c7

def z783 : W := mkw 0x900215092a7c765f 0xc400000000fc7e3f

def z784 : W := mkw 0xa2f7bf0009ef7809 0x7effff0419fffc38

def z785 : W := mkw 0x22f7bf0001ef7800 0x3fffff0499fffc00

def z786 : W := mkw 0x800215092a7c621b 0x8000000000f06007

def z787 : W := mkw 0x10c170b9e1b05756 0xf7c1f0ffe1f07fff

def z788 : W := mkw 0x13fdeaf6d4000544 0x3bfffffffe0001c0

def z789 : W := mkw 0x09ee00df01da83b0 0x7dfe33ff67ff83f8

def z790 : W := mkw 0x03fdeaf6d5820000 0x3bffffffff038000

def z791 : W := mkw 0x800215092a7c665f 0xc400000001fc7fff

def z792 : W := mkw 0x01e4009200000000 0x2b463f1ffe000000

def z793 : W := mkw 0x00109c0001a57800 0x3eb9cc0001fffc00

def z794 : W := mkw 0x10c160b8c1901744 0xb7c1c0f881f07fc7

def z795 : W := mkw 0x090a00df005883b0 0x7dfe00ff01ff83f8

def z796 : W := mkw 0x22f7bb0001eb5800 0x36fff30001f3fc00

def z797 : W := mkw 0x03fdeaf6d4000000 0x7ffffffffe0c0238

def z798 : W := mkw 0xa2f5aa092b931a1b 0xd1b9c01fff039e3f

def z799 : W := mkw 0x8411fc2098257c4d 0x8201fc0098007c07

def z800 : W := mkw 0x09ee00df01da83b0 0x54fe00fb01ff83f8

def z801 : W := mkw 0x10c170b8e1b05746 0xbfc1fcfcf9f07fc7

def z802 : W := mkw 0x800215092a7c621b 0xffc63ffffffc63ff

def z803 : W := mkw 0x22f5bf0001a77800 0x36f9ff0001f3fc00

def z804 : W := mkw 0x03f5aa9244000000 0x3bffff1ffe000000

def z805 : W := mkw 0xa6ef736499ead4ed 0xc14633e498f003ff

def z806 : W := mkw 0x140840fcf01087e6 0x810000f8e00003c7

def z807 : W := mkw 0x12c172b8e5b05746 0xb7c1f3f8e7f07fc7

def z808 : W := mkw 0x32c173b8e1b05746 0xb7c1f3f8e1f07fc7

def z809 : W := mkw 0x080a004d01da83b0 0x54b800e001ff83f8

def z810 : W := mkw 0x10c170b8e1b05746 0xb7c1f0fffff07fc7

def z811 : W := mkw 0x10c170b8e1b05746 0xffc1f0fce1fc7fff

def z812 : W := mkw 0x89ee15df2bfee3bb 0xd4b800e001ffe3ff

def z813 : W := mkw 0x00c170b881b05744 0xb7c1f0f881f07fc7

def z814 : W := mkw 0x800215092a7c621b 0xe700000080fc623f

def z815 : W := mkw 0x10c160b0c1801544 0x3bc7ffffff001dc0

def z816 : W := mkw 0x0010880000000000 0x3bffff1ffe000000

def z817 : W := mkw 0xa2f7bf010bef7819 0x7fffff1ffffffc38

def z818 : W := mkw 0x32f7bf9041ef7900 0x3effff0001fffc00

def z819 : W := mkw 0x841a8d44184da8a9 0x483e0f04180f8038

def z820 : W := mkw 0x133c9a4e35b05746 0x8c3e0f071ff07fc7

def z821 : W := mkw 0xa6f7bf0019ef7809 0x3effff0019fffc00

def z822 : W := mkw 0x22f7bf0001ef7800 0x16b9ff0001fffc00

def z823 : W := mkw 0x80020409085c2219 0xef463f1ffefc623f

def z824 : W := mkw 0x09ef20df41da83b0 0x7dfe30ff61ff83f8

def z825 : W := mkw 0xa00215092a7f6a1b 0xc400000000ffe23f

def z826 : W := mkw 0x10005028a1b05746 0xb7c1f0f8e1f07fc7

def z827 : W := mkw 0x07fdeaf6d4018ce4 0x7fffffffff0f9ff8

def z828 : W := mkw 0x8408406cb81086ef 0xc10000fcf80003ff

def z829 : W := mkw 0xa40215092bfffeff 0xc400000001ffffff

def z830 : W := mkw 0x22f7bf0103ef7810 0x3effff0307fffc00

def z831 : W := mkw 0x0d0840ff901087f4 0x410000ff000003f8

def z832 : W := mkw 0x84188c440805aced 0xffb9cce4010fffff

def z833 : W := mkw 0x10c170b8e1b05746 0xb781c0e081f07fc7

def z834 : W := mkw 0x03fdeaf6d4000000 0x0347fffffe000000

def z835 : W := mkw 0x8618ce649c05aced 0xffb9cfe49f0fffff

def z836 : W := mkw 0x8d0840ffdc1087fd 0xc10000fffe0003ff

def z837 : W := mkw 0x20d3bd0001ef7800 0x3ef9fc0001fffc00

def z838 : W := mkw 0x03fdeaf6d4000000 0x3fffffffff0003c0

def z839 : W := mkw 0x22e7330001ea5000 0x3efff30001fffc00

def z840 : W := mkw 0x00c17028a1b05646 0xb7c1f0f8e1f07fc7

def z841 : W := mkw 0xa2f7bf092bff7a1b 0xd4b9c00001fffe3f

def z842 : W := mkw 0x00f6880001cb0800 0x3cffc00001ff9c00

def z843 : W := mkw 0x000040b0c0000000 0x2b463ffffe000000

def z844 : W := mkw 0x840a5564986ce4ed 0xef463fe498fc63ff

def z845 : W := mkw 0x0211ea20d4000000 0x0247ff1bfe000000

def z846 : W := mkw 0x19c170bbe1b05756 0xb7c1f0fbe1f07fc7

def z847 : W := mkw 0x19e570bae1b25746 0xb7c1f0f8e1f07fc7

def z848 : W := mkw 0xa2f7bf0009ef7809 0xbeffff0099fffc07

def z849 : W := mkw 0x90c375b9ebfc775f 0xd481c0e001fc7fff

def z850 : W := mkw 0x8410dd20ba256c4f 0x8201cc0098007c07

def z851 : W := mkw 0x09ec00de019283a0 0x7df800fc01ff83f8

def z852 : W := mkw 0x192f7067e06ad4f6 0xca3ff007e00ffc3f

def z853 : W := mkw 0x19ef20df41da93b0 0x7dfe00ff01ff83f8

def z854 : W := mkw 0x100050b8e0304746 0xb7c1f0f8e1f07fc7

def z855 : W := mkw 0x00c170b8e0304646 0xb7c1f0f8e1f07fc7

def z856 : W := mkw 0x10c170b0e1a05546 0xb6c1f0e0e1f07dc7

def z857 : W := mkw 0x09ef20df01da83b0 0x7ffff0ff01ff83f8

def z858 : W := mkw 0x00c170b0c1a05444 0xb7c1f0f8e1f07fc7

def z859 : W := mkw 0x10c170b8e1b05746 0xb5c1c0f801f07fc7

def z860 : W := mkw 0x8418cc649805aced 0xffb9ccffff0fffff

def z861 : W := mkw 0x22f7bf0101ef7810 0x7effff0701fffc38

def z862 : W := mkw 0x2bf7bf0301ef7810 0x3effff0301fffc00

def z863 : W := mkw 0xa00215092a7d7a1b 0xc400000000fc7e3f

def z864 : W := mkw 0x10c170b8e1b05746 0x8341f0f8e0f07fc7

def z865 : W := mkw 0x10c170b8e1b05746 0x92c1f0f8e1f07dc7

def z866 : W := mkw 0x03fdaad654000000 0x3affff1f7e000000

def z867 : W := mkw 0x03fdaa4614000000 0x3bffff1ffe000000

def z868 : W := mkw 0x00128c00004d2800 0x3effcc0001fffc00

def z869 : W := mkw 0x03ed22d644000000 0x3bfe3ffffe000000

def z870 : W := mkw 0x000a0044004880a0 0x7dfe00e401ff83f8

def z871 : W := mkw 0x03fdeaf6d5801000 0x3bffffffff001c00

def z872 : W := mkw 0x041ad96db279cef6 0x10fff3fb67f39dc0

def z873 : W := mkw 0x20f69d0001ef7800 0x3effcc0001fffc00

def z874 : W := mkw 0x80021500086c6009 0xef463f1ffefc623f

def z875 : W := mkw 0x2bee03df01da83b0 0x7dfe03ff01ff83f8

def z876 : W := mkw 0x09ee00df23da83b2 0x7dfe00ff67ff83f8

def z877 : W := mkw 0x840215092a7deabb 0xc400000000ffe23f

def z878 : W := mkw 0x2213bf00006d7800 0x3effff0001fffc00

def z879 : W := mkw 0x0008004400000000 0x3bfe3ffffe000000

def z880 : W := mkw 0x800215092a7ce2bb 0xc400000001ffe3ff

def z881 : W := mkw 0x09ee00df15da83b0 0x7dfe00ff1fff83f8

def z882 : W := mkw 0x0bef22df01da83b0 0x7dfe33ff01ff83f8

def z883 : W := mkw 0xb211ff20ea257c4f 0x8201ff00fe007c07

def z884 : W := mkw 0x0018c864900084e4 0xffb9cce4990fffff

def z885 : W := mkw 0x10c170b9e3b05756 0xb7c1f0fbe7f07fc7

def z886 : W := mkw 0x22f7bf0001ef7800 0x3effff071ffffc00

def z887 : W := mkw 0x800211092a78421b 0xeb463f1ffef0023f

def z888 : W := mkw 0x17fdeaf6d5819de4 0x10b9c0e001039dc0

def z889 : W := mkw 0x8418cc649805aced 0xffbfcfe79f0fffff

def z890 : W := mkw 0x09ee00df01da83b0 0x7fffc0ff01fffff8

def z891 : W := mkw 0x800215092a7c621b 0xc3463f1ffef0623f

def z892 : W := mkw 0x03fdeaf6d4000000 0x097e3ffffe000000

def z893 : W := mkw 0x03ed62f6d4000000 0x2b463ffffe000000

def z894 : W := mkw 0x23f7bf9245ef7800 0x3fffff1ffffffc00

def z895 : W := mkw 0x09ee00df01da83b0 0x7db800e401ff83f8

def z896 : W := mkw 0x22f7bb0001eb5800 0x3affff0001f39c00

def z897 : W := mkw 0x00d1b80001a15800 0x36f9f00001f3fc00

def z898 : W := mkw 0x00ee004d01da82b0 0x7dfe00ff01ff83f8

def z899 : W := mkw 0x11e570bae1b05746 0xb7c7f0fbe1f07fc7

def z900 : W := mkw 0x8518cc669c05aced 0xffb9cce79f0fffff

def z901 : W := mkw 0xa618cf649805aced 0xffb9cfe4990fffff

def z902 : W := mkw 0xa2f7bf010bef7819 0xffffff079ffffe3f

def z903 : W := mkw 0x00c1300001a05000 0x3ef9f00001fffc00

def z904 : W := mkw 0x22f7ba0001eb5800 0x3efff00001fffc00

def z905 : W := mkw 0x0bfdeaf6d40081a0 0x3bfffffffe0001c0

def z906 : W := mkw 0x0008406490000000 0x2b463ffffe000000

def z907 : W := mkw 0x092e004f01da83b0 0x7dbe00e701ff83f8

def z908 : W := mkw 0x03fdeaf6d4000000 0x12fffffbfe000000

def z909 : W := mkw 0x00005028a0304646 0xb781c0e081f07fc7

def z910 : W := mkw 0xa2f7bf012bef781b 0xfeffff07fffffc3f

def z911 : W := mkw 0x8418cc64dc05aced 0xffb9cce4ff0fffff

def z912 : W := mkw 0x09ee00d701ca81b0 0x7cfe00e701ff81f8

def z913 : W := mkw 0x0000502081a05444 0xb781c0e081f07fc7

def z914 : W := mkw 0x0018cc648005ace4 0xffb9cce4810fffff

def z915 : W := mkw 0x03fdeaf6d4000444 0xbbfffffffe0003c7

def z916 : W := mkw 0x22f5be0001a77800 0x3ef9fc0001fffc00

def z917 : W := mkw 0x22f7aa0001cb1800 0x14b9c00001ff9c00

def z918 : W := mkw 0x10c040b8e1900746 0xb7c1c0f8e1f07fc7

def z919 : W := mkw 0x0219ea64d4000000 0x3bfffffffe000000

def z920 : W := mkw 0x900215092a7c675f 0xc400000000fc63ff

def z921 : W := mkw 0x0bef22df45da83b0 0x7dfe00ff01ff83f8

def z922 : W := mkw 0x000a004d005882b0 0x7db800e401ff83f8

def z923 : W := mkw 0x13e572bae5b05746 0xbfc7fffffff07fc7

def z924 : W := mkw 0x8418cc649805aced 0xffffccff990fffff

def z925 : W := mkw 0x10c170b8e1b05746 0xbfc7fff8e1f07fc7

def z926 : W := mkw 0x880215092a7ee2bb 0xc400000000ffe23f

def z927 : W := mkw 0x0000000000000000 0x6f463f1ffe0c0238

def z928 : W := mkw 0x0bfdeaf6d5820100 0x3bfffffffe000000

def z929 : W := mkw 0x100170b8e1b05746 0x8701f0f8e1f07fc7

def z930 : W := mkw 0x03e5229244000000 0x08463f1f7e000000

def z931 : W := mkw 0x10005028a1b05746 0x9481c0e001f07fc7

def z932 : W := mkw 0x10c170b8e1b05746 0xb7c7f3fbe7f07fc7

def z933 : W := mkw 0x03fdeaf6d4000000 0x3fffffffff0f8000

def z934 : W := mkw 0x010800d600000000 0x2b463ffffe000000

def z935 : W := mkw 0x8418cc649805aced 0xffb9ffe4ff0fffff

def z936 : W := mkw 0x09ee00df01da83b0 0x7ffe30ffe1ff83f8

def z937 : W := mkw 0x09ee00df01da83b0 0x7cfe00e001ff83f8

def z938 : W := mkw 0x10c170b8e1b05746 0x9581c0f8e1f07fc7

def z939 : W := mkw 0x00016020c0000000 0x2b47ff1ffe000000

def z940 : W := mkw 0x10017028e1b05746 0xb781f0e0e1f07fc7

def z941 : W := mkw 0x8418cd649a05aced 0xffb9cfe49f0fffff

def z942 : W := mkw 0x8418cc649805aced 0xdcb9cce4190fffff

def z943 : W := mkw 0x8611ff20fe256c4f 0x8201ff00fe007c07

def z944 : W := mkw 0x0000000000000000 0x08463f1f7e000000

def z945 : W := mkw 0x09ef20df01da93b0 0x7dffc0ff01ff9ff8

def z946 : W := mkw 0x10c170b0c1a05544 0xb7c1f0e081f07fc7

def z947 : W := mkw 0x0bef22df45da83b0 0x7ffe3fffffff83f8

def z948 : W := mkw 0x00e7200001ca1000 0x3cffc00001ff9c00

def z949 : W := mkw 0x09ee00df01da83b0 0x7dfe00ffffff83f8

def z950 : W := mkw 0x02e5220000000000 0x2b463f1ffe000000

def z951 : W := mkw 0x092e00df01da83b0 0x4d3e00ff01ff83f8

def z952 : W := mkw 0x8418cc649805aced 0xd5b9c0e4990fffff

def z953 : W := mkw 0x09ee00df01da83b0 0x7ffe0cff99ff83f8

def z954 : W := mkw 0x22f7bf0001ef7800 0x14fff30001fffc00

def z955 : W := mkw 0x00c1209040000000 0x2b463f1ffe000000

def z956 : W := mkw 0x980215092bfef7ff 0xc400000001ffffff

def z957 : W := mkw 0x09ee01df03da83b0 0x7dfe03ff07ff83f8

def z958 : W := mkw 0x03f5eab2d4000000 0x2b47ff1ffe000000

def z959 : W := mkw 0x10c171b8e3b05746 0xb7c1f3f8e7f07fc7

def z960 : W := mkw 0x033deaf6d4000000 0x0b3ffffffe000000

def z961 : W := mkw 0x17fdeaf6d5819de4 0x3bffffffff039dc0

def z962 : W := mkw 0x09ee00df01da83b0 0xfffe00ff81ffe3ff

def z963 : W := mkw 0x9d0840fff81087ff 0xc10000fff80003ff

def z964 : W := mkw 0x0000502080204444 0xb7c1f0e081f07fc7

def z965 : W := mkw 0x10c170b8e1b05746 0x9681f0e0e1f07fc7

def z966 : W := mkw 0x1bfdeaf6d58295e4 0x3bffffffff039dc0

def z967 : W := mkw 0x22f5ba0001a35800 0x10f9f00001f39c00

def z968 : W := mkw 0x0002100920784212 0xef463f1ffefc623f

def z969 : W := mkw 0x0010c82090000000 0x2b47ff1ffe000000

def z970 : W := mkw 0x800215092a7c621b 0x4000000000fc0038

def z971 : W := mkw 0x8d0840ffba1087ff 0xc10000fffe0003ff

def z972 : W := mkw 0x00109c0000256800 0x3ef9fc0001fffc00

def z973 : W := mkw 0x9411fd20fa257c4f 0x8201ff00fe007c07

def z974 : W := mkw 0x8418cc649805aced 0xfdb9c0e4010fffff

def z975 : W := mkw 0x880215092a7ce3bb 0xc400000000fc63ff

def z976 : W := mkw 0x02f7ae0001cf2800 0x3effff0001fffc00

def z977 : W := mkw 0x00c0402081800444 0xb7c1c0e081f07fc7

def z978 : W := mkw 0x03fdeaf6d40080a0 0x7bfffffffe0003f8

def z979 : W := mkw 0xb00215092bff7f5f 0xc400000001ffffff

def z980 : W := mkw 0x19ee00df61da83b2 0x7dfe00ff61ff83f8

def z981 : W := mkw 0x23fdeaf6d5821000 0x3bfffffffe000000

def z982 : W := mkw 0x800215092a7d6a1b 0xef463f1ffffffe3f

def z983 : W := mkw 0x22f7bf0021ef7802 0xbeffff00e1fffc07

def z984 : W := mkw 0x03fdeaf6d4000000 0xbffffffffe006207

def z985 : W := mkw 0x840844648805aced 0xffb9c0e4810fffff

def z986 : W := mkw 0x100050b8e1b05746 0xb781c0f8e1f07fc7

def z987 : W := mkw 0x00d08c0001852800 0x3ef9cc0001fffc00

def z988 : W := mkw 0x00004020d4000000 0x2b463f1ffe000000

def z989 : W := mkw 0x23fdeaf6d4011800 0x3bfffffffe001c00

def z990 : W := mkw 0x07fdeaf6d4010c44 0x3bfffffffe001c00

def z991 : W := mkw 0x09ee00df01da83b0 0x497e00ff00ff83f8

def z992 : W := mkw 0x0000402880100644 0xb7c1c0f881f07fc7

def z993 : W := mkw 0x00c80044018080a0 0x7df800e401ff83f8

def z994 : W := mkw 0xa63e8f451a4fa8b9 0x483e0f071e0f8038

def z995 : W := mkw 0x800a154d2a7ce2bb 0xfdb800e401ffe3ff

def z996 : W := mkw 0x800215092bfc631b 0xc400000001fc63ff

def z997 : W := mkw 0xab3e8f470a4fa8b9 0x483e0f071e0f8038

def z998 : W := mkw 0xa2f7bf002bef780b 0xbeffff0001fffc07

def z999 : W := mkw 0x00129d00006d6800 0x3eb9cc0001fffc00

def z1000 : W := mkw 0x01ed60f6c0000000 0x3bfffffffe000000

def z1001 : W := mkw 0x9611fe20fc257c4f 0x8201ff00fe007c07

def z1002 : W := mkw 0x0008004c001082a0 0x7df800fc01ff83f8

def z1003 : W := mkw 0xa2f7bf000bef7809 0x3effff001ffffc00

def z1004 : W := mkw 0x20129d0001ef7800 0x3effff0001fffc00

def z1005 : W := mkw 0x03f5aa9254000000 0x00463f1b7e000000

def z1006 : W := mkw 0x800215092bfc721b 0xc400000001fc7e3f

def z1007 : W := mkw 0x0324020204000000 0x2b463f1ffe000000

def z1008 : W := mkw 0x3be7339b61fa5312 0x0046331b60f00000

def z1009 : W := mkw 0x0418c86490018ce4 0xffb9c0e4810fffff

def z1010 : W := mkw 0x22d1bf0001a57800 0x3ef9ff0001fffc00

def z1011 : W := mkw 0x190840ffc01087f4 0x410000ff000003f8

def z1012 : W := mkw 0x840215092a7ce6ff 0xc400000000fc63ff

def z1013 : W := mkw 0x9408406cb81087ef 0xc10000e4980003ff

def z1014 : W := mkw 0x0100009244000000 0x2b463f1ffe000000

def z1015 : W := mkw 0x03fdeaf6d5800000 0x3ffffffffff00000

def z1016 : W := mkw 0x00128c0001cf2800 0x3eb9cc0001fffc00

def z1017 : W := mkw 0x800215092a7d6a1b 0xc400000001fffe3f

def z1018 : W := mkw 0x000a004401ca80a0 0x7db800e401ff83f8

def z1019 : W := mkw 0xa41a8d44184fa8a9 0x48380c04180f8038

def z1020 : W := mkw 0x00d3bd0001ed7800 0x3effff0001fffc00

def z1021 : W := mkw 0x012c004600000000 0x2b7e3f1ffe000000

def z1022 : W := mkw 0x2237bf0001ef7800 0x0e3fff0001fffc00

def z1023 : W := mkw 0x800200092a58021b 0xef463f1ffefc023f

def z1024 : W := mkw 0x2bfdeaf6d58399a0 0x3bffffffff039dc0

def z1025 : W := mkw 0x22f7bf0001ef7800 0x12ffff0001f3fc00

def z1026 : W := mkw 0x84084064980084ed 0xffb9c0e4990fffff

def z1027 : W := mkw 0x10c17020e1a05446 0xb7c1f0e0e1f07fc7

def z1028 : W := mkw 0x02f7bf00006d6800 0x3effff0001fffc00

def z1029 : W := mkw 0x22369f00006f6800 0x3effff0001fffc00

def z1030 : W := mkw 0x12e572b8e1b05746 0xb7c7f3f8e1f07fc7

def z1031 : W := mkw 0x01fcc8f690000000 0x3bfffffffe000000

def z1032 : W := mkw 0xa00215092bfe721b 0xc400000000fc623f

def z1033 : W := mkw 0x22f7bf0001ef7800 0x0a7fff0000fffc00

def z1034 : W := mkw 0xa80215092bfffbbb 0xc400000001ffffff

def z1035 : W := mkw 0x03f5eab2d4000000 0x3affff1bfe000000

def z1036 : W := mkw 0x800215092a7c621b 0xed00000400fc623f

def z1037 : W := mkw 0x03fdeaf6d4010800 0x3bffffffff039c00

def z1038 : W := mkw 0x1be7329b65fa5312 0x0046331b66f00000

def z1039 : W := mkw 0x03fdeaf6d4000000 0x0a7fff1ffe000000

def z1040 : W := mkw 0x8c0215092bffefff 0xc400000001ffffff

def z1041 : W := mkw 0x08ca00dd01da83b0 0x7df800fc01ff83f8

def z1042 : W := mkw 0x03fdeaf6d4000444 0x3bffffffff001dc0

def z1043 : W := mkw 0x8408406d981086fd 0xc10000ff980003ff

def z1044 : W := mkw 0x20e7350001ef7800 0x3efff00001fffc00

def z1045 : W := mkw 0x80025529aa7c665f 0xf781c0e081fc7fff

def z1046 : W := mkw 0x940215092bfdffff 0xc400000001ffffff

def z1047 : W := mkw 0x080a004d01da83b0 0x7dfe00ff01ff83f8

def z1048 : W := mkw 0x092e004f005a82b0 0x7dfe00ff01ff83f8

def z1049 : W := mkw 0x8c1a8c45184fa8b9 0x48380c04180f8038

def z1050 : W := mkw 0x09ee00df01da83b0 0x75f800f801ff83f8

def z1051 : W := mkw 0x873e8f471e4da8b9 0x483e0f071e0f8038

def z1052 : W := mkw 0x0bfdeaf6d40280a0 0x3bfffffffe038000

def z1053 : W := mkw 0x19e7319b63fa5312 0x0046331b66f00000

def z1054 : W := mkw 0x22f7bb0001eb5800 0x10b9c00001f39c00

def z1055 : W := mkw 0x840840fc981087ed 0xc10000fc980003ff

def z1056 : W := mkw 0x03fdeaf6d4000444 0xbbfffffffe007c07

def z1057 : W := mkw 0x22f7bf0023ef7802 0x3effff0067fffc00

def z1058 : W := mkw 0x22f5ba0001a35800 0x3effff0001f3fc00

def z1059 : W := mkw 0x033dea66d4000000 0x2b7fff1ffe000000

def z1060 : W := mkw 0x07fdeaf6d40084e4 0x3bfffffffe0001c0

def z1061 : W := mkw 0xb611ff20f8257c4f 0x8201ff00f8007c07

def z1062 : W := mkw 0x00c160b8c1900744 0xb7c1f0f8e1f07fc7

def z1063 : W := mkw 0xa611ff20dc257c4d 0x8201ff00fe007c07

def z1064 : W := mkw 0x800014082834620b 0xef463f1ffefc623f

def z1065 : W := mkw 0x033c8a4614000000 0x087e3f1f7e000000

def z1066 : W := mkw 0xa73e8f461c4fa8a9 0x483e0f071e0f8038

def z1067 : W := mkw 0x23f7bf9245ef7800 0x3effff0001fffc00

def z1068 : W := mkw 0x03fdeaf6d40080a0 0x7bfffffffe0f8038

def z1069 : W := mkw 0xa611ff20ba257c4f 0x8201ff00fe007c07

def z1070 : W := mkw 0x22f7ae0001cf3800 0x3effcc0001fffc00

def z1071 : W := mkw 0x0108004614000000 0x2b463f1ffe000000

def z1072 : W := mkw 0x090840ff801087f4 0xc10000ff800003ff

def z1073 : W := mkw 0x32e572b8e1b25746 0xb7c1f0f8e1f07fc7

def z1074 : W := mkw 0x0000402080000444 0xbfc7ffffff007fc7

def z1075 : W := mkw 0xa2f7bf0009ef7809 0xfeffff0001fffe3f

def z1076 : W := mkw 0x10e570b8e1b25746 0xb7f9f0f8e1f3ffc7

def z1077 : W := mkw 0x8d3e8d471a4fa8b9 0x483e0f071e0f8038

def z1078 : W := mkw 0x800844648804a4ed 0xffb9cce4990fffff

def z1079 : W := mkw 0x09c800df019083b0 0x7df800ff01ff83f8

def z1080 : W := mkw 0x800215092a7c621b 0xffc7ff1ffffc7e3f

def z1081 : W := mkw 0x9410dc20b8257c4f 0x8201cc0098007c07

def z1082 : W := mkw 0x092e00df005a83b0 0x6d7e00ff00ff83f8

def z1083 : W := mkw 0xa2f7bf002bef780b 0xbfffff1ffffffc07

def z1084 : W := mkw 0x22f7bb0001eb5800 0x3cfff30001ff9c00

def z1085 : W := mkw 0x0319eaf6d4000000 0x2b47fffffe000000

def z1086 : W := mkw 0x13fdeaf6d5801544 0xbfffffffff007fc7

def z1087 : W := mkw 0x08e6009901da83b0 0x7dfe00f801ff83f8

def z1088 : W := mkw 0x23f7bf0205ef7800 0x3effff0307fffc00

def z1089 : W := mkw 0x841add6dba7deeff 0xd4b9c0e001ffffff

def z1090 : W := mkw 0x10c170b8e1b05746 0xbff9f0f8e1ffffc7

def z1091 : W := mkw 0x033ccaf6d4000000 0x2b7e3ffffe000000

def z1092 : W := mkw 0x1bfdeaf6d58295e4 0x10b9c0e001039dc0

def z1093 : W := mkw 0x00e5300001a25000 0x36f9f00001f3fc00

def z1094 : W := mkw 0x8f3e8e471c4fa8b9 0x483e0f071e0f8038

def z1095 : W := mkw 0x22f7bf0015ef7800 0x3effff001ffffc00

def z1096 : W := mkw 0x33fdeaf6d5831d44 0x3bffffffff039dc0

def z1097 : W := mkw 0x22f7bf0045ef7800 0x3effff0067fffc00

def z1098 : W := mkw 0x2be7339b23fa5312 0x0046331b66f00000

def z1099 : W := mkw 0x850840fffe1086ff 0xc10000fffe0003ff

def z1100 : W := mkw 0x03e562b2c4000000 0x3bc7fffffe000000

def z1101 : W := mkw 0x8410cc208805aced 0xffb9cce0810fffff

def z1102 : W := mkw 0x03fdeaf6d40080a0 0x3bffffffff0381c0

def z1103 : W := mkw 0x03fdeaf6d4000000 0x3fffffffff007c00

def z1104 : W := mkw 0x09ee00df01da83b0 0x58fe00ff01ff81f8

def z1105 : W := mkw 0x8c08406d981087fd 0xc10000e4980003ff

def z1106 : W := mkw 0x09ec00d6018281a0 0x3bfe3fffff0381c0

def z1107 : W := mkw 0x0000402080000000 0x3bc7fffffe000000

def z1108 : W := mkw 0x0000402881900744 0xb781c0e081f07fc7

def z1109 : W := mkw 0x800010092a30421b 0xef463f1ffef0623f

def z1110 : W := mkw 0x22f7bf9001ef7900 0x3effffe001fffdc0

def z1111 : W := mkw 0x2bef22df01da93b0 0x7dfe00ff01ff83f8

def z1112 : W := mkw 0x100170b8e0305746 0xa741f0f8e0f07fc7

def z1113 : W := mkw 0x00f69d0001ef6800 0x3effff0001fffc00

def z1114 : W := mkw 0x22f7aa0001cb1800 0x10ffc00001f39c00

def z1115 : W := mkw 0xa2f7bf002bef780b 0xffffff04fffffe3f

def z1116 : W := mkw 0x02f5eab0c0000000 0x3bfffffffe000000

def z1117 : W := mkw 0x0008004c019083a0 0x7db800e401ff83f8

def z1118 : W := mkw 0x01ee00df005882b0 0x7dfe00ff01ff83f8

def z1119 : W := mkw 0x190840fee01087e6 0x810000f8e00003c7

def z1120 : W := mkw 0x2213bf0001ef7800 0x3eb9ff0001fffc00

def z1121 : W := mkw 0x00c0009000000000 0x3bc63ffffe000000

def z1122 : W := mkw 0x22f7af0001cf3800 0x3cffcf0001ff9c00

def z1123 : W := mkw 0x0418c86490018ce4 0x3bffffffff039dc0

def z1124 : W := mkw 0x13e572bae5b05746 0xb7c1f0f8e1f07fc7

def z1125 : W := mkw 0x940840fdfa1087ff 0xc10000fffe0003ff

def z1126 : W := mkw 0x01ee00d601ca80a0 0x7dfe00ff01ff83f8

def z1127 : W := mkw 0x990840ffea1087ff 0xc10000fffe0003ff

def z1128 : W := mkw 0x07fdeaf6d4018ce4 0xbfffffffff03ffc7

def z1129 : W := mkw 0x2bf7bf9201ef7900 0x3effff0001fffc00

def z1130 : W := mkw 0x840215092a7d6e5f 0xc400000000fc7e3f

def z1131 : W := mkw 0x80188c440805a8a9 0xffb9cce4990fffff

def z1132 : W := mkw 0x22f7bf0001ef7800 0x7fffff0401fffe38

def z1133 : W := mkw 0x32e7339963fa5312 0x0046331b66f00000

def z1134 : W := mkw 0x8410dd2098256c4d 0x8201ff0098007c07

def z1135 : W := mkw 0x10c1309821b05746 0xb7c1f0f801f07fc7

def z1136 : W := mkw 0x0211aa0000000000 0x2b47ff1ffe000000

def z1137 : W := mkw 0x02348a0000000000 0x2b7e3f1ffe000000

def z1138 : W := mkw 0xa410dd2098257c4d 0x8201cc0098007c07

def z1139 : W := mkw 0x03e5229244000000 0x02463f1bfe000000

def z1140 : W := mkw 0x190840fff41087f6 0xc10000fffe0003ff

def z1141 : W := mkw 0x10c17028a1b05746 0xb7c1f0e081f07fc7

def z1142 : W := mkw 0x00c1309821b05302 0xb7c1f0f8e1f07fc7

def z1143 : W := mkw 0x22f7bf9001ef7800 0x3ffffff801fffc00

def z1144 : W := mkw 0x0000000000000000 0x02463f1bfe000000

def z1145 : W := mkw 0x0ffdeaf6d5838de4 0x3bffffffff039dc0

def z1146 : W := mkw 0x800215092a7c621b 0xca463f1ffefc603f

def z1147 : W := mkw 0x11c170bae5b05746 0xb7c1f0fbe7f07fc7

def z1148 : W := mkw 0x22f7bf0001ef7800 0xbfffff0081fffe07

def z1149 : W := mkw 0x10017028e0305646 0xb7c1f0f8e1f07fc7

def z1150 : W := mkw 0x0201220044000000 0x2b463f1ffe000000

def z1151 : W := mkw 0x03fdeaf6d4000000 0x18ffffff7e000000

def z1152 : W := mkw 0x2237bf00006f7800 0x2e7fff0000fffc00

def z1153 : W := mkw 0xaf3e8f47184fa8b9 0x483e0f07180f8038

def z1154 : W := mkw 0x80108c092a152a1b 0xffb9cc1fff0ffe3f

def z1155 : W := mkw 0xa2f7bf0009ef7809 0xffffff1ffffffe3f

def z1156 : W := mkw 0x03fdeaf6d5800100 0x3bffffffff0001c0

def z1157 : W := mkw 0x22369f0001ef7800 0x3ebfcf0001fffc00

def z1158 : W := mkw 0x01c960f6d4000000 0x3bc7fffffe000000

def z1159 : W := mkw 0x22f5aa0001831800 0x3bffff1fff039c00

def z1160 : W := mkw 0x02d1eab0d4000000 0x3bc7fffffe000000

def z1161 : W := mkw 0x01ec40f6d4000000 0x3bfe3ffffe000000

def z1162 : W := mkw 0x27fdeaf6d5839ce4 0x3bffffffff039dc0

def z1163 : W := mkw 0xa00215092a7f6a1b 0xef463f1ffeffe23f

def z1164 : W := mkw 0x8408406dba1086ff 0xc10000e4980003ff

def z1165 : W := mkw 0x03f5eab2d4000000 0x33c7fffbfe000000

def z1166 : W := mkw 0x09ee00df45da83b0 0x7dfe00ff67ff83f8

def z1167 : W := mkw 0x00ee00dc01da83a0 0x7dfe00fc01ff83f8

def z1168 : W := mkw 0x07fdeaf6d40188a0 0x3bfffffffe038000

def z1169 : W := mkw 0x02fdea6490000000 0x3bfffffffe000000

def z1170 : W := mkw 0x13fdeaf6d4001444 0x3bfffffffe001c00

def z1171 : W := mkw 0x22f68f0001cf2800 0x3effcf0001fffc00

def z1172 : W := mkw 0x841a8c45184da8b9 0x483e0c07180f8038

def z1173 : W := mkw 0x00d9e8f4d0000000 0x3bfffffffe000000

def z1174 : W := mkw 0x00e6009901da0310 0x7dfe00ff01ff83f8

def z1175 : W := mkw 0x22f7bf0001ef7800 0x18ffff0001ff9c00

def z1176 : W := mkw 0x8010cc2088052c4d 0xffb9cce4990fffff

def z1177 : W := mkw 0x0bfdeaf6d58281a0 0x7fffffffff0f83f8

def z1178 : W := mkw 0x800215092a7c621b 0xc9463f1ffefc023f

def z1179 : W := mkw 0x23f7bf9201ef7800 0x3effff1b01fffc00

def z1180 : W := mkw 0x10c170b8f5b05746 0xb7c1f0f8fff07fc7

def z1181 : W := mkw 0x02108a0014000000 0x2b463f1ffe000000

def z1182 : W := mkw 0x09ee00df21da83b2 0xfdfe00ffe1ff83ff

def z1183 : W := mkw 0x08ee004d01da83b0 0x7dfe00e401ff83f8

def z1184 : W := mkw 0x03fdaad654000000 0x2b7e3f1ffe000000

def z1185 : W := mkw 0x22f7bf9041ef7800 0x3effff1861fffc00

def z1186 : W := mkw 0x00080044000080a0 0x7ffe3fffff0f83f8

def z1187 : W := mkw 0x03fdaad654000000 0x39fe3fff7e000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z8,z2,z3,z5,z6]),(0,[z7,z9,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z11,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z13,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z14]),(0,[z10,z15,z1,z2,z3,z5,z6])],[(0,[z1,z16,z2,z17,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z10,z1,z2,z3,z5,z19,z6]),(0,[z20,z10,z1,z2,z3,z5,z6]),(0,[z20,z1,z2,z3,z5,z6,z21])],[(0,[z10,z1,z2,z3,z5,z6,z22]),(0,[z10,z1,z2,z3,z5,z6,z23]),(0,[z24,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z25,z6])],[(0,[z10,z1,z2,z3,z5,z6,z26]),(0,[z27,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z28,z5,z6]),(0,[z10,z1,z29,z2,z3,z5,z6]),(0,[z30,z10,z31,z1,z2,z3,z6])],[(0,[z7,z1,z32,z2,z3,z5,z6]),(0,[z10,z33,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z34,z5,z6]),(0,[z35,z10,z1,z2,z3,z5,z6])],[(0,[z36,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z37,z3,z5,z6]),(0,[z10,z1,z2,z2,z3,z5,z6]),(0,[z10,z38,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z39,z4,z5,z6]),(1,[z40,z10,z2,z3,z5,z41])],[(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z42,z6])]],
   [[(0,[z7,z1,z2,z43,z3,z5,z6]),(0,[z10,z1,z2,z44,z43,z5,z6]),(0,[z45,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z3,z5,z46,z6,z47]),(1,[z1,z2,z3,z5,z6,z48]),(0,[z10,z1,z2,z3,z5,z49,z6])],[(0,[z10,z1,z50,z2,z3,z5,z6]),(0,[z51,z1,z16,z2,z3,z5,z6]),(0,[z52,z7,z1,z2,z3,z5,z6]),(1,[z10,z1,z53,z3,z5,z6]),(0,[z54,z10,z1,z2,z3,z5,z6]),(0,[z55,z10,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z56]),(0,[z57,z10,z1,z2,z3,z5,z6]),(0,[z10,z58,z1,z2,z3,z5,z6]),(0,[z10,z59,z1,z2,z3,z5,z6]),(1,[z60,z1,z2,z3,z5,z6])],[(0,[z1,z32,z2,z3,z4,z5,z6]),(0,[z61,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z6]),(0,[z10,z1,z2,z3,z5,z6,z63]),(0,[z10,z1,z64,z2,z5,z6,z65]),(0,[z10,z1,z2,z3,z5,z6,z66]),(0,[z10,z67,z1,z2,z3,z5,z6])],[(0,[z68,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z69,z3,z5,z6]),(0,[z70,z10,z1,z3,z71,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z72]),(0,[z10,z1,z73,z2,z3,z5,z6]),(0,[z10,z31,z1,z2,z3,z74,z5])],[(0,[z7,z1,z2,z3,z71,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z75]),(0,[z10,z1,z2,z3,z5,z76,z6])],[(0,[z77,z1,z2,z3,z4,z5,z6]),(0,[z78,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z79,z3,z5,z6]),(0,[z40,z10,z1,z2,z3,z5,z41])],[(0,[z51,z80,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z81,z3,z5,z6]),(0,[z10,z82,z1,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z83,z2,z3,z5,z6]),(0,[z84,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z85,z3,z5,z6]),(0,[z86,z10,z1,z2,z5,z6,z87]),(0,[z10,z88,z1,z2,z3,z5,z6])],[(0,[z89,z10,z1,z2,z90,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z10,z92,z1,z2,z3,z5,z6]),(0,[z93,z10,z94,z1,z2,z5,z6]),(1,[z10,z95,z2,z3,z5,z96])],[(0,[z68,z10,z0,z2,z3,z5,z6]),(0,[z10,z1,z16,z2,z3,z5,z6]),(0,[z10,z1,z2,z97,z3,z5,z6]),(0,[z10,z1,z2,z3,z98,z5,z6]),(0,[z10,z1,z2,z3,z5,z99,z6]),(0,[z10,z100,z1,z2,z3,z5,z6]),(0,[z1,z101,z2,z102,z3,z5,z6]),(0,[z60,z10,z1,z2,z3,z5,z6])],[(0,[z103,z10,z1,z2,z3,z5,z6]),(0,[z10,z104,z1,z2,z3,z5,z6]),(0,[z10,z31,z1,z2,z3,z5,z105]),(0,[z10,z1,z2,z3,z106,z5,z6])],[(0,[z10,z1,z107,z2,z3,z5,z6]),(0,[z108,z10,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z21]),(0,[z7,z10,z1,z2,z3,z5,z6]),(0,[z109,z10,z1,z2,z3,z5,z6]),(0,[z110,z10,z1,z2,z3,z5,z6]),(0,[z111,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z112,z2,z3,z5,z6]),(0,[z10,z113,z1,z2,z3,z5,z6])],[(0,[z1,z114,z2,z3,z4,z5,z6]),(0,[z115,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z116,z3,z5,z6]),(0,[z117,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z118,z6]),(0,[z119,z10,z1,z2,z3,z5,z6]),(1,[z120,z1,z2,z3,z5,z6]),(0,[z121,z10,z1,z2,z3,z5,z6])]],
   [[(0,[z122,z10,z1,z2,z3,z5,z6]),(0,[z10,z2,z123,z3,z5,z96,z6]),(0,[z10,z1,z2,z3,z124,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z125])],[(0,[z126,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z127,z3,z5,z6]),(0,[z9,z10,z1,z64,z2,z5,z6])],[(0,[z10,z1,z2,z128,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z129]),(0,[z10,z1,z2,z3,z130,z5,z6])],[(0,[z10,z0,z2,z3,z5,z6,z21]),(0,[z10,z1,z2,z3,z5,z6,z131]),(0,[z10,z1,z2,z3,z5,z6,z132]),(0,[z10,z133,z1,z2,z3,z5,z6])],[(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z134,z7,z1,z2,z3,z5,z6]),(0,[z10,z135,z1,z2,z3,z5,z6]),(1,[z10,z1,z2,z136,z5,z6]),(0,[z10,z1,z2,z3,z5,z137,z6]),(0,[z138,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z139])],[(0,[z10,z1,z2,z90,z140,z5,z6]),(0,[z7,z10,z1,z2,z141,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z142]),(0,[z10,z1,z2,z3,z5,z6,z143]),(0,[z10,z1,z2,z3,z5,z6,z144]),(0,[z10,z1,z2,z3,z145,z5,z6]),(0,[z10,z1,z114,z3,z5,z46,z6]),(0,[z10,z1,z146,z2,z3,z5,z6])],[(0,[z147,z10,z1,z2,z3,z5,z6]),(0,[z93,z10,z1,z2,z145,z5,z6]),(0,[z10,z2,z3,z5,z6,z148,z47]),(0,[z10,z1,z2,z140,z3,z5,z6]),(0,[z10,z1,z2,z3,z149,z5,z6])],[(0,[z150,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z151,z2,z3,z5,z6]),(1,[z10,z104,z2,z3,z5,z6]),(1,[z10,z1,z2,z3,z5,z152])]],
   [[(0,[z10,z1,z2,z153,z3,z5,z6]),(0,[z10,z1,z2,z154,z3,z5,z6]),(0,[z155,z10,z1,z2,z3,z156,z6]),(0,[z10,z1,z2,z157,z3,z5,z6]),(0,[z10,z158,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z159,z5,z6]),(0,[z10,z1,z2,z3,z160,z5,z6])],[(0,[z10,z1,z2,z161,z3,z5,z6]),(0,[z10,z1,z162,z3,z145,z5,z6]),(0,[z10,z1,z163,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z164])],[(0,[z10,z1,z2,z3,z5,z165,z6]),(0,[z7,z10,z1,z97,z3,z5,z6]),(0,[z10,z1,z2,z166,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z167,z6]),(0,[z168,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z169,z2,z3,z5,z6])],[(1,[z170,z32,z2,z3,z5,z6]),(0,[z68,z10,z32,z2,z3,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z171,z3,z5,z6]),(0,[z10,z1,z2,z3,z172,z5,z6])],[(0,[z80,z1,z32,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z65]),(1,[z10,z173,z2,z3,z5,z6]),(1,[z10,z1,z101,z3,z71,z6]),(0,[z70,z10,z1,z2,z3,z5,z47])],[(0,[z174,z10,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z175,z6]),(0,[z155,z10,z2,z3,z5,z6,z21]),(0,[z120,z10,z1,z2,z3,z5,z6])],[(1,[z51,z1,z16,z3,z5,z6]),(0,[z10,z1,z2,z3,z3,z5,z6]),(0,[z176,z10,z1,z2,z3,z5,z6]),(0,[z60,z1,z2,z140,z3,z5,z6])],[(0,[z7,z155,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z177]),(0,[z1,z2,z3,z4,z5,z6,z41]),(0,[z10,z1,z178,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z179])]],
   [[(0,[z10,z1,z2,z3,z5,z6,z180]),(0,[z10,z1,z2,z3,z5,z6,z181]),(0,[z10,z1,z2,z3,z5,z6,z182])],[(0,[z10,z1,z183,z2,z3,z5,z6]),(0,[z184,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z185]),(0,[z186,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z187,z2,z3,z5,z6])],[(0,[z10,z1,z2,z141,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z105]),(0,[z10,z1,z2,z3,z188,z5,z6]),(0,[z189,z10,z190,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z191]),(0,[z10,z192,z1,z2,z3,z5,z6]),(0,[z10,z1,z3,z5,z6,z193,z87])],[(0,[z7,z1,z2,z3,z5,z6,z194]),(0,[z10,z2,z3,z156,z5,z96,z6]),(0,[z10,z1,z2,z3,z195,z5,z6]),(0,[z196,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z74,z5,z87]),(0,[z30,z10,z1,z2,z3,z5,z87])],[(1,[z10,z1,z2,z197,z3,z5]),(0,[z10,z1,z101,z3,z71,z5,z6])],[(0,[z170,z1,z32,z2,z3,z5,z6]),(1,[z7,z1,z2,z141,z5,z6]),(0,[z10,z1,z2,z198,z3,z5,z6]),(0,[z10,z1,z2,z3,z199,z5,z6])],[(0,[z10,z200,z1,z2,z3,z5,z6]),(0,[z201,z10,z1,z2,z3,z5,z6]),(0,[z202,z10,z1,z2,z3,z5,z6]),(0,[z10,z2,z3,z5,z6,z203,z194])],[(0,[z10,z1,z2,z3,z5,z204,z6]),(0,[z10,z1,z2,z3,z5,z205,z6]),(0,[z9,z10,z1,z2,z3,z5,z62])]],
   [[(0,[z10,z1,z2,z3,z206,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z207]),(0,[z10,z1,z2,z3,z5,z6,z208]),(0,[z70,z10,z1,z3,z5,z6,z47]),(0,[z10,z1,z2,z140,z209,z5,z6]),(0,[z10,z1,z2,z3,z5,z210,z6])],[(0,[z89,z10,z1,z2,z39,z5,z6]),(0,[z7,z1,z2,z3,z211,z5,z6]),(0,[z7,z40,z1,z2,z3,z5,z6]),(0,[z10,z1,z212,z2,z3,z5,z6]),(0,[z213,z10,z1,z2,z3,z5,z6]),(0,[z214,z10,z1,z2,z3,z5,z6])],[(0,[z215,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z216,z5,z6]),(0,[z217,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z53,z2,z3,z5,z6]),(1,[z218,z1,z2,z3,z5,z6]),(0,[z10,z1,z64,z2,z140,z5,z6]),(0,[z10,z1,z2,z3,z5,z219,z6])],[(0,[z7,z1,z2,z3,z5,z6,z220]),(0,[z10,z94,z1,z2,z123,z5,z6]),(0,[z10,z1,z2,z3,z221,z5,z6]),(0,[z10,z2,z3,z5,z222,z6,z87])],[(0,[z10,z1,z2,z3,z223,z5,z6]),(0,[z10,z224,z1,z2,z3,z5,z6]),(0,[z10,z190,z1,z3,z5,z46,z6]),(0,[z225,z10,z1,z2,z3,z5,z6])],[(0,[z226,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z65]),(0,[z80,z10,z1,z2,z3,z5,z6]),(0,[z80,z10,z227,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z228])],[(0,[z10,z1,z2,z3,z5,z229,z6]),(0,[z10,z1,z230,z2,z3,z5,z6]),(0,[z231,z10,z1,z2,z3,z5,z6]),(0,[z232,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z233]),(0,[z70,z234,z1,z2,z3,z5,z6]),(0,[z10,z235,z1,z2,z3,z5,z6])],[(0,[z236,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z237,z3,z5,z6]),(0,[z9,z93,z10,z1,z2,z5,z6]),(0,[z120,z1,z2,z3,z5,z6,z177])]],
   [[(0,[z80,z10,z135,z2,z3,z5,z6]),(0,[z238,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z209,z5,z6]),(0,[z1,z2,z3,z5,z6,z48,z65]),(0,[z10,z1,z2,z3,z5,z239,z6])],[(0,[z7,z1,z2,z17,z3,z5,z6]),(0,[z10,z1,z2,z240,z3,z5,z6]),(0,[z1,z2,z3,z241,z4,z5,z6]),(0,[z186,z10,z1,z2,z43,z5,z6]),(0,[z40,z10,z242,z2,z3,z5,z6]),(0,[z10,z94,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z243,z3,z5,z6]),(1,[z244,z10,z1,z2,z6,z65])],[(0,[z89,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z123,z3,z5,z6]),(1,[z245,z1,z2,z3,z5,z6])],[(0,[z10,z190,z1,z242,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z246,z21]),(1,[z1,z2,z3,z5,z6,z247])],[(0,[z10,z248,z1,z2,z3,z5,z6]),(0,[z155,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z194]),(0,[z10,z1,z249,z2,z3,z5,z6])],[(0,[z7,z250,z1,z2,z3,z5,z6]),(0,[z251,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z252,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z253])],[(0,[z170,z10,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z254,z6]),(0,[z244,z10,z1,z2,z5,z62,z6])],[(0,[z250,z10,z1,z2,z5,z62,z6]),(0,[z255,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z256,z3,z5,z6]),(1,[z10,z1,z2,z5,z6,z257]),(1,[z234,z1,z2,z3,z5,z6]),(0,[z258,z10,z1,z2,z3,z5,z6]),(0,[z9,z10,z1,z2,z5,z6,z194]),(0,[z259,z10,z1,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z2,z3,z5,z6,z260])],[(0,[z261,z10,z1,z2,z3,z5,z6]),(0,[z262,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z263,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z152,z6]),(0,[z264,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z265,z3,z5,z6]),(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z267,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z268,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z269]),(0,[z10,z270,z1,z2,z3,z5,z6])],[(0,[z271,z10,z1,z2,z3,z5,z6]),(0,[z272,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z47]),(0,[z10,z1,z2,z273,z3,z5,z6])],[(0,[z10,z1,z2,z3,z274,z5,z6])],[(0,[z10,z1,z2,z3,z5,z275,z6]),(0,[z10,z1,z276,z2,z3,z5,z6]),(0,[z10,z95,z1,z2,z3,z5,z96]),(0,[z10,z1,z2,z3,z5,z277,z6]),(0,[z251,z10,z1,z3,z5,z46,z6]),(0,[z10,z1,z278,z2,z3,z5,z6])],[(0,[z170,z10,z0,z2,z3,z5,z6]),(0,[z10,z1,z2,z279,z3,z5,z6]),(0,[z280,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z90,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z281,z6]),(0,[z10,z266,z2,z3,z156,z5,z6]),(0,[z10,z95,z1,z2,z3,z5,z6])],[(0,[z282,z10,z1,z2,z3,z5,z6]),(0,[z283,z7,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z71,z4,z5,z6]),(1,[z20,z1,z2,z3,z5,z6]),(0,[z40,z284,z1,z2,z3,z5,z6]),(0,[z285,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z286]),(0,[z287,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z288,z140,z5,z6])],[(0,[z10,z1,z2,z3,z5,z289,z6]),(0,[z1,z2,z3,z211,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z290,z6]),(0,[z234,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z2,z5,z6,z291])]],
   [[(0,[z292,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z293,z3,z5,z6])],[(0,[z294,z10,z1,z2,z3,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z295,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z296])],[(0,[z77,z51,z1,z2,z3,z5,z6]),(0,[z10,z297,z1,z2,z3,z5,z6]),(0,[z250,z10,z1,z64,z2,z5,z6]),(0,[z10,z298,z1,z2,z3,z5,z6]),(1,[z284,z1,z2,z3,z5,z6])],[(0,[z299,z10,z1,z2,z3,z5,z6]),(0,[z68,z1,z2,z3,z4,z5,z6]),(0,[z300,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z301])],[(0,[z302,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z303]),(0,[z10,z1,z2,z3,z304,z5,z6]),(0,[z10,z1,z2,z305,z3,z5,z6])],[(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z40,z10,z2,z3,z156,z5,z6])],[(0,[z306,z10,z1,z2,z3,z5,z6]),(0,[z307,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z308,z6]),(0,[z10,z1,z2,z3,z5,z96,z6])],[(0,[z309,z10,z1,z2,z3,z5,z6]),(0,[z189,z10,z2,z43,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z310,z6]),(0,[z10,z266,z1,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z2,z171,z156,z5,z6]),(0,[z10,z1,z2,z311,z71,z5,z6]),(1,[z86,z10,z1,z2,z5,z6])],[(0,[z7,z309,z1,z2,z3,z5,z6]),(1,[z226,z1,z2,z3,z4,z6]),(0,[z312,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z313,z6]),(0,[z10,z1,z2,z3,z5,z6,z314])],[(0,[z10,z1,z2,z3,z315,z5,z6]),(1,[z10,z1,z8,z3,z5,z6]),(0,[z1,z2,z3,z145,z4,z5,z6]),(0,[z10,z1,z316,z2,z3,z5,z6]),(0,[z10,z1,z2,z140,z3,z6,z65])],[(0,[z31,z1,z2,z3,z4,z5,z6]),(1,[z10,z94,z2,z123,z5,z6]),(0,[z10,z1,z2,z3,z156,z5,z6]),(0,[z10,z1,z317,z2,z3,z5,z6]),(0,[z10,z1,z2,z162,z3,z5,z6]),(1,[z1,z2,z102,z3,z5,z6])],[(0,[z318,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z140,z39,z5,z6]),(0,[z10,z1,z2,z3,z319,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z93,z10,z1,z64,z3,z5,z6]),(0,[z117,z10,z2,z3,z5,z6,z194])],[(0,[z170,z10,z32,z2,z3,z5,z6]),(0,[z10,z321,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z209,z5,z62,z6]),(0,[z10,z1,z2,z3,z5,z6,z322])],[(0,[z10,z1,z2,z323,z3,z5,z6]),(0,[z324,z10,z1,z2,z3,z5,z6]),(0,[z325,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z326]),(0,[z10,z1,z2,z3,z5,z327,z6]),(0,[z40,z10,z1,z2,z3,z5,z96]),(0,[z328,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z329,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z330,z6]),(0,[z40,z250,z10,z2,z3,z5,z6]),(0,[z93,z250,z10,z1,z2,z5,z6]),(0,[z40,z10,z1,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z2,z3,z5,z6,z331]),(0,[z10,z1,z101,z17,z3,z5,z6]),(0,[z332,z10,z1,z2,z3,z5,z6]),(0,[z10,z333,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z334])],[(0,[z80,z1,z2,z17,z3,z5,z6]),(0,[z335,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z16,z3,z5,z46,z6]),(1,[z89,z1,z2,z39,z5,z6]),(0,[z10,z336,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z288,z3,z5,z62]),(0,[z10,z31,z1,z2,z3,z6,z87])],[(0,[z10,z32,z2,z3,z5,z6,z21]),(0,[z1,z101,z2,z3,z4,z5,z6]),(0,[z80,z10,z1,z2,z81,z5,z6]),(0,[z10,z1,z2,z3,z337,z5,z6]),(0,[z93,z10,z1,z2,z162,z5,z6]),(0,[z10,z31,z1,z2,z3,z5,z6])],[(0,[z338,z10,z1,z2,z3,z5,z6]),(0,[z7,z77,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z39,z5,z6]),(0,[z10,z1,z2,z3,z5,z339,z6]),(1,[z250,z10,z2,z211,z5,z6])],[(0,[z10,z1,z1,z2,z3,z5,z6]),(0,[z68,z80,z1,z2,z3,z5,z6]),(1,[z9,z10,z1,z2,z5,z194])],[(0,[z10,z340,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z341,z6]),(0,[z40,z10,z0,z2,z3,z5,z6]),(0,[z10,z0,z2,z3,z5,z96,z6]),(0,[z10,z1,z2,z3,z5,z342,z6]),(1,[z10,z135,z2,z3,z5,z6]),(0,[z343,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z344,z3,z5,z6]),(0,[z345,z7,z1,z2,z3,z5,z6]),(1,[z70,z10,z1,z3,z5,z47]),(0,[z10,z1,z2,z3,z5,z6,z346]),(0,[z10,z1,z2,z3,z5,z6,z87])]],
   [[(0,[z7,z1,z16,z2,z3,z5,z6]),(0,[z7,z1,z2,z97,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z5,z6]),(0,[z10,z1,z2,z3,z347,z5,z6]),(0,[z10,z190,z1,z43,z3,z5,z6]),(0,[z348,z10,z1,z2,z3,z5,z6])],[(0,[z7,z104,z1,z2,z3,z5,z6]),(0,[z7,z70,z1,z2,z3,z5,z6]),(0,[z349,z10,z1,z2,z3,z5,z6]),(0,[z10,z350,z1,z2,z3,z5,z6]),(0,[z10,z2,z3,z5,z96,z6,z41]),(0,[z10,z1,z2,z3,z351,z5,z6])],[(0,[z10,z1,z2,z352,z3,z5,z6]),(0,[z1,z2,z162,z3,z4,z5,z6]),(0,[z353,z10,z1,z2,z3,z5,z6]),(0,[z354,z1,z101,z2,z3,z5,z6]),(0,[z10,z1,z2,z288,z5,z6,z65])],[(0,[z355,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z356,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z357])],[(0,[z155,z10,z1,z2,z3,z6,z21]),(0,[z10,z1,z2,z3,z358,z5,z6])],[(0,[z10,z266,z32,z2,z3,z5,z6]),(0,[z309,z10,z1,z2,z90,z5,z6]),(0,[z7,z80,z1,z2,z3,z5,z6]),(0,[z10,z1,z359,z2,z3,z5,z6]),(0,[z109,z80,z1,z2,z3,z5,z6]),(0,[z250,z10,z2,z3,z5,z96,z6]),(0,[z10,z1,z2,z3,z5,z6,z360]),(0,[z10,z361,z1,z2,z3,z5,z6]),(0,[z10,z1,z114,z2,z3,z5,z47]),(0,[z362,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z193]),(0,[z10,z1,z2,z3,z363,z5,z6])],[(0,[z364,z10,z1,z2,z3,z5,z6]),(0,[z1,z365,z2,z3,z4,z5,z6]),(1,[z10,z190,z242,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z366]),(0,[z10,z1,z2,z3,z367,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z368]),(0,[z31,z133,z1,z2,z3,z5,z6])]],
   [[(0,[z7,z68,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z369,z5,z6]),(1,[z10,z1,z97,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z247,z177]),(0,[z244,z10,z1,z2,z5,z6,z65])],[(0,[z1,z2,z3,z4,z5,z6,z21]),(0,[z1,z2,z3,z74,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z56]),(0,[z10,z1,z2,z3,z5,z370,z6]),(0,[z250,z10,z1,z2,z5,z6,z65]),(1,[z354,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z145,z5,z6]),(0,[z371,z10,z1,z2,z3,z5,z6]),(0,[z372,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z373,z6]),(0,[z10,z1,z2,z3,z5,z62,z6])],[(0,[z7,z1,z2,z140,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z374,z6]),(0,[z93,z10,z1,z2,z5,z62,z6]),(0,[z10,z1,z2,z3,z5,z6,z375])],[(0,[z376,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z377,z3,z5,z6]),(0,[z10,z1,z378,z2,z3,z5,z6]),(0,[z10,z1,z379,z2,z3,z5,z6]),(0,[z10,z380,z1,z2,z3,z5,z6])],[(0,[z0,z1,z32,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z381,z6]),(0,[z10,z1,z2,z382,z3,z5,z6]),(0,[z383,z10,z1,z2,z3,z5,z6]),(0,[z93,z10,z1,z3,z5,z46,z6]),(0,[z10,z1,z2,z3,z384,z5,z6])],[(0,[z385,z10,z1,z2,z3,z5,z6]),(0,[z40,z10,z32,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z386]),(0,[z387,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z388,z5,z6])],[(0,[z389,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z390,z6])]],
   [[(0,[z10,z1,z2,z3,z391,z5,z6]),(0,[z10,z1,z101,z2,z3,z71,z6])],[],[(0,[z392,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z2,z3,z5,z220]),(0,[z7,z1,z2,z3,z5,z175,z6]),(0,[z10,z1,z2,z3,z5,z175,z87]),(0,[z9,z10,z94,z1,z2,z5,z6]),(0,[z393,z10,z1,z3,z5,z6,z41]),(0,[z10,z1,z101,z2,z3,z5,z6]),(0,[z394,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z2,z5,z395,z6])],[(0,[z7,z1,z173,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z254,z6]),(0,[z396,z10,z1,z2,z3,z5,z6]),(0,[z250,z10,z94,z2,z3,z5,z6]),(0,[z10,z1,z397,z2,z3,z5,z6]),(0,[z30,z10,z1,z2,z3,z74,z6])],[(0,[z10,z1,z2,z3,z398,z5,z6]),(0,[z7,z244,z1,z2,z3,z5,z6]),(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z80,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z399,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z400,z6]),(0,[z10,z1,z2,z3,z5,z6,z401])],[(0,[z402,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z48])],[(0,[z7,z10,z1,z2,z403,z5,z6]),(0,[z250,z10,z1,z2,z211,z5,z6]),(0,[z10,z1,z2,z404,z3,z5,z6])],[(0,[z7,z1,z2,z141,z3,z5,z6]),(1,[z10,z1,z2,z44,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z405]),(0,[z10,z1,z2,z3,z406,z5,z6]),(0,[z70,z10,z95,z1,z2,z3,z5]),(0,[z10,z1,z3,z71,z5,z46,z6]),(0,[z10,z1,z407,z2,z3,z5,z6]),(1,[z1,z2,z3,z5,z408,z6])]],
   [[(0,[z80,z10,z1,z295,z3,z5,z6]),(1,[z10,z1,z2,z5,z6,z14]),(0,[z251,z10,z1,z2,z3,z6,z177]),(0,[z10,z1,z409,z2,z3,z5,z6])],[(0,[z10,z1,z2,z410,z3,z5,z6]),(0,[z10,z411,z1,z2,z3,z5,z6])],[(0,[z10,z1,z412,z2,z3,z5,z6]),(0,[z413,z10,z1,z2,z3,z5,z6]),(0,[z189,z10,z1,z3,z5,z46,z6]),(0,[z10,z1,z414,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z415,z5,z6])],[(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z70,z10,z1,z17,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z177]),(0,[z10,z1,z2,z416,z3,z5,z6]),(0,[z417,z10,z1,z2,z3,z5,z6])],[],[(0,[z170,z1,z2,z3,z4,z5,z6]),(0,[z418,z10,z1,z2,z3,z5,z6]),(0,[z10,z0,z266,z2,z3,z5,z6]),(0,[z419,z10,z1,z2,z3,z5,z6]),(0,[z10,z94,z1,z2,z5,z62,z6]),(0,[z10,z1,z2,z288,z3,z5,z194])],[(0,[z420,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z421,z2,z3,z5,z6]),(0,[z70,z422,z1,z2,z3,z5,z6]),(0,[z1,z2,z140,z3,z423,z5,z6])],[(0,[z10,z1,z2,z3,z424,z5,z6]),(0,[z10,z1,z2,z425,z3,z5,z6]),(0,[z51,z1,z2,z3,z5,z6,z105]),(0,[z10,z1,z2,z209,z5,z6,z65])]],
   [[(0,[z426,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z427]),(1,[z10,z1,z2,z81,z5,z6]),(0,[z40,z10,z2,z3,z5,z6,z41]),(1,[z251,z10,z1,z3,z6,z177]),(0,[z428,z10,z1,z3,z5,z6,z194]),(1,[z10,z1,z2,z3,z74,z87]),(0,[z429,z1,z2,z3,z5,z6,z87])],[(0,[z189,z10,z1,z242,z3,z5,z6]),(0,[z244,z10,z1,z2,z3,z209,z6]),(0,[z10,z1,z2,z3,z5,z6,z430]),(0,[z431,z10,z1,z2,z3,z5,z6])],[(0,[z52,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z242,z2,z3,z5,z6])],[(0,[z432,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z175,z6]),(0,[z433,z10,z1,z2,z3,z5,z6]),(0,[z10,z434,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z435,z3,z5,z6]),(0,[z9,z10,z1,z2,z288,z5,z6])],[(0,[z436,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z437,z2,z3,z5,z6]),(0,[z438,z10,z1,z2,z3,z5,z6]),(0,[z439,z10,z1,z2,z3,z5,z6])],[(0,[z309,z10,z1,z2,z39,z5,z6]),(0,[z7,z1,z2,z3,z209,z5,z6]),(0,[z7,z109,z1,z2,z3,z5,z6]),(1,[z109,z1,z2,z3,z5,z105]),(0,[z440,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z441,z2,z3,z5,z6])],[(0,[z10,z442,z1,z2,z3,z5,z6]),(0,[z443,z10,z1,z2,z3,z5,z6]),(1,[z7,z1,z2,z403,z5,z6]),(0,[z7,z94,z1,z2,z3,z5,z6]),(0,[z94,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z123,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z6,z246]),(0,[z10,z1,z2,z3,z5,z6,z41]),(0,[z251,z10,z1,z101,z3,z5,z6]),(0,[z10,z1,z2,z444,z3,z5,z6])],[(1,[z77,z1,z17,z3,z5,z6]),(0,[z7,z1,z2,z123,z3,z5,z6]),(0,[z10,z1,z2,z3,z403,z5,z6]),(0,[z1,z2,z3,z445,z4,z5,z6]),(0,[z10,z1,z2,z3,z446,z5,z6]),(0,[z155,z10,z266,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z447]),(1,[z422,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z448]),(0,[z10,z1,z2,z3,z5,z6,z449]),(0,[z9,z10,z1,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z2,z450,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z451,z6]),(0,[z10,z1,z2,z3,z5,z452,z6]),(0,[z453,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z454])],[(0,[z455,z10,z1,z2,z3,z5,z6]),(0,[z280,z7,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z105]),(0,[z10,z1,z2,z456,z3,z5,z6])],[(0,[z10,z1,z2,z457,z3,z5,z6])],[(0,[z10,z458,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z459]),(0,[z10,z91,z1,z2,z3,z5,z6]),(0,[z460,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z461,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z462]),(0,[z10,z1,z463,z2,z3,z5,z6])],[(0,[z1,z32,z2,z3,z5,z6,z105]),(0,[z10,z1,z2,z464,z3,z5,z6]),(0,[z10,z1,z2,z3,z465,z5,z6]),(0,[z10,z190,z242,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z466]),(0,[z70,z10,z1,z114,z3,z5,z6]),(0,[z467,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z62,z6,z194])],[(0,[z468,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z469,z2,z3,z5,z6]),(0,[z309,z1,z2,z3,z4,z5,z6]),(0,[z7,z10,z1,z2,z3,z4,z6]),(0,[z470,z10,z1,z2,z3,z5,z6]),(1,[z10,z266,z2,z3,z156,z6]),(0,[z471,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z472,z3,z5,z6]),(0,[z10,z1,z2,z3,z473,z5,z6]),(1,[z30,z10,z31,z1,z2,z3])],[(0,[z89,z1,z2,z3,z39,z5,z6]),(0,[z10,z1,z2,z3,z5,z474,z6]),(0,[z10,z1,z2,z3,z5,z46,z6]),(0,[z244,z10,z1,z2,z140,z5,z6])]],
   [[(0,[z10,z1,z2,z475,z3,z5,z6]),(0,[z10,z1,z2,z3,z476,z5,z6]),(0,[z10,z477,z1,z2,z3,z5,z6]),(0,[z250,z10,z1,z2,z140,z5,z6]),(0,[z10,z1,z2,z3,z5,z478,z6]),(0,[z70,z10,z1,z2,z3,z5,z46])],[(0,[z170,z68,z1,z2,z3,z5,z6]),(0,[z479,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z114,z3,z5,z46]),(0,[z10,z1,z2,z5,z395,z6,z87])],[(0,[z480,z10,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z90,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z481]),(0,[z7,z95,z1,z2,z3,z5,z6]),(0,[z7,z226,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z254,z6]),(1,[z80,z1,z2,z3,z5,z175]),(0,[z80,z1,z2,z3,z5,z175,z6])],[(0,[z10,z1,z2,z3,z482,z5,z6]),(0,[z10,z1,z2,z3,z5,z483,z6]),(0,[z10,z1,z484,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z485,z5,z6]),(0,[z10,z1,z162,z3,z5,z46,z6])],[(0,[z486,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z487,z5,z6]),(0,[z488,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z489,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z490]),(0,[z10,z1,z64,z2,z145,z5,z6]),(0,[z10,z1,z114,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z65])],[(0,[z134,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z156,z5,z6,z257]),(0,[z93,z10,z1,z2,z5,z6,z65]),(0,[z70,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z491,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z492,z6]),(0,[z10,z1,z493,z2,z3,z5,z6]),(0,[z7,z10,z104,z2,z3,z5,z6]),(0,[z7,z10,z1,z2,z3,z5,z152]),(0,[z40,z1,z2,z3,z4,z5,z6]),(1,[z1,z494,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z14,z41]),(0,[z10,z1,z2,z495,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z496]),(0,[z10,z497,z1,z2,z3,z5,z6]),(0,[z9,z10,z1,z2,z3,z5,z194])],[(0,[z1,z2,z3,z498,z4,z5,z6]),(0,[z10,z1,z2,z5,z6,z291,z47]),(0,[z10,z1,z499,z2,z3,z5,z6])]],
   [[(1,[z186,z10,z1,z2,z5,z6]),(0,[z10,z500,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z501,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z502]),(0,[z9,z10,z1,z2,z209,z5,z6])],[(0,[z10,z1,z2,z3,z5,z503,z6]),(0,[z7,z89,z1,z2,z3,z5,z6]),(0,[z1,z2,z128,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z74,z6,z87])],[(0,[z10,z1,z504,z2,z3,z5,z6]),(0,[z10,z1,z16,z101,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z96,z6]),(0,[z7,z10,z173,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z505,z5,z6]),(0,[z506,z10,z1,z2,z5,z6,z47]),(0,[z10,z1,z2,z3,z74,z5,z6]),(0,[z30,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z507,z6]),(0,[z7,z7,z1,z2,z3,z5,z6]),(0,[z7,z266,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z487,z4,z5,z6]),(0,[z1,z2,z140,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z508,z5,z6])],[(0,[z10,z32,z2,z3,z5,z96,z6]),(0,[z10,z1,z2,z3,z5,z509,z6]),(0,[z510,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z64,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z511])],[(1,[z10,z1,z2,z3,z5,z6]),(0,[z9,z10,z1,z2,z90,z5,z6]),(1,[z7,z1,z2,z3,z4,z6]),(1,[z10,z227,z2,z3,z5,z6]),(1,[z189,z10,z43,z3,z5,z6])],[(0,[z189,z10,z2,z3,z5,z96,z6])]],
   [[(0,[z10,z1,z2,z3,z512,z5,z6]),(0,[z7,z1,z2,z3,z156,z5,z6]),(0,[z7,z1,z2,z162,z3,z5,z6]),(0,[z10,z1,z227,z2,z3,z5,z6]),(0,[z80,z10,z1,z53,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z513])],[(0,[z10,z1,z2,z3,z5,z6,z514]),(0,[z10,z1,z2,z3,z515,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z47])],[(0,[z70,z10,z1,z16,z3,z5,z6]),(0,[z10,z516,z1,z2,z3,z5,z6])],[(0,[z517,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z220]),(0,[z10,z1,z2,z3,z518,z5,z6]),(0,[z10,z1,z519,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z520,z5,z6]),(0,[z521,z10,z1,z2,z3,z5,z6]),(1,[z429,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z522,z3,z5,z6]),(0,[z51,z10,z1,z17,z3,z5,z6]),(0,[z10,z1,z2,z3,z136,z5,z6]),(0,[z10,z1,z2,z3,z5,z523,z6])],[(0,[z10,z1,z2,z39,z5,z62,z6]),(0,[z332,z10,z1,z2,z43,z3,z5]),(0,[z10,z1,z2,z3,z5,z6,z524]),(0,[z10,z1,z2,z140,z3,z209,z6])],[(1,[z7,z104,z2,z3,z5,z6]),(1,[z7,z1,z2,z3,z5,z152]),(1,[z10,z1,z2,z141,z5,z6]),(0,[z7,z10,z1,z2,z3,z254,z6]),(0,[z525,z10,z1,z2,z3,z5,z6]),(0,[z189,z10,z1,z43,z3,z5,z6]),(0,[z245,z266,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z526,z3,z5,z6])],[(0,[z527,z10,z1,z2,z3,z5,z6]),(0,[z7,z31,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z528]),(0,[z10,z94,z1,z2,z5,z6,z65]),(0,[z529,z10,z1,z2,z3,z5,z6])]],
   [[(0,[z530,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z10,z1,z2,z531,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z247]),(1,[z10,z1,z2,z5,z6,z208]),(1,[z10,z2,z3,z5,z222,z6])],[(0,[z7,z1,z2,z3,z39,z5,z6]),(0,[z10,z1,z2,z532,z3,z5,z6]),(0,[z10,z1,z2,z533,z3,z5,z6])],[(0,[z10,z1,z2,z534,z3,z5,z6]),(0,[z10,z1,z2,z3,z535,z5,z6]),(0,[z10,z1,z2,z536,z3,z5,z6]),(0,[z244,z9,z10,z1,z2,z5,z6]),(0,[z10,z1,z2,z3,z5,z222,z6])],[(1,[z7,z173,z2,z3,z5,z6]),(0,[z10,z190,z1,z2,z3,z5,z6]),(0,[z10,z242,z2,z43,z3,z5,z6]),(0,[z10,z1,z2,z197,z3,z5,z6]),(0,[z155,z10,z2,z3,z5,z96,z6]),(0,[z10,z1,z2,z71,z5,z6,z208])],[(0,[z10,z1,z17,z3,z5,z46,z6]),(0,[z10,z1,z2,z3,z537,z5,z6]),(0,[z538,z10,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z87]),(0,[z1,z242,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z96,z6])],[(0,[z10,z1,z2,z539,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z5,z6]),(1,[z155,z10,z2,z3,z6,z21]),(0,[z10,z1,z2,z3,z5,z6,z540]),(1,[z10,z2,z3,z5,z6,z203])],[(1,[z309,z1,z2,z90,z5,z6]),(0,[z226,z10,z1,z2,z3,z4,z6]),(0,[z10,z2,z123,z3,z211,z5,z6]),(1,[z541,z10,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z542]),(1,[z133,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z543,z5,z6]),(0,[z544,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z203])]],
   [[(0,[z10,z0,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z545,z5,z6]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z546,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z547]),(0,[z10,z1,z2,z3,z5,z6,z246]),(0,[z10,z1,z548,z2,z3,z5,z6])],[(0,[z10,z549,z1,z2,z3,z5,z6]),(1,[z332,z10,z1,z2,z3,z5]),(0,[z550,z10,z1,z2,z3,z5,z6]),(0,[z10,z551,z1,z2,z3,z5,z6]),(0,[z10,z422,z1,z2,z3,z5,z6]),(1,[z10,z2,z3,z5,z6,z148]),(0,[z10,z1,z2,z288,z3,z5,z6])],[(0,[z552,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z553,z5,z6])],[(0,[z10,z1,z8,z2,z3,z5,z6]),(0,[z10,z1,z2,z554,z3,z5,z6]),(0,[z10,z1,z2,z3,z555,z5,z6]),(0,[z10,z1,z2,z3,z556,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z148]),(0,[z557,z10,z1,z2,z3,z5,z6])],[(0,[z7,z30,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z326]),(0,[z10,z1,z2,z3,z5,z6,z558]),(0,[z10,z94,z1,z2,z211,z5,z6]),(0,[z10,z1,z2,z3,z5,z559,z6])],[(1,[z68,z0,z2,z3,z5,z6]),(0,[z77,z10,z1,z17,z3,z5,z6]),(0,[z10,z1,z2,z560,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z561]),(0,[z562,z10,z1,z2,z3,z5,z6]),(0,[z10,z266,z1,z2,z3,z156,z6]),(0,[z10,z1,z2,z3,z5,z563,z6]),(0,[z564,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z565,z5,z6])],[(0,[z1,z2,z3,z209,z4,z5,z6]),(0,[z10,z1,z2,z566,z3,z5,z6]),(0,[z10,z1,z2,z311,z3,z5,z6]),(0,[z567,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z568]),(0,[z10,z1,z32,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z62,z6]),(0,[z10,z266,z1,z2,z3,z6,z21]),(0,[z10,z284,z1,z2,z3,z5,z6]),(0,[z10,z1,z569,z2,z3,z5,z6]),(0,[z244,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z570,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z2,z3,z571,z5,z6]),(0,[z109,z10,z1,z2,z3,z5,z175]),(0,[z250,z10,z1,z2,z3,z5,z6]),(0,[z354,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z2,z305,z5,z6])],[(1,[z572,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z573,z5,z6])],[(0,[z1,z64,z2,z3,z4,z5,z6]),(0,[z10,z574,z1,z2,z3,z5,z6])],[(0,[z10,z1,z575,z2,z3,z5,z6]),(0,[z576,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z445,z5,z6]),(0,[z10,z1,z2,z43,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z577]),(1,[z10,z1,z3,z5,z6,z193])],[(0,[z10,z1,z2,z3,z5,z6,z578]),(0,[z579,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z580]),(0,[z93,z10,z1,z2,z140,z5,z6])],[(0,[z9,z10,z1,z2,z39,z5,z6]),(0,[z7,z93,z1,z2,z3,z5,z6]),(0,[z581,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z87])],[(0,[z51,z10,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z142]),(0,[z10,z1,z582,z2,z3,z5,z6]),(1,[z428,z10,z1,z3,z5,z6])],[(0,[z283,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z583]),(0,[z7,z1,z101,z2,z3,z5,z6]),(0,[z10,z584,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z585,z3,z5,z6]),(1,[z1,z2,z3,z423,z5,z6])]],
   [[(0,[z10,z1,z586,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z175,z6,z105]),(0,[z10,z1,z494,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z587,z5,z6]),(0,[z10,z1,z2,z3,z71,z5,z6]),(0,[z10,z1,z2,z102,z3,z5,z6])],[(0,[z12,z10,z1,z2,z3,z5,z6]),(0,[z52,z1,z2,z3,z4,z5,z6]),(0,[z588,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z305,z74,z5,z6])],[(0,[z1,z2,z90,z3,z39,z5,z6]),(0,[z10,z589,z1,z2,z3,z5,z6]),(0,[z10,z1,z3,z71,z5,z6,z177]),(1,[z506,z10,z1,z2,z5,z6]),(0,[z590,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z591])],[(0,[z592,z10,z1,z2,z3,z5,z6]),(1,[z285,z10,z1,z2,z5,z6])],[(0,[z10,z593,z1,z2,z3,z5,z6]),(0,[z10,z1,z365,z2,z3,z5,z6]),(0,[z10,z594,z1,z2,z3,z5,z6]),(1,[z117,z10,z2,z3,z5,z6])],[(0,[z7,z170,z1,z2,z3,z5,z6]),(0,[z226,z10,z1,z2,z3,z254,z6]),(0,[z9,z1,z2,z3,z4,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z595]),(0,[z596,z10,z1,z2,z3,z5,z6]),(0,[z597,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z257]),(0,[z10,z1,z2,z3,z598,z5,z6])]],
   [[(0,[z10,z10,z1,z2,z3,z5,z6]),(0,[z599,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z600]),(0,[z264,z7,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z601,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z602]),(0,[z10,z1,z2,z3,z5,z6,z21]),(0,[z10,z603,z1,z2,z3,z5,z6])],[(0,[z7,z10,z1,z8,z3,z5,z6]),(1,[z10,z1,z2,z5,z6,z314]),(0,[z604,z31,z1,z2,z3,z5,z6])],[(0,[z572,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z605,z5,z6]),(0,[z51,z10,z1,z16,z3,z5,z6]),(0,[z7,z189,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z606,z6]),(0,[z10,z1,z2,z607,z3,z5,z6]),(0,[z10,z94,z1,z64,z2,z5,z6])],[(0,[z309,z1,z2,z90,z3,z5,z6]),(0,[z10,z1,z2,z90,z5,z62,z6]),(0,[z218,z10,z1,z2,z3,z5,z6]),(0,[z40,z10,z95,z2,z3,z5,z6])],[(0,[z68,z1,z2,z3,z5,z6,z105]),(0,[z282,z7,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z608,z5,z6]),(0,[z10,z94,z1,z2,z140,z5,z6]),(0,[z10,z1,z2,z3,z5,z609,z6])],[(0,[z77,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z39,z5,z6,z65]),(0,[z7,z1,z242,z2,z3,z5,z6]),(0,[z1,z2,z43,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z6]),(0,[z109,z10,z1,z2,z3,z5,z105]),(0,[z10,z1,z2,z3,z5,z610,z6]),(0,[z611,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z291])]],
   [[(0,[z10,z1,z612,z2,z3,z5,z6]),(0,[z10,z1,z64,z2,z162,z5,z6]),(0,[z10,z1,z2,z3,z613,z5,z6])],[],[(0,[z10,z1,z614,z2,z3,z5,z6]),(1,[z10,z1,z2,z171,z5,z6]),(0,[z251,z10,z1,z3,z5,z6,z177]),(0,[z10,z1,z114,z2,z3,z5,z46])],[(0,[z7,z51,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z41]),(0,[z10,z94,z2,z123,z3,z5,z6]),(0,[z615,z10,z1,z2,z3,z5,z6])],[(0,[z309,z89,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z403,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z616])],[(0,[z617,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z618,z5,z6]),(0,[z10,z619,z1,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z5,z6,z105]),(0,[z109,z1,z2,z3,z5,z6,z105]),(0,[z10,z1,z2,z3,z5,z620,z6]),(0,[z10,z1,z2,z140,z5,z6,z194])],[(0,[z10,z1,z2,z3,z621,z5,z6]),(0,[z10,z1,z3,z5,z6,z490,z41]),(0,[z10,z1,z2,z3,z622,z5,z6])]],
   [[(0,[z345,z10,z1,z2,z3,z5,z6]),(0,[z488,z7,z1,z2,z3,z5,z6]),(0,[z80,z10,z1,z2,z3,z5,z175]),(0,[z10,z623,z1,z2,z3,z5,z6]),(0,[z624,z10,z1,z2,z3,z5,z6]),(0,[z625,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z626]),(0,[z86,z10,z1,z2,z3,z5,z6])],[(0,[z10,z627,z1,z2,z3,z5,z6]),(1,[z7,z1,z8,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z628]),(0,[z572,z1,z2,z3,z5,z6,z65])],[(0,[z7,z251,z1,z2,z3,z5,z6]),(0,[z30,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z177]),(0,[z10,z629,z1,z2,z3,z5,z6]),(1,[z259,z10,z2,z3,z5,z6]),(0,[z431,z10,z1,z3,z5,z6,z87])],[(0,[z10,z1,z2,z3,z498,z5,z6]),(0,[z10,z320,z1,z2,z3,z5,z6]),(0,[z630,z10,z1,z2,z3,z5,z6]),(0,[z10,z631,z1,z2,z3,z5,z6])],[(0,[z77,z10,z1,z16,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z46,z6]),(0,[z10,z632,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z156,z4,z5,z6]),(0,[z70,z10,z190,z1,z3,z5,z6]),(0,[z245,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z633,z5,z6])],[(0,[z10,z1,z2,z634,z3,z5,z6]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z324,z7,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z635,z5,z6]),(0,[z506,z10,z1,z2,z3,z5,z6]),(0,[z30,z10,z31,z1,z2,z3,z5]),(1,[z604,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z194])],[(0,[z10,z1,z2,z3,z636,z5,z6]),(0,[z10,z95,z1,z114,z2,z3,z5])]],
   [[(0,[z637,z10,z1,z2,z3,z5,z6]),(1,[z93,z10,z1,z145,z5,z6]),(0,[z70,z93,z10,z1,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6,z638]),(0,[z7,z1,z114,z2,z3,z5,z6]),(1,[z10,z1,z295,z3,z5,z6]),(0,[z10,z1,z64,z2,z5,z62,z6]),(1,[z10,z1,z2,z311,z5,z6]),(0,[z639,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z640,z2,z3,z5,z6]),(0,[z10,z641,z1,z2,z3,z5,z6]),(0,[z642,z10,z1,z2,z3,z5,z6]),(0,[z70,z10,z1,z162,z3,z5,z6]),(0,[z10,z1,z2,z3,z643,z5,z6]),(0,[z1,z2,z3,z5,z408,z6,z87])],[(0,[z10,z644,z1,z2,z3,z5,z6]),(0,[z10,z1,z173,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z645]),(0,[z10,z1,z2,z3,z646,z5,z6]),(0,[z10,z1,z2,z647,z3,z5,z6])],[(0,[z10,z1,z2,z3,z211,z5,z6]),(0,[z10,z1,z2,z648,z3,z5,z6]),(0,[z93,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z649,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z408,z6])],[(0,[z40,z189,z10,z2,z3,z5,z6]),(0,[z650,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z651,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z652,z5,z6]),(0,[z10,z653,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z654,z5,z6]),(0,[z10,z1,z2,z655,z3,z5,z6])],[(0,[z656,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z16,z3,z5,z6,z177]),(0,[z95,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z657,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z658])]],
   [[(0,[z10,z1,z2,z3,z659,z5,z6]),(0,[z7,z1,z2,z3,z74,z5,z6]),(0,[z10,z2,z3,z156,z5,z6,z21]),(0,[z10,z1,z2,z3,z660,z5,z6]),(0,[z10,z1,z3,z5,z6,z346,z194])],[(0,[z7,z10,z1,z2,z3,z5,z220]),(0,[z1,z2,z3,z4,z5,z6,z459]),(1,[z10,z1,z3,z5,z6,z490]),(0,[z285,z10,z1,z2,z5,z6,z41]),(0,[z10,z1,z2,z3,z423,z5,z6]),(0,[z429,z10,z1,z2,z3,z5,z6])],[(0,[z184,z10,z1,z2,z3,z5,z6]),(0,[z661,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z662]),(0,[z7,z1,z64,z2,z3,z5,z6]),(0,[z10,z1,z64,z162,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z663])],[(0,[z10,z1,z2,z3,z5,z664,z6]),(0,[z40,z218,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z665,z3,z5,z6]),(0,[z244,z10,z1,z2,z3,z6,z65]),(0,[z428,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z666,z3,z5,z6]),(0,[z10,z1,z2,z17,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z667]),(1,[z393,z10,z1,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z668,z6]),(0,[z10,z1,z101,z2,z3,z6,z177])],[(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z251,z70,z10,z1,z3,z5,z6])],[(0,[z669,z10,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z6,z47]),(0,[z70,z189,z10,z1,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z670]),(0,[z10,z1,z2,z3,z671,z5,z6]),(0,[z10,z1,z2,z672,z3,z5,z6]),(0,[z10,z1,z2,z673,z3,z5,z6])],[(0,[z10,z1,z2,z674,z3,z5,z6]),(1,[z7,z1,z97,z3,z5,z6]),(0,[z1,z2,z288,z3,z4,z5,z6]),(0,[z80,z10,z1,z2,z3,z5,z105]),(0,[z10,z1,z2,z3,z5,z6,z675]),(0,[z10,z1,z2,z74,z5,z6,z314])]],
   [[(0,[z10,z1,z2,z3,z5,z676,z6])],[(0,[z10,z1,z2,z3,z5,z254,z6]),(0,[z189,z10,z1,z2,z3,z5,z6]),(0,[z40,z10,z2,z123,z3,z5,z6]),(0,[z155,z40,z10,z2,z3,z5,z6]),(0,[z40,z10,z1,z114,z2,z3,z5])],[(0,[z10,z1,z2,z677,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z678,z6]),(0,[z10,z679,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z680,z5,z6]),(0,[z393,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z65,z194]),(1,[z431,z10,z1,z3,z5,z6])],[(0,[z77,z1,z2,z17,z3,z5,z6]),(0,[z217,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z681,z3,z5,z6]),(0,[z10,z1,z682,z2,z3,z5,z6]),(0,[z10,z95,z2,z3,z5,z96,z6])],[(0,[z68,z0,z1,z2,z3,z5,z6]),(0,[z683,z10,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z152,z6]),(0,[z10,z1,z2,z3,z5,z87,z105]),(0,[z684,z10,z1,z2,z3,z5,z6]),(0,[z604,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z685,z3,z5,z6]),(0,[z250,z10,z1,z2,z123,z5,z6]),(0,[z10,z1,z686,z2,z3,z5,z6]),(0,[z10,z1,z2,z288,z5,z62,z6])],[(0,[z10,z1,z2,z90,z5,z6,z65]),(0,[z244,z1,z2,z3,z4,z5,z6]),(0,[z80,z10,z1,z2,z136,z5,z6]),(0,[z10,z1,z687,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z688,z5,z6]),(0,[z689,z10,z1,z2,z3,z5,z6]),(0,[z70,z40,z10,z1,z2,z3,z5]),(0,[z10,z690,z1,z2,z3,z5,z6])],[(0,[z10,z1,z17,z3,z5,z6,z177]),(0,[z250,z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z691]),(0,[z541,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z3,z5,z6,z346])]],
   [[(0,[z7,z190,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z44,z3,z5,z6]),(0,[z10,z1,z2,z197,z43,z3,z5]),(0,[z541,z10,z2,z3,z5,z6,z47]),(0,[z10,z1,z2,z692,z3,z5,z6])],[(0,[z10,z1,z2,z3,z241,z5,z6]),(1,[z7,z1,z2,z3,z5,z220]),(0,[z693,z10,z1,z2,z3,z5,z6]),(0,[z10,z694,z1,z2,z3,z5,z6]),(0,[z695,z10,z1,z2,z3,z5,z6])],[(0,[z10,z1,z696,z2,z3,z5,z6]),(0,[z9,z250,z10,z1,z2,z5,z6]),(0,[z266,z1,z494,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z395,z6])],[(0,[z10,z1,z2,z3,z5,z6,z697]),(0,[z89,z10,z1,z2,z3,z5,z6]),(0,[z10,z242,z2,z3,z5,z96,z6]),(0,[z93,z10,z1,z3,z145,z5,z6])],[(0,[z10,z1,z2,z3,z698,z5,z6]),(0,[z10,z1,z699,z2,z3,z5,z6]),(0,[z250,z10,z2,z3,z211,z5,z6]),(0,[z700,z10,z1,z2,z3,z5,z6]),(0,[z10,z95,z1,z2,z3,z5,z41]),(0,[z701,z10,z1,z2,z3,z5,z6]),(0,[z251,z10,z1,z2,z3,z71,z6])],[(0,[z7,z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z17,z3,z5,z6,z105]),(0,[z702,z10,z1,z2,z3,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z10,z31,z1,z2,z3,z5,z175]),(0,[z10,z1,z2,z3,z5,z6,z703]),(0,[z155,z10,z1,z2,z3,z5,z6]),(1,[z10,z1,z2,z140,z209,z6])],[(0,[z7,z1,z2,z288,z3,z5,z6]),(1,[z10,z1,z64,z162,z5,z6]),(0,[z251,z10,z1,z2,z3,z5,z6]),(0,[z259,z10,z2,z3,z5,z6,z87])],[(0,[z10,z1,z2,z3,z704,z5,z6]),(1,[z10,z1,z2,z403,z5,z6]),(0,[z10,z1,z2,z3,z5,z6,z705]),(0,[z10,z1,z2,z3,z5,z706,z6]),(1,[z10,z1,z2,z288,z5,z62])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z10,z1,z707,z2,z3,z6]),(0,[z10,z1,z708,z3,z5,z6]),(0,[z428,z1,z3,z4,z5,z6]),(0,[z332,z189,z10,z2,z3,z5]),(0,[z10,z1,z3,z5,z6,z709]),(0,[z155,z20,z2,z3,z6,z21])],[(0,[z7,z94,z2,z123,z5,z6]),(0,[z710,z1,z2,z3,z5,z6]),(0,[z251,z10,z1,z3,z6,z711]),(0,[z259,z429,z2,z3,z5,z6])],[(0,[z712,z10,z1,z2,z5,z6]),(0,[z189,z10,z197,z43,z3,z5]),(0,[z117,z10,z3,z5,z6,z346])],[(0,[z10,z104,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z6,z713]),(0,[z10,z1,z2,z714,z5,z6]),(0,[z7,z104,z2,z3,z4,z6]),(0,[z7,z1,z2,z3,z4,z152]),(0,[z10,z1,z2,z3,z5,z152]),(0,[z10,z1,z2,z3,z715,z6]),(0,[z10,z2,z3,z716,z5,z6]),(0,[z717,z10,z2,z3,z5,z6]),(0,[z506,z10,z2,z5,z6,z148]),(0,[z718,z1,z2,z3,z5,z6])],[(0,[z418,z1,z2,z3,z4,z6]),(0,[z7,z1,z2,z719,z5,z6]),(0,[z604,z1,z2,z3,z5,z6])],[(0,[z10,z1,z720,z3,z5,z6]),(0,[z60,z1,z2,z90,z5,z6]),(0,[z9,z10,z2,z5,z203,z194])],[(0,[z10,z1,z2,z3,z5,z721]),(0,[z10,z1,z2,z5,z6,z722]),(0,[z7,z1,z723,z3,z5,z6]),(0,[z7,z1,z2,z3,z358,z6])],[(0,[z10,z1,z2,z5,z6,z724]),(0,[z7,z1,z2,z3,z342,z6]),(0,[z725,z10,z1,z2,z5,z6]),(0,[z726,z10,z1,z2,z5,z6]),(0,[z93,z10,z1,z145,z5,z6])]],
   [[(0,[z10,z173,z2,z3,z5,z6]),(0,[z7,z173,z2,z3,z4,z6]),(0,[z7,z1,z8,z141,z5,z6]),(0,[z120,z1,z97,z3,z5,z6]),(0,[z727,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z311,z5,z6]),(0,[z10,z1,z101,z3,z71,z6])],[(0,[z7,z1,z2,z3,z5,z6]),(0,[z234,z1,z17,z3,z5,z6]),(0,[z7,z227,z2,z3,z5,z6]),(0,[z728,z1,z2,z3,z5,z6]),(0,[z10,z2,z3,z5,z729,z6])],[(0,[z10,z730,z2,z3,z5,z6]),(0,[z1,z2,z128,z39,z5,z6]),(0,[z393,z10,z3,z5,z96,z6]),(0,[z10,z731,z2,z3,z5,z6])],[(0,[z309,z1,z2,z732,z5,z6]),(0,[z7,z104,z2,z3,z5,z152]),(0,[z10,z1,z2,z141,z5,z152])],[(0,[z10,z1,z733,z3,z5,z6]),(0,[z7,z135,z2,z3,z5,z6]),(0,[z109,z1,z2,z3,z5,z734]),(0,[z10,z735,z2,z3,z5,z6])],[(0,[z86,z1,z2,z4,z5,z6])],[(0,[z736,z10,z1,z2,z5,z6])],[(0,[z10,z1,z2,z737,z5,z6]),(0,[z1,z97,z3,z5,z6,z220]),(0,[z10,z1,z2,z738,z5,z6])]],
   [[(0,[z7,z1,z2,z3,z5,z739]),(0,[z7,z173,z2,z3,z5,z152]),(0,[z10,z173,z2,z141,z5,z6]),(0,[z10,z104,z97,z3,z5,z6]),(0,[z10,z1,z97,z3,z5,z152]),(0,[z30,z31,z1,z2,z3,z4]),(0,[z227,z2,z3,z4,z5,z6]),(0,[z10,z1,z3,z5,z6,z490]),(0,[z10,z1,z64,z5,z6,z449]),(0,[z10,z1,z3,z71,z6,z711]),(0,[z740,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z741,z6]),(0,[z7,z1,z2,z141,z5,z6]),(0,[z332,z742,z1,z2,z3,z5]),(0,[z10,z2,z3,z5,z96,z547]),(0,[z1,z2,z3,z5,z6,z743])],[(0,[z10,z1,z53,z81,z5,z6]),(0,[z1,z2,z3,z5,z744,z6])],[(0,[z745,z32,z2,z3,z5,z6]),(0,[z10,z266,z2,z3,z223,z6]),(0,[z10,z746,z2,z3,z5,z6]),(0,[z7,z40,z2,z3,z5,z41]),(0,[z7,z1,z2,z3,z373,z6]),(0,[z7,z2,z3,z5,z222,z6]),(0,[z7,z1,z2,z3,z747,z6]),(0,[z320,z2,z3,z498,z5,z6])],[(0,[z51,z1,z2,z3,z5,z220]),(0,[z10,z1,z748,z3,z5,z6]),(0,[z749,z1,z2,z3,z5,z6]),(0,[z10,z1,z5,z395,z6,z193])],[(0,[z10,z1,z2,z750,z5,z6]),(0,[z1,z53,z17,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z751]),(0,[z10,z752,z2,z3,z5,z6]),(0,[z7,z190,z242,z3,z5,z6]),(0,[z10,z173,z97,z3,z5,z6]),(0,[z10,z1,z2,z753,z5,z6]),(0,[z10,z2,z3,z5,z96,z558])],[(0,[z218,z1,z2,z3,z5,z6]),(0,[z7,z1,z97,z3,z5,z6]),(0,[z7,z1,z2,z754,z5,z6]),(0,[z10,z1,z2,z755,z5,z6]),(0,[z250,z10,z2,z406,z5,z6]),(0,[z354,z1,z101,z3,z71,z6]),(0,[z1,z2,z3,z5,z6,z756]),(0,[z757,z1,z2,z3,z5,z6])],[(0,[z758,z10,z2,z3,z5,z6]),(0,[z10,z759,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z760]),(0,[z282,z1,z2,z403,z5,z6]),(0,[z10,z2,z123,z716,z5,z6])]],
   [[(0,[z1,z2,z3,z747,z254,z6]),(0,[z189,z10,z79,z3,z5,z6]),(0,[z10,z1,z3,z5,z6,z761])],[(0,[z10,z1,z762,z3,z5,z6]),(0,[z218,z135,z2,z3,z5,z6]),(0,[z431,z429,z1,z3,z5,z6])],[(0,[z1,z2,z141,z39,z5,z6]),(0,[z7,z1,z2,z763,z5,z6]),(0,[z9,z1,z2,z4,z5,z194]),(0,[z1,z3,z4,z5,z6,z764]),(0,[z189,z10,z249,z3,z5,z6])],[(0,[z10,z1,z2,z765,z5,z6]),(0,[z10,z766,z2,z3,z5,z6]),(0,[z7,z104,z2,z3,z254,z6]),(0,[z7,z1,z2,z3,z254,z152]),(0,[z1,z2,z4,z5,z6,z257]),(0,[z767,z10,z1,z3,z5,z6]),(0,[z10,z1,z768,z2,z5,z6]),(0,[z393,z10,z95,z1,z3,z5]),(0,[z1,z2,z3,z769,z5,z6]),(0,[z1,z2,z770,z3,z5,z6]),(0,[z541,z10,z3,z5,z46,z6])],[(0,[z10,z771,z2,z3,z5,z6]),(0,[z10,z1,z2,z772,z5,z6]),(0,[z10,z94,z2,z649,z5,z6]),(1,[z10,z2,z3,z5,z773]),(0,[z10,z1,z64,z774,z5,z6])],[(0,[z10,z1,z2,z775,z5,z6]),(0,[z218,z0,z2,z3,z5,z6]),(0,[z318,z10,z1,z3,z6,z177]),(0,[z7,z1,z2,z3,z5,z776]),(0,[z7,z1,z2,z777,z5,z6]),(0,[z778,z1,z2,z3,z5,z6]),(0,[z779,z10,z1,z2,z5,z6]),(0,[z604,z1,z2,z780,z5,z6])],[(0,[z7,z1,z97,z141,z5,z6]),(0,[z1,z2,z403,z4,z5,z6]),(0,[z781,z1,z2,z3,z5,z6]),(0,[z10,z266,z2,z3,z6,z782]),(0,[z259,z10,z3,z5,z6,z193])],[(0,[z1,z2,z3,z5,z6,z783]),(0,[z155,z10,z2,z3,z327,z6]),(0,[z10,z1,z2,z5,z6,z784])]],
   [[(0,[z7,z1,z2,z785,z5,z6]),(0,[z7,z173,z2,z3,z254,z6]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z10,z1,z5,z6,z14,z490])],[(0,[z10,z1,z787,z3,z5,z6]),(0,[z1,z2,z788,z3,z5,z6]),(0,[z10,z1,z2,z74,z395,z87])],[(0,[z7,z1,z2,z3,z608,z6]),(0,[z7,z789,z2,z3,z5,z6]),(0,[z790,z1,z2,z3,z5,z6]),(0,[z10,z2,z3,z6,z782,z21]),(0,[z40,z10,z249,z2,z3,z5]),(0,[z1,z2,z3,z5,z791,z6])],[(0,[z7,z1,z2,z3,z659,z6]),(0,[z234,z1,z2,z3,z5,z6]),(0,[z7,z1,z2,z305,z5,z6]),(0,[z10,z1,z2,z5,z6,z257]),(0,[z792,z1,z2,z3,z5,z6])],[(0,[z120,z1,z17,z3,z5,z6]),(0,[z793,z10,z1,z2,z5,z6]),(0,[z60,z1,z2,z39,z5,z6]),(0,[z1,z2,z3,z5,z747,z6]),(0,[z332,z10,z1,z2,z44,z5]),(0,[z10,z1,z794,z3,z5,z6]),(0,[z70,z234,z1,z3,z5,z47]),(0,[z10,z795,z2,z3,z5,z6]),(0,[z30,z604,z31,z1,z2,z3])],[(0,[z7,z1,z2,z44,z5,z6]),(0,[z332,z10,z190,z1,z3,z5]),(0,[z10,z1,z64,z162,z5,z6]),(0,[z10,z1,z2,z796,z5,z6]),(0,[z9,z428,z10,z1,z5,z6])],[(0,[z797,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z288,z5,z62]),(0,[z1,z2,z3,z74,z408,z87])],[(0,[z7,z1,z2,z3,z489,z6]),(0,[z244,z10,z1,z2,z6,z798])]],
   [[(0,[z10,z2,z3,z5,z799,z6]),(0,[z9,z117,z10,z2,z5,z6])],[(0,[z1,z2,z3,z4,z6,z600]),(0,[z428,z10,z1,z5,z62,z6]),(0,[z30,z31,z133,z1,z2,z3])],[(0,[z10,z800,z2,z3,z5,z6]),(0,[z429,z1,z2,z3,z5,z175])],[(0,[z7,z1,z801,z3,z5,z6]),(0,[z10,z1,z2,z3,z802,z6]),(0,[z10,z1,z2,z803,z5,z6])],[(1,[z1,z97,z3,z5,z220]),(0,[z40,z10,z2,z3,z5,z773]),(0,[z541,z10,z114,z2,z3,z5]),(0,[z804,z1,z2,z3,z5,z6]),(0,[z9,z10,z1,z2,z5,z805]),(0,[z10,z1,z2,z806,z5,z6])],[(0,[z10,z1,z807,z3,z5,z6]),(0,[z1,z295,z3,z4,z5,z6]),(0,[z10,z1,z3,z808,z5,z6]),(0,[z10,z2,z171,z5,z96,z6]),(0,[z40,z10,z2,z3,z5,z41]),(0,[z40,z393,z10,z2,z3,z5]),(0,[z10,z809,z2,z3,z5,z6])],[(0,[z10,z1,z810,z3,z5,z6]),(0,[z7,z104,z2,z403,z5,z6]),(0,[z7,z1,z2,z3,z252,z6]),(0,[z7,z1,z2,z3,z74,z87]),(0,[z7,z1,z2,z81,z5,z6]),(0,[z10,z1,z811,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z48]),(0,[z1,z2,z3,z5,z6,z812]),(0,[z813,z10,z1,z3,z5,z6]),(0,[z1,z2,z3,z814,z5,z6]),(0,[z70,z10,z1,z5,z291,z47])]],
   [[(0,[z234,z1,z16,z3,z5,z6]),(0,[z80,z1,z2,z3,z5,z734]),(0,[z117,z10,z2,z5,z62,z6])],[(0,[z20,z0,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z454]),(0,[z1,z815,z2,z3,z5,z6]),(0,[z40,z218,z2,z3,z5,z41]),(0,[z816,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z5,z6,z817]),(0,[z10,z1,z2,z818,z5,z6]),(0,[z10,z1,z3,z5,z6,z819]),(0,[z10,z3,z5,z6,z203,z346])],[(0,[z0,z173,z2,z3,z5,z6]),(0,[z354,z1,z17,z3,z5,z6]),(0,[z51,z1,z820,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z821]),(0,[z70,z10,z3,z5,z148,z47])],[(0,[z10,z1,z2,z822,z5,z6]),(0,[z10,z1,z2,z3,z823,z6]),(0,[z80,z1,z2,z3,z5,z341]),(0,[z10,z824,z2,z3,z5,z6]),(0,[z7,z1,z2,z5,z6,z314]),(0,[z70,z40,z189,z10,z3,z5])],[(0,[z7,z431,z1,z3,z5,z6]),(1,[z10,z2,z3,z6,z782]),(0,[z10,z95,z2,z585,z3,z5]),(0,[z1,z2,z3,z5,z6,z825]),(0,[z251,z1,z3,z6,z247,z177])],[(0,[z7,z1,z8,z3,z4,z6]),(0,[z10,z1,z826,z3,z5,z6]),(0,[z827,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z828,z6]),(0,[z1,z2,z3,z5,z6,z829])],[(0,[z217,z1,z2,z5,z6,z56]),(0,[z80,z1,z2,z136,z5,z175]),(0,[z10,z1,z2,z830,z5,z6]),(0,[z10,z1,z831,z2,z5,z6])]],
   [[(0,[z9,z10,z1,z2,z5,z481]),(0,[z10,z94,z2,z716,z5,z6]),(0,[z10,z1,z2,z3,z5,z773])],[(0,[z10,z107,z2,z3,z5,z96]),(0,[z10,z1,z2,z3,z5,z832]),(0,[z10,z1,z833,z3,z5,z6]),(0,[z244,z1,z2,z4,z6,z65]),(0,[z834,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z805])],[(0,[z10,z1,z2,z3,z5,z835]),(0,[z1,z2,z732,z3,z5,z6]),(0,[z93,z10,z1,z774,z5,z6])],[(0,[z155,z10,z2,z3,z6,z782]),(0,[z10,z2,z3,z5,z773,z41]),(0,[z10,z1,z3,z74,z193,z87])],[(0,[z10,z1,z2,z5,z6,z836]),(0,[z10,z1,z2,z837,z5,z6]),(0,[z7,z186,z1,z2,z5,z6]),(0,[z838,z1,z2,z3,z5,z6]),(0,[z251,z120,z1,z3,z6,z177]),(0,[z244,z1,z2,z6,z48,z65])],[(0,[z89,z1,z2,z39,z5,z6]),(0,[z7,z1,z2,z171,z5,z6]),(0,[z10,z1,z2,z839,z5,z6]),(0,[z10,z1,z2,z140,z553,z6]),(0,[z840,z10,z1,z3,z5,z6])],[(0,[z120,z1,z2,z3,z5,z6]),(0,[z7,z1,z8,z3,z5,z152]),(0,[z7,z1,z2,z403,z5,z220]),(0,[z1,z2,z3,z5,z6,z841]),(0,[z842,z10,z1,z2,z5,z6])],[(0,[z7,z93,z1,z145,z5,z6]),(0,[z843,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z844,z6]),(0,[z845,z1,z2,z3,z5,z6])]],
   [[(0,[z250,z10,z2,z211,z5,z6]),(0,[z10,z1,z846,z3,z5,z6]),(0,[z10,z1,z847,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z848])],[(0,[z280,z104,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z849]),(0,[z429,z1,z2,z3,z5,z105]),(0,[z10,z1,z2,z388,z6,z65]),(1,[z10,z1,z3,z5,z761])],[(0,[z1,z2,z3,z4,z5,z152]),(0,[z7,z393,z1,z3,z5,z6]),(0,[z2,z3,z4,z5,z850,z6]),(0,[z40,z393,z10,z3,z5,z41]),(0,[z10,z851,z2,z3,z5,z6])],[(0,[z10,z1,z2,z136,z5,z6]),(0,[z7,z173,z8,z3,z5,z6]),(0,[z10,z227,z2,z136,z5,z6]),(0,[z10,z190,z852,z3,z5,z6]),(0,[z10,z2,z853,z3,z5,z6]),(0,[z70,z10,z1,z3,z5,z47]),(0,[z10,z1,z854,z3,z5,z6])],[(0,[z354,z1,z8,z3,z5,z6]),(0,[z855,z10,z1,z3,z5,z6]),(0,[z10,z1,z856,z3,z5,z6])],[(0,[z1,z32,z2,z3,z5,z220]),(0,[z40,z10,z2,z3,z5,z638]),(0,[z10,z857,z2,z3,z5,z6]),(0,[z1,z2,z141,z403,z5,z6])],[(0,[z858,z10,z1,z3,z5,z6]),(0,[z10,z135,z2,z136,z5,z6])],[(0,[z7,z1,z859,z3,z5,z6]),(0,[z1,z2,z3,z106,z4,z6]),(0,[z10,z2,z3,z156,z6,z782]),(0,[z10,z1,z114,z3,z5,z761])]],
   [[(0,[z7,z1,z2,z3,z5,z860]),(0,[z264,z1,z2,z3,z5,z220]),(0,[z190,z242,z3,z4,z5,z6]),(0,[z10,z1,z2,z861,z5,z6]),(0,[z10,z1,z2,z862,z5,z6]),(0,[z1,z2,z3,z5,z6,z863]),(1,[z10,z1,z3,z6,z711])],[(0,[z10,z94,z2,z5,z6,z675])],[(0,[z170,z32,z2,z3,z5,z6]),(0,[z1,z114,z3,z4,z5,z46]),(0,[z10,z1,z864,z3,z5,z6]),(0,[z10,z1,z865,z3,z5,z6]),(0,[z93,z10,z1,z520,z5,z6])],[(0,[z120,z1,z16,z3,z5,z6]),(0,[z866,z1,z2,z3,z5,z6])],[(0,[z80,z1,z2,z3,z5,z676]),(0,[z1,z2,z90,z732,z5,z6]),(0,[z7,z1,z295,z3,z5,z6]),(0,[z867,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z62,z322])],[(0,[z51,z1,z16,z3,z5,z6]),(0,[z354,z1,z2,z3,z5,z6]),(0,[z7,z189,z43,z3,z5,z6]),(0,[z7,z1,z437,z2,z3,z6]),(0,[z7,z541,z2,z3,z5,z6]),(0,[z10,z1,z8,z3,z5,z220]),(0,[z868,z10,z1,z2,z5,z6]),(0,[z10,z1,z774,z145,z5,z6]),(0,[z60,z1,z2,z140,z209,z6]),(1,[z10,z1,z2,z5,z805]),(0,[z431,z86,z10,z1,z5,z6])],[(0,[z10,z104,z2,z141,z5,z6]),(0,[z7,z1,z8,z3,z254,z6]),(0,[z1,z2,z4,z5,z395,z6]),(0,[z869,z1,z2,z3,z5,z6]),(0,[z870,z10,z2,z3,z5,z6])],[(0,[z10,z1,z2,z5,z62,z334]),(0,[z871,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z761]),(0,[z10,z872,z1,z2,z3,z74])]],
   [[(0,[z10,z1,z2,z873,z5,z6]),(0,[z10,z1,z2,z3,z874,z6]),(0,[z57,z91,z1,z2,z3,z5]),(0,[z2,z3,z4,z5,z222,z6]),(0,[z70,z10,z1,z79,z3,z5]),(0,[z10,z2,z3,z875,z5,z6]),(0,[z10,z876,z2,z3,z5,z6])],[(0,[z170,z745,z2,z3,z5,z6]),(0,[z280,z1,z2,z3,z5,z220]),(0,[z12,z1,z3,z5,z6,z142]),(0,[z1,z2,z311,z4,z5,z6]),(0,[z245,z266,z2,z3,z156,z6])],[(0,[z1,z2,z3,z5,z877,z6]),(0,[z10,z872,z1,z2,z3,z87]),(0,[z86,z10,z1,z5,z6,z193])],[(0,[z1,z8,z17,z3,z5,z6]),(0,[z189,z43,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z106,z87]),(0,[z10,z1,z2,z197,z3,z5]),(0,[z10,z1,z2,z878,z5,z6]),(0,[z879,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z880,z6]),(0,[z10,z1,z2,z74,z87,z314])],[(0,[z10,z881,z2,z3,z5,z6]),(0,[z10,z882,z2,z3,z5,z6]),(0,[z89,z1,z2,z732,z5,z6]),(0,[z104,z173,z2,z3,z5,z6]),(0,[z1,z2,z4,z5,z6,z14]),(0,[z10,z2,z3,z5,z6,z782]),(0,[z10,z2,z3,z5,z6,z883])],[(0,[z884,z10,z1,z2,z3,z5]),(0,[z134,z173,z2,z3,z5,z6]),(0,[z186,z1,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z203]),(0,[z189,z10,z852,z3,z5,z6]),(0,[z10,z1,z2,z288,z5,z49]),(0,[z10,z1,z2,z140,z6,z798]),(0,[z10,z1,z885,z3,z5,z6])],[(0,[z213,z32,z2,z3,z5,z6]),(0,[z68,z104,z2,z3,z5,z6]),(0,[z10,z1,z2,z886,z5,z6]),(0,[z10,z1,z2,z3,z887,z6]),(0,[z7,z1,z2,z3,z4,z220]),(0,[z7,z1,z2,z5,z6,z208]),(0,[z10,z1,z2,z3,z5,z220]),(0,[z10,z2,z716,z211,z5,z6]),(0,[z10,z1,z2,z3,z6,z711]),(0,[z10,z1,z2,z5,z395,z6])],[(0,[z300,z93,z10,z1,z5,z6]),(0,[z10,z2,z3,z74,z222,z87])]],
   [[(0,[z10,z1,z2,z888,z3,z6]),(0,[z7,z1,z748,z3,z5,z6]),(0,[z1,z2,z3,z5,z175,z459]),(0,[z70,z10,z653,z1,z3,z5])],[(0,[z7,z1,z2,z3,z5,z889]),(0,[z80,z173,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z148]),(0,[z93,z10,z1,z243,z5,z6]),(0,[z10,z890,z2,z3,z5,z6]),(0,[z86,z10,z1,z2,z74,z87])],[(0,[z354,z1,z16,z3,z5,z6]),(0,[z332,z10,z242,z2,z3,z5]),(0,[z10,z1,z2,z3,z891,z6]),(0,[z892,z1,z2,z3,z5,z6]),(0,[z117,z10,z2,z5,z6,z65]),(0,[z893,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z894,z5,z6])],[(0,[z567,z1,z17,z3,z5,z6]),(0,[z7,z479,z1,z2,z3,z6]),(0,[z7,z2,z3,z5,z6,z203]),(0,[z429,z1,z2,z3,z5,z220]),(0,[z10,z895,z2,z3,z5,z6]),(0,[z1,z2,z896,z4,z5,z6]),(0,[z429,z1,z2,z5,z395,z6]),(0,[z897,z10,z1,z2,z5,z6])],[(0,[z1,z2,z3,z4,z6,z697]),(0,[z10,z2,z3,z156,z277,z6]),(0,[z898,z10,z2,z3,z5,z6])],[(0,[z10,z1,z899,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z900]),(0,[z7,z1,z2,z3,z188,z6]),(0,[z10,z1,z2,z3,z5,z901]),(0,[z10,z1,z3,z5,z46,z357]),(0,[z10,z1,z2,z5,z6,z902])],[(0,[z7,z104,z2,z3,z5,z220]),(0,[z10,z1,z2,z141,z5,z220]),(0,[z70,z1,z3,z4,z5,z47]),(0,[z1,z2,z3,z74,z4,z87]),(0,[z903,z10,z1,z2,z5,z6])],[(0,[z7,z2,z3,z5,z6,z148]),(0,[z1,z101,z3,z71,z4,z6]),(0,[z10,z1,z2,z904,z5,z6]),(0,[z1,z905,z2,z3,z5,z6]),(0,[z906,z1,z2,z3,z5,z6])]],
   [[(0,[z10,z907,z2,z3,z5,z6]),(0,[z908,z1,z2,z3,z5,z6]),(0,[z244,z10,z1,z2,z6,z65]),(0,[z431,z259,z10,z3,z5,z6])],[(0,[z245,z1,z2,z3,z5,z6]),(0,[z7,z1,z8,z403,z5,z6]),(0,[z7,z285,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z473,z6]),(0,[z909,z10,z1,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z910]),(1,[z10,z2,z716,z5,z6]),(0,[z40,z285,z10,z2,z5,z41]),(0,[z10,z1,z2,z5,z62,z179]),(0,[z10,z1,z2,z6,z798,z65])],[(0,[z10,z1,z2,z3,z5,z911]),(0,[z1,z2,z3,z5,z6,z247]),(0,[z7,z1,z3,z5,z6,z346]),(0,[z10,z912,z2,z3,z5,z6]),(0,[z541,z506,z10,z2,z5,z6])],[(0,[z0,z2,z3,z5,z6,z326]),(0,[z1,z2,z3,z206,z4,z6]),(0,[z913,z10,z1,z3,z5,z6]),(0,[z7,z173,z2,z3,z5,z220]),(0,[z10,z1,z97,z3,z5,z220]),(0,[z155,z2,z3,z4,z6,z21]),(0,[z1,z2,z140,z209,z4,z6]),(0,[z1,z3,z4,z5,z6,z346]),(0,[z914,z10,z1,z2,z3,z5]),(0,[z915,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z6,z26]),(0,[z541,z2,z3,z4,z5,z6]),(0,[z10,z1,z3,z5,z46,z375]),(0,[z10,z1,z2,z209,z210,z6])],[(0,[z1,z365,z17,z3,z5,z6]),(0,[z7,z30,z31,z1,z2,z3]),(0,[z70,z10,z1,z3,z5,z591]),(0,[z10,z1,z2,z916,z5,z6]),(0,[z1,z2,z140,z423,z209,z6])],[(0,[z1,z2,z4,z5,z6,z291])],[(0,[z1,z2,z3,z223,z4,z6]),(0,[z7,z1,z2,z85,z3,z6])]],
   [[(0,[z7,z1,z2,z3,z424,z6]),(0,[z10,z1,z2,z917,z5,z6]),(0,[z245,z0,z2,z3,z5,z6]),(0,[z7,z1,z2,z140,z209,z6]),(0,[z1,z2,z3,z5,z152,z105]),(0,[z10,z1,z918,z3,z5,z6]),(0,[z919,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z920])],[(0,[z7,z1,z2,z3,z501,z6]),(0,[z7,z1,z64,z162,z5,z6]),(0,[z7,z1,z3,z5,z6,z193]),(0,[z10,z173,z2,z403,z5,z6]),(0,[z10,z921,z2,z3,z5,z6]),(0,[z922,z2,z3,z4,z5,z6]),(0,[z40,z10,z519,z2,z3,z5]),(0,[z604,z1,z923,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z924]),(0,[z1,z2,z3,z5,z6,z246]),(0,[z7,z1,z925,z3,z5,z6]),(0,[z7,z1,z2,z403,z5,z6]),(0,[z7,z1,z2,z288,z5,z62]),(0,[z1,z3,z4,z5,z6,z193]),(0,[z1,z2,z3,z5,z6,z926]),(0,[z927,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z706,z194])],[(0,[z422,z1,z2,z3,z5,z6]),(0,[z1,z928,z2,z3,z5,z6])],[(0,[z10,z1,z929,z3,z5,z6]),(0,[z7,z155,z2,z3,z6,z21]),(0,[z930,z1,z2,z3,z5,z6]),(0,[z431,z10,z3,z5,z222,z6]),(0,[z604,z1,z931,z3,z5,z6])],[(0,[z20,z1,z2,z3,z5,z6]),(0,[z10,z1,z932,z3,z5,z6]),(0,[z933,z1,z2,z3,z5,z6]),(0,[z934,z1,z2,z3,z5,z6]),(0,[z259,z2,z3,z5,z408,z6])],[(0,[z10,z1,z2,z3,z5,z935]),(0,[z10,z936,z2,z3,z5,z6]),(0,[z10,z937,z2,z3,z5,z6]),(0,[z1,z8,z3,z4,z5,z6]),(0,[z7,z1,z938,z3,z5,z6]),(0,[z7,z1,z2,z3,z254,z220]),(0,[z94,z2,z123,z4,z5,z6]),(0,[z939,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z291])],[(0,[z10,z1,z940,z3,z5,z6]),(0,[z93,z1,z145,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z941]),(0,[z40,z10,z2,z3,z5,z602]),(0,[z9,z10,z1,z5,z346,z194])]],
   [[(0,[z218,z32,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z942]),(0,[z1,z2,z732,z39,z5,z6]),(0,[z10,z2,z3,z5,z6,z943]),(0,[z10,z2,z852,z3,z5,z6])],[(0,[z284,z1,z2,z3,z5,z6]),(0,[z944,z1,z2,z3,z5,z6]),(0,[z10,z945,z2,z3,z5,z6]),(0,[z251,z10,z1,z3,z523,z6]),(0,[z10,z1,z946,z3,z5,z6]),(0,[z604,z947,z2,z3,z5,z6])],[(0,[z1,z365,z3,z241,z5,z6]),(0,[z10,z266,z2,z3,z156,z6]),(0,[z244,z572,z1,z2,z6,z65])],[(0,[z1,z97,z3,z4,z5,z6]),(0,[z948,z10,z1,z2,z5,z6]),(0,[z1,z2,z5,z408,z395,z6])],[(0,[z7,z1,z53,z3,z5,z6]),(0,[z250,z10,z2,z618,z5,z6]),(0,[z10,z1,z101,z71,z6,z208])],[(0,[z10,z1,z820,z3,z5,z6]),(0,[z10,z949,z2,z3,z5,z6]),(0,[z10,z1,z114,z3,z5,z46]),(0,[z950,z1,z2,z3,z5,z6]),(0,[z2,z3,z5,z408,z222,z6])],[(0,[z10,z951,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z952]),(0,[z7,z953,z2,z3,z5,z6]),(0,[z10,z1,z2,z954,z5,z6]),(0,[z80,z1,z2,z3,z5,z175]),(0,[z80,z227,z2,z3,z5,z175]),(0,[z70,z541,z10,z2,z3,z5]),(0,[z10,z1,z2,z5,z805,z194])],[(0,[z7,z1,z97,z403,z5,z6]),(0,[z955,z1,z2,z3,z5,z6]),(0,[z86,z10,z1,z2,z5,z6]),(0,[z86,z429,z1,z2,z5,z6])]],
   [[(0,[z1,z745,z2,z3,z5,z6]),(0,[z245,z32,z2,z3,z5,z6]),(0,[z104,z2,z3,z4,z5,z6]),(0,[z226,z1,z2,z3,z4,z6]),(0,[z266,z2,z3,z156,z4,z6]),(0,[z155,z2,z3,z6,z246,z21])],[(0,[z10,z1,z8,z3,z5,z6]),(0,[z318,z1,z2,z3,z4,z6]),(0,[z80,z135,z2,z3,z5,z175]),(0,[z1,z2,z3,z5,z6,z956]),(0,[z10,z957,z2,z3,z5,z6])],[(0,[z1,z494,z2,z3,z5,z6]),(0,[z1,z2,z17,z3,z5,z220]),(0,[z1,z2,z102,z3,z5,z6]),(0,[z1,z8,z97,z3,z5,z6]),(0,[z10,z94,z2,z123,z5,z6]),(0,[z428,z10,z1,z140,z5,z6])],[(0,[z117,z2,z3,z4,z5,z6]),(0,[z958,z1,z2,z3,z5,z6]),(0,[z10,z1,z959,z3,z5,z6])],[(0,[z7,z1,z2,z531,z3,z6]),(0,[z909,z1,z3,z4,z5,z6]),(0,[z960,z1,z2,z3,z5,z6]),(0,[z186,z10,z1,z2,z5,z6]),(0,[z1,z2,z961,z3,z5,z6])],[(0,[z10,z1,z2,z719,z5,z6]),(0,[z7,z95,z2,z3,z5,z96]),(0,[z173,z2,z3,z5,z6,z105]),(0,[z250,z10,z2,z716,z5,z6]),(0,[z10,z1,z2,z716,z5,z6]),(0,[z10,z962,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z6,z798]),(0,[z10,z1,z2,z5,z62,z805])],[(0,[z10,z2,z3,z5,z850,z6]),(0,[z10,z1,z2,z5,z6,z963]),(0,[z541,z10,z2,z5,z6,z291]),(0,[z964,z10,z1,z3,z5,z6])],[(0,[z7,z1,z965,z3,z5,z6]),(0,[z506,z1,z2,z4,z5,z6]),(0,[z1,z2,z966,z3,z5,z6]),(0,[z10,z1,z2,z967,z5,z6]),(0,[z9,z10,z1,z2,z5,z628]),(0,[z10,z1,z2,z140,z149,z6])]],
   [[(0,[z968,z10,z1,z2,z3,z6]),(0,[z135,z2,z3,z4,z5,z6]),(0,[z969,z1,z2,z3,z5,z6]),(0,[z428,z10,z3,z5,z6,z203])],[(1,[z1,z820,z3,z5,z6]),(0,[z7,z104,z8,z3,z5,z6]),(0,[z10,z1,z8,z141,z5,z6]),(0,[z285,z1,z2,z4,z5,z6]),(0,[z70,z10,z1,z3,z5,z761]),(0,[z117,z10,z2,z140,z5,z6])],[(0,[z10,z1,z2,z3,z5,z6]),(0,[z10,z227,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z5,z152,z220]),(0,[z1,z2,z3,z970,z5,z6]),(0,[z10,z1,z2,z543,z6,z65]),(0,[z10,z1,z2,z5,z6,z971]),(0,[z972,z10,z1,z2,z5,z6]),(0,[z10,z2,z3,z5,z6,z973])],[(0,[z7,z1,z2,z3,z5,z974]),(0,[z1,z2,z3,z5,z6,z975])],[(0,[z20,z32,z2,z3,z5,z6]),(0,[z976,z10,z1,z2,z5,z6]),(0,[z10,z104,z2,z3,z5,z152]),(0,[z9,z10,z1,z2,z5,z194])],[(0,[z10,z135,z2,z3,z5,z6]),(0,[z1,z2,z3,z315,z4,z6]),(0,[z1,z2,z90,z5,z6,z56]),(0,[z604,z1,z2,z3,z5,z152]),(0,[z1,z64,z162,z4,z5,z6]),(0,[z1,z2,z128,z487,z5,z6]),(0,[z650,z250,z10,z2,z5,z6])],[(0,[z10,z1,z295,z136,z5,z6]),(0,[z977,z10,z1,z3,z5,z6]),(0,[z978,z1,z2,z3,z5,z6]),(0,[z259,z86,z10,z2,z5,z6])],[(0,[z429,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z6,z979]),(0,[z10,z2,z980,z3,z5,z6]),(0,[z10,z1,z64,z5,z6,z577]),(0,[z1,z2,z3,z981,z5,z6])]],
   [[(0,[z321,z1,z2,z3,z4,z6]),(0,[z10,z242,z3,z5,z6,z191]),(0,[z10,z1,z3,z6,z711,z177]),(0,[z86,z10,z2,z5,z222,z6])],[(0,[z10,z1,z2,z3,z982,z6]),(0,[z10,z173,z2,z3,z5,z152]),(0,[z10,z1,z2,z983,z5,z6]),(0,[z93,z10,z1,z643,z5,z6]),(0,[z984,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z985]),(0,[z10,z1,z2,z141,z5,z6]),(0,[z10,z1,z986,z3,z5,z6]),(0,[z7,z104,z2,z3,z5,z6]),(0,[z7,z1,z2,z141,z4,z6]),(0,[z7,z1,z2,z3,z5,z152]),(0,[z987,z10,z1,z2,z5,z6]),(0,[z988,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z989,z5,z6]),(0,[z990,z1,z2,z3,z5,z6]),(0,[z10,z1,z114,z554,z3,z5]),(0,[z10,z991,z2,z3,z5,z6])],[(0,[z992,z10,z1,z3,z5,z6]),(0,[z40,z393,z10,z3,z5,z6]),(0,[z993,z10,z2,z3,z5,z6]),(0,[z10,z1,z3,z5,z6,z994])],[(0,[z7,z1,z2,z3,z369,z6]),(0,[z7,z1,z720,z3,z5,z6]),(0,[z10,z1,z2,z3,z747,z6]),(0,[z1,z2,z3,z5,z995,z6]),(0,[z1,z2,z3,z5,z996,z6]),(0,[z10,z1,z3,z5,z6,z997]),(0,[z10,z2,z3,z5,z222,z6])],[(0,[z7,z1,z2,z3,z5,z721]),(0,[z250,z2,z211,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z998])],[(0,[z234,z1,z53,z3,z5,z6]),(0,[z10,z190,z242,z3,z5,z6]),(0,[z10,z1,z101,z311,z71,z6])],[(0,[z10,z1,z97,z3,z5,z6]),(0,[z10,z1,z2,z754,z5,z6]),(0,[z7,z173,z2,z3,z5,z6]),(0,[z7,z1,z97,z3,z4,z6]),(0,[z7,z1,z101,z3,z71,z6]),(0,[z7,z1,z2,z311,z5,z6]),(0,[z999,z1,z2,z4,z5,z6]),(0,[z1000,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z209,z6,z798]),(0,[z1,z3,z5,z408,z6,z193])]],
   [[(0,[z10,z2,z3,z5,z6,z1001]),(0,[z259,z2,z3,z4,z5,z6]),(0,[z1002,z10,z2,z3,z5,z6])],[(0,[z7,z1,z8,z3,z5,z220]),(0,[z10,z1,z2,z5,z6,z1003]),(0,[z155,z10,z2,z3,z6,z21]),(1,[z10,z1,z2,z6,z798])],[(0,[z77,z1,z97,z3,z5,z6]),(0,[z7,z104,z2,z141,z5,z6]),(0,[z7,z1,z2,z141,z5,z152]),(0,[z10,z1,z3,z5,z6,z764]),(0,[z10,z1,z3,z5,z46,z502])],[(0,[z10,z1,z2,z763,z5,z6]),(0,[z7,z1,z733,z3,z5,z6]),(0,[z7,z1,z2,z3,z6,z663]),(0,[z10,z1,z2,z1004,z5,z6]),(0,[z1,z2,z44,z4,z5,z6]),(0,[z1005,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z6,z782])],[(0,[z10,z1,z2,z5,z6,z998]),(0,[z527,z1,z2,z3,z5,z105]),(0,[z1,z2,z3,z4,z5,z220])],[(0,[z10,z1,z2,z3,z5,z776]),(0,[z7,z1,z2,z737,z5,z6]),(0,[z7,z1,z2,z738,z5,z6]),(0,[z10,z1,z2,z777,z5,z6]),(0,[z1,z2,z3,z5,z1006,z6]),(0,[z70,z422,z1,z3,z5,z47]),(0,[z1007,z1,z2,z3,z5,z6]),(0,[z428,z10,z1,z5,z6,z65])],[(0,[z147,z1,z17,z3,z5,z6]),(0,[z7,z173,z2,z141,z5,z6]),(0,[z173,z2,z3,z5,z6,z220]),(0,[z7,z104,z97,z3,z5,z6]),(0,[z7,z1,z97,z3,z5,z152]),(0,[z7,z1,z2,z197,z3,z5]),(0,[z7,z1,z3,z5,z6,z490]),(0,[z10,z1,z97,z141,z5,z6]),(0,[z80,z1,z2,z3,z5,z152]),(0,[z922,z10,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z1008,z5]),(0,[z10,z1009,z1,z2,z3,z5]),(0,[z10,z1,z2,z1010,z5,z6]),(0,[z10,z1,z2,z1011,z5,z6]),(0,[z1,z2,z3,z5,z1012,z6])]],
   [[(0,[z10,z1,z2,z5,z6,z1013]),(1,[z1,z2,z732,z5,z6]),(1,[z1,z2,z3,z747,z6]),(0,[z1,z3,z4,z5,z6,z490]),(0,[z10,z1,z64,z607,z5,z6]),(0,[z428,z117,z10,z3,z5,z6]),(0,[z1014,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z785,z5,z6]),(0,[z1015,z1,z2,z3,z5,z6]),(0,[z604,z1,z2,z894,z5,z6])],[(0,[z1016,z10,z1,z2,z5,z6]),(0,[z7,z1,z2,z3,z254,z6]),(0,[z1,z2,z3,z5,z1017,z6])],[(0,[z669,z1,z2,z3,z5,z105]),(0,[z1018,z10,z2,z3,z5,z6]),(0,[z10,z1,z3,z5,z6,z1019]),(0,[z80,z1,z2,z81,z5,z175]),(0,[z1020,z10,z1,z2,z5,z6]),(0,[z10,z1,z311,z5,z46,z6]),(0,[z10,z1,z2,z780,z5,z6])],[(0,[z7,z1,z2,z3,z229,z6]),(0,[z7,z1,z2,z750,z5,z6]),(0,[z7,z173,z97,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z751]),(0,[z7,z752,z2,z3,z5,z6]),(0,[z324,z1,z2,z3,z5,z152]),(0,[z10,z1,z2,z3,z5,z734]),(0,[z10,z1,z2,z305,z5,z6]),(0,[z10,z872,z1,z2,z3,z5])],[(0,[z572,z1,z2,z3,z5,z6]),(0,[z1021,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z1022,z5,z6]),(0,[z10,z1,z2,z3,z1023,z6]),(0,[z7,z759,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z5,z760]),(0,[z1,z2,z3,z5,z408,z6]),(0,[z10,z1,z2,z44,z5,z6]),(0,[z1,z2,z3,z1024,z5,z6]),(0,[z10,z1,z2,z1025,z5,z6]),(1,[z10,z1,z774,z5,z6])],[(0,[z10,z1,z2,z3,z5,z1026]),(0,[z10,z1,z2,z5,z6,z14]),(0,[z10,z1,z1027,z3,z5,z6])]],
   [[(0,[z10,z745,z2,z3,z5,z6]),(0,[z283,z1,z97,z3,z5,z6]),(0,[z1028,z10,z1,z2,z5,z6]),(0,[z742,z1,z2,z3,z5,z6]),(0,[z285,z10,z2,z5,z96,z6]),(0,[z10,z1,z2,z1029,z5,z6])],[(0,[z10,z1,z1030,z3,z5,z6]),(0,[z10,z1,z2,z140,z206,z6]),(0,[z324,z173,z2,z3,z5,z6]),(0,[z1,z2,z97,z3,z5,z220]),(0,[z70,z10,z1,z3,z5,z705]),(0,[z332,z189,z10,z3,z5,z6]),(0,[z1031,z1,z2,z3,z5,z6]),(0,[z40,z10,z3,z5,z490,z41]),(0,[z1,z2,z3,z5,z6,z1032])],[(0,[z7,z1,z2,z765,z5,z6]),(0,[z7,z766,z2,z3,z5,z6]),(0,[z7,z1,z2,z141,z254,z6]),(0,[z10,z1,z2,z1033,z5,z6]),(0,[z1,z2,z3,z5,z6,z1034]),(0,[z1035,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z423,z5,z6]),(0,[z1,z2,z90,z403,z5,z6]),(0,[z7,z771,z2,z3,z5,z6]),(0,[z332,z1,z2,z3,z4,z5]),(0,[z510,z10,z31,z1,z2,z3]),(0,[z9,z10,z1,z2,z5,z703])],[(0,[z70,z10,z1,z3,z5,z22]),(0,[z10,z1,z2,z512,z5,z62]),(0,[z10,z1,z801,z3,z5,z6]),(0,[z40,z10,z2,z3,z5,z703]),(0,[z1,z2,z3,z1036,z5,z6])],[(0,[z1,z2,z4,z5,z6,z314]),(0,[z10,z1,z3,z71,z6,z72]),(0,[z1037,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z1038,z3,z5]),(0,[z1039,z1,z2,z3,z5,z6]),(0,[z40,z10,z2,z3,z5,z705]),(0,[z1,z2,z3,z5,z6,z1040]),(0,[z10,z266,z2,z171,z156,z6]),(0,[z506,z10,z1,z2,z5,z6]),(0,[z70,z541,z10,z3,z5,z47])],[(0,[z10,z1041,z2,z3,z5,z6]),(0,[z10,z1,z2,z81,z5,z6]),(0,[z7,z244,z1,z2,z6,z65]),(0,[z10,z104,z2,z403,z5,z6]),(0,[z7,z1,z97,z3,z254,z6]),(0,[z10,z1,z2,z403,z5,z152]),(0,[z10,z227,z2,z81,z5,z6]),(0,[z604,z1,z2,z3,z5,z175]),(0,[z332,z1005,z1,z2,z3,z5]),(0,[z40,z393,z10,z1,z3,z5]),(0,[z251,z10,z1,z3,z6,z177]),(0,[z1042,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z3,z74,z87])]],
   [[(0,[z7,z332,z1,z2,z3,z5]),(0,[z95,z2,z3,z4,z5,z96]),(0,[z10,z1,z2,z896,z5,z6]),(1,[z1,z2,z3,z5,z734]),(0,[z285,z10,z1,z2,z5,z6])],[(0,[z68,z1,z2,z3,z5,z220]),(0,[z117,z10,z2,z3,z5,z6]),(0,[z10,z1,z2,z5,z1043,z6])],[(0,[z10,z1,z2,z1044,z5,z6]),(0,[z7,z1,z2,z3,z18,z6]),(0,[z7,z1,z2,z5,z6,z257]),(0,[z1,z2,z3,z5,z1045,z6]),(0,[z10,z135,z2,z81,z5,z6]),(0,[z40,z10,z2,z171,z5,z6]),(0,[z10,z2,z3,z5,z6,z773]),(0,[z40,z285,z10,z2,z5,z6]),(0,[z431,z10,z1,z5,z395,z6])],[(0,[z51,z1,z53,z3,z5,z6]),(0,[z89,z1,z2,z403,z5,z6]),(1,[z10,z852,z3,z5,z6]),(0,[z332,z189,z10,z43,z3,z5]),(0,[z1,z2,z3,z5,z6,z1046])],[(1,[z745,z2,z3,z5,z6]),(0,[z320,z32,z2,z3,z5,z6]),(0,[z10,z1047,z2,z3,z5,z6]),(0,[z109,z1,z2,z3,z5,z105]),(0,[z10,z1,z2,z774,z5,z6]),(0,[z10,z1048,z2,z3,z5,z6]),(0,[z429,z1,z2,z3,z74,z87])],[(0,[z10,z1,z3,z5,z6,z1049]),(0,[z10,z1050,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z367,z6]),(0,[z7,z1,z2,z3,z654,z6]),(0,[z10,z1,z3,z5,z6,z1051]),(0,[z10,z95,z2,z3,z5,z773]),(0,[z10,z1,z2,z5,z6,z314])],[(0,[z77,z1,z17,z3,z5,z6]),(0,[z7,z1,z2,z3,z415,z6]),(0,[z10,z1,z53,z136,z5,z6]),(0,[z1,z1052,z2,z3,z5,z6])],[(0,[z10,z1,z2,z1053,z3,z5]),(0,[z604,z809,z2,z3,z5,z6])]],
   [[(0,[z345,z1,z8,z3,z5,z6]),(0,[z10,z1,z2,z1054,z5,z6]),(0,[z10,z1,z2,z5,z1055,z6]),(0,[z10,z1,z3,z5,z6,z711]),(0,[z10,z1,z2,z160,z6,z65])],[(0,[z7,z800,z2,z3,z5,z6]),(0,[z1056,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z1057,z5,z6])],[(0,[z7,z86,z1,z2,z5,z6]),(0,[z1,z2,z1058,z4,z5,z6]),(0,[z1059,z1,z2,z3,z5,z6]),(0,[z1060,z1,z2,z3,z5,z6])],[(0,[z1,z2,z820,z3,z5,z6]),(0,[z443,z10,z1,z2,z6,z65]),(0,[z1,z2,z3,z5,z175,z220]),(0,[z93,z10,z1,z444,z5,z6]),(0,[z10,z2,z3,z5,z6,z1061])],[(0,[z1062,z10,z1,z3,z5,z6]),(0,[z10,z2,z3,z5,z6,z1063]),(0,[z572,z1,z2,z90,z5,z6]),(0,[z1,z173,z2,z3,z5,z220])],[(0,[z10,z1,z2,z3,z1064,z6]),(0,[z7,z1,z810,z3,z5,z6]),(0,[z30,z10,z31,z1,z2,z3]),(0,[z1065,z1,z2,z3,z5,z6])],[(0,[z10,z1,z3,z5,z6,z1066]),(0,[z10,z1,z2,z1067,z5,z6]),(0,[z999,z10,z1,z2,z5,z6]),(0,[z10,z1,z2,z171,z5,z6])],[(0,[z7,z259,z2,z3,z5,z6]),(0,[z10,z1,z2,z403,z5,z220]),(0,[z1068,z1,z2,z3,z5,z6]),(0,[z10,z2,z3,z5,z6,z1069])]],
   [[(0,[z1,z2,z197,z3,z4,z5]),(0,[z10,z1,z2,z1070,z5,z6]),(0,[z1071,z1,z2,z3,z5,z6]),(0,[z10,z1072,z1,z2,z5,z6]),(0,[z10,z1,z3,z1073,z5,z6])],[(0,[z170,z173,z2,z3,z5,z6]),(0,[z1074,z1,z2,z3,z5,z6]),(0,[z1,z2,z4,z5,z6,z1075]),(0,[z80,z1,z295,z3,z5,z175]),(0,[z10,z1,z1076,z3,z5,z6]),(0,[z10,z1,z3,z5,z761,z47])],[(0,[z7,z506,z1,z2,z5,z6]),(0,[z10,z1,z3,z5,z6,z1077])],[(0,[z77,z1,z820,z3,z5,z6]),(0,[z7,z1,z2,z822,z5,z6]),(0,[z10,z1,z2,z3,z5,z1078])],[(0,[z7,z1,z2,z3,z160,z6]),(0,[z40,z2,z3,z4,z5,z41]),(0,[z40,z284,z2,z3,z5,z41]),(0,[z10,z1079,z2,z3,z5,z6])],[(0,[z7,z1,z8,z3,z5,z6]),(0,[z332,z189,z10,z1,z3,z5]),(0,[z186,z10,z1,z2,z197,z5]),(0,[z10,z1,z2,z3,z1080,z6]),(0,[z10,z3,z5,z222,z6,z193])],[(0,[z10,z2,z3,z5,z6,z1081]),(0,[z184,z2,z3,z5,z6,z326]),(0,[z1,z2,z171,z4,z5,z6]),(0,[z604,z1,z2,z3,z5,z105]),(0,[z259,z10,z2,z3,z5,z6]),(0,[z10,z2,z5,z395,z222,z6])],[(0,[z328,z1,z2,z90,z5,z6]),(0,[z10,z1082,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z859,z3,z5,z6]),(0,[z10,z1,z2,z5,z6,z1083]),(0,[z1,z16,z820,z3,z5,z6]),(0,[z7,z1,z833,z3,z5,z6]),(0,[z10,z190,z3,z5,z6,z66]),(0,[z10,z2,z123,z5,z6,z447])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z10,z1,z2,z3,z5,z860]),(0,[z10,z1,z2,z5,z6,z1075]),(0,[z10,z1,z2,z305,z74,z87])],[(0,[z10,z1,z723,z3,z5,z6]),(0,[z251,z1,z3,z4,z6,z177]),(0,[z70,z506,z10,z1,z5,z47]),(0,[z10,z872,z1,z2,z3,z6])],[(0,[z1,z2,z3,z476,z4,z6]),(0,[z10,z1,z2,z140,z34,z6]),(0,[z10,z1,z2,z1084,z5,z6])],[(0,[z1,z2,z3,z5,z734,z105])],[(0,[z10,z1,z295,z3,z5,z6]),(0,[z1,z2,z141,z4,z5,z6]),(0,[z1,z2,z136,z4,z5,z6]),(0,[z10,z227,z295,z3,z5,z6]),(0,[z189,z10,z43,z3,z5,z6]),(0,[z1085,z1,z2,z3,z5,z6]),(0,[z1,z2,z1086,z3,z5,z6])],[(0,[z10,z1087,z2,z3,z5,z6]),(0,[z10,z1,z2,z1088,z5,z6]),(0,[z309,z1,z2,z141,z5,z6]),(0,[z1,z2,z3,z5,z6,z1089]),(0,[z109,z1,z2,z3,z5,z220]),(0,[z226,z1,z2,z3,z747,z6]),(0,[z10,z1,z1090,z3,z5,z6]),(0,[z1091,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z1092,z3,z6]),(0,[z1,z2,z4,z5,z6,z208]),(0,[z10,z1,z852,z3,z5,z6]),(0,[z1093,z10,z1,z2,z5,z6]),(0,[z10,z2,z3,z5,z96,z360]),(0,[z30,z10,z872,z1,z2,z3])]],
   [[(0,[z10,z1,z3,z5,z6,z1094]),(0,[z10,z1,z2,z1095,z5,z6]),(0,[z10,z135,z295,z3,z5,z6]),(0,[z1,z2,z3,z1096,z5,z6])],[(0,[z10,z1,z2,z1097,z5,z6]),(0,[z10,z1,z2,z3,z1098,z5])],[(0,[z7,z1,z2,z136,z5,z6]),(0,[z189,z186,z10,z43,z5,z6])],[(0,[z418,z10,z2,z3,z6,z21]),(0,[z7,z1,z2,z3,z165,z6]),(0,[z0,z745,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z167,z6]),(0,[z10,z1,z2,z5,z6,z1099]),(0,[z1,z2,z3,z4,z747,z6]),(0,[z510,z1,z2,z3,z4,z6]),(0,[z1100,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z3,z5,z739]),(0,[z10,z1,z2,z3,z5,z1101]),(0,[z1,z2,z3,z4,z374,z6]),(0,[z250,z10,z317,z2,z5,z6]),(0,[z10,z1,z3,z774,z5,z6])],[(0,[z10,z852,z43,z3,z5,z6]),(0,[z332,z186,z10,z1,z2,z5]),(0,[z1102,z1,z2,z3,z5,z6]),(0,[z1103,z1,z2,z3,z5,z6]),(0,[z10,z1104,z2,z3,z5,z6])],[(0,[z10,z1,z2,z5,z6,z1105]),(0,[z10,z2,z5,z6,z291,z148]),(0,[z431,z1,z3,z5,z408,z6])],[(0,[z10,z1,z2,z732,z5,z6]),(0,[z1106,z1,z2,z3,z5,z6]),(0,[z189,z10,z44,z43,z5,z6]),(0,[z10,z1,z2,z5,z6,z208])]],
   [[(0,[z1,z820,z17,z3,z5,z6]),(0,[z345,z1,z2,z3,z5,z220]),(0,[z393,z10,z1,z3,z5,z6]),(0,[z1107,z1,z2,z3,z5,z6])],[(0,[z1108,z10,z1,z3,z5,z6]),(0,[z10,z1,z2,z3,z1109,z6]),(0,[z10,z1,z2,z1110,z5,z6]),(0,[z10,z2,z3,z1111,z5,z6])],[(0,[z10,z1,z2,z3,z5,z889]),(0,[z10,z1,z1112,z3,z5,z6]),(0,[z1113,z10,z1,z2,z5,z6]),(0,[z266,z494,z2,z3,z156,z6]),(0,[z10,z1,z2,z1114,z5,z6])],[(0,[z572,z1,z2,z39,z5,z6]),(1,[z332,z189,z10,z3,z5]),(0,[z10,z1,z2,z5,z6,z1115]),(0,[z1116,z1,z2,z3,z5,z6])],[(0,[z7,z250,z2,z211,z5,z6]),(0,[z10,z2,z3,z5,z6,z203]),(0,[z70,z541,z10,z3,z5,z6]),(0,[z429,z2,z3,z5,z222,z6])],[(0,[z309,z1,z2,z90,z5,z6]),(0,[z133,z1,z2,z3,z5,z6]),(0,[z541,z10,z2,z3,z5,z6]),(0,[z189,z10,z3,z5,z606,z6]),(0,[z259,z10,z2,z5,z395,z6])],[(0,[z1117,z10,z2,z3,z5,z6]),(0,[z93,z10,z1,z5,z668,z6]),(0,[z431,z10,z1,z3,z5,z6])],[(0,[z10,z104,z2,z3,z5,z220])]],
   [[(0,[z7,z1,z2,z3,z204,z6]),(0,[z68,z135,z2,z3,z5,z6]),(0,[z7,z1,z2,z3,z205,z6]),(0,[z1118,z10,z2,z3,z5,z6]),(0,[z332,z10,z1,z2,z3,z5]),(0,[z10,z2,z3,z5,z6,z148]),(0,[z10,z1,z2,z1119,z5,z6]),(0,[z10,z1,z3,z5,z46,z761])],[(0,[z10,z1,z2,z1120,z5,z6]),(0,[z1121,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z1122,z5,z6])],[(0,[z1,z16,z97,z3,z5,z6]),(0,[z1123,z1,z2,z3,z5,z6]),(0,[z10,z1,z8,z403,z5,z6]),(0,[z10,z1,z1124,z3,z5,z6])],[(0,[z10,z1,z3,z5,z6,z346]),(0,[z10,z1,z2,z5,z6,z1125])],[(0,[z68,z0,z2,z3,z5,z6]),(0,[z1126,z10,z2,z3,z5,z6]),(0,[z10,z173,z2,z3,z5,z220]),(0,[z10,z1,z2,z5,z6,z1127]),(0,[z1128,z1,z2,z3,z5,z6])],[(0,[z1,z2,z534,z3,z4,z6]),(0,[z7,z1,z2,z886,z5,z6]),(0,[z7,z1,z2,z3,z5,z220]),(0,[z7,z1,z2,z5,z395,z6])],[(0,[z10,z789,z2,z3,z5,z6]),(0,[z10,z1,z2,z1129,z5,z6]),(0,[z1,z2,z3,z5,z1130,z6]),(0,[z10,z1,z101,z3,z6,z711])],[(0,[z10,z1,z2,z44,z197,z5]),(0,[z10,z1,z2,z3,z5,z1131]),(0,[z10,z1,z2,z1132,z5,z6]),(0,[z10,z1,z2,z3,z1133,z5]),(0,[z10,z2,z3,z5,z1134,z6])]],
   [[(0,[z10,z1,z1135,z3,z5,z6]),(0,[z7,z70,z1,z3,z5,z47]),(0,[z7,z117,z2,z3,z5,z6]),(0,[z80,z1,z97,z3,z5,z6]),(0,[z1136,z1,z2,z3,z5,z6])],[(0,[z488,z1,z2,z141,z5,z6]),(0,[z1,z2,z775,z4,z5,z6]),(0,[z80,z1,z53,z3,z5,z175]),(0,[z1137,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z140,z209,z6])],[(0,[z10,z2,z3,z5,z6,z1138]),(0,[z7,z895,z2,z3,z5,z6]),(0,[z245,z104,z2,z3,z5,z6]),(0,[z1139,z1,z2,z3,z5,z6]),(0,[z10,z1,z3,z5,z6,z193]),(0,[z10,z1,z2,z5,z6,z805]),(0,[z10,z31,z872,z1,z2,z3])],[(0,[z10,z1,z925,z3,z5,z6]),(0,[z10,z1,z2,z403,z5,z6]),(0,[z529,z1,z2,z39,z5,z6]),(0,[z7,z1,z2,z403,z4,z6]),(0,[z7,z1,z2,z5,z6,z14]),(0,[z10,z266,z2,z156,z6,z257]),(1,[z70,z541,z10,z3,z5]),(0,[z259,z10,z2,z3,z74,z87])],[(0,[z10,z1,z2,z1140,z5,z6]),(0,[z1,z16,z3,z5,z6,z142]),(0,[z1,z101,z102,z3,z71,z6])],[(0,[z104,z32,z2,z3,z5,z6]),(0,[z10,z1,z1141,z3,z5,z6]),(0,[z324,z1,z97,z3,z5,z6]),(0,[z7,z1,z2,z141,z5,z220]),(0,[z1142,z10,z1,z3,z5,z6]),(0,[z428,z10,z1,z3,z5,z6])],[(0,[z1,z2,z3,z5,z6,z734]),(0,[z10,z2,z3,z5,z96,z773])],[(0,[z10,z1,z2,z1143,z5,z6]),(0,[z10,z1,z938,z3,z5,z6]),(0,[z1144,z1,z2,z3,z5,z6]),(0,[z1,z2,z305,z4,z5,z6]),(0,[z1,z1145,z2,z3,z5,z6]),(0,[z429,z1,z3,z5,z6,z193]),(0,[z10,z1,z923,z3,z5,z6])]],
   [[(1,[z173,z2,z3,z5,z220]),(0,[z10,z1,z2,z3,z1146,z6])],[(0,[z10,z1,z1147,z3,z5,z6]),(0,[z10,z1,z2,z1148,z5,z6])],[(0,[z7,z1,z97,z3,z5,z220]),(0,[z10,z1,z295,z81,z5,z6]),(0,[z10,z1,z1149,z3,z5,z6]),(0,[z1150,z1,z2,z3,z5,z6]),(0,[z1151,z1,z2,z3,z5,z6]),(0,[z86,z1,z2,z5,z408,z6]),(0,[z10,z1,z931,z3,z5,z6])],[(0,[z7,z1,z2,z403,z5,z152]),(0,[z7,z428,z1,z3,z5,z6]),(0,[z393,z1,z3,z4,z5,z6]),(0,[z10,z1,z2,z1152,z5,z6]),(0,[z10,z1,z3,z5,z6,z1153]),(0,[z70,z10,z1,z3,z5,z296]),(0,[z10,z1,z2,z5,z1154,z6])],[(0,[z7,z9,z1,z2,z5,z194]),(0,[z10,z1,z2,z5,z6,z1155]),(0,[z1156,z1,z2,z3,z5,z6]),(0,[z10,z242,z852,z3,z5,z6])],[(0,[z135,z32,z2,z3,z5,z6]),(0,[z10,z1,z53,z3,z5,z6]),(0,[z10,z1,z2,z1157,z5,z6]),(0,[z7,z251,z1,z3,z6,z177]),(0,[z1,z53,z3,z4,z5,z6]),(0,[z1,z2,z81,z4,z5,z6]),(0,[z10,z227,z53,z3,z5,z6]),(0,[z393,z10,z1,z5,z6,z14]),(0,[z1158,z1,z2,z3,z5,z6]),(0,[z506,z10,z1,z5,z46,z6])],[(0,[z1,z575,z2,z3,z4,z6]),(0,[z60,z1,z2,z3,z5,z6]),(0,[z1,z2,z1159,z3,z5,z6]),(0,[z1,z2,z3,z445,z5,z459]),(0,[z1160,z1,z2,z3,z5,z6]),(0,[z250,z10,z2,z5,z310,z6]),(0,[z250,z10,z409,z2,z5,z6]),(0,[z1161,z1,z2,z3,z5,z6])],[(0,[z10,z1,z101,z3,z315,z6]),(0,[z10,z1,z2,z3,z5,z952]),(0,[z10,z953,z2,z3,z5,z6]),(0,[z10,z94,z2,z5,z6,z626]),(0,[z9,z10,z1,z2,z5,z296]),(0,[z1,z2,z3,z1162,z5,z6]),(0,[z10,z947,z2,z3,z5,z6])]],
   [[(0,[z10,z1,z2,z3,z6,z1163]),(0,[z443,z1,z2,z3,z4,z6]),(0,[z7,z173,z2,z403,z5,z6]),(0,[z10,z1,z97,z403,z5,z6]),(0,[z1,z2,z4,z5,z1164,z6]),(0,[z10,z135,z53,z3,z5,z6]),(1,[z40,z393,z10,z3,z5]),(0,[z40,z10,z2,z5,z14,z41]),(0,[z70,z541,z10,z1,z3,z5]),(0,[z70,z506,z10,z1,z5,z6])],[(0,[z7,z1,z2,z3,z5,z924]),(0,[z7,z1050,z2,z3,z5,z6]),(0,[z431,z1,z3,z4,z5,z6]),(0,[z9,z428,z10,z1,z5,z194]),(1,[z10,z872,z1,z2,z3])],[(0,[z1165,z1,z2,z3,z5,z6]),(0,[z10,z1,z2,z288,z5,z805])],[(0,[z68,z745,z2,z3,z5,z6]),(0,[z10,z1166,z2,z3,z5,z6]),(0,[z20,z173,z2,z3,z5,z6]),(0,[z1167,z10,z2,z3,z5,z6]),(0,[z1168,z1,z2,z3,z5,z6]),(0,[z244,z10,z1,z2,z373,z6]),(0,[z1169,z1,z2,z3,z5,z6])],[(0,[z51,z1,z8,z3,z5,z6]),(0,[z7,z1,z932,z3,z5,z6]),(0,[z1,z2,z288,z4,z5,z62]),(0,[z1,z2,z1170,z3,z5,z6]),(0,[z10,z1,z2,z1171,z5,z6]),(0,[z285,z10,z1,z5,z6,z490]),(0,[z10,z1,z162,z5,z6,z301]),(0,[z9,z117,z10,z2,z5,z194])],[(0,[z7,z1,z2,z3,z5,z935]),(0,[z7,z936,z2,z3,z5,z6]),(0,[z7,z937,z2,z3,z5,z6]),(0,[z7,z1,z2,z5,z6,z291]),(0,[z1,z97,z3,z5,z6,z105]),(0,[z10,z1,z3,z5,z6,z1172]),(0,[z1173,z1,z2,z3,z5,z6])],[(0,[z119,z32,z2,z3,z5,z6]),(0,[z60,z1,z2,z141,z5,z6]),(0,[z10,z95,z2,z3,z5,z96]),(0,[z393,z285,z10,z1,z5,z6])],[(0,[z7,z1,z2,z3,z5,z942]),(0,[z70,z10,z1,z311,z5,z6])]],
   [[(0,[z10,z1,z965,z3,z5,z6]),(0,[z10,z1,z2,z5,z1164,z6]),(0,[z1174,z10,z2,z3,z5,z6])],[(0,[z7,z1,z2,z3,z483,z6]),(0,[z7,z266,z2,z3,z156,z6]),(0,[z1,z2,z3,z5,z175,z734]),(0,[z10,z1,z162,z774,z5,z6]),(0,[z10,z1,z2,z1175,z5,z6])],[(0,[z10,z104,z8,z3,z5,z6]),(0,[z10,z1,z8,z3,z5,z152]),(0,[z10,z1,z2,z3,z5,z1176]),(0,[z10,z1,z2,z5,z6,z798]),(0,[z1,z1177,z2,z3,z5,z6])],[(0,[z10,z1,z263,z3,z5,z46]),(0,[z10,z1,z2,z1058,z5,z6]),(0,[z173,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z403,z254,z6]),(0,[z10,z1,z2,z3,z1178,z6]),(0,[z431,z10,z1,z3,z74,z87])],[(0,[z10,z1,z2,z1179,z5,z6]),(0,[z10,z1,z1180,z3,z5,z6]),(0,[z10,z1,z2,z3,z5,z974]),(0,[z7,z949,z2,z3,z5,z6]),(0,[z7,z1,z114,z3,z5,z46]),(0,[z1181,z1,z2,z3,z5,z6]),(0,[z10,z1182,z2,z3,z5,z6])],[(0,[z10,z1183,z2,z3,z5,z6]),(0,[z7,z1,z2,z954,z5,z6])],[(0,[z572,z1,z2,z403,z5,z6]),(0,[z1184,z1,z2,z3,z5,z6])],[(0,[z10,z1,z2,z1185,z5,z6]),(0,[z7,z1,z2,z3,z704,z6]),(0,[z1186,z1,z2,z3,z5,z6]),(0,[z10,z173,z8,z3,z5,z6]),(0,[z1,z2,z4,z5,z6,z724]),(0,[z91,z1,z2,z3,z5,z105]),(0,[z1187,z1,z2,z3,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1046).take 190) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1236)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 524, 190] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 99).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 99).take 100).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 199).take 57).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [99, 100, 57] = true :=
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

end PEqualNP.Outside.L_meta_38433

theorem PEqualNP.Outside.L_meta_38433 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3972057216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3972057216) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38433.solve