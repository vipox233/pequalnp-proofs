import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38457

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
  Nat.testBit (4008372928 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x01006b15e10e31bc#64 ++ 0x7f44ff3fe31e73fc#64 : BitVec 128),
   (0x8019184c2860d455#64 ++ 0xffbb18cc7ce3fc7f#64 : BitVec 128),
   (0x00c2e0b057030a8a#64 ++ 0xddc3e0f07f038f8f#64 : BitVec 128),
   (0x02ec00ea86b40f60#64 ++ 0x7bfc00ff87fc0ff0#64 : BitVec 128),
   (0x0cf7b50007dbe000#64 ++ 0x6effff0007fff000#64 : BitVec 128),
   (0x14ffdeff78000000#64 ++ 0x74fffffff8000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [3, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0000000000000000 0x7044003f80000000

def z1 : W := mkw 0x00004a1560000000 0x7444ff3fe0000000

def z2 : W := mkw 0x00c2e0b057030a8a 0xddc3e0f07f038f8f

def z3 : W := mkw 0x01006b15e10e31bc 0x7f44ff3fe31e73fc

def z4 : W := mkw 0x02ec00ea86b40f60 0x7bfc00ff87fc0ff0

def z5 : W := mkw 0x0cf7b50007dbe000 0x6effff0007fff000

def z6 : W := mkw 0x8019184c2860d455 0xffbb18cc7ce3fc7f

def z7 : W := mkw 0x14f7d6b350000000 0x64ffff3380000000

def z8 : W := mkw 0x8008084c28201455 0x910000cc78000c7f

def z9 : W := mkw 0x00c000a006000a00 0x59c000f007000f80

def z10 : W := mkw 0x0c37b50001dbe000 0x263fff0000fff000

def z11 : W := mkw 0x14ffdeff78000000 0x74fffffff8000000

def z12 : W := mkw 0x8019184c2860d455 0x6ebb180c04e3f070

def z13 : W := mkw 0x00c2c0b050000000 0x54c3e0f078000000

def z14 : W := mkw 0x01002100810e31bc 0x0b000000031e73fc

def z15 : W := mkw 0x10084aff78000a8a 0x910000fff8000f8f

def z16 : W := mkw 0x00e4000006900000 0x6afc000007fc0000

def z17 : W := mkw 0x01004a15e00411bc 0x1100003fe00003fc

def z18 : W := mkw 0x0e3d154a80fce560 0x223c1f0f80fc7070

def z19 : W := mkw 0x01086b5de12e35fc 0x7ffcffffe7fe7ffc

def z20 : W := mkw 0x01006b15e10e31bc 0x0444ff33e31e738c

def z21 : W := mkw 0x001110000040c000 0x6ebb180004e3f000

def z22 : W := mkw 0x14e6c6b350000000 0x0044e73380000000

def z23 : W := mkw 0x94ffdeff78201455 0xf5fffffff8000c7f

def z24 : W := mkw 0x14e6e6b357030a8a 0xddc7e7f3ff038f8f

def z25 : W := mkw 0x00002100010a2000 0x6e44ff00031e7000

def z26 : W := mkw 0x0df7ff15e7dff1bc 0x7fffff3fe7fff3fc

def z27 : W := mkw 0x0002e0b051030a8a 0x9503e0f078038f8f

def z28 : W := mkw 0x143d1e4f28000000 0x203c1f0f80000000

def z29 : W := mkw 0x1cffdeff7ed1c000 0x74fffffffce18000

def z30 : W := mkw 0x00c2a0a017030a8a 0x898300c01f038f8f

def z31 : W := mkw 0x0effb5ea87ffef60 0x7fffffff87fffff0

def z32 : W := mkw 0x000040b050000a8a 0x910000f078000f8f

def z33 : W := mkw 0x00c280a016010a02 0x808300c01c018c03

def z34 : W := mkw 0x0000200007030a8a 0x8900000007038f8f

def z35 : W := mkw 0x02ec00ea06b00e40 0x00b800c004e00c00

def z36 : W := mkw 0x80dbf0f85f63cecb 0xddfbe0f07fe38f8f

def z37 : W := mkw 0x94ffdeff7860d455 0xfffffffffce3fc7f

def z38 : W := mkw 0x9cffffff7ffbf455 0xfffffffffffffc7f

def z39 : W := mkw 0x032c0b4fa0bc3574 0x223c1f0f80fc7070

def z40 : W := mkw 0x04ff94ea00000000 0x74ffffff80000000

def z41 : W := mkw 0x01006311c10e21a8 0x0044e733831c0380

def z42 : W := mkw 0x00ec00ea00200440 0x7bfc00ff84e00c70

def z43 : W := mkw 0x00c2a00007030000 0x4cc3e00007038000

def z44 : W := mkw 0x0c35150000d8e000 0x223c1f0000fc7000

def z45 : W := mkw 0x00c2e0b057030a8a 0x0040e03003000380

def z46 : W := mkw 0x8019184c2860d455 0x2238180c00e07070

def z47 : W := mkw 0x02ec4affe6b40f60 0x7ffcffffe7fc0ff0

def z48 : W := mkw 0x00c2c0b050000000 0x0040e03000000000

def z49 : W := mkw 0x03eeebfff7bf3ffe 0xffffffffffffffff

def z50 : W := mkw 0x04f7940000000000 0x64ffff0000000000

def z51 : W := mkw 0x0000000000000000 0xdd8300c07c038c0f

def z52 : W := mkw 0x0d13ff15e14ff1bc 0x7f47ff3fe31ff3fc

def z53 : W := mkw 0x143fde5f78000000 0x243fff0ff8000000

def z54 : W := mkw 0x14ff9e4f28000000 0x64ffff0f80000000

def z55 : W := mkw 0x00e4000000000000 0x60fc000000000000

def z56 : W := mkw 0x02e400a286940b20 0x00440033831c0380

def z57 : W := mkw 0x02eee0fad7b70fea 0xffffe0ffffff8fff

def z58 : W := mkw 0x14ffdeff78000000 0x207cff3f80000000

def z59 : W := mkw 0x020800ea00200e40 0x000000c000000c00

def z60 : W := mkw 0x0000000000000000 0x6ab8000004e00000

def z61 : W := mkw 0x00ec00ea00000000 0x70fc00ff80000000

def z62 : W := mkw 0x943d1e4f2860d455 0x223c1f0f80e07070

def z63 : W := mkw 0x00c2cab570000000 0x74c7fffff8000000

def z64 : W := mkw 0x01c2ebb5f70f3bbe 0xffc7ffffff1fffff

def z65 : W := mkw 0x00c2800006010000 0x0083000004018000

def z66 : W := mkw 0x0cf7b50007dbea8a 0xefffff0007ffff8f

def z67 : W := mkw 0x0008004800200440 0x7bb800cc04e00c70

def z68 : W := mkw 0x1cffffff7fdbe000 0x7efffffffffff000

def z69 : W := mkw 0x94fffeff7f63dedf 0xffffffffffe3ffff

def z70 : W := mkw 0x0000200007030a8a 0xdd8300c07f038f8f

def z71 : W := mkw 0x002c004a00000000 0x203c000f80000000

def z72 : W := mkw 0x01002100010a309c 0x000000000002700c

def z73 : W := mkw 0x0000080420000000 0x7400180c60000000

def z74 : W := mkw 0x94ff9cee3860d455 0xffbb18cc7ce3fc7f

def z75 : W := mkw 0x0eff94ea06f1ce40 0x00bb00c004e18c00

def z76 : W := mkw 0x020800ea86b40f60 0x1b0000ff87fc0ff0

def z77 : W := mkw 0x02e400a286940b20 0x6afc003387fc0380

def z78 : W := mkw 0x00c280a016010a02 0x0000000000000000

def z79 : W := mkw 0x0002e0105103008a 0x8403e0007803800f

def z80 : W := mkw 0x01004a156000109c 0x000000006000000c

def z81 : W := mkw 0x00004a1560000000 0x1000003fe0000000

def z82 : W := mkw 0x81002100816ef5fd 0x8b00000007ffffff

def z83 : W := mkw 0x0800210007dbe000 0x0a00000007fff000

def z84 : W := mkw 0x0de6ef15e79f31bc 0x7f44ff3fe31e73fc

def z85 : W := mkw 0x00c2e0b057030a8a 0x8940e03007038f8f

def z86 : W := mkw 0x0000401040000000 0x5440e03060000000

def z87 : W := mkw 0x801910480860c441 0xeebb18c01ce3fc03

def z88 : W := mkw 0x01c2e1b0d70f3bbe 0xdfc3e0f07f1fffff

def z89 : W := mkw 0x0008004880240560 0x7bfc00ff87fc0ff0

def z90 : W := mkw 0x81197b5de96ef5fd 0xffffffffffffffff

def z91 : W := mkw 0x81086b5de92e35fd 0xff44fffffb1e7fff

def z92 : W := mkw 0x943d1e4f2860d455 0xffbf1fcffce3fc7f

def z93 : W := mkw 0x0000080420001014 0x7f00180c6002707c

def z94 : W := mkw 0x0200000086b40f60 0x0b00000007fc0ff0

def z95 : W := mkw 0x02e400a286b40f60 0x0b44003387fc0ff0

def z96 : W := mkw 0x90084aff78201455 0x910000fff8000c7f

def z97 : W := mkw 0x01002100870f3bbe 0x8b000000071fffff

def z98 : W := mkw 0x0cf7b5a017dbea02 0xeeffffc01ffffc03

def z99 : W := mkw 0x0000200007030000 0x0800000007038000

def z100 : W := mkw 0x10cacaff78000000 0x54c3e0fff8000000

def z101 : W := mkw 0x01002100810e21a8 0x00000000031c0380

def z102 : W := mkw 0x14fffeff7f030a8a 0xfdffffffff038f8f

def z103 : W := mkw 0x00c2e01047030088 0x5dc3e0306703838c

def z104 : W := mkw 0x0011100000000000 0x64bb180000000000

def z105 : W := mkw 0x8819394c2ffbf455 0xffbb18cc7ffffc7f

def z106 : W := mkw 0x02ec00ea80240f60 0x71fc00ff80000ff0

def z107 : W := mkw 0x0000080420001014 0xff8318cc7c03fc7f

def z108 : W := mkw 0x80dbf8fc7f63dedf 0xfffbf8fc7fe3ffff

def z109 : W := mkw 0x0000000080040120 0x7b44003f831c03f0

def z110 : W := mkw 0x00c2e0b057030a8a 0x5d40e0306302038c

def z111 : W := mkw 0x8019184c28201455 0xf5bb18cc78000c7f

def z112 : W := mkw 0x0019184c28000000 0x74bb18cc78000000

def z113 : W := mkw 0x800000000060d455 0x8b00000004e3fc7f

def z114 : W := mkw 0x0cf794a016d1ca02 0x80bb00c01ce18c03

def z115 : W := mkw 0x01006b15610a309c 0x0400ff006002700c

def z116 : W := mkw 0x00ec00ea00000000 0x00b800c000000000

def z117 : W := mkw 0x8cffbd4c2ffbf455 0xffffffcc7ffffc7f

def z118 : W := mkw 0x0000000006900000 0x0a00000007fc0000

def z119 : W := mkw 0x01004b15e00c31bc 0x33041f3fe01c73fc

def z120 : W := mkw 0x02ec00ea86b40f60 0x00fc00f387fc0f80

def z121 : W := mkw 0x00002100810e2120 0x7f44ff3f831e73f0

def z122 : W := mkw 0x04f794000040c000 0x6effff0004e3f000

def z123 : W := mkw 0x15e6efb7f10e31bc 0x7f44ff3fe31e73fc

def z124 : W := mkw 0x0c24050000982000 0x00040700001c0000

def z125 : W := mkw 0x8019384c2f63dedf 0xffbb18cc7fe3ffff

def z126 : W := mkw 0x16ffdefffeb40f60 0x7ffffffffffc0ff0

def z127 : W := mkw 0x0200000086940b20 0x00000000031c0380

def z128 : W := mkw 0x14ffd4fa58000000 0x54fbe0f078000000

def z129 : W := mkw 0x0c13b500014be000 0x0403ff000003f000

def z130 : W := mkw 0x0cf7f5b057dbea8a 0xfffffff07fffff8f

def z131 : W := mkw 0x01004a15e00411bc 0x7544ff3fe00003fc

def z132 : W := mkw 0x0000000000000000 0x910000c078000c0f

def z133 : W := mkw 0x801910480860c441 0xfbbb00cc1ce18c73

def z134 : W := mkw 0x02ec00ea06b00e40 0x70fc00ff84e00c00

def z135 : W := mkw 0x00c2c0b056010a02 0xd4c3e0f07c018c03

def z136 : W := mkw 0x801910480860c441 0x80bb00c01ce18c03

def z137 : W := mkw 0x94ffdeff7860c441 0xf4fffffffce18c03

def z138 : W := mkw 0x01c2e3b1d70f2baa 0x0044e733831c0380

def z139 : W := mkw 0x0200000006b00e40 0x0000000004e00c00

def z140 : W := mkw 0x8008084c28201455 0xff0018cc78027c7f

def z141 : W := mkw 0x0000000000000000 0x0000000000000000

def z142 : W := mkw 0x01002904a10e31bc 0x7f00180c631e73fc

def z143 : W := mkw 0x01000100800c3134 0x02000000001c7070

def z144 : W := mkw 0x81084a5de82415fd 0x910000fff8000fff

def z145 : W := mkw 0x0000421140000000 0x0044e73380000000

def z146 : W := mkw 0x80dbd8fc7860d455 0xfffbf8fc7ce3fc7f

def z147 : W := mkw 0x0cf7b50007dbe000 0xffffffc07ffffc0f

def z148 : W := mkw 0x00004a1560000000 0x0400ff0060000000

def z149 : W := mkw 0x01000000800411bc 0x01000000000003fc

def z150 : W := mkw 0x14fff4fa5f030a8a 0xddfbe0f07f038f8f

def z151 : W := mkw 0x0ef7b5a287dfeb20 0x6effff3387fff380

def z152 : W := mkw 0x02ec00ea06b00e40 0x6afc00c007fc0c00

def z153 : W := mkw 0x94ff94ea1860c441 0x80bb00c01ce18c03

def z154 : W := mkw 0x0000601041020088 0x5d40e0306302038c

def z155 : W := mkw 0x0cf7b50007dbe000 0x227cff0003fc7000

def z156 : W := mkw 0x14fffeff7f030000 0x7cffffffff038000

def z157 : W := mkw 0x03ec6bffe7be3ffc 0x7ffcffffe7fe7ffc

def z158 : W := mkw 0x14eec6fb50000000 0x70fce7ff80000000

def z159 : W := mkw 0x8019184ca864d575 0xffff18ffffffffff

def z160 : W := mkw 0x14f7deb778000000 0x0447ff33f8000000

def z161 : W := mkw 0x0200000080b40560 0x0200000000fc0070

def z162 : W := mkw 0x00c2a00007030000 0x0040e00003000000

def z163 : W := mkw 0x0008084c20201454 0x7fb818cc64e27c7c

def z164 : W := mkw 0x0cf7940006d1c000 0x00bb000004e18000

def z165 : W := mkw 0x0ce6a500079b2000 0x0044e700031c0000

def z166 : W := mkw 0x10084aff78000000 0x100000fff8000000

def z167 : W := mkw 0x0ce6e5b0579b2a8a 0xddc7e7f07f1f8f8f

def z168 : W := mkw 0x01006311c10e21a8 0x5d44e733e31e038c

def z169 : W := mkw 0x94ffdeff7860d455 0x76fffffff8e07070

def z170 : W := mkw 0x801910480860c441 0xddbb00c07ce38c0f

def z171 : W := mkw 0x14ff94ea1e010a02 0x80bb00c01c018c03

def z172 : W := mkw 0x81197b5de96ef5fd 0x7f7cff3fe3fe73fc

def z173 : W := mkw 0x00cae0f857230eca 0xfffbe0fc7fe38fff

def z174 : W := mkw 0x82fd10ea0ef0ce41 0x80bb00c01ce18c03

def z175 : W := mkw 0x00ec004806b00440 0x7bfc00cc07fc0c70

def z176 : W := mkw 0x0000000000000000 0x808300c01c018c03

def z177 : W := mkw 0x14ff94ea18000000 0x00bb00c018000000

def z178 : W := mkw 0x15fffffff90e31bc 0x7ffffffffb1e73fc

def z179 : W := mkw 0x00195a5d68000000 0x74fffffff8000000

def z180 : W := mkw 0x022c004a80b40560 0x223c000f80fc0070

def z181 : W := mkw 0x0cffb5ea07dbe000 0x7effffff87fff000

def z182 : W := mkw 0x000040b050000a8a 0xdd8300f07c038f8f

def z183 : W := mkw 0x000000a010000a02 0x800000c018000c03

def z184 : W := mkw 0x821918eea864df75 0xffbb18fffce3ffff

def z185 : W := mkw 0x82fd18eeaef4df75 0xffff18ffffffffff

def z186 : W := mkw 0x000000a000000a00 0x110000f000000f80

def z187 : W := mkw 0x0ce6a500079b2000 0x6e44ff00031e7000

def z188 : W := mkw 0x801118042840d015 0x840318007803f00f

def z189 : W := mkw 0x9413de157840d015 0x8403ff007803f00f

def z190 : W := mkw 0x01006b15e10e31bc 0xffc7ffffff1fffff

def z191 : W := mkw 0x02eee0fad7b70fea 0x7bfce0ff87fc0ff0

def z192 : W := mkw 0x17ffffffffbe3ffc 0x7ffffffffffe7ffc

def z193 : W := mkw 0x1cffffff7f9b2000 0x74fffffffb1c0000

def z194 : W := mkw 0x0cf7f51047dbe088 0x7fffff3067fff38c

def z195 : W := mkw 0x00c000a006000a00 0x0040003003000380

def z196 : W := mkw 0x14ffdeff78000000 0x04bbffc078000000

def z197 : W := mkw 0x8cff9c4c2ef1d455 0xffbb18cc7ce3fc7f

def z198 : W := mkw 0x001910480060c440 0x7fbb18cc04e3fc70

def z199 : W := mkw 0x03084affe0241ffc 0x110000ffe0000ffc

def z200 : W := mkw 0x14ffd6fb58000000 0x00ffe7f398000000

def z201 : W := mkw 0x02eea0ea87b70f60 0x7fffe0ff87ff8ff0

def z202 : W := mkw 0x0cf7940006d1c000 0x64ffff0004e18000

def z203 : W := mkw 0x0df7f711c7dfe1a8 0x6effff3387fff380

def z204 : W := mkw 0x0a00210087ffef60 0x0b00000007fffff0

def z205 : W := mkw 0x8c3d1d4c28f8f455 0x223c1f0c00fc7070

def z206 : W := mkw 0x1c3d1f4f28d8e000 0x223c1f0f80fc7000

def z207 : W := mkw 0x0224000280940120 0x00040003801c0000

def z208 : W := mkw 0x0000000080040120 0x00440033831c0380

def z209 : W := mkw 0x1413de1578000000 0x7447ff3ff8000000

def z210 : W := mkw 0x02ee80ea96b50f62 0xfbff00ff9ffd8ff3

def z211 : W := mkw 0x01002b05a10e3134 0x6e44ff0f831e7070

def z212 : W := mkw 0x00c2eab577030a8a 0xfdc7ffffff038f8f

def z213 : W := mkw 0x02ec08eea6b41f74 0x7ffc18ffe7fe7ffc

def z214 : W := mkw 0x81195a5de864d5fd 0xffbb18fffce3ffff

def z215 : W := mkw 0x0ef7b50087ffef60 0x6fffff0007fffff0

def z216 : W := mkw 0x06ff94ea86b40f60 0x7fffffff87fc0ff0

def z217 : W := mkw 0x8c3d1d4c28f8f455 0xffbf1fcc7cfffc7f

def z218 : W := mkw 0x00e42100079a2000 0x6efcff0007fe7000

def z219 : W := mkw 0x00eee0fa57030a8a 0xfdffe0ffff038f8f

def z220 : W := mkw 0x82fff8fefff7dfff 0xfffff8ffffffffff

def z221 : W := mkw 0x153d7f5fe90e31bc 0x7f7cff3fe31e73fc

def z222 : W := mkw 0x00000a0520000000 0x20041f0f80000000

def z223 : W := mkw 0x823d184ea8f4d575 0x223c180f80fc7070

def z224 : W := mkw 0x15ffffffff0f3bbe 0xffffffffff1fffff

def z225 : W := mkw 0x0300210087be3ffc 0x0b00000007fe7ffc

def z226 : W := mkw 0x15ffdefff80411bc 0x75fffffff80003fc

def z227 : W := mkw 0x0000000000000000 0x6444ff0000000000

def z228 : W := mkw 0x020000a280040b20 0x0000003380000380

def z229 : W := mkw 0x01000b05a00c3134 0x22041f0f801c7070

def z230 : W := mkw 0x0000601047030a8a 0xdd40e03067038f8f

def z231 : W := mkw 0x16e6c6b3d6940b20 0x0044e733831c0380

def z232 : W := mkw 0x14d3feb57f030a8a 0xddc3fff07f038f8f

def z233 : W := mkw 0x82fd18eeaef4df75 0x7bfc18ff87fc7ff0

def z234 : W := mkw 0x0cf7b500014be000 0x64ffff000003f000

def z235 : W := mkw 0x03ec0befa6bc3f74 0x7bfc1fff87fc7ff0

def z236 : W := mkw 0x0000000000000000 0x598000c004000c00

def z237 : W := mkw 0x0000000080040120 0x1100003f800003f0

def z238 : W := mkw 0x0000000080040120 0x0b000000031c03f0

def z239 : W := mkw 0x0fffffffe7fffffc 0x7fffffffe7fffffc

def z240 : W := mkw 0x153d1f4fa80c3134 0x223c1f0f801c7070

def z241 : W := mkw 0x163d1e4fa8b40560 0x223c1f0f80fc0070

def z242 : W := mkw 0x02ec00ea86b40f60 0x227c003f83fc03f0

def z243 : W := mkw 0x00c0000006000000 0x48c0000007000000

def z244 : W := mkw 0x100042b350000000 0x0000003380000000

def z245 : W := mkw 0x00eec0fa50000000 0x74ffe0fff8000000

def z246 : W := mkw 0x81006b15e16ef5fd 0xff44ff3fe7ffffff

def z247 : W := mkw 0x143d5eff78000000 0x303c1ffff8000000

def z248 : W := mkw 0x0cffb54807fbe440 0x7fffffcc07fffc70

def z249 : W := mkw 0x0000010000082000 0x22041f00001c7000

def z250 : W := mkw 0x00c2e0b057030a8a 0x8443e0307b03838f

def z251 : W := mkw 0x10080a4f28000000 0x0000000f80000000

def z252 : W := mkw 0x0eff94ea86f5cf60 0x7bff00ff87fd8ff0

def z253 : W := mkw 0x1513ff15790a309c 0x0403ff007802700c

def z254 : W := mkw 0x14ffdeff78001014 0x7ffffffff802707c

def z255 : W := mkw 0x14ffdeff78200440 0x7ffffffffce00c70

def z256 : W := mkw 0x01006bb5f10e3bbe 0xff44fffffb1e7fff

def z257 : W := mkw 0x1cff94ea1ed1c000 0x00bb00c01ce18000

def z258 : W := mkw 0x82ec00ea86f4df75 0xfbfc00ff87ffffff

def z259 : W := mkw 0x00c280a010000000 0x008300c018000000

def z260 : W := mkw 0x0cf7b40007d3c000 0x4cfbe00007e38000

def z261 : W := mkw 0x020800ea80240f60 0x110000ff80000ff0

def z262 : W := mkw 0x80d3f8b47f43da9f 0xddc3f8f07f03ff8f

def z263 : W := mkw 0x0000000000000a8a 0x8100000000000f8f

def z264 : W := mkw 0x01006b15e10e31bc 0x2244ff3f831c73f0

def z265 : W := mkw 0x04f7940006900000 0x6effff0007fc0000

def z266 : W := mkw 0x02e6e0b2d7970baa 0x0044e033831c0380

def z267 : W := mkw 0x0df7b50087dff1bc 0x6fffff0007fff3fc

def z268 : W := mkw 0x00006110410a2088 0x7f44ff30631e738c

def z269 : W := mkw 0x80db90e81e61ce43 0x80bb00c01ce18c03

def z270 : W := mkw 0x00c800e806200e40 0x7bf800fc07e00ff0

def z271 : W := mkw 0x01c2ebb5770b3a9e 0xddc3fff07f03ff8f

def z272 : W := mkw 0x00113100014ae000 0x6effff0007fff000

def z273 : W := mkw 0x01006b15610a309c 0x7444ff3fe002700c

def z274 : W := mkw 0x1413de1578000000 0x0403ff0078000000

def z275 : W := mkw 0x00c2e0b051020088 0x5dc3e0f07b02038c

def z276 : W := mkw 0x0008084c28000000 0x100000cc78000000

def z277 : W := mkw 0x80c2e0b05763dedf 0xdfc3e0f07fe3ffff

def z278 : W := mkw 0x8019184c2860d455 0xab38180c04e3fc7f

def z279 : W := mkw 0x8019184c2860d455 0xa2bb18cc1ce1fc73

def z280 : W := mkw 0x8019184c2860d455 0x7f38180c60e2707c

def z281 : W := mkw 0x0cf7950006d9e000 0x22bf1f0004fdf000

def z282 : W := mkw 0x8019184c2860d455 0x76bb18cc78e07070

def z283 : W := mkw 0x02eee0fa57b30eca 0xddfbe0f07fe38f8f

def z284 : W := mkw 0x00e4000006900000 0x00440000031c0000

def z285 : W := mkw 0x1cf7ff157fdbe000 0x6effff007ffff000

def z286 : W := mkw 0x14ffdeff78000000 0xfdfffffffc038c0f

def z287 : W := mkw 0x03e46bb7e79e3bbc 0x7f44ff3fe31e73fc

def z288 : W := mkw 0x800020000763dedf 0x8b00000007e3ffff

def z289 : W := mkw 0x16ffdeff7eb00e40 0x74fffffffce00c00

def z290 : W := mkw 0x0002e0105103008a 0xdd83e0c07c038c0f

def z291 : W := mkw 0x80cae8fc7f231edf 0xddc3e0fc7f038fff

def z292 : W := mkw 0x143d5e5f68000000 0x747cff3fe0000000

def z293 : W := mkw 0x14d3deb578000000 0x54c3fff078000000

def z294 : W := mkw 0x8000080428001015 0x800000007800000f

def z295 : W := mkw 0x00c2e0105703008a 0xccc3e0007f03800f

def z296 : W := mkw 0x03006b15e7be3ffc 0x7f44ff3fe7fe7ffc

def z297 : W := mkw 0x1ce6e7b3579b2000 0x0044e733831c0000

def z298 : W := mkw 0x14ffdeff7e010a02 0xf4fffffffc018c03

def z299 : W := mkw 0x0102eb15f10f31be 0xff47ff3ffb1ff3ff

def z300 : W := mkw 0x00002100010a2000 0x0044e700031c0000

def z301 : W := mkw 0x1402c61150000000 0x0000e70000000000

def z302 : W := mkw 0x00c2c0b050000000 0xddc3e0f07c038c0f

def z303 : W := mkw 0x0008004800200440 0xffbb00cc7ce38c7f

def z304 : W := mkw 0x801bf85c7963d4df 0xffbbf8cc7ce3fc7f

def z305 : W := mkw 0x81117b15694af09d 0x8403ff007803f00f

def z306 : W := mkw 0x14eeceff78000000 0x1044e7fff8000000

def z307 : W := mkw 0x0c35140000d0c000 0x0038000000e00000

def z308 : W := mkw 0x01006110c10e31bc 0x5f40e030631e73fc

def z309 : W := mkw 0x15ffffff790a309c 0x74fffffff802700c

def z310 : W := mkw 0x141bdeff78000000 0x1403fffff8000000

def z311 : W := mkw 0x16ffdefffe940b20 0x74fffffffb1c0380

def z312 : W := mkw 0x01004a15e00411bc 0x7f00183fe00273fc

def z313 : W := mkw 0x00ec00ea06000a00 0x79fc00ff87000f80

def z314 : W := mkw 0x01004b15e00c3134 0x7644ff3fe01c7070

def z315 : W := mkw 0x00c2e1b0570b2a8a 0xffc7fff07f1fff8f

def z316 : W := mkw 0x01002100810e31bc 0x7b44003f831e73fc

def z317 : W := mkw 0x8019184c2860d455 0x84bb18c07ce3fc0f

def z318 : W := mkw 0x01004a15e00411bc 0x7b44003fe31c03fc

def z319 : W := mkw 0x0ce6a500079b2000 0x6afce70007fc0000

def z320 : W := mkw 0x15ffdffff80c3134 0x76fffffff81c7070

def z321 : W := mkw 0x16ffdefff8b40560 0x76fffffff8fc0070

def z322 : W := mkw 0x0000080420001014 0x1100000c6000007c

def z323 : W := mkw 0x0df7ff1567dbf09c 0x6effff0067fff00c

def z324 : W := mkw 0x14ffdeff78000000 0x10bb00fff8000000

def z325 : W := mkw 0x100800ea18000000 0x000000c018000000

def z326 : W := mkw 0x01006311c10e21a8 0x6e44ff33831e7380

def z327 : W := mkw 0x0df7ffb5f7dffbbe 0xffffffffffffffff

def z328 : W := mkw 0x80dbb84c2f63d455 0xfffbf8cc7fe3fc7f

def z329 : W := mkw 0x001110000040c000 0xffbb18c07ce3fc0f

def z330 : W := mkw 0x02ec00ea86b40f60 0x11b800ff84e00ff0

def z331 : W := mkw 0x0c13b50007dbe000 0x0e03ff0007fff000

def z332 : W := mkw 0x14ff94ea18000000 0x64ffffc018000000

def z333 : W := mkw 0x02cae0fad7270fea 0xddc3e0ffff038fff

def z334 : W := mkw 0x0413940000000000 0x0403ff0000000000

def z335 : W := mkw 0x14e6c6b350000000 0x54c7e7f3f8000000

def z336 : W := mkw 0x14e684a210000000 0x0000000000000000

def z337 : W := mkw 0x08c2a10007dbe000 0x4ec3e00007fff000

def z338 : W := mkw 0x801110000840c001 0x8003000018018003

def z339 : W := mkw 0x00ec00ea80040120 0x7bfc00ff831c03f0

def z340 : W := mkw 0x01006b15e10e21a8 0x7444ff3fe31c0380

def z341 : W := mkw 0x01c2ebb5f10e31bc 0x7fc7fffffb1e73fc

def z342 : W := mkw 0x80195a5d6860d455 0xfffffffffce3fc7f

def z343 : W := mkw 0x800800480060d455 0xfbb800cc04e3fc7f

def z344 : W := mkw 0x141bde5d78000000 0x74bbffcc78000000

def z345 : W := mkw 0x0000200001020088 0x090000000302038c

def z346 : W := mkw 0x1cffbf4f2fdbe000 0x6effff0f87fff000

def z347 : W := mkw 0x0ee6a5a2879f2b20 0x0044e733831c0380

def z348 : W := mkw 0x801118042860d455 0x8f0318007ce3fc7f

def z349 : W := mkw 0x00c2e0b057030a8a 0x4cc3e03007038380

def z350 : W := mkw 0x800848fc78201edf 0x910000fc78000fff

def z351 : W := mkw 0x8019184c2860d455 0x91bb00cc7ce18c7f

def z352 : W := mkw 0x00c2e8b477031a9e 0xffc3f8fc7f03ffff

def z353 : W := mkw 0x00002100010a2000 0x0a000000031e7000

def z354 : W := mkw 0x0800000006d1c000 0x0000000004e18000

def z355 : W := mkw 0x16ffdefff8240f60 0x75fffffff8000ff0

def z356 : W := mkw 0x0cf7b5a007dbea00 0x7ffffff007ffff80

def z357 : W := mkw 0x020840fad0240fea 0x910000fff8000fff

def z358 : W := mkw 0x8019394c296af455 0xffffffcc7ffffc7f

def z359 : W := mkw 0x02ec00ea06b00e40 0x7bb800cc04e00c70

def z360 : W := mkw 0x0011180428000000 0x0403180078000000

def z361 : W := mkw 0x00ec00ea06900000 0x7afc00ff87fc0000

def z362 : W := mkw 0x0cf7b500079b2000 0x64ffff00031c0000

def z363 : W := mkw 0x801118042840d015 0x0000180000007000

def z364 : W := mkw 0x0000000000000000 0x6a440000031c0000

def z365 : W := mkw 0x01004ab5f0041bbe 0x910000fff8000fff

def z366 : W := mkw 0x81191b4da86cf575 0x223c1f0f80fc7070

def z367 : W := mkw 0x10195aff78000000 0x74bb18fff8000000

def z368 : W := mkw 0x0d13ff15614bf09c 0x0403ff006003f00c

def z369 : W := mkw 0x02ec00ea86b40f60 0xffff00ffffff8fff

def z370 : W := mkw 0x04f7de1560000000 0x74ffff3fe0000000

def z371 : W := mkw 0x8008084c2860d455 0x9b0000cc7ce3fc7f

def z372 : W := mkw 0x00c2c0b050000a8a 0xd5c3e0f078000f8f

def z373 : W := mkw 0x0cd3b500074be000 0x4cc3ff000703f000

def z374 : W := mkw 0x82fd10ea8ef4cf61 0xfbff00ff9ffd8ff3

def z375 : W := mkw 0x8019785c6962d4dd 0xfffbf8fc7fe3ffff

def z376 : W := mkw 0x81191b4da86cf575 0xffbf1fcffcfffc7f

def z377 : W := mkw 0x00e6e0b057930a8a 0xffffe0f07fff8f8f

def z378 : W := mkw 0x00004a1560001014 0x7f44ff3fe002707c

def z379 : W := mkw 0x95fffffff96ef5fd 0xffffffffffffffff

def z380 : W := mkw 0x1cffffff7fdbea8a 0xffffffffffffff8f

def z381 : W := mkw 0x0000000000000000 0x548300c078000000

def z382 : W := mkw 0x00c2c0b056010a8a 0x918300f07c018f8f

def z383 : W := mkw 0x0000601041020088 0xddc3e0f07f038f8f

def z384 : W := mkw 0x0000080420001014 0x2200180c00007070

def z385 : W := mkw 0x0cf7b50087dfe120 0x7fffff3f87fff3f0

def z386 : W := mkw 0x800000000060d455 0x0200000000e07070

def z387 : W := mkw 0x0000000000000000 0x7b00000c00000070

def z388 : W := mkw 0x000060b051020a8a 0xdd40e0f07b020f8f

def z389 : W := mkw 0x04e6840000000000 0x0044e70000000000

def z390 : W := mkw 0x0208004886b40f60 0x7bb800cc07fc0ff0

def z391 : W := mkw 0x0811310007dbe000 0x6ebb180007fff000

def z392 : W := mkw 0x1513ff15f90e31bc 0x7f47ff3ffb1e73fc

def z393 : W := mkw 0x0de6e711c79f21a8 0x0044e733831c0380

def z394 : W := mkw 0x0cf7ff1567dbe000 0x7effff3fe7fff000

def z395 : W := mkw 0x1cffb5ea1fdbe000 0x6effffc01ffff000

def z396 : W := mkw 0x0c02a500010b2000 0x0000e70000000000

def z397 : W := mkw 0x0eeea5ea87bf2f60 0x7bfce7ff87fc0ff0

def z398 : W := mkw 0x8019184c2860d455 0x950318cc7803fc7f

def z399 : W := mkw 0x96ffdefffef4df75 0xffffffffffffffff

def z400 : W := mkw 0x02e4000086b40f60 0x6bfc000007fc0ff0

def z401 : W := mkw 0x8019184c2860d455 0xa63b180c78e3f07f

def z402 : W := mkw 0x14fd1eef28000000 0x70fc1fff80000000

def z403 : W := mkw 0x8cffbd4c2ffbf455 0x6effff0c07fff070

def z404 : W := mkw 0x000068146102109c 0x7f40f83c630273fc

def z405 : W := mkw 0x01006b15e10e31bc 0x2604ff0fe01e707c

def z406 : W := mkw 0x01006311c10e31bc 0x0b44e733831e73fc

def z407 : W := mkw 0x16fffeffffb70fea 0xffffffffffff8fff

def z408 : W := mkw 0x02ec20ea87b70fea 0xfbfc00ff87ff8fff

def z409 : W := mkw 0x8119394ca96ef5fd 0xffbb18cc7fffffff

def z410 : W := mkw 0x01006b15610a309c 0x7f00ff0c6002707c

def z411 : W := mkw 0x02c800ea86240f60 0x59c000ff87000ff0

def z412 : W := mkw 0x01006b15e10e31bc 0x1500ff3fe00273fc

def z413 : W := mkw 0x0008004800200440 0x00b800c004e00c00

def z414 : W := mkw 0x02e400a286940b20 0x7b44003f831c03f0

def z415 : W := mkw 0x02e6e0b2d7970baa 0xddc7e0f3ff1f8f8f

def z416 : W := mkw 0x08002100079b2000 0x00000000031c0000

def z417 : W := mkw 0x1413fe157903008a 0x8403ff007803800f

def z418 : W := mkw 0x15fffffff90e21a8 0x74fffffffb1c0380

def z419 : W := mkw 0x02fd10ea86f4cf60 0x7fff18ff87fffff0

def z420 : W := mkw 0x02fd18eeaeb40f60 0x7fff18fffffc0ff0

def z421 : W := mkw 0x00e400a200000000 0x0044003380000000

def z422 : W := mkw 0x03e463b3c79e2ba8 0x0044e733831c0380

def z423 : W := mkw 0x01006b15e10e31bc 0x1144e73fe31c03fc

def z424 : W := mkw 0x00004a15e0040120 0x7f44ff3fe31c03f0

def z425 : W := mkw 0x8cf7b50007fbf455 0xefffff0007fffc7f

def z426 : W := mkw 0x00c2a00007030000 0xddc3e0c07f038c0f

def z427 : W := mkw 0x00dbf8fc7f030a8a 0xfdfbf8fc7f038f8f

def z428 : W := mkw 0x02eec0fad6b40f60 0x7fffe0fffffc0ff0

def z429 : W := mkw 0x10084aff78000000 0x7444fffff8000000

def z430 : W := mkw 0x800008042060d455 0xff00180c64e3fc7f

def z431 : W := mkw 0x0000000080040120 0x2204000f801c0070

def z432 : W := mkw 0x01000b0520083014 0x00001f0000007000

def z433 : W := mkw 0x01000a05a0041134 0x0000000f80000070

def z434 : W := mkw 0x84ff9c4c2860d455 0xffffffcc7ce3fc7f

def z435 : W := mkw 0x02ec00ea86940b20 0x70fc00ff831c0380

def z436 : W := mkw 0x0c35350001dae000 0x6e7cff0003fe7000

def z437 : W := mkw 0x8cfffdfc7ffbfedf 0xfffffffc7fffffff

def z438 : W := mkw 0x00e4000006900000 0x00b8000004e00000

def z439 : W := mkw 0x801910480860d455 0x8bbb00c01ce3fc7f

def z440 : W := mkw 0x02ec00ea86b40f60 0x114400ff831c0ff0

def z441 : W := mkw 0x0019184c28000000 0xfdbb18cc7c038c0f

def z442 : W := mkw 0x14ffdeff7840c000 0x7efffffffce3f000

def z443 : W := mkw 0x01197b5de90e31bc 0x7ffffffffb1e73fc

def z444 : W := mkw 0x00c000a006000a00 0x008000c004000c00

def z445 : W := mkw 0x14ffdeff7e000a00 0x7dffffffff000f80

def z446 : W := mkw 0x00dbd8fc78000000 0x74fbf8fc78000000

def z447 : W := mkw 0x0cffbd4c2fdbe000 0x7effffcc7ffff000

def z448 : W := mkw 0x00ec4aff60000000 0x74fcffffe0000000

def z449 : W := mkw 0x0019184c28001014 0x7fbb18cc7802707c

def z450 : W := mkw 0x0200000086b40f60 0x7b44003f87fc0ff0

def z451 : W := mkw 0x01002100810e31bc 0x6f44ff00031e73fc

def z452 : W := mkw 0x00c2e0b057030a8a 0x9140e0f07b000f8f

def z453 : W := mkw 0x032c6b5fe1be35fc 0x7f7cff3fe3fe73fc

def z454 : W := mkw 0x12ec4afffeb40f60 0x7bfc00fffffc0ff0

def z455 : W := mkw 0x000040b050000000 0x100000f078000000

def z456 : W := mkw 0x00f5100006d0c000 0x6eff180007fff000

def z457 : W := mkw 0x00d3f0b05743ca8a 0xfffbf8f07fe3ff8f

def z458 : W := mkw 0x0000200007030a8a 0x0000000003000380

def z459 : W := mkw 0x143d144a08000000 0x0038000000000000

def z460 : W := mkw 0x03ec63fbc7be2fe8 0x7bfce7ff87fc0ff0

def z461 : W := mkw 0x14ff9cee38000000 0x74bb18cc78000000

def z462 : W := mkw 0x04f7b40007030000 0x6cffff0007038000

def z463 : W := mkw 0x022c004a80b40560 0x7bbc00cf84fc0c70

def z464 : W := mkw 0x01006311410a2088 0x0000e70000000000

def z465 : W := mkw 0x0ce6a50007dbe000 0x0a44e70007fff000

def z466 : W := mkw 0x0c13f510514be08a 0x8403ff007803f00f

def z467 : W := mkw 0x0cf7f5b057dbea8a 0x6effff3007fff380

def z468 : W := mkw 0x00c060b047020a88 0x5dc0e0f067020f8c

def z469 : W := mkw 0x00e4000086940120 0x7bfc003f87fc03f0

def z470 : W := mkw 0x0019184c2840c000 0x7ebb18cc7ce3f000

def z471 : W := mkw 0x8c13bd04294bf015 0x8403ff007803f00f

def z472 : W := mkw 0x14e6e6b357030a8a 0x0044e73383000380

def z473 : W := mkw 0x02ec00ea80b40560 0x72fc00ff80fc0070

def z474 : W := mkw 0x0000601041020088 0x0400e0006002000c

def z475 : W := mkw 0x01000b05a00c3134 0x7f041f0fe01e707c

def z476 : W := mkw 0x00c2a0a007030a00 0x5dc3e0f007038f80

def z477 : W := mkw 0x0aec21ea87ffef60 0x7bfc00ff87fffff0

def z478 : W := mkw 0x1cffdfff78d8e000 0x76fffffff8fc7000

def z479 : W := mkw 0x01c2e3b1d70f2baa 0xddc7e7f3ff1f8f8f

def z480 : W := mkw 0x941bde5d7860d455 0xffbbffcc7ce3fc7f

def z481 : W := mkw 0x020800ea80240f60 0x7bb800ff84e00ff0

def z482 : W := mkw 0x0002a00001030000 0x0403e00000038000

def z483 : W := mkw 0x00c2c0b056000a00 0x5dc3e0f07f000f80

def z484 : W := mkw 0x0800210007dbe000 0x6e44ff0007fff000

def z485 : W := mkw 0x0002c01050000000 0x0403e00078000000

def z486 : W := mkw 0x8019184c2860d455 0xb33818cc78e07c7f

def z487 : W := mkw 0x02e400a286940b20 0x59c400f3871c0f80

def z488 : W := mkw 0x01c2eb15e70f31bc 0x7fc7ff3fe71ff3fc

def z489 : W := mkw 0x0000000000000000 0x8900000004038c0f

def z490 : W := mkw 0x8008084c28201455 0x0000000c00000070

def z491 : W := mkw 0x8cf7bd042fdbf015 0xeeffff007ffff00f

def z492 : W := mkw 0x04f7b500010a2000 0x6effff00031e7000

def z493 : W := mkw 0x0000000000001014 0x0b0000000002707c

def z494 : W := mkw 0x80fd184c2ef0d455 0xffff18cc7ffffc7f

def z495 : W := mkw 0x12084afff8240f60 0x110000fff8000ff0

def z496 : W := mkw 0x81117b15e94ef1bd 0xff47ff3ffb1ff3ff

def z497 : W := mkw 0x801110000060d455 0xefbb180004e3fc7f

def z498 : W := mkw 0x00c2e0b057030a8a 0x8483e0c07c038c0f

def z499 : W := mkw 0x0cf7b50007dbe000 0x0447ff00031ff000

def z500 : W := mkw 0x0000080420001014 0x040018006002700c

def z501 : W := mkw 0x0cf7bd0427dbf014 0x7fffff0c67fff07c

def z502 : W := mkw 0x0000000000000000 0x5d0000006002000c

def z503 : W := mkw 0x022c00ea80b40f60 0x333c00ff80fc0ff0

def z504 : W := mkw 0x83fd7bffeffefffd 0xffffffffffffffff

def z505 : W := mkw 0x00002100010a2000 0x0400ff0000027000

def z506 : W := mkw 0x001118042040d014 0x7fbb180c64e3f07c

def z507 : W := mkw 0x000000000040c000 0x0a00000004e3f000

def z508 : W := mkw 0x0cf7b50007dbe000 0x04bbff0004e3f000

def z509 : W := mkw 0x14ffdeff78000a8a 0xf5fffffff8000f8f

def z510 : W := mkw 0x0cf7f5b057dbe000 0x7efffff07ffff000

def z511 : W := mkw 0x0200000080240f60 0x0100000000000ff0

def z512 : W := mkw 0x08e4210007dbe000 0x6afc000007fff000

def z513 : W := mkw 0x820808eea8241f75 0x910000fff8000fff

def z514 : W := mkw 0x14ff9eef38000000 0x20bf1fcf98000000

def z515 : W := mkw 0x82fd18ee2ef0de55 0xffbb18cc7ce3fc7f

def z516 : W := mkw 0x15e6e7b3d10e21a8 0x0044e733831c0380

def z517 : W := mkw 0x02ec00ea06b00e40 0x59f800f007e00f80

def z518 : W := mkw 0x14fffeff7903008a 0xf4fffffff803800f

def z519 : W := mkw 0x02ec00ea86b40f60 0x0bb800c007fc0ff0

def z520 : W := mkw 0x00d3b0000743c000 0x6efbf80007e3f000

def z521 : W := mkw 0x8019184c2860c441 0xf4bb18cc7ce18c03

def z522 : W := mkw 0x01000301800c2120 0x00040703801c0000

def z523 : W := mkw 0x1cf7f7b357dbe000 0x6effff3387fff000

def z524 : W := mkw 0x0000401040000088 0x110000306000038c

def z525 : W := mkw 0x00006a1561020088 0x7d44ff3fe302038c

def z526 : W := mkw 0x0900210087dff1bc 0x0b00000007fff3fc

def z527 : W := mkw 0x8008004808200441 0x800000c018000c03

def z528 : W := mkw 0x14e6ceb770000000 0x7444ff3fe0000000

def z529 : W := mkw 0x001110000040c000 0x040318000003f000

def z530 : W := mkw 0x00c2a100070b2000 0x6ec7ff00071ff000

def z531 : W := mkw 0x0cf5150006d8e000 0x6afc1f0007fc7000

def z532 : W := mkw 0x0800210007dbea8a 0x8b00000007ffff8f

def z533 : W := mkw 0x09006b15e7dff1bc 0x7f44ff3fe7fff3fc

def z534 : W := mkw 0x0002800010010002 0x8003000018018003

def z535 : W := mkw 0x0d351f05a0dcf134 0x223c1f0f80fc7070

def z536 : W := mkw 0x00006b15610a2000 0x7e44ff3fe31e7000

def z537 : W := mkw 0x01117b15e14ef1bc 0x7fffff3fe7fff3fc

def z538 : W := mkw 0x00c280a016010a02 0xdd8300c07c038c0f

def z539 : W := mkw 0x01004211c00401a8 0x0000003380000380

def z540 : W := mkw 0x11084afff80411bc 0x110000fff80003fc

def z541 : W := mkw 0x0cf7b50007dbe000 0x0abb000007fff000

def z542 : W := mkw 0x10ec4aff78000000 0x70fc00fff8000000

def z543 : W := mkw 0x00c2e0b057030a8a 0x59c0e0f007000f80

def z544 : W := mkw 0x82ec08eeaeb41f75 0xfbfc00fffffc0fff

def z545 : W := mkw 0x0000000000000000 0x4c83000004038000

def z546 : W := mkw 0x04f7940000000000 0x00bb000000000000

def z547 : W := mkw 0x01ec6bffe10e31bc 0x7ffcffffe31e73fc

def z548 : W := mkw 0x0008004800000000 0x70b800cc00000000

def z549 : W := mkw 0x022c004a80b40560 0x7b7c003f83fc03f0

def z550 : W := mkw 0x0000000006000a00 0x0900000007000f80

def z551 : W := mkw 0x0002e0105103008a 0x0000e00000000000

def z552 : W := mkw 0x02c2e0b0d7b70fea 0xdfc3e0f07fff8fff

def z553 : W := mkw 0x94ffdeff7840d015 0xf4fffffff803f00f

def z554 : W := mkw 0x8cff94480ef1c441 0x80bb00c01ce18c03

def z555 : W := mkw 0x04f7d4b050000000 0x74fffff078000000

def z556 : W := mkw 0x14ffffff790a2000 0x7efffffffb1e7000

def z557 : W := mkw 0x0efff5fad7ffefea 0xffffffffffffffff

def z558 : W := mkw 0x0008004800200440 0x2238000c00e00070

def z559 : W := mkw 0x022c004a86b40f60 0x2b3c000f87fc0ff0

def z560 : W := mkw 0x801118042840d015 0xdd8318c07c03fc0f

def z561 : W := mkw 0x00fd18ee28000000 0x74ff18fff8000000

def z562 : W := mkw 0x0800010000d8e000 0x0200000000fc7000

def z563 : W := mkw 0x0000000000000000 0x6e00180000027000

def z564 : W := mkw 0x801118042840d015 0xeebb18007ce3f00f

def z565 : W := mkw 0x00c000a000000000 0x50c000f000000000

def z566 : W := mkw 0x000040b050000a8a 0x0000003000000380

def z567 : W := mkw 0x000060b057030a8a 0x990000f07f038f8f

def z568 : W := mkw 0x000800ea00000000 0x100000ff80000000

def z569 : W := mkw 0x08c2e1b057dbea8a 0xdfc3e0f07fffff8f

def z570 : W := mkw 0x0efd15ea86fcef60 0x7bfc1fff87fc7ff0

def z571 : W := mkw 0x10004a1578000000 0x0000000078000000

def z572 : W := mkw 0x01006b15610a309c 0x6e44ff00631e700c

def z573 : W := mkw 0x01006b15e70f3bbe 0xff44ff3fe71fffff

def z574 : W := mkw 0x020800ea80240f60 0x7b4400ff831c0ff0

def z575 : W := mkw 0x01006b15e10e31bc 0x1b00003fe31e73fc

def z576 : W := mkw 0x1424060300000000 0x0004070380000000

def z577 : W := mkw 0x81197b5d696af4dd 0xffbbffcc7ce3fc7f

def z578 : W := mkw 0x08002100014be000 0x000000000003f000

def z579 : W := mkw 0x8200000086f4df75 0x8b00000007ffffff

def z580 : W := mkw 0x01006b15610a309c 0x5d40ff306302738c

def z581 : W := mkw 0x01006a15e10611bc 0x5d40e03fe30203fc

def z582 : W := mkw 0x001110000040c000 0x2238180000e07000

def z583 : W := mkw 0x800000000060d455 0xdf8300c07ce3fc7f

def z584 : W := mkw 0x14f7de1578000000 0x64ffff0078000000

def z585 : W := mkw 0x81dbfbfdff6fffff 0xffffffffffffffff

def z586 : W := mkw 0x01e46b15e79e31bc 0x7ffcff3fe7fe73fc

def z587 : W := mkw 0x14ffdeff7e900000 0x7efffffffffc0000

def z588 : W := mkw 0x0ce6a500079b2000 0x4cc7e700071f8000

def z589 : W := mkw 0x16ff94ea9eb40f60 0x7bff00ff9ffc0ff0

def z590 : W := mkw 0x80db98ec3e61de57 0xffbb18cc7ce3fc7f

def z591 : W := mkw 0x0c1115000048e000 0x00001f0000007000

def z592 : W := mkw 0x00c2800000000000 0x44c3e00000000000

def z593 : W := mkw 0x0cf7940006d1c000 0x6ebb180004e3f000

def z594 : W := mkw 0x0002e01057030a8a 0x8d03e0007f038f8f

def z595 : W := mkw 0x00c000a086040b20 0x7bc400ff871c0ff0

def z596 : W := mkw 0x02ee80ea16b10e42 0x80bb00c01ce18c03

def z597 : W := mkw 0x16fd1eefaeb40f60 0x7bfc1fff87fc0ff0

def z598 : W := mkw 0x0d357f15e1def1bc 0x7f7cff3fe3fe73fc

def z599 : W := mkw 0x8008084c28201455 0xfbb800cc7ce00c7f

def z600 : W := mkw 0x0c1394000041c000 0x0003000000018000

def z601 : W := mkw 0x0cd3f5b0574bea8a 0xddc3fff07f03ff8f

def z602 : W := mkw 0x14111e0528000000 0x00001f0000000000

def z603 : W := mkw 0x0000200001020000 0x4c40e00003020000

def z604 : W := mkw 0x02e400a206900a00 0x0000000000000000

def z605 : W := mkw 0x8019184c2840d015 0xf4bb18cc7803f00f

def z606 : W := mkw 0x02ec60fac7b60fe8 0x7ffce0ffe7fe0ffc

def z607 : W := mkw 0x1effffffffffef60 0x7ffffffffffffff0

def z608 : W := mkw 0x00c2e0b0d7070baa 0xffc7e0ffff1f8fff

def z609 : W := mkw 0x02c000a086b40f60 0x5bc000f007fc0ff0

def z610 : W := mkw 0x8cffb5480ffbe441 0xeeffffc01ffffc03

def z611 : W := mkw 0x01c06bb5e70e3bbc 0x7fc4ffffe71e7ffc

def z612 : W := mkw 0x00006010c10601a8 0x7f44e03fe31e03fc

def z613 : W := mkw 0x0cf7b50007dbe000 0x00ffe70007fd8000

def z614 : W := mkw 0x00c2e0b05103008a 0xd4c3e0f07803800f

def z615 : W := mkw 0x00c000a006000a00 0xddc300f07f038f8f

def z616 : W := mkw 0x800000000060c441 0x8000000004e18c03

def z617 : W := mkw 0x0000000000000000 0x840300007803800f

def z618 : W := mkw 0x02ec40fad6b40fea 0xfbfc00fffffc0fff

def z619 : W := mkw 0x0000601041020088 0x0040e03003000380

def z620 : W := mkw 0x01000b05a00c3134 0x7b441f3f831c73f0

def z621 : W := mkw 0x14ff94ea18000000 0x70ff00ff98000000

def z622 : W := mkw 0x01c2eab5f7071bbe 0xddc3e0ffff038fff

def z623 : W := mkw 0x14fffeff79020088 0x7dfffffffb02038c

def z624 : W := mkw 0x0208004a80240560 0x0000000f80000070

def z625 : W := mkw 0x0cf7f51057dbe08a 0xeeffff007ffff00f

def z626 : W := mkw 0x801118042840d015 0xff03180c7803f07f

def z627 : W := mkw 0x16ff94ea1eb00e40 0x00bb00c01ce00c00

def z628 : W := mkw 0x801958fc7860dedf 0xffbb18fc7ce3ffff

def z629 : W := mkw 0x00c2a0a017030a02 0xccc3e0c01f038c03

def z630 : W := mkw 0x14ffdefff8040120 0x7ffffffffb1c03f0

def z631 : W := mkw 0x02ec00ea86b40f60 0x22bc00cf84fc0c70

def z632 : W := mkw 0x03ec4affe6b41ffc 0x7bfc00ffe7fc0ffc

def z633 : W := mkw 0x801910480860c441 0x0038000000e00000

def z634 : W := mkw 0x80fd18ee2860d455 0xffff18fffce3fc7f

def z635 : W := mkw 0x00000804a0041134 0x7f44183fe31e73fc

def z636 : W := mkw 0x8effbdeeafffff75 0xffffffffffffffff

def z637 : W := mkw 0x01006311c10e21a8 0x7b44e73f831c03f0

def z638 : W := mkw 0x8013f8147943d09f 0x8403f8007803f00f

def z639 : W := mkw 0x00c2e0b057030a8a 0x80c3e0f01f018f83

def z640 : W := mkw 0x8019184c2860d455 0x7bb818cc04e07c70

def z641 : W := mkw 0x1dffffffffdff1bc 0x7ffffffffffff3fc

def z642 : W := mkw 0x03ec21ea87be3ffc 0x7bfc00ff87fe7ffc

def z643 : W := mkw 0x0000000000000000 0x5940003003000380

def z644 : W := mkw 0x80d918ec2e60de55 0xfffb18fc7fe3ffff

def z645 : W := mkw 0x0cf7950000d8e000 0x66ffff0000fc7000

def z646 : W := mkw 0x0c35150000d8e000 0x6ebf1f0004fff000

def z647 : W := mkw 0x1413940018000000 0x0003000018000000

def z648 : W := mkw 0x1c13ff15794be000 0x0403ff007803f000

def z649 : W := mkw 0x16eec6fbd6b40f60 0x7bfce7ff87fc0ff0

def z650 : W := mkw 0x0024000000900000 0x223c000000fc0000

def z651 : W := mkw 0x14fffeff7f030a8a 0x74fffffffb000380

def z652 : W := mkw 0x03086bffe12e3ffc 0x7f44ffffe31e7ffc

def z653 : W := mkw 0x0102eb15710b309e 0x8403ff007803f00f

def z654 : W := mkw 0x8800210007fbf455 0x8b00000007fffc7f

def z655 : W := mkw 0x0c35350007dbe000 0x2a3c1f0007fff000

def z656 : W := mkw 0x00c2e0b057030a8a 0x54c3e0f07b000380

def z657 : W := mkw 0x0df7bf05a7dff134 0x6effff0f87fff070

def z658 : W := mkw 0x0435140000000000 0x203c1f0000000000

def z659 : W := mkw 0x0019104808000000 0x00bb00c018000000

def z660 : W := mkw 0x0cf7f4b057d3ca8a 0xddfbe0f07fe38f8f

def z661 : W := mkw 0x00c020a007030a8a 0xd9c000f007038f8f

def z662 : W := mkw 0x8dffff5deffff5fd 0xffffffffffffffff

def z663 : W := mkw 0x00e6a00007930000 0x6effe00007ff8000

def z664 : W := mkw 0x000020000103008a 0x800000000003800f

def z665 : W := mkw 0x823d184ea8f4d575 0xffbf18cffcfffc7f

def z666 : W := mkw 0x8008084c28201455 0xdd8300cc7c038c7f

def z667 : W := mkw 0x0008004800200440 0x110000cc00000c70

def z668 : W := mkw 0x04f7f4b057030a8a 0xfdfffff07f038f8f

def z669 : W := mkw 0x04ff9c4c28000000 0x74ffffcc78000000

def z670 : W := mkw 0x00c040b056000a8a 0xd9c000f07f000f8f

def z671 : W := mkw 0x02ec004a86b40560 0x6afc000f87fc0070

def z672 : W := mkw 0x0019184c28000000 0x2038180c00000000

def z673 : W := mkw 0x02ec21ea87be2f60 0x7ffcffff87fe7ff0

def z674 : W := mkw 0x90195aff7860d455 0xffbb18fffce3fc7f

def z675 : W := mkw 0x000040105000008a 0x800000007800000f

def z676 : W := mkw 0x0ce6e5b0579b2a8a 0x0044e730031c0380

def z677 : W := mkw 0x143d1e4f28000000 0x74bf1fcff8000000

def z678 : W := mkw 0x00c280a016010a02 0xd9c300f01f018f83

def z679 : W := mkw 0x0effb5ea07fbee40 0x6effffc007fffc00

def z680 : W := mkw 0x8219184caef4df75 0xffbb18cc7fffffff

def z681 : W := mkw 0x0019184c28200440 0x7fbb18cc7ce00c70

def z682 : W := mkw 0x00e400a006900a00 0x7bfc00f007fc0f80

def z683 : W := mkw 0x0cf7940006d1c000 0x6aff000007fd8000

def z684 : W := mkw 0x800000000040d015 0x800000000003f00f

def z685 : W := mkw 0x0000000006010a02 0x8000000004018c03

def z686 : W := mkw 0x0200200087b70fea 0x8b00000007ff8fff

def z687 : W := mkw 0x01006b15e10e31bc 0x0f00ff00631e73fc

def z688 : W := mkw 0x00c2a00007030a8a 0xcdc3e00007038f8f

def z689 : W := mkw 0x05f7ff15e10e31bc 0x7fffff3fe31e73fc

def z690 : W := mkw 0x01002b05a10e31bc 0x2b041f0f831e73fc

def z691 : W := mkw 0x11086bfff90e31bc 0x7f44fffffb1e73fc

def z692 : W := mkw 0x0002e0105103008a 0xdd43e0307b03838f

def z693 : W := mkw 0x01c2ebb5f70f3bbe 0x7f44ff3fe31e73fc

def z694 : W := mkw 0x1cffffff794be000 0x74fffffff803f000

def z695 : W := mkw 0x00c2e0b057030000 0x5cc3e0f07f038000

def z696 : W := mkw 0x8000000000201455 0x8100000000000c7f

def z697 : W := mkw 0x0effb54a87ffe560 0x6effff0f87fff070

def z698 : W := mkw 0x10caeaff7f030a8a 0xddc3e0ffff038f8f

def z699 : W := mkw 0x0c13b500014be000 0x6e47ff00031ff000

def z700 : W := mkw 0x8c1bbd4c296bf455 0xffbbffcc7ce3fc7f

def z701 : W := mkw 0x001110000040c000 0x00bb000004e18000

def z702 : W := mkw 0x00002904210a3014 0x7f44ff0c631e707c

def z703 : W := mkw 0x0ce6840006910000 0x0000000000000000

def z704 : W := mkw 0x0c13b500014be000 0x6ebbff0004e3f000

def z705 : W := mkw 0x022c004a00b00440 0x0038000000e00000

def z706 : W := mkw 0x0000000000200440 0x0b00000004e00c70

def z707 : W := mkw 0x14e6c6b350000000 0x0447e733f8000000

def z708 : W := mkw 0x14eec6fb50000000 0x1044e7ff80000000

def z709 : W := mkw 0x00c2e0b051020088 0xddc3e0f07f038f8f

def z710 : W := mkw 0x00004a1560000000 0x7d44ff3fe3000380

def z711 : W := mkw 0x001118042040d014 0xffbb18cc7ce3fc7f

def z712 : W := mkw 0x0c37b50007dbe000 0x2e3fff0007fff000

def z713 : W := mkw 0x8ceead4c2fbb3455 0x9144e7cc7b1c0c7f

def z714 : W := mkw 0x9cffdeff7ef1c441 0xf4fffffffce18c03

def z715 : W := mkw 0x8019184ca864d575 0x223c180f80fc7070

def z716 : W := mkw 0x00004a1560000000 0x7e44ff3fe31c0000

def z717 : W := mkw 0x0300210087bf3ffe 0x8b00000007ffffff

def z718 : W := mkw 0x14e6c6b350000000 0xddc7e7f3fc038c0f

def z719 : W := mkw 0x14e6ceb770000000 0x74c7fffff8000000

def z720 : W := mkw 0x14ffdeff7e000a00 0x74fffffffc000c00

def z721 : W := mkw 0x1402c61150000000 0x0044e73380000000

def z722 : W := mkw 0x0c35150000d8e000 0x667cff0000fc7000

def z723 : W := mkw 0x02ec00ea86b40f60 0x7fff00fffffc0ff0

def z724 : W := mkw 0x0008084c20201454 0xffbb18cc7ce3fc7f

def z725 : W := mkw 0x01002100870f2baa 0x00000000031c0380

def z726 : W := mkw 0x0c37b50001dbe000 0x6ebfff0004fff000

def z727 : W := mkw 0x00ec4aff60201454 0x7ffcffffe4e27c7c

def z728 : W := mkw 0x0413de1560000000 0x7447ff3fe0000000

def z729 : W := mkw 0x16ffdeff78b00440 0x74fffffff8e00000

def z730 : W := mkw 0x00004ab570000a8a 0xf544fffff8000f8f

def z731 : W := mkw 0x94ffdeff78201edf 0xf5fffffff8000fff

def z732 : W := mkw 0x0df7de15e6d5d1bc 0x11bb003fe4e183fc

def z733 : W := mkw 0x94e6c6b35060d455 0x8b44e73384e3fc7f

def z734 : W := mkw 0x02ec00ea86b40f60 0x7ffcffff87fc0ff0

def z735 : W := mkw 0x801910480860d455 0xdfbb00c07ce3fc7f

def z736 : W := mkw 0x8019184c2860d455 0xffff18cc7ffffc7f

def z737 : W := mkw 0x14ffdeff7e000a8a 0xfdffffffff000f8f

def z738 : W := mkw 0x00ec00ea86940120 0x7bfc00ff87fc03f0

def z739 : W := mkw 0x04ff9cee28000000 0x74fffffff8000000

def z740 : W := mkw 0x00eecaff70000000 0x74fffffff8000000

def z741 : W := mkw 0x81197359c96ee5e9 0x80ffe7f39ffd8f83

def z742 : W := mkw 0x941bdeff7860d455 0xffbbfffffce3fc7f

def z743 : W := mkw 0x00004a1560001014 0x7644ff3fe0007070

def z744 : W := mkw 0x92084afff8241f75 0x910000fff8000fff

def z745 : W := mkw 0x14ffdeff78010002 0xf4fffffff8018003

def z746 : W := mkw 0x01006b15e10e31bc 0x0b000000631e73fc

def z747 : W := mkw 0x14ffde5f78000000 0x64ffff0ff8000000

def z748 : W := mkw 0x14ffdeff78201454 0x7ffffffffce27c7c

def z749 : W := mkw 0x09113904a7dff1bc 0x7fbb180c67fff3fc

def z750 : W := mkw 0x8019184c2860d455 0xffff18fffce3fc7f

def z751 : W := mkw 0x14ffdeff7840c000 0x74fffffffce18000

def z752 : W := mkw 0x04f7b500014ae000 0x6effff0007fff000

def z753 : W := mkw 0x14e6c6b356900000 0x6afce73387fc0000

def z754 : W := mkw 0x00e6a100079b2000 0x6effff0007fff000

def z755 : W := mkw 0x02ec00ea96b40f62 0xfbfc00ff9ffc0ff3

def z756 : W := mkw 0x0cf7b5a207dbe000 0x6effff3387fff000

def z757 : W := mkw 0x94ffdeff7860d455 0x7ffffffff8e2707c

def z758 : W := mkw 0x14ffdeff78000000 0xf4fffffff803800f

def z759 : W := mkw 0x04f7940006d0c000 0x6effff0007fff000

def z760 : W := mkw 0x94ffdeff7860d455 0xf6fffffffce1fc73

def z761 : W := mkw 0x03e6e3b3d79f2baa 0x0044e733831c0380

def z762 : W := mkw 0x18086bff7fdbe000 0x1a0000fffffff000

def z763 : W := mkw 0x00000a0520000000 0x6444ff0f80000000

def z764 : W := mkw 0x02e4000086b40f60 0x7bfc003f87fc0ff0

def z765 : W := mkw 0x00115a156040c000 0x7effff3fe4e3f000

def z766 : W := mkw 0x833d1b4fa8fcf575 0x223c1f0f80fc7070

def z767 : W := mkw 0x00c2a0a017030a8a 0xdd8300c07f038f8f

def z768 : W := mkw 0x01117b15614af09c 0x0403ff006003f00c

def z769 : W := mkw 0x16ffdeff7eb00e40 0x7ffffffffce00c70

def z770 : W := mkw 0x0e1bb5ea816fef60 0x1503ffff8003fff0

def z771 : W := mkw 0x8119194ca86cf575 0x2238180c00fc7070

def z772 : W := mkw 0x01002904a70f3bbe 0xff8318cc7f1fffff

def z773 : W := mkw 0x0cf7b50007dbe000 0x0ebbff0007fff000

def z774 : W := mkw 0x14e6ceb770001014 0x7f44ff3fe002707c

def z775 : W := mkw 0x14e6e4b257030a8a 0xddc3e0f07f038f8f

def z776 : W := mkw 0x00c04ab560000000 0x74c4ffffe0000000

def z777 : W := mkw 0x01002904a10e31bc 0x0f001800631e73fc

def z778 : W := mkw 0x81113904a94ef1bd 0x8f0318007b1ff3ff

def z779 : W := mkw 0x0cf7b50007dbea8a 0xffffffc07fffff8f

def z780 : W := mkw 0x022c00ea80b40f60 0x7b7c00ff83fc0ff0

def z781 : W := mkw 0x00195a5d68000000 0x747cff3fe0000000

def z782 : W := mkw 0x01c28ba5b60d3b36 0xa2871fcf9c1dfc73

def z783 : W := mkw 0x94ff9e4f2860d455 0x6effff0f84e3f070

def z784 : W := mkw 0x1effdeff7ef1ce40 0x74fffffffce18c00

def z785 : W := mkw 0x04f7deb570000000 0x74fffffff8000000

def z786 : W := mkw 0x91084afff82415fd 0x910000fff8000fff

def z787 : W := mkw 0x00004ab570000000 0x7444fffff8000000

def z788 : W := mkw 0x14f7d6b350000000 0x0447ff3380000000

def z789 : W := mkw 0x00c800e886240f60 0x7bfc00ff87fc0ff0

def z790 : W := mkw 0x08e4210007dbe000 0x6efcff0007fff000

def z791 : W := mkw 0x14ffdeff7e010a02 0xfdffffffff018f83

def z792 : W := mkw 0x943d5e5f6860d455 0xfffffffffce3fc7f

def z793 : W := mkw 0x00c2e1b0570b2a8a 0xdfc3e0f07f1fff8f

def z794 : W := mkw 0x01004a156000109c 0x7444ff3fe000000c

def z795 : W := mkw 0x00084a5d60000000 0x74fcffffe0000000

def z796 : W := mkw 0x14e6c6b350000a8a 0x9144e7f3f8000f8f

def z797 : W := mkw 0x00004a1560000000 0x74c7fffff8000000

def z798 : W := mkw 0x0000200001020088 0xdd8300c07f038f8f

def z799 : W := mkw 0x06ee84ea86b40f60 0x7bfce7ff87fc0ff0

def z800 : W := mkw 0x8019184c2860d455 0x8fbb18c07ce3fc7f

def z801 : W := mkw 0x14ffdeff7840c000 0x74fffffff803f000

def z802 : W := mkw 0x0cf7b50007dbe000 0x7fffffc007fffc00

def z803 : W := mkw 0x94ffdeff7840d015 0xfefffffffce3f00f

def z804 : W := mkw 0x8019184c2860d455 0xffffffcc7ce3fc7f

def z805 : W := mkw 0x14ffdeff7e000a00 0xfdffffffff038f8f

def z806 : W := mkw 0x8300210087fefffd 0x8b00000007ffffff

def z807 : W := mkw 0x14ffd6fb58000000 0x007ce73380000000

def z808 : W := mkw 0x00004a1560000000 0x2044ff3f80000000

def z809 : W := mkw 0x1413de1578000000 0x1403ff3ff8000000

def z810 : W := mkw 0x953d1f4fa86cf575 0x223c1f0f80fc7070

def z811 : W := mkw 0x0c13b500014be000 0x6effff0007fff000

def z812 : W := mkw 0x00c2e1b0570b2a8a 0xddc7e7f07f1f8f8f

def z813 : W := mkw 0x0002e01057030a8a 0xdd83e0c07f038f8f

def z814 : W := mkw 0x08c2e1b0579b2a8a 0xddc3e0f07f1f8f8f

def z815 : W := mkw 0x00c2c0b056000a00 0xddc3e0f07f038f8f

def z816 : W := mkw 0x0cf7b50007dbe000 0xeeffffc01ffffc03

def z817 : W := mkw 0x00c2e1b0570b2a8a 0xddc3fff07f03ff8f

def z818 : W := mkw 0x14ff9e4f28000000 0x74ffffcff8000000

def z819 : W := mkw 0x00e6e0b057030a8a 0xfdffe0f07f038f8f

def z820 : W := mkw 0x00115a1568000000 0x7447ff3ff8000000

def z821 : W := mkw 0x143fde5f78000000 0x74bfffcff8000000

def z822 : W := mkw 0x8900210087fff5fd 0x8b00000007ffffff

def z823 : W := mkw 0x14f7deb778000000 0x64ffff33f8000000

def z824 : W := mkw 0x14fd5eff68000000 0x74fcffffe0000000

def z825 : W := mkw 0x0cf7b50007dbe000 0x6afcff0007fc7000

def z826 : W := mkw 0x14ffdeff78000000 0x70fcffff80000000

def z827 : W := mkw 0x03084afff0241ffe 0x910000fff8000fff

def z828 : W := mkw 0x01002100810e31bc 0x8b000000071fffff

def z829 : W := mkw 0x00113100014ae000 0x6e7cff0003fe7000

def z830 : W := mkw 0x00c2e2b157030a8a 0xddc7e7f3ff038f8f

def z831 : W := mkw 0x82f518a6aed4db35 0x84471833fb1ff38f

def z832 : W := mkw 0x0cf7b50007dbea8a 0x6effff0007fff380

def z833 : W := mkw 0x01082148812e35fc 0x7bb800cc07fe7ffc

def z834 : W := mkw 0x0000421140000000 0x5444e733e0000000

def z835 : W := mkw 0x82ec00ea8eb40f61 0xfbfc00ff9ffc0ff3

def z836 : W := mkw 0x01002100810e31bc 0x01000000000273fc

def z837 : W := mkw 0x14eeceff78000000 0x70fce7fff8000000

def z838 : W := mkw 0x14ffdeff78000000 0x14bbfffff8000000

def z839 : W := mkw 0x14c2e6b157030a8a 0xddc3e7f07f038f8f

def z840 : W := mkw 0x8cf7b5000fdbe001 0xeeffff001ffff003

def z841 : W := mkw 0x14eec6fb50000000 0x00fce7f380000000

def z842 : W := mkw 0x01e42100879e31bc 0x6bfc000007fe73fc

def z843 : W := mkw 0x14ffd6fb58000000 0x64fffff398000000

def z844 : W := mkw 0x0cf7b5a017dbea02 0xffffffc07ffffc0f

def z845 : W := mkw 0x00ec42fb40000000 0x70fce7ff80000000

def z846 : W := mkw 0x00c2a00007030a8a 0xddc3e0c07f038f8f

def z847 : W := mkw 0x8019184c2860d455 0x9bbb00cc7ce3fc7f

def z848 : W := mkw 0x09002100879f31bc 0x0b000000031e73fc

def z849 : W := mkw 0x14ffdeff78001014 0xfffffffffc03fc7f

def z850 : W := mkw 0x02ec00ea86b50f62 0xfbfc00ff87fd8ff3

def z851 : W := mkw 0x14e6ceb770000000 0x2044ff3f80000000

def z852 : W := mkw 0x00c2e0b051030a8a 0xd5c3e0f078038f8f

def z853 : W := mkw 0x94ffdeff7860d455 0x227cff3f80e07070

def z854 : W := mkw 0x02e6e0b257930a8a 0xddc3e0f07f038f8f

def z855 : W := mkw 0x14f7d6b35040c000 0x6effff3384e3f000

def z856 : W := mkw 0x14ff9e4f28000000 0x207cff0f80000000

def z857 : W := mkw 0x94ffdeff7860c441 0x74fffffff8e00000

def z858 : W := mkw 0x0cf7b5a017dbe000 0x6effffc01ffff000

def z859 : W := mkw 0x10084a5f68000000 0x7444ff3fe0000000

def z860 : W := mkw 0x80dbf8fc7f63dedf 0x2278f83c03e073f0

def z861 : W := mkw 0x14f7deb778000000 0x54c7fff3f8000000

def z862 : W := mkw 0x14ffdeff78000a8a 0x74fffffff8000380

def z863 : W := mkw 0x02ec00ea86b40f60 0x7ffc18ff87fe7ff0

def z864 : W := mkw 0x04e6ce1560000000 0x7444ff3fe0000000

def z865 : W := mkw 0x0cf7b5a007dbea00 0x6effffc007fffc00

def z866 : W := mkw 0x0002e0b057030a8a 0x9d03e0f07f038f8f

def z867 : W := mkw 0x14dbdeff78000000 0x54c3fffff8000000

def z868 : W := mkw 0x14ffdeff7e010a02 0xfdfffffffc038c0f

def z869 : W := mkw 0x14ffdeff78000088 0x75fffffff800038c

def z870 : W := mkw 0x8a00210087ffff75 0x8b00000007ffffff

def z871 : W := mkw 0x9513ff15794af09d 0x8403ff007803f00f

def z872 : W := mkw 0x00c2c0b056010a8a 0xd5c3e0f07c018f8f

def z873 : W := mkw 0x1402ce1570000000 0x7444ff3fe0000000

def z874 : W := mkw 0x020800ea86b40f60 0x7bb800ff87fc0ff0

def z875 : W := mkw 0x143d1e4f28000000 0x647cff0f80000000

def z876 : W := mkw 0x0b00210087fffffc 0x0b00000007fffffc

def z877 : W := mkw 0x84ffde5d6860d455 0xfffffffffce3fc7f

def z878 : W := mkw 0x0c37950000d8e000 0x263fff0000fc7000

def z879 : W := mkw 0x14ffdeff78000000 0x64ffff3f80000000

def z880 : W := mkw 0x943fde5f7860d455 0xa63fff0ff8e3f07f

def z881 : W := mkw 0x8219184ea864d575 0x2238180f80e07070

def z882 : W := mkw 0x1cffdeff7ed1ca02 0xf4fffffffce18c03

def z883 : W := mkw 0x0000000000000000 0x7444ff3f80000000

def z884 : W := mkw 0x022c004a86b40f60 0x7b7c003f87fc0ff0

def z885 : W := mkw 0x94ffdeff7860d455 0xf4fffffffce3fc0f

def z886 : W := mkw 0x01002100812e35fc 0x0b00000007fe7ffc

def z887 : W := mkw 0x01113100814ef1bc 0x6fbb180007fff3fc

def z888 : W := mkw 0x00e6e0b257030a8a 0xddc7e0f3ff038f8f

def z889 : W := mkw 0x0cf7b50007dbe000 0x04ffff0007fff000

def z890 : W := mkw 0x04f7b500079a2000 0x6effff0007fe7000

def z891 : W := mkw 0x00e400a086940b20 0x7bfc00ff87fc0ff0

def z892 : W := mkw 0x100042b350000000 0x0044e73380000000

def z893 : W := mkw 0x0cf7950000d8e000 0x6effff0004fff000

def z894 : W := mkw 0x01002100810e31bc 0xdf8300c07f1fffff

def z895 : W := mkw 0x0900210087dff134 0x0a00000007fff070

def z896 : W := mkw 0x022ee05ad1b705ea 0xa63fe00ff8ff807f

def z897 : W := mkw 0x94ffdeff7860dedf 0xfffffffffce3ffff

def z898 : W := mkw 0x03ec6bff67ba3edc 0x04b8ffc064e27c0c

def z899 : W := mkw 0x141bdeff78000000 0x74bbfffff8000000

def z900 : W := mkw 0x02ec00ea86b40f60 0x22fc00ff87fc0ff0

def z901 : W := mkw 0x01c021a0870e3bbc 0x5bc000f0071e7ffc

def z902 : W := mkw 0x08ec21ea07dbe000 0x7afc00ff87fff000

def z903 : W := mkw 0x94ffdeff7860d455 0x7ffffffffce07c70

def z904 : W := mkw 0x0000421140000000 0x6444ff3380000000

def z905 : W := mkw 0x1cffdeff7ed1c000 0x7efffffffce3f000

def z906 : W := mkw 0x8019184c2860d455 0xa6bb18cc7ce3fc7f

def z907 : W := mkw 0x0cf7b50007dbe000 0x267fff0003fff000

def z908 : W := mkw 0x96ff94ea1ef0ce41 0x80bb00c01ce18c03

def z909 : W := mkw 0x02ec00ea86b40f60 0xfbff00ff9ffd8ff3

def z910 : W := mkw 0x000040b050000a8a 0x950300f078038f8f

def z911 : W := mkw 0x94191e4d2860d455 0xffbb1fcc7ce3fc7f

def z912 : W := mkw 0x0308294ca7be3ffc 0x7fb818cc67fe7ffc

def z913 : W := mkw 0x15ffb5ea990e31bc 0x0bbb00c01b1e73fc

def z914 : W := mkw 0x1424461340000000 0x0044e73380000000

def z915 : W := mkw 0x0002e0105103008a 0xddc3e0f07f038f8f

def z916 : W := mkw 0x14e6c6b356010a02 0x80c7e7f39c018c03

def z917 : W := mkw 0x03ec21ea87be3ffc 0x0bb800c007fe7ffc

def z918 : W := mkw 0x0cf7b50001dbe000 0x66ffff0000fff000

def z919 : W := mkw 0x00242100019a2000 0x6e7cff0003fe7000

def z920 : W := mkw 0x14eec6fb58000000 0x0044e7f398000000

def z921 : W := mkw 0x0cf7950006d9e000 0x66ffff0004fdf000

def z922 : W := mkw 0x0eff94ea16f1ce42 0x80bb00c01ce18c03

def z923 : W := mkw 0x12ec00ea9eb40f60 0x7bfc00ff9ffc0ff0

def z924 : W := mkw 0x0208004886b40f60 0x7bfc00ff87fc0ff0

def z925 : W := mkw 0x10c2e2b357030a8a 0xddc3e0f3ff038f8f

def z926 : W := mkw 0x01002100810e31bc 0x7f44ff3f831e73fc

def z927 : W := mkw 0x14eeceff78000000 0x54c7e7fff8000000

def z928 : W := mkw 0x01006b15e10e31bc 0x1544ff3fe31e73fc

def z929 : W := mkw 0x00f5310007dae000 0x6effff0007fff000

def z930 : W := mkw 0x0ce6e5b0579b2a8a 0xffc7fff07f1fff8f

def z931 : W := mkw 0x002c4a5f60000000 0x747cff3fe0000000

def z932 : W := mkw 0x01002100810e31bc 0x5b400030031e73fc

def z933 : W := mkw 0x94ffdeff7860d455 0xf7fffffff8e07c7f

def z934 : W := mkw 0x1cf7b5a217dbe000 0x6effff0007fff000

def z935 : W := mkw 0x14e6c6b356900000 0x0044e733831c0000

def z936 : W := mkw 0x022c004a80b40560 0x7bfc00ff87fc0ff0

def z937 : W := mkw 0x14ffdeff7e000a00 0x74fffffffb000380

def z938 : W := mkw 0x00c2e0b057030a8a 0x91c3e0f07f018f8f

def z939 : W := mkw 0x0c3555b050d8ea8a 0xb33c1ff078fc7f8f

def z940 : W := mkw 0x14ffdeff7eb00440 0x7ffffffffffc0c70

def z941 : W := mkw 0x01006110c10e31bc 0x1b000030631e73fc

def z942 : W := mkw 0x02ec4aff66b00e40 0x74fcffffe4e00c00

def z943 : W := mkw 0x14ffdeff78000000 0x10ffe7fff8000000

def z944 : W := mkw 0x0cf7b5a007dbea00 0xfffffff07fffff8f

def z945 : W := mkw 0x0000000080040120 0x7bfc003f87fc03f0

def z946 : W := mkw 0x04ffd4fa50000000 0x74fffffff8000000

def z947 : W := mkw 0x1cffdeff7ed1c000 0x7efffffffffd8000

def z948 : W := mkw 0x81193148896ef5fd 0x8bbb00c01fffffff

def z949 : W := mkw 0x8119394ca96ef5fd 0x2b38180c03fe73fc

def z950 : W := mkw 0x14e6c6b350000000 0x7044e73f80000000

def z951 : W := mkw 0x143d5e5f68000000 0x243cff0fe0000000

def z952 : W := mkw 0x143fde5f78000000 0x203cff0f80000000

def z953 : W := mkw 0x1cf7d6b356d1c000 0x00ffe73384e18000

def z954 : W := mkw 0x022c004a80b40560 0x227c003f83fc03f0

def z955 : W := mkw 0x02ec00ea86b40f60 0x7b7c003f83fc03f0

def z956 : W := mkw 0x0c35350001dae000 0x227cff0003fc7000

def z957 : W := mkw 0x01006b15e10e31bc 0x7ffcff3fe7fe73fc

def z958 : W := mkw 0x1613de15feb40f60 0x0f03ff007ffc0ff0

def z959 : W := mkw 0x1cffdeff7e910000 0x74fffffff8000000

def z960 : W := mkw 0x14ff9eef28000000 0x74ffffff80000000

def z961 : W := mkw 0x14ffdeff78000000 0x7dfffffffc000c00

def z962 : W := mkw 0x00ec00ea80240560 0x7bfc00ff87fc0ff0

def z963 : W := mkw 0x0cc2e5b0570b2a8a 0xddc3e7f07f038f8f

def z964 : W := mkw 0x00c2cab576010a02 0xf4c7fffffc018c03

def z965 : W := mkw 0x14ffdeff78000000 0x747cff3fe0000000

def z966 : W := mkw 0x00c2e0b057030a8a 0x84c3e0f07f038f8f

def z967 : W := mkw 0x00004a1560000000 0x7f44ff3fe0000070

def z968 : W := mkw 0x02ec00ea86b40f60 0x11fc00ff87fc0ff0

def z969 : W := mkw 0x00c2e0b057030a8a 0x998300f07f038f8f

def z970 : W := mkw 0x00ec00ea00000000 0x74fcffff80000000

def z971 : W := mkw 0x04e6e4b057030a8a 0xddc7e7f07f038f8f

def z972 : W := mkw 0x0800210087dfe120 0x0b00000007fff3f0

def z973 : W := mkw 0x943d5e5f6860d455 0x7f7cff3fe0e2707c

def z974 : W := mkw 0x14ffdeff78001014 0x76fffffff8007070

def z975 : W := mkw 0x14ffdeff7e900a00 0x7ffffffffffc0f80

def z976 : W := mkw 0x00c2c0b056010a8a 0xdd8300f07c038f8f

def z977 : W := mkw 0x8108294ca92e35fd 0x9b0000cc7b1e7fff

def z978 : W := mkw 0x8e3d1d4ea8fcf575 0x223c1f0f80fc7070

def z979 : W := mkw 0x01002100870f3bbe 0x0b000000031e73fc

def z980 : W := mkw 0x0ef7b5a207dbea00 0x6effff0007fff000

def z981 : W := mkw 0x0c37b50001dbe000 0x6e7fff0003fff000

def z982 : W := mkw 0x00c04ab566000a00 0x7dc4ffffe7000f80

def z983 : W := mkw 0x16ffdeff7eb10e42 0xf4fffffffce18c03

def z984 : W := mkw 0x00c2e0b057030a8a 0xffc7e0f07f1f8f8f

def z985 : W := mkw 0x800800480060d455 0xffbb00cc7ce3fc7f

def z986 : W := mkw 0x1437de1778000000 0x0407ff03f8000000

def z987 : W := mkw 0x14f7deb778000000 0x0044ff3380000000

def z988 : W := mkw 0x02ec00ea86b40f60 0x1bb800ff87fc0ff0

def z989 : W := mkw 0x01002100814ef1bc 0x0b00000007fff3fc

def z990 : W := mkw 0x01002100810e31bc 0x02000000031c73f0

def z991 : W := mkw 0x0200210087be2f60 0x0b00000007fe7ff0

def z992 : W := mkw 0x141bde5f78000000 0x0403ff0ff8000000

def z993 : W := mkw 0x01084a5de02415fc 0x110000ffe0000ffc

def z994 : W := mkw 0x0ce6e5b0579b2a8a 0xffffe7f07fff8f8f

def z995 : W := mkw 0x94ffdeff78201455 0xfffffffff8027c7f

def z996 : W := mkw 0x04f794a200000000 0x64ffff3380000000

def z997 : W := mkw 0x000060b057030a8a 0xdd8300f07f038f8f

def z998 : W := mkw 0x14ffdeff7e010a02 0x74fffffff8000000

def z999 : W := mkw 0x14eeceff70000000 0x74fcffffe0000000

def z1000 : W := mkw 0x0a00210087ffefea 0x8b00000007ffffff

def z1001 : W := mkw 0x90191a4f2860d455 0xffbb18cffce3fc7f

def z1002 : W := mkw 0x14e6ceb778000000 0x0044e733f8000000

def z1003 : W := mkw 0x01006b15e10e31bc 0xff44ff3fe71fffff

def z1004 : W := mkw 0x94ffdeff7840d015 0xfffffffff803f07f

def z1005 : W := mkw 0x00c280a016010a02 0xddc300f07f038f8f

def z1006 : W := mkw 0x14ffdeff78000a8a 0xfdfffffffc038f8f

def z1007 : W := mkw 0x02ec00ea80b40560 0x7bfc00ff83fc03f0

def z1008 : W := mkw 0x10004a1578000000 0x7444ff3ff8000000

def z1009 : W := mkw 0x0cf7b50007dbe08a 0xeeffff0007fff00f

def z1010 : W := mkw 0x94ffdeff7e60de55 0xffffffffffe3ffff

def z1011 : W := mkw 0x143d3e4f2f030a8a 0xa93c1f0f87038f8f

def z1012 : W := mkw 0x00e442b340000000 0x0044e73380000000

def z1013 : W := mkw 0x1cf7b5001fdbe000 0x6effff001ffff000

def z1014 : W := mkw 0x00115a1560000000 0x74ffff3fe0000000

def z1015 : W := mkw 0x0cf7950000d8e000 0x227cff0000fc7000

def z1016 : W := mkw 0x04f79e0520000000 0x64ffff0f80000000

def z1017 : W := mkw 0x00002100810e2120 0x0b000000031e73f0

def z1018 : W := mkw 0x0cf7b50007dbe000 0x7effffc07ffff000

def z1019 : W := mkw 0x01006b15e10e31bc 0xff47ff3ffb1ff3ff

def z1020 : W := mkw 0x0a19314887ffef60 0x7fbb18cc07fffff0

def z1021 : W := mkw 0x0c13b50007dbe000 0x6ebbff0007fff000

def z1022 : W := mkw 0x14e6c6b350000000 0x50c4e7f380000000

def z1023 : W := mkw 0x14ffdeff78900000 0x76fffffff8fc0000

def z1024 : W := mkw 0x13084afff8241ffc 0x110000fff8000ffc

def z1025 : W := mkw 0x01002904a10e31bc 0x2b00180c031e73fc

def z1026 : W := mkw 0x94ffdeff7860c441 0xfffffffffce18c73

def z1027 : W := mkw 0x01002100810e31bc 0x02000000001e707c

def z1028 : W := mkw 0x16ffdeff78200e40 0x74fffffff8000c00

def z1029 : W := mkw 0x8019184c2860d455 0xfffb18fc7fe3ffff

def z1030 : W := mkw 0x10ec4aff78000000 0x74fcfffff8000000

def z1031 : W := mkw 0x00004a1560000000 0x1400ff3fe0000000

def z1032 : W := mkw 0x00fd5aff68000000 0x74fffffff8000000

def z1033 : W := mkw 0x16ee84ea96b40f60 0x7bfc00ff87fc0ff0

def z1034 : W := mkw 0x943fde5f7860d455 0xffbfffcffce3fc7f

def z1035 : W := mkw 0x00004a1560000000 0x1044e73fe0000000

def z1036 : W := mkw 0x0c37b50001dbe000 0x223cff0000fc7000

def z1037 : W := mkw 0x0000601047030a8a 0xddc3e0f07f038f8f

def z1038 : W := mkw 0x0cf7b50007dbe000 0x7fffff3007fff380

def z1039 : W := mkw 0x00c2e01047030088 0xddc3e0f07f038f8f

def z1040 : W := mkw 0x81084afdf8241fff 0x910000fff8000fff

def z1041 : W := mkw 0x00c2e0b057030a8a 0x8d83e0c07f038f8f

def z1042 : W := mkw 0x94ffd6fb5860c441 0x80ffe7f39ce18c03

def z1043 : W := mkw 0x01002b05a10e3134 0x7f44ff3f831e73f0

def z1044 : W := mkw 0x10004ab770000000 0x7444ff3fe0000000

def z1045 : W := mkw 0x0cf7b50007dbe088 0x6fffff0007fff38c

def z1046 : W := mkw 0x14ffdeff78001014 0x74fffffff802700c

def z1047 : W := mkw 0x14ffde5f68000000 0x74ffff3fe0000000

def z1048 : W := mkw 0x94ffdeff7860c441 0xfdfffffffce38c0f

def z1049 : W := mkw 0x15ffdeff7800109c 0x74fffffff800000c

def z1050 : W := mkw 0x0cf7b50007dbe000 0x7effff3f87fff000

def z1051 : W := mkw 0x14eeceff78000000 0x0044e73f80000000

def z1052 : W := mkw 0x81002100816ef5fd 0x0b00000003fe73fc

def z1053 : W := mkw 0x02ee80ea86b40f60 0x7fffe0ff87fc0ff0

def z1054 : W := mkw 0x0cf7b5a007dbea8a 0xfffffff007ffff8f

def z1055 : W := mkw 0x0ee6e5b2d79f2baa 0x0044e733831c0380

def z1056 : W := mkw 0x14f7960300000000 0x64ffff0380000000

def z1057 : W := mkw 0x00e44ab760000000 0x7444ff3fe0000000

def z1058 : W := mkw 0x1413deb778000000 0x0403ff33f8000000

def z1059 : W := mkw 0x0002e0b051030a8a 0xdd83e0f07c038f8f

def z1060 : W := mkw 0x00004a15e0041134 0x7f44ff3fe31e73fc

def z1061 : W := mkw 0x14244e1760000000 0x7444ff3fe0000000

def z1062 : W := mkw 0x14e6c6b356000a00 0x59c4e7f387000f80

def z1063 : W := mkw 0x00006110c10e21a8 0x7f44ff3fe31e73fc

def z1064 : W := mkw 0x14ffdeff7e010000 0x74fffffffc018000

def z1065 : W := mkw 0x14eeceff78000000 0x7444fffff8000000

def z1066 : W := mkw 0x94ffdeff7840d015 0x74fffffff8007000

def z1067 : W := mkw 0x8019184c2860d455 0x95bb18cc7ce3fc7f

def z1068 : W := mkw 0x16ffdeff7e900a00 0x74fffffff8000000

def z1069 : W := mkw 0x010061b0d10e3bbe 0x9b0000f07b1e7fff

def z1070 : W := mkw 0x16eec6fb56b00e40 0x00fce7f384e00c00

def z1071 : W := mkw 0x94ffdeff7ef0d455 0xfffffffffffffc7f

def z1072 : W := mkw 0x14e6c6b350000000 0x60fce73380000000

def z1073 : W := mkw 0x140aceff78000000 0x1000e7fff8000000

def z1074 : W := mkw 0x94ffdeff7860d455 0xf5fffffff803fc7f

def z1075 : W := mkw 0x143f9e4f28000000 0x243fff0f80000000

def z1076 : W := mkw 0x0811310007dbe000 0x6effff0007fff000

def z1077 : W := mkw 0x0cf7b50007dbe000 0xefffff0007fffc0f

def z1078 : W := mkw 0x00c2e0b057030a8a 0xffc3f8f07f03ff8f

def z1079 : W := mkw 0x80191a4d2860d455 0xffbf1fcffce3fc7f

def z1080 : W := mkw 0x0cf7b50001dae000 0x6effff0003fe7000

def z1081 : W := mkw 0x84ff9cee2860d455 0xfffffffffce3fc7f

def z1082 : W := mkw 0x00004a1560000000 0x7e44ff3fe0027000

def z1083 : W := mkw 0x0cf7950006d8e000 0x6effff0007fc7000

def z1084 : W := mkw 0x01002100810e31bc 0x6f001800031e73fc

def z1085 : W := mkw 0x14ffdeff78000000 0x307cfffff8000000

def z1086 : W := mkw 0x0ce6a500079b2000 0x6efcff0007fe7000

def z1087 : W := mkw 0x01002100870f2baa 0x89000000071f8f8f

def z1088 : W := mkw 0x14ffdeff78000000 0x7efffffffce00000

def z1089 : W := mkw 0x020800ea80240f60 0x7bfc00ff87fc0ff0

def z1090 : W := mkw 0x94ffdeff7840c001 0xf4fffffff8018003

def z1091 : W := mkw 0x0c35350001dae000 0x263cff0000fe7000

def z1092 : W := mkw 0x11006b15f90e31bc 0x7f44ff3ffb1e73fc

def z1093 : W := mkw 0x0cf7b5a007dbea00 0x6effff3007fff380

def z1094 : W := mkw 0x0900210081def1bc 0x0b00000003fe73fc

def z1095 : W := mkw 0x81084a5de82415fd 0x1100003fe00003fc

def z1096 : W := mkw 0x14ffdeff78200440 0x74fffffffce00c00

def z1097 : W := mkw 0x00c2e0b057030a8a 0xfdc7fff07f038f8f

def z1098 : W := mkw 0x00004a1560001014 0x7544ff3fe000007c

def z1099 : W := mkw 0x01002904a10e31bc 0x1b00000c631e73fc

def z1100 : W := mkw 0x14ffdeff78000000 0x20ffffff98000000

def z1101 : W := mkw 0x0a00210087dfeb20 0x0a00000007fff380

def z1102 : W := mkw 0x02ec00ea86b40f60 0x7ffc00ffe7fe0ffc

def z1103 : W := mkw 0x0cf7b50007dbe000 0x66ffff0003fc7000

def z1104 : W := mkw 0x14ffd6fb58000000 0x70ffe7ff98000000

def z1105 : W := mkw 0x00c2cab570000000 0x7444ff3fe0000000

def z1106 : W := mkw 0x8d13ff15694bf09d 0x8403ff007803f00f

def z1107 : W := mkw 0x00c020a007030a8a 0xddc300f07f038f8f

def z1108 : W := mkw 0x0000000000000a8a 0xdd8300c07c038f8f

def z1109 : W := mkw 0x01006b15e10e31bc 0xff44fffffb1e7fff

def z1110 : W := mkw 0x0a002100879f2b20 0x00000000031c0380

def z1111 : W := mkw 0x1ce6e7b3579b2a8a 0xddc7e7f3ff1f8f8f

def z1112 : W := mkw 0x801110000060d455 0xffbb18c07ce3fc7f

def z1113 : W := mkw 0x0008004880240560 0x7b7c003f83fc03f0

def z1114 : W := mkw 0x14ffdeff78000a02 0xf4fffffff8000c03

def z1115 : W := mkw 0x00c2a0a007030a00 0xddc3e0f07f038f8f

def z1116 : W := mkw 0x00ec004886b40560 0x7bfc00ff87fc0ff0

def z1117 : W := mkw 0x14ffdeff7840d014 0x7ffffffffce3f07c

def z1118 : W := mkw 0x81191a4da864d575 0x2238180f80e07070

def z1119 : W := mkw 0x00e6e0b057930a8a 0xddc7e0f07f1f8f8f

def z1120 : W := mkw 0x141bde5d78000000 0x74fffffff8000000

def z1121 : W := mkw 0x01006311c10e21a8 0x7f44ff3f831e73f0

def z1122 : W := mkw 0x01002100810f31be 0x8b000000031ff3ff

def z1123 : W := mkw 0x000060b051020a8a 0xddc3e0f07f038f8f

def z1124 : W := mkw 0x143d5eff78000000 0x747cfffff8000000

def z1125 : W := mkw 0x00c2e0b057030a8a 0xfffbe0f07fe38f8f

def z1126 : W := mkw 0x0000000006000a00 0xdd8300c07f038f8f

def z1127 : W := mkw 0x81117b15694af09d 0x0400ff006002700c

def z1128 : W := mkw 0x14e6860300000000 0x0044e70380000000

def z1129 : W := mkw 0x04e6c61140000000 0x0044e73380000000

def z1130 : W := mkw 0x00c040b056000a8a 0xddc300f07f038f8f

def z1131 : W := mkw 0x1426c61350000000 0x0004e70380000000

def z1132 : W := mkw 0x0002c0b050010a8a 0x910300f078018f8f

def z1133 : W := mkw 0x0002e0b051030a8a 0xdd43e0f07b038f8f

def z1134 : W := mkw 0x14ffdeff78000000 0x7efffffff8027000

def z1135 : W := mkw 0x04f7940000000000 0x74ffff3f80000000

def z1136 : W := mkw 0x0cf7b5a017dbea8a 0xefffffc01fffff8f

def z1137 : W := mkw 0x00c2c2b150000000 0x54c7e7f3f8000000

def z1138 : W := mkw 0x00004a1560000000 0xfdc7fffffc038c0f

def z1139 : W := mkw 0x0300210081be35fc 0x0b00000003fe73fc

def z1140 : W := mkw 0x00c2ca1560000000 0x74c7ff3fe0000000

def z1141 : W := mkw 0x01c2e3b1570b2a8a 0xddc3e7f07f038f8f

def z1142 : W := mkw 0x14ffdeff7e900000 0x74fffffffce00000

def z1143 : W := mkw 0x1d13ff15794bf09c 0x0403ff007803f00c

def z1144 : W := mkw 0x14e6ceb770000000 0x0444ff33e0000000

def z1145 : W := mkw 0x0c35350001dae000 0x6effff0007fff000

def z1146 : W := mkw 0x81006b15e90e31bd 0xff44ff3ffb1e73ff

def z1147 : W := mkw 0x01006b15e10e31bc 0x7b44ff3f831c73f0

def z1148 : W := mkw 0x04ffdeff60000000 0x74ffffffe0000000

def z1149 : W := mkw 0x01002100810e31bc 0x5f000000631e73fc

def z1150 : W := mkw 0x06f7940086b40f60 0x6fffff0007fc0ff0

def z1151 : W := mkw 0x14ffdeff78000000 0x7ffffffff8000070

def z1152 : W := mkw 0x04ffde5d68000000 0x74fffffff8000000

def z1153 : W := mkw 0x14ffdeff78001014 0x75fffffff800007c

def z1154 : W := mkw 0x04ff944a00000000 0x64ffff0f80000000

def z1155 : W := mkw 0x0002ca1570000000 0x7447ff3ff8000000

def z1156 : W := mkw 0x14e6c6b350000000 0x44c7e73380000000

def z1157 : W := mkw 0x02ec00ea86b40f60 0x2b7c003f87fc0ff0

def z1158 : W := mkw 0x83084affe8241ffd 0x910000fff8000fff

def z1159 : W := mkw 0x00e44a1566900000 0x7efcff3fe7fc0000

def z1160 : W := mkw 0x0df7b50087dff1bc 0x0bbb000007fff3fc

def z1161 : W := mkw 0x14ffdeff78000000 0x7dfffffffb000380

def z1162 : W := mkw 0x14ffdeff7840c000 0xfffffffffce3fc0f

def z1163 : W := mkw 0x14d3deb578000000 0x74c7fffff8000000

def z1164 : W := mkw 0x14ffdeff78200440 0xfffffffffce38c7f

def z1165 : W := mkw 0x94ffdeff7840d015 0xfdfffffffc03fc0f

def z1166 : W := mkw 0x04f7de156040d014 0x7fffff3fe4e3f07c

def z1167 : W := mkw 0x00c2e0b057030a8a 0xfdc7e0ffff038f8f

def z1168 : W := mkw 0x14e6c6b350000a8a 0x0044e73380000380

def z1169 : W := mkw 0x01002100870f31bc 0x0b000000071ff3fc

def z1170 : W := mkw 0x14ffdeff78000000 0x7efffffffb1c0000

def z1171 : W := mkw 0x94ffdeff78200441 0xf4fffffff8000c03

def z1172 : W := mkw 0x00e6e0b057930a8a 0xddfbe0f07fe38f8f

def z1173 : W := mkw 0x14f7d6b350000000 0x00ffe73380000000

def z1174 : W := mkw 0x94ffdeff7e61de57 0xfffffffffce3fc7f

def z1175 : W := mkw 0x0de6e7b1d79f2baa 0x0044e733831c0380

def z1176 : W := mkw 0x8119394caf6fffff 0xffbb18cc7fffffff

def z1177 : W := mkw 0x0cf7b50007dbe000 0x7fffff0c07fff070

def z1178 : W := mkw 0x0eff94ea06f1ce40 0x74ffffff84e18c00

def z1179 : W := mkw 0x001910480060c440 0xffbb18cc7ce3fc7f

def z1180 : W := mkw 0x01c2a1a0970f3bbe 0x8b8300c01f1fffff

def z1181 : W := mkw 0x14ffdeff78000000 0xf4fffffffc018c03

def z1182 : W := mkw 0x14ffdeff7ed0c000 0x7efffffffffff000

def z1183 : W := mkw 0x02ec00ea86b40f60 0xfbfc00ff87ff8fff

def z1184 : W := mkw 0x14f7de1578000000 0x74ffff3ff8000000

def z1185 : W := mkw 0x10195aff78000000 0x74fffffff8000000

def z1186 : W := mkw 0x02ec004a86b40560 0x7bfc003f87fc03f0

def z1187 : W := mkw 0x0000421140000000 0x7044e73f80000000

def z1188 : W := mkw 0x000040b050000a8a 0x918300f07c018f8f

def z1189 : W := mkw 0x01002100810e21a8 0x0a000000031e7380

def z1190 : W := mkw 0x94ff9e4f2860d455 0xffffffcffce3fc7f

def z1191 : W := mkw 0x14ffdeff7e010a8a 0xf5fffffffc018f8f

def z1192 : W := mkw 0x00004a1560001014 0x7444ff3fe002700c

def z1193 : W := mkw 0x00c2c0b050000a8a 0xddc3e0f07c038f8f

def z1194 : W := mkw 0x8d3d1f4da8fcf575 0x223c1f0f80fc7070

def z1195 : W := mkw 0x80115a156840d015 0xf447ff3ff803f00f

def z1196 : W := mkw 0x14ffdeff78000000 0xf5fffffff8000c0f

def z1197 : W := mkw 0x01002100810e31bc 0x00000000031e738c

def z1198 : W := mkw 0x0cf7b50007dbe000 0x6e7cff0003fe7000

def z1199 : W := mkw 0x14ffdeff7860c440 0x7ffffffffce3fc70

def z1200 : W := mkw 0x143d5e5f68000000 0x74fffffff8000000

def z1201 : W := mkw 0x0effb5ea87ffef60 0x0bbb00c007fffff0

def z1202 : W := mkw 0x02ec00ea86b40f60 0x337c00ff83fc0ff0

def z1203 : W := mkw 0x94ffdeff78201455 0x74fffffff8000070

def z1204 : W := mkw 0x0a00210087ffe560 0x0a00000007fff070

def z1205 : W := mkw 0x01002100810e3134 0x0a000000031e7070

def z1206 : W := mkw 0x8219184ca8f4d575 0x2238180c00fc7070

def z1207 : W := mkw 0x10cacaff78000000 0x74c7fffff8000000

def z1208 : W := mkw 0x01006b15e10e31bc 0x6e44ff3f831e73f0

def z1209 : W := mkw 0x04355e1560000000 0x747cff3fe0000000

def z1210 : W := mkw 0x01006b15e10e31bc 0x2b44ff3f831e73fc

def z1211 : W := mkw 0x9413de157840d015 0xff47ff3ff803f07f

def z1212 : W := mkw 0x14eec6fb50200440 0x7bfce7ff84e00c70

def z1213 : W := mkw 0x0cf7b50007dbe000 0x22ffff0007fdf000

def z1214 : W := mkw 0x00e6e1b0579b2a8a 0xfffffff07fffff8f

def z1215 : W := mkw 0x14ffdeff78000000 0x247fff3ff8000000

def z1216 : W := mkw 0x02ee80ea96b50f62 0x7bfc00ff87fc0ff0

def z1217 : W := mkw 0x03002100812e3ffc 0x0b000000031e7ffc

def z1218 : W := mkw 0x14ffdeff7e900000 0x74fffffffb1c0000

def z1219 : W := mkw 0x80dbdafd7860d455 0xfffffffffce3fc7f

def z1220 : W := mkw 0x02e400a286940b20 0x7bfc003f87fc03f0

def z1221 : W := mkw 0x9cffdeff7ef1d455 0xfffffffffce3fc7f

def z1222 : W := mkw 0x1eff94ea1ef1ce40 0x00bb00c01ce18c00

def z1223 : W := mkw 0x14e6c6b350000000 0x5444e733e0000000

def z1224 : W := mkw 0x8113fb15794bf09f 0x8403ff007803f00f

def z1225 : W := mkw 0x80004a156060d455 0xff44ff3fe4e3fc7f

def z1226 : W := mkw 0x03084a5fe02415fc 0x1100003fe00003fc

def z1227 : W := mkw 0x14e6c6b356000a00 0x0044e73383000380

def z1228 : W := mkw 0x0a00210087bf2f60 0x0b00000007fc0ff0

def z1229 : W := mkw 0x90195aff7860d455 0xfffffffffce3fc7f

def z1230 : W := mkw 0x14ffd6fb50000000 0x74ffffff80000000

def z1231 : W := mkw 0x80195a5d6860d455 0x767cff3fe0e07070

def z1232 : W := mkw 0x94ffdeff7860c441 0xfefffffffce3fc03

def z1233 : W := mkw 0x14f7d6b358000000 0x0047e73398000000

def z1234 : W := mkw 0x10084aff78000000 0x1400fffff8000000

def z1235 : W := mkw 0x14ffdeff78200440 0x75fffffff8000c70

def z1236 : W := mkw 0x963d1e4fa8f4d575 0x223c1f0f80fc7070

def z1237 : W := mkw 0x0cf7b50007dbe000 0x7fffff0067fff00c

def z1238 : W := mkw 0x14eec6fb50000000 0x74ffe7fff8000000

def z1239 : W := mkw 0x94ffdeff7860d455 0xf5fffffffce18c7f

def z1240 : W := mkw 0x1ce6c6b356910000 0x0044e73380000000

def z1241 : W := mkw 0x1cffdeff7841c000 0x74fffffff8018000

def z1242 : W := mkw 0x14ffdeff78000000 0x1447fffff8000000

def z1243 : W := mkw 0x14ff9eef38000000 0x64ffffcf98000000

def z1244 : W := mkw 0x00004a1560000088 0x7544ff3fe000038c

def z1245 : W := mkw 0x01002100810e31bc 0x6b440000031e73fc

def z1246 : W := mkw 0x94ffdeff78201455 0xfffffffffce00c7f

def z1247 : W := mkw 0x94ffdeff7e61ce43 0xf4fffffffce18c03

def z1248 : W := mkw 0x00c2e0b057030a8a 0xffc3e0fc7f038fff

def z1249 : W := mkw 0x1413de1578000000 0x0447ff33f8000000

def z1250 : W := mkw 0x0cf7b50007dbe000 0xeeffff007ffff00f

def z1251 : W := mkw 0x022c00ea86b40f60 0x3b3c00ff87fc0ff0

def z1252 : W := mkw 0x01006b15e10e31bc 0x7fc7ff3fe71ff3fc

def z1253 : W := mkw 0x81002100812e35fd 0x8b000000031e7fff

def z1254 : W := mkw 0x00c2e0b057030a8a 0x9583e0f07c038f8f

def z1255 : W := mkw 0x00002100010a2000 0x6efcff0007fe7000

def z1256 : W := mkw 0x0c35350007dbe000 0x6e7cff0007fff000

def z1257 : W := mkw 0x14e6c6b350000000 0x00c7e7f398000000

def z1258 : W := mkw 0x0cf7b5a007dbe000 0x7efffff007fff000

def z1259 : W := mkw 0x0024000080940120 0x7b7c003f83fc03f0

def z1260 : W := mkw 0x81002100814ef1bd 0x8b000000031ff3ff

def z1261 : W := mkw 0x0ce6e4b057930a8a 0xddc3e0f07f038f8f

def z1262 : W := mkw 0x14f7d6b350000000 0x74fffff3f8000000

def z1263 : W := mkw 0x8eff94ea0ef1ce41 0x80bb00c01ce18c03

def z1264 : W := mkw 0x1413de1578000000 0x2407ff0ff8000000

def z1265 : W := mkw 0x14ffdeff78000a00 0x75fffffff8000f80

def z1266 : W := mkw 0x90084aff78201455 0xff44fffff8027c7f

def z1267 : W := mkw 0x14ffdeff7840c000 0x76fffffff8e07000

def z1268 : W := mkw 0x14ffdeff78200440 0x76fffffff8e00070

def z1269 : W := mkw 0x0d13ff15714bf09e 0x8403ff007803f00f

def z1270 : W := mkw 0x94ffdeff7860d455 0x7efffffffce3f070

def z1271 : W := mkw 0x01006b15e10e31bc 0x7fc7fffffb1e73fc

def z1272 : W := mkw 0x02ee80ea96b40f60 0x7bff00ff9ffc0ff0

def z1273 : W := mkw 0x14ffdeff78000000 0x04fffff3f8000000

def z1274 : W := mkw 0x0000401040000088 0xdd8300f07c038f8f

def z1275 : W := mkw 0x14ffdeff78000000 0x7cfffffffc038000

def z1276 : W := mkw 0x00084a5d60200440 0x7ffcffffe4e00c70

def z1277 : W := mkw 0x14ffdeff7e000000 0x7cffffffff000000

def z1278 : W := mkw 0x14e6c6b350000000 0x6444ff3380000000

def z1279 : W := mkw 0x143fdeff78000000 0x343ffffff8000000

def z1280 : W := mkw 0x04ee84ea00000000 0x70fce7ff80000000

def z1281 : W := mkw 0x1402c6b350000000 0x0000e73380000000

def z1282 : W := mkw 0x00c2c2b150000000 0x0044e73380000000

def z1283 : W := mkw 0x00006b15e10e2120 0x7f44ff3fe31e73f0

def z1284 : W := mkw 0x02ee80ea96b50f62 0xffff00ffffff8fff

def z1285 : W := mkw 0x14ffdeff78000000 0x24bfffcff8000000

def z1286 : W := mkw 0x941bdeff7860d455 0x9503fffff803fc7f

def z1287 : W := mkw 0x14f7d6b350000000 0x207cff3380000000

def z1288 : W := mkw 0x96ffdeff7ef0de55 0xfffffffffce3fc7f

def z1289 : W := mkw 0x09002100814ff1bc 0x0b000000031ff3fc

def z1290 : W := mkw 0x0d117f15614af09c 0x0400ff006002700c

def z1291 : W := mkw 0x8319394caffefffd 0xffbb18cc7fffffff

def z1292 : W := mkw 0x00084a5d68000000 0x7444fffff8000000

def z1293 : W := mkw 0x14ffdeff78000000 0x7dfffffff802000c

def z1294 : W := mkw 0x94ffdeff7860d455 0xf6fffffff8e3f07f

def z1295 : W := mkw 0x02ec00ea86b40f60 0x7fff00ff87ff8ff0

def z1296 : W := mkw 0x0000000000000000 0xddc300f07f038f8f

def z1297 : W := mkw 0x0cf7b5a017dbea02 0xfffffff01fffff83

def z1298 : W := mkw 0x14f7deb770000000 0x74ffff3fe0000000

def z1299 : W := mkw 0x00e44a1560000000 0x74fcff3fe0000000

def z1300 : W := mkw 0x04ff94ea0060c440 0x7fffffff84e3fc70

def z1301 : W := mkw 0x80084a5d68201455 0xf544fffff8000c7f

def z1302 : W := mkw 0x04e684a200000000 0x0044e73380000000

def z1303 : W := mkw 0x00004a1560000000 0x7d44ff3fe002000c

def z1304 : W := mkw 0x03002100879e2ba8 0x00000000031c0380

def z1305 : W := mkw 0x141bdeff78000000 0x7447fffff8000000

def z1306 : W := mkw 0x8919394caffff5fd 0xffbb18cc7fffffff

def z1307 : W := mkw 0x00c2e0b057930a8a 0xdfc3e0f07fff8f8f

def z1308 : W := mkw 0x01002100810e3bbe 0x8b000000031e7fff

def z1309 : W := mkw 0x00c2c0b056010a8a 0xd9c300f07f018f8f

def z1310 : W := mkw 0x941bde5d7860d455 0xfffffffffce3fc7f

def z1311 : W := mkw 0x00084aff60000000 0x7444ffffe0000000

def z1312 : W := mkw 0x14ff94ea18000000 0x74ffffff98000000

def z1313 : W := mkw 0x143d5e5f68000000 0x207cff3f80000000

def z1314 : W := mkw 0x1cffdeff78d0c000 0x74fffffff8e00000

def z1315 : W := mkw 0x02ec00ea86b40f60 0x6afc003f87fc03f0

def z1316 : W := mkw 0x0cf7b50007dbe000 0x2a7cff0007fff000

def z1317 : W := mkw 0x00c060b047020a88 0xddc3e0f07f038f8f

def z1318 : W := mkw 0x94ffdeff78001015 0xf4fffffff800000f

def z1319 : W := mkw 0x14ffdeff7e200e40 0x7fffffffffe00ff0

def z1320 : W := mkw 0x00d3b100074be000 0x6effff0007fff000

def z1321 : W := mkw 0x01006b15e10e31bc 0x7644ff3fe31c73f0

def z1322 : W := mkw 0x01006b15e10e31bc 0x3344ff3fe31c73fc

def z1323 : W := mkw 0x00c2cab570001014 0xffc7fffffc03fc7f

def z1324 : W := mkw 0x143fde5f78000000 0x747fff3ff8000000

def z1325 : W := mkw 0x00004a1560000000 0x0444ff33e0000000

def z1326 : W := mkw 0x01006b15f10e31be 0xff44ff3ffb1e73ff

def z1327 : W := mkw 0x00c2e0b057030a8a 0x9543e0f07b038f8f

def z1328 : W := mkw 0x0cf7b50017dbe002 0xeeffff001ffff003

def z1329 : W := mkw 0x10084aff78000000 0x1044e7fff8000000

def z1330 : W := mkw 0x80195a5d6860c441 0xf4fffffffce18c03

def z1331 : W := mkw 0x01002100810e21a8 0x0b000000031c03f0

def z1332 : W := mkw 0x0cf7b50007dbea02 0xeeffff0007fffc03

def z1333 : W := mkw 0x0cf7b50007dbe000 0x26bfff0004fff000

def z1334 : W := mkw 0x14e6c6b350000000 0x1044e7f3f8000000

def z1335 : W := mkw 0x00004a1560000000 0x2404ff0fe0000000

def z1336 : W := mkw 0x03002100879e3bbc 0x0b000000031e73fc

def z1337 : W := mkw 0x01006b15e10e31bc 0x7fc4ffffe71e7ffc

def z1338 : W := mkw 0x01004b15e00c3134 0x7f44ff3fe31c73f0

def z1339 : W := mkw 0x01002100810e31bc 0x01000000031c03fc

def z1340 : W := mkw 0x000000a000000a00 0xdd8300f07c038f8f

def z1341 : W := mkw 0x01002100879e31bc 0x0b00000007fe73fc

def z1342 : W := mkw 0x0300210087be2fe8 0x0b00000007fc0ff0

def z1343 : W := mkw 0x8a19394cafffff75 0xffbb18cc7fffffff

def z1344 : W := mkw 0x94eeceff78201455 0x9144e7fff8000c7f

def z1345 : W := mkw 0x0900210087dffbbe 0x8b00000007ffffff

def z1346 : W := mkw 0x81002100876fffff 0x8b00000007ffffff

def z1347 : W := mkw 0x0cf5350007dae000 0x6efcff0007fe7000

def z1348 : W := mkw 0x01002100870e3bbc 0x0b000000071e7ffc

def z1349 : W := mkw 0x16e6c6b356900a00 0x0044e73380000000

def z1350 : W := mkw 0x0cf7de1566d1c000 0x74ffff3fe4e18000

def z1351 : W := mkw 0x01006b15e10f31be 0xff44ff3fe31ff3ff

def z1352 : W := mkw 0x14eec6fb50000000 0x207ce73f80000000

def z1353 : W := mkw 0x02ee80ea86b50f60 0x7bff00ff87fd8ff0

def z1354 : W := mkw 0x14ffdeff7800008a 0xf4fffffff800000f

def z1355 : W := mkw 0x01002100810e31bc 0x7b00000c031e73fc

def z1356 : W := mkw 0x14e6c6b356010a02 0x0044e73380000000

def z1357 : W := mkw 0x16ffdeff7eb00e40 0x7dffffffffe00f80

def z1358 : W := mkw 0x02ec00ea86b40f60 0xfbfc00fffffc0fff

def z1359 : W := mkw 0x14ffd6fb58000000 0x54ffe7f3f8000000

def z1360 : W := mkw 0x02ec00ea86b40f60 0x72fc00ff83fc03f0

def z1361 : W := mkw 0x0cf7b5a017dbea02 0x6effff0007fff000

def z1362 : W := mkw 0x01002100810e21a8 0x09000000031e038c

def z1363 : W := mkw 0x0119394ca90e31bc 0x7fbb18cc7b1e73fc

def z1364 : W := mkw 0x14e6ceb770000000 0x1044e73fe0000000

def z1365 : W := mkw 0x14f7deb778000000 0x7447ff3ff8000000

def z1366 : W := mkw 0x0900210087dfe1a8 0x0a00000007fff380

def z1367 : W := mkw 0x80fd5aff6860d455 0xfffffffffce3fc7f

def z1368 : W := mkw 0x16ffdeff7eb00e40 0x7efffffffffc0c00

def z1369 : W := mkw 0x04f7d61140000000 0x64ffff3380000000

def z1370 : W := mkw 0x0cf7b50007dbea00 0x6fffff0007ffff80

def z1371 : W := mkw 0x0eee84ea86b50f60 0x7bfc00ff87fc0ff0

def z1372 : W := mkw 0x94ffdeff78201455 0xfdfffffffc038c7f

def z1373 : W := mkw 0x00dbdafd78000000 0x74fffffff8000000

def z1374 : W := mkw 0x14115e1568000000 0x7444ff3fe0000000

def z1375 : W := mkw 0x96ffdeff7ef0ce41 0xf4fffffffce18c03

def z1376 : W := mkw 0x01006b15e10e31bc 0x2644ff3fe31e73fc

def z1377 : W := mkw 0x00002904a10e3134 0x7f44ff3fe31e73fc

def z1378 : W := mkw 0x09002100879f21a8 0x00000000031c0380

def z1379 : W := mkw 0x94f7deb77840d015 0x8447ff33f803f00f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z7,z8,z6])],[(0,[z9,z2,z3,z4,z10,z11,z6]),(0,[z2,z3,z4,z5,z11,z12,z6]),(0,[z13,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z15,z11,z6]),(0,[z2,z16,z17,z3,z4,z11,z6]),(0,[z2,z3,z4,z5,z18,z11,z6]),(0,[z2,z3,z19,z4,z5,z11,z6]),(0,[z2,z20,z3,z4,z5,z11,z6]),(0,[z21,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z23]),(0,[z2,z3,z4,z5,z22,z24,z6])],[(1,[z25,z2,z4,z26,z11,z6]),(0,[z27,z16,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z28,z22,z6]),(0,[z2,z3,z4,z5,z11,z29,z6]),(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z31,z22,z6])],[(0,[z32,z33,z3,z4,z5,z11,z6]),(0,[z34,z2,z14,z3,z4,z5,z6]),(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z36]),(0,[z2,z3,z4,z5,z6,z37,z38])],[(0,[z2,z3,z4,z39,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z26,z6]),(0,[z2,z3,z4,z40,z5,z11,z6])],[(0,[z1,z2,z41,z3,z4,z5,z6]),(0,[z2,z42,z3,z4,z5,z6,z37])],[(0,[z43,z2,z3,z4,z44,z11,z6]),(0,[z45,z3,z4,z5,z11,z46,z6]),(0,[z25,z2,z3,z4,z5,z6,z37]),(0,[z1,z2,z3,z4,z47,z5,z6]),(0,[z48,z2,z3,z4,z5,z22,z6])]],
   [[(0,[z2,z3,z4,z49,z5,z11,z6]),(0,[z2,z3,z4,z50,z44,z11,z6]),(0,[z51,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z52,z11,z6]),(1,[z2,z3,z4,z5,z6,z23])],[(1,[z2,z3,z4,z5,z53,z6]),(1,[z2,z3,z4,z5,z54,z6]),(0,[z25,z21,z2,z3,z4,z11,z6]),(0,[z2,z55,z3,z4,z5,z11,z6])],[(0,[z2,z3,z56,z57,z5,z11,z6]),(1,[z2,z3,z4,z5,z58,z6]),(0,[z2,z3,z59,z4,z5,z11,z6]),(1,[z2,z3,z4,z5,z29,z6]),(0,[z60,z2,z3,z4,z5,z11,z6]),(0,[z2,z61,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z62])],[(0,[z63,z2,z3,z64,z4,z5,z6]),(0,[z65,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z66,z11,z6]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z2,z14,z3,z4,z5,z68,z6]),(0,[z67,z2,z3,z56,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z37,z69]),(1,[z3,z4,z5,z22,z24,z6]),(0,[z70,z3,z4,z5,z22,z11,z6])],[(0,[z71,z2,z3,z4,z5,z11,z6]),(0,[z2,z72,z3,z4,z5,z11,z6]),(0,[z2,z3,z35,z4,z5,z22,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z74]),(0,[z2,z4,z5,z75,z31,z11,z6]),(0,[z2,z3,z76,z4,z5,z11,z6]),(0,[z2,z3,z77,z4,z5,z11,z6])],[(0,[z78,z2,z3,z4,z5,z11,z6]),(0,[z79,z9,z3,z4,z5,z11,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z2,z80,z3,z4,z5,z11,z6]),(0,[z81,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z82]),(0,[z2,z61,z3,z4,z83,z5,z6]),(0,[z2,z3,z4,z5,z11,z68,z6]),(0,[z2,z3,z4,z5,z84,z11,z6]),(0,[z85,z2,z3,z4,z5,z11,z6])],[(0,[z86,z2,z3,z4,z5,z11,z6]),(0,[z1,z43,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z87,z6]),(0,[z2,z14,z3,z88,z4,z5,z6]),(0,[z89,z2,z3,z5,z11,z6,z90]),(0,[z2,z3,z4,z50,z11,z68,z6]),(0,[z2,z3,z4,z5,z11,z6,z91])],[(0,[z2,z3,z4,z5,z53,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z92]),(0,[z93,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z94,z4,z5,z22,z6]),(0,[z2,z3,z95,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z96,z37])]],
   [[(1,[z2,z97,z3,z4,z5,z6]),(0,[z2,z3,z64,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z98,z11,z6]),(0,[z1,z79,z2,z3,z4,z5,z6]),(0,[z99,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z100,z11,z6]),(0,[z2,z101,z41,z3,z4,z5,z6]),(1,[z27,z3,z4,z5,z11,z6])],[(0,[z3,z4,z5,z28,z11,z102,z6]),(0,[z103,z2,z3,z4,z5,z11,z6]),(0,[z104,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z105])],[(0,[z32,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z106,z4,z5,z11,z6])],[(0,[z2,z97,z3,z4,z5,z11,z6]),(0,[z107,z2,z3,z4,z5,z11,z6]),(0,[z3,z4,z5,z11,z46,z6,z108]),(0,[z109,z2,z14,z3,z4,z5,z6]),(0,[z110,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z111,z6]),(0,[z112,z2,z3,z4,z5,z11,z113])],[(0,[z109,z25,z2,z4,z5,z11,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z82])],[(0,[z2,z3,z4,z114,z5,z11,z6]),(0,[z51,z3,z4,z5,z11,z102,z6])],[(0,[z1,z9,z2,z3,z4,z5,z6]),(0,[z67,z2,z115,z3,z5,z11,z6]),(0,[z2,z116,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z117]),(0,[z118,z2,z3,z4,z5,z11,z6])],[(0,[z2,z119,z3,z4,z5,z11,z6]),(0,[z2,z3,z120,z4,z5,z11,z6]),(0,[z121,z2,z4,z5,z31,z11,z6]),(0,[z2,z3,z4,z122,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z123,z6])]],
   [[(0,[z2,z3,z4,z124,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z125]),(0,[z2,z17,z3,z4,z5,z22,z6]),(0,[z2,z14,z3,z94,z4,z5,z6]),(0,[z2,z3,z4,z5,z126,z6,z37]),(0,[z2,z3,z127,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z128,z11,z6]),(0,[z9,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z129,z130,z11,z6]),(0,[z51,z45,z3,z4,z5,z11,z6]),(0,[z2,z131,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z113,z6])],[(0,[z132,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z133,z6]),(0,[z2,z14,z3,z134,z4,z5,z6]),(0,[z135,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z136,z6,z137]),(0,[z67,z2,z3,z4,z5,z11,z6])],[(0,[z2,z3,z138,z4,z5,z11,z6]),(0,[z34,z2,z3,z4,z66,z11,z6]),(0,[z2,z3,z139,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z140,z6]),(0,[z141,z2,z14,z3,z4,z5,z6]),(1,[z2,z142,z3,z4,z5,z6])],[(0,[z2,z143,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z11,z6,z144,z90]),(0,[z145,z2,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z11,z6,z146]),(0,[z2,z3,z4,z50,z5,z102,z6]),(1,[z2,z3,z4,z147,z11,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z90]),(0,[z21,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z117,z37]),(1,[z2,z3,z4,z5,z22,z37])],[(0,[z2,z149,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z150,z6]),(0,[z2,z41,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z151,z11,z6])]],
   [[(0,[z2,z3,z64,z4,z5,z22,z6]),(0,[z2,z3,z152,z4,z5,z11,z6]),(1,[z2,z3,z4,z11,z6,z144]),(0,[z2,z3,z4,z5,z31,z11,z6]),(0,[z2,z3,z4,z5,z6,z153,z37])],[(0,[z154,z2,z14,z3,z4,z5,z6]),(1,[z63,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z155,z11,z6]),(0,[z1,z2,z3,z56,z4,z5,z6]),(0,[z2,z3,z56,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z11,z156,z6]),(0,[z2,z3,z4,z50,z5,z28,z6]),(1,[z109,z2,z157,z5,z11,z6]),(0,[z25,z2,z4,z5,z26,z11,z6]),(1,[z2,z3,z4,z5,z158,z6]),(0,[z2,z3,z4,z5,z6,z62,z37])],[(0,[z43,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z159]),(1,[z2,z3,z4,z5,z160,z6])],[(0,[z2,z3,z161,z4,z5,z11,z6]),(0,[z145,z2,z41,z3,z4,z5,z6]),(0,[z2,z3,z4,z50,z5,z22,z6])],[(0,[z162,z2,z3,z4,z5,z11,z6]),(0,[z163,z2,z3,z4,z5,z11,z6]),(0,[z2,z4,z164,z5,z26,z11,z6]),(0,[z1,z2,z3,z4,z165,z5,z6]),(0,[z1,z2,z3,z4,z5,z166,z6]),(1,[z2,z3,z4,z40,z5,z6]),(1,[z3,z4,z167,z5,z11,z6])],[(0,[z2,z168,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z46,z6,z169]),(0,[z2,z14,z3,z4,z164,z5,z6]),(0,[z2,z101,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z170,z6])]],
   [[(0,[z2,z3,z4,z5,z171,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z172]),(0,[z0,z2,z3,z4,z5,z11,z6]),(0,[z2,z173,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z174]),(0,[z2,z175,z3,z4,z5,z11,z6])],[(0,[z176,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z57,z5,z6]),(0,[z3,z4,z5,z11,z102,z46,z6]),(0,[z2,z115,z3,z35,z5,z11,z6]),(0,[z2,z4,z5,z177,z11,z178,z6]),(0,[z179,z2,z3,z4,z5,z11,z6])],[(0,[z3,z180,z4,z5,z11,z46,z6]),(0,[z1,z2,z3,z4,z157,z5,z6]),(0,[z2,z3,z4,z5,z181,z11,z6]),(0,[z182,z3,z4,z165,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z6,z37])],[(0,[z183,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z10,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z184]),(1,[z67,z2,z3,z5,z11,z185]),(0,[z2,z3,z4,z83,z166,z11,z6])],[(0,[z186,z2,z3,z4,z5,z11,z6]),(0,[z3,z180,z4,z57,z5,z11,z6]),(0,[z2,z3,z180,z5,z11,z6,z185]),(0,[z2,z3,z4,z187,z5,z11,z6]),(0,[z2,z3,z94,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z188,z6]),(0,[z2,z3,z4,z5,z11,z6,z189])],[(0,[z32,z3,z4,z44,z5,z11,z6]),(0,[z2,z3,z190,z4,z5,z11,z6]),(0,[z2,z3,z4,z191,z5,z11,z6]),(0,[z45,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z192,z6]),(0,[z2,z3,z4,z5,z22,z126,z6]),(0,[z2,z3,z4,z5,z11,z193,z6])],[(0,[z2,z3,z4,z5,z194,z11,z6]),(0,[z9,z2,z3,z4,z5,z53,z6]),(0,[z195,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z196,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z197]),(0,[z2,z3,z4,z5,z22,z136,z6]),(0,[z198,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z129,z5,z6,z37]),(0,[z2,z3,z4,z5,z126,z68,z6])],[(1,[z2,z3,z4,z199,z11,z6]),(0,[z2,z3,z4,z5,z200,z11,z6])]],
   [[(0,[z2,z3,z4,z201,z5,z11,z6]),(0,[z51,z2,z3,z4,z5,z11,z46]),(0,[z2,z14,z3,z4,z202,z5,z6]),(0,[z2,z3,z4,z5,z203,z11,z6]),(0,[z2,z3,z4,z204,z5,z31,z6])],[(0,[z154,z3,z64,z4,z5,z11,z6]),(0,[z33,z2,z3,z4,z5,z6,z37])],[(0,[z2,z14,z3,z4,z50,z5,z6]),(0,[z2,z16,z3,z5,z31,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z205])],[(0,[z2,z3,z4,z5,z22,z6,z108]),(0,[z2,z3,z4,z5,z11,z206,z6]),(0,[z2,z3,z4,z165,z5,z11,z8]),(0,[z2,z42,z3,z4,z5,z11,z6])],[(0,[z2,z3,z207,z4,z5,z11,z6]),(0,[z208,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z209,z11,z6]),(0,[z1,z2,z17,z3,z4,z5,z6])],[(0,[z2,z64,z4,z5,z11,z6,z90]),(0,[z2,z3,z4,z210,z5,z11,z6]),(0,[z2,z3,z4,z165,z130,z11,z6]),(0,[z2,z211,z3,z4,z5,z11,z6]),(0,[z51,z2,z3,z4,z5,z11,z6]),(0,[z2,z212,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z213,z5,z11,z6])],[(0,[z154,z2,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z214]),(0,[z2,z3,z4,z164,z5,z22,z6]),(0,[z2,z3,z4,z5,z215,z11,z6]),(0,[z2,z3,z4,z216,z5,z11,z6]),(0,[z2,z3,z4,z5,z8,z6,z23])],[(0,[z3,z4,z5,z130,z11,z46,z6]),(0,[z2,z3,z4,z5,z11,z6,z217]),(0,[z2,z3,z4,z155,z5,z11,z6]),(0,[z2,z218,z3,z4,z5,z11,z6]),(0,[z2,z219,z3,z4,z5,z11,z6])]],
   [[(0,[z2,z3,z4,z5,z11,z6,z220]),(0,[z2,z3,z4,z5,z11,z221,z6]),(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z2,z14,z3,z4,z5,z6,z37]),(0,[z93,z2,z3,z4,z5,z11,z90]),(0,[z3,z4,z5,z11,z6,z223,z185])],[(0,[z2,z3,z4,z5,z11,z224,z6]),(0,[z2,z3,z4,z57,z5,z6,z37]),(1,[z2,z3,z4,z225,z5,z6]),(0,[z2,z3,z4,z5,z11,z226,z6]),(0,[z227,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z228,z4,z5,z11,z6])],[(0,[z2,z229,z3,z4,z5,z6,z37]),(0,[z2,z115,z3,z5,z11,z188,z6]),(0,[z145,z2,z3,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z188,z6]),(0,[z230,z2,z3,z4,z5,z11,z6]),(1,[z179,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z231,z6]),(0,[z2,z3,z4,z5,z232,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z37])],[(0,[z3,z64,z4,z5,z130,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z233]),(0,[z2,z14,z3,z4,z5,z126,z6]),(0,[z2,z3,z4,z234,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z8,z6])],[(0,[z33,z2,z3,z210,z5,z11,z6]),(0,[z2,z3,z4,z235,z5,z11,z6]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z2,z14,z3,z4,z5,z136,z6]),(0,[z93,z2,z3,z4,z5,z11,z6]),(0,[z2,z16,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z11,z188,z6])],[(0,[z2,z3,z64,z4,z5,z11,z6]),(0,[z236,z2,z3,z4,z5,z11,z6]),(0,[z237,z2,z3,z4,z5,z11,z6]),(0,[z238,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z239,z11,z6]),(0,[z2,z3,z4,z5,z11,z240,z6]),(0,[z2,z3,z4,z5,z11,z241,z6])],[(0,[z25,z2,z3,z4,z44,z11,z6]),(0,[z51,z2,z3,z242,z5,z11,z6]),(0,[z109,z2,z4,z164,z5,z11,z6]),(0,[z2,z3,z4,z50,z83,z11,z6])],[(0,[z243,z2,z3,z4,z5,z11,z6]),(0,[z32,z2,z3,z4,z5,z11,z6]),(0,[z32,z3,z4,z5,z11,z46,z6]),(0,[z67,z2,z3,z4,z5,z11,z185]),(0,[z21,z2,z3,z4,z11,z6,z117]),(0,[z2,z3,z4,z5,z244,z22,z6])]],
   [[(0,[z2,z245,z3,z4,z5,z11,z6]),(0,[z43,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z5,z11,z6]),(0,[z2,z3,z4,z199,z157,z11,z6]),(0,[z67,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z246])],[(1,[z33,z229,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z247,z11,z6]),(0,[z2,z14,z3,z4,z5,z6,z108]),(1,[z2,z101,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z248,z11,z6]),(0,[z2,z3,z4,z50,z5,z11,z6]),(1,[z2,z3,z4,z5,z6,z37])],[(0,[z249,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z130,z166,z11,z6]),(0,[z2,z17,z3,z4,z26,z11,z6]),(0,[z250,z2,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z251,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z108]),(0,[z2,z3,z4,z5,z252,z11,z6]),(0,[z2,z3,z4,z5,z11,z253,z6]),(0,[z93,z2,z3,z4,z5,z254,z6]),(0,[z67,z2,z3,z4,z5,z255,z6])],[(0,[z2,z3,z256,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z257,z6]),(0,[z2,z3,z4,z5,z11,z6,z258])],[(0,[z259,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z260,z5,z11,z6]),(0,[z45,z2,z3,z4,z5,z11,z46]),(0,[z2,z3,z261,z129,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z262])],[(0,[z263,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z54,z11,z6]),(0,[z2,z14,z3,z4,z5,z28,z6]),(0,[z51,z2,z264,z4,z5,z11,z6]),(0,[z148,z2,z3,z4,z5,z11,z6]),(1,[z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z200,z6]),(0,[z93,z2,z4,z5,z11,z6,z90]),(0,[z2,z3,z4,z265,z5,z11,z6]),(0,[z2,z3,z4,z5,z158,z11,z6])],[(0,[z2,z3,z266,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z185]),(0,[z2,z3,z4,z5,z267,z11,z6])]],
   [[(0,[z268,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z269]),(0,[z1,z2,z3,z4,z5,z113,z6])],[(0,[z32,z2,z3,z4,z44,z11,z6]),(0,[z2,z270,z3,z4,z5,z11,z6]),(0,[z2,z3,z271,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z8,z6]),(0,[z272,z2,z3,z4,z11,z6,z90]),(0,[z2,z16,z3,z4,z31,z11,z6]),(0,[z2,z273,z3,z4,z5,z11,z6])],[(0,[z3,z4,z57,z5,z130,z11,z6]),(0,[z45,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z94,z5,z274,z11,z6]),(0,[z2,z3,z4,z165,z5,z6,z37])],[(0,[z1,z2,z3,z261,z4,z5,z6]),(0,[z275,z2,z3,z4,z5,z11,z6]),(0,[z276,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z8,z6]),(0,[z2,z3,z4,z5,z11,z6,z277])],[(1,[z2,z3,z210,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z278,z6]),(0,[z2,z3,z4,z5,z11,z6,z153]),(0,[z2,z3,z4,z5,z24,z11,z6])],[(0,[z2,z3,z4,z5,z11,z279,z6]),(0,[z2,z3,z4,z5,z11,z280,z6]),(1,[z45,z3,z4,z5,z11,z46]),(0,[z2,z61,z14,z3,z4,z5,z6])],[(0,[z2,z3,z4,z281,z5,z11,z6]),(0,[z13,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z11,z282,z6]),(0,[z2,z3,z4,z283,z5,z11,z6]),(0,[z2,z284,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z285,z6])],[(0,[z2,z3,z4,z5,z11,z286,z6]),(0,[z2,z72,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z287,z5,z11,z6])]],
   [[(0,[z2,z3,z4,z157,z5,z22,z6])],[(0,[z2,z41,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z288,z6]),(0,[z2,z3,z4,z5,z11,z289,z6]),(0,[z2,z14,z3,z4,z5,z274,z6]),(0,[z290,z2,z3,z4,z5,z11,z6])],[(0,[z9,z3,z4,z57,z5,z11,z6]),(0,[z2,z3,z4,z225,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z90,z37]),(0,[z2,z3,z4,z5,z11,z6,z291])],[(0,[z33,z2,z3,z4,z5,z292,z6]),(0,[z2,z3,z4,z5,z293,z11,z6]),(0,[z2,z3,z4,z164,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z294,z6]),(0,[z295,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z296,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z297,z6]),(0,[z2,z3,z4,z83,z5,z166,z6])],[(0,[z33,z2,z3,z4,z5,z298,z6]),(0,[z2,z3,z299,z4,z5,z11,z6]),(0,[z43,z3,z4,z5,z130,z11,z6]),(0,[z2,z3,z4,z5,z22,z46,z6]),(0,[z300,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z301,z11,z6]),(0,[z21,z2,z3,z4,z5,z11,z8]),(0,[z302,z2,z3,z4,z5,z6,z37])],[(0,[z229,z3,z4,z5,z11,z46,z6]),(0,[z303,z2,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z6,z304]),(0,[z34,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z286,z6]),(0,[z2,z3,z4,z5,z11,z6,z305]),(0,[z21,z2,z3,z4,z5,z306,z6]),(1,[z3,z4,z5,z24,z11,z6])],[(0,[z2,z3,z4,z307,z5,z11,z6]),(0,[z2,z308,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z309,z6]),(0,[z2,z3,z4,z5,z177,z11,z6]),(0,[z2,z16,z3,z4,z5,z310,z6]),(0,[z2,z3,z261,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z11,z311,z6]),(0,[z2,z312,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z11,z6]),(0,[z112,z2,z3,z4,z5,z6,z37])]],
   [[(0,[z32,z43,z3,z4,z5,z11,z6]),(0,[z51,z32,z3,z4,z5,z11,z6]),(0,[z2,z313,z3,z4,z5,z11,z6]),(0,[z109,z2,z4,z157,z5,z11,z6]),(1,[z2,z3,z4,z5,z289,z6]),(0,[z1,z2,z14,z4,z5,z11,z6])],[(0,[z2,z314,z3,z4,z5,z11,z6]),(0,[z2,z115,z3,z129,z5,z11,z6]),(0,[z25,z315,z3,z4,z5,z11,z6]),(1,[z2,z16,z3,z31,z11,z6]),(0,[z2,z316,z3,z4,z5,z11,z6])],[(0,[z32,z79,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z317,z6]),(0,[z25,z2,z3,z4,z5,z22,z6]),(1,[z2,z41,z4,z5,z11,z136]),(0,[z2,z318,z3,z4,z5,z11,z6]),(0,[z182,z2,z3,z4,z5,z11,z6])],[(0,[z1,z2,z3,z64,z4,z5,z6]),(0,[z13,z3,z4,z5,z11,z102,z6]),(0,[z51,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z129,z5,z11,z6]),(0,[z2,z3,z4,z319,z5,z11,z6]),(0,[z2,z3,z4,z5,z188,z6,z37])],[(0,[z2,z3,z4,z5,z11,z320,z6]),(0,[z2,z3,z4,z5,z11,z321,z6]),(0,[z322,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z31,z6]),(1,[z2,z3,z4,z5,z310,z6]),(0,[z2,z3,z4,z5,z244,z11,z6]),(1,[z2,z3,z4,z5,z7,z6]),(0,[z2,z3,z4,z5,z113,z6,z37])],[(0,[z2,z3,z4,z5,z11,z298,z6]),(0,[z2,z3,z4,z5,z323,z11,z6]),(1,[z2,z3,z4,z5,z209,z6]),(0,[z2,z3,z4,z5,z324,z11,z6]),(0,[z1,z2,z3,z4,z5,z177,z6]),(0,[z135,z2,z14,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z325,z11,z6]),(1,[z1,z2,z4,z5,z178,z6]),(0,[z2,z3,z4,z5,z274,z68,z6]),(0,[z2,z3,z4,z167,z5,z11,z6]),(0,[z2,z326,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z6,z69]),(0,[z2,z3,z4,z5,z6,z108,z37]),(0,[z109,z2,z115,z4,z5,z11,z6]),(0,[z1,z2,z14,z3,z4,z5,z6]),(0,[z2,z143,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z7,z11,z6])]],
   [[(0,[z154,z33,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z327,z11,z6]),(0,[z222,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z328]),(0,[z329,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z330,z4,z5,z11,z6]),(0,[z2,z17,z4,z164,z5,z11,z6]),(0,[z2,z3,z4,z331,z5,z11,z6])],[(0,[z33,z229,z3,z4,z5,z11,z6]),(0,[z2,z115,z3,z180,z5,z11,z6]),(0,[z109,z2,z3,z35,z5,z11,z6]),(0,[z227,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z332,z11,z6]),(0,[z21,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z333,z4,z5,z11,z6]),(0,[z2,z3,z4,z334,z5,z11,z6])],[(0,[z2,z14,z3,z4,z5,z46,z6]),(0,[z2,z3,z4,z5,z335,z46,z6]),(0,[z93,z2,z41,z4,z5,z11,z6]),(0,[z93,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z336,z22,z6])],[(1,[z2,z3,z4,z5,z292,z6]),(0,[z2,z3,z4,z337,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z338,z6]),(0,[z2,z3,z4,z5,z26,z6,z37]),(0,[z2,z339,z3,z4,z5,z11,z6]),(0,[z3,z4,z165,z167,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z96]),(0,[z2,z340,z3,z4,z5,z11,z6])],[(1,[z2,z3,z4,z5,z298,z6]),(0,[z2,z115,z3,z57,z5,z11,z6]),(0,[z2,z3,z341,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z102,z6,z37]),(0,[z2,z3,z4,z5,z11,z6,z342]),(0,[z2,z3,z261,z4,z31,z11,z6]),(0,[z2,z3,z4,z5,z11,z343,z6]),(0,[z2,z3,z4,z5,z344,z11,z6]),(0,[z21,z2,z3,z4,z165,z11,z6])],[(0,[z345,z2,z3,z4,z5,z11,z6]),(0,[z32,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z129,z44,z11,z6]),(0,[z2,z3,z4,z5,z11,z346,z6]),(0,[z2,z3,z4,z5,z335,z11,z6]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z2,z14,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z347,z11,z6]),(0,[z2,z3,z4,z5,z11,z348,z6]),(0,[z349,z2,z3,z4,z5,z11,z6])],[(0,[z9,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z57,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z350,z6]),(0,[z2,z3,z4,z5,z11,z351,z6]),(0,[z2,z352,z3,z4,z5,z11,z6]),(0,[z2,z61,z3,z94,z5,z11,z6]),(1,[z2,z3,z4,z5,z22,z113])],[(0,[z2,z229,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z102,z126,z6]),(1,[z2,z3,z4,z204,z5,z6]),(1,[z70,z3,z4,z5,z11,z6])]],
   [[(0,[z2,z3,z4,z44,z5,z6,z37]),(0,[z109,z67,z2,z3,z5,z11,z6]),(0,[z353,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z354,z5,z11,z6]),(0,[z2,z14,z3,z4,z83,z5,z6]),(0,[z2,z3,z4,z5,z11,z355,z6]),(0,[z141,z2,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z5,z356,z11,z6]),(0,[z2,z3,z357,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z358]),(0,[z2,z101,z14,z3,z4,z5,z6]),(0,[z2,z3,z359,z4,z5,z11,z6]),(0,[z360,z2,z3,z4,z5,z11,z6])],[(0,[z2,z361,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z83,z5,z68,z6]),(0,[z2,z3,z4,z362,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z363,z6]),(0,[z364,z2,z3,z4,z5,z11,z6]),(0,[z2,z115,z3,z157,z5,z11,z6]),(0,[z2,z115,z3,z4,z5,z6,z37]),(1,[z2,z3,z4,z5,z6,z342]),(0,[z2,z3,z4,z165,z5,z11,z117])],[(0,[z2,z365,z3,z4,z5,z11,z6]),(0,[z33,z2,z229,z4,z5,z11,z6]),(0,[z2,z14,z3,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z366]),(0,[z2,z3,z4,z5,z367,z11,z6]),(0,[z2,z3,z4,z5,z6,z6,z37])],[(0,[z2,z3,z4,z157,z5,z11,z6]),(0,[z2,z3,z4,z5,z368,z11,z6]),(0,[z141,z1,z2,z3,z4,z5,z6]),(1,[z2,z3,z5,z11,z6,z305])],[(0,[z154,z2,z3,z4,z5,z6,z37]),(0,[z51,z2,z3,z369,z5,z11,z6]),(0,[z2,z3,z4,z370,z5,z11,z6]),(0,[z179,z2,z3,z4,z5,z6,z90]),(0,[z2,z3,z4,z5,z11,z371,z6])],[(0,[z1,z2,z115,z3,z4,z5,z6]),(0,[z372,z2,z3,z4,z5,z11,z6])]],
   [[(0,[z2,z3,z4,z373,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z374]),(1,[z182,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z165,z11,z8])],[(0,[z2,z3,z4,z5,z11,z6,z375]),(0,[z33,z2,z3,z4,z98,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z376]),(0,[z2,z229,z4,z5,z11,z6,z90]),(0,[z1,z21,z2,z3,z4,z5,z6]),(0,[z30,z2,z3,z4,z5,z11,z6]),(1,[z2,z14,z4,z5,z177,z6]),(0,[z16,z377,z3,z4,z5,z11,z6]),(0,[z378,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z6,z37,z379])],[(0,[z79,z2,z3,z180,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z380,z6]),(0,[z381,z2,z3,z4,z5,z11,z6]),(0,[z382,z2,z3,z4,z5,z11,z6]),(0,[z383,z2,z3,z4,z5,z11,z6])],[(0,[z384,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z385,z11,z6]),(0,[z2,z3,z4,z5,z26,z22,z6]),(0,[z21,z2,z17,z3,z4,z11,z6])],[(0,[z2,z3,z4,z5,z11,z386,z6]),(0,[z387,z2,z3,z4,z5,z11,z6]),(0,[z388,z2,z3,z4,z5,z11,z6]),(1,[z2,z4,z5,z75,z11,z6]),(0,[z2,z3,z4,z389,z5,z22,z6]),(0,[z2,z3,z390,z4,z5,z11,z6]),(0,[z2,z3,z4,z391,z5,z11,z6])],[(0,[z2,z14,z3,z4,z44,z5,z6]),(0,[z2,z3,z4,z44,z31,z11,z6]),(0,[z2,z3,z4,z5,z11,z392,z6])],[(0,[z2,z3,z4,z5,z393,z11,z6]),(0,[z1,z2,z3,z4,z5,z394,z6]),(0,[z2,z3,z4,z5,z22,z178,z6]),(0,[z2,z3,z4,z5,z11,z395,z6]),(1,[z3,z4,z5,z11,z6,z366]),(0,[z2,z3,z4,z396,z5,z11,z6]),(0,[z2,z3,z4,z5,z397,z11,z6])],[(0,[z1,z33,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z22,z102,z6]),(1,[z2,z3,z242,z5,z11,z6]),(0,[z25,z2,z3,z4,z5,z11,z6]),(0,[z73,z2,z3,z4,z5,z11,z6]),(0,[z383,z3,z4,z5,z11,z6,z90]),(0,[z2,z3,z4,z5,z11,z398,z6]),(0,[z2,z3,z4,z5,z11,z6,z399]),(0,[z2,z3,z400,z4,z5,z11,z6])]],
   [[(0,[z2,z3,z4,z5,z11,z401,z6]),(0,[z2,z3,z4,z5,z402,z11,z6]),(0,[z2,z14,z3,z4,z5,z130,z6]),(0,[z2,z3,z4,z130,z31,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z403]),(0,[z25,z2,z35,z4,z5,z11,z6]),(0,[z2,z3,z5,z368,z26,z11,z6]),(0,[z1,z2,z212,z3,z4,z5,z6])],[(0,[z404,z2,z3,z4,z5,z11,z6])],[(0,[z2,z405,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z166,z6,z37]),(0,[z2,z3,z4,z5,z301,z22,z6])],[(0,[z2,z115,z3,z4,z5,z22,z6]),(0,[z2,z14,z3,z4,z129,z5,z6]),(0,[z2,z406,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z407,z6]),(0,[z79,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z408,z5,z11,z6]),(0,[z2,z3,z4,z5,z178,z6,z37]),(0,[z2,z14,z3,z4,z5,z6,z409]),(0,[z2,z41,z3,z4,z5,z11,z136]),(0,[z2,z410,z3,z4,z5,z11,z6])],[(0,[z2,z3,z411,z4,z5,z11,z6]),(0,[z51,z2,z190,z4,z5,z11,z6]),(0,[z2,z412,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z166,z126,z6]),(0,[z2,z3,z4,z5,z22,z22,z6])],[(1,[z2,z3,z4,z5,z335,z6]),(0,[z413,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z16,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z409]),(0,[z2,z3,z414,z4,z5,z11,z6]),(0,[z2,z3,z415,z4,z5,z11,z6]),(0,[z2,z3,z4,z416,z5,z6,z37])],[(0,[z51,z3,z180,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z417,z11,z6]),(1,[z2,z264,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z68,z6]),(0,[z2,z3,z4,z5,z336,z11,z6]),(0,[z2,z3,z4,z5,z11,z418,z6]),(0,[z2,z3,z4,z419,z5,z11,z6]),(0,[z2,z3,z4,z11,z8,z6,z117]),(0,[z2,z3,z4,z420,z5,z11,z6]),(0,[z2,z421,z3,z4,z5,z22,z6])]],
   [[(0,[z2,z3,z4,z422,z5,z11,z6]),(0,[z238,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z126,z6]),(0,[z2,z423,z3,z4,z5,z11,z6])],[(1,[z2,z3,z4,z98,z11,z6]),(0,[z2,z3,z4,z5,z11,z136,z6]),(0,[z2,z3,z4,z129,z5,z22,z6]),(0,[z424,z2,z3,z4,z5,z11,z6]),(0,[z302,z2,z3,z4,z5,z11,z6]),(0,[z70,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z425])],[(0,[z32,z2,z14,z3,z4,z5,z6]),(0,[z2,z218,z3,z4,z157,z11,z6]),(0,[z25,z2,z3,z4,z11,z8,z6]),(0,[z426,z2,z3,z4,z5,z11,z6]),(0,[z2,z427,z3,z4,z5,z11,z6])],[(0,[z43,z2,z14,z3,z4,z5,z6])],[(0,[z33,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z428,z5,z11,z6]),(0,[z25,z2,z3,z4,z26,z11,z6]),(1,[z2,z3,z5,z368,z11,z6]),(1,[z2,z3,z4,z370,z5,z6]),(0,[z2,z3,z4,z164,z5,z429,z6]),(0,[z2,z14,z3,z4,z5,z178,z6]),(0,[z2,z3,z4,z5,z11,z430,z6]),(0,[z2,z3,z261,z4,z5,z11,z6]),(0,[z112,z2,z3,z4,z5,z11,z6])],[(0,[z431,z2,z3,z4,z5,z11,z6]),(0,[z2,z432,z3,z4,z5,z11,z6]),(0,[z2,z433,z3,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z102,z6]),(0,[z51,z2,z3,z4,z5,z11,z108]),(1,[z2,z3,z4,z5,z6,z409])],[(0,[z2,z3,z4,z5,z11,z178,z6]),(0,[z2,z3,z4,z5,z11,z6,z434]),(0,[z2,z3,z435,z4,z5,z11,z6])],[(0,[z2,z3,z4,z436,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z437]),(0,[z2,z3,z4,z5,z11,z102,z6]),(0,[z2,z438,z3,z4,z5,z11,z6])]],
   [[(1,[z43,z3,z4,z130,z11,z6]),(1,[z1,z2,z14,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z439,z6]),(0,[z2,z3,z4,z40,z5,z31,z6])],[(0,[z63,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z394,z11,z6]),(0,[z2,z3,z134,z4,z5,z11,z6]),(0,[z2,z3,z5,z274,z11,z126,z6]),(0,[z2,z3,z440,z4,z5,z11,z6])],[(0,[z441,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z442,z6]),(0,[z2,z3,z443,z4,z5,z11,z6])],[(0,[z444,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z445,z6]),(0,[z2,z446,z3,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z274,z6,z37]),(0,[z2,z3,z4,z5,z447,z11,z6])],[(0,[z2,z3,z4,z57,z5,z22,z6]),(0,[z51,z3,z4,z5,z130,z11,z6]),(1,[z2,z448,z3,z4,z5,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z449,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z450,z4,z5,z11,z6]),(0,[z67,z2,z3,z4,z5,z160,z6]),(0,[z2,z451,z3,z4,z5,z11,z6]),(0,[z452,z2,z3,z4,z5,z11,z6])],[(0,[z2,z229,z41,z4,z5,z11,z6]),(0,[z2,z229,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z453,z5,z11,z6]),(0,[z45,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z35,z4,z5,z289,z6]),(0,[z2,z3,z4,z50,z5,z166,z6]),(0,[z2,z3,z4,z5,z454,z11,z6]),(1,[z70,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z130,z6,z37]),(0,[z455,z2,z3,z4,z5,z11,z6]),(0,[z51,z2,z3,z4,z5,z58,z6]),(0,[z2,z456,z3,z4,z5,z11,z6]),(0,[z2,z457,z3,z4,z5,z11,z6]),(0,[z458,z2,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z5,z459,z11,z6]),(0,[z1,z112,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z460,z5,z11,z6]),(0,[z2,z3,z4,z5,z461,z11,z6]),(0,[z2,z16,z3,z4,z5,z22,z6])]],
   [[(0,[z2,z3,z4,z462,z5,z11,z6]),(0,[z2,z3,z463,z4,z5,z11,z6]),(0,[z2,z464,z3,z4,z5,z11,z6]),(0,[z2,z14,z3,z35,z4,z5,z6]),(0,[z2,z3,z4,z5,z26,z11,z6]),(0,[z2,z3,z4,z5,z11,z255,z6]),(0,[z2,z3,z4,z465,z5,z11,z6]),(0,[z3,z4,z5,z22,z24,z11,z6])],[(0,[z2,z3,z4,z466,z5,z11,z6]),(0,[z2,z3,z4,z5,z467,z11,z6]),(0,[z109,z2,z3,z129,z5,z11,z6]),(0,[z468,z2,z3,z4,z5,z11,z6]),(0,[z2,z35,z4,z157,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z26,z6]),(0,[z2,z469,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z389,z5,z11,z6]),(0,[z470,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z5,z442,z6]),(0,[z2,z3,z4,z5,z11,z6,z471])],[(1,[z2,z3,z4,z5,z445,z6]),(0,[z2,z3,z4,z5,z472,z11,z6]),(0,[z2,z3,z473,z4,z5,z11,z6]),(0,[z2,z14,z41,z3,z4,z5,z6]),(0,[z2,z3,z56,z4,z5,z11,z188])],[(0,[z474,z2,z3,z4,z5,z11,z6]),(0,[z9,z3,z4,z5,z11,z46,z6]),(1,[z315,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z342]),(0,[z2,z3,z4,z5,z166,z274,z6])],[(0,[z34,z2,z3,z4,z5,z6,z37]),(0,[z2,z475,z3,z4,z5,z11,z6]),(0,[z476,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z261,z4,z129,z11,z6]),(0,[z2,z61,z3,z4,z50,z5,z6]),(0,[z2,z3,z4,z477,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z6,z117]),(1,[z2,z3,z4,z5,z22,z6])],[(0,[z141,z2,z3,z4,z5,z11,z6]),(0,[z2,z97,z3,z64,z4,z5,z6]),(1,[z79,z3,z180,z5,z11,z6]),(0,[z2,z3,z4,z44,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z478,z6]),(0,[z2,z3,z479,z4,z5,z11,z6]),(0,[z2,z41,z4,z5,z11,z136,z6]),(0,[z2,z3,z4,z5,z11,z6,z480]),(0,[z2,z3,z481,z4,z5,z11,z6])],[(0,[z482,z2,z3,z4,z5,z11,z6]),(0,[z1,z45,z2,z3,z4,z5,z6]),(0,[z2,z448,z3,z4,z5,z11,z6]),(1,[z377,z3,z4,z5,z11,z6])],[(0,[z32,z2,z3,z4,z5,z54,z6]),(1,[z13,z3,z4,z5,z102,z6]),(0,[z2,z3,z129,z5,z31,z11,z6]),(0,[z483,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z83,z5,z6,z37])]],
   [[(0,[z2,z115,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z484,z5,z11,z6]),(0,[z67,z2,z3,z5,z11,z6,z185])],[(0,[z51,z9,z3,z4,z5,z11,z6]),(0,[z485,z2,z3,z4,z5,z11,z6]),(0,[z109,z2,z3,z180,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z486,z6]),(0,[z2,z3,z4,z5,z274,z28,z6]),(1,[z2,z3,z261,z129,z11,z6])],[(0,[z2,z3,z4,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z66,z11,z6]),(0,[z45,z2,z3,z4,z5,z11,z108]),(0,[z2,z3,z487,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z164,z5,z6]),(0,[z272,z2,z3,z4,z5,z11,z6]),(0,[z2,z61,z3,z4,z5,z6,z37]),(0,[z2,z3,z390,z4,z5,z22,z6]),(0,[z2,z3,z4,z391,z5,z22,z6])],[(0,[z154,z3,z4,z5,z11,z46,z6]),(0,[z2,z3,z488,z4,z5,z11,z6]),(0,[z13,z2,z3,z4,z5,z102,z6]),(0,[z489,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z38])],[(0,[z2,z3,z4,z5,z11,z490,z6]),(0,[z2,z3,z4,z5,z58,z11,z6]),(1,[z51,z3,z4,z5,z11,z108]),(0,[z2,z3,z4,z5,z22,z6,z90]),(0,[z2,z421,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z491])],[(0,[z2,z3,z4,z492,z5,z11,z6]),(0,[z493,z2,z3,z4,z5,z11,z6]),(1,[z383,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z494]),(0,[z2,z3,z4,z5,z495,z11,z6]),(0,[z2,z3,z4,z165,z5,z22,z6])],[(0,[z34,z2,z3,z4,z5,z102,z6]),(0,[z2,z3,z4,z5,z11,z6,z496]),(0,[z2,z3,z4,z5,z11,z497,z6]),(0,[z70,z2,z3,z4,z5,z11,z6])],[(0,[z9,z2,z3,z180,z5,z11,z6]),(0,[z2,z3,z180,z56,z5,z11,z6]),(0,[z13,z2,z3,z4,z5,z28,z6]),(0,[z498,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z499,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z185,z37])]],
   [[(0,[z500,z2,z3,z4,z5,z11,z6]),(0,[z67,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z501,z11,z6])],[(0,[z33,z2,z3,z4,z5,z11,z6]),(0,[z502,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z503,z4,z5,z11,z6]),(0,[z13,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z504]),(0,[z505,z2,z3,z4,z5,z11,z6]),(0,[z2,z17,z3,z261,z4,z11,z6])],[(0,[z9,z2,z3,z57,z5,z11,z6]),(0,[z34,z2,z3,z4,z5,z28,z6]),(0,[z51,z2,z3,z4,z147,z11,z6]),(0,[z506,z2,z3,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z6,z117]),(0,[z2,z3,z4,z5,z310,z11,z6]),(0,[z507,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z306,z11,z6])],[(0,[z2,z3,z4,z508,z5,z11,z6]),(0,[z109,z2,z3,z157,z5,z11,z6]),(0,[z109,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z225,z157,z5,z6])],[(0,[z32,z2,z3,z4,z5,z509,z6]),(0,[z2,z3,z4,z5,z510,z11,z6]),(0,[z2,z3,z511,z4,z5,z11,z6]),(0,[z2,z3,z4,z512,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z513]),(0,[z2,z3,z4,z50,z5,z68,z6]),(0,[z2,z3,z4,z5,z11,z6,z117])],[(0,[z2,z3,z4,z5,z514,z11,z6]),(0,[z2,z3,z4,z83,z5,z28,z6]),(0,[z2,z3,z4,z5,z11,z6,z515]),(0,[z2,z3,z4,z5,z11,z516,z6])],[(0,[z2,z3,z517,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z518,z6]),(0,[z1,z2,z3,z519,z4,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6])],[(0,[z2,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z46,z6]),(0,[z2,z520,z3,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z521,z6]),(1,[z93,z2,z4,z5,z11,z90]),(0,[z2,z3,z4,z5,z166,z11,z6])]],
   [[(0,[z2,z522,z3,z4,z5,z11,z6]),(0,[z2,z16,z115,z3,z5,z11,z6]),(0,[z345,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z75,z11,z6]),(0,[z2,z3,z127,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z22,z523,z6])],[(0,[z154,z2,z229,z4,z5,z11,z6]),(0,[z524,z2,z3,z4,z5,z11,z6]),(0,[z79,z2,z3,z4,z5,z11,z6]),(0,[z525,z2,z3,z4,z5,z11,z6]),(0,[z25,z382,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z526,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z527,z6]),(0,[z2,z3,z4,z5,z528,z136,z6]),(0,[z529,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z189,z37])],[(0,[z530,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z531,z5,z11,z6]),(0,[z2,z3,z4,z532,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z11,z6]),(0,[z2,z14,z3,z4,z5,z6,z90]),(0,[z2,z3,z261,z4,z5,z22,z6]),(1,[z3,z4,z5,z11,z6,z223]),(0,[z2,z3,z4,z533,z5,z11,z6]),(0,[z112,z2,z3,z4,z5,z22,z6])],[(0,[z534,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z229,z3,z4,z5,z6]),(0,[z51,z34,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z535,z11,z6]),(0,[z2,z3,z4,z164,z5,z29,z6]),(0,[z1,z2,z3,z4,z5,z6,z37]),(0,[z2,z16,z3,z4,z5,z11,z6]),(0,[z536,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z537,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z147,z11,z6]),(0,[z2,z17,z3,z4,z164,z11,z6]),(0,[z2,z14,z3,z56,z4,z5,z6]),(0,[z538,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z204,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z6,z169]),(0,[z2,z539,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z188,z6]),(0,[z2,z3,z4,z5,z540,z11,z6]),(0,[z21,z2,z3,z4,z5,z6,z37]),(1,[z112,z2,z3,z4,z5,z37])],[(0,[z1,z154,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z541,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z126,z6]),(0,[z2,z3,z4,z5,z11,z6,z144]),(0,[z2,z3,z4,z5,z542,z11,z6]),(0,[z543,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z544])]],
   [[(0,[z545,z2,z3,z4,z5,z11,z6]),(0,[z2,z17,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z5,z28,z6,z37]),(0,[z2,z3,z4,z546,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(0,[z2,z3,z4,z5,z31,z6,z37]),(0,[z2,z3,z547,z4,z5,z11,z6]),(0,[z548,z2,z3,z4,z5,z11,z6])],[(1,[z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z549,z4,z5,z11,z6]),(0,[z550,z2,z3,z4,z5,z11,z6]),(0,[z551,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z429,z11,z6]),(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z2,z14,z3,z4,z165,z5,z6]),(0,[z2,z14,z3,z4,z5,z166,z6]),(0,[z2,z3,z4,z5,z11,z254,z6]),(0,[z2,z3,z552,z4,z5,z11,z6]),(0,[z67,z2,z3,z4,z5,z11,z188]),(0,[z2,z3,z4,z5,z11,z6,z553]),(0,[z2,z3,z4,z5,z11,z6,z554])],[(0,[z2,z3,z4,z5,z46,z6,z37]),(1,[z89,z2,z3,z5,z11,z6]),(0,[z2,z3,z4,z5,z8,z6,z37])],[(0,[z2,z3,z4,z555,z5,z11,z6]),(0,[z2,z3,z4,z5,z28,z126,z6])],[(0,[z2,z3,z4,z5,z11,z556,z6])],[(0,[z33,z3,z4,z5,z130,z11,z6]),(0,[z2,z14,z3,z4,z57,z5,z6]),(0,[z2,z3,z4,z5,z557,z11,z6]),(0,[z558,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z6,z108]),(0,[z109,z2,z3,z5,z11,z188,z6])],[(0,[z2,z3,z559,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z157,z5,z6]),(0,[z2,z3,z94,z4,z50,z5,z6]),(0,[z2,z3,z4,z5,z68,z6,z37]),(0,[z2,z101,z3,z4,z5,z6,z37])],[(0,[z9,z2,z3,z4,z5,z445,z6]),(0,[z2,z3,z4,z5,z11,z560,z6]),(0,[z1,z2,z3,z4,z5,z439,z6]),(0,[z2,z561,z3,z4,z5,z11,z6])]],
   [[(0,[z79,z2,z3,z57,z5,z11,z6]),(0,[z2,z3,z4,z562,z5,z11,z6]),(0,[z2,z264,z3,z4,z5,z11,z6]),(0,[z2,z3,z242,z4,z5,z11,z6]),(0,[z563,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z5,z254,z6]),(0,[z2,z3,z4,z5,z11,z564,z6]),(0,[z2,z3,z4,z5,z274,z11,z6]),(1,[z2,z3,z4,z5,z6,z553]),(0,[z2,z3,z4,z5,z11,z523,z6])],[(0,[z9,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z57,z5,z11,z6,z185]),(0,[z2,z3,z35,z4,z5,z6,z37]),(0,[z89,z2,z3,z4,z5,z11,z6])],[(0,[z565,z2,z3,z4,z5,z11,z6]),(0,[z566,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z28,z6]),(0,[z2,z35,z4,z164,z5,z11,z6]),(0,[z25,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z88,z4,z5,z11,z6]),(0,[z567,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z165,z5,z11,z6])],[(0,[z43,z2,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z44,z5,z22,z6]),(0,[z51,z2,z14,z3,z4,z5,z6]),(1,[z2,z3,z4,z526,z5,z6]),(0,[z568,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z160,z11,z6]),(0,[z2,z3,z4,z569,z5,z11,z6]),(0,[z141,z2,z3,z4,z5,z22,z6])],[(0,[z9,z2,z3,z4,z356,z11,z6]),(0,[z2,z3,z4,z50,z130,z11,z6]),(0,[z2,z3,z4,z5,z570,z11,z6]),(0,[z2,z16,z3,z4,z129,z11,z6]),(0,[z2,z3,z94,z4,z5,z6,z37])],[(0,[z79,z3,z4,z5,z130,z11,z6]),(0,[z1,z2,z3,z4,z5,z8,z6]),(0,[z1,z2,z4,z5,z11,z178,z6]),(0,[z2,z3,z4,z5,z571,z11,z6]),(0,[z2,z572,z3,z4,z5,z11,z6])],[(0,[z13,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z573,z4,z5,z11,z6]),(0,[z2,z3,z574,z4,z5,z11,z6]),(0,[z3,z4,z5,z11,z6,z366,z90]),(0,[z2,z575,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z576,z22,z6])],[(0,[z2,z3,z4,z5,z11,z6,z577]),(0,[z93,z2,z3,z4,z5,z11,z136]),(0,[z2,z3,z4,z578,z5,z11,z6]),(0,[z2,z3,z94,z4,z5,z126,z6]),(0,[z2,z3,z4,z5,z11,z6,z579])]],
   [[(0,[z2,z580,z3,z4,z5,z11,z6]),(0,[z2,z581,z3,z4,z5,z11,z6]),(0,[z582,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z583,z6]),(1,[z2,z17,z4,z164,z11,z6]),(0,[z2,z14,z17,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z584,z11,z6])],[(0,[z154,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z585]),(0,[z33,z2,z3,z549,z5,z11,z6]),(0,[z34,z2,z3,z4,z5,z11,z6]),(0,[z34,z3,z4,z5,z11,z46,z6]),(0,[z2,z3,z586,z4,z5,z11,z6])],[(1,[z2,z218,z3,z4,z11,z6]),(0,[z93,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z137]),(0,[z2,z3,z4,z5,z11,z587,z6])],[(1,[z154,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z588,z5,z11,z6])],[(0,[z2,z3,z180,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z11,z589,z6]),(0,[z2,z16,z3,z4,z5,z587,z6]),(0,[z2,z3,z4,z83,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z123,z6])],[(0,[z2,z3,z4,z5,z11,z6,z590]),(0,[z2,z3,z4,z591,z5,z11,z6]),(0,[z592,z2,z3,z4,z5,z11,z6]),(1,[z34,z3,z4,z5,z28,z6]),(0,[z2,z17,z3,z4,z5,z6,z37]),(0,[z1,z2,z3,z4,z5,z274,z6]),(0,[z2,z3,z4,z5,z11,z6,z379]),(0,[z2,z3,z4,z593,z5,z11,z6]),(0,[z594,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z6,z185]),(0,[z2,z3,z4,z165,z11,z8,z6])],[(0,[z595,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z596,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z597,z6]),(0,[z2,z3,z4,z5,z22,z113,z6])],[(0,[z2,z3,z4,z5,z598,z11,z6]),(0,[z112,z2,z14,z3,z4,z5,z6]),(0,[z2,z16,z3,z261,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z599,z6])]],
   [[(0,[z2,z14,z3,z180,z4,z5,z6]),(0,[z2,z3,z4,z600,z5,z11,z6]),(0,[z2,z3,z4,z601,z5,z11,z6]),(1,[z378,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z602,z11,z6]),(1,[z2,z3,z4,z5,z6,z137]),(1,[z2,z3,z4,z5,z587,z6])],[(0,[z603,z2,z3,z4,z5,z11,z6]),(0,[z34,z13,z3,z4,z5,z11,z6]),(0,[z2,z3,z604,z4,z5,z11,z6]),(0,[z2,z469,z3,z5,z26,z11,z6]),(0,[z2,z3,z4,z5,z11,z605,z6])],[(0,[z2,z3,z4,z606,z5,z11,z6]),(0,[z25,z2,z17,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z607,z6]),(0,[z112,z2,z3,z4,z5,z11,z37])],[(0,[z2,z3,z4,z5,z11,z509,z6]),(0,[z2,z608,z3,z4,z5,z11,z6]),(0,[z2,z315,z3,z4,z5,z11,z6]),(0,[z2,z41,z3,z4,z5,z6,z37])],[(0,[z2,z3,z609,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z610]),(0,[z2,z3,z4,z5,z166,z22,z6])],[(0,[z2,z3,z611,z4,z5,z11,z6]),(0,[z612,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z47,z5,z11,z6]),(0,[z2,z3,z4,z613,z5,z11,z6]),(0,[z614,z2,z3,z4,z5,z11,z6]),(0,[z615,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z56,z4,z5,z6,z37])],[(0,[z79,z2,z3,z4,z5,z22,z6]),(0,[z145,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z616,z6]),(0,[z2,z377,z3,z4,z5,z11,z6]),(0,[z21,z2,z3,z4,z5,z11,z117]),(0,[z2,z142,z3,z4,z5,z11,z6])]],
   [[(0,[z617,z2,z3,z4,z5,z11,z6]),(0,[z43,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z618,z5,z11,z6]),(0,[z109,z2,z3,z4,z5,z11,z6])],[(1,[z2,z3,z549,z5,z11,z6]),(0,[z51,z3,z4,z5,z11,z6,z108]),(1,[z2,z115,z35,z5,z11,z6]),(0,[z93,z2,z3,z4,z5,z200,z6]),(1,[z272,z2,z3,z4,z11,z6]),(0,[z2,z3,z4,z50,z5,z6,z37])],[(0,[z619,z2,z3,z4,z5,z11,z6]),(0,[z2,z620,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z528,z11,z6]),(0,[z2,z3,z4,z5,z188,z6,z553])],[(1,[z2,z3,z4,z5,z509,z6]),(0,[z2,z3,z4,z369,z5,z11,z6]),(0,[z2,z3,z4,z5,z621,z11,z6]),(0,[z25,z2,z16,z3,z4,z11,z6]),(0,[z2,z3,z622,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z5,z6,z185])],[(0,[z2,z3,z4,z5,z11,z623,z6]),(0,[z2,z3,z624,z4,z5,z11,z6]),(0,[z2,z3,z180,z4,z5,z22,z6]),(0,[z32,z1,z2,z3,z4,z5,z6]),(0,[z2,z14,z3,z4,z5,z113,z6])],[(0,[z32,z3,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z625,z11,z6]),(0,[z2,z3,z35,z4,z5,z209,z6]),(0,[z2,z3,z4,z5,z11,z626,z6]),(0,[z2,z3,z4,z526,z5,z26,z6]),(0,[z1,z2,z3,z4,z541,z5,z6]),(0,[z2,z3,z4,z5,z136,z6,z37]),(0,[z2,z3,z4,z5,z11,z627,z6]),(0,[z2,z3,z94,z4,z5,z274,z6]),(0,[z2,z3,z4,z5,z11,z6,z185])],[(0,[z9,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z628]),(0,[z1,z2,z3,z4,z5,z46,z6]),(0,[z629,z2,z3,z4,z5,z11,z6]),(0,[z1,z2,z61,z3,z4,z5,z6])],[(0,[z2,z14,z3,z261,z4,z5,z6]),(0,[z2,z14,z4,z5,z177,z11,z6])]],
   [[(0,[z33,z2,z3,z4,z436,z11,z6]),(0,[z2,z3,z4,z5,z274,z102,z6]),(1,[z615,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z158,z188,z6])],[(0,[z2,z3,z4,z5,z11,z630,z6]),(0,[z1,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z82,z90])],[(0,[z2,z3,z631,z4,z5,z11,z6]),(1,[z2,z3,z4,z356,z11,z6]),(0,[z51,z2,z3,z4,z5,z286,z6]),(0,[z45,z2,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z632,z5,z11,z6]),(1,[z121,z2,z4,z5,z11,z6]),(1,[z2,z3,z4,z5,z255,z6])],[(0,[z2,z3,z4,z5,z11,z633,z6]),(0,[z2,z3,z4,z44,z165,z11,z6]),(0,[z2,z3,z4,z5,z576,z11,z6]),(0,[z109,z2,z16,z3,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z177,z6]),(0,[z2,z3,z4,z5,z11,z6,z634]),(0,[z635,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z50,z68,z6])],[(1,[z2,z3,z4,z10,z11,z6]),(0,[z2,z115,z35,z4,z5,z11,z6]),(0,[z2,z149,z3,z4,z5,z11,z6]),(1,[z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z83,z5,z6]),(0,[z121,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z636])],[(0,[z2,z3,z4,z5,z28,z11,z6]),(0,[z2,z3,z4,z370,z5,z26,z6]),(0,[z2,z3,z56,z4,z5,z11,z185]),(0,[z2,z637,z3,z4,z5,z11,z6])],[(0,[z154,z2,z3,z4,z5,z11,z6]),(1,[z32,z3,z4,z44,z11,z6]),(0,[z2,z3,z4,z5,z11,z638,z6]),(0,[z639,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z274,z22,z6])],[(0,[z109,z2,z3,z57,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z640,z6]),(0,[z2,z3,z4,z5,z11,z641,z6]),(0,[z2,z14,z3,z4,z642,z5,z6])]],
   [[(0,[z643,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z644]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z493,z2,z14,z3,z4,z5,z6]),(0,[z2,z61,z3,z4,z5,z126,z6]),(0,[z2,z3,z56,z5,z11,z188,z6]),(0,[z2,z3,z4,z5,z6,z37,z399])],[(1,[z9,z3,z57,z5,z11,z6]),(0,[z2,z3,z4,z5,z130,z22,z6]),(0,[z48,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z645,z11,z6]),(0,[z2,z3,z4,z646,z5,z11,z6]),(0,[z2,z3,z4,z5,z647,z11,z6]),(0,[z2,z3,z4,z5,z11,z648,z6]),(0,[z378,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z11,z37]),(0,[z2,z3,z4,z5,z22,z649,z6])],[(0,[z2,z3,z4,z5,z292,z11,z6]),(0,[z650,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z651,z6]),(1,[z2,z3,z4,z5,z429,z6]),(0,[z2,z3,z4,z652,z5,z11,z6])],[(0,[z2,z3,z653,z4,z5,z11,z6]),(1,[z382,z3,z4,z5,z11,z6]),(0,[z25,z2,z3,z261,z4,z11,z6]),(0,[z2,z3,z4,z164,z5,z6,z37]),(0,[z2,z3,z4,z5,z11,z6,z223]),(0,[z2,z3,z4,z5,z11,z6,z654]),(0,[z2,z3,z4,z5,z22,z6,z6])],[(0,[z33,z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z655,z5,z11,z6]),(0,[z2,z3,z4,z83,z5,z102,z6]),(0,[z2,z3,z4,z202,z5,z11,z6]),(0,[z656,z2,z3,z4,z5,z11,z6])],[(0,[z2,z3,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z657,z11,z6]),(0,[z2,z3,z4,z658,z5,z11,z6]),(0,[z81,z1,z2,z3,z4,z5,z6]),(0,[z659,z2,z3,z4,z5,z11,z6])],[(0,[z2,z3,z35,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z660,z11,z6]),(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z661,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z5,z11,z188,z6,z185]),(0,[z2,z3,z4,z5,z6,z37,z37]),(0,[z2,z3,z4,z5,z22,z11,z113])],[(0,[z2,z14,z3,z64,z4,z5,z6]),(0,[z34,z2,z3,z4,z5,z22,z6]),(0,[z2,z448,z3,z4,z157,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z662]),(0,[z2,z3,z4,z5,z177,z6,z37])]],
   [[(1,[z2,z3,z4,z436,z11,z6]),(0,[z2,z663,z3,z4,z5,z11,z6]),(0,[z664,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z665]),(0,[z2,z3,z4,z5,z11,z666,z6]),(0,[z51,z2,z3,z4,z155,z11,z6]),(0,[z2,z14,z3,z4,z5,z31,z6]),(0,[z667,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z668,z5,z11,z6]),(0,[z2,z3,z4,z669,z5,z11,z6])],[(0,[z1,z2,z3,z4,z44,z5,z6]),(0,[z2,z14,z3,z4,z5,z177,z6]),(0,[z670,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z4,z5,z306,z6])],[(0,[z2,z3,z671,z4,z5,z11,z6]),(0,[z672,z2,z3,z4,z5,z11,z6]),(1,[z2,z3,z369,z5,z11,z6]),(0,[z2,z3,z4,z673,z5,z11,z6]),(0,[z2,z3,z5,z11,z6,z305,z90]),(1,[z2,z61,z3,z5,z126,z6]),(0,[z2,z3,z4,z83,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z674]),(0,[z2,z3,z4,z122,z5,z6,z37])],[(0,[z229,z3,z64,z4,z5,z11,z6]),(0,[z675,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z676,z5,z11,z6]),(0,[z2,z3,z4,z5,z677,z11,z6]),(0,[z2,z14,z14,z3,z4,z5,z6]),(0,[z2,z4,z5,z11,z136,z6,z90])],[(0,[z79,z2,z14,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z130,z6]),(0,[z678,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z521,z6]),(0,[z2,z3,z94,z4,z83,z5,z6])],[(0,[z2,z229,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z679,z11,z6]),(0,[z2,z61,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z5,z11,z6,z680]),(0,[z67,z2,z3,z4,z5,z6,z37])],[(0,[z353,z2,z14,z3,z4,z5,z6]),(0,[z681,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z416,z5,z11,z6])],[(0,[z51,z154,z3,z4,z5,z11,z6]),(0,[z25,z2,z3,z4,z164,z11,z6]),(0,[z1,z2,z3,z4,z129,z5,z6]),(0,[z2,z16,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z11,z6,z90])]],
   [[(0,[z2,z682,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z683,z5,z11,z6]),(0,[z2,z61,z3,z5,z11,z126,z6]),(0,[z2,z3,z4,z5,z11,z684,z6])],[(0,[z685,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z180,z4,z5,z11,z6]),(0,[z2,z3,z686,z4,z5,z11,z6]),(0,[z34,z2,z3,z4,z645,z11,z6]),(0,[z2,z3,z4,z645,z5,z11,z6]),(0,[z2,z687,z3,z4,z5,z11,z6]),(0,[z688,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z649,z6])],[(0,[z25,z2,z3,z4,z130,z11,z6]),(0,[z2,z17,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z689,z5,z11,z6])],[(0,[z79,z3,z180,z4,z5,z11,z6]),(0,[z2,z690,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z6,z6]),(1,[z2,z469,z3,z5,z11,z6]),(0,[z2,z3,z4,z5,z691,z11,z6])],[(0,[z692,z2,z3,z4,z5,z11,z6]),(1,[z2,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z166,z11,z68,z6]),(1,[z21,z2,z3,z4,z11,z117])],[(0,[z51,z229,z3,z4,z5,z11,z6]),(0,[z2,z3,z693,z4,z5,z11,z6]),(0,[z2,z3,z4,z199,z5,z11,z6]),(0,[z2,z41,z3,z4,z5,z11,z90]),(0,[z2,z3,z4,z5,z11,z694,z6]),(0,[z2,z142,z3,z4,z5,z22,z6])],[(0,[z109,z2,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z642,z5,z11,z6]),(0,[z2,z61,z3,z4,z5,z274,z6]),(1,[z2,z3,z56,z5,z11,z188]),(0,[z695,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z696,z6])],[(0,[z2,z3,z4,z5,z697,z11,z6]),(0,[z34,z3,z4,z5,z28,z11,z6]),(0,[z2,z3,z519,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z698,z11,z6])]],
   [[(1,[z2,z3,z4,z5,z6,z169]),(0,[z2,z3,z4,z699,z5,z11,z6]),(0,[z1,z2,z3,z4,z5,z178,z6])],[(0,[z33,z2,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z44,z11,z6,z117]),(0,[z1,z2,z3,z4,z5,z102,z6]),(1,[z2,z190,z4,z5,z11,z6]),(0,[z2,z41,z3,z4,z5,z11,z6]),(1,[z2,z3,z94,z5,z274,z6])],[(0,[z2,z14,z3,z4,z5,z267,z6]),(0,[z2,z3,z4,z5,z11,z6,z700]),(1,[z2,z3,z4,z83,z166,z6])],[(0,[z3,z4,z44,z5,z130,z11,z6]),(0,[z2,z14,z115,z3,z4,z5,z6]),(0,[z701,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z56,z4,z5,z11,z6]),(0,[z702,z2,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z130,z11,z6,z117]),(0,[z2,z17,z3,z4,z44,z11,z6]),(0,[z2,z3,z4,z44,z166,z11,z6]),(0,[z2,z3,z4,z703,z5,z11,z6]),(0,[z615,z3,z4,z5,z11,z6,z185]),(0,[z2,z3,z4,z704,z5,z11,z6])],[(0,[z2,z3,z705,z4,z5,z11,z6]),(0,[z32,z2,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z157,z5,z6,z37]),(0,[z2,z17,z3,z4,z11,z8,z6]),(0,[z27,z2,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z68,z6])],[(0,[z32,z3,z4,z57,z5,z11,z6]),(0,[z2,z3,z4,z5,z130,z11,z6]),(0,[z1,z13,z2,z3,z4,z5,z6]),(0,[z458,z2,z3,z4,z5,z11,z6]),(0,[z21,z2,z3,z4,z5,z442,z6])],[(0,[z1,z2,z3,z4,z5,z22,z6]),(1,[z2,z3,z4,z5,z528,z6]),(0,[z706,z2,z3,z4,z5,z11,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z107,z2,z4,z5,z11,z90]),(0,[z2,z3,z4,z5,z707,z6]),(0,[z377,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z202,z68,z6]),(0,[z2,z3,z56,z5,z22,z188])],[(0,[z2,z3,z4,z5,z708,z6]),(0,[z709,z3,z4,z5,z6,z37])],[(0,[z710,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z147,z11,z6]),(0,[z567,z3,z4,z5,z28,z6]),(0,[z2,z3,z4,z5,z22,z37])],[(0,[z711,z2,z3,z4,z5,z11]),(0,[z33,z229,z210,z5,z11,z6]),(0,[z2,z3,z4,z712,z11,z6]),(0,[z2,z190,z4,z5,z22,z6]),(0,[z2,z3,z4,z11,z713,z117])],[(0,[z2,z3,z4,z11,z6,z144]),(0,[z2,z3,z4,z5,z6,z714])],[(0,[z3,z4,z5,z11,z6,z715]),(0,[z25,z2,z14,z4,z26,z6]),(0,[z716,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z717,z5,z6]),(0,[z109,z2,z157,z5,z11,z6]),(0,[z345,z3,z88,z4,z5,z6]),(0,[z2,z3,z4,z165,z8,z37])],[(0,[z182,z3,z4,z155,z11,z6]),(0,[z2,z3,z4,z5,z718,z6]),(0,[z383,z14,z3,z4,z5,z6]),(0,[z179,z3,z4,z5,z6,z366]),(0,[z2,z3,z4,z5,z160,z6])],[(0,[z2,z3,z4,z5,z719,z6]),(0,[z2,z3,z4,z5,z720,z6]),(0,[z2,z3,z4,z645,z11,z6]),(0,[z2,z3,z4,z5,z721,z6]),(0,[z1,z2,z3,z4,z722,z6])],[(0,[z2,z3,z723,z5,z11,z6])],[],[(0,[z724,z2,z3,z4,z5,z11]),(0,[z2,z725,z3,z4,z5,z6]),(0,[z2,z3,z4,z726,z11,z6]),(0,[z2,z3,z242,z147,z11,z6]),(0,[z2,z727,z3,z4,z5,z6]),(0,[z2,z3,z4,z728,z5,z6])],[(0,[z2,z3,z4,z5,z729,z6]),(0,[z32,z14,z3,z4,z44,z6]),(0,[z730,z2,z3,z4,z5,z6]),(0,[z483,z3,z4,z5,z102,z6]),(0,[z2,z3,z4,z5,z6,z731])],[(0,[z2,z142,z4,z5,z336,z6])],[(0,[z2,z4,z164,z732,z11,z6]),(1,[z2,z3,z4,z5,z733])],[(0,[z1,z2,z3,z734,z5,z6])]],
   [[(0,[z2,z3,z4,z5,z11,z735]),(0,[z2,z3,z4,z5,z11,z736]),(0,[z2,z3,z4,z722,z11,z6]),(0,[z2,z16,z3,z31,z6,z37]),(0,[z2,z3,z4,z5,z737,z6]),(0,[z3,z4,z5,z24,z126,z6]),(0,[z2,z3,z4,z5,z306,z6])],[(0,[z2,z738,z3,z5,z11,z6]),(0,[z121,z2,z16,z5,z11,z6]),(0,[z2,z3,z4,z739,z5,z6]),(0,[z2,z61,z3,z5,z126,z6])],[],[(0,[z2,z740,z3,z4,z5,z6]),(0,[z3,z4,z5,z11,z46,z376]),(0,[z2,z264,z4,z147,z11,z6])],[(0,[z303,z2,z3,z4,z5,z37]),(0,[z2,z3,z4,z5,z11,z741])],[(0,[z2,z3,z4,z66,z22,z6])],[(0,[z2,z3,z4,z356,z53,z6]),(0,[z2,z3,z4,z40,z130,z6]),(0,[z2,z3,z4,z5,z6,z742])],[(0,[z743,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z11,z6,z744])],[(0,[z2,z3,z4,z5,z745,z6]),(0,[z3,z180,z369,z5,z11,z6]),(0,[z2,z218,z3,z4,z225,z6]),(0,[z2,z17,z4,z164,z429,z6]),(0,[z2,z746,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z747,z6]),(0,[z109,z2,z218,z5,z11,z6]),(0,[z2,z3,z4,z5,z748,z6]),(0,[z2,z3,z4,z749,z5,z6])],[(0,[z33,z229,z4,z5,z292,z6]),(0,[z32,z3,z4,z44,z54,z6]),(0,[z2,z3,z4,z40,z44,z6]),(0,[z2,z469,z3,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z750]),(0,[z1,z383,z3,z4,z5,z6]),(0,[z27,z3,z4,z5,z22,z6])],[(0,[z33,z229,z4,z5,z298,z6]),(0,[z2,z3,z4,z5,z751,z6]),(0,[z2,z3,z4,z752,z11,z6]),(0,[z2,z3,z4,z5,z753,z6])],[(0,[z383,z64,z4,z5,z11,z6]),(0,[z2,z754,z3,z4,z11,z6]),(0,[z34,z3,z4,z645,z28,z6]),(0,[z2,z41,z4,z5,z136,z37]),(0,[z2,z42,z3,z5,z6,z399])],[(0,[z2,z3,z4,z5,z113,z733])],[(0,[z2,z3,z755,z5,z11,z6]),(0,[z190,z4,z5,z130,z11,z6]),(0,[z179,z2,z3,z4,z5,z6]),(0,[z70,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z756,z22,z6])]],
   [[(0,[z2,z3,z4,z5,z6,z757]),(0,[z2,z14,z3,z369,z5,z6])],[(0,[z2,z3,z4,z5,z758,z6]),(0,[z1,z615,z3,z4,z5,z6]),(0,[z2,z3,z4,z50,z181,z6]),(0,[z2,z3,z4,z83,z166,z6]),(0,[z112,z2,z3,z4,z5,z733])],[(0,[z25,z2,z586,z4,z11,z6]),(0,[z2,z4,z5,z11,z6,z741]),(0,[z2,z3,z4,z759,z6,z37])],[],[(0,[z2,z3,z4,z5,z6,z760]),(0,[z2,z3,z4,z761,z5,z11]),(0,[z2,z469,z3,z526,z5,z6]),(1,[z2,z3,z4,z762,z6])],[(0,[z763,z2,z3,z4,z5,z6]),(0,[z2,z3,z764,z5,z11,z6]),(0,[z2,z101,z3,z4,z5,z6]),(0,[z765,z2,z3,z4,z5,z6])],[(0,[z109,z2,z453,z5,z11,z6]),(0,[z3,z4,z5,z11,z6,z766])],[(0,[z2,z3,z369,z5,z58,z6]),(0,[z383,z3,z4,z5,z6,z82])],[(0,[z2,z14,z4,z5,z75,z6])],[(0,[z154,z97,z64,z4,z5,z6]),(0,[z25,z2,z4,z26,z11,z6]),(0,[z145,z767,z3,z4,z5,z6]),(0,[z3,z4,z389,z5,z24,z6])],[(0,[z2,z3,z4,z5,z22,z343]),(0,[z2,z3,z768,z5,z11,z6])],[(0,[z33,z229,z14,z4,z5,z6]),(0,[z2,z3,z4,z155,z22,z6]),(0,[z1,z382,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z769,z6]),(0,[z2,z16,z3,z31,z310,z6]),(0,[z2,z3,z5,z770,z11,z6])],[(0,[z109,z1,z2,z157,z5,z6]),(0,[z3,z4,z5,z11,z6,z771])],[(0,[z2,z772,z3,z4,z5,z6]),(0,[z2,z3,z4,z773,z11,z6]),(0,[z2,z14,z3,z5,z6,z305]),(0,[z2,z3,z4,z5,z774,z6]),(0,[z3,z4,z5,z22,z775,z6])],[(0,[z776,z2,z3,z4,z5,z6]),(0,[z2,z3,z242,z5,z6,z37]),(0,[z2,z777,z3,z4,z5,z6])],[(0,[z426,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z5,z6,z778]),(0,[z3,z4,z167,z5,z22,z6]),(0,[z2,z3,z4,z779,z11,z6])]],
   [[(0,[z2,z682,z3,z31,z11,z6])],[(0,[z2,z3,z780,z5,z11,z6]),(0,[z45,z3,z4,z5,z46,z169]),(0,[z1,z2,z4,z5,z392,z6])],[],[(0,[z9,z3,z57,z10,z11,z6]),(0,[z781,z2,z3,z4,z5,z6]),(0,[z109,z2,z14,z157,z5,z6]),(0,[z2,z41,z3,z4,z5,z342]),(0,[z67,z2,z3,z5,z185,z37])],[],[(0,[z67,z2,z3,z5,z22,z185])],[(0,[z782,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z783]),(0,[z2,z264,z4,z5,z6,z37]),(0,[z1,z89,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z784,z6])],[],[(0,[z2,z3,z4,z785,z5,z6]),(0,[z33,z229,z4,z98,z11,z6]),(0,[z536,z2,z14,z4,z5,z6]),(0,[z70,z3,z4,z5,z24,z6])],[(0,[z2,z3,z4,z11,z6,z786])],[(0,[z3,z4,z5,z24,z11,z6]),(0,[z222,z30,z3,z4,z5,z6]),(0,[z635,z1,z2,z4,z5,z6])],[(0,[z787,z2,z3,z4,z5,z6]),(0,[z2,z3,z369,z147,z11,z6]),(0,[z2,z3,z5,z368,z6,z37]),(0,[z767,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z788,z6])],[(0,[z2,z789,z3,z5,z11,z6]),(0,[z2,z3,z4,z5,z289,z6]),(0,[z2,z3,z4,z790,z11,z6]),(0,[z2,z3,z4,z5,z791,z6]),(0,[z89,z2,z3,z5,z6,z82])],[(0,[z2,z3,z4,z5,z6,z792]),(0,[z688,z3,z4,z130,z11,z6]),(0,[z793,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z409,z37]),(0,[z383,z3,z5,z11,z6,z305]),(0,[z2,z794,z3,z4,z5,z6]),(0,[z795,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z796,z6]),(0,[z797,z2,z190,z4,z5,z6]),(0,[z1,z2,z3,z4,z165,z8]),(0,[z798,z3,z4,z5,z6,z409])],[(0,[z2,z3,z799,z5,z11,z6])]],
   [[(0,[z661,z3,z4,z5,z28,z6]),(0,[z2,z3,z4,z5,z310,z6]),(0,[z2,z3,z4,z5,z7,z6])],[(0,[z43,z14,z3,z4,z130,z6]),(0,[z45,z3,z4,z5,z335,z46]),(0,[z1,z2,z3,z4,z5,z800]),(0,[z2,z3,z4,z5,z801,z6])],[(0,[z2,z3,z4,z802,z11,z6]),(0,[z1,z2,z4,z5,z178,z6])],[(0,[z2,z3,z4,z83,z15,z6]),(0,[z2,z218,z14,z3,z4,z6]),(0,[z2,z469,z17,z3,z11,z6]),(0,[z2,z3,z4,z5,z6,z803])],[(0,[z2,z3,z4,z5,z11,z804])],[(0,[z2,z3,z4,z5,z805,z6])],[(0,[z383,z89,z3,z5,z11,z6]),(0,[z2,z101,z4,z5,z6,z153])],[(0,[z2,z3,z4,z5,z6,z806]),(0,[z1,z377,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z807,z6]),(0,[z13,z3,z4,z5,z24,z6]),(0,[z808,z2,z264,z4,z5,z6]),(0,[z2,z3,z4,z5,z809,z6]),(0,[z3,z4,z5,z11,z6,z810])],[(0,[z2,z3,z4,z5,z158,z6])],[(0,[z2,z3,z4,z811,z11,z6]),(0,[z315,z3,z4,z5,z6,z37]),(0,[z812,z3,z4,z5,z11,z6]),(0,[z93,z2,z3,z4,z5,z342])],[(0,[z33,z229,z4,z5,z22,z6]),(0,[z813,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z83,z6,z96])],[(0,[z3,z4,z814,z5,z11,z6]),(0,[z815,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z816,z11,z6]),(0,[z817,z3,z4,z5,z11,z6])],[(0,[z530,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z5,z818,z6]),(0,[z819,z3,z4,z5,z11,z6]),(0,[z820,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z22,z434])],[(0,[z2,z3,z4,z5,z821,z6]),(0,[z2,z3,z4,z5,z6,z822]),(0,[z27,z3,z4,z5,z587,z6]),(0,[z2,z3,z4,z5,z823,z6]),(0,[z2,z3,z390,z5,z274,z6])]],
   [[(0,[z2,z3,z4,z5,z824,z6]),(0,[z2,z115,z596,z5,z11,z6]),(0,[z2,z3,z4,z825,z11,z6]),(0,[z2,z3,z4,z5,z826,z6]),(0,[z2,z3,z261,z129,z6,z37]),(0,[z3,z4,z5,z274,z24,z6])],[(0,[z2,z3,z4,z827,z11,z6]),(0,[z1,z2,z308,z4,z5,z6]),(0,[z2,z828,z3,z4,z5,z6]),(0,[z829,z2,z3,z4,z11,z6]),(0,[z830,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z831])],[(0,[z538,z229,z4,z5,z11,z6]),(0,[z272,z2,z14,z3,z4,z6]),(0,[z2,z3,z4,z832,z6,z37])],[(0,[z1,z2,z190,z4,z5,z6]),(0,[z2,z3,z833,z4,z5,z6])],[(0,[z51,z3,z4,z5,z445,z6]),(0,[z2,z3,z4,z165,z11,z8])],[(0,[z51,z3,z4,z5,z11,z125]),(0,[z3,z5,z11,z6,z305,z366])],[(0,[z2,z3,z4,z199,z11,z6]),(0,[z1,z3,z4,z5,z6,z366]),(0,[z2,z3,z4,z83,z215,z6])],[(0,[z302,z3,z4,z5,z102,z6]),(0,[z45,z3,z4,z5,z22,z46])],[(0,[z1,z2,z3,z4,z436,z6]),(0,[z797,z2,z3,z4,z5,z6]),(0,[z834,z2,z3,z4,z5,z6]),(0,[z2,z3,z5,z11,z6,z835]),(0,[z2,z836,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z837,z6])],[(0,[z1,z2,z3,z4,z98,z6]),(0,[z51,z3,z4,z356,z11,z6]),(0,[z2,z3,z4,z5,z838,z6])],[(0,[z2,z3,z4,z50,z346,z6]),(0,[z377,z3,z4,z31,z11,z6]),(1,[z2,z3,z5,z11,z831])],[(0,[z1,z2,z3,z210,z5,z6]),(0,[z2,z3,z4,z147,z58,z6]),(0,[z3,z4,z5,z839,z11,z6])],[(0,[z2,z3,z4,z11,z6,z840]),(0,[z2,z115,z35,z5,z289,z6]),(0,[z2,z3,z4,z5,z841,z6]),(0,[z2,z3,z842,z4,z5,z6]),(1,[z2,z3,z4,z11,z713])],[(0,[z2,z3,z4,z5,z843,z6]),(0,[z2,z3,z4,z844,z11,z6]),(0,[z2,z845,z3,z4,z5,z6]),(0,[z846,z3,z4,z5,z11,z6])],[(0,[z1,z2,z3,z4,z5,z847]),(0,[z2,z3,z4,z848,z5,z6])],[]],
   [[(0,[z2,z3,z4,z5,z849,z6]),(0,[z2,z3,z850,z5,z11,z6]),(0,[z51,z3,z4,z5,z11,z644]),(0,[z179,z2,z3,z4,z6,z144])],[(0,[z2,z3,z4,z5,z851,z6]),(0,[z2,z3,z261,z632,z11,z6]),(0,[z2,z41,z4,z5,z136,z137]),(0,[z852,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z335,z6]),(0,[z86,z212,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z853]),(0,[z3,z854,z4,z5,z11,z6]),(0,[z93,z2,z4,z5,z200,z90]),(0,[z2,z16,z3,z31,z22,z6]),(0,[z2,z3,z4,z5,z855,z6])],[(0,[z34,z3,z4,z5,z58,z6]),(0,[z109,z2,z218,z157,z11,z6]),(0,[z1,z2,z142,z4,z5,z6]),(0,[z2,z41,z4,z5,z22,z136]),(0,[z2,z3,z4,z5,z856,z6])],[(0,[z2,z3,z4,z5,z6,z857]),(0,[z2,z3,z4,z858,z11,z6]),(0,[z2,z3,z4,z5,z859,z6])],[],[(1,[z3,z4,z5,z11,z860]),(0,[z142,z3,z4,z5,z24,z6])],[(0,[z2,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z5,z861,z6]),(0,[z2,z3,z4,z5,z862,z6]),(0,[z2,z3,z863,z5,z11,z6]),(0,[z2,z61,z3,z47,z5,z6]),(0,[z2,z3,z4,z864,z5,z6]),(0,[z145,z2,z4,z5,z123,z6])],[(0,[z2,z3,z4,z865,z11,z6]),(0,[z2,z14,z573,z4,z5,z6]),(0,[z2,z14,z3,z4,z199,z6]),(0,[z2,z3,z4,z83,z267,z6]),(0,[z121,z2,z16,z3,z11,z6])],[(0,[z2,z3,z94,z642,z5,z6]),(0,[z866,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z867,z6]),(0,[z43,z3,z4,z130,z11,z6]),(0,[z1,z2,z14,z4,z5,z6]),(0,[z2,z3,z4,z5,z868,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z22,z371])],[(0,[z1,z2,z3,z4,z10,z6]),(0,[z441,z2,z3,z4,z5,z37])],[(0,[z2,z3,z4,z5,z869,z6]),(0,[z3,z4,z588,z130,z11,z6])]],
   [[(0,[z2,z3,z4,z5,z6,z870]),(0,[z2,z3,z5,z6,z37,z871]),(0,[z2,z3,z4,z6,z744,z37])],[(0,[z872,z3,z4,z5,z11,z6]),(0,[z2,z3,z370,z5,z368,z6]),(0,[z70,z3,z4,z5,z22,z6])],[(0,[z109,z2,z218,z3,z11,z6])],[(0,[z2,z3,z210,z5,z11,z6]),(0,[z25,z2,z59,z4,z11,z6]),(0,[z2,z3,z4,z5,z873,z6]),(0,[z2,z3,z874,z5,z11,z6])],[(0,[z1,z27,z3,z4,z5,z6])],[(0,[z382,z3,z4,z5,z875,z6]),(0,[z1,z2,z406,z4,z5,z6])],[(0,[z2,z3,z4,z876,z5,z6]),(0,[z2,z3,z4,z5,z6,z877]),(0,[z2,z3,z4,z878,z11,z6])],[(0,[z2,z3,z4,z5,z879,z6])],[(0,[z2,z3,z4,z5,z6,z880]),(0,[z2,z469,z14,z3,z5,z6]),(0,[z3,z4,z5,z11,z6,z881])],[(0,[z79,z3,z180,z5,z11,z6]),(0,[z2,z3,z4,z5,z882,z6]),(0,[z2,z3,z4,z676,z5,z37]),(0,[z2,z218,z3,z4,z6,z37]),(0,[z383,z179,z3,z4,z5,z6]),(0,[z3,z4,z5,z22,z24,z37])],[(0,[z27,z14,z3,z4,z5,z6])],[(0,[z3,z4,z66,z11,z46,z6]),(0,[z883,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z689,z5,z6]),(0,[z67,z2,z3,z5,z255,z185])],[(0,[z2,z3,z884,z5,z11,z6]),(0,[z121,z2,z4,z130,z11,z6]),(0,[z2,z3,z4,z5,z6,z885])],[(0,[z3,z4,z57,z356,z11,z6]),(0,[z2,z3,z4,z5,z472,z37]),(0,[z2,z886,z3,z4,z5,z6])],[(0,[z2,z14,z3,z4,z155,z6]),(0,[z2,z3,z887,z4,z5,z6]),(0,[z2,z3,z5,z6,z82,z305]),(0,[z888,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z889,z11,z6]),(0,[z2,z3,z4,z890,z11,z6])]],
   [[(0,[z2,z891,z3,z5,z11,z6])],[(0,[z383,z3,z4,z5,z11,z6]),(0,[z2,z3,z242,z5,z22,z6]),(0,[z2,z3,z4,z5,z892,z6])],[(0,[z2,z190,z4,z5,z286,z6]),(0,[z2,z61,z3,z5,z649,z6])],[],[(0,[z3,z369,z5,z130,z11,z6]),(0,[z30,z3,z4,z5,z28,z6])],[(0,[z2,z3,z549,z98,z11,z6]),(0,[z615,z3,z180,z5,z11,z6]),(0,[z382,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z770,z11,z6])],[(0,[z2,z3,z4,z5,z875,z6])],[(0,[z2,z3,z4,z893,z11,z6]),(0,[z2,z894,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z82,z366])],[(0,[z2,z3,z549,z5,z6,z37]),(0,[z2,z3,z4,z895,z5,z6]),(0,[z79,z3,z896,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z897]),(0,[z1,z2,z690,z4,z5,z6]),(0,[z2,z115,z898,z5,z11,z6]),(0,[z2,z115,z35,z5,z6,z37]),(0,[z272,z2,z3,z4,z6,z37]),(0,[z2,z3,z4,z5,z899,z6]),(0,[z2,z3,z4,z5,z111,z37])],[(0,[z2,z3,z900,z5,z11,z6]),(0,[z2,z3,z901,z4,z5,z6]),(0,[z2,z264,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z292,z6]),(0,[z2,z3,z4,z902,z5,z6])],[(0,[z2,z3,z4,z5,z298,z6]),(0,[z2,z3,z4,z5,z6,z903]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z93,z2,z4,z5,z90,z37]),(0,[z2,z3,z4,z5,z905,z6])],[],[(0,[z2,z3,z4,z5,z11,z906]),(0,[z2,z3,z4,z907,z11,z6])],[(0,[z9,z3,z896,z5,z11,z6]),(0,[z2,z14,z264,z4,z5,z6]),(0,[z2,z3,z5,z368,z22,z6]),(1,[z2,z3,z770,z11,z6]),(0,[z2,z4,z5,z11,z6,z908])],[(0,[z1,z2,z3,z4,z66,z6]),(0,[z2,z3,z5,z11,z831,z185])]],
   [[(0,[z2,z3,z909,z5,z11,z6]),(0,[z2,z190,z4,z155,z11,z6]),(0,[z2,z16,z3,z770,z11,z6]),(0,[z910,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z356,z6,z37]),(0,[z678,z3,z57,z5,z11,z6]),(0,[z2,z3,z4,z5,z11,z911]),(0,[z2,z3,z4,z912,z5,z6]),(1,[z2,z4,z5,z913,z6]),(0,[z2,z16,z3,z40,z31,z6]),(0,[z121,z2,z4,z5,z6,z37]),(0,[z145,z3,z4,z5,z24,z6]),(0,[z2,z3,z4,z5,z22,z733])],[(0,[z2,z3,z4,z5,z914,z6]),(0,[z915,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z916,z6]),(0,[z2,z3,z4,z917,z5,z6]),(0,[z25,z315,z4,z26,z11,z6])],[(0,[z21,z2,z3,z4,z11,z713])],[(0,[z2,z3,z4,z918,z11,z6]),(0,[z919,z2,z3,z4,z11,z6]),(0,[z51,z3,z4,z5,z509,z6]),(0,[z3,z4,z5,z11,z860,z108]),(0,[z2,z3,z4,z5,z920,z6])],[(0,[z2,z3,z4,z921,z11,z6]),(0,[z32,z3,z210,z5,z11,z6]),(0,[z2,z4,z5,z922,z11,z6]),(0,[z89,z2,z3,z5,z11,z6]),(0,[z2,z3,z5,z923,z11,z6]),(0,[z2,z3,z924,z5,z11,z6])],[(0,[z154,z190,z4,z5,z11,z6]),(0,[z182,z3,z4,z5,z11,z6]),(0,[z3,z4,z5,z925,z11,z6])],[(0,[z2,z3,z4,z645,z6,z37]),(0,[z1,z2,z3,z5,z368,z6]),(0,[z2,z14,z4,z5,z177,z6]),(0,[z2,z16,z3,z31,z587,z6]),(0,[z2,z926,z4,z5,z11,z6])],[(0,[z3,z4,z201,z130,z11,z6]),(0,[z2,z3,z4,z5,z927,z6]),(0,[z2,z928,z4,z5,z11,z6]),(0,[z2,z3,z94,z477,z5,z6]),(0,[z2,z3,z4,z416,z6,z96])],[(0,[z382,z3,z4,z5,z6,z37])],[(0,[z2,z4,z5,z75,z11,z6]),(0,[z2,z929,z3,z4,z11,z6]),(0,[z135,z143,z3,z4,z5,z6]),(0,[z3,z4,z930,z5,z11,z6])],[(0,[z154,z63,z64,z4,z5,z6]),(0,[z931,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z254,z6])],[(0,[z2,z932,z3,z4,z5,z6]),(0,[z315,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z6,z933]),(0,[z2,z3,z4,z22,z934,z6])],[(0,[z33,z229,z4,z436,z11,z6]),(0,[z2,z3,z4,z5,z935,z6])]],
   [[(0,[z2,z3,z936,z5,z11,z6]),(0,[z2,z3,z4,z5,z937,z6]),(0,[z3,z4,z155,z130,z11,z6]),(0,[z2,z3,z4,z5,z125,z37]),(0,[z938,z3,z4,z5,z11,z6])],[(1,[z3,z4,z939,z11,z6]),(0,[z2,z3,z369,z5,z6,z37]),(0,[z2,z14,z3,z56,z5,z188])],[(0,[z2,z3,z4,z5,z940,z6])],[(0,[z2,z3,z261,z129,z22,z6])],[(0,[z2,z941,z3,z4,z5,z6]),(0,[z2,z3,z4,z942,z5,z6]),(0,[z2,z17,z4,z164,z11,z6])],[(0,[z2,z14,z3,z4,z356,z6]),(0,[z2,z3,z4,z5,z943,z6]),(0,[z1,z2,z3,z4,z5,z735]),(0,[z121,z2,z16,z4,z11,z6]),(0,[z615,z3,z4,z944,z11,z6]),(0,[z945,z2,z3,z5,z11,z6]),(0,[z2,z3,z4,z389,z523,z6])],[(0,[z51,z3,z4,z5,z22,z108])],[(0,[z154,z64,z4,z5,z11,z6]),(0,[z2,z3,z4,z946,z5,z6]),(0,[z2,z3,z4,z5,z947,z6]),(0,[z1,z2,z469,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z948]),(0,[z182,z1,z3,z4,z5,z6])],[(0,[z2,z3,z4,z98,z11,z6]),(0,[z2,z3,z4,z5,z6,z949]),(0,[z2,z3,z4,z5,z950,z6]),(0,[z2,z3,z4,z5,z951,z6]),(1,[z25,z2,z469,z11,z6]),(0,[z2,z3,z4,z5,z952,z6])],[(0,[z2,z3,z4,z5,z953,z6]),(0,[z2,z3,z954,z5,z11,z6])],[(0,[z2,z3,z549,z5,z292,z6]),(0,[z2,z3,z955,z5,z11,z6]),(0,[z14,z3,z4,z167,z5,z6]),(0,[z2,z4,z5,z177,z913,z6]),(0,[z2,z3,z4,z956,z11,z6]),(0,[z2,z957,z4,z5,z11,z6]),(0,[z2,z3,z5,z958,z126,z6])],[(0,[z2,z3,z549,z5,z298,z6]),(0,[z2,z3,z4,z5,z959,z6]),(0,[z2,z3,z4,z752,z6,z37])],[(0,[z2,z3,z4,z5,z960,z6]),(0,[z2,z3,z526,z5,z368,z6]),(0,[z2,z3,z4,z5,z6,z409]),(0,[z21,z2,z3,z4,z117,z37])],[(0,[z109,z2,z218,z4,z11,z6]),(0,[z2,z3,z4,z5,z6,z137]),(0,[z798,z14,z3,z4,z5,z6]),(0,[z2,z101,z3,z4,z5,z521]),(0,[z2,z3,z4,z5,z587,z6])],[(0,[z51,z3,z4,z5,z11,z375]),(0,[z2,z3,z4,z5,z961,z6]),(0,[z2,z4,z898,z5,z11,z6]),(0,[z2,z962,z3,z5,z11,z6])],[(0,[z2,z3,z4,z225,z199,z6]),(0,[z1,z2,z3,z4,z5,z750]),(0,[z1,z2,z3,z4,z6,z144]),(0,[z2,z3,z4,z5,z231,z37])]],
   [[(0,[z476,z3,z4,z130,z11,z6]),(0,[z2,z4,z164,z679,z11,z6]),(0,[z2,z4,z5,z11,z136,z741])],[(0,[z3,z4,z5,z6,z37,z810])],[(0,[z1,z2,z3,z4,z645,z6]),(0,[z3,z4,z963,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z674])],[(0,[z964,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z965,z6]),(0,[z966,z3,z4,z5,z11,z6]),(0,[z2,z898,z157,z5,z11,z6]),(0,[z967,z2,z3,z4,z5,z6])],[(0,[z2,z3,z968,z5,z11,z6]),(0,[z2,z4,z204,z5,z75,z6])],[(0,[z34,z3,z4,z5,z24,z6]),(0,[z1,z969,z3,z4,z5,z6])],[(0,[z2,z970,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z22,z439]),(0,[z3,z4,z971,z5,z11,z6])],[(0,[z45,z14,z3,z4,z5,z46]),(0,[z2,z3,z4,z972,z5,z6])],[(0,[z1,z2,z3,z242,z5,z6]),(0,[z2,z3,z5,z274,z958,z6])],[(0,[z2,z3,z4,z5,z6,z973]),(0,[z25,z2,z4,z26,z6,z37]),(0,[z93,z272,z2,z4,z11,z90])],[],[(0,[z2,z3,z4,z5,z22,z6]),(0,[z229,z782,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z974,z6]),(0,[z2,z3,z4,z5,z975,z6])],[(0,[z615,z3,z4,z5,z11,z6]),(0,[z976,z3,z4,z5,z11,z6]),(0,[z112,z2,z3,z4,z5,z342]),(0,[z2,z3,z4,z5,z6,z977]),(0,[z3,z4,z5,z11,z6,z978])],[(0,[z377,z3,z4,z5,z11,z6]),(0,[z45,z3,z4,z5,z46,z37]),(0,[z121,z1,z2,z4,z5,z6]),(0,[z2,z149,z3,z4,z202,z6])],[(0,[z2,z14,z190,z4,z5,z6]),(0,[z2,z979,z3,z4,z5,z6]),(0,[z2,z3,z4,z980,z11,z6]),(0,[z93,z383,z4,z5,z11,z90]),(0,[z2,z3,z4,z5,z255,z6])],[(0,[z2,z3,z4,z981,z11,z6]),(0,[z982,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z983,z6]),(0,[z984,z3,z4,z5,z11,z6]),(0,[z2,z142,z4,z5,z177,z6])]],
   [[(0,[z33,z782,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z11,z985]),(0,[z2,z3,z4,z5,z986,z6]),(0,[z3,z4,z5,z22,z6,z223])],[(0,[z1,z2,z3,z549,z5,z6]),(0,[z2,z3,z4,z5,z987,z6]),(0,[z32,z3,z4,z44,z11,z6]),(0,[z1,z2,z3,z988,z5,z6]),(0,[z2,z3,z11,z6,z144,z305]),(0,[z121,z2,z129,z5,z11,z6]),(0,[z2,z989,z3,z4,z5,z6])],[(0,[z3,z180,z5,z11,z6,z233]),(0,[z2,z3,z4,z5,z282,z37]),(0,[z2,z3,z4,z5,z22,z583]),(0,[z2,z990,z264,z4,z5,z6]),(0,[z45,z2,z3,z4,z5,z342]),(0,[z2,z3,z991,z4,z5,z6])],[(0,[z2,z3,z4,z5,z992,z6]),(0,[z45,z3,z4,z5,z11,z860]),(0,[z121,z2,z14,z4,z5,z6]),(0,[z2,z3,z993,z4,z11,z6]),(0,[z3,z4,z5,z24,z649,z6])],[(0,[z9,z3,z57,z5,z11,z6]),(0,[z424,z2,z14,z4,z5,z6]),(0,[z3,z4,z994,z5,z11,z6]),(0,[z48,z3,z4,z5,z24,z6])],[(0,[z2,z3,z4,z5,z6,z995]),(0,[z1,z2,z4,z5,z913,z6]),(0,[z2,z3,z4,z996,z5,z6]),(0,[z997,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z998,z6]),(0,[z2,z3,z4,z5,z999,z6])],[(0,[z2,z3,z4,z1000,z5,z6]),(0,[z121,z2,z4,z44,z11,z6]),(0,[z51,z190,z4,z5,z11,z108]),(0,[z73,z2,z3,z4,z5,z342])],[(0,[z2,z3,z4,z5,z11,z1001])],[(0,[z2,z218,z35,z4,z11,z6]),(0,[z2,z3,z4,z5,z358,z37]),(0,[z2,z3,z4,z5,z1002,z6])],[(0,[z615,z3,z57,z5,z11,z6]),(0,[z2,z1003,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z1004]),(0,[z2,z14,z3,z4,z921,z6]),(0,[z3,z4,z11,z6,z144,z366])],[(0,[z268,z64,z4,z5,z11,z6]),(0,[z2,z218,z3,z4,z22,z6]),(0,[z2,z3,z4,z6,z786,z37])],[(0,[z1005,z3,z4,z5,z11,z6]),(0,[z182,z3,z4,z5,z1006,z6])],[(0,[z2,z3,z1007,z5,z11,z6]),(0,[z93,z2,z4,z5,z11,z90]),(0,[z2,z3,z4,z5,z1008,z6])],[(0,[z2,z3,z4,z1009,z11,z6]),(0,[z2,z3,z4,z5,z317,z37]),(0,[z14,z3,z4,z5,z6,z223]),(0,[z2,z41,z4,z5,z528,z136])]],
   [[(0,[z2,z3,z4,z5,z6,z1010]),(0,[z378,z2,z35,z4,z5,z6])],[(0,[z3,z4,z5,z11,z6,z223]),(0,[z382,z3,z4,z44,z11,z6]),(0,[z70,z14,z3,z4,z5,z6])],[(0,[z3,z4,z5,z1011,z102,z6]),(0,[z2,z1012,z3,z4,z5,z6]),(0,[z25,z2,z4,z370,z26,z6]),(0,[z458,z3,z4,z5,z6,z62])],[(0,[z2,z16,z3,z385,z11,z6]),(0,[z2,z3,z4,z11,z1013,z6]),(0,[z1014,z2,z3,z4,z5,z6]),(0,[z70,z3,z4,z1015,z22,z6])],[(0,[z2,z3,z4,z1016,z5,z6]),(0,[z3,z4,z676,z5,z11,z46]),(0,[z1017,z121,z2,z4,z5,z6])],[(0,[z2,z3,z411,z129,z11,z6]),(0,[z2,z3,z4,z1018,z11,z6]),(0,[z808,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z147,z6,z37]),(0,[z2,z115,z5,z52,z11,z6]),(0,[z89,z179,z2,z3,z5,z6])],[(0,[z2,z1019,z4,z5,z11,z6]),(0,[z2,z313,z3,z5,z126,z6])],[(0,[z2,z3,z4,z5,z22,z92]),(0,[z1,z315,z3,z4,z5,z6]),(0,[z2,z3,z4,z541,z166,z6])],[(0,[z34,z3,z4,z5,z335,z6])],[(0,[z79,z3,z4,z356,z11,z6]),(0,[z32,z1,z3,z4,z44,z6]),(0,[z109,z2,z157,z5,z6,z37]),(0,[z1,z2,z3,z4,z5,z804]),(0,[z2,z101,z41,z4,z5,z136]),(0,[z2,z3,z4,z1020,z5,z6]),(0,[z2,z3,z4,z1021,z22,z6])],[(0,[z2,z3,z4,z5,z1022,z6]),(0,[z2,z3,z4,z5,z1023,z6]),(1,[z3,z4,z5,z1011,z6]),(0,[z2,z3,z4,z1024,z11,z6])],[(0,[z2,z3,z549,z5,z22,z6]),(0,[z229,z4,z5,z11,z6,z172]),(0,[z2,z1025,z3,z4,z5,z6]),(0,[z2,z115,z35,z5,z22,z6]),(0,[z2,z3,z4,z5,z188,z342]),(0,[z272,z2,z3,z4,z22,z6])],[(0,[z2,z3,z4,z5,z6,z1026])],[(0,[z2,z190,z4,z5,z11,z6]),(0,[z2,z1027,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1028,z6])],[(0,[z329,z2,z3,z4,z11,z117]),(0,[z1,z2,z41,z4,z5,z136]),(0,[z3,z4,z5,z6,z771,z409])],[(0,[z2,z3,z4,z5,z11,z1029]),(0,[z2,z3,z4,z5,z1030,z6]),(0,[z27,z16,z3,z31,z11,z6]),(0,[z2,z3,z4,z5,z6,z553])]],
   [[(0,[z2,z3,z4,z5,z11,z860]),(0,[z21,z2,z3,z4,z11,z358]),(0,[z1031,z2,z3,z4,z5,z6])],[(0,[z2,z1032,z3,z4,z5,z6]),(0,[z2,z3,z5,z22,z1033,z6])],[],[(0,[z2,z3,z4,z5,z6,z1034]),(0,[z2,z3,z4,z5,z342,z117])],[(0,[z2,z3,z4,z356,z22,z6]),(0,[z2,z3,z4,z10,z445,z6]),(0,[z1,z2,z4,z5,z6,z174]),(0,[z121,z2,z4,z5,z22,z6]),(0,[z470,z2,z3,z4,z5,z37])],[(0,[z109,z378,z2,z4,z5,z6]),(0,[z1035,z2,z3,z4,z5,z6]),(0,[z615,z3,z4,z1036,z11,z6])],[(0,[z629,z3,z4,z130,z11,z6]),(0,[z2,z190,z242,z5,z11,z6]),(0,[z2,z3,z4,z199,z6,z37]),(0,[z2,z3,z4,z391,z166,z6])],[(0,[z3,z4,z5,z775,z11,z6])],[(0,[z1037,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z1038,z11,z6]),(0,[z9,z3,z57,z5,z445,z6]),(0,[z1039,z3,z4,z5,z11,z6]),(0,[z67,z2,z3,z5,z11,z831])],[(0,[z2,z3,z4,z265,z68,z6])],[(0,[z2,z3,z4,z11,z6,z1040]),(0,[z2,z3,z4,z645,z22,z6]),(0,[z969,z3,z4,z5,z11,z6]),(0,[z1,z1041,z3,z4,z5,z6]),(0,[z2,z72,z3,z134,z5,z6]),(0,[z2,z3,z4,z5,z6,z1042])],[(0,[z2,z1043,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z165,z8]),(0,[z2,z3,z4,z5,z1044,z6])],[(0,[z2,z3,z4,z5,z54,z6]),(0,[z2,z3,z4,z155,z286,z6]),(0,[z382,z3,z4,z5,z22,z6]),(0,[z2,z469,z3,z5,z6,z37]),(0,[z1,z830,z3,z4,z5,z6])],[(0,[z9,z3,z57,z356,z11,z6]),(0,[z1,z45,z3,z4,z5,z46]),(0,[z2,z3,z4,z5,z29,z6]),(0,[z1,z2,z3,z4,z773,z6])],[(0,[z2,z3,z4,z1045,z11,z6]),(0,[z2,z3,z4,z66,z11,z6]),(0,[z2,z14,z4,z296,z5,z6]),(0,[z3,z4,z5,z22,z24,z6])]],
   [[(0,[z2,z3,z4,z5,z1046,z6]),(0,[z383,z3,z4,z11,z6,z144]),(0,[z3,z4,z5,z6,z223,z37])],[(0,[z2,z3,z4,z5,z1047,z6]),(0,[z2,z3,z4,z5,z6,z1048]),(0,[z2,z3,z4,z5,z1049,z6]),(0,[z1,z2,z3,z4,z1050,z6]),(0,[z2,z3,z5,z11,z1033,z6]),(0,[z2,z3,z4,z11,z934,z6])],[(0,[z2,z3,z4,z5,z1051,z6])],[(0,[z2,z3,z4,z5,z6,z1052]),(0,[z2,z3,z5,z11,z188,z831])],[(1,[z3,z896,z5,z11,z6]),(0,[z2,z3,z1053,z5,z11,z6]),(0,[z2,z3,z369,z5,z22,z6]),(0,[z2,z17,z4,z732,z11,z6]),(0,[z89,z2,z14,z3,z5,z6])],[(0,[z3,z4,z5,z1011,z11,z6]),(0,[z615,z3,z369,z5,z11,z6]),(0,[z2,z3,z4,z5,z913,z6])],[],[(0,[z25,z377,z3,z4,z11,z6]),(0,[z2,z3,z519,z5,z274,z6]),(0,[z2,z3,z4,z122,z68,z6]),(0,[z2,z3,z4,z5,z6,z733]),(0,[z2,z4,z5,z6,z37,z908])],[(0,[z525,z2,z14,z4,z5,z6]),(0,[z1,z2,z218,z3,z4,z6]),(0,[z2,z3,z4,z1054,z11,z6]),(0,[z70,z142,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1055,z11]),(0,[z2,z3,z4,z5,z1056,z6]),(0,[z2,z14,z4,z5,z6,z153]),(0,[z2,z4,z5,z75,z784,z6]),(0,[z2,z3,z4,z756,z11,z6]),(0,[z2,z1057,z3,z4,z5,z6])],[(0,[z2,z3,z266,z4,z5,z37]),(0,[z2,z17,z4,z11,z6,z91]),(0,[z145,z2,z142,z4,z5,z6]),(0,[z2,z3,z4,z5,z1058,z6])],[(0,[z1059,z3,z4,z5,z11,z6]),(0,[z1060,z2,z4,z5,z11,z6]),(0,[z21,z2,z3,z4,z442,z117])],[(0,[z2,z218,z115,z3,z11,z6])],[(0,[z2,z3,z4,z5,z1061,z6]),(0,[z315,z14,z3,z4,z5,z6]),(0,[z2,z469,z3,z5,z22,z6]),(0,[z1,z2,z451,z4,z5,z6]),(0,[z14,z3,z4,z5,z24,z6])],[(0,[z2,z3,z4,z5,z1062,z6]),(0,[z1063,z2,z4,z5,z11,z6]),(0,[z25,z2,z469,z5,z11,z6]),(0,[z145,z2,z3,z4,z5,z439]),(0,[z681,z2,z3,z4,z5,z37])],[(0,[z2,z3,z4,z165,z7,z8])]],
   [[(0,[z2,z3,z4,z5,z1064,z6]),(0,[z2,z3,z4,z5,z1065,z6])],[(0,[z109,z2,z19,z5,z11,z6]),(0,[z2,z14,z340,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1066]),(0,[z2,z3,z4,z5,z11,z1067]),(0,[z1041,z3,z4,z5,z11,z6]),(0,[z2,z448,z3,z4,z199,z6]),(0,[z2,z3,z4,z5,z1068,z6]),(0,[z2,z3,z4,z50,z68,z6])],[(0,[z2,z3,z210,z5,z6,z37]),(0,[z2,z3,z4,z10,z11,z6]),(0,[z2,z1069,z3,z4,z5,z6]),(0,[z2,z3,z5,z11,z188,z577]),(0,[z2,z3,z4,z5,z1070,z6]),(0,[z145,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1071]),(0,[z2,z3,z4,z5,z1072,z6]),(0,[z2,z3,z4,z5,z1073,z6]),(0,[z378,z2,z4,z5,z6,z379]),(0,[z2,z3,z390,z5,z301,z6])],[(0,[z2,z3,z609,z5,z274,z6]),(0,[z2,z3,z4,z5,z6,z1074]),(0,[z2,z3,z4,z5,z1075,z6]),(0,[z2,z3,z4,z1076,z22,z6])],[(0,[z63,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z1077,z11,z6]),(0,[z1078,z3,z4,z5,z11,z6]),(0,[z89,z2,z3,z11,z6,z144]),(0,[z2,z3,z4,z165,z11,z713])],[(0,[z2,z14,z3,z4,z436,z6]),(0,[z2,z3,z4,z5,z11,z1079]),(0,[z51,z14,z3,z4,z5,z108]),(0,[z67,z615,z3,z5,z11,z185])],[(0,[z2,z14,z3,z4,z98,z6]),(0,[z2,z3,z4,z1080,z11,z6]),(0,[z2,z3,z4,z5,z6,z1081]),(0,[z1082,z2,z3,z4,z5,z6])],[(0,[z1,z2,z299,z4,z5,z6]),(0,[z2,z3,z4,z1083,z11,z6]),(0,[z3,z4,z44,z939,z11,z6]),(0,[z2,z1084,z3,z4,z5,z6])],[(0,[z2,z14,z3,z210,z5,z6]),(0,[z1,z79,z3,z180,z5,z6]),(0,[z2,z3,z4,z5,z429,z6])],[],[(0,[z25,z2,z469,z26,z11,z6]),(0,[z1,z2,z17,z4,z164,z6]),(0,[z70,z3,z4,z779,z22,z6])],[(0,[z2,z3,z4,z5,z1085,z6]),(0,[z25,z2,z4,z385,z11,z6]),(0,[z2,z3,z4,z1086,z11,z6]),(0,[z25,z2,z4,z26,z22,z6]),(0,[z93,z4,z5,z11,z366,z90]),(0,[z2,z1087,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1088,z6]),(0,[z2,z4,z40,z5,z75,z6])],[(0,[z2,z3,z1089,z5,z11,z6]),(0,[z3,z4,z5,z24,z6,z37])],[(0,[z2,z3,z242,z155,z11,z6])],[(0,[z2,z3,z4,z436,z11,z6])]],
   [[(0,[z2,z3,z4,z5,z6,z1090]),(0,[z2,z3,z4,z1091,z11,z6]),(0,[z1,z2,z3,z261,z129,z6]),(0,[z2,z4,z5,z1092,z11,z6])],[(0,[z2,z3,z4,z1093,z11,z6]),(0,[z2,z3,z4,z1094,z5,z6]),(0,[z2,z3,z4,z11,z6,z1095]),(0,[z2,z16,z3,z673,z11,z6])],[(0,[z182,z3,z4,z130,z11,z6]),(0,[z2,z3,z4,z5,z1096,z6]),(0,[z1097,z3,z4,z5,z11,z6]),(0,[z377,z17,z3,z4,z11,z6]),(0,[z93,z2,z4,z5,z82,z90]),(0,[z1098,z2,z3,z4,z5,z6]),(0,[z2,z1099,z3,z4,z5,z6]),(0,[z2,z3,z4,z779,z22,z6])],[(0,[z2,z3,z4,z5,z1100,z6]),(0,[z2,z3,z4,z1101,z5,z6]),(0,[z182,z3,z4,z165,z11,z8])],[(0,[z2,z3,z4,z5,z342,z185]),(0,[z449,z2,z3,z4,z5,z37])],[(0,[z303,z2,z3,z5,z11,z185]),(0,[z290,z3,z180,z5,z11,z6]),(0,[z2,z3,z4,z5,z680,z37])],[(0,[z2,z3,z1102,z5,z11,z6]),(0,[z2,z3,z4,z1103,z11,z6]),(0,[z2,z190,z369,z5,z11,z6]),(0,[z2,z264,z4,z155,z11,z6]),(0,[z2,z16,z3,z204,z31,z6])],[(1,[z109,z2,z218,z11,z6]),(0,[z2,z3,z4,z5,z1104,z6])],[],[],[(0,[z1105,z2,z3,z4,z5,z6]),(0,[z2,z3,z5,z11,z6,z1106]),(0,[z2,z3,z4,z5,z22,z480])],[(0,[z2,z14,z3,z4,z5,z6]),(0,[z1107,z3,z4,z5,z11,z6]),(0,[z21,z2,z3,z4,z11,z117])],[(0,[z2,z14,z3,z4,z10,z6]),(0,[z1,z2,z3,z4,z147,z6]),(0,[z109,z2,z199,z157,z11,z6]),(0,[z1108,z3,z4,z5,z11,z6])],[(0,[z9,z3,z57,z5,z53,z6]),(0,[z2,z1109,z4,z5,z11,z6]),(0,[z1,z21,z2,z3,z4,z117]),(0,[z2,z3,z56,z5,z11,z188]),(0,[z2,z3,z4,z1015,z22,z6])],[(0,[z3,z4,z939,z5,z11,z6]),(0,[z2,z3,z4,z1110,z5,z6]),(0,[z3,z4,z5,z11,z1111,z6])],[(0,[z2,z3,z4,z5,z11,z1112]),(0,[z1113,z2,z3,z5,z11,z6]),(0,[z3,z4,z814,z5,z6,z37])]],
   [[(0,[z2,z3,z4,z5,z1114,z6]),(0,[z1,z2,z115,z35,z5,z6]),(0,[z1115,z3,z4,z5,z11,z6])],[(0,[z2,z1116,z3,z5,z11,z6])],[(0,[z2,z3,z4,z5,z1117,z6]),(0,[z2,z3,z799,z5,z22,z6])],[(0,[z3,z4,z5,z11,z6,z1118]),(0,[z1119,z3,z4,z5,z11,z6]),(0,[z182,z3,z4,z5,z856,z6])],[(0,[z2,z3,z4,z50,z380,z6])],[(0,[z33,z229,z4,z5,z11,z6]),(0,[z2,z3,z210,z5,z292,z6]),(0,[z51,z3,z4,z5,z286,z108]),(0,[z2,z3,z4,z5,z1120,z6]),(0,[z2,z42,z3,z5,z126,z6])],[(0,[z2,z3,z210,z5,z298,z6]),(0,[z2,z3,z4,z11,z8,z214]),(0,[z2,z3,z4,z5,z528,z6])],[(0,[z32,z3,z4,z44,z509,z6]),(0,[z798,z3,z4,z5,z11,z6]),(0,[z182,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z147,z22,z6]),(0,[z2,z115,z5,z11,z6,z496]),(0,[z2,z1121,z4,z5,z11,z6]),(0,[z2,z3,z4,z50,z206,z6])],[(0,[z135,z3,z4,z5,z102,z6]),(0,[z89,z3,z5,z11,z6,z366]),(0,[z2,z3,z4,z512,z166,z6]),(0,[z615,z3,z4,z5,z805,z6])],[(0,[z2,z1122,z3,z4,z5,z6]),(0,[z25,z2,z368,z26,z11,z6]),(0,[z2,z3,z4,z5,z200,z6])],[(0,[z567,z3,z4,z44,z11,z6]),(0,[z109,z2,z586,z5,z11,z6]),(0,[z2,z4,z5,z75,z6,z37])],[(0,[z3,z4,z5,z11,z6,z860]),(0,[z109,z2,z157,z5,z22,z6]),(0,[z2,z3,z4,z5,z22,z342])],[(0,[z2,z3,z4,z165,z11,z666]),(0,[z1123,z3,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z1124,z6]),(0,[z813,z3,z4,z5,z22,z6])],[(0,[z2,z3,z549,z436,z11,z6]),(0,[z1125,z3,z4,z5,z11,z6]),(0,[z1126,z3,z4,z5,z11,z6])]],
   [[(0,[z3,z4,z5,z335,z102,z6]),(0,[z2,z3,z5,z11,z6,z1127]),(0,[z2,z142,z41,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1128,z6]),(0,[z2,z3,z4,z1129,z5,z6]),(0,[z145,z2,z3,z4,z5,z342]),(0,[z2,z3,z4,z6,z82,z144]),(0,[z1130,z3,z4,z5,z11,z6])],[(0,[z32,z3,z4,z436,z11,z6]),(0,[z2,z3,z4,z5,z1131,z6]),(0,[z9,z3,z369,z5,z11,z6]),(0,[z1132,z218,z3,z4,z11,z6]),(0,[z1133,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z1134,z6])],[(0,[z3,z4,z436,z130,z11,z6]),(0,[z51,z3,z4,z155,z11,z108]),(0,[z2,z3,z4,z1135,z5,z6]),(0,[z1,z2,z3,z4,z1136,z6]),(0,[z1137,z2,z3,z4,z5,z6])],[(0,[z1138,z2,z3,z4,z5,z6]),(0,[z830,z3,z4,z5,z22,z6])],[(0,[z9,z14,z3,z57,z5,z6]),(0,[z2,z3,z4,z1139,z5,z6])],[(0,[z498,z3,z180,z5,z11,z6]),(0,[z2,z190,z4,z5,z58,z6]),(0,[z2,z14,z273,z4,z5,z6])],[(0,[z27,z3,z4,z5,z11,z6]),(0,[z1140,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z221,z6]),(0,[z3,z1141,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z1142,z6]),(0,[z272,z2,z3,z11,z6,z305])],[(0,[z2,z3,z4,z98,z6,z37]),(0,[z79,z14,z3,z180,z5,z6]),(0,[z2,z3,z5,z11,z1143,z6])],[(0,[z2,z3,z4,z199,z22,z6]),(0,[z2,z3,z4,z5,z1144,z6]),(0,[z1,z2,z316,z4,z5,z6])],[(0,[z2,z3,z4,z1145,z11,z6]),(0,[z2,z3,z4,z5,z286,z6]),(0,[z2,z16,z80,z3,z11,z6]),(0,[z2,z41,z4,z5,z11,z741]),(0,[z2,z421,z3,z5,z649,z6])],[(0,[z2,z3,z4,z5,z6,z82]),(0,[z2,z4,z5,z11,z6,z1146])],[(0,[z1,z2,z620,z4,z5,z6]),(1,[z2,z4,z732,z11,z6])],[(0,[z13,z212,z3,z4,z5,z6]),(0,[z2,z14,z3,z4,z66,z6]),(0,[z2,z35,z898,z5,z11,z6])],[(0,[z2,z1147,z4,z5,z11,z6]),(0,[z2,z3,z4,z1148,z5,z6]),(0,[z2,z41,z4,z5,z11,z136])],[(0,[z1,z9,z3,z57,z5,z6]),(0,[z43,z3,z4,z130,z6,z37]),(0,[z2,z1149,z3,z4,z5,z6]),(0,[z2,z14,z4,z5,z627,z6]),(0,[z93,z89,z2,z5,z11,z90]),(0,[z2,z3,z4,z5,z605,z37])]],
   [[(0,[z2,z3,z4,z1150,z5,z6])],[(0,[z382,z3,z4,z436,z11,z6]),(0,[z2,z3,z4,z5,z1151,z6]),(0,[z2,z3,z4,z1152,z5,z6]),(0,[z2,z3,z5,z22,z6,z305])],[(0,[z2,z3,z4,z5,z22,z278]),(0,[z2,z3,z4,z5,z1153,z6]),(0,[z2,z142,z3,z4,z5,z6]),(0,[z2,z3,z4,z122,z6,z38])],[(0,[z2,z3,z210,z98,z11,z6]),(0,[z2,z3,z4,z1154,z5,z6]),(0,[z32,z190,z4,z5,z11,z6]),(0,[z2,z3,z242,z5,z286,z6]),(0,[z93,z2,z5,z11,z305,z90]),(0,[z70,z3,z4,z5,z22,z113])],[(0,[z1155,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1156,z6]),(0,[z2,z3,z1157,z5,z11,z6]),(0,[z2,z3,z4,z11,z6,z1158]),(0,[z2,z1159,z3,z4,z5,z6]),(0,[z1,z2,z547,z4,z5,z6])],[(0,[z33,z229,z549,z5,z11,z6]),(0,[z2,z3,z4,z5,z1160,z6])],[(0,[z2,z3,z4,z5,z1161,z6]),(0,[z34,z3,z4,z66,z28,z6]),(0,[z2,z14,z3,z5,z368,z6]),(0,[z2,z3,z129,z770,z11,z6])],[(0,[z2,z3,z4,z50,z478,z6])],[(0,[z2,z3,z4,z155,z11,z6])],[(0,[z2,z3,z4,z5,z1162,z6])],[(0,[z2,z3,z4,z5,z1163,z6]),(0,[z2,z3,z4,z5,z1164,z6]),(0,[z2,z190,z4,z147,z11,z6]),(0,[z3,z4,z5,z22,z6,z366]),(0,[z2,z3,z4,z5,z22,z113])],[(0,[z2,z3,z4,z5,z6,z1165]),(0,[z2,z14,z4,z5,z171,z6]),(0,[z2,z264,z4,z5,z286,z6]),(0,[z2,z3,z4,z1166,z5,z6]),(0,[z1,z1167,z3,z4,z5,z6])],[(0,[z79,z3,z180,z5,z6,z37]),(0,[z3,z4,z167,z5,z11,z6]),(0,[z2,z3,z4,z5,z1168,z6]),(0,[z372,z3,z4,z5,z102,z6]),(0,[z25,z2,z4,z526,z26,z6]),(0,[z2,z3,z4,z40,z5,z6])],[(0,[z2,z1169,z3,z4,z5,z6]),(0,[z382,z14,z3,z4,z5,z6]),(0,[z2,z41,z3,z4,z5,z409]),(0,[z377,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z5,z1170,z6]),(0,[z2,z3,z4,z5,z6,z1171]),(0,[z2,z3,z4,z50,z762,z6])],[(0,[z25,z2,z469,z4,z11,z6]),(0,[z2,z3,z4,z5,z6,z342]),(0,[z2,z3,z4,z5,z22,z430]),(0,[z3,z4,z391,z5,z24,z6])]],
   [[(0,[z154,z14,z64,z4,z5,z6]),(0,[z2,z990,z3,z4,z5,z6]),(0,[z1172,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z1173,z6]),(0,[z1,z1097,z3,z4,z5,z6])],[(0,[z663,z3,z4,z130,z11,z6]),(0,[z2,z3,z5,z11,z6,z305]),(0,[z93,z2,z4,z5,z11,z741])],[(0,[z2,z3,z4,z5,z6,z1174]),(0,[z1,z2,z16,z3,z31,z6]),(0,[z67,z2,z3,z5,z11,z185])],[(0,[z2,z3,z4,z5,z1175,z11]),(0,[z2,z3,z4,z5,z6,z1176]),(0,[z21,z2,z3,z4,z306,z117])],[(0,[z383,z3,z4,z5,z6,z37])],[(0,[z2,z3,z4,z1177,z11,z6]),(0,[z2,z3,z4,z5,z1178,z6])],[(0,[z2,z3,z210,z5,z22,z6]),(0,[z51,z3,z4,z5,z11,z628]),(0,[z2,z4,z5,z11,z741,z90]),(0,[z2,z3,z874,z5,z22,z6])],[(0,[z25,z2,z469,z3,z11,z6]),(0,[z2,z3,z4,z5,z958,z6])],[(0,[z1179,z2,z3,z4,z5,z11]),(0,[z14,z3,z4,z5,z6,z366])],[(0,[z2,z3,z1180,z4,z5,z6]),(0,[z2,z3,z4,z5,z1181,z6]),(0,[z2,z3,z4,z5,z1182,z6])],[(0,[z3,z4,z5,z11,z6,z366]),(0,[z2,z3,z4,z98,z292,z6]),(0,[z2,z3,z1183,z5,z11,z6]),(0,[z2,z3,z4,z5,z1184,z6]),(0,[z2,z3,z4,z893,z6,z37])],[(0,[z3,z210,z5,z130,z11,z6]),(0,[z2,z3,z4,z98,z298,z6]),(0,[z2,z3,z4,z10,z53,z6]),(0,[z2,z3,z4,z5,z1185,z6]),(0,[z272,z2,z3,z4,z6,z82])],[(0,[z2,z3,z1186,z5,z11,z6])],[(0,[z2,z3,z4,z939,z11,z6]),(0,[z2,z14,z3,z4,z6,z144]),(0,[z93,z2,z4,z11,z144,z90]),(0,[z2,z3,z261,z770,z11,z6])],[(0,[z182,z3,z4,z44,z11,z6]),(0,[z1187,z2,z3,z4,z5,z6])],[(0,[z2,z3,z988,z5,z11,z6]),(0,[z1188,z3,z4,z5,z11,z6]),(0,[z2,z3,z56,z5,z188,z37])]],
   [[(0,[z25,z2,z4,z598,z11,z6]),(0,[z2,z14,z3,z4,z645,z6]),(0,[z2,z3,z4,z225,z5,z6]),(1,[z2,z3,z5,z958,z6])],[(0,[z81,z2,z3,z4,z541,z6]),(0,[z2,z1189,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z521,z37]),(0,[z767,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z6,z1190])],[(0,[z670,z3,z4,z44,z11,z6])],[(0,[z1132,z3,z4,z5,z11,z6]),(0,[z93,z2,z3,z4,z5,z409])],[(0,[z2,z3,z4,z5,z1191,z6]),(0,[z2,z4,z732,z26,z11,z6])],[(0,[z2,z14,z3,z242,z5,z6]),(0,[z2,z469,z164,z5,z11,z6]),(0,[z1192,z2,z3,z4,z5,z6]),(0,[z1193,z3,z4,z5,z11,z6])],[(0,[z33,z211,z4,z5,z11,z6]),(0,[z3,z4,z5,z58,z102,z6]),(0,[z3,z4,z5,z11,z6,z1194]),(0,[z2,z3,z5,z11,z958,z6])],[(0,[z2,z3,z4,z370,z5,z6]),(0,[z2,z3,z4,z5,z1195,z6]),(0,[z2,z4,z5,z913,z178,z6]),(0,[z377,z3,z4,z5,z310,z6])],[(0,[z2,z3,z4,z5,z1196,z6]),(0,[z238,z2,z3,z642,z5,z6]),(0,[z2,z1197,z3,z4,z5,z6]),(0,[z89,z2,z3,z5,z6,z37])],[(0,[z2,z3,z4,z1198,z11,z6]),(0,[z2,z3,z4,z5,z1199,z6])],[(0,[z32,z3,z4,z155,z11,z6]),(0,[z70,z3,z4,z5,z102,z6])],[(0,[z2,z3,z4,z5,z1200,z6]),(0,[z2,z264,z242,z5,z11,z6]),(0,[z2,z3,z4,z5,z1201,z6])],[(0,[z2,z3,z896,z5,z11,z6]),(0,[z2,z3,z1202,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z1203]),(0,[z121,z2,z261,z4,z11,z6])],[(0,[z2,z3,z4,z1204,z5,z6]),(0,[z2,z1205,z3,z4,z5,z6]),(0,[z3,z4,z5,z11,z6,z1206])],[(0,[z70,z3,z4,z5,z28,z6])]],
   [[(0,[z2,z3,z4,z5,z1207,z6]),(0,[z2,z14,z3,z549,z5,z6]),(0,[z2,z1208,z4,z5,z11,z6]),(0,[z2,z3,z4,z1209,z5,z6])],[(0,[z2,z1210,z4,z5,z11,z6]),(0,[z34,z3,z88,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1211]),(0,[z709,z3,z4,z5,z11,z6]),(0,[z2,z14,z4,z533,z5,z6])],[(0,[z1,z2,z3,z369,z5,z6]),(0,[z93,z179,z2,z4,z5,z90]),(0,[z2,z3,z4,z5,z1212,z6]),(0,[z2,z3,z4,z11,z6,z713]),(0,[z3,z4,z165,z167,z11,z8]),(0,[z302,z3,z4,z5,z6,z69])],[(0,[z2,z3,z4,z1213,z11,z6]),(0,[z2,z3,z369,z5,z286,z6]),(0,[z179,z2,z3,z5,z6,z305]),(0,[z2,z3,z94,z5,z6,z189])],[(0,[z3,z180,z896,z5,z11,z6]),(0,[z45,z3,z4,z5,z11,z46]),(0,[z2,z14,z4,z5,z913,z6]),(0,[z145,z2,z41,z4,z5,z136])],[(0,[z1214,z3,z4,z5,z11,z6]),(0,[z21,z2,z14,z3,z4,z117]),(0,[z121,z2,z4,z40,z5,z6])],[(0,[z2,z3,z4,z5,z1215,z6]),(0,[z43,z3,z4,z939,z11,z6]),(0,[z377,z115,z3,z5,z11,z6])],[(0,[z315,z3,z4,z5,z11,z6]),(0,[z109,z25,z2,z16,z11,z6]),(0,[z2,z17,z4,z164,z6,z37]),(0,[z70,z145,z3,z4,z5,z6])],[(0,[z2,z3,z1216,z5,z11,z6]),(0,[z2,z14,z314,z4,z5,z6]),(0,[z2,z3,z4,z1217,z5,z6])],[(0,[z2,z3,z4,z5,z1218,z6]),(0,[z815,z3,z4,z5,z11,z6]),(0,[z2,z3,z924,z5,z22,z6])],[(0,[z154,z64,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z6,z1219]),(0,[z329,z2,z3,z4,z5,z37]),(0,[z2,z3,z1220,z5,z11,z6]),(0,[z1,z2,z4,z5,z75,z6]),(0,[z1017,z2,z3,z4,z5,z6]),(0,[z182,z3,z4,z5,z22,z6]),(0,[z2,z3,z4,z165,z22,z8])],[(0,[z2,z3,z4,z532,z166,z6]),(0,[z3,z4,z5,z472,z11,z46]),(0,[z2,z16,z14,z3,z31,z6]),(0,[z2,z14,z3,z261,z129,z6])],[(0,[z2,z3,z4,z5,z6,z1221]),(0,[z2,z14,z131,z4,z5,z6])],[],[(0,[z2,z4,z5,z75,z22,z6]),(0,[z2,z3,z4,z944,z11,z6])],[(0,[z109,z2,z225,z157,z5,z6]),(0,[z1,z2,z3,z5,z6,z305]),(0,[z2,z4,z5,z11,z1222,z6])]],
   [[(0,[z2,z3,z4,z5,z1223,z6]),(0,[z2,z3,z5,z11,z6,z1224]),(0,[z32,z3,z4,z939,z11,z6]),(0,[z51,z3,z4,z5,z11,z108]),(0,[z2,z3,z4,z5,z1225,z6]),(0,[z793,z14,z3,z4,z5,z6]),(0,[z2,z142,z4,z5,z6,z90]),(0,[z2,z16,z3,z31,z11,z6])],[(0,[z2,z3,z4,z1226,z11,z6]),(0,[z2,z3,z369,z155,z11,z6]),(0,[z2,z962,z3,z5,z6,z37]),(0,[z3,z4,z5,z839,z22,z6])],[(1,[z782,z4,z5,z11,z6])],[(0,[z2,z3,z4,z5,z1227,z6]),(0,[z145,z830,z3,z4,z5,z6]),(0,[z2,z3,z5,z6,z305,z37]),(0,[z2,z3,z4,z1228,z5,z6]),(0,[z846,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z209,z6]),(0,[z2,z3,z4,z5,z6,z1229]),(0,[z2,z3,z4,z83,z762,z6])],[],[(0,[z2,z3,z4,z5,z1230,z6])],[(0,[z2,z3,z4,z5,z6,z1231]),(0,[z2,z3,z4,z5,z6,z1232]),(0,[z2,z3,z4,z5,z762,z6])],[(0,[z2,z3,z56,z5,z11,z560])],[(0,[z51,z3,z242,z5,z11,z108]),(0,[z2,z3,z4,z5,z1233,z6])],[(0,[z3,z4,z5,z11,z46,z665]),(0,[z51,z3,z4,z66,z11,z6]),(0,[z2,z3,z4,z5,z1234,z6]),(0,[z1,z3,z4,z5,z6,z223]),(0,[z377,z3,z4,z129,z11,z6]),(0,[z2,z3,z4,z5,z1235,z6]),(0,[z3,z4,z5,z11,z6,z1236])],[(0,[z2,z3,z4,z98,z22,z6]),(0,[z353,z2,z3,z4,z267,z6]),(0,[z1060,z2,z4,z5,z6,z37])],[(0,[z2,z14,z41,z4,z5,z136]),(0,[z615,z3,z4,z5,z952,z6])],[(0,[z2,z3,z4,z1237,z11,z6]),(0,[z2,z61,z3,z216,z5,z6])],[(0,[z2,z3,z4,z5,z1238,z6]),(0,[z79,z3,z671,z5,z11,z6]),(0,[z70,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z1239]),(0,[z2,z3,z4,z5,z1240,z6]),(0,[z2,z3,z4,z204,z5,z6]),(0,[z2,z3,z56,z5,z158,z188])],[(0,[z383,z229,z4,z5,z11,z6]),(0,[z3,z896,z57,z5,z11,z6]),(0,[z2,z3,z4,z5,z1241,z6]),(0,[z2,z3,z4,z5,z113,z409]),(0,[z615,z3,z4,z5,z6,z37])]],
   [[(0,[z1,z154,z64,z4,z5,z6]),(0,[z2,z3,z4,z5,z1242,z6])],[(0,[z2,z3,z4,z5,z1243,z6]),(0,[z51,z264,z4,z5,z11,z108]),(0,[z2,z4,z5,z75,z1008,z6]),(0,[z2,z3,z4,z391,z244,z6])],[(0,[z43,z3,z4,z130,z22,z6]),(0,[z1244,z2,z3,z4,z5,z6]),(0,[z2,z1245,z3,z4,z5,z6]),(0,[z2,z3,z4,z759,z11,z6]),(0,[z112,z2,z3,z4,z5,z37])],[(0,[z1,z767,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1246]),(0,[z2,z3,z127,z5,z6,z189])],[],[(0,[z2,z3,z4,z5,z11,z6]),(0,[z32,z3,z4,z44,z6,z37]),(1,[z2,z898,z5,z11,z6])],[(0,[z2,z3,z4,z5,z1011,z6])],[(0,[z32,z3,z4,z531,z11,z6]),(0,[z2,z3,z4,z5,z6,z1247]),(0,[z1248,z3,z4,z5,z11,z6]),(0,[z109,z2,z898,z5,z11,z6]),(0,[z382,z3,z4,z5,z1191,z6]),(0,[z2,z3,z4,z5,z1249,z6])],[(0,[z9,z3,z57,z5,z6,z37]),(0,[z2,z3,z4,z1250,z11,z6]),(0,[z2,z3,z1251,z5,z11,z6]),(0,[z2,z1252,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z22,z497])],[(0,[z3,z4,z939,z130,z11,z6]),(0,[z1,z2,z341,z4,z5,z6]),(0,[z2,z361,z3,z5,z126,z6]),(0,[z2,z3,z4,z5,z6,z1253])],[(0,[z1254,z3,z4,z5,z11,z6])],[(0,[z1,z2,z3,z4,z5,z1079])],[(0,[z2,z3,z4,z5,z170,z37]),(0,[z1255,z2,z3,z4,z11,z6])],[(0,[z2,z3,z4,z1256,z11,z6]),(0,[z2,z3,z4,z5,z1257,z6]),(0,[z229,z190,z4,z5,z11,z6]),(0,[z2,z3,z4,z6,z144,z37])],[(0,[z2,z3,z4,z1258,z11,z6]),(0,[z2,z3,z242,z5,z11,z6]),(0,[z1259,z2,z3,z5,z11,z6]),(0,[z70,z1,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1260])],[(0,[z2,z3,z4,z436,z6,z37]),(0,[z2,z3,z4,z356,z445,z6]),(0,[z79,z3,z180,z5,z22,z6]),(0,[z13,z3,z4,z5,z1011,z6]),(0,[z2,z3,z4,z526,z5,z6]),(0,[z3,z4,z5,z6,z366,z37]),(0,[z3,z4,z83,z5,z24,z6])]],
   [[(0,[z67,z2,z3,z5,z11,z159]),(0,[z2,z3,z4,z732,z11,z6]),(0,[z3,z4,z1261,z5,z11,z6]),(0,[z1,z2,z687,z4,z5,z6]),(0,[z377,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z1262,z6]),(0,[z2,z3,z4,z155,z58,z6]),(0,[z25,z2,z4,z732,z11,z6]),(0,[z2,z4,z5,z11,z6,z1263])],[(0,[z2,z3,z4,z5,z1264,z6])],[(0,[z2,z3,z4,z5,z1265,z6]),(0,[z2,z3,z4,z5,z6,z1266]),(0,[z2,z3,z4,z5,z22,z634])],[(0,[z2,z3,z4,z5,z1267,z6]),(0,[z109,z2,z600,z5,z11,z6]),(0,[z2,z115,z35,z5,z209,z6]),(0,[z888,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z1268,z6])],[(0,[z2,z264,z4,z5,z11,z6]),(0,[z2,z3,z5,z1269,z11,z6]),(0,[z2,z3,z4,z5,z6,z1270]),(0,[z2,z218,z3,z4,z11,z6])],[(0,[z2,z1271,z4,z5,z11,z6]),(0,[z2,z3,z4,z147,z286,z6]),(0,[z383,z3,z4,z5,z22,z6]),(0,[z2,z16,z75,z31,z11,z6])],[(0,[z2,z3,z1272,z5,z11,z6]),(0,[z2,z3,z4,z5,z1273,z6]),(0,[z1274,z3,z4,z5,z11,z6]),(0,[z1,z3,z4,z167,z5,z6])],[(0,[z2,z3,z4,z5,z1275,z6]),(0,[z2,z3,z4,z1050,z11,z6]),(0,[z1276,z2,z3,z4,z5,z6])],[(0,[z2,z3,z210,z436,z11,z6]),(0,[z2,z3,z5,z11,z6,z831])],[(0,[z2,z3,z4,z5,z1277,z6]),(0,[z2,z3,z4,z130,z54,z6]),(0,[z2,z3,z5,z368,z11,z6]),(0,[z2,z3,z4,z5,z1278,z6]),(0,[z227,z2,z3,z4,z394,z6]),(0,[z378,z2,z14,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1279,z6]),(0,[z2,z3,z4,z5,z11,z800]),(0,[z378,z2,z3,z4,z5,z6]),(0,[z1,z272,z2,z3,z4,z6])],[(0,[z2,z3,z4,z50,z523,z6]),(0,[z2,z3,z4,z1280,z5,z6])],[(0,[z34,z3,z4,z5,z6,z62]),(0,[z2,z3,z4,z5,z1281,z6]),(0,[z121,z2,z16,z31,z11,z6]),(0,[z2,z3,z4,z5,z11,z733])],[]],
   [[(0,[z1282,z2,z3,z4,z5,z6]),(0,[z1,z33,z229,z4,z5,z6]),(0,[z2,z190,z4,z5,z6,z37]),(0,[z2,z101,z3,z4,z5,z409]),(0,[z67,z2,z14,z3,z5,z185]),(1,[z2,z4,z5,z11,z741]),(0,[z1283,z2,z4,z5,z11,z6])],[(0,[z93,z2,z4,z5,z22,z90]),(0,[z2,z3,z1284,z5,z11,z6])],[],[(0,[z2,z3,z4,z5,z1285,z6]),(0,[z51,z3,z4,z5,z108,z37]),(0,[z2,z448,z3,z4,z5,z6]),(0,[z2,z3,z94,z5,z958,z6])],[(0,[z872,z14,z3,z4,z5,z6])],[(0,[z2,z3,z549,z5,z11,z6]),(0,[z154,z782,z4,z5,z11,z6]),(0,[z3,z4,z5,z445,z46,z6]),(0,[z2,z115,z35,z5,z11,z6]),(0,[z272,z2,z3,z4,z11,z6]),(0,[z2,z3,z4,z5,z6,z1286])],[(0,[z2,z3,z129,z323,z11,z6]),(0,[z1,z2,z4,z5,z691,z6])],[(0,[z3,z4,z356,z11,z46,z6]),(0,[z2,z17,z4,z114,z11,z6]),(0,[z2,z3,z4,z5,z1287,z6]),(0,[z2,z3,z4,z5,z6,z1288]),(0,[z121,z2,z4,z204,z5,z6]),(0,[z2,z3,z4,z1289,z5,z6])],[(0,[z2,z3,z5,z1290,z11,z6]),(0,[z2,z3,z4,z5,z6,z1291]),(0,[z0,z2,z3,z47,z5,z6]),(0,[z2,z3,z4,z5,z442,z6]),(0,[z1292,z2,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1293,z6]),(0,[z2,z3,z4,z5,z445,z6]),(0,[z2,z3,z4,z5,z6,z1294]),(0,[z2,z3,z1295,z5,z11,z6]),(0,[z51,z3,z369,z5,z11,z108]),(0,[z1296,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z1297,z11,z6]),(0,[z2,z14,z17,z4,z164,z6])],[],[(0,[z2,z3,z4,z5,z1298,z6])],[(0,[z2,z264,z4,z5,z58,z6]),(0,[z1,z2,z3,z4,z199,z6]),(0,[z89,z2,z3,z5,z22,z6]),(0,[z2,z1299,z3,z4,z5,z6]),(0,[z2,z3,z4,z1300,z5,z6])],[(0,[z51,z2,z3,z4,z5,z342]),(0,[z109,z377,z3,z5,z11,z6]),(0,[z2,z3,z4,z5,z1301,z6]),(0,[z2,z3,z400,z5,z274,z6]),(0,[z3,z4,z5,z925,z22,z6])],[(0,[z2,z3,z4,z356,z11,z6]),(0,[z13,z3,z4,z5,z102,z6]),(0,[z51,z3,z4,z5,z11,z860]),(0,[z121,z2,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z159,z37]),(0,[z2,z3,z4,z1302,z5,z6]),(0,[z2,z3,z4,z1036,z11,z6])],[(0,[z2,z41,z4,z5,z11,z170]),(0,[z1303,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z1304,z5,z6]),(0,[z2,z3,z4,z5,z1305,z6]),(0,[z2,z3,z4,z1136,z11,z6]),(0,[z67,z3,z5,z11,z223,z185]),(0,[z2,z3,z4,z5,z11,z713])]],
   [[(0,[z2,z3,z4,z5,z6,z1306]),(0,[z383,z272,z3,z4,z11,z6]),(0,[z2,z3,z261,z129,z11,z6])],[(0,[z2,z3,z4,z436,z292,z6]),(0,[z1307,z3,z4,z5,z11,z6]),(0,[z3,z4,z5,z22,z24,z113])],[(0,[z2,z3,z4,z436,z298,z6]),(0,[z2,z1308,z3,z4,z5,z6]),(0,[z2,z3,z4,z66,z6,z37]),(0,[z2,z3,z4,z832,z11,z6]),(0,[z1309,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z6,z1310])],[(0,[z3,z896,z4,z5,z11,z6])],[(0,[z378,z2,z4,z5,z178,z6]),(0,[z2,z3,z5,z11,z6,z871]),(0,[z1311,z2,z3,z4,z5,z6]),(0,[z67,z2,z3,z5,z160,z185])],[(0,[z2,z3,z4,z5,z1312,z6]),(0,[z2,z35,z5,z252,z11,z6]),(0,[z2,z3,z4,z5,z1313,z6]),(0,[z2,z3,z4,z5,z733,z37])],[(0,[z2,z3,z4,z5,z1314,z6]),(0,[z2,z3,z1315,z5,z11,z6]),(0,[z109,z2,z673,z5,z11,z6])],[(0,[z382,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z1316,z11,z6]),(0,[z1317,z3,z4,z5,z11,z6]),(0,[z27,z3,z4,z5,z6,z37]),(0,[z2,z3,z4,z5,z6,z1318])],[(0,[z2,z3,z4,z5,z297,z37])],[(0,[z34,z3,z4,z5,z1011,z6]),(0,[z383,z190,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z1319,z6]),(0,[z2,z3,z4,z5,z11,z847]),(0,[z2,z3,z134,z5,z126,z6])],[(0,[z2,z1320,z3,z4,z11,z6]),(0,[z2,z1321,z4,z5,z11,z6]),(0,[z2,z14,z3,z4,z147,z6]),(0,[z109,z2,z448,z157,z5,z6]),(0,[z2,z17,z4,z164,z22,z6]),(0,[z2,z3,z4,z11,z8,z713])],[(0,[z482,z3,z4,z130,z11,z6]),(0,[z2,z1322,z4,z5,z11,z6]),(0,[z272,z3,z4,z11,z6,z366]),(0,[z2,z3,z4,z5,z1006,z6]),(0,[z1037,z3,z4,z5,z22,z6])],[(0,[z3,z4,z5,z28,z1011,z6]),(0,[z1,z2,z443,z4,z5,z6])],[(0,[z154,z64,z4,z5,z22,z6]),(0,[z93,z1,z2,z4,z5,z90]),(0,[z2,z3,z4,z165,z8,z23])],[(0,[z1323,z2,z3,z4,z5,z6]),(0,[z2,z3,z369,z5,z11,z6]),(0,[z2,z14,z115,z35,z5,z6])],[(0,[z2,z3,z4,z5,z1324,z6]),(0,[z1325,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z155,z6])],[(0,[z2,z1326,z4,z5,z11,z6]),(0,[z1327,z3,z4,z5,z11,z6])],[],[(0,[z2,z3,z4,z1328,z11,z6]),(0,[z51,z1,z3,z4,z5,z108]),(0,[z1,z2,z4,z5,z123,z6])],[(0,[z378,z2,z101,z4,z5,z6]),(0,[z93,z2,z14,z4,z5,z90]),(0,[z2,z3,z4,z5,z22,z74])],[(0,[z93,z2,z4,z5,z254,z90]),(0,[z377,z3,z4,z5,z587,z6]),(0,[z883,z121,z2,z4,z5,z6])],[(0,[z2,z3,z4,z10,z6,z37]),(0,[z2,z3,z4,z5,z1329,z6]),(0,[z16,z377,z3,z31,z11,z6]),(0,[z2,z3,z56,z5,z188,z553])],[(0,[z2,z3,z4,z5,z6,z1330]),(0,[z2,z3,z4,z5,z516,z37]),(0,[z2,z1331,z3,z4,z5,z6])],[(0,[z2,z3,z4,z1332,z11,z6]),(0,[z2,z3,z4,z155,z6,z37])],[(0,[z2,z3,z4,z1333,z11,z6]),(0,[z2,z3,z4,z5,z1334,z6]),(0,[z51,z3,z4,z5,z58,z108]),(0,[z89,z272,z2,z3,z11,z6]),(0,[z3,z4,z50,z5,z24,z6])],[(0,[z1335,z2,z3,z4,z5,z6]),(0,[z2,z218,z448,z3,z4,z6]),(0,[z182,z14,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z351,z37]),(0,[z2,z3,z4,z5,z22,z348]),(0,[z2,z3,z4,z1336,z5,z6]),(0,[z2,z3,z4,z762,z68,z6])],[(0,[z2,z3,z4,z5,z6,z169]),(0,[z1,z2,z575,z4,z5,z6]),(0,[z3,z4,z167,z5,z6,z37]),(0,[z3,z4,z971,z5,z22,z6])],[(0,[z378,z2,z41,z4,z5,z6]),(0,[z2,z3,z94,z5,z274,z6])],[(0,[z2,z3,z4,z1076,z11,z6])],[(0,[z2,z1337,z4,z5,z11,z6]),(0,[z2,z1338,z4,z5,z11,z6]),(0,[z2,z264,z369,z5,z11,z6]),(0,[z2,z1339,z3,z4,z5,z6]),(0,[z1340,z3,z4,z5,z11,z6])]],
   [[(0,[z1,z2,z264,z4,z5,z6]),(0,[z3,z4,z5,z11,z46,z860]),(0,[z2,z1341,z3,z4,z5,z6])],[(0,[z2,z3,z4,z1342,z5,z6]),(0,[z2,z3,z4,z5,z6,z1343]),(0,[z2,z3,z4,z5,z6,z1344])],[(0,[z2,z3,z4,z1345,z5,z6]),(0,[z2,z3,z4,z5,z6,z1346]),(0,[z27,z3,z4,z5,z310,z6]),(0,[z615,z3,z4,z5,z22,z6])],[(0,[z2,z3,z770,z31,z11,z6])],[],[(0,[z2,z3,z4,z1347,z11,z6]),(0,[z2,z1348,z3,z4,z5,z6]),(0,[z1,z43,z3,z4,z130,z6]),(0,[z2,z3,z4,z645,z102,z6]),(0,[z2,z3,z4,z5,z1349,z6]),(0,[z2,z3,z4,z5,z1350,z6]),(0,[z70,z3,z4,z779,z11,z6])],[(0,[z2,z3,z4,z10,z22,z6]),(0,[z2,z3,z4,z5,z22,z146])],[(0,[z2,z1351,z4,z5,z11,z6]),(0,[z2,z3,z4,z5,z1352,z6]),(0,[z70,z3,z4,z5,z58,z6]),(0,[z25,z382,z4,z26,z11,z6]),(0,[z1,z67,z2,z3,z5,z185]),(0,[z14,z3,z4,z5,z6,z771])],[(0,[z32,z3,z4,z44,z22,z6])],[(0,[z2,z3,z4,z645,z28,z6])],[(0,[z2,z3,z1353,z5,z11,z6]),(0,[z2,z3,z4,z5,z8,z342]),(0,[z378,z2,z4,z5,z6,z90])],[(0,[z9,z3,z57,z5,z22,z6]),(0,[z2,z3,z4,z5,z105,z37])],[(0,[z2,z3,z4,z5,z1354,z6]),(0,[z34,z3,z4,z5,z28,z6]),(0,[z2,z1355,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z23]),(0,[z3,z4,z5,z301,z24,z6]),(0,[z997,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z5,z1356,z6]),(0,[z2,z3,z4,z5,z1357,z6]),(0,[z2,z3,z4,z5,z53,z6]),(0,[z682,z3,z57,z5,z11,z6]),(0,[z2,z3,z1358,z5,z11,z6]),(0,[z51,z3,z4,z147,z11,z108]),(0,[z2,z469,z3,z370,z5,z6]),(0,[z2,z14,z4,z5,z6,z246])],[(0,[z2,z3,z4,z5,z58,z6]),(0,[z25,z2,z537,z4,z11,z6]),(0,[z2,z3,z4,z166,z762,z6])],[(0,[z2,z3,z4,z5,z1359,z6]),(0,[z3,z4,z5,z509,z46,z6]),(0,[z2,z3,z1360,z5,z11,z6]),(0,[z2,z17,z4,z652,z11,z6]),(1,[z121,z2,z16,z11,z6])]],
   [[(0,[z2,z3,z4,z1361,z11,z6]),(0,[z2,z1362,z3,z4,z5,z6]),(0,[z2,z3,z734,z5,z11,z6]),(0,[z272,z179,z2,z3,z4,z6]),(0,[z70,z3,z4,z1015,z11,z6])],[(0,[z32,z3,z369,z5,z11,z6]),(0,[z2,z14,z4,z5,z257,z6]),(0,[z2,z3,z4,z11,z762,z6])],[(0,[z2,z3,z4,z436,z22,z6]),(0,[z2,z3,z1363,z4,z5,z6])],[(0,[z2,z3,z4,z5,z1364,z6]),(0,[z1,z2,z3,z56,z5,z188]),(0,[z3,z4,z5,z6,z37,z1236])],[(0,[z2,z97,z3,z4,z5,z6]),(0,[z2,z828,z190,z4,z5,z6]),(0,[z2,z3,z4,z5,z1365,z6]),(0,[z2,z3,z4,z22,z6,z144]),(0,[z2,z3,z4,z1366,z5,z6])],[(0,[z2,z3,z4,z5,z6,z1367]),(0,[z2,z3,z4,z5,z1368,z6]),(0,[z2,z14,z3,z4,z1045,z6])],[(0,[z3,z782,z4,z5,z11,z6]),(0,[z1167,z3,z4,z5,z11,z6]),(0,[z2,z3,z4,z1369,z5,z6]),(0,[z2,z3,z4,z1021,z11,z6]),(0,[z1193,z3,z4,z5,z6,z37])],[(0,[z1,z2,z3,z4,z356,z6]),(0,[z2,z3,z4,z44,z54,z6]),(0,[z2,z3,z242,z5,z58,z6]),(0,[z2,z3,z4,z1015,z11,z6])],[(0,[z33,z229,z4,z5,z6,z37]),(0,[z2,z3,z4,z1370,z11,z6]),(0,[z2,z3,z5,z1371,z11,z6])],[(0,[z2,z3,z4,z5,z376,z37]),(0,[z2,z3,z4,z5,z6,z1372]),(0,[z2,z3,z898,z5,z11,z6]),(0,[z2,z3,z4,z50,z394,z6]),(0,[z70,z3,z4,z5,z576,z6])],[(0,[z2,z1373,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z509,z6]),(0,[z493,z2,z3,z4,z5,z409])],[(0,[z2,z782,z4,z5,z11,z6]),(0,[z2,z4,z5,z732,z11,z6]),(0,[z1,z3,z4,z5,z24,z6]),(0,[z70,z3,z4,z5,z22,z37])],[(0,[z2,z3,z4,z5,z1374,z6]),(0,[z2,z3,z4,z5,z6,z1375])],[(0,[z2,z1376,z4,z5,z11,z6]),(0,[z3,z4,z5,z335,z24,z6]),(0,[z2,z17,z4,z164,z29,z6]),(0,[z148,z2,z3,z519,z5,z6]),(0,[z2,z4,z5,z11,z913,z6]),(0,[z1377,z2,z4,z5,z11,z6]),(0,[z2,z61,z3,z5,z958,z6])],[(0,[z218,z1214,z3,z4,z11,z6]),(0,[z25,z1,z2,z4,z26,z6]),(0,[z21,z2,z3,z4,z22,z117]),(0,[z1107,z3,z4,z5,z22,z6])],[(0,[z2,z3,z4,z1378,z5,z6]),(0,[z615,z14,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z1379]),(0,[z2,z3,z56,z5,z11,z831])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 506).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1016).take 392) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1408)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [506, 510, 392] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 167).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 167).take 152).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 319).take 150).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 469).take 43).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [167, 152, 150, 43] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_38457

theorem PEqualNP.Outside.L_meta_38457 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372928 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372928 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38457.solve