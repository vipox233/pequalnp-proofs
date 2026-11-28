import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39809

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
  Nat.testBit (4008372970 * 2 ^ 32 + 3974160512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x8002142854f10e1b#64 ++ 0xfd467cf8fdf11e3f#64 : BitVec 128),
   (0x8118b163303762c5#64 ++ 0xffb9b367327fe3c7#64 : BitVec 128),
   (0x02c14285c300b56e#64 ++ 0xdfc1c387c381ffff#64 : BitVec 128),
   (0x04ee03f803da03b0#64 ++ 0x6efe03f803fe03f8#64 : BitVec 128),
   (0x10f7fc0003edd800#64 ++ 0x74fffc0003fffc00#64 : BitVec 128),
   (0x08fdebd6a8000000#64 ++ 0x7bfffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x02c14285c300b56e 0xdfc1c387c381ffff

def z1 : W := mkw 0x04ee03f803da03b0 0x6efe03f803fe03f8

def z2 : W := mkw 0x060803fdc01227fe 0x8b0003ffc00003ff

def z3 : W := mkw 0x06ef43fdc3dab7fe 0xffffc3ffc3ffffff

def z4 : W := mkw 0x08fdebd6a8000000 0x7bfffffffc000000

def z5 : W := mkw 0x8002142854f10e1b 0xfd467cf8fdf11e3f

def z6 : W := mkw 0x8118b163303762c5 0xffb9b367327fe3c7

def z7 : W := mkw 0x10f7fc0003edd800 0x74fffc0003fffc00

def z8 : W := mkw 0x88fffffebcf10a11 0x7bfffffffc700000

def z9 : W := mkw 0x0cef4bfc8bda03b0 0x6efe4ff8cffe03f8

def z10 : W := mkw 0x08ffebfea8d00210 0x7ffffffffdf00238

def z11 : W := mkw 0x0008016000120280 0x6eb80360027e03c0

def z12 : W := mkw 0x8002140854e10c1b 0x91467c98fd811c3f

def z13 : W := mkw 0x81081163303322c5 0xff003367307103c7

def z14 : W := mkw 0x00c0028003000120 0x4ec00380038003f8

def z15 : W := mkw 0x083de956a8000000 0x313ffc7ffc000000

def z16 : W := mkw 0x00c0000003000000 0x44c0000003800000

def z17 : W := mkw 0x00c1428480000000 0x5bc1c387c0000000

def z18 : W := mkw 0x12e74e84c3c89d2a 0x00464c80c1801c38

def z19 : W := mkw 0x830803e7f01227ef 0x8b0003e7f00003ff

def z20 : W := mkw 0x040803f8001203b0 0x0a0003f8000003f8

def z21 : W := mkw 0x10fffd6003ffda80 0x7effff6003ffffc0

def z22 : W := mkw 0x08fdebd6a8000000 0x02b9830700000000

def z23 : W := mkw 0x8002142854f10e1b 0x8400000001f11e3f

def z24 : W := mkw 0x02c14285c300b56e 0x8b818387c200e3ff

def z25 : W := mkw 0x8002142854f10e1b 0xb1067c78fc711c07

def z26 : W := mkw 0x000000004000040a 0xdd404080c1811e3f

def z27 : W := mkw 0x12d1fe85c325fd6e 0xdfc1ff87c381ffff

def z28 : W := mkw 0x0002000800c00010 0x0046009801800038

def z29 : W := mkw 0x0cee03feabda03b0 0x6ffe03fffffe03f8

def z30 : W := mkw 0x82c356add7f1bf7f 0xffc7fffffff1ffff

def z31 : W := mkw 0x1013fc0000e5d800 0x7447fc0001f1fc00

def z32 : W := mkw 0x1002140003edd800 0x0400000003fffc00

def z33 : W := mkw 0x81080163301222c5 0x8b000367300003c7

def z34 : W := mkw 0x08e74e9cccc00c1a 0x00464c98cd801c38

def z35 : W := mkw 0x11fde943230ef0c4 0x02b98307020ee1c0

def z36 : W := mkw 0x10f5f800032dd000 0x74b9b000027fe000

def z37 : W := mkw 0x0000000000000000 0x79467cf8fc000000

def z38 : W := mkw 0x0cffebfeabda03b0 0x7ffffffffffe03f8

def z39 : W := mkw 0x02014005c000b44e 0xdf81c307c201ffc7

def z40 : W := mkw 0x02c142858300b164 0x56c1c3070381fdc0

def z41 : W := mkw 0x8118b16230374281 0x20383060307e0000

def z42 : W := mkw 0x06e7429cc3c8953a 0x00464098c1801c38

def z43 : W := mkw 0x00c1400003009000 0x54c1c0000381fc00

def z44 : W := mkw 0x913ebd6330ff6ac5 0xffbfbf67327fe3c7

def z45 : W := mkw 0x08e54a9488000000 0x0000000000000000

def z46 : W := mkw 0x02d9e3c7e300b56e 0xfff9f3e7f381ffff

def z47 : W := mkw 0x020140058000b044 0x000180070000e000

def z48 : W := mkw 0x04c803f8031203b0 0x4ec003f8038003f8

def z49 : W := mkw 0x02ed43d5c300b56e 0xffffc3ffc381ffff

def z50 : W := mkw 0x0000000000000000 0x0000000000000000

def z51 : W := mkw 0x06ed43d5830ab1e4 0x02b98307020ee1c0

def z52 : W := mkw 0x8110b023303762c5 0x9501b007327fe3c7

def z53 : W := mkw 0x08000006a8000000 0x01000007fc000000

def z54 : W := mkw 0x02c142858300b164 0x4ec183870380e3f8

def z55 : W := mkw 0x0402002803da03b0 0x6c4600f803fe03f8

def z56 : W := mkw 0x8002142854f10e1b 0xfd00306031f11e3f

def z57 : W := mkw 0x83d9f3e7f337f7ef 0xfff9f3e7f3ffffff

def z58 : W := mkw 0x8118b163303762c5 0x86b98307027fe3c7

def z59 : W := mkw 0x0118a143200660c4 0x7bb9b367320ee1c0

def z60 : W := mkw 0x042c0150000a0080 0x00380000000e0000

def z61 : W := mkw 0x853eb17b30ff62d5 0xffbfb37f327fe3c7

def z62 : W := mkw 0x020000014300b56e 0x840000000381ffff

def z63 : W := mkw 0x8002142814f10a11 0x20063c783c700000

def z64 : W := mkw 0x08e54a9488000000 0x5bc7cf9fcc000000

def z65 : W := mkw 0x8402142857fb0fbb 0xfd467cf8ffff1fff

def z66 : W := mkw 0x0811e806a8000000 0x1101fc07fc000000

def z67 : W := mkw 0x08f5e806a8000000 0x71fffc07fc000000

def z68 : W := mkw 0x02c14285c300b56e 0x9141c087c181fc3f

def z69 : W := mkw 0x85feb3fb33ff63f5 0xffffb3ff33ffe3ff

def z70 : W := mkw 0x0010b00000254000 0x74b9b000027fe000

def z71 : W := mkw 0x04ec03f0031a03a0 0x6eb80360027e03c0

def z72 : W := mkw 0x09fdebd7a80660c4 0x7bfffffffe0ee1c0

def z73 : W := mkw 0x8dfffbffbbff63f5 0xffffffffffffe3ff

def z74 : W := mkw 0x9013fc2854f5de1b 0xfd47fcf8fdf1fe3f

def z75 : W := mkw 0x8110b02330356245 0xfd01b0673071e207

def z76 : W := mkw 0x0018a14220000000 0x7bb9b36730000000

def z77 : W := mkw 0x89fdfbf7b83762c5 0xfffffffffe7fe3c7

def z78 : W := mkw 0x14ef4ff803da9bb0 0x6efe4ff803fe1ff8

def z79 : W := mkw 0x811ab56a34f74a91 0x203e3c783c7e0000

def z80 : W := mkw 0x8118b163303762c5 0xfffffffffe7fe3c7

def z81 : W := mkw 0x08e54a9488000000 0x00464c98cc000000

def z82 : W := mkw 0x81001021103762c5 0x84000000027fe3c7

def z83 : W := mkw 0x000000014000244e 0xdfc1c387c381ffff

def z84 : W := mkw 0x9119fd633037fac5 0xffb9ff67327fffc7

def z85 : W := mkw 0x04e6029803c80130 0x0046009801800038

def z86 : W := mkw 0x14f7fe9803edd930 0x74fffc9803fffc38

def z87 : W := mkw 0x14ee17f803ffdbb0 0x6efe03f803fffff8

def z88 : W := mkw 0x08fdebd6a8000000 0x207e7cf8fc000000

def z89 : W := mkw 0x89fdfbd7b8256045 0xfbfffffffc01e007

def z90 : W := mkw 0x91fffd6333fffac5 0xffffff6733ffffc7

def z91 : W := mkw 0x0818a3d6a8000000 0x7bb9b3fffc000000

def z92 : W := mkw 0x04ec03d0030a01a0 0x4ef80380038e03f8

def z93 : W := mkw 0x8002142954f12e5f 0xffc7fffffff1ffff

def z94 : W := mkw 0x81001021103762c5 0xfd003060327fe3c7

def z95 : W := mkw 0x90f7fc2013fdda01 0xfdfffc6033fffe07

def z96 : W := mkw 0x0afdebd7ab00b164 0x02b983070200e1c0

def z97 : W := mkw 0x02000285c000256e 0x8b000387c00003ff

def z98 : W := mkw 0x0000000100002044 0xdf8183070201e3c7

def z99 : W := mkw 0x02c14284c300952a 0x00404080c1801c38

def z100 : W := mkw 0x0afdebd6eb00952a 0x7bfffffffd801c38

def z101 : W := mkw 0x81081161103762c5 0xeeb80360027fe3c7

def z102 : W := mkw 0x9002142857fdde1b 0xfd467cf8fffffe3f

def z103 : W := mkw 0x00fde94220000000 0x7bffff6730000000

def z104 : W := mkw 0x042e017803da03b0 0x243e007803fe03f8

def z105 : W := mkw 0x0afdebd7ab00b164 0x7bfffffffe00e1c0

def z106 : W := mkw 0x14f7fc2803ffdbb0 0x74fffc0003fffff8

def z107 : W := mkw 0x02014005c000b44e 0xdd41c087c181fe3f

def z108 : W := mkw 0x08ffffd6a8e10800 0x7ffffffffdf11c00

def z109 : W := mkw 0x10f7fe8003edd920 0x7effff8003fffff8

def z110 : W := mkw 0x02c142858300b164 0x028183070200e1c0

def z111 : W := mkw 0x9011fc005425dc0b 0x9101fc00fc01fc07

def z112 : W := mkw 0x0018a14220000000 0x7bfffffffc000000

def z113 : W := mkw 0x00d1f0000325d000 0x74f9f00003fffc00

def z114 : W := mkw 0x18e74e948bc89800 0x00464c98cd801c00

def z115 : W := mkw 0x0810a80228000000 0x00003c003c000000

def z116 : W := mkw 0x98fffffefffdde1b 0xfffffffffffffe3f

def z117 : W := mkw 0x100014000025d800 0x000000000001fc00

def z118 : W := mkw 0x91f7fc2113fffac5 0xf4fffc0003ffffc7

def z119 : W := mkw 0x00080161001222c4 0xffb98367027fe3c7

def z120 : W := mkw 0x042e03f800da03b0 0x2a3e03f8007e03f8

def z121 : W := mkw 0x8000002814100211 0x000000783c000000

def z122 : W := mkw 0x00e6000003c80000 0x64fe000003fe0000

def z123 : W := mkw 0x14fffff803ffdbb0 0x7efffff803fffff8

def z124 : W := mkw 0x00f5e80000000000 0x70fffc0000000000

def z125 : W := mkw 0x18ffffd6abedd800 0x7ffffffffffffc00

def z126 : W := mkw 0x82c15685d721bd6f 0xdfc1ff87ff81ffff

def z127 : W := mkw 0x02014005c000b44e 0x9101c007c001fc07

def z128 : W := mkw 0x0afdebd7eb00b56e 0xffffffffff81ffff

def z129 : W := mkw 0x04ee03f803da03b0 0x22be0378027e01c0

def z130 : W := mkw 0x080803d6a8000000 0x0200030700000000

def z131 : W := mkw 0x02c142858300b164 0xdf8183070201e3c7

def z132 : W := mkw 0x04e6029803c80130 0x4ec60398038003f8

def z133 : W := mkw 0x10f5fc000025d800 0x70fffc000001fc00

def z134 : W := mkw 0x0402002803da03b0 0x0400000003fe03f8

def z135 : W := mkw 0x80f7fc2854f10e1b 0xfdfffcf8fdf11e3f

def z136 : W := mkw 0x18fdebd6ab0cd000 0x7bfffffffe0ee000

def z137 : W := mkw 0x1202140143edfd6e 0x8400000003ffffff

def z138 : W := mkw 0x1013fc0003edd800 0x1401fc0003fffc00

def z139 : W := mkw 0x0ce74a9c8bc80130 0x00464c98cd800038

def z140 : W := mkw 0x04ec03d0030a01a0 0x02b80300020e01c0

def z141 : W := mkw 0x8000140054210c0b 0x91007c00fc011c07

def z142 : W := mkw 0x1011fc000025d800 0x74b9fc00027ffc00

def z143 : W := mkw 0x08fdebd6a8000000 0x72ffff0700000000

def z144 : W := mkw 0x09fdebd7a80660c4 0x02b98307020ee1c0

def z145 : W := mkw 0x0118a143200660c4 0x02b98307020ee1c0

def z146 : W := mkw 0x8110b00330256045 0x9101b0073001e007

def z147 : W := mkw 0x00ec03d000000000 0x7bfe7ff8fc000000

def z148 : W := mkw 0x00c14284c000040a 0xdfc1c387c1811e3f

def z149 : W := mkw 0x00e7400003c89000 0x74ffc00003fffc00

def z150 : W := mkw 0x8000140054210c0b 0xf9467cf8fc011c07

def z151 : W := mkw 0x0000140000210800 0x10007c0000011c00

def z152 : W := mkw 0x00ec03f000120280 0x6efe03f8027e03c0

def z153 : W := mkw 0x02000005c000244e 0x81000007c0000007

def z154 : W := mkw 0x8002142814f10a11 0x0000000000700000

def z155 : W := mkw 0x880a17fefcf10e1b 0xff467ffffdf11e3f

def z156 : W := mkw 0x04ee03d803ca01b0 0x02fe0398038e01f8

def z157 : W := mkw 0x0000000100002044 0x910180070001e007

def z158 : W := mkw 0x0000028480000000 0x0b000387c0000000

def z159 : W := mkw 0x08fdebd6ab009000 0x7fffffffff81fc00

def z160 : W := mkw 0x040803d0000201a0 0x02000300000001c0

def z161 : W := mkw 0x0002002800d00210 0x6c4600f801f00238

def z162 : W := mkw 0x10f5e800030cd000 0x00b98000020ee000

def z163 : W := mkw 0x90f7fc2857fdde1b 0xfdfffcf8fffffe3f

def z164 : W := mkw 0x0002040844c00c1a 0x0000000001801c38

def z165 : W := mkw 0x1037fc0000edd800 0x303ffc00007ffc00

def z166 : W := mkw 0x00c1400003009000 0x008180000200e000

def z167 : W := mkw 0x14e74e9803c89930 0x00464c9801801c38

def z168 : W := mkw 0x00c0028103002164 0xdfc183870381e3ff

def z169 : W := mkw 0x00f7fc0000e10800 0x74fffc0001f11c00

def z170 : W := mkw 0x080803d6a8000000 0x0b0003fffc000000

def z171 : W := mkw 0x02c14285c300b56e 0x868183070381ffff

def z172 : W := mkw 0x02c14284c300952a 0x54c1c080c381fc38

def z173 : W := mkw 0x04e6069847c80d3a 0x00464c98cd801c38

def z174 : W := mkw 0x10f7fc0003edd800 0x7dfffcf8fffffc00

def z175 : W := mkw 0x12f5ea85c30cf56e 0xdff9c387c38fffff

def z176 : W := mkw 0x000000004000040a 0x8400000001811e3f

def z177 : W := mkw 0x0801480488000000 0x00004c00cc000000

def z178 : W := mkw 0x81081163303762c5 0x8f000367327fe3c7

def z179 : W := mkw 0x02c14284c300952a 0x5bc1c387c1801c38

def z180 : W := mkw 0x89fdebf7b81222c5 0xfbfffffffc0003c7

def z181 : W := mkw 0x0602002943dab7fe 0x8400000003ffffff

def z182 : W := mkw 0x04ef43f803da93b0 0x7effc3f803fffff8

def z183 : W := mkw 0x04ee03f843da07ba 0xfffe43f8c3ff1fff

def z184 : W := mkw 0x04e4029003080120 0x0000000000000000

def z185 : W := mkw 0x88fffffefcf10e1b 0xfffffffffdf11e3f

def z186 : W := mkw 0x0026000000c80000 0x203e0000007e0000

def z187 : W := mkw 0x80c356acd4f10e1b 0xffc7fffffdf11e3f

def z188 : W := mkw 0x00e4029000000000 0x0046009800000000

def z189 : W := mkw 0x8100000330002045 0x8100000730000007

def z190 : W := mkw 0x0000002000100200 0x6c00006000700200

def z191 : W := mkw 0x05fca3d3230e61e4 0x02b98307020ee1c0

def z192 : W := mkw 0x800000285410061b 0x800000000000023f

def z193 : W := mkw 0x10e5480003089000 0x0000000000000000

def z194 : W := mkw 0x883ebd7a7cf10e1b 0xfd7e7cf8fdf11e3f

def z195 : W := mkw 0x04ee03d803c80130 0x6afe03f801800038

def z196 : W := mkw 0x8813fc2efcf10e1b 0xfd47fcfffdf11e3f

def z197 : W := mkw 0x12f7fe85c3edfd6e 0xffffff87c3ffffff

def z198 : W := mkw 0x8202142957f1bf7f 0x8400000003f1ffff

def z199 : W := mkw 0x18ffefd6abc89800 0x7bfffffffd801c00

def z200 : W := mkw 0x042e017800da0290 0x203e0078007e0000

def z201 : W := mkw 0x10e74c0003c89800 0x00464c0001801c00

def z202 : W := mkw 0x81d8b3e3333763e5 0xfff9b3e733ffe3ff

def z203 : W := mkw 0x020000004300952a 0x0000000001801c38

def z204 : W := mkw 0x08ec03d6a8000000 0x6bfe03fffc000000

def z205 : W := mkw 0x8203542dd4f1be5f 0xfd47fcfffdf1fe3f

def z206 : W := mkw 0x00c140004300940a 0xddc1c080c381fe3f

def z207 : W := mkw 0x883ebd7a3cf10a11 0x203e3c783c700000

def z208 : W := mkw 0x8911f807b8256045 0x9101fc07fc01e007

def z209 : W := mkw 0x811ab56b74f76edf 0xffffffffffffffff

def z210 : W := mkw 0x0cfdebd6ab0a01a0 0x7bfffffffe0e01c0

def z211 : W := mkw 0x10f5e800030cd000 0x54f9c000038ffc00

def z212 : W := mkw 0x1011fc000025d800 0x1001fc000001fc00

def z213 : W := mkw 0x10c3540003edd800 0x54c1c00003fffc00

def z214 : W := mkw 0x94fffff857ffdfbb 0xfffffff8ffffffff

def z215 : W := mkw 0x8811fc06fc210c0b 0x9101fc07fc011c07

def z216 : W := mkw 0x880803fefc10061b 0x8b0003fffc00023f

def z217 : W := mkw 0x810a156b74f32edf 0xff467ffffdf11fff

def z218 : W := mkw 0x10f5fc00032dd800 0x10b9fc00020ffc00

def z219 : W := mkw 0x02c14285c300b56e 0x84404080c381ffff

def z220 : W := mkw 0x04feb3f803ff43b0 0x7effb3f803ffe3f8

def z221 : W := mkw 0x14febff803ff4bb0 0x6efe3ff803fe03f8

def z222 : W := mkw 0x0811e806a8000000 0x0001800700000000

def z223 : W := mkw 0x00c0028000000000 0x4ac0038000000000

def z224 : W := mkw 0x0effebffebdab7fe 0xffffffffffffffff

def z225 : W := mkw 0x1036bc0000ed4800 0x203e3c00007e0000

def z226 : W := mkw 0x000000084400041a 0x00000098cc000038

def z227 : W := mkw 0x02c14285c300b56e 0x8b404387c1801fff

def z228 : W := mkw 0x82015405d421bc4f 0x9101fc07fc01fc07

def z229 : W := mkw 0x0002142800f10a10 0x7c467cf801f11e38

def z230 : W := mkw 0x04ec03f8001203b0 0x6afe03f8000003f8

def z231 : W := mkw 0x18ffffd6abedd800 0x76ffff0703fffc00

def z232 : W := mkw 0x8002042854d00e1b 0x89464cf8fd801e3f

def z233 : W := mkw 0x10f7fe8483edd800 0x7fffff87c3fffc00

def z234 : W := mkw 0x80ee17f854f10e1b 0xfffe7ff8fdf11e3f

def z235 : W := mkw 0x04000000030a01a0 0x00000000020e01c0

def z236 : W := mkw 0x0808015228000000 0x000000783c000000

def z237 : W := mkw 0x12f7fe8583edf964 0x76ffff0703fffdc0

def z238 : W := mkw 0x851ab16b33ff63f5 0xffb9b36733ffe3ff

def z239 : W := mkw 0x08fcabd228000000 0x6afe3ff83c000000

def z240 : W := mkw 0x04ee07f847da0fba 0x6efe4ff8cffe1ff8

def z241 : W := mkw 0x08fde95228000000 0x70fffc783c000000

def z242 : W := mkw 0x83dbf7eff7f7ffff 0xffffffffffffffff

def z243 : W := mkw 0x0118a163201662c4 0x6eb98367027ee3c0

def z244 : W := mkw 0x84e616b857f90f3b 0xfd467cf8fdf11e3f

def z245 : W := mkw 0x85ee13f913ff63f5 0xeefe03f803ffe3ff

def z246 : W := mkw 0x0a11e807e800b44e 0x9101fc07fc01fc07

def z247 : W := mkw 0x840a17f854f30fbb 0xff467ff8fdf11fff

def z248 : W := mkw 0x000803d000000000 0x0a0003f800000000

def z249 : W := mkw 0x00ec03d000000000 0x6afe03f800000000

def z250 : W := mkw 0x0a0803d7e800256e 0x8b0003fffc0003ff

def z251 : W := mkw 0x02c14285c300b56e 0x9381c307c201fdc7

def z252 : W := mkw 0x8118b56374376ecf 0xffb9ff67fe7fffc7

def z253 : W := mkw 0x8112b42b74f56e5f 0xfd47fcfffdf1fe3f

def z254 : W := mkw 0x0000000000000000 0x11007c00fc000000

def z255 : W := mkw 0x8108016b741226df 0x8b0003fffc0003ff

def z256 : W := mkw 0x1036bc0003edd800 0x243e3c0003fffc00

def z257 : W := mkw 0x083cabd6a8000000 0x2b3e3ffffc000000

def z258 : W := mkw 0x0200028580002164 0x02000307000001c0

def z259 : W := mkw 0x0000002000120280 0x04000000027e03c0

def z260 : W := mkw 0x81fcb3f3303762c5 0xffffb3ff327fe3c7

def z261 : W := mkw 0x10014c0000009800 0x00004c0000001c00

def z262 : W := mkw 0x10f7fc0003edd800 0x04b9800003fffc00

def z263 : W := mkw 0x00c1428580002044 0xdfc1c387c201e3c7

def z264 : W := mkw 0x0002040844c00c1a 0x00464c98cd801c38

def z265 : W := mkw 0x8000102010310201 0xfd00306030710207

def z266 : W := mkw 0x0afdebd7e800256e 0xfbfffffffc0003ff

def z267 : W := mkw 0x0cfdebd6ab0a01a0 0x02b98307020e01c0

def z268 : W := mkw 0x80e6142857f90e1b 0xfdfe7cf8ffff1e3f

def z269 : W := mkw 0x1002140003edd800 0x74467c0003fffc00

def z270 : W := mkw 0x04ee03f803da03b0 0x0a4603f8018003f8

def z271 : W := mkw 0x02c3468cc7c09d3a 0x00464c98cd801c38

def z272 : W := mkw 0x0000000100002044 0x028183070200e1c0

def z273 : W := mkw 0x90f7fc0057eddc0b 0xf5fffc00fffffc07

def z274 : W := mkw 0x89fffffffcf76edf 0xffffffffffffffff

def z275 : W := mkw 0x8102142954f76edf 0xfd467cf8ffffffff

def z276 : W := mkw 0x0002140000e10800 0x74467c0001f11c00

def z277 : W := mkw 0x80c3542857f19e1b 0xfdc7fcf8fff1fe3f

def z278 : W := mkw 0x0110a00320046044 0x000180070000e000

def z279 : W := mkw 0x0819ebd6a8000000 0x1b01fffffc000000

def z280 : W := mkw 0x00f5e80003009000 0x74fffc000381fc00

def z281 : W := mkw 0x911ab56333fffac5 0xffb9b36733ffffc7

def z282 : W := mkw 0x0002040000c00800 0x00464c0001801c00

def z283 : W := mkw 0x1010bc0000254800 0x00003c0000000000

def z284 : W := mkw 0x0000000100002044 0x840000000201e3c7

def z285 : W := mkw 0x84ee17f817fb0bb1 0x6efe3ff83ffe03f8

def z286 : W := mkw 0x0002140000e10800 0x7d467cf8fdf11c00

def z287 : W := mkw 0x12c35685c3edfd6e 0xdfc1c387c3ffffff

def z288 : W := mkw 0x02c142858300b164 0x5bc1c387c200e1c0

def z289 : W := mkw 0x800010285431061b 0xfd0030f8fc71023f

def z290 : W := mkw 0x0012b40000e54800 0x74fffc0003fffc00

def z291 : W := mkw 0x8319f167f037f6cf 0xffb9f367f27fffc7

def z292 : W := mkw 0x8110b00330256045 0xdf81b3073201e3c7

def z293 : W := mkw 0x08ed4bd488000000 0x6afe4ff8cc000000

def z294 : W := mkw 0x04ee03f803da03b0 0x06b8030003fe03f8

def z295 : W := mkw 0x0000000100002044 0x8b000307000003c7

def z296 : W := mkw 0x10f7fc2803fdda10 0x7cfffcf803fffe38

def z297 : W := mkw 0x8000102010310201 0x2000306030700000

def z298 : W := mkw 0x8110b00330256045 0xf5b9b007327fe007

def z299 : W := mkw 0x02000285c000256e 0xdf404387c1811fff

def z300 : W := mkw 0x0010b00100256044 0xffb9b307027fe3c7

def z301 : W := mkw 0x8018b16230310201 0xffb9b36730710207

def z302 : W := mkw 0x12f7fc05c3edfc4e 0xf5fffc07c3fffc07

def z303 : W := mkw 0x02c14284c300952a 0x4ec04380c3801ff8

def z304 : W := mkw 0x02c140014300b56e 0xd4c1c0000381ffff

def z305 : W := mkw 0x840803f8541207bb 0x8b0003f8fc0003ff

def z306 : W := mkw 0x02f5ea85c300b56e 0xffffff87c381ffff

def z307 : W := mkw 0x8002142814f10a11 0x6c463cf83df00238

def z308 : W := mkw 0x020000010300b164 0x000000000200e1c0

def z309 : W := mkw 0x8cfffffefffb0fbb 0xffffffffffff1fff

def z310 : W := mkw 0x1011e8000004d000 0x000180000000e000

def z311 : W := mkw 0x8008116010330281 0xffb83360327f03c7

def z312 : W := mkw 0x88fdfbf6b8310201 0xfffffffffc710207

def z313 : W := mkw 0x1211fc05c025fc4e 0x9101fc07c001fc07

def z314 : W := mkw 0x08fdebd6a8000000 0x5bf9c387c0000000

def z315 : W := mkw 0x18f7fc06abedd800 0x75fffc07fffffc00

def z316 : W := mkw 0x8118b163303762c5 0x9b01b3673001e3c7

def z317 : W := mkw 0x00c1428480000000 0x0281830700000000

def z318 : W := mkw 0x81001021103762c5 0xdf818307027fe3c7

def z319 : W := mkw 0x0000000000000000 0x684600f800000000

def z320 : W := mkw 0x88fdffd6fc210c0b 0xfbfffffffc011c07

def z321 : W := mkw 0x00ee03d003c80000 0x6efe03f803fe0000

def z322 : W := mkw 0x800000285410061b 0x890000f8fc00023f

def z323 : W := mkw 0x8118b163303762c5 0xb139b067307fe007

def z324 : W := mkw 0x86ef57fdd7fbbfff 0xffffffffffffffff

def z325 : W := mkw 0x083ca95228000000 0x203e3c783c000000

def z326 : W := mkw 0x06ef43fcc3da97ba 0x6efe43f8c3fe1ff8

def z327 : W := mkw 0x00c1400003009000 0x0040400001801c00

def z328 : W := mkw 0x0002002800d00210 0x7d467cf8fdf00238

def z329 : W := mkw 0x8918b3f7b83762c5 0xffb9b3fffe7fe3c7

def z330 : W := mkw 0x85fcb3f3333f63e5 0xffb9b367327fe3c7

def z331 : W := mkw 0x0ae54a95cb00b56e 0xdfc7cf9fcf81ffff

def z332 : W := mkw 0x0000100000210000 0x7400300000710000

def z333 : W := mkw 0x92f7feadd7fdff7f 0xffffffffffffffff

def z334 : W := mkw 0x08fdebd6a8000000 0x6aff83ff00000000

def z335 : W := mkw 0x00f5e80000000000 0x79fffcf8fc000000

def z336 : W := mkw 0x1036bc0000ed4800 0x747e7c0001ff1c00

def z337 : W := mkw 0x083ca95228000000 0x7bbfbf7f3c000000

def z338 : W := mkw 0x02000285c000256e 0xdf818387c201e3ff

def z339 : W := mkw 0x8002142854f10e1b 0x95007c00fdf11e3f

def z340 : W := mkw 0x0000100000254000 0x04000000027fe000

def z341 : W := mkw 0x0000000000000000 0x00464c98cc000000

def z342 : W := mkw 0x8502102913ff63f5 0x8400000003ffe3ff

def z343 : W := mkw 0x99fffff7bbfffac5 0xffffffffffffffc7

def z344 : W := mkw 0x18ffffd6a8ed4800 0x7bfffffffc7e0000

def z345 : W := mkw 0x020000014300b56e 0xdd404080c381ffff

def z346 : W := mkw 0x10e6140003edd800 0x64fe000003fffc00

def z347 : W := mkw 0x8010b02010354201 0xfdb9b060327fe207

def z348 : W := mkw 0x8402142857fb0fbb 0x8400000003ff1fff

def z349 : W := mkw 0x0002040844c00c1a 0x79467cf8fd801c38

def z350 : W := mkw 0x02c1428483009120 0x0000000000000000

def z351 : W := mkw 0x00c803e0031203a0 0x6ef803e003fe03f8

def z352 : W := mkw 0x8118b16b743766df 0xffb9b3fffe7fe3ff

def z353 : W := mkw 0x820216add4f12f7f 0xff467ffffdf11fff

def z354 : W := mkw 0x8518b3fb303763f5 0xffb9b3ff327fe3ff

def z355 : W := mkw 0x08ed4bd6a8000000 0x0b464ffffc000000

def z356 : W := mkw 0x0000000000000000 0x4e800300020003c0

def z357 : W := mkw 0x08d1ea86a8000000 0x5bc1ff87fc000000

def z358 : W := mkw 0x81080163301222c5 0xefb80367327e03c7

def z359 : W := mkw 0x84ee17f857fb0fbb 0xfffe7ff8ffff1fff

def z360 : W := mkw 0x8000102010310201 0x8400000000710207

def z361 : W := mkw 0x9036bc2854fd4e1b 0xfd7e7cf8fdff1e3f

def z362 : W := mkw 0x84ee13f813fb03b1 0xfffe33f833ff03ff

def z363 : W := mkw 0x9002142857fdde1b 0x8400000003fffe3f

def z364 : W := mkw 0x91fffd6b77fffedf 0xffffffffffffffff

def z365 : W := mkw 0x08ffefdeecc00c1a 0x7bfffffffd801c38

def z366 : W := mkw 0x95fffffb33fffbf5 0xffffffff33ffffff

def z367 : W := mkw 0x00c002804300052a 0xdfc04380c3811fff

def z368 : W := mkw 0x04ffebf803da03b0 0x7efffff803fe03f8

def z369 : W := mkw 0x8002142854f10e1b 0xec4600f801f11e3f

def z370 : W := mkw 0x02c943e5c312b7ee 0xfff9c3e7c3ffffff

def z371 : W := mkw 0x01080143200220c4 0x02000307000001c0

def z372 : W := mkw 0x9102142113fffac5 0x8400000003ffffc7

def z373 : W := mkw 0x00c0028003000120 0x0040008001800038

def z374 : W := mkw 0x8108016230120281 0x0000006030000000

def z375 : W := mkw 0x9036bc2814fd4a11 0x203e3c783c7e0000

def z376 : W := mkw 0x0118b143202760c4 0x76b9b307027fe1c0

def z377 : W := mkw 0x0afdebd7eb00b56e 0xdff9c387c381ffff

def z378 : W := mkw 0x10f7fc0847eddc1a 0x74fffc98cffffc38

def z379 : W := mkw 0x0000000000000000 0x5440400001811c00

def z380 : W := mkw 0x02014285c000b56e 0x9b01c387c001ffff

def z381 : W := mkw 0x02c14284c300952a 0xdd404080c1811e3f

def z382 : W := mkw 0x91fffd6233ffda81 0x74fffc6033fffc00

def z383 : W := mkw 0x06ee03fdc3da27fe 0xeffe03ffc3fe03ff

def z384 : W := mkw 0x1036bc0000ed4800 0x74bfbc00027fe000

def z385 : W := mkw 0x0800029488000000 0x00000098cc000000

def z386 : W := mkw 0x18f7fe948bedd800 0x74fffc98cffffc00

def z387 : W := mkw 0x811ab56b74f76edf 0xffb9b36733ffffff

def z388 : W := mkw 0x04ec03f8031a03b0 0x0ab803f8020e03f8

def z389 : W := mkw 0x08fdebd6a8000000 0x02ffcf9fcc000000

def z390 : W := mkw 0x1affffd7ebedfd6e 0xffffffffffffffff

def z391 : W := mkw 0x8002102810f10211 0xfd4630f831f1023f

def z392 : W := mkw 0x08f5ea9488000000 0x70fffc98cc000000

def z393 : W := mkw 0x0000000000000000 0x4c40008001800238

def z394 : W := mkw 0x18fdebd6ab0cd000 0x02b98307020ee000

def z395 : W := mkw 0x02d1f285c325f56e 0xfff9f387c3ffffff

def z396 : W := mkw 0x8311f007f025f44f 0x9101f007f001fc07

def z397 : W := mkw 0x02c342adc3d0b77e 0xffc7c3ffc3f1ffff

def z398 : W := mkw 0x04e6002803da03b0 0x64fe000003fe03f8

def z399 : W := mkw 0x12f5ea85830cf164 0x02b98307020ee1c0

def z400 : W := mkw 0x16fffffdc3fffffe 0xffffffffc3ffffff

def z401 : W := mkw 0x820002add410277f 0x8b0003fffc0003ff

def z402 : W := mkw 0x0002000003c80000 0x0400000003fe0000

def z403 : W := mkw 0x14ffffd003efd9a0 0x76ffff0003fffdc0

def z404 : W := mkw 0x0402002800da0290 0x00000000007e0000

def z405 : W := mkw 0x02c14285c300b56e 0xffc7ffffff81ffff

def z406 : W := mkw 0x0018a14220000000 0x02b9830700000000

def z407 : W := mkw 0x8000140054210c0b 0xdd407c80fd811e3f

def z408 : W := mkw 0x080803d6a8000000 0x7b467ffffc000000

def z409 : W := mkw 0x08fdebd6a8000000 0x13b9ff07fc000000

def z410 : W := mkw 0x91f7fc0333edf845 0xf5fffc0733fffc07

def z411 : W := mkw 0x890803f7b81222c5 0x8b0003fffc0003c7

def z412 : W := mkw 0x8000142054310e0b 0xfd007c60fc711e07

def z413 : W := mkw 0x83c943e7f312b7ef 0xdfc1c3e7f381ffff

def z414 : W := mkw 0x0000040044000c0a 0x00004c00cc001c00

def z415 : W := mkw 0x0000000000000000 0x548180000201e000

def z416 : W := mkw 0x00f5ea8480000000 0x7bffff87c0000000

def z417 : W := mkw 0x02014005c300b56e 0x9501c007c381ffff

def z418 : W := mkw 0x04c202a803da03b0 0x4ec0038003fe03f8

def z419 : W := mkw 0x02e74285c3c8b56e 0xffffc387c3ffffff

def z420 : W := mkw 0x1402142803ffdbb0 0x0400000003fffff8

def z421 : W := mkw 0x14ffebf803ded3b0 0x6eff83f803fee3f8

def z422 : W := mkw 0x08fdebd6ab000120 0x7fffffffff8003f8

def z423 : W := mkw 0x0000000000000000 0x5b81830700000000

def z424 : W := mkw 0x0008016000120280 0x0a000360000003c0

def z425 : W := mkw 0x06ed43d5c30ab5ee 0xdff9c387c38fffff

def z426 : W := mkw 0x04ee03f803da03b0 0x7ffe7ff8fffe03f8

def z427 : W := mkw 0x84ee03f857da07bb 0xeffe03f8fffe03ff

def z428 : W := mkw 0x04ef43fc83da03b0 0x7fffc3ffc3fe03f8

def z429 : W := mkw 0x8118b16230374281 0xfd383060307f0207

def z430 : W := mkw 0x801ab56a74f10e1b 0xfffffffffdf11e3f

def z431 : W := mkw 0x000a016800d20290 0x6efe03f803fe03f8

def z432 : W := mkw 0x10f7fc0103edf844 0xffffff0703ffffc7

def z433 : W := mkw 0x0002000000c00000 0x6446000001f00000

def z434 : W := mkw 0x0018b16000374280 0x7eb9b360027fe3c0

def z435 : W := mkw 0x0819e946a8000000 0x7bb9ff67fc000000

def z436 : W := mkw 0x84ee17f857fb0fbb 0xeefe03f803ff1fff

def z437 : W := mkw 0x8002140054e10c0b 0xf5467c00fdf11c07

def z438 : W := mkw 0x0ac943d7eb00b56e 0xdfc1c3ffff81ffff

def z439 : W := mkw 0x00fca3d220000000 0x7bffb3ff30000000

def z440 : W := mkw 0x0034a80000000000 0x203e3c0000000000

def z441 : W := mkw 0x0000000000000000 0xdd00000000010207

def z442 : W := mkw 0x03d9e3c7a306f1e4 0x02b98307020ee1c0

def z443 : W := mkw 0x800a156854f30e9b 0xfffe7ff8ffff1fff

def z444 : W := mkw 0x850803fb301223f5 0x8b0003ff300003ff

def z445 : W := mkw 0x02000285c300b56e 0x8f000387c381ffff

def z446 : W := mkw 0x0000000000000000 0x64b80000027e0000

def z447 : W := mkw 0x8002002854d0061b 0xed4600f8fdf0023f

def z448 : W := mkw 0x00c1428480000000 0x00404080c0000000

def z449 : W := mkw 0x811ab56a74f74e9b 0xfd7e7cf8fdff1e3f

def z450 : W := mkw 0x0010b00000254000 0x1001b0000001e000

def z451 : W := mkw 0x8102142954f76edf 0x8400000003ffffff

def z452 : W := mkw 0x00e6028003c80120 0x6efe038003fe03f8

def z453 : W := mkw 0x020000014300b56e 0xdf8183070381ffff

def z454 : W := mkw 0x9111fc033025f845 0x9101fc073001fc07

def z455 : W := mkw 0x8110b40374256c4f 0x9101fc07fc01fc07

def z456 : W := mkw 0x06ee03f943dab7fe 0xeefe03f803ffffff

def z457 : W := mkw 0x08ffebd6abc80000 0x7ffffffffffe0000

def z458 : W := mkw 0x04fea3fa23da03b0 0x7fffb3ff33fe03f8

def z459 : W := mkw 0x02014004c000940a 0x00004000c0001c00

def z460 : W := mkw 0x040803f8001203b0 0x6eb803f8027e03f8

def z461 : W := mkw 0x0001400000009000 0x1001c0000001fc00

def z462 : W := mkw 0x8118b16230374281 0x74b9b060327fe000

def z463 : W := mkw 0x1cfffffeabffdbb0 0x7ffffffffffffff8

def z464 : W := mkw 0x8012b42854f54e1b 0xfdfffcf8fffffe3f

def z465 : W := mkw 0x0ae54a94cb00952a 0x00464c98cd801c38

def z466 : W := mkw 0x00c1428003009120 0x5ec1c3800381fff8

def z467 : W := mkw 0x10000000030cd000 0x00000000020ee000

def z468 : W := mkw 0x8118a163301222c5 0xfbb9b367300003c7

def z469 : W := mkw 0x040a016803da03b0 0x6eb8036003fe03f8

def z470 : W := mkw 0x0002042844d00e1a 0x6c464cf8cdf01e38

def z471 : W := mkw 0x00c1428480000000 0x7bc7fffffc000000

def z472 : W := mkw 0x8118b143302760c5 0x93b9b307320fe1c7

def z473 : W := mkw 0x08fdebf6a8120280 0x7ffffffffe7e03c0

def z474 : W := mkw 0x0010b00000254000 0x20383000007e0000

def z475 : W := mkw 0x10260c0000c80800 0x00060c0000000000

def z476 : W := mkw 0x0000000000000000 0x70467c0000000000

def z477 : W := mkw 0x10f5e800030cd000 0x70fffc00020ee000

def z478 : W := mkw 0x00ee016003da0280 0x6efe036003fe03c0

def z479 : W := mkw 0x042e017800da0290 0x6c7e00f801fe0238

def z480 : W := mkw 0x8118b14330256045 0xfbb9b3673001e007

def z481 : W := mkw 0x000000004000040a 0xfd467cf8fd811e3f

def z482 : W := mkw 0x000000004000040a 0x00404080c1801c38

def z483 : W := mkw 0x0118a143200660c4 0xdfb98307020fe3c7

def z484 : W := mkw 0x020000014000b44e 0x800000000001fc07

def z485 : W := mkw 0x04ee017803da0290 0x64fe007803fe0000

def z486 : W := mkw 0x0c3ea97a28da0290 0x203e3c783c7e0000

def z487 : W := mkw 0x00fdebd000000000 0x7afffff800000000

def z488 : W := mkw 0x82c356acd7f19f3b 0xfd467cf8fdf11e3f

def z489 : W := mkw 0x00ec03d000000000 0x02b8030000000000

def z490 : W := mkw 0x0cffebdeabc80130 0x7bfffffffd800038

def z491 : W := mkw 0x81fdf963303762c5 0xffffff67327fe3c7

def z492 : W := mkw 0x02c002814300b56e 0xcec003800381ffff

def z493 : W := mkw 0x0000000000000000 0x20063c783c000000

def z494 : W := mkw 0x0018a16220120280 0x7fb9b367327e03c0

def z495 : W := mkw 0x8110b00230254001 0x0000300030000000

def z496 : W := mkw 0x0c0803fea81203b0 0x0b0003fffc0003f8

def z497 : W := mkw 0x8000140054210c0b 0x8000000000011c07

def z498 : W := mkw 0x00c0028003000120 0x02800300020001c0

def z499 : W := mkw 0x8002142814f10a11 0x79467cf8fc700000

def z500 : W := mkw 0x00e6000003c80000 0x0046000001800000

def z501 : W := mkw 0x02c14005c300b44e 0xd5c1c007c381fc07

def z502 : W := mkw 0x811ab56b34f76ad5 0xffbfbf7f3e7fe3c7

def z503 : W := mkw 0x0cfdebfea81203b0 0x7bfffffffc0003f8

def z504 : W := mkw 0x00f6b00003ed4000 0x74ffb00003ffe000

def z505 : W := mkw 0x10f7fc0003edd800 0x207e7c0001fe1c00

def z506 : W := mkw 0x88e75ebcdcf10e1b 0xfd467cf8fdf11e3f

def z507 : W := mkw 0x0008016000120280 0x20380060007e0000

def z508 : W := mkw 0x02000284c000052a 0x00000080c0000038

def z509 : W := mkw 0x8002142010f10a01 0xfd467c6031f11e07

def z510 : W := mkw 0x842e157854fb0e9b 0xfd7e7cf8fdff1e3f

def z511 : W := mkw 0x8002142854f10e1b 0x20467cf8fdf01c38

def z512 : W := mkw 0x10f7ec0003ccd800 0x00ffcc00038efc00

def z513 : W := mkw 0x08fdebd6a8000000 0x7bb9b36730000000

def z514 : W := mkw 0x0018a14320002044 0xffb9b3673201e3c7

def z515 : W := mkw 0x0010a00220000000 0x1101b00730000000

def z516 : W := mkw 0x10e74c0003c89800 0x64fe4c0003fe1c00

def z517 : W := mkw 0x083ca95228000000 0x797e7cf8fc000000

def z518 : W := mkw 0x00e4000003080000 0x00b80000020e0000

def z519 : W := mkw 0x0000002800100210 0x080000f800000238

def z520 : W := mkw 0x8000100010210001 0x9100300030010007

def z521 : W := mkw 0x08e54a9488000000 0x79467cf8fc000000

def z522 : W := mkw 0x0000000003009000 0x040000000381fc00

def z523 : W := mkw 0x06c943fdc312b7fe 0xdfc1c3ffc381ffff

def z524 : W := mkw 0x800000285410061b 0xf9467cf8fc00023f

def z525 : W := mkw 0x10fffd4223edd800 0x7fffff6733fffc00

def z526 : W := mkw 0x83c152a5d337f7ef 0xdfc1c387c3ffffff

def z527 : W := mkw 0x000000004000040a 0x91004000c0011c07

def z528 : W := mkw 0x1012b40003edd800 0x74b9b00003fffc00

def z529 : W := mkw 0x1034a800000c4000 0x00380000000e0000

def z530 : W := mkw 0x12f7fe84c3eddd2a 0x74fffc80c3fffc38

def z531 : W := mkw 0x842e157814fb0a91 0x203e3c783c7e0000

def z532 : W := mkw 0x1002140000ed4800 0x00000000007e0000

def z533 : W := mkw 0x18fdffd6a825d800 0x7bfffffffc01fc00

def z534 : W := mkw 0x83d1f287f325f56f 0xdfc1f387f381ffff

def z535 : W := mkw 0x89fdfbf6b8374281 0x7bfffffffc7e0000

def z536 : W := mkw 0x8118b16230374281 0x7bb9b367307e0000

def z537 : W := mkw 0x01000001000660c4 0x00000000020ee1c0

def z538 : W := mkw 0x040a03f800d203b0 0x6e4603f801f003f8

def z539 : W := mkw 0x000000004000040a 0x89000080c000023f

def z540 : W := mkw 0x0402000803c80130 0x0000000001800038

def z541 : W := mkw 0x1002040003c89800 0x0000000001801c00

def z542 : W := mkw 0x10f7fc0000ed4800 0x70fffc00007e0000

def z543 : W := mkw 0x10ffffd003edd800 0x7efffff803fffc00

def z544 : W := mkw 0x8919f967b83762c5 0xffb9ff67fe7fe3c7

def z545 : W := mkw 0x00ed43d480000000 0x7bffc3ffc0000000

def z546 : W := mkw 0x0cffebfea8da0290 0x7bfffffffc7e0000

def z547 : W := mkw 0x00c3540003e19800 0x74c7fc0003f1fc00

def z548 : W := mkw 0x00e4000000000000 0x60fe000000000000

def z549 : W := mkw 0x03d9e3c7e306f5ee 0xdff9c387c38fffff

def z550 : W := mkw 0x14fdebd0030ed1a0 0x02b98300020ee1c0

def z551 : W := mkw 0x00ee03f800d00210 0x6efe03f801f00238

def z552 : W := mkw 0x10f7ec0003c89800 0x70fffc0001801c00

def z553 : W := mkw 0x0cffebfeabda03b0 0x6eff83ff03fe03f8

def z554 : W := mkw 0x08fdfbd6a8254000 0x7ffffffffe7fe000

def z555 : W := mkw 0x8000102110312245 0xff81b3673271e3c7

def z556 : W := mkw 0x0002002800d00210 0x2006007800700000

def z557 : W := mkw 0x042e017800da0290 0x6ebe0378027e03c0

def z558 : W := mkw 0x00e5480000000000 0x00464c0000000000

def z559 : W := mkw 0x0008014220000000 0x0b00036730000000

def z560 : W := mkw 0x85ee03fb33da23f5 0xeffe03ff33fe03ff

def z561 : W := mkw 0x80c216a857f10f3b 0xffc67ff8fff11fff

def z562 : W := mkw 0x8318b1637337f7ef 0xffb9b36733ffffff

def z563 : W := mkw 0x10f7e80003ccd000 0x64ff800003fee000

def z564 : W := mkw 0x12e74e85c3c8bd6e 0xdfc7cf87c381ffff

def z565 : W := mkw 0x00c202a803d00330 0x6ec603f803f003f8

def z566 : W := mkw 0x0010a00000000000 0x70b9b00000000000

def z567 : W := mkw 0x0018b14220254000 0x7fb9b367327fe000

def z568 : W := mkw 0x00f5f80000254000 0x74fffc00027fe000

def z569 : W := mkw 0x10f7fc0003edd800 0x20bfbc00027ee000

def z570 : W := mkw 0x06c342adc3dab7fe 0xdfc1c387c3ffffff

def z571 : W := mkw 0x8118a163301662c5 0x8bb98367320ee3c7

def z572 : W := mkw 0x002c015000000000 0x203e007800000000

def z573 : W := mkw 0x8002142854f10e1b 0xa9063cf8fc70023f

def z574 : W := mkw 0x0000000000000000 0x090000f8fc000000

def z575 : W := mkw 0x0010a00000044000 0x00b98000020ee000

def z576 : W := mkw 0x00ec03d003000120 0x6efe03f8038003f8

def z577 : W := mkw 0x0824081008000000 0x00060c180c000000

def z578 : W := mkw 0x0011e80000000000 0x1001fc0000000000

def z579 : W := mkw 0x811ab56330f76ac5 0xffffff6733ffffc7

def z580 : W := mkw 0x04000028001203b0 0x00000000000003f8

def z581 : W := mkw 0x8002142854f10e1b 0x84464c98cdf11e3f

def z582 : W := mkw 0x0afdebd7e800b44e 0xfbfffffffc01fc07

def z583 : W := mkw 0x0408017800120290 0x0000007800000000

def z584 : W := mkw 0x800000005400040b 0x81000000fc000007

def z585 : W := mkw 0x00e6002803d80210 0x6cfe00f803fe0238

def z586 : W := mkw 0x89fdfbf7b83762c5 0xffb9b367327fe3c7

def z587 : W := mkw 0x8118b163703766cf 0xfff9f3e7f3ffffff

def z588 : W := mkw 0x0002002840d0061a 0xfd4640f8c1f11e3f

def z589 : W := mkw 0x81d9f3e7b03762c5 0xfff9f3e7f27fe3c7

def z590 : W := mkw 0x083ca95228000000 0x0038000000000000

def z591 : W := mkw 0x08fdebd6a8000000 0x22bfbf7f3c000000

def z592 : W := mkw 0x06ef43fd83dab3f4 0x6eff83ff03fee3f8

def z593 : W := mkw 0x0002140844e10c1a 0x74467c98cdf11c38

def z594 : W := mkw 0x8118b163303762c5 0xa4383060327fe3c7

def z595 : W := mkw 0x800000285410061b 0xdd4040f8fd811e3f

def z596 : W := mkw 0x02c14285c000256e 0xdbc1c387c00003ff

def z597 : W := mkw 0x0002140000e10800 0x0400000001f11c00

def z598 : W := mkw 0x90e75c2857f99e1b 0xfd467cf8fdf11e3f

def z599 : W := mkw 0x11fffd4323eff8c4 0x76ffff0703fffdc0

def z600 : W := mkw 0x0008014000000000 0x6ab8036000000000

def z601 : W := mkw 0x0ad1ea87eb00b56e 0xdfc1ff87ff81ffff

def z602 : W := mkw 0x8000140014210801 0x00003c003c000000

def z603 : W := mkw 0x10e75c0003edd800 0x04464c0003fffc00

def z604 : W := mkw 0x8bfdfbf7fb37f7ef 0xffffffffffffffff

def z605 : W := mkw 0x08c943d6a8000000 0x5bc1c3fffc000000

def z606 : W := mkw 0x00c140010300b044 0xdfc1c3070381ffc7

def z607 : W := mkw 0x020000014000256e 0x80000000000003ff

def z608 : W := mkw 0x8002142854f10e1b 0xdd404080c1f11e3f

def z609 : W := mkw 0x08f5ea96a8000000 0x1147fc9ffc000000

def z610 : W := mkw 0x0000028000000120 0x0a000380000003f8

def z611 : W := mkw 0x0811e806a8000000 0x7947fcfffc000000

def z612 : W := mkw 0x81000021101222c5 0x80000000000003c7

def z613 : W := mkw 0x90f7fc2857fdde1b 0xf4fffc0003fffe3f

def z614 : W := mkw 0x10d1fc000325d800 0x54c1fc000381fc00

def z615 : W := mkw 0x10e74c0847c89c1a 0x00464c98cd801c38

def z616 : W := mkw 0x82c152a5d331b76f 0xffc1f3e7f3f1ffff

def z617 : W := mkw 0x0426001800c80010 0x0006001800000000

def z618 : W := mkw 0x00f7e80003c80000 0x74fffc0003fe0000

def z619 : W := mkw 0x0001400480000000 0x1101c007c0000000

def z620 : W := mkw 0x04e6029803c80130 0x64fe009803fe0038

def z621 : W := mkw 0x8100100110256045 0x800000000001e007

def z622 : W := mkw 0x02c14285c000b44e 0xdbc1c387c001fc07

def z623 : W := mkw 0x0002002800d00210 0x0400000001f00238

def z624 : W := mkw 0x81feb16333ff62c5 0xffffb36733ffe3c7

def z625 : W := mkw 0x81080163301222c5 0xdf8183673201e3c7

def z626 : W := mkw 0x00c1428483000120 0x5fc1c387c38003f8

def z627 : W := mkw 0x8202142957f1bf7f 0xfd467cf8fff1ffff

def z628 : W := mkw 0x04ee03f903da23f4 0xffff83ff03ffe3ff

def z629 : W := mkw 0x00f5e80000000000 0x00b9800000000000

def z630 : W := mkw 0x10f7fc0003edd800 0x1047fc000181fc00

def z631 : W := mkw 0x8002142854f10e1b 0x8d0000f8fdf11e3f

def z632 : W := mkw 0x1811fc06a825d800 0x1101fc07fc01fc00

def z633 : W := mkw 0x10e75c0003e99800 0x74467c0001f11c00

def z634 : W := mkw 0x830010215337f7ef 0x8400000003ffffff

def z635 : W := mkw 0x8118b16230374281 0x6eb83360327e03c0

def z636 : W := mkw 0x8afffffffff1bf7f 0xfffffffffff1ffff

def z637 : W := mkw 0x10e74c0003c89800 0x54c7cc000381fc00

def z638 : W := mkw 0x8002142814f10a11 0x74467c783df11c00

def z639 : W := mkw 0x81d9f1633337f2c5 0xfff9f36733ffffc7

def z640 : W := mkw 0x85feb3fa33ff43b1 0x6efe33f833fe03f8

def z641 : W := mkw 0x85feb7fb77ff6fff 0xffffffffffffffff

def z642 : W := mkw 0x0000000003000120 0x04000000038003f8

def z643 : W := mkw 0x893cb97238374281 0x203e3c783c7e0000

def z644 : W := mkw 0x8318b3e7f03767ef 0xffb9b3e7f27fe3ff

def z645 : W := mkw 0x02c00285c300256e 0xcfc00387c38003ff

def z646 : W := mkw 0x88fdebfefc10061b 0xfbfffffffc00023f

def z647 : W := mkw 0x811ab16b30f762d5 0xffffb3ff33ffe3ff

def z648 : W := mkw 0x8000002010100201 0x8900006030000207

def z649 : W := mkw 0x18fffd522bedd800 0x74fffc783ffffc00

def z650 : W := mkw 0x0008014000020080 0x02b80300020e01c0

def z651 : W := mkw 0x0cfeabfa2bda03b0 0x6efe3ff83ffe03f8

def z652 : W := mkw 0x0118a14220064080 0x00380000000e0000

def z653 : W := mkw 0x04ee17f803fb0bb0 0x7efe7ff803ff1ff8

def z654 : W := mkw 0x8118b163303762c5 0xab383367307e03c7

def z655 : W := mkw 0x93ffffe7f3ffffef 0xffffffe7f3ffffff

def z656 : W := mkw 0x00c1428483009000 0x5fc1c387c381fc00

def z657 : W := mkw 0x91fdf963333ff2c5 0xffb9b367327fe3c7

def z658 : W := mkw 0x05fea3fb23de63f4 0x6eff83ff03fee3f8

def z659 : W := mkw 0x14fffd7803ffda90 0x74fffc7803fffc00

def z660 : W := mkw 0x0002040804c00810 0x00060c180c000000

def z661 : W := mkw 0x8000102010310201 0xfd467cf8fc710207

def z662 : W := mkw 0x90f7fc2817fdda11 0x74fffc783ffffc00

def z663 : W := mkw 0x08fdebd6e800040a 0xfffffffffd811e3f

def z664 : W := mkw 0x00d9e3c6a0000000 0x7bf9f3e7f0000000

def z665 : W := mkw 0x08fdebd7a8002044 0xfffffffffe01e3c7

def z666 : W := mkw 0x040a03f803da03b0 0x0e0003f803fe03f8

def z667 : W := mkw 0x87fff3fff3fff7ff 0xfffff3fff3ffffff

def z668 : W := mkw 0x00c1400000000000 0x50c1c00000000000

def z669 : W := mkw 0x8100102010374281 0x00000000007e0000

def z670 : W := mkw 0x02c14285c300b56e 0x02c1c387c380fdf8

def z671 : W := mkw 0x183ebd5228ed4800 0x203e3c783c7e0000

def z672 : W := mkw 0x8002142854f10e1b 0xf4467c0001f11e3f

def z673 : W := mkw 0x04e602b803da03b0 0x0446009803fe03f8

def z674 : W := mkw 0x02c35685c3e1bd6e 0xffc7ff87c3f1ffff

def z675 : W := mkw 0x893cb973383762c5 0xffbfbf7f3e7fe3c7

def z676 : W := mkw 0x0018a14220000000 0x2038306030000000

def z677 : W := mkw 0x0002140000e10800 0x20063c0000700000

def z678 : W := mkw 0x10f6bc0003ed4800 0x64fe3c0003fe0000

def z679 : W := mkw 0x0002040844c00c1a 0xdd464c98cd811e3f

def z680 : W := mkw 0x143ebd7800ff4a90 0x203e3c78007e0000

def z681 : W := mkw 0x82c142add710b77f 0xdfc1c3ffff81ffff

def z682 : W := mkw 0x8002142814f10a11 0xfd063c783c710207

def z683 : W := mkw 0x06e7429dc3c8b57e 0xdfc7c39fc381ffff

def z684 : W := mkw 0x02c3468dc7c0bd7e 0xdfc7cf9fcf81ffff

def z685 : W := mkw 0x04ee03f800da0290 0x6afe03f8007e0000

def z686 : W := mkw 0x10f7fc0043eddc0a 0xfdfffc80c3fffe3f

def z687 : W := mkw 0x8118b163303762c5 0x22b9b367327ee1c0

def z688 : W := mkw 0x00e6140003e90800 0x74fe7c0003ff1c00

def z689 : W := mkw 0x12f7fc0143edfd6e 0xf4fffc0003ffffff

def z690 : W := mkw 0x8110b021103762c5 0xf4b9b000027fe3c7

def z691 : W := mkw 0x0000000000000000 0x7900306030000000

def z692 : W := mkw 0x913ebd6230ff4a81 0x203e3c60307e0000

def z693 : W := mkw 0x8002142854f10e1b 0xa4063c783df11e3f

def z694 : W := mkw 0x04ec03d0030a01a0 0x6afe03f8020e01c0

def z695 : W := mkw 0x04e602b803d80330 0x6c4600f801f00238

def z696 : W := mkw 0x0000000000000000 0x59404080c0000000

def z697 : W := mkw 0x8000142854310e1b 0x99007cf8fc011e3f

def z698 : W := mkw 0x0400029800000130 0x0000009800000038

def z699 : W := mkw 0x0002140040e10c0a 0xfd467c80c1f11e3f

def z700 : W := mkw 0x83d9f3e7b337f3e5 0xffb9b367327fe3c7

def z701 : W := mkw 0x853eb17a30ff4291 0x203e3078307e0000

def z702 : W := mkw 0x82c356add7f1bf7f 0xdfc1c387c3f1ffff

def z703 : W := mkw 0x08fdebd6a8000000 0x0bb983fffc000000

def z704 : W := mkw 0x04ee03f803da03b0 0x207e00f801fe0038

def z705 : W := mkw 0x800010205031060b 0xfd4070e0f1f11e3f

def z706 : W := mkw 0x04ee03d003ca01a0 0x66fe030003fe01c0

def z707 : W := mkw 0x10f7e80003ccd000 0x74ffc00003fffc00

def z708 : W := mkw 0x10d1fc000325d800 0x74f9fc0003fffc00

def z709 : W := mkw 0x04ef43fc83da03b0 0x7ffffffffffe03f8

def z710 : W := mkw 0x080803d6a8000000 0x2b063ffffc000000

def z711 : W := mkw 0x042e03f803da03b0 0x2e3e03f803fe03f8

def z712 : W := mkw 0x88fffffefcf10e1b 0x86b9830701f11e3f

def z713 : W := mkw 0x18f7fc022bedd800 0x74fffc003ffffc00

def z714 : W := mkw 0x12e74e8cc7c89d3a 0x00464c98cd801c38

def z715 : W := mkw 0x0c13e82eabda03b0 0x1501fc07fffe03f8

def z716 : W := mkw 0x8118b163303762c5 0xa6b9b367327fe3c7

def z717 : W := mkw 0x8110b021103762c5 0xffb9b307027fe3c7

def z718 : W := mkw 0x04e6029803c80130 0x6efe039803fe03f8

def z719 : W := mkw 0x10f7fe8483edd920 0x7fffff87c3fffff8

def z720 : W := mkw 0x8002142854f10e1b 0x99467cf8fd811e3f

def z721 : W := mkw 0x800000285410061b 0xfd467cf8fd811e3f

def z722 : W := mkw 0x04ee03f803da03b0 0x7efe43f803ff1ff8

def z723 : W := mkw 0x02e74005c3c8b44e 0xf5ffc007c3fffc07

def z724 : W := mkw 0x0efdebd7ab0ab1e4 0x02b98307020ee1c0

def z725 : W := mkw 0x04ef43fc83da03b0 0x6efe43f8c3fe03f8

def z726 : W := mkw 0x8118b163303762c5 0xfff9f36733ffffc7

def z727 : W := mkw 0x08ec03d6a8000000 0x7bfe7ffffc000000

def z728 : W := mkw 0x02c14285c300b56e 0xdfc7cf9fcf81ffff

def z729 : W := mkw 0x0cef4bfc8bda03b0 0x7ffe7ff8fffe03f8

def z730 : W := mkw 0x04ee03f803da03b0 0x6ffe03f8fffe03f8

def z731 : W := mkw 0x042e03f800da03b0 0x6ebe03f8027e03f8

def z732 : W := mkw 0x8118b163303762c5 0xffffff67327fe3c7

def z733 : W := mkw 0x811ab56a34f74a91 0x20383060307e0000

def z734 : W := mkw 0x08fdebd6a8000000 0x7ffffffffe01e000

def z735 : W := mkw 0x083cabd6a8000000 0x7bbfbffffc000000

def z736 : W := mkw 0x011aa54b64c66cde 0x02ffcf9fcf8efdf8

def z737 : W := mkw 0x083debd6a8000000 0x3b3ffffffc000000

def z738 : W := mkw 0x14ee0ff803da0bb0 0x6efe0ff803fe03f8

def z739 : W := mkw 0x02c14285c300b56e 0xdfc1c3ffff81ffff

def z740 : W := mkw 0x10f7fc0003edd800 0x7cfffc8003fffe38

def z741 : W := mkw 0x00ec03f0031203a0 0x6efe03f803fe03f8

def z742 : W := mkw 0x10f7fc0003edd800 0x7effff0003ffffc0

def z743 : W := mkw 0x042e017803da03b0 0x6c7e00f803fe03f8

def z744 : W := mkw 0x0cee0bf80bda03b0 0x6efe0ff80ffe03f8

def z745 : W := mkw 0x04ef43f803da03b0 0x7effc3f803fe03f8

def z746 : W := mkw 0x89e55ab5983762c5 0x84464c98ce7fe3c7

def z747 : W := mkw 0x042e017803da03b0 0x0438000003fe03f8

def z748 : W := mkw 0x040803f8001203b0 0x2a3803f8007e03f8

def z749 : W := mkw 0x02c14285c300b56e 0x9b41c387c181ffff

def z750 : W := mkw 0x06e54295c308b56e 0xdfc1c387c381ffff

def z751 : W := mkw 0x02c14285c300b56e 0xd6c1c3070381ffff

def z752 : W := mkw 0x84ec17d0572b0dab 0x93b87f00fe0f1dc7

def z753 : W := mkw 0x08fdebd6a8000000 0x7ffffffffd800238

def z754 : W := mkw 0x16e74e9cc3c89d3a 0x00464c98c1801c38

def z755 : W := mkw 0x00c1400003009000 0x74f9c00003fffc00

def z756 : W := mkw 0x062f417dc0dab6de 0xb13fc07fc07ffc07

def z757 : W := mkw 0x02e54295c300b56e 0xdfc7c39fc381ffff

def z758 : W := mkw 0x85f6b29b33ed6175 0x9147b09f3181e03f

def z759 : W := mkw 0x04e602b803da03b0 0x64fe009803fe03f8

def z760 : W := mkw 0x00f5f8000325d000 0x74fffc0003fffc00

def z761 : W := mkw 0x8202142954f12f7f 0x8400000001f11fff

def z762 : W := mkw 0x10f7fc0003edd800 0x7cfffcf803fffc00

def z763 : W := mkw 0x1cfdebd6ab0ed1a0 0x7bfffffffe0ee1c0

def z764 : W := mkw 0x0cee03feabda03b0 0x7ffe7ffffffe03f8

def z765 : W := mkw 0x04e602a803da03b0 0x6efe038003fe03f8

def z766 : W := mkw 0x8002142854f10e1b 0xfdfe7cf8ffff1e3f

def z767 : W := mkw 0x04ef43fc83da93b0 0x7fffc3ffc3fffff8

def z768 : W := mkw 0x0cee03fc8bda03b0 0x6efe03f8cffe03f8

def z769 : W := mkw 0x91ef4d6333dabac5 0x8b464f6731801fc7

def z770 : W := mkw 0x083cabd6a8000000 0x7b7e7ffffc000000

def z771 : W := mkw 0x00c002814300256e 0xdfc1c387c381ffff

def z772 : W := mkw 0x042e017800da0290 0x6efe03f803fe03f8

def z773 : W := mkw 0x10f5f800032dd000 0x74f9f00003fffc00

def z774 : W := mkw 0x1419fff80037dbb0 0x1a01fff80001fff8

def z775 : W := mkw 0x8602142957fbbfff 0x8400000003ffffff

def z776 : W := mkw 0x0010b0000325d000 0x74b9b00003fffc00

def z777 : W := mkw 0x8402142854fb0e9b 0xfd467cf8fdff1e3f

def z778 : W := mkw 0x853eb57a34ff4a91 0x203e3c783c7e0000

def z779 : W := mkw 0x14f7fe9803edd930 0x7effff9803fffff8

def z780 : W := mkw 0x04ee03f803da03b0 0x7eff83f803ffe3f8

def z781 : W := mkw 0x02c14285c300b56e 0x86c1c387c381ffff

def z782 : W := mkw 0x00e7540003e99800 0x74fffc0003fffc00

def z783 : W := mkw 0x00f7f00003edd000 0x74fff00003fffc00

def z784 : W := mkw 0x0ac14a85cb00b56e 0xdfc1cf87cf81ffff

def z785 : W := mkw 0x953ebd7a30ff4a91 0x203e3c78307e0000

def z786 : W := mkw 0x10f7fc0003edd800 0x74fffc98cffffc00

def z787 : W := mkw 0x18f7fe948bedd800 0x7dfffcf8fffffc00

def z788 : W := mkw 0x83d9f3e6f337d7ab 0x207870e0f1fe1c38

def z789 : W := mkw 0x0819e946a8000000 0x7bfffffffc000000

def z790 : W := mkw 0x90f5e828571cd61b 0x89b980f8fe0ee23f

def z791 : W := mkw 0x02e54a85c300b56e 0xdfc7cf87c381ffff

def z792 : W := mkw 0x04ee03f803da03b0 0x7ffe43f8c3fe03f8

def z793 : W := mkw 0x10f7fc0003edd800 0x75fffc00fffffc00

def z794 : W := mkw 0x02c14285c300b56e 0xdf8183070381ffff

def z795 : W := mkw 0x9102142957fffedf 0x8400000003ffffff

def z796 : W := mkw 0x10f7fc0003edd800 0x30bffc00027ffc00

def z797 : W := mkw 0x1236be85c0ed6d6e 0xab3e3f87c07e03ff

def z798 : W := mkw 0x00c142810300b164 0xdfc1c3870381ffff

def z799 : W := mkw 0x8002142854f54e1b 0xfd467cf8fffffe3f

def z800 : W := mkw 0x12e54a85c308b56e 0xdfc1c387c381ffff

def z801 : W := mkw 0x10f7fe8483edd800 0x7ffffffffffffc00

def z802 : W := mkw 0x04ec03f8001203b0 0x6efe03f8027e03f8

def z803 : W := mkw 0x10f7fc0003edd800 0x24bfbc0003fffc00

def z804 : W := mkw 0x1ae74e94cbc89d2a 0x00464c98cd801c38

def z805 : W := mkw 0x8002142854f10e1b 0xb1467cf8fdf11c3f

def z806 : W := mkw 0x80081161103322c5 0xffb9b367327fe3c7

def z807 : W := mkw 0x0a3ca9536b00b56e 0xa43e3c783f81ffff

def z808 : W := mkw 0x06e7469cc7c89d3a 0x00464c98cd801c38

def z809 : W := mkw 0x00fca3d220000000 0x7bfffffffc000000

def z810 : W := mkw 0x02000285c300b56e 0xdf818387c381ffff

def z811 : W := mkw 0x860803fdd41227ff 0x8b0003fffc0003ff

def z812 : W := mkw 0x08d1ea86a8000000 0x7bc7fffffc000000

def z813 : W := mkw 0x04ee03f803da03b0 0x26be037803fe03f8

def z814 : W := mkw 0x10f7fc0223edd800 0x75fffc0733fffc00

def z815 : W := mkw 0x10f7fe8003edd920 0x74fffc8003fffc38

def z816 : W := mkw 0x040a016803da03b0 0x06b8030003fe03f8

def z817 : W := mkw 0x00e602a803d80330 0x6efe03f803fe03f8

def z818 : W := mkw 0x0cef43feabda03b0 0x7fffc3fffffe03f8

def z819 : W := mkw 0x0118b143202760c4 0xffb9b307027fe3c7

def z820 : W := mkw 0x1013fc0000e5d800 0x74fffc0003fffc00

def z821 : W := mkw 0x8311f407f425fc4f 0x9101fc07fc01fc07

def z822 : W := mkw 0x10f7fe9003edd800 0x74fffc9803fffc00

def z823 : W := mkw 0x04ef4bf803da03b0 0x6efe4ff803fe03f8

def z824 : W := mkw 0x04e6002803da03b0 0x6cfe00f803fe03f8

def z825 : W := mkw 0x82c356ad97f1bb75 0x2287bf7f3e70e1c0

def z826 : W := mkw 0x08fdebd6ab009120 0x7fffffffff81fff8

def z827 : W := mkw 0x8002142854f10e1b 0xfdc7fcf8fff1fe3f

def z828 : W := mkw 0x08fde956a8000000 0x71fffc7ffc000000

def z829 : W := mkw 0x9111fc037425fc4f 0x9101fc07fc01fc07

def z830 : W := mkw 0x1036bc0003edd800 0x747e7c0003fffc00

def z831 : W := mkw 0x10f7fc0803edd810 0x74fffc9803fffc38

def z832 : W := mkw 0x08fdebd6a8000120 0x7bfffffffc0003f8

def z833 : W := mkw 0x083de956a8000000 0x7bbfff7ffc000000

def z834 : W := mkw 0x04c943f8031293b0 0x5ec1c3f80381fff8

def z835 : W := mkw 0x10f7fe8483edd800 0x76ffff0703fffc00

def z836 : W := mkw 0x8118b163303762c5 0xffffb3ff327fe3c7

def z837 : W := mkw 0x04ee017803da03b0 0x64fe007803fe03f8

def z838 : W := mkw 0x18f7fc100bedd800 0x74fffc180ffffc00

def z839 : W := mkw 0x1012b40003edd800 0x2438300003fffc00

def z840 : W := mkw 0x00f7fc0000e54800 0x74fffc0003fffc00

def z841 : W := mkw 0x08fdebd6ab009000 0x7bfffffffd801c00

def z842 : W := mkw 0x08c943d6a8000000 0x7bc7fffffc000000

def z843 : W := mkw 0x04ee03f803da03b0 0x6efe3ff83ffe03f8

def z844 : W := mkw 0x0000000000000000 0x7bc7fffffc000000

def z845 : W := mkw 0x04ee016803da03b0 0x6efe036003fe03f8

def z846 : W := mkw 0x8110b0037425644f 0x9101b007fc01e007

def z847 : W := mkw 0x10f7fc0807edd810 0x74fffc180ffffc00

def z848 : W := mkw 0x0cfdebd6ab0a01a0 0x7fffffffff8e03f8

def z849 : W := mkw 0x8002142854f10e1b 0xffc67ff8fff11fff

def z850 : W := mkw 0x8118b163303762c5 0x97b9b307327fe3c7

def z851 : W := mkw 0x08fdebd6ab080000 0x7bfffffffe0e0000

def z852 : W := mkw 0x00c14285c000244e 0xdfc1c387c381ffff

def z853 : W := mkw 0x890803fffc1226df 0x8b0003fffc0003ff

def z854 : W := mkw 0x0012b40000e54800 0x74b9b00003fffc00

def z855 : W := mkw 0x02014285c000b56e 0xdf41c387c181ffff

def z856 : W := mkw 0x8102142854f74e9b 0xfd467cf8fdff1e3f

def z857 : W := mkw 0x0426002803da03b0 0x243e000003fe03f8

def z858 : W := mkw 0x04e6002803da03b0 0x04b8000003fe03f8

def z859 : W := mkw 0x10f7fc0003edd800 0x20fffc0003fefc00

def z860 : W := mkw 0x8118b163303762c5 0xffb9ff67fe7fe3c7

def z861 : W := mkw 0x10e7540003edd800 0x74ffc00003fffc00

def z862 : W := mkw 0x8918b173383762c5 0xffb9b37f3e7fe3c7

def z863 : W := mkw 0x8002042854d00e1b 0xf9467cf8fd801e3f

def z864 : W := mkw 0x02c14285c300b56e 0xffc7c3ffc381ffff

def z865 : W := mkw 0x8118b56330376ac5 0xffb9ff67327fffc7

def z866 : W := mkw 0x8118b163303762c5 0xf6b9b307027fe3c7

def z867 : W := mkw 0x02e60285c3c8256e 0xeffe0387c3fe03ff

def z868 : W := mkw 0x000a016800d20290 0x6eb8036003fe03f8

def z869 : W := mkw 0x04ee07f807da0bb0 0x6efe0ff80ffe03f8

def z870 : W := mkw 0x0ee74a9ccbc8953a 0x00464c98cd801c38

def z871 : W := mkw 0x8118a163301662c5 0xefb98367327ee3c7

def z872 : W := mkw 0x8002140854e10c1b 0xf9467cf8fd811c3f

def z873 : W := mkw 0x10f7fc0003edd800 0x7dfffc80c3fffc00

def z874 : W := mkw 0x08f5e806a8000000 0x79fffcfffc000000

def z875 : W := mkw 0x8002142854f10e1b 0xffc7fffffdf11e3f

def z876 : W := mkw 0x1013fc0003edd800 0x74b9fc0003fffc00

def z877 : W := mkw 0x0010a00220000000 0x7947fcfffc000000

def z878 : W := mkw 0x00ee03d003c80120 0x6efe03f803fe03f8

def z879 : W := mkw 0x0cef4bfc8bda03b0 0x7fffcfffcffe03f8

def z880 : W := mkw 0x180a17d6abedd800 0x0f0003fffffffc00

def z881 : W := mkw 0x08fdebd6a8000000 0x7ffffffffe7e0000

def z882 : W := mkw 0x04ee03fa23da03b0 0x6ffe03ff33fe03f8

def z883 : W := mkw 0x042e017803da03b0 0x6ebe037803fe03f8

def z884 : W := mkw 0x10f7fc0003edd800 0x7dfffc6033fffc00

def z885 : W := mkw 0x04ee03f803da03b0 0x6eb8036003fe03f8

def z886 : W := mkw 0x8b0803f7f81227ef 0x8b0003fffc0003ff

def z887 : W := mkw 0x02c14285c300b56e 0xcec183870381ffff

def z888 : W := mkw 0x04ef43fc83da03b0 0x6eff83ff03fe03f8

def z889 : W := mkw 0x04ee03f803da03b0 0x2a7e03f801fe03f8

def z890 : W := mkw 0x14ee07f803da9bb0 0x6efe03f803fe1ff8

def z891 : W := mkw 0x04ee03d803ca01b0 0x66fe039803fe01f8

def z892 : W := mkw 0x04ee03f803da03b0 0x0eb803f803fe03f8

def z893 : W := mkw 0x04ee03f803da03b0 0x66fe030003fe03f8

def z894 : W := mkw 0x8202142954f1be5f 0x8400000001f1fe3f

def z895 : W := mkw 0x0002040844c00c1a 0xfd467cf8fd811e3f

def z896 : W := mkw 0x0008016000120280 0x6ef803e003fe03f8

def z897 : W := mkw 0x04ee03f803da03b0 0x7efe7ff803fe03f8

def z898 : W := mkw 0x0811e806a8000000 0x3107fc7ffc000000

def z899 : W := mkw 0x8118b163303762c5 0xabb9b367327ee3c7

def z900 : W := mkw 0x04ee03f803da03b0 0x06fe039803fe03f8

def z901 : W := mkw 0x04ee07f803da0bb0 0x6efe4ff803fe1ff8

def z902 : W := mkw 0x8002142854f10e1b 0xa9467cf8fdf01e3f

def z903 : W := mkw 0x04ee03f800da03b0 0x6afe03f8007e03f8

def z904 : W := mkw 0x0118a163201662c4 0xffb98367027fe3c7

def z905 : W := mkw 0x08fdebd6ab009000 0x7bfffffffe00e000

def z906 : W := mkw 0x00d9e3c6a0000000 0x7bfffffffc000000

def z907 : W := mkw 0x8302142957f7ffff 0x8400000003ffffff

def z908 : W := mkw 0x10f7fc0003edd800 0x64ff800003fffc00

def z909 : W := mkw 0x8118b143302760c5 0xf7b9b307327fe1c7

def z910 : W := mkw 0x10f7fc0003edd920 0x74fffc0003fffff8

def z911 : W := mkw 0x04c803f8031203b0 0x6ef803f803fe03f8

def z912 : W := mkw 0x06ef43fc83da93b0 0x6efe03f803fe03f8

def z913 : W := mkw 0x04ca03e803da03b0 0x6ef803e003fe03f8

def z914 : W := mkw 0x040a016803da03b0 0x6efe03f803fe03f8

def z915 : W := mkw 0x1037fc0003edd800 0x343ffc0003fffc00

def z916 : W := mkw 0x02014005c000b44e 0xdfc1c387c381ffff

def z917 : W := mkw 0x8118b16b303762d5 0xffb9b3ff327fe3ff

def z918 : W := mkw 0x8000140054210c0b 0xfd467cf8fd811e3f

def z919 : W := mkw 0x0002140040e10c0a 0xfd467cf8fdf11e3f

def z920 : W := mkw 0x10f6b40003edd800 0x74ffb00003fffc00

def z921 : W := mkw 0x913ebd6a34ff4a91 0x203e3c783c7e0000

def z922 : W := mkw 0x00fde94220000000 0x7bfffffffc000000

def z923 : W := mkw 0x0008016800120290 0x6eb803f8027e03f8

def z924 : W := mkw 0x0018b14320256044 0xffb9b367327fe3c7

def z925 : W := mkw 0x0bfdebd7ab06f1e4 0x02b98307020ee1c0

def z926 : W := mkw 0x83080163701227ef 0x8b000367300003ff

def z927 : W := mkw 0x02e54285c308b56e 0xdff9c387c38fffff

def z928 : W := mkw 0x10e6140003edd800 0x04b8000003fffc00

def z929 : W := mkw 0x10f7fc0003edd800 0x247e7c0003fffc00

def z930 : W := mkw 0x1010b4000025d800 0x74b9b000027ffc00

def z931 : W := mkw 0x0018b161003762c4 0xffb9b367027fe3c7

def z932 : W := mkw 0x08fdebd6a8000000 0x33bfff7ffc000000

def z933 : W := mkw 0x8310b0037025f44f 0x9101b0073001fc07

def z934 : W := mkw 0x0000000100002044 0xffb98307027fe3c7

def z935 : W := mkw 0x00080160031203a0 0x6eb8036003fe03f8

def z936 : W := mkw 0x9311fc07f025fc4f 0x9101fc07f001fc07

def z937 : W := mkw 0x04ee03f803da03b0 0x22fe03f803fe01f8

def z938 : W := mkw 0x12f7fe8483edd920 0x74fffc0003fffc00

def z939 : W := mkw 0x0cfdebd6ab080120 0x7bfffffffc000000

def z940 : W := mkw 0x0818a3d6a8000000 0x7bfffffffc000000

def z941 : W := mkw 0x04ee03f803da03b0 0xfffe03f803ff03ff

def z942 : W := mkw 0x0cef4bfc8bda03b0 0x6efe03f803fe03f8

def z943 : W := mkw 0x10f7fc0000edd800 0x70fffc00007ffc00

def z944 : W := mkw 0x083de956a8000000 0x797ffcfffc000000

def z945 : W := mkw 0x04ef43f803da93b0 0x6efe43f803fe1ff8

def z946 : W := mkw 0x1cef4ffc8bda9bb0 0x6efe4ff8cffe1ff8

def z947 : W := mkw 0x8118b163303762c5 0xffb9b3fffe7fe3c7

def z948 : W := mkw 0x02c140014300b56e 0xdfc1c3070381ffff

def z949 : W := mkw 0x893ebd7a3cf74a91 0x203e3c783c7e0000

def z950 : W := mkw 0x04ec03f0031a03a0 0x6ef803e003fe03f8

def z951 : W := mkw 0x81080163701226cf 0x8b0003e7f00003ff

def z952 : W := mkw 0x10f7fe8003edd800 0x7effff8003fffc00

def z953 : W := mkw 0x04ee03f803da03b0 0x7fff83ff03fe03f8

def z954 : W := mkw 0x18f7fe86abedd800 0x7fffff87fffffc00

def z955 : W := mkw 0x1afdebd7ab0cf164 0x02b98307020ee1c0

def z956 : W := mkw 0x18f7fe948bedd800 0x7fffff9fcffffc00

def z957 : W := mkw 0x08fdebd6a8000000 0x1b47fffffc000000

def z958 : W := mkw 0x14ef4bf803da93b0 0x6efe03f803fe03f8

def z959 : W := mkw 0x020000014300b56e 0x868183070381ffff

def z960 : W := mkw 0x020000014300b56e 0xdfc1c387c381ffff

def z961 : W := mkw 0x8118b56334376ac5 0xffb9bf673e7fe3c7

def z962 : W := mkw 0x81080163741226cf 0x8b000367fc0003c7

def z963 : W := mkw 0x040a03f803da03b0 0x6eb803f803fe03f8

def z964 : W := mkw 0x10f7fe8483edd800 0x74fffc80c3fffc00

def z965 : W := mkw 0x8118b163303762c5 0x8fb98367327fe3c7

def z966 : W := mkw 0x8110b40374256c4f 0x9101b0073001fc07

def z967 : W := mkw 0x08fdebd6ab000000 0x7fffffffff800000

def z968 : W := mkw 0x91f7fc0233edd801 0x74fffc0033fffc00

def z969 : W := mkw 0x00e6000003c89000 0x64fe000003fffc00

def z970 : W := mkw 0x10f7fc0003edd800 0x54f9c00003fffc00

def z971 : W := mkw 0x10f7fc0003edd800 0x14b9fc0003fffc00

def z972 : W := mkw 0x10f5fc00032dd800 0x74b9fc00027ffc00

def z973 : W := mkw 0x9002142854fd4e1b 0xfd467cf8fdff1e3f

def z974 : W := mkw 0x042e03f800da03b0 0x6e7e03f801fe03f8

def z975 : W := mkw 0x1002140003edd800 0x64b8000003fffc00

def z976 : W := mkw 0x02014285c300b56e 0x9f01c387c381ffff

def z977 : W := mkw 0x18f7fc048bedd800 0x74fffc00cffffc00

def z978 : W := mkw 0x0cee03feabda03b0 0x6efe03ff03fe03f8

def z979 : W := mkw 0x04ee03f803da03b0 0x4ef8038003fe03f8

def z980 : W := mkw 0x8010b02110356245 0xffb9b367327fe3c7

def z981 : W := mkw 0x04ee03d003ca01a0 0x6efe038003fe03f8

def z982 : W := mkw 0x8118b163303762c5 0xeeb98367027fe3c7

def z983 : W := mkw 0x04ee03f803da93b0 0x6efe03f803fffff8

def z984 : W := mkw 0x1a11fc07e825fc4e 0x9101fc07fc01fc07

def z985 : W := mkw 0x0002002840d0061a 0xfd467cf8fdf11e3f

def z986 : W := mkw 0x81080163301222c5 0xffb98367327fe3c7

def z987 : W := mkw 0x042e017800da03b0 0x203e0078007e03f8

def z988 : W := mkw 0x85ee03fa33da03b1 0x6efe03f833fe03f8

def z989 : W := mkw 0x0819ebd6a8000000 0x7b47fffffc000000

def z990 : W := mkw 0x8911fc07fc256c4f 0x9101fc07fc01fc07

def z991 : W := mkw 0x84ee03f813da03b1 0xeffe03f833fe03ff

def z992 : W := mkw 0x18f7fc06abedd800 0x74fffc0703fffc00

def z993 : W := mkw 0x8118b163303762c5 0xfff9f3e7f27fe3c7

def z994 : W := mkw 0x000803e0001203a0 0x6eb803e0027e03f8

def z995 : W := mkw 0x040a016803da03b0 0x2438006003fe03f8

def z996 : W := mkw 0x04ec03f8031a03b0 0x6eb803f8027e03f8

def z997 : W := mkw 0x0018a163201222c4 0xffb9b367327fe3c7

def z998 : W := mkw 0x08fdebd6a8000000 0x2bbfbffffc000000

def z999 : W := mkw 0x02c14285c300b56e 0xdfc1ff87ff81ffff

def z1000 : W := mkw 0x04ef43f803da93b0 0x6eff83f803fee3f8

def z1001 : W := mkw 0x14ef4ff803da9bb0 0x7effcff803fffff8

def z1002 : W := mkw 0x850803fb741227ff 0x8b0003fffc0003ff

def z1003 : W := mkw 0x02c14285c300b56e 0x9781c307c381ffff

def z1004 : W := mkw 0x0ae54a95cb00b56e 0xdfc1c387c381ffff

def z1005 : W := mkw 0x1036bc0003edd800 0x0438000003fffc00

def z1006 : W := mkw 0x18f7fe948bedd800 0x74fffc0003fffc00

def z1007 : W := mkw 0x1026140003edd800 0x243e000003fffc00

def z1008 : W := mkw 0x1036bc0003edd800 0x74bfbc0003fffc00

def z1009 : W := mkw 0x1cf7fe9c8bedd930 0x74fffc98cffffc38

def z1010 : W := mkw 0x08000006a8000000 0x79467cfffc000000

def z1011 : W := mkw 0x10e74c0003c89800 0x74ffcc0003fffc00

def z1012 : W := mkw 0x0e0803ffe81227fe 0x8b0003fffc0003ff

def z1013 : W := mkw 0x8110b0037025644f 0x9101f007f001fc07

def z1014 : W := mkw 0x10f5fc000025d800 0x74fffc00027ffc00

def z1015 : W := mkw 0x8002142854f10e1b 0xa4467cf8fdf11e3f

def z1016 : W := mkw 0x8002142954f12e5f 0x8400000003f1ffff

def z1017 : W := mkw 0x04ee03f803da03b0 0x7ffe33f833fe03f8

def z1018 : W := mkw 0x81081161103762c5 0xffb98367027fe3c7

def z1019 : W := mkw 0x08fdebd6a8009000 0x7bfffffffc01fc00

def z1020 : W := mkw 0x04ee03f803da03b0 0x6efe4ff8cffe03f8

def z1021 : W := mkw 0x10d1fe800325d920 0x5ec1ff800381fff8

def z1022 : W := mkw 0x00ee016803da0290 0x6efe03f803fe03f8

def z1023 : W := mkw 0x08fcabd6a8000000 0x6bfe3ffffc000000

def z1024 : W := mkw 0x0001400480000000 0x7947fcfffc000000

def z1025 : W := mkw 0x08fdebd6ab000120 0x7bfffffffe0001c0

def z1026 : W := mkw 0x08fdebd6a8000000 0x2b7e7ffffc000000

def z1027 : W := mkw 0x08fdebd6a8020080 0x7bfffffffe0e01c0

def z1028 : W := mkw 0x8108016b741226df 0x8b000367300003ff

def z1029 : W := mkw 0x0ae54a95cb00b56e 0xffc7ffffff81ffff

def z1030 : W := mkw 0x8118b163303762c5 0xb3b9b367327fe1c7

def z1031 : W := mkw 0x8b11f807f825f44f 0x9101fc07fc01fc07

def z1032 : W := mkw 0x00f5ea8480000000 0x7bfffffffc000000

def z1033 : W := mkw 0x18fdebd6a80c4000 0x7bfffffffc0e0000

def z1034 : W := mkw 0x04ee03fc83da03b0 0x6ffe03ffc3fe03f8

def z1035 : W := mkw 0x08fdebd6a8000000 0xfffffffffc010207

def z1036 : W := mkw 0x1012b40003edd800 0x04b9800003fffc00

def z1037 : W := mkw 0x08fdebd6a8000000 0x317ffcfffc000000

def z1038 : W := mkw 0x18f7fc06abedd800 0x7dfffcfffffffc00

def z1039 : W := mkw 0x9211fc05d425fc4f 0x9101fc07fc01fc07

def z1040 : W := mkw 0x0cfdebd6a80a0080 0x7bfffffffc0e0000

def z1041 : W := mkw 0x10f7fc0003edd800 0x7fffff0703fffc00

def z1042 : W := mkw 0x10f7fc0003edd800 0x74b9b00003fffc00

def z1043 : W := mkw 0x1012b40003edd800 0x74fffc0003fffc00

def z1044 : W := mkw 0x10f7fc0003edd800 0xfdfffc0003fffe07

def z1045 : W := mkw 0x8118b163303762c5 0xfff9b3e733ffe3ff

def z1046 : W := mkw 0x10f7fc0483edd800 0x75fffc07c3fffc00

def z1047 : W := mkw 0x02014005c300b56e 0xdf81c307c381ffff

def z1048 : W := mkw 0x1037fc0000edd800 0x747ffc0001fffc00

def z1049 : W := mkw 0x8110b00330256045 0xffb9b307327fe3c7

def z1050 : W := mkw 0x18fdebd6ab0cd000 0x7fffffffff8ffc00

def z1051 : W := mkw 0x10e75c0003edd800 0x64fe4c0003fffc00

def z1052 : W := mkw 0x8102142954f56e5f 0x8400000001f1fe3f

def z1053 : W := mkw 0x02e54285c300b56e 0xffffc387c381ffff

def z1054 : W := mkw 0x1037fc0000edd800 0x74bffc00027ffc00

def z1055 : W := mkw 0x8918b963383762c5 0xffb9bf673e7fe3c7

def z1056 : W := mkw 0x00ed43d480000000 0x7bfffffffc000000

def z1057 : W := mkw 0x0010b00000254000 0x74f9f00003fffc00

def z1058 : W := mkw 0x04ee03f803da03b0 0x2abe03f8027e03f8

def z1059 : W := mkw 0x08f5ea96a8000000 0x7947fcfffc000000

def z1060 : W := mkw 0x040a03f800d203b0 0x6efe03f803fe03f8

def z1061 : W := mkw 0x8102142954f32edf 0x8400000001f11fff

def z1062 : W := mkw 0x9118bd6330376ac5 0xffb9bf67327fe3c7

def z1063 : W := mkw 0x00f6b40003ed4800 0x74fffc0003fffc00

def z1064 : W := mkw 0x10e6140003edd800 0x74fe7c0003fffc00

def z1065 : W := mkw 0x10f7ec0003ccd800 0x64ffcc0003fefc00

def z1066 : W := mkw 0x0010b40000254800 0x74b9fc00027ffc00

def z1067 : W := mkw 0x90f7fc0013edd801 0xf5fffc0033fffc07

def z1068 : W := mkw 0x00e6000003c80120 0x64fe000003fe03f8

def z1069 : W := mkw 0x08fdebd6a8000000 0x7ffffffffe0003c0

def z1070 : W := mkw 0x9202142957fdff7f 0x8400000003ffffff

def z1071 : W := mkw 0x90f7fc0017edd801 0x74fffc003ffffc00

def z1072 : W := mkw 0x8518b17b303762d5 0xffb9b37f327fe3c7

def z1073 : W := mkw 0x1036bc0000ed4800 0x74fffc0003fffc00

def z1074 : W := mkw 0x08ed4bd6a8000000 0x7b467ffffc000000

def z1075 : W := mkw 0x18fdebd6ab089000 0x7bfffffffc000000

def z1076 : W := mkw 0x00f7e80003c89000 0x74fffc0003fffc00

def z1077 : W := mkw 0x04ee03f803da03b0 0x247e00f803fe03f8

def z1078 : W := mkw 0x08fdebd6a8000000 0x7ffffffffd811c00

def z1079 : W := mkw 0x800010205031060b 0xfd467cf8fdf11e3f

def z1080 : W := mkw 0x1211fc014025fc4e 0x9001fc000001fc07

def z1081 : W := mkw 0x00c0028003000120 0x6ef8038003fe03f8

def z1082 : W := mkw 0x0402002803da03b0 0x64b8000003fe03f8

def z1083 : W := mkw 0x8310b007f025644f 0x9101b007f001e007

def z1084 : W := mkw 0x02e74284c3c8952a 0x00464080c1801c38

def z1085 : W := mkw 0x00ee03f800d20290 0x6efe03f803fe03f8

def z1086 : W := mkw 0x02000285c000256e 0xdfc1c387c381ffff

def z1087 : W := mkw 0x0211f005c025f44e 0x9101f007c001fc07

def z1088 : W := mkw 0x0011f0000025d000 0x74b9f000027ffc00

def z1089 : W := mkw 0x0cee03fa2bda03b0 0x6efe03f83ffe03f8

def z1090 : W := mkw 0x10d3f40003edd800 0x74f9f00003fffc00

def z1091 : W := mkw 0x8118b163303762c5 0xdfb98307027fe3c7

def z1092 : W := mkw 0x00d3f40003e5d800 0x74fffc0003fffc00

def z1093 : W := mkw 0x84ee03f817da03b1 0x6efe03f83ffe03f8

def z1094 : W := mkw 0x09fdebd6a8064080 0x7bfffffffc0e0000

def z1095 : W := mkw 0x08e54a9488000000 0x7bc7fffffc000000

def z1096 : W := mkw 0x1036bc0000edd800 0x203e3c00007ffc00

def z1097 : W := mkw 0x14f7fe9003edd920 0x74fffc0003fffc00

def z1098 : W := mkw 0x10f7fc0003edd800 0x307ffc0001fffc00

def z1099 : W := mkw 0x00ee03e003da03a0 0x6efe03e003fe03f8

def z1100 : W := mkw 0x020803e5c01227ee 0x8b0003e7c00003ff

def z1101 : W := mkw 0x10f7fc0003edd800 0x74fffc783ffffc00

def z1102 : W := mkw 0x8118b16b343762d5 0xffb9b37f3e7fe3c7

def z1103 : W := mkw 0x1011fc000025d800 0x3039fc00007ffc00

def z1104 : W := mkw 0x02c002814300b56e 0xdfc183870381ffff

def z1105 : W := mkw 0x14f7fc0803edd930 0x74fffc0003fffc38

def z1106 : W := mkw 0x870803fff01227ff 0x8b0003fff00003ff

def z1107 : W := mkw 0x8118b163303762c5 0xffbfbf7f3e7fe3c7

def z1108 : W := mkw 0x0afdebd6ab009120 0x7bfffffffc000000

def z1109 : W := mkw 0x8002142854f30e9b 0xfd467cf8ffff1fff

def z1110 : W := mkw 0x8502142957ff6fff 0x8400000003ffffff

def z1111 : W := mkw 0x0008014220000000 0x7b467ffffc000000

def z1112 : W := mkw 0x02c14285c300b56e 0xfff9c387c3ffffff

def z1113 : W := mkw 0x02c14285c300b56e 0xffc7ff87c381ffff

def z1114 : W := mkw 0x14f7fc1803edd810 0x74fffc1803fffc00

def z1115 : W := mkw 0x083ca95228000000 0x7bfffffffc000000

def z1116 : W := mkw 0x10f7fe8003edd920 0x76ffff0003fffdc0

def z1117 : W := mkw 0x0000028480000000 0x7b467ffffc000000

def z1118 : W := mkw 0x060803f9401227fe 0x8a0003f8000003ff

def z1119 : W := mkw 0x000000014000244e 0xdf8183070381ffff

def z1120 : W := mkw 0x08fdebd6a8044000 0x7bfffffffe0ee000

def z1121 : W := mkw 0x18fdebd6a804d000 0x7bfffffffc00e000

def z1122 : W := mkw 0x00c140014300b44e 0xdfc1c387c381ffff

def z1123 : W := mkw 0x00ca03e803d203b0 0x6efe03f803fe03f8

def z1124 : W := mkw 0x083ca956a8000000 0x213e3c7ffc000000

def z1125 : W := mkw 0x04080168001203b0 0x6eb80360027e03f8

def z1126 : W := mkw 0x0ac14295cb00b56e 0xdfc1c39fcf81ffff

def z1127 : W := mkw 0x02c14285c300b56e 0xffc1f3e7f381ffff

def z1128 : W := mkw 0x83080167f01226cf 0x8b000367f00003c7

def z1129 : W := mkw 0x18f7fe96abedd800 0x75fffc9ffffffc00

def z1130 : W := mkw 0x10f6bc0003edd800 0x64fe3c0003fffc00

def z1131 : W := mkw 0x0cfdebd6a80201a0 0x7bfffffffc0001c0

def z1132 : W := mkw 0x0cef4bfeabda03b0 0x6ffe4ffffffe03f8

def z1133 : W := mkw 0x08fdebd6ab000120 0x7bfffffffd800038

def z1134 : W := mkw 0x02c14285c300b56e 0x8f818387c381ffff

def z1135 : W := mkw 0x08fdebd6a8000000 0x22fffffffc000000

def z1136 : W := mkw 0x830803eff41227ff 0x8b0003fffc0003ff

def z1137 : W := mkw 0x10f7fc0003edd800 0x04ffcc0003fffc00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[],[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z8]),(0,[z0,z1,z4,z9,z7,z5,z6])],[(0,[z0,z1,z4,z10,z7,z5,z6]),(0,[z11,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z12,z5,z6]),(0,[z0,z1,z4,z7,z5,z13,z6])],[(0,[z14,z0,z1,z15,z7,z5,z6]),(0,[z16,z0,z1,z4,z7,z5,z6]),(0,[z17,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z7,z18,z5]),(0,[z0,z1,z4,z7,z5,z6,z19]),(0,[z0,z20,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z21,z5,z6]),(0,[z0,z1,z22,z7,z23,z5,z6]),(0,[z24,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z25,z5,z6]),(0,[z26,z0,z1,z22,z4,z7,z6]),(0,[z0,z1,z4,z7,z27,z5,z6]),(0,[z28,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z29,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z30]),(0,[z0,z1,z4,z31,z7,z5,z6]),(0,[z0,z1,z4,z32,z5,z33,z6]),(0,[z0,z1,z34,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z35,z5,z6]),(0,[z0,z1,z4,z36,z7,z5,z6])],[(0,[z37,z0,z1,z38,z7,z5,z6]),(0,[z39,z0,z1,z4,z7,z5,z6]),(0,[z40,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z41,z6]),(1,[z0,z4,z9,z7,z5,z6])]],
   [[(0,[z0,z1,z42,z3,z4,z7,z5]),(0,[z43,z0,z20,z1,z4,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z44]),(0,[z0,z1,z45,z4,z7,z5,z6]),(0,[z0,z46,z1,z4,z7,z5,z6])],[(0,[z47,z0,z1,z4,z7,z5,z6])],[(0,[z0,z48,z1,z4,z7,z5,z6]),(0,[z0,z49,z1,z4,z7,z5,z6]),(1,[z0,z4,z29,z7,z5,z6])],[(0,[z50,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z51,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z52,z6]),(0,[z0,z1,z53,z4,z7,z5,z6]),(0,[z54,z0,z1,z4,z7,z5,z6]),(0,[z0,z55,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z56,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z57]),(0,[z0,z1,z4,z7,z5,z58,z6]),(0,[z59,z0,z1,z4,z7,z5,z6])],[(0,[z14,z0,z1,z4,z7,z5,z6]),(0,[z0,z60,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z61]),(0,[z62,z1,z4,z7,z5,z6,z30]),(0,[z1,z4,z7,z63,z5,z6,z30]),(0,[z0,z1,z64,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z65]),(0,[z37,z0,z1,z66,z7,z5,z6]),(0,[z0,z1,z67,z4,z7,z5,z6]),(0,[z68,z0,z1,z4,z7,z5,z6]),(1,[z11,z0,z4,z7,z5,z69]),(0,[z70,z0,z1,z4,z7,z5,z6]),(0,[z0,z71,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z72,z7,z5,z6])],[(0,[z0,z1,z4,z7,z18,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z73]),(0,[z0,z1,z4,z7,z5,z6,z74]),(0,[z0,z1,z4,z7,z5,z75,z6]),(1,[z76,z0,z1,z7,z5,z77]),(0,[z0,z1,z4,z7,z78,z5,z6]),(1,[z1,z4,z7,z5,z6,z79])],[(0,[z1,z4,z7,z63,z5,z41,z6]),(0,[z37,z0,z1,z4,z7,z5,z80]),(0,[z0,z1,z81,z7,z5,z82,z6]),(0,[z83,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z6,z84]),(0,[z0,z85,z1,z4,z86,z5,z6]),(0,[z0,z1,z4,z7,z87,z5,z6])],[(0,[z0,z1,z3,z4,z7,z5,z6]),(0,[z0,z1,z88,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z89])],[(0,[z70,z0,z1,z4,z7,z5,z90]),(0,[z0,z1,z91,z4,z7,z5,z6])],[(0,[z0,z92,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z93,z6]),(0,[z0,z1,z4,z7,z5,z94,z6]),(0,[z0,z1,z4,z7,z5,z6,z95])],[(1,[z0,z1,z4,z96,z7,z6]),(0,[z70,z97,z0,z1,z4,z5,z6]),(0,[z98,z99,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z100,z7,z5,z6]),(0,[z11,z99,z0,z1,z4,z7,z5]),(0,[z0,z1,z4,z7,z5,z101,z6]),(0,[z0,z1,z4,z7,z5,z6,z102]),(0,[z103,z0,z1,z4,z7,z5,z6])],[(1,[z0,z104,z4,z7,z5,z6]),(0,[z0,z1,z4,z105,z7,z5,z6]),(0,[z0,z1,z4,z7,z106,z5,z6]),(0,[z107,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z108,z7,z5,z6])],[(1,[z0,z1,z4,z109,z5,z6]),(1,[z110,z1,z4,z7,z63,z6]),(0,[z0,z1,z4,z7,z5,z6,z111]),(1,[z112,z0,z1,z7,z5,z6])],[(0,[z26,z0,z1,z4,z7,z5,z6]),(1,[z113,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z7,z114,z5,z6])]],
   [[(0,[z0,z1,z115,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z116])],[(0,[z98,z62,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z117,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z118])],[(0,[z119,z0,z1,z4,z7,z5,z6]),(0,[z0,z120,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z121,z5,z6]),(0,[z122,z0,z4,z7,z123,z5,z6]),(0,[z124,z0,z1,z7,z125,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z126]),(0,[z0,z1,z22,z4,z7,z5,z6])],[(0,[z122,z127,z0,z4,z7,z5,z6]),(0,[z0,z1,z66,z128,z7,z5,z6]),(0,[z0,z129,z1,z4,z7,z5,z6]),(0,[z0,z1,z130,z4,z7,z5,z6]),(0,[z131,z0,z1,z4,z7,z5,z6])],[(1,[z0,z1,z15,z7,z5,z6]),(0,[z0,z1,z128,z7,z125,z5,z6]),(0,[z0,z132,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z133,z7,z5,z6]),(0,[z0,z134,z66,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z135,z6]),(1,[z0,z1,z7,z136,z5,z6])],[(0,[z0,z1,z4,z7,z137,z5,z6]),(0,[z0,z1,z4,z138,z7,z5,z6]),(0,[z0,z1,z4,z139,z7,z5,z6]),(0,[z0,z140,z1,z4,z7,z141,z6]),(0,[z0,z1,z4,z142,z7,z5,z6]),(0,[z0,z1,z81,z4,z7,z5,z6]),(0,[z0,z1,z143,z4,z7,z5,z6])],[(0,[z70,z99,z0,z1,z4,z7,z5]),(0,[z0,z1,z4,z144,z7,z5,z6]),(0,[z145,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z14,z0,z4,z7,z5,z146,z6]),(0,[z147,z0,z1,z4,z7,z5,z6]),(0,[z0,z4,z7,z141,z5,z146,z6]),(0,[z148,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z1,z4,z7,z5,z6]),(1,[z149,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z7,z150,z5,z6]),(0,[z151,z0,z1,z4,z7,z5,z6]),(0,[z152,z0,z1,z4,z7,z5,z6])],[(0,[z153,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z154,z5,z6]),(0,[z122,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z7,z125,z23,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z155]),(0,[z0,z156,z1,z4,z7,z5,z6])],[(0,[z157,z0,z1,z4,z7,z5,z6]),(0,[z158,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z159,z7,z5,z6]),(0,[z97,z0,z20,z1,z4,z5,z6]),(0,[z0,z160,z1,z4,z7,z5,z6]),(0,[z161,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z162,z7,z6,z163])],[(0,[z164,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z165,z7,z5,z6]),(0,[z166,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z5,z6]),(0,[z0,z1,z4,z7,z167,z5,z6]),(0,[z168,z0,z1,z4,z7,z5,z6]),(0,[z169,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z170,z4,z32,z5,z6]),(1,[z171,z1,z4,z7,z5,z6]),(0,[z172,z0,z1,z4,z7,z5,z6])],[(0,[z0,z173,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z174,z5,z6]),(0,[z0,z1,z4,z7,z175,z5,z6])]],
   [[(0,[z176,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z177,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z178,z6]),(0,[z179,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z180])],[(0,[z0,z1,z181,z4,z7,z5,z6]),(0,[z43,z0,z182,z4,z7,z5,z6]),(0,[z43,z0,z1,z4,z5,z33,z6]),(0,[z122,z97,z0,z1,z4,z5,z6]),(0,[z0,z1,z183,z4,z7,z5,z6]),(0,[z26,z98,z1,z4,z7,z5,z6]),(0,[z0,z184,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z32,z162,z5,z6]),(0,[z37,z0,z1,z7,z5,z6,z185])],[(0,[z186,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z187,z6]),(0,[z188,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z189,z6]),(0,[z190,z0,z1,z4,z7,z5,z6])],[(0,[z43,z0,z120,z4,z7,z5,z6]),(0,[z0,z20,z1,z4,z123,z5,z6]),(0,[z0,z1,z191,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z192,z5,z6]),(0,[z76,z0,z1,z81,z7,z5,z6]),(0,[z0,z1,z4,z193,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z194]),(0,[z0,z195,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z196])],[(0,[z0,z1,z4,z197,z123,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z198]),(0,[z0,z1,z4,z7,z199,z5,z6])],[(0,[z0,z200,z4,z38,z7,z5,z6]),(0,[z70,z0,z1,z4,z7,z5,z33]),(0,[z0,z1,z4,z201,z5,z33,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z6,z202]),(0,[z203,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z18,z197,z5]),(0,[z0,z1,z204,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z205]),(0,[z206,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z207]),(0,[z0,z1,z4,z7,z5,z6,z208]),(0,[z0,z1,z4,z7,z5,z82,z209])],[(0,[z70,z43,z0,z1,z4,z5,z6]),(0,[z26,z0,z1,z4,z7,z63,z6]),(0,[z0,z1,z4,z210,z7,z5,z6]),(0,[z0,z1,z81,z4,z7,z5,z77])],[(0,[z17,z0,z104,z4,z7,z5,z6]),(0,[z0,z1,z4,z211,z7,z5,z6]),(0,[z0,z4,z212,z7,z123,z5,z6]),(0,[z0,z1,z4,z7,z5,z146,z6])],[(0,[z110,z1,z4,z128,z7,z5,z6]),(0,[z0,z1,z4,z213,z7,z5,z6]),(0,[z0,z1,z4,z38,z7,z5,z6]),(0,[z70,z0,z1,z4,z123,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z214]),(0,[z0,z1,z4,z7,z5,z6,z215]),(0,[z0,z1,z4,z7,z5,z6,z216]),(0,[z0,z1,z4,z7,z5,z217,z6])],[(0,[z14,z0,z4,z212,z7,z5,z6]),(0,[z0,z1,z4,z218,z7,z5,z6]),(0,[z219,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z220,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z221,z5,z6]),(0,[z0,z1,z222,z4,z7,z5,z6])]],
   [[(0,[z223,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z224,z7,z5,z6]),(0,[z97,z0,z1,z4,z225,z5,z6]),(0,[z226,z0,z1,z4,z7,z5,z6]),(0,[z227,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z228]),(1,[z0,z1,z4,z5,z6,z19]),(0,[z229,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z170,z4,z125,z5,z6]),(0,[z0,z230,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z231,z5,z6]),(0,[z0,z1,z4,z7,z232,z5,z6])],[(0,[z0,z1,z4,z7,z233,z5,z6]),(0,[z0,z1,z4,z7,z5,z234,z6]),(0,[z0,z235,z1,z4,z7,z5,z6])],[(0,[z0,z1,z236,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z237,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z238]),(0,[z11,z0,z20,z4,z7,z5,z6])],[(0,[z0,z1,z239,z4,z7,z5,z6]),(0,[z0,z1,z240,z4,z7,z5,z6])],[(0,[z0,z1,z241,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z242]),(0,[z37,z110,z0,z1,z4,z7,z6]),(1,[z0,z134,z66,z7,z5,z6]),(0,[z243,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z244]),(0,[z0,z1,z4,z7,z5,z6,z245])],[(0,[z0,z1,z4,z246,z7,z5,z6]),(0,[z0,z1,z170,z128,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z247])]],
   [[(0,[z1,z4,z128,z7,z5,z6,z30]),(0,[z248,z0,z1,z4,z7,z5,z6]),(0,[z249,z0,z4,z38,z7,z5,z6]),(0,[z0,z1,z7,z23,z5,z82,z6])],[(0,[z0,z1,z4,z128,z7,z5,z6]),(0,[z0,z1,z4,z250,z7,z5,z6]),(0,[z251,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z252]),(0,[z0,z1,z4,z7,z5,z253,z6]),(0,[z0,z1,z81,z4,z7,z5,z82])],[(0,[z1,z4,z128,z7,z5,z41,z6]),(0,[z254,z0,z1,z4,z7,z5,z6]),(0,[z145,z0,z1,z4,z7,z5,z82]),(0,[z0,z1,z4,z5,z255,z6,z209])],[(1,[z0,z1,z4,z256,z5,z6]),(0,[z43,z0,z1,z257,z7,z5,z6]),(0,[z258,z0,z1,z4,z7,z5,z6]),(0,[z259,z0,z1,z4,z7,z5,z6])],[(0,[z97,z0,z1,z4,z5,z33,z6]),(0,[z0,z1,z4,z7,z5,z6,z260]),(0,[z0,z1,z4,z261,z7,z5,z6]),(0,[z37,z0,z1,z4,z262,z5,z6]),(0,[z263,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z5,z33,z6,z90]),(0,[z264,z0,z1,z4,z7,z265,z6])],[(0,[z0,z1,z4,z266,z7,z5,z6]),(0,[z0,z1,z4,z267,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z268,z6]),(0,[z0,z1,z4,z269,z7,z5,z6]),(0,[z0,z270,z1,z4,z7,z5,z6])],[(0,[z0,z271,z1,z4,z7,z5,z6]),(0,[z272,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z273]),(0,[z0,z1,z4,z32,z5,z6,z163]),(0,[z0,z1,z4,z7,z5,z6,z274]),(0,[z0,z1,z4,z7,z5,z275,z6]),(0,[z276,z70,z0,z1,z4,z5,z6])],[(0,[z0,z1,z4,z7,z5,z277,z6]),(0,[z278,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z279,z4,z7,z5,z6])],[],[(0,[z280,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z212,z7,z5,z6]),(0,[z122,z0,z1,z4,z123,z5,z6]),(0,[z122,z0,z1,z4,z32,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z281]),(0,[z282,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z163])],[(1,[z0,z1,z170,z32,z5,z6]),(0,[z0,z1,z4,z7,z5,z255,z6])],[(0,[z0,z1,z4,z283,z7,z5,z6]),(0,[z284,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z285]),(0,[z286,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z287,z5,z6]),(0,[z288,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z33,z6]),(0,[z0,z1,z4,z7,z289,z5,z6]),(0,[z290,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z291]),(0,[z0,z1,z4,z7,z5,z292,z6]),(0,[z0,z1,z293,z4,z7,z5,z6]),(0,[z37,z0,z294,z4,z7,z5,z6])],[(0,[z295,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z296,z5,z6]),(0,[z0,z1,z22,z4,z7,z6,z185])],[(0,[z43,z97,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z297,z5,z6]),(0,[z0,z1,z4,z7,z5,z298,z6]),(0,[z76,z0,z1,z7,z23,z5,z6]),(0,[z299,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z43,z122,z0,z1,z4,z5,z6]),(0,[z300,z0,z1,z4,z7,z5,z6]),(0,[z99,z1,z4,z7,z5,z41,z6]),(0,[z0,z85,z4,z7,z5,z146,z6]),(0,[z0,z1,z4,z7,z5,z301,z6]),(0,[z290,z0,z1,z4,z5,z6,z209])],[(0,[z0,z1,z4,z7,z302,z5,z6]),(0,[z0,z140,z1,z4,z7,z5,z6]),(0,[z303,z0,z1,z4,z7,z5,z6]),(0,[z304,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z265,z5,z209])],[(0,[z0,z1,z4,z7,z5,z6,z305])],[(0,[z0,z134,z3,z4,z7,z5,z6]),(0,[z0,z306,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z307,z5,z6]),(0,[z308,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z309])],[(1,[z26,z1,z4,z7,z6,z30]),(1,[z0,z1,z7,z5,z6,z198]),(0,[z0,z1,z4,z310,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z311,z6]),(0,[z0,z1,z4,z7,z5,z6,z312])],[(0,[z0,z4,z7,z313,z197,z5,z6]),(0,[z0,z1,z314,z4,z7,z5,z6]),(0,[z0,z1,z66,z4,z315,z5,z6]),(0,[z0,z1,z4,z7,z5,z316,z6]),(0,[z0,z1,z4,z262,z7,z5,z6])],[(0,[z0,z134,z200,z4,z7,z5,z6]),(0,[z317,z0,z1,z4,z7,z5,z6]),(0,[z98,z1,z4,z128,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z318,z6]),(0,[z319,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z320]),(0,[z321,z0,z1,z4,z7,z5,z6]),(0,[z276,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z162,z7,z322,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z323,z6]),(0,[z0,z1,z4,z7,z5,z6,z324]),(0,[z0,z1,z4,z7,z5,z6,z185])],[(0,[z62,z0,z1,z325,z7,z5,z6]),(0,[z62,z0,z1,z7,z23,z5,z6]),(0,[z0,z1,z326,z4,z7,z5,z6]),(0,[z11,z0,z4,z38,z7,z5,z6]),(0,[z0,z20,z4,z7,z5,z146,z6])],[(0,[z37,z17,z0,z1,z7,z5,z6]),(0,[z0,z1,z4,z96,z128,z7,z6]),(0,[z327,z0,z1,z4,z7,z5,z6]),(0,[z1,z4,z225,z7,z197,z5,z6]),(0,[z328,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z141,z5,z6]),(1,[z0,z1,z210,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z329])],[(0,[z0,z1,z4,z7,z5,z6,z330]),(0,[z1,z81,z4,z331,z7,z5,z6]),(0,[z332,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z333]),(0,[z113,z0,z1,z4,z7,z5,z6]),(0,[z122,z0,z20,z4,z7,z5,z6]),(0,[z0,z1,z334,z4,z7,z5,z6]),(0,[z335,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z336,z7,z5,z6]),(0,[z98,z0,z1,z4,z7,z5,z57]),(0,[z98,z0,z1,z4,z201,z7,z5]),(0,[z0,z1,z337,z4,z7,z5,z6]),(0,[z11,z0,z1,z4,z7,z5,z69]),(1,[z0,z1,z4,z174,z5,z6]),(0,[z338,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z5,z6,z19,z57]),(0,[z0,z1,z4,z7,z339,z5,z6]),(0,[z340,z0,z1,z4,z7,z5,z6]),(0,[z341,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z342]),(0,[z0,z1,z4,z7,z5,z6,z343])]],
   [[(0,[z43,z0,z1,z4,z197,z5,z6]),(0,[z0,z1,z4,z7,z344,z5,z6]),(0,[z98,z0,z85,z1,z4,z7,z5]),(0,[z0,z170,z4,z29,z7,z5,z6]),(0,[z37,z76,z0,z1,z7,z5,z6]),(0,[z345,z0,z1,z4,z7,z5,z6])],[(0,[z249,z0,z1,z38,z7,z5,z6]),(1,[z0,z1,z4,z346,z5,z6]),(0,[z0,z1,z4,z7,z322,z5,z6]),(0,[z0,z1,z4,z7,z5,z347,z6])],[(0,[z17,z0,z1,z4,z256,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z348])],[(0,[z0,z134,z1,z4,z7,z5,z6]),(0,[z124,z0,z1,z170,z7,z5,z6])],[(0,[z37,z0,z1,z4,z7,z5,z58]),(0,[z349,z0,z1,z4,z7,z5,z6])],[(0,[z350,z0,z1,z4,z7,z5,z6]),(0,[z98,z1,z4,z7,z5,z6,z57]),(0,[z351,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z352]),(0,[z0,z4,z201,z7,z78,z5,z6])],[(0,[z0,z1,z4,z256,z7,z5,z6]),(1,[z62,z1,z325,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z353]),(0,[z0,z1,z4,z7,z5,z6,z354]),(0,[z11,z0,z85,z4,z7,z5,z6]),(0,[z0,z1,z355,z4,z7,z5,z6])],[(0,[z356,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z357,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z358,z6]),(0,[z0,z4,z7,z141,z5,z6,z359]),(0,[z124,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z360,z5,z6]),(0,[z76,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z6,z361]),(0,[z249,z0,z1,z66,z7,z5,z6]),(0,[z161,z0,z140,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z362])],[(0,[z1,z325,z4,z128,z7,z5,z6]),(1,[z99,z1,z4,z7,z5,z41]),(0,[z0,z1,z4,z7,z5,z6,z363])],[(0,[z0,z1,z4,z96,z7,z5,z6]),(0,[z0,z1,z4,z225,z7,z5,z6]),(0,[z110,z1,z4,z7,z63,z5,z6]),(1,[z37,z0,z1,z7,z6,z185]),(0,[z0,z1,z4,z7,z5,z6,z364]),(0,[z0,z1,z4,z365,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z366]),(0,[z367,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z368,z4,z7,z5,z6])],[(0,[z0,z3,z4,z7,z123,z5,z6]),(0,[z0,z1,z4,z7,z369,z5,z6])],[(0,[z0,z370,z1,z4,z7,z5,z6]),(0,[z371,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z372])],[(0,[z373,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z325,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z374,z6]),(0,[z0,z20,z1,z4,z32,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z375])],[(0,[z0,z20,z4,z212,z7,z5,z6]),(0,[z376,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z26,z1,z4,z7,z5,z6,z30]),(0,[z0,z1,z4,z7,z125,z5,z6]),(0,[z0,z1,z4,z377,z7,z5,z6]),(0,[z0,z1,z4,z7,z378,z5,z6])],[(0,[z62,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z233,z5,z6]),(0,[z379,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z6]),(0,[z380,z0,z1,z4,z7,z5,z6]),(0,[z381,z0,z1,z4,z7,z5,z6])],[(0,[z14,z1,z3,z4,z7,z5,z6]),(0,[z300,z0,z1,z4,z7,z197,z5]),(0,[z26,z1,z4,z7,z5,z41,z6]),(0,[z0,z1,z4,z7,z5,z6,z382]),(0,[z0,z20,z1,z4,z212,z5,z6]),(0,[z0,z1,z32,z7,z125,z5,z6]),(0,[z0,z81,z4,z9,z7,z5,z6])],[(0,[z0,z1,z383,z4,z7,z5,z6]),(0,[z0,z1,z4,z384,z7,z5,z6]),(0,[z0,z1,z385,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z386,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z387]),(0,[z0,z388,z1,z4,z7,z5,z6]),(0,[z0,z1,z389,z4,z7,z5,z6])],[(1,[z17,z1,z128,z7,z5,z6]),(0,[z0,z1,z4,z7,z390,z5,z6]),(0,[z0,z1,z4,z7,z391,z5,z6]),(0,[z0,z1,z392,z4,z7,z5,z6])],[(0,[z393,z0,z1,z4,z7,z5,z6]),(0,[z62,z1,z325,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z63,z5,z6]),(0,[z0,z134,z4,z7,z5,z146,z6]),(0,[z0,z1,z4,z7,z394,z5,z6]),(0,[z0,z1,z4,z7,z5,z209,z77]),(0,[z0,z395,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z90])],[(1,[z119,z0,z1,z4,z7,z5]),(0,[z0,z4,z7,z5,z6,z396,z57]),(0,[z0,z397,z1,z4,z7,z5,z6]),(1,[z0,z398,z4,z7,z5,z6]),(0,[z0,z398,z170,z4,z7,z5,z6]),(0,[z264,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z399,z5,z6]),(0,[z70,z0,z1,z4,z32,z5,z6]),(1,[z0,z1,z4,z7,z265,z209])],[(0,[z0,z1,z4,z7,z400,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z401]),(0,[z122,z0,z4,z38,z7,z5,z6]),(0,[z402,z0,z1,z4,z7,z5,z6]),(0,[z161,z0,z1,z4,z7,z6,z359]),(0,[z161,z0,z4,z7,z5,z146,z6]),(0,[z0,z1,z4,z7,z403,z5,z6]),(0,[z0,z85,z1,z4,z7,z5,z146]),(0,[z0,z294,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z162,z322,z6])],[(0,[z0,z404,z1,z4,z7,z5,z6]),(0,[z37,z405,z1,z4,z7,z5,z6]),(0,[z406,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z407,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z359]),(1,[z0,z1,z408,z7,z5,z6])],[(0,[z0,z1,z182,z4,z7,z5,z6]),(0,[z0,z1,z38,z7,z23,z5,z6]),(0,[z70,z0,z1,z4,z212,z5,z6]),(0,[z0,z1,z409,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z410]),(0,[z76,z0,z1,z4,z7,z5,z77]),(0,[z0,z1,z4,z7,z5,z6,z411]),(0,[z0,z1,z4,z331,z7,z5,z6]),(0,[z276,z0,z1,z4,z7,z6,z163])],[(0,[z0,z1,z4,z346,z7,z5,z6]),(0,[z161,z0,z4,z7,z5,z6,z359]),(0,[z0,z1,z4,z7,z412,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z413])],[(0,[z11,z0,z4,z7,z141,z5,z6]),(0,[z414,z0,z1,z4,z7,z5,z6])],[(0,[z415,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z32,z197,z5,z6]),(0,[z416,z0,z1,z4,z7,z5,z6]),(0,[z417,z0,z1,z4,z7,z5,z6]),(0,[z37,z0,z1,z7,z5,z82,z6])]],
   [[(0,[z0,z418,z1,z4,z7,z5,z6]),(0,[z0,z1,z66,z325,z7,z5,z6]),(1,[z300,z0,z1,z4,z7,z5]),(0,[z110,z0,z1,z4,z7,z6,z30]),(0,[z0,z1,z66,z7,z23,z5,z6]),(0,[z0,z419,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z420,z5,z6]),(0,[z0,z1,z4,z125,z5,z6,z163]),(0,[z0,z1,z4,z7,z421,z5,z6])],[(0,[z0,z1,z4,z422,z7,z5,z6]),(1,[z14,z3,z4,z7,z5,z6]),(0,[z423,z0,z1,z4,z7,z5,z6]),(0,[z11,z0,z1,z4,z7,z5,z146]),(1,[z0,z1,z4,z5,z255,z6])],[(1,[z0,z182,z4,z7,z5,z6]),(0,[z424,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z425,z4,z7,z5,z6]),(0,[z0,z1,z4,z125,z5,z33,z6]),(0,[z0,z1,z426,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z427])],[(0,[z17,z0,z428,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z197,z5,z6]),(0,[z0,z1,z4,z7,z5,z429,z6]),(0,[z0,z1,z4,z7,z5,z430,z6]),(1,[z431,z0,z4,z7,z5,z6])],[(1,[z0,z120,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z432,z5,z6]),(0,[z433,z0,z1,z4,z7,z5,z6]),(0,[z434,z0,z1,z4,z7,z5,z6]),(0,[z0,z140,z1,z210,z7,z5,z6]),(0,[z0,z1,z435,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z436])],[(0,[z0,z1,z4,z197,z125,z5,z6]),(0,[z0,z1,z4,z7,z437,z5,z6]),(0,[z0,z1,z4,z438,z7,z5,z6])],[(0,[z439,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z77])],[(0,[z17,z0,z1,z128,z7,z5,z6]),(0,[z62,z110,z1,z4,z7,z5,z6]),(0,[z440,z0,z1,z4,z7,z5,z6]),(0,[z441,z0,z1,z4,z7,z5,z6]),(0,[z98,z11,z0,z1,z4,z7,z5]),(0,[z0,z442,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z443,z6]),(0,[z0,z1,z4,z7,z5,z6,z444]),(1,[z0,z426,z4,z7,z5,z6])],[(0,[z445,z0,z1,z4,z7,z5,z6])],[(0,[z37,z0,z1,z170,z7,z5,z6]),(0,[z76,z0,z1,z4,z7,z5,z82])],[(0,[z43,z0,z1,z4,z7,z5,z6]),(0,[z446,z0,z1,z4,z7,z5,z6])],[(0,[z98,z1,z4,z7,z63,z5,z6]),(0,[z0,z134,z4,z212,z7,z5,z6]),(0,[z0,z1,z4,z7,z447,z5,z6]),(0,[z70,z0,z1,z4,z125,z5,z6])],[(0,[z448,z0,z1,z4,z7,z5,z6]),(0,[z110,z0,z1,z22,z4,z7,z6]),(0,[z0,z1,z4,z7,z5,z6,z449]),(1,[z0,z20,z4,z212,z5,z6]),(0,[z450,z0,z1,z4,z7,z5,z6]),(1,[z124,z0,z1,z125,z5,z6]),(0,[z37,z171,z1,z4,z7,z5,z6]),(0,[z0,z1,z7,z5,z451,z6,z209])],[(0,[z14,z0,z1,z422,z7,z5,z6]),(0,[z452,z0,z4,z7,z197,z5,z6]),(1,[z122,z0,z4,z123,z5,z6]),(0,[z37,z0,z1,z4,z7,z5,z6]),(1,[z453,z1,z4,z7,z5,z6])],[(0,[z14,z122,z0,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z454])]],
   [[(0,[z17,z0,z1,z4,z233,z5,z6]),(0,[z0,z1,z7,z5,z6,z198,z30]),(0,[z99,z0,z1,z4,z7,z5,z57]),(0,[z99,z0,z1,z4,z201,z7,z5]),(0,[z0,z4,z7,z5,z455,z6,z209])],[(0,[z0,z1,z456,z4,z7,z5,z6]),(0,[z0,z1,z4,z457,z7,z5,z6]),(0,[z122,z0,z1,z4,z212,z5,z6]),(0,[z0,z1,z458,z4,z7,z5,z6])],[(0,[z459,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z225,z123,z5,z6]),(0,[z70,z0,z1,z4,z5,z6,z90]),(0,[z0,z460,z4,z201,z7,z5,z6])],[(0,[z461,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z462,z6]),(0,[z351,z0,z4,z7,z5,z6,z57]),(0,[z99,z0,z85,z1,z4,z7,z5]),(1,[z0,z460,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z79])],[(0,[z0,z1,z4,z7,z463,z5,z6]),(0,[z0,z1,z4,z7,z5,z464,z6])],[(0,[z0,z1,z4,z465,z7,z5,z6]),(0,[z466,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z467,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z468,z6]),(0,[z0,z469,z1,z4,z7,z5,z6])],[(0,[z470,z0,z1,z4,z7,z5,z6])],[(0,[z471,z0,z1,z4,z7,z5,z6]),(0,[z0,z66,z4,z38,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z472,z6])]],
   [[(0,[z0,z1,z66,z4,z7,z5,z6]),(0,[z0,z1,z4,z473,z7,z5,z6]),(0,[z0,z85,z1,z4,z7,z5,z69]),(0,[z0,z405,z1,z4,z7,z5,z6]),(0,[z1,z4,z7,z5,z6,z79,z209])],[(0,[z0,z1,z4,z212,z225,z5,z6]),(0,[z474,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z475,z7,z5,z6]),(0,[z476,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z477,z7,z5,z6]),(0,[z478,z0,z1,z4,z7,z5,z6])],[(0,[z127,z0,z3,z4,z7,z5,z6]),(0,[z0,z479,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z480,z6]),(0,[z0,z398,z1,z4,z7,z5,z6])],[(0,[z481,z0,z1,z4,z128,z7,z6]),(0,[z482,z0,z1,z4,z7,z5,z6]),(0,[z483,z0,z1,z4,z7,z5,z6]),(0,[z83,z1,z4,z7,z5,z6,z209])],[(0,[z484,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z257,z7,z5,z6]),(1,[z43,z1,z4,z197,z5,z6]),(0,[z0,z485,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z486,z7,z5,z6]),(0,[z487,z0,z1,z4,z7,z5,z6]),(0,[z453,z1,z81,z4,z7,z5,z6])],[(0,[z17,z62,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z488]),(0,[z489,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z490,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z491]),(0,[z0,z1,z4,z7,z265,z6,z209]),(1,[z290,z0,z1,z4,z5,z6])],[(0,[z127,z0,z200,z4,z7,z5,z6]),(0,[z492,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z123,z5,z33,z6])],[(0,[z493,z0,z1,z4,z7,z5,z6]),(0,[z494,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z495,z6]),(0,[z110,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z496,z7,z5,z6]),(0,[z37,z0,z1,z22,z7,z5,z6])],[(0,[z0,z1,z428,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z497,z5,z6]),(0,[z122,z0,z1,z4,z125,z5,z6])],[(0,[z498,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z499,z5,z6]),(0,[z500,z0,z1,z4,z7,z5,z6]),(0,[z501,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z170,z325,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z502]),(0,[z0,z1,z170,z7,z23,z5,z6]),(1,[z0,z294,z4,z7,z5,z6]),(1,[z0,z1,z22,z7,z23,z6])],[(0,[z0,z1,z4,z503,z7,z5,z6]),(0,[z504,z0,z1,z4,z7,z5,z6])],[(0,[z43,z1,z4,z7,z197,z5,z6]),(0,[z0,z1,z4,z505,z7,z5,z6]),(0,[z0,z1,z4,z212,z5,z33,z6]),(0,[z0,z1,z4,z7,z23,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z506])],[(0,[z507,z0,z1,z4,z7,z5,z6]),(0,[z508,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z509,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z510]),(1,[z0,z428,z4,z7,z5,z6]),(0,[z97,z1,z4,z225,z7,z5,z6]),(0,[z0,z1,z4,z7,z511,z5,z6]),(0,[z0,z140,z1,z4,z7,z6,z359]),(0,[z0,z1,z4,z512,z7,z5,z6]),(0,[z0,z1,z513,z4,z7,z5,z6])]],
   [[(1,[z0,z1,z422,z7,z5,z6]),(0,[z119,z0,z1,z3,z4,z7,z5]),(0,[z514,z0,z1,z4,z7,z5,z6]),(0,[z0,z140,z4,z38,z7,z5,z6]),(0,[z0,z134,z140,z4,z7,z5,z6]),(0,[z515,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z516,z7,z5,z6]),(0,[z0,z1,z170,z32,z7,z5,z6]),(1,[z0,z1,z4,z7,z5,z80])],[(0,[z0,z1,z517,z4,z7,z5,z6]),(0,[z518,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z386,z5,z6])],[(0,[z127,z0,z1,z4,z7,z5,z6]),(0,[z149,z0,z1,z4,z7,z5,z6]),(0,[z519,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z520,z5,z6]),(0,[z0,z1,z4,z32,z7,z5,z6]),(1,[z0,z1,z4,z201,z5,z33]),(0,[z0,z1,z521,z4,z7,z5,z6])],[(0,[z481,z0,z1,z4,z7,z5,z6]),(0,[z522,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z523,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z524,z5,z6]),(0,[z0,z1,z4,z7,z525,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z526])],[(0,[z0,z0,z1,z4,z7,z5,z6]),(0,[z527,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z528,z5,z6]),(1,[z83,z1,z4,z7,z5,z6])],[(0,[z0,z1,z2,z4,z7,z5,z6]),(0,[z0,z1,z4,z529,z7,z5,z6]),(0,[z0,z1,z4,z7,z530,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z531])],[(0,[z0,z1,z4,z532,z7,z5,z6]),(0,[z0,z1,z4,z7,z7,z5,z6]),(0,[z0,z1,z4,z7,z533,z5,z6]),(0,[z161,z11,z0,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z534]),(0,[z0,z1,z4,z7,z5,z82,z6])],[(0,[z0,z1,z4,z7,z5,z6,z535]),(0,[z0,z1,z4,z7,z315,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z536,z6]),(0,[z537,z0,z1,z4,z7,z5,z6]),(0,[z276,z0,z1,z4,z7,z322,z6]),(0,[z0,z538,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z451,z6])],[(0,[z539,z0,z1,z4,z7,z5,z6]),(0,[z0,z540,z1,z4,z7,z5,z6]),(1,[z161,z0,z4,z7,z6,z359]),(0,[z0,z1,z4,z541,z7,z5,z6]),(0,[z0,z1,z4,z162,z322,z5,z6]),(0,[z70,z0,z1,z4,z201,z5,z6])],[(0,[z0,z1,z4,z542,z7,z5,z6]),(0,[z98,z0,z1,z4,z7,z5,z41]),(0,[z0,z1,z4,z7,z543,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z544]),(0,[z0,z1,z4,z7,z136,z5,z6])],[(0,[z545,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z546,z7,z5,z6]),(0,[z547,z0,z1,z4,z7,z5,z6]),(0,[z548,z0,z1,z4,z7,z5,z6]),(0,[z0,z549,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z550,z5,z6]),(0,[z551,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z552,z7,z5,z6])],[(0,[z0,z1,z4,z553,z7,z5,z6]),(0,[z0,z1,z4,z554,z7,z5,z6])],[(0,[z0,z1,z4,z7,z555,z5,z6]),(0,[z0,z4,z7,z5,z146,z6,z69])]],
   [[(0,[z14,z0,z1,z4,z165,z5,z6]),(0,[z556,z0,z1,z4,z7,z5,z6]),(0,[z0,z557,z1,z4,z7,z5,z6]),(0,[z558,z0,z1,z4,z7,z5,z6]),(0,[z559,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z560])],[(0,[z0,z1,z4,z7,z5,z561,z6]),(0,[z0,z1,z4,z7,z5,z6,z562]),(0,[z37,z26,z0,z1,z4,z7,z6]),(0,[z0,z1,z4,z563,z7,z5,z6]),(0,[z0,z1,z4,z7,z564,z5,z6])],[(0,[z565,z0,z1,z4,z7,z5,z6]),(0,[z113,z0,z1,z4,z5,z6,z57]),(0,[z566,z0,z1,z4,z7,z5,z6]),(0,[z567,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z7,z5,z58]),(0,[z568,z0,z1,z4,z7,z5,z6]),(0,[z112,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z569,z7,z5,z6]),(0,[z0,z1,z570,z4,z7,z5,z6]),(0,[z0,z1,z170,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z571,z6])],[(0,[z572,z0,z1,z4,z7,z5,z6]),(0,[z110,z0,z1,z4,z7,z63,z6])],[(0,[z0,z1,z42,z4,z7,z5,z6]),(0,[z127,z0,z4,z7,z5,z146,z6]),(0,[z0,z1,z4,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z573,z5,z6]),(0,[z0,z134,z4,z7,z5,z6,z359]),(0,[z574,z0,z1,z4,z7,z5,z6]),(0,[z171,z0,z1,z4,z7,z5,z6]),(0,[z575,z0,z1,z4,z7,z5,z6])],[(0,[z14,z0,z200,z4,z7,z5,z6]),(0,[z576,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z577,z4,z7,z5,z6]),(0,[z97,z0,z1,z4,z197,z5,z6]),(0,[z578,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z579]),(0,[z0,z1,z408,z4,z7,z5,z6])],[(0,[z0,z580,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z581,z5,z6])]],
   [[(0,[z200,z1,z3,z4,z7,z5,z6]),(0,[z0,z1,z4,z582,z7,z5,z6]),(0,[z0,z1,z4,z7,z313,z5,z6]),(0,[z0,z1,z4,z162,z125,z5,z6]),(0,[z70,z0,z1,z4,z322,z5,z6])],[(0,[z0,z583,z1,z4,z7,z5,z6]),(0,[z0,z104,z1,z4,z7,z5,z6]),(1,[z249,z0,z38,z7,z5,z6]),(0,[z0,z1,z4,z7,z584,z5,z6]),(0,[z37,z0,z1,z4,z7,z6,z185]),(0,[z585,z0,z1,z4,z7,z5,z6])],[(0,[z98,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z586])],[(0,[z0,z1,z4,z7,z5,z6,z587])],[(0,[z14,z127,z1,z4,z7,z5,z6]),(0,[z588,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z589]),(0,[z0,z1,z590,z4,z7,z5,z6]),(0,[z249,z0,z134,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z86,z5,z6]),(0,[z37,z0,z1,z4,z174,z5,z6])],[(0,[z0,z1,z591,z4,z7,z5,z6]),(0,[z0,z20,z1,z4,z125,z5,z6])],[(1,[z0,z4,z7,z313,z5,z6]),(0,[z0,z1,z592,z4,z7,z5,z6])],[(1,[z0,z85,z4,z7,z5,z146]),(0,[z593,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z594,z6]),(0,[z0,z1,z22,z4,z7,z23,z6])],[(0,[z0,z1,z4,z7,z595,z5,z6]),(0,[z596,z0,z1,z4,z7,z5,z6]),(0,[z597,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z598]),(0,[z0,z1,z4,z7,z599,z5,z6])],[(0,[z43,z0,z1,z159,z7,z5,z6]),(0,[z600,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z601,z7,z5,z6])],[(0,[z0,z3,z4,z38,z7,z5,z6]),(1,[z0,z1,z81,z7,z5,z82]),(0,[z0,z1,z4,z7,z5,z455,z6])],[(0,[z0,z1,z4,z7,z602,z5,z6]),(0,[z62,z1,z4,z7,z5,z41,z6]),(0,[z0,z1,z4,z7,z5,z6,z396]),(0,[z0,z1,z4,z7,z5,z6,z69]),(1,[z264,z145,z0,z1,z4,z7])],[(0,[z0,z140,z4,z7,z141,z5,z6]),(0,[z0,z1,z4,z603,z7,z5,z6]),(0,[z0,z1,z4,z7,z265,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z604]),(0,[z0,z1,z605,z4,z7,z5,z6]),(0,[z0,z1,z4,z528,z7,z5,z6]),(0,[z606,z0,z1,z4,z7,z5,z6])],[(0,[z145,z0,z1,z4,z7,z265,z5]),(0,[z431,z0,z4,z7,z5,z6,z209])]],
   [[(0,[z0,z200,z4,z7,z123,z5,z6]),(1,[z405,z1,z4,z7,z5,z6])],[(0,[z607,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z608,z5,z6]),(0,[z0,z1,z609,z4,z7,z5,z6]),(1,[z0,z4,z7,z78,z5,z6]),(1,[z0,z4,z7,z5,z455,z6])],[(0,[z610,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z165,z5,z6]),(1,[z127,z200,z4,z7,z5,z6]),(1,[z0,z4,z7,z5,z6,z396]),(0,[z0,z1,z66,z4,z346,z5,z6]),(1,[z0,z1,z611,z7,z5,z6]),(0,[z124,z0,z1,z4,z32,z5,z6]),(0,[z0,z1,z4,z7,z5,z612,z6]),(0,[z0,z1,z4,z7,z5,z6,z613])],[(0,[z127,z0,z4,z212,z7,z5,z6]),(0,[z0,z1,z4,z614,z7,z5,z6]),(0,[z0,z1,z4,z322,z5,z6,z163]),(0,[z0,z1,z4,z615,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z616])],[(0,[z0,z617,z1,z4,z7,z5,z6]),(1,[z98,z1,z4,z7,z5,z57]),(0,[z0,z1,z4,z201,z7,z5,z6])],[(0,[z618,z0,z1,z4,z7,z5,z6]),(0,[z0,z469,z81,z4,z7,z5,z6]),(0,[z0,z1,z4,z322,z5,z33,z6])],[(1,[z0,z1,z2,z4,z5,z6]),(0,[z619,z0,z1,z4,z7,z5,z6]),(0,[z127,z200,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z123,z5,z6]),(0,[z276,z0,z1,z4,z162,z5,z6]),(0,[z0,z620,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z621,z6]),(0,[z622,z0,z1,z4,z7,z5,z6]),(0,[z623,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z624]),(1,[z0,z1,z7,z5,z451,z6])]],
   [[(0,[z0,z200,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z625,z6]),(1,[z351,z0,z4,z7,z5,z6]),(0,[z626,z0,z1,z4,z7,z5,z6]),(1,[z70,z0,z1,z4,z5,z90])],[(0,[z0,z1,z4,z7,z5,z6,z627]),(0,[z0,z1,z628,z4,z7,z5,z6]),(0,[z0,z1,z611,z4,z7,z5,z6]),(0,[z629,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z201,z7,z5,z90])],[(0,[z43,z0,z1,z4,z225,z5,z6]),(0,[z0,z1,z4,z630,z7,z5,z6]),(0,[z264,z145,z0,z1,z4,z7,z5])],[(0,[z17,z1,z4,z128,z7,z5,z6]),(0,[z0,z134,z1,z38,z7,z5,z6]),(0,[z0,z1,z4,z7,z631,z5,z6]),(0,[z0,z1,z4,z7,z632,z5,z6]),(0,[z0,z1,z4,z633,z7,z5,z6])],[(0,[z0,z1,z4,z212,z197,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z634])],[(0,[z0,z1,z4,z7,z5,z635,z6]),(0,[z0,z1,z4,z7,z5,z6,z636]),(0,[z0,z1,z4,z637,z7,z5,z6]),(0,[z11,z0,z134,z4,z7,z5,z6]),(1,[z0,z1,z4,z262,z5,z6])],[(0,[z0,z1,z325,z7,z125,z5,z6]),(0,[z0,z1,z4,z7,z638,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6,z639]),(1,[z471,z0,z1,z7,z5,z6]),(0,[z471,z0,z1,z7,z5,z6,z30]),(0,[z0,z1,z4,z7,z5,z6,z640]),(0,[z0,z1,z4,z7,z5,z6,z641]),(0,[z0,z460,z1,z4,z7,z5,z6])]],
   [[(0,[z642,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z109,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z643]),(0,[z0,z1,z7,z5,z82,z6,z77])],[(0,[z0,z1,z4,z7,z5,z6,z644]),(0,[z645,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z162,z7,z136,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z646])],[(0,[z0,z1,z128,z38,z7,z5,z6]),(0,[z0,z134,z1,z66,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z647]),(0,[z0,z1,z4,z7,z648,z5,z6])],[(0,[z0,z1,z4,z7,z649,z5,z6]),(0,[z650,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z81,z4,z386,z5,z6])],[(1,[z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z651,z7,z5,z6]),(0,[z652,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z653,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z654,z6]),(0,[z99,z0,z1,z4,z7,z5,z41]),(1,[z0,z1,z4,z315,z5,z6])],[(0,[z0,z1,z325,z38,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z655]),(0,[z1,z4,z7,z5,z41,z6,z57]),(0,[z124,z0,z1,z4,z125,z5,z6]),(0,[z656,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z81,z4,z528,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z657]),(0,[z0,z1,z658,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z659,z5,z6]),(0,[z37,z62,z0,z1,z7,z5,z6]),(0,[z660,z0,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z142,z5,z6]),(0,[z0,z1,z4,z7,z661,z5,z6]),(0,[z453,z0,z1,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z5,z6,z662]),(0,[z0,z4,z38,z7,z5,z146,z6])],[(0,[z97,z0,z1,z4,z7,z5,z6]),(0,[z452,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z225,z125,z5,z6]),(0,[z0,z1,z4,z663,z7,z5,z6]),(0,[z664,z0,z1,z4,z7,z5,z6]),(0,[z249,z0,z1,z4,z7,z5,z6])],[(0,[z26,z110,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z665,z7,z5,z6]),(0,[z0,z666,z1,z4,z7,z5,z6]),(0,[z0,z1,z7,z23,z5,z6,z185])],[(0,[z0,z1,z4,z7,z5,z6,z667]),(0,[z17,z0,z1,z325,z7,z5,z6]),(0,[z668,z0,z1,z4,z7,z5,z6]),(0,[z17,z0,z1,z7,z23,z5,z6]),(1,[z452,z0,z4,z7,z5,z6]),(0,[z98,z70,z0,z1,z4,z7,z5])],[(0,[z0,z4,z38,z7,z5,z6,z359])],[(0,[z0,z1,z4,z7,z5,z669,z6]),(0,[z0,z1,z257,z4,z7,z5,z6]),(0,[z0,z4,z7,z123,z5,z146,z6]),(0,[z76,z0,z1,z7,z5,z6,z77]),(0,[z670,z0,z1,z4,z7,z5,z6])],[(0,[z0,z1,z15,z4,z7,z5,z6]),(1,[z0,z469,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z671,z5,z6]),(0,[z0,z1,z4,z7,z672,z5,z6]),(0,[z37,z0,z426,z4,z7,z5,z6]),(0,[z0,z673,z1,z4,z7,z5,z6]),(0,[z0,z674,z1,z4,z7,z5,z6]),(0,[z145,z0,z1,z4,z7,z6,z209])]],
   [[(0,[z0,z1,z4,z7,z5,z6,z675]),(0,[z161,z0,z1,z4,z7,z141,z6]),(0,[z11,z0,z4,z7,z5,z6,z69])],[(0,[z676,z0,z1,z4,z7,z5,z6]),(0,[z677,z0,z1,z4,z7,z5,z6]),(0,[z145,z0,z1,z4,z7,z5,z77])],[(0,[z11,z14,z0,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z80]),(0,[z112,z0,z1,z7,z5,z6,z209])],[(0,[z0,z20,z3,z4,z7,z5,z6]),(0,[z0,z1,z4,z678,z7,z5,z6]),(0,[z679,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z680,z5,z6]),(0,[z276,z0,z1,z4,z5,z6,z163]),(0,[z0,z1,z4,z7,z5,z6,z681])],[(0,[z0,z1,z4,z7,z682,z5,z6]),(0,[z0,z1,z683,z4,z7,z5,z6]),(0,[z0,z684,z1,z4,z7,z5,z6])],[(0,[z62,z0,z1,z128,z7,z5,z6]),(0,[z0,z685,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z686,z5,z6]),(0,[z0,z1,z4,z7,z5,z687,z6]),(0,[z99,z0,z1,z4,z7,z5,z6]),(0,[z688,z0,z1,z4,z7,z5,z6]),(0,[z276,z0,z1,z4,z5,z33,z6]),(0,[z0,z1,z4,z7,z5,z6,z209])],[(0,[z0,z1,z4,z7,z689,z5,z6]),(1,[z0,z140,z4,z7,z141,z6]),(0,[z0,z1,z4,z201,z7,z5,z33])],[(0,[z0,z20,z200,z4,z7,z5,z6]),(1,[z97,z1,z4,z225,z5,z6]),(0,[z26,z0,z1,z4,z7,z6,z30]),(0,[z0,z1,z4,z7,z5,z690,z6]),(1,[z1,z4,z331,z7,z5,z6]),(0,[z264,z145,z0,z1,z4,z7,z6])]],
   [[(0,[z37,z0,z1,z4,z7,z23,z6]),(0,[z691,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z692])],[(0,[z0,z1,z4,z7,z693,z5,z6]),(0,[z0,z1,z4,z32,z225,z5,z6]),(0,[z0,z694,z1,z4,z7,z5,z6]),(0,[z0,z695,z1,z4,z7,z5,z6])],[(0,[z696,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z697,z5,z6]),(0,[z11,z0,z4,z7,z123,z5,z6]),(0,[z0,z85,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z86,z5,z6]),(1,[z276,z0,z1,z4,z6,z163])],[(1,[z481,z0,z1,z4,z7,z6]),(0,[z0,z698,z1,z4,z7,z5,z6]),(0,[z431,z0,z1,z4,z7,z5,z6]),(0,[z264,z0,z1,z4,z7,z5,z209])],[(0,[z14,z0,z1,z4,z109,z5,z6]),(0,[z11,z127,z0,z4,z7,z5,z6]),(0,[z0,z1,z4,z159,z7,z5,z6]),(0,[z0,z140,z1,z611,z7,z5,z6])],[(0,[z14,z0,z3,z4,z7,z5,z6]),(0,[z699,z0,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z700]),(0,[z122,z0,z134,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z701]),(0,[z0,z85,z1,z4,z142,z5,z6]),(0,[z0,z1,z4,z7,z5,z6,z702]),(0,[z0,z1,z703,z4,z7,z5,z6])],[(0,[z149,z0,z1,z3,z4,z5,z6]),(0,[z0,z704,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z705,z5,z6]),(0,[z0,z4,z38,z212,z7,z5,z6]),(0,[z37,z0,z1,z7,z125,z5,z6]),(0,[z0,z1,z4,z162,z7,z5,z6]),(0,[z0,z706,z1,z4,z7,z5,z6])],[(1,[z0,z1,z42,z4,z7,z5]),(0,[z0,z1,z408,z162,z7,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z4,z707,z5,z6]),(0,[z0,z1,z4,z708,z5,z6]),(0,[z471,z0,z709,z7,z5,z6]),(0,[z0,z1,z710,z7,z5,z6]),(0,[z0,z294,z4,z174,z5,z6])],[(0,[z0,z1,z15,z7,z5,z6]),(0,[z452,z0,z4,z109,z5,z6]),(0,[z0,z711,z4,z7,z5,z6]),(0,[z0,z1,z7,z136,z5,z6]),(1,[z0,z1,z7,z6,z712])],[(0,[z0,z1,z4,z713,z5,z6]),(0,[z0,z1,z4,z7,z714,z5]),(0,[z0,z1,z715,z7,z5,z6])],[(0,[z149,z0,z182,z4,z5,z6]),(0,[z0,z1,z4,z7,z5,z716]),(0,[z0,z1,z4,z7,z5,z717]),(0,[z0,z718,z4,z7,z5,z6]),(0,[z171,z1,z4,z262,z5,z6])],[(0,[z0,z182,z4,z5,z33,z6]),(0,[z0,z1,z4,z719,z5,z6]),(0,[z431,z0,z4,z5,z255,z6])],[(0,[z97,z1,z523,z4,z5,z6]),(0,[z0,z1,z4,z7,z720,z6]),(0,[z0,z270,z4,z212,z5,z6])],[(0,[z14,z149,z0,z4,z5,z6])],[(0,[z119,z149,z0,z1,z4,z5]),(0,[z0,z1,z159,z7,z5,z6]),(0,[z0,z1,z4,z7,z721,z6]),(0,[z0,z722,z4,z7,z5,z6])]],
   [[(0,[z0,z723,z4,z7,z5,z6]),(0,[z0,z1,z4,z724,z7,z6]),(0,[z0,z725,z4,z7,z5,z6]),(0,[z481,z0,z1,z38,z7,z6]),(0,[z0,z1,z4,z7,z5,z726]),(0,[z0,z4,z5,z6,z19,z396])],[(0,[z98,z113,z1,z4,z5,z57]),(0,[z98,z0,z1,z4,z142,z5]),(0,[z0,z694,z38,z7,z5,z6]),(0,[z0,z1,z727,z7,z5,z6]),(0,[z728,z1,z4,z7,z5,z6]),(0,[z0,z4,z729,z7,z5,z6])],[(0,[z70,z0,z1,z159,z5,z6]),(0,[z98,z0,z460,z4,z7,z5]),(0,[z0,z730,z4,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z6]),(0,[z0,z731,z4,z7,z5,z6])],[(0,[z0,z620,z4,z123,z5,z6]),(0,[z0,z1,z4,z7,z5,z732]),(0,[z1,z4,z7,z5,z6,z733])],[(0,[z0,z1,z734,z7,z5,z6]),(0,[z0,z1,z735,z7,z5,z6]),(0,[z736,z0,z1,z4,z7,z209])],[(0,[z122,z0,z422,z7,z5,z6]),(0,[z0,z1,z737,z7,z5,z6]),(0,[z62,z405,z1,z7,z5,z6]),(0,[z0,z4,z7,z738,z5,z6]),(0,[z739,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z740,z5,z6]),(0,[z0,z428,z128,z7,z5,z6]),(0,[z741,z0,z4,z7,z5,z6]),(0,[z112,z0,z1,z7,z5,z77])]],
   [[(0,[z37,z0,z426,z7,z6,z185])],[(0,[z0,z1,z4,z742,z5,z6]),(0,[z0,z743,z4,z7,z5,z6]),(0,[z351,z0,z4,z5,z6,z19])],[(0,[z0,z4,z744,z7,z5,z6]),(0,[z70,z0,z1,z4,z432,z5]),(0,[z0,z1,z7,z6,z712,z185])],[(0,[z0,z134,z279,z7,z5,z6])],[(0,[z0,z745,z4,z7,z5,z6]),(0,[z0,z48,z4,z212,z5,z6]),(0,[z0,z1,z7,z23,z275,z6])],[(0,[z76,z0,z1,z7,z5,z746]),(0,[z290,z0,z1,z4,z265,z209])],[(0,[z280,z0,z1,z125,z5,z6])],[(0,[z11,z0,z422,z7,z5,z6]),(0,[z471,z0,z747,z7,z5,z6]),(0,[z0,z748,z4,z7,z5,z6]),(0,[z749,z1,z4,z7,z5,z6]),(0,[z1,z750,z4,z7,z5,z6]),(0,[z751,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z174,z5,z58])]],
   [[(0,[z0,z428,z4,z233,z5,z6]),(1,[z0,z4,z7,z6,z752]),(0,[z286,z0,z1,z4,z6,z163])],[(0,[z0,z1,z753,z7,z5,z6]),(0,[z0,z1,z4,z7,z754,z5]),(0,[z0,z140,z4,z7,z150,z6]),(0,[z755,z0,z1,z4,z5,z6])],[],[(0,[z200,z756,z4,z7,z5,z6]),(0,[z757,z1,z4,z7,z5,z6])],[(0,[z0,z1,z128,z233,z5,z6]),(0,[z99,z1,z683,z4,z7,z5]),(0,[z0,z49,z38,z7,z5,z6]),(0,[z122,z0,z4,z420,z5,z6]),(0,[z0,z4,z7,z5,z758,z69]),(0,[z0,z759,z4,z7,z5,z6])],[(0,[z119,z0,z134,z4,z7,z5]),(0,[z760,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z19]),(0,[z0,z1,z7,z5,z6,z761]),(0,[z98,z1,z4,z5,z19,z57]),(0,[z0,z1,z4,z762,z5,z6]),(0,[z0,z1,z7,z763,z5,z6]),(0,[z0,z140,z4,z7,z141,z6]),(0,[z112,z0,z1,z7,z5,z82]),(0,[z0,z4,z764,z7,z5,z6])],[(0,[z110,z1,z4,z7,z499,z6]),(0,[z0,z182,z257,z7,z5,z6]),(0,[z43,z182,z4,z197,z5,z6]),(0,[z0,z408,z764,z7,z5,z6])],[]],
   [[(0,[z0,z4,z109,z5,z146,z6]),(0,[z466,z3,z4,z7,z5,z6]),(0,[z0,z765,z4,z7,z5,z6]),(0,[z0,z120,z257,z7,z5,z6]),(0,[z43,z120,z4,z197,z5,z6]),(0,[z0,z134,z4,z346,z5,z6]),(0,[z0,z1,z4,z7,z766,z6]),(0,[z0,z767,z4,z7,z5,z6]),(0,[z0,z4,z768,z7,z5,z6])],[(0,[z0,z1,z4,z86,z5,z6]),(0,[z276,z0,z1,z4,z6,z163]),(0,[z70,z0,z1,z4,z5,z769])],[(0,[z481,z0,z1,z4,z7,z6]),(0,[z0,z1,z770,z7,z5,z6]),(0,[z110,z405,z1,z4,z7,z6]),(0,[z771,z1,z4,z7,z5,z6]),(0,[z0,z426,z4,z262,z5,z6]),(0,[z37,z0,z294,z7,z6,z185])],[(0,[z0,z772,z4,z7,z5,z6]),(0,[z0,z134,z66,z315,z5,z6]),(0,[z37,z0,z1,z7,z6,z196]),(0,[z0,z1,z262,z125,z5,z6]),(0,[z290,z1,z4,z5,z6,z79])],[(0,[z62,z1,z517,z7,z5,z6]),(0,[z304,z1,z325,z7,z5,z6]),(0,[z0,z1,z4,z773,z5,z6]),(0,[z122,z0,z4,z774,z5,z6]),(1,[z0,z1,z4,z5,z769]),(0,[z83,z1,z4,z7,z265,z209]),(0,[z0,z4,z7,z265,z455,z209])],[(0,[z0,z1,z7,z5,z6,z775]),(0,[z776,z0,z1,z4,z5,z6]),(0,[z70,z0,z1,z4,z5,z639])],[(0,[z0,z1,z4,z7,z6,z777]),(0,[z1,z4,z7,z5,z6,z778])],[(0,[z481,z1,z4,z7,z41,z6]),(0,[z1,z4,z465,z7,z5,z41]),(0,[z98,z351,z0,z4,z7,z5]),(0,[z0,z1,z4,z779,z5,z6])]],
   [[],[(0,[z14,z3,z422,z7,z5,z6]),(0,[z0,z780,z4,z7,z5,z6]),(0,[z781,z1,z4,z7,z5,z6])],[(0,[z782,z0,z1,z4,z5,z6]),(0,[z783,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z7,z18,z5]),(0,[z0,z85,z326,z4,z7,z5]),(0,[z1,z4,z784,z7,z5,z6]),(0,[z1,z4,z7,z5,z6,z785]),(0,[z0,z1,z4,z786,z5,z6]),(0,[z0,z1,z7,z265,z451,z209]),(0,[z0,z1,z4,z787,z5,z6])],[(0,[z99,z1,z4,z7,z5,z788])],[(0,[z0,z134,z357,z7,z5,z6]),(0,[z0,z1,z789,z7,z5,z6]),(0,[z37,z0,z1,z7,z58,z185]),(0,[z0,z1,z4,z6,z790,z163])],[(0,[z0,z3,z4,z109,z5,z6]),(0,[z149,z0,z4,z123,z5,z6]),(0,[z791,z1,z4,z7,z5,z6]),(0,[z405,z1,z4,z174,z5,z6]),(0,[z83,z1,z4,z5,z255,z6])],[(0,[z0,z792,z4,z7,z5,z6]),(0,[z62,z1,z88,z7,z5,z6]),(0,[z0,z1,z7,z394,z23,z6])],[(0,[z0,z1,z4,z793,z5,z6]),(0,[z0,z20,z4,z632,z5,z6]),(0,[z0,z1,z170,z32,z5,z6]),(0,[z0,z1,z392,z125,z5,z6]),(0,[z794,z1,z4,z7,z5,z6]),(0,[z0,z1,z7,z5,z6,z795])]],
   [[],[(0,[z0,z200,z4,z109,z5,z6]),(0,[z0,z1,z4,z796,z5,z6]),(0,[z1,z4,z7,z797,z5,z6]),(0,[z798,z1,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z146,z252]),(0,[z0,z1,z4,z7,z799,z6]),(0,[z1,z4,z7,z800,z5,z6]),(0,[z145,z736,z0,z1,z4,z7])],[(0,[z471,z0,z1,z801,z5,z6]),(0,[z0,z802,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z769])],[(0,[z0,z1,z15,z109,z5,z6]),(0,[z0,z1,z4,z803,z5,z6]),(0,[z0,z1,z4,z7,z804,z5])],[(0,[z0,z1,z4,z7,z805,z6]),(0,[z0,z1,z4,z7,z5,z806]),(0,[z0,z1,z807,z7,z5,z6]),(0,[z0,z418,z66,z7,z5,z6]),(0,[z1,z4,z7,z5,z41,z788]),(0,[z276,z0,z1,z4,z6,z790])],[(0,[z0,z1,z808,z4,z7,z5]),(0,[z809,z0,z1,z7,z5,z6]),(0,[z0,z4,z7,z5,z6,z758]),(0,[z810,z1,z4,z7,z5,z6]),(1,[z0,z1,z4,z6,z790])],[(0,[z0,z1,z4,z5,z6,z811]),(0,[z0,z1,z812,z7,z5,z6]),(0,[z0,z813,z4,z7,z5,z6]),(0,[z0,z1,z4,z814,z5,z6])],[(0,[z0,z1,z4,z815,z5,z6]),(0,[z0,z816,z4,z7,z5,z6])]],
   [[(0,[z43,z1,z257,z197,z5,z6]),(0,[z26,z471,z1,z7,z6,z30]),(0,[z26,z471,z0,z1,z7,z6])],[(0,[z1,z325,z807,z7,z5,z6]),(0,[z43,z452,z4,z197,z5,z6]),(0,[z817,z0,z4,z7,z5,z6]),(0,[z0,z4,z818,z7,z5,z6]),(0,[z1,z4,z7,z5,z788,z57])],[(0,[z452,z0,z4,z32,z5,z6]),(0,[z819,z0,z1,z4,z7,z5]),(0,[z453,z1,z4,z528,z5,z6])],[(0,[z0,z182,z4,z197,z5,z6])],[(0,[z0,z104,z4,z7,z5,z6]),(0,[z0,z1,z4,z820,z5,z6])],[(0,[z0,z1,z4,z109,z5,z6]),(0,[z0,z4,z7,z5,z146,z291]),(0,[z43,z395,z1,z4,z5,z6]),(0,[z110,z1,z4,z7,z63,z6]),(0,[z0,z4,z7,z5,z6,z821]),(0,[z0,z1,z4,z822,z5,z6]),(0,[z0,z460,z4,z201,z5,z33])],[(0,[z452,z0,z4,z212,z5,z6]),(0,[z0,z823,z4,z7,z5,z6]),(0,[z0,z824,z4,z7,z5,z6])],[(0,[z26,z1,z4,z7,z6,z825]),(0,[z0,z1,z826,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z7,z827,z6]),(0,[z0,z4,z201,z78,z5,z33])],[(0,[z0,z1,z828,z7,z5,z6]),(0,[z17,z1,z807,z7,z5,z6]),(0,[z0,z1,z4,z174,z5,z6]),(0,[z0,z4,z7,z5,z6,z829])],[(0,[z0,z1,z4,z830,z5,z6]),(0,[z0,z294,z38,z7,z5,z6]),(0,[z0,z1,z4,z831,z5,z6]),(0,[z0,z426,z4,z7,z5,z58]),(0,[z0,z1,z4,z262,z5,z80]),(0,[z290,z0,z1,z5,z451,z6])],[(0,[z0,z1,z832,z7,z5,z6]),(0,[z0,z1,z833,z7,z5,z6]),(0,[z0,z20,z182,z4,z5,z6]),(0,[z0,z834,z1,z4,z5,z6]),(0,[z0,z1,z4,z7,z5,z746]),(0,[z0,z1,z4,z7,z6,z790])],[(0,[z0,z1,z4,z835,z5,z6]),(0,[z0,z1,z4,z7,z5,z836])],[(0,[z471,z1,z128,z7,z5,z6]),(1,[z1,z4,z7,z5,z788]),(0,[z0,z1,z4,z346,z5,z6]),(0,[z0,z4,z5,z255,z455,z6])],[(0,[z0,z837,z4,z7,z5,z6]),(0,[z0,z1,z4,z838,z5,z6])],[(0,[z0,z1,z4,z839,z5,z6]),(0,[z37,z0,z1,z262,z6,z185]),(0,[z840,z0,z1,z4,z5,z6]),(0,[z70,z0,z1,z4,z5,z579])]],
   [[(0,[z149,z0,z1,z4,z5,z6]),(0,[z0,z1,z841,z7,z5,z6]),(0,[z0,z1,z842,z7,z5,z6])],[(0,[z0,z843,z4,z7,z5,z6]),(0,[z844,z0,z1,z7,z5,z6]),(0,[z0,z294,z66,z7,z5,z6]),(0,[z0,z85,z4,z7,z5,z758]),(0,[z112,z0,z7,z5,z455,z6])],[(0,[z62,z1,z325,z7,z5,z6]),(0,[z481,z0,z1,z170,z7,z6]),(0,[z43,z452,z0,z4,z5,z6]),(0,[z99,z0,z460,z4,z7,z5]),(0,[z11,z0,z4,z7,z5,z647]),(0,[z0,z845,z4,z7,z5,z6]),(0,[z0,z4,z7,z5,z846,z6])],[(0,[z0,z1,z4,z847,z5,z6]),(0,[z0,z294,z4,z7,z5,z80]),(0,[z112,z0,z1,z7,z265,z209])],[(0,[z0,z1,z848,z7,z5,z6])],[(0,[z0,z1,z4,z7,z849,z6]),(0,[z171,z1,z4,z7,z5,z6]),(0,[z0,z1,z128,z315,z5,z6]),(0,[z99,z1,z4,z7,z5,z41]),(0,[z0,z1,z4,z7,z5,z850]),(0,[z0,z1,z851,z7,z5,z6]),(0,[z852,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z5,z6,z853]),(0,[z0,z7,z5,z451,z455,z6])],[(0,[z300,z43,z1,z4,z197,z5]),(0,[z452,z0,z4,z125,z5,z6])],[(0,[z127,z4,z7,z5,z6,z534]),(0,[z481,z0,z1,z66,z7,z6]),(0,[z656,z1,z4,z197,z5,z6]),(0,[z854,z0,z1,z4,z5,z6])]],
   [[(0,[z855,z1,z4,z7,z5,z6]),(0,[z0,z140,z210,z7,z141,z6])],[(0,[z119,z14,z0,z4,z7,z5]),(0,[z0,z1,z4,z7,z856,z6]),(0,[z0,z857,z4,z7,z5,z6]),(1,[z0,z4,z774,z5,z6]),(0,[z0,z858,z408,z7,z5,z6])],[(0,[z0,z1,z4,z859,z5,z6]),(0,[z0,z1,z355,z32,z5,z6])],[(0,[z0,z1,z4,z7,z5,z860]),(0,[z0,z1,z4,z114,z5,z33])],[(0,[z0,z1,z4,z861,z5,z6])],[(0,[z11,z0,z4,z7,z5,z202]),(0,[z0,z1,z4,z7,z5,z862]),(0,[z0,z20,z1,z159,z5,z6]),(0,[z0,z1,z4,z7,z863,z6])],[(0,[z0,z1,z159,z225,z5,z6]),(0,[z864,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z865]),(0,[z0,z1,z4,z7,z5,z866]),(0,[z37,z171,z1,z7,z6,z185])],[(0,[z0,z170,z29,z32,z5,z6])]],
   [[(0,[z405,z426,z4,z7,z5,z6]),(0,[z0,z1,z408,z262,z5,z6])],[(0,[z17,z1,z128,z7,z5,z6]),(0,[z0,z867,z1,z4,z5,z6]),(0,[z868,z0,z4,z7,z5,z6]),(0,[z453,z1,z81,z7,z5,z82])],[(0,[z300,z0,z4,z7,z313,z5]),(0,[z431,z0,z7,z5,z451,z6])],[(0,[z0,z422,z7,z5,z146,z6]),(1,[z756,z4,z7,z5,z6]),(0,[z97,z1,z4,z5,z6,z413]),(0,[z0,z869,z4,z7,z5,z6]),(0,[z0,z398,z4,z7,z5,z6]),(0,[z37,z0,z1,z7,z6,z155])],[(0,[z0,z1,z4,z870,z7,z5]),(0,[z0,z1,z4,z7,z265,z209])],[(0,[z481,z98,z1,z4,z7,z6]),(1,[z1,z4,z7,z6,z825]),(0,[z0,z1,z4,z7,z5,z871]),(0,[z0,z1,z4,z162,z322,z6]),(0,[z1,z4,z7,z265,z79,z209])],[(0,[z0,z1,z4,z7,z872,z6])],[(0,[z0,z1,z4,z873,z5,z6]),(0,[z0,z1,z408,z7,z5,z6]),(0,[z1,z81,z331,z7,z5,z82])]],
   [[(0,[z0,z1,z874,z7,z5,z6]),(0,[z0,z4,z7,z141,z253,z6])],[(0,[z14,z419,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z875,z6]),(0,[z11,z0,z4,z7,z5,z238])],[(0,[z351,z99,z0,z4,z7,z5]),(0,[z0,z1,z4,z876,z5,z6]),(0,[z877,z0,z1,z7,z5,z6])],[(0,[z37,z0,z1,z7,z187,z6]),(0,[z878,z0,z4,z7,z5,z6]),(0,[z0,z4,z879,z7,z5,z6]),(1,[z0,z1,z880,z5,z6])],[(0,[z1,z756,z4,z7,z5,z6]),(0,[z300,z0,z1,z4,z7,z5]),(0,[z0,z1,z881,z7,z5,z6]),(0,[z0,z882,z4,z7,z5,z6])],[(0,[z0,z883,z4,z7,z5,z6]),(0,[z98,z1,z4,z7,z5,z562]),(0,[z0,z134,z66,z7,z5,z6]),(0,[z0,z1,z4,z884,z5,z6]),(0,[z0,z885,z4,z7,z5,z6]),(0,[z0,z1,z4,z5,z255,z6])],[(0,[z0,z4,z212,z109,z5,z6]),(0,[z0,z1,z477,z125,z5,z6])],[(0,[z0,z1,z4,z5,z6,z886]),(0,[z300,z43,z0,z1,z4,z5]),(0,[z249,z0,z715,z7,z5,z6]),(0,[z887,z1,z4,z7,z5,z6]),(0,[z405,z1,z7,z125,z5,z6]),(0,[z0,z1,z162,z136,z322,z6])]],
   [[(0,[z0,z888,z4,z7,z5,z6]),(0,[z481,z1,z4,z7,z6,z30]),(0,[z0,z889,z4,z7,z5,z6]),(0,[z335,z0,z1,z125,z5,z6])],[(0,[z1,z4,z7,z6,z825,z30]),(0,[z0,z1,z4,z7,z6,z752]),(0,[z0,z4,z7,z890,z5,z6]),(0,[z0,z891,z4,z7,z5,z6])],[(0,[z0,z1,z4,z256,z5,z6]),(0,[z1,z4,z7,z5,z6,z825]),(0,[z0,z892,z4,z7,z5,z6]),(0,[z83,z290,z1,z4,z5,z6])],[(0,[z0,z893,z4,z7,z5,z6]),(0,[z276,z0,z1,z4,z464,z6])],[(0,[z0,z1,z7,z5,z6,z894]),(0,[z37,z0,z428,z7,z5,z6]),(0,[z895,z0,z1,z4,z7,z6]),(0,[z0,z426,z4,z7,z5,z6]),(0,[z736,z0,z1,z4,z7,z5])],[(0,[z896,z0,z4,z7,z5,z6]),(0,[z471,z405,z1,z7,z5,z6]),(0,[z351,z113,z0,z4,z5,z6]),(0,[z0,z4,z7,z5,z6,z752]),(0,[z0,z897,z4,z7,z5,z6])],[],[(0,[z149,z0,z4,z38,z5,z6]),(0,[z98,z1,z4,z7,z5,z587]),(0,[z471,z110,z0,z1,z7,z6]),(0,[z0,z1,z898,z7,z5,z6]),(0,[z405,z1,z38,z7,z5,z6])]],
   [[(0,[z37,z308,z0,z1,z7,z6]),(0,[z0,z1,z4,z7,z5,z899]),(0,[z43,z1,z4,z18,z197,z5]),(0,[z11,z0,z4,z7,z5,z758]),(0,[z0,z900,z4,z7,z5,z6]),(0,[z0,z901,z4,z7,z5,z6])],[(0,[z0,z422,z212,z7,z5,z6]),(0,[z0,z1,z4,z7,z902,z6]),(0,[z0,z20,z4,z212,z5,z6]),(0,[z124,z0,z1,z125,z5,z6])],[(0,[z17,z1,z96,z128,z7,z6]),(0,[z0,z903,z4,z7,z5,z6]),(0,[z0,z4,z7,z774,z5,z6])],[(0,[z904,z0,z1,z4,z7,z5]),(0,[z0,z428,z325,z7,z5,z6]),(0,[z0,z428,z7,z23,z5,z6]),(0,[z0,z1,z905,z7,z5,z6]),(0,[z122,z0,z4,z463,z5,z6]),(0,[z446,z0,z4,z123,z5,z6])],[(0,[z14,z149,z3,z4,z5,z6]),(0,[z471,z62,z1,z7,z5,z6]),(0,[z906,z0,z1,z7,z5,z6]),(0,[z98,z370,z1,z4,z7,z5])],[(0,[z0,z294,z611,z7,z5,z6])],[(0,[z0,z1,z7,z5,z6,z907]),(0,[z0,z1,z4,z908,z5,z6]),(0,[z405,z1,z66,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z909])],[(0,[z0,z1,z4,z910,z5,z6]),(0,[z0,z911,z4,z7,z5,z6]),(0,[z0,z912,z4,z7,z5,z6]),(0,[z0,z460,z4,z7,z5,z6]),(0,[z0,z1,z81,z528,z5,z82]),(0,[z0,z1,z4,z5,z6,z790])]],
   [[(0,[z0,z913,z4,z7,z5,z6]),(0,[z405,z1,z4,z7,z5,z80]),(0,[z0,z914,z4,z7,z5,z6])],[(0,[z0,z1,z4,z915,z5,z6]),(0,[z37,z0,z1,z663,z7,z6]),(0,[z916,z1,z4,z7,z5,z6])],[(0,[z0,z1,z422,z165,z5,z6]),(0,[z481,z17,z0,z1,z7,z6]),(0,[z0,z1,z4,z801,z5,z6]),(0,[z0,z1,z4,z7,z5,z917]),(0,[z453,z1,z4,z386,z5,z6])],[(0,[z0,z1,z4,z7,z918,z6]),(0,[z0,z1,z315,z23,z5,z6]),(0,[z112,z0,z1,z7,z5,z80]),(0,[z0,z1,z7,z23,z6,z712])],[(0,[z0,z3,z422,z7,z5,z6]),(0,[z919,z0,z1,z4,z7,z6]),(0,[z0,z1,z7,z5,z6,z198]),(0,[z26,z1,z4,z7,z6,z30]),(0,[z0,z1,z4,z920,z5,z6]),(0,[z453,z469,z4,z7,z5,z6]),(0,[z1,z4,z7,z5,z6,z921])],[(0,[z300,z452,z0,z4,z7,z5]),(0,[z0,z1,z7,z5,z82,z80]),(0,[z4,z331,z9,z7,z5,z6]),(0,[z922,z0,z1,z7,z5,z6]),(0,[z923,z0,z4,z7,z5,z6])],[(0,[z924,z0,z1,z4,z7,z5]),(0,[z0,z1,z4,z925,z7,z6]),(0,[z0,z1,z4,z5,z6,z926]),(0,[z70,z508,z0,z1,z4,z5]),(0,[z0,z611,z38,z7,z5,z6]),(0,[z927,z1,z4,z7,z5,z6]),(0,[z0,z1,z611,z928,z5,z6]),(0,[z11,z168,z0,z4,z7,z5])],[(0,[z0,z1,z4,z929,z5,z6]),(0,[z0,z1,z4,z930,z5,z6]),(0,[z0,z398,z170,z32,z5,z6]),(0,[z37,z0,z1,z7,z80,z185]),(0,[z0,z1,z4,z162,z6,z790])]],
   [[(0,[z0,z200,z422,z7,z5,z6]),(0,[z931,z0,z1,z4,z7,z5]),(0,[z0,z1,z325,z233,z5,z6]),(0,[z43,z1,z4,z197,z5,z6]),(0,[z1,z4,z7,z63,z6,z449]),(0,[z0,z294,z4,z262,z5,z6])],[(0,[z0,z1,z932,z7,z5,z6]),(0,[z17,z405,z1,z7,z5,z6]),(0,[z0,z1,z210,z7,z5,z6])],[(0,[z0,z4,z7,z5,z6,z933]),(0,[z934,z0,z1,z4,z7,z5]),(0,[z0,z4,z78,z5,z33,z6]),(0,[z1,z4,z5,z255,z6,z79]),(0,[z290,z112,z0,z1,z5,z6])],[(0,[z935,z0,z4,z7,z5,z6]),(0,[z0,z398,z4,z32,z5,z6]),(0,[z171,z1,z4,z174,z5,z6])],[(0,[z149,z0,z134,z4,z5,z6]),(0,[z0,z4,z7,z5,z6,z936]),(0,[z0,z937,z4,z7,z5,z6]),(0,[z0,z4,z7,z6,z752,z359])],[(0,[z626,z1,z128,z7,z5,z6])],[],[(0,[z0,z4,z139,z7,z5,z146])]],
   [[(0,[z572,z0,z38,z7,z5,z6]),(0,[z1,z4,z807,z7,z5,z6]),(0,[z0,z1,z4,z938,z5,z6]),(0,[z0,z1,z939,z7,z5,z6])],[(0,[z0,z1,z940,z7,z5,z6]),(0,[z736,z0,z1,z4,z7,z6])],[(0,[z17,z104,z128,z7,z5,z6]),(0,[z0,z941,z4,z7,z5,z6]),(0,[z26,z1,z4,z7,z93,z6]),(0,[z0,z1,z22,z105,z7,z6]),(0,[z37,z148,z0,z1,z7,z6]),(0,[z0,z4,z942,z7,z5,z6]),(0,[z1,z7,z5,z451,z6,z79])],[(0,[z0,z1,z4,z943,z5,z6]),(0,[z0,z1,z944,z7,z5,z6]),(0,[z0,z428,z4,z7,z5,z6]),(0,[z122,z0,z182,z4,z5,z6]),(0,[z0,z945,z4,z7,z5,z6]),(0,[z0,z4,z7,z946,z5,z6]),(0,[z0,z1,z4,z7,z5,z947]),(0,[z948,z1,z4,z7,z5,z6]),(0,[z1,z4,z7,z5,z6,z949]),(0,[z0,z1,z4,z322,z217,z6])],[(0,[z0,z1,z422,z7,z5,z6]),(0,[z0,z950,z4,z7,z5,z6]),(0,[z99,z0,z1,z4,z142,z5]),(0,[z0,z1,z4,z7,z5,z80])],[(0,[z0,z1,z4,z5,z951,z6]),(0,[z0,z1,z4,z7,z661,z209]),(0,[z0,z1,z4,z5,z33,z769])],[(0,[z0,z1,z4,z952,z5,z6]),(0,[z0,z953,z4,z7,z5,z6]),(0,[z0,z1,z4,z201,z5,z33]),(0,[z83,z112,z1,z7,z5,z6])],[(0,[z119,z0,z4,z7,z123,z5]),(0,[z0,z1,z4,z954,z5,z6]),(0,[z0,z1,z4,z7,z955,z6]),(0,[z300,z0,z1,z4,z125,z5])]],
   [[(0,[z0,z1,z4,z956,z5,z6]),(0,[z0,z1,z957,z7,z5,z6]),(0,[z0,z4,z7,z958,z5,z6]),(0,[z959,z1,z4,z7,z5,z6])],[(0,[z0,z134,z611,z7,z5,z6]),(0,[z37,z0,z1,z7,z6,z185]),(0,[z960,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z265,z255,z209])],[(0,[z0,z1,z4,z7,z5,z961]),(0,[z0,z1,z4,z5,z962,z6]),(0,[z469,z4,z331,z7,z5,z6])],[(0,[z0,z963,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z6,z712]),(0,[z0,z1,z4,z201,z5,z769])],[(1,[z0,z4,z7,z5,z758])],[(0,[z0,z1,z4,z964,z5,z6]),(0,[z161,z0,z4,z7,z6,z359]),(0,[z453,z4,z9,z7,z5,z6])],[(0,[z14,z3,z4,z165,z5,z6]),(0,[z0,z1,z4,z7,z5,z965]),(0,[z0,z4,z7,z5,z966,z6])],[(0,[z0,z1,z967,z7,z5,z6]),(0,[z440,z0,z1,z125,z5,z6]),(0,[z43,z419,z1,z4,z5,z6]),(0,[z0,z1,z4,z262,z5,z58]),(0,[z0,z469,z4,z386,z5,z6]),(0,[z83,z431,z4,z7,z5,z6]),(0,[z112,z0,z1,z5,z255,z6])]],
   [[(0,[z14,z2,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z968]),(0,[z0,z1,z4,z233,z5,z6]),(0,[z969,z0,z1,z4,z5,z6]),(0,[z300,z0,z1,z4,z123,z5]),(0,[z1,z4,z7,z5,z41,z502])],[(0,[z0,z1,z4,z970,z5,z6]),(0,[z0,z1,z4,z971,z5,z6]),(0,[z0,z20,z4,z774,z5,z6]),(0,[z70,z0,z1,z4,z5,z84]),(0,[z124,z0,z1,z880,z5,z6])],[(0,[z0,z1,z4,z972,z5,z6]),(0,[z0,z469,z4,z528,z5,z6])],[(0,[z0,z104,z4,z256,z5,z6]),(0,[z0,z128,z29,z7,z5,z6]),(0,[z0,z1,z4,z7,z6,z973]),(0,[z0,z974,z4,z7,z5,z6]),(1,[z1,z4,z797,z5,z6]),(0,[z0,z20,z383,z4,z5,z6])],[(0,[z14,z756,z4,z7,z5,z6]),(0,[z149,z127,z0,z4,z5,z6]),(0,[z0,z4,z38,z346,z5,z6]),(0,[z0,z1,z4,z975,z5,z6])],[(0,[z0,z1,z4,z5,z33,z352])],[(0,[z14,z3,z15,z7,z5,z6]),(0,[z119,z0,z1,z4,z7,z5]),(0,[z1,z4,z7,z5,z6,z788]),(0,[z976,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z977,z5,z6]),(0,[z0,z4,z978,z7,z5,z6]),(0,[z290,z0,z4,z5,z455,z6])],[(0,[z0,z979,z4,z7,z5,z6]),(0,[z0,z325,z29,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z980]),(0,[z0,z981,z4,z7,z5,z6]),(0,[z0,z134,z66,z346,z5,z6]),(0,[z0,z1,z4,z7,z5,z982])]],
   [[(0,[z0,z983,z4,z7,z5,z6]),(0,[z0,z294,z4,z7,z5,z58]),(0,[z1,z4,z331,z386,z5,z6])],[(0,[z149,z0,z20,z4,z5,z6]),(0,[z0,z4,z7,z984,z5,z6]),(0,[z76,z0,z1,z7,z5,z80]),(0,[z431,z290,z0,z4,z5,z6])],[(0,[z985,z0,z1,z4,z7,z6]),(0,[z0,z1,z4,z774,z5,z6]),(0,[z0,z426,z4,z174,z5,z6]),(0,[z0,z1,z521,z7,z5,z82])],[(0,[z0,z1,z4,z7,z5,z986]),(0,[z11,z0,z628,z4,z7,z5]),(0,[z0,z1,z279,z32,z5,z6]),(0,[z0,z987,z4,z7,z5,z6]),(0,[z37,z0,z29,z7,z5,z6]),(0,[z37,z0,z1,z7,z6,z712]),(0,[z1,z4,z331,z528,z5,z6])],[(0,[z0,z4,z7,z5,z6,z988]),(0,[z0,z1,z989,z7,z5,z6]),(0,[z0,z1,z4,z167,z5,z33]),(0,[z0,z4,z86,z5,z146,z6]),(0,[z0,z4,z7,z5,z6,z990]),(0,[z0,z4,z7,z5,z6,z991])],[(0,[z0,z182,z159,z7,z5,z6]),(0,[z0,z1,z159,z5,z33,z6]),(0,[z0,z1,z4,z992,z5,z6]),(0,[z0,z1,z22,z7,z6,z712])],[(0,[z127,z756,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z993]),(0,[z37,z62,z110,z1,z7,z6]),(0,[z98,z395,z1,z4,z7,z5])],[(0,[z0,z1,z7,z23,z6,z627]),(0,[z0,z120,z159,z7,z5,z6])]],
   [[(0,[z14,z3,z4,z7,z5,z6]),(0,[z37,z0,z1,z233,z5,z6]),(0,[z98,z1,z4,z7,z5,z788])],[(0,[z0,z182,z4,z7,z5,z6]),(0,[z994,z0,z4,z7,z5,z6]),(0,[z98,z113,z0,z1,z4,z5]),(0,[z0,z995,z4,z7,z5,z6])],[(0,[z0,z4,z7,z313,z5,z6]),(0,[z492,z1,z325,z7,z5,z6]),(0,[z300,z97,z0,z1,z4,z5]),(0,[z1,z4,z225,z797,z5,z6]),(0,[z431,z0,z4,z7,z5,z6]),(0,[z0,z996,z4,z7,z5,z6])],[(0,[z0,z120,z4,z7,z5,z6])],[(0,[z997,z0,z1,z4,z7,z5]),(0,[z0,z1,z2,z42,z4,z5]),(0,[z0,z1,z998,z7,z5,z6]),(0,[z26,z1,z7,z6,z198,z30]),(0,[z999,z1,z4,z7,z5,z6]),(0,[z11,z0,z4,z86,z5,z6])],[(0,[z0,z1000,z4,z7,z5,z6]),(0,[z0,z4,z7,z1001,z5,z6]),(0,[z0,z1,z4,z5,z6,z1002]),(0,[z405,z1,z4,z262,z5,z6])],[(0,[z186,z0,z4,z123,z5,z6]),(0,[z1003,z1,z4,z7,z5,z6]),(0,[z0,z140,z4,z7,z6,z752]),(0,[z0,z85,z4,z142,z5,z146]),(0,[z171,z426,z4,z7,z5,z6]),(0,[z1,z4,z1004,z7,z5,z6])],[(0,[z11,z459,z0,z4,z7,z5]),(0,[z0,z293,z38,z7,z5,z6])]],
   [[(0,[z97,z1,z4,z797,z5,z6]),(0,[z471,z0,z1,z1005,z5,z6]),(0,[z0,z1,z4,z201,z530,z5]),(0,[z0,z4,z9,z386,z5,z6])],[(0,[z0,z1,z325,z315,z5,z6]),(1,[z0,z715,z7,z5,z6]),(0,[z0,z20,z4,z630,z5,z6]),(0,[z0,z1,z4,z1006,z5,z6]),(1,[z0,z1,z7,z5,z746])],[(0,[z0,z81,z9,z7,z5,z82]),(0,[z0,z1,z4,z5,z6,z769])],[(0,[z0,z1,z4,z1007,z5,z6]),(0,[z0,z1,z4,z1008,z5,z6]),(0,[z1,z4,z797,z197,z5,z6]),(0,[z0,z4,z9,z528,z5,z6])],[(0,[z0,z1,z4,z1009,z5,z6]),(0,[z0,z1,z1010,z7,z5,z6]),(0,[z0,z1,z7,z5,z6,z746])],[(0,[z0,z1,z4,z1011,z5,z6]),(0,[z453,z1,z4,z7,z5,z6]),(0,[z0,z182,z4,z225,z5,z6]),(0,[z70,z0,z182,z4,z5,z6]),(0,[z596,z1,z4,z225,z5,z6]),(0,[z122,z0,z4,z123,z5,z6])],[(0,[z127,z200,z4,z7,z5,z6]),(0,[z0,z1,z611,z7,z5,z6]),(0,[z405,z294,z4,z7,z5,z6])],[(0,[z0,z1,z4,z1012,z5,z6]),(0,[z452,z97,z0,z4,z5,z6]),(0,[z0,z4,z7,z5,z1013,z6]),(0,[z0,z1,z4,z1014,z5,z6]),(0,[z0,z1,z81,z386,z5,z82]),(0,[z0,z1,z4,z5,z769,z90])]],
   [[(0,[z17,z1,z128,z256,z5,z6]),(0,[z0,z1,z4,z7,z1015,z6]),(0,[z300,z0,z1,z4,z212,z5]),(0,[z98,z1,z4,z7,z5,z57]),(0,[z0,z1,z7,z5,z1016,z6])],[(0,[z0,z1017,z4,z7,z5,z6]),(0,[z0,z469,z81,z7,z5,z82])],[(0,[z0,z1,z605,z32,z5,z6]),(0,[z0,z858,z4,z7,z5,z6])],[(0,[z1,z4,z7,z63,z6,z825]),(0,[z0,z1,z7,z5,z746,z77])],[(0,[z351,z0,z4,z7,z5,z6]),(0,[z0,z66,z715,z7,z5,z6]),(0,[z37,z0,z1,z7,z430,z6]),(0,[z0,z1,z7,z5,z82,z387])],[(0,[z756,z3,z4,z7,z5,z6]),(0,[z501,z200,z4,z7,z5,z6]),(0,[z110,z1,z4,z377,z7,z6]),(0,[z0,z1,z170,z262,z5,z6])],[(0,[z0,z1,z422,z109,z5,z6]),(0,[z0,z1,z4,z7,z5,z1018]),(0,[z0,z1,z1019,z7,z5,z6]),(0,[z0,z306,z1,z125,z5,z6]),(0,[z0,z1020,z4,z7,z5,z6])],[(0,[z122,z0,z4,z109,z5,z6]),(0,[z119,z14,z3,z4,z7,z5]),(0,[z0,z4,z1021,z7,z5,z6]),(0,[z43,z1,z159,z197,z5,z6]),(0,[z1022,z0,z4,z7,z5,z6])]],
   [[(0,[z0,z1,z1023,z7,z5,z6]),(0,[z1024,z0,z1,z7,z5,z6]),(0,[z83,z4,z7,z5,z455,z6])],[(0,[z0,z1,z1025,z7,z5,z6]),(0,[z0,z1,z1026,z7,z5,z6]),(0,[z0,z1,z1027,z7,z5,z6]),(0,[z0,z85,z4,z86,z5,z146]),(0,[z0,z1,z4,z262,z5,z6]),(0,[z0,z1,z4,z5,z1028,z6])],[(0,[z466,z1,z4,z197,z5,z6]),(0,[z0,z1,z4,z174,z5,z80]),(0,[z1,z4,z1029,z7,z5,z6])],[(0,[z0,z1,z4,z7,z5,z1030]),(0,[z0,z1,z257,z7,z5,z6]),(0,[z0,z1,z233,z23,z5,z6]),(0,[z471,z0,z1,z7,z5,z6]),(0,[z349,z145,z0,z1,z4,z7])],[(0,[z0,z4,z7,z5,z6,z1031]),(0,[z1032,z0,z1,z7,z5,z6]),(0,[z0,z1,z7,z1033,z5,z6]),(0,[z110,z1,z4,z7,z6,z825]),(0,[z0,z1,z81,z7,z5,z746]),(0,[z290,z0,z1,z4,z5,z6])],[(0,[z119,z0,z4,z38,z7,z5]),(0,[z0,z1034,z4,z7,z5,z6]),(0,[z431,z112,z0,z7,z5,z6])],[(0,[z0,z20,z4,z614,z5,z6]),(0,[z83,z1,z7,z5,z451,z6])],[(0,[z0,z1,z1035,z7,z5,z6]),(0,[z37,z0,z1,z174,z6,z185]),(0,[z0,z1,z4,z1036,z5,z6])]],
   [[(0,[z11,z0,z4,z109,z5,z6]),(0,[z0,z140,z611,z7,z141,z6])],[(0,[z0,z1,z1037,z7,z5,z6]),(0,[z122,z153,z0,z4,z5,z6]),(0,[z0,z104,z4,z233,z5,z6]),(0,[z481,z0,z1,z7,z125,z6]),(0,[z0,z4,z7,z313,z18,z5]),(0,[z0,z709,z4,z7,z5,z6]),(0,[z0,z1,z4,z315,z5,z6]),(0,[z0,z1,z611,z1038,z5,z6]),(0,[z171,z294,z4,z7,z5,z6])],[(0,[z0,z4,z7,z5,z6,z1039]),(0,[z0,z294,z4,z7,z5,z6]),(0,[z0,z1,z408,z32,z5,z6]),(0,[z0,z1,z22,z7,z23,z6])],[(0,[z119,z0,z1,z2,z4,z5]),(0,[z0,z1,z1040,z7,z5,z6]),(0,[z0,z1,z4,z1041,z5,z6]),(0,[z0,z1,z4,z142,z5,z6]),(0,[z0,z4,z212,z774,z5,z6])],[(0,[z481,z405,z1,z4,z7,z6])],[(0,[z481,z17,z1,z128,z7,z6]),(0,[z405,z1,z4,z7,z5,z58]),(0,[z0,z1,z4,z1042,z5,z6])],[(0,[z62,z1,z807,z7,z5,z6]),(0,[z11,z0,z4,z7,z5,z354]),(0,[z171,z1,z4,z7,z5,z80]),(0,[z0,z1,z4,z1043,z5,z6]),(0,[z112,z1,z7,z5,z6,z79])],[(0,[z452,z0,z4,z7,z5,z6]),(0,[z43,z1,z4,z797,z5,z6])]],
   [[(0,[z0,z1,z170,z213,z5,z6]),(0,[z0,z1,z4,z1044,z5,z6]),(0,[z0,z747,z4,z7,z5,z6]),(0,[z0,z1,z4,z386,z5,z6]),(0,[z4,z7,z5,z455,z6,z79])],[(0,[z0,z1,z4,z7,z5,z1045]),(0,[z576,z0,z38,z7,z5,z6]),(0,[z0,z715,z38,z7,z5,z6]),(0,[z0,z4,z7,z167,z5,z146])],[(0,[z0,z1,z4,z1046,z5,z6]),(0,[z1047,z1,z4,z7,z5,z6]),(0,[z0,z469,z4,z7,z5,z6])],[(0,[z0,z1,z4,z1048,z5,z6]),(0,[z622,z200,z4,z7,z5,z6]),(0,[z83,z1,z4,z7,z5,z6]),(0,[z0,z1,z4,z928,z5,z6]),(0,[z0,z1,z4,z528,z5,z6]),(0,[z70,z0,z1,z4,z5,z281])],[(0,[z0,z1,z4,z7,z5,z1049]),(0,[z0,z1,z7,z1050,z5,z6]),(0,[z0,z1,z4,z1051,z5,z6]),(0,[z0,z1,z7,z5,z1052,z6]),(0,[z70,z0,z4,z78,z5,z6])],[(0,[z14,z370,z4,z7,z5,z6]),(0,[z1053,z1,z4,z7,z5,z6]),(0,[z0,z204,z38,z7,z5,z6]),(0,[z0,z4,z123,z5,z316,z6])],[(0,[z0,z1,z4,z1054,z5,z6]),(0,[z0,z1,z4,z7,z5,z1055]),(0,[z1056,z0,z1,z7,z5,z6]),(0,[z0,z1,z4,z5,z33,z644]),(0,[z1057,z0,z1,z4,z5,z6]),(0,[z113,z0,z4,z5,z6,z396])],[(0,[z0,z4,z212,z302,z5,z6])]],
   [[(0,[z481,z62,z0,z1,z7,z6]),(0,[z0,z1058,z4,z7,z5,z6]),(0,[z0,z1,z1059,z7,z5,z6]),(0,[z0,z1060,z4,z7,z5,z6]),(0,[z0,z1,z7,z5,z1061,z6])],[(0,[z0,z1,z4,z7,z5,z1062]),(0,[z17,z428,z128,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z788]),(0,[z37,z0,z1,z315,z5,z6]),(0,[z1063,z0,z1,z4,z5,z6]),(0,[z0,z29,z7,z23,z5,z6]),(0,[z431,z4,z7,z5,z6,z79])],[(0,[z14,z3,z4,z109,z5,z6]),(0,[z328,z0,z4,z7,z6,z359]),(0,[z0,z1,z4,z1064,z5,z6]),(0,[z0,z1,z4,z1065,z5,z6]),(0,[z1066,z0,z1,z4,z5,z6]),(0,[z0,z398,z4,z125,z5,z6])],[(0,[z1,z4,z331,z7,z5,z6]),(0,[z97,z1,z4,z225,z5,z6]),(0,[z0,z1,z4,z1038,z5,z6]),(0,[z0,z1,z4,z5,z6,z1067])],[(0,[z1068,z0,z4,z7,z5,z6]),(0,[z0,z1,z159,z197,z5,z6]),(0,[z0,z419,z4,z123,z5,z6]),(0,[z0,z1,z67,z125,z5,z6])],[(0,[z0,z1,z1069,z7,z5,z6]),(0,[z0,z1,z7,z5,z6,z1070]),(0,[z0,z134,z715,z7,z5,z6])],[(0,[z0,z1,z4,z5,z6,z1071]),(0,[z0,z1,z4,z7,z5,z1072]),(0,[z0,z1,z4,z1073,z5,z6]),(0,[z0,z134,z609,z7,z5,z6]),(0,[z0,z1,z408,z125,z5,z6])],[(0,[z300,z0,z1,z4,z32,z5])]],
   [[(0,[z122,z0,z1,z159,z5,z6]),(0,[z26,z405,z1,z4,z7,z6]),(0,[z466,z122,z0,z4,z5,z6]),(0,[z161,z0,z4,z7,z6,z752]),(0,[z171,z1,z4,z7,z5,z58])],[(0,[z0,z4,z715,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z58]),(0,[z0,z1,z1074,z7,z5,z6]),(0,[z0,z1,z7,z1075,z5,z6])],[(0,[z14,z42,z3,z4,z7,z5]),(0,[z1076,z0,z1,z4,z5,z6]),(0,[z0,z1077,z4,z7,z5,z6]),(0,[z0,z1,z1078,z7,z5,z6]),(0,[z645,z1,z4,z225,z5,z6]),(0,[z98,z4,z7,z5,z396,z57]),(0,[z0,z1,z32,z880,z5,z6])],[(0,[z0,z1,z42,z4,z7,z5]),(1,[z1,z807,z7,z5,z6]),(0,[z0,z1,z4,z7,z1079,z6]),(0,[z0,z4,z7,z1080,z5,z6]),(0,[z1081,z0,z4,z7,z5,z6]),(0,[z0,z1082,z4,z7,z5,z6])],[],[(0,[z62,z1,z7,z5,z6,z702]),(0,[z0,z4,z7,z5,z6,z1083]),(0,[z98,z351,z4,z7,z5,z57]),(0,[z0,z1084,z1,z4,z7,z5]),(0,[z161,z0,z4,z7,z443,z6]),(0,[z0,z4,z7,z141,z6,z752]),(0,[z0,z1,z4,z7,z5,z758]),(0,[z1085,z0,z4,z7,z5,z6])],[(0,[z17,z1,z128,z233,z5,z6]),(0,[z99,z1,z4,z7,z564,z5]),(0,[z0,z1,z7,z880,z5,z6]),(0,[z1086,z1,z4,z7,z5,z6])],[(0,[z1087,z0,z4,z7,z5,z6])]],
   [[(0,[z1088,z0,z1,z4,z5,z6]),(0,[z127,z4,z7,z27,z5,z6]),(0,[z0,z4,z1089,z7,z5,z6]),(0,[z0,z1,z4,z1090,z5,z6]),(0,[z249,z0,z38,z7,z5,z6]),(0,[z736,z0,z1,z4,z7,z265])],[(0,[z0,z1,z4,z7,z5,z1091]),(0,[z1092,z0,z1,z4,z5,z6])],[(0,[z0,z428,z4,z256,z5,z6]),(0,[z0,z4,z7,z5,z6,z1093]),(0,[z0,z1,z1094,z7,z5,z6]),(0,[z0,z1,z1095,z7,z5,z6]),(0,[z0,z1,z4,z1096,z5,z6]),(0,[z147,z0,z38,z7,z5,z6]),(0,[z0,z1,z4,z1097,z5,z6]),(0,[z0,z1,z4,z162,z524,z6]),(0,[z0,z1,z5,z451,z255,z6])],[(0,[z0,z1,z4,z1098,z5,z6]),(0,[z1099,z0,z4,z7,z5,z6]),(0,[z0,z4,z9,z7,z5,z6]),(0,[z1100,z0,z1,z4,z5,z6])],[(0,[z0,z1,z4,z797,z5,z6])],[(0,[z0,z1,z4,z1101,z5,z6]),(0,[z0,z1,z4,z7,z5,z1102]),(0,[z0,z426,z4,z7,z5,z80])],[(0,[z545,z0,z38,z7,z5,z6]),(0,[z481,z110,z1,z4,z7,z6]),(0,[z452,z0,z4,z7,z18,z5]),(0,[z0,z1,z4,z1103,z5,z6]),(0,[z0,z4,z29,z7,z5,z6]),(0,[z1104,z1,z4,z7,z5,z6]),(0,[z0,z85,z4,z7,z5,z146])],[(0,[z0,z1,z15,z165,z5,z6]),(0,[z0,z756,z4,z7,z5,z6]),(0,[z0,z1,z4,z1105,z5,z6]),(0,[z122,z0,z4,z87,z5,z6])]],
   [[(0,[z0,z1,z4,z5,z6,z1106]),(0,[z1,z64,z128,z7,z5,z6]),(0,[z0,z1,z880,z125,z5,z6]),(0,[z70,z606,z0,z1,z4,z5]),(0,[z264,z736,z0,z1,z4,z7])],[(0,[z626,z3,z4,z7,z5,z6]),(0,[z0,z1,z4,z7,z5,z1107]),(0,[z0,z1,z4,z7,z6,z825]),(0,[z0,z4,z774,z123,z5,z6]),(0,[z11,z0,z4,z7,z5,z69]),(0,[z0,z1,z170,z880,z5,z6]),(0,[z0,z1,z7,z5,z82,z746])],[(0,[z119,z127,z0,z4,z7,z5]),(0,[z1,z4,z7,z5,z6,z79]),(0,[z0,z1,z1108,z7,z5,z6]),(0,[z0,z1,z4,z7,z1109,z6]),(0,[z0,z1,z7,z5,z6,z1110]),(0,[z76,z0,z1,z7,z5,z77]),(0,[z0,z1,z81,z7,z5,z82]),(0,[z1111,z0,z1,z7,z5,z6])],[(0,[z1112,z1,z4,z7,z5,z6]),(0,[z405,z1,z170,z7,z5,z6]),(0,[z264,z145,z0,z1,z4,z7])],[(0,[z122,z0,z4,z106,z5,z6]),(0,[z1113,z1,z4,z7,z5,z6]),(0,[z0,z1,z408,z162,z322,z6])],[(0,[z0,z1,z4,z1114,z5,z6]),(0,[z0,z1,z1115,z7,z5,z6]),(0,[z0,z1,z4,z880,z5,z6])],[(0,[z0,z1,z4,z1116,z5,z6]),(0,[z1117,z0,z1,z7,z5,z6]),(0,[z0,z1,z4,z322,z6,z790])],[(0,[z119,z0,z20,z4,z7,z5]),(0,[z149,z0,z1,z42,z4,z5]),(0,[z405,z1,z4,z7,z5,z6]),(0,[z0,z1,z1118,z4,z5,z6]),(0,[z452,z0,z4,z123,z5,z6]),(0,[z1119,z1,z4,z7,z5,z6]),(0,[z0,z1,z1120,z7,z5,z6])]],
   [[(0,[z0,z1,z4,z96,z7,z6]),(0,[z0,z1,z4,z1005,z5,z6]),(0,[z0,z4,z7,z78,z5,z6]),(0,[z0,z1,z7,z1121,z5,z6]),(0,[z0,z4,z7,z5,z455,z6]),(0,[z0,z4,z7,z5,z146,z758]),(0,[z37,z405,z1,z7,z6,z185]),(0,[z1122,z1,z4,z7,z5,z6])],[(0,[z0,z1,z4,z165,z5,z6]),(0,[z0,z4,z7,z5,z6,z396]),(0,[z1123,z0,z4,z7,z5,z6]),(0,[z0,z4,z496,z212,z5,z6]),(0,[z0,z1,z1124,z7,z5,z6]),(0,[z0,z1125,z4,z7,z5,z6]),(0,[z1,z4,z1126,z7,z5,z6]),(0,[z1127,z1,z4,z7,z5,z6])],[(0,[z112,z0,z1,z7,z5,z6]),(1,[z736,z0,z1,z4,z7])],[(0,[z0,z1,z4,z5,z6,z1128]),(0,[z113,z0,z1,z4,z5,z6]),(0,[z0,z1,z4,z1129,z5,z6]),(0,[z0,z1,z7,z5,z6,z712]),(0,[z431,z0,z4,z7,z265,z209])],[(0,[z0,z1,z4,z1130,z5,z6]),(0,[z0,z1,z1131,z7,z5,z6]),(0,[z0,z4,z1132,z7,z5,z6])],[(0,[z0,z1,z1133,z7,z5,z6]),(0,[z0,z1,z2,z4,z5,z6]),(0,[z416,z0,z1,z125,z5,z6]),(0,[z0,z1,z267,z7,z23,z6]),(0,[z0,z4,z516,z123,z5,z6])],[(0,[z1,z807,z128,z7,z5,z6]),(0,[z656,z1,z128,z7,z5,z6]),(0,[z1134,z1,z4,z7,z5,z6]),(0,[z0,z1,z7,z5,z451,z6])],[(0,[z43,z4,z313,z197,z5,z6]),(0,[z0,z1,z1135,z7,z5,z6]),(0,[z0,z1,z4,z5,z6,z1136]),(0,[z113,z99,z0,z1,z4,z5]),(0,[z0,z1,z4,z1137,z5,z6]),(0,[z70,z0,z1,z4,z5,z90])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 545) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 545).take 539) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1084).take 22) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1106)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [545, 539, 22] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 143).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 143).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [143, 113] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_39809

theorem PEqualNP.Outside.L_meta_39809 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3974160512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3974160512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39809.solve