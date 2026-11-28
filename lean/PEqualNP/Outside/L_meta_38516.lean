import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38516

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
  Nat.testBit (4008372970 * 2 ^ 32 + 3941264000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x60000000540150ab#64 ++ 0xffe42738fce3f1ff#64 : BitVec 128),
   (0xba11ca53314cc665#64 ++ 0xfffbdad7335cce67#64 : BitVec 128),
   (0xcc2c14a5c2970b86#64 ++ 0xfdfc1ce7c39f0f87#64 : BitVec 128),
   (0x100ee0f803e00d50#64 ++ 0x1b2fe0f803e00ff8#64 : BitVec 128),
   (0x000f7f0003faa000#64 ++ 0x178fff0003fff000#64 : BitVec 128),
   (0x004fbffea8000000#64 ++ 0x0f5ffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.and, [6, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x000f7f0003faa000 0x178fff0003fff000

def z1 : W := mkw 0x004fbffea8000000 0x0f5ffffffc000000

def z2 : W := mkw 0x104ffffeabe00d50 0x1f7fffffffe00ff8

def z3 : W := mkw 0x60000000540150ab 0xffe42738fce3f1ff

def z4 : W := mkw 0xaa110a03300cc225 0xe4d01a07301cc007

def z5 : W := mkw 0xba11ca53314cc665 0xfffbdad7335cce67

def z6 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1ce7c39f0f87

def z7 : W := mkw 0x0000000000000000 0x0f442738fc000000

def z8 : W := mkw 0x100ee0f803e00d50 0x1b2fe0f803e00ff8

def z9 : W := mkw 0x604fbffefc0150ab 0xfffffffffce3f1ff

def z10 : W := mkw 0xcc611f07e8170286 0xe4d01f07fc1f0007

def z11 : W := mkw 0x00419f56a8000000 0x0f5bdfd7fc000000

def z12 : W := mkw 0x00011f00001aa000 0x04801f00001ff000

def z13 : W := mkw 0x000e600003e00000 0x130fe00003e00000

def z14 : W := mkw 0x100080f800000d50 0x000000c000000e00

def z15 : W := mkw 0xba11cafb314ccf75 0xfffbdaff335ccfff

def z16 : W := mkw 0x004fbffea8000000 0x001bd8c700000000

def z17 : W := mkw 0x1000c05001400440 0x1b2bc0d003400e60

def z18 : W := mkw 0x442c14a4c2930982 0x00040420c0830180

def z19 : W := mkw 0x0000000000000000 0x0704270000000000

def z20 : W := mkw 0x100ea0f800000d50 0x0b2fe0f800000ff8

def z21 : W := mkw 0x600f7f0057fbf0ab 0xffefff38fffff1ff

def z22 : W := mkw 0x0000000000000000 0x1784270000e3f000

def z23 : W := mkw 0xba10805330044665 0xe87000d730000e67

def z24 : W := mkw 0x100ef5f803f22d50 0x1b2fe5f803e33ff8

def z25 : W := mkw 0x0002a05800000000 0x0203e01800000000

def z26 : W := mkw 0x00018a5220000000 0x0f5bdad730000000

def z27 : W := mkw 0xba5fffffb94cc665 0xffffffffff5cce67

def z28 : W := mkw 0x3211ca523148c461 0x0203c2103040c060

def z29 : W := mkw 0x000f3f0000000000 0x070fff0000000000

def z30 : W := mkw 0x004080fea8000000 0x085000fffc000000

def z31 : W := mkw 0x004ffffeabfaa000 0x1fdffffffffff000

def z32 : W := mkw 0xba104001114cc665 0xf0a00000035cce67

def z33 : W := mkw 0xba11ca53314cc665 0xf0bbd8c7035cce67

def z34 : W := mkw 0x000c00a002800900 0x192c00e003800f80

def z35 : W := mkw 0x000f7fa003faa900 0x1fafffe003ffff80

def z36 : W := mkw 0xdc2ef4fdc3f70fd6 0xfffffcffc3ff0fff

def z37 : W := mkw 0xec2c14a5d6975baf 0xfffc3fffffffffff

def z38 : W := mkw 0xfa11ca53714dc6e7 0xffffdef7f3dfcfe7

def z39 : W := mkw 0x2000000014005029 0x020023183c60f078

def z40 : W := mkw 0xba11ca53354cd66d 0xfffbfbdf3f7cfe7f

def z41 : W := mkw 0x0000000000000000 0xfde0000000000007

def z42 : W := mkw 0x8800000100040204 0xfdf818c7031c0e07

def z43 : W := mkw 0x00036b000168a000 0x0203e3000060f000

def z44 : W := mkw 0xcc2000a5c0050b86 0xe87000e7c0000f87

def z45 : W := mkw 0x100080f800000d50 0x082000f800000ff8

def z46 : W := mkw 0x100ee0f803e00d50 0x082bc0f803000ff8

def z47 : W := mkw 0x3213eb523168e461 0x0203e3103060f060

def z48 : W := mkw 0x000ea0f800000000 0x1b2fe0f800e001f8

def z49 : W := mkw 0x1000c05001400440 0x1b2fe0f803e00ff8

def z50 : W := mkw 0x9a11ca53214c8644 0x001bd8c7031c0e00

def z51 : W := mkw 0x000c140002920000 0x00081800031c0000

def z52 : W := mkw 0x604e35acdc0150ab 0xffe42738fce3f1ff

def z53 : W := mkw 0x3211ca523548d469 0x0203e3183c60f078

def z54 : W := mkw 0xfa11ca53754dd6ef 0xffffffffffffffff

def z55 : W := mkw 0x00014a0001488000 0x0203c2000040c000

def z56 : W := mkw 0xcc201405c2970b86 0xf4f01c07c39f0f87

def z57 : W := mkw 0x100ef4fc83e00d50 0x1f7ffcffc3e00ff8

def z58 : W := mkw 0x100ee0f803e00d50 0x000bc0c003000e00

def z59 : W := mkw 0x2000000010004021 0xffe002103040c067

def z60 : W := mkw 0x004e35ac88000000 0x0f442738fc000000

def z61 : W := mkw 0xe8000001540552af 0xfffc3fffffffffff

def z62 : W := mkw 0x004080fea8000000 0x001000c700000000

def z63 : W := mkw 0x0000000000000000 0x1b24203800e001f8

def z64 : W := mkw 0xdc2ef4fdc3f70fd6 0xfdffdce7c39f0f87

def z65 : W := mkw 0x000ffff803faa000 0x1f8ffff803fff000

def z66 : W := mkw 0x000e600003faa000 0x138fe00003fff000

def z67 : W := mkw 0x0000400003faa000 0x1080000003fff000

def z68 : W := mkw 0xcc2f7fa5c3ffab86 0xffffffe7c3ffff87

def z69 : W := mkw 0x1000c05001400440 0x0203c01000400060

def z70 : W := mkw 0x000f7f0003faa000 0x000bd800031c0000

def z71 : W := mkw 0x1000400003e00d50 0x0000000003000e00

def z72 : W := mkw 0xa800000110044225 0xfff81ad7335cce67

def z73 : W := mkw 0x400000004401108a 0xfde42528cca3319f

def z74 : W := mkw 0x00014a0001488000 0x178bda00035cc000

def z75 : W := mkw 0x000e350002b22000 0x0004250000a33000

def z76 : W := mkw 0x004fbffeaab22000 0x0f5ffffffca33000

def z77 : W := mkw 0x880c140102960204 0xfdfc1cc7039f0e07

def z78 : W := mkw 0x9a1fff5323fea644 0x179fffc703fffe00

def z79 : W := mkw 0xba10000110044665 0xe020000000000e67

def z80 : W := mkw 0xba1fff5333fee665 0xffffffd733fffe67

def z81 : W := mkw 0x000c14a480000000 0x0d5c1ce7c0000000

def z82 : W := mkw 0xcc6fbfffea970b86 0xffffffffff9f0f87

def z83 : W := mkw 0xcc20000142970b86 0xf0a00000039f0f87

def z84 : W := mkw 0x100e600003e00d50 0x132fe00003e00ff8

def z85 : W := mkw 0xfa11ca53754dd6ef 0xfffbdaffff5ccfff

def z86 : W := mkw 0x1000400003e00d50 0x1020000003e00ff8

def z87 : W := mkw 0x004fff5a2bfaa000 0x178fff183ffff000

def z88 : W := mkw 0x004fbffea8000000 0x1f7ffffffce001f8

def z89 : W := mkw 0xba11ca53314cc665 0xe4dbdac7331cce07

def z90 : W := mkw 0x442c14a4c2930982 0x158c1c20c39f0180

def z91 : W := mkw 0x0043ab5a28000000 0x0003c00000000000

def z92 : W := mkw 0x4000000040010082 0xf0a0000000830187

def z93 : W := mkw 0x1002e05803e00d50 0x1223e01803e00ff8

def z94 : W := mkw 0x0043ab5a28000000 0x0203e3183c000000

def z95 : W := mkw 0xba1feafb33eccf75 0xfffffaff33fccfff

def z96 : W := mkw 0x100ee0f803e00d50 0x020be0d803600e78

def z97 : W := mkw 0x8800000100040204 0xf0a00000031c0e07

def z98 : W := mkw 0x000e350000000000 0x0004250000000000

def z99 : W := mkw 0x60000000540150ab 0xf7c42700fce3f007

def z100 : W := mkw 0x000c140002920000 0x158c1c00039f0000

def z101 : W := mkw 0x404e35accc01108a 0x00042528cca33198

def z102 : W := mkw 0xba1080fb30044f75 0xe87000ff30000fff

def z103 : W := mkw 0xee3d1ea7f29fcba7 0xfdfc1ee7f39fcf87

def z104 : W := mkw 0x00010a0220000000 0x04501a0730000000

def z105 : W := mkw 0x104ffffeabe00d50 0x1b3ff8ff03e00ff8

def z106 : W := mkw 0x00014a0001488000 0x178fff0003fff000

def z107 : W := mkw 0x100ffff803faad50 0x1faffff803fffff8

def z108 : W := mkw 0x700ee0f857e15dfb 0xffefe7f8ffe3ffff

def z109 : W := mkw 0x0000140000120000 0x04801c00001f0000

def z110 : W := mkw 0x000f7fa483faa000 0x1fdfffe7c3fff000

def z111 : W := mkw 0x000e20a802a00910 0x0004202800a00198

def z112 : W := mkw 0x400000004401108a 0x00042528cca33198

def z113 : W := mkw 0x500ee0f843e10dd2 0xffefe4f8c3e30fff

def z114 : W := mkw 0x321feafa33e8cd71 0x1b2fe2f833e0cff8

def z115 : W := mkw 0x6043ab5a7c0150ab 0xffe7e738fce3f1ff

def z116 : W := mkw 0x0043abfea8000000 0x0a53e3fffc000000

def z117 : W := mkw 0x100feafa23e00d50 0x1f7ffaff33e00ff8

def z118 : W := mkw 0xba11ca53314cc665 0xf2a3c210335cce67

def z119 : W := mkw 0xba104001114cc665 0xfdf818c7035cce67

def z120 : W := mkw 0x2000000010004021 0xe860001030000067

def z121 : W := mkw 0x60000000540150ab 0xe8600038fc0001ff

def z122 : W := mkw 0xaa100001100cc225 0xe0800000001cc007

def z123 : W := mkw 0xcc2c14a5c6971b8e 0xfdfc3defcfbf3f9f

def z124 : W := mkw 0x0000000000000000 0x15881800031c0000

def z125 : W := mkw 0xcc2c00a5c2850b86 0xf97c00e7c3800f87

def z126 : W := mkw 0x000c14a480000000 0x001818c700000000

def z127 : W := mkw 0xcc2c14a5c2970b86 0xfffc3cffc3ff0fff

def z128 : W := mkw 0x8c2c14a582960b04 0x001818c7031c0e00

def z129 : W := mkw 0xcc2000a5c2970b86 0xf8f000e7c39f0f87

def z130 : W := mkw 0xcc6d1fa7ea970b86 0xfdfc1fe7ff9f0f87

def z131 : W := mkw 0x000f7f0003faa000 0x1fafff3803fff1f8

def z132 : W := mkw 0xaa110a03300cc225 0xfff01a17305cc067

def z133 : W := mkw 0x8c2c14a582960b04 0x193c18e7039c0f80

def z134 : W := mkw 0x600e20a856a159bb 0xffe42738fce3f1ff

def z135 : W := mkw 0x404fbffee8010082 0xfffffffffc830187

def z136 : W := mkw 0x000e20a802a00910 0x192c20e803a00f98

def z137 : W := mkw 0x100ee0f803faad50 0x1bafe0f803fffff8

def z138 : W := mkw 0xcc2c140142970b86 0xf5ac1c00039f0f87

def z139 : W := mkw 0x60000000540150ab 0xefc42738fc03f007

def z140 : W := mkw 0x000ea0f800000000 0x0b0fe0f800000000

def z141 : W := mkw 0x0000000000000000 0x192800c003000e00

def z142 : W := mkw 0x100ee05803e00450 0x130fe01803e00078

def z143 : W := mkw 0x1001ca5221400440 0x1f7bdad733400e60

def z144 : W := mkw 0x00411f06a8000000 0x04501f07fc000000

def z145 : W := mkw 0x3253eb5a3948c461 0x0203e3183c40c060

def z146 : W := mkw 0x004fbffea8000000 0x045bdfc7fc000000

def z147 : W := mkw 0x000e600003e00000 0x178fe70003e3f000

def z148 : W := mkw 0x042c14a482920900 0x0000000000000000

def z149 : W := mkw 0x004fbffea8000000 0x085bd8fffc000000

def z150 : W := mkw 0x442e35a4c2b32982 0x00042520c0a33180

def z151 : W := mkw 0x321040001148c461 0x000000000040c060

def z152 : W := mkw 0xfe3080f7f0054fe7 0xe87000f7f0000fe7

def z153 : W := mkw 0xfe30400153dfcfe7 0xf0a0000003dfcfe7

def z154 : W := mkw 0x100cc0f003c00d40 0x1b2fc0f003c00fe0

def z155 : W := mkw 0x0000805220000000 0x085000d730000000

def z156 : W := mkw 0xba11ca53314cc665 0xe87bd8d7331c0e67

def z157 : W := mkw 0x000f3f00001aa000 0x078fff00001ff000

def z158 : W := mkw 0x104ef5fc8be00d50 0x1b2fe5f8cfe00ff8

def z159 : W := mkw 0x4000000040010082 0xe4c00400c0030007

def z160 : W := mkw 0x22110a023008c021 0x000002003000c000

def z161 : W := mkw 0x404fbffeec01108a 0x0f5ffffffca33198

def z162 : W := mkw 0x8800000100040204 0xe87000c700000e07

def z163 : W := mkw 0xaa10000330044225 0xe050000730000007

def z164 : W := mkw 0x00014a0001488000 0x000bd800031c0000

def z165 : W := mkw 0x60000000540150ab 0xfde40438fc8301ff

def z166 : W := mkw 0x880c14a580040204 0xfdfc1ce7c31c0e07

def z167 : W := mkw 0x442c14a4c693198a 0x00042528cca33198

def z168 : W := mkw 0xcc2e74a5c3f70b86 0xfffffce7c3ff0f87

def z169 : W := mkw 0x004eb5fea8000000 0x085425fffc000000

def z170 : W := mkw 0xea110a03740dd2af 0xfff43f3ffcfff1ff

def z171 : W := mkw 0x9800c05101440644 0xfffbd8d7035c0e67

def z172 : W := mkw 0x000f7f0003faa000 0x158fdc00039f0000

def z173 : W := mkw 0xcc2d1fa5c29fab86 0xfdfc1fe7c39fff87

def z174 : W := mkw 0xcc2f7fa5c3ffab86 0xfdffdce7c39f0f87

def z175 : W := mkw 0x100ee0f803e00d50 0x1f6fe7f8ffe00ff8

def z176 : W := mkw 0x000f7f0003faa000 0x130ff80003fc0000

def z177 : W := mkw 0x004fbffeaa800900 0x1f7fffffff800f80

def z178 : W := mkw 0xba11ca53314cc665 0xea73c2d73040ce67

def z179 : W := mkw 0xcc20000142970b86 0xfdf818c7039f0f87

def z180 : W := mkw 0xdc2ee0f943f70fd6 0xfbafe0f803ff0fff

def z181 : W := mkw 0x60000000540150ab 0x02042738fce3f1f8

def z182 : W := mkw 0x004e35ac88000000 0x0000000000000000

def z183 : W := mkw 0xcc201405c0170286 0xe4d01c07c01f0007

def z184 : W := mkw 0x321fff5233fae461 0x178fff1033fff060

def z185 : W := mkw 0xba1ee0fb33e44f75 0xfb7fe0ff33e00fff

def z186 : W := mkw 0xec2000a5d4055baf 0xe87000fffc000fff

def z187 : W := mkw 0x004f7f06abfaa000 0x17dfff07fffff000

def z188 : W := mkw 0x0000000000000000 0x1020000000e001f8

def z189 : W := mkw 0x442e34acc2b30992 0x00042428c0a30198

def z190 : W := mkw 0x60411f06fc0150ab 0xfff43f3ffce3f1ff

def z191 : W := mkw 0x60000000540150ab 0xf0a0000000e3f1ff

def z192 : W := mkw 0xba5fffffb94cc665 0xfffbdad7335cce67

def z193 : W := mkw 0x000e600003e00000 0x000bc00003000000

def z194 : W := mkw 0x000e20a802a00910 0x0000000000000000

def z195 : W := mkw 0x00011f0000000000 0x04001f0000000000

def z196 : W := mkw 0xcc2c00a142970b86 0xf9ac00e0039f0f87

def z197 : W := mkw 0x004e35ac88000000 0x00042528cc000000

def z198 : W := mkw 0x3211ca523148c461 0x0f5bdad73040c060

def z199 : W := mkw 0x000f7f0003faa000 0x000ffd0003bf3000

def z200 : W := mkw 0xfe3ddef7f7dfdfef 0xffffffffffffffff

def z201 : W := mkw 0x004f7fac8bfaa000 0x178fff28cffff000

def z202 : W := mkw 0x3213ea5a3168c471 0x0203e2183060c078

def z203 : W := mkw 0xfe3ddef7f3dfcfe7 0xffffdef7f3dfcfe7

def z204 : W := mkw 0xba118a53300cc665 0xecf01ad7301cce67

def z205 : W := mkw 0x9a10805320040644 0x001000c700000e00

def z206 : W := mkw 0x300ee0f817e05d79 0x1b2fe3f83fe0fff8

def z207 : W := mkw 0x00010a0000000000 0x070bda0000000000

def z208 : W := mkw 0x00418afea8000000 0x0f5bdafffc000000

def z209 : W := mkw 0x000f7f0003faa000 0x048bdf00031ff000

def z210 : W := mkw 0x00010a0000088000 0x04801a00001cc000

def z211 : W := mkw 0x000f7f0001488000 0x178fff00035cc000

def z212 : W := mkw 0x100ffff803faad50 0x000bd8c0031c0e00

def z213 : W := mkw 0xaa111f03301ee225 0xe4d01f07301ff007

def z214 : W := mkw 0x1000c0f801400d50 0x1b2bc0f803400ff8

def z215 : W := mkw 0x100fff5803faa450 0x178fff1803fff078

def z216 : W := mkw 0x000080f800000000 0x080000f800000000

def z217 : W := mkw 0x1000805000000440 0x082000d000000e60

def z218 : W := mkw 0x000000a800000910 0x0000002800000198

def z219 : W := mkw 0x004fbffeaa920000 0x1fdfffffff9f0000

def z220 : W := mkw 0x100c80f802800d50 0x192c00f803800ff8

def z221 : W := mkw 0xcc6fbfffe8170286 0xefdffffffc1f0007

def z222 : W := mkw 0x4000000040010082 0xfde40420c0830187

def z223 : W := mkw 0x8c2f7fa583feab04 0x179fffc703fffe00

def z224 : W := mkw 0x004ea0fea8000000 0x0b5fe0fffc000000

def z225 : W := mkw 0xaa511f07b80cc225 0xe4d01f07fc1cc007

def z226 : W := mkw 0xcc2c14a5c2970b86 0xe4d81cc7c31f0e07

def z227 : W := mkw 0x0043bf5ea8000000 0x0653ff1ffc000000

def z228 : W := mkw 0x0000000000000000 0x0000000000000000

def z229 : W := mkw 0xcc2f3fa5c2970b86 0xffffffe7c39f0f87

def z230 : W := mkw 0x104080fea8000d50 0x087000fffc000ff8

def z231 : W := mkw 0x880f7f0103fea204 0xffffffc703fffe07

def z232 : W := mkw 0x004fbffea8000000 0x071fffc700000000

def z233 : W := mkw 0x104ffffea9600450 0x0f5ffffffc600078

def z234 : W := mkw 0x3211ca523148c461 0x1b2bc2d03340ce60

def z235 : W := mkw 0x3210805230004461 0x0000001030000060

def z236 : W := mkw 0x00018a5220000000 0x0203c21030000000

def z237 : W := mkw 0x100ffff803faad50 0x1b2ff8f803fc0ff8

def z238 : W := mkw 0xfe31ca5373dfcfe7 0xfffbdad733dfcfe7

def z239 : W := mkw 0x600e600057e150ab 0xffefe738ffe3f1ff

def z240 : W := mkw 0x0002600001600000 0x0203e00000600000

def z241 : W := mkw 0x60011f00541bf0ab 0xffe43f38fcfff1ff

def z242 : W := mkw 0x0000000004001008 0x000021080c203018

def z243 : W := mkw 0xcc211f05c01fa286 0xe4d01f07c01ff007

def z244 : W := mkw 0x000f7f0003faa000 0x070fff00031c0000

def z245 : W := mkw 0x0042210808000000 0x000021080c000000

def z246 : W := mkw 0x000f3f0002920000 0x178fff00039f0000

def z247 : W := mkw 0x2000000014005029 0x000003003c00f000

def z248 : W := mkw 0x100ee0f803e00d50 0x0b0fe0f803000e00

def z249 : W := mkw 0xfa108053740556ef 0xe87000fffc000fff

def z250 : W := mkw 0x604fbffefc0150ab 0xef7ffffffc0001ff

def z251 : W := mkw 0x0000805000000000 0x0b0bc0d000000000

def z252 : W := mkw 0x2043ab5a3c005029 0x0203e3183c60f078

def z253 : W := mkw 0x446e35acca930982 0x00042528cc830180

def z254 : W := mkw 0x60000000540150ab 0xfba4203800e3f1ff

def z255 : W := mkw 0x100ee0f803e00d50 0x102bc0c003e00ff8

def z256 : W := mkw 0xec6fbffffe975baf 0xffffffffffffffff

def z257 : W := mkw 0xec2c14a5d2974ba7 0xfffc1ef7f3dfcfe7

def z258 : W := mkw 0x100ee0f803e00d50 0x192fc0e003800f80

def z259 : W := mkw 0x0001ca5221488000 0x1fdbdad7335cc000

def z260 : W := mkw 0x100ee0f803e00d50 0x1fafe7f803e3fff8

def z261 : W := mkw 0x0000000000000000 0x00042528cc000000

def z262 : W := mkw 0x1002e05801600450 0x0203e01800600078

def z263 : W := mkw 0xdc2080fdc0050fd6 0xe87000ffc0000fff

def z264 : W := mkw 0xba1fff5333fee665 0xfffbdad7335cce67

def z265 : W := mkw 0x1000400001400440 0x1020000003400e60

def z266 : W := mkw 0xdc2cd4f5c3d70fc6 0xffffdcf7c3df0fe7

def z267 : W := mkw 0x500ee0f847e11dda 0x1b2fe5f8cfe33ff8

def z268 : W := mkw 0x60000000540150ab 0xe4c00700fc03f007

def z269 : W := mkw 0x000d9ef6a0000000 0x0f5fdef7f0000000

def z270 : W := mkw 0xcc2c14a5c2970b86 0xf0a40420c39f0f87

def z271 : W := mkw 0xba1feafb33eccf75 0xfffbdad7335cce67

def z272 : W := mkw 0x0000000000000000 0x1fa4273800e3f1f8

def z273 : W := mkw 0x880c00a102840b04 0xfdfc18e7039c0f87

def z274 : W := mkw 0x000c140000000000 0x050c1c0000000000

def z275 : W := mkw 0x60000000540150ab 0xef642738fc0001ff

def z276 : W := mkw 0xba11df53315ee665 0xfffbdfd7335ffe67

def z277 : W := mkw 0x00037f00017aa000 0x0683ff00007ff000

def z278 : W := mkw 0x004fbffea8000000 0x0207e738fc000000

def z279 : W := mkw 0x0000150000122000 0x0000050000033000

def z280 : W := mkw 0x300ee0f813e04d71 0xffefe2f833e0cfff

def z281 : W := mkw 0xdc2c54a5c3f70fd6 0xfdfc1ce7c3ff0fff

def z282 : W := mkw 0xcc2c14a5c2970b86 0xe4d41c27c09f0187

def z283 : W := mkw 0x60000000540150ab 0xf2a023183ce3f1ff

def z284 : W := mkw 0x4000000040010082 0xe8600020c0000187

def z285 : W := mkw 0x642c14a4d69359ab 0xffe42738fce3f1ff

def z286 : W := mkw 0xec2000a5d4055baf 0xfff427fffce3ffff

def z287 : W := mkw 0x8c2c14a582960b04 0xfdf818c7031c0e07

def z288 : W := mkw 0x60014a005549d0ab 0xffefff38fffff1ff

def z289 : W := mkw 0xec201405d41752af 0xfff43f3ffcfff1ff

def z290 : W := mkw 0xcc2c14a5c0050b86 0xed7c1ce7c0000f87

def z291 : W := mkw 0xcc2014a5c0170b86 0xecf01ce7c01f0f87

def z292 : W := mkw 0xba114a03314cc665 0xf4f01a07335cce67

def z293 : W := mkw 0x400000004401108a 0x00000500cc033000

def z294 : W := mkw 0x442f7fa4c3fba982 0x178fff20c3fff180

def z295 : W := mkw 0xba51caffb94cc665 0xfffbdaffff5cce67

def z296 : W := mkw 0x004ffffeabfaa000 0x0f5fffffff1c0000

def z297 : W := mkw 0xba11ca53314cc665 0xfffffaff33fccfff

def z298 : W := mkw 0x000e20a800000000 0x0004202800000000

def z299 : W := mkw 0x000f7f0003e00000 0x170fff0003e00000

def z300 : W := mkw 0xba11ca53314cc665 0xffffffffff5cce67

def z301 : W := mkw 0xba1ddef7b14cc665 0xffffdef7f35cce67

def z302 : W := mkw 0x000eb4fc80000000 0x0f5ffcffc0000000

def z303 : W := mkw 0x100ee0f801600450 0x0b0fe0f800600078

def z304 : W := mkw 0x004e35ac88000000 0x0d5c3defcc000000

def z305 : W := mkw 0xcc2c54a5c3ffab86 0xfdfc1ce7c3ffff87

def z306 : W := mkw 0x2000000010004021 0xffe4271030e3f067

def z307 : W := mkw 0xfa5ffffffd4dd6ef 0xffffffffffffffff

def z308 : W := mkw 0x0000000000000000 0x08200038000001f8

def z309 : W := mkw 0x00014a0003faa000 0x178bda0003fff000

def z310 : W := mkw 0x7000400057e15dfb 0xf0a0000003e3ffff

def z311 : W := mkw 0x2000000010004021 0xe4c002003000c007

def z312 : W := mkw 0xcc2f7f05c3ffa286 0xf7dfff07c3fff007

def z313 : W := mkw 0x000c14a480000000 0x0f5c3ffffc000000

def z314 : W := mkw 0x000f7f0003faa000 0x0207e70000e3f000

def z315 : W := mkw 0x400000004401108a 0x1b242538cce331f8

def z316 : W := mkw 0x000c00a002800900 0x1b2c20f803e00ff8

def z317 : W := mkw 0x200f7f0017faf029 0x178fff183ffff078

def z318 : W := mkw 0x400000004401108a 0x00000028cc000198

def z319 : W := mkw 0x8c2000a580040b04 0x001000c700000e00

def z320 : W := mkw 0x0000000000000000 0x1924002000800180

def z321 : W := mkw 0x2000000010004021 0x020002103040c060

def z322 : W := mkw 0xc800000140050286 0xfdfc1ce7c39f0f87

def z323 : W := mkw 0x004fbffea8000000 0x0f5bdad730000000

def z324 : W := mkw 0xba118a5330044665 0xef7bdad730000e67

def z325 : W := mkw 0x000fff5223faa000 0x1fdfffd733fff000

def z326 : W := mkw 0x000e200000000000 0x030fe00000000000

def z327 : W := mkw 0x0000400003faa000 0x1784270003fff000

def z328 : W := mkw 0x2000000010004021 0xffe4223830e0c1ff

def z329 : W := mkw 0x3211ca523148c461 0xffe3c2103040c067

def z330 : W := mkw 0x004fbffea8000000 0x1fdffffffce3f000

def z331 : W := mkw 0x8c2c14a582960b04 0x0d5c1ce7c31c0e00

def z332 : W := mkw 0xcc201405c0170286 0xfdf81cc7c31f0e07

def z333 : W := mkw 0x004eb5fc88000000 0x0b0fe5f8cc000000

def z334 : W := mkw 0x0000400001488000 0x10800000035cc000

def z335 : W := mkw 0xba10805330044665 0xfff002d73040ce67

def z336 : W := mkw 0x1002e0f801600d50 0x0a23e0f800600ff8

def z337 : W := mkw 0x2000000014005029 0x178427183ce3f078

def z338 : W := mkw 0x000e350002b22000 0x158c3d0003bf3000

def z339 : W := mkw 0x100ea0f802a00d50 0x082420f800a00ff8

def z340 : W := mkw 0x20036b001568f029 0x0203e3183c60f078

def z341 : W := mkw 0x004fabfa28000000 0x0b0fe3f83c000000

def z342 : W := mkw 0xfa108053740556ef 0xfff427fffce3ffff

def z343 : W := mkw 0xcc2c14a5c2970b86 0xfffc3fffff9f0f87

def z344 : W := mkw 0x60000000540150ab 0xe0200000000001ff

def z345 : W := mkw 0xaa118a53300cc225 0xefdbdad7301cc007

def z346 : W := mkw 0x8c2c14a582960b04 0x159c1cc7039f0e00

def z347 : W := mkw 0xcc2e35a5c2b72b86 0xfdfc3de7c3bf3f87

def z348 : W := mkw 0x0002210000202000 0x0000210000203000

def z349 : W := mkw 0xba11ca5333eccf75 0xfffbdad733fccfff

def z350 : W := mkw 0x8c6fbfffaa960b04 0x001bd8c7031c0e00

def z351 : W := mkw 0x00010b000008a000 0x000003000000f000

def z352 : W := mkw 0x0000000000000000 0x1f642738fce001f8

def z353 : W := mkw 0x9a5fffffa94c8644 0x001bd8c7031c0e00

def z354 : W := mkw 0xcc2c14a5c2970b86 0xfffc3fe7c3ffff87

def z355 : W := mkw 0xcc6e35adca970b86 0xfdfc3defcf9f0f87

def z356 : W := mkw 0xfc2ef4fdd7f75fff 0xffffffffffffffff

def z357 : W := mkw 0xba11ca5333fee665 0xfffbdad733fffe67

def z358 : W := mkw 0x104febfa2be00d50 0x1b2fe3f83fe00ff8

def z359 : W := mkw 0x00015f00015aa000 0x178bdf00035ff000

def z360 : W := mkw 0x0000000000000000 0x0d5818c700000000

def z361 : W := mkw 0x004e35ac8ab22000 0x00042528cca33000

def z362 : W := mkw 0x0000000002920000 0x10800000039f0000

def z363 : W := mkw 0x442c14a4c2930982 0x0d5c1ce7c0830180

def z364 : W := mkw 0xfa11ca53754dd6ef 0xfffbdfd7ff5ffe67

def z365 : W := mkw 0x004fbffea8000000 0x0d5fdce7c0000000

def z366 : W := mkw 0x6000400057fbf0ab 0xf0a0000003fff1ff

def z367 : W := mkw 0xba11ca53314cc665 0xffffffd733fffe67

def z368 : W := mkw 0x4000000040010082 0xffe42438c0e301ff

def z369 : W := mkw 0x1002e05801600450 0x1b27e03800e001f8

def z370 : W := mkw 0x100e60a803e00d50 0x1024202803e00ff8

def z371 : W := mkw 0x3000c05011404461 0xffebc2d03340ce67

def z372 : W := mkw 0x325ffffeb948c461 0x0f5ffffffc40c060

def z373 : W := mkw 0x004fbffeaaa00910 0x0f5ffffffca00198

def z374 : W := mkw 0x1211ca5221488440 0x0003c00000000000

def z375 : W := mkw 0x700080f854015dfb 0xffe427f8fce3ffff

def z376 : W := mkw 0xcc2c14a5c2970b86 0xe87818e7c31c0f87

def z377 : W := mkw 0x100ffff803faad50 0x178fffc003fffe00

def z378 : W := mkw 0x0043ab5a28000000 0x0f5bfbdf3c000000

def z379 : W := mkw 0x004ffffeabfaa000 0x001bd8c7031c0000

def z380 : W := mkw 0x104ee0feabe00d50 0x1b7fe0ffffe00ff8

def z381 : W := mkw 0xba5fbfffb8044665 0xef7ffffffc000e67

def z382 : W := mkw 0xcc2c14a5c2970b86 0xf0b818c7039f0f87

def z383 : W := mkw 0x8c20140580160204 0x00101807001c0000

def z384 : W := mkw 0xfe31de57f15fc6e7 0xfffbded7f35fce67

def z385 : W := mkw 0x9c2ef4fd83f60f54 0x1b3ff8ff03fc0ff8

def z386 : W := mkw 0x000ea0f802800900 0x1b2fe0f803800f80

def z387 : W := mkw 0x100ee0f801400440 0x1b2fe0f803400e60

def z388 : W := mkw 0x004f3faea8000000 0x04543f2ffc000000

def z389 : W := mkw 0xcc2e34adc2b70b96 0xfdfc3cefc3bf0f9f

def z390 : W := mkw 0x0000140480000000 0x04501c07c0000000

def z391 : W := mkw 0x604080fefc0150ab 0xfff427fffce3f1ff

def z392 : W := mkw 0x442c14a4c2930982 0x192c04e0c3830f80

def z393 : W := mkw 0x004ffffea968a000 0x0f5ffffffc60f000

def z394 : W := mkw 0xba1feafb314cc665 0xfffffaff335cce67

def z395 : W := mkw 0xfe3c54a5d3dfcfe7 0xfdfc1ce7c3dfcfe7

def z396 : W := mkw 0x100ee0f803e00d50 0x0207e03800e001f8

def z397 : W := mkw 0x000f3f0000000000 0x178fff0000e3f000

def z398 : W := mkw 0x000f7f000168a000 0x070fff000060f000

def z399 : W := mkw 0x000e200002a00000 0x0004200000a00000

def z400 : W := mkw 0xfe3ffff7f3ffefe7 0xfffffff7f3ffffe7

def z401 : W := mkw 0x100c40a003e00d50 0x192c00e003e00ff8

def z402 : W := mkw 0x9a1feafb23ec8f54 0x001bd8c7031c0e00

def z403 : W := mkw 0x00419ffea8000000 0x0c501ffffc000000

def z404 : W := mkw 0x000f7f0003faa000 0x1fcfff38fffff000

def z405 : W := mkw 0x60000000540150ab 0xf0a42528cce3f1ff

def z406 : W := mkw 0x104ffffea9400440 0x1f7fffffff400e60

def z407 : W := mkw 0x000e740003f20000 0x178ffc0003ff0000

def z408 : W := mkw 0x1043eb5a29600450 0x0203e3183c600078

def z409 : W := mkw 0xfe7ffffffbdfcfe7 0xffffffffffdfcfe7

def z410 : W := mkw 0x1000c05003e00d50 0x1b2bc0d003e00ff8

def z411 : W := mkw 0x0000000000000000 0x1b20001000400060

def z412 : W := mkw 0x1003eb580168a450 0x0203e3180060f078

def z413 : W := mkw 0x000f3f0000000000 0x0f4fff38fc000000

def z414 : W := mkw 0x000ea0f802a00910 0x0b0fe0f800a00198

def z415 : W := mkw 0xaa5fbfffb80cc225 0xefdffffffc1cc007

def z416 : W := mkw 0x00018a5220000000 0x0f5ffffffc000000

def z417 : W := mkw 0x000d5e0003da8000 0x178fde0003dfc000

def z418 : W := mkw 0xba10c053314cc665 0xf8f000d7335cce67

def z419 : W := mkw 0x004000ac88000000 0x00000028cc000000

def z420 : W := mkw 0x60000000540150ab 0xfde40720fc83f187

def z421 : W := mkw 0x0040805a28000000 0x000000183c000000

def z422 : W := mkw 0xaa114a03314cc225 0xf7dbda07335cc007

def z423 : W := mkw 0xec2f7fa5d7fffbaf 0xffffffffffffffff

def z424 : W := mkw 0x88014a01014c8204 0xfffbdac7035cce07

def z425 : W := mkw 0x0000000000000000 0x0004202800a00198

def z426 : W := mkw 0xfa1feafb77eddfff 0xffffffffffffffff

def z427 : W := mkw 0x000f3f0002b22000 0x070fff0000a33000

def z428 : W := mkw 0x400c140042930082 0xfdec1c20c39f0187

def z429 : W := mkw 0x004ffffeabfaa000 0x179fffc703fff000

def z430 : W := mkw 0x000f3f0002baa000 0x04843f0000bff000

def z431 : W := mkw 0xfe3c94f7f2974fe7 0xfdfc1cf7f39f0fe7

def z432 : W := mkw 0x00036b000168a000 0x178bfb00037cf000

def z433 : W := mkw 0x000e35a802b22910 0x0004252800a33198

def z434 : W := mkw 0x4000000040010082 0xffe42720c0e3f187

def z435 : W := mkw 0x1000c05001400440 0x000bc0c003000e00

def z436 : W := mkw 0x000f3f0000000000 0x000bd80000000000

def z437 : W := mkw 0x100080f800000d50 0x1b2420f800e00ff8

def z438 : W := mkw 0x00015f0003faa000 0x14801f0003fff000

def z439 : W := mkw 0x8c20000102960b04 0x00000000031c0e00

def z440 : W := mkw 0x000faafa20000000 0x0f5ffaff30000000

def z441 : W := mkw 0x004fbffea8000000 0x0b1ff8ff00000000

def z442 : W := mkw 0x100ee0f803e00d50 0x130fe0c003e00e00

def z443 : W := mkw 0x9a104001014c8644 0x00000000031c0e00

def z444 : W := mkw 0x2000000014005029 0x1b2423383ce0f1f8

def z445 : W := mkw 0x3002e05815605479 0x0203e3183c60f078

def z446 : W := mkw 0xfe3ffefff3ffcff7 0xfffffefff3ffcfff

def z447 : W := mkw 0x600f3f00540150ab 0xffefff38fce3f1ff

def z448 : W := mkw 0x000fbff800000000 0x0f0ffff800000000

def z449 : W := mkw 0x000000a000000900 0x082000e000000f80

def z450 : W := mkw 0x9a1fff5323fea644 0x001bd8c7031c0e00

def z451 : W := mkw 0xfa104001554dd6ef 0xffe42738ffffffff

def z452 : W := mkw 0xec2c14a5d6975baf 0xfdfc1cffff9f0fff

def z453 : W := mkw 0xdc2ee0fdc3e50fd6 0xfb7fe0ffc3e00fff

def z454 : W := mkw 0x1001ca5001488440 0x1fabdad0035cce60

def z455 : W := mkw 0x200f7f0013fae021 0xffefff1033fff067

def z456 : W := mkw 0x9a11ca53214c8644 0x179bdac7035cce00

def z457 : W := mkw 0xba1dde5333dec665 0xffffded733dfce67

def z458 : W := mkw 0x400c14a4c0010082 0xfdfc1ce7c0830187

def z459 : W := mkw 0x00000000001aa000 0x00800000001ff000

def z460 : W := mkw 0xcc2d5ea5c3df8b86 0xffffdee7c3dfcf87

def z461 : W := mkw 0x000f3fa480000000 0x0f5fffe7c0000000

def z462 : W := mkw 0xba13eb53316ce665 0xfffbfbd7337cfe67

def z463 : W := mkw 0xba51df57b94cc665 0xfffbdfd7ff5cce67

def z464 : W := mkw 0x7000c050554154eb 0xffefe7f8ffe3ffff

def z465 : W := mkw 0x1000c0f803e00d50 0x182000f803e00ff8

def z466 : W := mkw 0x400000004401108a 0x17842728cce3f198

def z467 : W := mkw 0xdc6fffffebf70fd6 0xffffffffffff0fff

def z468 : W := mkw 0x1000400003e00d50 0x1b24203803e00ff8

def z469 : W := mkw 0x2000000010004021 0xffe42738fc40c067

def z470 : W := mkw 0x980ee0f903e40f54 0xfffff8ff03fc0fff

def z471 : W := mkw 0xbe3ddef7b3decf65 0xfffbdad7335cce67

def z472 : W := mkw 0x100ef4f803f20d50 0x1faffcf803ff0ff8

def z473 : W := mkw 0x88018a5320040204 0xfffbdad7331c0e07

def z474 : W := mkw 0x442c14a4c2930982 0xfde40420c0830187

def z475 : W := mkw 0x0000000002800900 0x1020000003800f80

def z476 : W := mkw 0x2000000014005029 0x0f442738fc60f078

def z477 : W := mkw 0x004e35ac8aa00910 0x00042528cca00198

def z478 : W := mkw 0x000f6a0003e88000 0x178ffa0003fcc000

def z479 : W := mkw 0x0000000000000000 0x1fc42738fce3f000

def z480 : W := mkw 0x700ee0f857e15dfb 0xfbafe0f803e3ffff

def z481 : W := mkw 0x00036b0003faa000 0x1283e30003fff000

def z482 : W := mkw 0x60000000500140a3 0xffe40630f0c3c1e7

def z483 : W := mkw 0x000ee0f803e00000 0x1b0fe0f803e00000

def z484 : W := mkw 0xcc6fffffebffab86 0xffffffffffffff87

def z485 : W := mkw 0x1000805800000450 0x0000001800000078

def z486 : W := mkw 0x000e60a803e00910 0x130fe02803e00198

def z487 : W := mkw 0xcc2000a5c0050b86 0xfdf818e7c31c0f87

def z488 : W := mkw 0x60000000540150ab 0xe6c02718fc63f07f

def z489 : W := mkw 0x60000000540150ab 0xf7a4270000e3f1ff

def z490 : W := mkw 0xba10400113fee665 0xf0a0000003fffe67

def z491 : W := mkw 0x9a11ca53214c8644 0xfdfbd8c7031c0e07

def z492 : W := mkw 0x000c140002920000 0x0004040000830000

def z493 : W := mkw 0xcc201405c0170286 0xfdf41c27c09f0187

def z494 : W := mkw 0x8800000100040204 0xe4d01807001c0007

def z495 : W := mkw 0x60000000540150ab 0xf8e00038fce3f1ff

def z496 : W := mkw 0x0000400001400000 0x130bc00003400000

def z497 : W := mkw 0x0000000002a00910 0x0000000000a00198

def z498 : W := mkw 0x0043eb5a2968a000 0x0203e3183c60f000

def z499 : W := mkw 0x0000000000000000 0x1080000000e3f000

def z500 : W := mkw 0x000040000168a000 0x000000000060f000

def z501 : W := mkw 0xec20000156975baf 0xf0a0000003ffffff

def z502 : W := mkw 0x100ffff803e00d50 0x1f2ffff803e00ff8

def z503 : W := mkw 0x004f3f06a8000000 0x075fff07fc000000

def z504 : W := mkw 0x000c14a480000000 0x00040420c0000000

def z505 : W := mkw 0x0000000000000000 0x0200201800600078

def z506 : W := mkw 0x000d1f00029aa000 0x158c1f00039ff000

def z507 : W := mkw 0xdc2c94fdc2970fd6 0xfdfc1cffc39f0fff

def z508 : W := mkw 0xba11ca53314cc665 0xe6d3da17305cc067

def z509 : W := mkw 0xcc6c94ffea970b86 0xfdfc1cffff9f0f87

def z510 : W := mkw 0x60036b005569f0ab 0xffe7e738fce3f1ff

def z511 : W := mkw 0x600c14a4d40150ab 0xfffc3ffffce3f1ff

def z512 : W := mkw 0x400e350046b3308a 0x00042528cca33198

def z513 : W := mkw 0x8800000100040204 0x001818c7031c0e00

def z514 : W := mkw 0x0000000000000000 0x1304200000e00000

def z515 : W := mkw 0xba1ffffb33feef75 0xffffffff33ffffff

def z516 : W := mkw 0x004080fea8000000 0x0f5427fffc000000

def z517 : W := mkw 0xfa104001554dd6ef 0xf0a0000003ffffff

def z518 : W := mkw 0x4420000042930982 0x0000000000830180

def z519 : W := mkw 0x0000400003faa000 0x00000000031c0000

def z520 : W := mkw 0x104ffffeabfaad50 0x1ffffffffffffff8

def z521 : W := mkw 0x0000000002b22000 0x0000000000a33000

def z522 : W := mkw 0x0000000000000000 0x0f40021030000000

def z523 : W := mkw 0x2000000010004021 0xf0a000000040c067

def z524 : W := mkw 0x100fff5003faa440 0x1fafffd003fffe60

def z525 : W := mkw 0x000e750003f22000 0x130fe50003e33000

def z526 : W := mkw 0xba11ca53314cc665 0x021bdad7335cce60

def z527 : W := mkw 0x004f3fac88000000 0x070fff28cc000000

def z528 : W := mkw 0x000e750003faa000 0x1084250003fff000

def z529 : W := mkw 0xba1ee0f913eccf75 0xfbafe0f803fccfff

def z530 : W := mkw 0x100ee0f803e00d50 0x000fe0e803a00f98

def z531 : W := mkw 0x884fbfffa8040204 0xffffffffff1c0e07

def z532 : W := mkw 0x8c2f7fa583feab04 0x001bd8c7031c0e00

def z533 : W := mkw 0xba114a01114cc665 0xf7abda00035cce67

def z534 : W := mkw 0x60000000540150ab 0xfde40420c0e3f1ff

def z535 : W := mkw 0x004fbffea81aa000 0x0fdffffffc1ff000

def z536 : W := mkw 0x0000000000000000 0x178002000040c000

def z537 : W := mkw 0xba10805330044665 0xfdf818d7331c0e67

def z538 : W := mkw 0x104fbffea8000d50 0x0f7ffffffc000ff8

def z539 : W := mkw 0x2000000014005029 0x000000000060f078

def z540 : W := mkw 0x00011f00001aa000 0x17843f0000fff000

def z541 : W := mkw 0xcc2c14a5c2970b86 0xe87404e7c0830f87

def z542 : W := mkw 0xcc2f7f0143ffab86 0xf7afff0003ffff87

def z543 : W := mkw 0x700ee0f857e15dfb 0xfb6fe0f8ffe00fff

def z544 : W := mkw 0xba104001114cc665 0xffe00210335cce67

def z545 : W := mkw 0xba53eb5b394cc665 0xfffbfbdf3f5cce67

def z546 : W := mkw 0x9a11ca53214c8644 0x1b3bd8d7035c0e60

def z547 : W := mkw 0xba1fff53314cc665 0xffffffd7335cce67

def z548 : W := mkw 0xcc20400143ffab86 0xf0a0000003ffff87

def z549 : W := mkw 0xcc6fbfffe8050b86 0xef7ffffffc000f87

def z550 : W := mkw 0x704ffffeffe15dfb 0xffffffffffe3ffff

def z551 : W := mkw 0x60411f06fc0150ab 0xe4d01f07fc03f007

def z552 : W := mkw 0x000f7fa803faa910 0x178fff2803fff198

def z553 : W := mkw 0x004fbffea8000000 0x021bfbdf3c000000

def z554 : W := mkw 0x000e600003e00000 0x1b2fe03803e001f8

def z555 : W := mkw 0x000e20a802a00910 0x1b24203800e001f8

def z556 : W := mkw 0x400000004401108a 0x0f442738fca33198

def z557 : W := mkw 0x600c00a0568159ab 0xffec27f8ffe3ffff

def z558 : W := mkw 0xea110a03740dd2af 0xe4d01f07fc1ff007

def z559 : W := mkw 0x2000000014005029 0xffe023183c60f07f

def z560 : W := mkw 0x000000a480000000 0x085000e7c0000000

def z561 : W := mkw 0x0000000000000000 0x048007000003f000

def z562 : W := mkw 0x100ee05003e00440 0x1b2fe0d003e00e60

def z563 : W := mkw 0x20018a5230004021 0xfffbdad73040c067

def z564 : W := mkw 0x600f7f0057fbf0ab 0xf7afff0003fff1ff

def z565 : W := mkw 0xec20000156975baf 0xffe42738ffffffff

def z566 : W := mkw 0x0000000000000000 0x020023000060f000

def z567 : W := mkw 0xcc200005c0050286 0xe0500007c0000007

def z568 : W := mkw 0x000e350002b22000 0x1784270000e3f000

def z569 : W := mkw 0x0000400003e00000 0x1000000003e00000

def z570 : W := mkw 0x400f7f0043fba082 0xffefff20c3fff187

def z571 : W := mkw 0x000ea0f800000000 0x000bc0c000000000

def z572 : W := mkw 0x00011f00001aa000 0x00001800001c0000

def z573 : W := mkw 0x542ef4fcc3f30dd2 0x1b2fe4f8c3e30ff8

def z574 : W := mkw 0xcc2eb4fdc2970b86 0xfffffcffc39f0f87

def z575 : W := mkw 0xba5080ffb8044665 0xe87000fffc000e67

def z576 : W := mkw 0x60000000540150ab 0xffe0021030e3f1ff

def z577 : W := mkw 0x60000000540150ab 0xece00738fc03f1ff

def z578 : W := mkw 0x60000000540150ab 0xea602338fc60f1ff

def z579 : W := mkw 0x0000000000000000 0x020023183c000000

def z580 : W := mkw 0x700ffff857fbfdfb 0xffeffff8ffffffff

def z581 : W := mkw 0x60011f00541bf0ab 0xe4c01f00fc1ff007

def z582 : W := mkw 0xcc20000142970b86 0xfde40420c39f0f87

def z583 : W := mkw 0x000c14a002920900 0x1dac1ce0039f0f80

def z584 : W := mkw 0x004fbffea8000000 0x001ffdefcc000000

def z585 : W := mkw 0x00411f06a81aa000 0x04d01f07fc1ff000

def z586 : W := mkw 0xaa110a03300cc225 0xfdf81ac7331cce07

def z587 : W := mkw 0x1000400003faad50 0x10a0000003fffff8

def z588 : W := mkw 0x104ffffeabe00d50 0x001bd8c703000e00

def z589 : W := mkw 0x400c00a042810982 0xfdec04e0c3830f87

def z590 : W := mkw 0x000c00a002800900 0x000800c003000e00

def z591 : W := mkw 0x000f6b0003e8a000 0x130fe30003e0f000

def z592 : W := mkw 0x400f7f0047fbb08a 0x178fff28cffff198

def z593 : W := mkw 0x000e350002b22000 0x0000000000000000

def z594 : W := mkw 0x000c00a002800900 0x0004002000800180

def z595 : W := mkw 0x00400006a8000000 0x00500007fc000000

def z596 : W := mkw 0x44201404c0130082 0x00000400c0030000

def z597 : W := mkw 0x604ffffefffbf0ab 0xfffffffffffff1ff

def z598 : W := mkw 0x1002e05801600450 0x1b2be0d803600e78

def z599 : W := mkw 0x000c00a000000000 0x090c00e000000000

def z600 : W := mkw 0xfa11ca53754dd6ef 0xfffbdad733ffffff

def z601 : W := mkw 0x004ffffea9488000 0x1fdfffffff5cc000

def z602 : W := mkw 0x0000000000000000 0x0b04203800000000

def z603 : W := mkw 0x0040150488000000 0x00000500cc000000

def z604 : W := mkw 0x9a11ca53214c8644 0x0f5bdad7331c0e00

def z605 : W := mkw 0xcc20000140170286 0xe0800000001f0007

def z606 : W := mkw 0x1000000000000d50 0x0020000000000ff8

def z607 : W := mkw 0x600ea0f8540150ab 0xffefe7f8fce3f1ff

def z608 : W := mkw 0xde3ddef7e3df8fc6 0xfdffdce7c39f0f87

def z609 : W := mkw 0x600c1400569350ab 0xffec3f38fffff1ff

def z610 : W := mkw 0x00410b0228000000 0x000003003c000000

def z611 : W := mkw 0xba10400113eccf75 0xf0a0000003fccfff

def z612 : W := mkw 0x100f7f0003faad50 0x17afff0003fffff8

def z613 : W := mkw 0x400000004401108a 0x0000000000a33198

def z614 : W := mkw 0x600f7f0057fbf0ab 0xf7cfff00fffff007

def z615 : W := mkw 0x004c94fea8000000 0x0d5c1cfffc000000

def z616 : W := mkw 0xba1fea5333ecc665 0xfffffad733fcce67

def z617 : W := mkw 0x000fbf5220000000 0x0f5fffd730000000

def z618 : W := mkw 0x3211ca523148c461 0x178bda10335cc060

def z619 : W := mkw 0xec201405d41752af 0xe4d01f07fc1ff007

def z620 : W := mkw 0x00036b000168a000 0x1787e70000e3f000

def z621 : W := mkw 0x7000400057e15dfb 0xffe42738ffe3ffff

def z622 : W := mkw 0x60000000540150ab 0xe0400000fc000007

def z623 : W := mkw 0xfa1fff5377fff6ef 0xffffffffffffffff

def z624 : W := mkw 0xba1dcaf333cccf65 0xffffdaf733dccfe7

def z625 : W := mkw 0x442000a4c0010982 0x00000020c0000180

def z626 : W := mkw 0x0000000000000000 0x04400700fc000000

def z627 : W := mkw 0x000f7f0003faa000 0x108bd80003fff000

def z628 : W := mkw 0x00411f06a8000000 0x0f543f3ffc000000

def z629 : W := mkw 0x000c000002800000 0x110c000003800000

def z630 : W := mkw 0xdc2ffffdc3ffafd6 0xffffffffc3ffffff

def z631 : W := mkw 0x1000400001600450 0x0000000000600078

def z632 : W := mkw 0xba1f7f0113fee665 0xf7afff0003fffe67

def z633 : W := mkw 0x60000000540150ab 0xe4c42728fca3f19f

def z634 : W := mkw 0xcc2d9ef7e2970b86 0xffffdef7f39f0f87

def z635 : W := mkw 0x60000000540150ab 0xfb642038fce001ff

def z636 : W := mkw 0xba10c051114cc665 0xfbabc0d0035cce67

def z637 : W := mkw 0x000c540003faa000 0x158c1c0003fff000

def z638 : W := mkw 0x7211ca527549d4eb 0xffe7e738fce3f1ff

def z639 : W := mkw 0x2000000014005029 0x000000183c000078

def z640 : W := mkw 0x0002200800200010 0x0000200800200018

def z641 : W := mkw 0x000c14a482800900 0x1d7c1ce7c3800f80

def z642 : W := mkw 0xcc6fbfffea970b86 0xfdffdce7c39f0f87

def z643 : W := mkw 0x00036b000168a000 0x0003c00000000000

def z644 : W := mkw 0x60000000540150ab 0xe8642538fca331ff

def z645 : W := mkw 0x0000000000000000 0x0d440420c0000000

def z646 : W := mkw 0x400e20a846a1199a 0x00042528cca33198

def z647 : W := mkw 0x004d1fa6a8000000 0x0d5c1fe7fc000000

def z648 : W := mkw 0x100ee0f803e00d50 0x1b2bc0d003400e60

def z649 : W := mkw 0x004ffffeabe00000 0x1f5fffffffe00000

def z650 : W := mkw 0x100febf803e8ad50 0x1b2fe3f803e0fff8

def z651 : W := mkw 0x700080f854015dfb 0xe86000f8fc000fff

def z652 : W := mkw 0x1002e05801600450 0x0003c00000000000

def z653 : W := mkw 0x8c6fbfffaa960b04 0x0f5fffffff1c0e00

def z654 : W := mkw 0xba10c05331444665 0xfb7bc0d733400e67

def z655 : W := mkw 0x0000000000000000 0x1584040000830000

def z656 : W := mkw 0x600e350056b370ab 0xffe42738fce3f1ff

def z657 : W := mkw 0x0000000000000000 0x08400038fc000000

def z658 : W := mkw 0xcc2c1405c2970286 0xf5dc1c07c39f0007

def z659 : W := mkw 0x00018a5220000000 0x001bd8c700000000

def z660 : W := mkw 0x9a5fffffa94c8644 0x0f5fffffff1c0e00

def z661 : W := mkw 0x9e3ddef7a3de8f44 0x001bd8c7031c0e00

def z662 : W := mkw 0x000f7f0003faa000 0x178bda00035cc000

def z663 : W := mkw 0xcc2c14a5c0170286 0xeddc1ce7c01f0007

def z664 : W := mkw 0x000e60a003e00900 0x1b2fe0e003e00f80

def z665 : W := mkw 0x8a110a03200c8204 0x00101807001c0000

def z666 : W := mkw 0x9a1feafb23ec8f54 0x1b3ff8ff03fc0ff8

def z667 : W := mkw 0xcc20000140050b86 0xe020000000000f87

def z668 : W := mkw 0x6000400057fbf0ab 0xffe42738fffff1ff

def z669 : W := mkw 0x604080fefc0150ab 0xe87000fffc0001ff

def z670 : W := mkw 0x4000000040010082 0x00040420c0830180

def z671 : W := mkw 0x004fbf5a28000000 0x070fff183c000000

def z672 : W := mkw 0xba5fffffbbeccf75 0xfffffffffffccfff

def z673 : W := mkw 0x104ffffeabe00d50 0x0f5fffffff000e00

def z674 : W := mkw 0xec2c14a5d6975baf 0xfdfc1fe7ff9fff87

def z675 : W := mkw 0x7002e058556154fb 0xffe7e738fce3f1ff

def z676 : W := mkw 0xdc20400143f70fd6 0xf0a0000003ff0fff

def z677 : W := mkw 0xfe31caf7f14dcfe7 0xfffbdaf7f35ccfe7

def z678 : W := mkw 0x0000000000000000 0x0004250000a33000

def z679 : W := mkw 0x100feaf803e88d50 0x1faffaf803fccff8

def z680 : W := mkw 0x0043ab5a28000000 0x0f47e738fc000000

def z681 : W := mkw 0xba5fffffbbfee665 0xfffffffffffffe67

def z682 : W := mkw 0x60000000540150ab 0xe08000000003f007

def z683 : W := mkw 0x60018a52740150ab 0xfffffffffce3f1ff

def z684 : W := mkw 0x4000000040010082 0xffe42738fc830187

def z685 : W := mkw 0x000f7f0003faa000 0x020bfb00037cf000

def z686 : W := mkw 0x446fbffeea930982 0x0f5ffffffc830180

def z687 : W := mkw 0x000c14a482920000 0x1ddc1ce7c39f0000

def z688 : W := mkw 0xec2c14a5d6975baf 0xfdfc1ce7c3ffffff

def z689 : W := mkw 0x60000000540150ab 0xffe00710fc43f067

def z690 : W := mkw 0x204fbffeb8004021 0xfffffffffc40c067

def z691 : W := mkw 0x20014a001148c021 0xffebda10335cc067

def z692 : W := mkw 0x00411f06a8000000 0x0010180700000000

def z693 : W := mkw 0x000ea0f800000000 0x0f4fe7f8fc000000

def z694 : W := mkw 0xcc2c14a5c2970b86 0x001c1ce7c39f0f80

def z695 : W := mkw 0xee311e07f01fc2a7 0xe4d01e07f01fc007

def z696 : W := mkw 0xcc2000a5c0050b86 0xfdf404e7c0830f87

def z697 : W := mkw 0x000c140002920000 0x178c3f0003fff000

def z698 : W := mkw 0x9c2ef4fd83f60f54 0x001bd8c7031c0e00

def z699 : W := mkw 0x60000000540150ab 0xf4e00700fce3f1ff

def z700 : W := mkw 0x604fbffefc0150ab 0xefdffffffc03f007

def z701 : W := mkw 0x204fbffebc005029 0x0f5ffffffc60f078

def z702 : W := mkw 0x00032b0000000000 0x0203e30000000000

def z703 : W := mkw 0xcc6080ffe8050b86 0xe87000fffc000f87

def z704 : W := mkw 0x60000000540150ab 0xffe00238fc40c1ff

def z705 : W := mkw 0xaa1f7f0333fee225 0xf7dfff0733fff007

def z706 : W := mkw 0xba13ea5b316cc675 0xfffbfadf337cce7f

def z707 : W := mkw 0x004fbffea8000000 0x085ffdfffc000000

def z708 : W := mkw 0x000f7f0003faa900 0x17afff0003ffff80

def z709 : W := mkw 0x3211ca523548d469 0x0203c2103060f078

def z710 : W := mkw 0x8c2c14a582960b04 0xe4d818c7031c0e07

def z711 : W := mkw 0x100ee0f803e00d50 0x1b2fe3f803e0fff8

def z712 : W := mkw 0x100ee0f803e00d50 0x1fafe2f803e0cff8

def z713 : W := mkw 0xcc2c14a5c2970b86 0xeddc1ce7c31f0e07

def z714 : W := mkw 0x884e35ad88040204 0xfdfc3defcf1c0e07

def z715 : W := mkw 0x3211ca523148c461 0x0203e2183060c078

def z716 : W := mkw 0x000f7f0003faa000 0x1fafffc003fffe00

def z717 : W := mkw 0xaa1f2aab32accb35 0xe4d43a2f30bcc19f

def z718 : W := mkw 0x000f3f0002baa000 0x078fff0000bff000

def z719 : W := mkw 0xcc2c14a5c2970b86 0xfffc1ef7f39f0f87

def z720 : W := mkw 0x1000c05001400440 0x1b2bc0f803400ff8

def z721 : W := mkw 0xba5e75ad994cc665 0xf0a42528cf5cce67

def z722 : W := mkw 0x000f7f0803faa010 0x178fff0803fff018

def z723 : W := mkw 0xcc2e34a5c2b70b86 0xfdfc3ce7c3bf0f87

def z724 : W := mkw 0x8800000102840b04 0xfdf818c7039c0f87

def z725 : W := mkw 0x10019ff8001aad50 0x0ca01ff8001ffff8

def z726 : W := mkw 0x004f7fac8bfaa910 0x178fff28cffff198

def z727 : W := mkw 0x000e740003faa000 0x178ffc0003fff000

def z728 : W := mkw 0x7211ca527549d4eb 0x0207e738fce3f1f8

def z729 : W := mkw 0x88014a01014c8204 0xfdfbd8c7031c0e07

def z730 : W := mkw 0x00419f56a8000000 0x045bdfc7fc000000

def z731 : W := mkw 0x100f7fa003faad50 0x1fafffe003fffff8

def z732 : W := mkw 0x763ddef6f3dbcde3 0x0207c630f0c3c1e0

def z733 : W := mkw 0xba11ca53314cc665 0xffffded733dfce67

def z734 : W := mkw 0x100ee0f803e00d50 0x1bafe0f803e3fff8

def z735 : W := mkw 0xcc6c14adca970b86 0xfdfc1cefcf9f0f87

def z736 : W := mkw 0xcc201405c0170286 0xfdfc1ce7c39f0f87

def z737 : W := mkw 0x004fbffeaabaa000 0x0fdffffffcbff000

def z738 : W := mkw 0x004fbffea8000000 0x0657ff3ffc000000

def z739 : W := mkw 0x100ee0f803e00d50 0x182bc0f803e00ff8

def z740 : W := mkw 0x60000000540150ab 0xea642738fce3f1ff

def z741 : W := mkw 0x3211ca523168e461 0x0203c2103060f060

def z742 : W := mkw 0x00018a5220000000 0x0f5bdafffc000000

def z743 : W := mkw 0x9a11ca53214c8644 0xf0bbd8c7031c0e07

def z744 : W := mkw 0xcc2000a5c0050b86 0xe87818e7c31c0f87

def z745 : W := mkw 0x004fbffeaaa00910 0x1f7ffffffce001f8

def z746 : W := mkw 0xba11ca53314cc665 0xfffffaff335cce67

def z747 : W := mkw 0x000f7f0003faa000 0x178fff183ffff000

def z748 : W := mkw 0x3211cb523148e461 0x0203c3103040f060

def z749 : W := mkw 0x004f7faeabfaa000 0x17dfff2ffffff000

def z750 : W := mkw 0x000f7f00015aa000 0x178fff00035ff000

def z751 : W := mkw 0x000f7f0003faa000 0x1fafff1003fff060

def z752 : W := mkw 0x100f7f0003faa450 0x178fff0003fff078

def z753 : W := mkw 0x004fbffea8000910 0x0f5ffffffc000198

def z754 : W := mkw 0x8c2c14a582960b04 0xfdfc1ce7c31c0e07

def z755 : W := mkw 0x004d9ff6a8000000 0x0f5fdff7fc000000

def z756 : W := mkw 0x004fbffea8000000 0x045fffeffc000000

def z757 : W := mkw 0xcc6e35adcab72b86 0xfdfc3defcfbf3f87

def z758 : W := mkw 0xdc22f45dc17706d6 0xe6d3fc1fc07f007f

def z759 : W := mkw 0x000f7fa803faa910 0x1fafffe803ffff98

def z760 : W := mkw 0x60000000540150ab 0xe6c42738fce3f1ff

def z761 : W := mkw 0xcc63ab5b6a970b86 0xf2a3e3183f9f0f87

def z762 : W := mkw 0x00018a5220000000 0x0f5bdfd7fc000000

def z763 : W := mkw 0x004fbffea81aa000 0x0f5ffffffc1c0000

def z764 : W := mkw 0x880e350102b62204 0xfdfc3dc703bf3e07

def z765 : W := mkw 0x00014a00015aa000 0x178bda00035ff000

def z766 : W := mkw 0xba11ca53314cc665 0xf2bbdad7335cce67

def z767 : W := mkw 0x000f7f0003faa000 0x178fff2803fff198

def z768 : W := mkw 0x000f3f00001aa000 0x048bdf00001ff000

def z769 : W := mkw 0x004f7f06abfaa000 0x179fff0703fff000

def z770 : W := mkw 0x100f7fa803faad50 0x17afff2803fffff8

def z771 : W := mkw 0xda11ca53654d96ce 0x001ffdefcfbf3f98

def z772 : W := mkw 0x1040c0feabe00d50 0x187000ffffe00ff8

def z773 : W := mkw 0xba1eb55332b66665 0xe87425d730a33e67

def z774 : W := mkw 0x100ee0f803e00d50 0x002bc0c003000ff8

def z775 : W := mkw 0x004fbffeaa920000 0x0f5ffffffc830000

def z776 : W := mkw 0xcc2014a5c2970b86 0xfcf01ce7c39f0f87

def z777 : W := mkw 0x1002e05801600450 0x1b2fe0f803e00ff8

def z778 : W := mkw 0xba114a01114cc665 0xfffbdac7035cce67

def z779 : W := mkw 0x004ea0fea8000000 0x085bc0fffc000000

def z780 : W := mkw 0x004fbffea8000000 0x0a57e7fffc000000

def z781 : W := mkw 0xba11ca53314cc665 0xfbbbd8d7035cce67

def z782 : W := mkw 0xfa108053740556ef 0xe87000d7fc000e67

def z783 : W := mkw 0x004fbffeaa800900 0x0f5ffffffc800180

def z784 : W := mkw 0x004fbffeaab22000 0x1fdffffffce3f000

def z785 : W := mkw 0xcc2c14a5c2970b86 0xe09818c7031f0e07

def z786 : W := mkw 0xcc201405c0170286 0xe4d81cc7c31f0e07

def z787 : W := mkw 0x1002e0f801600d50 0x1b2be0f803600ff8

def z788 : W := mkw 0x000eb4fc80000000 0x0f5ffffffc000000

def z789 : W := mkw 0xfe30400157dfdfef 0xf0a0000003ffffff

def z790 : W := mkw 0xc800000140050286 0xfdf81cc7c31f0e07

def z791 : W := mkw 0x000f7fa803faa910 0x1fafff3803fff1f8

def z792 : W := mkw 0x321fff5233fae461 0x0207e71030e3f060

def z793 : W := mkw 0x000f6a0003e88000 0x178fff0003fff000

def z794 : W := mkw 0x3213ea5a3168c471 0x0203c2103040c060

def z795 : W := mkw 0x604fbffefc0150ab 0xf0bbd8c700e3f1ff

def z796 : W := mkw 0x0040c0feabfaa000 0x18d000fffffff000

def z797 : W := mkw 0x1000c0f803e00d50 0x1b2bc0f803e00ff8

def z798 : W := mkw 0x8800000100040204 0xfdfc18e7039c0f87

def z799 : W := mkw 0x700ee0f857e15dfb 0xe4cbc7c0ff03fe07

def z800 : W := mkw 0x004fbffea8000000 0x1f7ffffffc400060

def z801 : W := mkw 0x004fbffea8000000 0x0c5bdffffc000000

def z802 : W := mkw 0x004f3f06a8000000 0x0f5fff3ffc000000

def z803 : W := mkw 0x3211ca523148c461 0x0203e3103060f060

def z804 : W := mkw 0xcc201405c2970b86 0xfdf81cc7c39f0f87

def z805 : W := mkw 0x004fbffea8000000 0x0f5ffffffca33000

def z806 : W := mkw 0x000f7fa803faa000 0x178fff2803fff000

def z807 : W := mkw 0x3213ea5a3148c461 0x0203e2183040c060

def z808 : W := mkw 0x0042a0fea8000000 0x0a53e0fffc000000

def z809 : W := mkw 0x100ee0f803e00d50 0x0b2fe0f803000ff8

def z810 : W := mkw 0x9801ca51014c8644 0xfffbdad7035cce67

def z811 : W := mkw 0x600f7f0057fbf0ab 0xe86bd838ff1c01ff

def z812 : W := mkw 0x8800000100040204 0xe4d818c7031c0e07

def z813 : W := mkw 0x00014a0003faa000 0x1283c20003fff000

def z814 : W := mkw 0x100e60a003e00d50 0x1b2fe0e003e00ff8

def z815 : W := mkw 0x104ef5fc8be00d50 0x1f6fe7f8ffe00ff8

def z816 : W := mkw 0x004fbffeaaa00910 0x1f7fffffffa00f98

def z817 : W := mkw 0x00036b0003faa000 0x178bfb0003fff000

def z818 : W := mkw 0x004f7f06abfaa000 0x1fdfff3ffffff000

def z819 : W := mkw 0x8c2c14a582960b04 0xfdfc18e7039c0f87

def z820 : W := mkw 0x880e20a902a40b14 0xfdfc38ef03bc0f9f

def z821 : W := mkw 0xac2c14a596965b2d 0x02183bdf3f7cfe78

def z822 : W := mkw 0x0043bffea8000000 0x0e53fffffc000000

def z823 : W := mkw 0x880c140102960204 0xfdf818c7031c0e07

def z824 : W := mkw 0x60000000540150ab 0xffec27f8ffe3ffff

def z825 : W := mkw 0x000f7f0003faa000 0x17cfff00fffff000

def z826 : W := mkw 0xc800000140050286 0xfdf818c7039f0f87

def z827 : W := mkw 0xcc2c14a5c2970b86 0xf9bc18e7039f0f87

def z828 : W := mkw 0x9800c05101440644 0xfdfbd8c7031c0e07

def z829 : W := mkw 0x100ef5f803f22d50 0x1faffdf803ff3ff8

def z830 : W := mkw 0x10415f06abe00d50 0x14701f07ffe00ff8

def z831 : W := mkw 0xba11ca53354cd66d 0xfffbdad7337cfe7f

def z832 : W := mkw 0x880c14a582960204 0xfdfc1ce7c39f0e07

def z833 : W := mkw 0x8800140100160204 0xfdf81cc7031f0e07

def z834 : W := mkw 0xcc2e34adc2970b86 0xfdfc3cefc39f0f87

def z835 : W := mkw 0x8800000100040204 0xf0b818c7031c0e07

def z836 : W := mkw 0xfa5080fffc0556ef 0xe87000fffc000fff

def z837 : W := mkw 0x00011f00001aa000 0x078bdf00001ff000

def z838 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1fe7c39fff87

def z839 : W := mkw 0x004fbffea8000000 0x0f5ffffffc60f000

def z840 : W := mkw 0xcc236ba5c16dab86 0xea73e3e7c060ff87

def z841 : W := mkw 0x880000a100040b04 0xfdf818e7031c0f87

def z842 : W := mkw 0x100ee0f803e00d50 0x1f7ff8ff03e00ff8

def z843 : W := mkw 0x000f7f0003faa000 0x078fff00031ff000

def z844 : W := mkw 0x100ee0f801600d50 0x0b2fe0f800600ff8

def z845 : W := mkw 0xa8014a01114cc225 0xfffbdad7335cce67

def z846 : W := mkw 0x100ee0f803e00d50 0x1f6fe4f8c3e00ff8

def z847 : W := mkw 0x000d5e0003faa000 0x178fde0003fff000

def z848 : W := mkw 0x0002600003faa000 0x1283e00003fff000

def z849 : W := mkw 0x8800000100040204 0xfdfc1ce7c31c0e07

def z850 : W := mkw 0x100ee0f803e8ad50 0x1b2fe0f803e0fff8

def z851 : W := mkw 0x1000c05003e00d50 0x1223c01003e00ff8

def z852 : W := mkw 0x100e60a803e00d50 0x132fe02803e00ff8

def z853 : W := mkw 0x000f7f0003faa000 0x178bdf00035ff000

def z854 : W := mkw 0xcc2014a5c0170b86 0xfdf81ce7c31f0f87

def z855 : W := mkw 0x3211ca5a3148c471 0x0203c2183040c078

def z856 : W := mkw 0x100f7f0003faa440 0x17afff0003fffe60

def z857 : W := mkw 0x3213ea5a3568d479 0x0203e3183c60f078

def z858 : W := mkw 0xfc20400157f75fff 0xf0a0000003ffffff

def z859 : W := mkw 0xcc2c14a5c2970b86 0xfdf818e7c31c0f87

def z860 : W := mkw 0x8800000100040204 0xe87818c7031c0e07

def z861 : W := mkw 0x004fbffeaa800900 0x1f7fffffffe00ff8

def z862 : W := mkw 0x100ea0f802a00d50 0x0b2fe0f800a00ff8

def z863 : W := mkw 0x000e60a003e00900 0x1b2fe0f803e00ff8

def z864 : W := mkw 0xfe3080f7f4055fef 0xe87000fffc000fff

def z865 : W := mkw 0x1000c0f801400d50 0x082bc0f803000ff8

def z866 : W := mkw 0xcc2c14a5c6971b8e 0xfffc3fefcfffff9f

def z867 : W := mkw 0x3253eb5a3968c471 0x0203e3183c60c078

def z868 : W := mkw 0x0043bf5ea8000000 0x0f5bffdffc000000

def z869 : W := mkw 0x042f7fa483faa900 0x178fff0003fff000

def z870 : W := mkw 0x1000c05003e00d50 0x102bc0c003e00ff8

def z871 : W := mkw 0x000f7f0003faa000 0x1f8fff3803fff000

def z872 : W := mkw 0xcc2000a5c0050b86 0xfdfc1ce7c39f0f87

def z873 : W := mkw 0xcc2c00a5c2850b86 0xfdfc18e7c39c0f87

def z874 : W := mkw 0x000f7f0003faa000 0xffefff0003fff007

def z875 : W := mkw 0x100ee0f803e00d50 0x1f6fe2f833e00ff8

def z876 : W := mkw 0x100ee0f803e00d50 0x132fe0c003e00ff8

def z877 : W := mkw 0x9a11ca53214c8644 0xe87bd8c7031c0e07

def z878 : W := mkw 0xcc6e35adcab70b96 0xfdfc3defcfbf0f9f

def z879 : W := mkw 0xc80c14a5c0050286 0xfdfc1ce7c39f0f87

def z880 : W := mkw 0x000f7fa483faa000 0x178fff20c3fff000

def z881 : W := mkw 0x004fbffeaa920000 0x1fdffffffffff000

def z882 : W := mkw 0x100ef4fc83f20d50 0x1ffffcffc3ff0ff8

def z883 : W := mkw 0x004eb4fea8000000 0x0f5ffcfffc000000

def z884 : W := mkw 0x880c14a580040204 0xfdf818c7031c0e07

def z885 : W := mkw 0x100ee0f803e00d50 0x1f2fe7f803e00ff8

def z886 : W := mkw 0x000f7f0003faa910 0x178fff0003fff198

def z887 : W := mkw 0x00015f00015aa000 0x0683df00005ff000

def z888 : W := mkw 0xcc2e34adc2b70b96 0xfdfc1ce7c39f0f87

def z889 : W := mkw 0x8800000100040204 0xfffc38ff03fc0fff

def z890 : W := mkw 0x100ee0f803e00d50 0xffefe0f803e00fff

def z891 : W := mkw 0x000fbf5220000000 0x0f5ffffffc000000

def z892 : W := mkw 0xcc2c14a5c2970b86 0xf4f81cc7c39f0f87

def z893 : W := mkw 0x3211ca523148c461 0x0003c2003000c000

def z894 : W := mkw 0x004fbffea8200010 0x0f5ffffffc200018

def z895 : W := mkw 0xba11ca53314cc665 0xfffbdad733fccfff

def z896 : W := mkw 0x8800000100040204 0xfff818d7035c0e67

def z897 : W := mkw 0x8800000100040204 0xfff81ac7035cce07

def z898 : W := mkw 0x8c2c14a582960b04 0xfdfc1cc7039f0e07

def z899 : W := mkw 0x1000c05003e00d50 0x1b2fe0f803e00ff8

def z900 : W := mkw 0x3253eb5a3948c461 0x0203c2103040c060

def z901 : W := mkw 0xcc2e34adc6b71b9e 0xfdfc3defcfbf3f9f

def z902 : W := mkw 0x100ef4fc83e00d50 0x1f7fffffffe00ff8

def z903 : W := mkw 0x1002e0f803e00d50 0x1a23e0f803e00ff8

def z904 : W := mkw 0x00015f00015aa000 0x178fff0003fff000

def z905 : W := mkw 0x00418afea8000000 0x0a53c2fffc000000

def z906 : W := mkw 0xba11ca53314cc665 0xf7dbdac7335cce07

def z907 : W := mkw 0x000f7f0223faa000 0x17dfff0733fff000

def z908 : W := mkw 0xba11ca53314cc665 0xea7bdad7335cce67

def z909 : W := mkw 0x00014a0001488000 0x178bdf00035ff000

def z910 : W := mkw 0xba11ca53354cd66d 0xffffffffff7cfe7f

def z911 : W := mkw 0x100ef5f803e00d50 0x1b2fe5f803e00ff8

def z912 : W := mkw 0x100ee0f803e00d50 0x1fafe4f803e30ff8

def z913 : W := mkw 0x004fbffea8000000 0x0a5bfbfffc000000

def z914 : W := mkw 0x004fbffea8000000 0x1fdfffffff1c0000

def z915 : W := mkw 0x8800000100040204 0xfffc3fffff1c0e07

def z916 : W := mkw 0x004f7fa6abfaa000 0x1fdfffe7fffff000

def z917 : W := mkw 0x3213eb5a3168e471 0x0203e3183060f078

def z918 : W := mkw 0x88010a0100040204 0xfffbdac7031c0e07

def z919 : W := mkw 0xfa10400157fff6ef 0xf0a0000003ffffff

def z920 : W := mkw 0x8800000100040204 0xfff81ad7331c0e07

def z921 : W := mkw 0x100ee0f803e00d50 0x020fe0f803e00ff8

def z922 : W := mkw 0x000f7f0003faa000 0x1fdfffc703fff000

def z923 : W := mkw 0x442e34a4c2b30982 0x00042420c0a30180

def z924 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1ce7c3ffff87

def z925 : W := mkw 0x00418afea8000000 0x0f5ffffffc000000

def z926 : W := mkw 0x100ee0f803e00d50 0x122be0d803e00ff8

def z927 : W := mkw 0x442e35a4c2930982 0x00042520c0830180

def z928 : W := mkw 0x000f7f0003faa000 0x178fff1803fff078

def z929 : W := mkw 0x100ee0f803e00d50 0x1227e03803e00ff8

def z930 : W := mkw 0x004fbffeaaa00000 0x0f5ffffffca00000

def z931 : W := mkw 0x004f7fac8bfaa000 0x1fdfffefcffff000

def z932 : W := mkw 0x004fbffeaab22910 0x0f5ffffffca33198

def z933 : W := mkw 0x000f7f0003faa000 0x0687ff0000fff000

def z934 : W := mkw 0x000f7f0003faa000 0x048fff0003bff000

def z935 : W := mkw 0x004fbffeaab22000 0x1fdfffffffbf3000

def z936 : W := mkw 0x100f7f0003faad50 0x1fafff3803fffff8

def z937 : W := mkw 0x100ee0f803e00d50 0x1b2bc0d003e00ff8

def z938 : W := mkw 0xb800c05111444665 0xfffbdad7335cce67

def z939 : W := mkw 0x100f7f0003faad50 0x178fff0003fffe00

def z940 : W := mkw 0x3211ca523148c461 0x0003c0000040c060

def z941 : W := mkw 0x004fbffea8000000 0x1f7fffffff000e00

def z942 : W := mkw 0x004fbffea8000000 0xfffffffffc000007

def z943 : W := mkw 0xcc2c14a5c2970b86 0xfffc3fffffffff87

def z944 : W := mkw 0xec6080fffc055baf 0xe87000fffc000fff

def z945 : W := mkw 0xcc2c15a5c2972b86 0xfdfc1de7c39f3f87

def z946 : W := mkw 0x1002e05803e00d50 0x1023c00003e00ff8

def z947 : W := mkw 0xcc2c14a5c2970b86 0xfffc3fffc3ffffff

def z948 : W := mkw 0xcc2c14a5c2970b86 0xfffc1ee7c3dfcf87

def z949 : W := mkw 0xea511f07fc0dd2af 0xe4d01f07fc1ff007

def z950 : W := mkw 0x000f7f0003faa000 0x148bdf0003fff000

def z951 : W := mkw 0x000f7f0003faa000 0x1287e70003fff000

def z952 : W := mkw 0x000f7f0003faa000 0x1fcfff20c3fff000

def z953 : W := mkw 0xfa1080fb74055fff 0xe87000fffc000fff

def z954 : W := mkw 0x104fbffeaaa00d50 0x0f7ffffffca00ff8

def z955 : W := mkw 0x442e35a4c2b32982 0x00040420c0830180

def z956 : W := mkw 0x100ee0f803e00d50 0x0a27e0f800e00ff8

def z957 : W := mkw 0x004fbffea8000000 0x021ffffffc000000

def z958 : W := mkw 0x000f7fa003faa900 0x1faffff803fffff8

def z959 : W := mkw 0x880c14a582840b04 0xfdfc1ce7c39c0f87

def z960 : W := mkw 0x3211ca523148c461 0x0003c01030000060

def z961 : W := mkw 0x000f7fa003faa900 0x178fff2003fff180

def z962 : W := mkw 0xcc2e35a5c2b72b86 0xfffc3fe7c3ffff87

def z963 : W := mkw 0xba11ca53354cd66d 0xfffbdadf3f5cce7f

def z964 : W := mkw 0xcc20000142970b86 0xfdfc1ce7c39f0f87

def z965 : W := mkw 0x1000c0f801400d50 0x1b2fe0f803e00ff8

def z966 : W := mkw 0x3253eb5a3d48d469 0x0203e3183c60f078

def z967 : W := mkw 0x104ee0feabe00d50 0x1f7fe7ffffe00ff8

def z968 : W := mkw 0x000f7fa003faa000 0x1f8fffe003fff000

def z969 : W := mkw 0x1002e05803e00d50 0x1b27e03803e00ff8

def z970 : W := mkw 0xba11ca53354cd66d 0xfffffbff3ffcffff

def z971 : W := mkw 0x100ee0f803e00d50 0x1b2bc0f803400ff8

def z972 : W := mkw 0xc80c140142970286 0xfdfc1ce7c39f0f87

def z973 : W := mkw 0x004fbffeaaa00910 0x0f5ffffffc000000

def z974 : W := mkw 0x0043abfea8000000 0x0853c0fffc000000

def z975 : W := mkw 0xba11ca53314cc665 0xfffffffffffccfff

def z976 : W := mkw 0x60000000540150ab 0xffec3f38fffff1ff

def z977 : W := mkw 0x3211ca523148c461 0x0f43c2103040c060

def z978 : W := mkw 0xcc6e35adce971b8e 0xfdfc3defcfbf3f9f

def z979 : W := mkw 0xba11ca53354cd66d 0xfffbdbd73f5cfe67

def z980 : W := mkw 0xba11ca53314cc665 0xfffbdaff335ccfff

def z981 : W := mkw 0x8800000100040204 0xfffc3fc703fffe07

def z982 : W := mkw 0x004fbffea8122000 0x0f5ffffffc033000

def z983 : W := mkw 0x100ef4fc83e00d50 0x1b2fe4f8c3e00ff8

def z984 : W := mkw 0xba11ca53314cc665 0xfffbfadf337cce7f

def z985 : W := mkw 0xba11ca53314cc665 0xfffbdfd7ff5cce67

def z986 : W := mkw 0x100e600003e00d50 0x102bc00003e00ff8

def z987 : W := mkw 0xba11ca53314cc665 0xfdfbd8c7035cce67

def z988 : W := mkw 0x3211ca523148c461 0x1b23c2103040c060

def z989 : W := mkw 0x100ee05803e00d50 0x132fe01803e00ff8

def z990 : W := mkw 0xc80000014405128e 0xfdfc3defcfbf3f9f

def z991 : W := mkw 0x8800000100040204 0xfdfc1cc7039f0e07

def z992 : W := mkw 0x104ef5feabe00d50 0x1b7fe5ffffe00ff8

def z993 : W := mkw 0xba10c051114cc665 0xfffbd8d7035cce67

def z994 : W := mkw 0x100ee0f803e00d50 0x1b2fe5f803e33ff8

def z995 : W := mkw 0xba11ca53314cc665 0xfffbfbd7337cfe67

def z996 : W := mkw 0x880c00a102840b04 0xfdf818c7031c0e07

def z997 : W := mkw 0x3253eb5a3968e461 0x0203e3183c60f060

def z998 : W := mkw 0xee311e07f41fd2af 0xe4d01f07fc1ff007

def z999 : W := mkw 0xcc2e34adc2b70b96 0xfffc3cffc3ff0fff

def z1000 : W := mkw 0x000f7f0003faa000 0x158fdc0003fff000

def z1001 : W := mkw 0x100ee0f803e00d50 0x1fefe7f8ffe3fff8

def z1002 : W := mkw 0x000f7fa803faa910 0x178fff0003fff000

def z1003 : W := mkw 0xba11ca53314cc665 0xfdfbd8d7331c0e67

def z1004 : W := mkw 0x3211ca523148c461 0x1783c2103040c060

def z1005 : W := mkw 0xba11ca53314cc665 0xfdfbdac7331cce07

def z1006 : W := mkw 0x100e600003e00d50 0x1b2fe03803e00ff8

def z1007 : W := mkw 0x00015f0003faa000 0x178bdf0003fff000

def z1008 : W := mkw 0x60000000540150ab 0xfffc3ffffce3f1ff

def z1009 : W := mkw 0x8c2c14a582960b04 0xf0b818c7031c0e07

def z1010 : W := mkw 0x000f7f0003faa000 0x020fff0003fff000

def z1011 : W := mkw 0x004f7f022bfaa000 0x178fff003ffff000

def z1012 : W := mkw 0x100ea0f800000d50 0x082bc0f800000ff8

def z1013 : W := mkw 0x000f7f0003faa000 0x178bda0003fff000

def z1014 : W := mkw 0x104ef5fc8be00d50 0x1f7ffdffcfe00ff8

def z1015 : W := mkw 0xcc2c14a5c2970b86 0xf8f818e7c39f0f87

def z1016 : W := mkw 0xcc2c14a5c2970b86 0xe05818c7c31c0e07

def z1017 : W := mkw 0x004fbffea8000000 0x075fffc7fc000000

def z1018 : W := mkw 0x004fbffeaa9aa000 0x1fdfffffff9ff000

def z1019 : W := mkw 0x442e35a4c6b3398a 0x00042528cca33198

def z1020 : W := mkw 0x3251ca5a3948c461 0x0203c2183c40c060

def z1021 : W := mkw 0xcc2c14a5c2970b86 0xecf81ce7c31f0f87

def z1022 : W := mkw 0x321feafa33e8cd71 0x0207e23830e0c1f8

def z1023 : W := mkw 0xec20400157fffbaf 0xf0a0000003ffffff

def z1024 : W := mkw 0x100ee0f803e00d50 0x1b6fe0f8ffe00ff8

def z1025 : W := mkw 0x000f7f0003faa000 0x178fff28cffff000

def z1026 : W := mkw 0xcc2c14a5c2970b86 0xfdfc3defcf9f0f87

def z1027 : W := mkw 0x100ee05003e00d50 0x1b2fe0d003e00ff8

def z1028 : W := mkw 0x104fbffea8000450 0x0f5ffffffc000078

def z1029 : W := mkw 0x100ee0f803e00d50 0x1b2fe5f8cfe00ff8

def z1030 : W := mkw 0xcc20000142970b86 0xf0b818c7039f0f87

def z1031 : W := mkw 0x00419ffea81aa000 0x0cd01ffffc1ff000

def z1032 : W := mkw 0xcc2c1405c2970286 0xfdfc1cc7c39f0e07

def z1033 : W := mkw 0x1000400003e00d50 0x132bc00003e00ff8

def z1034 : W := mkw 0x0043abfea8000000 0x0f5bfbfffc000000

def z1035 : W := mkw 0x004080fea8000000 0x0b5bc0fffc000000

def z1036 : W := mkw 0xcc2c14a5c6971b8e 0xfdfc1cefcf9f0f9f

def z1037 : W := mkw 0xcc20000140170286 0xfdf818c7031f0e07

def z1038 : W := mkw 0x8800400101440204 0xfffbd8c7035c0e07

def z1039 : W := mkw 0xcc2c14a5c2970b86 0xfdfc3cefc3bf0f9f

def z1040 : W := mkw 0x00015f00015aa000 0x048bdf00031ff000

def z1041 : W := mkw 0x100ee0fc83e00d50 0x1b7fe0ffc3e00ff8

def z1042 : W := mkw 0x3211ca523148c461 0x1b27e23830e0c1f8

def z1043 : W := mkw 0x046fbffeaa920900 0x0f5ffffffc000000

def z1044 : W := mkw 0x000f7f0001488000 0x178fff0003fff000

def z1045 : W := mkw 0xba11ca53354cd66d 0xffffffdf3ffffe7f

def z1046 : W := mkw 0x000f7f00017aa000 0x078fff00007ff000

def z1047 : W := mkw 0xea110a03740dd2af 0xe4d01a07301ff007

def z1048 : W := mkw 0xba11ca53314cc665 0xf4fbdac7335cce67

def z1049 : W := mkw 0x100ee0f803f20d50 0x1bafe0f803ff0ff8

def z1050 : W := mkw 0x004fbffea8000000 0x0d5fdcfffc000000

def z1051 : W := mkw 0x0043bf5ea8000000 0x0f57ff3ffc000000

def z1052 : W := mkw 0xcc6e35adca970b86 0xfdfc1ce7c39f0f87

def z1053 : W := mkw 0x004fbffea8120000 0x0fdffffffc1f0000

def z1054 : W := mkw 0x100ef4f803f20d50 0x1b2fe4f803e30ff8

def z1055 : W := mkw 0x100ee0fa23e00d50 0x1b7fe0ff33e00ff8

def z1056 : W := mkw 0xcc2c14a5c2970b86 0xf97c18e7c39c0f87

def z1057 : W := mkw 0xcc2e35a5c6b73b8e 0xfdfc3defcfbf3f9f

def z1058 : W := mkw 0x004f3f06a8000000 0x045bdf07fc000000

def z1059 : W := mkw 0x004fbffea808a000 0x0f5ffffffc00f000

def z1060 : W := mkw 0xcc2c14a5c2b72b86 0xfdfc1ce7c3bf3f87

def z1061 : W := mkw 0xba11ca53314cc665 0xffffffff33ffffff

def z1062 : W := mkw 0x00014a0001488000 0x178bda0003fff000

def z1063 : W := mkw 0x100ee0f803e00d50 0x192fc0f803800ff8

def z1064 : W := mkw 0x100ee0f803e00d50 0x1b2fe3f83fe00ff8

def z1065 : W := mkw 0x004fbffea8000000 0x0f5bdfd7fc000000

def z1066 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1fe7ff9f0f87

def z1067 : W := mkw 0xec211f05d41ff2af 0xe4d01f07fc1ff007

def z1068 : W := mkw 0xcc2e34a5c2970b86 0xfffffce7c39f0f87

def z1069 : W := mkw 0xba11ca53314cc665 0xfffbdfd7335ffe67

def z1070 : W := mkw 0x000ea0f802800900 0x1b2fe0f803e00ff8

def z1071 : W := mkw 0xcc6e35adca970b86 0xfffc3fffff9f0f87

def z1072 : W := mkw 0x880c000102840204 0xfdfc18c7039c0e07

def z1073 : W := mkw 0x100ee1f803e02d50 0x1b2fe1f803e03ff8

def z1074 : W := mkw 0xba11ca53314cc665 0xf7bbdac7035cce67

def z1075 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1ce7c3ff0fff

def z1076 : W := mkw 0x000f3f00029aa000 0x178fff00039ff000

def z1077 : W := mkw 0x100ee0f803faad50 0x1b2fe0f803fc0ff8

def z1078 : W := mkw 0x00433f06a8000000 0x0653ff07fc000000

def z1079 : W := mkw 0x880000a580040204 0xfdf818e7c31c0e07

def z1080 : W := mkw 0xcc2c140142970b86 0xfdfc1cc7039f0f87

def z1081 : W := mkw 0x60000000540150ab 0xf2a42738fce3f1ff

def z1082 : W := mkw 0x1002e05801600d50 0x0223e01800600ff8

def z1083 : W := mkw 0x100ee05003e00440 0x1b2fe0f803e00ff8

def z1084 : W := mkw 0x100ee0f803e00d50 0x1faff8f803fc0ff8

def z1085 : W := mkw 0x000f7fa003faa900 0x178fffc003fffe00

def z1086 : W := mkw 0x100ef4f803e00d50 0x1f2ffcf803e00ff8

def z1087 : W := mkw 0xcc2c14a5c2970b86 0xfffc3fffffff0fff

def z1088 : W := mkw 0x00033f00001aa000 0x0683ff00001ff000

def z1089 : W := mkw 0x0043ab5a28000000 0x0f5ffffffc000000

def z1090 : W := mkw 0x1000c0f801400d50 0x0a23c0f800400ff8

def z1091 : W := mkw 0x004fbffeaa800900 0x0f5fffffff000e00

def z1092 : W := mkw 0xcc2c14a5c2970b86 0xf0bc1ce7c39f0f87

def z1093 : W := mkw 0x00418a56a8000000 0x0f5bdad7fc000000

def z1094 : W := mkw 0x3211ca523148c461 0x0203e3183c40c060

def z1095 : W := mkw 0x9a11ca53214c8644 0xe4dbd8c7031c0e07

def z1096 : W := mkw 0x004fbffeaab22000 0x0f5ffffffc000000

def z1097 : W := mkw 0xba11ca53316cc675 0xfffbdad7337cce7f

def z1098 : W := mkw 0x004fbffea81aa000 0x1fdffffffcfff000

def z1099 : W := mkw 0xcc2c14a5c2970b86 0xe4dc1ce7c39f0f87

def z1100 : W := mkw 0x3211ca523148c461 0x0f47e738fc40c060

def z1101 : W := mkw 0xc80c00a142850b86 0xfdfc1ce7c39f0f87

def z1102 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1cffff9f0f87

def z1103 : W := mkw 0x100ef5f803f22d50 0x1fafe7f803e3fff8

def z1104 : W := mkw 0xba11ca5b314cc675 0xfffbdadf335cce7f

def z1105 : W := mkw 0x000d5f0003daa000 0x178fdf0003dff000

def z1106 : W := mkw 0x000f7f0003faa000 0x068bff00037ff000

def z1107 : W := mkw 0x004fbffeaa920000 0x0f5fffffff1c0000

def z1108 : W := mkw 0x10419ffea8000d50 0x0c701ffffc000ff8

def z1109 : W := mkw 0xcc2c14a5c2970b86 0xfdfc1cffc39f0fff

def z1110 : W := mkw 0x00036b0003faa000 0x1083c00003fff000

def z1111 : W := mkw 0x100ea0f800000d50 0x1b2fe0f800e00ff8

def z1112 : W := mkw 0x004f3fa6a8000000 0x0f5fffe7fc000000

def z1113 : W := mkw 0x88018a5320040204 0xfdfbd8c7031c0e07

def z1114 : W := mkw 0x004faafea8000000 0x0f5ffafffc000000

def z1115 : W := mkw 0x004f7fac8bfaa000 0x178fff0003fff000

def z1116 : W := mkw 0x004fbffea8000000 0x1ffffffffce3f1f8

def z1117 : W := mkw 0x004fbffea8202000 0x0f5ffffffc203000

def z1118 : W := mkw 0x100ef4f803f20d50 0x1faffff803fffff8

def z1119 : W := mkw 0x004ea0fea8000000 0x0f5fe7fffc000000

def z1120 : W := mkw 0x8800805100040204 0xfffbd8d7031c0e07

def z1121 : W := mkw 0x000f7f0003faa000 0x108ffd0003fff000

def z1122 : W := mkw 0x9801ca5321440644 0xfffbdad7335c0e67

def z1123 : W := mkw 0x00036b000168a000 0x178fff0003fff000

def z1124 : W := mkw 0xba11ca53314cc665 0xfffbfbdf3f5cce67

def z1125 : W := mkw 0x00419f56a8000000 0x0653df17fc000000

def z1126 : W := mkw 0x100ef5f803f22d50 0x1b2fe0f803e00ff8

def z1127 : W := mkw 0x3211ca523148c461 0x1787e71030e3f060

def z1128 : W := mkw 0xcc2e35a5c2b72b86 0xfdfc1ce7c39f0f87

def z1129 : W := mkw 0x004fbffea8088000 0x0fdffffffc1cc000

def z1130 : W := mkw 0x100ee0f803e00d50 0x0a2be0f803600ff8

def z1131 : W := mkw 0x00419ffea8000000 0x0f5bdffffc000000

def z1132 : W := mkw 0x004fbf56a8000000 0x0f5fffd7fc000000

def z1133 : W := mkw 0x100ee0f803faad50 0x1fafe7f803fffff8

def z1134 : W := mkw 0xba11ca53314cc665 0xfffbdaffff5cce67

def z1135 : W := mkw 0x1002600003e00d50 0x1223e00003e00ff8

def z1136 : W := mkw 0x100ee0f801400d50 0x1b2fe0f803400ff8

def z1137 : W := mkw 0x104fbffea8000440 0x0f7ffffffc000e60

def z1138 : W := mkw 0x00014a0003faa000 0x108bd80003fff000

def z1139 : W := mkw 0x000f7f0483faa000 0x17dfff07c3fff000

def z1140 : W := mkw 0x000f7f0003faa000 0x128bfb0003fff000

def z1141 : W := mkw 0x100ef4f803f20d50 0x1b2ff8f803fc0ff8

def z1142 : W := mkw 0x8c2c14a582960b04 0xe87818c7031c0e07

def z1143 : W := mkw 0x000f6b0003faa000 0x138fe30003fff000

def z1144 : W := mkw 0x004fbffea8000000 0x1fdffffffc830000

def z1145 : W := mkw 0xc800000140050286 0xfdf818e7c31c0f87

def z1146 : W := mkw 0xcc2c14a5c2970b86 0xed7c1ce7c31c0f87

def z1147 : W := mkw 0x880c14a102960b04 0xfdfc1ce7039f0f87

def z1148 : W := mkw 0x100cc0f803c00d50 0x1b2fc0f803c00ff8

def z1149 : W := mkw 0xec611f07fc1752af 0xe4d01f07fc1ff007

def z1150 : W := mkw 0x8c20140580160204 0xfdf818c7031c0e07

def z1151 : W := mkw 0x442e34acc2b30992 0x00040420c0830180

def z1152 : W := mkw 0x104ef5fc8bf22d50 0x1b2fe5f8cfe33ff8

def z1153 : W := mkw 0xba11ca53314cc665 0xffffffd7335cce67

def z1154 : W := mkw 0x100ee0f801400440 0x1b2fe0f803e00ff8

def z1155 : W := mkw 0xcc2000a5c2970b86 0xfdf818e7c39f0f87

def z1156 : W := mkw 0x100080f800000d50 0x0b2bc0f800000ff8

def z1157 : W := mkw 0x1002e0f801600d50 0x0823c0f800000ff8

def z1158 : W := mkw 0x004fbffea8000000 0x0b5ff8fffc000000

def z1159 : W := mkw 0x00036b00017aa000 0x0283e300007ff000

def z1160 : W := mkw 0xba11ca53314cc665 0xe05bd8c7331c0e07

def z1161 : W := mkw 0x442e34acc2930982 0x00042428c0830180

def z1162 : W := mkw 0x100ef5f803faad50 0x1bafe5f803fffff8

def z1163 : W := mkw 0xba11ca53314cc665 0xffffdef7f35cce67

def z1164 : W := mkw 0x000f7fa483faa000 0x179fffc703fff000

def z1165 : W := mkw 0x100ea0f802800d50 0x1b2fe0f803800ff8

def z1166 : W := mkw 0x10015f0003faad50 0x14a01f0003fffff8

def z1167 : W := mkw 0xba11ca53314cc665 0xefdbdad7331cce07

def z1168 : W := mkw 0x004eb5fea8000000 0x0b5fe5fffc000000

def z1169 : W := mkw 0x004f7fac8bfaa000 0x1fcfff38fffff000

def z1170 : W := mkw 0x004fbffea8000900 0x0f7ffffffc000f80

def z1171 : W := mkw 0x104ef4feabe00d50 0x1f7ffcffffe00ff8

def z1172 : W := mkw 0xcc20000140050b86 0xfdf818c7031c0f87

def z1173 : W := mkw 0xfa104001554dd6ef 0xf0a00000035ccfff

def z1174 : W := mkw 0x8c20000102960b04 0xfdf818c7031c0e07

def z1175 : W := mkw 0xfa108053740556ef 0xe87000d730000fff

def z1176 : W := mkw 0xea110a03740dd2af 0xe4d01a07fc1cc007

def z1177 : W := mkw 0x100cc0f003e00d50 0x1b2fc0f003e00ff8

def z1178 : W := mkw 0x880c00a100040204 0xfdfc18e7031c0e07

def z1179 : W := mkw 0x000f7fa483faa900 0x1fffffe7c3ffff80

def z1180 : W := mkw 0x000e600003faa000 0x108bc00003fff000

def z1181 : W := mkw 0x004fbffea8000000 0x1fdffffffc40c000

def z1182 : W := mkw 0xcc2c14a5c0170286 0xfdfc1ce7c31f0e07

def z1183 : W := mkw 0xcc2c14a5c6971b8e 0xfdfc1de7cf9f3f87

def z1184 : W := mkw 0xcc2c14a5c2970b86 0xfdfc3de7c3bf3f87

def z1185 : W := mkw 0xcc2c14a5c2b70b96 0xfdfc1ce7c3bf0f9f

def z1186 : W := mkw 0x9a11ca53214c8644 0xfffbd8d7035c0e67

def z1187 : W := mkw 0x9a11ca53214c8644 0xfffbdac7035cce07

def z1188 : W := mkw 0xba118a5330044665 0xfffbdad7331c0e67

def z1189 : W := mkw 0x000f7f0003faa000 0x138ff80003fff000

def z1190 : W := mkw 0x104ef5fc8be00d50 0x1b2fe0f803e00ff8

def z1191 : W := mkw 0x00037f00017aa000 0x1787ff0000fff000

def z1192 : W := mkw 0x004fbffeaa800000 0x1f5fffffff800000

def z1193 : W := mkw 0x8800140580040204 0xfdf81cc7c31c0e07

def z1194 : W := mkw 0xcc2c14a5c2970b86 0xfffc3fe7c39f0f87

def z1195 : W := mkw 0xba11ca53314cc665 0xe6dbdad7335cce67

def z1196 : W := mkw 0x9a11ca53214c8644 0xfffbdad7331c0e07

def z1197 : W := mkw 0x004fbffea8000000 0x065bffdffc000000

def z1198 : W := mkw 0xcc200005c0050286 0xfdf818c7c31c0e07

def z1199 : W := mkw 0x000f7f0003faa000 0x17afff0003fff1f8

def z1200 : W := mkw 0x000f7fa483faa000 0x1fdffffffffff000

def z1201 : W := mkw 0x3213ea523168c461 0x0203e2103060c060

def z1202 : W := mkw 0x00419f56a8000000 0x0f5ffffffc000000

def z1203 : W := mkw 0x004fbffeaa920900 0x1fffffffff9f0f80

def z1204 : W := mkw 0x880c140100040204 0xfdfc1cc7031c0e07

def z1205 : W := mkw 0x100ee0f803f22d50 0x1b2fe0f803e33ff8

def z1206 : W := mkw 0x104fbffea8000d50 0x0f5ffffffc000e00

def z1207 : W := mkw 0x3213eb523148c461 0x0203e3103040c060

def z1208 : W := mkw 0x004d9efea8000000 0x0f5fdefffc000000

def z1209 : W := mkw 0x442e34acc6b3199a 0x00042528cca33198

def z1210 : W := mkw 0xcc2c14a5c2970b86 0xe03818c7031c0f87

def z1211 : W := mkw 0xcc2c14a5c2970b86 0xe87c1ce7c39f0f87

def z1212 : W := mkw 0xaa114a03314cc225 0xfffbdac7335cce07

def z1213 : W := mkw 0xba11ca53314cc665 0xfffffffffffffe67

def z1214 : W := mkw 0xa8018a5330044225 0xfffbdad7335cce67

def z1215 : W := mkw 0x000e750003faa000 0x138fe50003fff000

def z1216 : W := mkw 0xba11ca53314cc665 0xfffbdad733fffe67

def z1217 : W := mkw 0x446e35accab30992 0x00042528cca30198

def z1218 : W := mkw 0x100ee0f803e00d50 0x082fe0f803a00ff8

def z1219 : W := mkw 0xba11ca53314cc665 0xef7bdad7331c0e67

def z1220 : W := mkw 0x00418afea8000000 0x085bd8fffc000000

def z1221 : W := mkw 0xcc2c14a5c2970b86 0xf5dc1cc7c39f0e07

def z1222 : W := mkw 0x8c2000a580040b04 0xfdf818c7031c0e07

def z1223 : W := mkw 0xba11ca53316ce665 0xfffbdad7337cfe67

def z1224 : W := mkw 0xea111f03741ff2af 0xe4d01f07fc1ff007

def z1225 : W := mkw 0x0000400003faa000 0x138bc00003fff000

def z1226 : W := mkw 0xcc2c14a5c2970b86 0xfdf81cc7c31f0e07

def z1227 : W := mkw 0x8801ca53214c8204 0xfffbdad7335cce07

def z1228 : W := mkw 0x3213eb523168e461 0x0203c2103040c060

def z1229 : W := mkw 0xba51cb53394cc665 0xfffbdbd73f5cce67

def z1230 : W := mkw 0x000f7f0003faa000 0x1fafff2003fff180

def z1231 : W := mkw 0x8800000102960204 0xfdf818c7039f0e07

def z1232 : W := mkw 0xba11ca53314cc665 0xfb7bd8d7335c0e67

def z1233 : W := mkw 0x004fbffea8000000 0x0f5bdafffc000000

def z1234 : W := mkw 0x104fbffeaa800d50 0x1f7fffffff800ff8

def z1235 : W := mkw 0xcc2c14a5c2970b86 0xfffc3cffc39f0f87

def z1236 : W := mkw 0xcc6c15a5ca970b86 0xfdfc1de7cf9f0f87

def z1237 : W := mkw 0x446e35acca930982 0x00040420c0830180

def z1238 : W := mkw 0xcc2e35a5c2970b86 0xfdfc3de7c39f0f87

def z1239 : W := mkw 0x1002e0f801600d50 0x1b27e0f800e00ff8

def z1240 : W := mkw 0x004f7f048bfaa000 0x178fff00cffff000

def z1241 : W := mkw 0x3211ca523548d469 0x0203c2183c40c078

def z1242 : W := mkw 0x100ef4f803faad50 0x1faffcf803fffff8

def z1243 : W := mkw 0x00037f00017aa000 0x0483df00001ff000

def z1244 : W := mkw 0x1002a0f800000d50 0x0a23e0f800000ff8

def z1245 : W := mkw 0x004f7f080bfaa000 0x178fff080ffff000

def z1246 : W := mkw 0x00037f0003faa000 0x1683ff0003fff000

def z1247 : W := mkw 0x100ee0f803e00d50 0x192fc0e003e00ff8

def z1248 : W := mkw 0x100cc0f003c00d40 0x1b2fe0f803e00ff8

def z1249 : W := mkw 0x00036b0003faa000 0x1787e70003fff000

def z1250 : W := mkw 0x3211ca523168c471 0x0203c2103060c078

def z1251 : W := mkw 0x004fbffea8000000 0x0f5ffffffca00198

def z1252 : W := mkw 0x442e35acc2b32992 0x00042528c0a33198

def z1253 : W := mkw 0xcc2c14a5c2970b86 0xfdf818c7039f0f87

def z1254 : W := mkw 0x0043ab5ea8000000 0x0253e31ffc000000

def z1255 : W := mkw 0x000f3f00001aa000 0x178fff0000fff000

def z1256 : W := mkw 0xcc2c14a5c6971b8e 0xfdfc1ce7c3bf3f9f

def z1257 : W := mkw 0x004fbffea8000000 0x1f7ffffffc800180

def z1258 : W := mkw 0x100ef4fc83e00d50 0x1b3ff8ff03e00ff8

def z1259 : W := mkw 0xcc2c14a5c2970b86 0xfffc1cf7c3df0fe7

def z1260 : W := mkw 0x104fbffea8000d50 0x1f7ffffffce00ff8

def z1261 : W := mkw 0x004fbffea8000000 0x1f5ffffffce00000

def z1262 : W := mkw 0xcc2c14adc2970b96 0xfdfc1cefc39f0f9f

def z1263 : W := mkw 0xba51ca5b394cc665 0xfffbdadf3f5cce67

def z1264 : W := mkw 0xba11cb53314ce665 0xfffbdbd7335cfe67

def z1265 : W := mkw 0xcc2c14a5c6971b8e 0xfffc3dffcfff3fff

def z1266 : W := mkw 0xcc2c14a5c2970b86 0xfffc3ce7c3ff0f87

def z1267 : W := mkw 0x00014a0003faa000 0x178fff0003fff000

def z1268 : W := mkw 0xcc2c14a5c6971b8e 0xfffc3fffffbf3f9f

def z1269 : W := mkw 0x000d5e0003da8000 0x178fff0003fff000

def z1270 : W := mkw 0x00037f00017aa000 0x178bff00037ff000

def z1271 : W := mkw 0x1000c0f803faad50 0x18a000f803fffff8

def z1272 : W := mkw 0x1002e05803e00d50 0x1b2be0d803e00ff8

def z1273 : W := mkw 0xcc2e35adc2b72b96 0xfdfc3defc3bf3f9f

def z1274 : W := mkw 0xaa118a53300cc225 0xfffbdad7331cce07

def z1275 : W := mkw 0x000f6a0003faa000 0x178ffa0003fff000

def z1276 : W := mkw 0xfa104001554dd6ef 0xf0a00000035ffe67

def z1277 : W := mkw 0xfa10400157eddfff 0xf0a0000003ffffff

def z1278 : W := mkw 0x0043bf5ea8000000 0x0453df07fc000000

def z1279 : W := mkw 0xba10c05331444665 0xfffbd8d7335c0e67

def z1280 : W := mkw 0x0043abfea8000000 0x0f57e7fffc000000

def z1281 : W := mkw 0xba11ca53314cc665 0xecfbdad7331cce67

def z1282 : W := mkw 0x00411f06a8000000 0x075bdf07fc000000

def z1283 : W := mkw 0x325ffffeb948c461 0x0207e738fc40c060

def z1284 : W := mkw 0xba11ca53314cc665 0xffffdaf733dccfe7

def z1285 : W := mkw 0xba11ca53314cc665 0xfffffad733fcce67

def z1286 : W := mkw 0x004fabfea8000000 0x0b5fe3fffc000000

def z1287 : W := mkw 0x3213eb523568f469 0x0203e3183c60f078

def z1288 : W := mkw 0xcc2c14a5c0050b86 0xfdfc1ce7c31c0f87

def z1289 : W := mkw 0x000f7f0003faa000 0x1fcfff1033fff000

def z1290 : W := mkw 0x000d9ef6a0000000 0x0f5ffffffc000000

def z1291 : W := mkw 0x1000c05001400d50 0x1b2bc0d003400ff8

def z1292 : W := mkw 0x446e35acce93198a 0x00042528cca33198

def z1293 : W := mkw 0x104ee0fc8be00d50 0x1b2fe0f8cfe00ff8

def z1294 : W := mkw 0xba11ca53314cc665 0xf8fbd8d7335cce67

def z1295 : W := mkw 0x000f7f0003faa000 0x158fdf00039ff000

def z1296 : W := mkw 0xba11ca53314cc665 0xe03bd8c7031c0e67

def z1297 : W := mkw 0x004fbffea8000000 0x005bd8c7fc000000

def z1298 : W := mkw 0x004f3faea8000000 0x075fff2ffc000000

def z1299 : W := mkw 0x000e600003faa000 0x178fe70003fff000

def z1300 : W := mkw 0x000faafa20000000 0x0f5ffffffc000000

def z1301 : W := mkw 0x100ee0f803e88d50 0x1bafe0f803fccff8

def z1302 : W := mkw 0x000f3fa480000000 0x0f5ffffffc000000

def z1303 : W := mkw 0x1000c05001400440 0x1b2bc0d003e00ff8

def z1304 : W := mkw 0x104ee0fa2be00d50 0x1b2fe0f83fe00ff8

def z1305 : W := mkw 0x000f7f0003faa000 0x008bd800031ff000

def z1306 : W := mkw 0x100ee0f803e00d50 0x102fe0e803e00ff8

def z1307 : W := mkw 0x104ee1f80be00d50 0x1b2fe1f80fe00ff8

def z1308 : W := mkw 0xfc2080fdd4055fff 0xe87000fffc000fff

def z1309 : W := mkw 0x3211ca523548d469 0x0203c3103c40f060

def z1310 : W := mkw 0x000f7f0003faa000 0x1fefff38fffff1f8

def z1311 : W := mkw 0x004fbffea8000000 0x0d5fdfe7fc000000

def z1312 : W := mkw 0x004fbffea8000000 0x0fdffffffc03f000

def z1313 : W := mkw 0x000e740003f20000 0x178fff0003fff000

def z1314 : W := mkw 0x142ef4fc83f20d50 0x1b2fe0f803e00ff8

def z1315 : W := mkw 0xcc2c14a5c2970b86 0xf5bc1cc7039f0f87

def z1316 : W := mkw 0x004fbffea8000000 0x0f7ffffffc0001f8

def z1317 : W := mkw 0xba11ca53314cc665 0xe09bd8c7031cce07

def z1318 : W := mkw 0x3251cb523948c461 0x0203c3103c40c060

def z1319 : W := mkw 0x446e35accab32982 0x00042528cca33180

def z1320 : W := mkw 0x104ee0feabe00d50 0x1b3fe0ff03e00ff8

def z1321 : W := mkw 0xcc2c00a142970b86 0xfdfc18e7039f0f87

def z1322 : W := mkw 0x004fbf5ea8000000 0x075fff1ffc000000

def z1323 : W := mkw 0x004fbffea8000000 0x0f5ffffffc600078

def z1324 : W := mkw 0x00415f06abfaa000 0x14d01f07fffff000

def z1325 : W := mkw 0x000f3f0002920000 0x178fff0003fff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z8,z3,z9,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z10]),(0,[z0,z11,z1,z8,z3,z5,z6])],[(0,[z12,z13,z1,z8,z3,z5,z6]),(0,[z0,z1,z14,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z15,z6]),(0,[z0,z16,z8,z2,z3,z5,z6]),(0,[z0,z1,z17,z8,z18,z3,z6])],[(0,[z19,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z20,z8,z3,z5,z6]),(0,[z12,z1,z8,z3,z21,z5,z6]),(0,[z22,z1,z8,z3,z23,z5,z6]),(0,[z0,z1,z8,z24,z3,z5,z6]),(0,[z25,z0,z1,z8,z3,z5,z6]),(1,[z26,z0,z8,z3,z27,z6])],[(1,[z7,z0,z8,z9,z5,z6]),(0,[z0,z16,z1,z8,z28,z3,z5])],[(0,[z29,z0,z30,z8,z3,z5,z6]),(0,[z29,z0,z31,z8,z3,z5,z6]),(0,[z0,z8,z2,z3,z32,z5,z6]),(0,[z7,z0,z1,z8,z3,z33,z6]),(0,[z34,z35,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z36,z37]),(0,[z0,z1,z8,z3,z5,z6,z38]),(0,[z0,z1,z8,z39,z3,z40,z6]),(0,[z41,z0,z1,z8,z3,z42,z5])],[(0,[z43,z0,z1,z8,z3,z5,z44])],[(0,[z0,z1,z45,z8,z3,z5,z6]),(1,[z0,z1,z46,z3,z5,z6]),(1,[z0,z1,z8,z47,z3,z5]),(0,[z48,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z49,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z42,z50])],[(0,[z13,z0,z1,z45,z3,z5,z6]),(0,[z51,z0,z1,z8,z3,z5,z6]),(0,[z0,z8,z3,z32,z5,z27,z6]),(0,[z0,z1,z8,z3,z52,z5,z6]),(0,[z0,z1,z8,z53,z3,z5,z54]),(0,[z55,z0,z1,z8,z28,z3,z5])]],
   [[(0,[z12,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z56,z6]),(0,[z0,z1,z8,z57,z3,z5,z6]),(0,[z0,z1,z58,z8,z3,z5,z6]),(0,[z0,z1,z8,z59,z3,z42,z5]),(0,[z0,z60,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z61])],[(0,[z0,z62,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z64])],[(1,[z12,z1,z45,z3,z5,z6]),(0,[z0,z65,z1,z8,z3,z5,z6]),(1,[z66,z1,z8,z3,z5,z6])],[(0,[z67,z1,z8,z3,z5,z6,z68]),(0,[z0,z1,z69,z8,z28,z3,z5])],[(0,[z29,z0,z1,z8,z3,z5,z6]),(0,[z70,z0,z1,z8,z21,z5,z6]),(0,[z0,z1,z71,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z54]),(0,[z0,z1,z8,z3,z72,z5,z6]),(0,[z0,z1,z8,z73,z3,z5,z6])],[(0,[z0,z1,z46,z8,z3,z5,z6]),(0,[z74,z0,z1,z8,z3,z23,z6]),(0,[z75,z0,z76,z8,z3,z5,z6]),(0,[z75,z0,z1,z8,z28,z3,z5])],[(1,[z0,z1,z8,z3,z77,z5]),(0,[z0,z1,z8,z3,z78,z5,z6])],[(0,[z0,z1,z8,z3,z79,z5,z6]),(0,[z0,z1,z8,z3,z3,z5,z6]),(1,[z74,z1,z8,z3,z80,z6]),(0,[z81,z0,z1,z8,z3,z5,z82]),(0,[z0,z8,z3,z5,z83,z6,z82]),(0,[z0,z1,z8,z28,z18,z3,z6])]],
   [[(1,[z0,z1,z84,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z85]),(0,[z0,z1,z86,z58,z3,z5,z6]),(0,[z0,z1,z87,z8,z3,z5,z6]),(0,[z63,z0,z88,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z89,z6]),(1,[z0,z1,z8,z53,z3,z5])],[(0,[z0,z1,z8,z90,z3,z5,z6]),(0,[z0,z91,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z92,z3,z5,z6]),(1,[z0,z1,z93,z3,z5,z6]),(0,[z0,z94,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z50,z95,z6]),(0,[z0,z1,z96,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z97,z42,z5])],[(0,[z98,z0,z1,z8,z3,z5,z6]),(0,[z26,z0,z31,z8,z3,z5,z6]),(0,[z26,z0,z30,z8,z3,z5,z6]),(0,[z0,z1,z8,z99,z3,z5,z6]),(0,[z100,z0,z1,z8,z3,z5,z44]),(0,[z0,z1,z8,z101,z3,z5,z6]),(0,[z0,z1,z8,z3,z102,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z103])],[(0,[z67,z0,z8,z2,z3,z5,z6]),(0,[z0,z1,z84,z8,z3,z5,z6]),(0,[z104,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z105,z3,z5,z6]),(0,[z106,z0,z1,z8,z3,z5,z6])],[(0,[z0,z1,z107,z3,z108,z5,z6]),(0,[z109,z0,z1,z8,z3,z5,z6]),(0,[z12,z74,z1,z8,z3,z5,z6]),(0,[z0,z1,z45,z3,z108,z5,z6]),(0,[z0,z110,z1,z8,z3,z5,z6]),(0,[z0,z1,z17,z3,z5,z95,z6]),(0,[z111,z0,z1,z8,z18,z3,z6]),(0,[z0,z1,z8,z59,z112,z5,z6]),(0,[z0,z1,z8,z113,z3,z5,z6]),(0,[z0,z1,z8,z114,z3,z5,z6])],[(0,[z0,z1,z8,z3,z42,z5,z82]),(0,[z0,z1,z8,z3,z115,z5,z6])],[(1,[z0,z116,z8,z3,z5,z6]),(0,[z0,z1,z8,z117,z3,z5,z6]),(0,[z0,z1,z8,z3,z118,z5,z6]),(0,[z0,z1,z8,z3,z119,z5,z6])],[(0,[z0,z1,z8,z120,z3,z5,z6]),(0,[z0,z1,z86,z8,z3,z5,z6])]],
   [[(0,[z1,z8,z121,z3,z21,z5,z6]),(0,[z0,z1,z8,z3,z122,z5,z6]),(1,[z0,z1,z8,z3,z5,z123]),(0,[z124,z0,z1,z8,z3,z42,z5])],[(0,[z0,z1,z8,z3,z5,z125,z6]),(0,[z126,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z83]),(0,[z63,z0,z1,z8,z3,z5,z127]),(0,[z111,z0,z1,z8,z3,z95,z6]),(0,[z0,z1,z8,z3,z128,z5,z6])],[(0,[z0,z1,z8,z3,z5,z129,z6]),(1,[z74,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z3,z5,z44,z37]),(0,[z0,z1,z8,z3,z5,z6,z130]),(0,[z26,z0,z1,z8,z3,z5,z6]),(0,[z63,z131,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z132,z5,z6]),(0,[z0,z1,z8,z3,z133,z5,z6]),(0,[z0,z1,z8,z3,z134,z5,z6]),(0,[z0,z1,z8,z135,z3,z5,z6]),(1,[z0,z1,z8,z3,z42,z5]),(1,[z0,z1,z8,z28,z3,z42]),(0,[z136,z0,z1,z8,z28,z3,z5])],[(1,[z0,z1,z137,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z138,z6]),(0,[z74,z1,z8,z107,z3,z5,z6]),(0,[z0,z1,z8,z39,z128,z5,z6])],[(1,[z67,z30,z8,z3,z5,z6]),(0,[z75,z1,z8,z3,z23,z5,z6]),(0,[z0,z1,z8,z139,z3,z5,z6])],[(0,[z1,z31,z8,z3,z5,z6,z68]),(0,[z0,z1,z31,z8,z3,z42,z5]),(0,[z140,z0,z1,z8,z3,z42,z5]),(1,[z0,z1,z17,z3,z95,z6]),(0,[z0,z1,z8,z112,z3,z50,z6]),(0,[z141,z0,z1,z8,z3,z42,z5])],[(0,[z74,z0,z1,z8,z3,z42,z5]),(1,[z43,z1,z8,z3,z5,z44]),(0,[z0,z1,z142,z8,z3,z5,z6]),(0,[z0,z1,z143,z8,z3,z5,z6]),(0,[z66,z144,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z145,z3,z5,z27]),(1,[z0,z146,z8,z3,z5,z6]),(0,[z147,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z148,z8,z3,z5,z6])],[(0,[z22,z0,z149,z8,z3,z5,z6]),(1,[z0,z1,z8,z150,z3,z6]),(0,[z0,z1,z8,z151,z3,z5,z6]),(1,[z34,z0,z1,z3,z5,z36]),(0,[z0,z1,z8,z3,z5,z6,z152]),(0,[z0,z1,z8,z3,z5,z6,z153]),(0,[z0,z1,z154,z8,z3,z5,z6])]],
   [[(0,[z155,z0,z1,z8,z3,z5,z6]),(0,[z12,z0,z1,z107,z3,z5,z6]),(1,[z0,z1,z8,z3,z156,z6]),(0,[z157,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z158,z3,z5,z6]),(0,[z0,z1,z8,z159,z3,z5,z6]),(0,[z0,z1,z8,z160,z3,z5,z6]),(0,[z0,z1,z8,z161,z3,z5,z6]),(0,[z0,z1,z8,z3,z162,z42,z5])],[(0,[z0,z30,z8,z3,z32,z5,z6]),(0,[z0,z1,z8,z3,z163,z5,z6]),(0,[z164,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z165,z3,z5,z6]),(0,[z0,z1,z86,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z166,z5,z6]),(1,[z0,z1,z8,z112,z50,z6]),(0,[z0,z1,z8,z167,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z6,z168]),(0,[z0,z169,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z77,z5,z6]),(0,[z0,z1,z8,z3,z50,z23,z6]),(0,[z0,z1,z8,z3,z5,z6,z170]),(0,[z0,z1,z8,z3,z171,z6,z36]),(0,[z172,z0,z1,z8,z3,z5,z6])],[(0,[z13,z0,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z6,z173]),(0,[z0,z1,z8,z3,z5,z6,z174]),(1,[z0,z1,z175,z3,z5,z6])],[(0,[z176,z0,z1,z8,z3,z5,z6]),(0,[z34,z0,z177,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z178,z5,z6]),(0,[z140,z0,z144,z8,z3,z5,z6]),(0,[z0,z1,z86,z3,z108,z5,z6]),(1,[z0,z1,z8,z3,z5,z179]),(0,[z0,z1,z8,z28,z3,z32,z5]),(0,[z0,z1,z8,z3,z5,z6,z180]),(0,[z0,z1,z8,z181,z3,z5,z6]),(0,[z0,z1,z8,z28,z114,z3,z5])],[(0,[z0,z1,z8,z28,z3,z5,z80]),(0,[z75,z0,z1,z8,z18,z3,z6]),(0,[z0,z182,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z27,z6,z54]),(0,[z0,z1,z3,z5,z183,z6,z36]),(0,[z0,z1,z8,z184,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z185,z6]),(0,[z0,z1,z8,z3,z42,z5,z44]),(0,[z0,z1,z8,z3,z5,z27,z6]),(0,[z0,z1,z8,z3,z5,z6,z186])]],
   [[(0,[z0,z1,z76,z8,z3,z5,z6]),(1,[z140,z0,z2,z3,z5,z6]),(0,[z0,z1,z17,z8,z3,z42,z5])],[(0,[z22,z0,z1,z8,z3,z5,z6]),(0,[z0,z144,z1,z2,z3,z5,z6]),(1,[z187,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z37])],[(0,[z188,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z189,z3,z6,z36]),(0,[z0,z1,z8,z112,z3,z5,z123])],[(0,[z0,z1,z8,z3,z190,z5,z6]),(0,[z0,z1,z8,z191,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z192,z6])],[(1,[z0,z1,z20,z3,z5,z6]),(0,[z193,z0,z1,z8,z3,z5,z6]),(0,[z43,z1,z8,z107,z3,z5,z6]),(0,[z75,z0,z1,z8,z3,z80,z6]),(0,[z194,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z112,z3,z42,z5])],[(0,[z195,z0,z1,z8,z3,z5,z6]),(0,[z22,z1,z8,z3,z21,z5,z6]),(0,[z0,z1,z8,z3,z5,z196,z6]),(0,[z0,z197,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z198,z3,z5,z6]),(0,[z199,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z200])],[(0,[z0,z1,z8,z3,z21,z42,z5]),(0,[z70,z0,z1,z8,z121,z5,z6]),(1,[z0,z144,z86,z3,z5,z6]),(0,[z0,z201,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z202,z3,z5,z95])],[(0,[z0,z30,z1,z8,z3,z5,z6]),(0,[z74,z0,z1,z8,z3,z42,z6]),(0,[z43,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z28,z3,z5,z203])]],
   [[(0,[z0,z1,z8,z3,z204,z5,z6]),(0,[z0,z1,z8,z3,z205,z5,z6]),(0,[z0,z1,z8,z206,z3,z5,z6])],[(0,[z207,z0,z1,z8,z3,z5,z6]),(0,[z67,z1,z45,z8,z3,z5,z6]),(0,[z0,z1,z8,z107,z3,z42,z5]),(0,[z0,z1,z8,z47,z3,z5,z6]),(1,[z0,z208,z8,z3,z5,z6]),(0,[z63,z209,z1,z8,z3,z5,z6])],[(0,[z210,z0,z1,z8,z3,z5,z6]),(0,[z211,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z95])],[(0,[z0,z1,z8,z212,z3,z5,z6]),(0,[z74,z1,z8,z3,z5,z80,z6]),(0,[z0,z1,z8,z3,z213,z5,z6]),(0,[z0,z1,z214,z8,z3,z5,z6]),(0,[z0,z1,z8,z215,z3,z5,z6])],[(0,[z216,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z217,z8,z3,z5,z6]),(0,[z218,z0,z1,z8,z3,z5,z6]),(1,[z0,z219,z8,z3,z5,z6]),(0,[z0,z1,z220,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z221]),(0,[z0,z1,z8,z222,z3,z5,z37]),(0,[z0,z1,z8,z3,z223,z5,z6])],[(0,[z140,z0,z1,z107,z3,z5,z6]),(0,[z12,z0,z224,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z225,z5,z6]),(0,[z0,z1,z8,z3,z5,z179,z6]),(1,[z0,z1,z8,z3,z5,z226])],[(0,[z0,z8,z191,z3,z32,z5,z6]),(0,[z209,z0,z1,z8,z3,z5,z6]),(1,[z0,z227,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z42,z5]),(0,[z0,z1,z8,z18,z3,z6,z203])],[(0,[z228,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z229]),(1,[z0,z1,z214,z3,z5,z6]),(0,[z0,z1,z8,z230,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z32,z6]),(0,[z0,z197,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z231,z5,z6])]],
   [[(0,[z0,z232,z1,z8,z3,z5,z6]),(0,[z100,z0,z116,z8,z3,z5,z6]),(0,[z7,z0,z1,z8,z3,z42,z5])],[(0,[z0,z1,z17,z8,z3,z42,z6]),(0,[z0,z1,z8,z233,z3,z5,z6]),(0,[z0,z1,z8,z234,z3,z5,z6]),(0,[z0,z1,z8,z235,z28,z3,z5]),(0,[z236,z0,z1,z8,z28,z3,z5])],[(0,[z1,z45,z8,z107,z3,z5,z6]),(0,[z0,z1,z8,z237,z3,z5,z6]),(0,[z0,z16,z1,z8,z191,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z238]),(1,[z0,z1,z8,z222,z5,z37])],[(0,[z0,z1,z8,z3,z239,z5,z6]),(0,[z240,z0,z1,z8,z3,z5,z6]),(0,[z1,z8,z107,z3,z23,z5,z6]),(0,[z0,z1,z8,z3,z241,z5,z6]),(0,[z70,z0,z1,z8,z28,z3,z5]),(0,[z111,z0,z1,z8,z3,z42,z5]),(0,[z242,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z128,z5])],[(0,[z0,z144,z1,z45,z3,z5,z6]),(0,[z0,z1,z8,z3,z23,z5,z6]),(0,[z75,z0,z1,z8,z3,z23,z6]),(0,[z100,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z243,z6]),(0,[z244,z0,z1,z8,z3,z5,z6]),(0,[z0,z245,z1,z8,z3,z5,z6]),(0,[z246,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z247,z3,z5,z6]),(0,[z0,z1,z8,z59,z3,z50,z6])],[(0,[z0,z1,z248,z8,z3,z5,z6]),(0,[z26,z0,z197,z8,z3,z5,z6]),(0,[z0,z197,z1,z158,z3,z5,z6]),(1,[z0,z197,z8,z3,z32,z6]),(0,[z41,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z249])],[(0,[z0,z1,z8,z3,z250,z5,z6]),(0,[z251,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z252,z3,z5,z6]),(0,[z0,z1,z8,z253,z3,z6,z82]),(0,[z0,z1,z8,z3,z5,z95,z6]),(0,[z0,z1,z8,z59,z5,z6,z54])],[(0,[z22,z74,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z254,z3,z5,z6]),(1,[z0,z1,z255,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z256]),(0,[z0,z1,z8,z3,z42,z5,z27]),(0,[z0,z1,z8,z3,z5,z6,z257]),(0,[z0,z1,z258,z8,z3,z5,z6])]],
   [[(0,[z259,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z17,z107,z3,z5,z6]),(1,[z0,z1,z260,z3,z5,z6]),(0,[z74,z0,z1,z8,z3,z80,z6]),(0,[z261,z0,z1,z8,z3,z5,z6]),(0,[z34,z0,z1,z262,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z263])],[(0,[z12,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z264,z6]),(0,[z0,z1,z265,z8,z3,z5,z6]),(0,[z7,z0,z1,z175,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z266]),(0,[z0,z1,z8,z59,z3,z5,z6]),(0,[z0,z1,z8,z267,z3,z5,z6]),(0,[z228,z0,z1,z8,z3,z42,z5])],[(0,[z0,z94,z31,z8,z3,z5,z6]),(1,[z75,z1,z8,z3,z23,z6]),(0,[z0,z1,z58,z268,z3,z5,z6]),(1,[z0,z11,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z36]),(0,[z269,z0,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z270,z6]),(0,[z0,z1,z8,z3,z5,z271,z6])],[(0,[z272,z0,z1,z8,z3,z5,z6]),(1,[z70,z1,z8,z121,z5,z6]),(0,[z81,z0,z94,z8,z3,z5,z6]),(0,[z81,z0,z1,z57,z3,z5,z6]),(0,[z0,z1,z8,z3,z273,z5,z95])],[(0,[z274,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z275,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z276,z6]),(0,[z0,z1,z8,z3,z95,z6,z54]),(0,[z0,z1,z8,z3,z4,z6,z54]),(0,[z277,z0,z1,z8,z3,z5,z6]),(0,[z0,z278,z1,z8,z3,z42,z5])],[(0,[z279,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z108,z5]),(0,[z0,z1,z8,z280,z3,z5,z6]),(1,[z0,z1,z8,z3,z40,z6])],[(1,[z0,z224,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z281]),(0,[z0,z1,z8,z3,z5,z282,z6]),(0,[z0,z1,z8,z3,z5,z6,z37]),(0,[z0,z1,z8,z28,z3,z42,z6])]],
   [[(0,[z67,z70,z1,z8,z3,z5,z6]),(0,[z0,z1,z262,z2,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z42,z6]),(0,[z0,z1,z8,z283,z3,z5,z6]),(0,[z0,z1,z8,z50,z5,z6,z54])],[(1,[z0,z149,z8,z3,z5,z6]),(0,[z0,z1,z8,z284,z3,z5,z6]),(0,[z0,z16,z8,z191,z3,z5,z6]),(0,[z197,z201,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z8,z28,z3,z5]),(0,[z0,z227,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z285,z5,z6])],[(0,[z74,z1,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z286]),(0,[z0,z1,z8,z3,z97,z5,z6]),(0,[z0,z94,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z287,z5,z6])],[(0,[z0,z1,z8,z3,z288,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z36]),(0,[z0,z1,z8,z3,z5,z183,z6]),(0,[z0,z1,z8,z3,z5,z6,z289])],[(0,[z0,z1,z8,z3,z5,z290,z6]),(0,[z63,z0,z1,z8,z268,z5,z6]),(0,[z63,z0,z1,z8,z108,z5,z6]),(0,[z0,z1,z58,z8,z28,z3,z5]),(0,[z111,z0,z1,z8,z3,z42,z6]),(1,[z0,z1,z8,z3,z42,z54])],[(0,[z0,z1,z8,z3,z5,z291,z6]),(0,[z12,z0,z1,z86,z3,z5,z6]),(0,[z75,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z68,z37]),(0,[z0,z1,z8,z3,z292,z5,z6]),(0,[z0,z1,z8,z293,z3,z5,z6]),(0,[z0,z1,z8,z294,z3,z5,z6])],[(0,[z140,z0,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z295,z6]),(0,[z140,z0,z30,z8,z3,z5,z6]),(0,[z0,z1,z296,z8,z3,z5,z6]),(0,[z0,z144,z94,z8,z3,z5,z6]),(0,[z81,z0,z1,z8,z28,z3,z5]),(1,[z0,z1,z8,z3,z297,z6])],[(0,[z67,z29,z1,z8,z3,z5,z6]),(0,[z298,z0,z1,z8,z3,z5,z6]),(0,[z299,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z300,z6]),(0,[z7,z0,z1,z8,z9,z5,z6]),(0,[z0,z1,z8,z3,z5,z301,z6]),(0,[z302,z0,z1,z8,z3,z5,z6])]],
   [[(0,[z0,z30,z16,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z32,z5,z6]),(0,[z0,z1,z303,z8,z3,z5,z6]),(0,[z0,z304,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z6,z305]),(0,[z124,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z306,z3,z5,z6]),(0,[z0,z1,z8,z3,z128,z5,z68]),(0,[z0,z1,z8,z3,z5,z6,z307]),(0,[z0,z1,z8,z3,z89,z5,z6]),(1,[z63,z0,z1,z108,z5,z6])],[(0,[z308,z0,z1,z8,z3,z5,z6]),(0,[z309,z197,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z310,z5,z6]),(0,[z0,z1,z8,z311,z3,z5,z6])],[(1,[z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z137,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z312]),(0,[z313,z0,z1,z8,z3,z5,z6]),(0,[z314,z0,z1,z8,z3,z42,z5])],[(0,[z0,z1,z8,z315,z3,z5,z6]),(0,[z316,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z317,z3,z5,z6])],[(0,[z0,z1,z8,z318,z3,z5,z6]),(0,[z0,z1,z8,z3,z50,z80,z6]),(0,[z0,z1,z8,z3,z5,z226,z6]),(0,[z0,z1,z268,z3,z108,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z183]),(0,[z0,z1,z8,z39,z28,z3,z5])],[(0,[z0,z1,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z319,z5,z6]),(0,[z140,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z255,z8,z3,z5,z6]),(0,[z141,z0,z1,z8,z3,z5,z6])],[(0,[z74,z0,z1,z8,z3,z5,z6]),(0,[z320,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z321,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z322,z54]),(0,[z0,z323,z1,z8,z3,z5,z6])]],
   [[(0,[z0,z1,z8,z3,z324,z5,z6]),(0,[z67,z0,z1,z8,z28,z3,z5]),(0,[z0,z224,z1,z8,z3,z5,z6]),(0,[z0,z144,z1,z8,z28,z3,z5]),(0,[z0,z325,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z158,z3,z5,z6])],[(0,[z326,z0,z1,z8,z3,z5,z6]),(0,[z22,z0,z1,z260,z3,z5,z6]),(0,[z0,z1,z8,z3,z162,z5,z6]),(0,[z327,z0,z1,z8,z3,z5,z6]),(0,[z81,z0,z8,z3,z5,z6,z82]),(0,[z0,z1,z8,z328,z3,z5,z6]),(1,[z0,z1,z8,z3,z273,z5]),(0,[z0,z1,z8,z28,z3,z50,z5]),(0,[z0,z1,z8,z39,z222,z5,z6]),(0,[z0,z1,z8,z329,z3,z5,z6])],[(0,[z67,z30,z1,z8,z3,z5,z6])],[(0,[z43,z1,z31,z8,z3,z5,z6]),(1,[z0,z330,z8,z3,z5,z6]),(0,[z144,z187,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z175,z3,z5,z6]),(0,[z0,z1,z8,z3,z331,z5,z6]),(1,[z0,z1,z8,z3,z5,z332])],[(0,[z26,z0,z8,z2,z3,z5,z6]),(0,[z0,z333,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z222,z3,z42,z5])],[(0,[z334,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z45,z262,z3,z5,z6]),(0,[z0,z1,z8,z3,z335,z5,z6]),(0,[z0,z1,z336,z8,z3,z5,z6]),(0,[z43,z0,z1,z8,z3,z5,z68]),(0,[z0,z1,z8,z337,z3,z5,z6]),(0,[z7,z0,z1,z255,z3,z5,z6]),(1,[z111,z0,z1,z8,z3,z42]),(0,[z338,z0,z1,z8,z3,z5,z6])],[(0,[z0,z1,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z121,z3,z5]),(0,[z0,z1,z339,z8,z3,z5,z6]),(0,[z75,z0,z1,z8,z3,z42,z6]),(0,[z0,z8,z2,z3,z9,z5,z6]),(0,[z34,z0,z1,z8,z3,z5,z36]),(0,[z0,z1,z8,z28,z3,z5,z5])],[(0,[z0,z1,z8,z340,z3,z5,z6]),(0,[z0,z1,z8,z28,z191,z3,z5]),(1,[z0,z1,z8,z202,z3,z5]),(1,[z277,z1,z8,z3,z5,z6]),(0,[z0,z341,z1,z8,z3,z5,z6])]],
   [[(0,[z13,z1,z8,z107,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z342]),(0,[z0,z1,z58,z2,z3,z5,z6]),(0,[z0,z144,z8,z3,z9,z5,z6]),(1,[z0,z1,z8,z3,z5,z343]),(1,[z309,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z108,z42,z5]),(0,[z0,z1,z8,z3,z5,z6,z36])],[(0,[z0,z1,z8,z344,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z6,z82]),(0,[z0,z1,z8,z3,z345,z5,z6]),(0,[z0,z1,z8,z3,z128,z5,z82]),(0,[z0,z1,z17,z8,z3,z5,z6]),(0,[z0,z1,z8,z222,z3,z128,z5])],[(0,[z0,z1,z8,z3,z346,z5,z6]),(1,[z0,z1,z8,z3,z5,z347]),(0,[z348,z0,z1,z8,z3,z5,z6]),(0,[z140,z0,z1,z86,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z349,z6]),(0,[z0,z197,z8,z3,z32,z5,z6]),(0,[z0,z1,z8,z3,z350,z5,z6])],[(0,[z13,z0,z1,z8,z3,z42,z5]),(0,[z0,z144,z8,z3,z5,z6,z82]),(0,[z7,z0,z8,z3,z32,z5,z6]),(0,[z111,z0,z11,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z4,z5])],[(0,[z70,z1,z31,z8,z3,z5,z6]),(0,[z351,z0,z1,z8,z3,z5,z6]),(0,[z75,z0,z208,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z68]),(0,[z352,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z353,z5,z6])],[(0,[z0,z1,z8,z3,z5,z6,z354]),(1,[z0,z1,z8,z3,z5,z355]),(0,[z0,z1,z8,z3,z5,z6,z356]),(0,[z0,z1,z8,z112,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z357,z6]),(0,[z1,z8,z107,z3,z21,z5,z6]),(0,[z0,z1,z8,z358,z3,z5,z6]),(0,[z0,z1,z17,z8,z3,z4,z6]),(0,[z359,z0,z1,z8,z3,z5,z6]),(0,[z360,z0,z1,z8,z3,z42,z5])],[(0,[z0,z361,z1,z8,z3,z5,z6]),(0,[z362,z0,z1,z8,z3,z5,z6]),(0,[z67,z1,z8,z3,z23,z5,z6]),(0,[z0,z1,z8,z3,z21,z5,z6])]],
   [[(0,[z43,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z363,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z364]),(0,[z0,z365,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z203])],[(0,[z0,z1,z8,z3,z366,z5,z6]),(1,[z100,z1,z8,z3,z5,z68]),(1,[z0,z1,z8,z28,z18,z3])],[(0,[z0,z1,z8,z107,z3,z5,z6]),(0,[z22,z0,z1,z8,z3,z367,z6]),(0,[z75,z0,z1,z214,z3,z5,z6]),(0,[z100,z0,z1,z8,z3,z5,z68]),(0,[z0,z1,z8,z2,z28,z3,z5]),(0,[z0,z1,z8,z368,z3,z5,z6]),(0,[z0,z1,z8,z128,z5,z6,z37]),(0,[z0,z1,z369,z8,z3,z5,z6])],[(0,[z0,z208,z1,z8,z3,z5,z6]),(0,[z0,z1,z370,z8,z3,z5,z6]),(0,[z0,z1,z8,z371,z3,z5,z6]),(0,[z0,z1,z8,z202,z3,z5,z6]),(0,[z0,z1,z8,z372,z3,z5,z6])],[(0,[z0,z1,z8,z3,z23,z6,z54]),(0,[z0,z1,z8,z150,z3,z5,z6]),(1,[z0,z373,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z50,z5,z6]),(0,[z0,z1,z8,z374,z3,z5,z6])],[(0,[z0,z1,z8,z3,z375,z5,z6]),(0,[z0,z1,z8,z3,z5,z376,z6]),(0,[z7,z0,z1,z8,z3,z300,z6]),(0,[z0,z1,z8,z377,z3,z5,z6]),(0,[z0,z1,z8,z39,z3,z5,z37]),(0,[z0,z378,z1,z8,z3,z5,z6])],[(0,[z0,z1,z45,z17,z3,z5,z6]),(0,[z0,z1,z86,z262,z3,z5,z6]),(0,[z0,z1,z93,z8,z3,z5,z6]),(1,[z35,z1,z8,z3,z5,z6])],[(0,[z0,z31,z8,z3,z9,z5,z6]),(0,[z0,z1,z379,z8,z3,z5,z6]),(0,[z12,z43,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z222,z3,z5]),(0,[z0,z1,z8,z28,z3,z5,z6])]],
   [[(0,[z0,z30,z1,z380,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z381,z6]),(0,[z0,z1,z8,z150,z3,z6,z68]),(0,[z0,z1,z8,z3,z5,z382,z6]),(0,[z0,z1,z8,z3,z383,z5,z6]),(0,[z34,z0,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z6,z384]),(0,[z0,z1,z8,z3,z385,z5,z6])],[(0,[z7,z0,z1,z8,z3,z5,z6]),(0,[z81,z0,z1,z8,z3,z5,z83]),(0,[z386,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z59,z3,z6,z54]),(0,[z0,z1,z8,z18,z3,z42,z5])],[(0,[z0,z31,z8,z3,z5,z6,z82]),(0,[z0,z1,z8,z3,z42,z23,z5]),(0,[z0,z1,z387,z8,z3,z5,z6]),(0,[z0,z388,z1,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z5,z389])],[(0,[z390,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z17,z8,z3,z42])],[(0,[z0,z1,z8,z3,z391,z5,z6]),(0,[z22,z0,z330,z8,z3,z5,z6]),(0,[z111,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z392,z3,z5,z6])],[(0,[z100,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z393,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z394,z6]),(0,[z0,z1,z8,z3,z5,z6,z395]),(1,[z106,z1,z8,z3,z5,z6]),(0,[z0,z1,z396,z8,z3,z42,z5])],[(0,[z397,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z50,z32,z6]),(0,[z398,z0,z1,z8,z3,z5,z6])],[(0,[z399,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z400]),(0,[z0,z1,z401,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z83]),(0,[z0,z1,z8,z3,z402,z5,z6]),(0,[z0,z1,z373,z8,z3,z5,z6]),(0,[z0,z1,z262,z8,z28,z3,z5])]],
   [[(0,[z0,z403,z1,z8,z3,z5,z6]),(0,[z70,z1,z8,z107,z3,z5,z6]),(0,[z0,z1,z8,z260,z3,z5,z6]),(0,[z81,z110,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z58,z3,z5,z6]),(1,[z0,z1,z8,z189,z3,z6])],[(1,[z404,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z33,z5,z6]),(0,[z0,z1,z8,z405,z3,z5,z6]),(0,[z0,z94,z8,z3,z5,z83,z6]),(0,[z0,z1,z8,z406,z3,z5,z6]),(0,[z407,z0,z1,z8,z3,z5,z6]),(0,[z106,z1,z8,z3,z5,z6,z54])],[(0,[z0,z1,z8,z408,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z409]),(0,[z0,z1,z410,z8,z3,z5,z6]),(0,[z411,z0,z1,z8,z3,z5,z6])],[(0,[z13,z0,z1,z107,z3,z5,z6]),(0,[z0,z1,z412,z8,z3,z5,z6]),(0,[z12,z1,z8,z3,z5,z6,z68]),(0,[z413,z0,z1,z8,z3,z5,z6]),(0,[z70,z0,z1,z8,z3,z42,z5]),(0,[z414,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z415,z5,z6]),(1,[z416,z0,z8,z3,z5,z6]),(0,[z417,z0,z1,z8,z3,z5,z6])],[(0,[z0,z187,z1,z8,z3,z5,z6]),(0,[z359,z111,z1,z8,z3,z5,z6]),(0,[z111,z0,z1,z8,z3,z5,z332])],[(0,[z0,z1,z8,z3,z418,z5,z6]),(0,[z0,z419,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z420,z3,z5,z6])],[(0,[z0,z421,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z422,z5,z6]),(0,[z7,z0,z1,z8,z3,z5,z343]),(0,[z0,z278,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z6,z423]),(1,[z0,z1,z8,z3,z424,z6]),(0,[z0,z1,z86,z17,z3,z5,z6]),(0,[z425,z0,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z8,z3,z89,z6]),(0,[z0,z1,z8,z3,z5,z6,z426])]],
   [[(0,[z55,z0,z1,z8,z3,z5,z6]),(1,[z75,z0,z1,z8,z3,z42]),(0,[z43,z1,z8,z3,z5,z44,z6]),(0,[z427,z0,z1,z8,z3,z5,z6])],[(0,[z22,z0,z1,z8,z21,z5,z6]),(0,[z0,z1,z8,z428,z3,z5,z6]),(0,[z0,z1,z429,z8,z3,z5,z6]),(0,[z430,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z273,z5,z6])],[(0,[z0,z1,z8,z3,z5,z80,z6]),(0,[z0,z1,z8,z3,z5,z6,z431]),(0,[z0,z1,z219,z8,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z5,z355]),(0,[z432,z0,z1,z8,z3,z5,z6])],[(0,[z433,z0,z1,z8,z3,z5,z6]),(1,[z22,z1,z8,z21,z5,z6]),(0,[z0,z1,z8,z434,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z32,z5]),(0,[z0,z1,z435,z8,z3,z5,z6])],[(0,[z436,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z437,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z80]),(0,[z438,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z108,z5,z6]),(0,[z0,z1,z8,z3,z439,z5,z6]),(1,[z26,z0,z1,z8,z3,z42]),(0,[z0,z1,z69,z8,z3,z5,z6]),(0,[z0,z440,z1,z8,z3,z5,z6])],[(0,[z81,z0,z1,z93,z3,z5,z6]),(0,[z0,z441,z1,z8,z3,z5,z6])],[(0,[z1,z31,z45,z8,z3,z5,z6]),(0,[z74,z1,z8,z121,z3,z5,z6]),(0,[z0,z1,z442,z8,z3,z5,z6]),(0,[z75,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z443,z5,z6]),(0,[z0,z16,z1,z8,z3,z42,z5]),(1,[z0,z197,z1,z8,z3,z42]),(0,[z0,z1,z8,z444,z3,z5,z6])],[(0,[z0,z1,z8,z445,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z446]),(0,[z0,z1,z49,z3,z5,z6,z54])]],
   [[(0,[z0,z1,z8,z3,z447,z5,z6]),(0,[z0,z448,z1,z8,z3,z5,z6]),(0,[z449,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z450,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z451])],[(0,[z43,z100,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z8,z3,z42,z5])],[(0,[z0,z1,z8,z3,z5,z6,z452]),(0,[z0,z1,z8,z3,z5,z6,z453]),(0,[z0,z144,z86,z8,z3,z5,z6])],[(0,[z0,z1,z8,z8,z3,z5,z6]),(0,[z0,z1,z454,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z5,z382]),(0,[z0,z1,z8,z455,z3,z5,z6])],[(0,[z0,z94,z8,z2,z3,z5,z6]),(0,[z314,z0,z1,z8,z3,z5,z6])],[(0,[z0,z1,z45,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z456,z5,z6]),(0,[z1,z8,z3,z23,z5,z80,z6]),(0,[z0,z1,z8,z3,z80,z6,z54]),(0,[z0,z1,z8,z3,z5,z457,z6]),(0,[z0,z1,z8,z458,z3,z5,z6]),(1,[z0,z1,z8,z3,z166,z5]),(0,[z0,z1,z8,z3,z5,z83,z6]),(0,[z63,z0,z146,z8,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z95,z6]),(0,[z111,z0,z373,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z203])],[(0,[z459,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z460]),(0,[z461,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z462,z6]),(0,[z0,z1,z8,z3,z5,z463,z6]),(0,[z81,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z464,z5,z6]),(1,[z0,z177,z8,z3,z5,z6]),(0,[z416,z0,z8,z3,z5,z6,z54])],[(0,[z0,z1,z465,z8,z3,z5,z6]),(0,[z13,z1,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z466,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z467]),(0,[z0,z1,z468,z8,z3,z5,z6]),(0,[z0,z1,z8,z469,z3,z5,z6])]],
   [[(0,[z0,z1,z107,z3,z4,z5,z6]),(0,[z0,z1,z45,z3,z4,z5,z6]),(1,[z0,z1,z262,z3,z5,z183]),(1,[z0,z1,z49,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z54]),(0,[z0,z1,z8,z3,z42,z470,z5])],[(0,[z29,z0,z8,z2,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z471,z6])],[(0,[z67,z1,z8,z3,z21,z5,z6]),(0,[z7,z0,z16,z8,z3,z5,z6]),(0,[z7,z26,z0,z8,z3,z5,z6]),(0,[z0,z94,z1,z8,z3,z5,z82]),(0,[z0,z1,z58,z8,z108,z5,z6]),(0,[z0,z1,z58,z8,z268,z5,z6])],[(0,[z29,z0,z1,z8,z28,z3,z5]),(0,[z30,z1,z8,z107,z3,z5,z6]),(1,[z0,z1,z472,z3,z5,z6]),(0,[z0,z1,z8,z3,z166,z5,z27]),(0,[z0,z1,z8,z3,z473,z5,z6]),(1,[z0,z1,z58,z268,z5,z6]),(0,[z111,z0,z1,z8,z3,z5,z389]),(0,[z0,z1,z8,z28,z372,z3,z5]),(0,[z136,z0,z1,z8,z3,z5,z6])],[(1,[z0,z1,z380,z3,z5,z6]),(1,[z0,z1,z8,z3,z367,z6]),(0,[z0,z1,z8,z3,z5,z297,z6]),(0,[z0,z1,z8,z474,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z42,z5])],[(0,[z75,z0,z1,z8,z3,z5,z347]),(0,[z475,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z476,z3,z5,z6]),(0,[z0,z1,z8,z112,z3,z6,z54]),(0,[z0,z1,z8,z222,z3,z5,z6])],[(0,[z0,z477,z1,z8,z3,z5,z6])],[(0,[z7,z404,z1,z8,z3,z5,z6]),(0,[z478,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z8,z39,z128,z5])]],
   [[(0,[z479,z0,z1,z8,z3,z5,z6]),(0,[z67,z0,z1,z8,z3,z42,z5]),(0,[z0,z144,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z480,z5,z6]),(0,[z481,z0,z1,z8,z3,z5,z6]),(0,[z0,z146,z1,z8,z3,z5,z6]),(0,[z1,z8,z3,z5,z6,z249,z54]),(0,[z0,z1,z8,z482,z3,z5,z6])],[(0,[z0,z31,z86,z8,z3,z5,z6]),(0,[z483,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z484]),(0,[z67,z0,z1,z137,z3,z5,z6]),(0,[z12,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z485,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z5,z6]),(0,[z486,z0,z1,z8,z3,z5,z6]),(0,[z100,z0,z219,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z108,z5,z6]),(0,[z0,z1,z8,z3,z42,z128,z5])],[(1,[z0,z1,z8,z3,z5,z487]),(0,[z0,z1,z8,z488,z3,z5,z6]),(0,[z0,z1,z8,z39,z3,z128,z5])],[(0,[z0,z1,z8,z489,z3,z5,z6])],[(0,[z13,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z121,z3,z42,z5]),(0,[z0,z1,z8,z3,z42,z6,z203])],[(0,[z0,z1,z8,z3,z490,z5,z6]),(0,[z0,z16,z1,z8,z9,z5,z6]),(0,[z0,z1,z8,z3,z491,z5,z6])],[(0,[z492,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z336,z3,z5,z6]),(0,[z0,z1,z86,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z493,z6]),(0,[z0,z1,z8,z3,z171,z5,z6]),(0,[z0,z1,z8,z3,z494,z42,z5])],[(0,[z0,z1,z8,z495,z3,z5,z6]),(0,[z496,z0,z1,z8,z3,z5,z6]),(0,[z497,z0,z1,z8,z3,z5,z6]),(0,[z360,z0,z1,z8,z3,z5,z6]),(1,[z81,z0,z8,z3,z5,z82])]],
   [[(0,[z0,z498,z1,z8,z3,z5,z6]),(0,[z67,z0,z144,z8,z3,z5,z6]),(0,[z22,z70,z1,z8,z3,z5,z6]),(1,[z0,z1,z8,z145,z3,z5])],[(0,[z499,z0,z1,z8,z3,z5,z6]),(0,[z500,z0,z1,z8,z3,z5,z6]),(0,[z12,z1,z45,z8,z3,z5,z6]),(0,[z0,z1,z86,z3,z4,z5,z6]),(0,[z26,z0,z1,z8,z28,z3,z5]),(1,[z0,z88,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z501])],[(0,[z0,z1,z8,z502,z3,z5,z6]),(0,[z0,z503,z45,z8,z3,z5,z6]),(0,[z504,z0,z1,z8,z3,z5,z6]),(0,[z505,z0,z1,z8,z3,z5,z6]),(0,[z506,z0,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z6,z507]),(0,[z22,z0,z1,z8,z121,z5,z6]),(0,[z0,z1,z8,z28,z3,z21,z5]),(1,[z0,z1,z8,z3,z33,z6]),(0,[z277,z34,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z508,z5,z6])],[(0,[z67,z74,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z509]),(0,[z0,z1,z8,z3,z510,z5,z6]),(0,[z26,z0,z8,z191,z3,z5,z6]),(0,[z0,z1,z8,z3,z511,z5,z6]),(0,[z63,z0,z1,z8,z3,z5,z226])],[(0,[z0,z1,z8,z512,z3,z5,z6]),(0,[z0,z1,z8,z18,z3,z50,z6])],[(0,[z0,z0,z1,z8,z3,z5,z6]),(0,[z26,z0,z144,z8,z3,z5,z6]),(0,[z0,z1,z8,z189,z3,z5,z6]),(0,[z0,z1,z8,z3,z513,z42,z5]),(0,[z0,z1,z8,z151,z28,z3,z5])],[(0,[z514,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z515,z6]),(0,[z0,z1,z8,z3,z473,z6,z82]),(0,[z0,z1,z8,z3,z5,z183,z37]),(0,[z0,z1,z8,z160,z28,z3,z5])]],
   [[(0,[z0,z516,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z6]),(0,[z26,z0,z1,z8,z3,z27,z6]),(0,[z0,z1,z262,z8,z3,z5,z36]),(1,[z0,z8,z3,z5,z6,z517])],[(0,[z0,z1,z330,z8,z3,z5,z6]),(0,[z7,z0,z1,z8,z3,z5,z382]),(0,[z0,z1,z8,z518,z3,z5,z6])],[(0,[z67,z0,z1,z20,z3,z5,z6]),(0,[z519,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z42,z5]),(1,[z0,z1,z8,z3,z5,z127]),(1,[z111,z0,z1,z3,z4,z6]),(0,[z0,z1,z8,z18,z3,z5,z6])],[(0,[z0,z1,z8,z520,z3,z5,z6]),(0,[z521,z0,z1,z8,z3,z5,z6]),(0,[z522,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z523,z3,z5,z6]),(1,[z131,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z524,z3,z5,z6]),(1,[z359,z1,z8,z3,z5,z6]),(0,[z525,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z526,z5,z6])],[(0,[z0,z30,z94,z8,z3,z5,z6]),(0,[z12,z0,z1,z45,z3,z5,z6]),(0,[z0,z527,z1,z8,z3,z5,z6]),(1,[z0,z16,z8,z191,z5,z6]),(0,[z528,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z145,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z529,z6]),(0,[z0,z1,z88,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z332,z6])],[(1,[z481,z1,z8,z3,z5,z6]),(0,[z0,z1,z530,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z531,z5,z6])],[(0,[z0,z1,z8,z3,z532,z5,z6]),(0,[z140,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z396,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z533,z5,z6]),(0,[z100,z1,z8,z3,z5,z6,z68]),(0,[z0,z1,z8,z534,z3,z5,z6])]],
   [[(0,[z0,z144,z1,z107,z3,z5,z6]),(0,[z12,z0,z535,z8,z3,z5,z6]),(0,[z536,z0,z1,z8,z3,z5,z6]),(0,[z22,z0,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z537,z5,z6]),(0,[z0,z1,z8,z3,z5,z82,z37]),(0,[z34,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z262,z3,z5,z183,z6]),(0,[z0,z1,z8,z3,z5,z6,z123])],[(1,[z0,z8,z538,z3,z5,z6]),(0,[z0,z1,z8,z539,z3,z5,z6]),(0,[z540,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z268,z3,z5])],[(0,[z0,z1,z8,z3,z5,z541,z6]),(0,[z0,z1,z8,z235,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z542])],[(0,[z0,z1,z8,z3,z543,z5,z6]),(0,[z0,z1,z8,z3,z544,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z183]),(1,[z0,z1,z8,z59,z6,z54]),(0,[z0,z1,z8,z3,z5,z6,z517]),(0,[z0,z1,z8,z3,z42,z531,z5])],[(0,[z70,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z487,z6]),(0,[z0,z1,z8,z3,z9,z42,z5]),(0,[z0,z197,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z545,z6]),(0,[z0,z1,z8,z3,z546,z5,z6]),(0,[z0,z1,z8,z3,z50,z4,z6])],[(0,[z0,z1,z8,z3,z5,z547,z6]),(0,[z0,z1,z8,z3,z5,z548,z6]),(0,[z0,z1,z8,z3,z5,z6,z549]),(0,[z0,z1,z8,z3,z550,z5,z6]),(0,[z0,z1,z8,z3,z551,z5,z6]),(1,[z552,z1,z8,z3,z5,z6]),(0,[z0,z553,z1,z8,z3,z5,z6])],[(0,[z0,z30,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z424,z5,z6]),(0,[z0,z1,z8,z3,z128,z5,z44])],[(0,[z0,z16,z31,z8,z3,z5,z6]),(0,[z554,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z82]),(0,[z0,z1,z262,z8,z3,z42,z5]),(0,[z555,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z50,z5])]],
   [[(0,[z12,z70,z1,z8,z3,z5,z6]),(0,[z0,z116,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z556,z3,z5,z6]),(0,[z0,z1,z8,z3,z557,z5,z6]),(1,[z0,z1,z3,z5,z6,z558]),(0,[z0,z1,z8,z559,z3,z5,z6])],[(0,[z560,z0,z1,z8,z3,z5,z6]),(0,[z561,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z562,z8,z3,z5,z6]),(0,[z0,z1,z17,z2,z3,z5,z6]),(0,[z0,z1,z8,z563,z3,z5,z6]),(0,[z0,z1,z8,z3,z564,z5,z6]),(1,[z0,z1,z8,z253,z3,z6]),(0,[z0,z1,z8,z3,z5,z6,z565])],[(0,[z0,z1,z8,z3,z424,z6,z68]),(0,[z26,z0,z1,z8,z18,z3,z6])],[(0,[z0,z1,z8,z3,z156,z5,z6]),(0,[z566,z0,z1,z8,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z27,z6])],[(0,[z1,z31,z8,z3,z23,z5,z6]),(0,[z0,z1,z8,z3,z5,z567,z6]),(0,[z0,z1,z8,z538,z3,z5,z6]),(1,[z0,z1,z8,z3,z473,z6]),(0,[z111,z0,z1,z8,z3,z4,z6]),(0,[z568,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z39,z3,z491,z6]),(0,[z0,z1,z8,z3,z42,z5,z5])],[(0,[z569,z0,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z8,z3,z297,z6]),(0,[z0,z1,z8,z570,z3,z5,z6])],[(0,[z0,z30,z8,z3,z9,z5,z6]),(0,[z0,z1,z8,z3,z5,z44,z6]),(0,[z571,z0,z1,z8,z3,z5,z6]),(0,[z34,z0,z1,z3,z5,z6,z36]),(0,[z228,z0,z1,z8,z28,z3,z5])],[(0,[z12,z29,z1,z8,z3,z5,z6]),(0,[z572,z0,z1,z8,z3,z5,z6]),(0,[z0,z16,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z573,z3,z5,z6])]],
   [[(0,[z100,z0,z1,z336,z3,z5,z6])],[(0,[z0,z30,z8,z3,z5,z6,z82]),(0,[z140,z0,z1,z45,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z574]),(0,[z0,z1,z8,z3,z5,z575,z6]),(0,[z0,z1,z8,z576,z3,z5,z6]),(1,[z110,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z4,z5]),(0,[z0,z35,z1,z8,z3,z5,z6])],[(0,[z30,z1,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z577,z3,z5,z6]),(1,[z0,z535,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z68]),(1,[z209,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z112,z50,z5,z6])],[(0,[z22,z0,z1,z8,z3,z5,z376]),(0,[z0,z1,z8,z578,z3,z5,z6]),(0,[z0,z144,z8,z3,z32,z5,z6]),(0,[z579,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z32,z6,z54]),(0,[z0,z1,z8,z3,z128,z5,z83]),(0,[z0,z1,z17,z8,z3,z95,z6])],[],[(0,[z0,z1,z8,z3,z580,z5,z6]),(0,[z0,z1,z8,z3,z581,z5,z6]),(0,[z0,z1,z8,z3,z5,z582,z6]),(0,[z0,z1,z8,z268,z3,z5,z6]),(0,[z0,z552,z1,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z171,z6])],[(0,[z583,z0,z1,z8,z3,z5,z6]),(0,[z0,z584,z1,z8,z3,z5,z6])],[(0,[z81,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z389])]],
   [[(0,[z0,z585,z1,z8,z3,z5,z6]),(0,[z12,z0,z1,z8,z28,z3,z5]),(0,[z1,z8,z3,z5,z44,z6,z68]),(1,[z157,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z586,z5,z6]),(0,[z0,z1,z8,z59,z28,z3,z5]),(0,[z0,z1,z8,z3,z42,z50,z6])],[(1,[z29,z31,z8,z3,z5,z6]),(0,[z67,z0,z31,z8,z3,z5,z6]),(0,[z67,z0,z30,z8,z3,z5,z6]),(0,[z0,z1,z587,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z44]),(0,[z0,z1,z8,z588,z3,z5,z6]),(0,[z0,z1,z8,z589,z3,z5,z6]),(0,[z590,z0,z1,z8,z3,z5,z6]),(0,[z591,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z592,z3,z5,z6])],[(0,[z12,z30,z1,z8,z3,z5,z6]),(0,[z593,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z24,z3,z5,z6]),(0,[z594,z0,z1,z8,z3,z5,z6])],[(0,[z0,z595,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z472,z3,z5,z6]),(0,[z309,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z596,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z37])],[(0,[z0,z1,z8,z3,z597,z5,z6]),(0,[z0,z1,z8,z380,z3,z5,z6]),(0,[z0,z404,z1,z8,z3,z5,z6]),(0,[z34,z0,z227,z8,z3,z5,z6])],[(0,[z0,z1,z535,z8,z3,z5,z6]),(0,[z0,z1,z45,z8,z3,z42,z5]),(1,[z0,z1,z8,z3,z5,z354]),(0,[z75,z0,z1,z8,z3,z5,z487]),(0,[z0,z197,z1,z8,z18,z3,z6]),(0,[z0,z1,z8,z222,z5,z6,z37]),(0,[z0,z1,z8,z3,z42,z5,z6]),(0,[z0,z1,z598,z8,z3,z5,z6])],[(0,[z599,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z600]),(0,[z0,z1,z8,z39,z3,z5,z6])],[(0,[z0,z1,z262,z107,z3,z5,z6]),(0,[z0,z1,z601,z8,z3,z5,z6]),(0,[z602,z0,z1,z8,z3,z5,z6]),(0,[z0,z603,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z604,z5,z6]),(0,[z0,z1,z58,z8,z3,z42,z5]),(0,[z0,z1,z8,z268,z3,z42,z5]),(0,[z34,z0,z1,z8,z3,z5,z183]),(1,[z0,z1,z8,z3,z287,z5]),(0,[z0,z1,z8,z3,z5,z40,z6])]],
   [[(0,[z29,z1,z8,z107,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z605,z6]),(1,[z0,z1,z57,z3,z5,z6]),(0,[z63,z0,z1,z3,z108,z5,z6])],[(0,[z67,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z606,z8,z3,z5,z6]),(0,[z0,z45,z8,z538,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z23,z5]),(0,[z0,z144,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z607,z5,z6]),(0,[z0,z94,z1,z8,z28,z3,z5]),(0,[z0,z1,z268,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z128,z5,z36]),(0,[z0,z1,z8,z3,z5,z6,z608]),(0,[z0,z1,z8,z3,z42,z231,z5])],[(0,[z0,z31,z8,z3,z32,z5,z6]),(0,[z0,z1,z8,z3,z609,z5,z6]),(0,[z0,z610,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z611,z5,z6])],[(0,[z29,z0,z1,z8,z3,z42,z5]),(0,[z74,z75,z1,z8,z3,z5,z6]),(0,[z0,z8,z191,z3,z9,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z95])],[(0,[z67,z13,z1,z8,z3,z5,z6]),(1,[z1,z8,z612,z3,z5,z6]),(0,[z157,z1,z86,z8,z3,z5,z6]),(0,[z0,z1,z8,z613,z3,z5,z6]),(0,[z0,z1,z8,z3,z614,z5,z6])],[(0,[z0,z1,z8,z121,z3,z5,z6]),(0,[z0,z615,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z616,z6]),(0,[z0,z617,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z618,z3,z5,z6]),(0,[z111,z552,z1,z8,z3,z5,z6]),(0,[z0,z1,z262,z8,z3,z5,z183]),(0,[z0,z1,z8,z3,z5,z6,z619]),(0,[z620,z0,z1,z8,z3,z5,z6])],[(0,[z12,z1,z8,z3,z23,z5,z6]),(0,[z0,z1,z8,z3,z621,z5,z6]),(0,[z0,z1,z8,z3,z494,z5,z6]),(0,[z0,z1,z8,z3,z470,z5,z6]),(0,[z0,z304,z1,z8,z28,z3,z5])]],
   [[(0,[z0,z1,z8,z622,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z623]),(0,[z0,z1,z8,z3,z5,z300,z6]),(0,[z0,z1,z8,z3,z5,z624,z6]),(0,[z0,z1,z8,z39,z3,z42,z5])],[(0,[z0,z1,z8,z3,z77,z5,z80]),(0,[z0,z1,z8,z625,z3,z5,z6]),(0,[z626,z0,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z367,z6]),(1,[z0,z76,z8,z3,z5,z6]),(1,[z627,z1,z8,z3,z5,z6]),(0,[z0,z628,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z18,z3,z6,z54]),(1,[z0,z1,z8,z28,z3,z5])],[(0,[z29,z0,z144,z8,z3,z5,z6]),(0,[z629,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z107,z3,z5,z6,z36]),(0,[z0,z1,z8,z3,z5,z6,z630]),(1,[z0,z503,z8,z3,z5,z6]),(0,[z0,z1,z45,z3,z5,z6,z36]),(0,[z140,z0,z8,z2,z3,z5,z6]),(0,[z1,z86,z8,z612,z3,z5,z6]),(0,[z627,z0,z1,z8,z3,z5,z6]),(1,[z201,z1,z8,z3,z5,z6])],[(0,[z22,z0,z1,z46,z3,z5,z6]),(0,[z0,z86,z8,z2,z3,z5,z6]),(0,[z0,z1,z631,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z632,z6]),(0,[z111,z0,z1,z17,z3,z5,z6]),(0,[z0,z1,z177,z8,z3,z5,z6])],[(0,[z0,z1,z31,z8,z28,z3,z5]),(0,[z140,z0,z1,z8,z28,z3,z5]),(0,[z0,z144,z1,z86,z3,z5,z6]),(0,[z0,z1,z8,z633,z3,z5,z6])],[(0,[z74,z0,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z6,z634]),(0,[z0,z1,z17,z268,z3,z5,z6]),(0,[z0,z1,z8,z321,z28,z3,z5])],[(0,[z1,z8,z107,z3,z5,z6,z68]),(0,[z0,z1,z8,z635,z3,z5,z6]),(0,[z0,z1,z8,z3,z636,z5,z6]),(0,[z637,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z513,z5,z6]),(0,[z0,z1,z8,z3,z638,z5,z6])]],
   [[(0,[z0,z1,z8,z639,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z68]),(0,[z416,z0,z1,z8,z3,z5,z6])],[(0,[z26,z0,z1,z8,z3,z32,z6]),(0,[z26,z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z28,z3,z5,z27]),(0,[z640,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z112,z3,z287,z5])],[(0,[z641,z0,z1,z8,z3,z5,z6]),(1,[z0,z1,z410,z3,z5,z6])],[(0,[z70,z1,z8,z121,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z642]),(0,[z26,z0,z8,z3,z5,z27,z6]),(0,[z0,z1,z8,z3,z5,z6,z61])],[(0,[z643,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z612,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z5,z36]),(0,[z338,z0,z1,z8,z28,z3,z5])],[(0,[z0,z149,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z644,z3,z5,z6]),(0,[z645,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z646,z3,z5,z6])],[(0,[z22,z0,z1,z8,z3,z5,z354]),(0,[z0,z647,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z53,z3,z5,z6]),(0,[z0,z1,z648,z8,z3,z5,z6])],[(0,[z1,z31,z8,z3,z21,z5,z6]),(0,[z0,z1,z649,z8,z3,z5,z6]),(0,[z0,z1,z58,z107,z3,z5,z6]),(0,[z0,z1,z8,z650,z3,z5,z6]),(0,[z0,z1,z8,z253,z3,z5,z6]),(0,[z63,z0,z1,z17,z3,z5,z6]),(0,[z0,z1,z8,z3,z651,z5,z6]),(0,[z0,z1,z652,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z653,z5,z6])]],
   [[(0,[z0,z30,z86,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z654,z5,z6]),(0,[z655,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z47,z3,z5,z80]),(0,[z0,z1,z8,z3,z656,z5,z6]),(0,[z0,z1,z17,z8,z28,z3,z5]),(0,[z0,z1,z8,z28,z73,z3,z5])],[(0,[z657,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z658,z6]),(0,[z659,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z83,z37]),(0,[z34,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z660,z5,z6]),(0,[z0,z1,z8,z3,z661,z5,z6])],[(1,[z1,z8,z3,z5,z6,z249]),(0,[z662,z0,z1,z8,z3,z5,z6])],[(0,[z13,z0,z1,z86,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z663,z6]),(1,[z0,z1,z8,z3,z42,z203]),(0,[z0,z1,z8,z28,z184,z3,z5])],[(0,[z0,z30,z1,z84,z3,z5,z6]),(0,[z0,z1,z86,z3,z5,z6,z36]),(0,[z7,z0,z1,z8,z191,z5,z6]),(0,[z0,z1,z3,z5,z6,z558,z54]),(0,[z0,z1,z8,z181,z3,z42,z5])],[(1,[z0,z1,z8,z3,z5,z376]),(0,[z1,z8,z121,z3,z23,z5,z6]),(0,[z664,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z9,z5,z6]),(0,[z0,z1,z8,z3,z665,z5,z6]),(0,[z0,z1,z8,z3,z666,z5,z6])],[(0,[z0,z1,z8,z3,z5,z667,z6]),(0,[z0,z1,z8,z3,z668,z5,z6]),(0,[z0,z1,z8,z3,z669,z5,z6]),(0,[z0,z1,z8,z3,z42,z5,z54]),(0,[z0,z1,z8,z670,z3,z5,z6])],[(0,[z43,z0,z1,z8,z28,z3,z5]),(1,[z0,z1,z8,z3,z5,z322])]],
   [[(0,[z22,z0,z1,z8,z3,z42,z5]),(0,[z0,z671,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z672,z6]),(0,[z0,z1,z8,z3,z5,z6,z82]),(0,[z0,z1,z8,z673,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z674]),(0,[z0,z1,z262,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z675,z5,z6]),(0,[z0,z8,z3,z5,z6,z517,z54]),(0,[z0,z1,z8,z3,z5,z6,z558])],[(0,[z0,z1,z8,z107,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z6,z676])],[(1,[z13,z1,z107,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z677]),(0,[z0,z144,z16,z8,z3,z5,z6]),(0,[z0,z1,z8,z191,z3,z42,z5]),(0,[z26,z0,z1,z8,z3,z42,z6])],[(0,[z678,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z679,z3,z5,z6]),(0,[z66,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z322,z6]),(0,[z0,z680,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z374,z28,z3,z5])],[(0,[z0,z1,z8,z3,z5,z681,z6]),(0,[z13,z0,z1,z2,z3,z5,z6]),(0,[z0,z94,z1,z8,z3,z5,z83])],[(0,[z0,z1,z8,z682,z3,z5,z6]),(0,[z0,z1,z8,z3,z683,z5,z6]),(0,[z236,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z684,z3,z5,z6]),(0,[z685,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z686,z3,z5,z6])],[(0,[z0,z30,z1,z8,z3,z42,z5]),(0,[z22,z0,z1,z8,z3,z156,z6]),(0,[z0,z1,z8,z28,z28,z3,z5])],[(0,[z687,z0,z1,z8,z3,z5,z6]),(0,[z74,z0,z1,z8,z18,z3,z6]),(0,[z0,z1,z8,z3,z5,z6,z688]),(0,[z0,z1,z8,z689,z3,z5,z6]),(0,[z0,z1,z8,z690,z3,z5,z6])]],
   [[(0,[z0,z1,z8,z691,z3,z5,z6]),(0,[z100,z0,z1,z472,z3,z5,z6]),(0,[z0,z692,z1,z8,z3,z5,z6]),(0,[z7,z627,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z343]),(0,[z7,z0,z1,z8,z28,z3,z5]),(0,[z693,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z694,z6]),(0,[z0,z1,z8,z3,z5,z6,z695])],[(0,[z0,z1,z8,z3,z5,z696,z6]),(0,[z697,z0,z1,z8,z3,z5,z6])],[(0,[z0,z503,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z347]),(0,[z0,z1,z8,z3,z50,z27,z6]),(0,[z0,z1,z8,z3,z698,z5,z6]),(0,[z0,z1,z8,z28,z112,z3,z5]),(0,[z0,z1,z8,z28,z3,z638,z5])],[(0,[z0,z1,z8,z699,z3,z5,z6]),(0,[z481,z81,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z700,z5,z6]),(0,[z111,z0,z1,z8,z28,z3,z5])],[(0,[z100,z0,z1,z8,z28,z3,z5])],[(0,[z75,z0,z1,z24,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z355]),(0,[z0,z1,z8,z3,z42,z6,z54]),(0,[z0,z1,z8,z701,z3,z5,z6])],[(0,[z702,z0,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z6,z703]),(0,[z0,z131,z1,z8,z3,z5,z6]),(0,[z111,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z8,z3,z491,z6]),(0,[z0,z1,z8,z28,z18,z3,z5])],[(0,[z29,z1,z31,z8,z3,z5,z6]),(0,[z67,z43,z1,z8,z3,z5,z6]),(0,[z0,z1,z45,z58,z3,z5,z6]),(0,[z0,z1,z8,z704,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z9,z5]),(0,[z0,z197,z1,z410,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z5,z179]),(0,[z0,z1,z8,z3,z5,z6,z127]),(0,[z0,z1,z8,z3,z705,z5,z6]),(0,[z0,z1,z8,z3,z5,z706,z6]),(0,[z0,z1,z8,z3,z128,z5,z183])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z67,z30,z8,z3,z5,z6]),(0,[z397,z31,z8,z3,z5,z6]),(0,[z0,z707,z8,z3,z5,z6]),(0,[z0,z1,z24,z3,z5,z347]),(0,[z0,z1,z8,z112,z42,z50])],[],[(0,[z29,z8,z520,z3,z5,z6]),(0,[z708,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z709,z3,z5]),(0,[z0,z1,z8,z3,z710,z5]),(0,[z0,z1,z8,z374,z3,z42]),(0,[z0,z1,z8,z3,z638,z42])],[(0,[z0,z1,z711,z3,z5,z6])],[(0,[z0,z1,z712,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z713]),(0,[z0,z1,z8,z3,z42,z714]),(0,[z0,z1,z8,z715,z3,z5])],[(0,[z0,z1,z8,z112,z50,z6])],[(0,[z716,z1,z8,z3,z5,z6]),(0,[z0,z1,z17,z3,z717,z6])],[(0,[z585,z1,z45,z3,z5,z6]),(0,[z718,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z719])],[(0,[z111,z0,z1,z17,z3,z42]),(0,[z0,z1,z8,z328,z6,z54])],[(0,[z0,z1,z336,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z179]),(0,[z0,z197,z8,z28,z3,z32]),(0,[z0,z197,z8,z686,z3,z6])],[(0,[z0,z224,z107,z3,z5,z6]),(0,[z0,z1,z720,z3,z5,z6]),(0,[z0,z8,z3,z5,z721,z6]),(0,[z722,z1,z8,z3,z5,z6])],[],[(0,[z67,z403,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z723])],[(0,[z187,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z112,z50,z123])],[(0,[z13,z1,z587,z3,z5,z6]),(0,[z0,z1,z8,z3,z724,z5])],[(0,[z106,z1,z8,z3,z23,z6]),(0,[z0,z88,z3,z4,z5,z6])]],
   [[(0,[z67,z74,z1,z8,z3,z42]),(0,[z12,z1,z725,z3,z5,z6]),(0,[z100,z116,z8,z3,z5,z68]),(0,[z0,z1,z8,z28,z3,z462]),(0,[z726,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z559,z6,z54])],[],[(0,[z0,z1,z8,z3,z367,z376]),(0,[z0,z144,z86,z3,z5,z6]),(0,[z727,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z728,z5])],[(0,[z0,z1,z8,z3,z729,z6]),(0,[z659,z0,z1,z8,z3,z42]),(0,[z0,z1,z17,z3,z42,z470]),(0,[z111,z552,z1,z8,z3,z42]),(0,[z111,z0,z11,z8,z3,z42]),(0,[z0,z730,z8,z3,z5,z6])],[(0,[z0,z8,z3,z721,z27,z6]),(0,[z1,z8,z731,z3,z5,z6]),(0,[z0,z1,z8,z3,z732,z42])],[(0,[z0,z208,z8,z3,z5,z6]),(0,[z74,z1,z137,z3,z5,z6]),(0,[z0,z1,z8,z3,z733,z6]),(0,[z0,z333,z2,z3,z5,z6]),(0,[z0,z1,z8,z181,z128,z5])],[(0,[z413,z31,z8,z3,z5,z6]),(0,[z0,z1,z734,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z735]),(0,[z0,z1,z214,z8,z3,z42]),(0,[z140,z0,z2,z3,z42,z5]),(0,[z309,z1,z8,z3,z5,z179]),(0,[z359,z1,z8,z28,z3,z5])],[(0,[z140,z0,z520,z3,z5,z6]),(0,[z43,z535,z8,z3,z5,z6]),(0,[z63,z0,z1,z108,z5,z226]),(0,[z0,z1,z8,z3,z5,z736]),(0,[z0,z737,z8,z3,z5,z6]),(0,[z0,z738,z8,z3,z5,z6])],[(0,[z0,z1,z739,z3,z5,z6]),(0,[z481,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z740,z42,z5])],[(0,[z13,z1,z107,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z118]),(0,[z0,z1,z8,z3,z89,z226])],[(0,[z0,z1,z20,z3,z42,z5]),(0,[z0,z1,z8,z741,z3,z5]),(0,[z0,z1,z8,z3,z42,z156]),(0,[z742,z0,z8,z3,z5,z6]),(0,[z0,z227,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z743,z6]),(0,[z0,z1,z8,z3,z5,z744])],[(0,[z0,z1,z410,z3,z5,z355]),(0,[z0,z745,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z746,z6]),(0,[z747,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z748,z3,z5]),(0,[z75,z0,z1,z8,z3,z77]),(0,[z111,z0,z11,z3,z4,z6])],[(0,[z0,z1,z8,z512,z3,z42]),(0,[z0,z304,z8,z3,z5,z82]),(0,[z749,z1,z8,z3,z5,z6])],[(0,[z74,z1,z8,z3,z231,z6]),(0,[z750,z1,z8,z3,z5,z6]),(0,[z7,z0,z8,z9,z5,z382]),(0,[z751,z1,z8,z3,z5,z6])]],
   [[(0,[z330,z8,z3,z23,z5,z6]),(0,[z1,z8,z752,z3,z5,z6]),(0,[z552,z1,z8,z28,z3,z5])],[(0,[z0,z1,z8,z3,z77,z50]),(0,[z63,z0,z146,z108,z5,z6]),(0,[z0,z1,z17,z268,z3,z42])],[(0,[z0,z144,z20,z3,z5,z6]),(0,[z67,z169,z8,z3,z5,z6]),(0,[z0,z753,z8,z3,z5,z6]),(0,[z34,z0,z1,z8,z3,z171])],[(0,[z0,z1,z255,z3,z5,z6]),(0,[z0,z1,z8,z3,z754,z5]),(0,[z0,z755,z8,z3,z5,z6])],[(0,[z1,z45,z725,z3,z5,z6]),(0,[z0,z756,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z757]),(0,[z240,z1,z107,z3,z5,z6]),(0,[z12,z224,z45,z3,z5,z6]),(0,[z506,z1,z45,z3,z5,z6]),(0,[z0,z1,z214,z3,z42,z5]),(1,[z0,z1,z3,z5,z758]),(0,[z0,z1,z8,z3,z491,z6]),(0,[z759,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z466,z50,z6]),(0,[z0,z11,z8,z3,z5,z6]),(0,[z0,z144,z468,z3,z5,z6]),(0,[z7,z0,z8,z9,z300,z6]),(0,[z277,z227,z8,z3,z5,z6])],[(0,[z35,z1,z3,z5,z6,z36]),(0,[z0,z1,z8,z28,z3,z491])],[(0,[z140,z0,z538,z3,z5,z6]),(0,[z693,z0,z2,z3,z5,z6]),(0,[z26,z0,z175,z3,z5,z6]),(0,[z63,z0,z88,z108,z5,z6]),(0,[z0,z1,z8,z3,z287,z54]),(0,[z0,z1,z8,z760,z42,z5])],[(0,[z0,z1,z8,z3,z5,z761]),(0,[z131,z1,z8,z3,z5,z127]),(0,[z762,z0,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z273,z50]),(0,[z0,z304,z1,z8,z3,z42])],[(1,[z0,z208,z8,z3,z42])],[(0,[z0,z224,z8,z3,z5,z6]),(0,[z30,z587,z8,z3,z5,z6]),(0,[z0,z763,z8,z3,z5,z6]),(0,[z43,z1,z472,z3,z5,z6]),(0,[z0,z1,z8,z42,z50,z61])],[(0,[z75,z0,z1,z8,z3,z764]),(0,[z765,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z766,z6]),(0,[z0,z1,z8,z18,z3,z355]),(0,[z81,z0,z8,z253,z3,z82])],[(0,[z140,z30,z107,z3,z5,z6]),(0,[z0,z1,z46,z3,z5,z6]),(0,[z209,z1,z8,z28,z3,z5]),(0,[z767,z1,z8,z3,z5,z6])],[(0,[z187,z16,z8,z3,z5,z6]),(0,[z768,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z389])],[(0,[z769,z1,z8,z3,z5,z6])]],
   [[(0,[z0,z197,z1,z8,z3,z714]),(0,[z63,z0,z1,z108,z297,z6])],[(0,[z12,z1,z45,z3,z5,z6]),(0,[z157,z8,z2,z3,z5,z6]),(0,[z144,z187,z86,z3,z5,z6]),(0,[z0,z197,z158,z3,z32,z6]),(1,[z0,z1,z3,z717,z6])],[(0,[z0,z1,z8,z3,z42,z295]),(0,[z535,z8,z3,z21,z5,z6]),(0,[z0,z1,z8,z150,z3,z42])],[(0,[z0,z16,z8,z28,z191,z5])],[(0,[z1,z725,z107,z3,z5,z6]),(0,[z664,z1,z107,z3,z5,z6])],[(0,[z0,z1,z8,z3,z367,z354]),(0,[z0,z1,z8,z3,z77,z5]),(0,[z1,z58,z612,z3,z5,z6]),(0,[z1,z8,z770,z3,z5,z6]),(0,[z63,z0,z1,z108,z5,z6]),(0,[z35,z227,z8,z3,z5,z6])],[(0,[z0,z1,z214,z3,z42,z6]),(0,[z0,z197,z8,z3,z32,z179]),(0,[z0,z1,z8,z50,z6,z771]),(0,[z0,z1,z154,z8,z3,z42])],[(0,[z0,z1,z8,z3,z5,z6]),(0,[z0,z8,z772,z3,z5,z6]),(0,[z0,z149,z8,z3,z42,z5]),(0,[z1,z8,z3,z773,z80,z6]),(0,[z1,z612,z3,z5,z6,z36]),(0,[z7,z0,z8,z9,z5,z343]),(0,[z0,z1,z8,z3,z89,z6]),(0,[z0,z1,z8,z234,z3,z42]),(1,[z106,z1,z8,z3,z42]),(0,[z0,z1,z8,z53,z3,z5]),(0,[z338,z0,z1,z8,z3,z42])],[(0,[z0,z1,z774,z3,z5,z6]),(0,[z0,z94,z380,z3,z5,z6]),(0,[z140,z0,z380,z3,z5,z6]),(0,[z0,z1,z24,z3,z5,z487]),(0,[z0,z775,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z608])],[(0,[z0,z1,z8,z3,z5,z776]),(0,[z111,z0,z1,z8,z3,z273]),(0,[z0,z1,z777,z3,z5,z6])],[(0,[z0,z1,z8,z3,z778,z6]),(0,[z0,z1,z8,z3,z42,z422]),(0,[z25,z0,z2,z3,z5,z6]),(0,[z0,z779,z8,z3,z5,z6]),(0,[z0,z1,z17,z3,z42,z95]),(0,[z0,z780,z8,z3,z42,z5])],[(0,[z0,z1,z8,z3,z781,z6]),(0,[z1,z8,z3,z5,z6,z782]),(0,[z0,z783,z8,z3,z5,z6]),(0,[z0,z784,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z785]),(0,[z0,z1,z8,z3,z5,z786])],[(0,[z67,z615,z8,z3,z5,z6]),(0,[z0,z149,z8,z3,z156,z6]),(0,[z0,z1,z8,z3,z42,z367]),(0,[z0,z1,z787,z3,z5,z6]),(0,[z66,z1,z86,z3,z5,z6]),(0,[z788,z0,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z273,z5]),(0,[z0,z8,z3,z5,z6,z789])],[(0,[z13,z31,z86,z3,z5,z6]),(0,[z0,z1,z58,z139,z5,z6]),(0,[z0,z1,z8,z3,z5,z790]),(0,[z416,z0,z8,z3,z5,z322]),(0,[z791,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z306,z6,z54]),(0,[z0,z1,z8,z792,z3,z5]),(0,[z1,z8,z612,z28,z3,z5]),(0,[z0,z1,z8,z3,z473,z37]),(0,[z793,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z123])]],
   [[(0,[z0,z1,z8,z794,z3,z5])],[(0,[z67,z30,z380,z3,z5,z6]),(0,[z144,z1,z612,z3,z5,z6]),(0,[z0,z8,z3,z795,z5,z6])],[(0,[z796,z1,z8,z3,z5,z6]),(0,[z67,z144,z45,z3,z5,z6]),(0,[z106,z1,z8,z3,z80,z6]),(0,[z416,z0,z8,z18,z3,z6])],[(0,[z0,z1,z797,z3,z5,z6]),(0,[z277,z1,z8,z3,z5,z6]),(0,[z81,z0,z57,z3,z5,z82])],[(0,[z1,z8,z3,z23,z6,z85]),(0,[z75,z0,z1,z214,z3,z42]),(0,[z0,z1,z8,z3,z42,z636]),(0,[z0,z1,z8,z3,z798,z297]),(0,[z0,z1,z58,z799,z5,z6]),(0,[z0,z1,z262,z114,z3,z5])],[(0,[z0,z116,z336,z3,z5,z6]),(0,[z641,z0,z1,z3,z5,z36]),(0,[z0,z1,z8,z563,z3,z42]),(0,[z0,z800,z8,z3,z5,z6])],[(0,[z0,z801,z8,z3,z5,z6]),(0,[z0,z802,z8,z3,z5,z6]),(0,[z0,z1,z8,z803,z3,z5]),(0,[z0,z1,z8,z3,z5,z804]),(0,[z34,z0,z1,z3,z5,z36])],[(0,[z0,z1,z158,z3,z5,z6]),(0,[z0,z177,z3,z5,z6,z36])],[(0,[z0,z805,z8,z3,z5,z6]),(0,[z806,z1,z8,z3,z5,z6])],[(0,[z0,z330,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z42,z764]),(0,[z386,z0,z2,z3,z5,z6])],[(0,[z31,z8,z3,z5,z6,z229]),(0,[z702,z31,z8,z3,z5,z6]),(0,[z438,z0,z2,z3,z5,z6]),(0,[z0,z1,z8,z807,z3,z5]),(0,[z0,z808,z8,z3,z5,z6])],[(0,[z0,z31,z20,z3,z5,z6]),(0,[z0,z380,z3,z32,z5,z6]),(0,[z0,z1,z8,z3,z89,z127]),(0,[z0,z1,z8,z799,z5,z6]),(0,[z640,z0,z1,z8,z3,z42])],[(0,[z74,z1,z31,z8,z3,z42]),(0,[z0,z1,z809,z3,z5,z6]),(0,[z0,z1,z8,z3,z810,z6]),(0,[z0,z1,z8,z811,z5,z6]),(0,[z0,z88,z8,z3,z42,z5])],[(0,[z75,z1,z214,z3,z23,z6]),(0,[z100,z1,z8,z3,z5,z68]),(0,[z0,z1,z8,z3,z812,z5]),(0,[z0,z1,z8,z315,z50,z6]),(0,[z0,z1,z8,z28,z18,z3]),(0,[z813,z1,z8,z28,z3,z5])],[(0,[z503,z187,z8,z3,z5,z6])],[(0,[z0,z20,z538,z3,z5,z6]),(0,[z13,z0,z538,z3,z5,z6]),(0,[z0,z330,z8,z3,z156,z6]),(0,[z75,z0,z208,z8,z3,z42])]],
   [[(0,[z0,z1,z814,z3,z5,z6]),(0,[z0,z538,z3,z4,z5,z6]),(0,[z0,z373,z8,z3,z5,z6]),(0,[z0,z8,z59,z6,z517,z54])],[(0,[z1,z8,z3,z23,z367,z6]),(0,[z627,z1,z8,z3,z33,z6]),(0,[z481,z1,z57,z3,z5,z6]),(0,[z0,z1,z815,z3,z5,z6]),(0,[z0,z816,z8,z28,z3,z5])],[(0,[z817,z1,z8,z3,z5,z6])],[(0,[z0,z8,z28,z3,z5,z517]),(0,[z0,z1,z49,z3,z5,z322])],[(0,[z0,z1,z8,z3,z42,z456]),(0,[z55,z0,z1,z8,z3,z424]),(0,[z0,z2,z3,z292,z5,z6]),(0,[z309,z1,z158,z3,z5,z6]),(0,[z41,z0,z1,z8,z5,z61])],[(0,[z1,z725,z8,z3,z5,z6]),(0,[z74,z330,z8,z3,z5,z6]),(0,[z818,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z819,z5]),(0,[z0,z1,z8,z3,z42,z820]),(0,[z0,z1,z8,z821,z5,z37])],[(0,[z0,z822,z8,z3,z5,z6])],[(0,[z26,z0,z31,z8,z3,z42]),(0,[z0,z1,z8,z3,z823,z5]),(0,[z0,z16,z8,z254,z5,z6]),(0,[z0,z1,z8,z3,z297,z226]),(0,[z0,z1,z17,z8,z3,z42]),(0,[z0,z1,z8,z824,z5,z6]),(0,[z0,z1,z49,z18,z3,z6])],[(0,[z825,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z826]),(0,[z26,z0,z8,z3,z166,z27]),(0,[z136,z0,z1,z160,z3,z5])],[(0,[z74,z1,z8,z28,z3,z80]),(0,[z0,z1,z8,z3,z42,z677]),(0,[z106,z1,z8,z53,z3,z5])],[(0,[z13,z1,z520,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z827]),(0,[z0,z1,z8,z3,z828,z6]),(0,[z136,z0,z1,z8,z3,z42]),(0,[z0,z1,z829,z3,z5,z6])],[(0,[z0,z219,z8,z3,z5,z6]),(0,[z140,z0,z830,z3,z5,z6]),(0,[z0,z1,z255,z3,z5,z382]),(0,[z0,z1,z8,z3,z831,z6])],[(0,[z0,z1,z8,z3,z832,z5]),(0,[z0,z1,z8,z3,z833,z5]),(0,[z0,z1,z8,z3,z5,z834]),(0,[z0,z1,z8,z3,z835,z33]),(0,[z131,z1,z3,z4,z5,z6]),(0,[z0,z1,z8,z3,z5,z226]),(0,[z0,z1,z3,z42,z558,z54])],[],[(0,[z1,z8,z3,z5,z6,z836]),(0,[z0,z8,z3,z32,z6,z600])],[(0,[z837,z1,z8,z3,z5,z6]),(1,[z0,z1,z8,z3,z732])]],
   [[(0,[z0,z1,z8,z3,z5,z838]),(0,[z1,z262,z612,z3,z5,z6]),(1,[z309,z1,z8,z3,z42]),(0,[z111,z552,z1,z3,z4,z6]),(0,[z0,z1,z8,z181,z513,z5])],[(0,[z7,z26,z0,z8,z3,z42]),(0,[z0,z1,z8,z222,z5,z37])],[(0,[z0,z839,z8,z3,z5,z6]),(1,[z0,z1,z214,z3,z42]),(0,[z0,z1,z255,z3,z300,z6]),(0,[z26,z0,z8,z28,z3,z27]),(0,[z0,z1,z8,z3,z42,z471])],[(1,[z1,z8,z3,z5,z840]),(0,[z209,z1,z8,z3,z89,z6])],[(0,[z0,z1,z8,z3,z841,z5]),(0,[z75,z0,z1,z8,z3,z42]),(0,[z0,z197,z8,z3,z32,z6]),(0,[z0,z1,z8,z3,z42,z355])],[(0,[z348,z0,z1,z8,z3,z42]),(0,[z0,z1,z842,z3,z42,z5])],[(0,[z0,z388,z86,z3,z5,z6])],[(0,[z29,z535,z8,z3,z5,z6]),(0,[z0,z1,z260,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z424]),(0,[z0,z208,z8,z3,z5,z347]),(0,[z843,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z33])],[(0,[z0,z1,z844,z3,z5,z6]),(0,[z583,z1,z8,z3,z5,z68]),(0,[z0,z1,z8,z3,z845,z6]),(0,[z0,z8,z3,z32,z300,z6]),(0,[z0,z1,z8,z556,z50,z6]),(0,[z0,z1,z435,z8,z3,z42])],[(0,[z416,z0,z8,z3,z32,z6]),(0,[z1,z8,z3,z42,z249,z54]),(0,[z416,z0,z8,z3,z42,z5]),(0,[z0,z1,z8,z112,z6,z771])],[(0,[z0,z388,z1,z8,z3,z42])],[],[(0,[z0,z224,z380,z3,z5,z6]),(0,[z0,z1,z846,z3,z5,z6]),(0,[z847,z1,z8,z3,z5,z6]),(0,[z848,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z128,z491])],[(0,[z43,z1,z8,z3,z5,z290]),(0,[z0,z1,z8,z374,z73,z5])],[(0,[z0,z1,z46,z3,z367,z6]),(0,[z55,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z3,z849,z5])],[(0,[z0,z1,z850,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z382]),(0,[z0,z1,z49,z8,z3,z42]),(0,[z0,z1,z851,z3,z5,z6])]],
   [[(0,[z26,z0,z8,z2,z3,z42]),(0,[z26,z404,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z89])],[(0,[z0,z1,z852,z3,z5,z6]),(0,[z496,z1,z107,z3,z5,z6]),(0,[z22,z1,z8,z21,z42,z5]),(0,[z100,z219,z8,z3,z5,z68]),(0,[z309,z197,z8,z3,z32,z6])],[(0,[z30,z535,z8,z3,z5,z6]),(0,[z12,z1,z230,z3,z5,z6]),(0,[z48,z0,z2,z3,z5,z6]),(0,[z0,z647,z86,z3,z5,z6])],[(0,[z0,z1,z255,z3,z5,z343]),(0,[z0,z1,z17,z3,z470,z6]),(0,[z0,z1,z8,z3,z42,z54])],[(0,[z0,z86,z380,z3,z5,z6]),(0,[z0,z1,z17,z2,z3,z42]),(0,[z0,z1,z8,z3,z42,z473])],[(0,[z0,z1,z24,z3,z42,z5]),(0,[z0,z1,z8,z3,z297,z6]),(0,[z853,z1,z8,z3,z5,z6])],[(0,[z70,z1,z137,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z854]),(0,[z0,z1,z8,z855,z3,z5]),(0,[z1,z8,z856,z3,z5,z6]),(0,[z0,z1,z8,z3,z300,z6]),(0,[z0,z1,z8,z857,z3,z5]),(0,[z0,z8,z3,z5,z6,z858])],[(0,[z0,z1,z8,z3,z42,z357]),(0,[z22,z1,z8,z21,z156,z6])],[(0,[z0,z1,z380,z3,z5,z6]),(0,[z29,z187,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z859]),(0,[z0,z76,z24,z3,z5,z6])],[],[(0,[z0,z1,z8,z3,z860,z156]),(0,[z7,z0,z8,z9,z33,z6]),(0,[z110,z8,z3,z5,z6,z82]),(0,[z416,z0,z8,z3,z42,z6]),(0,[z0,z861,z8,z3,z5,z6])],[(0,[z0,z1,z862,z3,z5,z6]),(0,[z0,z1,z84,z28,z3,z5]),(0,[z486,z1,z107,z3,z5,z6]),(0,[z863,z0,z1,z3,z5,z6]),(0,[z1,z8,z121,z811,z5,z6]),(0,[z157,z144,z8,z3,z5,z6]),(0,[z0,z1,z8,z189,z3,z389]),(0,[z1,z8,z3,z5,z6,z864]),(0,[z0,z1,z865,z3,z5,z6]),(0,[z0,z1,z8,z39,z128,z5])],[(0,[z0,z1,z8,z3,z5,z866])],[(0,[z0,z477,z8,z3,z32,z6]),(0,[z0,z1,z8,z867,z3,z5]),(0,[z0,z868,z8,z3,z5,z6]),(0,[z1,z869,z8,z3,z5,z6]),(0,[z0,z1,z870,z3,z5,z6])],[(0,[z12,z1,z437,z3,z5,z6]),(0,[z404,z16,z8,z3,z5,z6]),(0,[z277,z177,z8,z3,z5,z6]),(0,[z0,z1,z49,z3,z42,z5])],[(0,[z1,z107,z3,z204,z5,z6]),(0,[z871,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z300])]],
   [[(0,[z0,z1,z8,z3,z5,z872])],[(0,[z0,z1,z472,z3,z42,z5]),(0,[z0,z1,z58,z268,z42,z5])],[(0,[z0,z1,z336,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z873])],[(0,[z0,z1,z8,z3,z300,z343]),(0,[z874,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z39,z128,z40])],[(0,[z0,z1,z875,z3,z5,z6]),(0,[z0,z1,z8,z145,z3,z5])],[(0,[z0,z1,z876,z3,z5,z6]),(0,[z74,z1,z8,z47,z3,z80]),(0,[z0,z1,z8,z3,z877,z6]),(0,[z627,z1,z8,z3,z42,z5])],[(0,[z0,z1,z137,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z878]),(0,[z0,z1,z8,z3,z5,z879]),(0,[z201,z1,z8,z3,z42,z5]),(0,[z880,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z202,z3,z5]),(0,[z0,z881,z8,z3,z5,z6])],[(0,[z309,z1,z8,z3,z5,z6]),(0,[z0,z1,z882,z3,z5,z6]),(0,[z0,z883,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z343]),(0,[z0,z1,z8,z3,z884,z5])],[(0,[z0,z1,z885,z3,z5,z6]),(0,[z193,z1,z107,z3,z5,z6]),(0,[z0,z76,z8,z28,z3,z5]),(0,[z886,z1,z8,z3,z5,z6]),(1,[z0,z1,z410,z3,z42]),(0,[z209,z1,z8,z3,z5,z226]),(0,[z552,z11,z8,z3,z5,z6])],[(0,[z0,z503,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z347]),(0,[z0,z1,z8,z3,z288,z42]),(0,[z43,z219,z8,z3,z5,z6]),(0,[z66,z1,z2,z3,z5,z6]),(0,[z0,z146,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z297,z127]),(0,[z887,z1,z8,z28,z3,z5])],[(0,[z1,z107,z3,z239,z5,z6]),(0,[z0,z1,z8,z3,z5,z888])],[(0,[z0,z1,z8,z3,z889,z5])],[(0,[z404,z1,z255,z3,z5,z6]),(0,[z0,z8,z3,z5,z6,z517]),(0,[z0,z1,z8,z3,z714,z5]),(0,[z63,z0,z1,z108,z5,z127])],[(0,[z1,z8,z3,z5,z840,z68]),(0,[z0,z1,z69,z8,z3,z42]),(0,[z0,z1,z890,z3,z5,z6])],[(0,[z0,z891,z8,z3,z5,z6]),(0,[z1,z17,z612,z3,z5,z6]),(0,[z627,z1,z175,z3,z5,z6]),(0,[z0,z1,z175,z28,z3,z5]),(0,[z0,z1,z8,z3,z5,z127])],[(0,[z0,z1,z8,z3,z5,z892]),(0,[z0,z1,z8,z893,z3,z5]),(0,[z0,z894,z8,z3,z5,z6]),(0,[z0,z1,z49,z3,z42,z6])]],
   [[(0,[z67,z503,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z895,z6]),(0,[z0,z1,z8,z795,z5,z6]),(0,[z0,z1,z410,z28,z3,z5]),(0,[z0,z1,z8,z3,z896,z5]),(0,[z0,z1,z3,z4,z6,z364])],[(0,[z0,z1,z8,z3,z897,z5]),(0,[z0,z1,z8,z3,z898,z5]),(0,[z0,z1,z899,z3,z5,z6]),(0,[z201,z1,z410,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z661])],[(0,[z404,z8,z3,z32,z5,z6]),(0,[z0,z1,z8,z900,z3,z5]),(0,[z0,z1,z8,z3,z5,z901]),(0,[z0,z1,z902,z3,z5,z6])],[(0,[z0,z1,z8,z3,z42,z324]),(0,[z140,z0,z2,z28,z3,z5]),(0,[z0,z88,z3,z108,z5,z6])],[(0,[z0,z1,z903,z3,z5,z6]),(0,[z904,z1,z8,z3,z5,z6])],[(0,[z35,z1,z8,z3,z5,z6]),(0,[z0,z2,z3,z607,z5,z6]),(0,[z111,z0,z1,z3,z42,z4]),(0,[z106,z1,z8,z3,z42,z54]),(0,[z1,z8,z28,z3,z5,z249]),(0,[z0,z905,z8,z28,z3,z5])],[(0,[z0,z1,z8,z3,z906,z6]),(0,[z907,z1,z8,z3,z5,z6]),(0,[z111,z0,z1,z3,z4,z332])],[(0,[z0,z1,z8,z28,z3,z156]),(0,[z0,z1,z8,z3,z908,z6]),(0,[z0,z86,z830,z3,z5,z6]),(0,[z909,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z73,z5,z37])],[(0,[z100,z1,z336,z3,z5,z68]),(0,[z1,z8,z3,z5,z840,z6]),(0,[z0,z1,z410,z3,z5,z179]),(0,[z0,z1,z8,z128,z821,z5])],[(0,[z0,z16,z380,z3,z5,z6]),(0,[z552,z1,z8,z3,z5,z6]),(0,[z131,z1,z8,z3,z42,z5])],[(0,[z0,z16,z8,z191,z42,z5]),(0,[z0,z158,z3,z32,z5,z6]),(0,[z0,z1,z8,z3,z910,z6])],[(0,[z0,z1,z911,z3,z5,z6]),(0,[z0,z1,z912,z3,z5,z6])],[(0,[z66,z1,z45,z3,z5,z6]),(0,[z106,z1,z8,z3,z5,z6]),(0,[z187,z8,z3,z9,z5,z6]),(0,[z404,z1,z8,z3,z300,z6]),(0,[z269,z0,z1,z8,z3,z42])],[(0,[z0,z913,z8,z3,z5,z6]),(0,[z0,z914,z8,z3,z5,z6]),(0,[z75,z1,z24,z3,z23,z6]),(0,[z219,z8,z3,z5,z6,z68]),(0,[z131,z146,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z156,z376]),(1,[z0,z1,z8,z821,z5]),(0,[z141,z0,z1,z3,z470,z5])],[(0,[z12,z45,z538,z3,z5,z6]),(0,[z0,z8,z538,z3,z42,z5]),(0,[z75,z0,z76,z8,z3,z42]),(0,[z0,z208,z8,z3,z5,z487]),(0,[z187,z8,z3,z5,z6,z82]),(0,[z0,z1,z8,z3,z915,z5])]],
   [[(0,[z404,z1,z8,z3,z5,z6]),(0,[z22,z149,z8,z21,z5,z6]),(0,[z0,z1,z8,z3,z473,z6]),(0,[z0,z1,z8,z3,z798,z5]),(0,[z916,z1,z8,z3,z5,z6])],[(0,[z209,z1,z8,z3,z297,z6])],[(0,[z0,z1,z8,z917,z3,z5]),(0,[z0,z1,z214,z28,z3,z5]),(0,[z0,z1,z8,z3,z42,z297])],[(0,[z0,z1,z8,z3,z918,z6]),(0,[z0,z8,z3,z5,z6,z919]),(0,[z568,z1,z8,z3,z23,z6]),(0,[z0,z1,z8,z3,z920,z5]),(0,[z0,z1,z8,z3,z820,z5]),(0,[z0,z1,z921,z3,z5,z6]),(0,[z0,z1,z8,z59,z42,z54]),(0,[z922,z1,z8,z3,z42,z5])],[(0,[z0,z1,z8,z923,z3,z6]),(0,[z1,z260,z3,z23,z5,z6])],[(0,[z0,z1,z8,z3,z5,z924]),(0,[z0,z380,z3,z9,z5,z6]),(0,[z0,z925,z8,z3,z5,z6]),(0,[z0,z1,z926,z3,z5,z6])],[(0,[z209,z1,z8,z3,z5,z6]),(0,[z0,z219,z336,z3,z5,z6]),(0,[z110,z1,z93,z3,z5,z6])],[(0,[z326,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z927,z3,z6]),(0,[z75,z1,z8,z3,z42,z23]),(0,[z928,z1,z8,z3,z5,z6]),(0,[z0,z1,z929,z3,z42,z5])],[(0,[z326,z0,z2,z3,z5,z6]),(0,[z0,z930,z8,z3,z5,z6]),(0,[z0,z1,z260,z3,z367,z6]),(0,[z359,z373,z8,z3,z5,z6]),(0,[z931,z1,z8,z28,z3,z5])],[(0,[z0,z932,z8,z3,z5,z6]),(0,[z74,z1,z8,z3,z773,z6]),(0,[z35,z1,z262,z3,z5,z6])],[(0,[z1,z137,z3,z21,z5,z6]),(0,[z933,z1,z8,z3,z5,z6])],[(0,[z26,z0,z1,z8,z3,z42]),(0,[z934,z1,z8,z3,z5,z6]),(0,[z111,z0,z373,z8,z3,z42]),(0,[z0,z935,z8,z28,z3,z5])],[(0,[z528,z0,z1,z8,z3,z42])],[(0,[z404,z1,z8,z3,z5,z343]),(0,[z1,z8,z936,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z42]),(0,[z359,z111,z1,z8,z3,z42]),(0,[z111,z0,z1,z3,z4,z389])],[(0,[z0,z1,z8,z3,z42,z463]),(0,[z0,z1,z8,z3,z300,z382]),(0,[z7,z0,z8,z9,z42,z5]),(0,[z106,z8,z3,z5,z6,z517]),(0,[z0,z1,z8,z3,z42,z38])],[(0,[z687,z0,z8,z3,z5,z82]),(0,[z140,z1,z612,z3,z5,z6]),(0,[z0,z1,z937,z3,z5,z6]),(0,[z110,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z938,z6])]],
   [[(0,[z0,z535,z8,z3,z42,z5]),(0,[z1,z8,z939,z3,z5,z6]),(0,[z0,z1,z8,z940,z3,z5])],[(0,[z0,z16,z8,z795,z5,z6]),(0,[z0,z941,z8,z3,z5,z6]),(0,[z0,z942,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z943]),(0,[z22,z330,z8,z21,z5,z6]),(0,[z552,z373,z8,z3,z5,z6]),(0,[z416,z0,z1,z8,z3,z42])],[(0,[z1,z8,z3,z5,z6,z944]),(0,[z0,z197,z1,z410,z3,z42]),(0,[z0,z1,z8,z28,z189,z3])],[(0,[z0,z1,z8,z3,z5,z945]),(0,[z0,z149,z8,z28,z3,z5])],[(0,[z1,z8,z3,z811,z5,z6]),(0,[z0,z208,z8,z18,z3,z6]),(0,[z0,z177,z8,z3,z5,z6]),(0,[z555,z0,z1,z8,z3,z42])],[(0,[z70,z330,z8,z3,z5,z6]),(0,[z157,z1,z8,z3,z42,z5]),(0,[z0,z1,z255,z3,z33,z6]),(0,[z0,z1,z946,z3,z5,z6])],[(0,[z29,z31,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z947]),(0,[z0,z1,z8,z3,z5,z948]),(0,[z1,z8,z121,z5,z6,z342]),(0,[z0,z1,z8,z3,z42,z457]),(0,[z7,z0,z175,z9,z5,z6]),(0,[z63,z209,z1,z108,z5,z6])],[(0,[z1,z8,z612,z3,z5,z6]),(0,[z66,z1,z8,z28,z3,z5]),(0,[z0,z1,z3,z5,z6,z949])],[(0,[z140,z31,z45,z3,z5,z6]),(0,[z12,z503,z45,z3,z5,z6]),(0,[z950,z1,z8,z3,z5,z6]),(0,[z951,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z28,z3,z367]),(0,[z309,z197,z1,z8,z3,z42])],[(0,[z0,z1,z8,z3,z367,z6]),(0,[z952,z1,z8,z3,z5,z6])],[(0,[z327,z30,z8,z3,z5,z6]),(0,[z74,z535,z8,z3,z5,z6]),(0,[z438,z1,z45,z3,z5,z6]),(0,[z7,z404,z8,z9,z5,z6]),(0,[z0,z1,z3,z4,z297,z6]),(0,[z1,z8,z3,z5,z6,z953]),(0,[z0,z1,z49,z3,z4,z6])],[(0,[z67,z30,z84,z3,z5,z6]),(0,[z0,z8,z954,z3,z5,z6])],[(0,[z0,z1,z8,z955,z3,z6]),(0,[z697,z1,z8,z3,z5,z68]),(0,[z0,z1,z57,z3,z42,z5])],[(0,[z0,z1,z454,z8,z3,z42]),(0,[z0,z1,z956,z3,z5,z6]),(0,[z0,z1,z93,z28,z3,z5]),(0,[z0,z146,z8,z3,z89,z6])]],
   [[(0,[z0,z957,z8,z3,z42,z5])],[(1,[z796,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z156,z354]),(0,[z0,z1,z8,z3,z5,z487]),(0,[z0,z1,z8,z3,z52,z42]),(0,[z0,z8,z3,z32,z721,z6]),(0,[z359,z11,z8,z3,z5,z6]),(0,[z0,z1,z3,z42,z5,z558])],[(0,[z958,z1,z8,z3,z5,z6])],[],[(0,[z164,z0,z1,z8,z3,z42]),(0,[z74,z1,z24,z3,z5,z6]),(0,[z0,z1,z8,z3,z959,z5]),(0,[z81,z0,z1,z8,z3,z473]),(0,[z0,z1,z8,z198,z3,z42]),(0,[z0,z1,z8,z3,z42,z526])],[(0,[z67,z1,z84,z3,z5,z6]),(0,[z75,z0,z1,z24,z3,z42])],[(0,[z1,z84,z107,z3,z5,z6]),(0,[z433,z0,z1,z8,z3,z42]),(0,[z0,z330,z8,z28,z3,z5]),(0,[z0,z1,z8,z960,z3,z5]),(0,[z0,z477,z1,z8,z3,z42]),(0,[z81,z0,z8,z3,z5,z82]),(0,[z0,z11,z8,z18,z3,z6]),(0,[z961,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z53,z18,z3]),(0,[z0,z1,z8,z3,z5,z962]),(0,[z813,z1,z8,z3,z5,z6])],[(0,[z12,z29,z2,z3,z5,z6]),(0,[z67,z30,z8,z3,z42,z5]),(0,[z0,z149,z8,z3,z5,z376]),(0,[z0,z1,z8,z3,z963,z6]),(0,[z0,z1,z8,z3,z5,z964])],[(0,[z67,z30,z137,z3,z5,z6]),(0,[z0,z1,z965,z3,z5,z6]),(0,[z0,z1,z8,z966,z3,z5]),(0,[z0,z1,z268,z799,z5,z6])],[(0,[z0,z1,z967,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z840]),(0,[z197,z201,z8,z3,z32,z6]),(0,[z0,z177,z262,z3,z5,z6])],[(0,[z968,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z33,z6]),(0,[z0,z1,z969,z3,z5,z6]),(0,[z0,z8,z53,z3,z5,z517]),(0,[z0,z816,z8,z3,z5,z6])],[],[(0,[z0,z1,z8,z3,z970,z6])],[(0,[z0,z1,z971,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z972]),(0,[z0,z197,z1,z158,z3,z42]),(0,[z0,z973,z8,z3,z5,z6]),(0,[z0,z974,z8,z3,z5,z6]),(0,[z716,z1,z8,z3,z42,z5])],[(0,[z12,z74,z1,z8,z3,z42]),(0,[z1,z8,z3,z5,z6,z249]),(0,[z0,z1,z8,z189,z3,z42])],[(0,[z0,z1,z8,z3,z975,z6]),(0,[z0,z1,z8,z3,z721,z6]),(0,[z0,z1,z3,z799,z5,z6]),(0,[z0,z1,z8,z3,z42,z364]),(0,[z0,z1,z8,z976,z42,z5])]],
   [[(0,[z74,z1,z8,z3,z77,z80]),(0,[z0,z477,z1,z3,z4,z6]),(0,[z0,z1,z8,z977,z3,z5]),(0,[z35,z177,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z978]),(0,[z0,z1,z8,z3,z979,z6])],[(0,[z359,z1,z8,z3,z5,z6]),(0,[z43,z1,z8,z3,z5,z125]),(0,[z0,z1,z8,z3,z980,z6]),(0,[z0,z1,z8,z3,z981,z5])],[(0,[z0,z982,z8,z3,z5,z6]),(0,[z0,z1,z983,z3,z5,z6]),(0,[z0,z1,z8,z3,z984,z6]),(0,[z0,z1,z396,z3,z494,z5])],[(0,[z481,z1,z8,z3,z5,z6]),(0,[z0,z538,z3,z108,z5,z6]),(0,[z74,z314,z1,z8,z3,z42]),(0,[z187,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z985,z6]),(0,[z0,z1,z8,z3,z732,z5])],[(0,[z0,z1,z986,z3,z5,z6]),(0,[z0,z1,z8,z3,z987,z6]),(0,[z0,z1,z8,z3,z5,z758])],[(0,[z13,z1,z612,z3,z5,z6])],[(0,[z0,z1,z8,z3,z656,z42]),(0,[z0,z1,z8,z3,z33,z343]),(0,[z0,z1,z8,z988,z3,z5]),(0,[z0,z1,z8,z3,z42,z171]),(0,[z0,z1,z8,z3,z42,z384]),(0,[z0,z8,z3,z5,z322,z517])],[(0,[z298,z0,z1,z8,z3,z42]),(0,[z404,z1,z8,z3,z5,z382]),(0,[z0,z1,z8,z28,z3,z72])],[(0,[z0,z330,z8,z3,z5,z376]),(0,[z26,z0,z1,z8,z3,z166]),(0,[z0,z1,z8,z3,z134,z42])],[(0,[z29,z0,z380,z3,z5,z6]),(0,[z0,z1,z20,z28,z3,z5]),(0,[z0,z144,z587,z3,z5,z6]),(0,[z0,z373,z3,z4,z5,z6]),(0,[z0,z304,z8,z151,z3,z5])],[(0,[z0,z1,z989,z3,z5,z6]),(0,[z0,z30,z8,z3,z473,z6]),(0,[z12,z0,z538,z3,z5,z6]),(0,[z0,z197,z1,z8,z3,z166]),(0,[z0,z1,z8,z3,z5,z990]),(0,[z0,z1,z8,z28,z3,z732])],[(0,[z0,z1,z8,z3,z991,z5]),(0,[z0,z1,z992,z3,z5,z6]),(0,[z0,z208,z8,z3,z42,z5]),(0,[z75,z1,z8,z294,z3,z6]),(0,[z0,z1,z8,z3,z993,z6])],[(0,[z106,z1,z8,z3,z367,z6]),(0,[z0,z1,z994,z3,z5,z6]),(0,[z0,z1,z8,z3,z995,z6]),(0,[z7,z627,z8,z9,z5,z6]),(0,[z0,z1,z8,z28,z3,z706])],[(0,[z0,z1,z830,z3,z5,z6]),(0,[z0,z1,z8,z371,z3,z42]),(0,[z0,z1,z8,z3,z996,z5]),(0,[z0,z738,z8,z3,z42,z5])],[(0,[z416,z0,z49,z3,z5,z6])]],
   [[(0,[z0,z1,z8,z997,z3,z5]),(0,[z13,z1,z107,z3,z42,z5]),(0,[z131,z1,z3,z108,z5,z6]),(0,[z0,z1,z3,z5,z6,z998])],[(0,[z67,z8,z230,z3,z5,z6]),(0,[z0,z1,z8,z3,z717,z6]),(0,[z0,z227,z8,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z999]),(0,[z338,z1,z8,z235,z3,z5])],[(0,[z0,z1,z8,z3,z287,z50])],[(0,[z1000,z1,z8,z3,z5,z6]),(0,[z0,z1,z69,z8,z3,z171])],[(0,[z0,z1,z8,z28,z3,z424]),(0,[z309,z1,z8,z18,z3,z6]),(0,[z0,z146,z8,z3,z5,z226]),(0,[z0,z1,z8,z39,z128,z491])],[(0,[z0,z1,z8,z3,z732,z6])],[(0,[z0,z1,z1001,z3,z5,z6]),(0,[z26,z0,z8,z3,z27,z6]),(0,[z0,z1,z8,z3,z166,z54]),(0,[z1002,z1,z8,z3,z5,z6])],[(0,[z1,z31,z84,z3,z5,z6]),(0,[z157,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1003,z6]),(0,[z0,z1,z8,z1004,z3,z5]),(0,[z0,z1,z8,z3,z764,z5]),(0,[z0,z1,z8,z3,z42,z345])],[(0,[z0,z1,z8,z3,z1005,z6]),(0,[z0,z1,z799,z108,z5,z6]),(0,[z0,z1,z8,z374,z3,z491])],[(0,[z0,z1,z1006,z3,z5,z6]),(0,[z0,z1,z262,z3,z5,z758]),(0,[z0,z1,z369,z3,z5,z183]),(1,[z0,z1,z8,z6,z771])],[(0,[z0,z149,z8,z3,z5,z354]),(0,[z100,z1,z8,z3,z5,z840]),(0,[z1007,z1,z8,z3,z5,z6]),(0,[z0,z1,z255,z3,z42,z5])],[(0,[z0,z361,z8,z3,z32,z6]),(0,[z0,z380,z3,z5,z6,z82]),(0,[z0,z1,z8,z1008,z5,z6]),(0,[z0,z1,z8,z3,z1009,z5])],[(0,[z1,z612,z3,z4,z5,z6]),(0,[z404,z8,z3,z9,z5,z6]),(0,[z1010,z1,z8,z3,z5,z6])],[(0,[z0,z208,z8,z3,z42,z6]),(0,[z26,z0,z278,z8,z3,z42]),(0,[z0,z88,z17,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z89]),(0,[z0,z11,z8,z3,z42,z5])],[],[(0,[z100,z0,z1,z8,z3,z424]),(0,[z1011,z1,z8,z3,z5,z6])]],
   [[(0,[z404,z1,z8,z3,z33,z6]),(0,[z111,z0,z1,z3,z717,z6]),(0,[z34,z0,z177,z3,z5,z36])],[(0,[z361,z1,z8,z3,z23,z6]),(0,[z0,z1,z1012,z3,z5,z6])],[(0,[z0,z224,z8,z3,z42,z5]),(0,[z1013,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z253,z3,z355]),(0,[z0,z1,z3,z5,z6,z758]),(0,[z0,z1,z1014,z28,z3,z5])],[(0,[z0,z1,z8,z3,z5,z1015]),(0,[z259,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z3,z5,z1016]),(0,[z0,z1017,z8,z3,z5,z6]),(0,[z74,z1,z8,z3,z80,z6]),(0,[z0,z197,z410,z3,z32,z6]),(0,[z0,z1018,z8,z3,z5,z6])],[(0,[z0,z1,z84,z3,z5,z6]),(0,[z0,z1,z46,z3,z42,z5]),(0,[z0,z1,z8,z1019,z3,z6])],[(0,[z0,z1,z8,z3,z42,z460])],[(0,[z0,z1,z8,z3,z287,z5])],[(0,[z0,z1,z8,z1020,z3,z5]),(0,[z0,z1,z8,z3,z5,z1021]),(0,[z131,z1,z17,z3,z5,z6]),(0,[z0,z1,z8,z1022,z3,z5])],[(0,[z67,z796,z8,z3,z5,z6]),(0,[z12,z1,z45,z3,z42,z5]),(0,[z1,z8,z811,z21,z5,z6]),(0,[z0,z8,z3,z5,z6,z1023]),(0,[z0,z1,z86,z3,z171,z6]),(0,[z111,z0,z373,z3,z4,z6])],[(0,[z0,z1,z1024,z3,z5,z6]),(0,[z0,z208,z214,z3,z5,z6]),(0,[z1025,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z473,z128]),(0,[z106,z1,z8,z18,z3,z6]),(0,[z0,z1,z8,z821,z5,z6])],[(0,[z0,z1,z46,z3,z156,z6]),(0,[z0,z1,z8,z3,z5,z1026]),(0,[z0,z94,z1,z8,z3,z473]),(0,[z0,z1,z17,z28,z3,z95]),(0,[z359,z111,z1,z3,z4,z6])],[(0,[z0,z1,z8,z3,z683,z42]),(0,[z0,z1,z49,z28,z3,z5])],[(0,[z0,z330,z8,z3,z5,z354]),(0,[z0,z1,z8,z28,z3,z300]),(0,[z0,z60,z8,z3,z32,z6]),(0,[z63,z0,z1,z108,z42,z5])],[(0,[z0,z1,z1027,z3,z5,z6]),(0,[z0,z8,z1028,z3,z5,z6]),(0,[z0,z1,z1029,z3,z5,z6]),(0,[z209,z1,z8,z3,z5,z127]),(0,[z0,z146,z8,z3,z297,z6]),(0,[z0,z1,z8,z222,z5,z61])],[(0,[z0,z11,z8,z3,z42,z6]),(0,[z0,z1,z8,z28,z3,z42])],[(0,[z0,z1,z137,z3,z5,z6]),(0,[z0,z1,z8,z803,z3,z367]),(0,[z0,z1,z8,z59,z28,z54]),(0,[z0,z1,z8,z3,z5,z1030])]],
   [[(0,[z1031,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1032]),(0,[z0,z1,z1033,z3,z5,z6])],[(0,[z0,z76,z8,z3,z5,z6]),(0,[z0,z1034,z8,z3,z5,z6]),(0,[z0,z1,z2,z3,z171,z6]),(0,[z0,z1035,z8,z3,z5,z6]),(0,[z0,z1,z17,z3,z95,z6])],[(0,[z0,z503,z8,z3,z5,z6]),(0,[z13,z1,z137,z3,z5,z6]),(0,[z272,z1,z8,z21,z5,z6]),(0,[z0,z1,z8,z3,z5,z1036]),(0,[z74,z1,z8,z3,z42,z231]),(0,[z43,z1,z8,z3,z5,z44]),(0,[z0,z1,z8,z3,z424,z37]),(0,[z0,z146,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1037]),(0,[z0,z1,z8,z3,z33,z382]),(0,[z555,z0,z1,z3,z4,z6]),(0,[z416,z0,z8,z59,z6,z54])],[(0,[z0,z1,z8,z3,z1038,z6]),(0,[z0,z1,z8,z150,z3,z6]),(0,[z0,z1,z8,z3,z5,z1039]),(0,[z1040,z1,z8,z3,z5,z6])],[(0,[z0,z1,z1041,z3,z5,z6]),(0,[z75,z208,z8,z3,z23,z6]),(0,[z0,z116,z8,z3,z42,z5]),(0,[z34,z0,z227,z3,z5,z36]),(0,[z0,z1,z8,z321,z638,z5])],[(0,[z0,z1,z86,z17,z3,z42]),(0,[z0,z1,z8,z1042,z3,z5])],[(0,[z0,z1043,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z40])],[(0,[z535,z8,z3,z23,z5,z6]),(0,[z0,z1,z175,z3,z5,z6]),(0,[z1044,z1,z8,z3,z5,z6]),(0,[z316,z0,z1,z3,z5,z36]),(0,[z416,z0,z3,z5,z6,z558]),(0,[z0,z49,z3,z5,z6,z517]),(0,[z0,z8,z3,z42,z517,z54])],[(0,[z0,z1,z8,z3,z1045,z6]),(0,[z1046,z1,z8,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1047])],[(0,[z0,z1,z8,z3,z1048,z6]),(0,[z0,z1,z410,z3,z5,z6])],[(0,[z0,z1,z1049,z3,z5,z6]),(0,[z67,z516,z8,z3,z5,z6]),(0,[z0,z1050,z8,z3,z5,z6]),(0,[z277,z1,z8,z3,z42,z5])],[(0,[z70,z1,z8,z635,z5,z6]),(0,[z0,z1051,z8,z3,z5,z6])],[(0,[z66,z144,z86,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1052]),(0,[z81,z110,z8,z3,z5,z82]),(0,[z0,z88,z8,z28,z3,z5]),(0,[z1,z8,z53,z3,z5,z249])],[(0,[z26,z0,z8,z3,z295,z6]),(0,[z0,z1,z8,z646,z3,z42])],[(0,[z0,z1053,z8,z3,z5,z6]),(0,[z0,z1,z1054,z3,z5,z6]),(0,[z352,z0,z1,z108,z5,z6]),(0,[z0,z1,z158,z3,z42,z5]),(0,[z0,z905,z8,z3,z5,z6])],[(0,[z0,z1,z1055,z3,z5,z6]),(0,[z75,z1,z8,z3,z773,z6]),(0,[z0,z1,z8,z253,z3,z42])]],
   [[(0,[z66,z1,z107,z3,z5,z6]),(0,[z0,z76,z8,z3,z5,z347])],[(0,[z147,z1,z107,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1056]),(0,[z0,z1,z8,z3,z5,z1057]),(0,[z0,z1058,z8,z3,z5,z6])],[(0,[z0,z1059,z8,z3,z5,z6]),(0,[z0,z58,z538,z3,z5,z6]),(0,[z0,z1,z8,z150,z3,z347]),(0,[z197,z201,z1,z8,z3,z42])],[(0,[z0,z1,z8,z3,z5,z1060]),(0,[z433,z0,z1,z3,z4,z6]),(0,[z0,z1,z8,z3,z1061,z6]),(0,[z0,z1,z8,z28,z3,z545])],[(0,[z0,z1,z45,z3,z171,z6]),(0,[z1062,z1,z8,z3,z5,z6]),(0,[z201,z1,z8,z3,z5,z355])],[(0,[z12,z1,z465,z3,z5,z6]),(0,[z0,z1,z1063,z3,z5,z6]),(0,[z0,z1,z1064,z3,z5,z6]),(0,[z0,z1065,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z1066]),(0,[z0,z175,z3,z32,z5,z6]),(0,[z309,z1,z410,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z322])],[(0,[z74,z1,z8,z107,z3,z42]),(0,[z0,z1,z3,z5,z6,z1067]),(0,[z0,z8,z3,z5,z761,z82]),(0,[z0,z373,z8,z3,z42,z5]),(0,[z136,z0,z1,z3,z5,z36]),(0,[z0,z1,z49,z59,z6,z54])],[(0,[z0,z1,z8,z3,z5,z1068]),(0,[z0,z1,z8,z3,z1069,z6]),(0,[z1070,z0,z1,z3,z5,z6]),(0,[z26,z0,z8,z3,z42,z531])],[(0,[z100,z1,z8,z150,z3,z68]),(0,[z100,z1,z8,z3,z231,z5]),(0,[z0,z1,z49,z3,z95,z6]),(0,[z1,z8,z3,z5,z322,z249]),(0,[z0,z1,z8,z3,z5,z1071])],[(0,[z74,z1,z8,z3,z357,z6]),(0,[z0,z1,z8,z3,z1072,z5]),(0,[z0,z1,z1073,z3,z5,z6]),(0,[z124,z1,z8,z3,z231,z5])],[(1,[z1,z725,z3,z5,z6])],[(0,[z67,z30,z20,z3,z5,z6]),(0,[z0,z1,z8,z3,z1074,z6]),(0,[z0,z8,z538,z28,z3,z5]),(0,[z0,z144,z86,z3,z42,z5])],[(0,[z70,z535,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1075])],[(0,[z1076,z1,z8,z3,z5,z6]),(0,[z106,z416,z8,z3,z5,z6]),(0,[z0,z1,z8,z824,z42,z5])],[(0,[z430,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z3,z42,z508])]],
   [[(0,[z0,z1,z1077,z3,z5,z6]),(0,[z131,z88,z8,z3,z5,z6])],[(0,[z0,z1078,z8,z3,z5,z6]),(0,[z931,z1,z8,z3,z5,z6])],[(0,[z399,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z3,z42,z654]),(0,[z0,z219,z8,z3,z42,z5])],[(0,[z0,z149,z46,z3,z5,z6]),(0,[z552,z1,z3,z4,z5,z6])],[(0,[z22,z1,z8,z21,z5,z354]),(0,[z22,z1,z8,z811,z5,z6]),(0,[z43,z1,z8,z184,z3,z5]),(0,[z0,z935,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1079,z5]),(0,[z0,z1,z8,z3,z5,z1080]),(0,[z0,z8,z2,z3,z473,z6]),(0,[z0,z1,z17,z3,z349,z6]),(0,[z0,z1,z8,z1081,z5,z6])],[(0,[z0,z1,z1082,z3,z5,z6]),(0,[z0,z1,z1083,z3,z5,z6]),(0,[z0,z1,z1084,z3,z5,z6])],[(0,[z0,z796,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z33]),(0,[z1085,z1,z8,z3,z5,z6])],[(0,[z70,z1,z8,z121,z5,z6]),(0,[z0,z16,z175,z3,z5,z6]),(0,[z26,z0,z8,z145,z3,z27])],[(0,[z0,z1,z8,z18,z3,z347]),(0,[z416,z0,z8,z28,z3,z5])],[(0,[z0,z1,z1086,z3,z5,z6]),(0,[z427,z31,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1087]),(0,[z1088,z1,z8,z3,z5,z6]),(0,[z63,z0,z1,z464,z5,z6]),(1,[z359,z1,z8,z3,z42]),(0,[z0,z1089,z8,z3,z5,z6]),(0,[z0,z1,z1090,z28,z3,z5])],[],[(0,[z0,z1091,z8,z3,z5,z6]),(0,[z34,z0,z1,z3,z5,z758])],[(0,[z0,z149,z8,z3,z5,z6]),(0,[z272,z0,z1,z108,z5,z6]),(0,[z0,z535,z8,z28,z3,z5]),(1,[z1,z8,z3,z773,z6]),(0,[z0,z1,z8,z3,z5,z1092]),(0,[z0,z1,z8,z3,z42,z50])],[(0,[z0,z1093,z8,z3,z5,z6]),(0,[z0,z1,z260,z3,z42,z5]),(0,[z0,z11,z8,z3,z5,z332])],[(0,[z0,z57,z3,z5,z6,z82]),(0,[z81,z0,z8,z3,z473,z82]),(0,[z0,z1,z8,z329,z3,z42])]],
   [[(0,[z416,z0,z8,z3,z27,z6]),(0,[z360,z0,z8,z3,z531,z5])],[(0,[z66,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z1094,z3,z300]),(0,[z0,z1,z8,z3,z1095,z6])],[],[(0,[z0,z20,z2,z3,z5,z6]),(0,[z0,z1096,z8,z3,z5,z6]),(0,[z157,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z1097,z6]),(0,[z0,z1098,z8,z3,z5,z6])],[(0,[z436,z31,z8,z3,z5,z6]),(0,[z0,z361,z1,z8,z3,z42]),(0,[z67,z1,z8,z3,z424,z6]),(0,[z0,z1,z260,z3,z156,z6]),(0,[z0,z1,z8,z28,z3,z473]),(0,[z0,z1,z8,z3,z5,z1099])],[(0,[z0,z330,z46,z3,z5,z6]),(0,[z0,z1,z24,z28,z3,z5]),(0,[z0,z1,z8,z1100,z3,z5]),(0,[z0,z1,z8,z3,z42,z600])],[(0,[z29,z585,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z835,z5]),(0,[z0,z1,z8,z3,z5,z1101])],[],[(0,[z0,z1,z8,z3,z5,z1102]),(0,[z0,z1,z93,z3,z5,z6]),(0,[z309,z0,z1,z8,z3,z42]),(0,[z106,z1,z8,z3,z5,z322]),(0,[z0,z1,z1103,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1104,z6]),(0,[z1105,z1,z8,z3,z5,z6])],[(0,[z796,z31,z8,z3,z5,z6]),(0,[z74,z1,z260,z3,z5,z6]),(0,[z43,z1,z8,z3,z5,z840]),(0,[z63,z131,z1,z108,z5,z6]),(0,[z1106,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z39,z638,z5])],[(0,[z0,z1107,z8,z3,z5,z6]),(0,[z0,z1,z57,z28,z3,z5])],[],[(0,[z0,z1,z1108,z3,z5,z6]),(0,[z0,z262,z538,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1109]),(0,[z1110,z1,z8,z3,z5,z6])],[(0,[z0,z1,z1111,z3,z5,z6]),(0,[z0,z1112,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1113,z6])],[(0,[z0,z1114,z8,z3,z5,z6]),(0,[z43,z0,z1,z8,z3,z424]),(0,[z0,z1,z175,z3,z5,z382]),(0,[z0,z1,z8,z181,z42,z50])]],
   [[(0,[z1115,z1,z8,z3,z5,z6]),(0,[z481,z81,z8,z3,z5,z82]),(0,[z0,z1,z8,z28,z167,z3])],[(0,[z0,z1,z8,z3,z42,z5]),(0,[z0,z1,z472,z28,z3,z5]),(0,[z111,z0,z1,z8,z3,z42])],[(0,[z70,z1,z8,z275,z5,z6]),(0,[z0,z1,z8,z28,z150,z3]),(0,[z0,z1,z8,z3,z42,z349])],[(0,[z0,z1116,z8,z3,z5,z6]),(0,[z0,z1117,z8,z3,z5,z6]),(0,[z0,z1,z1118,z3,z5,z6])],[(0,[z0,z1119,z8,z3,z5,z6]),(0,[z0,z1,z262,z3,z5,z658]),(0,[z22,z1,z8,z21,z5,z376]),(0,[z314,z1,z8,z3,z5,z44]),(0,[z0,z1,z8,z3,z728,z54]),(0,[z0,z1,z8,z181,z50,z6])],[(0,[z0,z1,z8,z3,z1120,z6]),(0,[z627,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z42,z634]),(0,[z0,z11,z8,z3,z5,z389]),(0,[z0,z60,z1,z8,z3,z42]),(0,[z887,z1,z8,z3,z5,z6])],[(0,[z571,z0,z2,z3,z5,z6]),(0,[z0,z1,z175,z3,z300,z6]),(0,[z1121,z1,z8,z3,z5,z6]),(0,[z201,z1,z8,z28,z3,z5])],[(0,[z0,z1,z8,z3,z156,z6]),(0,[z0,z1,z8,z3,z1122,z6])],[(0,[z0,z76,z8,z3,z5,z487]),(0,[z0,z1,z8,z3,z171,z37]),(0,[z1123,z1,z8,z3,z5,z6]),(0,[z0,z1,z69,z114,z3,z5])],[(0,[z438,z30,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1124,z6]),(0,[z0,z197,z8,z3,z42,z32])],[(0,[z76,z8,z3,z23,z5,z6]),(0,[z0,z8,z795,z9,z5,z6]),(0,[z0,z1125,z8,z28,z3,z5])],[(0,[z0,z30,z20,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z533]),(0,[z330,z8,z3,z21,z5,z6]),(0,[z0,z1,z1126,z3,z5,z6]),(0,[z0,z1,z8,z3,z821,z5])],[(0,[z0,z1,z8,z1127,z3,z5]),(0,[z0,z1,z8,z3,z5,z1128]),(0,[z277,z34,z1,z3,z5,z36])],[(0,[z0,z1129,z8,z3,z5,z6]),(0,[z12,z1,z339,z3,z5,z6]),(0,[z352,z0,z8,z9,z5,z6]),(0,[z26,z0,z8,z3,z463,z6]),(0,[z106,z0,z1,z8,z3,z42])],[(0,[z12,z503,z8,z3,z5,z6]),(0,[z302,z0,z2,z3,z5,z6]),(0,[z309,z1,z8,z3,z42,z5])],[(0,[z0,z1,z1130,z3,z5,z6]),(0,[z140,z0,z2,z3,z5,z6]),(0,[z26,z0,z8,z3,z531,z6]),(0,[z0,z1,z17,z8,z3,z273])]],
   [[(0,[z0,z1131,z8,z3,z5,z6]),(0,[z0,z1132,z8,z3,z5,z6]),(0,[z0,z1,z1133,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1134,z6]),(0,[z0,z1,z8,z740,z5,z6]),(0,[z0,z1,z1135,z3,z5,z6]),(0,[z63,z0,z1,z28,z108,z5])],[(0,[z0,z1,z1136,z3,z5,z6]),(0,[z0,z1,z8,z3,z728,z42])],[(0,[z0,z1,z20,z3,z5,z6]),(0,[z0,z8,z1137,z3,z5,z6]),(0,[z0,z1,z396,z3,z5,z183]),(0,[z1138,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z42,z178]),(0,[z0,z144,z401,z3,z5,z6]),(1,[z0,z11,z8,z3,z42]),(0,[z0,z1,z8,z42,z50,z54]),(0,[z0,z1,z890,z3,z42,z5])],[(0,[z22,z1,z8,z28,z21,z5]),(0,[z1139,z1,z8,z3,z5,z6]),(0,[z1140,z1,z8,z3,z5,z6]),(0,[z111,z0,z1,z28,z3,z4])],[(0,[z1,z31,z8,z3,z424,z6]),(0,[z0,z1,z1141,z3,z5,z6]),(0,[z0,z1,z8,z3,z1142,z5]),(0,[z1143,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z389])],[(0,[z0,z1144,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1145]),(0,[z0,z1,z175,z3,z5,z343])],[(0,[z0,z1,z8,z3,z5,z1146]),(0,[z0,z1,z8,z3,z1147,z5]),(0,[z593,z0,z1,z8,z3,z42]),(0,[z0,z1,z1148,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1149]),(0,[z0,z373,z8,z3,z5,z332]),(0,[z111,z0,z1,z8,z3,z820])],[(0,[z0,z1,z158,z3,z5,z355]),(0,[z131,z1,z8,z28,z3,z5]),(0,[z0,z146,z8,z3,z5,z127]),(0,[z0,z1,z8,z3,z1150,z5]),(0,[z0,z1,z8,z1151,z3,z6])],[(0,[z0,z1,z1152,z3,z5,z6]),(0,[z0,z1,z58,z99,z5,z6]),(0,[z22,z74,z1,z8,z3,z42])],[(0,[z0,z1,z842,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1153,z6]),(0,[z0,z1,z3,z717,z95,z6]),(0,[z35,z1,z8,z3,z42,z5])],[(0,[z0,z149,z260,z3,z5,z6]),(0,[z22,z1,z46,z21,z5,z6]),(0,[z620,z1,z8,z3,z5,z44]),(0,[z0,z1,z1154,z3,z5,z6]),(0,[z0,z8,z191,z795,z5,z6])],[(0,[z0,z1,z8,z3,z5,z1155]),(0,[z461,z31,z8,z3,z5,z6]),(0,[z0,z1,z214,z3,z5,z6]),(0,[z157,z535,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z860,z5])],[(0,[z0,z1,z1156,z3,z5,z6]),(0,[z309,z1,z8,z3,z42,z6]),(0,[z416,z0,z8,z53,z3,z5])]],
   [[(0,[z552,z1,z8,z3,z42,z5]),(0,[z0,z1,z1157,z3,z5,z6])],[(0,[z0,z1158,z8,z3,z5,z6]),(0,[z1,z24,z3,z23,z5,z6]),(0,[z0,z1,z8,z3,z42,z347]),(0,[z0,z1,z8,z760,z5,z6]),(0,[z0,z1,z17,z396,z3,z42])],[(0,[z12,z1,z612,z3,z5,z6]),(0,[z1159,z1,z8,z3,z5,z6]),(0,[z7,z0,z8,z795,z5,z6]),(0,[z0,z1,z8,z28,z3,z297])],[(0,[z29,z144,z107,z3,z5,z6]),(0,[z0,z1,z8,z3,z1160,z6]),(0,[z0,z1,z8,z1161,z3,z6]),(0,[z0,z1,z1162,z3,z5,z6]),(0,[z0,z1,z8,z5,z6,z771]),(0,[z106,z1,z8,z3,z42,z5]),(0,[z0,z1,z28,z3,z5,z558])],[(0,[z0,z1,z45,z17,z3,z42]),(0,[z0,z1,z8,z3,z1163,z6]),(0,[z1164,z1,z8,z3,z5,z6]),(0,[z81,z0,z8,z3,z531,z5]),(0,[z0,z914,z8,z3,z42,z5])],[(0,[z0,z1,z1165,z3,z5,z6]),(0,[z0,z1,z1166,z3,z5,z6]),(0,[z0,z1,z8,z3,z1167,z6]),(0,[z110,z94,z8,z3,z5,z6]),(0,[z110,z1,z57,z3,z5,z6])],[(0,[z0,z1168,z8,z3,z5,z6]),(0,[z251,z0,z1,z8,z3,z42]),(0,[z0,z182,z1,z8,z3,z42]),(0,[z1169,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z77,z54]),(0,[z75,z1,z8,z28,z3,z23]),(0,[z404,z1,z8,z3,z42,z5]),(0,[z0,z88,z8,z3,z5,z226]),(0,[z0,z1,z8,z3,z42,z491])],[(0,[z535,z8,z3,z5,z6,z68]),(0,[z0,z1170,z8,z3,z5,z6]),(0,[z0,z208,z1,z8,z3,z42]),(0,[z26,z0,z158,z3,z5,z6]),(0,[z0,z1,z8,z28,z253,z3]),(0,[z0,z1,z8,z28,z3,z586])],[(0,[z0,z1,z17,z107,z3,z42]),(0,[z75,z1,z8,z3,z23,z6]),(0,[z0,z1,z8,z3,z849,z300])],[(0,[z1,z8,z107,z3,z424,z6]),(0,[z0,z144,z830,z3,z5,z6]),(0,[z0,z1,z921,z3,z42,z5])],[(0,[z0,z1,z1171,z3,z5,z6]),(0,[z0,z1,z3,z4,z717,z6]),(0,[z34,z0,z1,z189,z3,z36]),(0,[z0,z1,z1014,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z1172]),(0,[z1,z8,z3,z23,z773,z6]),(0,[z0,z1,z3,z5,z758,z36]),(0,[z0,z3,z5,z6,z558,z517])],[(0,[z98,z0,z1,z8,z3,z42]),(0,[z0,z8,z3,z5,z6,z1173]),(0,[z0,z1,z214,z3,z5,z347]),(0,[z0,z1,z8,z3,z1174,z5]),(0,[z1,z8,z3,z5,z6,z1175]),(0,[z209,z1,z8,z3,z42,z5]),(0,[z63,z0,z1,z17,z3,z42]),(0,[z0,z1,z8,z3,z40,z6])],[(0,[z0,z149,z8,z3,z367,z6]),(0,[z0,z1,z3,z5,z6,z1176]),(0,[z0,z1,z1177,z3,z5,z6])],[(0,[z0,z330,z260,z3,z5,z6]),(0,[z0,z144,z8,z3,z473,z6]),(0,[z110,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z42,z301]),(0,[z0,z1,z8,z3,z273,z54]),(0,[z0,z373,z8,z3,z5,z389])]],
   [[(0,[z43,z1,z137,z3,z5,z6]),(0,[z0,z1,z8,z3,z1178,z5]),(0,[z1179,z1,z8,z3,z5,z6]),(0,[z1,z612,z3,z108,z5,z6]),(0,[z404,z1,z175,z3,z5,z6]),(0,[z0,z175,z3,z9,z5,z6]),(0,[z81,z0,z8,z3,z5,z761]),(0,[z1180,z1,z8,z3,z5,z6])],[(0,[z1,z107,z3,z5,z6,z168]),(0,[z0,z1,z46,z28,z3,z5]),(0,[z0,z1181,z8,z3,z5,z6]),(0,[z209,z146,z8,z3,z5,z6]),(0,[z933,z1,z8,z3,z42,z5])],[(0,[z359,z1,z8,z18,z3,z6])],[(0,[z0,z1,z8,z3,z42,z276]),(0,[z0,z780,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1182]),(0,[z0,z8,z3,z5,z6,z761]),(0,[z0,z1,z8,z3,z5,z1183])],[(0,[z0,z1,z8,z3,z5,z1184]),(0,[z0,z1,z8,z3,z5,z1185]),(0,[z0,z94,z57,z3,z5,z6]),(0,[z0,z1,z8,z3,z1186,z6]),(0,[z0,z1,z262,z3,z5,z183]),(0,[z106,z1,z8,z3,z42,z6]),(0,[z0,z1,z49,z53,z3,z5])],[(0,[z0,z1,z8,z3,z1187,z6]),(0,[z0,z373,z17,z3,z5,z6]),(0,[z111,z0,z1,z573,z3,z6])],[(0,[z0,z830,z2,z3,z5,z6]),(0,[z0,z197,z8,z3,z32,z355])],[(0,[z29,z31,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z1188,z6]),(0,[z0,z1,z8,z3,z42,z85]),(1,[z0,z1,z49,z3,z42]),(0,[z0,z1,z8,z53,z3,z42])],[(0,[z527,z31,z8,z3,z5,z6]),(0,[z75,z1,z8,z3,z23,z347]),(0,[z314,z1,z8,z3,z162,z5]),(0,[z0,z941,z8,z3,z42,z5]),(0,[z0,z942,z8,z3,z42,z5])],[(0,[z100,z1,z8,z3,z424,z68]),(0,[z0,z1,z58,z28,z268,z5]),(0,[z0,z1,z17,z3,z273,z95]),(0,[z0,z11,z1,z8,z3,z42])],[(0,[z0,z224,z86,z3,z5,z6]),(0,[z0,z144,z538,z3,z5,z6]),(0,[z26,z187,z8,z3,z5,z6])],[(0,[z338,z1,z8,z3,z5,z68]),(0,[z236,z0,z1,z8,z3,z473])],[(0,[z0,z1,z8,z3,z812,z89]),(0,[z0,z177,z8,z3,z42,z5]),(0,[z0,z1,z8,z444,z128,z5])],[(0,[z0,z116,z472,z3,z5,z6]),(0,[z0,z8,z191,z5,z6,z451])],[(0,[z0,z88,z58,z3,z5,z6])],[(0,[z1,z137,z3,z23,z5,z6]),(0,[z1189,z1,z8,z3,z5,z6]),(0,[z1,z8,z612,z3,z42,z5]),(0,[z0,z1,z17,z202,z3,z95])]],
   [[(0,[z70,z1,z8,z811,z5,z6]),(0,[z0,z88,z8,z3,z297,z6]),(0,[z951,z1,z8,z3,z42,z5])],[(0,[z0,z585,z86,z3,z5,z6]),(0,[z0,z1,z725,z3,z5,z6]),(0,[z0,z116,z8,z28,z3,z5]),(0,[z0,z1,z1190,z3,z5,z6]),(0,[z0,z1,z8,z3,z491,z37])],[(0,[z0,z330,z8,z3,z5,z6]),(0,[z0,z1,z380,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z332])],[(0,[z12,z1,z84,z3,z5,z6]),(0,[z1,z84,z612,z3,z5,z6]),(0,[z0,z224,z2,z3,z5,z6]),(0,[z0,z144,z370,z3,z5,z6]),(0,[z1191,z1,z8,z3,z5,z6]),(0,[z359,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z28,z3,z40])],[(0,[z0,z1192,z8,z3,z5,z6]),(0,[z13,z1,z725,z3,z5,z6]),(0,[z0,z1,z46,z3,z5,z376]),(0,[z81,z0,z93,z3,z5,z82])],[(0,[z0,z2,z3,z5,z6,z574]),(0,[z0,z88,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1193,z5]),(0,[z0,z88,z8,z3,z89,z6])],[(0,[z0,z1,z8,z3,z5,z1194]),(0,[z67,z13,z2,z3,z5,z6]),(0,[z496,z0,z1,z8,z3,z42]),(0,[z0,z1,z8,z3,z1195,z6]),(0,[z0,z1,z956,z3,z42,z5])],[(0,[z67,z30,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z1196,z6])],[(0,[z67,z187,z8,z3,z5,z6]),(0,[z433,z1,z8,z3,z23,z6]),(0,[z0,z1,z107,z3,z171,z6]),(0,[z236,z0,z1,z8,z3,z42])],[(0,[z0,z1197,z8,z3,z5,z6]),(0,[z194,z0,z1,z8,z3,z42])],[(0,[z0,z403,z86,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1198]),(0,[z1199,z1,z8,z3,z5,z6]),(0,[z0,z628,z86,z3,z5,z6]),(0,[z1200,z1,z8,z3,z5,z6])],[(0,[z0,z1,z8,z1201,z3,z5]),(0,[z0,z1202,z8,z3,z5,z6])],[(0,[z0,z1203,z8,z3,z5,z6]),(0,[z0,z208,z24,z3,z5,z6]),(0,[z0,z1,z336,z3,z42,z5]),(0,[z0,z1,z8,z3,z5,z355]),(0,[z1,z49,z3,z5,z6,z249])],[(0,[z0,z1,z8,z3,z1204,z5]),(0,[z0,z1,z1205,z3,z5,z6]),(0,[z0,z8,z1206,z3,z5,z6]),(0,[z874,z1,z8,z3,z42,z5])],[(0,[z326,z1,z107,z3,z5,z6]),(0,[z0,z1,z8,z1207,z3,z5]),(0,[z74,z1,z8,z3,z367,z6]),(0,[z22,z1,z8,z288,z5,z6]),(0,[z0,z1208,z8,z3,z5,z6]),(0,[z111,z0,z1,z3,z4,z6])],[(0,[z0,z1,z262,z3,z5,z663]),(0,[z131,z1,z8,z3,z89,z6]),(0,[z0,z1,z8,z1209,z3,z6])]],
   [[(0,[z0,z1,z8,z3,z5,z1210]),(0,[z0,z1,z8,z3,z5,z1211])],[(0,[z0,z1,z8,z3,z1212,z6]),(0,[z201,z1,z8,z3,z5,z179])],[(0,[z0,z1,z8,z3,z1213,z6]),(0,[z481,z1,z93,z3,z5,z6])],[(0,[z0,z1,z8,z3,z773,z6]),(0,[z0,z1,z8,z3,z1214,z6])],[(0,[z187,z1,z8,z28,z3,z5]),(0,[z1215,z1,z8,z3,z5,z6]),(0,[z34,z0,z1,z3,z470,z5])],[(0,[z0,z1,z3,z5,z183,z758])],[(0,[z0,z1,z8,z3,z1216,z6]),(0,[z0,z224,z45,z3,z5,z6]),(0,[z0,z1,z8,z1217,z3,z6]),(0,[z0,z1,z8,z3,z6,z771])],[(0,[z503,z8,z107,z3,z5,z6]),(0,[z22,z1,z260,z21,z5,z6]),(0,[z0,z1,z1218,z3,z5,z6]),(0,[z26,z0,z8,z3,z300,z6]),(0,[z0,z1,z8,z28,z3,z171]),(0,[z0,z1,z8,z59,z6,z54])],[(0,[z0,z144,z465,z3,z5,z6]),(0,[z0,z31,z8,z3,z473,z6])],[(0,[z0,z1,z8,z3,z1219,z6]),(0,[z26,z0,z380,z3,z5,z6]),(0,[z0,z144,z86,z28,z3,z5]),(0,[z922,z1,z8,z3,z5,z6]),(0,[z309,z1,z8,z3,z5,z355]),(0,[z359,z1,z8,z3,z42,z5])],[(0,[z0,z1,z175,z3,z33,z6]),(0,[z0,z1,z17,z3,z297,z6])],[(0,[z31,z8,z3,z447,z5,z6]),(0,[z0,z538,z3,z5,z6,z36]),(0,[z0,z219,z472,z3,z5,z6]),(0,[z481,z1,z8,z3,z42,z5]),(0,[z416,z0,z8,z3,z42,z54]),(0,[z0,z1220,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z1221]),(0,[z0,z208,z8,z28,z3,z5]),(0,[z0,z1,z3,z5,z6,z558])],[(0,[z0,z1,z8,z3,z1222,z5]),(0,[z26,z0,z197,z8,z3,z42]),(0,[z0,z1,z929,z3,z5,z6]),(0,[z0,z1,z8,z253,z3,z6]),(0,[z0,z1,z8,z6,z771,z54]),(0,[z416,z8,z3,z5,z6,z249])],[(0,[z525,z1,z107,z3,z5,z6]),(0,[z0,z1,z8,z434,z5,z37]),(0,[z94,z187,z8,z3,z5,z6]),(0,[z416,z0,z8,z3,z300,z6])],[(0,[z0,z1,z8,z3,z1223,z6]),(0,[z0,z1,z8,z960,z3,z156]),(0,[z0,z1,z8,z189,z3,z6])]],
   [[(0,[z13,z1,z107,z28,z3,z5]),(0,[z12,z535,z45,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1224]),(0,[z0,z1,z8,z3,z166,z50])],[(0,[z0,z1,z8,z3,z42,z238]),(0,[z1225,z1,z8,z3,z5,z6]),(0,[z552,z1,z8,z3,z5,z332]),(0,[z0,z227,z8,z28,z3,z5])],[(0,[z31,z465,z8,z3,z5,z6]),(0,[z1,z45,z137,z3,z5,z6]),(0,[z416,z0,z8,z3,z5,z6]),(0,[z26,z0,z8,z3,z42,z27]),(0,[z0,z1,z8,z3,z5,z1226])],[(0,[z0,z1,z8,z3,z1227,z6]),(1,[z1,z8,z811,z5,z6]),(0,[z140,z0,z230,z3,z5,z6]),(0,[z0,z1,z1090,z3,z5,z6])],[(0,[z0,z169,z1,z8,z3,z42]),(0,[z1,z472,z3,z5,z6,z68]),(0,[z0,z1,z8,z684,z5,z37])],[(0,[z0,z1,z8,z1228,z3,z5]),(0,[z0,z1,z214,z3,z5,z487]),(0,[z0,z1,z8,z3,z1229,z6]),(0,[z1230,z1,z8,z3,z5,z6]),(0,[z0,z1,z59,z6,z558,z54]),(0,[z0,z1,z8,z3,z732,z203])],[(0,[z0,z535,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1231,z5]),(0,[z637,z30,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1232,z6]),(0,[z0,z1,z8,z3,z424,z6]),(0,[z0,z245,z1,z8,z3,z42])],[(0,[z0,z1,z46,z3,z5,z354]),(0,[z0,z1233,z8,z3,z5,z6]),(0,[z0,z8,z1234,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z1235]),(0,[z0,z1,z8,z715,z3,z297]),(0,[z0,z1,z8,z3,z42,z266])],[(0,[z13,z535,z8,z3,z5,z6]),(0,[z0,z1,z410,z18,z3,z6]),(0,[z0,z1,z8,z3,z171,z6])],[(0,[z0,z16,z8,z489,z5,z6]),(0,[z22,z1,z8,z21,z5,z6]),(0,[z0,z1,z8,z3,z5,z1236]),(0,[z627,z1,z255,z3,z5,z6]),(0,[z0,z1,z255,z28,z3,z5]),(0,[z359,z1,z8,z3,z42,z6])],[(0,[z7,z0,z8,z28,z9,z5]),(0,[z0,z1,z8,z1237,z3,z6])],[(0,[z759,z1,z8,z28,z3,z5])],[(0,[z0,z1,z8,z3,z5,z1238]),(0,[z0,z1,z1239,z3,z5,z6]),(0,[z26,z0,z8,z3,z721,z6]),(0,[z0,z11,z8,z28,z3,z5])],[(0,[z0,z1,z24,z3,z5,z6]),(0,[z0,z17,z538,z3,z5,z6]),(0,[z251,z0,z2,z3,z5,z6]),(0,[z1240,z1,z8,z3,z5,z6]),(0,[z359,z1,z8,z3,z5,z389])],[(0,[z0,z1,z8,z1241,z3,z5]),(0,[z0,z1,z370,z8,z3,z42]),(0,[z0,z1,z1242,z3,z5,z6]),(0,[z1243,z1,z8,z3,z5,z6])]],
   [[(0,[z75,z1,z8,z3,z23,z487]),(0,[z0,z1,z1244,z3,z5,z6]),(0,[z0,z1,z49,z3,z42,z54])],[(0,[z0,z8,z3,z42,z5,z517])],[(0,[z0,z224,z8,z28,z3,z5]),(0,[z0,z1,z49,z3,z297,z6]),(0,[z1,z8,z59,z6,z249,z54]),(0,[z0,z1,z8,z1008,z42,z5])],[(0,[z1245,z1,z8,z3,z5,z6]),(0,[z34,z35,z1,z3,z5,z36])],[(0,[z554,z1,z107,z3,z5,z6]),(0,[z407,z1,z107,z3,z5,z6]),(0,[z0,z1,z57,z3,z5,z6]),(0,[z0,z1,z8,z3,z166,z5]),(0,[z131,z1,z8,z3,z5,z226])],[(0,[z0,z1,z8,z618,z3,z42]),(0,[z1246,z1,z8,z3,z5,z6]),(0,[z0,z1,z1247,z3,z5,z6]),(0,[z0,z1,z1248,z3,z5,z6]),(0,[z0,z1,z8,z112,z287,z50])],[(0,[z207,z0,z1,z8,z3,z42]),(0,[z74,z1,z8,z3,z276,z6]),(0,[z1249,z1,z8,z3,z5,z6])],[(0,[z74,z0,z1,z8,z3,z77]),(0,[z26,z0,z144,z8,z3,z42]),(0,[z0,z1,z8,z1250,z3,z5]),(0,[z0,z1,z49,z3,z5,z6])],[(0,[z12,z1,z45,z28,z3,z5]),(0,[z414,z0,z2,z3,z5,z6]),(0,[z26,z201,z8,z3,z5,z6]),(0,[z552,z1,z8,z3,z5,z389]),(0,[z34,z0,z1,z3,z171,z36])],[(0,[z0,z1,z339,z8,z3,z42])],[(0,[z0,z1,z472,z3,z5,z6]),(0,[z627,z1,z8,z3,z300,z6]),(0,[z0,z1,z58,z268,z5,z6]),(0,[z0,z1251,z8,z3,z5,z6])],[(0,[z0,z1,z84,z3,z42,z5]),(0,[z0,z1,z8,z1252,z3,z6]),(0,[z0,z1,z214,z18,z3,z6])],[(0,[z0,z1,z8,z3,z424,z128]),(0,[z0,z1,z8,z3,z5,z1253]),(0,[z313,z0,z8,z3,z5,z82])],[(0,[z0,z1,z8,z476,z128,z5])],[(0,[z0,z1,z8,z28,z3,z5]),(0,[z627,z1,z8,z3,z5,z6]),(0,[z0,z1254,z8,z3,z5,z6]),(0,[z0,z1,z260,z3,z5,z376]),(0,[z0,z1,z8,z893,z3,z89]),(0,[z552,z1,z17,z3,z5,z6]),(0,[z106,z1,z3,z5,z6,z558])],[(0,[z201,z1,z8,z3,z5,z6]),(0,[z74,z1,z8,z121,z3,z42]),(0,[z1255,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1256]),(0,[z63,z0,z1,z799,z5,z6])]],
   [[(0,[z29,z1,z137,z3,z5,z6]),(0,[z641,z0,z8,z3,z5,z82]),(0,[z0,z1257,z8,z3,z5,z6])],[(0,[z70,z1,z8,z28,z121,z5]),(0,[z0,z1,z410,z8,z3,z42])],[(0,[z0,z1,z8,z3,z42,z15]),(0,[z540,z1,z45,z3,z5,z6]),(0,[z0,z1,z1258,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1259])],[(0,[z0,z330,z8,z3,z367,z6]),(0,[z0,z8,z1260,z3,z5,z6]),(0,[z0,z1,z8,z39,z821,z5]),(0,[z0,z1125,z8,z3,z5,z6])],[(0,[z0,z1261,z8,z3,z5,z6]),(0,[z0,z1,z17,z3,z15,z6]),(0,[z0,z1,z8,z3,z5,z1262]),(0,[z0,z1,z8,z337,z128,z5]),(0,[z0,z1,z8,z3,z42,z604])],[(0,[z0,z1,z8,z3,z1263,z6]),(0,[z0,z1,z8,z976,z5,z6])],[(0,[z503,z31,z8,z3,z5,z6]),(0,[z0,z1,z137,z3,z42,z5]),(0,[z187,z86,z8,z3,z5,z6]),(0,[z0,z1,z8,z59,z6,z771])],[(1,[z0,z8,z3,z721,z6]),(0,[z0,z1,z268,z5,z6,z170])],[(0,[z0,z1,z8,z3,z1264,z6]),(0,[z0,z76,z8,z3,z42,z5]),(0,[z0,z8,z830,z3,z5,z6])],[(0,[z0,z503,z8,z3,z42,z5]),(0,[z1,z8,z3,z5,z773,z6]),(0,[z0,z146,z8,z3,z42,z5])],[(0,[z12,z30,z86,z3,z5,z6]),(0,[z157,z144,z86,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1265]),(0,[z277,z1,z8,z28,z3,z5])],[(0,[z30,z1,z137,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1266]),(0,[z627,z1,z8,z3,z5,z343]),(1,[z0,z8,z795,z5,z6]),(0,[z26,z0,z8,z191,z3,z42]),(0,[z309,z1,z8,z28,z3,z5]),(0,[z0,z1,z8,z28,z3,z119]),(0,[z131,z1,z58,z3,z5,z6])],[(0,[z1267,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1268])],[(0,[z131,z1,z8,z3,z297,z6])],[(0,[z0,z1,z175,z3,z42,z5]),(0,[z0,z1,z158,z28,z3,z5]),(1,[z416,z0,z8,z3,z42]),(0,[z1269,z1,z8,z3,z5,z6])],[(0,[z1,z260,z3,z21,z5,z6]),(0,[z201,z1,z158,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z203])]],
   [[(0,[z479,z1,z8,z21,z5,z6]),(0,[z100,z1,z472,z3,z5,z68]),(0,[z0,z1,z410,z3,z42,z5]),(0,[z1270,z1,z8,z3,z5,z6])],[(0,[z535,z45,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z376])],[(0,[z1,z1271,z8,z3,z5,z6]),(0,[z131,z1,z8,z3,z5,z6]),(0,[z0,z1,z1272,z3,z5,z6])],[(0,[z31,z8,z3,z418,z5,z6]),(0,[z0,z1,z8,z3,z5,z1273]),(0,[z0,z1,z8,z3,z1274,z6]),(0,[z0,z16,z8,z191,z5,z6]),(0,[z7,z0,z255,z9,z5,z6])],[(0,[z74,z76,z8,z3,z5,z6]),(0,[z1275,z1,z8,z3,z5,z6])],[(0,[z0,z8,z3,z5,z6,z1276])],[(0,[z140,z187,z8,z3,z5,z6]),(1,[z0,z830,z3,z5,z6]),(0,[z0,z1,z8,z940,z3,z33]),(0,[z0,z1,z158,z3,z5,z179]),(0,[z0,z8,z3,z5,z6,z1277]),(0,[z0,z1,z8,z368,z5,z37]),(0,[z0,z1,z8,z222,z821,z5]),(0,[z0,z1278,z8,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1279,z6]),(0,[z0,z1280,z8,z3,z5,z6]),(0,[z0,z373,z8,z28,z3,z5]),(0,[z0,z1,z8,z3,z42,z200])],[(0,[z0,z8,z538,z3,z5,z6]),(0,[z0,z1,z8,z3,z1281,z6]),(0,[z0,z1,z8,z3,z991,z367]),(0,[z0,z1282,z8,z3,z5,z6]),(0,[z0,z1,z8,z28,z3,z537]),(0,[z0,z1,z8,z1283,z3,z5])],[(0,[z246,z31,z8,z3,z5,z6]),(0,[z430,z1,z45,z3,z5,z6]),(0,[z0,z1,z8,z3,z1284,z6]),(0,[z35,z1,z8,z28,z3,z5]),(0,[z106,z1,z49,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1285,z6]),(0,[z359,z1,z8,z3,z5,z332]),(0,[z0,z1,z53,z3,z5,z558])],[(0,[z0,z1286,z8,z3,z5,z6]),(0,[z0,z1,z8,z1287,z3,z5])],[(0,[z74,z1,z8,z3,z42,z80]),(0,[z0,z88,z8,z3,z5,z127]),(0,[z0,z1,z8,z3,z128,z171])],[(0,[z0,z1,z8,z3,z5,z1288])],[(0,[z70,z1,z260,z3,z5,z6]),(0,[z0,z1,z8,z691,z3,z42]),(0,[z1289,z1,z8,z3,z5,z6]),(1,[z0,z1,z799,z5,z6])],[(0,[z0,z1,z262,z8,z3,z171]),(0,[z1290,z0,z8,z3,z5,z6])]],
   [[(0,[z1,z137,z3,z5,z6,z68]),(0,[z106,z1,z8,z28,z3,z5])],[(0,[z0,z1,z1291,z3,z5,z6]),(0,[z583,z0,z1,z3,z5,z36]),(0,[z0,z1,z260,z3,z5,z354]),(0,[z1,z8,z3,z5,z44,z840]),(0,[z0,z1,z8,z1292,z3,z6]),(0,[z0,z1,z410,z3,z42,z6]),(0,[z568,z0,z1,z8,z3,z42]),(0,[z0,z1,z829,z28,z3,z5])],[(0,[z0,z219,z8,z28,z3,z5]),(0,[z0,z1,z143,z8,z3,z42]),(0,[z0,z1,z8,z59,z322,z54])],[(0,[z0,z1,z1293,z3,z5,z6]),(0,[z26,z0,z30,z8,z3,z42]),(0,[z0,z1,z8,z18,z3,z732])],[(0,[z404,z1,z8,z28,z3,z5])],[(0,[z0,z1,z8,z3,z1294,z6]),(0,[z0,z76,z214,z3,z5,z6])],[(0,[z12,z1,z220,z3,z5,z6]),(0,[z1295,z1,z8,z3,z5,z6])],[(0,[z157,z30,z8,z3,z5,z6]),(0,[z7,z0,z8,z9,z5,z6]),(0,[z0,z1,z8,z3,z464,z42]),(0,[z0,z1,z3,z5,z322,z558])],[(0,[z29,z796,z8,z3,z5,z6]),(0,[z110,z1,z8,z3,z5,z6]),(0,[z403,z1,z107,z3,z5,z6])],[(0,[z0,z1,z8,z3,z1296,z6]),(0,[z0,z1297,z8,z3,z5,z6]),(0,[z0,z1298,z8,z3,z5,z6]),(0,[z1299,z1,z8,z3,z5,z6])],[(0,[z67,z0,z380,z3,z5,z6]),(0,[z74,z75,z1,z8,z3,z42]),(0,[z0,z1,z8,z47,z3,z5])],[(0,[z22,z1,z8,z21,z367,z6]),(0,[z0,z1300,z8,z3,z5,z6])],[(0,[z0,z1,z1301,z3,z5,z6]),(0,[z1302,z0,z8,z3,z5,z6]),(0,[z0,z1,z1303,z3,z5,z6]),(0,[z0,z1,z8,z1081,z42,z5])],[(0,[z0,z1,z1084,z3,z42,z5])],[(0,[z0,z1,z1304,z3,z5,z6]),(0,[z0,z1,z260,z28,z3,z5]),(0,[z1305,z1,z8,z3,z5,z6]),(0,[z0,z1,z1306,z3,z5,z6]),(0,[z0,z1,z1307,z3,z5,z6])],[(0,[z157,z1,z8,z3,z5,z6]),(0,[z70,z1,z8,z121,z42,z5]),(0,[z7,z0,z8,z683,z5,z6])]],
   [[(0,[z29,z31,z8,z3,z5,z6]),(0,[z75,z76,z8,z3,z23,z6]),(0,[z1,z8,z3,z5,z6,z1308])],[(0,[z0,z1,z8,z1309,z3,z5]),(0,[z1,z3,z5,z6,z558,z249])],[(0,[z12,z1,z8,z3,z424,z6]),(0,[z0,z197,z8,z3,z721,z6]),(0,[z63,z0,z1,z108,z89,z6]),(0,[z0,z1,z8,z59,z53,z54])],[(0,[z30,z796,z8,z3,z5,z6]),(0,[z528,z30,z8,z3,z5,z6]),(0,[z1310,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z1094,z3,z5]),(0,[z0,z1311,z8,z3,z5,z6]),(0,[z1,z8,z3,z42,z5,z249])],[(0,[z0,z1,z8,z3,z5,z354]),(0,[z201,z8,z3,z32,z5,z6]),(0,[z209,z88,z8,z3,z5,z6])],[(0,[z0,z1312,z8,z3,z5,z6]),(0,[z1313,z1,z8,z3,z5,z6]),(0,[z8,z3,z5,z6,z517,z249]),(0,[z0,z1,z1314,z3,z5,z6])],[(0,[z0,z1,z8,z3,z5,z1315]),(0,[z627,z1,z8,z3,z5,z382]),(0,[z0,z1,z8,z18,z3,z389]),(0,[z0,z1,z8,z3,z42,z624]),(0,[z1010,z1,z8,z3,z42,z5]),(0,[z55,z1,z8,z184,z3,z5]),(0,[z0,z1,z851,z28,z3,z5])],[(0,[z479,z0,z8,z9,z5,z6])],[(0,[z0,z1316,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z1317,z6]),(0,[z66,z1,z8,z3,z42,z5]),(0,[z0,z1,z8,z1318,z3,z5])],[(0,[z0,z1,z8,z1319,z3,z6]),(0,[z66,z1,z137,z3,z5,z6]),(0,[z0,z1,z1320,z3,z5,z6]),(0,[z0,z177,z8,z28,z3,z5]),(0,[z0,z957,z8,z3,z5,z6])],[(0,[z0,z116,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z1321]),(0,[z144,z86,z612,z3,z5,z6]),(0,[z0,z1,z8,z101,z3,z42]),(0,[z0,z1,z3,z717,z5,z6])],[(0,[z0,z1322,z8,z3,z5,z6])],[(0,[z0,z1,z8,z469,z6,z54]),(0,[z0,z1323,z8,z3,z5,z6]),(0,[z106,z1,z8,z59,z6,z54]),(0,[z0,z1,z8,z53,z3,z40])],[(0,[z207,z31,z8,z3,z5,z6]),(0,[z417,z0,z1,z8,z3,z42])],[(0,[z687,z1,z8,z3,z5,z68]),(0,[z0,z1324,z8,z3,z5,z6]),(0,[z74,z0,z1,z8,z3,z42]),(0,[z1325,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z42,z546])],[(0,[z0,z1,z380,z28,z3,z5]),(0,[z187,z8,z3,z32,z5,z6]),(0,[z0,z1,z93,z3,z42,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 498).take 497) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 995).take 352) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1347)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [498, 497, 352] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 119).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 119).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 241).take 120).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 361).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 478).take 34).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [119, 122, 120, 117, 34] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

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

end PEqualNP.Outside.L_meta_38516

theorem PEqualNP.Outside.L_meta_38516 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 3941264000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 3941264000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38516.solve