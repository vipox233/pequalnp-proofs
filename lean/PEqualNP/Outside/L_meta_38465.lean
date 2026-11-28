import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38465

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
  Nat.testBit (4008372936 * 2 ^ 32 + 3940608512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x40002b1386170e15#64 ++ 0xef427f3f8e7f1e3f#64 : BitVec 128),
   (0x011c9848bab362cc#64 ++ 0x3fbd98c9ffb3e3cc#64 : BitVec 128),
   (0x02c160b1d141b770#64 ++ 0x37c1e0f1f1c3fff0#64 : BitVec 128),
   (0x88ee00ec01e801aa#64 ++ 0xfbfe00fe01fc03ff#64 : BitVec 128),
   (0x04f7dd0001fed800#64 ++ 0x3dffff0001fffc00#64 : BitVec 128),
   (0x10fbf6ff6c000000#64 ++ 0x3efffffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 5]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x011c9848bab362cc 0x3fbd98c9ffb3e3cc

def z1 : W := mkw 0x02c160b1d141b770 0x37c1e0f1f1c3fff0

def z2 : W := mkw 0x04f7dd0001fed800 0x3dffff0001fffc00

def z3 : W := mkw 0x10fbf6ff6c000000 0x3efffffffe000000

def z4 : W := mkw 0x40002b1386170e15 0xef427f3f8e7f1e3f

def z5 : W := mkw 0x88ee00ec01e801aa 0xfbfe00fe01fc03ff

def z6 : W := mkw 0x89fe98ecbbfb63ee 0xffff98ffffffe3ff

def z7 : W := mkw 0x00c1400001409000 0x35c1e00001c3fc00

def z8 : W := mkw 0x00f3d40000000000 0x3cffff0000000000

def z9 : W := mkw 0x04d1dd000156d800 0x35c1ff0001c3fc00

def z10 : W := mkw 0x02c140a0d141b770 0x118180c071c3fff0

def z11 : W := mkw 0x0000221304000000 0x04007f018e000000

def z12 : W := mkw 0x020000009141b770 0x378180c1f1c3fff0

def z13 : W := mkw 0x10e366b744000000 0x0042673600000000

def z14 : W := mkw 0x0611fd11d017fe50 0x0401ff01f003fc00

def z15 : W := mkw 0x8cffdd4c01fed88a 0xfdffff0e01fffc0f

def z16 : W := mkw 0x04f7d40001e8d000 0x10bd80000180e000

def z17 : W := mkw 0x4000221386010615 0xc200003f8e00023f

def z18 : W := mkw 0x000c084882b3028c 0x3fbc18c98fb303cc

def z19 : W := mkw 0x42c16bb3d757bf75 0xffc3ffffffffffff

def z20 : W := mkw 0x0411dd000016d800 0x0401ff000003fc00

def z21 : W := mkw 0x40002b1386170e15 0x04007f018e031c00

def z22 : W := mkw 0x0000000090012240 0x378180c1f183e3c0

def z23 : W := mkw 0x40002b1306160c15 0xc8427f3e0e7c1c3f

def z24 : W := mkw 0x0000281182130614 0x2f4078398e731e3c

def z25 : W := mkw 0x103ab6ff6c000000 0x0a3e1ffffe000000

def z26 : W := mkw 0x00f3dd0000160800 0x3dffff00007f1c00

def z27 : W := mkw 0x0000201190012650 0x37c1e0f1f1c3fff0

def z28 : W := mkw 0x8808004c0000008a 0xc000000e0000000f

def z29 : W := mkw 0x053e9d482abe488c 0x083e1f080e3c000c

def z30 : W := mkw 0x98fbf6ff6d480122 0xfefffffffe4c0033

def z31 : W := mkw 0x100822ff6c000000 0x020000fffe000000

def z32 : W := mkw 0x8a0820fdd00127fa 0xc20000fff00003ff

def z33 : W := mkw 0x40002b1386170e15 0xc300003f8e7f1e3f

def z34 : W := mkw 0x14ffffff6dfed800 0x3ffffffffffffc00

def z35 : W := mkw 0x0000000000000000 0x29420000007c0000

def z36 : W := mkw 0x4000090082170e15 0x0000000000031c00

def z37 : W := mkw 0x0000080002120004 0x080018080e30000c

def z38 : W := mkw 0x89fe98ec2bfa41ae 0xfbfe18fe0ffc03ff

def z39 : W := mkw 0x88ee00ec01e801aa 0xd0fe00f601cc01f3

def z40 : W := mkw 0x11fff6ff7ca060c8 0x3effffffff80e1c0

def z41 : W := mkw 0x0000090000160800 0x04007f0000031c00

def z42 : W := mkw 0x00c000a001400120 0x33c000f001c003f0

def z43 : W := mkw 0x882e004c00a8008a 0xc83e000e003c000f

def z44 : W := mkw 0x43ddfbfbfff7fffd 0xffffffffffffffff

def z45 : W := mkw 0x01109800ba136244 0x04019801fe03e000

def z46 : W := mkw 0x411cbb5bbeb76edd 0xffffffffffffffff

def z47 : W := mkw 0x88ee00ec01e801aa 0x3bbc00c801b003cc

def z48 : W := mkw 0x000c004800a00088 0x3bbc00c801b003cc

def z49 : W := mkw 0x011c9848bab362cc 0x0a3c18c9fe3003cc

def z50 : W := mkw 0x06d1fdb1d157ff70 0x37c1fff1f1c3fff0

def z51 : W := mkw 0xc8ee2bff87ff0fbf 0xfffe7fff8fff1fff

def z52 : W := mkw 0x00002a1386130204 0x2f427f3f8e33020c

def z53 : W := mkw 0x1111fe13fe136244 0x0401ff01fe03e000

def z54 : W := mkw 0x00c0000001400000 0x31c0000001c00000

def z55 : W := mkw 0x02c140a05140b160 0x108180c07180e1c0

def z56 : W := mkw 0x0000000000000000 0xeb42003e007c023f

def z57 : W := mkw 0x04f7dd0001fed800 0xffffff3e01fffe3f

def z58 : W := mkw 0x10fbf6ff6c000000 0x087e7f3e0e000000

def z59 : W := mkw 0x10f3f6b76c000000 0x0443ff37fe000000

def z60 : W := mkw 0x8bfff8fdfbfbf7fe 0xfffff8ffffffffff

def z61 : W := mkw 0x04e34d00015e9800 0x2d427f00007f1c00

def z62 : W := mkw 0x42002bb3d6172f75 0xef427ffffe7f1fff

def z63 : W := mkw 0x10fbffff6c160800 0x3ffffffffe7f1c00

def z64 : W := mkw 0x001c904828a00088 0x3fbd98c9ffb003cc

def z65 : W := mkw 0x02c160b1d141b770 0x0441e031f043fc30

def z66 : W := mkw 0x4000221386010615 0x000000018e000000

def z67 : W := mkw 0x98ef66ff45e801aa 0xfbfe67fe01fc03ff

def z68 : W := mkw 0x04c5490001fed800 0x35c1e00001fffc00

def z69 : W := mkw 0x04f7dd0001fed800 0x18bf9f0001bce000

def z70 : W := mkw 0x0104080092b362cc 0x0100000001b3e3cc

def z71 : W := mkw 0x0404090001fed800 0x0100000001fffc00

def z72 : W := mkw 0x4108225bbe0126dd 0xc20000fffe0003ff

def z73 : W := mkw 0x16fffffffdffff70 0x3ffffffffffffff0

def z74 : W := mkw 0x9cffffff6dfed9aa 0xffffffffffffffff

def z75 : W := mkw 0x10fbf6fffc012240 0x3fffffffff83e3c0

def z76 : W := mkw 0x000c004800a00088 0x10bc00c0018001c0

def z77 : W := mkw 0x10fbd4ec68000000 0x10bd80c070000000

def z78 : W := mkw 0x4000090082170e15 0xc1000000007f1e3f

def z79 : W := mkw 0x02c160b141409530 0x0040603000401c30

def z80 : W := mkw 0x03ddf8f9fbf3f7fc 0x3ffdf8f9fff3fffc

def z81 : W := mkw 0x88e200a401480122 0xeb42003e007c023f

def z82 : W := mkw 0x020140005000b040 0x000180007000e000

def z83 : W := mkw 0x0000201100000410 0x0040603000401c30

def z84 : W := mkw 0x411c9b4a2eb6488d 0xc83e1f0e0e3c000f

def z85 : W := mkw 0x12fbd4ec7940b160 0x10bd80c07180e1c0

def z86 : W := mkw 0x4000030204040801 0xc0020706000c0003

def z87 : W := mkw 0x4104090092b76edd 0xc100000001ffffff

def z88 : W := mkw 0x02c160b15140b570 0x10c1e0f071c0fdf0

def z89 : W := mkw 0x12fbf6fffd41b770 0x3fffffffffc3fff0

def z90 : W := mkw 0x04ffdd4801fed888 0x3fffffc801ffffcc

def z91 : W := mkw 0x503abf5fae170e15 0xef7e7f3f8e7f1e3f

def z92 : W := mkw 0x8aef60fdd1e9b7fa 0xffffe0fff1ffffff

def z93 : W := mkw 0x020020b1d141b770 0x030000f1f1c3fff0

def z94 : W := mkw 0x01080048ba0122cc 0x020000c9fe0003cc

def z95 : W := mkw 0x04e34500014c9800 0x00426700004c1c00

def z96 : W := mkw 0x0000090000160800 0x2d427f00007f1c00

def z97 : W := mkw 0x50fbf7ff6c040c11 0xfefffffffe4c1c33

def z98 : W := mkw 0x88e200a401480122 0xc0420036004c0033

def z99 : W := mkw 0x00c160b140000000 0x36c1e0f1f0000000

def z100 : W := mkw 0x88ee00ec01e801aa 0xd8be00ce01bc01cf

def z101 : W := mkw 0x04f7d40001e8d000 0x3cffff000180e000

def z102 : W := mkw 0x00ea00ec00000000 0x3afe00fe00000000

def z103 : W := mkw 0x98fff6ff6de801aa 0xfffffffffffc03ff

def z104 : W := mkw 0x01109800ba136244 0x2f019809fe33e20c

def z105 : W := mkw 0x011c9948bab76acc 0x3fffffc9ffffffcc

def z106 : W := mkw 0x02c000a09141b770 0x33c000f001c3fff0

def z107 : W := mkw 0x03c960f9fb41b7fc 0x37c1e0f9ffc3fffc

def z108 : W := mkw 0x880800ec000001aa 0x000000c0000001c0

def z109 : W := mkw 0x0000221304000000 0x0042673600000000

def z110 : W := mkw 0x11ffdcecfab362cc 0x3fbd98c9ffb3e3cc

def z111 : W := mkw 0x42c16bb3d757bf75 0x37c1fff1ffc3fff0

def z112 : W := mkw 0x02d5f8b1d1f3f770 0x3ffdf8f1f1f3fff0

def z113 : W := mkw 0x40002b1306160805 0xee427f3f8e3c000f

def z114 : W := mkw 0x10fbf6ff6d400120 0x3fffffffffc003f0

def z115 : W := mkw 0x4000221386010615 0xee427f3f8e00023f

def z116 : W := mkw 0x44e36713054c9c11 0xc0426736004c1c33

def z117 : W := mkw 0x02c160b1d141b770 0x1481e0c1f183fdc0

def z118 : W := mkw 0x011c98482ab2408c 0x083c18080e30000c

def z119 : W := mkw 0x02016011d001b650 0x0401e001f003fc00

def z120 : W := mkw 0x12fbf6ff6d409530 0x3efffffffe401c30

def z121 : W := mkw 0x0100080092136244 0x000000000003e000

def z122 : W := mkw 0x06e365b1414c9d30 0x00426730004c1c30

def z123 : W := mkw 0x411c9948bab76edd 0xffbd98c9ffffffff

def z124 : W := mkw 0x04ffddec01fed800 0x3ffffffe01fffc00

def z125 : W := mkw 0x88e200a401480122 0x0000000000000000

def z126 : W := mkw 0x0415dd0000b6d800 0x3dbdff0001b3fc00

def z127 : W := mkw 0x00f3d40001409000 0x3dffff0001c3fc00

def z128 : W := mkw 0x4000090082170e15 0xed427f00007f1e3f

def z129 : W := mkw 0x0000000000000000 0x358180000183e000

def z130 : W := mkw 0x02c160b141409530 0x33c060f001c01ff0

def z131 : W := mkw 0x06f7fd11d1fffe50 0x3dffff01f1fffc00

def z132 : W := mkw 0x0018b25b2c000000 0x3efffffffe000000

def z133 : W := mkw 0x0004000001e80000 0x0100000001fc0000

def z134 : W := mkw 0x02c140a05140b160 0x35c1e0c071c3fdc0

def z135 : W := mkw 0x8cffddec01fed9aa 0xfffffffe01ffffff

def z136 : W := mkw 0x88ef40ec01e891aa 0xffffe0fe01ffffff

def z137 : W := mkw 0x88e200a401480122 0xf3c200f601cc03f3

def z138 : W := mkw 0x020020b1d0012770 0x020000f1f00003f0

def z139 : W := mkw 0x04369d0000be4800 0x083e1f00003c0000

def z140 : W := mkw 0x8cfe9dec01fe49aa 0xfbfe1ffe01fc03ff

def z141 : W := mkw 0x011c9048b8a162c8 0x37bd80c1f183e3c0

def z142 : W := mkw 0x00fbd44828000000 0x3effffc9fe000000

def z143 : W := mkw 0x0401450000049800 0x0000670000001c00

def z144 : W := mkw 0xc8e22bb7875f0f37 0xef427f3f8e7f1e3f

def z145 : W := mkw 0x011cb859bab366dc 0x3ffdf8f9fff3fffc

def z146 : W := mkw 0x011cba5bbeb362cc 0x3fffffffffb3e3cc

def z147 : W := mkw 0x02002011d0012650 0x00000001f0000000

def z148 : W := mkw 0x54ffffffefffde15 0xfffffffffffffe3f

def z149 : W := mkw 0x0000090082170a04 0x2f427f098e7f1e0c

def z150 : W := mkw 0x0018904828000000 0x3ebd98c9fe000000

def z151 : W := mkw 0x0000221384010610 0x2f427f3f8e431e30

def z152 : W := mkw 0x04f7fd1181ffde10 0x3fffff3181fffe30

def z153 : W := mkw 0x04f7dd0001fed800 0x14bdff000183fc00

def z154 : W := mkw 0x04e74d0001fed800 0x0142670001fffc00

def z155 : W := mkw 0x40002b1386170e15 0xcc027f0f8e3f1c0f

def z156 : W := mkw 0x0000221304000000 0x2e427f3f8e000000

def z157 : W := mkw 0x0014980000b24000 0x3dbd980001b3e000

def z158 : W := mkw 0x05ffdd48bbfffacc 0x3fffffc9ffffffcc

def z159 : W := mkw 0x04e3440001489000 0x0000000000000000

def z160 : W := mkw 0x0110900038006040 0x000180007000e000

def z161 : W := mkw 0x42c162b3d741b775 0xf7c1e0ffffc3ffff

def z162 : W := mkw 0x88ee00ec01e801aa 0xd1bc00c001fc03ff

def z163 : W := mkw 0x0000020204000000 0x08021f0e0e000000

def z164 : W := mkw 0x011c904838a060c8 0x10bd80c07180e1c0

def z165 : W := mkw 0x14e367b7454c9800 0x00426736004c1c00

def z166 : W := mkw 0x00e200a400000000 0x0042003600000000

def z167 : W := mkw 0x42c163b3d545bf71 0xf7c3e7f7f1cffff3

def z168 : W := mkw 0x40c16bb3c6170e15 0xffc3fffffe7f1e3f

def z169 : W := mkw 0x10f3f6b744000000 0x3cffff3600000000

def z170 : W := mkw 0x4000010000040c11 0xc0000000004c1c33

def z171 : W := mkw 0x04f7dd0000be4800 0x3cffff00003c0000

def z172 : W := mkw 0x010c0848bab362cc 0x030000c9ffb3e3cc

def z173 : W := mkw 0x020020b1d0012770 0x274060f1f0431ff0

def z174 : W := mkw 0x01fe9848bbfb62cc 0x3fff98c9ffffe3cc

def z175 : W := mkw 0x88ee00ec01e801aa 0x3afe00fe018001c0

def z176 : W := mkw 0x0104080092b362cc 0x378180c1f1b3e3cc

def z177 : W := mkw 0x99fffefffffb63ee 0xffffffffffffe3ff

def z178 : W := mkw 0x8a04000091e9b7fa 0xc100000001ffffff

def z179 : W := mkw 0x01109800ba136244 0x378198c1ff83e3c0

def z180 : W := mkw 0x00e6090001fe0800 0x3dfe7f0001ff1c00

def z181 : W := mkw 0x4000231304040c11 0xeb42673e007c1e3f

def z182 : W := mkw 0x02f3f4b1d141b770 0x3ffffff1f1c3fff0

def z183 : W := mkw 0x88ee00ec01e801aa 0x10bc00c0018001c0

def z184 : W := mkw 0x46f7ffb3d7ffff75 0xffffffffffffffff

def z185 : W := mkw 0x1211f613fc01b650 0x0401ff01fe03fc00

def z186 : W := mkw 0x1011f6136c000000 0x0401ff01fe000000

def z187 : W := mkw 0x42c16bb3c7579f35 0xef427f3f8e7f1e3f

def z188 : W := mkw 0x51fffffffeb76edd 0xffffffffffffffff

def z189 : W := mkw 0x10e366b744000000 0x2e427f3f8e000000

def z190 : W := mkw 0x031cb8f9fab367fc 0x3fbd98f9ffb3e3fc

def z191 : W := mkw 0x40c02bb387570f35 0xffc27fff8fff1fff

def z192 : W := mkw 0x8ae360b5d149b772 0xf7c3e0f7f1cffff3

def z193 : W := mkw 0x011c9848bab362cc 0x0c3d9809fe33e00c

def z194 : W := mkw 0x00ea00ec00000000 0x10bc00c000000000

def z195 : W := mkw 0x0004000000a00088 0x0100000001b003cc

def z196 : W := mkw 0x103a964e2c000000 0x083e1f0e0e000000

def z197 : W := mkw 0x8804000000a8008a 0xc0000000003c000f

def z198 : W := mkw 0x88e6000001e801aa 0xf9fe000001fc03ff

def z199 : W := mkw 0x8cffddec01fed9aa 0x3dffffc001fffdc0

def z200 : W := mkw 0x020020b1d0012770 0x378180f1f183e3f0

def z201 : W := mkw 0x880c00ec01e801aa 0xc30000fe01fc03ff

def z202 : W := mkw 0x040009000016d800 0x000000000003fc00

def z203 : W := mkw 0x880000a400000122 0xc000003600000033

def z204 : W := mkw 0x88fe90ec29e801aa 0xffff98fffffc03ff

def z205 : W := mkw 0x0000000001409000 0x0100000001c3fc00

def z206 : W := mkw 0x020000009141b770 0x0100000001c3fff0

def z207 : W := mkw 0x50fbffffee170e15 0xfffffffffe7f1e3f

def z208 : W := mkw 0x020020b140000530 0x0000003000000030

def z209 : W := mkw 0x02c168b1d353b774 0x3fc1f8f9fff3fffc

def z210 : W := mkw 0x00c160b1c0010610 0x37c1e0f1f0431e30

def z211 : W := mkw 0x0415dd0001fed800 0x0501ff0001fffc00

def z212 : W := mkw 0x89ee00ecbbe923ee 0xfbfe00fffffc03ff

def z213 : W := mkw 0x11fbfefffe136244 0x3efffffffe03e000

def z214 : W := mkw 0x98fbf6ff6c0001aa 0xfefffffffe0003ff

def z215 : W := mkw 0x04369d0000be4800 0x3dbf9f0001bfe000

def z216 : W := mkw 0x11fbf6fffe0122cc 0x3efffffffe0003cc

def z217 : W := mkw 0x88ea00ec000001aa 0xfafe00fe000003ff

def z218 : W := mkw 0x011c904838a060c8 0x3ebd98c9ff80e1c0

def z219 : W := mkw 0x00e3440000000000 0x0042670000000000

def z220 : W := mkw 0x10c962ff6c000000 0x36c1e0fffe000000

def z221 : W := mkw 0x00c140a040000000 0x108180c070000000

def z222 : W := mkw 0x0000201180010610 0x2740603180431e30

def z223 : W := mkw 0x11fffefffeb362cc 0x3fffffffffb3e3cc

def z224 : W := mkw 0x05ffdc48bbfbf2cc 0x3fbd98c9ffb3e3cc

def z225 : W := mkw 0x02e760b1d1e9b770 0x3fffe0f1f1fffff0

def z226 : W := mkw 0x02d9f0f9f941b770 0x3ffdf8f9ffc3fff0

def z227 : W := mkw 0x06f7fdb1d1ffff70 0x3ffffff1f1fffff0

def z228 : W := mkw 0x88c800ec014001aa 0xf3c000fe01c003ff

def z229 : W := mkw 0x00c1400001409000 0x0040600000401c00

def z230 : W := mkw 0x0004000000a00000 0x39bc000001b00000

def z231 : W := mkw 0x04220500000c0800 0x00020700000c0000

def z232 : W := mkw 0x04f7fdb141fed800 0x3ffffff1f1fffc00

def z233 : W := mkw 0x14ffdf4e2dfed800 0x3dffff0e0ffffc00

def z234 : W := mkw 0x8cffd4ec01e8d1aa 0x10bd80c00180e1c0

def z235 : W := mkw 0x0404090001fed800 0x2d427f0001fffc00

def z236 : W := mkw 0x0000000090012240 0x010000000183e3c0

def z237 : W := mkw 0x13fffefffff3f7fc 0x3ffffffffff3fffc

def z238 : W := mkw 0x00189048b8012240 0x3fbd98c9ff83e3c0

def z239 : W := mkw 0x01080848ba1322cc 0x2f0018c9fe3303cc

def z240 : W := mkw 0x50082bffee170e15 0xef427ffffe7f1e3f

def z241 : W := mkw 0x00fa90ec28000000 0x3eff98fffe000000

def z242 : W := mkw 0x01fe98ecbab362cc 0x3fff98ffffb3e3cc

def z243 : W := mkw 0x00c160b140000000 0x0040603000000000

def z244 : W := mkw 0x8804000001e801aa 0xeb42003e01fc03ff

def z245 : W := mkw 0x14fbf7ff6d4c9800 0x3efffffffe4c1c00

def z246 : W := mkw 0x04f69d0001fe4800 0x39fe1f0001fc0000

def z247 : W := mkw 0x14ffd4ec69e8d000 0x10bd80c07180e000

def z248 : W := mkw 0x40002b1304160c11 0xed427f36007f1c33

def z249 : W := mkw 0x880800ec000001aa 0xc20000fe000003ff

def z250 : W := mkw 0x4110bb13be176e55 0x0401ff01fe03fc00

def z251 : W := mkw 0x06c569b1d1ffff70 0x37c1e0f1f1fffff0

def z252 : W := mkw 0x10fbf6ff6c000000 0x12bd80fffe000000

def z253 : W := mkw 0x00e2000001480000 0x00420000004c0000

def z254 : W := mkw 0x1019f65b6c000000 0x3ebdffc9fe000000

def z255 : W := mkw 0x40000b0206160805 0xed427f0e0e7f1c0f

def z256 : W := mkw 0x00e6000001e80000 0x39fe000001fc0000

def z257 : W := mkw 0x8ce345a4014c9922 0xc0426736004c1c33

def z258 : W := mkw 0x8804000001e801aa 0xc100000001fc03ff

def z259 : W := mkw 0x0000000000000000 0xc200003e0000023f

def z260 : W := mkw 0x983e964e2ca8008a 0xc83e1f0e0e3c000f

def z261 : W := mkw 0x04f7d40001e8d000 0x39ff800001fce000

def z262 : W := mkw 0x10fbd4ec68000000 0x3aff80fe70000000

def z263 : W := mkw 0x0411dd000016d800 0x2d43ff00007ffc00

def z264 : W := mkw 0x0000000080010200 0x2700000180030200

def z265 : W := mkw 0x04e7450001ec9800 0x39fe670001fc1c00

def z266 : W := mkw 0x011c9848bab362cc 0x14bd98c1ff83e1c0

def z267 : W := mkw 0x10e366b744000000 0x36c3e7f7f0000000

def z268 : W := mkw 0x1001661344000000 0x0000670000000000

def z269 : W := mkw 0x10eb66ff44000000 0x3afe67fe00000000

def z270 : W := mkw 0x88ee08ec83fb03ae 0xfffe18ff8fff03ff

def z271 : W := mkw 0x03d1f8b1fb53f774 0x37c1f8f1ffc3fff0

def z272 : W := mkw 0x10fbf6ff6d409000 0x3fffffffffc3fc00

def z273 : W := mkw 0x04f7dd0091fffa40 0x3fffffc1f1ffffc0

def z274 : W := mkw 0x06f7fdb141fedd30 0x3dffff3001fffc30

def z275 : W := mkw 0x110822fffe0122cc 0x020000fffe0003cc

def z276 : W := mkw 0x4000231304040c11 0xc0426736004c1c33

def z277 : W := mkw 0x04f7ff1305fed800 0x3fffff3f8ffffc00

def z278 : W := mkw 0x40000b0206160805 0xc8021f0e0e3c000f

def z279 : W := mkw 0x10fbf6ffec010610 0x3ffffffffe431e30

def z280 : W := mkw 0x12c962fffd41b770 0x37c1e0ffffc3fff0

def z281 : W := mkw 0x88ea00ec014801aa 0xc24200fe004c03ff

def z282 : W := mkw 0x10fbd64e2c000000 0x3cffff0e0e000000

def z283 : W := mkw 0x011c9848bab362cc 0x11bd80c071b3e3cc

def z284 : W := mkw 0x04f3dd00015ed800 0x0443ff00004ffc00

def z285 : W := mkw 0x0000000000000000 0x0000000000000000

def z286 : W := mkw 0x01080048380020c8 0x000000c0700001c0

def z287 : W := mkw 0x50fbffff6e160805 0xfefffffffe3c000f

def z288 : W := mkw 0x00fbd4ec00000000 0x3efffffe00000000

def z289 : W := mkw 0x41082b5bbe172edd 0xef427ffffe7f1fff

def z290 : W := mkw 0x0000221304000000 0x0200003f8e000000

def z291 : W := mkw 0x04f3dd000016d800 0x3cffff000003fc00

def z292 : W := mkw 0x02c160b1d141b770 0x0140603001c3fff0

def z293 : W := mkw 0x40002b1386170e15 0xc6007f3f8e031e3f

def z294 : W := mkw 0x00c140a001409120 0x37c1e0f001c3fff0

def z295 : W := mkw 0x05f7dd0093fffacc 0x3dffff0001ffffcc

def z296 : W := mkw 0x04f7dd0083ffda04 0x3fffff098ffffe0c

def z297 : W := mkw 0x020160b1d001b770 0x0601e0f1f003fff0

def z298 : W := mkw 0x00d5d80001f2d000 0x3dfdf80001f3fc00

def z299 : W := mkw 0x40002a1386130615 0xef00183f8e33023f

def z300 : W := mkw 0x000000a000000120 0x020000f0000003f0

def z301 : W := mkw 0x52fbffffff57bf75 0xffffffffffffffff

def z302 : W := mkw 0x04f7dd0001fed800 0x11bd800001fffc00

def z303 : W := mkw 0x8aee00ec91e9b7fa 0xfbfe00fe01ffffff

def z304 : W := mkw 0xc8ee22ff87e907bf 0xfbfe00ff8ffc03ff

def z305 : W := mkw 0x011c9848bab362cc 0xffff98ffffffe3ff

def z306 : W := mkw 0x0014980000b24000 0x083c180000300000

def z307 : W := mkw 0x02c160b1c1419730 0x2740603180431e30

def z308 : W := mkw 0x000c004890a122c8 0x3fbd80c9f1b3e3cc

def z309 : W := mkw 0x01ffdc48bab362cc 0x3fffffc9ffb3e3cc

def z310 : W := mkw 0x8cef45ec01ec99aa 0xfbfe67fe01fc1fff

def z311 : W := mkw 0x06f7dd0091ffff70 0x3dffff0001fffff0

def z312 : W := mkw 0x011c98482ab2408c 0x3bbc18c80fb003cc

def z313 : W := mkw 0x40ea2bff86170e15 0xfffe7fff8e7f1e3f

def z314 : W := mkw 0x10fbf6ff6c000000 0xfffffffffe7c023f

def z315 : W := mkw 0x0404000001e8d000 0x000000000180e000

def z316 : W := mkw 0x411cba5bbeb366dd 0xffbd98ffffb3e3ff

def z317 : W := mkw 0x10f3f6136c000000 0x3cffff01fe000000

def z318 : W := mkw 0x0000000000000000 0xc1000000007c023f

def z319 : W := mkw 0x00c1490001569800 0x3dc3ff0001fffc00

def z320 : W := mkw 0x10fa96ee2c000000 0x3afe1ffe0e000000

def z321 : W := mkw 0x02016011d001b650 0x2741e031f043fe30

def z322 : W := mkw 0x00d9f0f968000000 0x3efdf8f9fe000000

def z323 : W := mkw 0x04e6090001fed800 0x39fe000001fffc00

def z324 : W := mkw 0x0000090000160800 0x08021f00003c0000

def z325 : W := mkw 0x04f7d40001e8d000 0x35fde00001c3fc00

def z326 : W := mkw 0xc8ee09ec83ff0fbf 0xfbfe00fe01ff1fff

def z327 : W := mkw 0x40002b1386170e15 0xc5007f018e7f1e3f

def z328 : W := mkw 0x04109d0000164800 0x00001f0000000000

def z329 : W := mkw 0x00c140009141b240 0x37c1e0c1f1c3ffc0

def z330 : W := mkw 0x01000000ba012244 0x00000001fe000000

def z331 : W := mkw 0x0000080082130204 0xef42183f8e7f023f

def z332 : W := mkw 0x14ffffff6cbe4800 0x3efffffffe3c0000

def z333 : W := mkw 0x40002b1386170e15 0x2e427f3f8e031c00

def z334 : W := mkw 0x04369d0000be4800 0x2d7e7f00007f1c00

def z335 : W := mkw 0x14ffddec69fed800 0x3dffffc071fffc00

def z336 : W := mkw 0x89fe90ec39e861ea 0x10bd80c07180e1c0

def z337 : W := mkw 0x40002b1386170e15 0xca021f3f8e3c023f

def z338 : W := mkw 0x0411d4000000d000 0x000180000000e000

def z339 : W := mkw 0x02c16011d141b650 0x35c1e001f1c3fc00

def z340 : W := mkw 0x04ffdd4829fed800 0x3fffffc9fffffc00

def z341 : W := mkw 0x05ffdd4839fef8c8 0x3dffffc071fffdc0

def z342 : W := mkw 0x882e00ec00a801aa 0xca3e00fe003c03ff

def z343 : W := mkw 0x0200000090012770 0x00000000000003f0

def z344 : W := mkw 0x0000080092132244 0x3f8198c9ffb3e3cc

def z345 : W := mkw 0x88ee00ec01e801aa 0xd2bc00fe018003ff

def z346 : W := mkw 0x010c084892b362cc 0x3bbc00c801b3e3cc

def z347 : W := mkw 0x44f7ff1305fedc11 0xfdffff3601fffc33

def z348 : W := mkw 0x0000000001400120 0x0100000001c003f0

def z349 : W := mkw 0x0000000000000000 0xc802000e003c000f

def z350 : W := mkw 0x10fffeff6cb24000 0x3fffffffffb3e000

def z351 : W := mkw 0x00c000a001400120 0xfbc200fe01fc03ff

def z352 : W := mkw 0x01189048ba0122cc 0x3ebd98c9fe0003cc

def z353 : W := mkw 0x44f7ff1387ffde15 0xffffff3f8ffffe3f

def z354 : W := mkw 0x10fff6ff6ca00088 0x3fffffffffb003cc

def z355 : W := mkw 0x00c1400000000000 0x34c1e00000000000

def z356 : W := mkw 0x011c984838b260c8 0x3dbd98c071b3e1c0

def z357 : W := mkw 0xc8082bff86170fbf 0xef427fff8e7f1fff

def z358 : W := mkw 0x44f7ff1387ffde15 0x3dffff018ffffc00

def z359 : W := mkw 0x8aef40ec51e8b1ea 0x10bd80c07180e1c0

def z360 : W := mkw 0x0000090000160800 0x01000000007f1c00

def z361 : W := mkw 0x40002b1386170e15 0x2d427f018e7f1c00

def z362 : W := mkw 0x010800482a00008c 0x000000080e00000c

def z363 : W := mkw 0x00c000a001400120 0x0040003000400030

def z364 : W := mkw 0x882e004c00a8008a 0xeb7e003e007c023f

def z365 : W := mkw 0x8ac560b1d1e9b7fa 0xf7c1e0f1f1ffffff

def z366 : W := mkw 0x05ffdd482bfed88c 0x3dffff080ffffc0c

def z367 : W := mkw 0x88ee20fd81e907ba 0xfffe60ff81ff1fff

def z368 : W := mkw 0x0437dd0000bed800 0x0c3fff00003ffc00

def z369 : W := mkw 0x103bf65f6c000000 0x0c3fff0ffe000000

def z370 : W := mkw 0x01149800bab362cc 0x05019801ffb3e3cc

def z371 : W := mkw 0x14f7ff136dfed800 0x3dffff01fffffc00

def z372 : W := mkw 0x8cf7dd0001fed9aa 0xfdffff0001ffffff

def z373 : W := mkw 0x02c160b1d141b770 0xffc3e0fff1ffffff

def z374 : W := mkw 0x0404090000be4800 0x00000000003c0000

def z375 : W := mkw 0x88c400a001e801aa 0xf3c000f001fc03ff

def z376 : W := mkw 0x12fbf6ff7d40b160 0x3effffffff80e1c0

def z377 : W := mkw 0x8cffd4ec01e8d1aa 0xfbff80fe01fce3ff

def z378 : W := mkw 0x4000231304040c11 0x0000670000001c00

def z379 : W := mkw 0x020000001140b160 0x000000000180e1c0

def z380 : W := mkw 0xc82e0b4e06be088f 0xc83e1f0e0e3c000f

def z381 : W := mkw 0x0000000000000000 0xc0420036004c0033

def z382 : W := mkw 0x12fbf6fffc012770 0x3efffffffe0003f0

def z383 : W := mkw 0x00e6000001e80000 0xfbfe003e01fc023f

def z384 : W := mkw 0x0414990001fed800 0x3dbd980001fffc00

def z385 : W := mkw 0x000c004800a00088 0xfbfe00fe01fc03ff

def z386 : W := mkw 0x0000080082130204 0x040018018e030000

def z387 : W := mkw 0x011c9048baa162cc 0x12bd80c9ff80e3cc

def z388 : W := mkw 0x0000000010002040 0x108180c07180e1c0

def z389 : W := mkw 0x04f3d500014c9800 0x3cffff00004c1c00

def z390 : W := mkw 0x00f3f4b140000000 0x3efffff1f0000000

def z391 : W := mkw 0x88ffd4ec01e801aa 0xfffffffe01fc03ff

def z392 : W := mkw 0x143e9f4e2cbe4800 0x083e1f0e0e3c0000

def z393 : W := mkw 0xc80822ff860107bf 0xc20000ff8e0003ff

def z394 : W := mkw 0x06f7dda051fef960 0x3dffffc071fffdc0

def z395 : W := mkw 0x45ffff5bbffffedd 0xffffffffffffffff

def z396 : W := mkw 0x04000100014c9800 0x00000000004c1c00

def z397 : W := mkw 0x0000010000040800 0x00426700004c1c00

def z398 : W := mkw 0x0000080082130204 0x2f0018098e33020c

def z399 : W := mkw 0xc804090083ff0fbf 0xc100000001ff1fff

def z400 : W := mkw 0x04f7dd0001fed800 0x087e7f00007c1c00

def z401 : W := mkw 0x0000080082130204 0x010000000033020c

def z402 : W := mkw 0x030820f9fa0127fc 0x020000f9fe0003fc

def z403 : W := mkw 0xc8ee0bee07fe09af 0xfbfe1ffe0ffc03ff

def z404 : W := mkw 0x000800ec00000000 0x020000fe00000000

def z405 : W := mkw 0x01149800bab36244 0x3dbd9801ffb3e000

def z406 : W := mkw 0x8dffddecbbfffbee 0xffffffffffffffff

def z407 : W := mkw 0x02c160b141409530 0x35c1e03001c3fc30

def z408 : W := mkw 0x0010980000124000 0x040198000003e000

def z409 : W := mkw 0x06f7f4b1d1e9f770 0x37fde0f1f1c3fff0

def z410 : W := mkw 0x411cbb5bbeb76edd 0x3fbdffc9ffb3ffcc

def z411 : W := mkw 0x04f7dda001fed920 0x3ffffff001fffff0

def z412 : W := mkw 0x0008004828000000 0x020000c9fe000000

def z413 : W := mkw 0x01dc98e8bbf363ec 0x3ffd98f9fff3e3fc

def z414 : W := mkw 0x44369f0206be4805 0xc83e1f0e0e3c000f

def z415 : W := mkw 0x0000000000000000 0x368180c1f0000000

def z416 : W := mkw 0x00e600a001e80120 0x3bfe00f001fc03f0

def z417 : W := mkw 0xcaef6bffd7ffbfff 0xffffffffffffffff

def z418 : W := mkw 0x40002b1396172e55 0xffc3ffffffffffff

def z419 : W := mkw 0x01ddf8f9fab362cc 0x3ffdf8f9ffb3e3cc

def z420 : W := mkw 0x44f7df0207fed805 0xfdffff0e0ffffc0f

def z421 : W := mkw 0x120822fffc012770 0x020000fffe0003f0

def z422 : W := mkw 0x100822ff6c000000 0x2e427ffffe000000

def z423 : W := mkw 0x00e6000001e80000 0x10bc000001800000

def z424 : W := mkw 0x10fbf6ff6c000000 0x14bdffc1fe000000

def z425 : W := mkw 0x40000b0286170a05 0xef021f0f8e3f020f

def z426 : W := mkw 0x88e600a401e80122 0xf9fe003601fc0033

def z427 : W := mkw 0x4110bb13be176e55 0xef43ff3ffe7ffe3f

def z428 : W := mkw 0x0104080092b362cc 0x2f0018098fb3e3cc

def z429 : W := mkw 0x12d1f6b3fd41b770 0x37c1fff1ffc3fff0

def z430 : W := mkw 0x011c98482ab2408c 0x3dbd98080fb3e00c

def z431 : W := mkw 0x10fbd4ec68000000 0x3cffffc070000000

def z432 : W := mkw 0x40002b1386170e15 0xc1426736007f1e3f

def z433 : W := mkw 0x40000b0206160805 0xeb421f3e0e7c023f

def z434 : W := mkw 0x88ea00ec01480122 0xfafe00fe004c0033

def z435 : W := mkw 0x50fbffffee170e15 0x3efffffffe031c00

def z436 : W := mkw 0x0511dd00ba17fa44 0x0401ff01fe03fc00

def z437 : W := mkw 0x88ee00ec00a8008a 0xfafe00fe003c000f

def z438 : W := mkw 0x88ee22ff05e801aa 0xfffe7fff8ffc03ff

def z439 : W := mkw 0x04369d0001fed800 0x093e1f0001fffc00

def z440 : W := mkw 0xc8e223b7054c0d33 0xc0426736004c1c33

def z441 : W := mkw 0x4411ff138617de15 0xef43ff3f8e7ffe3f

def z442 : W := mkw 0x1011d40068000000 0x0001800070000000

def z443 : W := mkw 0x0011d40000000000 0x0401ff0000000000

def z444 : W := mkw 0x98ffd4ec69e801aa 0x10bd80c0718001c0

def z445 : W := mkw 0x882e004c00a8008a 0xfbbe00ce01bc03cf

def z446 : W := mkw 0x00eb60fd40000000 0x3effe0fff0000000

def z447 : W := mkw 0xc8042b1387ff0fbf 0xef427f3f8fff1fff

def z448 : W := mkw 0x88e600a401e801aa 0xc142003601fc03ff

def z449 : W := mkw 0x12e366b7d541b770 0x37c3e7f7f1c3fff0

def z450 : W := mkw 0x04f7d50001ecd800 0x10ffe70001ccfc00

def z451 : W := mkw 0x0014990000b64800 0x3dffff0001fffc00

def z452 : W := mkw 0x02016011d001b650 0x3781e0c1f183ffc0

def z453 : W := mkw 0x42016b13d617be55 0xef43ff3ffe7ffe3f

def z454 : W := mkw 0x88ee09ec01fe09aa 0xfffe7ffe01ff1fff

def z455 : W := mkw 0x02c020b1d1412770 0x33c000f1f1c003f0

def z456 : W := mkw 0x12e366b745409530 0x0042673600401c30

def z457 : W := mkw 0x031c9848bbf3f7fc 0x3fbd98c9fff3fffc

def z458 : W := mkw 0x4000291182170e15 0xe7406031807f1e3f

def z459 : W := mkw 0x1411ff136c16d800 0x0401ff01fe03fc00

def z460 : W := mkw 0x01000000920122cc 0x00000000000003cc

def z461 : W := mkw 0x40000b0286170e15 0xc9021f0e0e7f1e3f

def z462 : W := mkw 0x02eb60fdd141b770 0x3fffe0fff1c3fff0

def z463 : W := mkw 0x111dfe5bfeb362cc 0x3fbdffc9ffb3e3cc

def z464 : W := mkw 0x0000080000120000 0x2d00180000330000

def z465 : W := mkw 0x89fe90ec39e861ea 0xfbff80fe71fce3ff

def z466 : W := mkw 0x00189848aa130204 0x3fbd98c9fe33020c

def z467 : W := mkw 0x11fffeff6eb2408c 0x3efffffffe30000c

def z468 : W := mkw 0x88ee004c01e8008a 0xf9fe000e01fc000f

def z469 : W := mkw 0x0000000080010610 0x0100000000431e30

def z470 : W := mkw 0x8804000001e801aa 0x00000000018001c0

def z471 : W := mkw 0x0104000010a060c8 0x000000000180e1c0

def z472 : W := mkw 0x98fe96ee2de801aa 0xfbfe1ffe0ffc03ff

def z473 : W := mkw 0x00f7dc0000b24000 0x3dffff0001b3e000

def z474 : W := mkw 0x0001400000009000 0x0401e0000003fc00

def z475 : W := mkw 0x42002b139757bf75 0xef427f3f8fffffff

def z476 : W := mkw 0xccffffff87ffdfbf 0xffffffff8fffffff

def z477 : W := mkw 0x44f7dd0083ffde15 0xfdffff0001fffe3f

def z478 : W := mkw 0x8aef40ec51e8b1ea 0xfbff80fe71fce3ff

def z479 : W := mkw 0x890800ecba0123ee 0xc20000fffe0003ff

def z480 : W := mkw 0x00c160b141409000 0x37c1e0f1f1c3fc00

def z481 : W := mkw 0x4000090082170e15 0xef0018098e7f1e3f

def z482 : W := mkw 0xc8ee23ff05ec0dbb 0xfbfe67fe01fc1fff

def z483 : W := mkw 0x053e9d48babf6acc 0x3fbf9fc9ffbfe3cc

def z484 : W := mkw 0x9afff6fffde9b7fa 0xffffffffffffffff

def z485 : W := mkw 0x42016b13d617be55 0x0401ff01fe03fc00

def z486 : W := mkw 0x40002b1386170e15 0x27407f318e431e30

def z487 : W := mkw 0x00f3d40000000000 0x10bd800000000000

def z488 : W := mkw 0x000020b140000000 0x020000f1f0000000

def z489 : W := mkw 0x50e36fb7c6170e15 0xef427f3f8e7f1e3f

def z490 : W := mkw 0x10fbfeffee130204 0x3ffffffffe33020c

def z491 : W := mkw 0x1018b2ff6c000000 0x3ebd98fffe000000

def z492 : W := mkw 0x0000291180170e10 0x2f427f31807f1e30

def z493 : W := mkw 0x4018bb5bae170e15 0xfffffffffe7f1e3f

def z494 : W := mkw 0x101096022c000000 0x00001f000e000000

def z495 : W := mkw 0x0000000090012240 0x020000c1f00003c0

def z496 : W := mkw 0x44e36f13875f9e15 0xef427f3f8e7f1e3f

def z497 : W := mkw 0x00ee00ec01e80000 0x3bfe00fe01fc0000

def z498 : W := mkw 0x8c04090001fed9aa 0xc100000001ffffff

def z499 : W := mkw 0x5011ff13ee170e15 0xef43ff3ffe7f1e3f

def z500 : W := mkw 0x100022b744000000 0x0000003600000000

def z501 : W := mkw 0x0018904828000000 0x10bd80c070000000

def z502 : W := mkw 0x103a944c28000000 0x003c000000000000

def z503 : W := mkw 0x14fff6ff6de8d000 0x3effffffff80e000

def z504 : W := mkw 0x00f6980001fa4000 0x3dff980001ffe000

def z505 : W := mkw 0x0000000000000000 0x2340003000400230

def z506 : W := mkw 0x12fbf6fffc01b650 0x3efffffffe03fc00

def z507 : W := mkw 0x8aee20fdd1e927fa 0xfbfe00fff1fc03ff

def z508 : W := mkw 0x88000000000001aa 0xc0000000000003ff

def z509 : W := mkw 0x02016011d141b770 0x0501e001f1c3fff0

def z510 : W := mkw 0x98fff6ff6de801aa 0x3effffffff8001c0

def z511 : W := mkw 0x503a9f4e2e160805 0xc83e1f0e0e3c000f

def z512 : W := mkw 0x05f7dd00bbfffa44 0x3dffff01fffffc00

def z513 : W := mkw 0x113e9e4ebeb362cc 0x3fbf9fcfffb3e3cc

def z514 : W := mkw 0x44042b1387ffde15 0xef427f3f8ffffe3f

def z515 : W := mkw 0x02c140009141b770 0x35c1e00001c3fff0

def z516 : W := mkw 0x113e9e4e2eb2408c 0x083e1f0e0e30000c

def z517 : W := mkw 0x0000201180010610 0xef42603f807f1e3f

def z518 : W := mkw 0x11ffd4ec78a060c8 0x10bd80c07180e1c0

def z519 : W := mkw 0x011c9848bab362cc 0x093c18080fb3e3cc

def z520 : W := mkw 0x88ee00ec01e801aa 0x39fe00c001fc01c0

def z521 : W := mkw 0x02c162b3d541b770 0x3fc3ffffffc3fff0

def z522 : W := mkw 0x0114980092b362cc 0x3dbd980001b3e3cc

def z523 : W := mkw 0x0504090093fffacc 0x0100000001ffffcc

def z524 : W := mkw 0x0000000000000000 0x2540600000431c00

def z525 : W := mkw 0x42c163b345449d31 0xc0426736004c1c33

def z526 : W := mkw 0x051ddd48bab7facc 0x3fbdffc9ffb3ffcc

def z527 : W := mkw 0x020000009001b650 0x000000000003fc00

def z528 : W := mkw 0x00e2000000000000 0x38fe000000000000

def z529 : W := mkw 0x0008004800000088 0x020000c8000003cc

def z530 : W := mkw 0x50fbf6ffee010615 0xfefffffffe00023f

def z531 : W := mkw 0x0200000001409530 0x0000000000401c30

def z532 : W := mkw 0x88ef60fd41e801aa 0xffffe0fff1fc03ff

def z533 : W := mkw 0x02c160b1d141b770 0x024060f1f0401ff0

def z534 : W := mkw 0x011c9848aab3428c 0x2f3c18098e33020c

def z535 : W := mkw 0x0201601140009410 0x0000600000001c00

def z536 : W := mkw 0x06e365b1d14dbf70 0x37c3e7f1f1cffff0

def z537 : W := mkw 0x011c904838a060c8 0x3bbd80c871b0e3cc

def z538 : W := mkw 0x41042b1396b76edd 0xef427f3f8fffffff

def z539 : W := mkw 0x40c16b1387579e15 0xffc3ff3f8ffffe3f

def z540 : W := mkw 0x10fbd6ee6c000000 0x18bf9fce7e000000

def z541 : W := mkw 0x8aef60fdd1e9b7fa 0x37fde0f1f1c3fff0

def z542 : W := mkw 0x00ee00ec00a00088 0x3bfe00fe01b003cc

def z543 : W := mkw 0x8cf7dda401fed922 0xfdffff3601fffc33

def z544 : W := mkw 0x00cc00e801e001a8 0x3bfc00f801f003fc

def z545 : W := mkw 0x882e004c01e801aa 0xc93e000e01fc03ff

def z546 : W := mkw 0x111cbafffeb362cc 0x3fbd98ffffb3e3cc

def z547 : W := mkw 0x0000201180010610 0x0400600180031c00

def z548 : W := mkw 0x40f3ff1386170e15 0xffffff3f8e7f1e3f

def z549 : W := mkw 0x00002b1304160800 0x2f427f3f8e7f1c00

def z550 : W := mkw 0x00c020b181410730 0x37c060f181c31ff0

def z551 : W := mkw 0xc9febbffbfff6fff 0xffffffffffffffff

def z552 : W := mkw 0x4000221386010615 0xe740603f8e431e3f

def z553 : W := mkw 0xc82e2b5f86bf0e9f 0xef7e7f3f8e7f1e3f

def z554 : W := mkw 0x02c160b1d141b770 0x128180f1f180e3f0

def z555 : W := mkw 0x882e004c00a8008a 0x003c000000000000

def z556 : W := mkw 0x020020119141b770 0x2740603181c3fff0

def z557 : W := mkw 0x98ffd4ec69e801aa 0xfbff80fe71fc03ff

def z558 : W := mkw 0x0000000082010204 0x020000098e00020c

def z559 : W := mkw 0x4000090002160805 0xc0000000003c000f

def z560 : W := mkw 0x00c000a001400120 0x108000c0018001c0

def z561 : W := mkw 0x4000000082010615 0xc00000000000023f

def z562 : W := mkw 0x0004080000b24000 0x0100000001b3e000

def z563 : W := mkw 0x4014bb1386b74e15 0xffffff3f8ffffe3f

def z564 : W := mkw 0x8904080093fb63ee 0xc100000001ffe3ff

def z565 : W := mkw 0x00e7400001e89000 0x3dffe00001fffc00

def z566 : W := mkw 0x0436940000a84000 0x003c000000000000

def z567 : W := mkw 0x02c140a05140b160 0x33c180f071c0e3f0

def z568 : W := mkw 0x011c904828a04088 0x003c000000000000

def z569 : W := mkw 0x0010900028000000 0x04019801fe000000

def z570 : W := mkw 0x0026000000a80000 0x083e0000003c0000

def z571 : W := mkw 0x14fbffff6c16d800 0x3efffffffe03fc00

def z572 : W := mkw 0x4000090082170e15 0xeb42003e007f1e3f

def z573 : W := mkw 0x103a964e2c000000 0x3ebf9fcffe000000

def z574 : W := mkw 0x00ea22ff04000000 0x3efe7fff8e000000

def z575 : W := mkw 0x411cbb5baeb74e9d 0xef7e7f3f8e7f1e3f

def z576 : W := mkw 0x001c984800b24088 0x3fbd98c801b3e3cc

def z577 : W := mkw 0x02c140a0d141b360 0x378180c1f183e3c0

def z578 : W := mkw 0x031df859fab3f6dc 0x3fbdf8c9ffb3ffcc

def z579 : W := mkw 0x4000231386050e15 0xc242673f8e4c1e3f

def z580 : W := mkw 0x1008024e2c000000 0x0000000e0e000000

def z581 : W := mkw 0x420022b3d6012775 0xc20000fffe0003ff

def z582 : W := mkw 0x40000b0206160805 0x00001f000e000000

def z583 : W := mkw 0x891c9848bbfb63ee 0xffbd98c9ffffe3ff

def z584 : W := mkw 0x0000201100000000 0x2640603180000000

def z585 : W := mkw 0x0001601140000000 0x0401e001f0000000

def z586 : W := mkw 0x880800ec000001aa 0xeb4200fe007c03ff

def z587 : W := mkw 0x02c140a041409120 0x0000000000000000

def z588 : W := mkw 0x4000231304040c11 0xee427f3f8e4c1c33

def z589 : W := mkw 0x4000221386010615 0xeb42003f8e7c023f

def z590 : W := mkw 0x42c169b1d357bf75 0xf7c1e0f1f1ffffff

def z591 : W := mkw 0x00c160b141400120 0x37c1e0f1f1c003f0

def z592 : W := mkw 0x0104080002b2408c 0x000000000030000c

def z593 : W := mkw 0x051c9948bbfffacc 0x3fbd98c9ffffffcc

def z594 : W := mkw 0x0000000090012240 0x04018001f003e000

def z595 : W := mkw 0x98fff6ff6ca8008a 0xfefffffffe3c000f

def z596 : W := mkw 0x8cee09ec01fed9aa 0xfbfe00fe01ffffff

def z597 : W := mkw 0x011098002a124004 0x000018000e000000

def z598 : W := mkw 0x00c000a091412360 0x37c180f1f1c3e3f0

def z599 : W := mkw 0x01080048ba0122cc 0x378180c9ff83e3cc

def z600 : W := mkw 0x00c162b344000000 0x3ec3fffffe000000

def z601 : W := mkw 0x0032940000000000 0x083e1f0000000000

def z602 : W := mkw 0x98ee22ff6de801aa 0xfbfe00fffffc03ff

def z603 : W := mkw 0x1011f6136c000000 0x2e43ff3ffe000000

def z604 : W := mkw 0x400c2b5b86b70e9d 0xfffe7fff8fff1fff

def z605 : W := mkw 0x02c160b1d0012770 0x36c1e0f1f00003f0

def z606 : W := mkw 0x0604090091ffff70 0x0100000001fffff0

def z607 : W := mkw 0x10d1f6b36c000000 0x36c1fff1fe000000

def z608 : W := mkw 0x02c160b1d001b650 0x36c1e0f1f003fc00

def z609 : W := mkw 0x411c9b4abeb76acd 0xffbf9fcfffbfe3cf

def z610 : W := mkw 0x10fbf4fd68000000 0x36fde0f1f0000000

def z611 : W := mkw 0x50e367b744040c11 0xc0426736004c1c33

def z612 : W := mkw 0x00ee004801e80088 0x3bfe00c801fc03cc

def z613 : W := mkw 0x0014980082b34204 0x3fbd98098fb3e20c

def z614 : W := mkw 0x40e62b1387ff0e15 0xfffe7f3f8fff1e3f

def z615 : W := mkw 0x8c3e9d4c00be488a 0xc83e1f0e003c000f

def z616 : W := mkw 0x1022060604000000 0x0002070600000000

def z617 : W := mkw 0x02c160b141409530 0x36c1e0f1f0401c30

def z618 : W := mkw 0x14f7ffb745fed800 0x3dffff3601fffc00

def z619 : W := mkw 0x0000000000000000 0x2e0018098e000000

def z620 : W := mkw 0x001c984828b24000 0x3fbd98c9ffb3e000

def z621 : W := mkw 0x88ee00ec91e923ea 0xffff80fff1ffe3ff

def z622 : W := mkw 0x15fffffffffffacc 0x3fffffffffffffcc

def z623 : W := mkw 0x8ae360b541489532 0xc0426036004c1c33

def z624 : W := mkw 0x4411ff138617de15 0x0401ff018e03fc00

def z625 : W := mkw 0x420009009357bf75 0xc100000001ffffff

def z626 : W := mkw 0x03ddd0e879e0f1e8 0x10bd80c07180e1c0

def z627 : W := mkw 0x880c004801e801aa 0xfbbc00c801fc03ff

def z628 : W := mkw 0x02c160b15140b160 0x36c1e0f1f180e1c0

def z629 : W := mkw 0x0000000000000000 0x2b0000080030020c

def z630 : W := mkw 0x011c98483ab260cc 0x18bd98c87fb0e1cc

def z631 : W := mkw 0x02c169b1d157bf70 0x3fc3fff1f1fffff0

def z632 : W := mkw 0x04f7dc0001fad000 0x3dbd980001b3e000

def z633 : W := mkw 0x020000a050002160 0x000000c0700001c0

def z634 : W := mkw 0x00ea00ec00000000 0xfbfe00fe007c023f

def z635 : W := mkw 0x04e34500014c9800 0x35c3e70001cffc00

def z636 : W := mkw 0x880c00ec00a001aa 0xfbbc00fe01b003ff

def z637 : W := mkw 0x40002b1386170e15 0xc4427f378e4f1c33

def z638 : W := mkw 0x1019f6ff6c000000 0x0601fffffe000000

def z639 : W := mkw 0x0000000000000000 0x2c427f0000000000

def z640 : W := mkw 0x10fbf6ff6c000000 0x10ffe7f670000000

def z641 : W := mkw 0x40002b1386170e15 0x2f007f098e331e0c

def z642 : W := mkw 0x8efffdfdd1fffffa 0xfffffffff1ffffff

def z643 : W := mkw 0x0014900000a04000 0x10bd80000180e000

def z644 : W := mkw 0x011c98482ab2408c 0x3ebd98c9fe30000c

def z645 : W := mkw 0x103ab65f2c000000 0x2e7e7f3f8e000000

def z646 : W := mkw 0xd8ffffffefff0fbf 0xffffffffffff1fff

def z647 : W := mkw 0x12fbf4fdf941b770 0x37fde0f1f1c3fff0

def z648 : W := mkw 0x8822000400080002 0xc0020006000c0003

def z649 : W := mkw 0x4000231384050e11 0xe7426737804f1e33

def z650 : W := mkw 0x4000221304000411 0xc000003600000033

def z651 : W := mkw 0x02cd60f9d1e1b7f8 0x3ffde0f9f1f3fffc

def z652 : W := mkw 0x88fe98ec01fa41aa 0xffff98fe01ffe3ff

def z653 : W := mkw 0x00c160b1d0012240 0x37c1e0f1f183e3c0

def z654 : W := mkw 0x01189848ba1362cc 0x060198c9fe03e3cc

def z655 : W := mkw 0x10eb66ff6c000000 0x024267fffe000000

def z656 : W := mkw 0x4000020206000005 0xc000000e0e00000f

def z657 : W := mkw 0x002a004c00000000 0x083e000e00000000

def z658 : W := mkw 0x891c98ecbab363ee 0xffbd98ffffb3e3ff

def z659 : W := mkw 0x05ffd44839e8f0c8 0x10bd80c07180e1c0

def z660 : W := mkw 0x00ea00ec01400120 0x3bfe00fe01c003f0

def z661 : W := mkw 0x00f3f61304000000 0x3effff3f8e000000

def z662 : W := mkw 0x4404090083ffde15 0xc100000001fffe3f

def z663 : W := mkw 0x89ee08ec93fb63ee 0xfbfe00fe01ffe3ff

def z664 : W := mkw 0x8aef60fd41e895ba 0xfbfe60fe01fc1fff

def z665 : W := mkw 0x10fbd4ec68000000 0x3ebd98c9fe000000

def z666 : W := mkw 0x100022136c000000 0x00000001fe000000

def z667 : W := mkw 0x10ea22ff6c000000 0x3afe00fffe000000

def z668 : W := mkw 0x10fff6ff6de80000 0x3ffffffffffc0000

def z669 : W := mkw 0x8ac960fdd141b7fa 0xf7c1e0fff1c3ffff

def z670 : W := mkw 0x980822ff6c0001aa 0xc20000fffe0003ff

def z671 : W := mkw 0x0304080093f3f7fc 0x0100000001f3fffc

def z672 : W := mkw 0x4436bf1386bf4e15 0xef7e7f3f8e7f1e3f

def z673 : W := mkw 0x0000221304000000 0xef427f3f8e7c023f

def z674 : W := mkw 0x10e344a440000000 0x0000000000000000

def z675 : W := mkw 0x010c0048baa122cc 0x3bbc00c9ffb003cc

def z676 : W := mkw 0x8800000001480122 0xc0000000004c0033

def z677 : W := mkw 0x5011ff13ee170e15 0x0401ff01fe031c00

def z678 : W := mkw 0x0000000000000000 0x2a42003e00000000

def z679 : W := mkw 0x0311f811fa13f654 0x0401f801fe03fc00

def z680 : W := mkw 0x01189848ba136244 0x3ebd98c9fe03e000

def z681 : W := mkw 0x0000000000000000 0x338000c0018003c0

def z682 : W := mkw 0x00c1601181419610 0x37c1e03181c3fe30

def z683 : W := mkw 0x0000090000160800 0xef427f3e007f1e3f

def z684 : W := mkw 0x03c568b1d3f3f7fc 0x37c1e0f1f1f3fffc

def z685 : W := mkw 0x03ddd8e8fbf3f3ec 0x3fbd98c9ffb3e3cc

def z686 : W := mkw 0x88ee00ec01e801aa 0xc87e003e007c003f

def z687 : W := mkw 0x0000201180010610 0x0200003180000230

def z688 : W := mkw 0x01ddd848bbf3f2cc 0x3ffdf8c9fff3ffcc

def z689 : W := mkw 0x00c1400001409000 0x108180000180e000

def z690 : W := mkw 0x88ee00ec01e801aa 0x33fc00f001c003f0

def z691 : W := mkw 0x00f7d40001e80000 0x3dffff0001fc0000

def z692 : W := mkw 0x07fffdf9fbfffffc 0x3ffffff9fffffffc

def z693 : W := mkw 0x000c004800a00088 0x083c00080030000c

def z694 : W := mkw 0x03ddf0f9f9e1f7f8 0x37fde0f1f1c3fff0

def z695 : W := mkw 0x00c000a000000000 0x32c000f000000000

def z696 : W := mkw 0x06f7d4a051e8f160 0x10bd80c07180e1c0

def z697 : W := mkw 0x0018904828000000 0x083c18080e000000

def z698 : W := mkw 0x0008004800000000 0x3abc00c800000000

def z699 : W := mkw 0x893e984cbabb62ce 0xffbf98cfffbfe3cf

def z700 : W := mkw 0x98e366b745480122 0xc0426736004c0033

def z701 : W := mkw 0x0010900000000000 0x3cbd980000000000

def z702 : W := mkw 0x893e984c2aba408e 0xc83e180e0e3c000f

def z703 : W := mkw 0x0014980090b36240 0x3fbd98c1f1b3e3c0

def z704 : W := mkw 0x89fe98ecbbfb63ee 0x3fbd98c9ffb3e3cc

def z705 : W := mkw 0x100800ec68000000 0x000000c070000000

def z706 : W := mkw 0x500822ffee010615 0xc20000fffe00023f

def z707 : W := mkw 0x40002b1306160c15 0xee427f3f8e7c1c3f

def z708 : W := mkw 0x0636bdb1d0bf6f70 0x0a3e1ff1f03c03f0

def z709 : W := mkw 0x98fbf6ff6c00008a 0xfefffffffe00000f

def z710 : W := mkw 0x10fbf6ff6c000000 0x14fffff7fe000000

def z711 : W := mkw 0xca0822ffd60127ff 0xc20000fffe0003ff

def z712 : W := mkw 0x8d3e9d4c2abe488e 0xc83e1f0e0e3c000f

def z713 : W := mkw 0x89f298a4bb5b6366 0xc4439837fe4fe033

def z714 : W := mkw 0x001c9048b8a122c8 0x3fbd98c9ffb3e3cc

def z715 : W := mkw 0x510822fffe0126dd 0xc20000fffe0003ff

def z716 : W := mkw 0x120822fffc012650 0x020000fffe000000

def z717 : W := mkw 0x50fbf6ff6c000411 0xfefffffffe000033

def z718 : W := mkw 0x42c162b3d741b775 0xffc3ffffffc3ffff

def z719 : W := mkw 0x12e366b745409120 0x0042673600000000

def z720 : W := mkw 0x04f7dd0001fed800 0xfdffff0e01fffc0f

def z721 : W := mkw 0x0018904828000000 0x3effffc9fe000000

def z722 : W := mkw 0x02c140a0d141b360 0x37c1e0c1f1c3ffc0

def z723 : W := mkw 0x411cb35b3ca46cd9 0xd0ffe7f671ccfdf3

def z724 : W := mkw 0x011c9848bab362cc 0x37bd98c1ff83e3c0

def z725 : W := mkw 0xc8ee2bff87ff0fbf 0x14bc7fc18f831dc0

def z726 : W := mkw 0x05eb4548bb4dbacc 0x024267c9fe4c1fcc

def z727 : W := mkw 0x011c99482ab6488c 0x083e1f080e3c000c

def z728 : W := mkw 0x88ee00ec01e801aa 0xd1fe00f601fc03ff

def z729 : W := mkw 0x44f7f61387e9d615 0xd2bd803f8f80e23f

def z730 : W := mkw 0x020160b1d001b770 0x3781e0f1f183fff0

def z731 : W := mkw 0x8a2f605dd0a9b6da 0xcc3fe00ff03ffc0f

def z732 : W := mkw 0x011c9848bab362cc 0x3ffd98f9fff3e3fc

def z733 : W := mkw 0x10fab6ff6c000000 0x3afe1ffffe000000

def z734 : W := mkw 0x50fbddecea170e15 0xd1bd80c0707f1e3f

def z735 : W := mkw 0x882e004c00a8008a 0xfbfe00fe01fc03ff

def z736 : W := mkw 0x00fab2ff2c000000 0x3efffffffe000000

def z737 : W := mkw 0xc904090093ff6fff 0xc100000001ffffff

def z738 : W := mkw 0x123a964ebd41b770 0x093e1f0e0fc3fff0

def z739 : W := mkw 0x02016011d001b650 0x1481e0c1f183fdc0

def z740 : W := mkw 0x00f7dc0001f2d000 0x3dffff0001f3fc00

def z741 : W := mkw 0x88ef40ec01e801aa 0xffffe0fe01fc03ff

def z742 : W := mkw 0x0000000090012650 0x378180c1f1c3fff0

def z743 : W := mkw 0x03ddf8f96bf2d5bc 0x087c78380e701c3c

def z744 : W := mkw 0x02c160b1d141b770 0x11c1e0f071c3fff0

def z745 : W := mkw 0x04f3dd00015ed800 0x3cffff00004ffc00

def z746 : W := mkw 0x011c9848bab362cc 0x1cbd98c9ffb3e1cc

def z747 : W := mkw 0x02c160b1d001b650 0x37c1e0f1f183ffc0

def z748 : W := mkw 0x40002b1396172e55 0xef427f3f8fffffff

def z749 : W := mkw 0x11e76eb7d6b362cc 0x0142673601b3e3cc

def z750 : W := mkw 0x10fbf6ff6c000000 0x3fffffffff8003c0

def z751 : W := mkw 0x8ae360b5d149b772 0x37c1e0f1f1c3fff0

def z752 : W := mkw 0x8c19ddec0016d9aa 0xc601fffe0003ffff

def z753 : W := mkw 0x0000221384010610 0xef427f3f8e7f1e3f

def z754 : W := mkw 0x00c160b141409120 0x37c1e0f1f1c3fff0

def z755 : W := mkw 0x00c140a09141b360 0x37c1e0f1f1c3fff0

def z756 : W := mkw 0x88ee00ec00a801aa 0xfafe00fe003c03ff

def z757 : W := mkw 0x882e00ec00a801aa 0xeb7e00fe007c03ff

def z758 : W := mkw 0x00f7d40001e89000 0x3dffff0001fffc00

def z759 : W := mkw 0x0437dd0000bed800 0x043dff000003fc00

def z760 : W := mkw 0x9815f6136de801aa 0xc501ff01fffc03ff

def z761 : W := mkw 0x14f7dd0069fed800 0x3dffff0071fffc00

def z762 : W := mkw 0x02c160b1d141b770 0x3fc1f8f9ffc3fff0

def z763 : W := mkw 0x12fbf6ff6d409530 0x3fffffffffc01ff0

def z764 : W := mkw 0x04f7dd0001fed800 0x15bdff0001fffc00

def z765 : W := mkw 0x02c160b1d141b770 0xf7c1e0f1f1ffffff

def z766 : W := mkw 0x88ee00ec01e801aa 0xffff80fff1fc03ff

def z767 : W := mkw 0x011c9948bab76acc 0x3fbdffc9ffb3ffcc

def z768 : W := mkw 0x0019d44828000000 0x3ebdffc9fe000000

def z769 : W := mkw 0x12fbf6ff6c000530 0x3efffffffe000030

def z770 : W := mkw 0x0415dd0000b6d800 0x3dffff0001fffc00

def z771 : W := mkw 0x40000b0206160805 0xef427f3e0e7f1e3f

def z772 : W := mkw 0x02c000a09141b770 0x37c180f1f1c3fff0

def z773 : W := mkw 0x011c9048baa162cc 0x3bbd80c9ffb0e3cc

def z774 : W := mkw 0x011c9848bab362cc 0x3dbd98c1ffb3e1c0

def z775 : W := mkw 0x011c9948bab76acc 0x3fbf9fc9ffbfe3cc

def z776 : W := mkw 0x011c904838a060c8 0x3fbd98c9ffb0e3cc

def z777 : W := mkw 0x88ee00ec01e801aa 0xc97e003e01fc03ff

def z778 : W := mkw 0x42c14ba25756b965 0xd8839fce7fbce1cf

def z779 : W := mkw 0x103bf65f6c000000 0x2e7fff3ffe000000

def z780 : W := mkw 0x40002b1386170e15 0xffc3ff3f8ffffe3f

def z781 : W := mkw 0x051c9d482ab6488c 0x083c1f080e30000c

def z782 : W := mkw 0x04f7dd0001fed800 0x3fffff0801fffe0c

def z783 : W := mkw 0x1019f65b6c000000 0x0c3dff09fe000000

def z784 : W := mkw 0x04f7dd0029fed800 0x3dffff01fffffc00

def z785 : W := mkw 0x4000231304040c11 0xef427f3f8e7c1e3f

def z786 : W := mkw 0x103ab65f6c000000 0x083e1f0ffe000000

def z787 : W := mkw 0x98fbf6ff6c0001aa 0x3efffffffe0001c0

def z788 : W := mkw 0x0411dd000016d800 0x3cbdff000003fc00

def z789 : W := mkw 0x0504090093fffa44 0x0100000001fffc00

def z790 : W := mkw 0x00e7490001fe9800 0x3dffff0001fffc00

def z791 : W := mkw 0x10fbf6ff6c000000 0x3cffffc1fe000000

def z792 : W := mkw 0x04f7dd0001fed800 0xfdffff0001fffe3f

def z793 : W := mkw 0x103bf65f6c000000 0x3ebfffcffe000000

def z794 : W := mkw 0x0437dd0000bed800 0x2d7fff00007ffc00

def z795 : W := mkw 0x5211ff13fe17be55 0x0401ff01fe03fc00

def z796 : W := mkw 0x88ea00ec000001aa 0xfbfe00fe007c03ff

def z797 : W := mkw 0x00189848ba132244 0x3fbd98c9ffb3e3cc

def z798 : W := mkw 0x103ab65f2c000000 0x3efffffffe000000

def z799 : W := mkw 0x02c140a05140b160 0x1481e0c07183fdc0

def z800 : W := mkw 0x04d5dd0001f6d800 0x3dfdff0001f3fc00

def z801 : W := mkw 0x001c9848b8b36240 0x3fbd98c9ffb3e3c0

def z802 : W := mkw 0x02c160b1d141b770 0x1581e0c1f1c3fff0

def z803 : W := mkw 0x8cf7dd0001fed88a 0xfdffff0001fffc0f

def z804 : W := mkw 0x10fbf6ff6c000000 0x3ffffffffe400230

def z805 : W := mkw 0x02e360b1d141b770 0x3fffe0f1f1c3fff0

def z806 : W := mkw 0x04f7dd0001fed800 0x14ffff0001cffc00

def z807 : W := mkw 0x01149800bab36244 0x3fbd98c1ffb3e3c0

def z808 : W := mkw 0x140c2bff6dfed800 0x030000fffffffc00

def z809 : W := mkw 0x020020b1d141b770 0x378180f1f1c3fff0

def z810 : W := mkw 0x10fbf6ff6d480000 0x3efffffffe4c0000

def z811 : W := mkw 0x880c00ec01e801aa 0xfbbc00fe01fc03ff

def z812 : W := mkw 0x9ce367b7454c9922 0xc0426736004c1c33

def z813 : W := mkw 0x0014990000b64800 0x3dbdff0001b3fc00

def z814 : W := mkw 0x053e9d4828be4888 0x083e1f00003c0000

def z815 : W := mkw 0x0437dd0001fed800 0x0d3fff0001fffc00

def z816 : W := mkw 0x9ae366b745489532 0xc0426736004c1c33

def z817 : W := mkw 0x88ee00ec01e801aa 0xfffe60fe01ff1fff

def z818 : W := mkw 0x10ea22ff6c000000 0x3efe7ffffe000000

def z819 : W := mkw 0x103a964e2c000000 0x0c3f9f0ffe000000

def z820 : W := mkw 0x42002b13d6172e55 0xef427f3ffe7f1e3f

def z821 : W := mkw 0x8cf7dd0401fed802 0xfdffff0601fffc03

def z822 : W := mkw 0x04369d0001fed800 0x2d7e7f0001fffc00

def z823 : W := mkw 0x10f3f6136c000000 0x14bdff01fe000000

def z824 : W := mkw 0x10fbf6ff6c000000 0x3ffffffffe7c0000

def z825 : W := mkw 0x9ae366b7d549b772 0xf7c3e7f7f1cffff3

def z826 : W := mkw 0x880c004801e801aa 0xfbfe00fe01fc03ff

def z827 : W := mkw 0x020000009141b770 0x118180c071c3fff0

def z828 : W := mkw 0x98ee00ec69e801aa 0xfbfe00fe71fc03ff

def z829 : W := mkw 0x011c9848bab362cc 0xffbd98ffffb3e3ff

def z830 : W := mkw 0x04f7dd0001fed800 0x3fffff3e01fffc00

def z831 : W := mkw 0x01189048ba0122cc 0x3fbd98c9ff83e3cc

def z832 : W := mkw 0x130822fffe0127fc 0x020000fffe0003fc

def z833 : W := mkw 0x40002b1386170e15 0xffc27fff8fff1fff

def z834 : W := mkw 0x020020b1d0012770 0x37c1e0f1f1c3fff0

def z835 : W := mkw 0x011c9048b8a162c8 0x3fbd98c9ff83e3c0

def z836 : W := mkw 0x020160b1d141b770 0x0701e0f1f1c3fff0

def z837 : W := mkw 0x011c984838b260c8 0x3fbd98c9ffb3e1c0

def z838 : W := mkw 0x10fbd4ec68000000 0x3effffc9fe000000

def z839 : W := mkw 0x88ee00ec29e801aa 0xfbfe00fffffc03ff

def z840 : W := mkw 0x04f7dd0001fed800 0xfdffff3601fffc33

def z841 : W := mkw 0x8ae360b5d149b772 0xffc3e0fff1ffffff

def z842 : W := mkw 0x011c9848bab362cc 0x3fffffc9ffb3e3cc

def z843 : W := mkw 0x40002b1386170e15 0xca427f3f8e7c1e3f

def z844 : W := mkw 0x10fbf6ff6d409000 0x3effffffff80e000

def z845 : W := mkw 0x00002b1304160800 0xef427f3f8e7f1e3f

def z846 : W := mkw 0x00f3d40000009000 0x3cffff000003fc00

def z847 : W := mkw 0x153e9f4e2ebe488c 0x083e1f0e0e3c000c

def z848 : W := mkw 0x00f6990001fe4800 0x3dffff0001fffc00

def z849 : W := mkw 0x411c9b4a2eb6488d 0x083c1f080e30000c

def z850 : W := mkw 0x4511ff13be17fe55 0x0401ff01fe03fc00

def z851 : W := mkw 0x04f7dda001fed920 0x3dffffc001fffdc0

def z852 : W := mkw 0x10f3f6b76c000000 0x3cffff37fe000000

def z853 : W := mkw 0x02c162b3d541b770 0x37c3e7f7f1c3fff0

def z854 : W := mkw 0x40002b1396172e55 0xef427ffffe7f1fff

def z855 : W := mkw 0x04f7dd0001fed800 0x3fffffc1f1fffc00

def z856 : W := mkw 0x020020119141b770 0x37c1e0f1f1c3fff0

def z857 : W := mkw 0x0415dd0000b6d800 0x14bdff000183fc00

def z858 : W := mkw 0x011c98483ab260cc 0x3ebd98c9ffb0e1cc

def z859 : W := mkw 0x011c9048baa162cc 0x3ebd98c9ff80e3cc

def z860 : W := mkw 0x10fbf65f6c000000 0x3cffff0ffe000000

def z861 : W := mkw 0x453e9f4a2ebe488d 0xc83e1f0e0e3c000f

def z862 : W := mkw 0x04f7dda001fed920 0x3dffff3001fffc30

def z863 : W := mkw 0x8cf7dda001fed9aa 0xfffffff001ffffff

def z864 : W := mkw 0x88e6000001e801aa 0xfbfe003e01fc03ff

def z865 : W := mkw 0x02c160b1d141b770 0xf7c1e0fff1c3ffff

def z866 : W := mkw 0x02c160b15140b570 0x35c1e0f071c3fdf0

def z867 : W := mkw 0x40002b1306160c15 0xeb427f3e0e7c1e3f

def z868 : W := mkw 0x98fbf6ff6d4001aa 0xffffffffffc003ff

def z869 : W := mkw 0x05f7dd0003fed88c 0x3dffff0001fffc0c

def z870 : W := mkw 0x02c160b1d141b770 0x3781e0c1f183ffc0

def z871 : W := mkw 0x04f7dd0003fed804 0x3dffff080ffffc0c

def z872 : W := mkw 0x04f7dd0001fed800 0x3dbdff0001b3fc00

def z873 : W := mkw 0x10fbf6ff6d409120 0x3fffffffffc3fff0

def z874 : W := mkw 0x04f3dd000156d800 0x3dffff0001c3fc00

def z875 : W := mkw 0x04f7dda001fed920 0xfffffffe01ffffff

def z876 : W := mkw 0x40002b1386170e15 0xcc427f3f8e7f1c3f

def z877 : W := mkw 0x00cc00e801e001a8 0xfbfe00fe01fc03ff

def z878 : W := mkw 0x02e360b1d149b770 0x37c3e0f1f1cffff0

def z879 : W := mkw 0x04369d0000be4800 0x3dffff0001fffc00

def z880 : W := mkw 0xc90822ffbe0127ff 0xc20000fffe0003ff

def z881 : W := mkw 0x40002b1386170e15 0xffc3fffffe7f1e3f

def z882 : W := mkw 0x06f7dda041fed920 0x3dffff0001fffc00

def z883 : W := mkw 0x00fbf65b2c000000 0x3efffffffe000000

def z884 : W := mkw 0x4108225bbe0126dd 0x020000c9fe0003cc

def z885 : W := mkw 0x04f7dd0001fed800 0x3fffffc001ffffc0

def z886 : W := mkw 0x10fbf6ff6d400000 0x3fffffffffc00000

def z887 : W := mkw 0x8cf7dd0001fed9aa 0x3dffff0001fffdc0

def z888 : W := mkw 0x103ab6ff6c000000 0x3ebf9ffffe000000

def z889 : W := mkw 0x98fbf6ff6d4801aa 0xfefffffffe4c03ff

def z890 : W := mkw 0x02c140a0d141b770 0x33c180f071c3fff0

def z891 : W := mkw 0x011c9848bab362cc 0xffbd98c9ffffe3ff

def z892 : W := mkw 0x00d9f2fb6c000000 0x3efffffffe000000

def z893 : W := mkw 0x8ac160b1d149b772 0xf7c1e0f1f1cffff3

def z894 : W := mkw 0x12e364b5d141b770 0x37c1e0f1f1c3fff0

def z895 : W := mkw 0x04f7dda001fed800 0x3ffffff001fffc00

def z896 : W := mkw 0x52e367b745449d31 0xc0426736004c1c33

def z897 : W := mkw 0x10fbf6ff6c000000 0x36fdfff1fe000000

def z898 : W := mkw 0x0018904838002040 0x3ebd98c9ff80e1c0

def z899 : W := mkw 0x04f7dd0001fed800 0x3fffff3001fffe30

def z900 : W := mkw 0x40002b1306160c15 0xed427f3e0e7f1c3f

def z901 : W := mkw 0x04f7dd0001fed800 0x0c7fff00007ffc00

def z902 : W := mkw 0x02c160b1d141b770 0x14c1e0f1f1c3fdf0

def z903 : W := mkw 0x02e360b5d141b770 0x37c3e0f7f1c3fff0

def z904 : W := mkw 0x98fbf6ff6c000122 0xfefffffffe000033

def z905 : W := mkw 0x98ef44ec41e801aa 0xfbfe00fe01fc03ff

def z906 : W := mkw 0xc93e9b4e2ebe488f 0xc83e1f0e0e3c000f

def z907 : W := mkw 0x0000000090012240 0x37c1e0c1f1c3ffc0

def z908 : W := mkw 0x04f7d50001ecd800 0x35ffe70001cffc00

def z909 : W := mkw 0x8d04090093fffbee 0xc100000001ffffff

def z910 : W := mkw 0x0414990001fed800 0x3dffff0001fffc00

def z911 : W := mkw 0x103bf6ff6c000000 0x0e3ffffffe000000

def z912 : W := mkw 0x4504090093fffedd 0xc100000001ffffff

def z913 : W := mkw 0x44f7dd0003fed805 0xfdffff0001fffc0f

def z914 : W := mkw 0x04f3d500014c9800 0x3dffff0001cffc00

def z915 : W := mkw 0x02c162b3d541b770 0x37c1fff1ffc3fff0

def z916 : W := mkw 0x0000201190012650 0x3781e0c1f183ffc0

def z917 : W := mkw 0x000140009001b240 0x3781e0c1f183ffc0

def z918 : W := mkw 0x011c9848bab362cc 0x3ebd98c9ff83e1c0

def z919 : W := mkw 0x00ee004801e80088 0xfbfe00fe01fc03ff

def z920 : W := mkw 0x16e367b7454c9d30 0x00426736004c1c30

def z921 : W := mkw 0x04f7d40001e8d000 0x3dffff0001c3fc00

def z922 : W := mkw 0x4311fb13fe17fe55 0x0401ff01fe03fc00

def z923 : W := mkw 0x9affd4ec79e8b1ea 0x10bd80c07180e1c0

def z924 : W := mkw 0xca04090093ffbfff 0xc100000001ffffff

def z925 : W := mkw 0x04f7dd0001fed800 0x3cffff000183fc00

def z926 : W := mkw 0x88ef40ec41e801aa 0xfbff80fe71fc03ff

def z927 : W := mkw 0x01189848ba136244 0x3fbd98c9ff83e3c0

def z928 : W := mkw 0x1018964a2c000000 0x3ebd9fc9fe000000

def z929 : W := mkw 0x42c162b3d541b771 0xf7c1e0f7f1c3fff3

def z930 : W := mkw 0x011c9948bab76acc 0x3fbd98c9ffffffcc

def z931 : W := mkw 0x10f3f6b36c000000 0x3efffff1fe000000

def z932 : W := mkw 0x02c160b1d141b770 0x1681e0f1f183fff0

def z933 : W := mkw 0x00fbf4f968000000 0x3efffff9fe000000

def z934 : W := mkw 0x00c160119141b650 0x37c1e0f1f1c3fff0

def z935 : W := mkw 0x1019f6ff6c000000 0x3ebdfffffe000000

def z936 : W := mkw 0x00eb62ff44000000 0x3efffffffe000000

def z937 : W := mkw 0x12c162b7d541b770 0x37c1e0f7f1c3fff0

def z938 : W := mkw 0x10fbf65b6c000000 0x3effffc9fe000000

def z939 : W := mkw 0x00e600a001e80120 0xfbfe00fe01fc03ff

def z940 : W := mkw 0x02c160b1d141b770 0x3fc3e0f1f1fffff0

def z941 : W := mkw 0x10fbf6ff6c000000 0xfefffffffe00023f

def z942 : W := mkw 0x0415dd0000b6d800 0x0c3dff000033fc00

def z943 : W := mkw 0x02c140a0d141b770 0x378180c1f1c3fff0

def z944 : W := mkw 0x891c9848babb62ce 0xffbd98c9ffbfe3cf

def z945 : W := mkw 0x02c160b15140b160 0x37c1e0f1f1c3fdc0

def z946 : W := mkw 0x000000009141b240 0x378180c1f1c3ffc0

def z947 : W := mkw 0x98fbf6ff6d480122 0xffffffffffcc03f3

def z948 : W := mkw 0x8ac160b5d141b772 0xf7c1e0f7f1c3fff3

def z949 : W := mkw 0x103a964e2c000000 0x0a3e1fcffe000000

def z950 : W := mkw 0xcae363b7454c9d33 0xc0426736004c1c33

def z951 : W := mkw 0x020000009001b650 0x378180c1f183ffc0

def z952 : W := mkw 0x430822fbfe0127fd 0xc20000fffe0003ff

def z953 : W := mkw 0x0437dd0000bed800 0x3dbfff0001bffc00

def z954 : W := mkw 0x00c140001140b040 0x35c1e0c071c3fdc0

def z955 : W := mkw 0x051c9948babf6acc 0x3fbd98c9ffbfe3cc

def z956 : W := mkw 0x011c9848bab366dc 0x3fbd98c9fff3fffc

def z957 : W := mkw 0x10fbf6ff6d409000 0x3efffffffe401c00

def z958 : W := mkw 0x011c9848bab362cc 0x1abd98c9ffb0e3cc

def z959 : W := mkw 0x12c166b3d541b770 0x37c1e7f1f1c3fff0

def z960 : W := mkw 0x10fbf6ff6c000000 0xfefffffffe3c000f

def z961 : W := mkw 0x02c160b1d141b770 0x35c1e0c1f1c3fdc0

def z962 : W := mkw 0x000c084892b322cc 0x3fbd98c9ffb3e3cc

def z963 : W := mkw 0x02c160b1d141b770 0x36c1e0f1f183fdc0

def z964 : W := mkw 0x00fbd4ec28000000 0x3efffffffe000000

def z965 : W := mkw 0x8cf7dd0001fed9aa 0xffffff3e01ffffff

def z966 : W := mkw 0x10fbf6ff6c000000 0x0c7fff3ffe000000

def z967 : W := mkw 0x8dffd4ec39e8f1ea 0x10bd80c07180e1c0

def z968 : W := mkw 0x98fbf6ff6d480122 0xfffffffffe7c023f

def z969 : W := mkw 0x04f7dd0001fed920 0x3dffff0001fffff0

def z970 : W := mkw 0x12fbf6ff6d409120 0x3efffffffe000000

def z971 : W := mkw 0x411c9948bab76edd 0xffff98ffffffffff

def z972 : W := mkw 0x12e366b7d541b770 0x3fc3ffffffc3fff0

def z973 : W := mkw 0x011c9048baa162cc 0x37bd80c9ff83e3cc

def z974 : W := mkw 0x411c9948bab76acd 0xffbd98c9ffbfe3cf

def z975 : W := mkw 0x103ab6ff6c000000 0x2e7e7ffffe000000

def z976 : W := mkw 0x88ee00ec01e801aa 0xd3bc00fe01fc03ff

def z977 : W := mkw 0x02c140a0d141b770 0x35c1e0c071c3fff0

def z978 : W := mkw 0x1019f65b6c000000 0x14bdffc1fe000000

def z979 : W := mkw 0x02c162b3d541b770 0x37c1e0ffffc3fff0

def z980 : W := mkw 0x02c140009141b770 0x37c1e0c1f1c3fff0

def z981 : W := mkw 0x04f7dd0001fed800 0x3fffff098ffffc00

def z982 : W := mkw 0x011c9048baa162cc 0x10bd80c1ff80e1c0

def z983 : W := mkw 0x0504090092bf6acc 0x0100000001bfe3cc

def z984 : W := mkw 0x10fbf6ff6c000000 0x1cbfffcffe000000

def z985 : W := mkw 0x011c904838a060c8 0x14bd98c1ff80e1c0

def z986 : W := mkw 0x04e7450001ec9800 0x3dffe70001fffc00

def z987 : W := mkw 0x06e364b1d149b770 0x37c1e0f1f1c3fff0

def z988 : W := mkw 0x14fbf6ff6d489000 0x3efffffffe000000

def z989 : W := mkw 0x10f3f6136c000000 0x3effff3ffe000000

def z990 : W := mkw 0x0704090093fffffc 0x0100000001fffffc

def z991 : W := mkw 0x8cf7dd0001fed922 0xfdffff0001fffc33

def z992 : W := mkw 0x882e00ec01e801aa 0xcb3e00fe01fc03ff

def z993 : W := mkw 0x88ee00ec01e801aa 0xdabe00fe01bc03ff

def z994 : W := mkw 0x0014980092b36244 0x3fbd98c9ffb3e3cc

def z995 : W := mkw 0x8cf7dda401fed922 0xfffffff601fffff3

def z996 : W := mkw 0x10fbf6ff6c000000 0x1abf9ffffe000000

def z997 : W := mkw 0x011c9948bab76acc 0xffffffffffffffff

def z998 : W := mkw 0x0018b25b2c000000 0x3ebdffc9fe000000

def z999 : W := mkw 0x891c984cbab362ce 0xffbd98cfffb3e3cf

def z1000 : W := mkw 0x011c9848bab362cc 0x3fff98c9ffffe3cc

def z1001 : W := mkw 0x88ee00ec01e801aa 0xfffe18ff8ffc03ff

def z1002 : W := mkw 0x4604090093ffff75 0xc100000001ffffff

def z1003 : W := mkw 0x88ef40ec01e891aa 0xfbff80fe01fce3ff

def z1004 : W := mkw 0x42c162b3d741b775 0xffc3e0ffffffffff

def z1005 : W := mkw 0x0504090092b7facc 0x0100000001b3ffcc

def z1006 : W := mkw 0x12fbf6ff6c009410 0x3efffffffe001c00

def z1007 : W := mkw 0x8cef44ec01e891aa 0xfbfe00fe01fc03ff

def z1008 : W := mkw 0x011c9848bab362cc 0x15bd98c1ffb3e3cc

def z1009 : W := mkw 0x10fbd64e2c000000 0x3effffcffe000000

def z1010 : W := mkw 0x00ee00ec00a00088 0xfbfe00fe01fc03ff

def z1011 : W := mkw 0x010c0048baa122cc 0x3fbd80c9ffb3e3cc

def z1012 : W := mkw 0x04f7dd0001fed800 0x097e7f0001fffc00

def z1013 : W := mkw 0x02016011d001b650 0x37c1e0f1f1c3fff0

def z1014 : W := mkw 0x0104090092b76acc 0x0100000001ffffcc

def z1015 : W := mkw 0x40002b1386170e15 0xc9427f3e0e7f1e3f

def z1016 : W := mkw 0x04f7dd0000bed800 0x3cffff00003ffc00

def z1017 : W := mkw 0x4304090093f7fffd 0xc100000001ffffff

def z1018 : W := mkw 0x9afbf6ff6d489532 0xfefffffffe4c1c33

def z1019 : W := mkw 0x00f3d40028000000 0x3cffff01fe000000

def z1020 : W := mkw 0x8cf7dda401fed9aa 0xfdffff3601ffffff

def z1021 : W := mkw 0x10fbf6ff6c000120 0x3efffffffe0003f0

def z1022 : W := mkw 0x05f7dd002bfed804 0x3dffff000ffffc00

def z1023 : W := mkw 0x051c9d48bab76acc 0x3fbd9fc9ffb3e3cc

def z1024 : W := mkw 0x02c140a05140b160 0x118180c071c3fdc0

def z1025 : W := mkw 0x411c9848bab366dd 0xffbd98c9ffb3e3ff

def z1026 : W := mkw 0x411c9948bab76edd 0x3fbd98c9ffb3ffcc

def z1027 : W := mkw 0x10fbf6ff6c000000 0x3fffffffff83e000

def z1028 : W := mkw 0x00c160b1d0012650 0x37c1e0f1f1c3fff0

def z1029 : W := mkw 0x8cf7dda401fed922 0x3dffff0001fffc00

def z1030 : W := mkw 0x011c904838a060c8 0x12bd80c9ff80e1c0

def z1031 : W := mkw 0x88e600a401e801aa 0xf9fe003601fc03ff

def z1032 : W := mkw 0x04f7dda041fed800 0x3dffffc071fffc00

def z1033 : W := mkw 0x42c162b3d741b775 0x37c1e0f1ffc3fff0

def z1034 : W := mkw 0x04e6090001fed800 0x3dfe7f0001fffc00

def z1035 : W := mkw 0x04f7dd0001fed800 0x1cbfff0001bffc00

def z1036 : W := mkw 0x88ef40ec01e891aa 0xfbfe60fe01fc1fff

def z1037 : W := mkw 0x02c140a0d141b770 0x108180c07183fdc0

def z1038 : W := mkw 0x12fbf6ff6d409530 0x3fffffffffc3fc30

def z1039 : W := mkw 0x0415dd0001fed800 0x3dbdff0001fffc00

def z1040 : W := mkw 0x9cffd4ec69e8d1aa 0x10bd80c07180e1c0

def z1041 : W := mkw 0x103bf65f6c000000 0x043dff01fe000000

def z1042 : W := mkw 0x4104090092b76acd 0xc100000001bfe3cf

def z1043 : W := mkw 0x011c9848bab362cc 0x3fff98ffffb3e3cc

def z1044 : W := mkw 0x88ef44ec01e801aa 0xfbfe67fe01fc03ff

def z1045 : W := mkw 0x04f3dd000016d800 0x14bdff000003fc00

def z1046 : W := mkw 0x10d9f6fb6c000000 0x3efdfff9fe000000

def z1047 : W := mkw 0x5111ff13fe176e55 0x0401ff01fe03fc00

def z1048 : W := mkw 0x9a0822fffc0127fa 0xc20000fffe0003ff

def z1049 : W := mkw 0x04e74d0001fed800 0x39fe670001fffc00

def z1050 : W := mkw 0x882e00ec00a801aa 0xfbbe00fe01bc03ff

def z1051 : W := mkw 0x003a944828000000 0x3ebf9fc9fe000000

def z1052 : W := mkw 0x011c9848bab362cc 0x13bd80c9ffb3e3cc

def z1053 : W := mkw 0x04f7dd0001fed800 0x35fdff0001c3fc00

def z1054 : W := mkw 0x42c160b1d341b775 0xf7c1e0f1f1c3ffff

def z1055 : W := mkw 0x98fbf6ff6d480122 0x3efffffffe000000

def z1056 : W := mkw 0x02c160b1d141b770 0x3fc3fff1f1c3fff0

def z1057 : W := mkw 0x10fbf6ff6c000410 0x3efffffffe401c30

def z1058 : W := mkw 0x8aef40ec41e891aa 0xfbfe00fe01fc03ff

def z1059 : W := mkw 0x513e9f4e2eb6488d 0xc83e1f0e0e3c000f

def z1060 : W := mkw 0x88ee00ec01e891aa 0xfbfe00fe01ffffff

def z1061 : W := mkw 0x04f7dd0001fed800 0x11ffe70001fffc00

def z1062 : W := mkw 0x02c140a05140b160 0x37c1e0f071c3fff0

def z1063 : W := mkw 0x02c160b1d141b770 0x3fc1e0f9f1f3fffc

def z1064 : W := mkw 0x02c160b1d341b774 0x37c1e0f9ffc3fffc

def z1065 : W := mkw 0x00f7dd0000b64800 0x3dffff0001fffc00

def z1066 : W := mkw 0x00c020b191412770 0x37c1e0f1f1c3fff0

def z1067 : W := mkw 0x10fbf6ff6c000000 0x16bdfffffe000000

def z1068 : W := mkw 0x00ea00ec01400120 0xfbfe00fe01fc03ff

def z1069 : W := mkw 0x011c9848bab362cc 0xffbf98cfffbfe3cf

def z1070 : W := mkw 0x10fbf6ff6c000000 0x0a7e7ffffe000000

def z1071 : W := mkw 0x00f3f6b344000000 0x3efffffffe000000

def z1072 : W := mkw 0x1033f6136c000000 0x0c3fff01fe000000

def z1073 : W := mkw 0x882e004c01e801aa 0xeb7e003e01fc03ff

def z1074 : W := mkw 0x00d5d90001f6d800 0x3dffff0001fffc00

def z1075 : W := mkw 0x10fbd6ee6c000000 0x3ebf9fcffe000000

def z1076 : W := mkw 0x04f7dd0001fed888 0x3dffff0001ffffcc

def z1077 : W := mkw 0x411c99482ab6488d 0xc83c18080e3c000f

def z1078 : W := mkw 0x04f3dd000016d800 0x3dffff00007ffc00

def z1079 : W := mkw 0x10fbf6ff6c000000 0xfefffffffe4c0033

def z1080 : W := mkw 0x10fa96ee2c000000 0x3eff9ffffe000000

def z1081 : W := mkw 0x10fbf6ff6d400120 0x3effffffff8001c0

def z1082 : W := mkw 0x88ee00ec01e801aa 0xffff80fe01ffe3ff

def z1083 : W := mkw 0x011c9848bab362cc 0x3ffdf8c9fff3ffcc

def z1084 : W := mkw 0x00f3dd0001569800 0x3dffff0001fffc00

def z1085 : W := mkw 0x04f7dda401fed800 0x3dffff3601fffc00

def z1086 : W := mkw 0x10fbf6ff6c000000 0x3ffffffffe30020c

def z1087 : W := mkw 0x02c162b3d541b770 0xffc3ffffffffffff

def z1088 : W := mkw 0x1011f6136c000000 0x3cbdff01fe000000

def z1089 : W := mkw 0x1018b2ff6c000000 0x3efffffffe000000

def z1090 : W := mkw 0x46e367b3454c9d31 0xc0426736004c1c33

def z1091 : W := mkw 0x10fbf6ff6c009000 0x3efffffffe03fc00

def z1092 : W := mkw 0x0433dd000016d800 0x0c3fff000003fc00

def z1093 : W := mkw 0x4104090092b76edd 0x0100000001b3ffcc

def z1094 : W := mkw 0x98fbf6ff6c080002 0xfefffffffe0c0003

def z1095 : W := mkw 0x88ee00ec01e801aa 0xca7e00fe007c03ff

def z1096 : W := mkw 0x40002b1396172e55 0xef43ff3ffe7ffe3f

def z1097 : W := mkw 0x00c160b1d141b240 0x37c1e0f1f1c3ffc0

def z1098 : W := mkw 0x98fbf6ff6c0001aa 0xfffffffffe7c03ff

def z1099 : W := mkw 0x41002b1396176e55 0xef427f3f8e7ffe3f

def z1100 : W := mkw 0x8cf7dda401fed922 0xffffff3e01fffe3f

def z1101 : W := mkw 0x02e364b1d141b770 0x37c3e7f1f1c3fff0

def z1102 : W := mkw 0x4611ff13d617fe55 0x0401ff01fe03fc00

def z1103 : W := mkw 0x02016011d141b770 0x3781e0c1f1c3fff0

def z1104 : W := mkw 0x001c984828b24088 0x3fbd98c9ffb3e3cc

def z1105 : W := mkw 0x14f7dda441fed800 0x3dffff0001fffc00

def z1106 : W := mkw 0x411c9948bab76edd 0xffffffc9ffffffff

def z1107 : W := mkw 0x9c3e9f4e2cbe488a 0xc83e1f0e0e3c000f

def z1108 : W := mkw 0x051c99482abe488c 0x083c18080e3c000c

def z1109 : W := mkw 0x8cee00ec01e8d1aa 0xfbfe00fe01fce3ff

def z1110 : W := mkw 0x0000090082170a04 0xef427f3f8e7f1e3f

def z1111 : W := mkw 0x14fbf6ff6c00d000 0x3efffffffe00e000

def z1112 : W := mkw 0x10fbf6ff6c000088 0x3efffffffe0003cc

def z1113 : W := mkw 0x04f7dd0000b6d800 0x3dffff0001b3fc00

def z1114 : W := mkw 0x1019f65b6c000000 0x3efffffffe000000

def z1115 : W := mkw 0x520822fffe012775 0xc20000fffe0003ff

def z1116 : W := mkw 0x10fbf6ff6d400120 0xfffffffffffc03ff

def z1117 : W := mkw 0x02c160b1d141b770 0x3fc3e0fff1c3fff0

def z1118 : W := mkw 0x880c00ec00a001aa 0xfbfe00fe01fc03ff

def z1119 : W := mkw 0x0018924a2c000000 0x3ebf9fcffe000000

def z1120 : W := mkw 0x88ee00ec01e801aa 0xfffe7ffe01fc03ff

def z1121 : W := mkw 0x011c9848bab362cc 0x16bd98c9ff83e3cc

def z1122 : W := mkw 0x02c16011d141b650 0x37c1e0c1f1c3ffc0

def z1123 : W := mkw 0x10fbf6ff6d400120 0x3efffffffe400030

def z1124 : W := mkw 0x10fbf6ff6c000000 0x3ffffffffe431c00

def z1125 : W := mkw 0x02c160b1d141b770 0xf7c3e0f7f1cffff3

def z1126 : W := mkw 0x10fbf6ff6c000000 0x3ebdffc9fe000000

def z1127 : W := mkw 0x02c160b1d141b770 0x138180f1f1c3fff0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z0,z1,z3,z4,z5]),(0,[z0,z1,z9,z2,z3,z4,z5]),(0,[z0,z10,z1,z2,z3,z4,z5]),(0,[z11,z0,z1,z2,z3,z4,z5])],[(0,[z0,z12,z2,z13,z3,z4,z5]),(0,[z0,z1,z2,z14,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z15]),(0,[z0,z1,z16,z2,z3,z17,z5]),(0,[z18,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z19,z5]),(0,[z0,z1,z20,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z21,z4,z5])],[(0,[z22,z0,z1,z2,z3,z23,z5]),(0,[z24,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z25,z4,z5]),(0,[z26,z0,z1,z2,z3,z4,z5])],[(1,[z27,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z28,z5])],[(0,[z0,z1,z2,z29,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z30]),(0,[z7,z0,z1,z31,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z32]),(0,[z0,z1,z2,z3,z33,z4,z5]),(0,[z0,z1,z2,z3,z34,z4,z5]),(0,[z35,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z36,z4,z5])],[(0,[z37,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z38]),(0,[z0,z1,z2,z3,z4,z39,z5]),(0,[z0,z1,z2,z3,z40,z4,z5]),(0,[z8,z0,z1,z3,z34,z4,z5]),(0,[z41,z0,z1,z2,z3,z4,z5])],[(0,[z42,z0,z1,z2,z3,z4,z43])]],
   [[(0,[z0,z1,z2,z3,z4,z44,z5])],[(0,[z45,z1,z2,z3,z4,z46,z5]),(0,[z0,z1,z2,z3,z4,z47,z5]),(0,[z48,z0,z1,z2,z3,z21,z4]),(0,[z49,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z50,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z51])],[(0,[z52,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z53,z4,z5]),(0,[z54,z0,z1,z2,z3,z4,z5]),(0,[z0,z55,z1,z2,z3,z19,z5]),(0,[z56,z0,z1,z57,z3,z4,z5])],[(0,[z0,z1,z2,z58,z3,z4,z5]),(0,[z0,z1,z2,z59,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z60]),(0,[z0,z1,z61,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z62,z5]),(0,[z0,z1,z2,z3,z63,z4,z5]),(0,[z64,z0,z1,z2,z3,z4,z5])],[(0,[z0,z65,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z66,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z67])],[(0,[z0,z1,z68,z2,z3,z4,z5]),(0,[z0,z1,z69,z2,z3,z4,z5])]],
   [[(0,[z70,z0,z1,z71,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z72,z5]),(0,[z0,z1,z2,z3,z73,z4,z5]),(0,[z42,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z74])],[(0,[z0,z1,z2,z3,z75,z4,z5]),(1,[z0,z1,z3,z4,z72,z5]),(0,[z76,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z77,z78,z5])],[(0,[z79,z1,z80,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z81,z5]),(0,[z0,z82,z1,z2,z3,z4,z5])],[(0,[z83,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z84,z5]),(0,[z0,z1,z2,z3,z85,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z86,z4,z5]),(0,[z0,z1,z2,z4,z87,z46,z5])],[(0,[z0,z88,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z89,z4,z5])],[(0,[z0,z1,z2,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z91,z5]),(0,[z42,z0,z1,z2,z3,z4,z92]),(0,[z0,z93,z1,z2,z3,z4,z5])],[(0,[z94,z1,z95,z2,z3,z4,z5]),(0,[z96,z94,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z97,z5]),(1,[z45,z1,z2,z3,z4,z98]),(1,[z99,z0,z2,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z100,z5]),(0,[z0,z1,z101,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z4,z103]),(0,[z104,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z79,z1,z2,z3,z4,z5]),(0,[z96,z105,z1,z2,z3,z4,z5]),(0,[z0,z106,z1,z2,z3,z4,z5])],[(0,[z0,z1,z107,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z108,z5])],[(0,[z109,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z89,z4,z19,z5]),(0,[z0,z1,z2,z3,z110,z4,z5]),(1,[z56,z0,z1,z2,z3,z51]),(0,[z0,z1,z2,z3,z4,z111,z5])],[(0,[z0,z1,z112,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z113,z4,z5]),(0,[z0,z1,z2,z3,z114,z4,z5]),(0,[z0,z1,z2,z3,z115,z4,z5]),(0,[z0,z1,z2,z3,z4,z116,z5]),(0,[z0,z117,z1,z2,z3,z4,z5])],[(0,[z118,z0,z119,z2,z3,z4,z5]),(0,[z0,z79,z1,z2,z120,z4,z5]),(0,[z121,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z122,z3,z4,z5]),(0,[z1,z2,z3,z78,z4,z123,z5]),(0,[z0,z1,z2,z124,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z125,z5]),(0,[z0,z1,z126,z2,z3,z4,z5]),(1,[z127,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z128,z4,z5])],[(0,[z129,z0,z1,z2,z3,z4,z5]),(0,[z0,z130,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z131,z3,z4,z5])]],
   [[(0,[z0,z1,z80,z2,z3,z4,z5]),(0,[z8,z70,z0,z1,z2,z4,z5]),(0,[z132,z0,z1,z2,z4,z46,z5]),(0,[z133,z0,z1,z2,z3,z4,z5]),(0,[z0,z134,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z135])],[(0,[z0,z1,z2,z3,z4,z5,z136]),(0,[z8,z0,z1,z3,z4,z5,z135])],[(0,[z0,z1,z2,z3,z4,z137,z5]),(1,[z0,z138,z139,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z140]),(0,[z141,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z31,z3,z4,z5])],[(1,[z142,z0,z1,z2,z4,z5]),(0,[z0,z1,z143,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z144]),(0,[z0,z145,z1,z2,z3,z4,z5]),(0,[z0,z146,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z103])],[(0,[z0,z147,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z148,z5]),(0,[z0,z1,z71,z31,z3,z4,z5]),(0,[z0,z1,z2,z77,z3,z4,z5])],[(0,[z149,z0,z1,z2,z3,z4,z5]),(0,[z150,z0,z1,z2,z78,z4,z5]),(0,[z151,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z152,z3,z4,z5]),(0,[z42,z0,z2,z3,z4,z5,z92]),(0,[z0,z1,z153,z2,z3,z4,z5])],[(0,[z0,z1,z154,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z155,z4,z5]),(0,[z156,z0,z1,z2,z3,z78,z5]),(0,[z56,z0,z1,z2,z3,z4,z51])],[(0,[z157,z1,z2,z158,z3,z4,z5]),(0,[z0,z1,z159,z2,z3,z4,z5]),(0,[z160,z0,z1,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z161,z5]),(0,[z0,z1,z2,z3,z4,z162,z5])]],
   [[(0,[z0,z1,z2,z3,z23,z4,z5]),(0,[z7,z0,z1,z2,z25,z4,z5]),(0,[z163,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z16,z3,z17,z5])],[(0,[z22,z0,z139,z2,z3,z4,z5]),(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z164,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z165,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z166,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z167,z5]),(0,[z0,z1,z2,z3,z4,z168,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z169,z3,z4,z5]),(0,[z0,z1,z2,z3,z170,z4,z5]),(0,[z0,z1,z171,z2,z3,z4,z5]),(0,[z172,z0,z1,z2,z3,z4,z5]),(0,[z0,z173,z1,z2,z3,z4,z5]),(0,[z0,z174,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z175,z5]),(0,[z0,z1,z2,z3,z21,z4,z51])],[(0,[z176,z0,z1,z2,z3,z4,z5]),(0,[z56,z0,z1,z153,z3,z4,z5])],[(0,[z0,z1,z3,z4,z72,z46,z5])],[(0,[z0,z1,z2,z3,z4,z5,z177]),(0,[z0,z1,z2,z3,z4,z5,z178]),(0,[z179,z0,z1,z2,z3,z4,z5]),(0,[z180,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z120,z4,z5]),(0,[z0,z1,z2,z3,z181,z4,z5]),(0,[z0,z1,z182,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z183,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z184,z5]),(0,[z0,z1,z2,z3,z185,z4,z5]),(0,[z0,z1,z2,z186,z3,z4,z103])],[(1,[z102,z0,z1,z2,z4,z103])],[(0,[z0,z1,z2,z3,z4,z187,z5]),(0,[z0,z1,z2,z3,z4,z188,z5]),(0,[z0,z1,z2,z189,z3,z4,z5]),(0,[z0,z1,z190,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z191,z5])],[(1,[z0,z2,z3,z4,z5,z192])],[(0,[z132,z0,z1,z2,z3,z4,z5]),(0,[z193,z0,z1,z2,z3,z4,z5]),(0,[z194,z0,z1,z2,z3,z4,z5])],[(0,[z195,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z196,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z197,z5]),(0,[z0,z1,z2,z3,z4,z198,z5]),(0,[z0,z105,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z199])],[(0,[z142,z0,z1,z2,z158,z4,z5]),(0,[z0,z200,z1,z2,z3,z4,z5]),(0,[z45,z164,z1,z2,z3,z4,z5])],[(0,[z94,z0,z1,z3,z17,z4,z5]),(0,[z0,z1,z2,z3,z4,z201,z5]),(0,[z0,z1,z202,z2,z3,z4,z5]),(0,[z0,z1,z2,z57,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z203,z5]),(0,[z0,z1,z2,z3,z4,z5,z204]),(0,[z0,z1,z2,z3,z4,z98,z5]),(0,[z205,z0,z1,z2,z3,z4,z5]),(1,[z0,z206,z2,z196,z4,z5]),(0,[z0,z1,z31,z3,z34,z4,z5]),(0,[z0,z1,z2,z4,z207,z5,z103]),(1,[z0,z1,z57,z3,z4,z5])],[(0,[z157,z0,z1,z95,z3,z4,z5])],[(0,[z0,z208,z1,z2,z3,z4,z5]),(0,[z0,z1,z209,z2,z3,z4,z5]),(0,[z210,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z211,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z212]),(0,[z94,z1,z2,z3,z4,z46,z5]),(0,[z0,z1,z2,z3,z213,z4,z5]),(1,[z0,z1,z2,z4,z5,z214])],[(0,[z0,z1,z215,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z216,z4,z5]),(0,[z0,z1,z2,z3,z4,z217,z5]),(0,[z218,z1,z2,z3,z78,z4,z5])],[(0,[z219,z0,z1,z2,z3,z4,z5]),(0,[z150,z0,z1,z2,z196,z4,z5]),(0,[z0,z1,z2,z220,z3,z4,z5]),(0,[z221,z0,z1,z2,z3,z4,z5]),(0,[z222,z0,z2,z3,z4,z19,z5]),(0,[z96,z0,z1,z16,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z207,z5])],[(0,[z0,z1,z2,z3,z223,z4,z5]),(0,[z7,z0,z2,z3,z4,z19,z5]),(0,[z0,z1,z71,z2,z31,z4,z5]),(0,[z0,z1,z2,z224,z3,z4,z5]),(0,[z0,z1,z225,z2,z3,z4,z5])],[(0,[z0,z1,z226,z2,z3,z4,z5]),(0,[z0,z1,z227,z3,z4,z5,z135]),(0,[z0,z55,z139,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z228,z5])]],
   [[(0,[z229,z0,z1,z2,z3,z4,z5]),(0,[z230,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z231,z2,z3,z4,z5]),(0,[z0,z1,z2,z232,z3,z4,z5]),(0,[z0,z1,z2,z3,z233,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z234]),(0,[z0,z1,z235,z2,z3,z4,z5])],[(0,[z236,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z237,z4,z5]),(0,[z0,z1,z2,z3,z46,z19,z5]),(1,[z238,z1,z2,z3,z4,z5]),(0,[z239,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z126,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z240,z5])],[(0,[z241,z0,z1,z2,z3,z4,z5]),(0,[z0,z242,z1,z2,z3,z4,z5])],[(0,[z243,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z16,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z244,z5])],[(0,[z22,z1,z2,z13,z3,z4,z5]),(0,[z0,z1,z2,z3,z245,z4,z5]),(0,[z0,z1,z246,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z247,z4,z5]),(0,[z56,z0,z1,z2,z3,z5,z51])],[(0,[z0,z1,z2,z3,z248,z4,z5]),(0,[z0,z119,z55,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z249,z43])]],
   [[(0,[z118,z0,z2,z3,z4,z5,z92]),(0,[z0,z1,z2,z3,z4,z250,z46]),(0,[z0,z1,z2,z251,z3,z4,z5]),(0,[z0,z1,z2,z252,z3,z4,z5])],[(0,[z253,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z254,z3,z4,z5]),(0,[z0,z1,z2,z3,z255,z4,z5]),(1,[z256,z0,z1,z3,z4,z135]),(0,[z0,z1,z2,z3,z4,z5,z257]),(0,[z0,z1,z2,z3,z4,z258,z5])],[(0,[z0,z138,z139,z2,z3,z4,z5]),(0,[z259,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z260]),(0,[z0,z1,z261,z2,z3,z4,z5]),(0,[z0,z1,z2,z262,z3,z4,z5]),(0,[z0,z1,z263,z2,z3,z4,z5])],[(0,[z264,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z265,z2,z3,z4,z5]),(0,[z266,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z21,z183])],[(0,[z0,z1,z2,z267,z3,z4,z5]),(0,[z157,z0,z1,z20,z3,z4,z5]),(0,[z0,z1,z2,z268,z3,z4,z5]),(0,[z0,z1,z2,z269,z3,z4,z5]),(0,[z0,z1,z2,z25,z3,z4,z5]),(1,[z1,z2,z3,z4,z123,z5]),(0,[z56,z0,z1,z2,z3,z21,z5])],[(0,[z0,z1,z2,z3,z4,z5,z270]),(0,[z0,z1,z271,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z272,z4,z5]),(0,[z0,z1,z2,z186,z77,z4,z5])],[(0,[z0,z1,z2,z273,z3,z4,z5]),(0,[z0,z1,z2,z274,z3,z4,z5]),(0,[z0,z1,z2,z3,z275,z4,z5]),(1,[z164,z1,z2,z3,z276,z5]),(0,[z0,z1,z2,z277,z3,z4,z5]),(1,[z156,z0,z1,z2,z207,z5])],[(0,[z118,z0,z2,z3,z278,z4,z5]),(0,[z150,z0,z1,z2,z13,z4,z5]),(0,[z0,z1,z2,z3,z276,z4,z5]),(0,[z222,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z279,z4,z5]),(0,[z0,z1,z2,z3,z280,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z281,z5]),(0,[z70,z0,z1,z2,z223,z4,z5]),(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z282,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z249,z5]),(0,[z283,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z284,z2,z3,z4,z5])],[(0,[z285,z0,z1,z2,z3,z4,z5]),(0,[z286,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z46,z5]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z287,z5]),(0,[z288,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z249,z5,z214])],[(0,[z0,z1,z2,z3,z4,z289,z5]),(0,[z290,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z291,z3,z4,z258,z5])],[(0,[z0,z292,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z278,z4,z19,z5]),(0,[z0,z1,z2,z3,z293,z4,z5])],[(0,[z0,z1,z2,z3,z4,z249,z92]),(0,[z294,z0,z1,z2,z3,z4,z5])],[(0,[z142,z0,z1,z2,z3,z4,z5]),(1,[z94,z1,z95,z3,z4,z5]),(0,[z156,z150,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z295,z3,z4,z5]),(0,[z0,z1,z2,z296,z3,z4,z5]),(0,[z0,z206,z1,z2,z89,z4,z5]),(0,[z0,z297,z1,z2,z3,z4,z5])]],
   [[(0,[z22,z0,z119,z2,z3,z4,z5]),(0,[z298,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z299,z4,z5]),(0,[z300,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z186,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z301,z5]),(0,[z0,z55,z1,z2,z3,z278,z5]),(0,[z0,z1,z302,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z303]),(0,[z0,z1,z2,z3,z4,z5,z304]),(0,[z0,z305,z1,z2,z3,z4,z5])],[(0,[z306,z0,z1,z2,z3,z4,z5]),(0,[z0,z307,z1,z2,z3,z4,z5]),(0,[z308,z0,z1,z2,z3,z4,z5]),(0,[z0,z309,z1,z2,z3,z4,z5]),(1,[z0,z1,z153,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z310]),(0,[z0,z1,z2,z311,z3,z4,z5]),(0,[z312,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z313,z5]),(0,[z56,z0,z1,z2,z314,z4,z5])],[(0,[z79,z1,z2,z13,z3,z4,z5]),(0,[z238,z0,z1,z2,z3,z4,z5]),(0,[z0,z119,z1,z2,z3,z4,z43]),(0,[z0,z1,z315,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z316,z5]),(0,[z256,z0,z1,z20,z3,z4,z5])],[(0,[z56,z45,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z317,z4,z249,z5]),(0,[z318,z0,z1,z2,z3,z4,z5])],[(0,[z0,z138,z1,z227,z3,z4,z5]),(0,[z319,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z320,z3,z4,z5]),(0,[z0,z321,z1,z2,z3,z4,z5])],[(0,[z322,z0,z1,z2,z3,z4,z5]),(1,[z0,z2,z29,z3,z4,z5]),(0,[z164,z0,z1,z2,z3,z276,z5]),(0,[z164,z1,z2,z3,z276,z4,z5]),(1,[z218,z1,z2,z3,z4,z5]),(0,[z0,z1,z323,z2,z3,z4,z5])]],
   [[(0,[z157,z0,z1,z3,z4,z5,z135]),(0,[z324,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z325,z2,z3,z4,z5]),(0,[z8,z0,z1,z71,z3,z4,z5]),(0,[z0,z1,z2,z3,z17,z4,z5]),(0,[z156,z0,z1,z2,z3,z207,z5]),(0,[z0,z1,z2,z3,z4,z5,z326]),(0,[z102,z0,z1,z2,z186,z4,z5]),(0,[z0,z1,z2,z3,z327,z4,z5])],[(0,[z0,z1,z328,z2,z3,z4,z5]),(1,[z0,z10,z2,z3,z4,z5])],[(0,[z329,z0,z2,z158,z3,z4,z5]),(0,[z330,z0,z1,z2,z3,z4,z5]),(0,[z331,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z332,z4,z5]),(0,[z0,z1,z20,z2,z3,z4,z249]),(0,[z0,z1,z2,z3,z333,z4,z5])],[(0,[z99,z0,z1,z2,z89,z4,z5]),(0,[z0,z1,z334,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z78,z4,z5]),(0,[z0,z1,z2,z3,z335,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z336]),(0,[z0,z1,z2,z3,z337,z4,z5])],[(0,[z0,z119,z1,z2,z3,z4,z5]),(0,[z0,z1,z338,z2,z3,z4,z5]),(0,[z0,z339,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z340,z3,z4,z5]),(0,[z0,z1,z2,z341,z3,z4,z5]),(0,[z0,z1,z2,z3,z278,z276,z5]),(0,[z7,z0,z1,z2,z3,z4,z342]),(0,[z0,z343,z1,z2,z3,z4,z5]),(0,[z344,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z345,z5]),(0,[z346,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z347,z5]),(0,[z0,z1,z2,z77,z3,z78,z5])]],
   [[(0,[z94,z164,z1,z2,z3,z4,z5]),(0,[z0,z12,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z276,z4,z46,z5]),(0,[z348,z0,z1,z2,z3,z4,z5]),(0,[z349,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z17,z4,z161,z5])],[(0,[z0,z1,z2,z3,z350,z4,z5]),(0,[z0,z138,z1,z139,z3,z4,z5]),(0,[z351,z0,z1,z2,z3,z4,z5]),(0,[z352,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z16,z2,z3,z353,z5]),(0,[z0,z1,z2,z4,z258,z5,z103])],[(0,[z157,z0,z1,z2,z3,z4,z5]),(0,[z94,z0,z1,z158,z3,z4,z5]),(0,[z70,z0,z1,z2,z89,z4,z5]),(0,[z0,z1,z2,z3,z354,z4,z5]),(0,[z355,z0,z1,z2,z3,z4,z5]),(0,[z356,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z357]),(0,[z0,z1,z2,z3,z4,z358,z5])],[(0,[z150,z79,z1,z2,z3,z4,z5]),(0,[z0,z139,z2,z3,z4,z19,z5]),(0,[z0,z119,z1,z2,z3,z4,z92]),(0,[z0,z1,z2,z3,z4,z5,z359]),(1,[z96,z0,z1,z3,z353,z5]),(0,[z0,z1,z20,z3,z4,z249,z5])],[(1,[z0,z1,z2,z3,z4,z136]),(0,[z0,z134,z2,z3,z17,z4,z5])],[(0,[z1,z2,z158,z3,z4,z46,z5]),(1,[z0,z2,z3,z4,z84,z5]),(0,[z360,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z20,z3,z4,z249]),(0,[z0,z1,z2,z3,z361,z4,z5])],[(0,[z362,z0,z1,z2,z3,z4,z5]),(0,[z363,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z364,z5]),(0,[z0,z1,z2,z3,z4,z5,z365])],[(0,[z0,z1,z2,z366,z3,z4,z5]),(0,[z118,z0,z206,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z367]),(0,[z0,z1,z368,z2,z3,z4,z5]),(0,[z42,z0,z1,z2,z369,z4,z5]),(0,[z0,z1,z71,z2,z3,z4,z5]),(0,[z370,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z371,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z372]),(0,[z56,z0,z373,z2,z3,z4,z5])]],
   [[(0,[z0,z2,z3,z4,z84,z46,z5]),(0,[z0,z1,z374,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z375,z5]),(0,[z0,z1,z2,z3,z376,z4,z5]),(1,[z42,z0,z2,z3,z4,z92]),(0,[z0,z1,z2,z3,z4,z5,z377]),(0,[z256,z0,z1,z3,z4,z5,z135]),(1,[z0,z1,z3,z4,z5,z372])],[(0,[z0,z1,z2,z3,z378,z4,z5]),(0,[z0,z379,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z380]),(0,[z0,z1,z2,z3,z21,z183,z5])],[(0,[z0,z1,z95,z2,z3,z4,z5]),(0,[z381,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z227,z3,z4,z5]),(0,[z0,z1,z2,z3,z382,z4,z5]),(0,[z383,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z384,z2,z3,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z5]),(0,[z385,z0,z1,z2,z3,z4,z46]),(0,[z96,z0,z1,z3,z4,z353,z5])],[(0,[z386,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z317,z3,z4,z5])],[(0,[z96,z387,z1,z2,z3,z4,z5]),(0,[z96,z0,z1,z2,z3,z17,z5])],[(0,[z118,z0,z1,z2,z3,z4,z5]),(0,[z388,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z389,z2,z3,z4,z5]),(0,[z390,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z391]),(0,[z0,z1,z2,z3,z392,z4,z5]),(0,[z156,z0,z1,z2,z4,z207,z5]),(0,[z0,z1,z2,z3,z4,z5,z393])],[(0,[z0,z1,z2,z394,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z395,z5]),(0,[z0,z1,z396,z2,z3,z4,z5]),(0,[z397,z0,z1,z2,z3,z4,z5]),(0,[z70,z0,z1,z2,z4,z5,z103]),(0,[z398,z0,z1,z2,z3,z276,z5]),(0,[z0,z1,z2,z3,z4,z5,z399])],[(0,[z0,z1,z400,z2,z3,z4,z5]),(0,[z401,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z4,z87,z5]),(1,[z8,z0,z1,z34,z4,z5]),(0,[z0,z1,z2,z78,z4,z207,z5])],[(0,[z0,z1,z402,z2,z3,z4,z5]),(0,[z45,z0,z1,z2,z3,z4,z98]),(0,[z0,z1,z2,z3,z4,z5,z403]),(0,[z404,z0,z1,z2,z3,z4,z5]),(0,[z256,z0,z1,z2,z3,z4,z5]),(0,[z405,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z406]),(0,[z0,z407,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z23,z5]),(0,[z408,z0,z1,z2,z3,z4,z5]),(0,[z398,z1,z2,z3,z4,z46,z5]),(0,[z0,z1,z2,z409,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z410,z5])],[(0,[z150,z0,z1,z71,z2,z4,z5]),(0,[z0,z1,z2,z411,z3,z4,z5])],[(0,[z412,z0,z1,z2,z3,z4,z5]),(0,[z0,z413,z1,z2,z3,z4,z5]),(1,[z0,z1,z411,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z414,z5]),(0,[z0,z1,z16,z3,z4,z5,z135])],[(0,[z415,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z416,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z417]),(0,[z0,z1,z2,z186,z4,z207,z5]),(0,[z56,z305,z1,z2,z3,z4,z5])],[(0,[z0,z1,z139,z3,z4,z5,z135]),(0,[z0,z1,z2,z369,z3,z4,z5])],[(0,[z22,z0,z1,z2,z3,z418,z5]),(0,[z118,z0,z80,z2,z3,z4,z5]),(0,[z0,z419,z1,z2,z3,z4,z5])],[(0,[z22,z7,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z420,z5])],[(0,[z22,z0,z2,z3,z4,z5,z92]),(1,[z0,z1,z2,z3,z4,z342]),(0,[z0,z1,z2,z3,z421,z4,z5]),(0,[z0,z1,z2,z422,z3,z4,z5]),(0,[z423,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z424,z3,z4,z5])],[(0,[z0,z1,z2,z3,z425,z4,z5]),(0,[z0,z1,z2,z3,z4,z426,z5]),(0,[z1,z2,z13,z3,z223,z4,z5]),(0,[z0,z1,z2,z3,z4,z427,z5]),(0,[z0,z1,z2,z89,z34,z4,z5]),(1,[z0,z1,z3,z421,z4,z5]),(0,[z0,z1,z20,z2,z3,z4,z135]),(0,[z428,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z429,z4,z5])],[(1,[z0,z1,z2,z4,z5,z30]),(0,[z430,z0,z1,z2,z3,z4,z5]),(0,[z8,z0,z1,z2,z34,z4,z5]),(0,[z0,z1,z20,z16,z3,z4,z5]),(0,[z0,z1,z2,z431,z3,z4,z5]),(0,[z156,z0,z1,z2,z77,z4,z5]),(0,[z0,z1,z373,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z183,z5,z51])],[(0,[z0,z1,z2,z3,z432,z4,z5]),(1,[z7,z0,z227,z3,z4,z5]),(0,[z0,z1,z2,z3,z433,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z434,z5]),(0,[z0,z1,z2,z3,z4,z435,z5])],[(0,[z0,z1,z2,z436,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z437,z5]),(0,[z0,z1,z2,z3,z4,z5,z438]),(1,[z0,z1,z2,z314,z4,z5])],[(0,[z48,z0,z1,z2,z3,z4,z98]),(0,[z0,z1,z439,z2,z3,z4,z5]),(1,[z0,z1,z2,z369,z4,z5]),(1,[z105,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z440])],[(0,[z22,z0,z2,z3,z278,z4,z5]),(0,[z70,z0,z1,z2,z186,z4,z5]),(0,[z0,z1,z139,z2,z3,z4,z5]),(0,[z0,z206,z55,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z441,z5])],[(0,[z22,z150,z1,z2,z3,z4,z5]),(0,[z45,z0,z1,z2,z3,z4,z5]),(1,[z222,z0,z2,z3,z19,z5]),(0,[z0,z1,z2,z186,z4,z258,z5])],[(0,[z94,z0,z1,z95,z3,z4,z5]),(0,[z0,z1,z20,z227,z3,z4,z5]),(0,[z0,z1,z2,z31,z89,z4,z5]),(0,[z0,z1,z2,z442,z3,z4,z5])],[(0,[z443,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z444])],[(0,[z0,z1,z2,z3,z4,z445,z5]),(0,[z446,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z447])]],
   [[(0,[z0,z1,z2,z3,z4,z418,z5]),(0,[z0,z1,z2,z3,z4,z448,z5]),(0,[z0,z1,z2,z3,z449,z4,z5]),(0,[z0,z1,z450,z2,z3,z4,z5]),(0,[z451,z0,z1,z2,z3,z4,z5]),(0,[z0,z452,z2,z3,z4,z98,z5]),(0,[z0,z1,z2,z3,z4,z453,z5]),(0,[z0,z1,z2,z3,z4,z5,z454]),(0,[z0,z455,z1,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z4,z5,z103])],[(0,[z150,z1,z2,z3,z223,z4,z5]),(0,[z0,z1,z2,z3,z276,z19,z5]),(0,[z7,z0,z1,z2,z3,z4,z136]),(0,[z0,z1,z2,z3,z456,z4,z5]),(0,[z0,z1,z457,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z458,z4,z5]),(0,[z222,z0,z1,z2,z3,z19,z5]),(0,[z0,z1,z2,z3,z459,z4,z5])],[(0,[z460,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z461,z4,z5]),(0,[z0,z1,z3,z17,z4,z353,z5]),(0,[z0,z1,z462,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z463,z4,z5])],[(0,[z464,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z158,z3,z4,z5]),(0,[z70,z1,z2,z13,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z465]),(0,[z466,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z467,z4,z5]),(0,[z0,z1,z2,z3,z4,z468,z5]),(0,[z469,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z470,z5])],[(0,[z471,z0,z1,z2,z3,z4,z5]),(0,[z387,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z317,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z472]),(0,[z0,z119,z2,z3,z4,z19,z5]),(0,[z0,z1,z31,z3,z4,z5,z135])],[(0,[z0,z206,z2,z3,z4,z19,z5]),(0,[z0,z1,z2,z3,z4,z92,z135]),(0,[z256,z0,z1,z2,z3,z4,z249])]],
   [[(0,[z473,z0,z1,z2,z3,z4,z5]),(0,[z474,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z1,z227,z3,z4,z5]),(0,[z0,z1,z20,z139,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z475,z5])],[(0,[z0,z1,z2,z3,z4,z5,z476]),(0,[z0,z1,z2,z3,z4,z477,z5])],[(0,[z1,z2,z13,z3,z4,z46,z5]),(0,[z48,z45,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z478]),(0,[z0,z55,z2,z3,z4,z5,z92])],[(0,[z0,z1,z2,z3,z4,z5,z479]),(0,[z238,z1,z2,z3,z89,z4,z5]),(0,[z480,z0,z1,z2,z3,z4,z5])],[(1,[z0,z12,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z481,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z482]),(0,[z48,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z483,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z484]),(0,[z0,z1,z2,z3,z4,z485,z5]),(0,[z0,z1,z2,z3,z486,z4,z5]),(0,[z487,z0,z1,z2,z3,z4,z5])],[(0,[z488,z0,z1,z2,z3,z4,z5]),(1,[z0,z55,z2,z3,z278,z5]),(1,[z0,z373,z2,z3,z4,z5]),(0,[z56,z0,z1,z2,z424,z4,z5])],[(0,[z42,z0,z1,z368,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z489,z5]),(0,[z0,z1,z2,z3,z490,z4,z5])]],
   [[(0,[z157,z0,z1,z3,z17,z4,z5]),(0,[z329,z0,z1,z2,z3,z4,z5]),(0,[z94,z0,z1,z20,z3,z4,z5]),(0,[z0,z1,z2,z491,z3,z4,z5]),(0,[z492,z0,z1,z2,z3,z4,z5]),(0,[z56,z0,z117,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z493,z5]),(0,[z0,z1,z2,z494,z3,z4,z5]),(0,[z0,z55,z2,z3,z278,z4,z5]),(0,[z0,z1,z2,z3,z4,z353,z5])],[(0,[z495,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z496,z5]),(0,[z497,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z498]),(0,[z0,z1,z2,z3,z4,z499,z5])],[(0,[z0,z2,z29,z158,z3,z4,z5]),(0,[z0,z1,z2,z500,z3,z4,z5]),(0,[z501,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z98,z5,z192]),(0,[z0,z1,z2,z89,z4,z5,z103]),(0,[z0,z1,z2,z502,z3,z4,z5]),(0,[z0,z1,z2,z3,z503,z4,z5]),(0,[z0,z1,z3,z4,z258,z5,z372])],[(0,[z504,z0,z1,z2,z3,z4,z5]),(0,[z505,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z506,z4,z5]),(0,[z8,z0,z1,z2,z4,z5,z103]),(1,[z387,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z507]),(0,[z0,z1,z2,z3,z4,z43,z5]),(0,[z0,z1,z2,z3,z4,z508,z5]),(0,[z0,z509,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z510])],[(1,[z451,z0,z1,z3,z4,z5]),(0,[z0,z2,z196,z3,z89,z4,z5]),(0,[z42,z0,z1,z411,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z511,z5])],[(0,[z0,z1,z2,z512,z3,z4,z5]),(0,[z0,z1,z2,z3,z513,z4,z5]),(0,[z0,z1,z2,z3,z4,z514,z5]),(0,[z0,z515,z1,z2,z3,z4,z5])]],
   [[(1,[z118,z79,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z516,z4,z5]),(0,[z517,z0,z1,z2,z3,z4,z5])],[(0,[z1,z95,z2,z158,z3,z4,z5]),(0,[z0,z1,z2,z3,z518,z4,z5]),(0,[z398,z164,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z46,z5,z6]),(0,[z519,z0,z1,z2,z3,z4,z5]),(0,[z0,z206,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z520,z5]),(0,[z156,z0,z521,z2,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z4,z258])],[(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z522,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z186,z3,z4,z5])],[(1,[z22,z80,z2,z3,z4,z5]),(0,[z22,z0,z206,z2,z3,z4,z5]),(1,[z0,z1,z2,z523,z4,z5]),(0,[z45,z1,z2,z3,z4,z98,z5]),(0,[z524,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z525,z5]),(0,[z0,z1,z2,z526,z3,z4,z5])],[(0,[z118,z0,z79,z2,z3,z4,z5]),(1,[z70,z1,z2,z13,z4,z5]),(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z0,z527,z1,z2,z3,z4,z5]),(0,[z528,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z13,z3,z4,z5])],[(0,[z222,z118,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z120,z4,z5]),(0,[z0,z1,z2,z523,z158,z4,z5]),(0,[z529,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z2,z227,z3,z4,z5]),(0,[z99,z0,z206,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z530,z5]),(1,[z305,z1,z2,z3,z4,z5])],[(0,[z7,z118,z0,z2,z3,z4,z5]),(0,[z0,z531,z1,z2,z3,z4,z5]),(0,[z0,z452,z1,z2,z3,z4,z5]),(0,[z218,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z532])],[(0,[z0,z533,z1,z2,z3,z4,z5]),(0,[z7,z0,z138,z2,z3,z4,z5])],[(0,[z22,z0,z1,z2,z3,z4,z5]),(0,[z534,z0,z1,z2,z3,z4,z5])],[(0,[z0,z535,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z536,z3,z4,z5]),(0,[z537,z0,z1,z2,z3,z4,z5])],[(0,[z150,z8,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z538,z5]),(0,[z99,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z71,z31,z4,z5])],[(0,[z22,z118,z1,z2,z3,z4,z5]),(0,[z45,z0,z1,z2,z3,z21,z4]),(0,[z0,z1,z2,z3,z4,z539,z5]),(0,[z0,z1,z2,z540,z3,z4,z5]),(0,[z42,z0,z119,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z541])],[(0,[z542,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z98,z5,z543]),(0,[z8,z0,z1,z2,z186,z4,z5])]],
   [[(0,[z544,z0,z1,z2,z3,z4,z5]),(0,[z118,z79,z1,z2,z3,z4,z5]),(0,[z70,z0,z1,z2,z78,z4,z5])],[(0,[z0,z1,z2,z3,z4,z545,z5]),(1,[z0,z1,z368,z3,z4,z5]),(0,[z0,z1,z2,z3,z546,z4,z5]),(0,[z56,z266,z1,z2,z3,z4,z5])],[(0,[z118,z0,z2,z3,z89,z4,z5]),(0,[z547,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z548,z5]),(0,[z256,z0,z1,z2,z3,z4,z135]),(0,[z0,z1,z2,z3,z4,z5,z214])],[(0,[z549,z0,z1,z2,z3,z4,z5]),(0,[z550,z0,z1,z2,z3,z4,z5])],[(0,[z164,z0,z1,z2,z3,z46,z5]),(0,[z0,z1,z2,z3,z4,z5,z551]),(0,[z0,z1,z2,z3,z552,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z553]),(0,[z0,z554,z1,z2,z3,z4,z5]),(0,[z0,z1,z20,z3,z4,z353,z5])],[(0,[z150,z0,z1,z2,z223,z4,z5]),(0,[z164,z1,z2,z13,z3,z4,z5]),(0,[z0,z206,z1,z2,z196,z4,z5]),(0,[z0,z1,z2,z3,z4,z555,z5]),(0,[z0,z556,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z557])],[(0,[z22,z0,z80,z2,z3,z4,z5]),(0,[z94,z0,z1,z2,z3,z4,z5]),(0,[z558,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z559,z4,z5]),(0,[z0,z1,z2,z186,z196,z4,z5]),(0,[z560,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z561,z4,z5]),(0,[z0,z1,z16,z3,z17,z4,z5])],[(0,[z562,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z563,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z564]),(0,[z565,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z566,z2,z3,z4,z5]),(0,[z0,z567,z1,z2,z3,z4,z5])],[(0,[z568,z0,z1,z2,z3,z4,z5]),(0,[z569,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z254,z4,z5]),(0,[z570,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z571,z4,z5]),(0,[z0,z1,z2,z186,z3,z4,z258])],[(0,[z0,z1,z2,z3,z278,z46,z5]),(0,[z0,z1,z2,z3,z572,z4,z5])],[(0,[z0,z79,z1,z2,z573,z4,z5]),(0,[z0,z2,z3,z4,z19,z5,z92]),(0,[z42,z0,z1,z2,z114,z4,z5])],[(1,[z48,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z314,z4,z5]),(0,[z574,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z575,z5]),(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z576,z0,z1,z2,z3,z4,z5])],[(0,[z157,z94,z1,z2,z3,z4,z5]),(0,[z150,z70,z1,z2,z3,z4,z5]),(0,[z0,z577,z1,z2,z3,z4,z5]),(0,[z0,z1,z578,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z579,z4,z5]),(0,[z0,z2,z13,z3,z449,z4,z5]),(0,[z0,z1,z2,z580,z3,z4,z5]),(0,[z0,z55,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z581,z5]),(1,[z0,z119,z2,z3,z4,z43])],[(0,[z99,z0,z1,z2,z196,z4,z5]),(0,[z0,z55,z2,z3,z89,z4,z5]),(0,[z0,z1,z2,z3,z582,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z583])],[(0,[z584,z0,z1,z2,z3,z4,z5]),(0,[z585,z0,z1,z2,z3,z4,z5]),(0,[z0,z206,z2,z196,z3,z4,z5]),(0,[z8,z0,z1,z20,z3,z4,z5]),(0,[z0,z1,z71,z2,z34,z4,z5]),(0,[z0,z1,z2,z3,z4,z586,z5])],[(0,[z0,z587,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z588,z4,z5]),(0,[z0,z138,z1,z31,z3,z4,z5]),(0,[z0,z1,z2,z3,z589,z4,z5]),(0,[z0,z1,z2,z3,z4,z590,z5]),(0,[z591,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z424,z4,z5])],[(0,[z592,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z593,z3,z4,z5])],[(0,[z594,z0,z1,z2,z3,z4,z5]),(1,[z385,z0,z1,z2,z3,z4]),(1,[z0,z1,z2,z3,z4,z250]),(0,[z1,z2,z3,z456,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z595]),(0,[z0,z1,z2,z3,z4,z5,z596]),(0,[z0,z1,z2,z3,z4,z161,z5])],[(0,[z597,z0,z1,z2,z3,z4,z5]),(0,[z598,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z272,z4,z5]),(0,[z599,z0,z1,z2,z3,z4,z5]),(0,[z127,z0,z1,z2,z3,z4,z5]),(0,[z600,z0,z1,z2,z3,z4,z5]),(1,[z0,z117,z2,z3,z4,z5]),(0,[z56,z0,z1,z2,z3,z4,z183])],[(0,[z0,z1,z2,z523,z3,z4,z5]),(1,[z398,z1,z2,z3,z46,z5]),(1,[z0,z1,z2,z186,z4,z258])]],
   [[(0,[z70,z0,z1,z2,z196,z4,z5]),(0,[z601,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z602]),(0,[z0,z1,z2,z603,z3,z4,z5])],[(0,[z22,z222,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z604,z5]),(0,[z0,z605,z1,z2,z3,z4,z5])],[(1,[z0,z452,z2,z3,z4,z5])],[(0,[z157,z0,z1,z158,z3,z4,z5]),(0,[z150,z164,z1,z2,z3,z4,z5]),(0,[z0,z138,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z606,z3,z4,z5]),(0,[z0,z1,z2,z196,z34,z4,z5]),(0,[z0,z1,z2,z607,z3,z4,z5]),(0,[z0,z1,z2,z3,z21,z4,z183])],[(0,[z0,z1,z2,z573,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z250,z5]),(0,[z102,z0,z1,z2,z3,z4,z5]),(0,[z0,z608,z1,z2,z3,z4,z5])],[(0,[z96,z157,z0,z1,z3,z4,z5]),(0,[z398,z0,z1,z2,z3,z46,z5]),(0,[z0,z1,z2,z3,z4,z609,z5]),(0,[z0,z1,z2,z610,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z611,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z612,z0,z1,z2,z3,z4,z5]),(0,[z613,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z614,z5]),(0,[z0,z1,z2,z3,z4,z5,z615]),(0,[z156,z0,z10,z2,z3,z4,z5])],[(0,[z0,z1,z2,z616,z3,z4,z5]),(1,[z0,z1,z2,z573,z4,z5]),(0,[z150,z0,z1,z2,z89,z4,z5]),(0,[z0,z617,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z618,z4,z5]),(0,[z0,z1,z2,z254,z4,z98,z5]),(1,[z0,z1,z291,z3,z4,z5])]],
   [[(1,[z329,z0,z2,z3,z4,z5]),(0,[z619,z0,z1,z2,z3,z4,z5]),(0,[z156,z70,z0,z1,z2,z4,z5])],[(0,[z56,z48,z0,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z98,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z192]),(0,[z620,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z621]),(0,[z0,z1,z2,z3,z622,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z543]),(0,[z0,z1,z2,z3,z4,z5,z623]),(0,[z0,z1,z2,z3,z4,z624,z5]),(0,[z0,z1,z521,z2,z3,z4,z5])],[(1,[z0,z1,z3,z4,z5,z543]),(0,[z0,z139,z2,z227,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z625,z5])],[(0,[z0,z1,z626,z2,z3,z4,z5]),(1,[z150,z1,z2,z223,z4,z5]),(0,[z0,z1,z2,z3,z4,z627,z5]),(0,[z0,z628,z1,z2,z3,z4,z5])],[(0,[z629,z0,z1,z2,z3,z4,z5]),(0,[z630,z0,z1,z2,z3,z4,z5]),(0,[z96,z0,z1,z2,z3,z353,z5]),(0,[z0,z1,z2,z77,z78,z4,z5])],[(0,[z0,z1,z631,z2,z3,z4,z5])],[(0,[z0,z1,z632,z2,z3,z4,z5]),(0,[z0,z633,z1,z2,z3,z4,z5]),(0,[z222,z0,z1,z2,z3,z278,z5]),(1,[z0,z1,z2,z114,z4,z5]),(0,[z634,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z635,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z636,z5]),(0,[z0,z1,z2,z3,z637,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z2,z638,z3,z4,z5]),(0,[z0,z1,z2,z77,z4,z5,z103])],[(0,[z639,z0,z1,z2,z3,z4,z5])],[(0,[z70,z0,z1,z2,z13,z4,z5]),(0,[z0,z1,z2,z640,z3,z4,z5]),(0,[z0,z1,z2,z3,z641,z4,z5])],[(0,[z0,z2,z3,z4,z43,z5,z92]),(0,[z156,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z77,z3,z207,z5])],[(0,[z150,z0,z1,z2,z4,z5,z103]),(0,[z0,z1,z2,z3,z4,z5,z642]),(0,[z0,z1,z2,z3,z4,z43,z135]),(1,[z0,z134,z2,z3,z4,z5])],[(0,[z643,z0,z1,z2,z3,z4,z5]),(0,[z164,z1,z2,z158,z3,z4,z5]),(0,[z7,z0,z1,z139,z3,z4,z5]),(1,[z1,z2,z3,z456,z4,z5]),(0,[z644,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z645,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z92]),(0,[z0,z1,z2,z3,z4,z5,z646]),(0,[z0,z1,z2,z3,z647,z4,z5])],[(0,[z0,z1,z2,z3,z4,z648,z5]),(0,[z0,z1,z2,z3,z649,z4,z5]),(0,[z0,z1,z2,z3,z650,z4,z5]),(0,[z0,z1,z651,z2,z3,z4,z5]),(1,[z266,z1,z2,z3,z4,z5])]],
   [[(0,[z22,z0,z79,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z652]),(0,[z653,z0,z1,z2,z3,z4,z5]),(0,[z8,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z71,z2,z4,z5,z103]),(0,[z654,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z655,z3,z4,z5]),(0,[z150,z1,z2,z3,z4,z46,z5]),(0,[z0,z1,z126,z3,z4,z98,z5]),(0,[z0,z1,z2,z3,z656,z4,z5]),(0,[z657,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z658])],[(0,[z0,z1,z2,z659,z3,z4,z5]),(1,[z0,z2,z3,z449,z4,z5]),(0,[z660,z0,z1,z2,z3,z4,z5]),(0,[z661,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z662,z5]),(0,[z0,z1,z3,z4,z249,z5,z135])],[(0,[z0,z1,z2,z3,z4,z5,z663])],[(0,[z0,z1,z2,z3,z4,z5,z664]),(1,[z132,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z665,z3,z4,z5]),(0,[z0,z1,z2,z666,z3,z4,z5]),(0,[z0,z1,z2,z667,z3,z4,z5])],[(0,[z118,z0,z139,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z278,z4,z5]),(0,[z0,z1,z2,z3,z668,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z669]),(0,[z0,z1,z2,z3,z4,z5,z670])],[(0,[z0,z1,z671,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z672,z5]),(0,[z222,z0,z55,z2,z3,z4,z5]),(0,[z673,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z674,z3,z4,z5]),(0,[z7,z0,z55,z2,z3,z4,z5]),(0,[z8,z0,z138,z1,z3,z4,z5]),(0,[z0,z1,z3,z421,z89,z4,z5]),(0,[z675,z0,z1,z2,z3,z4,z5])]],
   [[],[(0,[z0,z1,z2,z3,z4,z676,z5]),(0,[z0,z1,z2,z3,z4,z342,z5]),(0,[z0,z1,z2,z196,z4,z5,z103]),(1,[z0,z521,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z677,z5])],[(1,[z157,z1,z158,z3,z4,z5]),(0,[z678,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z291,z2,z3,z4,z5])],[(0,[z0,z1,z679,z2,z3,z4,z5]),(0,[z7,z0,z1,z2,z272,z4,z5]),(0,[z0,z1,z2,z31,z196,z4,z5]),(0,[z680,z0,z1,z2,z3,z4,z5])],[(0,[z681,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z98,z5,z30]),(0,[z682,z0,z1,z2,z3,z4,z5]),(0,[z683,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z684,z2,z3,z4,z5]),(0,[z27,z0,z2,z3,z4,z46,z5]),(0,[z0,z1,z685,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z686,z5]),(0,[z22,z0,z2,z3,z89,z4,z5]),(0,[z687,z0,z1,z2,z3,z4,z5]),(0,[z0,z119,z2,z3,z4,z43,z5])],[(0,[z94,z0,z1,z3,z4,z5,z135]),(0,[z0,z688,z1,z2,z3,z4,z5]),(0,[z689,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z123,z5])]],
   [[(0,[z150,z0,z1,z2,z186,z4,z5]),(0,[z0,z1,z2,z3,z4,z87,z5]),(0,[z0,z1,z2,z3,z4,z690,z5])],[(0,[z99,z0,z2,z3,z89,z4,z5]),(0,[z691,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z692,z3,z4,z5]),(0,[z693,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z694,z2,z3,z4,z5]),(0,[z695,z0,z1,z2,z3,z4,z5]),(0,[z8,z0,z1,z2,z31,z4,z5]),(0,[z0,z1,z20,z31,z3,z4,z5])],[(1,[z0,z1,z2,z3,z418,z5]),(0,[z0,z1,z2,z696,z3,z4,z5]),(0,[z0,z1,z71,z2,z186,z4,z5])],[(0,[z22,z1,z80,z2,z3,z4,z5]),(0,[z697,z0,z1,z2,z3,z4,z5]),(0,[z698,z0,z1,z2,z3,z4,z5]),(0,[z451,z0,z1,z3,z4,z46,z5]),(0,[z127,z0,z1,z3,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z699]),(0,[z96,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z353,z5,z135]),(0,[z0,z1,z2,z3,z4,z5,z700])],[(0,[z701,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z702]),(0,[z703,z0,z1,z2,z3,z4,z5]),(0,[z56,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z704])],[(0,[z0,z1,z2,z705,z3,z4,z5])],[(0,[z70,z0,z1,z2,z3,z4,z5]),(0,[z398,z0,z1,z2,z3,z4,z5]),(0,[z385,z0,z1,z2,z3,z4,z5]),(0,[z48,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z706,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z22,z2,z3,z456,z4,z5]),(0,[z22,z457,z2,z3,z4,z5]),(0,[z0,z1,z2,z78,z538,z5]),(0,[z8,z0,z1,z3,z4,z136])],[(0,[z0,z1,z2,z3,z707,z5]),(0,[z70,z12,z2,z13,z4,z5]),(0,[z7,z0,z708,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z709])],[(0,[z0,z1,z3,z4,z5,z543]),(0,[z0,z1,z2,z710,z4,z5]),(0,[z0,z1,z3,z4,z5,z711])],[(0,[z0,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z4,z713,z6]),(0,[z714,z1,z2,z3,z4,z5])],[(0,[z0,z1,z3,z4,z715,z5]),(0,[z0,z455,z139,z3,z4,z5])],[(0,[z0,z1,z3,z716,z4,z5])],[(0,[z0,z1,z2,z4,z717,z5]),(0,[z0,z1,z9,z3,z4,z249]),(0,[z0,z2,z3,z4,z718,z5]),(0,[z634,z0,z1,z2,z4,z103])],[(0,[z142,z0,z1,z2,z4,z5]),(0,[z0,z55,z2,z3,z113,z5]),(0,[z1,z2,z3,z719,z4,z5]),(0,[z0,z1,z720,z3,z4,z5]),(0,[z721,z105,z1,z2,z4,z5]),(0,[z156,z0,z521,z2,z207,z5])]],
   [[(0,[z0,z722,z2,z3,z4,z5]),(0,[z164,z1,z2,z3,z723,z5]),(0,[z42,z0,z2,z114,z4,z92])],[(0,[z22,z145,z2,z3,z4,z5]),(0,[z724,z1,z2,z3,z4,z5]),(0,[z0,z16,z3,z17,z161,z5]),(0,[z0,z134,z16,z3,z17,z5]),(0,[z0,z1,z2,z3,z4,z725])],[(1,[z1,z726,z3,z4,z5]),(0,[z0,z727,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z728]),(0,[z398,z1,z2,z87,z46,z5]),(0,[z0,z126,z3,z4,z5,z192]),(0,[z0,z1,z2,z272,z4,z342]),(1,[z0,z708,z3,z4,z5]),(0,[z0,z2,z3,z4,z161,z5]),(0,[z238,z127,z1,z3,z4,z5]),(0,[z96,z0,z1,z3,z729,z5])],[(0,[z0,z730,z2,z3,z4,z5]),(0,[z8,z0,z1,z340,z4,z5]),(0,[z164,z1,z2,z3,z181,z5]),(0,[z0,z134,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z731])],[(0,[z22,z127,z0,z3,z4,z5]),(0,[z732,z1,z2,z3,z4,z5]),(0,[z0,z1,z71,z4,z5,z670])],[(0,[z0,z139,z366,z3,z4,z5]),(0,[z266,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z733,z4,z5]),(0,[z0,z1,z2,z78,z734,z5])],[(0,[z0,z1,z2,z3,z4,z735]),(0,[z736,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z4,z5,z737]),(0,[z99,z0,z2,z738,z4,z5])]],
   [[(0,[z79,z2,z3,z449,z4,z5]),(0,[z451,z0,z3,z4,z84,z5]),(0,[z0,z739,z2,z3,z4,z5]),(0,[z0,z117,z2,z314,z4,z5])],[(0,[z740,z0,z1,z3,z4,z5]),(0,[z27,z0,z3,z4,z72,z5]),(0,[z0,z452,z2,z4,z5,z30])],[(0,[z149,z1,z2,z3,z46,z5]),(0,[z0,z2,z4,z87,z84,z5]),(0,[z0,z1,z31,z382,z4,z5]),(0,[z0,z1,z2,z3,z734,z5])],[(0,[z157,z329,z158,z3,z4,z5]),(0,[z150,z1,z2,z456,z4,z5]),(0,[z0,z1,z2,z3,z4,z741]),(0,[z0,z106,z2,z196,z4,z5]),(0,[z742,z0,z2,z3,z4,z5])],[(1,[z743,z2,z3,z4,z5]),(0,[z0,z744,z2,z3,z4,z5]),(0,[z0,z1,z745,z3,z4,z5]),(0,[z127,z0,z1,z31,z4,z5]),(0,[z746,z1,z2,z3,z4,z5])],[(0,[z0,z747,z2,z3,z4,z5]),(0,[z385,z305,z1,z2,z3,z4]),(0,[z45,z1,z3,z4,z98,z543]),(0,[z102,z0,z1,z2,z4,z103])],[(0,[z0,z1,z2,z3,z748,z5]),(0,[z22,z150,z2,z89,z4,z5]),(0,[z45,z305,z1,z2,z3,z4]),(0,[z0,z1,z411,z114,z4,z5])],[(0,[z0,z2,z3,z4,z5,z192]),(0,[z118,z2,z3,z4,z609,z5]),(0,[z1,z2,z749,z223,z4,z5])]],
   [[(0,[z0,z1,z2,z750,z4,z5]),(0,[z385,z0,z1,z2,z4,z87]),(0,[z0,z2,z3,z4,z5,z751]),(0,[z0,z521,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z249,z752])],[(0,[z753,z0,z1,z2,z3,z5]),(0,[z754,z0,z2,z3,z4,z5])],[(0,[z755,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z758,z0,z1,z3,z4,z5]),(0,[z0,z1,z759,z3,z4,z5]),(0,[z8,z0,z1,z571,z4,z5]),(0,[z0,z1,z2,z4,z760,z103])],[(0,[z0,z2,z3,z4,z5,z731]),(0,[z0,z1,z3,z761,z4,z5])],[(0,[z118,z2,z3,z4,z5,z623]),(0,[z0,z1,z3,z17,z289,z5]),(0,[z0,z762,z2,z3,z4,z5]),(0,[z0,z1,z2,z763,z4,z5]),(0,[z0,z206,z2,z196,z4,z5]),(0,[z0,z1,z764,z3,z4,z5]),(0,[z0,z765,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z766]),(0,[z0,z2,z3,z4,z731,z92])],[(0,[z767,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z734,z207,z5])],[(0,[z22,z0,z2,z3,z4,z136]),(0,[z416,z0,z1,z3,z4,z135]),(0,[z768,z0,z1,z2,z4,z5])]],
   [[(0,[z0,z1,z2,z769,z4,z5]),(0,[z0,z1,z770,z3,z4,z5]),(0,[z0,z1,z2,z3,z771,z5])],[(0,[z0,z1,z4,z5,z543,z30])],[(0,[z0,z1,z2,z3,z418,z5]),(0,[z0,z772,z2,z3,z4,z5]),(0,[z773,z1,z2,z3,z4,z5]),(0,[z774,z1,z2,z3,z4,z5])],[(0,[z0,z2,z3,z89,z418,z5]),(0,[z775,z1,z2,z3,z4,z5]),(0,[z673,z0,z1,z2,z207,z5]),(0,[z776,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z777]),(0,[z70,z1,z2,z749,z4,z5]),(0,[z99,z0,z421,z89,z4,z5]),(0,[z0,z1,z2,z3,z778,z5]),(0,[z0,z1,z2,z779,z4,z5])],[(0,[z0,z1,z2,z3,z780,z5]),(0,[z0,z1,z3,z17,z729,z5])],[(0,[z0,z2,z781,z3,z4,z5])],[(0,[z0,z1,z782,z3,z4,z5]),(0,[z0,z1,z2,z4,z217,z103])]],
   [[],[(0,[z0,z1,z2,z783,z4,z5]),(0,[z0,z1,z139,z3,z4,z136]),(0,[z218,z1,z2,z77,z78,z5]),(0,[z266,z1,z2,z314,z4,z5])],[(0,[z0,z1,z784,z3,z4,z5]),(0,[z0,z1,z2,z3,z785,z5]),(0,[z0,z1,z2,z25,z4,z5]),(0,[z99,z127,z0,z89,z4,z5]),(0,[z0,z1,z2,z786,z4,z5])],[(0,[z27,z0,z2,z3,z4,z5]),(0,[z0,z3,z4,z72,z84,z5]),(0,[z0,z1,z2,z4,z5,z787])],[(0,[z743,z80,z2,z3,z4,z5]),(0,[z0,z1,z788,z3,z4,z5]),(0,[z398,z1,z2,z3,z723,z5]),(0,[z451,z0,z1,z3,z4,z250]),(0,[z0,z1,z2,z789,z4,z5]),(0,[z790,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z791,z4,z5]),(0,[z0,z1,z792,z3,z4,z5])],[(0,[z398,z27,z2,z3,z46,z5]),(0,[z102,z0,z1,z2,z4,z760])],[(0,[z0,z1,z2,z793,z4,z5]),(0,[z0,z1,z794,z3,z4,z5])],[(0,[z2,z3,z456,z449,z4,z5]),(0,[z0,z1,z2,z3,z21,z427]),(0,[z0,z1,z2,z3,z4,z795])]],
   [[(0,[z150,z1,z2,z120,z4,z5]),(0,[z0,z1,z3,z4,z426,z135]),(0,[z0,z1,z708,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z796]),(0,[z0,z1,z16,z3,z729,z5]),(1,[z0,z1,z3,z4,z752])],[(0,[z70,z0,z2,z449,z4,z5]),(0,[z127,z70,z0,z1,z4,z5])],[(0,[z1,z726,z158,z3,z4,z5]),(0,[z164,z1,z2,z3,z276,z5]),(0,[z0,z55,z2,z3,z4,z136]),(0,[z797,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z798,z4,z5]),(0,[z0,z799,z2,z3,z4,z5])],[(0,[z1,z2,z13,z4,z87,z5]),(0,[z0,z2,z3,z778,z19,z5])],[(0,[z0,z1,z800,z3,z4,z5]),(0,[z451,z1,z158,z3,z4,z5]),(0,[z801,z1,z2,z3,z4,z5]),(0,[z0,z802,z2,z3,z4,z5]),(0,[z305,z117,z2,z3,z4,z5])],[(0,[z22,z578,z2,z3,z4,z5]),(0,[z331,z1,z2,z3,z46,z5]),(0,[z0,z3,z4,z5,z192,z543]),(0,[z0,z1,z2,z272,z4,z136]),(0,[z0,z1,z3,z4,z5,z803]),(0,[z0,z1,z2,z804,z4,z5]),(0,[z0,z805,z2,z3,z4,z5])],[(0,[z0,z1,z806,z3,z4,z5]),(0,[z807,z1,z2,z3,z4,z5]),(0,[z0,z1,z71,z808,z4,z5])]],
   [[(0,[z118,z79,z2,z573,z4,z5]),(0,[z0,z1,z3,z4,z72,z5]),(0,[z0,z809,z2,z3,z4,z5]),(0,[z0,z1,z2,z810,z4,z5]),(0,[z0,z1,z71,z295,z4,z5]),(0,[z0,z1,z2,z77,z78,z5])],[],[(0,[z0,z1,z2,z3,z4,z811]),(0,[z0,z2,z3,z4,z250,z84]),(0,[z1,z2,z3,z4,z5,z812]),(0,[z813,z0,z1,z3,z4,z5])],[(0,[z94,z1,z95,z3,z4,z5]),(0,[z0,z1,z20,z3,z4,z228]),(0,[z591,z0,z2,z89,z4,z5])],[(0,[z329,z0,z2,z523,z4,z5]),(0,[z0,z2,z814,z3,z4,z5]),(0,[z0,z2,z3,z552,z19,z5]),(0,[z0,z1,z815,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z816])],[(0,[z70,z1,z2,z4,z123,z5]),(0,[z132,z0,z2,z4,z84,z5]),(0,[z0,z1,z2,z3,z4,z817]),(0,[z0,z1,z2,z818,z4,z5])],[(0,[z45,z1,z2,z3,z4,z98]),(0,[z0,z1,z2,z819,z4,z5]),(0,[z0,z1,z2,z3,z820,z5]),(0,[z480,z0,z2,z89,z4,z5]),(0,[z0,z1,z153,z3,z4,z5])],[(0,[z0,z1,z3,z4,z5,z821]),(0,[z0,z1,z822,z3,z4,z5]),(0,[z0,z1,z3,z808,z4,z5]),(0,[z0,z1,z2,z823,z4,z5])]],
   [[(0,[z0,z1,z2,z25,z4,z342]),(1,[z0,z1,z808,z4,z5]),(0,[z0,z1,z2,z824,z4,z5]),(0,[z0,z2,z3,z4,z5,z825])],[(0,[z222,z0,z2,z3,z418,z5])],[(0,[z22,z2,z3,z449,z4,z5]),(0,[z0,z1,z2,z3,z4,z826]),(0,[z0,z827,z2,z3,z4,z5]),(0,[z0,z1,z31,z4,z5,z498]),(0,[z0,z1,z2,z3,z4,z828]),(0,[z829,z1,z2,z3,z4,z5]),(0,[z0,z1,z830,z3,z4,z5])],[(0,[z0,z2,z29,z3,z4,z5]),(0,[z218,z1,z2,z3,z4,z5]),(0,[z831,z1,z2,z3,z4,z5]),(0,[z222,z0,z2,z3,z778,z5]),(0,[z0,z1,z186,z4,z258,z372])],[(0,[z0,z1,z3,z832,z4,z5])],[(0,[z0,z1,z2,z3,z833,z5]),(0,[z0,z834,z2,z3,z4,z5]),(0,[z127,z0,z1,z3,z4,z5]),(0,[z0,z10,z2,z3,z4,z5]),(0,[z56,z0,z1,z2,z424,z51])],[(0,[z0,z2,z708,z3,z4,z5]),(0,[z835,z1,z2,z3,z4,z5]),(0,[z0,z836,z2,z3,z4,z5]),(0,[z837,z1,z2,z3,z4,z5])],[(0,[z7,z0,z273,z3,z4,z5]),(0,[z0,z1,z2,z838,z4,z5]),(0,[z0,z1,z2,z3,z4,z839]),(0,[z0,z1,z840,z3,z4,z5]),(0,[z305,z373,z2,z3,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z723,z5]),(0,[z0,z2,z3,z4,z5,z841]),(0,[z0,z1,z31,z3,z4,z136]),(0,[z842,z1,z2,z3,z4,z5])],[(1,[z1,z2,z749,z4,z5]),(0,[z0,z138,z139,z3,z4,z5])],[(0,[z0,z1,z2,z3,z843,z5]),(0,[z70,z1,z2,z593,z4,z5]),(0,[z0,z1,z2,z844,z4,z5]),(0,[z0,z206,z2,z645,z4,z5]),(0,[z0,z55,z2,z3,z433,z5]),(0,[z845,z0,z1,z2,z3,z5])],[(0,[z846,z0,z1,z3,z4,z5])],[(0,[z0,z2,z3,z847,z4,z5]),(0,[z848,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z4,z258,z760]),(0,[z0,z2,z3,z4,z849,z5])],[(0,[z0,z1,z2,z3,z4,z850]),(0,[z0,z452,z2,z254,z4,z5]),(0,[z0,z1,z851,z3,z4,z5])],[(0,[z0,z1,z2,z852,z4,z5]),(0,[z150,z146,z1,z2,z4,z5]),(0,[z0,z853,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z854,z5]),(0,[z0,z1,z855,z3,z4,z5]),(0,[z415,z0,z2,z89,z4,z5]),(0,[z0,z856,z2,z3,z4,z5]),(0,[z0,z1,z857,z3,z4,z5]),(0,[z858,z1,z2,z3,z4,z5]),(0,[z859,z1,z2,z3,z4,z5]),(0,[z96,z0,z1,z3,z353,z5]),(0,[z0,z1,z16,z3,z17,z5])]],
   [[],[(0,[z0,z2,z3,z4,z84,z5]),(0,[z385,z0,z1,z3,z4,z72]),(0,[z7,z0,z227,z272,z4,z5]),(0,[z0,z1,z368,z114,z4,z5]),(0,[z0,z1,z20,z3,z4,z249]),(0,[z56,z0,z1,z57,z3,z51])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z157,z29,z158,z3,z4,z5]),(0,[z0,z1,z2,z860,z4,z5]),(0,[z0,z1,z20,z3,z4,z586]),(0,[z0,z117,z2,z424,z4,z5])],[(0,[z0,z2,z3,z4,z861,z5]),(1,[z0,z1,z2,z3,z725])],[(0,[z118,z0,z2,z272,z4,z5])],[(0,[z0,z1,z862,z3,z4,z5]),(0,[z660,z0,z1,z2,z4,z103]),(0,[z0,z1,z3,z4,z5,z863]),(0,[z0,z1,z2,z3,z4,z864]),(0,[z0,z865,z2,z3,z4,z5]),(0,[z0,z1,z317,z4,z5,z135])],[(0,[z0,z1,z2,z120,z4,z5]),(0,[z0,z866,z2,z3,z4,z5]),(0,[z45,z1,z126,z3,z4,z98])],[(0,[z0,z1,z2,z3,z867,z5]),(0,[z150,z1,z2,z463,z4,z5]),(0,[z0,z1,z2,z4,z5,z868]),(0,[z96,z105,z1,z3,z353,z5])]],
   [[(0,[z0,z1,z869,z3,z4,z5]),(0,[z0,z870,z2,z3,z4,z5]),(0,[z56,z0,z117,z2,z3,z51]),(0,[z0,z1,z2,z3,z21,z725])],[(0,[z0,z1,z871,z3,z4,z5]),(0,[z142,z1,z2,z4,z46,z5]),(0,[z0,z1,z872,z3,z4,z5]),(0,[z519,z0,z2,z89,z4,z5]),(0,[z0,z1,z411,z3,z4,z43]),(0,[z0,z1,z2,z873,z4,z5])],[(0,[z1,z2,z3,z749,z4,z5]),(0,[z0,z1,z874,z3,z4,z5]),(0,[z0,z1,z875,z3,z4,z5])],[(0,[z0,z1,z2,z3,z876,z5]),(0,[z877,z0,z1,z2,z3,z4]),(0,[z0,z878,z2,z3,z4,z5])],[(0,[z0,z1,z879,z3,z4,z5])],[(0,[z1,z2,z13,z749,z4,z5]),(0,[z0,z1,z3,z4,z5,z880]),(0,[z294,z0,z227,z3,z4,z5]),(0,[z8,z0,z1,z34,z4,z5])],[(0,[z0,z1,z2,z3,z881,z5]),(0,[z0,z1,z882,z3,z4,z5]),(0,[z883,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z723,z5]),(0,[z45,z1,z2,z3,z4,z713]),(0,[z0,z1,z3,z4,z884,z5])],[(0,[z22,z80,z2,z3,z418,z5]),(0,[z0,z1,z885,z3,z4,z5]),(0,[z0,z1,z2,z886,z4,z5]),(0,[z0,z1,z57,z3,z4,z5]),(0,[z0,z1,z291,z186,z4,z258])]],
   [[(0,[z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z4,z713]),(0,[z238,z99,z2,z89,z4,z5]),(0,[z0,z1,z3,z4,z5,z887])],[(0,[z0,z1,z2,z888,z4,z5]),(0,[z0,z1,z2,z4,z5,z889])],[(0,[z0,z1,z2,z4,z5,z214]),(0,[z0,z890,z2,z3,z4,z5])],[(0,[z127,z118,z0,z3,z4,z5]),(0,[z891,z1,z2,z3,z4,z5])],[(0,[z892,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z186,z4,z244]),(0,[z0,z373,z2,z424,z4,z5])],[(0,[z0,z2,z3,z4,z5,z893]),(0,[z0,z2,z3,z894,z4,z5]),(0,[z398,z2,z3,z84,z46,z5]),(0,[z0,z1,z895,z3,z4,z5]),(0,[z1,z2,z3,z4,z896,z5]),(0,[z351,z0,z2,z3,z4,z92]),(0,[z0,z1,z2,z897,z4,z5])],[(0,[z0,z2,z3,z4,z137,z92]),(0,[z0,z1,z2,z186,z4,z375]),(0,[z898,z1,z2,z3,z4,z5])],[(0,[z329,z142,z0,z2,z4,z5]),(0,[z0,z139,z3,z4,z581,z5]),(0,[z0,z2,z3,z738,z4,z5]),(0,[z0,z1,z899,z3,z4,z5]),(0,[z0,z339,z2,z3,z4,z43])]],
   [[(0,[z0,z1,z2,z3,z900,z5]),(0,[z0,z1,z901,z3,z4,z5]),(0,[z0,z1,z20,z3,z4,z281]),(0,[z0,z1,z2,z3,z4,z342]),(0,[z8,z0,z1,z4,z5,z74])],[(0,[z238,z1,z2,z3,z4,z5]),(0,[z27,z2,z13,z3,z4,z5]),(0,[z0,z902,z2,z3,z4,z5])],[(0,[z0,z1,z126,z3,z4,z5]),(0,[z0,z903,z2,z3,z4,z5]),(0,[z45,z1,z2,z3,z4,z81]),(0,[z1,z2,z3,z4,z5,z713]),(0,[z0,z1,z2,z3,z4,z760])],[(0,[z0,z1,z2,z4,z5,z904]),(0,[z0,z617,z2,z89,z4,z5]),(0,[z0,z1,z2,z3,z4,z905]),(0,[z0,z2,z3,z4,z5,z906]),(0,[z0,z1,z2,z25,z4,z136]),(0,[z0,z1,z2,z4,z734,z5]),(0,[z266,z1,z2,z424,z4,z5])],[(0,[z150,z1,z2,z513,z4,z5]),(0,[z0,z1,z808,z34,z4,z5]),(0,[z907,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z725])],[(0,[z0,z1,z908,z3,z4,z5]),(0,[z96,z0,z1,z3,z563,z5]),(0,[z0,z1,z2,z4,z5,z909]),(0,[z344,z1,z2,z3,z46,z5]),(0,[z27,z0,z2,z3,z19,z5]),(0,[z45,z2,z3,z4,z98,z192]),(0,[z0,z1,z2,z314,z4,z5])],[(0,[z105,z1,z2,z3,z4,z5]),(0,[z0,z1,z910,z3,z4,z5]),(0,[z451,z132,z0,z1,z4,z5]),(0,[z0,z1,z2,z911,z4,z5]),(0,[z0,z1,z2,z369,z4,z5]),(0,[z266,z117,z2,z3,z4,z5])],[(0,[z0,z1,z2,z4,z912,z5]),(0,[z70,z2,z13,z449,z4,z5]),(0,[z385,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z913,z5]),(0,[z8,z0,z1,z808,z4,z5]),(0,[z683,z0,z1,z3,z353,z5]),(1,[z0,z1,z2,z734,z5])]],
   [[(0,[z0,z1,z914,z3,z4,z5]),(0,[z7,z0,z394,z3,z4,z5]),(1,[z0,z1,z3,z729,z5]),(0,[z256,z0,z1,z3,z4,z135]),(0,[z0,z915,z2,z3,z4,z5]),(0,[z916,z0,z2,z3,z4,z5])],[],[(0,[z132,z0,z1,z2,z4,z250]),(0,[z917,z0,z2,z3,z4,z5]),(0,[z918,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z21,z183])],[(0,[z919,z0,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z123,z5]),(0,[z0,z1,z2,z4,z434,z103]),(0,[z0,z2,z4,z5,z192,z30]),(0,[z1,z2,z3,z920,z4,z5]),(0,[z0,z1,z921,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z922]),(0,[z0,z577,z2,z3,z278,z5]),(0,[z141,z1,z2,z3,z276,z5]),(0,[z0,z1,z2,z3,z5,z923]),(0,[z0,z1,z2,z4,z5,z924]),(0,[z907,z105,z2,z3,z4,z5]),(0,[z0,z1,z925,z3,z4,z5])],[(0,[z94,z105,z1,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z926]),(0,[z927,z1,z2,z3,z4,z5]),(0,[z156,z0,z1,z2,z207,z5]),(0,[z305,z1,z2,z424,z4,z5])],[(0,[z157,z105,z1,z3,z4,z5]),(0,[z0,z1,z2,z928,z4,z5])],[(0,[z127,z0,z3,z4,z19,z5]),(0,[z0,z1,z291,z4,z5,z103])]],
   [[(0,[z0,z2,z3,z4,z929,z5]),(0,[z930,z1,z2,z3,z4,z5])],[(0,[z27,z0,z2,z4,z87,z5]),(0,[z0,z1,z2,z931,z4,z5]),(0,[z0,z932,z2,z3,z4,z5]),(0,[z56,z0,z373,z2,z3,z51])],[(0,[z933,z0,z1,z2,z4,z5]),(0,[z150,z1,z2,z4,z87,z5]),(0,[z0,z1,z57,z314,z4,z5])],[(0,[z934,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z935,z4,z5]),(0,[z600,z0,z2,z89,z4,z5])],[(0,[z27,z385,z0,z2,z3,z4]),(0,[z936,z0,z1,z2,z4,z5])],[(0,[z0,z2,z3,z937,z4,z5]),(0,[z0,z1,z2,z938,z4,z5]),(0,[z398,z385,z1,z2,z3,z46])],[(0,[z939,z0,z1,z2,z3,z4]),(0,[z0,z940,z2,z3,z4,z5])],[(0,[z164,z1,z2,z3,z248,z5]),(0,[z1,z2,z3,z4,z98,z713]),(0,[z0,z1,z2,z941,z4,z5])]],
   [[(0,[z0,z12,z2,z3,z4,z5]),(0,[z0,z1,z942,z3,z4,z5]),(0,[z266,z373,z2,z3,z4,z5])],[(0,[z22,z0,z2,z272,z4,z5]),(0,[z142,z0,z2,z29,z4,z5]),(0,[z0,z2,z3,z4,z19,z136]),(0,[z127,z0,z55,z3,z4,z5]),(0,[z0,z55,z2,z3,z278,z5]),(0,[z517,z0,z2,z3,z19,z5])],[],[(0,[z0,z943,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z944]),(0,[z0,z945,z2,z3,z4,z5]),(0,[z946,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z4,z5,z947]),(0,[z0,z2,z3,z4,z5,z948]),(0,[z0,z1,z2,z949,z4,z5]),(1,[z0,z1,z2,z4,z760])],[(0,[z0,z1,z3,z4,z729,z5])],[(0,[z7,z0,z227,z25,z4,z5]),(0,[z1,z2,z3,z4,z5,z950]),(0,[z0,z951,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z725,z51])],[(0,[z0,z1,z3,z4,z952,z5]),(0,[z0,z1,z953,z3,z4,z5]),(0,[z954,z0,z2,z3,z4,z5]),(0,[z1,z2,z955,z3,z4,z5]),(0,[z956,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z957,z4,z5]),(0,[z958,z1,z2,z3,z4,z5])],[(0,[z0,z2,z3,z959,z4,z5]),(0,[z0,z1,z2,z960,z4,z5])],[(0,[z451,z0,z1,z3,z4,z5]),(0,[z0,z1,z726,z3,z4,z5]),(0,[z727,z105,z2,z3,z4,z5]),(0,[z0,z1,z291,z186,z4,z5])],[(0,[z0,z961,z2,z3,z4,z5])],[(0,[z118,z79,z2,z3,z4,z5]),(0,[z962,z1,z2,z3,z4,z5]),(0,[z0,z963,z2,z3,z4,z5])],[(0,[z964,z0,z1,z2,z4,z5]),(0,[z256,z0,z1,z3,z4,z752])],[(0,[z157,z142,z1,z158,z4,z5]),(0,[z42,z0,z2,z3,z4,z731]),(0,[z0,z1,z3,z4,z5,z965])],[(0,[z22,z80,z2,z3,z4,z5]),(0,[z1,z743,z2,z3,z4,z5]),(0,[z0,z1,z2,z523,z4,z5]),(0,[z0,z2,z272,z4,z19,z5])]],
   [[(0,[z118,z79,z2,z120,z4,z5]),(0,[z70,z1,z2,z13,z4,z5]),(0,[z383,z0,z1,z3,z4,z135]),(0,[z1,z2,z77,z78,z123,z5])],[(0,[z385,z451,z0,z1,z3,z4]),(0,[z0,z138,z708,z3,z4,z5]),(0,[z0,z1,z20,z3,z4,z752])],[(0,[z0,z1,z2,z966,z4,z5]),(0,[z0,z1,z2,z3,z5,z967]),(0,[z451,z105,z1,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z968]),(0,[z48,z305,z1,z2,z3,z4]),(0,[z45,z1,z2,z254,z4,z98]),(0,[z0,z1,z969,z3,z4,z5])],[(0,[z0,z1,z2,z970,z4,z5]),(0,[z0,z1,z2,z3,z4,z136]),(0,[z1,z2,z3,z4,z971,z5]),(0,[z56,z266,z1,z2,z3,z51])],[(0,[z0,z743,z2,z3,z4,z5]),(0,[z70,z1,z2,z456,z4,z5]),(0,[z0,z2,z3,z972,z4,z5]),(0,[z0,z55,z2,z272,z4,z5])],[(0,[z973,z1,z2,z3,z4,z5])],[(0,[z156,z0,z1,z2,z493,z5])],[(0,[z0,z1,z3,z4,z72,z250]),(0,[z1,z2,z3,z4,z974,z5]),(0,[z42,z0,z2,z3,z4,z92]),(0,[z0,z1,z3,z4,z5,z372])]],
   [[(0,[z118,z743,z2,z3,z4,z5]),(0,[z0,z1,z2,z975,z4,z5]),(0,[z0,z1,z2,z3,z4,z976]),(0,[z0,z977,z2,z3,z4,z5])],[(0,[z0,z139,z2,z3,z418,z5]),(0,[z0,z1,z2,z978,z4,z5]),(0,[z0,z1,z71,z31,z4,z5]),(0,[z0,z979,z2,z3,z4,z5])],[(0,[z0,z980,z2,z3,z4,z5])],[(0,[z1,z2,z726,z3,z4,z5]),(0,[z0,z1,z981,z3,z4,z5]),(0,[z164,z1,z2,z3,z432,z5]),(0,[z150,z0,z521,z2,z4,z5]),(0,[z982,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z983,z4,z5]),(0,[z0,z1,z2,z984,z4,z5]),(0,[z985,z1,z2,z3,z4,z5]),(0,[z0,z1,z153,z314,z4,z5])],[(0,[z0,z1,z986,z3,z4,z5]),(0,[z132,z0,z1,z4,z72,z5]),(0,[z0,z1,z368,z3,z4,z5]),(0,[z0,z2,z3,z4,z43,z731]),(0,[z0,z1,z3,z4,z198,z135])],[(0,[z94,z1,z3,z4,z316,z5]),(0,[z0,z2,z987,z3,z4,z5]),(0,[z1,z2,z3,z723,z46,z5]),(0,[z398,z451,z1,z3,z46,z5]),(0,[z0,z1,z20,z317,z4,z5])],[(0,[z0,z1,z2,z988,z4,z5]),(0,[z0,z55,z2,z3,z337,z5]),(0,[z0,z1,z2,z989,z4,z5])]],
   [[(0,[z0,z1,z2,z990,z4,z5]),(0,[z150,z127,z0,z1,z4,z5]),(0,[z0,z1,z2,z4,z87,z5]),(0,[z0,z1,z3,z4,z5,z991]),(0,[z0,z1,z2,z3,z4,z992]),(0,[z0,z1,z2,z3,z4,z993]),(0,[z994,z1,z2,z3,z4,z5]),(0,[z127,z0,z1,z34,z4,z5])],[(0,[z0,z1,z3,z4,z5,z995]),(0,[z0,z1,z2,z996,z4,z5]),(0,[z0,z2,z738,z89,z4,z5]),(0,[z0,z1,z225,z3,z4,z135]),(0,[z997,z1,z2,z3,z4,z5]),(0,[z998,z0,z1,z2,z4,z5])],[(0,[z398,z132,z1,z2,z46,z5]),(0,[z45,z452,z2,z3,z4,z98]),(0,[z1,z2,z3,z4,z5,z999]),(0,[z1000,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1001]),(0,[z150,z1,z2,z749,z4,z5]),(0,[z27,z451,z0,z3,z4,z5])],[(0,[z1,z3,z421,z456,z4,z5])],[(0,[z157,z1,z726,z3,z4,z5]),(0,[z94,z1,z61,z3,z4,z5]),(0,[z8,z0,z1,z272,z4,z5]),(0,[z0,z1,z411,z3,z4,z5]),(0,[z56,z305,z1,z2,z3,z51])],[(0,[z0,z1,z2,z254,z4,z5]),(0,[z8,z0,z1,z459,z4,z5])],[(0,[z27,z132,z0,z2,z4,z5]),(0,[z0,z1,z2,z4,z1002,z5]),(0,[z0,z139,z708,z3,z4,z5]),(0,[z0,z1,z2,z186,z4,z201])]],
   [[(0,[z398,z1,z2,z3,z250,z46]),(0,[z0,z1,z2,z3,z4,z1003]),(0,[z0,z1,z3,z4,z5,z752]),(0,[z0,z2,z3,z4,z1004,z5])],[(0,[z0,z452,z3,z4,z5,z543]),(0,[z0,z1,z2,z1005,z4,z5])],[],[(0,[z0,z1,z2,z1006,z4,z5]),(0,[z0,z1,z2,z3,z4,z1007]),(0,[z0,z292,z2,z196,z4,z5]),(0,[z1,z2,z3,z481,z46,z5]),(0,[z127,z1,z3,z456,z4,z5]),(0,[z0,z119,z2,z3,z4,z364]),(0,[z0,z1,z411,z3,z4,z92]),(0,[z1008,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1009,z4,z5]),(0,[z7,z0,z227,z3,z4,z136]),(0,[z0,z1,z3,z421,z4,z5]),(1,[z0,z2,z738,z4,z5]),(0,[z0,z119,z2,z3,z4,z43])],[(0,[z1010,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z4,z5,z30])],[(0,[z22,z226,z2,z3,z4,z5]),(0,[z7,z0,z227,z3,z4,z5])],[(0,[z1011,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z752])]],
   [[(0,[z0,z1,z1012,z3,z4,z5]),(0,[z0,z119,z2,z3,z4,z686]),(0,[z150,z0,z2,z449,z4,z5]),(0,[z0,z1013,z2,z3,z4,z5]),(0,[z1014,z0,z1,z2,z4,z5]),(0,[z0,z373,z153,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1015,z5]),(0,[z385,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z250]),(0,[z565,z0,z1,z3,z4,z135])],[(0,[z0,z117,z2,z3,z4,z5]),(0,[z0,z119,z2,z3,z4,z731])],[(0,[z0,z206,z2,z58,z4,z5]),(0,[z398,z1,z2,z3,z46,z5]),(0,[z570,z0,z1,z3,z4,z135]),(0,[z0,z1,z1016,z3,z4,z5]),(0,[z222,z0,z2,z3,z19,z5]),(0,[z0,z1,z2,z186,z4,z258])],[(0,[z0,z1,z2,z4,z1017,z5]),(0,[z0,z1,z68,z31,z4,z5]),(0,[z0,z1,z2,z4,z5,z1018]),(0,[z0,z1,z20,z4,z249,z214])],[(0,[z118,z0,z2,z120,z4,z5]),(0,[z1,z2,z456,z120,z4,z5]),(0,[z27,z150,z2,z3,z4,z5]),(0,[z1019,z0,z1,z2,z4,z5]),(0,[z96,z387,z1,z3,z353,z5]),(0,[z0,z1,z2,z77,z734,z5])],[(0,[z1,z2,z13,z3,z418,z5]),(0,[z0,z452,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1020]),(0,[z398,z1,z3,z72,z46,z5]),(0,[z0,z1,z4,z87,z72,z5]),(0,[z0,z1,z2,z1021,z4,z5])],[(0,[z0,z1,z31,z808,z4,z5])]],
   [[(0,[z0,z1,z1022,z3,z4,z5]),(0,[z1,z2,z1023,z3,z4,z5]),(0,[z1014,z105,z1,z2,z4,z5]),(0,[z156,z0,z1,z2,z734,z5])],[(0,[z0,z1024,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z1025,z5])],[(0,[z0,z1,z2,z573,z4,z5]),(0,[z27,z0,z2,z3,z278,z5]),(0,[z0,z1,z20,z317,z4,z249]),(0,[z0,z1,z2,z3,z183,z725])],[(0,[z329,z0,z2,z3,z4,z5]),(0,[z150,z1,z2,z4,z123,z5]),(0,[z0,z515,z2,z196,z4,z5]),(0,[z0,z1,z2,z317,z4,z5]),(0,[z721,z0,z1,z2,z4,z5]),(0,[z1,z2,z3,z4,z1026,z5])],[],[(0,[z0,z1,z126,z254,z4,z5]),(0,[z127,z0,z1,z4,z5,z103])],[(0,[z0,z1,z2,z1027,z4,z5]),(0,[z1028,z0,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1029]),(0,[z0,z1,z2,z808,z4,z5]),(0,[z1030,z1,z2,z3,z4,z5]),(0,[z0,z117,z57,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z150,z1,z2,z223,z4,z5]),(0,[z150,z309,z1,z2,z4,z5]),(0,[z45,z1,z2,z4,z98,z30]),(0,[z0,z1,z1032,z3,z4,z5]),(0,[z0,z2,z3,z4,z1033,z5]),(0,[z0,z1,z1034,z3,z4,z5])],[(0,[z45,z1,z2,z3,z4,z410]),(0,[z99,z2,z456,z89,z4,z5]),(0,[z0,z1,z1035,z3,z4,z5]),(0,[z0,z1,z411,z369,z4,z5]),(0,[z305,z1,z153,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1036]),(0,[z0,z1037,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1038,z4,z5]),(0,[z0,z1,z1039,z3,z4,z5]),(0,[z238,z1,z3,z421,z4,z5]),(0,[z0,z1,z2,z114,z4,z5]),(0,[z0,z55,z2,z3,z778,z5]),(0,[z0,z1,z2,z3,z5,z1040])],[(0,[z7,z0,z227,z3,z4,z342]),(0,[z0,z373,z2,z3,z4,z5]),(0,[z0,z1,z2,z1041,z4,z5]),(0,[z0,z1,z2,z4,z1042,z5]),(0,[z156,z0,z10,z2,z207,z5]),(0,[z1043,z1,z2,z3,z4,z5])],[(0,[z22,z743,z2,z3,z4,z5]),(0,[z0,z1,z126,z4,z5,z30])],[(0,[z0,z2,z523,z29,z4,z5])],[(0,[z8,z0,z1,z371,z4,z5])]],
   [[(0,[z0,z119,z2,z3,z418,z5]),(0,[z0,z1,z2,z3,z4,z1044]),(0,[z0,z1,z1045,z3,z4,z5])],[(0,[z0,z1,z2,z749,z4,z5]),(0,[z0,z1,z16,z3,z589,z5])],[(0,[z1,z2,z3,z456,z4,z5]),(0,[z0,z1,z2,z1046,z4,z5]),(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z206,z2,z738,z4,z5])],[(0,[z387,z1,z2,z3,z4,z5]),(0,[z150,z1,z2,z40,z4,z5]),(0,[z0,z1,z3,z4,z5,z1048])],[(0,[z22,z688,z2,z3,z4,z5]),(0,[z0,z1,z1049,z3,z4,z5])],[(0,[z27,z0,z2,z3,z4,z250])],[(0,[z0,z2,z3,z418,z5,z92]),(0,[z0,z2,z3,z449,z4,z5]),(0,[z0,z1,z2,z3,z4,z1050]),(0,[z94,z1,z3,z4,z5,z257]),(0,[z0,z452,z126,z3,z4,z5]),(0,[z1051,z0,z1,z2,z4,z5]),(0,[z1052,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1053,z3,z4,z5]),(0,[z0,z2,z3,z4,z1054,z5]),(0,[z56,z0,z1,z2,z3,z725])]],
   [[(0,[z132,z0,z1,z2,z4,z5]),(0,[z0,z2,z3,z4,z778,z5])],[(0,[z0,z1,z2,z4,z5,z1055]),(0,[z0,z1,z2,z738,z4,z5]),(0,[z127,z0,z1,z186,z4,z5]),(0,[z0,z1056,z2,z3,z4,z5]),(0,[z0,z373,z57,z3,z4,z5])],[(0,[z0,z1,z2,z1057,z4,z5]),(0,[z0,z1,z2,z3,z4,z1058]),(0,[z451,z94,z1,z3,z4,z5]),(0,[z0,z2,z3,z4,z1059,z5]),(0,[z385,z0,z2,z3,z4,z84]),(0,[z0,z1,z2,z3,z4,z1060])],[(0,[z118,z2,z3,z456,z4,z5]),(0,[z0,z1,z1061,z3,z4,z5]),(0,[z0,z1062,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z752,z135])],[(0,[z0,z1063,z2,z3,z4,z5])],[(0,[z0,z1064,z2,z3,z4,z5]),(0,[z1065,z0,z1,z3,z4,z5]),(0,[z305,z1,z2,z3,z4,z5]),(0,[z1066,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z1067,z4,z5])],[(0,[z150,z1,z2,z75,z4,z5]),(0,[z79,z743,z2,z3,z4,z5]),(0,[z157,z1,z158,z3,z4,z5]),(0,[z1068,z0,z1,z2,z3,z4]),(0,[z56,z0,z1,z153,z3,z51])],[(0,[z1,z2,z3,z276,z723,z5]),(0,[z1069,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z1070,z4,z5]),(0,[z0,z206,z2,z3,z418,z5]),(0,[z451,z0,z1,z4,z87,z5]),(0,[z1071,z0,z1,z2,z4,z5]),(0,[z0,z138,z3,z280,z4,z5]),(0,[z0,z1,z2,z1072,z4,z5]),(0,[z0,z1,z2,z3,z4,z1073]),(0,[z294,z0,z2,z3,z4,z92]),(0,[z0,z1,z3,z729,z353,z5]),(0,[z266,z1,z57,z3,z4,z5])],[(0,[z70,z0,z521,z2,z4,z5]),(0,[z56,z0,z1,z2,z3,z604])],[(0,[z1074,z0,z1,z3,z4,z5]),(0,[z0,z1,z2,z1075,z4,z5]),(0,[z0,z1,z1076,z3,z4,z5]),(0,[z48,z1,z2,z3,z4,z713]),(0,[z0,z2,z3,z4,z1077,z5])],[(0,[z0,z1,z227,z3,z4,z136])],[(0,[z0,z1,z1078,z3,z4,z5])],[(0,[z385,z45,z1,z2,z3,z4]),(0,[z0,z1,z2,z1079,z4,z5])],[(0,[z118,z2,z483,z3,z4,z5]),(1,[z1,z2,z3,z723,z5]),(0,[z742,z2,z3,z4,z123,z5]),(0,[z0,z1,z153,z424,z4,z5])],[(0,[z0,z1,z2,z1080,z4,z5]),(0,[z0,z1,z2,z1081,z4,z5]),(0,[z0,z373,z2,z314,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z1082]),(0,[z22,z80,z2,z3,z23,z5]),(1,[z1,z2,z3,z4,z713]),(0,[z1083,z1,z2,z3,z4,z5]),(0,[z1084,z0,z1,z3,z4,z5])],[(0,[z0,z1,z1085,z3,z4,z5]),(0,[z0,z117,z153,z3,z4,z5])],[(0,[z22,z0,z2,z120,z4,z5]),(0,[z0,z1,z2,z1086,z4,z5]),(0,[z238,z1,z2,z4,z5,z103]),(0,[z42,z0,z368,z3,z4,z92]),(0,[z0,z1087,z2,z3,z4,z5]),(0,[z305,z1,z57,z3,z4,z5])],[(0,[z1,z95,z726,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z760])],[(0,[z0,z1,z254,z4,z5,z543]),(0,[z2,z3,z4,z1077,z123,z5])],[(0,[z0,z1,z2,z1088,z4,z5])],[(0,[z0,z1,z2,z1089,z4,z5]),(0,[z1,z2,z3,z4,z1090,z5])],[(0,[z94,z1,z726,z3,z4,z5]),(0,[z385,z132,z0,z1,z2,z4]),(1,[z0,z2,z3,z4,z731])]],
   [[(0,[z127,z0,z1,z272,z4,z5]),(0,[z0,z1,z2,z1091,z4,z5]),(0,[z0,z1,z1092,z3,z4,z5])],[(0,[z0,z1,z2,z4,z1093,z5])],[(0,[z1,z2,z13,z120,z4,z5]),(0,[z0,z1,z2,z186,z4,z448]),(0,[z42,z0,z411,z3,z4,z92])],[(0,[z0,z1,z2,z4,z5,z1094])],[(0,[z0,z1,z2,z3,z4,z1095]),(0,[z0,z1,z2,z3,z1096,z5]),(0,[z1097,z0,z2,z3,z4,z5]),(0,[z48,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z5,z1098])],[(0,[z0,z1,z2,z3,z1099,z5]),(0,[z0,z1,z3,z4,z5,z1100]),(0,[z0,z1,z31,z272,z4,z5]),(0,[z0,z708,z227,z3,z4,z5])],[(0,[z0,z2,z3,z278,z575,z5]),(0,[z157,z1,z526,z3,z4,z5]),(0,[z142,z164,z1,z2,z4,z5])],[(0,[z0,z1101,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z729,z5])]],
   [[(0,[z151,z0,z2,z3,z19,z5]),(0,[z305,z1,z2,z314,z4,z5])],[(0,[z157,z1,z523,z158,z4,z5]),(0,[z1,z2,z4,z87,z123,z5]),(0,[z0,z1,z2,z77,z572,z5])],[(0,[z118,z0,z2,z3,z4,z136]),(0,[z0,z1,z2,z3,z4,z1102]),(0,[z0,z2,z196,z738,z4,z5]),(0,[z0,z1,z2,z424,z4,z5])],[(0,[z7,z0,z2,z3,z418,z5]),(0,[z0,z1103,z2,z3,z4,z5]),(0,[z7,z0,z182,z3,z4,z5]),(0,[z1104,z1,z2,z3,z4,z5])],[(0,[z0,z1,z3,z1105,z4,z5]),(0,[z1,z2,z3,z4,z1106,z5])],[(0,[z0,z2,z267,z89,z4,z5]),(0,[z0,z1,z2,z272,z4,z5]),(0,[z238,z1,z2,z186,z4,z5]),(0,[z0,z2,z3,z4,z5,z1107]),(0,[z0,z2,z1108,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1109])],[(0,[z1110,z0,z1,z2,z3,z5]),(0,[z42,z0,z2,z369,z4,z92]),(0,[z0,z1,z2,z1111,z4,z5]),(0,[z0,z1,z2,z186,z4,z760]),(0,[z56,z0,z1,z2,z314,z51])],[]],
   [[(0,[z0,z1,z2,z1112,z4,z5])],[(0,[z0,z1,z1113,z3,z4,z5]),(0,[z0,z1,z2,z1114,z4,z5]),(0,[z0,z2,z254,z4,z5,z192]),(0,[z0,z1,z3,z4,z1115,z5])],[(0,[z0,z1,z2,z1116,z4,z5]),(0,[z0,z1117,z2,z3,z4,z5]),(0,[z266,z1,z153,z3,z4,z5])],[(0,[z27,z0,z2,z3,z418,z5]),(0,[z0,z2,z3,z278,z418,z5]),(0,[z0,z1,z2,z3,z4,z1118]),(0,[z99,z0,z2,z89,z4,z5]),(0,[z1119,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z1120]),(0,[z1121,z1,z2,z3,z4,z5])],[(0,[z150,z1,z2,z3,z418,z5]),(0,[z0,z1122,z2,z3,z4,z5]),(0,[z0,z1,z368,z369,z4,z5])],[(0,[z0,z1,z2,z1123,z4,z5]),(0,[z0,z1,z2,z1124,z4,z5]),(0,[z0,z2,z3,z278,z778,z5]),(0,[z0,z1,z20,z3,z4,z201])],[(0,[z0,z1,z291,z3,z4,z5]),(0,[z56,z0,z1,z2,z3,z51])],[(0,[z70,z1,z2,z4,z5,z700]),(0,[z0,z1,z2,z4,z87,z250]),(0,[z0,z1125,z2,z3,z4,z5]),(0,[z0,z1,z2,z1126,z4,z5]),(1,[z0,z2,z3,z778,z5]),(0,[z0,z1127,z2,z3,z4,z5]),(0,[z0,z1,z57,z424,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 538) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1082)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 538] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 148).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 148).take 108).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [148, 108] = true :=
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

end PEqualNP.Outside.L_meta_38465

theorem PEqualNP.Outside.L_meta_38465 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3940608512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3940608512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38465.solve