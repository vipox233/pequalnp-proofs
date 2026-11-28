import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38669

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
  Nat.testBit (4276808392 * 2 ^ 32 + 3941264064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x04000244c601515c#64 ++ 0xfb4027cfce73f3fc#64 : BitVec 128),
   (0x4801c9121aa4c4c5#64 ++ 0xf7c3d9327faccccf#64 : BitVec 128),
   (0x901c162c614b0b0a#64 ++ 0xeffc1e3c71cf0f0f#64 : BitVec 128),
   (0xe02ee03b01f00ea0#64 ++ 0xdfbfe03f81f00ff0#64 : BitVec 128),
   (0x00777d8001fea000#64 ++ 0xbe7fffc001fff000#64 : BitVec 128),
   (0x00bbbffffc000000#64 ++ 0x7ebffffffe000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [11, 8]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0026600001f00000 0xdf3fe00f81f003f0

def z1 : W := mkw 0x00777d8001fea000 0xbe7fffc001fff000

def z2 : W := mkw 0x00bbbffffc000000 0x7ebffffffe000000

def z3 : W := mkw 0x04000244c601515c 0xfb4027cfce73f3fc

def z4 : W := mkw 0x4801c9121aa4c4c5 0xf7c3d9327faccccf

def z5 : W := mkw 0x901c162c614b0b0a 0xeffc1e3c71cf0f0f

def z6 : W := mkw 0xe02ee03b01f00ea0 0xdfbfe03f81f00ff0

def z7 : W := mkw 0xe07ef4bb01fa2ea0 0xdfbfe6ff81f33ff0

def z8 : W := mkw 0x48a3e9d39ea4c4c5 0x1003e1c38e20c0c0

def z9 : W := mkw 0x48bbfffffea4c4c5 0xffffffffffaccccf

def z10 : W := mkw 0x04777dc087fef054 0xbe7fffc38ffff0f0

def z11 : W := mkw 0x00141400014a0000 0xeffc1e3071cf0c0f

def z12 : W := mkw 0x0001090018000000 0x200019007e000000

def z13 : W := mkw 0x00000244c4010108 0xfb4027cfce43030c

def z14 : W := mkw 0x0c010b44de05d15d 0xfb403fcffe7ff3ff

def z15 : W := mkw 0x00333d8000000000 0x3e3fffc000000000

def z16 : W := mkw 0x90bfbffffd4b0b0a 0xffffffffffcf0f0f

def z17 : W := mkw 0x04000244c601515c 0x4100000fce0003fc

def z18 : W := mkw 0xe008803b00000ea0 0x4180003f80000ff0

def z19 : W := mkw 0x00ba36ede4000000 0x083c26cd80000000

def z20 : W := mkw 0x4800400002a4c4c5 0x8140000001accccf

def z21 : W := mkw 0x0000020440010108 0xefc01e3c71cf0f0f

def z22 : W := mkw 0x0400004086005054 0x100021c38e30f0f0

def z23 : W := mkw 0x04000244c4011118 0x080026cd80533330

def z24 : W := mkw 0x0018166ce4000000 0x7ebc3ffffe000000

def z25 : W := mkw 0x800c002801400a00 0xeffc183c71cc0f0f

def z26 : W := mkw 0xe82fe93b1bf4cee5 0xfffff93ffffccfff

def z27 : W := mkw 0x4c01cb56dea5d5dd 0xf7c3d93fffaccfff

def z28 : W := mkw 0x00000244c4000000 0x7a0027cfce000000

def z29 : W := mkw 0x901c1428214b0b0a 0x85fc183031cf0f0f

def z30 : W := mkw 0x00911fc4fc000000 0x20001fc07e000000

def z31 : W := mkw 0xe004400001f00ea0 0x8100000001f00ff0

def z32 : W := mkw 0xf03ef63f61fb0faa 0xfffffe3ff1ff0fff

def z33 : W := mkw 0x6022e01300b004a0 0x1003e003803000f0

def z34 : W := mkw 0xa02e202901500a20 0x083c200d80500330

def z35 : W := mkw 0x4800c0121aa4c4c5 0xc1c000327faccccf

def z36 : W := mkw 0x00bbfffffca48000 0xfeffffffffacc000

def z37 : W := mkw 0x00ffbffffd5a2000 0x7ebffffffe533000

def z38 : W := mkw 0x047636c4c75b715c 0xfb7c27cfce73f3fc

def z39 : W := mkw 0x0488827ffe01515c 0x4180003ffe0003fc

def z40 : W := mkw 0x04bbbffffe01515c 0xfffffffffe73f3fc

def z41 : W := mkw 0x90040000014b0b0a 0x8140000001cf0f0f

def z42 : W := mkw 0x0044400001fea000 0x8040000001fff000

def z43 : W := mkw 0x0088827ffc000000 0x4080003ffe000000

def z44 : W := mkw 0xe42ee27fc7f15ffc 0xdfbfe03fcff00ffc

def z45 : W := mkw 0x4863e9921ab4e4c5 0xf7c3f9f27fbcfccf

def z46 : W := mkw 0x000189121a004044 0xf7c3d9327e20c0cc

def z47 : W := mkw 0x0000000000000000 0xe7c01830718c0c0f

def z48 : W := mkw 0x0018162c60000000 0x6ebc1e3c70000000

def z49 : W := mkw 0x800c002801400a00 0x04bc003001800c00

def z50 : W := mkw 0x800c002801400a00 0x083c000c00400300

def z51 : W := mkw 0x040000000201515c 0x814000000073f3fc

def z52 : W := mkw 0x002aa03b00000000 0x04bfc03000000000

def z53 : W := mkw 0x800c022c41410b08 0xeffc063c41c30f0c

def z54 : W := mkw 0x00777d8001fea000 0x043fd800018c0000

def z55 : W := mkw 0x0000020440010108 0xeb40060c4043030c

def z56 : W := mkw 0x00bbbdfbbc000000 0x14bff9f3be000000

def z57 : W := mkw 0x0000000000000000 0xdb00200f807003f0

def z58 : W := mkw 0x00bbbffffc000000 0xffbffffffe7003f0

def z59 : W := mkw 0x0000000000000000 0xba4027c00073f000

def z60 : W := mkw 0x00bbbffffc000000 0xfefffffffe73f000

def z61 : W := mkw 0x00333fc4c4000000 0x7e3fffcfce000000

def z62 : W := mkw 0x04777fc4c7fff15c 0xff7fffcfcffff3fc

def z63 : W := mkw 0xe02ee03b03f04ee4 0xffffe13fcff0cffc

def z64 : W := mkw 0x4801c9121aa4c4c5 0x1483d9323facccc3

def z65 : W := mkw 0x00911fc4fc000000 0x7a003fcffe000000

def z66 : W := mkw 0x6823e9131ab4c4e5 0x1003e1038e30c0f0

def z67 : W := mkw 0x00bbbdbb38000000 0x04bfd83030000000

def z68 : W := mkw 0x901d9f3e794b0b0a 0xffffdf3e7fcf0f0f

def z69 : W := mkw 0xa0be36ede5500a20 0x083c26cd80500330

def z70 : W := mkw 0x04000244c601515c 0x204007c04e03f00c

def z71 : W := mkw 0xa02e202901500a20 0xcfbc203d81d00f30

def z72 : W := mkw 0x00511d80000ea000 0x20401fc0000ff000

def z73 : W := mkw 0xe07ffdbb01feaea0 0xffffffff81fffff0

def z74 : W := mkw 0x04000244c601515c 0xffc03fffffffffff

def z75 : W := mkw 0x4801c9121aa4c4c5 0xd783c1320fa0ccc0

def z76 : W := mkw 0x00fffffffdfea000 0xfefffffffffff000

def z77 : W := mkw 0xe4044244c7f15ffc 0xfb4027cfcff3fffc

def z78 : W := mkw 0x4c01cb56dea5d5dd 0xffc3ffffffffffff

def z79 : W := mkw 0xe000000000000ea0 0x0100000000000ff0

def z80 : W := mkw 0x04000244c601515c 0x000000004e00000c

def z81 : W := mkw 0x482be93b1aa4c4c5 0xfffff93fffaccccf

def z82 : W := mkw 0x00bbbdbb38000000 0x76bfd9327e000000

def z83 : W := mkw 0x941c166ce74b5b5e 0xfffc3fffffffffff

def z84 : W := mkw 0x0004400001f00000 0x8000000001f00000

def z85 : W := mkw 0xe02fe93b01f48ea0 0xfffff93f81fccff0

def z86 : W := mkw 0x9018162c600b0b0a 0x61c01e3c700f0f0f

def z87 : W := mkw 0x909c967ffd4b0b0a 0xeffc1e3fffcf0f0f

def z88 : W := mkw 0x0000000000000000 0x080026c000533000

def z89 : W := mkw 0x04000244c4011118 0x0000000d80000330

def z90 : W := mkw 0x90bfbffffd4b0b0a 0x7ebffffffe430300

def z91 : W := mkw 0x00a3a9d39c000000 0x1003e1c38e000000

def z92 : W := mkw 0x901c162c614b0b0a 0xfffc3ffc71ffff0f

def z93 : W := mkw 0x0001490000a48000 0xb643d90001acc000

def z94 : W := mkw 0x480080121a0044c5 0x418000327e000ccf

def z95 : W := mkw 0x907e36ac615b2b0a 0xeffc3efc71df3f0f

def z96 : W := mkw 0x00501480000a2000 0x000006c000033000

def z97 : W := mkw 0x00141400014a0000 0xae7c1e0001cf0000

def z98 : W := mkw 0x0063698000b4a000 0x1003e1c00030f000

def z99 : W := mkw 0x00b33fc4fc000000 0x3e3fffc07e000000

def z100 : W := mkw 0x0022a01300000000 0x1003e00380000000

def z101 : W := mkw 0x901c1428214a0a02 0x04bc1830318c0c03

def z102 : W := mkw 0x807f7da801feaa00 0xfffffffc01ffff00

def z103 : W := mkw 0x80bfbffffd400a00 0xffbfffffffc00f00

def z104 : W := mkw 0x4000c01200a00480 0xf7c3d83271ac0ccf

def z105 : W := mkw 0xf01c963f614b0faa 0xeffc1e3ff1cf0fff

def z106 : W := mkw 0x04444244c7fff15c 0xfb4027cfcffff3fc

def z107 : W := mkw 0x4801cb56dea4c4c5 0xffc3ffffffaccccf

def z108 : W := mkw 0x909d1fecfd4b0b0a 0xeffc1ffc7fcf0f0f

def z109 : W := mkw 0x4801c91218a48481 0xe7c3d830718c0c0f

def z110 : W := mkw 0x04333fc4c601515c 0xff7fffcfce73f3fc

def z111 : W := mkw 0x00111d8000000000 0x20001fc000000000

def z112 : W := mkw 0x04ba36ede4011118 0x083c26cd80533330

def z113 : W := mkw 0x0000000000010108 0x814000000043030c

def z114 : W := mkw 0xa02ea03b01500a20 0x5ebfe03f80500330

def z115 : W := mkw 0x4801c91218a48481 0x0483d830318c0c03

def z116 : W := mkw 0x4877fd921bfee4c5 0xfffffff27ffffccf

def z117 : W := mkw 0xf01c562c61fb0faa 0xeffc1e3c71ff0fff

def z118 : W := mkw 0x0000000002004044 0xf34001024e20c0cc

def z119 : W := mkw 0xf83fff3f7bffcfef 0xffffff3fffffcfff

def z120 : W := mkw 0x00373d80014a0000 0xbe7fffc001cf0000

def z121 : W := mkw 0xa02e202901500a20 0xdb3c200f807003f0

def z122 : W := mkw 0xd804400003efcfcf 0x8140000001efcfcf

def z123 : W := mkw 0xd81ddf3e7befcfcf 0xffffdf3e7fefcfcf

def z124 : W := mkw 0x00773d80015ea000 0x287c3fc0005ff000

def z125 : W := mkw 0xe02ea03b01500ea0 0x49bc203f80500ff0

def z126 : W := mkw 0xe0777d8001feaea0 0xbf7fffc001fffff0

def z127 : W := mkw 0x800c002801400a00 0xcfbc003c01c00f00

def z128 : W := mkw 0xe06ee03b01feaea0 0xdfffe03f81fffff0

def z129 : W := mkw 0xa02e602901f00a20 0x9e3fe00d81f00330

def z130 : W := mkw 0xe4bffffffff15ffc 0xfffffffffff3fffc

def z131 : W := mkw 0x90777d8001ffab0a 0xbf7fffc001ffff0f

def z132 : W := mkw 0x00bbbffffc000000 0x24bfdff07e000000

def z133 : W := mkw 0x941c166ce74b5b5e 0xeffc1e3fffcf0fff

def z134 : W := mkw 0xe02ee03b01f00ea0 0x0cbfe03d81d00f30

def z135 : W := mkw 0x00fbbffffc0ea000 0x7efffffffe0ff000

def z136 : W := mkw 0x9088827ffc010b0a 0x4180003ffe000f0f

def z137 : W := mkw 0x0000000000000000 0xd3000002002000c0

def z138 : W := mkw 0x901c1428214a0a02 0xe7fc1830718c0c0f

def z139 : W := mkw 0xe02e602901f00ea0 0x893c200d81f00ff0

def z140 : W := mkw 0x0001891218000000 0xf7c3d9327f8c0c0f

def z141 : W := mkw 0xd805c9121befcfcf 0xf7c3d9327fefcfcf

def z142 : W := mkw 0xe0bffffffdf00ea0 0x7ebfffffff800c00

def z143 : W := mkw 0x0000000000000000 0xb24001000020c000

def z144 : W := mkw 0xe02ee03b01f00ea0 0x85bfc03001f00ff0

def z145 : W := mkw 0x0044400001fea000 0xba4027c001fff000

def z146 : W := mkw 0x04bbbffffc011118 0x7ebffffffe533330

def z147 : W := mkw 0x0001891218000000 0x7683d9327e000000

def z148 : W := mkw 0x08777d801bfee045 0xbe7fffc07ffff00f

def z149 : W := mkw 0x0076748001fea000 0x887c26c001fff000

def z150 : W := mkw 0x90040000014b0b0a 0x0000000000430300

def z151 : W := mkw 0x4800400002a4c4c5 0xe7c0183071accccf

def z152 : W := mkw 0x00bbbffffc000000 0xffffffffff8c0c0f

def z153 : W := mkw 0x941c166ce74b5b5e 0xfb7c27cfce73f3fc

def z154 : W := mkw 0x00bffffffdf00000 0xfebffffffff00000

def z155 : W := mkw 0x48a3e9d39ea4c4c5 0xf7c3f9f3ffaccccf

def z156 : W := mkw 0x00511d80000ea000 0xba403fc0007ff000

def z157 : W := mkw 0x4000c01200a00480 0xd783c03201a00cc0

def z158 : W := mkw 0x00737d8000bea000 0x3043ffc0003ff000

def z159 : W := mkw 0x00000244c6004044 0xfb4027cfce20c0cc

def z160 : W := mkw 0xe8bffffffff4cee5 0xfffffffffffccfff

def z161 : W := mkw 0x04000244c601515c 0xa14007c04e73f3fc

def z162 : W := mkw 0x90fffffffdffab0a 0xffffffffffffff0f

def z163 : W := mkw 0xe07ffdbb01feaea0 0xdfbff83f81fc0ff0

def z164 : W := mkw 0x800c002801400a00 0xdfbc203f81f00ff0

def z165 : W := mkw 0x0000000000000000 0x5a00200f80000000

def z166 : W := mkw 0x4801cb165aa5c5cd 0xffc3df3e7fefcfcf

def z167 : W := mkw 0x90141400014b0b0a 0xaf7c1e0001cf0f0f

def z168 : W := mkw 0x04014b44c6a5d15c 0xff43ffcfcffff3fc

def z169 : W := mkw 0x00991fecfc000000 0x6ebc1ffc7e000000

def z170 : W := mkw 0x10911fc4fc0b010a 0x20401fc07e0f000f

def z171 : W := mkw 0xe02ee03b01f00ea0 0x183fe00f807003f0

def z172 : W := mkw 0x4801c9121aa4c4c5 0x1003c1020e20c0c0

def z173 : W := mkw 0x10101604600b010a 0x20401e00700f000f

def z174 : W := mkw 0x10bbbffffc0b010a 0x7efffffffe0f000f

def z175 : W := mkw 0x4833fd921aa4c4c5 0xfffffff27faccccf

def z176 : W := mkw 0x4877fd921bfee4c5 0xf7ffd9327faccccf

def z177 : W := mkw 0x90141604614b0b0a 0xa1401e0071cf0f0f

def z178 : W := mkw 0x48bbfffffea4c4c5 0x7ebffffffe20c0c0

def z179 : W := mkw 0x0000000002004044 0xfb40210fce70c3fc

def z180 : W := mkw 0x14101644e60b515e 0x20401fc07e0ff00f

def z181 : W := mkw 0x00777d8001fea000 0xae7fde0001cf0000

def z182 : W := mkw 0xe0bffffffdf00ea0 0xffbffffffff00ff0

def z183 : W := mkw 0x00aba9fb9c000000 0x5ebfe1ff8e000000

def z184 : W := mkw 0x04000244c4011118 0xba4027cd8073f330

def z185 : W := mkw 0xe408827fc6015ffc 0x4180003fce000ffc

def z186 : W := mkw 0x04000244c601515c 0x284027cdce53f33c

def z187 : W := mkw 0x00bbbdbb38000000 0x3ebffff030000000

def z188 : W := mkw 0x480080121a0044c5 0x000000020e0000c0

def z189 : W := mkw 0x4801c9121aa4c4c5 0x9143c1020faccccf

def z190 : W := mkw 0x947f7fece7fffb5e 0xffffffffffffffff

def z191 : W := mkw 0x480080121a0044c5 0xf3c001327e20cccf

def z192 : W := mkw 0x04000244c601515c 0xf340010fce20c3fc

def z193 : W := mkw 0x0045490001fea000 0xb643d90001fff000

def z194 : W := mkw 0x1018162c600b010a 0x6efc1e3c700f000f

def z195 : W := mkw 0x080189121a04c045 0x76c3d9327e0cc00f

def z196 : W := mkw 0x00018b56dc000000 0x7e83fffffe000000

def z197 : W := mkw 0x4001c91200a48480 0xf7c3d93201acccc0

def z198 : W := mkw 0x00777d8001fea000 0x847fd80001fff000

def z199 : W := mkw 0x402ae03b00a00480 0xdfbfe03f81a00cc0

def z200 : W := mkw 0x00f7fdd39dfea000 0xbe7fffc38ffff000

def z201 : W := mkw 0xe42ee27fc5f11fb8 0xdfbfe6ff81f33ff0

def z202 : W := mkw 0x002a202900000000 0x083c200d80000000

def z203 : W := mkw 0x90bfbdbb394a0a02 0x04bfd830318c0c03

def z204 : W := mkw 0x00155d0001ee8000 0xbe7fdf0001efc000

def z205 : W := mkw 0x0000020440010108 0x204006004003000c

def z206 : W := mkw 0x0063698000b4a000 0xba43e7c00073f000

def z207 : W := mkw 0xe82fe93b1bf4cee5 0xf7ffd9327faccccf

def z208 : W := mkw 0xe02ee03b01f00ea0 0xffffe7ff81f3fff0

def z209 : W := mkw 0x0001490000a48000 0xf7c3d93071accc0f

def z210 : W := mkw 0x0000000002004044 0x100001020e20c0c0

def z211 : W := mkw 0x00bbbffffc010108 0xfffffffffe43030c

def z212 : W := mkw 0x00777d8001fea000 0x247fdfc0018ff000

def z213 : W := mkw 0xe42ee27fc7f15ffc 0xffffe7ffcff3fffc

def z214 : W := mkw 0xe808803b1a004ee5 0x4180003ffe000fff

def z215 : W := mkw 0x00551d80014ea000 0xae7c1fc001cff000

def z216 : W := mkw 0x0001c91218a48000 0xf6c3d9327facc000

def z217 : W := mkw 0x00101400000a0000 0x20401e00000f0000

def z218 : W := mkw 0x0000000000000000 0x6680183070000000

def z219 : W := mkw 0xd8bfffffffefcfcf 0xffffffffffefcfcf

def z220 : W := mkw 0xe0afe9fb9df00ea0 0xdfbfe1ff8ff00ff0

def z221 : W := mkw 0xe804400003f4cee5 0x8140000001fccfff

def z222 : W := mkw 0x00763480015a2000 0x083c26c000533000

def z223 : W := mkw 0xe0bbbffffc000ea0 0x7fbffffffe000ff0

def z224 : W := mkw 0x00bbbffffe004044 0xfffffffffe20c0cc

def z225 : W := mkw 0x4000c01200a00480 0xdf83e03f81f00ff0

def z226 : W := mkw 0x00000244c4000000 0xfa4027cfce73f000

def z227 : W := mkw 0x00bb3fede4000000 0x3e3fffcd80000000

def z228 : W := mkw 0x901c162c614b0b0a 0x897c060c01cf0f0f

def z229 : W := mkw 0x00e3e9d39cb4a000 0x1003e1c38e30f000

def z230 : W := mkw 0x4cbbfffffea5d5dd 0xffffffffffffffff

def z231 : W := mkw 0x00ba34a920000000 0x003c000000000000

def z232 : W := mkw 0x00777d8001fea000 0x183fe7c00073f000

def z233 : W := mkw 0x0000000000000000 0x0000000000000000

def z234 : W := mkw 0x0000000000000000 0x81400000018c0c0f

def z235 : W := mkw 0x0010140000000000 0x2e3c1e0000000000

def z236 : W := mkw 0x00000244c4000000 0x200007c04e000000

def z237 : W := mkw 0x04000244c601515c 0x490026cfce5333fc

def z238 : W := mkw 0x10101400200a0002 0x00001800300c0003

def z239 : W := mkw 0x04000244c4011118 0xdb0026cf807333f0

def z240 : W := mkw 0xe03ffdbb01f00ea0 0xffbfffff81f00ff0

def z241 : W := mkw 0x0444400003fff15c 0x8140000001fff3fc

def z242 : W := mkw 0xe0bffdbb39f00ea0 0x04bfd83031800c00

def z243 : W := mkw 0x801c162c61400a00 0xefbc1e3c71c00f00

def z244 : W := mkw 0xe02ee03b01f00ea0 0x04bfc03001800c00

def z245 : W := mkw 0x00515d8000aea000 0xb643dfc001aff000

def z246 : W := mkw 0xe408827fc6015ffc 0xfbc027ffce73fffc

def z247 : W := mkw 0x602ae03b00b004a0 0x5ebfe03f803000f0

def z248 : W := mkw 0x00bbbffffc000000 0x0cbffefdb0000000

def z249 : W := mkw 0xb03e362d615b0b2a 0x083c260d80530330

def z250 : W := mkw 0x9008022c60010b0a 0x4180003c70000f0f

def z251 : W := mkw 0xe02aa03b00000ea0 0x5fbfe03f80000ff0

def z252 : W := mkw 0x4827e9121bf4c4c5 0xfffff9327ffccccf

def z253 : W := mkw 0x903f3fac614b0b0a 0xfffffffc71cf0f0f

def z254 : W := mkw 0xd809cb3e7aa5cfcf 0xf7c3d93e7faccfcf

def z255 : W := mkw 0x04fffffffffff15c 0xfffffffffffff3fc

def z256 : W := mkw 0x0000000000000000 0xaa40060000430000

def z257 : W := mkw 0x100002046001010a 0x000000007000000f

def z258 : W := mkw 0x48777d8003fee4c5 0xbf7fffc001fffccf

def z259 : W := mkw 0x0088026de4000000 0x0000000d80000000

def z260 : W := mkw 0x4863e9921ab4e4c5 0x1003e1c20e30f0c0

def z261 : W := mkw 0x94bfbfffff4b5b5e 0xffffffffffffffff

def z262 : W := mkw 0x047636c4c55b3118 0x083c26cd80533330

def z263 : W := mkw 0x4801c9121aa4c4c5 0xf343c1024e20c0cc

def z264 : W := mkw 0x4801490002a4c4c5 0xb743d90001accccf

def z265 : W := mkw 0x042aa27fc601515c 0xffffe7ffce73f3fc

def z266 : W := mkw 0x00777f8441ffa108 0xff7fffcc41fff30c

def z267 : W := mkw 0x00199f3e78000000 0x7ebfdf3e7e000000

def z268 : W := mkw 0x48fffffffffee4c5 0xfffffffffffffccf

def z269 : W := mkw 0x00440000015a2000 0x0000000000533000

def z270 : W := mkw 0xe02ee03b01f00ea0 0x9ebfe03001f00c00

def z271 : W := mkw 0x04911fc4fe01515c 0x20401fc07e03f00c

def z272 : W := mkw 0x6022e01300b004a0 0x0003c00000000000

def z273 : W := mkw 0x4c01c9529ea4d4d5 0xf7c3f9f3ffbcfcff

def z274 : W := mkw 0x0000000000000000 0x804000000073f000

def z275 : W := mkw 0x08511d801a0ee045 0x20401fc07e0ff00f

def z276 : W := mkw 0x040000000201515c 0x004000000003f00c

def z277 : W := mkw 0x08bbbffffe04c045 0x7efffffffe0cc00f

def z278 : W := mkw 0x4801c9121aa4c4c5 0xffc3fff27ffffccf

def z279 : W := mkw 0xe87ffdbb1bfeeee5 0xffffffffffffffff

def z280 : W := mkw 0x00141400014a0000 0x083c060000430000

def z281 : W := mkw 0x9044400001ffab0a 0x8140000001ffff0f

def z282 : W := mkw 0x903e762c61fb0b0a 0xfffffe3c71ff0f0f

def z283 : W := mkw 0x0000020440010108 0x0800060c00430300

def z284 : W := mkw 0x0000000000000000 0x204007c00003f000

def z285 : W := mkw 0x0000000000000000 0x4180003070000c0f

def z286 : W := mkw 0x0026600001f00000 0x9e3fe00001f00000

def z287 : W := mkw 0x04a3abd7de01515c 0xfb43e7cfce73f3fc

def z288 : W := mkw 0x0000801218000000 0x408000327e000000

def z289 : W := mkw 0x00bbbffffc000000 0x44bfd83ffe000000

def z290 : W := mkw 0x9008002820000a02 0x0080003030000c03

def z291 : W := mkw 0x00777d8001fea000 0xff7fffcf81fff3f0

def z292 : W := mkw 0x00777d8001fea000 0xfffffff071fffc0f

def z293 : W := mkw 0x9008022c60010b0a 0xebc0063c70430f0f

def z294 : W := mkw 0x4877fd9219fea481 0x04bfd830318c0c03

def z295 : W := mkw 0x00999ffffc000000 0x60801ffffe000000

def z296 : W := mkw 0x4801c91218a48481 0x7683d9327f8c0c03

def z297 : W := mkw 0x00555d8001fea000 0xa0401fc001fff000

def z298 : W := mkw 0x04511fc4c60ff15c 0xfb403fcfce7ff3fc

def z299 : W := mkw 0x04000244c601515c 0xdb00200fce7003fc

def z300 : W := mkw 0x90be36ede54b0b0a 0x083c26cd80430300

def z301 : W := mkw 0x00733d80000ea000 0x3e7fffc0000ff000

def z302 : W := mkw 0x4000c01202a044c4 0xf7c3c1324fa0cccc

def z303 : W := mkw 0x080109001a04c045 0x204019007e0cc00f

def z304 : W := mkw 0xd01cd63e61eb0f8a 0xffffde3e71ef0fcf

def z305 : W := mkw 0x10777f8461ffa10a 0xbe7fffc071fff00f

def z306 : W := mkw 0x901c162c614b0b0a 0x083c060c00430300

def z307 : W := mkw 0xe004400001f00ea0 0xdb00200f81f00ff0

def z308 : W := mkw 0x00911d8038000000 0x0000180030000000

def z309 : W := mkw 0xe004c01201f00ea0 0xd783c03201f00ff0

def z310 : W := mkw 0x4c00400002a5d5dd 0x8140000001ffffff

def z311 : W := mkw 0xd81ddd3a39ee8e83 0x04bfd830318c0c03

def z312 : W := mkw 0x002aa03b00000000 0x5ebfe03f80000000

def z313 : W := mkw 0x6026e01301f004a0 0x9e3fe00381f000f0

def z314 : W := mkw 0x4c008256de0155dd 0xfbc027fffe73ffff

def z315 : W := mkw 0x00b3bdd39c000000 0x3e3fffc38e000000

def z316 : W := mkw 0x080000000204c045 0x00400000000cc00f

def z317 : W := mkw 0x0036740001fa0000 0xbe7ffe0001ff0000

def z318 : W := mkw 0x901c166ce54b0b0a 0xfffc3fffffcf0f0f

def z319 : W := mkw 0xe02ee03b01f00ea0 0x45bfc03f81800ff0

def z320 : W := mkw 0x8008002800000a00 0x4180003c00000f00

def z321 : W := mkw 0x002aa03b00000000 0xdfbfe03f807003f0

def z322 : W := mkw 0x00763480015a2000 0xae7c3ec001df3000

def z323 : W := mkw 0x04000244c601515c 0xf34007c24e23f0cc

def z324 : W := mkw 0x0008022c60000000 0x4080003c70000000

def z325 : W := mkw 0x900c022c61410b0a 0xcfbc003c71c00f0f

def z326 : W := mkw 0x0018142820000000 0x04bc183030000000

def z327 : W := mkw 0x901c162c614b0b0a 0xeb7c060c4043030c

def z328 : W := mkw 0x907f7da821feaa02 0xbefffff031fffc03

def z329 : W := mkw 0x6823e9131ab4c4e5 0xf7c3f933ffbcccff

def z330 : W := mkw 0x04000244c601515c 0x614007cfce03f3fc

def z331 : W := mkw 0x4801c9121aa4c4c5 0x24c3d9307f8ccc0f

def z332 : W := mkw 0x0c010b44de05d15d 0x20401fc07e0ff00f

def z333 : W := mkw 0xe02ee03b01f00ea0 0xfffff83ff1fc0fff

def z334 : W := mkw 0x4801c9121aa4c4c5 0x4583d8327f8c0ccf

def z335 : W := mkw 0x0044400001fea000 0x00000000018c0000

def z336 : W := mkw 0x901c162c614b0b0a 0x45bc183c718c0f0f

def z337 : W := mkw 0x00898b7ffc000000 0x7683d93ffe000000

def z338 : W := mkw 0x0018162c60000000 0x083c060c00000000

def z339 : W := mkw 0xd81ddf3e79ef8f8b 0xefffde3c71cf0f0f

def z340 : W := mkw 0x00aaa27ffc000000 0x5ebfe03ffe000000

def z341 : W := mkw 0x00141400014a0000 0xbe7c3fc001fff000

def z342 : W := mkw 0x00511d80000ea000 0x00001800000c0000

def z343 : W := mkw 0x4844400003fee4c5 0x8140000001fffccf

def z344 : W := mkw 0x4c004244c6a5d5dd 0xfb4027cfcfffffff

def z345 : W := mkw 0x0418166ce601515c 0xfffc3ffffe73f3fc

def z346 : W := mkw 0xe088827ffc000ea0 0x4180003ffe000ff0

def z347 : W := mkw 0x04000244c601515c 0x7a4027cfce03f00c

def z348 : W := mkw 0x901c162c614b0b0a 0xcfbc063c01c30f00

def z349 : W := mkw 0x907f7fac61ffab0a 0xfffffffc71ffff0f

def z350 : W := mkw 0x6022e01300b004a0 0xdb03e00f807003f0

def z351 : W := mkw 0x907f7fac61ffab0a 0xbe7fffcc01fff300

def z352 : W := mkw 0x0008803b00000000 0x4080003f80000000

def z353 : W := mkw 0x4845c9121bfee4c5 0xf7c3d9327ffffccf

def z354 : W := mkw 0x4801c9121aa4c4c5 0x7683d9327e20c0c0

def z355 : W := mkw 0xe42ee07b87f05ef4 0xdfbfe1ff8ff0fff0

def z356 : W := mkw 0x9408026ce6015b5e 0xfbc027fffe73ffff

def z357 : W := mkw 0x0000004084000000 0x100021c38e000000

def z358 : W := mkw 0x080149001aa4c045 0xb643d9007facc00f

def z359 : W := mkw 0x0000000000000000 0x04801830318c0c03

def z360 : W := mkw 0x00bb3fedfc000000 0x283c3fcdfe000000

def z361 : W := mkw 0xf0bffffffdfb0faa 0xffffffffffff0fff

def z362 : W := mkw 0xe02ee03b01f00ea0 0x14bfe03381b00cf0

def z363 : W := mkw 0x94040000034b5b5e 0x8140000001ffffff

def z364 : W := mkw 0x4800801218000481 0x0080003030000c03

def z365 : W := mkw 0xc80dc93a1be4cec5 0xffffd93e7feccfcf

def z366 : W := mkw 0x4026e01201f00480 0xdfbfe03201f00cc0

def z367 : W := mkw 0x007ffdbb01fea000 0xfeffffff81fff000

def z368 : W := mkw 0x48bbbffffe0044c5 0x7fbffffffe000ccf

def z369 : W := mkw 0x0098967ffc000000 0x6ebc1e3ffe000000

def z370 : W := mkw 0x04636bc4c6b5f15c 0xfb43e7cfce73f3fc

def z371 : W := mkw 0x941c166ce54b1b1a 0xeffc3efdf1df3f3f

def z372 : W := mkw 0x901c162c614b0b0a 0xae7c1e0c01cf0300

def z373 : W := mkw 0x6063e99300b4a4a0 0x1003e1c38030f0f0

def z374 : W := mkw 0x00a3abd7dc000000 0x7a03e7cfce000000

def z375 : W := mkw 0xe404400003f15ffc 0x8140000001f3fffc

def z376 : W := mkw 0x0026600001f00000 0xbe7fe7c001f3f000

def z377 : W := mkw 0xe0bffdbb39f00ea0 0xdfbff83fb1f00ff0

def z378 : W := mkw 0x00773d80015a2000 0x3e3fffc000533000

def z379 : W := mkw 0x0054540001fea000 0xae7c1e0001fff000

def z380 : W := mkw 0x8004000001400a00 0x8100000001c00f00

def z381 : W := mkw 0x04bbbffffe005054 0x7ebffffffe30f0f0

def z382 : W := mkw 0x080109001a04c045 0xf34019027e2cc0cf

def z383 : W := mkw 0x10101604600b010a 0xe7c01e30718f0c0f

def z384 : W := mkw 0x0063698000b4a000 0x0003c00000000000

def z385 : W := mkw 0x0033bd9218000000 0x7ebffff27e000000

def z386 : W := mkw 0x901c162c634b4b4e 0xfffc1f3e7fefcfcf

def z387 : W := mkw 0xa008002900000a20 0x0000000d80000330

def z388 : W := mkw 0xe06fe9bb01f4aea0 0xdfbfe1ff81f0fff0

def z389 : W := mkw 0x0400000000011118 0x0000000000533330

def z390 : W := mkw 0x00777d8003fee044 0xff7fffc24ffff0cc

def z391 : W := mkw 0x00bbbdbb38000000 0x5ebff83fb0000000

def z392 : W := mkw 0xe07ffdbb01feaea0 0xbefffff001fffc00

def z393 : W := mkw 0x00000244c4000000 0x4000000fce000000

def z394 : W := mkw 0xec2feb7fdff5dffd 0xffffffffffffffff

def z395 : W := mkw 0x4801c9121aa4c4c5 0xffc3f93ffffccfff

def z396 : W := mkw 0x901c162c614b0b0a 0x24fc1e30718f0c0f

def z397 : W := mkw 0xb03e362d615b0b2a 0xeffc3e3df1df0f3f

def z398 : W := mkw 0x0000000002004044 0x814000000020c0cc

def z399 : W := mkw 0x4800c01202a4c4c5 0xd7c3c03201accccf

def z400 : W := mkw 0x0001490000a48000 0x1003c1000020c000

def z401 : W := mkw 0x0018162c60000000 0xeffc1e3c718c0c0f

def z402 : W := mkw 0x0010160460000000 0x20001e0070000000

def z403 : W := mkw 0x00bbbffffc000000 0x183fe7cf8e000000

def z404 : W := mkw 0x0076748001fa2000 0x9e3fe6c001f33000

def z405 : W := mkw 0x00919fd6fc000000 0x7683dff27e000000

def z406 : W := mkw 0xe0fffffffdfeaea0 0xfffffffffffffff0

def z407 : W := mkw 0x04141644c74b515c 0xff7c3fcfcffff3fc

def z408 : W := mkw 0x008080539c000000 0x000000038e000000

def z409 : W := mkw 0x0001490000a48000 0x0403d800018c0000

def z410 : W := mkw 0x004109800004a000 0x000001c00000f000

def z411 : W := mkw 0x0000000000000000 0x720001024e000000

def z412 : W := mkw 0x4800400002a4c4c5 0xf34001024faccccf

def z413 : W := mkw 0xa07f7da901feaa20 0xbe7fffcd81fff330

def z414 : W := mkw 0xf004400001fb0faa 0x8140000001ff0fff

def z415 : W := mkw 0x0088803b38000000 0x0080003030000000

def z416 : W := mkw 0x00377d8001f00000 0xbe3fffc001f00000

def z417 : W := mkw 0x080109001a04c045 0xe7c019307f8ccc0f

def z418 : W := mkw 0x04777fc4c7fff15c 0xbe7fffc04ffff00c

def z419 : W := mkw 0x002ba93b18000000 0x7ebff93ffe000000

def z420 : W := mkw 0x802e602801f00a00 0xdfbfe03c01f00f00

def z421 : W := mkw 0xe02ee27fc5f00ea0 0xffbfe7ffcff00ff0

def z422 : W := mkw 0x00141604414b0108 0xef7c1e0c41cf030c

def z423 : W := mkw 0x903eb63f614b0b0a 0xfffffe3ff1cf0f0f

def z424 : W := mkw 0x04bbbffffe01515c 0x7fbffffffe0003fc

def z425 : W := mkw 0x4801c9121aa4c4c5 0xb643d9020facc0c0

def z426 : W := mkw 0x941c166ce54b1b1a 0x083c26cd80533330

def z427 : W := mkw 0xa42e226dc5511b38 0x083c26cd80533330

def z428 : W := mkw 0x4000c01200a00480 0x1003c002002000c0

def z429 : W := mkw 0x981d1f2c7b4fcb4f 0xeffc1f3c7fcfcf0f

def z430 : W := mkw 0x0000020440010108 0xfb40260fc07303fc

def z431 : W := mkw 0x0022200000000000 0x1e3fe00000000000

def z432 : W := mkw 0x003b3fac60000000 0x7ebffffc70000000

def z433 : W := mkw 0x0001891218000000 0x0483d83030000000

def z434 : W := mkw 0x4c01c9529ea4d4d5 0x1003e1c38e30f0f0

def z435 : W := mkw 0x4801c91218a48481 0x0003c00000000000

def z436 : W := mkw 0x901c162c614b0b0a 0xfffc3e3ff1ff0fff

def z437 : W := mkw 0x04000244c601515c 0xeb4007cc4e43f30c

def z438 : W := mkw 0xe82ee03b1bf04ee5 0xdfbfe03ffff00fff

def z439 : W := mkw 0x00bfbffffd4a0000 0xfeffffffffcf0000

def z440 : W := mkw 0x4c01cb56dea5d5dd 0xfb43e7cfce73f3fc

def z441 : W := mkw 0x4801c9121aa4c4c5 0x3043d9027e2cc0cf

def z442 : W := mkw 0x00fbfffffcb4a000 0x7ebffffffe30f000

def z443 : W := mkw 0x0077fd9219fea000 0xfefffff27ffff000

def z444 : W := mkw 0x0000020440010108 0xfb4027cc4073f30c

def z445 : W := mkw 0x00a3a9d39c000000 0x7683f9f3fe000000

def z446 : W := mkw 0x00777d8001fea000 0x3e3fffc0018c0000

def z447 : W := mkw 0x90be36ede54b0b0a 0xeffc3efdf1cf0f0f

def z448 : W := mkw 0x040000000201515c 0xdb40200f8073f3fc

def z449 : W := mkw 0x00000244c4000000 0xfb0027cfce7003f0

def z450 : W := mkw 0x002aa27fc4000000 0x7ebfe7ffce000000

def z451 : W := mkw 0x901c162c614a0a02 0x6ebc1e3c718c0c03

def z452 : W := mkw 0xe82fe93b19f48ea1 0xdfbff83fb1fc0ff3

def z453 : W := mkw 0x04000244c601515c 0x180027cf8e73f3f0

def z454 : W := mkw 0xe044400001feaea0 0x8140000001fffff0

def z455 : W := mkw 0x4888827ffe0044c5 0x4180003ffe000ccf

def z456 : W := mkw 0x04000244c4011118 0x7a0027cfce533330

def z457 : W := mkw 0x14101644e60b515e 0xfb403fcffe7ff3ff

def z458 : W := mkw 0xe008c03b00a00ea0 0xd783c03f81a00ff0

def z459 : W := mkw 0x4000c01200a00480 0x0483c03001800c00

def z460 : W := mkw 0x801c1428014a0a00 0xeffc1e3c01cf0f00

def z461 : W := mkw 0x10141604614b010a 0xae7c1e0071cf000f

def z462 : W := mkw 0x4800400002a4c4c5 0x000000000020c0c0

def z463 : W := mkw 0x00777d8001fea000 0x143ff9c001bcf000

def z464 : W := mkw 0x4851dd921aaee4c5 0xf7c3dff27faffccf

def z465 : W := mkw 0x00777fc4c5fea000 0xfe7fffcfcffff000

def z466 : W := mkw 0xf008823f60010faa 0x4180003ff0000fff

def z467 : W := mkw 0x007f7fac61fea000 0xfefffffc71fff000

def z468 : W := mkw 0x10000000000b010a 0x00400000000f000f

def z469 : W := mkw 0x0000000002004044 0xfb4027c24e73f0cc

def z470 : W := mkw 0x04a3a9d39e005054 0x1003e1c38e30f0f0

def z471 : W := mkw 0xe026e01301f00ea0 0x9103e00381f00ff0

def z472 : W := mkw 0x040002044201515c 0xeb40060c4073f3fc

def z473 : W := mkw 0xe02ee03b01f00ea0 0xcfbfc03c01c00f00

def z474 : W := mkw 0x00d11fc4fc0ea000 0x20401fc07e0ff000

def z475 : W := mkw 0x90bfbffffd4a0a02 0x7ebfffffff8c0c03

def z476 : W := mkw 0x00400000000ea000 0x00400000000ff000

def z477 : W := mkw 0x0000000000000000 0x20401800700c000f

def z478 : W := mkw 0xe82fe93b19f48ea1 0x04bfd830318c0c03

def z479 : W := mkw 0x4889cb7ffea4c4c5 0xf7c3d93fffaccccf

def z480 : W := mkw 0x4c01c9121aa5d5dd 0xf7c3d9327fffffff

def z481 : W := mkw 0x480189121a04c4c5 0x61c019327e0ccccf

def z482 : W := mkw 0x04777fc4c5ffb118 0xbe7fffcd81fff330

def z483 : W := mkw 0x00763480015a2000 0xba7c27c00073f000

def z484 : W := mkw 0x04000244c4011118 0xeb4026cdc053333c

def z485 : W := mkw 0x04777d8003fff15c 0xbf7fffc001fff3fc

def z486 : W := mkw 0x802ea03b01400a00 0xdfbfe03f81c00f00

def z487 : W := mkw 0xf43ef67fe7fb5ffe 0xffffffffffffffff

def z488 : W := mkw 0x0001090000048000 0x20401900000cc000

def z489 : W := mkw 0x901c1428214a0a02 0x003c000000000000

def z490 : W := mkw 0x0000000000000000 0xfb4027cf8073f3f0

def z491 : W := mkw 0x00000244c4000000 0x080026cd80000000

def z492 : W := mkw 0x90040000014b0b0a 0xe7c0183071cf0f0f

def z493 : W := mkw 0x4819df3e7aa4c4c5 0xffffdf3e7faccccf

def z494 : W := mkw 0x18111f047a0fc14f 0x20401f007e0fc00f

def z495 : W := mkw 0x00800244fc000000 0x000000007e000000

def z496 : W := mkw 0xe008803b00000ea0 0x0080003000000c00

def z497 : W := mkw 0x009016c4e4000000 0x000006c000000000

def z498 : W := mkw 0xc00cc03a01e00e80 0xdfbfc03e01e00fc0

def z499 : W := mkw 0x00333d8000000000 0xbe7fffc00073f000

def z500 : W := mkw 0x00ababfffc000000 0x5083e1fffe000000

def z501 : W := mkw 0x00ff7fede5fea000 0xbe7fffcd81fff000

def z502 : W := mkw 0x00ba36ede4000000 0x6ebc3efdf0000000

def z503 : W := mkw 0x0023298000000000 0x1003e1c000000000

def z504 : W := mkw 0x0000400000a48000 0x8040000001acc000

def z505 : W := mkw 0x0000000000000000 0x0800200d80500330

def z506 : W := mkw 0x04bbbffffe01515c 0x7efffffffe03f00c

def z507 : W := mkw 0x6077fd9301fea4a0 0xbe7fffc381fff0f0

def z508 : W := mkw 0x6022e01300b004a0 0xd783e03381b00cf0

def z509 : W := mkw 0x4001c91218a00480 0xf783d9327fa00cc0

def z510 : W := mkw 0xf07fffbf61ffafaa 0xfffffffff1ffffff

def z511 : W := mkw 0x90bbbffffc010b0a 0x7fbffffffe000f0f

def z512 : W := mkw 0xdc1ddf7effefdfdf 0xffffffffffffffff

def z513 : W := mkw 0x941c166ce74b5b5e 0xeffc1ffc7fcfff0f

def z514 : W := mkw 0x905d1fac614fab0a 0xeffc1ffc71cfff0f

def z515 : W := mkw 0x0400004086005054 0x000001c00e00f000

def z516 : W := mkw 0x04911fc4fe01515c 0xfb403fcffe73f3fc

def z517 : W := mkw 0x9000000000010b0a 0x0100000000000f0f

def z518 : W := mkw 0x48bbfdbb3aa4c4c5 0xf7ffd9327faccccf

def z519 : W := mkw 0x4877fd9219fea481 0xbefffff031fffc03

def z520 : W := mkw 0x6422e257c6b155fc 0xfb43e7cfce73f3fc

def z521 : W := mkw 0x900c0028014b0b0a 0xcffc003c01cf0f0f

def z522 : W := mkw 0x04511fc4c60ff15c 0x20401fc04e0ff00c

def z523 : W := mkw 0xf03ef43b21fa0ea2 0xdfbff83fb1fc0ff3

def z524 : W := mkw 0x840c026cc7415b5c 0xfffc27ffcff3fffc

def z525 : W := mkw 0x00a220c184000000 0x000020c180000000

def z526 : W := mkw 0x0801090018048001 0x00001800300c0003

def z527 : W := mkw 0x0026600001f00000 0x043fc00001800000

def z528 : W := mkw 0x901c162c614b0b0a 0x49bc063c70430f0f

def z529 : W := mkw 0x4c77ffd6dffff5dd 0xffffffffffffffff

def z530 : W := mkw 0x905c562c61ffab0a 0xeffc1e3c71ffff0f

def z531 : W := mkw 0x60bbfffffcb004a0 0x7ebffffffe3000f0

def z532 : W := mkw 0xe0aee27ffdf00ea0 0xdfbfe03ffff00ff0

def z533 : W := mkw 0xe026600001f00ea0 0x9f3fe00001f00ff0

def z534 : W := mkw 0x040000000201515c 0x01000000000003fc

def z535 : W := mkw 0x046369c086b4f054 0x1003e1c38e30f0f0

def z536 : W := mkw 0xd808823e7a014fcf 0x4180003e7e000fcf

def z537 : W := mkw 0x9018162c60010b0a 0x6fbc1e3c70000f0f

def z538 : W := mkw 0x9008022c60010b0a 0xe7c0183c718c0f0f

def z539 : W := mkw 0x5811df167aafc5cf 0xf7c3df327fafcccf

def z540 : W := mkw 0xe00cc03b01f00ea0 0xc180003f81f00ff0

def z541 : W := mkw 0x0040400000b4a000 0x000000000030f000

def z542 : W := mkw 0x0000400000a00000 0x9603c00001a00000

def z543 : W := mkw 0x4800400000a48481 0x00000000018c0c03

def z544 : W := mkw 0x0400000002005054 0x000000000030f0f0

def z545 : W := mkw 0xe42ee03b03f15ffc 0xdfffe03f81f3fffc

def z546 : W := mkw 0x0001490002a4c044 0xf743d9024facc0cc

def z547 : W := mkw 0x00b3bfd7fc000000 0x3003ffc3fe000000

def z548 : W := mkw 0x10511f84600fa10a 0x20401fc0700ff00f

def z549 : W := mkw 0xe03ef63f61f00ea0 0xffbffe3ff1f00ff0

def z550 : W := mkw 0x0066600001fea000 0x9e7fe00001fff000

def z551 : W := mkw 0xf03ef43b21fa0ea2 0x04bfd830318c0c03

def z552 : W := mkw 0xd87fffbe7bffefcf 0xfffffffe7fffffcf

def z553 : W := mkw 0x480080121a0044c5 0xe7c018327f8c0ccf

def z554 : W := mkw 0x00f77fc4fdfea000 0xbe7fffc07ffff000

def z555 : W := mkw 0x4877fd921bfee4c5 0xbe7fffc20ffff0c0

def z556 : W := mkw 0x04000244c601515c 0x304027c3ce33f0fc

def z557 : W := mkw 0xe004400001f00ea0 0x0000000001800c00

def z558 : W := mkw 0x0400004084001010 0x000020c180103030

def z559 : W := mkw 0x0027690001f48000 0xbe7ff90001fcc000

def z560 : W := mkw 0x4801c91218a48481 0xb6c3d93031accc03

def z561 : W := mkw 0x90040000014a0a02 0x00000000018c0c03

def z562 : W := mkw 0x0000000000000000 0xe34000004000000c

def z563 : W := mkw 0x00777d8001fea000 0xb67fd90001acc000

def z564 : W := mkw 0x90040204414b0b0a 0xeb40060c41cf0f0f

def z565 : W := mkw 0xe82ee03b03f4cee5 0xdfffe03f81fccfff

def z566 : W := mkw 0x40bbfffffca00480 0xffbfffffffa00cc0

def z567 : W := mkw 0x00bab6ffe4000000 0x5ebfe6ff80000000

def z568 : W := mkw 0xd81c562c63efcfcf 0xeffc1e3c71efcfcf

def z569 : W := mkw 0x00fe36ede55a2000 0x083c26cd80533000

def z570 : W := mkw 0x901c1428214a0a02 0xaefc1e3031cf0c03

def z571 : W := mkw 0xf02ee03b01fb0faa 0xdfffe03f81ff0fff

def z572 : W := mkw 0x901c162c614b0b0a 0x0cbc1e3c31cf0f03

def z573 : W := mkw 0x480189121a0044c5 0x7783d9327e000ccf

def z574 : W := mkw 0x0000020440010108 0x4100000c4000030c

def z575 : W := mkw 0x00777d8001fea000 0x9e3ff80001fc0000

def z576 : W := mkw 0x4815dd121beec4c5 0xffffdf327fefcccf

def z577 : W := mkw 0x0400004086005054 0xba4027c38e73f0f0

def z578 : W := mkw 0xa02e202901500a20 0x003c000000000000

def z579 : W := mkw 0x0001891218000000 0x1003c1020e000000

def z580 : W := mkw 0x0063698000b4a000 0xb643f9c001bcf000

def z581 : W := mkw 0x002ee03b01f00000 0xdebfe03f81f00000

def z582 : W := mkw 0xe47fffffc7fffffc 0xffffffffcffffffc

def z583 : W := mkw 0x04000244c601515c 0xeb40060fce4303fc

def z584 : W := mkw 0xe00c803b01400ea0 0xcfbc003f81c00ff0

def z585 : W := mkw 0x001c162c614a0000 0xeefc1e3c71cf0000

def z586 : W := mkw 0x4801c9121aa4c4c5 0x5183c1327e20cccf

def z587 : W := mkw 0x00337d8000a48000 0xbe7fffc001acc000

def z588 : W := mkw 0x000002044201414c 0xfb40070e4e63c3cc

def z589 : W := mkw 0xa0bfbffffd500a20 0x7ebffffffe500330

def z590 : W := mkw 0x04000244c601515c 0x7b0027cfce0003fc

def z591 : W := mkw 0x6000400000b004a0 0x00000000003000f0

def z592 : W := mkw 0xf03ef63f61fb0faa 0xdfbfe63f81f30ff0

def z593 : W := mkw 0x040000000201515c 0xbb4027c00073f3fc

def z594 : W := mkw 0x080000001a004045 0x000000007e00000f

def z595 : W := mkw 0x94040244c74b5b5e 0xfb4027cfcfffffff

def z596 : W := mkw 0x4801c9121aa4c4c5 0x85c3d83031accccf

def z597 : W := mkw 0x4000400000a00480 0x8100000001a00cc0

def z598 : W := mkw 0x4801c91218a48481 0xd783d83231ac0cc3

def z599 : W := mkw 0x003bbdbb00000000 0x7ebfffff80000000

def z600 : W := mkw 0x48bbfdbb38a48481 0x04bfd830318c0c03

def z601 : W := mkw 0xe02fe93b19f00ea0 0xffbff93ffff00ff0

def z602 : W := mkw 0x040000000201515c 0xf34001024e73f3fc

def z603 : W := mkw 0x04000244c6005054 0x7a0027cfce30f0f0

def z604 : W := mkw 0xe02ee23f41f10fa8 0xffffe63fc1f30ffc

def z605 : W := mkw 0x040000408601515c 0x914021c38e73f3fc

def z606 : W := mkw 0x480149001aa4c4c5 0xa14019007faccccf

def z607 : W := mkw 0x0000000000000000 0xc780003001800c00

def z608 : W := mkw 0x0000000002004044 0x410000024e0000cc

def z609 : W := mkw 0x941c162c634b5b5e 0xeffc1e3c71ffffff

def z610 : W := mkw 0x00fffffffdfea000 0x7ebfffffff8c0000

def z611 : W := mkw 0x907f7da821feaa02 0x04bfd830318c0c03

def z612 : W := mkw 0x00fffdbb39fea000 0xbefffff031fff000

def z613 : W := mkw 0x04018b56de01515c 0xffc3fffffe73f3fc

def z614 : W := mkw 0x04ba36ede601515c 0xfb7c27cfce73f3fc

def z615 : W := mkw 0x0008002800000000 0x4ebc003c00000000

def z616 : W := mkw 0x0000000002004044 0x204001004e00c00c

def z617 : W := mkw 0x907e36ac615b2b0a 0x083c26cc00533300

def z618 : W := mkw 0x04000244c601515c 0x894026cd8073f3fc

def z619 : W := mkw 0x4c01cb56dea5d5dd 0xf7c3dff27faffccf

def z620 : W := mkw 0x0026200001500000 0x083c200000500000

def z621 : W := mkw 0x4000801200000480 0x4180003200000cc0

def z622 : W := mkw 0xe02ae03b00b00ea0 0x5183e03f80300ff0

def z623 : W := mkw 0xe0bef6ffe5f00ea0 0xdfbfe6ff81f00ff0

def z624 : W := mkw 0x04000244c601515c 0xc140000fce73f3fc

def z625 : W := mkw 0x0488827ffe01515c 0xfbc027fffe73f3fc

def z626 : W := mkw 0x00763480015a2000 0x003c000000000000

def z627 : W := mkw 0xe00c402801f00ea0 0xcfbc003c01f00ff0

def z628 : W := mkw 0x0000000000000000 0xcb00000c00400300

def z629 : W := mkw 0x04266244c7f1515c 0xff7fe7cfcff3f3fc

def z630 : W := mkw 0x0067698001fea000 0x9043e1c001fff000

def z631 : W := mkw 0x0400004086005054 0xf34021c3ce30f0fc

def z632 : W := mkw 0x0000000000000000 0xa6401800018c0000

def z633 : W := mkw 0x04000244c601515c 0x510021cfce30f3fc

def z634 : W := mkw 0x0000000000000000 0x4100000f800003f0

def z635 : W := mkw 0xa42e226dc7515b7c 0xfb7c27cfce73f3fc

def z636 : W := mkw 0x0000000000000000 0x81000000007003f0

def z637 : W := mkw 0x10101604600b010a 0x0000060000030000

def z638 : W := mkw 0xe03ef43b01fa0ea0 0xfffffe3f81ff0ff0

def z639 : W := mkw 0xe02ee03b01f00ea0 0x5ebfe03f81800c00

def z640 : W := mkw 0x901c1428214a0a02 0xcfbc183c31cc0f03

def z641 : W := mkw 0x4400c256c6a155dc 0xffc3e7ffcff3fffc

def z642 : W := mkw 0x48bbfffffca48481 0x7ebfffffff8c0c03

def z643 : W := mkw 0xe82fe93b1bf4cee5 0xdfbfe13f8ff0cff0

def z644 : W := mkw 0x0067698001f4a000 0x9e3fe1c001f0f000

def z645 : W := mkw 0x0000000000000000 0x9a00200000700000

def z646 : W := mkw 0x907f7fac61ffab0a 0xefffde3c71cf0f0f

def z647 : W := mkw 0x901d5f2c61ef8b0a 0xffffdf3c71efcf0f

def z648 : W := mkw 0x0022600000b00000 0x1003e00000300000

def z649 : W := mkw 0x9408026ce6015b5e 0x4180003ffe000fff

def z650 : W := mkw 0x00141400014a0000 0x043c1800018c0000

def z651 : W := mkw 0xf02ee23f61f10faa 0xdfbfe03ff1f00fff

def z652 : W := mkw 0x00737d8000b4a000 0x3e3fffc00030f000

def z653 : W := mkw 0xe02ee03b01f00ea0 0xd7bfc03201a00cc0

def z654 : W := mkw 0x0062208000102000 0x000020c000103000

def z655 : W := mkw 0x0000000000000000 0x3a0027c000000000

def z656 : W := mkw 0x04000244c601515c 0xba4027c04e73f00c

def z657 : W := mkw 0x0000000000000000 0x10002003803000f0

def z658 : W := mkw 0x4077fd9201fea480 0xfffffff201fffcc0

def z659 : W := mkw 0x0032348000000000 0x083c26c000000000

def z660 : W := mkw 0xe809c93b1aa4cee5 0xf7c3d93fffaccfff

def z661 : W := mkw 0x901c162c614b0b0a 0x6ebc1e3c70430300

def z662 : W := mkw 0x60a3e9d39cb004a0 0x1003e1c38e3000f0

def z663 : W := mkw 0x0400004086005054 0xdb0021cf8e70f3f0

def z664 : W := mkw 0x60008013000004a0 0x00000003800000f0

def z665 : W := mkw 0x08911fc4fe04c045 0x20401fc07e0cc00f

def z666 : W := mkw 0x0000000002004044 0xf7c019327faccccf

def z667 : W := mkw 0x0000000000000000 0x100021c00030f000

def z668 : W := mkw 0xe805c9121bf4cee5 0xf7c3d9327ffccfff

def z669 : W := mkw 0x2022200100100020 0x0000200180100030

def z670 : W := mkw 0x080109001a04c045 0x000001000e00c000

def z671 : W := mkw 0xe07ffdbb01feaea0 0x04bfd830018c0c00

def z672 : W := mkw 0x00bbbfbf78000000 0x6ebfde3c70000000

def z673 : W := mkw 0x00040000014a0000 0x8040000001cf0000

def z674 : W := mkw 0xd81c963e7b4b4fcf 0xeffc1e3e7fcf0fcf

def z675 : W := mkw 0x6422e05386b054f4 0x1003e1c38e30f0f0

def z676 : W := mkw 0xe008803b00000ea0 0xdb80203f80700ff0

def z677 : W := mkw 0x00ba36ede4000000 0x7a3c27cfce000000

def z678 : W := mkw 0xa07e34a9015a2a20 0x083c26cd80533330

def z679 : W := mkw 0x008109c09c000000 0x000001c00e000000

def z680 : W := mkw 0x48000000020044c5 0x0100000000000ccf

def z681 : W := mkw 0x4800c0121aa044c5 0xd783c0327fa00ccf

def z682 : W := mkw 0xd81ddd3a3beecec7 0xf7ffd9327faccccf

def z683 : W := mkw 0x0088827ffc000000 0x7a8027fffe000000

def z684 : W := mkw 0x10101604600b010a 0xeb401e0c704f030f

def z685 : W := mkw 0x003ab63f60000000 0x7ebffe3ff0000000

def z686 : W := mkw 0x0400004086005054 0x000000038e0000f0

def z687 : W := mkw 0x900c022c614b0b0a 0xc1c0003c71cf0f0f

def z688 : W := mkw 0x0004000001400000 0x8e3c000001c00000

def z689 : W := mkw 0x0001090000000000 0x3603d90000000000

def z690 : W := mkw 0x00bab6fffc000000 0x48bc26fffe000000

def z691 : W := mkw 0xa004000001500a20 0x0000000000500330

def z692 : W := mkw 0x4891dfd6fea4c4c5 0xf7c3dff27faccccf

def z693 : W := mkw 0x9008022c60010b0a 0x0000000c00000300

def z694 : W := mkw 0x0000020440000000 0x6a00060c40000000

def z695 : W := mkw 0x0018162c60010108 0xeffc1e3c7043030c

def z696 : W := mkw 0xf03ef63f61fb0faa 0xefffde3c71cf0f0f

def z697 : W := mkw 0x00333d8000000000 0x043fd80000000000

def z698 : W := mkw 0x00777d8001fea000 0x0c3ffec001df3000

def z699 : W := mkw 0x0001490000a48000 0xbe43ffc001fff000

def z700 : W := mkw 0x4c008256de0155dd 0x4180003ffe000fff

def z701 : W := mkw 0x90bfbfbf794b0b0a 0xefffde3c71cf0f0f

def z702 : W := mkw 0x00a3a99318000000 0x0003c00000000000

def z703 : W := mkw 0x04000244c4011118 0x000006c000033000

def z704 : W := mkw 0x0000801200000000 0x5683c03200000000

def z705 : W := mkw 0x00fffdbb39fea000 0x04bfd830318c0000

def z706 : W := mkw 0x901c162c614b0b0a 0x287c1e0c704f030f

def z707 : W := mkw 0x04000244c601515c 0xdb0027cf8e73f3f0

def z708 : W := mkw 0xe06ee03b01feaea0 0xdfbfe03f81fc0ff0

def z709 : W := mkw 0xe0777d8001feaea0 0xff7fffcf81fffff0

def z710 : W := mkw 0x480189121a0044c5 0xf7c3d9327f8c0ccf

def z711 : W := mkw 0x080149001aa4c045 0xf7c3d9307faccc0f

def z712 : W := mkw 0x7032f61760bb05aa 0x3043fe03f03f00ff

def z713 : W := mkw 0x4801c9121aa4c4c5 0x0483d8307f8c0c0f

def z714 : W := mkw 0x901c162c614b0b0a 0xe7fc1e30718f0c0f

def z715 : W := mkw 0xe42ee27fc7f15ffc 0x24ffc7f04f83fc0c

def z716 : W := mkw 0x4801c9121aa4c4c5 0xe7c3d8327f8c0ccf

def z717 : W := mkw 0x801c1428014a0a00 0xeffc1e3c71cf0f0f

def z718 : W := mkw 0x602ae03b00b004a0 0xdfbfe03f807003f0

def z719 : W := mkw 0xdc08827efe015fdf 0x4180003ffe000fff

def z720 : W := mkw 0x941c1468a74a5a56 0x14bc39f3bfbcfcf3

def z721 : W := mkw 0x002aa03b00000000 0x5fbfe03f800003f0

def z722 : W := mkw 0x00333d8000000000 0x7e3fffc24e000000

def z723 : W := mkw 0x10bbbffffc0b010a 0xffffffffff8f0c0f

def z724 : W := mkw 0x900c0028014b0b0a 0xeffc183c71cf0f0f

def z725 : W := mkw 0x00bbbffffc000000 0x383fffcffe000000

def z726 : W := mkw 0x901c1428214a0a02 0xeffc1e3071cf0c0f

def z727 : W := mkw 0x08777d8019fea001 0xbe7fffc031fff003

def z728 : W := mkw 0xe02ee03b01f00ea0 0x8dbfe03d81f00ff0

def z729 : W := mkw 0x941c162c614b1b1a 0xeffc1e3c71df3f3f

def z730 : W := mkw 0x4801c9121aa4c4c5 0xe7c3d9307f8ccc0f

def z731 : W := mkw 0x04bbbdbb3a01515c 0x85ffd8303073f3fc

def z732 : W := mkw 0xec08827fde015ffd 0x4180003ffe000fff

def z733 : W := mkw 0x901c162c614a0a02 0xeffc1e3c718c0c0f

def z734 : W := mkw 0x04000244c601515c 0xfbc027fffe73ffff

def z735 : W := mkw 0x00bbbdbb38000000 0x44bfd8327e000000

def z736 : W := mkw 0x60bbbffffc0004a0 0x7ebffffffe0000f0

def z737 : W := mkw 0x00bbbffffc010108 0x7ebffffffe430300

def z738 : W := mkw 0xe02ee03b01f00ea0 0xdb3fe00f807003f0

def z739 : W := mkw 0x906b6bac60b5ab0a 0x5183e1fc7030ff0f

def z740 : W := mkw 0x00f77d8039fea000 0xbe7fffc031fff000

def z741 : W := mkw 0x4801c9121aa4c4c5 0xf7c3d9327ffffccf

def z742 : W := mkw 0x00bbbfbf78000000 0x7ebfdf3e7e000000

def z743 : W := mkw 0xa0bbbffffc000a20 0x7ebffffffe000330

def z744 : W := mkw 0x0008002800000000 0xeffc183c718c0c0f

def z745 : W := mkw 0x00b33fc4fc000000 0x243fdfc07e000000

def z746 : W := mkw 0x901c162c614b0b0a 0xa5fc1e3071cf0f0f

def z747 : W := mkw 0x48ba76ede6a4c4c5 0x897c26cd81accccf

def z748 : W := mkw 0x801c162c61400a00 0xeffc1e3c71cc0f0f

def z749 : W := mkw 0x00bbbdfbbc000000 0x5ebff9ffbe000000

def z750 : W := mkw 0xd81ddf3e7befcfcf 0x183fc70e0e63c3c0

def z751 : W := mkw 0x901c1428214b0b0a 0x05bc1830318c0f0f

def z752 : W := mkw 0x900c022c61410b0a 0xeffc183c71cc0f0f

def z753 : W := mkw 0xf02ee03b01fa0ea2 0xdfbfe03f81fc0ff3

def z754 : W := mkw 0x905c162c615b2b0a 0xeffc1e3c71df3f0f

def z755 : W := mkw 0x00bbbdbb38000000 0x7ebffff27e000000

def z756 : W := mkw 0x4876b4921b5a64c5 0x49bc26f27e533ccf

def z757 : W := mkw 0xb01c162c615b0b2a 0xeffc1e3c71df0f3f

def z758 : W := mkw 0x4801c9121aa4c4c5 0xc5c3d8327faccccf

def z759 : W := mkw 0x00777d8001fea000 0xbe7fffcd81fff330

def z760 : W := mkw 0xe02ee03b01f00ea0 0xffbfe7ff81f00ff0

def z761 : W := mkw 0x90a7a9d39d4b0b0a 0x9143e1c38fcf0f0f

def z762 : W := mkw 0x00fbbffffc102000 0x7ebffffffe103000

def z763 : W := mkw 0x905c16ac614b2b0a 0xeffc1efc71cf3f0f

def z764 : W := mkw 0x901c162c614b0b0a 0xeffc1ffc71cfff0f

def z765 : W := mkw 0x4801c9121aa4c4c5 0xffc3f9327ffccccf

def z766 : W := mkw 0x00337d8000a48000 0xbe7fffc001fff000

def z767 : W := mkw 0x0067698001f4a000 0xbe7fe7c001f3f000

def z768 : W := mkw 0x00bbbffffc000000 0x4cbffefffe000000

def z769 : W := mkw 0xf404400003fb5ffe 0x8140000001ffffff

def z770 : W := mkw 0x00333dc084000000 0x3e3fffc38e000000

def z771 : W := mkw 0x00bbbffffc000000 0x6ebfdffc7e000000

def z772 : W := mkw 0x00373d80014a0000 0xbe7fffc001fff000

def z773 : W := mkw 0x14911fc4fe0b515e 0x20401fc07e0ff00f

def z774 : W := mkw 0x00aba9fb9c000000 0x183fe1cf8e000000

def z775 : W := mkw 0x90bbbffffc0b0b0a 0x7ffffffffe0f0f0f

def z776 : W := mkw 0xe02ee03b01f00ea0 0xdfbfe6ff81f33ff0

def z777 : W := mkw 0x00777d8001fea000 0x2c7fffc001dff000

def z778 : W := mkw 0x04bbbffffc001010 0x7ebffffffe103030

def z779 : W := mkw 0x00bbbffffc000000 0x5ebff83ffe000000

def z780 : W := mkw 0x00bbbffffc000000 0x7fbffffffe0003f0

def z781 : W := mkw 0x4c01cb56dca59599 0x0c83fefdb1df3f33

def z782 : W := mkw 0x901c162c614b0b0a 0xcfbc183c71cc0f0f

def z783 : W := mkw 0x002ba93b18000000 0x5ebfe13f8e000000

def z784 : W := mkw 0xa82f29291b54ca65 0x287c390dfe5cc33f

def z785 : W := mkw 0x909c16ece54b0b0a 0xeffc1efc71cf0f0f

def z786 : W := mkw 0x4001c91218a00480 0xf7c3d9327fac0ccf

def z787 : W := mkw 0x901c166ce54b0b0a 0xfffc3fffffff0fff

def z788 : W := mkw 0x00aaa27ffc000000 0x44bfc03ffe000000

def z789 : W := mkw 0x0c511fc4de0ff15d 0x20401fc07e0ff00f

def z790 : W := mkw 0x4804400003eec4c5 0x8140000001efcccf

def z791 : W := mkw 0x60777d8001fea4a0 0xbe7fffc001fff0f0

def z792 : W := mkw 0x04000244c601515c 0x590027cfce73f3fc

def z793 : W := mkw 0x00d55fc4fdfea000 0xa0401fc07ffff000

def z794 : W := mkw 0x4801c9121aa4c4c5 0x76c3d9327f8ccc0f

def z795 : W := mkw 0x4801c9121aa4c4c5 0x7783d9327f8c0ccf

def z796 : W := mkw 0x00aaa27ffc000000 0x7ebfe7fffe000000

def z797 : W := mkw 0x00bbbffffc010108 0x7fbffffffe00030c

def z798 : W := mkw 0x00733d80000ea000 0x247fdfc0000ff000

def z799 : W := mkw 0x00bbbffffc000000 0x5ebfe7ff8e000000

def z800 : W := mkw 0x00333d8018000000 0x3e3fffc07e000000

def z801 : W := mkw 0x0044400003fee044 0x8140000001fff0cc

def z802 : W := mkw 0xc00cc03a01e00e80 0xdfbfe03f81f00ff0

def z803 : W := mkw 0x00bbbffffc000000 0x7efffffffe0c000f

def z804 : W := mkw 0x00bbbffffc000000 0x7ebffffffe30f000

def z805 : W := mkw 0x4c88827ffe0155dd 0x4180003ffe000fff

def z806 : W := mkw 0x0076748001fa2000 0xbe7fe7c001f3f000

def z807 : W := mkw 0x04000244c601515c 0xffc027ffcff3fffc

def z808 : W := mkw 0x4026e01201f00480 0xdfbfe03f81f00ff0

def z809 : W := mkw 0x04266244c7f1515c 0xbe7fe7c04ff3f00c

def z810 : W := mkw 0xf804400003ffcfef 0x8140000001ffcfff

def z811 : W := mkw 0x1c111f44fe0fd15f 0x20401fc07e0ff00f

def z812 : W := mkw 0x0076748001fea000 0x9e7fe6c001fff000

def z813 : W := mkw 0x901c162c614b0b0a 0xc5fc183c71cf0f0f

def z814 : W := mkw 0xe0955fc4fdf00ea0 0xa1001fc07ff00ff0

def z815 : W := mkw 0x00141604414b0108 0xeffc1e3c71cf0f0f

def z816 : W := mkw 0x00bbbffffc000000 0xfffffffffe73f3f0

def z817 : W := mkw 0x4801c9121aa4c4c5 0xffc3f93fffaccccf

def z818 : W := mkw 0x901c1428214b0b0a 0xcffc183c31cf0f0f

def z819 : W := mkw 0x08bbbffffc048001 0x7ebffffffe0c0003

def z820 : W := mkw 0x00bbbffffc000000 0x7ebffffffe3000f0

def z821 : W := mkw 0x00733d80000ea000 0xbe7fffc0007ff000

def z822 : W := mkw 0x04777fc4c7fff15c 0x453fd80fcf8c03fc

def z823 : W := mkw 0x0033bfd6dc000000 0x7ebffffffe000000

def z824 : W := mkw 0x4c63e9d29eb4f4d5 0x1003e1c38e30f0f0

def z825 : W := mkw 0x0000000002004044 0xfb4027cfce73f3fc

def z826 : W := mkw 0xe02ee03b01f00ea0 0xdfffe03f81f3fff0

def z827 : W := mkw 0xe02ee03b01f00ea0 0x5fbfe03f81800ff0

def z828 : W := mkw 0x901c162c614b0b0a 0xfffc3e3ff1cf0f0f

def z829 : W := mkw 0x0018162c60010108 0xeffc1e3c71cf0f0f

def z830 : W := mkw 0x0444400003fef054 0x8040000001fff0f0

def z831 : W := mkw 0x4844400003fee4c5 0x8040000001fff0c0

def z832 : W := mkw 0xe87ffdbb19feaea1 0x04bfd830318c0c03

def z833 : W := mkw 0x00999f7ffc000000 0x7ebfdf3ffe000000

def z834 : W := mkw 0x0c911fc4fe05d15d 0x20401fc07e0ff00f

def z835 : W := mkw 0x4841c9921aa4e4c5 0xf7c3d9f27facfccf

def z836 : W := mkw 0x00777d8001fea000 0x9e3fe7c001f3f000

def z837 : W := mkw 0xdc04400003efdfdf 0x8140000001ffffff

def z838 : W := mkw 0x0022200000000000 0xdf3fe00f807003f0

def z839 : W := mkw 0x00ccc27ffdfea000 0xc0c0003ffffff000

def z840 : W := mkw 0x4801c9121aa4c4c5 0x5583d9327faccccf

def z841 : W := mkw 0x04bbbffffc011118 0xffbffffffe7333f0

def z842 : W := mkw 0x90bbbffffc010b0a 0xfffffffffe430f0f

def z843 : W := mkw 0x00bbbffffc010108 0xfffffffffe73f30c

def z844 : W := mkw 0xd804400003eecec7 0x8140000001accccf

def z845 : W := mkw 0x00bbbffffc000000 0x7fbffffffe000c0f

def z846 : W := mkw 0x00444244c5fea000 0xfa4027cfcffff000

def z847 : W := mkw 0x00bbbffffc000000 0x54bff9fffe000000

def z848 : W := mkw 0x00bbbdbb38000000 0x14bfd9323e000000

def z849 : W := mkw 0x00bbbffffc000000 0x3e3fffcf8e000000

def z850 : W := mkw 0x00777d8001fea000 0xae7fdfc001cff000

def z851 : W := mkw 0x00bbbffffc010108 0xfffffffffe7303fc

def z852 : W := mkw 0x04000244c601515c 0x384027cfce73f3fc

def z853 : W := mkw 0x4801c9121aa4c4c5 0x65c3d9327f8ccccf

def z854 : W := mkw 0x901c162c614b0b0a 0x04bc1830718c0c0f

def z855 : W := mkw 0x00773d80014ea000 0xbe7fffc001cff000

def z856 : W := mkw 0x20777d8101fea020 0xbe7fffc181fff030

def z857 : W := mkw 0x00bbbffffc000000 0xfefffffffe430000

def z858 : W := mkw 0x9444400003fffb5e 0x8140000001ffffff

def z859 : W := mkw 0xe02ee03b01f00ea0 0xdfffe03f81fc0fff

def z860 : W := mkw 0x00bbbdfbbc000000 0x76bff9f3fe000000

def z861 : W := mkw 0x901c162c614b0b0a 0xeffc1e3c71ffff0f

def z862 : W := mkw 0xe444400003fffffc 0x8140000001fffffc

def z863 : W := mkw 0xd844400003ffefcf 0x8140000001ffffcf

def z864 : W := mkw 0x10bbbffffc01010a 0x7ebffffffe00000f

def z865 : W := mkw 0x941c166ce54b1b1a 0xfffc3fffffdf3f3f

def z866 : W := mkw 0x00155d0001ee8000 0xbe7fffc001fff000

def z867 : W := mkw 0xe0aee03b39f00ea0 0xdfbfe03fb1f00ff0

def z868 : W := mkw 0xe02ee03b01f00ea0 0xd7bfc03f81a00ff0

def z869 : W := mkw 0x901c162c614b0b0a 0xfffc3e3c71ff0f0f

def z870 : W := mkw 0x4863e9921ab4e4c5 0x1003c1020e20c0c0

def z871 : W := mkw 0x4823e9131aa4c4c5 0x1003e1038e20c0c0

def z872 : W := mkw 0x4801c9121aa4c4c5 0xffc3fff27faccccf

def z873 : W := mkw 0x947e36ece55b3b1a 0x083c26cd80533330

def z874 : W := mkw 0xe02ee03b01f00ea0 0x5ebfe03f807003f0

def z875 : W := mkw 0x00777d8001fea000 0x1c3fffc001fff000

def z876 : W := mkw 0x00777d8001fea000 0xbe7fffc071fff00f

def z877 : W := mkw 0x00bbbdfbbc000000 0x04bfd9f03e000000

def z878 : W := mkw 0x00bbbdfbbc000000 0x04bfd833be000000

def z879 : W := mkw 0x00bbbffffc000000 0x1cbfffffbe000000

def z880 : W := mkw 0x00777d8001fea000 0xfffffff001fffc00

def z881 : W := mkw 0x90bbbffffc000a02 0x7ebffffffe000c03

def z882 : W := mkw 0xe0599dbb000eaea0 0x61c01fff800ffff0

def z883 : W := mkw 0x901c1428214b0b0a 0xaffc1e3031cf0f0f

def z884 : W := mkw 0x00b3bfd7dc000000 0x7e3fffcfce000000

def z885 : W := mkw 0x4801c9121aa4c4c5 0xf7c3f933ffbcccff

def z886 : W := mkw 0x04bbbffffc011118 0xfefffffffe73f330

def z887 : W := mkw 0x0066600001fea000 0xbe7fe7c001fff000

def z888 : W := mkw 0xe02ee03b01f00ea0 0x1cbfe03f81f00ff0

def z889 : W := mkw 0xe02ee03b01f00ea0 0x993fe00f81f00ff0

def z890 : W := mkw 0x00999ffefc000000 0x7ebfdffe7e000000

def z891 : W := mkw 0x00bb3fecfc000000 0x7ebffffc7e000000

def z892 : W := mkw 0x48bbbffffc000481 0x7ebffffffe000c03

def z893 : W := mkw 0x00bbbdfbbc000000 0x3ebffff3be000000

def z894 : W := mkw 0x080189121a04c045 0xf7c3d9327f8ccc0f

def z895 : W := mkw 0x00bbbffffc000000 0x7ebffffffe500330

def z896 : W := mkw 0x0023a91218000000 0x7ebff9327e000000

def z897 : W := mkw 0x901c1428214b0b0a 0x04fc1830318f0c0f

def z898 : W := mkw 0x00b3bfd6fc000000 0x7ebffff27e000000

def z899 : W := mkw 0x00bab6ffe4000000 0x7ebfe7ffce000000

def z900 : W := mkw 0x00b33dc09c000000 0x3e3fffc00e000000

def z901 : W := mkw 0x003ab67fe4000000 0x7ebffffffe000000

def z902 : W := mkw 0x90058912194b0b0a 0xf7c3d9327fcf0f0f

def z903 : W := mkw 0x901c162c614b0b0a 0xfffc3ffc71cf0f0f

def z904 : W := mkw 0x002aa03b18000000 0x5ebfe03ffe000000

def z905 : W := mkw 0x00119d1218000000 0x7ebfdf327e000000

def z906 : W := mkw 0xe02aa03b00000ea0 0x45bfc03f80000ff0

def z907 : W := mkw 0x00777d8001fea000 0x987fe7c001fff000

def z908 : W := mkw 0x001c162c614a0000 0xeffc1e3c71cf0c0f

def z909 : W := mkw 0x00bbbffffc000000 0x6ebfde3ffe000000

def z910 : W := mkw 0x00fbbffffc04a000 0x7ebffffffe00f000

def z911 : W := mkw 0x9488827ffe015b5e 0x4180003ffe000fff

def z912 : W := mkw 0x04000244c601515c 0xfb403fcffe7ff3ff

def z913 : W := mkw 0x002bab7fdc000000 0x7ebffffffe000000

def z914 : W := mkw 0x4800c0121aa044c5 0xf7c3d8327fac0ccf

def z915 : W := mkw 0x000189121a004044 0xf7c3d9327faccccf

def z916 : W := mkw 0x00bbbffffc000000 0x04bfd8307e000000

def z917 : W := mkw 0x10777d8021fea002 0xbe7fffc031fff003

def z918 : W := mkw 0x901c162c614b0b0a 0xeffc3e3df1df0f3f

def z919 : W := mkw 0xe488827ffe015ffc 0x4180003ffe000ffc

def z920 : W := mkw 0xe0777d8001feaea0 0xbe7fffc001fffc00

def z921 : W := mkw 0x0033bd9218000000 0x76bfd9327e000000

def z922 : W := mkw 0x00b3bdd39c000000 0x7ebffff3fe000000

def z923 : W := mkw 0xe00cc03b01e00ea0 0xdfbfc03f81e00ff0

def z924 : W := mkw 0x04266244c7f1515c 0xdf3fe00fcff003fc

def z925 : W := mkw 0x6026e01301f004a0 0xdf3fe00f81f003f0

def z926 : W := mkw 0x4801c9121aa4c4c5 0xb6c3d9307faccc0f

def z927 : W := mkw 0x00777d8001fea000 0xfe7fffc24ffff000

def z928 : W := mkw 0x00bbbffffc000000 0xfffffffffe00000c

def z929 : W := mkw 0x00bbbffffc000000 0x3ebffff07e000000

def z930 : W := mkw 0xe02ae03b00b00ea0 0x5fbfe03f80300ff0

def z931 : W := mkw 0x901c162c614b0b0a 0xeffc3efc71df3f0f

def z932 : W := mkw 0xe02ae03b00a00ea0 0xdfbfe03f81a00ff0

def z933 : W := mkw 0x90bbbffffc010b0a 0xffffffffff8c0f0f

def z934 : W := mkw 0x002aa27fc4000000 0x5ebfe03fce000000

def z935 : W := mkw 0x00abab7ffc000000 0x7ebff93ffe000000

def z936 : W := mkw 0x00bbbffffc000000 0x7ebfffffff8c0c03

def z937 : W := mkw 0x00ababffdc000000 0x7ebfe7ffce000000

def z938 : W := mkw 0x00777d8001fea000 0x387fffc0007ff000

def z939 : W := mkw 0x802e602801f00a00 0xdfbfe03f81f00ff0

def z940 : W := mkw 0x00aaa07b9c000000 0x5ebfe03f8e000000

def z941 : W := mkw 0x0010140000000000 0xeffc1e30718c0c0f

def z942 : W := mkw 0xe804400003f4cee5 0x8100000001f0cff0

def z943 : W := mkw 0xe02ee03b01f00ea0 0xffffe13f81f0cff0

def z944 : W := mkw 0x48777d8001fea481 0xbe7fffc001fffc03

def z945 : W := mkw 0xe02ee03b01fa0ea0 0xdfffe03f81ff0ff0

def z946 : W := mkw 0xe02ee03b01f00ea0 0xcfbfc03f81c00ff0

def z947 : W := mkw 0x802ea03b01400a00 0xdfbfe03f81f00ff0

def z948 : W := mkw 0xe06ee03b01fa2ea0 0xdfbfe03f81f33ff0

def z949 : W := mkw 0x00fbbffffc0ea000 0x7ebffffffe0c0000

def z950 : W := mkw 0xe404400003f15ffc 0x8100000001f00ffc

def z951 : W := mkw 0x901c162c614b0b0a 0x6efc1e3c718f0c0f

def z952 : W := mkw 0x40777d8001fea480 0xbf7fffc001fffcc0

def z953 : W := mkw 0xe02ee03b01f00ea0 0x4dbfe03f81d00ff0

def z954 : W := mkw 0xa02ea03b01500a20 0xdfbfe03f807003f0

def z955 : W := mkw 0xe008803b00000ea0 0xfbc027ff8073fff0

def z956 : W := mkw 0xb01c162d614b0b2a 0xeffc1e3df1cf0f3f

def z957 : W := mkw 0x800c022c41410b08 0xeffc1e3c71cf0f0f

def z958 : W := mkw 0xe02ee03b01f00ea0 0xdfbfe03ff1f00fff

def z959 : W := mkw 0x0004000001400000 0xeffc183071cc0c0f

def z960 : W := mkw 0x0844400003fee045 0x8040000001fff00f

def z961 : W := mkw 0x00bbbffffc010108 0xffffffffffcf0f0f

def z962 : W := mkw 0x00777d8001fea000 0xb67fdfc001aff000

def z963 : W := mkw 0x00bbbffffc000000 0x64bfdffffe000000

def z964 : W := mkw 0x00333d8000000000 0x3e7fffc00003f000

def z965 : W := mkw 0x00773d80015ea000 0x3e7fffc0005ff000

def z966 : W := mkw 0xe0bbbffffc000ea0 0xffbffffffe700ff0

def z967 : W := mkw 0x4801c9121aa4c4c5 0xf7c3dff27faffccf

def z968 : W := mkw 0x00bbbffffc048000 0x7efffffffe0cc000

def z969 : W := mkw 0x002ee03b01f00000 0xdfbfe03f81f003f0

def z970 : W := mkw 0x00bbbffffc000000 0x76bfd93ffe000000

def z971 : W := mkw 0x4801c9121aa4c4c5 0xa5c3d9307faccccf

def z972 : W := mkw 0x0408827fc601515c 0x4180003fce0003fc

def z973 : W := mkw 0xe02ee03b01f00ea0 0xffffe03fc1f00ffc

def z974 : W := mkw 0x901c162c614b0b0a 0x2cfc1e3c71cf0f0f

def z975 : W := mkw 0x00bbbdbb38000000 0x7ebff93ffe000000

def z976 : W := mkw 0x00b3bdd39c000000 0x143ff9c38e000000

def z977 : W := mkw 0xe844400003feeee5 0x8140000001ffffff

def z978 : W := mkw 0x4818562c62a4c4c5 0xeffc1e3c71accccf

def z979 : W := mkw 0xf408827fe6015ffe 0x4180003ffe000fff

def z980 : W := mkw 0x909c166de54b0b0a 0xeffc1e3df1cf0f0f

def z981 : W := mkw 0x003bbfffc4000000 0x7ebfffffce000000

def z982 : W := mkw 0xe026600001f00ea0 0xdf3fe00f81f00ff0

def z983 : W := mkw 0x00bbbffffc000000 0x34bffff3fe000000

def z984 : W := mkw 0x00fbbffffc0ea000 0xfefffffffe7ff000

def z985 : W := mkw 0xc804400003e4cec5 0x8140000001eccfcf

def z986 : W := mkw 0x4ca3e9d39ea4d4d5 0x1003e1c38e30f0f0

def z987 : W := mkw 0xe02ee03b01f00ea0 0xdfbff83fb1fc0ff3

def z988 : W := mkw 0xe02e602901f00ea0 0x9f3fe00d81f00ff0

def z989 : W := mkw 0xe82ee03b01f48ea1 0xdfbfe03f81fc0ff3

def z990 : W := mkw 0x00777d8001fea000 0xff7fffc201fff0c0

def z991 : W := mkw 0xe02ee03b01f00ea0 0xc5bfc03f81f00ff0

def z992 : W := mkw 0x901c166ce54b0b0a 0xeffc3efdf1cf0f0f

def z993 : W := mkw 0x00bbbffffc000000 0xffbffffffe2000c0

def z994 : W := mkw 0x002aa07b84000000 0x5ebfe1ff8e000000

def z995 : W := mkw 0x901c166ce54b0b0a 0xfffc3fffffffff0f

def z996 : W := mkw 0x901c166ce54b0b0a 0xeffc1e3fffcf0f0f

def z997 : W := mkw 0x901c162c614b0b0a 0x4dbc1e3c71cf0f0f

def z998 : W := mkw 0x6801c9131aa4c4e5 0xf7c3d933ffacccff

def z999 : W := mkw 0x04000244c601515c 0x994027cf8e73f3fc

def z1000 : W := mkw 0x002ba93b18000000 0x76bfd9327e000000

def z1001 : W := mkw 0x00777d8001fea000 0x3e3fffc00073f000

def z1002 : W := mkw 0x04bbbffffc011118 0x7ebffffffe033000

def z1003 : W := mkw 0x04111fc4c601515c 0x20401fc04e03f00c

def z1004 : W := mkw 0x901c162c614b0b0a 0xe7fc183c718c0f0f

def z1005 : W := mkw 0x00777d8019fea000 0xbe7fffc07ffff000

def z1006 : W := mkw 0x00aba9fb9c000000 0x7ebff9fffe000000

def z1007 : W := mkw 0x00bbbffffc000000 0xfeffffffff8c0000

def z1008 : W := mkw 0x4801c9121aa4c4c5 0xf7c3d9327ffccfff

def z1009 : W := mkw 0xe02ee03b01f00ea0 0x55bfe03f81b00ff0

def z1010 : W := mkw 0xe02ee03b01f00ea0 0xfffff83f81fc0ff0

def z1011 : W := mkw 0x80bbbffffc000a00 0x7fbffffffe000f00

def z1012 : W := mkw 0x901c1428214a0a02 0xeffc183c71cc0f0f

def z1013 : W := mkw 0xe0fffdbb39feaea0 0x04bfd830318c0c00

def z1014 : W := mkw 0x00bab67ffc000000 0x7ebffe3ffe000000

def z1015 : W := mkw 0x00bb3fede4000000 0x7e3fffcfce000000

def z1016 : W := mkw 0x00777d8001fea000 0x347fffc001bff000

def z1017 : W := mkw 0xe404400003f05ef4 0x8100000001f0fff0

def z1018 : W := mkw 0x00777d8001fea000 0xba7fe7c00073f000

def z1019 : W := mkw 0x941c166ce54b1b1a 0xfffc3efff1ff3fff

def z1020 : W := mkw 0xe02ee03b01f00ea0 0xffffe63f81f30ff0

def z1021 : W := mkw 0x4823e9121ab4c4c5 0x1003e1020e30c0c0

def z1022 : W := mkw 0x402ae03b00a00480 0xdfbfe03f81f00ff0

def z1023 : W := mkw 0x94be36ede54b1b1a 0x083c26cd80533330

def z1024 : W := mkw 0x00222244c4000000 0x7e3fe7cfce000000

def z1025 : W := mkw 0x901c162c614b0b0a 0xfffc1f3e7fcf0f0f

def z1026 : W := mkw 0x0022200000000000 0xbe7fe7c00073f000

def z1027 : W := mkw 0x00aba9fb9c000000 0x14bfe1f38e000000

def z1028 : W := mkw 0x4823e9921aa4c4c5 0x1003e1c20e20c0c0

def z1029 : W := mkw 0x14000244e601515e 0xfb4027cffe73f3ff

def z1030 : W := mkw 0x00737d8000aea000 0xbe7fffc001aff000

def z1031 : W := mkw 0x90141400014b0b0a 0xeffc1e3071cf0f0f

def z1032 : W := mkw 0xe804400003f4cee5 0x8140000001accccf

def z1033 : W := mkw 0x00fbbffffc0a2000 0x7ebffffffe033000

def z1034 : W := mkw 0x002aa03b00000000 0x7ebfe13fce000000

def z1035 : W := mkw 0x4801c9121aa4c4c5 0xffc3ffffffffffff

def z1036 : W := mkw 0x00777d8001fea000 0xbf7fffc001fffc0f

def z1037 : W := mkw 0x4801c9121aa4c4c5 0x34c3d9327faccccf

def z1038 : W := mkw 0x00bbbffffc000000 0xffbfffffff800c00

def z1039 : W := mkw 0x003bbfbe78000000 0x7ebffffe7e000000

def z1040 : W := mkw 0x4801c9121aa4c4c5 0xf7c3f9f27fbcfccf

def z1041 : W := mkw 0x0400004086005054 0xfb4027cf8e73f3f0

def z1042 : W := mkw 0x800c002801400a00 0xe7fc1830718c0c0f

def z1043 : W := mkw 0x4801c9121aa4c4c5 0xffc3df327fefcccf

def z1044 : W := mkw 0x00bbbffffc000000 0xffbffffffe400300

def z1045 : W := mkw 0x4804400003f4c4c5 0x8140000001fccccf

def z1046 : W := mkw 0x00777d8001fea000 0xa47fdfc001fff000

def z1047 : W := mkw 0x00199f7efc000000 0x7ebffffffe000000

def z1048 : W := mkw 0xf02ee03b21f00ea2 0xdfbfe03fb1f00ff3

def z1049 : W := mkw 0xa02e602901f00a20 0xdf3fe00f81f003f0

def z1050 : W := mkw 0xe0bbbffffc000ea0 0x7ebffffffe000c00

def z1051 : W := mkw 0x4801c9121aa4c4c5 0xf7c3d93fffaccfff

def z1052 : W := mkw 0x04000244c601515c 0x7a0027cfce73f3f0

def z1053 : W := mkw 0x80777d8001feaa00 0xbf7fffc001ffff00

def z1054 : W := mkw 0x901c166ce54b0b0a 0xeffc1ffc7fcf0f0f

def z1055 : W := mkw 0x901c162c614b0b0a 0xfffc1e3e71ef0fcf

def z1056 : W := mkw 0x00bbbffffc000000 0x7efffffffe03f000

def z1057 : W := mkw 0x10141604614b010a 0xeffc1e3071cf0c0f

def z1058 : W := mkw 0x00ababfffc000000 0x5ebfe1fffe000000

def z1059 : W := mkw 0x901c162c614b0b0a 0x8dfc1e3c31cf0f0f

def z1060 : W := mkw 0x00555d8001eea000 0xbe7fdfc001eff000

def z1061 : W := mkw 0x4801c9121aa4c4c5 0xd783d8327fac0ccf

def z1062 : W := mkw 0x4801c91218a48481 0xf7c3d9327f8c0c0f

def z1063 : W := mkw 0xe06ee0bb01f02ea0 0xdfbfe0ff81f03ff0

def z1064 : W := mkw 0x0404400003f1515c 0x8140000001f3f3fc

def z1065 : W := mkw 0xe02aa03b00000ea0 0xdfbfe03f80700ff0

def z1066 : W := mkw 0xb43e366de55b1b3a 0x083c26cd80533330

def z1067 : W := mkw 0x00777d8001fea000 0xfe7fffcf81fff000

def z1068 : W := mkw 0x04333d800201515c 0xbf7fffc00073f3fc

def z1069 : W := mkw 0x00511d80000ea000 0xfb403fcf807ff3f0

def z1070 : W := mkw 0x4801c9121aa4c4c5 0xffc3d93e7feccfcf

def z1071 : W := mkw 0x901c1428214a0a02 0x24fc1830718c0c0f

def z1072 : W := mkw 0x901c162c614b0b0a 0x65fc1e3c718f0f0f

def z1073 : W := mkw 0x04000244c601515c 0xfb4027cfcfffffff

def z1074 : W := mkw 0x10bbbffffc0b010a 0xfffffffffe4f030f

def z1075 : W := mkw 0x003bbdbb18000000 0x7ebffffffe000000

def z1076 : W := mkw 0xe02ee03b01f48ea0 0xdfffe03f81fccff0

def z1077 : W := mkw 0x4c44400003fff5dd 0x8140000001ffffff

def z1078 : W := mkw 0x00377d8001f00000 0xbe7fffc001f3f000

def z1079 : W := mkw 0x04bbbffffc011118 0xfffffffffe53333c

def z1080 : W := mkw 0x4841c9121ab4e4c5 0xf7c3d9327fbcfccf

def z1081 : W := mkw 0x1018162c600b010a 0xeffc1e3c718f0c0f

def z1082 : W := mkw 0x0444400003fff15c 0x8040000001fff00c

def z1083 : W := mkw 0x00bbbffffc000000 0xfefffffffe20c000

def z1084 : W := mkw 0x00bbbffffc000000 0xfebffffffe700000

def z1085 : W := mkw 0x901c1428214a0a02 0x45bc1830718c0c0f

def z1086 : W := mkw 0xe02ee03b01f00ea0 0x9e3fe00f81f003f0

def z1087 : W := mkw 0xe06ee03b01f4aea0 0xdfbfe03f81f0fff0

def z1088 : W := mkw 0x00777d8001fea000 0x8c7ffec001fff000

def z1089 : W := mkw 0x00bbbffffc010108 0x7efffffffe03000c

def z1090 : W := mkw 0xf0bbbffffc010faa 0x7fbffffffe000fff

def z1091 : W := mkw 0xe02ee03b19f00ea0 0xdfbfe03ffff00ff0

def z1092 : W := mkw 0xa0777d8001feaa20 0xbe7fffc001fff330

def z1093 : W := mkw 0x04bbbffffc011118 0x7ebffffffe000330

def z1094 : W := mkw 0x90777d8001feaa02 0xbe7fffc001fffc03

def z1095 : W := mkw 0x4c01c9121aa4d4d5 0xf7c3d9327fbcfcff

def z1096 : W := mkw 0x00bbbdbb38000000 0x24bfd9307e000000

def z1097 : W := mkw 0x00bbbdfb9c000000 0x7ebfffff8e000000

def z1098 : W := mkw 0x00777d8001fea000 0xff7fffcc01fff300

def z1099 : W := mkw 0xe02ea03b01500ea0 0x5fbfe03f80500ff0

def z1100 : W := mkw 0x9018162c60010b0a 0xeffc1e3c718c0f0f

def z1101 : W := mkw 0x04000244c601515c 0xff403fcfcffff3fc

def z1102 : W := mkw 0xe02ea03b01400ea0 0xdfbfe03f81c00ff0

def z1103 : W := mkw 0x04911fc4fe01515c 0x20001fc07e00000c

def z1104 : W := mkw 0xe02ee03b01f00ea0 0xffbff83ff1f00ff0

def z1105 : W := mkw 0x901c162c614b0b0a 0xaefc1e3071cf0c0f

def z1106 : W := mkw 0x901c162c614b0b0a 0xfffc3ffff1ffffff

def z1107 : W := mkw 0x901c162c614b0b0a 0xeffc1e3ff1cf0fff

def z1108 : W := mkw 0x6801c9121ab4c4e5 0xf7c3d9327fbcccff

def z1109 : W := mkw 0x00777d8001fea000 0xbefffff031fffc03

def z1110 : W := mkw 0x6863e9931ab4e4e5 0x1003e1c38e30f0f0

def z1111 : W := mkw 0x00bbbffffc0a0000 0x7efffffffe0f0000

def z1112 : W := mkw 0x042aa03b0201515c 0xdfffe03f8073f3fc

def z1113 : W := mkw 0x00bbbffffc000000 0x76bfdff27e000000

def z1114 : W := mkw 0x00b33fc4fc000000 0x7e3fffcffe000000

def z1115 : W := mkw 0x003b3fece4000000 0x7ebffffffe000000

def z1116 : W := mkw 0x00bbbdfbbc000000 0x103fe1c38e000000

def z1117 : W := mkw 0x901c1428214b0b0a 0xe7fc183071cf0f0f

def z1118 : W := mkw 0x04000244c601515c 0xffc03ffffe73f3fc

def z1119 : W := mkw 0x4000c01202a044c4 0xf7c3d9327faccccf

def z1120 : W := mkw 0xe02ee03b01f00ea0 0xffbfe13fcff00ff0

def z1121 : W := mkw 0x00777d8001fea000 0xff7fffc041fff00c

def z1122 : W := mkw 0x40bbbffffc000480 0x7fbffffffe000cc0

def z1123 : W := mkw 0x00bbbffffc000000 0x2cbffffdfe000000

def z1124 : W := mkw 0x04000244c601515c 0xba4027cf8e73f3f0

def z1125 : W := mkw 0xec04400003f5dffd 0x8140000001ffffff

def z1126 : W := mkw 0x00777d8001fea000 0xbe7fffc381fff0f0

def z1127 : W := mkw 0x4844400003fee4c5 0x8140000001accccf

def z1128 : W := mkw 0x04d11fc4fe0ff15c 0x20401fc07e0ff00c

def z1129 : W := mkw 0x00737d8000b4a000 0xbe7fffc00073f000

def z1130 : W := mkw 0x48e3e9d39eb4e4c5 0x1003e1c38e30f0c0

def z1131 : W := mkw 0x14511fc4e60ff15e 0x20401fc07e0ff00f

def z1132 : W := mkw 0x68a3e9d39eb4c4e5 0x1003e1c38e30c0f0

def z1133 : W := mkw 0x10bbbffffc0a0002 0x7ebffffffe0c0003

def z1134 : W := mkw 0x20bbbffffc100020 0x7ebffffffe100030

def z1135 : W := mkw 0x00773d80015a2000 0xbe7fffc00073f000

def z1136 : W := mkw 0x00737d8000bea000 0x3e7fffc0003ff000

def z1137 : W := mkw 0xe0044244c5f00ea0 0xfb0027cfcff00ff0

def z1138 : W := mkw 0x00bbbffffc000000 0x7a3fe7cfce000000

def z1139 : W := mkw 0x00bb3fedfc000000 0x3e3fffcdfe000000

def z1140 : W := mkw 0x901c162c614b0b0a 0xeffc1e3c71ff0fff

def z1141 : W := mkw 0x00199d3a38000000 0x76bfd9327e000000

def z1142 : W := mkw 0xe02ee03b01f00ea0 0x59bfe03f80700ff0

def z1143 : W := mkw 0x00bab6fffc000000 0x5ebfe6fffe000000

def z1144 : W := mkw 0x0001c91218a48000 0xf7c3d9327faccc0f

def z1145 : W := mkw 0x00b3bfd7fc000000 0x3e3fffc3fe000000

def z1146 : W := mkw 0x48a3e9931aa4c4c5 0x1003c1020e20c0c0

def z1147 : W := mkw 0x0027690001f48000 0xbe7fffc001fff000

def z1148 : W := mkw 0xe08cc27ffdf00ea0 0xc180003ffff00ff0

def z1149 : W := mkw 0x00000244c4000000 0xfb4027cfce73f3f0

def z1150 : W := mkw 0x941c166ce54b1b1a 0xfffc3ffdf1ffff3f

def z1151 : W := mkw 0x941c166ce54b1b1a 0xeffc1e3df1cf0f3f

def z1152 : W := mkw 0x6c23e9539eb4d4f5 0x1003e1c38e30f0f0

def z1153 : W := mkw 0xe06ee03b01feaea0 0xffffe7ff81fffff0

def z1154 : W := mkw 0x00777d8001fea000 0xbf7fffc001fff3f0

def z1155 : W := mkw 0x901c1428214a0a02 0x85fc1830318c0c0f

def z1156 : W := mkw 0x00bbbffffc000000 0x58bfe7fffe000000

def z1157 : W := mkw 0xe004400003f04ee4 0x8140000001f0cffc

def z1158 : W := mkw 0x941c166ce54b1b1a 0xeffc1efc71cf3f0f

def z1159 : W := mkw 0xe82ee03b19f00ea1 0xdfbfe03fb1f00ff3

def z1160 : W := mkw 0x00777d8001fea000 0x3e7fffc0018ff000

def z1161 : W := mkw 0x0488827ffe01515c 0x4080003ffe00000c

def z1162 : W := mkw 0x901c162c614b0b0a 0x6fbc1e3c718c0f0f

def z1163 : W := mkw 0x00141400014a0000 0xe7fc1830718c0c0f

def z1164 : W := mkw 0x00b3bdd39c000000 0x183fe7c38e000000

def z1165 : W := mkw 0x90fe36ede55b2b0a 0x083c26cd80533300

def z1166 : W := mkw 0xe02ee03b01f00ea0 0xdfbfe1ff81f0fff0

def z1167 : W := mkw 0xb0be36ede55b0b2a 0x083c26cd80530330

def z1168 : W := mkw 0x003bbf3f78000000 0x7ebfff3ffe000000

def z1169 : W := mkw 0x0018142820000000 0xe7fc1830718c0c0f

def z1170 : W := mkw 0x0001490002a4c044 0xf7c3d9327faccccf

def z1171 : W := mkw 0x0033bd9218000000 0x3e3fffc20e000000

def z1172 : W := mkw 0x10fbbffffc0fa10a 0x7efffffffe0ff00f

def z1173 : W := mkw 0x00bbbffffc000000 0x7ebffffffe533000

def z1174 : W := mkw 0x00777d8001fea000 0xfefffff071fff000

def z1175 : W := mkw 0x10bbbffffc0b010a 0x7ebffffffe030000

def z1176 : W := mkw 0x901c162c614b0b0a 0xfffc1f3c71efcf0f

def z1177 : W := mkw 0xe804400003f04ee5 0x8100000001f00fff

def z1178 : W := mkw 0x00333fc4c4000000 0x3e3fffc04e000000

def z1179 : W := mkw 0x90bbbffffc010b0a 0x7ebffffffe000300

def z1180 : W := mkw 0x6823e9131ab4c4e5 0x1003c1020e20c0c0

def z1181 : W := mkw 0x00a3a9d39c000000 0x1e3fe1c38e000000

def z1182 : W := mkw 0x0036740001fa0000 0xbe7fffc001fff000

def z1183 : W := mkw 0x0009893a18000000 0x7ebfd93e7e000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z7]),(0,[z1,z2,z3,z4,z8,z9,z6]),(0,[z1,z2,z3,z10,z4,z5,z6])],[(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z12,z1,z2,z3,z4,z5,z6]),(0,[z13,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z14,z4,z5,z6])],[(0,[z15,z1,z3,z4,z5,z16,z6]),(0,[z2,z17,z3,z4,z5,z18,z6]),(0,[z1,z19,z2,z3,z20,z5,z6]),(0,[z21,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z23,z4,z5,z6]),(0,[z24,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z25,z6,z26])],[(0,[z1,z2,z3,z4,z27,z5,z6]),(0,[z28,z1,z2,z3,z4,z29,z6]),(0,[z1,z30,z3,z4,z5,z31,z6]),(0,[z1,z2,z3,z4,z5,z26,z32]),(0,[z1,z2,z3,z4,z33,z5,z34])],[(0,[z1,z2,z3,z35,z4,z5,z6]),(0,[z1,z2,z36,z3,z4,z5,z6]),(0,[z1,z2,z37,z3,z4,z5,z6]),(0,[z1,z2,z3,z38,z4,z5,z6]),(0,[z2,z3,z39,z40,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z5,z6])],[(0,[z42,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z44]),(0,[z1,z2,z3,z4,z45,z5,z6]),(0,[z46,z1,z2,z3,z4,z5,z6]),(0,[z47,z48,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z49,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6])],[(0,[z15,z1,z51,z3,z4,z5,z6]),(0,[z52,z1,z2,z3,z4,z5,z6]),(0,[z1,z19,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z53,z5,z6])],[(0,[z54,z2,z17,z3,z4,z5,z6]),(0,[z55,z1,z56,z3,z4,z5,z6]),(0,[z57,z1,z58,z3,z4,z5,z6])]],
   [[(0,[z59,z1,z60,z3,z4,z5,z6]),(0,[z61,z1,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z63]),(0,[z1,z2,z3,z64,z4,z5,z6]),(0,[z1,z65,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z66,z6])],[(0,[z28,z1,z67,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z68,z6]),(0,[z1,z2,z3,z4,z5,z69,z6]),(0,[z1,z30,z2,z70,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z71,z6])],[(0,[z72,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z74,z4,z5,z6]),(0,[z1,z2,z3,z75,z4,z5,z6])],[(0,[z43,z2,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z77]),(0,[z1,z2,z23,z3,z78,z5,z6])],[(0,[z1,z2,z3,z4,z5,z79,z6]),(0,[z1,z2,z80,z3,z4,z5,z6]),(0,[z1,z2,z3,z40,z4,z5,z6]),(0,[z1,z2,z3,z4,z81,z5,z6]),(0,[z1,z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z3,z4,z83,z6])],[(0,[z84,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z62,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z85]),(0,[z1,z2,z3,z4,z86,z5,z6])],[(0,[z1,z2,z3,z4,z5,z87,z6]),(0,[z88,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z89,z3,z4,z5,z6]),(0,[z28,z1,z3,z40,z4,z5,z6]),(0,[z1,z67,z51,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z90,z6])]],
   [[(0,[z15,z1,z91,z3,z4,z5,z6]),(0,[z42,z1,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z5,z92,z6]),(0,[z93,z1,z2,z3,z94,z5,z6]),(0,[z1,z2,z3,z4,z5,z95,z6]),(0,[z96,z1,z2,z3,z4,z5,z6]),(0,[z97,z98,z2,z3,z4,z5,z6]),(0,[z1,z99,z3,z4,z5,z18,z6]),(0,[z100,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z6])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z91,z3,z4,z41,z5,z6]),(0,[z1,z2,z3,z4,z102,z5,z6]),(0,[z1,z2,z3,z4,z103,z5,z6]),(0,[z1,z2,z3,z104,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z105]),(0,[z1,z2,z3,z4,z66,z6,z26])],[(0,[z1,z2,z3,z106,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z1,z2,z3,z4,z5,z108,z6]),(0,[z1,z2,z3,z109,z4,z5,z6])],[(0,[z1,z2,z3,z110,z4,z5,z6]),(0,[z111,z1,z2,z3,z4,z5,z6]),(0,[z42,z1,z51,z3,z4,z5,z6]),(0,[z1,z2,z3,z112,z4,z5,z6]),(0,[z113,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z114,z6]),(0,[z1,z2,z115,z4,z78,z5,z6])],[(1,[z93,z2,z3,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z117]),(0,[z118,z1,z2,z4,z78,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z119])],[(0,[z1,z43,z67,z3,z4,z5,z6]),(0,[z48,z1,z2,z3,z4,z5,z6]),(0,[z120,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z121,z6]),(0,[z1,z3,z4,z5,z122,z123,z6]),(0,[z124,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z125,z6]),(1,[z2,z3,z4,z5,z6,z126]),(0,[z1,z2,z3,z4,z127,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z128]),(0,[z2,z3,z62,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z5,z129,z6]),(0,[z1,z2,z3,z4,z5,z6,z130]),(0,[z1,z3,z20,z4,z9,z5,z6]),(0,[z1,z2,z3,z4,z5,z131,z6]),(0,[z1,z2,z3,z4,z5,z83,z6]),(0,[z1,z132,z2,z3,z4,z5,z6])],[(0,[z15,z1,z3,z20,z4,z5,z6]),(1,[z59,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z133,z6]),(0,[z1,z2,z3,z94,z4,z5,z6]),(0,[z1,z91,z3,z4,z9,z5,z6]),(0,[z1,z2,z3,z4,z5,z134,z6])],[(1,[z1,z135,z3,z4,z5,z6]),(0,[z1,z91,z3,z40,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z136,z6]),(0,[z47,z1,z91,z2,z3,z4,z6]),(0,[z137,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z138,z5,z6]),(0,[z55,z1,z2,z22,z4,z5,z6]),(0,[z47,z1,z2,z74,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z139,z6]),(1,[z1,z2,z3,z4,z8,z6]),(1,[z140,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z141,z6]),(0,[z1,z2,z3,z4,z5,z6,z142])],[(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z143,z1,z2,z3,z4,z5,z6]),(0,[z93,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(0,[z145,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z146,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z83,z6])],[(0,[z147,z42,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z148,z4,z5,z6])],[(0,[z42,z1,z91,z3,z4,z5,z6]),(0,[z149,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z5,z6]),(0,[z1,z2,z3,z151,z4,z5,z6]),(0,[z47,z1,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z153,z6]),(0,[z1,z2,z3,z4,z5,z34,z32])],[(0,[z1,z2,z154,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z2,z22,z4,z78,z5,z6]),(0,[z156,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z157,z4,z5,z34]),(0,[z158,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z159,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z160]),(0,[z1,z2,z161,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z162,z6]),(0,[z1,z2,z3,z4,z5,z6,z163]),(0,[z1,z3,z4,z41,z5,z16,z6]),(0,[z1,z2,z3,z4,z164,z5,z6])],[(0,[z165,z1,z2,z3,z4,z5,z6]),(0,[z1,z67,z3,z20,z4,z5,z6]),(0,[z1,z2,z3,z4,z166,z5,z6])],[(0,[z1,z2,z3,z4,z167,z5,z6]),(0,[z72,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z168,z4,z5,z6]),(0,[z28,z1,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z70,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z128]),(0,[z98,z1,z2,z3,z4,z5,z6]),(0,[z1,z169,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z170,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z31,z6]),(0,[z1,z2,z3,z4,z5,z171,z6]),(0,[z1,z2,z3,z172,z4,z33,z6]),(0,[z1,z3,z173,z174,z4,z5,z6])],[(0,[z1,z2,z3,z4,z175,z5,z6]),(0,[z1,z2,z3,z4,z176,z5,z6]),(0,[z1,z2,z3,z4,z177,z5,z6]),(0,[z1,z2,z3,z4,z178,z5,z6]),(0,[z179,z1,z2,z3,z4,z5,z6])],[(0,[z42,z1,z3,z20,z4,z5,z6]),(0,[z28,z1,z3,z4,z5,z31,z6]),(0,[z1,z2,z3,z172,z4,z83,z6]),(0,[z1,z2,z3,z180,z4,z5,z6]),(0,[z181,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z15,z1,z3,z4,z5,z6,z182]),(1,[z1,z183,z3,z4,z5,z6])],[(0,[z1,z2,z184,z3,z4,z5,z6]),(1,[z2,z3,z4,z5,z6,z185]),(0,[z1,z2,z186,z3,z4,z5,z6])],[(0,[z1,z187,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z188,z4,z5,z6]),(0,[z1,z2,z3,z189,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z190,z6]),(0,[z1,z2,z3,z191,z4,z5,z6]),(0,[z1,z2,z192,z3,z4,z5,z6]),(0,[z193,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z194,z4,z5,z6])],[(0,[z1,z2,z3,z195,z4,z5,z6]),(0,[z196,z1,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z172,z5,z6])],[(0,[z1,z2,z3,z197,z4,z5,z6]),(0,[z198,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z199,z4,z5,z6]),(0,[z1,z2,z200,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z201])],[(0,[z202,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z203,z6]),(0,[z204,z1,z2,z3,z4,z5,z6])],[(0,[z1,z43,z2,z3,z4,z5,z6]),(0,[z205,z1,z2,z3,z4,z5,z6]),(0,[z206,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z207]),(0,[z1,z2,z3,z172,z4,z127,z6])]],
   [[(0,[z43,z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z5,z6,z208]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z211,z3,z4,z5,z6]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z213]),(0,[z1,z2,z3,z4,z5,z6,z214]),(0,[z215,z1,z2,z3,z4,z5,z6])],[(0,[z216,z1,z2,z3,z4,z5,z6]),(0,[z217,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z29,z6]),(0,[z218,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z219,z6]),(0,[z1,z2,z3,z4,z5,z6,z220]),(0,[z1,z2,z3,z4,z5,z6,z221])],[(0,[z1,z43,z3,z4,z5,z31,z6]),(0,[z222,z2,z3,z94,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z223]),(0,[z1,z2,z3,z4,z16,z83,z6]),(0,[z1,z2,z224,z3,z4,z5,z6]),(0,[z1,z2,z3,z225,z4,z5,z6])],[(0,[z226,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z60,z3,z4,z5,z6]),(0,[z1,z227,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z39,z4,z5,z6]),(0,[z1,z2,z3,z4,z228,z5,z6])],[(0,[z1,z2,z229,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z231,z2,z3,z4,z5,z6]),(0,[z47,z232,z2,z3,z4,z5,z6])],[(0,[z233,z1,z2,z3,z4,z5,z6]),(0,[z42,z1,z3,z4,z5,z6,z182]),(0,[z59,z54,z2,z3,z4,z5,z6]),(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z22,z4,z101,z5,z6]),(0,[z232,z1,z2,z3,z4,z5,z6])],[(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z236,z1,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z33,z6])]],
   [[(0,[z28,z42,z1,z3,z4,z5,z6]),(0,[z1,z2,z237,z3,z4,z5,z6]),(0,[z1,z3,z40,z4,z5,z16,z6]),(0,[z1,z2,z3,z238,z4,z5,z6]),(0,[z1,z2,z239,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z240]),(0,[z1,z3,z241,z62,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z5,z73]),(0,[z72,z2,z3,z4,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z6,z242]),(0,[z1,z2,z3,z4,z243,z5,z6]),(0,[z47,z1,z2,z3,z4,z83,z6]),(0,[z1,z2,z4,z5,z244,z6,z213]),(0,[z245,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z246]),(0,[z1,z2,z3,z4,z247,z5,z6]),(0,[z1,z248,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z249,z6])],[(1,[z1,z2,z3,z4,z5,z208]),(0,[z72,z1,z135,z3,z4,z5,z6])],[(1,[z98,z2,z3,z4,z250,z6]),(0,[z47,z1,z2,z3,z5,z123,z6])],[(0,[z42,z1,z2,z3,z4,z5,z251]),(0,[z1,z2,z3,z4,z252,z5,z6])],[(0,[z1,z2,z3,z4,z5,z253,z6]),(0,[z1,z2,z3,z94,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z254,z6])]],
   [[(0,[z1,z2,z3,z255,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z128]),(0,[z1,z2,z3,z174,z4,z5,z6])],[(0,[z256,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z257,z4,z5,z6]),(0,[z1,z2,z3,z4,z258,z5,z6]),(0,[z1,z23,z3,z146,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z127,z6]),(0,[z1,z2,z3,z173,z4,z5,z6])],[(0,[z1,z259,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z5,z6]),(0,[z1,z2,z3,z4,z5,z261,z6]),(1,[z1,z2,z3,z4,z138,z6])],[(0,[z1,z2,z3,z262,z4,z5,z6]),(1,[z1,z82,z3,z4,z5,z6]),(0,[z1,z2,z3,z263,z4,z5,z6])],[(0,[z1,z2,z3,z264,z4,z5,z6]),(0,[z1,z2,z3,z265,z4,z5,z6]),(0,[z118,z1,z2,z3,z78,z5,z6]),(0,[z1,z266,z2,z3,z4,z5,z6]),(1,[z1,z56,z3,z4,z5,z6]),(0,[z267,z1,z3,z4,z5,z123,z6])],[(0,[z59,z15,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z268,z5,z6]),(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z270,z6]),(0,[z1,z3,z4,z5,z18,z6,z223]),(0,[z1,z2,z3,z271,z4,z5,z6]),(0,[z1,z2,z3,z4,z272,z5,z6]),(0,[z1,z2,z3,z4,z273,z5,z6]),(1,[z57,z1,z2,z4,z5,z213])],[(0,[z1,z2,z3,z4,z5,z6,z6]),(1,[z47,z1,z2,z3,z123,z6])],[(0,[z274,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z275,z4,z5,z6]),(0,[z1,z2,z276,z3,z4,z5,z6]),(0,[z1,z2,z3,z277,z4,z5,z6])]],
   [[(1,[z1,z2,z3,z278,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z279]),(0,[z280,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z281,z6])],[(0,[z1,z2,z3,z4,z5,z282,z6]),(0,[z1,z2,z3,z4,z5,z18,z213]),(0,[z283,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z70,z3,z4,z5,z213])],[(0,[z15,z72,z2,z3,z4,z5,z6]),(0,[z284,z1,z2,z3,z4,z5,z6]),(0,[z285,z1,z2,z3,z4,z5,z6]),(0,[z286,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z287,z4,z5,z6])],[(0,[z288,z1,z2,z3,z4,z5,z6]),(1,[z1,z289,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z290,z5,z6]),(1,[z11,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z260,z116,z6]),(1,[z291,z2,z3,z4,z5,z6]),(1,[z292,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z26])],[(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z54,z2,z3,z4,z5,z6,z73]),(0,[z1,z2,z3,z4,z294,z5,z6]),(1,[z222,z2,z3,z94,z5,z6]),(0,[z1,z295,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z296,z4,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z127,z5,z32])],[(0,[z15,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z298,z4,z5,z6]),(0,[z1,z2,z299,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z300,z6]),(0,[z301,z2,z3,z4,z5,z31,z6]),(0,[z55,z1,z2,z4,z5,z83,z6]),(0,[z1,z2,z3,z302,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z171]),(0,[z1,z2,z3,z303,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z304,z6]),(0,[z1,z2,z3,z305,z4,z5,z6])],[(0,[z1,z2,z3,z241,z4,z5,z6]),(0,[z1,z2,z3,z4,z41,z83,z6]),(0,[z1,z2,z3,z4,z306,z5,z6])],[(0,[z1,z3,z40,z20,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z307,z6]),(0,[z1,z2,z3,z4,z9,z5,z6])]],
   [[(0,[z59,z1,z2,z17,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z213]),(0,[z28,z1,z2,z40,z4,z5,z6]),(0,[z1,z308,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z309,z6]),(0,[z1,z2,z3,z4,z310,z5,z6]),(0,[z1,z2,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z311,z6])],[(1,[z1,z2,z3,z4,z92,z6]),(0,[z312,z1,z3,z4,z5,z16,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z313,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z182])],[(0,[z1,z183,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z314,z5,z6]),(1,[z1,z315,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z29,z5,z6]),(0,[z1,z2,z3,z316,z4,z5,z6]),(1,[z1,z2,z3,z172,z306,z6]),(0,[z317,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z318,z6])],[(0,[z59,z1,z2,z3,z4,z5,z319]),(0,[z1,z2,z3,z4,z320,z5,z6]),(0,[z321,z1,z2,z3,z4,z5,z6]),(0,[z322,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z323,z3,z4,z5,z6])]],
   [[(0,[z324,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z325,z5,z6]),(0,[z326,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z327,z5,z6]),(0,[z1,z2,z3,z4,z5,z328,z6]),(0,[z1,z2,z3,z4,z329,z5,z6])],[(0,[z1,z2,z330,z3,z4,z5,z6]),(1,[z1,z2,z3,z331,z5,z6]),(0,[z1,z2,z3,z4,z5,z122,z6])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z286,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z332,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z333])],[(0,[z42,z1,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z115,z116,z5,z6]),(0,[z1,z2,z3,z5,z34,z6,z26])],[(0,[z1,z2,z3,z334,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z5,z6])],[(0,[z335,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z336,z5,z6]),(0,[z1,z337,z2,z3,z4,z5,z6]),(0,[z338,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z339,z6]),(0,[z1,z2,z3,z306,z5,z123,z6])],[(0,[z1,z43,z3,z40,z4,z5,z6]),(0,[z72,z1,z340,z3,z4,z5,z6]),(0,[z28,z1,z2,z51,z4,z5,z6]),(0,[z1,z3,z40,z4,z5,z6,z182]),(0,[z341,z1,z2,z3,z4,z5,z6])],[(0,[z147,z15,z1,z3,z4,z5,z6]),(0,[z312,z1,z91,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z182])]],
   [[(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z289,z2,z3,z4,z5,z6]),(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z222,z1,z2,z3,z116,z5,z6]),(0,[z1,z2,z3,z4,z343,z5,z6]),(0,[z147,z48,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z344,z5,z6]),(0,[z1,z2,z3,z345,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z346]),(0,[z1,z2,z347,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z348,z5,z6])],[(0,[z2,z3,z4,z250,z5,z349,z6]),(1,[z1,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z350,z5,z6]),(0,[z1,z2,z3,z4,z5,z351,z6]),(1,[z1,z2,z3,z303,z5,z34])],[(0,[z286,z1,z2,z3,z4,z5,z73]),(0,[z147,z1,z2,z3,z306,z5,z6])],[(0,[z15,z1,z43,z3,z4,z5,z6]),(1,[z42,z43,z3,z4,z5,z6]),(0,[z352,z1,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z221])],[(0,[z1,z2,z3,z4,z353,z5,z6]),(0,[z1,z2,z3,z4,z278,z5,z6]),(0,[z72,z1,z2,z3,z4,z5,z18]),(1,[z1,z3,z4,z5,z6,z223]),(0,[z1,z2,z3,z354,z4,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z31]),(0,[z1,z2,z3,z4,z5,z6,z355])],[(1,[z1,z60,z3,z4,z5,z6]),(0,[z93,z222,z2,z3,z4,z5,z6]),(0,[z98,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z356,z6]),(0,[z357,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z358,z4,z5,z6]),(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z1,z360,z2,z3,z4,z5,z6])],[(0,[z1,z3,z4,z343,z116,z5,z6]),(1,[z321,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z361])]],
   [[(0,[z28,z1,z2,z3,z4,z318,z6]),(0,[z312,z1,z3,z20,z4,z5,z6])],[(0,[z15,z1,z76,z3,z4,z5,z6]),(0,[z1,z67,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z362,z6]),(0,[z1,z2,z3,z4,z5,z363,z6])],[(0,[z1,z2,z3,z364,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z244]),(0,[z1,z51,z3,z40,z4,z5,z6]),(0,[z1,z2,z70,z3,z4,z5,z244]),(0,[z1,z2,z3,z4,z5,z365,z6])],[(0,[z1,z2,z3,z366,z4,z5,z6]),(0,[z1,z315,z2,z3,z4,z5,z6]),(0,[z1,z367,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z368,z5,z6]),(0,[z1,z369,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z370,z4,z5,z6]),(0,[z2,z3,z4,z5,z18,z6,z73]),(0,[z1,z2,z23,z3,z4,z371,z6])],[(0,[z98,z222,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z372,z5,z6]),(0,[z1,z2,z3,z4,z373,z5,z6]),(0,[z1,z374,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z375]),(1,[z267,z1,z3,z4,z5,z6])],[(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z376,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z377]),(0,[z378,z1,z2,z3,z4,z5,z6]),(0,[z379,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z380,z5,z6]),(0,[z1,z2,z3,z381,z4,z5,z6]),(0,[z1,z2,z3,z382,z4,z5,z6]),(0,[z1,z2,z3,z383,z4,z5,z6])]],
   [[(0,[z59,z1,z2,z3,z4,z336,z6]),(0,[z384,z1,z2,z3,z4,z5,z6]),(0,[z385,z1,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z386,z6])],[(0,[z42,z1,z43,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z31]),(1,[z1,z3,z174,z4,z5,z6])],[(0,[z1,z67,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z387,z6]),(0,[z1,z2,z3,z4,z5,z6,z388]),(0,[z1,z2,z389,z3,z4,z5,z6]),(0,[z1,z390,z2,z3,z4,z5,z6]),(0,[z1,z391,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z303,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z392]),(0,[z1,z183,z3,z173,z4,z5,z6])],[(0,[z97,z1,z2,z3,z172,z4,z6]),(0,[z72,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z23,z115,z5,z6])],[(0,[z393,z1,z2,z3,z4,z5,z6]),(0,[z385,z1,z2,z3,z4,z5,z6]),(0,[z48,z1,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z5,z6,z394]),(1,[z1,z2,z3,z395,z5,z6]),(1,[z1,z2,z3,z4,z396,z6]),(0,[z1,z2,z70,z4,z5,z244,z6]),(0,[z1,z2,z3,z4,z5,z397,z6])],[(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z399,z4,z5,z6])],[(0,[z42,z1,z76,z3,z4,z5,z6]),(0,[z54,z1,z2,z17,z4,z5,z6]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z9,z6]),(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z312,z1,z3,z4,z5,z6,z182]),(0,[z1,z2,z3,z173,z4,z101,z6]),(0,[z47,z1,z403,z3,z4,z5,z6]),(0,[z404,z1,z2,z3,z4,z5,z6]),(0,[z1,z405,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z406]),(0,[z1,z2,z3,z407,z4,z5,z6])],[(0,[z1,z408,z2,z3,z4,z5,z6]),(0,[z409,z1,z2,z3,z4,z5,z6]),(0,[z410,z1,z2,z3,z4,z5,z6]),(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z412,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z413,z6]),(0,[z1,z2,z3,z4,z5,z6,z414])],[(0,[z28,z15,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z73]),(0,[z1,z2,z3,z4,z101,z6,z32]),(0,[z1,z2,z3,z172,z306,z5,z6])],[(0,[z1,z415,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z16,z31,z6]),(0,[z416,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z32]),(0,[z1,z2,z3,z417,z4,z5,z6])],[(1,[z312,z1,z3,z4,z5,z182]),(0,[z1,z2,z3,z418,z4,z5,z6]),(1,[z419,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z420,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z421]),(1,[z1,z2,z74,z4,z5,z6])],[(0,[z422,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z423,z6])],[(1,[z1,z3,z241,z4,z5,z6]),(0,[z1,z2,z3,z424,z4,z5,z6]),(0,[z1,z2,z3,z425,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z16,z6]),(0,[z1,z2,z3,z4,z5,z426,z6])]],
   [[(1,[z401,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z1,z2,z3,z4,z5,z427,z6]),(0,[z1,z2,z3,z428,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z429,z6]),(0,[z430,z1,z2,z3,z4,z5,z6])],[(0,[z1,z91,z2,z3,z4,z41,z6]),(0,[z1,z2,z23,z3,z4,z5,z6]),(1,[z1,z152,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z127,z6,z32])],[(0,[z431,z1,z2,z3,z4,z5,z6]),(0,[z432,z1,z2,z3,z4,z5,z6]),(0,[z433,z1,z2,z3,z4,z5,z6]),(0,[z1,z51,z3,z4,z5,z31,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z434,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z436,z6]),(0,[z1,z2,z437,z3,z4,z5,z6])],[(0,[z54,z1,z2,z62,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z438]),(0,[z1,z2,z439,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z440,z5,z6]),(0,[z1,z2,z3,z441,z4,z5,z6])],[],[(0,[z1,z2,z442,z3,z4,z5,z6]),(0,[z1,z443,z2,z3,z4,z5,z6]),(0,[z147,z1,z19,z3,z4,z5,z6])],[(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z1,z403,z2,z3,z4,z5,z6]),(0,[z1,z445,z2,z3,z4,z5,z6])],[(0,[z286,z72,z2,z3,z4,z5,z6]),(0,[z446,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z447,z6]),(0,[z1,z2,z448,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z286,z2,z17,z3,z4,z5,z6]),(0,[z449,z1,z2,z3,z4,z5,z6]),(1,[z450,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z172,z4,z123,z6])],[(0,[z1,z2,z3,z4,z451,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z452]),(0,[z47,z1,z2,z453,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z454]),(0,[z1,z2,z3,z115,z5,z6,z26]),(1,[z1,z3,z4,z5,z122,z6])],[(0,[z1,z2,z3,z4,z250,z101,z6]),(1,[z286,z2,z3,z4,z5,z73]),(0,[z1,z2,z3,z4,z455,z5,z6]),(0,[z1,z2,z456,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z4,z83,z6]),(1,[z212,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z157,z5,z6,z26]),(0,[z1,z2,z3,z457,z4,z5,z6])],[(0,[z59,z43,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z458,z6]),(0,[z1,z2,z3,z459,z4,z5,z6])],[(0,[z59,z1,z2,z3,z334,z5,z6]),(0,[z1,z2,z3,z4,z460,z5,z6]),(0,[z1,z2,z3,z461,z4,z5,z6]),(0,[z1,z2,z3,z462,z4,z5,z6]),(0,[z463,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z22,z4,z101,z6])],[(0,[z15,z2,z17,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z464,z5,z6]),(0,[z1,z465,z2,z3,z4,z5,z6]),(0,[z147,z312,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z466])]],
   [[],[(1,[z1,z3,z4,z343,z5,z6]),(0,[z1,z99,z2,z3,z4,z5,z6]),(0,[z1,z467,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z6]),(0,[z1,z2,z23,z115,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z375,z213])],[(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z470,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z471,z6]),(0,[z1,z2,z472,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(1,[z1,z132,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z33,z5,z6])],[(0,[z1,z2,z474,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z475,z6])],[(0,[z47,z98,z1,z2,z3,z4,z6]),(0,[z140,z1,z2,z3,z5,z16,z6]),(0,[z57,z1,z2,z3,z4,z5,z244])],[(0,[z1,z2,z3,z303,z4,z5,z26]),(0,[z1,z2,z3,z4,z66,z5,z6])],[(0,[z476,z1,z2,z3,z4,z5,z6]),(1,[z385,z1,z3,z4,z5,z6]),(0,[z57,z286,z1,z2,z3,z4,z5]),(0,[z57,z1,z2,z4,z5,z6,z213]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z221,z26]),(0,[z1,z2,z3,z4,z5,z6,z478])],[(0,[z1,z2,z3,z4,z479,z5,z6]),(0,[z2,z3,z94,z4,z116,z5,z6]),(1,[z1,z2,z3,z4,z318,z6]),(0,[z1,z2,z3,z4,z480,z5,z6]),(0,[z1,z2,z3,z20,z4,z5,z6]),(0,[z1,z2,z3,z4,z33,z5,z26])]],
   [[(0,[z1,z2,z3,z4,z250,z5,z6]),(0,[z1,z2,z3,z481,z4,z5,z6]),(0,[z312,z1,z51,z3,z4,z5,z6]),(1,[z1,z91,z3,z4,z41,z6]),(0,[z1,z2,z3,z482,z4,z5,z6]),(0,[z483,z1,z2,z3,z4,z5,z6]),(1,[z232,z2,z3,z4,z5,z6]),(0,[z1,z2,z484,z3,z4,z5,z6])],[(0,[z1,z2,z3,z485,z4,z5,z6]),(0,[z1,z2,z3,z4,z486,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z487])],[(0,[z488,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z489,z5,z6]),(0,[z47,z1,z2,z3,z4,z123,z6])],[(0,[z490,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z349,z83,z6]),(0,[z312,z1,z30,z3,z4,z5,z6])],[(0,[z491,z1,z2,z3,z4,z5,z6]),(0,[z47,z1,z19,z2,z3,z5,z6]),(0,[z1,z91,z2,z3,z4,z16,z6])],[(0,[z1,z2,z3,z4,z492,z5,z6]),(0,[z1,z2,z3,z4,z493,z5,z6]),(1,[z1,z3,z4,z5,z6,z375]),(0,[z1,z2,z3,z494,z4,z5,z6])],[(0,[z1,z495,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z62,z4,z5,z6]),(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z496,z6]),(1,[z97,z2,z3,z4,z349,z6]),(0,[z312,z1,z2,z3,z4,z5,z18]),(0,[z1,z497,z2,z3,z4,z5,z6]),(1,[z48,z1,z3,z4,z16,z6]),(0,[z1,z56,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z498,z6])]],
   [[(1,[z61,z1,z3,z4,z5,z6]),(0,[z93,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z6]),(1,[z499,z2,z3,z4,z5,z6]),(0,[z47,z147,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z300,z16,z6]),(0,[z1,z2,z3,z4,z5,z6,z126]),(1,[z118,z1,z2,z78,z5,z6]),(0,[z1,z2,z70,z3,z4,z5,z6])],[(0,[z1,z500,z2,z3,z4,z5,z6]),(0,[z1,z2,z501,z3,z4,z5,z6]),(0,[z1,z2,z58,z3,z4,z5,z6]),(0,[z1,z502,z2,z3,z4,z5,z6])],[(0,[z503,z1,z2,z3,z4,z5,z6]),(0,[z504,z1,z2,z3,z4,z5,z6]),(0,[z57,z312,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z173,z4,z33,z5])],[(0,[z505,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z506,z4,z5,z6]),(0,[z1,z2,z3,z172,z4,z306,z6]),(1,[z1,z2,z3,z157,z5,z26]),(0,[z1,z2,z3,z4,z507,z5,z6])],[(0,[z59,z2,z3,z62,z4,z5,z6]),(1,[z1,z2,z3,z4,z260,z6]),(0,[z1,z2,z3,z94,z78,z5,z6]),(0,[z1,z3,z4,z9,z5,z16,z6]),(0,[z1,z2,z3,z4,z508,z5,z6])],[],[(0,[z222,z1,z2,z3,z94,z5,z6]),(0,[z147,z1,z2,z3,z9,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z182]),(0,[z1,z2,z3,z509,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z510]),(0,[z1,z2,z3,z4,z5,z511,z6]),(0,[z1,z2,z3,z4,z5,z512,z6]),(0,[z1,z2,z23,z3,z115,z5,z6]),(0,[z1,z2,z3,z4,z5,z513,z6])]],
   [[(0,[z286,z1,z2,z70,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z514,z6]),(0,[z147,z1,z3,z4,z41,z5,z6]),(0,[z1,z19,z3,z4,z5,z16,z6]),(0,[z1,z2,z515,z3,z4,z5,z6])],[(0,[z2,z17,z3,z62,z4,z5,z6]),(0,[z1,z2,z3,z516,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z517,z5,z6]),(0,[z1,z2,z3,z4,z518,z5,z6]),(0,[z1,z2,z3,z4,z519,z5,z6]),(0,[z57,z1,z2,z3,z4,z396,z6]),(0,[z1,z2,z3,z4,z520,z5,z6])],[(1,[z15,z76,z3,z4,z5,z6]),(1,[z2,z3,z39,z4,z5,z6]),(0,[z1,z91,z19,z3,z4,z5,z6])],[(0,[z59,z286,z2,z3,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z18]),(0,[z147,z1,z67,z3,z4,z5,z6]),(0,[z48,z1,z2,z3,z4,z41,z6]),(0,[z1,z2,z3,z4,z521,z5,z6])],[(1,[z1,z2,z3,z522,z4,z5]),(0,[z1,z2,z3,z115,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z523]),(0,[z1,z2,z3,z4,z524,z5,z6])],[(0,[z1,z525,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z526,z4,z5,z6]),(0,[z1,z2,z3,z157,z4,z5,z6])],[(0,[z15,z2,z76,z3,z4,z5,z6]),(0,[z527,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z528,z5,z6])]],
   [[(0,[z1,z2,z3,z116,z78,z5,z6]),(0,[z1,z82,z23,z3,z4,z5,z6]),(1,[z55,z1,z2,z4,z83,z6]),(0,[z450,z1,z2,z3,z4,z5,z6])],[(0,[z15,z42,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z529,z5,z6]),(0,[z147,z1,z3,z40,z4,z5,z6]),(1,[z1,z30,z3,z4,z5,z31]),(0,[z1,z2,z3,z4,z5,z6,z333])],[(0,[z1,z2,z3,z4,z5,z530,z6]),(0,[z312,z1,z43,z3,z4,z5,z6]),(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z185]),(0,[z1,z2,z3,z4,z531,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z532]),(0,[z1,z2,z3,z4,z5,z533,z6]),(1,[z147,z1,z3,z9,z5,z6]),(0,[z1,z2,z3,z157,z4,z5,z26])],[(0,[z1,z2,z534,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z319]),(0,[z1,z2,z3,z535,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z31,z6,z182]),(0,[z1,z2,z23,z3,z4,z138,z6]),(0,[z1,z2,z3,z4,z5,z536,z6])],[(0,[z72,z54,z2,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z250,z6]),(0,[z1,z91,z2,z3,z172,z4,z6]),(0,[z1,z2,z3,z4,z5,z244,z6]),(0,[z47,z1,z2,z3,z4,z306,z6])],[(0,[z1,z2,z3,z4,z5,z319,z6]),(0,[z1,z2,z22,z3,z4,z101,z6])],[(0,[z1,z2,z3,z4,z537,z5,z6]),(0,[z1,z2,z3,z4,z538,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z73]),(1,[z1,z67,z51,z4,z5,z6]),(0,[z1,z2,z3,z4,z539,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z540,z6]),(0,[z312,z1,z76,z3,z4,z5,z6]),(0,[z541,z1,z2,z3,z4,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z543,z4,z5,z6]),(0,[z1,z2,z544,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z545]),(1,[z1,z2,z70,z4,z5,z244])],[(0,[z546,z1,z2,z3,z4,z5,z6]),(0,[z118,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z371,z6]),(0,[z1,z547,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z4,z5,z32])],[(0,[z59,z2,z3,z4,z5,z18,z6]),(0,[z1,z2,z3,z548,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z549]),(0,[z550,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z31,z6,z126]),(0,[z1,z2,z3,z4,z33,z127,z5]),(0,[z1,z2,z3,z4,z5,z6,z551])],[(0,[z1,z2,z3,z4,z5,z552,z6]),(0,[z1,z2,z3,z553,z4,z5,z6]),(0,[z1,z2,z554,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z555,z5,z6]),(0,[z1,z2,z556,z3,z4,z5,z6])],[(0,[z97,z1,z2,z3,z4,z349,z6]),(0,[z1,z30,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z123,z6])],[(0,[z1,z76,z3,z40,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z333]),(0,[z419,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z25,z6])],[(0,[z1,z2,z3,z4,z5,z557,z6]),(0,[z1,z2,z558,z3,z4,z5,z6]),(1,[z376,z2,z3,z4,z5,z6]),(0,[z559,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z303,z4,z5,z34])],[(0,[z1,z2,z3,z560,z4,z5,z6]),(0,[z1,z2,z3,z4,z561,z5,z6]),(0,[z1,z19,z3,z20,z4,z5,z6]),(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z563,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z564,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z565]),(0,[z301,z1,z2,z3,z4,z5,z6]),(0,[z57,z212,z2,z3,z4,z5,z6])],[(0,[z1,z340,z2,z3,z4,z5,z6]),(0,[z147,z1,z2,z3,z20,z5,z6]),(0,[z450,z1,z3,z4,z5,z6,z213]),(0,[z1,z2,z3,z566,z4,z5,z6]),(0,[z1,z567,z2,z3,z4,z5,z6])],[(0,[z72,z1,z2,z70,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z568,z6]),(0,[z1,z2,z22,z3,z4,z5,z6]),(0,[z57,z291,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z436,z6])],[(0,[z1,z2,z569,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z570,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z73]),(0,[z1,z2,z3,z4,z5,z6,z571]),(0,[z1,z2,z3,z4,z572,z5,z6])],[(0,[z147,z1,z2,z3,z4,z5,z6]),(0,[z57,z1,z30,z2,z3,z4,z5]),(0,[z55,z1,z2,z3,z4,z101,z6]),(0,[z376,z2,z3,z4,z5,z6,z213])],[(0,[z1,z2,z3,z573,z4,z5,z6]),(0,[z1,z2,z17,z3,z4,z5,z6]),(0,[z48,z1,z91,z3,z4,z5,z6])],[(0,[z574,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z116,z6]),(0,[z1,z2,z51,z3,z4,z5,z6]),(0,[z57,z1,z132,z3,z4,z5,z6]),(0,[z575,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z576,z5,z6]),(0,[z1,z2,z577,z3,z4,z5,z6]),(0,[z1,z67,z3,z4,z5,z16,z6]),(0,[z48,z1,z2,z3,z4,z16,z6]),(0,[z1,z2,z3,z4,z5,z578,z6]),(0,[z1,z2,z3,z4,z25,z5,z6]),(0,[z1,z2,z3,z303,z5,z34,z6]),(1,[z1,z2,z3,z173,z4,z33])],[(0,[z57,z72,z1,z2,z3,z4,z5]),(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z147,z1,z3,z4,z5,z31,z6]),(0,[z1,z2,z4,z101,z5,z83,z6]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z580,z1,z2,z3,z4,z5,z6])],[(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z582]),(0,[z93,z1,z2,z3,z116,z5,z6])],[(0,[z1,z2,z583,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z584,z6]),(1,[z1,z19,z3,z20,z5,z6])],[(0,[z585,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z586,z4,z5,z6]),(0,[z1,z2,z3,z271,z40,z4,z5]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z588,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z589,z6]),(0,[z1,z2,z3,z173,z4,z33,z6])],[(0,[z1,z2,z590,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z336,z6]),(0,[z286,z2,z3,z4,z5,z6,z73]),(0,[z1,z3,z20,z4,z41,z5,z6]),(0,[z1,z2,z3,z4,z591,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z592])],[(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z3,z594,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z595,z6]),(1,[z301,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z596,z4,z5,z6]),(0,[z48,z1,z3,z20,z4,z5,z6]),(0,[z1,z2,z3,z597,z4,z5,z6]),(0,[z1,z2,z3,z598,z4,z5,z6])]],
   [[(0,[z599,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z600,z5,z6]),(0,[z1,z2,z3,z172,z4,z101,z6])],[(0,[z1,z2,z3,z4,z5,z6,z601]),(0,[z1,z2,z602,z3,z4,z5,z6]),(0,[z1,z2,z603,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z604]),(0,[z57,z1,z2,z3,z331,z5,z6])],[(0,[z1,z91,z67,z3,z4,z5,z6]),(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z2,z3,z606,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z5,z6]),(1,[z1,z58,z3,z4,z5,z6]),(0,[z607,z1,z2,z3,z4,z5,z6])],[(0,[z15,z2,z3,z4,z5,z6,z73]),(0,[z608,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z609,z6]),(0,[z401,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z610,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z611,z6]),(0,[z1,z291,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z395,z5,z6]),(0,[z1,z292,z2,z3,z4,z5,z6])],[(0,[z1,z76,z3,z4,z5,z31,z6]),(0,[z1,z2,z612,z3,z4,z5,z6]),(0,[z1,z2,z3,z613,z4,z5,z6]),(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z615,z1,z2,z3,z4,z5,z6]),(0,[z616,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z617,z6]),(0,[z1,z2,z618,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z619,z5,z6]),(0,[z1,z2,z3,z173,z4,z127,z6])],[]],
   [[(0,[z620,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z621,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z622,z6]),(1,[z1,z3,z4,z5,z511,z6]),(0,[z1,z2,z3,z4,z5,z6,z623]),(0,[z1,z2,z3,z303,z78,z5,z6])],[(0,[z1,z2,z624,z3,z4,z5,z6]),(0,[z1,z2,z3,z625,z4,z5,z6]),(0,[z626,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z250,z5,z511,z6]),(0,[z1,z67,z2,z40,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z627,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z127,z32])],[(0,[z1,z2,z3,z629,z4,z5,z6]),(0,[z630,z1,z2,z3,z4,z5,z6]),(1,[z1,z403,z3,z4,z5,z6]),(0,[z1,z2,z631,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z633,z3,z4,z5,z6])],[(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z303,z157,z5,z6]),(0,[z1,z2,z3,z4,z5,z635,z6])],[(0,[z1,z2,z3,z78,z5,z6,z26]),(0,[z1,z2,z3,z172,z4,z5,z6])],[(0,[z321,z1,z2,z3,z40,z4,z5]),(0,[z636,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z637,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z251]),(0,[z59,z1,z2,z3,z4,z5,z208]),(0,[z1,z2,z3,z4,z5,z6,z638]),(0,[z1,z2,z3,z4,z101,z349,z6]),(1,[z28,z1,z40,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z639,z6]),(0,[z118,z1,z2,z3,z115,z5,z6]),(0,[z1,z2,z3,z4,z83,z6,z32]),(0,[z1,z2,z3,z4,z640,z5,z6]),(0,[z1,z2,z3,z641,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z349,z6]),(0,[z48,z1,z2,z3,z172,z4,z6]),(0,[z1,z2,z3,z4,z642,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z643]),(0,[z644,z1,z2,z3,z4,z5,z6])],[(0,[z645,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z646,z6]),(0,[z1,z2,z3,z4,z5,z647,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z98,z2,z3,z4,z250,z5,z6]),(0,[z1,z2,z4,z78,z5,z83,z6]),(0,[z55,z1,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6])],[(0,[z650,z1,z2,z3,z4,z5,z6]),(0,[z1,z315,z3,z4,z250,z5,z6]),(0,[z1,z2,z3,z4,z250,z83,z6]),(0,[z1,z2,z3,z4,z5,z6,z651]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z653,z6]),(0,[z47,z1,z2,z3,z4,z101,z6])],[(0,[z654,z1,z2,z3,z4,z5,z6]),(1,[z1,z99,z3,z4,z5,z6])],[(0,[z655,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z656,z3,z4,z5,z6]),(0,[z657,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z658,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z185,z213])],[(0,[z659,z1,z2,z3,z4,z5,z6]),(0,[z499,z2,z3,z40,z4,z5,z6]),(0,[z1,z30,z67,z3,z4,z5,z6]),(0,[z1,z19,z2,z3,z306,z5,z6])],[(0,[z1,z2,z76,z3,z4,z5,z6]),(0,[z1,z67,z2,z51,z4,z5,z6]),(0,[z1,z19,z2,z3,z9,z5,z6]),(0,[z419,z1,z3,z4,z5,z6,z26])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z660]),(0,[z1,z2,z3,z4,z661,z5,z6]),(0,[z1,z2,z3,z4,z662,z5,z6]),(0,[z47,z292,z2,z3,z4,z5,z6]),(0,[z1,z2,z663,z3,z4,z5,z6])],[(0,[z1,z2,z3,z522,z4,z5,z6]),(0,[z1,z2,z3,z4,z664,z5,z6]),(0,[z1,z2,z135,z3,z4,z5,z6]),(1,[z72,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z34,z6])],[(1,[z1,z2,z3,z334,z5,z6]),(0,[z667,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z668]),(0,[z47,z1,z2,z3,z4,z5,z171]),(0,[z1,z2,z3,z669,z4,z5,z6]),(0,[z1,z2,z3,z670,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z251,z6]),(0,[z43,z2,z17,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z278,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z671]),(0,[z1,z30,z3,z40,z4,z5,z6]),(0,[z1,z91,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z146,z4,z5,z6]),(0,[z1,z672,z2,z3,z4,z5,z6])],[(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z674,z6]),(0,[z98,z1,z2,z3,z4,z250,z6]),(0,[z1,z2,z3,z4,z675,z5,z6]),(1,[z1,z2,z453,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z676,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z28,z312,z1,z3,z4,z5,z6]),(0,[z1,z677,z2,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z395,z5,z6])],[(0,[z59,z1,z289,z3,z4,z5,z6]),(1,[z54,z2,z17,z4,z5,z6]),(0,[z98,z1,z2,z3,z172,z4,z6]),(0,[z1,z2,z3,z4,z5,z678,z6]),(0,[z1,z67,z3,z4,z5,z6,z182]),(0,[z1,z3,z20,z4,z5,z31,z6]),(1,[z1,z2,z3,z5,z300,z6]),(0,[z1,z679,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z680,z4,z5,z6]),(0,[z2,z3,z4,z116,z5,z349,z6]),(0,[z47,z97,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z681,z4,z5,z6]),(0,[z1,z91,z3,z4,z5,z31,z6]),(0,[z1,z2,z3,z4,z5,z682,z6]),(0,[z1,z2,z3,z4,z5,z6,z213]),(0,[z47,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z683,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z684,z4,z5,z6]),(0,[z685,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z686,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z687,z5,z6]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z97,z2,z3,z4,z5,z349,z6]),(0,[z312,z1,z2,z3,z4,z5,z6])],[(0,[z689,z1,z2,z3,z4,z5,z6]),(0,[z1,z690,z2,z3,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z349,z6]),(0,[z147,z1,z3,z4,z9,z5,z6]),(0,[z1,z2,z3,z4,z5,z691,z6]),(0,[z1,z2,z3,z4,z692,z5,z6])],[(0,[z59,z1,z2,z3,z4,z92,z6]),(0,[z1,z2,z3,z4,z693,z5,z6]),(0,[z694,z1,z2,z3,z4,z5,z6]),(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z696])],[(0,[z697,z1,z2,z3,z4,z5,z6]),(0,[z59,z1,z2,z3,z4,z5,z6]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z699,z1,z2,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z522,z62,z4,z5]),(0,[z1,z2,z3,z4,z41,z101,z6]),(0,[z1,z2,z3,z4,z700,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z701,z6]),(0,[z1,z702,z2,z3,z4,z5,z6]),(0,[z118,z1,z2,z23,z4,z5,z6]),(0,[z1,z2,z703,z3,z4,z5,z6]),(0,[z57,z1,z2,z3,z4,z436,z6])],[(1,[z1,z340,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z78,z5,z6])],[(0,[z222,z2,z3,z4,z5,z349,z6]),(0,[z704,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z371,z6])],[],[(0,[z1,z2,z23,z4,z5,z83,z6]),(0,[z1,z2,z3,z4,z33,z6,z32])],[(0,[z312,z1,z2,z70,z3,z4,z5])],[(0,[z1,z2,z705,z3,z4,z5,z6])],[(1,[z1,z2,z3,z271,z4,z5]),(0,[z1,z2,z3,z4,z396,z5,z6]),(0,[z1,z2,z3,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z58,z3,z331,z5,z6]),(0,[z1,z2,z707,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z708]),(0,[z1,z3,z241,z522,z4,z5]),(0,[z326,z1,z3,z4,z16,z6]),(0,[z2,z3,z4,z5,z6,z709]),(0,[z1,z403,z3,z4,z5,z6]),(0,[z1,z2,z3,z383,z4,z33])],[(0,[z1,z2,z3,z710,z5,z6]),(0,[z1,z2,z3,z711,z5,z6]),(0,[z1,z2,z3,z4,z712,z5])],[(0,[z147,z499,z3,z4,z5,z6]),(0,[z1,z2,z453,z4,z138,z6])],[(0,[z226,z1,z40,z4,z5,z6]),(0,[z1,z2,z3,z713,z5,z6]),(0,[z1,z2,z3,z4,z714,z6]),(0,[z1,z2,z4,z5,z244,z715]),(1,[z47,z267,z1,z3,z6])],[(0,[z1,z2,z3,z716,z5,z6]),(0,[z1,z2,z3,z4,z717,z6]),(0,[z1,z2,z3,z4,z718,z5]),(0,[z2,z3,z4,z5,z719,z6]),(1,[z1,z2,z4,z720,z6])],[(0,[z721,z1,z2,z3,z4,z5]),(0,[z722,z1,z3,z4,z5,z6]),(0,[z1,z3,z723,z4,z5,z6])],[(0,[z1,z2,z3,z4,z724,z6]),(0,[z1,z725,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z128]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z2,z3,z727,z4,z5,z6]),(0,[z1,z183,z3,z173,z4,z33])],[(0,[z1,z2,z3,z4,z5,z728]),(0,[z1,z2,z3,z4,z729,z6])],[(0,[z1,z99,z3,z4,z5,z6]),(0,[z1,z289,z3,z334,z5,z6]),(0,[z1,z3,z4,z343,z260,z6]),(0,[z1,z23,z146,z115,z5,z6]),(0,[z1,z2,z3,z730,z5,z6])],[(0,[z1,z67,z731,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z732])],[(0,[z11,z385,z1,z3,z4,z6]),(0,[z1,z2,z3,z4,z733,z6]),(0,[z292,z2,z453,z4,z5,z6])],[(0,[z59,z2,z110,z4,z5,z6]),(0,[z1,z2,z734,z4,z5,z6]),(0,[z48,z1,z3,z4,z68,z6]),(0,[z1,z2,z3,z395,z436,z6])],[(0,[z28,z39,z40,z4,z5,z6]),(0,[z1,z3,z4,z41,z568,z6]),(0,[z419,z1,z3,z4,z25,z6]),(0,[z1,z3,z4,z66,z6,z221])],[(0,[z1,z51,z106,z4,z5,z6]),(0,[z385,z1,z3,z4,z260,z6]),(0,[z1,z735,z3,z4,z5,z6]),(0,[z1,z3,z4,z736,z5,z6]),(0,[z1,z737,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z738]),(0,[z1,z2,z74,z4,z5,z333])]],
   [[(0,[z1,z2,z3,z4,z739,z6]),(0,[z72,z2,z3,z4,z5,z18]),(0,[z1,z30,z3,z4,z5,z223]),(0,[z28,z499,z40,z4,z5,z6]),(0,[z1,z456,z40,z4,z5,z6]),(0,[z2,z740,z3,z4,z5,z6])],[(0,[z1,z2,z3,z741,z5,z6]),(0,[z1,z742,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z743,z6]),(0,[z744,z1,z2,z3,z4,z6]),(0,[z1,z82,z3,z4,z371,z6])],[(0,[z1,z745,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z746,z6]),(0,[z1,z2,z3,z747,z5,z6]),(0,[z1,z2,z3,z4,z748,z6]),(0,[z1,z749,z3,z4,z5,z6]),(0,[z1,z152,z3,z4,z5,z333])],[(0,[z1,z2,z3,z750,z123,z6])],[(0,[z15,z1,z3,z4,z318,z6]),(0,[z1,z2,z3,z4,z751,z6]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z2,z3,z5,z300,z6]),(0,[z140,z48,z1,z3,z16,z6]),(0,[z57,z2,z4,z5,z185,z213])],[(0,[z15,z443,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z754,z6]),(0,[z42,z1,z3,z4,z318,z6]),(0,[z1,z755,z3,z4,z5,z6]),(0,[z699,z2,z3,z116,z5,z6]),(0,[z2,z3,z94,z756,z5,z6]),(0,[z1,z2,z3,z4,z757,z6])],[(0,[z1,z2,z3,z758,z5,z6]),(0,[z42,z43,z3,z4,z5,z251])]],
   [[(0,[z759,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z33,z643])],[(0,[z1,z2,z3,z4,z5,z760]),(0,[z42,z43,z3,z4,z5,z128]),(0,[z99,z3,z4,z5,z6,z73]),(0,[z48,z1,z3,z4,z761,z6]),(0,[z1,z91,z3,z4,z178,z6]),(0,[z1,z2,z3,z4,z25,z32])],[(0,[z1,z762,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z2,z453,z4,z83,z6])],[(0,[z1,z2,z3,z4,z764,z6]),(0,[z291,z2,z3,z4,z5,z213]),(0,[z47,z1,z2,z3,z365,z6]),(0,[z267,z1,z3,z172,z4,z6])],[(0,[z140,z42,z1,z3,z5,z6]),(0,[z1,z2,z3,z765,z5,z6]),(0,[z2,z3,z756,z116,z5,z6]),(0,[z766,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z303,z5,z121]),(0,[z767,z2,z3,z4,z5,z6]),(0,[z1,z58,z3,z395,z5,z6])],[],[(0,[z1,z768,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z769]),(0,[z770,z1,z3,z4,z5,z6]),(0,[z1,z771,z3,z4,z5,z6])],[(0,[z772,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z340,z3,z4,z5,z6]),(0,[z15,z3,z4,z5,z6,z406]),(0,[z15,z554,z3,z4,z5,z6]),(0,[z1,z2,z3,z773,z4,z5]),(0,[z1,z2,z663,z4,z101,z6]),(0,[z47,z1,z2,z453,z123,z6]),(0,[z1,z774,z3,z4,z5,z6])],[(0,[z222,z2,z3,z756,z5,z6]),(0,[z341,z2,z3,z4,z349,z6]),(0,[z1,z3,z4,z5,z775,z6]),(0,[z490,z1,z2,z4,z5,z213]),(0,[z1,z30,z58,z3,z4,z5]),(0,[z1,z2,z3,z4,z371,z6]),(1,[z1,z2,z3,z4,z712])],[(0,[z61,z17,z3,z4,z5,z6]),(0,[z61,z1,z3,z522,z4,z5]),(0,[z321,z1,z3,z4,z5,z16])],[(0,[z28,z1,z3,z4,z5,z251]),(0,[z1,z2,z3,z4,z5,z776])],[(0,[z777,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z172,z426,z6]),(0,[z1,z2,z3,z173,z4,z712])],[(0,[z59,z0,z2,z62,z4,z5]),(0,[z1,z3,z778,z4,z5,z6]),(0,[z1,z2,z484,z4,z83,z6])],[(0,[z1,z779,z3,z4,z5,z6]),(0,[z1,z780,z3,z4,z5,z6]),(0,[z499,z3,z4,z5,z16,z6]),(0,[z1,z2,z23,z781,z5,z6])],[(0,[z1,z2,z3,z4,z782,z6]),(0,[z1,z82,z3,z4,z5,z6]),(0,[z1,z3,z345,z4,z16,z6]),(0,[z1,z58,z3,z4,z436,z6]),(0,[z783,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z172,z750,z6]),(0,[z1,z2,z3,z5,z34,z784])]],
   [[(0,[z2,z3,z4,z5,z18,z208]),(0,[z93,z2,z3,z260,z116,z6]),(0,[z1,z2,z3,z4,z785,z6]),(0,[z140,z1,z19,z3,z5,z6]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z1,z2,z3,z4,z787,z6])],[(0,[z147,z1,z3,z493,z5,z6]),(0,[z57,z1,z2,z4,z5,z213]),(0,[z1,z788,z3,z4,z5,z6])],[(0,[z59,z2,z62,z4,z5,z208]),(0,[z1,z2,z3,z789,z4,z5]),(0,[z1,z3,z4,z790,z5,z6]),(0,[z321,z1,z51,z3,z4,z5]),(0,[z2,z3,z4,z791,z5,z6]),(0,[z232,z2,z3,z4,z5,z333])],[(0,[z43,z3,z424,z4,z5,z6]),(0,[z1,z2,z3,z278,z92,z6]),(0,[z1,z2,z792,z4,z5,z6]),(0,[z1,z340,z70,z3,z4,z5])],[(0,[z1,z793,z3,z4,z5,z6]),(0,[z1,z2,z3,z278,z5,z6]),(0,[z11,z292,z2,z3,z4,z6]),(0,[z1,z2,z3,z794,z5,z6]),(0,[z1,z403,z74,z4,z5,z6]),(0,[z1,z2,z3,z4,z33,z333]),(0,[z1,z2,z3,z4,z712,z6])],[],[(0,[z431,z2,z3,z4,z5,z73]),(1,[z1,z3,z4,z761,z6]),(0,[z1,z91,z3,z4,z761,z6])],[(0,[z1,z289,z3,z4,z5,z6]),(0,[z286,z2,z80,z3,z4,z5]),(0,[z11,z1,z2,z3,z4,z6]),(0,[z57,z1,z132,z4,z5,z213])]],
   [[(0,[z1,z2,z3,z795,z5,z6]),(0,[z1,z3,z4,z5,z251,z223]),(0,[z1,z2,z3,z334,z5,z319]),(0,[z1,z796,z3,z4,z5,z6]),(0,[z1,z797,z3,z4,z5,z6]),(0,[z312,z1,z3,z4,z5,z223]),(0,[z798,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z225,z5,z26]),(0,[z1,z799,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z66,z6])],[(0,[z1,z3,z4,z511,z83,z6]),(0,[z1,z19,z152,z3,z5,z6]),(0,[z48,z1,z3,z462,z4,z6]),(0,[z376,z3,z4,z5,z6,z375]),(0,[z1,z2,z3,z4,z5,z171]),(0,[z47,z267,z1,z3,z5,z6]),(0,[z267,z1,z3,z306,z5,z6]),(0,[z800,z1,z3,z4,z5,z6])],[(0,[z444,z1,z2,z4,z83,z6]),(0,[z801,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z802]),(0,[z1,z803,z3,z4,z5,z6])],[(0,[z1,z60,z3,z4,z5,z208]),(0,[z98,z2,z3,z4,z739,z6]),(0,[z1,z3,z146,z4,z138,z6]),(0,[z376,z2,z70,z3,z4,z5]),(0,[z47,z1,z2,z3,z750,z6])],[(0,[z1,z804,z3,z4,z5,z6]),(0,[z147,z321,z1,z3,z4,z5]),(0,[z2,z3,z4,z805,z5,z6]),(0,[z147,z1,z152,z3,z5,z6]),(0,[z806,z2,z3,z4,z5,z6]),(0,[z1,z2,z807,z4,z5,z6])],[(0,[z1,z2,z3,z4,z92,z6]),(0,[z1,z2,z3,z808,z4,z5]),(0,[z209,z2,z3,z116,z5,z6]),(0,[z1,z2,z3,z809,z4,z5]),(0,[z1,z2,z656,z4,z5,z244]),(0,[z140,z1,z3,z40,z5,z6]),(0,[z1,z3,z4,z5,z6,z810])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z59,z2,z62,z278,z5,z6]),(0,[z0,z2,z17,z3,z4,z5]),(1,[z1,z2,z781,z5,z6]),(0,[z1,z2,z3,z811,z4,z5]),(0,[z57,z1,z2,z4,z5,z715]),(0,[z1,z2,z3,z4,z127,z333])],[(0,[z11,z98,z2,z3,z4,z6]),(0,[z812,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z813,z6]),(0,[z15,z30,z3,z4,z5,z73]),(0,[z1,z30,z3,z4,z5,z814]),(0,[z1,z211,z3,z4,z101,z6])],[(0,[z59,z289,z62,z4,z5,z6]),(0,[z490,z2,z62,z4,z5,z6]),(0,[z815,z1,z2,z3,z4,z6]),(0,[z1,z816,z3,z4,z5,z6]),(0,[z1,z2,z3,z817,z5,z6]),(0,[z1,z2,z3,z4,z818,z6]),(0,[z1,z3,z819,z4,z5,z6]),(0,[z1,z820,z3,z4,z5,z6]),(0,[z450,z3,z4,z5,z6,z185]),(0,[z1,z2,z3,z172,z306,z6])],[(0,[z0,z291,z2,z3,z4,z5]),(0,[z821,z2,z3,z4,z5,z6])],[(0,[z15,z474,z3,z4,z5,z6]),(0,[z1,z2,z822,z4,z5,z6]),(0,[z823,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z824,z6]),(0,[z825,z1,z2,z4,z5,z6]),(1,[z1,z2,z4,z5,z715]),(0,[z1,z2,z3,z157,z5,z784])],[(0,[z93,z2,z3,z116,z5,z6])],[(0,[z1,z2,z3,z4,z5,z826]),(0,[z1,z2,z3,z4,z5,z827]),(0,[z42,z3,z4,z5,z136,z6]),(0,[z2,z3,z629,z4,z5,z73]),(0,[z1,z2,z3,z4,z828,z6]),(0,[z499,z3,z20,z4,z5,z6]),(0,[z829,z1,z2,z3,z4,z6]),(0,[z1,z30,z3,z506,z4,z5])],[(1,[z1,z3,z4,z5,z814]),(0,[z1,z3,z830,z4,z5,z6]),(0,[z1,z3,z4,z831,z5,z6]),(0,[z1,z2,z3,z4,z33,z712])],[(0,[z1,z60,z3,z278,z5,z6]),(0,[z59,z2,z62,z4,z92,z6]),(0,[z1,z2,z4,z5,z6,z832]),(0,[z1,z833,z3,z4,z5,z6]),(0,[z1,z2,z3,z834,z4,z5])]],
   [[(0,[z72,z2,z3,z4,z5,z540]),(0,[z59,z2,z62,z4,z5,z6]),(0,[z2,z3,z822,z4,z5,z6]),(0,[z1,z2,z3,z835,z5,z6]),(0,[z1,z30,z3,z4,z5,z307]),(0,[z836,z2,z3,z4,z5,z6])],[(0,[z28,z1,z731,z4,z5,z6]),(0,[z1,z3,z4,z5,z837,z6]),(0,[z1,z3,z4,z25,z6,z221])],[(0,[z838,z1,z2,z3,z4,z5]),(0,[z1,z839,z3,z4,z5,z6]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z1,z152,z453,z4,z5,z6]),(0,[z1,z3,z841,z4,z5,z6])],[(0,[z1,z30,z3,z4,z5,z540]),(0,[z839,z76,z3,z4,z5,z6]),(0,[z321,z1,z43,z3,z4,z5]),(0,[z1,z3,z4,z5,z842,z6]),(0,[z1,z843,z3,z4,z5,z6]),(0,[z1,z3,z146,z4,z5,z6])],[(0,[z1,z3,z4,z5,z844,z6])],[(0,[z1,z845,z3,z4,z5,z6]),(0,[z1,z211,z3,z4,z5,z6]),(0,[z1,z91,z3,z4,z492,z6]),(0,[z1,z2,z3,z303,z5,z34])],[(0,[z846,z1,z3,z4,z5,z6]),(0,[z1,z847,z3,z4,z5,z6]),(0,[z2,z3,z4,z739,z349,z6]),(0,[z2,z3,z4,z5,z739,z6]),(0,[z1,z848,z3,z4,z5,z6])],[(0,[z42,z43,z3,z4,z5,z6]),(0,[z232,z403,z3,z4,z5,z6])]],
   [[(0,[z1,z60,z3,z4,z92,z6]),(0,[z1,z849,z3,z4,z5,z6]),(0,[z147,z1,z3,z8,z9,z6]),(0,[z850,z2,z3,z4,z5,z6]),(0,[z1,z851,z3,z4,z5,z6])],[(0,[z1,z60,z3,z4,z5,z6]),(0,[z1,z2,z70,z298,z4,z5]),(0,[z140,z1,z2,z3,z83,z6]),(0,[z1,z2,z852,z4,z5,z6])],[(0,[z1,z2,z3,z853,z5,z6]),(0,[z1,z2,z3,z4,z854,z6]),(0,[z147,z401,z1,z3,z4,z6]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z750,z6]),(0,[z2,z3,z856,z4,z5,z6])],[(0,[z145,z43,z3,z4,z5,z6]),(0,[z1,z857,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z858,z6]),(0,[z97,z2,z3,z4,z739,z6]),(0,[z28,z1,z40,z4,z318,z6]),(0,[z321,z1,z2,z3,z4,z5]),(0,[z1,z51,z4,z5,z6,z77]),(0,[z449,z312,z1,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z814])],[(0,[z490,z286,z2,z3,z4,z5]),(0,[z499,z3,z4,z5,z6,z182]),(0,[z1,z2,z3,z4,z5,z859]),(0,[z140,z1,z152,z3,z5,z6]),(0,[z1,z860,z3,z4,z5,z6]),(0,[z57,z1,z2,z4,z396,z213])],[(0,[z1,z2,z3,z4,z861,z6]),(0,[z1,z3,z4,z5,z6,z862]),(0,[z312,z291,z2,z3,z4,z5])],[(0,[z15,z135,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z863,z6]),(0,[z1,z3,z864,z4,z5,z6]),(0,[z1,z2,z3,z4,z865,z6]),(0,[z866,z2,z3,z4,z5,z6])],[(0,[z321,z1,z76,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z867]),(0,[z1,z183,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z25,z333])]],
   [[(0,[z42,z839,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z3,z4,z869,z6]),(0,[z2,z3,z4,z5,z6,z185]),(0,[z1,z2,z3,z4,z870,z6]),(0,[z1,z2,z3,z4,z871,z6])],[(0,[z1,z2,z3,z872,z5,z6]),(0,[z1,z2,z3,z5,z873,z6]),(0,[z297,z2,z3,z4,z5,z18]),(0,[z13,z1,z40,z4,z5,z6]),(0,[z267,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z874])],[(0,[z875,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z715]),(0,[z376,z450,z3,z4,z5,z6])],[(0,[z140,z15,z1,z3,z5,z6]),(0,[z59,z60,z62,z4,z5,z6]),(0,[z312,z2,z3,z4,z5,z126]),(0,[z876,z2,z3,z4,z5,z6]),(0,[z1,z877,z3,z4,z5,z6])],[(0,[z1,z878,z3,z4,z5,z6]),(0,[z301,z3,z4,z5,z16,z6]),(0,[z301,z30,z3,z4,z5,z31])],[(0,[z28,z301,z3,z4,z5,z6]),(0,[z147,z1,z3,z81,z5,z6]),(0,[z1,z879,z3,z4,z5,z6]),(0,[z880,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z336,z319]),(0,[z1,z3,z4,z5,z881,z6]),(0,[z2,z3,z4,z5,z6,z882])],[(0,[z1,z2,z3,z4,z883,z6]),(0,[z1,z884,z3,z4,z5,z6]),(1,[z147,z401,z1,z3,z6]),(0,[z1,z2,z4,z720,z83,z6]),(0,[z1,z2,z3,z885,z5,z6]),(0,[z1,z2,z3,z417,z5,z34])]],
   [[(0,[z15,z2,z3,z4,z5,z128]),(0,[z1,z3,z886,z4,z5,z6]),(0,[z483,z2,z3,z94,z5,z6]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z312,z1,z3,z4,z5,z814]),(0,[z1,z2,z3,z4,z5,z888])],[(0,[z1,z2,z3,z278,z5,z208]),(0,[z1,z2,z3,z4,z29,z6]),(0,[z321,z1,z3,z20,z4,z5]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z2,z3,z4,z396,z6]),(0,[z232,z2,z453,z4,z5,z6]),(0,[z1,z890,z3,z4,z5,z6])],[(0,[z1,z891,z3,z4,z5,z6]),(0,[z321,z1,z3,z4,z5,z182]),(0,[z1,z82,z3,z4,z138,z6]),(0,[z57,z1,z4,z5,z375,z213]),(0,[z419,z1,z3,z4,z66,z6])],[(0,[z1,z3,z4,z892,z5,z6]),(0,[z1,z893,z3,z4,z5,z6]),(0,[z1,z2,z3,z894,z5,z6]),(0,[z1,z895,z3,z4,z5,z6]),(0,[z1,z2,z3,z173,z4,z350])],[(0,[z15,z534,z3,z4,z5,z6]),(0,[z1,z289,z3,z4,z5,z208]),(0,[z896,z1,z3,z4,z5,z6]),(0,[z450,z1,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z897,z6]),(0,[z1,z2,z74,z4,z5,z171])],[(0,[z2,z17,z625,z4,z5,z6]),(0,[z1,z898,z3,z4,z5,z6]),(0,[z312,z1,z3,z4,z5,z346]),(0,[z1,z899,z3,z4,z5,z6]),(0,[z1,z900,z3,z4,z5,z6])],[(0,[z140,z1,z91,z2,z3,z6]),(0,[z179,z1,z2,z78,z5,z6])],[(0,[z286,z2,z3,z4,z5,z882]),(0,[z901,z1,z3,z4,z5,z6])]],
   [[(0,[z419,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z747,z5,z6]),(0,[z1,z3,z4,z902,z5,z6])],[(0,[z1,z2,z3,z4,z903,z6]),(0,[z54,z2,z3,z4,z5,z208]),(0,[z904,z1,z3,z4,z5,z6]),(0,[z905,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z906]),(0,[z907,z2,z3,z4,z5,z6]),(0,[z147,z401,z1,z3,z9,z6]),(0,[z1,z3,z4,z41,z761,z6]),(0,[z1,z2,z74,z4,z5,z6]),(0,[z1,z2,z3,z4,z712,z32])],[(0,[z908,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z92,z208]),(0,[z1,z909,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z208]),(0,[z1,z910,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z911,z6]),(0,[z1,z2,z781,z78,z5,z6]),(0,[z1,z2,z912,z4,z5,z6])],[(0,[z98,z2,z3,z4,z250,z6]),(0,[z2,z3,z4,z5,z882,z73]),(0,[z913,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z5,z16,z251]),(0,[z1,z2,z3,z914,z5,z6]),(0,[z915,z1,z2,z3,z5,z6]),(0,[z292,z2,z3,z4,z101,z6])],[(0,[z1,z916,z3,z4,z5,z6]),(0,[z57,z1,z340,z3,z4,z5]),(0,[z147,z1,z3,z150,z5,z6]),(0,[z2,z3,z917,z4,z5,z6])],[(0,[z61,z3,z4,z5,z6,z73]),(0,[z98,z315,z3,z4,z250,z6])]],
   [[(0,[z1,z289,z3,z278,z5,z6]),(0,[z1,z3,z112,z20,z5,z6]),(0,[z1,z2,z3,z4,z918,z6]),(0,[z47,z1,z2,z3,z123,z171])],[(0,[z1,z51,z3,z4,z5,z251]),(0,[z2,z17,z822,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z919]),(0,[z2,z3,z4,z5,z6,z920]),(0,[z140,z312,z1,z3,z5,z6]),(0,[z1,z2,z3,z4,z138,z6])],[(0,[z59,z99,z3,z4,z5,z6]),(0,[z921,z1,z3,z4,z5,z6]),(0,[z1,z922,z3,z4,z5,z6]),(0,[z47,z292,z2,z3,z123,z6])],[(0,[z72,z2,z3,z4,z5,z676]),(0,[z54,z2,z299,z4,z5,z6]),(0,[z2,z3,z4,z756,z5,z6]),(0,[z1,z2,z3,z4,z5,z923]),(0,[z1,z56,z3,z4,z5,z6]),(0,[z301,z3,z20,z4,z5,z6]),(0,[z1,z3,z20,z5,z6,z668]),(0,[z430,z1,z2,z4,z83,z6])],[(0,[z2,z3,z924,z4,z5,z6]),(0,[z1,z2,z3,z4,z925,z5]),(0,[z1,z2,z3,z926,z5,z6]),(0,[z927,z2,z3,z4,z5,z6]),(0,[z1,z928,z3,z4,z5,z6]),(0,[z1,z403,z3,z4,z5,z333])],[(0,[z1,z929,z3,z4,z5,z6]),(0,[z499,z51,z3,z4,z5,z6]),(0,[z292,z2,z3,z4,z5,z171]),(0,[z47,z1,z2,z3,z123,z6]),(0,[z47,z267,z1,z2,z3,z6])],[(0,[z147,z1,z3,z175,z5,z6]),(0,[z1,z2,z3,z4,z5,z930]),(0,[z1,z2,z3,z4,z931,z6]),(0,[z1,z3,z4,z5,z122,z6]),(0,[z1,z3,z4,z5,z761,z6])],[(0,[z1,z2,z3,z4,z5,z932]),(0,[z1,z67,z593,z4,z5,z6]),(0,[z212,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z933,z6])]],
   [[(0,[z934,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z814]),(0,[z1,z3,z157,z5,z221,z26])],[(0,[z1,z289,z3,z4,z92,z6]),(0,[z1,z935,z3,z4,z5,z6]),(0,[z499,z30,z3,z4,z5,z6]),(0,[z1,z2,z22,z4,z101,z6]),(0,[z1,z2,z3,z4,z164,z32])],[(0,[z291,z2,z3,z4,z5,z6]),(0,[z292,z2,z3,z4,z5,z6]),(0,[z401,z1,z3,z20,z4,z6]),(0,[z1,z936,z3,z4,z5,z6]),(0,[z1,z937,z3,z4,z5,z6]),(0,[z938,z2,z3,z4,z5,z6])],[(0,[z1,z91,z3,z4,z5,z251]),(0,[z1,z2,z3,z4,z939,z5]),(0,[z222,z2,z3,z94,z5,z6]),(0,[z1,z940,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z720,z6]),(0,[z57,z1,z2,z331,z5,z213])],[(0,[z941,z1,z2,z3,z4,z6]),(0,[z450,z1,z3,z4,z5,z73]),(0,[z72,z291,z2,z3,z4,z5]),(0,[z499,z2,z3,z271,z4,z5]),(0,[z1,z3,z4,z5,z6,z942])],[(0,[z312,z1,z3,z4,z5,z406]),(0,[z321,z2,z3,z39,z4,z5]),(0,[z1,z91,z3,z4,z177,z6]),(0,[z55,z1,z211,z4,z83,z6])],[(0,[z1,z2,z3,z4,z5,z943]),(0,[z1,z132,z3,z4,z5,z6]),(0,[z2,z3,z4,z944,z5,z6]),(0,[z1,z2,z3,z172,z155,z6])],[(0,[z1,z2,z3,z4,z5,z945]),(0,[z1,z2,z3,z4,z5,z946]),(0,[z499,z91,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z947,z5]),(0,[z1,z2,z3,z157,z25,z26])],[(0,[z43,z3,z4,z5,z6,z454])],[(0,[z385,z1,z3,z4,z5,z6]),(0,[z301,z135,z3,z4,z5,z6]),(0,[z312,z1,z3,z4,z5,z421]),(0,[z301,z3,z4,z5,z6,z182]),(0,[z55,z1,z56,z4,z83,z6])],[(0,[z1,z2,z3,z4,z5,z948]),(0,[z1,z949,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z950]),(0,[z93,z11,z2,z3,z116,z6]),(0,[z1,z2,z3,z104,z5,z26])],[(0,[z1,z315,z3,z4,z5,z6]),(0,[z1,z3,z20,z4,z5,z251]),(0,[z54,z2,z822,z4,z5,z6]),(0,[z1,z2,z3,z4,z951,z6]),(0,[z2,z3,z952,z4,z5,z6]),(0,[z1,z91,z3,z4,z41,z6]),(1,[z140,z48,z1,z3,z6]),(0,[z1,z2,z3,z5,z784,z6])],[(0,[z140,z1,z67,z3,z5,z6])],[(0,[z1,z3,z4,z537,z16,z6]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z1,z67,z618,z4,z5,z6]),(0,[z1,z2,z3,z4,z761,z6]),(0,[z1,z2,z453,z4,z5,z333])],[(0,[z2,z3,z4,z5,z955,z6]),(0,[z1,z2,z3,z4,z956,z6]),(0,[z2,z3,z39,z271,z4,z5]),(0,[z401,z1,z19,z2,z3,z6]),(0,[z1,z2,z3,z4,z957,z6]),(0,[z291,z2,z3,z4,z5,z244])]],
   [[(0,[z1,z2,z3,z4,z5,z958]),(0,[z959,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z331,z5,z6]),(0,[z1,z3,z960,z4,z5,z6])],[(0,[z0,z1,z2,z3,z4,z5]),(1,[z2,z3,z756,z5,z6]),(0,[z1,z961,z3,z4,z5,z6]),(0,[z962,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z784,z26]),(0,[z1,z2,z3,z157,z66,z26])],[(0,[z1,z963,z3,z4,z5,z6]),(0,[z28,z1,z271,z40,z4,z5]),(0,[z1,z3,z4,z5,z6,z375]),(0,[z964,z2,z3,z4,z5,z6])],[(0,[z97,z2,z3,z4,z349,z6]),(0,[z965,z2,z3,z4,z5,z6]),(0,[z48,z1,z3,z4,z16,z6])],[(0,[z61,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z966])],[(0,[z206,z2,z3,z4,z250,z6]),(0,[z140,z1,z3,z5,z31,z6])],[(0,[z147,z1,z3,z4,z5,z251]),(0,[z1,z2,z23,z115,z371,z6])],[(0,[z1,z91,z3,z4,z687,z6]),(0,[z499,z43,z3,z4,z5,z6]),(0,[z0,z1,z3,z241,z4,z5]),(0,[z1,z51,z731,z4,z5,z6]),(0,[z55,z1,z2,z4,z720,z6]),(0,[z1,z2,z3,z306,z750,z6])]],
   [[(0,[z2,z839,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z260,z6]),(0,[z312,z1,z3,z4,z318,z6]),(0,[z1,z2,z70,z4,z5,z715]),(1,[z1,z2,z3,z750,z6])],[(0,[z1,z2,z3,z967,z5,z6]),(0,[z1,z968,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z576,z6]),(0,[z1,z3,z20,z747,z5,z6])],[(0,[z969,z1,z2,z3,z4,z5]),(0,[z1,z970,z3,z4,z5,z6]),(0,[z1,z2,z3,z971,z5,z6]),(0,[z1,z3,z4,z5,z6,z221]),(0,[z1,z374,z3,z4,z41,z6])],[(0,[z226,z15,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z223]),(0,[z1,z2,z603,z4,z101,z6]),(0,[z2,z3,z972,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z973]),(0,[z1,z2,z3,z4,z974,z6]),(0,[z1,z975,z3,z4,z5,z6]),(0,[z1,z3,z174,z4,z101,z6])],[(0,[z1,z2,z3,z334,z336,z6]),(0,[z1,z976,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z977]),(0,[z1,z3,z4,z978,z5,z6]),(0,[z1,z2,z3,z306,z447,z6]),(0,[z1,z19,z3,z151,z5,z6]),(0,[z1,z82,z23,z115,z5,z6]),(0,[z2,z3,z4,z5,z6,z979])],[(0,[z499,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z980,z6]),(0,[z981,z1,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z784]),(0,[z1,z2,z3,z303,z5,z784])],[(0,[z1,z2,z3,z4,z5,z982]),(0,[z1,z2,z3,z278,z5,z319]),(0,[z47,z1,z525,z2,z3,z6]),(0,[z1,z983,z3,z4,z5,z6]),(0,[z1,z984,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z985,z6])],[(0,[z15,z76,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z986,z6]),(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z211,z3,z4,z83,z6]),(0,[z57,z1,z2,z395,z5,z213])]],
   [[(0,[z1,z2,z3,z4,z5,z988]),(0,[z59,z2,z629,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z19,z3,z747,z5,z6]),(0,[z990,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z993,z3,z4,z5,z6]),(0,[z994,z1,z3,z4,z5,z6])],[(0,[z15,z839,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z995,z6]),(0,[z222,z2,z3,z553,z5,z6]),(0,[z376,z2,z3,z4,z5,z18]),(0,[z1,z3,z4,z5,z31,z814]),(0,[z212,z2,z3,z4,z396,z6])],[(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z59,z61,z62,z4,z5,z6]),(0,[z1,z2,z3,z998,z5,z6]),(0,[z1,z2,z999,z4,z5,z6]),(0,[z147,z1,z3,z747,z5,z6]),(0,[z1000,z1,z3,z4,z5,z6])],[(1,[z2,z3,z4,z5,z882]),(0,[z1001,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z4,z83,z6])],[(0,[z43,z135,z3,z4,z5,z6]),(0,[z1,z67,z448,z4,z5,z6]),(0,[z1,z3,z4,z5,z814,z182]),(0,[z1,z3,z1002,z4,z5,z6]),(0,[z291,z2,z3,z4,z396,z6])],[(0,[z1,z2,z3,z1003,z4,z5]),(0,[z43,z839,z3,z4,z5,z6])],[(0,[z499,z60,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1004,z6]),(0,[z147,z1,z3,z9,z5,z6]),(0,[z1005,z2,z3,z4,z5,z6]),(0,[z1,z19,z3,z5,z90,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z319]),(0,[z321,z499,z2,z3,z4,z5]),(0,[z1,z3,z174,z4,z5,z6]),(0,[z1,z1006,z3,z4,z5,z6])],[(0,[z15,z60,z3,z4,z5,z6]),(0,[z59,z241,z62,z4,z5,z6]),(0,[z1,z1007,z3,z4,z5,z6]),(0,[z1,z2,z3,z1008,z5,z6]),(0,[z48,z1,z152,z3,z4,z6]),(0,[z1,z132,z3,z4,z396,z6])],[(0,[z1,z2,z3,z4,z5,z1009]),(0,[z1,z2,z3,z4,z5,z1010])],[(0,[z59,z2,z822,z4,z5,z6]),(0,[z1,z3,z4,z1011,z5,z6]),(0,[z1,z67,z51,z4,z5,z6]),(0,[z301,z51,z3,z4,z5,z6]),(0,[z401,z1,z3,z4,z16,z6]),(0,[z1,z2,z70,z516,z4,z5]),(0,[z1,z2,z23,z115,z5,z6]),(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z152,z3,z4,z101,z6]),(0,[z1,z403,z453,z4,z5,z6])],[(0,[z0,z72,z2,z3,z4,z5]),(0,[z1,z91,z3,z4,z564,z6]),(0,[z1,z3,z20,z5,z141,z6]),(0,[z1,z2,z3,z395,z5,z6]),(0,[z1,z2,z70,z4,z5,z244])],[(0,[z1,z2,z4,z5,z6,z1013]),(0,[z1,z1014,z3,z4,z5,z6]),(0,[z292,z2,z74,z4,z5,z6])],[],[(0,[z43,z2,z3,z4,z5,z128]),(0,[z61,z72,z3,z4,z5,z6]),(0,[z1,z1015,z3,z4,z5,z6]),(0,[z140,z48,z1,z2,z3,z6]),(0,[z301,z30,z3,z4,z5,z6])]],
   [[(0,[z1,z474,z3,z4,z5,z31]),(0,[z1,z3,z731,z4,z5,z6]),(0,[z28,z499,z3,z4,z5,z6]),(0,[z1016,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1017]),(0,[z47,z1,z2,z3,z682,z6])],[(0,[z469,z1,z2,z78,z5,z6]),(0,[z72,z99,z3,z4,z5,z18]),(0,[z292,z152,z3,z4,z5,z6])],[(0,[z59,z2,z62,z4,z5,z319]),(0,[z57,z212,z2,z4,z5,z213])],[(0,[z1,z3,z4,z5,z251,z182]),(0,[z312,z1,z3,z4,z5,z182]),(0,[z1018,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z331,z396,z6]),(0,[z1,z152,z3,z4,z5,z171]),(0,[z1,z2,z3,z4,z1019,z6])],[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z4,z1021,z6]),(0,[z1,z2,z3,z1022,z4,z5]),(0,[z1,z2,z4,z5,z720,z6])],[(0,[z1,z67,z3,z4,z318,z6]),(0,[z1,z2,z3,z5,z1023,z6]),(0,[z301,z91,z3,z4,z5,z6]),(0,[z1,z2,z23,z109,z5,z6])],[(0,[z1,z3,z241,z4,z5,z6]),(0,[z1024,z1,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1025,z6]),(0,[z28,z321,z1,z40,z4,z5]),(0,[z140,z48,z1,z3,z5,z6]),(0,[z1026,z2,z3,z4,z5,z6])],[(0,[z42,z3,z4,z258,z5,z6]),(0,[z297,z43,z3,z4,z5,z6]),(0,[z401,z1,z2,z3,z4,z6]),(0,[z140,z1,z3,z41,z5,z6]),(0,[z1,z1027,z3,z4,z5,z6]),(0,[z1,z2,z3,z172,z329,z6])]],
   [[(0,[z1,z2,z3,z4,z1028,z6]),(0,[z1,z2,z1029,z4,z5,z6]),(0,[z1,z3,z747,z9,z5,z6]),(0,[z1,z152,z3,z4,z5,z6]),(0,[z1030,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1031,z6]),(0,[z98,z3,z4,z250,z511,z6]),(0,[z1,z3,z4,z5,z6,z1032])],[(0,[z1,z30,z3,z4,z5,z454]),(0,[z376,z2,z3,z4,z5,z73]),(0,[z1,z3,z40,z4,z318,z6])],[(0,[z1,z60,z3,z4,z5,z319]),(0,[z1,z1033,z3,z4,z5,z6]),(0,[z1034,z1,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1035,z5,z6]),(0,[z1,z3,z4,z5,z31,z545]),(0,[z1036,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z1037,z5,z6]),(0,[z1,z1038,z3,z4,z5,z6])],[(0,[z59,z2,z522,z62,z4,z5]),(0,[z1039,z1,z3,z4,z5,z6]),(0,[z1,z2,z184,z115,z5,z6]),(0,[z47,z1,z2,z3,z493,z6])],[(0,[z1,z91,z152,z3,z4,z6])],[(0,[z1,z2,z3,z1040,z5,z6]),(0,[z295,z2,z3,z4,z5,z73]),(0,[z450,z1,z3,z4,z5,z6]),(0,[z140,z1,z3,z9,z5,z6]),(0,[z1,z152,z3,z4,z83,z6]),(0,[z212,z132,z3,z4,z5,z6])]],
   [[(0,[z1,z30,z3,z4,z5,z251]),(0,[z312,z1,z3,z4,z5,z532]),(0,[z2,z3,z4,z5,z18,z882]),(0,[z291,z30,z2,z3,z4,z5])],[(0,[z1,z2,z1041,z4,z5,z6]),(0,[z321,z1,z91,z3,z4,z5]),(0,[z401,z1,z152,z3,z4,z6]),(0,[z1,z2,z22,z4,z138,z6])],[(0,[z286,z2,z3,z4,z5,z73]),(0,[z291,z132,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1042,z6])],[(0,[z15,z2,z3,z4,z5,z208]),(0,[z1,z2,z3,z1043,z5,z6]),(0,[z1,z1044,z3,z4,z5,z6])],[(0,[z1,z3,z4,z1045,z5,z6]),(0,[z1046,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z31,z565]),(0,[z30,z2,z3,z4,z5,z126]),(0,[z1047,z1,z3,z4,z5,z6])],[(0,[z301,z43,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1048]),(0,[z1,z67,z472,z4,z5,z6]),(0,[z47,z147,z48,z1,z3,z6])],[(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z3,z4,z5,z6,z1050]),(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z58,z3,z4,z5,z6]),(0,[z147,z401,z1,z2,z3,z6]),(0,[z1,z2,z1052,z4,z5,z6]),(0,[z2,z3,z4,z1053,z5,z6])],[(0,[z43,z2,z3,z4,z5,z208]),(0,[z2,z822,z62,z4,z5,z6]),(0,[z72,z340,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z1054,z6])]],
   [[(0,[z1,z3,z4,z343,z5,z6]),(0,[z147,z301,z3,z4,z5,z6]),(0,[z30,z3,z4,z5,z31,z126]),(0,[z1,z2,z3,z4,z1055,z6]),(0,[z1,z2,z4,z781,z5,z6])],[(0,[z1,z1056,z3,z4,z5,z6]),(0,[z1,z2,z3,z1057,z4,z6]),(0,[z1,z1058,z3,z4,z5,z6]),(1,[z2,z3,z4,z739,z6]),(0,[z1,z2,z3,z4,z1059,z6]),(0,[z24,z1,z3,z4,z16,z6]),(0,[z212,z2,z3,z331,z5,z6]),(0,[z1060,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z1061,z5,z6]),(0,[z2,z3,z4,z5,z18,z44]),(0,[z1,z2,z3,z1062,z5,z6]),(0,[z232,z2,z3,z4,z5,z171]),(0,[z47,z1,z152,z3,z123,z6])],[(0,[z301,z76,z3,z4,z5,z6]),(0,[z59,z2,z62,z4,z336,z6]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z3,z1064,z4,z5,z6]),(0,[z47,z1,z2,z3,z68,z6]),(0,[z1,z2,z22,z4,z720,z6])],[(0,[z1,z2,z3,z4,z5,z1065]),(0,[z292,z2,z3,z4,z83,z6]),(0,[z1,z2,z3,z5,z1066,z6]),(0,[z291,z2,z3,z331,z5,z6])],[(0,[z1067,z2,z3,z4,z5,z6]),(0,[z449,z1,z40,z4,z5,z6]),(0,[z147,z401,z1,z3,z5,z6]),(0,[z1,z2,z239,z115,z5,z6]),(0,[z1,z2,z4,z5,z715,z213]),(0,[z1,z2,z3,z4,z127,z32])],[(0,[z1,z3,z1068,z4,z5,z6]),(0,[z2,z17,z4,z5,z6,z246]),(0,[z1069,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z318,z6]),(0,[z1,z2,z3,z1070,z5,z6]),(0,[z47,z267,z1,z3,z4,z6]),(0,[z1,z2,z3,z4,z1071,z6])],[(0,[z232,z2,z3,z4,z5,z6]),(0,[z11,z2,z3,z4,z349,z6]),(0,[z1,z2,z3,z395,z396,z6])]],
   [[(0,[z1,z2,z3,z4,z1072,z6]),(0,[z1,z2,z1073,z4,z5,z6]),(0,[z1,z132,z3,z331,z5,z6]),(0,[z1,z3,z1074,z4,z5,z6])],[(0,[z312,z43,z3,z4,z5,z73]),(0,[z1075,z1,z3,z4,z5,z6]),(0,[z21,z1,z2,z4,z83,z6])],[],[(0,[z1,z2,z3,z4,z5,z251]),(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z3,z4,z1077,z5,z6]),(0,[z93,z385,z3,z116,z5,z6]),(0,[z28,z1,z40,z4,z5,z6]),(0,[z1078,z2,z3,z4,z5,z6]),(1,[z1,z3,z747,z5,z6]),(0,[z1,z2,z453,z4,z101,z6]),(0,[z47,z232,z2,z3,z123,z6]),(0,[z1,z3,z1079,z4,z5,z6])],[(0,[z1,z2,z3,z1080,z5,z6]),(0,[z1,z60,z3,z4,z336,z6])],[(0,[z1,z2,z3,z1081,z4,z6]),(0,[z1,z3,z1082,z4,z5,z6])],[(0,[z1,z43,z3,z4,z5,z251]),(0,[z42,z3,z4,z5,z6,z346]),(0,[z1,z1083,z3,z4,z5,z6]),(0,[z1,z1084,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1085,z6]),(0,[z1,z2,z3,z4,z5,z1086]),(0,[z312,z1,z276,z3,z4,z5])],[(0,[z499,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z118,z1,z2,z78,z5,z6])]],
   [[(0,[z11,z1,z3,z4,z343,z6]),(0,[z1088,z2,z3,z4,z5,z6]),(0,[z1,z1089,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z1090])],[(0,[z1,z2,z3,z4,z5,z1091]),(0,[z59,z0,z2,z3,z4,z5]),(0,[z57,z1,z2,z629,z4,z5]),(0,[z2,z3,z4,z5,z1092,z6])],[(0,[z28,z1,z110,z4,z5,z6]),(0,[z1,z3,z1093,z4,z5,z6]),(0,[z2,z3,z4,z5,z1094,z6]),(0,[z1,z2,z3,z1095,z5,z6]),(0,[z401,z1,z91,z3,z4,z6]),(0,[z13,z1,z2,z4,z83,z6]),(0,[z1,z2,z3,z157,z5,z26])],[(0,[z93,z3,z343,z116,z5,z6]),(0,[z1,z2,z453,z4,z5,z171]),(0,[z1,z1096,z3,z4,z5,z6])],[(0,[z1,z76,z3,z4,z5,z251]),(0,[z1,z1097,z3,z4,z5,z6]),(0,[z1098,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1099]),(0,[z1,z2,z3,z4,z1100,z6]),(0,[z1,z2,z3,z334,z92,z6]),(0,[z1,z2,z1101,z4,z5,z6]),(0,[z2,z3,z4,z250,z739,z6]),(0,[z1,z340,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z33,z25]),(0,[z1,z2,z3,z4,z712,z127])],[(0,[z1,z2,z3,z4,z5,z1102]),(0,[z1,z2,z3,z334,z5,z6]),(0,[z1,z2,z3,z1103,z4,z5]),(0,[z695,z1,z3,z4,z16,z6]),(0,[z1,z2,z3,z4,z5,z1104]),(0,[z312,z1,z3,z4,z5,z601]),(0,[z1,z2,z23,z115,z138,z6])],[(0,[z2,z3,z62,z4,z5,z208]),(0,[z376,z2,z3,z4,z5,z208]),(0,[z1,z2,z3,z4,z1105,z6]),(0,[z1,z2,z3,z4,z1106,z6]),(0,[z72,z3,z4,z5,z18,z223])]],
   [[(0,[z1,z2,z3,z4,z1107,z6]),(0,[z1,z2,z3,z1108,z5,z6]),(0,[z1,z2,z453,z4,z5,z6]),(0,[z1109,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1110,z6]),(0,[z1,z1111,z3,z4,z5,z6]),(0,[z1,z3,z4,z318,z31,z6]),(0,[z28,z321,z1,z3,z4,z5]),(0,[z1,z3,z1112,z4,z5,z6]),(0,[z48,z1,z3,z300,z16,z6])],[(0,[z2,z3,z39,z4,z5,z6]),(0,[z54,z2,z17,z4,z5,z6]),(0,[z1,z1113,z3,z4,z5,z6]),(0,[z1,z3,z173,z174,z4,z33])],[(0,[z2,z3,z4,z5,z533,z73]),(0,[z1,z1114,z3,z4,z5,z6]),(0,[z1,z152,z74,z4,z5,z6])],[(0,[z1,z289,z3,z4,z5,z319]),(0,[z1,z2,z3,z522,z4,z5]),(0,[z1115,z1,z3,z4,z5,z6]),(0,[z99,z17,z3,z4,z5,z6]),(1,[z1,z731,z4,z5,z6]),(0,[z1,z1116,z3,z4,z5,z6])],[(0,[z15,z200,z3,z4,z5,z6]),(0,[z72,z2,z3,z4,z5,z882]),(0,[z212,z2,z3,z395,z5,z6])],[(0,[z1,z2,z3,z4,z1117,z6]),(0,[z57,z1,z58,z4,z5,z213])],[(0,[z286,z2,z3,z4,z5,z208]),(0,[z156,z2,z3,z4,z5,z18]),(0,[z1,z2,z1118,z4,z5,z6]),(0,[z1,z2,z3,z1119,z5,z6]),(0,[z1,z2,z3,z4,z101,z333])]],
   [[(0,[z59,z2,z62,z334,z5,z6]),(0,[z1,z2,z3,z756,z5,z6]),(0,[z98,z292,z2,z3,z4,z6]),(0,[z72,z135,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z1120]),(0,[z1,z30,z3,z4,z5,z31]),(0,[z1121,z2,z3,z4,z5,z6]),(0,[z291,z2,z3,z395,z5,z6]),(0,[z47,z1,z2,z3,z123,z333])],[(0,[z1,z3,z1122,z4,z5,z6]),(0,[z1,z58,z3,z4,z396,z6])],[(0,[z1,z2,z3,z4,z92,z319]),(0,[z47,z1,z91,z19,z3,z6]),(0,[z1,z1123,z3,z4,z5,z6])],[(0,[z1,z2,z1124,z4,z5,z6])],[(0,[z98,z2,z3,z4,z538,z6]),(0,[z1,z3,z4,z5,z6,z1125]),(0,[z1126,z2,z3,z4,z5,z6]),(0,[z1,z132,z3,z395,z5,z6]),(0,[z47,z267,z1,z3,z123,z6])],[(0,[z1,z3,z4,z1127,z5,z6]),(0,[z57,z1,z2,z4,z436,z213]),(0,[z292,z2,z3,z4,z5,z333])],[(0,[z1,z2,z3,z1128,z4,z5]),(0,[z1,z2,z3,z4,z336,z208]),(0,[z550,z2,z3,z4,z5,z73]),(0,[z1129,z2,z3,z4,z5,z6]),(0,[z57,z376,z2,z4,z5,z213])],[(0,[z1,z2,z3,z4,z1130,z6]),(0,[z1,z2,z3,z1131,z4,z5]),(0,[z1,z2,z3,z4,z1132,z6]),(0,[z1,z3,z1133,z4,z5,z6]),(0,[z1,z3,z1134,z4,z5,z6])]],
   [[(0,[z43,z60,z3,z4,z5,z6]),(0,[z212,z2,z3,z4,z436,z6])],[(0,[z1,z60,z3,z334,z5,z6]),(0,[z1,z2,z731,z4,z5,z6]),(0,[z1135,z2,z3,z4,z5,z6]),(0,[z1136,z2,z3,z4,z5,z6])],[(0,[z15,z465,z3,z4,z5,z6]),(0,[z1,z2,z577,z4,z101,z6]),(0,[z1,z3,z4,z5,z1137,z6]),(0,[z1,z1138,z3,z4,z5,z6]),(0,[z1,z3,z174,z4,z83,z6]),(0,[z57,z291,z2,z4,z5,z213])],[(0,[z1,z1139,z3,z4,z5,z6]),(0,[z98,z2,z3,z4,z555,z6]),(0,[z1,z2,z3,z271,z4,z5]),(0,[z1,z2,z3,z4,z1140,z6]),(0,[z1141,z1,z3,z4,z5,z6]),(0,[z291,z2,z3,z4,z436,z6]),(0,[z47,z1,z2,z74,z123,z6])],[(1,[z2,z822,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1142]),(0,[z72,z2,z3,z418,z4,z5]),(0,[z1,z2,z3,z4,z5,z333]),(0,[z1,z2,z3,z4,z25,z6])],[(0,[z1,z3,z20,z353,z5,z6]),(0,[z376,z2,z3,z4,z5,z6]),(0,[z1,z1143,z3,z4,z5,z6]),(0,[z1,z340,z3,z4,z5,z73])],[(0,[z1144,z1,z2,z3,z5,z6]),(0,[z1,z1145,z3,z4,z5,z6]),(0,[z28,z1,z40,z4,z29,z6]),(0,[z1,z3,z4,z761,z16,z6]),(0,[z1,z2,z4,z101,z720,z6]),(0,[z47,z1,z403,z3,z123,z6])],[(0,[z0,z61,z1,z3,z4,z5]),(0,[z1,z2,z3,z4,z1146,z6]),(0,[z1,z2,z3,z781,z5,z6]),(0,[z1147,z2,z3,z4,z5,z6]),(0,[z1,z132,z3,z4,z436,z6]),(0,[z57,z376,z2,z3,z4,z5])]],
   [[(0,[z1,z3,z4,z5,z6,z1148]),(0,[z1149,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z1150,z6])],[(0,[z59,z61,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1151,z6]),(0,[z1,z2,z3,z4,z1152,z6])],[(0,[z1,z2,z3,z278,z336,z6]),(0,[z1,z2,z3,z4,z436,z6]),(0,[z232,z2,z74,z4,z5,z6]),(0,[z1,z2,z3,z4,z750,z6])],[(1,[z839,z3,z4,z5,z6]),(0,[z527,z2,z3,z4,z5,z73]),(0,[z1,z2,z3,z4,z5,z882]),(0,[z1,z2,z3,z4,z5,z1153]),(0,[z1154,z2,z3,z4,z5,z6]),(0,[z1,z3,z146,z4,z371,z6]),(0,[z1,z2,z3,z4,z83,z333])],[(0,[z1,z2,z3,z4,z1155,z6]),(0,[z312,z1,z3,z4,z5,z220]),(0,[z57,z450,z1,z4,z5,z213]),(0,[z1,z2,z3,z4,z5,z715])],[(0,[z1,z289,z3,z4,z336,z6]),(0,[z93,z2,z3,z756,z5,z6]),(0,[z321,z1,z30,z3,z4,z5]),(0,[z118,z1,z2,z781,z5,z6])],[(0,[z0,z2,z3,z4,z5,z73]),(0,[z232,z152,z3,z4,z5,z6])],[(0,[z1,z1156,z3,z4,z5,z6]),(0,[z1,z731,z40,z4,z5,z6]),(0,[z1,z3,z170,z4,z5,z31]),(0,[z1,z3,z4,z5,z1157,z6]),(0,[z1,z2,z3,z4,z1158,z6]),(0,[z212,z58,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z784]),(0,[z1,z2,z3,z173,z4,z33])]],
   [[(0,[z97,z292,z2,z3,z4,z6]),(0,[z140,z48,z1,z3,z4,z6]),(0,[z57,z1,z2,z265,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1159]),(0,[z1160,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z331,z436,z6]),(0,[z2,z3,z1161,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1162,z6]),(0,[z1163,z1,z2,z3,z4,z6]),(0,[z1,z1164,z3,z4,z5,z6]),(0,[z147,z1,z3,z518,z5,z6]),(0,[z1,z19,z3,z20,z5,z6]),(0,[z1,z3,z194,z4,z16,z6]),(0,[z140,z1,z2,z3,z101,z6]),(0,[z291,z58,z3,z4,z5,z6]),(0,[z3,z4,z5,z6,z375,z185])],[],[(0,[z1,z2,z3,z4,z336,z6]),(0,[z72,z99,z3,z4,z5,z6]),(0,[z666,z1,z2,z78,z5,z6]),(0,[z419,z1,z3,z157,z5,z26])],[(0,[z301,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1165,z6]),(0,[z1,z2,z3,z4,z5,z1166]),(0,[z1,z2,z3,z5,z1167,z6]),(0,[z57,z450,z1,z3,z4,z5]),(0,[z1168,z1,z3,z4,z5,z6])],[(0,[z1169,z1,z2,z3,z4,z6])],[(0,[z1170,z1,z2,z3,z5,z6]),(0,[z1,z2,z115,z781,z5,z6]),(0,[z1171,z1,z3,z4,z5,z6])]],
   [[(0,[z321,z1,z58,z3,z4,z5])],[],[(0,[z28,z1,z265,z4,z5,z6]),(0,[z292,z403,z3,z4,z5,z6])],[(0,[z2,z3,z4,z5,z6,z126]),(0,[z1,z2,z3,z334,z5,z208]),(0,[z1,z3,z1172,z4,z5,z6])],[(0,[z1,z1173,z3,z4,z5,z6]),(0,[z1174,z2,z3,z4,z5,z6]),(0,[z1,z403,z3,z4,z5,z171]),(0,[z1,z3,z1175,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1176,z6]),(0,[z1,z3,z4,z5,z6,z1177]),(0,[z1,z2,z4,z138,z83,z6]),(0,[z450,z1,z70,z3,z4,z5]),(0,[z1178,z1,z3,z4,z5,z6])],[(0,[z1,z135,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z1179,z6]),(0,[z1,z3,z4,z101,z511,z6]),(0,[z286,z291,z2,z3,z4,z5]),(0,[z312,z1,z58,z3,z4,z5]),(0,[z1,z2,z3,z4,z1180,z6]),(0,[z47,z1,z3,z122,z123,z6])],[(0,[z1,z3,z4,z5,z511,z6]),(0,[z42,z3,z485,z4,z5,z6]),(0,[z1,z2,z3,z172,z45,z6]),(0,[z1,z1181,z3,z4,z5,z6]),(0,[z140,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z8,z6]),(0,[z1182,z2,z3,z4,z5,z6]),(0,[z1183,z1,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 537) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 537).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1072).take 66) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1138)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [537, 535, 66] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 111).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 111).take 115).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 226).take 30).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [111, 115, 30] = true :=
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

end PEqualNP.Outside.L_meta_38669

theorem PEqualNP.Outside.L_meta_38669 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 3941264064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 3941264064) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38669.solve